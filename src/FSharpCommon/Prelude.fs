(*
 * F# Common Library
 * Prelude.fs: misc stuff
 * (C) 2007-2012 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module FSharpCommon.Prelude

open System
open System.Collections.Generic
open System.Text.RegularExpressions
open Microsoft.FSharp

exception Unexpected of string

let identity = id

let throw_formatted exnf fmt = Printf.kprintf (fun s -> raise (exnf s)) fmt

let unexpected fmt = throw_formatted Unexpected fmt

let not_implemented fmt = throw_formatted (fun s -> new NotImplementedException (s)) fmt

let equal_float (x : float) y = Math.Abs (x - y) <= Double.Epsilon

let flatten_strings_or_nothing empty sep sc =
    match Seq.length sc with
        0 -> empty
      | 1 -> Seq.head sc
      | _ -> Seq.fold (fun r s -> r + sep + s) (Seq.head sc) (Seq.skip 1 sc)

let mappen_strings_or_nothing f empty sep c = flatten_strings_or_nothing empty sep (Seq.map f c)

let flatten_strings sep = flatten_strings_or_nothing "" sep

let mappen_strings f = mappen_strings_or_nothing f ""

let separate2 f = List.fold (fun (aa, bb) x -> match f x with Choice1Of2 a -> (a :: aa, bb) | Choice2Of2 b -> (aa, b :: bb)) ([], [])

let fresh =
    let cnt = ref 0
    in
        fun () -> let r = !cnt in incr cnt; r

let something f def = function
    None   -> def
  | Some x -> f x

let rec try_map f = function
    | [] -> Some []
    | x :: xs -> match f x with Some y -> Option.map (fun ys -> y :: ys) (try_map f xs) | None -> None

let soprintf fmt = function None -> "" | Some x -> sprintf fmt x

let either def o = something (fun x -> x) def o

let split_string_on_size n (s : string) =
    let m = s.Length % n
    in
        Array.init (s.Length / n + (if m > 0 then 1 else 0)) (fun i -> s.Substring (i * n, if i * n + n > s.Length then m else n))

let capitalize (s : string) =
    if s.Length > 1 then s.Substring(0, 1).ToUpper() + s.Substring(1) else s.ToUpper()

let inline append_format (fmt1 : PrintfFormat< ^a -> _, _, _, _>) (fmt2 : PrintfFormat< ^b, _, _, _>) =
    new PrintfFormat< ^a -> ^b, _, _, _> (fmt1.Value + fmt2.Value)

let inline (+%) fmt1 fmt2 = append_format fmt1 fmt2

let get_assembly_attribute<'T when 'T :> System.Attribute> (asm : System.Reflection.Assembly) =
    let t = typeof<'T>
    try
        let rex = new Text.RegularExpressions.Regex ("(System.Reflection.Assembly)(\w+)(Attribute)")
        let name = rex.Match(t.FullName).Groups.[2].Value
        let atts = asm.GetCustomAttributes (t, false)
        let att = atts.[0] :?> System.Attribute
        in
            att.GetType().GetProperty(name).GetValue(att).ToString ()
    with _ -> ""


module CustomCompare =

    let equals_on f x (yobj : obj) =
        match yobj with
            | :? 'T as y -> (f x = f y)
            | _          -> false
     
    let hash_on f x =  hash (f x)
 
    let compare_on f x (yobj: obj) =
        match yobj with
            | :? 'T as y -> compare (f x) (f y)
            | _          -> invalidArg "yobj" "cannot compare values of different types"
    
    type [< AbstractClass >] basic_by_property<'a when 'a : comparison> () =
        let c (x : basic_by_property<'a>) = x.cmp
        interface IComparable with
            member x.CompareTo yobj = compare_on c x yobj
        override x.Equals yobj = equals_on c x yobj
        override x.GetHashCode () = hash_on c x
        abstract cmp : 'a

    type [< AbstractClass >] basic_by_function<'a when 'a : comparison> (f : basic_by_property<'a> -> 'a) =
        inherit basic_by_property<'a> ()
        override self.cmp = f self
