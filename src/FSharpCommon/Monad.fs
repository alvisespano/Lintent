(*
 * F# Common Library
 * Prelude.fs: misc stuff
 * (C) 2007-2012 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module FSharpCommon.Monad

open FSharpCommon.Prelude

let inline mapM b f m =       
    let inline (>>=) m f = (^x: (member Bind: ^m -> (^n -> ^n) -> ^n) b, m, f)
    let inline unit x = (^x: (member Return: ^b -> ^n) b, x)  
    in
        m >>= (fun x -> unit (f x))

let inline joinM b m =
    let inline (>>=) m f = (^x: (member Bind: ^m -> (^n -> ^n) -> ^n) b, m, f)
    in
        m >>= id

type M<'s, 'a> = 's -> 'a * 's

type builder () =
    member m.Delay f : M<'s, 'a> = f ()
    member m.Return x : M<'s, 'a> = fun s -> (x, s)
    member m.ReturnFrom f : M<'s, 'a> = fun s -> f s
    member m.Bind (e, f) : M<'s, 'b> = fun s -> let (r, s') = e s in f r s'
    member m.Zero () : M<'s, unit> = fun s -> ((), s)
    member m.For (seq, f) : M<'s, unit> = fun s -> ((), Seq.fold (fun s x -> let (r, s') = f x s in s') s seq)
    member m.TryWith (e : M<'s, 'a>, catch : exn -> M<'s, 'a>) : M<'s, 'a> = fun s -> try e s with exn -> catch exn s
    member m.TryFinally (e, fin) : M<'s, 'a> = fun s -> try e s finally fin ()
    member m.Combine (e1, e2) : M<'s, 'a> = fun s -> let ((), s') = e1 s in e2 s'

let M = new builder ()

let get_state = fun s -> (s, s)
let set_state s = fun _ -> ((), s)
let lift_state f = fun s -> ((), f s)

let lift f x = fun s -> (f x, s)

let fork f =
  M {
    let! st = get_state
    let (r, st) = f st
    do! set_state st
  }

module Lazy =
    
    let suspend f st = lazy (let r, _ = f st in r), st


module Option =        

    let something f def o =
      M {
        match o with
            | Some x -> return! f x
            | None   -> return def
      }

    let map f = something (fun x -> M { let! r = f x in return Some r }) None

    let iter f = function
        | None   -> fun s -> ((), s)
        | Some x -> f x

    let bind f = something f None

module List =               

    let map f l st = List.fold (fun (l, st) x -> let (r, st) = f x st in (r :: l, st)) ([], st) l

    let pick f l st =
        let rec recur st = function
            | []     -> raise (new System.Collections.Generic.KeyNotFoundException ())
            | x :: l -> let (r, st) = f x st in match r with None -> recur st l | Some y -> (y, st)
        in
            recur st l

