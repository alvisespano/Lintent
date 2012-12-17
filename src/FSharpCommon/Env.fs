(*
 * F# Common Library
 * Env.fs: environment definitions
 * (C) 2007-2012 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module FSharpCommon.Env

open System
open System.Text.RegularExpressions
open FSharpCommon.Prelude
open FSharpCommon.Log

(* generic environment reporting *)
    
exception UnboundSymbolError of string

module Report =
    let unbound_symbol id = throw_formatted UnboundSymbolError "%O" id


(* polymoprhic environment *)

type ('id, 'a) combine_mode = Existant of 'id * 'a * 'a
                            | New of 'id * 'a

type ('id, 'a) t when 'id : comparison = private Env of Map<'id, 'a>
    
let search_by p (Env m) = Map.tryPick (fun x v -> if p x v then Some v else None) m

let search x env = search_by (fun x' _ -> x' = x) env

let lookup x env =
    match search x env with
        | Some x -> x
        | None   -> Report.unbound_symbol x

let bind x v (Env m) = Env (Map.add x v m)
    
let append (Env m2) (Env m1) = Env (Map.fold (fun m x t -> Map.add x t m) m1 m2)

let update x f env = bind x (f (lookup x env)) env

let effect x f env = f (lookup x env)

let diff f z (Env m2) (Env m1) =
    let f z x v2 =
        let esit = 
            match Map.tryFind x m1 with
                | Some v1 -> Existant (x, v1, v2)
                | None    -> New (x, v2)
        in
            f z esit
    in
        Map.fold f z m2

let map f (Env m) = Env (Map.map f m)

let combine f env2 env1 =
    let g env' = function
        (Existant (x, _, _) | New (x, _)) as esit ->
            match f esit with
                | Some v -> bind x v env'
                | None   -> env'
    in
        diff g env1 env2 env1

let filter f (Env m) = Env (Map.filter f m)

let find f (Env m) = Map.findKey f m

let exists f (Env m) = Map.exists f m

let occurs x (Env m) = Map.containsKey x m

let toSeq (Env m) = Map.toSeq m

let asMap (Env m) = m

let pretty_sep p sep (Env m) =
    if m.IsEmpty then "<empty>"
    else
        let ss = Map.fold (fun ss x v -> p x v :: ss) [] m
        in
            flatten_strings sep ss

let pretty p = pretty_sep p "\n"

let pretty_diffs pretty_existant pretty_new env2 env1 =
    let f ss = function
        Existant (x, v1, v2) -> if v1 <> v2 then pretty_existant x v1 v2 :: ss else ss
        | New (x, v)           -> pretty_new x v :: ss
    in
        diff f [] env2 env1

let empty = Env Map.empty

let partial_compare (Env m1) (Env m2) =
    let cmp op m1 m2 = Map.forall (fun x1 v1 -> match Map.tryFind x1 m2 with Some v2 -> op v1 v2 | None -> false) m1
    in
        if m1.Count = m2.Count && cmp (=) m1 m2 then Some 0
        elif cmp (>) m2 m1 then Some -1
        elif cmp (>) m1 m2 then Some 1
        else None


module M =

    type [< AbstractClass >] access<'state, 'id, 'a when 'id : comparison> () =
        abstract get : 'state -> t<'id, 'a> * 'state
        abstract set : t<'id, 'a> -> 'state  -> unit * 'state
        abstract bind : 'id -> 'a -> 'state -> unit * 'state

        member self.apply f st = let env, st = self.get st in f env, st
        member self.lift f st = let env, st = self.get st in self.set (f env) st
        default self.bind id v st = self.lift (bind id v) st
        member self.search_by p = self.apply <| search_by p
        member self.search x st = self.search_by (fun x' _ -> x = x') st           
        member self.lookup x st =
            let o, st = self.search x st
            match o with
                | Some v -> v, st
                | None   -> Report.unbound_symbol x

        member self.update x f = self.lift (fun env -> update x f env)
        member self.effect x f = self.apply <| effect x f

        member self.fork f st =
            let env, st = self.get st
            let r, st = f st
            let (), st = self.set env st
            in
                (r, st)

    let get (acc : access<_, _, _>) = acc.get
    let set (acc : access<_, _, _>) = acc.set
    let bind (acc : access<_, _, _>) = acc.bind
    let search_by (acc : access<_, _, _>) = acc.search_by
    let search (acc : access<_, _, _>) = acc.search
    let lookup (acc : access<_, _, _>) = acc.lookup
    let effect (acc : access<_, _, _>) = acc.effect
    let update (acc : access<_, _, _>) = acc.update
    let fork (acc : access<_, _, _>) = acc.fork



      
    