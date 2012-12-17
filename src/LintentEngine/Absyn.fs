(*
 * TypeDroid - LintentEngine
 * Absyn.fs: Abstract Syntax
 * (C) 2012 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
 
module LintentEngine.Absyn

open System
open FSharpCommon.Prelude
open FSharpCommon.Log

(* error locating *)

type location (line : int, col : int, ?end_line : int, ?end_col : int, ?filename : string) =
    member val filename = defaultArg filename "" with get, set
    member val line = line + 1 with get
    member val col = col + 1 with get
    member self.start_line = self.line
    member self.start_col = self.col
    member val end_line = 1 + something identity line end_line with get
    member val end_col = 1 + something identity col end_col with get

    static member internal pretty_pair prefix a b =
        if a = b then sprintf "%s%d" prefix a else sprintf "%s%d-%d" prefix a b
       
    member private self.pretty_verbose =        
        sprintf "in file %s: %s %s"
            (if self.filename = "" then "<UNKNOWN-FILE>" else self.filename)
            (location.pretty_pair "at line" self.start_line self.end_line)
            (location.pretty_pair "column" self.start_col self.end_col)

    member private self.pretty_short =    
        sprintf "%s:%s,%s"
            (if self.filename = "" then "<UNKNOWN-FILE>"
            else try IO.Path.GetFileName self.filename with _ -> self.filename)
            (location.pretty_pair "" self.start_line self.end_line)
            (location.pretty_pair "" self.start_col self.end_col)

    member self.pretty = if Config.Log.verbose_pretty_location then self.pretty_verbose else self.pretty_short

let uloc = new location (-2, -2)

type located_error (message, loc : location) =
    inherit System.Exception (message)
    member val location = loc with get
    member self.header = self.location.pretty
    override self.Message = sprintf "%s: %s" self.header message

let throw_located_error loc err fmt = throw_formatted (fun msg -> err (msg, loc)) fmt


(*
 * identifiers
 *)

type id = string

type qid (prefixes : id array, id : id) =
    
    inherit CustomCompare.basic_by_function<string> (fun self -> self.ToString ())

    member val id = id with get
    member val prefixes = prefixes with get

    member self.fold fprefix fid z = Array.fold fprefix z prefixes |> fid

    member self.pretty = flatten_strings "." self.parts
    override self.ToString () = self.pretty

    member self.append id' = new qid (self.parts, id')

    member x.is_suffix_of y =
        let x = x.ToString ()
        let y = y.ToString ()
        in
            y.EndsWith x

    member x.is_prefix_of y =
        let x = x.ToString ()
        let y = y.ToString ()
        in
            y.StartsWith x

    member self.parts = Array.append self.prefixes [|id|]

    new (sa : id array) =
        let l = sa.Length
        in
            new qid (Array.sub sa 0 (l - 1), sa.[l - 1])

    new (seq : id seq) = new qid (Seq.toArray seq)

    static member of_string (s : string) = new qid (s.Split ([|'.';'$'|], StringSplitOptions.RemoveEmptyEntries))

    static member (+) (qid1 : qid, qid2 : qid) = new qid (Array.append qid1.parts qid2.parts)
    
type fqid = FQId of qid
with
    member self.pretty = match self with FQId qid -> qid.pretty
    override self.ToString () = self.pretty
    static member of_string s = FQId (qid.of_string s)
    member self.append id = match self with FQId qid -> FQId (qid.append id)
    member self.is_prefix_of y = match (self, y) with | FQId xq, FQId yq -> xq.is_prefix_of yq

let (|QId|) (qid : qid) = (qid.prefixes, qid.id)

let SQId (id : id) = qid.of_string id
let (|SQId|_|) (id : id) = function
    | QId (prefixes, id') when new qid (prefixes, id') = qid.of_string id -> Some ()
    | _ -> None



(*
 * DLM AST
 *)

module Dlm =

    type id = string

    [<CustomEquality>]
    [<CustomComparison>]
    type principal = Principal of id
                   | Top
                   | Bottom
        with
            interface IComparable with
                member self.CompareTo yobj =
                    match yobj with
                        | :? principal as p2 -> self.pretty.CompareTo p2.pretty
                        | _                  -> invalidArg "yobj" "cannot compare values of different types"

            member self.acts_for p2 hierarchy =
                match self with
                    | Top    -> true
                    | Bottom -> p2 = Bottom
                    | _      -> 
                        if self = p2 || p2 = Bottom then true
                        else List.exists (fun (actor, role) -> self = actor && role = p2) hierarchy

            member self.pretty = 
                match self with
                    | Principal id -> id
                    | Bottom       -> Config.Dlm.pretty_bottom
                    | Top          -> Config.Dlm.pretty_top

            override self.Equals obj2 =
                match obj2 with
                    | :? principal as p2 ->
                        match self, p2 with
                            | Bottom, Bottom               -> true
                            | Top, Top                     -> true
                            | Principal id1, Principal id2 -> id1.Equals id2
                            | _                            -> false
                    | _ -> false

            override self.GetHashCode () = self.pretty.GetHashCode ()



//    type reader_policy = {
//        owner  : principal
//        reader : principal
//    }
//
//    type writer_policy = {
//        owner  : principal
//        writer : principal
//    }
//
//    type op = OpJoin | OpMeet
//    with
//        member self.pri =
//            match self with
//                | OpJoin -> 1
//                | OpMeet -> 2
//    
//    let (|Join|_|) = function
//        | BinOp (p1, OpJoin, p2) -> Some(p1, p2)
//        | _                      -> None
//
//    let (|Meet|_|) = function
//        | BinOp (p1, OpMeet, p2) -> Some(p1, p2)
//        | _                      -> None
//
//    let internal Join (a, b) = BinOp (a, OpJoin, b)
//    let internal Meet (a, b) = BinOp (a, OpMeet, b)
//
//    type 'policy policy_set = BinOp of 'policy policy_set * op * 'policy policy_set
//                            | Policy of 'policy
//
//    let some_secrecy = either (Policy { owner = Bottom; reader = Bottom })
//    let some_integrity = either (Policy { owner = Bottom; writer = Bottom })
//
//    let pretty_reader_policy (p : reader_policy) = sprintf "%s:%s" (pretty_principal p.owner) (pretty_principal p.reader)
//    let pretty_writer_policy (p : writer_policy) = sprintf "%s<-%s" (pretty_principal p.owner) (pretty_principal p.writer)
//
//    let pretty_op = function
//        | OpJoin -> "|"
//        | OpMeet -> "&"
//
//    let rec pretty_policy_set pretty_policy cmp pol =
//        let R = pretty_policy_set pretty_policy cmp
//        let p fmt op pset1 pset2 = sprintf fmt (R pset1) (pretty_op op) (R pset2) 
//        in
//            match pol with
//                | Policy pol                                                       -> pretty_policy pol
//                | BinOp (pset1, op, (BinOp (_, op', _) as pset2)) when cmp op op'  -> p "%s %s (%s)" op pset1 pset2
//                | BinOp ((BinOp (_, op', _) as pset1), op, pset2) when cmp op op'  -> p "(%s) %s %s" op pset1 pset2
//                | BinOp (pset1, op, pset2)                                         -> p "%s %s %s" op pset1 pset2
//
//    let pretty_reader_policy_set = pretty_policy_set pretty_reader_policy (fun op1 op2 -> op2.pri < op1.pri)
//
//    let pretty_writer_policy_set = pretty_policy_set pretty_writer_policy (fun op1 op2 -> op2.pri > op1.pri)
//
//    let internal unfold_principals p cons owner = function
//        | [] -> unexpected "empty principal list"
//
//        | princ0 :: princs ->
//            let z = Policy (p owner princ0)
//            in
//                List.fold (fun polset princ -> cons (Policy (p owner princ), polset)) z princs
//
//    let internal unfold_readers = unfold_principals (fun owner princ -> { owner = owner; reader = princ }) Join
//    let internal unfold_writers = unfold_principals (fun owner princ -> { owner = owner; writer = princ }) Meet

    let pretty_principals set =
        match Set.toList set with
            | []                         -> ""
            | (head : principal) :: tail -> List.fold (fun s (p : principal) -> sprintf "%s, %s" s (p.pretty)) head.pretty tail


    [<AbstractClass>]
    type policy (owner : principal, right_hands_set : Set<principal>) =
        member val owner = owner with get
        member val right_hands = right_hands_set.Add owner with get, set
        
        abstract member pretty : string
        member self.allows p = p = owner || Set.contains p self.right_hands
        member self.is_bottom = 
            match self.owner with 
                | Bottom -> true //if (Set.isSubset self.right_hands (Set.singleton Bottom)) then true else false 
                | _ -> false

        member internal self.pretty_with sep = 
            sprintf "%s%s%s" (self.owner.pretty) sep (pretty_principals (self.right_hands.Remove self.owner))

        /// Returns true if the given policy p2 is at least as restrictive as the policy on which this method is invoked.
        member self.is_covered_by (p2 : policy) hierarchy = 
            let o2 = p2.owner
            match self.owner with
                | Bottom -> true
                | o when (o = o2 || o2.acts_for o hierarchy) -> p2.right_hands.IsSubsetOf self.right_hands || self.right_hands.Contains Bottom
                | _                                          -> false


    type reader_policy (owner : principal, readers : Set<principal>) =
        inherit policy (owner = owner, right_hands_set = readers)
        public new (owner : principal, ?readers : principal list) = reader_policy (owner, Set (defaultArg readers []))
        
        member self.add_reader r = new reader_policy (self.owner, self.right_hands.Add r)
        member self.apply_op (op: Set<principal> -> Set<principal> -> Set<principal>) (p2 : reader_policy) = 
            new reader_policy (self.owner, op self.readers p2.readers)
        member self.readers = self.right_hands
        override self.pretty = self.pretty_with ": "
        static member default_reader_policy = new reader_policy (Bottom, [])

        
    type writer_policy (owner : principal, writers : Set<principal>) =
        inherit policy (owner = owner, right_hands_set = writers)
        public new (owner : principal, ?writers : principal list) = writer_policy (owner, Set (defaultArg writers []))
        
        member self.add_writer w = new writer_policy (self.owner, self.right_hands.Add w)
        member self.apply_op (op: Set<principal> -> Set<principal> -> Set<principal>) (p2 : writer_policy) = 
            new writer_policy (self.owner, op self.writers p2.right_hands)
        override self.pretty = self.pretty_with "<- "
        member self.writers = self.right_hands
        static member default_writer_policy = new writer_policy (Bottom, [])


    type secrecy_policy_set (list_of_policies : reader_policy list) =

        public new (policy : reader_policy) = secrecy_policy_set ([policy])
        member val policies = list_of_policies

        member private self.add_flow (owner : principal) rh =
            let ((rpo : reader_policy option), l2) = self.list_partition owner
            match rpo with
                | Some rp -> new secrecy_policy_set (list_of_policies = rp.add_reader rh :: l2)
                | None    -> unexpected "secret_policy_set.add_flow: found no policies with owner '%s' in policy_set: %s" owner.pretty self.pretty
            
        member private self.add_implicit_righthands hierarchy =
            let add_rhs_to_policy (pset : secrecy_policy_set) (p : policy) =
                let pset = List.fold (fun state (act, role) -> if p.allows role then pset.add_flow p.owner act else pset) pset hierarchy
                pset.add_flow p.owner Top
            List.fold add_rhs_to_policy self self.policies

        member private self.add_policy op (rp2 : reader_policy) =
            let (rpo, l2) = self.list_partition rp2.owner
            match rpo with
                | Some rp -> new secrecy_policy_set (rp.apply_op op rp2 :: l2)
                | None   -> new secrecy_policy_set (rp2 :: l2)

        member private self.add_policy_set (ps2: secrecy_policy_set) op =
            List.fold (fun (pset : secrecy_policy_set) p -> pset.add_policy op p) self ps2.policies

        member private self.list_partition owner =
            let (l1, l2) = List.partition (fun (p : reader_policy) -> p.owner = owner) self.policies
            match l1 with
                | []         -> (None, l2)
                | head :: [] -> (Some head, l2)
                | _ -> unexpected "secret_policy_set.list_partition: found multiple policies with owner '%s' in policy_set: %s" owner.pretty self.pretty

        member self.is_covered_by (ps2 : secrecy_policy_set) hierarchy = 
            let expnd1 = self.add_implicit_righthands hierarchy
            let expnd2 = ps2.add_implicit_righthands hierarchy
            List.fold (
                fun b (p : reader_policy) -> b && (List.exists (fun p2 -> p.is_covered_by p2 hierarchy) expnd2.policies)
            ) true expnd1.policies
            
        member self.join ps2 = self.add_policy_set ps2 Set.intersect
        member self.meet ps2 = self.add_policy_set ps2 Set.union

        member self.principals =
            List.fold (fun s (p : reader_policy) -> Set.union s (p.right_hands)) Set.empty self.policies

        member self.remove_policy owner = 
            let rec remove_from = function
                | [] -> []
                | (head : reader_policy) :: tail -> if head.owner = owner then tail else head :: (remove_from tail)
            new secrecy_policy_set (remove_from self.policies)

        member self.pretty =
            match self.policies with
                | []            -> ""
                | head :: []    -> head.pretty
                | head :: tail  -> 
                    List.fold (fun s (p : reader_policy) -> 
                        if p.is_bottom then s 
                        else match s with
                                | ""                        -> p.pretty
                                | str when str.EndsWith ";" -> sprintf "%s %s" s p.pretty
                                | _                         -> sprintf "%s; %s" s p.pretty
                    ) "" self.policies

        static member empty_readers_set = new secrecy_policy_set (reader_policy.default_reader_policy)


    type integrity_policy_set (list_of_policies : writer_policy list) =

        public new (policy : writer_policy) = integrity_policy_set ([policy])
        member val policies = list_of_policies

        member private self.add_flow (owner : principal) rh =
            let ((wpo : writer_policy option), l2) = self.list_partition owner
            match wpo with
                | Some wp -> new integrity_policy_set (list_of_policies = wp.add_writer rh :: l2)
                | None    -> unexpected "secret_policy_set.add_flow: found no policies with owner '%s' in policy_set: %s" owner.pretty self.pretty
            
        member private self.add_implicit_righthands hierarchy =
            let add_rhs_to_policy (pset : integrity_policy_set) (p : policy) =
                let pset = List.fold (fun state (act, role) -> if p.allows role then pset.add_flow p.owner act else pset) pset hierarchy
                pset.add_flow p.owner Top
            List.fold add_rhs_to_policy self self.policies

        member private self.add_policy op (wp2 : writer_policy) =
            let (rpo, l2) = self.list_partition wp2.owner
            match rpo with
                | Some rp -> new integrity_policy_set (rp.apply_op op wp2 :: l2)
                | None    -> new integrity_policy_set (wp2 :: l2)

        member private self.add_policy_set (ps2: integrity_policy_set) op =
            List.fold (fun (pset : integrity_policy_set) p -> pset.add_policy op p) self ps2.policies

        member private self.list_partition owner =
            let (l1, l2) = List.partition (fun (p : writer_policy) -> p.owner = owner) self.policies
            match l1 with
                | []         -> (None, l2)
                | head :: [] -> (Some head, l2)
                | _ -> unexpected "found multiple policies with owner '%s' in policy_set: %s" owner.pretty (self.pretty)

        member self.is_covered_by (ps2 : integrity_policy_set) hierarchy = 
            let expnd1 = self.add_implicit_righthands hierarchy
            let expnd2 = ps2.add_implicit_righthands hierarchy
            List.fold (
                fun b (p : writer_policy) -> b && (List.exists (fun p2 -> p.is_covered_by p2 hierarchy) expnd2.policies)
            ) true expnd1.policies
            
        member self.join ps2 = self.add_policy_set ps2 Set.intersect
        member self.meet ps2 = self.add_policy_set ps2 Set.union

        member self.principals =
            List.fold (fun s (p : writer_policy) -> Set.union s (p.right_hands)) Set.empty self.policies

        member self.remove_policy owner = 
            let rec remove_from = function
                | [] -> []
                | (head : writer_policy) :: tail -> if head.owner = owner then tail else head :: (remove_from tail)
            new integrity_policy_set (remove_from self.policies)

        member self.pretty =
            match self.policies with
                | []            -> ""
                | head :: []    -> head.pretty
                | head :: tail  -> 
                    List.fold (fun s (p : writer_policy) ->
                        if p.is_bottom then s 
                        else match s with
                                | ""                        -> p.pretty
                                | str when str.EndsWith ";" -> sprintf "%s %s" s p.pretty
                                | _                         -> sprintf "%s; %s" s p.pretty
                    ) "" self.policies

        static member empty_writers_set = new integrity_policy_set (writer_policy.default_writer_policy)


    type label (?secrecy : secrecy_policy_set, ?integrity : integrity_policy_set, ?loc : location) =
        public new (p : principal) = label (
                                        secrecy = new secrecy_policy_set([new reader_policy(p, Set ([p]))]),
                                        integrity = new integrity_policy_set([new writer_policy(p, Set ([p]))])
                                    )
                         
        member val secrecy = defaultArg secrecy secrecy_policy_set.empty_readers_set with get
        member val integrity = defaultArg integrity integrity_policy_set.empty_writers_set with get
        member val loc = defaultArg loc uloc with get, set

        member self.principals = 
            let set = match secrecy with Some s -> s.principals | None -> Set.empty
            Set.toList (Set.union set (match integrity with Some i -> i.principals | None -> Set.empty))


        /// The conjunction of two labels ensures that both policies are enforced. An information flow then becomes valid only
        /// if both owners permit it. Secrecy policies are joined, while integrity policies are met.
        abstract member conjunction : label -> label
        default self.conjunction (lb : label) = 
            new label (self.secrecy.join lb.secrecy, self.integrity.meet lb.integrity, self.loc)

//        /// Conjugates the label with the given list of labels, assuring that all policies are enforced. An information flow then becomes valid only
//        /// if both owners permit it. Secrecy policies are joined, while integrity policies are met.
//        member self.conjunction (lbs : label list) =
//            List.fold (fun (lb1 : label) (lb2 : label) -> lb1.conjunction lb2) self lbs

        /// The disjunction of two labels permits every information flow permitted by at least one of the owners. Thus, secrecy
        /// policies are met while integrity policies are joined.
        abstract member disjunction : label -> label
        default self.disjunction (lb : label) =
            new label (self.secrecy.meet lb.secrecy, self.integrity.join lb.integrity, self.loc)

//        /// The disjunction of a list of labels permits every information flow permitted by at least one of the owners. Thus, 
//        /// secrecy policies are met while integrity policies are joined.
//        member self.disjunction (lbs : label list) =
//            List.fold (fun (lb1 : label) (lb2 : label) -> lb1.disjunction lb2) self lbs
            
        /// <summary>Tells whether or not the first label is a subtype of the second. A label lb1 is considered a subtype
        ///     of a label lb2 if and only if the set of readers of lb1 is a superset of the set of readers of lb2 and, dually,
        ///     if the set of writers of lb1 is a subset of the set of writers of lb2. </summary>
        /// <param name="lb1">The subtype label.</param>
        /// <param name="lb2">The supertype label.</param>
        /// <returns>True if the first label is a subtype of the second.</returns>
        member self.is_subtype (lb: label) hierarchy =
            let secrecy_covered = self.secrecy.is_covered_by lb.secrecy hierarchy
            let integrity_covered = self.integrity.is_covered_by lb.integrity hierarchy
            secrecy_covered && integrity_covered

        member self.pretty =
            sprintf "{%s ; %s}" self.secrecy.pretty self.integrity.pretty


    type array_label (variable_label : label, ?type_label : array_label, ?loc : location) =
        inherit label (secrecy = variable_label.secrecy, integrity = variable_label.integrity, ?loc = loc)
        member val var_lb = variable_label with get
        member val type_lb = type_label with get
        override self.conjunction (lb : label) =
            match self.type_lb with
                | Some blb -> 
                    new label ((self.secrecy.join blb.secrecy).join lb.secrecy, 
                               (self.integrity.meet blb.integrity).meet lb.integrity, self.loc)
                | None -> new label (self.secrecy.join lb.secrecy, self.integrity.meet lb.integrity, self.loc)
        override self.disjunction (lb : label) =
            match self.type_lb with
                | Some blb -> 
                    new label ((self.secrecy.meet blb.secrecy).meet lb.secrecy, 
                               (self.integrity.join blb.integrity).join lb.integrity, self.loc)
                | None -> new label (self.secrecy.meet lb.secrecy, self.integrity.join lb.integrity, self.loc)


    let bottom_label = new label (Bottom)    
    let top_label = new label (Top)     




    (*type annotation =
        | Label of label
        | PrincipalDecl of principal list
        | Declassify of id
        | Endorse of id*)

//    let pretty_label (lb : label) = 
//        match (lb.secrecy, lb.integrity) with
//            | Some pset1, Some pset2 -> sprintf "%s; %s" (pretty_reader_policy_set pset1) (pretty_writer_policy_set pset2)
//            | Some pset, None        -> pretty_reader_policy_set pset
//            | None, Some pset        -> pretty_writer_policy_set pset
//            | None, None             -> ""




(*
 * Java AST
 *)

module Java =

    type id = string

    type [< AbstractClass >] node<'tag> (loc : location, ?tag : 'tag) =
        member self.is_tagged = Option.isSome self.tag
        member val tag = tag with get, set
        member val location = loc with get

        abstract relocate_filename : string -> unit
        default self.relocate_filename filename =
            if self.location.filename = "" then self.location.filename <- filename

        static member internal relocate_filename_in_nodes filename (nodes : seq<#node<_>>) =
            for n in nodes do n.relocate_filename filename

        abstract pretty : string
        default self.pretty = self.ToString ()

        abstract pretty_localized : string
        default self.pretty_localized = sprintf "[@%s]%s" loc.pretty (soprintf " [%O]" tag)        

    type locatable<'a, 'tag> (value : 'a, loc : location, ?tag : 'tag) =
        inherit node<'tag> (?tag = tag, loc = loc)
        member val value = value with get
        override self.pretty = sprintf "%O" value
        override self.pretty_localized = sprintf "%O %s" value base.pretty_localized
        override self.ToString () = self.pretty

    

    (* types *)

    type ty_builtin =
        | Ty_Int
        | Ty_Long
        | Ty_Bool
        | Ty_Float
        | Ty_Double
        | Ty_Short
        | Ty_Byte
        | Ty_Char
        | Ty_Bottom
    with
        member self.pretty =
            match self with
                | Ty_Int    -> "int"
                | Ty_Long   -> "long"
                | Ty_Bool   -> "bool"
                | Ty_Float  -> "float"
                | Ty_Double -> "double"
                | Ty_Short  -> "short"
                | Ty_Byte   -> "byte"
                | Ty_Char   -> "char"
                | Ty_Bottom -> "NullType"

    type ty =
        | Ty_Builtin of ty_builtin
        | Ty_Id of id
        | Ty_Sel of ty * id
        | Ty_App of ty * ty_arg list
        | Ty_Array of ty
    with
        static member of_qid (qid : qid) =
            let a = qid.parts
            in
                Array.fold (fun ty id -> Ty_Sel (ty, id)) (Ty_Id a.[0]) a.[1 .. Array.length a - 1]

        member self.apply_subst subst =
            let rec R = function
                | Ty_Array ty -> Ty_Array (R ty)

                | Ty_Id id as r ->
                    match List.tryFind (fun (id', _) -> id = id') subst with
                        | Some (_, ty) -> ty
                        | None         -> r
                
                | Ty_Sel (ty, id) -> Ty_Sel (R ty, id)

                | Ty_App (ty, tyargs)  ->
                    let f = function
                        | TyArg_Ty argty               -> TyArg_Ty (R argty)
                        | TyArg_Wildcard (rel, parent) -> TyArg_Wildcard (rel, R parent)
                    in
                        Ty_App (R ty, List.map f tyargs)

                | Ty_Builtin _ as ty -> ty
            in
                R self

//        member self.apply_ty_args tyargs =
//            let subst = List.map2 (fun (p : ty_param) (ty : ty) -> p.name, ty) ty_params tyargs
//            in
//                  List.map (fun (ty : ty) -> ty.apply_subst subst) extends

        member self.reifiable =
            let rec R = function
                | Ty_Id id        -> new qid ([|id|])
                | Ty_Array _      -> SQId Config.Java.Names.Type.Array
                | Ty_App (ty, _)  -> R ty
                | Ty_Sel (ty, id) -> (R ty).append id

                | Ty_Builtin b ->
                    SQId 
                        (match b with
                            | Ty_Bottom -> Config.Java.Names.Type.Null                
                            | Ty_Int    -> Config.Java.Names.Type.Integer
                            | Ty_Bool   -> Config.Java.Names.Type.Boolean
                            | Ty_Long   -> Config.Java.Names.Type.Long
                            | Ty_Float  -> Config.Java.Names.Type.Float
                            | Ty_Double -> Config.Java.Names.Type.Double
                            | Ty_Short  -> Config.Java.Names.Type.Short
                            | Ty_Byte   -> Config.Java.Names.Type.Byte
                            | Ty_Char   -> Config.Java.Names.Type.Char)
            in
                R self

        member self.pretty = 
            match self with
                | Ty_Id id          -> id
                | Ty_Sel (ty, id)   -> sprintf "%s.%s" ty.pretty id
                | Ty_Builtin b      -> b.pretty
                | Ty_Array ty       -> sprintf "%s[]" ty.pretty
                | Ty_App (ty, args) -> sprintf "%s<%s>" ty.pretty (mappen_strings (fun (a : ty_arg) -> sprintf "%s" a.pretty) ", " args)

        override self.ToString () = self.pretty

    and ty_reifiable = Ty_Reifiable of ty
    with
        member self.pretty = match self with Ty_Reifiable ty -> ty.pretty
        override self.ToString () = self.pretty
        static member of_ty (t : ty) = Ty_Reifiable (ty.of_qid t.reifiable)

    and ty_arg =
        | TyArg_Ty of ty
        | TyArg_Wildcard of ty_arg_rel * ty
    with
        member self.pretty =
            match self with
                | TyArg_Ty ty -> ty.pretty
                | TyArg_Wildcard (r, ty) -> sprintf "%s %s" r.pretty ty.pretty

    and ty_arg_rel = Extends | Super
    with
        member self.pretty =
            match self with
                | Extends -> "extends"
                | Super   -> "super"

    and [< NoComparison >] ty_param = {
        name        : id
        parent      : ty
        interfaces  : ty list
    }        

    (* shortcuts *)

    let rec (|Ty_QId|_|) = function
        | Ty_Sel (ty, id) ->
            match ty with
                | Ty_QId (qid : qid) -> Some (qid.append id)
                | _                  -> None
        | _ -> None

    let Ty_QId = ty.of_qid

    let (|Ty_SQId|_|) s = function
        | Ty_QId (SQId s) -> Some ()
        | _               -> None

    let Ty_SQId s = Ty_QId (SQId s)

    let private Ty_Class s = Ty_SQId s, (function Ty_SQId s -> Some () | _ -> None)

    let Ty_String, (|Ty_String|_|) = Ty_Class Config.Java.Names.Type.String
    let Ty_Object, (|Ty_Object|_|) = Ty_Class Config.Java.Names.Type.Object


    (* java modifiers *)

    type visibility = Private | Public | Protected | Package

    and [< AbstractClass >] basic_modifiers (?final) =
        member val final = defaultArg final false with get

    and param_modifiers (?final) =
        inherit basic_modifiers (?final = final)

    and decl_modifiers (?staticc, ?final) =
        inherit basic_modifiers (?final = final)
        member val staticc = defaultArg staticc false with get

    and [< AbstractClass >] member_modifiers (?staticc, ?final, ?visibility) =
        inherit decl_modifiers (?staticc = staticc, ?final = final)
        member val visibility = defaultArg visibility Package with get

    and attribute_modifiers (?staticc, ?final, ?visibility) =
        inherit member_modifiers (?staticc = staticc, ?final = final, ?visibility = visibility)

    and class_modifiers (?staticc, ?final, ?visibility, ?abstractt, ?strictfp) =
        inherit member_modifiers (?staticc = staticc, ?final = final, ?visibility = visibility)
        member val abstractt = defaultArg abstractt false with get
        member val strictfp = defaultArg strictfp false with get

    and method_modifiers (?staticc, ?final, ?visibility, ?abstractt, ?strictfp, ?native, ?synchronized) =
        inherit class_modifiers (?staticc = staticc, ?final = final, ?visibility = visibility, ?abstractt = abstractt, ?strictfp = strictfp)
        member val native = defaultArg native false with get
        member val synchronized = defaultArg synchronized false with get

    and constructor_modifiers (?visibility, ?strictfp, ?native, ?synchronized) =
        inherit method_modifiers (staticc = true, final = false, ?visibility = visibility, ?strictfp = strictfp, ?native = native, ?synchronized = synchronized)


    (* java language constructs *)
    
    type annotation (name : id, bindings : (id * lit) list, loc : location) =
        inherit node<obj> (loc = loc)
        member val name = name with get
        member val bindings = bindings with get
        override self.pretty = sprintf "@%s(%s) %s" name (mappen_strings (fun (id, lit) -> sprintf "%s = %O" id lit) "," bindings) base.pretty

    and annotations = annotation list

    and [< AbstractClass >] basic_annotated<'tag> (loc : location, ?annots : annotations, ?tag : 'tag) =
        inherit node<'tag> (?tag = tag, loc = loc)
        member val annots = defaultArg annots [] with get
        abstract member what : string

    and [< AbstractClass >] named_annotated<'modif, 'id> (modif : 'modif, name : 'id, loc : location, ?annots : annotations) =
        inherit basic_annotated<obj> (loc = loc, ?annots = annots)
        member val modif = modif with get
        member val name = name with get
          
    and param (modif : param_modifiers, name : id, ty : ty, loc : location, ?annots : annotations) =
        inherit named_annotated<param_modifiers, id> (modif, name, loc = loc, ?annots = annots)
        member val ty = ty with get
        override self.what = "param"
        override self.pretty = name

    and [< AbstractClass >] memberr<'modif when 'modif :> member_modifiers> (modif : 'modif, name : id, loc : location, ?annots : annotations) =
        inherit named_annotated<'modif, id> (modif, name, loc = loc, ?annots = annots)
         
    and attribute (modif : attribute_modifiers, name : id, ty : ty, loc : location, ?expr : expr, ?annots : annotations) =
        inherit memberr<attribute_modifiers> (modif, name, loc = loc, ?annots = annots)
        member val ty = ty with get
        member val expr = expr with get
        override self.what = "attribute"

    and method_signature (modif : method_modifiers, name : id,
                          ty_params : ty_param list, rty : ty option, paramss : param list,
                          throws : ty list, loc : location, ?annots : annotations) =
        inherit memberr<method_modifiers> (modif = modif, name = name, loc = loc, ?annots = annots)
        member val ty_params = ty_params with get
        member val rty = rty with get
        member val paramss = paramss with get
        member val throws = throws with get
        override self.what = "method"

    and methodd (modif : method_modifiers, name : id, body : block,
                 ty_params : ty_param list, rty : ty option, paramss : param list,
                 throws : ty list, loc : location, ?annots : annotations) =
        inherit method_signature (modif = modif, name = name, loc = loc, ty_params = ty_params, rty = rty, paramss = paramss, throws = throws, ?annots = annots)
        member val body = body with get
        new (method_signature as super : method_signature, body : block) =
            new methodd (super.modif, super.name, body, super.ty_params, super.rty, super.paramss, super.throws, super.location, super.annots)
        

    and constructorr (modif : constructor_modifiers, name : id, body : block,
                      ty_params, paramss : param list, throws : ty list,
                      loc : location, ?annots : annotations) =
        inherit methodd (modif, name = name, loc = loc, body = body, ty_params = ty_params,
                         rty = Some (Ty_Id name), paramss = paramss, throws = throws, ?annots = annots)
        override self.what = "constructor"
    
    and [< AbstractClass >] class_signature (modif : class_modifiers, name : id,
                                             extends : ty list, ty_params : ty_param list,
                                             attributes : attribute list,
                                             inner_classes : classs list, inner_interfaces : interfacee list,
                                             loc : location, ?annots : annotations) =
        inherit named_annotated<class_modifiers, id> (modif, name, loc = loc, ?annots = annots)
//        member self.qid = new qid ([|self.name|])
        member val ty_params = ty_params with get
        member val inner_classes = inner_classes with get
        member val inner_interfaces = inner_interfaces with get

        member self.inner_class_signatures =
            Seq.toList <| seq { for cl in self.inner_classes do yield (cl :> class_signature);
                                for i in self.inner_interfaces do yield (i :> class_signature) }

        abstract method_signatures : method_signature list with get
        member val attributes = attributes with get

        member self.super_tys = extends

        member self.super_ty = extends.[0]
        
//        member self.super_tys tyargs =
//            let subst = List.map2 (fun (p : ty_param) (ty : ty) -> p.name, ty) ty_params tyargs
//            in
//                List.map (fun (ty : ty) -> ty.apply_subst subst) extendsmember self.super_tys tyargs =
            

//        member self.super_qids = List.map (fun (ty : ty) -> ty.reifiable) extends

        override self.relocate_filename filename =
            node<_>.relocate_filename_in_nodes filename self.inner_class_signatures
            node<_>.relocate_filename_in_nodes filename self.method_signatures

    and class_body (attributes : attribute list, methods : methodd list, constructors : constructorr list,                
                    inner_classes : classs list, inner_interfaces : interfacee list,
                    initializer : block, static_initializer : block,
                    loc : location) =
        inherit node<obj> (loc = loc)
        member val attributes = attributes with get
        member val methods = methods with get
        member val constructors = constructors with get
        member val initializer = initializer with get
        member val static_initializer = static_initializer with get
        member val inner_classes = inner_classes with get
        member val inner_interfaces = inner_interfaces with get

    and classs (modif : class_modifiers, name : id,
                ty_params : ty_param list, extends : ty option, implements : ty list,
                attributes : attribute list, methods : methodd list, constructors : constructorr list,                
                inner_classes : classs list, inner_interfaces : interfacee list,
                initializer : block, static_initializer : block,
                loc : location, ?annots : annotations) =

        inherit class_signature (modif, name, extends = List.concat [(match extends with Some x -> [x] | None -> []) ; implements] ,
                                 ty_params = ty_params, inner_classes = inner_classes, attributes = attributes,
                                 inner_interfaces = inner_interfaces, loc = loc, ?annots = annots)
        member val implements = implements with get
        member val initializer = initializer with get
        member val static_initializer = static_initializer with get
        member val methods = methods with get
        member val constructors = constructors with get
//        member self.parent_qid = List.head self.super_qids

//        member self.methods_with_constructors = Seq.toList <| seq { for m in self.methods do yield m; for c in self.constructors do yield (c :> methodd) }

        override self.what = "class"
        override self.method_signatures = Seq.toList <| seq { for m in self.methods do yield m :> method_signature }

        override self.relocate_filename filename =
            base.relocate_filename filename
            node<_>.relocate_filename_in_nodes filename self.initializer
            node<_>.relocate_filename_in_nodes filename self.static_initializer
            node<_>.relocate_filename_in_nodes filename self.constructors

        new (modif : class_modifiers, name : id, ty_params : ty_param list, extends : ty option, implements : ty list,
             body : class_body, ?annots : annotations) =
            new classs (modif = modif, name = name, ty_params = ty_params, extends = extends, implements = implements,
                        attributes = body.attributes, methods = body.methods, constructors = body.constructors, 
                        inner_classes = body.inner_classes, inner_interfaces = body.inner_interfaces,
                        initializer = body.initializer, static_initializer = body.static_initializer,
                        loc = body.location, ?annots = annots)

    and interfacee (modif : class_modifiers, name : id,
                    ty_params : ty_param list, extends : ty list,
                    attributes : attribute list,
                    method_signatures : method_signature list,
                    inner_classes : classs list, inner_interfaces : interfacee list,
                    loc : location, ?annots : annotations) =
        inherit class_signature (modif, name, extends = extends, ty_params = ty_params, attributes = attributes,
                                 inner_classes = inner_classes, inner_interfaces = inner_interfaces,
                                 loc = loc, ?annots = annots)
        override self.method_signatures = method_signatures
        override self.what = "interface"
       
    and compilation_unit (filename : string, package : fqid, public_class_name : string, imports : fqid list, 
                          classes : classs list, interfaces : interfacee list) =
        do
            node<_>.relocate_filename_in_nodes filename classes
            node<_>.relocate_filename_in_nodes filename interfaces

        member val package = package with get
        member val imports = (List.map fqid.of_string Config.Java.implicit_imports) @ imports with get
        member val public_class_name = public_class_name with get
        member val classes = classes with get
        member val interfaces = interfaces with get
        member self.filename = sprintf "%s.java" self.public_class_name
        member self.public_class_fqid = self.package.append self.public_class_name

    and permission (description : string, icon : string, label : string, name : string, group : string, 
                    level : string) =
        member val description = description with get
        member val icon = icon with get
        member val label = label with get
        member val name = name with get
        member val group = group with get
        member val level = level with get
        
    and manifest (uses_permissions : string list,
                  defines_permissions : permission list,
                  calling_permissions : (fqid * string) list) =
        member val uses_permissions = uses_permissions with get
        member val calling_permissions = List.fold (fun m (fqid, s) -> Map.add fqid s m) Map.empty calling_permissions with get
        // TODO: nobody checks whether user-defined permissions truly belongs to this set
        member val defines_permissions = defines_permissions with get

    and program (compilation_units : compilation_unit list, manifest : manifest, implicit_imports : fqid list) = 
        member val compilation_units = compilation_units with get
        member val manifest = manifest with get
        member val implicit_imports = implicit_imports with get


    (* statements *)

//    and annotable<'a, 'tag> (value : 'a, loc : location, ?tag : 'tag, ?annots : annotations) =
//        inherit basic_annotated<'tag> (?tag = tag, ?annots = annots, loc = loc)
//        member val value = value with get

    and statement = locatable<statement', obj>

    and [<NoComparison>] statement' =
        | Decl of  decl_modifiers * decl * expr option
        | StatementExpr of expr
        | Assign of expr * expr
        | Return of expr option
        | Throw of expr
        | If of expr * block * block option
        | While of expr * block
        | DoWhile of block * expr
        | For of statement option * expr option * statement option * block
        | ForEach of decl * expr * block
        | Try of block * catch_block list * block option
        | Switch of expr * switch_case list * block option
        | Break of id option
        | Continue of id option
        | ThisCons of actuals
        | SuperCons of actuals
        | Assert of expr * expr option
        | Labeled of id * statement
    with
        member self.pretty = 
            match self with
                | Decl (_, (ty, id, _), eo) -> sprintf "%O %s%s" ty id (soprintf " = %O" eo)
                | StatementExpr e -> sprintf "%O" e
                | Assign (e1, e2) -> sprintf "%O = %O" e1 e2
                | Return e -> sprintf "return %O" e
                | Throw e -> sprintf "throw %O" e
                | If (e, _, bo) -> sprintf "if (%O) {..}%s" e (if bo.IsSome then " else {..}" else "")
                | While (e, _) -> sprintf "while (%O) {..}" e
                | DoWhile (_, e) -> sprintf "do {..} while (%O)" e
                | For (st1o, e, st2o, _) -> sprintf "for (%s; %O; %s) {..}" (soprintf "%O" st1o) e (soprintf "%O" st2o)
                | ForEach ((ty, id, _), e, _) -> sprintf "for (%O %s : %O) {..}" ty id e
                | Try (b, cbs, fbo) ->
                     sprintf "try {..} %s%s"
                        (mappen_strings (fun (p : param, _) -> sprintf "catch (%O %s) {..}" p.ty p.name) " " cbs)
                        (if fbo.IsSome then " finally {..}" else "")
                | Switch (e, cs, defbo) ->
                    sprintf "switch (%O) %s%s" e
                        (mappen_strings (fun (e, _) -> sprintf "case %O: {..}" e) "; " cs)
                        (if defbo.IsSome then " default: {..}" else "")
                | Break ido -> sprintf "break%s" (soprintf "%s" ido)
                | Continue ido -> sprintf "continue%s" (soprintf "%s" ido)
                | ThisCons acs -> sprintf "this%s" (expr'.pretty_actuals acs)
                | SuperCons acs -> sprintf "super%s" (expr'.pretty_actuals acs)
                | Assert (e, eo) -> sprintf "assert %O%s" e (soprintf " : %O" eo)
                | Labeled (id, st) -> sprintf "%s: %O" id st

        override self.ToString () = self.pretty


    (* expressions and literals *)

    and expr = locatable<expr', obj>

    and [<NoComparison>] expr' = 
        | This
        | Lit of lit
        | Var of id
        | Cast of ty * expr
        | MemberSel of member_sel
        | Subscript of expr * expr
        | Cons of ty * actuals * class_body option
        | Cond of expr * expr * expr
        | BinOp of expr * bin_op * expr
        | UnOp of un_op * expr
    with
        static member pretty_actuals (acs : actuals) =
            let p f =
                match acs with
                    | [], args -> sprintf "(%s)" (f args)
                    | tys, args -> sprintf "<%s>(%s)" (mappen_strings (sprintf "%O") ", " tys) (f args)
            in
                p (mappen_strings (sprintf "%O") ", ")

        member self.pretty =
            match self with
                | This -> "this"
                | Lit l -> sprintf "%O" l
                | Var x -> x
                | Cast (ty, e) -> sprintf "(%s) %s" ty.pretty e.pretty
                | MemberSel (recp, id, acso) -> sprintf "%s.%s%s" recp.pretty id (something expr'.pretty_actuals "" acso)
                | Subscript (e1, e2) -> sprintf "%s[%s]" e1.pretty e2.pretty
                | Cons (ty, acs, bo) -> sprintf "new %s%s%s" ty.pretty (expr'.pretty_actuals acs) (if bo.IsSome then " { .. }" else "")
                | Cond (e1, e2, e3) -> sprintf "(%s ? %s : %s)" e1.pretty e2.pretty e3.pretty
                | BinOp (e1, op, e2) -> sprintf "(%s %O %s)" e1.pretty op e2.pretty
                | UnOp (op, e) -> sprintf "%O (%s)" op e.pretty

        override self.ToString () = self.pretty

    and [<NoComparison>] lit = 
        | Int of int32
        | Long of int64
        | Char of char
        | Float of single
        | Double of double
        | Bool of bool
        | String of string
        | Array of ty * expr list
        | ClassOp of qid
        | Null
    with
        member self.pretty =
            match self with
                | Int n -> sprintf "%d" n
                | Long n -> sprintf "%d" n
                | Char c -> sprintf "%c" c
                | Float x -> sprintf "%g" x
                | Double x -> sprintf "%g" x
                | Bool true -> "true"
                | Bool false -> "false"
                | String s -> sprintf "\"%s\"" s 
                | Array (ty, es) -> sprintf "new %O[] { %s }" ty (mappen_strings (sprintf "%O") ", " es)
                | ClassOp tyr -> sprintf "%s.class" tyr.pretty
                | Null -> "null"
    
        override self.ToString () = self.pretty

    and bin_op =
        | Plus | Minus | Mult | Div | Mod    // arithmetic
        | AShR                               // arithmetic shift
        | ShL | ShR                          // bitwise shift 
        | And | Or | Xor                     // bitwise logic
        | Eq | Neq | Lt | Gt | Leq | Geq     // relational
        | LAnd | LOr                         // logic
    with
        member self.pretty =
            match self with
                | Plus -> "+"
                | Minus -> "-"
                | Mult -> "*"
                | Div -> "/"
                | Mod -> "%"
                | AShR -> ">>>"
                | ShR -> ">>"
                | ShL -> "<<"
                | And -> "&"
                | Or -> "|"
                | Xor -> "^"
                | Eq -> "=="
                | Neq -> "!="
                | Lt -> "<"
                | Gt -> ">"
                | Leq -> "<="
                | Geq -> ">="
                | LAnd -> "&&"
                | LOr -> "||"

        override self.ToString () = self.pretty

    and un_op =
        | Neg                   // arithmentic unary negate
        | Not                   // logic not
        | BNot                  // binary not
        | PreInc | PostInc
        | PreDec | PostDec
    with
        member self.pretty =
            match self with
                | Neg -> "-"
                | Not -> "!"
                | BNot -> "~"
                | PreInc -> "++."
                | PreDec -> "--."
                | PostDec -> ".--"
                | PostInc -> ".++"
            
        override self.ToString () = self.pretty

    and member_sel = recipient * id * actuals option    

    and [< NoComparison >] recipient =
        | Recp_Obj of expr
        | Recp_Super
    with
        member self.pretty =
            match self with
                | Recp_Obj e -> e.pretty
                | Recp_Super -> "super"

        override self.ToString () = self.pretty

    and actuals = ty_arg list * expr list

    and decl = ty * id * annotations
    
    and catch_block = param * block

    and switch_case = expr * block

    and block = statement list

    
    (* active patterns & shotcuts *)      

    let (|New|_|) = function
        | Cons (ty, acs, None) -> Some (ty, acs)
        | _                    -> None

    let (|AnonymousClass|_|) = function
        | Cons (ty, acs, Some b) -> Some (ty, acs, b)
        | _                      -> None

    let Locatable (x : 'a, loc) = new locatable<'a, obj> (x, loc = loc)
    let (|Locatable|) (l : locatable<'a, 'tag>) = (l.value, l.location)

    let (|UL|) = function Locatable (x, _) -> x
    let UL x = Locatable (x, new location (-1, -1))

    let Call (e, id, tyargs, args) = (Recp_Obj e, id, Some (tyargs, args))
    let Sel (e, id) = (Recp_Obj e, id, None)
    let SuperCall (id, tyargs, args) = (Recp_Super, id, Some (tyargs, args))
    let SuperSel (id) = (Recp_Super, id, None)

    let ThisSel (id, loc) = Locatable (MemberSel (Sel (Locatable (This, loc), id)), loc)

    let (|Call|Sel|SuperCall|SuperSel|) = function
        | Recp_Obj e, id, Some (tyargs, args)    -> Call (e, id, tyargs, args)
        | Recp_Obj e, id, None                   -> Sel (e, id)
        | Recp_Super, id, Some (tyargs, args)    -> SuperCall (id, tyargs, args)
        | Recp_Super, id, None                   -> SuperSel id

    let (|ArithBinOp|LogicBinOp|RelBinOp|) = function
        | Plus | Minus | Div | Mult | Mod
        | ShL | ShR | AShR | And | Or | Xor -> ArithBinOp
        | LAnd | LOr                        -> LogicBinOp
        | Eq | Neq | Lt | Gt | Leq | Geq    -> RelBinOp

    let (|ArithUnOp|LogicUnOp|) = function
        | Neg | BNot
        | PreInc | PostInc
        | PreDec | PostDec  -> ArithUnOp
        | Not               -> LogicUnOp

    let (|MethodSignature|) (meth : methodd) = meth.name, meth.rty, List.map (fun (par : param) -> par.ty, par.name) meth.paramss


(*
 * External AST
 *)

module X =

    type perm_expr =
        | P_Id of id
        | P_Or of perm_expr * perm_expr
        | P_And of perm_expr * perm_expr
    with
        member self.flatten =
            match self with
                | P_Id id        -> [id]
                | P_Or (e1, _)   -> e1.flatten
                | P_And (e1, e2) -> e1.flatten @ e2.flatten

    type [< NoComparison >] api_call =
      {
        class_fqid       : fqid
        method_signature : Java.method_signature
        call_perms       : string list
      }

    type implicit_call =
      {
        action_string : string
        call_perms    : string list
      }


(* parser auxiliary utilities *)

module ParseAux =
    module J = Java

    let rec build_tyarray_from_dims ty = function | 0 -> ty | n -> J.Ty_Array (build_tyarray_from_dims ty (n - 1))

    let build_class_modifs visib (mods: bool array) =
        J.class_modifiers (mods.[0], mods.[1], visib, mods.[3], mods.[2])

    let build_method_modifs visib (mods: bool array) =
        J.method_modifiers (mods.[0], mods.[1], visib, mods.[2], mods.[3], mods.[4], mods.[5])

    let build_constr_modifs visib (mods: bool array) =
        J.constructor_modifiers (visib, mods.[3], mods.[4], mods.[5])

    let build_attr_modifs visib (mods: bool array) =
        J.attribute_modifiers (mods.[0], mods.[1], visib)

    let build_decl_modifiers (mods: bool array) =
        J.decl_modifiers (mods.[0], mods.[1])

    let build_param_modifs (mods: bool array) =
        J.param_modifiers (mods.[1])

    let rebuild_type_from_parts =
        let f = function
            | [] -> unexpected "rebuild_type: empty type parts"
            | [id, []]   -> J.Ty_SQId id
            | [id, args] -> J.Ty_App (J.Ty_SQId id, args)
            | idargss ->
                let a = List.toArray idargss
                let ids = Array.fold (fun ids (id, args) -> id :: ids) [] a.[0 .. a.Length - 2]
                let id0, args0 = a.[a.Length - 1]
                let qid = new qid (ids |> List.rev |> List.toArray, id0)
                in
                    match args0 with
                        | []    -> J.Ty_QId qid
                        | args  -> J.Ty_App (J.Ty_QId qid, args)
        in
            fun dims idargss -> build_tyarray_from_dims (f idargss) dims

    let build_attr (vis, modifs, id, ty, eo, anns, loc) =
        match eo with
            | Some expr -> J.attribute (modif = build_attr_modifs vis modifs, name = id, ty = ty, expr = expr, loc = loc, annots = anns)
            | None      -> J.attribute (modif = build_attr_modifs vis modifs, name = id, ty = ty, loc = loc, annots = anns)

    let build_param (vis, modifs, id, ty, eo, anns, loc) =
        J.param (modif = build_param_modifs modifs, name = id, ty = ty, loc = loc, annots = anns)


    // external file stuff

    let build_x_method_signature (qid : qid) argtys rtyo (parseState : Parsing.IParseState) =
        let p, pe = parseState.ResultRange
        let loc0 = new location (line = p.Line, col = p.Column, (*end_line = pe.Line, end_col = pe.Column,*) filename = p.FileName)
        let paramss = List.map (fun ty -> new J.param (modif = new J.param_modifiers (), name = "", ty = ty, loc = loc0)) argtys
        let m =
            new J.method_signature (modif = new J.method_modifiers (), name = qid.id, ty_params = [], rty = rtyo, paramss = paramss,
                                       throws = [], loc = loc0)
        in
            new qid (qid.prefixes), m
