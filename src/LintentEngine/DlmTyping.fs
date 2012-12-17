(*
 * TypeDroid - LintentEngine
 * DlmTyping.fs: DLM type checker
 * (C) 2012 Alessandro Frazza, Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)


#light

module LintentEngine.Typing.Dlm

open System
open System.Text.RegularExpressions
open FSharpCommon.Prelude
open FSharpCommon.Log
open FSharpCommon
open LintentEngine
open LintentEngine.Absyn

module J = Java
module TJ = Typing.Java
module LF = LintFeedback
module LFI = LintFeedback.Issue


/// Defines the type of the errors to be thrown.
type type_error (msg, pri, loc, issue) =
    inherit Typing.Android.type_error (msg, pri, loc, issue)
    
(* 
 * ----------------------------------------
 *
 * Error reporting module
 *
 * ----------------------------------------
 *)

 
module Report =

    let internal t issue = Typing.Android.Report.t issue
    let inline internal log f = Typing.Android.Report.log f
    let inline internal w issue = Typing.Android.Report.w issue
    let inline internal h (loc : location) = Typing.Android.Report.h loc
    let trapped = Typing.Android.Report.trapped

let inline unexpected (loc : location) fmt =  Globals.reporter.report_unexpected loc fmt

module Error = 
    open Report
   
    let lack_of_authority (meth : J.method_signature) (required_auths : Set<Dlm.principal>) expanded_auths loc =
        let msg = sprintf "missing authorities: %s" (Dlm.pretty_principals <| Set.difference required_auths expanded_auths)
        t LFI.Annotation loc Unmaskerable "caller lacks required authority in order to call method %s: %s" meth.pretty msg

    let multiple_annotation (names : J.id list) where pretty_printed loc =
        let msg = sprintf "ambiguous multiple annotations on %s found among the followings: %s" where (flatten_strings ", " names)
        in
            Globals.logger.debug Normal "%s" pretty_printed;
            t LFI.Annotation loc Unmaskerable "%s" msg

    let non_unary_annotation (annot : J.annotation) = 
        t LFI.Annotation annot.location Unmaskerable "multiple binding in annotation %s" annot.name

    let subtype_error where loc what (e1 : string) e2 (lb1 : Dlm.label) (lb2 : Dlm.label) = 
        let msg = sprintf "illegal %s '%s': \n%s %s is more restrictive than %s %s, thus producing an illegal flow." what where e1 (lb1.pretty) e2 (lb2.pretty)
        t LFI.InformationFlow loc Unmaskerable "%s" msg

    let principal_annot_bad_format (loc : location) = 
        t LFI.Annotation loc Unmaskerable "non-string literal in array of principals"

    let principal_unknown (loc : location) (principal : Dlm.principal) (lb : Dlm.label) =
        t LFI.Annotation loc Unmaskerable "'%s' in label '%s' is neither a principal nor a variable" principal.pretty lb.pretty

    let policy_set_bad_format pset_pretty (loc: location) = unexpected loc "policy set %s is neither a Join nor a Meet" pset_pretty

module Warning =
    open Report


    let used_array_label_with_base_type (loc : location) (ty : J.ty) =
        w LFI.Annotation loc High "supplied annotation for an array-type label but declared base type '%s'" ty.pretty
//    let used_array_label_with_base_type (annot : J.annotation) (ty : J.ty) =
//        w LFI.Annotation annot.location High "declared an array label in annotation '%s' for the base type '%s'" annot.pretty ty.pretty


(* 
 * ----------------------------------------
 *
 * Label defaults module.
 *
 * ----------------------------------------
 *)

module Defaults =
    
    let begin_label = Dlm.top_label
    let parameter_label = Dlm.bottom_label

    let return_label (par_lbs : Lazy<Dlm.label> list) = 
        List.fold (fun (lb1 : Dlm.label) lb2 -> lb1.conjunction lb2) Dlm.bottom_label 
                            (List.map (fun (lb : Lazy<Dlm.label>) -> lb.Value) par_lbs)    

    let attribute_label = Dlm.bottom_label
    let unannotated_array_label = new Dlm.array_label (Dlm.bottom_label, new Dlm.array_label (Dlm.bottom_label))
    let unannotated_decl_label = Dlm.bottom_label



(* 
 * ----------------------------------------
 *
 * Miscellanous utility functions.
 *
 * ----------------------------------------
 *)

module Utilities =

    open Dlm
    
    /// <summary>Creates a list of principals from a set of literals, may it be made up by a string or an array of strings.</summary>
    /// <param name="loc">The location of the set of literals in the original source file, to be used in case of bad formatting of
    ///     the literals themselves.</param>
    /// <param name="lits">The set of literals from which the principal list has to be created. It can consists in either a string
    ///     or an array of strings.</param>
    /// <return>A list of principals.</return>
    let create_principals_from loc lits = 
        let f = function 
            | (J.UL (J.Lit (J.String s)))   -> Principal s
            | _                             -> Error.principal_annot_bad_format loc
        in
            match lits with
                | J.String s        -> [Principal s]
                | J.Array (_, es)   -> List.map f es
                | _                 -> Error.principal_annot_bad_format loc
    
    let trap f (x : #J.node<_>) st =
        try f x st
        with e ->
            Report.trapped x.location e x
            (), st


       


(* 
 * ----------------------------------------
 *
 * Active Patterns recognizer module.
 *
 * ----------------------------------------
 *)

module Detector =

    open Utilities
    open Dlm

    let (|UnaryAnnotationBinding|) (annot : J.annotation) =
        match annot.bindings with
            | ["value", lit] -> lit
            | _              -> Error.non_unary_annotation annot


    let (|MultipleUnaryAnnotations|_|) names annots =
        match List.filter (fun (annot : J.annotation) -> List.exists (fun s -> s = annot.name) names) annots with
            | []        -> None
            | anns      -> Some (List.map (function UnaryAnnotationBinding lit -> lit) anns)


    let (|UnaryAnnotation|_|) names (a : J.basic_annotated<_>) = 
        match a.annots with 
        | MultipleUnaryAnnotations names [lit]          -> Some lit
        | MultipleUnaryAnnotations names (head :: tail) -> Error.multiple_annotation names a.pretty a.what a.location
        | _                                             -> None
        

    let (|UnaryStringAnnotation|_|) names = function
        | UnaryAnnotation names (J.String s)    -> Some s
        | _                                     -> None


    let (|UnaryDlmLabelAnnotation|_|) names = function
        | UnaryStringAnnotation names s         -> Some (lazy Parsing.parse_dlm_label s)
        | _                                     -> None


    let (|DefaultedUnaryDlmLabelAnnotation|) names def = function
        | UnaryDlmLabelAnnotation names l       -> l
        | _                                     -> lazy def


    let (|DlmLabel|_|) (annots : J.annotations) = 
        let names = Config.Dlm.label_annotation
        let print anns = List.fold (fun s (ann : J.annotation) -> sprintf "%s;%s" s ann.pretty) "" anns
        let loc = try annots.Head.location with _ -> uloc
        match annots with
            | MultipleUnaryAnnotations names [J.String s]   -> Some (lazy Parsing.parse_dlm_label s)
            | MultipleUnaryAnnotations names (head :: tail) -> Error.multiple_annotation names (print (annots)) "declaration" loc
            | _                                             -> None
            

    let (|DlmAttributeLabel|) = function
        | DefaultedUnaryDlmLabelAnnotation Config.Dlm.label_annotation Defaults.attribute_label l -> l


    let (|DlmParamLabel|) = function
        | DefaultedUnaryDlmLabelAnnotation Config.Dlm.label_annotation Defaults.parameter_label l -> l
        

    let (|DlmReturnLabel|) (param_labels : Lazy<label> list) (begin_lb : label) m = 
        match m with
            | DefaultedUnaryDlmLabelAnnotation Config.Dlm.return_annotation (Defaults.return_label param_labels) l -> l


    let (|DlmBeginLabel|) = function
        | DefaultedUnaryDlmLabelAnnotation Config.Dlm.begin_annotation Defaults.begin_label l -> l     


    let (|DlmDeclassify|_|) = function
        | UnaryDlmLabelAnnotation Config.Dlm.declassify_annotation s    -> Some s
        | _                                                             -> None


    let (|DlmEndorse|_|) = function
        | UnaryDlmLabelAnnotation Config.Dlm.endorse_annotation s   -> Some s
        | _                                                         -> None


    let (|DlmPrincipals|) (annotated : #J.basic_annotated<_>) =
        match annotated.annots with
            | MultipleUnaryAnnotations Config.Dlm.principal_annotation literals ->
                List.concat <| List.map (create_principals_from annotated.location) literals 
            | _ -> []


    let (|DlmAuthority|) (annotated : #J.basic_annotated<_>) =
        match annotated.annots with
            | MultipleUnaryAnnotations Config.Dlm.authority_annotation literals ->
                List.concat <| List.map (create_principals_from annotated.location) literals 
            | _ -> [] 

            
    let (|DlmClass|) (cl : #J.class_signature) =
        let (DlmAuthority auths) = cl
        in
            DlmClass (cl, auths)


    let (|DlmMethod|) (m : J.method_signature) =
        let (DlmBeginLabel begin_lb) = m
        let par_lbs = List.map (function (DlmParamLabel l) -> l) m.paramss
        let (DlmReturnLabel par_lbs begin_lb.Value ret_lb) = m 
        let (DlmAuthority auths) = m
        in
            DlmMethod (m, begin_lb, ret_lb, par_lbs, auths)


    let (|DlmAttribute|) (a : J.attribute) =
        let (DlmAttributeLabel lb) = a
        in
            DlmAttribute (a, lb)


(* 
 * ----------------------------------------
 *
 * DLM Typechecker's State Monad.
 *
 * ----------------------------------------
 *)

module D = Detector

module CustomMonad =

    open Env.M
    open System.Collections.Generic
    open Monad

    let M = new builder ()

    type [<NoComparison>] state =
        {
        classes         : TJ.class_env
        var_lbs_tys     : Env.t<id, Dlm.label * J.ty>
        pc_label        : Dlm.label
        principals      : Dlm.principal Set
        hierarchy       : (Dlm.principal * Dlm.principal) list
        static_authority: Dlm.principal Set
        latest_loop_lb  : Dlm.label option
        goto_targets    : (id * Dlm.label) list
        goto_statements : (J.statement * Dlm.label) list
        }
    with
        member state.add_principals princs =
            { state with principals = List.fold (fun set princ -> Set.add princ set) state.principals princs }


    let state0 =
        {
        classes = TJ.Env0.class_env
        var_lbs_tys = Env.empty
        pc_label = Dlm.bottom_label
        principals = Set.empty
        hierarchy = []
        static_authority = Set.empty
        latest_loop_lb = None
        goto_targets = []
        goto_statements = []
        }
            
                 
    let in_classes =
        { new Env.M.access<state, fqid, J.class_signature> () with
            member self.get st = st.classes, st
            member self.set x st = (), { st with classes = x } }
    

    let in_var_lbs_tys =
        { new Env.M.access<state, id, Dlm.label * J.ty> () with
            member self.get st = st.var_lbs_tys, st
            member self.set x st = (), { st with var_lbs_tys = x } }

    
    let add_goto_statement stm s = ((), { s with goto_statements = (stm, s.pc_label) :: s.goto_statements })

    let add_goto_target id s =  ((), { s with goto_targets = (id, s.pc_label) :: s.goto_targets })


    /// Given the list of authorities currently possessed by the caller and the actual state of the program returns
    /// an expanded set containing all the authorities in the list and all the principals they can act for.
    let private expand_authorities auths state =
        let folder set p =
            List.fold (fun (set : Set<Dlm.principal>) (actor, role) -> if p = actor then set.Add role else set) set state.hierarchy
        let rec recursive_expansion old_set =
            let new_set = List.fold folder old_set auths
            if new_set.Count = old_set.Count then new_set
            else recursive_expansion new_set
        recursive_expansion Set.empty
            
    /// Given an annotable object adds all its principal declarations to the state.
    let add_principals_from_annotable (a : #J.basic_annotated<_>) (state : state) =
        let (D.DlmPrincipals princs) = a
        in
            ((), state.add_principals princs)

    /// Takes a list of labels and returns their combination.
    let combine_labels list loc state =
        match list with
            | []            -> unexpected loc "tried to combine an empty list of labels"
            | head :: []    -> head, state
            | head :: tail  -> List.fold (fun (lb1 : Dlm.label) (lb2 : Dlm.label) -> lb1.conjunction lb2) head tail, state

    /// Takes a list of labels and returns their combination, merged with the pc_label.
    let combine_with_pc_label list loc state =
        combine_labels (state.pc_label :: list) loc state

    /// Performs the given check and combines the resulting label with the pc_label.
    let check_and_combine checker loc st = let (lb, st') = checker st in combine_with_pc_label [lb] loc st' 

    /// Checks whether or not the caller has the required authority to execute a call to the method meth
    let check_authorization envs meth (obj_ty : J.ty) loc state =
        let (D.DlmMethod (_, _, _, _, callee_auths)) = meth
        let (obj_ty, obj_fqid) = TJ.resolve_ty envs obj_ty
        let (cl, state) = lookup in_classes obj_fqid state
        let (D.DlmClass (cl, obj_auths)) = cl
        let expanded_auths = expand_authorities (List.concat [Set.toList state.static_authority; obj_auths]) state
        let required_auths = List.fold (fun (set : Set<Dlm.principal>) p -> set.Add p) Set.empty callee_auths
        if not (required_auths.IsSubsetOf expanded_auths) then
            Error.lack_of_authority meth required_auths expanded_auths loc
        ((), state)

    /// Checks if the first label is a subtype of the second one, otherwise throws the given error.
    let check_subtyping (lb1 : Dlm.label) lb2 error state =
        if lb1.is_subtype lb2 state.hierarchy then ((), state)
        else error lb1 lb2

    /// Returns the pc_label of the current state
    let get_pc_label state = (state.pc_label, state)

    /// Returns the current state of the monad.
    let get_state = fun state -> (state, state)

    /// Creates a "module" that contains monadic wrappers for non-monadic functions.
    let mkW pkg imp = TJ.M.mkW in_classes in_var_lbs_tys snd pkg imp
    
    /// Parses a lazy label into its value and checks that all principals in it are already declared.
    let parse_label (lazy_lb : Lazy<Dlm.label>) loc state =
        let declared_principals = state.principals
        let rec check_principals (lb : Dlm.label) = function
            | []           -> lb, state
            | head :: tail -> 
                match head, Set.contains head declared_principals with
                    | Dlm.Bottom      , _
                    | Dlm.Top         , _
                    | _               , true  -> check_principals lb tail
                    | Dlm.Principal id, false ->
                        let (lbtyo, st) = Env.M.search in_var_lbs_tys id state
                        match lbtyo with
                            | Some (var_lb, ty) -> check_principals (lb.conjunction var_lb) tail
                            | None              -> Error.principal_unknown loc head lb
        check_principals lazy_lb.Value lazy_lb.Value.principals

    /// Returns a new state where all entries regarding goto-like statements are reset to the initial state.
    let reset_goto_labels s = ((), { s with latest_loop_lb = None; goto_targets = []; goto_statements = []})

    /// Sets the label of the latest loop found to be equal to the current pc_label.
    let set_context_loop s = ((), { s with latest_loop_lb = Some s.pc_label })

    /// If the given block option is None does nothing, otherwise applies f to every statement of the block.
    let something_block f bo =
        M {
        match bo with
            | Some b -> for stm in b do do! f stm
            | None -> return ()  
        }

    /// Updates state's pc_label by combining it with the given label.
    let update_pc_label lb state = 
        ((), { state with pc_label = state.pc_label.conjunction lb })
     
    /// Forks the computation by creating a backup of the current state, updating the pc_label with a new label
    /// and then restoring it from the backup after a given function has been executed.
    let fork_pc_label new_pc_label f =
      M {
        let! st0 = get_state
        do! update_pc_label new_pc_label
        let! st1 = get_state
        let (r, st2) = f st1
        do! set_state { st2 with pc_label = st0.pc_label }
      }


        





(* 
 * ----------------------------------------
 *
 * Implementation of the DLM label checker.
 *
 * ----------------------------------------
 *)

open Dlm
open Env.M
open Utilities
open CustomMonad



type [< NoComparison >] context =
  {
    this_ty             : J.ty
    envs                : TJ.environments
    W                   : TJ.M.W<CustomMonad.state>
    current_method      : J.methodd option
  }
with
    member self.this_fqid = let (_, fqid) = TJ.resolve_ty self.envs self.this_ty in fqid



/// <summary>Populates the global environment for the DLM typechecker.</summary>
/// <param name="prg">The Java program used to populate the environment.</param>
let populate_env (prg : J.program) =
  M {
    let rec bind_class_signatures (prefix : fqid) (cls : seq<J.class_signature>) =
      M {
        for cl in cls do            
            let prefix' = prefix.append cl.name
            do! Env.M.bind in_classes prefix' cl
            do! add_principals_from_annotable cl
            do! bind_class_signatures prefix' cl.inner_class_signatures
      }
    for cu in prg.compilation_units do
        do! bind_class_signatures cu.package (seq { for cl in cu.classes do yield cl :> J.class_signature })    
        do! bind_class_signatures cu.package (seq { for cl in cu.interfaces do yield cl :> J.class_signature })

  }



/// <summary>Typechecks a java program by iterating through all its compilation units by analyzing them. 
///     It also populates the global environment.</summary>
/// <param name="prg">The Java program used to populate the environment.</param>
/// <exception cref="unexpected">Raises an unexpected exception whenever something goes wrong during environment
///     population.</exception>
let rec typecheck_program (prg : J.program) =
  M {
    try do! populate_env prg
    // Must call Prelude.unexpected because we don't have any information about location.
    with e -> Prelude.unexpected "exception caught during environment initialization: %s" e.Message

    let! state = get_state
    for cu in prg.compilation_units do
        do! typecheck_compilation_unit cu
    
  }



/// <summary>Typechecks a compilation unit, that is a single java source file. Iterates through all its classes
///     by analyzing them.</summary>
/// <param name="cu">The compilation unit to be typechecked.</param>
and typecheck_compilation_unit cu =
  M {
    let! class_env = Env.M.get in_classes
    let W = mkW cu.package cu.imports
    for cl in cu.classes do
        let this_fqid = cu.package.append cl.name
        let envs = new TJ.environments (class_env, cu.package, cu.imports, this_fqid)
        let ctx =
            {
            this_ty = TJ.qualify_ty envs (J.Ty_Id cl.name)
            W = W this_fqid
            envs = envs
            current_method = None
            }
        do! trap (typecheck_class ctx) cl
  }



/// <summary>Typechecks a class, analyzing all its inner classes, methods and initializers.</summary>
/// <param name="ctx">The context of the compilation unit in which the class is found.</param>
/// <param name="cl">The class to be typechecked.</param>
and typecheck_class ctx (cl : J.classs) =
  M {

    for inner_class in cl.inner_classes do
        do! trap (typecheck_class ctx) inner_class

    // TODO: verificare sia sufficiente questo per initializers
    for stm in cl.initializer do
        do! trap (typecheck_statement ctx) stm
        
    // TODO: verificare sia sufficiente questo per initializers
    for stm in cl.static_initializer do
        do! trap (typecheck_statement ctx) stm

    for c in cl.constructors do
        do! trap (typecheck_method ctx) c

    for m in cl.methods do
        do! trap (typecheck_method ctx) m
  }



/// <summary>Typechecks the given method by analyzing every statement in it.</summary>
/// <param name="ctx">The context of the class in which the method is found.</param>
/// <param name="m">The method to be typechecked.</param>
and typecheck_method ctx (m : J.methodd) =
  M {

    let (D.DlmMethod (_, begin_lb, ret_lb, par_lbs, _)) = m
    let ctx = { ctx with current_method = Some m; }
    do! reset_goto_labels

    for par in m.paramss do
        let (D.DlmParamLabel lb) = par
        let! lb = parse_label lb m.location
        do! bind in_var_lbs_tys par.name (lb, par.ty)

    let! begin_lb = parse_label begin_lb m.location
    do! fork_pc_label begin_lb (M {
        for s in m.body do
            do! trap (typecheck_statement ctx) s
    })

    let! state = get_state
    for (stm, pc_label) in state.goto_statements do
        let target_lb, id =
            match stm.value with
                | J.Break (Some id)
                | J.Continue (Some id) -> 
                    match List.tryFind (fun (x, lb) -> x = id) state.goto_targets with
                        | Some (x, label)   -> label, id
                        | None              -> unexpected stm.location "couldn't find a goto label called: %s" id
                | s -> unexpected stm.location "trying to typecheck as goto-like a statement that is neither a 
                                                    break nor a continue: '%s'" s.pretty
        do! check_subtyping pc_label target_lb (Error.subtype_error stm.pretty stm.location "branch" "pc_label" (sprintf "pc_label_at %s:" id))

  }



/// <summary>Typechecks a Java statement (with its eventual annotations), looking for illegal information flows. 
///     If no such flow is found it terminates normally without returning any result, otherwise it raises a 
///     type_error exception.</summary>
/// <param name="ctx">The context of the method in which the statement is found.</param>
/// <param name="stm">The statement to be typechecked.</param>
/// <exception cref="type_error">Calls Report.subtype_error when the statement (or any of its parts) contains an illegal
///     information flow.</exception>
and typecheck_statement ctx (stm : J.statement) =
  M {

    let s = stm.value
    let loc = stm.location
    let check_expr = typecheck_expr ctx
    let check_statement = trap (typecheck_statement ctx)
    let subtype_error = Error.subtype_error stm.pretty loc
    let (D.DlmMethod (meth, begin_lb, ret_lb, par_lbs, _)) = ctx.current_method.Value

    let! pcl = get_pc_label

    match s with

        // TODO: Gestire declassify ed endorsment

        | J.Assert (cond_expr, eo) ->
            let! cond_lb = check_expr cond_expr
            match eo with
                | Some e -> 
                    do! fork_pc_label cond_lb (M {
                        // TODO: Si tipa così? Dovrebbe bastare il check dell'espressione! Verifica bene prima.
                        let! _ = check_expr e in ()
                    }) 
                | None -> return ()

        | J.Assign (id_expr, value_expr) ->  
            let! state = get_state
            let! value_lb = check_and_combine (check_expr value_expr) loc
            let! id_lb = check_expr id_expr
            return! check_subtyping value_lb id_lb (subtype_error "assignment" value_expr.pretty id_expr.pretty)

        // They are supported in JFlow and introduce the simple requirement that the pc at the destination 
        // statement is at least as restrictive as the pc at the break or continue statement
        | J.Break (Some id)
        | J.Continue (Some id) -> return! add_goto_statement stm

        | J.Break None
        | J.Continue None -> 
            let! pc_label = get_pc_label
            let! state = get_state
            match state.latest_loop_lb with
                | Some lb -> return! check_subtyping pc_label lb (subtype_error "branch" "pc_label" "pc_label_before_loop")
                | None    -> unexpected loc "found goto-like statement outstide of a loop"

        | J.Decl (_, (ty, id, D.DlmLabel label), None) ->
            let! label = parse_label label loc
            match label with
                | :? array_label -> match ty with | J.Ty_Array _ -> () | _ -> Warning.used_array_label_with_base_type loc ty 
                | _ -> ()
            do! bind in_var_lbs_tys id (label, ty)

        | J.Decl (_, (ty, id, D.DlmLabel label), Some expr) -> 
            let! label = parse_label label loc
            match label with
                | :? array_label -> match ty with | J.Ty_Array _ -> () | _ -> Warning.used_array_label_with_base_type loc ty 
                | _ -> ()
            do! bind in_var_lbs_tys id (label, ty)
            do! trap (typecheck_statement ctx) (J.Locatable (J.Assign (J.UL (J.Var id), expr), expr.location))

        | J.Decl (_, (ty, id, _), None) -> 
            match ty with
                | J.Ty_Array ty -> do! bind in_var_lbs_tys id (Defaults.unannotated_array_label :> Dlm.label, ty)
                | _             -> do! bind in_var_lbs_tys id (Defaults.unannotated_decl_label, ty)

        | J.Decl (_, (ty, id, _), Some e) -> 
            let! lb = check_expr e 
            let! expr_lb = combine_with_pc_label [lb] loc
            do! bind in_var_lbs_tys id (expr_lb, ty)

        | J.DoWhile (block, e) ->
            do! set_context_loop
            for stm in block do
                do! check_statement stm
            let! _ = check_expr e in return ()

        | J.For (init_opt, cond_expr_opt, incr_opt, block) ->
            do! set_context_loop 
            let! cond_lb =
                match cond_expr_opt with
                    | Some e    -> check_and_combine (check_expr e) loc
                    | None      -> get_pc_label

            do! fork_pc_label cond_lb (M {
                do! Monad.Option.iter check_statement init_opt
                do! Monad.Option.iter check_statement incr_opt                
                for stm in block do
                    do! check_statement stm
            })

        | J.ForEach ((ty, id, D.DlmLabel id_lb), e, block) ->
            do! set_context_loop
            let! src_lb = check_and_combine (check_expr e) loc
            let! id_lb = parse_label id_lb loc
            do! fork_pc_label src_lb <| M { 
                let! var_lb = combine_with_pc_label [id_lb] loc
                do! bind in_var_lbs_tys id (var_lb, ty)
                for stm in block do do! check_statement stm 
            }
            
        (* Literals and variables declared "on the fly" must be annotated with the pc_label. That's because
         * we can learn an amount of information up to {pc_label; src_lb} just by knowing we are inside the for each. *)
        | J.ForEach ((ty, id, _), e, block) ->
            do! set_context_loop
            let! src_lb = check_and_combine (check_expr e) loc
            do! fork_pc_label src_lb <| M {
                do! bind in_var_lbs_tys id (src_lb, ty) 
                for stm in block do do! check_statement stm 
            }

        | J.If (e, t, eo) ->
            let! if_label = check_expr e
            do! fork_pc_label if_label (M {
                for stm in t do
                    do! check_statement stm
                do! something_block check_statement eo
            })       
            
        | J.Labeled (id, stm) -> 
            do! add_goto_target id
            do! check_statement stm

        | J.Return (Some e) ->
            let! actual_lb = check_expr e
            let! ret_lb = parse_label ret_lb loc
            return! check_subtyping actual_lb ret_lb (subtype_error "return statement" e.pretty "return_label")
            
        | J.Return None ->
            let! pc_label = get_pc_label
            let! ret_lb = parse_label ret_lb loc
            return! check_subtyping pc_label ret_lb (subtype_error "return statement" "pc_label" "return_label")

        | J.StatementExpr e ->
            let! _ = check_expr e in return ()

        | J.SuperCons (tyargs, args) -> 
            let! cl = lookup in_classes ctx.this_fqid
            do! typecheck_constructor_call ctx cl.super_ty tyargs args stm.pretty loc

        | J.Switch (e, cases, def_opt) -> 
            // TODO: basta così per lo switch? controlla come va tipato il break
            do! set_context_loop 
            let! expr_lb = check_and_combine (check_expr e) loc
            do! fork_pc_label expr_lb (M {
                for (lit, block) in cases do
                    for stm in block do
                        do! check_statement stm
                do! set_context_loop
                if def_opt.IsSome then
                    for stm in def_opt.Value do
                        do! check_statement stm
            })

        | J.ThisCons (tyargs, args) ->
            do! typecheck_constructor_call ctx ctx.this_ty tyargs args stm.pretty loc

        | J.Throw e -> 
            let! pc_label = get_pc_label
            let! expr_lb = check_expr e
            let! begin_lb = parse_label begin_lb loc
            //TODO: Decidere come tipare le eccezioni. subtype di return_label? subtype di begin_label? subtype di pc_label?
            return! check_subtyping expr_lb begin_lb (subtype_error "throw statement" e.pretty "begin_label")

        | J.Try (block, cbs, fbo) -> 
            for stm in block do
                do! check_statement stm
            for cb in cbs do
                let! state = get_state
                let! exn_lb =
                    match (fst cb).annots with
                        | D.DlmLabel lb -> let (lb, state) = parse_label lb loc state in combine_with_pc_label [lb] loc
                        | _             -> get_pc_label
                do! bind in_var_lbs_tys (fst cb).name (exn_lb, (fst cb).ty) 
                for stm in snd cb do
                    do! check_statement stm
            do! Monad.Option.iter (fun fb -> M { for stm in fb do do! check_statement stm }) fbo

        | J.While (expr, block) ->
            do! set_context_loop
            let! cond_expr = check_and_combine (check_expr expr) loc
            do! fork_pc_label cond_expr <| M { for stm in block do do! check_statement stm }

  }



/// <summary>Typechecks an expression, looking for illegal information flows. If no such flow is found, returns the normal value
///     of the expression.</summary>
/// <param name="this_qid">The qualified id of the class that contains the given expression.</param>.
/// <param name="located_exp">The expression to be typechecked.</param>
/// <returns>The label of the expression.</returns>
/// <exception cref="type_error">Calls Report.subtype_error when the expression (or any of its sub-expressions) presents an invalid
///     flow of information.</exception>
and typecheck_expr ctx (located_exp : J.expr) = 
  M {
    
    let check = typecheck_expr ctx
    let (e, loc) = match located_exp with | J.Locatable (e', loc) -> (e', loc)
    
    match e with

        | J.AnonymousClass (ty, (tyargs, args), b) ->
            let ms = new J.class_modifiers (visibility = Java.Package)
            // As far as I know type parameters are NOT possible in anonymous classes.
            do! typecheck_class ctx (new J.classs (ms, ty.reifiable.id, [], None, [], b))
            do! typecheck_constructor_call ctx ty tyargs args e.pretty loc
            return! get_pc_label
            
        | J.BinOp (e1, _ , e2) -> 
            let! lb1 = check e1
            let! lb2 = check e2 
            return! combine_labels [lb1; lb2] loc

        | J.Cast (ty, expr) -> 
            // TODO: verificare che sia sempre vero
            return! check expr 

        | J.Cond (c, e1, e2) -> 
            let! cond_label = check c
            let! old_state = get_state
            let! new_pc_label = combine_with_pc_label [cond_label] loc
            do! update_pc_label new_pc_label
            let! lb1 = check e1 
            let! lb2 = check e2 
            do! update_pc_label old_state.pc_label
            return! combine_labels [new_pc_label; lb1; lb2] loc
           
        | J.Lit lit ->
            // TODO: verificare che non sia necessario caso particolare per array
            return! get_pc_label

        | J.MemberSel (recp, id, acso) ->
            let! obj_ty = ctx.W.deduce_recipient ctx.this_ty recp
            match acso with
                | Some (tyargs, args) -> return! typecheck_method_call ctx obj_ty id tyargs args e.pretty loc
                | None ->
                    let! o = ctx.W.search_attribute obj_ty id
                    match o with
                        | Some (_, ty, D.DlmAttribute (att, lb)) -> let! lb = parse_label lb loc in return lb
                        | None                                   -> return not_implemented "Dlm.typecheck_expr: select on inner class"
        
        | J.New (ty, (tyargs, args)) -> 
            (* The normal value label of a New is the join of the end-label of the constructor with the pc label. *)
            let (obj_ty, _) = TJ.resolve_ty ctx.envs ty 
            do! typecheck_constructor_call ctx obj_ty tyargs args e.pretty loc
            return! get_pc_label

        // operand, index
        | J.Subscript (e1, e2) ->
            let! opnd_lb = check e1
            let! idx_lb = check e2
            return! combine_labels [opnd_lb; idx_lb] loc

        | J.This ->
            // TODO: verificare come tipare THIS!!
            return! get_pc_label
                                    
        | J.Var id ->                
            let! var_opt = Env.M.search in_var_lbs_tys id
            match var_opt with
                | Some (lb, ty) -> return lb
                | None          -> return! check (J.Locatable (J.MemberSel (J.Sel (J.UL J.This, id)), loc))

        | J.UnOp ( _ , e1) -> return! check e1

        | _ -> return! not_implemented "typecheck_expr: %s" e.pretty 
      
  }



/// <summary>Typechecks a call to a constructor, verifying that actuals' labels are at most as restrictive as parameters'.</summary>
/// <param name="ctx">The context of the method in which this call is found.</param>/// <param name="obj_qid">The qualified id of the class that contains the constructor to be invoked.</param>
/// <param name="obj_ty">The type of the class that contains the method to be invoked.</param>
/// <param name="tyargs">The type arguments passed to the invoked method.</param>
/// <param name="args">The arguments passed to the invoked method.
/// <param name="where">A string representing the statement in which the string appears.</param>
/// <param name="loc">The location corresponding to this constructor call.</param>
/// <exception cref="type_error">Throws an exception calling Report.subtype_error if any of the actuals' label is more
///     restrictive than its formal counterpart.</exception>
and typecheck_constructor_call ctx obj_ty (tyargs : J.ty_arg list) args where loc =
  M {
    let id = obj_ty.reifiable.id
    
//    let! state = get_state
//    let es = List.map (fun e -> ctx.W.try_deduce_expr ctx.this_ty e state) args
    let! ro = ctx.W.resolve_overloaded_constructor tyargs args ctx.this_ty obj_ty id

//    let args = List.map (fun (exp : J.expr) -> match exp with | J.UL (J.Lit (J.ClassOp qid)) -> J.Locatable (J.Cast (J.Ty_QId (Absyn.qid.of_string Config.Java.Names.Type.Class), exp), uloc) | _ -> exp) args
//    let es = List.map (fun e -> ctx.W.try_deduce_expr ctx.this_ty e state) args
//    let! ro = ctx.W.resolve_overloaded_constructor tyargs args obj_ty id

    let co = 
        match ro with
            | Some (_, _, c) -> Some (c :> J.method_signature)
            | None -> None
    let! _ = typecheck_call ctx obj_ty id tyargs args where loc co "constructor"
    ()
  }
   


/// <summary>Typechecks a call to a method, verifying that actuals' labels are at most as restrictive as parameters'.</summary>
/// <param name="ctx">The context of the method in which this call is found.</param>
/// <param name="obj_ty">The type of the class that contains the method to be invoked.</param>
/// <param name="id">The id of the method to be invoked.</param>
/// <param name="tyargs">The type arguments passed to the invoked method.</param>
/// <param name="args">The arguments passed to the invoked method.
/// <param name="where">A string representing the statement in which the string appears.</param>
/// <param name="loc">The location corresponding to this constructor call.</param>
/// <returns>The return label of the invoked method, as long as actuals' labels are valid.</returns>
/// <exception cref="type_error">Throws an exception calling Report.subtype_error if any of the actuals' label is more
///     restrictive than its formal counterpart.</exception>
and typecheck_method_call ctx obj_ty id tyargs args where loc =
  M {
    let! state = get_state 
    let es = List.map (fun e -> ctx.W.try_deduce_expr ctx.this_ty e state) args
    let! ro = ctx.W.resolve_overloaded_method_signature tyargs args ctx.this_ty obj_ty id
//    let! ro = ctx.W.resolve_overloaded_method_signature tyargs args ctx.this_ty id
    let mo = 
        match ro with
            | Some (_, _, m) -> Some m
            | None -> None
    return! typecheck_call ctx obj_ty id tyargs args where loc mo "method"
  }


and typecheck_call ctx obj_ty id tyargs args where loc mo what =
  M {
    match mo with
        | Some (D.DlmMethod (meth, _, ret_lb, par_lbs, _)) -> 
            if (par_lbs.Length <> args.Length) then 
                return! unexpected loc "typecheck_method_call: %s: list of actuals and formal parameters are of different sizes" meth.pretty
            for (par, par_lb, ac) in List.zip3 meth.paramss par_lbs args do
                let! aclb = typecheck_expr ctx ac
                let! par_lb = parse_label par_lb loc
                do! check_subtyping aclb par_lb (Error.subtype_error where loc "method_call" (sprintf "actual parameter '%s'" ac.pretty) (sprintf "formal parameter '%s'" par.pretty))
            do! check_authorization ctx.envs meth obj_ty loc
            return! parse_label ret_lb loc
        | None -> 
            let pretty_string = sprintf "%s.%s<%s>(%s)" obj_ty.pretty id
            let pretty_tyargs = 
                match tyargs with
                    | [] -> ""
                    | head :: tail -> List.fold (fun s (tyarg : J.ty_arg) -> sprintf "%s, %s" s tyarg.pretty) head.pretty tail
            let pretty_args =
                match args with
                    | [] -> ""
                    | head :: tail -> List.fold (fun (str : string) (arg : J.expr) -> sprintf "%s, %s" str arg.pretty) head.pretty tail
            return! unexpected loc "couldn't resolve overloaded %s call: '%s'" what (pretty_string pretty_tyargs pretty_args)
  }