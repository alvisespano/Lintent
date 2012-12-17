(*
 * TypeDroid - LintentEngine
 * AndroidTyping.fs: android typing data and definitions
 * (C) 2012 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)

module LintentEngine.Typing.Android

open System
open System.Text.RegularExpressions
open FSharpCommon.Prelude
open FSharpCommon.Log
open FSharpCommon
open LintentEngine
open LintentEngine.Absyn

module J = LintentEngine.Absyn.Java
module TJ = LintentEngine.Typing.Java
module N = Config.Java.Names


(*
 * error reporting
 *)

type type_error (message, pri : Log.pri, loc, issue) =
    inherit located_error (message, loc)
    member val pri = pri with get
    member val issue = issue with get

module Report =   
    
    open LintFeedback

    let internal t issue (loc : location) pri fmt = 
        Globals.reporter.report_and_throw issue loc (fun s -> new type_error (s, pri, loc, issue)) fmt

    let inline internal log f (loc : location) pri (fmt : Printf.StringFormat<_, unit>) = f pri ("%s: " +% fmt) loc.pretty
    
    let inline internal w issue (loc : location) pri (fmt : Printf.StringFormat<_, unit>) = 
        if Globals.reporter.can_write then Printf.kprintf (Globals.reporter.report_issue issue loc) fmt  
        else Globals.logger.warn pri ("%s: " +% fmt) loc.pretty

    let inline internal h (loc : location) pri fmt = 
        if Globals.reporter.can_write then Printf.kprintf (Globals.reporter.report_hint loc) fmt  
        else Globals.logger.hint pri ("%s: " +% fmt) loc.pretty

    let trapped loc (e : exn) (x : J.node<_>) =
        let pri, s, issue =
            match e with
                | Unexpected s                      -> Unmaskerable, sprintf "unexpected exception: %s" s, Issue.Unexpected
                | Env.UnboundSymbolError s          -> Unmaskerable, sprintf "unbound symbol: %s" s, Issue.Unknown
                | :? NotImplementedException as e   -> Unmaskerable, sprintf "not_implemented exception: %s" e.Message, Issue.NotImplemented
                | :? type_error as e                -> e.pri, sprintf "type error: %s" e.Message, e.issue
                | e                                 -> Unmaskerable, sprintf "trapped exception: %s\n%s" e.Message e.StackTrace, Issue.Unexpected
        in
            w issue loc pri "%s" s;
            Globals.logger.debug Normal "%O" x

    module Err =

        let intent_owner_is_not_this loc = t Issue.Intent loc High "intent owner is not 'this' component"

    module Warn =
        
        let nonconst_intent_extra_key loc id = w Issue.PartialEvaluation loc High "intent '%s' has non-statically-evaluable key" id
        let nonconst_intent_action_string loc = w Issue.PartialEvaluation loc High "action string does not evaluate to a literal constant"
        let nonconst_intent loc = w Issue.PartialEvaluation loc High "intent expression cannot be statically evaluable"
        let nonconst_activity_result_code loc activity_name = w Issue.PartialEvaluation loc Normal "activity '%s' result code cannot be evaluated statically" activity_name
                
        let undefined_intent_recipient loc id = w Issue.Intent loc Unmaskerable "intent '%s' has no recipient" id
        let defined_intent_recipient_in_setResult loc id = w Issue.Intent loc Unmaskerable "intent '%s' passed to setResult() has a recipient" id
        let intent_receive_forbidden loc iid methname = w Issue.Intent loc Normal "invokation of method '%s' on intent '%s' in a context where intent receive is forbidden" methname iid
        let intent_extra_type_mismatch loc k ty ty' = w Issue.Intent loc High "intent extra type mismatch: %s had type %s but is reused with type %s" k ty ty'

        let illformed_intent_annotation loc iid s = w Issue.Annotation loc Normal "ill-formed annotation on intent '%s': %s" iid s

        let assignment_of_attribute loc ty att = w Issue.NotImplemented loc High "assignment of attributes is not supported: %s.%s" ty att

        let unknown_getExtra loc s = w Issue.Unexpected loc High "unknown typename \"%s\" matched within invokation of method Intent.get%sExtra(). Defaulting to Object" s s

    module Hint =
             
        let non_final_variable loc id = h loc Low "non-final variable %s is actually statically evaluable" id

//        let intent_extra_reuse loc k ty ty' = h loc High "intent extra reuse is discouraged: label %s existed with type %s and is being reused with type %s" k ty ty'

    module Priv =        

        module Err =

            let implicit_intent_in_call_with_result loc iaddr s = t Issue.Intent loc High "implicit intent '%s' passed to call for result with action string '%s'" iaddr s


        module Warn =
            let unknown_action_string loc s = w Issue.Unknown loc Low "action string '%s' is unknown thus its calling permissions cannot be checked" s

            let unknown_component_name loc s = w Issue.Unknown loc Low "component '%s' is unknown thus its calling permissions cannot be checked" s

            let effective_permissions_greater_than_calling_permissions loc comp ep cp dp =
                w Issue.Perms loc Unmaskerable "component %s can be accessed using calling permissions %s but it exercises permissions %s. Exposed permissions: %s" comp cp ep dp

            let overprivileged_application loc up ep dp =
                w Issue.Perms loc High "application is over-privileged: owns permissions %s but exercises permissions %s. Unused permissions: %s" up ep dp
        
            let component_call_permission_denied loc perms call = w Issue.Perms loc Unmaskerable "component call permission denied: caller permissions are %s but requires %s" perms call

            let api_call_permission_denied loc perms call = w Issue.Perms loc Unmaskerable "API call permission denied: caller permissions are %s but requires %s" perms call

            let secrecy_violation loc i ip p dp = w Issue.Perms loc Unmaskerable "secrecy violation: intent '%s' enables permissions %s but is protected with permissions %s. Exposed permissions: %s" i ip p dp

module LF = LintentEngine.LintFeedback

let inline not_implemented (loc : location) fmt = Globals.reporter.report_not_implemented loc fmt

let inline unexpected (loc : location) fmt =  Globals.reporter.report_unexpected loc fmt
    



(*
 * datatypes for reconstruction and checking
 *)

type address (mem : int, expr : J.expr) =
    inherit CustomCompare.basic_by_property<int> ()
    override self.cmp = self.mem
    member val mem = mem with get
    member val expr = expr with get
    member self.pretty = sprintf "%O#%d" self.expr self.mem
    override self.ToString () = self.pretty
    new (e) = new address (fresh (), e)

type perm (name : string) =
    inherit CustomCompare.basic_by_function<string> (fun _ -> name)
    member val name = name with get
    static member of_activity_name name = new perm (sprintf "%s__%d" name (name.GetHashCode ()))
    member self.pretty = name
    override self.ToString () = self.pretty

type [< NoComparison >] perms (set : perm Set) =
    override x.Equals yobj = CustomCompare.equals_on (fun (self : perms) -> self.toSet) x yobj
    override x.GetHashCode () = CustomCompare.hash_on (fun (self : perms) -> self.toSet) x
    member val toSet = set with get
    new (p : perm) = new perms (Set.singleton p)
    new (ps : seq<perm>) = new perms (Set.ofSeq ps)
    static member bottom = new perms (Set.empty)
    member self.pretty = sprintf "[%s]" (mappen_strings (fun (p : perm) -> if p.name.Length = 0 then "\"\"" else sprintf "%s" p.pretty) ", " set)
    override self.ToString () = self.pretty
    member self.is_empty = set.IsEmpty
    static member of_strings ss = new perms (seq { for s in ss do yield new perm (s) })
    member self.union (perms' : perms) = new perms (Set.union set perms'.toSet)
    static member (+) (perms1 : perms, perms2 : perms) = perms1.union perms2
    static member (-) (perms1 : perms, perms2 : perms) = new perms (Set.difference perms1.toSet perms2.toSet)
    static member get_Zero () = perms.bottom
    member x.is_in (y : perms) = x.toSet.IsSubsetOf y.toSet
    member x.is_strictly_in (y : perms) = x.toSet.IsProperSubsetOf y.toSet
            

(* const type *)

type [< NoComparison >] constt =
        | CLit of J.lit
        | CObj of J.ty * address option
with
    member self.pretty =
        match self with
            | CLit l               -> sprintf "%O" l
            | CObj (ty, Some addr) -> sprintf "%O@%O" ty addr
            | CObj (ty, None)      -> sprintf "<%O>@?" ty

    override self.ToString () = self.pretty

let (|CNum|_|) = function
    | Some (CLit (J.Int n))  -> Some (int64 n)
    | Some (CLit (J.Long n)) -> Some n
    | _                      -> None

let (|CString|_|) = function
    | Some (CLit (J.String s)) -> Some s
    | _                        -> None

let (|CChar|_|) = function
    | Some (CLit (J.Char c)) -> Some c
    | _                      -> None

let (|CBool|_|) = function
    | Some (CLit (J.Bool b)) -> Some b
    | _                       -> None

let (|CReal|_|) = function
    | Some (CLit (J.Double x)) -> Some x
    | Some (CLit (J.Float x))  -> Some (float x)
    | _                        -> None

let CNum n = Some (CLit (J.Long n))
let CReal x = Some (CLit (J.Double x))
let CString s = Some (CLit (J.String s))
let CBool b = Some (CLit (J.Bool b))


(* intents *)

module Intent =

    type recipient =
        | Explicit of fqid
        | Implicit of string
        | Undefined
    with
        member self.pretty =
            match self with
                | Explicit qid -> sprintf "%s.class" qid.pretty
                | Implicit s   -> sprintf "@%s" s
                | Undefined     -> "?"

    type extra_key = J.id

    type [< NoComparison >] extra_content =
        | NonSensitive of constt option
        | Sensitive of address * t
    with
        member self.perms =
            match self with
                | NonSensitive _   -> perms.bottom
                | Sensitive (_, i) -> i.perms

        member self.pretty =
            match self with
                | NonSensitive (Some c) -> c.pretty
                | Sensitive (iaddr, _)  -> sprintf "%s" iaddr.pretty
                | _                     -> "?"

        override self.ToString () = self.pretty

                    
    and [< NoComparison >] extra_value =
      {
        ty      : J.ty
        content : extra_content option
      }
    with
        member self.perms = something (fun (ec : extra_content) -> ec.perms) perms.bottom self.content
            


    and t (recp : recipient, ?additional_perms, ?declassify_perms) =
        let mutable extras_ : Env.t<extra_key, extra_value> = Env.empty
        let mutable additional_prms_ = defaultArg additional_perms perms.bottom
        let cmp (self : t) = self.extras |> Env.asMap |> Map.map (fun _ v -> v.ty)

        interface IComparable with
            member x.CompareTo yobj = CustomCompare.compare_on cmp x yobj
        override x.Equals y = CustomCompare.equals_on cmp x y
        override self.GetHashCode () = CustomCompare.hash_on cmp self

        abstract recipient : recipient with get 
        default self.recipient with get () = recp

        member self.extras = extras_

        member val locked = false with get, set

        member self.perms
            with get () = (self.extras |> Env.toSeq |> Seq.sumBy (fun (_, ev) -> ev.perms)) + additional_prms_ - self.declassify_perms

        member val declassify_perms = defaultArg declassify_perms perms.bottom with get, set

        member self.add_perms prms = additional_prms_ <- additional_prms_ + prms
        
        member private self.add_extra k ev =
            if not self.locked then
                extras_ <- Env.bind k ev extras_

        member self.add_put_extra loc k (ty : J.ty) ec =
            match Env.search k self.extras with                    
                | Some ev when ev.ty <> ty -> Report.Warn.intent_extra_type_mismatch loc k ty.pretty ev.ty.pretty
                | _ -> ()
            self.add_extra k { ty = ty; content = Some ec }

        member self.add_get_extra loc k ty =
            match Env.search k self.extras with                    
                | Some ev ->
                    if ev.ty <> ty then Report.Warn.intent_extra_type_mismatch loc k ty.pretty ev.ty.pretty
                    Some ev

                | None -> self.add_extra k { ty = ty; content = None }; None
                        
        static member pretty_extra k (ev : extra_value) = sprintf "%s : %s" k ev.ty.pretty

        member i.pretty =
            let bra, ket = if i.locked then "[|", "|]" else "{", "}"
            let extras = Env.pretty_sep t.pretty_extra "; " i.extras
            in
                sprintf "(%s)%s %s %s" i.recipient.pretty bra extras ket

        member self.clone =
            let i = new t (self.recipient, additional_prms_, self.declassify_perms)
            for (k, ev) in Env.toSeq self.extras do i.add_extra k ev
            i

type intent = Intent.t
type labeled_intent = intent * string option



module Tag =
    type [< NoComparison >] t =
        | App of bool * address
        | ApiCall of fqid * id * J.ty list * perms
        | PendingIntentFactory of address
        | PendingIntentDeclassify of perms * address


module Component =

    let internal make_tab n = new String (' ', n * 3)
    let internal pretty_set f tabn set = mappen_strings f (sprintf "\n%s" (make_tab tabn)) set
    let internal pretty_intent_set = pretty_set (fun (i : intent) -> i.pretty)  
    let internal pretty_intent_and_code_set = pretty_set (fun (i : intent, co) -> sprintf "code[%s] %s" (either "_" co) i.pretty)

    // TODO: dovrebbe essere senza side-effect per funzionare al meglio con la valutazione lazy
    type [< AbstractClass >] t (out_requests : labeled_intent Set, in_requests : intent Set,
                                calling_perms : perms) =
        member val in_requests = in_requests with get, set
        member val out_requests = out_requests with get, set
        
        member self.add_in_requests i = self.in_requests <- Set.add i self.in_requests
        member self.add_out_requests li = self.out_requests <- Set.add li self.out_requests

        abstract pretty : int -> string

        override self.ToString () = self.pretty 0

        member internal self.pretty_out_requests tab = pretty_intent_and_code_set tab self.out_requests 
        member internal self.pretty_in_requests tab = pretty_intent_set tab self.in_requests

        member val calling_perms = calling_perms with get        

type componentt = Component.t

module Activity =
    
    module C = Component

    type t (out_requests, in_requests, out_results, in_results, calling_perms) =
        inherit componentt (out_requests, in_requests, calling_perms)

        member val out_results = out_results with get, set
        member val in_results = in_results with get, set
        
        new (calling_perms, ?secr) = new t (Set.empty, Set.empty, Set.empty, Set.empty, calling_perms)

        override self.pretty n =
            let tab = Component.make_tab n
            let n = n + 1
            let oress = C.pretty_intent_and_code_set n self.out_results
            let iress = C.pretty_intent_set n self.in_results
            let oreqs = self.pretty_out_requests n
            let ireqs = self.pretty_in_requests n
            in
                sprintf "%sOUT-REQ: %s\n%sIN-RES: %s\n%sIN-REQ: %s\n%sOUT-RES: %s"
                    tab oreqs
                    tab iress
                    tab ireqs
                    tab oress
                    

        member self.add_out_results li = self.out_results <- Set.add li self.out_results
        member self.add_in_results i = self.in_results <- Set.add i self.in_results

type activity = Activity.t

module Service =

    type t (out_requests : intent Set, in_requests : intent Set, calling_perms) =
        inherit componentt (Set.map (fun i -> i, None) out_requests, in_requests, calling_perms)

        new (calling_perms) = new t (Set.empty, Set.empty, calling_perms)

        override self.pretty n =
            let tab = Component.make_tab n
            let n = n + 1
            let oreqs = self.pretty_out_requests n
            let ireqs = self.pretty_in_requests n
            in
                sprintf "%sOUT-REQ: %s\n%sIN-REQ: %s"
                    tab oreqs
                    tab ireqs

type service = Service.t


(* var declarations *)

type [< NoComparison >] var_decl =
  {
    modif   : J.decl_modifiers
    expr    : (J.expr * constt option Lazy) option
    ty      : J.ty
  }
with
    member self.pretty =
        flatten_strings " " [(if self.modif.staticc then "static" else "");
                             (if self.modif.final then "final" else "");
                             self.ty.pretty;
                             (match self.expr with Some _ -> " = <expr>" | None -> "")]


(*
 * code detectors
 *)

module Detector =

    let (|S|) (J.UL x : J.statement) = x
    let (|E|) (J.UL x : J.expr) = x
    let (|SE|_|) = function S (J.StatementExpr (E e)) -> Some e | _ -> None
    
    let (|Id|_|) (s : id) = function
        | id when id = s -> Some ()
        | _              -> None

    let (|RexId|_|) s =
        let rex = new Text.RegularExpressions.Regex (s)
        in
            fun id ->
                let m = rex.Match id
                in
                    if m.Success then Some m.Groups.[1].Value
                    else None

    let (|ThisCall'|_|) name = function
        | J.MemberSel (J.Call (E J.This, Id name, [], args)) -> Some args
        | _                                                  -> None

    let (|ThisCall|_|) name = function
        | E (ThisCall' name args) -> Some args
        | _                       -> None
            
    let (|SThisCall|_|) name = function
        | SE (ThisCall' name args) -> Some args
        | _                      -> None

    let (|SubClassOf|_|) (super_ty : J.ty) envs (cl : #J.class_signature) =
        let sub_ty = J.Ty_Id cl.name
        in
            if TJ.is_subclass_of envs super_ty sub_ty then Some sub_ty
            else None

    let (|Ty|_|) tyname envs ty = if TJ.qualify_ty envs ty = J.Ty_SQId tyname then Some () else None

    module Annot =
        let (|Unary|) label (a : J.annotation) =
            match a.bindings with
                | [l, lit] when l = label -> lit, a.location
                | bs -> unexpected a.location "expected an unary annotation: @%s(%s)" a.name (mappen_strings (fun (k, v) -> sprintf "%s = %O" k v) ", " bs)
        
        //let (|Unary|) (a : J.annotation) = (|UnaryNamed|) "value" a

        let (|MultipleUnaries|_|) names label anns =
            match List.filter (fun (annot : J.annotation) -> List.exists (fun s -> s = annot.name) names) anns with
                | [] -> None
                | annots -> Some (List.map (function Unary label lit -> lit) annots)

        let (|MultipleUnary|_|) names label = function
            | MultipleUnaries names label [] -> None
            | MultipleUnaries names label [lit] -> Some lit
            | _  -> None
        
        let (|MultipleUnaryString|_|) names label = function
            | MultipleUnary names label (J.String s, loc) -> Some (s, loc)
            | _ -> None

    module Intent =

        let (|Ty|_|) envs ty = (|Ty|_|) N.Type.Intent envs ty

        let (|New|_|) envs = function
            | E (J.New (Ty envs, ([], args))) -> Some args
            | _ -> None

        let (|Annotated|_|) anns =
            match anns with
                | Annot.MultipleUnaryString Config.Java.Annot.intent "value" s -> Some s
                | _ -> None

        let (|PutExtra|_|) = function
            | SE (J.MemberSel (J.Call (recp, Id N.Method.Intent.putExtra, [], [ke; ve]))) -> Some (recp, ke, ve)
            | _ -> None

        let (|GetExtraCall|_|) = function
            | E (J.MemberSel (J.Call (recp, RexId N.Method.Intent.getExtra tyinfix, [], args))) ->
                match args with
                    | [ke]       -> Some (recp, ke, None, tyinfix)
                    | [ke; defe] -> Some (recp, ke, Some defe, tyinfix)
                    | _          -> None
            | _ -> None

        let (|Attribute|_|) envs (a : J.attribute) =
            match a.ty, a.expr with
                | Ty envs, eo -> Some (a.name, eo, a.annots)
                | _      -> None


    module PendingIntent =

        let (|Ty|_|) envs ty = (|Ty|_|) N.Type.PendingIntent envs ty

        let (|GetActivity|_|) = function
            | E (J.MemberSel (J.Call (e, Id N.Method.PendingIntent.getActivity, [], args))) ->
                match args with
                    | [_; _; ie; _] 
                    | [_; _; ie; _; _] -> Some (e, ie)
                    | _               -> None
            | _ -> None

        let (|Decl|_|) envs = function
            | S (J.Decl (_, (Ty envs, id, annots), Some (GetActivity (e, ie)))) -> Some (id, e, ie, annots)
            | _ -> None
            
                
    module Activity =

        let (|Class|_|) envs = function
            | SubClassOf (J.Ty_SQId N.Type.Activity) envs ty -> Some ty
            | _                                              -> None

        let (|Method_onCreate|_|) = function
            | J.MethodSignature
                (Id N.Method.Activity.onCreate, _,
                // TODO: bundle argument must be typed
                 [_, b]) -> Some b
            | _                                -> None

        let (|Method_onActivityResult|_|) envs = function
            | J.MethodSignature
                (Id N.Method.Activity.onActivityResult, _,
                 [J.Ty_Builtin J.Ty_Int, reqcode;
                  J.Ty_Builtin J.Ty_Int, rescode;
                  Intent.Ty envs, i]) -> Some (reqcode, rescode, i)
            | _ -> None

        let (|StartActivityForResult|_|) = function
            | SThisCall N.Method.Activity.startActivityForResult [e; ce] -> Some (e, ce)
            | _ -> None

        let (|StartActivity|_|) = function
            | SThisCall N.Method.Activity.startActivity ([e] | [e; E (J.Var _)]) -> Some e
            | _ -> None

        let (|StartActivity_or_StartActivityForResult|_|) = function
            | StartActivityForResult (id, ce) -> Some (id, Some ce)
            | StartActivity id                -> Some (id, None)
            | _                               -> None

        let (|StartActivities|_|) = function
            | SThisCall N.Method.Activity.startActivities ([e] | [e; _]) -> Some e
            | _ -> None

        let (|GetIntent|_|) = function
            | ThisCall N.Method.Activity.getIntent [] -> Some ()
            | _                                       -> None

        let (|SetResult|_|) = function
            | SThisCall N.Method.Activity.setResult args ->
                match args with
                    | [ce]     -> Some (ce, None)
                    | [ce; ie] -> Some (ce, Some ie)
                    | _        -> None
            | _ -> None

        let (|StartService|_|) = function
            | SThisCall N.Method.Activity.startService [ie] -> Some ie
            | _                                             -> None


    module Service =

        let (|Class|_|) envs = function
            | SubClassOf (J.Ty_SQId N.Type.Service) envs ty -> Some ty
            | _                                             -> None
        

(*
 * custom state monad
 *)
                                  
module CustomMonad =

    type builder = Monad.builder
            
    let M = new builder ()
        
    type api_call_id = fqid * id * J.ty list

    type [<NoComparison>] environments =
      {
        var_decls           : Env.t<id, var_decl>
        classes             : TJ.class_env
        intents             : Env.t<address, Intent.t>
        components          : Env.t<fqid, componentt>
        api_calls           : Env.t<api_call_id, perms>
        implicit_calls      : Env.t<string, perms>
        component_effective_perms : Env.t<fqid, perms>
      }

        member envs.pretty =
            let tab = "   "
            let p pid f = Env.pretty (fun id x -> sprintf "%s%s : %s" tab (pid id) (f x))
            let envs = [
                "INTENTS",          p (sprintf "%O") (fun (i : intent) -> i.pretty) envs.intents
                "VAR DECLS",        p identity (fun (v : var_decl) -> v.pretty) envs.var_decls
                "COMPONENT",        Env.pretty (fun fqid (c: componentt) -> sprintf "%s%O:\n%O" tab fqid (c.pretty 2)) envs.components
//                "CLASSES",          p (sprintf "%O") (fun (c : J.class_signature) -> match c with :? J.classs -> "<class>" | :? J.interfacee -> "<interface>" | _ -> "<class signature>") envs.classes
//                "ACTIVITY CALLS",   p (fun (fqid, id, _) -> sprintf "%O.%s" fqid id) (fun (prms : perms) -> prms.pretty) envs.api_calls
//                "API CALLS",        p identity (fun (prms : perms) -> prms.pretty) envs.implicit_calls
                ]
            in
                mappen_strings (fun (name, env) -> sprintf "%s:\n%s" name env) "\n\n" envs
            

    type [<NoComparison>] state =
      {
        envs             : environments
        effective_perms  : perms
        onCreate_perms   : perms
      }

    let state0 api_calls implicit_calls =
      {
        envs =
          { 
            intents      = Env.empty
            var_decls    = Env.empty
            classes      = TJ.Env0.class_env
            components   = Env.empty
            component_effective_perms = Env.empty

            api_calls =
                List.fold (fun env (a : X.api_call) ->
                    let m = a.method_signature
                    let k = (a.class_fqid, m.name, List.map (fun (p : J.param) -> p.ty) m.paramss)
                    in
                        Env.bind k (perms.of_strings a.call_perms) env)
                    Env.empty api_calls

            implicit_calls =
                List.fold (fun env (a : X.implicit_call) -> Env.bind a.action_string (perms.of_strings a.call_perms) env)
                    Env.empty implicit_calls
          }
        effective_perms = perms.bottom
        onCreate_perms  = perms.bottom
      }

    open Env.M

    let in_var_decls =
        { new Env.M.access<state, id, var_decl> () with
            member self.get st = st.envs.var_decls, st
            member self.set x st = (), { st with envs = { st.envs with var_decls = x } } }

    let in_intents =
        { new Env.M.access<state, address, intent> () with
            member self.get st = st.envs.intents, st
            member self.set x st = (), { st with envs = { st.envs with intents = x } } 
        }

    let in_classes =
        { new Env.M.access<state, fqid, J.class_signature> () with
            member self.get st = st.envs.classes, st
            member self.set x st = (), { st with envs = { st.envs with classes = x } } }

    let in_components =
        { new Env.M.access<state, fqid, componentt> () with
            member self.get st = st.envs.components, st
            member self.set x st = (), { st with envs = { st.envs with components = x } } }

    let in_implicit_calls =
        { new Env.M.access<state, string, perms> () with
            member self.get st = st.envs.implicit_calls, st
            member self.set x st = (), { st with envs = { st.envs with implicit_calls = x } } }

    let in_api_calls =
        { new Env.M.access<state, api_call_id, perms> () with
            member self.get st = st.envs.api_calls, st
            member self.set x st = (), { st with envs = { st.envs with api_calls = x } } }
            
    let in_component_effective_perms =
        { new Env.M.access<state, fqid, perms> () with
            member self.get st = st.envs.component_effective_perms, st
            member self.set x st = (), { st with envs = { st.envs with component_effective_perms = x } } }

    let mkW pkg imp = TJ.M.mkW in_classes in_var_decls (fun vd -> vd.ty) pkg imp

    let private effect_a_component (|C|_|) (FQId qid as fqid) f =
      M {
        do! Env.M.effect in_components fqid (function C x as c -> f x
                                                    | comp -> Prelude.unexpected "component of unknown type %s bound to qid '%s'" (comp.GetType ()).Name qid.pretty)
      }
      
    let effect_activity qid f = effect_a_component (function :? activity as a -> Some a | _ -> None) qid f
    let effect_service qid f = effect_a_component (function :? service as s -> Some s | _ -> None) qid f
    let effect_component qid f = effect_a_component (function c -> Some c) qid f

    let lift_effective_perms f st = (), { st with effective_perms = f st.effective_perms }
    let get_effective_perms (st : state) = st.effective_perms, st
    let set_effective_perms prms = lift_effective_perms (fun _ -> prms)

    let add_effective_perms (prms' : perms) =
        if not prms'.is_empty then Globals.logger.debug High "adding effective perms: %O" prms'
        lift_effective_perms (fun prms -> prms + prms')

    let print_envs =
      M {
        let! state0 = Monad.get_state
        do Globals.logger.debug High "environments:\n%s" state0.envs.pretty
      }

    let trap f (x : #J.node<_>) st =
        try f x st
        with e ->
            Report.trapped x.location e x
            match e with
                | :? NotImplementedException -> ()
                | _ -> ignore <| print_envs st; raise e
            (), st


