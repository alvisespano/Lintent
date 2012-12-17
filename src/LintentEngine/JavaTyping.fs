(*
 * TypeDroid - LintentEngine
 * JavaTyping.fs: Java typing
 * (C) 2012 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
#light

module LintentEngine.Typing.Java

open System
open System.Text.RegularExpressions
open FSharpCommon.Prelude
open FSharpCommon.Log
open FSharpCommon
open LintentEngine
open LintentEngine.Absyn

module J = Java

(* environments *)

type class_env = Env.t<fqid, J.class_signature>

type environments (classes   : class_env,
                   package   : fqid,
                   imports   : fqid list,
                   this_fqid : Absyn.fqid) =
    member val classes = classes with get
    member val package = package with get
    // NOTE: reversing imports order is important to simulate shadowing
    member val imports = imports |> List.rev with get
    member val this_fqid = this_fqid with get

type [< AbstractClass >] ty_environments (classes   : class_env,
                                          package   : fqid,
                                          imports   : fqid list,
                                          this_fqid : fqid) =
    inherit environments (classes, package, imports, this_fqid)
    abstract search_var_ty : id -> Java.ty option


(* lazy class loader *)

//let load_lazy_class_signature bootclasspath classpaths (fqid : fqid) =
//    let s = javap bootclasspath classpaths fqid.pretty

    

(* misc utils *)
        
let rec qualify_ty (envs : environments) =
    let rec R = function
        | J.Ty_Id id as r ->
            match List.tryFind (fun (FQId qid) -> qid.id = id) envs.imports with
                | Some (FQId qid) -> J.Ty_QId qid
                | None ->
                    let (FQId qid as fqid) = envs.package.append id
                    in
                        match Env.search fqid envs.classes with
                            | Some _ -> J.Ty_QId qid
                            | None -> 
                            // TODO: sistemare inner class innestate multiple?
                            let (FQId qid as fqid) = envs.this_fqid.append id
                            match Env.search fqid envs.classes with
                                | Some _ -> J.Ty_QId qid
                                | None -> r

        | J.Ty_Sel (ty, id) -> J.Ty_Sel (R ty, id)

        | J.Ty_App (ty, tyargs) -> J.Ty_App (R ty, List.map (qualify_ty_args envs) tyargs)

        | J.Ty_Array ty -> J.Ty_Array (R ty)

        | J.Ty_Builtin _ as r -> r
    in
        R
        
and qualify_ty_args envs = function
    | J.TyArg_Ty ty              -> J.TyArg_Ty (qualify_ty envs ty)
    | J.TyArg_Wildcard (rel, ty) -> J.TyArg_Wildcard (rel, qualify_ty envs ty)

let resolve_ty envs ty =
    let ty = qualify_ty envs ty
    in
        ty, FQId ty.reifiable

let (|Qualified_Ty|) envs ty = qualify_ty envs ty
let (|Resolved_Ty|) envs ty = resolve_ty envs ty

let search_class_by_ty envs (Resolved_Ty envs (ty, fqid)) =
    match Env.search fqid envs.classes with
        | Some cl -> Some (fqid, cl)
        | None    -> None

let is_subclass_of (envs : environments) (Qualified_Ty envs super_ty) =
    let rec R (Qualified_Ty envs sub_ty) =
        if sub_ty = super_ty then true
        else
            match search_class_by_ty envs sub_ty with
                | None             -> false
                | Some (_, sub_cl) -> List.fold (fun r ty -> r || R ty) false sub_cl.super_tys
    in
        R

type 'a found_member = fqid * J.ty * 'a

let search_in_type ps f (envs : environments) =
    let rec R ty =
        match search_class_by_ty envs ty with
            | None -> []
            | Some (fqid, cl) ->
                let items = List.filter (fun x -> List.forall (fun p -> p x) ps) (f cl)
                match items, cl.super_tys with
                    | [], []      -> []
                    | items, []   -> [(fqid, ty, items)]

                    | items, tys  ->
                        let rs = List.map R tys
                        in
                            (fqid, ty, items) :: (List.concat rs)
    in
        R

(* some common predicates *)
let inline has_name id (x : ^a) = (^a : (member name : ^id) x) = id
let inline is_static (x : ^a) = let m : ^m = (^a : (member modif : 'm) x) in (^m : (member staticc : bool) m)
let inline is_final (x : ^a) = let m : ^m = (^a : (member modif : 'm) x) in (^m : (member final : bool) m)
let (>&&>) f1 f2 x = f1 x && f2 x


let inline resolve_overloaded f envs (tyargs : J.ty_arg list) (argtys : J.ty list) =
    let dist pars =
        let rec dist_ty (Qualified_Ty envs argty) (Qualified_Ty envs party) =
            if argty = party then 0
            else
                match search_class_by_ty envs argty with
                    | None            -> raise (Failure (sprintf "cannot find class for argument type: %O" argty))
                    | Some (fqid, cl) ->
                        match cl.super_tys with
                            | []          -> 0
                            | argsupertys -> 1 + (List.sumBy (fun argsuperty -> dist_ty argsuperty party) argsupertys)
        
        if List.length pars <> List.length argtys then Int32.MaxValue
        else List.zip argtys pars |> List.sumBy (fun (argty, par : J.param) -> dist_ty argty par.ty)
    in
        fun this_ty obj_ty id ->
            try
//                Some (search_in_type [has_name id] f envs this_ty
//                     |> List.map (fun (fqid, ty, meths) -> List.map (fun meth -> (fqid, ty, meth)) meths)
//                     |> List.concat
//                     |> List.minBy (fun (fqid, ty, meth : ^m) -> dist (^m : (member paramss : J.param list) meth)))
                Some (search_in_type [has_name id] f envs obj_ty
                     |> List.map (fun (fqid, _, meths) -> List.map (fun meth -> (fqid, this_ty, meth)) meths)
                     |> List.concat
                     |> List.minBy (fun (fqid, ty, meth : ^m) -> dist (^m : (member paramss : J.param list) meth)))
            with e -> 
                Globals.logger.debug Unmaskerable "resolve_overloaded failed with: %s\n" e.Message
                None

let resolve_overloaded_method_signature envs = resolve_overloaded (fun (cl : J.class_signature) -> cl.method_signatures) envs
let resolve_overloaded_method envs = resolve_overloaded (function :? J.classs as cl -> cl.methods | _ -> []) envs
let resolve_overloaded_constructor envs = resolve_overloaded (function :? J.classs as cl -> cl.constructors | _ -> []) envs

let inline private search_unique ps f envs ty =
    search_in_type ps f envs ty |> List.tryPick (function
        | fqid, ty, [x]                -> Some (fqid, ty, x)
        | fqid, ty, (_ :: _ :: _ as l) -> unexpected "search_unique: multiple items in %O: %s" fqid (mappen_strings (sprintf "%O") ", " l)
        | _, _, []                     -> None)

let search_attribute envs this_ty id =
    search_unique [has_name id] (fun (cl : J.class_signature) -> cl.attributes) envs this_ty

let search_inner_class_signature envs this_ty id =
    search_unique [has_name id (*>&&> is_static*)] (fun cl -> cl.inner_class_signatures) envs this_ty

    

(* java type deductor *)

type [< NoComparison >] resolved_var =
    | RVar of id * J.ty
    | RClass of J.ty (** J.class_signature*)
    | RAttribute of J.attribute found_member
    | RInnerClass of J.class_signature found_member
                    
let resolve_var (envs : ty_environments) this_ty id =
    match envs.search_var_ty id with
        | Some ty -> RVar (id, ty)
        | None ->
            match search_attribute envs this_ty id with
                | Some r -> RAttribute r
                | None ->
                    match search_inner_class_signature envs this_ty id with
                        | Some r -> RInnerClass r
                        | None ->
                            match resolve_ty envs (J.Ty_Id id) with
                                | J.Ty_Id _, _ -> unexpected "unresolved var '%s' within type '%O'" id this_ty
                                | ty, fqid     -> (*let cl = Env.lookup fqid envs.classes in*) RClass ty

let rec deduce_method envs tyargs args this_ty id =
    let argtys = List.map (deduce_expr envs this_ty) args
    match resolve_overloaded_method envs tyargs argtys this_ty this_ty id with
        | Some (_, _, meth) ->
            match meth.rty with
                | None      -> unexpected "deduce_method: void method call in expression"
                | Some ty   -> ty

        | None -> unexpected "cannot resolve overloaded method call: %s(%s)" id (mappen_strings (sprintf "%O") ", " argtys)
            

and deduce_attribute_or_inner_class envs this_ty id =
    match search_attribute envs this_ty id with
        | Some (_, _, att) -> att.ty
        | None ->
            match search_inner_class_signature envs this_ty id with
                | Some (fqid, ty, _) -> J.Ty_Sel (ty, id)
                | None               -> unexpected "deduce_attribute_or_inner_class: '%s' cannot be found within type '%O'" id this_ty

and deduce_member envs acso fqid id =
    match acso with
        | Some (tyargs, args) -> deduce_method envs tyargs args fqid id
        | None                -> deduce_attribute_or_inner_class envs fqid id
  
and deduce_expr (envs : #ty_environments) this_ty (J.Locatable (e, loc)) =
  match e with
    | J.Lit lit ->
        match lit with
            | J.Int _           -> J.Ty_Builtin J.Ty_Int
            | J.Long _          -> J.Ty_Builtin J.Ty_Long
            | J.Float _         -> J.Ty_Builtin J.Ty_Float
            | J.Bool _          -> J.Ty_Builtin J.Ty_Bool
            | J.Double _        -> J.Ty_Builtin J.Ty_Double
            | J.Char _          -> J.Ty_Builtin J.Ty_Char
            | J.String _        -> J.Ty_String
            | J.Array (ty, _)   -> ty
            | J.ClassOp qid     -> J.Ty_App (J.Ty_SQId Config.Java.Names.Type.Class, [J.TyArg_Ty (J.Ty_QId qid)])
            | J.Null            -> J.Ty_Builtin J.Ty_Bottom     
                                    
    | J.Var id ->
        match resolve_var envs this_ty id with
            | RVar (_, ty)    -> ty
            | RClass ty       -> ty
            | RAttribute _
            | RInnerClass _   -> deduce_expr envs this_ty (J.ThisSel (id, loc))

    | J.This -> this_ty
                
    | J.UnOp (J.ArithUnOp, e1)
    | J.BinOp (e1, J.ArithBinOp, _) -> deduce_expr envs this_ty e1

    | J.UnOp (J.LogicUnOp, _)
    | J.BinOp (_, J.LogicBinOp, _) 
    | J.BinOp (_, J.RelBinOp, _)  -> J.Ty_Builtin J.Ty_Bool

    | J.Cast (ty, _) -> ty

    | J.Cond (_, e2, _) -> deduce_expr envs this_ty e2

    | J.Cons (ty, _, _) -> ty

    | J.Subscript (e1, _) ->
        match deduce_expr envs this_ty e1 with
            | J.Ty_Array ty -> ty
            | _             -> unexpected "non-array type in left-hand of subscript"
            
    | J.MemberSel (recp, id, acso) ->
        let recp_ty = deduce_recipient envs this_ty recp
        in
            deduce_member envs acso recp_ty id

and deduce_recipient envs this_ty = function
    | J.Recp_Obj e -> deduce_expr envs this_ty e

    | J.Recp_Super ->
        match search_class_by_ty envs this_ty with
            | Some (_, cl) -> cl.super_ty
            | None         -> J.Ty_Object


module Env0 =

    module N = Config.Java.Names.Type
    
    let private cm = J.class_modifiers (false, false, Java.visibility.Public, false, false)

    let private class_of_pervasive (s, super) =
        let extends_opt = match super with | "" -> None | super -> Some (J.Ty_QId (Absyn.qid.of_string super))
        let qid = qid.of_string s
        in
            new J.classs (modif = cm, name = qid.id, ty_params = [], extends = extends_opt, loc = uloc, annots = [],
                        implements = [], attributes = [], methods = [], constructors = [], inner_classes = [], 
                        inner_interfaces = [], initializer = [], static_initializer = [])

    let pervasives =
        let l t = t, N.Object
        let a t = t, N.Activity
        let s t = t, N.Service

        [
        //N.Object, "";
        //l N.Class;
        l N.String;
        l N.Array;
        l N.Integer;
        l N.Float;
        l N.Double;
        l N.Long;
        l N.Char;
        l N.Boolean;
        l N.Byte;
        l N.CharSequence;
        l N.Serializable;
        l N.ArrayList;
        l N.Context;
        l N.Location;
        l N.LocationManager;
        l N.LocationProvider;
        l N.Menu;
        l N.WallpaperManager;

        a N.AccountAuthenticatorActivity;
        a N.ActivityGroup;
        a N.AliasActivity;
        a N.BasicDream;
        a N.ExpandableListActivity;
        a N.FragmentActivity;
        a N.ListActivity;
        a N.NativeActivity;

        N.ContextWrapper, N.Context;
        N.ContextThemeWrapper, N.ContextWrapper;
        N.Service, N.ContextWrapper;

        s N.AbstractInputMethodService;
        s N.AccessibilityService;
        s N.IntentService;
        s N.RecognitionService;
        s N.RemoteViewsService;
        s N.SpellCheckerService;
        s N.TextToSpeechService;
        s N.VpnService;
        s N.WallpaperService
        ]
    
    let std_lib_classes =
        let intent_ty = J.Ty_QId (qid.of_string "Intent")
        let am = new J.attribute_modifiers(true, true, J.Public)
        let cm = new J.constructor_modifiers (J.Public, false, false, false)
        let mm = new J.method_modifiers (false, false, J.Public)
        let pm = new J.param_modifiers (false)
        let a name lit = new J.annotation (name = name, bindings = [("value", lit)], loc = Absyn.uloc)
        let pintent = [new J.param (modif = pm, name = "intent", ty = intent_ty, loc = uloc)]
        let pstring name = [new J.param (modif = pm, name = name, ty = J.Ty_String, loc = uloc)]
        let pint name = [new J.param (modif = pm, name = name, ty = J.Ty_Builtin J.Ty_Int, loc = uloc, annots = [a "L" (J.String "^:;_<-")])]        
        let pty s name = new J.param (modif = pm, name = name, ty = (J.Ty_QId (qid.of_string s)), loc = uloc)
        let m name rty ps = new J.methodd (modif = mm, name =name, body = [], ty_params = [], rty = rty, paramss = ps, throws = [], loc = uloc)
        let m_ann name rty ps anns = new J.methodd (modif = mm, name =name, body = [], ty_params = [], rty = rty, paramss = ps, throws = [], loc = uloc, annots = anns)
        let c name rty ps = new J.constructorr (modif = cm, name =name, body = [], ty_params = [], paramss = ps, throws = [], loc = uloc)

        let object_class =
            let ms =
              [
                m "equals" (Some (J.Ty_Builtin J.Ty_Bool)) [new J.param(modif = pm, name = "obj", ty = J.Ty_Object, loc = uloc)]
                m "toString" (Some J.Ty_String) []
              ]
            in
                new J.classs (modif = cm, name = "Object", ty_params = [], extends = None,  
                                implements = [], attributes = [], methods = ms, constructors = [], inner_classes = [], 
                                inner_interfaces = [], initializer = [], static_initializer = [], loc = uloc, annots = []) 

        let string_class =
            let ms =
              [ 
                m "charAt" (Some (J.Ty_Builtin J.Ty_Char)) (pint "index")
                m "indexOf" (Some (J.Ty_Builtin J.Ty_Int)) [new J.param(modif = pm, name = "str", ty = J.Ty_String, loc = uloc)]
                m "substring" (Some J.Ty_String) (pint "start")
                m "substring" (Some J.Ty_String) ((pint "start") @ (pint "end"))
              ]
            in
                new J.classs (modif = cm, name = "String", ty_params = [], extends = Some (J.Ty_QId (Absyn.qid.of_string N.Object)),  
                                implements = [], attributes = [], methods = ms, constructors = [], inner_classes = [], 
                                inner_interfaces = [], initializer = [], static_initializer = [], loc = uloc, annots = [])   
        
        let menu_infl_class =
            
            let ms =
              [
                m "inflate" (Some (intent_ty)) ((pint "menuRes") @ [new J.param(modif = pm, name = "menu", ty = J.Ty_QId (qid.of_string N.Menu), loc = uloc, annots = [a "L" (J.String "^:;_<-")])]) 
              ]
            in
                new J.classs (modif = cm, name = "MenuInflater", ty_params = [], extends = Some (J.Ty_Object),
                                implements = [], attributes = [], methods = ms, constructors = [], inner_classes = [], 
                                inner_interfaces = [], initializer = [], static_initializer = [], loc = uloc, annots = [])  

        let activity_class =  
        
            let atts =
              [
                new J.attribute (modif = am, name = "RESULT_CANCELED", ty = J.Ty_Builtin J.Ty_Int, loc = uloc)
                new J.attribute (modif = am, name = "RESULT_OK", ty = J.Ty_Builtin J.Ty_Int, loc = uloc)
              ]      
            
            let ms =
              [
                m "getIntent" (Some (intent_ty)) []
                m "startActivity" None pintent
                m "startActivityForResult" None (pintent @ (pint "resCode"))
                m "setResult" None (pint "resCode")
                m "setContentView" None (pint "layoutResID")
                m "setResult" None ((pint "resCode") @ pintent)
                m "getMenuInflater" (Some (J.Ty_QId (qid.of_string N.MenuInflater))) []
                m "onCreate" None [new J.param(modif = pm, name = "savedInstanceState", ty = J.Ty_QId (qid.of_string N.Bundle), loc = uloc)]
                m "finish" None []
              ]
            in
                new J.classs (modif = cm, name = "Activity", ty_params = [], extends = Some (J.Ty_QId (Absyn.qid.of_string N.ContextThemeWrapper)),  
                                implements = [], attributes = atts, methods = ms, constructors = [], inner_classes = [], 
                                inner_interfaces = [], initializer = [], static_initializer = [], loc = uloc, annots = [])     
        let loc_mng_class =        
            
            let ms =
              [
                m "getLastKnownLocation" (Some (J.Ty_QId (qid.of_string N.Location))) (pstring "provider")
              ]
            in
                new J.classs (modif = cm, name = "LocationManager", ty_params = [], extends = Some (J.Ty_Object),  
                                implements = [], attributes = [], methods = ms, constructors = [], inner_classes = [], 
                                inner_interfaces = [], initializer = [], static_initializer = [], loc = uloc, annots = [])

        let camera_class =
            let ms =
              [
                m "open" (Some (J.Ty_QId (qid.of_string N.Camera))) []
                m "startPreview" None []
              ]
            in
                new J.classs (modif = cm, name = "Camera", ty_params = [], extends = Some (J.Ty_Object),  
                                implements = [], attributes = [], methods = ms, constructors = [], inner_classes = [], 
                                inner_interfaces = [], initializer = [], static_initializer = [], loc = uloc, annots = [])

        let wlppr_mng_class =
            let ms =
              [
                m "getInstance" (Some (J.Ty_QId (qid.of_string N.WallpaperManager))) [pty N.Context "context"]
                m "clear" None []
              ]
            in
                new J.classs (modif = cm, name = "WallpaperManager", ty_params = [], extends = Some (J.Ty_Object),  
                                implements = [], attributes = [], methods = ms, constructors = [], inner_classes = [], 
                                inner_interfaces = [], initializer = [], static_initializer = [], loc = uloc, annots = [])
          
        let vibrator_class =
            let ms =
              [
                m "vibrate" None [pty N.Long "ms"]
              ]
            in
                new J.classs (modif = cm, name = "Vibrator", ty_params = [], extends = Some (J.Ty_Object),  
                                implements = [], attributes = [], methods = ms, constructors = [], inner_classes = [], 
                                inner_interfaces = [], initializer = [], static_initializer = [], loc = uloc, annots = [])
                          
        let pending_int_class =
            let ms =
              [
                m "getActivity" (Some (J.Ty_QId (qid.of_string N.PendingIntent))) [pty N.Context "ctx"; pty N.Integer "n" ; pty N.Intent "intent"; pty N.Integer "flags"]
              ]

            in
                new J.classs (modif = cm, name = "PendingIntent", ty_params = [], extends = Some (J.Ty_Object),  
                                implements = [], attributes = [], methods = ms, constructors = [], inner_classes = [], 
                                inner_interfaces = [], initializer = [], static_initializer = [], loc = uloc, annots = [])

        let bundle_class =
            let ms =
              [
                m "size" (Some (J.Ty_QId (qid.of_string N.Integer))) []
              ]
            in
                new J.classs (modif = cm, name = "Bundle", ty_params = [], extends = Some (J.Ty_QId (Absyn.qid.of_string N.ContextThemeWrapper)),  
                                implements = [], attributes = [], methods = ms, constructors = [], inner_classes = [], 
                                inner_interfaces = [], initializer = [], static_initializer = [], loc = uloc, annots = []) 
             
        let class_class =
            let cs =
              [
                c "Class" (Some (J.Ty_QId (qid.of_string N.Class))) []
              ]
            in
                new J.classs (modif = cm, name = "Class", ty_params = [{ name = "C"; parent = J.Ty_Object; interfaces = [] }], extends = Some (J.Ty_Object),  
                                implements = [], attributes = [], methods = [], constructors = cs, inner_classes = [], 
                                inner_interfaces = [], initializer = [], static_initializer = [], loc = uloc, annots = [])
               

        let intent_class =        
            let plabel = [new J.param (modif = pm, name = "label", ty = J.Ty_String, loc = uloc)]
            let pdef ty = [new J.param (modif = pm, name = "default", ty = ty, loc = uloc)]
            let p ty = [new J.param (modif = pm, name = "value", ty = ty, loc = uloc)]
            let putExtra ty = m "putExtra" (Some (J.Ty_QId (qid.of_string N.Intent))) (plabel @ (p ty))
            let getExtra ps s ty = m (sprintf "get%sExtra" s) (Some ty) ps
            let getExtra1 = getExtra plabel
            let getExtra2 s ty = getExtra (plabel @ (pdef ty)) s ty
            let ty_class = J.Ty_App (J.Ty_QId (qid.of_string N.Class), [J.TyArg_Wildcard (J.Extends, J.Ty_Object)])

            let ms =
              [
                putExtra (J.Ty_Builtin J.Ty_Int)
                putExtra (J.Ty_Builtin J.Ty_Long)
                putExtra J.Ty_String
                putExtra (J.Ty_Builtin J.Ty_Char)
                putExtra (J.Ty_Builtin J.Ty_Bool)
                m "putExtra" (Some (J.Ty_QId (qid.of_string N.Intent))) [pty N.String "name"; pty N.Serializable "value"] 

                getExtra1 "Int" (J.Ty_Builtin J.Ty_Int)
                getExtra2 "Int" (J.Ty_Builtin J.Ty_Int)
                getExtra1 "Long" (J.Ty_Builtin J.Ty_Long)
                getExtra2 "Long" (J.Ty_Builtin J.Ty_Long)
                getExtra1 "Char" (J.Ty_Builtin J.Ty_Char)
                getExtra2 "Char" (J.Ty_Builtin J.Ty_Char)
                getExtra1 "String" J.Ty_String
                getExtra2 "String" J.Ty_String
                getExtra1 "Boolean" (J.Ty_Builtin J.Ty_Bool)
                getExtra2 "Boolean" (J.Ty_Builtin J.Ty_Bool)
                m "getExtras" (Some (J.Ty_QId (qid.of_string N.Bundle))) []
                m "getSerializableExtra" (Some (J.Ty_QId (qid.of_string N.Serializable))) (pstring "name")
              ]

            let cs =
              [
                c "Intent" (Some (J.Ty_QId (qid.of_string N.Intent))) []
                c "Intent" (Some (J.Ty_QId (qid.of_string N.Intent))) (p J.Ty_String)
                c "Intent" (Some (J.Ty_QId (qid.of_string N.Intent))) (pty N.Context "ctx" :: p ty_class)
              ]
            in
                new J.classs (modif = cm, name = "Activity", ty_params = [], extends = Some (J.Ty_QId (Absyn.qid.of_string N.ContextThemeWrapper)),  
                                implements = [], attributes = [], methods = ms, constructors = cs, inner_classes = [], 
                                inner_interfaces = [], initializer = [], static_initializer = [], loc = uloc, annots = [])        

        in
          [
            N.Intent, intent_class
            N.Class, class_class
            N.Activity, activity_class
            N.Object, object_class
            N.String, string_class
            N.LocationManager, loc_mng_class
            N.MenuInflater, menu_infl_class
            N.Camera, camera_class
            N.WallpaperManager, wlppr_mng_class
            N.Vibrator, vibrator_class
            N.PendingIntent, pending_int_class
            N.Bundle, bundle_class
          ]
    
    let class_env : class_env =
        let env = 
            List.fold (fun env ((s, _) as p) -> Env.bind (FQId (qid.of_string s)) (class_of_pervasive p :> J.class_signature) env) Env.empty pervasives
        let env =
            List.fold (fun env (name, cl) -> Env.bind (FQId (qid.of_string name)) (cl :> J.class_signature) env) env std_lib_classes
        in
            env


(* monadic wrapper *)

module M =

    type wrap<'st> =
      abstract apply<'a> : (ty_environments -> 'a) -> 'st -> 'a * 'st

    type W<'st> (w : wrap<'st>) =
        member inline private self.overloaded resolve tyargs args this_ty obj_ty id =
            w.apply <| fun envs -> resolve envs tyargs (List.map (deduce_expr envs this_ty) args) this_ty obj_ty id

        member self.resolve_overloaded_method_signature = self.overloaded resolve_overloaded_method_signature
        member self.resolve_overloaded_method = self.overloaded resolve_overloaded_method
        member self.resolve_overloaded_constructor = self.overloaded resolve_overloaded_constructor

        member self.search_attribute this_ty id =
            w.apply <| fun envs -> search_attribute envs this_ty id

        member self.search_inner_class_signature this_ty id =
            w.apply <| fun envs -> search_inner_class_signature envs this_ty id

        member self.resolve_var this_ty id =
            w.apply <| fun envs -> resolve_var envs this_ty id

        member self.try_deduce_expr this_ty e =
            w.apply <| fun envs -> try Some (deduce_expr envs this_ty e) with e -> None

        member self.deduce_recipient this_ty lh =
            w.apply <| fun envs -> deduce_recipient envs this_ty lh
  

    let create_wrap in_classes in_types extract_ty package imports this_ty =
      { new wrap<_> with
        member self.apply f st = 
            let (classes, st) = Env.M.get in_classes st
            let (st, _) = Monad.get_state st
            let ty_envs =
              { new ty_environments (classes, package, imports, this_ty)
                with
                    override self.search_var_ty id =
                        let (xo, _) = Env.M.search in_types id st
                        in
                            Option.map extract_ty xo     
              }
            in
                (f ty_envs, st)
      }

    let mkW in_classes in_types extract_ty package_qid imports this_ty = new W<_> (create_wrap in_classes in_types extract_ty package_qid imports this_ty)
              
