(*
 * TypeDroid - LintentEngine
 * ComponentTyping.fs: component typing - intents, activity, services
 * (C) 2012 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)

module LintentEngine.Typing.Component

open System
open System.Text.RegularExpressions
open FSharpCommon.Prelude
open FSharpCommon.Log
open FSharpCommon
open LintentEngine
open LintentEngine.Absyn
open Typing.Android

module J = LintentEngine.Absyn.Java
module TJ = Typing.Java
module N = Config.Java.Names
module D = Detector

type [< NoComparison >] context =
  {
    this_ty             : J.ty
    envs                : TJ.environments
    W                   : TJ.M.W<CustomMonad.state>
    current_method      : J.methodd option
  }
with
    member self.this_fqid = let (_, fqid) = TJ.resolve_ty self.envs self.this_ty in fqid
    
    member self.in_component = self.in_service || self.in_activity

    member self.in_activity = self.in_a_component D.Activity.(|Class|_|) 
    member self.in_service = self.in_a_component D.Service.(|Class|_|) 

    member private self.in_a_component (|CompClass|_|) =
        match TJ.search_class_by_ty self.envs self.this_ty with
            | Some (_, CompClass self.envs _) -> true
            | _                               -> false
    
    member self.in_onActivityResult =
        self.in_activity
            && something (function D.Activity.Method_onActivityResult self.envs _ -> true | _ -> false) false self.current_method


(*
 * static const evaluator
 *)

module Const =    

    open CustomMonad
   
    let num_unop loc0 = function
        | J.Neg     -> fun n -> -n
        | J.BNot    -> fun n -> ~~~n
        | J.PreInc  -> fun n -> n + 1L
        | J.PreDec  -> fun n -> n - 1L
        | J.PostInc -> identity
        | J.PostDec -> identity
        | op        -> unexpected loc0 "operator %O in arithmetic integral expression" op

    let real_unop loc0 = function
        | J.Neg     -> fun n -> -n
        | J.PreInc  -> fun n -> n + 1.0
        | J.PreDec  -> fun n -> n - 1.0
        | J.PostInc -> identity
        | J.PostDec -> identity
        | op        -> unexpected loc0 "operator %O in arithmetic floating-point expression" op

    let bool_unop loc0 = function
        | J.Not    -> (not)
        | op       -> unexpected loc0 "operator %O in boolean expression" op

    let num_binop loc0 = function
        | J.Plus    -> (+) : int64 -> int64 -> int64
        | J.Minus   -> (-)
        | J.Mult    -> (*)
        | J.Div     -> (/)
        | J.Mod     -> (%)
        // TODO: other int operators
        | op        -> not_implemented loc0 "operator %O in arithmetic integral expression" op

    let real_binop loc0 = function
        | J.Plus    -> (+) : float -> float -> float
        | J.Minus   -> (-)
        | J.Mult    -> (*)
        | J.Div     -> (/)
        | J.Mod     -> (%)
        // TODO: other int operators
        | op        -> not_implemented loc0 "operator %O in arithmetic floating-point expression" op

    let bool_binop loc0 = function
        | J.And -> (&&)
        | J.Or  -> (||)
        | op    -> unexpected loc0 "operator %O in boolean expression" op
   
    let rec eval_member_call loc0 (ctx : context) that_ty id tyargs args =
      M {
        let! o = ctx.W.resolve_overloaded_method_signature tyargs args (ctx.this_ty) that_ty id
        match o with
            | Some (that_fqid, that_ty, (:? J.methodd as meth)) ->
                let pes = List.zip meth.paramss args
                return! Env.M.fork in_var_decls
                    (M {
                    for (pi, ei) in pes do
                        let! lc = Monad.Lazy.suspend (eval_expr ctx ei)
                        let argi = { modif  = new J.decl_modifiers (final = pi.modif.final, staticc = false)
                                     expr   = Some (ei, lc)
                                     ty     = pi.ty }
                        do! Env.M.bind in_var_decls pi.name argi
                    return! eval_method_body { ctx with this_ty = that_ty } meth
                    })
            | _ -> return None
      }

    and eval_member_sel loc0 (ctx : context) that_ty id =
      M {
        let! a = ctx.W.search_attribute that_ty id
        match a with
            | None ->
                let! ic = ctx.W.search_inner_class_signature that_ty id
                match ic with
                    | Some (fqid, ty, cl) -> return Some (CObj (J.Ty_Sel (ty, cl.name), None))
                    | None                -> return unexpected loc0 "eval_expr: unknown class %O member: %s" that_ty id

            | Some (fqid, ty, att) -> 
                match att.modif.final, att.expr with
                    | true, Some e -> return! eval_expr { ctx with this_ty = that_ty } e
                    | _            -> return None
      }

    and eval_expr (ctx : context) (e : J.expr) =
      M {
        try return! eval_expr' ctx e
        with ex -> Report.trapped e.location ex e; return None
      }
      
    and private eval_expr' (ctx : context) (J.Locatable (e0', loc0) as e0) =    
      M {
        match e0' with
            | J.Lit l -> return Some (CLit l)

            | J.MemberSel (J.Call (e, id, tyargs, args)) ->
                let! co = eval_expr ctx e
                match co with
                    | Some (CObj (that_ty, _)) -> return! eval_member_call loc0 ctx that_ty id tyargs args
                    | None -> return None
                    | _    -> return unexpected loc0 "eval_expr: call left-hand side evaluates to non-object"

            | J.MemberSel (J.Sel (e, id)) ->
                let! co = eval_expr ctx e
                match co with
                    | Some (CObj (that_ty, _)) -> return! eval_member_sel loc0 ctx that_ty id
                    | None -> return None
                    | _    -> return unexpected loc0 "eval_expr: select left-hand side evaluates to non-object"

            | J.MemberSel (J.SuperCall (id, tyargs, args)) ->
                let! clo = Env.M.search in_classes ctx.this_fqid
                match clo with
                    | None    -> return None
                    | Some cl -> return! eval_member_call loc0 ctx cl.super_ty id tyargs args

            | J.MemberSel (J.SuperSel id) ->
                let! clo = Env.M.search in_classes ctx.this_fqid
                match clo with
                    | None    -> return None
                    | Some cl -> return! eval_member_sel loc0 ctx cl.super_ty id

            | J.Var id ->                
                let! o = ctx.W.resolve_var ctx.this_ty id
                match o with
                    | TJ.RVar (id, _) ->
                        let! vd = Env.M.lookup in_var_decls id
                        match vd with
                            | { modif = modif; expr = Some (_, lc) } ->
                                let r = lc.Value
                                if r.IsSome && not modif.final then Report.Hint.non_final_variable loc0 id
                                return r

                            | _ -> return None              

                    | TJ.RAttribute _
                    | TJ.RInnerClass _ -> return! eval_expr ctx (J.ThisSel (id, loc0))

                    | TJ.RClass ty -> return Some (CObj (ty, None))                                

            | J.This ->
                return Some (CObj (ctx.this_ty, None))
            
            | J.Cons (TJ.Qualified_Ty ctx.envs ty, (tyargs, _), _) ->
                return Some (CObj (ty, Some (new address (e0))))

            | J.Cond (e1, e2, e3) ->
                let! c1 = eval_expr ctx e1
                match c1 with
                    | CBool b -> return! eval_expr ctx (if b then e2 else e3)
                    | Some _  -> return unexpected loc0 "eval_expr: non-bool in conditional expression"
                    | None    -> return None                        
                                
            | J.UnOp (op, e1) ->
                let! c1 = eval_expr ctx e1
                match (op, c1) with
                    | op, CNum a  -> return CNum (num_unop loc0 op a)
                    | op, CReal a -> return CReal (real_unop loc0 op a)
                    | op, CBool a -> return CBool (bool_unop loc0 op a)
                    | _           -> return not_implemented loc0 "eval_expr: operator '%O' in unary application of const expr" op

            | J.BinOp (e1, op, e2) ->
                let! c1 = eval_expr ctx e1
                let! c2 = eval_expr ctx e2
                match (c1, op, c2) with
                    | CNum a, op, CNum b            -> return CNum (num_binop loc0 op a b)
                    | CReal a, op, CReal b          -> return CReal (real_binop loc0 op a b)
                    | CBool a, op, CBool b          -> return CBool (bool_binop loc0 op a b)

                    | CString a, J.Plus, CString b  -> return CString (sprintf "%s%s" a b)
                    | CString a, J.Plus, CNum b     -> return CString (sprintf "%s%d" a b)
                    | CNum a, J.Plus, CString b     -> return CString (sprintf "%d%s" a b)
                    | CString a, J.Plus, CReal b     -> return CString (sprintf "%s%g" a b)
                    | CReal a, J.Plus, CString b     -> return CString (sprintf "%g%s" a b)
                    | CString a, J.Plus, CChar b     -> return CString (sprintf "%s%c" a b)
                    | CChar a, J.Plus, CString b     -> return CString (sprintf "%c%s" a b)

                    | None, _, _
                    | _, _, None                    -> return None
                    | _                             -> return not_implemented loc0 "eval_expr: operator '%O' in binary application of const expr" op
            
            | J.Cast (TJ.Qualified_Ty ctx.envs ty, e) ->
                let! co = eval_expr ctx e
                match co with
                    | Some (CObj (fqid, addr)) -> return Some (CObj (ty, addr))
                    | Some (CLit _) as r       -> return r
                    | None                     -> return None

            | J.Subscript (e1, e2) ->
                let! c1 = eval_expr ctx e1
                match c1 with
                    | Some (CLit (J.Array (_, es))) ->
                        let! c2 = eval_expr ctx e2
                        match c2 with
                            | Some (CLit (J.Int n)) -> return! eval_expr ctx (es.Item n)
                            | None   -> return None
                            | Some r -> return unexpected loc0 "eval_expr: array subscript evaluates to non-int: %O" r

                    | _ -> return None
      }

    and eval_method_body ctx (meth : J.methodd) =
      M {
        try return! Monad.List.pick (eval_statement ctx) meth.body
        with _ -> return None
      }

    and eval_statement ctx (J.Locatable (st, _)) =
      M {
        match st with
            | J.Return (Some e) ->
                let! r = eval_expr ctx e
                return Some r

            | _ -> return None
      }


(* 
 * aux analysis utils
 *)

open CustomMonad

(* misc evaluators *)

let eval_activity_result_code (ctx : context) ce =
  M {
    let! vo = Const.eval_expr ctx ce
    return match vo with
            | CNum code     -> Some (sprintf "%d" code)
            | Some (CLit l) -> unexpected ce.location "result code evaluates to non-int litarel: %O" l
            | Some _        -> unexpected ce.location "result code evaluates to object"
            | None          -> Report.Warn.nonconst_activity_result_code ce.location ctx.this_ty.pretty; None
  }

let eval_intent_extra_key (ctx : context) (addr : address) ke =
  M {
    let! kvo = Const.eval_expr ctx ke
    return match kvo with
            | CString key -> key                    
            | Some _            -> unexpected ke.location "extra key expression of intent '%s' evaluates to non-string value" addr.pretty
            | None              -> Report.Warn.nonconst_intent_extra_key ke.location addr.pretty;
                                   Config.Typing.fallback_intent_extra_key addr.pretty ke
  }

(* intent utilities *)

let eval_and_lookup_intent (ctx : context) ie =
  M {
    let! cio = Const.eval_expr ctx ie
    match cio with
        | Some (CObj (D.PendingIntent.Ty ctx.envs, Some addr))
        | Some (CObj (D.Intent.Ty ctx.envs, Some addr)) ->
            let! i = Env.M.lookup in_intents addr
            return (addr, i)

        | None ->
            Report.Warn.nonconst_intent ie.location
            let i = new intent (Intent.Undefined)
            let addr = new address (ie)
            do! Env.M.bind in_intents addr i
            return (addr, i)

        | _ -> return unexpected ie.location "expected expression evaluating to object of type %s" N.Type.Intent
  }

let create_intent_by_constructor_args loc0 (ctx : context) args =
  M {
    match args with
        | [] ->
            return new intent (Intent.Undefined)

        // quick pattern matching against litarals
        //

        | [D.E (J.Lit (J.String s))] ->
            return new intent (Intent.Implicit s)

        | [D.E J.This; D.E (J.Lit (J.ClassOp qid))] ->
            let _, fqid = TJ.resolve_ty ctx.envs (J.ty.of_qid qid)
            return new intent (Intent.Explicit fqid)

        // otherwise go through typing and const-evaluation of arguments
        // 

        | [e] ->
            let! tyo = ctx.W.try_deduce_expr ctx.this_ty e
            match tyo with
                | Some (J.Ty_String) ->
                    let! co = Const.eval_expr ctx e
                    let r =
                        match co with
                            | None      -> Report.Warn.nonconst_intent_action_string loc0;
                                           Config.Typing.fallback_intent_action_string e
                            | CString s -> s
                            | Some _    -> unexpected e.location "intent action string evaluates to non-string value"
                    return new intent (Intent.Implicit r)

                | Some (D.Intent.Ty ctx.envs) ->
                    let! (_, i) = eval_and_lookup_intent ctx e
                    return i.clone

                | _ -> return not_implemented loc0 "unknown intent unary constructor overload"

        | [e1; e2] ->
            let! c1 = Const.eval_expr ctx e1
            let! c2 = Const.eval_expr ctx e2
            match c1, c2 with
                | Some (CObj (this_ty, _)), Some (CLit (J.ClassOp qid)) when this_ty = ctx.this_ty ->
                    let _, fqid = TJ.resolve_ty ctx.envs (J.ty.of_qid qid)
                    return new intent (Intent.Explicit fqid)

                | _ -> return Report.Err.intent_owner_is_not_this e1.location

        | _ -> return unexpected loc0 "unknown intent constructor"
  }

let bind_annotated_intent iaddr i anns =
  M {
    do! Env.M.bind in_intents iaddr i
    match anns with
        | D.Intent.Annotated (s, loc) ->
            let () =                
                try
                    (Globals.logger.debug Normal "parsing intent annotation: \"%s\"" s;
                    let bs = Parsing.parse_intent_annotations s in
                    (for (key, ty) in bs do i.add_put_extra loc key ty (Intent.Sensitive (iaddr, i)));
                    do i.locked <- true)
                with _ -> do Report.Warn.illformed_intent_annotation loc iaddr.pretty s
            in
                ()
        | _ -> ()
  }


  
 (*
 * intent & activity type analyzer
 *)

let analyze_any_startActivity (ctx : context) (ie, ceo) (node : J.node<obj>) =
  M {
    let is_forResult = Option.isSome ceo
    let! codeo = Monad.Option.bind (eval_activity_result_code ctx) ceo
    let! (iaddr, i) = eval_and_lookup_intent ctx ie
    match i.recipient with
        | Intent.Undefined -> Report.Warn.undefined_intent_recipient ie.location iaddr.pretty

        | recp ->
            do! effect_activity ctx.this_fqid (fun a -> a.add_out_requests (i, codeo))
            node.tag <- Some (Tag.App (is_forResult, iaddr) :> obj)
  }

let rec analyze_decl loc (ctx : context) (modif : J.basic_modifiers) ((ty, id, annots) : J.decl) eo =
  M {
    let! elco = Monad.Option.bind (fun e -> M { let! lco = analyze_and_eval_expr ctx (Some annots) e in return Some (e, lco) }) eo
    do! Env.M.bind in_var_decls id { var_decl.modif = new J.decl_modifiers (final = modif.final); expr = elco;  ty = ty }
  }

and analyze_statement (ctx : context) (st : J.statement) =
  M {
    //Globals.logger.debug Low "[st] %s" st.pretty

    let loc0 = st.location

    // visit statements
    //
    //

    match st.value with        
        | J.Decl (modif, ((_, _, annots) as decl), eo) ->
            //do! Monad.Option.iter (analyze_expr ctx (Some annots)) eo
            do! analyze_decl loc0 ctx modif decl eo
            
        | J.Assign (e1, e2) ->
            let! co1 = analyze_and_eval_expr ctx None e1
            let! co2 = analyze_and_eval_expr ctx None e2
            match e1 with
                | D.E (J.Var id) ->
                    let! rv = ctx.W.resolve_var ctx.this_ty id
                    match rv with
                        | TJ.RVar (id, ty)           -> do! Env.M.update in_var_decls id (fun vd -> { vd with ty = ty; expr = Some (e2, co2) })
                        | TJ.RAttribute (_, ty, att) -> Report.Warn.assignment_of_attribute loc0 ty.pretty att.name
                        | _                          -> return unexpected loc0 "assignment of class"
                | _ -> return not_implemented loc0 "non-var in left side of assignment"
                       
        | J.If (e, b, bo) ->
            do! analyze_block ctx b
            do! Monad.Option.iter (analyze_block ctx) bo
            do! analyze_expr ctx None e

        | J.DoWhile (b, e)
        | J.While (e, b) ->
            do! analyze_block ctx b
            do! analyze_expr ctx None e
        
        | J.For (st1o, eo, st2o, b) ->
            do! analyze_special_block (M {
                do! Monad.Option.iter (analyze_statement ctx) st1o
                do! Monad.Option.iter (analyze_statement ctx) st2o
                return ctx
                }) b
            do! Monad.Option.iter (analyze_expr ctx None) eo

        | J.ForEach ((ty, id, annots), e, b) ->
            do! analyze_special_block (M {
                do! Env.M.bind in_var_decls id { var_decl.modif = new J.decl_modifiers (); ty = ty; expr = None }
                return ctx
                }) b
            do! analyze_expr ctx (Some annots) e

        | J.Try (b, cbs, fbo) ->
            do! analyze_block ctx b
            for (p, b) in cbs do
                do! analyze_special_block (M {
                    do! Env.M.bind in_var_decls p.name { var_decl.modif = new J.decl_modifiers (final = p.modif.final); ty = p.ty; expr = None }
                    return ctx
                    }) b
            do! Monad.Option.iter (analyze_block ctx) fbo

        | J.Switch (e, cs, defbo) ->
            for (_, b) in cs do
                do! analyze_block ctx b
            do! Monad.Option.iter (analyze_block ctx) defbo
            do! analyze_expr ctx None e

        | J.Return eo ->
            do! Monad.Option.iter (analyze_expr ctx None) eo

        | J.Assert (e, eo) ->
            do! analyze_expr ctx None e
            do! Monad.Option.iter (analyze_expr ctx None) eo

        | J.StatementExpr e
        | J.Throw e as st ->
            do! analyze_expr ctx None e

        | J.ThisCons (_, es)
        | J.SuperCons (_, es) ->
            for e in es do
                do! analyze_expr ctx None e

        // ignored statements
        | J.Break _
        | J.Continue _
        | J.Labeled _ -> ()


    // detect special Android stuff
    //
    //

    match st with

        // intent extras
        //

        | D.PendingIntent.Decl ctx.envs (_, _, ie, annots) ->
             match annots with
                | D.Annot.MultipleUnaryString Config.Java.Annot.Priv.annotation Config.Java.Annot.Priv.declassify (s, _) ->
                    let sa = s.Split ([|',';';'|], StringSplitOptions.RemoveEmptyEntries)
                    let p = new perms (seq { for s in sa do yield new perm (s.Trim ()) })
                    Globals.logger.debug High "annotation found in pending intent decl: %O" p
                    let! (iaddr, _) = eval_and_lookup_intent ctx ie
                    st.tag <- Some (Tag.PendingIntentDeclassify (p, iaddr) :> obj)
                | _ -> ()

        | D.Intent.PutExtra (ie, ke, ve) ->
            let! (addr, i) = eval_and_lookup_intent ctx ie
            let! k = eval_intent_extra_key ctx addr ke
            let! vtyo = ctx.W.try_deduce_expr ctx.this_ty ve
            let vty = either J.Ty_Object vtyo
            let! ec =
              M {
                match vty with
                    | D.PendingIntent.Ty ctx.envs
                    | D.Intent.Ty ctx.envs ->
                        let! (iaddr, i) = eval_and_lookup_intent ctx ve
                        return Intent.Sensitive (iaddr, i)

                    | _ ->
                        let! vco = Const.eval_expr ctx ve
                        return Intent.NonSensitive vco
              }
            i.add_put_extra loc0 k vty ec

                
        // activity API
        //
                    
        // TODO: onActivityResult() deve avere qualche forma di analisi dello switch o non serve fare niente?
//        | D.S (J.Switch (e, cases, bo)) when mode.is_in_onActivityResult ->
//            match e, mode with
//                | J.Var id, Some (_, resultCode, _) when id = resultCode ->
//                    for (ce, b) in cases do
//                        let! codeo = eval_activity_result_code ctx.this_fqid (Some ce)
//                        match codeo with
//                            | None -> return unexpected "non-statically evaluable case label in onActivityResult() switch over result code"
//                            | Some code -> 


        | D.Activity.StartService e when ctx.in_component ->
            let! (addr, i) = eval_and_lookup_intent ctx e
            let! i = Env.M.lookup in_intents addr
            match i.recipient with
                | Intent.Undefined -> do! effect_activity ctx.this_fqid (fun a -> a.add_out_requests (i, None))
                | _                -> Report.Warn.defined_intent_recipient_in_setResult e.location addr.pretty
            

        | D.Activity.SetResult (ce, eo) when ctx.in_activity ->
            let! aio = Monad.Option.map (eval_and_lookup_intent ctx) eo
            let! codeo = eval_activity_result_code ctx ce
            do! Monad.Option.iter (fun (addr, i) -> M {
                let! i = Env.M.lookup in_intents addr
                match i.recipient with
                    | Intent.Undefined -> do! effect_activity ctx.this_fqid (fun a -> a.add_out_results (i, codeo))
                    | _                -> Report.Warn.defined_intent_recipient_in_setResult eo.Value.location addr.pretty
                }) aio

        | D.Activity.StartActivity_or_StartActivityForResult (ie, ceo) when ctx.in_activity ->
            do! analyze_any_startActivity ctx (ie, ceo) st

        // TODO: startActivities()
//        | D.Activity.StartActivities es when ctx.in_activity ->
//            for e in es do
//                do! analyze_any_startActivity ctx (e, None) e

        | _ -> ()
  }

and analyze_expr (ctx : context) parent_annotso (e : J.expr) =
  M {
    let! _ = analyze_and_eval_expr ctx parent_annotso e
    return ()
  }

and analyze_and_eval_expr (ctx : context) parent_annotso (e0 : J.expr) =
  M {
    //Globals.logger.debug Low "[e] %s" e.pretty
    let loc0 = e0.location

    let bind_and_return_intent i e =
      M {
        let addr = new address (e)
        do! bind_annotated_intent addr i (either [] parent_annotso)
        return lazy (Some (CObj (J.Ty_SQId N.Type.Intent, Some addr)))
      }

    let return_expr e =
      M {
        return! Monad.Lazy.suspend (Const.eval_expr ctx e)
      }

    match e0 with
        | D.Intent.GetExtraCall (ie, ke, defeo, tyinfix) ->
            let! (addr, i) = eval_and_lookup_intent ctx ie
            let! key = eval_intent_extra_key ctx addr ke
            let ty =
                let m = (new Text.RegularExpressions.Regex ("(\w+)((Array|ArrayList)?)")).Match tyinfix
                let g1 = m.Groups.[1].Value
                let g2 = m.Groups.[2].Value
                let basic_ty = function
                    | "Int"     -> J.Ty_Builtin J.Ty_Int
                    | "Long"    -> J.Ty_Builtin J.Ty_Long
                    | "Boolean" -> J.Ty_Builtin J.Ty_Bool
                    | "Char"    -> J.Ty_Builtin J.Ty_Char
                    | "Short"   -> J.Ty_Builtin J.Ty_Short
                    | "Float"   -> J.Ty_Builtin J.Ty_Float
                    | "Double"  -> J.Ty_Builtin J.Ty_Double
                    | "String"  -> J.Ty_String
                    | "CharSequence" -> J.Ty_QId (SQId N.Type.CharSequence)
                    | s              -> Report.Warn.unknown_getExtra loc0 s; J.Ty_Object
                in                
                    match g1, g2 with
                        | s1, ""          -> basic_ty s1
                        | s1, "Array"     -> J.Ty_Array (basic_ty s1)
                        | s1, "ArrayList" -> J.Ty_App (J.Ty_SQId N.Type.ArrayList, [J.TyArg_Ty (basic_ty s1)])
                        | s1, s2          -> Report.Warn.unknown_getExtra loc0 (s1 + s2); J.Ty_Object
            match i.add_get_extra loc0 key ty with
                | Some { content = Some (Intent.Sensitive (iaddr, _)) } -> return lazy Some (CObj (ty, Some iaddr))
                | Some { content = Some (Intent.NonSensitive co) }      -> return lazy co
                | _                                                     -> return lazy None

        | D.Intent.New ctx.envs args as e ->
            let! i = create_intent_by_constructor_args loc0 ctx args
            return! bind_and_return_intent i e

        | D.Activity.GetIntent as e ->
            let i = new intent (Intent.Undefined)
            do! effect_activity ctx.this_fqid (fun a -> (if ctx.in_onActivityResult then a.add_in_results else a.add_in_requests) i)
            return! bind_and_return_intent i e

        | D.PendingIntent.GetActivity (e, ie) ->
            let! tyo = ctx.W.try_deduce_expr ctx.this_ty e
            match tyo with
                | Some (D.PendingIntent.Ty ctx.envs) ->
                    let! (iaddr, i) = eval_and_lookup_intent ctx ie
                    match i.recipient with
                        | Intent.Undefined -> Report.Warn.undefined_intent_recipient loc0 iaddr.pretty
                        | _ -> ()
                    let pi = i.clone
                    let piaddr = new address (e0)
                    do! Env.M.bind in_intents piaddr pi
                    e0.tag <- Some (Tag.PendingIntentFactory piaddr :> obj)
                    return lazy (Some (CObj (J.Ty_SQId N.Type.PendingIntent, Some piaddr)))

                | _ -> return lazy None

        // NOTE: this must be after special method call detection
        // detect Android API calls
        | D.E (J.MemberSel (J.Call (e, id, tyargs, args))) ->
            try
                let! argtys = Monad.List.map (fun e -> M { let! tyo = ctx.W.try_deduce_expr ctx.this_ty e in return tyo.Value }) args
                let! etyo = ctx.W.try_deduce_expr ctx.this_ty e
                let _, efqid = TJ.resolve_ty ctx.envs etyo.Value
                let! o = Env.M.search in_api_calls (efqid, id, argtys)
                Option.iter (fun prms -> e0.tag <- Some (Tag.ApiCall (efqid, id, argtys, prms) :> obj)) o
            with _ -> ()                
            return! return_expr e0

        | _ -> return! return_expr e0
  }

and analyze_special_block init_ctx (b : J.block) =
  M {
    //Globals.logger.debug Low "[block] {.."
    do! Env.M.fork in_var_decls (M {
        let! ctx = init_ctx
        for st in b do
            do! trap (analyze_statement ctx) st
        })
    //Globals.logger.debug Low "[block] ..}"
  }

and analyze_block ctx = analyze_special_block (M { return ctx })

let analyze_method (ctx : context) (meth : J.methodd) =
  M {
    Globals.logger.debug Low "[meth] %s %s(%s)" (something (sprintf "%O") "void" meth.rty) meth.name (mappen_strings (fun (p : J.param) -> sprintf "%O %s" p.ty p.name) ", " meth.paramss)
    do! analyze_special_block (M {
        for p in meth.paramss do
            do! analyze_decl p.location ctx p.modif (p.ty, p.name, p.annots) None
        return ctx
        }) meth.body
  }

let analyze_class (ctx : context) (cl : J.classs) =
  M {
    Globals.logger.debug Low "[class] %s" cl.name

//    let analyze_attribute (att : J.attribute) =
//      M {
//        do! analyze_decl att.location ctx att.modif (att.ty, att.name, att.annots) att.expr
//      }
//
//    // bind all attributes of this to env
//    for att in cl.attributes do
//        do! analyze_attribute att
//
//    // bind public and protected super attributes to env
//    for ty in cl.super_tys do
//        let _, fqid = TJ.resolve_ty ctx.envs ty
//        let! clo = Env.M.search in_classes fqid
//        match clo with
//            | None    -> ()
//            | Some cl ->
//                for att in cl.attributes do
//                    match att.modif.visibility with
//                        | J.Public | J.Protected | J.Package -> do! analyze_attribute att
//                        | J.Private -> ()

    for meth in cl.methods do
        do! trap (analyze_method ctx) meth
  }

let analyze_compilation_unit (cu : J.compilation_unit) =
  M {
    Globals.logger.debug Low "[cu] %s" cu.public_class_fqid.pretty
    let W = mkW cu.package cu.imports
    for cl in cu.classes do
        let! class_env = Env.M.get in_classes
        let this_fqid = cu.package.append cl.name
        let envs = new TJ.environments (class_env, cu.package, cu.imports, this_fqid)
        let ctx =
          {
            this_ty = TJ.qualify_ty envs (J.Ty_Id cl.name)
            W = W this_fqid
            envs = envs
            current_method = None
          }
        do! trap (analyze_class ctx) cl
  }

// TODO: lazy class loader
//let load_class_signature fqid =
//  M {
//    let lcl = TJ.load_lazy_class_signature fqid
//    do! Env.M.bind in_classes fqid lcl
//  }

let populate_env (prg : J.program) =
  M {
    let rec bind_class_signatures (prefix : fqid) (cls : seq<J.class_signature>) =
      M {
        for cl in cls do            
            let prefix' = prefix.append cl.name
            do! Env.M.bind in_classes prefix' cl
            do! bind_class_signatures prefix' cl.inner_class_signatures
      }

//    for fqid in prg.implicit_imports do
//        do! load_class_signature fqid

    for cu in prg.compilation_units do
        do! bind_class_signatures cu.package (seq { for cl in cu.classes do yield cl :> J.class_signature })    
        do! bind_class_signatures cu.package (seq { for cl in cu.interfaces do yield cl :> J.class_signature })

    // populate component env with top-level component classes
    for cu in prg.compilation_units do
//        for fqid in cu.imports do
//            do! load_class_signature fqid

        for cl in cu.classes do            
            let! class_env = Env.M.get in_classes
            let fqid = cu.package.append cl.name // TJ.resolve_qid envs cl.qid
            let envs = new TJ.environments (class_env, cu.package, prg.implicit_imports @ cu.imports, fqid)
            let perms fqid = try new perms (new perm (Map.find fqid prg.manifest.calling_permissions)) with _ -> perms.bottom
            match cl with
                | D.Activity.Class envs _ -> do! Env.M.bind in_components fqid (new activity (calling_perms = perms fqid) :> componentt)
                | D.Service.Class envs  _ -> do! Env.M.bind in_components fqid (new service (calling_perms = perms fqid) :> componentt)
                | _                       -> return ()
  }

let analyze_program (prg : J.program) =
  M {
    let unexpected = Prelude.unexpected "exception caught during primary environment creation: %s"
    try do! populate_env prg
    with e -> Prelude.unexpected "exception caught during environment initialization: %s" e.Message
    
    do! print_envs

    for cu in prg.compilation_units do
        do! analyze_compilation_unit cu

    do! print_envs
  }