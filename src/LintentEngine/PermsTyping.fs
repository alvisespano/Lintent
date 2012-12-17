(*
 * TypeDroid - LintentEngine
 * PermsTyping.fs: permission typing and privilege escalation
 * (C) 2012 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)

module LintentEngine.Typing.Perms

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

open CustomMonad

type [< NoComparison >] context =
  {
    this_fqid  : fqid
    uses_perms : perms
    W          : TJ.M.W<state>
  }

let report_perms_diff report (p1 : perms) (p2 : perms) =
    report p1.pretty p2.pretty (p1 - p2).pretty


let rec permscheck_program (prg : J.program) =
  M {
    let uses_perms = perms.of_strings prg.manifest.uses_permissions
    for cu in prg.compilation_units do
        do! permscheck_compilation_unit uses_perms cu

    let! cps = Env.M.get in_component_effective_perms
    let ep = cps |> Env.toSeq |> Seq.sumBy (fun (_, p) -> p)
    
    if ep.is_strictly_in uses_perms then
        report_perms_diff (Report.Priv.Warn.overprivileged_application (try prg.compilation_units.Head.classes.Head.location with _ -> uloc)) uses_perms ep
  }

and permscheck_compilation_unit uses_perms (cu : J.compilation_unit) =
  M {
    for cl in cu.classes do
        let! class_env = Env.M.get in_classes
        let fqid = cu.package.append cl.name
        let envs = new TJ.environments (class_env, cu.package, cu.imports, fqid)
        match cl with
            | D.Activity.Class envs _
            | D.Service.Class envs _  ->
                let! o = Env.M.search in_component_effective_perms fqid
                match o with
                    | Some _ -> ()
                    | None ->
                        let ctx =
                          {
                            this_fqid = fqid
                            uses_perms = uses_perms
                            W = mkW cu.package cu.imports fqid
                          }
                        do! trap (permscheck_component_class ctx) cl

            | cl ->                
                Globals.logger.msg Low "ignoring non-component class: %O" fqid
  }

and permscheck_component_class (ctx : context) (cl : J.classs) =
  M {
    Globals.logger.debug Normal "[component] %O" cl.name
    do! set_effective_perms perms.bottom
    for meth in cl.methods do
        do! trap (permscheck_method ctx) meth

    // post-analysis checkings
    //

    let! comp = Env.M.lookup in_components ctx.this_fqid
    let! ep = get_effective_perms        
    let! st = Monad.get_state
    let ep = ep - st.onCreate_perms
    if not (ep.is_in comp.calling_perms) then
        report_perms_diff (Report.Priv.Warn.effective_permissions_greater_than_calling_permissions cl.location ctx.this_fqid.pretty)
            ep comp.calling_perms

    do! Env.M.bind in_component_effective_perms ctx.this_fqid ep
  }

and permscheck_method (ctx : context) (meth : J.methodd) =
  M {
    Globals.logger.debug Normal "[meth] %O" meth.name

    match meth with
        | D.Activity.Method_onCreate _ ->
            match meth.annots with
                | D.Annot.MultipleUnaryString Config.Java.Annot.Priv.annotation Config.Java.Annot.Priv.endorse (s, _) ->
                    let sa = s.Split ([|',';';'|], StringSplitOptions.RemoveEmptyEntries)
                    let p = new perms (seq { for s in sa do yield new perm (s.Trim ()) })
                    do! Monad.lift_state (fun st -> { st with onCreate_perms = p })
                    Globals.logger.debug High "onCreate() annotation found: %O" p
                | _ -> ()
        | _ -> ()

    do! permscheck_block ctx meth.body
  }

and permscheck_special_block init_ctx (b : J.block) =
  M {
    let! ctx = init_ctx
    for st in b do
        do! trap (permscheck_statement ctx) st
  }
  
and permscheck_block ctx = permscheck_special_block (M { return ctx })

and permscheck_statement ctx (st : J.statement) =
  M {
    Globals.logger.debug Low "[st] %O" st.value
    let loc0 = st.location

    match st.value with        
        | J.Decl (_, _, eo) ->
            do! Monad.Option.iter (permscheck_expr ctx) eo           

        | J.Assign (e1, e2) ->
            do! permscheck_expr ctx e1
            do! permscheck_expr ctx e2
                       
        | J.If (e, b, bo) ->
            do! permscheck_block ctx b
            do! Monad.Option.iter (permscheck_block ctx) bo
            do! permscheck_expr ctx e

        | J.DoWhile (b, e)
        | J.While (e, b) ->
            do! permscheck_block ctx b
            do! permscheck_expr ctx e
        
        | J.For (st1o, eo, st2o, b) ->
            do! permscheck_special_block (M {
                do! Monad.Option.iter (permscheck_statement ctx) st1o
                do! Monad.Option.iter (permscheck_statement ctx) st2o
                return ctx
                }) b
            do! Monad.Option.iter (permscheck_expr ctx) eo

        | J.ForEach ((ty, id, _), e, b) ->
            do! permscheck_special_block (M {
                do! Env.M.bind in_var_decls id { var_decl.modif = new J.decl_modifiers (); ty = ty; expr = None }
                return ctx
                }) b
            do! permscheck_expr ctx e

        | J.Try (b, cbs, fbo) ->
            do! permscheck_block ctx b
            for (p, b) in cbs do
                do! permscheck_special_block (M {
                    do! Env.M.bind in_var_decls p.name { var_decl.modif = new J.decl_modifiers (final = p.modif.final); ty = p.ty; expr = None }
                    return ctx
                    }) b
            do! Monad.Option.iter (permscheck_block ctx) fbo

        | J.Switch (e, cs, defbo) ->
            for (_, b) in cs do
                do! permscheck_block ctx b
            do! Monad.Option.iter (permscheck_block ctx) defbo
            do! permscheck_expr ctx e

        | J.Return eo ->
            do! Monad.Option.iter (permscheck_expr ctx) eo

        | J.Assert (e, eo) ->
            do! permscheck_expr ctx e
            do! Monad.Option.iter (permscheck_expr ctx) eo

        | J.StatementExpr e
        | J.Throw e as st ->
            do! permscheck_expr ctx e

        | J.ThisCons (_, es)
        | J.SuperCons (_, es) ->
            for e in es do
                do! permscheck_expr ctx e

        // ignored statements
        | J.Break _
        | J.Continue _
        | J.Labeled _ -> ()


    // perform tag check
    //

    do! permscheck_node ctx st

  }               

and permscheck_expr (ctx : context) (e : J.expr) =
  M {
    match e.value with
        | J.UnOp (_, e)
        | J.Cast (_, e)
        | J.MemberSel (J.Sel (e, _)) ->
            do! permscheck_expr ctx e

        | J.MemberSel (J.Call (e, _, _, args)) -> 
            do! permscheck_expr ctx e
            for e in args do
                do! permscheck_expr ctx e


        | J.MemberSel (J.SuperCall (_, _, args)) -> 
            for e in args do
                do! permscheck_expr ctx e

        | J.BinOp (e1, _, e2)
        | J.Subscript (e1, e2) ->
            do! permscheck_expr ctx e1
            do! permscheck_expr ctx e2

        | J.Cons (_, (_, args), cbo) ->
            for e in args do
                do! permscheck_expr ctx e
            do! Monad.Option.iter (fun (cb : J.class_body) -> M { for m in cb.methods do do! permscheck_method ctx m }) cbo

        | J.Cond (e1, e2, e3) ->
            do! permscheck_expr ctx e1
            do! permscheck_expr ctx e2
            do! permscheck_expr ctx e3

        | J.MemberSel (J.SuperSel _)
        | J.This  
        | J.Lit _
        | J.Var _ -> ()

    do! permscheck_node ctx e
  }

and permscheck_node ctx (n : J.node<obj>) =
  M {
    match n.tag with
        | Some (:? Tag.t as tag) -> return! permscheck_tag ctx n.location tag
        | _                      -> return ()
  }

and permscheck_tag ctx loc0 tag =
  M {
    match tag with
        | Tag.App (is_forResult, iaddr) ->
            Globals.logger.debug Normal "[App] %O" iaddr
            let! i = Env.M.lookup in_intents iaddr
            let! effective_perms_approx, effective_perms = (M {                            
                match is_forResult, i.recipient with
                    | (true, Intent.Implicit s) ->
                        return Report.Priv.Err.implicit_intent_in_call_with_result loc0 iaddr.pretty s

                    | (false, Intent.Implicit s) ->
                        if i.perms <> perms.bottom then
                            report_perms_diff (Report.Priv.Warn.secrecy_violation loc0 i.pretty) i.perms perms.bottom
                        let! permso = Env.M.search in_implicit_calls s
                        match permso with
                            | None       -> Report.Priv.Warn.unknown_action_string loc0 s
                                            return perms.bottom, ctx.uses_perms
                            | Some perms -> return perms, perms
                                
                    | (_, Intent.Explicit fqid) ->
                        let! compo = Env.M.search in_components fqid
                        match compo with
                            | None ->
                                Report.Priv.Warn.unknown_component_name loc0 fqid.pretty
                                return perms.bottom, ctx.uses_perms

                            | Some comp ->
                                let p = comp.calling_perms
                                return p, p

                    | (_, Intent.Undefined) ->
                        return unexpected loc0 "intent has an undefined recipient"
                })
            if not (effective_perms_approx.is_in ctx.uses_perms) then
                Report.Priv.Warn.component_call_permission_denied loc0 ctx.uses_perms.pretty effective_perms_approx.pretty
            else do! add_effective_perms effective_perms
            return ()

        | Tag.ApiCall (fqid, id, argtys, prms) ->
            Globals.logger.debug Normal "[ApiCall] %O.%s(%s) %O" fqid id (mappen_strings (sprintf "%O") ", " argtys) prms
            if not (prms.is_in ctx.uses_perms) then
                Report.Priv.Warn.api_call_permission_denied loc0 ctx.uses_perms.pretty prms.pretty
            else do! add_effective_perms prms

        | Tag.PendingIntentFactory iaddr ->
            Globals.logger.debug Normal "[PendingIntentFactory] %O" iaddr
            let! i = Env.M.lookup in_intents iaddr
            match i.recipient with
                | Intent.Implicit _ -> i.add_perms ctx.uses_perms
                | Intent.Undefined  -> ()

                | Intent.Explicit fqid ->
                    let! compo = Env.M.search in_components fqid
                    match compo with
                        | Some comp ->
                            let! o = Env.M.search in_component_effective_perms fqid
                            match o with
                                | Some p ->
                                    i.add_perms p

                                | None ->
                                    let! cl = Env.M.lookup in_classes fqid
                                    match cl with
                                        | :? J.classs as cl ->
                                            do! permscheck_component_class ctx cl
                                            let! p = Env.M.lookup in_component_effective_perms fqid
                                            i.add_perms p

                                        | _ -> ()
                                                                           
                        | None -> Report.Priv.Warn.unknown_component_name loc0 fqid.pretty                                             

        | Tag.PendingIntentDeclassify (prms, iaddr) ->
            Globals.logger.debug Normal "[PendingIntentDeclassify] %O, %O" prms iaddr
            let! i = Env.M.lookup in_intents iaddr
            i.declassify_perms <- prms

  }