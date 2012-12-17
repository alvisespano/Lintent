(*
 * TypeDroid - LintentEngine
 * Main.fs: type checker
 * (C) 2012 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module LintentEngine.Main

open FSharpCommon.Prelude
open FSharpCommon.Log
open LintentEngine.Absyn
open System
open System.Diagnostics
open System.Net.Sockets
open FSharpCommon
open Globals

let parse_calls () =
    logger.msg Low "parsing external API Calls: %s..." Config.X.api_calls_filename
    let api_calls = Parsing.parse_x_api_calls Config.X.api_calls_filename
    logger.msg Low "parsing external Implicit Calls: %s..." Config.X.implicit_calls_filename
    let implicit_calls = Parsing.parse_x_implicit_calls Config.X.implicit_calls_filename
    api_calls, implicit_calls

let component_typing prg =
    let api_calls, implicit_calls = parse_calls ()
    logger.msg Normal "pass 1: reconstructing types of Android activities and intents..."
    let ((), state) = Typing.Component.analyze_program prg (Typing.Android.CustomMonad.state0 api_calls implicit_calls)
    state

let perms_typing prg state =
    logger.msg Normal "pass 2: checking privilege escalation over Android permissions..."
    ignore <| Typing.Perms.permscheck_program prg state


let analyze_program (tcp_cl : TcpClient) =
    let prg = Parsing.parse_lombok_java_program (new IO.StreamReader (new NetworkStream (tcp_cl.Client)))

    match (Config.Typing.perform_component_typing, Config.Typing.perform_perms_typing) with
        | false, false  -> ()
        | true, false   -> ignore <| component_typing prg
        | false, true   -> let acs, ics = parse_calls () in ignore <| perms_typing prg (Typing.Android.CustomMonad.state0 acs ics)
        | true, true    -> let state = component_typing prg in ignore <| perms_typing prg state

    if Config.Typing.perform_dlm_typing then
        logger.msg Normal "pass 3: looking for potential illegal information flows"
        ignore <| Typing.Dlm.typecheck_program prg (Typing.Dlm.CustomMonad.state0)
           
    logger.msg Low "all passes done."



module Client =

    let locate_lint () =
        let lint_exe_path, lint_exe_filename =
            try
                List.pick (fun path ->
                    let exe_filename = sprintf """%s\%s""" path Config.Lint.exe_relative_filename
                    let fi = new IO.FileInfo (exe_filename)
                    if fi.Exists then Some (fi.DirectoryName, exe_filename) else None)
                    Config.Lint.android_sdk_paths
            with e -> raise (Failure (sprintf "cannot locate ADT Lint installation: %s" e.Message))
        logger.msg Low "ADT Lint executable located: %s" lint_exe_filename
        let args_filename = sprintf """%s\%s""" Config.Lint.jars_path Config.Lint.Lintent.args_relative_filename
        IO.File.Delete args_filename
        (lint_exe_path, lint_exe_filename, args_filename)
            
    let launch_lint folder lint_exe_filename args_filename =
        let () =
            try
                use args_sw = IO.File.CreateText args_filename
                args_sw.WriteLine Config.Lint.Lintent.client_mode_args_file_content
                logger.debug Normal "args file created: %s" args_filename
            with e -> raise (Failure (sprintf "cannot create args file '%s': %s" args_filename e.Message))
        let proc_args = sprintf "--quiet %s" folder 
        let proc_infos = new ProcessStartInfo (lint_exe_filename, proc_args)
        proc_infos.ErrorDialog <- true
        proc_infos.RedirectStandardOutput <- true
        proc_infos.RedirectStandardError <- true
        proc_infos.CreateNoWindow <- true
        proc_infos.UseShellExecute <- false
        use proc = new Process () 
        proc.StartInfo <- proc_infos
        let cmdname = sprintf "%s %s" proc_infos.FileName proc_infos.Arguments
        if proc.Start () then
            logger.msg High "process '%s' has started" cmdname
            let h log (evargs : DataReceivedEventArgs) : unit = log Normal (Printf.StringFormat<_, _> "%s") evargs.Data
            let errh = h (logger.special ConsoleColor.Magenta "LINT")
            proc.ErrorDataReceived.Add errh
            proc.BeginErrorReadLine ()
            #if DEBUG__SHOW_LINT_STDOUT
            let outh = h (logger.special ConsoleColor.Green "OUT")
            proc.OutputDataReceived.Add outh
            proc.BeginOutputReadLine ()
            #endif            
        else raise (Failure (sprintf "cannot launch '%s'" cmdname))

    let main folder lint_exe_filename args_filename =
        logger.msg Normal "entering client mode with project folder '%s'..." folder
        let tcp_listener = new TcpListener (Net.IPAddress ([| 127uy; 0uy; 0uy; 1uy |]), Config.Comm.lintent_port)
        tcp_listener.Start () 
        launch_lint folder lint_exe_filename args_filename
        let tcp_client = tcp_listener.AcceptTcpClient ()
        analyze_program tcp_client
        tcp_listener.Stop ()
        ()        

        
module Server =

    let main () =
        logger.msg Normal "entering server mode..."
        let tcp_client = new TcpClient (Config.Comm.lintent_ip_address, Config.Comm.lintent_port)
        reporter.start tcp_client.Client
        analyze_program tcp_client
        reporter.stop ()


module LF = LintFeedback

[<EntryPoint>]
let main _ =

    let code =
        try
            Args.parse ()    
            match Args.mode with
                | Args.Mode_Server ->
                    Server.main ()

                | Args.Mode_Client folder ->
                    Globals.logger.msg Normal "%s" (Args.credits ())
                    Globals.logger.debug Low "CWD: %s" System.Environment.CurrentDirectory
                    let lint_exe_path, lint_exe_filename, args_filename = Client.locate_lint ()
                    Client.main folder lint_exe_filename args_filename
                    // TODO: move this such that file gets deleted always
                    try IO.File.Delete args_filename
                    finally ()
            0
        with
          //| :? Typing.Dlm.type_error as e     -> logger.fatal_error "security type error: %s" e.Message; 1
            | :? Typing.Android.type_error as e -> 
                if reporter.can_write then reporter.report_fatal LF.Issue.Unexpected (sprintf "android type error: %s" e.Message)
                logger.fatal_error "android type error: %s" e.Message; 1
            | :? Parsing.syntax_error as e      -> 
                if reporter.can_write then reporter.report_fatal LF.Issue.Unexpected (sprintf "syntax error: %s" e.Message)
                logger.fatal_error "syntax error: %s" e.Message; 1
            | :? NotImplementedException as e   -> 
                if reporter.can_write then reporter.report_fatal LF.Issue.NotImplemented (sprintf "%s" e.Message)
                logger.error "NOT IMPLEMENTED" "%s" e.Message; 1
            | Env.UnboundSymbolError s          -> 
                if reporter.can_write then reporter.report_fatal LF.Issue.Unknown s
                logger.fatal_error "unbound symbol: %s" s; 1
            | Failure s                         -> 
                if reporter.can_write then reporter.report_fatal LF.Issue.Unexpected (sprintf "failure: %s" s)
                logger.fatal_error "failure: %s" s; 1
            | Unexpected s                      -> 
                if reporter.can_write then reporter.report_fatal LF.Issue.Unexpected (sprintf "%s" s)
                logger.unexpected_error "%s" s; 1
            | Quit n                            -> 
                if reporter.can_write then reporter.report_fatal LF.Issue.Unexpected (sprintf "exit forced with code %d" n)
                logger.msg Normal "exit forced with code %d" n; n
            | e                                 -> 
                if reporter.can_write then reporter.report_fatal LF.Issue.Unexpected (sprintf "exception: %s" e.Message)
                logger.fatal_error "exception: %s" e.Message; 1

    #if DEBUG
    ignore <| System.Console.ReadKey ()
    #endif
    code
