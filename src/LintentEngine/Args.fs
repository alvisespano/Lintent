(*
 * TypeDroid - LintentEngine
 * Args.fs: command line argument parsing
 * (C) 2012 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module LintentEngine.Args

open FSharpCommon.Prelude
open FSharpCommon.Log
open System
open System.Runtime.InteropServices
open System.Reflection

type mode = Mode_Server | Mode_Client of string

let mutable mode = Mode_Server

let credits () =
    let now = DateTime.Now
    let asm = Assembly.GetExecutingAssembly ()
    let name = asm.GetName ()
    let ver = name.Version
    let title = get_assembly_attribute<AssemblyTitleAttribute> asm
    let description = get_assembly_attribute<AssemblyDescriptionAttribute> asm
    let product = get_assembly_attribute<AssemblyProductAttribute> asm
    let copyright = get_assembly_attribute<AssemblyCopyrightAttribute> asm
    let company = get_assembly_attribute<AssemblyCompanyAttribute> asm
    in
        sprintf "%s v%d.%d.%d build %d [%04d-%02d-%02d]\n\
                \n\
                %s\n\
                \n\
                %s and %s are %s - %s\n"
            title ver.Major ver.Minor ver.Build ver.Revision now.Year now.Month now.Day
            description
            product title copyright company

let usage () =
    sprintf "\n\nusage: %s <SOURCE FILENAME>\n\n"
        (IO.Path.GetFileName (Diagnostics.Process.GetCurrentProcess ()).MainModule.FileName)

let private other s = mode <- Mode_Client s

module private Entry =
    let private arg argty f (name : string) help defopt =
        ArgInfo ((if name.Length = 1 then sprintf "-%s" else sprintf "--%s") name,
                 argty (fun x -> f x),
                 match defopt with None -> help | Some def -> sprintf "%s (default = %A)" help def)

    let int name f help def = [|arg ArgType.Int f name help def|]
    
    let flag name f help = [|arg ArgType.Unit f name help None|]

    let string name f help def = [|arg ArgType.String f name help def|]

    let bool name f help =
        let noname = sprintf "no-%s" name
        in
            [|arg ArgType.Unit (fun () -> f true) name help None;
              arg ArgType.Unit (fun () -> f false) noname help None|]

let private infos =
  [|
    Entry.flag "pedantic" (fun () -> Config.Log.cfg.all_thresholds <- Min)  "set all log thresholds to minimum level"
    Entry.flag "v" (fun () -> Config.Log.cfg.all_thresholds <- Low) "set all log thresholds to low level"
    Entry.flag "quiet" (fun () -> Config.Log.cfg.all_thresholds <- High) "set all log thresholds to high level"
    Entry.flag "no-comp" (fun () -> Config.Typing.perform_component_typing <- false) "do not perform components typechecking"
    Entry.flag "no-perms" (fun () -> Config.Typing.perform_perms_typing <- false) "do not perform permissions typechecking"
    Entry.flag "no-dlm" (fun () -> Config.Typing.perform_dlm_typing <- false) "do not perform DLM typechecking"
    Entry.bool "show-log-priority" (fun b -> Config.Log.cfg.show_priority <- b) "show log lines priority"
    Entry.bool "show-log-urgency" (fun b -> Config.Log.cfg.show_urgency <- b) "show log lines urgency"
    Entry.bool "show-log-datetime" (fun b -> Config.Log.cfg.show_datetime <- b) "show datetime in log lines"
    Entry.string "log-file" (fun s -> Config.Log.cfg.filename <- Some s) "set log filename" Config.Log.cfg.filename
    Entry.string "debug-threshold" (fun s -> Config.Log.cfg.debug_threshold <- pri.Parse s) "set debug verbosity threshold" (Some Config.Log.cfg.debug_threshold)
    Entry.string "msg-threshold" (fun s -> Config.Log.cfg.msg_threshold <- pri.Parse s) "set informational messages verbosity threshold" (Some Config.Log.cfg.msg_threshold)
    Entry.string "hint-threshold" (fun s -> Config.Log.cfg.hint_threshold <- pri.Parse s) "set hint messages verbosity threshold" (Some Config.Log.cfg.hint_threshold)
    Entry.string "warn-threshold" (fun s -> Config.Log.cfg.warn_threshold <- pri.Parse s) "set warnings verbosity threshold" (Some Config.Log.cfg.warn_threshold)
    Entry.flag "server-mode" (fun () -> mode <- Mode_Server) "enter server mode and wait for Lint data"
    Entry.string "client-mode" (fun s -> mode <- Mode_Client s) "enter client mode and spawn Lint passing the given path as project root directory" None
  |] |> Array.concat

let parse () = ArgParser.Parse (arguments = infos, otherArgs = other, usageText = usage ())
