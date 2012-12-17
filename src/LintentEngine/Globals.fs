(*
 * TypeDroid - LintentEngine
 * Globals.fs: global stuff
 * (C) 2012 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
 
module LintentEngine.Globals

open System
open System.IO
open FSharpCommon
open FSharpCommon.Log

let logger = new Log.console_logger (Config.Log.cfg)
let reporter = new LintFeedback.issue_reporter ()

exception Quit of int


