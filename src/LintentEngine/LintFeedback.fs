(*
 * TypeDroid - LintentEngine
 * Main.fs: type checker
 * (C) 2012 Alvise Spano', Alessandro Frazza @ Universita' Ca' Foscari di Venezia
 *)

module LintentEngine.LintFeedback

open FSharpCommon
open FSharpCommon.Prelude
open System
open System.IO
open System.Net.Sockets
open Absyn

module Issue =

    type t =
        | NotImplemented
        | Unexpected
        | Annotation
        | PartialEvaluation
        | Intent
        | Unknown
        | Perms
        | InformationFlow
    with
        override self.ToString () = self.pretty

        member self.pretty =
            match self with
                | NotImplemented -> "NotImplemented"
                | PartialEvaluation -> "PartialEvaluation"
                | Unexpected -> "Unexpected"
                | Annotation -> "Annotation"
                | Intent -> "Intent"
                | Unknown -> "Unknown"
                | Perms -> "Perms"
                | InformationFlow -> "InformationFlow"


type issue_reporter () =

    let hint_tag = Config.Comm.hint_tag
    let issue_tag = Config.Comm.issue_tag
    let sep = Config.Comm.separator
    let fatal_tag = Config.Comm.fatal
 

    let rec sprintf_with_sep = 
        function | [] -> "" | head :: [] -> head | head :: tail -> sprintf "%s%s%s" head sep (sprintf_with_sep tail)
               
    let mutable sw : StreamWriter = null
    let mutable socket : Socket = null
   
    // TODO: trovare modo migliore per loggare da qualche parte che si è provato a scrivere su stream chiuso.
    member private self.print (msg : string) =
        if self.can_write then sw.WriteLine msg; sw.Flush ()
        else printf "!!SOCKET ERROR!! Tried to write %s but couldn't" msg

    member self.report_and_throw issue loc exnf fmt =
        if self.can_write then Printf.kprintf (fun msg -> self.report_issue issue loc msg; raise (exnf msg)) fmt 
        else Printf.kprintf (fun msg -> raise (exnf msg)) fmt
    
    member self.can_write = match sw with | null -> false | _ -> sw.BaseStream.CanWrite
    member self.debug_print msg = self.print <| sprintf "[DEBUG]%s%s" sep msg
    member self.get_stream = sw.BaseStream
    member self.start (socket: Socket) = let ns = new NetworkStream (socket) in sw <- new StreamWriter (ns); sw.AutoFlush <-true
    member self.report_hint (loc : location) msg = self.print (sprintf_with_sep [hint_tag; loc.pretty; msg]) 
    member self.report_issue (issue : Issue.t) (loc : location) msg = self.print (sprintf_with_sep [issue_tag; loc.pretty; issue.ToString (); msg])

    /// Tries to write the error message to the stream and then raises a NotImplementedException. If the stream is closed it will only
    /// raise the exception.
    member self.report_not_implemented loc fmt = self.report_and_throw Issue.NotImplemented loc (fun s -> new NotImplementedException (s)) fmt
    
    /// Tries to write the error message to the stream and then raises an Unexpected exception. If the stream is closed it will only
    /// raise the exception.
    member self.report_unexpected loc fmt = self.report_and_throw Issue.Unexpected loc Unexpected fmt

    member self.report_fatal issue msg = self.print (sprintf_with_sep [fatal_tag; issue.ToString (); msg])

    // TODO: Trovare un modo migliore per aspettare che Java finisca di leggere lo stream prima di chiudere
    member self.stop () =
        socket.Shutdown (SocketShutdown.Both)
        socket.Close ()