(*
 * F# Common Library
 * Log.fs: log facilities
 * (C) 2007-2012 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module FSharpCommon.Log

open System
open System.IO
open Prelude
open Printf


(* log line priority type *)

[<CustomEquality; CustomComparison>]
type pri = Unmaskerable | High | Normal | Low | Min
with
    static member Parse = function
        "U" -> Unmaskerable
      | "H" -> High
      | "N" -> Normal
      | "L" -> Low
      | "M" -> Min
      | s   -> invalidArg "s" (sprintf "invalid string '%s'" s)

    static member op_Explicit p =
        match p with
            Unmaskerable    -> 4
          | High            -> 3
          | Normal          -> 2
          | Low             -> 1
          | Min             -> 0

    override self.Equals yobj = CustomCompare.equals_on int self yobj
    override self.GetHashCode () = CustomCompare.hash_on int self
    interface IComparable with
        member self.CompareTo yobj = CustomCompare.compare_on int self yobj

    member self.pretty =
        match self with
            Unmaskerable    -> "U"
          | High            -> "H"
          | Normal          -> "N"
          | Low             -> "L"
          | Min             -> "M"


(* dynamic configuration *)

type config (?filename : string) =
    let mutable swo : StreamWriter option = Option.map (fun (s : string) -> new StreamWriter (s)) filename

    interface IDisposable with
        member self.Dispose () =
            Option.iter (fun (sw : StreamWriter) ->
                            sw.Flush ()
                            sw.Close ()
                            swo <- None)
                swo

    member self.filename
        with get () = Option.map (fun (sw : StreamWriter) -> (sw.BaseStream :?> FileStream).Name) swo

        and set newnameo =
            (self :> IDisposable).Dispose ()
            swo <- Option.map (fun newname ->
                                if self.move_logfile_on_name_change then
                                    Option.iter (fun oldname ->
                                                    File.Copy (oldname, newname, true)
                                                    File.Delete oldname)
                                        self.filename
                                new StreamWriter (newname))
                            newnameo

    member internal self.StreamWriter
        with get () = something id StreamWriter.Null swo

    member val move_logfile_on_name_change = true with get, set

    member val debug_threshold = Min with get, set
    member val msg_threshold = Min with get, set
    member val hint_threshold = Min with get, set
    member val warn_threshold = Min with get, set

    member val has_console = (try (ignore Console.CursorLeft; true) with _ -> false) with get

    member self.all_thresholds
        with set pri =
            self.debug_threshold <- pri
            self.msg_threshold <- pri
            self.hint_threshold <- pri
            self.warn_threshold <- pri

    member val show_datetime = true with get, set
    member val show_priority = true with get, set
    member val show_urgency = true with get, set
    member val shade_urgency = true with get, set

    member val multiline_tab_width = 2 with get, set
    member val datetime_max_len = 22 with get, set
    member val priority_max_len = 4 with get, set
    member val header_max_len = 7 with get, set

    member val datetime_color = ConsoleColor.DarkMagenta with get, set
    member val priority_color = ConsoleColor.Blue with get, set
    member val urgency_color = ConsoleColor.White with get, set
    member val msg_color = ConsoleColor.Gray with get, set
    member val debug_color = ConsoleColor.Cyan with get, set
    member val hint_color = ConsoleColor.Green with get, set
    member val warn_color = ConsoleColor.Yellow with get, set
    member val error_color = ConsoleColor.Red with get, set


(* fast color printer: ugly, imperative, lambda-unfolded *)

let mutex = new Threading.Mutex ()

let private create_prompter (cfg : config) =
    let tab = new String (' ', cfg.multiline_tab_width)
    let tablen = ref 0
    let out (s : string) =
        Console.Write s
        cfg.StreamWriter.Write s
        tablen := !tablen + s.Length
    let outcol fg bg (s : string) =
        Console.ForegroundColor <- fg
        Console.BackgroundColor <- bg
        out s
    let outsq fg bg len s =
        outcol ConsoleColor.White ConsoleColor.Black "["
        outcol fg bg s
        outcol ConsoleColor.White ConsoleColor.Black "]"
        let dlen = len - (s.Length + 2)
        if dlen > 0 then Console.ResetColor (); out (new String (' ', dlen))
    let outsqfg fg len s = outsq fg ConsoleColor.Black len s
    let pad n = Console.ResetColor (); out (new String (' ', n))
    in
        fun (hdo : string option) (col : ConsoleColor) ->
            let colenumty = col.GetType ()
            let darkcol =
                try ConsoleColor.Parse (colenumty, "dark" + ConsoleColor.GetName (colenumty, col), true) :?> ConsoleColor
                with _ -> if col = ConsoleColor.Black then ConsoleColor.DarkGray else ConsoleColor.Black
            in
              fun markso lvo (s : string) ->
                let print_on_console () =
                    tablen := 0
                    // datetime              
                    if cfg.show_datetime then outsqfg cfg.datetime_color cfg.datetime_max_len (sprintf "%O" DateTime.Now)
                    // header
                    match hdo with
                        | Some hd -> outsq col darkcol cfg.header_max_len hd
                        | None    -> pad cfg.header_max_len
                    // priority
                    if cfg.show_priority then
                        match lvo with
                            | Some (lv : pri) -> outsqfg cfg.priority_color cfg.priority_max_len lv.pretty
                            | None            -> pad cfg.priority_max_len
                    // urgency
                    if cfg.show_urgency then
                        Option.iter (fun marks -> outcol cfg.urgency_color ConsoleColor.Black (new String ('!', marks) + new String (' ', 5 - marks))) markso
                    else out " "
                    // body
                    let at = Console.CursorLeft
                    let (bodyfgcol, bodybgcol) =
                        if cfg.shade_urgency then
                            match markso with
                                | None 
                                | Some 1 -> col, ConsoleColor.Black
                                | Some 0 -> darkcol, ConsoleColor.Black
                                | Some 2 -> ConsoleColor.White, darkcol
                                | Some 3 -> darkcol, ConsoleColor.Gray
                                | Some 4 -> col, ConsoleColor.Gray
                                | Some n -> unexpected "logger marks = %d" n
                        else (col, ConsoleColor.Black)
                    let outbody tabn (s : string) =
                        Console.CursorLeft <- at + tabn
                        Console.ForegroundColor <- bodyfgcol
                        Console.BackgroundColor <- bodybgcol
                        Console.Write s
                        Console.ResetColor ()
                        Console.WriteLine ()
                    let p (s : string) =
                        let s = s.Replace ("\t", tab)
                        let tabn = cfg.multiline_tab_width + (new Text.RegularExpressions.Regex ("[^ ]+")).Match(s).Index
                        let sa = split_string_on_size (Console.BufferWidth - at - 1 - cfg.multiline_tab_width) s
                        if sa.Length > 0 then
                            outbody 0 sa.[0]
                            for i = 1 to sa.Length - 1 do
                                outbody tabn sa.[i]
                    Array.iter p (s.Split [|'\n'|])

                let print_on_stream () =
                    cfg.StreamWriter.WriteLine s

                ignore <| mutex.WaitOne ()
                if cfg.has_console then print_on_console ()
                print_on_stream ()
                mutex.ReleaseMutex ()
                   

let private prompt_printf prompt marks lvo fmt = kprintf (prompt marks lvo) fmt

let private null_printf _ _ = kprintf (fun _ -> ())

let private print prompt thre lv fmt =
    (if lv >= thre then prompt_printf prompt (Some (int lv - int thre)) else null_printf 0) (Some lv) fmt


(* public API *)

type [< AbstractClass >] logger () =
    abstract msg : pri -> StringFormat<'a, unit> -> 'a
    abstract debug : pri -> StringFormat<'a, unit> -> 'a
    abstract hint : pri -> StringFormat<'a, unit> -> 'a
    abstract warn : pri -> StringFormat<'a, unit> -> 'a
    abstract special : ConsoleColor -> string -> pri -> StringFormat<'a, unit> -> 'a
    abstract error : string -> StringFormat<'a, unit> -> 'a
    abstract recoverable_error : StringFormat<'a, unit> -> 'a
    abstract fatal_error :  StringFormat<'a, unit> -> 'a
    abstract unexpected_error : StringFormat<'a, unit> -> 'a
    abstract line_feed : unit
    member inline self.prefix fmt1 f lv fmt = f lv (fmt1 +% fmt)

type console_logger (cfg : config) =
    inherit logger ()

    let p = create_prompter cfg

    interface IDisposable with
        member self.Dispose () = (cfg :> IDisposable).Dispose ()

    member private self.debug_prompt = p (Some "DEBUG") cfg.debug_color
    member private self.hint_prompt = p (Some "HINT") cfg.hint_color
    member private self.warn_prompt = p (Some "WARN") cfg.warn_color
    member private self.msg_prompt = p None cfg.msg_color
    member private self.error_prompt s = prompt_printf (p (Some s) cfg.error_color) None None

    override self.msg lv fmt = print self.msg_prompt cfg.msg_threshold lv fmt
    override self.debug lv fmt = print self.debug_prompt cfg.debug_threshold lv fmt
    override self.hint lv fmt = print self.hint_prompt cfg.hint_threshold lv fmt
    override self.warn lv fmt = print self.warn_prompt cfg.warn_threshold lv fmt
    override self.special fgcol header lv fmt = print (p (Some header) fgcol) pri.Min lv fmt
    override self.error header fmt = self.error_prompt header fmt
    override self.recoverable_error fmt = self.error "ERROR" fmt
    override self.fatal_error fmt = self.error "FATAL" fmt
    override self.unexpected_error fmt = self.error "UNEXPECTED" fmt
    override self.line_feed = Console.WriteLine ""


