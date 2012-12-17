(*
 * TypeDroid - LintentEngine
 * Parsing.fs: parsing facilities
 * (C) 2012 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
#light

module LintentEngine.Parsing

open System
open FSharpCommon.Prelude
open FSharpCommon.Log
open LintentEngine.Absyn
open Globals

(* parsing exceptions hierarchy *)

type syntax_error (message, loc) =
    inherit located_error (message, loc)

    static member internal locate_from_lexbuf (lexbuf : Lexing.LexBuffer<_>) =
        new location (filename = lexbuf.EndPos.FileName,
                      line = lexbuf.StartPos.Line, col = lexbuf.StartPos.Column,
                      end_line = lexbuf.EndPos.Line, end_col = lexbuf.EndPos.Column)

    new (message, lexbuf : Lexing.LexBuffer<_>) = new syntax_error (message, syntax_error.locate_from_lexbuf lexbuf)


(* Yacc parser wrapper *)

let private yparse parser (tokenizer : Lexing.LexBuffer<_> -> 'tok) tokenTagToTokenId prodIdxToNonTerminal =
    let pretty_token = sprintf "<%A>"
    let pretty_token_tag = tokenTagToTokenId >> sprintf "%A"
    let pretty_prod = prodIdxToNonTerminal >> sprintf "%A"
    let pretty_token_tags = mappen_strings pretty_token_tag " "
    let pretty_prods = mappen_strings pretty_prod "|"
    let pretty_detailed (ctx : Parsing.ParseErrorContext<'tok>) =
        let shifts = pretty_token_tags ctx.ShiftTokens
        let reduces = pretty_token_tags ctx.ReduceTokens
        let states = mappen_strings (sprintf "%d") " " ctx.StateStack
        let prods = mappen_strings pretty_prods "; " ctx.ReducibleProductions
        sprintf "shifts: %s\nreduces: %s\nstates: %s\nreducible prods: %s" shifts reduces states prods
    let pretty_simple (ctx : Parsing.ParseErrorContext<'tok>) =
        let shifts = pretty_token_tags ctx.ShiftTokens
        sprintf "expected tokens: %s" shifts
    let tokenizer lexbuf =   
        let tok =
            try tokenizer lexbuf
            with e -> raise (syntax_error (e.Message, lexbuf))
        #if DEBUG__SHOW_LEXER_TOKENS
        logger.debug Min "%s" (pretty_token tok);
        #endif
        tok
    in
        fun (lexbuf : Lexing.LexBuffer<_>) ->
            try parser tokenizer lexbuf
            with :? syntax_error -> reraise ()
               | Failure s       -> raise (syntax_error (s, lexbuf))
               | Parser.ParseErrorContext ctx as e ->
                    let ctx = ctx :?> Parsing.ParseErrorContext<'tok>
                    let tok = match ctx.CurrentToken with Some t -> pretty_token t | None -> "?"
                    let msg = sprintf "%s\ntoken: %s\n%s" ctx.Message tok ((if Config.Parsing.detailed_error_context then pretty_detailed else pretty_simple) ctx)
                    in
                        raise (syntax_error (msg, lexbuf))

let private init_lexbuf name (lexbuf : Lexing.LexBuffer<_>) =
    lexbuf.EndPos <- { pos_bol = 0
                       pos_fname = name
                       pos_cnum = 0
                       pos_lnum = 0 }

let private parse_from_TextReader p l name tr =
    let lexbuf = Lexing.LexBuffer<_>.FromTextReader tr
    init_lexbuf name lexbuf
    yparse p l Parser.tokenTagToTokenId Parser.prodIdxToNonTerminal lexbuf

let private parse_string p l name s = 
    let lexbuf = Lexing.LexBuffer<_>.FromString s
    init_lexbuf name lexbuf
    yparse p l Parser.tokenTagToTokenId Parser.prodIdxToNonTerminal lexbuf

let private parse_x p (filename : string) =
    let str = new IO.StreamReader (filename)
    let mutable r = []
    while not str.EndOfStream do
        let line = str.ReadLine ()
        try
            let lexbuf = Lexing.LexBuffer<_>.FromString line
            let a = p lexbuf
            r <- a :: r
        with e ->
            #if DEBUG__SHOW_X_PARSE_ERRORS
            Globals.logger.warn Low "parse error %s on line: %s" e.Message line
            #else
            ()
            #endif
    r        

let parse_x_api_calls =
    let p_method_signature lexbuf = yparse Parser.x_api_call_line__method_signature Lexer.x_tokenize Parser.tokenTagToTokenId Parser.prodIdxToNonTerminal lexbuf
    let p_perm_expr lexbuf = yparse Parser.x_api_call_line__perm_expr Lexer.x_tokenize Parser.tokenTagToTokenId Parser.prodIdxToNonTerminal lexbuf
    let p lexbuf =
        let qid, m = p_method_signature lexbuf
        let pe = p_perm_expr lexbuf
        let a =
            { X.api_call.class_fqid = FQId qid
              X.api_call.method_signature = m
              X.api_call.call_perms = pe.flatten |> List.fold (fun z s -> let s = s.Trim () in if s.Length = 0 then z else s :: z) []
            }
        #if DEBUG__SHOW_PARSED_API_CALLS
        Globals.logger.debug Low "API Call parsed: %O.%O - %s" a.class_fqid a.method_signature (flatten_strings ", " a.call_perms)
        #endif
        a
    in
        parse_x p

let parse_x_implicit_calls =
    let p lexbuf =
        let a = yparse Parser.x_implicit_call_line Lexer.x_tokenize Parser.tokenTagToTokenId Parser.prodIdxToNonTerminal lexbuf
        #if DEBUG__SHOW_PARSED_IMPLICIT_CALLS
        Globals.logger.debug Low "Implicit Call parsed: %s - %s" a.action_string (flatten_strings ", " a.call_perms)
        #endif
        a
    in
        parse_x p

let parse_dlm_label = parse_string Parser.label Lexer.dlm_tokenize "dlm-annot"

let parse_intent_annotations = parse_string Parser.intent_annotations Lexer.lombok_java_tokenize "intent-annot"

let parse_lombok_java_program tr = parse_from_TextReader Parser.lombok_java_program Lexer.lombok_java_tokenize "lombok-out" tr
