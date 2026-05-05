/// Module for reading existing Prolog source files and importing their facts,
/// rules, and other clauses as an FsLogical Database ready for querying.
///
/// Supported syntax
/// ----------------
///   * Facts:     functor(arg1, arg2, ...).
///   * Rules:     head :- goal1, goal2, ....
///   * Terms:     atoms, variables, integers, floats, compound terms, lists
///   * Comments:  % line comments and /* block comments */
///   * Directives (:- ...) are silently skipped.
///   * Any clause that cannot be parsed is silently skipped (error recovery).
///
/// Limitations
/// -----------
///   * Operator-notation arithmetic in rule bodies is parsed right-to-left
///     (no precedence climbing), which may not match Prolog semantics for
///     complex expressions.  Pure knowledge-base files (facts + simple rules)
///     are handled correctly.
///   * Disjunction (;) in rule bodies causes those clauses to be skipped.
///   * 0'c character-code syntax, base literals (0x…, 0b…, 0o…) are not
///     supported.
module FsLogical.PrologImport

open System
open System.IO
open FsLogical.Term

// ─────────────────────────────────────────────────────────────────────────────
// Tokenizer
// ─────────────────────────────────────────────────────────────────────────────

[<RequireQualifiedAccess>]
type private Tok =
    | Atom    of string   // atom or operator symbol
    | Var     of string   // variable (uppercase or _…)
    | Int     of int      // integer literal
    | Float   of float    // float literal
    | LParen              // (
    | RParen              // )
    | LBracket            // [ (non-empty list start)
    | RBracket            // ]
    | Pipe                // |
    | Comma               // ,
    | Dot                 // end-of-clause terminator
    | Neck                // :-
    | EOF

/// True for characters that compose Prolog graphic/symbol atoms.
let private isSymChar (c: char) =
    "+-*/\\^<>=~?@#&!:".Contains(string c)

/// Tokenize a Prolog source string into an array of tokens.
let private tokenize (src: string) : Tok array =
    let buf = src.ToCharArray()
    let n   = buf.Length
    let mutable i = 0
    let out = System.Collections.Generic.List<Tok>()

    let isEnd () = i >= n
    let cur  () = buf.[i]
    let peek1() = if i + 1 < n then ValueSome buf.[i + 1] else ValueNone
    let adv  () = i <- i + 1

    while not (isEnd ()) do
        let c = cur ()

        if Char.IsWhiteSpace(c) then
            adv ()

        // ── Line comment  % ... ────────────────────────────────────────────
        elif c = '%' then
            while not (isEnd ()) && cur () <> '\n' do adv ()

        // ── Block comment /* ... */ ────────────────────────────────────────
        elif c = '/' && peek1 () = ValueSome '*' then
            adv (); adv ()
            while not (isEnd ()) &&
                  not (cur () = '*' && peek1 () = ValueSome '/') do adv ()
            if not (isEnd ()) then adv (); adv ()   // consume */

        // ── Single-quoted atom 'hello world' ──────────────────────────────
        elif c = '\'' then
            adv ()
            let sb = Text.StringBuilder()
            let mutable closed = false
            while not (isEnd ()) && not closed do
                if cur () = '\'' then
                    if peek1 () = ValueSome '\'' then           // '' escape
                        sb.Append('\'') |> ignore; adv (); adv ()
                    else
                        adv (); closed <- true
                elif cur () = '\\' && i + 1 < n then
                    adv ()
                    let e = match cur () with
                            | 'n' -> '\n' | 't' -> '\t' | 'r' -> '\r'
                            | '\\' -> '\\' | '\'' -> '\''
                            | x -> x
                    sb.Append(e) |> ignore; adv ()
                else
                    sb.Append(cur ()) |> ignore; adv ()
            out.Add(Tok.Atom(sb.ToString()))

        // ── Double-quoted string → atom ────────────────────────────────────
        elif c = '"' then
            adv ()
            let sb = Text.StringBuilder()
            while not (isEnd ()) && cur () <> '"' do
                sb.Append(cur ()) |> ignore; adv ()
            if not (isEnd ()) then adv ()
            out.Add(Tok.Atom(sb.ToString()))

        // ── Structural punctuation ─────────────────────────────────────────
        elif c = '(' then adv (); out.Add(Tok.LParen)
        elif c = ')' then adv (); out.Add(Tok.RParen)
        elif c = '[' then
            adv ()
            // [] is a special atom; [ followed by anything else is LBracket
            if not (isEnd ()) && cur () = ']' then
                adv (); out.Add(Tok.Atom "[]")
            else
                out.Add(Tok.LBracket)
        elif c = ']' then adv (); out.Add(Tok.RBracket)
        elif c = ',' then adv (); out.Add(Tok.Comma)
        elif c = '|' then adv (); out.Add(Tok.Pipe)

        // ── Clause-terminator dot ──────────────────────────────────────────
        elif c = '.' then
            adv ()
            // A dot terminates a clause only when followed by whitespace or EOF
            if isEnd () || Char.IsWhiteSpace(cur ()) then
                out.Add(Tok.Dot)
            else
                out.Add(Tok.Atom ".")

        // ── Digits → integer or float ──────────────────────────────────────
        elif Char.IsDigit(c) then
            let start = i
            while not (isEnd ()) && Char.IsDigit(cur ()) do adv ()
            if not (isEnd ()) && cur () = '.' &&
               i + 1 < n && Char.IsDigit(buf.[i + 1]) then
                adv ()   // consume '.'
                while not (isEnd ()) && Char.IsDigit(cur ()) do adv ()
                let s = String(buf, start, i - start)
                out.Add(Tok.Float(Double.Parse(s, Globalization.CultureInfo.InvariantCulture)))
            else
                let s = String(buf, start, i - start)
                out.Add(Tok.Int(Int32.Parse(s)))

        // ── Lowercase identifier → atom ────────────────────────────────────
        elif Char.IsLower(c) then
            let start = i
            while not (isEnd ()) &&
                  (Char.IsLetterOrDigit(cur ()) || cur () = '_') do adv ()
            out.Add(Tok.Atom(String(buf, start, i - start)))

        // ── Uppercase / _ → variable ───────────────────────────────────────
        elif Char.IsUpper(c) || c = '_' then
            let start = i
            while not (isEnd ()) &&
                  (Char.IsLetterOrDigit(cur ()) || cur () = '_') do adv ()
            out.Add(Tok.Var(String(buf, start, i - start)))

        // ── Graphic / symbol atoms (includes :-, +, -, *, =, \+, …) ───────
        elif isSymChar c then
            // :- is always emitted as Neck
            if c = ':' && peek1 () = ValueSome '-' then
                adv (); adv (); out.Add(Tok.Neck)
            else
                let start = i
                while not (isEnd ()) && isSymChar (cur ()) &&
                      not (cur () = ':' && peek1 () = ValueSome '-') do adv ()
                out.Add(Tok.Atom(String(buf, start, i - start)))

        // ── Semicolon (disjunction operator) ──────────────────────────────
        elif c = ';' then adv (); out.Add(Tok.Atom ";")

        // ── Anything else: skip ────────────────────────────────────────────
        else adv ()

    out.Add(Tok.EOF)
    out.ToArray()

// ─────────────────────────────────────────────────────────────────────────────
// Parser
// ─────────────────────────────────────────────────────────────────────────────

/// Raised when the parser encounters unexpected input.
exception private ParseError of string

/// Infix binary operators recognised in term position.
let private infixOps =
    Set.ofList [
        "is"; "="; "\\="; "=="; "\\=="; "<"; ">"; "=<"; ">="
        "=.."; "mod"; "rem"; "div"; "//"; "**"; "->"; "xor"; "rdiv"
        "+"; "-"; "*"; "/"; "^"; "\\"
    ]

/// Prefix unary operators recognised in term position.
let private prefixOps = Set.ofList ["\\+"; "not"]

type private Parser(tokens: Tok array) =
    let mutable pos = 0
    let mutable anonIdx = 0L

    member _.Current    = tokens.[pos]
    member _.Lookahead  = if pos + 1 < tokens.Length then tokens.[pos + 1] else Tok.EOF

    member _.Advance() =
        if pos < tokens.Length - 1 then pos <- pos + 1

    member this.Eat(expected: Tok) =
        if this.Current = expected then this.Advance()
        else raise (ParseError(sprintf "Expected %A but got %A" expected this.Current))

    /// Create a fresh anonymous variable name.
    member _.FreshAnon() =
        anonIdx <- anonIdx + 1L
        Var(sprintf "_G%d" anonIdx)

    /// True when `tok` can legally begin a term.
    member _.CouldStartTerm(tok: Tok) =
        match tok with
        | Tok.Atom _ | Tok.Var _ | Tok.Int _ | Tok.Float _
        | Tok.LParen | Tok.LBracket -> true
        | _ -> false

    // ── Term grammar ─────────────────────────────────────────────────────────

    /// Full term: primary optionally followed by an infix operator and
    /// a right-hand term (right-recursive — no precedence climbing).
    member this.ParseTerm() : Term =
        let lhs = this.ParsePrimary()
        match this.Current with
        | Tok.Atom op when Set.contains op infixOps ->
            this.Advance()
            let rhs = this.ParseTerm()    // right-recursive
            Compound(op, [lhs; rhs])
        | _ -> lhs

    /// Primary term: atom, variable, number, compound f(…), list, or
    /// parenthesised term; also handles unary minus and prefix operators.
    member this.ParsePrimary() : Term =
        match this.Current with

        // Prefix operators: \+ or not (when followed by something term-like)
        | Tok.Atom op when Set.contains op prefixOps &&
                           this.CouldStartTerm(this.Lookahead) ->
            this.Advance()
            let operand = this.ParsePrimary()
            Compound(op, [operand])

        // Unary minus: produce a negative literal when the next token is a number
        | Tok.Atom "-" when (match this.Lookahead with
                             | Tok.Int _ | Tok.Float _ -> true
                             | _ -> false) ->
            this.Advance()
            match this.Current with
            | Tok.Int   n -> this.Advance(); Integer(-n)
            | Tok.Float f -> this.Advance(); Float(-f)
            | _ -> failwith "impossible: lookahead mismatch in unary-minus branch"

        // Unary minus applied to a non-literal expression
        | Tok.Atom "-" ->
            this.Advance()
            Compound("-", [this.ParsePrimary()])

        // Atom or compound functor(args…)
        | Tok.Atom name ->
            this.Advance()
            if this.Current = Tok.LParen then
                this.Advance()   // consume '('
                if this.Current = Tok.RParen then
                    this.Advance()
                    normalize (Compound(name, []))
                else
                    let args = this.ParseArgList()
                    this.Eat(Tok.RParen)
                    normalize (Compound(name, args))
            else
                Atom name

        // Variable (anonymous _ gets a fresh unique name each occurrence)
        | Tok.Var name ->
            this.Advance()
            if name = "_" then this.FreshAnon() else Var name

        // Numeric literals
        | Tok.Int   n -> this.Advance(); Integer n
        | Tok.Float f -> this.Advance(); Float f

        // Parenthesised term
        | Tok.LParen ->
            this.Advance()
            let t = this.ParseTerm()
            this.Eat(Tok.RParen)
            t

        // List literal [h1, h2, … | Tail]
        | Tok.LBracket ->
            this.ParseList()

        | tok -> raise (ParseError(sprintf "Unexpected token in term position: %A" tok))

    /// Comma-separated argument list inside f(…).  Commas here are separators,
    /// not conjunction operators, so each arg is parsed as a full term.
    member this.ParseArgList() : Term list =
        let args = System.Collections.Generic.List<Term>()
        args.Add(this.ParseTerm())
        while this.Current = Tok.Comma do
            this.Advance()
            args.Add(this.ParseTerm())
        Seq.toList args

    /// List literal starting at '[' (LBracket has NOT been consumed yet).
    member this.ParseList() : Term =
        this.Advance()   // consume '['
        if this.Current = Tok.RBracket then
            this.Advance(); Atom "[]"
        else
            let elems = System.Collections.Generic.List<Term>()
            elems.Add(this.ParseTerm())
            while this.Current = Tok.Comma do
                this.Advance()
                elems.Add(this.ParseTerm())
            let tail =
                if this.Current = Tok.Pipe then
                    this.Advance()
                    this.ParseTerm()
                else
                    Atom "[]"
            this.Eat(Tok.RBracket)
            // Build ./2 cons cells right-to-left
            List.foldBack
                (fun elem acc -> Compound(".", [elem; acc]))
                (Seq.toList elems) tail

    /// Rule body: top-level conjunction separated by ','.
    member this.ParseBody() : Term list =
        let goals = System.Collections.Generic.List<Term>()
        goals.Add(this.ParseTerm())
        while this.Current = Tok.Comma do
            this.Advance()
            goals.Add(this.ParseTerm())
        Seq.toList goals

    // ── Clause-level parsing ──────────────────────────────────────────────────

    /// Advance past all tokens up to and including the next clause-terminating
    /// dot (or EOF).  Used for error recovery.
    member this.SkipToNextClause() =
        while this.Current <> Tok.Dot && this.Current <> Tok.EOF do
            this.Advance()
        if this.Current = Tok.Dot then this.Advance()

    /// Parse one clause.  Returns Some clause for a fact or rule, None for a
    /// directive (:- …) or any clause that fails to parse.
    member this.TryParseClause() : Clause option =
        match this.Current with
        | Tok.EOF -> None

        // Directive  :- …  → skip silently
        | Tok.Neck ->
            this.SkipToNextClause()
            None

        | _ ->
            try
                let head = this.ParseTerm()
                match this.Current with
                | Tok.Dot ->
                    this.Advance()
                    Some (fact head)
                | Tok.Neck ->
                    this.Advance()   // consume :-
                    let body = this.ParseBody()
                    this.Eat(Tok.Dot)
                    Some (rule head body)
                | _ ->
                    // Unexpected token after head — skip this clause
                    this.SkipToNextClause()
                    None
            with :? ParseError ->
                // Error recovery: discard the rest of this clause
                this.SkipToNextClause()
                None

    /// Parse all clauses in the token stream, returning a list of every
    /// successfully parsed clause.
    member this.ParseAll() : Clause list =
        let clauses = System.Collections.Generic.List<Clause>()
        while this.Current <> Tok.EOF do
            match this.TryParseClause() with
            | Some c -> clauses.Add(c)
            | None   -> ()
        Seq.toList clauses

// ─────────────────────────────────────────────────────────────────────────────
// Public API
// ─────────────────────────────────────────────────────────────────────────────

/// Parse Prolog source text and return a Database.
///
/// Directives (:- …) are silently ignored.
/// Clauses that cannot be parsed are silently skipped.
/// Lists are represented as nested ./2 compound terms with '[]' as the tail.
let parseString (src: string) : Database =
    let toks = tokenize src
    let p    = Parser(toks)
    { Clauses = p.ParseAll() }

/// Read a Prolog source file and return a Database.
///
/// Directives (:- …) are silently ignored.
/// Clauses that cannot be parsed are silently skipped.
/// Lists are represented as nested ./2 compound terms with '[]' as the tail.
let parseFile (path: string) : Database =
    parseString (File.ReadAllText(path))
