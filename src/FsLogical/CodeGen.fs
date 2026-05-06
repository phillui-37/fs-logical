/// Module for generating F# DSL source code from a FsLogical Database.
///
/// The output is a self-contained .fs file that reconstructs the same
/// Database when compiled against the FsLogical library.
///
/// Example – given a parsed Prolog database the module emits:
/// <code>
///   module GeneratedDb
///
///   open FsLogical.Term
///   open FsLogical.DSL
///
///   let db : Database =
///       logicDB {
///           yield fact (atom "alive")
///           yield fact ("parent" /@ [atom "tom"; atom "bob"])
///           yield ("ancestor" /@ [Var "X"; Var "Y"]) |- ["parent" /@ [Var "X"; Var "Y"]]
///       }
/// </code>
module FsLogical.CodeGen

open System
open System.Text
open FsLogical.Term

// ── Helpers ───────────────────────────────────────────────────────────────────

/// Escape a string for use inside an F# double-quoted string literal.
let private escapeStr (s: string) =
    s.Replace("\\", "\\\\").Replace("\"", "\\\"")

/// Render a float value as a valid F# float literal (always includes a decimal
/// point so the literal is unambiguous as a float in generated code).
let private renderFloat (f: float) =
    let s = f.ToString("G17", Globalization.CultureInfo.InvariantCulture)
    if s.Contains('.') || s.Contains('E') || s.Contains('e') then s
    else s + ".0"

/// Try to extract elements from a proper Prolog list (./2 chain ending with []).
/// Returns Some elements if the list is proper, None for an improper list.
let private tryExtractList (term: Term) : Term list option =
    let rec go acc t =
        match t with
        | Atom "[]"                -> Some (List.rev acc)
        | Compound(".", [h; rest]) -> go (h :: acc) rest
        | _                        -> None
    go [] term

// ── Term rendering ────────────────────────────────────────────────────────────

/// Render a Term as an F# expression using the FsLogical DSL.
///
/// Proper Prolog lists are rendered using a `prologList` helper that must be
/// present in the generated module (see <see cref="renderDatabase"/>).
let rec renderTerm (term: Term) : string =
    match term with
    | Atom "[]"  -> "atom \"[]\""
    | Atom s     -> $"atom \"{escapeStr s}\""
    | Integer n  -> $"Integer {n}"
    | Float f    -> $"Float {renderFloat f}"
    | Var s      -> $"Var \"{s}\""
    | Compound(".", _) ->
        match tryExtractList term with
        | Some elems ->
            let elemsStr = elems |> List.map renderTerm |> String.concat "; "
            $"prologList [{elemsStr}]"
        | None ->
            // Improper list: render as ordinary compound
            renderCompound "." (match term with Compound(_, a) -> a | _ -> [])
    | Compound(name, []) ->
        // Normalised zero-arity compounds → atom
        $"atom \"{escapeStr name}\""
    | Compound(name, args) ->
        renderCompound name args

and private renderCompound (name: string) (args: Term list) : string =
    let argsStr = args |> List.map renderTerm |> String.concat "; "
    $"\"{escapeStr name}\" /@ [{argsStr}]"

// ── Clause rendering ──────────────────────────────────────────────────────────

/// Render a single clause as a `yield` expression inside a `logicDB` block.
let renderClause (clause: Clause) : string =
    let headStr = renderTerm clause.Head
    match clause.Body with
    | [] ->
        $"        yield fact ({headStr})"
    | body ->
        let bodyStr = body |> List.map renderTerm |> String.concat "; "
        $"        yield ({headStr}) |- [{bodyStr}]"

// ── Database-level helpers ────────────────────────────────────────────────────

/// Return true when any term in the database contains a proper list.
let private databaseHasLists (db: Database) : bool =
    let rec termHasList t =
        match t with
        | Compound(".", _) when tryExtractList t |> Option.isSome -> true
        | Compound(_, args) -> List.exists termHasList args
        | _ -> false
    let clauseHasList c =
        termHasList c.Head || List.exists termHasList c.Body
    List.exists clauseHasList db.Clauses

// ── Public API ────────────────────────────────────────────────────────────────

/// Render a Database as a complete F# source file (returned as a string).
///
/// Parameters:
///   moduleName – fully-qualified F# module name emitted at the top of the file
///                (e.g. "MyApp.KnowledgeBase").  Defaults to "GeneratedDb" if
///                empty.
///   inputPath  – used only for the file-header comment; pass "" to omit the
///                source-file reference.
///   db         – the Database to render.
///
/// The generated file opens <c>FsLogical.Term</c> and <c>FsLogical.DSL</c> and
/// declares a single <c>let db : Database = logicDB { … }</c> binding.
let renderDatabase (moduleName: string) (inputPath: string) (db: Database) : string =
    let name = if String.IsNullOrWhiteSpace moduleName then "GeneratedDb" else moduleName
    let sb   = StringBuilder()
    let line (s: string) = sb.AppendLine(s) |> ignore

    // Header comment
    if inputPath <> "" then
        line $"// Auto-generated by fslogical-codegen from: {inputPath}"
    else
        line "// Auto-generated by fslogical-codegen."
    line "// Do not edit manually."
    line ""

    // Module declaration
    line $"module {name}"
    line ""
    line "open FsLogical.Term"
    line "open FsLogical.DSL"

    // prologList helper — only emitted when at least one proper list is present
    if databaseHasLists db then
        line ""
        line "// Helper: build a proper Prolog list term from F# list elements."
        line "let private prologList xs ="
        line "    List.foldBack (fun e acc -> \".\" /@ [e; acc]) xs (atom \"[]\")"

    // Database value
    line ""
    line "let db : Database ="
    line "    logicDB {"
    for clause in db.Clauses do
        line (renderClause clause)
    line "    }"

    sb.ToString()
