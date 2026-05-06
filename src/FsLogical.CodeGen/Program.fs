/// Entry point for the fslogical-codegen command-line tool.
///
/// Usage:
///   fslogical-codegen [options] [<input.pl>]
///
/// Options:
///   <input.pl>           Path to the Prolog source file to convert.
///                        Omit (or pass -) to read from standard input.
///   --module, -m <name>  F# module name for the generated file
///                        (default: GeneratedDb).
///   --output, -o <file>  Write the generated F# code to <file> instead of
///                        standard output.
///   --help, -h           Print this help message.
///
/// Example:
///   fslogical-codegen facts.pl --module MyApp.Kb --output Kb.fs
module FsLogical.CodeGen.Program

open System
open System.IO
open FsLogical.PrologImport
open FsLogical.CodeGen

// ── Help ──────────────────────────────────────────────────────────────────────

let private helpText = """
fslogical-codegen – generate F# DSL code from a Prolog source file

Usage:
  fslogical-codegen [options] [<input.pl>]

Options:
  <input.pl>           Path to the Prolog source file (.pl) to convert.
                       Omit this argument (or pass -) to read from stdin.
  --module, -m <name>  F# module name for the generated file.
                       Default: GeneratedDb
  --output, -o <file>  Write the generated F# source to <file>.
                       Default: write to stdout.
  --help,   -h         Show this help and exit.

Examples:
  fslogical-codegen knowledge.pl
  fslogical-codegen knowledge.pl --module MyApp.Kb --output Kb.fs
  cat knowledge.pl | fslogical-codegen - --module MyApp.Kb
"""

// ── Argument parsing ──────────────────────────────────────────────────────────

type private CliArgs = {
    InputPath  : string   // "" or "-" means stdin
    ModuleName : string
    OutputPath : string   // "" means stdout
    ShowHelp   : bool
}

let private defaultArgs = {
    InputPath  = ""
    ModuleName = "GeneratedDb"
    OutputPath = ""
    ShowHelp   = false
}

let private parseArgs (argv: string array) : Result<CliArgs, string> =
    let mutable a     = defaultArgs
    let mutable i     = 0
    let mutable error = ""

    while i < argv.Length && error = "" do
        match argv.[i] with
        | "--help" | "-h" ->
            a <- { a with ShowHelp = true }
            i <- i + 1

        | "--module" | "-m" ->
            if i + 1 < argv.Length then
                a <- { a with ModuleName = argv.[i + 1] }
                i <- i + 2
            else
                error <- "--module requires an argument"

        | "--output" | "-o" ->
            if i + 1 < argv.Length then
                a <- { a with OutputPath = argv.[i + 1] }
                i <- i + 2
            else
                error <- "--output requires an argument"

        | arg when arg.StartsWith("-") && arg <> "-" ->
            error <- $"Unknown option: {arg}"

        | arg ->
            if a.InputPath = "" then
                a <- { a with InputPath = arg }
            else
                error <- $"Unexpected argument: {arg}"
            i <- i + 1

    if error <> "" then Error error else Ok a

// ── I/O helpers ───────────────────────────────────────────────────────────────

let private readSource (inputPath: string) : Result<string, string> =
    if inputPath = "" || inputPath = "-" then
        try
            use reader = new StreamReader(Console.OpenStandardInput())
            Ok (reader.ReadToEnd())
        with ex ->
            Error $"Failed to read from stdin: {ex.Message}"
    else
        try Ok (File.ReadAllText(inputPath))
        with ex -> Error $"Failed to read '{inputPath}': {ex.Message}"

let private writeOutput (outputPath: string) (content: string) : Result<unit, string> =
    if outputPath = "" then
        try
            Console.Write(content)
            Ok ()
        with ex ->
            Error $"Failed to write to stdout: {ex.Message}"
    else
        try
            File.WriteAllText(outputPath, content)
            Ok ()
        with ex ->
            Error $"Failed to write '{outputPath}': {ex.Message}"

// ── Entry point ───────────────────────────────────────────────────────────────

[<EntryPoint>]
let main argv =
    match parseArgs argv with
    | Error msg ->
        eprintfn $"Error: {msg}"
        eprintfn "Run with --help for usage information."
        1

    | Ok args when args.ShowHelp ->
        printfn "%s" helpText
        0

    | Ok args ->
        match readSource args.InputPath with
        | Error msg ->
            eprintfn $"Error: {msg}"
            1
        | Ok src ->
            let db   = parseString src
            let code = renderDatabase args.ModuleName args.InputPath db
            match writeOutput args.OutputPath code with
            | Error msg ->
                eprintfn $"Error: {msg}"
                1
            | Ok () ->
                0
