# fs-logical

![Coverage](https://img.shields.io/badge/coverage-87.0%25-yellowgreen)

A Prolog-like logical programming framework implemented in F# targeting .NET 10.

It implements core Prolog concepts (unification, SLD resolution, backtracking) in idiomatic F# with a DSL-friendly API.

---

## REPL / FSI

For one-stop interactive usage, load the repository root script:

```fsharp
#load "FsLogical.fsx"

open FsLogical.Term
open FsLogical.DSL
```

That script pulls in the required package dependency and loads the source files in the correct order for FSI.

---

## Features

| Concept | Implementation |
|---|---|
| Terms | `Atom`, `Integer`, `Float`, `Var`, `Compound` discriminated union |
| Unification | Robinson's algorithm with occurs check (`Unification` module) |
| Knowledge base | Facts and rules in a `Database` (`Term` module) |
| Backtracking search | Lazy `seq<Substitution>` via SLD resolution (`Solver` module) |
| Solver controls | `solveN`, `solveWithOptions`, indexed solver variants |
| F# DSL | `logicDB {}` CE, `logicQuery {}` CE, operators, active patterns (`DSL` module) |
| Prolog import | Parse `.pl` files or raw Prolog strings into a `Database` (`PrologImport` module) |

---

## Quick Start

```fsharp
open FsLogical.Term
open FsLogical.DSL

// Build a knowledge base using the logicDB computation expression
let family =
    logicDB {
        yield fact ("parent" /@ [atom "tom"; atom "bob"])
        yield fact ("parent" /@ [atom "tom"; atom "liz"])
        yield fact ("parent" /@ [atom "bob"; atom "ann"])
        yield fact ("parent" /@ [atom "bob"; atom "pat"])

        // ancestor(X,Y) :- parent(X,Y)
        yield ("ancestor" /@ [Var "X"; Var "Y"]) |- ["parent" /@ [Var "X"; Var "Y"]]
        // ancestor(X,Y) :- parent(X,Z), ancestor(Z,Y)
        yield ("ancestor" /@ [Var "X"; Var "Y"]) |-
              [ "parent"   /@ [Var "X"; Var "Z"]
                "ancestor" /@ [Var "Z"; Var "Y"] ]
    }

// Query: who are tom's children?
let children =
    query family ("parent" /@ [atom "tom"; Var "Child"])
    |> Seq.map (valueOf "Child")
    |> Seq.toList
// → [Atom "bob"; Atom "liz"]

// Recursive query: all ancestors of ann
let ancestors =
    query family ("ancestor" /@ [Var "A"; atom "ann"])
    |> Seq.map (valueOf "A")
    |> Seq.toList
// → [Atom "bob"; Atom "tom"]

// Chain queries with the logicQuery computation expression
let grandchildren =
    logicQuery {
        let! sub1 = query family ("parent" /@ [atom "tom"; Var "P"])
        let p = valueOf "P" sub1
        let! sub2 = query family ("parent" /@ [p; Var "GC"])
        return valueOf "GC" sub2
    }
    |> Seq.toList
// → [Atom "ann"; Atom "pat"]
```

---

## Project Structure

```
src/
  FsLogical/
    Term.fs          ← Core types: Term, Clause, Substitution, Database; DSL operators
    Unification.fs   ← Robinson's unification algorithm
    Solver.fs        ← SLD resolution with lazy backtracking
    DSL.fs           ← logicDB / logicQuery CEs, active patterns, helpers
    PrologImport.fs  ← Prolog source parser; produces a Database from .pl files or strings
tests/
  FsLogical.Tests/
    UnificationTests.fs
    SolverTests.fs
    DSLTests.fs
    StressTests.fs
    PrologImportTests.fs
  FsLogical.Benchmarks/
    Benchmarks.fs
    Program.fs
```

---

## Key DSL Elements

### `/@` — build a compound term
```fsharp
"parent" /@ [atom "john"; atom "mary"]   // parent(john, mary)
```

### `|-` — define a rule
```fsharp
("ancestor" /@ [Var "X"; Var "Y"]) |- ["parent" /@ [Var "X"; Var "Y"]]
```

### `logicDB { }` — build a database
```fsharp
let db = logicDB {
    yield fact (...)
    yield head |- body
}
```

### `logicQuery { }` — chain queries monadically
```fsharp
let results = logicQuery {
    let! sub = query db goal1
    let! sub2 = query db goal2
    return valueOf "X" sub
}
```

### Active patterns
```fsharp
match subst with
| BoundVar "X" t   -> printfn "X = %A" t
| UnboundVar "X"   -> printfn "X is free"

match term with
| Pred "parent" [a; b] -> printfn "%A is parent of %A" a b
| _ -> ()
```

---

## Prolog Import

The `FsLogical.PrologImport` module reads existing Prolog source (`.pl` files or
raw strings) and returns a `Database` that works directly with the solver pipeline.

```fsharp
open FsLogical.PrologImport

// From a string
let db = parseString """
parent(tom, bob).
parent(tom, liz).
ancestor(X, Y) :- parent(X, Y).
ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
"""

// From a file
let db = parseFile "knowledge_base.pl"

// Use the imported database with the existing solver
solve db ("ancestor" /@ [Var "A"; Atom "bob"])
|> Seq.map (fun s -> ground "A" s)
|> Seq.toList
// → [Atom "tom"]

// Works with indexDatabase too
let idb = indexDatabase db
solveIndexed idb ("parent" /@ [Atom "tom"; Var "C"])
|> Seq.map (fun s -> ground "C" s)
|> Seq.toList
// → [Atom "bob"; Atom "liz"]
```

### Supported Prolog syntax

| Feature | Detail |
|---|---|
| Facts | `functor(arg1, arg2, …).` |
| Rules | `head :- g1, g2, g3.` |
| Atoms | Bare (`foo`) and single-quoted (`'hello world'`) |
| Variables | Uppercase (`X`, `MyVar`) and anonymous (`_`) |
| Numbers | Integers, floats, negative literals |
| Compounds | `f(a, g(b, c))` |
| Lists | `[a,b,c]`, `[H\|T]`, `[]` — translated to nested `./2` cons cells |
| Infix operators | `is`, `=`, `\=`, `<`, `>`, arithmetic (`+`, `-`, `*`, `/`, `mod`, …) |
| Prefix operators | `\+`, `not` |
| Comments | `%` line comments and `/* */` block comments |
| Directives | `:- …` silently skipped |
| Error recovery | Malformed clauses are skipped; parsing continues at the next `.` |

### Limitations

- Operator precedence is not implemented; infix expressions are parsed
  right-recursively. Pure knowledge-base files (facts and simple rules) are
  unaffected, but complex arithmetic may not associate as standard Prolog would.
- Disjunction (`;`) in rule bodies causes those clauses to be skipped.
- Character-code (`0'c`) and non-decimal base literals (`0x…`, `0b…`, `0o…`) are
  not supported.

---

## Building & Testing

Requires **.NET 10 SDK**.

```bash
dotnet build
dotnet test
```

Coverage:

```bash
dotnet test tests/FsLogical.Tests/FsLogical.Tests.fsproj --collect:"XPlat Code Coverage"
```

---

## Native AOT Compatibility

The library is fully compatible with [.NET Native AOT](https://learn.microsoft.com/en-us/dotnet/core/deploying/native-aot/) compilation.  The library project sets `<IsAotCompatible>true</IsAotCompatible>` so AOT analysis warnings are surfaced at build time.

### What was fixed for AOT

All `sprintf` format-string calls in the library were replaced with F# [string interpolation](https://learn.microsoft.com/en-us/dotnet/fsharp/language-reference/interpolated-strings) (`$"…"`).  The old `sprintf` implementation uses `MethodInfo.MakeGenericMethod()` internally which is not allowed by the Native AOT compiler.

### AOT test project

`tests/FsLogical.AotTests/` is a Native AOT console application that exercises every public surface of the library (50 assertion-style tests covering Term, Subst, Unification, Solver, IndexedDatabase, DSL, and PrologImport).  Publish and run it with:

```bash
dotnet publish tests/FsLogical.AotTests/FsLogical.AotTests.fsproj -c Release
./tests/FsLogical.AotTests/bin/Release/net10.0/linux-x64/publish/FsLogical.AotTests
```

---

## Benchmark Snapshot

Short-run BenchmarkDotNet sample on GitHub-hosted Linux (`AMD EPYC 9V74`, `.NET 10.0.5`):

### JIT vs. Native AOT comparison

| Scenario | JIT (ShortRun) | NativeAOT | AOT / JIT |
|---|---:|---:|---:|
| `ancestor` all descendants, depth 5 (non-indexed) | 68.67 µs | 67.35 µs | 0.98× |
| `ancestor` all descendants, depth 10 (non-indexed) | 187.67 µs | 179.16 µs | 0.95× |
| `ancestor` all descendants, depth 20 (non-indexed) | 555.32 µs | 534.21 µs | 0.96× |
| `solve` fan-out enumeration, 50 facts (non-indexed) | 37.24 µs | 34.89 µs | 0.94× |
| `solve` fan-out enumeration, 200 facts (non-indexed) | 139.78 µs | 138.94 µs | 0.99× |
| `solve` fan-out enumeration, 1,000 facts (non-indexed) | 730.19 µs | 748.41 µs | 1.02× |

AOT and JIT performance are essentially equivalent for this library.  The logic-programming workloads are dominated by allocations and GC rather than JIT overhead, so the AOT speedup is modest (typically < 5 %).

Reproduce the JIT-only snapshot:

```bash
dotnet run --project tests/FsLogical.Benchmarks/FsLogical.Benchmarks.fsproj -c Release -- -j short -m --join -f '*.SolverBenchmarks.SolveFanOutAll' '*.SolverBenchmarks.SolveFanOutAllIndexed' '*.AncestorBenchmarks.FindAllDescendants' '*.AncestorBenchmarks.FindAllDescendantsIndexed'
```

Reproduce the JIT + AOT side-by-side table (adds `--aot` flag; downloads the ILCompiler package on first run):

```bash
dotnet run --project tests/FsLogical.Benchmarks/FsLogical.Benchmarks.fsproj -c Release -- --aot -j short --join -f '*.AncestorBenchmarks.FindAllDescendants' '*.SolverBenchmarks.SolveFanOutAll'
```

