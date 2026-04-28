# fs-logical

![Coverage](https://img.shields.io/badge/coverage-87.0%25-yellowgreen)

A Prolog-like logical programming framework implemented in F# targeting .NET 10.

It implements core Prolog concepts (unification, SLD resolution, backtracking) in idiomatic F# with a DSL-friendly API.

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
tests/
  FsLogical.Tests/
    UnificationTests.fs
    SolverTests.fs
    DSLTests.fs
    StressTests.fs
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

## Benchmark Snapshot

Short-run BenchmarkDotNet sample on GitHub-hosted Linux (`AMD EPYC 7763`, `.NET 10.0.5`):

| Scenario | Mean |
|---|---:|
| `ancestor` all descendants, depth 20 (non-indexed) | 550.56 µs |
| `ancestor` all descendants, depth 20 (indexed) | 372.95 µs |
| `solve` fan-out enumeration, 1,000 facts (non-indexed) | 730.66 µs |
| `solve` fan-out enumeration, 1,000 facts (indexed) | 790.79 µs |

The indexed path helps most on recursive ancestor workloads, while flat full-enumeration workloads are already dominated by result materialisation.

Reproduce the sample:

```bash
dotnet run --project tests/FsLogical.Benchmarks/FsLogical.Benchmarks.fsproj -c Release -- -j short -m --join -f '*.SolverBenchmarks.SolveFanOutAll' '*.SolverBenchmarks.SolveFanOutAllIndexed' '*.AncestorBenchmarks.FindAllDescendants' '*.AncestorBenchmarks.FindAllDescendantsIndexed'
```
