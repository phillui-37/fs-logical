module FsLogical.Benchmarks.Benchmarks

open BenchmarkDotNet.Attributes
open FsLogical.Term
open FsLogical.Unification
open FsLogical.Solver

// ── Shared test data ──────────────────────────────────────────────────────────

/// Ancestor-style database: N parent facts arranged in a linear chain.
/// parent(0,1), parent(1,2), ..., parent(n-1,n)
/// ancestor(X,Y) :- parent(X,Y)
/// ancestor(X,Y) :- parent(X,Z), ancestor(Z,Y)
let private buildLinearAncestorDB (n: int) : Database =
    let clauses =
        [ for i in 0 .. n - 1 ->
              fact ("parent" /@ [Integer i; Integer (i + 1)])
          yield rule ("ancestor" /@ [Var "X"; Var "Y"]) ["parent" /@ [Var "X"; Var "Y"]]
          yield rule
              ("ancestor" /@ [Var "X"; Var "Y"])
              ["parent" /@ [Var "X"; Var "Z"]; "ancestor" /@ [Var "Z"; Var "Y"]] ]
    { Clauses = clauses }

/// Wide fan-out database: N children of a single root.
let private buildFanOutDB (n: int) : Database =
    let clauses =
        [ for i in 0 .. n - 1 ->
              fact ("child" /@ [Atom "root"; Integer i]) ]
    { Clauses = clauses }

// ── Unification benchmarks ────────────────────────────────────────────────────

[<MemoryDiagnoser>]
type UnificationBenchmarks() =

    /// Two large flat compounds: f(a,a,...,a) vs f(a,a,...,X)
    [<Params(10, 100, 500)>]
    member val Arity = 10 with get, set

    member this.FlatCompound() =
        let args = [ for _ in 1 .. this.Arity -> Atom "a" ]
        Compound("f", args)

    member this.FlatCompoundWithVar() =
        let args =
            [ for i in 1 .. this.Arity ->
                  if i = this.Arity then Var "X" else Atom "a" ]
        Compound("f", args)

    [<Benchmark(Description = "unify flat compounds - all ground match")>]
    member this.UnifyFlatGroundMatch() =
        let t = this.FlatCompound()
        unifyFresh t t |> ignore

    [<Benchmark(Description = "unify flat compounds - last arg is variable")>]
    member this.UnifyFlatWithVar() =
        unifyFresh (this.FlatCompound()) (this.FlatCompoundWithVar()) |> ignore

    [<Benchmark(Description = "unify fails (different atom in last arg)")>]
    member this.UnifyFlatFails() =
        let args1 = [ for _ in 1 .. this.Arity -> Atom "a" ]
        let args2 =
            [ for i in 1 .. this.Arity ->
                  if i = this.Arity then Atom "b" else Atom "a" ]
        unifyFresh (Compound("f", args1)) (Compound("f", args2)) |> ignore

    [<Benchmark(Description = "occursIn - deep nesting")>]
    member this.OccursInDeep() =
        // Build a deeply nested term: f(f(f(...f(X)...)))
        let rec buildNested n =
            if n = 0 then Var "X"
            else Compound("f", [buildNested (n - 1)])
        let deep = buildNested this.Arity
        occursIn "X" deep Subst.empty |> ignore

// ── applySubst benchmarks ────────────────────────────────────────────────────

[<MemoryDiagnoser>]
type ApplySubstBenchmarks() =

    [<Params(10, 50, 200)>]
    member val ChainLength = 10 with get, set

    member this.BuildChainSubst() =
        // X0 -> X1 -> X2 -> ... -> Xn -> Atom "end"
        let pairs =
            [ for i in 0 .. this.ChainLength - 1 ->
                  (sprintf "X%d" i, Var (sprintf "X%d" (i + 1)))
              yield (sprintf "X%d" this.ChainLength, Atom "end") ]
        Subst.ofSeq pairs

    [<Benchmark(Description = "walk through substitution chain")>]
    member this.WalkChain() =
        let subst = this.BuildChainSubst()
        walk (Var "X0") subst |> ignore

    [<Benchmark(Description = "applySubst on compound with many bound vars")>]
    member this.ApplySubstWideCompound() =
        let pairs =
            [ for i in 1 .. this.ChainLength ->
                  (sprintf "V%d" i, Integer i) ]
        let subst = Subst.ofSeq pairs
        let term =
            Compound("f", [ for i in 1 .. this.ChainLength -> Var (sprintf "V%d" i) ])
        applySubst subst term |> ignore

// ── Solver benchmarks - non-indexed ──────────────────────────────────────────

[<MemoryDiagnoser>]
type SolverBenchmarks() =

    [<Params(50, 200, 1000)>]
    member val DatabaseSize = 50 with get, set

    member this.FanOutDB() = buildFanOutDB this.DatabaseSize
    member this.LinearAncestorDB() = buildLinearAncestorDB (min this.DatabaseSize 30)

    [<Benchmark(Description = "solve - enumerate all from fan-out DB (non-indexed)")>]
    member this.SolveFanOutAll() =
        let db = this.FanOutDB()
        solve db ("child" /@ [Atom "root"; Var "X"])
        |> Seq.length |> ignore

    [<Benchmark(Description = "solve - enumerate all from fan-out DB (indexed)")>]
    member this.SolveFanOutAllIndexed() =
        let db = this.FanOutDB()
        let idb = indexDatabase db
        solveIndexed idb ("child" /@ [Atom "root"; Var "X"])
        |> Seq.length |> ignore

    [<Benchmark(Description = "solve - first result only (non-indexed)")>]
    member this.SolveFanOutFirst() =
        let db = this.FanOutDB()
        solve db ("child" /@ [Atom "root"; Var "X"])
        |> Seq.tryHead |> ignore

    [<Benchmark(Description = "solve - first result only (indexed)")>]
    member this.SolveFanOutFirstIndexed() =
        let db = this.FanOutDB()
        let idb = indexDatabase db
        solveIndexed idb ("child" /@ [Atom "root"; Var "X"])
        |> Seq.tryHead |> ignore

    [<Benchmark(Description = "indexDatabase construction cost")>]
    member this.IndexDatabaseConstruction() =
        let db = this.FanOutDB()
        indexDatabase db |> ignore

// ── Recursive ancestor benchmarks ─────────────────────────────────────────────

[<MemoryDiagnoser>]
type AncestorBenchmarks() =

    [<Params(5, 10, 20)>]
    member val ChainDepth = 5 with get, set

    member this.AncestorDB() = buildLinearAncestorDB this.ChainDepth
    member this.IndexedAncestorDB() = indexDatabase (buildLinearAncestorDB this.ChainDepth)

    [<Benchmark(Description = "ancestor - find all descendants (non-indexed)")>]
    member this.FindAllDescendants() =
        let db = this.AncestorDB()
        solve db ("ancestor" /@ [Integer 0; Var "D"])
        |> Seq.length |> ignore

    [<Benchmark(Description = "ancestor - find all descendants (indexed)")>]
    member this.FindAllDescendantsIndexed() =
        let idb = this.IndexedAncestorDB()
        solveIndexed idb ("ancestor" /@ [Integer 0; Var "D"])
        |> Seq.length |> ignore

    [<Benchmark(Description = "ancestor - ground query true (non-indexed)")>]
    member this.AncestorGroundTrue() =
        let db = this.AncestorDB()
        solve db ("ancestor" /@ [Integer 0; Integer this.ChainDepth])
        |> Seq.tryHead |> ignore

    [<Benchmark(Description = "ancestor - ground query true (indexed)")>]
    member this.AncestorGroundTrueIndexed() =
        let idb = this.IndexedAncestorDB()
        solveIndexed idb ("ancestor" /@ [Integer 0; Integer this.ChainDepth])
        |> Seq.tryHead |> ignore

// ── Substitution micro-benchmarks ─────────────────────────────────────────────

[<MemoryDiagnoser>]
type SubstitutionBenchmarks() =

    [<Params(10, 100, 500)>]
    member val Size = 10 with get, set

    [<Benchmark(Description = "Subst.add - build substitution incrementally")>]
    member this.SubstBuildIncremental() =
        let mutable s = Subst.empty
        for i in 1 .. this.Size do
            s <- Subst.add (sprintf "V%d" i) (Integer i) s
        s |> ignore

    [<Benchmark(Description = "Subst.tryFind - lookup in substitution")>]
    member this.SubstTryFind() =
        let s =
            Subst.ofSeq [ for i in 1 .. this.Size -> (sprintf "V%d" i, Integer i) ]
        // Look up the last-inserted key (worst hash probe scenario for some implementations)
        Subst.tryFind (sprintf "V%d" this.Size) s |> ignore

    [<Benchmark(Description = "Subst.ofSeq - bulk construction")>]
    member this.SubstOfSeq() =
        Subst.ofSeq [ for i in 1 .. this.Size -> (sprintf "V%d" i, Integer i) ]
        |> ignore
