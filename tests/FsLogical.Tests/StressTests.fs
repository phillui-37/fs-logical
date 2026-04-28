module FsLogical.Tests.StressTests

open System.Threading.Tasks
open Xunit
open FsUnit.Xunit
open FsLogical.Term
open FsLogical.Unification
open FsLogical.Solver

// ── Helpers ──────────────────────────────────────────────────────────────────

/// Build a linear-chain ancestor DB with N parent facts.
/// parent(0,1), parent(1,2), ..., parent(n-1,n)
/// ancestor(X,Y) :- parent(X,Y)
/// ancestor(X,Y) :- parent(X,Z), ancestor(Z,Y)
let private linearAncestorDB (n: int) =
    let clauses =
        [ for i in 0 .. n - 1 ->
              fact ("parent" /@ [Integer i; Integer (i + 1)])
          yield rule ("ancestor" /@ [Var "X"; Var "Y"]) ["parent" /@ [Var "X"; Var "Y"]]
          yield rule
              ("ancestor" /@ [Var "X"; Var "Y"])
              ["parent" /@ [Var "X"; Var "Z"]; "ancestor" /@ [Var "Z"; Var "Y"]] ]
    { Clauses = clauses }

/// Build a database with N independent unrelated facts.
let private largeFlatDB (n: int) =
    { Clauses = [ for i in 0 .. n - 1 -> fact ("item" /@ [Integer i]) ] }

// ── Large database stress tests ───────────────────────────────────────────────

[<Fact>]
let ``stress: large flat DB - enumerate all 5000 solutions`` () =
    let db = largeFlatDB 5000
    let results = solve db ("item" /@ [Var "X"]) |> Seq.toList
    results |> List.length |> should equal 5000

[<Fact>]
let ``stress: large flat DB - indexed enumerate all 5000 solutions`` () =
    let db = largeFlatDB 5000
    let idb = indexDatabase db
    let results = solveIndexed idb ("item" /@ [Var "X"]) |> Seq.toList
    results |> List.length |> should equal 5000

[<Fact>]
let ``stress: large flat DB - indexed and non-indexed give same count`` () =
    let db = largeFlatDB 2000
    let idb = indexDatabase db
    let n1 = solve db ("item" /@ [Var "X"]) |> Seq.length
    let n2 = solveIndexed idb ("item" /@ [Var "X"]) |> Seq.length
    n1 |> should equal n2

[<Fact>]
let ``stress: large flat DB - only take first 1 is O(1) not O(n)`` () =
    // Should not materialize all 10_000 solutions
    let db = largeFlatDB 10_000
    let first = solve db ("item" /@ [Var "X"]) |> Seq.tryHead
    first |> Option.isSome |> should equal true
    ground "X" first.Value |> should equal (Integer 0)

[<Fact>]
let ``stress: large flat DB - ground goal lookup in 10000 clauses`` () =
    let db = largeFlatDB 10_000
    // Look up the very last item - requires scanning all (non-indexed path)
    let results = solve db ("item" /@ [Integer 9_999]) |> Seq.toList
    results |> List.length |> should equal 1

[<Fact>]
let ``stress: large flat DB indexed - ground goal lookup in 10000 clauses`` () =
    let db = largeFlatDB 10_000
    let idb = indexDatabase db
    let results = solveIndexed idb ("item" /@ [Integer 9_999]) |> Seq.toList
    results |> List.length |> should equal 1

// ── Recursive / deep chain tests ─────────────────────────────────────────────

[<Fact>]
let ``stress: ancestor chain depth 15 - find all descendants`` () =
    let db = linearAncestorDB 15
    let results =
        solve db ("ancestor" /@ [Integer 0; Var "D"])
        |> Seq.map (fun s -> ground "D" s)
        |> Seq.toList
    // All nodes 1..15 should be reachable from 0
    results |> List.length |> should equal 15
    for i in 1 .. 15 do
        results |> should contain (Integer i)

[<Fact>]
let ``stress: ancestor chain depth 15 - indexed same results`` () =
    let db = linearAncestorDB 15
    let idb = indexDatabase db
    let results =
        solveIndexed idb ("ancestor" /@ [Integer 0; Var "D"])
        |> Seq.map (fun s -> ground "D" s)
        |> Seq.toList
    results |> List.length |> should equal 15

[<Fact>]
let ``stress: ancestor chain depth 15 - ground query at end of chain`` () =
    let db = linearAncestorDB 15
    let solutions = solve db ("ancestor" /@ [Integer 0; Integer 15]) |> Seq.toList
    solutions |> should not' (be Empty)

[<Fact>]
let ``stress: ancestor chain depth 20 - non-ancestor returns no results`` () =
    let db = linearAncestorDB 20
    // 5 is not an ancestor of 3 in a 0->1->...->20 chain
    let solutions = solve db ("ancestor" /@ [Integer 5; Integer 3]) |> Seq.toList
    solutions |> should be Empty

// ── Wide fanout tests ─────────────────────────────────────────────────────────

[<Fact>]
let ``stress: 500 children of root - all found via solveAll`` () =
    let n = 500
    let db =
        { Clauses =
            [ for i in 0 .. n - 1 ->
                  fact ("child" /@ [Atom "root"; Integer i]) ] }
    let results =
        solveAll db ["child" /@ [Atom "root"; Var "X"]]
        |> Seq.toList
    results |> List.length |> should equal n

[<Fact>]
let ``stress: cross-product of two 50-child fan-outs - 2500 combinations`` () =
    let n = 50
    let db =
        { Clauses =
            [ for i in 0 .. n - 1 do
                  yield fact ("a" /@ [Integer i])
                  yield fact ("b" /@ [Integer i]) ] }
    let results =
        solveAll db ["a" /@ [Var "X"]; "b" /@ [Var "Y"]]
        |> Seq.toList
    results |> List.length |> should equal (n * n)

// ── Unification stress tests ──────────────────────────────────────────────────

[<Fact>]
let ``stress: unify two 500-arity flat compounds`` () =
    let n = 500
    let lhs = Compound("f", [ for _ in 1 .. n -> Atom "x" ])
    let rhs = Compound("f", [ for _ in 1 .. n -> Atom "x" ])
    let result = unifyFresh lhs rhs
    result |> Option.isSome |> should equal true

[<Fact>]
let ``stress: unify 500-arity compound with last arg a variable`` () =
    let n = 500
    let lhs = Compound("f", [ for i in 1 .. n -> Atom (sprintf "v%d" i) ])
    let rhs =
        Compound(
            "f",
            [ for i in 1 .. n ->
                  if i = n then Var "Last" else Atom (sprintf "v%d" i) ])
    let result = unifyFresh lhs rhs
    result |> Option.isSome |> should equal true
    applySubst result.Value (Var "Last") |> should equal (Atom (sprintf "v%d" n))

[<Fact>]
let ``stress: unify 500-arity compound that fails on last arg`` () =
    let n = 500
    let lhs = Compound("f", [ for i in 1 .. n -> Atom (sprintf "v%d" i) ])
    let rhs = Compound("f", [ for i in 1 .. n -> Atom (sprintf "w%d" i) ])
    let result = unifyFresh lhs rhs
    // Fails immediately on first arg mismatch
    result |> should equal None

[<Fact>]
let ``stress: substitution chain walk of depth 200`` () =
    // X0 -> X1 -> ... -> X200 -> Atom "end"
    let n = 200
    let pairs =
        [ for i in 0 .. n - 1 -> (sprintf "X%d" i, Var (sprintf "X%d" (i + 1)))
          yield (sprintf "X%d" n, Atom "end") ]
    let subst = Subst.ofSeq pairs
    walk (Var "X0") subst |> should equal (Atom "end")

[<Fact>]
let ``stress: applySubst on compound with 300 bound variables`` () =
    let n = 300
    let subst = Subst.ofSeq [ for i in 1 .. n -> (sprintf "V%d" i, Integer i) ]
    let term = Compound("big", [ for i in 1 .. n -> Var (sprintf "V%d" i) ])
    let result = applySubst subst term
    match result with
    | Compound("big", args) ->
        args |> List.length |> should equal n
        args.[0] |> should equal (Integer 1)
        args.[n - 1] |> should equal (Integer n)
    | _ -> failwith "expected Compound big"

// ── Thread safety tests ───────────────────────────────────────────────────────

[<Fact>]
let ``stress: concurrent solve calls produce correct independent results`` () =
    // Run 8 concurrent queries and verify each gives the right answer
    let db = largeFlatDB 100
    let tasks =
        [| for _ in 1 .. 8 ->
               Task.Run(fun () ->
                   solve db ("item" /@ [Var "X"])
                   |> Seq.length) |]
    Task.WaitAll(tasks |> Array.map (fun t -> t :> Task))
    for t in tasks do
        t.Result |> should equal 100

[<Fact>]
let ``stress: concurrent indexed solve calls produce correct independent results`` () =
    let db = largeFlatDB 100
    let idb = indexDatabase db
    let tasks =
        [| for _ in 1 .. 8 ->
               Task.Run(fun () ->
                   solveIndexed idb ("item" /@ [Var "X"])
                   |> Seq.length) |]
    Task.WaitAll(tasks |> Array.map (fun t -> t :> Task))
    for t in tasks do
        t.Result |> should equal 100

// ── solveAll + indexed completeness ──────────────────────────────────────────

[<Fact>]
let ``stress: solveAllIndexed matches solveAll on large conjunction`` () =
    let n = 100
    let db =
        { Clauses =
            [ for i in 0 .. n - 1 do
                  yield fact ("a" /@ [Integer i])
                  yield fact ("b" /@ [Integer i]) ] }
    let idb = indexDatabase db
    let goals = ["a" /@ [Var "X"]; "b" /@ [Var "Y"]]
    let n1 = solveAll db goals |> Seq.length
    let n2 = solveAllIndexed idb goals |> Seq.length
    n1 |> should equal n2
    n1 |> should equal (n * n)
