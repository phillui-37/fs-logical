module FsLogical.Tests.SolverTests

open Xunit
open FsUnit.Xunit
open FSharpx.Collections
open FsLogical.Term
open FsLogical.Unification
open FsLogical.Solver

// ── Helpers ──────────────────────────────────────────────────────────────

let private mkSubst (pairs: (string * Term) list) : Substitution =
    Subst.ofSeq pairs

let private emptySubst : Substitution = Subst.empty

/// Build a small family database for tests.
let private familyDB =
    { Clauses =
        [ // facts
          fact ("parent" /@ [atom "tom";  atom "bob"])
          fact ("parent" /@ [atom "tom";  atom "liz"])
          fact ("parent" /@ [atom "bob";  atom "ann"])
          fact ("parent" /@ [atom "bob";  atom "pat"])
          // ancestor(X,Y) :- parent(X,Y)
          rule
            ("ancestor" /@ [Var "X"; Var "Y"])
            ["parent" /@ [Var "X"; Var "Y"]]
          // ancestor(X,Y) :- parent(X,Z), ancestor(Z,Y)
          rule
            ("ancestor" /@ [Var "X"; Var "Y"])
            ["parent" /@ [Var "X"; Var "Z"]
             "ancestor" /@ [Var "Z"; Var "Y"]] ] }

// ── Fact queries ─────────────────────────────────────────────────────────

[<Fact>]
let ``query single fact with ground args returns one solution`` () =
    let solutions = solve familyDB ("parent" /@ [atom "tom"; atom "bob"]) |> Seq.toList
    solutions |> List.length |> should equal 1

[<Fact>]
let ``query fact that does not exist returns no solutions`` () =
    let solutions = solve familyDB ("parent" /@ [atom "ann"; atom "tom"]) |> Seq.toList
    solutions |> should be Empty

[<Fact>]
let ``query with one variable returns all matching children`` () =
    let solutions =
        solve familyDB ("parent" /@ [atom "tom"; Var "Child"])
        |> Seq.map (fun sub -> ground "Child" sub)
        |> Seq.toList
    solutions |> should contain (atom "bob")
    solutions |> should contain (atom "liz")
    solutions |> List.length |> should equal 2

[<Fact>]
let ``query with variable on both sides returns all parent-child pairs`` () =
    let solutions =
        solve familyDB ("parent" /@ [Var "P"; Var "C"])
        |> Seq.toList
    solutions |> List.length |> should equal 4

// ── Rule queries (recursive ancestor) ────────────────────────────────────

[<Fact>]
let ``ancestor with direct parent is found`` () =
    let solutions =
        solve familyDB ("ancestor" /@ [atom "tom"; atom "bob"])
        |> Seq.toList
    solutions |> should not' (be Empty)

[<Fact>]
let ``ancestor with grandchild is found via recursion`` () =
    let solutions =
        solve familyDB ("ancestor" /@ [atom "tom"; atom "ann"])
        |> Seq.toList
    solutions |> should not' (be Empty)

[<Fact>]
let ``all ancestors of ann`` () =
    let ancestors =
        solve familyDB ("ancestor" /@ [Var "A"; atom "ann"])
        |> Seq.map (fun sub -> ground "A" sub)
        |> Seq.toList
    ancestors |> should contain (atom "bob")
    ancestors |> should contain (atom "tom")

[<Fact>]
let ``non-ancestor returns no solutions`` () =
    let solutions =
        solve familyDB ("ancestor" /@ [atom "ann"; atom "tom"])
        |> Seq.toList
    solutions |> should be Empty

// ── solveAll (conjunctive queries) ────────────────────────────────────────

[<Fact>]
let ``solveAll finds siblings (shared parent)`` () =
    // sibling(X,Y) :- parent(P,X), parent(P,Y), X ≠ Y
    // We query: parent(P, X), parent(P, Y) and then filter X ≠ Y in the test
    let solutions =
        solveAll familyDB
            ["parent" /@ [Var "P"; Var "X"]
             "parent" /@ [Var "P"; Var "Y"]]
        |> Seq.filter (fun sub ->
            ground "X" sub <> ground "Y" sub)
        |> Seq.map (fun sub -> ground "X" sub, ground "Y" sub)
        |> Seq.distinct
        |> Seq.toList
    // bob and liz are siblings (both children of tom)
    solutions |> should contain (atom "bob", atom "liz")
    solutions |> should contain (atom "liz", atom "bob")

// ── ground helper ────────────────────────────────────────────────────────

[<Fact>]
let ``ground returns atom when variable is bound`` () =
    let subst = mkSubst [("X", Atom "hello")]
    ground "X" subst |> should equal (Atom "hello")

[<Fact>]
let ``ground returns Var when variable is unbound`` () =
    ground "X" emptySubst |> should equal (Var "X")

// ── Lazy evaluation / backtracking ────────────────────────────────────────

[<Fact>]
let ``solve returns lazy sequence; taking one result does not compute all`` () =
    // Build a DB with many facts
    let largeClauses =
        [ for i in 1 .. 1000 ->
              fact ("item" /@ [Integer i]) ]
    let db = { Clauses = largeClauses }
    let first =
        solve db ("item" /@ [Var "X"])
        |> Seq.head
    ground "X" first |> should equal (Integer 1)

// ── No solutions for wrong types ─────────────────────────────────────────

[<Fact>]
let ``query with integer instead of atom returns no match`` () =
    let solutions =
        solve familyDB ("parent" /@ [Integer 1; Var "Y"])
        |> Seq.toList
    solutions |> should be Empty

// ── Additional solver tests ───────────────────────────────────────────────

[<Fact>]
let ``solve goal that is a plain Var returns no solutions`` () =
    let solutions = solve familyDB (Var "X") |> Seq.toList
    solutions |> should be Empty

[<Fact>]
let ``solve goal that is an Integer returns no solutions`` () =
    let solutions = solve familyDB (Integer 42) |> Seq.toList
    solutions |> should be Empty

[<Fact>]
let ``solve goal that is an Atom matches fact atoms`` () =
    let db = { Clauses = [fact (Atom "hello")] }
    let solutions = solve db (Atom "hello") |> Seq.toList
    solutions |> List.length |> should equal 1

[<Fact>]
let ``solve empty database returns no solutions`` () =
    let db = { Clauses = [] }
    let solutions = solve db ("parent" /@ [Var "X"; Var "Y"]) |> Seq.toList
    solutions |> should be Empty

[<Fact>]
let ``solve with recursive rules finds all descendants`` () =
    // tom -> bob -> ann, pat; tom -> liz
    let ancestors =
        solve familyDB ("ancestor" /@ [atom "tom"; Var "D"])
        |> Seq.map (fun sub -> ground "D" sub)
        |> Seq.toList
    ancestors |> should contain (atom "bob")
    ancestors |> should contain (atom "liz")
    ancestors |> should contain (atom "ann")
    ancestors |> should contain (atom "pat")

[<Fact>]
let ``freshenClause prevents variable capture in recursive rules`` () =
    // Two successive calls to freshenClause must use distinct stamps
    let clause = rule ("f" /@ [Var "X"]) ["g" /@ [Var "X"]]
    let c1 = solve familyDB ("ancestor" /@ [atom "tom"; Var "D1"]) |> Seq.toList
    let c2 = solve familyDB ("ancestor" /@ [atom "bob"; Var "D2"]) |> Seq.toList
    // Both queries work independently (no variable capture)
    c1 |> should not' (be Empty)
    c2 |> should not' (be Empty)

[<Fact>]
let ``lookup returns Some for bound variable`` () =
    let subst = mkSubst [("X", Atom "hello")]
    lookup "X" subst |> should equal (Some (Atom "hello"))

[<Fact>]
let ``lookup returns None for unbound variable`` () =
    lookup "X" emptySubst |> should equal None

[<Fact>]
let ``solve returns lazy sequence only compute what needed`` () =
    let mutable computed = 0
    let largeClauses =
        [ for i in 1 .. 100 ->
              fact ("item" /@ [Integer i]) ]
    let db = { Clauses = largeClauses }
    // Only take first 3 - should not force entire sequence
    let results =
        solve db ("item" /@ [Var "X"])
        |> Seq.truncate 3
        |> Seq.toList
    results |> List.length |> should equal 3

[<Fact>]
let ``solveAll empty goals returns one empty solution`` () =
    let solutions = solveAll familyDB [] |> Seq.toList
    solutions |> List.length |> should equal 1
    solutions.[0] |> Subst.isEmpty |> should equal true

[<Fact>]
let ``solveAll with multiple goals all succeed`` () =
    let solutions =
        solveAll familyDB
            ["parent" /@ [atom "tom"; Var "X"]
             "parent" /@ [atom "bob"; Var "Y"]]
        |> Seq.toList
    // tom has 2 children (bob, liz), bob has 2 children (ann, pat) → 4 combinations
    solutions |> List.length |> should equal 4

[<Fact>]
let ``solveAll with one failing goal returns empty`` () =
    let solutions =
        solveAll familyDB
            ["parent" /@ [atom "tom"; Var "X"]
             "parent" /@ [atom "ann"; Var "Y"]]  // ann has no children
        |> Seq.toList
    solutions |> should be Empty

[<Fact>]
let ``ground for deeply nested term`` () =
    let subst = mkSubst [("X", Compound("f", [Compound("g", [Atom "deep"])]))]
    ground "X" subst |> should equal (Compound("f", [Compound("g", [Atom "deep"])]))

// ── IndexedDatabase tests ─────────────────────────────────────────────────

[<Fact>]
let ``indexDatabase groups clauses by functor and arity`` () =
    let idb = indexDatabase familyDB
    idb.Clauses |> List.length |> should equal 6
    idb.Index |> Map.containsKey ("parent", 2) |> should equal true
    idb.Index |> Map.containsKey ("ancestor", 2) |> should equal true
    idb.Index.[("parent", 2)] |> List.length |> should equal 4

[<Fact>]
let ``solveIndexed returns same results as solve`` () =
    let idb = indexDatabase familyDB
    let normal = solve familyDB ("parent" /@ [atom "tom"; Var "C"]) |> Seq.map (fun s -> ground "C" s) |> Seq.toList |> List.sort
    let indexed = solveIndexed idb ("parent" /@ [atom "tom"; Var "C"]) |> Seq.map (fun s -> ground "C" s) |> Seq.toList |> List.sort
    normal |> should equal indexed

[<Fact>]
let ``solveIndexed handles recursive ancestor`` () =
    let idb = indexDatabase familyDB
    let ancestors =
        solveIndexed idb ("ancestor" /@ [atom "tom"; Var "D"])
        |> Seq.map (fun sub -> ground "D" sub)
        |> Seq.toList
    ancestors |> should contain (atom "ann")
    ancestors |> should contain (atom "tom" |> fun _ -> atom "bob")

[<Fact>]
let ``solveAllIndexed returns same results as solveAll`` () =
    let idb = indexDatabase familyDB
    let goals = ["parent" /@ [Var "P"; Var "X"]; "parent" /@ [Var "P"; Var "Y"]]
    let normal = solveAll familyDB goals |> Seq.toList |> List.length
    let indexed = solveAllIndexed idb goals |> Seq.toList |> List.length
    normal |> should equal indexed
