module FsLogical.Tests.SolverTests

open Xunit
open FsUnit.Xunit
open FsLogical.Term
open FsLogical.Unification
open FsLogical.Solver

// ── Helpers ──────────────────────────────────────────────────────────────

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
    let subst = Map.ofList [("X", Atom "hello")]
    ground "X" subst |> should equal (Atom "hello")

[<Fact>]
let ``ground returns Var when variable is unbound`` () =
    let subst = Map.empty
    ground "X" subst |> should equal (Var "X")

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
