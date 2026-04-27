module FsLogical.Tests.DSLTests

open Xunit
open FsUnit.Xunit
open FsLogical.Term
open FsLogical.DSL

// ── logicDB computation expression ───────────────────────────────────────

let private family =
    logicDB {
        // facts
        yield fact ("parent" /@ [atom "tom"; atom "bob"])
        yield fact ("parent" /@ [atom "tom"; atom "liz"])
        yield fact ("parent" /@ [atom "bob"; atom "ann"])
        yield fact ("parent" /@ [atom "bob"; atom "pat"])

        // rules using the |- operator
        yield ("ancestor" /@ [Var "X"; Var "Y"]) |- ["parent" /@ [Var "X"; Var "Y"]]
        yield ("ancestor" /@ [Var "X"; Var "Y"]) |-
              [ "parent"   /@ [Var "X"; Var "Z"]
                "ancestor" /@ [Var "Z"; Var "Y"] ]
    }

[<Fact>]
let ``logicDB builds database with correct number of clauses`` () =
    family.Clauses |> List.length |> should equal 6

[<Fact>]
let ``query returns results via DSL query helper`` () =
    let results =
        query family ("parent" /@ [atom "tom"; Var "C"])
        |> Seq.map (valueOf "C")
        |> Seq.toList
    results |> should contain (atom "bob")
    results |> should contain (atom "liz")

[<Fact>]
let ``query with ground goal succeeds`` () =
    let results = query family ("parent" /@ [atom "tom"; atom "bob"]) |> Seq.toList
    results |> List.length |> should equal 1

[<Fact>]
let ``query with no match returns empty`` () =
    let results = query family ("parent" /@ [atom "ann"; Var "X"]) |> Seq.toList
    results |> should be Empty

// ── logicQuery computation expression ────────────────────────────────────

[<Fact>]
let ``logicQuery chains two queries`` () =
    // Find all (grandparent, grandchild) pairs: parent(GP, P), parent(P, GC)
    let pairs =
        logicQuery {
            let! sub1 = query family ("parent" /@ [Var "GP"; Var "P"])
            let p = valueOf "P" sub1
            let gp = valueOf "GP" sub1
            let! sub2 = query family ("parent" /@ [p; Var "GC"])
            return gp, valueOf "GC" sub2
        }
        |> Seq.toList
    pairs |> should contain (atom "tom", atom "ann")
    pairs |> should contain (atom "tom", atom "pat")
    pairs |> List.length |> should equal 2

[<Fact>]
let ``logicQuery returns empty when inner query fails`` () =
    let results =
        logicQuery {
            let! sub = query family ("parent" /@ [atom "ann"; Var "X"])
            return valueOf "X" sub
        }
        |> Seq.toList
    results |> should be Empty

// ── Active patterns ──────────────────────────────────────────────────────

[<Fact>]
let ``BoundVar active pattern matches bound variable`` () =
    let subst = Map.ofList [("X", Atom "john")]
    match subst with
    | BoundVar "X" t -> t |> should equal (Atom "john")
    | _ -> failwith "expected BoundVar match"

[<Fact>]
let ``BoundVar active pattern does not match unbound variable`` () =
    let subst = Map.empty
    match subst with
    | BoundVar "X" _ -> failwith "should not match"
    | _ -> ()  // correct

[<Fact>]
let ``UnboundVar active pattern matches unbound variable`` () =
    let subst = Map.empty
    match subst with
    | UnboundVar "X" -> ()  // correct
    | _ -> failwith "expected UnboundVar match"

[<Fact>]
let ``Pred active pattern deconstructs compound term`` () =
    let term = "parent" /@ [atom "john"; atom "mary"]
    match term with
    | Pred "parent" [a; b] ->
        a |> should equal (atom "john")
        b |> should equal (atom "mary")
    | _ -> failwith "expected Pred match"

[<Fact>]
let ``Pred active pattern does not match wrong functor`` () =
    let term = "child" /@ [atom "ann"]
    match term with
    | Pred "parent" _ -> failwith "should not match"
    | _ -> ()  // correct

// ── valueOf helper ────────────────────────────────────────────────────────

[<Fact>]
let ``valueOf returns bound term`` () =
    let subst = Map.ofList [("X", Atom "result")]
    valueOf "X" subst |> should equal (Atom "result")

[<Fact>]
let ``valueOf returns Var when unbound`` () =
    let subst = Map.empty
    valueOf "X" subst |> should equal (Var "X")

// ── Ancestor query via DSL ────────────────────────────────────────────────

[<Fact>]
let ``ancestor query returns all ancestors of ann`` () =
    let ancestors =
        query family ("ancestor" /@ [Var "A"; atom "ann"])
        |> Seq.map (valueOf "A")
        |> Seq.toList
    ancestors |> should contain (atom "bob")
    ancestors |> should contain (atom "tom")

// ── /@ operator ──────────────────────────────────────────────────────────

[<Fact>]
let ``compound operator creates Compound term`` () =
    let term = "foo" /@ [atom "a"; atom "b"]
    term |> should equal (Compound("foo", [Atom "a"; Atom "b"]))

[<Fact>]
let ``|- operator creates rule clause`` () =
    let head = "ancestor" /@ [Var "X"; Var "Y"]
    let body = ["parent" /@ [Var "X"; Var "Y"]]
    let clause = head |- body
    clause.Head |> should equal head
    clause.Body |> should equal body
