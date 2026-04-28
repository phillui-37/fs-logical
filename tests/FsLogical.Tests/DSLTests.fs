module FsLogical.Tests.DSLTests

open Xunit
open FsUnit.Xunit
open FSharpx.Collections
open FsLogical.Term
open FsLogical.DSL

// ── Helpers ──────────────────────────────────────────────────────────────

let private mkSubst (pairs: (string * Term) list) : Substitution =
    Subst.ofSeq pairs

let private emptySubst : Substitution = Subst.empty

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
    let subst = mkSubst [("X", Atom "john")]
    match subst with
    | BoundVar "X" t -> t |> should equal (Atom "john")
    | _ -> failwith "expected BoundVar match"

[<Fact>]
let ``BoundVar active pattern does not match unbound variable`` () =
    match emptySubst with
    | BoundVar "X" _ -> failwith "should not match"
    | _ -> ()  // correct

[<Fact>]
let ``UnboundVar active pattern matches unbound variable`` () =
    match emptySubst with
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
    let subst = mkSubst [("X", Atom "result")]
    valueOf "X" subst |> should equal (Atom "result")

[<Fact>]
let ``valueOf returns Var when unbound`` () =
    valueOf "X" emptySubst |> should equal (Var "X")

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

// ── Additional DSL tests ──────────────────────────────────────────────────

[<Fact>]
let ``wild creates unique variable each call`` () =
    let w1 = wild ()
    let w2 = wild ()
    w1 |> should not' (equal w2)

[<Fact>]
let ``multiple wild calls are all different`` () =
    let wilds = [ for _ in 1..10 -> wild () ]
    let distinct = wilds |> List.distinct
    distinct |> List.length |> should equal 10

[<Fact>]
let ``logicDB with empty block gives empty database`` () =
    let db = logicDB { () }
    db.Clauses |> should be Empty

[<Fact>]
let ``logicDB with YieldFrom`` () =
    let moreClauses = [fact (atom "hello"); fact (atom "world")]
    let db = logicDB {
        yield! moreClauses
    }
    db.Clauses |> List.length |> should equal 2

[<Fact>]
let ``queryAll with empty goals returns one solution`` () =
    let solutions = queryAll family [] |> Seq.toList
    solutions |> List.length |> should equal 1

[<Fact>]
let ``queryAll with multiple goals`` () =
    let solutions =
        queryAll family
            ["parent" /@ [atom "tom"; Var "X"]
             "parent" /@ [atom "bob"; Var "Y"]]
        |> Seq.toList
    solutions |> List.length |> should equal 4

[<Fact>]
let ``BoundVar with compound value`` () =
    let subst = mkSubst [("X", Compound("f", [Atom "a"]))]
    match subst with
    | BoundVar "X" t ->
        t |> should equal (Compound("f", [Atom "a"]))
    | _ -> failwith "expected BoundVar match"

[<Fact>]
let ``UnboundVar does not match bound var`` () =
    let subst = mkSubst [("X", Atom "bound")]
    match subst with
    | UnboundVar "X" -> failwith "should not match unbound"
    | _ -> ()  // correct

[<Fact>]
let ``Pred with wrong arity doesn't match`` () =
    let term = "parent" /@ [atom "john"]  // arity 1
    match term with
    | Pred "parent" [_; _] -> failwith "should not match arity 2"
    | Pred "parent" [_] -> ()  // correct: matches arity 1
    | _ -> failwith "should have matched arity 1"

[<Fact>]
let ``Pred with zero args`` () =
    let term = "empty" /@ []
    match term with
    | Pred "empty" [] -> ()  // correct
    | _ -> failwith "expected Pred empty match"

[<Fact>]
let ``zero-arity operator result is atom-like`` () =
    let term = "ready" /@ []
    term |> should equal (Atom "ready")

[<Fact>]
let ``logicQuery with return from inner query failure is empty`` () =
    let results =
        logicQuery {
            let! sub1 = query family ("parent" /@ [atom "nobody"; Var "X"])
            return valueOf "X" sub1
        }
        |> Seq.toList
    results |> should be Empty

[<Fact>]
let ``valueOf with chain substitution`` () =
    let subst = mkSubst [("X", Var "Y"); ("Y", Atom "final")]
    valueOf "X" subst |> should equal (Atom "final")

[<Fact>]
let ``atom var int' float' constructors`` () =
    atom "hello" |> should equal (Atom "hello")
    var "X" |> should equal (Var "X")
    int' 42 |> should equal (Integer 42)
    float' 3.14 |> should equal (Float 3.14)

[<Fact>]
let ``fact and rule constructors`` () =
    let f = fact (atom "hello")
    f.Head |> should equal (Atom "hello")
    f.Body |> should be Empty
    let r = rule (atom "head") [atom "body1"; atom "body2"]
    r.Head |> should equal (Atom "head")
    r.Body |> List.length |> should equal 2

[<Fact>]
let ``logicDB builds indexed database correctly`` () =
    let idb = FsLogical.Solver.indexDatabase family
    idb.Index |> Map.containsKey ("parent", 2) |> should equal true
    idb.Index |> Map.containsKey ("ancestor", 2) |> should equal true
    idb.Index.[("parent", 2)] |> List.length |> should equal 4
    idb.Index.[("ancestor", 2)] |> List.length |> should equal 2

[<Fact>]
let ``logicQuery supports for loops`` () =
    let results =
        logicQuery {
            for parent in [atom "tom"; atom "bob"] do
                let! sub = query family ("parent" /@ [parent; Var "Child"])
                return valueOf "Child" sub
        }
        |> Seq.toList
    results |> List.length |> should equal 4
    results |> should contain (atom "bob")
    results |> should contain (atom "liz")
    results |> should contain (atom "ann")
    results |> should contain (atom "pat")
