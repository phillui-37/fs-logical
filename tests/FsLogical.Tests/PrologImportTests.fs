module FsLogical.Tests.PrologImportTests

open Xunit
open FsUnit.Xunit
open FsLogical.Term
open FsLogical.Solver
open FsLogical.PrologImport

// ── Helpers ──────────────────────────────────────────────────────────────────

/// Build the expected cons-cell representation of a Prolog list.
let private mkList (elems: Term list) =
    List.foldBack (fun e acc -> Compound(".", [e; acc])) elems (Atom "[]")

// ── Facts ─────────────────────────────────────────────────────────────────────

[<Fact>]
let ``parse single atom fact`` () =
    let db = parseString "alive."
    db.Clauses |> List.length |> should equal 1
    db.Clauses.[0].Head |> should equal (Atom "alive")
    db.Clauses.[0].Body |> should be Empty

[<Fact>]
let ``parse compound fact`` () =
    let db = parseString "parent(tom, bob)."
    db.Clauses |> List.length |> should equal 1
    db.Clauses.[0].Head |> should equal (Compound("parent", [Atom "tom"; Atom "bob"]))

[<Fact>]
let ``parse integer fact`` () =
    let db = parseString "age(alice, 30)."
    db.Clauses.[0].Head |> should equal (Compound("age", [Atom "alice"; Integer 30]))

[<Fact>]
let ``parse float fact`` () =
    let db = parseString "weight(bob, 72.5)."
    db.Clauses.[0].Head |> should equal (Compound("weight", [Atom "bob"; Float 72.5]))

[<Fact>]
let ``parse negative integer`` () =
    let db = parseString "temperature(arctic, -40)."
    db.Clauses.[0].Head
    |> should equal (Compound("temperature", [Atom "arctic"; Integer -40]))

[<Fact>]
let ``parse negative float`` () =
    let db = parseString "offset(-1.5)."
    db.Clauses.[0].Head |> should equal (Compound("offset", [Float -1.5]))

[<Fact>]
let ``parse quoted atom`` () =
    let db = parseString "'hello world'(a)."
    db.Clauses.[0].Head
    |> should equal (Compound("hello world", [Atom "a"]))

[<Fact>]
let ``parse multiple facts`` () =
    let src = "parent(tom, bob).\nparent(tom, liz).\nparent(bob, ann)."
    let db  = parseString src
    db.Clauses |> List.length |> should equal 3

// ── Variables ─────────────────────────────────────────────────────────────────

[<Fact>]
let ``parse fact with variables`` () =
    let db = parseString "equal(X, X)."
    db.Clauses.[0].Head |> should equal (Compound("equal", [Var "X"; Var "X"]))

[<Fact>]
let ``anonymous variables are distinct`` () =
    let db = parseString "any(_, _)."
    let args =
        match db.Clauses.[0].Head with
        | Compound(_, a) -> a
        | _              -> failwith "expected compound"
    args.[0] |> should not' (equal args.[1])
    // Both should be Var values (not Atom / Compound)
    args |> List.forall (function Var _ -> true | _ -> false) |> should equal true

// ── Lists ─────────────────────────────────────────────────────────────────────

[<Fact>]
let ``parse empty list fact`` () =
    let db = parseString "empty([])."
    db.Clauses.[0].Head |> should equal (Compound("empty", [Atom "[]"]))

[<Fact>]
let ``parse ground list fact`` () =
    let db     = parseString "colors([red, green, blue])."
    let list   = mkList [Atom "red"; Atom "green"; Atom "blue"]
    db.Clauses.[0].Head |> should equal (Compound("colors", [list]))

[<Fact>]
let ``parse list with tail variable`` () =
    let db   = parseString "hd([H|_])."
    let args =
        match db.Clauses.[0].Head with
        | Compound(_, a) -> a
        | _              -> failwith "expected compound"
    // args.[0] should be a Compound(".", [Var "H"; Var _anon])
    match args.[0] with
    | Compound(".", [Var "H"; Var _]) -> ()
    | other -> failwith (sprintf "unexpected: %A" other)

[<Fact>]
let ``parse nested list`` () =
    let db = parseString "matrix([[1,2],[3,4]])."
    db.Clauses |> List.length |> should equal 1
    // Just check it parsed without error
    match db.Clauses.[0].Head with
    | Compound("matrix", [_]) -> ()
    | other -> failwith (sprintf "unexpected: %A" other)

// ── Rules ─────────────────────────────────────────────────────────────────────

[<Fact>]
let ``parse simple rule`` () =
    let db = parseString "ancestor(X, Y) :- parent(X, Y)."
    db.Clauses |> List.length |> should equal 1
    let c = db.Clauses.[0]
    c.Head |> should equal (Compound("ancestor", [Var "X"; Var "Y"]))
    c.Body |> should equal [Compound("parent", [Var "X"; Var "Y"])]

[<Fact>]
let ``parse rule with conjunction`` () =
    let db = parseString "ancestor(X,Y) :- parent(X,Z), ancestor(Z,Y)."
    db.Clauses.[0].Body |> List.length |> should equal 2

[<Fact>]
let ``parse rule with three goals`` () =
    let db = parseString "path(X,Z) :- edge(X,Y), edge(Y,Z), edge(Z,X)."
    db.Clauses.[0].Body |> List.length |> should equal 3

// ── Comments ──────────────────────────────────────────────────────────────────

[<Fact>]
let ``line comment is ignored`` () =
    let src = "% this is a comment\nfoo(a). % trailing comment\nbar(b)."
    let db  = parseString src
    db.Clauses |> List.length |> should equal 2

[<Fact>]
let ``block comment is ignored`` () =
    let src = "/* block\ncomment */\nfoo(a)."
    let db  = parseString src
    db.Clauses |> List.length |> should equal 1

// ── Directives ────────────────────────────────────────────────────────────────

[<Fact>]
let ``directive is skipped`` () =
    let src = ":- use_module(library(lists)).\nfoo(a)."
    let db  = parseString src
    db.Clauses |> List.length |> should equal 1
    db.Clauses.[0].Head |> should equal (Compound("foo", [Atom "a"]))

[<Fact>]
let ``multiple directives are all skipped`` () =
    let src = ":- module(m, []).\n:- use_module(lists).\nfoo(1)."
    let db  = parseString src
    db.Clauses |> List.length |> should equal 1

// ── Error recovery ────────────────────────────────────────────────────────────

[<Fact>]
let ``malformed clause is skipped and rest is parsed`` () =
    // foo( is unterminated; the dot after it triggers recovery
    let src = "foo(.\nbar(b)."
    let db  = parseString src
    // foo(. is malformed → skipped; bar(b). parses fine
    db.Clauses |> List.length |> should equal 1
    db.Clauses.[0].Head |> should equal (Compound("bar", [Atom "b"]))

[<Fact>]
let ``parse empty string`` () =
    let db = parseString ""
    db.Clauses |> should be Empty

[<Fact>]
let ``parse only comments`` () =
    let db = parseString "% just a comment\n/* another comment */"
    db.Clauses |> should be Empty

// ── Infix operators in term positions ─────────────────────────────────────────

[<Fact>]
let ``infix operator in fact arg`` () =
    // foo(1+2) is unusual in a KB but should parse
    let db = parseString "foo(1+2)."
    db.Clauses |> List.length |> should equal 1
    db.Clauses.[0].Head
    |> should equal (Compound("foo", [Compound("+", [Integer 1; Integer 2])]))

[<Fact>]
let ``is/2 goal in rule body`` () =
    let db = parseString "double(X, Y) :- Y is X * 2."
    let body = db.Clauses.[0].Body
    body |> List.length |> should equal 1
    match body.[0] with
    | Compound("is", [Var "Y"; Compound("*", [Var "X"; Integer 2])]) -> ()
    | other -> failwith (sprintf "unexpected body: %A" other)

// ── Integration: parsed database works with the solver ───────────────────────

[<Fact>]
let ``parsed family db solves parent query`` () =
    let src = """
parent(tom, bob).
parent(tom, liz).
parent(bob, ann).
parent(bob, pat).
"""
    let db      = parseString src
    let results =
        solve db ("parent" /@ [Atom "tom"; Var "C"])
        |> Seq.map (fun s -> ground "C" s)
        |> Seq.toList
    results |> should contain (Atom "bob")
    results |> should contain (Atom "liz")
    results |> List.length |> should equal 2

[<Fact>]
let ``parsed family db solves ancestor query`` () =
    let src = """
parent(tom, bob).
parent(tom, liz).
parent(bob, ann).
parent(bob, pat).
ancestor(X, Y) :- parent(X, Y).
ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
"""
    let db       = parseString src
    let ancestors =
        solve db ("ancestor" /@ [Var "A"; Atom "ann"])
        |> Seq.map (fun s -> ground "A" s)
        |> Seq.toList
    ancestors |> should contain (Atom "bob")
    ancestors |> should contain (Atom "tom")

[<Fact>]
let ``parsed db can be used with indexDatabase`` () =
    let src = "parent(tom,bob).\nparent(tom,liz).\nancestor(X,Y) :- parent(X,Y)."
    let db  = parseString src
    let idb = indexDatabase db
    idb.Index |> Map.containsKey ("parent", 2)   |> should equal true
    idb.Index |> Map.containsKey ("ancestor", 2) |> should equal true
    idb.Index.[("parent", 2)]   |> List.length   |> should equal 2
    idb.Index.[("ancestor", 2)] |> List.length   |> should equal 1
