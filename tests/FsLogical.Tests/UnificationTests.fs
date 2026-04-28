module FsLogical.Tests.UnificationTests

open Xunit
open FsUnit.Xunit
open FSharpx.Collections
open FsLogical.Term
open FsLogical.Unification

// ── Helpers ──────────────────────────────────────────────────────────────

/// Create a substitution from a list of key-value pairs.
let private mkSubst (pairs: (string * Term) list) : Substitution =
    Subst.ofSeq pairs

/// The empty substitution.
let private emptySubst : Substitution = Subst.empty

/// Assert that a substitution option is Some and its contents match expected pairs.
let private assertSubstMatches (expected: (string * Term) list) (result: Substitution option) =
    result |> Option.isSome |> should equal true
    let s = result.Value
    Subst.count s |> should equal (List.length expected)
    for (k, v) in expected do
        s.ContainsKey(k) |> should equal true
        s.[k] |> should equal v

/// Assert the result is Some with an empty substitution.
let private assertEmptySolution (result: Substitution option) =
    result |> Option.isSome |> should equal true
    result |> Option.get |> Subst.isEmpty |> should equal true

// ── Basic atom / number unification ─────────────────────────────────────

[<Fact>]
let ``unify identical atoms succeeds with empty substitution`` () =
    unifyFresh (Atom "foo") (Atom "foo")
    |> assertEmptySolution

[<Fact>]
let ``unify different atoms fails`` () =
    unifyFresh (Atom "foo") (Atom "bar")
    |> should equal None

[<Fact>]
let ``unify identical integers succeeds`` () =
    unifyFresh (Integer 42) (Integer 42)
    |> assertEmptySolution

[<Fact>]
let ``unify different integers fails`` () =
    unifyFresh (Integer 1) (Integer 2)
    |> should equal None

[<Fact>]
let ``unify integer with float fails`` () =
    unifyFresh (Integer 1) (Float 1.0)
    |> should equal None

// ── Variable unification ─────────────────────────────────────────────────

[<Fact>]
let ``unify variable with atom binds variable`` () =
    unifyFresh (Var "X") (Atom "hello")
    |> assertSubstMatches [("X", Atom "hello")]

[<Fact>]
let ``unify atom with variable binds variable`` () =
    unifyFresh (Atom "hello") (Var "X")
    |> assertSubstMatches [("X", Atom "hello")]

[<Fact>]
let ``unify two distinct variables binds one to the other`` () =
    let result = unifyFresh (Var "X") (Var "Y")
    result |> should not' (equal None)
    match result with
    | Some subst ->
        // One variable must be bound to the other - substitution should be non-empty
        Subst.isEmpty subst |> should equal false
    | None -> failwith "expected Some"

[<Fact>]
let ``unify variable with itself succeeds`` () =
    let result = unifyFresh (Var "X") (Var "X")
    result |> should not' (equal None)

// ── Occurs check ─────────────────────────────────────────────────────────

[<Fact>]
let ``unify variable with compound containing that variable fails (occurs check)`` () =
    // X = f(X) should fail
    unifyFresh (Var "X") ("f" /@ [Var "X"])
    |> should equal None

[<Fact>]
let ``unify variable with compound NOT containing that variable succeeds`` () =
    unifyFresh (Var "X") ("f" /@ [Atom "a"])
    |> should not' (equal None)

// ── Compound term unification ────────────────────────────────────────────

[<Fact>]
let ``unify identical compounds with no args succeeds`` () =
    unifyFresh ("foo" /@ []) ("foo" /@ [])
    |> assertEmptySolution

[<Fact>]
let ``unify compounds with same functor different arity fails`` () =
    unifyFresh ("f" /@ [Atom "a"]) ("f" /@ [Atom "a"; Atom "b"])
    |> should equal None

[<Fact>]
let ``unify compounds with different functors fails`` () =
    unifyFresh ("foo" /@ [Atom "a"]) ("bar" /@ [Atom "a"])
    |> should equal None

[<Fact>]
let ``unify compound with variable argument binds variable`` () =
    let result = unifyFresh ("parent" /@ [Var "X"; Atom "mary"]) ("parent" /@ [Atom "john"; Atom "mary"])
    result |> assertSubstMatches [("X", Atom "john")]

[<Fact>]
let ``unify nested compounds with variables`` () =
    // f(g(X), Y) = f(g(a), b)
    let lhs = "f" /@ ["g" /@ [Var "X"]; Var "Y"]
    let rhs = "f" /@ ["g" /@ [Atom "a"]; Atom "b"]
    let result = unifyFresh lhs rhs
    result |> should not' (equal None)
    match result with
    | Some subst ->
        applySubst subst (Var "X") |> should equal (Atom "a")
        applySubst subst (Var "Y") |> should equal (Atom "b")
    | None -> failwith "expected Some"

// ── applySubst ──────────────────────────────────────────────────────────

[<Fact>]
let ``applySubst replaces bound variable`` () =
    let subst = mkSubst [("X", Atom "john")]
    applySubst subst (Var "X") |> should equal (Atom "john")

[<Fact>]
let ``applySubst leaves unbound variable unchanged`` () =
    let subst = mkSubst [("X", Atom "john")]
    applySubst subst (Var "Y") |> should equal (Var "Y")

[<Fact>]
let ``applySubst recursively substitutes in compounds`` () =
    let subst = mkSubst [("X", Atom "john"); ("Y", Atom "mary")]
    let term = "parent" /@ [Var "X"; Var "Y"]
    applySubst subst term |> should equal ("parent" /@ [Atom "john"; Atom "mary"])

[<Fact>]
let ``applySubst follows substitution chains`` () =
    // X -> Y, Y -> john
    let subst = mkSubst [("X", Var "Y"); ("Y", Atom "john")]
    applySubst subst (Var "X") |> should equal (Atom "john")

// ── Additional walk tests ─────────────────────────────────────────────────

[<Fact>]
let ``walk follows multi-level variable chain`` () =
    // X -> Y -> Z -> atom
    let subst = mkSubst [("X", Var "Y"); ("Y", Var "Z"); ("Z", Atom "end")]
    walk (Var "X") subst |> should equal (Atom "end")

[<Fact>]
let ``walk returns original atom when not a variable`` () =
    walk (Atom "foo") emptySubst |> should equal (Atom "foo")

[<Fact>]
let ``walk returns same var when chain dead-ends`` () =
    let subst = mkSubst [("X", Var "Y")]
    walk (Var "X") subst |> should equal (Var "Y")

// ── Additional unify tests ────────────────────────────────────────────────

[<Fact>]
let ``unify with occurs check in nested compound fails`` () =
    // X = f(g(X)) should fail
    unifyFresh (Var "X") ("f" /@ ["g" /@ [Var "X"]])
    |> should equal None

[<Fact>]
let ``unify two different compounds with no args fails`` () =
    unifyFresh ("foo" /@ []) ("bar" /@ [])
    |> should equal None

[<Fact>]
let ``unify compound with wrong arity fails`` () =
    unifyFresh ("f" /@ [Atom "a"; Atom "b"]) ("f" /@ [Atom "a"; Atom "b"; Atom "c"])
    |> should equal None

[<Fact>]
let ``unify variable with integer succeeds`` () =
    let result = unifyFresh (Var "X") (Integer 42)
    result |> assertSubstMatches [("X", Integer 42)]

[<Fact>]
let ``unify variable with float succeeds`` () =
    let result = unifyFresh (Var "X") (Float 3.14)
    result |> assertSubstMatches [("X", Float 3.14)]

[<Fact>]
let ``unify deeply nested same structure succeeds`` () =
    let t = "a" /@ ["b" /@ ["c" /@ [Atom "d"]]]
    unifyFresh t t |> assertEmptySolution

[<Fact>]
let ``unify two variables then second variable with atom`` () =
    // Unify X=Y, then Y=atom
    let step1 = unifyFresh (Var "X") (Var "Y")
    step1 |> should not' (equal None)
    let subst1 = step1.Value
    let step2 = unify (Var "Y") (Atom "hello") subst1
    step2 |> should not' (equal None)
    let subst2 = step2.Value
    // X should be transitively bound to "hello"
    applySubst subst2 (Var "X") |> should equal (Atom "hello")

[<Fact>]
let ``unify X=Y then Y=atom results in X=atom transitively`` () =
    let subst0 = emptySubst
    let subst1 = unify (Var "X") (Var "Y") subst0 |> Option.get
    let subst2 = unify (Var "Y") (Atom "result") subst1 |> Option.get
    applySubst subst2 (Var "X") |> should equal (Atom "result")

[<Fact>]
let ``unifyFresh empty compounds are equal`` () =
    unifyFresh ("f" /@ []) ("f" /@ []) |> assertEmptySolution

[<Fact>]
let ``unify partial match one arg matches one doesn't`` () =
    // f(a, X) = f(a, b) succeeds binding X=b
    let result = unifyFresh ("f" /@ [Atom "a"; Var "X"]) ("f" /@ [Atom "a"; Atom "b"])
    result |> assertSubstMatches [("X", Atom "b")]

[<Fact>]
let ``zero-arity compounds are normalised to atoms`` () =
    "flag" /@ [] |> should equal (Atom "flag")

// ── occursIn tests ────────────────────────────────────────────────────────

[<Fact>]
let ``occursIn returns false for atoms`` () =
    occursIn "X" (Atom "foo") emptySubst |> should equal false

[<Fact>]
let ``occursIn returns true for direct var reference`` () =
    occursIn "X" (Var "X") emptySubst |> should equal true

[<Fact>]
let ``occursIn returns true through compound nesting`` () =
    occursIn "X" ("f" /@ ["g" /@ [Var "X"]]) emptySubst |> should equal true

[<Fact>]
let ``occursIn follows substitution chain`` () =
    // X -> Y, check if "X" occurs in Var "Y"
    let subst = mkSubst [("Y", Var "X")]
    occursIn "X" (Var "Y") subst |> should equal true

// ── applySubst additional tests ───────────────────────────────────────────

[<Fact>]
let ``applySubst handles deeply nested compound`` () =
    let subst = mkSubst [("X", Atom "deep")]
    let term = "a" /@ ["b" /@ ["c" /@ [Var "X"]]]
    let expected = "a" /@ ["b" /@ ["c" /@ [Atom "deep"]]]
    applySubst subst term |> should equal expected

[<Fact>]
let ``applySubst returns atoms unchanged`` () =
    applySubst emptySubst (Atom "hello") |> should equal (Atom "hello")

[<Fact>]
let ``applySubst returns integers unchanged`` () =
    applySubst emptySubst (Integer 99) |> should equal (Integer 99)

[<Fact>]
let ``isGround returns true when all variables are bound`` () =
    let subst = mkSubst [("X", Atom "left")]
    isGround ("pair" /@ [Var "X"; Atom "right"]) subst |> should equal true

[<Fact>]
let ``isGround returns false when a variable is still unbound`` () =
    isGround ("pair" /@ [Var "X"; Atom "right"]) emptySubst |> should equal false

[<Fact>]
let ``Subst.toMap converts bindings for inspection`` () =
    let subst = mkSubst [("X", Atom "left"); ("Y", Integer 2)]
    Subst.toMap subst |> should equal (Map.ofList [("X", Atom "left"); ("Y", Integer 2)])
