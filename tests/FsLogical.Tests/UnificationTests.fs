module FsLogical.Tests.UnificationTests

open Xunit
open FsUnit.Xunit
open FsLogical.Term
open FsLogical.Unification

// ── Basic atom / number unification ─────────────────────────────────────

/// Helper: assert the result is Some with an empty substitution.
let private assertEmptySolution (result: Substitution option) =
    result |> Option.isSome |> should equal true
    result |> Option.get |> Map.isEmpty |> should equal true

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
    |> should equal (Some (Map.ofList [("X", Atom "hello")]))

[<Fact>]
let ``unify atom with variable binds variable`` () =
    unifyFresh (Atom "hello") (Var "X")
    |> should equal (Some (Map.ofList [("X", Atom "hello")]))

[<Fact>]
let ``unify two distinct variables binds one to the other`` () =
    let result = unifyFresh (Var "X") (Var "Y")
    result |> should not' (equal None)
    match result with
    | Some subst ->
        // One variable must be bound to the other - substitution should be non-empty
        subst |> Map.isEmpty |> should equal false
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
    result |> should equal (Some (Map.ofList [("X", Atom "john")]))

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
    let subst = Map.ofList [("X", Atom "john")]
    applySubst subst (Var "X") |> should equal (Atom "john")

[<Fact>]
let ``applySubst leaves unbound variable unchanged`` () =
    let subst = Map.ofList [("X", Atom "john")]
    applySubst subst (Var "Y") |> should equal (Var "Y")

[<Fact>]
let ``applySubst recursively substitutes in compounds`` () =
    let subst = Map.ofList [("X", Atom "john"); ("Y", Atom "mary")]
    let term = "parent" /@ [Var "X"; Var "Y"]
    applySubst subst term |> should equal ("parent" /@ [Atom "john"; Atom "mary"])

[<Fact>]
let ``applySubst follows substitution chains`` () =
    // X -> Y, Y -> john
    let subst = Map.ofList [("X", Var "Y"); ("Y", Atom "john")]
    applySubst subst (Var "X") |> should equal (Atom "john")
