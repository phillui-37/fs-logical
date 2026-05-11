/// Tests verifying that recursive term-processing functions raise
/// InvalidOperationException before hitting an actual stack overflow when given
/// terms whose nesting depth exceeds maxTermDepth.
module FsLogical.Tests.StackGuardTests

open System
open Xunit
open FsUnit.Xunit
open FsLogical.Term
open FsLogical.Unification
open FsLogical.Solver

// ── Helpers ───────────────────────────────────────────────────────────────────

/// Build a Prolog list [1, 2, ..., n] as nested Compound(".", ...) terms.
/// Constructed iteratively to avoid stack overflow during test setup.
let private makePrologList (n: int) : Term =
    let mutable acc = Atom "[]"
    for i in n .. -1 .. 1 do
        acc <- Compound(".", [Integer i; acc])
    acc

// ── normalize guard ───────────────────────────────────────────────────────────

[<Fact>]
let ``stack guard: normalize raises on term deeper than maxTermDepth`` () =
    let deepTerm = makePrologList (maxTermDepth + 1)
    Assert.Throws<InvalidOperationException>(fun () ->
        normalize deepTerm |> ignore)
    |> ignore

[<Fact>]
let ``stack guard: normalize succeeds on term within maxTermDepth`` () =
    let term = makePrologList (maxTermDepth / 2)
    // Should complete without raising
    let result = normalize term
    result |> should not' (equal (Atom "impossible"))

// ── isGround guard ────────────────────────────────────────────────────────────

[<Fact>]
let ``stack guard: isGround raises on term deeper than maxTermDepth`` () =
    let deepTerm = makePrologList (maxTermDepth + 1)
    Assert.Throws<InvalidOperationException>(fun () ->
        isGround deepTerm Subst.empty |> ignore)
    |> ignore

// ── applySubst guard ──────────────────────────────────────────────────────────

[<Fact>]
let ``stack guard: applySubst raises on term deeper than maxTermDepth`` () =
    let deepTerm = makePrologList (maxTermDepth + 1)
    let ex = Assert.Throws<InvalidOperationException>(fun () ->
        applySubst Subst.empty deepTerm |> ignore)
    ex.Message.Contains(string maxTermDepth) |> should equal true

[<Fact>]
let ``stack guard: applySubst succeeds on term within maxTermDepth`` () =
    let term = makePrologList (maxTermDepth / 2)
    // Should complete without raising
    let result = applySubst Subst.empty term
    result |> should not' (equal (Atom "impossible"))

// ── occursIn guard ────────────────────────────────────────────────────────────

[<Fact>]
let ``stack guard: occursIn raises on term deeper than maxTermDepth`` () =
    let deepTerm = makePrologList (maxTermDepth + 1)
    Assert.Throws<InvalidOperationException>(fun () ->
        occursIn "X" deepTerm Subst.empty |> ignore)
    |> ignore

[<Fact>]
let ``stack guard: occursIn succeeds on term within maxTermDepth`` () =
    let term = makePrologList (maxTermDepth / 2)
    let result = occursIn "X" term Subst.empty
    result |> should equal false

// ── renameTerm guard (via solve / freshenClause) ──────────────────────────────

[<Fact>]
let ``stack guard: solve raises when rule body contains term deeper than maxTermDepth`` () =
    // The rule head is a plain atom so applySubst on the goal does not overflow.
    // freshenClause -> renameTerm will overflow when renaming the deep body term.
    let deepTerm = makePrologList (maxTermDepth + 1)
    let db = { Clauses = [ rule (Atom "trigger") [deepTerm] ] }
    Assert.Throws<InvalidOperationException>(fun () ->
        solve db (Atom "trigger") |> Seq.toList |> ignore)
    |> ignore
