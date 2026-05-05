/// AOT compatibility test suite for FsLogical.
/// Published and run as a Native AOT binary to verify every major feature
/// works correctly under ahead-of-time compilation.
///
/// Exit codes:
///   0  – all tests passed
///   1  – one or more tests failed
module FsLogical.AotTests.Program

open System
open FsLogical.Term
open FsLogical.Unification
open FsLogical.Solver
open FsLogical.DSL
open FsLogical.PrologImport

// ── Minimal test harness ─────────────────────────────────────────────────────

let mutable private failures = 0

let private test (name: string) (body: unit -> unit) =
    try
        body ()
        printfn "  PASS  %s" name
    with ex ->
        printfn "  FAIL  %s\n        %s" name ex.Message
        failures <- failures + 1

let private check (label: string) (cond: bool) =
    if not cond then failwith $"Assertion failed: {label}"

// ── Test cases ───────────────────────────────────────────────────────────────

// ── Term construction & normalisation ────────────────────────────────────────

let private termTests () =
    test "Atom ToString" (fun () ->
        check "atom str" (Atom("foo").ToString() = "foo"))

    test "Integer ToString" (fun () ->
        check "int str" (Integer(42).ToString() = "42"))

    test "Float ToString" (fun () ->
        check "float str" ((Float 3.14).ToString().StartsWith("3.14")))

    test "Var ToString" (fun () ->
        check "var str" (Var("X").ToString() = "X"))

    test "Compound ToString" (fun () ->
        let t = "parent" /@ [Atom "tom"; Atom "bob"]
        check "compound str" (t.ToString() = "parent(tom, bob)"))

    test "normalize zero-arity compound → Atom" (fun () ->
        let t = normalize (Compound("foo", []))
        check "is atom" (t = Atom "foo"))

    test "/@ operator" (fun () ->
        let t = "f" /@ [Integer 1; Atom "a"]
        match t with
        | Compound("f", [Integer 1; Atom "a"]) -> ()
        | _ -> failwith "unexpected shape")

    test "atom / int' / float' / var helpers" (fun () ->
        check "atom" (atom "x" = Atom "x")
        check "int'" (int' 3 = Integer 3)
        check "float'" (float' 1.0 = Float 1.0)
        check "var" (var "X" = Var "X"))

    test "isGround on ground term" (fun () ->
        check "ground" (isGround (Atom "a") Subst.empty))

    test "isGround on unbound var" (fun () ->
        check "not ground" (not (isGround (Var "X") Subst.empty)))

// ── Subst helpers ─────────────────────────────────────────────────────────────

let private substTests () =
    test "Subst.empty is empty" (fun () ->
        check "empty" (Subst.isEmpty Subst.empty))

    test "Subst.add / tryFind round-trip" (fun () ->
        let s = Subst.add "X" (Atom "a") Subst.empty
        check "found" (Subst.tryFind "X" s = Some (Atom "a"))
        check "miss" (Subst.tryFind "Y" s = None))

    test "Subst.count" (fun () ->
        let s = Subst.ofSeq [("A", Atom "x"); ("B", Integer 1)]
        check "count" (Subst.count s = 2))

    test "Subst.toMap" (fun () ->
        let s = Subst.ofSeq [("K", Atom "v")]
        let m = Subst.toMap s
        check "map key" (Map.containsKey "K" m))

// ── Unification ──────────────────────────────────────────────────────────────

let private unificationTests () =
    test "unify identical atoms" (fun () ->
        let r = unifyFresh (Atom "a") (Atom "a")
        check "some" (Option.isSome r))

    test "unify fails on different atoms" (fun () ->
        let r = unifyFresh (Atom "a") (Atom "b")
        check "none" (Option.isNone r))

    test "unify variable with atom" (fun () ->
        let r = unifyFresh (Var "X") (Atom "hello")
        check "some" (Option.isSome r)
        let s = r.Value
        check "binding" (Subst.tryFind "X" s = Some (Atom "hello")))

    test "unify compounds" (fun () ->
        let t1 = "f" /@ [Var "X"; Atom "b"]
        let t2 = "f" /@ [Atom "a"; Atom "b"]
        let r = unifyFresh t1 t2
        check "some" (Option.isSome r)
        check "X=a" (Subst.tryFind "X" r.Value = Some (Atom "a")))

    test "unify fails arity mismatch" (fun () ->
        let r = unifyFresh ("f" /@ [Atom "a"]) ("f" /@ [Atom "a"; Atom "b"])
        check "none" (Option.isNone r))

    test "walk through chain" (fun () ->
        let s = Subst.ofSeq [("X", Var "Y"); ("Y", Atom "end")]
        let result = walk (Var "X") s
        check "end" (result = Atom "end"))

    test "applySubst deep" (fun () ->
        let s = Subst.ofSeq [("X", Atom "deep")]
        let t = "f" /@ [Var "X"]
        let r = applySubst s t
        check "applied" (r = ("f" /@ [Atom "deep"])))

    test "occursIn detects cycle candidate" (fun () ->
        // occursIn "X" (f(X)) should return true
        let t = "f" /@ [Var "X"]
        check "occurs" (occursIn "X" t Subst.empty))

// ── Solver ────────────────────────────────────────────────────────────────────

let private buildFamilyDB () =
    { Clauses =
        [ fact ("parent" /@ [atom "tom";  atom "bob"])
          fact ("parent" /@ [atom "tom";  atom "liz"])
          fact ("parent" /@ [atom "bob";  atom "ann"])
          fact ("parent" /@ [atom "bob";  atom "pat"])
          rule ("ancestor" /@ [Var "X"; Var "Y"]) ["parent" /@ [Var "X"; Var "Y"]]
          rule ("ancestor" /@ [Var "X"; Var "Y"])
               ["parent" /@ [Var "X"; Var "Z"]; "ancestor" /@ [Var "Z"; Var "Y"]] ] }

let private solverTests () =
    let db = buildFamilyDB ()

    test "solve ground fact" (fun () ->
        let r = solve db ("parent" /@ [atom "tom"; atom "bob"]) |> Seq.toList
        check "one solution" (r.Length = 1))

    test "solve all children of tom" (fun () ->
        let children =
            solve db ("parent" /@ [atom "tom"; Var "C"])
            |> Seq.map (fun s -> ground "C" s)
            |> Seq.toList
        check "bob" (List.contains (Atom "bob") children)
        check "liz" (List.contains (Atom "liz") children)
        check "count" (children.Length = 2))

    test "recursive ancestor" (fun () ->
        let ancestors =
            solve db ("ancestor" /@ [atom "tom"; Var "D"])
            |> Seq.map (fun s -> ground "D" s)
            |> Seq.toList
        check "ann" (List.contains (Atom "ann") ancestors)
        check "bob" (List.contains (Atom "bob") ancestors))

    test "no solutions for non-fact" (fun () ->
        let r = solve db ("parent" /@ [atom "ann"; Var "X"]) |> Seq.toList
        check "empty" (r.IsEmpty))

    test "solveN limits solutions" (fun () ->
        let r = solveN 1 db ("parent" /@ [atom "tom"; Var "X"]) |> Seq.toList
        check "one" (r.Length = 1))

    test "solveAll conjunction" (fun () ->
        let goals =
            [ "parent" /@ [atom "tom"; Var "X"]
              "parent" /@ [atom "bob"; Var "Y"] ]
        let r = solveAll db goals |> Seq.toList
        check "four combos" (r.Length = 4))

    test "lookup / ground" (fun () ->
        let s = Subst.ofSeq [("X", Atom "hello")]
        check "lookup some" (lookup "X" s = Some (Atom "hello"))
        check "lookup none" (lookup "Z" s = None)
        check "ground" (ground "X" s = Atom "hello"))

    test "maxDepth 0 returns empty" (fun () ->
        let opts = { MaxDepth = 0 }
        let r = solveWithOptions opts db ("parent" /@ [atom "tom"; atom "bob"]) |> Seq.toList
        check "empty" (r.IsEmpty))

// ── IndexedDatabase ───────────────────────────────────────────────────────────

let private indexedTests () =
    let db = buildFamilyDB ()
    let idb = indexDatabase db

    test "indexDatabase creates index" (fun () ->
        check "parent key" (Map.containsKey ("parent", 2) idb.Index)
        check "ancestor key" (Map.containsKey ("ancestor", 2) idb.Index)
        check "parent count" (idb.Index.[("parent", 2)].Length = 4))

    test "solveIndexed same results as solve" (fun () ->
        let normal =
            solve db ("parent" /@ [atom "tom"; Var "C"])
            |> Seq.map (fun s -> ground "C" s) |> Seq.toList |> List.sort
        let indexed =
            solveIndexed idb ("parent" /@ [atom "tom"; Var "C"])
            |> Seq.map (fun s -> ground "C" s) |> Seq.toList |> List.sort
        check "equal" (normal = indexed))

    test "solveIndexed recursive ancestor" (fun () ->
        let ancs =
            solveIndexed idb ("ancestor" /@ [atom "tom"; Var "D"])
            |> Seq.map (fun s -> ground "D" s)
            |> Seq.toList
        check "ann" (List.contains (Atom "ann") ancs))

// ── DSL ───────────────────────────────────────────────────────────────────────

let private dslTests () =
    test "logicDB computation expression" (fun () ->
        let db =
            logicDB {
                yield fact ("edge" /@ [atom "a"; atom "b"])
                yield fact ("edge" /@ [atom "b"; atom "c"])
                yield ("path" /@ [Var "X"; Var "Y"]) |- ["edge" /@ [Var "X"; Var "Y"]]
                yield ("path" /@ [Var "X"; Var "Y"]) |-
                      [ "edge" /@ [Var "X"; Var "Z"]
                        "path" /@ [Var "Z"; Var "Y"] ]
            }
        let r =
            query db ("path" /@ [atom "a"; atom "c"])
            |> Seq.toList
        check "reachable" (r.Length > 0))

    test "logicQuery computation expression" (fun () ->
        let db =
            logicDB {
                yield fact ("num" /@ [Integer 1])
                yield fact ("num" /@ [Integer 2])
            }
        let results =
            logicQuery {
                let! s = query db ("num" /@ [Var "N"])
                return valueOf "N" s
            }
            |> Seq.toList
        check "two nums" (results.Length = 2))

    test "wild creates distinct variables" (fun () ->
        let w1 = wild ()
        let w2 = wild ()
        check "distinct" (w1 <> w2))

    test "BoundVar active pattern" (fun () ->
        let s = Subst.ofSeq [("X", Atom "val")]
        match s with
        | BoundVar "X" t -> check "val" (t = Atom "val")
        | _ -> failwith "expected bound")

    test "UnboundVar active pattern" (fun () ->
        match Subst.empty with
        | UnboundVar "X" -> ()
        | _ -> failwith "expected unbound")

    test "Pred active pattern" (fun () ->
        let t = "foo" /@ [Atom "a"; Atom "b"]
        match t with
        | Pred "foo" [Atom "a"; Atom "b"] -> ()
        | _ -> failwith "pred match failed")

    test "|- operator builds rule" (fun () ->
        let head = "parent" /@ [Var "X"; Var "Y"]
        let body = ["child" /@ [Var "Y"; Var "X"]]
        let clause = head |- body
        check "head" (clause.Head = head)
        check "body" (clause.Body = body))

// ── PrologImport ──────────────────────────────────────────────────────────────

let private prologImportTests () =
    test "parseString: fact" (fun () ->
        let db = parseString "parent(alice, bob)."
        check "one clause" (db.Clauses.Length = 1)
        check "head" (db.Clauses.[0].Head = ("parent" /@ [Atom "alice"; Atom "bob"]))
        check "no body" (db.Clauses.[0].Body.IsEmpty))

    test "parseString: rule" (fun () ->
        let db = parseString "ancestor(X,Y) :- parent(X,Y)."
        check "one clause" (db.Clauses.Length = 1)
        check "body" (not db.Clauses.[0].Body.IsEmpty))

    test "parseString: query works" (fun () ->
        let db = parseString """
parent(alice, bob).
parent(bob, carol).
ancestor(X,Y) :- parent(X,Y).
ancestor(X,Y) :- parent(X,Z), ancestor(Z,Y).
"""
        let r =
            solve db ("ancestor" /@ [Atom "alice"; Var "D"])
            |> Seq.map (fun s -> ground "D" s)
            |> Seq.toList
        check "bob" (List.contains (Atom "bob") r)
        check "carol" (List.contains (Atom "carol") r))

    test "parseString: integers and floats" (fun () ->
        let db = parseString "val(42, 3.14)."
        let t = db.Clauses.[0].Head
        check "head" (t = ("val" /@ [Integer 42; Float 3.14])))

    test "parseString: list syntax" (fun () ->
        let db = parseString "items([a,b,c])."
        check "one" (db.Clauses.Length = 1))

    test "parseString: comments skipped" (fun () ->
        let db = parseString "% comment\nfoo(x). /* block */ bar(y)."
        check "two clauses" (db.Clauses.Length = 2))

    test "parseString: directives skipped" (fun () ->
        let db = parseString ":- module(m, []). fact(a)."
        check "one clause" (db.Clauses.Length = 1))

    test "parseString: negative integer" (fun () ->
        let db = parseString "neg(-1)."
        check "neg" (db.Clauses.[0].Head = ("neg" /@ [Integer -1])))

// ── Entry point ──────────────────────────────────────────────────────────────

[<EntryPoint>]
let main _ =
    printfn "=== FsLogical Native AOT Tests ==="
    printfn ""
    printfn "Term tests:"
    termTests ()
    printfn ""
    printfn "Subst tests:"
    substTests ()
    printfn ""
    printfn "Unification tests:"
    unificationTests ()
    printfn ""
    printfn "Solver tests:"
    solverTests ()
    printfn ""
    printfn "IndexedDatabase tests:"
    indexedTests ()
    printfn ""
    printfn "DSL tests:"
    dslTests ()
    printfn ""
    printfn "PrologImport tests:"
    prologImportTests ()
    printfn ""
    if failures = 0 then
        printfn "All AOT tests passed."
        0
    else
        printfn "%d test(s) FAILED." failures
        1
