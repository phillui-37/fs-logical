module FsLogical.Tests.CodeGenTests

open Xunit
open FsUnit.Xunit
open FsLogical.Term
open FsLogical.PrologImport
open FsLogical.CodeGen

// ── Helpers ───────────────────────────────────────────────────────────────────

/// Assert that a string contains the given substring.
let private hasSubstring (sub: string) (s: string) =
    s.Contains(sub) |> should equal true

/// Assert that a string does not contain the given substring.
let private notHasSubstring (sub: string) (s: string) =
    s.Contains(sub) |> should equal false

// ── renderTerm ────────────────────────────────────────────────────────────────

[<Fact>]
let ``renderTerm atom produces atom helper`` () =
    renderTerm (Atom "foo") |> should equal "atom \"foo\""

[<Fact>]
let ``renderTerm empty list atom`` () =
    renderTerm (Atom "[]") |> should equal "atom \"[]\""

[<Fact>]
let ``renderTerm integer`` () =
    renderTerm (Integer 42) |> should equal "Integer 42"

[<Fact>]
let ``renderTerm negative integer`` () =
    renderTerm (Integer -7) |> should equal "Integer -7"

[<Fact>]
let ``renderTerm float`` () =
    renderTerm (Float 3.14) |> should startWith "Float 3.14"

[<Fact>]
let ``renderTerm float always has decimal point`` () =
    renderTerm (Float 1.0) |> should equal "Float 1.0"

[<Fact>]
let ``renderTerm var`` () =
    renderTerm (Var "X") |> should equal "Var \"X\""

[<Fact>]
let ``renderTerm compound`` () =
    renderTerm (Compound("parent", [Atom "tom"; Atom "bob"]))
    |> should equal "\"parent\" /@ [atom \"tom\"; atom \"bob\"]"

[<Fact>]
let ``renderTerm atom with special chars is escaped`` () =
    renderTerm (Atom "say \"hi\"")
    |> should equal "atom \"say \\\"hi\\\"\""

[<Fact>]
let ``renderTerm proper list uses prologList`` () =
    let list = Compound(".", [Atom "a"; Compound(".", [Atom "b"; Atom "[]"])])
    renderTerm list
    |> should equal "prologList [atom \"a\"; atom \"b\"]"

[<Fact>]
let ``renderTerm improper list uses /@ compound`` () =
    // [H|T] is Compound(".", [Var "H"; Var "T"])
    renderTerm (Compound(".", [Var "H"; Var "T"]))
    |> should equal "\".\" /@ [Var \"H\"; Var \"T\"]"

[<Fact>]
let ``renderTerm zero-arity compound renders as atom`` () =
    renderTerm (Compound("foo", []))
    |> should equal "atom \"foo\""

// ── renderClause ──────────────────────────────────────────────────────────────

[<Fact>]
let ``renderClause fact`` () =
    let c = fact (Atom "alive")
    renderClause c
    |> should equal "        yield fact (atom \"alive\")"

[<Fact>]
let ``renderClause rule`` () =
    let c = rule
                (Compound("ancestor", [Var "X"; Var "Y"]))
                [Compound("parent", [Var "X"; Var "Y"])]
    let result = renderClause c
    hasSubstring "yield"                                   result
    hasSubstring "|-"                                      result
    hasSubstring "\"ancestor\" /@ [Var \"X\"; Var \"Y\"]" result
    hasSubstring "\"parent\" /@ [Var \"X\"; Var \"Y\"]"   result

// ── renderDatabase ────────────────────────────────────────────────────────────

[<Fact>]
let ``renderDatabase contains module declaration`` () =
    let db = parseString "foo(a)."
    let code = renderDatabase "MyModule" "" db
    hasSubstring "module MyModule" code

[<Fact>]
let ``renderDatabase opens required namespaces`` () =
    let db = parseString "foo(a)."
    let code = renderDatabase "MyModule" "" db
    hasSubstring "open FsLogical.Term" code
    hasSubstring "open FsLogical.DSL"  code

[<Fact>]
let ``renderDatabase contains db binding`` () =
    let db = parseString "foo(a)."
    let code = renderDatabase "MyModule" "" db
    hasSubstring "let db : Database =" code
    hasSubstring "logicDB {"           code

[<Fact>]
let ``renderDatabase includes input path in comment when provided`` () =
    let db = parseString "foo(a)."
    let code = renderDatabase "MyModule" "my_file.pl" db
    hasSubstring "my_file.pl" code

[<Fact>]
let ``renderDatabase includes prologList helper when lists present`` () =
    let db = parseString "colors([red,green,blue])."
    let code = renderDatabase "MyModule" "" db
    hasSubstring "prologList"             code
    hasSubstring "let private prologList" code

[<Fact>]
let ``renderDatabase omits prologList helper when no lists present`` () =
    let db = parseString "parent(tom, bob)."
    let code = renderDatabase "MyModule" "" db
    notHasSubstring "prologList" code

[<Fact>]
let ``renderDatabase defaults module name to GeneratedDb when empty`` () =
    let db = parseString "foo(a)."
    let code = renderDatabase "" "" db
    hasSubstring "module GeneratedDb" code

[<Fact>]
let ``renderDatabase round-trips simple fact DB`` () =
    let src  = "parent(tom, bob).\nparent(tom, liz)."
    let db   = parseString src
    let code = renderDatabase "TestDb" "" db
    hasSubstring "atom \"tom\""   code
    hasSubstring "atom \"bob\""   code
    hasSubstring "atom \"liz\""   code
    hasSubstring "\"parent\" /@ " code
    hasSubstring "yield fact"     code

[<Fact>]
let ``renderDatabase round-trips rule`` () =
    let src  = "ancestor(X,Y) :- parent(X,Y)."
    let db   = parseString src
    let code = renderDatabase "TestDb" "" db
    hasSubstring "\"ancestor\" /@ " code
    hasSubstring " |- "             code
    hasSubstring "Var \"X\""        code
    hasSubstring "Var \"Y\""        code

[<Fact>]
let ``renderDatabase handles integers and floats`` () =
    let src  = "age(alice, 30).\nweight(bob, 72.5)."
    let db   = parseString src
    let code = renderDatabase "TestDb" "" db
    hasSubstring "Integer 30" code
    hasSubstring "Float "     code

[<Fact>]
let ``renderDatabase handles list facts`` () =
    let db   = parseString "colors([red, green, blue])."
    let code = renderDatabase "TestDb" "" db
    hasSubstring "prologList [atom \"red\"; atom \"green\"; atom \"blue\"]" code
