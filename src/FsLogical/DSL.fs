/// F# DSL for building logic databases and queries in a Prolog-like style.
/// Provides operators, computation expressions, and active patterns for
/// ergonomic logical programming.
module FsLogical.DSL

open FSharpx.Collections
open FsLogical.Term
open FsLogical.Unification
open FsLogical.Solver

// ── Term construction helpers ──────────────────────────────────────────────

let mutable private wildCounter = 0L

/// Create an anonymous wildcard variable. Each call returns a distinct variable,
/// so all wildcards in a query are independent of each other.
let wild () =
    let n = System.Threading.Interlocked.Increment(&wildCounter)
    Var $"_w{n}"

// ── Operators re-exported for convenience ────────────────────────────────

/// Build a Compound term:  "parent" /@ [atom "john"; atom "mary"]
let inline (/@ ) (name: string) (args: Term list) = normalize (Compound(name, args))

/// Build a Rule clause:   head |- [body1; body2]
let inline (|-) head body = rule head body

// ── DatabaseBuilder computation expression ───────────────────────────────

/// Computation expression for building a Database in a readable block.
/// Uses DList internally for O(1) Combine (append), converting to a list in Run.
///
/// Example:
/// ```fsharp
/// let family = logicDB {
///     yield fact ("parent" /@ [atom "tom"; atom "bob"])
///     yield fact ("parent" /@ [atom "tom"; atom "liz"])
///     yield ("ancestor" /@ [Var "X"; Var "Y"]) |- ["parent" /@ [Var "X"; Var "Y"]]
/// }
/// ```
type DatabaseBuilder() =
    member _.Yield(clause: Clause) : DList<Clause> = DList.singleton clause
    member _.YieldFrom(clauses: Clause list) : DList<Clause> = DList.ofSeq clauses
    member _.Combine(a: DList<Clause>, b: DList<Clause>) : DList<Clause> = DList.append a b
    // Intentionally eager: logicDB builds a fully materialised database immediately.
    member _.Delay(f: unit -> DList<Clause>) : DList<Clause> = f ()
    member _.Zero() : DList<Clause> = DList.empty
    member _.Run(dl: DList<Clause>) : Database = { Clauses = DList.toList dl }

/// The `logicDB` computation expression builder.
let logicDB = DatabaseBuilder()

// ── Query / solver helpers ────────────────────────────────────────────────

/// Query a database with a single goal; returns a lazy sequence of substitutions.
let query (db: Database) (goal: Term) : seq<Substitution> =
    solve db goal

/// Query a database with a conjunction of goals.
let queryAll (db: Database) (goals: Term list) : seq<Substitution> =
    solveAll db goals

/// Extract the (fully-applied) value of variable `name` from a substitution.
let valueOf (name: string) (subst: Substitution) : Term =
    applySubst subst (Var name)

// ── LogicQueryBuilder computation expression ──────────────────────────────

/// Computation expression that threads substitutions through a sequence of
/// goal queries, enabling a monadic query style.
///
/// Example:
/// ```fsharp
/// let results =
///     logicQuery {
///         let! sub  = query family ("parent" /@ [Var "X"; atom "bob"])
///         let! sub2 = query family ("parent" /@ [Var "Y"; valueOf "X" sub |> fun p -> p])
///         return valueOf "X" sub, valueOf "Y" sub2
///     }
/// ```
type LogicQueryBuilder() =
    member _.Bind(solutions: seq<Substitution>, f: Substitution -> seq<'b>) : seq<'b> =
        Seq.collect f solutions

    member _.Return(value: 'a) : seq<'a> =
        Seq.singleton value

    member _.ReturnFrom(s: seq<'a>) : seq<'a> = s

    member _.Zero() : seq<'a> = Seq.empty

    member _.Yield(value: 'a) : seq<'a> = Seq.singleton value

    member _.YieldFrom(s: seq<'a>) : seq<'a> = s

    member _.Combine(a: seq<'a>, b: seq<'a>) : seq<'a> = Seq.append a b

    member _.For(values: seq<'a>, f: 'a -> seq<'b>) : seq<'b> =
        Seq.collect f values

    member _.Delay(f: unit -> seq<'a>) : seq<'a> = Seq.delay f

/// The `logicQuery` computation expression builder.
let logicQuery = LogicQueryBuilder()

// ── Prolog-style query operators ─────────────────────────────────────────

/// Prolog-style infix query operator.
/// <c>db ?- goals</c> runs the conjunction <c>goals</c> against <c>db</c> and
/// returns a lazy sequence of satisfying substitutions — directly analogous to
/// the Prolog top-level <c>?- g1, g2.</c>
///
/// Examples:
/// <code>
/// // ?-a(X),b(X).  → find X satisfying both a and b
/// family ?- ["a" /@ [Var "X"]; "b" /@ [Var "X"]]
///
/// // ?-parent(tom,X).  → find X such that parent(tom,X)
/// family ?- ["parent" /@ [atom "tom"; Var "X"]]
///
/// // ?-parent(tom,bob).  → check ground fact (use `ask` for boolean)
/// family ?- ["parent" /@ [atom "tom"; atom "bob"]]
/// </code>
let inline (?-) (db: Database) (goals: Term list) : seq<Substitution> =
    queryAll db goals

/// Return <c>true</c> when the conjunction of goals has at least one solution —
/// analogous to using <c>?-</c> as a pure boolean check in Prolog.
///
/// Example:
/// <code>
/// // ?-parent(tom,bob).  → is bob a child of tom?
/// ask family ["parent" /@ [atom "tom"; atom "bob"]]  // true
/// </code>
let ask (db: Database) (goals: Term list) : bool =
    queryAll db goals |> Seq.isEmpty |> not

/// Return all values bound to <c>varName</c> across every solution of the
/// conjunction — analogous to Prolog's <c>findall/3</c> for a single variable.
///
/// Example:
/// <code>
/// // ?-parent(tom,X).  → what children does tom have?
/// findAll "X" family ["parent" /@ [atom "tom"; Var "X"]]
/// // → [Atom "bob"; Atom "liz"]
/// </code>
let findAll (varName: string) (db: Database) (goals: Term list) : Term list =
    queryAll db goals |> Seq.map (valueOf varName) |> Seq.toList

/// Return the value of <c>varName</c> in the first solution, or <c>None</c> if
/// there are no solutions.
///
/// Example:
/// <code>
/// // ?-parent(tom,X).  → first child of tom
/// findFirst "X" family ["parent" /@ [atom "tom"; Var "X"]]
/// // → Some (Atom "bob")
/// </code>
let findFirst (varName: string) (db: Database) (goals: Term list) : Term option =
    queryAll db goals |> Seq.tryHead |> Option.map (valueOf varName)

// ── Active patterns ──────────────────────────────────────────────────────

/// Active pattern: match a solution in which the given variable is bound.
/// Usage:  match sub with BoundVar "X" t -> ...
let (|BoundVar|_|) (varName: string) (subst: Substitution) =
    match applySubst subst (Var varName) with
    | Var _ -> None
    | t -> Some t

/// Active pattern: match a solution in which the given variable is unbound.
let (|UnboundVar|_|) (varName: string) (subst: Substitution) =
    match applySubst subst (Var varName) with
    | Var _ -> Some ()
    | _ -> None

/// Active pattern: deconstruct a compound term.
/// Usage:  match term with Pred "parent" [a; b] -> ...
let (|Pred|_|) (name: string) (term: Term) =
    match normalize term with
    | Atom n when n = name -> Some []
    | Compound(n, args) when n = name -> Some args
    | _ -> None
