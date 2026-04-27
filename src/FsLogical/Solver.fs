module FsLogical.Solver

open FsLogical.Term
open FsLogical.Unification

/// Counter for generating unique variable names (thread-safe via Interlocked).
[<Literal>]
let private initialCount = 0
let mutable private counter = initialCount

/// Allocate a fresh integer stamp for variable renaming.
let private freshStamp () : int =
    System.Threading.Interlocked.Increment(&counter)

/// Rename all variables in a clause to fresh names, preventing variable capture
/// when the same rule is applied multiple times in a derivation.
let private freshenClause (stamp: int) (clause: Clause) : Clause =
    let rename name = sprintf "%s_%d" name stamp

    let rec renameTerm term =
        match term with
        | Var v -> Var (rename v)
        | Compound(name, args) -> Compound(name, List.map renameTerm args)
        | other -> other

    { Head = renameTerm clause.Head
      Body = List.map renameTerm clause.Body }

/// Retrieve all clauses from the database whose head functor/arity matches the goal.
/// Returns [] immediately for non-predicate goals (variables, integers, floats).
let private matchingClauses (db: Database) (goal: Term) : Clause list =
    match goal with
    | Atom _ | Compound _ ->
        let goalKey =
            match goal with
            | Atom name -> (name, 0)
            | Compound(name, args) -> (name, List.length args)
            | _ -> ("", -1)
        db.Clauses
        |> List.filter (fun clause ->
            let headKey =
                match clause.Head with
                | Atom name -> (name, 0)
                | Compound(name, args) -> (name, List.length args)
                | _ -> ("", -2)
            headKey = goalKey)
    | _ -> []  // variables and numbers never match any clause head

/// Resolve a list of goals against the database, yielding each solution substitution.
/// Uses lazy F# sequences for implicit backtracking.
let rec private resolveGoals (db: Database) (goals: Term list) (subst: Substitution) : seq<Substitution> =
    seq {
        match goals with
        | [] -> yield subst  // all goals satisfied → one solution
        | goal :: rest ->
            let resolvedGoal = applySubst subst goal
            for clause in matchingClauses db resolvedGoal do
                let stamp = freshStamp ()
                let fresh = freshenClause stamp clause
                match unify resolvedGoal fresh.Head subst with
                | None -> ()  // unification failed, backtrack
                | Some subst' ->
                    // Prepend the body of the matched clause to the remaining goals
                    let newGoals = fresh.Body @ rest
                    yield! resolveGoals db newGoals subst'
    }

/// Solve a single goal against the database.
/// Returns a lazy sequence of substitutions (one per solution).
let solve (db: Database) (goal: Term) : seq<Substitution> =
    resolveGoals db [goal] Subst.empty

/// Solve a conjunction of goals against the database.
/// Returns a lazy sequence of substitutions (one per solution).
let solveAll (db: Database) (goals: Term list) : seq<Substitution> =
    resolveGoals db goals Subst.empty

/// Convenience: extract the value of a named variable from a substitution.
/// Returns None if the variable is unbound.
let lookup (varName: string) (subst: Substitution) : Term option =
    let term = applySubst subst (Var varName)
    match term with
    | Var _ -> None  // still unbound
    | t -> Some t

/// Convenience: extract and fully ground a variable value (applySubst already handles chains).
let ground (varName: string) (subst: Substitution) : Term =
    applySubst subst (Var varName)

// ── Indexed Database ─────────────────────────────────────────────────────

/// An indexed database for faster clause lookup by functor/arity key.
type IndexedDatabase = {
    Clauses: Clause list
    Index: Map<(string * int), Clause list>
}

/// Build an IndexedDatabase from a regular Database.
/// Groups clauses by (functor, arity) for O(log n) lookup instead of O(n) scan.
let indexDatabase (db: Database) : IndexedDatabase =
    let index =
        db.Clauses
        |> List.groupBy (fun clause ->
            match clause.Head with
            | Atom name -> (name, 0)
            | Compound(name, args) -> (name, List.length args)
            | _ -> ("", -2))
        |> Map.ofList
    { Clauses = db.Clauses; Index = index }

/// Retrieve matching clauses from an IndexedDatabase using the index.
let private matchingClausesIndexed (idb: IndexedDatabase) (goal: Term) : Clause list =
    match goal with
    | Atom name ->
        idb.Index |> Map.tryFind (name, 0) |> Option.defaultValue []
    | Compound(name, args) ->
        idb.Index |> Map.tryFind (name, List.length args) |> Option.defaultValue []
    | _ -> []

let rec private resolveGoalsIndexed (idb: IndexedDatabase) (goals: Term list) (subst: Substitution) : seq<Substitution> =
    seq {
        match goals with
        | [] -> yield subst
        | goal :: rest ->
            let resolvedGoal = applySubst subst goal
            for clause in matchingClausesIndexed idb resolvedGoal do
                let stamp = freshStamp ()
                let fresh = freshenClause stamp clause
                match unify resolvedGoal fresh.Head subst with
                | None -> ()
                | Some subst' ->
                    let newGoals = fresh.Body @ rest
                    yield! resolveGoalsIndexed idb newGoals subst'
    }

/// Solve a single goal against an IndexedDatabase.
let solveIndexed (idb: IndexedDatabase) (goal: Term) : seq<Substitution> =
    resolveGoalsIndexed idb [goal] Subst.empty

/// Solve a conjunction of goals against an IndexedDatabase.
let solveAllIndexed (idb: IndexedDatabase) (goals: Term list) : seq<Substitution> =
    resolveGoalsIndexed idb goals Subst.empty
