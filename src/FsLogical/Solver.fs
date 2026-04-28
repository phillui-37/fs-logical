module FsLogical.Solver

open FsLogical.Term
open FsLogical.Unification

/// Counter for generating unique variable names (thread-safe via Interlocked).
let private initialCount = 0L
let mutable private counter = initialCount

/// Allocate a fresh integer stamp for variable renaming.
let private freshStamp () : int64 =
    System.Threading.Interlocked.Increment(&counter)

/// Rename all variables in a clause to fresh names, preventing variable capture
/// when the same rule is applied multiple times in a derivation.
let private freshenClause (stamp: int64) (clause: Clause) : Clause =
    let rename name = sprintf "%s_%d" name stamp

    let rec renameTerm term =
        match term with
        | Var v -> Var (rename v)
        | Compound(name, args) -> normalize (Compound(name, List.map renameTerm args))
        | other -> other

    { Head = renameTerm clause.Head
      Body = List.map renameTerm clause.Body }

type SolverOptions = {
    MaxDepth: int
}

let private defaultMaxDepth = 1_000

let defaultSolverOptions = { MaxDepth = defaultMaxDepth }

let private validateOptions (options: SolverOptions) =
    if options.MaxDepth < 0 then
        invalidArg (nameof options.MaxDepth) "MaxDepth must be non-negative."

let private termKey (term: Term) : (string * int) option =
    match normalize term with
    | Atom name -> Some(name, 0)
    | Compound(name, args) -> Some(name, List.length args)
    | _ -> None

/// Retrieve all clauses from the database whose head functor/arity matches the goal.
/// Returns [] immediately for non-predicate goals (variables, integers, floats).
let private matchingClauses (db: Database) (goal: Term) : Clause list =
    match termKey goal with
    | Some goalKey ->
        db.Clauses
        |> List.filter (fun clause -> termKey clause.Head = Some goalKey)
    | None -> []  // variables and numbers never match any clause head

/// Resolve a list of goals against the database, yielding each solution substitution.
/// Uses lazy F# sequences for implicit backtracking.
let rec private resolveGoals (db: Database) (goals: Term list) (subst: Substitution) (remainingDepth: int) : seq<Substitution> =
    seq {
        match goals with
        | [] -> yield subst  // all goals satisfied → one solution
        | _ when remainingDepth = 0 -> ()
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
                    yield! resolveGoals db newGoals subst' (remainingDepth - 1)
    }

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
    /// Original clause order retained for diagnostics and iteration.
    Clauses: Clause list
    Index: Map<(string * int), Clause list>
}

/// Build an IndexedDatabase from a regular Database.
/// Groups clauses by (functor, arity) for O(log n) lookup instead of O(n) scan.
let indexDatabase (db: Database) : IndexedDatabase =
    let index =
        db.Clauses
        |> List.choose (fun clause ->
            termKey clause.Head
            |> Option.map (fun key -> key, clause))
        |> List.groupBy fst
        |> List.map (fun (key, entries) -> key, (entries |> List.map snd))
        |> Map.ofList
    { Clauses = db.Clauses; Index = index }

/// Retrieve matching clauses from an IndexedDatabase using the index.
let private matchingClausesIndexed (idb: IndexedDatabase) (goal: Term) : Clause list =
    match termKey goal with
    | Some key -> idb.Index |> Map.tryFind key |> Option.defaultValue []
    | None -> []

let rec private resolveGoalsIndexed (idb: IndexedDatabase) (goals: Term list) (subst: Substitution) (remainingDepth: int) : seq<Substitution> =
    seq {
        match goals with
        | [] -> yield subst
        | _ when remainingDepth = 0 -> ()
        | goal :: rest ->
            let resolvedGoal = applySubst subst goal
            for clause in matchingClausesIndexed idb resolvedGoal do
                let stamp = freshStamp ()
                let fresh = freshenClause stamp clause
                match unify resolvedGoal fresh.Head subst with
                | None -> ()
                | Some subst' ->
                    let newGoals = fresh.Body @ rest
                    yield! resolveGoalsIndexed idb newGoals subst' (remainingDepth - 1)
    }

/// Solve a single goal against the database.
/// Returns a lazy sequence of substitutions (one per solution).
/// The returned sequence should not be enumerated concurrently from multiple threads.
let solveWithOptions (options: SolverOptions) (db: Database) (goal: Term) : seq<Substitution> =
    validateOptions options
    resolveGoals db [goal] Subst.empty options.MaxDepth

/// Solve a conjunction of goals against the database.
/// Returns a lazy sequence of substitutions (one per solution).
/// The returned sequence should not be enumerated concurrently from multiple threads.
let solveAllWithOptions (options: SolverOptions) (db: Database) (goals: Term list) : seq<Substitution> =
    validateOptions options
    resolveGoals db goals Subst.empty options.MaxDepth

/// Solve a single goal against the database.
/// Returns a lazy sequence of substitutions (one per solution).
/// The returned sequence should not be enumerated concurrently from multiple threads.
let solve (db: Database) (goal: Term) : seq<Substitution> =
    solveWithOptions defaultSolverOptions db goal

/// Solve a conjunction of goals against the database.
/// Returns a lazy sequence of substitutions (one per solution).
/// The returned sequence should not be enumerated concurrently from multiple threads.
let solveAll (db: Database) (goals: Term list) : seq<Substitution> =
    solveAllWithOptions defaultSolverOptions db goals

/// Solve a single goal and lazily cap the number of solutions.
let solveN (n: int) (db: Database) (goal: Term) : seq<Substitution> =
    solve db goal |> Seq.truncate n

/// Solve a single goal against an IndexedDatabase.
/// The returned sequence should not be enumerated concurrently from multiple threads.
let solveIndexedWithOptions (options: SolverOptions) (idb: IndexedDatabase) (goal: Term) : seq<Substitution> =
    validateOptions options
    resolveGoalsIndexed idb [goal] Subst.empty options.MaxDepth

/// Solve a conjunction of goals against an IndexedDatabase.
/// The returned sequence should not be enumerated concurrently from multiple threads.
let solveAllIndexedWithOptions (options: SolverOptions) (idb: IndexedDatabase) (goals: Term list) : seq<Substitution> =
    validateOptions options
    resolveGoalsIndexed idb goals Subst.empty options.MaxDepth

/// Solve a single goal against an IndexedDatabase.
let solveIndexed (idb: IndexedDatabase) (goal: Term) : seq<Substitution> =
    solveIndexedWithOptions defaultSolverOptions idb goal

/// Solve a conjunction of goals against an IndexedDatabase.
let solveAllIndexed (idb: IndexedDatabase) (goals: Term list) : seq<Substitution> =
    solveAllIndexedWithOptions defaultSolverOptions idb goals
