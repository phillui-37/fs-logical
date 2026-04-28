# Code Review – FsLogical

> Branch: `review-and-benchmarks`  
> Reviewed files: `Term.fs`, `Unification.fs`, `Solver.fs`, `DSL.fs`

---

## Potential Issues

### 1. Global mutable counters shared across all calls (Solver.fs · DSL.fs)

```fsharp
// Solver.fs
let mutable private counter = initialCount

// DSL.fs
let mutable private wildCounter = 0
```

Both counters are module-level mutable state.  `Interlocked.Increment` makes
the increment itself atomic, but the *counter value* can overflow to
`Int32.MinValue` if the process runs long enough (unlikely in practice but
worth acknowledging).  More importantly, the counters are **never reset**
between test runs; this is benign for correctness (stamps only need to be
unique, not sequential from zero) but can make debugging harder.

**Recommendation:** Consider using `int64` for the counter, or document the
overflow risk explicitly.

---

### 2. `Subst.tryFind` performs two hash-map lookups (Term.fs)

```fsharp
let tryFind (k: string) (s: Substitution) : Term option =
    if s.ContainsKey(k) then Some s.[k] else None
```

`ContainsKey` traverses the hash trie once and the indexer `s.[k]` traverses
it a second time.  `PersistentHashMap` does not expose a `TryGetValue`-style
API, so this is the best the current abstraction allows—but the comment
calling it "single-pass" is inaccurate.

**Recommendation:** Update the comment to say "two lookups" or wrap the
indexer call in a try/catch to avoid the double traversal.

---

### 3. Occurs check makes unification O(n²) in term size (Unification.fs)

```fsharp
let rec unify ... =
    ...
    | Var v, t | t, Var v ->
        if occursIn v t subst then None   // walks the entire sub-term
        else Some (Subst.add v t subst)
```

`occursIn` walks the full term each time a variable binding is attempted.
For a compound with *k* arguments each containing *m* sub-terms, this is
O(k·m) per binding.  Real Prolog systems omit the occurs check by default
(`unify_without_occurs_check/2`) and offer it only on demand.

**Recommendation:** Add a `unifyNoOccursCheck` variant, or make the occurs
check optional via a parameter/flag.

---

### 4. `matchingClauses` does a full O(n) linear scan (Solver.fs)

```fsharp
let private matchingClauses (db: Database) (goal: Term) : Clause list =
    db.Clauses
    |> List.filter (fun clause -> headKey = goalKey)
```

Every goal resolution step scans all clauses in the database.  `IndexedDatabase`
fixes this for the indexed path, but `solve` / `solveAll` still use the linear
path.

**Recommendation:** Either deprecate the non-indexed `Database` type and
always require `IndexedDatabase`, or build the index lazily on first use via a
`lazy` value inside `Database`.

---

### 5. Dead / unreachable match arm in `matchingClauses` (Solver.fs)

```fsharp
| Atom _ | Compound _ ->
    let goalKey =
        match goal with
        | Atom name -> (name, 0)
        | Compound(name, args) -> (name, List.length args)
        | _ -> ("", -1)   // <-- unreachable; outer match already filtered
```

The `| _ -> ("", -1)` branch can never be reached.

**Recommendation:** Remove the dead branch or add a `failwith` to make it a
compile-time exhaustiveness marker.

---

### 6. `IndexedDatabase` redundantly stores the full clause list (Solver.fs)

```fsharp
type IndexedDatabase = {
    Clauses: Clause list   // unused in resolveGoalsIndexed
    Index: Map<(string * int), Clause list>
}
```

`resolveGoalsIndexed` never reads `Clauses`; it is only provided for external
introspection.  This doubles the memory used by the clause list.

**Recommendation:** Document clearly that `Clauses` is for diagnostics/
iteration only, or remove it and derive it from the index when needed.

---

### 7. `IndexedDatabase.Index` uses `Map` (O(log n) lookup) (Solver.fs)

```fsharp
Index: Map<(string * int), Clause list>
```

F#'s `Map` is a balanced binary tree with O(log n) lookup.  Using
`Dictionary<(string * int), Clause list>` would give O(1) average lookup.
For a typical Prolog database the number of distinct functor/arity keys is
small, so the difference is minimal, but it is worth noting given the stated
goal of "O(log n) lookup instead of O(n) scan".

**Recommendation:** Swap to `System.Collections.Generic.Dictionary` or a
`readOnlyDict` for O(1) amortised lookup.

---

### 8. `Compound("foo", [])` and `Atom "foo"` are semantically conflated in the index (Solver.fs · Unification.fs)

In `matchingClauses` a `Compound("foo", [])` goal produces key `("foo", 0)`,
the same as `Atom "foo"`.  However `unify (Atom "foo") (Compound("foo", []))`
returns `None` because the outer pattern-match falls to `| _ -> None`.
This means indexing can return candidates that unification will then reject—
a silent waste of work, but also a conceptual inconsistency.

**Recommendation:** Normalise zero-argument compounds to `Atom` in the smart
constructors, or explicitly reject `Compound(_, [])` in the index key
computation.

---

### 9. No depth limit or cycle detection in the resolver (Solver.fs)

A left-recursive rule such as  
`ancestor(X,Y) :- ancestor(X,Z), parent(Z,Y)`  
will cause infinite recursion in `resolveGoals`, consuming stack until a
`StackOverflowException` is raised (unrecoverable in .NET).

**Recommendation:** Add an optional depth-limit parameter to `solve` /
`solveAll`, or document the left-recursion restriction prominently.

---

### 10. `DatabaseBuilder.Delay` is eager (DSL.fs)

```fsharp
member _.Delay(f: unit -> DList<Clause>) : DList<Clause> = f ()
```

`Delay` is invoked synchronously at construction time, so exceptions inside
a `logicDB { … }` block propagate immediately.  This is correct behaviour for
a *builder* (you want the DB fully constructed before use), but means
conditional clauses (`if cond then yield …`) are evaluated eagerly.

**Recommendation:** This is by design for a builder CE; add a comment to
clarify intentional eager evaluation.

---

### 11. `LogicQueryBuilder` missing `For` member (DSL.fs)

The computation expression does not implement `For`, which prevents using
`for x in collection do …` syntax inside a `logicQuery { … }` block.

**Recommendation:** Add  
```fsharp
member _.For(s: seq<'a>, f: 'a -> seq<'b>) : seq<'b> = Seq.collect f s
```

---

## Improvement Points

| # | Area | Suggestion |
|---|------|-----------|
| A | **Performance** | Make `IndexedDatabase` the primary (or only) path; build the index lazily inside `Database` via `Lazy<Map<...>>` to avoid a separate construction step. |
| B | **Performance** | Replace `Map<(string * int), Clause list>` with `Dictionary` for O(1) functor index lookup. |
| C | **Performance** | Offer `unifyNoOccursCheck` for trusted/generated code paths where circular terms are impossible. |
| D | **API ergonomics** | Add `For` to `LogicQueryBuilder` so `for` loops work inside `logicQuery { … }`. |
| E | **API ergonomics** | Expose `solveN (n: int)` to take the first N solutions without forcing a `Seq.truncate`. |
| F | **Correctness / safety** | Add a `maxDepth` parameter to `resolveGoals` with a sensible default (e.g., 1 000) and a `SolverOptions` record to package it alongside future flags. |
| G | **Correctness** | Normalise `Compound(name, [])` to `Atom name` in the `/@` operator or in a dedicated `normalize` function to eliminate the index/unification mismatch. |
| H | **Diagnostics** | Add `Term.isGround : Term -> Substitution -> bool` — a frequently needed predicate when extracting results. |
| I | **Diagnostics** | Add `Substitution.toMap : Substitution -> Map<string, Term>` for easier inspection and pretty-printing in tests. |
| J | **Code clarity** | Remove the unreachable `| _ -> ("", -1)` match arm in `matchingClauses`. |
| K | **Code clarity** | Fix the inaccurate "single-pass" comment in `Subst.tryFind`. |
| L | **Thread safety doc** | Document that `solve` / `solveAll` return lazy `seq<Substitution>` values that are **not** thread-safe to iterate concurrently from multiple threads. |

---

## Benchmark & Stress Test Summary

Two new test/tooling artefacts were added on this branch:

### `tests/FsLogical.Tests/StressTests.fs` (20 new xUnit tests)

Covers:
- **Large flat databases** (up to 10 000 facts): full enumeration, first-result
  short-circuit, and ground-term lookup via both the linear and indexed paths.
- **Deep recursive chains** (ancestor up to depth 20): all-descendants query,
  ground true/false queries, non-ancestor negative case.
- **Wide fan-out** (up to 500 children, 2 500-element cross-products).
- **Unification under load**: 500-arity flat compounds, fail-fast on mismatch,
  200-element substitution chain walk, 300-variable `applySubst`.
- **Concurrency**: 8 parallel `Task`-based calls to `solve` and `solveIndexed`
  verifying independent results.

### `tests/FsLogical.Benchmarks/` (BenchmarkDotNet project)

Five benchmark classes targeting the performance-critical hot-spots identified
in the review:

| Class | What it measures |
|-------|-----------------|
| `UnificationBenchmarks` | Ground match, variable binding, and `occursIn` on flat compounds of arity 10 / 100 / 500 |
| `ApplySubstBenchmarks` | `walk` through a substitution chain; `applySubst` on wide compounds |
| `SolverBenchmarks` | Full enumeration and first-result on fan-out DBs of 50 / 200 / 1 000 facts; `indexDatabase` construction cost; non-indexed vs indexed comparison |
| `AncestorBenchmarks` | All-descendants and ground queries on recursive ancestor chains of depth 5 / 10 / 20; non-indexed vs indexed comparison |
| `SubstitutionBenchmarks` | Incremental `Subst.add`, `Subst.tryFind`, and bulk `Subst.ofSeq` at sizes 10 / 100 / 500 |

Run benchmarks in Release mode:
```bash
dotnet run --project tests/FsLogical.Benchmarks -c Release -- --filter '*'
```
