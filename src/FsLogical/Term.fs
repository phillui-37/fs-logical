module FsLogical.Term

open FSharpx.Collections

/// A logical term in the Prolog-like framework.
/// Terms can be atoms, numbers, variables, or compound structures.
type Term =
    /// An atomic symbol, e.g. 'john', 'true', '[]'
    | Atom of string
    /// An integer literal
    | Integer of int
    /// A floating-point literal
    | Float of float
    /// A logic variable (conventionally uppercase), e.g. Var "X"
    | Var of string
    /// A compound term: functor name + argument list, e.g. parent(john, mary)
    | Compound of Name: string * Args: Term list

    override this.ToString() =
        match this with
        | Atom s -> s
        | Integer n -> string n
        | Float f -> string f
        | Var s -> s
        | Compound(name, []) -> name
        | Compound(name, args) ->
            let argsStr = args |> List.map string |> String.concat ", "
            sprintf "%s(%s)" name argsStr

/// A logic clause: a fact (head with no body) or a rule (head :- body).
type Clause = {
    Head: Term
    Body: Term list
}

/// A substitution: a persistent hash map from variable names to terms.
/// Uses PersistentHashMap for O(1) average lookup vs O(log n) for Map.
type Substitution = PersistentHashMap<string, Term>

/// A knowledge base: an ordered list of clauses.
type Database = {
    Clauses: Clause list
}

/// Helper module for working with Substitution values.
module Subst =
    /// The empty substitution.
    let empty : Substitution = PersistentHashMap.empty

    /// Add a binding to a substitution.
    let add (k: string) (v: Term) (s: Substitution) : Substitution = s.Add(k, v)

    /// Try to find a binding in a substitution.
    /// PersistentHashMap exposes no TryGetValue; ContainsKey + indexer means two lookups
    /// with the current API surface.
    let tryFind (k: string) (s: Substitution) : Term option =
        if s.ContainsKey(k) then Some s.[k] else None

    /// Create a substitution from a sequence of key-value pairs.
    let ofSeq (pairs: seq<string * Term>) : Substitution = PersistentHashMap.ofSeq pairs

    /// Convert a substitution into an immutable F# Map for inspection.
    let toMap (s: Substitution) : Map<string, Term> =
        s |> Map.ofSeq

    /// Return the number of bindings.
    let count (s: Substitution) : int = s.Length

    /// Return true if the substitution has no bindings.
    /// PersistentHashMap provides no dedicated IsEmpty property; Length is the canonical check.
    let isEmpty (s: Substitution) : bool = s.Length = 0

/// Smart constructor for a fact (a clause with no body).
let fact head = { Head = head; Body = [] }

/// Smart constructor for a rule (head :- body).
let rule head body = { Head = head; Body = body }

/// Smart constructor for a database.
let database clauses = { Clauses = clauses }

/// Normalise term representations used by the public DSL.
/// Zero-argument compounds are treated as atoms.
let rec normalize (term: Term) : Term =
    match term with
    | Compound(name, []) -> Atom name
    | Compound(name, args) -> Compound(name, args |> List.map normalize)
    | other -> other

/// Return true when the term is ground under the supplied substitution.
let rec isGround (term: Term) (subst: Substitution) : bool =
    match normalize term with
    | Var v ->
        match Subst.tryFind v subst with
        | Some t -> isGround t subst
        | None -> false
    | Atom _ | Integer _ | Float _ -> true
    | Compound(_, args) -> args |> List.forall (fun arg -> isGround arg subst)

/// Inline operator: "functor" /@ [arg1; arg2] builds a Compound term.
let inline (/@) (name: string) (args: Term list) = normalize (Compound(name, args))

/// Inline operator: head |- body builds a Rule clause.
let inline (|-) head body = rule head body

/// Shorthand for creating an Atom.
let inline atom (s: string) = Atom s

/// Shorthand for creating an Integer term.
let inline int' (n: int) = Integer n

/// Shorthand for creating a Float term.
let inline float' (f: float) = Float f

/// Shorthand for creating a Var term.
let inline var (s: string) = Var s
