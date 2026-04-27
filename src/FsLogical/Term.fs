module FsLogical.Term

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

/// A substitution: a mapping from variable names to terms.
type Substitution = Map<string, Term>

/// A knowledge base: an ordered list of clauses.
type Database = {
    Clauses: Clause list
}

/// Smart constructor for a fact (a clause with no body).
let fact head = { Head = head; Body = [] }

/// Smart constructor for a rule (head :- body).
let rule head body = { Head = head; Body = body }

/// Smart constructor for a database.
let database clauses = { Clauses = clauses }

/// Inline operator: "functor" /@ [arg1; arg2] builds a Compound term.
let inline (/@) (name: string) (args: Term list) = Compound(name, args)

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
