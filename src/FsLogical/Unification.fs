module FsLogical.Unification

open FsLogical.Term

/// Walk a variable through a substitution chain to find its ultimate binding.
let rec walk (term: Term) (subst: Substitution) : Term =
    match term with
    | Var v ->
        match Subst.tryFind v subst with
        | Some t -> walk t subst
        | None -> Var v
    | Compound(name, []) -> Atom name  // normalise zero-arity compounds
    | _ -> term

/// Apply a substitution deeply to a term, replacing all bound variables.
/// Raises <see cref="System.InvalidOperationException"/> when the term nesting depth
/// exceeds <see cref="maxTermDepth"/>.
let applySubst (subst: Substitution) (term: Term) : Term =
    let rec go depth t =
        if depth > maxTermDepth then
            invalidOp $"Term nesting depth exceeds the maximum of {maxTermDepth}. Reduce compound term depth to avoid stack overflow."
        let walked = walk t subst
        match walked with
        | Var _ | Atom _ | Integer _ | Float _ -> walked
        | Compound(name, []) -> Atom name  // normalise zero-arity
        | Compound(name, args) ->
            Compound(name, args |> List.map (go (depth + 1)))
    go 0 term

/// Occurs check: does variable 'v' appear in term 't' under substitution?
/// Raises <see cref="System.InvalidOperationException"/> when the term nesting depth
/// exceeds <see cref="maxTermDepth"/>.
let occursIn (v: string) (term: Term) (subst: Substitution) : bool =
    let rec go depth t =
        if depth > maxTermDepth then
            invalidOp $"Term nesting depth exceeds the maximum of {maxTermDepth}. Reduce compound term depth to avoid stack overflow."
        let walked = walk t subst
        match walked with
        | Var w -> v = w
        | Atom _ | Integer _ | Float _ -> false
        | Compound(_, args) -> args |> List.exists (fun a -> go (depth + 1) a)
    go 0 term

let rec private unifyCore (checkOccurs: bool) (t1: Term) (t2: Term) (subst: Substitution) : Substitution option =
    let t1' = walk t1 subst
    let t2' = walk t2 subst
    match t1', t2' with
    | _ when t1' = t2' -> Some subst
    | Var v, t | t, Var v ->
        if checkOccurs && occursIn v t subst then None
        else Some (Subst.add v t subst)
    | Compound(n1, args1), Compound(n2, args2) when n1 = n2 && List.length args1 = List.length args2 ->
        List.fold
            (fun acc (a1, a2) ->
                match acc with
                | None -> None
                | Some s -> unifyCore checkOccurs a1 a2 s)
            (Some subst)
            (List.zip args1 args2)
    | _ -> None

/// Unify two terms under the given substitution.
/// Returns Some extended substitution on success, None on failure.
let rec unify (t1: Term) (t2: Term) (subst: Substitution) : Substitution option =
    unifyCore true t1 t2 subst

/// Unify two terms starting with an empty substitution.
let unifyFresh (t1: Term) (t2: Term) : Substitution option =
    unify t1 t2 Subst.empty
