module FsLogical.Unification

open FsLogical.Term

/// Walk a variable through a substitution chain to find its ultimate binding.
let rec walk (term: Term) (subst: Substitution) : Term =
    match term with
    | Var v ->
        match Map.tryFind v subst with
        | Some t -> walk t subst
        | None -> term
    | _ -> term

/// Apply a substitution deeply to a term, replacing all bound variables.
let rec applySubst (subst: Substitution) (term: Term) : Term =
    let t = walk term subst
    match t with
    | Var _ -> t  // unbound variable
    | Atom _ | Integer _ | Float _ -> t
    | Compound(name, args) ->
        Compound(name, args |> List.map (applySubst subst))

/// Occurs check: does variable 'v' appear in term 't' under substitution?
let rec occursIn (v: string) (term: Term) (subst: Substitution) : bool =
    let t = walk term subst
    match t with
    | Var w -> v = w
    | Atom _ | Integer _ | Float _ -> false
    | Compound(_, args) -> args |> List.exists (fun a -> occursIn v a subst)

/// Unify two terms under the given substitution.
/// Returns Some extended substitution on success, None on failure.
let rec unify (t1: Term) (t2: Term) (subst: Substitution) : Substitution option =
    let t1' = walk t1 subst
    let t2' = walk t2 subst
    match t1', t2' with
    | _ when t1' = t2' -> Some subst
    | Var v, t | t, Var v ->
        if occursIn v t subst then None
        else Some (Map.add v t subst)
    | Compound(n1, args1), Compound(n2, args2) when n1 = n2 && List.length args1 = List.length args2 ->
        List.fold
            (fun acc (a1, a2) ->
                match acc with
                | None -> None
                | Some s -> unify a1 a2 s)
            (Some subst)
            (List.zip args1 args2)
    | _ -> None

/// Unify two terms starting with an empty substitution.
let unifyFresh (t1: Term) (t2: Term) : Substitution option =
    unify t1 t2 Map.empty
