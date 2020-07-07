datatype Option<a> = None | Some(a)

datatype Type = Nat | Fun(Type, Type)
datatype Term = Var(string) | Lam(string, Term) | App(Term, Term)

type Ctx = map<string, Type>

predicate HasTypeAux(t : Term, ctx : Ctx, ty : Type)

predicate HasType(t : Term, ty : Type)
{
    HasTypeAux(t, map[], ty)
}

method typeSynthAux(t : Term, ctx : Ctx)
    returns (p : Option<Type>)
    ensures exists ty : Type :: p == Some(ty) <==> HasTypeAux(t, ctx, ty)
{
    match t {
        case Var(x) =>
            if x in ctx {
                p := Some(ctx[x]);
            } else {
                p := None;
            }
        case Lam(x, body) =>
            p := None
        case App(r, s) => {}
    }
}

method typeCheck(t : Term, ty : Term) returns (b : bool)
    ensures b <=> HasType(t, ty)

method typeSynth(t : Term) returns (p : Option<Type>)
    ensures exists ty : Type :: p == Some(ty) <==> HasType(t, ty)
{
    p := typeCheckAux(t, map[]);
}
