import Isotope.Syntax.Intrinsic.Ctx

inductive Term {T} [HasLin T]: Ctx T -> Variable T -> Type
  | var {Γ x} (v: Ctx.var Γ x): Term Γ x
  -- TODO

inductive Term.subst {T} [HasLin T]: Ctx T -> Ctx T -> Type
  | nil {Γ} (H: Ctx.wk Γ []): subst Γ []
  | cons {Θ ΘΓ Γ Θx x}
    (s: Ctx.ssplit Θ ΘΓ Θx)
    (HΘΓ: subst ΘΓ Γ)
    (HΘx: HasLin.lin Θx x.toTransparency)
    (t: Term Θx x)
    : subst Θ (x::Γ)
