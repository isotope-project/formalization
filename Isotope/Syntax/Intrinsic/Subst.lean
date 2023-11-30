import Isotope.Syntax.Intrinsic.Basic
import Isotope.Syntax.Intrinsic.Wk

inductive Ctx.subst {T: Type u} [HasLin T] (F: Type u) [InstructionSet F T]
  : Ctx T -> Ctx T -> Type u
  | nil {Γ} (H: Ctx.wk Γ []): subst F Γ []
  | cons {Θ ΘΓ Γ Θx p A q}
    (S: Ctx.ssplit Θ ΘΓ Θx)
    (HΘΓ: subst F ΘΓ Γ)
    (HΘx: HasLin.lin Θx q)
    (t: Term F Θx p A q)
    : subst F Θ (⟨q, A⟩::Γ)
