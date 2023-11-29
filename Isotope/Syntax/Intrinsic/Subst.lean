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

def Ctx.subst.wk_src {T: Type u} [HasLin T] {F: Type u} [InstructionSet F T]
  {Θ Θ' Γ: Ctx T} (H: Θ'.wk Θ): subst F Θ Γ -> subst F Θ' Γ
  | nil HΘ => nil (H.comp HΘ)
  | cons S HΘΓ HΘx t =>
    let ⟨_, _, S', Wl, Wr⟩ := S.distribute_left H
    sorry
    -- cons S' (HΘΓ.wk_src Wl) sorry sorry
