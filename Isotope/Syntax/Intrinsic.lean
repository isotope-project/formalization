import Isotope.Syntax.Intrinsic.LCtx

inductive GCtx (T: Type u) [HasLin T]: Type u
  | df (Γ: Ctx T)
  | cf (L: LCtx T)

inductive Result (T: Type u) [HasLin T]: Type u
  | term (x: Var T)
  | label (L: LCtx T)

class InstructionSet (F: Type u) (T: Type v)
  where
  inst_ty: F -> Ty T -> Ty T -> Prop
  inst_aff: F -> Ty T -> Ty T -> Prop
  inst_rel: F -> Ty T -> Ty T -> Prop
  inst_cen: F -> Ty T -> Ty T -> Prop


structure InstructionSet.inst {F: Type u} {T: Type v}
  [HasLin T] [InstructionSet F T]
  (f: F) (p: Bool) (q: Transparency) (A B: Ty T) where
  well_typed: inst_ty f A B
  inst_aff: (q.aff → inst_aff f A B)
  insrt_rel: (q.rel → inst_rel f A B)
  inst_cen: (p → inst_cen f A B)

open InstructionSet

inductive Term {T F: Type u} [HasLin T] [InstructionSet F T]
  : Ctx T -> Bool -> Ty T -> Transparency -> Type u
  | var {Γ A q} (p) (v: Ctx.var Γ ⟨q, A⟩): Term Γ p A q
  | app {Γ} {f: F} {p A B} (Hf: inst f p q A B): Term Γ p A q -> Term Γ p B q
  | pair {Γ Δ Ξ A B q}: Ctx.ssplit Γ Δ Ξ
    -> Term Δ true A q
    -> Term Ξ true B q
    -> Term Γ true (Ty.tensor A B) q
  | unit (p) (v: Ctx.wk Γ []) (q): Term Γ p Ty.unit q
  | tt (p) (v: Ctx.wk Γ []) (q): Term Γ p Ty.bool q
  | ff (p) (v: Ctx.wk Γ []) (q): Term Γ p Ty.bool q
  | let1 {Γ Δ Ξ A B q} (p): Ctx.ssplit Γ Δ Ξ
    -> Term Ξ true A q
    -> Term (⟨⟨true, true⟩, A⟩::Δ) p B q
    -> Term Γ p B q
  | let2 {Γ Δ Ξ A B C q} (p): Ctx.ssplit Γ Δ Ξ
    -> Term Ξ true (Ty.tensor A B) q
    -> Term (⟨⟨true, true⟩, A⟩::⟨⟨true, true⟩, B⟩::Δ) p C q
    -> Term Γ p C q

inductive Cf {T: Type u} [HasLin T]: GCtx T -> LCtx T -> Type
  -- TODO

def Block {T: Type u} [HasLin T] (Γ: Ctx T) (L: LCtx T) := Cf (GCtx.df Γ) L
def Cfg {T: Type u} [HasLin T] (L: LCtx T) (K: LCtx T) := Cf (GCtx.cf L) K

-- inductive Term.subst {T} [HasLin T]: Ctx T -> Ctx T -> Type
--   | nil {Γ} (H: Ctx.wk Γ []): subst Γ []
--   | cons {Θ ΘΓ Γ Θx x}
--     (s: Ctx.ssplit Θ ΘΓ Θx)
--     (HΘΓ: subst ΘΓ Γ)
--     (HΘx: HasLin.lin Θx x.toTransparency)
--     (t: Term Θx x)
--     : subst Θ (x::Γ)
