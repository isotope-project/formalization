import Isotope.Syntax.NamedList.LCtx

open InstructionSet

namespace NamedList

inductive GCtx (N: Type u) (T: Type v) [HasLin T]
  | df (Γ: Ctx N T)
  | cf (L: LCtx N T)

inductive Result (N: Type u) (T: Type v) [HasLin T]
  | term (x: Var N T)
  | label (L: LCtx N T)

inductive Term {N: Type u} {T: Type v} [HasLin T]
  (F: Type w) [InstructionSet F T]
  : Ctx N T -> Bool -> Ty T -> Transparency -> Type (max (max u v) w)
  | var {Γ q n A} (p) (v: Γ.var ⟨q, n, A⟩): Term F Γ p A q
  | app {Γ} {f: F} {p A B} (Hf: inst f p q A B)
    : Term F Γ p A q -> Term F Γ p B q
  | pair {Γ Δ Ξ A B q} (p): Γ.ssplit Δ Ξ
    -> Term F Δ true A q
    -> Term F Ξ true B q
    -> Term F Γ p (Ty.tensor A B) q
  | unit (p) (v: Ctx.wk Γ []) (q): Term F Γ p Ty.unit q
  | tt (p) (v: Ctx.wk Γ []) (q): Term F Γ p Ty.bool q
  | ff (p) (v: Ctx.wk Γ []) (q): Term F Γ p Ty.bool q
  | let1 {Γ Δ Ξ q x A B} (p): Γ.ssplit Δ Ξ
    -> Term F Ξ true A q
    -> Term F (⟨⟨true, true⟩, x, A⟩::Δ) p B q
    -> Term F Γ p B q
  | let2 {Γ Δ Ξ q x A y B C} (p): Γ.ssplit Δ Ξ
    -> Term F Ξ true (Ty.tensor A B) q
    -> Term F (⟨⟨true, true⟩, x, A⟩::⟨⟨true, true⟩, y, B⟩::Δ) p C q
    -> Term F Γ p C q
