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

def Term.upgrade {N: Type u} {T: Type v} [HasLin T]
  {F: Type w} [InstructionSet F T]
  {Γ: Ctx N T} {c A q c' q'} (Hp: c ≥ c') (Hq: q ≥ q')
  : Term F Γ c A q → Term F Γ c' A q'
  | var _ X => var _ (X.upgrade ⟨rfl, rfl, Hq⟩)
  | app Hf a => app (Hf.upgrade Hp Hq) (upgrade Hp Hq a)
  | pair _ S a b =>
    pair _ S (upgrade (le_refl _) Hq a) (upgrade (le_refl _) Hq b)
  | unit _ D _ => unit _ D _
  | tt _ D _ => tt _ D _
  | ff _ D _ => ff _ D _
  | let1 _ S a e =>
    let1 _ S (upgrade (le_refl _) Hq a) (upgrade Hp Hq e)
  | let2 p S a e =>
    let2 _ S (upgrade (le_refl _) Hq a) (upgrade Hp Hq e)

inductive NCfg {N: Type u} {T: Type v} (F: Type w) [HasLin T]
  [InstructionSet F T]: List N -> GCtx N T -> LCtx N T -> Type (max (max u v) w)
  | br {ΓN Γ Δ Ξ ℓ q n A L}:
    Γ.ssplit Δ Ξ ->
    Term F Ξ true A q ->
    L.label ⟨ℓ, Δ, ⟨q, n, A⟩⟩ ->
    NCfg F ΓN (GCtx.df Γ) L
  | ite {ΓN Γ Δ Ξ L}:
    Γ.ssplit Δ Ξ ->
    Term F Ξ true Ty.bool q ->
    NCfg F ΓN (GCtx.df Δ) L ->
    NCfg F ΓN (GCtx.df Δ) L ->
    NCfg F ΓN (GCtx.df Γ) L
  | let1 {ΓN Γ Δ Ξ p q x A L}:
    Γ.ssplit Δ Ξ ->
    x ∉ ΓN ->
    Term F Ξ p A q ->
    NCfg F (x::ΓN) (GCtx.df (⟨⟨true, true⟩, x, A⟩::Δ)) L ->
    NCfg F ΓN (GCtx.df Γ) L
  | let2 {ΓN Γ Δ Ξ p q x A y B L}:
    Γ.ssplit Δ Ξ ->
    x ∉ ΓN ->
    y ∉ ΓN ->
    Term F Ξ p (Ty.tensor A B) q ->
    NCfg F (x::y::ΓN) (GCtx.df (⟨⟨true, true⟩, x, A⟩::⟨⟨true, true⟩, y, B⟩::Δ)) L ->
    NCfg F ΓN (GCtx.df Γ) L
  | cfg {ΓN Γ L K}:
    NCfg F ΓN (GCtx.df Γ) L ->
    NCfg F ΓN (GCtx.cf L) K ->
    NCfg F ΓN (GCtx.df Γ) K
  --TODO: control control-flow
  | cfg_id {ΓN L K}:
    LCtx.lwk L K ->
    NCfg F ΓN (GCtx.cf L) K
  | cfg_def {ΓN Γ ℓ q x A L K}:
    x ∉ ΓN ->
    NCfg F (x::ΓN) (GCtx.cf L) (⟨ℓ, Γ, ⟨q, x, A⟩⟩::L) ->
    NCfg F ΓN (GCtx.df Γ) K ->
    NCfg F ΓN (GCtx.cf L) K

inductive INCfg {N: Type u} {T: Type v} (F: Type w) [HasLin T]
  [InstructionSet F T]: GCtx N T -> LCtx N T -> Type (max (max u v) w)
  | br {Γ Δ Ξ ℓ q n A L}:
    Γ.ssplit Δ Ξ ->
    Term F Ξ true A q ->
    L.label ⟨ℓ, Δ, ⟨q, n, A⟩⟩ ->
    INCfg F (GCtx.df Γ) L
  | ite {Γ Δ Ξ L}:
    Γ.ssplit Δ Ξ ->
    Term F Ξ true Ty.bool q ->
    INCfg F (GCtx.df Δ) L ->
    INCfg F (GCtx.df Δ) L ->
    INCfg F (GCtx.df Γ) L
  | let1 {Γ Δ Ξ p q x A L}:
    Γ.ssplit Δ Ξ ->
    Term F Ξ p A q ->
    INCfg F (GCtx.df (⟨⟨true, true⟩, x, A⟩::Δ)) L ->
    INCfg F (GCtx.df Γ) L
  | let2 {Γ Δ Ξ p q x A y B L}:
    Γ.ssplit Δ Ξ ->
    Term F Ξ p (Ty.tensor A B) q ->
    INCfg F (GCtx.df (⟨⟨true, true⟩, x, A⟩::⟨⟨true, true⟩, y, B⟩::Δ)) L ->
    INCfg F (GCtx.df Γ) L
  | cfg {Γ L K}:
    INCfg F (GCtx.df Γ) L ->
    INCfg F (GCtx.cf L) K ->
    INCfg F (GCtx.df Γ) K
  | cfg_id (L):
    INCfg F (GCtx.cf L) L
  | cfg_def {Γ ℓ q x A L K}:
    INCfg F (GCtx.cf L) (⟨ℓ, Γ, ⟨q, x, A⟩⟩::L) ->
    INCfg F (GCtx.df Γ) K ->
    INCfg F (GCtx.cf L) K
