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

inductive NRCfg {N: Type u} {T: Type v} (F: Type w) [HasLin T]
  [InstructionSet F T]: List N -> GCtx N T -> LCtx N T -> LCtx N T
    -> Type (max (max u v) w)
  | br {ΓN Γ Δ Ξ ℓ q n A L K}:
    Γ.ssplit Δ Ξ ->
    Term F Ξ true A q ->
    L.label ⟨ℓ, Δ, ⟨q, n, A⟩⟩ ->
    L.lwk K ->
    NRCfg F ΓN (GCtx.df Γ) L K
  -- anybody defining new variables must be new AND unique
  | ite {ΓN Γ Δ Ξ L K J}:
    Γ.ssplit Δ Ξ ->
    J.njoin ΓN L K ->
    Term F Ξ true Ty.bool q ->
    NRCfg F ΓN (GCtx.df Δ) L J ->
    NRCfg F ΓN (GCtx.df Δ) K J ->
    NRCfg F ΓN (GCtx.df Γ) J J
  | let1 {ΓN Γ Δ Ξ p q x A L K}:
    Γ.ssplit Δ Ξ ->
    x ∉ ΓN ->
    Term F Ξ p A q ->
    NRCfg F (x::ΓN) (GCtx.df (⟨⟨true, true⟩, x, A⟩::Δ)) L K ->
    NRCfg F ΓN (GCtx.df Γ) L K
  | let2 {ΓN Γ Δ Ξ p q x A y B L K}:
    Γ.ssplit Δ Ξ ->
    x ∉ ΓN ->
    y ∉ ΓN ->
    Term F Ξ p (Ty.tensor A B) q ->
    NRCfg F (x::y::ΓN)
      (GCtx.df (⟨⟨true, true⟩, x, A⟩::⟨⟨true, true⟩, y, B⟩::Δ)) L K ->
    NRCfg F ΓN (GCtx.df Γ) L K
  | cfg {ΓN Γ L K K'}:
    NRCfg F ΓN (GCtx.df Γ) L L ->
    NRCfg F ΓN (GCtx.cf L) K K ->
    K.lwk K' ->
    NRCfg F ΓN (GCtx.df Γ) K K'
  | cfg_id {ΓN L K J}:
    LCtx.lwk L K ->
    LCtx.lwk K J ->
    NRCfg F ΓN (GCtx.cf K) L J
  | cfg_def {ΓN Γ ℓ q x A Tt L TL K}:
    TJ.njoin ΓN TL Tt ->
    x ∉ ΓN ->
    NRCfg F (x::ΓN) (GCtx.cf L) TL (⟨ℓ, Γ, ⟨q, x, A⟩⟩::K) ->
    NRCfg F ΓN (GCtx.df Γ) Tt L ->
    NRCfg F ΓN (GCtx.cf L) TJ K

def NRCfg.intermediate_list {N: Type u} {T: Type v} {F: Type w} [HasLin T]
  [InstructionSet F T] {ΓN} {G: GCtx N T} {L K}
  (H: NRCfg F ΓN G L K)
  : List N :=
  match H with
  | br _ _ _ _ => []
  | ite _ _ _ s t => s.intermediate_list ++ t.intermediate_list
  | @let1 _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _ _ _ t
    => x::(t.intermediate_list)
  | @let2 _ _ _ _ _ _ _ _ _ _ _ x _ y _ _ _ _ _ _ _ t
    => x::y::(t.intermediate_list)
  | cfg t L _ => t.intermediate_list ++ L.intermediate_list
  | cfg_id _ _ => []
  | @cfg_def _ _ _ _ _ _ _ _ ℓ _ x _ _ _ _ _ _ _ t L
    => ℓ::x::(t.intermediate_list ++ L.intermediate_list)

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
  | cfg_id {L}:
    LCtx.lwk L K ->
    INCfg F (GCtx.cf L) K
  | cfg_def {Γ ℓ q x A L K}:
    INCfg F (GCtx.cf L) (⟨ℓ, Γ, ⟨q, x, A⟩⟩::K) ->
    INCfg F (GCtx.df Γ) L ->
    INCfg F (GCtx.cf L) K

def INCfg.intermediate_list {N: Type u} {T: Type v} {F: Type w} [HasLin T]
  [InstructionSet F T] {G: GCtx N T} {L}
  (H: INCfg F G L)
  : List N :=
  match H with
  | br _ _ _ => []
  | ite _ _ s t => s.intermediate_list ++ t.intermediate_list
  | @let1 _ _ _ _ _ _ _ _ _ _ x _ _ _ _ t
    => x::(t.intermediate_list)
  | @let2 _ _ _ _ _ _ _ _ _ _ x _ y _ _ _ _ t
    => x::y::(t.intermediate_list)
  | cfg t L => t.intermediate_list ++ L.intermediate_list
  | cfg_id _ => []
  | @cfg_def _ _ _ _ _ _ ℓ _ x _ _ _ t L
    => ℓ::x::(t.intermediate_list ++ L.intermediate_list)

def INCfg.lwk {N: Type u} {T: Type v} {F: Type w} [HasLin T]
  [InstructionSet F T]
  {G: GCtx N T} {L K: LCtx N T} (HK: L.lwk K): INCfg F G L → INCfg F G K
  | br S a ℓ => br S a (ℓ.comp HK)
  | ite S e s t => ite S e (lwk HK s) (lwk HK t)
  | let1 S a t => let1 S a (lwk HK t)
  | let2 S a t => let2 S a (lwk HK t)
  | cfg t W => cfg t (lwk HK W)
  | cfg_id H => cfg_id (H.comp HK)
  | cfg_def W t => cfg_def (lwk (HK.scons _) W) t

def NRCfg.toINCfg {N: Type u} {T: Type v} {F: Type w} [HasLin T]
  [InstructionSet F T] {ΓN} {G: GCtx N T} {L K}
  : NRCfg F ΓN G L K -> INCfg F G K
  | br S t HL HK => INCfg.br S t (HL.comp HK)
  | ite S _ e s t => INCfg.ite S e s.toINCfg t.toINCfg
  | let1 S _ a t => INCfg.let1 S a t.toINCfg
  | let2 S _ _ a t => INCfg.let2 S a t.toINCfg
  | cfg t W H => INCfg.cfg t.toINCfg ((W.toINCfg).lwk H)
  | cfg_id HL HK => INCfg.cfg_id HK
  | cfg_def _ _ W t => INCfg.cfg_def W.toINCfg t.toINCfg
