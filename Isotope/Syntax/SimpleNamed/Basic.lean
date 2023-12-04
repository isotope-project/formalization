import Isotope.Syntax.SimpleNamed.LCtx
import Std.Data.List.Basic

open InstructionSet

namespace SimpleNamed

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

def Term.wk {N: Type u} {T: Type v} [HasLin T]
  {F: Type w} [InstructionSet F T]
  {Γ Δ: Ctx N T} {p A q} (H: Γ.wk Δ): Term F Δ p A q → Term F Γ p A q
  | var _ X => var _ (H.comp X)
  | app Hf a => app Hf (wk H a)
  | pair _ S a b =>
    let ⟨_, S, H'⟩ := S.distribute_right H;
    pair _ S a (wk H' b)
  | unit _ D _ => unit _ (H.comp D) _
  | tt _ D _ => tt _ (H.comp D) _
  | ff _ D _ => ff _ (H.comp D) _
  | let1 _ S a e =>
    let ⟨_, S, H'⟩ := S.distribute_right H;
    let1 _ S (wk H' a) e
  | let2 _ S a e =>
    let ⟨_, S, H'⟩ := S.distribute_right H;
    let2 _ S (wk H' a) e

inductive SNCfg {N: Type u} {T: Type v} (F: Type w) [HasLin T]
  [InstructionSet F T]: GCtx N T -> LCtx N T -> Type (max (max u v) w)
  | br {Γ Δ Ξ ℓ q n A L}:
    Γ.ssplit Δ Ξ ->
    Term F Ξ true A q ->
    L.label ⟨ℓ, Δ, ⟨q, n, A⟩⟩ ->
    SNCfg F (GCtx.df Γ) L
  | ite {Γ Δ Ξ L}:
    Γ.ssplit Δ Ξ ->
    Term F Ξ true Ty.bool q ->
    SNCfg F (GCtx.df Δ) L ->
    SNCfg F (GCtx.df Δ) L ->
    SNCfg F (GCtx.df Γ) L
  | let1 {Γ Δ Ξ p q x A L}:
    Γ.ssplit Δ Ξ ->
    Term F Ξ p A q ->
    SNCfg F (GCtx.df (⟨⟨true, true⟩, x, A⟩::Δ)) L ->
    SNCfg F (GCtx.df Γ) L
  | let2 {Γ Δ Ξ p q x A y B L}:
    Γ.ssplit Δ Ξ ->
    Term F Ξ p (Ty.tensor A B) q ->
    SNCfg F (GCtx.df (⟨⟨true, true⟩, x, A⟩::⟨⟨true, true⟩, y, B⟩::Δ)) L ->
    SNCfg F (GCtx.df Γ) L
  | cfg {Γ L K}:
    SNCfg F (GCtx.df Γ) L ->
    SNCfg F (GCtx.cf L) K ->
    SNCfg F (GCtx.df Γ) K
  | cfg_id {L}:
    LCtx.lwk L K ->
    SNCfg F (GCtx.cf L) K
  | cfg_def {Γ ℓ q x A L K}:
    SNCfg F (GCtx.cf L) (⟨ℓ, Γ, ⟨q, x, A⟩⟩::K) ->
    SNCfg F (GCtx.df Γ) L ->
    SNCfg F (GCtx.cf L) K

def SNCfg.intermediate_list {N: Type u} {T: Type v} {F: Type w} [HasLin T]
  [InstructionSet F T] {G: GCtx N T} {L}
  (H: SNCfg F G L)
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
  | @cfg_def _ _ _ _ _ _ ℓ _ x _ _ _ W t
    => ℓ::x::(W.intermediate_list ++ t.intermediate_list)

--TODO: make into an inductive?
def SNCfg.ssa {N: Type u} {T: Type v} {F: Type w} [HasLin T]
  [InstructionSet F T]
  : {G: GCtx N T} -> {L: _} -> SNCfg F G L -> Prop
  | GCtx.df Γ, _, s => (Γ.names ++ s.intermediate_list).Nodup
  | GCtx.cf _, _, cfg_id _ => true
  | GCtx.cf _, _, @cfg_def _ _ _ _ _ Γ ℓ _ x _ _ _ W t =>
    W.ssa
    ∧ t.ssa
    ∧ (Γ.names ++ ℓ::x::(W.intermediate_list ++ t.intermediate_list)).Nodup

inductive GCtx.wk {N: Type u} {T: Type v} [HasLin T]
  : GCtx N T -> GCtx N T -> Type (max u v)
  | df {Γ Δ}: Γ.wk Δ -> GCtx.wk (GCtx.df Γ) (GCtx.df Δ)

def SNCfg.wk' {N: Type u} {T: Type v} {F: Type w} [HasLin T]
  [InstructionSet F T]
  {Γ Δ: GCtx N T} {L: LCtx N T}: Γ.wk Δ -> SNCfg F Δ L -> SNCfg F Γ L
  | GCtx.wk.df H, br S a ℓ =>
    let ⟨_, S, H'⟩ := S.distribute_right H;
    br S (a.wk H') ℓ
  | GCtx.wk.df H, ite S e s t =>
    let ⟨_, S, H'⟩ := S.distribute_right H;
    ite S (e.wk H') s t
  | GCtx.wk.df H, let1 S a t =>
    let ⟨_, S, H'⟩ := S.distribute_right H;
    let1 S (a.wk H') t
  | GCtx.wk.df H, let2 S a t =>
    let ⟨_, S, H'⟩ := S.distribute_right H;
    let2 S (a.wk H') t
  | GCtx.wk.df H, cfg t W => cfg (t.wk' (GCtx.wk.df H)) W

def SNCfg.wk {N: Type u} {T: Type v} {F: Type w} [HasLin T]
  [InstructionSet F T]
  {Γ Δ: Ctx N T} {L: LCtx N T} (H: Γ.wk Δ)
  : SNCfg F (GCtx.df Δ) L -> SNCfg F (GCtx.df Γ) L
  := SNCfg.wk' (GCtx.wk.df H)

def SNCfg.lwk {N: Type u} {T: Type v} {F: Type w} [HasLin T]
  [InstructionSet F T]
  {G: GCtx N T} {L K: LCtx N T} (HK: L.lwk K): SNCfg F G L -> SNCfg F G K
  | br S a ℓ => br S a (ℓ.comp HK)
  | ite S e s t => ite S e (lwk HK s) (lwk HK t)
  | let1 S a t => let1 S a (lwk HK t)
  | let2 S a t => let2 S a (lwk HK t)
  | cfg t W => cfg t (lwk HK W)
  | cfg_id H => cfg_id (H.comp HK)
  | cfg_def W t => cfg_def (lwk (HK.scons _) W) t

--TODO: substitution, et al
