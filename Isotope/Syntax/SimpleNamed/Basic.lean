import Isotope.Syntax.SimpleNamed.LCtx
import Std.Data.List.Basic

open InstructionSet

namespace SimpleNamed

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

--TODO: wk associativity theorem

inductive GCtx (N: Type u) (T: Type v)
  | df (Γ: Ctx N T)
  | cf (L: LCtx N T)

inductive GKind
  | df
  | cf

open GKind

def GKind.Ctx (N: Type u) (T: Type v)
  : GKind -> Type (max u v)
  | df => SimpleNamed.Ctx N T
  | cf => LCtx N T

inductive SGCfg.{u, v, w} {N: Type u} {T: Type v} (F: Type w) [HasLin T]
  [InstructionSet F T]:
    (k: GKind) -> k.Ctx N T -> LCtx N T -> Type (max (max u v) w)
  | br {Γ Δ Ξ ℓ q n A L}:
    Γ.ssplit Δ Ξ ->
    Term F Ξ true A q ->
    L.label ⟨ℓ, Δ, ⟨q, n, A⟩⟩ ->
    SGCfg F df Γ L
  | ite {Γ Δ Ξ L}:
    Γ.ssplit Δ Ξ ->
    Term F Ξ true Ty.bool q ->
    SGCfg F df Δ L ->
    SGCfg F df Δ L ->
    SGCfg F df Γ L
  | let1 {Γ Δ Ξ p q x A L}:
    Γ.ssplit Δ Ξ ->
    Term F Ξ p A q ->
    SGCfg F df (⟨⟨true, true⟩, x, A⟩::Δ) L ->
    SGCfg F df Γ L
  | let2 {Γ Δ Ξ p q x A y B L}:
    Γ.ssplit Δ Ξ ->
    Term F Ξ p (Ty.tensor A B) q ->
    SGCfg F df (⟨⟨true, true⟩, x, A⟩::⟨⟨true, true⟩, y, B⟩::Δ) L ->
    SGCfg F df Γ L
  | cfg {Γ L K}:
    SGCfg F df Γ L ->
    SGCfg F cf L K ->
    SGCfg F df Γ K
  | cfg_id {L}:
    LCtx.lwk L K ->
    SGCfg F cf L K
  | cfg_def {Γ ℓ q x A L K}:
    SGCfg F cf L (⟨ℓ, Γ, ⟨q, x, A⟩⟩::K) ->
    SGCfg F df Γ L ->
    SGCfg F cf L K

def SGCfg.intermediate_list {N: Type u} {T: Type v} {F: Type w} [HasLin T]
  [InstructionSet F T] {k} {G: k.Ctx N T} {L}
  (H: SGCfg F k G L)
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
def SGCfg.ssa {N: Type u} {T: Type v} {F: Type w} [HasLin T]
  [InstructionSet F T]
  : {k: GKind} -> {G: k.Ctx N T} -> {L: _} -> SGCfg F k G L -> Prop
  | df, Γ, _, s => (Γ.names ++ s.intermediate_list).Nodup
  | cf, _, _, cfg_id _ => true
  | cf, _, _, @cfg_def _ _ _ _ _ Γ ℓ _ x _ _ _ W t =>
    W.ssa
    ∧ t.ssa
    ∧ (Γ.names ++ ℓ::x::(W.intermediate_list ++ t.intermediate_list)).Nodup

def SGCfg.wk {N: Type u} {T: Type v} {F: Type w} [HasLin T]
  [InstructionSet F T]
  {Γ Δ: Ctx N T} {L: LCtx N T}: Γ.wk Δ -> SGCfg F df Δ L -> SGCfg F df Γ L
  | H, br S a ℓ =>
    let ⟨_, S, H'⟩ := S.distribute_right H;
    br S (a.wk H') ℓ
  | H, ite S e s t =>
    let ⟨_, S, H'⟩ := S.distribute_right H;
    ite S (e.wk H') s t
  | H, let1 S a t =>
    let ⟨_, S, H'⟩ := S.distribute_right H;
    let1 S (a.wk H') t
  | H, let2 S a t =>
    let ⟨_, S, H'⟩ := S.distribute_right H;
    let2 S (a.wk H') t
  | H, cfg t W => cfg (t.wk H) W

def SGCfg.lwk {N: Type u} {T: Type v} {F: Type w} [HasLin T]
  [InstructionSet F T]
  {k} {G: k.Ctx N T} {L K: LCtx N T} (HK: L.lwk K)
  : SGCfg F k G L -> SGCfg F k G K
  | br S a ℓ => br S a (ℓ.comp HK)
  | ite S e s t => ite S e (lwk HK s) (lwk HK t)
  | let1 S a t => let1 S a (lwk HK t)
  | let2 S a t => let2 S a (lwk HK t)
  | cfg t W => cfg t (lwk HK W)
  | cfg_id H => cfg_id (H.comp HK)
  | cfg_def W t => cfg_def (lwk (HK.scons _) W) t

--TODO: can't we just use abbrev?
def SNBlk.{u, v, w} {N: Type u} {T: Type v} (F: Type w)
  [HasLin T] [InstructionSet F T]
  : Ctx N T -> LCtx N T -> Type (max (max u v) w)
  := @SGCfg N T F _ _ df

@[match_pattern]
def SNBlk.br {N: Type u} {T: Type v} {F: Type w} [HasLin T] [InstructionSet F T]
  {Γ Δ Ξ: Ctx N T} {ℓ q n A} {L: LCtx N T}
  (S: Γ.ssplit Δ Ξ) (a: Term F Ξ true A q) (H: L.label ⟨ℓ, Δ, ⟨q, n, A⟩⟩)
  : SNBlk F Γ L
  := SGCfg.br S a H
@[match_pattern]
def SNBlk.ite {N: Type u} {T: Type v} {F: Type w}
  [HasLin T] [InstructionSet F T]
  {Γ Δ Ξ: Ctx N T} {L: LCtx N T}
  (S: Γ.ssplit Δ Ξ) (e: Term F Ξ true Ty.bool q)
  (s t: SNBlk F Δ L)
  : SNBlk F Γ L
  := SGCfg.ite S e s t
@[match_pattern]
def SNBlk.let1 {N: Type u} {T: Type v} {F: Type w}
  [HasLin T] [InstructionSet F T]
  {Γ Δ Ξ: Ctx N T} {p q x A} {L: LCtx N T}
  (S: Γ.ssplit Δ Ξ) (a: Term F Ξ p A q)
  (t: SNBlk F (⟨⟨true, true⟩, x, A⟩::Δ) L)
  : SNBlk F Γ L
  := SGCfg.let1 S a t
@[match_pattern]
def SNBlk.let2 {N: Type u} {T: Type v} {F: Type w}
  [HasLin T] [InstructionSet F T]
  {Γ Δ Ξ: Ctx N T} {p q x A y B} {L: LCtx N T}
  (S: Γ.ssplit Δ Ξ) (a: Term F Ξ p (A.tensor B) q)
  (t: SNBlk F (⟨⟨true, true⟩, x, A⟩::⟨⟨true, true⟩, y, B⟩::Δ) L)
  : SNBlk F Γ L
  := SGCfg.let2 S a t

def SNBlk.wk {N: Type u} {T: Type v} {F: Type w}
  [HasLin T] [InstructionSet F T]
  {Γ Δ: Ctx N T} {L: LCtx N T} (H: Γ.wk Δ)
  : SNBlk F Δ L -> SNBlk F Γ L
  := SGCfg.wk H
def SNBlk.lwk {N: Type u} {T: Type v} {F: Type w}
  [HasLin T] [InstructionSet F T]
  {Γ: Ctx N T} {L K: LCtx N T} (H: L.lwk K)
  : SNBlk F Γ L -> SNBlk F Γ K
  := SGCfg.lwk H

--TODO: can't we just use abbrev?
def SNCfg {N: Type u} {T: Type v} (F: Type w) [HasLin T] [InstructionSet F T]
  := @SGCfg N T F _ _ cf

@[match_pattern]
def SNBlk.cfg {N: Type u} {T: Type v} {F: Type w}
  [HasLin T] [InstructionSet F T]
  {Γ: Ctx N T} {L K: LCtx N T}
  (t: SNBlk F Γ L) (W: SNCfg F L K)
  : SNBlk F Γ K
  := SGCfg.cfg t W

@[match_pattern]
def SNCfg.cfg_id {N: Type u} {T: Type v} {F: Type w}
  [HasLin T] [InstructionSet F T]
  {L K: LCtx N T}
  (H: L.lwk K)
  : SNCfg F L K
  := SGCfg.cfg_id H
@[match_pattern]
def SNCfg.cfg_def {N: Type u} {T: Type v} {F: Type w}
  [HasLin T] [InstructionSet F T]
  {Γ: Ctx N T} {ℓ q x A} {L K: LCtx N T}
  (W: SNCfg F L (⟨ℓ, Γ, ⟨q, x, A⟩⟩::K))
  (t: SNBlk F Γ L)
  : SNCfg F L K
  := SGCfg.cfg_def W t

def SNCfg.lwk {N: Type u} {T: Type v} {F: Type w}
  [HasLin T] [InstructionSet F T]
  {L K K': LCtx N T} (H: K.lwk K')
  : SNCfg F L K -> SNCfg F L K'
  := SGCfg.lwk H

--TODO: factor out substitution?

inductive SNSubst' {N: Type u} {T: Type v} (F: Type w) [HasLin T]
  [InstructionSet F T] (p: Bool)
  : Ctx N T -> Ctx N T -> Type (max (max u v) w)
  | nil {Γ Δ} (H: Γ.wk Δ): SNSubst' F p Γ Δ
  | cons {Θ ΘΓ Θx q x A Γ} (S: Θ.ssplit ΘΓ Θx)
    (BΓ: SNSubst' F p ΘΓ Γ)
    (Bx: Term F Θx p A q)
    : HasLin.lin Θx (q ⊓ HasLin.qtt A) -> SNSubst' F p Θ (⟨q, x, A⟩::Γ)

def SNSubst'.swk {N: Type u} {T: Type v} {F: Type w}
  [HasLin T] [InstructionSet F T] {p} {Θ Γ Δ: Ctx N T}
  (H: Θ.wk Γ): SNSubst' F p Γ Δ -> SNSubst' F p Θ Δ
  | nil H' => nil (H.comp H')
  | cons S BΓ Bx Hx =>
    let ⟨_, S, H⟩ := S.distribute_left H;
    cons S (swk H BΓ) Bx Hx

def SNSubst'.twk {N: Type u} {T: Type v} {F: Type w}
  [HasLin T] [InstructionSet F T] {p} {Θ Γ Δ: Ctx N T}
  : Θ.wk Δ -> SNSubst' F p Γ Θ -> SNSubst' F p Γ Δ
  | W, nil H => nil (H.comp W)
  | Ctx.wk.cons Hl W, cons S BΓ Bx Hx
    => cons S (twk W BΓ)
      (Hl.2.1 ▸ Bx.upgrade (le_refl p) Hl.2.2)
      (HasLin.sublin (Hl.2.1 ▸ (inf_le_inf_right _ Hl.2.2)) Hx)
  | Ctx.wk.discard Hl W, cons S BΓ Bx Hx
    => twk W (swk (S.drop_left
      (Ctx.wk.fromAff (by
        simp only [
          HasLin.lin, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq
          ] at Hx
        exact Hx.1 Hl
        ))) BΓ)

def SNSubst'.source {N: Type u} {T: Type v} {F: Type w}
  [HasLin T] [InstructionSet F T] {p} {Γ Δ: Ctx N T}
  (_: SNSubst' F p Γ Δ): Ctx N T
  := Γ

def SNSubst'.target {N: Type u} {T: Type v} {F: Type w}
  [HasLin T] [InstructionSet F T] {p} {Γ Δ: Ctx N T}
  (_: SNSubst' F p Γ Δ): Ctx N T
  := Δ

def SNSubst {N: Type u} {T: Type v} (F: Type w)
  [HasLin T] [InstructionSet F T] := @SNSubst' N T F _ _ true

@[match_pattern]
def SNSubst.nil {N: Type u} {T: Type v} {F: Type w}
  [HasLin T] [InstructionSet F T] {Γ Δ: Ctx N T} (H: Γ.wk Δ)
  : SNSubst F Γ Δ := SNSubst'.nil H

@[match_pattern]
def SNSubst.cons {N: Type u} {T: Type v} {F: Type w}
  [HasLin T] [InstructionSet F T]
  {Θ ΘΓ Θx: Ctx N T} {q x A Γ} (H: Θ.ssplit ΘΓ Θx)
  (BΓ: SNSubst F ΘΓ Γ) (Bx: Term F Θx true A q)
  : HasLin.lin Θx (q ⊓ HasLin.qtt A) -> SNSubst F Θ (⟨q, x, A⟩::Γ)
  := SNSubst'.cons H BΓ Bx

def SNSubst.toDrop {N: Type u} {T: Type v} {F: Type w}
  [HasLin T] [InstructionSet F T] {Γ: Ctx N T}
  : SNSubst F Γ [] -> Γ.wk []
  | nil H => H

def SNSubst.toTerm {N: Type u} {T: Type v} {F: Type w}
  [HasLin T] [InstructionSet F T] {Γ: Ctx N T} {v}
  : SNSubst F Γ [v] -> Term F Γ true v.ty v.toTransparency
  | nil W => Term.var true W
  | cons S BΓ Bx _ => Bx.wk (S.drop_right BΓ.toDrop)

def SNSubst.scons {N: Type u} {T: Type v} {F: Type w}
  [HasLin T] [InstructionSet F T]
  {Θ: Ctx N T} {Γ}
  (BΓ: SNSubst F Θ Γ) (v: Var N T)
  : SNSubst F (v::Θ) (v::Γ)
  := BΓ.cons
    ((Ctx.ssplit.list_left Θ).sright v)
    (Term.var true (Ctx.wk.id [v]))
    (by
      simp only [HasLin.lin, HasLin.aff, Transparency.instLattice, HasLin.rel]
      aesop)

def SNSubst.swk {N: Type u} {T: Type v} {F: Type w}
  [HasLin T] [InstructionSet F T] {Θ Γ Δ: Ctx N T}
  (H: Θ.wk Γ): SNSubst F Γ Δ -> SNSubst F Θ Δ
  := SNSubst'.swk H

def SNSubst.twk {N: Type u} {T: Type v} {F: Type w}
  [HasLin T] [InstructionSet F T] {Θ Γ Δ: Ctx N T}
  : Θ.wk Δ -> SNSubst F Γ Θ -> SNSubst F Γ Δ
  := SNSubst'.twk

def SNSubst.source {N: Type u} {T: Type v} {F: Type w}
  [HasLin T] [InstructionSet F T] {Γ Δ: Ctx N T}
  (_: SNSubst F Γ Δ): Ctx N T
  := Γ

def SNSubst.target {N: Type u} {T: Type v} {F: Type w}
  [HasLin T] [InstructionSet F T] {Γ Δ: Ctx N T}
  (_: SNSubst F Γ Δ): Ctx N T
  := Δ

def SNSubst.distribute_ssplit {N: Type u} {T: Type v} {F: Type w}
  [HasLin T] [InstructionSet F T] {Θ Γ Δ Ξ: Ctx N T}
  : SNSubst F Θ Γ -> Γ.ssplit Δ Ξ ->
    (ΘΔ ΘΞ: Ctx N T) × Θ.ssplit ΘΔ ΘΞ × SNSubst F ΘΔ Δ × SNSubst F ΘΞ Ξ
  | nil H, S =>
    let ⟨Δ', S, H⟩ := S.distribute_left H;
    ⟨Δ', Ξ, S, nil H, nil (Ctx.wk.id _)⟩
  | cons S BΓ Bx H, Ctx.ssplit.left Hl S' =>
    let ⟨ΘΔ, ΘΞ, S', BΔ, BΞ⟩ := distribute_ssplit BΓ S';
    let ⟨ΘΨ, S, S'⟩ := S.swap.associate_left S';
    ⟨ΘΨ, ΘΞ, S,
      cons S'.swap BΔ
        (Hl.2.1 ▸ Bx.upgrade (le_refl _) Hl.2.2)
        (HasLin.sublin (Hl.2.1 ▸ (inf_le_inf_right _ Hl.2.2)) H),
      BΞ⟩
  | cons S BΓ Bx H, Ctx.ssplit.right Hr S' =>
    let ⟨ΘΔ, ΘΞ, S', BΔ, BΞ⟩ := distribute_ssplit BΓ S';
    let ⟨ΘΨ, S, S'⟩ := S.associate_right S';
    ⟨ΘΔ, ΘΨ, S, BΔ,
      cons S' BΞ
        (Hr.2.1 ▸ Bx.upgrade (le_refl _) Hr.2.2)
        (HasLin.sublin (Hr.2.1 ▸ (inf_le_inf_right _ Hr.2.2)) H)⟩
  | cons S BΓ Bx H, Ctx.ssplit.dup Hrel Hl Hr S' =>
    let ⟨ΘΔ, ΘΞ, S', BΔ, BΞ⟩ := distribute_ssplit BΓ S';
    let ⟨_, _, S1324, S13, S24⟩ := S.distribute_dup_left S'
      (by
        simp only [
          HasLin.lin, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq
        ] at H
        exact H.2 Hrel
      );
    ⟨_, _, S1324,
      cons S13 BΔ
        (Hl.2.1 ▸ Bx.upgrade (le_refl _) Hl.2.2)
        (HasLin.sublin (Hl.2.1 ▸ (inf_le_inf_right _ Hl.2.2)) H),
      cons S24 BΞ
        (Hr.2.1 ▸ Bx.upgrade (le_refl _) Hr.2.2)
        (HasLin.sublin (Hr.2.1 ▸ (inf_le_inf_right _ Hr.2.2)) H)⟩

--TODO: "subsubst w.r.t"

--TODO: "subsubst distr"

--TODO: "selector rune"

def Term.subst {N: Type u} {T: Type v} {F: Type w}
  [HasLin T] [InstructionSet F T] {Θ Γ: Ctx N T} {p A q}
  (σ: SNSubst F Θ Γ): Term F Γ p A q -> Term F Θ p A q
  | var _ X => (σ.twk X).toTerm.upgrade (by simp) (le_refl _)
  | app Hf a => app Hf (subst σ a)
  | pair _ S a b =>
    let ⟨_, _, S, σΔ, σΞ⟩ := σ.distribute_ssplit S;
    pair _ S (subst σΔ a) (subst σΞ b)
  | unit _ H _ => unit _ (σ.twk H).toDrop _
  | tt _ H _ => tt _ (σ.twk H).toDrop _
  | ff _ H _ => ff _ (σ.twk H).toDrop _
  | let1 _ S a e =>
    let ⟨_, _, S, σΔ, σΞ⟩ := σ.distribute_ssplit S;
    let1 _ S (subst σΞ a) (subst (σΔ.scons _) e)
  | let2 _ S a e =>
    let ⟨_, _, S, σΔ, σΞ⟩ := σ.distribute_ssplit S;
    let2 _ S (subst σΞ a) (subst ((σΔ.scons _).scons _) e)

inductive SNHLSubst {N: Type u} {T: Type v} (F: Type w)
  [HasLin T] [InstructionSet F T] : LCtx N T -> LCtx N T
    -> Type (max (max u v) w)
  | nil: SNHLSubst F [] []
  | cons {L K ℓ A Γ Δ}: SNHLSubst F L K -> SNSubst F Γ Δ
    -> SNHLSubst F (⟨ℓ, Γ, A⟩::L) (⟨ℓ, Δ, A⟩::K)

--TODO: "subhlbsubst w.r.t"

--TODO: CFG substitution theorem

inductive SNLSubst {N: Type u} {T: Type v} (F: Type w)
  [HasLin T] [InstructionSet F T]: LCtx N T -> LCtx N T
    -> Type (max (max u v) w)
  | nil (K): SNLSubst F [] K
  -- | cons {L K ℓ A Γ Δ}: SNLSubst F L K ->
  --   -> SNLSubst F (⟨ℓ, Γ, A⟩::L) (⟨ℓ, Δ, A⟩::K)
