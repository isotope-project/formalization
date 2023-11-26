import Mathlib.Init.Order.Defs
import Mathlib.Data.Bool.Basic
import Mathlib.Logic.Equiv.Defs

inductive Ty (T: Type u)
| base (X: T)
| unit
| bool
| tensor (A B: Ty T)

class HasLin (T: Type u) :=
  aff: T → Bool
  rel: T → Bool

instance Ty.instHasLin {T} [HasLin T]: HasLin (Ty T) where
  aff := let rec aff
    | base X => HasLin.aff X
    | tensor A B => aff A && aff B
    | _ => true
    aff
  rel := let rec rel
    | base X => HasLin.rel X
    | tensor A B => rel A && rel B
    | _ => true
    rel

structure Transparency where
  aff: Bool
  rel: Bool

def HasLin.lin {T} [HasLin T] (t: T) (l: Transparency): Bool
  := (l.aff → HasLin.aff t) ∧ (l.rel → HasLin.rel t)

instance Transparency.instPartialOrder: PartialOrder Transparency where
  le l r := l.aff ≤ r.aff ∧ l.rel ≤ r.rel
  le_refl := by simp
  le_trans _ _ _ H H' := ⟨le_trans H.1 H'.1, le_trans H.2 H'.2⟩
  le_antisymm _ _ H H'
    := mk.injEq _ _ _ _ ▸ ⟨le_antisymm H.1 H'.1, le_antisymm H.2 H'.2⟩

theorem Transparency.le.aff {l r: Transparency}
  : l ≤ r → l.aff → r.aff := And.left

theorem Transparency.le.rel {l r: Transparency}
  : l ≤ r → l.rel → r.rel := And.right

--TODO: add resource algebra to variables?
structure Variable (T: Type u) extends Transparency where
  ty: Ty T

instance Variable.instHasLin {T} [HasLin T]: HasLin (Variable T) where
  aff v := v.aff && HasLin.aff v.ty
  rel v := v.rel && HasLin.rel v.ty

instance Variable.instPartialOrder {T}: PartialOrder (Variable T) where
  le l r := l.ty = r.ty ∧ l.toTransparency ≤ r.toTransparency
  le_refl := by simp [le_refl]
  le_trans _ _ _  | ⟨He, Ht⟩, ⟨He', Ht'⟩ => ⟨He.trans He', le_trans Ht Ht'⟩
  le_antisymm x x' H H'
    := mk.injEq _ _ _ _ ▸ ⟨le_antisymm H.2 H'.2, H.1⟩

theorem Variable.le.aff {T} [HasLin T] {l r: Variable T}
  : l ≤ r → HasLin.aff l → HasLin.aff r
  | ⟨He, Ht⟩ => by
    simp only [HasLin.aff, He, Bool.and_eq_true, and_imp]
    intro H H';
    exact ⟨Ht.1 H, H'⟩

theorem Variable.le.rel {T} [HasLin T] {l r: Variable T}
  : l ≤ r → HasLin.rel l → HasLin.rel r
  | ⟨He, Ht⟩ => by
    simp only [HasLin.rel, He, Bool.and_eq_true, and_imp]
    intro H H';
    exact ⟨Ht.2 H, H'⟩

abbrev Ctx (T: Type u) := List (Variable T)

inductive Ctx.split {T} [HasLin T]: Ctx T → Ctx T → Ctx T → Type
  | nil: split [] [] []
  | left {Γ Δ Ξ} (v l):  l ≤ v → split Γ Δ Ξ → split (v::Γ) (l::Δ) Ξ
  | right {Γ Δ Ξ} (v r): r ≤ v → split Γ Δ Ξ → split (v::Γ) Δ (r::Ξ)
  | discard {Γ Δ Ξ} (v): HasLin.aff v → split Γ Δ Ξ → split (v::Γ) Δ Ξ
  | dup {Γ Δ Ξ} (v l r): HasLin.rel v → l ≤ v → r ≤ v → split Γ Δ Ξ
    → split (v::Γ) (l::Δ) (r::Ξ)

inductive Ctx.split.strict {T} [HasLin T]
  : {Γ Δ Ξ: Ctx T} -> split Γ Δ Ξ -> Prop
  | nil: strict nil
  | left (v H): strict H → strict (left v v (le_refl v) H)
  | right (v H): strict H → strict (right v v (le_refl v) H)
  | dup (v Hr H)
    : strict H → strict (dup v v v Hr (le_refl v) (le_refl v) H)

inductive Ctx.ssplit {T} [HasLin T]: Ctx T → Ctx T → Ctx T → Type
  | nil: ssplit [] [] []
  | left {Γ Δ Ξ} (v):  ssplit Γ Δ Ξ → ssplit (v::Γ) (v::Δ) Ξ
  | right {Γ Δ Ξ} (v): ssplit Γ Δ Ξ → ssplit (v::Γ) Δ (v::Ξ)
  | dup {Γ Δ Ξ} (v): HasLin.rel v → ssplit Γ Δ Ξ
    → ssplit (v::Γ) (v::Δ) (v::Ξ)

def Ctx.ssplit.toSplit {T} [HasLin T] {Γ Δ Ξ: Ctx T}
  : ssplit Γ Δ Ξ → split Γ Δ Ξ
  | nil => split.nil
  | left v H => split.left v v (le_refl v) (ssplit.toSplit H)
  | right v H => split.right v v (le_refl v) (ssplit.toSplit H)
  | dup v Hr H =>
    split.dup v v v Hr (le_refl v) (le_refl v) (ssplit.toSplit H)

def Ctx.split.swap {T} [HasLin T] {Γ Δ Ξ: Ctx T}
  : split Γ Δ Ξ -> split Γ Ξ Δ
  | nil => nil
  | left v l Hl H => right v l Hl (swap H)
  | right v r Hl H => left v r Hl (swap H)
  | discard v Ha Hl => discard v Ha (swap Hl)
  | dup v l r H Hl Hr HΓ
    => dup v r l H Hr Hl (swap HΓ)

def Ctx.ssplit.swap {T} [HasLin T] {Γ Δ Ξ: Ctx T}
  : ssplit Γ Δ Ξ -> ssplit Γ Ξ Δ
  | nil => nil
  | left v H => right v (swap H)
  | right v H => left v (swap H)
  | dup v Hr H => dup v Hr (swap H)

def Ctx.ssplit.swap_toSplit {T} [HasLin T] {Γ Δ Ξ: Ctx T}
  : (H: ssplit Γ Δ Ξ) -> H.swap.toSplit = H.toSplit.swap
  | nil => rfl
  | left v H => congrArg _ (swap_toSplit H)
  | right v H => congrArg _ (swap_toSplit H)
  | dup v Hr H => congrArg _ (swap_toSplit H)

def Ctx.split.swap_idem {T} [HasLin T] {Γ Δ Ξ: Ctx T}
  : Function.LeftInverse (@swap T _ Γ Δ Ξ) (@swap T _ Γ Ξ Δ)
  | nil => rfl
  | left v l Hl HΓ => by simp [swap, swap_idem HΓ]
  | right v r Hr HΓ => by simp [swap, swap_idem HΓ]
  | discard v Ha HΓ => by simp [swap, swap_idem HΓ]
  | dup v l r Har Hl Hr HΓ => by simp [swap, swap_idem HΓ]

def Ctx.ssplit.swap_idem {T} [HasLin T] {Γ Δ Ξ: Ctx T}
  : Function.LeftInverse (@swap T _ Γ Δ Ξ) (@swap T _ Γ Ξ Δ)
  | nil => rfl
  | left v H => by simp [swap, swap_idem H]
  | right v H => by simp [swap, swap_idem H]
  | dup v Hr H => by simp [swap, swap_idem H]

def Ctx.split.swap_equiv {T} [HasLin T] (Γ Δ Ξ: Ctx T)
  : Equiv (split Γ Δ Ξ) (split Γ Ξ Δ) where
  toFun := swap
  invFun := swap
  left_inv := swap_idem
  right_inv := swap_idem

def Ctx.ssplit.swap_equiv {T} [HasLin T] (Γ Δ Ξ: Ctx T)
  : Equiv (ssplit Γ Δ Ξ) (ssplit Γ Ξ Δ) where
  toFun := swap
  invFun := swap
  left_inv := swap_idem
  right_inv := swap_idem

theorem Ctx.split.left_length_decreasing {T} [HasLin T] {Γ Δ Ξ: Ctx T}
  : split Γ Δ Ξ -> Δ.length ≤ Γ.length
  | nil => le_refl _
  | left _ _ _ HΓ => Nat.succ_le_succ HΓ.left_length_decreasing
  | right _ _ _ HΓ => Nat.le_step HΓ.left_length_decreasing
  | discard _ _ HΓ => Nat.le_step HΓ.left_length_decreasing
  | dup _ _ _ _ _ _ HΓ => Nat.succ_le_succ HΓ.left_length_decreasing

theorem Ctx.ssplit.left_length_decreasing {T} [HasLin T] {Γ Δ Ξ: Ctx T}
  (H: ssplit Γ Δ Ξ): Δ.length ≤ Γ.length
  := H.toSplit.left_length_decreasing

theorem Ctx.split.right_length_decreasing {T} [HasLin T] {Γ Δ Ξ: Ctx T}
  (H: split Γ Δ Ξ): Ξ.length ≤ Γ.length
  := H.swap.left_length_decreasing

theorem Ctx.ssplit.right_length_decreasing {T} [HasLin T] {Γ Δ Ξ: Ctx T}
  (H: ssplit Γ Δ Ξ): Ξ.length ≤ Γ.length
  := H.toSplit.right_length_decreasing

def Ctx.wk {T} [HasLin T] (Γ Δ: Ctx T) := Ctx.split Γ Δ []

def Ctx.var {T} [HasLin T] (Γ: Ctx T) (x: Variable T) := Ctx.wk Γ [x]

@[match_pattern]
def Ctx.wk.nil {T} [HasLin T]: @Ctx.wk T _ [] [] := Ctx.split.nil
@[match_pattern]
def Ctx.wk.cons {T} [HasLin T] {Γ Δ: Ctx T}
  : (v l: Variable T) -> (Hl: l ≤ v) -> Ctx.wk Γ Δ -> Ctx.wk (v::Γ) (l::Δ)
  := Ctx.split.left
@[match_pattern]
def Ctx.wk.discard {T} [HasLin T] {Γ Δ: Ctx T}
  : (v: Variable T) -> (Ha: HasLin.aff v) -> Ctx.wk Γ Δ -> Ctx.wk (v::Γ) Δ
  := Ctx.split.discard

def Ctx.split.left_decompose {T} [HasLin T] {Γ Δ Ξ: Ctx T}
  : Ctx.split Γ Δ Ξ
  -> (Δ' Ξ': Ctx T) × Ctx.ssplit Γ Δ' Ξ' × Ctx.wk Δ' Δ × Ctx.wk Ξ' Ξ
  | nil => ⟨[], [], ssplit.nil, wk.nil, wk.nil⟩
  | left v l Hl H => let ⟨Δ', Ξ', HΓ, HΔ, HΞ⟩ := left_decompose H;
    ⟨v::Δ', Ξ', ssplit.left v HΓ, wk.cons v l Hl HΔ, HΞ⟩
  | right v r Hl H => let ⟨Δ', Ξ', HΓ, HΔ, HΞ⟩ := left_decompose H;
    ⟨Δ', v::Ξ', ssplit.right v HΓ, HΔ, wk.cons v r Hl HΞ⟩
  | discard v Ha H => let ⟨Δ', Ξ', HΓ, HΔ, HΞ⟩ := left_decompose H;
    ⟨v::Δ', Ξ', ssplit.left v HΓ, wk.discard v Ha HΔ, HΞ⟩
  | dup v l r Hrel Hl Hr H => let ⟨Δ', Ξ', HΓ, HΔ, HΞ⟩ := left_decompose H;
    ⟨v::Δ', v::Ξ', ssplit.dup v Hrel HΓ, wk.cons v l Hl HΔ, wk.cons v r Hr HΞ⟩

def Ctx.split.right_decompose {T} [HasLin T] {Γ Δ Ξ: Ctx T}
  : Ctx.split Γ Δ Ξ
  -> (Δ' Ξ': Ctx T) × Ctx.ssplit Γ Δ' Ξ' × Ctx.wk Δ' Δ × Ctx.wk Ξ' Ξ
  | nil => ⟨[], [], ssplit.nil, wk.nil, wk.nil⟩
  | left v l Hl H => let ⟨Δ', Ξ', HΓ, HΔ, HΞ⟩ := right_decompose H;
    ⟨v::Δ', Ξ', ssplit.left v HΓ, wk.cons v l Hl HΔ, HΞ⟩
  | right v r Hl H => let ⟨Δ', Ξ', HΓ, HΔ, HΞ⟩ := right_decompose H;
    ⟨Δ', v::Ξ', ssplit.right v HΓ, HΔ, wk.cons v r Hl HΞ⟩
  | discard v Ha H => let ⟨Δ', Ξ', HΓ, HΔ, HΞ⟩ := right_decompose H;
    ⟨Δ', v::Ξ', ssplit.right v HΓ, HΔ, wk.discard v Ha HΞ⟩
  | dup v l r Hrel Hl Hr H => let ⟨Δ', Ξ', HΓ, HΔ, HΞ⟩ := right_decompose H;
    ⟨v::Δ', v::Ξ', ssplit.dup v Hrel HΓ, wk.cons v l Hl HΔ, wk.cons v r Hr HΞ⟩

theorem Ctx.wk.length_decreasing {T} [HasLin T] {Γ Δ: Ctx T} (H: wk Γ Δ)
  : Δ.length ≤ Γ.length
  := Ctx.split.left_length_decreasing H

theorem Ctx.wk.append_false {T} [HasLin T] {Γ: Ctx T} {A}
  (H: wk Γ (A::Γ)): False
  := have H := H.length_decreasing; by simp_arith at H

theorem Ctx.wk.nil_nil {T} [HasLin T] {Γ: Ctx T}
  : wk [] Γ -> Γ = []
  | nil => rfl

def Ctx.wk.refl {T} [HasLin T]
  : (Γ: Ctx T) -> Ctx.wk Γ Γ
  | [] => Ctx.split.nil
  | v::Γ => Ctx.split.left v v (le_refl v) (wk.refl Γ)

instance Ctx.wk.instInhabitedRefl {T} [HasLin T] {Γ: Ctx T}
  : Inhabited (Ctx.wk Γ Γ) where
  default := wk.refl Γ

instance Ctx.wk.instSubsingletonRefl {T} [HasLin T] {Γ: Ctx T}
  : Subsingleton (Ctx.wk Γ Γ) where
  allEq := let rec allEq
  : ∀ {Γ: Ctx T} (HΓ: Ctx.wk Γ Γ) (HΓ': Ctx.wk Γ Γ), HΓ = HΓ'
  | [], nil, nil => rfl
  | _, cons _ _ _ HΓ, cons _ _ _ HΓ' => congrArg _ (allEq HΓ HΓ')
  | _, discard _ _ HΓ, _ | _, _, discard _ _ HΓ => HΓ.append_false.elim
  allEq

--TODO: subsingleton to nil --> nil is terminal object
--TODO: subsingleton from nil

def Ctx.wk.comp {T} [HasLin T] {Γ Δ Ξ: Ctx T}
  : Ctx.wk Γ Δ -> Ctx.wk Δ Ξ -> Ctx.wk Γ Ξ
  | nil, nil => nil
  | cons _ _ Hl HΓ, cons _ _ Hl' HΓ' =>
    cons _ _ (le_trans Hl' Hl) (comp HΓ HΓ')
  | cons _ _ Hl HΓ, discard _ Ha HΓ' =>
    discard _ (Variable.le.aff Hl Ha) (comp HΓ HΓ')
  | discard _ Ha HΓ, H =>
    discard _ Ha (comp HΓ H)

def Ctx.wk.comp_refl {T} [HasLin T] {Γ Δ: Ctx T}
  : (H: Ctx.wk Γ Δ) -> (R: Ctx.wk Δ Δ) -> H.comp R = H
  | nil, nil => rfl
  | cons _ _ _ HΓ, cons _ _ _ HΓ' => congrArg _ (comp_refl HΓ HΓ')
  | discard _ _ HΓ, HΓ' => congrArg _ (comp_refl HΓ HΓ')
  | cons _ _ _ _, discard _ _ HΓ => HΓ.append_false.elim

def Ctx.wk.refl_comp {T} [HasLin T] {Γ Δ: Ctx T}
  : (R: Ctx.wk Γ Γ) -> (H: Ctx.wk Γ Δ) -> R.comp H = H
  | nil, nil => rfl
  | cons _ _ _ HΓ, cons _ _ _ HΓ' => congrArg _ (refl_comp HΓ HΓ')
  | cons _ _ _ HΓ, discard _ _ HΓ' => congrArg _ (refl_comp HΓ HΓ')
  | discard _ _ HΓ, _ => HΓ.append_false.elim

def Ctx.wk.comp_assoc {T} [HasLin T] {Γ Δ Ξ Θ: Ctx T}
  : (X: Ctx.wk Γ Δ)
  -> (Y: Ctx.wk Δ Ξ)
  -> (Z: Ctx.wk Ξ Θ)
  -> (X.comp Y).comp Z = X.comp (Y.comp Z)
  | nil, nil, nil => rfl
  | cons _ _ _ X, cons _ _ _ Y, cons _ _ _ Z => congrArg _ (comp_assoc X Y Z)
  | cons _ _ _ X, cons _ _ _ Y, discard _ _ Z => congrArg _ (comp_assoc X Y Z)
  | cons _ _ _ X, discard _ _ Y, Z => congrArg _ (comp_assoc X Y Z)
  | discard _ _ X, Y, Z => congrArg _ (comp_assoc X Y Z)

def Ctx.wk.antisymm {T} [HasLin T] {Γ Δ: Ctx T}
  : Ctx.wk Γ Δ -> Ctx.wk Δ Γ -> Γ = Δ
  | nil, nil => rfl
  | cons _ _ Hl HΓ, cons _ _ Hl' HΓ' =>
    by rw [antisymm HΓ HΓ', le_antisymm Hl Hl']
  | cons _ _ _ HΓ, discard _ _ HΓ' =>
    have H := le_trans HΓ'.length_decreasing HΓ.length_decreasing;
    by simp_arith at H
  | discard _ _ HΓ, cons _ _ _ HΓ' =>
    have H := le_trans HΓ.length_decreasing HΓ'.length_decreasing;
    by simp_arith at H
  | discard _ _ HΓ, discard _ _ HΓ' =>
    have H := le_trans (Nat.le_step HΓ'.length_decreasing) HΓ.length_decreasing;
    by simp_arith at H

def Ctx.split.right_wk {T} [HasLin T] {Γ Δ: Ctx T}
  : Ctx.split Γ [] Δ → Ctx.wk Γ Δ
  := swap

def Ctx.wk.right_wk {T} [HasLin T] {Γ Δ: Ctx T}
  : Ctx.wk Γ Δ → Ctx.split Γ [] Δ
  := Ctx.split.swap

def Ctx.wk.equiv_right {T} [HasLin T] {Γ Δ: Ctx T}
  : Equiv (Ctx.wk Γ Δ) (Ctx.split Γ [] Δ)
  := Ctx.split.swap_equiv Γ Δ []

instance Ctx.instHasLin {T} [HasLin T]: HasLin (Ctx T) where
  aff Γ := Γ.all HasLin.aff
  rel Γ := Γ.all HasLin.rel

-- def Ctx.split.associate_left_tri {T} [HasLin T] {Γ Δ Ξ Θ Φ: Ctx T}:
--   Ctx.split Γ Δ Ξ → Ctx.split Ξ Θ Φ → (Ψ: _) × Ctx.split Γ Ψ Φ × Ctx.split Ψ Δ Θ
--   | H, nil => ⟨Δ, H, wk.refl Δ⟩
--   | _, _ => sorry

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
