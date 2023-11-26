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
  | copy {Γ Δ Ξ} (v l r): HasLin.rel v → l ≤ v → r ≤ v → split Γ Δ Ξ
    → split (v::Γ) (l::Δ) (r::Ξ)

def Ctx.split.swap {T} [HasLin T] {Γ Δ Ξ: Ctx T}
  : split Γ Δ Ξ -> split Γ Ξ Δ
  | nil => nil
  | left v l Hl H => right v l Hl (swap H)
  | right v r Hl H => left v r Hl (swap H)
  | discard v Ha Hl => discard v Ha (swap Hl)
  | copy v l r H Hl Hr HΓ
    => copy v r l H Hr Hl (swap HΓ)

def Ctx.split.swap_idem {T} [HasLin T] {Γ Δ Ξ: Ctx T}
  : Function.LeftInverse (@swap T _ Γ Δ Ξ) (@swap T _ Γ Ξ Δ)
  | nil => rfl
  | left v l Hl HΓ => by simp [swap, swap_idem HΓ]
  | right v r Hr HΓ => by simp [swap, swap_idem HΓ]
  | discard v Ha HΓ => by simp [swap, swap_idem HΓ]
  | copy v l r Har Hl Hr HΓ => by simp [swap, swap_idem HΓ]

def Ctx.split.swap_equiv {T} [HasLin T] (Γ Δ Ξ: Ctx T)
  : Equiv (split Γ Δ Ξ) (split Γ Ξ Δ) where
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
  | copy _ _ _ _ _ _ HΓ => Nat.succ_le_succ HΓ.left_length_decreasing

theorem Ctx.split.right_length_decreasing {T} [HasLin T] {Γ Δ Ξ: Ctx T}
  (H: split Γ Δ Ξ): Ξ.length ≤ Γ.length
  := H.swap.left_length_decreasing

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

def Ctx.wk.length_decreasing {T} [HasLin T] {Γ Δ: Ctx T} (H: wk Γ Δ)
  : Δ.length ≤ Γ.length
  := Ctx.split.left_length_decreasing H

def Ctx.wk.refl {T} [HasLin T]
  : (Γ: Ctx T) -> Ctx.wk Γ Γ
  | [] => Ctx.split.nil
  | v::Γ => Ctx.split.left v v (le_refl v) (wk.refl Γ)

instance Ctx.wk.instInhabitedRefl {T} [HasLin T] {Γ: Ctx T}
  : Inhabited (Ctx.wk Γ Γ) where
  default := wk.refl Γ

def Ctx.wk.trans {T} [HasLin T] {Γ Δ Ξ: Ctx T}
  : Ctx.wk Γ Δ -> Ctx.wk Δ Ξ -> Ctx.wk Γ Ξ
  | Ctx.split.nil, Ctx.split.nil => nil
  | cons _ _ Hl HΓ, cons _ _ Hl' HΓ' =>
    cons _ _ (le_trans Hl' Hl) (trans HΓ HΓ')
  | cons _ _ Hl HΓ, discard _ Ha HΓ' =>
    discard _ (Variable.le.aff Hl Ha) (trans HΓ HΓ')
  | discard _ Ha HΓ, H =>
    discard _ Ha (trans HΓ H)

-- def Ctx.wk.trans_refl {T} [HasLin T] {Γ Δ: Ctx T}
--   : (H: Ctx.wk Γ Δ) -> (R: Ctx.wk Δ Δ) -> H.trans R = H
--   := sorry

-- def Ctx.wk.refl_trans {T} [HasLin T] {Γ Δ: Ctx T}
--   : (R: Ctx.wk Γ Γ) -> (H: Ctx.wk Γ Δ) -> R.trans H = H
--   := sorry

-- instance Ctx.wk.instSubsingletonRefl {T} [HasLin T] {Γ: Ctx T}
--   : Subsingleton (Ctx.wk Γ Γ)
--   := sorry

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
    (s: Ctx.split Θ ΘΓ Θx)
    (H: subst ΘΓ Γ)
    (t: Term Θx x)
    : subst Θ (x::Γ)
