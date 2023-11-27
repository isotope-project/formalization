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
