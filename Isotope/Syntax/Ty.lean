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

instance Transparency.instHasLin: HasLin Transparency where
  aff := Transparency.aff
  rel := Transparency.rel

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
