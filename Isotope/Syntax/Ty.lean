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

class InstructionSet (F: Type u) (T: Type v)
  where
  --TODO: enforce instructions only having a single type?
  -- Could prove results for untyped syntax this way...
  inst_ty: F -> Ty T -> Ty T -> Prop
  inst_aff: F -> Ty T -> Ty T -> Prop
  inst_rel: F -> Ty T -> Ty T -> Prop
  inst_cen: F -> Ty T -> Ty T -> Prop

structure InstructionSet.inst {F: Type u} {T: Type v}
  [HasLin T] [InstructionSet F T]
  (f: F) (p: Bool) (q: Transparency) (A B: Ty T) where
  well_typed: inst_ty f A B
  inst_aff: (q.aff → inst_aff f A B)
  inst_rel: (q.rel → inst_rel f A B)
  inst_cen: (p → inst_cen f A B)

def InstructionSet.inst.upgrade {F: Type u} {T: Type v}
  [HasLin T] [InstructionSet F T]
  {f: F} {A B: Ty T} {p q p' q'} (Hp: p ≥ p') (Hq: q ≥ q')
  (H: InstructionSet.inst f p q A B ): InstructionSet.inst f p' q' A B where
  well_typed := H.well_typed
  inst_aff := λ Haff => H.inst_aff (Hq.1 Haff)
  inst_rel := λ Hrel => H.inst_rel (Hq.2 Hrel)
  inst_cen := λ Hcen => H.inst_cen (Hp Hcen)

def HasLin.sublin {T} [HasLin T] {t: T} {l l': Transparency}
  : l ≥ l' -> HasLin.lin t l -> HasLin.lin t l'
  | Hl, H => by
    simp only [lin, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] at *
    exact ⟨H.1 ∘ Hl.1, H.2 ∘ Hl.2⟩
