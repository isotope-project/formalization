import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Init.Order.Defs

import Isotope.Syntax.Ty

--TODO: class for binary validity relation?
class ResourceAlgebra (T: Type u) extends
  OrderedAddCommMonoid T
  -- ,One T
  where
  -- mandatory separation between values and ghosts
  -- NOTE: if this is not enforced, we're allowed "pure ghost" values which
  -- are always unusable. Or, of course, we could allow using them, in which
  -- case we simply have that they *must* be the unit type...
  -- zero_ne_one: zero ≠ one

  -- Emulating a partial commutative monoid via `valid`:
  valid: T -> T -> Prop
  valid_zero: valid 0 0
  -- valid_zero_one: valid 0 1
  valid_symm: ∀ x y, valid x y → valid y x
  valid_assoc: ∀ x y z, valid x y → valid y z →
    (valid (x + y) z → valid x (y + z))

  -- valid_one_zero: valid 1 0 := valid_symm 0 1 valid_zero_one

  -- TODO: do this externally, by saying valid values are valid 0 x?
  -- valid_left: ∀ x y, valid x y → valid 0 x
  -- valid_right: ∀ x y, valid x y → valid 0 y
  -- TODO: do *this* externally too?
  -- i.e. have valid' x y := valid x y ∧ valid 0 (x + y)?
  valid_add: ∀ x y, valid x y → valid 0 (x + y)

def ResourceAlgebra.valid_assoc' {T: Type u} [ResourceAlgebra T]
  : ∀x y z: T,  valid x y → valid y z → valid x (y + z) → valid (x + y) z
  := by
    intros
    apply valid_symm
    rw [add_comm]
    apply valid_assoc
    apply valid_symm
    assumption
    apply valid_symm
    assumption
    rw [add_comm]
    apply valid_symm
    assumption

--TODO: subalgebra definition; induces (guess what) a complete semilattice!

def ResourceAlgebra.affineAlgebra (T: Type u) [R: ResourceAlgebra T]
  : ResourceAlgebra T where
  valid x y := R.valid x y ∧ (x = 0 ∨ y = 0)
  valid_zero := ⟨R.valid_zero, Or.inl rfl⟩
  valid_symm _ _ | ⟨Hr, Hxy⟩ => ⟨R.valid_symm _ _ Hr, Hxy.elim Or.inr Or.inl⟩
  valid_assoc _ _ _
    | ⟨Hr1, Or.inl Hx⟩, ⟨Hr2, _⟩, ⟨Hr3, _⟩ =>
      ⟨R.valid_assoc _ _ _ Hr1 Hr2 Hr3, Or.inl Hx⟩
    | ⟨Hr1, Or.inr Hy⟩, ⟨Hr2, _⟩, ⟨Hr3, Or.inr Hz⟩ =>
      ⟨R.valid_assoc _ _ _ Hr1 Hr2 Hr3, by simp [Hy, Hz]⟩
    | ⟨Hr1, Or.inr Hy⟩, ⟨Hr2, _⟩, ⟨Hr3, Or.inl Hxy⟩ =>
      ⟨R.valid_assoc _ _ _ Hr1 Hr2 Hr3, by rw [<-Hxy]; simp [Hy]⟩
  valid_add _ _ | ⟨Hr, _⟩ => ⟨R.valid_add _ _ Hr, Or.inl rfl⟩

def ResourceAlgebra.relevantAlgebra (T: Type u) [R: ResourceAlgebra T]
  : ResourceAlgebra T where
  le := Eq
  le_refl := Eq.refl
  le_trans _ _ _ := Eq.trans
  le_antisymm _ _ H _ := H
  lt _ _ := False
  lt_iff_le_not_le _ _ := ⟨False.elim, λ⟨H, C⟩ => C H.symm⟩
  add_le_add_left _ _ | rfl, _ => rfl
  valid := R.valid
  valid_zero := R.valid_zero
  valid_symm := R.valid_symm
  valid_assoc := R.valid_assoc
  valid_add := R.valid_add

def ResourceAlgebra.linearAlgebra (T: Type u) [R: ResourceAlgebra T]
  : ResourceAlgebra T where
  le := Eq
  le_refl := Eq.refl
  le_trans _ _ _ := Eq.trans
  le_antisymm _ _ H _ := H
  lt _ _ := False
  lt_iff_le_not_le _ _ := ⟨False.elim, λ⟨H, C⟩ => C H.symm⟩
  add_le_add_left _ _ | rfl, _ => rfl
  valid x y := R.valid x y ∧ (x = 0 ∨ y = 0)
  valid_zero := ⟨R.valid_zero, Or.inl rfl⟩
  valid_symm _ _ | ⟨Hr, Hxy⟩ => ⟨R.valid_symm _ _ Hr, Hxy.elim Or.inr Or.inl⟩
  valid_assoc _ _ _
    | ⟨Hr1, Or.inl Hx⟩, ⟨Hr2, _⟩, ⟨Hr3, _⟩ =>
      ⟨R.valid_assoc _ _ _ Hr1 Hr2 Hr3, Or.inl Hx⟩
    | ⟨Hr1, Or.inr Hy⟩, ⟨Hr2, _⟩, ⟨Hr3, Or.inr Hz⟩ =>
      ⟨R.valid_assoc _ _ _ Hr1 Hr2 Hr3, by simp [Hy, Hz]⟩
    | ⟨Hr1, Or.inr Hy⟩, ⟨Hr2, _⟩, ⟨Hr3, Or.inl Hxy⟩ =>
      ⟨R.valid_assoc _ _ _ Hr1 Hr2 Hr3, by rw [<-Hxy]; simp [Hy]⟩
  valid_add _ _ | ⟨Hr, _⟩ => ⟨R.valid_add _ _ Hr, Or.inl rfl⟩

--TODO: the linear algebra is the smallest possible resource algebra

def ResourceAlgebra.transparentAlgebra (T: Type u) [R: ResourceAlgebra T]
  : Transparency -> ResourceAlgebra T
  | ⟨true, true⟩ => R
  | ⟨true, false⟩ => R.affineAlgebra
  | ⟨false, true⟩ => R.relevantAlgebra
  | ⟨false, false⟩ => R.linearAlgebra

def LinT (_: Transparency) (T: Type u) := T

instance LinT.instResourceAlgebra (T: Type u) [ResourceAlgebra T]
  (q: Transparency): ResourceAlgebra (LinT q T)
  := ResourceAlgebra.transparentAlgebra T q

def Aff (T: Type u) := T
def Rel (T: Type u) := T
def Lin (T: Type u) := T

instance Aff.instResourceAlgebra {T: Type u} [ResourceAlgebra T]
  : ResourceAlgebra (Aff T) := ResourceAlgebra.affineAlgebra T
instance Rel.instResourceAlgebra {T: Type u} [ResourceAlgebra T]
  : ResourceAlgebra (Rel T) := ResourceAlgebra.relevantAlgebra T
instance Lin.instResourceAlgebra {T: Type u} [ResourceAlgebra T]
  : ResourceAlgebra (Lin T) := ResourceAlgebra.linearAlgebra T

inductive VarState
  | ghost
  | value

inductive VarState.le: VarState -> VarState -> Prop
  | ghost: ∀ x, le ghost x
  | value: VarState.le value value

instance VarState.instPartialOrder: PartialOrder VarState where
  le := VarState.le
  le_refl a := by cases a <;> constructor
  le_trans a b c Hab Hbc := by cases Hab <;> cases Hbc <;> constructor
  le_antisymm a b Hab Hba := by cases Hab <;> cases Hba <;> rfl

instance VarState.instZero: Zero VarState where
  zero := ghost
instance VarState.instOne: One VarState where
  one := value
instance VarState.instOrderedAddCommMonoid: OrderedAddCommMonoid VarState where
  add
  | ghost, x | x, ghost => x
  | value, value => value
  add_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  add_comm := by intro a b; cases a <;> cases b <;> rfl
  zero_add := by intro a; cases a <;> rfl
  add_zero := by intro a; cases a <;> rfl
  add_le_add_left a b Hab c
    := by cases a <;> cases b <;> cases c <;> cases Hab <;> constructor
instance VarState.instResourceAlgebra: ResourceAlgebra VarState where
  valid _ _ := true
  valid_zero := by trivial
  -- valid_zero_one := by trivial
  valid_symm := by intros; trivial
  valid_assoc := by intros; trivial
  valid_add := by intros; trivial

--TODO: resource algebra on types
--TODO: relevant/affine resource algebras on types; products of subalgebras
