import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Init.Order.Defs

--TODO: class for binary validity relation?
class ResourceAlgebra (T: Type u) extends
  OrderedAddCommMonoid T,
  One T
  where
  -- mandatory separation between values and ghosts
  -- NOTE: if this is not enforced, we're allowed "pure ghost" values which
  -- are always unusable. Or, of course, we could allow using them, in which
  -- case we simply have that they *must* be the unit type...
  -- zero_ne_one: zero ≠ one

  -- emulating a partial commutative monoid
  valid: T -> T -> Prop
  --TODO: do this externally, by saying valid values are valid 0 x?
  -- valid_left: ∀ x y, valid x y → valid 0 x
  -- valid_right: ∀ x y, valid x y → valid 0 y
  -- valid_add: ∀ x y, valid x y → valid 0 (x + y)
  valid_symm: ∀ x y, valid x y → valid y x
  valid_assoc: ∀ x y z, valid x y → valid y z →
    (valid (x + y) z → valid x (y + z))

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

--TODO: subalgebra definition; induces partial order
--TODO: affine subalgebra (strip validity)
--TODO: relevant subalgebra (strip order)
--TODO: linear subalgebra
--TODO: affine/relevant/linear wrappers

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
  valid_symm := by intros; trivial
  valid_assoc := by intros; trivial
