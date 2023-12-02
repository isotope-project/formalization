import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Init.Order.Defs

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

inductive ResState
  | ghost
  | value
  | invalid

inductive ResState.valid: ResState -> Prop
  | ghost: ResState.valid ghost
  | value: ResState.valid value

inductive ResState.le: ResState -> ResState -> Prop
  | ghost: ∀ x, ResState.le ghost x
  | value: ResState.le value value
  | invalid: ∀ x, ResState.le x invalid

instance ResState.instPartialOrder: PartialOrder ResState where
  le := ResState.le
  le_refl a := by cases a <;> constructor
  le_trans a b c Hab Hbc := by cases Hab <;> cases Hbc <;> constructor
  le_antisymm a b Hab Hba := by cases Hab <;> cases Hba <;> rfl

instance ResState.instZero: Zero ResState where
  zero := ghost

instance ResState.instOne: One ResState where
  one := value

-- def IntRes := ResState

-- namespace IntRes

-- export ResState (
--   ghost value invalid
--   valid valid.value valid.ghost
--   le le.ghost le.value le.invalid)

-- instance instPartialOrder: PartialOrder IntRes := ResState.instPartialOrder
-- instance instZero: Zero IntRes := ResState.instZero
-- instance instOne: One IntRes := ResState.instOne
-- instance instOrderedAddCommMonoid: OrderedAddCommMonoid IntRes where
--   add
--   | ghost, x | x, ghost => x
--   | invalid, _ | _, invalid => invalid
--   | value, value => value
--   add_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
--   add_comm := by intro a b; cases a <;> cases b <;> rfl
--   zero_add := by intro a; cases a <;> rfl
--   add_zero := by intro a; cases a <;> rfl
--   add_le_add_left a b Hab c
--     := by cases a <;> cases b <;> cases c <;> cases Hab <;> constructor

-- instance instResourceAlgebra: ResourceAlgebra IntRes where
--   valid := valid
--   valid_one := ResState.valid.value
--   valid_zero := ResState.valid.ghost
--   valid_add_left
--     := by intro a b H; cases a <;> cases b <;> cases H <;> constructor
--   valid_add_right
--     := by intro a b H; cases a <;> cases b <;> cases H <;> constructor
--   zero_ne_one := by simp

-- end IntRes

-- def AffRes := ResState

-- namespace AffRes

-- export ResState (
--   ghost value invalid
--   valid valid.value valid.ghost
--   le le.ghost le.value le.invalid)

-- instance instPartialOrder: PartialOrder AffRes := ResState.instPartialOrder
-- instance instZero: Zero AffRes := ResState.instZero
-- instance instOne: One AffRes := ResState.instOne
-- instance instOrderedAddCommMonoid: OrderedAddCommMonoid AffRes where
--   add
--   | ghost, x | x, ghost => x
--   | invalid, _ | _, invalid => invalid
--   | value, value => invalid
--   add_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
--   add_comm := by intro a b; cases a <;> cases b <;> rfl
--   zero_add := by intro a; cases a <;> rfl
--   add_zero := by intro a; cases a <;> rfl
--   add_le_add_left a b Hab c
--     := by cases a <;> cases b <;> cases c <;> cases Hab <;> constructor

-- instance instResourceAlgebra: ResourceAlgebra AffRes where
--   valid := valid
--   valid_one := ResState.valid.value
--   valid_zero := ResState.valid.ghost
--   valid_add_left
--     := by intro a b H; cases a <;> cases b <;> cases H <;> constructor
--   valid_add_right
--     := by intro a b H; cases a <;> cases b <;> cases H <;> constructor
--   zero_ne_one := by simp

-- end AffRes

-- def RelRes := ResState

-- namespace RelRes

-- export ResState (
--   ghost value invalid
--   valid valid.value valid.ghost)

-- instance instPartialOrder: PartialOrder RelRes where
--   le := Eq
--   le_refl := Eq.refl
--   le_trans _ _ _ := Eq.trans
--   le_antisymm _ _ H _ := H

-- instance instZero: Zero RelRes := ResState.instZero
-- instance instOne: One RelRes := ResState.instOne
-- instance instOrderedAddCommMonoid: OrderedAddCommMonoid RelRes where
--   add
--   | ghost, x | x, ghost => x
--   | invalid, _ | _, invalid => invalid
--   | value, value => value
--   add_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
--   add_comm := by intro a b; cases a <;> cases b <;> rfl
--   zero_add := by intro a; cases a <;> rfl
--   add_zero := by intro a; cases a <;> rfl
--   add_le_add_left a b Hab c
--     := by cases a <;> cases b <;> cases c <;> cases Hab <;> constructor

-- instance instResourceAlgebra: ResourceAlgebra RelRes where
--   valid := valid
--   valid_one := ResState.valid.value
--   valid_zero := ResState.valid.ghost
--   valid_add_left
--     := by intro a b H; cases a <;> cases b <;> cases H <;> constructor
--   valid_add_right
--     := by intro a b H; cases a <;> cases b <;> cases H <;> constructor
--   zero_ne_one := by simp

-- end RelRes

-- def LinRes := ResState

-- namespace LinRes

-- export ResState (
--   ghost value invalid
--   valid valid.value valid.ghost)

-- instance instPartialOrder: PartialOrder LinRes where
--   le := Eq
--   le_refl := Eq.refl
--   le_trans _ _ _ := Eq.trans
--   le_antisymm _ _ H _ := H

-- instance instZero: Zero LinRes := ResState.instZero
-- instance instOne: One LinRes := ResState.instOne
-- instance instOrderedAddCommMonoid: OrderedAddCommMonoid LinRes where
--   add
--   | ghost, x | x, ghost => x
--   | invalid, _ | _, invalid => invalid
--   | value, value => invalid
--   add_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
--   add_comm := by intro a b; cases a <;> cases b <;> rfl
--   zero_add := by intro a; cases a <;> rfl
--   add_zero := by intro a; cases a <;> rfl
--   add_le_add_left a b Hab c
--     := by cases a <;> cases b <;> cases c <;> cases Hab <;> constructor

-- instance instResourceAlgebra: ResourceAlgebra LinRes where
--   valid := valid
--   valid_one := ResState.valid.value
--   valid_zero := ResState.valid.ghost
--   valid_add_left
--     := by intro a b H; cases a <;> cases b <;> cases H <;> constructor
--   valid_add_right
--     := by intro a b H; cases a <;> cases b <;> cases H <;> constructor
--   zero_ne_one := by simp

-- end LinRes
