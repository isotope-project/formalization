import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Init.Order.Defs

class ResourceAlgebra (T: Type u) extends
  OrderedAddCommMonoid T,
  One T
  where
  -- emulating a partial commutative monoid
  valid: T -> Prop
  valid_one: valid 1
  valid_zero: valid 0
  --TODO: not strictly necessary, but makes it easier to define splits...
  valid_add_left: ∀ x y, valid (x + y) → valid x
  valid_add_right: ∀ x y, valid (x + y) → valid y
  -- TODO: allow purely "ghostly" values?
  -- or would this be by making 1 invalid?
  zero_ne_one: zero ≠ one

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

def IntRes := ResState

namespace IntRes

export ResState (
  ghost value invalid
  valid valid.value valid.ghost
  le le.ghost le.value le.invalid)

instance instPartialOrder: PartialOrder IntRes := ResState.instPartialOrder
instance instZero: Zero IntRes := ResState.instZero
instance instOne: One IntRes := ResState.instOne
instance instOrderedAddCommMonoid: OrderedAddCommMonoid IntRes where
  add
  | ghost, x | x, ghost => x
  | invalid, _ | _, invalid => invalid
  | value, value => value
  add_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  add_comm := by intro a b; cases a <;> cases b <;> rfl
  zero_add := by intro a; cases a <;> rfl
  add_zero := by intro a; cases a <;> rfl
  add_le_add_left a b Hab c
    := by cases a <;> cases b <;> cases c <;> cases Hab <;> constructor

instance instResourceAlgebra: ResourceAlgebra IntRes where
  valid := valid
  valid_one := ResState.valid.value
  valid_zero := ResState.valid.ghost
  valid_add_left
    := by intro a b H; cases a <;> cases b <;> cases H <;> constructor
  valid_add_right
    := by intro a b H; cases a <;> cases b <;> cases H <;> constructor
  zero_ne_one := by simp

end IntRes

def AffRes := ResState

namespace AffRes

export ResState (
  ghost value invalid
  valid valid.value valid.ghost
  le le.ghost le.value le.invalid)

instance instPartialOrder: PartialOrder AffRes := ResState.instPartialOrder
instance instZero: Zero AffRes := ResState.instZero
instance instOne: One AffRes := ResState.instOne
instance instOrderedAddCommMonoid: OrderedAddCommMonoid AffRes where
  add
  | ghost, x | x, ghost => x
  | invalid, _ | _, invalid => invalid
  | value, value => invalid
  add_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  add_comm := by intro a b; cases a <;> cases b <;> rfl
  zero_add := by intro a; cases a <;> rfl
  add_zero := by intro a; cases a <;> rfl
  add_le_add_left a b Hab c
    := by cases a <;> cases b <;> cases c <;> cases Hab <;> constructor

instance instResourceAlgebra: ResourceAlgebra AffRes where
  valid := valid
  valid_one := ResState.valid.value
  valid_zero := ResState.valid.ghost
  valid_add_left
    := by intro a b H; cases a <;> cases b <;> cases H <;> constructor
  valid_add_right
    := by intro a b H; cases a <;> cases b <;> cases H <;> constructor
  zero_ne_one := by simp

end AffRes

def RelRes := ResState

namespace RelRes

export ResState (
  ghost value invalid
  valid valid.value valid.ghost)

instance instPartialOrder: PartialOrder RelRes where
  le := Eq
  le_refl := Eq.refl
  le_trans _ _ _ := Eq.trans
  le_antisymm _ _ H _ := H

instance instZero: Zero RelRes := ResState.instZero
instance instOne: One RelRes := ResState.instOne
instance instOrderedAddCommMonoid: OrderedAddCommMonoid RelRes where
  add
  | ghost, x | x, ghost => x
  | invalid, _ | _, invalid => invalid
  | value, value => value
  add_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  add_comm := by intro a b; cases a <;> cases b <;> rfl
  zero_add := by intro a; cases a <;> rfl
  add_zero := by intro a; cases a <;> rfl
  add_le_add_left a b Hab c
    := by cases a <;> cases b <;> cases c <;> cases Hab <;> constructor

instance instResourceAlgebra: ResourceAlgebra RelRes where
  valid := valid
  valid_one := ResState.valid.value
  valid_zero := ResState.valid.ghost
  valid_add_left
    := by intro a b H; cases a <;> cases b <;> cases H <;> constructor
  valid_add_right
    := by intro a b H; cases a <;> cases b <;> cases H <;> constructor
  zero_ne_one := by simp

end RelRes

def LinRes := ResState

namespace LinRes

export ResState (
  ghost value invalid
  valid valid.value valid.ghost)

instance instPartialOrder: PartialOrder LinRes where
  le := Eq
  le_refl := Eq.refl
  le_trans _ _ _ := Eq.trans
  le_antisymm _ _ H _ := H

instance instZero: Zero LinRes := ResState.instZero
instance instOne: One LinRes := ResState.instOne
instance instOrderedAddCommMonoid: OrderedAddCommMonoid LinRes where
  add
  | ghost, x | x, ghost => x
  | invalid, _ | _, invalid => invalid
  | value, value => invalid
  add_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  add_comm := by intro a b; cases a <;> cases b <;> rfl
  zero_add := by intro a; cases a <;> rfl
  add_zero := by intro a; cases a <;> rfl
  add_le_add_left a b Hab c
    := by cases a <;> cases b <;> cases c <;> cases Hab <;> constructor

instance instResourceAlgebra: ResourceAlgebra LinRes where
  valid := valid
  valid_one := ResState.valid.value
  valid_zero := ResState.valid.ghost
  valid_add_left
    := by intro a b H; cases a <;> cases b <;> cases H <;> constructor
  valid_add_right
    := by intro a b H; cases a <;> cases b <;> cases H <;> constructor
  zero_ne_one := by simp

end LinRes
