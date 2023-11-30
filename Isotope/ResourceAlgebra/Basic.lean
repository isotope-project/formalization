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
  valid_add_left: ∀ x y, valid (x + y) → valid x
  valid_add_right: ∀ x y, valid (x + y) → valid y
  zero_le_one: zero ≤ one
  add_increasing: ∀x y: T, x + y ≥ y
  -- TODO: allow purely "ghostly" values?
  -- or would this be by making 1 invalid?
  zero_ne_one: zero ≠ one
