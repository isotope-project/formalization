import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Braided
import Mathlib.Combinatorics.Quiver.Subquiver

import Isotope.Premonoidal.Category
import Isotope.Premonoidal.Braided
import Isotope.WideSubcategory.Premonoidal

open CategoryTheory
open BinoidalCategory

inductive Linearity
  | relevant
  | affine
  | central

open Linearity

class SubstructuralEffectfulCategory (C: Type u)
  [Category C] [O: TensorMonoid C] [𝒞: PremonoidalCategory C]
extends SymmetricPremonoidalCategory C where
  linearity: Linearity -> Set C
  linearity_tensor
    : ∀{A B q}, linearity q A -> linearity q B -> linearity q (A ⊗ B)
  purity: Linearity -> SymmetricPremonoidalSubcategory C
  drop: ∀{A}, linearity affine A -> (A ⟶ O.tensorUnit)
  drop_pure: ∀{A H q}, (purity q).contains A O.tensorUnit (drop H)
  split: ∀{A}, linearity relevant A -> (A ⟶ A ⊗ A)
  split_pure: ∀{A H q}, (purity q).contains A (A ⊗ A) (split H)
  split_comm: ∀{A H}, split H ≫ (braiding A A).hom = split H
  split_duplicate_left: ∀{A B HA HB f},
    (purity relevant).contains A B f -> f ≫ split HB = split HA ≫ f ⋉ f
  split_duplicate_right: ∀{A B HA HB f},
    (purity relevant).contains A B f -> f ≫ split HB = split HA ≫ f ⋊ f
  drop_affine: ∀{A B HA HB f},
    (purity affine).contains A B f -> f ≫ drop HB = drop HA
  split_comonoid: ∀{A HAa HAr},
    split HAr ≫ A ◁ drop HAa = (𝒞.rightUnitor A).inv

namespace SubstructuralPremonoidalCategory
