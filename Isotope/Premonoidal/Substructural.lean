import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Braided
import Mathlib.Combinatorics.Quiver.Subquiver

import Isotope.Premonoidal.Category
import Isotope.Premonoidal.Braided

open CategoryTheory
open BinoidalCategory

inductive Linearity
  | relevant
  | affine

open Linearity

--TODO: factor out subcategory...

class SubstructuralPremonoidalCategory (C: Type u)
  [Category C] [O: TensorMonoid C] [𝒞: PremonoidalCategory C]
extends SymmetricPremonoidalCategory C where
  linearity: Linearity -> Set C
  linearity_tensor
    : ∀{A B q}, linearity q A -> linearity q B -> linearity q (A ⊗ B)
  transparency: Linearity -> WideSubquiver C
  transparency_comp
    : ∀{A B C q} {f: A ⟶ B} {g: B ⟶ C},
    transparency q A B f -> transparency q B C g -> transparency q A C (f ≫ g)
  transparency_whiskerLeft
    : ∀{A B C q} {f: A ⟶ B},
    transparency q A B f -> transparency q (C ⊗ A) (C ⊗ B) (C ◁ f)
  transparency_whiskerRight
    : ∀{A B C q} {f: A ⟶ B},
    transparency q A B f -> transparency q (A ⊗ C) (B ⊗ C) (f ▷ C)
  transparency_id: ∀{A q}, transparency q A A (𝟙 A)
  associator_pure: ∀{A B C q}, transparency q _ _ (𝒞.associator A B C).hom
  associator_inv_pure: ∀{A B C q}, transparency q _ _ (𝒞.associator A B C).inv
  leftUnitor_pure: ∀{A q}, transparency q _ _ (𝒞.leftUnitor A).hom
  leftUnitor_inv_pure: ∀{A q}, transparency q _ _ (𝒞.leftUnitor A).inv
  rightUnitor_pure: ∀{A q}, transparency q _ _ (𝒞.rightUnitor A).hom
  rightUnitor_inv_pure: ∀{A q}, transparency q _ _ (𝒞.rightUnitor A).inv
  braiding_pure: ∀{A B q}, transparency q _ _ (braiding A B).hom
  drop: ∀{A}, linearity affine A -> (A ⟶ O.tensorUnit)
  drop_pure: ∀{A H q}, transparency q A O.tensorUnit (drop H)
  split: ∀{A}, linearity relevant A -> (A ⟶ A ⊗ A)
  split_pure: ∀{A H q}, transparency q A (A ⊗ A) (split H)
  split_comm: ∀{A H}, split H ≫ (braiding A A).hom = split H
  split_duplicate_left: ∀{A B HA HB f},
    transparency relevant A B f -> f ≫ split HB = split HA ≫ f ⋉ f
  split_duplicate_right: ∀{A B HA HB f},
    transparency relevant A B f -> f ≫ split HB = split HA ≫ f ⋊ f
  drop_affine: ∀{A B HA HB f},
    transparency affine A B f -> f ≫ drop HB = drop HA
  split_comonoid: ∀{A HAa HAr},
    split HAr ≫ A ◁ drop HAa = (𝒞.rightUnitor A).inv

namespace SubstructuralPremonoidalCategory
