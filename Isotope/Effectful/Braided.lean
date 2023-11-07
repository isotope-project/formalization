import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Braided
import Mathlib.Order.Monotone.Basic

import Isotope.Binoidal.Category
import Isotope.Premonoidal.Category
import Isotope.Premonoidal.Monoidal'
import Isotope.Premonoidal.Braided
import Isotope.Effectful.Category

open CategoryTheory
open PremonoidalCategory
open BinoidalCategory

class BraidedEffectfulCategory (C: Type u)
  [TensorMonoid C]
  [Category (Value C)]
  [PremonoidalCategory (Value C)]
  [MonoidalCategory' (Value C)]
  [Category C]
  [PremonoidalCategory C]
  [ℰ: EffectfulCategory C]
  [𝒱: BraidedPremonoidalCategory (Value C)]
  [𝒞: BraidedPremonoidalCategory C]
where
  inclusion_braiding : ∀X Y, ℰ.inclusion.map' (𝒱.braiding X Y).hom = (𝒞.braiding X Y).hom

class SymmetricEffectfulCategory (C: Type u)
  [TensorMonoid C]
  [Category (Value C)]
  [PremonoidalCategory (Value C)]
  [MonoidalCategory' (Value C)]
  [Category C]
  [PremonoidalCategory C]
  [EffectfulCategory C]
  [SymmetricPremonoidalCategory (Value C)]
  [SymmetricPremonoidalCategory C]
extends BraidedEffectfulCategory C
