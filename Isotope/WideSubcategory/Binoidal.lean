import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Braided
import Mathlib.Combinatorics.Quiver.Subquiver

import Isotope.WideSubcategory.Basic
import Isotope.Binoidal.Category

open CategoryTheory
open BinoidalCategory

class BinoidalSubcategory (C)
  [Category C] [TensorProduct C] [BinoidalCategory C]
  extends WideSubcategory C where
  whiskerLeft: ∀{X Y f},
    contains X Y f -> (Z: C) -> contains (Z ⊗ X) (Z ⊗ Y) (Z ◁ f)
  whiskerRight: ∀{X Y f},
    (Z: C) -> contains X Y f -> contains (X ⊗ Z) (Y ⊗ Z) (f ▷ Z)

def BinoidalSubcategory.discrete (C)
  [Category C] [TensorProduct C] [B: BinoidalCategory C]
  : BinoidalSubcategory C where
  toWideSubcategory := WideSubcategory.discrete C
  whiskerLeft := λ⟨HXY, Hf⟩ Z => by
    cases HXY; cases Hf; exists rfl; simp [B.whiskerLeft_id]
  whiskerRight := λZ ⟨HXY, Hf⟩ => by
    cases HXY; cases Hf; exists rfl; simp [B.id_whiskerRight]

def BinoidalSubcategory.full (C)
  [Category C] [TensorProduct C] [BinoidalCategory C]
  : BinoidalSubcategory C where
  toWideSubcategory := WideSubcategory.full C
  whiskerLeft _ _ := True.intro
  whiskerRight _ _ := True.intro
