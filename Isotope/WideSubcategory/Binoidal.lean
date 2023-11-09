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
    (Z: C) -> contains X Y f -> contains (Z ⊗ X) (Z ⊗ Y) (Z ◁ f)
  whiskerRight: ∀{X Y f},
    contains X Y f -> (Z: C) -> contains (X ⊗ Z) (Y ⊗ Z) (f ▷ Z)

theorem BinoidalSubcategory.ext_wide {C}
  [Category C] [TensorProduct C] [BinoidalCategory C]
  {L R: BinoidalSubcategory C}
  (H: L.toWideSubcategory = R.toWideSubcategory): L = R
  := by cases L; cases R; cases H; rfl

theorem BinoidalSubcategory.ext {C}
  [Category C] [TensorProduct C] [BinoidalCategory C]
  {L R: BinoidalSubcategory C}
  (H: L.contains = R.contains): L = R
  := ext_wide (WideSubcategory.ext H)

instance BinoidalSubcategory.instPartialOrder {C}
  [Category C] [TensorProduct C] [BinoidalCategory C]
  : PartialOrder (BinoidalSubcategory C)
  where
  le L R := L.contains ≤ R.contains
  le_refl _ _ _ := le_refl _
  le_trans _ _ _ HL HR X Y := le_trans (HL X Y) (HR X Y)
  le_antisymm _ _ HL HR := ext (le_antisymm HL HR)

theorem BinoidalSubcategory.le_ext {C}
  [Category C] [TensorProduct C] [BinoidalCategory C]
  {L R: BinoidalSubcategory C}
  (H: L.contains ≤ R.contains): L ≤ R
  := H

theorem BinoidalSubcategory.le_ext' {C}
  [Category C] [TensorProduct C] [BinoidalCategory C]
  {L R: BinoidalSubcategory C}
  (H: L.toWideSubcategory ≤ R.toWideSubcategory): L ≤ R
  := H

instance BinoidalSubcategory.instBot (C)
  [Category C] [TensorProduct C] [B: BinoidalCategory C]
  : Bot (BinoidalSubcategory C) where
  bot := {
    toWideSubcategory := ⊥
    whiskerLeft := λZ ⟨HXY, Hf⟩ => by
      cases HXY; cases Hf; exists rfl; simp [B.whiskerLeft_id]
    whiskerRight := λ⟨HXY, Hf⟩ Z => by
      cases HXY; cases Hf; exists rfl; simp [B.id_whiskerRight]
  }

instance BinoidalSubcategory.instOrderBot (C)
  [Category C] [TensorProduct C] [BinoidalCategory C]
  : OrderBot (BinoidalSubcategory C) where
  bot_le _ := le_ext' bot_le

instance BinoidalSubcategory.instTop (C)
  [Category C] [TensorProduct C] [BinoidalCategory C]
  : Top (BinoidalSubcategory C) where
  top := {
    toWideSubcategory := ⊤
    whiskerLeft := λ _ _ => True.intro
    whiskerRight := λ _ _ => True.intro
  }

instance BinoidalSubcategory.instOrderTop (C)
  [Category C] [TensorProduct C] [BinoidalCategory C]
  : OrderTop (BinoidalSubcategory C) where
  le_top _ := le_ext' le_top

instance BinoidalSubcategory.instInf (C)
  [Category C] [TensorProduct C] [BinoidalCategory C]
  : Inf (BinoidalSubcategory C) where
  inf L R := {
    toWideSubcategory := L.toWideSubcategory ⊓ R.toWideSubcategory
    whiskerLeft := λZ Hf => ⟨L.whiskerLeft Z Hf.1, R.whiskerLeft Z Hf.2⟩
    whiskerRight := λHf Z => ⟨L.whiskerRight Hf.1 Z, R.whiskerRight Hf.2 Z⟩
  }

instance BinoidalSubcategory.instSemilatticeInf (C)
  [Category C] [TensorProduct C] [BinoidalCategory C]
  : SemilatticeInf (BinoidalSubcategory C) where
  inf_le_left _ _ := le_ext' inf_le_left
  inf_le_right _ _ := le_ext' inf_le_right
  le_inf _ _ _ HL HR := le_ext' (le_inf HL HR)

-- instance BinoidalSubcategory.instSInf (C)
--   [Category C] [TensorProduct C] [BinoidalCategory C]
--   : InfSet (BinoidalSubcategory C) where
--   sInf S := {
--     toWideSubcategory := sInf {(W.toWideSubcategory) | W ∈ S}
--     whiskerLeft := sorry
--     whiskerRight := sorry
--   }

--TODO: instSup

--TODO: instCompleteSemilatticeInf

--TODO: instCompleteLattice

def CenterQuiver (C)
  [Category C] [TensorProduct C] [BinoidalCategory C]
  : WideSubquiver C
  := λ_ _ f => Central f

def CentralQuiver {C}
  [Category C] [TensorProduct C] [BinoidalCategory C]
  (W: WideSubquiver C)
  := W ≤ CenterQuiver C

def WideSubcategory.Center (C)
  [Category C] [TensorProduct C] [BinoidalCategory C]
  : WideSubcategory C where
  contains := CenterQuiver C
  contains_comp Hf Hg := Central.comp Hf Hg
  contains_id X := Central.id X
