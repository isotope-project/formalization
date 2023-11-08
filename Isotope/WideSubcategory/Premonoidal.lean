import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Braided
import Mathlib.Combinatorics.Quiver.Subquiver

import Isotope.WideSubcategory.Basic
import Isotope.WideSubcategory.Binoidal
import Isotope.Binoidal.Category
import Isotope.Premonoidal.Category
import Isotope.Premonoidal.Braided

open CategoryTheory
open BinoidalCategory
open PremonoidalCategory

class SymmetricPremonoidalSubcategory (C)
  [Category C] [TensorMonoid C] [M: PremonoidalCategory C]
  [B: SymmetricPremonoidalCategory C]
  extends BinoidalSubcategory C where
  associator: ∀(X Y Z), contains _ _ (M.associator X Y Z).hom
  associator_inv: ∀(X Y Z), contains _ _ (M.associator X Y Z).inv
  leftUnitor: ∀(X), contains _ _ (M.leftUnitor X).hom
  leftUnitor_inv: ∀(X), contains _ _ (M.leftUnitor X).inv
  rightUnitor: ∀(X), contains _ _ (M.rightUnitor X).hom
  rightUnitor_inv: ∀(X), contains _ _ (M.rightUnitor X).inv
  braiding: ∀(X Y), contains _ _ (B.braiding X Y).hom

inductive SymmetricPremonoidalCategory.skeleton (C)
  [Category C] [TensorMonoid C] [M: PremonoidalCategory C]
  [B: SymmetricPremonoidalCategory C]
  : WideSubquiver C
  | id (X: C): skeleton C X X (𝟙 X)
  | comp {X Y Z f g}: skeleton C X Y f
    -> skeleton C Y Z g
    -> skeleton C X Z (f ≫ g)
  | whiskerLeft {X Y f} (Z): skeleton C X Y f
    -> skeleton C _ _ (Z ◁ f)
  | whiskerRight {X Y f}: skeleton C X Y f -> (Z: C)
    -> skeleton C _ _ (f ▷ Z)
  | associator (X Y Z): skeleton C _ _ (M.associator X Y Z).hom
  | associator_inv (X Y Z): skeleton C _ _ (M.associator X Y Z).inv
  | leftUnitor (X): skeleton C _ _ (M.leftUnitor X).hom
  | leftUnitor_inv (X): skeleton C _ _ (M.leftUnitor X).inv
  | rightUnitor (X): skeleton C _ _ (M.rightUnitor X).hom
  | rightUnitor_inv (X): skeleton C _ _ (M.rightUnitor X).inv
  | braiding (X Y): skeleton C _ _ (B.braiding X Y).hom

instance SymmetricPremonoidalCategory.instBot {C}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C]
  : Bot (SymmetricPremonoidalSubcategory C) where
  bot := {
    contains := SymmetricPremonoidalCategory.skeleton C
    contains_comp := SymmetricPremonoidalCategory.skeleton.comp
    contains_id := SymmetricPremonoidalCategory.skeleton.id
    whiskerLeft := SymmetricPremonoidalCategory.skeleton.whiskerLeft
    whiskerRight := SymmetricPremonoidalCategory.skeleton.whiskerRight
    associator := SymmetricPremonoidalCategory.skeleton.associator
    associator_inv := SymmetricPremonoidalCategory.skeleton.associator_inv
    leftUnitor := SymmetricPremonoidalCategory.skeleton.leftUnitor
    leftUnitor_inv := SymmetricPremonoidalCategory.skeleton.leftUnitor_inv
    rightUnitor := SymmetricPremonoidalCategory.skeleton.rightUnitor
    rightUnitor_inv := SymmetricPremonoidalCategory.skeleton.rightUnitor_inv
    braiding := SymmetricPremonoidalCategory.skeleton.braiding
  }

theorem SymmetricPremonoidalCategory.ext_binoidal {C}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C]
  {L R: SymmetricPremonoidalSubcategory C}
  (H: L.toBinoidalSubcategory = R.toBinoidalSubcategory): L = R
  := by cases L; cases R; cases H; rfl

theorem SymmetricPremonoidalCategory.ext {C}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C]
  {L R: SymmetricPremonoidalSubcategory C}
  (H: L.contains = R.contains): L = R
  := ext_binoidal (BinoidalSubcategory.ext H)

instance SymmetricPremonoidalCategory.instPartialOrder {C}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C]
  : PartialOrder (SymmetricPremonoidalSubcategory C) where
  le L R := L.contains ≤ R.contains
  le_refl _ _ _ := le_refl _
  le_trans _ _ _ HL HR X Y := le_trans (HL X Y) (HR X Y)
  le_antisymm _ _ HL HR := ext (le_antisymm HL HR)

theorem SymmetricPremonoidalCategory.skeleton.inclusion
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  [B: SymmetricPremonoidalCategory C]
  (W: SymmetricPremonoidalSubcategory C)
  {X Y f}
  (H: SymmetricPremonoidalCategory.skeleton C X Y f)
  : W.contains X Y f := by induction H with
  | id X => exact W.contains_id X
  | comp _ _ If Ig => exact W.contains_comp If Ig
  | whiskerLeft Z _ If => exact W.whiskerLeft Z If
  | whiskerRight _ Z If => exact W.whiskerRight If Z
  | associator => apply W.associator
  | associator_inv => apply W.associator_inv
  | leftUnitor => apply W.leftUnitor
  | leftUnitor_inv => apply W.leftUnitor_inv
  | rightUnitor => apply W.rightUnitor
  | rightUnitor_inv => apply W.rightUnitor_inv
  | braiding => apply W.braiding

instance SymmetricPremonoidalCategory.instOrderBot {C}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C]
  : OrderBot (SymmetricPremonoidalSubcategory C) where
  bot_le W _ _ _ Hf := Hf.inclusion W

--TODO: infimum

class SymmetricMonoidalSubcategory (C)
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C]
  extends SymmetricPremonoidalSubcategory C where
  sliding: ∀{X Y X' Y' f g},
    contains X Y f -> contains X' Y' g -> OrdCommute f g

class CentralSubcategory (C)
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  [B: SymmetricPremonoidalCategory C]
  extends SymmetricMonoidalSubcategory C where
  centrality: ∀{X Y f}, contains X Y f -> Central f

def CentralSubcategory.mk' {C}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C]
  (S: SymmetricPremonoidalSubcategory C)
  (centrality: ∀{X Y f}, S.contains X Y f -> Central f)
  : CentralSubcategory C where
  toSymmetricPremonoidalSubcategory := S
  sliding Hf _ := (centrality Hf).commute_left _
  centrality := centrality
