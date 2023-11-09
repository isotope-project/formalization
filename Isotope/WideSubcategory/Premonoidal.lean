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
open BraidedPremonoidalCategory
open SymmetricPremonoidalCategory

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

theorem SymmetricPremonoidalSubcategory.ext_binoidal {C}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C]
  {L R: SymmetricPremonoidalSubcategory C}
  (H: L.toBinoidalSubcategory = R.toBinoidalSubcategory): L = R
  := by cases L; cases R; cases H; rfl

theorem SymmetricPremonoidalSubcategory.ext {C}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C]
  {L R: SymmetricPremonoidalSubcategory C}
  (H: L.contains = R.contains): L = R
  := ext_binoidal (BinoidalSubcategory.ext H)

instance SymmetricPremonoidalSubcategory.instPartialOrder {C}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C]
  : PartialOrder (SymmetricPremonoidalSubcategory C) where
  le L R := L.contains ≤ R.contains
  le_refl _ _ _ := le_refl _
  le_trans _ _ _ HL HR X Y := le_trans (HL X Y) (HR X Y)
  le_antisymm _ _ HL HR := ext (le_antisymm HL HR)

theorem SymmetricPremonoidalSubcategory.le_ext {C}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C]
  {L R: SymmetricPremonoidalSubcategory C}
  (H: L.contains ≤ R.contains): L ≤ R
  := H

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

theorem SymmetricMonoidalSubcategory.ext_premonoidal {C}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C]
  {L R: SymmetricMonoidalSubcategory C}
  (H: L.toSymmetricPremonoidalSubcategory = R.toSymmetricPremonoidalSubcategory)
  : L = R := by cases L; cases R; cases H; rfl

theorem SymmetricMonoidalSubcategory.ext {C}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C]
  {L R: SymmetricMonoidalSubcategory C}
  (H: L.contains = R.contains): L = R
  := ext_premonoidal (SymmetricPremonoidalSubcategory.ext H)

instance SymmetricMonoidalSubcategory.instPartialOrder {C}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C]
  : PartialOrder (SymmetricMonoidalSubcategory C) where
  le L R := L.contains ≤ R.contains
  le_refl _ _ _ := le_refl _
  le_trans _ _ _ HL HR X Y := le_trans (HL X Y) (HR X Y)
  le_antisymm _ _ HL HR := ext (le_antisymm HL HR)

theorem SymmetricMonoidalSubcategory.le_ext {C}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C]
  {L R: SymmetricMonoidalSubcategory C}
  (H: L.contains ≤ R.contains): L ≤ R
  := H

theorem SymmetricPremonoidalCategory.skeleton.central
  [Category C] [TensorMonoid C] [M: PremonoidalCategory C]
  [B: SymmetricPremonoidalCategory C]
  {X Y f}
  (H: SymmetricPremonoidalCategory.skeleton C X Y f)
  : Central f := by induction H with
  | id X => apply Central.id
  | comp _ _ If Ig => exact If.comp Ig
  | whiskerLeft Z _ If => exact If.whiskerLeft Z
  | whiskerRight _ Z If => exact If.whiskerRight Z
  | associator => exact (M.associator_centrality _ _ _).hom
  | associator_inv => exact (M.associator_centrality _ _ _).inv
  | leftUnitor => exact (M.leftUnitor_centrality _).hom
  | leftUnitor_inv => exact (M.leftUnitor_centrality _).inv
  | rightUnitor => exact (M.rightUnitor_centrality _).hom
  | rightUnitor_inv => exact (M.rightUnitor_centrality _).inv
  | braiding => exact (B.braiding_centrality _ _).hom

instance SymmetricMonoidalSubcategory.instBot {C}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C]
  : Bot (SymmetricMonoidalSubcategory C) where
  bot := {
    toSymmetricPremonoidalSubcategory := ⊥
    sliding := λHf _ => Hf.central.commute_left _
  }

instance SymmetricMonoidalSubcategory.instOrderBot {C}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C]
  : OrderBot (SymmetricMonoidalSubcategory C) where
  bot_le W _ _ _ Hf := Hf.inclusion W.toSymmetricPremonoidalSubcategory

class CentralSubcategory (C)
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  [B: SymmetricPremonoidalCategory C]
  extends SymmetricMonoidalSubcategory C where
  centrality: CentralQuiver contains

theorem CentralSubcategory.ext_monoidal {C}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C]
  {L R: CentralSubcategory C}
  (H: L.toSymmetricMonoidalSubcategory = R.toSymmetricMonoidalSubcategory)
  : L = R := by cases L; cases R; cases H; rfl

theorem CentralSubcategory.ext {C}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C]
  {L R: CentralSubcategory C}
  (H: L.contains = R.contains): L = R
  := ext_monoidal (SymmetricMonoidalSubcategory.ext H)

instance CentralSubcategory.instPartialOrder {C}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C]
  : PartialOrder (CentralSubcategory C) where
  le L R := L.contains ≤ R.contains
  le_refl _ _ _ := le_refl _
  le_trans _ _ _ HL HR X Y := le_trans (HL X Y) (HR X Y)
  le_antisymm _ _ HL HR := ext (le_antisymm HL HR)

theorem CentralSubcategory.le_ext {C}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C]
  {L R: CentralSubcategory C}
  (H: L.contains ≤ R.contains): L ≤ R
  := H

instance CentralSubcategory.instBot {C}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C]
  : Bot (CentralSubcategory C) where
  bot := {
    toSymmetricMonoidalSubcategory := ⊥
    centrality := λ_ _ _ Hf => Hf.central
  }

instance CentralSubcategory.instOrderBot {C}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C]
  : OrderBot (CentralSubcategory C) where
  bot_le W _ _ _ Hf := Hf.inclusion W.toSymmetricPremonoidalSubcategory

def BinoidalSubcategory.Center (C)
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  : BinoidalSubcategory C where
  toWideSubcategory := WideSubcategory.Center C
  whiskerLeft := Central.whiskerLeft
  whiskerRight := Central.whiskerRight

def SymmetricPremonoidalSubcategory.Center (C)
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C]
  : SymmetricPremonoidalSubcategory C where
  toBinoidalSubcategory := BinoidalSubcategory.Center C
  associator X Y Z := (associator_centrality X Y Z).hom
  associator_inv X Y Z := (associator_centrality X Y Z).inv
  leftUnitor X := (leftUnitor_centrality X).hom
  leftUnitor_inv X := (leftUnitor_centrality X).inv
  rightUnitor X := (rightUnitor_centrality X).hom
  rightUnitor_inv X := (rightUnitor_centrality X).inv
  braiding X Y := (braiding_centrality X Y).hom

def SymmetricMonoidalSubcategory.Center (C)
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C]
  : SymmetricMonoidalSubcategory C where
  toSymmetricPremonoidalSubcategory := SymmetricPremonoidalSubcategory.Center C
  sliding Hf _ := Hf.commute_left _

def CentralSubcategory.mk' {C}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C]
  (S: SymmetricPremonoidalSubcategory C)
  (centrality: CentralQuiver S.contains)
  : CentralSubcategory C where
  toSymmetricPremonoidalSubcategory := S
  sliding Hf _ := (centrality _ _ Hf).commute_left _
  centrality := centrality

instance CentralSubcategory.instTop {C}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C]
  : Top (CentralSubcategory C) where
  top := {
    toSymmetricMonoidalSubcategory := SymmetricMonoidalSubcategory.Center C
    centrality := le_refl _
  }

instance CentralSubcategory.instOrderTop {C}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C]
  : OrderTop (CentralSubcategory C) where
  le_top W := W.centrality
