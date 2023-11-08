import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Braided
import Mathlib.Combinatorics.Quiver.Subquiver
import Mathlib.Data.SetLike.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.CompleteLattice

open CategoryTheory

class WideSubcategory (C) [Category C] where
  contains: WideSubquiver C
  contains_comp: ∀{X Y Z: C} {f: X ⟶ Y} {g: Y ⟶ Z},
    contains X Y f -> contains Y Z g -> contains X Z (f ≫ g)
  contains_id: ∀(X: C), contains X X (𝟙 X)

def WideSubcategory.discrete (C) [Category C]: WideSubcategory C where
  contains X Y f := ∃H: X = Y, f = H ▸ 𝟙 X
  contains_comp := λ⟨HXY, Hf⟩ ⟨HYZ, Hg⟩ => ⟨
    HXY ▸ HYZ,
    by cases HXY; cases HYZ; cases Hf; cases Hg; simp⟩
  contains_id X := ⟨rfl, rfl⟩

def WideSubcategory.ext {C} [Category C]
  {L R: WideSubcategory C} (H: L.contains = R.contains)
  : L = R
  := by cases L; cases R; cases H; rfl

def WideSubcategory.ext' {C} [Category C]
  {L R: WideSubcategory C} (H: ∀X Y, L.contains X Y = R.contains X Y)
  : L = R
  := WideSubcategory.ext (by funext X Y; exact H X Y)

instance WideSubquiver.instPartialOrder {C} [Quiver C]
  : PartialOrder (WideSubquiver C) where
  le L R := ∀X Y, L X Y ≤ R X Y
  le_refl _ _ _ := le_refl _
  le_trans _ _ _ HL HR X Y := le_trans (HL X Y) (HR X Y)
  le_antisymm _ _ HL HR
    := by funext X Y; exact le_antisymm (HL X Y) (HR X Y)

instance WideSubcategory.instPartialOrder {C} [Category C]
  : PartialOrder (WideSubcategory C) where
  le L R := L.contains ≤ R.contains
  le_refl _ _ _ := le_refl _
  le_trans _ _ _ HL HR X Y := le_trans (HL X Y) (HR X Y)
  le_antisymm _ _ HL HR := ext (le_antisymm HL HR)

theorem WideSubcategory.le_ext {C} [Category C]
  {L R: WideSubcategory C}
  (H: L.contains ≤ R.contains)
  : L ≤ R
  := H

instance WideSubquiver.instInf {C} [Quiver C]
  : Inf (WideSubquiver C) where
  inf L R X Y f := L X Y f ∧ R X Y f

instance WideSubcategory.instInf {C} [Category C]
  : Inf (WideSubcategory C) where
  inf L R := {
    contains := L.contains ⊓ R.contains
    contains_comp := λHf Hg => ⟨
      L.contains_comp Hf.1 Hg.1,
      R.contains_comp Hf.2 Hg.2⟩
    contains_id := λX => ⟨L.contains_id X, R.contains_id X⟩
  }

instance WideSubquiver.instInfSet {C} [Quiver C]
  : InfSet (WideSubquiver C) where
  sInf S X Y f := ∀W ∈ S, W X Y f

instance WideSubcategory.instInfSet {C} [Category C]
  : InfSet (WideSubcategory C) where
  sInf S := {
    contains := λX Y f => ∀W ∈ S, W.contains X Y f
    contains_comp := λHf Hg W HW => W.contains_comp (Hf W HW) (Hg W HW)
    contains_id := λX W _ => W.contains_id X
  }

instance WideSubquiver.instSemilatticeInf {C} [Quiver C]
  : SemilatticeInf (WideSubquiver C) where
  inf_le_left _ _ _ _ _ H := H.1
  inf_le_right _ _ _ _ _ H := H.2
  le_inf _ _ _ HL HR X Y _ H := ⟨HL X Y H, HR X Y H⟩

instance WideSubcategory.instSemilatticeInf {C} [Category C]
  : SemilatticeInf (WideSubcategory C) where
  inf_le_left _ _ _ _ _ H := H.1
  inf_le_right _ _ _ _ _ H := H.2
  le_inf _ _ _ HL HR X Y _ H := ⟨HL X Y H, HR X Y H⟩

instance WideSubquiver.instBot {C} [Quiver C]
  : Bot (WideSubquiver C) where
  bot _ _ _ := False

instance WideSubquiver.instOrderBot {C} [Category C]
  : OrderBot (WideSubquiver C) where
  bot_le _ _ _ _ := False.elim

instance WideSubcategory.instBot {C} [Category C]
  : Bot (WideSubcategory C) where
  bot := {
    contains := λX Y f => ∃H: X = Y, f = H ▸ 𝟙 X
    contains_comp := λ⟨HXY, Hf⟩ ⟨HYZ, Hg⟩ => ⟨
      HXY ▸ HYZ,
      by cases HXY; cases HYZ; cases Hf; cases Hg; simp⟩
    contains_id := λ_ => ⟨rfl, rfl⟩
  }

instance WideSubcategory.instOrderBot {C} [Category C]
  : OrderBot (WideSubcategory C) where
  bot_le L _ _ _ := λ⟨HXY, Hf⟩ => by cases HXY; cases Hf; exact L.contains_id _

instance WideSubquiver.instTop {C} [Quiver C]
  : Top (WideSubquiver C) where
  top _ _ _ := True

instance WideSubcategory.instTop {C} [Category C]
  : Top (WideSubcategory C) where
  top := {
    contains := ⊤
    contains_comp := λ_ _ => True.intro
    contains_id := λ_ => True.intro
  }

instance WideSubquiver.instOrderTop {C} [Quiver C]
  : OrderTop (WideSubquiver C) where
  le_top _ _ _ _ _ := True.intro

instance WideSubcategory.instOrderTop {C} [Category C]
  : OrderTop (WideSubcategory C) where
  le_top _ _ _ _ _ := True.intro

instance WideSubcategory.instCompleteSemilatticeInf {C} [Category C]
  : CompleteSemilatticeInf (WideSubcategory C) where
  sInf_le _ W HW _ _ _ Hf := Hf W HW
  le_sInf _ _ HL _ _ _ Hf := λW HW => HL W HW _ _ Hf

instance WideSubquiver.instSup {C} [Quiver C]
  : Sup (WideSubquiver C) where
  sup L R X Y f := L X Y f ∨ R X Y f

instance WideSubquiver.instSemilatticeSup {C} [Quiver C]
  : SemilatticeSup (WideSubquiver C) where
  le_sup_left _ _ _ _ _ := Or.inl
  le_sup_right _ _ _ _ _ := Or.inr
  sup_le _ _ _ HL HR _ _ _ Hf := Or.elim Hf (λH => HL _ _ H) (λH => HR _ _ H)

instance WideSubcategory.instSup {C} [Category C]
  : Sup (WideSubcategory C) where
  sup := (completeLatticeOfCompleteSemilatticeInf (WideSubcategory C)).sup

instance WideSubcategory.instSemilatticeSup {C} [Category C]
  : SemilatticeSup (WideSubcategory C) where
  le_sup_left :=
    (completeLatticeOfCompleteSemilatticeInf (WideSubcategory C)).le_sup_left
  le_sup_right :=
    (completeLatticeOfCompleteSemilatticeInf (WideSubcategory C)).le_sup_right
  sup_le :=
    (completeLatticeOfCompleteSemilatticeInf (WideSubcategory C)).sup_le

instance WideSubquiver.instSupSet {C} [Quiver C]
  : SupSet (WideSubquiver C) where
  sSup S X Y f := ∃W ∈ S, W X Y f

instance WideSubcategory.instSupSet {C} [Category C]
  : SupSet (WideSubcategory C) where
  sSup := (completeLatticeOfCompleteSemilatticeInf (WideSubcategory C)).sSup

instance WideSubquiver.instCompleteLattice {C} [Category C]
  : CompleteLattice (WideSubquiver C) where
  inf_le_left _ _ _ _ _ H := H.1
  inf_le_right _ _ _ _ _ H := H.2
  le_inf _ _ _ HL HR X Y _ H := ⟨HL X Y H, HR X Y H⟩
  bot_le _ _ _ _ := False.elim
  le_sSup _ _ HS _ _ _ Hf := ⟨_, HS, Hf⟩
  sSup_le _ _ HS _ _ _ := λ⟨W, HW, Hf⟩ => HS W HW _ _ Hf
  sInf_le _ W HW _ _ _ Hf := Hf W HW
  le_sInf _ _ HL _ _ _ Hf := λW HW => HL W HW _ _ Hf
  le_top _ _ _ _ _ := True.intro

instance WideSubcategory.instCompleteLattice {C} [Category C]
  : CompleteLattice (WideSubcategory C) where
  inf_le_left _ _ _ _ _ H := H.1
  inf_le_right _ _ _ _ _ H := H.2
  le_inf _ _ _ HL HR X Y _ H := ⟨HL X Y H, HR X Y H⟩
  bot_le L _ _ _ := λ⟨HXY, Hf⟩ => by cases HXY; cases Hf; exact L.contains_id _
  le_top _ _ _ _ _ := True.intro
  le_sSup :=
    (completeLatticeOfCompleteSemilatticeInf (WideSubcategory C)).le_sSup
  sSup_le _ W HW _ _ _ Hf := Hf W HW
  sInf_le _ W HW _ _ _ Hf := Hf W HW
  le_sInf _ _ HL _ _ _ Hf := λW HW => HL W HW _ _ Hf
