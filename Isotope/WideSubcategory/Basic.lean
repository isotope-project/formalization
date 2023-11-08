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

def WideSubcategory.full (C) [Category C]: WideSubcategory C where
  contains _ _ _ := True
  contains_comp _ _ := True.intro
  contains_id _ := True.intro

def WideSubcategory.ext {C} [Category C]
  {L R: WideSubcategory C} (H: L.contains = R.contains)
  : L = R
  := by cases L; cases R; cases H; rfl

def WideSubcategory.ext' {C} [Category C]
  {L R: WideSubcategory C} (H: ∀X Y, L.contains X Y = R.contains X Y)
  : L = R
  := WideSubcategory.ext (by funext X Y; exact H X Y)

instance WideSubcategory.instPartialOrder {C} [Category C]
  : PartialOrder (WideSubcategory C) where
  le L R := ∀X Y, L.contains X Y ≤ R.contains X Y
  le_refl _ _ _ := le_refl _
  le_trans _ _ _ HL HR X Y := le_trans (HL X Y) (HR X Y)
  le_antisymm _ _ HL HR := ext' (λX Y => le_antisymm (HL X Y) (HR X Y))

instance WideSubcategory.instInf {C} [Category C]
  : Inf (WideSubcategory C) where
  inf L R := {
    contains := λX Y f => L.contains X Y f ∧ R.contains X Y f
    contains_comp := λHf Hg => ⟨
      L.contains_comp Hf.1 Hg.1,
      R.contains_comp Hf.2 Hg.2⟩
    contains_id := λX => ⟨L.contains_id X, R.contains_id X⟩
  }

instance WideSubcategory.instInfSet {C} [Category C]
  : InfSet (WideSubcategory C) where
  sInf S := {
    contains := λX Y f => ∀W ∈ S, W.contains X Y f
    contains_comp := λHf Hg W HW => W.contains_comp (Hf W HW) (Hg W HW)
    contains_id := λX W _ => W.contains_id X
  }

instance WideSubcategory.instSemilatticeInf {C} [Category C]
  : SemilatticeInf (WideSubcategory C) where
  inf_le_left _ _ _ _ _ H := H.1
  inf_le_right _ _ _ _ _ H := H.2
  le_inf _ _ _ HL HR X Y _ H := ⟨HL X Y H, HR X Y H⟩

instance WideSubcategory.instOrderBot {C} [Category C]
  : OrderBot (WideSubcategory C) where
  bot := WideSubcategory.discrete C
  bot_le L _ _ _ := λ⟨HXY, Hf⟩ => by cases HXY; cases Hf; exact L.contains_id _

instance WideSubcategory.instOrderTop {C} [Category C]
  : OrderTop (WideSubcategory C) where
  top := WideSubcategory.full C
  le_top _ _ _ _ _ := True.intro

instance WideSubcategory.instCompleteSemilatticeInf {C} [Category C]
  : CompleteSemilatticeInf (WideSubcategory C) where
  sInf_le _ W HW _ _ _ Hf := Hf W HW
  le_sInf _ _ HL _ _ _ Hf := λW HW => HL W HW _ _ Hf

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

instance WideSubcategory.instSupSet {C} [Category C]
  : SupSet (WideSubcategory C) where
  sSup := (completeLatticeOfCompleteSemilatticeInf (WideSubcategory C)).sSup

instance WideSubcategory.instCompleteSemilatticeSup {C} [Category C]
  : CompleteSemilatticeSup (WideSubcategory C) where
  sSup_le _ W HW _ _ _ Hf := Hf W HW
  le_sSup :=
    (completeLatticeOfCompleteSemilatticeInf (WideSubcategory C)).le_sSup

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
