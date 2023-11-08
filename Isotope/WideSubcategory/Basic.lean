import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Braided
import Mathlib.Combinatorics.Quiver.Subquiver

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

def WideSubcategory.intersect {C} [Category C]
  (L R: WideSubcategory C): WideSubcategory C where
  contains X Y f := L.contains X Y f ∧ R.contains X Y f
  contains_comp Hf Hg := ⟨
    L.contains_comp Hf.1 Hg.1,
    R.contains_comp Hf.2 Hg.2⟩
  contains_id X := ⟨L.contains_id X, R.contains_id X⟩
