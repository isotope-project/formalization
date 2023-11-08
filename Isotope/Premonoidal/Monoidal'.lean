import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Monoidal.Category

import Isotope.Premonoidal.Category

open CategoryTheory
open PremonoidalCategory
open BinoidalCategory

class MonoidalCategory' (C: Type u)
  [Category C] [TensorMonoid C]
  [PremonoidalCategory C] :=
  /-- Sliding -/
  sliding: ∀{X₁ Y₁ X₂ Y₂: C}, ∀f: X₁ ⟶ Y₁, ∀g: X₂ ⟶ Y₂, f ⋉ g = f ⋊ g
  /-- Centrality -/
  centrality: ∀{X Y: C}, ∀f: X ⟶ Y, Central f := λ{_ _} f => {
    commute := λg => ⟨sliding f g, sliding g f⟩
  }

namespace MonoidalCategory'

def MonoidalCategory'.fromMonoidalCategory (C: Type u) [Category C] [MonoidalCategory C]
  : MonoidalCategory' C where
  sliding := OrdCommute.monoidal

instance MonoidalCategory'.instMonoidalCategory'MonoidalCategory {C: Type u} [Category C] [MonoidalCategory C]
  : MonoidalCategory' C where
  sliding := OrdCommute.monoidal

-- def MonoidalCategory'.toMonoidalCategory (C: Type u)
--   [𝒞: Category C]
--   [𝒯: TensorMonoid C]
--   [ℳ: PremonoidalCategory C]
--   [𝒮: MonoidalCategory' C]
--   : MonoidalCategory C where
--   tensorObj := 𝒯.tensorObj
--   whiskerLeft := ℳ.whiskerLeft
--   whiskerRight := ℳ.whiskerRight
--   tensorHom := ℳ.leftTensorHom
--   tensor_id X Y := by simp only [
--     leftTensorHom, ℳ.whiskerLeft_id, ℳ.id_whiskerRight,
--     𝒞.comp_id]
--   tensor_comp f₁ f₂ g₁ g₂ := by
--     simp only [leftTensorHom]
--     rw [
--       ℳ.whiskerRight_comp,
--       ℳ.whiskerLeft_comp,
--       𝒞.assoc,
--       <-𝒞.assoc (g₁ ▷ _),
--       <-BinoidalCategory.leftTensorHom_def g₁ f₂,
--       𝒮.sliding,
--       BinoidalCategory.rightTensorHom_def,
--       𝒞.assoc,
--       𝒞.assoc
--     ]
--   tensorUnit' := 𝒯.tensorUnit
--   associator := ℳ.associator
--   whiskerLeft_id := ℳ.whiskerLeft_id
--   id_whiskerRight := ℳ.id_whiskerRight
--   associator_naturality := sorry
--   leftUnitor := ℳ.leftUnitor
--   leftUnitor_naturality f := by simp only [
--     leftTensorHom, <-ℳ.leftUnitor_naturality f,
--     ℳ.id_whiskerRight, 𝒞.id_comp]
--   rightUnitor := ℳ.rightUnitor
--   rightUnitor_naturality f := by simp only [
--     leftTensorHom, <-ℳ.rightUnitor_naturality f,
--     ℳ.whiskerLeft_id, 𝒞.comp_id]
--   pentagon W X Y Z := by simp only [
--     leftTensorHom, ℳ.id_whiskerRight, ℳ.whiskerLeft_id,
--     𝒞.id_comp, 𝒞.comp_id, ℳ.pentagon]
--   triangle X Y := by simp only [
--     leftTensorHom, ℳ.id_whiskerRight, ℳ.whiskerLeft_id,
--     𝒞.id_comp, 𝒞.comp_id, ℳ.triangle]
