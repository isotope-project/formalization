/- Adapted from https://github.com/leanprover-community/mathlib4/blob/9f8f772f02755375a8301679aeb67186742c59fa/Mathlib/CategoryTheory/Monoidal/Category.lean#L73-L147 -/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Order.Monotone.Basic

import Isotope.Binoidal.Category

open CategoryTheory
open BinoidalCategory


class TensorMonoid (C: Type u) extends TensorProduct C :=
  /-- The tensor unity in the monoidal structure `𝟙_ C` -/
  tensorUnit : C

open TensorMonoid

class PremonoidalCategory (C: Type u) [Category C] [TensorMonoid C] extends BinoidalCategory C :=
  /-- The associator isomorphism `(X ⊗ Y) ⊗ Z ≃ X ⊗ (Y ⊗ Z)` -/
  associator : ∀ X Y Z : C, tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z)
  /-- The left unitor: `𝟙_ C ⊗ X ≃ X` -/
  leftUnitor : ∀ X : C, tensorObj tensorUnit X ≅ X
  /-- The right unitor: `X ⊗ 𝟙_ C ≃ X` -/
  rightUnitor : ∀ X : C, tensorObj X tensorUnit ≅ X
  /--
  Centrality of the associator
  -/
  associator_centrality :
    ∀ (X₁ X₂ X₃), CentralIso (associator X₁ X₂ X₃) := by
    aesop_cat
  /--
  Naturality of the associator w.r.t the first parameter
  -/
  associator_left_naturality :
    ∀ {X₁ X₂ X₃ Y : C} (f : X₁ ⟶ Y),
      whiskerRight (whiskerRight f X₂) X₃ ≫ (associator Y X₂ X₃).hom =
        (associator X₁ X₂ X₃).hom ≫ whiskerRight f (tensorObj X₂ X₃) := by
    aesop_cat
  /--
  Naturality of the associator w.r.t the second parameter
  -/
  associator_mid_naturality :
    ∀ {X₁ X₂ X₃ Y : C} (f : X₂ ⟶ Y),
      whiskerRight (whiskerLeft X₁ f) X₃ ≫ (associator X₁ Y X₃).hom =
        (associator X₁ X₂ X₃).hom ≫ whiskerLeft X₁ (whiskerRight f X₃) := by
    aesop_cat
  /--
  Naturality of the associator w.r.t the third parameter
  -/
  associator_right_naturality :
    ∀ {X₁ X₂ X₃ Y : C} (f : X₃ ⟶ Y),
      whiskerLeft (tensorObj X₁ X₂) f ≫ (associator X₁ X₂ Y).hom =
        (associator X₁ X₂ X₃).hom ≫ whiskerLeft X₁ (whiskerLeft X₂ f) := by
    aesop_cat
  /--
  Centrality of the left unitor
  -/
  leftUnitor_centrality :
    ∀ (Z), CentralIso (leftUnitor Z)
   := by
    aesop_cat
  /--
  Naturality of the left unitor, commutativity of `𝟙_ C ⊗ X ⟶ 𝟙_ C ⊗ Y ⟶ Y` and `𝟙_ C ⊗ X ⟶ X ⟶ Y`
  -/
  leftUnitor_naturality :
    ∀ {X Y : C} (f : X ⟶ Y),
      whiskerLeft _ f ≫ (leftUnitor Y).hom = (leftUnitor X).hom ≫ f := by
    aesop_cat
  /--
  Centrality of the right unitor
  -/
  rightUnitor_centrality :
    ∀ (Z), CentralIso (rightUnitor Z)
   := by
    aesop_cat
  /--
  Naturality of the right unitor: commutativity of `X ⊗ 𝟙_ C ⟶ Y ⊗ 𝟙_ C ⟶ Y` and `X ⊗ 𝟙_ C ⟶ X ⟶ Y`
  -/
  rightUnitor_naturality :
    ∀ {X Y : C} (f : X ⟶ Y),
      whiskerRight f _ ≫ (rightUnitor Y).hom = (rightUnitor X).hom ≫ f := by
    aesop_cat
  /--
  The pentagon identity relating the isomorphism between `X ⊗ (Y ⊗ (Z ⊗ W))` and `((X ⊗ Y) ⊗ Z) ⊗ W`
  -/
  pentagon :
    ∀ W X Y Z : C,
      whiskerRight (associator W X Y).hom Z ≫
          (associator W (tensorObj X Y) Z).hom ≫ whiskerLeft W (associator X Y Z).hom =
        (associator (tensorObj W X) Y Z).hom ≫ (associator W X (tensorObj Y Z)).hom := by
    aesop_cat
  /--
  The identity relating the isomorphisms between `X ⊗ (𝟙_C ⊗ Y)`, `(X ⊗ 𝟙_C) ⊗ Y` and `X ⊗ Y`
  -/
  triangle :
    ∀ X Y : C,
      (associator X tensorUnit Y).hom ≫ whiskerLeft X (leftUnitor Y).hom =
        whiskerRight (rightUnitor X).hom Y := by
    aesop_cat

instance TensorMonoid.fromMonoidalCategory (C: Type u) [Category C] [MonoidalCategory C]: TensorMonoid C := {
  tensorUnit := MonoidalCategory.tensorUnit
}
namespace PremonoidalCategory

export TensorMonoid (tensorUnit)

theorem associator_epi {C: Type u}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  (X Y Z: C)
  : Epi (associator X Y Z).hom
  := IsIso.epi_of_iso _

theorem associator_inv_epi {C: Type u}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  (X Y Z: C)
  : Epi (associator X Y Z).inv
  := IsIso.epi_of_iso _

theorem leftUnitor_epi {C: Type u}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  (X: C)
  : Epi (leftUnitor X).hom
  := IsIso.epi_of_iso _

theorem leftUnitor_inv_epi {C: Type u}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  (X: C)
  : Epi (leftUnitor X).inv
  := IsIso.epi_of_iso _

theorem rightUnitor_epi {C: Type u}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  (X: C)
  : Epi (rightUnitor X).hom
  := IsIso.epi_of_iso _

theorem rightUnitor_inv_epi {C: Type u}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  (X: C)
  : Epi (rightUnitor X).inv
  := IsIso.epi_of_iso _

theorem associator_mono {C: Type u}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  (X Y Z: C)
  : Mono (associator X Y Z).hom
  := IsIso.mono_of_iso _

theorem associator_inv_mono {C: Type u}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  (X Y Z: C)
  : Mono (associator X Y Z).inv
  := IsIso.mono_of_iso _

theorem leftUnitor_mono {C: Type u}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  (X: C)
  : Mono (leftUnitor X).hom
  := IsIso.mono_of_iso _

theorem leftUnitor_inv_mono {C: Type u}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  (X: C)
  : Mono (leftUnitor X).inv
  := IsIso.mono_of_iso _

theorem rightUnitor_mono {C: Type u}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  (X: C)
  : Mono (rightUnitor X).hom
  := IsIso.mono_of_iso _

theorem rightUnitor_inv_mono {C: Type u}
  [Category C] [TensorMonoid C] [PremonoidalCategory C]
  (X: C)
  : Mono (rightUnitor X).inv
  := IsIso.mono_of_iso _

instance fromMonoidalCategory (C: Type u) [Category C] [MonoidalCategory C]
  : PremonoidalCategory C := {
  toBinoidalCategory := BinoidalCategory.fromMonoidalCategory C
  associator := MonoidalCategory.associator
  leftUnitor := MonoidalCategory.leftUnitor
  rightUnitor := MonoidalCategory.rightUnitor
  associator_centrality := λ_ _ _ => monoidalCentralIso _
  associator_left_naturality := by
    simp [
      BinoidalCategory.whiskerLeft, BinoidalCategory.whiskerRight,
      <-MonoidalCategory.tensorHom_id,
      TensorProduct.tensorObj
    ]
  associator_mid_naturality := by
    simp [
      BinoidalCategory.whiskerLeft, BinoidalCategory.whiskerRight,
      <-MonoidalCategory.tensorHom_id, <-MonoidalCategory.id_tensorHom
    ]
  associator_right_naturality := by
    intros
    simp only [
      BinoidalCategory.whiskerLeft, BinoidalCategory.whiskerRight,
      <-MonoidalCategory.id_tensorHom,
      <-MonoidalCategory.tensor_id,
      MonoidalCategory.associator_naturality,
      TensorProduct.tensorObj
    ]
  leftUnitor_centrality := λ_ => monoidalCentralIso _
  leftUnitor_naturality := by
    simp [
      BinoidalCategory.whiskerLeft, BinoidalCategory.whiskerRight,
      tensorUnit, <-MonoidalCategory.id_tensorHom
    ]
  rightUnitor_centrality := λ_ => monoidalCentralIso _
  rightUnitor_naturality := by
    simp [
      BinoidalCategory.whiskerLeft, BinoidalCategory.whiskerRight,
      tensorUnit, <-MonoidalCategory.tensorHom_id
    ]
  pentagon := by
    simp [
      BinoidalCategory.whiskerLeft, BinoidalCategory.whiskerRight,
      TensorProduct.tensorObj,
      associator, <-MonoidalCategory.tensorHom_id, <-MonoidalCategory.id_tensorHom,
      MonoidalCategory.pentagon
    ]
  triangle := by
    simp [
      BinoidalCategory.whiskerLeft, BinoidalCategory.whiskerRight,
      TensorProduct.tensorObj, TensorMonoid.tensorUnit,
      associator, <-MonoidalCategory.tensorHom_id, <-MonoidalCategory.id_tensorHom
    ]
}
