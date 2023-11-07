import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Braided

import Isotope.Premonoidal.Category

open CategoryTheory
open PremonoidalCategory
open BinoidalCategory

class BraidedPremonoidalCategory (C: Type u) [Category C] [TensorMonoid C] [PremonoidalCategory C]
where
  braiding : ∀ X Y : C, X ⊗ Y ≅ Y ⊗ X
  braiding_left_naturality : ∀ {X Y: C} (f: X ⟶ Y) (Z),
    (braiding X Z).hom ≫ whiskerLeft Z f = whiskerRight f Z ≫ (braiding Y Z).hom
  braiding_right_naturality : ∀ {X Y: C} (f: X ⟶ Y) (Z),
    (braiding Z X).hom ≫ whiskerRight f Z = whiskerLeft Z f ≫ (braiding Z Y).hom
  hexagon_forward : ∀ X Y Z: C,
    (associator X Y Z).hom ≫ (braiding X (Y ⊗ Z)).hom ≫ (associator Y Z X).hom =
    whiskerRight (braiding X Y).hom Z ≫ (associator Y X Z).hom ≫ whiskerLeft Y (braiding X Z).hom
  hexagon_reverse : ∀ X Y Z: C,
    (associator X Y Z).inv ≫ (braiding (X ⊗ Y) Z).hom ≫ (associator Z X Y).inv =
    whiskerLeft X (braiding Y Z).hom ≫ (associator X Z Y).inv ≫ whiskerRight (braiding X Z).hom Y

class SymmetricPremonoidalCategory (C: Type u) [Category C] [TensorMonoid C] [PremonoidalCategory C]
extends BraidedPremonoidalCategory C where
  symmetry : ∀ X Y : C, (braiding X Y).hom ≫ (braiding Y X).hom = 𝟙 (X ⊗ Y)
namespace BraidedPremonoidalCategory

instance fromBraidedCategory {C: Type u} [Category C] [MonoidalCategory C] [BraidedCategory C]
: BraidedPremonoidalCategory C
where
  braiding := BraidedCategory.braiding
  braiding_left_naturality := by
    simp [
      BinoidalCategory.whiskerLeft, BinoidalCategory.whiskerRight,
      <-MonoidalCategory.tensorHom_id, <-MonoidalCategory.id_tensorHom
    ]
  braiding_right_naturality := by
    simp [
      BinoidalCategory.whiskerLeft, BinoidalCategory.whiskerRight,
      <-MonoidalCategory.tensorHom_id, <-MonoidalCategory.id_tensorHom
    ]
  hexagon_forward := by
    simp [
      BinoidalCategory.whiskerLeft, BinoidalCategory.whiskerRight,
      TensorProduct.tensorObj,
      braiding, associator, BraidedCategory.hexagon_forward,
      <-MonoidalCategory.tensorHom_id, <-MonoidalCategory.id_tensorHom
    ]
  hexagon_reverse := by
    simp [
      BinoidalCategory.whiskerLeft, BinoidalCategory.whiskerRight,
      TensorProduct.tensorObj,
      braiding, associator, BraidedCategory.hexagon_reverse,
      <-MonoidalCategory.tensorHom_id, <-MonoidalCategory.id_tensorHom
    ]

end BraidedPremonoidalCategory

namespace SymmetricPremonoidalCategory

instance fromSymmetricCategory {C: Type u} [Category C] [MonoidalCategory C] [SymmetricCategory C]
: SymmetricPremonoidalCategory C
where
  toBraidedPremonoidalCategory := BraidedPremonoidalCategory.fromBraidedCategory
  symmetry := SymmetricCategory.symmetry

end SymmetricPremonoidalCategory
