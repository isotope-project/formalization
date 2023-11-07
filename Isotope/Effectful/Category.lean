/- Adapted from https://github.com/leanprover-community/mathlib4/blob/9f8f772f02755375a8301679aeb67186742c59fa/Mathlib/CategoryTheory/Monoidal/Category.lean#L73-L147 -/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Functorial
import Mathlib.CategoryTheory.Monoidal.Category

import Isotope.Binoidal.Category
import Isotope.Premonoidal.Category
import Isotope.Premonoidal.Monoidal'

open CategoryTheory
open BinoidalCategory

def Value (C: Type u): Type u := C

instance valueTensorProduct {C: Type u} [T: TensorProduct C]: TensorProduct (Value C) := T
instance valueTensorMonoid {C: Type u} [T: TensorMonoid C]: TensorMonoid (Value C) := T

def Value.inclusion {C: Type u} (A: Value C): C := A
def Value.box {C: Type u} (A: C): Value C := A
def Value.inclusion_def {C: Type u} (A: Value C): inclusion A = A := rfl

def functorial_iso {C D: Type u} (F: C -> D)
  [Category C] [Category D] [ℱ: Functorial F] {X Y: C}
  (f: X ≅ Y)
  : F X ≅ F Y
  := {
    hom := ℱ.map' f.hom
    inv := ℱ.map' f.inv
    hom_inv_id := by rw [<-ℱ.map_comp', f.hom_inv_id, ℱ.map_id']
    inv_hom_id := by rw [<-ℱ.map_comp', f.inv_hom_id, ℱ.map_id']
  }

theorem functorial_iso_ext {C D: Type u} {F: C -> D}
  [Category C] [Category D] [ℱ: Functorial F] {X Y: C}
  (f: X ≅ Y)
  (Ff: F X ≅ F Y)
  (H: ℱ.map' f.hom = Ff.hom)
  : functorial_iso F f = Ff
  := Iso.ext H

theorem iso_inv_map {C D: Type u} {F: C -> D}
  [Category C] [Category D] [ℱ: Functorial F] {X Y: C}
  (f: X ≅ Y)
  (Ff: F X ≅ F Y)
  (H: ℱ.map' f.hom = Ff.hom)
  : ℱ.map' f.inv = Ff.inv
  := by rw [<-functorial_iso_ext f Ff H]; rfl

class EffectfulCategory (C: Type u)
  [TensorMonoid C]
  [Category (Value C)]
  [𝒱: PremonoidalCategory (Value C)]
  [MonoidalCategory' (Value C)]
  [Category C]
  [𝒞: PremonoidalCategory C] where
  inclusion: Functorial (@Value.inclusion C)
  inclusion_central: ∀{X Y}, ∀f: X ⟶ Y, Central (inclusion.map' f)
  inclusion_associator: ∀X Y Z, inclusion.map' (𝒱.associator X Y Z).hom = (𝒞.associator X Y Z).hom
  inclusion_associator_inv:
    ∀X Y Z, inclusion.map' (𝒱.associator X Y Z).inv = (𝒞.associator X Y Z).inv
    := λX Y Z => iso_inv_map _ _ (inclusion_associator X Y Z)
  inclusion_leftUnitor: ∀Z, inclusion.map' (𝒱.leftUnitor Z).hom = (𝒞.leftUnitor Z).hom
  inclusion_leftUnitor_inv: ∀Z, inclusion.map' (𝒱.leftUnitor Z).inv = (𝒞.leftUnitor Z).inv
    := λZ => iso_inv_map _ _ (inclusion_leftUnitor Z)
  inclusion_rightUnitor: ∀Z, inclusion.map' (𝒱.rightUnitor Z).hom = (𝒞.rightUnitor Z).hom
  inclusion_rightUnitor_inv: ∀Z, inclusion.map' (𝒱.rightUnitor Z).inv = (𝒞.rightUnitor Z).inv
    := λZ => iso_inv_map _ _ (inclusion_rightUnitor Z)
  inclusion_whiskerLeft: ∀{X Y Z}, ∀f: X ⟶ Y,
    inclusion.map' (𝒱.whiskerLeft Z f) = 𝒞.whiskerLeft Z (inclusion.map' f)
  inclusion_whiskerRight: ∀{X Y Z}, ∀f: X ⟶ Y,
    inclusion.map' (𝒱.whiskerRight f Z) = 𝒞.whiskerRight (inclusion.map' f) Z
