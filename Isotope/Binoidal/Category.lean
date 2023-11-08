/- Adapted from https://github.com/leanprover-community/mathlib4/blob/9f8f772f02755375a8301679aeb67186742c59fa/Mathlib/CategoryTheory/Monoidal/Category.lean#L73-L147 -/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Monoidal.Category
open CategoryTheory
open Quiver

class TensorProduct (C: Type u) :=
  /-- curried tensor product of objects -/
  tensorObj: C -> C -> C

open TensorProduct

class BinoidalCategory (C: Type u) [Category C] [TensorProduct C] :=
  /-- left whiskering for morphisms -/
  whiskerLeft: (X: C) -> {Y₁ Y₂: C} -> (Y₁ ⟶ Y₂) -> (tensorObj X Y₁ ⟶ tensorObj X Y₂)
  whiskerLeft_id : ∀ (X Y : C), whiskerLeft X (𝟙 Y) = 𝟙 (tensorObj X Y) := by
    aesop_cat
  whiskerLeft_comp {X Y₁ Y₂: C} (f: Y₁ ⟶ Y₂) {Y₃: C} (g: Y₂ ⟶ Y₃)
    : whiskerLeft X (f ≫ g) = whiskerLeft X f ≫ whiskerLeft X g

  /-- right whiskering for morphisms -/
  whiskerRight: {X₁ X₂: C} -> (X₁ ⟶ X₂) -> (Y: C) -> (tensorObj X₁ Y ⟶ tensorObj X₂ Y)
  id_whiskerRight : ∀ (X Y : C), whiskerRight (𝟙 X) Y = 𝟙 (tensorObj X Y) := by
    aesop_cat
  whiskerRight_comp {X Y₁ Y₂: C} (f: Y₁ ⟶ Y₂) {Y₃: C} (g: Y₂ ⟶ Y₃)
    : whiskerRight (f ≫ g) X = whiskerRight f X ≫ whiskerRight g X

  /-- left tensor product `f ⋉ g` -/
def BinoidalCategory.leftTensorHom {C: Type u} [Category C] [TensorProduct C] [BinoidalCategory C]
  {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g: X₂ ⟶ Y₂)
  : (tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂) := whiskerRight f _ ≫ whiskerLeft _ g


  /-- right tensor product `f ⋉ g` -/
def BinoidalCategory.rightTensorHom {C: Type u} [Category C] [TensorProduct C] [BinoidalCategory C]
  {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g: X₂ ⟶ Y₂)
  : (tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂) := whiskerLeft _ g ≫ whiskerRight f _

/- Notation based on https://www.dpmms.cam.ac.uk/~martin/Research/Publications/2002/bh02.pdf -/

namespace BinoidalCategory

export TensorProduct (tensorObj)

/-- Notation for `tensorObj`, the tensor product of objects in a binoidal category -/
scoped infixr:70 " ⊗ " => tensorObj

/-- Notation for the `whiskerLeft` operator of binoidal categories -/
scoped infixr:81 " ◁ " => whiskerLeft

/-- Notation for the `whiskerRight` operator of binoidal categories -/
scoped infixl:81 " ▷ " => whiskerRight

/-- Notation for the `leftTensorHom` operator of binoidal categories -/
scoped infixr:81 " ⋉ " => leftTensorHom

def BinoidalCategory.leftTensorHom_def {C: Type u}
  [Category C] [TensorProduct C] [BinoidalCategory C]
  {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g: X₂ ⟶ Y₂)
  : f ⋉ g = whiskerRight f _ ≫ whiskerLeft _ g := rfl

/-- Notation for the `rightTensorHom` operator of binoidal categories -/
scoped infixl:81 " ⋊ " => rightTensorHom

def BinoidalCategory.rightTensorHom_def {C: Type u}
  [Category C] [TensorProduct C] [BinoidalCategory C]
  {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g: X₂ ⟶ Y₂)
  : f ⋊ g = whiskerLeft _ g ≫ whiskerRight f _ := rfl

instance TensorProduct.fromMonoidalCategory (C: Type u)
  [Category C] [MonoidalCategory C]: TensorProduct C := {
  tensorObj := MonoidalCategory.tensorObj
}

instance fromMonoidalCategory (C: Type u) [Category C] [MonoidalCategory C]
  : BinoidalCategory C := {
  whiskerLeft := MonoidalCategory.whiskerLeft
  whiskerRight := MonoidalCategory.whiskerRight
  whiskerLeft_comp := by simp [<-MonoidalCategory.id_tensorHom]
  whiskerRight_comp := by simp [<-MonoidalCategory.tensorHom_id]
}

abbrev OrdCommute {C} [Category C] [TensorProduct C] [BinoidalCategory C]
  {X Y Z W: C} (f: X ⟶ Y) (g: Z ⟶ W)
  := f ⋉ g = f ⋊ g

theorem OrdCommute.monoidal {C} [Category C] [MonoidalCategory C] {X Y Z W: C}
  (f: X ⟶ Y) (g: Z ⟶ W): OrdCommute f g
  := by simp [
    OrdCommute, leftTensorHom, rightTensorHom, whiskerLeft, whiskerRight,
    MonoidalCategory.whisker_exchange
  ]

theorem OrdCommute.id_left {C}
  [Category C] [TensorProduct C] [BinoidalCategory C]
  {X Y} (Z: C) (f: X ⟶ Y): OrdCommute (𝟙 Z) f
  := by simp [
    OrdCommute, leftTensorHom, rightTensorHom, id_whiskerRight
  ]

theorem OrdCommute.id_right {C}
  [Category C] [TensorProduct C] [BinoidalCategory C]
  {X Y} (f: X ⟶ Y) (Z: C): OrdCommute f (𝟙 Z)
  := by simp [
    OrdCommute, leftTensorHom, rightTensorHom, whiskerLeft_id
  ]

def OrdCommute.comp_left {C} [Category C] [TensorProduct C] [BinoidalCategory C]
  {X Y Z W W': C} {f: X ⟶ Y} {g: Y ⟶ Z} {h: W ⟶ W'}
  (Hf: OrdCommute f h) (Hg: OrdCommute g h): OrdCommute (f ≫ g) h
  := by
    simp only [
      OrdCommute, leftTensorHom,
      whiskerRight_comp, Category.assoc, rightTensorHom]
    rw [
      <-leftTensorHom, Hg,
      <-Category.assoc,
      <-rightTensorHom,
      <-Hf,
      leftTensorHom,
      Category.assoc
    ]
    rfl

def OrdCommute.comp_right {C} [Category C] [TensorProduct C] [BinoidalCategory C]
  {X Y Z W W': C} {f: X ⟶ Y} {g: Y ⟶ Z} {h: W ⟶ W'}
  (Hf: OrdCommute h f) (Hg: OrdCommute h g): OrdCommute h (f ≫ g)
  := by
    simp only [
      OrdCommute, leftTensorHom,
      whiskerLeft_comp, rightTensorHom, Category.assoc]
    rw [
      <-rightTensorHom, <-Hg,
      <-Category.assoc,
      <-leftTensorHom,
      Hf,
      leftTensorHom,
      rightTensorHom,
      Category.assoc
    ]

class Commute {C} [Category C] [TensorProduct C] [BinoidalCategory C]
  {X Y Z W: C} (f: X ⟶ Y) (g: Z ⟶ W): Prop
  where
  left: OrdCommute f g
  right: OrdCommute g f

def Commute.symm
  [Category C] [TensorProduct C] [BinoidalCategory C]
  {X Y Z W: C} {f: X ⟶ Y} {g: Z ⟶ W}
  (H: Commute f g)
  : Commute g f
  := ⟨H.2, H.1⟩

def Commute.comp_left {C} [Category C] [TensorProduct C] [BinoidalCategory C]
  {X Y Z W W': C} {f: X ⟶ Y} {g: Y ⟶ Z} {h: W ⟶ W'}
  (Hf: Commute f h) (Hg: Commute g h): Commute (f ≫ g) h where
  left := Hf.left.comp_left Hg.left
  right := Hf.right.comp_right Hg.right

def Commute.comp_right {C} [Category C] [TensorProduct C] [BinoidalCategory C]
  {X Y Z W W': C} {f: X ⟶ Y} {g: Y ⟶ Z} {h: W ⟶ W'}
  (Hf: Commute f h) (Hg: Commute g h): Commute h (f ≫ g)
  := (Hf.comp_left Hg).symm

def Commute.monoidal {C} [Category C] [MonoidalCategory C] {X Y Z W: C}
  (f: X ⟶ Y) (g: Z ⟶ W): Commute f g
  := ⟨OrdCommute.monoidal f g, OrdCommute.monoidal g f⟩

-- instance monoidalCommute
--   {C} [Category C] [MonoidalCategory C]
--   {X Y Z W: C} {f: X ⟶ Y} {g: Z ⟶ W}
--   : Commute f g
--   := Commute.monoidal f g

class Central {C} [Category C] [TensorProduct C] [BinoidalCategory C]
  {X Y: C} (f: X ⟶ Y): Prop :=
  commute: ∀{Z W}, ∀g: Z ⟶ W, Commute f g
  commute_left: ∀{Z W}, ∀g: Z ⟶ W, OrdCommute f g := λg => (commute g).left
  commute_right: ∀{Z W}, ∀g: Z ⟶ W, OrdCommute g f := λg => (commute g).right

def Central.id {C} [Category C] [TensorProduct C] [BinoidalCategory C]
  (X: C): Central (𝟙 X) where
  commute _ := ⟨OrdCommute.id_left _ _, OrdCommute.id_right _ _⟩

def Central.comp {C} [Category C] [TensorProduct C] [BinoidalCategory C]
  {X Y Z: C} {f: X ⟶ Y} {g: Y ⟶ Z}
  (Hf: Central f) (Hg: Central g): Central (f ≫ g) where
  commute _ := Commute.comp_left (Hf.commute _) (Hg.commute _)

class CentralIso {C} [Category C] [TensorProduct C] [BinoidalCategory C]
  {X Y: C} (f: X ≅ Y): Prop :=
  hom: Central f.hom
  inv: Central f.inv

instance monoidalCentral {C: Type u} [Category C] [MonoidalCategory C]
  {X Y: C} (f: X ⟶ Y)
  : Central f where
  commute := λg => Commute.monoidal f g

instance centralLeft {C}
  [Category C] [TensorProduct C] [BinoidalCategory C]
  {X Y Z W: C} {f: X ⟶ Y} {g: Z ⟶ W}
  [H: Central f]
  : Commute f g
  := H.commute g

instance centralRight {C}
  [Category C] [TensorProduct C] [BinoidalCategory C]
  {X Y Z W: C} {f: X ⟶ Y} {g: Z ⟶ W}
  [H: Central g]
  : Commute f g
  := (H.commute f).symm

instance monoidalCentralIso {C: Type u} [Category C] [MonoidalCategory C]
  {X Y: C} (f: X ≅ Y): CentralIso f := {
  hom := monoidalCentral f.hom
  inv := monoidalCentral f.inv
}
