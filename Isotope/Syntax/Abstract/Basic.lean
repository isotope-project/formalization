import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.DiscreteCategory

open CategoryTheory

namespace Abstract

class Splittable.{u, v} (A: Type u): Type (max u v) where
  Split: A -> A -> A -> Sort v
  splitSymm {a b c: A}: Split a b c -> Split a c b
  splitAssoc {a123 a12 a1 a2 a3: A}:
    Split a123 a12 a3 -> Split a12 a1 a2 ->
      (a23: A) ×' (_: Split a123 a1 a23) ×' (Split a23 a2 a3)
  splitAssoc_inv {a123 a23 a1 a2 a3}:
    Split a123 a1 a23 -> Split a23 a2 a3 ->
      (a12: A) ×' (_: Split a123 a12 a3) ×' (Split a12 a1 a2)
      := λS1 S2 =>
        let ⟨a21, S1, S2⟩ := splitAssoc (splitSymm S1) (splitSymm S2)
        ⟨a21, splitSymm S1, splitSymm S2⟩

class Joinable.{u, v} (A: Type u): Type (max u v) where
  Joins: A -> A -> A -> Sort v
  joinsSymm {a b c: A}: Joins a b c -> Joins b a c
  joinsAssoc {a123 a12 a1 a2 a3: A}:
    Joins a12 a3 a123 -> Joins a1 a2 a12 ->
      (a23: A) ×' (_: Joins a1 a23 a123) ×' (Joins a2 a3 a23)
  joinsAssoc_inv {a123 a23 a1 a2 a3}:
    Joins a1 a23 a123 -> Joins a2 a3 a23 ->
      (a12: A) ×' (_: Joins a12 a3 a123) ×' (Joins a1 a2 a12)
      := λJ1 J2 =>
        let ⟨a21, J1, J2⟩ := joinsAssoc (joinsSymm J1) (joinsSymm J2)
        ⟨a21, joinsSymm J1, joinsSymm J2⟩

class Weakenable.{u, v} (A: Type u): Type (max u v) where
  Wk: A -> A -> Sort v
  wkId: (a: A) -> Wk a a
  wkTrans {a b c: A}: Wk a b -> Wk b c -> Wk a c

def Wks (A: Type u) := A

instance Wks.instQuiver {A: Type u} [W: Weakenable A]
  : Quiver (Wks A) where
  Hom := W.Wk

instance Wks.instCategoryStruct {A: Type u} [W: Weakenable.{u, v+1} A]
  : CategoryStruct (Wks A) where
  id := W.wkId
  comp := W.wkTrans

class Droppable.{u, v} (A: Type u) where
  Drop: A -> Sort v

class SplitWk.{u, v, w} (A: Type u)
  extends Splittable.{u, v} A, Weakenable.{u, w} A
  where
  wkLeft {a a' b c: A}: Wk a' a -> Split a b c
    -> (b': A) ×' (_: Split a' b' c) ×' (Wk b' b)
  wkRight {a a' b c: A}: Wk a' a -> Split a b c
    -> (c': A) ×' (_: Split a' b c') ×' (Wk c' c)
    := λW S =>
      let ⟨c', Ss, W⟩ := wkLeft W (splitSymm S);
      ⟨c', splitSymm Ss, W⟩
  --TODO: distributive variant?

class CSplitWk.{u, v} (A: Type u)
  extends SplitWk.{u, v} A
  where
  wkSplits {a a' b b' c c': A}: Wk a' a -> Split a b c -> Split a' b c
  splitWkLeft {a b c b': A}
    : Split a b c -> Wk b b' -> Split a b' c
  splitWkRight {a b c c': A}
    : Split a b c -> Wk c c' -> Split a b c'

def ESRes (A: Type u) := A

instance ESRes.instSplittable {A}: Splittable (ESRes A) where
  Split a b c := b = a ∧ c = a
  splitSymm | ⟨_, _⟩ => by simp [*]
  splitAssoc | ⟨_, _⟩, ⟨_, _⟩ => ⟨_, ⟨by simp [*], rfl⟩, by simp [*]⟩

instance ESRes.instWeakenable {A} [W: Weakenable A]: Weakenable (ESRes A)
  := W

def EWRes (A: Type u) := A

instance EWRes.instWeakenable {A}: Weakenable (EWRes A) where
  Wk := Eq
  wkTrans | rfl, rfl => rfl
  wkId _ := rfl

instance EWRes.instSplittable {A} [S: Splittable A]
  : Splittable (EWRes A) := S

instance EWRes.instSplitWk {A} [Splittable A]: SplitWk (EWRes A) where
  wkLeft | rfl, H => ⟨_, H, rfl⟩
  wkRight | rfl, H => ⟨_, H, rfl⟩

instance EWRes.instCSplitWk {A} [Splittable A]: CSplitWk (EWRes A) where
  wkSplits | rfl, H => H
  splitWkLeft | H, rfl => H
  splitWkRight | H, rfl => H

def PRes (A: Type u) := A

instance PRes.instWeakenable {A} [P: PartialOrder A]: Weakenable (PRes A) where
  Wk := P.le
  wkTrans := P.le_trans _ _ _
  wkId := P.le_refl
