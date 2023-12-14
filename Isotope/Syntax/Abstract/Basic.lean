import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.DiscreteCategory

open CategoryTheory

namespace Abstract

class Splits.{u, v} (A: Type u): Type (max u v) where
  Split: A -> A -> A -> Sort v
  splitSymm {a b c: A}: Split a b c -> Split a c b
  splitAssoc {a123 a12 a1 a2 a3: A}:
    Split a123 a12 a3 -> Split a12 a1 a2 ->
      (a23: A) ×' (_: Split a123 a1 a23) ×' (Split a23 a2 a3)
  splitAssoc_inv {a123 a23 a1 a2 a3}:
    Split a123 a1 a23 -> Split a23 a2 a3 ->
      (a12: A) ×' (_: Split a123 a12 a3) ×' (Split a12 a1 a2)
      := λs1_23 s2_3 =>
        let ⟨a21, s3_21, s2_1⟩ := splitAssoc (splitSymm s1_23) (splitSymm s2_3)
        ⟨a21, splitSymm s3_21, splitSymm s2_1⟩
  permute_1234_1324 {a1234 a12 a34 a1 a2 a3 a4}:
    Split a1234 a12 a34 -> Split a12 a1 a2 -> Split a34 a3 a4 ->
      (a13 a24: A)
        ×' (_: Split a1234 a13 a24)
        ×' (_: Split a13 a1 a3)
        ×' (Split a24 a2 a4)
      := λs12_34 s1_2 s3_4 =>
        let ⟨_a234, s1_234, s2_34⟩ := splitAssoc s12_34 s1_2;
        let ⟨_a23, s23_4, s2_3⟩ := splitAssoc_inv s2_34 s3_4;
        let ⟨a24, s32_4, s2_4⟩ := splitAssoc s23_4 (splitSymm s2_3);
        let ⟨a13, s13_24, s1_3⟩ := splitAssoc_inv s1_234 s32_4;
        ⟨a13, a24, s13_24, s1_3, s2_4⟩

open Splits

instance instSplitsUnit: Splits Unit where
  Split _ _ _ := Unit
  splitSymm _ := ()
  splitAssoc _ _ := ⟨(), (), ()⟩

class Joins.{u, v} (A: Type u): Type (max u v) where
  Join: A -> A -> A -> Sort v
  joinSymm {a b c: A}: Join a b c -> Join b a c
  joinAssoc {a123 a12 a1 a2 a3: A}:
    Join a12 a3 a123 -> Join a1 a2 a12 ->
      (a23: A) ×' (_: Join a1 a23 a123) ×' (Join a2 a3 a23)
  joinAssoc_inv {a123 a23 a1 a2 a3}:
    Join a1 a23 a123 -> Join a2 a3 a23 ->
      (a12: A) ×' (_: Join a12 a3 a123) ×' (Join a1 a2 a12)
      := λJ1 J2 =>
        let ⟨a21, J1, J2⟩ := joinAssoc (joinSymm J1) (joinSymm J2)
        ⟨a21, joinSymm J1, joinSymm J2⟩

open Joins

instance instJoinsUnit: Joins Unit where
  Join _ _ _ := Unit
  joinSymm _ := ()
  joinAssoc _ _ := ⟨(), (), ()⟩

class Wkns.{u, v} (A: Type u): Type (max u v) where
  Wk: A -> A -> Sort v
  wkId: (a: A) -> Wk a a
  wkTrans {a b c: A}: Wk a b -> Wk b c -> Wk a c

open Wkns

instance instWknsUnit: Wkns Unit where
  Wk _ _ := Unit
  wkId _ := ()
  wkTrans _ _ := ()

def Wks (A: Type u) := A

instance Wks.instQuiver {A: Type u} [W: Wkns A]
  : Quiver (Wks A) where
  Hom := W.Wk

instance Wks.instCategoryStruct {A: Type u} [W: Wkns.{u, v+1} A]
  : CategoryStruct (Wks A) where
  id := W.wkId
  comp := W.wkTrans

class Droppable.{u, v} (A: Type u) where
  Drop: A -> Sort v

class DropWk.{u, v} (A: Type u) [Wkns.{u, w} A]
  extends Droppable.{u, v} A
  where
  dropWk {a b: A}: Wk a b -> Drop a -> Drop b

class DistWk.{u, s, w} (A: Type u) [Splits.{u, s} A] [Wkns.{u, w} A]
  where
  distWk {a' a b c: A}: Wk a' a -> Split a b c
    -> (b' c': A) ×' (_: Split a' b' c') ×' (_: Wk b' b) ×' (Wk c' c)

open DistWk

class BiasedDistWk.{u, s, w} (A: Type u) [Splits.{u, s} A] [Wkns.{u, w} A]
  extends DistWk A
  where
  wkLeft {a' a b c: A}: Wk a' a -> Split a b c
    -> (b': A) ×' (_: Split a' b' c) ×' (Wk b' b)
  wkRight {a' a b c: A}: Wk a' a -> Split a b c
    -> (c': A) ×' (_: Split a' b c') ×' (Wk c' c)
    := λw s =>
      let ⟨c', s, W⟩ := wkLeft w (splitSymm s);
      ⟨c', splitSymm s, W⟩
  distWk w s :=
      let ⟨c', s, w⟩ := wkLeft w s;
      ⟨c', _, s, w, wkId _⟩

open BiasedDistWk

instance instBiasedDistWkUnit: BiasedDistWk Unit where
  wkLeft _ _ := ⟨(), (), ()⟩

class SplitWk.{u, v, w} (A: Type u)
  extends Splits.{u, v} A, Wkns.{u, w} A, BiasedDistWk.{u, v, w} A
  --TODO: distributive variant?

class MergeWk.{u, s, w} (A: Type u) [Splits.{u, s} A] [Wkns.{u, w} A]
  extends BiasedDistWk.{u, s, w} A
  where
  wkSplit {a' a b c: A}: Wk a' a -> Split a b c -> Split a' b c
  splitWkLeft {a b c b': A}
    : Split a b c -> Wk b b' -> Split a b' c
  splitWkRight {a b c c': A}
    : Split a b c -> Wk c c' -> Split a b c'
    := λs w => splitSymm (splitWkLeft (splitSymm s) w)
  splitWk {a b c b' c': A}
    : Split a b c -> Wk b b' -> Wk c c' -> Split a b' c'
    := λs wl wr => splitWkRight (splitWkLeft s wl) wr
  wkLeft w s := ⟨_, wkSplit w s, wkId _⟩
  wkRight w s := ⟨_, wkSplit w s, wkId _⟩
  distWk w s := ⟨_, _, wkSplit w s, wkId _, wkId _⟩

open MergeWk

class CSplitWk (A: Type u)
  extends Splits.{u, v} A, Wkns.{u, w} A, MergeWk.{u, v, w} A

-- instance CSplitWk.instSplitWk {A} [W: CSplitWk A]: SplitWk A where
--   wkLeft w s := ⟨_, wkSplit w s, W.wkId _⟩
--   wkRight w s := ⟨_, wkSplit w s, W.wkId _⟩

def ESRes (A: Type u) := A

instance ESRes.instSplits {A}: Splits (ESRes A) where
  Split a b c := b = a ∧ c = a
  splitSymm | ⟨_, _⟩ => by simp [*]
  splitAssoc | ⟨_, _⟩, ⟨_, _⟩ => ⟨_, ⟨by simp [*], rfl⟩, by simp [*]⟩

instance ESRes.instWkns {A} [W: Wkns A]: Wkns (ESRes A)
  := W

def EWRes (A: Type u) := A

instance EWRes.instWkns {A}: Wkns (EWRes A) where
  Wk := Eq
  wkTrans | rfl, rfl => rfl
  wkId _ := rfl

instance EWRes.instSplits {A} [S: Splits A]
  : Splits (EWRes A) := S

-- instance EWRes.instCSplitWk {A} [Splits A]: CSplitWk (EWRes A) where
--   wkSplit | rfl, H => H
--   splitWkLeft | H, rfl => H
--   splitWkRight | H, rfl => H

def PRes (A: Type u) := A

instance PRes.instWkns {A} [P: PartialOrder A]: Wkns (PRes A) where
  Wk a b := P.le b a
  wkTrans H H' := P.le_trans _ _ _ H' H
  wkId := P.le_refl

instance PRes.instSplits {A} [P: PartialOrder A]: Splits (PRes A) where
  Split a b c := P.le b a ∧ P.le c a
  splitSymm | ⟨_, _⟩ => by simp [*]
  splitAssoc | ⟨Ha12, Ha3⟩, ⟨Ha1, Ha2⟩ => ⟨_, -- a23 = a123
    ⟨le_trans Ha1 Ha12, le_refl _⟩,
    ⟨le_trans Ha2 Ha12, Ha3⟩⟩

-- instance PRes.instCSplitWk {A} [PartialOrder A]: CSplitWk (PRes A) where
--   wkSplit | H, ⟨Hl, Hr⟩ => ⟨le_trans Hl H, le_trans Hr H⟩
--   splitWkLeft | ⟨Hl, Hr⟩, H => ⟨le_trans H Hl, Hr⟩
--   splitWkRight | ⟨Hl, Hr⟩, H => ⟨Hl, le_trans H Hr⟩
