import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.DiscreteCategory

open CategoryTheory

class ReflexiveQuiver {A: Type u} (Q: Quiver.{v} A) where
  id (a: A): Q.Hom a a

instance CategoryStruct.instReflexiveQuiver {A: Type u} [C: CategoryStruct A]
  : ReflexiveQuiver C.toQuiver where
  id := C.id

class Precategory {A: Type u} (Q: Quiver.{v} A) extends ReflexiveQuiver Q where
  comp {a b c: A}: Q.Hom a b -> Q.Hom b c -> Q.Hom a c

instance CategoryStruct.instPrecategory {A: Type u} [C: CategoryStruct A]
  : Precategory C.toQuiver where
  comp := C.comp

class QCategory {A: Type u} (Q: Quiver.{v} A) extends Precategory Q where
  id_comp {a b: A} (f: Q.Hom a b): comp (id a) f = f
  comp_id {a b: A} (f: Q.Hom a b): comp f (id b) = f
  assoc {a b c d: A}
    (f: Q.Hom a b) (g: Q.Hom b c) (h: Q.Hom c d):
    comp (comp f g) h = comp f (comp g h)

instance CategoryStruct.instQCategory {A: Type u} [C: Category A]
  : QCategory C.toQuiver where
  id_comp := C.id_comp
  comp_id := C.comp_id
  assoc := C.assoc

-- class QuiverLike.{u, v, w} (A: Type u) (H: Type v) where
--   toQuiver: H -> Quiver.{w} A

-- class PrecategoryLike.{u, v, w} (A: Type u) (H: Type v)
--   extends QuiverLike.{u, v, w} A H
--   where
--   idOf (H: H) (a: A): (toQuiver H).Hom a a
--   compOf (H: H) {a b c: A}:
--     (toQuiver H).Hom a b ->
--     (toQuiver H).Hom b c ->
--     (toQuiver H).Hom a c

-- --TODO: toCategoryStruct

-- class CategoryLike.{u, v, w} (A: Type u) (H: Type v)
--   extends PrecategoryLike.{u, v, w} A H
--   where
--   id_comp_of (H: H) {a b: A} (f: (toQuiver H).Hom a b):
--     compOf H (idOf H a) f = f
--   comp_id_of (H: H) {a b: A} (f: (toQuiver H).Hom a b):
--     compOf H f (idOf H b) = f
--   comp_assoc_of (H: H) {a b c d: A}
--     (f: (toQuiver H).Hom a b)
--     (g: (toQuiver H).Hom b c)
--     (h: (toQuiver H).Hom c d):
--     compOf H (compOf H f g) h = compOf H f (compOf H g h)

--TODO: toCategory

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

class SWkns.{u, v, w} (A: Type u)
  extends Wkns.{u, v} A: Type (max u v w)
  where
  SWk: A -> A -> Sort w
  swkId: (a: A) -> SWk a a
  swkTrans {a b c: A}: SWk a b -> SWk b c -> SWk a c
  swkToWk {a b: A}: SWk a b -> Wk a b

-- instance Wkns.instQuiverLike {A: Type u}
--   : QuiverLike A (Wkns A) where
--   toQuiver W := { Hom := W.Wk }

open Wkns

instance instWknsUnit: Wkns Unit where
  Wk _ _ := Unit
  wkId _ := ()
  wkTrans _ _ := ()

def Wks (A: Type u) := A

instance Wks.instQuiver {A: Type u} [W: Wkns A]
  : Quiver (Wks A) where
  Hom := W.Wk

def Wks.quiver (A: Type u) [Wkns A]: Quiver A := Wks.instQuiver

instance Wks.instReflexiveQuiver {A} [W: Wkns A]
  : ReflexiveQuiver (Wks.quiver A) where
  id := W.wkId

instance Wks.instPrecategory {A} [W: Wkns A]
  : Precategory (Wks.quiver A) where
  comp := W.wkTrans

instance Wks.instCategoryStruct {A: Type u} [W: Wkns.{u, v+1} A]
  : CategoryStruct (Wks A) where
  id := W.wkId
  comp := W.wkTrans

class WkCat.{u, v} (A: Type u) extends Wkns.{u, v} A, Category (Wks A) where

--TODO: Split ==> Splat
--TODO: Splat ==> Split;(Wk × Wk)
--TODO: Wk;Split ==> Splat
class Splats.{u, v} (A: Type u) extends Splits.{u, v} A
  : Type (max u v) where
  Splat: A -> A -> A -> Sort v
  splitToSplat {a b c: A}: Split a b c -> Splat a b c
  splatSymm {a b c: A}: Splat a b c -> Splat a c b
  splatAssoc {a123 a12 a1 a2 a3: A}:
    Splat a123 a12 a3 -> Splat a12 a1 a2 ->
      (a23: A) ×' (_: Splat a123 a1 a23) ×' (Splat a23 a2 a3)
  splatAssoc_inv {a123 a23 a1 a2 a3}:
    Splat a123 a1 a23 -> Splat a23 a2 a3 ->
      (a12: A) ×' (_: Splat a123 a12 a3) ×' (Splat a12 a1 a2)
      := λs1_23 s2_3 =>
        let ⟨a21, s3_21, s2_1⟩ := splatAssoc (splatSymm s1_23) (splatSymm s2_3)
        ⟨a21, splatSymm s3_21, splatSymm s2_1⟩
  splatPermute_1234_1324 {a1234 a12 a34 a1 a2 a3 a4}:
    Splat a1234 a12 a34 -> Splat a12 a1 a2 -> Splat a34 a3 a4 ->
      (a13 a24: A)
        ×' (_: Splat a1234 a13 a24)
        ×' (_: Splat a13 a1 a3)
        ×' (Splat a24 a2 a4)
      := λs12_34 s1_2 s3_4 =>
        let ⟨_a234, s1_234, s2_34⟩ := splatAssoc s12_34 s1_2;
        let ⟨_a23, s23_4, s2_3⟩ := splatAssoc_inv s2_34 s3_4;
        let ⟨a24, s32_4, s2_4⟩ := splatAssoc s23_4 (splatSymm s2_3);
        let ⟨a13, s13_24, s1_3⟩ := splatAssoc_inv s1_234 s32_4;
        ⟨a13, a24, s13_24, s1_3, s2_4⟩

open Splats

class Drops.{u, v} (A: Type u) where
  Drop: A -> Sort v

open Drops

class DropArr.{u, v, w} (A: Type u) (Q: Quiver.{v} A) [Drops.{u, w} A]
  where
  dropArr {a b: A}: Q.Hom a b -> Drop b -> Drop a

open DropArr

class SplitDropArr.{u, s, v, d}
  (A: Type u) (S: Splits.{u, s} A) (Q: Quiver.{v} A)
  [Drops.{u, d} A] [DropArr.{u, v, d} A Q]
  where
  splitDropLeft {a b c: A}: Split a b c -> Drop b -> Q.Hom a c
  splitDropRight {a b c: A}: Split a b c -> Drop c -> Q.Hom a b
    := λs d => splitDropLeft (splitSymm s) d
  splitDrop {a b c: A}: Split a b c -> Drop b -> Drop c -> Drop a
    := λs dl dr => dropArr (splitDropLeft s dl) dr

class DropWk (A: Type u) [Wkns.{u, w} A]
  extends Drops A, DropArr A (Wks.quiver A)

abbrev DropWk.dropWk {A: Type u}
  [W: Wkns A] [D: DropWk A]
  {a b: A} : W.Wk a b -> Drop b -> Drop a
  := D.dropArr

open DropWk

class SplitDropWk (A: Type u) [S: Splits A] [Wkns A]
  extends DropWk A, SplitDropArr A S (Wks.quiver A)

open SplitDropWk

--TODO: add instance?

class DistArr.{u, s, w}
  (A: Type u)
  (S: Splits.{u, s} A)
  (H: Quiver.{w} A)
  where
  distArr {a' a b c: A}: H.Hom a' a -> Split a b c
    -> (b' c': A) ×' (_: Split a' b' c') ×' (_: H.Hom b' b) ×' (H.Hom c' c)

open DistArr

class DistWk.{u, s, w} (A: Type u) [S: Splits.{u, s} A] [W: Wkns.{u, w} A]
  extends DistArr A S (Wks.quiver A)
  where

abbrev DistWk.distWk {A} [Splits A] [Wkns A] [D: DistWk A]
  {a' a b c: A}: Wk a' a -> Split a b c
    -> (b' c': A) ×' (_: Split a' b' c') ×' (_: Wk b' b) ×' (Wk c' c)
  := D.distArr

open DistWk

class BiasedDistArr.{u, s, w} (A: Type u)
  (S: Splits.{u, s} A) (H: Quiver.{w} A)
  extends DistArr A S H
  where
  distArrLeft {a' a b c: A}: H.Hom a' a -> Split a b c
    -> (b': A) ×' (_: Split a' b' c) ×' (H.Hom b' b)
  distArrRight {a' a b c: A}: H.Hom a' a -> Split a b c
    -> (c': A) ×' (_: Split a' b c') ×' (H.Hom c' c)
    := λw s =>
      let ⟨c', s, W⟩ := distArrLeft w (splitSymm s);
      ⟨c', splitSymm s, W⟩

open BiasedDistArr

instance BiasedDistArr.instDistArr {A: Type u} {S: Splits.{u, s} A}
  {H: Quiver.{w} A} [BiasedDistArr A S H] [R: ReflexiveQuiver H]
  : DistArr A S H where
    distArr w s :=
      let ⟨c', s, w⟩ := distArrLeft w s;
      ⟨c', _, s, w, R.id _⟩

class BiasedDistWk.{u, s, w} (A: Type u) [S: Splits.{u, s} A] [Wkns.{u, w} A]
  extends BiasedDistArr A S (Wks.quiver A), DistWk A
  where
  distArr w s :=
    let ⟨c', s, w⟩ := distArrLeft w s;
    ⟨c', _, s, w, wkId _⟩

abbrev BiasedDistWk.wkLeft {A} [Splits A] [Wkns A] [D: BiasedDistWk A]
   {a' a b c: A}: Wk a' a -> Split a b c
    -> (b': A) ×' (_: Split a' b' c) ×' (Wk b' b)
   := D.distArrLeft

abbrev BiasedDistWk.wkRight {A} [Splits A] [Wkns A] [D: BiasedDistWk A]
  {a' a b c: A}: Wk a' a -> Split a b c
    -> (c': A) ×' (_: Split a' b c') ×' (Wk c' c)
  := D.distArrRight

open BiasedDistWk

instance instBiasedDistWkUnit: BiasedDistWk Unit where
  distArrLeft _ _ := ⟨(), (), ()⟩

-- class SplitWk.{u, v, w} (A: Type u)
--   extends Splits.{u, v} A, Wkns.{u, w} A, BiasedDistWk.{u, v, w} A

-- open MergeArr

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
  distArrLeft w s := ⟨_, wkSplit w s, wkId _⟩
  distArrRight w s := ⟨_, wkSplit w s, wkId _⟩
  distArr w s := ⟨_, _, wkSplit w s, wkId _, wkId _⟩

open MergeWk

-- class CSplitWk (A: Type u)
--   extends Splits.{u, v} A, Wkns.{u, w} A, MergeWk.{u, v, w} A

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
