import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.DiscreteCategory

open CategoryTheory

namespace Abstract

--TODO: split vs ssplit?

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

class CSplitWk.{u, v} (A: Type u)
  extends SplitWk.{u, v} A
  where
  wkSplits {a a' b b' c c': A}: Wk a' a -> Split a b c -> Split a' b c
  splitWkLeft {a b c b': A}
    : Split a b c -> Wk b b' -> Split a b' c
  splitWkRight {a b c c': A}
    : Split a b c -> Wk c c' -> Split a b c'

def TRes (A: Type u) := A

instance TRes.instSplittable {A}: Splittable (TRes A) where
  Split a b c := b = a ∧ c = a
  splitSymm | ⟨_, _⟩ => by simp [*]
  splitAssoc | ⟨_, _⟩, ⟨_, _⟩ => ⟨_, ⟨by simp [*], rfl⟩, by simp [*]⟩

inductive URfl.{u} {A: Type u}
  : TRes A -> TRes A -> Type u
  | urfl {a: A}: URfl a a

open URfl

instance TRes.instWeakenable {A}: Weakenable (TRes A) where
  Wk := URfl
  wkTrans | urfl, urfl => urfl
  wkId _ := urfl

instance TRes.instSplitWk {A}: SplitWk (TRes A) where
  wkLeft | urfl, H => ⟨_, H, urfl⟩
  wkRight | urfl, H => ⟨_, H, urfl⟩

instance TRes.instCSplitWk {A}: CSplitWk (TRes A) where
  wkSplits | urfl, H => H
  splitWkLeft | H, urfl => H
  splitWkRight | H, urfl => H

instance TRes.instCategory {A}: Category (Wks (TRes A)) where
  comp_id | urfl => rfl
  id_comp | urfl => rfl
  assoc | urfl, urfl, urfl => rfl

def TWkRes (A: Type u) := A

instance TWkRes.instWeakenable {A}: Weakenable (TWkRes A) where
  Wk := URfl
  wkTrans | urfl, urfl => urfl
  wkId _ := urfl

instance TWkRes.instSplittable {A} [S: Splittable A]
  : Splittable (TWkRes A) := S

instance TWkRes.instSplitWk {A} [Splittable A]: SplitWk (TWkRes A) where
  wkLeft | urfl, H => ⟨_, H, urfl⟩
  wkRight | urfl, H => ⟨_, H, urfl⟩

instance TWkRes.instCategory {A}: Category (Wks (TWkRes A)) where
  comp_id | urfl => rfl
  id_comp | urfl => rfl
  assoc | urfl, urfl, urfl => rfl

instance TWkRes.instCSplitWk {A} [Splittable A]: CSplitWk (TWkRes A) where
  wkSplits | urfl, H => H
  splitWkLeft | H, urfl => H
  splitWkRight | H, urfl => H

open Splittable
open SplitWk
open CSplitWk
open Weakenable

def Elementwise (A: Type u) := List A

inductive Elementwise.Split.{u, v} {A: Type u} [S: Splittable.{u, v} A]
  : Elementwise A -> Elementwise A -> Elementwise A -> Sort (max (u+1) v)
  | nil: Split [] [] []
  | cons {a b c: A} {Γ Δ Ξ: List A}: S.Split a b c -> Split Γ Δ Ξ ->
    Split (a :: Γ) (b :: Δ) (c :: Ξ)

def Elementwise.Split.symm {A} [Splittable A] {Γ Δ Ξ: Elementwise A}:
  Split Γ Δ Ξ -> Split Γ Ξ Δ
  | nil => nil
  | cons s sl => cons (splitSymm s) (symm sl)

def Elementwise.Split.assoc
  {A} [Splittable A] {Γ123 Γ12 Γ1 Γ2 Γ3: Elementwise A}:
  Split Γ123 Γ12 Γ3 -> Split Γ12 Γ1 Γ2 ->
      (Γ23: List A)
      ×' (_: Split Γ123 Γ1 Γ23)
      ×' (Split Γ23 Γ2 Γ3)
  | nil, nil => ⟨[], nil, nil⟩
  | cons s sl, cons s' sl' =>
    let ⟨a23, s, s'⟩ := splitAssoc s s'
    let ⟨Γ23, sl, sl'⟩ := assoc sl sl'
    ⟨a23::Γ23, cons s sl, cons s' sl'⟩

instance Elementwise.instSplittable {A: Type u} [Splittable.{u, v} A]
  : Splittable.{u, max (u+1) v} (Elementwise A) where
  Split := Split.{u, v}
  splitSymm := Split.symm
  splitAssoc := Split.assoc

inductive Elementwise.Wk.{u, v} {A: Type u} [W: Quiver.{v} (Wks A)]
  : Elementwise A -> Elementwise A -> Sort (max (u+1) v)
  | nil: Wk [] []
  | cons {a b: A} {Γ Δ: Elementwise A}
    : W.Hom a b -> Wk Γ Δ -> Wk (a :: Γ) (b :: Δ)

def Elementwise.Wk.id {A} [W: CategoryStruct (Wks A)]
  : (Γ: Elementwise A) -> Wk Γ Γ
  | [] => nil
  | l::Γ => cons (W.id l) (id Γ)

def Elementwise.Wk.trans {A} [W: CategoryStruct (Wks A)] {Γ Δ Ξ: Elementwise A}:
  Wk Γ Δ -> Wk Δ Ξ -> Wk Γ Ξ
  | nil, nil => nil
  | cons l Wl, cons r Wr => cons (W.comp l r) (trans Wl Wr)

instance Elementwise.instQuiver {A: Type u} [Quiver.{v} (Wks A)]
  : Quiver (Wks (Elementwise A)) where
  Hom := Elementwise.Wk.{u, v}

instance Elementwise.instCategoryStruct {A: Type u} [CategoryStruct.{v} (Wks A)]
  : CategoryStruct (Wks (Elementwise A)) where
  id := Elementwise.Wk.id
  comp := Elementwise.Wk.trans

-- instance Elementwise.instCategory {A: Type u} [Category.{v} (Wks A)]
--   : Category (Wks (Elementwise A)) where
--   id_comp := λW => sorry
--   comp_id := λW => sorry
--   assoc := λW W' W'' => sorry

--TODO: elementwise resource theorems, e.g. split wk

inductive List.Partitions {A: Type u}
  : List A -> List A -> List A -> Type u
  | nil: Partitions [] [] []
  | left {Γ Δ Ξ} (l): Partitions Γ Δ Ξ -> Partitions (l::Γ) (l::Δ) Ξ
  | right {Γ Δ Ξ} (r): Partitions Γ Δ Ξ -> Partitions (r::Γ) Δ (r::Ξ)

def List.Partitions.symm {A} {Γ Δ Ξ: List A}:
  List.Partitions Γ Δ Ξ -> List.Partitions Γ Ξ Δ
  | nil => nil
  | left l p => right l (symm p)
  | right r p => left r (symm p)

def List.Partitions.assoc {A}: {Γ123 Γ12 Γ1 Γ2 Γ3: List A} ->
  List.Partitions Γ123 Γ12 Γ3 -> List.Partitions Γ12 Γ1 Γ2 ->
      (Γ23: List A)
      ×' (_: List.Partitions Γ123 Γ1 Γ23)
      ×' (List.Partitions Γ23 Γ2 Γ3)
  | _, _, _, _, _, nil, nil => ⟨[], nil, nil⟩
  | _, _, _, _, _, left v p, left _ p' =>
    let ⟨Γ23, p, p'⟩ := assoc p p'
    ⟨Γ23, left v p, p'⟩
  | _, _, _, _, _, left v p, right _ p' =>
    let ⟨Γ23, p, p'⟩ := assoc p p'
    ⟨v::Γ23, right v p, left v p'⟩
  | _, _, _, _, _, right v p, p' =>
    let ⟨Γ23, p, p'⟩ := assoc p p'
    ⟨v::Γ23, right v p, right v p'⟩

def List.Partitions.splittable {A}: Splittable (List A) where
  Split := List.Partitions
  splitSymm := List.Partitions.symm
  splitAssoc := List.Partitions.assoc

def List.Partitions.joinable {A}: Joinable (List A) where
  Joins Δ Ξ Γ := List.Partitions Γ Δ Ξ
  joinsSymm := List.Partitions.symm
  joinsAssoc := List.Partitions.assoc

inductive List.Sublist {A: Type u}
  : List A -> List A -> Type u
  | nil: Sublist [] []
  | cons {Γ Δ} (l): Sublist Γ Δ -> Sublist (l::Γ) (l::Δ)
  | discard {Γ Δ} (l): Sublist Γ Δ -> Sublist (l::Γ) Δ

def List.Sublist.id {A}
  : (Γ: List A) -> List.Sublist Γ Γ
  | [] => nil
  | l::Γ => cons l (id Γ)

def List.Sublist.trans {A} {Γ Δ Ξ: List A}
  : List.Sublist Γ Δ -> List.Sublist Δ Ξ -> List.Sublist Γ Ξ
  | H, nil => H
  | cons l H, cons _ H'  => cons l (trans H H')
  | cons l H, discard _ H' | discard l H, H' => discard l (trans H H')

-- def List.Sublist.weakenable {A}: Weakenable (List A) where
--   Wk := List.Sublist
--   wkId := List.Sublist.id
--   wkTrans := List.Sublist.trans

--TODO: sublist/partition theorems? should this be the instance for List?

def SplitBoth (A: Type u) := List A

inductive SplitBoth.Split.{u, v} {A: Type u} [S: Splittable.{u, v} A]
  : SplitBoth A -> SplitBoth A -> SplitBoth A -> Sort (max (u+1) v)
  | nil: Split [] [] []
  | left (a): Split Γ Δ Ξ -> Split (a::Γ) (a::Δ) Ξ
  | right (a): Split Γ Δ Ξ -> Split (a::Γ) Δ (a::Ξ)
  | both {a b c: A} {Γ Δ Ξ: List A}: S.Split a b c -> Split Γ Δ Ξ ->
    Split (a :: Γ) (b :: Δ) (c :: Ξ)

def SplitBoth.Split.symm {A} [Splittable A] {Γ Δ Ξ: SplitBoth A}:
  Split Γ Δ Ξ -> Split Γ Ξ Δ
  | nil => nil
  | left a s => right a (symm s)
  | right a s => left a (symm s)
  | both s ss => both (splitSymm s) (symm ss)

def SplitBoth.Split.assoc {A} [Splittable A] {Γ123 Γ12 Γ1 Γ2 Γ3: SplitBoth A}:
  Split Γ123 Γ12 Γ3 -> Split Γ12 Γ1 Γ2 ->
      (Γ23: List A)
      ×' (_: Split Γ123 Γ1 Γ23)
      ×' (Split Γ23 Γ2 Γ3)
  | nil, nil => ⟨[], nil, nil⟩
  | left a s, left _ s' =>
    let ⟨Γ23, s, s'⟩ := assoc s s'
    ⟨Γ23, left a s, s'⟩
  | left a s, right _ s' =>
    let ⟨Γ23, s, s'⟩ := assoc s s'
    ⟨a::Γ23, right a s, left a s'⟩
  | left _ s, both sa s' =>
    let ⟨Γ23, s, s'⟩ := assoc s s'
    ⟨_::Γ23, both sa s, left _ s'⟩
  | right a s, s' =>
    let ⟨Γ23, s, s'⟩ := assoc s s'
    ⟨a::Γ23, right a s, right a s'⟩
  | both sa s, left _ s' =>
    let ⟨Γ23, s, s'⟩ := assoc s s'
    ⟨_::Γ23, both sa s, right _ s'⟩
  | both sa s, right _ s' =>
    let ⟨Γ23, s, s'⟩ := assoc s s'
    ⟨_::Γ23, right _ s, both sa s'⟩
  | both sa s, both sa' s' =>
    let ⟨Γ23, s, s'⟩ := assoc s s'
    let ⟨_, sa, sa'⟩ := splitAssoc sa sa';
    ⟨_::Γ23, both sa s, both sa' s'⟩

instance SplitBoth.instSplittable {A: Type u} [Splittable.{u, v} A]
  : Splittable.{u, max (u+1) v} (SplitBoth A) where
  Split := Split.{u, v}
  splitSymm := Split.symm
  splitAssoc := Split.assoc

def Elementwise.Split.toSplitBoth {A: Type u} [Splittable.{u, v} A]
  {Γ Δ Ξ: Elementwise A}: Split Γ Δ Ξ -> SplitBoth.Split Γ Δ Ξ
  | nil => SplitBoth.Split.nil
  | cons sa s => SplitBoth.Split.both sa (toSplitBoth s)

def List.Partitions.Split.toSplitBoth {A: Type u} [Splittable.{u, v} A]
  {Γ Δ Ξ: List A}: List.Partitions Γ Δ Ξ -> SplitBoth.Split Γ Δ Ξ
  | nil => SplitBoth.Split.nil
  | left l p => SplitBoth.Split.left l (toSplitBoth p)
  | right r p => SplitBoth.Split.right r (toSplitBoth p)

def SplitOrWk (A: Type u) := List A

inductive SplitOrWk.Split.{u, v, w} {A: Type u}
  [S: Splittable.{u, v} A] [Weakenable.{u, w} A]
  : SplitOrWk A -> SplitOrWk A -> SplitOrWk A -> Sort _
  | nil: Split [] [] []
  | left {a b}: Wk a b -> Split Γ Δ Ξ -> Split (a::Γ) (b::Δ) Ξ
  | right {a b}: Wk a b -> Split Γ Δ Ξ -> Split (a::Γ) Δ (b::Ξ)
  | both {a b c: A} {Γ Δ Ξ: List A}: S.Split a b c -> Split Γ Δ Ξ ->
    Split (a :: Γ) (b :: Δ) (c :: Ξ)

@[match_pattern]
def SplitOrWk.Split.sleft.{u, v, w} {A: Type u}
  [Splittable.{u, v} A] [Weakenable.{u, w} A]
  {Γ Δ Ξ} (a: A): SplitOrWk.Split Γ Δ Ξ -> SplitOrWk.Split (a::Γ) (a::Δ) Ξ
  := SplitOrWk.Split.left (wkId a)

@[match_pattern]
def SplitOrWk.Split.sright.{u, v, w} {A: Type u}
  [Splittable.{u, v} A] [Weakenable.{u, w} A]
  {Γ Δ Ξ} (a: A): SplitOrWk.Split Γ Δ Ξ -> SplitOrWk.Split (a::Γ) Δ (a::Ξ)
  := SplitOrWk.Split.right (wkId a)

def SplitOrWk.Split.symm {A}
  [Splittable A] [Weakenable A] {Γ Δ Ξ: SplitOrWk A}:
  Split Γ Δ Ξ -> Split Γ Ξ Δ
  | nil => nil
  | left a s => right a (symm s)
  | right a s => left a (symm s)
  | both s ss => both (splitSymm s) (symm ss)

def SplitOrWk.Split.assoc {A} [CSplitWk A] {Γ123 Γ12 Γ1 Γ2 Γ3: SplitOrWk A}:
  Split Γ123 Γ12 Γ3 -> Split Γ12 Γ1 Γ2 ->
      (Γ23: List A)
      ×' (_: Split Γ123 Γ1 Γ23)
      ×' (Split Γ23 Γ2 Γ3)
  | nil, nil => ⟨[], nil, nil⟩
  | left w s, left w' s' =>
    let ⟨Γ23, s, s'⟩ := assoc s s'
    ⟨Γ23, left (wkTrans w w') s, s'⟩
  | left w s, right w' s' =>
    let ⟨Γ23, s, s'⟩ := assoc s s'
    ⟨_::Γ23, right w s, left w' s'⟩
  | left w s, both sa s' =>
    let ⟨Γ23, s, s'⟩ := assoc s s'
    let ⟨_, sa, w⟩ := wkRight w sa
    ⟨_::Γ23, both sa s, left w s'⟩
  | right w s, s' =>
    let ⟨Γ23, s, s'⟩ := assoc s s'
    ⟨_::Γ23, right w s, right (wkId _) s'⟩
  | both sa s, left w s' =>
    let ⟨Γ23, s, s'⟩ := assoc s s'
    ⟨_::Γ23, both (splitWkLeft sa w) s, right (wkId _) s'⟩
  | both sa s, right w s' =>
    let ⟨Γ23, s, s'⟩ := assoc s s'
    ⟨_::Γ23, right (wkId _) s, both (splitWkLeft sa w) s'⟩
  | both sa s, both sa' s' =>
    let ⟨Γ23, s, s'⟩ := assoc s s'
    let ⟨_, sa, sa'⟩ := splitAssoc sa sa';
    ⟨_::Γ23, both sa s, both sa' s'⟩
