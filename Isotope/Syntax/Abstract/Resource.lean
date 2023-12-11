namespace Abstract

--TODO: split vs ssplit?

class Splittable.{u, v} (A: Type u): Type (max u v) where
  Split: A -> A -> A -> Sort v
  splitsSymm {a b c: A}: Split a b c -> Split a c b
  splitsAssoc {a123 a12 a1 a2 a3: A}:
    Split a123 a12 a3 -> Split a12 a1 a2 ->
      (a23: A) ×' (_: Split a123 a1 a23) ×' (Split a23 a2 a3)
  splitsAssoc_inv {a123 a23 a1 a2 a3}:
    Split a123 a1 a23 -> Split a23 a2 a3 ->
      (a12: A) ×' (_: Split a123 a12 a3) ×' (Split a12 a1 a2)
      := λS1 S2 =>
        let ⟨a21, S1, S2⟩ := splitsAssoc (splitsSymm S1) (splitsSymm S2)
        ⟨a21, splitsSymm S1, splitsSymm S2⟩

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

class Weakenable.{u, v} (A: Type u) where
  Wk: A -> A -> Sort v
  wkId (a: A): Wk a a
  wkTrans {a b c: A}: Wk a b -> Wk b c -> Wk a c

class Droppable.{u, v} (A: Type u) where
  Drop: A -> Sort v

class SplitWk.{u, v} (A: Type u)
  extends Splittable.{u, v} A, Weakenable.{u, v} A
  where
  wkLeft {a a' b c: A}: Wk a' a -> Split a b c
    -> (b': A) ×' (_: Split a' b' c) ×' (Wk b' b)
  wkRight {a a' b c: A}: Wk a' a -> Split a b c
    -> (c': A) ×' (_: Split a' b c') ×' (Wk c' c)
    := λW S =>
      let ⟨c', Ss, W⟩ := wkLeft W (splitsSymm S);
      ⟨c', splitsSymm Ss, W⟩

class CSplitWk.{u, v} (A: Type u)
  extends SplitWk.{u, v} A
  where
  wkSplits {a a' b b' c c': A}: Wk a' a -> Split a b c -> Split a' b c
  splitsWks {a b c b' c': A}
    : Split a b c -> Wk b b' -> Wk c c' -> Split a b' c'

def TRes (A: Type u) := A

instance TRes.instSplittable {A}: Splittable (TRes A) where
  Split a b c := b = a ∧ c = a
  splitsSymm | ⟨_, _⟩ => by simp [*]
  splitsAssoc | ⟨_, _⟩, ⟨_, _⟩ => ⟨_, ⟨by simp [*], rfl⟩, by simp [*]⟩

instance TRes.instWeakenable {A}: Weakenable (TRes A) where
  Wk a b := b = a
  wkId _ := rfl
  wkTrans | rfl, rfl => rfl

instance TRes.instResource {A}: SplitWk (TRes A) where
  wkLeft | rfl, H => ⟨_, H, rfl⟩
  wkRight | rfl, H => ⟨_, H, rfl⟩

instance TRes.instCSplitWk {A}: CSplitWk (TRes A) where
  wkSplits | rfl, H => H
  splitsWks | H, rfl, rfl => H

def TWkRes (A: Type u) := A

instance TWkRes.instSplittable {A} [S: Splittable A]
  : Splittable (TWkRes A) := S

instance TWkRes.instWeakenable {A}: Weakenable (TWkRes A) where
  Wk a b := b = a
  wkId _ := rfl
  wkTrans | rfl, rfl => rfl

instance TWkRes.instResource {A} [Splittable A]: SplitWk (TWkRes A) where
  wkLeft | rfl, H => ⟨_, H, rfl⟩
  wkRight | rfl, H => ⟨_, H, rfl⟩

instance TWkRes.instCSplitWk {A} [Splittable A]: CSplitWk (TWkRes A) where
  wkSplits | rfl, H => H
  splitsWks | H, rfl, rfl => H

open Splittable
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
  | cons s sl => cons (splitsSymm s) (symm sl)

def Elementwise.Split.assoc
  {A} [Splittable A] {Γ123 Γ12 Γ1 Γ2 Γ3: Elementwise A}:
  Split Γ123 Γ12 Γ3 -> Split Γ12 Γ1 Γ2 ->
      (Γ23: List A)
      ×' (_: Split Γ123 Γ1 Γ23)
      ×' (Split Γ23 Γ2 Γ3)
  | nil, nil => ⟨[], nil, nil⟩
  | cons s sl, cons s' sl' =>
    let ⟨a23, s, s'⟩ := splitsAssoc s s'
    let ⟨Γ23, sl, sl'⟩ := assoc sl sl'
    ⟨a23::Γ23, cons s sl, cons s' sl'⟩

instance Elementwise.instSplittable {A: Type u} [Splittable.{u, v} A]
  : Splittable.{u, max (u+1) v} (Elementwise A) where
  Split := Split.{u, v}
  splitsSymm := Split.symm
  splitsAssoc := Split.assoc

inductive Elementwise.Wk.{u, v} {A: Type u} [W: Weakenable.{u, v} A]
  : Elementwise A -> Elementwise A -> Sort (max (u+1) v)
  | nil: Wk [] []
  | cons {a b: A} {Γ Δ: Elementwise A}
    : W.Wk a b -> Wk Γ Δ -> Wk (a :: Γ) (b :: Δ)

def Elementwise.Wk.id {A} [W: Weakenable A]
  : (Γ: Elementwise A) -> Wk Γ Γ
  | [] => nil
  | l::Γ => cons (W.wkId l) (id Γ)

def Elementwise.Wk.trans {A} [Weakenable A] {Γ Δ Ξ: Elementwise A}:
  Wk Γ Δ -> Wk Δ Ξ -> Wk Γ Ξ
  | nil, nil => nil
  | cons l Wl, cons r Wr => cons (wkTrans l r) (trans Wl Wr)

def Elementwise.instWeakenable {A: Type u} [Weakenable.{u, v} A]
  : Weakenable.{u, max (u+1) v} (List A) where
  Wk := Elementwise.Wk.{u, v}
  wkId := Elementwise.Wk.id
  wkTrans := Elementwise.Wk.trans

--TODO: elementwise resource theorems

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
  splitsSymm := List.Partitions.symm
  splitsAssoc := List.Partitions.assoc

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

def List.Sublist.weakenable {A}: Weakenable (List A) where
  Wk := List.Sublist
  wkId := List.Sublist.id
  wkTrans := List.Sublist.trans

--TODO: sublist/partition theorems? should this be the instance for List?
