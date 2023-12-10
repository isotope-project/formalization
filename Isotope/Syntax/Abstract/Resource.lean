namespace Abstract

--TODO: split vs ssplit?

class Splittable.{u, v} (A: Type u): Type (max u v) where
  Splits: A -> A -> A -> Sort v
  splitsSymm {a b c: A}: Splits a b c -> Splits a c b
  splitsAssoc {a123 a12 a1 a2 a3: A}:
    Splits a123 a12 a3 -> Splits a12 a1 a2 ->
      (a23: A) ×' (_: Splits a123 a1 a23) ×' (Splits a23 a2 a3)
  splitsAssoc_inv {a123 a23 a1 a2 a3}:
    Splits a123 a1 a23 -> Splits a23 a2 a3 ->
      (a12: A) ×' (_: Splits a123 a12 a3) ×' (Splits a12 a1 a2)
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
  Wks: A -> A -> Sort v
  wksTrans: {a b c: A} -> Wks a b -> Wks b c -> Wks a c

class SplitWk.{u, v} (A: Type u)
  extends Splittable.{u, v} A, Weakenable.{u, v} A
  where
  wksLeft {a a' b c: A}: Wks a' a -> Splits a b c
    -> (b': A) ×' (_: Splits a' b' c) ×' (Wks b' b)
  wksRight {a a' b c: A}: Wks a' a -> Splits a b c
    -> (c': A) ×' (_: Splits a' b c') ×' (Wks c' c)
    := λW S =>
      let ⟨c', Ss, W⟩ := wksLeft W (splitsSymm S);
      ⟨c', splitsSymm Ss, W⟩

class CSplitWk.{u, v} (A: Type u)
  extends SplitWk.{u, v} A
  where
  wksSplits {a a' b b' c c': A}: Wks a' a -> Splits a b c -> Splits a' b c

def TRes (A: Type u) := A

instance TRes.instSplittable {A}: Splittable (TRes A) where
  Splits a b c := b = a ∧ c = a
  splitsSymm | ⟨_, _⟩ => by simp [*]
  splitsAssoc | ⟨_, _⟩, ⟨_, _⟩ => ⟨_, ⟨by simp [*], rfl⟩, by simp [*]⟩

instance TRes.instWeakenable {A}: Weakenable (TRes A) where
  Wks a b := b = a
  wksTrans | rfl, rfl => rfl

instance TRes.instResource {A}: SplitWk (TRes A) where
  wksLeft | rfl, H => ⟨_, H, rfl⟩
  wksRight | rfl, H => ⟨_, H, rfl⟩

instance TRes.instCSplitWk {A}: CSplitWk (TRes A) where
  wksSplits | rfl, H => H

def TWkRes (A: Type u) := A

instance TWkRes.instSplittable {A} [S: Splittable A]
  : Splittable (TWkRes A) := S

instance TWkRes.instWeakenable {A}: Weakenable (TWkRes A) where
  Wks a b := b = a
  wksTrans | rfl, rfl => rfl

instance TWkRes.instResource {A} [Splittable A]: SplitWk (TWkRes A) where
  wksLeft | rfl, H => ⟨_, H, rfl⟩
  wksRight | rfl, H => ⟨_, H, rfl⟩

instance TWkRes.instCSplitWk {A} [Splittable A]: CSplitWk (TWkRes A) where
  wksSplits | rfl, H => H

open Splittable
open Weakenable

def Elementwise (A: Type u) := List A

inductive Elementwise.Splits.{u, v} {A: Type u} [S: Splittable.{u, v} A]
  : Elementwise A -> Elementwise A -> Elementwise A -> Sort (max (u+1) v)
  | nil: Splits [] [] []
  | cons {a b c: A} {Γ Δ Ξ: List A}: S.Splits a b c -> Splits Γ Δ Ξ ->
    Splits (a :: Γ) (b :: Δ) (c :: Ξ)

def Elementwise.Splits.symm {A} [Splittable A] {Γ Δ Ξ: Elementwise A}:
  Splits Γ Δ Ξ -> Splits Γ Ξ Δ
  | nil => nil
  | cons s sl => cons (splitsSymm s) (symm sl)

def Elementwise.Splits.assoc
  {A} [Splittable A] {Γ123 Γ12 Γ1 Γ2 Γ3: Elementwise A}:
  Splits Γ123 Γ12 Γ3 -> Splits Γ12 Γ1 Γ2 ->
      (Γ23: List A)
      ×' (_: Splits Γ123 Γ1 Γ23)
      ×' (Splits Γ23 Γ2 Γ3)
  | nil, nil => ⟨[], nil, nil⟩
  | cons s sl, cons s' sl' =>
    let ⟨a23, s, s'⟩ := splitsAssoc s s'
    let ⟨Γ23, sl, sl'⟩ := assoc sl sl'
    ⟨a23::Γ23, cons s sl, cons s' sl'⟩

instance Elementwise.instSplittable {A: Type u} [Splittable.{u, v} A]
  : Splittable.{u, max (u+1) v} (Elementwise A) where
  Splits := Splits.{u, v}
  splitsSymm := Splits.symm
  splitsAssoc := Splits.assoc

inductive Elementwise.Wks.{u, v} {A: Type u} [W: Weakenable.{u, v} A]
  : Elementwise A -> Elementwise A -> Sort (max (u+1) v)
  | nil: Wks [] []
  | cons {a b: A} {Γ Δ: Elementwise A}
    : W.Wks a b -> Wks Γ Δ -> Wks (a :: Γ) (b :: Δ)

def Elementwise.Wks.trans {A} [Weakenable A] {Γ Δ Ξ: List A}:
  Wks Γ Δ -> Wks Δ Ξ -> Wks Γ Ξ
  | nil, nil => nil
  | cons l Wl, cons r Wr => cons (wksTrans l r) (trans Wl Wr)

def Elementwise.instWeakenable {A: Type u} [Weakenable.{u, v} A]
  : Weakenable.{u, max (u+1) v} (List A) where
  Wks := Elementwise.Wks.{u, v}
  wksTrans := Elementwise.Wks.trans

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
  Splits := List.Partitions
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

def List.Sublist.trans {A} {Γ Δ Ξ: List A}
  : List.Sublist Γ Δ -> List.Sublist Δ Ξ -> List.Sublist Γ Ξ
  | H, nil => H
  | cons l H, cons _ H'  => cons l (trans H H')
  | cons l H, discard _ H' | discard l H, H' => discard l (trans H H')

def List.Sublist.weakenable {A}: Weakenable (List A) where
  Wks := List.Sublist
  wksTrans := List.Sublist.trans

--TODO: sublist/partition theorems? should this be the instance for List?
