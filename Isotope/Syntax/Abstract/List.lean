import Isotope.Syntax.Abstract.Basic

namespace Abstract

open Splittable
open SplitWk
open CSplitWk
open Weakenable

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

instance List.instSlittable {A}: Splittable (List A) where
  Split := List.Partitions
  splitSymm := List.Partitions.symm
  splitAssoc := List.Partitions.assoc

def List.instJoinable {A}: Joinable (List A) where
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

instance List.instWeakenable {A}: Weakenable (List A) where
  Wk := List.Sublist
  wkId := List.Sublist.id
  wkTrans := List.Sublist.trans

--TODO: elementwise resource theorems, e.g. split wk

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

inductive Elementwise.Wk.{u, v, w} {A: Type u} [W: Weakenable.{u, w} A]
  : Elementwise A -> Elementwise A -> Sort (max (u+1) v w)
  | nil: Wk [] []
  | cons {a b: A} {Γ Δ: Elementwise A}
    : W.Wk a b -> Wk Γ Δ -> Wk (a :: Γ) (b :: Δ)

def Elementwise.Wk.id {A} [Weakenable A]
  : (Γ: Elementwise A) -> Wk Γ Γ
  | [] => nil
  | l::Γ => cons (wkId l) (id Γ)

def Elementwise.Wk.trans {A} [Weakenable A] {Γ Δ Ξ: Elementwise A}:
  Wk Γ Δ -> Wk Δ Ξ -> Wk Γ Ξ
  | nil, nil => nil
  | cons l Wl, cons r Wr => cons (wkTrans l r) (trans Wl Wr)

instance Elementwise.instWeakenable {A: Type u} [Weakenable A]
  : Weakenable (Elementwise A) where
  Wk := Elementwise.Wk
  wkId := Elementwise.Wk.id
  wkTrans :=  Elementwise.Wk.trans

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

--TODO: instCSplitWk

def SplitOrWk (A: Type u) := List A

inductive SplitOrWk.Split.{u, v, w} {A: Type u}
  [S: Splittable.{u, v} A] [Weakenable.{u, w} A]
  : SplitOrWk A -> SplitOrWk A -> SplitOrWk A -> Sort _
  | nil: Split [] [] []
  | left {a b}: Wk a b -> Split Γ Δ Ξ -> Split (a::Γ) (b::Δ) Ξ
  | right {a b}: Wk a b -> Split Γ Δ Ξ -> Split (a::Γ) Δ (b::Ξ)
  | both {a b c: A} {Γ Δ Ξ: List A}: S.Split a b c -> Split Γ Δ Ξ ->
    Split (a :: Γ) (b :: Δ) (c :: Ξ)

def SplitOrWk.Wk {A} [Weakenable A]
  : SplitOrWk A -> SplitOrWk A -> Sort _ := Elementwise.Wk

@[match_pattern]
def SplitOrWk.Wk.nil {A} [Weakenable A]: @Wk A _ [] [] := Elementwise.Wk.nil

@[match_pattern]
def SplitOrWk.Wk.cons {A} [W: Weakenable A] {Γ Δ: SplitOrWk A} {a b: A}
  : W.Wk a b -> Wk Γ Δ -> Wk (a::Γ) (b::Δ)
  := Elementwise.Wk.cons

def SplitOrWk.Wk.id {A} [Weakenable A] (Γ: SplitOrWk A)
  : Wk Γ Γ := Elementwise.Wk.id Γ

def SplitOrWk.Wk.trans {A} [Weakenable A] {Γ Δ Ξ: SplitOrWk A}
  : Wk Γ Δ -> Wk Δ Ξ -> Wk Γ Ξ
  := Elementwise.Wk.trans

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

--TODO: toSplitOrWk for SplitOrBoth, Elementwise, Partition

instance SplitOrWk.instWeakenable {A} [Weakenable A]
  : Weakenable (SplitOrWk A) where
  Wk := Wk
  wkId := Wk.id
  wkTrans := Wk.trans

instance SplitOrWk.instSplittable {A} [CSplitWk A]
  : Splittable (SplitOrWk A) where
  Split := Split
  splitSymm := Split.symm
  splitAssoc := Split.assoc

--TODO: instCSplitWk

--TODO: weaken + drop

--TODO: weaken w/ discard

--TODO: split w/ discard

--TODO: merge related inductives?
