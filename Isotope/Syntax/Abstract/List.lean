import Isotope.Syntax.Abstract.Basic

namespace Abstract

open Splits
open Wkns
open Drops
open MergeWk
open BiasedDistWk
open SplitDropArr

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

instance List.instSlittable {A}: Splits (List A) where
  Split := List.Partitions
  splitSymm := List.Partitions.symm
  splitAssoc := List.Partitions.assoc

def List.instJoinable {A}: Joins (List A) where
  Join Δ Ξ Γ := List.Partitions Γ Δ Ξ
  joinSymm := List.Partitions.symm
  joinAssoc := List.Partitions.assoc

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

instance List.instWkns {A}: Wkns (List A) where
  Wk := List.Sublist
  wkId := List.Sublist.id
  wkTrans := List.Sublist.trans

--TODO: elementwise resource theorems, e.g. split wk

def Elementwise (A: Type u) := List A

inductive Elementwise.Split.{u, v} {A: Type u} [S: Splits.{u, v} A]
  : Elementwise A -> Elementwise A -> Elementwise A -> Sort (max (u+1) v)
  | nil: Split [] [] []
  | cons {a b c: A} {Γ Δ Ξ: List A}: S.Split a b c -> Split Γ Δ Ξ ->
    Split (a :: Γ) (b :: Δ) (c :: Ξ)

def Elementwise.Split.symm {A} [Splits A] {Γ Δ Ξ: Elementwise A}:
  Split Γ Δ Ξ -> Split Γ Ξ Δ
  | nil => nil
  | cons s sl => cons (splitSymm s) (symm sl)

def Elementwise.Split.assoc
  {A} [Splits A] {Γ123 Γ12 Γ1 Γ2 Γ3: Elementwise A}:
  Split Γ123 Γ12 Γ3 -> Split Γ12 Γ1 Γ2 ->
      (Γ23: List A)
      ×' (_: Split Γ123 Γ1 Γ23)
      ×' (Split Γ23 Γ2 Γ3)
  | nil, nil => ⟨[], nil, nil⟩
  | cons s sl, cons s' sl' =>
    let ⟨a23, s, s'⟩ := splitAssoc s s'
    let ⟨Γ23, sl, sl'⟩ := assoc sl sl'
    ⟨a23::Γ23, cons s sl, cons s' sl'⟩

instance Elementwise.instSplits {A: Type u} [Splits.{u, v} A]
  : Splits.{u, max (u+1) v} (Elementwise A) where
  Split := Split.{u, v}
  splitSymm := Split.symm
  splitAssoc := Split.assoc

inductive Elementwise.Wk.{u, w} {A: Type u} [W: Wkns.{u, w} A]
  : Elementwise A -> Elementwise A -> Sort (max (u+1) w)
  | nil: Wk [] []
  | cons {a b: A} {Γ Δ: Elementwise A}
    : W.Wk a b -> Wk Γ Δ -> Wk (a :: Γ) (b :: Δ)

def Elementwise.Wk.id {A} [Wkns A]
  : (Γ: Elementwise A) -> Wk Γ Γ
  | [] => nil
  | l::Γ => cons (wkId l) (id Γ)

def Elementwise.Wk.trans {A} [Wkns A] {Γ Δ Ξ: Elementwise A}:
  Wk Γ Δ -> Wk Δ Ξ -> Wk Γ Ξ
  | nil, nil => nil
  | cons l Wl, cons r Wr => cons (wkTrans l r) (trans Wl Wr)

instance Elementwise.instWkns {A: Type u} [Wkns A]
  : Wkns (Elementwise A) where
  Wk := Elementwise.Wk
  wkId := Elementwise.Wk.id
  wkTrans :=  Elementwise.Wk.trans

def SplitBoth (A: Type u) := List A

inductive SplitBoth.Split.{u, v} {A: Type u} [S: Splits.{u, v} A]
  : SplitBoth A -> SplitBoth A -> SplitBoth A -> Sort (max (u+1) v)
  | nil: Split [] [] []
  | left (a): Split Γ Δ Ξ -> Split (a::Γ) (a::Δ) Ξ
  | right (a): Split Γ Δ Ξ -> Split (a::Γ) Δ (a::Ξ)
  | both {a b c: A} {Γ Δ Ξ: List A}: S.Split a b c -> Split Γ Δ Ξ ->
    Split (a :: Γ) (b :: Δ) (c :: Ξ)

def SplitBoth.Split.symm {A} [Splits A] {Γ Δ Ξ: SplitBoth A}:
  Split Γ Δ Ξ -> Split Γ Ξ Δ
  | nil => nil
  | left a s => right a (symm s)
  | right a s => left a (symm s)
  | both s ss => both (splitSymm s) (symm ss)

def SplitBoth.Split.assoc {A} [Splits A] {Γ123 Γ12 Γ1 Γ2 Γ3: SplitBoth A}:
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

instance SplitBoth.instSplits {A: Type u} [Splits.{u, v} A]
  : Splits.{u, max (u+1) v} (SplitBoth A) where
  Split := Split.{u, v}
  splitSymm := Split.symm
  splitAssoc := Split.assoc

def Elementwise.Split.toSplitBoth {A: Type u} [Splits.{u, v} A]
  {Γ Δ Ξ: Elementwise A}: Split Γ Δ Ξ -> SplitBoth.Split Γ Δ Ξ
  | nil => SplitBoth.Split.nil
  | cons sa s => SplitBoth.Split.both sa (toSplitBoth s)

def List.Partitions.Split.toSplitBoth {A: Type u} [Splits.{u, v} A]
  {Γ Δ Ξ: List A}: List.Partitions Γ Δ Ξ -> SplitBoth.Split Γ Δ Ξ
  | nil => SplitBoth.Split.nil
  | left l p => SplitBoth.Split.left l (toSplitBoth p)
  | right r p => SplitBoth.Split.right r (toSplitBoth p)

--TODO: instCSplitWk

def SplitOrWk (A: Type u) := List A

inductive SplitOrWk.Split.{u, v, w} {A: Type u}
  [S: Splits.{u, v} A] [Wkns.{u, w} A]
  : SplitOrWk A -> SplitOrWk A -> SplitOrWk A -> Sort (max (u + 1) v w)
  | nil: Split [] [] []
  | left {a b}: Wk a b -> Split Γ Δ Ξ -> Split (a::Γ) (b::Δ) Ξ
  | right {a b}: Wk a b -> Split Γ Δ Ξ -> Split (a::Γ) Δ (b::Ξ)
  | both {a b c: A} {Γ Δ Ξ: List A}: S.Split a b c -> Split Γ Δ Ξ ->
    Split (a :: Γ) (b :: Δ) (c :: Ξ)

def SplitOrWk.Wk.{u, w} {A: Type u} [Wkns.{u, w} A]
  : SplitOrWk A -> SplitOrWk A -> Sort (max (u + 1) w) := Elementwise.Wk

@[match_pattern]
def SplitOrWk.Wk.nil {A} [Wkns A]: @Wk A _ [] [] := Elementwise.Wk.nil

@[match_pattern]
def SplitOrWk.Wk.cons {A} [W: Wkns A] {Γ Δ: SplitOrWk A} {a b: A}
  : W.Wk a b -> Wk Γ Δ -> Wk (a::Γ) (b::Δ)
  := Elementwise.Wk.cons

def SplitOrWk.Wk.id {A} [Wkns A] (Γ: SplitOrWk A)
  : Wk Γ Γ := Elementwise.Wk.id Γ

def SplitOrWk.Wk.trans {A} [Wkns A] {Γ Δ Ξ: SplitOrWk A}
  : Wk Γ Δ -> Wk Δ Ξ -> Wk Γ Ξ
  := Elementwise.Wk.trans

@[match_pattern]
def SplitOrWk.Split.sleft.{u, v, w} {A: Type u}
  [Splits.{u, v} A] [Wkns.{u, w} A]
  {Γ Δ Ξ} (a: A): SplitOrWk.Split Γ Δ Ξ -> SplitOrWk.Split (a::Γ) (a::Δ) Ξ
  := SplitOrWk.Split.left (wkId a)

@[match_pattern]
def SplitOrWk.Split.sright.{u, v, w} {A: Type u}
  [Splits.{u, v} A] [Wkns.{u, w} A]
  {Γ Δ Ξ} (a: A): SplitOrWk.Split Γ Δ Ξ -> SplitOrWk.Split (a::Γ) Δ (a::Ξ)
  := SplitOrWk.Split.right (wkId a)

def SplitOrWk.Split.symm {A}
  [Splits A] [Wkns A] {Γ Δ Ξ: SplitOrWk A}:
  Split Γ Δ Ξ -> Split Γ Ξ Δ
  | nil => nil
  | left a s => right a (symm s)
  | right a s => left a (symm s)
  | both s ss => both (splitSymm s) (symm ss)

def SplitOrWk.Split.assoc {A}
  [Splits.{u, v} A] [Wkns.{u, w} A] [MergeWk.{u, v, w} A]
  {Γ123 Γ12 Γ1 Γ2 Γ3: SplitOrWk A}:
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
    let ⟨_, sa, sa'⟩ := splitAssoc sa sa'
    ⟨_::Γ23, both sa s, both sa' s'⟩

def SplitOrWk.Split.wkSplit {A}
  [Splits.{u, v} A] [Wkns.{u, w} A] [MergeWk.{u, v, w} A]
  {Γ' Γ Δ Ξ: SplitOrWk A}: Wk Γ' Γ -> Split Γ Δ Ξ -> Split Γ' Δ Ξ
  | Wk.nil, nil => nil
  | Wk.cons w W, left w' s => left (wkTrans w w') (wkSplit W s)
  | Wk.cons w W, right w' s => right (wkTrans w w') (wkSplit W s)
  | Wk.cons w W, both sa s => both (MergeWk.wkSplit w sa) (wkSplit W s)

def SplitOrWk.Split.splitWkLeft {A}
  [Splits.{u, v} A] [Wkns.{u, w} A] [MergeWk.{u, v, w} A]
  {Γ Δ Δ' Ξ: SplitOrWk A}: Split Γ Δ Ξ -> Wk Δ Δ' -> Split Γ Δ' Ξ
  | nil, Wk.nil => nil
  | left w S, Wk.cons w' W => left (wkTrans w w') (splitWkLeft S W)
  | right w S, W => right w (splitWkLeft S W)
  | both sa S, Wk.cons w' W
    => both (MergeWk.splitWkLeft sa w') (splitWkLeft S W)

def SplitOrWk.Split.splitWkRight {A}
  [Splits.{u, v} A] [Wkns.{u, w} A] [MergeWk.{u, v, w} A]
  {Γ Δ Ξ Ξ': SplitOrWk A}: Split Γ Δ Ξ -> Wk Ξ Ξ' -> Split Γ Δ Ξ'
  | nil, Wk.nil => nil
  | left w S, W => left w (splitWkRight S W)
  | right w S, Wk.cons w' W => right (wkTrans w w') (splitWkRight S W)
  | both sa S, Wk.cons w' W
    => both (MergeWk.splitWkRight sa w') (splitWkRight S W)

instance SplitOrWk.instWkns {A: Type u} [Wkns.{u, w} A]
  : Wkns.{u, max (u + 1) w} (SplitOrWk A) where
  Wk := Wk
  wkId := Wk.id
  wkTrans := Wk.trans

instance SplitOrWk.instSplits {A: Type u}
  [Splits.{u, v} A] [Wkns.{u, w} A] [MergeWk.{u, v, w} A]
  : Splits.{u, max (u + 1) v w} (SplitOrWk A) where
  Split := Split
  splitSymm := Split.symm
  splitAssoc := Split.assoc

instance SplitOrWk.instMergeWk {A: Type u}
  [Splits.{u, v} A] [Wkns.{u, w} A] [MergeWk.{u, v, w} A]
  : MergeWk.{u, max (u + 1) v w, _} (SplitOrWk A) where
  wkSplit := Split.wkSplit
  splitWkLeft := Split.splitWkLeft
  splitWkRight := Split.splitWkRight

def DropOrWk (A: Type u) := List A

inductive DropOrWk.Split.{u, v, w, d} {A: Type u}
  [S: Splits.{u, v} A] [Wkns.{u, w} A] [Drops.{u, d} A]
  : DropOrWk A -> DropOrWk A -> DropOrWk A -> Type (max u v w d)
  | nil: Split [] [] []
  | left {a b}: Wk a b -> Split Γ Δ Ξ -> Split (a::Γ) (b::Δ) Ξ
  | right {a b}: Wk a b -> Split Γ Δ Ξ -> Split (a::Γ) Δ (b::Ξ)
  | both {a b c: A} {Γ Δ Ξ: List A}: S.Split a b c -> Split Γ Δ Ξ ->
    Split (a :: Γ) (b :: Δ) (c :: Ξ)
  | discard {a: A}: Drop a -> Split Γ Δ Ξ -> Split (a::Γ) Δ Ξ

@[match_pattern]
def DropOrWk.Split.sleft.{u, v, w, d} {A: Type u}
  [Splits.{u, v} A] [Wkns.{u, w} A] [Drops.{u, d} A]
  {Γ Δ Ξ} (a: A): Split Γ Δ Ξ -> Split (a::Γ) (a::Δ) Ξ
  := Split.left (wkId a)

@[match_pattern]
def DropOrWk.Split.sright.{u, v, w} {A: Type u}
  [Splits.{u, v} A] [Wkns.{u, w} A] [Drops.{u, d} A]
  {Γ Δ Ξ} (a: A): Split Γ Δ Ξ -> Split (a::Γ) Δ (a::Ξ)
  := Split.right (wkId a)

@[match_pattern]
def DropOrWk.Split.symm {A}
  [Splits A] [Wkns A] [Drops A] {Γ Δ Ξ: DropOrWk A}:
  Split Γ Δ Ξ -> Split Γ Ξ Δ
  | nil => nil
  | left a s => right a (symm s)
  | right a s => left a (symm s)
  | both s ss => both (splitSymm s) (symm ss)
  | discard d s => discard d (symm s)

@[match_pattern]
def DropOrWk.Split.assoc {A}
  [Splits.{u, v} A] [Wkns.{u, w} A]
  [MergeWk.{u, v, w} A] [D: SplitDropWk A]
  {Γ123 Γ12 Γ1 Γ2 Γ3: DropOrWk A}:
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
  | left w s, discard d s' =>
    let ⟨Γ23, s, s'⟩ := assoc s s'
    ⟨_::Γ23, right w s, discard d s'⟩
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
    let ⟨_, sa, sa'⟩ := splitAssoc sa sa'
    ⟨_::Γ23, both sa s, both sa' s'⟩
  | both sa s, discard d s' =>
    let ⟨Γ23, s, s'⟩ := assoc s s'
    ⟨_::Γ23, sright _ s, right (D.splitDropLeft sa d) s'⟩
  | discard d s, s' =>
    let ⟨_, s, s'⟩ := assoc s s'
    ⟨_, discard d s, s'⟩

-- instance DropOrWk.instWkns {A: Type u} [Wkns.{u, w} A]
--   : Wkns.{u, max (u + 1) w} (DropOrWk A) where
--   Wk := Wk
--   wkId := Wk.id
--   wkTrans := Wk.trans

instance DropOrWk.instSplits {A: Type u}
  [Splits.{u, v} A] [Wkns.{u, w} A]
  [MergeWk.{u, v, w} A] [SplitDropWk A]
  : Splits (DropOrWk A) where
  Split := Split
  splitSymm := Split.symm
  splitAssoc := Split.assoc

-- instance SplitOrWk.instMergeWk {A: Type u}
--   [Splits.{u, v} A] [Wkns.{u, w} A] [MergeWk.{u, v, w} A]
--   : MergeWk.{u, max (u + 1) v w, _} (SplitOrWk A) where
--   wkSplit := Split.wkSplit
--   splitWkLeft := Split.splitWkLeft
--   splitWkRight := Split.splitWkRight

--TODO: weaken + drop

--TODO: weaken w/ discard

--TODO: split w/ discard

--TODO: merge related inductives?
