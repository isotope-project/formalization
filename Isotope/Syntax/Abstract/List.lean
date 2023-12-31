import Isotope.Syntax.Abstract.Basic

namespace Abstract

open Wkns
open Splits
open Joins
open Drops
open WkDrop
open SplitWk
open BiasedDistWkSplit
open DropToSplit
open SplitDropWk

inductive List.SubList {A: Type u}
  : List A -> List A -> Type u
  | nil: SubList [] []
  | cons {Γ Δ} (l): SubList Γ Δ -> SubList (l::Γ) (l::Δ)
  | discard {Γ Δ} (l): SubList Γ Δ -> SubList (l::Γ) Δ

def List.SubList.id {A}
  : (Γ: List A) -> SubList Γ Γ
  | [] => nil
  | l::Γ => cons l (id Γ)

def List.SubList.trans {A} {Γ Δ Ξ: List A}
  : SubList Γ Δ -> SubList Δ Ξ -> SubList Γ Ξ
  | H, nil => H
  | cons l H, cons _ H'  => cons l (trans H H')
  | cons l H, discard _ H' | discard l H, H' => discard l (trans H H')

instance List.instWkns {A}: Wkns (List A) where
  Wk := SubList
  wkId := SubList.id
  wkTrans := SubList.trans

structure List.SubLists {A: Type u} (Γ Δ Ξ: List A) where
  left: List.SubList Γ Δ
  right: List.SubList Γ Ξ

def List.SubLists.symm {A: Type u} {Γ Δ Ξ: List A}
  (H: SubLists Γ Δ Ξ): SubLists Γ Ξ Δ where
  left := H.right
  right := H.left

def List.SubLists.assoc {A: Type u} {Γ123 Γ12 Γ1 Γ2 Γ3: List A}
  (H12_3: SubLists Γ123 Γ12 Γ3) (H12: SubLists Γ12 Γ1 Γ2)
  : (Γ23: List A)
    ×' (_: SubLists Γ123 Γ1 Γ23)
    ×' (SubLists Γ23 Γ2 Γ3)
  := ⟨
    Γ123,
    {
      left := H12_3.left.trans H12.left,
      right := List.SubList.id Γ123
    },
    {
      left := H12_3.left.trans H12.right,
      right := H12_3.right
    }
  ⟩

instance List.instSplittable {A}: Splits (List A) where
  Split := List.SubLists
  splitSymm := List.SubLists.symm
  splitAssoc := List.SubLists.assoc

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

def List.Partitions.leftSubList {A} {Γ Δ Ξ: List A}
  : List.Partitions Γ Δ Ξ -> SubList Γ Δ
  | nil => SubList.nil
  | left l p => SubList.cons l (leftSubList p)
  | right r p => SubList.discard r (leftSubList p)

def List.Partitions.rightSubList {A} {Γ Δ Ξ: List A}
  : List.Partitions Γ Δ Ξ -> SubList Γ Ξ
  | nil => SubList.nil
  | left l p => SubList.discard l (rightSubList p)
  | right r p => SubList.cons r (rightSubList p)

def List.Partitions.toSubLists {A} {Γ Δ Ξ: List A}
  (H: List.Partitions Γ Δ Ξ): List.SubLists Γ Δ Ξ where
  left := H.leftSubList
  right := H.rightSubList

instance List.instSSplits {A}: SSplits (List A) where
  SSplit := Partitions
  ssplitToSplit := Partitions.toSubLists
  ssplitSymm := Partitions.symm
  ssplitAssoc := Partitions.assoc

--TODO: fix this
instance List.instJoinable {A}: Joins (List A) where
  Join Δ Ξ Γ := List.Partitions Γ Δ Ξ
  joinSymm := List.Partitions.symm
  joinAssoc := List.Partitions.assoc

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

def Elementwise.Wk.scons {A} [Wkns A]
  {Γ Δ: Elementwise A}: Wk Γ Δ -> (a: A) -> Wk (a::Γ) (a::Δ)
  | w, a => cons (wkId a) w

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

inductive Elementwise.Join.{u, v} {A: Type u} [J: JoinStruct.{u, v} A]
  : Elementwise A -> Elementwise A -> Elementwise A -> Sort (max (u+1) v)
  | nil: Join [] [] []
  | cons {a b c: A} {Γ Δ Ξ: List A}: J.Join a b c -> Join Γ Δ Ξ ->
    Join (a :: Γ) (b :: Δ) (c :: Ξ)

def Elementwise.Join.symm {A} [Joins A] {Γ Δ Ξ: Elementwise A}:
  Join Γ Δ Ξ -> Join Δ Γ Ξ
  | nil => nil
  | cons s sl => cons (joinSymm s) (symm sl)

def Elementwise.Join.assoc
  {A} [Joins A] {Γ123 Γ12 Γ1 Γ2 Γ3: Elementwise A}:
  Join Γ12 Γ3 Γ123 -> Join Γ1 Γ2 Γ12 ->
      (Γ23: List A)
      ×' (_: Join Γ1 Γ23 Γ123)
      ×' (Join Γ2 Γ3 Γ23)
  | nil, nil => ⟨[], nil, nil⟩
  | cons s sl, cons s' sl' =>
    let ⟨a23, s, s'⟩ := joinAssoc s s'
    let ⟨Γ23, sl, sl'⟩ := assoc sl sl'
    ⟨a23::Γ23, cons s sl, cons s' sl'⟩

instance Elementwise.instJoins {A: Type u} [Joins.{u, v} A]
  : Joins.{u, max (u+1) v} (Elementwise A) where
  Join := Join.{u, v}
  joinSymm := Join.symm
  joinAssoc := Join.assoc

def OptElementwise (A: Type u) := List A

inductive OptElementwise.Split.{u, v} {A: Type u} [S: Splits.{u, v} A]
  : OptElementwise A -> OptElementwise A -> OptElementwise A -> Sort (max (u+1) v)
  | nil: Split [] [] []
  | left (a): Split Γ Δ Ξ -> Split (a::Γ) (a::Δ) Ξ
  | right (a): Split Γ Δ Ξ -> Split (a::Γ) Δ (a::Ξ)
  | both {a b c: A} {Γ Δ Ξ: List A}: S.Split a b c -> Split Γ Δ Ξ ->
    Split (a :: Γ) (b :: Δ) (c :: Ξ)

def OptElementwise.Split.symm {A} [Splits A] {Γ Δ Ξ: OptElementwise A}:
  Split Γ Δ Ξ -> Split Γ Ξ Δ
  | nil => nil
  | left a s => right a (symm s)
  | right a s => left a (symm s)
  | both s ss => both (splitSymm s) (symm ss)

def OptElementwise.Split.assoc {A} [Splits A] {Γ123 Γ12 Γ1 Γ2 Γ3: OptElementwise A}:
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

instance OptElementwise.instSplits {A: Type u} [Splits.{u, v} A]
  : Splits.{u, max (u+1) v} (OptElementwise A) where
  Split := Split.{u, v}
  splitSymm := Split.symm
  splitAssoc := Split.assoc

--TODO: separate out SplitStruct?
def Elementwise.Split.toOptElementwise {A: Type u} [Splits.{u, v} A]
  {Γ Δ Ξ: Elementwise A}: Split Γ Δ Ξ -> OptElementwise.Split Γ Δ Ξ
  | nil => OptElementwise.Split.nil
  | cons sa s => OptElementwise.Split.both sa (toOptElementwise s)

def List.Partitions.Split.toOptElementwise {A: Type u} [Splits.{u, v} A]
  {Γ Δ Ξ: List A}: List.Partitions Γ Δ Ξ -> OptElementwise.Split Γ Δ Ξ
  | nil => OptElementwise.Split.nil
  | left l p => OptElementwise.Split.left l (toOptElementwise p)
  | right r p => OptElementwise.Split.right r (toOptElementwise p)

inductive OptElementwise.Join.{u, v} {A: Type u} [S: JoinStruct.{u, v} A]
  : OptElementwise A -> OptElementwise A -> OptElementwise A -> Sort (max (u+1) v)
  | nil: Join [] [] []
  | left (a): Join Γ Δ Ξ -> Join (a::Γ) Δ (a::Ξ)
  | right (a): Join Γ Δ Ξ -> Join Γ (a::Δ) (a::Ξ)
  | both {a b c: A} {Γ Δ Ξ: List A}: S.Join a b c -> Join Γ Δ Ξ ->
    Join (a :: Γ) (b :: Δ) (c :: Ξ)

def OptElementwise.Join.symm {A} [Joins A] {Γ Δ Ξ: OptElementwise A}:
  Join Γ Δ Ξ -> Join Δ Γ Ξ
  | nil => nil
  | left a s => right a (symm s)
  | right a s => left a (symm s)
  | both s ss => both (joinSymm s) (symm ss)

def OptElementwise.Join.assoc {A} [Joins A] {Γ123 Γ12 Γ1 Γ2 Γ3: OptElementwise A}:
  Join Γ12 Γ3 Γ123 -> Join Γ1 Γ2 Γ12 ->
      (Γ23: List A)
      ×' (_: Join Γ1 Γ23 Γ123)
      ×' (Join Γ2 Γ3 Γ23)
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
    let ⟨_, sa, sa'⟩ := joinAssoc sa sa';
    ⟨_::Γ23, both sa s, both sa' s'⟩

instance OptElementwise.instJoinStruct {A: Type u} [JoinStruct.{u, v} A]
  : JoinStruct.{u, max (u+1) v} (OptElementwise A) where
  Join := Join.{u, v}

instance OptElementwise.instJoins {A: Type u} [Joins.{u, v} A]
  : Joins.{u, max (u+1) v} (OptElementwise A) where
  joinSymm := Join.symm
  joinAssoc := Join.assoc

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
  [Splits.{u, v} A] [Wkns.{u, w} A] [SplitWk.{u, v, w} A]
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
    let ⟨_, sa, w⟩ := wkSplitRight w sa
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

def SplitOrWk.Split.wk {A}
  [Splits.{u, v} A] [Wkns.{u, w} A] [SplitWk.{u, v, w} A]
  {Γ' Γ Δ Ξ: SplitOrWk A}: Wk Γ' Γ -> Split Γ Δ Ξ -> Split Γ' Δ Ξ
  | Wk.nil, nil => nil
  | Wk.cons w W, left w' s => left (wkTrans w w') (wk W s)
  | Wk.cons w W, right w' s => right (wkTrans w w') (wk W s)
  | Wk.cons w W, both sa s => both (wkSplit w sa) (wk W s)

def SplitOrWk.Split.wkLeft {A}
  [Splits.{u, v} A] [Wkns.{u, w} A] [SplitWk.{u, v, w} A]
  {Γ Δ Δ' Ξ: SplitOrWk A}: Split Γ Δ Ξ -> Wk Δ Δ' -> Split Γ Δ' Ξ
  | nil, Wk.nil => nil
  | left wa s, Wk.cons wa' w => left (wkTrans wa wa') (wkLeft s w)
  | right wa s, w => right wa (wkLeft s w)
  | both sa s, Wk.cons wa w
    => both (splitWkLeft sa wa) (wkLeft s w)

def SplitOrWk.Split.wkRight {A}
  [Splits.{u, v} A] [Wkns.{u, w} A] [SplitWk.{u, v, w} A]
  {Γ Δ Ξ Ξ': SplitOrWk A}: Split Γ Δ Ξ -> Wk Ξ Ξ' -> Split Γ Δ Ξ'
  | nil, Wk.nil => nil
  | left wa s, w => left wa (wkRight s w)
  | right wa s, Wk.cons wa' w => right (wkTrans wa wa') (wkRight s w)
  | both sa s, Wk.cons wa w
    => both (splitWkRight sa wa) (wkRight s w)

instance SplitOrWk.instWkns {A: Type u} [Wkns.{u, w} A]
  : Wkns.{u, max (u + 1) w} (SplitOrWk A) where
  Wk := Wk
  wkId := Wk.id
  wkTrans := Wk.trans

instance SplitOrWk.instSplits {A: Type u}
  [Splits.{u, v} A] [Wkns.{u, w} A] [SplitWk.{u, v, w} A]
  : Splits.{u, max (u + 1) v w} (SplitOrWk A) where
  Split := Split
  splitSymm := Split.symm
  splitAssoc := Split.assoc

instance SplitOrWk.instSplitWk {A: Type u}
  [Splits.{u, v} A] [Wkns.{u, w} A] [SplitWk.{u, v, w} A]
  : SplitWk.{u, max (u + 1) v w, _} (SplitOrWk A) where
  wkSplit := Split.wk
  splitWkLeft := Split.wkLeft
  splitWkRight := Split.wkRight

def DropOrWk (A: Type u) := List A

--TODO: define Drop Γ to be Wk Γ []?
-- but this also requires another type bound on A
inductive DropOrWk.Drop.{u, w, d} {A: Type u}
  [D: Drops.{u, d} A]
  : DropOrWk A -> Type (max u w d)
  | nil: Drop []
  | discard {a}: D.Drop a -> Drop Γ -> Drop (a::Γ)

instance DropOrWk.instDrop {A: Type u} [Drops A]: Drops (DropOrWk A)
  where
  Drop := Drop

--TODO: define as split to Δ []?
-- issue is requires another type bound on A...
inductive DropOrWk.Wk.{u, w, d} {A: Type u}
  [W: Wkns.{u, w} A] [D: Drops.{u, d} A]
  : DropOrWk A -> DropOrWk A -> Type (max u w d)
  | nil: Wk [] []
  | cons {a b}: W.Wk a b -> Wk Γ Δ -> Wk (a :: Γ) (b :: Δ)
  | discard {a}: D.Drop a -> Wk Γ Δ -> Wk (a :: Γ) Δ

def DropOrWk.Wk.scons {A} [Wkns A] [Drops A]
  {Γ Δ: DropOrWk A}: Wk Γ Δ -> (a: A) -> Wk (a::Γ) (a::Δ)
  | w, a => cons (wkId a) w

def DropOrWk.Wk.id {A} [Wkns.{u, w} A] [Drops.{u, d} A]
  : (Γ: DropOrWk A) -> DropOrWk.Wk Γ Γ
  | [] => nil
  | l::Γ => cons (wkId l) (id Γ)

def DropOrWk.Wk.trans.{u, w, d} {A} [Wkns A] [WkDrop.{u, w, d} A]
  {Γ Δ Ξ: DropOrWk A}: Wk.{u, w, d} Γ Δ -> Wk.{u, w, d} Δ Ξ -> Wk Γ Ξ
  | H, nil => H
  | cons w H, cons w' H' => cons (wkTrans w w') (trans H H')
  | cons w H, discard d H' => discard (wkDrop w d) (trans H H')
  | discard d H, H' => discard d (trans H H')

instance DropOrWk.instWk {A: Type u}
  [Wkns.{u, w} A] [WkDrop.{u, w, d} A]: Wkns (DropOrWk A)
  where
  Wk := Wk
  wkId := Wk.id
  wkTrans := Wk.trans

def DropOrWk.Wk.drop {A} [Wkns A] [WkDrop A]
  {Γ Δ: DropOrWk A}: Wk Γ Δ -> Drop Δ -> Drop Γ
  | nil, _ => Drop.nil
  | cons wa w, Drop.discard d D => Drop.discard (wkDrop wa d) (drop w D)
  | discard da w, D => Drop.discard da (drop w D)

instance DropOrWk.instDropWk {A: Type u}
  [Wkns.{u, w} A] [WkDrop.{u, w, d} A]: WkDrop (DropOrWk A)
  where
  wkDrop := Wk.drop

inductive DropOrWk.Split.{u, v, w, d} {A: Type u}
  [S: Splits.{u, v} A] [W: Wkns.{u, w} A] [D: Drops.{u, d} A]
  : DropOrWk A -> DropOrWk A -> DropOrWk A -> Sort (max (u + 1) v w d)
  | nil: Split [] [] []
  | left {a b}: W.Wk a b -> Split Γ Δ Ξ -> Split (a::Γ) (b::Δ) Ξ
  | right {a b}: W.Wk a b -> Split Γ Δ Ξ -> Split (a::Γ) Δ (b::Ξ)
  | both {a b c: A} {Γ Δ Ξ: List A}: S.Split a b c -> Split Γ Δ Ξ ->
    Split (a :: Γ) (b :: Δ) (c :: Ξ)
  | discard {a: A}: D.Drop a -> Split Γ Δ Ξ -> Split (a::Γ) Δ Ξ

def DropOrWk.Split.sleft.{u, v, w, d} {A: Type u}
  [Splits.{u, v} A] [Wkns.{u, w} A] [Drops.{u, d} A]
  {Γ Δ Ξ} (a: A): Split Γ Δ Ξ -> Split (a::Γ) (a::Δ) Ξ
  := Split.left (wkId a)

def DropOrWk.Split.sright.{u, v, w} {A: Type u}
  [Splits.{u, v} A] [Wkns.{u, w} A] [Drops.{u, d} A]
  {Γ Δ Ξ} (a: A): Split Γ Δ Ξ -> Split (a::Γ) Δ (a::Ξ)
  := Split.right (wkId a)

def DropOrWk.Split.symm {A}
  [Splits A] [Wkns A] [Drops A] {Γ Δ Ξ: DropOrWk A}:
  Split Γ Δ Ξ -> Split Γ Ξ Δ
  | nil => nil
  | left a s => right a (symm s)
  | right a s => left a (symm s)
  | both s ss => both (splitSymm s) (symm ss)
  | discard d s => discard d (symm s)

def DropOrWk.Split.assoc {A}
  [Splits.{u, v} A] [Wkns.{u, w} A]
  [SplitWk.{u, v, w} A] [D: SplitDropWk A]
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
    let ⟨_, sa, w⟩ := wkSplitRight w sa
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

instance DropOrWk.instSplits {A: Type u}
  [Splits.{u, v} A] [Wkns.{u, w} A]
  [SplitWk.{u, v, w} A] [SplitDropWk A]
  : Splits (DropOrWk A) where
  Split := Split
  splitSymm := Split.symm
  splitAssoc := Split.assoc

def DropOrWk.Split.wk {A}
  [Splits.{u, v} A] [Wkns.{u, w} A]
  [SplitWk.{u, v, w} A] [SplitDropWk A]
  {Γ' Γ Δ Ξ: DropOrWk A}: Wk Γ' Γ -> Split Γ Δ Ξ -> Split Γ' Δ Ξ
  | Wk.nil, nil => nil
  | Wk.cons wa w, left wa' s => left (wkTrans wa wa') (wk w s)
  | Wk.cons wa w, right wa' s => right (wkTrans wa wa') (wk w s)
  | Wk.cons wa w, both sa s => both (wkSplit wa sa) (wk w s)
  | Wk.cons wa w, discard da s => discard (wkDrop wa da) (wk w s)
  | Wk.discard da w, s => discard da (wk w s)

def DropOrWk.Split.wkLeft {A}
  [Splits.{u, v} A] [Wkns.{u, w} A]
  [SplitWk.{u, v, w} A] [SplitDropWk A]
  {Γ Δ Δ' Ξ: DropOrWk A}: Split Γ Δ Ξ -> Wk Δ Δ' -> Split Γ Δ' Ξ
  | nil, Wk.nil => nil
  | left wa s, Wk.cons wa' w => left (wkTrans wa wa') (wkLeft s w)
  | left wa s, Wk.discard da w => discard (wkDrop wa da) (wkLeft s w)
  | right wa s, w => right wa (wkLeft s w)
  | both sa s, Wk.cons wa w
    => both (splitWkLeft sa wa) (wkLeft s w)
  | both sa s, Wk.discard da w
    => right (splitDropLeft sa da) (wkLeft s w)
  | discard da s, w => discard da (wkLeft s w)

def DropOrWk.Split.wkRight {A}
  [Splits.{u, v} A] [Wkns.{u, w} A]
  [SplitWk.{u, v, w} A] [SplitDropWk A]
  {Γ Δ Ξ Ξ': DropOrWk A}: Split Γ Δ Ξ -> Wk Ξ Ξ' -> Split Γ Δ Ξ'
  | nil, Wk.nil => nil
  | left wa s, w => left wa (wkRight s w)
  | right wa s, Wk.cons wa' w => right (wkTrans wa wa') (wkRight s w)
  | right wa s, Wk.discard da w => discard (wkDrop wa da) (wkRight s w)
  | both sa s, Wk.cons wa w
    => both (splitWkRight sa wa) (wkRight s w)
  | both sa s, Wk.discard da w
    => left (splitDropRight sa da) (wkRight s w)
  | discard da s, w => discard da (wkRight s w)

instance DropOrWk.instSplitWk {A}
  [Splits.{u, v} A] [Wkns.{u, w} A]
  [SplitWk.{u, v, w} A] [SplitDropWk A]
  : SplitWk (DropOrWk A)
  where
  wkSplit := Split.wk
  splitWkLeft := Split.wkLeft
  splitWkRight := Split.wkRight

--TODO: instSplitDropWk

--TODO: instSWk

def DropOrWk.SWk {A} [Wkns A]
  : DropOrWk A -> DropOrWk A -> Sort _
  := Elementwise.Wk

@[match_pattern]
def DropOrWk.SWk.nil {A} [Wkns A]: @SWk A _ [] [] := Elementwise.Wk.nil

@[match_pattern]
def DropOrWk.SWk.cons {A} [W: Wkns A] {Γ Δ: DropOrWk A} {a b: A}
  : W.Wk a b -> SWk Γ Δ -> SWk (a::Γ) (b::Δ)
  := Elementwise.Wk.cons

def DropOrWk.SWk.toWk {A} [Wkns A] [Drops A] {Γ Δ: DropOrWk A}
  : SWk Γ Δ -> Wk Γ Δ
  | nil => Wk.nil
  | cons w W => Wk.cons w (toWk W)

def DropOrWk.SWk.id {A} [Wkns A] (Γ: DropOrWk A)
  : SWk Γ Γ := Elementwise.Wk.id Γ

def DropOrWk.SWk.trans {A} [Wkns A]
  {Γ Δ Ξ: DropOrWk A}: SWk Γ Δ -> SWk Δ Ξ -> SWk Γ Ξ
  := Elementwise.Wk.trans

instance DropOrWk.instSWk {A} [Wkns A] [WkDrop A]: SWkns (DropOrWk A) where
  SWk := SWk
  swkToWk := SWk.toWk
  swkId := SWk.id
  swkTrans := SWk.trans

def DropOrWk.SSplit.{u, v} {A: Type u}
  [Splits.{u, v} A]
  : DropOrWk A -> DropOrWk A -> DropOrWk A -> Sort (max (u+1) v)
  := Elementwise.Split

@[match_pattern]
def DropOrWk.SSplit.nil {A: Type u}
  [Splits.{u, v} A]
  : @DropOrWk.SSplit A _ [] [] []
  := Elementwise.Split.nil

@[match_pattern]
def DropOrWk.SSplit.cons {A: Type u}
  [Splits.{u, v} A]
  {a b c: A} {Γ Δ Ξ: DropOrWk A}
  : Splits.Split a b c
    -> SSplit Γ Δ Ξ
    -> SSplit (a::Γ) (b::Δ) (c::Ξ)
  := Elementwise.Split.cons

def DropOrWk.SSplit.symm {A: Type u}
  [Splits.{u, v} A]
  {Γ Δ Ξ: DropOrWk A}: SSplit Γ Δ Ξ -> SSplit Γ Ξ Δ
  := Elementwise.Split.symm

def DropOrWk.SSplit.assoc {A: Type u}
  [Splits.{u, v} A]
  {Γ123 Γ12 Γ1 Γ2 Γ3: DropOrWk A}
  : SSplit Γ123 Γ12 Γ3 -> SSplit Γ12 Γ1 Γ2 ->
      (Γ23: DropOrWk A)
      ×' (_: SSplit Γ123 Γ1 Γ23)
      ×' (SSplit Γ23 Γ2 Γ3)
  := Elementwise.Split.assoc

def DropOrWk.SSplit.toSplit {A: Type u}
  [Splits.{u, v} A] [Wkns.{u, w} A]
  [SplitWk.{u, v, w} A] [SplitDropWk A]
  {Γ Δ Ξ: DropOrWk A}
  : SSplit Γ Δ Ξ -> Split Γ Δ Ξ
  | SSplit.nil => Split.nil
  | SSplit.cons s sl => Split.both s (toSplit sl)

def Elementwise.Split.toDropOrWk {A: Type u}
  [Splits.{u, v} A] [Wkns.{u, w} A]
  [SplitWk.{u, v, w} A] [SplitDropWk A]
  {Γ Δ Ξ: Elementwise A}
  : Split Γ Δ Ξ -> DropOrWk.Split Γ Δ Ξ
  := DropOrWk.SSplit.toSplit

instance DropOrWk.instSSplits {A: Type u}
  [Splits.{u, v} A] [Wkns.{u, w} A]
  [SplitWk.{u, v, w} A] [SplitDropWk A]
  : SSplits (DropOrWk A) where
  SSplit := SSplit
  ssplitToSplit := SSplit.toSplit
  ssplitSymm := SSplit.symm
  ssplitAssoc := SSplit.assoc

def DropOrWk.SSplit.dist {A: Type u}
  [Splits.{u, v} A] [Wkns.{u, w} A]
  [SplitWk.{u, v, w} A] [SplitDropWk A]
  [DropToSplit A]
  {Γ' Γ Δ Ξ: DropOrWk A}
  : Wk Γ' Γ -> SSplit Γ Δ Ξ ->
      (Δ' Ξ': DropOrWk A)
      ×' (_: SSplit Γ' Δ' Ξ')
      ×' (_: Wk Δ' Δ)
      ×' Wk Ξ' Ξ
  | Wk.nil, SSplit.nil => ⟨_, _, SSplit.nil, Wk.nil, Wk.nil⟩
  | Wk.cons wa w, SSplit.cons sa s =>
      let ⟨_, _, s, wl, wr⟩ := dist w s
      ⟨_, _, s.cons (wkSplit wa sa), wl.scons _, wr.scons _⟩
  | Wk.discard wa w, s =>
      let ⟨_, _, s, wl, wr⟩ := dist w s
      let ⟨_, _, sa, dl, dr⟩ := dropToSplit wa
      ⟨_, _, s.cons sa, wl.discard dl, wr.discard dr⟩

instance DropOrWk.instDistWkSSplit {A: Type u}
  [Splits.{u, v} A] [Wkns.{u, w} A]
  [SplitWk.{u, v, w} A] [SplitDropWk A]
  [DropToSplit A]
  : DistWkSSplit (DropOrWk A) where
  distWkSSplit := DropOrWk.SSplit.dist

--TODO: instDistWkSSplit

--TODO: instSSplitDropSWk

--TODO: should SSplitDropWk be a typeclass?

def DropOrWk.instElementwiseSSplits {A: Type u}
  [Splits.{u, v} A] [Wkns.{u, w} A]
  [SplitWk.{u, v, w} A] [SplitDropWk A]
  : SSplits (DropOrWk A) where
  SSplit := Elementwise.Split
  ssplitToSplit := Elementwise.Split.toDropOrWk
  ssplitSymm := Elementwise.Split.symm
  ssplitAssoc := Elementwise.Split.assoc

--TODO: export that the above is equal to instSSplits?

--TODO: instSWk

--TODO: instDistWkSSplit

--TODO: instSSplitDropSWk

def SplitOrWk.Split.toDropOrWk {A: Type u}
  [Splits.{u, v} A] [Wkns.{u, w} A]
  [SplitWk.{u, v, w} A] [SplitDropWk A]
  {Γ Δ Ξ: SplitOrWk A}
  : Split Γ Δ Ξ -> DropOrWk.Split Γ Δ Ξ
  | nil => DropOrWk.Split.nil
  | left w s => DropOrWk.Split.left w (toDropOrWk s)
  | right w s => DropOrWk.Split.right w (toDropOrWk s)
  | both s ss => DropOrWk.Split.both s (toDropOrWk ss)

def DropOrWk.instSplitOrWkSSplits {A: Type u}
  [Splits.{u, v} A] [Wkns.{u, w} A]
  [SplitWk.{u, v, w} A] [SplitDropWk A]
  : SSplits (DropOrWk A) where
  SSplit := SplitOrWk.Split
  ssplitToSplit := SplitOrWk.Split.toDropOrWk
  ssplitSymm := SplitOrWk.Split.symm
  ssplitAssoc := SplitOrWk.Split.assoc

--TODO: instSWk

--TODO: instDistWkSSplit

--TODO: instSSplitDropSWk
