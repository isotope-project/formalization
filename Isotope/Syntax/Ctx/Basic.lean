class Splittable.{u, v} (A: Type u): Type (max u v) where
  Splits: A -> A -> A -> Sort v
  splitsSymm {a b c: A}: Splits a b c -> Splits a c b
  splitsAssoc {a123 a12 a1 a2 a3: A}:
    Splits a123 a12 a3 -> Splits a12 a1 a2 ->
      (a23: A) ×' (_: Splits a123 a1 a23) ×' (Splits a23 a2 a3)

class Weakenable.{u, v} (A: Type u) where
  Weakens: A -> A -> Sort v
  weakensTrans: {a b c: A} -> Weakens a b -> Weakens b c -> Weakens a c

class Discardable.{u, v} (A: Type u) where
  Drops: A -> Sort v

open Splittable
open Weakenable
open Discardable

inductive Splittable.ElementwiseSplit.{u, v} {A: Type u} [Splittable.{u, v} A]
  : List A -> List A -> List A -> Sort (max (u+1) v)
  | nil: ElementwiseSplit [] [] []
  | cons {a b c: A} {Γ Δ Ξ: List A}: Splits a b c -> ElementwiseSplit Γ Δ Ξ ->
    ElementwiseSplit (a :: Γ) (b :: Δ) (c :: Ξ)

def Splittable.ElementwiseSplit.symm {A} [Splittable A] {Γ Δ Ξ: List A}:
  ElementwiseSplit Γ Δ Ξ -> ElementwiseSplit Γ Ξ Δ
  | nil => nil
  | cons s sl => cons (splitsSymm s) (symm sl)

def Splittable.ElementwiseSplit.assoc
  {A} [Splittable A] {Γ123 Γ12 Γ1 Γ2 Γ3: List A}:
  ElementwiseSplit Γ123 Γ12 Γ3 -> ElementwiseSplit Γ12 Γ1 Γ2 ->
      (Γ23: List A)
      ×' (_: ElementwiseSplit Γ123 Γ1 Γ23)
      ×' (ElementwiseSplit Γ23 Γ2 Γ3)
  | nil, nil => ⟨[], nil, nil⟩
  | cons s sl, cons s' sl' =>
    let ⟨a23, s, s'⟩ := splitsAssoc s s'
    let ⟨Γ23, sl, sl'⟩ := assoc sl sl'
    ⟨a23::Γ23, cons s sl, cons s' sl'⟩

def Splitabble.Elementwise.{u, v} {A: Type u} [Splittable.{u, v} A]
  : Splittable.{u, max (u+1) v} (List A) where
  Splits := Splittable.ElementwiseSplit.{u, v}
  splitsSymm := Splittable.ElementwiseSplit.symm
  splitsAssoc := Splittable.ElementwiseSplit.assoc

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

-- def List.Partitions.assoc {A}: {Γ123 Γ12 Γ1 Γ2 Γ3: List A} ->
--   List.Partitions Γ123 Γ12 Γ3 -> List.Partitions Γ12 Γ1 Γ2 ->
--       (Γ23: List A)
--       ×' (_: List.Partitions Γ123 Γ1 Γ23)
--       ×' (List.Partitions Γ23 Γ2 Γ3)
--   | _, _, _, _, _, nil, nil => ⟨[], nil, nil⟩
--   | _, _, _, _, _, left l p, _ => sorry
--   | _, _, _, _, _, right r p, _ => sorry
