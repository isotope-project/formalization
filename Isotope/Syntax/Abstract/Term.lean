import Isotope.Syntax.Abstract.Resource

namespace Abstract

class Lang.{u, v, sv, sb, si, sc} (C: Type u) (V: Type v) where
  var: C -> V -> Sort sv
  bind: V -> C -> C -> Sort sb
  inst: V -> V -> Sort si
  cnst: C -> V -> Sort sc

inductive Term.{u, v, ss, sj, sv, sb, si, sc} {C: Type u} {V: Type v}
  [S: Splittable.{u, ss} C] [J: Joinable.{v, sj} V]
  [L: Lang.{u, v, sv, sb, si, sc} C V]
  : C -> V -> Type (max u v ss sj sv sb si sc)
  where
  | var {Γ X}: L.var Γ X -> Term Γ X
  | op {Γ A B}: L.inst A B -> Term Γ A -> Term Γ B
  | cnst {Γ A}: L.cnst Γ A -> Term Γ A
  | pair {Γ Δ Ξ A B C}: S.Splits Γ Δ Ξ ->
    Term Δ A -> Term Ξ B -> J.Joins A B C ->
    Term Γ C
  | bind {Γ Δ Ξ A AΔ B}: S.Splits Γ Δ Ξ ->
    L.bind A Δ AΔ ->
    Term Ξ A ->
    Term AΔ B ->
    Term Γ B

class Subst.{u, v, ss, sj, sv, sb, si, sc}
  (C: Type u) (V: Type v)
  [S: Splittable.{u, ss} C] [J: Joinable.{v, sj} V]
  [L: Lang.{u, v, sv, sb, si, sc} C V] (Sbst: C -> C -> Type w)
  where
  var {Θ Γ X}: Sbst Θ Γ -> L.var Γ X -> Term Θ X
  cnst {Θ Γ}: Sbst Θ Γ -> L.cnst Γ A -> L.cnst Θ A
  bind {Θ Γ A AΓ}: Sbst Θ Γ -> L.bind A Γ AΓ
    -> (AΘ: C) ×' (_: Sbst AΘ AΓ) ×' L.bind A Θ AΘ
  split {Θ Γ Δ Ξ}: Sbst Θ Γ -> S.Splits Γ Δ Ξ
    -> (ΘΔ ΘΞ: C) ×' (_: S.Splits Θ ΘΔ ΘΞ) ×' (_: Sbst ΘΔ Δ) ×' Sbst ΘΞ Ξ

def Term.subst {C V S}
  [Splittable C] [Joinable V] [Lang C V] [σs: Subst C V S]
  {Θ Γ: C} {A: V} (σ: S Θ Γ): Term Γ A -> Term Θ A
  | var x => σs.var σ x
  | op f x => Term.op f (subst σ x)
  | cnst c => Term.cnst (σs.cnst σ c)
  | pair s a b J =>
    let ⟨_ΘΔ, _ΘΞ, s, σa, σb⟩ := σs.split σ s;
    Term.pair s (subst σa a) (subst σb b) J
  | bind s x a e =>
    let ⟨_ΘΔ, _ΘΞ, s, σe, σa⟩ := σs.split σ s;
    let ⟨_ΘxΔ, σxe, x⟩ := σs.bind σe x;
    Term.bind s x (subst σa a) (subst σxe e)
