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
  | var {Γ X}: L.var Γ x -> Term Γ X
  | op {Γ A B}: L.inst A B -> Term Γ A -> Term Γ B
  | cnst {Γ A}: L.cnst Γ A -> Term Γ A
  | pair {Γ Δ Ξ A B C}: S.Splits Γ Δ Ξ ->
    Term Δ A -> Term Ξ B -> J.Joins A B C ->
    Term Γ C
  | bind {Γ Δ Ξ A AΔ B}: S.Splits Γ Δ Ξ ->
    Term Ξ A ->
    L.bind A Δ AΔ -> Term AΔ B ->
    Term Γ B
