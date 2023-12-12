import Mathlib.CategoryTheory.Category.Basic
import Isotope.Syntax.Abstract.Basic

open CategoryTheory

namespace Abstract

class Lang.{u, v, ss, sj, sv, sb, si, sc} (C: Type u)
  extends Splittable.{u, ss} C
  where
  Ty: Type v
  pair: Joinable.{v, sj} Ty
  inst: Quiver.{si} Ty
  var: C -> Ty -> Sort sv
  bind: Ty -> C -> C -> Sort sb
  cnst: C -> Ty -> Sort sc

inductive Term.{u, v, ss, sj, sv, sb, si, sc} {C: Type u}
  [L: Lang.{u, v, ss, sj, sv, sb, si, sc} C]
  : C -> L.Ty -> Type (max u v ss sj sv sb si sc)
  where
  | var {Γ X}: L.var Γ X -> Term Γ X
  | op {Γ A B}: L.inst.Hom A B -> Term Γ A -> Term Γ B
  | cnst {Γ A}: L.cnst Γ A -> Term Γ A
  | pair {Γ Δ Ξ A B C}: L.Split Γ Δ Ξ ->
    Term Δ A -> Term Ξ B -> L.pair.Joins A B C ->
    Term Γ C
  | bind {Γ Δ Ξ A AΔ B}: L.Split Γ Δ Ξ ->
    L.bind A Δ AΔ ->
    Term Ξ A ->
    Term AΔ B ->
    Term Γ B

class Subst.{u, v, ss, sj, sv, sb, si, sc}
  (C: Type u)
  extends Lang.{u, v, ss, sj, sv, sb, si, sc} C, Quiver C
  where
  subst_var {Θ Γ X}: Hom Θ Γ -> var Γ X -> Term Θ X
  subst_cnst {Θ Γ}: Hom Θ Γ -> cnst Γ A -> cnst Θ A
  subst_bind {Θ Γ A AΓ}: Hom Θ Γ -> bind A Γ AΓ
    -> (AΘ: C) ×' (_: Hom AΘ AΓ) ×' bind A Θ AΘ
  subst_split {Θ Γ Δ Ξ}: Hom Θ Γ -> Split Γ Δ Ξ
    -> (ΘΔ ΘΞ: C) ×' (_: Split Θ ΘΔ ΘΞ) ×' (_: Hom ΘΔ Δ) ×' Hom ΘΞ Ξ

def Term.subst {C} [L: Subst C]
  {Θ Γ: C} {A: L.Ty} (σ: L.Hom Θ Γ): Term Γ A -> Term Θ A
  | var x => L.subst_var σ x
  | op f x => Term.op f (subst σ x)
  | cnst c => Term.cnst (L.subst_cnst σ c)
  | pair s a b J =>
    let ⟨_ΘΔ, _ΘΞ, s, σa, σb⟩ := L.subst_split σ s;
    Term.pair s (subst σa a) (subst σb b) J
  | bind s x a e =>
    let ⟨_ΘΔ, _ΘΞ, s, σe, σa⟩ := L.subst_split σ s;
    let ⟨_ΘxΔ, σxe, x⟩ := L.subst_bind σe x;
    Term.bind s x (subst σa a) (subst σxe e)

class SubstCatStruct.{u, v, ss, sj, sv, sb, si, sc}
  (C: Type u)
  extends Subst.{u, v, ss, sj, sv, sb, si, sc} C, CategoryStruct C

class SubstCat.{u, v, ss, sj, sv, sb, si, sc}
  (C: Type u)
  extends SubstCatStruct.{u, v, ss, sj, sv, sb, si, sc} C, Category C
  where
  subst_id_var {Γ A} (X: var Γ A): subst_var (𝟙 Γ) X = Term.var X
  --TODO: should this hold for every morphism Γ --> Γ?
  subst_id_cnst {Γ A} (c: cnst Γ A): subst_cnst (𝟙 Γ) c = c
  subst_id_bind {Γ A AΓ} (X: bind A Γ AΓ): subst_bind (𝟙 Γ) X = ⟨AΓ, 𝟙 AΓ, X⟩
  subst_id_split {Γ Δ Ξ} (X: Split Γ Δ Ξ):
    subst_split (𝟙 Γ) X = ⟨Δ, Ξ, X, 𝟙 Δ, 𝟙 Ξ⟩
  subst_comp_var {Θ Γ Δ} (σ: Hom Θ Γ) (τ: Hom Γ Δ) (X: var Δ A):
    subst_var (σ ≫ τ) X = (subst_var τ X).subst σ
  subst_comp_cnst {Θ Γ Δ} (σ: Hom Θ Γ) (τ: Hom Γ Δ) (c: cnst Δ A):
    subst_cnst (σ ≫ τ) c = subst_cnst σ (subst_cnst τ c)
  subst_comp_bind {Θ Γ Δ} (σ: Hom Θ Γ) (τ: Hom Γ Δ) (x: bind A Δ AΔ):
    subst_bind (σ ≫ τ) x = (
      let ⟨_Γx, τx, x⟩ := subst_bind τ x;
      let ⟨Θx, σx, x⟩ := subst_bind σ x
      ⟨Θx, σx ≫ τx, x⟩
    )
  subst_comp_split {Θ Γ Δ Δl Δr} (σ: Hom Θ Γ) (τ: Hom Γ Δ) (s: Split Δ Δl Δr):
    subst_split (σ ≫ τ) s = (
      let ⟨_Γl, _Γr, s, τl, τr⟩ := subst_split τ s;
      let ⟨Θl, Θr, s, σl, σr⟩ := subst_split σ s;
      ⟨Θl, Θr, s, σl ≫ τl, σr ≫ τr⟩
    )

def Term.subst_id {C} [L: SubstCat C]
  {Γ: C} {A: L.Ty}: (a: Term Γ A) -> a.subst (𝟙 Γ) = a
  | var X => L.subst_id_var X
  | op f x => congrArg _ (subst_id x)
  | cnst c => congrArg _ (L.subst_id_cnst c)
  | pair s a b J => by
    rw [Term.subst, L.subst_id_split]
    simp only []
    rw [subst_id a, subst_id b]
  | bind s x a e => by
    rw [Term.subst, L.subst_id_split]
    simp only []
    rw [L.subst_id_bind, subst_id a, subst_id e]

def Term.subst_comp {C} [L: SubstCat C]
  {Θ Γ Δ: C} {A: L.Ty} (σ: L.Hom Θ Γ) (τ: L.Hom Γ Δ):
  (a: Term Δ A) -> a.subst (σ ≫ τ) = (a.subst τ).subst σ
  | var X => L.subst_comp_var σ τ X
  | op f x => congrArg _ (subst_comp σ τ x)
  | cnst c => congrArg _ (L.subst_comp_cnst σ τ c)
  | pair s a b j => by
    rw [Term.subst, L.subst_comp_split]
    simp only []
    rw [subst_comp _ _ a, subst_comp _ _ b]
    rfl
  | bind s x a e => by
    rw [Term.subst, L.subst_comp_split]
    simp only []
    rw [L.subst_comp_bind, subst_comp _ _ a, subst_comp _ _ e]
    rfl
