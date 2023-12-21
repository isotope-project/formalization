import Isotope.Syntax.Ty
import Isotope.ResourceAlgebra.Basic
import Isotope.Syntax.Abstract.Basic

open Abstract

namespace ResourceNamed

structure Res (T: Type v) [ResourceAlgebraFamily T] where
  ty: Ty T
  res: ty.res
  qnt: Transparency

--TODO: define Res.le inductively, and prove equal?
-- Why does kernel leave metavariables here?

instance Res.instPartialOrder {T: Type v}
  [R: ResourceAlgebraFamily T]
  : PartialOrder (Res T) where
  le l r := l.qnt ≤ r.qnt
    ∧ ∃p: l.ty = r.ty, r.ty.resourceAlgebra.le (p ▸ l.res) r.res
  le_refl l := ⟨le_refl _, rfl, l.ty.resourceAlgebra.le_refl _⟩
  le_trans
    | ⟨tx, rx, qx⟩, ⟨_, ry, qy⟩, ⟨_, rz, qz⟩, ⟨Hq, rfl, Hxy⟩, ⟨Hq', rfl, Hyz⟩
    => ⟨le_trans Hq Hq', rfl, tx.resourceAlgebra.le_trans _ _ _ Hxy Hyz⟩
  le_antisymm
    | ⟨tx, rx, qx⟩, ⟨ty, ry, qy⟩
    => by
      intro ⟨Hq, H, Hxy⟩ ⟨Hq', H', Hyx⟩; cases H
      have H'' := le_antisymm Hxy Hyx
      have Hq'' := le_antisymm Hq Hq'
      simp only at *;
      simp [H'', Hq'']

inductive Res.Split {T: Type v} [ResourceAlgebraFamily T]
  : Res T → Res T → Res T → Prop where
  | mk (A: Ty T) {v l r: A.res} {q}
    (H: ResourceAlgebra.QSplit q v l r)
    (Hl: q ≥ ql) (Hr: q ≥ qr)
    : Split ⟨A, v, q⟩ ⟨A, l, ql⟩ ⟨A, r, qr⟩

def Res.Split.ty_eq_left {T: Type v} [ResourceAlgebraFamily T]
  {v l r: Res T}: Split v l r -> l.ty = v.ty
  | mk _ _ _ _ => rfl

def Res.Split.ty_eq_right {T: Type v} [ResourceAlgebraFamily T]
  {v l r: Res T}: Split v l r -> r.ty = v.ty
  | mk _ _ _ _ => rfl

def Res.Split.ty_eq_sides {T: Type v} [ResourceAlgebraFamily T]
  {v l r: Res T}: Split v l r -> l.ty = r.ty
  | mk _ _ _ _ => rfl

def Res.Split.split {T: Type v} [ResourceAlgebraFamily T]
  {v l r: Res T}: (s: Split v l r)
    -> ResourceAlgebra.QSplit v.qnt v.res
      (s.ty_eq_left ▸ l.res)
      (s.ty_eq_right ▸ r.res)
  | mk _ H _ _ => H

def Res.Split.symm {T: Type v} [ResourceAlgebraFamily T]
  {v l r: Res T}: Split v l r -> Split v r l
  | mk A H Hl Hr => mk A H.symm Hr Hl

def Res.Split.assoc' {T: Type v} [ResourceAlgebraFamily T]
  {v123 v12 v1 v2 v3: Res T}
  (s12_3: Split v123 v12 v3) (s1_2: Split v12 v1 v2)
  : (v23: Res T) ×' Split v123 v1 v23 ∧ Split v23 v2 v3
  :=
    let r2 := s12_3.ty_eq_left ▸ (s1_2.ty_eq_right ▸ v2.res)
    let r3 := s12_3.ty_eq_right ▸ v3.res
    ⟨⟨v123.ty, r2 + r3, v123.qnt⟩,
      by cases s12_3 with
      | mk _ s12_3 H12 H3 =>
        cases s1_2 with
        | mk _ s1_2 H1 H2 =>
          let ⟨s1_23, s2_3⟩  := s12_3.assoc (s1_2.upcast H12)
          exact ⟨
            mk _ s1_23 (le_trans H1 H12) (le_refl _),
            mk _ s2_3 (le_trans H2 H12) H3
          ⟩
    ⟩

def Res.Split.assoc {T: Type v} [ResourceAlgebraFamily T]
  {v123 v12 v1 v2 v3: Res T}
  (s12_3: Split v123 v12 v3) (s1_2: Split v12 v1 v2)
  : (v23: Res T) ×' (_: Split v123 v1 v23) ×' Split v23 v2 v3
  := let A := s12_3.assoc' s1_2
    ⟨A.1, A.2.1, A.2.2⟩

instance Res.instSplit [ResourceAlgebraFamily T]
  : Splits (Res T) where
  Split := Split
  splitSymm := Split.symm
  splitAssoc := Split.assoc

structure Var (N: Type u) (T: Type v) [ResourceAlgebraFamily T]
  extends Res T where
  name: N

instance Var.instPartialOrder {N: Type u} {T: Type v} [ResourceAlgebraFamily T]
  : PartialOrder (Var N T) where
  le l r := l.name = r.name
    ∧ l.toRes ≤ r.toRes
  le_refl _ := ⟨rfl, le_refl _⟩
  le_trans _ _ _ H H'
    := ⟨Eq.trans H.1 H'.1, le_trans H.2 H'.2⟩
  le_antisymm x x' H H' :=
    have Ht := le_antisymm H.2 H'.2;
    by cases x; cases x'; simp only [] at *; rw [Ht, H.1]
