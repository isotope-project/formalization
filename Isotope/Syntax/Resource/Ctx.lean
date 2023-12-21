import Isotope.Syntax.Ty
import Isotope.ResourceAlgebra.Basic
import Isotope.Syntax.Abstract.Basic
import Isotope.Syntax.Abstract.List

open Abstract

namespace ResourceNamed

structure Res (T: Type v) [ResourceAlgebraFamily T] where
  ty: Ty T
  res: ty.res
  qnt: Transparency

instance Res.instDrops {T} [ResourceAlgebraFamily T]: Drops (Res T) where
  Drop v := ResourceAlgebra.QWk v.qnt v.res 0

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

instance Res.instSplits [ResourceAlgebraFamily T]
  : Splits (Res T) where
  Split := Split
  splitSymm := Split.symm
  splitAssoc := Split.assoc

--TODO: Res.instSplitWk

--TODO: Res.instSplitDropWk


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

structure Var.Split {N: Type u} {T: Type v} [ResourceAlgebraFamily T]
  (v l r: Var N T): Prop where
  res: v.toRes.Split l.toRes r.toRes
  left_name: l.name = v.name
  right_name: r.name = v.name

def Var.Split.symm {N: Type u} {T: Type v} [ResourceAlgebraFamily T]
  {v l r: Var N T}: Split v l r -> Split v r l
  | ⟨s, Hl, Hr⟩ => ⟨s.symm, Hr, Hl⟩

def Var.Split.assoc {N: Type u} {T: Type v} [ResourceAlgebraFamily T]
  {v123 v12 v1 v2 v3: Var N T}
  (s12_3: Split v123 v12 v3) (s1_2: Split v12 v1 v2)
  : (v23: Var N T) ×' (_: Split v123 v1 v23) ×' Split v23 v2 v3
  :=
    let ⟨r23, sr1_23, sr2_3⟩ := s12_3.res.assoc s1_2.res
    ⟨⟨r23, v123.name⟩,
      ⟨sr1_23,
        by rw [s1_2.left_name, s12_3.left_name],
        rfl⟩,
      ⟨sr2_3,
        by rw [s1_2.right_name, s12_3.left_name],
        s12_3.right_name⟩⟩

instance Var.instSplits {N} {T} [ResourceAlgebraFamily T]
  : Splits (Var N T) where
  Split := Var.Split
  splitSymm := Split.symm
  splitAssoc := Split.assoc

instance Var.instDrops {N} {T} [ResourceAlgebraFamily T]
  : Drops (Var N T) where
  Drop v := Drops.Drop v.toRes

instance Var.instWk {N} {T} [ResourceAlgebraFamily T]
  : Wkns (Var N T) := PRes.instWkns

--TODO:
-- instance Var.instSplitWk {N} {T} [ResourceAlgebraFamily T]
--   : SplitWk (Var N T) where
--   wkSplit | ⟨Heq, Hr, Hq⟩, ⟨Hs, Hel, Her⟩ => sorry
--   splitWkLeft := sorry
--   splitWkRight := sorry

--TODO: var.instSplitDropWk

structure Comp (T: Type v) [ResourceAlgebraFamily T]
  extends Res T where
  central: Bool

instance Comp.instPartialOrder {T: Type v} [ResourceAlgebraFamily T]
  : PartialOrder (Comp T) where
  le l r := l.central ≤ r.central
    ∧ l.toRes ≤ r.toRes
  le_refl _ := ⟨le_refl _, le_refl _⟩
  le_trans _ _ _ H H'
    := ⟨le_trans H.1 H'.1, le_trans H.2 H'.2⟩
  le_antisymm x x' H H' :=
    have Hc := le_antisymm H.1 H'.1;
    have Ht := le_antisymm H.2 H'.2;
    by cases x; cases x'; simp only [] at *; rw [Ht, Hc]

def Ctx (N: Type u) (T: Type v) [ResourceAlgebraFamily T] := List (Var N T)

def Ctx.SSplit {N: Type u} {T: Type v} [ResourceAlgebraFamily T]
  : Ctx N T → Ctx N T → Ctx N T → Type _
  := @Elementwise.Split (Var N T) _

def Ctx.SSplit.symm {N: Type u} {T: Type v} [ResourceAlgebraFamily T]
  {Γ Δ Ξ: Ctx N T}: SSplit Γ Δ Ξ -> SSplit Γ Ξ Δ
  := Elementwise.Split.symm

def Ctx.SSplit.assoc {N: Type u} {T: Type v} [ResourceAlgebraFamily T]
  {Γ123 Γ12 Γ1 Γ2 Γ3: Ctx N T}
  : SSplit Γ123 Γ12 Γ3 -> SSplit Γ12 Γ1 Γ2 ->
    (Γ23: Ctx N T) ×' (_: SSplit Γ123 Γ1 Γ23) ×' SSplit Γ23 Γ2 Γ3
  := Elementwise.Split.assoc

-- def Ctx.Split {N: Type u} {T: Type v} [ResourceAlgebraFamily T]
--   : Ctx N T → Ctx N T → Ctx N T → Type _
--   := @DropOrWk.Split (Var N T) _

-- def Ctx.Split.symm {N: Type u} {T: Type v} [ResourceAlgebraFamily T]
--   {Γ Δ Ξ: Ctx N T}: Split Γ Δ Ξ -> Split Γ Ξ Δ
--   := Elementwise.Split.symm

-- def Ctx.Split.assoc {N: Type u} {T: Type v} [ResourceAlgebraFamily T]
--   {Γ123 Γ12 Γ1 Γ2 Γ3: Ctx N T}
--   : Split Γ123 Γ12 Γ3 -> Split Γ12 Γ1 Γ2 ->
--     (Γ23: Ctx N T) ×' (_: Split Γ123 Γ1 Γ23) ×' Split Γ23 Γ2 Γ3
--   := Elementwise.Split.assoc
