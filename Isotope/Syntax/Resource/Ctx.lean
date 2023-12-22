import Isotope.Syntax.Ty
import Isotope.ResourceAlgebra.Basic
import Isotope.Syntax.Abstract.Basic
import Isotope.Syntax.Abstract.List

open Abstract

namespace ResourceNamed

--TODO: remove Ty T, put in ResourceAlgebra file? Too general for now...
structure Res (T: Type v) [ResourceAlgebraFamily T] where
  ty: Ty T
  res: ty.res
  qnt: Transparency

inductive Res.le {T: Type v} [ResourceAlgebraFamily T]
  : Res T -> Res T -> Prop
  | mk (A: Ty T) {v v': A.res} {q q'}
    (Hv: ResourceAlgebra.QWk q' v' v)
    (Hq: q ≤ q')
    : le ⟨A, v, q⟩ ⟨A, v', q'⟩

theorem Res.le.ty_eq {T: Type v} [ResourceAlgebraFamily T]
  {v v': Res T}: v.le v' -> v.ty = v'.ty
  | mk _ _ _ => rfl

instance Res.instPartialOrder {T: Type v}
  [R: ResourceAlgebraFamily T]
  : PartialOrder (Res T) where
  le := Res.le
  le_refl _
    := le.mk _ ((ResourceAlgebra.transparentAlgebra _ _).le_refl _) (le_refl _)
  le_trans
    | ⟨_, ra, _qa⟩, ⟨_, rb, _qb⟩, ⟨_, rc, _qc⟩, le.mk _ h hq, le.mk _ h' hq'
    => le.mk _
      ((ResourceAlgebra.transparentAlgebra _ _).le_trans ra rb rc
        ((ResourceAlgebra.transparentLeSubalgebra _ hq').le_sub _ _ h) h')
      (le_trans hq hq')
  le_antisymm x y Hxy Hyx := by
    cases x; cases y; cases Hxy with
    | mk _ v q => cases Hyx with
      | mk _ v' q' =>
        have Hq := le_antisymm q q';
        cases Hq;
        have Hr :=
          (ResourceAlgebra.transparentAlgebra _ _).le_antisymm _ _ v v';
        cases Hr;
        rfl

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

instance Res.instDrops {T} [ResourceAlgebraFamily T]: Drops (Res T) where
  Drop v := ResourceAlgebra.QWk v.qnt v.res 0

instance Res.instWkns {T} [ResourceAlgebraFamily T]: Wkns (Res T)
  := PRes.instWkns

instance Res.instSplitWk {T} [ResourceAlgebraFamily T]
  : SplitWk (Res T) where
  wkSplit
    | ⟨_, w, wq⟩, Split.mk _ s ql qr =>
      Split.mk _ ((s.upcast wq).wk w) (le_trans ql wq) (le_trans qr wq)
  splitWkLeft
    | Split.mk _ s ql qr, w => by
      cases w with
      | mk _ w wq =>
        exact Split.mk _ (s.wkLeft (w.upcast ql)) (le_trans wq ql) qr
  splitWkRight
    | Split.mk _ s ql qr, w => by
      cases w with
      | mk _ w wq =>
        exact Split.mk _ (s.wkRight (w.upcast qr)) ql (le_trans wq qr)

def Res.Split.wk {T} [ResourceAlgebraFamily T]
  {v' v l r: Res T}: Wkns.Wk v' v -> Split v l r -> Split v' l r
  := SplitWk.wkSplit

def Res.Split.wkLeft {T} [ResourceAlgebraFamily T]
  {v l l' r: Res T}: Split v l r -> Wkns.Wk l l' -> Split v l' r
  | s => SplitWk.splitWkLeft s

def Res.Split.wkRight {T} [ResourceAlgebraFamily T]
  {v l r r': Res T}: Split v l r -> Wkns.Wk r r' -> Split v l r'
  | s => SplitWk.splitWkRight s

instance Res.instSplitDropWk {T} [ResourceAlgebraFamily T]
  : SplitDropWk (Res T) where
  wkDrop
    | ⟨_, w, wq⟩, Or.inl ⟨a, dq⟩
      => Or.inl ⟨Transparency.le.aff wq a, le_trans dq w.toLE⟩
    | ⟨_, Or.inl ⟨a, wr⟩, _⟩, Or.inr d
      => Or.inl ⟨a, d ▸ wr⟩
    | ⟨_, Or.inr d, _⟩, Or.inr d'
      => Or.inr (Eq.trans d' d)
  splitDropLeft
    | ⟨_, s, ql, qr⟩, Or.inl ⟨a, dq⟩
      => ⟨_, (s.wkLeft (Or.inl ⟨Transparency.le.aff ql a, dq⟩)).dropLeft, qr⟩
    | ⟨_, s, _, qr⟩, Or.inr d
      => by simp only [] at d; exact ⟨_, (d.symm ▸ s).dropLeft, qr⟩

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

instance Var.instSplitWk {N} {T} [ResourceAlgebraFamily T]
  : SplitWk (Var N T) where
  wkSplit | ⟨Heq, w⟩, ⟨s, Hel, Her⟩ =>
            ⟨s.wk w, Eq.trans Hel Heq, Eq.trans Her Heq⟩
  splitWkLeft | ⟨s, Hel, Her⟩, ⟨Heq, w⟩ =>
                ⟨s.wkLeft w, Eq.trans Heq Hel, Her⟩
  splitWkRight | ⟨s, Hel, Her⟩, ⟨Heq, w⟩ =>
                ⟨s.wkRight w, Hel, Eq.trans Heq Her⟩

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
