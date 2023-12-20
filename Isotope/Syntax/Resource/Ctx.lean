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

inductive Res.Splits {T: Type v} [ResourceAlgebraFamily T]
  : Res T → Res T → Res T → Prop where
  | mk {A: Ty T} {v l r: A.res} {q}
    (H: ResourceAlgebra.QSplit q v l r)
    : Res.Splits ⟨A, v, q⟩ ⟨A, l, q⟩ ⟨A, r, q⟩

-- instance Res.Splits [ResourceAlgebraFamily T]
--   : Splits (Res T) where
--   Split v l r :=
--     ∃pl: v.ty = l.ty,
--     ∃pr: v.ty = r.ty,
--     ResourceAlgebra.Split v.res (pl ▸ l.res) (pr ▸ r.res)
--   splitSymm := sorry
--   splitAssoc := sorry

--TODO: comonoid instance...

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
