import Isotope.Syntax.Ty
import Isotope.ResourceAlgebra.Basic
import Isotope.Syntax.Abstract.Basic

open Abstract

namespace ResourceNamed

structure Res (T: Type v) [ResourceAlgebraFamily T] where
  ty: Ty T
  res: ty.res

instance Res.instPartialOrder {T: Type v}
  [R: ResourceAlgebraFamily T]
  : PartialOrder (Res T) where
  le l r := ∃p: l.ty = r.ty, r.ty.resourceAlgebra.le (p ▸ l.res) r.res
  le_refl l := ⟨rfl, l.ty.resourceAlgebra.le_refl _⟩
  le_trans
    | ⟨tx, rx⟩, ⟨_, ry⟩, ⟨_, rz⟩, ⟨rfl, Hxy⟩, ⟨rfl, Hyz⟩
    => ⟨rfl, tx.resourceAlgebra.le_trans _ _ _ Hxy Hyz⟩
  le_antisymm
    | ⟨tx, rx⟩, ⟨ty, ry⟩
    => by
      intro ⟨H, Hxy⟩ ⟨H', Hyx⟩; cases H
      have H'' := le_antisymm Hxy Hyx
      simp only at H'';
      simp [H'']

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
  transparency: Transparency

instance Var.instPartialOrder {N: Type u} {T: Type v} [ResourceAlgebraFamily T]
  : PartialOrder (Var N T) where
  le l r := l.name = r.name
    ∧ l.transparency ≤ r.transparency
    ∧ l.toRes ≤ r.toRes
  le_refl _ := ⟨rfl, le_refl _, le_refl _⟩
  le_trans _ _ _ H H'
    := ⟨Eq.trans H.1 H'.1, le_trans H.2.1 H'.2.1, le_trans H.2.2 H'.2.2⟩
  le_antisymm x x' H H' :=
    have Hr := le_antisymm H.2.1 H'.2.1
    have Ht := le_antisymm H.2.2 H'.2.2;
    by cases x; cases x'; simp only [] at *; rw [Hr, Ht, H.1]
