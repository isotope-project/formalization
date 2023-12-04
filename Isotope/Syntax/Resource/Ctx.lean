import Isotope.Syntax.Ty
import Isotope.ResourceAlgebra.Basic

namespace SimpleNamed

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

structure Var (N: Type u) (T: Type v) [ResourceAlgebraFamily T]
  extends Res T where
  name: N
  transparency: Transparency
