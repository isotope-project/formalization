import Isotope.Syntax.Resource.Ctx
import Isotope.Syntax.Abstract.Term

inductive Ty.Cnst: Ty T -> Type
  | tt: Cnst bool
  | ff: Cnst bool
  | unit: Cnst unit

namespace ResourceNamed

structure Ctx.Cnst {N T} [ResourceAlgebraFamily T] (Γ: Ctx N T) (A: Comp T)
  : Type _ where
  drop: Drop Γ
  val: A.ty.Cnst

--TODO: is there a better way to distinguish between binds and central binds?

inductive Ctx.CBind {N T} [ResourceAlgebraFamily T]
  : Comp T -> Ctx N T -> Ctx N T -> Type _
  | let1 (x A Γ): A.central -> CBind A Γ (Γ.cons ⟨A.toRes, x⟩)
  -- | let2 (x A B Γ):

inductive Ctx.Bind {N T} [ResourceAlgebraFamily T]
  : Comp T -> Ctx N T -> Ctx N T -> Type _
  | let1 (x A Γ): Bind A Γ (Γ.cons ⟨A.toRes, x⟩)

--NOTE: there should be an equivalence with projections here, should prove this
