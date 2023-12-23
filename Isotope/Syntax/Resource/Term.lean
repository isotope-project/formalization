import Isotope.Syntax.Resource.Ctx
import Isotope.Syntax.Abstract.Term

inductive Ty.Cnst {T}: Ty T -> Type _
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

structure InstructionSet (T) [ResourceAlgebraFamily T] where
  Op: Res T -> Comp T -> Type

structure InstructionSet.Hom {T} [ResourceAlgebraFamily T] (I: InstructionSet T)
  (A B: Comp T) where
  central_le: B.central -> A.central
  op_ty: Comp T
  op_le: op_ty ≥ B
  op: I.Op A.toRes op_ty

def InstructionSet.toQuiver {T} [ResourceAlgebraFamily T] (IS: InstructionSet T)
  : Quiver (Comp T) where
  Hom := Hom IS

--TODO: joining into pairs for Res T...
-- intersection of quantities? how to express this best?

--TODO: joining into pairs for Comp T...
-- can say only centrals join

-- def InstructionSet.toLang {N T} [ResourceAlgebraFamily T] (IS: InstructionSet T)
--   : Abstract.Lang (Ctx N T) where
--   Ty := Comp T
--   pair := sorry
--   inst := IS.toQuiver
--   cnst := Ctx.Cnst
--   var := Ctx.Var
--   bind := Ctx.Bind
