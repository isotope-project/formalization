import Isotope.Syntax.Resource.Ctx

namespace ResourceNamed

def Ctx.SJoin {N T} [ResourceAlgebraFamily T]
  : Ctx N T → Ctx N T → Ctx N T -> Sort _
  | Γ, Δ, Θ => SWk Γ Θ × SWk Δ Θ

def Ctx.Join {N T} [ResourceAlgebraFamily T]
  : Ctx N T → Ctx N T → Ctx N T -> Sort _
  | Γ, Δ, Θ => Wk Γ Θ × Wk Δ Θ

def Ctx.LiveWk {N T} [ResourceAlgebraFamily T]
  : Bool -> Ctx N T -> Ctx N T -> Sort _
  | true => SWk
  | false => Wk

structure Label (N: Type u) (T: Type v) [ResourceAlgebraFamily T] where
  name: N
  live: Ctx N T
  --TODO: why a res and not just a type? Is this the right level of generality?
  param: Res T
  dominated: Bool

structure Label.Join {N T} [ResourceAlgebraFamily T] (ℓ κ τ: Label N T) where
  left_name: ℓ.name = τ.name
  right_name: κ.name = τ.name
  left_res: ℓ.param ≥ τ.param
  right_res: κ.param ≥ τ.param
  left_free: ¬ℓ.dominated
  right_free: ¬κ.dominated
  join_free: ¬τ.dominated
  live_join: ℓ.live.Join κ.live τ.live

structure Label.Wk {N T} [ResourceAlgebraFamily T] (ℓ κ: Label N T) where
  name: ℓ.name = κ.name
  res: ℓ.param ≥ κ.param
  dominated: ℓ.dominated ≥ κ.dominated
  wk: ℓ.live.LiveWk ℓ.dominated κ.live

def Label.Split {N T} [ResourceAlgebraFamily T] (ℓ κ τ: Label N T)
  := ℓ.Wk κ × ℓ.Wk τ

def LCtx (N: Type u) (T: Type v) [ResourceAlgebraFamily T] := List (Label N T)

-- def LCtx.Join {N T} [ResourceAlgebraFamily T]
--   : LCtx N T → LCtx N T → LCtx N T -> Sort _
--   := sorry
