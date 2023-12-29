import Isotope.Syntax.Resource.Ctx
import Isotope.Syntax.Abstract.List

open Abstract
open Joins

namespace ResourceNamed

structure Ctx.SJoin {N T} [ResourceAlgebraFamily T] (Γ Δ Ξ: Ctx N T) where
  left: SWk Γ Ξ
  right: SWk Δ Ξ

structure Ctx.Join {N T} [ResourceAlgebraFamily T] (Γ Δ Ξ: Ctx N T) where
  left: Wk Γ Ξ
  right: Wk Δ Ξ

def Ctx.Join.symm {N T} [ResourceAlgebraFamily T]
  {Γ Δ Ξ: Ctx N T} (J: Join Γ Δ Ξ): Join Δ Γ Ξ where
  left := J.right
  right := J.left

def Ctx.Join.assoc {N T} [ResourceAlgebraFamily T]
  {Γ123 Γ12 Γ1 Γ2 Γ3: Ctx N T} (J12_3: Join Γ12 Γ3 Γ123) (J1_2: Join Γ1 Γ2 Γ12)
  : (_: Join Γ1 Γ123 Γ123) ×' Join Γ2 Γ3 Γ123
  := ⟨{
      left := J1_2.left.trans J12_3.left
      right := Wk.id _
      },
      {
        left := J1_2.right.trans J12_3.left
        right := J12_3.right
      }⟩

instance Ctx.instJoins {N T} [ResourceAlgebraFamily T]: Joins (Ctx N T)
  where
  Join := Join
  joinSymm := Join.symm
  joinAssoc J J' := ⟨_, Join.assoc J J'⟩

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

def Label.Join.symm {N T} [ResourceAlgebraFamily T] {ℓ κ τ: Label N T}
  (J: Join ℓ κ τ): Join κ ℓ τ where
  left_name := J.right_name
  right_name := J.left_name
  left_res := J.right_res
  right_res := J.left_res
  left_free := J.right_free
  right_free := J.left_free
  join_free := J.join_free
  live_join := J.live_join.symm

def Label.Join.assoc {N T} [ResourceAlgebraFamily T]
  {ℓ123 ℓ12 ℓ1 ℓ2 ℓ3: Label N T}
  (J12_3: Join ℓ12 ℓ3 ℓ123)
  (J1_2: Join ℓ1 ℓ2 ℓ12)
  : (_: Join ℓ1 ℓ123 ℓ123) ×' Join ℓ2 ℓ3 ℓ123
  := let ⟨J1_23, J2_3⟩ := J12_3.live_join.assoc J1_2.live_join;
    ⟨
    {
      left_name := J1_2.left_name.trans J12_3.left_name
      right_name := rfl
      left_res := le_trans J12_3.left_res J1_2.left_res
      right_res := le_refl _
      left_free := J1_2.left_free
      right_free := J12_3.join_free
      join_free := J12_3.join_free
      live_join := J1_23
    },
    {
      left_name := J1_2.right_name.trans J12_3.left_name
      right_name := J12_3.right_name
      left_res := le_trans J12_3.left_res J1_2.right_res
      right_res := J12_3.right_res
      left_free := J1_2.right_free
      right_free := J12_3.right_free
      join_free := J12_3.join_free
      live_join := J2_3
    }⟩

instance Label.instJoins {N T} [ResourceAlgebraFamily T]: Joins (Label N T)
  where
  Join := Join
  joinSymm := Join.symm
  joinAssoc J J' := ⟨_, Join.assoc J J'⟩

structure Label.Wk {N T} [ResourceAlgebraFamily T] (ℓ κ: Label N T) where
  name: ℓ.name = κ.name
  res: ℓ.param ≥ κ.param
  dominated: ℓ.dominated ≥ κ.dominated
  wk: ℓ.live.LiveWk ℓ.dominated κ.live

def Label.Split {N T} [ResourceAlgebraFamily T] (ℓ κ τ: Label N T)
  := ℓ.Wk κ × ℓ.Wk τ

def LCtx (N: Type u) (T: Type v) [ResourceAlgebraFamily T] := List (Label N T)

def LCtx.Join {N T} [ResourceAlgebraFamily T]
  : LCtx N T → LCtx N T → LCtx N T -> Sort _
  := OptElementwise.Join
