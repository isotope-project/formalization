import Isotope.Syntax.Intrinsic.Ctx

structure Label (T: Type u) where
  live: Ctx T
  param: Variable T

structure Label.wk {T: Type u} [HasLin T] (l k: Label T) where
  live: l.live.wk k.live
  param: l.param ≥ k.param

def Label.wk.id {T: Type u} [HasLin T] (l: Label T): l.wk l where
  live := Ctx.wk.id l.live
  param := le_refl l.param

def Label.wk.comp {T: Type u} [HasLin T] {l k j: Label T}
  (Hlk: l.wk k) (Hkj: k.wk j): l.wk j where
  live := Ctx.wk.comp Hlk.live Hkj.live
  param := le_trans Hkj.param Hlk.param

abbrev LCtx (T: Type u) := List (Label T)

inductive LCtx.join {T: Type u} [HasLin T]: LCtx T -> LCtx T -> Type u
  | nil: join [] []
  | unreached {L K: LCtx T} (l: Label T): join L K -> join L (l :: K)
  | cons {L K: LCtx T} {l l': Label T}
    : l.wk l' -> join L K  -> join (l :: L) (l' :: K)

-- inductive LCtx.sjoin {T: Type u} [HasLin T]: LCtx T -> LCtx T -> Type u
--   | nil: sjoin [] []
--   | cons {L K: LCtx T} (l: Label T): sjoin L K -> sjoin (l :: L) (l :: K)
--   | unreached {L K: LCtx T} (l: Label T): sjoin L K -> sjoin L (l :: K)

def LCtx.join.id {T: Type u} [HasLin T]: (L: LCtx T) -> LCtx.join L L
  | [] => nil
  | l :: L => cons (Label.wk.id l) (join.id L)

def LCtx.join.comp {T: Type u} [HasLin T] {L K M: LCtx T}
  : LCtx.join L K -> LCtx.join K M -> LCtx.join L M
  | nil, j => j
  | k, unreached l j => unreached l (comp k j)
  | unreached _ j, cons H k => unreached _ (comp j k)
  | cons H j, cons H' k => cons (Label.wk.comp H H') (comp j k)

--TODO: LCtx.comp_id, LCtx.id_comp, LCtx.comp_assoc ==> LCtx is a category
