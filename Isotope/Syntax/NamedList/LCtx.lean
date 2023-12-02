import Isotope.Syntax.NamedList.Ctx

namespace NamedList

structure Label (T: Type u) where
  name: String
  live: Ctx T
  param: Var T

def Label.subctx {T: Type u} [HasLin T] (Γ: Ctx T) (l: Label T)
  := Γ.subctx l.live

structure Label.wk {T: Type u} [HasLin T] (l k: Label T) where
  name: l.name = k.name
  live: l.live.wk k.live
  param: l.param ≥ k.param

def Label.wk.id {T: Type u} [HasLin T] (l: Label T): l.wk l where
  name := rfl
  live := Ctx.wk.id l.live
  param := le_refl l.param

def Label.wk.comp {T: Type u} [HasLin T] {l k j: Label T}
  (Hlk: l.wk k) (Hkj: k.wk j): l.wk j where
  name := Hlk.name.trans Hkj.name
  live := Ctx.wk.comp Hlk.live Hkj.live
  param := le_trans Hkj.param Hlk.param

abbrev LCtx (T: Type u) := List (Label T)

inductive LCtx.lwk {T: Type u} [HasLin T]: LCtx T -> LCtx T -> Type u
  | nil: lwk [] []
  | unreached {L K: LCtx T} (l: Label T): lwk L K -> lwk L (l :: K)
  | cons {L K: LCtx T} {l l': Label T}
    : l.wk l' -> lwk L K  -> lwk (l :: L) (l' :: K)

-- inductive LCtx.sjoin {T: Type u} [HasLin T]: LCtx T -> LCtx T -> Type u
--   | nil: sjoin [] []
--   | cons {L K: LCtx T} (l: Label T): sjoin L K -> sjoin (l :: L) (l :: K)
--   | unreached {L K: LCtx T} (l: Label T): sjoin L K -> sjoin L (l :: K)

def LCtx.lwk.id {T: Type u} [HasLin T]: (L: LCtx T) -> LCtx.lwk L L
  | [] => nil
  | l :: L => cons (Label.wk.id l) (lwk.id L)

def LCtx.lwk.comp {T: Type u} [HasLin T] {L K M: LCtx T}
  : LCtx.lwk L K -> LCtx.lwk K M -> LCtx.lwk L M
  | nil, j => j
  | k, unreached l j => unreached l (comp k j)
  | unreached _ j, cons H k => unreached _ (comp j k)
  | cons H j, cons H' k => cons (Label.wk.comp H H') (comp j k)

def LCtx.label {T: Type u} [HasLin T] (L: LCtx T) (l: Label T): Type u
  := LCtx.lwk [l] L

def LCtx.label.wk {T: Type u} [HasLin T] {L: LCtx T} {l k: Label T}
  (W: l.wk k): L.label k -> L.label l
  | lwk.unreached l' j => lwk.unreached l' (wk W j)
  | lwk.cons W' j => lwk.cons (W.comp W') j

inductive LCtx.join {T: Type u} [HasLin T]
  : (Label T -> Sort v) -> LCtx T -> LCtx T -> LCtx T -> Sort (max (u+1) v)
  | nil P: join P [] [] []
  | left {P L K J} (l): join P L K J -> join P (l::L) K (l::J)
  | right {P L K J} (r): join P L K J -> join P L (r::K) (r::J)
  | both {P L K J b}: P b -> join P L K J -> join P (b::L) (b::K) (b::J)
  | unreached {P L K J} (l): join P L K J -> join P L K (l::J)

def LCtx.cjoin {T: Type u} [HasLin T] (Γ: Ctx T)
  := LCtx.join (Label.subctx Γ)
