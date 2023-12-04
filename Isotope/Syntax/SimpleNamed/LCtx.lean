import Isotope.Syntax.SimpleNamed.Ctx

namespace SimpleNamed

structure Label (N: Type u) (T: Type v) where
  name: N
  live: Ctx N T
  param: Var N T

def Label.subctx {N: Type u} {T: Type v} [HasLin T] (Γ: Ctx N T) (l: Label N T)
  := Γ.subctx l.live
-- def Label.subnames {N: Type u} {T: Type v} [HasLin T] (Γ: List N) (l: Label N T)
--   := Ctx.subnames Γ l.live

structure Label.wk {N: Type u} {T: Type v} [HasLin T] (l k: Label N T) where
  name: l.name = k.name
  live: l.live.wk k.live
  param: l.param ≥ k.param

def Label.wk.id {N: Type u} {T: Type v} [HasLin T] (l: Label N T): l.wk l where
  name := rfl
  live := Ctx.wk.id l.live
  param := le_refl l.param

def Label.wk.comp {N: Type u} {T: Type v} [HasLin T] {l k j: Label N T}
  (Hlk: l.wk k) (Hkj: k.wk j): l.wk j where
  name := Hlk.name.trans Hkj.name
  live := Ctx.wk.comp Hlk.live Hkj.live
  param := le_trans Hkj.param Hlk.param

abbrev LCtx (N: Type u) (T: Type v) := List (Label N T)

inductive LCtx.lwk {N: Type u} {T: Type v} [HasLin T]
  : LCtx N T -> LCtx N T -> Type (max u v)
  | nil: lwk [] []
  | unreached {L K: LCtx N T} (l: Label N T): lwk L K -> lwk L (l :: K)
  | cons {L K: LCtx N T} {l l': Label N T}
    : l.wk l' -> lwk L K  -> lwk (l :: L) (l' :: K)

@[match_pattern]
def LCtx.lwk.scons {N: Type u} {T: Type v} [HasLin T] {L K: LCtx N T}
  (l: Label N T): lwk L K -> lwk (l :: L) (l :: K)
  := cons (Label.wk.id l)

-- inductive LCtx.sjoin {T: Type u} [HasLin T]: LCtx T -> LCtx T -> Type u
--   | nil: sjoin [] []
--   | cons {L K: LCtx T} (l: Label T): sjoin L K -> sjoin (l :: L) (l :: K)
--   | unreached {L K: LCtx T} (l: Label T): sjoin L K -> sjoin L (l :: K)

def LCtx.lwk.id {N: Type u} {T: Type v} [HasLin T]: (L: LCtx N T) -> LCtx.lwk L L
  | [] => nil
  | l :: L => cons (Label.wk.id l) (lwk.id L)

def LCtx.lwk.comp {N: Type u} {T: Type v} [HasLin T] {L K M: LCtx N T}
  : LCtx.lwk L K -> LCtx.lwk K M -> LCtx.lwk L M
  | nil, j => j
  | k, unreached l j => unreached l (comp k j)
  | unreached _ j, cons H k => unreached _ (comp j k)
  | cons H j, cons H' k => cons (Label.wk.comp H H') (comp j k)

def LCtx.label {N: Type u} {T: Type v} [HasLin T] (L: LCtx N T) (l: Label N T)
  := LCtx.lwk [l] L

def LCtx.label.wk {N: Type u} {T: Type v} [HasLin T] {L: LCtx N T}
  {l k: Label N T} (W: l.wk k): L.label k -> L.label l
  | lwk.unreached l' j => lwk.unreached l' (wk W j)
  | lwk.cons W' j => lwk.cons (W.comp W') j

inductive LCtx.join {N: Type u} {T: Type v} [HasLin T]
  (P: Label N T -> Sort w)
  : LCtx N T -> LCtx N T -> LCtx N T
    -> Sort (max (max (u+1) (v+1)) w)
  | nil: join P [] [] []
  | left {L K J} (l): join P L K J -> join P (l::L) K (l::J)
  | right {L K J} (r): join P L K J -> join P L (r::K) (r::J)
  | both {L K J b}: P b -> join P L K J -> join P (b::L) (b::K) (b::J)
  | unreached {L K J} (l): join P L K J -> join P L K (l::J)

def LCtx.cjoin {N: Type u} {T: Type v} [HasLin T] (Γ: Ctx N T)
  := LCtx.join (Label.subctx Γ)

def LCtx.njoin {N: Type u} {T: Type v} [HasLin T] (Γ: List N) (L: LCtx N T)
  := LCtx.join (λL => List.Sublist L.live.names Γ) L

def LCtx.njoin.nwk {N: Type u} {T: Type v} [HasLin T] {Γ Δ: List N}
  {L K J: LCtx N T} (H: Δ.Sublist Γ): LCtx.njoin Δ L K J -> LCtx.njoin Γ L K J
  | LCtx.join.nil => LCtx.join.nil
  | LCtx.join.left _ j => LCtx.join.left _ (nwk H j)
  | LCtx.join.right _ j => LCtx.join.right _ (nwk H j)
  | LCtx.join.both b j => LCtx.join.both (b.trans H) (nwk H j)
  | LCtx.join.unreached _ j => LCtx.join.unreached _ (nwk H j)
