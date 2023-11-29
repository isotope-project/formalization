import Isotope.Syntax.Intrinsic.LCtx

inductive GCtx (T: Type u) [HasLin T]: Type u
  | df (Γ: Ctx T)
  | cf (L: LCtx T)

inductive Result (T: Type u) [HasLin T]: Type u
  | term (x: Var T)
  | label (L: LCtx T)

class InstructionSet (F: Type u) (T: Type v)
  where
  inst_ty: F -> Ty T -> Ty T -> Prop
  inst_aff: F -> Ty T -> Ty T -> Prop
  inst_rel: F -> Ty T -> Ty T -> Prop
  inst_cen: F -> Ty T -> Ty T -> Prop


structure InstructionSet.inst {F: Type u} {T: Type v}
  [HasLin T] [InstructionSet F T]
  (f: F) (p: Bool) (q: Transparency) (A B: Ty T) where
  well_typed: inst_ty f A B
  inst_aff: (q.aff → inst_aff f A B)
  insrt_rel: (q.rel → inst_rel f A B)
  inst_cen: (p → inst_cen f A B)

open InstructionSet

inductive Term {T: Type u} [HasLin T] (F: Type u) [InstructionSet F T]
  : Ctx T -> Bool -> Ty T -> Transparency -> Type u
  | var {Γ A q} (p) (v: Γ.var ⟨q, A⟩): Term F Γ p A q
  | app {Γ} {f: F} {p A B} (Hf: inst f p q A B)
    : Term F Γ p A q -> Term F Γ p B q
  | pair {Γ Δ Ξ A B q}: Γ.ssplit Δ Ξ
    -> Term F Δ true A q
    -> Term F Ξ true B q
    -> Term F Γ true (Ty.tensor A B) q
  | unit (p) (v: Ctx.wk Γ []) (q): Term F Γ p Ty.unit q
  | tt (p) (v: Ctx.wk Γ []) (q): Term F Γ p Ty.bool q
  | ff (p) (v: Ctx.wk Γ []) (q): Term F Γ p Ty.bool q
  | let1 {Γ Δ Ξ A B q} (p): Γ.ssplit Δ Ξ
    -> Term F Ξ true A q
    -> Term F (⟨⟨true, true⟩, A⟩::Δ) p B q
    -> Term F Γ p B q
  | let2 {Γ Δ Ξ A B C q} (p): Γ.ssplit Δ Ξ
    -> Term F Ξ true (Ty.tensor A B) q
    -> Term F (⟨⟨true, true⟩, A⟩::⟨⟨true, true⟩, B⟩::Δ) p C q
    -> Term F Γ p C q

inductive NCfg {T: Type u} (F: Type u) [HasLin T] [InstructionSet F T]
  : GCtx T -> LCtx T -> Type u
  | br {Γ Δ Ξ A q L}:
    Γ.ssplit Δ Ξ ->
    Term F Ξ true A q ->
    L.label ⟨Δ, ⟨q, A⟩⟩ ->
    NCfg F (GCtx.df Γ) L
  | ite {Γ Δ Ξ L}:
    Γ.ssplit Δ Ξ ->
    Term F Ξ true Ty.bool q ->
    NCfg F (GCtx.df Δ) L ->
    NCfg F (GCtx.df Δ) L ->
    NCfg F (GCtx.df Γ) L
  | let1 {Γ Δ Ξ p A q L}:
    Γ.ssplit Δ Ξ ->
    Term F Ξ p A q ->
    NCfg F (GCtx.df (⟨⟨true, true⟩, A⟩::Δ)) L ->
    NCfg F (GCtx.df Γ) L
  | let2 {Γ Δ Ξ p A B q L}:
    Γ.ssplit Δ Ξ ->
    Term F Ξ p (Ty.tensor A B) q ->
    NCfg F (GCtx.df (⟨⟨true, true⟩, A⟩::⟨⟨true, true⟩, B⟩::Δ)) L ->
    NCfg F (GCtx.df Γ) L
  | cfg {Γ L K}:
    NCfg F (GCtx.df Γ) L ->
    NCfg F (GCtx.cf L) K ->
    NCfg F (GCtx.df Γ) K
  | cfg_id (L):
    NCfg F (GCtx.cf L) L
  | cfg_def {Γ A q L K}:
    NCfg F (GCtx.cf (⟨Γ, ⟨q, A⟩⟩::L)) K ->
    NCfg F (GCtx.df Γ) K ->
    NCfg F (GCtx.cf L) K

def Block {T: Type u} [HasLin T] (F: Type u) [InstructionSet F T]
  (Γ: Ctx T) (L: LCtx T) := NCfg F (GCtx.df Γ) L

namespace Block
export NCfg (br ite let1 let2 cfg)
end Block

def Cfg {T: Type u} [HasLin T] (F: Type u) [InstructionSet F T]
  (L: LCtx T) (K: LCtx T) := NCfg F (GCtx.cf L) K

namespace Cfg
export NCfg (cfg_id cfg_def)
end Cfg

inductive GBlock {T: Type u} (F: Type u) [HasLin T] [InstructionSet F T]
  : Ctx T -> LCtx T -> Bool -> Type u
  | br {Γ Δ Ξ A q L} (t):
    Γ.ssplit Δ Ξ ->
    Term F Ξ true A q ->
    L.label ⟨Δ, ⟨q, A⟩⟩ ->
    GBlock F Γ L t
  | ite {Γ Δ Ξ L} (t):
    Γ.ssplit Δ Ξ ->
    Term F Ξ true Ty.bool q ->
    GBlock F Δ L true ->
    GBlock F Δ L true ->
    GBlock F Γ L t
  | let1 {Γ Δ Ξ p A q L t}:
    Γ.ssplit Δ Ξ ->
    Term F Ξ p A q ->
    GBlock F (⟨⟨true, true⟩, A⟩::Δ) L t ->
    GBlock F Γ L false
  | let2 {Γ Δ Ξ p A B q L t}:
    Γ.ssplit Δ Ξ ->
    Term F Ξ p (Ty.tensor A B) q ->
    GBlock F (⟨⟨true, true⟩, A⟩::⟨⟨true, true⟩, B⟩::Δ) L t ->
    GBlock F Γ L false

def BBlock {T: Type u} (F: Type u) [HasLin T] [InstructionSet F T]
  (Γ: Ctx T) (L: LCtx T) := GBlock F Γ L false

inductive SCfg {T: Type u} (F: Type u) [HasLin T] [InstructionSet F T]
  : LCtx T -> LCtx T -> Type u
  | cfg_id (L):
    SCfg F L L
  | cfg_def {Γ A q L K}:
    SCfg F (⟨Γ, ⟨q, A⟩⟩::L) K ->
    BBlock F Γ K ->
    SCfg F L K

-- inductive Term.subst {T} [HasLin T]: Ctx T -> Ctx T -> Type
--   | nil {Γ} (H: Ctx.wk Γ []): subst Γ []
--   | cons {Θ ΘΓ Γ Θx x}
--     (s: Ctx.ssplit Θ ΘΓ Θx)
--     (HΘΓ: subst ΘΓ Γ)
--     (HΘx: HasLin.lin Θx x.toTransparency)
--     (t: Term Θx x)
--     : subst Θ (x::Γ)
