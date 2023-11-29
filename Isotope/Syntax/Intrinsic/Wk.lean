import Isotope.Syntax.Intrinsic.Basic

def Term.wk {T: Type u} [HasLin T] {F: Type u} [InstructionSet F T]
  {Γ Δ: Ctx T} {c A q} (W: Γ.wk Δ)
  : Term F Δ c A q → Term F Γ c A q
  | var p X => var p (W.comp X)
  | app Hf a => app Hf (wk W a)
  | pair S a b =>
    have ⟨_, _, S', Wl, Wr⟩ := S.distribute_left W;
    pair S' (wk Wl a) (wk Wr b)
  | unit p D q => unit p (W.comp D) q
  | tt p D q => tt p (W.comp D) q
  | ff p D q => ff p (W.comp D) q
  | let1 p S a e =>
    have ⟨_, _, S', Wl, Wr⟩ := S.distribute_left W;
    let1 p S' (wk Wr a) (wk (Wl.scons _) e)
  | let2 p S a e =>
    have ⟨_, _, S', Wl, Wr⟩ := S.distribute_left W;
    let2 p S' (wk Wr a) (wk ((Wl.scons _).scons _) e)

inductive GCtx.wk {T: Type u} [HasLin T]: GCtx T -> GCtx T -> Type u
  | df {Γ Δ: Ctx T}: Γ.wk Δ -> GCtx.wk (df Γ) (df Δ)

def NCfg.wk {T: Type u} [HasLin T] {F: Type u} [InstructionSet F T]
  {L}:
  {G G': GCtx T} -> G.wk G' -> NCfg F G' L → NCfg F G L
  | _, _, GCtx.wk.df W, br S a l =>
    have ⟨Δ', Ξ', S', Wl, Wr⟩ := S.distribute_left W;
    -- Don't know why this requires going into tactic mode not to get a type error
    br S' (a.wk Wr) (l.wk ⟨by exact Wl, by apply le_refl⟩ )
  | _, _, GCtx.wk.df W, ite S e s t =>
    have ⟨_, _, S', Wl, Wr⟩ := S.distribute_left W;
    ite S' (e.wk Wr) (s.wk (GCtx.wk.df Wl)) (t.wk (GCtx.wk.df Wl))
  | _, _, GCtx.wk.df W, let1 S a t =>
    have ⟨_, _, S', Wl, Wr⟩ := S.distribute_left W;
    let1 S' (a.wk Wr) (t.wk (GCtx.wk.df (Wl.scons _)))
  | _, _, GCtx.wk.df W, let2 S a t =>
    have ⟨_, _, S', Wl, Wr⟩ := S.distribute_left W;
    let2 S' (a.wk Wr) (t.wk (GCtx.wk.df ((Wl.scons _).scons _)))
  | _, _, GCtx.wk.df W, cfg t C => cfg (t.wk (GCtx.wk.df W)) C

def Block.wk {T: Type u} [HasLin T] {F: Type u} [InstructionSet F T]
  {Γ Δ: Ctx T} {L} (W: Γ.wk Δ)
  : Block F Δ L → Block F Γ L
  := NCfg.wk (GCtx.wk.df W)
