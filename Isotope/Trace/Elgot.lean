import Isotope.Trace.Optional.Elgot
import Isotope.Trace.Optional.Nonempty
import Isotope.Trace.Basic

open Classical

theorem OptTraces.dagger_nonempty {ε τ α β} [Mul ε] [One ε] [SMul ε τ] [FromStream ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (Hf: ∀a, (f a).is_nonempty)
  (a: α)
  : (ElgotMonadStructure.iterate f a).is_nonempty
  := if p: ∃t, OptTraces.iterated_nonterminating f a t
  then let ⟨t, H⟩ := p; Or.inr ⟨t, Or.inl H⟩
  else if q: ∃b e, OptTraces.iterated_terminating f a b e
  then Or.inl q
  else
    have p: ¬∃n t, (OptTraces.iterated f n a).nonterminating t
      := λ⟨n, t, H⟩ => p ⟨t, n, H⟩;
    have q: ∀n c e, (OptTraces.iterated f n a).terminating c e -> c.isRight
      := λn c e h => match c with
        | Sum.inl b => (q ⟨b, e, n, h⟩).elim
        | Sum.inr _ => rfl
      ;
    have I: ∀n a' e, (OptTraces.iterated f n a).terminating (Sum.inr a') e ->
      ∃a'' e',
        (OptTraces.iterated f n.succ a).terminating (Sum.inr a'') (e * e')
          ∧ (OptTraces.is_trace_step f a' a'' e')
      := λn a' e H =>
        match (Hf a') with
        | Or.inl ⟨Sum.inl b, e', Hae⟩ =>
          have ca := q n.succ (Sum.inl b) (e * e')
            ⟨Sum.inr a', e, e', H, Hae, rfl⟩;
          by contradiction
        | Or.inl ⟨Sum.inr a'', e', Hae⟩ => ⟨a'',
          e',
          (OptTraces.iterated_terminating_succ_inr f n a a'' _).mpr
            ⟨a', e, e', H, Hae, rfl⟩,
          Hae⟩
        | Or.inr ⟨t, Ht⟩ =>
          (p ⟨n.succ, e • t,
            (OptTraces.iterated_nonterminating_succ' f n a _).mpr
              (Or.inr ⟨a', e, t, H, Ht, rfl⟩)
          ⟩).elim
      ;
    Or.inr ⟨_, Or.inr (OptTraces.iterated_sequence_spec f a I).to_infinitely_iterated⟩

-- Note: this makes Traces into an Elgot submonad
instance Traces.instElgotMonadStructure {ε τ} [Mul ε] [One ε] [SMul ε τ] [FromStream ε τ]
  : ElgotMonadStructure (Traces ε τ)
  where
  iterate f a := {
    toOptTraces := ElgotMonadStructure.iterate (λa => (f a).toOptTraces) a,
    nonempty := OptTraces.dagger_nonempty (λa => (f a).toOptTraces) (λa => (f a).nonempty) a
  }

def Traces.arrow_iterate {ε τ} [Mul ε] [One ε] [SMul ε τ] [FromStream ε τ]
  {α β} (f: α -> Traces ε τ (β ⊕ α))
  : arrow_toOptTraces (ElgotMonadStructure.iterate f)
  = ElgotMonadStructure.iterate (arrow_toOptTraces f)
  := rfl

-- Note: follows from facts all Elgot submonads are Elgot
-- instance Traces.instElgotMonad {ε τ}
--   [Monoid ε] [MulAction ε τ] [StreamAction ε τ]: ElgotMonad (Traces ε τ)
--   where
--   fixpoint f := by
--     apply Traces.arrow_ext
--     rw [
--       Traces.arrow_iterate,
--       <-ElgotMonad.fixpoint,
--       Traces.arrow_kleisli
--     ]
--     apply congrArg
--     funext a; cases a <;> rfl
--   naturality := sorry
--   codiagonal := sorry
--   uniformity := sorry
