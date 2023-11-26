import Isotope.Trace.Optional.Basic
import Isotope.Trace.Optional.Nonempty
import Isotope.StreamAction
import Isotope.Utils.Monad
import Isotope.Elgot.Monad
import Mathlib.Data.Stream.Defs

open Classical

def OptTraces.iterated {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  : ℕ -> α-> OptTraces ε τ (β ⊕ α)
  | 0, a => pure (Sum.inr a)
  | n + 1, a => (iterated f n a) >>= Sum.elim (pure ∘ Sum.inl) f

def OptTraces.iterated_kleisli {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  : ℕ -> α -> OptTraces ε τ (β ⊕ α)
  | 0 => pure ∘ Sum.inr
  | n + 1 => (iterated_kleisli f n) >=> Sum.elim (pure ∘ Sum.inl) f

def OptTraces.iterated_kleisli_spec
  : @iterated_kleisli = @iterated
  := by funext ε τ α β _ _ _ f n; induction n with
  | zero => rfl
  | succ n I => simp only [iterated_kleisli, I]; rfl

def OptTraces.iterated_kleisli_back {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  : ℕ -> α -> OptTraces ε τ (β ⊕ α)
  | 0 => pure ∘ Sum.inr
  | n + 1 => f >=> Sum.elim (pure ∘ Sum.inl) (iterated_kleisli_back f n)

def OptTraces.iterated_back {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  : ℕ -> α-> OptTraces ε τ (β ⊕ α)
  | 0, a => pure (Sum.inr a)
  | n + 1, a => f a >>= Sum.elim (pure ∘ Sum.inl) (iterated_back f n)

def OptTraces.iterated_kleisli_back_spec'
  : @iterated_kleisli_back = @iterated_back
  := by funext ε τ α β _ _ _ f n; induction n with
  | zero => rfl
  | succ n I => simp only [iterated_kleisli_back, I]; rfl

def OptTraces.iterated_kleisli_back_spec''
  {ε τ α β}
  [m: Monoid ε] [a: MulAction ε τ]
  : @iterated_kleisli_back ε τ α β m.toMul m.toOne a.toSMul
  = @iterated_kleisli ε τ α β m.toMul m.toOne a.toSMul
  := by funext f n; induction n with
  | zero => rfl
  | succ n I =>
    simp only [iterated_kleisli_back, iterated_kleisli]
    funext a
    cases n with
    | zero => simp [I, iterated_kleisli, Bind.kleisliRight]
    | succ n =>
      rw [
        <-I, iterated_kleisli_back,
        <-kleisli_assoc
      ]
      apply bind_congr
      intro c
      cases c with
      | inl b => simp [Bind.kleisliRight]
      | inr a =>
        simp only [Sum.elim_inr, Bind.kleisliRight, iterated_kleisli_back_spec']
        clear I
        induction n generalizing a with
        | zero =>
          rw [<-iterated_kleisli_back_spec']
          simp [iterated_kleisli_back]
        | succ n I =>
          simp only [iterated_back]
          rw [bind_assoc]
          apply congr rfl
          funext c
          cases c with
          | inl b => simp
          | inr a => simp [I]

def OptTraces.iterated_kleisli_back_spec
  {ε τ α β}
  [m: Monoid ε] [a: MulAction ε τ]
  : @iterated_kleisli_back ε τ α β m.toMul m.toOne a.toSMul
  = @iterated ε τ α β m.toMul m.toOne a.toSMul
  := by rw [
    iterated_kleisli_back_spec'',
    iterated_kleisli_spec
  ]

def OptTraces.iterated_back_spec
  {ε τ α β}
  [m: Monoid ε] [a: MulAction ε τ]
  : @iterated_back ε τ α β m.toMul m.toOne a.toSMul
  = @iterated ε τ α β m.toMul m.toOne a.toSMul
  := by rw [
    <-iterated_kleisli_back_spec',
    iterated_kleisli_back_spec
  ]

def OptTraces.is_trace_step {ε τ α β}
  (f: α -> OptTraces ε τ (β ⊕ α))
  (a: α)
  (r: α)
  (e: ε)
  : Prop
  := (f a).terminating (Sum.inr r) e

theorem OptTraces.iterated_terminating_zero {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (a: α)
  (c e)
  : (iterated f 0 a).terminating c e ↔ (c = Sum.inr a ∧ e = 1)
  := by rfl

theorem OptTraces.iterated_nonterminating_zero {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (a: α)
  (t)
  : (iterated f 0 a).nonterminating t ↔ False
  := by rfl

theorem OptTraces.iterated_terminating_succ {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (n: ℕ)
  (a: α)
  (c e)
  : (iterated f n.succ a).terminating c e ↔
  (∃ c' e' e'',
    terminating (iterated f n a) c' e' ∧
      terminating (Sum.elim (pure ∘ Sum.inl) f c') c e'' ∧
      e = e' * e'')
  := by rfl

theorem OptTraces.iterated_nonterminating_succ {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (n: ℕ)
  (a: α)
  (t)
  : (iterated f n.succ a).nonterminating t ↔
    (iterated f n a).nonterminating t
      ∨ ∃c e t', (iterated f n a).terminating c e
        ∧ (Sum.elim (pure ∘ Sum.inl) f c).nonterminating t'
        ∧ t = e • t'
  := by rfl

theorem OptTraces.iterated_terminating_succ' {ε τ α β}
  [Monoid ε] [SMul ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (n: ℕ)
  (a: α)
  (c e)
  : (iterated f n.succ a).terminating c e ↔
    ((∃b, (iterated f n a).terminating (Sum.inl b) e ∧ c = Sum.inl b) ∨ (∃a' e' e'',
      (iterated f n a).terminating (Sum.inr a') e' ∧
        (f a').terminating c e'' ∧ e = e' * e''))
  := ⟨
      λ
      | ⟨Sum.inl b, e', e'', Hfn, ⟨Hb, He''⟩, He⟩ =>
        have p: e = e' := by simp [He, He''];
        Or.inl ⟨b, p ▸ Hfn, Hb⟩
      | ⟨Sum.inr a', e', e'', Hfn, Hf, He⟩ => Or.inr ⟨a', e', e'', Hfn, Hf, He⟩,
      λ
      | Or.inl ⟨b, Hfn, Hb⟩ => ⟨Sum.inl b, e, 1, Hfn, ⟨Hb, rfl⟩, by simp⟩
      | Or.inr ⟨a', e', e'', Hfn, Hf, He⟩ => ⟨Sum.inr a', e', e'', Hfn, Hf, He⟩
    ⟩

theorem OptTraces.iterated_nonterminating_succ' {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (n: ℕ)
  (a: α)
  (t)
  : (iterated f n.succ a).nonterminating t ↔
    (iterated f n a).nonterminating t
      ∨ ∃a' e t', (iterated f n a).terminating (Sum.inr a') e
        ∧ (f a').nonterminating t'
        ∧ t = e • t'
  := ⟨
    λ
    | Or.inl H => Or.inl H
    | Or.inr ⟨Sum.inr a', e, t', Ha', Ht', Ht⟩ => Or.inr ⟨a', e, t', Ha', Ht', Ht⟩,
    λ
    | Or.inl H => Or.inl H
    | Or.inr ⟨a', e, t', Ha', Ht', Ht⟩ => Or.inr ⟨Sum.inr a', e, t', Ha', Ht', Ht⟩
  ⟩

theorem OptTraces.iterated_terminating_succ_inr {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (n: ℕ)
  (a: α)
  (a' e)
  : (iterated f n.succ a).terminating (Sum.inr a') e ↔
    ∃a'' e' e'',
      (iterated f n a).terminating (Sum.inr a'') e'
        ∧ is_trace_step f a'' a' e''
        ∧ e = e' * e''
  := ⟨
      λ
      | ⟨Sum.inl b, _, _, _, ⟨Hb, _⟩, _⟩ => by contradiction
      | ⟨Sum.inr a', e', e'', Hfn, Hf, He⟩ => ⟨a', e', e'', Hfn, Hf, He⟩,
      λ ⟨a', e', e'', Hfn, Hf, He⟩ => ⟨Sum.inr a', e', e'', Hfn, Hf, He⟩
    ⟩

def OptTraces.iterated_terminating {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (a: α) (b: β) (e: ε): Prop
  := ∃n: ℕ, (OptTraces.iterated f n a).terminating (Sum.inl b) e

def OptTraces.iterated_nonterminating {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (a: α) (t: τ): Prop
  := ∃n: ℕ, (OptTraces.iterated f n a).nonterminating t

def accumulate_stream {ε} [Mul ε] [One ε] (es: Stream' ε): Stream' ε
  | 0 => 1
  | n + 1 => accumulate_stream es n * es n

def OptTraces.is_preinfinite_trace {ε τ α β}
  (f: α -> OptTraces ε τ (β ⊕ α))
  (as: Stream' α)
  : Prop
  := ∀n: ℕ, ∃e, OptTraces.is_trace_step f (as n) (as n.succ) e

def OptTraces.is_infinite_trace {ε τ α β}
  (f: α -> OptTraces ε τ (β ⊕ α))
  (as: Stream' α)
  (es: Stream' ε)
  : Prop
  := ∀n: ℕ, OptTraces.is_trace_step f (as n) (as n.succ) (es n)

noncomputable def OptTraces.is_preinfinite_trace.to_event_trace {ε τ α β}
  {f: α -> OptTraces ε τ (β ⊕ α)}
  {as: Stream' α}
  (H: is_preinfinite_trace f as)
  : Stream' ε
  := λn => Classical.choose (H n)

theorem OptTraces.is_preinfinite_trace.to_infinite_trace {ε τ α β}
  {f: α -> OptTraces ε τ (β ⊕ α)}
  {as: Stream' α}
  (H: is_preinfinite_trace f as)
  : is_infinite_trace f as H.to_event_trace
  := λn => Classical.choose_spec (H n)

noncomputable def OptTraces.is_preinfinite_trace.to_effect {ε τ α β}
  [FromStream ε τ]
  {f: α -> OptTraces ε τ (β ⊕ α)}
  {as: Stream' α}
  (H: is_preinfinite_trace f as)
  : τ := FromStream.fromStream H.to_event_trace

theorem OptTraces.is_infinite_trace_spec {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (as: Stream' α)
  (es: Stream' ε)
  (H: is_infinite_trace f as es)
  : ∀n, (iterated f n (as 0)).terminating (Sum.inr (as n)) (accumulate_stream es n)
  | 0 => ⟨rfl, rfl⟩
  | n + 1 => ⟨
      (Sum.inr (as n)), (accumulate_stream es n), es n,
        by simp [is_infinite_trace_spec f as es H n],
        H n, rfl⟩

def OptTraces.infinitely_iterated {ε τ α β}
  [FromStream ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (a: α)
  (t: τ): Prop
  := ∃(as: Stream' α) (es: Stream' ε),
    as 0 = a ∧
    FromStream.fromStream es = t ∧
    is_infinite_trace f as es

theorem OptTraces.is_infinite_trace.to_infinitely_iterated {ε τ α β}
  [FromStream ε τ]
  {f: α -> OptTraces ε τ (β ⊕ α)}
  {as: Stream' α}
  {es: Stream' ε}
  (H: is_infinite_trace f as es)
  : infinitely_iterated f (as 0) (FromStream.fromStream es)
  := ⟨as, es, rfl, rfl, H⟩

theorem OptTraces.is_preinfinite_trace.to_infinitely_iterated {ε τ α β}
  [FromStream ε τ]
  {f: α -> OptTraces ε τ (β ⊕ α)}
  {as: Stream' α}
  (H: is_preinfinite_trace f as)
  : infinitely_iterated f (as 0) (H.to_effect)
  := H.to_infinite_trace.to_infinitely_iterated

theorem OptTraces.is_infinite_trace.to_infinitely_iterated' {ε τ α β}
  [FromStream ε τ]
  {f: α -> OptTraces ε τ (β ⊕ α)}
  {as: Stream' α}
  {es: Stream' ε}
  (H: is_infinite_trace f as es)
  (a: α)
  (Ha: as 0 = a)
  (e: τ)
  (He: FromStream.fromStream es = e)
  : infinitely_iterated f a e
  := ⟨as, es, Ha, He, H⟩

theorem OptTraces.is_preinfinite_trace.to_infinitely_iterated' {ε τ α β}
  [FromStream ε τ]
  {f: α -> OptTraces ε τ (β ⊕ α)}
  {as: Stream' α}
  (H: is_preinfinite_trace f as)
  (a: α)
  (Ha: as 0 = a)
  (e: τ)
  (He: H.to_effect = e)
  : infinitely_iterated f a e
  := H.to_infinite_trace.to_infinitely_iterated' a Ha e He

def exists_nfn {α} {β: α -> Prop}: (¬∀a: α, ¬β a) -> ∃a: α, β a
  := λk => Classical.by_contradiction (λk' => k (λa h => k' ⟨a, h⟩))

noncomputable def OptTraces.iterated_sequence_helper {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ] [FromStream ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (a: α)
  (I: ∀n a' e, (OptTraces.iterated f n a).terminating (Sum.inr a') e ->
          ∃a'' e',
            (OptTraces.iterated f n.succ a).terminating (Sum.inr a'') (e * e')
              ∧ (OptTraces.is_trace_step f a' a'' e'))
  : (n: ℕ) -> {p: α × ε | ∃e', (OptTraces.iterated f n a).terminating (Sum.inr p.1) e'}
  | 0 => ⟨⟨a, 1⟩, 1, rfl, rfl⟩
  | n + 1 =>
    let Hv := iterated_sequence_helper f a I n;
    let HI := I n Hv.1.1 (Classical.choose Hv.2) (Classical.choose_spec Hv.2)
    let a'' := Classical.choose HI;
    let e' := Classical.choose (Classical.choose_spec HI);
    let HI' := Classical.choose_spec (Classical.choose_spec HI);
    ⟨⟨a'', e'⟩, _, HI'.1⟩

noncomputable def OptTraces.iterated_sequence {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ] [FromStream ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (a: α)
  (I: ∀n a' e, (OptTraces.iterated f n a).terminating (Sum.inr a') e ->
          ∃a'' e',
            (OptTraces.iterated f n.succ a).terminating (Sum.inr a'') (e * e')
              ∧ (OptTraces.is_trace_step f a' a'' e'))
  : Stream' α
  := λn => (iterated_sequence_helper f a I n).1.1

noncomputable def OptTraces.iterated_event_sequence {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ] [FromStream ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (a: α)
  (I: ∀n a' e, (OptTraces.iterated f n a).terminating (Sum.inr a') e ->
          ∃a'' e',
            (OptTraces.iterated f n.succ a).terminating (Sum.inr a'') (e * e')
              ∧ (OptTraces.is_trace_step f a' a'' e'))
  : Stream' ε
  := λn => (iterated_sequence_helper f a I n.succ).1.2

theorem OptTraces.iterated_sequence_zero {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ] [FromStream ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (a: α)
  (I: ∀n a' e, (OptTraces.iterated f n a).terminating (Sum.inr a') e ->
          ∃a'' e',
            (OptTraces.iterated f n.succ a).terminating (Sum.inr a'') (e * e')
              ∧ (OptTraces.is_trace_step f a' a'' e'))
  : (iterated_sequence f a I) 0 = a
  := rfl

theorem OptTraces.iterated_sequence_succ {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ] [FromStream ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (a: α)
  (I: ∀n a' e, (OptTraces.iterated f n a).terminating (Sum.inr a') e ->
          ∃a'' e',
            (OptTraces.iterated f n.succ a).terminating (Sum.inr a'') (e * e')
              ∧ (OptTraces.is_trace_step f a' a'' e'))
  (n: ℕ)
  : (iterated_sequence f a I) n.succ =
    let Hv := iterated_sequence_helper f a I n;
    let HI := I n Hv.1.1 (Classical.choose Hv.2) (Classical.choose_spec Hv.2)
    Classical.choose HI
  := rfl

theorem OptTraces.iterated_sequence_spec {ε τ α β}
  [Mul ε] [One ε] [SMul ε τ] [FromStream ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (a: α)
  (I: ∀n a' e, (OptTraces.iterated f n a).terminating (Sum.inr a') e ->
          ∃a'' e',
            (OptTraces.iterated f n.succ a).terminating (Sum.inr a'') (e * e')
              ∧ (OptTraces.is_trace_step f a' a'' e'))
  : is_infinite_trace f (iterated_sequence f a I) (iterated_event_sequence f a I)
  := λn =>
    let Hv := iterated_sequence_helper f a I n;
    let HI := I n Hv.1.1 (Classical.choose Hv.2) (Classical.choose_spec Hv.2)
    (Classical.choose_spec (Classical.choose_spec HI)).2

instance OptTraces.instElgotMonadStructure {ε τ} [Mul ε] [One ε] [SMul ε τ] [FromStream ε τ]
  : ElgotMonadStructure (OptTraces ε τ)
  where
  iterate f a := {
    terminating := OptTraces.iterated_terminating f a,
    nonterminating := λt =>
      OptTraces.iterated_nonterminating f a t ∨
      OptTraces.infinitely_iterated f a t
  }

theorem OptTraces.dagger_terminating {ε τ α β} [Mul ε] [One ε] [SMul ε τ] [FromStream ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (a: α)
  : (ElgotMonadStructure.iterate f a).terminating = OptTraces.iterated_terminating f a
  := rfl

theorem OptTraces.dagger_nonterminating {ε τ α β} [Mul ε] [One ε] [SMul ε τ] [FromStream ε τ]
  (f: α -> OptTraces ε τ (β ⊕ α))
  (a: α) (t)
  : (ElgotMonadStructure.iterate f a).nonterminating t
  = (OptTraces.iterated_nonterminating f a t ∨
    OptTraces.infinitely_iterated f a t)
  := rfl

-- instance OptTraces.instElgotMonad {ε τ} [Monoid ε] [MulAction ε τ] [StreamAction ε τ]: ElgotMonad (OptTraces ε τ)
--   where
--   fixpoint f := by
--     funext a
--     apply OptTraces.ext
--     constructor
--     . funext b e
--       apply propext
--       apply Iff.intro
--       . intro ⟨c, e', e'', Hstep, Htail, He⟩
--         cases c with
--         | inl b' =>
--           exact ⟨1, Sum.inr a, e'', e',
--             ⟨rfl, Htail.2⟩,
--             Htail.1 ▸ Hstep,
--             by rw [Htail.2, one_mul, He, Htail.2, mul_one]⟩
--         | inr a' =>
--           let ⟨n, Htail⟩ := Htail;
--           exists n.succ
--           rw [<-iterated_back_spec, iterated_back]
--           exact ⟨Sum.inr a', e', e'',
--             Hstep,
--             by rw [iterated_back_spec]; exact Htail,
--             He⟩
--       . intro ⟨n, H⟩
--         cases n with
--         | zero => simp [iterated, pure, pure'] at H
--         | succ n =>
--           rw [<-iterated_back_spec] at H
--           let ⟨c, e, e', Hstep, Hiter, He⟩ := H;
--           cases c with
--           | inl b' =>
--             exact ⟨
--               Sum.inl b', e, e', Hstep,
--               ⟨Sum.inl.inj Hiter.1, Hiter.2⟩,
--               He⟩
--           | inr a' =>
--             rw [iterated_back_spec] at Hiter
--             exact ⟨Sum.inr a', e, e', Hstep, ⟨n, Hiter⟩, He⟩
--     . funext t
--       apply propext
--       apply Iff.intro
--       . intro H
--         match H with
--         | Or.inl Hstep => exact Or.inl ⟨1, Or.inr ⟨Sum.inr a, 1, t, ⟨rfl, rfl⟩, Hstep, by simp⟩⟩
--         | Or.inr ⟨Sum.inr a', e, t', Hstep, Or.inl ⟨n, Hiter⟩, He⟩ =>
--           exact Or.inl ⟨n.succ, by
--             rw [<-iterated_back_spec]
--             exact Or.inr ⟨Sum.inr a', e, t', Hstep,
--               by rw [iterated_back_spec]; exact Hiter,
--               He⟩
--             ⟩
--         | Or.inr ⟨Sum.inr a', e, t', Hstep, Or.inr ⟨as, es, Has, Hes, Hiter⟩, He⟩ =>
--           exact Or.inr ⟨as.cons a, es.cons e, rfl,
--             by rw [StreamAction.fromStream_cons, Hes, He],
--             λ
--             | 0 => by
--               simp only [Stream'.cons, Has]
--               exact Hstep
--             | n + 1 => Hiter n⟩
--       . intro H
--         match H with
--         | Or.inl ⟨0, H⟩ => simp [iterated, pure, pure'] at H
--         | Or.inl ⟨n + 1, H⟩ =>
--           rw [<-iterated_back_spec, iterated_back] at H;
--           match H with
--           | Or.inl Hstep => exact Or.inl Hstep
--           | Or.inr ⟨Sum.inr a', e, t', Hstep, Hiter, He⟩ =>
--             exact Or.inr ⟨Sum.inr a', e, t', Hstep, Or.inl ⟨n, by rw [<-iterated_back_spec]; exact Hiter⟩, He⟩
--         | Or.inr ⟨as, es, Has, Hes, Hiter⟩ =>
--           exact Or.inr ⟨
--             Sum.inr (as 1), es 0, FromStream.fromStream es.tail,
--             Has ▸ Hiter 0,
--             Or.inr ⟨as.tail, es.tail, rfl, rfl, λn => Hiter n.succ⟩,
--             by rw [<-StreamAction.fromStream_ind, Hes]
--           ⟩
--   naturality f g := sorry
--     -- by
--     -- funext a
--     -- apply OptTraces.ext
--     -- constructor
--     -- . sorry
--     -- . sorry
--   codiagonal f := sorry
--   uniformity f g h := sorry
