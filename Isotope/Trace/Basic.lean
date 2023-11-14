import Isotope.Trace.Optional.Nonempty

class Traces (ε τ α) extends OptTraces ε τ α where
  nonempty: toOptTraces.is_nonempty

def Traces.arrow_toOptTraces {ε τ α β} (f: α -> Traces ε τ β)
  (a: α): OptTraces ε τ β
  := (f a).toOptTraces

def Trace.toTraces {ε τ α} (t: Trace ε τ α): Traces ε τ α where
  toOptTraces := t.toOptTraces
  nonempty := t.toOptTraces_is_nonempty

theorem Traces.ext {ε τ α} (t t': Traces ε τ α)
  : t.toOptTraces = t'.toOptTraces -> t = t'
  := λH => by
      cases t; cases t';
      let ⟨_, _⟩ := (OptTraces.injEq' _ _).mpr H;
      simp only at *;
      simp [*]

def Traces.arrow_ext {ε τ α β} (f g: α -> Traces ε τ β)
  (H: arrow_toOptTraces f = arrow_toOptTraces g): f = g
  := by
    have H': ∀a, arrow_toOptTraces f a = arrow_toOptTraces g a
      := by simp [H];
    funext a
    apply Traces.ext
    exact H' a

--TODO: there must be a better way...
theorem Traces.injOpt {ε τ α} (t t': Traces ε τ α)
  : t.toOptTraces = t'.toOptTraces ↔ t = t'
  := ⟨
    t.ext t',
    λH => by rw [H]
  ⟩

theorem Traces.injEq' {ε τ α} (t t': Traces ε τ α)
  : t.terminating = t'.terminating ∧ t.nonterminating = t'.nonterminating ↔ t = t'
  := Iff.trans (OptTraces.injEq' t.toOptTraces t'.toOptTraces) (Traces.injOpt t t')

theorem Traces.injEq_mp {ε τ α} (t t': Traces ε τ α)
  : t.terminating = t'.terminating ∧ t.nonterminating = t'.nonterminating -> t = t'
  := (Traces.injEq' t t').mp

def Traces.map_terminating {ε τ α ε'} (f: ε -> ε') (t: Traces ε τ α)
  : Traces ε' τ α where
  toOptTraces := t.toOptTraces.map_terminating f
  nonempty := t.toOptTraces.map_terminating_nonempty f t.nonempty

theorem Traces.map_terminating_id {ε τ α} (t: Traces α ε τ)
  : t.map_terminating id = t
  := Traces.ext _ _ t.toOptTraces.map_terminating_id

def Traces.map_nonterminating {ε τ α τ'} (f: τ -> τ') (t: Traces ε τ α)
  : Traces ε τ' α where
  toOptTraces := t.toOptTraces.map_nonterminating f
  nonempty := t.toOptTraces.map_nonterminating_nonempty f t.nonempty

theorem Traces.map_nonterminating_id {ε τ α} (t: Traces α ε τ)
  : t.map_nonterminating id = t
  := Traces.ext _ _ t.toOptTraces.map_nonterminating_id

def Traces.map' {ε τ α β} (f: α -> β) (x: Traces ε τ α): Traces ε τ β where
  toOptTraces := x.toOptTraces.map' f
  nonempty := x.toOptTraces.map_nonempty' f x.nonempty

def Traces.pure' {α} (ε τ) [One ε] (a: α): Traces ε τ α where
  toOptTraces := OptTraces.pure' ε τ a
  nonempty := OptTraces.pure_nonempty' ε τ a

def Traces.pure_spec' {α} (ε τ) [One ε] (a: α): Traces.pure' ε τ a = (Trace.pure' ε τ a).toTraces
  := rfl

def Traces.bind' {ε τ α β} [Mul ε] [One ε] [SMul ε τ]
  (x: Traces ε τ α) (f: α -> Traces ε τ β)
  : Traces ε τ β where
  toOptTraces := OptTraces.bind' x.toOptTraces (λa => (f a).toOptTraces)
  nonempty := OptTraces.bind_nonempty
    x.toOptTraces
    (λa => (f a).toOptTraces)
    x.nonempty
    (λa => (f a).nonempty)

instance Traces.instMonad {ε τ} [Mul ε] [One ε] [SMul ε τ]
  : Monad (Traces ε τ) where
  pure := Traces.pure' _ _
  bind := Traces.bind'

instance Traces.instLawfulMonad {ε τ} [M: Monoid ε] [A: MulAction ε τ]
  : LawfulMonad (Traces ε τ) :=
  LawfulMonad.mk' (Traces ε τ)
    (λ_ => Traces.ext _ _ (OptTraces.instLawfulMonad.id_map _))
    (λ_ _ => Traces.ext _ _ (OptTraces.instLawfulMonad.pure_bind _ _))
    (λ_ _ _ => Traces.ext _ _ (OptTraces.instLawfulMonad.bind_assoc _ _ _))

theorem Traces.toOptTraces_bind {ε τ α β}
  [Monoid ε] [MulAction ε τ]
  (x: Traces ε τ α) (f: α -> Traces ε τ β)
  : (x >>= f).toOptTraces = x.toOptTraces >>= (arrow_toOptTraces f)
  := rfl

theorem Traces.arrow_kleisli {ε τ α β γ}
  [Monoid ε] [MulAction ε τ]
  (f: α -> Traces ε τ β) (g: β -> Traces ε τ γ)
  : arrow_toOptTraces (f >=> g)
  = (arrow_toOptTraces f) >=> (arrow_toOptTraces g)
  := rfl
