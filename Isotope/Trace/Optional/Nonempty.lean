import Isotope.Trace.Optional.Basic

def OptTraces.is_nonempty {ε τ α} (t: OptTraces ε τ α)
  := (∃a e, t.terminating a e) ∨ (∃e, t.nonterminating e)

def Trace.toOptTraces_is_nonempty {ε τ α}
  : (t: Trace ε τ α) -> t.toOptTraces.is_nonempty
  | terminating a e => Or.inl ⟨a, e, rfl, rfl⟩
  | nonterminating t => Or.inr ⟨t, rfl⟩

theorem OptTraces.map_terminating_nonempty {ε τ α ε'} (f: ε -> ε') (t: OptTraces ε τ α)
  : t.is_nonempty -> (t.map_terminating f).is_nonempty
  | Or.inl ⟨a, e, H⟩ => Or.inl ⟨a, f e, e, H, rfl⟩
  | Or.inr H => Or.inr H

theorem OptTraces.map_nonterminating_nonempty
  {ε τ α τ'} (f: τ -> τ') (t: OptTraces ε τ α)
  : t.is_nonempty -> (t.map_nonterminating f).is_nonempty
  | Or.inl H => Or.inl H
  | Or.inr ⟨t, H⟩ => Or.inr ⟨f t, t, H, rfl⟩

theorem OptTraces.map_nonempty' {ε τ α β} (f: α -> β) (t: OptTraces ε τ α)
  : t.is_nonempty -> (t.map' f).is_nonempty
  | Or.inl ⟨a, e, H⟩ => Or.inl ⟨f a, e, a, H, rfl⟩
  | Or.inr H => Or.inr H

theorem OptTraces.pure_nonempty' (ε τ) [One ε] (a: α)
  : (OptTraces.pure' ε τ a).is_nonempty
  := Or.inl ⟨a, 1, rfl, rfl⟩

theorem OptTraces.bind_nonempty {ε τ α β} [Mul ε] [One ε] [SMul ε τ]
  (x: OptTraces ε τ α) (f: α -> OptTraces ε τ β)
  (Hx: x.is_nonempty)
  (Hf: ∀a, (f a).is_nonempty)
  : (x.bind' f).is_nonempty :=
  match Hx with
  | Or.inl ⟨a, e, Hae⟩ => match (Hf a) with
    | Or.inl ⟨b, e', H⟩ => Or.inl ⟨b, e * e', a, e, e', Hae, H, rfl⟩
    | Or.inr ⟨t, H⟩ => Or.inr ⟨e • t, Or.inr ⟨a, e, t, Hae, H, rfl⟩⟩
  | Or.inr ⟨t, H⟩ => Or.inr ⟨t, Or.inl H⟩
