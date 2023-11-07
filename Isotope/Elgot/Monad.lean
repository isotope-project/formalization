import Mathlib.Data.Sum.Basic

class ElgotMonadStructure (m: Type u -> Type v): Type (max (u + 1) v) where
  iterate: ∀{α β: Type u}, (α -> m (β ⊕ α)) -> α -> m β
  -- diverge (α: Type u) [Monad m]: m α := iterate (pure ∘ Sum.inr) PUnit.unit

class ElgotMonad (m: Type u -> Type v) [Monad m] [LawfulMonad m]
  extends ElgotMonadStructure m
  where
  fixpoint: ∀{α β: Type u}
    (f: α -> m (β ⊕ α)),
    f >=> Sum.elim pure (iterate f) = iterate f
  naturality: ∀{α β γ: Type u}
    (f: α -> m (β ⊕ α))
    (g: β -> m γ),
    iterate (f >=> Sum.elim (g >=> (pure ∘ Sum.inl)) (pure ∘ Sum.inr))
      = (iterate f) >=> g
  -- Derivable from fixpoint + naturality + codiagonal + uniformity
  -- by lemma 31 of Goncharov and Schröder (2018, Guarded Traced Categories)
  -- dinaturality: ∀{α β γ: Type u}
  --   (g: α -> m (β ⊕ γ))
  --   (h: γ -> m (β ⊕ α)),
  --   iterate (g >=> Sum.elim (pure ∘ Sum.inl) h)
  --     = g >=> Sum.elim pure (iterate (h >=> Sum.elim (pure ∘ Sum.inl) g))
  codiagonal: ∀{α β: Type u}
    (f: α -> m ((β ⊕ α) ⊕ α)),
    iterate (f >=> Sum.elim pure (pure ∘ Sum.inr)) = iterate (iterate f)
  uniformity: ∀{α β γ: Type u}
    (f: α -> m (β ⊕ α))
    (g: γ -> m (β ⊕ γ))
    (h: γ -> m α),
    g >=> Sum.elim (pure ∘ Sum.inl) (h >=> (pure ∘ Sum.inr))
      = h >=> f
    -> iterate g
      = h >=> iterate f

class IterativeMonad (m: Type u -> Type v) [Monad m] [LawfulMonad m]
  extends ElgotMonad m
  where
  uniqueness: ∀{α β: Type u}
    (f: α -> m (β ⊕ α))
    (g: α -> m β),
    f >=> Sum.elim pure (g) = g
      -> g = iterate f

-- Proposition 18 of Levy and Goncharov
-- (2012, Coinductive Resumption Monads: Guarded Iterative and Guarded Elgot)
-- def IterativeMonad.mk' (m: Type u -> Type v) [Monad m] [LawfulMonad m]
--   (iterate: ∀{α β: Type u}, (α -> m (β ⊕ α)) -> α -> m β)
--   (fixpoint: ∀{α β: Type u}
--     (f: α -> m (β ⊕ α)),
--     f >=> Sum.elim pure (iterate f) = iterate f)
--   (uniqueness: ∀{α β: Type u}
--     (f: α -> m (β ⊕ α))
--     (g: α -> m β),
--     f >=> Sum.elim pure (g) = g
--       -> g = iterate f)
--   : IterativeMonad m where
--   iterate := iterate
--   fixpoint := fixpoint
--   naturality := sorry
--   dinaturality := sorry
--   uniformity := sorry
--   uniqueness := uniqueness
