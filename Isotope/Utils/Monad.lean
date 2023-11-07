theorem kleisli_assoc {m: Type u -> Type v} [Monad m] [LawfulMonad m] {α β γ δ}
  (f: α -> m β) (g: β -> m γ) (h: γ -> m δ)
  : f >=> g >=> h = (f >=> g) >=> h
  := by funext a; unfold Bind.kleisliRight; rw [bind_assoc]

theorem kleisli_pure_comp {m: Type u -> Type v} [Monad m] [LawfulMonad m]
  {α β γ: Type u}
  (f: α -> m β) (g: β -> γ) (a)
  : (f >=> pure ∘ g) a = (g <$> f a)
  := by simp only [Bind.kleisliRight, <-bind_pure_comp]; rfl
