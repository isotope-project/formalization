import Mathlib.Init.Set
import Mathlib.Data.Subtype
import Std.Classes.LawfulMonad

structure Submonad (m) [Monad m] where
  contains: ∀{α}, Set (m α)
  contains_pure: ∀{α}, ∀a: α, contains (pure a)
  contains_bind: ∀{α β},
    ∀a: m α, contains a ->
    (f: α -> m β) ->
    (∀a: α, contains (f a)) ->
    (contains (a >>= f))

theorem Submonad.ext {m} [Monad m]
  {S S': Submonad m}
  (H: ∀{α}, @Submonad.contains m _ S α = S'.contains)
  : S = S'
  := by cases S; cases S'; simp only [mk.injEq]; funext α; exact H

def Submonad.members {m: Type u -> Type v}
  [Monad m] (S: Submonad m) (α: Type u): Type v
  := { a: m α // S.contains a }

instance Submonad.toMonad {m}
  [Monad m] {S: Submonad m}: Monad (S.members) where
  pure a := ⟨pure a, S.contains_pure a⟩
  bind a f := ⟨a.1 >>= (λa => (f a).1),
    S.contains_bind _ a.2 _ (λa => (f a).2)⟩

theorem Submonad.pure_def {m}
  [Monad m] {S: Submonad m}
  {α}
  (a: α)
  : (@Submonad.toMonad m _ S).pure a = ⟨pure a, S.contains_pure a⟩
  := rfl

theorem Submonad.bind_def {m}
  [Monad m] {S: Submonad m}
  {α β}
  (a: S.members α)
  (f: α -> S.members β)
  : a >>= f = ⟨a.1 >>= (λa => (f a).1),
    S.contains_bind _ a.2 _ (λa => (f a).2)⟩
  := rfl

theorem Submonad.contains_map {m}
  [Monad m] [HL: LawfulMonad m] {S: Submonad m}
  {α β}
  (f: α -> β)
  (a: m α)
  (H: S.contains a)
  : S.contains (f <$> a)
  := by
    rw [<-HL.bind_pure_comp]
    exact
      S.contains_bind _ H _
      (λa => S.contains_pure (f a))

theorem Submonad.contains.map {m}
  [Monad m] [LawfulMonad m] {S: Submonad m}
  {α β a}
  (H: S.contains a)
  (f: α -> β)
  : S.contains (f <$> a)
  := S.contains_map f a H

theorem Submonad.map_subtype {m}
  [Monad m] [H: LawfulMonad m] {S: Submonad m}
  {α β}
  (f: α -> β)
  (a: S.members α)
  : f <$> a = ⟨f <$> a.1, a.2.map f⟩
  := by
    apply Subtype.ext
    simp only []
    rw [<-H.bind_pure_comp]
    rfl

instance Submonad.toLawfulMonad {m}
  [Monad m]
  [H: LawfulMonad m]
  {S: Submonad m}: LawfulMonad (S.members)
  := LawfulMonad.mk'
    S.members
    (λx => Subtype.ext (by simp only [map_subtype, H.id_map]))
    (λx f => Subtype.ext (by simp only [S.bind_def, S.pure_def, H.pure_bind]))
    (λx f g =>  Subtype.ext (by simp only [S.bind_def, H.bind_assoc]))
