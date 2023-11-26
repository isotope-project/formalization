import Mathlib.Data.Set.Image
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

def Submonad.values (m) [mm: Monad m] [LawfulMonad m]: Submonad m where
  contains := Set.range mm.pure
  contains_pure a := ⟨a, rfl⟩
  contains_bind a := λ⟨x, Hx⟩ f Hf =>
    let ⟨y, Hy⟩ := Hf x;
    ⟨y, by simp [<-Hx, Hy]⟩

def Submonad.univ (m) [Monad m]: Submonad m where
  contains := Set.univ
  contains_pure _ := True.intro
  contains_bind _ _ _ _ := True.intro

def Submonad.intersect {m} [Monad m]
  (S S': Submonad m): Submonad m where
  contains a := S.contains a ∧ S'.contains a
  contains_pure a := ⟨S.contains_pure a, S'.contains_pure a⟩
  contains_bind a Ha f Hf := ⟨
    S.contains_bind a Ha.1 f (λa => (Hf a).1),
    S'.contains_bind a Ha.2 f (λa => (Hf a).2)
  ⟩

theorem Submonad.ext {m} [Monad m]
  {S S': Submonad m}
  (H: ∀{α}, @Submonad.contains m _ S α = S'.contains)
  : S = S'
  := by cases S; cases S'; simp only [mk.injEq]; funext α; exact H

def Submonad.members {m: Type u -> Type v}
  [Monad m] (S: Submonad m) (α: Type u): Type v
  := { a: m α // S.contains a }

@[simp]
def Submonad.vals {m} [Monad m] (S: Submonad m)
  {α β}
  (f: α -> S.members β)
  (a: α)
  : m β
  := (f a).1

theorem Submonad.contains_vals {m} [Monad m] (S: Submonad m)
  {α β}
  (f: α -> S.members β)
  (a: α)
  : S.contains (S.vals f a)
  := (f a).2

theorem Submonad.ext_vals {m} [Monad m] (S: Submonad m)
  {α β}
  {f g: α -> S.members β}
  (H: S.vals f = S.vals g)
  : f = g
  := by funext a; apply Subtype.ext; exact congrFun H a

instance Submonad.toMonad {m}
  [Monad m] {S: Submonad m}: Monad (S.members) where
  pure a := ⟨pure a, S.contains_pure a⟩
  bind a f := ⟨a.1 >>= (S.vals f),
    S.contains_bind _ a.2 _ (S.contains_vals f)⟩

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
  : a >>= f = ⟨
      a.1 >>= S.vals f,
      S.contains_bind _ a.2 _ (S.contains_vals f)
    ⟩
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
  [LawfulMonad m]
  {S: Submonad m}: LawfulMonad (S.members)
  := LawfulMonad.mk'
    S.members
    (λx => Subtype.ext (by simp [map_subtype]))
    (λx f => Subtype.ext (by simp [S.bind_def, S.pure_def]))
    (λx f g =>  Subtype.ext (by simp only [S.bind_def]; rw [bind_assoc]; rfl))

theorem Submonad.bind_vals {m}
  [Monad m]
  {S: Submonad m}
  {α β}
  (f: α -> S.members β)
  (a: S.members α)
  : a.1 >>= S.vals f = (a >>= f).1
  := rfl

theorem Submonad.vals_kleisli {m}
  [Monad m]
  {S: Submonad m}
  {α β γ}
  (f: α -> S.members β)
  (g: β -> S.members γ)
  : S.vals (f >=> g) = S.vals f >=> S.vals g
  := by
    funext a
    rfl
