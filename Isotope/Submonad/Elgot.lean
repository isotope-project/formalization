import Isotope.Submonad.Basic
import Isotope.Elgot.Monad
import Isotope.Utils.Monad

structure ElgotSubmonad (m) [Monad m] [mi: ElgotMonadStructure m]
  extends Submonad m where
  contains_dagger: ∀{α β},
    ∀(f: α -> m (β ⊕ α)),
    (∀(a: α), contains (f a)) ->
    (∀(a: α), contains (mi.iterate f a))

instance ElgotSubmonad.toElgotMonadStructure {m}
  [Monad m] [mi: ElgotMonadStructure m]
  {S: ElgotSubmonad m}
  : ElgotMonadStructure S.members where
  iterate f a := ⟨
      mi.iterate (S.vals f) a,
      S.contains_dagger _ (S.contains_vals f) _⟩

theorem ElgotSubmonad.iterate_def {m}
  [Monad m] [ElgotMonadStructure m]
  {S: ElgotSubmonad m}
  {α β}
  (f: α -> S.members (β ⊕ α))
  (a: α)
  : ElgotMonadStructure.iterate f a = ⟨
      ElgotMonadStructure.iterate (S.vals f) a,
      S.contains_dagger _ (S.contains_vals f) _⟩
  := rfl

theorem ElgotSubmonad.vals_iterate {m}
  [Monad m] [ElgotMonadStructure m]
  {S: ElgotSubmonad m}
  {α β} (f: α -> S.members (β ⊕ α))
  : S.vals (ElgotMonadStructure.iterate f)
  = ElgotMonadStructure.iterate (S.vals f)
  := by
    funext a
    rfl

instance ElgotSubmonad.toElgotMonad {m}
  [Monad m] [LawfulMonad m] [mi: ElgotMonad m]
  {S: ElgotSubmonad m}
  : ElgotMonad S.members where
  fixpoint f := by
    apply Submonad.ext_vals
    rw [
      ElgotSubmonad.vals_iterate,
      <-mi.fixpoint,
      Submonad.vals_kleisli
    ]
    apply congrArg
    funext a
    cases a <;> rfl
  naturality f g := by
    apply Submonad.ext_vals
    rw [
      Submonad.vals_kleisli,
      ElgotSubmonad.vals_iterate,
      ElgotSubmonad.vals_iterate,
      <-mi.naturality,
      Submonad.vals_kleisli,
    ]
    apply congrArg
    apply congrArg
    funext a
    cases a <;> rfl
  codiagonal f := by
    apply Submonad.ext_vals
    rw [
      ElgotSubmonad.vals_iterate,
      ElgotSubmonad.vals_iterate,
      ElgotSubmonad.vals_iterate,
      <-mi.codiagonal,
      Submonad.vals_kleisli
    ]
    apply congrArg
    apply congrArg
    funext a
    cases a <;> rfl
  uniformity f g h H := by
    apply Submonad.ext_vals
    rw [
      ElgotSubmonad.vals_iterate,
      Submonad.vals_kleisli,
      mi.uniformity (S.vals f) (S.vals g) (S.vals h),
      ElgotSubmonad.vals_iterate
    ]
    rw [
      <-Submonad.vals_kleisli h f,
      <-H,
      Submonad.vals_kleisli
    ]
    apply congrArg
    funext a
    cases a <;> rfl
