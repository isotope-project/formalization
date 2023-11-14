import Mathlib.Algebra.Group.Defs
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Lattice

inductive Trace (ε: Type u1) (τ: Type u2) (α: Type u3): Type (max u1 (max u2 u3))
  | terminating (a: α) (e: ε)
  | nonterminating (t: τ)

def Trace.prepend {ε τ α} [Mul ε] [SMul ε τ] (e: ε): Trace ε τ α -> Trace ε τ α
  | terminating a e' => terminating a (e * e')
  | nonterminating t => nonterminating (e • t)

def Trace.append {ε τ α} [Mul ε] [SMul ε τ] (e: ε): Trace ε τ α -> Trace ε τ α
  | terminating a e' => terminating a (e' * e)
  | nonterminating t => nonterminating t

def Terminates: Type := Empty

instance {ε} [Monoid ε]: MulAction ε Terminates where
  smul := λ_ t => match t with .
  one_smul := λt => match t with .
  mul_smul := λ_ _ t => match t with .

def Trace.map' {ε τ α β} (f: α -> β): Trace ε τ α -> Trace ε τ β
  | terminating a e => terminating (f a) e
  | nonterminating t => nonterminating t

def Trace.pure' {α} (ε τ) [One ε] (a: α): Trace ε τ α
  := terminating a 1

def Trace.bind' {ε τ α β} [Mul ε] [One ε] [SMul ε τ] (x: Trace ε τ α) (f: α -> Trace ε τ β)
  : Trace ε τ β
  := match x with
  | terminating a e =>
    match f a with
    | terminating b e' => terminating b (e * e')
    | nonterminating t => nonterminating (e • t)
  | nonterminating t => nonterminating t

instance Trace.instMonad {ε τ} [Mul ε] [One ε] [SMul ε τ]: Monad (Trace ε τ) where
  pure := Trace.pure' _ _
  bind := Trace.bind'

def Trace.seqLeft' {ε τ α β} [Mul ε] [One ε] [SMul ε τ]: Trace ε τ α -> Trace ε τ β -> Trace ε τ α
  | terminating a e, terminating _ e' => terminating a (e * e')
  | nonterminating t, _ => nonterminating t
  | terminating _ e, nonterminating t => nonterminating (e • t)

def Trace.seqRight' {ε τ α β} [Mul ε] [One ε] [SMul ε τ]: Trace ε τ α -> Trace ε τ β -> Trace ε τ β
  | terminating _ e, terminating b e' => terminating b (e * e')
  | nonterminating t, _ => nonterminating t
  | terminating _ e, nonterminating t => nonterminating (e • t)

theorem Trace.seqLeft_spec {ε τ α β} [Monoid ε] [SMul ε τ]
  (l: Trace ε τ α) (r: Trace ε τ β)
  : l <* r = l.seqLeft' r
  := by cases l <;> cases r <;> simp [SeqLeft.seqLeft, bind', seqLeft', pure']

theorem Trace.seqRight_spec {ε τ α β} [Monoid ε] [SMul ε τ]
  (l: Trace ε τ α) (r: Trace ε τ β)
  : l <* r = l.seqLeft' r
  := by cases l <;> cases r <;> simp [SeqLeft.seqLeft, bind', seqLeft', pure']

instance Trace.instLawfulMonad {ε τ} [M: Monoid ε] [MulAction ε τ]: LawfulMonad (Trace ε τ)
  := LawfulMonad.mk' _
    (λx => by cases x <;> simp [Functor.map, bind', pure'])
    (λx f => by simp only [bind, bind', pure, pure']; split <;> simp [*])
    (λx f g => by
      cases x <;> simp only [bind, bind']
      case terminating a e =>
        generalize Hy: f a = y;
        cases y <;> simp only []
        case terminating b e' =>
          generalize Hz: g b = z;
          cases z <;> simp [MulAction.mul_smul, M.mul_assoc]
    )

def TraceSet (ε τ α) := Set (Trace ε τ α)

instance TraceSet.instEmptyCollection {ε τ α}: EmptyCollection (TraceSet ε τ α)
  := Set.instEmptyCollectionSet

instance TraceSet.instSingleton {ε τ α}: Singleton (Trace ε τ α) (TraceSet ε τ α)
  := Set.instSingletonSet

instance TraceSet.instMembership {ε τ α}: Membership (Trace ε τ α) (TraceSet ε τ α)
  := Set.instMembershipSet

def TraceSet.Nonempty {ε τ α}: TraceSet ε τ α -> Prop := Set.Nonempty

def TraceSet.prepend {ε τ α} [Mul ε] [SMul ε τ] (e: ε) (t: TraceSet ε τ α): TraceSet ε τ α
  := Set.image (Trace.prepend e) t

def TraceSet.append {ε τ α} [Mul ε] [SMul ε τ] (e: ε) (t: TraceSet ε τ α): TraceSet ε τ α
  := Set.image (Trace.append e) t

def TraceSet.pure' {α} (ε τ) [One ε] (a: α): TraceSet ε τ α
  := { Trace.pure' ε τ a }

def Trace.bind_opt {ε τ α β} [Mul ε] [One ε] [SMul ε τ] (x: Trace ε τ α) (f: α -> TraceSet ε τ β)
  : TraceSet ε τ β
  := match x with
    | Trace.terminating a e => (f a).prepend e
    | Trace.nonterminating t => { Trace.nonterminating t }

def TraceSet.bind' {ε τ α β} [Mul ε] [One ε] [SMul ε τ] (xs: TraceSet ε τ α) (f: α -> TraceSet ε τ β)
  : TraceSet ε τ β
  := ⋃ x ∈ xs, x.bind_opt f

instance TraceSet.instMonad {ε τ} [Mul ε] [One ε] [SMul ε τ]: Monad (TraceSet ε τ) where
  pure := TraceSet.pure' _ _
  bind := TraceSet.bind'
