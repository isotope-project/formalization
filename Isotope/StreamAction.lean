import Mathlib.Data.Stream.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.PUnitInstances

class FromStream (α: Type u) (β: Type v) where
  fromStream: (Stream' α) -> β

class StreamAction (α: Type u) (β: Type v)
  [SMul α β]
  extends FromStream α β: Type (max u v)
  where
  fromStream_cons: ∀a f, fromStream (f.cons a) = a • fromStream f

theorem StreamAction.fromStream_ind {α β}
  [SMul α β] [A: StreamAction α β]
  (f: Stream' α)
  : A.fromStream f = f 0 • A.fromStream f.tail
  := by
    rw [<-fromStream_cons]
    apply congr rfl
    funext n
    cases n <;> rfl

instance PUnit.instFromStream {α: Type u}: FromStream α PUnit where
  fromStream _ := ()

instance PUnit.instStreamAction {α: Type u}: StreamAction α PUnit where
  fromStream_cons _ _ := rfl

instance Prod.instFromStream {α β γ} [FromStream α β] [FromStream α γ]
  : FromStream α (β × γ) where
  fromStream f := (FromStream.fromStream f, FromStream.fromStream f)

instance Prod.instStreamAction {α β γ} [SMul α β] [SMul α γ]
  [StreamAction α β] [StreamAction α γ]
  : StreamAction α (β × γ) where
  fromStream_cons a f := by simp only [
    instHSMul, SMul.smul, FromStream.fromStream,
    StreamAction.fromStream_cons
  ]

instance Pi.instFromStream {α: Type u} {I: Type v} {g: I -> Type w}
  [(i: I) -> FromStream α (g i)]
  : FromStream α ((i: I) -> g i) where
  fromStream f _ := FromStream.fromStream f

instance Pi.instStreamAction {α: Type u} {I: Type v} {g: I -> Type w}
  [(i: I) -> SMul α (g i)]
  [(i: I) -> StreamAction α (g i)]
  : StreamAction α ((i: I) -> g i) where
  fromStream_cons a f := by simp only [
    instHSMul, SMul.smul, FromStream.fromStream,
    StreamAction.fromStream_cons
  ]
