import Mathlib.Data.Stream.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.PUnitInstances
-- import Mathlib.CategoryTheory.ConcreteCategory.BundledHom

class FromStream (α: Type u) (β: Type v) where
  fromStream: (Stream' α) -> β

class StreamAction (α: Type u) (β: Type v) [SMul α β]
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

instance Prod.instStreamAction {α β γ}
  [SMul α β] [StreamAction α β] [SMul α γ] [StreamAction α γ]
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

structure StreamActionHom (α: Type u) (β: Type v)
  [SMul α β]
  [FromStream α β]
  (γ: Type w) [SMul α γ] [FromStream α γ]
  where
  toFun: β -> γ
  map_smul: ∀(a: α) b, toFun (a • b) = a • toFun b

def StreamActionHom.id (α: Type u) (β: Type v)
  [SMul α β]
  [FromStream α β]
  : StreamActionHom α β β where
  toFun b := b
  map_smul _ _ := rfl

def StreamActionHom.comp
  {α β γ δ}
  [SMul α β]
  [FromStream α β]
  [SMul α γ]
  [FromStream α γ]
  [SMul α δ]
  [FromStream α δ]
  (habg: StreamActionHom α β γ)
  (hagd: StreamActionHom α γ δ)
  : StreamActionHom α β δ where
  toFun := hagd.toFun ∘ habg.toFun
  map_smul a b := by
    simp only [habg.map_smul, hagd.map_smul, Function.comp_apply, SMul.smul]

instance StreamActionHom.instFunLike {α β γ}
  [SMul α β] [FromStream α β]
  [SMul α γ] [FromStream α γ]
  : FunLike (StreamActionHom α β γ) β (λ_ => γ) where
  coe := toFun
  coe_injective' := by
    intro f g h
    cases f
    cases g
    cases h
    rfl

-- open CategoryTheory

-- def StreamActionCat (α: Type u) := Bundled (StreamAction α)

-- instance StreamActionCat.instCategory {α}
--   : Category (StreamActionCat α) := sorry

-- instance StreamActionCat.concreteCategory {α}
--   : ConcreteCategory (StreamActionCat α)
--   := by simp only [StreamActionCat]; infer_instance
