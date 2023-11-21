import Isotope.StreamAction.Basic

structure StreamMonoidHom
  (α: Type u) (β: Type v) (γ: Type w) (δ: Type x)
  [MulOneClass α] [MulOneClass β]
  [SMul α γ] [FromStream α γ]
  [SMul β δ] [FromStream β δ]
  extends MonoidHom α β
  where
  traceFun: γ -> δ
  map_smul: ∀(a: α) (g: γ), traceFun (a • g) = toFun a • traceFun g

def StreamMonoidHom.id
  {α β}
  [MulOneClass α] [MulOneClass β]
  [SMul α β] [FromStream α β]
  : StreamMonoidHom α α β β where
  toMonoidHom := MonoidHom.id α
  traceFun a := a
  map_smul _ _ := rfl

def StreamMonoidHom.comp
  {α β γ δ}
  [MulOneClass α] [MulOneClass β]
  [SMul α γ] [FromStream α γ]
  [SMul β δ] [FromStream β δ]
  {β' δ'}
  [MulOneClass β']
  [SMul β' δ'] [FromStream β' δ']
  (g: StreamMonoidHom β β' δ δ')
  (f: StreamMonoidHom α β γ δ)
  : StreamMonoidHom α β' γ δ' where
  toMonoidHom := MonoidHom.comp g.toMonoidHom f.toMonoidHom
  traceFun := g.traceFun ∘ f.traceFun
  map_smul a _ := by simp [g.map_smul, f.map_smul]


-- open CategoryTheory

-- -- def StreamMonoidCat := Bundled StreamMonoid
