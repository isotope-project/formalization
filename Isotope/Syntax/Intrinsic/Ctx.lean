import Isotope.Syntax.Ty

abbrev Ctx (T: Type u) := List (Var T)

instance Ctx.instHasLin {T: Type u} [HasLin T]: HasLin (Ctx T) where
  aff Γ := Γ.all HasLin.aff
  rel Γ := Γ.all HasLin.rel

inductive Ctx.split {T: Type u} [HasLin T]: Ctx T → Ctx T → Ctx T → Type u
  | nil: split [] [] []
  | left {Γ Δ Ξ} (v l):  l ≤ v → split Γ Δ Ξ → split (v::Γ) (l::Δ) Ξ
  | right {Γ Δ Ξ} (v r): r ≤ v → split Γ Δ Ξ → split (v::Γ) Δ (r::Ξ)
  | discard {Γ Δ Ξ} (v): HasLin.aff v → split Γ Δ Ξ → split (v::Γ) Δ Ξ
  | dup {Γ Δ Ξ} (v l r): HasLin.rel v → l ≤ v → r ≤ v → split Γ Δ Ξ
    → split (v::Γ) (l::Δ) (r::Ξ)

inductive Ctx.split.strict {T: Type u} [HasLin T]
  : {Γ Δ Ξ: Ctx T} -> split Γ Δ Ξ -> Prop
  | nil: strict nil
  | left (v H): strict H → strict (left v v (le_refl v) H)
  | right (v H): strict H → strict (right v v (le_refl v) H)
  | dup (v Hr H)
    : strict H → strict (dup v v v Hr (le_refl v) (le_refl v) H)

inductive Ctx.ssplit {T: Type u} [HasLin T]: Ctx T → Ctx T → Ctx T → Type u
  | nil: ssplit [] [] []
  | left {Γ Δ Ξ} (v):  ssplit Γ Δ Ξ → ssplit (v::Γ) (v::Δ) Ξ
  | right {Γ Δ Ξ} (v): ssplit Γ Δ Ξ → ssplit (v::Γ) Δ (v::Ξ)
  | dup {Γ Δ Ξ} (v): HasLin.rel v → ssplit Γ Δ Ξ
    → ssplit (v::Γ) (v::Δ) (v::Ξ)

def Ctx.ssplit.toSplit {T: Type u} [HasLin T] {Γ Δ Ξ: Ctx T}
  : ssplit Γ Δ Ξ → split Γ Δ Ξ
  | nil => split.nil
  | left v H => split.left v v (le_refl v) (ssplit.toSplit H)
  | right v H => split.right v v (le_refl v) (ssplit.toSplit H)
  | dup v Hr H =>
    split.dup v v v Hr (le_refl v) (le_refl v) (ssplit.toSplit H)

def Ctx.split.swap {T: Type u} [HasLin T] {Γ Δ Ξ: Ctx T}
  : split Γ Δ Ξ -> split Γ Ξ Δ
  | nil => nil
  | left v l Hl H => right v l Hl (swap H)
  | right v r Hl H => left v r Hl (swap H)
  | discard v Ha Hl => discard v Ha (swap Hl)
  | dup v l r H Hl Hr HΓ
    => dup v r l H Hr Hl (swap HΓ)

def Ctx.ssplit.swap {T: Type u} [HasLin T] {Γ Δ Ξ: Ctx T}
  : ssplit Γ Δ Ξ -> ssplit Γ Ξ Δ
  | nil => nil
  | left v H => right v (swap H)
  | right v H => left v (swap H)
  | dup v Hr H => dup v Hr (swap H)

def Ctx.ssplit.swap_toSplit {T: Type u} [HasLin T] {Γ Δ Ξ: Ctx T}
  : (H: ssplit Γ Δ Ξ) -> H.swap.toSplit = H.toSplit.swap
  | nil => rfl
  | left v H => congrArg _ (swap_toSplit H)
  | right v H => congrArg _ (swap_toSplit H)
  | dup v Hr H => congrArg _ (swap_toSplit H)

def Ctx.split.swap_idem {T: Type u} [HasLin T] {Γ Δ Ξ: Ctx T}
  : Function.LeftInverse (@swap T _ Γ Δ Ξ) (@swap T _ Γ Ξ Δ)
  | nil => rfl
  | left v l Hl HΓ => by simp [swap, swap_idem HΓ]
  | right v r Hr HΓ => by simp [swap, swap_idem HΓ]
  | discard v Ha HΓ => by simp [swap, swap_idem HΓ]
  | dup v l r Har Hl Hr HΓ => by simp [swap, swap_idem HΓ]

def Ctx.ssplit.swap_idem {T: Type u} [HasLin T] {Γ Δ Ξ: Ctx T}
  : Function.LeftInverse (@swap T _ Γ Δ Ξ) (@swap T _ Γ Ξ Δ)
  | nil => rfl
  | left v H => by simp [swap, swap_idem H]
  | right v H => by simp [swap, swap_idem H]
  | dup v Hr H => by simp [swap, swap_idem H]

def Ctx.split.swap_equiv {T: Type u} [HasLin T] (Γ Δ Ξ: Ctx T)
  : Equiv (split Γ Δ Ξ) (split Γ Ξ Δ) where
  toFun := swap
  invFun := swap
  left_inv := swap_idem
  right_inv := swap_idem

def Ctx.ssplit.swap_equiv {T: Type u} [HasLin T] (Γ Δ Ξ: Ctx T)
  : Equiv (ssplit Γ Δ Ξ) (ssplit Γ Ξ Δ) where
  toFun := swap
  invFun := swap
  left_inv := swap_idem
  right_inv := swap_idem

theorem Ctx.split.left_length_decreasing {T: Type u} [HasLin T] {Γ Δ Ξ: Ctx T}
  : split Γ Δ Ξ -> Δ.length ≤ Γ.length
  | nil => le_refl _
  | left _ _ _ HΓ => Nat.succ_le_succ HΓ.left_length_decreasing
  | right _ _ _ HΓ => Nat.le_step HΓ.left_length_decreasing
  | discard _ _ HΓ => Nat.le_step HΓ.left_length_decreasing
  | dup _ _ _ _ _ _ HΓ => Nat.succ_le_succ HΓ.left_length_decreasing

theorem Ctx.ssplit.left_length_decreasing {T: Type u} [HasLin T] {Γ Δ Ξ: Ctx T}
  (H: ssplit Γ Δ Ξ): Δ.length ≤ Γ.length
  := H.toSplit.left_length_decreasing

theorem Ctx.split.right_length_decreasing {T: Type u} [HasLin T] {Γ Δ Ξ: Ctx T}
  (H: split Γ Δ Ξ): Ξ.length ≤ Γ.length
  := H.swap.left_length_decreasing

theorem Ctx.ssplit.right_length_decreasing {T: Type u} [HasLin T] {Γ Δ Ξ: Ctx T}
  (H: ssplit Γ Δ Ξ): Ξ.length ≤ Γ.length
  := H.toSplit.right_length_decreasing

def Ctx.wk {T: Type u} [HasLin T] (Γ Δ: Ctx T) := Ctx.split Γ Δ []

def Ctx.var {T: Type u} [HasLin T] (Γ: Ctx T) (x: Var T) := Ctx.wk Γ [x]

@[match_pattern]
def Ctx.wk.nil {T: Type u} [HasLin T]: @Ctx.wk T _ [] [] := Ctx.split.nil
@[match_pattern]
def Ctx.wk.cons {T: Type u} [HasLin T] {Γ Δ: Ctx T}
  : (v l: Var T) -> (Hl: l ≤ v) -> Ctx.wk Γ Δ -> Ctx.wk (v::Γ) (l::Δ)
  := Ctx.split.left
  @[match_pattern]
def Ctx.wk.scons {T: Type u} [HasLin T] {Γ Δ: Ctx T}
  (v: Var T): Ctx.wk Γ Δ -> Ctx.wk (v::Γ) (v::Δ)
  := Ctx.split.left v v (le_refl v)
@[match_pattern]
def Ctx.wk.discard {T: Type u} [HasLin T] {Γ Δ: Ctx T}
  : (v: Var T) -> (Ha: HasLin.aff v) -> Ctx.wk Γ Δ -> Ctx.wk (v::Γ) Δ
  := Ctx.split.discard

def Ctx.split.left_decompose {T: Type u} [HasLin T] {Γ Δ Ξ: Ctx T}
  : Ctx.split Γ Δ Ξ
  -> (Δ' Ξ': Ctx T) × Ctx.ssplit Γ Δ' Ξ' × Ctx.wk Δ' Δ × Ctx.wk Ξ' Ξ
  | nil => ⟨[], [], ssplit.nil, wk.nil, wk.nil⟩
  | left v l Hl H => let ⟨Δ', Ξ', HΓ, HΔ, HΞ⟩ := left_decompose H;
    ⟨v::Δ', Ξ', ssplit.left v HΓ, wk.cons v l Hl HΔ, HΞ⟩
  | right v r Hl H => let ⟨Δ', Ξ', HΓ, HΔ, HΞ⟩ := left_decompose H;
    ⟨Δ', v::Ξ', ssplit.right v HΓ, HΔ, wk.cons v r Hl HΞ⟩
  | discard v Ha H => let ⟨Δ', Ξ', HΓ, HΔ, HΞ⟩ := left_decompose H;
    ⟨v::Δ', Ξ', ssplit.left v HΓ, wk.discard v Ha HΔ, HΞ⟩
  | dup v l r Hrel Hl Hr H => let ⟨Δ', Ξ', HΓ, HΔ, HΞ⟩ := left_decompose H;
    ⟨v::Δ', v::Ξ', ssplit.dup v Hrel HΓ, wk.cons v l Hl HΔ, wk.cons v r Hr HΞ⟩

def Ctx.split.right_decompose {T: Type u} [HasLin T] {Γ Δ Ξ: Ctx T}
  : Ctx.split Γ Δ Ξ
  -> (Δ' Ξ': Ctx T) × Ctx.ssplit Γ Δ' Ξ' × Ctx.wk Δ' Δ × Ctx.wk Ξ' Ξ
  | nil => ⟨[], [], ssplit.nil, wk.nil, wk.nil⟩
  | left v l Hl H => let ⟨Δ', Ξ', HΓ, HΔ, HΞ⟩ := right_decompose H;
    ⟨v::Δ', Ξ', ssplit.left v HΓ, wk.cons v l Hl HΔ, HΞ⟩
  | right v r Hl H => let ⟨Δ', Ξ', HΓ, HΔ, HΞ⟩ := right_decompose H;
    ⟨Δ', v::Ξ', ssplit.right v HΓ, HΔ, wk.cons v r Hl HΞ⟩
  | discard v Ha H => let ⟨Δ', Ξ', HΓ, HΔ, HΞ⟩ := right_decompose H;
    ⟨Δ', v::Ξ', ssplit.right v HΓ, HΔ, wk.discard v Ha HΞ⟩
  | dup v l r Hrel Hl Hr H => let ⟨Δ', Ξ', HΓ, HΔ, HΞ⟩ := right_decompose H;
    ⟨v::Δ', v::Ξ', ssplit.dup v Hrel HΓ, wk.cons v l Hl HΔ, wk.cons v r Hr HΞ⟩

--TODO: adjust types here
def Ctx.ssplit.distribute_left {T: Type u} [HasLin T] {Γ Γ' Δ Ξ: Ctx T}
  : Ctx.wk Γ' Γ -> Ctx.ssplit Γ Δ Ξ
    -> (Δ' Ξ': Ctx T) × Ctx.ssplit Γ' Δ' Ξ' × Ctx.wk Δ' Δ × Ctx.wk Ξ' Ξ
  | wk.nil, nil => ⟨[], [], ssplit.nil, wk.nil, wk.nil⟩
  | wk.cons _ _ Hl W, left _ S =>
    let ⟨_, _, HΓ, HΔ, HΞ⟩ := distribute_left W S;
    ⟨_, _,
      ssplit.left _ HΓ,
      wk.cons _ _ Hl HΔ,
      HΞ⟩
  | wk.cons _ _ Hl W, right _ S =>
    let ⟨_, _, HΓ, HΔ, HΞ⟩ := distribute_left W S;
    ⟨_, _,
      ssplit.right _ HΓ,
      HΔ,
      wk.cons _ _ Hl HΞ⟩
  | wk.cons _ _ Hl W, dup _ Hrel S =>
    let ⟨_, _, HΓ, HΔ, HΞ⟩ := distribute_left W S;
    ⟨_, _,
      ssplit.dup _ (Var.le.rel Hl Hrel) HΓ,
      wk.cons _ _ Hl HΔ,
      wk.cons _ _ Hl HΞ⟩
  | wk.discard v Ha W, S =>
    let ⟨_, _, HΓ, HΔ, HΞ⟩ := distribute_left W S;
    ⟨_, _, left _ HΓ, wk.discard v Ha HΔ, HΞ⟩

def Ctx.ssplit.distribute_right {T: Type u} [HasLin T] {Γ Γ' Δ Ξ: Ctx T}
  : Ctx.wk Γ' Γ -> Ctx.ssplit Γ Δ Ξ
    -> (Δ' Ξ': Ctx T) × Ctx.ssplit Γ' Δ' Ξ' × Ctx.wk Δ' Δ × Ctx.wk Ξ' Ξ
  | wk.nil, nil => ⟨[], [], ssplit.nil, wk.nil, wk.nil⟩
  | wk.cons _ _ Hl W, left _ S =>
    let ⟨_, _, HΓ, HΔ, HΞ⟩ := distribute_right W S;
    ⟨_, _,
      ssplit.left _ HΓ,
      wk.cons _ _ Hl HΔ,
      HΞ⟩
  | wk.cons _ _ Hl W, right _ S =>
    let ⟨_, _, HΓ, HΔ, HΞ⟩ := distribute_right W S;
    ⟨_, _,
      ssplit.right _ HΓ,
      HΔ,
      wk.cons _ _ Hl HΞ⟩
  | wk.cons _ _ Hl W, dup _ Hrel S =>
    let ⟨_, _, HΓ, HΔ, HΞ⟩ := distribute_right W S;
    ⟨_, _,
      ssplit.dup _ (Var.le.rel Hl Hrel) HΓ,
      wk.cons _ _ Hl HΔ,
      wk.cons _ _ Hl HΞ⟩
  | wk.discard v Ha W, S =>
    let ⟨_, _, HΓ, HΔ, HΞ⟩ := distribute_right W S;
    ⟨_, _, right _ HΓ, HΔ, wk.discard v Ha HΞ⟩

theorem Ctx.wk.length_decreasing {T: Type u} [HasLin T] {Γ Δ: Ctx T} (H: wk Γ Δ)
  : Δ.length ≤ Γ.length
  := Ctx.split.left_length_decreasing H

theorem Ctx.wk.append_false {T: Type u} [HasLin T] {Γ: Ctx T} {A}
  (H: wk Γ (A::Γ)): False
  := have H := H.length_decreasing; by simp_arith at H

theorem Ctx.wk.nil_nil {T: Type u} [HasLin T] {Γ: Ctx T}
  : wk [] Γ -> Γ = []
  | nil => rfl

def Ctx.wk.id {T: Type u} [HasLin T]
  : (Γ: Ctx T) -> Ctx.wk Γ Γ
  | [] => Ctx.split.nil
  | v::Γ => Ctx.split.left v v (le_refl v) (id Γ)

instance Ctx.wk.instInhabitedRefl {T: Type u} [HasLin T] {Γ: Ctx T}
  : Inhabited (Ctx.wk Γ Γ) where
  default := wk.id Γ

instance Ctx.wk.instSubsingletonRefl {T: Type u} [HasLin T] {Γ: Ctx T}
  : Subsingleton (Ctx.wk Γ Γ) where
  allEq := let rec allEq
  : ∀ {Γ: Ctx T} (HΓ: Ctx.wk Γ Γ) (HΓ': Ctx.wk Γ Γ), HΓ = HΓ'
  | [], nil, nil => rfl
  | _, cons _ _ _ HΓ, cons _ _ _ HΓ' => congrArg _ (allEq HΓ HΓ')
  | _, discard _ _ HΓ, _ | _, _, discard _ _ HΓ => HΓ.append_false.elim
  allEq

--TODO: subsingleton to nil --> nil is terminal object
--TODO: subsingleton from nil

def Ctx.wk.comp {T: Type u} [HasLin T] {Γ Δ Ξ: Ctx T}
  : Ctx.wk Γ Δ -> Ctx.wk Δ Ξ -> Ctx.wk Γ Ξ
  | nil, nil => nil
  | cons _ _ Hl HΓ, cons _ _ Hl' HΓ' =>
    cons _ _ (le_trans Hl' Hl) (comp HΓ HΓ')
  | cons _ _ Hl HΓ, discard _ Ha HΓ' =>
    discard _ (Var.le.aff Hl Ha) (comp HΓ HΓ')
  | discard _ Ha HΓ, H =>
    discard _ Ha (comp HΓ H)

def Ctx.wk.comp_id {T: Type u} [HasLin T] {Γ Δ: Ctx T}
  : (H: Ctx.wk Γ Δ) -> (R: Ctx.wk Δ Δ) -> H.comp R = H
  | nil, nil => rfl
  | cons _ _ _ HΓ, cons _ _ _ HΓ' => congrArg _ (comp_id HΓ HΓ')
  | discard _ _ HΓ, HΓ' => congrArg _ (comp_id HΓ HΓ')
  | cons _ _ _ _, discard _ _ HΓ => HΓ.append_false.elim

def Ctx.wk.id_comp {T: Type u} [HasLin T] {Γ Δ: Ctx T}
  : (R: Ctx.wk Γ Γ) -> (H: Ctx.wk Γ Δ) -> R.comp H = H
  | nil, nil => rfl
  | cons _ _ _ HΓ, cons _ _ _ HΓ' => congrArg _ (id_comp HΓ HΓ')
  | cons _ _ _ HΓ, discard _ _ HΓ' => congrArg _ (id_comp HΓ HΓ')
  | discard _ _ HΓ, _ => HΓ.append_false.elim

def Ctx.wk.comp_assoc {T: Type u} [HasLin T] {Γ Δ Ξ Θ: Ctx T}
  : (X: Ctx.wk Γ Δ)
  -> (Y: Ctx.wk Δ Ξ)
  -> (Z: Ctx.wk Ξ Θ)
  -> (X.comp Y).comp Z = X.comp (Y.comp Z)
  | nil, nil, nil => rfl
  | cons _ _ _ X, cons _ _ _ Y, cons _ _ _ Z => congrArg _ (comp_assoc X Y Z)
  | cons _ _ _ X, cons _ _ _ Y, discard _ _ Z => congrArg _ (comp_assoc X Y Z)
  | cons _ _ _ X, discard _ _ Y, Z => congrArg _ (comp_assoc X Y Z)
  | discard _ _ X, Y, Z => congrArg _ (comp_assoc X Y Z)

def Ctx.wk.antisymm {T: Type u} [HasLin T] {Γ Δ: Ctx T}
  : Ctx.wk Γ Δ -> Ctx.wk Δ Γ -> Γ = Δ
  | nil, nil => rfl
  | cons _ _ Hl HΓ, cons _ _ Hl' HΓ' =>
    by rw [antisymm HΓ HΓ', le_antisymm Hl Hl']
  | cons _ _ _ HΓ, discard _ _ HΓ' =>
    have H := le_trans HΓ'.length_decreasing HΓ.length_decreasing;
    by simp_arith at H
  | discard _ _ HΓ, cons _ _ _ HΓ' =>
    have H := le_trans HΓ.length_decreasing HΓ'.length_decreasing;
    by simp_arith at H
  | discard _ _ HΓ, discard _ _ HΓ' =>
    have H := le_trans (Nat.le_step HΓ'.length_decreasing) HΓ.length_decreasing;
    by simp_arith at H

def Ctx.split.right_wk {T: Type u} [HasLin T] {Γ Δ: Ctx T}
  : Ctx.split Γ [] Δ → Ctx.wk Γ Δ
  := swap

def Ctx.wk.right_wk {T: Type u} [HasLin T] {Γ Δ: Ctx T}
  : Ctx.wk Γ Δ → Ctx.split Γ [] Δ
  := Ctx.split.swap

def Ctx.wk.equiv_right {T: Type u} [HasLin T] {Γ Δ: Ctx T}
  : Equiv (Ctx.wk Γ Δ) (Ctx.split Γ [] Δ)
  := Ctx.split.swap_equiv Γ Δ []

-- def Ctx.split.associate_left_tri {T} [HasLin T] {Γ Δ Ξ Θ Φ: Ctx T}:
--   Ctx.split Γ Δ Ξ → Ctx.split Ξ Θ Φ → (Ψ: _) × Ctx.split Γ Ψ Φ × Ctx.split Ψ Δ Θ
--   | H, nil => ⟨Δ, H, wk.refl Δ⟩
--   | _, _ => sorry

def Ctx.var.upgrade {T: Type u} [HasLin T] {Γ: Ctx T} {v v': Var T}
  (H: Γ.var v) (H': v ≥ v'): Γ.var v'
  := Ctx.wk.comp H (Ctx.wk.cons v v' H' (Ctx.wk.nil))
