import Isotope.Syntax.Ty

namespace NamedList

structure Var (T: Type u) extends Transparency where
  name: String
  ty: T

instance Var.instHasLin {T} [HasLin T]: HasLin (Var T) where
  aff v := v.aff && HasLin.aff v.ty
  rel v := v.rel && HasLin.rel v.ty

instance Var.instPartialOrder {T}: PartialOrder (Var T) where
  le l r := l.name = r.name ∧ l.ty = r.ty ∧ l.toTransparency ≤ r.toTransparency
  le_refl := by simp [le_refl]
  le_trans _ _ _
    | ⟨Hn, HA, Ht⟩, ⟨Hn', HA', Ht'⟩
    => ⟨Hn.trans Hn', HA.trans HA', le_trans Ht Ht'⟩
  le_antisymm x x' H H'
    := mk.injEq _ _ _ _ _ _ ▸ ⟨le_antisymm H.2.2 H'.2.2, H.1, H.2.1⟩

theorem Var.le.aff {T} [HasLin T] {l r: Var T}
  : l ≤ r → HasLin.aff l → HasLin.aff r
  | ⟨He, Ht⟩ => by
    simp only [HasLin.aff, He, Bool.and_eq_true, and_imp]
    intro H H';
    exact ⟨Ht.2.1 H, Ht.1 ▸ H'⟩

theorem Var.le.rel {T} [HasLin T] {l r: Var T}
  : l ≤ r → HasLin.rel l → HasLin.rel r
  | ⟨He, Ht⟩ => by
    simp only [HasLin.rel, He, Bool.and_eq_true, and_imp]
    intro H H';
    exact ⟨Ht.2.2 H, Ht.1 ▸ H'⟩

--TODO: add context well-formedness condition? (no repeated names)
--TODO: contexts as finite functions Name -> Var? could be !FUN!
--Can be equipped with a separate "domain"?
--In this case can define separation-style judgements on domains...
abbrev Ctx (T: Type u) := List (Var T)

inductive Ctx.has_name {T: Type u}: Ctx T -> String -> Prop
  | head (q n A) (Γ: Ctx T): Ctx.has_name (⟨q, n, A⟩::Γ) n
  | tail v (Γ: Ctx T) (m: String): Ctx.has_name Γ m -> Ctx.has_name (v::Γ) m

instance Ctx.instHasLin {T: Type u} [HasLin T]: HasLin (Ctx T) where
  aff Γ := Γ.all HasLin.aff
  rel Γ := Γ.all HasLin.rel

inductive Ctx.split {T: Type u} [HasLin T]: Ctx T → Ctx T → Ctx T → Type u
  | nil: split [] [] []
  | left {Γ Δ Ξ} {v l}:  l ≤ v → split Γ Δ Ξ → split (v::Γ) (l::Δ) Ξ
  | right {Γ Δ Ξ} {v r}: r ≤ v → split Γ Δ Ξ → split (v::Γ) Δ (r::Ξ)
  | discard {Γ Δ Ξ} {v}: HasLin.aff v → split Γ Δ Ξ → split (v::Γ) Δ Ξ
  | dup {Γ Δ Ξ} {v l r}: HasLin.rel v → l ≤ v → r ≤ v → split Γ Δ Ξ
    → split (v::Γ) (l::Δ) (r::Ξ)

@[match_pattern]
def Ctx.split.sleft {T: Type u} [HasLin T] {Γ Δ Ξ: Ctx T}
  (v: Var T): split Γ Δ Ξ -> split (v::Γ) (v::Δ) Ξ
  := left (le_refl v)
@[match_pattern]
def Ctx.split.sright {T: Type u} [HasLin T] {Γ Δ Ξ: Ctx T}
  (v: Var T): split Γ Δ Ξ -> split (v::Γ) Δ (v::Ξ)
  := right (le_refl v)
@[match_pattern]
def Ctx.split.sdup {T: Type u} [HasLin T] {Γ Δ Ξ: Ctx T}
  {v} (Hv: HasLin.rel v): split Γ Δ Ξ -> split (v::Γ) (v::Δ) (v::Ξ)
  := dup Hv (le_refl v) (le_refl v)

inductive Ctx.ssplit {T: Type u} [HasLin T]: Ctx T → Ctx T → Ctx T → Type u
  | nil: ssplit [] [] []
  | left {Γ Δ Ξ} {v l}:  l ≤ v → ssplit Γ Δ Ξ → ssplit (v::Γ) (l::Δ) Ξ
  | right {Γ Δ Ξ} {v r}: r ≤ v → ssplit Γ Δ Ξ → ssplit (v::Γ) Δ (r::Ξ)
  | dup {Γ Δ Ξ} {v l r}: HasLin.rel v → l ≤ v → r ≤ v → ssplit Γ Δ Ξ
    → ssplit (v::Γ) (l::Δ) (r::Ξ)

@[match_pattern]
def Ctx.ssplit.sleft {T: Type u} [HasLin T] {Γ Δ Ξ: Ctx T}
  (v: Var T): ssplit Γ Δ Ξ -> ssplit (v::Γ) (v::Δ) Ξ
  := left (le_refl v)
@[match_pattern]
def Ctx.ssplit.sright {T: Type u} [HasLin T] {Γ Δ Ξ: Ctx T}
  (v: Var T): ssplit Γ Δ Ξ -> ssplit (v::Γ) Δ (v::Ξ)
  := right (le_refl v)
@[match_pattern]
def Ctx.ssplit.sdup {T: Type u} [HasLin T] {Γ Δ Ξ: Ctx T}
  {v} (Hv: HasLin.rel v): ssplit Γ Δ Ξ -> ssplit (v::Γ) (v::Δ) (v::Ξ)
  := dup Hv (le_refl v) (le_refl v)

def Ctx.ssplit.toSplit {T: Type u} [HasLin T] {Γ Δ Ξ: Ctx T}
  : ssplit Γ Δ Ξ → split Γ Δ Ξ
  | nil => split.nil
  | left Hl H => split.left Hl (ssplit.toSplit H)
  | right Hr H => split.right Hr (ssplit.toSplit H)
  | dup Hrel Hl Hr H => split.dup Hrel Hl Hr (ssplit.toSplit H)

def Ctx.split.swap {T: Type u} [HasLin T] {Γ Δ Ξ: Ctx T}
  : split Γ Δ Ξ -> split Γ Ξ Δ
  | nil => nil
  | left Hl H => right Hl (swap H)
  | right Hl H => left Hl (swap H)
  | discard Ha Hl => discard Ha (swap Hl)
  | dup H Hl Hr HΓ
    => dup H Hr Hl (swap HΓ)

def Ctx.ssplit.swap {T: Type u} [HasLin T] {Γ Δ Ξ: Ctx T}
  : ssplit Γ Δ Ξ -> ssplit Γ Ξ Δ
  | nil => nil
  | left Hl H => right Hl (swap H)
  | right Hr H => left Hr (swap H)
  | dup Hrel Hl Hr H => dup Hrel Hr Hl (swap H)

def Ctx.ssplit.swap_toSplit {T: Type u} [HasLin T] {Γ Δ Ξ: Ctx T}
  : (H: ssplit Γ Δ Ξ) -> H.swap.toSplit = H.toSplit.swap
  | nil => rfl
  | left _ H => congrArg _ (swap_toSplit H)
  | right _ H => congrArg _ (swap_toSplit H)
  | dup _ _ _ H => congrArg _ (swap_toSplit H)

def Ctx.split.swap_idem {T: Type u} [HasLin T] {Γ Δ Ξ: Ctx T}
  : Function.LeftInverse (@swap T _ Γ Δ Ξ) (@swap T _ Γ Ξ Δ)
  | nil => rfl
  | left _ HΓ => by simp [swap, swap_idem HΓ]
  | right _ HΓ => by simp [swap, swap_idem HΓ]
  | discard _ HΓ => by simp [swap, swap_idem HΓ]
  | dup _ _ _ HΓ => by simp [swap, swap_idem HΓ]

def Ctx.ssplit.swap_idem {T: Type u} [HasLin T] {Γ Δ Ξ: Ctx T}
  : Function.LeftInverse (@swap T _ Γ Δ Ξ) (@swap T _ Γ Ξ Δ)
  | nil => rfl
  | left _ H => by simp [swap, swap_idem H]
  | right _ H => by simp [swap, swap_idem H]
  | dup _ _ _ H => by simp [swap, swap_idem H]

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
  | left _ HΓ => Nat.succ_le_succ HΓ.left_length_decreasing
  | right _ HΓ => Nat.le_step HΓ.left_length_decreasing
  | discard _ HΓ => Nat.le_step HΓ.left_length_decreasing
  | dup _ _ _ HΓ => Nat.succ_le_succ HΓ.left_length_decreasing

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
  : {v l: Var T} -> (Hl: l ≤ v) -> Ctx.wk Γ Δ -> Ctx.wk (v::Γ) (l::Δ)
  := Ctx.split.left
  @[match_pattern]
def Ctx.wk.scons {T: Type u} [HasLin T] {Γ Δ: Ctx T}
  (v: Var T): Ctx.wk Γ Δ -> Ctx.wk (v::Γ) (v::Δ)
  := Ctx.split.left (le_refl v)
@[match_pattern]
def Ctx.wk.discard {T: Type u} [HasLin T] {Γ Δ: Ctx T}
  : {v: Var T} -> (Ha: HasLin.aff v) -> Ctx.wk Γ Δ -> Ctx.wk (v::Γ) Δ
  := Ctx.split.discard

@[match_pattern]
def Ctx.var.head {T: Type u} [HasLin T] {Γ: Ctx T}
  {v v': Var T} (H: v ≥ v') (W: Γ.wk []): Ctx.var (v::Γ) v'
  := Ctx.wk.cons H W
@[match_pattern]
def Ctx.var.shead {T: Type u} [HasLin T] {Γ: Ctx T}
  (v: Var T) (W: Γ.wk []): Ctx.var (v::Γ) v
  := Ctx.wk.scons v W
@[match_pattern]
def Ctx.var.tail {T: Type u} [HasLin T] {Γ: Ctx T}
  {v a: Var T} (W: Γ.var v) (Ha: HasLin.aff a): Ctx.var (a::Γ) v
  := Ctx.wk.discard Ha W

def Ctx.split.left_decompose {T: Type u} [HasLin T] {Γ Δ Ξ: Ctx T}
  : Ctx.split Γ Δ Ξ
  -> (Δ': Ctx T) × Ctx.ssplit Γ Δ' Ξ × Ctx.wk Δ' Δ
  | nil => ⟨[], ssplit.nil, wk.nil⟩
  | left Hl H => let ⟨Δ', HΓ, HΔ⟩ := left_decompose H;
    ⟨_::Δ', ssplit.left Hl HΓ, wk.scons _ HΔ⟩
  | right Hr H => let ⟨Δ', HΓ, HΔ⟩ := left_decompose H;
    ⟨Δ', ssplit.right Hr HΓ, HΔ⟩
  | discard Ha H => let ⟨Δ', HΓ, HΔ⟩ := left_decompose H;
    ⟨_::Δ', ssplit.sleft _ HΓ, wk.discard Ha HΔ⟩
  | dup Hrel Hl Hr H => let ⟨Δ', HΓ, HΔ⟩ := left_decompose H;
    ⟨_::Δ', ssplit.dup Hrel Hl Hr HΓ, wk.scons _ HΔ⟩

def Ctx.split.right_decompose {T: Type u} [HasLin T] {Γ Δ Ξ: Ctx T}
  : Ctx.split Γ Δ Ξ
  -> (Ξ': Ctx T) × Ctx.ssplit Γ Δ Ξ' × Ctx.wk Ξ' Ξ
  | nil => ⟨[], ssplit.nil, wk.nil⟩
  | left Hl H => let ⟨Ξ', HΓ, HΞ⟩ := right_decompose H;
    ⟨Ξ', ssplit.left Hl HΓ, HΞ⟩
  | right Hr H => let ⟨Ξ', HΓ, HΞ⟩ := right_decompose H;
    ⟨_::Ξ', ssplit.right Hr HΓ, wk.scons _ HΞ⟩
  | discard Ha H => let ⟨Ξ', HΓ, HΞ⟩ := right_decompose H;
    ⟨_::Ξ', ssplit.right (le_refl _) HΓ, wk.discard Ha HΞ⟩
  | dup Hrel Hl Hr H => let ⟨Ξ', HΓ, HΞ⟩ := right_decompose H;
    ⟨_::Ξ', ssplit.dup Hrel Hl Hr HΓ, wk.scons _ HΞ⟩

def Ctx.ssplit.distribute_left {T: Type u} [HasLin T] {Γ Γ' Δ Ξ: Ctx T}
  : Ctx.wk Γ' Γ -> Ctx.ssplit Γ Δ Ξ
    -> (Δ': Ctx T) × Ctx.ssplit Γ' Δ' Ξ × Ctx.wk Δ' Δ
  | wk.nil, nil => ⟨[], ssplit.nil, wk.nil⟩
  | wk.cons Hc W, left Hl S =>
    let ⟨_, HΓ, HΔ⟩ := distribute_left W S;
    ⟨_,
      ssplit.left (le_trans Hl Hc) HΓ,
      wk.scons _ HΔ⟩
  | wk.cons Hc W, right Hr S =>
    let ⟨_, HΓ, HΔ⟩ := distribute_left W S;
    ⟨_,
      ssplit.right (le_trans Hr Hc) HΓ,
      HΔ⟩
  | wk.cons Hc W, dup Hrel Hl Hr S =>
    let ⟨_, HΓ, HΔ⟩ := distribute_left W S;
    ⟨_,
      ssplit.dup (Var.le.rel Hc Hrel) (le_trans Hl Hc) (le_trans Hr Hc) HΓ,
      wk.scons _ HΔ⟩
  | wk.discard Ha W, S =>
    let ⟨_, HΓ, HΔ⟩ := distribute_left W S;
    ⟨_, sleft _ HΓ, wk.discard Ha HΔ⟩

def Ctx.ssplit.distribute_right {T: Type u} [HasLin T] {Γ Γ' Δ Ξ: Ctx T}
  : Ctx.wk Γ' Γ -> Ctx.ssplit Γ Δ Ξ
    -> (Ξ': Ctx T) × Ctx.ssplit Γ' Δ Ξ' × Ctx.wk Ξ' Ξ
  | wk.nil, nil => ⟨[], ssplit.nil, wk.nil⟩
  | wk.cons Hc W, left Hl S =>
    let ⟨_, HΓ, HΞ⟩ := distribute_right W S;
    ⟨_,
      ssplit.left (le_trans Hl Hc) HΓ,
      HΞ⟩
  | wk.cons Hc W, right Hr S =>
    let ⟨_, HΓ, HΞ⟩ := distribute_right W S;
    ⟨_,
      ssplit.right (le_trans Hr Hc) HΓ,
      wk.scons _ HΞ⟩
  | wk.cons Hc W, dup Hrel Hl Hr S =>
    let ⟨_, HΓ, HΞ⟩ := distribute_right W S;
    ⟨_,
      ssplit.dup (Var.le.rel Hc Hrel) (le_trans Hl Hc) (le_trans Hr Hc) HΓ,
      wk.scons _ HΞ⟩
  | wk.discard Ha W, S =>
    let ⟨_, HΓ, HΞ⟩ := distribute_right W S;
    ⟨_, sright _ HΓ, wk.discard Ha HΞ⟩

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
  | v::Γ => Ctx.split.left (le_refl v) (id Γ)

instance Ctx.wk.instInhabitedRefl {T: Type u} [HasLin T] {Γ: Ctx T}
  : Inhabited (Ctx.wk Γ Γ) where
  default := wk.id Γ

instance Ctx.wk.instSubsingletonRefl {T: Type u} [HasLin T] {Γ: Ctx T}
  : Subsingleton (Ctx.wk Γ Γ) where
  allEq := let rec allEq
  : ∀ {Γ: Ctx T} (HΓ: Ctx.wk Γ Γ) (HΓ': Ctx.wk Γ Γ), HΓ = HΓ'
  | [], nil, nil => rfl
  | _, cons _ HΓ, cons _ HΓ' => congrArg _ (allEq HΓ HΓ')
  | _, discard _ HΓ, _ | _, _, discard _ HΓ => HΓ.append_false.elim
  allEq

--TODO: subsingleton to nil --> nil is terminal object
--TODO: subsingleton from nil

def Ctx.wk.comp {T: Type u} [HasLin T] {Γ Δ Ξ: Ctx T}
  : Ctx.wk Γ Δ -> Ctx.wk Δ Ξ -> Ctx.wk Γ Ξ
  | nil, nil => nil
  | cons Hl HΓ, cons Hl' HΓ' =>
    cons (le_trans Hl' Hl) (comp HΓ HΓ')
  | cons Hl HΓ, discard Ha HΓ' =>
    discard (Var.le.aff Hl Ha) (comp HΓ HΓ')
  | discard Ha HΓ, H =>
    discard Ha (comp HΓ H)

def Ctx.wk.comp_id {T: Type u} [HasLin T] {Γ Δ: Ctx T}
  : (H: Ctx.wk Γ Δ) -> (R: Ctx.wk Δ Δ) -> H.comp R = H
  | nil, nil => rfl
  | cons _ HΓ, cons _ HΓ' => congrArg _ (comp_id HΓ HΓ')
  | discard _ HΓ, HΓ' => congrArg _ (comp_id HΓ HΓ')
  | cons _ _, discard _ HΓ => HΓ.append_false.elim

def Ctx.wk.id_comp {T: Type u} [HasLin T] {Γ Δ: Ctx T}
  : (R: Ctx.wk Γ Γ) -> (H: Ctx.wk Γ Δ) -> R.comp H = H
  | nil, nil => rfl
  | cons _ HΓ, cons _ HΓ' => congrArg _ (id_comp HΓ HΓ')
  | cons _ HΓ, discard _ HΓ' => congrArg _ (id_comp HΓ HΓ')
  | discard _ HΓ, _ => HΓ.append_false.elim

def Ctx.wk.comp_assoc {T: Type u} [HasLin T] {Γ Δ Ξ Θ: Ctx T}
  : (X: Ctx.wk Γ Δ)
  -> (Y: Ctx.wk Δ Ξ)
  -> (Z: Ctx.wk Ξ Θ)
  -> (X.comp Y).comp Z = X.comp (Y.comp Z)
  | nil, nil, nil => rfl
  | cons _ X, cons _ Y, cons _ Z => congrArg _ (comp_assoc X Y Z)
  | cons _ X, cons _ Y, discard _ Z => congrArg _ (comp_assoc X Y Z)
  | cons _ X, discard _ Y, Z => congrArg _ (comp_assoc X Y Z)
  | discard _ X, Y, Z => congrArg _ (comp_assoc X Y Z)

def Ctx.wk.antisymm {T: Type u} [HasLin T] {Γ Δ: Ctx T}
  : Ctx.wk Γ Δ -> Ctx.wk Δ Γ -> Γ = Δ
  | nil, nil => rfl
  | cons Hl HΓ, cons Hl' HΓ' =>
    by rw [antisymm HΓ HΓ', le_antisymm Hl Hl']
  | cons _ HΓ, discard _ HΓ' =>
    have H := le_trans HΓ'.length_decreasing HΓ.length_decreasing;
    by simp_arith at H
  | discard _ HΓ, cons _ HΓ' =>
    have H := le_trans HΓ.length_decreasing HΓ'.length_decreasing;
    by simp_arith at H
  | discard _ HΓ, discard _ HΓ' =>
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
  := Ctx.wk.comp H (Ctx.wk.cons H' (Ctx.wk.nil))
