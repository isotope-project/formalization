import Isotope.Syntax.Ty

namespace NamedList

structure Var (N: Type u) (T: Type v) extends Transparency where
  name: N
  ty: Ty T

instance Var.instHasLin {N: Type u} {T: Type v} [HasLin T]: HasLin (Var N T) where
  aff v := v.aff && HasLin.aff v.ty
  rel v := v.rel && HasLin.rel v.ty

instance Var.instPartialOrder {N: Type u} {T: Type v}: PartialOrder (Var N T) where
  le l r := l.name = r.name ∧ l.ty = r.ty ∧ l.toTransparency ≤ r.toTransparency
  le_refl := by simp [le_refl]
  le_trans _ _ _
    | ⟨Hn, HA, Ht⟩, ⟨Hn', HA', Ht'⟩
    => ⟨Hn.trans Hn', HA.trans HA', le_trans Ht Ht'⟩
  le_antisymm x x' H H'
    := mk.injEq _ _ _ _ _ _ ▸ ⟨le_antisymm H.2.2 H'.2.2, H.1, H.2.1⟩

theorem Var.le.aff {N: Type u} {T: Type v} [HasLin T] {l r: Var N T}
  : l ≤ r → HasLin.aff l → HasLin.aff r
  | ⟨He, Ht⟩ => by
    simp only [HasLin.aff, He, Bool.and_eq_true, and_imp]
    intro H H';
    exact ⟨Ht.2.1 H, Ht.1 ▸ H'⟩

theorem Var.le.rel {N: Type u} {T: Type v} [HasLin T] {l r: Var N T}
  : l ≤ r → HasLin.rel l → HasLin.rel r
  | ⟨He, Ht⟩ => by
    simp only [HasLin.rel, He, Bool.and_eq_true, and_imp]
    intro H H';
    exact ⟨Ht.2.2 H, Ht.1 ▸ H'⟩

--TODO: add context well-formedness condition? (no repeated names)
--TODO: contexts as finite functions Name -> Var? could be !FUN!
--Can be equipped with a separate "domain"?
--In this case can define separation-style judgements on domains...
abbrev Ctx (N: Type u) (T: Type v) := List (Var N T)

inductive Ctx.name {N: Type u} {T: Type v}: Ctx N T -> N -> Type (max u v)
  | head (q n A) (Γ: Ctx N T): Ctx.name (⟨q, n, A⟩::Γ) n
  | tail {m Γ} v: Ctx.name Γ m -> Ctx.name (v::Γ) m

def Ctx.undef {N: Type u} {T: Type v} (Γ: Ctx N T) (n: N): Prop
  := IsEmpty (Γ.name n)

def Ctx.names {N: Type u} {T: Type v}: Ctx N T -> List N
  := List.map Var.name

instance Ctx.instHasLin {N: Type u} {T: Type v} [HasLin T]
  : HasLin (Ctx N T) where
  aff Γ := Γ.all HasLin.aff
  rel Γ := Γ.all HasLin.rel

inductive Ctx.subctx {N: Type u} {T: Type v} [HasLin T]
  : Ctx N T -> Ctx N T -> Type (max u v)
  | nil: subctx [] []
  | cons {Γ Δ} {v l: Var N T}: l ≤ v -> subctx Γ Δ -> subctx (v::Γ) (l::Δ)
  | discard {Γ Δ} (v: Var N T): subctx Γ Δ -> subctx (v::Γ) Δ

def Ctx.is_subctx {N: Type u} {T: Type v} [HasLin T] {Γ Δ: Ctx N T}: Prop
  := Nonempty (Γ.subctx Δ)

inductive Ctx.subnames {N: Type u} {T: Type v} [HasLin T]
  : List N -> Ctx N T -> Type (max u v)
  | nil: subnames [] []
  | cons {Γ Δ} {q n A}: Ctx.subnames Γ Δ -> subnames (n::Γ) (⟨q, n, A⟩::Δ)
  | discard {Γ Δ} {n}: Ctx.subnames Γ Δ -> subnames (n::Γ) Δ

--TODO: all subcontexts are unique if and only if all variable names are unique
--TODO: think of how this could be used to define nameless SSA...

inductive Ctx.split {N: Type u} {T: Type v} [HasLin T]
  : Ctx N T → Ctx N T → Ctx N T → Type (max u v)
  | nil: split [] [] []
  | left {Γ Δ Ξ} {v l}:  l ≤ v → split Γ Δ Ξ → split (v::Γ) (l::Δ) Ξ
  | right {Γ Δ Ξ} {v r}: r ≤ v → split Γ Δ Ξ → split (v::Γ) Δ (r::Ξ)
  | discard {Γ Δ Ξ} {v}: HasLin.aff v → split Γ Δ Ξ → split (v::Γ) Δ Ξ
  | dup {Γ Δ Ξ} {v l r}: HasLin.rel v → l ≤ v → r ≤ v → split Γ Δ Ξ
    → split (v::Γ) (l::Δ) (r::Ξ)

def Ctx.split.subctx_left {N: Type u} {T: Type v} [HasLin T] {Γ Δ Ξ: Ctx N T}
  : Γ.split Δ Ξ -> Γ.subctx Δ
  | nil => subctx.nil
  | right _ H | discard _ H => subctx.discard _ (subctx_left H)
  | left Hl H | dup _ Hl _ H => subctx.cons Hl (subctx_left H)

def Ctx.split.subctx_right {N: Type u} {T: Type v}[HasLin T] {Γ Δ Ξ: Ctx N T}
  : Γ.split Δ Ξ -> Γ.subctx Ξ
  | nil => subctx.nil
  | left _ H | discard _ H => subctx.discard _ (subctx_right H)
  | right Hr H | dup _ _ Hr H => subctx.cons Hr (subctx_right H)

@[match_pattern]
def Ctx.split.sleft {N: Type u} {T: Type v}[HasLin T] {Γ Δ Ξ: Ctx N T}
  (v: Var N T): split Γ Δ Ξ -> split (v::Γ) (v::Δ) Ξ
  := left (le_refl v)
@[match_pattern]
def Ctx.split.sright {N: Type u} {T: Type v}[HasLin T] {Γ Δ Ξ: Ctx N T}
  (v: Var N T): split Γ Δ Ξ -> split (v::Γ) Δ (v::Ξ)
  := right (le_refl v)
@[match_pattern]
def Ctx.split.sdup {N: Type u} {T: Type v}[HasLin T] {Γ Δ Ξ: Ctx N T}
  {v} (Hv: HasLin.rel v): split Γ Δ Ξ -> split (v::Γ) (v::Δ) (v::Ξ)
  := dup Hv (le_refl v) (le_refl v)

inductive Ctx.ssplit {N: Type u} {T: Type v} [HasLin T]
  : Ctx N T → Ctx N T → Ctx N T → Type (max u v)
  | nil: ssplit [] [] []
  | left {Γ Δ Ξ} {v l}:  l ≤ v → ssplit Γ Δ Ξ → ssplit (v::Γ) (l::Δ) Ξ
  | right {Γ Δ Ξ} {v r}: r ≤ v → ssplit Γ Δ Ξ → ssplit (v::Γ) Δ (r::Ξ)
  | dup {Γ Δ Ξ} {v l r}: HasLin.rel v → l ≤ v → r ≤ v → ssplit Γ Δ Ξ
    → ssplit (v::Γ) (l::Δ) (r::Ξ)

@[match_pattern]
def Ctx.ssplit.sleft {N: Type u} {T: Type v} [HasLin T] {Γ Δ Ξ: Ctx N T}
  (v: Var N T): ssplit Γ Δ Ξ -> ssplit (v::Γ) (v::Δ) Ξ
  := left (le_refl v)
@[match_pattern]
def Ctx.ssplit.sright {N: Type u} {T: Type v} [HasLin T] {Γ Δ Ξ: Ctx N T}
  (v: Var N T): ssplit Γ Δ Ξ -> ssplit (v::Γ) Δ (v::Ξ)
  := right (le_refl v)
@[match_pattern]
def Ctx.ssplit.sdup {N: Type u} {T: Type v} [HasLin T] {Γ Δ Ξ: Ctx N T}
  {v} (Hv: HasLin.rel v): ssplit Γ Δ Ξ -> ssplit (v::Γ) (v::Δ) (v::Ξ)
  := dup Hv (le_refl v) (le_refl v)

def Ctx.ssplit.toSplit {N: Type u} {T: Type v} [HasLin T] {Γ Δ Ξ: Ctx N T}
  : ssplit Γ Δ Ξ → split Γ Δ Ξ
  | nil => split.nil
  | left Hl H => split.left Hl (ssplit.toSplit H)
  | right Hr H => split.right Hr (ssplit.toSplit H)
  | dup Hrel Hl Hr H => split.dup Hrel Hl Hr (ssplit.toSplit H)

def Ctx.split.swap {N: Type u} {T: Type v} [HasLin T] {Γ Δ Ξ: Ctx N T}
  : split Γ Δ Ξ -> split Γ Ξ Δ
  | nil => nil
  | left Hl H => right Hl (swap H)
  | right Hl H => left Hl (swap H)
  | discard Ha Hl => discard Ha (swap Hl)
  | dup H Hl Hr HΓ
    => dup H Hr Hl (swap HΓ)

def Ctx.ssplit.swap {N: Type u} {T: Type v} [HasLin T] {Γ Δ Ξ: Ctx N T}
  : ssplit Γ Δ Ξ -> ssplit Γ Ξ Δ
  | nil => nil
  | left Hl H => right Hl (swap H)
  | right Hr H => left Hr (swap H)
  | dup Hrel Hl Hr H => dup Hrel Hr Hl (swap H)

def Ctx.ssplit.swap_toSplit {N: Type u} {T: Type v} [HasLin T] {Γ Δ Ξ: Ctx N T}
  : (H: ssplit Γ Δ Ξ) -> H.swap.toSplit = H.toSplit.swap
  | nil => rfl
  | left _ H => congrArg _ (swap_toSplit H)
  | right _ H => congrArg _ (swap_toSplit H)
  | dup _ _ _ H => congrArg _ (swap_toSplit H)

def Ctx.split.swap_idem {N: Type u} {T: Type v} [HasLin T] {Γ Δ Ξ: Ctx N T}
  : Function.LeftInverse (@swap N T _ Γ Δ Ξ) (@swap N T _ Γ Ξ Δ)
  | nil => rfl
  | left _ HΓ => by simp [swap, swap_idem HΓ]
  | right _ HΓ => by simp [swap, swap_idem HΓ]
  | discard _ HΓ => by simp [swap, swap_idem HΓ]
  | dup _ _ _ HΓ => by simp [swap, swap_idem HΓ]

def Ctx.ssplit.swap_idem {N: Type u} {T: Type v} [HasLin T] {Γ Δ Ξ: Ctx N T}
  : Function.LeftInverse (@swap N T _ Γ Δ Ξ) (@swap N T _ Γ Ξ Δ)
  | nil => rfl
  | left _ H => by simp [swap, swap_idem H]
  | right _ H => by simp [swap, swap_idem H]
  | dup _ _ _ H => by simp [swap, swap_idem H]

def Ctx.split.swap_equiv {N: Type u} {T: Type v} [HasLin T] (Γ Δ Ξ: Ctx N T)
  : Equiv (split Γ Δ Ξ) (split Γ Ξ Δ) where
  toFun := swap
  invFun := swap
  left_inv := swap_idem
  right_inv := swap_idem

def Ctx.ssplit.swap_equiv {N: Type u} {T: Type v} [HasLin T] (Γ Δ Ξ: Ctx N T)
  : Equiv (ssplit Γ Δ Ξ) (ssplit Γ Ξ Δ) where
  toFun := swap
  invFun := swap
  left_inv := swap_idem
  right_inv := swap_idem

theorem Ctx.split.left_length_decreasing {N: Type u} {T: Type v} [HasLin T]
  {Γ Δ Ξ: Ctx N T}
  : split Γ Δ Ξ -> Δ.length ≤ Γ.length
  | nil => le_refl _
  | left _ HΓ => Nat.succ_le_succ HΓ.left_length_decreasing
  | right _ HΓ => Nat.le_step HΓ.left_length_decreasing
  | discard _ HΓ => Nat.le_step HΓ.left_length_decreasing
  | dup _ _ _ HΓ => Nat.succ_le_succ HΓ.left_length_decreasing

theorem Ctx.ssplit.left_length_decreasing {N: Type u} {T: Type v} [HasLin T]
  {Γ Δ Ξ: Ctx N T} (H: ssplit Γ Δ Ξ): Δ.length ≤ Γ.length
  := H.toSplit.left_length_decreasing

theorem Ctx.split.right_length_decreasing {N: Type u} {T: Type v} [HasLin T]
  {Γ Δ Ξ: Ctx N T} (H: split Γ Δ Ξ): Ξ.length ≤ Γ.length
  := H.swap.left_length_decreasing

theorem Ctx.ssplit.right_length_decreasing {N: Type u} {T: Type v} [HasLin T]
  {Γ Δ Ξ: Ctx N T} (H: ssplit Γ Δ Ξ): Ξ.length ≤ Γ.length
  := H.toSplit.right_length_decreasing

def Ctx.wk {N: Type u} {T: Type v} [HasLin T] (Γ Δ: Ctx N T)
  := Ctx.split Γ Δ []
def Ctx.var {N: Type u} {T: Type v} [HasLin T] (Γ: Ctx N T) (x: Var N T)
  := Ctx.wk Γ [x]

@[match_pattern]
def Ctx.wk.nil {N: Type u} {T: Type v} [HasLin T]: @Ctx.wk N T _ [] []
  := Ctx.split.nil
@[match_pattern]
def Ctx.wk.cons {N: Type u} {T: Type v} [HasLin T] {Γ Δ: Ctx N T}
  : {v l: Var N T} -> (Hl: l ≤ v) -> Ctx.wk Γ Δ -> Ctx.wk (v::Γ) (l::Δ)
  := Ctx.split.left
  @[match_pattern]
def Ctx.wk.scons {N: Type u} {T: Type v} [HasLin T] {Γ Δ: Ctx N T}
  (v: Var N T): Ctx.wk Γ Δ -> Ctx.wk (v::Γ) (v::Δ)
  := Ctx.split.left (le_refl v)
@[match_pattern]
def Ctx.wk.discard {N: Type u} {T: Type v} [HasLin T] {Γ Δ: Ctx N T}
  : {v: Var N T} -> (Ha: HasLin.aff v) -> Ctx.wk Γ Δ -> Ctx.wk (v::Γ) Δ
  := Ctx.split.discard

@[match_pattern]
def Ctx.var.head {N: Type u} {T: Type v} [HasLin T] {Γ: Ctx N T}
  {v v': Var N T} (H: v ≥ v') (W: Γ.wk []): Ctx.var (v::Γ) v'
  := Ctx.wk.cons H W
@[match_pattern]
def Ctx.var.shead {N: Type u} {T: Type v} [HasLin T] {Γ: Ctx N T}
  (v: Var N T) (W: Γ.wk []): Ctx.var (v::Γ) v
  := Ctx.wk.scons v W
@[match_pattern]
def Ctx.var.tail {N: Type u} {T: Type v} [HasLin T] {Γ: Ctx N T}
  {v a: Var N T} (Ha: HasLin.aff a) (W: Γ.var v): Ctx.var (a::Γ) v
  := Ctx.wk.discard Ha W

theorem Ctx.var.name {N: Type u} {T: Type v} [HasLin T] {Γ: Ctx N T} {v}
  : Γ.var v -> Γ.name v.name
  | head ⟨H, _, _⟩ _ => H ▸ name.head _ _ _ _
  | tail _ W => name.tail _ (var.name W)

def Ctx.split.left_decompose {T: Type u} [HasLin T] {Γ Δ Ξ: Ctx N T}
  : Ctx.split Γ Δ Ξ
  -> (Δ': Ctx N T) × Ctx.ssplit Γ Δ' Ξ × Ctx.wk Δ' Δ
  | nil => ⟨[], ssplit.nil, wk.nil⟩
  | left Hl H => let ⟨Δ', HΓ, HΔ⟩ := left_decompose H;
    ⟨_::Δ', ssplit.left Hl HΓ, wk.scons _ HΔ⟩
  | right Hr H => let ⟨Δ', HΓ, HΔ⟩ := left_decompose H;
    ⟨Δ', ssplit.right Hr HΓ, HΔ⟩
  | discard Ha H => let ⟨Δ', HΓ, HΔ⟩ := left_decompose H;
    ⟨_::Δ', ssplit.sleft _ HΓ, wk.discard Ha HΔ⟩
  | dup Hrel Hl Hr H => let ⟨Δ', HΓ, HΔ⟩ := left_decompose H;
    ⟨_::Δ', ssplit.dup Hrel Hl Hr HΓ, wk.scons _ HΔ⟩

def Ctx.split.right_decompose {N: Type u} {T: Type v} [HasLin T]
  {Γ Δ Ξ: Ctx N T}: Ctx.split Γ Δ Ξ
    -> (Ξ': Ctx N T) × Ctx.ssplit Γ Δ Ξ' × Ctx.wk Ξ' Ξ
  | nil => ⟨[], ssplit.nil, wk.nil⟩
  | left Hl H => let ⟨Ξ', HΓ, HΞ⟩ := right_decompose H;
    ⟨Ξ', ssplit.left Hl HΓ, HΞ⟩
  | right Hr H => let ⟨Ξ', HΓ, HΞ⟩ := right_decompose H;
    ⟨_::Ξ', ssplit.right Hr HΓ, wk.scons _ HΞ⟩
  | discard Ha H => let ⟨Ξ', HΓ, HΞ⟩ := right_decompose H;
    ⟨_::Ξ', ssplit.right (le_refl _) HΓ, wk.discard Ha HΞ⟩
  | dup Hrel Hl Hr H => let ⟨Ξ', HΓ, HΞ⟩ := right_decompose H;
    ⟨_::Ξ', ssplit.dup Hrel Hl Hr HΓ, wk.scons _ HΞ⟩

def Ctx.ssplit.distribute_left {N: Type u} {T: Type v} [HasLin T]
  {Γ Γ' Δ Ξ: Ctx N T}: Ctx.wk Γ' Γ -> Ctx.ssplit Γ Δ Ξ
    -> (Δ': Ctx N T) × Ctx.ssplit Γ' Δ' Ξ × Ctx.wk Δ' Δ
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

def Ctx.ssplit.distribute_right {N: Type u} {T: Type v} [HasLin T]
  {Γ Γ' Δ Ξ: Ctx N T}: Ctx.wk Γ' Γ -> Ctx.ssplit Γ Δ Ξ
    -> (Ξ': Ctx N T) × Ctx.ssplit Γ' Δ Ξ' × Ctx.wk Ξ' Ξ
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

theorem Ctx.wk.length_decreasing {T: Type u} [HasLin T] {Γ Δ: Ctx N T}
  (H: wk Γ Δ): Δ.length ≤ Γ.length
  := Ctx.split.left_length_decreasing H

theorem Ctx.wk.append_false {T: Type u} [HasLin T] {Γ: Ctx N T} {A}
  (H: wk Γ (A::Γ)): False
  := have H := H.length_decreasing; by simp_arith at H

theorem Ctx.wk.nil_nil {T: Type u} [HasLin T] {Γ: Ctx N T}
  : wk [] Γ -> Γ = []
  | nil => rfl

def Ctx.wk.id {T: Type u} [HasLin T]
  : (Γ: Ctx N T) -> Ctx.wk Γ Γ
  | [] => Ctx.split.nil
  | v::Γ => Ctx.split.left (le_refl v) (id Γ)

instance Ctx.wk.instInhabitedRefl {N: Type u} {T: Type v} [HasLin T]
  {Γ: Ctx N T}: Inhabited (Ctx.wk Γ Γ) where
  default := wk.id Γ

instance Ctx.wk.instSubsingletonRefl {N: Type u} {T: Type v} [HasLin T]
  {Γ: Ctx N T}: Subsingleton (Ctx.wk Γ Γ) where
  allEq := let rec allEq
  : ∀ {Γ: Ctx N T} (HΓ: Ctx.wk Γ Γ) (HΓ': Ctx.wk Γ Γ), HΓ = HΓ'
  | [], nil, nil => rfl
  | _, cons _ HΓ, cons _ HΓ' => congrArg _ (allEq HΓ HΓ')
  | _, discard _ HΓ, _ | _, _, discard _ HΓ => HΓ.append_false.elim
  allEq

--TODO: subsingleton to nil --> nil is terminal object
--TODO: subsingleton from nil

def Ctx.wk.comp {N: Type u} {T: Type v}[HasLin T] {Γ Δ Ξ: Ctx N T}
  : Ctx.wk Γ Δ -> Ctx.wk Δ Ξ -> Ctx.wk Γ Ξ
  | nil, nil => nil
  | cons Hl HΓ, cons Hl' HΓ' =>
    cons (le_trans Hl' Hl) (comp HΓ HΓ')
  | cons Hl HΓ, discard Ha HΓ' =>
    discard (Var.le.aff Hl Ha) (comp HΓ HΓ')
  | discard Ha HΓ, H =>
    discard Ha (comp HΓ H)

def Ctx.wk.comp_id {N: Type u} {T: Type v}[HasLin T] {Γ Δ: Ctx N T}
  : (H: Ctx.wk Γ Δ) -> (R: Ctx.wk Δ Δ) -> H.comp R = H
  | nil, nil => rfl
  | cons _ HΓ, cons _ HΓ' => congrArg _ (comp_id HΓ HΓ')
  | discard _ HΓ, HΓ' => congrArg _ (comp_id HΓ HΓ')
  | cons _ _, discard _ HΓ => HΓ.append_false.elim

def Ctx.wk.id_comp {N: Type u} {T: Type v} [HasLin T] {Γ Δ: Ctx N T}
  : (R: Ctx.wk Γ Γ) -> (H: Ctx.wk Γ Δ) -> R.comp H = H
  | nil, nil => rfl
  | cons _ HΓ, cons _ HΓ' => congrArg _ (id_comp HΓ HΓ')
  | cons _ HΓ, discard _ HΓ' => congrArg _ (id_comp HΓ HΓ')
  | discard _ HΓ, _ => HΓ.append_false.elim

def Ctx.wk.comp_assoc {N: Type u} {T: Type v} [HasLin T] {Γ Δ Ξ Θ: Ctx N T}
  : (X: Ctx.wk Γ Δ)
  -> (Y: Ctx.wk Δ Ξ)
  -> (Z: Ctx.wk Ξ Θ)
  -> (X.comp Y).comp Z = X.comp (Y.comp Z)
  | nil, nil, nil => rfl
  | cons _ X, cons _ Y, cons _ Z => congrArg _ (comp_assoc X Y Z)
  | cons _ X, cons _ Y, discard _ Z => congrArg _ (comp_assoc X Y Z)
  | cons _ X, discard _ Y, Z => congrArg _ (comp_assoc X Y Z)
  | discard _ X, Y, Z => congrArg _ (comp_assoc X Y Z)

def Ctx.wk.antisymm {N: Type u} {T: Type v} [HasLin T] {Γ Δ: Ctx N T}
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

def Ctx.split.right_wk {N: Type u} {T: Type v} [HasLin T] {Γ Δ: Ctx N T}
  : Ctx.split Γ [] Δ → Ctx.wk Γ Δ
  := swap

def Ctx.wk.right_wk {N: Type u} {T: Type v} [HasLin T] {Γ Δ: Ctx N T}
  : Ctx.wk Γ Δ → Ctx.split Γ [] Δ
  := Ctx.split.swap

def Ctx.wk.equiv_right {N: Type u} {T: Type v} [HasLin T] {Γ Δ: Ctx N T}
  : Equiv (Ctx.wk Γ Δ) (Ctx.split Γ [] Δ)
  := Ctx.split.swap_equiv Γ Δ []

-- def Ctx.split.associate_left_tri {T} [HasLin T] {Γ Δ Ξ Θ Φ: Ctx T}:
--   Ctx.split Γ Δ Ξ → Ctx.split Ξ Θ Φ → (Ψ: _) × Ctx.split Γ Ψ Φ × Ctx.split Ψ Δ Θ
--   | H, nil => ⟨Δ, H, wk.refl Δ⟩
--   | _, _ => sorry

def Ctx.var.upgrade {N: Type u} {T: Type v} [HasLin T] {Γ: Ctx N T}
  {v v': Var N T} (H: Γ.var v) (H': v ≥ v'): Γ.var v'
  := Ctx.wk.comp H (Ctx.wk.cons H' (Ctx.wk.nil))
