import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.Group.Ext
import Mathlib.Init.Order.Defs

import Isotope.Syntax.Ty
import Isotope.Syntax.Abstract.Basic

open Abstract

--TODO: class for binary validity relation?
class ResourceAlgebra (T: Type u) extends
  OrderedAddCommMonoid T
  -- ,One T
  where
  -- Emulating a partial commutative monoid via `valid`:
  valid: T -> T -> Prop
  valid_id x: valid 0 x
  zero_min x: le x 0 -> x = 0
  -- cancel_zero_left: ∀ x y, add x y = 0 -> x = 0
  valid_symm: ∀ x y, valid x y -> valid y x
  valid_le_right: ∀ x y y', le y' y -> valid x y -> valid x y'
  valid_le_left: ∀x x' y, le x' x -> valid x y -> valid x' y
    := λ _ _ _ Hxx' Hxy => valid_symm _ _
      (valid_le_right _ _ _ Hxx' (valid_symm _ _ Hxy))
  valid_left_assoc: ∀ x y z, valid (x + y) z -> valid x y -> valid y z
  valid_assoc_mp: ∀ x y z, valid x y -> valid (x + y) z -> valid x (y + z)
  valid_right_assoc: ∀ x y z, valid x (y + z) -> valid y z -> valid x y
    := λ x y z Hxyz Hyz
      => valid_symm y x
        (valid_left_assoc _ _ _ (valid_symm _ _ (add_comm y z ▸ Hxyz))
          (valid_symm y z Hyz))

def ResourceAlgebra.valid_assoc_mpr {T} [ResourceAlgebra T]
  (x y z: T) (Hyz: valid y z) (Hxyz: valid x (y + z)): valid (x + y) z
  := valid_symm _ _ ((add_comm x y) ▸ valid_assoc_mp z y x
      (valid_symm _ _ Hyz)
      (add_comm y z ▸ valid_symm _ _ Hxyz))

  -- mandatory separation between values and ghosts
  -- NOTE: if this is not enforced, we're allowed "pure ghost" values which
  -- are *always* unusable. Or, of course, we could allow using them, in which
  -- case we simply have that they *must* be the unit type...
  -- zero_ne_one: zero ≠ one

theorem ordered_add_comm_monoid_ext {T} (S R: OrderedAddCommMonoid T)
  (Hadd: R.add = S.add) (Hle: ∀x y, R.le x y ↔ S.le x y): R = S
  := by
      cases R; cases S;
      have Hle := PartialOrder.ext Hle;
      have Hadd := AddCommMonoid.ext Hadd;
      congr

theorem ResourceAlgebra.ext {T} (S R: ResourceAlgebra T)
    (Hadd: R.add = S.add)
    (Hle: ∀x y, R.le x y ↔ S.le x y)
    (Hvalid: ∀x y, R.valid x y ↔ S.valid x y): R = S
  := by
    have Hvalid: R.valid = S.valid
      := by funext x y; apply propext; apply Hvalid
    cases R; cases S;
    have Hoadd := ordered_add_comm_monoid_ext _ _ Hadd Hle;
    congr

structure ResourceAlgebra.Subalgebra {T} (S R: ResourceAlgebra T): Prop where
  add_eq: S.add = R.add --TODO: only require equality on valid set?
  le_sub x y: S.le x y -> R.le x y
  valid_sub x y: S.valid x y -> R.valid x y

  monoid_eq: S.toAddMonoid = R.toAddMonoid := AddMonoid.ext add_eq
  zero_eq: S.zero = R.zero := monoid_eq ▸ rfl

def ResourceAlgebra.Subalgebra.refl {T} (R: ResourceAlgebra T)
  : R.Subalgebra R where
  add_eq := rfl
  le_sub _ _ := id
  valid_sub _ _ := id

def ResourceAlgebra.Subalgebra.trans {T} {Q S R: ResourceAlgebra T}
  (H: Q.Subalgebra S) (H': S.Subalgebra R)
  : Q.Subalgebra R where
  add_eq := Eq.trans H.add_eq H'.add_eq
  le_sub _ _ := H'.le_sub _ _ ∘ H.le_sub _ _
  valid_sub _ _ := H'.valid_sub _ _ ∘ H.valid_sub _ _

def ResourceAlgebra.affineAlgebra (T: Type u) [R: ResourceAlgebra T]
  : ResourceAlgebra T where
  valid x y := x = 0 ∨ y = 0
  valid_id y := Or.inl rfl
  zero_min := R.zero_min
  -- cancel_zero_left := R.cancel_zero_left
  valid_le_right _x _y _y' H
    | Or.inl Hx => Or.inl Hx
    | Or.inr Hy => Or.inr (R.zero_min _ (Hy ▸ H))
  valid_symm _ _ | Hxy => Hxy.elim Or.inr Or.inl
  valid_left_assoc _x _y _z
    | Or.inl Hxy, Or.inl Hx => Or.inl (by rw [<-Hxy, Hx, zero_add])
    | Or.inr Hz, _ => Or.inr Hz
    | _, Or.inr Hy => Or.inl Hy
  valid_assoc_mp _x _y _z
    | Or.inl Hx, _ => Or.inl Hx
    | Or.inr Hy, Or.inl Hxy => Or.inl (by rw [<-Hxy, Hy, add_zero])
    | Or.inr Hy, Or.inr Hz => Or.inr (by rw [Hy, Hz, add_zero])

def ResourceAlgebra.affineSubalgebra (T: Type u) [R: ResourceAlgebra T]
  : (R.affineAlgebra).Subalgebra R where
  add_eq := rfl
  le_sub _ _ := id
  valid_sub
    | _, _, Or.inl rfl => valid_id _
    | _, _, Or.inr rfl => valid_symm _ _ (valid_id _)

def ResourceAlgebra.relevantAlgebra (T: Type u) [R: ResourceAlgebra T]
  : ResourceAlgebra T where
  le := Eq
  le_refl := Eq.refl
  le_trans _ _ _ := Eq.trans
  le_antisymm _ _ H _ := H
  lt _ _ := False
  lt_iff_le_not_le _ _ := ⟨False.elim, λ⟨H, C⟩ => C H.symm⟩
  add_le_add_left _ _ | rfl, _ => rfl
  valid := R.valid
  valid_id := R.valid_id
  valid_le_right _ _ _ H V := H ▸ V
  zero_min _ H := H
  valid_symm := R.valid_symm
  valid_left_assoc := R.valid_left_assoc
  valid_assoc_mp := R.valid_assoc_mp

def ResourceAlgebra.relevantSubalgebra (T: Type u) [R: ResourceAlgebra T]
  : (R.relevantAlgebra).Subalgebra R where
  add_eq := rfl
  le_sub _ _ | rfl => le_refl _
  valid_sub _ _ := id

def ResourceAlgebra.linearAlgebra (T: Type u) [R: AddCommMonoid T]
  : ResourceAlgebra T where
  le := Eq
  le_refl := Eq.refl
  le_trans _ _ _ := Eq.trans
  le_antisymm _ _ H _ := H
  lt _ _ := False
  lt_iff_le_not_le _ _ := ⟨False.elim, λ⟨H, C⟩ => C H.symm⟩
  add_le_add_left _ _ | rfl, _ => rfl
  valid x y := x = 0 ∨ y = 0
  valid_id y := Or.inl rfl
  valid_le_right _ _ _ H V := H ▸ V
  zero_min _ H := H
  valid_symm _ _ | Hxy => Hxy.elim Or.inr Or.inl
  valid_left_assoc _x _y _z
    | Or.inl Hxy, Or.inl Hx => Or.inl (by rw [<-Hxy, Hx, zero_add])
    | Or.inr Hz, _ => Or.inr Hz
    | _, Or.inr Hy => Or.inl Hy
  valid_assoc_mp _x _y _z
    | Or.inl Hx, _ => Or.inl Hx
    | Or.inr Hy, Or.inl Hxy => Or.inl (by rw [<-Hxy, Hy, add_zero])
    | Or.inr Hy, Or.inr Hz => Or.inr (by rw [Hy, Hz, add_zero])

def ResourceAlgebra.linearSubalgebra (T: Type u) [R: ResourceAlgebra T]
  : (linearAlgebra T).Subalgebra R where
  add_eq := rfl
  le_sub _ _ | rfl => le_refl _
  valid_sub _ _
    | Or.inl H => H ▸ (valid_id _)
    | Or.inr H => H ▸ (valid_symm _ _ (valid_id _))

def ResourceAlgebra.linearAffineSubalgebra (T: Type u) [ResourceAlgebra T]
  : (linearAlgebra T).Subalgebra (affineAlgebra T) where
  add_eq := rfl
  le_sub _ _ | rfl => le_refl _
  valid_sub _ _ := id

def ResourceAlgebra.linearRelevantSubalgebra (T: Type u) [R: ResourceAlgebra T]
  : (linearAlgebra T).Subalgebra (relevantAlgebra T) where
  add_eq := rfl
  le_sub _ _ := id
  valid_sub
    | _, _, Or.inl rfl => R.valid_id _
    | _, _, Or.inr rfl => R.valid_symm _ _ (R.valid_id _)

def ResourceAlgebra.transparentAlgebra' (T: Type u) [R: ResourceAlgebra T]
  : Transparency -> ResourceAlgebra T
  | ⟨true, true⟩ => R
  | ⟨true, false⟩ => R.affineAlgebra
  | ⟨false, true⟩ => R.relevantAlgebra
  | ⟨false, false⟩ => linearAlgebra T

def ResourceAlgebra.transparentAlgebra (T: Type u) [R: ResourceAlgebra T]
  (q: Transparency): ResourceAlgebra T where
  le x y := (q.aff ∧ R.le x y) ∨ x = y
  le_refl x := Or.inr rfl
  le_trans  _ _ _
    | Or.inl H, Or.inl H' => Or.inl ⟨H.1, H.2.trans H'.2⟩
    | Or.inr rfl, H | H, Or.inr rfl => H
  le_antisymm _ _
    | Or.inl H, Or.inl H' => R.le_antisymm _ _ H.2 H'.2
    | Or.inr rfl, _ | _, Or.inr rfl => rfl
  lt x y := q.aff ∧ R.lt x y
  lt_iff_le_not_le _ _ := ⟨
    λ⟨Ha, Hlt⟩ =>
      let H' := (R.lt_iff_le_not_le _ _).mp Hlt;
      ⟨ Or.inl ⟨Ha, H'.1⟩,
        λH => H'.2 (match H with | Or.inr rfl => le_refl _ | Or.inl H => H.2) ⟩,
    λ| ⟨Or.inr rfl, Hnl⟩ => (Hnl (Or.inr rfl)).elim
     | ⟨Or.inl ⟨Ha, Hle⟩, Hnl⟩
      => ⟨Ha, (R.lt_iff_le_not_le _ _).mpr ⟨Hle, λH => Hnl (Or.inl ⟨Ha, H⟩)⟩⟩
    ⟩
  add_le_add_left _ _
    | Or.inl H, _ => Or.inl ⟨H.1, R.add_le_add_left _ _ H.2 _⟩
    | Or.inr rfl, _ => Or.inr rfl
  valid x y := (q.rel ∧ R.valid x y) ∨ x = 0 ∨ y = 0
  valid_id y := Or.inr (Or.inl rfl)
  valid_le_right _x _y _y'
    | Or.inl ⟨_, H⟩, Or.inl ⟨Hr, V⟩ => Or.inl ⟨Hr, valid_le_right _ _ _ H V⟩
    | Or.inl _, Or.inr (Or.inl H') => Or.inr (Or.inl H')
    | Or.inl ⟨_, H⟩, Or.inr (Or.inr H') => Or.inr (Or.inr (zero_min _ (H' ▸ H)))
    | Or.inr H, V => H ▸ V
  zero_min _x
    | Or.inl ⟨_, H⟩ => R.zero_min _ H
    | Or.inr H => H
  valid_symm _ _
    | Or.inl Hxy => Or.inl ⟨Hxy.1, R.valid_symm _ _ Hxy.2⟩
    | Or.inr Hxy => Or.inr (Or.elim Hxy Or.inr Or.inl)
  valid_left_assoc _x _y _z
    | Or.inl ⟨Hr, Hxyz⟩, Or.inl ⟨_, Hxy⟩
      => Or.inl ⟨Hr, R.valid_left_assoc _ _ _ Hxyz Hxy⟩
    | Or.inl ⟨Hr, Hxyz⟩, Or.inr (Or.inl Hx)
      => Or.inl ⟨Hr, by simp [Hx] at Hxyz; exact Hxyz⟩
    | _, Or.inr (Or.inr Hy) => Or.inr (Or.inl Hy)
    | Or.inr (Or.inl Hxy), Or.inl ⟨Hr, Hxy'⟩
      => Or.inl ⟨Hr, valid_left_assoc _ _ _ (Hxy.symm ▸ valid_id _) Hxy'⟩
    | Or.inr (Or.inl Hxy), Or.inr (Or.inl Hx)
      => Or.inr (Or.inl (by rw [<-Hxy, Hx, zero_add]))
    | Or.inr (Or.inr Hz), _ => Or.inr (Or.inr Hz)
  valid_assoc_mp _x _y _z
    | Or.inl ⟨Hr, Hxy⟩, Or.inl ⟨_, Hxyz⟩
      => Or.inl ⟨Hr, R.valid_assoc_mp _ _ _ Hxy Hxyz⟩
    | Or.inl ⟨Hr, Hxy⟩, Or.inr (Or.inl Hxy')
      => Or.inl ⟨Hr, R.valid_assoc_mp _ _ _ Hxy (Hxy'.symm ▸ valid_id _)⟩
    | Or.inl ⟨Hr, Hxy⟩, Or.inr (Or.inr Hz)
      => Or.inl ⟨Hr, by rw [Hz, add_zero]; exact Hxy⟩
    | Or.inr (Or.inl Hx), _ => Or.inr (Or.inl Hx)
    | Or.inr (Or.inr Hy), Or.inl ⟨Hr, Hxyz⟩
      => Or.inl ⟨Hr, by simp only [Hy, add_zero, zero_add] at *; exact Hxyz⟩
    | Or.inr (Or.inr Hy), Or.inr (Or.inl Hxy)
      => Or.inr (Or.inl (by simp only [Hy, add_zero] at Hxy; exact Hxy))
    | Or.inr (Or.inr Hy), Or.inr (Or.inr Hz)
      => Or.inr (Or.inr (by simp [Hy, Hz]))

theorem ResourceAlgebra.transparentAlgebra_int
  (T: Type u) [R: ResourceAlgebra T]
  : R.transparentAlgebra ⟨true, true⟩ = R
  := ResourceAlgebra.ext _ _ rfl
    (λ_ _ => ⟨λ
      | Or.inl H => H.2
      | Or.inr rfl => le_refl _,
      λH => Or.inl ⟨rfl, H⟩⟩)
    (λ_ _ => ⟨λ
      | Or.inl H => H.2
      | Or.inr (Or.inl H) => H ▸ R.valid_id _
      | Or.inr (Or.inr H) => H ▸ R.valid_symm _ _ (R.valid_id _),
      λH => Or.inl ⟨rfl, H⟩⟩)

theorem ResourceAlgebra.transparentAlgebra_rel
  (T: Type u) [R: ResourceAlgebra T]
  : R.transparentAlgebra ⟨false, true⟩ = R.relevantAlgebra
  := ResourceAlgebra.ext _ _ rfl
    (λ_ _ => ⟨λ
      | Or.inl H => by cases H.1
      | Or.inr rfl => rfl, λ| rfl => Or.inr rfl⟩)
    (λ_ _ => ⟨λ
      | Or.inl H => H.2
      | Or.inr (Or.inl H) => H ▸ R.valid_id _
      | Or.inr (Or.inr H) => H ▸ R.valid_symm _ _ (R.valid_id _),
      λH => Or.inl ⟨rfl, H⟩⟩)

theorem ResourceAlgebra.transparentAlgebra_aff
  (T: Type u) [R: ResourceAlgebra T]
  : R.transparentAlgebra ⟨true, false⟩ = R.affineAlgebra
  := ResourceAlgebra.ext _ _ rfl
    (λ_ _ => ⟨λ
      | Or.inl H => H.2
      | Or.inr rfl => le_refl _,
      λH => Or.inl ⟨rfl, H⟩⟩)
    (λ_ _ => ⟨λ
      | Or.inl H => by cases H.1
      | Or.inr H => H,
      Or.inr⟩)

theorem ResourceAlgebra.transparentAlgebra_lin
  (T: Type u) [R: ResourceAlgebra T]
  : R.transparentAlgebra ⟨false, false⟩ = ResourceAlgebra.linearAlgebra T
  := ResourceAlgebra.ext _ _ rfl
    (λ_ _ => ⟨λ
      | Or.inl H => by cases H.1
      | Or.inr rfl => rfl, λ| rfl => Or.inr rfl⟩)
    (λ_ _ => ⟨λ
      | Or.inl H => by cases H.1
      | Or.inr H => H,
      Or.inr⟩)

theorem ResourceAlgebra.transparentSubalgebra'
  (T: Type u) [R: ResourceAlgebra T]
  : (q: Transparency) -> (R.transparentAlgebra' q).Subalgebra R
  | ⟨true, true⟩ => Subalgebra.refl R
  | ⟨true, false⟩ => R.affineSubalgebra
  | ⟨false, true⟩ => R.relevantSubalgebra
  | ⟨false, false⟩ => R.linearSubalgebra

theorem ResourceAlgebra.transparentAlgebra_char
  (T: Type u) [R: ResourceAlgebra T]
  : (q: Transparency) -> R.transparentAlgebra q = R.transparentAlgebra' q
  | ⟨true, true⟩ => R.transparentAlgebra_int
  | ⟨true, false⟩ => R.transparentAlgebra_aff
  | ⟨false, true⟩ => R.transparentAlgebra_rel
  | ⟨false, false⟩ => R.transparentAlgebra_lin

theorem ResourceAlgebra.transparentSubalgebra
  (T: Type u) [R: ResourceAlgebra T]
  (q: Transparency): (R.transparentAlgebra q).Subalgebra R
  := R.transparentAlgebra_char q ▸ R.transparentSubalgebra' q

theorem ResourceAlgebra.transparentLeSubalgebra
  (T: Type u) [R: ResourceAlgebra T]
  {q q': Transparency} (Hq: q ≤ q'):
  (R.transparentAlgebra q).Subalgebra (R.transparentAlgebra q')
  where
  add_eq := rfl
  le_sub _ _
    | Or.inl ⟨Hrel, H⟩ => Or.inl ⟨Hq.1 Hrel, H⟩
    | Or.inr rfl => Or.inr rfl
  valid_sub _ _
    | Or.inl ⟨Hrel, H⟩ => Or.inl ⟨Hq.2 Hrel, H⟩
    | Or.inr H => Or.inr H

def LinT (_: Transparency) (T: Type u) := T

instance LinT.instResourceAlgebra (T: Type u) [ResourceAlgebra T]
  (q: Transparency): ResourceAlgebra (LinT q T)
  := ResourceAlgebra.transparentAlgebra T q

def Aff (T: Type u) := T
def Rel (T: Type u) := T
def Lin (T: Type u) := T

instance Aff.instResourceAlgebra {T: Type u} [ResourceAlgebra T]
  : ResourceAlgebra (Aff T) := ResourceAlgebra.affineAlgebra T
instance Rel.instResourceAlgebra {T: Type u} [ResourceAlgebra T]
  : ResourceAlgebra (Rel T) := ResourceAlgebra.relevantAlgebra T
instance Lin.instResourceAlgebra {T: Type u} [ResourceAlgebra T]
  : ResourceAlgebra (Lin T) := ResourceAlgebra.linearAlgebra T

--TODO: make this into a resource algebra for booleans?
inductive VarState: Type u
  | ghost
  | value

inductive VarState.le: VarState -> VarState -> Prop
  | ghost: ∀ x, le ghost x
  | value: VarState.le value value

instance VarState.instPartialOrder: PartialOrder VarState where
  le := VarState.le
  le_refl a := by cases a <;> constructor
  le_trans a b c Hab Hbc := by cases Hab <;> cases Hbc <;> constructor
  le_antisymm a b Hab Hba := by cases Hab <;> cases Hba <;> rfl

instance VarState.instZero: Zero VarState where
  zero := ghost
instance VarState.instOne: One VarState where
  one := value
instance VarState.instOrderedAddCommMonoid: OrderedAddCommMonoid VarState where
  add
  | ghost, x | x, ghost => x
  | value, value => value
  add_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  add_comm := by intro a b; cases a <;> cases b <;> rfl
  zero_add := by intro a; cases a <;> rfl
  add_zero := by intro a; cases a <;> rfl
  add_le_add_left a b Hab c
    := by cases a <;> cases b <;> cases c <;> cases Hab <;> constructor

instance VarState.instResourceAlgebra: ResourceAlgebra VarState where
  valid _ _ := true
  valid_id _ := by trivial
  zero_min _ H := by cases H; rfl
  valid_le_right := by intros; trivial
  valid_symm := by intros; trivial
  valid_left_assoc := by intros; trivial
  valid_assoc_mp := by intros; trivial

instance ResourceAlgebra.instResourceAlgebraPair {A B}
  [ResourceAlgebra A] [ResourceAlgebra B]
  : ResourceAlgebra (A × B) where
  valid x y := valid x.1 y.1 ∧ valid x.2 y.2
  valid_id | ⟨a, b⟩ => ⟨valid_id a, valid_id b⟩
  zero_min
    | ⟨_l, _r⟩, ⟨Hl, Hr⟩
    => by simp only [] at *; rw [zero_min _ Hl, zero_min _ Hr]; rfl
  valid_le_right _ _ _ H V := ⟨valid_le_right _ _ _ H.1 V.1, valid_le_right _ _ _ H.2 V.2⟩
  valid_symm _ _ | ⟨Ha, Hb⟩ => ⟨valid_symm _ _ Ha, valid_symm _ _ Hb⟩
  valid_left_assoc _ _ _ H H' :=
    ⟨valid_left_assoc _ _ _ H.1 H'.1, valid_left_assoc _ _ _ H.2 H'.2⟩
  valid_assoc_mp _ _ _
    | ⟨Hxya, Hxyb⟩, ⟨Hxyza, Hxyzb⟩
    => ⟨valid_assoc_mp _ _ _ Hxya Hxyza,
        valid_assoc_mp _ _ _ Hxyb Hxyzb⟩

class ResourceAlgebraFamily.{u, v} (T: Type u) where
  res: T -> Type v
  resourceAlgebra: (t: T) -> ResourceAlgebra (res t)

instance ResourceAlgebraFamily.instResourceAlgebra
  {T: Type u} [ResourceAlgebraFamily T] {t: T}
  : ResourceAlgebra (res t)
  := resourceAlgebra t

def Ty.res {T: Type u} [ResourceAlgebraFamily T]: Ty T -> Type v
  | Ty.base X => ResourceAlgebraFamily.res X
  | Ty.unit | Ty.bool => VarState
  | Ty.tensor A B => res A × res B

def Ty.resourceAlgebra {T: Type u} [ResourceAlgebraFamily T]
  : (t: Ty T) -> ResourceAlgebra (res t)
  | Ty.base X => ResourceAlgebraFamily.resourceAlgebra X
  | Ty.unit | Ty.bool => VarState.instResourceAlgebra
  | Ty.tensor A B => @ResourceAlgebra.instResourceAlgebraPair _ _
    (resourceAlgebra A)
    (resourceAlgebra B)

instance Ty.instResourceAlgebra
  {T: Type u} [ResourceAlgebraFamily T] {t: Ty T}: ResourceAlgebra (t.res)
  := t.resourceAlgebra

instance ResourceAlgebraFamily.instResourceAlgebraFamilyTy
  {T: Type u} [ResourceAlgebraFamily T]: ResourceAlgebraFamily (Ty T)
  where
  res := Ty.res
  resourceAlgebra := Ty.resourceAlgebra

def ResourceAlgebra.Split {T: Type u} [ResourceAlgebra T]
  (x l r: T): Prop := x ≥ l + r ∧ valid l r

def ResourceAlgebra.Split.symm {T: Type u} [R: ResourceAlgebra T]
  {x l r: T}: Split x l r -> Split x r l
  | ⟨Hxlr, Vlr⟩ => ⟨R.add_comm _ _ ▸ Hxlr, R.valid_symm _ _ Vlr⟩

def ResourceAlgebra.Split.sum {T: Type u} [ResourceAlgebra T]
  {l r: T} (H: valid l r): Split (l + r) l r
  := ⟨le_refl _, H⟩

def ResourceAlgebra.Split.assoc {T: Type u} [R: ResourceAlgebra T]
  {x123 x12 x1 x2 x3: T}
  : Split x123 x12 x3 -> Split x12 x1 x2
    -> Split x123 x1 (x2 + x3) ∧ Split (x2 + x3) x2 x3
  | ⟨Hx123, V123⟩, ⟨Hx12, V12⟩ =>
    have Hx123' := valid_le_left _ _ _ Hx12 V123
    have Hx123'' := valid_assoc_mp _ _ _ V12 Hx123'
    ⟨⟨le_trans (R.add_assoc _ _ _ ▸ add_le_add_right Hx12 _) Hx123, Hx123''⟩,
     ⟨le_refl _, valid_left_assoc _ _ _ Hx123' V12⟩⟩

instance ResourceAlgebra.instSplits {T: Type u} [ResourceAlgebra T]
  : Splits T where
  Split := Split
  splitSymm := Split.symm
  splitAssoc s12_3 s12 :=
    let ⟨s1_23, s23⟩ := s12_3.assoc s12
    ⟨_, s1_23, s23⟩

instance ResourceAlgebra.instWk {T: Type u} [ResourceAlgebra T]
  : Wkns T := PRes.instWkns

--TODO: swap valid_le left/right here? splitWk?
instance ResourceAlgebra.instSplitWk {T: Type u} [ResourceAlgebra T]
  : SplitWk T where
  wkSplit w s := ⟨le_trans s.1 w, s.2⟩
  splitWkLeft s w := ⟨
    le_trans (add_le_add_right w _) s.1,
    valid_le_left _ _ _ w s.2⟩
  splitWkRight s w := ⟨
    le_trans (add_le_add_left w _) s.1,
    valid_le_right _ _ _ w s.2⟩

def ResourceAlgebra.QSplit {T: Type u} [ResourceAlgebra T]
  (q: Transparency) (x l r: T): Prop
  := @Split T (ResourceAlgebra.transparentAlgebra T q) x l r

--TODO: QWk x x' iff QSplit x' x 0 iff QSplit x x' 0
def ResourceAlgebra.QWk {T: Type u} [ResourceAlgebra T]
  (q: Transparency) (x x': T): Prop
  := (ResourceAlgebra.transparentAlgebra T q).le x' x

theorem ResourceAlgebra.QSplit.upcast {T: Type u} [ResourceAlgebra T]
  {q q': Transparency} {x l r: T} (H: q ≤ q')
  : QSplit q x l r -> QSplit q' x l r
  | ⟨Hxlr, Vlr⟩ => ⟨
    (transparentLeSubalgebra _ H).le_sub (l + r) x Hxlr,
    (transparentLeSubalgebra _ H).valid_sub _ _ Vlr⟩

theorem ResourceAlgebra.QWk.upcast {T: Type u} [ResourceAlgebra T]
  {q q': Transparency} {v v': T} (H: q ≤ q')
  : QWk q v v' -> QWk q' v v'
  := (transparentLeSubalgebra _ H).le_sub _ _

theorem ResourceAlgebra.QSplit.symm {T: Type u} [ResourceAlgebra T]
  {q} {x l r: T}: QSplit q x l r -> QSplit q x r l
  := @Split.symm T (ResourceAlgebra.transparentAlgebra T q) x l r

theorem ResourceAlgebra.QSplit.wk {T: Type u} [ResourceAlgebra T]
  {q} {x' x l r: T}:  QWk q x' x -> QSplit q x l r -> QSplit q x' l r
  := (@ResourceAlgebra.instSplitWk (LinT q T) _).wkSplit

theorem ResourceAlgebra.QSplit.wkLeft {T: Type u} [ResourceAlgebra T]
  {q} {x l l' r: T}: QSplit q x l r -> QWk q l l' -> QSplit q x l' r
  := (@ResourceAlgebra.instSplitWk (LinT q T) _).splitWkLeft

theorem ResourceAlgebra.QSplit.wkRight {T: Type u} [ResourceAlgebra T]
  {q} {x l r r': T}: QSplit q x l r -> QWk q r r' -> QSplit q x l r'
  := (@ResourceAlgebra.instSplitWk (LinT q T) _).splitWkRight

theorem ResourceAlgebra.QSplit.assoc {T: Type u} [ResourceAlgebra T]
  {q} {x123 x12 x1 x2 x3: T}
  : QSplit q x123 x12 x3 -> QSplit q x12 x1 x2
    -> QSplit q x123 x1 (x2 + x3) ∧ QSplit q (x2 + x3) x2 x3
  := @Split.assoc T (ResourceAlgebra.transparentAlgebra T q) x123 x12 x1 x2 x3

theorem ResourceAlgebra.qsplit_rel {T: Type u} [ResourceAlgebra T]
  {q} {x l r: T}: QSplit q x l r -> q.rel ∨ l = 0 ∨ r = 0
  | ⟨_, Or.inl Hv⟩ => Or.inl Hv.1
  | ⟨_, Or.inr Hv⟩ => Or.inr Hv

theorem ResourceAlgebra.qsplit_aff {T: Type u} [ResourceAlgebra T]
  {q} {x l r: T}: QSplit q x l r -> q.aff ∨ l + r = x
  | ⟨Or.inl H, _⟩ => Or.inl H.1
  | ⟨Or.inr H, _⟩ => Or.inr H

theorem ResourceAlgebra.qsplit_split {T: Type u} [ResourceAlgebra T]
  {q} {x l r: T}: QSplit q x l r -> Split x l r
  | ⟨Hxlr, Vlr⟩ => ⟨
    (transparentSubalgebra _ q).le_sub (l + r) x Hxlr,
    (transparentSubalgebra _ q).valid_sub _ _ Vlr⟩
