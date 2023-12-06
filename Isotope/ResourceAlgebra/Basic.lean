import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.Group.Ext
import Mathlib.Init.Order.Defs

import Isotope.Syntax.Ty

--TODO: class for binary validity relation?
class ResourceAlgebra (T: Type u) extends
  OrderedAddCommMonoid T
  -- ,One T
  where
  -- Emulating a partial commutative monoid via `valid`:
  valid: T -> T -> Prop
  valid_id x: valid 0 x
  valid_symm: ∀ x y, valid x y -> valid y x
  valid_assoc_mp: ∀ x y z, valid x y -> valid y z ->
    valid (x + y) z -> valid x (y + z)
  valid_assoc_mpr: ∀x y z: T,  valid x y -> valid y z
    -> valid x (y + z) -> valid (x + y) z
    := λ x y z Hxy Hyz Hxyz
      => valid_symm _ _ ((add_comm x y) ▸ valid_assoc_mp z y x
        (valid_symm _ _ Hyz)
        (valid_symm _ _ Hxy)
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
  valid_symm _ _ | Hxy => Hxy.elim Or.inr Or.inl
  valid_assoc_mp _ _ _
    | Or.inl Hx, _, _ => Or.inl Hx
    | Or.inr Hy, _, Or.inr Hz => by simp [Hy, Hz]
    | Or.inr Hy, _, Or.inl Hxy => by rw [<-Hxy]; simp [Hy]

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
  valid_symm := R.valid_symm
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
  valid_symm _ _ | Hxy => Hxy.elim Or.inr Or.inl
  valid_assoc_mp _ _ _
    | Or.inl Hx, _, _ => Or.inl Hx
    | Or.inr Hy, _, Or.inr Hz => by simp [Hy, Hz]
    | Or.inr Hy, _, Or.inl Hxy => by rw [<-Hxy]; simp [Hy]

def ResourceAlgebra.linearSubalgebra (T: Type u) [R: ResourceAlgebra T]
  : (linearAlgebra T).Subalgebra R where
  add_eq := rfl
  le_sub _ _ | rfl => le_refl _
  valid_sub _ _
    | Or.inl H => H ▸ (valid_id _)
    | Or.inr H => H ▸ (valid_symm _ _ (valid_id _))

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
  valid_symm _ _
    | Or.inl Hxy => Or.inl ⟨Hxy.1, R.valid_symm _ _ Hxy.2⟩
    | Or.inr Hxy => Or.inr (Or.elim Hxy Or.inr Or.inl)
  valid_assoc_mp x y z
    | Or.inl ⟨Hr, Hxy⟩, Hyz, Hxyz
      => Or.inl ⟨Hr, R.valid_assoc_mp _ _ _ Hxy
        (match Hyz with
          | Or.inl H => H.2
          | Or.inr (Or.inl H) => H ▸ R.valid_id _
          | Or.inr (Or.inr H) => H ▸ R.valid_symm _ _ (R.valid_id _) )
        (match Hxyz with
          | Or.inl H => H.2
          | Or.inr (Or.inl H) => H ▸ R.valid_id _
          | Or.inr (Or.inr H) => H ▸ R.valid_symm _ _ (R.valid_id _) )⟩
    | Or.inr (Or.inl Hx), _, _ => Or.inr (Or.inl Hx)
    | Or.inr (Or.inr Hy), Hz, Or.inl ⟨Hr, Hyz⟩ =>
      Or.inl ⟨Hr, by simp only [Hy, add_zero, zero_add] at *; exact Hyz⟩
    | Or.inr (Or.inr Hy), _, Or.inr (Or.inr Hz) => by simp [Hy, Hz]
    | Or.inr (Or.inr Hy), _, Or.inr (Or.inl Hxy) => by rw [<-Hxy]; simp [Hy]

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
  valid_symm := by intros; trivial
  valid_assoc_mp := by intros; trivial

instance ResourceAlgebra.instResourceAlgebraPair {A B}
  [ResourceAlgebra A] [ResourceAlgebra B]
  : ResourceAlgebra (A × B) where
  valid | ⟨xa, xb⟩, ⟨ya, yb⟩ => valid xa ya ∧ valid xb yb
  valid_id | ⟨a, b⟩ => ⟨valid_id a, valid_id b⟩
  valid_symm _ _ | ⟨Ha, Hb⟩ => ⟨valid_symm _ _ Ha, valid_symm _ _ Hb⟩
  valid_assoc_mp _ _ _
    | ⟨Hxya, Hxyb⟩, ⟨Hyza, Hyzb⟩, ⟨Hxyza, Hxyzb⟩
    => ⟨valid_assoc_mp _ _ _ Hxya Hyza Hxyza,
        valid_assoc_mp _ _ _ Hxyb Hyzb Hxyzb⟩

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

def ResourceAlgebra.splits {T: Type u} [ResourceAlgebra T]
  (x l r: T): Prop := x ≥ l + r ∧ valid l r

def ResourceAlgebra.qsplits {T: Type u} [ResourceAlgebra T]
  (q: Transparency) (x l r: T): Prop
  := @splits T (ResourceAlgebra.transparentAlgebra T q) x l r

theorem ResourceAlgebra.qsplits_rel {T: Type u} [ResourceAlgebra T]
  {q} {x l r: T}: qsplits q x l r -> q.rel ∨ l = 0 ∨ r = 0
  | ⟨_, Or.inl Hv⟩ => Or.inl Hv.1
  | ⟨_, Or.inr Hv⟩ => Or.inr Hv

theorem ResourceAlgebra.qsplits_aff {T: Type u} [ResourceAlgebra T]
  {q} {x l r: T}: qsplits q x l r -> q.aff ∨ l + r = x
  | ⟨Or.inl H, _⟩ => Or.inl H.1
  | ⟨Or.inr H, _⟩ => Or.inr H
