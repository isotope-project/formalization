import Mathlib.Order.Monotone.Basic
import Mathlib.Init.Function
import Mathlib.Logic.Function.Basic
import Aesop

/--A weakening, corresponding to a monotonic map from `1..n` to `1..m` where `m >= n`-/

inductive Wk: Type where
  | /-- The identity weakening, which maps all integers to themselves -/
  id: Wk
  | /-- `ρ.step` maps `n` to `(ρ n) + 1` -/
  step: Wk -> Wk
  | /-- `ρ.lift` leaves `0` unchanged and maps `n + 1` to `(ρ n) + 1` -/
  lift: Wk -> Wk
deriving Inhabited, DecidableEq, Repr

/-- The weakening mapping `n` to `n + 1` -/
abbrev Wk.wk1: Wk := step id

/-- `ρ.stepn n` maps numbers `k` to `(ρ k) + n`` -/
def Wk.stepn: Wk -> Nat -> Wk
  | ρ, 0 => ρ
  | ρ, Nat.succ n => Wk.step (ρ.stepn n)

theorem Wk.stepn_0 (ρ: Wk): ρ.stepn 0 = ρ := rfl
theorem Wk.stepn_1 (ρ: Wk): ρ.stepn 1 = ρ.step := rfl
theorem Wk.stepn_succ (ρ: Wk) (n: Nat): ρ.stepn (n + 1) = (ρ.stepn n).step := rfl
theorem Wk.stepn_step (ρ: Wk) (n: Nat): (ρ.stepn n).step = ρ.stepn (n + 1) := rfl
theorem Wk.step_stepn (ρ: Wk) (n: Nat): (ρ.step).stepn n = ρ.stepn (n + 1)
  := by induction n <;> simp [stepn, *]
theorem Wk.step_stepn_comm (ρ: Wk) (n: Nat): (ρ.step).stepn n = (ρ.stepn n).step
  := by rw [step_stepn, stepn_step]
theorem Wk.stepn_add (ρ: Wk) (n m: Nat): (ρ.stepn n).stepn m = ρ.stepn (n + m)
  := by induction m <;> simp [stepn, *]
theorem Wk.stepn_comm (ρ: Wk) (n m: Nat): (ρ.stepn n).stepn m = (ρ.stepn m).stepn n
  := by simp only [stepn_add, Nat.add_comm]
/-- `ρ.liftn n` is the identity on `0..n` and maps numbers `n + k` to `(ρ k) + n` -/
def Wk.liftn: Wk -> Nat -> Wk
  | ρ, 0 => ρ
  | ρ, Nat.succ n => Wk.lift (ρ.liftn n)

theorem Wk.liftn_0 (ρ: Wk): ρ.liftn 0 = ρ := rfl
theorem Wk.liftn_1 (ρ: Wk): ρ.liftn 1 = ρ.lift := rfl
theorem Wk.liftn_succ (ρ: Wk) (n: Nat)
  : ρ.liftn (n + 1) = (ρ.liftn n).lift := rfl
theorem Wk.liftn_lift (ρ: Wk) (n: Nat)
  : (ρ.liftn n).lift = ρ.liftn (n + 1) := rfl
theorem Wk.lift_liftn (ρ: Wk) (n: Nat): (ρ.lift).liftn n = ρ.liftn (n + 1)
  := by induction n <;> simp [liftn, *]
theorem Wk.lift_liftn_comm (ρ: Wk) (n: Nat): (ρ.lift).liftn n = (ρ.liftn n).lift
  := by rw [lift_liftn, liftn_lift]
theorem Wk.liftn_add (ρ: Wk) (n m: Nat): (ρ.liftn n).liftn m = ρ.liftn (n + m)
  := by induction m <;> simp [liftn, *]
theorem Wk.liftn_comm (ρ: Wk) (n m: Nat)
  : (ρ.liftn n).liftn m = (ρ.liftn m).liftn n
  := by simp only [liftn_add, Nat.add_comm]

/-- `wkn m` maps `n` to `n + m`; equivalent to applying `wk1` `m` times -/
abbrev Wk.wkn (n: Nat): Wk := id.stepn n

theorem Wk.wkn_0: wkn 0 = id := rfl
theorem Wk.wkn_1: wkn 1 = wk1 := rfl
theorem Wk.wk1_wkn1: wk1 = wkn 1 := rfl
theorem Wk.wkn_succ (n: Nat): wkn (n + 1) = (wkn n).step := rfl
theorem Wk.wkn_step (n: Nat): (wkn n).step = wkn (n + 1) := rfl
theorem Wk.wkn_stepn (n m: Nat): (wkn n).stepn m = wkn (n + m)
  := by rw [stepn_add]


/-- `ρ.wknth` is the identity on `0..n` and maps numbers `n + k` to `n + k + 1` -/
abbrev Wk.wknth (n: Nat): Wk := wk1.liftn n

theorem Wk.wknth_0: wknth 0 = wk1 := rfl
theorem Wk.wknth_succ (n: Nat): wknth (n + 1) = (wknth n).lift := rfl
theorem Wk.wknth_lift (n: Nat): (wknth n).lift = wknth (n + 1) := rfl
theorem Wk.wknth_liftn (n m: Nat): (wknth n).liftn m = wknth (n + m)
  := by rw [liftn_add]

/-- Apply a weakening to a natural number -/
def Wk.app: Wk -> Nat -> Nat
  | Wk.id, n => n
  | Wk.step ρ, n => (app ρ n) + 1
  | Wk.lift _, 0 => 0
  | Wk.lift ρ, (n + 1) => (app ρ n) + 1

theorem Wk.app_id {n}: id.app n = n := rfl
theorem Wk.app_step {n} (ρ: Wk): ρ.step.app n = (ρ.app n).succ := rfl
theorem Wk.app_wk1 {n}: wk1.app n = n.succ := rfl
theorem Wk.app_wkn {n m}: (wkn n).app m = m + n := by induction n with
  | zero => rfl
  | succ _ I => simp only [wkn, stepn, app_step, Nat.add_succ, I]
theorem Wk.app_step_fn (ρ: Wk): ρ.step.app = λx => (ρ.app x).succ := rfl
theorem Wk.app_lift_0 (ρ: Wk): ρ.lift.app 0 = 0 := rfl
theorem Wk.app_lift_1 (ρ: Wk): ρ.lift.app 1 = (ρ.app 0).succ := rfl
theorem Wk.app_lift_succ {n} (ρ: Wk): ρ.lift.app (n + 1) = (ρ.app n).succ := rfl
theorem Wk.app_lift {n} (ρ: Wk)
  : ρ.lift.app n = match n with | 0 => 0 | n + 1 => (app ρ n) + 1
  := by cases n <;> rfl
theorem Wk.app_lift_fn (ρ: Wk)
  : ρ.lift.app = λn => match n with | 0 => 0 | n + 1 => (app ρ n) + 1
  := by funext n; rw [app_lift]
theorem Wk.app_liftn {n v} (ρ: Wk)
  : (ρ.liftn n).app v = if v < n then v else (app ρ (v - n)) + n
  := by induction n generalizing v ρ with
     | zero => simp_arith [liftn]
     | succ n I =>
      rw [liftn, app_lift]
      cases v with
      | zero => simp_arith
      | succ v =>
        simp only [I]
        split
        simp_arith only []
        split
        rfl
        contradiction
        simp_arith only []
        split
        contradiction
        simp_arith

theorem Wk.strictMono (ρ: Wk): StrictMono ρ.app
  := λn m H => match ρ with
  | id => H
  | step ρ => Nat.succ_lt_succ (strictMono ρ H)
  | lift ρ => by
    cases n <;> cases m <;> try contradiction
    exact Nat.zero_lt_succ _
    exact Nat.succ_lt_succ (strictMono ρ (Nat.lt_of_succ_lt_succ H))

theorem Wk.monotone (ρ: Wk): Monotone ρ.app
  := λn m H => by rw [ρ.strictMono.le_iff_le]; exact H

theorem Wk.injective (ρ: Wk): Function.Injective ρ.app
  := by rw [<-ρ.monotone.strictMono_iff_injective]; exact ρ.strictMono

theorem Wk.larger (ρ: Wk) (n: Nat): n ≤ ρ.app n
  := match ρ with
  | id => n.le_refl
  | step ρ => Nat.le_trans (larger ρ n) (Nat.le_succ _)
  | lift ρ => match n with
              | 0 => Nat.le_refl 0
              | n + 1 => Nat.succ_le_succ (larger ρ n)

def Wk.comp: Wk -> Wk -> Wk
    | Wk.id, σ => σ
    | Wk.step ρ, σ => Wk.step (comp ρ σ)
    | Wk.lift ρ, Wk.id => Wk.lift ρ
    | Wk.lift ρ, Wk.step σ => Wk.step (comp ρ σ)
    | Wk.lift ρ, Wk.lift σ => Wk.lift (comp ρ σ)
theorem Wk.id_comp (ρ: Wk): id.comp ρ = ρ := rfl
theorem Wk.comp_id (ρ: Wk): ρ.comp id = ρ
  := by induction ρ <;> simp [comp, *]
theorem Wk.wk1_comp (ρ: Wk): wk1.comp ρ = ρ.step := rfl
theorem Wk.comp_assoc (ρ σ τ: Wk): (ρ.comp σ).comp τ = ρ.comp (σ.comp τ)
  := by {
    induction ρ generalizing σ τ <;>
    (try simp only [comp]) <;>
    cases σ <;> cases τ <;>
    simp only [comp, *]
  }

theorem Wk.lift_comp_lift {ρ σ: Wk}: (ρ.lift).comp (σ.lift) = (ρ.comp σ).lift
  := rfl
theorem Wk.liftn_comp_liftn {ρ σ: Wk} {n}
  : (ρ.liftn n).comp (σ.liftn n) = (ρ.comp σ).liftn n
  := by induction n generalizing ρ σ with
    | zero => rfl
    | succ => simp only [liftn_succ, lift_comp_lift, *]
theorem Wk.lift_dist_comp {ρ σ: Wk}: (ρ.comp σ).lift = (ρ.lift).comp (σ.lift)
  := lift_comp_lift.symm
theorem Wk.liftn_dist_comp {ρ σ: Wk} {n}
  : (ρ.comp σ).liftn n = (ρ.liftn n).comp (σ.liftn n)
  := liftn_comp_liftn.symm

-- theorem Wk.wkn_comp_wk1 (n: Nat): (wkn n).comp wk1 = wkn (n + 1)
--   := by induction n <;> simp only [wkn_succ, comp, *]
-- theorem Wk.app_comp (ρ σ: Wk) (n: Nat)
--   : Wk.app (Wk.comp ρ σ) n = Wk.app ρ (Wk.app σ n)
--   := by {
--     induction ρ generalizing σ n <;> cases σ <;> cases n <;> simp [app, *]
--   }


-- def Wk.equiv (ρ σ: Wk) := ρ.app = σ.app

-- theorem Wk.equiv_refl (ρ: Wk): ρ.equiv ρ := rfl
-- theorem Wk.equiv.symm {ρ σ: Wk}: ρ.equiv σ -> σ.equiv ρ := Eq.symm
-- theorem Wk.equiv.trans {ρ σ τ: Wk}
--   : ρ.equiv σ -> σ.equiv τ -> ρ.equiv τ := Eq.trans
-- theorem Wk.equiv.app {ρ σ: Wk}
--   : ρ.equiv σ -> ∀n, ρ.app n = σ.app n := λH n => by rw [H]
-- theorem Wk.equiv.ext {ρ σ: Wk} (H: ∀n, ρ.app n = σ.app n)
--   : ρ.equiv σ := by funext n; apply H

-- def Wk.coherent_inner (f: Wk -> Wk)
--   := ∀{ρ σ: Wk}, ρ.equiv σ -> (f ρ).equiv (f σ)
-- def Wk.coherent {A} (f: Wk -> A) := ∀{ρ σ: Wk}, ρ.equiv σ -> f ρ = f σ

-- theorem Wk.equiv.step: coherent_inner step
--   := λH => by funext n; simp only [Wk.app]; rw [H]
-- theorem Wk.equiv.step_aesop_helper
--   : ∀{ρ σ: Wk}, ρ.equiv σ -> (Wk.step ρ).equiv (Wk.step σ)
--   := Wk.equiv.step
-- theorem Wk.equiv.lift: coherent_inner lift
--   := λH => by funext n; cases n <;> simp only [Wk.app]; rw [H]
-- theorem Wk.equiv.lift_aesop_helper
--   : ∀{ρ σ: Wk}, ρ.equiv σ -> (Wk.lift ρ).equiv (Wk.lift σ)
--   := Wk.equiv.lift
-- theorem Wk.equiv.stepn {ρ σ: Wk} {n} (H: ρ.equiv σ)
--   : (ρ.stepn n).equiv (σ.stepn n)
--   := by induction n with | zero => exact H | succ _ I => exact I.step
-- theorem Wk.equiv.liftn {ρ σ: Wk} {n} (H: ρ.equiv σ)
--   : (ρ.liftn n).equiv (σ.liftn n)
--   := by induction n with | zero => exact H | succ _ I => exact I.lift
-- theorem Wk.equiv.unstep {ρ σ: Wk} (H: ρ.step.equiv σ.step): ρ.equiv σ
--   := by funext n; apply Nat.succ.inj; simp only [<-Wk.app_step]; rw [H]
-- theorem Wk.equiv.unlift {ρ σ: Wk} (H: ρ.lift.equiv σ.lift): ρ.equiv σ
--   := by funext n;
--         have H' := congr H (@rfl _ (n + 1));
--         apply Nat.succ.inj; exact H'
-- theorem Wk.equiv.unstepn {ρ σ: Wk} {n} (H: (ρ.stepn n).equiv (σ.stepn n))
--   : ρ.equiv σ
--   := by induction n with | zero => exact H | succ _ I => exact I (H.unstep)
-- theorem Wk.equiv.unliftn {ρ σ: Wk} {n} (H: (ρ.liftn n).equiv (σ.liftn n))
--   : ρ.equiv σ
--   := by induction n with | zero => exact H | succ _ I => exact I (H.unlift)
-- theorem Wk.lift_id_equiv_id: id.lift.equiv id := by funext n; cases n <;> rfl
-- theorem Wk.equiv.not_step {ρ: Wk}: ¬(ρ.step.equiv id)
--   := Function.ne_iff.mpr ⟨0, by simp [Wk.app]⟩
-- theorem Wk.equiv.lift_equiv_id {ρ: Wk} (H: ρ.equiv id): ρ.lift.equiv id
--   := H.lift.trans lift_id_equiv_id
-- theorem Wk.equiv.liftn_equiv_id {ρ: Wk} (H: ρ.equiv id) (n: Nat): (ρ.liftn n).equiv id
--   := by induction n with
--   | zero => exact H
--   | succ n I => rw [liftn_succ]; exact I.lift_equiv_id
-- theorem Wk.equiv.unlift_equiv_id {ρ: Wk} (H: ρ.lift.equiv id): ρ.equiv id
--   := (H.trans lift_id_equiv_id.symm).unlift
-- theorem Wk.equiv.equiv_id_decomp {ρ: Wk} (H: ρ.equiv id): ∃n, ρ = id.liftn n
--   := match ρ with
--     | Wk.id => ⟨0, rfl⟩
--     | Wk.step _ => H.not_step.elim
--     | Wk.lift ρ =>
--       let ⟨n, p⟩ := H.unlift_equiv_id.equiv_id_decomp;
--       ⟨n.succ, by rw [liftn_succ, p]⟩
-- theorem Wk.equiv_id_char (ρ: Wk): ρ.equiv id ↔ ∃n, ρ = id.liftn n :=
--   ⟨Wk.equiv.equiv_id_decomp, λ⟨n, E⟩ => E ▸ id.equiv_refl.liftn_equiv_id n⟩

-- /-- The source range `0..n` of a weakening -/
-- def Wk.src: Wk -> Nat
--   | id => 0
--   | step ρ => ρ.src
--   | lift ρ => ρ.src + 1

-- /-- The target range `0..m` of a weakening -/
-- def Wk.trg: Wk -> Nat
--   | id => 0
--   | step ρ => ρ.trg + 1
--   | lift ρ => ρ.trg + 1

-- /-- The minimal source range `0..n` of a weakening -/
-- def Wk.min_src: Wk -> Nat
--   | id => 0
--   | step ρ => ρ.min_src
--   | lift ρ => match ρ.min_src with | 0 => 0 | n => n + 1

-- /-- The minimal target range `0..m` of a weakening -/
-- def Wk.min_trg: Wk -> Nat
--   | id => 0
--   | step ρ => ρ.min_trg
--   | lift ρ => match ρ.min_trg with | 0 => 0 | n => n + 1

-- theorem Wk.src_le_trg (ρ: Wk): ρ.src ≤ ρ.trg
--   := by induction ρ with
--   | id => simp
--   | step =>
--     simp only [Wk.src, Wk.trg]
--     apply Nat.le_of_succ_le
--     apply Nat.succ_le_succ
--     assumption
--   | lift => simp only [Wk.src, Wk.trg]; apply Nat.succ_le_succ; assumption

-- def Wk.app_inv: Wk -> Nat -> Nat
--   | Wk.id, n => n
--   | Wk.step _, 0 => 0
--   | Wk.step ρ, n + 1 => (app_inv ρ n)
--   | Wk.lift _, 0 => 0
--   | Wk.lift ρ, (n + 1) => (app_inv ρ n) + 1

-- theorem Wk.app_inv_inv (ρ: Wk) (n: Nat): ρ.app_inv (ρ.app n) = n
--   := by induction ρ generalizing n with
--   | id => rfl
--   | step _ I => exact I _
--   | lift ρ I => cases n
--     <;> simp only [app_inv, Nat.add_zero, Nat.add, I _]

-- theorem Wk.wk1_app_inv (n: Nat): wk1.app_inv n = n - 1 := by cases n <;> aesop
-- theorem Wk.wkn_app_inv (n m: Nat): (wkn n).app_inv m = m - n :=
--   by induction n generalizing m <;> cases m <;> aesop
