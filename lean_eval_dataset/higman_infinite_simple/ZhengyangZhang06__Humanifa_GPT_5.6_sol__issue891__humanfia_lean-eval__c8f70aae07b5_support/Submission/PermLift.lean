import Mathlib

namespace Submission.PermLift

open Equiv

variable {G : Type*} [Group G]

/-- The canonical factorization of a finite permutation, with every formal
transposition interpreted by `tr`. -/
def lift : (n : ℕ) → (Fin n → Fin n → G) → Equiv.Perm (Fin n) → G
  | 0, _, _ => 1
  | n + 1, tr, e =>
      let d := Equiv.Perm.decomposeFin e
      tr 0 d.1 * lift n (fun i j => tr i.succ j.succ) d.2

theorem decompose_apply_zero {n : ℕ} (e : Equiv.Perm (Fin (n + 1))) :
    e 0 = (Equiv.Perm.decomposeFin e).1 := by
  calc
    e 0 = Equiv.Perm.decomposeFin.symm (Equiv.Perm.decomposeFin e) 0 := by
      rw [Equiv.Perm.decomposeFin.symm_apply_apply]
    _ = (Equiv.Perm.decomposeFin e).1 :=
      Equiv.Perm.decomposeFin_symm_apply_zero _ _

theorem decompose_apply_succ {n : ℕ} (e : Equiv.Perm (Fin (n + 1)))
    (k : Fin n) :
    e k.succ = Equiv.swap 0 (Equiv.Perm.decomposeFin e).1
      ((Equiv.Perm.decomposeFin e).2 k).succ := by
  calc
    e k.succ = Equiv.Perm.decomposeFin.symm (Equiv.Perm.decomposeFin e) k.succ := by
      rw [Equiv.Perm.decomposeFin.symm_apply_apply]
    _ = _ := Equiv.Perm.decomposeFin_symm_apply_succ _ _ _

theorem equiv_apply_swap {α : Type*} [DecidableEq α] (e : α ≃ α) (a b x : α) :
    e (Equiv.swap a b x) = Equiv.swap (e a) (e b) (e x) := by
  have h := congrArg (fun f : α ≃ α => f (e x))
    (Equiv.symm_trans_swap_trans a b e)
  change e (Equiv.swap a b (e.symm (e x))) =
    Equiv.swap (e a) (e b) (e x) at h
  rw [e.symm_apply_apply] at h
  exact h

@[simp] theorem swap_succ_apply {n : ℕ} (a b x : Fin n) :
    Equiv.swap a.succ b.succ x.succ = (Equiv.swap a b x).succ := by
  simp only [Equiv.swap_apply_def, Fin.succ_inj]
  split_ifs <;> rfl

@[simp] theorem swap_succ_zero {n : ℕ} (a b : Fin n) :
    Equiv.swap a.succ b.succ (0 : Fin (n + 1)) = 0 := by
  apply Equiv.swap_apply_of_ne_of_ne
  · exact (Fin.succ_ne_zero a).symm
  · exact (Fin.succ_ne_zero b).symm

theorem decompose_tail_swap {n : ℕ} (e : Equiv.Perm (Fin (n + 1)))
    (i j : Fin n) :
    Equiv.Perm.decomposeFin (Equiv.swap i.succ j.succ * e) =
      (Equiv.swap i.succ j.succ (Equiv.Perm.decomposeFin e).1,
        Equiv.swap i j * (Equiv.Perm.decomposeFin e).2) := by
  apply Equiv.Perm.decomposeFin.symm.injective
  rw [Equiv.Perm.decomposeFin.symm_apply_apply]
  apply Equiv.ext
  intro x
  refine Fin.cases ?_ (fun k => ?_) x
  · simp [Equiv.Perm.mul_apply, decompose_apply_zero]
  · simp only [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.Perm.mul_apply]
    rw [decompose_apply_succ]
    change Equiv.swap i.succ j.succ
        (Equiv.swap 0 (Equiv.Perm.decomposeFin e).1
          (((Equiv.Perm.decomposeFin e).2 k).succ)) =
      Equiv.swap 0
        (Equiv.swap i.succ j.succ (Equiv.Perm.decomposeFin e).1)
        ((Equiv.swap i j ((Equiv.Perm.decomposeFin e).2 k)).succ)
    rw [equiv_apply_swap]
    simp

theorem decompose_zero_swap_of_zero {n : ℕ} (e : Equiv.Perm (Fin (n + 1)))
    (j : Fin n) (hp : (Equiv.Perm.decomposeFin e).1 = 0) :
    Equiv.Perm.decomposeFin (Equiv.swap 0 j.succ * e) =
      (j.succ, (Equiv.Perm.decomposeFin e).2) := by
  apply Equiv.Perm.decomposeFin.symm.injective
  rw [Equiv.Perm.decomposeFin.symm_apply_apply]
  apply Equiv.ext
  intro x
  refine Fin.cases ?_ (fun k => ?_) x
  · rw [Equiv.Perm.mul_apply, decompose_apply_zero, hp]
    simp
  · rw [Equiv.Perm.mul_apply, decompose_apply_succ, hp]
    simp only [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def]
    by_cases hk : (Equiv.Perm.decomposeFin e).2 k = j <;> simp [hk]

theorem decompose_zero_swap_of_eq {n : ℕ} (e : Equiv.Perm (Fin (n + 1)))
    (j : Fin n) (hp : (Equiv.Perm.decomposeFin e).1 = j.succ) :
    Equiv.Perm.decomposeFin (Equiv.swap 0 j.succ * e) =
      (0, (Equiv.Perm.decomposeFin e).2) := by
  apply Equiv.Perm.decomposeFin.symm.injective
  rw [Equiv.Perm.decomposeFin.symm_apply_apply]
  apply Equiv.ext
  intro x
  refine Fin.cases ?_ (fun k => ?_) x
  · rw [Equiv.Perm.mul_apply, decompose_apply_zero, hp]
    simp
  · rw [Equiv.Perm.mul_apply, decompose_apply_succ, hp]
    let y := (Equiv.Perm.decomposeFin e).2 k
    change Equiv.swap 0 j.succ (Equiv.swap 0 j.succ y.succ) = y.succ
    exact Equiv.swap_apply_self 0 j.succ y.succ

theorem decompose_zero_swap_of_ne {n : ℕ} (e : Equiv.Perm (Fin (n + 1)))
    (j p : Fin n) (hp : (Equiv.Perm.decomposeFin e).1 = p.succ) (hne : p ≠ j) :
    Equiv.Perm.decomposeFin (Equiv.swap 0 j.succ * e) =
      (p.succ, Equiv.swap p j * (Equiv.Perm.decomposeFin e).2) := by
  apply Equiv.Perm.decomposeFin.symm.injective
  rw [Equiv.Perm.decomposeFin.symm_apply_apply]
  apply Equiv.ext
  intro x
  refine Fin.cases ?_ (fun k => ?_) x
  · rw [Equiv.Perm.mul_apply, decompose_apply_zero, hp]
    simp [Equiv.swap_apply_def, hne]
  · simp only [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.Perm.mul_apply]
    rw [decompose_apply_succ, hp]
    change Equiv.swap 0 j.succ
        (Equiv.swap 0 p.succ (((Equiv.Perm.decomposeFin e).2 k).succ)) =
      Equiv.swap 0 p.succ
        ((Equiv.swap p j ((Equiv.Perm.decomposeFin e).2 k)).succ)
    let y := (Equiv.Perm.decomposeFin e).2 k
    change Equiv.swap 0 j.succ (Equiv.swap 0 p.succ y.succ) =
      Equiv.swap 0 p.succ (Equiv.swap p j y).succ
    by_cases hyp : y = p
    · rw [hyp]
      simp [Equiv.swap_apply_def, Ne.symm hne]
    · by_cases hyj : y = j
      · rw [hyj]
        simp [Equiv.swap_apply_def, Ne.symm hne]
      · simp [Equiv.swap_apply_def, hyp, hyj]

theorem conjugate_move {n : ℕ} (tr : Fin n → Fin n → G)
    (hconj : ∀ a b c d,
      tr a b * tr c d * (tr a b)⁻¹ =
        tr (Equiv.swap a b c) (Equiv.swap a b d))
    (a b c d : Fin n) :
    tr (Equiv.swap a b c) (Equiv.swap a b d) * tr a b =
      tr a b * tr c d := by
  rw [← hconj]
  simp [mul_assoc]

@[simp] theorem decompose_one {n : ℕ} :
    Equiv.Perm.decomposeFin (1 : Equiv.Perm (Fin (n + 1))) = (0, 1) := by
  apply Equiv.Perm.decomposeFin.symm.injective
  simp
  rfl

theorem lift_one : ∀ (n : ℕ) (tr : Fin n → Fin n → G)
    (_hone : ∀ i, tr i i = 1), lift n tr 1 = 1 := by
  intro n
  induction n with
  | zero => intro tr _; rfl
  | succ n ih =>
      intro tr hone
      rw [lift, decompose_one]
      rw [hone 0, one_mul]
      exact ih _ (fun i => hone i.succ)

theorem lift_swap_mul : ∀ (n : ℕ) (tr : Fin n → Fin n → G),
    (∀ i, tr i i = 1) →
    (∀ i j, tr i j = tr j i) →
    (∀ i j, tr i j * tr i j = 1) →
    (∀ a b c d,
      tr a b * tr c d * (tr a b)⁻¹ =
        tr (Equiv.swap a b c) (Equiv.swap a b d)) →
    ∀ (e : Equiv.Perm (Fin n)) (a b : Fin n),
      lift n tr (Equiv.swap a b * e) = tr a b * lift n tr e := by
  intro n
  induction n with
  | zero =>
      intro tr hone hsymm hsq hconj e a
      exact Fin.elim0 a
  | succ n ih =>
      intro tr hone hsymm hsq hconj e a b
      have hswapSucc (a b c : Fin n) :
          Equiv.swap a.succ b.succ c.succ = (Equiv.swap a b c).succ := by
        simp only [Equiv.swap_apply_def]
        split_ifs <;> simp_all
      have ihTail := ih (fun i j => tr i.succ j.succ)
        (fun i => hone i.succ) (fun i j => hsymm i.succ j.succ)
        (fun i j => hsq i.succ j.succ)
        (fun a b c d => by
          simpa only [hswapSucc] using hconj a.succ b.succ c.succ d.succ)
      have hzero (j : Fin n) :
          lift (n + 1) tr (Equiv.swap 0 j.succ * e) =
            tr 0 j.succ * lift (n + 1) tr e := by
        rcases Fin.eq_zero_or_eq_succ (Equiv.Perm.decomposeFin e).1 with hp | ⟨p, hp⟩
        · rw [lift, decompose_zero_swap_of_zero e j hp, lift]
          simp only [hp, hone, one_mul]
        · by_cases hpj : p = j
          · subst p
            rw [lift, decompose_zero_swap_of_eq e j hp, lift]
            simp only [hp, hone, one_mul]
            rw [← mul_assoc, hsq, one_mul]
          · rw [lift, decompose_zero_swap_of_ne e j p hp hpj, lift, ihTail]
            simp only [hp]
            rw [← mul_assoc]
            have hmove := conjugate_move tr hconj 0 p.succ p.succ j.succ
            have hswapP : Equiv.swap 0 p.succ p.succ = 0 := by
              simp
            have hswapJ : Equiv.swap 0 p.succ j.succ = j.succ := by
              apply Equiv.swap_apply_of_ne_of_ne
              · exact Fin.succ_ne_zero j
              · exact fun h => hpj (Fin.succ_injective n h.symm)
            rw [hswapP, hswapJ] at hmove
            rw [hmove.symm, mul_assoc]
      refine Fin.cases ?_ (fun i => ?_) a
      · refine Fin.cases ?_ (fun j => ?_) b
        · have hs : Equiv.swap (0 : Fin (n + 1)) 0 = 1 := by
            ext x
            simp
          rw [hs, one_mul, hone 0, one_mul]
        · exact hzero j
      · refine Fin.cases ?_ (fun j => ?_) b
        · rw [Equiv.swap_comm, hzero i, hsymm]
        · let d := Equiv.Perm.decomposeFin e
          rw [lift, decompose_tail_swap e i j, lift, ihTail]
          dsimp only
          rw [← mul_assoc]
          have hmove := conjugate_move tr hconj i.succ j.succ 0 d.1
          have hzeroFixed : Equiv.swap i.succ j.succ 0 = 0 := by
            apply Equiv.swap_apply_of_ne_of_ne
            · exact (Fin.succ_ne_zero i).symm
            · exact (Fin.succ_ne_zero j).symm
          rw [hzeroFixed] at hmove
          rw [hmove, mul_assoc]

theorem lift_mul : ∀ (n : ℕ) (tr : Fin n → Fin n → G),
    (∀ i, tr i i = 1) →
    (∀ i j, tr i j = tr j i) →
    (∀ i j, tr i j * tr i j = 1) →
    (∀ a b c d,
      tr a b * tr c d * (tr a b)⁻¹ =
        tr (Equiv.swap a b c) (Equiv.swap a b d)) →
    ∀ e f : Equiv.Perm (Fin n), lift n tr (e * f) = lift n tr e * lift n tr f := by
  intro n tr hone hsymm hsq hconj e
  induction e using Equiv.Perm.swap_induction_on with
  | one =>
      intro f
      simp [lift_one n tr hone]
  | swap_mul e a b hab ih =>
      intro f
      rw [mul_assoc, lift_swap_mul n tr hone hsymm hsq hconj,
        lift_swap_mul n tr hone hsymm hsq hconj, ih, ← mul_assoc]

/-- The transposition presentation of a finite symmetric group. -/
def hom (n : ℕ) (tr : Fin n → Fin n → G)
    (hone : ∀ i, tr i i = 1)
    (hsymm : ∀ i j, tr i j = tr j i)
    (hsq : ∀ i j, tr i j * tr i j = 1)
    (hconj : ∀ a b c d,
      tr a b * tr c d * (tr a b)⁻¹ =
        tr (Equiv.swap a b c) (Equiv.swap a b d)) :
    Equiv.Perm (Fin n) →* G where
  toFun := lift n tr
  map_one' := lift_one n tr hone
  map_mul' := lift_mul n tr hone hsymm hsq hconj

@[simp] theorem hom_swap (n : ℕ) (tr : Fin n → Fin n → G)
    (hone : ∀ i, tr i i = 1)
    (hsymm : ∀ i j, tr i j = tr j i)
    (hsq : ∀ i j, tr i j * tr i j = 1)
    (hconj : ∀ a b c d,
      tr a b * tr c d * (tr a b)⁻¹ =
        tr (Equiv.swap a b c) (Equiv.swap a b d))
    (a b : Fin n) :
    hom n tr hone hsymm hsq hconj (Equiv.swap a b) = tr a b := by
  simpa [hom, lift_one n tr hone] using
    lift_swap_mul n tr hone hsymm hsq hconj (1 : Equiv.Perm (Fin n)) a b

end Submission.PermLift

namespace Submission.PermLift.Tower

open Equiv

variable {G : Type*} [Group G]

/-- The transposition between the first point and a point in its tail.  The
base element `s` exchanges the two points at the bottom of the tower, while
`h` is the stable exchange of the first two points once a further tail is
present. -/
def cross (r : G →* G) (s h : G) : (n : ℕ) → Fin (n + 1) → G
  | 0, _ => s
  | n + 1, j => Fin.cases h
      (fun k => r (cross r s h n k) * h * (r (cross r s h n k))⁻¹) j

@[simp] theorem cross_zero (r : G →* G) (s h : G) (j : Fin 1) :
    cross r s h 0 j = s :=
  rfl

@[simp] theorem cross_succ_zero (r : G →* G) (s h : G) (n : ℕ) :
    cross r s h (n + 1) 0 = h :=
  rfl

@[simp] theorem cross_succ_succ (r : G →* G) (s h : G) (n : ℕ)
    (j : Fin (n + 1)) :
    cross r s h (n + 1) j.succ =
      r (cross r s h n j) * h * (r (cross r s h n j))⁻¹ :=
  rfl

/-- All transpositions on `Fin (n + 1)`, obtained by putting a smaller tower
in the tail and adjoining the first-point transpositions. -/
def trans (r : G →* G) (s h : G) :
    (n : ℕ) → Fin (n + 1) → Fin (n + 1) → G
  | 0, _, _ => 1
  | n + 1, i, j =>
      Fin.cases
        (Fin.cases 1 (fun k => cross r s h n k) j)
        (fun k => Fin.cases (cross r s h n k)
          (fun l => r (trans r s h n k l)) j) i

@[simp] theorem trans_zero (r : G →* G) (s h : G) (i j : Fin 1) :
    trans r s h 0 i j = 1 :=
  rfl

@[simp] theorem trans_succ_zero_zero (r : G →* G) (s h : G) (n : ℕ) :
    trans r s h (n + 1) 0 0 = 1 :=
  rfl

@[simp] theorem trans_succ_zero_succ (r : G →* G) (s h : G) (n : ℕ)
    (j : Fin (n + 1)) :
    trans r s h (n + 1) 0 j.succ = cross r s h n j :=
  rfl

@[simp] theorem trans_succ_succ_zero (r : G →* G) (s h : G) (n : ℕ)
    (i : Fin (n + 1)) :
    trans r s h (n + 1) i.succ 0 = cross r s h n i :=
  rfl

@[simp] theorem trans_succ_succ_succ (r : G →* G) (s h : G) (n : ℕ)
    (i j : Fin (n + 1)) :
    trans r s h (n + 1) i.succ j.succ = r (trans r s h n i j) :=
  rfl

theorem cross_sq (r : G →* G) (s h : G) (hs : s * s = 1)
    (hh : h * h = 1) (n : ℕ) (j : Fin (n + 1)) :
    cross r s h n j * cross r s h n j = 1 := by
  induction n with
  | zero => simpa using hs
  | succ n ih =>
      refine Fin.cases ?_ (fun k => ?_) j
      · simpa using hh
      · simp only [cross_succ_succ]
        calc
          (r (cross r s h n k) * h * (r (cross r s h n k))⁻¹) *
                (r (cross r s h n k) * h * (r (cross r s h n k))⁻¹) =
              r (cross r s h n k) * (h * h) *
                (r (cross r s h n k))⁻¹ := by group
          _ = 1 := by rw [hh]; simp

@[simp] theorem cross_inv (r : G →* G) (s h : G) (hs : s * s = 1)
    (hh : h * h = 1) (n : ℕ) (j : Fin (n + 1)) :
    (cross r s h n j)⁻¹ = cross r s h n j := by
  exact (eq_inv_of_mul_eq_one_right (cross_sq r s h hs hh n j)).symm

theorem trans_one (r : G →* G) (s h : G) (n : ℕ) (i : Fin (n + 1)) :
    trans r s h n i i = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      refine Fin.cases ?_ (fun k => ?_) i
      · rfl
      · simp [ih]

theorem trans_symm (r : G →* G) (s h : G) (n : ℕ) (i j : Fin (n + 1)) :
    trans r s h n i j = trans r s h n j i := by
  induction n with
  | zero => rfl
  | succ n ih =>
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j <;> rfl
      · refine Fin.cases ?_ (fun j => ?_) j
        · rfl
        · simp [ih i j]

theorem trans_sq (r : G →* G) (s h : G) (hs : s * s = 1)
    (hh : h * h = 1) (n : ℕ) (i j : Fin (n + 1)) :
    trans r s h n i j * trans r s h n i j = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp
        · exact cross_sq r s h hs hh n j
      · refine Fin.cases ?_ (fun j => ?_) j
        · exact cross_sq r s h hs hh n i
        · simpa using congrArg r (ih i j)

@[simp] theorem trans_inv (r : G →* G) (s h : G) (hs : s * s = 1)
    (hh : h * h = 1) (n : ℕ) (i j : Fin (n + 1)) :
    (trans r s h n i j)⁻¹ = trans r s h n i j := by
  exact (eq_inv_of_mul_eq_one_right (trans_sq r s h hs hh n i j)).symm

/-- The stable first transposition braids with every first transposition in
the localized tail. -/
theorem cross_braid (r : G →* G) (s h : G)
    (hfar : ∀ z, Commute h (r (r z)))
    (hbraidS : h * r s * h = r s * h * r s)
    (hbraidH : h * r h * h = r h * h * r h)
    (n : ℕ) (j : Fin (n + 1)) :
    h * r (cross r s h n j) * h =
      r (cross r s h n j) * h * r (cross r s h n j) := by
  induction n with
  | zero => simpa using hbraidS
  | succ n ih =>
      refine Fin.cases ?_ (fun k => ?_) j
      · simpa using hbraidH
      · let u := r (r (cross r s h n k))
        let v := r h
        have hhu : h * u = u * h := (hfar (cross r s h n k)).eq
        have hhuInv : h * u⁻¹ = u⁻¹ * h :=
          (hfar (cross r s h n k)).inv_right.eq
        have huConj : u⁻¹ * h * u = h := by
          calc
            u⁻¹ * h * u = u⁻¹ * (h * u) := by group
            _ = u⁻¹ * (u * h) := by rw [hhu]
            _ = h := by group
        simp only [cross_succ_succ, map_mul, map_inv]
        change h * (u * v * u⁻¹) * h =
          (u * v * u⁻¹) * h * (u * v * u⁻¹)
        calc
          h * (u * v * u⁻¹) * h = (h * u) * v * (u⁻¹ * h) := by group
          _ = (u * h) * v * (h * u⁻¹) := by rw [hhu, hhuInv.symm]
          _ = u * (h * v * h) * u⁻¹ := by group
          _ = u * (v * h * v) * u⁻¹ := by rw [hbraidH]
          _ = u * v * h * v * u⁻¹ := by group
          _ = u * v * (u⁻¹ * h * u) * v * u⁻¹ := by rw [huConj]
          _ = (u * v * u⁻¹) * h * (u * v * u⁻¹) := by group

/-! The following extension lemma is the algebraic heart of the tower.  It
is the usual induction which obtains the transposition presentation of
`S_(n+2)` from that of `S_(n+1)`. -/

def adjoinCross {n : ℕ} (u : Fin (n + 1) → Fin (n + 1) → G) (h : G)
    (i : Fin (n + 1)) : G :=
  u 0 i * h * (u 0 i)⁻¹

def adjoinTrans {n : ℕ} (u : Fin (n + 1) → Fin (n + 1) → G) (h : G)
    (i j : Fin (n + 2)) : G :=
  Fin.cases
    (Fin.cases 1 (fun k => adjoinCross u h k) j)
    (fun k => Fin.cases (adjoinCross u h k) (fun l => u k l) j) i

@[simp] theorem adjoinTrans_zero_zero {n : ℕ}
    (u : Fin (n + 1) → Fin (n + 1) → G) (h : G) :
    adjoinTrans u h 0 0 = 1 :=
  rfl

@[simp] theorem adjoinTrans_zero_succ {n : ℕ}
    (u : Fin (n + 1) → Fin (n + 1) → G) (h : G) (j : Fin (n + 1)) :
    adjoinTrans u h 0 j.succ = adjoinCross u h j :=
  rfl

@[simp] theorem adjoinTrans_succ_zero {n : ℕ}
    (u : Fin (n + 1) → Fin (n + 1) → G) (h : G) (i : Fin (n + 1)) :
    adjoinTrans u h i.succ 0 = adjoinCross u h i :=
  rfl

@[simp] theorem adjoinTrans_succ_succ {n : ℕ}
    (u : Fin (n + 1) → Fin (n + 1) → G) (h : G) (i j : Fin (n + 1)) :
    adjoinTrans u h i.succ j.succ = u i j :=
  rfl

theorem adjoinCross_sq {n : ℕ}
    (u : Fin (n + 1) → Fin (n + 1) → G) (h : G)
    (hh : h * h = 1) (i : Fin (n + 1)) :
    adjoinCross u h i * adjoinCross u h i = 1 := by
  calc
    adjoinCross u h i * adjoinCross u h i =
        u 0 i * (h * h) * (u 0 i)⁻¹ := by
          simp only [adjoinCross]
          group
    _ = 1 := by rw [hh]; simp

@[simp] theorem adjoinCross_inv {n : ℕ}
    (u : Fin (n + 1) → Fin (n + 1) → G) (h : G)
    (hh : h * h = 1) (i : Fin (n + 1)) :
    (adjoinCross u h i)⁻¹ = adjoinCross u h i := by
  exact (eq_inv_of_mul_eq_one_right (adjoinCross_sq u h hh i)).symm

theorem adjoinTrans_conj {n : ℕ}
    (u : Fin (n + 1) → Fin (n + 1) → G) (h : G)
    (hone : ∀ i, u i i = 1)
    (hsymm : ∀ i j, u i j = u j i)
    (hsq : ∀ i j, u i j * u i j = 1)
    (hconj : ∀ a b c d,
      u a b * u c d * (u a b)⁻¹ =
        u (Equiv.swap a b c) (Equiv.swap a b d))
    (hh : h * h = 1)
    (hfar : ∀ i j : Fin n, Commute h (u i.succ j.succ))
    (hbraid : ∀ j : Fin n,
      h * u 0 j.succ * h = u 0 j.succ * h * u 0 j.succ) :
    ∀ a b c d,
      adjoinTrans u h a b * adjoinTrans u h c d *
          (adjoinTrans u h a b)⁻¹ =
        adjoinTrans u h (Equiv.swap a b c) (Equiv.swap a b d) := by
  have huInv (i j : Fin (n + 1)) : (u i j)⁻¹ = u i j :=
    (eq_inv_of_mul_eq_one_right (hsq i j)).symm
  have hhInv : h⁻¹ = h :=
    (eq_inv_of_mul_eq_one_right hh).symm
  have hcrossZero : adjoinCross u h 0 = h := by
    simp [adjoinCross, hone]
  have htransOne (i : Fin (n + 2)) : adjoinTrans u h i i = 1 := by
    refine Fin.cases rfl (fun k => ?_) i
    exact hone k
  have htransSymm (i j : Fin (n + 2)) :
      adjoinTrans u h i j = adjoinTrans u h j i := by
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases rfl (fun _ => rfl) j
    · refine Fin.cases rfl (fun j => ?_) j
      exact hsymm i j
  have hA_tail (a b : Fin n) (k : Fin (n + 1)) :
      u a.succ b.succ * adjoinCross u h k * (u a.succ b.succ)⁻¹ =
        adjoinCross u h (Equiv.swap a.succ b.succ k) := by
    let q := u a.succ b.succ
    have hqh : (MulAut.conj q) h = h := by
      change q * h * q⁻¹ = h
      calc
        q * h * q⁻¹ = h * q * q⁻¹ := by rw [(hfar a b).symm.eq]
        _ = h := by group
    change (MulAut.conj q) (adjoinCross u h k) = _
    simp only [adjoinCross, map_mul, map_inv]
    have hqu : (MulAut.conj q) (u 0 k) =
        u 0 (Equiv.swap a.succ b.succ k) := by
      have hc := hconj a.succ b.succ 0 k
      have hzero : Equiv.swap a.succ b.succ 0 = 0 := by
        apply Equiv.swap_apply_of_ne_of_ne
        · exact (Fin.succ_ne_zero a).symm
        · exact (Fin.succ_ne_zero b).symm
      rw [hzero] at hc
      exact hc
    rw [hqu, hqh]
  have hA_zero (b : Fin n) (k : Fin (n + 1)) :
      u 0 b.succ * adjoinCross u h k * (u 0 b.succ)⁻¹ =
        adjoinCross u h (Equiv.swap 0 b.succ k) := by
    refine Fin.cases ?_ (fun l => ?_) k
    · rw [hcrossZero]
      rfl
    · by_cases hlb : l = b
      · subst l
        rw [Equiv.swap_apply_right]
        rw [hcrossZero]
        simp only [adjoinCross, huInv]
        calc
          u 0 b.succ * (u 0 b.succ * h * u 0 b.succ) * u 0 b.succ =
              (u 0 b.succ * u 0 b.succ) * h *
                (u 0 b.succ * u 0 b.succ) := by group
          _ = h := by rw [hsq]; simp
      · let q := u 0 b.succ
        change (MulAut.conj q) (adjoinCross u h l.succ) = _
        simp only [adjoinCross, map_mul, map_inv]
        have hqu : (MulAut.conj q) (u 0 l.succ) = u b.succ l.succ := by
          simpa [q, Equiv.swap_apply_def, hlb] using hconj 0 b.succ 0 l.succ
        have hqh : (MulAut.conj q) h = adjoinCross u h b.succ := by
          rfl
        rw [hqu, hqh]
        have hsOuter : Equiv.swap 0 b.succ l.succ = l.succ := by
          apply Equiv.swap_apply_of_ne_of_ne
          · exact Fin.succ_ne_zero l
          · exact fun heq => hlb (Fin.succ_injective n heq)
        rw [hsOuter]
        simpa only [adjoinCross, Equiv.swap_apply_left] using hA_tail b l b.succ
  have hA (a b k : Fin (n + 1)) :
      u a b * adjoinCross u h k * (u a b)⁻¹ =
        adjoinCross u h (Equiv.swap a b k) := by
    refine Fin.cases ?_ (fun a => ?_) a
    · refine Fin.cases ?_ (fun b => ?_) b
      · simp [hone]
      · exact hA_zero b k
    · refine Fin.cases ?_ (fun b => ?_) b
      · simpa [hsymm a.succ 0, Equiv.swap_comm] using hA_zero a k
      · exact hA_tail a b k
  have hB_zero (j : Fin n) :
      adjoinCross u h 0 * adjoinCross u h j.succ *
          (adjoinCross u h 0)⁻¹ = u 0 j.succ := by
    rw [hcrossZero, hhInv, adjoinCross, huInv]
    calc
      h * (u 0 j.succ * h * u 0 j.succ) * h =
          (h * u 0 j.succ * h) * u 0 j.succ * h := by group
      _ = (u 0 j.succ * h * u 0 j.succ) * u 0 j.succ * h := by
        rw [hbraid]
      _ = u 0 j.succ * h * (u 0 j.succ * u 0 j.succ) * h := by group
      _ = u 0 j.succ * (h * h) := by rw [hsq]; group
      _ = u 0 j.succ := by rw [hh]; simp
  have hB_zero_rev (i : Fin n) :
      adjoinCross u h i.succ * adjoinCross u h 0 *
          (adjoinCross u h i.succ)⁻¹ = u i.succ 0 := by
    rw [hcrossZero, adjoinCross_inv u h hh, hsymm i.succ 0]
    simp only [adjoinCross, huInv]
    calc
      (u 0 i.succ * h * u 0 i.succ) * h *
          (u 0 i.succ * h * u 0 i.succ) =
        (h * u 0 i.succ * h) * h *
          (u 0 i.succ * h * u 0 i.succ) := by rw [hbraid]
      _ = h * u 0 i.succ * (h * h) * u 0 i.succ * h * u 0 i.succ := by
        group
      _ = h * u 0 i.succ * u 0 i.succ * h * u 0 i.succ := by
        rw [hh]
        group
      _ = h * (u 0 i.succ * u 0 i.succ) * h * u 0 i.succ := by
        group
      _ = h * h * u 0 i.succ := by rw [hsq]; group
      _ = u 0 i.succ := by rw [hh]; simp
  have hB_nonzero (i j : Fin n) (hij : i ≠ j) :
      adjoinCross u h i.succ * adjoinCross u h j.succ *
          (adjoinCross u h i.succ)⁻¹ = u i.succ j.succ := by
    let q := u 0 i.succ
    apply (MulAut.conj q).injective
    simp only [map_mul, map_inv]
    rw [show (MulAut.conj q) (adjoinCross u h i.succ) =
        adjoinCross u h 0 by simpa [q] using hA 0 i.succ i.succ]
    rw [show (MulAut.conj q) (adjoinCross u h j.succ) =
        adjoinCross u h j.succ by
          simpa [q, Equiv.swap_apply_def, hij, Ne.symm hij] using
            hA 0 i.succ j.succ]
    rw [hB_zero]
    simpa [q, Equiv.swap_apply_def, hij, Ne.symm hij] using
      (hconj 0 i.succ i.succ j.succ).symm
  have hB (i j : Fin (n + 1)) :
      adjoinCross u h i * adjoinCross u h j * (adjoinCross u h i)⁻¹ =
        adjoinTrans u h (Equiv.swap 0 i.succ 0) (Equiv.swap 0 i.succ j.succ) := by
    by_cases hij : i = j
    · subst j
      rw [adjoinCross_inv u h hh i, adjoinCross_sq u h hh i, one_mul]
      simp
    · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
        · exact (hij rfl).elim
        · have hs0 : Equiv.swap 0 (0 : Fin (n + 1)).succ 0 =
              (0 : Fin (n + 1)).succ := Equiv.swap_apply_left _ _
          have hsj : Equiv.swap 0 (0 : Fin (n + 1)).succ j.succ.succ =
              j.succ.succ := by
            apply Equiv.swap_apply_of_ne_of_ne
            · exact Fin.succ_ne_zero j.succ
            · intro heq
              exact Fin.succ_ne_zero j (Fin.succ_injective _ heq)
          rw [hs0, hsj]
          exact hB_zero j
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
        · have hs0 : Equiv.swap 0 i.succ.succ 0 = i.succ.succ :=
              Equiv.swap_apply_left _ _
          have hs1 : Equiv.swap 0 i.succ.succ (0 : Fin (n + 1)).succ =
              (0 : Fin (n + 1)).succ := by
            apply Equiv.swap_apply_of_ne_of_ne
            · exact Fin.succ_ne_zero 0
            · intro heq
              exact (Fin.succ_ne_zero i).symm (Fin.succ_injective _ heq)
          rw [hs0, hs1]
          exact hB_zero_rev i
        · have hij' : i ≠ j := by
            intro h
            exact hij (congrArg Fin.succ h)
          simpa [Equiv.swap_apply_def, hij', Ne.symm hij'] using
            hB_nonzero i j hij'
  have hC_left (i d : Fin (n + 1)) (hid : i ≠ d) :
      adjoinCross u h i * u i d * (adjoinCross u h i)⁻¹ =
        adjoinCross u h d := by
    have hb := hB i d
    have hci := adjoinCross_inv u h hh i
    rw [hci] at hb ⊢
    have hb' :
        adjoinCross u h i * adjoinCross u h d * adjoinCross u h i =
          u i d := by
      simpa [Equiv.swap_apply_def, hid, Ne.symm hid] using hb
    rw [← hb']
    calc
      adjoinCross u h i *
            (adjoinCross u h i * adjoinCross u h d * adjoinCross u h i) *
          adjoinCross u h i =
        (adjoinCross u h i * adjoinCross u h i) *
          adjoinCross u h d *
            (adjoinCross u h i * adjoinCross u h i) := by group
      _ = adjoinCross u h d := by
        have hxi := adjoinCross_sq u h hh i
        rw [hxi]
        simp
  have hC (i c d : Fin (n + 1)) :
      adjoinCross u h i * u c d * (adjoinCross u h i)⁻¹ =
        adjoinTrans u h (Equiv.swap 0 i.succ c.succ)
          (Equiv.swap 0 i.succ d.succ) := by
    by_cases hcd : c = d
    · subst d
      rw [hone, mul_one, mul_inv_cancel, htransOne]
    · by_cases hic : i = c
      · subst c
        simpa [Equiv.swap_apply_def, hcd, Ne.symm hcd] using
          hC_left i d hcd
      · by_cases hid : i = d
        · subst d
          have hic' : i ≠ c := hic
          simpa [hsymm c i, Equiv.swap_apply_def, hic', Ne.symm hic'] using
            hC_left i c hic'
        · have ha := hA c d i
          have hfix : Equiv.swap c d i = i := by
            simp [Equiv.swap_apply_def, hic, hid]
          rw [hfix] at ha
          rw [huInv c d] at ha
          have hcomm :
              u c d * adjoinCross u h i = adjoinCross u h i * u c d := by
            calc
              u c d * adjoinCross u h i =
                  u c d * adjoinCross u h i * 1 := by simp
              _ = u c d * adjoinCross u h i * (u c d * u c d) := by
                rw [hsq]
              _ = (u c d * adjoinCross u h i * u c d) * u c d := by group
              _ = adjoinCross u h i * u c d := by rw [ha]
          rw [adjoinCross_inv u h hh i]
          calc
            adjoinCross u h i * u c d * adjoinCross u h i =
                u c d * (adjoinCross u h i * adjoinCross u h i) := by
                  rw [hcomm.symm]
                  group
            _ = u c d := by
              rw [adjoinCross_sq u h hh i]
              simp
            _ = adjoinTrans u h (Equiv.swap 0 i.succ c.succ)
                (Equiv.swap 0 i.succ d.succ) := by
              simp [Equiv.swap_apply_def, Ne.symm hic, Ne.symm hid]
  have hZero (b : Fin (n + 1)) (c d : Fin (n + 2)) :
      adjoinTrans u h 0 b.succ * adjoinTrans u h c d *
          (adjoinTrans u h 0 b.succ)⁻¹ =
        adjoinTrans u h (Equiv.swap 0 b.succ c) (Equiv.swap 0 b.succ d) := by
    refine Fin.cases ?_ (fun c => ?_) c
    · refine Fin.cases ?_ (fun d => ?_) d
      · rw [adjoinTrans_zero_zero, mul_one, mul_inv_cancel, htransOne]
      · simpa [Equiv.swap_apply_def] using hB b d
    · refine Fin.cases ?_ (fun d => ?_) d
      · conv_rhs => rw [htransSymm]
        simpa [Equiv.swap_apply_def] using hB b c
      · simpa [Equiv.swap_apply_def] using hC b c d
  have hswapSucc (a b c : Fin (n + 1)) :
      Equiv.swap a.succ b.succ c.succ = (Equiv.swap a b c).succ := by
    simp only [Equiv.swap_apply_def]
    split_ifs <;> simp_all
  have hswapZero (a b : Fin (n + 1)) :
      Equiv.swap a.succ b.succ (0 : Fin (n + 2)) = 0 := by
    apply Equiv.swap_apply_of_ne_of_ne
    · exact (Fin.succ_ne_zero a).symm
    · exact (Fin.succ_ne_zero b).symm
  intro a b c d
  refine Fin.cases ?_ (fun a => ?_) a
  · refine Fin.cases ?_ (fun b => ?_) b
    · simp [htransOne]
    · exact hZero b c d
  · refine Fin.cases ?_ (fun b => ?_) b
    · have ht : adjoinTrans u h a.succ 0 = adjoinTrans u h 0 a.succ :=
          htransSymm a.succ 0
      rw [ht]
      have hswap : Equiv.swap a.succ 0 = Equiv.swap 0 a.succ :=
        Equiv.swap_comm _ _
      rw [hswap]
      exact hZero a c d
    · refine Fin.cases ?_ (fun c => ?_) c
      · refine Fin.cases ?_ (fun d => ?_) d
        · rw [adjoinTrans_zero_zero, mul_one, mul_inv_cancel,
            hswapZero, htransOne]
        · simpa only [adjoinTrans_succ_succ, adjoinTrans_zero_succ,
            hswapZero, hswapSucc] using hA a b d
      · refine Fin.cases ?_ (fun d => ?_) d
        · simpa only [adjoinTrans_succ_succ, adjoinTrans_succ_zero,
            hswapZero, hswapSucc] using hA a b c
        · simpa only [adjoinTrans_succ_succ, hswapSucc] using
            hconj a b c d

theorem trans_conj (r : G →* G) (s h : G)
    (hs : s * s = 1) (hh : h * h = 1)
    (hfar : ∀ z, Commute h (r (r z)))
    (hbraidS : h * r s * h = r s * h * r s)
    (hbraidH : h * r h * h = r h * h * r h) :
    ∀ (n : ℕ) (a b c d : Fin (n + 1)),
      trans r s h n a b * trans r s h n c d *
          (trans r s h n a b)⁻¹ =
        trans r s h n (Equiv.swap a b c) (Equiv.swap a b d) := by
  intro n
  induction n with
  | zero =>
      intro a b c d
      fin_cases a
      fin_cases b
      fin_cases c
      fin_cases d
      simp
  | succ n ih =>
      cases n with
      | zero =>
          intro a b c d
          let u : Fin 1 → Fin 1 → G := fun i j => r (trans r s h 0 i j)
          have huOne : ∀ i, u i i = 1 := by intro i; simp [u]
          have huSymm : ∀ i j, u i j = u j i := by intro i j; simp [u]
          have huSq : ∀ i j, u i j * u i j = 1 := by intro i j; simp [u]
          have huConj : ∀ i j k l,
              u i j * u k l * (u i j)⁻¹ =
                u (Equiv.swap i j k) (Equiv.swap i j l) := by
            intro i j k l
            simp [u]
          have hext := adjoinTrans_conj u s huOne huSymm huSq huConj hs
            (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
          have hcrossIdent (k : Fin 1) :
              adjoinCross u s k = cross r s h 0 k := by
            fin_cases k
            simp [u, adjoinCross]
          have htransIdent (i j : Fin 2) :
              adjoinTrans u s i j = trans r s h 1 i j := by
            refine Fin.cases ?_ (fun i => ?_) i
            · refine Fin.cases rfl (fun j => hcrossIdent j) j
            · refine Fin.cases (hcrossIdent i) (fun _ => by simp [u]) j
          simpa only [htransIdent] using hext a b c d
      | succ n =>
          intro a b c d
          let u : Fin (n + 2) → Fin (n + 2) → G :=
            fun i j => r (trans r s h (n + 1) i j)
          have huOne : ∀ i, u i i = 1 := by
            intro i
            simp [u, trans_one]
          have huSymm : ∀ i j, u i j = u j i := by
            intro i j
            simp [u, trans_symm]
          have huSq : ∀ i j, u i j * u i j = 1 := by
            intro i j
            simpa [u] using congrArg r (trans_sq r s h hs hh (n + 1) i j)
          have huConj : ∀ i j k l,
              u i j * u k l * (u i j)⁻¹ =
                u (Equiv.swap i j k) (Equiv.swap i j l) := by
            intro i j k l
            simpa [u] using congrArg r (ih i j k l)
          have huFar (i j : Fin (n + 1)) : Commute h (u i.succ j.succ) := by
            simpa [u] using hfar (trans r s h n i j)
          have huBraid (j : Fin (n + 1)) :
              h * u 0 j.succ * h = u 0 j.succ * h * u 0 j.succ := by
            simpa [u] using cross_braid r s h hfar hbraidS hbraidH n j
          have hext := adjoinTrans_conj u h huOne huSymm huSq huConj hh
            huFar huBraid
          have hcrossIdent (k : Fin (n + 2)) :
              adjoinCross u h k = cross r s h (n + 1) k := by
            refine Fin.cases ?_ (fun _ => rfl) k
            simp [u, adjoinCross, trans_one]
          have htransIdent (i j : Fin (n + 3)) :
              adjoinTrans u h i j = trans r s h (n + 2) i j := by
            refine Fin.cases ?_ (fun i => ?_) i
            · refine Fin.cases rfl (fun j => hcrossIdent j) j
            · refine Fin.cases (hcrossIdent i) (fun _ => rfl) j
          simpa only [htransIdent] using hext a b c d

/-- The finite symmetric-group representation supplied by a transposition
tower satisfying its two local braid diagrams. -/
def permHom (r : G →* G) (s h : G)
    (hs : s * s = 1) (hh : h * h = 1)
    (hfar : ∀ z, Commute h (r (r z)))
    (hbraidS : h * r s * h = r s * h * r s)
    (hbraidH : h * r h * h = r h * h * r h)
    (n : ℕ) : Equiv.Perm (Fin (n + 1)) →* G :=
  Submission.PermLift.hom (n + 1) (trans r s h n)
    (trans_one r s h n) (trans_symm r s h n)
    (trans_sq r s h hs hh n)
    (trans_conj r s h hs hh hfar hbraidS hbraidH n)

@[simp] theorem permHom_swap (r : G →* G) (s h : G)
    (hs : s * s = 1) (hh : h * h = 1)
    (hfar : ∀ z, Commute h (r (r z)))
    (hbraidS : h * r s * h = r s * h * r s)
    (hbraidH : h * r h * h = r h * h * r h)
    (n : ℕ) (i j : Fin (n + 1)) :
    permHom r s h hs hh hfar hbraidS hbraidH n (Equiv.swap i j) =
      trans r s h n i j := by
  exact Submission.PermLift.hom_swap (n + 1) (trans r s h n)
    (trans_one r s h n) (trans_symm r s h n)
    (trans_sq r s h hs hh n)
    (trans_conj r s h hs hh hfar hbraidS hbraidH n) i j

end Submission.PermLift.Tower
