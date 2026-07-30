import Mathlib

open Function

namespace Submission.Helpers

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Multiply a fixed alternating form by the value of a bilinear form. -/
def pairMap {n : ℕ} (B : M →ₗ[R] M →ₗ[R] R) (f : M [⋀^Fin n]→ₗ[R] R) :
    M →ₗ[R] M →ₗ[R] M [⋀^Fin n]→ₗ[R] R :=
  LinearMap.mk₂ R (fun x y ↦ B x y • f)
    (fun x₁ x₂ y ↦ by simp [add_smul])
    (fun c x y ↦ by simp [mul_smul])
    (fun x y₁ y₂ ↦ by simp [add_smul])
    (fun c x y ↦ by simp [mul_smul])

/-- The integral one-pair Pfaffian recurrence, curried in its first argument. -/
def pfCurry {n : ℕ} (B : M →ₗ[R] M →ₗ[R] R) (f : M [⋀^Fin n]→ₗ[R] R) :
    M →ₗ[R] M [⋀^Fin (n + 1)]→ₗ[R] R :=
  AlternatingMap.alternatizeUncurryFinLM.comp (pairMap B f)

@[simp]
theorem pfCurry_apply {n : ℕ} (B : M →ₗ[R] M →ₗ[R] R)
    (f : M [⋀^Fin n]→ₗ[R] R) (x : M) :
    pfCurry B f x = AlternatingMap.alternatizeUncurryFin (pairMap B f x) :=
  rfl

private theorem alternating_apply_eq_zero_of_coord_eq {n : ℕ}
    (g : M →ₗ[R] M [⋀^Fin (n + 1)]→ₗ[R] R)
    (hg : ∀ x, (g x).curryLeft x = 0) (x : M) (v : Fin (n + 1) → M)
    (i : Fin (n + 1)) (hvi : v i = x) :
    g x v = 0 := by
  rw [← i.insertNth_self_removeNth v, hvi, AlternatingMap.map_insertNth]
  change (-1) ^ (i : ℕ) • (g x).curryLeft x (i.removeNth v) = 0
  rw [hg]
  simp

/-- Uncurry a family of alternating maps when inserting the curried vector makes it vanish. -/
def alternatingUncurry {n : ℕ} (g : M →ₗ[R] M [⋀^Fin (n + 1)]→ₗ[R] R)
    (hg : ∀ x, (g x).curryLeft x = 0) :
    M [⋀^Fin (n + 2)]→ₗ[R] R where
  toMultilinearMap := (AlternatingMap.toMultilinearMapLM.comp g).uncurryLeft
  map_eq_zero_of_eq' v i j hv hij := by
    cases i using Fin.cases with
    | zero =>
        cases j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j =>
            exact alternating_apply_eq_zero_of_coord_eq g hg (v 0) (Fin.tail v) j
              (by change v j.succ = v 0; exact hv.symm)
    | succ i =>
        cases j using Fin.cases with
        | zero =>
            exact alternating_apply_eq_zero_of_coord_eq g hg (v 0) (Fin.tail v) i
              (by change v i.succ = v 0; exact hv)
        | succ j =>
            exact (g (v 0)).map_eq_zero_of_eq (Fin.tail v)
              (by change v i.succ = v j.succ; exact hv)
              (fun h ↦ hij (congrArg Fin.succ h))

@[simp]
theorem alternatingUncurry_apply {n : ℕ}
    (g : M →ₗ[R] M [⋀^Fin (n + 1)]→ₗ[R] R)
    (hg : ∀ x, (g x).curryLeft x = 0) (v : Fin (n + 2) → M) :
    alternatingUncurry g hg v = g (v 0) (Fin.tail v) :=
  rfl

@[simp]
theorem alternatingUncurry_curryLeft {n : ℕ}
    (g : M →ₗ[R] M [⋀^Fin (n + 1)]→ₗ[R] R) (hg : ∀ x, (g x).curryLeft x = 0) :
    (alternatingUncurry g hg).curryLeft = g := by
  ext x v
  rfl

/-- The symmetric rank-one bilinear form obtained by squaring a linear functional. -/
def squareBilinear (B : M →ₗ[R] M →ₗ[R] R) (x : M) : M →ₗ[R] M →ₗ[R] R :=
  LinearMap.mk₂ R (fun y z ↦ B x y * B x z)
    (fun y₁ y₂ z ↦ by simp [add_mul])
    (fun c y z ↦ by simp [mul_assoc])
    (fun y z₁ z₂ ↦ by simp [mul_add])
    (fun c y z ↦ by simp [mul_left_comm])

theorem squareBilinear_comm (B : M →ₗ[R] M →ₗ[R] R) (x y z : M) :
    squareBilinear B x y z = squareBilinear B x z y := by
  simp [squareBilinear, mul_comm]

omit [AddCommGroup M] [Module R M] in
@[simp]
private theorem removeNth_succ_vecCons {n : ℕ} (i : Fin (n + 1)) (x : M)
    (v : Fin (n + 1) → M) :
    i.succ.removeNth (Matrix.vecCons x v) = Matrix.vecCons x (i.removeNth v) := by
  ext j
  cases j using Fin.cases <;> simp [Fin.removeNth]

private theorem pfCurry_pfCurry_same {n : ℕ} (B : M →ₗ[R] M →ₗ[R] R)
    (f : M [⋀^Fin n]→ₗ[R] R) (x : M) :
    pfCurry B (pfCurry B f x) x = 0 := by
  have hinner :
      AlternatingMap.alternatizeUncurryFinLM.comp (pairMap (squareBilinear B x) f) =
        pairMap B (pfCurry B f x) x := by
    ext y v
    simp [pfCurry, pairMap, squareBilinear,
      AlternatingMap.alternatizeUncurryFin_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [pfCurry_apply, ← hinner]
  exact AlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric
    (fun y z ↦ by
      ext v
      simp [pairMap, squareBilinear, mul_comm])

private theorem pfCurry_curryLeft_same_eq_neg {n : ℕ}
    (B : M →ₗ[R] M →ₗ[R] R) (hB : ∀ x, B x x = 0)
    (f : M [⋀^Fin (n + 1)]→ₗ[R] R) (x : M) :
    (pfCurry B f x).curryLeft x = -pfCurry B (f.curryLeft x) x := by
  ext v
  simp [pfCurry, pairMap, AlternatingMap.alternatizeUncurryFin_apply,
    Fin.sum_univ_succ, hB, pow_add]

private theorem pfCurry_const_curryLeft_same (B : M →ₗ[R] M →ₗ[R] R)
    (hB : ∀ x, B x x = 0) (x : M) :
    (pfCurry B (AlternatingMap.constOfIsEmpty R M (Fin 0) 1) x).curryLeft x = 0 := by
  ext v
  simp [pfCurry, pairMap, AlternatingMap.alternatizeUncurryFin_apply, hB]

private theorem pfStep_curryLeft_same {n : ℕ} (B : M →ₗ[R] M →ₗ[R] R)
    (hB : ∀ x, B x x = 0) (f : M [⋀^Fin n]→ₗ[R] R)
    (hf : ∀ x, (pfCurry B f x).curryLeft x = 0) (x : M) :
    (pfCurry B (alternatingUncurry (pfCurry B f) hf) x).curryLeft x = 0 := by
  rw [pfCurry_curryLeft_same_eq_neg B hB]
  change -pfCurry B (pfCurry B f x) x = 0
  rw [pfCurry_pfCurry_same, neg_zero]

/-- An integral Pfaffian alternating form together with the fact needed for the next recurrence. -/
structure PfData (B : M →ₗ[R] M →ₗ[R] R) (n : ℕ) where
  form : M [⋀^Fin (2 * n)]→ₗ[R] R
  next_same : ∀ x, (pfCurry B form x).curryLeft x = 0

/-- Integral divided wedge powers of an alternating bilinear form. -/
noncomputable def pfData (B : M →ₗ[R] M →ₗ[R] R) (hB : ∀ x, B x x = 0) :
    (n : ℕ) → PfData B n
  | 0 =>
      { form := AlternatingMap.constOfIsEmpty R M (Fin 0) 1
        next_same := pfCurry_const_curryLeft_same B hB }
  | n + 1 =>
      let d := pfData B hB n
      { form := alternatingUncurry (pfCurry B d.form) d.next_same
        next_same := pfStep_curryLeft_same B hB d.form d.next_same }

/-- The degree `2n` integral Pfaffian alternating form of `B`. -/
noncomputable def pfForm (B : M →ₗ[R] M →ₗ[R] R) (hB : ∀ x, B x x = 0) (n : ℕ) :
    M [⋀^Fin (2 * n)]→ₗ[R] R :=
  (pfData B hB n).form

@[simp]
theorem pfForm_zero_apply (B : M →ₗ[R] M →ₗ[R] R) (hB : ∀ x, B x x = 0)
    (v : Fin 0 → M) :
    pfForm B hB 0 v = 1 :=
  rfl

theorem pfForm_succ_apply (B : M →ₗ[R] M →ₗ[R] R) (hB : ∀ x, B x x = 0)
    (n : ℕ) (v : Fin (2 * (n + 1)) → M) :
    pfForm B hB (n + 1) v =
      ∑ i : Fin (2 * n + 1), (-1 : R) ^ (i : ℕ) * B (v 0) (Fin.tail v i) *
        pfForm B hB n (i.removeNth (Fin.tail v)) := by
  simp [pfForm, pfData, pfCurry, pairMap,
    AlternatingMap.alternatizeUncurryFin_apply, mul_assoc]

/-- Integral Pfaffian forms depend only on the pairings of their arguments. -/
theorem pfForm_congr_pairings (B : M →ₗ[R] M →ₗ[R] R) (hB : ∀ x, B x x = 0)
    (n : ℕ) {v w : Fin (2 * n) → M}
    (h : ∀ i j, B (v i) (v j) = B (w i) (w j)) :
    pfForm B hB n v = pfForm B hB n w := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pfForm_succ_apply, pfForm_succ_apply]
      apply Finset.sum_congr rfl
      intro i _
      rw [show B (v 0) (Fin.tail v i) = B (w 0) (Fin.tail w i) by
        change B (v 0) (v i.succ) = B (w 0) (w i.succ)
        exact h 0 i.succ]
      congr 1
      apply ih
      intro a b
      change
        B (v (Fin.succ (i.succAbove a))) (v (Fin.succ (i.succAbove b))) =
          B (w (Fin.succ (i.succAbove a))) (w (Fin.succ (i.succAbove b)))
      exact h (Fin.succ (i.succAbove a)) (Fin.succ (i.succAbove b))

theorem pfForm_vecCons_pair (B : M →ₗ[R] M →ₗ[R] R) (hB : ∀ x, B x x = 0)
    (n : ℕ) (x y : M) (v : Fin (2 * n) → M) (u : R)
    (hxy : B x y = u) (hxv : ∀ i, B x (v i) = 0) :
    pfForm B hB (n + 1) (Matrix.vecCons x (Matrix.vecCons y v)) =
      u * pfForm B hB n v := by
  rw [pfForm_succ_apply]
  simp [Fin.sum_univ_succ, hxy, hxv]

section SymplecticForm

variable {l : Type*} [DecidableEq l] [Fintype l]

/-- The bilinear form represented by `Matrix.J`, written without matrix multiplication. -/
def sympBilinear : (l ⊕ l → R) →ₗ[R] (l ⊕ l → R) →ₗ[R] R :=
  LinearMap.mk₂ R
    (fun x y ↦ ∑ i : l, (x (.inr i) * y (.inl i) - x (.inl i) * y (.inr i)))
    (fun x₁ x₂ y ↦ by
      simp only [Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring)
    (fun c x y ↦ by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring)
    (fun x y₁ y₂ ↦ by
      simp only [Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring)
    (fun c x y ↦ by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring)

omit [DecidableEq l] in
@[simp]
theorem sympBilinear_self (x : l ⊕ l → R) : sympBilinear x x = 0 := by
  simp [sympBilinear, mul_comm]

theorem sympBilinear_rows (A : Matrix (l ⊕ l) (l ⊕ l) R) (i j : l ⊕ l) :
    sympBilinear (A i) (A j) = (A * Matrix.J l R * A.transpose) i j := by
  simp [sympBilinear, Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type,
    Matrix.fromBlocks, Matrix.one_apply, Finset.sum_sub_distrib]
  ring

@[simp]
theorem sympBilinear_single_inl_inl (i j : l) :
    (sympBilinear (l := l) (R := R))
      (Pi.single (.inl i) 1) (Pi.single (.inl j) 1) = 0 := by
  classical
  simp [sympBilinear, Pi.single_apply]

@[simp]
theorem sympBilinear_single_inl_inr (i j : l) :
    (sympBilinear (l := l) (R := R))
      (Pi.single (.inl i) 1) (Pi.single (.inr j) 1) =
      if i = j then -1 else 0 := by
  classical
  simp [sympBilinear, Pi.single_apply]
  split_ifs <;> simp_all

@[simp]
theorem sympBilinear_single_inr_inl (i j : l) :
    (sympBilinear (l := l) (R := R))
      (Pi.single (.inr i) 1) (Pi.single (.inl j) 1) =
      if i = j then 1 else 0 := by
  classical
  simp [sympBilinear, Pi.single_apply, eq_comm]

@[simp]
theorem sympBilinear_single_inr_inr (i j : l) :
    (sympBilinear (l := l) (R := R))
      (Pi.single (.inr i) 1) (Pi.single (.inr j) 1) = 0 := by
  classical
  simp [sympBilinear, Pi.single_apply]

@[simp]
theorem sympBilinear_single (i j : l ⊕ l) :
    (sympBilinear (l := l) (R := R)) (Pi.single i 1) (Pi.single j 1) =
      Matrix.J l R i j := by
  rcases i with i | i <;> rcases j with j | j
  all_goals simp [Matrix.J, Matrix.fromBlocks, Matrix.one_apply]
  all_goals split_ifs <;> simp_all

/-- Split an even-sized `Fin` into an index and a two-valued side coordinate. -/
def finPairEquiv (n : ℕ) : Fin (2 * n) ≃ Fin n × Fin 2 :=
  (finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm

/-- Turn a two-valued side coordinate into the two summands of a sum type. -/
def finPairToSumEquiv (n : ℕ) : Fin n × Fin 2 ≃ Fin n ⊕ Fin n where
  toFun p := Fin.cases (.inl p.1) (fun _ ↦ .inr p.1) p.2
  invFun s := s.elim (fun i ↦ (i, 0)) (fun i ↦ (i, 1))
  left_inv p := by
    rcases p with ⟨i, j⟩
    fin_cases j <;> rfl
  right_inv s := by
    rcases s with i | i <;> rfl

@[simp]
private theorem finPairToSumEquiv_zero (n : ℕ) (i : Fin n) :
    finPairToSumEquiv n (i, 0) = .inl i :=
  rfl

@[simp]
private theorem finPairToSumEquiv_one (n : ℕ) (i : Fin n) :
    finPairToSumEquiv n (i, 1) = .inr i := by
  change
    Fin.cases (Sum.inl i : Fin n ⊕ Fin n)
      (fun _ ↦ (Sum.inr i : Fin n ⊕ Fin n)) 1 = Sum.inr i
  rfl

/-- Interleave the left and right copies of a finite index family. -/
def sympIndex {n : ℕ} (e : Fin n → l) : Fin (2 * n) → l ⊕ l :=
  Sum.map e e ∘ finPairToSumEquiv n ∘ finPairEquiv n

/-- The interleaving is an equivalence when the underlying index family is. -/
def sympIndexEquiv {n : ℕ} (e : Fin n ≃ l) : Fin (2 * n) ≃ l ⊕ l :=
  (finPairEquiv n).trans ((finPairToSumEquiv n).trans (Equiv.sumCongr e e))

omit [DecidableEq l] [Fintype l] in
@[simp]
theorem sympIndexEquiv_apply {n : ℕ} (e : Fin n ≃ l) (i : Fin (2 * n)) :
    sympIndexEquiv e i = sympIndex e i :=
  rfl

@[simp]
private theorem finPairEquiv_zero (n : ℕ) :
    finPairEquiv (n + 1) 0 = (0, 0) := by
  apply Prod.ext <;> apply Fin.ext <;>
    simp [finPairEquiv, finProdFinEquiv]

@[simp]
private theorem finPairEquiv_one (n : ℕ) :
    finPairEquiv (n + 1) 1 = (0, 1) := by
  apply (finPairEquiv (n + 1)).symm.injective
  simp only [Equiv.symm_apply_apply]
  apply Fin.ext
  rfl

private theorem finPairEquiv_succ_succ (n : ℕ) (i : Fin (2 * n)) :
    finPairEquiv (n + 1) i.succ.succ =
      ((finPairEquiv n i).1.succ, (finPairEquiv n i).2) := by
  apply Prod.ext <;> apply Fin.ext <;>
    simp [finPairEquiv, finProdFinEquiv] <;> omega

omit [DecidableEq l] [Fintype l] in
@[simp]
theorem sympIndex_zero {n : ℕ} (e : Fin (n + 1) → l) :
    sympIndex e 0 = .inl (e 0) := by
  simp [sympIndex, finPairToSumEquiv]

omit [DecidableEq l] [Fintype l] in
@[simp]
theorem sympIndex_one {n : ℕ} (e : Fin (n + 1) → l) :
    sympIndex e 1 = .inr (e 0) := by
  rw [sympIndex, comp_apply, comp_apply, finPairEquiv_one]
  change Sum.map e e (.inr 0) = .inr (e 0)
  rfl

omit [DecidableEq l] [Fintype l] in
@[simp]
theorem sympIndex_succ_succ {n : ℕ} (e : Fin (n + 1) → l) (i : Fin (2 * n)) :
    sympIndex e i.succ.succ = sympIndex (e ∘ Fin.succ) i := by
  simp only [sympIndex, Function.comp_apply, finPairEquiv_succ_succ]
  rcases h : finPairEquiv n i with ⟨j, k⟩
  cases k using Fin.cases with
  | zero => rfl
  | succ k =>
      have hk : k = 0 := Fin.eq_zero k
      subst k
      rfl

theorem pfForm_sympBasis (n : ℕ) (e : Fin n → l) (he : Function.Injective e) :
    pfForm (sympBilinear (l := l) (R := R)) sympBilinear_self n
        (fun i ↦ Pi.single (sympIndex e i) 1) =
      (-1 : R) ^ n := by
  induction n with
  | zero => simp [pfForm, pfData]
  | succ n ih =>
      let e' : Fin n → l := e ∘ Fin.succ
      have he' : Function.Injective e' := he.comp (Fin.succ_injective n)
      have hv :
          (fun i ↦ Pi.single (sympIndex e i) (1 : R)) =
            Matrix.vecCons (Pi.single (.inl (e 0)) 1)
              (Matrix.vecCons (Pi.single (.inr (e 0)) 1)
                (fun i ↦ Pi.single (sympIndex e' i) 1)) := by
        ext i j
        cases i using Fin.cases with
        | zero => simp
        | succ i =>
            cases i using Fin.cases with
            | zero => simp
            | succ i => simp [e']
      rw [hv, pfForm_vecCons_pair _ _ n _ _ _ (-1)]
      · rw [ih e' he']
        simp [pow_succ]
      · simp [Matrix.J, Matrix.fromBlocks]
      · intro i
        rcases hpair : finPairEquiv n i with ⟨j, k⟩
        have hne : e 0 ≠ e j.succ := fun h ↦ (Fin.succ_ne_zero j) (he h).symm
        fin_cases k <;>
          simp [sympIndex, e', hpair, hne,
            Matrix.J, Matrix.fromBlocks]

end SymplecticForm

end Submission.Helpers
