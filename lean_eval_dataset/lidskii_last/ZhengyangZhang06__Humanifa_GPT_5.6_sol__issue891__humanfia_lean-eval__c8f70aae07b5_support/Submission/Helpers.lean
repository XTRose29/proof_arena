import Mathlib

/-! Local spectral and rank-one decomposition lemmas for the submission. -/

open scoped ComplexConjugate ComplexOrder

open Module WithLp Matrix

namespace Submission.Helpers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

lemma re_inner_apply_eq_sum {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    {d : ℕ} (hd : finrank ℂ E = d) (x : E) :
    Complex.re (inner ℂ x (T x)) =
      ∑ i : Fin d, hT.eigenvalues hd i * ‖(hT.eigenvectorBasis hd).repr x i‖ ^ 2 := by
  let b := hT.eigenvectorBasis hd
  rw [← b.repr.inner_map_map x (T x), PiLp.inner_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  change Complex.re (inner ℂ ((hT.eigenvectorBasis hd).repr x i)
    ((hT.eigenvectorBasis hd).repr (T x) i)) = _
  rw [hT.eigenvectorBasis_apply_self_apply hd]
  simp [Complex.mul_re, Complex.sq_norm, Complex.normSq_apply]
  ring

lemma eigenvalue_mul_norm_sq_le_re_inner_apply {T : E →ₗ[ℂ] E}
    (hT : T.IsSymmetric) {d : ℕ} (hd : finrank ℂ E = d) (k : Fin d) (x : E)
    (hx : ∀ i, k < i → (hT.eigenvectorBasis hd).repr x i = 0) :
    hT.eigenvalues hd k * ‖x‖ ^ 2 ≤ Complex.re (inner ℂ x (T x)) := by
  rw [re_inner_apply_eq_sum hT hd x]
  calc
    hT.eigenvalues hd k * ‖x‖ ^ 2 =
        ∑ i : Fin d, hT.eigenvalues hd k * ‖(hT.eigenvectorBasis hd).repr x i‖ ^ 2 := by
      rw [← Finset.mul_sum]
      congr 1
      rw [← EuclideanSpace.norm_sq_eq ((hT.eigenvectorBasis hd).repr x)]
      exact congrArg (fun z : ℝ ↦ z ^ 2) ((hT.eigenvectorBasis hd).repr.norm_map x).symm
    _ ≤ ∑ i : Fin d,
          hT.eigenvalues hd i * ‖(hT.eigenvectorBasis hd).repr x i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ≤ k
      · exact mul_le_mul_of_nonneg_right (hT.eigenvalues_antitone hd hi) (sq_nonneg _)
      · have hki : k < i := lt_of_not_ge hi
        simp [hx i hki]

lemma re_inner_apply_le_eigenvalue_mul_norm_sq {T : E →ₗ[ℂ] E}
    (hT : T.IsSymmetric) {d : ℕ} (hd : finrank ℂ E = d) (k : Fin d) (x : E)
    (hx : ∀ i, i < k → (hT.eigenvectorBasis hd).repr x i = 0) :
    Complex.re (inner ℂ x (T x)) ≤ hT.eigenvalues hd k * ‖x‖ ^ 2 := by
  rw [re_inner_apply_eq_sum hT hd x]
  calc
    (∑ i : Fin d, hT.eigenvalues hd i * ‖(hT.eigenvectorBasis hd).repr x i‖ ^ 2) ≤
        ∑ i : Fin d, hT.eigenvalues hd k * ‖(hT.eigenvectorBasis hd).repr x i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : k ≤ i
      · exact mul_le_mul_of_nonneg_right (hT.eigenvalues_antitone hd hi) (sq_nonneg _)
      · have hik : i < k := lt_of_not_ge hi
        simp [hx i hik]
    _ = hT.eigenvalues hd k * ‖x‖ ^ 2 := by
      rw [← Finset.mul_sum]
      congr 1
      rw [← EuclideanSpace.norm_sq_eq ((hT.eigenvectorBasis hd).repr x)]
      exact congrArg (fun z : ℝ ↦ z ^ 2) ((hT.eigenvectorBasis hd).repr.norm_map x)

theorem eigenvalues_mono_of_re_inner_le {S T : E →ₗ[ℂ] E}
    (hS : S.IsSymmetric) (hT : T.IsSymmetric)
    {d : ℕ} (hd : finrank ℂ E = d)
    (hST : ∀ x, Complex.re (inner ℂ x (S x)) ≤ Complex.re (inner ℂ x (T x)))
    (k : Fin d) : hS.eigenvalues hd k ≤ hT.eigenvalues hd k := by
  let bS := hS.eigenvectorBasis hd
  let bT := hT.eigenvectorBasis hd
  let topIndex : Fin (k.val + 1) → Fin d := fun i ↦
    ⟨i.val, by omega⟩
  let botIndex : Fin (d - k.val) → Fin d := fun i ↦
    ⟨k.val + i.val, by omega⟩
  let fS : Fin (k.val + 1) → E := fun i ↦ bS (topIndex i)
  let fT : Fin (d - k.val) → E := fun i ↦ bT (botIndex i)
  let U : Submodule ℂ E := Submodule.span ℂ (Set.range fS)
  let V : Submodule ℂ E := Submodule.span ℂ (Set.range fT)
  have htopIndex : Function.Injective topIndex := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun x : Fin d ↦ x.val) hij
  have hbotIndex : Function.Injective botIndex := by
    intro i j hij
    apply Fin.ext
    have := congrArg (fun x : Fin d ↦ x.val) hij
    change k.val + i.val = k.val + j.val at this
    omega
  have hfS : LinearIndependent ℂ fS := by
    exact bS.toBasis.linearIndependent.comp topIndex htopIndex
  have hfT : LinearIndependent ℂ fT := by
    exact bT.toBasis.linearIndependent.comp botIndex hbotIndex
  have hdimU : finrank ℂ U = k.val + 1 := by
    simpa [U] using finrank_span_eq_card hfS
  have hdimV : finrank ℂ V = d - k.val := by
    simpa [V] using finrank_span_eq_card hfT
  have hnotdisjoint : ¬ Disjoint U V := by
    intro hdisjoint
    have hdim := Submodule.finrank_add_finrank_le_of_disjoint hdisjoint
    rw [hdimU, hdimV, hd] at hdim
    omega
  have hne : U ⊓ V ≠ ⊥ := by
    intro heq
    apply hnotdisjoint
    rw [disjoint_iff_inf_le, heq]
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hxU : x ∈ U := hx.1
  have hxV : x ∈ V := hx.2
  have hxS : ∀ i, k < i → bS.repr x i = 0 := by
    intro i hki
    have hle : U ≤ LinearMap.ker (bS.toBasis.coord i) := by
      apply Submodule.span_le.2
      rintro _ ⟨a, rfl⟩
      change bS.toBasis.coord i (fS a) = 0
      have hneIndex : topIndex a ≠ i := by
        intro heq
        have hval := congrArg (fun x : Fin d ↦ x.val) heq
        change a.val = i.val at hval
        omega
      simp [fS, bS, hneIndex]
    have hmem := hle hxU
    change bS.toBasis.coord i x = 0 at hmem
    exact hmem
  have hxT : ∀ i, i < k → bT.repr x i = 0 := by
    intro i hik
    have hle : V ≤ LinearMap.ker (bT.toBasis.coord i) := by
      apply Submodule.span_le.2
      rintro _ ⟨a, rfl⟩
      change bT.toBasis.coord i (fT a) = 0
      have hneIndex : botIndex a ≠ i := by
        intro heq
        have hval := congrArg (fun x : Fin d ↦ x.val) heq
        change k.val + a.val = i.val at hval
        omega
      simp [fT, bT, hneIndex]
    have hmem := hle hxV
    change bT.toBasis.coord i x = 0 at hmem
    exact hmem
  have hlow := eigenvalue_mul_norm_sq_le_re_inner_apply hS hd k x hxS
  have hupp := re_inner_apply_le_eigenvalue_mul_norm_sq hT hd k x hxT
  have hmul : hS.eigenvalues hd k * ‖x‖ ^ 2 ≤ hT.eigenvalues hd k * ‖x‖ ^ 2 :=
    hlow.trans ((hST x).trans hupp)
  nlinarith [sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hx0)]

theorem eigenvalues₀_mono {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : (B - A).PosSemidef) (k : Fin (Fintype.card n)) :
    hA.eigenvalues₀ k ≤ hB.eigenvalues₀ k := by
  let TA := A.toEuclideanLin
  let TB := B.toEuclideanLin
  have hTA : TA.IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr hA
  have hTB : TB.IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr hB
  have hpos : (B - A).toEuclideanLin.IsPositive := isPositive_toEuclideanLin_iff.mpr hAB
  have hquad : ∀ x, Complex.re (inner ℂ x (TA x)) ≤ Complex.re (inner ℂ x (TB x)) := by
    intro x
    have hx := hpos.re_inner_nonneg_right x
    simpa [TA, TB, inner_sub_right, sub_nonneg] using hx
  exact eigenvalues_mono_of_re_inner_le hTA hTB finrank_euclideanSpace hquad k

lemma sum_eigenvalues₀_eq_re_trace {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ∑ i, hA.eigenvalues₀ i = Complex.re A.trace := by
  rw [hA.trace_eq_sum_eigenvalues]
  rw [Complex.re_sum]
  change (∑ i, hA.eigenvalues₀ i) = ∑ i, Complex.re (hA.eigenvalues i : ℂ)
  simp only [Complex.ofReal_re]
  let e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))
  change (∑ i, hA.eigenvalues₀ i) = ∑ i, hA.eigenvalues₀ (e.symm i)
  exact (e.symm.sum_comp hA.eigenvalues₀).symm

lemma sum_abs_eigenvalues₀_sub_eq_re_trace_sub_of_posSemidef {n : Type*}
    [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : (B - A).PosSemidef) :
    ∑ i, |hA.eigenvalues₀ i - hB.eigenvalues₀ i| =
      Complex.re (B.trace - A.trace) := by
  calc
    (∑ i, |hA.eigenvalues₀ i - hB.eigenvalues₀ i|) =
        ∑ i, (hB.eigenvalues₀ i - hA.eigenvalues₀ i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_of_nonpos (sub_nonpos.mpr (eigenvalues₀_mono hA hB hAB i))]
      ring
    _ = Complex.re (B.trace - A.trace) := by
      rw [Finset.sum_sub_distrib, sum_eigenvalues₀_eq_re_trace,
        sum_eigenvalues₀_eq_re_trace]
      exact (map_sub Complex.reCLM B.trace A.trace).symm

def rankOne {n : Type*} (v : n → ℂ) : Matrix n n ℂ :=
  Matrix.vecMulVec v (star v)

lemma rankOne_posSemidef {n : Type*} [Finite n] (v : n → ℂ) :
    (rankOne v).PosSemidef := by
  exact Matrix.posSemidef_vecMulVec_self_star v

lemma re_trace_rankOne {n : Type*} [Fintype n] (v : n → ℂ) :
    Complex.re (rankOne v).trace = ∑ i, ‖v i‖ ^ 2 := by
  simp [rankOne, Matrix.trace, Matrix.vecMulVec_apply, Complex.sq_norm,
    Complex.normSq_apply]

lemma sum_abs_eigenvalues₀_add_rankOne_le {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (r : ℝ) (v : n → ℂ) :
    let hR : (r • rankOne v).IsHermitian :=
      (rankOne_posSemidef v).isHermitian.smul (by rfl)
    let hAR : (A + r • rankOne v).IsHermitian := hA.add hR
    ∑ i, |hA.eigenvalues₀ i - hAR.eigenvalues₀ i| ≤ |r| * ∑ i, ‖v i‖ ^ 2 := by
  dsimp only
  let hR : (r • rankOne v).IsHermitian :=
    (rankOne_posSemidef v).isHermitian.smul (by rfl)
  let hAR : (A + r • rankOne v).IsHermitian := hA.add hR
  change (∑ i, |hA.eigenvalues₀ i - hAR.eigenvalues₀ i|) ≤ _
  by_cases hr : 0 ≤ r
  · have hpos : ((A + r • rankOne v) - A).PosSemidef := by
      simpa [add_sub_cancel_left] using (rankOne_posSemidef v).smul hr
    rw [sum_abs_eigenvalues₀_sub_eq_re_trace_sub_of_posSemidef hA hAR hpos]
    rw [trace_add, trace_smul, add_sub_cancel_left]
    simp [re_trace_rankOne, abs_of_nonneg hr]
  · have hr' : 0 ≤ -r := neg_nonneg.mpr (le_of_not_ge hr)
    have hpos : (A - (A + r • rankOne v)).PosSemidef := by
      convert (rankOne_posSemidef v).smul hr' using 1
      all_goals module
    have heq :=
      sum_abs_eigenvalues₀_sub_eq_re_trace_sub_of_posSemidef hAR hA hpos
    have hlhs : (∑ i, |hA.eigenvalues₀ i - hAR.eigenvalues₀ i|) =
        ∑ i, |hAR.eigenvalues₀ i - hA.eigenvalues₀ i| := by
      apply Finset.sum_congr rfl
      intro i _
      exact abs_sub_comm _ _
    rw [hlhs, heq, trace_add, trace_smul]
    rw [show A.trace - (A.trace + r • (rankOne v).trace) =
      -(r • (rankOne v).trace) by abel]
    simp [re_trace_rankOne, abs_of_nonpos (le_of_not_ge hr)]

lemma sum_abs_eigenvalues₀_triangle {n : Type*} [Fintype n] [DecidableEq n]
    {A B C : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hC : C.IsHermitian) :
    (∑ i, |hA.eigenvalues₀ i - hC.eigenvalues₀ i|) ≤
      (∑ i, |hA.eigenvalues₀ i - hB.eigenvalues₀ i|) +
        ∑ i, |hB.eigenvalues₀ i - hC.eigenvalues₀ i| := by
  calc
    (∑ i, |hA.eigenvalues₀ i - hC.eigenvalues₀ i|) =
        ∑ i, |(hA.eigenvalues₀ i - hB.eigenvalues₀ i) +
          (hB.eigenvalues₀ i - hC.eigenvalues₀ i)| := by
      congr 1
      funext i
      congr 1
      ring
    _ ≤ ∑ i, (|hA.eigenvalues₀ i - hB.eigenvalues₀ i| +
          |hB.eigenvalues₀ i - hC.eigenvalues₀ i|) := by
      apply Finset.sum_le_sum
      intro i _
      exact abs_add_le _ _
    _ = _ := Finset.sum_add_distrib

theorem sum_abs_eigenvalues₀_add_sum_rankOne_le {n ι : Type*} [Fintype n]
    [DecidableEq n] [DecidableEq ι] (s : Finset ι) (r : ι → ℝ) (v : ι → n → ℂ)
    {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hM : (A + ∑ a ∈ s, r a • rankOne (v a)).IsHermitian) :
    (∑ i, |hA.eigenvalues₀ i - hM.eigenvalues₀ i|) ≤
      ∑ a ∈ s, |r a| * ∑ i, ‖v a i‖ ^ 2 := by
  induction s using Finset.induction_on generalizing A with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha] at hM ⊢
      let hR : (r a • rankOne (v a)).IsHermitian :=
        (rankOne_posSemidef (v a)).isHermitian.smul (by rfl)
      let hA' : (A + r a • rankOne (v a)).IsHermitian := hA.add hR
      have hM' : (A + r a • rankOne (v a) + ∑ x ∈ s, r x • rankOne (v x)).IsHermitian := by
        convert hM using 1
        all_goals module
      have hstep := sum_abs_eigenvalues₀_add_rankOne_le hA (r a) (v a)
      have htail := ih hA' hM'
      have htri := sum_abs_eigenvalues₀_triangle hA hA' hM'
      calc
        (∑ i, |hA.eigenvalues₀ i - hM.eigenvalues₀ i|) ≤
            (∑ i, |hA.eigenvalues₀ i - hA'.eigenvalues₀ i|) +
              ∑ i, |hA'.eigenvalues₀ i - hM'.eigenvalues₀ i| := by
          simpa only [add_assoc] using htri
        _ ≤ |r a| * ∑ i, ‖v a i‖ ^ 2 +
              ∑ x ∈ s, |r x| * ∑ i, ‖v x i‖ ^ 2 := add_le_add hstep htail

noncomputable def unitPhase (z : ℂ) : ℂ :=
  if z = 0 then 1 else z / (‖z‖ : ℂ)

@[simp] lemma norm_unitPhase (z : ℂ) : ‖unitPhase z‖ = 1 := by
  by_cases hz : z = 0
  · simp [unitPhase, hz]
  · simp [unitPhase, hz]

lemma norm_mul_unitPhase (z : ℂ) : (‖z‖ : ℂ) * unitPhase z = z := by
  by_cases hz : z = 0
  · simp [unitPhase, hz]
  · rw [unitPhase, if_neg hz, mul_div_cancel₀]
    exact_mod_cast norm_ne_zero_iff.mpr hz

lemma norm_mul_star_unitPhase (z : ℂ) :
    (‖z‖ : ℂ) * star (unitPhase z) = star z := by
  calc
    (‖z‖ : ℂ) * star (unitPhase z) =
        star (unitPhase z) * star (‖z‖ : ℂ) := by simp [mul_comm]
    _ = star ((‖z‖ : ℂ) * unitPhase z) := by rw [star_mul]
    _ = star z := congrArg star (norm_mul_unitPhase z)

def basisVec {n : Type*} [DecidableEq n] (i : n) : n → ℂ :=
  Pi.single i 1

noncomputable def offVec {n : Type*} [DecidableEq n]
    (z : ℂ) (i j : n) (positive : Bool) : n → ℂ :=
  Pi.single i (unitPhase z) + if positive then Pi.single j 1 else -Pi.single j 1

lemma sum_norm_sq_basisVec {n : Type*} [Fintype n] [DecidableEq n] (i : n) :
    ∑ k, ‖basisVec i k‖ ^ 2 = 1 := by
  classical
  calc
    (∑ k, ‖basisVec i k‖ ^ 2) = ∑ k, if k = i then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hki : k = i <;> simp [basisVec, hki]
    _ = 1 := by simp

lemma sum_norm_sq_offVec {n : Type*} [Fintype n] [DecidableEq n]
    (z : ℂ) {i j : n} (hij : i ≠ j) (positive : Bool) :
    ∑ k, ‖offVec z i j positive k‖ ^ 2 = 2 := by
  classical
  calc
    (∑ k, ‖offVec z i j positive k‖ ^ 2) =
        ∑ k, ((if k = i then 1 else 0) + if k = j then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hki : k = i <;> by_cases hkj : k = j <;>
        cases positive <;> simp_all [offVec]
    _ = 2 := by
      rw [Finset.sum_add_distrib]
      norm_num

noncomputable def offHalf {n : Type*} [DecidableEq n]
    (z : ℂ) (i j : n) : Matrix n n ℂ :=
  (‖z‖ / 4 : ℝ) • rankOne (offVec z i j true) +
    (-(‖z‖ / 4) : ℝ) • rankOne (offVec z i j false)

lemma offHalf_apply {n : Type*} [DecidableEq n] (z : ℂ) {i j : n} (hij : i ≠ j)
    (p q : n) :
    offHalf z i j p q =
      if p = i ∧ q = j then z / 2
      else if p = j ∧ q = i then star z / 2 else 0 := by
  by_cases hpi : p = i <;> by_cases hpj : p = j <;>
    by_cases hqi : q = i <;> by_cases hqj : q = j
  all_goals
    simp_all [offHalf, rankOne, Matrix.vecMulVec_apply, offVec]
  case pos =>
    calc
      (‖z‖ : ℂ) / 4 * unitPhase z + (‖z‖ : ℂ) / 4 * unitPhase z =
          (‖z‖ : ℂ) * unitPhase z * (1 / 2) := by ring
      _ = z * (1 / 2) := by rw [norm_mul_unitPhase]
      _ = z / 2 := by ring
  case neg =>
    calc
      (‖z‖ : ℂ) / 4 * star (unitPhase z) +
          (‖z‖ : ℂ) / 4 * star (unitPhase z) =
          (‖z‖ : ℂ) * star (unitPhase z) * (1 / 2) := by ring
      _ = star z * (1 / 2) := by rw [norm_mul_star_unitPhase]
      _ = star z / 2 := by ring

lemma coe_re_diag_eq {n : Type*} {D : Matrix n n ℂ} (hD : D.IsHermitian) (i : n) :
    (D i i).re = D i i := by
  apply Complex.ext
  · simp
  · have h := congrArg Complex.im (hD.apply i i)
    simp at h ⊢
    linarith

lemma rankOne_basisVec_apply {n : Type*} [DecidableEq n] (i p q : n) :
    rankOne (basisVec i) p q = if p = i ∧ q = i then 1 else 0 := by
  by_cases hpi : p = i <;> by_cases hqi : q = i <;>
    simp_all [rankOne, basisVec, Matrix.vecMulVec_apply]

noncomputable def diagPart {n : Type*} [Fintype n] [DecidableEq n]
    (D : Matrix n n ℂ) :
    Matrix n n ℂ :=
  ∑ i, (D i i).re • rankOne (basisVec i)

lemma diagPart_apply {n : Type*} [Fintype n] [DecidableEq n]
    {D : Matrix n n ℂ} (hD : D.IsHermitian) (p q : n) :
    diagPart D p q = if p = q then D p p else 0 := by
  unfold diagPart
  let entry : Matrix n n ℂ →+ ℂ :=
    { toFun := fun M ↦ M p q
      map_zero' := rfl
      map_add' := by intros; rfl }
  change entry (∑ i, (D i i).re • rankOne (basisVec i)) = _
  rw [map_sum]
  change (∑ i, ((D i i).re : ℂ) * rankOne (basisVec i) p q) =
    if p = q then D p p else 0
  simp_rw [rankOne_basisVec_apply]
  by_cases hpq : p = q
  · subst q
    simp [coe_re_diag_eq hD]
  · rw [if_neg hpq]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hpi : p = i
    · have hqi : q ≠ i := fun hqi ↦ hpq (hpi.trans hqi.symm)
      simp [hpi, hqi]
    · simp [hpi]

noncomputable def offPart {n : Type*} [Fintype n] [DecidableEq n]
    (D : Matrix n n ℂ) :
    Matrix n n ℂ :=
  ∑ i, ∑ j, if i = j then 0 else offHalf (D i j) i j

lemma offPart_apply {n : Type*} [Fintype n] [DecidableEq n]
    {D : Matrix n n ℂ} (hD : D.IsHermitian) (p q : n) :
    offPart D p q = if p = q then 0 else D p q := by
  unfold offPart
  let entry : Matrix n n ℂ →+ ℂ :=
    { toFun := fun M ↦ M p q
      map_zero' := rfl
      map_add' := by intros; rfl }
  change entry (∑ i, ∑ j, if i = j then 0 else offHalf (D i j) i j) = _
  rw [map_sum]
  simp_rw [map_sum]
  change (∑ i, ∑ j, (if i = j then 0 else offHalf (D i j) i j) p q) =
    if p = q then 0 else D p q
  calc
    (∑ i, ∑ j, (if i = j then 0 else offHalf (D i j) i j) p q) =
        ∑ i, ∑ j, if h : i = j then 0
          else if p = i ∧ q = j then D i j / 2
          else if p = j ∧ q = i then star (D i j) / 2 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      split
      · simp_all
      · rw [offHalf_apply _ ‹i ≠ j›]
    _ = if p = q then 0 else D p q := by
      by_cases hpq : p = q
      · subst q
        rw [if_pos rfl]
        apply Finset.sum_eq_zero
        intro i _
        apply Finset.sum_eq_zero
        intro j _
        by_cases hpi : p = i <;> by_cases hpj : p = j <;> simp_all
      · have hinner (i : n) :
            (∑ j, if h : i = j then 0
              else if p = i ∧ q = j then D i j / 2
              else if p = j ∧ q = i then star (D i j) / 2 else 0) =
              if i = p then D p q / 2 else if i = q then D p q / 2 else 0 := by
          by_cases hip : i = p
          · subst i
            rw [if_pos rfl]
            let f : n → ℂ := fun j =>
              if h : p = j then 0
              else if p = p ∧ q = j then D p j / 2
              else if p = j ∧ q = p then star (D p j) / 2 else 0
            change (∑ j, f j) = D p q / 2
            have hfq : f q = D p q / 2 := by
              simp [f, hpq]
            rw [← hfq]
            apply Finset.sum_eq_single (s := Finset.univ) q
            · intro j _ hjq
              have hqj : q ≠ j := Ne.symm hjq
              by_cases hpj : p = j <;> simp [f, hpj, hqj]
            · simp
          · by_cases hiq : i = q
            · subst i
              rw [if_neg (Ne.symm hpq), if_pos rfl]
              let f : n → ℂ := fun j =>
                if h : q = j then 0
                else if p = q ∧ q = j then D q j / 2
                else if p = j ∧ q = q then star (D q j) / 2 else 0
              change (∑ j, f j) = D p q / 2
              have hqp : q ≠ p := Ne.symm hpq
              have hfp : f p = D p q / 2 := by
                simp [f, hpq, hqp, hD.apply]
              rw [← hfp]
              apply Finset.sum_eq_single (s := Finset.univ) p
              · intro j _ hjp
                have hpj : p ≠ j := Ne.symm hjp
                by_cases hqj : q = j <;> simp [f, hpj, hqj]
              · simp
            · rw [if_neg hip, if_neg hiq]
              have hpi : p ≠ i := Ne.symm hip
              have hqi : q ≠ i := Ne.symm hiq
              simp [hpi, hqi]
        rw [if_neg hpq]
        simp_rw [hinner]
        calc
          (∑ i, if i = p then D p q / 2 else if i = q then D p q / 2 else 0) =
              ∑ i, ((if i = p then D p q / 2 else 0) +
                if i = q then D p q / 2 else 0) := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hip : i = p <;> by_cases hiq : i = q <;> simp_all
          _ = D p q := by
            rw [Finset.sum_add_distrib]
            simp

lemma diagPart_add_offPart {n : Type*} [Fintype n] [DecidableEq n]
    {D : Matrix n n ℂ} (hD : D.IsHermitian) :
    diagPart D + offPart D = D := by
  ext p q
  rw [Matrix.add_apply, diagPart_apply hD, offPart_apply hD]
  split <;> simp_all

abbrev DecompIndex (n : Type*) := Sum n ((n × n) × Bool)

noncomputable def decompCoeff {n : Type*} [DecidableEq n]
    (D : Matrix n n ℂ) : DecompIndex n → ℝ
  | Sum.inl i => (D i i).re
  | Sum.inr ((i, j), positive) =>
      if i = j then 0 else if positive then ‖D i j‖ / 4 else -(‖D i j‖ / 4)

noncomputable def decompVec {n : Type*} [DecidableEq n] (D : Matrix n n ℂ) :
    DecompIndex n → n → ℂ
  | Sum.inl i => basisVec i
  | Sum.inr ((i, j), positive) => offVec (D i j) i j positive

lemma sum_decomp_eq {n : Type*} [Fintype n] [DecidableEq n]
    {D : Matrix n n ℂ} (hD : D.IsHermitian) :
    (∑ a : DecompIndex n, decompCoeff D a • rankOne (decompVec D a)) = D := by
  rw [Fintype.sum_sum_type]
  change diagPart D + _ = D
  have hoff :
      (∑ a : (n × n) × Bool,
        decompCoeff D (Sum.inr a) • rankOne (decompVec D (Sum.inr a))) = offPart D := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    unfold offPart
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i = j
    · simp [decompCoeff, hij]
    · simp [decompCoeff, decompVec, offHalf, hij]
  rw [hoff, diagPart_add_offPart hD]

lemma decomp_cost_eq_entrywise {n : Type*} [Fintype n] [DecidableEq n]
    {D : Matrix n n ℂ} (hD : D.IsHermitian) :
    (∑ a : DecompIndex n,
      |decompCoeff D a| * ∑ k, ‖decompVec D a k‖ ^ 2) =
        ∑ i, ∑ j, ‖D i j‖ := by
  have hdiag (i : n) :
      |decompCoeff D (Sum.inl i)| * ∑ k, ‖decompVec D (Sum.inl i) k‖ ^ 2 =
        ‖D i i‖ := by
    rw [show (D i i) = ((D i i).re : ℂ) from (coe_re_diag_eq hD i).symm]
    simp [decompCoeff, decompVec, sum_norm_sq_basisVec]
  have hoff (i j : n) :
      (∑ positive : Bool,
        |decompCoeff D (Sum.inr ((i, j), positive))| *
          ∑ k, ‖decompVec D (Sum.inr ((i, j), positive)) k‖ ^ 2) =
        if i = j then 0 else ‖D i j‖ := by
    by_cases hij : i = j
    · simp [decompCoeff, hij]
    · simp [decompCoeff, decompVec, hij, sum_norm_sq_offVec]
      rw [abs_of_nonneg (by positivity)]
      ring
  rw [Fintype.sum_sum_type]
  simp_rw [Fintype.sum_prod_type, hdiag, hoff]
  calc
    (∑ i, ‖D i i‖) + ∑ i, ∑ j, (if i = j then 0 else ‖D i j‖) =
        ∑ i, ((∑ j, if i = j then ‖D i j‖ else 0) +
          ∑ j, if i = j then 0 else ‖D i j‖) := by
      rw [Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp
    _ = ∑ i, ∑ j, ‖D i j‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i = j <;> simp [hij]

theorem lidskii_last_proof {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∑ j, |hA.eigenvalues₀ j - hB.eigenvalues₀ j| ≤
      ∑ i, ∑ j, ‖A i j - B i j‖ := by
  let D := B - A
  have hD : D.IsHermitian := hB.sub hA
  have hsum :
      (∑ a : DecompIndex n, decompCoeff D a • rankOne (decompVec D a)) = D :=
    sum_decomp_eq hD
  have hM :
      (A + ∑ a ∈ (Finset.univ : Finset (DecompIndex n)),
        decompCoeff D a • rankOne (decompVec D a)).IsHermitian := by
    simpa [hsum, D] using hB
  have hbound := sum_abs_eigenvalues₀_add_sum_rankOne_le
    (Finset.univ : Finset (DecompIndex n)) (decompCoeff D) (decompVec D) hA hM
  have hcost := decomp_cost_eq_entrywise hD
  have hbound' :
      (∑ i, |hA.eigenvalues₀ i - hM.eigenvalues₀ i|) ≤
        ∑ a : DecompIndex n,
          |decompCoeff D a| * ∑ i, ‖decompVec D a i‖ ^ 2 := by
    simpa using hbound
  rw [hcost] at hbound'
  simpa [hsum, D, norm_sub_rev] using hbound'

end Submission.Helpers
