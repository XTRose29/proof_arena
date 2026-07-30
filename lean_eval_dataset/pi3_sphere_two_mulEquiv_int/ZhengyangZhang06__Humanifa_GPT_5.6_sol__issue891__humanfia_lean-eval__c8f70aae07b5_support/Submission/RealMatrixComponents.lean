import Mathlib

open scoped unitInterval

noncomputable section

namespace Submission.RealMatrixComponents

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Concrete path-component data for an invertible real matrix.  The endpoint
is diagonal with entries in `{1, -1}`, the path stays invertible, and the
endpoint has the same determinant sign as the source. -/
structure SignedDiagonalPath (A : Matrix n n ℝ) where
  signs : n → ℝ
  signs_eq_one_or_neg_one : ∀ i, signs i = 1 ∨ signs i = -1
  path : Path A (diagonal signs)
  det_ne_zero : ∀ s, (path s).det ≠ 0
  sameOrientation : 0 < A.det * (diagonal signs).det

private def diagonalSign (D : n → ℝ) (i : n) : ℝ :=
  if 0 < D i then 1 else -1

omit [Fintype n] [DecidableEq n] in
private theorem diagonalSign_eq_one_or_neg_one
    (D : n → ℝ) (i : n) :
    diagonalSign D i = 1 ∨ diagonalSign D i = -1 := by
  by_cases hi : 0 < D i
  · exact Or.inl (by simp [diagonalSign, hi])
  · exact Or.inr (by simp [diagonalSign, hi])

omit [Fintype n] [DecidableEq n] in
private theorem diagonalSign_mul_pos
    (D : n → ℝ) (hD : ∀ i, D i ≠ 0) (i : n) :
    0 < D i * diagonalSign D i := by
  by_cases hi : 0 < D i
  · simp [diagonalSign, hi]
  · have hineg : D i < 0 := lt_of_le_of_ne (le_of_not_gt hi) (hD i)
    simp [diagonalSign, hi]
    linarith

private def diagonalPath (D : n → ℝ) :
    I → Matrix n n ℝ :=
  fun s => diagonal fun i =>
    (1 - (s : ℝ)) * D i + (s : ℝ) * diagonalSign D i

omit [Fintype n] in
private theorem diagonalPath_continuous (D : n → ℝ) :
    Continuous (diagonalPath D) := by
  apply continuous_matrix
  intro i j
  by_cases hij : i = j
  · subst j
    simp only [diagonalPath, diagonal_apply_eq]
    fun_prop
  · simp only [diagonalPath, diagonal_apply_ne _ hij]
    fun_prop

omit [Fintype n] in
private theorem diagonalPath_zero (D : n → ℝ) :
    diagonalPath D 0 = diagonal D := by
  ext i j
  by_cases hij : i = j <;> simp [diagonalPath, hij]

omit [Fintype n] in
private theorem diagonalPath_one (D : n → ℝ) :
    diagonalPath D 1 = diagonal (diagonalSign D) := by
  ext i j
  by_cases hij : i = j <;> simp [diagonalPath, hij]

omit [Fintype n] [DecidableEq n] in
private theorem diagonalPath_entry_mul_sign_pos
    (D : n → ℝ) (hD : ∀ i, D i ≠ 0) (s : I) (i : n) :
    0 <
      ((1 - (s : ℝ)) * D i +
        (s : ℝ) * diagonalSign D i) *
          diagonalSign D i := by
  have hmain : 0 < D i * diagonalSign D i :=
    diagonalSign_mul_pos D hD i
  have hsignSq : diagonalSign D i * diagonalSign D i = 1 := by
    rcases diagonalSign_eq_one_or_neg_one D i with hi | hi <;>
      simp [hi]
  calc
    ((1 - (s : ℝ)) * D i + (s : ℝ) * diagonalSign D i) *
          diagonalSign D i =
        (1 - (s : ℝ)) * (D i * diagonalSign D i) +
          (s : ℝ) * (diagonalSign D i * diagonalSign D i) := by ring
    _ = (1 - (s : ℝ)) * (D i * diagonalSign D i) + (s : ℝ) := by
      rw [hsignSq, mul_one]
    _ > 0 := by
      by_cases hs : (s : ℝ) = 0
      · simpa [hs] using hmain
      · exact add_pos_of_nonneg_of_pos
          (mul_nonneg (sub_nonneg.mpr s.property.2) hmain.le)
          (lt_of_le_of_ne s.property.1 (Ne.symm hs))

private theorem diagonalPath_det_ne_zero
    (D : n → ℝ) (hD : ∀ i, D i ≠ 0) (s : I) :
    (diagonalPath D s).det ≠ 0 := by
  rw [diagonalPath, det_diagonal]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  have hpos := diagonalPath_entry_mul_sign_pos D hD s i
  intro hzero
  rw [hzero, zero_mul] at hpos
  exact lt_irrefl 0 hpos

private def signedDiagonalPathOfDiagonal
    (D : n → ℝ) (hdet : (diagonal D).det ≠ 0) :
    SignedDiagonalPath (diagonal D) := by
  have hD : ∀ i, D i ≠ 0 := by
    intro i hi
    apply hdet
    rw [det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  refine {
    signs := diagonalSign D
    signs_eq_one_or_neg_one := diagonalSign_eq_one_or_neg_one D
    path := {
      toFun := diagonalPath D
      continuous_toFun := diagonalPath_continuous D
      source' := diagonalPath_zero D
      target' := diagonalPath_one D
    }
    det_ne_zero := diagonalPath_det_ne_zero D hD
    sameOrientation := ?_
  }
  rw [det_diagonal, det_diagonal, ← Finset.prod_mul_distrib]
  exact Finset.prod_pos fun i hi => diagonalSign_mul_pos D hD i

private def transvectionPath
    (t : TransvectionStruct n ℝ) : I → Matrix n n ℝ :=
  fun s => transvection t.i t.j ((1 - (s : ℝ)) * t.c)

omit [Fintype n] in
private theorem transvectionPath_continuous
    (t : TransvectionStruct n ℝ) :
    Continuous (transvectionPath t) := by
  apply continuous_matrix
  intro i j
  simp only [transvectionPath, transvection, Matrix.add_apply, one_apply,
    single_apply]
  by_cases hi : t.i = i <;> by_cases hj : t.j = j <;>
    simp [hi, hj] <;> fun_prop

omit [Fintype n] in
private theorem transvectionPath_zero
    (t : TransvectionStruct n ℝ) :
    transvectionPath t 0 = t.toMatrix := by
  simp [transvectionPath, TransvectionStruct.toMatrix]

omit [Fintype n] in
private theorem transvectionPath_one
    (t : TransvectionStruct n ℝ) :
    transvectionPath t 1 = diagonal (fun _ => 1) := by
  simp [transvectionPath, transvection_zero, diagonal_one]

private def signedDiagonalPathOfTransvection
    (t : TransvectionStruct n ℝ) :
    SignedDiagonalPath t.toMatrix where
  signs := fun _ => 1
  signs_eq_one_or_neg_one := fun _ => Or.inl rfl
  path :=
    { toFun := transvectionPath t
      continuous_toFun := transvectionPath_continuous t
      source' := transvectionPath_zero t
      target' := transvectionPath_one t }
  det_ne_zero s := by
    change
      (transvection t.i t.j ((1 - (s : ℝ)) * t.c)).det ≠ 0
    rw [det_transvection_of_ne t.i t.j t.hij]
    norm_num
  sameOrientation := by
    rw [TransvectionStruct.det, det_diagonal]
    simp

private def mulSignedDiagonalPath {A B : Matrix n n ℝ}
    (a : SignedDiagonalPath A) (b : SignedDiagonalPath B) :
    SignedDiagonalPath (A * B) where
  signs i := a.signs i * b.signs i
  signs_eq_one_or_neg_one i := by
    rcases a.signs_eq_one_or_neg_one i with ha | ha <;>
      rcases b.signs_eq_one_or_neg_one i with hb | hb <;>
      simp [ha, hb]
  path :=
    { toFun := fun s => a.path s * b.path s
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by
        rw [a.path.target, b.path.target,
          diagonal_mul_diagonal] }
  det_ne_zero s := by
    change (a.path s * b.path s).det ≠ 0
    rw [det_mul]
    exact mul_ne_zero (a.det_ne_zero s) (b.det_ne_zero s)
  sameOrientation := by
    have hdiag :
        (diagonal fun i => a.signs i * b.signs i).det =
          (diagonal a.signs).det * (diagonal b.signs).det := by
      simp only [det_diagonal, Finset.prod_mul_distrib]
    rw [det_mul, hdiag]
    rw [mul_mul_mul_comm]
    exact mul_pos a.sameOrientation b.sameOrientation

/-- Every invertible real matrix can be joined through invertible matrices to
a diagonal sign matrix in the same determinant-sign component. -/
theorem exists_signedDiagonalPath
    (A : Matrix n n ℝ) (hA : A.det ≠ 0) :
    Nonempty (SignedDiagonalPath A) := by
  apply Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => Nonempty (SignedDiagonalPath M)) A hA
  · intro D hD
    exact ⟨signedDiagonalPathOfDiagonal D hD⟩
  · intro t
    exact ⟨signedDiagonalPathOfTransvection t⟩
  · intro B C hB hC hPB hPC
    rcases hPB with ⟨b⟩
    rcases hPC with ⟨c⟩
    exact ⟨mulSignedDiagonalPath b c⟩

private theorem toEuclideanLin_ne_zero_of_det_ne_zero
    (A : Matrix n n ℝ) (hA : A.det ≠ 0)
    {v : EuclideanSpace ℝ n} (hv : v ≠ 0) :
    A.toEuclideanLin v ≠ 0 := by
  intro hzero
  have hunit : IsUnit A :=
    A.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hA)
  have hinjective : Function.Injective A.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hunit
  have hmulVec : A *ᵥ WithLp.ofLp v = 0 := by
    change
      WithLp.toLp 2 (A *ᵥ WithLp.ofLp v) =
        WithLp.toLp 2 0 at hzero
    exact WithLp.toLp_injective 2 hzero
  have hcoordinates : WithLp.ofLp v = 0 := by
    apply hinjective
    simpa using hmulVec
  exact hv (WithLp.ofLp_injective 2 hcoordinates)

theorem SignedDiagonalPath.continuous_apply {A : Matrix n n ℝ}
    (p : SignedDiagonalPath A) :
    Continuous
      (fun z : I × EuclideanSpace ℝ n =>
        (p.path z.1).toEuclideanLin z.2) := by
  refine (PiLp.continuous_toLp 2 (fun _ : n => ℝ)).comp ?_
  apply continuous_pi
  intro i
  change Continuous
    (fun z : I × EuclideanSpace ℝ n =>
      ∑ j, p.path z.1 i j * z.2 j)
  fun_prop

/-- A compact path of invertible matrices has a uniform lower norm bound.
After multiplying the path by one positive scalar, every vector of norm at
least one is sent to a vector of norm at least one. -/
theorem SignedDiagonalPath.exists_uniform_scale [Nonempty n]
    {A : Matrix n n ℝ} (p : SignedDiagonalPath A) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (s : I) (v : EuclideanSpace ℝ n), 1 ≤ ‖v‖ →
        1 ≤ ‖K • (p.path s).toEuclideanLin v‖ := by
  have hinverseMatrix :
      Continuous (fun s : I => (p.path s)⁻¹) := by
    rw [continuous_iff_continuousAt]
    intro s
    apply (continuousAt_matrix_inv (p.path s) ?_).comp
      p.path.continuous.continuousAt
    simpa only [Ring.inverse_eq_inv'] using
      continuousAt_inv₀ (p.det_ne_zero s)
  let inverseCLM :
      I → (EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) :=
    fun s => Matrix.toEuclideanCLM (𝕜 := ℝ) ((p.path s)⁻¹)
  have hinverseCLM : Continuous inverseCLM := by
    exact
      (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toLinearMap
        |>.continuous_of_finiteDimensional
        |>.comp hinverseMatrix
  have hnormContinuous : Continuous (fun s => ‖inverseCLM s‖) :=
    hinverseCLM.norm
  obtain ⟨s₀, _, hmax⟩ :=
    isCompact_univ.exists_isMaxOn Set.univ_nonempty
      hnormContinuous.continuousOn
  let K : ℝ := max 1 ‖inverseCLM s₀‖
  have hKone : 1 ≤ K := le_max_left _ _
  refine ⟨K, hKone, ?_⟩
  intro s v hvnorm
  have hunit : IsUnit (p.path s).det :=
    isUnit_iff_ne_zero.mpr (p.det_ne_zero s)
  have hrecover :
      ((p.path s)⁻¹).toEuclideanLin
          ((p.path s).toEuclideanLin v) = v := by
    apply WithLp.ofLp_injective 2
    change
      (p.path s)⁻¹ *ᵥ
          ((p.path s) *ᵥ WithLp.ofLp v) =
        WithLp.ofLp v
    rw [Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul (p.path s) hunit,
      Matrix.one_mulVec]
  have hvBound :
      ‖v‖ ≤
        ‖inverseCLM s‖ * ‖(p.path s).toEuclideanLin v‖ := by
    calc
      ‖v‖ =
          ‖((p.path s)⁻¹).toEuclideanLin
            ((p.path s).toEuclideanLin v)‖ := by rw [hrecover]
      _ ≤ ‖inverseCLM s‖ * ‖(p.path s).toEuclideanLin v‖ := by
        exact (inverseCLM s).le_opNorm _
  have hinverseLe : ‖inverseCLM s‖ ≤ K :=
    (hmax (Set.mem_univ s)).trans (le_max_right _ _)
  have hvBound' :
      ‖v‖ ≤ K * ‖(p.path s).toEuclideanLin v‖ :=
    hvBound.trans
      (mul_le_mul_of_nonneg_right hinverseLe (norm_nonneg _))
  have hone :
      1 ≤ K * ‖(p.path s).toEuclideanLin v‖ :=
    hvnorm.trans hvBound'
  simpa [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (zero_le_one.trans hKone)] using hone

/-- A single invertible matrix admits a positive scale whose image norm
dominates the source norm.  The first conjunct is the boundary form used by
local sphere bubbles. -/
theorem exists_uniform_scale [Nonempty n]
    (A : Matrix n n ℝ) (hA : A.det ≠ 0) :
    ∃ K : ℝ, 1 ≤ K ∧
      (∀ v : EuclideanSpace ℝ n, 1 ≤ ‖v‖ →
        1 ≤ ‖K • A.toEuclideanLin v‖) ∧
      ∀ v : EuclideanSpace ℝ n,
        ‖v‖ ≤ ‖K • A.toEuclideanLin v‖ := by
  obtain ⟨p⟩ := exists_signedDiagonalPath A hA
  obtain ⟨K, hKone, hKpath⟩ := p.exists_uniform_scale
  have hK :
      ∀ v : EuclideanSpace ℝ n, 1 ≤ ‖v‖ →
        1 ≤ ‖K • A.toEuclideanLin v‖ :=
    fun v hv => by simpa only [p.path.source] using hKpath 0 v hv
  refine ⟨K, hKone, hK, ?_⟩
  intro v
  by_cases hv : v = 0
  · simp [hv]
  let r : ℝ := ‖v‖
  have hrpos : 0 < r := by
    dsimp only [r]
    exact norm_pos_iff.mpr hv
  let u : EuclideanSpace ℝ n := r⁻¹ • v
  have hu : ‖u‖ = 1 := by
    dsimp only [u]
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hrpos)]
    dsimp only [r]
    exact inv_mul_cancel₀ hrpos.ne'
  have hunit := hK u hu.ge
  have himage :
      K • A.toEuclideanLin u =
        r⁻¹ • (K • A.toEuclideanLin v) := by
    simp [u, map_smul, smul_smul, mul_comm]
  rw [himage, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hrpos)] at hunit
  calc
    ‖v‖ = r * 1 := by simp [r]
    _ ≤ r * (r⁻¹ * ‖K • A.toEuclideanLin v‖) :=
      mul_le_mul_of_nonneg_left hunit hrpos.le
    _ = ‖K • A.toEuclideanLin v‖ := by
      field_simp [hrpos.ne']

end Submission.RealMatrixComponents
