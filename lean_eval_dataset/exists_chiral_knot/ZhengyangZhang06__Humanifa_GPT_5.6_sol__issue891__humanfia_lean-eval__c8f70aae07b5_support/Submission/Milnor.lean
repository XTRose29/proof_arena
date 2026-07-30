import Submission.AlgebraicTrefoil

open Complex

namespace Submission.Milnor

noncomputable section

abbrev CSphere := {q : ℂ × ℂ // normSq q.1 + normSq q.2 = 1}

noncomputable instance : CompactSpace CSphere := by
  apply isCompact_iff_compactSpace.mp
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · exact isClosed_singleton.preimage (by fun_prop)
  · rw [isBounded_iff_forall_norm_le]
    refine ⟨1, ?_⟩
    intro q hq
    rw [Prod.norm_def, max_le_iff]
    have hsphere : normSq q.1 + normSq q.2 = 1 := hq
    rw [normSq_eq_norm_sq, normSq_eq_norm_sq] at hsphere
    constructor <;> nlinarith [norm_nonneg q.1, norm_nonneg q.2]

def north : CSphere := ⟨(0, I), by simp [normSq_apply]⟩

abbrev PuncturedSphere := {q : CSphere // q ≠ north}

def compactify (p : LeanEval.KnotTheory.R3) : PuncturedSphere :=
  ⟨⟨(AlgebraicTrefoil.inverseZ p, AlgebraicTrefoil.inverseW p),
      AlgebraicTrefoil.inverse_normSq p⟩, by
    intro h
    have him := congrArg (fun q : CSphere => q.1.2.im) h
    change (AlgebraicTrefoil.radiusSq p - 1) /
        AlgebraicTrefoil.sphereDenom p = 1 at him
    field_simp [AlgebraicTrefoil.sphereDenom_ne] at him
    rw [AlgebraicTrefoil.sphereDenom] at him
    nlinarith⟩

def decompactify (q : PuncturedSphere) : LeanEval.KnotTheory.R3 :=
  AlgebraicTrefoil.stereo q.1.1.1 q.1.1.2

theorem punctured_im_ne_one (q : PuncturedSphere) : q.1.1.2.im ≠ 1 := by
  intro him
  have hsphere := q.1.2
  simp [normSq_apply, him] at hsphere
  have hzre : q.1.1.1.re = 0 := by
    nlinarith [sq_nonneg q.1.1.1.re, sq_nonneg q.1.1.1.im, sq_nonneg q.1.1.2.re]
  have hzim : q.1.1.1.im = 0 := by
    nlinarith [sq_nonneg q.1.1.1.re, sq_nonneg q.1.1.1.im, sq_nonneg q.1.1.2.re]
  have hwre : q.1.1.2.re = 0 := by
    nlinarith [sq_nonneg q.1.1.1.re, sq_nonneg q.1.1.1.im, sq_nonneg q.1.1.2.re]
  apply q.2
  apply Subtype.ext
  apply Prod.ext <;> apply Complex.ext <;> simp [north, hzre, hzim, hwre, him]

def stereoEquiv : LeanEval.KnotTheory.R3 ≃ PuncturedSphere where
  toFun := compactify
  invFun := decompactify
  left_inv := AlgebraicTrefoil.stereo_inverse
  right_inv := by
    intro q
    obtain ⟨hz, hw⟩ := AlgebraicTrefoil.inverse_stereo q.1.2 (punctured_im_ne_one q)
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext hz hw

theorem compactify_continuous : Continuous compactify := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact AlgebraicTrefoil.inverseZ_contDiff.continuous.prodMk
    AlgebraicTrefoil.inverseW_contDiff.continuous

theorem decompactify_continuous : Continuous decompactify := by
  have hden : Continuous (fun q : PuncturedSphere => 1 - q.1.1.2.im) := by
    fun_prop
  have hden_ne : ∀ q : PuncturedSphere, 1 - q.1.1.2.im ≠ 0 := by
    intro q
    exact sub_ne_zero.mpr (punctured_im_ne_one q).symm
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous ((fun q : PuncturedSphere => q.1.1.1.re) /
      fun q => 1 - q.1.1.2.im)
    exact (show Continuous (fun q : PuncturedSphere => q.1.1.1.re) by fun_prop).div
      hden hden_ne
  · change Continuous ((fun q : PuncturedSphere => q.1.1.1.im) /
      fun q => 1 - q.1.1.2.im)
    exact (show Continuous (fun q : PuncturedSphere => q.1.1.1.im) by fun_prop).div
      hden hden_ne
  · change Continuous ((fun q : PuncturedSphere => q.1.1.2.re) /
      fun q => 1 - q.1.1.2.im)
    exact (show Continuous (fun q : PuncturedSphere => q.1.1.2.re) by fun_prop).div
      hden hden_ne

def stereoHomeomorph : LeanEval.KnotTheory.R3 ≃ₜ PuncturedSphere where
  toEquiv := stereoEquiv
  continuous_toFun := compactify_continuous
  continuous_invFun := decompactify_continuous

theorem compactify_isEmbedding :
    Topology.IsEmbedding (fun p : LeanEval.KnotTheory.R3 => (compactify p).1) := by
  change Topology.IsEmbedding (Subtype.val ∘ stereoHomeomorph)
  exact Topology.IsEmbedding.subtypeVal.comp stereoHomeomorph.isEmbedding

theorem range_compactify :
    Set.range (fun p : LeanEval.KnotTheory.R3 => (compactify p).1) = {north}ᶜ := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    exact (compactify p).2
  · intro hq
    have hne : q ≠ north := by simpa using hq
    rcases stereoEquiv.surjective ⟨q, hne⟩ with ⟨p, hp⟩
    refine ⟨p, ?_⟩
    exact congrArg Subtype.val hp

noncomputable def onePointSphereHomeomorph :
    OnePoint LeanEval.KnotTheory.R3 ≃ₜ CSphere :=
  OnePoint.equivOfIsEmbeddingOfRangeEq north
    (fun p : LeanEval.KnotTheory.R3 => (compactify p).1)
    compactify_isEmbedding range_compactify

@[simp] theorem onePointSphereHomeomorph_coe (p : LeanEval.KnotTheory.R3) :
    onePointSphereHomeomorph (p : OnePoint LeanEval.KnotTheory.R3) = (compactify p).1 :=
  OnePoint.equivOfIsEmbeddingOfRangeEq_apply_coe north
    (fun p : LeanEval.KnotTheory.R3 => (compactify p).1) compactify_isEmbedding range_compactify p

@[simp] theorem onePointSphereHomeomorph_infty :
    onePointSphereHomeomorph (OnePoint.infty : OnePoint LeanEval.KnotTheory.R3) = north :=
  OnePoint.equivOfIsEmbeddingOfRangeEq_apply_infty north
    (fun p : LeanEval.KnotTheory.R3 => (compactify p).1) compactify_isEmbedding range_compactify

def rotate (n : ℕ) (s : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (((n : ℝ) * s : ℝ) * I) * z

theorem normSq_exp_mul_I (s : ℝ) : normSq (Complex.exp ((s : ℂ) * I)) = 1 := by
  rw [normSq_eq_norm_sq, norm_exp_ofReal_mul_I, one_pow]

theorem normSq_rotate (n : ℕ) (s : ℝ) (z : ℂ) :
    normSq (rotate n s z) = normSq z := by
  rw [rotate, normSq_mul, normSq_exp_mul_I, one_mul]

theorem rotate_zero (n : ℕ) (z : ℂ) : rotate n 0 z = z := by
  simp [rotate]

theorem rotate_add (n : ℕ) (s t : ℝ) (z : ℂ) :
    rotate n s (rotate n t z) = rotate n (s + t) z := by
  unfold rotate
  rw [← mul_assoc]
  rw [← Complex.exp_add]
  rw [show (((n : ℝ) * s : ℝ) : ℂ) * I + (((n : ℝ) * t : ℝ) : ℂ) * I =
      (((n : ℝ) * (s + t) : ℝ) : ℂ) * I by
    push_cast
    ring]

def weightedRotate (s : ℝ) : CSphere ≃ CSphere where
  toFun q := ⟨(rotate 3 s q.1.1, rotate 2 s q.1.2), by
    rw [normSq_rotate, normSq_rotate]
    exact q.2⟩
  invFun q := ⟨(rotate 3 (-s) q.1.1, rotate 2 (-s) q.1.2), by
    rw [normSq_rotate, normSq_rotate]
    exact q.2⟩
  left_inv q := by
    apply Subtype.ext
    apply Prod.ext <;> simp [rotate_add, rotate_zero]
  right_inv q := by
    apply Subtype.ext
    apply Prod.ext <;> simp [rotate_add, rotate_zero]

def weightedRotateHomeomorph (s : ℝ) : CSphere ≃ₜ CSphere where
  toEquiv := weightedRotate s
  continuous_toFun := by
    apply Continuous.subtype_mk
    change Continuous (fun q : CSphere =>
      (rotate 3 s q.1.1, rotate 2 s q.1.2))
    unfold rotate
    fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    change Continuous (fun q : CSphere =>
      (rotate 3 (-s) q.1.1, rotate 2 (-s) q.1.2))
    unfold rotate
    fun_prop

theorem weightedRotate_continuous :
    Continuous (fun x : ℝ × CSphere => weightedRotate x.1 x.2) := by
  apply Continuous.subtype_mk
  unfold rotate
  fun_prop

def polynomial (q : CSphere) : ℂ := 64 * q.1.1 ^ 2 + 45 * q.1.2 ^ 3

@[simp] theorem polynomial_compactify (p : LeanEval.KnotTheory.R3) :
    polynomial (compactify p).1 = AlgebraicTrefoil.detectorMap p :=
  rfl

theorem compactify_curve (t : ℝ) :
    (compactify (AlgebraicTrefoil.curve t)).1 =
      ⟨(AlgebraicTrefoil.sphereCurveZ t, AlgebraicTrefoil.sphereCurveW t),
        AlgebraicTrefoil.sphereCurve_normSq t⟩ := by
  apply Subtype.ext
  exact Prod.ext (AlgebraicTrefoil.inverseZ_curve t) (AlgebraicTrefoil.inverseW_curve t)

theorem polynomial_north_ne_zero : polynomial north ≠ 0 := by
  simp [polynomial, north]

theorem polynomial_zero_iff_range (q : CSphere) :
    polynomial q = 0 ↔
      q ∈ Set.range (fun t : ℝ => (compactify (AlgebraicTrefoil.curve t)).1) := by
  constructor
  · intro hzero
    have hne : q ≠ north := by
      intro h
      rw [h] at hzero
      exact polynomial_north_ne_zero hzero
    let qp : PuncturedSphere := ⟨q, hne⟩
    let p : LeanEval.KnotTheory.R3 := decompactify qp
    have hp : compactify p = qp := stereoEquiv.apply_symm_apply qp
    have hdet : AlgebraicTrefoil.detectorMap p = 0 := by
      rw [← polynomial_compactify]
      rw [congrArg Subtype.val hp]
      exact hzero
    rcases (AlgebraicTrefoil.detectorMap_zero_iff p).mp hdet with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    calc
      (compactify (AlgebraicTrefoil.curve t)).1 = (compactify p).1 := by rw [ht]
      _ = q := congrArg Subtype.val hp
  · rintro ⟨t, rfl⟩
    exact AlgebraicTrefoil.detectorMap_curve t

theorem polynomial_weightedRotate (s : ℝ) (q : CSphere) :
    polynomial (weightedRotate s q) =
      Complex.exp (((6 : ℝ) * s : ℝ) * I) * polynomial q := by
  have h2 : Complex.exp (((3 : ℝ) * s : ℝ) * I) ^ 2 =
      Complex.exp (((6 : ℝ) * s : ℝ) * I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h3 : Complex.exp (((2 : ℝ) * s : ℝ) * I) ^ 3 =
      Complex.exp (((6 : ℝ) * s : ℝ) * I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hr2 : rotate 3 s q.1.1 ^ 2 =
      Complex.exp (((6 : ℝ) * s : ℝ) * I) * q.1.1 ^ 2 := by
    unfold rotate
    rw [mul_pow]
    rw [show Complex.exp (((((3 : ℕ) : ℝ) * s : ℝ) : ℂ) * I) ^ 2 =
      Complex.exp (((6 : ℝ) * s : ℝ) * I) by simpa using h2]
  have hr3 : rotate 2 s q.1.2 ^ 3 =
      Complex.exp (((6 : ℝ) * s : ℝ) * I) * q.1.2 ^ 3 := by
    unfold rotate
    rw [mul_pow]
    rw [show Complex.exp (((((2 : ℕ) : ℝ) * s : ℝ) : ℂ) * I) ^ 3 =
      Complex.exp (((6 : ℝ) * s : ℝ) * I) by simpa using h3]
  change 64 * rotate 3 s q.1.1 ^ 2 + 45 * rotate 2 s q.1.2 ^ 3 =
    Complex.exp (((6 : ℝ) * s : ℝ) * I) *
      (64 * q.1.1 ^ 2 + 45 * q.1.2 ^ 3)
  rw [hr2, hr3]
  ring

def monodromy : CSphere ≃ CSphere := weightedRotate (Real.pi / 3)

theorem polynomial_monodromy (q : CSphere) : polynomial (monodromy q) = polynomial q := by
  rw [monodromy, polynomial_weightedRotate]
  have harg : (((6 : ℝ) * (Real.pi / 3) : ℝ) : ℂ) * I =
      2 * (Real.pi : ℂ) * I := by
    push_cast
    ring
  rw [harg, Complex.exp_two_pi_mul_I, one_mul]

def Fiber := {q : CSphere // 0 < (polynomial q).re ∧ (polynomial q).im = 0}

instance : TopologicalSpace Fiber := by
  unfold Fiber
  infer_instance

def fiberMonodromy : Fiber ≃ Fiber where
  toFun q := ⟨monodromy q.1, by rw [polynomial_monodromy]; exact q.2⟩
  invFun q := ⟨monodromy.symm q.1, by
    have h := polynomial_monodromy (monodromy.symm q.1)
    rw [monodromy.apply_symm_apply] at h
    rw [← h]
    exact q.2⟩
  left_inv q := by
    apply Subtype.ext
    exact monodromy.symm_apply_apply q.1
  right_inv q := by
    apply Subtype.ext
    exact monodromy.apply_symm_apply q.1

def fiberMonodromyHomeomorph : Fiber ≃ₜ Fiber where
  toEquiv := fiberMonodromy
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (weightedRotateHomeomorph (Real.pi / 3)).continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (weightedRotateHomeomorph (Real.pi / 3)).symm.continuous.comp
      continuous_subtype_val

end

end Submission.Milnor
