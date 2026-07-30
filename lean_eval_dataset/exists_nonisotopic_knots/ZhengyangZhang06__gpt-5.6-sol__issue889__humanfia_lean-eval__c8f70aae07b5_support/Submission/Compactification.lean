import Submission.AlgebraicTrefoil
import Submission.Helpers

open LeanEval.KnotTheory
open Complex Set

namespace Submission.Compactification

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

def compactify (p : R3) : PuncturedSphere :=
  ⟨⟨(AlgebraicTrefoil.inverseZ p, AlgebraicTrefoil.inverseW p),
      AlgebraicTrefoil.inverse_normSq p⟩, by
    intro h
    have him := congrArg (fun q : CSphere => q.1.2.im) h
    change (AlgebraicTrefoil.radiusSq p - 1) /
        AlgebraicTrefoil.sphereDenom p = 1 at him
    field_simp [AlgebraicTrefoil.sphereDenom_ne] at him
    rw [AlgebraicTrefoil.sphereDenom] at him
    nlinarith⟩

def decompactify (q : PuncturedSphere) : R3 :=
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

def stereoEquiv : R3 ≃ PuncturedSphere where
  toFun := compactify
  invFun := decompactify
  left_inv := AlgebraicTrefoil.stereo_inverse
  right_inv := by
    intro q
    obtain ⟨hz, hw⟩ :=
      AlgebraicTrefoil.inverse_stereo q.1.2 (punctured_im_ne_one q)
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

def stereoHomeomorph : R3 ≃ₜ PuncturedSphere where
  toEquiv := stereoEquiv
  continuous_toFun := compactify_continuous
  continuous_invFun := decompactify_continuous

theorem compactify_isEmbedding :
    Topology.IsEmbedding (fun p : R3 => (compactify p).1) := by
  change Topology.IsEmbedding (Subtype.val ∘ stereoHomeomorph)
  exact Topology.IsEmbedding.subtypeVal.comp stereoHomeomorph.isEmbedding

theorem range_compactify :
    Set.range (fun p : R3 => (compactify p).1) = {north}ᶜ := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    exact (compactify p).2
  · intro hq
    have hne : q ≠ north := by simpa using hq
    rcases stereoEquiv.surjective ⟨q, hne⟩ with ⟨p, hp⟩
    refine ⟨p, ?_⟩
    exact congrArg Subtype.val hp

def onePointSphereHomeomorph : OnePoint R3 ≃ₜ CSphere :=
  OnePoint.equivOfIsEmbeddingOfRangeEq north
    (fun p : R3 => (compactify p).1)
    compactify_isEmbedding range_compactify

@[simp] theorem onePointSphereHomeomorph_coe (p : R3) :
    onePointSphereHomeomorph (p : OnePoint R3) = (compactify p).1 :=
  OnePoint.equivOfIsEmbeddingOfRangeEq_apply_coe north
    (fun p : R3 => (compactify p).1) compactify_isEmbedding range_compactify p

@[simp] theorem onePointSphereHomeomorph_infty :
    onePointSphereHomeomorph (OnePoint.infty : OnePoint R3) = north :=
  OnePoint.equivOfIsEmbeddingOfRangeEq_apply_infty north
    (fun p : R3 => (compactify p).1) compactify_isEmbedding range_compactify

def polynomial (q : CSphere) : ℂ := 64 * q.1.1 ^ 2 + 45 * q.1.2 ^ 3

@[simp] theorem polynomial_compactify (p : R3) :
    polynomial (compactify p).1 = AlgebraicTrefoil.detectorMap p :=
  rfl

theorem compactify_trefoil_curve (t : ℝ) :
    (compactify (AlgebraicTrefoil.curve t)).1 =
      ⟨(AlgebraicTrefoil.sphereCurveZ t, AlgebraicTrefoil.sphereCurveW t),
        AlgebraicTrefoil.sphereCurve_normSq t⟩ := by
  apply Subtype.ext
  exact Prod.ext (AlgebraicTrefoil.inverseZ_curve t)
    (AlgebraicTrefoil.inverseW_curve t)

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
    let p : R3 := decompactify qp
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

def compactCurve (K : Knot) (t : ℝ) : OnePoint R3 := K.curve t

abbrev CompactComplement (K : Knot) :=
  {q : OnePoint R3 // q ∉ Set.range (compactCurve K)}

private theorem isotopy_compact_range_eq {K1 K2 : Knot} (Phi : AmbientIsotopy)
    (sigma : CircleReparam)
    (hcurve : ∀ t, Phi.H 1 (K1.curve t) = K2.curve (sigma.f t)) :
    (Helpers.ambientHomeomorph Phi 1).onePointCongr '' Set.range (compactCurve K1) =
      Set.range (compactCurve K2) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    refine ⟨sigma.f t, ?_⟩
    have h := congrArg (fun x : R3 => (x : OnePoint R3)) (hcurve t).symm
    simpa [compactCurve, Helpers.ambientHomeomorph] using h
  · rintro _ ⟨u, rfl⟩
    refine ⟨compactCurve K1 (sigma.finv u), ⟨sigma.finv u, rfl⟩, ?_⟩
    have h := congrArg (fun x : R3 => (x : OnePoint R3)) (hcurve (sigma.finv u))
    simpa [compactCurve, Helpers.ambientHomeomorph, sigma.right_inv u] using h

/-- Ambient-isotopic knots have homeomorphic complements in the one-point compactification. -/
def isotopicCompactComplementHomeomorph {K1 K2 : Knot}
    (h : K1.Isotopic K2) : CompactComplement K1 ≃ₜ CompactComplement K2 := by
  let Phi := Classical.choose h
  let sigma := Classical.choose (Classical.choose_spec h)
  have hcurve := Classical.choose_spec (Classical.choose_spec h)
  let e := (Helpers.ambientHomeomorph Phi 1).onePointCongr
  apply e.subtype
  intro x
  have hrange := isotopy_compact_range_eq Phi sigma hcurve
  constructor
  · intro hx hmem
    rw [← hrange] at hmem
    rcases hmem with ⟨y, hy, hey⟩
    exact hx (e.injective hey ▸ hy)
  · intro hx hmem
    apply hx
    rw [← hrange]
    exact ⟨x, hmem, rfl⟩

private theorem hasAbelianFundamentalGroups_homeomorph_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    Helpers.HasAbelianFundamentalGroups X ↔ Helpers.HasAbelianFundamentalGroups Y := by
  constructor
  · intro h y a b
    let g := Helpers.fundamentalGroupMulEquivOfHomeomorph e.symm y
    apply g.injective
    simpa only [map_mul] using h (e.symm y) (g a) (g b)
  · intro h x a b
    let g := Helpers.fundamentalGroupMulEquivOfHomeomorph e x
    apply g.injective
    simpa only [map_mul] using h (e x) (g a) (g b)

theorem isotopic_compact_hasAbelianFundamentalGroups_iff {K1 K2 : Knot}
    (h : K1.Isotopic K2) :
    Helpers.HasAbelianFundamentalGroups (CompactComplement K1) ↔
      Helpers.HasAbelianFundamentalGroups (CompactComplement K2) :=
  hasAbelianFundamentalGroups_homeomorph_iff (isotopicCompactComplementHomeomorph h)

abbrev SphereTrefoilComplement := {q : CSphere // polynomial q ≠ 0}

private theorem trefoil_sphere_range :
    onePointSphereHomeomorph '' Set.range (compactCurve AlgebraicTrefoil.knot) =
      {q : CSphere | polynomial q = 0} := by
  ext q
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    change polynomial (compactify (AlgebraicTrefoil.curve t)).1 = 0
    exact AlgebraicTrefoil.detectorMap_curve t
  · intro hq
    rcases (polynomial_zero_iff_range q).mp hq with ⟨t, ht⟩
    refine ⟨compactCurve AlgebraicTrefoil.knot t, ⟨t, rfl⟩, ?_⟩
    change (compactify (AlgebraicTrefoil.curve t)).1 = q
    exact ht

def trefoilCompactComplementHomeomorph :
    CompactComplement AlgebraicTrefoil.knot ≃ₜ SphereTrefoilComplement := by
  apply onePointSphereHomeomorph.subtype
  intro q
  have hrange := trefoil_sphere_range
  constructor
  · intro hq hzero
    apply hq
    have himage : onePointSphereHomeomorph q ∈
        onePointSphereHomeomorph '' Set.range (compactCurve AlgebraicTrefoil.knot) := by
      rw [hrange]
      exact hzero
    rcases himage with ⟨p, hp, heq⟩
    exact onePointSphereHomeomorph.injective heq ▸ hp
  · intro hq hmem
    apply hq
    have himage : onePointSphereHomeomorph q ∈
        onePointSphereHomeomorph '' Set.range (compactCurve AlgebraicTrefoil.knot) :=
      ⟨q, hmem, rfl⟩
    rw [hrange] at himage
    exact himage

abbrev SphereUnknotComplement := {q : CSphere // q.1.2 ≠ 0}

theorem compactify_roundCircleCurve (t : ℝ) :
    (compactify (Helpers.roundCircleCurve t)).1 =
      ⟨(Complex.exp ((t : ℂ) * I), 0), by
        simp [normSq_apply]
        nlinarith [Real.sin_sq_add_cos_sq t]⟩ := by
  apply Subtype.ext
  apply Prod.ext
  · apply Complex.ext
    · simp [compactify, AlgebraicTrefoil.inverseZ, AlgebraicTrefoil.sphereDenom,
        AlgebraicTrefoil.radiusSq, Complex.exp_ofReal_mul_I_re]
      nlinarith [Real.sin_sq_add_cos_sq t]
    · simp [compactify, AlgebraicTrefoil.inverseZ, AlgebraicTrefoil.sphereDenom,
        AlgebraicTrefoil.radiusSq, Complex.exp_ofReal_mul_I_im]
      nlinarith [Real.sin_sq_add_cos_sq t]
  · apply Complex.ext
    · simp [compactify, AlgebraicTrefoil.inverseW, AlgebraicTrefoil.sphereDenom,
        AlgebraicTrefoil.radiusSq]
    · simp [compactify, AlgebraicTrefoil.inverseW, AlgebraicTrefoil.sphereDenom,
        AlgebraicTrefoil.radiusSq]

private theorem unknot_sphere_range :
    onePointSphereHomeomorph '' Set.range (compactCurve Helpers.roundCircle) =
      {q : CSphere | q.1.2 = 0} := by
  ext q
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    simpa [compactCurve, Helpers.roundCircle] using
      congrArg (fun p : CSphere => p.1.2) (compactify_roundCircleCurve t)
  · intro hq
    have hzsq : normSq q.1.1 = 1 := by
      have hsphere := q.2
      rw [hq, map_zero, add_zero] at hsphere
      exact hsphere
    have hznorm : ‖q.1.1‖ = 1 := by
      rw [Complex.norm_def, hzsq, Real.sqrt_one]
    rcases (Complex.norm_eq_one_iff q.1.1).mp hznorm with ⟨t, ht⟩
    refine ⟨compactCurve Helpers.roundCircle t, ⟨t, rfl⟩, ?_⟩
    rw [show onePointSphereHomeomorph (compactCurve Helpers.roundCircle t) =
        (compactify (Helpers.roundCircleCurve t)).1 by rfl,
      compactify_roundCircleCurve]
    apply Subtype.ext
    exact Prod.ext ht hq.symm

def unknotCompactComplementHomeomorph :
    CompactComplement Helpers.roundCircle ≃ₜ SphereUnknotComplement := by
  apply onePointSphereHomeomorph.subtype
  intro q
  have hrange := unknot_sphere_range
  constructor
  · intro hq hzero
    apply hq
    have himage : onePointSphereHomeomorph q ∈
        onePointSphereHomeomorph '' Set.range (compactCurve Helpers.roundCircle) := by
      rw [hrange]
      exact hzero
    rcases himage with ⟨p, hp, heq⟩
    exact onePointSphereHomeomorph.injective heq ▸ hp
  · intro hq hmem
    apply hq
    have himage : onePointSphereHomeomorph q ∈
        onePointSphereHomeomorph '' Set.range (compactCurve Helpers.roundCircle) :=
      ⟨q, hmem, rfl⟩
    rw [hrange] at himage
    exact himage

end

end Submission.Compactification
