import Submission.PlanarIsotopy

open LeanEval.Geometry.FaryMilnorProblem
open MeasureTheory
open ProbabilityTheory
open Set
open Filter
open scoped ENNReal
open scoped RealInnerProductSpace

namespace Submission.Helpers

def gaussianSeparatingDirections (x y : Space) : Set Space :=
  {u | inner ℝ u x * inner ℝ u y < 0}

theorem measurableSet_gaussianSeparatingDirections (x y : Space) :
    MeasurableSet (gaussianSeparatingDirections x y) := by
  unfold gaussianSeparatingDirections
  have hx : Continuous (fun u : Space => inner ℝ u x) :=
    continuous_id.inner continuous_const
  have hy : Continuous (fun u : Space => inner ℝ u y) :=
    continuous_id.inner continuous_const
  exact measurableSet_lt (hx.mul hy).measurable measurable_const

theorem preimage_gaussianSeparatingDirections_linearIsometryEquiv
    (e : Space ≃ₗᵢ[ℝ] Space) (x y : Space) :
    e ⁻¹' gaussianSeparatingDirections (e x) (e y) =
      gaussianSeparatingDirections x y := by
  ext u
  simp [gaussianSeparatingDirections, e.inner_map_map]

theorem stdGaussian_gaussianSeparatingDirections_linearIsometryEquiv
    (e : Space ≃ₗᵢ[ℝ] Space) (x y : Space) :
    stdGaussian Space (gaussianSeparatingDirections (e x) (e y)) =
      stdGaussian Space (gaussianSeparatingDirections x y) := by
  calc
    stdGaussian Space (gaussianSeparatingDirections (e x) (e y)) =
        (stdGaussian Space).map e
          (gaussianSeparatingDirections (e x) (e y)) := by
      rw [stdGaussian_map e]
    _ = stdGaussian Space
        (e ⁻¹' gaussianSeparatingDirections (e x) (e y)) := by
      rw [Measure.map_apply e.continuous.measurable
        (measurableSet_gaussianSeparatingDirections (e x) (e y))]
    _ = stdGaussian Space (gaussianSeparatingDirections x y) := by
      rw [preimage_gaussianSeparatingDirections_linearIsometryEquiv]

noncomputable def planarGaussianDensityReal (p : ℝ × ℝ) : ℝ :=
  gaussianPDFReal 0 1 p.1 * gaussianPDFReal 0 1 p.2

noncomputable def planarGaussianDensity (p : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (planarGaussianDensityReal p)

theorem planarGaussianDensity_eq (p : ℝ × ℝ) :
    planarGaussianDensity p = gaussianPDF 0 1 p.1 * gaussianPDF 0 1 p.2 := by
  rw [planarGaussianDensity, planarGaussianDensityReal, gaussianPDF, gaussianPDF]
  rw [ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 p.1)]

theorem planarGaussianDensityReal_polar (r θ : ℝ) :
    planarGaussianDensityReal (polarCoord.symm (r, θ)) =
      planarGaussianDensityReal (r, 0) := by
  change gaussianPDFReal 0 1 (r * Real.cos θ) *
      gaussianPDFReal 0 1 (r * Real.sin θ) =
    gaussianPDFReal 0 1 r * gaussianPDFReal 0 1 0
  simp only [gaussianPDFReal, sub_zero, NNReal.coe_one, mul_one]
  ring_nf
  have harg : r ^ 2 * Real.cos θ ^ 2 * (-1 / 2 : ℝ) +
      r ^ 2 * Real.sin θ ^ 2 * (-1 / 2 : ℝ) = r ^ 2 * (-1 / 2 : ℝ) := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  conv_lhs => rw [mul_assoc, ← Real.exp_add]
  simp only [Real.exp_zero, mul_one]
  rw [harg]

theorem planarGaussianDensity_polar (r θ : ℝ) :
    planarGaussianDensity (polarCoord.symm (r, θ)) =
      planarGaussianDensity (r, 0) := by
  unfold planarGaussianDensity
  rw [planarGaussianDensityReal_polar]

noncomputable def planarStandardGaussian : Measure (ℝ × ℝ) :=
  (gaussianReal 0 1).prod (gaussianReal 0 1)

theorem measurable_planarGaussianDensity : Measurable planarGaussianDensity := by
  rw [show planarGaussianDensity = fun p : ℝ × ℝ =>
      gaussianPDF 0 1 p.1 * gaussianPDF 0 1 p.2 by
    funext p
    exact planarGaussianDensity_eq p]
  fun_prop

theorem planarStandardGaussian_eq_withDensity :
    planarStandardGaussian =
      (volume : Measure (ℝ × ℝ)).withDensity planarGaussianDensity := by
  unfold planarStandardGaussian
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero]
  rw [prod_withDensity (measurable_gaussianPDF 0 1)
    (measurable_gaussianPDF 0 1)]
  congr 1
  funext p
  exact (planarGaussianDensity_eq p).symm

theorem planarStandardGaussian_apply {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) :
    planarStandardGaussian s = ∫⁻ p in s, planarGaussianDensity p := by
  rw [planarStandardGaussian_eq_withDensity, withDensity_apply _ hs]

noncomputable def planarAngle (p : ℝ × ℝ) : ℝ :=
  Complex.arg (Complex.equivRealProd.symm p)

def planarAngularSet (A : Set ℝ) : Set (ℝ × ℝ) :=
  planarAngle ⁻¹' A

theorem measurable_planarAngle : Measurable planarAngle := by
  unfold planarAngle
  apply Complex.measurable_arg.comp
  have h : Measurable (fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * Complex.I) := by
    fun_prop
  rw [show (⇑Complex.equivRealProd.symm : (ℝ × ℝ) → ℂ) =
      fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * Complex.I by
    funext p
    exact Complex.equivRealProd_symm_apply p]
  exact h

theorem measurableSet_planarAngularSet {A : Set ℝ} (hA : MeasurableSet A) :
    MeasurableSet (planarAngularSet A) := by
  exact hA.preimage measurable_planarAngle

theorem planarAngle_polarCoord_symm {p : ℝ × ℝ} (hp : p ∈ polarCoord.target) :
    planarAngle (polarCoord.symm p) = p.2 := by
  have h := congrArg Prod.snd (polarCoord.right_inv hp)
  simpa [planarAngle, polarCoord] using h

theorem mem_planarAngularSet_polarCoord_symm {A : Set ℝ} {p : ℝ × ℝ}
    (hp : p ∈ polarCoord.target) :
    polarCoord.symm p ∈ planarAngularSet A ↔ p.2 ∈ A := by
  change planarAngle (polarCoord.symm p) ∈ A ↔ p.2 ∈ A
  rw [planarAngle_polarCoord_symm hp]

noncomputable def planarGaussianRadialIntegrand (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal r * planarGaussianDensity (r, 0)

noncomputable def planarGaussianRadialMass : ℝ≥0∞ :=
  ∫⁻ r in Ioi (0 : ℝ), planarGaussianRadialIntegrand r

theorem measurable_planarGaussianRadialIntegrand :
    Measurable planarGaussianRadialIntegrand := by
  unfold planarGaussianRadialIntegrand
  exact (ENNReal.measurable_ofReal.comp measurable_id).mul
    (measurable_planarGaussianDensity.comp (measurable_id.prodMk measurable_const))

theorem planarStandardGaussian_planarAngularSet_eq
    {A : Set ℝ} (hA : MeasurableSet A) (hsub : A ⊆ Ioo (-Real.pi) Real.pi) :
    planarStandardGaussian (planarAngularSet A) =
      planarGaussianRadialMass * volume A := by
  rw [planarStandardGaussian_apply (measurableSet_planarAngularSet hA)]
  rw [← lintegral_indicator (measurableSet_planarAngularSet hA)]
  rw [← lintegral_comp_polarCoord_symm]
  change (∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal p.1 *
        (planarAngularSet A).indicator planarGaussianDensity
          (polarCoord.symm p)) = _
  calc
    (∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal p.1 *
          (planarAngularSet A).indicator planarGaussianDensity
            (polarCoord.symm p)) =
        ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
          (univ ×ˢ A).indicator
            (fun p : ℝ × ℝ => planarGaussianRadialIntegrand p.1) p := by
      refine setLIntegral_congr_fun
        (measurableSet_Ioi.prod measurableSet_Ioo) (fun p hp => ?_)
      by_cases hpA : p.2 ∈ A
      · have hmem : polarCoord.symm p ∈ planarAngularSet A :=
          (mem_planarAngularSet_polarCoord_symm hp).2 hpA
        rw [Set.indicator_of_mem hmem]
        rw [Set.indicator_of_mem (show p ∈ univ ×ˢ A from ⟨mem_univ _, hpA⟩)]
        unfold planarGaussianRadialIntegrand
        rw [planarGaussianDensity_polar]
      · have hmem : polarCoord.symm p ∉ planarAngularSet A := by
          intro h
          exact hpA ((mem_planarAngularSet_polarCoord_symm hp).1 h)
        rw [Set.indicator_of_notMem hmem]
        rw [Set.indicator_of_notMem (show p ∉ univ ×ˢ A by
          intro h
          exact hpA h.2)]
        simp
    _ = ∫⁻ p in Ioi (0 : ℝ) ×ˢ A,
          planarGaussianRadialIntegrand p.1 := by
      rw [setLIntegral_indicator (MeasurableSet.univ.prod hA)]
      have hset : (univ ×ˢ A) ∩ (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) =
          Ioi (0 : ℝ) ×ˢ A := by
        ext p
        constructor
        · rintro ⟨⟨_hpUniv, hpA⟩, ⟨hp0, _hppi⟩⟩
          exact ⟨hp0, hpA⟩
        · rintro ⟨hp0, hpA⟩
          exact ⟨⟨mem_univ _, hpA⟩, ⟨hp0, hsub hpA⟩⟩
      rw [hset]
    _ = planarGaussianRadialMass * volume A := by
      change (∫⁻ p in Ioi (0 : ℝ) ×ˢ A,
        planarGaussianRadialIntegrand p.1
          ∂((volume : Measure ℝ).prod (volume : Measure ℝ))) = _
      rw [setLIntegral_prod]
      · simp only [planarGaussianRadialMass]
        simp_rw [setLIntegral_const]
        rw [lintegral_mul_const (μ := volume.restrict (Ioi (0 : ℝ)))
          (volume A) measurable_planarGaussianRadialIntegrand]
      · exact (measurable_planarGaussianRadialIntegrand.comp measurable_fst).aemeasurable

theorem polarCoord_source_subset_planarAngularSet_Ioo_neg_pi_pi :
    polarCoord.source ⊆ planarAngularSet (Ioo (-Real.pi) Real.pi) := by
  intro p hp
  change -Real.pi < Complex.arg (Complex.equivRealProd.symm p) ∧
    Complex.arg (Complex.equivRealProd.symm p) < Real.pi
  constructor
  · exact Complex.neg_pi_lt_arg _
  · rw [Complex.arg_lt_pi_iff]
    change 0 ≤ p.1 ∨ p.2 ≠ 0
    rcases hp with hp | hp
    · exact Or.inl hp.le
    · exact Or.inr hp

theorem planarStandardGaussian_planarAngularSet_Ioo_neg_pi_pi :
    planarStandardGaussian (planarAngularSet (Ioo (-Real.pi) Real.pi)) = 1 := by
  have hac : planarStandardGaussian ≪ (volume : Measure (ℝ × ℝ)) := by
    rw [planarStandardGaussian_eq_withDensity]
    exact withDensity_absolutelyContinuous _ _
  have haeVolume : planarAngularSet (Ioo (-Real.pi) Real.pi) =ᵐ[volume]
      (univ : Set (ℝ × ℝ)) := by
    filter_upwards [polarCoord_source_ae_eq_univ] with p hp
    apply propext
    constructor
    · intro _
      exact mem_univ p
    · intro _
      have hpSource : p ∈ polarCoord.source :=
        (iff_of_eq hp).mpr (mem_univ p)
      exact polarCoord_source_subset_planarAngularSet_Ioo_neg_pi_pi
        hpSource
  have hae := hac.ae_eq haeVolume
  rw [measure_congr hae]
  simp [planarStandardGaussian]

theorem planarGaussianRadialMass_eq :
    planarGaussianRadialMass = (ENNReal.ofReal (2 * Real.pi))⁻¹ := by
  have hfactor := planarStandardGaussian_planarAngularSet_eq
    measurableSet_Ioo (Subset.rfl : Ioo (-Real.pi) Real.pi ⊆
      Ioo (-Real.pi) Real.pi)
  rw [planarStandardGaussian_planarAngularSet_Ioo_neg_pi_pi,
    Real.volume_Ioo] at hfactor
  have hlength : Real.pi - -Real.pi = 2 * Real.pi := by ring
  rw [hlength] at hfactor
  exact ENNReal.eq_inv_of_mul_eq_one_left hfactor.symm

theorem planarStandardGaussian_planarAngularSet_eq_normalized
    {A : Set ℝ} (hA : MeasurableSet A) (hsub : A ⊆ Ioo (-Real.pi) Real.pi) :
    planarStandardGaussian (planarAngularSet A) =
      volume A * (ENNReal.ofReal (2 * Real.pi))⁻¹ := by
  rw [planarStandardGaussian_planarAngularSet_eq hA hsub,
    planarGaussianRadialMass_eq, mul_comm]

def symmetricSeparatingAngles (a : ℝ) : Set ℝ :=
  Ioo (-Real.pi / 2 - a / 2) (-Real.pi / 2 + a / 2) ∪
    Ioo (Real.pi / 2 - a / 2) (Real.pi / 2 + a / 2)

theorem measurableSet_symmetricSeparatingAngles (a : ℝ) :
    MeasurableSet (symmetricSeparatingAngles a) := by
  exact measurableSet_Ioo.union measurableSet_Ioo

theorem symmetricSeparatingAngles_subset {a : ℝ}
    (_ha0 : 0 ≤ a) (hapi : a ≤ Real.pi) :
    symmetricSeparatingAngles a ⊆ Ioo (-Real.pi) Real.pi := by
  intro θ hθ
  rcases hθ with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
  · constructor <;> linarith [Real.pi_pos]
  · constructor <;> linarith [Real.pi_pos]

theorem volume_symmetricSeparatingAngles {a : ℝ}
    (ha0 : 0 ≤ a) (hapi : a ≤ Real.pi) :
    volume (symmetricSeparatingAngles a) = ENNReal.ofReal (2 * a) := by
  have hdisjoint : Disjoint
      (Ioo (-Real.pi / 2 - a / 2) (-Real.pi / 2 + a / 2))
      (Ioo (Real.pi / 2 - a / 2) (Real.pi / 2 + a / 2)) := by
    rw [Set.disjoint_left]
    intro x hx hxp
    rcases hx with ⟨_, hxhi⟩
    rcases hxp with ⟨hxlo, _⟩
    linarith
  rw [symmetricSeparatingAngles, measure_union hdisjoint measurableSet_Ioo,
    Real.volume_Ioo, Real.volume_Ioo]
  have hlengthNeg : -Real.pi / 2 + a / 2 - (-Real.pi / 2 - a / 2) = a := by
    ring
  have hlengthPos : Real.pi / 2 + a / 2 - (Real.pi / 2 - a / 2) = a := by
    ring
  rw [hlengthNeg, hlengthPos, ← ENNReal.ofReal_add ha0 ha0]
  congr 1
  ring

theorem cos_neg_of_neg_three_pi_div_two_lt_of_lt_neg_pi_div_two {x : ℝ}
    (hxlow : -(Real.pi + Real.pi / 2) < x)
    (hxhigh : x < -(Real.pi / 2)) :
    Real.cos x < 0 := by
  rw [← Real.cos_neg]
  exact Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)

theorem cos_nonpos_of_neg_three_pi_div_two_le_of_le_neg_pi_div_two {x : ℝ}
    (hxlow : -(Real.pi + Real.pi / 2) ≤ x)
    (hxhigh : x ≤ -(Real.pi / 2)) :
    Real.cos x ≤ 0 := by
  rw [← Real.cos_neg]
  exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)

theorem cos_sub_mul_cos_add_neg_iff_mem_symmetricSeparatingAngles
    {a θ : ℝ} (ha0 : 0 ≤ a) (hapi : a ≤ Real.pi)
    (hθ : θ ∈ Ioo (-Real.pi) Real.pi) :
    Real.cos (θ - a / 2) * Real.cos (θ + a / 2) < 0 ↔
      θ ∈ symmetricSeparatingAngles a := by
  rw [mul_neg_iff]
  constructor
  · rintro (hposneg | hnegpos)
    · right
      rcases hposneg with ⟨hleftPos, hrightNeg⟩
      constructor
      · by_contra hnot
        have hrightUpper : θ + a / 2 ≤ Real.pi / 2 := by linarith
        by_cases hrightLower : -(Real.pi / 2) ≤ θ + a / 2
        · exact (not_lt_of_ge
            (Real.cos_nonneg_of_neg_pi_div_two_le_of_le
              hrightLower hrightUpper)) hrightNeg
        · have hleftLow : -(Real.pi + Real.pi / 2) < θ - a / 2 := by
            linarith [hθ.1]
          have hleftHigh : θ - a / 2 < -(Real.pi / 2) := by linarith
          exact (not_lt_of_ge hleftPos.le)
            (cos_neg_of_neg_three_pi_div_two_lt_of_lt_neg_pi_div_two
              hleftLow hleftHigh)
      · by_contra hnot
        have hleftLower : Real.pi / 2 ≤ θ - a / 2 := by linarith
        have hleftUpper : θ - a / 2 ≤ Real.pi + Real.pi / 2 := by
          linarith [hθ.2, Real.pi_pos]
        exact (not_lt_of_ge
          (Real.cos_nonpos_of_pi_div_two_le_of_le hleftLower hleftUpper)) hleftPos
    · left
      rcases hnegpos with ⟨hleftNeg, hrightPos⟩
      constructor
      · by_contra hnot
        have hrightUpper : θ + a / 2 ≤ -(Real.pi / 2) := by linarith
        have hrightLower : -(Real.pi + Real.pi / 2) ≤ θ + a / 2 := by
          linarith [hθ.1, Real.pi_pos]
        exact (not_lt_of_ge
          (cos_nonpos_of_neg_three_pi_div_two_le_of_le_neg_pi_div_two
            hrightLower hrightUpper)) hrightPos
      · by_contra hnot
        have hleftLower : -(Real.pi / 2) ≤ θ - a / 2 := by linarith
        by_cases hleftUpper : θ - a / 2 ≤ Real.pi / 2
        · exact (not_lt_of_ge
            (Real.cos_nonneg_of_neg_pi_div_two_le_of_le
              hleftLower hleftUpper)) hleftNeg
        · have hrightLow : Real.pi / 2 < θ + a / 2 := by linarith
          have hrightHigh : θ + a / 2 < Real.pi + Real.pi / 2 := by
            linarith [hθ.2]
          exact (not_lt_of_ge hrightPos.le)
            (Real.cos_neg_of_pi_div_two_lt_of_lt hrightLow hrightHigh)
  · rintro (hneg | hpos)
    · right
      rcases hneg with ⟨hnegLow, hnegHigh⟩
      constructor
      · apply cos_neg_of_neg_three_pi_div_two_lt_of_lt_neg_pi_div_two
        · linarith
        · linarith
      · apply Real.cos_pos_of_mem_Ioo
        constructor <;> linarith
    · left
      rcases hpos with ⟨hposLow, hposHigh⟩
      constructor
      · apply Real.cos_pos_of_mem_Ioo
        constructor <;> linarith
      · apply Real.cos_neg_of_pi_div_two_lt_of_lt <;> linarith

theorem cos_sub_mul_cos_add_neg_iff_mem_symmetricSeparatingAngles_Ioc
    {a θ : ℝ} (ha0 : 0 ≤ a) (hapi : a ≤ Real.pi)
    (hθ : θ ∈ Ioc (-Real.pi) Real.pi) :
    Real.cos (θ - a / 2) * Real.cos (θ + a / 2) < 0 ↔
      θ ∈ symmetricSeparatingAngles a := by
  rcases hθ.2.lt_or_eq with hθpi | rfl
  · exact cos_sub_mul_cos_add_neg_iff_mem_symmetricSeparatingAngles
      ha0 hapi ⟨hθ.1, hθpi⟩
  · constructor
    · intro h
      have hproduct : Real.cos (Real.pi - a / 2) *
          Real.cos (Real.pi + a / 2) = Real.cos (a / 2) ^ 2 := by
        rw [Real.cos_pi_sub, Real.cos_add]
        simp
        ring
      rw [hproduct] at h
      exact ((not_lt_of_ge (sq_nonneg _)) h).elim
    · intro h
      have hmem := symmetricSeparatingAngles_subset ha0 hapi h
      exact ((lt_irrefl Real.pi) hmem.2).elim

def planarSymmetricSeparatingDirections (a : ℝ) : Set (ℝ × ℝ) :=
  {p | (p.1 * Real.cos (a / 2) + p.2 * Real.sin (a / 2)) *
      (p.1 * Real.cos (a / 2) - p.2 * Real.sin (a / 2)) < 0}

theorem planarSymmetricSeparatingDirections_eq {a : ℝ}
    (ha0 : 0 ≤ a) (hapi : a ≤ Real.pi) :
    planarSymmetricSeparatingDirections a =
      planarAngularSet (symmetricSeparatingAngles a) := by
  ext p
  let z : ℂ := Complex.equivRealProd.symm p
  let θ : ℝ := Complex.arg z
  have hre : ‖z‖ * Real.cos θ = p.1 := by
    dsimp [θ]
    rw [Complex.norm_mul_cos_arg]
    simp [z, Complex.equivRealProd_symm_apply]
  have him : ‖z‖ * Real.sin θ = p.2 := by
    dsimp [θ]
    rw [Complex.norm_mul_sin_arg]
    simp [z, Complex.equivRealProd_symm_apply]
  have hleft : p.1 * Real.cos (a / 2) + p.2 * Real.sin (a / 2) =
      ‖z‖ * Real.cos (θ - a / 2) := by
    rw [← hre, ← him, Real.cos_sub]
    ring
  have hright : p.1 * Real.cos (a / 2) - p.2 * Real.sin (a / 2) =
      ‖z‖ * Real.cos (θ + a / 2) := by
    rw [← hre, ← him, Real.cos_add]
    ring
  by_cases hz : z = 0
  · have hp : p = 0 := by
      apply Complex.equivRealProd.symm.injective
      simpa [z] using hz
    subst p
    simp only [planarSymmetricSeparatingDirections, Set.mem_setOf_eq,
      Prod.fst_zero, zero_mul, Prod.snd_zero, zero_add, zero_sub,
      lt_self_iff_false, planarAngularSet, Set.mem_preimage]
    change False ↔ planarAngle 0 ∈ symmetricSeparatingAngles a
    rw [show planarAngle 0 = 0 by simp [planarAngle]]
    constructor
    · intro h
      contradiction
    · intro h
      rcases h with ⟨_, hhigh⟩ | ⟨hlow, _⟩ <;> linarith
  · have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hnormSq : 0 < ‖z‖ * ‖z‖ := mul_pos hnorm hnorm
    have hscale :
        (‖z‖ * Real.cos (θ - a / 2)) *
            (‖z‖ * Real.cos (θ + a / 2)) < 0 ↔
          Real.cos (θ - a / 2) * Real.cos (θ + a / 2) < 0 := by
      rw [show (‖z‖ * Real.cos (θ - a / 2)) *
          (‖z‖ * Real.cos (θ + a / 2)) =
          (‖z‖ * ‖z‖) *
            (Real.cos (θ - a / 2) * Real.cos (θ + a / 2)) by ring]
      constructor
      · intro h
        rcases (mul_neg_iff.mp h) with h | h
        · exact h.2
        · exact (not_lt_of_ge hnormSq.le h.1).elim
      · exact mul_neg_of_pos_of_neg hnormSq
    change (p.1 * Real.cos (a / 2) + p.2 * Real.sin (a / 2)) *
        (p.1 * Real.cos (a / 2) - p.2 * Real.sin (a / 2)) < 0 ↔
      θ ∈ symmetricSeparatingAngles a
    rw [hleft, hright, hscale]
    exact cos_sub_mul_cos_add_neg_iff_mem_symmetricSeparatingAngles_Ioc
      ha0 hapi (Complex.arg_mem_Ioc z)

theorem planarStandardGaussian_planarSymmetricSeparatingDirections
    {a : ℝ} (ha0 : 0 ≤ a) (hapi : a ≤ Real.pi) :
    planarStandardGaussian (planarSymmetricSeparatingDirections a) =
      ENNReal.ofReal (a / Real.pi) := by
  rw [planarSymmetricSeparatingDirections_eq ha0 hapi,
    planarStandardGaussian_planarAngularSet_eq_normalized
      (measurableSet_symmetricSeparatingAngles a)
      (symmetricSeparatingAngles_subset ha0 hapi),
    volume_symmetricSeparatingAngles ha0 hapi]
  rw [← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos
    (show 0 < 2 * Real.pi by positivity)]
  congr 1
  field_simp

theorem piGaussian_firstTwo_preimage {A : Set (ℝ × ℝ)}
    (hA : MeasurableSet A) :
    Measure.pi (fun _ : Fin 3 ↦ gaussianReal 0 1)
        ((fun q : Fin 3 → ℝ => (q 0, q 1)) ⁻¹' A) =
      planarStandardGaussian A := by
  let μ : Fin 3 → Measure ℝ := fun _ => gaussianReal 0 1
  let split := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (2 : Fin 3)
  have hsplit : MeasurePreserving split (Measure.pi μ)
      ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin 2 => gaussianReal 0 1)) := by
    simpa [μ, split] using measurePreserving_piFinSuccAbove μ (2 : Fin 3)
  have hsnd : MeasurePreserving Prod.snd
      ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin 2 => gaussianReal 0 1))
      (Measure.pi fun _ : Fin 2 => gaussianReal 0 1) := by
    refine ⟨measurable_snd, ?_⟩
    rw [Measure.map_snd_prod]
    simp
  have hpair : MeasurePreserving MeasurableEquiv.finTwoArrow
      (Measure.pi fun _ : Fin 2 => gaussianReal 0 1) planarStandardGaussian := by
    simpa [planarStandardGaussian] using
      measurePreserving_finTwoArrow (gaussianReal 0 1)
  have hcomp := hpair.comp (hsnd.comp hsplit)
  have hfirst : (MeasurableEquiv.finTwoArrow ∘ Prod.snd ∘ split) =
      fun q : Fin 3 → ℝ => (q 0, q 1) := by
    funext q
    ext <;> rfl
  rw [← hfirst]
  exact hcomp.measure_preimage hA.nullMeasurableSet

theorem exists_symmetric_unit_pair {x y : Space}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : x ≠ y) (hneg : x ≠ -y) :
    let a := Real.arccos (inner ℝ x y)
    ∃ e0 e1 : Space, ‖e0‖ = 1 ∧ ‖e1‖ = 1 ∧ inner ℝ e0 e1 = 0 ∧
      x = Real.cos (a / 2) • e0 + Real.sin (a / 2) • e1 ∧
      y = Real.cos (a / 2) • e0 - Real.sin (a / 2) • e1 := by
  dsimp only
  let c := inner ℝ x y
  let a := Real.arccos c
  let cp := Real.cos (a / 2)
  let sp := Real.sin (a / 2)
  have hc : c ∈ Icc (-1 : ℝ) 1 := real_inner_mem_Icc_of_norm_eq_one hx hy
  have hclt : c < 1 := (inner_lt_one_iff_real_of_norm_eq_one hx hy).2 hxy
  have hcneg : -1 < c := by
    apply lt_of_le_of_ne hc.1
    intro heq
    apply hneg
    exact (inner_eq_neg_one_iff_of_norm_eq_one hx hy).mp heq.symm
  have ha0 : 0 < a := Real.arccos_pos.mpr hclt
  have hapi : a < Real.pi := Real.arccos_lt_pi.mpr hcneg
  have hcpa : 0 < cp := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> dsimp [a, cp] <;> linarith [Real.pi_pos]
  have hspa : 0 < sp := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · dsimp [a, sp]
      linarith
    · dsimp [a, sp]
      linarith [Real.pi_pos]
  have hcosa : Real.cos a = c := Real.cos_arccos hc.1 hc.2
  have hsumSq : ‖x + y‖ ^ 2 = (2 * cp) ^ 2 := by
    rw [norm_add_sq_real, hx, hy]
    have hdouble : 2 * (a / 2) = a := by ring
    rw [← hdouble, Real.cos_two_mul] at hcosa
    dsimp [c] at hcosa ⊢
    dsimp [cp]
    nlinarith
  have hsubSq : ‖x - y‖ ^ 2 = (2 * sp) ^ 2 := by
    rw [norm_sub_sq_real, hx, hy]
    have hsin := Real.sin_sq_eq_half_sub (a / 2)
    have hdouble : 2 * (a / 2) = a := by ring
    rw [hdouble, hcosa] at hsin
    dsimp [c] at hsin ⊢
    dsimp [sp]
    nlinarith
  have hsum : ‖x + y‖ = 2 * cp := by
    nlinarith [norm_nonneg (x + y)]
  have hsub : ‖x - y‖ = 2 * sp := by
    nlinarith [norm_nonneg (x - y)]
  let e0 : Space := (2 * cp)⁻¹ • (x + y)
  let e1 : Space := (2 * sp)⁻¹ • (x - y)
  have he0 : ‖e0‖ = 1 := by
    dsimp [e0]
    rw [norm_smul, hsum, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (mul_pos two_pos hcpa))]
    field_simp
  have he1 : ‖e1‖ = 1 := by
    dsimp [e1]
    rw [norm_smul, hsub, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (mul_pos two_pos hspa))]
    field_simp
  have horthRaw : inner ℝ (x + y) (x - y) = 0 := by
    rw [inner_add_left, inner_sub_right, inner_sub_right]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      real_inner_comm y x]
    rw [hx, hy]
    ring
  have horth : inner ℝ e0 e1 = 0 := by
    dsimp [e0, e1]
    rw [real_inner_smul_left, real_inner_smul_right, horthRaw]
    ring
  have hcpcoef : cp * (2 * cp)⁻¹ = (1 / 2 : ℝ) := by
    field_simp
  have hspcoef : sp * (2 * sp)⁻¹ = (1 / 2 : ℝ) := by
    field_simp
  have hxexp : x = cp • e0 + sp • e1 := by
    dsimp [e0, e1]
    rw [smul_smul, smul_smul, hcpcoef, hspcoef]
    module
  have hyexp : y = cp • e0 - sp • e1 := by
    dsimp [e0, e1]
    rw [smul_smul, smul_smul, hcpcoef, hspcoef]
    module
  exact ⟨e0, e1, he0, he1, horth, hxexp, hyexp⟩

theorem exists_orthonormalBasis_symmetric {x y : Space}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : x ≠ y) (hneg : x ≠ -y) :
    let a := Real.arccos (inner ℝ x y)
    ∃ b : OrthonormalBasis (Fin 3) ℝ Space,
      x = Real.cos (a / 2) • b 0 + Real.sin (a / 2) • b 1 ∧
      y = Real.cos (a / 2) • b 0 - Real.sin (a / 2) • b 1 := by
  dsimp only
  obtain ⟨e0, e1, he0, he1, horth, hxexp, hyexp⟩ :=
    exists_symmetric_unit_pair hx hy hxy hneg
  let v : Fin 3 → Space := ![e0, e1, 0]
  let s : Set (Fin 3) := {0, 1}
  have horthsym : inner ℝ e1 e0 = 0 := by
    rw [real_inner_comm]
    exact horth
  have hv : Orthonormal ℝ (s.restrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    fin_cases i <;> fin_cases j <;>
      simp [s, v, he0, he1, horth, horthsym] at hi hj ⊢
  have hcard : Module.finrank ℝ Space = Fintype.card (Fin 3) := by
    simp [Space]
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq hcard
  have hb0 : b 0 = e0 := hb 0 (by simp [s])
  have hb1 : b 1 = e1 := hb 1 (by simp [s])
  refine ⟨b, ?_, ?_⟩
  · rw [hb0, hb1]
    exact hxexp
  · rw [hb0, hb1]
    exact hyexp

theorem measurableSet_planarSymmetricSeparatingDirections (a : ℝ) :
    MeasurableSet (planarSymmetricSeparatingDirections a) := by
  unfold planarSymmetricSeparatingDirections
  exact measurableSet_lt
    (((measurable_fst.mul measurable_const).add
      (measurable_snd.mul measurable_const)).mul
      ((measurable_fst.mul measurable_const).sub
        (measurable_snd.mul measurable_const))) measurable_const

theorem stdGaussian_gaussianSeparatingDirections_of_ne {x y : Space}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : x ≠ y) (hneg : x ≠ -y) :
    stdGaussian Space (gaussianSeparatingDirections x y) =
      ENNReal.ofReal (Real.arccos (inner ℝ x y) / Real.pi) := by
  let a := Real.arccos (inner ℝ x y)
  obtain ⟨b, hxexp, hyexp⟩ :=
    exists_orthonormalBasis_symmetric hx hy hxy hneg
  have ha0 : 0 ≤ a := Real.arccos_nonneg _
  have hapi : a ≤ Real.pi := Real.arccos_le_pi _
  let synth : (Fin 3 → ℝ) → Space := fun q => ∑ i, q i • b i
  have hinnerx : ∀ q : Fin 3 → ℝ, inner ℝ (synth q) x =
      q 0 * Real.cos (a / 2) + q 1 * Real.sin (a / 2) := by
    intro q
    rw [hxexp, inner_add_right, inner_smul_right, inner_smul_right]
    simp_rw [synth, sum_inner, real_inner_smul_left]
    simp [orthonormal_iff_ite.mp b.orthonormal]
    ring
  have hinnery : ∀ q : Fin 3 → ℝ, inner ℝ (synth q) y =
      q 0 * Real.cos (a / 2) - q 1 * Real.sin (a / 2) := by
    intro q
    rw [hyexp, inner_sub_right, inner_smul_right, inner_smul_right]
    simp_rw [synth, sum_inner, real_inner_smul_left]
    simp [orthonormal_iff_ite.mp b.orthonormal]
    ring
  have hpre : synth ⁻¹' gaussianSeparatingDirections x y =
      (fun q : Fin 3 → ℝ => (q 0, q 1)) ⁻¹'
        planarSymmetricSeparatingDirections a := by
    ext q
    change inner ℝ (synth q) x * inner ℝ (synth q) y < 0 ↔
      (q 0, q 1) ∈ planarSymmetricSeparatingDirections a
    rw [hinnerx, hinnery]
    rfl
  rw [stdGaussian_eq_map_pi_orthonormalBasis b]
  rw [Measure.map_apply (by fun_prop)
    (measurableSet_gaussianSeparatingDirections x y)]
  rw [hpre, piGaussian_firstTwo_preimage
    (measurableSet_planarSymmetricSeparatingDirections a)]
  exact planarStandardGaussian_planarSymmetricSeparatingDirections ha0 hapi

theorem stdGaussian_inner_eq_zero {x : Space} (hx : ‖x‖ = 1) :
    stdGaussian Space {u | inner ℝ u x = 0} = 0 := by
  let L : Space →L[ℝ] ℝ := innerSL ℝ x
  have hmap : (stdGaussian Space).map L = gaussianReal 0 1 := by
    rw [IsGaussian.map_eq_gaussianReal]
    congr 2
    · exact integral_strongDual_stdGaussian _
    · rw [variance_dual_stdGaussian, innerSL_apply_norm, hx]
      simp
  have hpre : L ⁻¹' ({0} : Set ℝ) = {u : Space | inner ℝ u x = 0} := by
    ext u
    simp [L, real_inner_comm]
  rw [← hpre, ← Measure.map_apply (by fun_prop) (MeasurableSet.singleton 0), hmap]
  letI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal one_ne_zero
  exact measure_singleton 0

theorem stdGaussian_gaussianSeparatingDirections {x y : Space}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    stdGaussian Space (gaussianSeparatingDirections x y) =
      ENNReal.ofReal (Real.arccos (inner ℝ x y) / Real.pi) := by
  by_cases hxy : x = y
  · subst y
    have hset : gaussianSeparatingDirections x x = ∅ := by
      ext u
      change inner ℝ u x * inner ℝ u x < 0 ↔ False
      constructor
      · intro h
        exact (not_lt_of_ge (mul_self_nonneg _)) h
      · intro h
        contradiction
    rw [hset, measure_empty, inner_self_eq_one_of_norm_eq_one hx,
      Real.arccos_one]
    simp
  · by_cases hneg : x = -y
    · have hinner : inner ℝ x y = -1 :=
        (inner_eq_neg_one_iff_of_norm_eq_one hx hy).2 hneg
      have hset : gaussianSeparatingDirections x y =
          {u : Space | inner ℝ u y ≠ 0} := by
        ext u
        change inner ℝ u x * inner ℝ u y < 0 ↔ inner ℝ u y ≠ 0
        rw [hneg, inner_neg_right]
        constructor
        · intro h hzero
          rw [hzero] at h
          norm_num at h
        · intro hne
          nlinarith [sq_pos_of_ne_zero hne]
      rw [hset, hinner, Real.arccos_neg_one]
      have hzero : stdGaussian Space {u : Space | inner ℝ u y = 0} = 0 :=
        stdGaussian_inner_eq_zero hy
      have hmeas : MeasurableSet {u : Space | inner ℝ u y = 0} := by
        exact (MeasurableSet.singleton 0).preimage
          (continuous_id.inner continuous_const).measurable
      have hcompl : {u : Space | inner ℝ u y ≠ 0} =
          ({u : Space | inner ℝ u y = 0})ᶜ := by
        ext u
        simp
      rw [hcompl, measure_compl hmeas (by simp [hzero]), hzero]
      simp [Real.pi_ne_zero]
    · exact stdGaussian_gaussianSeparatingDirections_of_ne hx hy hxy hneg

noncomputable def dyadicTangentSample (r : ℝ → Space) (n : ℕ)
    (i : ℕ) : Space :=
  unitTangent r
    (period * (i : ℝ) / (((2 ^ (n + 1) : ℕ) : ℝ)))

noncomputable def dyadicSignChangeCount (r : ℝ → Space) (n : ℕ)
    (u : Space) : ℝ≥0∞ := by
  classical
  exact ∑ i ∈ Finset.range (2 ^ (n + 1)),
    if u ∈ gaussianSeparatingDirections (dyadicTangentSample r n i)
        (dyadicTangentSample r n (i + 1)) then 1 else 0

noncomputable def dyadicSphericalLength (r : ℝ → Space) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (2 ^ (n + 1)),
    Real.arccos (inner ℝ (dyadicTangentSample r n i)
      (dyadicTangentSample r n (i + 1)))

theorem measurable_dyadicSignChangeCount (r : ℝ → Space) (n : ℕ) :
    Measurable (dyadicSignChangeCount r n) := by
  classical
  unfold dyadicSignChangeCount
  apply Finset.measurable_sum
  intro i hi
  simp only [Finset.mem_range] at hi
  exact Measurable.ite
    (measurableSet_gaussianSeparatingDirections
      (dyadicTangentSample r n i) (dyadicTangentSample r n (i + 1)))
    measurable_const measurable_const

theorem lintegral_dyadicSignChangeCount {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (n : ℕ) :
    ∫⁻ u, dyadicSignChangeCount r n u ∂stdGaussian Space =
      ENNReal.ofReal (dyadicSphericalLength r n / Real.pi) := by
  classical
  simp only [dyadicSignChangeCount]
  have hsum := lintegral_finsetSum (Finset.range (2 ^ (n + 1)))
    (μ := stdGaussian Space)
    (f := fun i u => if u ∈ gaussianSeparatingDirections
        (dyadicTangentSample r n i) (dyadicTangentSample r n (i + 1))
      then (1 : ℝ≥0∞) else 0) (by
      intro i _hi
      exact Measurable.ite
        (measurableSet_gaussianSeparatingDirections
          (dyadicTangentSample r n i) (dyadicTangentSample r n (i + 1)))
        measurable_const measurable_const)
  rw [hsum]
  have hedge : ∀ i : ℕ,
      ∫⁻ u, (if u ∈ gaussianSeparatingDirections
          (dyadicTangentSample r n i) (dyadicTangentSample r n (i + 1))
        then (1 : ℝ≥0∞) else 0) ∂stdGaussian Space =
        ENNReal.ofReal (Real.arccos (inner ℝ (dyadicTangentSample r n i)
          (dyadicTangentSample r n (i + 1))) / Real.pi) := by
    intro i
    rw [show (fun u : Space => if u ∈ gaussianSeparatingDirections
        (dyadicTangentSample r n i) (dyadicTangentSample r n (i + 1))
      then (1 : ℝ≥0∞) else 0) =
        (gaussianSeparatingDirections (dyadicTangentSample r n i)
          (dyadicTangentSample r n (i + 1))).indicator (fun _ => 1) by
      funext u
      simp only [Set.indicator]]
    rw [lintegral_indicator
      (measurableSet_gaussianSeparatingDirections _ _), setLIntegral_one]
    exact stdGaussian_gaussianSeparatingDirections
      (norm_unitTangent hknot _) (norm_unitTangent hknot _)
  simp_rw [hedge]
  rw [dyadicSphericalLength]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · congr 1
    rw [Finset.sum_div]
  · intro i _hi
    exact div_nonneg (Real.arccos_nonneg _) Real.pi_pos.le

theorem norm_sub_eq_two_mul_sin_half_arccos_inner {x y : Space}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖x - y‖ = 2 * Real.sin (Real.arccos (inner ℝ x y) / 2) := by
  let a := Real.arccos (inner ℝ x y)
  have hc := real_inner_mem_Icc_of_norm_eq_one hx hy
  have hcosa : Real.cos a = inner ℝ x y := Real.cos_arccos hc.1 hc.2
  have ha0 : 0 ≤ a := Real.arccos_nonneg _
  have hapi : a ≤ Real.pi := Real.arccos_le_pi _
  have hsin : 0 ≤ Real.sin (a / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
      (by linarith [Real.pi_pos])
  have hsq : ‖x - y‖ ^ 2 = (2 * Real.sin (a / 2)) ^ 2 := by
    rw [norm_sub_sq_real, hx, hy]
    have hs := Real.sin_sq_eq_half_sub (a / 2)
    have hdouble : 2 * (a / 2) = a := by ring
    rw [hdouble, hcosa] at hs
    nlinarith
  dsimp [a] at hsq hsin ⊢
  nlinarith [norm_nonneg (x - y)]

theorem arccos_inner_le_pi_div_two_mul_norm_sub {x y : Space}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    Real.arccos (inner ℝ x y) ≤ Real.pi / 2 * ‖x - y‖ := by
  let a := Real.arccos (inner ℝ x y)
  have ha0 : 0 ≤ a := Real.arccos_nonneg _
  have hapi : a ≤ Real.pi := Real.arccos_le_pi _
  have hJordan := Real.mul_le_sin (x := a / 2) (by linarith)
    (by linarith [Real.pi_pos])
  have hchord := norm_sub_eq_two_mul_sin_half_arccos_inner hx hy
  field_simp [Real.pi_ne_zero] at hJordan
  dsimp [a] at hJordan hchord ⊢
  nlinarith [Real.pi_pos]

theorem arccos_inner_le_norm_sub_add_cube {x y : Space}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hsmall : ‖x - y‖ ≤ 2 / Real.pi) :
    Real.arccos (inner ℝ x y) ≤ ‖x - y‖ +
      Real.pi ^ 3 / 128 * ‖x - y‖ ^ 3 := by
  let a := Real.arccos (inner ℝ x y)
  let d := ‖x - y‖
  have ha0 : 0 ≤ a := Real.arccos_nonneg _
  have hd0 : 0 ≤ d := norm_nonneg _
  have hlinear : a ≤ Real.pi / 2 * d :=
    arccos_inner_le_pi_div_two_mul_norm_sub hx hy
  have hsmall' : ‖x - y‖ * Real.pi ≤ 2 :=
    (le_div_iff₀ Real.pi_pos).mp hsmall
  have ha_le_one : a / 2 ≤ 1 := by
    dsimp [d] at hlinear
    nlinarith [Real.pi_pos]
  have hbase : a ≤ d + a ^ 3 / 16 := by
    by_cases haZero : a = 0
    · rw [haZero]
      exact add_nonneg hd0 (by positivity)
    · have haPos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm haZero)
      have hs := Real.sin_gt_sub_cube (show 0 < a / 2 by positivity) ha_le_one
      have hchord := norm_sub_eq_two_mul_sin_half_arccos_inner hx hy
      dsimp [a, d] at hs hchord ⊢
      nlinarith
  have hcube : a ^ 3 ≤ (Real.pi / 2 * d) ^ 3 :=
    pow_le_pow_left₀ ha0 hlinear 3
  dsimp [a, d] at hbase hcube ⊢
  nlinarith

noncomputable def dyadicChordLength (r : ℝ → Space) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (2 ^ (n + 1)),
    ‖dyadicTangentSample r n (i + 1) - dyadicTangentSample r n i‖

theorem sum_uniform_intervalIntegrals (f : ℝ → ℝ)
    (hf : Continuous f) (a : ℝ) {N : ℕ} (hN : N ≠ 0) :
    (∑ i ∈ Finset.range N,
      ∫ t in a * (i : ℝ) / (N : ℝ)..a * (i + 1 : ℕ) / (N : ℝ), f t) =
      ∫ t in (0 : ℝ)..a, f t := by
  have hpartial : ∀ k : ℕ,
      (∑ i ∈ Finset.range k,
        ∫ t in a * (i : ℝ) / (N : ℝ)..a * (i + 1 : ℕ) / (N : ℝ), f t) =
        ∫ t in (0 : ℝ)..a * (k : ℝ) / (N : ℝ), f t := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        rw [intervalIntegral.integral_add_adjacent_intervals
          (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]
  rw [hpartial N]
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  rw [mul_div_cancel_right₀ a hNreal]

theorem dyadicChordLength_le_totalCurvature {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (n : ℕ) :
    dyadicChordLength r n ≤ totalCurvature r := by
  let N : ℕ := 2 ^ (n + 1)
  have hN : N ≠ 0 := pow_ne_zero _ (by norm_num)
  have hNpos : 0 < (N : ℝ) := by positivity
  have hperiod : 0 < period := by simp [period, Real.pi_pos]
  have hedge : ∀ i ∈ Finset.range N,
      ‖dyadicTangentSample r n (i + 1) - dyadicTangentSample r n i‖ ≤
        ∫ t in period * (i : ℝ) / (N : ℝ)..
          period * (i + 1 : ℕ) / (N : ℝ),
            ‖deriv (unitTangent r) t‖ := by
    intro i hi
    have hab : period * (i : ℝ) / (N : ℝ) ≤
        period * (i + 1 : ℕ) / (N : ℝ) := by
      apply div_le_div_of_nonneg_right _ hNpos.le
      gcongr
      exact Nat.le_succ i
    simp only [dyadicTangentSample]
    dsimp [N] at hab ⊢
    exact norm_sub_le_integral_of_norm_deriv_le_of_le hab
      (contDiff_unitTangent hknot).continuous.continuousOn
      ((contDiff_unitTangent hknot).differentiable (by simp)).differentiableOn
      (Filter.Eventually.of_forall fun _ _ => le_rfl)
      (show IntervalIntegrable (fun t => ‖deriv (unitTangent r) t‖) volume
          (period * (i : ℝ) / (((2 ^ (n + 1) : ℕ) : ℝ)))
          (period * (i + 1 : ℕ) / (((2 ^ (n + 1) : ℕ) : ℝ))) from
        (continuous_norm_deriv_unitTangent hknot).intervalIntegrable _ _)
  calc
    dyadicChordLength r n ≤
        ∑ i ∈ Finset.range N,
          ∫ t in period * (i : ℝ) / (N : ℝ)..
            period * (i + 1 : ℕ) / (N : ℝ),
              ‖deriv (unitTangent r) t‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact hedge i hi
    _ = ∫ t in (0 : ℝ)..period, ‖deriv (unitTangent r) t‖ := by
      exact sum_uniform_intervalIntegrals
        (fun t => ‖deriv (unitTangent r) t‖)
        (continuous_norm_deriv_unitTangent hknot) period hN
    _ = totalCurvature r :=
      (totalCurvature_eq_integral_norm_deriv_unitTangent hknot).symm

theorem exists_dyadicChord_bound {r : ℝ → Space}
    (hknot : IsSmoothKnot r) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n i, i ∈ Finset.range (2 ^ (n + 1)) →
      ‖dyadicTangentSample r n (i + 1) - dyadicTangentSample r n i‖ ≤
        M * period / (((2 ^ (n + 1) : ℕ) : ℝ)) := by
  let speedT : ℝ → ℝ := fun t => ‖deriv (unitTangent r) t‖
  have hcont : Continuous speedT := continuous_norm_deriv_unitTangent hknot
  have hperiod : 0 ≤ period := by simp [period, Real.pi_pos.le]
  obtain ⟨t0, ht0, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr hperiod) hcont.continuousOn
  refine ⟨speedT t0, norm_nonneg _, ?_⟩
  intro n i hi
  let N : ℕ := 2 ^ (n + 1)
  have hNpos : 0 < (N : ℝ) := by positivity
  have hiN : i < N := Finset.mem_range.mp hi
  have hipN : i + 1 ≤ N := hiN
  let a : ℝ := period * (i : ℝ) / (N : ℝ)
  let b : ℝ := period * (i + 1 : ℕ) / (N : ℝ)
  have ha0 : 0 ≤ a := by positivity
  have hbperiod : b ≤ period := by
    dsimp [b]
    rw [div_le_iff₀ hNpos]
    have hcast : ((i + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hipN
    nlinarith [hperiod]
  have hab : a ≤ b := by
    dsimp [a, b]
    apply div_le_div_of_nonneg_right _ hNpos.le
    gcongr
    exact Nat.le_succ i
  have hdisp : ‖unitTangent r b - unitTangent r a‖ ≤
      ∫ _t in a..b, speedT t0 := by
    apply norm_sub_le_integral_of_norm_deriv_le_of_le hab
    · exact (contDiff_unitTangent hknot).continuous.continuousOn
    · exact ((contDiff_unitTangent hknot).differentiable (by simp)).differentiableOn
    · filter_upwards [] with t ht
      exact hmax ⟨ha0.trans ht.1.le, ht.2.le.trans hbperiod⟩
    · exact continuous_const.intervalIntegrable _ _
  have hconst : (∫ _t in a..b, speedT t0) = (b - a) * speedT t0 := by
    simp [smul_eq_mul]
  rw [hconst] at hdisp
  have hwidth : b - a = period / (N : ℝ) := by
    dsimp [a, b]
    push_cast
    ring
  rw [hwidth] at hdisp
  simp only [dyadicTangentSample]
  dsimp [a, b, N] at hdisp ⊢
  convert hdisp using 1
  all_goals ring

theorem tendsto_dyadicChordBound_zero (M : ℝ) :
    Tendsto (fun n : ℕ => M * period /
      (((2 ^ (n + 1) : ℕ) : ℝ))) atTop (nhds 0) := by
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) atTop (nhds 0) :=
    (tendsto_add_atTop_iff_nat 1).2
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  have hmul := hpow.const_mul (M * period)
  convert hmul using 1
  · funext n
    simp [div_eq_mul_inv, inv_pow]
  · norm_num

theorem dyadicSphericalLength_le_of_chord_bound {r : ℝ → Space}
    (hknot : IsSmoothKnot r) {n : ℕ} {q : ℝ} (hq0 : 0 ≤ q)
    (hqsmall : q ≤ 2 / Real.pi)
    (hbound : ∀ i ∈ Finset.range (2 ^ (n + 1)),
      ‖dyadicTangentSample r n (i + 1) - dyadicTangentSample r n i‖ ≤ q) :
    dyadicSphericalLength r n ≤
      (1 + Real.pi ^ 3 / 128 * q ^ 2) * totalCurvature r := by
  let C : ℝ := Real.pi ^ 3 / 128
  have hC0 : 0 ≤ C := by positivity
  have hedge : ∀ i ∈ Finset.range (2 ^ (n + 1)),
      Real.arccos (inner ℝ (dyadicTangentSample r n i)
          (dyadicTangentSample r n (i + 1))) ≤
        ‖dyadicTangentSample r n (i + 1) - dyadicTangentSample r n i‖ +
          C * q ^ 2 *
            ‖dyadicTangentSample r n (i + 1) - dyadicTangentSample r n i‖ := by
    intro i hi
    let d := ‖dyadicTangentSample r n (i + 1) - dyadicTangentSample r n i‖
    have hd0 : 0 ≤ d := norm_nonneg _
    have hdq : d ≤ q := hbound i hi
    have hsmall' : ‖dyadicTangentSample r n i -
        dyadicTangentSample r n (i + 1)‖ ≤ 2 / Real.pi := by
      simpa [d, norm_sub_rev] using hdq.trans hqsmall
    have hangle := arccos_inner_le_norm_sub_add_cube
      (x := dyadicTangentSample r n i)
      (y := dyadicTangentSample r n (i + 1))
      (norm_unitTangent hknot _) (norm_unitTangent hknot _) hsmall'
    have hnorm : ‖dyadicTangentSample r n i -
        dyadicTangentSample r n (i + 1)‖ = d := by
      dsimp [d]
      exact norm_sub_rev _ _
    rw [hnorm] at hangle
    have hcube : d ^ 3 ≤ q ^ 2 * d := by
      have hsq : d ^ 2 ≤ q ^ 2 := (sq_le_sq₀ hd0 hq0).2 hdq
      calc
        d ^ 3 = d ^ 2 * d := by ring
        _ ≤ q ^ 2 * d := mul_le_mul_of_nonneg_right hsq hd0
    change Real.arccos (inner ℝ (dyadicTangentSample r n i)
        (dyadicTangentSample r n (i + 1))) ≤ d + C * d ^ 3 at hangle
    have herror := mul_le_mul_of_nonneg_left hcube hC0
    have hsum : d + C * d ^ 3 ≤ d + C * (q ^ 2 * d) := by
      exact add_le_add_right herror d
    have hfinal := hangle.trans hsum
    dsimp [d, C] at hfinal ⊢
    simpa only [mul_assoc] using hfinal
  calc
    dyadicSphericalLength r n ≤
        ∑ i ∈ Finset.range (2 ^ (n + 1)),
          (‖dyadicTangentSample r n (i + 1) - dyadicTangentSample r n i‖ +
            C * q ^ 2 *
              ‖dyadicTangentSample r n (i + 1) - dyadicTangentSample r n i‖) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hedge i hi
    _ = (1 + C * q ^ 2) * dyadicChordLength r n := by
      rw [Finset.sum_add_distrib]
      simp only [dyadicChordLength]
      rw [← Finset.mul_sum]
      ring
    _ ≤ (1 + C * q ^ 2) * totalCurvature r := by
      gcongr
      exact dyadicChordLength_le_totalCurvature hknot n
    _ = (1 + Real.pi ^ 3 / 128 * q ^ 2) * totalCurvature r := rfl

theorem sum_range_double (f : ℕ → ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range (2 * N), f j) =
      ∑ i ∈ Finset.range N, (f (2 * i) + f (2 * i + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      rw [← ih]
      rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega]
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      ring

theorem dyadicTangentSample_refine_even (r : ℝ → Space)
    (n i : ℕ) :
    dyadicTangentSample r (n + 1) (2 * i) =
      dyadicTangentSample r n i := by
  unfold dyadicTangentSample
  congr 1
  push_cast
  rw [pow_succ]
  field_simp

theorem dyadicTangentSample_refine_next (r : ℝ → Space)
    (n i : ℕ) :
    dyadicTangentSample r (n + 1) (2 * i + 2) =
      dyadicTangentSample r n (i + 1) := by
  rw [show 2 * i + 2 = 2 * (i + 1) by omega]
  exact dyadicTangentSample_refine_even r n (i + 1)

theorem arccos_inner_triangle {x y z : Space}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1) :
    Real.arccos (inner ℝ x z) ≤
      Real.arccos (inner ℝ x y) + Real.arccos (inner ℝ y z) := by
  simpa [InnerProductGeometry.angle, hx, hy, hz] using
    (InnerProductGeometry.angle_le_angle_add_angle x y z)

theorem dyadicSphericalLength_mono {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (n : ℕ) :
    dyadicSphericalLength r n ≤ dyadicSphericalLength r (n + 1) := by
  let N : ℕ := 2 ^ (n + 1)
  let f : ℕ → ℝ := fun j =>
    Real.arccos (inner ℝ (dyadicTangentSample r (n + 1) j)
      (dyadicTangentSample r (n + 1) (j + 1)))
  have hedge : ∀ i ∈ Finset.range N,
      Real.arccos (inner ℝ (dyadicTangentSample r n i)
          (dyadicTangentSample r n (i + 1))) ≤
        f (2 * i) + f (2 * i + 1) := by
    intro i _hi
    have htri := arccos_inner_triangle
      (x := dyadicTangentSample r (n + 1) (2 * i))
      (y := dyadicTangentSample r (n + 1) (2 * i + 1))
      (z := dyadicTangentSample r (n + 1) (2 * i + 2))
      (norm_unitTangent hknot _) (norm_unitTangent hknot _)
      (norm_unitTangent hknot _)
    dsimp [f]
    calc
      Real.arccos (inner ℝ (dyadicTangentSample r n i)
          (dyadicTangentSample r n (i + 1))) =
          Real.arccos (inner ℝ (dyadicTangentSample r (n + 1) (2 * i))
            (dyadicTangentSample r (n + 1) (2 * i + 2))) := by
        rw [dyadicTangentSample_refine_even,
          dyadicTangentSample_refine_next]
      _ ≤ _ := htri
  calc
    dyadicSphericalLength r n ≤
        ∑ i ∈ Finset.range N, (f (2 * i) + f (2 * i + 1)) := by
      unfold dyadicSphericalLength
      apply Finset.sum_le_sum
      intro i hi
      exact hedge i hi
    _ = ∑ j ∈ Finset.range (2 * N), f j := by
      exact (sum_range_double f N).symm
    _ = dyadicSphericalLength r (n + 1) := by
      unfold dyadicSphericalLength
      dsimp [N, f]
      congr 1
      rw [show 2 * 2 ^ (n + 1) = 2 ^ (n + 1 + 1) by ring]

theorem monotone_dyadicSphericalLength {r : ℝ → Space}
    (hknot : IsSmoothKnot r) : Monotone (dyadicSphericalLength r) := by
  exact monotone_nat_of_le_succ (dyadicSphericalLength_mono hknot)

theorem dyadicSphericalLength_le_totalCurvature {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (n : ℕ) :
    dyadicSphericalLength r n ≤ totalCurvature r := by
  obtain ⟨M, hM0, hbound⟩ := exists_dyadicChord_bound hknot
  let q : ℕ → ℝ := fun k => M * period /
    (((2 ^ (k + 1) : ℕ) : ℝ))
  let C : ℝ := Real.pi ^ 3 / 128
  have hq : Tendsto q atTop (nhds 0) := by
    exact tendsto_dyadicChordBound_zero M
  have hqsmall : ∀ᶠ k in atTop, q k < 2 / Real.pi :=
    (tendsto_order.1 hq).2 _ (by positivity)
  have herr : Tendsto (fun k => C * q k ^ 2 * totalCurvature r)
      atTop (nhds 0) := by
    simpa [mul_assoc] using
      ((hq.pow 2).const_mul C).mul_const (totalCurvature r)
  apply le_of_forall_pos_le_add
  intro ε hε
  have herrsmall : ∀ᶠ k in atTop,
      C * q k ^ 2 * totalCurvature r < ε :=
    (tendsto_order.1 herr).2 _ hε
  obtain ⟨k, hkq, hkerr, hnk⟩ :=
    (hqsmall.and (herrsmall.and (eventually_ge_atTop n))).exists
  have hq0 : 0 ≤ q k := by
    dsimp [q]
    exact div_nonneg (mul_nonneg hM0 (by simp [period, Real.pi_pos.le]))
      (Nat.cast_nonneg _)
  have hboundk : ∀ i ∈ Finset.range (2 ^ (k + 1)),
      ‖dyadicTangentSample r k (i + 1) - dyadicTangentSample r k i‖ ≤ q k := by
    intro i hi
    exact hbound k i hi
  calc
    dyadicSphericalLength r n ≤ dyadicSphericalLength r k :=
      monotone_dyadicSphericalLength hknot hnk
    _ ≤ (1 + C * q k ^ 2) * totalCurvature r := by
      exact dyadicSphericalLength_le_of_chord_bound hknot hq0 hkq.le hboundk
    _ ≤ totalCurvature r + ε := by
      dsimp [C] at hkerr ⊢
      nlinarith

theorem stdGaussian_singleton_zero {r : ℝ → Space}
    (hknot : IsSmoothKnot r) :
    stdGaussian Space ({0} : Set Space) = 0 := by
  apply measure_mono_null (t := {u : Space | inner ℝ u (unitTangent r 0) = 0})
  · rintro u rfl
    simp
  · exact stdGaussian_inner_eq_zero (norm_unitTangent hknot 0)

theorem exists_nonzero_dyadicSignChangeCount_lt_four
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (n : ℕ)
    (hlt : dyadicSphericalLength r n < 4 * Real.pi) :
    ∃ u : Space, u ≠ 0 ∧ dyadicSignChangeCount r n u < 4 := by
  by_contra hnone
  have hzero := stdGaussian_singleton_zero hknot
  have hae_ne : ∀ᵐ u ∂stdGaussian Space, u ≠ 0 := by
    rw [ae_iff]
    simpa using hzero
  have hae_lower : ∀ᵐ u ∂stdGaussian Space,
      (4 : ℝ≥0∞) ≤ dyadicSignChangeCount r n u := by
    filter_upwards [hae_ne] with u hu
    exact le_of_not_gt fun hltu => hnone ⟨u, hu, hltu⟩
  have hlower : (4 : ℝ≥0∞) ≤
      ∫⁻ u, dyadicSignChangeCount r n u ∂stdGaussian Space := by
    calc
      (4 : ℝ≥0∞) = ∫⁻ _u : Space, (4 : ℝ≥0∞) ∂stdGaussian Space := by simp
      _ ≤ _ := lintegral_mono_ae hae_lower
  have hreal : dyadicSphericalLength r n / Real.pi < 4 := by
    rw [div_lt_iff₀ Real.pi_pos]
    linarith
  have hupper : (∫⁻ u, dyadicSignChangeCount r n u ∂stdGaussian Space) <
      (4 : ℝ≥0∞) := by
    rw [lintegral_dyadicSignChangeCount hknot n]
    simpa using
      (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 4)).2 hreal
  exact (not_lt_of_ge hlower) hupper

theorem mem_gaussianSeparatingDirections_smul_iff
    {u x y : Space} {c : ℝ} (hc : c ≠ 0) :
    c • u ∈ gaussianSeparatingDirections x y ↔
      u ∈ gaussianSeparatingDirections x y := by
  simp only [gaussianSeparatingDirections, Set.mem_setOf_eq,
    real_inner_smul_left]
  change (c * inner ℝ u x) * (c * inner ℝ u y) < 0 ↔
    inner ℝ u x * inner ℝ u y < 0
  have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  constructor <;> intro h <;> nlinarith

theorem dyadicSignChangeCount_normalizedDirection
    (r : ℝ → Space) (n : ℕ) {u : Space} (hu : u ≠ 0) :
    dyadicSignChangeCount r n (normalizedDirection u) =
      dyadicSignChangeCount r n u := by
  classical
  unfold dyadicSignChangeCount
  apply Finset.sum_congr rfl
  intro i _hi
  apply if_congr
  · unfold normalizedDirection
    exact mem_gaussianSeparatingDirections_smul_iff
      (inv_ne_zero (norm_ne_zero_iff.mpr hu))
  · rfl
  · rfl

theorem exists_unit_dyadicSignChangeCount_lt_four
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (n : ℕ)
    (hlt : dyadicSphericalLength r n < 4 * Real.pi) :
    ∃ u : Space, ‖u‖ = 1 ∧ dyadicSignChangeCount r n u < 4 := by
  obtain ⟨u, hu, hcount⟩ :=
    exists_nonzero_dyadicSignChangeCount_lt_four hknot n hlt
  refine ⟨normalizedDirection u, norm_normalizedDirection hu, ?_⟩
  rw [dyadicSignChangeCount_normalizedDirection r n hu]
  exact hcount

def IsDyadicRegular (r : ℝ → Space) (n : ℕ) (u : Space) : Prop :=
  ∀ i ∈ Finset.range (2 ^ (n + 1)),
    inner ℝ u (dyadicTangentSample r n i) ≠ 0

theorem ae_isDyadicRegular {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (n : ℕ) :
    ∀ᵐ u ∂stdGaussian Space, IsDyadicRegular r n u := by
  classical
  unfold IsDyadicRegular
  rw [Finset.eventually_all]
  intro i _hi
  rw [ae_iff]
  simpa using stdGaussian_inner_eq_zero
    (x := dyadicTangentSample r n i) (norm_unitTangent hknot _)

theorem exists_nonzero_regular_dyadicSignChangeCount_lt_four
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (n : ℕ)
    (hlt : dyadicSphericalLength r n < 4 * Real.pi) :
    ∃ u : Space, u ≠ 0 ∧ IsDyadicRegular r n u ∧
      dyadicSignChangeCount r n u < 4 := by
  by_contra hnone
  have hae_ne : ∀ᵐ u ∂stdGaussian Space, u ≠ 0 := by
    rw [ae_iff]
    simpa using stdGaussian_singleton_zero hknot
  have hae_lower : ∀ᵐ u ∂stdGaussian Space,
      (4 : ℝ≥0∞) ≤ dyadicSignChangeCount r n u := by
    filter_upwards [hae_ne, ae_isDyadicRegular hknot n] with u hu hreg
    exact le_of_not_gt fun hltu => hnone ⟨u, hu, hreg, hltu⟩
  have hlower : (4 : ℝ≥0∞) ≤
      ∫⁻ u, dyadicSignChangeCount r n u ∂stdGaussian Space := by
    calc
      (4 : ℝ≥0∞) = ∫⁻ _u : Space, (4 : ℝ≥0∞) ∂stdGaussian Space := by simp
      _ ≤ _ := lintegral_mono_ae hae_lower
  have hreal : dyadicSphericalLength r n / Real.pi < 4 := by
    rw [div_lt_iff₀ Real.pi_pos]
    linarith
  have hupper : (∫⁻ u, dyadicSignChangeCount r n u ∂stdGaussian Space) <
      (4 : ℝ≥0∞) := by
    rw [lintegral_dyadicSignChangeCount hknot n]
    simpa using
      (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 4)).2 hreal
  exact (not_lt_of_ge hlower) hupper

theorem isDyadicRegular_normalizedDirection
    (r : ℝ → Space) (n : ℕ) {u : Space} (hu : u ≠ 0)
    (hreg : IsDyadicRegular r n u) :
    IsDyadicRegular r n (normalizedDirection u) := by
  intro i hi
  unfold normalizedDirection
  rw [real_inner_smul_left]
  exact mul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hu)) (hreg i hi)

theorem exists_unit_regular_dyadicSignChangeCount_lt_four
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (n : ℕ)
    (hlt : dyadicSphericalLength r n < 4 * Real.pi) :
    ∃ u : Space, ‖u‖ = 1 ∧ IsDyadicRegular r n u ∧
      dyadicSignChangeCount r n u < 4 := by
  obtain ⟨u, hu, hreg, hcount⟩ :=
    exists_nonzero_regular_dyadicSignChangeCount_lt_four hknot n hlt
  refine ⟨normalizedDirection u, norm_normalizedDirection hu,
    isDyadicRegular_normalizedDirection r n hu hreg, ?_⟩
  rw [dyadicSignChangeCount_normalizedDirection r n hu]
  exact hcount

end Submission.Helpers
