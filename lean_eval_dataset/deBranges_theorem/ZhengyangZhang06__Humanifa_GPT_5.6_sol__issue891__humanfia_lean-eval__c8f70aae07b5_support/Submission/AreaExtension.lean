import Submission.GrunskyArea

open Metric Set

namespace Submission

noncomputable def exteriorAnalyticFactor (L : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.exp (-L z)

noncomputable def exteriorAnalyticSlope (L : ℂ → ℂ) : ℂ → ℂ :=
  dslope (exteriorAnalyticFactor L) 0

noncomputable def exteriorHarmonicFill (L : ℂ → ℂ) (A : ℝ) (z : ℂ) : ℂ :=
  z + exteriorAnalyticSlope L (starRingEnd ℂ z / (A : ℂ) ^ 2)

noncomputable def interiorReflection (A : ℝ) (z : ℂ) : ℂ :=
  starRingEnd ℂ z / (A : ℂ) ^ 2

noncomputable def interiorReflectionLipschitzConstant (A : ℝ) : NNReal :=
  ⟨1 / A ^ 2, by positivity⟩

def outsideRadius (A : ℝ) : Set ℂ :=
  {z | A < ‖z‖}

lemma isOpen_outsideRadius (A : ℝ) : IsOpen (outsideRadius A) :=
  isOpen_lt continuous_const continuous_norm

lemma compl_outsideRadius (A : ℝ) : (outsideRadius A)ᶜ = closedBall (0 : ℂ) A := by
  ext z
  simp [outsideRadius]

lemma isConnected_outsideRadius {A : ℝ} (hA : 0 ≤ A) :
    IsConnected (outsideRadius A) := by
  let radialMap : ℝ × ℂ → ℂ := fun p => (p.1 : ℂ) * p.2
  have hI : IsPathConnected (Set.Ioi A) :=
    (convex_Ioi A).isPathConnected ⟨A + 1, by simp⟩
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  have hsphere : IsPathConnected (sphere (0 : ℂ) 1) :=
    isPathConnected_sphere hrank 0 zero_le_one
  have himage : IsConnected
      (radialMap '' (Set.Ioi A ×ˢ sphere (0 : ℂ) 1)) := by
    exact (hI.isConnected.prod hsphere.isConnected).image radialMap (by fun_prop)
  have heq : radialMap '' (Set.Ioi A ×ˢ sphere (0 : ℂ) 1) = outsideRadius A := by
    ext z
    constructor
    · rintro ⟨⟨r, u⟩, ⟨hr, hu⟩, rfl⟩
      rw [outsideRadius, mem_setOf_eq, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (hA.trans_lt hr).le]
      have hunorm : ‖u‖ = 1 := by
        simpa [mem_sphere, dist_zero_right] using hu
      rw [hunorm, mul_one]
      exact hr
    · intro hz
      have hnorm : A < ‖z‖ := hz
      have hnorm0 : 0 < ‖z‖ := hA.trans_lt hnorm
      let u : ℂ := (‖z‖⁻¹ : ℝ) • z
      have hu : u ∈ sphere (0 : ℂ) 1 := by
        rw [mem_sphere, dist_zero_right]
        simp [u, hnorm0.ne']
      refine ⟨(‖z‖, u), ⟨hnorm, hu⟩, ?_⟩
      dsimp only [radialMap, u]
      rw [Complex.real_smul]
      rw [← mul_assoc, ← Complex.ofReal_mul]
      simp [hnorm0.ne']
  rwa [heq] at himage

lemma exteriorAnalyticFactor_differentiableOn {L : ℂ → ℂ} {R : ℝ}
    (hL : DifferentiableOn ℂ L (ball 0 R)) :
    DifferentiableOn ℂ (exteriorAnalyticFactor L) (ball 0 R) := by
  intro z hz
  exact (hL z hz).neg.cexp

@[simp]
lemma exteriorAnalyticFactor_zero {L : ℂ → ℂ} (hL0 : L 0 = 0) :
    exteriorAnalyticFactor L 0 = 1 := by
  simp [exteriorAnalyticFactor, hL0]

lemma exteriorAnalyticSlope_differentiableOn {L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) :
    DifferentiableOn ℂ (exteriorAnalyticSlope L) (ball 0 R) := by
  have hzero : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  exact (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds hzero)).2
    (exteriorAnalyticFactor_differentiableOn hL)

lemma conj_div_real_sq_eq_inv {A : ℝ} {z : ℂ} (hz : ‖z‖ = A) :
    starRingEnd ℂ z / (A : ℂ) ^ 2 = z⁻¹ := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hz]
  push_cast
  rw [div_eq_mul_inv]

lemma interiorReflection_lipschitzWith (A : ℝ) :
    LipschitzWith (interiorReflectionLipschitzConstant A) (interiorReflection A) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  change ‖starRingEnd ℂ x / (A : ℂ) ^ 2 - starRingEnd ℂ y / (A : ℂ) ^ 2‖ ≤
    (1 / A ^ 2) * ‖x - y‖
  rw [← sub_div, ← map_sub, norm_div, norm_pow, Complex.norm_real, Complex.norm_conj]
  have hsq : ‖A‖ ^ 2 = A ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
  rw [hsq]
  rw [div_eq_mul_inv, one_div]
  ring_nf
  exact le_rfl

lemma interiorReflection_mapsTo_closedBall {A ρ : ℝ} (hA : 0 < A)
    (hAρ : 1 / A ≤ ρ) :
    MapsTo (interiorReflection A) (closedBall (0 : ℂ) A) (closedBall 0 ρ) := by
  intro z hz
  rw [mem_closedBall_zero_iff] at hz ⊢
  rw [interiorReflection, norm_div, norm_pow, Complex.norm_real, Complex.norm_conj]
  have hnormA : ‖A‖ = A := Real.norm_of_nonneg hA.le
  rw [hnormA]
  calc
    ‖z‖ / A ^ 2 ≤ A / A ^ 2 := div_le_div_of_nonneg_right hz (sq_nonneg A)
    _ = 1 / A := by field_simp [hA.ne']
    _ ≤ ρ := hAρ

lemma exteriorHarmonicPerturbation_lipschitzOnWith {L : ℂ → ℂ} {A ρ : ℝ}
    {M : NNReal} (hA : 0 < A) (hAρ : 1 / A ≤ ρ)
    (hP : LipschitzOnWith M (exteriorAnalyticSlope L) (closedBall (0 : ℂ) ρ)) :
    LipschitzOnWith (M * interiorReflectionLipschitzConstant A)
      (fun z => exteriorHarmonicFill L A z - z) (closedBall (0 : ℂ) A) := by
  have hreflect : LipschitzOnWith (interiorReflectionLipschitzConstant A)
      (interiorReflection A) (closedBall (0 : ℂ) A) :=
    (interiorReflection_lipschitzWith A).lipschitzOnWith
  have hcomp := hP.comp hreflect (interiorReflection_mapsTo_closedBall hA hAρ)
  have heq : (fun z => exteriorHarmonicFill L A z - z) =
      exteriorAnalyticSlope L ∘ interiorReflection A := by
    funext z
    simp [exteriorHarmonicFill, interiorReflection, Function.comp_apply]
  rw [heq]
  exact hcomp

lemma exists_exteriorAnalyticSlope_lipschitzOn {L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < R ∧
      ∃ M : NNReal, LipschitzOnWith M (exteriorAnalyticSlope L) (closedBall (0 : ℂ) ρ) := by
  let ρ : ℝ := R / 2
  have hρ : 0 < ρ := by dsimp only [ρ]; linarith
  have hρR : ρ < R := by dsimp only [ρ]; linarith
  have hclosed : closedBall (0 : ℂ) ρ ⊆ ball 0 R := by
    intro z hz
    rw [mem_closedBall_zero_iff] at hz
    rw [mem_ball_zero_iff]
    exact hz.trans_lt hρR
  have hP := exteriorAnalyticSlope_differentiableOn hR hL
  have hderiv : DifferentiableOn ℂ (deriv (exteriorAnalyticSlope L)) (ball 0 R) :=
    hP.deriv isOpen_ball
  have hcont : ContinuousOn (fun z => ‖deriv (exteriorAnalyticSlope L) z‖)
      (closedBall (0 : ℂ) ρ) :=
    hderiv.continuousOn.norm.mono hclosed
  rcases (isCompact_closedBall (0 : ℂ) ρ).bddAbove_image hcont with ⟨C, hC⟩
  let M : NNReal := ⟨max C 0, le_max_right C 0⟩
  refine ⟨ρ, hρ, hρR, M, ?_⟩
  apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
  · intro z hz
    exact hP.differentiableAt (isOpen_ball.mem_nhds (hclosed hz))
  · intro z hz
    apply NNReal.coe_le_coe.mp
    change ‖deriv (exteriorAnalyticSlope L) z‖ ≤ max C 0
    exact (hC ⟨z, hz, rfl⟩).trans (le_max_left C 0)
  · exact convex_closedBall 0 ρ

lemma exists_contracting_extension_exteriorHarmonicPerturbation
    {L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) :
    ∃ A : ℝ, 0 < A ∧ 1 / R < A ∧
      ∃ K : NNReal, K < 1 ∧ ∃ u : ℂ → ℂ, LipschitzWith K u ∧
        EqOn (fun z => exteriorHarmonicFill L A z - z) u (closedBall (0 : ℂ) A) := by
  rcases exists_exteriorAnalyticSlope_lipschitzOn hR hL with
    ⟨ρ, hρ, hρR, M, hM⟩
  let C : NNReal := lipschitzExtensionConstant ℂ
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt
    (max (1 / ρ) (((C * M : NNReal) : ℝ) + 1))
  let A : ℝ := N
  have hAρ' : 1 / ρ < A := (le_max_left _ _).trans_lt hN
  have hCM : ((C * M : NNReal) : ℝ) + 1 < A :=
    (le_max_right _ _).trans_lt hN
  have hA : 0 < A := by
    have : 0 < 1 / ρ := one_div_pos.mpr hρ
    linarith
  have hAρ : 1 / A ≤ ρ := by
    exact (one_div_le hA hρ).2 (le_of_lt hAρ')
  have hRA : 1 / R < A := by
    have hrecip : 1 / R < 1 / ρ := one_div_lt_one_div_of_lt hρ hρR
    exact hrecip.trans hAρ'
  let K₀ : NNReal := M * interiorReflectionLipschitzConstant A
  let K : NNReal := C * K₀
  have hAone : 1 < A := by
    have hCnonneg : 0 ≤ ((C * M : NNReal) : ℝ) := NNReal.coe_nonneg (C * M)
    linarith
  have hAsq : ((C * M : NNReal) : ℝ) < A ^ 2 := by
    nlinarith
  have hK : K < 1 := by
    have hreflect : ((interiorReflectionLipschitzConstant A : NNReal) : ℝ) =
        1 / A ^ 2 := rfl
    apply NNReal.coe_lt_coe.mp
    change (C : ℝ) * ((K₀ : NNReal) : ℝ) < 1
    rw [show ((K₀ : NNReal) : ℝ) = (M : ℝ) * (1 / A ^ 2) by
      simp only [K₀, NNReal.coe_mul, hreflect]]
    rw [← mul_assoc, ← NNReal.coe_mul]
    simpa [div_eq_mul_inv] using (div_lt_one (sq_pos_of_pos hA)).2 hAsq
  have hperturb : LipschitzOnWith K₀
      (fun z => exteriorHarmonicFill L A z - z) (closedBall (0 : ℂ) A) := by
    exact exteriorHarmonicPerturbation_lipschitzOnWith hA hAρ hM
  rcases hperturb.extend_finite_dimension with ⟨u, hu, heq⟩
  refine ⟨A, hA, hRA, K, hK, u, ?_, heq⟩
  simpa only [K, K₀, C] using hu

lemma exists_exteriorHarmonicFill_homeomorph {L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) :
    ∃ A : ℝ, 0 < A ∧ 1 / R < A ∧ ∃ e : ℂ ≃ₜ ℂ,
      EqOn (exteriorHarmonicFill L A) e (closedBall (0 : ℂ) A) := by
  rcases exists_contracting_extension_exteriorHarmonicPerturbation hR hL with
    ⟨A, hA, hRA, K, hK, u, hu, heq⟩
  let G : ℂ → ℂ := fun z => z + u z
  let idEquiv : ℂ ≃L[ℝ] ℂ := ContinuousLinearEquiv.refl ℝ ℂ
  have happrox : ApproximatesLinearOn G (idEquiv : ℂ →L[ℝ] ℂ) univ K := by
    intro x hx y hy
    change ‖(x + u x) - (y + u y) - (x - y)‖ ≤ K * ‖x - y‖
    calc
      ‖(x + u x) - (y + u y) - (x - y)‖ = ‖u x - u y‖ := by
        congr 1
        ring
      _ ≤ K * ‖x - y‖ := hu.norm_sub_le x y
  have hidnorm : ‖(idEquiv.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ = 1 := by
    simp [idEquiv]
  have hsmall : Subsingleton ℂ ∨ K < ‖(idEquiv.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ := by
    right
    simpa only [hidnorm] using hK
  let e : ℂ ≃ₜ ℂ := happrox.toHomeomorph G hsmall
  refine ⟨A, hA, hRA, e, ?_⟩
  intro z hz
  change exteriorHarmonicFill L A z = G z
  dsimp only [G]
  rw [← heq hz]
  ring

lemma exteriorHarmonicFill_eq_exteriorTransform_on_sphere
    {f L : ℂ → ℂ} {R A : ℝ} (hR : 0 < R) (hA : 0 < A)
    (hRA : 1 / R < A) (hf : NormalizedUnivalentOn f R) (hL0 : L 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z) :
    Set.EqOn (exteriorHarmonicFill L A) (exteriorTransform f) (sphere 0 A) := by
  intro z hz
  have hnorm : ‖z‖ = A := by
    simpa [mem_sphere, dist_zero_right] using hz
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    simp at hnorm
    linarith
  have hzext : z ∈ exteriorDisk R := by
    change 1 / R < ‖z‖
    simpa [hnorm] using hRA
  have hinv : starRingEnd ℂ z / (A : ℂ) ^ 2 = z⁻¹ :=
    conj_div_real_sq_eq_inv hnorm
  rw [exteriorHarmonicFill, exteriorAnalyticSlope, hinv,
    dslope_of_ne _ (inv_ne_zero hz0), slope_def_field,
    exteriorTransform_eq_mul_exp_neg hR hf hexp hzext,
    exteriorAnalyticFactor_zero hL0]
  unfold exteriorAnalyticFactor
  field_simp [hz0]
  ring

end Submission
