import Mathlib

open scoped Polynomial

namespace Submission.Helpers

noncomputable section

open ContinuousMap

/-- Restrict a continuous-on function to its set, as a bundled continuous map. -/
def restrictTo {K : Set ℂ} (f : ℂ → ℂ) (hf : ContinuousOn f K) : C(K, ℂ) :=
  ⟨fun z ↦ f z, hf.restrict⟩

@[simp]
theorem restrictTo_apply {K : Set ℂ} (f : ℂ → ℂ) (hf : ContinuousOn f K) (z : K) :
    restrictTo f hf z = f z :=
  rfl

/-- Membership in the closure of polynomial functions, written as uniform approximation. -/
theorem mem_polynomialFunctions_topologicalClosure_iff {K : Set ℂ} [CompactSpace K]
    (f : ℂ → ℂ) (hfc : ContinuousOn f K) :
    restrictTo f hfc ∈ (polynomialFunctions K).topologicalClosure ↔
      ∀ ε : ℝ, 0 < ε → ∃ p : ℂ[X], ∀ z ∈ K, ‖f z - p.eval z‖ < ε := by
  rw [← SetLike.mem_coe, Subalgebra.topologicalClosure_coe, Metric.mem_closure_iff]
  constructor
  · intro h ε hε
    obtain ⟨g, hg, hfg⟩ := h ε hε
    rw [polynomialFunctions_coe] at hg
    obtain ⟨p, rfl⟩ := hg
    refine ⟨p, fun z hz ↦ ?_⟩
    have hpoint :
        ‖(restrictTo f hfc - p.toContinuousMapOn K) ⟨z, hz⟩‖ < ε :=
      lt_of_le_of_lt
        ((restrictTo f hfc - p.toContinuousMapOn K).norm_coe_le_norm ⟨z, hz⟩)
        (by simpa [dist_eq_norm] using hfg)
    simpa using hpoint
  · intro h ε hε
    obtain ⟨p, hp⟩ := h ε hε
    refine ⟨p.toContinuousMapOn K, ?_, ?_⟩
    · rw [polynomialFunctions_coe]
      exact ⟨p, rfl⟩
    · rw [dist_eq_norm, (restrictTo f hfc - p.toContinuousMapOn K).norm_lt_iff hε]
      intro z
      simpa using hp z z.property

/-- A resolvent whose pole lies off `K` belongs to the closed polynomial algebra on `K`. -/
theorem exists_resolvent_mem_polynomialClosure {K : Set ℂ} [CompactSpace K]
    (hKc : IsConnected (Kᶜ)) {a : ℂ} (ha : a ∉ K) :
    ∃ g : (polynomialFunctions K).topologicalClosure,
      ∀ z : K, (g : C(K, ℂ)) z = (a - z)⁻¹ := by
  let A : Subalgebra ℂ C(K, ℂ) := (polynomialFunctions K).topologicalClosure
  letI : IsClosed (A : Set C(K, ℂ)) := by
    dsimp [A]
    exact Subalgebra.isClosed_topologicalClosure _
  let coord : C(K, ℂ) := Polynomial.X.toContinuousMapOn K
  have hcoord : coord ∈ A := by
    apply Subalgebra.le_topologicalClosure
    have hm : coord ∈ (polynomialFunctions K : Set C(K, ℂ)) := by
      rw [polynomialFunctions_coe]
      exact ⟨Polynomial.X, rfl⟩
    exact hm
  let x : A := ⟨coord, hcoord⟩
  have hrange : Set.range coord = K := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      rw [show coord w = (w : ℂ) by simp [coord]]
      exact w.property
    · intro hz
      exact ⟨⟨z, hz⟩, by simp [coord]⟩
  have hspectrum_ambient : spectrum ℂ (x : C(K, ℂ)) = K := by
    change spectrum ℂ coord = K
    rw [ContinuousMap.spectrum_eq_range, hrange]
  have hspectrum_sub : spectrum ℂ x = K :=
    (Subalgebra.spectrum_eq_of_isPreconnected_compl A x
      (by simpa [hspectrum_ambient] using hKc.isPreconnected)).trans hspectrum_ambient
  have ha_spec : a ∉ spectrum ℂ x := by
    simpa [hspectrum_sub] using ha
  have hu : IsUnit (algebraMap ℂ A a - x) := spectrum.notMem_iff.mp ha_spec
  refine ⟨(↑hu.unit⁻¹ : A), fun z ↦ ?_⟩
  let ev : A →ₐ[ℂ] ℂ :=
    (ContinuousMap.evalAlgHom ℂ ℂ z).comp (Subalgebra.val A)
  have hz : ev (algebraMap ℂ A a - x) * ev (↑hu.unit⁻¹ : A) = 1 := by
    rw [← map_mul, hu.mul_val_inv, map_one]
  have hev : ev (algebraMap ℂ A a - x) = a - (z : ℂ) := by
    simp [ev, A, x, coord]
  rw [hev] at hz
  have hne : a - (z : ℂ) ≠ 0 := sub_ne_zero.mpr fun haz ↦ by
    apply ha
    rw [haz]
    exact z.property
  change ev (↑hu.unit⁻¹ : A) = (a - (z : ℂ))⁻¹
  exact ((mul_eq_one_iff_inv_eq₀ hne).mp hz).symm

/-- A rational function with no pole on `K` belongs to the closed polynomial algebra on `K`. -/
theorem exists_rational_mem_polynomialClosure {K : Set ℂ} [CompactSpace K]
    (hKc : IsConnected (Kᶜ)) (p q : ℂ[X]) (hq : ∀ z ∈ K, q.eval z ≠ 0) :
    ∃ g : (polynomialFunctions K).topologicalClosure,
      ∀ z : K, (g : C(K, ℂ)) z = p.eval (z : ℂ) / q.eval (z : ℂ) := by
  classical
  by_cases hKempty : K = ∅
  · subst K
    refine ⟨0, fun z ↦ ?_⟩
    exact z.property.elim
  have hKne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hKempty
  letI : Nonempty K := Set.nonempty_coe_sort.mpr hKne
  haveI : Nontrivial C(K, ℂ) := inferInstance
  let A : Subalgebra ℂ C(K, ℂ) := (polynomialFunctions K).topologicalClosure
  letI : IsClosed (A : Set C(K, ℂ)) := by
    dsimp [A]
    exact Subalgebra.isClosed_topologicalClosure _
  letI : CompleteSpace A := (show IsClosed (A : Set C(K, ℂ)) from inferInstance).completeSpace_coe
  let z₀ : K := ⟨hKne.choose, hKne.choose_spec⟩
  have hzero_ne_one : (0 : A) ≠ 1 := by
    intro h
    have hz := congrArg (fun y : A ↦ (y : C(K, ℂ)) z₀) h
    simp at hz
  letI : Nontrivial A := ⟨⟨0, 1, hzero_ne_one⟩⟩
  let coord : C(K, ℂ) := Polynomial.X.toContinuousMapOn K
  have hcoord : coord ∈ A := by
    apply Subalgebra.le_topologicalClosure
    have hm : coord ∈ (polynomialFunctions K : Set C(K, ℂ)) := by
      rw [polynomialFunctions_coe]
      exact ⟨Polynomial.X, rfl⟩
    exact hm
  let x : A := ⟨coord, hcoord⟩
  have hrange : Set.range coord = K := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      rw [show coord w = (w : ℂ) by simp [coord]]
      exact w.property
    · intro hz
      exact ⟨⟨z, hz⟩, by simp [coord]⟩
  have hspectrum_ambient : spectrum ℂ (x : C(K, ℂ)) = K := by
    change spectrum ℂ coord = K
    rw [ContinuousMap.spectrum_eq_range, hrange]
  have hspectrum_x : spectrum ℂ x = K :=
    (Subalgebra.spectrum_eq_of_isPreconnected_compl A x
      (by simpa [hspectrum_ambient] using hKc.isPreconnected)).trans hspectrum_ambient
  have hzero : 0 ∉ spectrum ℂ (Polynomial.aeval x q) := by
    rw [spectrum.map_polynomial_aeval, hspectrum_x]
    rintro ⟨z, hz, hqz⟩
    exact hq z hz hqz
  have hu : IsUnit (Polynomial.aeval x q) := (spectrum.zero_notMem_iff ℂ).mp hzero
  refine ⟨Polynomial.aeval x p * (↑hu.unit⁻¹ : A), fun z ↦ ?_⟩
  let ev : A →ₐ[ℂ] ℂ :=
    (ContinuousMap.evalAlgHom ℂ ℂ z).comp (Subalgebra.val A)
  have hqev : ev (Polynomial.aeval x q) = q.eval (z : ℂ) := by
    simp [ev, x, coord]
  have hpev : ev (Polynomial.aeval x p) = p.eval (z : ℂ) := by
    simp [ev, x, coord]
  have hinv : ev (↑hu.unit⁻¹ : A) = (q.eval (z : ℂ))⁻¹ := by
    have hone : ev (Polynomial.aeval x q) * ev (↑hu.unit⁻¹ : A) = 1 := by
      rw [← map_mul, hu.mul_val_inv, map_one]
    rw [hqev] at hone
    exact ((mul_eq_one_iff_inv_eq₀ (hq z z.property)).mp hone).symm
  change ev (Polynomial.aeval x p * (↑hu.unit⁻¹ : A)) =
    p.eval (z : ℂ) / q.eval (z : ℂ)
  rw [map_mul, hpev, hinv, div_eq_mul_inv]

/-- Uniform approximation by rational functions without poles on `K` implies membership in the
closed polynomial algebra when the complement of `K` is connected. -/
theorem mem_polynomialClosure_of_rationalApprox {K : Set ℂ} [CompactSpace K]
    (hKc : IsConnected (Kᶜ)) (f : ℂ → ℂ) (hfc : ContinuousOn f K)
    (happrox :
      ∀ ε : ℝ, 0 < ε →
        ∃ p q : ℂ[X], (∀ z ∈ K, q.eval z ≠ 0) ∧
          ∀ z ∈ K, ‖f z - p.eval z / q.eval z‖ < ε) :
    restrictTo f hfc ∈ (polynomialFunctions K).topologicalClosure := by
  let A : Subalgebra ℂ C(K, ℂ) := (polynomialFunctions K).topologicalClosure
  have hAclosed : IsClosed (A : Set C(K, ℂ)) := by
    dsimp [A]
    exact Subalgebra.isClosed_topologicalClosure _
  apply hAclosed.closure_subset
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨p, q, hq, hf⟩ := happrox ε hε
  obtain ⟨g, hg⟩ := exists_rational_mem_polynomialClosure hKc p q hq
  refine ⟨(g : C(K, ℂ)), g.property, ?_⟩
  rw [dist_eq_norm, (restrictTo f hfc - (g : C(K, ℂ))).norm_lt_iff hε]
  intro z
  change ‖f z - (g : C(K, ℂ)) z‖ < ε
  rw [hg z]
  exact hf z z.property

/-- On a compact set with connected complement, uniform rational approximation without poles
implies uniform polynomial approximation. -/
theorem exists_polynomial_approx_of_rationalApprox (K : Set ℂ) (hK : IsCompact K)
    (hKc : IsConnected (Kᶜ)) (f : ℂ → ℂ) (hfc : ContinuousOn f K)
    (happrox :
      ∀ ε : ℝ, 0 < ε →
        ∃ p q : ℂ[X], (∀ z ∈ K, q.eval z ≠ 0) ∧
          ∀ z ∈ K, ‖f z - p.eval z / q.eval z‖ < ε)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℂ[X], ∀ z ∈ K, ‖f z - p.eval z‖ < ε := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact (mem_polynomialFunctions_topologicalClosure_iff f hfc).mp
    (mem_polynomialClosure_of_rationalApprox hKc f hfc happrox) ε hε

/-- Finite linear combinations of resolvents with poles off `K` are in the polynomial closure. -/
theorem exists_resolventSum_mem_polynomialClosure {K : Set ℂ} [CompactSpace K]
    (hKc : IsConnected (Kᶜ)) {ι : Type*} [Fintype ι] (a c : ι → ℂ)
    (ha : ∀ i, a i ∉ K) :
    ∃ g : (polynomialFunctions K).topologicalClosure,
      ∀ z : K, (g : C(K, ℂ)) z = ∑ i, c i * (a i - z)⁻¹ := by
  classical
  choose r hr using fun i ↦ exists_resolvent_mem_polynomialClosure hKc (ha i)
  refine ⟨∑ i, c i • r i, fun z ↦ ?_⟩
  simp [hr]

/-- Uniform approximation by finite resolvent sums implies membership in the polynomial closure. -/
theorem mem_polynomialClosure_of_resolventSumApprox {K : Set ℂ} [CompactSpace K]
    (hKc : IsConnected (Kᶜ)) (f : ℂ → ℂ) (hfc : ContinuousOn f K)
    (happrox :
      ∀ ε : ℝ, 0 < ε →
        ∃ n : ℕ, ∃ a c : Fin n → ℂ, (∀ i, a i ∉ K) ∧
          ∀ z ∈ K, ‖f z - ∑ i, c i * (a i - z)⁻¹‖ < ε) :
    restrictTo f hfc ∈ (polynomialFunctions K).topologicalClosure := by
  let A : Subalgebra ℂ C(K, ℂ) := (polynomialFunctions K).topologicalClosure
  have hAclosed : IsClosed (A : Set C(K, ℂ)) := by
    dsimp [A]
    exact Subalgebra.isClosed_topologicalClosure _
  have hclosure : restrictTo f hfc ∈ closure (A : Set C(K, ℂ)) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, a, c, ha, hf⟩ := happrox ε hε
    obtain ⟨g, hg⟩ := exists_resolventSum_mem_polynomialClosure hKc a c ha
    refine ⟨(g : C(K, ℂ)), g.property, ?_⟩
    rw [dist_eq_norm, (restrictTo f hfc - (g : C(K, ℂ))).norm_lt_iff hε]
    intro z
    change ‖f z - (g : C(K, ℂ)) z‖ < ε
    rw [hg z]
    exact hf z z.property
  change restrictTo f hfc ∈ A
  exact hAclosed.closure_subset hclosure

/-- Turn a partial sum of a one-variable formal power series into an ordinary polynomial. -/
noncomputable def partialSumPolynomial (p : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) : ℂ[X] :=
  ∑ i ∈ Finset.range n, Polynomial.monomial i (p.coeff i)

theorem partialSumPolynomial_eval (p : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) (z : ℂ) :
    (partialSumPolynomial p n).eval z = p.partialSum n z := by
  rw [partialSumPolynomial, Polynomial.eval_finsetSum]
  simp [FormalMultilinearSeries.partialSum, mul_comm]

set_option maxHeartbeats 1000000 in
/-- An entire function is uniformly approximable on a compact set by its Taylor polynomials. -/
theorem exists_polynomial_approx_of_differentiable (K : Set ℂ) (hK : IsCompact K)
    (g : ℂ → ℂ) (hg : Differentiable ℂ g) (ε : ℝ) (hε : 0 < ε) :
    ∃ q : ℂ[X], ∀ z ∈ K, ‖g z - q.eval z‖ < ε := by
  obtain ⟨r, hr, hKr⟩ := hK.isBounded.subset_ball_lt 0 (0 : ℂ)
  let r₀ : NNReal := ⟨r, hr.le⟩
  let p : FormalMultilinearSeries ℂ ℂ ℂ :=
    cauchyPowerSeries g 0 (1 : NNReal)
  have hp : HasFPowerSeriesOnBall g p 0 ⊤ := by
    simpa only [p] using
      hg.hasFPowerSeriesOnBall 0 (R := (1 : NNReal)) (by norm_num)
  have hu :
      TendstoUniformlyOn (fun n z ↦ p.partialSum n (z - 0)) g Filter.atTop
        (Metric.ball (0 : ℂ) r₀) :=
    hp.tendstoUniformlyOn' ENNReal.coe_lt_top
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformlyOn_iff.mp hu ε hε).exists
  refine ⟨partialSumPolynomial p n, fun z hz ↦ ?_⟩
  have hdist := hn z (hKr hz)
  rw [partialSumPolynomial_eval]
  simpa [dist_eq_norm] using hdist

/-- It suffices to approximate the target on `K` by entire functions. -/
theorem exists_polynomial_approx_of_entireApprox (K : Set ℂ) (hK : IsCompact K)
    (f : ℂ → ℂ)
    (happrox :
      ∀ ε : ℝ, 0 < ε →
        ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z ∈ K, ‖f z - g z‖ < ε)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ q : ℂ[X], ∀ z ∈ K, ‖f z - q.eval z‖ < ε := by
  obtain ⟨g, hg, hfg⟩ := happrox (ε / 2) (half_pos hε)
  obtain ⟨q, hgq⟩ :=
    exists_polynomial_approx_of_differentiable K hK g hg (ε / 2) (half_pos hε)
  refine ⟨q, fun z hz ↦ ?_⟩
  calc
    ‖f z - q.eval z‖ =
        ‖(f z - g z) + (g z - q.eval z)‖ := by congr 1; ring
    _ ≤ ‖f z - g z‖ + ‖g z - q.eval z‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hfg z hz) (hgq z hz)
    _ = ε := by ring

end

end Submission.Helpers
