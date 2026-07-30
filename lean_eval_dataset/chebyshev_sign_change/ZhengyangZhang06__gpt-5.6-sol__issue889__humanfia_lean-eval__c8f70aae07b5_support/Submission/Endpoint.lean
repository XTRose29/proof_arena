import Submission.SignChange

open Complex Filter Set Topology

namespace Submission.Endpoint

open Submission.Analytic Submission.Helpers Submission.PrimeSeries
open Submission.SignChange

lemma eventually_chiFour_LFunction_ne_zero_nhdsNE {rho : ℂ}
    (_hrho : DirichletCharacter.LFunction chiFour rho = 0) :
    ∀ᶠ s in 𝓝[≠] rho, DirichletCharacter.LFunction chiFour s ≠ 0 := by
  have hL : AnalyticAt ℂ (DirichletCharacter.LFunction chiFour) rho :=
    differentiable_chiFour_LFunction.analyticAt rho
  have hfinite :
      analyticOrderAt (DirichletCharacter.LFunction chiFour) rho ≠ ⊤ :=
    chiFour_LFunction_analyticOrderAt_ne_top rho
  let m := analyticOrderNatAt (DirichletCharacter.LFunction chiFour) rho
  obtain ⟨g, hg, hg0, hfactor⟩ :=
    (hL.analyticOrderNatAt_eq_iff hfinite (n := m)).mp rfl
  have hgNe : ∀ᶠ s in 𝓝 rho, g s ≠ 0 :=
    hg.continuousAt.preimage_mem_nhds (compl_singleton_mem_nhds_iff.mpr hg0)
  filter_upwards [hfactor.filter_mono nhdsWithin_le_nhds,
    hgNe.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with s hfactorS hgS hs
  rw [hfactorS]
  exact smul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hs)) hgS

private lemma nontrivial_zero_re_le_half_of_global_positive_neg_one {C : ℝ}
    (hone : ∀ n, 1 ≤ adjustedPrimeSum (-1) C n) {rho : ℂ}
    (hrho : rho ∈ chiFourNontrivialZeroSet) :
    rho.re ≤ (1 / 2 : ℝ) := by
  have hreBounds : (0 : ℝ) < rho.re ∧ rho.re < 1 := ⟨hrho.1, hrho.2.1⟩
  by_contra hle
  ·
    have hre : (1 / 2 : ℝ) < rho.re := lt_of_not_ge hle
    have hbeta : mellinAbscissa (-1) C = (1 / 2 : ℝ) :=
      mellinAbscissa_eq_half hone (by norm_num)
    have hA : AnalyticAt ℂ (adjustedPrimeDirichlet (-1) C) rho := by
      unfold adjustedPrimeDirichlet
      exact analyticAt_id.mul (analyticAt_adjustedPrimeMellin hone (by simpa [hbeta] using hre))
    have hleft : Filter.Tendsto
        (fun s : ℂ => (s - rho) * deriv (adjustedPrimeDirichlet (-1) C) s)
        (𝓝[≠] rho) (𝓝 0) := by
      have hsub : Filter.Tendsto (fun s : ℂ => s - rho) (𝓝[≠] rho) (𝓝 0) := by
        have hcont : ContinuousAt (fun s : ℂ => s - rho) rho := by fun_prop
        simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
      simpa using hsub.mul
        (hA.deriv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    have him : rho.im ≠ 0 := by
      intro him
      have hrhoReal : rho = (rho.re : ℂ) := by
        apply Complex.ext
        · simp
        · simp [him]
      have hrealNe : DirichletCharacter.LFunction chiFour (rho.re : ℂ) ≠ 0 :=
        Submission.Central.chiFour_LFunction_real_ne_zero (by linarith)
      rw [hrhoReal] at hrho
      exact hrealNe hrho.2.2
    have hright := tendsto_twistedPrimeLogContinuation_nonreal_zero
      hrho.2.2 hre.le him
    have heq :
        (fun s : ℂ => (s - rho) * deriv (adjustedPrimeDirichlet (-1) C) s) =ᶠ[𝓝[≠] rho]
          fun s : ℂ => (s - rho) * twistedPrimeLogContinuation s := by
      have hsReEvent : ∀ᶠ s : ℂ in 𝓝[≠] rho, (1 / 2 : ℝ) < s.re :=
        Filter.Eventually.filter_mono nhdsWithin_le_nhds
          ((isOpen_lt continuous_const continuous_re).mem_nhds hre)
      filter_upwards [eventually_chiFour_LFunction_ne_zero_nhdsNE hrho.2.2,
        hsReEvent]
        with s hL hsRe
      rw [deriv_adjustedPrimeDirichlet_eq_neg_twistedPrimeLogContinuation_of_ne_zero
        hone]
      · norm_num
      · rw [hbeta, max_self]
        exact hsRe
      · exact hL
    have hleft' : Filter.Tendsto
        (fun s : ℂ => (s - rho) * deriv (adjustedPrimeDirichlet (-1) C) s)
        (𝓝[≠] rho) (𝓝 (-(chiFourZeroMultiplicity rho : ℂ))) :=
      (tendsto_congr' heq).2 hright
    have hzero : (0 : ℂ) = -(chiFourZeroMultiplicity rho : ℂ) :=
      tendsto_nhds_unique hleft hleft'
    have hmult : chiFourZeroMultiplicity rho = 0 := by
      exact_mod_cast (neg_eq_zero.mp hzero.symm)
    exact (Nat.ne_of_gt (chiFourZeroMultiplicity_pos hrho.2.2)) hmult

lemma nontrivial_zero_re_eq_half_of_global_positive_neg_one {C : ℝ}
    (hone : ∀ n, 1 ≤ adjustedPrimeSum (-1) C n) {rho : ℂ}
    (hrho : rho ∈ chiFourNontrivialZeroSet) :
    rho.re = (1 / 2 : ℝ) := by
  apply le_antisymm
  · exact nontrivial_zero_re_le_half_of_global_positive_neg_one hone hrho
  · have hsym := nontrivial_zero_re_le_half_of_global_positive_neg_one hone
      (chiFourNontrivialZeroSet_one_sub hrho)
    norm_num only [Complex.sub_re, Complex.one_re] at hsym
    linarith

lemma shifted_zero_re_eq_zero_of_global_positive_neg_one {C R : ℝ}
    (hone : ∀ n, 1 ≤ adjustedPrimeSum (-1) C n) {u : ℂ}
    (hu : Submission.ZeroMass.shiftedZeroDivisor R u ≠ 0) :
    u.re = 0 := by
  have hcritical := nontrivial_zero_re_eq_half_of_global_positive_neg_one hone
    (Submission.ResidueCertificate.shiftedZero_original_mem_nontrivial hu)
  rw [Complex.add_re] at hcritical
  norm_num at hcritical
  linarith

end Submission.Endpoint
