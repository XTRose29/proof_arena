import Submission.PesinContractionBlock
import Submission.CocycleCheapFrequency

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory

noncomputable def setBadIndicator
    {M : Type*} (G : Set M) : M → ℝ :=
  Gᶜ.indicator 1

lemma measurable_setBadIndicator
    {M : Type*} [MeasurableSpace M] {G : Set M}
    (hG : MeasurableSet G) : Measurable (setBadIndicator G) := by
  exact measurable_const.indicator hG.compl

lemma integral_setBadIndicator
    {M : Type*} [MeasurableSpace M] (mu : Measure M)
    {G : Set M} (hG : MeasurableSet G) :
    ∫ x, setBadIndicator G x ∂mu = mu.real Gᶜ := by
  exact integral_indicator_one hG.compl

lemma integrable_setBadIndicator
    {M : Type*} [MeasurableSpace M] (mu : Measure M) [IsFiniteMeasure mu]
    {G : Set M} (hG : MeasurableSet G) :
    Integrable (setBadIndicator G) mu := by
  apply Integrable.of_bound (measurable_setBadIndicator hG).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun x => by
    classical
    rw [setBadIndicator, Set.indicator_apply]
    split <;> norm_num

lemma badCount_orbit_set_eq_birkhoffSum
    {M : Type*} (T : M → M) (G : Set M) (m : ℕ) (x : M) :
    badCount (fun j => T^[j] x ∈ G) 0 m =
      birkhoffSum T (setBadIndicator G) m x := by
  classical
  simp only [badCount, birkhoffSum, Nat.zero_add, setBadIndicator]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Set.indicator_apply]
  by_cases hG : T^[j] x ∈ G <;> simp [hG]

theorem ae_eventually_badCount_orbit_set_mul_lt
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    (G : Set M) (hG : MeasurableSet G)
    {C theta : ℝ} (hsmall : C * mu.real Gᶜ < theta) :
    ∀ᵐ x ∂mu, ∀ᶠ m : ℕ in atTop,
      C * badCount (fun j => T^[j] x ∈ G) 0 m < theta * m := by
  have havg := ae_tendsto_birkhoffAverage_integral
    mu T hT hErg (setBadIndicator G)
      (measurable_setBadIndicator hG)
      (integrable_setBadIndicator mu hG)
  filter_upwards [havg] with x hxavg
  have hscaled : Tendsto
      (fun m => C * birkhoffAverage ℝ T (setBadIndicator G) m x)
      atTop (nhds (C * mu.real Gᶜ)) := by
    simpa [integral_setBadIndicator mu hG] using
      tendsto_const_nhds.mul hxavg
  have heventually : ∀ᶠ m : ℕ in atTop,
      C * birkhoffAverage ℝ T (setBadIndicator G) m x < theta :=
    (tendsto_order.1 hscaled).2 theta hsmall
  filter_upwards [heventually, eventually_gt_atTop 0] with m hm hmpos
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hmpos
  rw [badCount_orbit_set_eq_birkhoffSum]
  rw [birkhoffAverage, smul_eq_mul] at hm
  have hm' :
      (C * birkhoffSum T (setBadIndicator G) m x) / m < theta := by
    calc
      (C * birkhoffSum T (setBadIndicator G) m x) / m =
          C * ((m : ℝ)⁻¹ * birkhoffSum T (setBadIndicator G) m x) := by
        field_simp [hmreal.ne']
      _ < theta := hm
  exact (div_lt_iff₀ hmreal).mp hm'

theorem exists_pesinContractionBlock_twoSided_low_badCount
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    {lam1 lam2 eta cost theta : ℝ}
    (hlam1 : lam1 = ∫ x, lyapunovUpperAt T x ∂mu)
    (hlam2 : lam2 = ∫ x, lyapunovLowerAt T x ∂mu)
    (hlam1_pos : 0 < lam1) (hlam2_neg : lam2 < 0)
    (heta : 0 < eta)
    (hstable_neg : lam2 + 5 * eta < 0)
    (hunstable_neg : -lam1 + 5 * eta < 0)
    (hrate : 8 * eta < hyperbolicRate lam1 lam2)
    (htheta : 0 < theta) :
    ∃ C : ℕ,
      let G := pesinContractionBlock T T_inv lam1 lam2 eta C
      MeasurableSet G ∧
      ∀ᵐ x ∂mu,
        (∀ᶠ m : ℕ in atTop,
          cost * badCount (fun j => T^[j] x ∈ G) 0 m < theta * m) ∧
        ∀ᶠ m : ℕ in atTop,
          cost * badCount (fun j => T_inv^[j] x ∈ G) 0 m < theta * m := by
  have hmeasure := tendsto_measureReal_compl_pesinContractionBlock_zero
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta
      hstable_neg hunstable_neg hrate
  have hscaled : Tendsto (fun C : ℕ => cost * mu.real
      (pesinContractionBlock T T_inv lam1 lam2 eta C)ᶜ)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hmeasure
  have hsmall : ∀ᶠ C : ℕ in atTop, cost * mu.real
      (pesinContractionBlock T T_inv lam1 lam2 eta C)ᶜ < theta :=
    (tendsto_order.1 hscaled).2 theta htheta
  obtain ⟨C, hC⟩ := hsmall.exists
  let G := pesinContractionBlock T T_inv lam1 lam2 eta C
  have hG : MeasurableSet G := measurableSet_pesinContractionBlock
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right lam1 lam2 eta C
  have hT_inv : MeasurePreserving T_inv mu mu :=
    measurePreserving_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hT
  have hErg_inv : Ergodic T_inv mu :=
    ergodic_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hErg
  have hforward := ae_eventually_badCount_orbit_set_mul_lt
    mu T hT hErg G hG hC
  have hbackward := ae_eventually_badCount_orbit_set_mul_lt
    mu T_inv hT_inv hErg_inv G hG hC
  exact ⟨C, hG, hforward.and hbackward⟩

end Submission.Helpers
