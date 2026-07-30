import Submission.PesinBadPrefixBlock
import Submission.PesinRegularBlock
import Submission.MaximalErgodic

namespace Submission.Helpers

open LeanEval.Dynamics Filter MeasureTheory

noncomputable def badPrefixViolationSet
    (T : EucPlane → EucPlane) (G : Set EucPlane)
    (cost theta : ℝ) : Set EucPlane :=
  positiveMaxSetInfinite T
    (fun x => cost * setBadIndicator G x - theta)

lemma birkhoffSum_badPrefixPotential
    (T : EucPlane → EucPlane) (G : Set EucPlane)
    (cost theta : ℝ) (n : ℕ) (x : EucPlane) :
    birkhoffSum T (fun z => cost * setBadIndicator G z - theta) n x =
      cost * badCount (fun j => T^[j] x ∈ G) 0 n - theta * n := by
  rw [badCount_orbit_set_eq_birkhoffSum]
  simp only [birkhoffSum, Finset.sum_sub_distrib, Finset.mul_sum]
  simp [mul_comm]

lemma not_mem_badPrefixViolationSet_iff
    (T : EucPlane → EucPlane) (G : Set EucPlane)
    {cost theta : ℝ} (x : EucPlane) :
    x ∉ badPrefixViolationSet T G cost theta ↔
      ∀ n : ℕ,
        cost * badCount (fun j => T^[j] x ∈ G) 0 n ≤ theta * n := by
  constructor
  · intro hx n
    by_contra hle
    have hlt :
        theta * (n : ℝ) <
          cost * badCount (fun j => T^[j] x ∈ G) 0 n :=
      lt_of_not_ge hle
    have hn : 0 < n := by
      by_contra hn
      have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn
      subst n
      simp [badCount] at hlt
    apply hx
    apply Set.mem_iUnion_of_mem n
    rw [mem_positiveMaxSet_iff]
    refine ⟨n, hn, le_rfl, ?_⟩
    rw [show windowSum
        (fun k => cost * setBadIndicator G (T^[k] x) - theta) 0 n =
          birkhoffSum T
            (fun z => cost * setBadIndicator G z - theta) n x by
          simp [windowSum, birkhoffSum]]
    rw [birkhoffSum_badPrefixPotential]
    linarith
  · intro hbound hx
    obtain ⟨N, hxN⟩ := Set.mem_iUnion.mp hx
    rw [mem_positiveMaxSet_iff] at hxN
    obtain ⟨n, hn, _hnN, hpositive⟩ := hxN
    have hsum :
        windowSum
            (fun k => cost * setBadIndicator G (T^[k] x) - theta) 0 n =
          cost * badCount (fun j => T^[j] x ∈ G) 0 n - theta * n := by
      rw [show windowSum
          (fun k => cost * setBadIndicator G (T^[k] x) - theta) 0 n =
            birkhoffSum T
              (fun z => cost * setBadIndicator G z - theta) n x by
            simp [windowSum, birkhoffSum]]
      exact birkhoffSum_badPrefixPotential T G cost theta n x
    rw [hsum] at hpositive
    linarith [hbound n]

lemma measurableSet_badPrefixViolationSet
    (T : EucPlane → EucPlane) (hT : Measurable T)
    (G : Set EucPlane) (hG : MeasurableSet G)
    (cost theta : ℝ) :
    MeasurableSet (badPrefixViolationSet T G cost theta) := by
  apply measurableSet_positiveMaxSetInfinite hT
  exact measurable_const.mul (measurable_setBadIndicator hG) |>.sub
    measurable_const

lemma measureReal_badPrefixViolationSet_le
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (T : EucPlane → EucPlane) (hT : MeasurePreserving T mu mu)
    (G : Set EucPlane) (hG : MeasurableSet G)
    {cost theta : ℝ} (hcost : 0 ≤ cost) (htheta : 0 < theta) :
    mu.real (badPrefixViolationSet T G cost theta) ≤
      cost * mu.real Gᶜ / theta := by
  let f : EucPlane → ℝ :=
    fun x => cost * setBadIndicator G x - theta
  let E := badPrefixViolationSet T G cost theta
  have hf_measurable : Measurable f := by
    exact measurable_const.mul (measurable_setBadIndicator hG) |>.sub
      measurable_const
  have hf_integrable : Integrable f mu := by
    exact (integrable_setBadIndicator mu hG).const_mul cost
      |>.sub (integrable_const theta)
  have hmax : 0 ≤ ∫ x in E, f x ∂mu := by
    exact integral_positiveMaxSetInfinite_nonneg
      mu T hT f hf_measurable hf_integrable
  have hbad_nonneg :
      0 ≤ᵐ[mu] setBadIndicator G := by
    filter_upwards [] with x
    classical
    simp [setBadIndicator, Set.indicator_apply]
    positivity
  have hbad_le :
      (∫ x in E, setBadIndicator G x ∂mu) ≤ mu.real Gᶜ := by
    calc
      (∫ x in E, setBadIndicator G x ∂mu) ≤
          ∫ x, setBadIndicator G x ∂mu :=
        setIntegral_le_integral (integrable_setBadIndicator mu hG)
          hbad_nonneg
      _ = mu.real Gᶜ := integral_setBadIndicator mu hG
  have hE_measurable : MeasurableSet E := by
    exact measurableSet_badPrefixViolationSet
      T hT.measurable G hG cost theta
  have hrewrite :
      (∫ x in E, f x ∂mu) =
        cost * (∫ x in E, setBadIndicator G x ∂mu) -
          theta * mu.real E := by
    dsimp [f]
    rw [integral_sub
      ((integrable_setBadIndicator mu hG).const_mul cost).integrableOn
      (integrable_const theta)]
    rw [integral_const_mul]
    simp [measureReal_def]
    ring
  rw [hrewrite] at hmax
  have hscaled :
      cost * (∫ x in E, setBadIndicator G x ∂mu) ≤
        cost * mu.real Gᶜ :=
    mul_le_mul_of_nonneg_left hbad_le hcost
  apply (le_div_iff₀ htheta).2
  nlinarith

lemma measureReal_compl_twoSidedBadPrefixBlock_zero_le
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (T T_inv : EucPlane → EucPlane)
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    (G : Set EucPlane) (hG : MeasurableSet G)
    {cost theta : ℝ} (hcost : 0 ≤ cost) (htheta : 0 < theta) :
    mu.real
        (twoSidedBadPrefixBlock T T_inv G cost theta 0)ᶜ ≤
      2 * cost * mu.real Gᶜ / theta := by
  let Ef := badPrefixViolationSet T G cost theta
  let Eb := badPrefixViolationSet T_inv G cost theta
  have hblock :
      twoSidedBadPrefixBlock T T_inv G cost theta 0 = Efᶜ ∩ Ebᶜ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff]
    rw [not_mem_badPrefixViolationSet_iff,
      not_mem_badPrefixViolationSet_iff]
    simp [twoSidedBadPrefixBlock]
    constructor
    · intro h
      exact ⟨fun n => (h n).1, fun n => (h n).2⟩
    · rintro ⟨hf, hb⟩ n
      exact ⟨hf n, hb n⟩
  have hEf :
      mu.real Ef ≤ cost * mu.real Gᶜ / theta :=
    measureReal_badPrefixViolationSet_le
      mu T hT G hG hcost htheta
  have hEb :
      mu.real Eb ≤ cost * mu.real Gᶜ / theta :=
    measureReal_badPrefixViolationSet_le
      mu T_inv hT_inv G hG hcost htheta
  rw [hblock, Set.compl_inter]
  calc
    mu.real (Efᶜᶜ ∪ Ebᶜᶜ) ≤ mu.real Efᶜᶜ + mu.real Ebᶜᶜ :=
      measureReal_union_le _ _
    _ = mu.real Ef + mu.real Eb := by simp
    _ ≤ cost * mu.real Gᶜ / theta +
        cost * mu.real Gᶜ / theta := add_le_add hEf hEb
    _ = 2 * cost * mu.real Gᶜ / theta := by ring

theorem exists_pesinContractionBlock_twoSided_zeroPrefix_highMeasure
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    {lam1 lam2 eta cost theta gamma : ℝ}
    (hlam1 : lam1 = ∫ x, LeanEval.Dynamics.lyapunovUpperAt T x ∂mu)
    (hlam2 : lam2 = ∫ x, LeanEval.Dynamics.lyapunovLowerAt T x ∂mu)
    (hlam1_pos : 0 < lam1) (hlam2_neg : lam2 < 0)
    (heta : 0 < eta)
    (hstable_neg : lam2 + 5 * eta < 0)
    (hunstable_neg : -lam1 + 5 * eta < 0)
    (hrate : 8 * eta < hyperbolicRate lam1 lam2)
    (hcost : 0 ≤ cost) (htheta : 0 < theta) (hgamma : 0 < gamma) :
    ∃ C : ℕ,
      let G := pesinContractionBlock T T_inv lam1 lam2 eta C
      let good := twoSidedBadPrefixBlock T T_inv G cost theta 0
      MeasurableSet G ∧ MeasurableSet good ∧ mu.real goodᶜ < gamma := by
  have hmeasure := tendsto_measureReal_compl_pesinContractionBlock_zero
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta
      hstable_neg hunstable_neg hrate
  have hscaled :
      Tendsto
        (fun C : ℕ =>
          2 * cost *
              mu.real
                (pesinContractionBlock T T_inv lam1 lam2 eta C)ᶜ /
            theta)
        atTop (nhds 0) := by
    have hmul :
        Tendsto
          (fun C : ℕ =>
            (2 * cost) *
              mu.real
                (pesinContractionBlock T T_inv lam1 lam2 eta C)ᶜ)
          atTop (nhds ((2 * cost) * 0)) :=
      tendsto_const_nhds.mul hmeasure
    simpa only [mul_zero, zero_div] using hmul.div_const theta
  have heventually : ∀ᶠ C : ℕ in atTop,
      2 * cost *
          mu.real (pesinContractionBlock T T_inv lam1 lam2 eta C)ᶜ /
        theta < gamma :=
    (tendsto_order.1 hscaled).2 gamma hgamma
  obtain ⟨C, hC⟩ := heventually.exists
  let G := pesinContractionBlock T T_inv lam1 lam2 eta C
  let good := twoSidedBadPrefixBlock T T_inv G cost theta 0
  have hG : MeasurableSet G :=
    measurableSet_pesinContractionBlock
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        lam1 lam2 eta C
  have hT_inv : MeasurePreserving T_inv mu mu :=
    measurePreserving_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hT
  have hgood : MeasurableSet good :=
    measurableSet_twoSidedBadPrefixBlock
      T T_inv hT.measurable hT_inv.measurable G hG cost theta 0
  refine ⟨C, hG, hgood, ?_⟩
  exact (measureReal_compl_twoSidedBadPrefixBlock_zero_le
    mu T T_inv hT hT_inv G hG hcost htheta).trans_lt hC

theorem exists_pesinRegularBlock_twoSided_zeroPrefix_highMeasure
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    {lam1 lam2 eta cost theta gamma : ℝ}
    (hlam1 : lam1 = ∫ x, lyapunovUpperAt T x ∂mu)
    (hlam2 : lam2 = ∫ x, lyapunovLowerAt T x ∂mu)
    (hlam1_pos : 0 < lam1) (hlam2_neg : lam2 < 0)
    (heta : 0 < eta)
    (hstable_neg : lam2 + 5 * eta < 0)
    (hunstable_neg : -lam1 + 5 * eta < 0)
    (hrate : 8 * eta < hyperbolicRate lam1 lam2)
    (hcost : 0 ≤ cost) (htheta : 0 < theta) (hgamma : 0 < gamma) :
    ∃ C : ℕ,
      let G := pesinRegularBlock T T_inv lam1 lam2 eta C
      let good := twoSidedBadPrefixBlock T T_inv G cost theta 0
      MeasurableSet G ∧ MeasurableSet good ∧ mu.real goodᶜ < gamma := by
  have hmeasure := tendsto_measureReal_compl_pesinRegularBlock_zero
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta
      hstable_neg hunstable_neg hrate
  have hscaled :
      Tendsto
        (fun C : ℕ =>
          2 * cost *
              mu.real (pesinRegularBlock T T_inv lam1 lam2 eta C)ᶜ /
            theta)
        atTop (nhds 0) := by
    have hmul :
        Tendsto
          (fun C : ℕ =>
            (2 * cost) *
              mu.real (pesinRegularBlock T T_inv lam1 lam2 eta C)ᶜ)
          atTop (nhds ((2 * cost) * 0)) :=
      tendsto_const_nhds.mul hmeasure
    simpa only [mul_zero, zero_div] using hmul.div_const theta
  have heventually : ∀ᶠ C : ℕ in atTop,
      2 * cost *
          mu.real (pesinRegularBlock T T_inv lam1 lam2 eta C)ᶜ /
        theta < gamma :=
    (tendsto_order.1 hscaled).2 gamma hgamma
  obtain ⟨C, hC⟩ := heventually.exists
  let G := pesinRegularBlock T T_inv lam1 lam2 eta C
  let good := twoSidedBadPrefixBlock T T_inv G cost theta 0
  have hG : MeasurableSet G :=
    measurableSet_pesinRegularBlock
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        lam1 lam2 eta C
  have hT_inv : MeasurePreserving T_inv mu mu :=
    measurePreserving_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hT
  have hgood : MeasurableSet good :=
    measurableSet_twoSidedBadPrefixBlock
      T T_inv hT.measurable hT_inv.measurable G hG cost theta 0
  refine ⟨C, hG, hgood, ?_⟩
  exact (measureReal_compl_twoSidedBadPrefixBlock_zero_le
    mu T T_inv hT hT_inv G hG hcost htheta).trans_lt hC

end Submission.Helpers
