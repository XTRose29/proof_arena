import Submission.PesinBlockFrequency

namespace Submission.Helpers

open LeanEval.Dynamics Filter MeasureTheory

def twoSidedBadPrefixBlock
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (cost theta : ℝ) (M : ℕ) : Set EucPlane :=
  {x | ∀ j : ℕ,
    cost * badCount (fun k => T^[k] x ∈ G) 0 j ≤ theta * j + cost * M ∧
    cost * badCount (fun k => T_inv^[k] x ∈ G) 0 j ≤
      theta * j + cost * M}

lemma measurableSet_twoSidedBadPrefixBlock
    (T T_inv : EucPlane → EucPlane)
    (hT : Measurable T) (hT_inv : Measurable T_inv)
    (G : Set EucPlane) (hG : MeasurableSet G)
    (cost theta : ℝ) (M : ℕ) :
    MeasurableSet (twoSidedBadPrefixBlock T T_inv G cost theta M) := by
  have hforward (j : ℕ) : Measurable fun x =>
      cost * badCount (fun k => T^[k] x ∈ G) 0 j := by
    have heq : (fun x => cost * badCount (fun k => T^[k] x ∈ G) 0 j) =
        fun x => cost * birkhoffSum T (setBadIndicator G) j x := by
      funext x
      rw [badCount_orbit_set_eq_birkhoffSum]
    rw [heq]
    exact measurable_const.mul (measurable_birkhoffSum hT
      (measurable_setBadIndicator hG) j)
  have hbackward (j : ℕ) : Measurable fun x =>
      cost * badCount (fun k => T_inv^[k] x ∈ G) 0 j := by
    have heq :
        (fun x => cost * badCount (fun k => T_inv^[k] x ∈ G) 0 j) =
          fun x => cost * birkhoffSum T_inv (setBadIndicator G) j x := by
      funext x
      rw [badCount_orbit_set_eq_birkhoffSum]
    rw [heq]
    exact measurable_const.mul (measurable_birkhoffSum hT_inv
      (measurable_setBadIndicator hG) j)
  have heq : twoSidedBadPrefixBlock T T_inv G cost theta M =
      ⋂ j : ℕ,
        {x | cost * badCount (fun k => T^[k] x ∈ G) 0 j ≤
          theta * j + cost * M} ∩
        {x | cost * badCount (fun k => T_inv^[k] x ∈ G) 0 j ≤
          theta * j + cost * M} := by
    ext x
    simp [twoSidedBadPrefixBlock]
  rw [heq]
  exact MeasurableSet.iInter fun j =>
    (measurableSet_le (hforward j) measurable_const).inter
      (measurableSet_le (hbackward j) measurable_const)

lemma monotone_twoSidedBadPrefixBlock
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    {cost theta : ℝ} (hcost : 0 ≤ cost) :
    Monotone (twoSidedBadPrefixBlock T T_inv G cost theta) := by
  intro M N hMN x hx j
  have hMNreal : (M : ℝ) ≤ N := by exact_mod_cast hMN
  have hbudget : theta * (j : ℝ) + cost * M ≤
      theta * j + cost * N := by
    gcongr
  exact ⟨(hx j).1.trans hbudget, (hx j).2.trans hbudget⟩

theorem ae_mem_iUnion_twoSidedBadPrefixBlock
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (T T_inv : EucPlane → EucPlane)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    (hT_inv : MeasurePreserving T_inv mu mu) (hErg_inv : Ergodic T_inv mu)
    (G : Set EucPlane) (hG : MeasurableSet G)
    {cost theta : ℝ} (hcost : 0 ≤ cost) (htheta : 0 ≤ theta)
    (hsmall : cost * mu.real Gᶜ < theta) :
    ∀ᵐ x ∂mu, x ∈ ⋃ M : ℕ,
      twoSidedBadPrefixBlock T T_inv G cost theta M := by
  have hforward := ae_eventually_badCount_orbit_set_mul_lt
    mu T hT hErg G hG hsmall
  have hbackward := ae_eventually_badCount_orbit_set_mul_lt
    mu T_inv hT_inv hErg_inv G hG hsmall
  filter_upwards [hforward, hbackward] with x hxf hxb
  obtain ⟨Mf, hMf⟩ := eventually_atTop.1 hxf
  obtain ⟨Mb, hMb⟩ := eventually_atTop.1 hxb
  let M := max Mf Mb
  refine Set.mem_iUnion.mpr ⟨M, ?_⟩
  intro j
  have hsmall_prefix
      (F : EucPlane → EucPlane) (N : ℕ)
      (hN : ∀ j, N ≤ j →
        cost * badCount (fun k => F^[k] x ∈ G) 0 j < theta * j)
      (hNM : N ≤ M) :
      cost * badCount (fun k => F^[k] x ∈ G) 0 j ≤
        theta * j + cost * M := by
    by_cases hNj : N ≤ j
    · exact (hN j hNj).le.trans (le_add_of_nonneg_right
        (mul_nonneg hcost (Nat.cast_nonneg M)))
    · have hjN : j ≤ N := Nat.le_of_lt (lt_of_not_ge hNj)
      have hcount := badCount_le_natCast
        (fun k => F^[k] x ∈ G) 0 j
      calc
        cost * badCount (fun k => F^[k] x ∈ G) 0 j ≤ cost * j :=
          mul_le_mul_of_nonneg_left hcount hcost
        _ ≤ cost * M := by
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hjN.trans hNM) hcost
        _ ≤ theta * j + cost * M :=
          le_add_of_nonneg_left (mul_nonneg htheta (Nat.cast_nonneg j))
  constructor
  · exact hsmall_prefix T Mf hMf (le_max_left _ _)
  · exact hsmall_prefix T_inv Mb hMb (le_max_right _ _)

theorem tendsto_measureReal_compl_twoSidedBadPrefixBlock_zero
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (T T_inv : EucPlane → EucPlane)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    (hT_inv : MeasurePreserving T_inv mu mu) (hErg_inv : Ergodic T_inv mu)
    (G : Set EucPlane) (hG : MeasurableSet G)
    {cost theta : ℝ} (hcost : 0 ≤ cost) (htheta : 0 ≤ theta)
    (hsmall : cost * mu.real Gᶜ < theta) :
    Tendsto (fun M : ℕ => mu.real
      (twoSidedBadPrefixBlock T T_inv G cost theta M)ᶜ)
      atTop (nhds 0) := by
  have hfull := ae_mem_iUnion_twoSidedBadPrefixBlock
    mu T T_inv hT hErg hT_inv hErg_inv G hG hcost htheta hsmall
  have hfullUnion : mu (⋃ M : ℕ,
      twoSidedBadPrefixBlock T T_inv G cost theta M)ᶜ = 0 :=
    mem_ae_iff.mp hfull
  have hinter : ⋂ M : ℕ,
      (twoSidedBadPrefixBlock T T_inv G cost theta M)ᶜ =
        (⋃ M : ℕ, twoSidedBadPrefixBlock T T_inv G cost theta M)ᶜ := by
    simp
  have hmeasure := tendsto_measure_iInter_atTop
    (μ := mu)
    (fun M => (measurableSet_twoSidedBadPrefixBlock
      T T_inv hT.measurable hT_inv.measurable G hG cost theta M).compl.nullMeasurableSet)
    (fun M N hMN => Set.compl_subset_compl.mpr
      (monotone_twoSidedBadPrefixBlock T T_inv G hcost hMN))
    ⟨0, measure_ne_top mu _⟩
  rw [hinter, hfullUnion] at hmeasure
  change Tendsto (fun M : ℕ =>
      (mu (twoSidedBadPrefixBlock T T_inv G cost theta M)ᶜ).toReal)
    atTop (nhds 0)
  exact (ENNReal.tendsto_toReal_zero_iff
    (fun M => measure_ne_top mu
      (twoSidedBadPrefixBlock T T_inv G cost theta M)ᶜ)).2 hmeasure

end Submission.Helpers
