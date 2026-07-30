import Submission.ReturnCrossing

open Filter Function Metric Set Topology
open scoped Convex

open LeanEval.Dynamics

namespace Submission.ConsecutiveHits

noncomputable section

/-- Two exact-hit sequences approaching ordered points of one affine section
provide a late left hit followed by a still later right hit. -/
theorem exists_ordered_hits_of_two_limits
    (β : ℝ → Plane) {v base : Plane} (hv : v ≠ 0)
    {L q m z R T : ℝ}
    (hLq : L < q) (hqm : q < m) (hmz : m < z) (hzR : z < R)
    {σq σz : ℕ → ℝ}
    (hσq : Tendsto σq atTop atTop)
    (hβq :
      Tendsto (β ∘ σq) atTop
        (𝓝 (Transversal.sectionPoint v base q)))
    (hhitq : ∀ n,
      Transversal.transverseValue v base (β (σq n)) = 0)
    (hσz : Tendsto σz atTop atTop)
    (hβz :
      Tendsto (β ∘ σz) atTop
        (𝓝 (Transversal.sectionPoint v base z)))
    (hhitz : ∀ n,
      Transversal.transverseValue v base (β (σz n)) = 0) :
    ∃ a b qa qb : ℝ,
      T < a ∧ a < b ∧
      qa ∈ Icc L m ∧ qa < m ∧
      qb ∈ Icc m R ∧ m < qb ∧
      β a = Transversal.sectionPoint v base qa ∧
      β b = Transversal.sectionPoint v base qb := by
  let uq : ℕ → ℝ :=
    fun n ↦ Transversal.sectionValue v base (β (σq n))
  let uz : ℕ → ℝ :=
    fun n ↦ Transversal.sectionValue v base (β (σz n))
  have huq : Tendsto uq atTop (𝓝 q) := by
    have h :=
      (Transversal.continuous_sectionValue v base).tendsto
        (Transversal.sectionPoint v base q)
        |>.comp hβq
    simpa only [uq, Function.comp_def,
      Transversal.sectionValue_sectionPoint hv] using h
  have huz : Tendsto uz atTop (𝓝 z) := by
    have h :=
      (Transversal.continuous_sectionValue v base).tendsto
        (Transversal.sectionPoint v base z)
        |>.comp hβz
    simpa only [uz, Function.comp_def,
      Transversal.sectionValue_sectionPoint hv] using h
  have hqWindow : ∀ᶠ n in atTop, uq n ∈ Ioo L m :=
    huq.eventually (Ioo_mem_nhds hLq hqm)
  have hqLate : ∀ᶠ n in atTop, T < σq n :=
    hσq.eventually (eventually_gt_atTop T)
  obtain ⟨n, hnWindow, hnLate⟩ :=
    (hqWindow.and hqLate).exists
  have hzWindow : ∀ᶠ k in atTop, uz k ∈ Ioo m R :=
    huz.eventually (Ioo_mem_nhds hmz hzR)
  have hzLate : ∀ᶠ k in atTop, σq n < σz k :=
    hσz.eventually (eventually_gt_atTop (σq n))
  obtain ⟨k, hkWindow, hkLate⟩ :=
    (hzWindow.and hzLate).exists
  refine
    ⟨σq n, σz k, uq n, uz k, hnLate, hkLate,
      ⟨hnWindow.1.le, hnWindow.2.le⟩, hnWindow.2,
      ⟨hkWindow.1.le, hkWindow.2.le⟩, hkWindow.1, ?_, ?_⟩
  · exact
      (Transversal.sectionPoint_sectionValue hv (hhitq n)).symm
  · exact
      (Transversal.sectionPoint_sectionValue hv (hhitz k)).symm

/-- Between a hit on the left of a transverse coordinate and a later hit on
the right, there are two consecutive hits of the surrounding compact
transverse segment whose coordinates straddle the chosen divider. -/
theorem exists_consecutive_hits_straddling
    {G : Plane → Plane} (β : ℝ → Plane)
    (hβ : IsIntegralCurve β (fun _ y ↦ G y))
    {v base : Plane} (hv : v ≠ 0)
    {L m R a b qa qb : ℝ}
    (hLm : L < m) (hmR : m < R) (hab : a < b)
    (hqa : qa ∈ Icc L m) (hqam : qa < m)
    (hqb : qb ∈ Icc m R) (hmqb : m < qb)
    (hβa : β a = Transversal.sectionPoint v base qa)
    (hβb : β b = Transversal.sectionPoint v base qb)
    (hpositive : ∀ u ∈ Icc L R,
      0 <
        Transversal.transverseFunctional v
          (G (Transversal.sectionPoint v base u))) :
    ∃ s t A B : ℝ,
      a ≤ s ∧ s < t ∧ t ≤ b ∧
      A ∈ Icc L R ∧ B ∈ Icc L R ∧
      A < m ∧ m ≤ B ∧
      β s = Transversal.sectionPoint v base A ∧
      β t = Transversal.sectionPoint v base B ∧
      ∀ u ∈ Icc s t,
        β u ∈
            [Transversal.sectionPoint v base L -[ℝ]
              Transversal.sectionPoint v base R] →
          u = s ∨ u = t := by
  let fullSeg : Set Plane :=
    [Transversal.sectionPoint v base L -[ℝ]
      Transversal.sectionPoint v base R]
  let rightSeg : Set Plane :=
    [Transversal.sectionPoint v base m -[ℝ]
      Transversal.sectionPoint v base R]
  let Hright : Set ℝ := Icc a b ∩ β ⁻¹' rightSeg
  have hrightSegCompact : IsCompact rightSeg := by
    dsimp only [rightSeg]
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  have hrightCompact : IsCompact Hright := by
    exact
      isCompact_Icc.inter_right
        (hrightSegCompact.isClosed.preimage hβ.continuous)
  have hrightNe : Hright.Nonempty := by
    refine ⟨b, right_mem_Icc.mpr hab.le, ?_⟩
    change β b ∈ rightSeg
    dsimp only [rightSeg]
    rw [hβb]
    exact
      Transversal.sectionPoint_mem_segment hmR
        ⟨hmqb.le, hqb.2⟩
  obtain ⟨t, htH, htMin⟩ :=
    hrightCompact.exists_isMinOn hrightNe
      continuous_id.continuousOn
  change t ∈ Icc a b ∧ β t ∈ rightSeg at htH
  have hat : a < t := by
    have hatle : a ≤ t := htH.1.1
    refine lt_of_le_of_ne hatle ?_
    intro hat
    have haRight : β a ∈ rightSeg := by
      simpa only [hat] using htH.2
    obtain ⟨u, hu, hau⟩ :=
      Transversal.exists_eq_sectionPoint_of_mem_segment hmR haRight
    have hqu : qa = u :=
      Transversal.sectionPoint_injective hv
        (hβa.symm.trans hau)
    linarith [hqam, hu.1]
  have htb : t ≤ b := htH.1.2
  obtain ⟨B, hB, hβt⟩ :=
    Transversal.exists_eq_sectionPoint_of_mem_segment hmR htH.2
  have hBLR : B ∈ Icc L R :=
    ⟨hLm.le.trans hB.1, hB.2⟩
  let f : ℝ → ℝ :=
    fun u ↦ Transversal.transverseValue v base (β u)
  have hft : f t = 0 := by
    simp only [f, hβt]
    exact Transversal.transverseValue_sectionPoint hv B
  have hfderiv :
      HasDerivAt f
        (Transversal.transverseFunctional v (G (β t))) t := by
    exact Transversal.hasDerivAt_transverseValue hβ v base t
  have hderiv : 0 < deriv f t := by
    rw [hfderiv.deriv, hβt]
    exact hpositive B hBLR
  have hneg : ∀ᶠ u in 𝓝[<] t, f u < 0 := by
    have hsign :=
      eventually_nhdsWithin_sign_eq_of_deriv_pos hderiv hft
    filter_upwards
      [hsign.filter_mono inf_le_left, self_mem_nhdsWithin]
      with u huSign hu
    apply sign_eq_neg_one_iff.mp
    exact huSign.trans (sign_neg (sub_neg.mpr hu))
  obtain ⟨η, hηt, hηsub⟩ :=
    mem_nhdsLT_iff_exists_Ioo_subset.mp hneg
  let t₀ : ℝ := max η ((a + t) / 2)
  have hat₀ : a < t₀ := by
    dsimp only [t₀]
    have hmid : a < (a + t) / 2 := by
      linarith [hat]
    exact hmid.trans_le (le_max_right η ((a + t) / 2))
  have ht₀t : t₀ < t := by
    dsimp only [t₀]
    rw [max_lt_iff]
    exact ⟨hηt, by linarith [hat]⟩
  have hηt₀ : η ≤ t₀ := by
    exact le_max_left _ _
  let H : Set ℝ := Icc a t₀ ∩ β ⁻¹' fullSeg
  have hfullSegCompact : IsCompact fullSeg := by
    dsimp only [fullSeg]
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  have hHcompact : IsCompact H := by
    exact
      isCompact_Icc.inter_right
        (hfullSegCompact.isClosed.preimage hβ.continuous)
  have hHne : H.Nonempty := by
    refine ⟨a, left_mem_Icc.mpr hat₀.le, ?_⟩
    change β a ∈ fullSeg
    dsimp only [fullSeg]
    rw [hβa]
    exact
      Transversal.sectionPoint_mem_segment
        (hLm.trans hmR) ⟨hqa.1, hqa.2.trans hmR.le⟩
  obtain ⟨s, hsH, hsMax⟩ :=
    hHcompact.exists_isMaxOn hHne
      continuous_id.continuousOn
  change s ∈ Icc a t₀ ∧ β s ∈ fullSeg at hsH
  have has : a ≤ s := hsH.1.1
  have hst₀ : s ≤ t₀ := hsH.1.2
  have hst : s < t := hst₀.trans_lt ht₀t
  obtain ⟨A, hA, hβs⟩ :=
    Transversal.exists_eq_sectionPoint_of_mem_segment
      (hLm.trans hmR) hsH.2
  have hAm : A < m := by
    by_contra hnot
    have hAwm : m ≤ A := le_of_not_gt hnot
    have hsRight : β s ∈ rightSeg := by
      dsimp only [rightSeg]
      rw [hβs]
      exact
        Transversal.sectionPoint_mem_segment hmR
          ⟨hAwm, hA.2⟩
    have htles : t ≤ s :=
      htMin ⟨⟨has, hst.le.trans htb⟩, hsRight⟩
    exact (not_le_of_gt hst) htles
  refine
    ⟨s, t, A, B, has, hst, htb, hA, hBLR,
      hAm, hB.1, hβs, hβt, ?_⟩
  intro u hu huSeg
  by_cases hut : u = t
  · exact Or.inr hut
  left
  have hutlt : u < t := hu.2.lt_of_ne hut
  have hut₀ : u ≤ t₀ := by
    by_contra hnot
    have hηu : η < u := hηt₀.trans_lt (lt_of_not_ge hnot)
    have hfuNeg : f u < 0 := hηsub ⟨hηu, hutlt⟩
    have hfuZero :=
      OrbitArc.transverseValue_segment_eq_zero
        (Transversal.transverseValue_sectionPoint hv L)
        (Transversal.transverseValue_sectionPoint hv R)
        huSeg
    exact (hfuNeg.ne hfuZero).elim
  have huH : u ∈ H :=
    ⟨⟨has.trans hu.1, hut₀⟩, huSeg⟩
  exact le_antisymm (hsMax huH) hu.1

end

end Submission.ConsecutiveHits
