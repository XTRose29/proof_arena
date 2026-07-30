import Submission.ConsecutiveHits
import Submission.ExteriorComponents

open Filter Function Metric Set Topology
open scoped Convex

open LeanEval.Dynamics

namespace Submission.SectionOrder

noncomputable section

theorem exists_eventually_ne_of_injOn_Ici
    (β : ℝ → Plane) (hβinj : InjOn β (Ici (0 : ℝ)))
    (p : Plane) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t, T ≤ t → β t ≠ p := by
  by_cases hp : p ∈ β '' Ici (0 : ℝ)
  · obtain ⟨s, hs, hβs⟩ := hp
    change 0 ≤ s at hs
    refine ⟨s + 1, by linarith, ?_⟩
    intro t ht hβt
    have ht0 : 0 ≤ t := by linarith
    have hts : t = s :=
      hβinj ht0 hs (hβt.trans hβs.symm)
    linarith
  · refine ⟨0, le_rfl, ?_⟩
    intro t ht hβt
    exact hp ⟨t, ht, hβt⟩

/-- An injective positive-time orbit cannot have two distinct cluster points
on one short affine transversal on which the vector field crosses
positively. -/
theorem no_two_ordered_section_cluster_points
    {G : Plane → Plane} (β : ℝ → Plane)
    (hβ : IsIntegralCurve β (fun _ y ↦ G y))
    (hβinj : InjOn β (Ici (0 : ℝ)))
    {v base : Plane} (hv : v ≠ 0)
    (hvbase : v = G base)
    {L Q m U R : ℝ}
    (hLQ : L < Q) (hQm : Q < m)
    (hmU : m < U) (hUR : U < R)
    (hpositive : ∀ u ∈ Icc L R,
      0 <
        Transversal.transverseFunctional v
          (G (Transversal.sectionPoint v base u)))
    {σQ σU : ℕ → ℝ}
    (hσQ : Tendsto σQ atTop atTop)
    (hβQ :
      Tendsto (β ∘ σQ) atTop
        (𝓝 (Transversal.sectionPoint v base Q)))
    (hhitQ : ∀ n,
      Transversal.transverseValue v base (β (σQ n)) = 0)
    (hσU : Tendsto σU atTop atTop)
    (hβU :
      Tendsto (β ∘ σU) atTop
        (𝓝 (Transversal.sectionPoint v base U)))
    (hhitU : ∀ n,
      Transversal.transverseValue v base (β (σU n)) = 0) :
    False := by
  subst v
  let v : Plane := G base
  obtain ⟨TQ, hTQ, hneQ⟩ :=
    exists_eventually_ne_of_injOn_Ici β hβinj
      (Transversal.sectionPoint v base Q)
  obtain ⟨TU, hTU, hneU⟩ :=
    exists_eventually_ne_of_injOn_Ici β hβinj
      (Transversal.sectionPoint v base U)
  let T := max TQ TU
  have hT : 0 ≤ T := by
    exact hTQ.trans (le_max_left _ _)
  obtain ⟨a, b, qa, qb, hTa, hab, hqa, hqam,
      hqb, hmqb, hβa, hβb⟩ :=
    ConsecutiveHits.exists_ordered_hits_of_two_limits
      β hv hLQ hQm hmU hUR hσQ hβQ hhitQ
        hσU hβU hhitU (T := T)
  obtain ⟨s, t, A, B, has, hst, htb, hA, hB,
      hAm, hmB, hβs, hβt, hconsecutive⟩ :=
    ConsecutiveHits.exists_consecutive_hits_straddling
      β hβ hv (hLm := hLQ.trans hQm)
      (hmR := hmU.trans hUR) hab hqa hqam hqb hmqb
      hβa hβb hpositive
  have hAB : A < B := hAm.trans_le hmB
  have hpositiveAB :
      ∀ u ∈ Icc A B,
        0 <
          Transversal.transverseFunctional v
            (G (Transversal.sectionPoint v base u)) := by
    intro u hu
    exact hpositive u
      ⟨hA.1.trans hu.1, hu.2.trans hB.2⟩
  have ha0 : 0 ≤ a := hT.trans hTa.le
  have hs0 : 0 ≤ s := ha0.trans has
  have ht0 : 0 ≤ t := hs0.trans hst.le
  have hβinjST : InjOn β (Icc s t) := by
    intro x hx y hy hxy
    exact hβinj (hs0.trans hx.1) (hs0.trans hy.1) hxy
  let O : Set Plane := β '' Icc s t
  have hOcompact : IsCompact O :=
    isCompact_Icc.image hβ.continuous
  have hOne : O.Nonempty :=
    ⟨β s, ⟨s, left_mem_Icc.mpr hst.le, rfl⟩⟩
  have hLR : L < R := hLQ.trans (hQm.trans (hmU.trans hUR))
  have hAFull :
      Transversal.sectionPoint v base A ∈
        [Transversal.sectionPoint v base L -[ℝ]
          Transversal.sectionPoint v base R] :=
    Transversal.sectionPoint_mem_segment hLR hA
  have hBFull :
      Transversal.sectionPoint v base B ∈
        [Transversal.sectionPoint v base L -[ℝ]
          Transversal.sectionPoint v base R] :=
    Transversal.sectionPoint_mem_segment hLR hB
  have hsmallSegment :
      [Transversal.sectionPoint v base A -[ℝ]
          Transversal.sectionPoint v base B] ⊆
        [Transversal.sectionPoint v base L -[ℝ]
          Transversal.sectionPoint v base R] :=
    (convex_segment (𝕜 := ℝ)
      (Transversal.sectionPoint v base L)
      (Transversal.sectionPoint v base R)).segment_subset
        hAFull hBFull
  have hinter :
      O ∩ [β t -[ℝ] β s] ⊆ {β s, β t} := by
    rintro z ⟨⟨u, hu, rfl⟩, huz⟩
    have huSmall :
        β u ∈
          [Transversal.sectionPoint v base L -[ℝ]
            Transversal.sectionPoint v base R] := by
      apply hsmallSegment
      rw [hβt, hβs] at huz
      simpa only [v, segment_symm] using huz
    rcases hconsecutive u hu huSmall with rfl | rfl
    · exact mem_insert _ _
    · exact mem_insert_of_mem _ (mem_singleton _)
  let loop := OrbitArc.closingLoop β hst hβ.continuous.continuousOn
  have hloopInj : Injective loop :=
    OrbitArc.injective_closingLoop β hst
      hβ.continuous.continuousOn hβinjST hinter
  have hrange :
      range loop =
        O ∪
          [Transversal.sectionPoint v base A -[ℝ]
            Transversal.sectionPoint v base B] := by
    rw [OrbitArc.range_closingLoop]
    rw [hβt, hβs, segment_symm]
  have hOcoordinate :
      ∀ u ∈ Icc L R,
        Transversal.sectionPoint v base u ∈ O →
          u = A ∨ u = B := by
    intro u hu huO
    obtain ⟨w, hw, hβw⟩ := huO
    have huFull :
        β w ∈
          [Transversal.sectionPoint v base L -[ℝ]
            Transversal.sectionPoint v base R] := by
      rw [hβw]
      exact
        Transversal.sectionPoint_mem_segment hLR hu
    rcases hconsecutive w hw huFull with hws | hwt
    · left
      apply Transversal.sectionPoint_injective hv
      rw [← hβs, ← hws]
      exact hβw.symm
    · right
      apply Transversal.sectionPoint_injective hv
      rw [← hβt, ← hwt]
      exact hβw.symm
  have hOline :
      ∀ u ∈ Icc Q U,
        Transversal.sectionPoint v base u ∈ O →
          u = A ∨ u = B := by
    intro u hu
    exact hOcoordinate u
      ⟨hLQ.le.trans hu.1, hu.2.trans hUR.le⟩
  have hOdisj :
      ∀ u ∈ Ioo A B,
        Transversal.sectionPoint v base u ∉ O := by
    intro u hu huO
    rcases hOcoordinate u
        ⟨hA.1.trans hu.1.le, hu.2.le.trans hB.2⟩ huO with
      rfl | rfl <;> linarith [hu.1, hu.2]
  let D := t - s
  let α : ℝ → Plane := fun u ↦ β (s + u)
  have hD : 0 < D := sub_pos.mpr hst
  have hα : IsIntegralCurve α (fun _ y ↦ G y) := by
    simpa only [α, Function.comp_def, add_comm] using hβ.comp_add s
  have hαinj : InjOn α (Icc (0 : ℝ) D) := by
    intro x hx y hy hxy
    have hsx : s + x ∈ Icc s t := by
      constructor
      · linarith [hx.1]
      · dsimp only [D] at hx
        linarith [hx.2]
    have hsy : s + y ∈ Icc s t := by
      constructor
      · linarith [hy.1]
      · dsimp only [D] at hy
        linarith [hy.2]
    have := hβinjST hsx hsy hxy
    linarith
  have hα0 : α 0 = Transversal.sectionPoint v base A := by
    simpa only [α, add_zero] using hβs
  have hαD : α D = Transversal.sectionPoint v base B := by
    change
      β (s + (t - s)) =
        Transversal.sectionPoint v base B
    rw [show s + (t - s) = t by ring]
    simpa only [v] using hβt
  have hαzero :
      Transversal.transverseValue v base (α 0) = 0 := by
    rw [hα0]
    exact Transversal.transverseValue_sectionPoint hv A
  have hαDzero :
      Transversal.transverseValue v base (α D) = 0 := by
    rw [hαD]
    exact Transversal.transverseValue_sectionPoint hv B
  have hderiv0 :
      0 <
        deriv (fun u ↦
          Transversal.transverseValue v base (α u)) 0 := by
    rw [(Transversal.hasDerivAt_transverseValue hα v base 0).deriv,
      hα0]
    exact hpositive A hA
  have hderivD :
      0 <
        deriv (fun u ↦
          Transversal.transverseValue v base (α u)) D := by
    rw [(Transversal.hasDerivAt_transverseValue hα v base D).deriv,
      hαD]
    exact hpositive B hB
  obtain ⟨RA, hRA, hstartα⟩ :=
    EndpointBridge.exists_start_ball_orbitArc_nonneg
      α hα.continuous hD hαinj hαzero hderiv0
  obtain ⟨RB, hRB, hendα⟩ :=
    EndpointBridge.exists_end_ball_orbitArc_nonpos
      α hα.continuous hD hαinj hαDzero hderivD
  have hOα : O = α '' Icc (0 : ℝ) D := by
    apply Subset.antisymm
    · rintro z ⟨u, hu, rfl⟩
      refine ⟨u - s, ?_, ?_⟩
      · dsimp only [D]
        constructor <;> linarith [hu.1, hu.2]
      · dsimp only [α]
        rw [show s + (u - s) = u by ring]
    · rintro z ⟨u, hu, rfl⟩
      refine ⟨s + u, ?_, rfl⟩
      dsimp only [D] at hu
      constructor <;> linarith [hu.1, hu.2]
  have hstart :
      ∀ z ∈ O,
        z ∈ ball (Transversal.sectionPoint v base A) RA →
          0 ≤ Transversal.transverseValue v base z := by
    intro z hzO hzBall
    have hz :=
      hstartα z (by simpa only [← hOα] using hzO)
        (by simpa only [hα0] using hzBall)
    exact hz.1
  have hend :
      ∀ z ∈ O,
        z ∈ ball (Transversal.sectionPoint v base B) RB →
          Transversal.transverseValue v base z ≤ 0 := by
    intro z hzO hzBall
    have hz :=
      hendα z (by simpa only [← hOα] using hzO)
        (by simpa only [hαD] using hzBall)
    exact hz.1
  have hfutureAvoidO {c d : ℝ} (htc : t < c) :
      ∀ u ∈ Icc c d, β u ∉ O := by
    intro u hu
    rintro ⟨w, hw, hwu⟩
    have huw : u = w :=
      hβinj (hs0.trans (hst.le.trans (htc.le.trans hu.1)))
        (hs0.trans hw.1) hwu.symm
    linarith [hu.1, hw.2]
  have hfutureAvoidEndpoints {c d : ℝ} (htc : t < c) :
      ∀ u ∈ Icc c d,
        β u ≠ Transversal.sectionPoint v base A ∧
        β u ≠ Transversal.sectionPoint v base B := by
    intro u hu
    constructor
    · intro huA
      have hus : u = s :=
        hβinj
          (hs0.trans (hst.le.trans (htc.le.trans hu.1)))
          hs0 (huA.trans hβs.symm)
      exact (hst.trans (htc.trans_le hu.1)).ne hus.symm
    · intro huB
      have hut : u = t :=
        hβinj
          (hs0.trans (hst.le.trans (htc.le.trans hu.1)))
          ht0 (huB.trans hβt.symm)
      exact (htc.trans_le hu.1).ne hut.symm
  have hfutureInj {c d : ℝ} (hc0 : 0 ≤ c) :
      InjOn β (Icc c d) := by
    intro x hx y hy hxy
    exact hβinj (hc0.trans hx.1) (hc0.trans hy.1) hxy
  have noInterior
      {P : ℝ} (hP : P ∈ Ioo A B)
      {σ : ℕ → ℝ} (hσ : Tendsto σ atTop atTop)
      (hβP :
        Tendsto (β ∘ σ) atTop
          (𝓝 (Transversal.sectionPoint v base P)))
      (hhit : ∀ n,
        Transversal.transverseValue v base (β (σ n)) = 0) :
      False := by
    let u : ℕ → ℝ :=
      fun n ↦ Transversal.sectionValue v base (β (σ n))
    have hu : Tendsto u atTop (𝓝 P) := by
      have h :=
        (Transversal.continuous_sectionValue v base).tendsto
          (Transversal.sectionPoint v base P)
          |>.comp hβP
      simpa only [u, Function.comp_def, v,
        Transversal.sectionValue_sectionPoint hv] using h
    have hwindow : ∀ᶠ n in atTop, u n ∈ Ioo A B :=
      hu.eventually (Ioo_mem_nhds hP.1 hP.2)
    have hlate : ∀ᶠ n in atTop, t < σ n :=
      hσ.eventually (eventually_gt_atTop t)
    obtain ⟨n, hnWindow, hnLate⟩ :=
      (hwindow.and hlate).exists
    have hlater : ∀ᶠ k in atTop, σ n < σ k :=
      hσ.eventually (eventually_gt_atTop (σ n))
    obtain ⟨k, hkWindow, hnk⟩ :=
      (hwindow.and hlater).exists
    have hβn :
        β (σ n) = Transversal.sectionPoint v base (u n) :=
      (Transversal.sectionPoint_sectionValue hv (hhit n)).symm
    have hβk :
        β (σ k) = Transversal.sectionPoint v base (u k) :=
      (Transversal.sectionPoint_sectionValue hv (hhit k)).symm
    exact
      ReturnCrossing.no_two_positive_crossings
        β hβ loop hloopInj O hv
        hAB hOcompact.isClosed hOne
        hOdisj
        hrange hpositiveAB hnk hnWindow hβn
        (by
          rw [hβk, hrange]
          exact Or.inr
            (Transversal.sectionPoint_mem_segment hAB
              ⟨hkWindow.1.le, hkWindow.2.le⟩))
        (hfutureAvoidO hnLate)
        (fun u hu ↦
          hfutureAvoidEndpoints hnLate u ⟨hu.1.le, hu.2⟩)
        (hfutureInj
          (ht0.trans hnLate.le))
  by_cases hAQ : A < Q
  · exact noInterior ⟨hAQ, hQm.trans_le hmB⟩ hσQ hβQ hhitQ
  · have hQA' : Q < A := by
      have hQneA : Q ≠ A := by
        intro hQAeq
        apply hneQ s (by
          exact (le_max_left TQ TU).trans
            (hTa.le.trans has))
        simpa only [hQAeq] using hβs
      exact lt_of_le_of_ne (not_lt.mp hAQ) hQneA
    by_cases hUB : U < B
    · exact noInterior ⟨hAm.trans hmU, hUB⟩
        hσU hβU hhitU
    · have hBU' : B < U := by
        have hBneU : B ≠ U := by
          intro hBUeq
          apply hneU t (by
            exact (le_max_right TQ TU).trans
              (hTa.le.trans (has.trans hst.le)))
          simpa only [hBUeq] using hβt
        exact lt_of_le_of_ne (not_lt.mp hUB) hBneU
      have houtsideNe
          {q u : ℝ} (hq : q ∈ Ioo L A)
          (hu : u ∈ Ioo B R) :
          connectedComponentIn (range loop)ᶜ
              (Transversal.sectionPoint v base q) ≠
            connectedComponentIn (range loop)ᶜ
              (Transversal.sectionPoint v base u) := by
        apply
          ExteriorComponents.components_ne_of_outside_closing_segment
            loop hloopInj O hv hq.2 hAB hu.1
              hOcompact.isClosed hOne
        · intro w hw hwO
          exact hOcoordinate w
            ⟨hq.1.le.trans hw.1, hw.2.trans hu.2.le⟩ hwO
        · exact hrange
        · exact hRA
        · exact hRB
        · exact hstart
        · exact hend
      let uq : ℕ → ℝ :=
        fun n ↦ Transversal.sectionValue v base (β (σQ n))
      let uu : ℕ → ℝ :=
        fun n ↦ Transversal.sectionValue v base (β (σU n))
      have huq : Tendsto uq atTop (𝓝 Q) := by
        have h :=
          (Transversal.continuous_sectionValue v base).tendsto
            (Transversal.sectionPoint v base Q)
            |>.comp hβQ
        simpa only [uq, Function.comp_def, v,
          Transversal.sectionValue_sectionPoint hv] using h
      have huu : Tendsto uu atTop (𝓝 U) := by
        have h :=
          (Transversal.continuous_sectionValue v base).tendsto
            (Transversal.sectionPoint v base U)
            |>.comp hβU
        simpa only [uu, Function.comp_def, v,
          Transversal.sectionValue_sectionPoint hv] using h
      have hqWindow : ∀ᶠ n in atTop, uq n ∈ Ioo L A :=
        huq.eventually (Ioo_mem_nhds hLQ hQA')
      have huWindow : ∀ᶠ n in atTop, uu n ∈ Ioo B R :=
        huu.eventually (Ioo_mem_nhds hBU' hUR)
      have hqLate : ∀ᶠ n in atTop, t < σQ n :=
        hσQ.eventually (eventually_gt_atTop t)
      obtain ⟨n, hnQ, hnLate⟩ :=
        (hqWindow.and hqLate).exists
      have huLate : ∀ᶠ k in atTop, σQ n < σU k :=
        hσU.eventually (eventually_gt_atTop (σQ n))
      obtain ⟨k, hkU, hnk⟩ :=
        (huWindow.and huLate).exists
      have hqLater : ∀ᶠ l in atTop, σU k < σQ l :=
        hσQ.eventually (eventually_gt_atTop (σU k))
      obtain ⟨l, hlQ, hkl⟩ :=
        (hqWindow.and hqLater).exists
      have hβn :
          β (σQ n) = Transversal.sectionPoint v base (uq n) :=
        (Transversal.sectionPoint_sectionValue hv (hhitQ n)).symm
      have hβk :
          β (σU k) = Transversal.sectionPoint v base (uu k) :=
        (Transversal.sectionPoint_sectionValue hv (hhitU k)).symm
      have hβl :
          β (σQ l) = Transversal.sectionPoint v base (uq l) :=
        (Transversal.sectionPoint_sectionValue hv (hhitQ l)).symm
      have hpointCompl {w : ℝ} (hw : w ∈ Ioo L A) :
          Transversal.sectionPoint v base w ∈ (range loop)ᶜ := by
        apply
          EndpointBridge.sectionPoint_mem_compl_of_outside
            loop O hv hAB (Or.inl hw.2) _ hrange
        intro hwO
        rcases hOcoordinate w
            ⟨hw.1.le, hw.2.le.trans hA.2⟩ hwO with
          rfl | rfl <;> linarith [hw.2]
      have hpointComplRight {w : ℝ} (hw : w ∈ Ioo B R) :
          Transversal.sectionPoint v base w ∈ (range loop)ᶜ := by
        apply
          EndpointBridge.sectionPoint_mem_compl_of_outside
            loop O hv hAB (Or.inr hw.1) _ hrange
        intro hwO
        rcases hOcoordinate w
            ⟨hB.1.trans hw.1.le, hw.2.le⟩ hwO with
          rfl | rfl <;> linarith [hw.1]
      exact
        EndpointBridge.no_alternating_complement_components
          β hβ loop hloopInj O hv hAB hOcompact.isClosed hOne
          hOdisj
          hrange hpositiveAB hnk hkl
          (by simpa only [hβn] using hpointCompl hnQ)
          (by simpa only [hβk] using hpointComplRight hkU)
          (by simpa only [hβl] using hpointCompl hlQ)
          (by
            simpa only [hβn, hβk] using houtsideNe hnQ hkU)
          (by
            intro heq
            exact
              (houtsideNe hlQ hkU)
                (by simpa only [hβl, hβk] using heq.symm))
          (hfutureAvoidO hnLate)
          (hfutureAvoidEndpoints hnLate)
          (hfutureInj
            (ht0.trans hnLate.le))

end

end Submission.SectionOrder
