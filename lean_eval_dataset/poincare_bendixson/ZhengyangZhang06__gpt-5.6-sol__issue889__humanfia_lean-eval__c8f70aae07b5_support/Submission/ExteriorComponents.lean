import Submission.EndpointBridge

open Function Metric Set Topology
open scoped Convex

open LeanEval.Dynamics

namespace Submission.ExteriorComponents

noncomputable section

theorem offset_mem_ball_of_abs_bounds
    {v base : Plane} {u a c R : ℝ} (hR : 0 < R)
    (hc :
      |c| ≤ R / (4 * (‖v‖ + 1)))
    (hu :
      |u - a| ≤ R / (4 * (‖v‖ + 1))) :
    Transversal.sectionPoint v base u + c • v ∈
      ball (Transversal.sectionPoint v base a) R := by
  have hden : 0 < 4 * (‖v‖ + 1) := by positivity
  have hterm :
      R / (4 * (‖v‖ + 1)) * ‖v‖ < R / 4 := by
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hden).2
    nlinarith [norm_nonneg v]
  rw [mem_ball]
  calc
    dist
        (Transversal.sectionPoint v base u + c • v)
        (Transversal.sectionPoint v base a) ≤
        dist
            (Transversal.sectionPoint v base u + c • v)
            (Transversal.sectionPoint v base u) +
          dist
            (Transversal.sectionPoint v base u)
            (Transversal.sectionPoint v base a) :=
      dist_triangle _ _ _
    _ = |c| * ‖v‖ + ‖v‖ * |u - a| := by
      rw [Transversal.dist_offset_sectionPoint,
        Transversal.dist_sectionPoint]
    _ ≤
        R / (4 * (‖v‖ + 1)) * ‖v‖ +
          ‖v‖ * (R / (4 * (‖v‖ + 1))) := by
      gcongr
    _ < R := by
      rw [mul_comm ‖v‖]
      linarith

theorem offset_mem_ball_self_of_abs_bound
    {v base : Plane} {u c R : ℝ} (hR : 0 < R)
    (hc : |c| ≤ R / (2 * (‖v‖ + 1))) :
    Transversal.sectionPoint v base u + c • v ∈
      ball (Transversal.sectionPoint v base u) R := by
  rw [mem_ball, Transversal.dist_offset_sectionPoint]
  have hden : 0 < 2 * (‖v‖ + 1) := by positivity
  calc
    |c| * ‖v‖ ≤
        R / (2 * (‖v‖ + 1)) * ‖v‖ := by
      gcongr
    _ < R := by
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ hden).2
      nlinarith [norm_nonneg v]

/-- For a positive transverse orbit arc closed by its affine section
segment, section points just beyond the two segment endpoints belong to
different complementary components. -/
theorem components_ne_of_outside_closing_segment
    (r : C(Circle, Plane)) (hinj : Injective r)
    (O : Set Plane) {v base : Plane} (hv : v ≠ 0)
    {Q A B U : ℝ} (hQA : Q < A) (hAB : A < B) (hBU : B < U)
    (hOclosed : IsClosed O) (hOne : O.Nonempty)
    (hOline :
      ∀ u ∈ Icc Q U,
        Transversal.sectionPoint v base u ∈ O →
          u = A ∨ u = B)
    (hrange :
      range r =
        O ∪
          [Transversal.sectionPoint v base A -[ℝ]
            Transversal.sectionPoint v base B])
    {RA RB : ℝ} (hRA : 0 < RA) (hRB : 0 < RB)
    (hstart :
      ∀ z ∈ O,
        z ∈ ball (Transversal.sectionPoint v base A) RA →
          0 ≤ Transversal.transverseValue v base z)
    (hend :
      ∀ z ∈ O,
        z ∈ ball (Transversal.sectionPoint v base B) RB →
          Transversal.transverseValue v base z ≤ 0) :
    connectedComponentIn (range r)ᶜ
        (Transversal.sectionPoint v base Q) ≠
      connectedComponentIn (range r)ᶜ
        (Transversal.sectionPoint v base U) := by
  have hQU : Q < U := hQA.trans (hAB.trans hBU)
  have hnotO {u : ℝ} (hu : u ∈ Icc Q U)
      (huA : u ≠ A) (huB : u ≠ B) :
      Transversal.sectionPoint v base u ∉ O := by
    intro huO
    rcases hOline u hu huO with rfl | rfl
    · exact huA rfl
    · exact huB rfl
  have hrangeLine :
      range r ⊆
        O ∪ {z | Transversal.transverseValue v base z = 0} := by
    rw [hrange]
    apply union_subset_union_right
    intro z hz
    exact
      OrbitArc.transverseValue_segment_eq_zero
        (Transversal.transverseValue_sectionPoint hv A)
        (Transversal.transverseValue_sectionPoint hv B) hz
  let εA : ℝ :=
    min ((A - Q) / 4)
      (min ((B - A) / 8)
        (RA / (8 * (‖v‖ + 1))))
  let εB : ℝ :=
    min ((U - B) / 4)
      (min ((B - A) / 8)
        (RB / (8 * (‖v‖ + 1))))
  have hεA : 0 < εA := by
    dsimp only [εA]
    exact
      lt_min (by positivity)
        (lt_min (by positivity) (by positivity))
  have hεB : 0 < εB := by
    dsimp only [εB]
    exact
      lt_min (by positivity)
        (lt_min (by positivity) (by positivity))
  have hεAQ : εA < A - Q := by
    have hle : εA ≤ (A - Q) / 4 := min_le_left _ _
    linarith [hQA]
  have hεBU : εB < U - B := by
    have hle : εB ≤ (U - B) / 4 := min_le_left _ _
    linarith [hBU]
  have hεAgap : εA ≤ (B - A) / 8 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hεBgap : εB ≤ (B - A) / 8 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hεAradius :
      εA ≤ RA / (8 * (‖v‖ + 1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hεBradius :
      εB ≤ RB / (8 * (‖v‖ + 1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  let aL := A - εA
  let aR := A + εA
  let bL := B - εB
  let bR := B + εB
  have hQaL : Q < aL := by
    dsimp only [aL]
    linarith
  have haLA : aL < A := by
    dsimp only [aL]
    linarith
  have hAaR : A < aR := by
    dsimp only [aR]
    linarith
  have haRbL : aR < bL := by
    dsimp only [aR, bL]
    linarith [hAB]
  have hbLB : bL < B := by
    dsimp only [bL]
    linarith
  have hBbR : B < bR := by
    dsimp only [bR]
    linarith
  have hbRU : bR < U := by
    dsimp only [bR]
    linarith
  have haRBounds : aR ∈ Icc Q U :=
    ⟨hQaL.trans (haLA.trans hAaR) |>.le,
      haRbL.trans (hbLB.trans (hBU)) |>.le⟩
  have hbLBounds : bL ∈ Icc Q U :=
    ⟨hQA.trans (hAaR.trans haRbL) |>.le,
      hbLB.trans hBU |>.le⟩
  have haRO : Transversal.sectionPoint v base aR ∉ O :=
    hnotO haRBounds (by linarith) (by linarith)
  have hbLO : Transversal.sectionPoint v base bL ∉ O :=
    hnotO hbLBounds (by linarith) (by linarith)
  obtain ⟨rA, hrA, hlocalAraw⟩ :=
    LocalSides.exists_ball_union_segment_iff_transverseValue_eq_zero
      (a := A) (m := aR) (b := B)
      hv hAaR (haRbL.trans hbLB)
      hOclosed haRO
  obtain ⟨rB, hrB, hlocalBraw⟩ :=
    LocalSides.exists_ball_union_segment_iff_transverseValue_eq_zero
      (a := A) (m := bL) (b := B)
      hv (hAaR.trans haRbL) hbLB
      hOclosed hbLO
  have hlocalA :
      ∀ z ∈ ball (Transversal.sectionPoint v base aR) rA,
        (z ∈ range r ↔
          Transversal.transverseFunctional v
            (z - Transversal.sectionPoint v base aR) = 0) := by
    intro z hz
    rw [hrange]
    rw [Transversal.transverseValue_recenter_sectionPoint hv]
    exact hlocalAraw z hz
  have hlocalB :
      ∀ z ∈ ball (Transversal.sectionPoint v base bL) rB,
        (z ∈ range r ↔
          Transversal.transverseFunctional v
            (z - Transversal.sectionPoint v base bL) = 0) := by
    intro z hz
    rw [hrange]
    rw [Transversal.transverseValue_recenter_sectionPoint hv]
    exact hlocalBraw z hz
  let cA : ℝ :=
    min (RA / (8 * (‖v‖ + 1)))
      (rA / (2 * (‖v‖ + 1)))
  let cB : ℝ :=
    min (RB / (8 * (‖v‖ + 1)))
      (rB / (2 * (‖v‖ + 1)))
  have hcA : 0 < cA := by
    dsimp only [cA]
    exact lt_min (by positivity) (by positivity)
  have hcB : 0 < cB := by
    dsimp only [cB]
    exact lt_min (by positivity) (by positivity)
  have hcARA :
      cA ≤ RA / (8 * (‖v‖ + 1)) :=
    min_le_left _ _
  have hcBrB :
      cB ≤ RB / (8 * (‖v‖ + 1)) :=
    min_le_left _ _
  have hcArA :
      cA ≤ rA / (2 * (‖v‖ + 1)) :=
    min_le_right _ _
  have hcBrBlocal :
      cB ≤ rB / (2 * (‖v‖ + 1)) :=
    min_le_right _ _
  have hcornerA (u : ℝ) (hu : u ∈ Icc aL aR)
      (d : ℝ) (hd : d ∈ Icc (0 : ℝ) cA) :
      Transversal.sectionPoint v base u + (-d) • v ∈
        ball (Transversal.sectionPoint v base A) RA := by
    apply offset_mem_ball_of_abs_bounds hRA
    · rw [abs_neg, abs_of_nonneg hd.1]
      exact
        hd.2.trans hcARA |>.trans
          (by
            gcongr
            norm_num)
    · have huAbs : |u - A| ≤ εA := by
        rw [abs_le]
        constructor <;>
          dsimp only [aL, aR] at hu <;> linarith [hu.1, hu.2]
      exact
        huAbs.trans hεAradius |>.trans
          (by
            gcongr
            norm_num)
  have hcornerB (u : ℝ) (hu : u ∈ Icc bL bR)
      (d : ℝ) (hd : d ∈ Icc (0 : ℝ) cB) :
      Transversal.sectionPoint v base u + d • v ∈
        ball (Transversal.sectionPoint v base B) RB := by
    apply offset_mem_ball_of_abs_bounds hRB
    · rw [abs_of_nonneg hd.1]
      exact
        hd.2.trans hcBrB |>.trans
          (by
            gcongr
            norm_num)
    · have huAbs : |u - B| ≤ εB := by
        rw [abs_le]
        constructor <;>
          dsimp only [bL, bR] at hu <;> linarith [hu.1, hu.2]
      exact
        huAbs.trans hεBradius |>.trans
          (by
            gcongr
            norm_num)
  have hQaLO : Transversal.sectionPoint v base Q ∉ O :=
    hnotO ⟨le_rfl, hQU.le⟩ (by linarith) (by linarith)
  have haLO : Transversal.sectionPoint v base aL ∉ O :=
    hnotO
      ⟨hQaL.le, haLA.trans (hAB.trans hBU) |>.le⟩
      (by linarith) (by linarith)
  have hbRO : Transversal.sectionPoint v base bR ∉ O :=
    hnotO
      ⟨hQA.trans (hAB.trans hBbR) |>.le, hbRU.le⟩
      (by linarith) (by linarith)
  have hUO : Transversal.sectionPoint v base U ∉ O :=
    hnotO ⟨hQU.le, le_rfl⟩ (by linarith) (by linarith)
  have hQCompl :
      Transversal.sectionPoint v base Q ∈ (range r)ᶜ :=
    EndpointBridge.sectionPoint_mem_compl_of_outside
      r O hv hAB (Or.inl hQA) hQaLO hrange
  have haLCompl :
      Transversal.sectionPoint v base aL ∈ (range r)ᶜ :=
    EndpointBridge.sectionPoint_mem_compl_of_outside
      r O hv hAB (Or.inl haLA) haLO hrange
  have hbRCompl :
      Transversal.sectionPoint v base bR ∈ (range r)ᶜ :=
    EndpointBridge.sectionPoint_mem_compl_of_outside
      r O hv hAB (Or.inr hBbR) hbRO hrange
  have hUCompl :
      Transversal.sectionPoint v base U ∈ (range r)ᶜ :=
    EndpointBridge.sectionPoint_mem_compl_of_outside
      r O hv hAB (Or.inr hBU) hUO hrange
  let xA :=
    Transversal.sectionPoint v base aR + (-cA) • v
  let yB :=
    Transversal.sectionPoint v base bL + cB • v
  have hxABall :
      xA ∈ ball (Transversal.sectionPoint v base aR) rA := by
    apply offset_mem_ball_self_of_abs_bound hrA
    rw [abs_neg, abs_of_pos hcA]
    exact hcArA
  have hyBBall :
      yB ∈ ball (Transversal.sectionPoint v base bL) rB := by
    apply offset_mem_ball_self_of_abs_bound hrB
    rw [abs_of_pos hcB]
    exact hcBrBlocal
  have hxACompl : xA ∈ (range r)ᶜ := by
    intro hxRange
    rcases hrangeLine hxRange with hxO | hxLine
    · have hwrong :=
        hstart xA hxO
          (hcornerA aR
            (right_mem_Icc.mpr (by linarith [haLA, hAaR]))
            cA (right_mem_Icc.mpr hcA.le))
      dsimp only [xA] at hwrong
      rw [Transversal.transverseValue_offset_sectionPoint hv] at hwrong
      linarith
    · dsimp only [xA] at hxLine
      change
        Transversal.transverseValue v base
            (Transversal.sectionPoint v base aR + (-cA) • v) = 0
        at hxLine
      rw [Transversal.transverseValue_offset_sectionPoint hv] at hxLine
      linarith
  have hyBCompl : yB ∈ (range r)ᶜ := by
    intro hyRange
    rcases hrangeLine hyRange with hyO | hyLine
    · have hwrong :=
        hend yB hyO
          (hcornerB bL
            (left_mem_Icc.mpr (by linarith [hbLB, hBbR]))
            cB (right_mem_Icc.mpr hcB.le))
      dsimp only [yB] at hwrong
      rw [Transversal.transverseValue_offset_sectionPoint hv] at hwrong
      linarith
    · dsimp only [yB] at hyLine
      change
        Transversal.transverseValue v base
            (Transversal.sectionPoint v base bL + cB • v) = 0
        at hyLine
      rw [Transversal.transverseValue_offset_sectionPoint hv] at hyLine
      linarith
  have hxANeg :
      Transversal.transverseFunctional v
          (xA - Transversal.sectionPoint v base aR) < 0 := by
    rw [Transversal.transverseValue_recenter_sectionPoint hv]
    dsimp only [xA]
    rw [Transversal.transverseValue_offset_sectionPoint hv]
    linarith
  have hyBPos :
      0 <
        Transversal.transverseFunctional v
          (yB - Transversal.sectionPoint v base bL) := by
    rw [Transversal.transverseValue_recenter_sectionPoint hv]
    dsimp only [yB]
    rw [Transversal.transverseValue_offset_sectionPoint hv]
    exact hcB
  have hOdisjMid :
      ∀ u ∈ Ioo aR bL,
        Transversal.sectionPoint v base u ∉ O := by
    intro u hu
    apply hnotO
    · exact
        ⟨(hQA.trans (hAaR.trans hu.1)).le,
          (hu.2.trans (hbLB.trans hBU)).le⟩
    · exact ne_of_gt (hAaR.trans hu.1)
    · exact ne_of_lt (hu.2.trans hbLB)
  have hxyNe :
      connectedComponentIn (range r)ᶜ xA ≠
        connectedComponentIn (range r)ᶜ yB := by
    exact
      LocalSides.components_ne_of_opposite_side_along_segment_rev
        r hinj O hv haRbL hOclosed hOne hOdisjMid
        hrangeLine hrA hrB hlocalA hlocalB
        hxACompl hyBCompl hxABall hyBBall hxANeg hyBPos
  have hQaLComp :
      connectedComponentIn (range r)ᶜ
          (Transversal.sectionPoint v base Q) =
        connectedComponentIn (range r)ᶜ
          (Transversal.sectionPoint v base aL) := by
    apply
      EndpointBridge.component_eq_sectionPoints_of_interval_disjoint
        r O hv hQaL (Or.inl rfl) hOclosed hOne
        (fun u hu ↦ hnotO
          ⟨hu.1.le,
            (hu.2.trans (haLA.trans (hAB.trans hBU))).le⟩
          (ne_of_lt (hu.2.trans haLA))
          (ne_of_lt (hu.2.trans (haLA.trans hAB))))
        hrangeLine hQCompl haLCompl
  have haLxA :
      connectedComponentIn (range r)ᶜ
          (Transversal.sectionPoint v base aL) =
        connectedComponentIn (range r)ᶜ xA := by
    have hvertical :=
      EndpointBridge.component_eq_corner_vertical
        r O hv hcA (Or.inl rfl)
        (fun d hd ↦ by
          simpa only [neg_mul, one_mul] using
            hcornerA aL
              (left_mem_Icc.mpr (by linarith [haLA, hAaR])) d hd)
        (fun z hzO hzBall ↦ by
          simpa only [one_mul] using hstart z hzO hzBall)
        hrangeLine haLCompl
    have hbridge :=
      EndpointBridge.component_eq_across_endpoint_offset
        r O hv haLA hAaR hcA (Or.inl rfl)
        (fun u hu ↦ by
          simpa only [neg_mul, one_mul] using
            hcornerA u hu cA (right_mem_Icc.mpr hcA.le))
        (fun z hzO hzBall ↦ by
          simpa only [one_mul] using hstart z hzO hzBall)
        hrangeLine
    simpa only [xA, neg_mul, one_mul] using hvertical.trans hbridge
  have hyBbR :
      connectedComponentIn (range r)ᶜ yB =
        connectedComponentIn (range r)ᶜ
          (Transversal.sectionPoint v base bR) := by
    have hbridge :=
      EndpointBridge.component_eq_across_endpoint_offset
        r O hv hbLB hBbR hcB (Or.inr rfl)
        (fun u hu ↦ by
          simpa only [neg_neg, one_mul] using
            hcornerB u hu cB (right_mem_Icc.mpr hcB.le))
        (fun z hzO hzBall ↦ by
          have := hend z hzO hzBall
          linarith)
        hrangeLine
    have hvertical :=
      EndpointBridge.component_eq_corner_vertical
        r O hv hcB (Or.inr rfl)
        (fun d hd ↦ by
          simpa only [neg_neg, one_mul] using
            hcornerB bR
              (right_mem_Icc.mpr (by linarith [hbLB, hBbR])) d hd)
        (fun z hzO hzBall ↦ by
          have := hend z hzO hzBall
          linarith)
        hrangeLine hbRCompl
    simpa only [yB, neg_neg, one_mul] using
      hbridge.trans hvertical.symm
  have hbRUComp :
      connectedComponentIn (range r)ᶜ
          (Transversal.sectionPoint v base bR) =
        connectedComponentIn (range r)ᶜ
          (Transversal.sectionPoint v base U) := by
    apply
      EndpointBridge.component_eq_sectionPoints_of_interval_disjoint
        r O hv hbRU (Or.inl rfl) hOclosed hOne
        (fun u hu ↦ hnotO
          ⟨hQA.trans (hAB.trans (hBbR.trans hu.1)) |>.le,
            hu.2.le⟩
          (ne_of_gt (hAB.trans (hBbR.trans hu.1)))
          (ne_of_gt (hBbR.trans hu.1)))
        hrangeLine hbRCompl hUCompl
  intro hQUComp
  apply hxyNe
  exact
    haLxA.symm.trans
      (hQaLComp.symm.trans
        (hQUComp.trans
          (hbRUComp.symm.trans hyBbR.symm)))

end

end Submission.ExteriorComponents
