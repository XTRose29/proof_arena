import Submission.LocalSides

open Filter Function Metric Set Topology
open scoped Convex

open LeanEval.Dynamics

namespace Submission.ReturnCrossing

noncomputable section

/-- Once a future path crosses the open part of a Jordan closing segment in
the positive flow direction, it cannot cross that open segment a second
time in the same direction. -/
theorem no_two_positive_crossings
    {G : Plane → Plane} (β : ℝ → Plane)
    (hβ : IsIntegralCurve β (fun _ y ↦ G y))
    (r : C(Circle, Plane)) (hinj : Injective r)
    (O : Set Plane) {base : Plane} (hbase : G base ≠ 0)
    {A B : ℝ} (hAB : A < B)
    (hOclosed : IsClosed O) (hOne : O.Nonempty)
    (hOdisj : ∀ u ∈ Ioo A B,
      Transversal.sectionPoint (G base) base u ∉ O)
    (hrange :
      range r =
        O ∪
          [Transversal.sectionPoint (G base) base A -[ℝ]
            Transversal.sectionPoint (G base) base B])
    (hpositive : ∀ u ∈ Icc A B,
      0 <
        Transversal.transverseFunctional (G base)
          (G (Transversal.sectionPoint (G base) base u)))
    {c d C : ℝ} (hcd : c < d) (hC : C ∈ Ioo A B)
    (hβc : β c = Transversal.sectionPoint (G base) base C)
    (hβd : β d ∈ range r)
    (havoidO : ∀ t ∈ Icc c d, β t ∉ O)
    (havoidEndpoints : ∀ t ∈ Ioc c d,
      β t ≠ Transversal.sectionPoint (G base) base A ∧
      β t ≠ Transversal.sectionPoint (G base) base B)
    (hβinj : InjOn β (Icc c d)) :
    False := by
  let v := G base
  let pC := Transversal.sectionPoint v base C
  let f : ℝ → ℝ :=
    fun t ↦ Transversal.transverseValue v base (β t)
  have hv : v ≠ 0 := hbase
  have hCO : pC ∉ O := hOdisj C hC
  obtain ⟨RC, hRC, hlocalC⟩ :=
    LocalSides.exists_ball_union_segment_iff_transverseValue_eq_zero
      hv hC.1 hC.2 hOclosed hCO
  have hlocalC' :
      ∀ z ∈ ball pC RC,
        (z ∈ range r ↔
          Transversal.transverseFunctional v (z - pC) = 0) := by
    intro z hz
    rw [hrange]
    rw [Transversal.transverseValue_recenter_sectionPoint hv]
    exact hlocalC z hz
  have hfc : f c = 0 := by
    simp only [f, hβc]
    exact Transversal.transverseValue_sectionPoint hv C
  have hfderivC :
      HasDerivAt f
        (Transversal.transverseFunctional v (G (β c))) c := by
    exact Transversal.hasDerivAt_transverseValue hβ v base c
  have hderivC : 0 < deriv f c := by
    rw [hfderivC.deriv, hβc]
    exact hpositive C ⟨hC.1.le, hC.2.le⟩
  have hsignC :=
    eventually_nhdsWithin_sign_eq_of_deriv_pos hderivC hfc
  have hposC : ∀ᶠ t in 𝓝[>] c, 0 < f t := by
    filter_upwards
      [hsignC.filter_mono inf_le_left, self_mem_nhdsWithin]
      with t htSign ht
    apply sign_eq_one_iff.mp
    exact htSign.trans (sign_pos (sub_pos.mpr ht))
  have hballC : ∀ᶠ t in 𝓝 c, β t ∈ ball pC RC := by
    have : ball pC RC ∈ 𝓝 (β c) := by
      rw [hβc]
      exact ball_mem_nhds _ hRC
    exact hβ.continuous.continuousAt.eventually this
  have hchooseC :
      ∀ᶠ t in 𝓝[>] c,
        0 < f t ∧ β t ∈ ball pC RC ∧ t ∈ Ioo c d := by
    filter_upwards
      [hposC, hballC.filter_mono inf_le_left,
        Ioo_mem_nhdsGT hcd]
      with t htPos htBall htIoo
    exact ⟨htPos, htBall, htIoo⟩
  obtain ⟨c₀, hc₀Pos, hc₀Ball, hc₀⟩ :=
    hchooseC.exists
  have hc₀Compl : β c₀ ∈ (range r)ᶜ := by
    intro hc₀Range
    have hzero :=
      (hlocalC' (β c₀) hc₀Ball).mp hc₀Range
    rw [Transversal.transverseValue_recenter_sectionPoint hv] at hzero
    exact hc₀Pos.ne' hzero
  let H : Set ℝ := Icc c₀ d ∩ β ⁻¹' range r
  have hHcompact : IsCompact H := by
    exact
      isCompact_Icc.inter_right
        ((isCompact_range r.continuous).isClosed.preimage
          hβ.continuous)
  have hHne : H.Nonempty := by
    exact ⟨d, ⟨hc₀.2.le, le_rfl⟩, hβd⟩
  obtain ⟨e, heH, heMin⟩ :=
    hHcompact.exists_isMinOn hHne continuous_id.continuousOn
  have hc₀e : c₀ < e := by
    have hle : c₀ ≤ e := heH.1.1
    exact lt_of_le_of_ne hle fun heq ↦
      hc₀Compl (heq ▸ heH.2)
  have hed : e ≤ d := heH.1.2
  have hce : c < e := hc₀.1.trans hc₀e
  have hecd : e ∈ Ioc c d := ⟨hce, hed⟩
  have heO : β e ∉ O :=
    havoidO e ⟨hce.le, hed⟩
  have heSegment :
      β e ∈
        [Transversal.sectionPoint v base A -[ℝ]
          Transversal.sectionPoint v base B] := by
    have heRange : β e ∈ range r := heH.2
    rw [hrange] at heRange
    exact heRange.resolve_left heO
  obtain ⟨E, hE, hβe⟩ :=
    Transversal.exists_eq_sectionPoint_of_mem_segment
      hAB heSegment
  have hEA : E ≠ A := by
    intro h
    exact (havoidEndpoints e hecd).1 (by simpa [h, v] using hβe)
  have hEB : E ≠ B := by
    intro h
    exact (havoidEndpoints e hecd).2 (by simpa [h, v] using hβe)
  have hEopen : E ∈ Ioo A B :=
    ⟨hE.1.lt_of_ne hEA.symm, hE.2.lt_of_ne hEB⟩
  have hEC : E ≠ C := by
    intro h
    have hβec : β e = β c := by
      rw [hβe, h, hβc]
    have heq :=
      hβinj ⟨hce.le, hed⟩ ⟨le_rfl, hcd.le⟩ hβec
    exact hce.ne' heq
  let pE := Transversal.sectionPoint v base E
  have hEO : pE ∉ O := hOdisj E hEopen
  obtain ⟨RE, hRE, hlocalE⟩ :=
    LocalSides.exists_ball_union_segment_iff_transverseValue_eq_zero
      hv hEopen.1 hEopen.2 hOclosed hEO
  have hlocalE' :
      ∀ z ∈ ball pE RE,
        (z ∈ range r ↔
          Transversal.transverseFunctional v (z - pE) = 0) := by
    intro z hz
    rw [hrange]
    rw [Transversal.transverseValue_recenter_sectionPoint hv]
    exact hlocalE z hz
  have hfe : f e = 0 := by
    simp only [f, hβe]
    exact Transversal.transverseValue_sectionPoint hv E
  have hfderivE :
      HasDerivAt f
        (Transversal.transverseFunctional v (G (β e))) e := by
    exact Transversal.hasDerivAt_transverseValue hβ v base e
  have hderivE : 0 < deriv f e := by
    rw [hfderivE.deriv, hβe]
    exact hpositive E ⟨hEopen.1.le, hEopen.2.le⟩
  have hsignE :=
    eventually_nhdsWithin_sign_eq_of_deriv_pos hderivE hfe
  have hnegE : ∀ᶠ t in 𝓝[<] e, f t < 0 := by
    filter_upwards
      [hsignE.filter_mono inf_le_left, self_mem_nhdsWithin]
      with t htSign ht
    apply sign_eq_neg_one_iff.mp
    exact htSign.trans (sign_neg (sub_neg.mpr ht))
  have hballE : ∀ᶠ t in 𝓝 e, β t ∈ ball pE RE := by
    have : ball pE RE ∈ 𝓝 (β e) := by
      rw [hβe]
      exact ball_mem_nhds _ hRE
    exact hβ.continuous.continuousAt.eventually this
  have hchooseE :
      ∀ᶠ t in 𝓝[<] e,
        f t < 0 ∧ β t ∈ ball pE RE ∧ t ∈ Ioo c₀ e := by
    filter_upwards
      [hnegE, hballE.filter_mono inf_le_left,
        Ioo_mem_nhdsLT hc₀e]
      with t htNeg htBall htIoo
    exact ⟨htNeg, htBall, htIoo⟩
  obtain ⟨e₀, he₀Neg, he₀Ball, he₀⟩ :=
    hchooseE.exists
  have he₀Compl : β e₀ ∈ (range r)ᶜ := by
    intro he₀Range
    have hzero :=
      (hlocalE' (β e₀) he₀Ball).mp he₀Range
    rw [Transversal.transverseValue_recenter_sectionPoint hv] at hzero
    exact he₀Neg.ne hzero
  let S : Set Plane := β '' Icc c₀ e₀
  have hSpre : IsPreconnected S :=
    isPreconnected_Icc.image β hβ.continuous.continuousOn
  have hSsub : S ⊆ (range r)ᶜ := by
    rintro _ ⟨t, ht, rfl⟩ htRange
    have htH : t ∈ H := by
      refine ⟨⟨ht.1, ?_⟩, htRange⟩
      exact ht.2.trans (he₀.2.le.trans hed)
    have het : e ≤ t := heMin htH
    linarith [ht.2, he₀.2]
  have hsame :
      connectedComponentIn (range r)ᶜ (β c₀) =
        connectedComponentIn (range r)ᶜ (β e₀) := by
    apply connectedComponentIn_eq
    exact
      hSpre.subset_connectedComponentIn
        ⟨c₀, left_mem_Icc.mpr he₀.1.le, rfl⟩ hSsub
        ⟨e₀, right_mem_Icc.mpr he₀.1.le, rfl⟩
  have hrangeLine :
      range r ⊆ O ∪
        {z | Transversal.transverseValue v base z = 0} := by
    rw [hrange]
    apply union_subset_union_right
    intro z hz
    exact
      OrbitArc.transverseValue_segment_eq_zero
        (Transversal.transverseValue_sectionPoint hv A)
        (Transversal.transverseValue_sectionPoint hv B) hz
  have hc₀Pos' :
      0 <
        Transversal.transverseFunctional v (β c₀ - pC) := by
    rw [Transversal.transverseValue_recenter_sectionPoint hv]
    exact hc₀Pos
  have he₀Neg' :
      Transversal.transverseFunctional v (β e₀ - pE) < 0 := by
    rw [Transversal.transverseValue_recenter_sectionPoint hv]
    exact he₀Neg
  rcases lt_or_gt_of_ne hEC with hEC' | hCE'
  · have hne :=
      LocalSides.components_ne_of_opposite_side_along_segment_rev
        r hinj O hv hEC' hOclosed hOne
        (fun u hu ↦ hOdisj u ⟨hEopen.1.trans hu.1,
          hu.2.trans hC.2⟩)
        hrangeLine hRE hRC hlocalE' hlocalC'
        he₀Compl hc₀Compl he₀Ball hc₀Ball he₀Neg' hc₀Pos'
    exact hne hsame.symm
  · have hne :=
      LocalSides.components_ne_of_opposite_side_along_segment
        r hinj O hv hCE' hOclosed hOne
        (fun u hu ↦ hOdisj u ⟨hC.1.trans hu.1,
          hu.2.trans hEopen.2⟩)
        hrangeLine hRC hRE hlocalC' hlocalE'
        hc₀Compl he₀Compl hc₀Ball he₀Ball hc₀Pos' he₀Neg'
    exact hne hsame

end

end Submission.ReturnCrossing
