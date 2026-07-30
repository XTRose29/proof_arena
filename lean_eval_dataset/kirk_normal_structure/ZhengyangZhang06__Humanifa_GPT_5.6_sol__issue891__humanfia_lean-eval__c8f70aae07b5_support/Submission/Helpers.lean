import ChallengeDeps

open Bornology Set Topology
open Function
open LeanEval.Topology.KirkNormalStructure

namespace Submission.Helpers

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A bounded closed convex set in a reflexive real normed space is weakly compact. -/
lemma isCompact_toWeakSpace_image [CompleteSpace E]
    (hE_reflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E))
    (K : Set E) (hK_closed : IsClosed K) (hK_bounded : IsBounded K)
    (hK_convex : Convex ℝ K) :
    IsCompact (toWeakSpace ℝ E '' K) := by
  have hb : IsBounded ((toWeakSpace ℝ E) ⁻¹' (toWeakSpace ℝ E '' K)) := by
    rw [Set.preimage_image_eq K (toWeakSpace ℝ E).injective]
    exact hK_bounded
  have hrange :
      closure (NormedSpace.inclusionInDoubleDualWeak ℝ E '' (toWeakSpace ℝ E '' K)) ⊆
        Set.range (NormedSpace.inclusionInDoubleDualWeak ℝ E) := by
    intro z _
    obtain ⟨x, hx⟩ := hE_reflexive (WeakDual.toStrongDual z)
    refine ⟨toWeakSpace ℝ E x, ?_⟩
    apply WeakDual.toStrongDual.injective
    simpa [NormedSpace.inclusionInDoubleDualWeak] using hx
  have hcompact :=
    NormedSpace.isCompact_closure_of_isBounded ℝ E (toWeakSpace ℝ E '' K) hb hrange
  have hclosure : closure (toWeakSpace ℝ E '' K) = toWeakSpace ℝ E '' K := by
    rw [← hK_convex.toWeakSpace_closure ℝ, hK_closed.closure_eq]
  rwa [hclosure] at hcompact

omit [NormedSpace ℝ E] in
private lemma pairDistances_bddAbove {s : Set E} (hs : IsBounded s) :
    BddAbove {r : ℝ | ∃ x ∈ s, ∃ y ∈ s, dist x y = r} := by
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hs
  refine ⟨C, ?_⟩
  rintro r ⟨x, hx, y, hy, rfl⟩
  exact hC hx hy

omit [NormedSpace ℝ E] in
private lemma pointDistances_bddAbove {s : Set E} (hs : IsBounded s) {x : E}
    (hx : x ∈ s) : BddAbove {r : ℝ | ∃ y ∈ s, dist x y = r} := by
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hs
  refine ⟨C, ?_⟩
  rintro r ⟨y, hy, rfl⟩
  exact hC hx hy

omit [NormedSpace ℝ E] in
private lemma pairDistances_nonempty {s : Set E} (hs : s.Nonempty) :
    {r : ℝ | ∃ x ∈ s, ∃ y ∈ s, dist x y = r}.Nonempty := by
  obtain ⟨x, hx⟩ := hs
  exact ⟨0, x, hx, x, hx, dist_self x⟩

omit [NormedSpace ℝ E] in
private lemma pointDistances_nonempty {s : Set E} (hs : s.Nonempty) (x : E) :
    {r : ℝ | ∃ y ∈ s, dist x y = r}.Nonempty := by
  obtain ⟨y, hy⟩ := hs
  exact ⟨dist x y, y, hy, rfl⟩

omit [NormedSpace ℝ E] in
private lemma dist_le_pointRadiusIn {s : Set E} (hs : IsBounded s) {x y : E}
    (hx : x ∈ s) (hy : y ∈ s) : dist x y ≤ pointRadiusIn x s := by
  exact le_csSup (pointDistances_bddAbove hs hx) ⟨y, hy, rfl⟩

omit [NormedSpace ℝ E] in
private lemma pointRadiusIn_le_metricDiameter {s : Set E} (hs : IsBounded s)
    (hsn : s.Nonempty) {x : E} (hx : x ∈ s) :
    pointRadiusIn x s ≤ metricDiameter s := by
  apply csSup_le (pointDistances_nonempty hsn x)
  rintro r ⟨y, hy, hxy⟩
  exact le_csSup (pairDistances_bddAbove hs) ⟨x, hx, y, hy, hxy⟩

omit [NormedSpace ℝ E] in
private lemma metricDiameter_le_of_forall_dist_le {s : Set E} (hs : s.Nonempty) {r : ℝ}
    (h : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ r) : metricDiameter s ≤ r := by
  apply csSup_le (pairDistances_nonempty hs)
  rintro d ⟨x, hx, y, hy, rfl⟩
  exact h x hx y hy

/-- The closed convex subsets used in the minimal-invariant-set argument. -/
private def IsGoodSet (K : Set E) (T : K → K) (M : Set E) : Prop :=
  M ⊆ K ∧ M.Nonempty ∧ IsClosed M ∧ Convex ℝ M ∧
    ∀ x : K, x.1 ∈ M → (T x).1 ∈ M

/-- Kirk's normal-structure argument, factored out from the benchmark theorem. -/
theorem exists_fixedPoint_of_normalStructure [CompleteSpace E]
    (hE_reflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E))
    (K : Set E) (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K)
    (hK_bounded : IsBounded K) (hK_convex : Convex ℝ K)
    (hK_normal : HasNormalStructure K) (T : K → K)
    (hT : IsNonexpansiveSelfMap K T) :
    ∃ x : K, IsFixedPt T x := by
  classical
  have hK_good : IsGoodSet K T K := by
    exact ⟨Subset.rfl, hK_nonempty, hK_closed, hK_convex, fun x _ ↦ (T x).2⟩
  have chain_has_lower_bound :
      ∀ c ⊆ {M : Set E | IsGoodSet K T M}, IsChain (· ⊆ ·) c → c.Nonempty →
        ∃ lb ∈ {M : Set E | IsGoodSet K T M}, ∀ M ∈ c, lb ⊆ M := by
    intro c hc_good hc_chain hc_nonempty
    let L : Set E := ⋂₀ c
    obtain ⟨M₀, hM₀c⟩ := hc_nonempty
    have hL_nonempty : L.Nonempty := by
      let W : c → Set (WeakSpace ℝ E) := fun M ↦ toWeakSpace ℝ E '' (M.1 : Set E)
      letI : Nonempty c := ⟨⟨M₀, hM₀c⟩⟩
      have hW_directed : Directed (· ⊇ ·) W := by
        intro A B
        rcases hc_chain.total A.2 B.2 with hAB | hBA
        · exact ⟨A, Subset.rfl, image_mono hAB⟩
        · exact ⟨B, image_mono hBA, Subset.rfl⟩
      have hW_nonempty : ∀ A, (W A).Nonempty := by
        intro A
        exact (hc_good A.2).2.1.image _
      have hW_compact : ∀ A, IsCompact (W A) := by
        intro A
        rcases hc_good A.2 with ⟨hAK, _, hA_closed, hA_convex, _⟩
        exact isCompact_toWeakSpace_image hE_reflexive A.1 hA_closed
          (hK_bounded.subset hAK) hA_convex
      have hW_closed : ∀ A, IsClosed (W A) := fun A ↦ (hW_compact A).isClosed
      obtain ⟨w, hw⟩ :=
        IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed W hW_directed
          hW_nonempty hW_compact hW_closed
      refine ⟨(toWeakSpace ℝ E).symm w, ?_⟩
      rw [mem_sInter]
      intro A hAc
      have hwA := mem_iInter.mp hw ⟨A, hAc⟩
      obtain ⟨y, hyA, hyw⟩ := hwA
      have hy : y = (toWeakSpace ℝ E).symm w := by
        apply (toWeakSpace ℝ E).injective
        rw [hyw, (toWeakSpace ℝ E).apply_symm_apply]
      rwa [← hy]
    refine ⟨L, ?_, fun M hMc ↦ sInter_subset_of_mem hMc⟩
    have hLK : L ⊆ K := (sInter_subset_of_mem hM₀c).trans (hc_good hM₀c).1
    have hL_closed : IsClosed L :=
      isClosed_sInter fun M hMc ↦ (hc_good hMc).2.2.1
    have hL_convex : Convex ℝ L :=
      convex_sInter fun M hMc ↦ (hc_good hMc).2.2.2.1
    refine ⟨hLK, hL_nonempty, hL_closed, hL_convex, ?_⟩
    intro x hxL
    rw [mem_sInter] at hxL ⊢
    intro M hMc
    exact (hc_good hMc).2.2.2.2 x (hxL M hMc)
  obtain ⟨M, _, hM_min⟩ :=
    zorn_superset_nonempty {N : Set E | IsGoodSet K T N} chain_has_lower_bound K hK_good
  rcases hM_min.prop with ⟨hMK, hM_nonempty, hM_closed, hM_convex, hM_invariant⟩
  by_cases hM_nontrivial : M.Nontrivial
  · have hM_bounded : IsBounded M := hK_bounded.subset hMK
    let TM : Set E := Set.range fun y : M => (T ⟨y.1, hMK y.2⟩).1
    let H : Set E := closure (convexHull ℝ TM)
    have hTM_M : TM ⊆ M := by
      rintro _ ⟨y, rfl⟩
      exact hM_invariant ⟨y.1, hMK y.2⟩ y.2
    have hH_M : H ⊆ M := by
      exact closure_minimal (convexHull_min hTM_M hM_convex) hM_closed
    have hH_good : IsGoodSet K T H := by
      refine ⟨hH_M.trans hMK, ?_, isClosed_closure,
        (convex_convexHull ℝ TM).closure, ?_⟩
      · obtain ⟨y, hyM⟩ := hM_nonempty
        refine ⟨(T ⟨y, hMK hyM⟩).1, subset_closure ?_⟩
        apply subset_convexHull ℝ
        exact ⟨⟨y, hyM⟩, rfl⟩
      · intro x hxH
        apply subset_closure
        apply subset_convexHull ℝ
        refine ⟨⟨x.1, hH_M hxH⟩, ?_⟩
        congr
    have hM_eq_H : M = H := hM_min.eq_of_superset hH_good hH_M
    obtain ⟨x, hxM, hx_not_diametral⟩ :=
      hK_normal M hMK hM_convex hM_nontrivial
    have hx_radius_ne : pointRadiusIn x M ≠ metricDiameter M := by
      intro heq
      exact hx_not_diametral ⟨hxM, heq⟩
    have hx_radius_lt : pointRadiusIn x M < metricDiameter M :=
      lt_of_le_of_ne (pointRadiusIn_le_metricDiameter hM_bounded hM_nonempty hxM)
        hx_radius_ne
    obtain ⟨r, hx_radius_r, hr_diam⟩ := exists_between hx_radius_lt
    let C : Set E := {z | z ∈ M ∧ ∀ y ∈ M, dist z y ≤ r}
    have hxC : x ∈ C := by
      refine ⟨hxM, fun y hyM ↦ ?_⟩
      exact (dist_le_pointRadiusIn hM_bounded hxM hyM).trans hx_radius_r.le
    have hC_eq : C = M ∩ ⋂ y : M, Metric.closedBall y.1 r := by
      ext z
      simp [C, Metric.mem_closedBall]
    have hC_closed : IsClosed C := by
      rw [hC_eq]
      exact hM_closed.inter (isClosed_iInter fun _ ↦ Metric.isClosed_closedBall)
    have hC_convex : Convex ℝ C := by
      rw [hC_eq]
      exact hM_convex.inter (convex_iInter fun y ↦ convex_closedBall y.1 r)
    have hC_invariant : ∀ z : K, z.1 ∈ C → (T z).1 ∈ C := by
      intro z hzC
      refine ⟨hM_invariant z hzC.1, ?_⟩
      have hTM_ball : TM ⊆ Metric.closedBall (T z).1 r := by
        rintro _ ⟨w, rfl⟩
        rw [Metric.mem_closedBall, dist_comm]
        have hlip : dist (T z).1 (T ⟨w.1, hMK w.2⟩).1 ≤ dist z.1 w.1 := by
          simpa [Subtype.dist_eq] using hT.dist_le_mul z ⟨w.1, hMK w.2⟩
        exact hlip.trans (hzC.2 w.1 w.2)
      have hH_ball : H ⊆ Metric.closedBall (T z).1 r :=
        closure_minimal (convexHull_min hTM_ball (convex_closedBall (T z).1 r))
          Metric.isClosed_closedBall
      intro y hyM
      simpa [Metric.mem_closedBall, dist_comm] using hH_ball (hM_eq_H ▸ hyM)
    have hC_good : IsGoodSet K T C :=
      ⟨fun _ hz ↦ hMK hz.1, ⟨x, hxC⟩, hC_closed, hC_convex, hC_invariant⟩
    have hM_eq_C : M = C := hM_min.eq_of_superset hC_good (fun _ hz ↦ hz.1)
    have hdiam_le : metricDiameter M ≤ r := by
      apply metricDiameter_le_of_forall_dist_le hM_nonempty
      intro y hyM z hzM
      exact (hM_eq_C ▸ hyM).2 z hzM
    exact (not_lt_of_ge hdiam_le hr_diam).elim
  · have hM_subsingleton : M.Subsingleton := Set.not_nontrivial_iff.mp hM_nontrivial
    obtain ⟨x, hxM⟩ := hM_nonempty
    let xK : K := ⟨x, hMK hxM⟩
    refine ⟨xK, ?_⟩
    apply Subtype.ext
    exact hM_subsingleton (hM_invariant xK hxM) hxM

end

end Submission.Helpers
