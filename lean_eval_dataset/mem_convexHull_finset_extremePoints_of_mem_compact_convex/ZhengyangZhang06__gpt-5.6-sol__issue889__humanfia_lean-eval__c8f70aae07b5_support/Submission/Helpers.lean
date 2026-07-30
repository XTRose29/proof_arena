import Mathlib

namespace Submission.Helpers

open Set

lemma exists_supporting_functional_of_mem_intrinsicFrontier
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {C : Set E} {x : E} (hCconv : Convex ℝ C)
    (hx : x ∈ intrinsicFrontier ℝ C) :
    ∃ L : StrongDual ℝ E,
      (∃ v : (affineSpan ℝ C).direction, L v ≠ 0) ∧
      ∀ y ∈ closure C, L y ≤ L x := by
  classical
  obtain ⟨x', hxfront, rfl⟩ := mem_intrinsicFrontier.mp hx
  let A := affineSpan ℝ C
  letI : Nonempty A := ⟨x'⟩
  let e : A ≃ᵃⁱ[ℝ] A.direction := AffineIsometryEquiv.constVSub ℝ x'
  let eh : A ≃ₜ A.direction := e.toHomeomorph
  let g : A.direction →ᵃ[ℝ] E :=
    A.subtype.comp e.symm.toAffineEquiv.toAffineMap
  let C' : Set A := ((↑) : A → E) ⁻¹' C
  let D : Set A.direction := g ⁻¹' C
  have hD_eq : D = eh.symm ⁻¹' C' := rfl
  have hDconv : Convex ℝ D :=
    Convex.affine_preimage (𝕜 := ℝ) g hCconv
  have hCne : C.Nonempty :=
    (intrinsicClosure_nonempty (𝕜 := ℝ)).mp
      ⟨_, intrinsicFrontier_subset_intrinsicClosure hx⟩
  have hC'int : (interior C').Nonempty := by
    obtain ⟨z, hz⟩ := Set.Nonempty.intrinsicInterior hCconv hCne
    obtain ⟨z', hz', -⟩ := mem_intrinsicInterior.mp hz
    exact ⟨z', hz'⟩
  have hDint : (interior D).Nonempty := by
    obtain ⟨z, hz⟩ := hC'int
    refine ⟨eh z, ?_⟩
    rw [hD_eq, ← eh.symm.preimage_interior]
    simpa
  have hzero : (0 : A.direction) ∉ interior D := by
    intro hz
    have hz' : (0 : A.direction) ∈ eh.symm ⁻¹' interior C' := by
      rw [eh.symm.preimage_interior, ← hD_eq]
      exact hz
    have hx' : x' ∈ interior C' := by
      simpa [eh, e] using hz'
    exact (Set.disjoint_left.1 disjoint_interior_frontier) hx' hxfront
  obtain ⟨l, hlne, hl⟩ :=
    geometric_hahn_banach_of_nonempty_interior_point hDconv hzero hDint
  obtain ⟨L, hL⟩ := StrongDual.exists_extension A.direction l
  refine ⟨-L, ?_, ?_⟩
  · have hex : ∃ v : A.direction, l v ≠ 0 := by
      by_contra h
      push Not at h
      apply hlne
      ext v
      simpa using h v
    obtain ⟨v, hv⟩ := hex
    exact ⟨v, by simpa [hL v] using hv⟩
  · have hsubset : C ⊆ {y : E | (-L) y ≤ (-L) (x' : E)} := by
      intro y hy
      let y' : A := ⟨y, subset_affineSpan ℝ C hy⟩
      let v : A.direction := e y'
      have hvD : v ∈ D := by
        change ((e.symm v : A) : E) ∈ C
        rw [show e.symm v = y' by simp [v]]
        exact hy
      have hvle : L (x' - y) ≤ 0 := by
        have hvcoe : (v : E) = (x' : E) - y := by
          simp [v, e, y']
        calc
          L ((x' : E) - y) = L (v : E) := by rw [hvcoe]
          _ = l v := hL v
          _ ≤ 0 := by simpa using hl v hvD
      have hxy : L (x' : E) ≤ L y := by
        simpa only [map_sub, sub_nonpos] using hvle
      simpa using neg_le_neg hxy
    exact closure_minimal hsubset (isClosed_Iic.preimage (-L).continuous)

lemma mem_convexHull_extremePoints_of_compact_convex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} {x : E} (hscomp : IsCompact s) (hsconv : Convex ℝ s)
    (hx : x ∈ s) :
    x ∈ convexHull ℝ (s.extremePoints ℝ) := by
  classical
  let P := fun d : ℕ ↦
    ∀ (A : Set E),
      Module.finrank ℝ (affineSpan ℝ A).direction = d →
      ∀ z : E, IsCompact A → Convex ℝ A → z ∈ A →
        z ∈ convexHull ℝ (A.extremePoints ℝ)
  have hmain : ∀ d, P d := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro A hAdim z hAcomp hAconv hz
        let C := convexHull ℝ (A.extremePoints ℝ)
        have hCconv : Convex ℝ C := convex_convexHull ℝ _
        have hCclosure : closure C = A :=
          closure_convexHull_extremePoints hAcomp hAconv
        have hCsub : C ⊆ A := by
          rw [← hCclosure]
          exact subset_closure
        have hAsubspanC : A ⊆ (affineSpan ℝ C : Set E) := by
          rw [← hCclosure]
          exact closure_minimal (subset_affineSpan ℝ C)
            (affineSpan ℝ C).closed_of_finiteDimensional
        have hspan : affineSpan ℝ C = affineSpan ℝ A := by
          apply le_antisymm
          · exact affineSpan_mono ℝ hCsub
          · exact affineSpan_le.2 hAsubspanC
        have hCiclosure : intrinsicClosure ℝ C = A := by
          rw [intrinsicClosure_eq_closure_inter_affineSpan, hCclosure,
            inter_eq_left]
          exact hAsubspanC
        by_cases hzint : z ∈ intrinsicInterior ℝ C
        · exact intrinsicInterior_subset hzint
        · have hziclosure : z ∈ intrinsicClosure ℝ C := by
            rw [hCiclosure]
            exact hz
          have hzfront : z ∈ intrinsicFrontier ℝ C := by
            rw [← intrinsicClosure_sdiff_intrinsicInterior C]
            exact ⟨hziclosure, hzint⟩
          obtain ⟨L, hLnonzero, hLsupport⟩ :=
            exists_supporting_functional_of_mem_intrinsicFrontier hCconv hzfront
          rw [hspan] at hLnonzero
          let F := L.toExposed A
          have hFexp : IsExposed ℝ A F :=
            ContinuousLinearMap.toExposed.isExposed (l := L) (A := A)
          have hzF : z ∈ F := by
            refine ⟨hz, fun y hy ↦ ?_⟩
            apply hLsupport y
            rw [hCclosure]
            exact hy
          have hFcomp : IsCompact F := hFexp.isCompact hAcomp
          have hFconv : Convex ℝ F := hFexp.convex hAconv
          have hFsub : F ⊆ A := hFexp.subset
          have hdirle :
              (affineSpan ℝ F).direction ≤ (affineSpan ℝ A).direction :=
            AffineSubspace.direction_le (affineSpan_mono ℝ hFsub)
          have hdirker : (affineSpan ℝ F).direction ≤ L.ker := by
            rw [direction_affineSpan,
              vectorSpan_eq_span_vsub_set_right ℝ hzF, Submodule.span_le]
            rintro v ⟨y, hyF, rfl⟩
            change L (y -ᵥ z) = 0
            rw [vsub_eq_sub, map_sub]
            change L y - L z = 0
            apply sub_eq_zero.mpr
            apply le_antisymm
            · apply hLsupport y
              rw [hCclosure]
              exact hFsub hyF
            · exact hyF.2 z hz
          have hdirne :
              (affineSpan ℝ F).direction ≠ (affineSpan ℝ A).direction := by
            intro heq
            obtain ⟨v, hv⟩ := hLnonzero
            apply hv
            apply hdirker
            rw [heq]
            exact v.property
          have hdirlt :
              (affineSpan ℝ F).direction < (affineSpan ℝ A).direction :=
            lt_of_le_of_ne hdirle hdirne
          have hdimlt :
              Module.finrank ℝ (affineSpan ℝ F).direction < d := by
            rw [← hAdim]
            exact Submodule.finrank_lt_finrank_of_lt hdirlt
          have hzrec :
              z ∈ convexHull ℝ (F.extremePoints ℝ) :=
            ih _ hdimlt F rfl z hFcomp hFconv hzF
          exact convexHull_mono
            hFexp.isExtreme.extremePoints_subset_extremePoints hzrec
  exact hmain _ s rfl x hscomp hsconv hx

end Submission.Helpers
