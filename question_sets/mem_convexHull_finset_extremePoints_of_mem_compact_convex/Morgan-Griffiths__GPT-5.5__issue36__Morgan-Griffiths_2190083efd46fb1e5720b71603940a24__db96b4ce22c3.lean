import Mathlib

namespace Submission

open Set

/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
universe u

/-- An injective affine map sends the extreme points of a set exactly to the extreme points of the
image. -/
lemma affineMap_image_extremePoints_of_injective {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f) (s : Set E) :
    f '' (s.extremePoints ℝ) = (f '' s).extremePoints ℝ := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [mem_extremePoints] at ha ⊢
    refine ⟨⟨a, ha.1, rfl⟩, ?_⟩
    rintro _ ⟨x1, hx1, rfl⟩ _ ⟨x2, hx2, rfl⟩ hbseg
    have hseg : f a ∈ f '' openSegment ℝ x1 x2 := by
      simpa [image_openSegment _ f x1 x2] using hbseg
    rcases hseg with ⟨a', ha', hfa'⟩
    have haeq : a = a' := hf hfa'.symm
    subst haeq
    exact ⟨congrArg f (ha.2 x1 hx1 x2 hx2 ha').1,
      congrArg f (ha.2 x1 hx1 x2 hx2 ha').2⟩
  · intro hb
    rw [mem_extremePoints] at hb
    rcases hb.1 with ⟨a, ha, rfl⟩
    refine ⟨a, ?_, rfl⟩
    rw [mem_extremePoints]
    refine ⟨ha, ?_⟩
    intro x1 hx1 x2 hx2 haseg
    have hbseg : f a ∈ openSegment ℝ (f x1) (f x2) := by
      rw [← image_openSegment _ f x1 x2]
      exact ⟨a, haseg, rfl⟩
    have hpair := hb.2 (f x1) ⟨x1, hx1, rfl⟩ (f x2) ⟨x2, hx2, rfl⟩ hbseg
    exact ⟨hf hpair.1, hf hpair.2⟩

/-- Transport a point in the convex hull of extreme points across an injective affine map. -/
lemma affineMap_mem_convexHull_image_extremePoints_of_injective {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f)
    {t : Set E} {s : Set F} (himg : f '' t = s) {x : E}
    (hx : x ∈ convexHull ℝ (t.extremePoints ℝ)) :
    f x ∈ convexHull ℝ (s.extremePoints ℝ) := by
  have hximg : f x ∈ f '' convexHull ℝ (t.extremePoints ℝ) := ⟨x, hx, rfl⟩
  rw [f.image_convexHull] at hximg
  refine convexHull_mono ?_ hximg
  rw [affineMap_image_extremePoints_of_injective f hf t, himg]

/-- The affine inclusion of a submodule translated by a point. -/
noncomputable def Submodule.vaddAffineMap {E : Type*} [AddCommGroup E] [Module ℝ E]
    (V : Submodule ℝ E) (p : E) : V →ᵃ[ℝ] E where
  toFun v := (v : E) + p
  linear := V.subtype
  map_vadd' := by intro q v; simp [vadd_eq_add, add_assoc]

lemma Submodule.vaddAffineMap_injective {E : Type*} [AddCommGroup E] [Module ℝ E]
    (V : Submodule ℝ E) (p : E) : Function.Injective (Submodule.vaddAffineMap V p) := by
  intro a b h
  ext
  exact add_right_cancel h

lemma Submodule.isClosedEmbedding_vaddAffineMap {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (V : Submodule ℝ E) (p : E) :
    Topology.IsClosedEmbedding (Submodule.vaddAffineMap V p) := by
  have hclosed : IsClosed (V : Set E) := V.closed_of_finiteDimensional
  simpa [Submodule.vaddAffineMap, Function.comp_def] using
    ((Homeomorph.addRight p).isClosedEmbedding.comp hclosed.isClosedEmbedding_subtypeVal)

lemma Submodule.image_preimage_vaddAffineMap_eq {E : Type*} [AddCommGroup E] [Module ℝ E]
    (V : Submodule ℝ E) (p : E) {s : Set E}
    (hmem : ∀ y ∈ s, y - p ∈ V) :
    Submodule.vaddAffineMap V p '' (Submodule.vaddAffineMap V p ⁻¹' s) = s := by
  ext y
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact hv
  · intro hy
    let v : V := ⟨y - p, hmem y hy⟩
    have hgv : Submodule.vaddAffineMap V p v = y := by
      simp [Submodule.vaddAffineMap, v, sub_add_cancel]
    exact ⟨v, by simpa [hgv] using hy, hgv⟩

/-- Ordinary interior points of a full-dimensional compact convex set lie in the convex hull of the
extreme points. -/
lemma interior_subset_convexHull_extremePoints_of_isCompact_convex {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (hscomp : IsCompact s) (hsconv : Convex ℝ s) :
    interior s ⊆ convexHull ℝ (s.extremePoints ℝ) := by
  intro x hx
  let C : Set E := convexHull ℝ (s.extremePoints ℝ)
  have hclosure : closure C = s := by
    simpa [C] using closure_convexHull_extremePoints (s := s) hscomp hsconv
  have hspan_s : affineSpan ℝ s = ⊤ :=
    hsconv.interior_nonempty_iff_affineSpan_eq_top.mp ⟨x, hx⟩
  have hC_subset_span : C ⊆ (affineSpan ℝ (s.extremePoints ℝ) : Set E) := by
    dsimp [C]
    exact convexHull_min (subset_affineSpan ℝ _)
      (affineSpan ℝ (s.extremePoints ℝ)).convex
  have hclC_subset_span : closure C ⊆ (affineSpan ℝ (s.extremePoints ℝ) : Set E) :=
    closure_minimal hC_subset_span
      (affineSpan ℝ (s.extremePoints ℝ)).closed_of_finiteDimensional
  have hs_subset_span : s ⊆ (affineSpan ℝ (s.extremePoints ℝ) : Set E) := by
    intro y hy
    exact hclC_subset_span (by simpa [hclosure] using hy)
  have hle : affineSpan ℝ s ≤ affineSpan ℝ (s.extremePoints ℝ) :=
    affineSpan_le_of_subset_coe hs_subset_span
  have hspan_ext_top : affineSpan ℝ (s.extremePoints ℝ) = ⊤ := by
    rw [hspan_s] at hle
    exact top_le_iff.mp hle
  have hCint : (interior C).Nonempty := by
    dsimp [C]
    rw [interior_convexHull_nonempty_iff_affineSpan_eq_top]
    exact hspan_ext_top
  have h_int_eq : interior (closure C) = interior C :=
    (convex_convexHull ℝ (s.extremePoints ℝ)).interior_closure_eq_interior_of_nonempty_interior
      hCint
  have hx' : x ∈ interior (closure C) := by
    rwa [hclosure]
  have hxC : x ∈ interior C := by
    rwa [h_int_eq] at hx'
  exact interior_subset hxC

/-- Finite-dimensional Minkowski/Krein--Milman in closure-free membership form. The proof is by
strong induction on ambient dimension. If the set has empty interior, translate it into the direction
of its affine span and use the induction hypothesis. If it has nonempty interior, interior points
are handled using `closure_convexHull_extremePoints`; boundary points lie in a proper exposed face,
which after translation lies in the kernel of a nonzero functional, so induction applies. -/
theorem mem_convexHull_extremePoints_of_mem_compact_convex {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} {x : E} (hscomp : IsCompact s) (hsconv : Convex ℝ s) (hx : x ∈ s) :
    x ∈ convexHull ℝ (s.extremePoints ℝ) := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
      Module.finrank ℝ E = n → ∀ {s : Set E} {x : E},
        IsCompact s → Convex ℝ s → x ∈ s → x ∈ convexHull ℝ (s.extremePoints ℝ)
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n IH =>
      intro E _ _ _ hdim s x hscomp hsconv hx
      by_cases hsint : (interior s).Nonempty
      · by_cases hxint : x ∈ interior s
        · exact interior_subset_convexHull_extremePoints_of_isCompact_convex hscomp hsconv hxint
        · obtain ⟨f, hfne, hmax⟩ :=
            geometric_hahn_banach_of_nonempty_interior_point hsconv hxint hsint
          let F : Set E := ContinuousLinearMap.toExposed f s
          have hFexp : IsExposed ℝ s F :=
            ContinuousLinearMap.toExposed.isExposed (l := f) (A := s)
          have hxF : x ∈ F := by
            exact ⟨hx, hmax⟩
          let V : Submodule ℝ E := LinearMap.ker f.toLinearMap
          let g : V →ᵃ[ℝ] E := Submodule.vaddAffineMap V x
          let T : Set V := g ⁻¹' F
          have hTcomp : IsCompact T := by
            exact (Submodule.isClosedEmbedding_vaddAffineMap V x).isCompact_preimage
              (hFexp.isCompact hscomp)
          have hTconv : Convex ℝ T := by
            exact (hFexp.convex hsconv).affine_preimage g
          have h0T : (0 : V) ∈ T := by
            simp [T, g, Submodule.vaddAffineMap, hxF]
          have hfne' : f.toLinearMap ≠ 0 := by
            intro hzero
            apply hfne
            ext y
            exact LinearMap.congr_fun hzero y
          have hVlt : Module.finrank ℝ V < n := by
            have hkeradd : Module.finrank ℝ (LinearMap.ker f.toLinearMap) + 1 =
                Module.finrank ℝ E := by
              simpa using (Module.Dual.finrank_ker_add_one_of_ne_zero (f := f.toLinearMap) hfne')
            simp only [V]
            omega
          have h0conv : (0 : V) ∈ convexHull ℝ (T.extremePoints ℝ) :=
            IH (Module.finrank ℝ V) hVlt V rfl hTcomp hTconv h0T
          have hmemF : ∀ y ∈ F, y - x ∈ V := by
            intro y hy
            have hy_s : y ∈ s := hy.1
            have hle_yx : f y ≤ f x := hmax y hy_s
            have hle_xy : f x ≤ f y := hy.2 x hx
            have heq : f y = f x := le_antisymm hle_yx hle_xy
            change f.toLinearMap (y - x) = 0
            simp [map_sub, heq]
          have himg : g '' T = F := by
            simpa [g, T] using Submodule.image_preimage_vaddAffineMap_eq V x hmemF
          have hxFconv : g (0 : V) ∈ convexHull ℝ (F.extremePoints ℝ) :=
            affineMap_mem_convexHull_image_extremePoints_of_injective g
              (Submodule.vaddAffineMap_injective V x) himg h0conv
          have hxSconv : g (0 : V) ∈ convexHull ℝ (s.extremePoints ℝ) :=
            convexHull_mono (hFexp.isExtreme.extremePoints_subset_extremePoints) hxFconv
          simpa [g, Submodule.vaddAffineMap] using hxSconv
      · let V : Submodule ℝ E := (affineSpan ℝ s).direction
        let g : V →ᵃ[ℝ] E := Submodule.vaddAffineMap V x
        let T : Set V := g ⁻¹' s
        have hTcomp : IsCompact T := by
          exact (Submodule.isClosedEmbedding_vaddAffineMap V x).isCompact_preimage hscomp
        have hTconv : Convex ℝ T := by
          exact hsconv.affine_preimage g
        have h0T : (0 : V) ∈ T := by
          simp [T, g, Submodule.vaddAffineMap, hx]
        have hspan_ne_top : affineSpan ℝ s ≠ ⊤ := by
          intro htop
          exact hsint (hsconv.interior_nonempty_iff_affineSpan_eq_top.mpr htop)
        have hdir_ne_top : V ≠ ⊤ := by
          intro hdir
          apply hspan_ne_top
          have hne : ((affineSpan ℝ s : AffineSubspace ℝ E) : Set E).Nonempty :=
            ⟨x, subset_affineSpan ℝ s hx⟩
          exact (AffineSubspace.direction_eq_top_iff_of_nonempty hne).1 hdir
        have hVlt : Module.finrank ℝ V < n := by
          have hlt : V < ⊤ := lt_top_iff_ne_top.mpr hdir_ne_top
          have hlt' : Module.finrank ℝ V < Module.finrank ℝ (⊤ : Submodule ℝ E) :=
            Submodule.finrank_lt_finrank_of_lt hlt
          simpa [hdim] using hlt'
        have h0conv : (0 : V) ∈ convexHull ℝ (T.extremePoints ℝ) :=
          IH (Module.finrank ℝ V) hVlt V rfl hTcomp hTconv h0T
        have hmem : ∀ y ∈ s, y - x ∈ V := by
          intro y hy
          exact AffineSubspace.vsub_mem_direction (s := affineSpan ℝ s)
            (subset_affineSpan ℝ s hy) (subset_affineSpan ℝ s hx)
        have himg : g '' T = s := by
          simpa [g, T] using Submodule.image_preimage_vaddAffineMap_eq V x hmem
        have hxSconv : g (0 : V) ∈ convexHull ℝ (s.extremePoints ℝ) :=
          affineMap_mem_convexHull_image_extremePoints_of_injective g
            (Submodule.vaddAffineMap_injective V x) himg h0conv
        simpa [g, Submodule.vaddAffineMap] using hxSconv
  exact hP (Module.finrank ℝ E) E rfl hscomp hsconv hx

/-- Carathéodory reduction in finite dimension: every point in the convex hull of `A` lies in the
convex hull of finitely many points of `A`, with at most `finrank + 1` points. -/
theorem exists_finset_card_le_of_mem_convexHull {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] {A : Set E} {x : E} (hx : x ∈ convexHull ℝ A) :
    ∃ t : Finset E,
      (↑t : Set E) ⊆ A ∧
      t.card ≤ Module.finrank ℝ E + 1 ∧
      x ∈ convexHull ℝ (↑t : Set E) := by
  classical
  rw [convexHull_eq_union] at hx
  simp only [Set.mem_iUnion, exists_prop] at hx
  rcases hx with ⟨t, htA, htaff, hxt⟩
  refine ⟨t, htA, ?_, hxt⟩
  have hc1 :
      Fintype.card t ≤
        Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → E))) + 1 :=
    htaff.card_le_finrank_succ
  have hc2 :
      Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → E))) ≤
        Module.finrank ℝ E :=
    Submodule.finrank_le _
  have hcard : Fintype.card t = t.card := by simp
  rw [← hcard]
  exact hc1.trans (Nat.add_le_add_right hc2 1)
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/
theorem mem_convexHull_finset_extremePoints_of_mem_compact_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} {x : E}
    (hscomp : IsCompact s)
    (hsconv : Convex ℝ s)
    (hx : x ∈ s) :
    ∃ t : Finset E,
      (↑t : Set E) ⊆ s.extremePoints ℝ ∧
      t.card ≤ Module.finrank ℝ E + 1 ∧
      x ∈ convexHull ℝ (↑t : Set E) :=
/-ResultProofBegin-/by
  exact exists_finset_card_le_of_mem_convexHull
    (mem_convexHull_extremePoints_of_mem_compact_convex hscomp hsconv hx)
/-ResultProofEnd-/
/-ResultEnd-/
end Submission

