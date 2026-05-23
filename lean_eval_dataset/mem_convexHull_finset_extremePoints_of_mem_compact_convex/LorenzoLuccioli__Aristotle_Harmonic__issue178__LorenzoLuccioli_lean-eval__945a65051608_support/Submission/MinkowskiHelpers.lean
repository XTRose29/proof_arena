import Mathlib

open Set Finset

universe u

namespace Submission.MinkowskiHelpers

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-
The translation of a face {p ∈ s | f p = f a} by -a lies in ker(f).
-/
theorem vadd_face_subset_ker
    (f : E →L[ℝ] ℝ) (a : E) (s : Set E) (hf : ∀ p ∈ s, f p ≤ f a) :
    ((-a) +ᵥ ·) '' {p ∈ s | f p = f a} ⊆ LinearMap.ker f.toLinearMap := by
  intro x hx
  aesop

/-
Given a face F = {p ∈ s | f p = f a} with f ≠ 0, and the IH that
    lower-dimensional compact convex sets satisfy Minkowski, we get
    a ∈ convexHull ℝ (extremePoints ℝ F).
-/
set_option maxHeartbeats 800000 in
theorem face_point_in_hull
    (f : E →L[ℝ] ℝ) (hf_ne : f ≠ 0) (a : E)
    (s : Set E) (hscomp : IsCompact s) (hsconv : Convex ℝ s)
    (hf_sup : ∀ p ∈ s, f p ≤ f a) (ha : a ∈ s)
    (ih : ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V],
      Module.finrank ℝ V < Module.finrank ℝ E →
      ∀ (s' : Set V), IsCompact s' → Convex ℝ s' →
      s' ⊆ convexHull ℝ (s'.extremePoints ℝ)) :
    a ∈ convexHull ℝ (extremePoints ℝ {p ∈ s | f p = f a}) := by
  -- Set F = {p ∈ s | f p = f a}. We need a ∈ convexHull ℝ (extremePoints ℝ F).
  set F := {p ∈ s | f p = f a} with hF_def
  have hF_compact : IsCompact F := by
    exact hscomp.inter_right ( isClosed_eq f.continuous continuous_const )
  have hF_convex : Convex ℝ F := by
    refine' convex_iff_forall_pos.mpr _;
    simp +zetaDelta at *;
    exact fun x hx hx' y hy hy' a b ha hb hab => ⟨ hsconv hx hy ha.le hb.le hab, by rw [ hx', hy', ← add_mul, hab, one_mul ] ⟩
  have haF : a ∈ F := by
    exact ⟨ ha, rfl ⟩;
  -- Let $V = \ker(f.toLinearMap)$ and $\iota = V.subtypeL$. Let $s' = \iota^{-1}(F')$.
  set V := LinearMap.ker f.toLinearMap with hV_def
  set ι := Submodule.subtypeL V with hι_def
  set s' := ι ⁻¹' ((-a +ᵥ ·) '' F) with hs'_def
  have hs'_compact : IsCompact s' := by
    have hs'_closed : IsClosed s' := by
      exact IsClosed.preimage ι.continuous ( hF_compact.image ( continuous_const.add continuous_id' ) |> IsCompact.isClosed );
    have hs'_bounded : Bornology.IsBounded s' := by
      have hs'_bounded : Bornology.IsBounded ((-a +ᵥ ·) '' F) := by
        exact hF_compact.image ( continuous_const.add continuous_id' ) |> IsCompact.isBounded;
      rw [ Metric.isBounded_iff ] at *;
      obtain ⟨ C, hC ⟩ := hs'_bounded; use C; intro x hx y hy; specialize hC hx hy; simp_all +decide [ dist_eq_norm ] ;
    exact ( Metric.isCompact_iff_isClosed_bounded.mpr ⟨ hs'_closed, hs'_bounded ⟩ )
  have hs'_convex : Convex ℝ s' := by
    intro x hx y hy a b ha hb hab; simp_all +decide [ Set.mem_preimage, Set.mem_image ] ;
    convert hsconv hx hy ha hb hab using 1 ; simp +decide [ add_smul, smul_add, ← add_assoc ];
    rw [ show b = 1 - a by linarith ] ; simp +decide [ add_smul, sub_smul ] ; abel1;
  have hs'_subset : s' ⊆ convexHull ℝ (extremePoints ℝ s') := by
    have hV_finrank : Module.finrank ℝ V < Module.finrank ℝ E := by
      have := LinearMap.finrank_range_add_finrank_ker ( f : E →ₗ[ℝ] ℝ );
      rw [ ← this ];
      exact lt_add_of_pos_left _ ( Nat.pos_of_ne_zero ( by simp +decide [ show LinearMap.range ( f : E →ₗ[ℝ] ℝ ) = ⊤ from LinearMap.range_eq_top.mpr ( show Function.Surjective f from by exact fun x => by exact ⟨ ( x / f ( Classical.choose ( show ∃ y, f y ≠ 0 from not_forall.mp fun h => hf_ne <| ContinuousLinearMap.ext h ) ) ) • Classical.choose ( show ∃ y, f y ≠ 0 from not_forall.mp fun h => hf_ne <| ContinuousLinearMap.ext h ), by simp +decide [ div_mul_cancel₀ _ ( Classical.choose_spec ( show ∃ y, f y ≠ 0 from not_forall.mp fun h => hf_ne <| ContinuousLinearMap.ext h ) ) ] ⟩ ) ] ) )
    exact ih V hV_finrank s' hs'_compact hs'_convex
  have h0_s' : (0 : V) ∈ s' := by
    aesop
  have h0_convexHull : (0 : V) ∈ convexHull ℝ (extremePoints ℝ s') := by
    exact hs'_subset h0_s'
  have h0_image : (0 : E) ∈ convexHull ℝ (extremePoints ℝ ((-a +ᵥ ·) '' F)) := by
    have h0_image : (0 : E) ∈ ι '' convexHull ℝ (extremePoints ℝ s') := by
      exact ⟨ 0, h0_convexHull, by simp +decide ⟩;
    have h_image_convexHull : ι '' convexHull ℝ (extremePoints ℝ s') ⊆ convexHull ℝ (extremePoints ℝ ((-a +ᵥ ·) '' F)) := by
      have h_image_convexHull : ι '' extremePoints ℝ s' ⊆ extremePoints ℝ ((-a +ᵥ ·) '' F) := by
        simp +decide [ Set.image_subset_iff, extremePoints ];
        simp +zetaDelta at *;
        intro x hx hx' hx''; refine' ⟨ ⟨ hx', hx ⟩, _ ⟩ ; intro y hy hy' z hz hz' h; specialize hx'' y hy' hy z hz' hz; simp_all +decide [ openSegment_eq_image ] ;
      refine' Set.Subset.trans _ ( convexHull_mono h_image_convexHull );
      simp +decide [ Set.image_subset_iff, convexHull_min ];
      exact convexHull_min ( Set.subset_def.mpr fun x hx => subset_convexHull ℝ _ <| Set.mem_image_of_mem _ hx ) ( convex_convexHull ℝ _ |> fun h => h.linear_preimage ι.toLinearMap );
    exact h_image_convexHull h0_image
  have ha_convexHull : a ∈ convexHull ℝ (extremePoints ℝ F) := by
    have h_extreme_points : extremePoints ℝ ((-a +ᵥ ·) '' F) = (-a +ᵥ ·) '' extremePoints ℝ F := by
      ext x; simp [extremePoints];
      intro hx;
      constructor <;> intro h y hy z hz hxy;
      · contrapose! h;
        refine' ⟨ y - a, _, z - a, _, _, _ ⟩ <;> simp_all +decide [ openSegment_eq_image ];
        · obtain ⟨ t, ht, h ⟩ := hxy; use t; simp_all +decide [ sub_smul, smul_sub ] ;
          grind +qlia;
        · grind +qlia;
      · contrapose! h;
        refine' ⟨ a + y, hy, a + z, hz, _, _ ⟩ <;> simp_all +decide [ openSegment_eq_image ];
        rcases hxy with ⟨ t, ⟨ ht₀, ht₁ ⟩, rfl ⟩ ; exact ⟨ t, ⟨ ht₀, ht₁ ⟩, by simp +decide [ sub_smul, add_smul ] ; abel1 ⟩ ;
    rw [h_extreme_points] at h0_image;
    rw [ mem_convexHull_iff ] at *;
    intro t ht ht_convex; specialize h0_image ( ( fun x => -a +ᵥ x ) '' t ) ; simp_all +decide [ Set.image_subset_iff ] ;
    apply h0_image;
    · exact Set.preimage_mono ht;
    · exact Convex.translate_preimage_right ht_convex a
  exact ha_convexHull

/-
Empty interior case of Minkowski's theorem. If s is compact convex with
    empty interior, then s lies in a proper subspace and we can apply the IH.
-/
theorem minkowski_empty_interior
    (n : ℕ)
    (ih : ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V],
      Module.finrank ℝ V ≤ n →
      ∀ (s' : Set V), IsCompact s' → Convex ℝ s' →
      s' ⊆ convexHull ℝ (s'.extremePoints ℝ))
    (hd : Module.finrank ℝ E ≤ n + 1)
    {s : Set E} (hscomp : IsCompact s) (hsconv : Convex ℝ s)
    (hint : ¬(interior s).Nonempty)
    {x : E} (hx : x ∈ s) :
    x ∈ convexHull ℝ (s.extremePoints ℝ) := by
  -- Since $s$ is convex and has no interior points, its vector span $V$ is a proper subspace of $E$.
  set V := vectorSpan ℝ s
  have hV : V ≠ ⊤ := by
    intro hV_top
    have h_interior_nonempty : (interior s).Nonempty := by
      have := hsconv.interior_nonempty_iff_affineSpan_eq_top.mpr ?_;
      · exact this;
      · rw [ eq_top_iff ] at *;
        intro y hy; specialize hV_top ( show y - x ∈ ⊤ from trivial ) ; simp_all +decide [ vectorSpan ] ;
        rw [ affineSpan ];
        exact ⟨ x, hx, y - x, hV_top, by simp +decide ⟩
    contradiction
  have hV_dim : Module.finrank ℝ V < Module.finrank ℝ E := by
    refine' lt_of_le_of_ne ( Submodule.finrank_le _ ) _;
    exact fun h => hV <| Submodule.eq_top_of_finrank_eq h;
  -- Let $p₀$ be any point in $s$. Then $s - p₀ ⊆ V$.
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ ∈ s, True := by
    exact ⟨ x, hx, trivial ⟩
  set s' := {v : V | v.val + p₀ ∈ s}
  have hs'_comp : IsCompact s' := by
    have hs'_comp : IsClosed s' := by
      exact hscomp.isClosed.preimage ( continuous_subtype_val.add continuous_const );
    have hs'_bounded : ∃ M > 0, ∀ v ∈ s', ‖v‖ ≤ M := by
      have := hscomp.isBounded.exists_pos_norm_le;
      obtain ⟨ R, hR₀, hR ⟩ := this; use R + ‖p₀‖; exact ⟨ add_pos_of_pos_of_nonneg hR₀ ( norm_nonneg _ ), fun v hv => by simpa using le_trans ( norm_sub_le ( v + p₀ ) p₀ ) ( by linarith [ hR _ hv ] ) ⟩ ;
    exact ( Metric.isCompact_iff_isClosed_bounded.mpr ⟨ hs'_comp, isBounded_iff_forall_norm_le.mpr ⟨ hs'_bounded.choose, fun v hv => hs'_bounded.choose_spec.2 v hv ⟩ ⟩ )
  have hs'_conv : Convex ℝ s' := by
    intro v hv w hw a b ha hb hab; simp_all +decide [ ← eq_sub_iff_add_eq' ] ;
    convert hsconv hv hw ha ( sub_nonneg.2 hb ) ( by linarith ) using 1 ; simp +decide [ hab, add_smul, smul_add, smul_sub, sub_smul ] ; abel_nf;
    simp +decide [ s', add_assoc ];
  -- By the induction hypothesis, $s'$ is contained in the convex hull of its extreme points.
  have hs'_hull : s' ⊆ convexHull ℝ (extremePoints ℝ s') := by
    exact ih V (by omega) s' hs'_comp hs'_conv;
  -- Translate back to $s$ by adding $p₀$.
  have hs_hull : s ⊆ (fun v : V => v.val + p₀) '' (convexHull ℝ (extremePoints ℝ s')) := by
    intro x hx
    have hx' : x - p₀ ∈ V := by
      exact Submodule.subset_span ⟨ x, hx, p₀, hp₀.1, rfl ⟩;
    exact ⟨ ⟨ x - p₀, hx' ⟩, hs'_hull ( by aesop ), by simp +decide ⟩;
  -- The extreme points of $s'$ map to the extreme points of $s$ under the translation by $p₀$.
  have h_extreme_points : (fun v : V => v.val + p₀) '' extremePoints ℝ s' ⊆ extremePoints ℝ s := by
    rintro _ ⟨ v, hv, rfl ⟩;
    constructor;
    · exact hv.1;
    · rintro x₁ hx₁ x₂ hx₂ ⟨ a, b, ha, hb, hab, h ⟩;
      -- Since $x₁$ and $x₂$ are in $s$, we have $x₁ - p₀$ and $x₂ - p₀$ in $s'$.
      have hx₁' : ⟨x₁ - p₀, by
        exact Submodule.subset_span ⟨ x₁, hx₁, p₀, hp₀.1, rfl ⟩⟩ ∈ s' := by
        aesop
      have hx₂' : ⟨x₂ - p₀, by
        exact Submodule.subset_span ⟨ x₂, hx₂, p₀, hp₀.1, rfl ⟩⟩ ∈ s' := by
        aesop
      generalize_proofs at *;
      have := hv.2 hx₁' hx₂' ?_;
      · simp +decide [ ← this ];
      · use a, b;
        simp_all +decide [ Subtype.ext_iff ];
        convert congr_arg ( fun x => x - p₀ ) h using 1 <;> simp +decide [ smul_sub, ← eq_sub_iff_add_eq' ] ; abel_nf;
        rw [ show a = 1 - b by linarith ] ; simp +decide [ sub_smul ] ; abel_nf;
  refine' convexHull_mono h_extreme_points _;
  obtain ⟨ v, hv, rfl ⟩ := hs_hull hx;
  rw [ mem_convexHull_iff_exists_fintype ] at hv ⊢;
  rcases hv with ⟨ ι, x, w, z, hw, hw', hz, rfl ⟩ ; use ι, x, w, fun i => ( z i : V ) + p₀; simp_all +decide [ Finset.sum_add_distrib, add_smul ] ;
  simp +decide [ ← Finset.sum_smul, hw' ]

end Submission.MinkowskiHelpers