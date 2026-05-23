import Mathlib
import Submission.ConvexHullCompact
import Submission.MinkowskiHelpers

open Set Finset

universe u

namespace Submission.Minkowski

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem isExtreme_exposedFace {s : Set E} (hsconv : Convex ℝ s)
    (f : E →ₗ[ℝ] ℝ) (c : ℝ) (hc : ∀ p ∈ s, f p ≤ c) :
    IsExtreme ℝ s {p ∈ s | f p = c} := by
  refine' ⟨_, _⟩
  · exact fun x hx => hx.1
  · rintro x hx y hy z ⟨hz, hz'⟩ ⟨a, b, ha, hb, hab, rfl⟩
    simp_all +decide [← eq_sub_iff_add_eq']
    nlinarith [hc x hx, hc y hy]

theorem exists_supporting_functional
    {s : Set E} (hscomp : IsCompact s) (hsconv : Convex ℝ s)
    (hint : (interior s).Nonempty) {a : E} (ha : a ∈ s) (ha_bdy : a ∉ interior s) :
    ∃ f : E →L[ℝ] ℝ, f ≠ 0 ∧ ∀ p ∈ s, f p ≤ f a := by
  obtain ⟨f, hf_nonzero, hf⟩ : ∃ f : E →L[ℝ] ℝ, f ≠ 0 ∧ ∀ y ∈ interior s, f y < f a := by
    obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hsconv.interior isOpen_interior ha_bdy
    exact ⟨f, fun h => by simp [h] at hf; exact hf _ hint.choose_spec, hf⟩
  have h_seq : ∀ p ∈ s, ∃ y : ℕ → E, (∀ n, y n ∈ interior s) ∧
      Filter.Tendsto y Filter.atTop (nhds p) := fun p hp =>
    mem_closure_iff_seq_limit.mp
      (hsconv.closure_interior_eq_closure_of_nonempty_interior hint ▸ subset_closure hp)
  exact ⟨f, hf_nonzero, fun p hp =>
    le_of_tendsto_of_tendsto'
      (f.continuous.continuousAt.tendsto.comp (h_seq p hp).choose_spec.2)
      tendsto_const_nhds
      (fun n => le_of_lt (hf _ ((h_seq p hp).choose_spec.1 n)))⟩

set_option maxHeartbeats 800000 in
theorem exists_boundary_segment
    {s : Set E} (hscomp : IsCompact s) (hsconv : Convex ℝ s)
    (hint : (interior s).Nonempty) {x : E} (hx : x ∈ s) (hxne : x ∉ s.extremePoints ℝ) :
    ∃ a b : E, a ∈ s ∧ b ∈ s ∧ a ∉ interior s ∧ b ∉ interior s ∧
      x ∈ openSegment ℝ a b := by
  -- Since $x$ is not an extreme point, there exist $y, z \in s$ with $y \neq z$ and $x \in \text{openSegment} \, \mathbb{R} \, y \, z$.
  obtain ⟨y, z, hy, hz, hyz, hx⟩ : ∃ y z : E, y ∈ s ∧ z ∈ s ∧ y ≠ z ∧ x ∈ openSegment ℝ y z := by
    contrapose! hxne; simp_all +decide [ extremePoints ] ;
    intro y hy z hz h; specialize hxne y z hy hz; contrapose! hxne; aesop;
  -- Let $L(t) = (1-t)y + tz$ be the line through $y$ and $z$.
  set L : ℝ → E := fun t => (1 - t) • y + t • z;
  -- Let $I = \{ t \in \mathbb{R} \mid L(t) \in s \}$. This set is compact and convex.
  set I : Set ℝ := {t | L t ∈ s}
  have hI_compact : IsCompact I := by
    have hL_cont : Continuous L := by
      fun_prop;
    have hI_bounded : ∃ M > 0, ∀ t : ℝ, L t ∈ s → |t| ≤ M := by
      have hL_bounded : ∃ M > 0, ∀ t : ℝ, L t ∈ s → ‖L t - y‖ ≤ M := by
        obtain ⟨ M, hM ⟩ := hscomp.isBounded.exists_pos_norm_le;
        exact ⟨ M + M, add_pos hM.1 hM.1, fun t ht => le_trans ( norm_sub_le _ _ ) ( add_le_add ( hM.2 _ ht ) ( hM.2 _ hy ) ) ⟩;
      obtain ⟨ M, hM₀, hM ⟩ := hL_bounded; use M / ‖z - y‖; refine' ⟨ div_pos hM₀ ( norm_pos_iff.mpr <| sub_ne_zero.mpr <| Ne.symm hyz ), fun t ht => _ ⟩ ; specialize hM t ht; simp_all +decide [ norm_smul, abs_mul ] ;
      rw [ le_div_iff₀ ( norm_pos_iff.mpr ( sub_ne_zero.mpr ( Ne.symm hyz ) ) ) ];
      convert hM using 1 ; rw [ show L t - y = t • ( z - y ) by rw [ show L t = ( 1 - t ) • y + t • z by rfl ] ; simp +decide [ sub_smul, smul_sub ] ; abel1 ] ; rw [ norm_smul, Real.norm_eq_abs ];
    exact CompactIccSpace.isCompact_Icc.of_isClosed_subset ( hscomp.isClosed.preimage hL_cont ) fun t ht => ⟨ neg_le_of_abs_le ( hI_bounded.choose_spec.2 t ht ), le_of_abs_le ( hI_bounded.choose_spec.2 t ht ) ⟩
  have hI_convex : Convex ℝ I := by
    intro t ht u hu a b ha hb hab;
    convert hsconv ht hu ha hb hab using 1 ; simp +decide [ L ] ; ring;
    simp +zetaDelta at *;
    rw [ ← eq_sub_iff_add_eq' ] at hab ; subst_vars ; simp +decide [ sub_smul, smul_sub ] ; abel_nf;
    simp +decide [ add_smul, mul_smul, smul_add, smul_sub ] ; abel_nf;
  -- Let $t_{\min} = \min I$ and $t_{\max} = \max I$.
  obtain ⟨t_min, ht_min⟩ : ∃ t_min ∈ I, ∀ t ∈ I, t_min ≤ t := by
    apply_rules [ hI_compact.exists_isLeast ];
    exact ⟨ 0, by aesop ⟩
  obtain ⟨t_max, ht_max⟩ : ∃ t_max ∈ I, ∀ t ∈ I, t ≤ t_max := by
    exact hI_compact.exists_isGreatest ⟨ t_min, ht_min.1 ⟩;
  refine' ⟨ L t_min, L t_max, ht_min.1, ht_max.1, _, _, _ ⟩;
  · intro h;
    -- Since $L(t_min) \in \text{interior } s$, there exists an $\epsilon > 0$ such that $L(t_min - \epsilon) \in s$.
    obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, ∀ t, abs (t - t_min) < ε → L t ∈ s := by
      have h_cont : Continuous L := by
        fun_prop;
      exact Metric.mem_nhds_iff.mp ( h_cont.continuousAt.preimage_mem_nhds ( mem_interior_iff_mem_nhds.mp h ) );
    exact absurd ( ht_min.2 ( t_min - ε / 2 ) ( hε _ ( by rw [ abs_of_neg ] <;> linarith ) ) ) ( by linarith );
  · intro hL_max_interior
    obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, ∀ t, abs (t - t_max) < ε → L t ∈ s := by
      have hL_max_interior : ContinuousAt L t_max := by
        fun_prop;
      exact Metric.mem_nhds_iff.mp ( hL_max_interior ( mem_interior_iff_mem_nhds.mp ‹_› ) );
    exact not_lt_of_ge ( ht_max.2 ( t_max + ε / 2 ) ( hε _ ( by rw [ abs_of_pos ] <;> linarith ) ) ) ( by linarith );
  · -- Since $x \in \text{openSegment} \, \mathbb{R} \, y \, z$, there exists $t \in (0, 1)$ such that $x = L(t)$.
    obtain ⟨t, ht⟩ : ∃ t ∈ Set.Ioo 0 1, x = L t := by
      rcases hx with ⟨ a, b, ha, hb, hab, rfl ⟩ ; exact ⟨ b, ⟨ hb, by linarith ⟩, by simp +decide [ L, ← hab ] ⟩ ;
    -- Since $t \in (0, 1)$, we have $t_min < t < t_max$.
    have ht_bounds : t_min < t ∧ t < t_max := by
      constructor <;> contrapose! hyz;
      · have := ht_min.2 0 ?_ <;> simp_all +decide [ openSegment_eq_image ];
        · linarith;
        · aesop;
      · have := ht_max.2 1 ?_ <;> simp_all +decide;
        · linarith;
        · aesop;
    -- Since $t \in (t_min, t_max)$, we can write $t$ as a convex combination of $t_min$ and $t_max$.
    obtain ⟨s, hs⟩ : ∃ s ∈ Set.Ioo 0 1, t = (1 - s) * t_min + s * t_max := by
      exact ⟨ ( t - t_min ) / ( t_max - t_min ), ⟨ by rw [ lt_div_iff₀ ] <;> linarith, by rw [ div_lt_iff₀ ] <;> linarith ⟩, by linarith [ mul_div_cancel₀ ( t - t_min ) ( by linarith : ( t_max - t_min ) ≠ 0 ) ] ⟩;
    simp_all +decide [ openSegment_eq_image ];
    refine' ⟨ s, hs.1, _ ⟩ ; simp +decide [ L, smul_add, add_smul, mul_assoc, mul_left_comm, mul_add, add_mul, sub_mul, mul_sub ] ; ring;
    module

end Helpers

section InductiveProof

theorem minkowski_induction (d : ℕ) :
    ∀ (E : Type u) [inst1 : NormedAddCommGroup E] [inst2 : NormedSpace ℝ E]
      [inst3 : FiniteDimensional ℝ E],
    Module.finrank ℝ E ≤ d →
    ∀ (s : Set E), IsCompact s → Convex ℝ s →
    s ⊆ convexHull ℝ (s.extremePoints ℝ) := by
  induction d with
  | zero =>
    intro E _ _ _ hd s hscomp hsconv x hx
    have : Subsingleton E := by simp_all +decide [Module.finrank_zero_iff]
    exact subset_convexHull ℝ _ ⟨hx, fun y hy z hz _ => Subsingleton.elim _ _⟩
  | succ n ih =>
    intro E inst1 inst2 inst3 hd s hscomp hsconv x hx
    by_cases hxe : x ∈ s.extremePoints ℝ
    · exact subset_convexHull ℝ _ hxe
    · by_cases hint : (interior s).Nonempty
      · obtain ⟨a, b, ha, hb, ha_bdy, hb_bdy, hx_seg⟩ :=
          exists_boundary_segment hscomp hsconv hint hx hxe
        obtain ⟨ga, hga_ne, hga_sup⟩ :=
          exists_supporting_functional hscomp hsconv hint ha ha_bdy
        obtain ⟨gb, hgb_ne, hgb_sup⟩ :=
          exists_supporting_functional hscomp hsconv hint hb hb_bdy
        have ha_hull : a ∈ convexHull ℝ (s.extremePoints ℝ) :=
          convexHull_mono (isExtreme_exposedFace hsconv ga.toLinearMap (ga a) hga_sup).extremePoints_subset_extremePoints
            (Submission.MinkowskiHelpers.face_point_in_hull ga hga_ne a s hscomp hsconv hga_sup ha
              (fun V _ _ _ hV s' hs' hc' => ih V (by omega) s' hs' hc'))
        have hb_hull : b ∈ convexHull ℝ (s.extremePoints ℝ) :=
          convexHull_mono (isExtreme_exposedFace hsconv gb.toLinearMap (gb b) hgb_sup).extremePoints_subset_extremePoints
            (Submission.MinkowskiHelpers.face_point_in_hull gb hgb_ne b s hscomp hsconv hgb_sup hb
              (fun V _ _ _ hV s' hs' hc' => ih V (by omega) s' hs' hc'))
        exact (convex_convexHull ℝ _).openSegment_subset ha_hull hb_hull hx_seg
      · exact Submission.MinkowskiHelpers.minkowski_empty_interior n
          (fun V _ _ _ hV s' hs' hc' => ih V hV s' hs' hc')
          hd hscomp hsconv hint hx

theorem compact_convex_eq_convexHull_extremePoints
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (hscomp : IsCompact s) (hsconv : Convex ℝ s) :
    convexHull ℝ (s.extremePoints ℝ) = s := by
  apply le_antisymm
  · exact convexHull_min extremePoints_subset hsconv
  · exact @minkowski_induction (Module.finrank ℝ E) E _ _ _ le_rfl s hscomp hsconv

end InductiveProof

end Submission.Minkowski