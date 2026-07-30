import Mathlib

open scoped BigOperators
open Fintype Set
open Module

namespace Submission.Helpers

noncomputable section

set_option maxHeartbeats 4000000 in
/-- The finite colorful Carathéodory theorem, in exactly the Euclidean
form needed for Sarkaria's proof of Tverberg's theorem. -/
theorem colorful_caratheodory {η κ : Type*} [Fintype η] [Fintype κ] [Nonempty κ]
    (a : Fin (Fintype.card η + 1) → κ → EuclideanSpace ℝ η)
    (ha : ∀ i, 0 ∈ convexHull ℝ (Set.range (a i))) :
    ∃ choose : Fin (Fintype.card η + 1) → κ,
      0 ∈ convexHull ℝ (Set.range fun i ↦ a i (choose i)) := by
  classical
  cases isEmpty_or_nonempty η with
  | inl hη =>
      letI : IsEmpty η := hη
      let choose : Fin (Fintype.card η + 1) → κ := fun _ ↦ Classical.choice inferInstance
      refine ⟨choose, (subset_convexHull ℝ _) ?_⟩
      refine ⟨0, ?_⟩
      ext i
      exact isEmptyElim i
  | inr hη =>
      letI : Nonempty η := hη
      let K : Set (EuclideanSpace ℝ η) :=
        ⋃ choose : Fin (Fintype.card η + 1) → κ,
          convexHull ℝ (Set.range fun i ↦ a i (choose i))
      have hK_compact : IsCompact K := by
        exact isCompact_iUnion fun choose ↦
          (Set.finite_range fun i ↦ a i (choose i)).isCompact_convexHull ℝ
      have hK_nonempty : K.Nonempty := by
        let choose : Fin (Fintype.card η + 1) → κ := fun _ ↦ Classical.choice inferInstance
        refine ⟨a 0 (choose 0), ?_⟩
        exact Set.mem_iUnion_of_mem choose
          ((subset_convexHull ℝ _) ⟨0, rfl⟩)
      obtain ⟨x, hxK, hx_min⟩ :=
        hK_compact.exists_isMinOn hK_nonempty continuous_norm.continuousOn
      obtain ⟨choose, hx_choose⟩ :
          ∃ choose : Fin (Fintype.card η + 1) → κ,
            x ∈ convexHull ℝ (Set.range fun i ↦ a i (choose i)) := by
        simpa only [K, Set.mem_iUnion] using hxK
      by_cases hx : x = 0
      · exact ⟨choose, hx ▸ hx_choose⟩
      have hx_le (y : EuclideanSpace ℝ η)
          (hy : y ∈ convexHull ℝ (Set.range fun i ↦ a i (choose i))) :
          ‖x‖ ≤ ‖y‖ := by
        exact hx_min (Set.mem_iUnion_of_mem choose hy)
      letI : Nonempty
          {y // y ∈ convexHull ℝ (Set.range fun i ↦ a i (choose i))} :=
        ⟨⟨x, hx_choose⟩⟩
      have hx_inf :
          ‖(0 : EuclideanSpace ℝ η) - x‖ =
            ⨅ y : {y // y ∈ convexHull ℝ (Set.range fun i ↦ a i (choose i))},
              ‖(0 : EuclideanSpace ℝ η) - (y : EuclideanSpace ℝ η)‖ := by
        simp only [zero_sub, norm_neg]
        apply le_antisymm
        · exact le_ciInf fun y ↦ hx_le y y.property
        ·
          have h_bdd : BddBelow (Set.range fun y :
              {y // y ∈ convexHull ℝ (Set.range fun i ↦ a i (choose i))} ↦
                ‖(y : EuclideanSpace ℝ η)‖) := by
            refine ⟨0, ?_⟩
            rintro _ ⟨y, rfl⟩
            exact norm_nonneg (y : EuclideanSpace ℝ η)
          exact ciInf_le h_bdd ⟨x, hx_choose⟩
      have hx_support (y : EuclideanSpace ℝ η)
          (hy : y ∈ convexHull ℝ (Set.range fun i ↦ a i (choose i))) :
          0 ≤ inner ℝ x (y - x) := by
        have h := (norm_eq_iInf_iff_real_inner_le_zero
          (convex_convexHull ℝ _) hx_choose).1 hx_inf y hy
        simp only [zero_sub, inner_neg_left] at h
        linarith
      obtain ⟨ι, hι, z, w, hz_range, hz_independent, hw_pos, hw_sum, hw_center⟩ :=
        eq_pos_convex_span_of_mem_convexHull hx_choose
      letI : Fintype ι := hι
      letI : Nonempty ι := by
        by_contra hι_empty
        haveI : IsEmpty ι := not_nonempty_iff.mp hι_empty
        simp at hw_sum
      have hz_support (i : ι) : 0 ≤ inner ℝ x (z i - x) := by
        apply hx_support
        exact (subset_convexHull ℝ _) (hz_range ⟨i, rfl⟩)
      have hsum_support : ∑ i, w i * inner ℝ x (z i - x) = 0 := by
        calc
          ∑ i, w i * inner ℝ x (z i - x) =
              inner ℝ x (∑ i, w i • (z i - x)) := by
                simp only [inner_sum, inner_smul_right]
          _ = inner ℝ x ((∑ i, w i • z i) - (∑ i, w i) • x) := by
                congr 1
                simp_rw [smul_sub]
                rw [Finset.sum_sub_distrib, Finset.sum_smul]
          _ = 0 := by rw [hw_center, hw_sum]; simp
      have hz_hyperplane (i : ι) : inner ℝ x (z i - x) = 0 := by
        have hterm : w i * inner ℝ x (z i - x) = 0 :=
          congrFun ((Fintype.sum_eq_zero_iff_of_nonneg fun j ↦
            mul_nonneg (hw_pos j).le (hz_support j)).mp hsum_support) i
        exact (mul_eq_zero.mp hterm).resolve_left (hw_pos i).ne'
      let H : AffineSubspace ℝ (EuclideanSpace ℝ η) :=
        AffineSubspace.mk' x ((ℝ ∙ x)ᗮ)
      have hz_H : Set.range z ⊆ (H : Set (EuclideanSpace ℝ η)) := by
        rintro _ ⟨i, rfl⟩
        change z i ∈ AffineSubspace.mk' x ((ℝ ∙ x)ᗮ)
        rw [AffineSubspace.mem_mk', vsub_eq_sub,
          Submodule.mem_orthogonal_singleton_iff_inner_right]
        exact hz_hyperplane i
      have hspan : vectorSpan ℝ (Set.range z) ≤ (ℝ ∙ x)ᗮ := by
        calc
          vectorSpan ℝ (Set.range z) ≤ vectorSpan ℝ (H : Set (EuclideanSpace ℝ η)) :=
            vectorSpan_mono ℝ hz_H
          _ = H.direction := H.direction_eq_vectorSpan.symm
          _ = (ℝ ∙ x)ᗮ := by simp [H]
      letI : Fact (finrank ℝ (EuclideanSpace ℝ η) =
          (Fintype.card η - 1) + 1) := ⟨by
        simp only [finrank_euclideanSpace]
        have hη_card := Fintype.card_pos (α := η)
        omega⟩
      have horthogonal :
          finrank ℝ ((ℝ ∙ x)ᗮ) = Fintype.card η - 1 :=
        Submodule.finrank_orthogonal_span_singleton hx
      have hcard : Fintype.card ι ≤ Fintype.card η := by
        calc
          Fintype.card ι =
              finrank ℝ (vectorSpan ℝ (Set.range z)) + 1 :=
            hz_independent.finrank_vectorSpan_add_one.symm
          _ ≤ finrank ℝ ((ℝ ∙ x)ᗮ) + 1 :=
            Nat.add_le_add_right (Submodule.finrank_mono hspan) 1
          _ = Fintype.card η := by
            rw [horthogonal]
            exact Nat.sub_add_cancel Fintype.card_pos
      choose source hsource using fun i ↦ hz_range (Set.mem_range_self i)
      have hsource_not_surjective :
          ¬Function.Surjective (source : ι → Fin (Fintype.card η + 1)) := by
        intro hs
        have := Fintype.card_le_of_surjective source hs
        simp only [Fintype.card_fin] at this
        omega
      obtain ⟨missing, hmissing⟩ :
          ∃ missing : Fin (Fintype.card η + 1), ∀ i, source i ≠ missing := by
        simpa only [Function.Surjective, not_forall, not_exists,
          Classical.not_not] using hsource_not_surjective
      have hother : ∃ k : κ, inner ℝ x (a missing k) ≤ 0 := by
        by_contra h
        push Not at h
        have hsubset :
            Set.range (a missing) ⊆
              {y : EuclideanSpace ℝ η | 0 < inner ℝ x y} := by
          rintro _ ⟨k, rfl⟩
          exact h k
        have hlinear : IsLinearMap ℝ (fun y : EuclideanSpace ℝ η ↦ inner ℝ x y) :=
          .mk (inner_add_right x) (by
            intro c y
            simp only [inner_smul_right, smul_eq_mul])
        have hzero_pos : (0 : EuclideanSpace ℝ η) ∈
            {y : EuclideanSpace ℝ η | 0 < inner ℝ x y} :=
          convexHull_min hsubset (convex_halfSpace_gt hlinear 0) (ha missing)
        simp at hzero_pos
      obtain ⟨other, hother⟩ := hother
      let choose' : Fin (Fintype.card η + 1) → κ :=
        Function.update choose missing other
      have hz_range' :
          Set.range z ⊆ Set.range (fun i ↦ a i (choose' i)) := by
        rintro _ ⟨i, rfl⟩
        refine ⟨source i, ?_⟩
        simp only [choose', Function.update_of_ne (hmissing i)]
        exact hsource i
      have hx_choose' :
          x ∈ convexHull ℝ (Set.range fun i ↦ a i (choose' i)) := by
        apply mem_convexHull_of_exists_fintype w z
        · exact fun i ↦ (hw_pos i).le
        · exact hw_sum
        · exact fun i ↦ hz_range' (Set.mem_range_self i)
        · exact hw_center
      have hother_choose' :
          a missing other ∈ convexHull ℝ (Set.range fun i ↦ a i (choose' i)) := by
        exact (subset_convexHull ℝ _) ⟨missing, by
          simp only [choose', Function.update_self]⟩
      let delta : EuclideanSpace ℝ η := a missing other - x
      have hinner_delta : inner ℝ x delta < 0 := by
        change inner ℝ x (a missing other - x) < 0
        rw [inner_sub_right, real_inner_self_eq_norm_sq]
        have hxnorm : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
        linarith
      have hdelta : delta ≠ 0 := by
        intro h
        rw [h, inner_zero_right] at hinner_delta
        exact lt_irrefl 0 hinner_delta
      let t : ℝ := min 1 (-inner ℝ x delta / ‖delta‖ ^ 2)
      have ht_pos : 0 < t := by
        apply lt_min zero_lt_one
        exact div_pos (neg_pos.mpr hinner_delta) (sq_pos_of_pos (norm_pos_iff.mpr hdelta))
      have ht_one : t ≤ 1 := min_le_left _ _
      have ht_bound : t * ‖delta‖ ^ 2 ≤ -inner ℝ x delta := by
        have := min_le_right (1 : ℝ) (-inner ℝ x delta / ‖delta‖ ^ 2)
        apply (le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hdelta))).mp
        exact this
      let y : EuclideanSpace ℝ η := x + t • delta
      have hy_choose' :
          y ∈ convexHull ℝ (Set.range fun i ↦ a i (choose' i)) := by
        have hcombo := (convex_convexHull ℝ
          (Set.range fun i ↦ a i (choose' i))) hx_choose' hother_choose'
          (sub_nonneg.mpr ht_one) ht_pos.le (by ring)
        convert hcombo using 1
        all_goals
          (simp [y, delta, sub_smul]; module)
      have hy_norm : ‖y‖ < ‖x‖ := by
        have hfactor :
            t * (2 * inner ℝ x delta + t * ‖delta‖ ^ 2) < 0 := by
          apply mul_neg_of_pos_of_neg ht_pos
          linarith
        have hsquares : ‖y‖ ^ 2 < ‖x‖ ^ 2 := by
          change ‖x + t • delta‖ ^ 2 < ‖x‖ ^ 2
          rw [norm_add_sq_real, inner_smul_right, norm_smul]
          rw [Real.norm_eq_abs, abs_of_pos ht_pos]
          nlinarith
        nlinarith [norm_nonneg y, norm_nonneg x]
      have hx_le_y : ‖x‖ ≤ ‖y‖ := hx_min
        (Set.mem_iUnion_of_mem choose' hy_choose')
      exact False.elim ((not_lt_of_ge hx_le_y) hy_norm)

end

end Submission.Helpers
