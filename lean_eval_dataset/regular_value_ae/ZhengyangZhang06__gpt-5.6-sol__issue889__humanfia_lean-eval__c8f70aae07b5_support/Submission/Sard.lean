import Submission.Probe

open Filter MeasureTheory Module Set
open scoped ContDiff ENNReal NNReal Topology

namespace Submission.Helpers

set_option maxHeartbeats 1600000 in
lemma measure_image_criticalSet_eq_zero_on_open
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (d : ℕ) (f : E → ℝ) (s : Set E)
    (hd : finrank ℝ E = d) (hs : IsOpen s)
    (hf : ∀ x ∈ s, ContDiffAt ℝ (sardOrder d) f x) :
    volume (f '' (s ∩ CriticalSet f)) = 0 := by
  induction d using Nat.strong_induction_on generalizing E with
  | h d ih =>
      have hflat :
          volume (f '' (s ∩ JetZeroSet f (d + 1))) = 0 := by
        apply measure_image_jetZeroSet_eq_zero
        · omega
        · intro x hx
          exact (hf x hx.1).of_le (by
            exact_mod_cast dimension_succ_le_sardOrder d)
      have hstratum :
          ∀ k ∈ Set.Icc 1 d,
            volume
              (f '' (s ∩ (JetZeroSet f k \ JetZeroSet f (k + 1)))) = 0 := by
        intro k hk
        apply measure_image_eq_zero_of_locally
        intro x hx
        have hd_pos : 1 ≤ d := hk.1.trans hk.2
        have hk_zero : iteratedFDeriv ℝ k f x = 0 :=
          hx.2.1 k hk.1 le_rfl
        have hk_succ_ne : iteratedFDeriv ℝ (k + 1) f x ≠ 0 := by
          intro hk_succ
          apply hx.2.2
          intro j hj₁ hj
          by_cases hjk : j ≤ k
          · exact hx.2.1 j hj₁ hjk
          · have : j = k + 1 := by omega
            subst j
            exact hk_succ
        obtain ⟨g, hg, hg_zero, hg_deriv, hg_vanish⟩ :=
          exists_scalar_jet
            (E := E) (f := f) (x := x) (k := k)
            (m := sardOrder (d - 1)) (n := sardOrder d)
            (hf x hx.1)
            (by exact_mod_cast sardOrder_pos (d - 1))
            (by exact_mod_cast sardOrder_pred_add_le hd_pos hk.2)
            hk_zero hk_succ_ne
        obtain ⟨ψ, r, hψ, hr, hr_zero, hψ_zero, hparam⟩ :=
          exists_implicit_parametrization
            (E := E) (n := sardOrder (d - 1)) hg
            (by exact_mod_cast (sardOrder_pos (d - 1)).ne')
            hg_deriv
        have hψ_event :
            ∀ᶠ z in 𝓝 (0 : (fderiv ℝ g x).ker),
              ContDiffAt ℝ (sardOrder (d - 1)) ψ z :=
          hψ.eventually (by simp)
        have hs_mem : s ∈ 𝓝 (ψ 0) := by
          rw [hψ_zero]
          exact hs.mem_nhds hx.1
        have hψ_mem :
            ∀ᶠ z in 𝓝 (0 : (fderiv ℝ g x).ker), ψ z ∈ s :=
          hψ.continuousAt hs_mem
        obtain ⟨v, hv_sub, hv_open, hzero_v⟩ :=
          mem_nhds_iff.mp (hψ_event.and hψ_mem)
        have hchild_le : sardOrder (d - 1) ≤ sardOrder d := by
          simpa using
            (sardOrder_pred_add_le (d := d) (k := 0) hd_pos (Nat.zero_le d))
        have hcomp :
            ∀ z ∈ v, ContDiffAt ℝ (sardOrder (d - 1)) (f ∘ ψ) z := by
          intro z hz
          exact ((hf (ψ z) (hv_sub hz).2).of_le (by
            exact_mod_cast hchild_le)).comp z (hv_sub hz).1
        have hker_dim_add :
            finrank ℝ (fderiv ℝ g x).ker + 1 = finrank ℝ E := by
          exact Module.Dual.finrank_ker_add_one_of_ne_zero
            (f := (fderiv ℝ g x).toLinearMap) (by
              intro hzero
              apply hg_deriv
              ext y
              exact LinearMap.congr_fun hzero y)
        have hker_dim : finrank ℝ (fderiv ℝ g x).ker = d - 1 := by
          omega
        have hcritical_comp :
            volume
              ((f ∘ ψ) ''
                (v ∩ CriticalSet (f ∘ ψ))) = 0 :=
          ih (d - 1) (by omega) (E := (fderiv ℝ g x).ker)
            (f ∘ ψ) v hker_dim hv_open hcomp
        have hr_mem :
            ∀ᶠ y in 𝓝 x, r y ∈ v :=
          hr (hv_open.mem_nhds (by simpa only [hr_zero] using hzero_v))
        have hu_event :
            ∀ᶠ y in 𝓝 x,
              r y ∈ v ∧ (g y = g x → ψ (r y) = y) :=
          hr_mem.and hparam
        obtain ⟨u, hu_sub, hu_open, hx_u⟩ :=
          mem_nhds_iff.mp hu_event
        refine ⟨u, hu_open.mem_nhds hx_u, ?_⟩
        apply measure_mono_null _ hcritical_comp
        intro c hc
        obtain ⟨y, hy, rfl⟩ := hc
        have hy_data := hu_sub hy.2
        have hgy_zero : g y = 0 :=
          hg_vanish y (hy.1.2.1 k hk.1 le_rfl)
        have hgy : g y = g x := hgy_zero.trans hg_zero.symm
        have hψry : ψ (r y) = y := hy_data.2 hgy
        have hy_critical : fderiv ℝ f y = 0 := by
          change y ∈ CriticalSet f
          rw [criticalSet_eq_jetZeroSet_one]
          exact jetZeroSet_mono f hk.1 hy.1.2.1
        have hf_diff : DifferentiableAt ℝ f (ψ (r y)) := by
          rw [hψry]
          exact (hf y hy.1.1).differentiableAt (by
            exact_mod_cast (sardOrder_pos d).ne')
        have hψ_diff : DifferentiableAt ℝ ψ (r y) :=
          ((hv_sub hy_data.1).1).differentiableAt (by
            exact_mod_cast (sardOrder_pos (d - 1)).ne')
        have hcomp_deriv :
            HasFDerivAt (f ∘ ψ)
              ((fderiv ℝ f (ψ (r y))).comp (fderiv ℝ ψ (r y))) (r y) :=
          hf_diff.hasFDerivAt.comp (r y) hψ_diff.hasFDerivAt
        have hcomp_critical : r y ∈ CriticalSet (f ∘ ψ) := by
          change fderiv ℝ (f ∘ ψ) (r y) = 0
          rw [hcomp_deriv.fderiv, hψry, hy_critical]
          ext z
          simp
        refine ⟨r y, ⟨hy_data.1, hcomp_critical⟩, ?_⟩
        change f (ψ (r y)) = f y
        rw [hψry]
      have hstrata :
          volume
            (⋃ k, ⋃ _ : k ∈ Set.Icc 1 d,
              f '' (s ∩ (JetZeroSet f k \ JetZeroSet f (k + 1)))) = 0 :=
        measure_iUnion_null fun k ↦
          measure_iUnion_null fun hk ↦ hstratum k hk
      apply measure_mono_null _ (measure_union_null hflat hstrata)
      intro c hc
      obtain ⟨x, hx, rfl⟩ := hc
      have hx_one : x ∈ JetZeroSet f 1 := by
        rw [← criticalSet_eq_jetZeroSet_one]
        exact hx.2
      rcases jetZeroSet_one_subset_flat_or_strata f d hx_one with
        hx_flat | hx_stratum
      · exact Or.inl ⟨x, ⟨hx.1, hx_flat⟩, rfl⟩
      · right
        obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx_stratum
        apply mem_iUnion_of_mem k
        apply mem_iUnion_of_mem hk
        exact ⟨x, ⟨hx.1, hxk⟩, rfl⟩

lemma measure_image_criticalSet_eq_zero
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → ℝ) (hf : ContDiff ℝ ∞ f) :
    volume (f '' CriticalSet f) = 0 := by
  simpa only [univ_inter] using
    measure_image_criticalSet_eq_zero_on_open
      (finrank ℝ E) f univ rfl isOpen_univ
      (fun x _ ↦ hf.contDiffAt.of_le (by
        exact_mod_cast
          (show (sardOrder (finrank ℝ E) : ℕ∞) ≤ ⊤ from le_top)))

end Submission.Helpers
