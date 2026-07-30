import Submission.OmegaInvariant

open Filter Metric Set Topology
open scoped NNReal

open LeanEval.Dynamics

namespace Submission.PeriodicBranch

theorem omegaSet_eq_range_of_forward_periodic
    {γ β : ℝ → Plane} {a T : ℝ} (_ha : 0 ≤ a) (hT : 0 < T)
    (hβcont : Continuous β) (hperiodic : Function.Periodic β T)
    (hforward : ∀ t, 0 ≤ t → γ (a + t) = β t) :
    Helpers.omegaSet γ = range β := by
  have hrange_eq : range β = β '' Icc (0 : ℝ) T := by
    apply Subset.antisymm
    · rintro _ ⟨t, rfl⟩
      obtain ⟨u, hu, htu⟩ := hperiodic.exists_mem_Ico₀ hT t
      exact ⟨u, ⟨hu.1, hu.2.le⟩, htu.symm⟩
    · rintro _ ⟨t, _ht, rfl⟩
      exact ⟨t, rfl⟩
  have hrange_closed : IsClosed (range β) := by
    rw [hrange_eq]
    exact (isCompact_Icc.image hβcont).isClosed
  apply Subset.antisymm
  · refine (Helpers.omegaSet_subset_closure_image_Ici γ a).trans ?_
    apply closure_minimal
    · rintro _ ⟨t, ht, rfl⟩
      let u := t - a
      have hu : 0 ≤ u := sub_nonneg.mpr ht
      refine ⟨u, ?_⟩
      convert (hforward u hu).symm using 1
      dsimp only [u]
      ring_nf
    · exact hrange_closed
  · rintro x ⟨t, rfl⟩
    obtain ⟨u, hu, htu⟩ := hperiodic.exists_mem_Ico₀ hT t
    rw [Helpers.omegaSet, mem_iInter]
    intro s
    apply subset_closure
    obtain ⟨n, hn⟩ := exists_nat_ge ((s - a - u) / T)
    have hmul :
        s - a - u ≤ (n : ℝ) * T := by
      have := mul_le_mul_of_nonneg_right hn hT.le
      rwa [div_mul_cancel₀ _ hT.ne'] at this
    let q : ℝ := a + (u + (n : ℝ) * T)
    have hq : s ≤ q := by
      dsimp [q]
      linarith
    refine ⟨q, hq, ?_⟩
    have huq : 0 ≤ u + (n : ℝ) * T :=
      add_nonneg hu.1
        (mul_nonneg (Nat.cast_nonneg n) hT.le)
    calc
      γ q = β (u + (n : ℝ) * T) := by
        simpa [q] using hforward (u + (n : ℝ) * T) huq
      _ = β u := by
        simpa only [nsmul_eq_mul] using (hperiodic.nsmul n) u
      _ = β t := htu.symm

/-- If a bounded forward trajectory meets itself at two distinct
nonnegative times, its omega-limit set is already a periodic orbit (or
the repeated point is an equilibrium). -/
theorem equilibrium_or_periodic_of_eq
    (F : Plane → Plane) (hF : ContDiff ℝ 1 F)
    (γ : ℝ → Plane)
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ F x) (Ici 0))
    (hbounded : Bornology.IsBounded (γ '' Ici 0))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hγab : γ a = γ b) :
    (∃ x₀, F x₀ = 0 ∧ x₀ ∈ Helpers.omegaSet γ) ∨
      ∃ T : ℝ, 0 < T ∧ ∃ β : ℝ → Plane,
        IsIntegralCurve β (fun _ x ↦ F x) ∧
        Function.Periodic β T ∧
        F (β 0) ≠ 0 ∧
        Helpers.omegaSet γ = range β := by
  obtain ⟨G, K, hGcompact, hGdiff, hG, hEq⟩ :=
    Helpers.exists_compactlySupported_lipschitz_extension F hF hbounded
  obtain ⟨β, hβ0, hβ⟩ :=
    GlobalFlow.exists_global_integralCurve_of_compactSupport
      G hGcompact hGdiff (γ a)
  let T := b - a
  have hT : 0 < T := sub_pos.mpr hab
  have hforward (t : ℝ) (ht : 0 ≤ t) :
      γ (a + t) = β t := by
    apply dist_eq_zero.mp
    exact le_antisymm
      (OmegaInvariant.dist_shift_le hG γ β hγ hEq hβ hβ0 ha ht
        |>.trans_eq (by simp))
      dist_nonneg
  have hβT : β T = β 0 := by
    calc
      β T = γ (a + T) := (hforward T hT.le).symm
      _ = γ b := by simp [T]
      _ = γ a := hγab.symm
      _ = β 0 := hβ0.symm
  have hperiodic : Function.Periodic β T :=
    by
      simpa using
        (Helpers.integralCurve_periodic_of_eq_of_lipschitz
          (a := T) (b := 0) hG hβ hβT)
  have hrange : range β ⊆ γ '' Ici 0 := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨u, hu, htu⟩ := hperiodic.exists_mem_Ico₀ hT t
    refine ⟨a + u, add_nonneg ha hu.1, ?_⟩
    rw [hforward u hu.1]
    exact htu.symm
  have hβF : IsIntegralCurve β (fun _ x ↦ F x) := by
    intro t
    simpa only [hEq (hrange ⟨t, rfl⟩)] using hβ t
  have homega : Helpers.omegaSet γ = range β :=
    omegaSet_eq_range_of_forward_periodic ha hT hβ.continuous
      hperiodic hforward
  by_cases hzero : F (β 0) = 0
  · exact Or.inl ⟨β 0, hzero, homega.symm.subset ⟨0, rfl⟩⟩
  · exact Or.inr ⟨T, hT, β, hβF, hperiodic, hzero, homega⟩

theorem equilibrium_or_periodic_of_not_injOn
    (F : Plane → Plane) (hF : ContDiff ℝ 1 F)
    (γ : ℝ → Plane)
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ F x) (Ici 0))
    (hbounded : Bornology.IsBounded (γ '' Ici 0))
    (hinj : ¬ Set.InjOn γ (Ici 0)) :
    (∃ x₀, F x₀ = 0 ∧ x₀ ∈ Helpers.omegaSet γ) ∨
      ∃ T : ℝ, 0 < T ∧ ∃ β : ℝ → Plane,
        IsIntegralCurve β (fun _ x ↦ F x) ∧
        Function.Periodic β T ∧
        F (β 0) ≠ 0 ∧
        Helpers.omegaSet γ = range β := by
  rw [Set.injOn_iff_injective, Function.not_injective_iff] at hinj
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, heq, hne⟩ := hinj
  have habne : a ≠ b := by
    intro hab
    apply hne
    exact Subtype.ext hab
  rcases lt_or_gt_of_ne habne with hab | hba
  · exact equilibrium_or_periodic_of_eq F hF γ hγ hbounded
      ha hab heq
  · exact equilibrium_or_periodic_of_eq F hF γ hγ hbounded
      hb hba heq.symm

end Submission.PeriodicBranch
