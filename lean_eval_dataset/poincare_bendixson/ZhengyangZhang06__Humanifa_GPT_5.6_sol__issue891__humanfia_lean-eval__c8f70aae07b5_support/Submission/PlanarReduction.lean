import Submission.PeriodicFromSection

open Filter Metric Set Topology
open scoped NNReal

open LeanEval.Dynamics

namespace Submission.PlanarReduction

noncomputable section

/-- Local uniqueness of omega-limit points on every short transversal reduces
the regular compact invariant case to one periodic orbit. -/
theorem exists_periodic_range_eq
    {G : Plane → Plane} {K : ℝ≥0}
    (hGcompact : HasCompactSupport G) (hGcont : Continuous G)
    (hG : LipschitzWith K G)
    {Φ : Plane → ℝ → Plane}
    (hΦ0 : ∀ x, Φ x 0 = x)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (fun _ y ↦ G y))
    {A : Set Plane} (hAcompact : IsCompact A) (hAne : A.Nonempty)
    (hApre : IsPreconnected A)
    (hAinv : ∀ x ∈ A, ∀ t, Φ x t ∈ A)
    (hregular : ∀ x ∈ A, G x ≠ 0)
    (hsection : ∀ q ∈ A, ∃ R : ℝ, 0 < R ∧
      ∀ z ∈ A, z ∈ ball q R →
        Transversal.transverseValue (G q) q z = 0 → z = q) :
    ∃ T : ℝ, 0 < T ∧ ∃ p ∈ A,
      Function.Periodic (Φ p) T ∧ A = range (Φ p) := by
  obtain ⟨p, hpA⟩ := hAne
  have hforward : Φ p '' Ici (0 : ℝ) ⊆ A := by
    rintro _ ⟨t, _ht, rfl⟩
    exact hAinv p hpA t
  have hbounded : Bornology.IsBounded (Φ p '' Ici (0 : ℝ)) :=
    hAcompact.isBounded.subset hforward
  obtain ⟨q, hqomega⟩ := Helpers.omegaSet_nonempty (Φ p) hbounded
  have hqA : q ∈ A := by
    apply closure_minimal hforward hAcompact.isClosed
    exact Helpers.omegaSet_subset_closure_image_Ici (Φ p) 0 hqomega
  have hqcluster : MapClusterPt q atTop (Φ p) :=
    (Helpers.mem_omegaSet_iff_mapClusterPt (Φ p) q).mp hqomega
  obtain ⟨T, hT, hperiodic⟩ :=
    PeriodicFromSection.periodic_of_cluster_and_section_unique
      hGcompact hGcont hG hΦ0 hΦ hAinv hpA
      (hregular q hqA) hqcluster (hsection q hqA)
  let C : Set Plane := range (Φ p)
  have hCsub : C ⊆ A := by
    rintro _ ⟨t, rfl⟩
    exact hAinv p hpA t
  have hpC : p ∈ C := ⟨0, hΦ0 p⟩
  have hCcompact : IsCompact C := by
    exact hperiodic.compact_of_continuous hT.ne' (hΦ p).continuous
  have hlocal :
      ∀ x ∈ C, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ∩ A ⊆ C := by
    intro x hxC
    have hxA := hCsub hxC
    obtain ⟨R, hR, hxsection⟩ := hsection x hxA
    obtain ⟨δ, hδ, ρ, hρ, hcross⟩ :=
      FlowBox.exists_unique_transverse_time
        hGcompact hGcont hG hΦ0 hΦ (hregular x hxA) hR
    refine ⟨ρ, hρ, ?_⟩
    rintro y ⟨hynear, hyA⟩
    obtain ⟨u, hu, _hunique⟩ := hcross y hynear
    have hflowA : Φ y u ∈ A := hAinv y hyA u
    have hflowx : Φ y u = x :=
      hxsection _ hflowA hu.2.1 hu.2.2.1
    have hyback : Φ x (-u) = y := by
      calc
        Φ x (-u) = Φ (Φ y u) (-u) := by rw [hflowx]
        _ = Φ y (u + -u) :=
          (GlobalFlow.globalFlow_add hG hΦ0 hΦ y u (-u)).symm
        _ = y := by simp only [add_neg_cancel, hΦ0]
    obtain ⟨s, hs⟩ := hxC
    refine ⟨s - u, ?_⟩
    calc
      Φ p (s - u) = Φ p (s + -u) := by rw [sub_eq_add_neg]
      _ = Φ (Φ p s) (-u) :=
        GlobalFlow.globalFlow_add hG hΦ0 hΦ p s (-u)
      _ = Φ x (-u) := by rw [hs]
      _ = y := hyback
  let U : Set Plane :=
    {y | ∃ x ∈ C, ∃ ρ : ℝ, 0 < ρ ∧
      ball x ρ ∩ A ⊆ C ∧ y ∈ ball x ρ}
  have hUopen : IsOpen U := by
    rw [isOpen_iff_forall_mem_open]
    intro y hy
    obtain ⟨x, hxC, ρ, hρ, hxlocal, hyball⟩ := hy
    refine ⟨ball x ρ, ?_, isOpen_ball, hyball⟩
    intro z hz
    exact ⟨x, hxC, ρ, hρ, hxlocal, hz⟩
  have hCsubU : C ⊆ U := by
    intro x hxC
    obtain ⟨ρ, hρ, hxlocal⟩ := hlocal x hxC
    exact ⟨x, hxC, ρ, hρ, hxlocal, mem_ball_self hρ⟩
  have hAUsubC : A ∩ U ⊆ C := by
    rintro y ⟨hyA, hyU⟩
    obtain ⟨x, _hxC, ρ, _hρ, hxlocal, hyball⟩ := hyU
    exact hxlocal ⟨hyball, hyA⟩
  have hAsubC : A ⊆ C := by
    by_contra hnot
    obtain ⟨z, hzA, hzC⟩ := not_subset.mp hnot
    have hcover : A ⊆ U ∪ Cᶜ := by
      intro y hyA
      by_cases hyC : y ∈ C
      · exact Or.inl (hCsubU hyC)
      · exact Or.inr hyC
    have hleft : (A ∩ U).Nonempty :=
      ⟨p, hpA, hCsubU hpC⟩
    have hright : (A ∩ Cᶜ).Nonempty :=
      ⟨z, hzA, hzC⟩
    obtain ⟨w, hwA, hwU, hwC⟩ :=
      hApre U Cᶜ hUopen hCcompact.isClosed.isOpen_compl
        hcover hleft hright
    exact hwC (hAUsubC ⟨hwA, hwU⟩)
  exact
    ⟨T, hT, p, hpA, hperiodic,
      Subset.antisymm hAsubC hCsub⟩

end

end Submission.PlanarReduction
