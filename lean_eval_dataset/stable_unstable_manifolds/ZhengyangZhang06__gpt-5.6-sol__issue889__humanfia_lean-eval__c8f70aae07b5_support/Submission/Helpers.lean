import Mathlib

namespace Submission.Helpers

open Filter Function
open scoped Topology

/-- A strict local Lyapunov function rules out nontrivial orbits which converge
to the same fixed point in both time directions. -/
theorem stable_inter_unstable_eq_singleton_of_strict_lyapunov
    {α : Type*} [TopologicalSpace α] [T2Space α]
    (f : α → α) (x₀ : α) (U : Set α) (V : α → ℝ)
    (hfix : f x₀ = x₀) (hx₀U : x₀ ∈ U) (hV : ContinuousAt V x₀)
    (hstrict : ∀ x ∈ U, x ≠ x₀ → V x < V (f x)) :
    {x | (∀ k : ℕ, f^[k] x ∈ U) ∧
          Tendsto (fun k => f^[k] x) atTop (𝓝 x₀)} ∩
        {x | ∃ y : ℕ → α,
          y 0 = x ∧
          (∀ k : ℕ, y k ∈ U) ∧
          (∀ k : ℕ, f (y (k + 1)) = y k) ∧
          Tendsto y atTop (𝓝 x₀)} =
      {x₀} := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hstay, hforward⟩, y, hy₀, hystay, hyback, hyforward⟩
    by_contra hx
    have hmono : Monotone (fun k : ℕ => V (f^[k] x)) :=
      monotone_nat_of_le_succ fun k => by
        by_cases hk : f^[k] x = x₀
        · simp [Function.iterate_succ_apply', hk, hfix]
        · rw [Function.iterate_succ_apply']
          exact (hstrict _ (hstay k) hk).le
    have hx_lt : V x < V x₀ := by
      calc
        V x < V (f x) := hstrict x (by simpa using hstay 0) hx
        _ = V (f^[1] x) := by simp
        _ ≤ V x₀ := hmono.ge_of_tendsto (hV.tendsto.comp hforward) 1
    have hanti : Antitone (fun k : ℕ => V (y k)) :=
      antitone_nat_of_succ_le fun k => by
        by_cases hk : y (k + 1) = x₀
        · have hk' : y k = x₀ := by
            rw [← hyback k, hk, hfix]
          simp [hk, hk']
        · calc
            V (y (k + 1)) ≤ V (f (y (k + 1))) :=
              (hstrict _ (hystay (k + 1)) hk).le
            _ = V (y k) := congrArg V (hyback k)
    have hx₀_le : V x₀ ≤ V x := by
      simpa [hy₀] using
        hanti.le_of_tendsto (hV.tendsto.comp hyforward) 0
    exact (not_lt_of_ge hx₀_le) hx_lt
  · intro hx
    subst x
    constructor
    · constructor
      · intro k
        simpa [Function.iterate_fixed hfix] using hx₀U
      · simpa only [Function.iterate_fixed hfix] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => x₀) atTop (𝓝 x₀))
    · refine ⟨fun _ => x₀, rfl, ?_, ?_, tendsto_const_nhds⟩
      · exact fun _ => hx₀U
      · exact fun _ => hfix

/-- A continuous, quadratically homogeneous Lyapunov function for the
linearization remains strictly increasing for the nonlinear map on a
sufficiently small neighbourhood. -/
theorem exists_strict_lyapunov_neighborhood
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    (f : F → F) (x₀ : F) (A : F →L[ℝ] F)
    (hf : HasFDerivAt f A x₀) (hfix : f x₀ = x₀)
    (q : F → ℝ) (hq : Continuous q)
    (hq_smul : ∀ (r : ℝ), 0 ≤ r → ∀ v, q (r • v) = r ^ 2 * q v)
    (hlinear : ∀ v ≠ 0, q v < q (A v)) :
    ∃ U : Set F, IsOpen U ∧ x₀ ∈ U ∧
      ∀ x ∈ U, x ≠ x₀ → q (x - x₀) < q (f x - x₀) := by
  let K : Set (F × F) := Metric.sphere (0 : F) 1 ×ˢ ({0} : Set F)
  let H : F × F → ℝ := fun p => q (A p.1 + p.2) - q p.1
  have hH : Continuous H := by
    dsimp [H]
    fun_prop
  have hK : IsCompact K :=
    (isCompact_sphere (0 : F) 1).prod isCompact_singleton
  have hKpos : K ⊆ {p | 0 < H p} := by
    rintro ⟨u, e⟩ ⟨hu, he⟩
    have he₀ : e = 0 := by simpa using he
    subst e
    have hu_norm : ‖u‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hu
    have hu_ne : u ≠ 0 := by
      intro hu₀
      simp [hu₀] at hu_norm
    change 0 < H (u, 0)
    simpa [H] using sub_pos.mpr (hlinear u hu_ne)
  have hHopen : IsOpen {p | 0 < H p} := isOpen_lt continuous_const hH
  obtain ⟨δ, hδ, hδsub⟩ :=
    hK.exists_cthickening_subset_open hHopen hKpos
  have hrem :
      ∀ᶠ x in 𝓝 x₀,
        ‖f x - f x₀ - A (x - x₀)‖ ≤ δ * ‖x - x₀‖ :=
    hf.isLittleO.bound hδ
  have hlocal :
      ∀ᶠ x in 𝓝 x₀,
        x ≠ x₀ → q (x - x₀) < q (f x - x₀) := by
    filter_upwards [hrem] with x hxrem
    intro hx
    let v : F := x - x₀
    let r : ℝ := ‖v‖
    let u : F := r⁻¹ • v
    let rem : F := f x - f x₀ - A v
    let e : F := r⁻¹ • rem
    have hv_ne : v ≠ 0 := sub_ne_zero.mpr hx
    have hr : 0 < r := by simpa [r] using norm_pos_iff.mpr hv_ne
    have hr_ne : r ≠ 0 := ne_of_gt hr
    have hu_norm : ‖u‖ = 1 := by
      change ‖r⁻¹ • v‖ = 1
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr,
        inv_mul_cancel₀ hr_ne]
    have he_norm : ‖e‖ ≤ δ := by
      calc
        ‖e‖ = r⁻¹ * ‖rem‖ := by
          change ‖r⁻¹ • rem‖ = r⁻¹ * ‖rem‖
          rw [norm_smul, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hr)]
        _ ≤ r⁻¹ * (δ * r) := by
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hr.le)
          simpa [rem, v, r] using hxrem
        _ = δ := by
          field_simp
    have hbase : (u, (0 : F)) ∈ K := by
      exact ⟨by simpa [Metric.mem_sphere, dist_eq_norm] using hu_norm, Set.mem_singleton 0⟩
    have hnear : (u, e) ∈ Metric.cthickening δ K := by
      apply Metric.mem_cthickening_of_dist_le (u, e) (u, 0) δ K hbase
      simpa [dist_prod_same_left, dist_zero_right] using he_norm
    have hpos : 0 < H (u, e) := hδsub hnear
    have hv_scale : r • u = v := by
      simp [u, hr_ne]
    have hrem_scale : r • e = rem := by
      simp [e, hr_ne]
    have himage_scale : r • (A u + e) = f x - x₀ := by
      rw [smul_add, ← A.map_smul, hv_scale, hrem_scale]
      simp [rem, v, hfix]
    have hr_sq : 0 < r ^ 2 := sq_pos_of_pos hr
    have hscaled :
        r ^ 2 * q u < r ^ 2 * q (A u + e) :=
      mul_lt_mul_of_pos_left
        (sub_pos.mp (by simpa [H] using hpos)) hr_sq
    calc
      q (x - x₀) = q (r • u) := by rw [hv_scale]
      _ = r ^ 2 * q u := hq_smul r hr.le u
      _ < r ^ 2 * q (A u + e) := hscaled
      _ = q (r • (A u + e)) := (hq_smul r hr.le (A u + e)).symm
      _ = q (f x - x₀) := by rw [himage_scale]
  rcases mem_nhds_iff.mp hlocal with ⟨U, hUsub, hUopen, hx₀U⟩
  exact ⟨U, hUopen, hx₀U, fun x hxU => hUsub hxU⟩

end Submission.Helpers
