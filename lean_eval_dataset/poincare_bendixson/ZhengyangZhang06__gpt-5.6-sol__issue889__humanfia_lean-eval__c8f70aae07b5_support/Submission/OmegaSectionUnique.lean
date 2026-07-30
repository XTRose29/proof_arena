import Submission.SectionHitFamily
import Submission.SectionOrder

open Filter Function Metric Set Topology
open scoped NNReal

open LeanEval.Dynamics

namespace Submission.OmegaSectionUnique

noncomputable section

/-- In the injective forward-orbit branch, every regular omega-limit point
has a short affine transversal on which it is the only omega-limit point. -/
theorem exists_radius_unique
    {F G : Plane → Plane} {K : ℝ≥0}
    (hGcompact : HasCompactSupport G) (hGcont : Continuous G)
    (hG : LipschitzWith K G) (γ : ℝ → Plane)
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ F x) (Ici 0))
    (hEq : EqOn G F (γ '' Ici 0))
    (hγinj : InjOn γ (Ici (0 : ℝ)))
    {Φ : Plane → ℝ → Plane}
    (hΦ0 : ∀ x, Φ x 0 = x)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (fun _ y ↦ G y))
    {q : Plane} (hqOmega : q ∈ Helpers.omegaSet γ)
    (hqreg : G q ≠ 0) :
    ∃ R : ℝ, 0 < R ∧
      ∀ z ∈ Helpers.omegaSet γ,
        z ∈ ball q R →
        Transversal.transverseValue (G q) q z = 0 →
          z = q := by
  let v := G q
  have hv : v ≠ 0 := hqreg
  obtain ⟨r, hr, hvel⟩ :=
    Transversal.exists_ball_velocityValue_pos hGcont hqreg
  let d : ℝ := r / (4 * (‖v‖ + 1))
  have hd : 0 < d := by
    dsimp only [d]
    positivity
  obtain ⟨ρ, hρ, hhits⟩ :=
    SectionHitFamily.exists_radius_exact_hits_near_section
      hGcompact hGcont hG γ hγ hEq hΦ0 hΦ hqreg
  have hcoordNhds :
      {z : Plane |
          Transversal.sectionValue v q z ∈ Ioo (-d / 4) (d / 4)}
        ∈ 𝓝 q := by
    have hzero :
        Transversal.sectionValue v q q = 0 := by
      simp [Transversal.sectionValue]
    have hopen : Ioo (-d / 4) (d / 4) ∈
        𝓝 (Transversal.sectionValue v q q) := by
      rw [hzero]
      exact Ioo_mem_nhds (by linarith [hd]) (by linarith [hd])
    exact
      (Transversal.continuous_sectionValue v q).continuousAt.eventually hopen
  obtain ⟨rcoord, hrcoord, hrcoordSub⟩ :=
    Metric.mem_nhds_iff.mp hcoordNhds
  let R : ℝ := min ρ rcoord
  have hR : 0 < R := lt_min hρ hrcoord
  refine ⟨R, hR, ?_⟩
  intro z hzOmega hzBall hzLine
  change dist z q < R at hzBall
  have hzρ : z ∈ ball q ρ := by
    change dist z q < ρ
    exact hzBall.trans_le (min_le_left _ _)
  have hzcoord :
      Transversal.sectionValue v q z ∈ Ioo (-d / 4) (d / 4) := by
    apply hrcoordSub
    change dist z q < rcoord
    exact hzBall.trans_le (min_le_right _ _)
  let U := Transversal.sectionValue v q z
  have hzSection : z = Transversal.sectionPoint v q U := by
    exact (Transversal.sectionPoint_sectionValue hv
      (by simpa only [v] using hzLine)).symm
  by_cases hU : U = 0
  · rw [hzSection, hU, Transversal.sectionPoint_zero]
  have hUwindow : U ∈ Ioo (-d / 4) (d / 4) := by
    simpa only [U] using hzcoord
  obtain ⟨σQ, hσQnonneg, hσQ, hγQ, hhitQ⟩ :=
    hhits hqOmega (mem_ball_self hρ)
      (by
        simp [Transversal.transverseValue])
  obtain ⟨σU, hσUnonneg, hσU, hγU, hhitU⟩ :=
    hhits hzOmega hzρ (by simpa only [v] using hzLine)
  let β : ℝ → Plane := Φ (γ 0)
  have hβ : IsIntegralCurve β (fun _ y ↦ G y) := hΦ (γ 0)
  have hβeq (t : ℝ) (ht : 0 ≤ t) : β t = γ t := by
    simpa only [β, zero_add] using
      SectionHits.globalFlow_eq_shift hG γ hγ hEq hΦ0 hΦ
        (τ := 0) (u := t) le_rfl
          (by simpa only [zero_add] using ht)
  have hβinj : InjOn β (Ici (0 : ℝ)) := by
    intro x hx y hy hxy
    apply hγinj hx hy
    rw [← hβeq x hx, ← hβeq y hy]
    exact hxy
  have hβQ :
      Tendsto (β ∘ σQ) atTop
        (𝓝 (Transversal.sectionPoint v q 0)) := by
    have heq : β ∘ σQ = γ ∘ σQ := by
      funext n
      exact hβeq (σQ n) (hσQnonneg n)
    rw [heq]
    simpa only [Transversal.sectionPoint_zero] using hγQ
  have hβU :
      Tendsto (β ∘ σU) atTop
        (𝓝 (Transversal.sectionPoint v q U)) := by
    have heq : β ∘ σU = γ ∘ σU := by
      funext n
      exact hβeq (σU n) (hσUnonneg n)
    rw [heq]
    simpa only [← hzSection] using hγU
  have hβhitQ (n : ℕ) :
      Transversal.transverseValue v q (β (σQ n)) = 0 := by
    rw [hβeq (σQ n) (hσQnonneg n)]
    simpa only [v] using hhitQ n
  have hβhitU (n : ℕ) :
      Transversal.transverseValue v q (β (σU n)) = 0 := by
    rw [hβeq (σU n) (hσUnonneg n)]
    simpa only [v] using hhitU n
  have hsectionBall :
      ∀ u ∈ Icc (-d) d,
        Transversal.sectionPoint v q u ∈ ball q r := by
    intro u hu
    have huAbs : |u - 0| ≤ r / (4 * (‖v‖ + 1)) := by
      simpa only [sub_zero, d] using (abs_le.mpr hu)
    simpa only [zero_smul, add_zero,
      Transversal.sectionPoint_zero] using
      ExteriorComponents.offset_mem_ball_of_abs_bounds
        (v := v) (base := q) (u := u) (a := 0)
        (c := 0) hr
          (by
            rw [abs_zero]
            exact div_nonneg hr.le (by positivity))
          huAbs
  have hpositive :
      ∀ u ∈ Icc (-d) d,
        0 <
          Transversal.transverseFunctional v
            (G (Transversal.sectionPoint v q u)) := by
    intro u hu
    exact
      (half_pos zero_lt_one).trans
        (by
          simpa only [v, Transversal.velocityValue] using
            hvel (Transversal.sectionPoint v q u)
              (hsectionBall u hu))
  exfalso
  rcases lt_or_gt_of_ne hU with hUneg | hUpos
  · exact
      SectionOrder.no_two_ordered_section_cluster_points
        β hβ hβinj hv rfl
        (L := -d) (Q := U) (m := U / 2)
        (U := 0) (R := d)
        (by linarith [hUwindow.1, hd])
        (by linarith)
        (by linarith)
        hd hpositive
        hσU hβU hβhitU hσQ hβQ hβhitQ
  · exact
      SectionOrder.no_two_ordered_section_cluster_points
        β hβ hβinj hv rfl
        (L := -d) (Q := 0) (m := U / 2)
        (U := U) (R := d)
        (by linarith [hd])
        (by linarith)
        (by linarith)
        (by linarith [hUwindow.2, hd])
        hpositive
        hσQ hβQ hβhitQ hσU hβU hβhitU

end

end Submission.OmegaSectionUnique
