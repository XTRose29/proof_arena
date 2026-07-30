import Submission.Exchange
import Submission.Geometry
import Submission.Hall

open LeanEval.Dynamics.LaxApproximation
open MeasureTheory Set
open scoped ENNReal

namespace Submission

open Helpers Grid Geometry

theorem lax_approximation {d : ℕ} (hd : 0 < d) (T : ToralDynamicalSystem d)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (n : ℕ) (S : VolumePreservingEquiv d),
      IsCyclicCubeExchange S n ∧ deltaDist T.toVolumePreservingEquiv S < ε := by
  obtain ⟨ρ, hρ, hρε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
  have hρ' : 0 < (ρ : ℝ) := by
    exact_mod_cast hρ
  have huc : UniformContinuous T.toHomeomorph :=
    CompactSpace.uniformContinuous_of_continuous T.toHomeomorph.continuous
  obtain ⟨δ, hδ, hTδ⟩ := (Metric.uniformContinuous_iff.mp huc) ((ρ : ℝ) / 2) (by positivity)
  let τ : ℝ := min δ ((ρ : ℝ) / 2)
  have hτ : 0 < τ := lt_min hδ (by positivity)
  let C : ℝ := 4 * d + 1
  have hC : 0 < C := by positivity
  obtain ⟨m, hm⟩ := exists_nat_gt (C / τ)
  have hm' : 0 < (m : ℝ) := (div_pos hC hτ).trans hm
  have hmNat : 0 < m := by exact_mod_cast hm'
  have hn : 0 < m * 2 := Nat.mul_pos hmNat (by norm_num)
  have hCmt : C < (m : ℝ) * τ := (div_lt_iff₀ hτ).mp hm
  have hmesh : C / (m * 2 : ℕ) < τ := by
    push_cast
    apply (div_lt_iff₀ (mul_pos hm' (by norm_num))).2
    nlinarith
  have hsource : (2 * (2 * d : ℕ) + 1 : ℝ) / (m * 2 : ℕ) < δ := by
    calc
      (2 * (2 * d : ℕ) + 1 : ℝ) / (m * 2 : ℕ) = C / (m * 2 : ℕ) := by
        simp only [C]
        push_cast
        ring
      _ < τ := hmesh
      _ ≤ δ := min_le_left _ _
  have hcell : 1 / (m * 2 : ℕ) < (ρ : ℝ) / 2 := by
    have hC1 : (1 : ℝ) ≤ C := by
      have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      dsimp only [C]
      nlinarith
    have hle : (1 : ℝ) / (m * 2 : ℕ) ≤ C / (m * 2 : ℕ) := by
      exact div_le_div_of_nonneg_right hC1 (by positivity)
    exact hle.trans_lt (hmesh.trans_le (min_le_right _ _))
  obtain ⟨p, hp⟩ := exists_grid_matching (m * 2) hn T
  let q := cyclicize p
  have hqcycle := cyclicize_isCycle_support hd hmNat p
  obtain ⟨r, hq, hr⟩ := cyclicize_factor_steps p
  let S := cubeExchange (m * 2) hn q
  refine ⟨m * 2, S, ?_, ?_⟩
  · refine ⟨q, hqcycle.1, hqcycle.2, ?_⟩
    intro k x hx i
    exact cubeExchange_apply_of_mem_cube (m * 2) hn q k x hx i
  · change essSup (fun x => edist (T.toHomeomorph x) (S.toMeasurableEquiv x))
        (volume : Measure (Torus d)) < ε
    refine lt_of_le_of_lt (essSup_le_of_ae_le (ρ : ℝ≥0∞) ?_) hρε
    exact Filter.Eventually.of_forall fun x => by
      let k := gridIndex (m * 2) hn x
      obtain ⟨y, ⟨⟨z, hz, rfl⟩, hy⟩⟩ := hp (r k)
      have hxzBound := dist_mem_cubes_of_steps (m * 2) hn (hr k)
        (mem_cube_gridIndex (m * 2) hn x) hz
      have hxz : dist x z < δ := hxzBound.trans_lt hsource
      have hTclose : dist (T.toHomeomorph x) (T.toHomeomorph z) < (ρ : ℝ) / 2 := hTδ hxz
      have hqk : q k = p (r k) := by
        rw [show q = p * r by exact hq, Equiv.Perm.mul_apply]
      have hSx : S.toMeasurableEquiv x ∈ cube (m * 2) (p (r k)) := by
        change cubeExchangeMap (m * 2) hn q x ∈ cube (m * 2) (p (r k))
        rw [← hqk]
        exact cubeExchangeMap_mem_cube (m * 2) hn q x
      have htarget : dist (T.toHomeomorph z) (S.toMeasurableEquiv x) < (ρ : ℝ) / 2 :=
        (dist_mem_same_cube (m * 2) hn hy hSx).trans_lt hcell
      have hpoint : dist (T.toHomeomorph x) (S.toMeasurableEquiv x) < (ρ : ℝ) := by
        calc
          dist (T.toHomeomorph x) (S.toMeasurableEquiv x) ≤
              dist (T.toHomeomorph x) (T.toHomeomorph z) +
                dist (T.toHomeomorph z) (S.toMeasurableEquiv x) := dist_triangle _ _ _
          _ < (ρ : ℝ) / 2 + (ρ : ℝ) / 2 := add_lt_add hTclose htarget
          _ = (ρ : ℝ) := by ring
      change edist (T.toHomeomorph x) (S.toMeasurableEquiv x) ≤ (ρ : ℝ≥0∞)
      rw [edist_dist]
      exact ENNReal.ofReal_le_coe.mpr hpoint.le

end Submission
