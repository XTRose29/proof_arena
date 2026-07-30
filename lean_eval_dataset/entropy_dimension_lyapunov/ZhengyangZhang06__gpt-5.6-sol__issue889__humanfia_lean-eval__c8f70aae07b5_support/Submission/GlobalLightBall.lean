import Submission.GlobalOrbitGeometry

namespace Submission.Helpers

open LeanEval.Dynamics
open MeasureTheory

lemma measure_closedBall_le_exp_neg_of_mem_light_centered_atom_global
    (mu : Measure EucPlane) [IsFiniteMeasure mu]
    (T T_inv : EucPlane → EucPlane)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K s : Set EucPlane} (hsK : s ⊆ K)
    (hmu_s : mu sᶜ = 0) (hK_inv : T '' K = K) (hs_invariant : T '' s = s)
    {p : ℕ} (center : Fin p → EucPlane) (radius : Fin p → ℝ)
    (P : Finset (Set EucPlane))
    (hstable : ∀ {u v}, u ∈ s → v ∈ s →
      (∀ i, u ∈ Metric.ball (center i) (radius i) ↔
        v ∈ Metric.ball (center i) (radius i)) →
      ∀ A ∈ P, u ∈ A ↔ v ∈ A)
    {C D delta c : ℝ} (hC : 1 ≤ C) (hD : 1 ≤ D) (hdelta : 0 < delta)
    (hforward_lipschitz :
      ∀ x ∈ K, ∀ y ∈ K, dist (T x) (T y) ≤ C * dist x y)
    (hbackward_lipschitz :
      ∀ x ∈ K, ∀ y ∈ K, dist (T_inv x) (T_inv y) ≤ D * dist x y)
    {m n : ℕ} {x : EucPlane}
    (hxs : x ∈ s)
    (hxlight : x ∈ ⋃ A ∈ lightAtoms mu (centeredJoin T T_inv P m n) c, A)
    (havoid : x ∉ centeredBoundaryBadReal
      T T_inv center radius delta m n) :
    mu (Metric.closedBall x
      (delta / (2 * max (C ^ n) (D ^ m)))) ≤
        ENNReal.ofReal (Real.exp (-c)) := by
  classical
  obtain ⟨A, hxA⟩ := Set.mem_iUnion.mp hxlight
  obtain ⟨hAlight, hxA⟩ := Set.mem_iUnion.mp hxA
  have hAjoin : A ∈ centeredJoin T T_inv P m n :=
    (Finset.mem_filter.mp hAlight).1
  have hAmeasure : mu.real A < Real.exp (-c) :=
    (Finset.mem_filter.mp hAlight).2
  have hmax_pos : 0 < max (C ^ n) (D ^ m) :=
    lt_of_lt_of_le (pow_pos (lt_of_lt_of_le zero_lt_one hC) n) (le_max_left _ _)
  have hradius_lt :
      delta / (2 * max (C ^ n) (D ^ m)) <
        delta / max (C ^ n) (D ^ m) := by
    rw [div_lt_div_iff₀ (mul_pos zero_lt_two hmax_pos) hmax_pos]
    nlinarith
  have hsubset :
      Metric.closedBall x (delta / (2 * max (C ^ n) (D ^ m))) ∩ s ⊆ A := by
    intro y hy
    apply mem_centeredJoin_atom_of_dist_lt_global_radius
      T T_inv hT_left hT_right hsK hK_inv hs_invariant center radius P hstable
        hC hD hdelta hforward_lipschitz hbackward_lipschitz
        hAjoin hxA hxs hy.2 havoid
    rw [dist_comm]
    exact (Metric.mem_closedBall.mp hy.1).trans_lt hradius_lt
  calc
    mu (Metric.closedBall x (delta / (2 * max (C ^ n) (D ^ m)))) =
        mu (Metric.closedBall x (delta / (2 * max (C ^ n) (D ^ m))) ∩ s) :=
      (measure_inter_eq_of_compl_eq_zero mu hmu_s _).symm
    _ ≤ mu A := measure_mono hsubset
    _ = ENNReal.ofReal (mu.real A) := (ofReal_measureReal).symm
    _ ≤ ENNReal.ofReal (Real.exp (-c)) :=
      ENNReal.ofReal_le_ofReal hAmeasure.le

end Submission.Helpers
