import Submission.BoundaryAvoidance

namespace Submission.Helpers

open LeanEval.Dynamics

lemma mem_centeredJoin_atom_of_orbit_close_avoiding_boundaries
    (T T_inv : EucPlane → EucPlane)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {s : Set EucPlane} (hs_invariant : T '' s = s)
    {p : ℕ} (center : Fin p → EucPlane) (radius : Fin p → ℝ)
    (P : Finset (Set EucPlane))
    (hstable : ∀ {u v}, u ∈ s → v ∈ s →
      (∀ i, u ∈ Metric.ball (center i) (radius i) ↔
        v ∈ Metric.ball (center i) (radius i)) →
      ∀ C ∈ P, u ∈ C ↔ v ∈ C)
    {k m n : ℕ} {x y : EucPlane} {A : Set EucPlane}
    (hA : A ∈ centeredJoin T T_inv P m n) (hxA : x ∈ A)
    (hxs : x ∈ s) (hys : y ∈ s)
    (havoid : x ∉ centeredBoundaryBad T T_inv center radius k m n)
    (hforward : ∀ j : Fin n,
      dist (T^[j.val] x) (T^[j.val] y) < 1 / ((k : ℝ) + 1))
    (hbackward : ∀ q, 0 < q → q ≤ m →
      dist (T_inv^[q] x) (T_inv^[q] y) < 1 / ((k : ℝ) + 1)) :
    y ∈ A := by
  classical
  have hs_inv : T_inv '' s = s :=
    inverse_image_eq_of_image_eq hT_left hs_invariant
  have hT_mem {z : EucPlane} (hz : z ∈ s) (j : ℕ) : T^[j] z ∈ s := by
    rw [← image_iterate_eq_of_image_eq T hs_invariant j]
    exact ⟨z, hz, rfl⟩
  have hT_inv_mem {z : EucPlane} (hz : z ∈ s) (q : ℕ) : T_inv^[q] z ∈ s := by
    rw [← image_iterate_eq_of_image_eq T_inv hs_inv q]
    exact ⟨z, hz, rfl⟩
  have hnot_forward (j : Fin n) :
      T^[j.val] x ∉ ballBoundaryNeighborhood center radius k := by
    intro hj
    apply havoid
    apply Set.mem_union_left
    exact Set.mem_iUnion_of_mem j hj
  have hnot_backward (q : ℕ) (hq_pos : 0 < q) (hq_le : q ≤ m) :
      T_inv^[q] x ∉ ballBoundaryNeighborhood center radius k := by
    intro hq
    let iq : Fin m := ⟨q - 1, by omega⟩
    have hiq : iq.val + 1 = q := by
      dsimp [iq]
      omega
    apply havoid
    apply Set.mem_union_right
    apply Set.mem_iUnion_of_mem iq
    simpa [hiq] using hq
  rw [centeredJoin, preimagePartition] at hA
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
  change T_inv^[m] y ∈ B
  change T_inv^[m] x ∈ B at hxA
  rw [iteratedJoin] at hB
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hB
  apply Set.mem_iInter.mpr
  intro i
  have hfi : f i ∈ P := Fintype.mem_piFinset.mp hf i
  have hxi := Set.mem_iInter.mp hxA i
  change T^[i.val] (T_inv^[m] x) ∈ f i at hxi
  change T^[i.val] (T_inv^[m] y) ∈ f i
  by_cases hi : i.val < m
  · let q := m - i.val
    have hq_pos : 0 < q := by omega
    have hq_le : q ≤ m := Nat.sub_le _ _
    have hiq : m - q = i.val := by omega
    rw [← hiq, iterate_sub_inverse_cancel hT_right hq_le] at hxi ⊢
    apply (hstable (hT_inv_mem hxs q) (hT_inv_mem hys q) ?_ (f i) hfi).mp hxi
    intro a
    exact mem_ball_iff_of_dist_lt_boundaryNeighborhood center radius
      (hnot_backward q hq_pos hq_le) (hbackward q hq_pos hq_le) a
  · have hmi : m ≤ i.val := le_of_not_gt hi
    let j := i.val - m
    have hj_lt : j < n := by omega
    let jf : Fin n := ⟨j, hj_lt⟩
    have hij : m + jf.val = i.val := by
      dsimp [jf, j]
      omega
    rw [← hij, iterate_after_inverse_cancel hT_right] at hxi ⊢
    apply (hstable (hT_mem hxs jf.val) (hT_mem hys jf.val) ?_ (f i) hfi).mp hxi
    intro a
    exact mem_ball_iff_of_dist_lt_boundaryNeighborhood center radius
      (hnot_forward jf) (hforward jf) a

end Submission.Helpers
