import Submission.WeightedBoundaryAvoidance

namespace Submission.Helpers

open LeanEval.Dynamics

lemma mem_ball_iff_of_dist_lt_boundaryNeighborhoodReal
    {M : Type*} [PseudoMetricSpace M] {p : ℕ}
    (center : Fin p → M) (radius : Fin p → ℝ)
    {delta : ℝ} {x y : M}
    (hx : x ∉ ballBoundaryNeighborhoodReal center radius delta)
    (hxy : dist x y < delta) (i : Fin p) :
    x ∈ Metric.ball (center i) (radius i) ↔
      y ∈ Metric.ball (center i) (radius i) := by
  have hmargin : delta < |dist x (center i) - radius i| := by
    apply lt_of_not_ge
    intro hnear
    apply hx
    exact Set.mem_iUnion_of_mem i hnear
  constructor
  · intro hxball
    rw [Metric.mem_ball] at hxball ⊢
    by_contra hyball
    have hyradius : radius i ≤ dist y (center i) := le_of_not_gt hyball
    have hxradius : dist x (center i) ≤ radius i := hxball.le
    rw [abs_of_nonpos (sub_nonpos.mpr hxradius)] at hmargin
    have hdiff : dist y (center i) - dist x (center i) ≤ dist x y := by
      calc
        dist y (center i) - dist x (center i) ≤
            |dist y (center i) - dist x (center i)| := le_abs_self _
        _ ≤ dist y x := abs_dist_sub_le y x (center i)
        _ = dist x y := dist_comm _ _
    linarith
  · intro hyball
    rw [Metric.mem_ball] at hyball ⊢
    by_contra hxball
    have hxradii : radius i ≤ dist x (center i) := le_of_not_gt hxball
    rw [abs_of_nonneg (sub_nonneg.mpr hxradii)] at hmargin
    have hdiff : dist x (center i) - dist y (center i) ≤ dist x y := by
      calc
        dist x (center i) - dist y (center i) ≤
            |dist x (center i) - dist y (center i)| := le_abs_self _
        _ ≤ dist x y := abs_dist_sub_le x y (center i)
    linarith

lemma mem_centeredJoin_atom_of_orbit_close_avoiding_boundariesReal
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
    {delta : ℝ} {m n : ℕ} {x y : EucPlane} {A : Set EucPlane}
    (hA : A ∈ centeredJoin T T_inv P m n) (hxA : x ∈ A)
    (hxs : x ∈ s) (hys : y ∈ s)
    (havoid : x ∉ centeredBoundaryBadReal
      T T_inv center radius delta m n)
    (hforward : ∀ j : Fin n,
      dist (T^[j.val] x) (T^[j.val] y) < delta)
    (hbackward : ∀ q, 0 < q → q ≤ m →
      dist (T_inv^[q] x) (T_inv^[q] y) < delta) :
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
      T^[j.val] x ∉ ballBoundaryNeighborhoodReal center radius delta := by
    intro hj
    apply havoid
    apply Set.mem_union_left
    exact Set.mem_iUnion_of_mem j hj
  have hnot_backward (q : ℕ) (hq_pos : 0 < q) (hq_le : q ≤ m) :
      T_inv^[q] x ∉ ballBoundaryNeighborhoodReal center radius delta := by
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
    exact mem_ball_iff_of_dist_lt_boundaryNeighborhoodReal center radius
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
    exact mem_ball_iff_of_dist_lt_boundaryNeighborhoodReal center radius
      (hnot_forward jf) (hforward jf) a

end Submission.Helpers
