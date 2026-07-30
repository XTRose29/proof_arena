import Submission.CenteredJoin

namespace Submission.Helpers

open LeanEval.Dynamics

/-- The centered orbit interval, reindexed from its left endpoint. -/
def centeredOrbit
    (T T_inv : EucPlane → EucPlane) (m n : ℕ) (x : EucPlane) :
    Fin (m + n) → EucPlane :=
  fun i => T^[i.val] (T_inv^[m] x)

lemma centeredOrbit_center
    (T T_inv : EucPlane → EucPlane)
    (hT_right : Function.RightInverse T_inv T)
    {m n : ℕ} (hn : 0 < n) (x : EucPlane) :
    centeredOrbit T T_inv m n x ⟨m, by omega⟩ = x := by
  simp only [centeredOrbit]
  exact hT_right.iterate m x

lemma centeredOrbit_left
    (T T_inv : EucPlane → EucPlane)
    {m n : ℕ} (hmn : 0 < m + n) (x : EucPlane) :
    centeredOrbit T T_inv m n x ⟨0, hmn⟩ = T_inv^[m] x := by
  simp [centeredOrbit]

lemma centeredOrbit_right
    (T T_inv : EucPlane → EucPlane)
    (hT_right : Function.RightInverse T_inv T)
    {m n : ℕ} (hn : 0 < n) (x : EucPlane) :
    centeredOrbit T T_inv m n x
        ⟨m + n - 1, by omega⟩ = T^[n - 1] x := by
  simp only [centeredOrbit]
  have hindex : m + n - 1 = m + (n - 1) := by omega
  rw [hindex, iterate_after_inverse_cancel hT_right]

lemma centeredOrbit_forward
    (T T_inv : EucPlane → EucPlane)
    {m n : ℕ} (x : EucPlane) (i : Fin (m + n)) (j : ℕ)
    (hij : i.val + j < m + n) :
    centeredOrbit T T_inv m n x ⟨i.val + j, hij⟩ =
      T^[j] (centeredOrbit T T_inv m n x i) := by
  simp only [centeredOrbit]
  rw [show i.val + j = j + i.val by omega, Function.iterate_add_apply]

lemma centeredOrbit_backward
    (T T_inv : EucPlane → EucPlane)
    (hT_left : Function.LeftInverse T_inv T)
    {m n : ℕ} (x : EucPlane) (i : Fin (m + n)) (j : ℕ)
    (hji : j ≤ i.val) :
    T_inv^[j] (centeredOrbit T T_inv m n x i) =
      centeredOrbit T T_inv m n x ⟨i.val - j, by omega⟩ := by
  simp only [centeredOrbit]
  conv_lhs =>
    rw [show i.val = j + (i.val - j) by omega,
      Function.iterate_add_apply]
  exact hT_left.iterate j _

lemma norm_centeredOrbit_sub_le_of_mem_centeredJoin_atom
    (T T_inv : EucPlane → EucPlane)
    (P : Finset (Set EucPlane))
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hP_diam : ∀ A ∈ P, Metric.ediam A ≤ ENNReal.ofReal delta)
    {m n : ℕ} {A : Set EucPlane}
    (hA : A ∈ centeredJoin T T_inv P m n)
    {x y : EucPlane} (hx : x ∈ A) (hy : y ∈ A)
    (i : Fin (m + n)) :
    ‖centeredOrbit T T_inv m n y i -
        centeredOrbit T T_inv m n x i‖ ≤ delta := by
  obtain ⟨B, hB, hxB, hyB⟩ :=
    exists_iteratedJoin_atom_of_mem_centeredJoin_atom T T_inv P hA hx hy
  have hclose := edist_iterate_le_of_mem_iteratedJoin_atom
    T P hP_diam hB hxB hyB i
  rw [edist_dist] at hclose
  have hdist :
      dist (centeredOrbit T T_inv m n x i)
        (centeredOrbit T T_inv m n y i) ≤ delta := by
    exact (ENNReal.ofReal_le_ofReal_iff hdelta).mp hclose
  simpa [dist_eq_norm, norm_sub_rev] using hdist

end Submission.Helpers
