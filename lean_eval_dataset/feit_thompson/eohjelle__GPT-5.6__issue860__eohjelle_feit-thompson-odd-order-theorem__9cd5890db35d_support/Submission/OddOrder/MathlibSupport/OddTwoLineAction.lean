import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
Odd-order groups cannot swap a pair of complementary lines.
-/

namespace Submission.OddOrder.MathlibSupport

variable {F G V : Type*} [Field F] [Group G]
  [AddCommGroup V] [Module F V]

/-- Every element of a finite odd-order group is a power of its square. -/
theorem exists_eq_sq_pow_of_odd_natCard
    (hodd : Odd (Nat.card G)) (y : G) :
    ∃ k : ℕ, y = (y ^ 2) ^ k := by
  have hyodd : Odd (orderOf y) :=
    Odd.of_dvd_nat hodd (orderOf_dvd_natCard y)
  obtain ⟨k, hk⟩ := hyodd
  refine ⟨k + 1, ?_⟩
  rw [← pow_mul]
  rw [show 2 * (k + 1) = orderOf y + 1 by omega, pow_succ,
    pow_orderOf_eq_one, one_mul]

/-- Taking the underlying endomorphism commutes with natural powers of a
linear equivalence. -/
theorem linearEquiv_toLinearMap_pow (e : V ≃ₗ[F] V) (n : ℕ) :
    (e ^ n).toLinearMap = e.toLinearMap ^ n := by
  induction n with
  | zero => simp [Module.End.one_eq_id]
  | succ n ih => rw [pow_succ, pow_succ, LinearEquiv.coe_toLinearMap_mul, ih]

/-- If an odd-order group action permutes two complementary one-dimensional
subspaces, then it fixes both subspaces individually. -/
theorem odd_action_preserves_complementary_lines
    [FiniteDimensional F V]
    (hodd : Odd (Nat.card G)) (phi : G →* (V ≃ₗ[F] V))
    (U W : Submodule F V) (hcompl : IsCompl U W)
    (hUdim : Module.finrank F U = 1)
    (hWdim : Module.finrank F W = 1)
    (hUperm : ∀ y : G,
      U.map (phi y).toLinearMap ≤ U ∨ U.map (phi y).toLinearMap ≤ W)
    (hWperm : ∀ y : G,
      W.map (phi y).toLinearMap ≤ U ∨ W.map (phi y).toLinearMap ≤ W) :
    ∀ y : G,
      U.map (phi y).toLinearMap = U ∧
        W.map (phi y).toLinearMap = W := by
  have hUWne : U ≠ W := by
    intro hUW
    have hUbot : U = ⊥ := by
      apply disjoint_self.mp
      exact hUW ▸ hcompl.disjoint
    rw [hUbot, finrank_bot] at hUdim
    omega
  intro y
  let e := phi y
  have hUmapdim : Module.finrank F (U.map e.toLinearMap) = 1 :=
    (e.finrank_map_eq U).trans hUdim
  have hWmapdim : Module.finrank F (W.map e.toLinearMap) = 1 :=
    (e.finrank_map_eq W).trans hWdim
  have hUeq : U.map e.toLinearMap = U ∨ U.map e.toLinearMap = W := by
    rcases hUperm y with hle | hle
    · exact Or.inl (Submodule.eq_of_le_of_finrank_eq hle
        (hUmapdim.trans hUdim.symm))
    · exact Or.inr (Submodule.eq_of_le_of_finrank_eq hle
        (hUmapdim.trans hWdim.symm))
  have hWeq : W.map e.toLinearMap = U ∨ W.map e.toLinearMap = W := by
    rcases hWperm y with hle | hle
    · exact Or.inl (Submodule.eq_of_le_of_finrank_eq hle
        (hWmapdim.trans hUdim.symm))
    · exact Or.inr (Submodule.eq_of_le_of_finrank_eq hle
        (hWmapdim.trans hWdim.symm))
  have hUfixed : U.map e.toLinearMap = U := by
    rcases hUeq with hUfixed | hUswap
    · exact hUfixed
    · have hWswap : W.map e.toLinearMap = U := by
        rcases hWeq with hWswap | hWfixed
        · exact hWswap
        · exfalso
          apply hUWne
          apply Submodule.map_injective_of_injective e.injective
          rw [hUswap, hWfixed]
      have hE2 : U ≤ U.comap (e.toLinearMap ^ 2) := by
        intro u hu
        have hEuW : e u ∈ W := by
          rw [← hUswap]
          exact Submodule.mem_map_of_mem hu
        have hEEuU : e (e u) ∈ U := by
          rw [← hWswap]
          exact Submodule.mem_map_of_mem hEuW
        simpa [pow_two, Module.End.mul_apply] using hEEuU
      obtain ⟨k, hyk⟩ := exists_eq_sq_pow_of_odd_natCard hodd y
      have heq : e = (e ^ 2) ^ k := by
        change phi y = (phi y ^ 2) ^ k
        calc
          phi y = phi ((y ^ 2) ^ k) := congrArg phi hyk
          _ = (phi (y ^ 2)) ^ k := map_pow phi (y ^ 2) k
          _ = (phi y ^ 2) ^ k := by rw [map_pow]
      have hlin : e.toLinearMap = (e.toLinearMap ^ 2) ^ k := by
        calc
          e.toLinearMap = ((e ^ 2) ^ k).toLinearMap :=
            congrArg (fun q : V ≃ₗ[F] V => q.toLinearMap) heq
          _ = (e ^ 2).toLinearMap ^ k := linearEquiv_toLinearMap_pow _ _
          _ = (e.toLinearMap ^ 2) ^ k := by rw [linearEquiv_toLinearMap_pow]
      have hpowInv := U.le_comap_pow_of_le_comap hE2 k
      rw [← hlin] at hpowInv
      have hmaple : U.map e.toLinearMap ≤ U :=
        Submodule.map_le_iff_le_comap.mpr hpowInv
      rw [hUswap] at hmaple
      exfalso
      apply hUWne
      exact (Submodule.eq_of_le_of_finrank_eq hmaple
        (hWdim.trans hUdim.symm)).symm
  refine ⟨hUfixed, ?_⟩
  rcases hWeq with hWswap | hWfixed
  · exfalso
    apply hUWne
    apply Submodule.map_injective_of_injective e.injective
    rw [hUfixed, hWswap]
  · exact hWfixed

end Submission.OddOrder.MathlibSupport
