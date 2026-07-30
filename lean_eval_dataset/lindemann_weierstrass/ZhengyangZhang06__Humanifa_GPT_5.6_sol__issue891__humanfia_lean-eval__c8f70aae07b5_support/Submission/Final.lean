import Submission.Galois

namespace Submission.Final

noncomputable section

set_option maxHeartbeats 0

private theorem algebraicIndependent_exp_of_integral {ι : Type*} [Finite ι]
    (x : ι → ℂ) (hx : ∀ i, IsIntegral ℤ (x i))
    (hli : LinearIndependent ℚ x) :
    AlgebraicIndependent ℚ (fun i ↦ Complex.exp (x i)) := by
  letI : Algebra.IsAlgebraic ℤ ℚ :=
    IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have hZ : AlgebraicIndependent ℤ (fun i ↦ Complex.exp (x i)) := by
    rw [algebraicIndependent_iff]
    intro q hq
    by_contra hq0
    exact Submission.Galois.no_relation_of_integral x hx hli q hq0 hq
  exact (Algebra.IsAlgebraic.algebraicIndependent_iff ℤ ℚ).mp hZ

theorem algebraicIndependent_exp_of_algebraic {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (hx : ∀ i, IsAlgebraic ℚ (x i))
    (hli : LinearIndependent ℚ x) :
    AlgebraicIndependent ℚ (fun i ↦ Complex.exp (x i)) := by
  letI : Algebra.IsAlgebraic ℤ ℚ :=
    IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  choose d hd hdint using fun i ↦
    ((hx i).restrictScalars ℤ).exists_integral_multiple
  let m : ι → ℕ := fun i ↦ (d i).natAbs
  have hm : ∀ i, 0 < m i := fun i ↦ Int.natAbs_pos.mpr (hd i)
  let a : ι → ℂ := fun i ↦ m i • x i
  have haint : ∀ i, IsIntegral ℤ (a i) := by
    intro i
    have h := (hdint i).smul (d i).sign
    rw [← mul_smul, Int.sign_mul_self_eq_natAbs] at h
    simpa [a, m, Nat.cast_smul_eq_nsmul] using h
  let w : ι → ℚˣ := fun i ↦ Units.mk0 (m i : ℚ) (by
    exact_mod_cast (Nat.ne_of_gt (hm i)))
  have hali : LinearIndependent ℚ a := by
    convert hli.units_smul w using 1
    funext i
    simp [a, w, Nat.cast_smul_eq_nsmul]
  have haexp : AlgebraicIndependent ℚ (fun i ↦ Complex.exp (a i)) :=
    algebraicIndependent_exp_of_integral a haint hali
  apply Submission.Galois.algebraicIndependent_of_generators_of_finite
    (fun i ↦ Complex.exp (x i)) (fun i ↦ Complex.exp (a i)) haexp
  intro i
  rw [show Complex.exp (a i) = Complex.exp (x i) ^ m i by
    simpa [a] using Complex.exp_nsmul (x i) (m i)]
  exact (Algebra.adjoin ℚ (Set.range fun i ↦ Complex.exp (x i))).pow_mem
    (Algebra.subset_adjoin (Set.mem_range_self i)) _

end

end Submission.Final
