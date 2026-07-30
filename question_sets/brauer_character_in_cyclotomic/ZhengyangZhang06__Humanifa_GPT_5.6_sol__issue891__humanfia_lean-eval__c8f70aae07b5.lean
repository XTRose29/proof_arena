import Mathlib
import Submission.Helpers

namespace Submission

open Polynomial

theorem brauer_character_in_cyclotomic (G : Type) [Group G] [Fintype G] :
    ∃ φ : CyclotomicField (Monoid.exponent G) ℚ →+* ℂ,
      ∀ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
        (ρ : Representation ℂ G V) (g : G),
        LinearMap.trace ℂ V (ρ g) ∈ φ.range := by
  let n := Monoid.exponent G
  let p : ℚ[X] := X ^ n - 1
  letI : NeZero n := by
    dsimp [n]
    infer_instance
  letI : NeZero (n : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne n)⟩
  letI : IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) :=
    CyclotomicField.isCyclotomicExtension n ℚ
  letI : Polynomial.IsSplittingField ℚ (CyclotomicField n ℚ) p := by
    dsimp [p]
    exact IsCyclotomicExtension.isSplittingField_X_pow_sub_one n ℚ _
  let i : CyclotomicField n ℚ →ₐ[ℚ] ℂ :=
    Polynomial.IsSplittingField.lift (CyclotomicField n ℚ) p (IsAlgClosed.splits _)
  refine ⟨i.toRingHom, ?_⟩
  intro V _ _ _ ρ g
  change LinearMap.trace ℂ V (ρ g) ∈ i.range
  rw [← Polynomial.IsSplittingField.adjoin_rootSet_eq_range
    (CyclotomicField n ℚ) p i]
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  apply (Algebra.adjoin ℚ (p.rootSet ℂ)).multiset_sum_mem
  intro μ hμ
  apply Algebra.subset_adjoin
  rw [Polynomial.mem_rootSet_of_ne]
  · have hρ : (ρ g) ^ n = 1 := by
      simpa [n] using congrArg ρ (Monoid.pow_exponent_eq_one g)
    have hEigen : Module.End.HasEigenvalue (ρ g) μ :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly (ρ g) μ).2
        (Polynomial.isRoot_of_mem_roots hμ)
    obtain ⟨v, hv⟩ := hEigen.exists_hasEigenvector
    have hvpow : v = μ ^ n • v := by
      simpa [hρ] using hv.pow_apply n
    have hμpow : μ ^ n = 1 :=
      ((smul_left_injective ℂ hv.2) (by simpa using hvpow)).symm
    simp [p, hμpow]
  · dsimp [p]
    simpa using Polynomial.X_pow_sub_C_ne_zero (NeZero.pos n) (1 : ℚ)

end Submission
