import Submission.OddOrder.BG.Section03.FrobeniusZeroInvariants
import Submission.OddOrder.BG.Section03.OddPrimeSemidirectIrreducibleReduction
import Submission.OddOrder.MathlibSupport.AbelianPerfectPrimeAction
import Submission.OddOrder.MathlibSupport.FaithfulIrreducibleCenter

/-!
The faithful irreducible branch of Bender-Glauberman Theorem 3.4 reduces to
the nonabelian prime-power kernel case.  The faithful representation also
makes the ambient center cyclic, as required in the extraspecial reduction.
-/

namespace Submission.OddOrder.BG.Section03

open Submission.OddOrder.MathlibSupport

universe u v w

variable {G : Type u} [Group G] [Fintype G]
variable {K R : Subgroup G}
variable {k : Type v} [Field k]
variable {V : Type w} [AddCommGroup V] [Module k V] [Finite V]

noncomputable section

/-- The abelian perfect-action branch is Frobenius, contradicting the zero
complement-fixed space of a faithful representation. -/
theorem false_of_abelian_faithful_prime_action
    [IsMulCommutative K]
    (sigma : Representation k G V)
    (hsigma : Function.Injective sigma)
    (hKR : K.IsComplement' R)
    (hnormK : R ≤ Subgroup.normalizer (K : Set G))
    (hRprime : (Nat.card R).Prime)
    (hGcard : (Nat.card G : k) ≠ 0)
    (hperfect : ⁅R, K⁆ = K)
    (hKne : K ≠ ⊥)
    (hfix : Representation.invariants
      (sigma.comp R.subtype : Representation k R V) = ⊥) :
    False := by
  letI : K.Normal :=
    normal_left_of_isComplement'_of_right_le_normalizer hKR hnormK
  have hRne : R ≠ ⊥ := by
    intro hRbot
    apply hRprime.ne_one
    simp [hRbot]
  let hfrob : IsFrobeniusDecomposition K R :=
    { isComplement := hKR
      kernel_normal := inferInstance
      kernel_ne_bot := hKne
      complement_ne_bot := hRne
      fixedPointFree := fun r hr x hx ↦
        fixed_eq_one_of_abelian_perfect_prime_action
          hnormK hRprime hperfect r hr x hx }
  have hKcard : (Nat.card K : k) ≠ 0 :=
    IsFrobeniusDecomposition.subgroup_natCard_cast_ne_zero_of_group_natCard_cast_ne_zero
      K hGcard
  have hKker : K ≤ sigma.ker :=
    hfrob.kernel_le_representation_ker_of_invariants_eq_bot sigma hKcard hfix
  apply hKne
  rw [sigma.ker_eq_bot hsigma] at hKker
  exact le_bot_iff.mp hKker

/-- All elementary reductions leave a nonabelian prime-power kernel, a
faithful irreducible representation, and a cyclic ambient center. -/
theorem kernel_commutator_le_representation_ker_of_nonabelian_cases
    [IsSolvable G]
    (rho : Representation k G V)
    (hKR : K.IsComplement' R)
    (hnormK : R ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card K) (Nat.card R))
    (hodd : Odd (Nat.card G))
    (hRprime : (Nat.card R).Prime)
    (hGcard : (Nat.card G : k) ≠ 0)
    (hfix : Representation.invariants
      (rho.comp R.subtype : Representation k R V) = ⊥)
    (ih : OddPrimeSemidirectGlobalInductionHypothesis.{u, v, w}
      k (Nat.card G))
    (nonabelianCase :
      ∀ (q : ℕ), q.Prime → IsPGroup q K → ⁅R, K⁆ = K → K ≠ ⊥ →
      ∀ (W : Type w) [AddCommGroup W] [Module k W] [Finite W]
        (sigma : Representation k G W) [Representation.IsIrreducible sigma],
        Function.Injective sigma →
        Representation.invariants
          (sigma.comp R.subtype : Representation k R W) = ⊥ →
        ¬IsMulCommutative K →
        IsCyclic (Subgroup.center G) →
        False) :
    ⁅R, K⁆ ≤ rho.ker := by
  apply kernel_commutator_le_representation_ker_of_faithful_irreducible_pGroup_cases
    rho hKR hnormK hcop hodd hRprime hGcard hfix ih
  intro q hq hKq hperfect W _ _ _ sigma _ hsigma hKne hfixsigma
  by_cases hKab : IsMulCommutative K
  · letI : IsMulCommutative K := hKab
    exact false_of_abelian_faithful_prime_action sigma hsigma hKR hnormK
      hRprime hGcard hperfect hKne hfixsigma
  · exact nonabelianCase q hq hKq hperfect hKne W sigma hsigma hfixsigma
      hKab (center_isCyclic_of_faithful_irreducible sigma hsigma)

end

end Submission.OddOrder.BG.Section03
