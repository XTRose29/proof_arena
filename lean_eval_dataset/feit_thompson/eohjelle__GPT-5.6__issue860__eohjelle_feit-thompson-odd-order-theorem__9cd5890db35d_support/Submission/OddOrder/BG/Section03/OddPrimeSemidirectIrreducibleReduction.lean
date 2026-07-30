import Submission.OddOrder.BG.Section03.OddPrimeSemidirectFaithfulReduction
import Submission.OddOrder.BG.Section03.OddPrimeSemidirectStructuralReduction

/-!
The full structural reduction of Bender-Glauberman Theorem 3.4 to the
faithful irreducible prime-power-kernel case.
-/

namespace Submission.OddOrder.BG.Section03

universe u v w

variable {G : Type u} [Group G] [Fintype G]
variable {K R : Subgroup G}
variable {k : Type v} [Field k]
variable {V : Type w} [AddCommGroup V] [Module k V] [Finite V]

noncomputable section

/-- Hall reduction, perfect-action reduction, Maschke constituent selection,
and quotient induction together leave only the faithful irreducible case. -/
theorem kernel_commutator_le_representation_ker_of_faithful_irreducible_pGroup_cases
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
    (faithfulIrreducibleCase :
      ∀ (q : ℕ), q.Prime → IsPGroup q K → ⁅R, K⁆ = K →
      ∀ (W : Type w) [AddCommGroup W] [Module k W] [Finite W]
        (sigma : Representation k G W) [Representation.IsIrreducible sigma],
        Function.Injective sigma →
        K ≠ ⊥ →
        Representation.invariants
          (sigma.comp R.subtype : Representation k R W) = ⊥ →
        False) :
    ⁅R, K⁆ ≤ rho.ker := by
  apply kernel_commutator_le_representation_ker_of_pGroup_perfect_cases
    rho hKR hnormK hcop hodd hRprime hGcard hfix (ih.toSubgroup rho)
  intro q hq hKq hperfect
  rw [hperfect]
  exact kernel_le_representation_ker_of_faithful_irreducible_cases
    rho hKR hnormK hcop hodd hRprime hGcard hfix hperfect ih
      (faithfulIrreducibleCase q hq hKq hperfect)

end

end Submission.OddOrder.BG.Section03
