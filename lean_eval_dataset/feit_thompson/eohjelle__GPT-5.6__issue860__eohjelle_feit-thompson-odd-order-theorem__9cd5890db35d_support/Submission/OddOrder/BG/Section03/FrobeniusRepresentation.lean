import Submission.OddOrder.BG.Section03.FrobeniusPartitionSum
import Submission.OddOrder.MathlibSupport.RepresentationSubgroupNorm

/-!
Fixed vectors for representations of finite Frobenius decompositions.
-/

namespace Submission.OddOrder.BG.Section03

open Submission.OddOrder.MathlibSupport

universe u v w

variable {G : Type u} [Group G] [Fintype G]
variable {K R : Subgroup G}
variable {k : Type v} [Field k]
variable {V : Type w} [AddCommGroup V] [Module k V]

noncomputable section

local instance : DecidableEq G := Classical.decEq G
local instance : DecidablePred (fun g : G ↦ g ∈ K) := Classical.decPred _
local instance : DecidablePred (fun g : G ↦ g ∈ R) := Classical.decPred _

namespace IsFrobeniusDecomposition

/-- Bender-Glauberman Lemma 3.3: in characteristic coprime to the Frobenius
kernel order, every representation on which the kernel acts nontrivially has
a nonzero vector fixed by the complement. -/
theorem complement_invariants_ne_bot
    (h : IsFrobeniusDecomposition K R)
    (rho : _root_.Representation k G V)
    (hcard : (Fintype.card K : k) ≠ 0)
    (hker : ¬ K ≤ rho.ker) :
    _root_.Representation.invariants
      (rho.comp R.subtype : _root_.Representation k R V) ≠ ⊥ := by
  intro hfix
  have hnormR : _root_.Representation.norm
      (rho.comp R.subtype : _root_.Representation k R V) = 0 :=
    Representation.norm_eq_zero_of_invariants_eq_bot _ hfix
  have hnormG : rho.norm = 0 :=
    Representation.norm_eq_zero_of_restrict_invariants_eq_bot rho R hfix
  have hconjugate (x : K) :
      (∑ r : R, rho ((x : G) * (r : G) * (x : G)⁻¹)) = 0 := by
    rw [Representation.sum_conjugates_eq_mul_norm_mul_inv rho R (x : G), hnormR]
    simp
  have hpartition :=
    h.sum_add_card_nsmul_one_eq_kernel_add_conjugates
      (fun g : G ↦ rho g)
  change rho.norm + Fintype.card K • rho 1 =
      _root_.Representation.norm
          (rho.comp K.subtype : _root_.Representation k K V) +
        ∑ x : K, ∑ r : R,
          rho ((x : G) * (r : G) * (x : G)⁻¹) at hpartition
  have hnormK : _root_.Representation.norm
      (rho.comp K.subtype : _root_.Representation k K V) =
        Fintype.card K • (1 : Module.End k V) := by
    rw [hnormG] at hpartition
    simp_rw [hconjugate] at hpartition
    simpa only [_root_.Representation.norm, map_one, zero_add,
      Finset.sum_const_zero, add_zero] using hpartition.symm
  apply hker
  exact Representation.subgroup_le_ker_of_norm_eq_card_nsmul_one
    rho K hnormK hcard

end IsFrobeniusDecomposition

end

end Submission.OddOrder.BG.Section03
