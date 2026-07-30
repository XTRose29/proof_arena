import Submission.OddOrder.BG.Section03.OddPrimeSemidirectGlobalInduction
import Submission.OddOrder.MathlibSupport.MaschkeNormalConstituent
import Submission.OddOrder.MathlibSupport.NormalPrimeComplement
import Submission.OddOrder.MathlibSupport.SubrepresentationInvariants

/-!
The simple-constituent selection in Bender-Glauberman Theorem 3.4.
-/

namespace Submission.OddOrder.BG.Section03

open Submission.OddOrder.MathlibSupport
open scoped MonoidAlgebra

universe u v w

variable {G : Type u} [Group G] [Fintype G]
variable {K R : Subgroup G}
variable {k : Type v} [Field k]
variable {V : Type w} [AddCommGroup V] [Module k V]

noncomputable section

omit [Fintype G] in
/-- A factor normalized by its complement in a complementary factorization
is ambient normal. -/
theorem normal_left_of_isComplement'_of_right_le_normalizer
    (hKR : K.IsComplement' R)
    (hnormK : R ≤ Subgroup.normalizer (K : Set G)) :
    K.Normal := by
  rw [← Subgroup.normalizer_eq_top_iff]
  apply top_unique
  rw [← hKR.sup_eq_top]
  exact sup_le K.le_normalizer hnormK

/-- If `K` acts nontrivially, a simple Maschke constituent can be chosen on
which it still acts nontrivially.  The constituent has zero `R`-fixed space,
and its kernel is a normal subgroup of `K` disjoint from `R`. -/
theorem exists_irreducible_constituent_with_kernel_le_left
    (rho : Representation k G V)
    (hKR : K.IsComplement' R)
    (hnormK : R ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card K) (Nat.card R))
    (hRprime : (Nat.card R).Prime)
    (hGcard : (Nat.card G : k) ≠ 0)
    (hfix : Representation.invariants
      (rho.comp R.subtype : Representation k R V) = ⊥)
    (hK : ¬ K ≤ rho.ker) :
    ∃ U : Subrepresentation rho,
      Representation.IsIrreducible U.toRepresentation ∧
      ¬ K ≤ U.toRepresentation.ker ∧
      Representation.invariants
        (U.toRepresentation.comp R.subtype :
          Representation k R U.toSubmodule) = ⊥ ∧
      U.toRepresentation.ker ≤ K ∧
      Disjoint U.toRepresentation.ker R := by
  letI : K.Normal :=
    normal_left_of_isComplement'_of_right_le_normalizer hKR hnormK
  obtain ⟨U, hU, hUK⟩ :=
    exists_irreducible_subrepresentation_not_le_ker_of_normal
      rho K hGcard hK
  letI : Representation.IsIrreducible U.toRepresentation := hU
  letI : IsSimpleModule k[G] U.toRepresentation.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).mp hU
  letI : Nontrivial U.toRepresentation.asModule :=
    IsSimpleModule.nontrivial k[G] U.toRepresentation.asModule
  letI : Nontrivial U.toSubmodule :=
    Function.Injective.nontrivial
      U.toRepresentation.asModuleEquiv.injective
  have hfixU : Representation.invariants
      (U.toRepresentation.comp R.subtype :
        Representation k R U.toSubmodule) = ⊥ :=
    subrepresentation_invariants_eq_bot rho R U hfix
  have hdis : Disjoint U.toRepresentation.ker R :=
    representation_ker_disjoint_prime_subgroup_of_invariants_eq_bot
      U.toRepresentation R hRprime hfixU
  have hkerK : U.toRepresentation.ker ≤ K :=
    normal_le_left_of_disjoint_prime_right hKR hcop hRprime hdis
  exact ⟨U, hU, hUK, hfixU, hkerK, hdis⟩

end

end Submission.OddOrder.BG.Section03
