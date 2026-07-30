import Submission.OddOrder.MathlibSupport.IrreducibleCharacterDegreeDivides
import Submission.OddOrder.MathlibSupport.IrreducibleHallExtensionCoprimeDegree

/-!
# Extension of invariant irreducible characters from normal Hall subgroups

This is the ordinary-character extension theorem used in Peterfalvi 1.7(c).
The projective factor set is killed by its two coprime annihilators: the
character degree and the Hall index.
-/

namespace Submission.OddOrder.MathlibSupport

noncomputable section

open Submission.OddOrder.PF

universe u

/-- An invariant irreducible character of a normal Hall subgroup extends to
an irreducible character of the ambient group.  The abelian-quotient
assumption is the specialization needed by Peterfalvi 1.7(c); the underlying
coprime extension construction is valid without it. -/
theorem exists_irreducible_extension_of_normal_hall_abelian
    {T k : Type u} [Group T] [Fintype T]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup T) [K.Normal]
    (theta : IrreducibleCharacter K k)
    (hHall : Nat.Coprime (Nat.card K) K.index)
    (hInv : ClassFunction.inertia K (theta : ClassFunction K k) = ⊤)
    [IsMulCommutative (T ⧸ K)] :
    ∃ psi : IrreducibleCharacter T k,
      ClassFunction.restrict K (psi : ClassFunction T k) =
        (theta : ClassFunction K k) := by
  letI : Fintype K := Fintype.ofFinite K
  have hDegreeDvd : Module.finrank k theta.representation ∣ Nat.card K :=
    theta.finrank_representation_dvd_natCard
  have hDegree : Nat.Coprime
      (Module.finrank k theta.representation) K.index :=
    hHall.of_dvd_left hDegreeDvd
  exact exists_irreducible_extension_of_normal_hall_of_coprime_degree
    K theta hHall hDegree hInv

end

end Submission.OddOrder.MathlibSupport
