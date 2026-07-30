import Submission.OddOrder.MathlibSupport.IrreducibleHallExtension
import Submission.OddOrder.PF.Section01.CentralInertiaInduction

/-!
# Assembly for Peterfalvi 1.7(c)

An irreducible extension of the invariant Hall-subgroup character forces the
common multiplicity in 1.7(b) to be one.  This file isolates that formal
consequence from the character-extension theorem itself.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical IsMulCommutative

universe u

namespace ClassFunction

variable {G k : Type u} [Group G] [Fintype G]
  [Field k] [IsAlgClosed k] [CharZero k]

/-- The conclusion of Peterfalvi 1.7(c), assuming the exact irreducible
extension supplied by the normal Hall-subgroup extension theorem. -/
theorem cfInd_Hall_central_inertia_of_exists_extension
    (H : Subgroup G) [H.Normal] (theta : IrreducibleCharacter H k)
    [IsMulCommutative
      ((inertia H (theta : ClassFunction H k)) ⧸
        H.subgroupOf (inertia H (theta : ClassFunction H k)))]
    (hext : ∃ psi : IrreducibleCharacter
        (inertia H (theta : ClassFunction H k)) k,
      restrict
          (H.subgroupOf (inertia H (theta : ClassFunction H k)))
          (psi : ClassFunction
            (inertia H (theta : ClassFunction H k)) k) =
        (inertiaSubgroupCharacter H theta : ClassFunction
          (H.subgroupOf (inertia H (theta : ClassFunction H k))) k)) :
    let T := inertia H (theta : ClassFunction H k)
    let calB := constituents (induce H (theta : ClassFunction H k))
    induce H (theta : ClassFunction H k) =
        ∑ chi ∈ calB, (chi : ClassFunction G k) ∧
      calB.card = Nat.card T / Nat.card H ∧
      ∀ chi ∈ calB,
        chi 1 = (T.index : k) * theta 1 := by
  dsimp only
  let T := inertia H (theta : ClassFunction H k)
  let K := H.subgroupOf T
  let thetaT := inertiaSubgroupCharacter H theta
  let V : FDRep k T := FDRep.induceFromSubgroup K thetaT.representation
  let F : ClassFunction T k := ofRepresentation V.ρ
  let calA := inertiaConstituents H theta
  let calB := constituents (induce H (theta : ClassFunction H k))
  letI : Fintype K := Fintype.ofFinite _
  letI : Invertible (Nat.card K : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card T : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨psi, hres⟩ := hext
  change restrict K (psi : ClassFunction T k) =
    (thetaT : ClassFunction K k) at hres
  have hF : F = induce K (thetaT : ClassFunction K k) := by
    dsimp only [F, V]
    exact (ofRepresentation_induceFromSubgroup_general
      K thetaT.representation).trans
        (congrArg (induce K) thetaT.ofRepresentation_representation)
  have hpair :
      characterPairing F (psi : ClassFunction T k) = 1 := by
    rw [hF, frobeniusReciprocity K, hres]
    exact IrreducibleCharacter.characterPairing_self thetaT
  have hpsi : psi ∈ calA := by
    apply (mem_constituents_iff F psi).2
    unfold IrreducibleCharacter.IsConstituent
    rw [hpair]
    exact one_ne_zero
  have hmcast : (psi.multiplicity V : k) = 1 := by
    exact (psi.characterPairing_ofRepresentation_eq_multiplicity V).symm.trans
      hpair
  have hm : psi.multiplicity V = 1 := by
    apply Nat.cast_injective (R := k)
    simpa using hmcast
  obtain ⟨e, he, huniform, hInd, hcard, hdegree⟩ :=
    cfInd_central_inertia H theta
  change ∀ phi ∈ calA, phi.multiplicity V = e at huniform
  have heone : e = 1 := (huniform psi hpsi).symm.trans hm
  subst e
  refine ⟨?_, ?_, ?_⟩
  · simpa using hInd
  · apply Nat.cast_injective (R := k)
    simpa using hcard
  · intro chi hchi
    simpa using hdegree chi hchi

/-- Peterfalvi 1.7(c), source `cfInd_Hall_central_Inertia`: when the normal
subgroup is Hall in its inertia subgroup, the common multiplicity is one. -/
theorem cfInd_Hall_central_inertia
    (H : Subgroup G) [H.Normal] (theta : IrreducibleCharacter H k)
    [IsMulCommutative
      ((inertia H (theta : ClassFunction H k)) ⧸
        H.subgroupOf (inertia H (theta : ClassFunction H k)))]
    (hHall : Nat.Coprime
      (Nat.card
        (H.subgroupOf (inertia H (theta : ClassFunction H k))))
      (H.subgroupOf
        (inertia H (theta : ClassFunction H k))).index) :
    let T := inertia H (theta : ClassFunction H k)
    let calB := constituents (induce H (theta : ClassFunction H k))
    induce H (theta : ClassFunction H k) =
        ∑ chi ∈ calB, (chi : ClassFunction G k) ∧
      calB.card = Nat.card T / Nat.card H ∧
      ∀ chi ∈ calB,
        chi 1 = (T.index : k) * theta 1 := by
  let T := inertia H (theta : ClassFunction H k)
  let K := H.subgroupOf T
  let thetaT := inertiaSubgroupCharacter H theta
  have hInv : inertia K (thetaT : ClassFunction K k) = ⊤ := by
    exact inertia_inertiaSubgroupCharacter_eq_top H theta
  have hext : ∃ psi : IrreducibleCharacter T k,
      restrict K (psi : ClassFunction T k) =
        (thetaT : ClassFunction K k) :=
    _root_.Submission.OddOrder.MathlibSupport.exists_irreducible_extension_of_normal_hall_abelian
        K thetaT hHall hInv
  exact cfInd_Hall_central_inertia_of_exists_extension H theta hext

end ClassFunction

end

end Submission.OddOrder.PF
