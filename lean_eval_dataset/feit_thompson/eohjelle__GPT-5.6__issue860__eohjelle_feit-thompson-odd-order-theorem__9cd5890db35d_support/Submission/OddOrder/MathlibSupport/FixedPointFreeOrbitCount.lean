import Submission.OddOrder.MathlibSupport.FixedPointFreeOrbitQuotient

/-!
The cardinality equation for a fixed-point-free-away-from-one orbit partition.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v

variable {G : Type u} {X : Type v}
variable [Group G] [Group X] [MulDistribMulAction G X]

/-- The orbit-quotient classes other than the class of the identity. -/
abbrev nonidentityOrbitQuotient :=
  { omega : MulAction.orbitRel.Quotient G X //
    omega ≠ (⟦1⟧ : MulAction.orbitRel.Quotient G X) }

/-- A finite action that is fixed-point-free away from one partitions `X` into
one singleton orbit and uniformly `|G|`-element nonidentity orbits. -/
theorem natCard_eq_one_add_nonidentityOrbitQuotient_mul_natCard
    [Finite G] [Finite X]
    (hfixed : ∀ g : G, g ≠ 1 -> ∀ x : X, g • x = x -> x = 1) :
    Nat.card X = 1 + Nat.card (nonidentityOrbitQuotient (G := G) (X := X)) * Nat.card G := by
  classical
  let Omega := MulAction.orbitRel.Quotient G X
  let omegaOne : Omega := ⟦1⟧
  letI := Fintype.ofFinite G
  letI := Fintype.ofFinite X
  letI := Fintype.ofFinite Omega
  letI (omega : Omega) := Fintype.ofFinite omega.orbit
  letI := Fintype.ofFinite (nonidentityOrbitQuotient (G := G) (X := X))
  have hpartition :
      Fintype.card X = ∑ omega : Omega, Fintype.card omega.orbit := by
    calc
      Fintype.card X = Fintype.card (Σ omega : Omega, omega.orbit) :=
        Fintype.card_congr (MulAction.selfEquivSigmaOrbits' G X)
      _ = ∑ omega : Omega, Fintype.card omega.orbit := Fintype.card_sigma
  have hsplit :
      (∑ omega : Omega, Fintype.card omega.orbit) =
        (∑ omega ∈ Finset.univ.erase omegaOne, Fintype.card omega.orbit) +
          Fintype.card omegaOne.orbit := by
    symm
    exact Finset.sum_erase_add _ _ (Finset.mem_univ omegaOne)
  have hone : Fintype.card omegaOne.orbit = 1 := by
    calc
      Fintype.card omegaOne.orbit = Fintype.card ({1} : Set X) :=
        Fintype.card_congr
          (Equiv.setCongr orbitRel_quotient_one_orbit_eq_singleton)
      _ = 1 := by simp
  have hrest :
      (∑ omega ∈ Finset.univ.erase omegaOne, Fintype.card omega.orbit) =
        (Finset.univ.erase omegaOne).card * Fintype.card G := by
    calc
      (∑ omega ∈ Finset.univ.erase omegaOne, Fintype.card omega.orbit) =
          ∑ _omega ∈ Finset.univ.erase omegaOne, Fintype.card G := by
        apply Finset.sum_congr rfl
        intro omega homega
        have hne : omega ≠ omegaOne := (Finset.mem_erase.mp homega).1
        simpa [Nat.card_eq_fintype_card, Omega, omegaOne] using
          natCard_orbitRel_quotient_orbit_eq_natCard_of_ne_one
            hfixed omega hne
      _ = (Finset.univ.erase omegaOne).card * Fintype.card G := by simp
  have hcard_index :
      Fintype.card (nonidentityOrbitQuotient (G := G) (X := X)) =
        (Finset.univ.erase omegaOne).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext omega
    simp [Omega, omegaOne]
  simp only [Nat.card_eq_fintype_card]
  calc
    Fintype.card X = ∑ omega : Omega, Fintype.card omega.orbit := hpartition
    _ = (∑ omega ∈ Finset.univ.erase omegaOne, Fintype.card omega.orbit) +
        Fintype.card omegaOne.orbit := hsplit
    _ = (Finset.univ.erase omegaOne).card * Fintype.card G + 1 := by
      rw [hrest, hone]
    _ = 1 + Fintype.card (nonidentityOrbitQuotient (G := G) (X := X)) *
        Fintype.card G := by rw [hcard_index, add_comm]

end Submission.OddOrder.MathlibSupport
