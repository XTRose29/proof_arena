import Submission.OddOrder.MathlibSupport.CentralizerConjugationFixedPoint

/-!
Orbit counting for group actions that fix a distinguished identity element.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v

variable {G : Type u} {X : Type v}
variable [Group G] [Group X] [MulAction G X]

/-- The nonidentity orbit-quotient classes for a group action on a group. -/
abbrev nonidentityFixedOneOrbitQuotient :=
  { omega : MulAction.orbitRel.Quotient G X //
    omega ≠ (⟦1⟧ : MulAction.orbitRel.Quotient G X) }

/-- If every acting element fixes `1`, then the orbit of `1` is a singleton. -/
theorem orbit_one_eq_singleton_of_smul_one
    (hone : ∀ g : G, g • (1 : X) = 1) :
    MulAction.orbit G (1 : X) = {1} := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    simpa using hone g
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact MulAction.mem_orbit_self 1

/-- The orbit-quotient class of `1` has singleton orbit when `1` is fixed. -/
theorem orbitRel_quotient_one_orbit_eq_singleton_of_smul_one
    (hone : ∀ g : G, g • (1 : X) = 1) :
    MulAction.orbitRel.Quotient.orbit
      (⟦1⟧ : MulAction.orbitRel.Quotient G X) = {1} := by
  rw [MulAction.orbitRel.Quotient.orbit_mk]
  exact orbit_one_eq_singleton_of_smul_one hone

/-- Every orbit-quotient class other than the class of `1` has cardinality
`|G|` when nonidentity acting elements fix only `1`. -/
theorem natCard_orbitRel_quotient_orbit_eq_natCard_of_fixed_one
    [Finite G]
    (hfixed : ∀ g : G, g ≠ 1 -> ∀ x : X, g • x = x -> x = 1)
    (omega : MulAction.orbitRel.Quotient G X)
    (homega : omega ≠ (⟦1⟧ : MulAction.orbitRel.Quotient G X)) :
    Nat.card omega.orbit = Nat.card G := by
  have hout : omega.out ≠ (1 : X) := by
    intro hout
    apply homega
    rw [← Quotient.out_eq' omega, hout]
  rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out omega Quotient.out_eq']
  exact natCard_orbit_eq_natCard_of_ne_one_of_fixed_point_free
    omega.out hout hfixed

/-- A finite action fixing `1` and otherwise fixed-point-free partitions `X`
into one singleton orbit and uniformly `|G|`-element nonidentity orbits. -/
theorem natCard_eq_one_add_fixedOneOrbits_mul_natCard
    [Finite G] [Finite X]
    (hone : ∀ g : G, g • (1 : X) = 1)
    (hfixed : ∀ g : G, g ≠ 1 -> ∀ x : X, g • x = x -> x = 1) :
    Nat.card X =
      1 + Nat.card (nonidentityFixedOneOrbitQuotient (G := G) (X := X)) * Nat.card G := by
  classical
  let Omega := MulAction.orbitRel.Quotient G X
  let omegaOne : Omega := ⟦1⟧
  letI := Fintype.ofFinite G
  letI := Fintype.ofFinite X
  letI := Fintype.ofFinite Omega
  letI (omega : Omega) := Fintype.ofFinite omega.orbit
  letI := Fintype.ofFinite
    (nonidentityFixedOneOrbitQuotient (G := G) (X := X))
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
  have hone_card : Fintype.card omegaOne.orbit = 1 := by
    calc
      Fintype.card omegaOne.orbit = Fintype.card ({1} : Set X) :=
        Fintype.card_congr
          (Equiv.setCongr
            (orbitRel_quotient_one_orbit_eq_singleton_of_smul_one hone))
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
          natCard_orbitRel_quotient_orbit_eq_natCard_of_fixed_one
            hfixed omega hne
      _ = (Finset.univ.erase omegaOne).card * Fintype.card G := by simp
  have hcard_index :
      Fintype.card
          (nonidentityFixedOneOrbitQuotient (G := G) (X := X)) =
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
      rw [hrest, hone_card]
    _ = 1 + Fintype.card
          (nonidentityFixedOneOrbitQuotient (G := G) (X := X)) *
        Fintype.card G := by rw [hcard_index, add_comm]

end Submission.OddOrder.MathlibSupport
