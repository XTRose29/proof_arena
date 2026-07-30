import Mathlib.GroupTheory.Complement
import Submission.OddOrder.MathlibSupport.FixedOneMulActionOrbitCount
import Submission.OddOrder.MathlibSupport.SubgroupConjugationQuotientAction

/-!
Mathlib-native Frobenius kernel/complement decompositions.

The ambient group is represented by a type, while `K` and `R` are its
internal kernel and complement. This is the form needed throughout
Bender-Glauberman Section 3.
-/

namespace Submission.OddOrder.BG.Section03

open Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G]

/-- An internal Frobenius decomposition: `K` and `R` are complementary,
`K` is normal, both factors are nontrivial, and conjugation by every
nonidentity element of `R` fixes only the identity of `K`. -/
structure IsFrobeniusDecomposition (K R : Subgroup G) : Prop where
  isComplement : K.IsComplement' R
  kernel_normal : K.Normal
  kernel_ne_bot : K ≠ ⊥
  complement_ne_bot : R ≠ ⊥
  fixedPointFree : ∀ r : R, r ≠ 1 → ∀ k : K,
    (r : G) * (k : G) * (r : G)⁻¹ = (k : G) → k = 1

namespace IsFrobeniusDecomposition

variable {K R : Subgroup G} (h : IsFrobeniusDecomposition K R)

include h

theorem sup_eq_top : K ⊔ R = ⊤ :=
  Subgroup.IsComplement'.sup_eq_top h.isComplement

theorem disjoint : Disjoint K R :=
  Subgroup.IsComplement'.disjoint h.isComplement

omit h in
theorem kernel_le_normalizer : K ≤ Subgroup.normalizer (K : Set G) :=
  Subgroup.le_normalizer

theorem complement_le_normalizer : R ≤ Subgroup.normalizer (K : Set G) := by
  letI : K.Normal := h.kernel_normal
  rw [K.normalizer_eq_top]
  exact le_top

theorem card_mul_card [Finite G] :
    Nat.card K * Nat.card R = Nat.card G :=
  Subgroup.IsComplement'.card_mul h.isComplement

/-- The conjugation action of the Frobenius complement on its kernel. -/
abbrev conjugationAction : MulDistribMulAction R K :=
  subgroupConjugationAction K R (complement_le_normalizer h)

theorem coe_smul (r : R) (k : K) :
    letI := conjugationAction h
    ((r • k : K) : G) = (r : G) * (k : G) * (r : G)⁻¹ := by
  exact coe_subgroupConjugationAction_smul
    K R (complement_le_normalizer h) r k

/-- Pointwise fixed-point-free form of the Frobenius condition for the
installed conjugation action. -/
theorem smul_eq_imp_eq_one :
    letI := conjugationAction h
    ∀ r : R, r ≠ 1 → ∀ k : K, r • k = k → k = 1 := by
  letI := conjugationAction h
  intro r hr k hk
  apply IsFrobeniusDecomposition.fixedPointFree h r hr k
  exact congrArg Subtype.val hk

/-- The centralizer in the kernel of every nonidentity complement element is
trivial. -/
theorem centralizerWithin_zpowers_eq_bot (r : R) (hr : r ≠ 1) :
    centralizerWithin K (Subgroup.zpowers (r : G)) = ⊥ := by
  apply le_bot_iff.mp
  intro k hk
  have hcomm : (r : G) * k = k * (r : G) := by
    exact Subgroup.mem_centralizer_iff.mp hk.2 (r : G)
      (Subgroup.mem_zpowers (r : G))
  have hfix : (r : G) * k * (r : G)⁻¹ = k := by
    calc
      (r : G) * k * (r : G)⁻¹ = k * (r : G) * (r : G)⁻¹ := by
        rw [hcomm]
      _ = k := by simp
  have hkOne : (⟨k, hk.1⟩ : K) = 1 :=
    IsFrobeniusDecomposition.fixedPointFree h r hr ⟨k, hk.1⟩ hfix
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hkOne)

/-- Every nonidentity kernel element has a full complement-sized conjugacy
orbit. -/
theorem natCard_orbit_eq_natCard [Finite R]
    (k : K) (hk : k ≠ 1) :
    letI := conjugationAction h
    Nat.card (MulAction.orbit R k) = Nat.card R := by
  letI := conjugationAction h
  exact natCard_orbit_eq_natCard_of_ne_one_of_fixed_point_free
    k hk (smul_eq_imp_eq_one h)

/-- The kernel is the identity together with uniformly complement-sized
nonidentity conjugation orbits. -/
theorem kernel_card_eq_one_add_orbits_mul_card [Finite K] [Finite R] :
    letI := conjugationAction h
    Nat.card K =
      1 + Nat.card
        (nonidentityFixedOneOrbitQuotient (G := R) (X := K)) * Nat.card R := by
  letI := conjugationAction h
  apply natCard_eq_one_add_fixedOneOrbits_mul_natCard
  · intro r
    exact smul_one r
  · exact smul_eq_imp_eq_one h

/-- Kernel and complement orders in a finite Frobenius decomposition are
coprime. -/
theorem natCard_coprime [Finite K] [Finite R] :
    Nat.Coprime (Nat.card K) (Nat.card R) := by
  letI := conjugationAction h
  let t := Nat.card
    (nonidentityFixedOneOrbitQuotient (G := R) (X := K))
  have hcard : Nat.card K = 1 + t * Nat.card R := by
    simpa [t] using kernel_card_eq_one_add_orbits_mul_card h
  rw [hcard]
  exact (Nat.coprime_add_mul_right_left 1 (Nat.card R) t).mpr
    (Nat.coprime_one_left (Nat.card R))

end IsFrobeniusDecomposition

end Submission.OddOrder.BG.Section03
