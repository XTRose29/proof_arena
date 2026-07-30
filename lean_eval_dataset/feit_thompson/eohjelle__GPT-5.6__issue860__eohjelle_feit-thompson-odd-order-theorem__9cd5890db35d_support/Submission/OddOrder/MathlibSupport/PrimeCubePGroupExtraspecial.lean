import Submission.OddOrder.MathlibSupport.Extraspecial
import Submission.OddOrder.MathlibSupport.FrattiniPGroup

/-!
# Noncommutative groups of prime-cube order

The generic order-`p ^ 3` classification used in Bender--Glauberman,
Theorem 4.16.  This is the Mathlib-native counterpart of MathComp's
`p3group_extraspecial` (via `card_p3group_extraspecial`) in
`solvable/maximal.v`.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative

universe u

private theorem isExtraspecial_of_isPGroup_of_natCard_eq_prime_cube_of_center_card
    {P : Type u} [Group P] [Finite P]
    {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) (hcard : Nat.card P = p ^ 3)
    (hcenter : Nat.card (Subgroup.center P) = p) : IsExtraspecial P := by
  classical
  let Z : Subgroup P := Subgroup.center P
  let q : P →* P ⧸ Z := QuotientGroup.mk' Z
  have hQcard : Nat.card (P ⧸ Z) = p ^ 2 := by
    apply Nat.mul_right_cancel (Fact.out : p.Prime).pos
    calc
      Nat.card (P ⧸ Z) * p =
          Nat.card (P ⧸ Z) * Nat.card Z := by
            rw [show Nat.card Z = p from by simpa [Z] using hcenter]
      _ = Nat.card P :=
        (Subgroup.card_eq_card_quotient_mul_card_subgroup Z).symm
      _ = p ^ 3 := hcard
      _ = p ^ 2 * p := by rw [pow_succ]
  letI : IsMulCommutative (P ⧸ Z) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hQcard
  have hcommLe : _root_.commutator P ≤ Z := by
    exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
      (show IsMulCommutative (P ⧸ Z) from inferInstance)
  have hnoncomm : ¬ IsMulCommutative P := by
    intro hcomm
    letI : IsMulCommutative P := hcomm
    have hZtop : Subgroup.center P = ⊤ := Subgroup.center_eq_top_iff.mpr hcomm
    have : Nat.card P = p := by simpa [Z, hZtop] using hcenter
    have hpCubeNe : p ^ 3 ≠ p := by
      nlinarith [(Fact.out : p.Prime).one_lt]
    exact hpCubeNe (hcard.symm.trans this)
  have hcommNe : _root_.commutator P ≠ ⊥ := by
    intro hbot
    exact hnoncomm ((_root_.commutator_eq_bot_iff P).mp hbot)
  have hcommEq : _root_.commutator P = Z := by
    letI : Fact (Nat.card Z).Prime := ⟨by simpa [Z, hcenter] using
      (Fact.out : p.Prime)⟩
    rcases ((_root_.commutator P).subgroupOf Z).eq_bot_or_eq_top_of_prime_card with
      hbot | htop
    · have hdisjoint : Disjoint (_root_.commutator P) Z :=
        Subgroup.subgroupOf_eq_bot.mp hbot
      have hinf : _root_.commutator P ⊓ Z = ⊥ := disjoint_iff.mp hdisjoint
      exact (hcommNe (by rw [← inf_eq_left.mpr hcommLe, hinf])).elim
    · exact le_antisymm hcommLe (Subgroup.subgroupOf_eq_top.mp htop)
  have hQnoncyclic : ¬ IsCyclic (P ⧸ Z) := by
    intro hcyclic
    letI : IsCyclic (P ⧸ Z) := hcyclic
    apply hnoncomm
    simpa [Z] using isMulCommutative_of_isCyclic_quotient_center_self P
  have hQexponent : Monoid.exponent (P ⧸ Z) = p :=
    (not_isCyclic_iff_exponent_eq_prime (Fact.out : p.Prime) hQcard).mp
      hQnoncyclic
  have hQpow (x : P ⧸ Z) : x ^ p = 1 := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (by
      rw [hQexponent])
  have hfrattiniQ : frattini (P ⧸ Z) = ⊥ :=
    IsPGroup.frattini_eq_bot_of_isMulCommutative_of_pow_prime hQpow
  have hfrattiniLe : frattini P ≤ Z := by
    have hle := frattini_le_comap_frattini_of_surjective
      (φ := q) (QuotientGroup.mk'_surjective Z)
    rw [hfrattiniQ, MonoidHom.comap_bot, QuotientGroup.ker_mk'] at hle
    exact hle
  have hcenterLe : Z ≤ frattini P := by
    rw [← hcommEq]
    exact IsPGroup.commutator_le_frattini hP
  exact
    { toIsSpecial :=
        { frattini_eq_center := by simpa [Z] using le_antisymm hfrattiniLe hcenterLe
          commutator_eq_center := by simpa [Z] using hcommEq }
      center_card_prime := by simpa [hcenter] using (Fact.out : p.Prime) }

/-- A noncommutative finite `p`-group of order `p ^ 3` is extraspecial.

This is the exact-cardinality form of MathComp's `p3group_extraspecial`.
-/
theorem isExtraspecial_of_isPGroup_of_natCard_eq_prime_cube_of_not_isMulCommutative
    {P : Type u} [Group P] [Finite P]
    {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) (hcard : Nat.card P = p ^ 3)
    (hnoncomm : ¬ IsMulCommutative P) : IsExtraspecial P := by
  classical
  have hcardOne : 1 < Nat.card P := by
    rw [hcard]
    exact one_lt_pow₀ (Fact.out : p.Prime).one_lt (by decide : (3 : ℕ) ≠ 0)
  letI : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp hcardOne
  obtain ⟨k, hkpos, hcenterPow⟩ :=
    IsPGroup.card_center_eq_prime_pow hcard (by omega : 0 < (3 : ℕ))
  have hkLe : k ≤ 3 := by
    apply (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp
    simpa [hcenterPow, hcard] using
      (Subgroup.center P).card_subgroup_dvd_card
  have hkNeThree : k ≠ 3 := by
    intro hk
    have hcenterTop : Subgroup.center P = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      calc
        Nat.card (Subgroup.center P) = p ^ 3 := by rw [hcenterPow, hk]
        _ = Nat.card P := hcard.symm
    exact hnoncomm (Subgroup.center_eq_top_iff.mp hcenterTop)
  have hkNeTwo : k ≠ 2 := by
    intro hk
    let Z : Subgroup P := Subgroup.center P
    have hQcard : Nat.card (P ⧸ Z) = p := by
      apply Nat.mul_right_cancel (pow_pos (Fact.out : p.Prime).pos 2)
      calc
        Nat.card (P ⧸ Z) * p ^ 2 =
            Nat.card (P ⧸ Z) * Nat.card Z := by rw [hcenterPow, hk]
        _ = Nat.card P :=
          (Subgroup.card_eq_card_quotient_mul_card_subgroup Z).symm
        _ = p ^ 3 := hcard
        _ = p * p ^ 2 := by ring
    letI : IsCyclic (P ⧸ Z) := isCyclic_of_prime_card hQcard
    apply hnoncomm
    simpa [Z] using isMulCommutative_of_isCyclic_quotient_center_self P
  have hk : k = 1 := by omega
  have hcenter : Nat.card (Subgroup.center P) = p := by
    simpa [hk] using hcenterPow
  exact isExtraspecial_of_isPGroup_of_natCard_eq_prime_cube_of_center_card
    hP hcard hcenter

end Submission.OddOrder.MathlibSupport
