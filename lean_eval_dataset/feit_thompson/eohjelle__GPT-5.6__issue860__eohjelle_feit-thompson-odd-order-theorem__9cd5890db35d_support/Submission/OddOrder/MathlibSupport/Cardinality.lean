import Mathlib

/-!
Cardinality and parity wrappers used by the odd-order port.

These lemmas deliberately stay close to mathlib's native statements.  The
porting files can depend on the names here while the proof terms remain thin
adapters around upstream APIs.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

theorem natCard_subgroup_dvd_natCard (H : Subgroup G) :
    Nat.card H ∣ Nat.card G :=
  H.card_subgroup_dvd_card

theorem natCard_quotient_dvd_natCard (H : Subgroup G) :
    Nat.card (G ⧸ H) ∣ Nat.card G :=
  H.card_quotient_dvd_card

theorem odd_natCard_subgroup (H : Subgroup G) (hG : Odd (Nat.card G)) :
    Odd (Nat.card H) :=
  hG.of_dvd_nat (natCard_subgroup_dvd_natCard H)

theorem odd_natCard_quotient (H : Subgroup G) (hG : Odd (Nat.card G)) :
    Odd (Nat.card (G ⧸ H)) :=
  hG.of_dvd_nat (natCard_quotient_dvd_natCard H)

/-- Nonvanishing of the ambient group order in a field descends to every
quotient order. -/
theorem natCard_quotient_cast_ne_zero
    {k : Type*} [Field k] [Finite G]
    (H : Subgroup G) (hG : (Nat.card G : k) ≠ 0) :
    (Nat.card (G ⧸ H) : k) ≠ 0 := by
  intro hzero
  apply hG
  rw [H.card_eq_card_quotient_mul_card_subgroup, Nat.cast_mul,
    hzero, zero_mul]

theorem natCard_eq_one_iff_subsingleton :
    Nat.card G = 1 ↔ Subsingleton G :=
  ⟨fun h => (Nat.card_eq_one_iff_unique.mp h).1,
    fun h => Nat.card_eq_one_iff_unique.mpr ⟨h, ⟨1⟩⟩⟩

end Submission.OddOrder.MathlibSupport
