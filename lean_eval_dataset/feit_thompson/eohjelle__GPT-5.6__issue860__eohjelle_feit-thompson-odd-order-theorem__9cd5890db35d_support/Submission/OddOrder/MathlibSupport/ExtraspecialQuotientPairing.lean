import Submission.OddOrder.MathlibSupport.ExtraspecialCommutatorPairing

/-!
The nondegenerate commutator pairing on the center quotient of a special group.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G]

namespace IsSpecial

/-- Pairing with a fixed first argument, as a homomorphism in the second
argument. -/
def commutatorPairingRightHom (hG : IsSpecial G) (x : G) :
    G →* Subgroup.center G where
  toFun := hG.commutatorPairing x
  map_one' := by
    apply Subtype.ext
    simp [commutatorPairing]
  map_mul' := hG.commutatorPairing_mul_right x

/-- Central elements are in the kernel of either argument of the commutator
pairing. -/
theorem center_le_ker_commutatorPairingRightHom (hG : IsSpecial G) (x : G) :
    Subgroup.center G ≤ (hG.commutatorPairingRightHom x).ker := by
  intro z hz
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  exact commutatorElement_eq_one_iff_commute.mpr
    (Subgroup.mem_center_iff.mp hz x)

/-- The right argument of the commutator pairing, descended to the center
quotient. -/
def commutatorPairingRightQuotientHom (hG : IsSpecial G) (x : G) :
    (G ⧸ Subgroup.center G) →* Subgroup.center G :=
  QuotientGroup.lift (Subgroup.center G) (hG.commutatorPairingRightHom x)
    (hG.center_le_ker_commutatorPairingRightHom x)

@[simp]
theorem commutatorPairingRightQuotientHom_mk (hG : IsSpecial G) (x y : G) :
    hG.commutatorPairingRightQuotientHom x
        (QuotientGroup.mk' (Subgroup.center G) y) =
      hG.commutatorPairing x y :=
  rfl

/-- Pairing into the dual of the center quotient, before descending the first
argument. -/
def commutatorPairingLeftHom (hG : IsSpecial G) :
    G →* ((G ⧸ Subgroup.center G) →* Subgroup.center G) where
  toFun := hG.commutatorPairingRightQuotientHom
  map_one' := by
    apply QuotientGroup.monoidHom_ext
    ext y
    change (hG.commutatorPairing 1 y : G) = 1
    simp [commutatorPairing]
  map_mul' := by
    intro a b
    apply QuotientGroup.monoidHom_ext
    ext y
    change (hG.commutatorPairing (a * b) y : G) =
      ((hG.commutatorPairing a y * hG.commutatorPairing b y :
        Subgroup.center G) : G)
    exact congrArg Subtype.val (hG.commutatorPairing_mul_left a b y)

/-- The center is in the kernel of the first argument of the descended
pairing. -/
theorem center_le_ker_commutatorPairingLeftHom (hG : IsSpecial G) :
    Subgroup.center G ≤ hG.commutatorPairingLeftHom.ker := by
  intro z hz
  rw [MonoidHom.mem_ker]
  apply QuotientGroup.monoidHom_ext
  ext y
  change (hG.commutatorPairing z y : G) = 1
  exact commutatorElement_eq_one_iff_commute.mpr
    (Subgroup.mem_center_iff.mp hz y).symm

/-- The central commutator pairing on the quotient by the center. -/
def quotientCommutatorPairing (hG : IsSpecial G) :
    (G ⧸ Subgroup.center G) →*
      ((G ⧸ Subgroup.center G) →* Subgroup.center G) :=
  QuotientGroup.lift (Subgroup.center G) hG.commutatorPairingLeftHom
    hG.center_le_ker_commutatorPairingLeftHom

@[simp]
theorem quotientCommutatorPairing_mk_mk (hG : IsSpecial G) (x y : G) :
    hG.quotientCommutatorPairing (QuotientGroup.mk' (Subgroup.center G) x)
        (QuotientGroup.mk' (Subgroup.center G) y) =
      hG.commutatorPairing x y :=
  rfl

/-- The quotient pairing has trivial left radical. -/
theorem quotientCommutatorPairing_nondegenerate (hG : IsSpecial G)
    (x : G ⧸ Subgroup.center G)
    (hx : ∀ y : G ⧸ Subgroup.center G,
      hG.quotientCommutatorPairing x y = 1) : x = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) x
  apply (QuotientGroup.eq_one_iff x).mpr
  apply (hG.commutatorPairing_left_radical x).mp
  intro y
  exact hx (QuotientGroup.mk' (Subgroup.center G) y)

/-- The quotient commutator pairing embeds the center quotient in its
central-valued dual. -/
theorem quotientCommutatorPairing_injective (hG : IsSpecial G) :
    Function.Injective hG.quotientCommutatorPairing := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_bot]
    apply hG.quotientCommutatorPairing_nondegenerate x
    change hG.quotientCommutatorPairing x = 1 at hx
    exact fun y ↦ DFunLike.congr_fun hx y
  · exact bot_le

end IsSpecial

end Submission.OddOrder.MathlibSupport
