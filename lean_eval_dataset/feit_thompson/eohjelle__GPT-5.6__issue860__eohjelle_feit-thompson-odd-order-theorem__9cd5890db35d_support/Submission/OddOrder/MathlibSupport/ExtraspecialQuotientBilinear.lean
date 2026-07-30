import Submission.OddOrder.MathlibSupport.ExtraspecialQuotientModule

/-!
The extraspecial quotient commutator pairing as a `ZMod p`-bilinear map.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G]

namespace IsSpecial

variable {p : ℕ}
variable [IsMulCommutative (G ⧸ Subgroup.center G)]
variable [Module (ZMod p) (Additive (G ⧸ Subgroup.center G))]
variable [Module (ZMod p) (Additive (Subgroup.center G))]

/-- The quotient commutator pairing with fixed first argument, linearized over
`ZMod p`. -/
def quotientCommutatorRightLinearMap (hG : IsSpecial G)
    (x : Additive (G ⧸ Subgroup.center G)) :
    Additive (G ⧸ Subgroup.center G) →ₗ[ZMod p]
      Additive (Subgroup.center G) :=
  (MonoidHom.toAdditive
    (hG.quotientCommutatorPairing x.toMul)).toZModLinearMap p

@[simp]
theorem quotientCommutatorRightLinearMap_apply (hG : IsSpecial G)
    (x y : Additive (G ⧸ Subgroup.center G)) :
    hG.quotientCommutatorRightLinearMap (p := p) x y =
      Additive.ofMul
        (hG.quotientCommutatorPairing x.toMul y.toMul) :=
  rfl

/-- The quotient commutator pairing, linearized in both arguments over
`ZMod p`. -/
def quotientCommutatorLinearMap (hG : IsSpecial G) :
    Additive (G ⧸ Subgroup.center G) →ₗ[ZMod p]
      (Additive (G ⧸ Subgroup.center G) →ₗ[ZMod p]
        Additive (Subgroup.center G)) :=
  ({ toFun := hG.quotientCommutatorRightLinearMap (p := p)
     map_zero' := by
       apply LinearMap.ext
       intro y
       apply Additive.toMul.injective
       simp only [quotientCommutatorRightLinearMap_apply, toMul_ofMul,
         toMul_zero, map_one]
       change (1 : Subgroup.center G) = 1
       rfl
     map_add' := by
       intro x y
       apply LinearMap.ext
       intro z
       apply Additive.toMul.injective
       simp only [quotientCommutatorRightLinearMap_apply,
         LinearMap.add_apply, toMul_ofMul, toMul_add]
       exact DFunLike.congr_fun
         (hG.quotientCommutatorPairing.map_mul x.toMul y.toMul) z.toMul } :
    Additive (G ⧸ Subgroup.center G) →+
      (Additive (G ⧸ Subgroup.center G) →ₗ[ZMod p]
        Additive (Subgroup.center G))).toZModLinearMap p

@[simp]
theorem quotientCommutatorLinearMap_apply (hG : IsSpecial G)
    (x y : Additive (G ⧸ Subgroup.center G)) :
    hG.quotientCommutatorLinearMap (p := p) x y =
      Additive.ofMul
        (hG.quotientCommutatorPairing x.toMul y.toMul) :=
  rfl

/-- The linearized quotient form is alternating. -/
@[simp]
theorem quotientCommutatorLinearMap_self (hG : IsSpecial G)
    (x : Additive (G ⧸ Subgroup.center G)) :
    hG.quotientCommutatorLinearMap (p := p) x x = 0 := by
  apply Additive.toMul.injective
  simpa only [quotientCommutatorLinearMap_apply, toMul_ofMul,
    toMul_zero] using hG.quotientCommutatorPairing_self x.toMul

/-- The linearized quotient form has trivial left radical. -/
theorem quotientCommutatorLinearMap_nondegenerate (hG : IsSpecial G)
    (x : Additive (G ⧸ Subgroup.center G))
    (hx : ∀ y : Additive (G ⧸ Subgroup.center G),
      hG.quotientCommutatorLinearMap (p := p) x y = 0) : x = 0 := by
  apply Additive.toMul.injective
  rw [toMul_zero]
  apply hG.quotientCommutatorPairing_nondegenerate x.toMul
  intro y
  simpa only [quotientCommutatorLinearMap_apply, toMul_ofMul,
    toMul_zero] using
      congrArg Additive.toMul (hx (Additive.ofMul y))

/-- The linearized pairing embeds the quotient module into its dual. -/
theorem quotientCommutatorLinearMap_injective (hG : IsSpecial G) :
    Function.Injective (hG.quotientCommutatorLinearMap (p := p)) := by
  intro x y hxy
  apply Additive.toMul.injective
  apply hG.quotientCommutatorPairing_injective
  apply MonoidHom.ext
  intro z
  simpa only [quotientCommutatorLinearMap_apply, toMul_ofMul] using
    congrArg Additive.toMul
      (LinearMap.congr_fun hxy (Additive.ofMul z))

end IsSpecial

end Submission.OddOrder.MathlibSupport
