import Submission.Fourier

namespace Submission.Helpers

open scoped BigOperators commutatorElement

noncomputable section

lemma expect_commutator_character_eq_inv_index
    (G : Type) [Group G] [Fintype G]
    (hcentral : commutator G ≤ Subgroup.center G)
    (psi : AddChar (Additive (commutator G)) ℂ) :
    (𝔼 x : Additive G, 𝔼 y : Additive G,
      psi (Additive.ofMul (derivedCommutator G x.toMul y.toMul))) =
        1 / ((commutatorCharMap G hcentral psi).ker.index : ℂ) := by
  classical
  calc
    _ = 𝔼 x : Additive G,
        if commutatorAddChar G hcentral psi x.toMul = 0 then (1 : ℂ) else 0 := by
      apply Finset.expect_congr rfl
      intro x _
      exact AddChar.expect_eq_ite (commutatorAddChar G hcentral psi x.toMul)
    _ = _ := by
      change (𝔼 x : Additive G,
        if commutatorCharMap G hcentral psi x = 0 then (1 : ℂ) else 0) = _
      exact expect_zero_fiber_eq_inv_index
        (A := Additive G) (B := AddChar (Additive G) ℂ)
        (commutatorCharMap G hcentral psi)

lemma expect_commutator_character_on_group_eq_inv_index
    (G : Type) [Group G] [Fintype G]
    (hcentral : commutator G ≤ Subgroup.center G)
    (psi : AddChar (Additive (commutator G)) ℂ) :
    (𝔼 x : G, 𝔼 y : G,
      psi (Additive.ofMul (derivedCommutator G x y))) =
        1 / ((commutatorCharMap G hcentral psi).ker.index : ℂ) := by
  classical
  calc
    _ = 𝔼 x : Additive G, 𝔼 y : Additive G,
        psi (Additive.ofMul (derivedCommutator G x.toMul y.toMul)) := by
      apply Fintype.expect_equiv Additive.ofMul
      intro x
      apply Fintype.expect_equiv Additive.ofMul
      intro y
      rfl
    _ = _ := expect_commutator_character_eq_inv_index G hcentral psi

lemma expect_derived_character_eq_commute_indicator
    (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (hcentral : commutator G ≤ Subgroup.center G) (x y : G) :
    letI := commutatorCommGroupOfLeCenter G hcentral
    (𝔼 psi : AddChar (Additive (commutator G)) ℂ,
      psi (Additive.ofMul (derivedCommutator G x y))) =
        if x * y = y * x then (1 : ℂ) else 0 := by
  classical
  letI := commutatorCommGroupOfLeCenter G hcentral
  letI := Fintype.ofFinite (commutator G)
  rw [AddChar.expect_apply_eq_ite]
  by_cases hxy : x * y = y * x
  · have hc : derivedCommutator G x y = 1 := by
      apply Subtype.ext
      exact commutatorElement_eq_one_iff_mul_comm.mpr hxy
    simp [hxy, hc]
  · have hc : derivedCommutator G x y ≠ 1 := by
      intro h
      apply hxy
      exact commutatorElement_eq_one_iff_mul_comm.mp (congrArg Subtype.val h)
    simp [hxy, hc]

end

end Submission.Helpers
