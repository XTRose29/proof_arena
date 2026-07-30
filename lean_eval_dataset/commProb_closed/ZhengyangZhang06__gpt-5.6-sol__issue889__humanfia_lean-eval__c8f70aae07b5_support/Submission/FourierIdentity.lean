import Submission.FourierFormula

namespace Submission.Helpers

open scoped BigOperators commutatorElement

noncomputable section

lemma commProb_eq_expect_inv_commutatorCharMap_index
    (G : Type) [Group G] [Finite G]
    (hcentral : commutator G ≤ Subgroup.center G) :
    letI := commutatorCommGroupOfLeCenter G hcentral
    letI := Fintype.ofFinite (commutator G)
    ((commProb G : ℚ) : ℂ) =
      𝔼 psi : AddChar (Additive (commutator G)) ℂ,
        1 / ((commutatorCharMap G hcentral psi).ker.index : ℂ) := by
  classical
  letI fintypeG : Fintype G := Fintype.ofFinite G
  letI commGroup : CommGroup (commutator G) :=
    commutatorCommGroupOfLeCenter G hcentral
  letI fintypeComm : Fintype (commutator G) := Fintype.ofFinite (commutator G)
  letI fintypeDual : Fintype (AddChar (Additive (commutator G)) ℂ) :=
    Fintype.ofFinite (AddChar (Additive (commutator G)) ℂ)
  calc
    ((commProb G : ℚ) : ℂ) =
        𝔼 x : G, 𝔼 y : G, if x * y = y * x then (1 : ℂ) else 0 :=
      (expect_commute_indicator_eq_commProb G).symm
    _ = 𝔼 x : G, 𝔼 y : G,
        𝔼 psi : AddChar (Additive (commutator G)) ℂ,
          psi (Additive.ofMul (derivedCommutator G x y)) := by
      apply Finset.expect_congr rfl
      intro x _
      apply Finset.expect_congr rfl
      intro y _
      exact (expect_derived_character_eq_commute_indicator G hcentral x y).symm
    _ = 𝔼 psi : AddChar (Additive (commutator G)) ℂ, 𝔼 x : G,
        𝔼 y : G, psi (Additive.ofMul (derivedCommutator G x y)) :=
      @expect_rotate_three G G (AddChar (Additive (commutator G)) ℂ)
        fintypeG fintypeG fintypeDual
        (fun x y psi => psi (Additive.ofMul (derivedCommutator G x y)))
    _ = 𝔼 psi : AddChar (Additive (commutator G)) ℂ,
        1 / ((commutatorCharMap G hcentral psi).ker.index : ℂ) := by
      apply Finset.expect_congr rfl
      intro psi _
      exact expect_commutator_character_on_group_eq_inv_index G hcentral psi

end

end Submission.Helpers
