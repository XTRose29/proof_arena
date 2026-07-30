import Submission.ClassTwoLimit

namespace Submission.Helpers

noncomputable section

lemma commutatorCharMap_ker_inf_le_add
    (G : Type) [Group G]
    (hcentral : commutator G ≤ Subgroup.center G)
    (psi chi : AddChar (Additive (commutator G)) ℂ) :
    (commutatorCharMap G hcentral psi).ker ⊓
        (commutatorCharMap G hcentral chi).ker ≤
      (commutatorCharMap G hcentral (psi + chi)).ker := by
  intro x hx
  change commutatorAddChar G hcentral psi x.toMul = 0 ∧
    commutatorAddChar G hcentral chi x.toMul = 0 at hx
  change commutatorAddChar G hcentral (psi + chi) x.toMul = 0
  have hsum : commutatorAddChar G hcentral (psi + chi) x.toMul =
      commutatorAddChar G hcentral psi x.toMul +
        commutatorAddChar G hcentral chi x.toMul := by rfl
  rw [hsum, hx.1, hx.2]
  simp

lemma commutatorCharMap_index_add_le_mul
    (G : Type) [Group G] [Finite G]
    (hcentral : commutator G ≤ Subgroup.center G)
    (psi chi : AddChar (Additive (commutator G)) ℂ) :
    (commutatorCharMap G hcentral (psi + chi)).ker.index ≤
      (commutatorCharMap G hcentral psi).ker.index *
        (commutatorCharMap G hcentral chi).ker.index := by
  let H := (commutatorCharMap G hcentral psi).ker
  let K := (commutatorCharMap G hcentral chi).ker
  let L := (commutatorCharMap G hcentral (psi + chi)).ker
  letI : (H ⊓ K).FiniteIndex :=
    AddSubgroup.finiteIndex_of_finite (H := H ⊓ K)
  have hsub : H ⊓ K ≤ L := by
    simpa [H, K, L] using commutatorCharMap_ker_inf_le_add G hcentral psi chi
  change L.index ≤ H.index * K.index
  exact (AddSubgroup.index_antitone hsub).trans AddSubgroup.index_inf_le

lemma commutatorCharMap_ker_unitChar_inv
    (G : Type) [Group G]
    (hcentral : commutator G ≤ Subgroup.center G)
    (chi : commutator G →* ℂˣ) :
    (commutatorCharMap G hcentral (unitCharToComplex chi⁻¹)).ker =
      (commutatorCharMap G hcentral (unitCharToComplex chi)).ker := by
  ext x
  change commutatorAddChar G hcentral (unitCharToComplex chi⁻¹) x.toMul = 0 ↔
    commutatorAddChar G hcentral (unitCharToComplex chi) x.toMul = 0
  constructor <;> intro hx <;> apply AddChar.ext <;> intro y
  · have hy := congrArg (fun c : AddChar (Additive G) ℂ => c y) hx
    let z : commutator G := Multiplicative.ofAdd
      (Additive.ofMul (derivedCommutator G x.toMul y.toMul))
    change ((chi⁻¹ z : ℂˣ) : ℂ) = 1 at hy
    have hu : chi⁻¹ z = 1 := Units.ext hy
    change (chi z)⁻¹ = 1 at hu
    have hz : chi z = 1 := inv_eq_one.mp hu
    change (chi z : ℂ) = 1
    exact congrArg (fun u : ℂˣ => (u : ℂ)) hz
  · have hy := congrArg (fun c : AddChar (Additive G) ℂ => c y) hx
    let z : commutator G := Multiplicative.ofAdd
      (Additive.ofMul (derivedCommutator G x.toMul y.toMul))
    change (chi z : ℂ) = 1 at hy
    have hz : chi z = 1 := Units.ext hy
    have hu : chi⁻¹ z = 1 := by
      change (chi z)⁻¹ = 1
      exact inv_eq_one.mpr hz
    change ((chi⁻¹ z : ℂˣ) : ℂ) = 1
    exact congrArg (fun u : ℂˣ => (u : ℂ)) hu

lemma commutatorCharMap_index_unitChar_inv
    (G : Type) [Group G]
    (hcentral : commutator G ≤ Subgroup.center G)
    (chi : commutator G →* ℂˣ) :
    (commutatorCharMap G hcentral (unitCharToComplex chi⁻¹)).ker.index =
      (commutatorCharMap G hcentral (unitCharToComplex chi)).ker.index := by
  rw [commutatorCharMap_ker_unitChar_inv]

lemma commutatorCharMap_index_unitChar_one
    (G : Type) [Group G] [Finite G]
    (hcentral : commutator G ≤ Subgroup.center G) :
    (commutatorCharMap G hcentral
      (unitCharToComplex (1 : commutator G →* ℂˣ))).ker.index = 1 := by
  have hzero : unitCharToComplex (1 : commutator G →* ℂˣ) = 0 := by rfl
  rw [hzero]
  have hmap : commutatorCharMap G hcentral 0 = 0 := by
    ext x y
    rfl
  rw [hmap]
  simp

end

end Submission.Helpers
