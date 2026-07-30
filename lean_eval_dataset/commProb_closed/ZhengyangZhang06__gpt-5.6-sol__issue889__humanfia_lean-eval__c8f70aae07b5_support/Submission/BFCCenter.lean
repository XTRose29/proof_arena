import Submission.BFCProfile

namespace Submission.Helpers

open scoped BigOperators Filter Topology commutatorElement

noncomputable section

lemma classTwo_center_toAddSubgroup_eq_iInf_character_kernels
    (G : Type) [Group G] [Finite G]
    (hcentral : commutator G ≤ Subgroup.center G) :
    letI := commutatorCommGroupOfLeCenter G hcentral
    (Subgroup.center G).toAddSubgroup =
      ⨅ chi : commutator G →* ℂˣ,
        (commutatorCharMap G hcentral (unitCharToComplex chi)).ker := by
  letI := commutatorCommGroupOfLeCenter G hcentral
  ext x
  simp only [Additive.mem_toAddSubgroup, AddSubgroup.mem_iInf,
    AddMonoidHom.mem_ker]
  constructor
  · intro hx chi
    apply AddChar.ext
    intro y
    change (unitCharToComplex chi)
      (Additive.ofMul (derivedCommutator G x.toMul y.toMul)) = 1
    have hxy : x.toMul * y.toMul = y.toMul * x.toMul :=
      (Subgroup.mem_center_iff.mp hx y.toMul).symm
    have hd : derivedCommutator G x.toMul y.toMul = 1 := by
      apply Subtype.ext
      exact commutatorElement_eq_one_iff_mul_comm.mpr hxy
    rw [hd]
    exact (unitCharToComplex chi).map_zero_eq_one
  · intro hx
    rw [Subgroup.mem_center_iff]
    intro y
    let d : commutator G := derivedCommutator G x.toMul y
    have hall : ∀ chi : commutator G →* ℂˣ, chi d = 1 := by
      intro chi
      have hker := hx chi
      have hy := DFunLike.congr_fun hker (Additive.ofMul y)
      change (unitCharToComplex chi) (Additive.ofMul d) = 1 at hy
      exact Units.ext hy
    have hdmem : d ∈ (⊥ : Subgroup (commutator G)) := by
      rw [← CommGroup.forall_monoidHom_apply_eq_one_iff ℂ
        (⊥ : Subgroup (commutator G)) d]
      intro chi _
      exact hall chi
    have hd : d = 1 := by simpa using hdmem
    have hcomm : x.toMul * y = y * x.toMul := by
      apply commutatorElement_eq_one_iff_mul_comm.mp
      exact congrArg Subtype.val hd
    exact hcomm.symm

lemma classTwo_center_index_le_characterKernel_product
    (G : Type) [Group G] [Finite G]
    (hcentral : commutator G ≤ Subgroup.center G) :
    letI := commutatorCommGroupOfLeCenter G hcentral
    (Subgroup.center G).index ≤
      ∏ chi : commutator G →* ℂˣ,
        (commutatorCharMap G hcentral (unitCharToComplex chi)).ker.index := by
  classical
  letI := commutatorCommGroupOfLeCenter G hcentral
  rw [← Subgroup.index_toAddSubgroup]
  rw [classTwo_center_toAddSubgroup_eq_iInf_character_kernels G hcentral]
  exact AddSubgroup.index_iInf_le _

lemma classTwo_center_toAddSubgroup_eq_iInf_addChar_kernels
    (G : Type) [Group G] [Finite G]
    (hcentral : commutator G ≤ Subgroup.center G) :
    letI := commutatorCommGroupOfLeCenter G hcentral
    (Subgroup.center G).toAddSubgroup =
      ⨅ psi : AddChar (Additive (commutator G)) ℂ,
        (commutatorCharMap G hcentral psi).ker := by
  letI := commutatorCommGroupOfLeCenter G hcentral
  ext x
  simp only [Additive.mem_toAddSubgroup, AddSubgroup.mem_iInf,
    AddMonoidHom.mem_ker]
  constructor
  · intro hx psi
    apply AddChar.ext
    intro y
    change psi (Additive.ofMul (derivedCommutator G x.toMul y.toMul)) = 1
    have hxy : x.toMul * y.toMul = y.toMul * x.toMul :=
      (Subgroup.mem_center_iff.mp hx y.toMul).symm
    have hd : derivedCommutator G x.toMul y.toMul = 1 := by
      apply Subtype.ext
      exact commutatorElement_eq_one_iff_mul_comm.mpr hxy
    rw [hd]
    exact psi.map_zero_eq_one
  · intro hx
    rw [Subgroup.mem_center_iff]
    intro y
    let d : commutator G := derivedCommutator G x.toMul y
    have hall : ∀ chi : commutator G →* ℂˣ, chi d = 1 := by
      intro chi
      have hker := hx (unitCharToComplex chi)
      have hy := DFunLike.congr_fun hker (Additive.ofMul y)
      change (unitCharToComplex chi) (Additive.ofMul d) = 1 at hy
      exact Units.ext hy
    have hdmem : d ∈ (⊥ : Subgroup (commutator G)) := by
      rw [← CommGroup.forall_monoidHom_apply_eq_one_iff ℂ
        (⊥ : Subgroup (commutator G)) d]
      intro chi _
      exact hall chi
    have hd : d = 1 := by simpa using hdmem
    have hcomm : x.toMul * y = y * x.toMul := by
      apply commutatorElement_eq_one_iff_mul_comm.mp
      exact congrArg Subtype.val hd
    exact hcomm.symm

lemma classTwo_center_index_le_addCharKernel_product
    (G : Type) [Group G] [Finite G]
    (hcentral : commutator G ≤ Subgroup.center G) :
    letI := commutatorCommGroupOfLeCenter G hcentral
    (Subgroup.center G).index ≤
      ∏ psi : AddChar (Additive (commutator G)) ℂ,
        (commutatorCharMap G hcentral psi).ker.index := by
  classical
  letI := commutatorCommGroupOfLeCenter G hcentral
  rw [← Subgroup.index_toAddSubgroup]
  rw [classTwo_center_toAddSubgroup_eq_iInf_addChar_kernels G hcentral]
  exact AddSubgroup.index_iInf_le _

def conjugationOnCommutatorHom (G : Type) [Group G] :
    G →* MulAut (commutator G) :=
  MulAut.conjNormal

lemma conjugationOnCommutatorHom_ker (G : Type) [Group G] :
    (conjugationOnCommutatorHom G).ker = bfcCore G := by
  ext g
  change conjugationOnCommutatorHom G g = 1 ↔
    ∀ d ∈ (commutator G : Set G), d * g = g * d
  constructor
  · intro hg d hd
    have hdval := congrArg
      (fun e : MulAut (commutator G) => e ⟨d, hd⟩) hg
    have hconj : g * d * g⁻¹ = d := congrArg Subtype.val hdval
    exact (mul_inv_eq_iff_eq_mul.mp hconj).symm
  · intro hg
    apply MulEquiv.ext
    intro d
    apply Subtype.ext
    change g * d.1 * g⁻¹ = d.1
    rw [← hg d.1 d.2]
    simp

lemma bfcCore_index_le_commutatorCard_pow
    (G : Type) [Group G] [Finite G] :
    (bfcCore G).index ≤ Nat.card (commutator G) ^ Nat.card (commutator G) := by
  let f := conjugationOnCommutatorHom G
  rw [← conjugationOnCommutatorHom_ker G, Subgroup.index_ker]
  calc
    Nat.card f.range ≤ Nat.card (MulAut (commutator G)) :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    _ ≤ Nat.card (commutator G → commutator G) :=
      Nat.card_le_card_of_injective
        (fun e : MulAut (commutator G) => (e : commutator G → commutator G))
        (by
          intro e₁ e₂ h
          apply MulEquiv.ext
          exact congrFun h)
    _ = Nat.card (commutator G) ^ Nat.card (commutator G) := by
      rw [Nat.card_fun]

noncomputable def bfcCoreCenterActionHom (G : Type) [Group G] :
    let C := bfcCore G
    letI := C.toGroup
    Subgroup.center C →* ((G ⧸ C) → bfcCoreCommutatorIntersection G) := by
  let C := bfcCore G
  letI := C.toGroup
  exact {
    toFun := fun z q => bfcCoreMixedCommutator G (Quotient.out q) z.1
    map_one' := by
      funext q
      apply Subtype.ext
      simp [bfcCoreMixedCommutator]
    map_mul' := by
      intro z w
      funext q
      exact bfcCoreMixedCommutator_mul_right G (Quotient.out q) z.1 w.1 }

noncomputable def bfcCoreCenterActionKernelEquivCenter
    (G : Type) [Group G] :
    let C := bfcCore G
    letI := C.toGroup
    (bfcCoreCenterActionHom G).ker ≃ Subgroup.center G := by
  let C := bfcCore G
  letI := C.toGroup
  let f := bfcCoreCenterActionHom G
  refine {
    toFun := fun z => ⟨z.1.1.1, ?_⟩
    invFun := fun z => ⟨⟨⟨z.1, ?_⟩, ?_⟩, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · rw [Subgroup.mem_center_iff]
    intro g
    let c := leftSubgroupPart C g
    let q : G ⧸ C := g
    have hzker : f z.1 = 1 := z.2
    have hzqValue := congrArg
      (fun h : (G ⧸ C) → bfcCoreCommutatorIntersection G => h q) hzker
    have hzqComm : Quotient.out q * z.1.1.1 = z.1.1.1 * Quotient.out q := by
      apply commutatorElement_eq_one_iff_mul_comm.mp
      exact congrArg Subtype.val hzqValue
    have hzc : (c : G) * z.1.1.1 = z.1.1.1 * c := by
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.1.2 c)
    rw [← leftSubgroupPart_mul_out C g]
    calc
      ((c : G) * Quotient.out q) * z.1.1.1 =
          (c : G) * (Quotient.out q * z.1.1.1) := by simp [mul_assoc]
      _ = (c : G) * (z.1.1.1 * Quotient.out q) := by rw [hzqComm]
      _ = ((c : G) * z.1.1.1) * Quotient.out q := by simp [mul_assoc]
      _ = (z.1.1.1 * c) * Quotient.out q := by rw [hzc]
      _ = z.1.1.1 * ((c : G) * Quotient.out q) := by simp [mul_assoc]
  · exact Subgroup.center_le_centralizer (commutator G) z.2
  · rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp z.2 c.1
  · change f (⟨⟨z.1, _⟩, _⟩ : Subgroup.center C) = 1
    funext q
    apply Subtype.ext
    change ⁅Quotient.out q, z.1⁆ = 1
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact Subgroup.mem_center_iff.mp z.2 (Quotient.out q)
  · intro z
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl
  · intro z
    apply Subtype.ext
    rfl

lemma bfcCoreCommutatorIntersection_card_le
    (G : Type) [Group G] [Finite G] :
    Nat.card (bfcCoreCommutatorIntersection G) ≤ Nat.card (commutator G) := by
  exact Nat.card_le_card_of_injective
    (fun z : bfcCoreCommutatorIntersection G =>
      (⟨z.1, z.2.1⟩ : commutator G))
    (by
      intro x y h
      have hv : x.1 = y.1 := congrArg
        (fun d : commutator G => (d : G)) h
      exact Subtype.ext hv)

lemma bfcCoreCenterActionKernel_index_le
    (G : Type) [Group G] [Finite G] :
    let C := bfcCore G
    letI := C.toGroup
    (bfcCoreCenterActionHom G).ker.index ≤
      Nat.card (commutator G) ^ C.index := by
  let C := bfcCore G
  letI := C.toGroup
  let f := bfcCoreCenterActionHom G
  rw [Subgroup.index_ker]
  calc
    Nat.card f.range ≤
        Nat.card ((G ⧸ C) → bfcCoreCommutatorIntersection G) :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    _ = Nat.card (bfcCoreCommutatorIntersection G) ^ Nat.card (G ⧸ C) := by
      rw [Nat.card_fun]
    _ ≤ Nat.card (commutator G) ^ C.index := by
      rw [← C.index_eq_card]
      exact Nat.pow_le_pow_left (bfcCoreCommutatorIntersection_card_le G) _

lemma center_index_eq_bfcCore_factors
    (G : Type) [Group G] [Finite G] :
    let C := bfcCore G
    letI := C.toGroup
    (Subgroup.center G).index =
      (bfcCoreCenterActionHom G).ker.index *
        (Subgroup.center C).index * C.index := by
  let C := bfcCore G
  letI := C.toGroup
  let f := bfcCoreCenterActionHom G
  have hkcard : Nat.card f.ker = Nat.card (Subgroup.center G) :=
    Nat.card_congr (bfcCoreCenterActionKernelEquivCenter G)
  have hmul : Nat.card (Subgroup.center G) *
        (f.ker.index * (Subgroup.center C).index * C.index) =
      Nat.card (Subgroup.center G) * (Subgroup.center G).index := by
    calc
      Nat.card (Subgroup.center G) *
          (f.ker.index * (Subgroup.center C).index * C.index) =
          (Nat.card f.ker * f.ker.index) *
            (Subgroup.center C).index * C.index := by
        rw [← hkcard]
        simp [mul_assoc]
      _ = Nat.card (Subgroup.center C) *
            (Subgroup.center C).index * C.index := by
        rw [f.ker.card_mul_index]
      _ = Nat.card C * C.index := by
        rw [(Subgroup.center C).card_mul_index]
      _ = Nat.card G := C.card_mul_index
      _ = Nat.card (Subgroup.center G) * (Subgroup.center G).index :=
        (Subgroup.center G).card_mul_index.symm
  exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos hmul).symm

end

end Submission.Helpers
