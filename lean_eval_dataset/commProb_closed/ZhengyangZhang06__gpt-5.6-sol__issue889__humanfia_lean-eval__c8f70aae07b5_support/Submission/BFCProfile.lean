import Submission.BFCClosure

namespace Submission.Helpers

open scoped BigOperators commutatorElement

noncomputable section

lemma bfcCore_conjugate_commutator
    (G : Type) [Group G] (d : bfcCore G) (x y : G) :
    d.1 * ⁅x, y⁆ * d.1⁻¹ = ⁅x, y⁆ := by
  have hcomm : d.1 * ⁅x, y⁆ = ⁅x, y⁆ * d.1 := by
    exact (d.2 ⁅x, y⁆ (derivedCommutator G x y).2).symm
  rw [hcomm]
  simp [mul_assoc]

lemma bfcCore_commutator_mul_mul
    (G : Type) [Group G] (a b : G) (d e : bfcCore G) :
    ⁅d.1 * a, e.1 * b⁆ =
      ⁅a, e.1⁆ * ⁅a, b⁆ * (⁅d.1, e.1⁆ * ⁅d.1, b⁆) := by
  calc
    ⁅d.1 * a, e.1 * b⁆ =
        d.1 * ⁅a, e.1 * b⁆ * d.1⁻¹ * ⁅d.1, e.1 * b⁆ :=
      commutatorElement_mul_left_eq_conj_mul d.1 a (e.1 * b)
    _ = ⁅a, e.1 * b⁆ * ⁅d.1, e.1 * b⁆ := by
      rw [bfcCore_conjugate_commutator G d a (e.1 * b)]
    _ = (⁅a, e.1⁆ * (e.1 * ⁅a, b⁆ * e.1⁻¹)) *
        (⁅d.1, e.1⁆ * (e.1 * ⁅d.1, b⁆ * e.1⁻¹)) := by
      rw [commutatorElement_mul_right_eq_mul_conj,
        commutatorElement_mul_right_eq_mul_conj]
      simp [mul_assoc]
    _ = (⁅a, e.1⁆ * ⁅a, b⁆) * (⁅d.1, e.1⁆ * ⁅d.1, b⁆) := by
      rw [bfcCore_conjugate_commutator G e a b,
        bfcCore_conjugate_commutator G e d.1 b]
    _ = _ := by simp [mul_assoc]

def bfcCoreTwistUnitChar
    (G : Type) [Group G]
    (theta : letI := bfcCoreCommutatorIntersectionCommGroup G;
      bfcCoreCommutatorIntersection G →* ℂˣ)
    (a : G) : bfcCore G →* ℂˣ where
  toFun d := theta (bfcCoreMixedCommutator G a d)
  map_one' := by
    have hzero : bfcCoreMixedCommutator G a 1 = 1 := by
      apply Subtype.ext
      simp [bfcCoreMixedCommutator]
    rw [hzero, map_one]
  map_mul' := by
    intro d e
    rw [bfcCoreMixedCommutator_mul_right, map_mul]

lemma bfcCoreCharacterValue_eq_zeroExtension
    (G : Type) [Group G] [Finite G]
    (hcentral : let C := bfcCore G;
      letI := C.toGroup
      commutator C ≤ Subgroup.center C)
    (chi : let C := bfcCore G;
      letI := C.toGroup
      letI := commutatorCommGroupOfLeCenter C hcentral
      commutator C →* ℂˣ)
    (x y : G) (hxy : ⁅x, y⁆ ∈ bfcCoreCommutatorIntersection G) :
    bfcCoreCharacterValue G hcentral chi x y =
      bfcCoreCharacterZeroExtension G hcentral chi ⟨⁅x, y⁆, hxy⟩ := by
  classical
  let C := bfcCore G
  letI := C.toGroup
  letI := commutatorCommGroupOfLeCenter C hcentral
  letI := bfcCoreCommutatorIntersectionCommGroup G
  let z : bfcCoreCommutatorIntersection G := ⟨⁅x, y⁆, hxy⟩
  change (if hrange : ⁅x, y⁆ ∈ (bfcCoreDerivedEmbedding G).range then
      (chi ((bfcCoreDerivedEquivRange G).symm ⟨⁅x, y⁆, hrange⟩) : ℂ)
    else 0) =
    if hz : z ∈ (bfcCoreDerivedEmbeddingToIntersection G).range then
      (chi ((bfcCoreDerivedEquivIntersectionRange G).symm ⟨z, hz⟩) : ℂ)
    else 0
  by_cases hrange : ⁅x, y⁆ ∈ (bfcCoreDerivedEmbedding G).range
  · obtain ⟨d, hd⟩ := hrange
    have hz : z ∈ (bfcCoreDerivedEmbeddingToIntersection G).range := by
      refine ⟨d, ?_⟩
      apply Subtype.ext
      exact hd
    have hdG : (bfcCoreDerivedEquivRange G).symm
        ⟨⁅x, y⁆, ⟨d, hd⟩⟩ = d := by
      apply (bfcCoreDerivedEquivRange G).injective
      rw [MulEquiv.apply_symm_apply]
      apply Subtype.ext
      exact hd.symm
    have hdI : (bfcCoreDerivedEquivIntersectionRange G).symm
        ⟨z, hz⟩ = d := by
      have hpair :
          (⟨z, hz⟩ : (bfcCoreDerivedEmbeddingToIntersection G).range) =
            (bfcCoreDerivedEquivIntersectionRange G) d := by
        apply Subtype.ext
        apply Subtype.ext
        exact hd.symm
      calc
        (bfcCoreDerivedEquivIntersectionRange G).symm ⟨z, hz⟩ =
            (bfcCoreDerivedEquivIntersectionRange G).symm
              ((bfcCoreDerivedEquivIntersectionRange G) d) := congrArg _ hpair
        _ = d := MulEquiv.symm_apply_apply _ d
    rw [dif_pos ⟨d, hd⟩, dif_pos hz, hdG, hdI]
  · have hz : z ∉ (bfcCoreDerivedEmbeddingToIntersection G).range := by
      rintro ⟨d, hd⟩
      apply hrange
      refine ⟨d, ?_⟩
      exact congrArg Subtype.val hd
    rw [dif_neg hrange, dif_neg hz]

lemma bfcCore_commutator_mem_intersection_mul_mul_iff
    (G : Type) [Group G] (a b : G) (d e : bfcCore G) :
    ⁅d.1 * a, e.1 * b⁆ ∈ bfcCoreCommutatorIntersection G ↔
      ⁅a, b⁆ ∈ bfcCoreCommutatorIntersection G := by
  let C := bfcCore G
  have hae : ⁅a, e.1⁆ ∈ C := (bfcCoreMixedCommutator G a e).2.2
  have hde : ⁅d.1, e.1⁆ ∈ C := by
    rw [commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem d.2 e.2) (C.inv_mem d.2)) (C.inv_mem e.2)
  have hdb : ⁅d.1, b⁆ ∈ C := by
    have hbd := C.inv_mem (bfcCoreMixedCommutator G b d).2.2
    change ⁅b, d.1⁆⁻¹ ∈ C at hbd
    rw [commutatorElement_inv] at hbd
    exact hbd
  constructor
  · intro htotal
    constructor
    · exact (derivedCommutator G a b).2
    · have hcancel := C.mul_mem
          (C.mul_mem (C.inv_mem hae) htotal.2)
          (C.inv_mem (C.mul_mem hde hdb))
      have heq : ⁅a, b⁆ =
          ⁅a, e.1⁆⁻¹ * ⁅d.1 * a, e.1 * b⁆ *
            (⁅d.1, e.1⁆ * ⁅d.1, b⁆)⁻¹ := by
        rw [bfcCore_commutator_mul_mul G a b d e]
        group
      rw [heq]
      exact hcancel
  · intro hbase
    constructor
    · exact (derivedCommutator G (d.1 * a) (e.1 * b)).2
    · rw [bfcCore_commutator_mul_mul G a b d e]
      exact C.mul_mem (C.mul_mem hae hbase.2) (C.mul_mem hde hdb)

lemma bfcCore_extension_coset_value
    (G : Type) [Group G]
    (_hcentral : let C := bfcCore G;
      letI := C.toGroup
      commutator C ≤ Subgroup.center C)
    (chi : let C := bfcCore G;
      letI := C.toGroup
      commutator C →* ℂˣ)
    (theta : letI := bfcCoreCommutatorIntersectionCommGroup G;
      bfcCoreCommutatorIntersection G →* ℂˣ)
    (hrestrict : ∀ d,
      theta (bfcCoreDerivedEmbeddingToIntersection G d) = chi d)
    (a b : G) (d e : bfcCore G)
    (hab : ⁅a, b⁆ ∈ bfcCoreCommutatorIntersection G) :
    let htotal := (bfcCore_commutator_mem_intersection_mul_mul_iff G a b d e).2 hab
    (theta ⟨⁅d.1 * a, e.1 * b⁆, htotal⟩ : ℂ) =
      (theta ⟨⁅a, b⁆, hab⟩ : ℂ) *
        ((bfcCoreTwistUnitChar G theta b)⁻¹ d : ℂ) *
        (chi (derivedCommutator (bfcCore G) d e) : ℂ) *
        (bfcCoreTwistUnitChar G theta a e : ℂ) := by
  let C := bfcCore G
  letI := C.toGroup
  letI := bfcCoreCommutatorIntersectionCommGroup G
  let htotal := (bfcCore_commutator_mem_intersection_mul_mul_iff G a b d e).2 hab
  let ztotal : bfcCoreCommutatorIntersection G :=
    ⟨⁅d.1 * a, e.1 * b⁆, htotal⟩
  let zae := bfcCoreMixedCommutator G a e
  let zab : bfcCoreCommutatorIntersection G := ⟨⁅a, b⁆, hab⟩
  let zde := bfcCoreDerivedEmbeddingToIntersection G
    (derivedCommutator C d e)
  let zbd := bfcCoreMixedCommutator G b d
  have htotalValue : ztotal = zae * zab * (zde * zbd⁻¹) := by
    apply Subtype.ext
    change ⁅d.1 * a, e.1 * b⁆ =
      ⁅a, e.1⁆ * ⁅a, b⁆ * (⁅d.1, e.1⁆ * ⁅b, d.1⁆⁻¹)
    rw [commutatorElement_inv]
    exact bfcCore_commutator_mul_mul G a b d e
  change (theta ztotal : ℂ) = _
  rw [htotalValue, map_mul, map_mul, map_mul, map_inv, hrestrict]
  push_cast
  dsimp [bfcCoreTwistUnitChar, zae, zab, zbd, C]
  rw [Units.val_inv_eq_inv_val]
  ring

lemma norm_expect_bfcCoreCharacterValue_coset_le_inv_index
    (G : Type) [Group G] [Finite G]
    (hcentral : let C := bfcCore G;
      letI := C.toGroup
      commutator C ≤ Subgroup.center C)
    (chi : let C := bfcCore G;
      letI := C.toGroup
      letI := commutatorCommGroupOfLeCenter C hcentral
      commutator C →* ℂˣ)
    (a b : G) :
    let C := bfcCore G
    letI := C.toGroup
    letI := Fintype.ofFinite C
    ‖𝔼 d : C, 𝔼 e : C,
      bfcCoreCharacterValue G hcentral chi (d.1 * a) (e.1 * b)‖ ≤
      1 / ((commutatorCharMap C hcentral (unitCharToComplex chi)).ker.index : ℝ) := by
  classical
  let C := bfcCore G
  letI := C.toGroup
  letI := commutatorCommGroupOfLeCenter C hcentral
  letI := Fintype.ofFinite C
  letI := Fintype.ofFinite G
  letI := bfcCoreCommutatorIntersectionCommGroup G
  let X := bfcCoreCharacterExtensionKernel G
  letI := Fintype.ofFinite X
  change ‖𝔼 d : C, 𝔼 e : C,
      bfcCoreCharacterValue G hcentral chi (d.1 * a) (e.1 * b)‖ ≤
    1 / ((commutatorCharMap C hcentral (unitCharToComplex chi)).ker.index : ℝ)
  by_cases hab : ⁅a, b⁆ ∈ bfcCoreCommutatorIntersection G
  · have hrepresentation :
        (𝔼 d : C, 𝔼 e : C,
          bfcCoreCharacterValue G hcentral chi (d.1 * a) (e.1 * b)) =
        𝔼 eta : X, 𝔼 d : C, 𝔼 e : C,
          (((extendedBfcCoreCharacter G hcentral chi * eta.1)
            ⟨⁅d.1 * a, e.1 * b⁆,
              (bfcCore_commutator_mem_intersection_mul_mul_iff
                G a b d e).2 hab⟩ : ℂˣ) : ℂ) := by
      calc
        (𝔼 d : C, 𝔼 e : C,
            bfcCoreCharacterValue G hcentral chi (d.1 * a) (e.1 * b)) =
            𝔼 d : C, 𝔼 e : C, 𝔼 eta : X,
              (((extendedBfcCoreCharacter G hcentral chi * eta.1)
                ⟨⁅d.1 * a, e.1 * b⁆,
                  (bfcCore_commutator_mem_intersection_mul_mul_iff
                    G a b d e).2 hab⟩ : ℂˣ) : ℂ) := by
          apply Finset.expect_congr rfl
          intro d _
          apply Finset.expect_congr rfl
          intro e _
          let z : bfcCoreCommutatorIntersection G :=
            ⟨⁅d.1 * a, e.1 * b⁆,
              (bfcCore_commutator_mem_intersection_mul_mul_iff
                G a b d e).2 hab⟩
          rw [bfcCoreCharacterValue_eq_zeroExtension G hcentral chi]
          exact (expect_extendedBfcCoreCharacter_mul_extensionKernel
            G hcentral chi z).symm
        _ = _ := @expect_rotate_three C C X _ _ _
          (fun d e eta =>
            (((extendedBfcCoreCharacter G hcentral chi * eta.1)
              ⟨⁅d.1 * a, e.1 * b⁆,
                (bfcCore_commutator_mem_intersection_mul_mul_iff
                  G a b d e).2 hab⟩ : ℂˣ) : ℂ))
    rw [hrepresentation]
    calc
      ‖𝔼 eta : X, 𝔼 d : C, 𝔼 e : C,
          (((extendedBfcCoreCharacter G hcentral chi * eta.1)
            ⟨⁅d.1 * a, e.1 * b⁆,
              (bfcCore_commutator_mem_intersection_mul_mul_iff
                G a b d e).2 hab⟩ : ℂˣ) : ℂ)‖ ≤
          𝔼 eta : X, ‖𝔼 d : C, 𝔼 e : C,
            (((extendedBfcCoreCharacter G hcentral chi * eta.1)
              ⟨⁅d.1 * a, e.1 * b⁆,
                (bfcCore_commutator_mem_intersection_mul_mul_iff
                G a b d e).2 hab⟩ : ℂˣ) : ℂ)‖ :=
          RCLike.norm_expect_le (K := ℂ)
      _ ≤ 1 / ((commutatorCharMap C hcentral (unitCharToComplex chi)).ker.index : ℝ) := by
        rw [Fintype.expect_eq_sum_div_card]
        have hcardX : (0 : ℝ) < Fintype.card X := by positivity
        apply (div_le_iff₀ hcardX).2
        calc
          ∑ eta : X, ‖𝔼 d : C, 𝔼 e : C,
              (((extendedBfcCoreCharacter G hcentral chi * eta.1)
                ⟨⁅d.1 * a, e.1 * b⁆,
                  (bfcCore_commutator_mem_intersection_mul_mul_iff
                    G a b d e).2 hab⟩ : ℂˣ) : ℂ)‖ ≤
              ∑ _eta : X,
                (1 / ((commutatorCharMap C hcentral
                  (unitCharToComplex chi)).ker.index : ℝ)) := by
            apply Finset.sum_le_sum
            intro eta _
            let theta := extendedBfcCoreCharacter G hcentral chi * eta.1
            have hrestrict : ∀ z,
                theta (bfcCoreDerivedEmbeddingToIntersection G z) = chi z := by
              intro z
              have heta := eta.2
              change (MonoidHom.restrictHom
                (bfcCoreDerivedEmbeddingToIntersection G).range ℂˣ) eta.1 = 1 at heta
              have hz := DFunLike.congr_fun heta
                ⟨bfcCoreDerivedEmbeddingToIntersection G z, ⟨z, rfl⟩⟩
              change eta.1 (bfcCoreDerivedEmbeddingToIntersection G z) = 1 at hz
              simp [theta, extendedBfcCoreCharacter_apply_embedding, hz]
            have hvalue :
                (𝔼 d : C, 𝔼 e : C,
                  ((theta ⟨⁅d.1 * a, e.1 * b⁆,
                    (bfcCore_commutator_mem_intersection_mul_mul_iff
                      G a b d e).2 hab⟩ : ℂˣ) : ℂ)) =
                (theta ⟨⁅a, b⁆, hab⟩ : ℂ) *
                  (𝔼 d : Additive C,
                    (((bfcCoreTwistUnitChar G theta b)⁻¹ d.toMul : ℂ) *
                      (𝔼 e : Additive C,
                        (chi (derivedCommutator C d.toMul e.toMul) : ℂ) *
                          (bfcCoreTwistUnitChar G theta a e.toMul : ℂ)))) := by
              calc
                (𝔼 d : C, 𝔼 e : C,
                    ((theta ⟨⁅d.1 * a, e.1 * b⁆,
                      (bfcCore_commutator_mem_intersection_mul_mul_iff
                        G a b d e).2 hab⟩ : ℂˣ) : ℂ)) =
                    𝔼 d : Additive C, 𝔼 e : Additive C,
                      ((theta ⟨⁅d.toMul.1 * a, e.toMul.1 * b⁆,
                        (bfcCore_commutator_mem_intersection_mul_mul_iff
                          G a b d.toMul e.toMul).2 hab⟩ : ℂˣ) : ℂ) := by
                    apply Fintype.expect_equiv Additive.ofMul
                    intro d
                    apply Fintype.expect_equiv Additive.ofMul
                    intro e
                    rfl
                _ = _ := by
                  calc
                    (𝔼 d : Additive C, 𝔼 e : Additive C,
                        ((theta ⟨⁅d.toMul.1 * a, e.toMul.1 * b⁆,
                          (bfcCore_commutator_mem_intersection_mul_mul_iff
                            G a b d.toMul e.toMul).2 hab⟩ : ℂˣ) : ℂ)) =
                        𝔼 d : Additive C, 𝔼 e : Additive C,
                          (theta ⟨⁅a, b⁆, hab⟩ : ℂ) *
                            ((bfcCoreTwistUnitChar G theta b)⁻¹ d.toMul : ℂ) *
                            (chi (derivedCommutator C d.toMul e.toMul) : ℂ) *
                            (bfcCoreTwistUnitChar G theta a e.toMul : ℂ) := by
                      apply Finset.expect_congr rfl
                      intro d _
                      apply Finset.expect_congr rfl
                      intro e _
                      exact bfcCore_extension_coset_value G hcentral chi theta
                        hrestrict a b d.toMul e.toMul hab
                    _ = 𝔼 d : Additive C,
                        (theta ⟨⁅a, b⁆, hab⟩ : ℂ) *
                          (((bfcCoreTwistUnitChar G theta b)⁻¹ d.toMul : ℂ) *
                            (𝔼 e : Additive C,
                              (chi (derivedCommutator C d.toMul e.toMul) : ℂ) *
                                (bfcCoreTwistUnitChar G theta a e.toMul : ℂ))) := by
                      apply Finset.expect_congr rfl
                      intro d _
                      calc
                        (𝔼 e : Additive C,
                            (theta ⟨⁅a, b⁆, hab⟩ : ℂ) *
                              ((bfcCoreTwistUnitChar G theta b)⁻¹ d.toMul : ℂ) *
                              (chi (derivedCommutator C d.toMul e.toMul) : ℂ) *
                              (bfcCoreTwistUnitChar G theta a e.toMul : ℂ)) =
                            𝔼 e : Additive C,
                              ((theta ⟨⁅a, b⁆, hab⟩ : ℂ) *
                                ((bfcCoreTwistUnitChar G theta b)⁻¹ d.toMul : ℂ)) *
                              ((chi (derivedCommutator C d.toMul e.toMul) : ℂ) *
                                (bfcCoreTwistUnitChar G theta a e.toMul : ℂ)) := by
                          apply Finset.expect_congr rfl
                          intro e _
                          ring
                        _ = ((theta ⟨⁅a, b⁆, hab⟩ : ℂ) *
                            ((bfcCoreTwistUnitChar G theta b)⁻¹ d.toMul : ℂ)) *
                            (𝔼 e : Additive C,
                              (chi (derivedCommutator C d.toMul e.toMul) : ℂ) *
                                (bfcCoreTwistUnitChar G theta a e.toMul : ℂ)) := by
                          rw [Finset.mul_expect]
                        _ = _ := by ring
                    _ = _ := by
                      rw [Finset.mul_expect]
            rw [hvalue, norm_mul]
            have hconst : ‖(theta ⟨⁅a, b⁆, hab⟩ : ℂ)‖ = 1 := by
              simpa using (unitCharToComplex theta).norm_apply
                (Additive.ofMul ⟨⁅a, b⁆, hab⟩)
            rw [hconst, one_mul]
            exact norm_expect_twisted_unit_commutator_le_inv_index C hcentral chi
              (bfcCoreTwistUnitChar G theta b)⁻¹
              (bfcCoreTwistUnitChar G theta a)
          _ = _ := by
            simp
            ring
  · have hzero : ∀ d e : C,
        bfcCoreCharacterValue G hcentral chi (d.1 * a) (e.1 * b) = 0 := by
      intro d e
      have hnot : ⁅d.1 * a, e.1 * b⁆ ∉ (bfcCoreDerivedEmbedding G).range := by
        rintro ⟨z, hz⟩
        apply hab
        apply (bfcCore_commutator_mem_intersection_mul_mul_iff G a b d e).mp
        constructor
        · exact (derivedCommutator G (d.1 * a) (e.1 * b)).2
        · rw [← hz]
          exact z.1.2
      simp [bfcCoreCharacterValue, hnot]
    simp_rw [hzero]
    simp

def pairPairReorder (A B : Type) :
    ((A × B) × (A × B)) ≃ ((B × B) × (A × A)) where
  toFun p := ((p.1.2, p.2.2), (p.1.1, p.2.1))
  invFun p := ((p.2.1, p.1.1), (p.2.2, p.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

lemma norm_expect_bfcCoreCharacterValue_le_inv_index
    (G : Type) [Group G] [Finite G]
    (hcentral : let C := bfcCore G;
      letI := C.toGroup
      commutator C ≤ Subgroup.center C)
    (chi : let C := bfcCore G;
      letI := C.toGroup
      letI := commutatorCommGroupOfLeCenter C hcentral
      commutator C →* ℂˣ) :
    let C := bfcCore G
    letI := C.toGroup
    letI := Fintype.ofFinite C
    letI := Fintype.ofFinite G
    ‖𝔼 x : G, 𝔼 y : G, bfcCoreCharacterValue G hcentral chi x y‖ ≤
      1 / ((commutatorCharMap C hcentral (unitCharToComplex chi)).ker.index : ℝ) := by
  classical
  let C := bfcCore G
  letI := C.toGroup
  letI := commutatorCommGroupOfLeCenter C hcentral
  letI := Fintype.ofFinite C
  letI := Fintype.ofFinite G
  let Q := G ⧸ C
  letI := Fintype.ofFinite Q
  let e := groupEquivSubgroupProdQuotient G C
  let pairEquiv : G × G ≃ (Q × Q) × (C × C) :=
    (e.prodCongr e).trans (pairPairReorder C Q)
  have hdecompose :
      (𝔼 x : G, 𝔼 y : G, bfcCoreCharacterValue G hcentral chi x y) =
        𝔼 qr : Q × Q, 𝔼 de : C × C,
          bfcCoreCharacterValue G hcentral chi
            (de.1.1 * Quotient.out qr.1) (de.2.1 * Quotient.out qr.2) := by
    calc
      (𝔼 x : G, 𝔼 y : G, bfcCoreCharacterValue G hcentral chi x y) =
          𝔼 p : G × G, bfcCoreCharacterValue G hcentral chi p.1 p.2 := by
        rw [← Finset.expect_product']
        simp only [Finset.univ_product_univ]
      _ = 𝔼 z : (Q × Q) × (C × C),
          bfcCoreCharacterValue G hcentral chi
            (z.2.1.1 * Quotient.out z.1.1)
            (z.2.2.1 * Quotient.out z.1.2) := by
        symm
        apply Fintype.expect_equiv pairEquiv.symm
        intro z
        rfl
      _ = _ := by
        rw [← Finset.univ_product_univ, Finset.expect_product]
  rw [hdecompose]
  calc
    ‖𝔼 qr : Q × Q, 𝔼 de : C × C,
        bfcCoreCharacterValue G hcentral chi
          (de.1.1 * Quotient.out qr.1) (de.2.1 * Quotient.out qr.2)‖ ≤
        𝔼 qr : Q × Q, ‖𝔼 de : C × C,
          bfcCoreCharacterValue G hcentral chi
            (de.1.1 * Quotient.out qr.1) (de.2.1 * Quotient.out qr.2)‖ :=
      RCLike.norm_expect_le (K := ℂ)
    _ ≤ 1 / ((commutatorCharMap C hcentral (unitCharToComplex chi)).ker.index : ℝ) := by
      rw [Fintype.expect_eq_sum_div_card]
      have hcardQ : (0 : ℝ) < Fintype.card (Q × Q) := by positivity
      apply (div_le_iff₀ hcardQ).2
      calc
        ∑ qr : Q × Q, ‖𝔼 de : C × C,
            bfcCoreCharacterValue G hcentral chi
              (de.1.1 * Quotient.out qr.1) (de.2.1 * Quotient.out qr.2)‖ ≤
            ∑ _qr : Q × Q,
              (1 / ((commutatorCharMap C hcentral
                (unitCharToComplex chi)).ker.index : ℝ)) := by
          apply Finset.sum_le_sum
          intro qr _
          rw [← Finset.univ_product_univ, Finset.expect_product]
          exact norm_expect_bfcCoreCharacterValue_coset_le_inv_index
            G hcentral chi (Quotient.out qr.1) (Quotient.out qr.2)
        _ = _ := by
          simp
          ring

end

end Submission.Helpers
