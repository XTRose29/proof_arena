import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Submission.OddOrder.MathlibSupport.RepresentationDeterminant
import Submission.OddOrder.PF.Section01.PiCharacterAutomorphism
import Submission.OddOrder.PF.Section03.CyclicCharacterFacts
import Submission.OddOrder.PF.Section03.DirectProductCharacters

/-!
# Cyclotomic power automorphisms of the complex numbers

The complex numbers are not algebraic over `ℚ`, so the algebraic-closure
version of Peterfalvi's cyclotomic automorphism cannot be applied to `ℂ`
directly.  We first construct the automorphism on the relative algebraic
closure of `ℚ` in `ℂ`.  An automorphism of that field extends over a purely
transcendental extension by acting on coefficients and fixing a
transcendence basis; uniqueness of algebraic closures then extends it to all
of `ℂ`.
-/

namespace Submission.OddOrder.MathlibSupport

noncomputable section

open scoped Classical

/-- Every `ℚ`-automorphism of the relative algebraic closure of `ℚ` in `ℂ`
extends to a `ℚ`-automorphism of `ℂ`.

This is the field-theoretic step needed to use algebraic cyclotomic Galois
automorphisms with ordinary complex-valued characters. -/
theorem exists_complex_algEquiv_extending_algebraicClosure
    (sigma : algebraicClosure ℚ ℂ ≃ₐ[ℚ] algebraicClosure ℚ ℂ) :
    ∃ tau : ℂ ≃ₐ[ℚ] ℂ,
      ∀ x : algebraicClosure ℚ ℂ, tau x.1 = (sigma x).1 := by
  let A := algebraicClosure ℚ ℂ
  obtain ⟨T, hT⟩ := exists_isTranscendenceBasis A ℂ
  let F : IntermediateField A ℂ :=
    IntermediateField.adjoin A (Set.range ((↑) : T → ℂ))
  have hcoeAF (x : A) :
      algebraMap F ℂ (algebraMap A F x) = x.1 := rfl
  let pAut : MvPolynomial T A ≃+* MvPolynomial T A :=
    MvPolynomial.mapEquiv T sigma.toRingEquiv
  let rAut : FractionRing (MvPolynomial T A) ≃+*
      FractionRing (MvPolynomial T A) :=
    IsFractionRing.ringEquivOfRingEquiv pAut
  let evalEquiv : FractionRing (MvPolynomial T A) ≃ₐ[A] F :=
    hT.1.aevalEquivField
  let fAut : F ≃+* F :=
    evalEquiv.toRingEquiv.symm.trans
      (rAut.trans evalEquiv.toRingEquiv)
  have hfAut (x : A) : fAut (algebraMap A F x) = algebraMap A F (sigma x) := by
    dsimp only [fAut, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv,
      RingEquiv.symm_apply_apply]
    have heval :
        evalEquiv.toRingEquiv.symm (algebraMap A F x) =
          algebraMap (MvPolynomial T A)
            (FractionRing (MvPolynomial T A)) (MvPolynomial.C x) := by
      apply evalEquiv.toRingEquiv.symm_apply_eq.mpr
      symm
      apply Subtype.ext
      change
        ↑(hT.1.aevalEquivField
          (algebraMap (MvPolynomial T A)
            (FractionRing (MvPolynomial T A)) (MvPolynomial.C x))) =
          algebraMap A ℂ x
      simpa only [MvPolynomial.aeval_C] using
        hT.1.aevalEquivField_algebraMap_apply_coe (MvPolynomial.C x)
    rw [heval, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    simp only [pAut, MvPolynomial.mapEquiv_apply, MvPolynomial.map_C]
    apply Subtype.ext
    change
      ↑(hT.1.aevalEquivField
        (algebraMap (MvPolynomial T A)
          (FractionRing (MvPolynomial T A)) (MvPolynomial.C (sigma x)))) =
        algebraMap A ℂ (sigma x)
    simpa only [MvPolynomial.aeval_C] using
      hT.1.aevalEquivField_algebraMap_apply_coe
        (MvPolynomial.C (sigma x))
  letI : Module.IsTorsionFree F ℂ :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (algebraMap F ℂ).injective
  letI : IsAlgClosure F ℂ :=
    { isAlgClosed := inferInstance
      isAlgebraic := by simpa only [F] using hT.isAlgebraic_field }
  let tauRing : ℂ ≃+* ℂ :=
    IsAlgClosure.equivOfEquiv ℂ ℂ fAut
  let tau : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := tauRing) (by
    intro q
    have hbase := IsAlgClosure.equivOfEquiv_algebraMap
      ℂ ℂ fAut (algebraMap A F (algebraMap ℚ A q))
    rw [hfAut, sigma.commutes] at hbase
    change tauRing (algebraMap F ℂ (algebraMap A F (algebraMap ℚ A q))) =
      algebraMap F ℂ (algebraMap A F (algebraMap ℚ A q)) at hbase
    rw [hcoeAF] at hbase
    change tauRing (algebraMap ℚ ℂ q) = algebraMap ℚ ℂ q
    exact hbase)
  refine ⟨tau, ?_⟩
  intro x
  have hbase := IsAlgClosure.equivOfEquiv_algebraMap
    ℂ ℂ fAut (algebraMap A F x)
  change tauRing x.1 = (sigma x).1
  rw [hfAut] at hbase
  change tauRing (algebraMap F ℂ (algebraMap A F x)) =
    algebraMap F ℂ (algebraMap A F (sigma x)) at hbase
  simpa only [hcoeAF] using hbase

end

end Submission.OddOrder.MathlibSupport

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical

open Submission.OddOrder.MathlibSupport

universe u v w

/-- Peterfalvi's cyclotomic power automorphism for ordinary complex-valued
virtual characters.

Unlike `make_pi_cfAut`, this theorem does not incorrectly require `ℂ` to be
algebraic over `ℚ`.  The prescribed automorphism is first constructed on the
relative algebraic closure of `ℚ` in `ℂ`, and then extended to `ℂ` while
fixing a transcendence basis. -/
theorem make_pi_cfAut_complex
    (G : Type v) [Group G] [Fintype G]
    (a k : ℕ) (hka : k.Coprime a) :
    ∃ nu : ℂ ≃ₐ[ℚ] ℂ,
      (∀ {G₀ : Type w} [Group G₀] [Fintype G₀]
          (chi : VirtualCharacter G₀ ℂ) (x : G₀),
          orderOf x ∣ a →
          nu (VirtualCharacter.realize chi x) =
            VirtualCharacter.realize chi (x ^ k)) ∧
      ∀ (chi : VirtualCharacter G ℂ) (x : G),
        (orderOf x).Coprime a →
        nu (VirtualCharacter.realize chi x) =
          VirtualCharacter.realize chi x := by
  by_cases ha0 : a = 0
  · subst a
    have hk : k = 1 := by
      simpa only [Nat.coprime_zero_right] using hka
    refine ⟨AlgEquiv.refl, ?_, fun _ _ _ ↦ rfl⟩
    intro G₀ _ _ chi x _
    change VirtualCharacter.realize chi x =
      VirtualCharacter.realize chi (x ^ k)
    simp only [hk, pow_one]
  · letI : NeZero a := ⟨ha0⟩
    let A := algebraicClosure ℚ ℂ
    letI : Module.IsTorsionFree ℚ A :=
      Module.isTorsionFree_iff_algebraMap_injective.mpr
        (algebraMap ℚ A).injective
    letI : IsAlgClosure ℚ A := by
      dsimp only [A]
      exact algebraicClosure.isAlgClosure ℚ ℂ
    let b : ℕ := ∏ x : G,
      if (orderOf x).Coprime a then orderOf x else 1
    have hab : a.Coprime b := by
      change a.Coprime
        (∏ x : G, if (orderOf x).Coprime a then orderOf x else 1)
      rw [Nat.coprime_fintype_prod_right_iff]
      intro x
      by_cases hx : (orderOf x).Coprime a
      · rw [if_pos hx]
        exact hx.symm
      · rw [if_neg hx]
        exact Nat.coprime_one_right a
    have hbpos : 0 < b := by
      dsimp only [b]
      apply Finset.prod_pos
      intro x _
      by_cases hx : (orderOf x).Coprime a
      · rw [if_pos hx]
        exact orderOf_pos x
      · rw [if_neg hx]
        exact Nat.zero_lt_one
    letI : NeZero b := ⟨Nat.ne_of_gt hbpos⟩
    let c := Nat.chineseRemainder hab k 1
    have hca : (c : ℕ).Coprime a := by
      rw [Nat.coprime_iff_gcd_eq_one, c.property.1.gcd_eq]
      exact Nat.coprime_iff_gcd_eq_one.mp hka
    have hcb : (c : ℕ).Coprime b := by
      rw [Nat.coprime_iff_gcd_eq_one, c.property.2.gcd_eq]
      simp
    have hcab : (c : ℕ).Coprime (a * b) :=
      Nat.Coprime.mul_right hca hcb
    obtain ⟨sigmaA, hsigmaA⟩ :=
      exists_algEquiv_apply_eq_pow_of_coprime
        (K := A) (a * b) (c : ℕ) hcab
    have hsigmaA_a (z : A) (hz : z ^ a = 1) :
        sigmaA z = z ^ k := by
      calc
        sigmaA z = z ^ (c : ℕ) := hsigmaA z (by
          rw [pow_mul, hz, one_pow])
        _ = z ^ k := pow_eq_pow_of_modEq c.property.1 hz
    have hsigmaA_b (z : A) (hz : z ^ b = 1) :
        sigmaA z = z := by
      calc
        sigmaA z = z ^ (c : ℕ) := hsigmaA z (by
          rw [mul_comm, pow_mul, hz, one_pow])
        _ = z ^ 1 := pow_eq_pow_of_modEq c.property.2 hz
        _ = z := pow_one z
    obtain ⟨nu, hnu⟩ :=
      exists_complex_algEquiv_extending_algebraicClosure sigmaA
    have hnu_a (z : ℂ) (hz : z ^ a = 1) : nu z = z ^ k := by
      have hzIntegral : IsIntegral ℚ z :=
        IsIntegral.of_pow (Nat.pos_of_ne_zero ha0) (hz ▸ isIntegral_one)
      let zA : A := ⟨z, mem_algebraicClosure_iff'.2 hzIntegral⟩
      have hzA : zA ^ a = 1 := by
        apply Subtype.ext
        exact hz
      calc
        nu z = nu zA.1 := rfl
        _ = (sigmaA zA).1 := hnu zA
        _ = (zA ^ k).1 := congrArg Subtype.val (hsigmaA_a zA hzA)
        _ = z ^ k := rfl
    have hnu_b (z : ℂ) (hz : z ^ b = 1) : nu z = z := by
      have hzIntegral : IsIntegral ℚ z :=
        IsIntegral.of_pow (NeZero.pos b) (hz ▸ isIntegral_one)
      let zA : A := ⟨z, mem_algebraicClosure_iff'.2 hzIntegral⟩
      have hzA : zA ^ b = 1 := by
        apply Subtype.ext
        exact hz
      calc
        nu z = nu zA.1 := rfl
        _ = (sigmaA zA).1 := hnu zA
        _ = zA.1 := congrArg Subtype.val (hsigmaA_b zA hzA)
        _ = z := rfl
    obtain ⟨omegaAValue, homegaAValue⟩ :=
      HasEnoughRootsOfUnity.exists_primitiveRoot ℂ a
    let omegaA : ℂˣ :=
      Units.mk0 omegaAValue
        (homegaAValue.ne_zero (NeZero.ne a))
    have homegaA : IsPrimitiveRoot omegaA a := by
      apply IsPrimitiveRoot.coe_units_iff.mp
      simpa only [omegaA, Units.val_mk0] using homegaAValue
    have hnuOmegaA : nu (omegaA : ℂ) = (omegaA : ℂ) ^ k := by
      apply hnu_a
      simpa only [omegaA, Units.val_mk0] using homegaAValue.pow_eq_one
    obtain ⟨omegaBValue, homegaBValue⟩ :=
      HasEnoughRootsOfUnity.exists_primitiveRoot ℂ b
    let omegaB : ℂˣ :=
      Units.mk0 omegaBValue
        (homegaBValue.ne_zero (NeZero.ne b))
    have homegaB : IsPrimitiveRoot omegaB b := by
      apply IsPrimitiveRoot.coe_units_iff.mp
      simpa only [omegaB, Units.val_mk0] using homegaBValue
    have hnuOmegaB : nu (omegaB : ℂ) = (omegaB : ℂ) ^ 1 := by
      simpa only [pow_one] using hnu_b (omegaB : ℂ) (by
        simpa only [omegaB, Units.val_mk0] using homegaBValue.pow_eq_one)
    refine ⟨nu, ?_, ?_⟩
    · intro G₀ _ _ chi x hx
      exact algEquiv_virtualCharacter_apply_eq_pow
        homegaA nu k hnuOmegaA chi x hx
    · intro chi x hx
      have hxb : orderOf x ∣ b := by
        have hd := Finset.dvd_prod_of_mem
          (fun y : G ↦ if (orderOf y).Coprime a then orderOf y else 1)
          (Finset.mem_univ x)
        change orderOf x ∣
          ∏ y : G, if (orderOf y).Coprime a then orderOf y else 1
        simpa only [if_pos hx] using hd
      simpa only [pow_one] using
        algEquiv_virtualCharacter_apply_eq_pow
          homegaB nu 1 hnuOmegaB chi x hxb

/-- On a one-dimensional representation, the character value is its
determinant character. -/
private theorem irreducibleCharacter_apply_eq_representationDeterminant
    {Q : Type u} [Group Q] [Fintype Q]
    (chi : IrreducibleCharacter Q ℂ)
    (hdim : Module.finrank ℂ chi.representation = 1)
    (x : Q) :
    chi x =
      (Submission.OddOrder.MathlibSupport.representationDeterminant
        chi.representation.ρ x : ℂ) := by
  rw [← chi.representation_character]
  rw [FDRep.character]
  change LinearMap.trace ℂ chi.representation
      (chi.representation.ρ x) =
    (LinearEquiv.det
      (Submission.OddOrder.MathlibSupport.representationLinearEquiv
        chi.representation.ρ x) : ℂ)
  rw [LinearEquiv.coe_det,
    Submission.OddOrder.MathlibSupport.representationLinearEquiv_toLinearMap]
  letI : Nontrivial chi.representation :=
    Module.nontrivial_of_finrank_pos (hdim ▸ Nat.zero_lt_one)
  obtain ⟨v, hv⟩ := exists_ne (0 : chi.representation)
  let basis : Module.Basis Unit ℂ chi.representation :=
    FiniteDimensional.basisSingleton Unit hdim v hv
  rw [LinearMap.trace_eq_matrix_trace ℂ basis,
    ← LinearMap.det_toMatrix basis]
  simp only [Matrix.trace, Finset.univ_unique, Finset.sum_singleton,
    Matrix.det_unique, Matrix.diag_apply]

/-- Any two nonprincipal irreducible characters of a prime-order cyclic
group are conjugate by a `ℚ`-automorphism of `ℂ`.

This is the complex-valued form of the transitivity assertion used in
Peterfalvi's `cfExp_prime_transitive`. -/
theorem exists_prime_cyclic_irreducible_algEquiv
    {Q : Type u} [Group Q] [Fintype Q]
    (hq : (Nat.card Q).Prime) (hcyclic : IsCyclic Q)
    (source : IrreducibleCharacter Q ℂ)
    (hsource : source ≠ IrreducibleCharacter.trivial)
    (target : IrreducibleCharacter Q ℂ)
    (htarget : target ≠ IrreducibleCharacter.trivial) :
    ∃ nu : ℂ ≃ₐ[ℚ] ℂ,
      IrreducibleCharacter.mapRingEquiv nu.toRingEquiv source = target := by
  letI : IsCyclic Q := hcyclic
  letI : NeZero (Nat.card Q) := ⟨hq.ne_zero⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Q)
  let sourceDet : Q →* ℂˣ :=
    Submission.OddOrder.MathlibSupport.representationDeterminant
      source.representation.ρ
  let targetDet : Q →* ℂˣ :=
    Submission.OddOrder.MathlibSupport.representationDeterminant
      target.representation.ρ
  have hsourceDim : Module.finrank ℂ source.representation = 1 := by
    letI : CategoryTheory.Simple source.representation :=
      source.representation_simple
    letI : Representation.IsIrreducible source.representation.ρ :=
      Submission.OddOrder.MathlibSupport.representation_isIrreducible_of_simple_fdRep
        source.representation
    exact Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative
      source.representation.ρ
  have htargetDim : Module.finrank ℂ target.representation = 1 := by
    letI : CategoryTheory.Simple target.representation :=
      target.representation_simple
    letI : Representation.IsIrreducible target.representation.ρ :=
      Submission.OddOrder.MathlibSupport.representation_isIrreducible_of_simple_fdRep
        target.representation
    exact Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative
      target.representation.ρ
  have hsourceApply (x : Q) : source x = (sourceDet x : ℂ) :=
    irreducibleCharacter_apply_eq_representationDeterminant
      source hsourceDim x
  have htargetApply (x : Q) : target x = (targetDet x : ℂ) :=
    irreducibleCharacter_apply_eq_representationDeterminant
      target htargetDim x
  have hsourceGen : sourceDet g ≠ 1 := by
    intro hgen
    apply hsource
    apply IrreducibleCharacter.ext
    intro x
    obtain ⟨n, rfl⟩ := hg x
    rw [IrreducibleCharacter.trivial_apply, hsourceApply, map_zpow,
      hgen, one_zpow]
    rfl
  have htargetGen : targetDet g ≠ 1 := by
    intro hgen
    apply htarget
    apply IrreducibleCharacter.ext
    intro x
    obtain ⟨n, rfl⟩ := hg x
    rw [IrreducibleCharacter.trivial_apply, htargetApply, map_zpow,
      hgen, one_zpow]
    rfl
  have hgOrder : orderOf g = Nat.card Q :=
    orderOf_eq_card_of_forall_mem_zpowers hg
  have hsourceOrder : orderOf (sourceDet g) = Nat.card Q := by
    have hdiv : orderOf (sourceDet g) ∣ Nat.card Q := by
      rw [← hgOrder]
      exact orderOf_map_dvd sourceDet g
    rcases (Nat.dvd_prime hq).mp hdiv with hone | hcard
    · exact (hsourceGen (orderOf_eq_one_iff.mp hone)).elim
    · exact hcard
  have htargetOrder : orderOf (targetDet g) = Nat.card Q := by
    have hdiv : orderOf (targetDet g) ∣ Nat.card Q := by
      rw [← hgOrder]
      exact orderOf_map_dvd targetDet g
    rcases (Nat.dvd_prime hq).mp hdiv with hone | hcard
    · exact (htargetGen (orderOf_eq_one_iff.mp hone)).elim
    · exact hcard
  have hsourcePrimitiveUnits :
      IsPrimitiveRoot (sourceDet g) (Nat.card Q) := by
    simpa only [hsourceOrder] using IsPrimitiveRoot.orderOf (sourceDet g)
  have htargetPrimitiveUnits :
      IsPrimitiveRoot (targetDet g) (Nat.card Q) := by
    simpa only [htargetOrder] using IsPrimitiveRoot.orderOf (targetDet g)
  have hsourcePrimitive :
      IsPrimitiveRoot (source g) (Nat.card Q) := by
    rw [hsourceApply]
    exact IsPrimitiveRoot.coe_units_iff.mpr hsourcePrimitiveUnits
  have htargetPrimitive :
      IsPrimitiveRoot (target g) (Nat.card Q) := by
    rw [htargetApply]
    exact IsPrimitiveRoot.coe_units_iff.mpr htargetPrimitiveUnits
  obtain ⟨k, _hklt, hk, hpower⟩ :=
    hsourcePrimitive.isPrimitiveRoot_iff.mp htargetPrimitive
  have hdetPower : (sourceDet g) ^ k = targetDet g := by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, ← hsourceApply,
      ← htargetApply] using hpower
  have hdetPowerAll (x : Q) : (sourceDet x) ^ k = targetDet x := by
    have hx := hg x
    rw [mem_zpowers_iff_mem_range_orderOf] at hx
    obtain ⟨n, _hn, rfl⟩ := Finset.mem_image.mp hx
    rw [map_pow, map_pow, ← hdetPower, ← pow_mul, ← pow_mul,
      Nat.mul_comm]
  obtain ⟨nu, hnuPower, _hnuFixed⟩ :=
    make_pi_cfAut_complex Q (Nat.card Q) k hk
  refine ⟨nu, ?_⟩
  apply IrreducibleCharacter.ext
  intro x
  rw [IrreducibleCharacter.mapRingEquiv_apply]
  change nu (source x) = target x
  have hxOrder : orderOf x ∣ Nat.card Q := orderOf_dvd_natCard x
  have hnuSource := hnuPower
    (Finsupp.single source 1 : VirtualCharacter Q ℂ) x hxOrder
  have hnuSource' : nu (source x) = source (x ^ k) := by
    simpa only [VirtualCharacter.realize_single, Int.cast_one, one_smul]
      using hnuSource
  rw [hnuSource', hsourceApply, map_pow, hdetPowerAll, htargetApply]

end

end Submission.OddOrder.PF
