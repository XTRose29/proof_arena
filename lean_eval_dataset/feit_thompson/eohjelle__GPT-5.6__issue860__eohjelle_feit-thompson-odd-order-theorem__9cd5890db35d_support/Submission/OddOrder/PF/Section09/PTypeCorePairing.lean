import Submission.OddOrder.PF.Section09.PTypeCoreSupport

/-!
# Peterfalvi Section 9: virtual-character pairings in the rigid branch

This module isolates the reusable pairing calculation in Peterfalvi (9.11.4)
and the integral Fourier facts used in (9.11.7)--(9.11.8).  The elementary
sesquilinear rewrites remain private; the narrow downstream interface is
`PTypeCorePairingInternal`.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section16
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.MathlibSupport
open PTypeCoreContextInternal
open PTypeCoreBoundsInternal
open PTypeCoreGammaInternal
open PTypeCoreSupportInternal
open scoped BigOperators Classical

universe u

namespace PTypeCorePairingInternal

local instance invertibleNatCardComplex
    {Q : Type u} [Group Q] [Fintype Q] :
    Invertible (Nat.card Q : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-! ## The source alpha and beta pairings -/

/-- Source `beta = lambda - scale * psi`. -/
def pTypeCoreBeta
    {M : Type u} [Group M]
    (lambda psi : ClassFunction M ℂ) (scale : ℕ) :
    ClassFunction M ℂ :=
  lambda - (scale : ℂ) • psi

private theorem pairing_neg_left
    {M : Type u} [Group M] [Fintype M]
    (phi psi : ClassFunction M ℂ) :
    characterPairing (-phi) psi = -characterPairing phi psi := by
  rw [← neg_one_smul ℂ phi, characterPairing_smul_left]
  ring

private theorem pairing_neg_right
    {M : Type u} [Group M] [Fintype M]
    (phi psi : ClassFunction M ℂ) :
    characterPairing phi (-psi) = -characterPairing phi psi := by
  rw [← neg_one_smul ℂ psi, characterPairing_smul_right]
  ring

private theorem pairing_sub_left
    {M : Type u} [Group M] [Fintype M]
    (phi psi eta : ClassFunction M ℂ) :
    characterPairing (phi - psi) eta =
      characterPairing phi eta - characterPairing psi eta := by
  rw [sub_eq_add_neg, characterPairing_add_left, pairing_neg_left,
    sub_eq_add_neg]

private theorem pairing_sub_right
    {M : Type u} [Group M] [Fintype M]
    (phi psi eta : ClassFunction M ℂ) :
    characterPairing phi (psi - eta) =
      characterPairing phi psi - characterPairing phi eta := by
  rw [sub_eq_add_neg, characterPairing_add_right, pairing_neg_right,
    sub_eq_add_neg]

/-- Subtracting an orthogonal norm-one character raises the norm by one. -/
theorem pTypeCore_alpha_pairing
    {M : Type u} [Group M] [Fintype M]
    (gamma psi : ClassFunction M ℂ)
    (hgammaPsi : characterPairing gamma psi = 0)
    (hpsiNorm : characterPairing psi psi = 1) :
    characterPairing (pTypeCoreAlpha gamma psi)
        (pTypeCoreAlpha gamma psi) =
      characterPairing gamma gamma + 1 := by
  rw [pTypeCoreAlpha, pairing_sub_left, pairing_sub_right,
    pairing_sub_right, hgammaPsi, characterPairing_comm psi gamma,
    hgammaPsi, hpsiNorm]
  ring

/-- The complete norm identity in Peterfalvi (9.11.4).  This is specialized
to universe zero because the support theorem supplying the orthogonality is
currently available at that boundary. -/
theorem PTypeCoreRigidFacts.alpha_pairing
    {G : Type} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    {ctx : PTypeFCoreContext M U W W₁ W₂}
    {facts : PTypeFCoreFactorFacts ctx}
    {not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)}
    {S₂ : Finset (ClassFunction M ℂ)}
    (rigid : PTypeCoreRigidFacts ctx facts not_Galois S₂)
    {psi : ClassFunction M ℂ} (hpsi : psi ∈ S₂) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    let a := pTypeNonGaloisIndex hD not_Galois
    let u₀ := pTypeActionFactorCard D
    characterPairing
        (pTypeCoreAlpha (pTypeCoreGamma ctx facts not_Galois) psi)
        (pTypeCoreAlpha (pTypeCoreGamma ctx facts not_Galois) psi) =
      (a : ℂ) + ((((D.q - 1) * a ^ 2 : ℕ) : ℂ) / (u₀ : ℂ)) + 1 := by
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let a := pTypeNonGaloisIndex hD not_Galois
  let u₀ := pTypeActionFactorCard D
  let gamma := pTypeCoreGamma ctx facts not_Galois
  let psiIrr : IrreducibleCharacter M ℂ :=
    ⟨psi, rigid.slice_irreducible psi hpsi⟩
  have horth : characterPairing gamma psi = 0 :=
    Submission.OddOrder.PF.PTypeCoreSupportInternal.PTypeCoreRigidFacts.gamma_pairing_slice_eq_zero
      rigid hpsi
  have hpsiNorm : characterPairing psi psi = 1 := by
    change characterPairing
        (psiIrr : ClassFunction M ℂ)
        (psiIrr : ClassFunction M ℂ) = 1
    exact IrreducibleCharacter.characterPairing_self psiIrr
  rw [pTypeCore_alpha_pairing gamma psi horth hpsiNorm,
    pTypeCoreGamma_pairing rigid]

/-- `beta` vanishes at the identity when its two source degrees match. -/
theorem pTypeCoreBeta_one_eq_zero
    {M : Type u} [Group M]
    (lambda psi : ClassFunction M ℂ) (scale : ℕ)
    (hdegree : lambda 1 = (scale : ℂ) * psi 1) :
    pTypeCoreBeta lambda psi scale 1 = 0 := by
  change lambda 1 - (scale : ℂ) * psi 1 = 0
  rw [hdegree, sub_self]

/-- The abstract scalar identity underlying
`<alpha^tau, beta^tau> = scale`. -/
theorem pTypeCore_alpha_beta_pairing
    {M : Type u} [Group M] [Fintype M]
    (gamma psi lambda : ClassFunction M ℂ) (scale : ℕ)
    (hgammaLambda : characterPairing gamma lambda = 0)
    (hgammaPsi : characterPairing gamma psi = 0)
    (hpsiLambda : characterPairing psi lambda = 0)
    (hpsiNorm : characterPairing psi psi = 1) :
    characterPairing (pTypeCoreAlpha gamma psi)
        (pTypeCoreBeta lambda psi scale) = (scale : ℂ) := by
  rw [pTypeCoreAlpha, pTypeCoreBeta, pairing_sub_left,
    pairing_sub_right, pairing_sub_right, characterPairing_smul_right,
    characterPairing_smul_right, hgammaLambda, hgammaPsi, hpsiLambda,
    hpsiNorm]
  ring

/-! ## Integral virtual-character pairings -/

/-- Every pairing of virtual characters is an integer. -/
theorem pTypeCore_virtual_pairing_isInt
    {Q : Type u} [Group Q] [Fintype Q]
    {phi psi : ClassFunction Q ℂ}
    (hphi : ClassFunction.IsVirtual phi)
    (hpsi : ClassFunction.IsVirtual psi) :
    ∃ z : ℤ, characterPairing phi psi = (z : ℂ) := by
  obtain ⟨v, rfl⟩ := hphi
  obtain ⟨w, rfl⟩ := hpsi
  exact ⟨coeffDot v w, VirtualCharacter.characterPairing_realize v w⟩

/-- A virtual character with zero squared norm is zero. -/
theorem pTypeCore_virtual_eq_zero_of_pairing_self_eq_zero
    {Q : Type u} [Group Q] [Fintype Q]
    {phi : ClassFunction Q ℂ}
    (hphi : ClassFunction.IsVirtual phi)
    (hnorm : characterPairing phi phi = 0) :
    phi = 0 := by
  obtain ⟨v, rfl⟩ := hphi
  have hv : normSq v = 0 := by
    apply Int.cast_injective (α := ℂ)
    simpa only [Int.cast_zero] using
      (VirtualCharacter.characterPairing_realize_self v).symm.trans hnorm
  rw [(normSq_eq_zero_iff v).mp hv]
  simp

/-- On virtual characters, the star pairing used by the Dade isometry is
the ordinary character pairing. -/
private theorem representation_character_inv_eq_star
    {Q : Type u} {V : Type*} [Group Q] [Fintype Q]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ Q V) (x : Q) :
    rho.character x⁻¹ = star (rho.character x) := by
  let n := Nat.card Q
  have hn : n ≠ 0 := Nat.card_pos.ne'
  letI : NeZero n := ⟨hn⟩
  let omega₀ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have homega₀ : IsPrimitiveRoot omega₀ n := by
    simpa only [omega₀] using Complex.isPrimitiveRoot_exp n hn
  let omega : ℂˣ := Units.mk0 omega₀ (homega₀.ne_zero hn)
  have homega : IsPrimitiveRoot omega n := by
    apply IsPrimitiveRoot.coe_units_iff.mp
    simpa [omega] using homega₀
  have homegaNorm : ‖(omega : ℂ)‖ = 1 := by
    simpa [omega] using homega₀.norm'_eq_one hn
  have homegaPow : (omega : ℂ) ^ n = 1 :=
    congrArg (fun z : ℂˣ ↦ (z : ℂ)) homega.pow_eq_one
  have hpow : (rho x) ^ n = 1 := by
    rw [← map_pow, pow_card_eq_one', map_one]
  have hxinvPow : x⁻¹ = x ^ (n - 1) :=
    inv_eq_of_mul_eq_one_right (by
      rw [mul_pow_sub_one hn, pow_card_eq_one'])
  have hinvPow : rho x⁻¹ = (rho x) ^ (n - 1) := by
    rw [hxinvPow, map_pow]
  have hweight (i : ZMod n) :
      (primitiveRootUnitWeight homega i : ℂ) =
        (omega : ℂ) ^ i.val := by
    conv_lhs =>
      rw [← ZMod.natCast_zmod_val i,
        primitiveRootUnitWeight_natCast]
    rfl
  have hweightStar (i : ZMod n) :
      (starRingEnd ℂ) (primitiveRootUnitWeight homega i : ℂ) =
        (primitiveRootUnitWeight homega i : ℂ) ^ (n - 1) := by
    let w : ℂ := primitiveRootUnitWeight homega i
    have hwNorm : ‖w‖ = 1 := by
      rw [show w = (omega : ℂ) ^ i.val by exact hweight i,
        norm_pow, homegaNorm, one_pow]
    have hwPow : w ^ n = 1 := by
      rw [show w = (omega : ℂ) ^ i.val by exact hweight i,
        ← pow_mul, Nat.mul_comm, pow_mul, homegaPow, one_pow]
    have hwInv : w⁻¹ = w ^ (n - 1) :=
      inv_eq_of_mul_eq_one_right (by rw [mul_pow_sub_one hn, hwPow])
    change (starRingEnd ℂ) w = w ^ (n - 1)
    rw [← Complex.inv_eq_conj hwNorm, hwInv]
  have htraceOne :=
    trace_pow_eq_sum_primitiveRootUnitWeight homega (rho x) hpow 1
  have htracePred :=
    trace_pow_eq_sum_primitiveRootUnitWeight homega (rho x) hpow (n - 1)
  simp only [pow_one] at htraceOne
  calc
    rho.character x⁻¹ = LinearMap.trace ℂ V (rho x⁻¹) := rfl
    _ = LinearMap.trace ℂ V ((rho x) ^ (n - 1)) := by rw [hinvPow]
    _ = ∑ i : ZMod n,
          (Module.finrank ℂ
              (Module.End.eigenspace (rho x)
                (primitiveRootUnitWeight homega i : ℂ)) : ℂ) *
            (primitiveRootUnitWeight homega i : ℂ) ^ (n - 1) :=
      htracePred
    _ = star (∑ i : ZMod n,
          (Module.finrank ℂ
              (Module.End.eigenspace (rho x)
                (primitiveRootUnitWeight homega i : ℂ)) : ℂ) *
            (primitiveRootUnitWeight homega i : ℂ)) := by
      change _ = (starRingEnd ℂ) (∑ i : ZMod n,
        (Module.finrank ℂ
            (Module.End.eigenspace (rho x)
              (primitiveRootUnitWeight homega i : ℂ)) : ℂ) *
          (primitiveRootUnitWeight homega i : ℂ))
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul, map_natCast, hweightStar]
    _ = star (LinearMap.trace ℂ V (rho x)) := by rw [htraceOne]
    _ = star (rho.character x) := rfl

private theorem irreducibleCharacter_apply_inv_eq_star
    {Q : Type u} [Group Q] [Fintype Q]
    (chi : IrreducibleCharacter Q ℂ) (x : Q) :
    chi x⁻¹ = star (chi x) := by
  rw [← chi.representation_character,
    ← chi.representation_character]
  exact representation_character_inv_eq_star chi.representation.ρ x

theorem pTypeCore_starPairing_eq_pairing_of_virtual
    {Q : Type u} [Group Q] [Fintype Q]
    {phi psi : ClassFunction Q ℂ}
    (hphi : ClassFunction.IsVirtual phi)
    (hpsi : ClassFunction.IsVirtual psi) :
    starCharacterPairing phi psi = characterPairing phi psi := by
  obtain ⟨v, rfl⟩ := hphi
  obtain ⟨w, rfl⟩ := hpsi
  apply starCharacterPairing_eq_characterPairing_of_star_apply_eq_inv
  intro x
  induction w using Finsupp.induction with
  | zero => simp
  | single_add chi z w hchi hz ih =>
      rw [VirtualCharacter.realize_add,
        VirtualCharacter.realize_single]
      change (starRingEnd ℂ) ((z : ℂ) * chi.val x +
          VirtualCharacter.realize w x) =
        (z : ℂ) * chi.val x⁻¹ +
          VirtualCharacter.realize w x⁻¹
      have hchiStar :=
        (irreducibleCharacter_apply_inv_eq_star chi x).symm
      change (starRingEnd ℂ) (chi.val x) = chi.val x⁻¹ at hchiStar
      have ih' := ih
      change (starRingEnd ℂ) (VirtualCharacter.realize w x) =
        VirtualCharacter.realize w x⁻¹ at ih'
      rw [map_add, map_mul, map_intCast, ih', hchiStar]

/-! ## Finite orthonormal families -/

/-- Fourier expansion of an element of the integral span of a finite
orthonormal family. -/
theorem pTypeCore_eq_sum_pairing_smul_of_mem_closure
    {Q : Type u} [Group Q] [Fintype Q]
    (T : Finset (ClassFunction Q ℂ))
    (horthonormal : ∀ alpha ∈ T, ∀ gamma ∈ T,
      characterPairing alpha gamma =
        if alpha = gamma then 1 else 0)
    {X : ClassFunction Q ℂ}
    (hX : X ∈ AddSubgroup.closure
      (↑T : Set (ClassFunction Q ℂ))) :
    X = ∑ alpha ∈ T, characterPairing X alpha • alpha := by
  classical
  induction hX using AddSubgroup.closure_induction with
  | mem alpha halpha =>
      rw [Finset.sum_eq_single alpha]
      · rw [horthonormal alpha halpha alpha halpha, if_pos rfl,
          one_smul]
      · intro gamma hgamma hne
        rw [horthonormal alpha halpha gamma hgamma, if_neg hne.symm,
          zero_smul]
      · exact fun h ↦ (h halpha).elim
  | zero => simp
  | add X Y hX hY ihX ihY =>
      simp only [characterPairing_add_left, add_smul,
        Finset.sum_add_distrib]
      rw [← ihX, ← ihY]
  | neg X hX ihX =>
      calc
        -X = -(∑ alpha ∈ T,
            characterPairing X alpha • alpha) := congrArg Neg.neg ihX
        _ = ∑ alpha ∈ T,
            characterPairing (-X) alpha • alpha := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro alpha _
          rw [pairing_neg_left]
          exact (neg_smul (characterPairing X alpha) alpha).symm

/-- The self-pairing of the sum of a finite orthonormal family is its
cardinality. -/
theorem pTypeCore_pairing_orthonormal_sum_self
    {Q : Type u} [Group Q] [Fintype Q]
    (T : Finset (ClassFunction Q ℂ))
    (horthonormal : ∀ alpha ∈ T, ∀ gamma ∈ T,
      characterPairing alpha gamma =
        if alpha = gamma then 1 else 0) :
    characterPairing (∑ alpha ∈ T, alpha)
        (∑ alpha ∈ T, alpha) = (T.card : ℂ) := by
  change characterPairingRight (∑ alpha ∈ T, alpha)
      (∑ alpha ∈ T, alpha) = (T.card : ℂ)
  rw [map_sum]
  calc
    (∑ alpha ∈ T,
        characterPairing alpha (∑ gamma ∈ T, gamma)) =
        ∑ _alpha ∈ T, (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro alpha halpha
      change characterPairingLeft alpha (∑ gamma ∈ T, gamma) = 1
      rw [map_sum, Finset.sum_eq_single alpha]
      · change characterPairing alpha alpha = 1
        rw [horthonormal alpha halpha alpha halpha, if_pos rfl]
      · intro gamma hgamma hne
        change characterPairing alpha gamma = 0
        rw [horthonormal alpha halpha gamma hgamma, if_neg hne.symm]
      · exact fun h ↦ (h halpha).elim
    _ = (T.card : ℂ) := by simp

/-- Bessel's bound for a finite orthonormal family of virtual characters.
If a virtual character has nonzero coefficient at every family member, the
family cardinal is at most its squared norm. -/
theorem pTypeCore_orthonormal_card_le_norm
    {Q : Type u} [Group Q] [Fintype Q]
    (T : Finset (ClassFunction Q ℂ))
    (hvirtual : ∀ alpha ∈ T, ClassFunction.IsVirtual alpha)
    (horthonormal : ∀ alpha ∈ T, ∀ gamma ∈ T,
      characterPairing alpha gamma =
        if alpha = gamma then 1 else 0)
    {beta : ClassFunction Q ℂ}
    (hbeta : ClassFunction.IsVirtual beta)
    (hnonzero : ∀ alpha ∈ T,
      characterPairing beta alpha ≠ 0) :
    (T.card : ℝ) ≤ (characterPairing beta beta).re := by
  classical
  obtain ⟨b, hb⟩ := hbeta
  let z : ClassFunction Q ℂ → VirtualCharacter Q ℂ := fun alpha ↦
    if halpha : alpha ∈ T then Classical.choose (hvirtual alpha halpha)
    else 0
  have hz (alpha : ClassFunction Q ℂ) (halpha : alpha ∈ T) :
      VirtualCharacter.realize (z alpha) = alpha := by
    simp only [z, dif_pos halpha]
    exact Classical.choose_spec (hvirtual alpha halpha)
  have hnorm (alpha : ClassFunction Q ℂ) (halpha : alpha ∈ T) :
      normSq (z alpha) = 1 := by
    apply Int.cast_injective (α := ℂ)
    rw [← VirtualCharacter.characterPairing_realize_self, hz alpha halpha,
      horthonormal alpha halpha alpha halpha, if_pos rfl]
    norm_num
  let A := {alpha : ClassFunction Q ℂ // alpha ∈ T}
  let index : A → IrreducibleCharacter Q ℂ := fun alpha ↦
    Classical.choose
      (eq_signed_single_of_normSq_eq_one (z alpha.1)
        (hnorm alpha.1 alpha.2))
  let sign : A → ℤ := fun alpha ↦
    Classical.choose (Classical.choose_spec
      (eq_signed_single_of_normSq_eq_one (z alpha.1)
        (hnorm alpha.1 alpha.2)))
  have hsign (alpha : A) : IsSign (sign alpha) :=
    (Classical.choose_spec (Classical.choose_spec
      (eq_signed_single_of_normSq_eq_one (z alpha.1)
        (hnorm alpha.1 alpha.2)))).1
  have hzSigned (alpha : A) :
      z alpha.1 = Finsupp.single (index alpha) (sign alpha) :=
    (Classical.choose_spec (Classical.choose_spec
      (eq_signed_single_of_normSq_eq_one (z alpha.1)
        (hnorm alpha.1 alpha.2)))).2
  have hindexInjective : Function.Injective index := by
    intro alpha gamma hindex
    apply Subtype.ext
    by_contra hne
    have hpair := horthonormal alpha.1 alpha.2 gamma.1 gamma.2
    rw [if_neg hne] at hpair
    have hpairCast : ((sign alpha * sign gamma : ℤ) : ℂ) = 0 := by
      calc
        ((sign alpha * sign gamma : ℤ) : ℂ) =
            characterPairing
              (VirtualCharacter.realize (z alpha.1))
              (VirtualCharacter.realize (z gamma.1)) := by
          rw [VirtualCharacter.characterPairing_realize,
            hzSigned alpha, hzSigned gamma, hindex]
          simp
        _ = characterPairing alpha.1 gamma.1 := by
          rw [hz alpha.1 alpha.2, hz gamma.1 gamma.2]
        _ = 0 := hpair
    have hprod : sign alpha * sign gamma = 0 := by
      have hpairCast' :
          ((sign alpha * sign gamma : ℤ) : ℂ) = ((0 : ℤ) : ℂ) := by
        simpa only [Int.cast_zero] using hpairCast
      exact Int.cast_injective hpairCast'
    exact (mul_ne_zero (isSign_ne_zero (hsign alpha))
      (isSign_ne_zero (hsign gamma))) hprod
  have hindexSupport (alpha : A) : index alpha ∈ b.support := by
    rw [Finsupp.mem_support_iff]
    intro hzero
    apply hnonzero alpha.1 alpha.2
    rw [← hb, ← hz alpha.1 alpha.2,
      VirtualCharacter.characterPairing_realize, hzSigned alpha]
    simp [hzero]
  have hcardLe : T.card ≤ b.support.card := by
    have hEsub : T.attach.image index ⊆ b.support := by
      intro chi hchi
      obtain ⟨alpha, _, rfl⟩ := Finset.mem_image.mp hchi
      exact hindexSupport alpha
    calc
      T.card = T.attach.card := Finset.card_attach.symm
      _ = (T.attach.image index).card :=
        (Finset.card_image_iff.mpr hindexInjective.injOn).symm
      _ ≤ b.support.card := Finset.card_le_card hEsub
  have hsupportNorm : (b.support.card : ℤ) ≤ normSq b := by
    rw [normSq_eq_sum]
    calc
      (b.support.card : ℤ) = ∑ _chi ∈ b.support, (1 : ℤ) := by simp
      _ ≤ ∑ chi ∈ b.support, b chi ^ 2 := by
        apply Finset.sum_le_sum
        intro chi hchi
        have hchi0 : b chi ≠ 0 := by simpa using hchi
        have hcases : b chi ≤ -1 ∨ 1 ≤ b chi := by omega
        rcases hcases with hneg | hpos
        · nlinarith [sq_nonneg (b chi + 1)]
        · nlinarith [sq_nonneg (b chi - 1)]
  have hcardLeInt : (T.card : ℤ) ≤ (b.support.card : ℤ) := by
    exact_mod_cast hcardLe
  have hcardNorm : (T.card : ℤ) ≤ normSq b :=
    hcardLeInt.trans hsupportNorm
  have hnormReal : (characterPairing beta beta).re = (normSq b : ℝ) := by
    rw [← hb, VirtualCharacter.characterPairing_realize_self]
    norm_num
  rw [hnormReal]
  exact_mod_cast hcardNorm

end PTypeCorePairingInternal

end

end Submission.OddOrder.PF
