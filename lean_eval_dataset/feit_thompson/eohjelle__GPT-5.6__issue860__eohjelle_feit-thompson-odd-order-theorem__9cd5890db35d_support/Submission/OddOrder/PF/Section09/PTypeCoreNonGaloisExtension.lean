import Submission.OddOrder.PF.Section09.PTypeCoreBoolean
import Submission.OddOrder.PF.Section09.PTypeCoreNonGaloisDichotomy
import Submission.OddOrder.PF.Section09.PTypeCoreGaloisBranch

/-!
# Peterfalvi Section 9: the rigid non-Galois extension

This module joins the independent numerical and Boolean branches of
Peterfalvi (9.11).  In the rigid case, coherence of the remaining equal-degree
family supplies a second isometry.  Its image is compared with the image of
the current slice, and the Boolean calculation packages the result as the
common extension input from `PTypeCoreGaloisBranch`.

Only the resulting one-step progress theorem is exported.  The image,
orthogonality, and degree-slice adapters are local to this assembly.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open PTypeCoreContextInternal
open PTypeCoreBoundsInternal
open PTypeCoreActionKernelInternal
open PTypeCoreGammaInternal
open PTypeCoreSupportInternal
open PTypeCorePairingInternal
open PTypeCoreBooleanInternal
open PTypeCoreNonGaloisDichotomyInternal
open PTypeCoreGaloisBranchInternal
open scoped BigOperators Classical

namespace PTypeCoreNonGaloisExtensionInternal

set_option maxHeartbeats 4000000

local instance invertibleNatCardComplex
    {Q : Type} [Group Q] [Fintype Q] :
    Invertible (Nat.card Q : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

local instance subgroupCoeTCToAmbient
    {A : Type} [Group A] (S : Subgroup A) : CoeTC S A :=
  ⟨fun x ↦ x.1⟩

/-! ## Elementary pairing transport -/

private theorem pairing_neg_left
    {Q : Type} [Group Q] [Fintype Q]
    (phi psi : ClassFunction Q ℂ) :
    characterPairing (-phi) psi = -characterPairing phi psi := by
  rw [← neg_one_smul ℂ phi, characterPairing_smul_left]
  ring

private theorem pairing_neg_right
    {Q : Type} [Group Q] [Fintype Q]
    (phi psi : ClassFunction Q ℂ) :
    characterPairing phi (-psi) = -characterPairing phi psi := by
  rw [← neg_one_smul ℂ psi, characterPairing_smul_right]
  ring

private theorem pairing_sub_left
    {Q : Type} [Group Q] [Fintype Q]
    (phi psi eta : ClassFunction Q ℂ) :
    characterPairing (phi - psi) eta =
      characterPairing phi eta - characterPairing psi eta := by
  rw [sub_eq_add_neg, characterPairing_add_left, pairing_neg_left,
    sub_eq_add_neg]

private theorem pairing_sub_right
    {Q : Type} [Group Q] [Fintype Q]
    (phi psi eta : ClassFunction Q ℂ) :
    characterPairing phi (psi - eta) =
      characterPairing phi psi - characterPairing phi eta := by
  rw [sub_eq_add_neg, characterPairing_add_right, pairing_neg_right,
    sub_eq_add_neg]

private theorem pairing_zero_on_right_closure
    {Q : Type} [Group Q] [Fintype Q]
    (T : Finset (ClassFunction Q ℂ)) (phi : ClassFunction Q ℂ)
    (hgen : ∀ psi ∈ T, characterPairing phi psi = 0)
    {eta : ClassFunction Q ℂ}
    (heta : eta ∈ AddSubgroup.closure
      (↑T : Set (ClassFunction Q ℂ))) :
    characterPairing phi eta = 0 := by
  induction heta using AddSubgroup.closure_induction with
  | mem psi hpsi => exact hgen psi hpsi
  | zero => simp
  | add psi eta hpsi heta ihpsi iheta =>
      rw [characterPairing_add_right, ihpsi, iheta, add_zero]
  | neg psi hpsi ihpsi => rw [pairing_neg_right, ihpsi, neg_zero]

private theorem pairing_zero_on_left_closure
    {Q : Type} [Group Q] [Fintype Q]
    (T : Finset (ClassFunction Q ℂ)) (psi : ClassFunction Q ℂ)
    (hgen : ∀ phi ∈ T, characterPairing phi psi = 0)
    {eta : ClassFunction Q ℂ}
    (heta : eta ∈ AddSubgroup.closure
      (↑T : Set (ClassFunction Q ℂ))) :
    characterPairing eta psi = 0 := by
  induction heta using AddSubgroup.closure_induction with
  | mem phi hphi => exact hgen phi hphi
  | zero => simp
  | add phi eta hphi heta ihphi iheta =>
      rw [characterPairing_add_left, ihphi, iheta, add_zero]
  | neg phi hphi ihphi => rw [pairing_neg_left, ihphi, neg_zero]

/-- The support lemmas are naturally stated on `FTsupport`; the outer Dade
map is parameterized by the containing set `FTsupport0`. -/
private theorem supportedOn_FTsupport0_of_FTsupport
    {G : Type} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    {phi : ClassFunction M ℂ}
    (hphi : phi ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport M}) :
    phi ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport0 M} := by
  rw [ClassFunction.mem_supportedOn_iff] at hphi ⊢
  intro x hx
  apply hphi
  intro hxSupport
  exact hx (FTsupp_sub0 M hxSupport)

/-! ## Coherent images of finite orthonormal families -/

private theorem coherent_image_data
    {M Q : Type}
    [Group M] [Fintype M] [Group Q] [Fintype Q]
    (S : Finset (ClassFunction M ℂ))
    (tau nu : ClassFunction M ℂ →ₗ[ℂ] ClassFunction Q ℂ)
    (hcoh : coherent_with (↑S : Set (ClassFunction M ℂ))
      (nonidentitySet M) tau nu)
    (hsource : ∀ phi ∈ S, ∀ psi ∈ S,
      characterPairing phi psi = if phi = psi then 1 else 0) :
    let T := S.image nu
    (∀ phi ∈ T, ClassFunction.IsVirtual phi) ∧
      (∀ phi ∈ T, ∀ psi ∈ T,
        characterPairing phi psi = if phi = psi then 1 else 0) ∧
      T.card = S.card := by
  classical
  let T := S.image nu
  have hinj : Set.InjOn nu (↑S : Set (ClassFunction M ℂ)) := by
    intro phi hphi psi hpsi heq
    by_contra hne
    have hcross := hcoh.isometry phi
      (AddSubgroup.subset_closure hphi) psi
      (AddSubgroup.subset_closure hpsi)
    have hself := hcoh.isometry phi
      (AddSubgroup.subset_closure hphi) phi
      (AddSubgroup.subset_closure hphi)
    rw [heq, hsource phi hphi psi hpsi, if_neg hne] at hcross
    rw [heq, hsource phi hphi phi hphi, if_pos rfl] at hself
    exact zero_ne_one (hcross.symm.trans hself)
  have hvirtual : ∀ phi ∈ T, ClassFunction.IsVirtual phi := by
    intro phi hphi
    obtain ⟨psi, hpsi, rfl⟩ := Finset.mem_image.mp hphi
    exact hcoh.mapsToVirtual psi (AddSubgroup.subset_closure hpsi)
  have horth : ∀ phi ∈ T, ∀ psi ∈ T,
      characterPairing phi psi = if phi = psi then 1 else 0 := by
    intro phi hphi psi hpsi
    obtain ⟨alpha, halpha, rfl⟩ := Finset.mem_image.mp hphi
    obtain ⟨beta, hbeta, rfl⟩ := Finset.mem_image.mp hpsi
    rw [hcoh.isometry alpha (AddSubgroup.subset_closure halpha)
      beta (AddSubgroup.subset_closure hbeta),
      hsource alpha halpha beta hbeta]
    by_cases heq : alpha = beta
    · subst beta
      simp
    · rw [if_neg heq, if_neg]
      exact fun h ↦ heq (hinj halpha hbeta h)
  exact ⟨hvirtual, horth, Finset.card_image_iff.mpr hinj⟩

private theorem irreducible_subfamily_orthonormal
    {M Q : Type}
    [Group M] [Fintype M] [Group Q] [Fintype Q]
    {S₀ : Set (ClassFunction M ℂ)}
    {tau : ClassFunction M ℂ →ₗ[ℂ] ClassFunction Q ℂ}
    {R : ClassFunction M ℂ → Finset (ClassFunction Q ℂ)}
    (hsub : subcoherent S₀ tau R)
    (S : Finset (ClassFunction M ℂ))
    (hS : (↑S : Set (ClassFunction M ℂ)) ⊆ S₀)
    (hirr : ∀ phi ∈ S, IsIrreducibleCharacter M ℂ phi) :
    ∀ phi ∈ S, ∀ psi ∈ S,
      characterPairing phi psi = if phi = psi then 1 else 0 := by
  intro phi hphi psi hpsi
  by_cases heq : phi = psi
  · subst psi
    rw [if_pos rfl]
    let chi : IrreducibleCharacter M ℂ := ⟨phi, hirr phi hphi⟩
    exact IrreducibleCharacter.characterPairing_self chi
  · rw [if_neg heq]
    exact hsub.pairwise_orthogonal (hS hphi) (hS hpsi) heq

/-! ## Transporting `alpha` across the Dade isometry -/

private theorem alpha_target_facts
    {G : Type} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (S₂ : Finset (ClassFunction M ℂ))
    (rigid : PTypeCoreRigidFacts ctx facts not_Galois S₂)
    (tau₃ : ClassFunction M ℂ →ₗ[ℂ] ClassFunction (⊤ : Subgroup G) ℂ)
    (R : ClassFunction M ℂ → Finset (ClassFunction (⊤ : Subgroup G) ℂ))
    (hsub : subcoherent
      (↑(pTypeCoreFamilyOfContext ctx) : Set (ClassFunction M ℂ))
      (Dade (FT_Dade0_hyp M ctx.maxM)) R)
    (hcoh₃ : coherent_with
      (↑(pTypeCoreRemainder (pTypeCoreFamilyOfContext ctx) S₂) :
        Set (ClassFunction M ℂ))
      (nonidentitySet M) (Dade (FT_Dade0_hyp M ctx.maxM)) tau₃)
    {psi : ClassFunction M ℂ} (hpsi : psi ∈ S₂) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    let a := pTypeNonGaloisIndex hD not_Galois
    let u₀ := pTypeActionFactorCard D
    let S₃ := pTypeCoreRemainder (pTypeCoreFamilyOfContext ctx) S₂
    let alpha := pTypeCoreAlpha
      (pTypeCoreGamma ctx facts not_Galois) psi
    ClassFunction.IsVirtual (Dade (FT_Dade0_hyp M ctx.maxM) alpha) ∧
      (characterPairing
        (Dade (FT_Dade0_hyp M ctx.maxM) alpha)
        (Dade (FT_Dade0_hyp M ctx.maxM) alpha)).re =
          pTypeCoreAlphaNorm D.q u₀ a ∧
      ∀ lambda ∈ S₃,
        characterPairing
          (Dade (FT_Dade0_hyp M ctx.maxM) alpha) (tau₃ lambda) = 0 := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let a := pTypeNonGaloisIndex hD not_Galois
  let u₀ := pTypeActionFactorCard D
  let S₀ := pTypeCoreFamilyOfContext ctx
  let S₃ := pTypeCoreRemainder S₀ S₂
  let HU := pTypeCoreDerived M
  let H := pTypeCoreFitting M
  let H₀C := pTypeH0CInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let S₄ := pTypeCoreIrreducibleRemainder HU H H₀C S₃
  let gamma := pTypeCoreGamma ctx facts not_Galois
  let alpha := pTypeCoreAlpha gamma psi
  let tau : ClassFunction M ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup G) ℂ :=
    Dade (FT_Dade0_hyp M ctx.maxM)
  have hpsi₀ : psi ∈ S₀ := by
    have hslice : psi ∈ pTypeCoreDegreeSlice S₀ (D.q * a) := by
      rw [← rigid.current_eq_slice]
      exact hpsi
    exact (Finset.mem_filter.mp hslice).1
  have hpsiVirtual : ClassFunction.IsVirtual psi :=
    hsub.source_virtual psi hpsi₀
  have halphaVirtual : ClassFunction.IsVirtual alpha :=
    (pTypeCoreGamma_isVirtual ctx facts not_Galois).sub hpsiVirtual
  have halphaSupportSmall : alpha ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport M} := by
    simpa only [alpha, gamma] using
      pTypeCoreAlpha_supportedOn rigid hpsi
  have halphaSupport : alpha ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport0 M} :=
    supportedOn_FTsupport0_of_FTsupport halphaSupportSmall
  have halphaTauVirtual : ClassFunction.IsVirtual (tau alpha) := by
    obtain ⟨z, hz⟩ := halphaVirtual
    have hzSupport : VirtualCharacter.realize z ∈
        ClassFunction.supportedOn {x : M | (x : G) ∈ FTsupport0 M} := by
      rw [hz]
      exact halphaSupport
    obtain ⟨w, hw, _⟩ :=
      (Dade_Zisometry (FT_Dade0_hyp M ctx.maxM)).2 z hzSupport
    exact ⟨w, by simpa only [tau, hz] using hw.symm⟩
  have halphaNormSource :=
    PTypeCorePairingInternal.PTypeCoreRigidFacts.alpha_pairing rigid hpsi
  have halphaNormIso :
      characterPairing (tau alpha) (tau alpha) =
        characterPairing alpha alpha := by
    have hiso := Dade_isometry (FT_Dade0_hyp M ctx.maxM)
      alpha alpha halphaSupport halphaSupport
    rw [pTypeCore_starPairing_eq_pairing_of_virtual
          halphaTauVirtual halphaTauVirtual,
        pTypeCore_starPairing_eq_pairing_of_virtual
          halphaVirtual halphaVirtual] at hiso
    exact hiso
  have halphaNormReal :
      (characterPairing (tau alpha) (tau alpha)).re =
        pTypeCoreAlphaNorm D.q u₀ a := by
    rw [halphaNormIso, halphaNormSource, pTypeCoreAlphaNorm]
    simp only [Complex.add_re, Complex.div_natCast_re,
      Complex.natCast_re, Complex.one_re]
    ring
  have hlocalAlpha : ∀ lambda ∈ S₃,
      characterPairing alpha lambda = 0 := by
    intro lambda hlambda
    have hlambda₀ : lambda ∈ S₀ := (Finset.mem_filter.mp hlambda).1
    have hlambdaNot : lambda ∉ S₂ := (Finset.mem_filter.mp hlambda).2
    have hpsiLambda : characterPairing psi lambda = 0 :=
      hsub.pairwise_orthogonal hpsi₀ hlambda₀
        (fun heq ↦ hlambdaNot (heq ▸ hpsi))
    change characterPairing
      (pTypeCoreGamma ctx facts not_Galois - psi) lambda = 0
    rw [pairing_sub_left,
      pTypeCoreGamma_pairing_family_eq_zero
        ctx facts not_Galois hlambda₀,
      hpsiLambda, sub_zero]
  have hsource₄ : ∀ lambda ∈ S₄, ∀ nu ∈ S₄,
      characterPairing lambda nu = if lambda = nu then 1 else 0 := by
    intro lambda hlambda nu hnu
    have hlambda₃ := (Finset.mem_filter.mp hlambda).1
    have hnu₃ := (Finset.mem_filter.mp hnu).1
    have hlambdaIrr := (Finset.mem_filter.mp hlambda).2.2
    by_cases heq : lambda = nu
    · subst nu
      let chi : IrreducibleCharacter M ℂ := ⟨lambda, hlambdaIrr⟩
      rw [if_pos rfl]
      exact IrreducibleCharacter.characterPairing_self chi
    · rw [if_neg heq]
      exact hsub.pairwise_orthogonal
        (Finset.mem_filter.mp hlambda₃).1
        (Finset.mem_filter.mp hnu₃).1 heq
  have hS₄S₃ : (↑S₄ : Set (ClassFunction M ℂ)) ⊆
      (↑S₃ : Set (ClassFunction M ℂ)) := by
    intro lambda hlambda
    exact (Finset.mem_filter.mp hlambda).1
  have hcoh₄ := subset_coherent_with hS₄S₃ hcoh₃
  let T₄ := S₄.image tau₃
  have hT₄data := coherent_image_data S₄ tau tau₃ hcoh₄ hsource₄
  have hT₄virtual : ∀ x ∈ T₄, ClassFunction.IsVirtual x := by
    simpa only [T₄] using hT₄data.1
  have hT₄orth : ∀ x ∈ T₄, ∀ y ∈ T₄,
      characterPairing x y = if x = y then 1 else 0 := by
    simpa only [T₄] using hT₄data.2.1
  have hT₄card : T₄.card = S₄.card := by
    simpa only [T₄] using hT₄data.2.2
  have hlarge := pTypeCore_nonGalois_rigid_remainder_gt_alphaNorm
    ctx facts not_Galois S₂ rigid
  refine ⟨by simpa only [tau] using halphaTauVirtual,
    by simpa only [tau] using halphaNormReal, ?_⟩
  intro lambda hlambda
  by_contra hlambdaPair
  have hcoeffEq : ∀ nu ∈ S₄,
      characterPairing (tau alpha) (tau₃ nu) =
        characterPairing (tau alpha) (tau₃ lambda) := by
    intro nu hnu
    have hnu₃ : nu ∈ S₃ := (Finset.mem_filter.mp hnu).1
    have hlambda₀ : lambda ∈ S₀ :=
      (Finset.mem_filter.mp hlambda).1
    have hnu₀ : nu ∈ S₀ := (Finset.mem_filter.mp hnu₃).1
    have hdegree : lambda 1 = nu 1 :=
      (rigid.remainder_degree lambda hlambda).trans
        (rigid.remainder_degree nu hnu₃).symm
    have hdiffSpan : lambda - nu ∈
        AddSubgroup.closure (↑S₃ : Set (ClassFunction M ℂ)) :=
      (AddSubgroup.closure
        (↑S₃ : Set (ClassFunction M ℂ))).sub_mem
        (AddSubgroup.subset_closure hlambda)
        (AddSubgroup.subset_closure hnu₃)
    have hdiffOff : lambda - nu ∈
        ClassFunction.supportedOn (nonidentitySet M) := by
      rw [ClassFunction.mem_supportedOn_iff]
      intro x hx
      have hxOne : x = 1 := by
        simpa [nonidentitySet] using not_not.mp hx
      subst x
      change lambda 1 - nu 1 = 0
      rw [hdegree, sub_self]
    have hdiffSupport := supportedOn_FTsupport0_of_FTsupport
      (pTypeCore_family_difference_supportedOn
        ctx facts hlambda₀ hnu₀ hdegree)
    have hdiffVirtual : ClassFunction.IsVirtual (lambda - nu) :=
      (hsub.source_virtual lambda hlambda₀).sub
        (hsub.source_virtual nu hnu₀)
    have htauDiffVirtual : ClassFunction.IsVirtual (tau (lambda - nu)) :=
      hsub.tau_virtual (lambda - nu)
        ((AddSubgroup.closure
          (↑S₀ : Set (ClassFunction M ℂ))).sub_mem
          (AddSubgroup.subset_closure hlambda₀)
          (AddSubgroup.subset_closure hnu₀)) hdiffOff
    have hagree : tau₃ (lambda - nu) = tau (lambda - nu) :=
      hcoh₃.agrees (lambda - nu) hdiffSpan hdiffOff
    have hiso := Dade_isometry (FT_Dade0_hyp M ctx.maxM)
      alpha (lambda - nu) halphaSupport hdiffSupport
    rw [pTypeCore_starPairing_eq_pairing_of_virtual
          halphaTauVirtual htauDiffVirtual,
        pTypeCore_starPairing_eq_pairing_of_virtual
          halphaVirtual hdiffVirtual] at hiso
    have hzero : characterPairing (tau alpha)
        (tau₃ (lambda - nu)) = 0 := by
      rw [hagree, hiso, pairing_sub_right,
        hlocalAlpha lambda hlambda, hlocalAlpha nu hnu₃, sub_self]
    rw [map_sub, pairing_sub_right] at hzero
    exact (sub_eq_zero.mp hzero).symm
  have hnonzero : ∀ x ∈ T₄,
      characterPairing (tau alpha) x ≠ 0 := by
    intro x hx
    obtain ⟨nu, hnu, rfl⟩ := Finset.mem_image.mp hx
    rw [hcoeffEq nu hnu]
    exact hlambdaPair
  have hbound := pTypeCore_orthonormal_card_le_norm
    T₄ hT₄virtual hT₄orth halphaTauVirtual hnonzero
  rw [hT₄card, halphaNormReal] at hbound
  exact (not_lt_of_ge hbound) hlarge.1

/-! ## The rigid extension -/

private theorem rigid_extension
    {G : Type} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (S₂ : Finset (ClassFunction M ℂ))
    (tau₂ : ClassFunction M ℂ →ₗ[ℂ] ClassFunction (⊤ : Subgroup G) ℂ)
    (R : ClassFunction M ℂ → Finset (ClassFunction (⊤ : Subgroup G) ℂ))
    (hsub : subcoherent
      (↑(pTypeCoreFamilyOfContext ctx) : Set (ClassFunction M ℂ))
      (Dade (FT_Dade0_hyp M ctx.maxM)) R)
    (hS₂ : cfConjC_subset
      (↑S₂ : Set (ClassFunction M ℂ))
      (↑(pTypeCoreFamilyOfContext ctx) : Set (ClassFunction M ℂ)))
    (hcoh₂ : coherent_with
      (↑S₂ : Set (ClassFunction M ℂ))
      (nonidentitySet M) (Dade (FT_Dade0_hyp M ctx.maxM)) tau₂)
    (rigid : PTypeCoreRigidFacts ctx facts not_Galois S₂) :
    ∃ chi : ClassFunction M ℂ,
      chi ∈ pTypeCoreFamilyOfContext ctx ∧ chi ∉ S₂ ∧
        coherent
          ({chi, ClassFunction.inverseLinear chi} ∪
            (↑S₂ : Set (ClassFunction M ℂ)))
          (nonidentitySet M)
          (Dade (FT_Dade0_hyp M ctx.maxM)) := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let a := pTypeNonGaloisIndex hD not_Galois
  let u₀ := pTypeActionFactorCard D
  let scale := u₀ / a
  let S₀ := pTypeCoreFamilyOfContext ctx
  let S₃ := pTypeCoreRemainder S₀ S₂
  let HU := pTypeCoreDerived M
  let H := pTypeCoreFitting M
  let H₀C := pTypeH0CInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let S₄ := pTypeCoreIrreducibleRemainder HU H H₀C S₃
  let tau : ClassFunction M ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup G) ℂ :=
    Dade (FT_Dade0_hyp M ctx.maxM)
  let gamma := pTypeCoreGamma ctx facts not_Galois

  have hS₀closed : cfConjC_closed
      (↑S₀ : Set (ClassFunction M ℂ)) := by
    intro chi hchi
    exact hsub.inverse_mem chi hchi
  have hS₃ : cfConjC_subset
      (↑S₃ : Set (ClassFunction M ℂ))
      (↑S₀ : Set (ClassFunction M ℂ)) :=
    pTypeCore_remainder_cfConjC_subset S₀ S₂ hS₀closed hS₂.2
  have hsub₃ : subcoherent
      (↑S₃ : Set (ClassFunction M ℂ)) tau R :=
    subset_subcoherent hsub hS₃
  have hcoherent₃ : coherent
      (↑S₃ : Set (ClassFunction M ℂ))
      (nonidentitySet M) tau := by
    apply uniform_degree_coherence hsub₃
    intro chi hchi eta heta
    exact (rigid.remainder_degree chi hchi).trans
      (rigid.remainder_degree eta heta).symm
  obtain ⟨tau₃, hcoh₃⟩ := hcoherent₃
  obtain ⟨psi, hpsi₂⟩ :=
    PTypeCoreActionKernelInternal.PTypeCoreRigidFacts.exists_slice_character
      rigid

  have hlarge := pTypeCore_nonGalois_rigid_remainder_gt_alphaNorm
    ctx facts not_Galois S₂ rigid
  obtain ⟨lambda, hlambda₄⟩ := Finset.card_pos.mp hlarge.2
  have hlambda₃ : lambda ∈ S₃ := (Finset.mem_filter.mp hlambda₄).1
  have hlambda₀ : lambda ∈ S₀ := (Finset.mem_filter.mp hlambda₃).1
  have hlambdaNot : lambda ∉ S₂ := (Finset.mem_filter.mp hlambda₃).2
  have hlambdaSmall : lambda ∈ pTypeCoreFamily HU H H₀C :=
    (Finset.mem_filter.mp hlambda₄).2.1
  have hlambdaIrr : IsIrreducibleCharacter M ℂ lambda :=
    (Finset.mem_filter.mp hlambda₄).2.2
  have hpsi₀ : psi ∈ S₀ := hS₂.1 hpsi₂
  have hpsiIrr : IsIrreducibleCharacter M ℂ psi :=
    rigid.slice_irreducible psi hpsi₂

  have haDvdU : a ∣ u₀ :=
    pTypeCore_nonGalois_index_dvd_factorCard ctx facts not_Galois
  have hscale : 1 < scale := by
    simpa only [scale, u₀, a, D, hD] using
      PTypeCoreActionKernelInternal.PTypeCoreRigidFacts.one_lt_factorCard_div_index
        rigid
  have hcard₂ : S₂.card = 2 * scale := by
    rw [rigid.slice_card_two]
    simpa only [scale, u₀, a] using Nat.mul_div_assoc 2 haDvdU
  have hpsiDegree : psi 1 = ((D.q * a : ℕ) : ℂ) := by
    have hmem : psi ∈ pTypeCoreDegreeSlice S₀ (D.q * a) := by
      rw [← rigid.current_eq_slice]
      exact hpsi₂
    exact (Finset.mem_filter.mp hmem).2
  have hlambdaDegree : lambda 1 = ((D.q * u₀ : ℕ) : ℂ) :=
    rigid.remainder_degree lambda hlambda₃
  have hdegreeBalance : lambda 1 = (scale : ℂ) * psi 1 := by
    rw [hlambdaDegree, hpsiDegree]
    have hcancel : scale * a = u₀ := Nat.div_mul_cancel haDvdU
    have hcancelC : (scale : ℂ) * (a : ℂ) = (u₀ : ℂ) := by
      exact_mod_cast hcancel
    norm_num only [Nat.cast_mul]
    rw [← hcancelC]
    ring

  have hsource₁ : ∀ phi ∈ S₂, ∀ eta ∈ S₂,
      characterPairing phi eta = if phi = eta then 1 else 0 :=
    irreducible_subfamily_orthonormal
      hsub S₂ hS₂.1 rigid.slice_irreducible
  have hS₄S₀ : (↑S₄ : Set (ClassFunction M ℂ)) ⊆
      (↑S₀ : Set (ClassFunction M ℂ)) := by
    intro chi hchi
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hchi).1).1
  have hsource₄ : ∀ phi ∈ S₄, ∀ eta ∈ S₄,
      characterPairing phi eta = if phi = eta then 1 else 0 := by
    apply irreducible_subfamily_orthonormal hsub S₄ hS₄S₀
    intro chi hchi
    exact (Finset.mem_filter.mp hchi).2.2
  have hS₄S₃ : (↑S₄ : Set (ClassFunction M ℂ)) ⊆
      (↑S₃ : Set (ClassFunction M ℂ)) := by
    intro chi hchi
    exact (Finset.mem_filter.mp hchi).1
  have hcoh₄ := subset_coherent_with hS₄S₃ hcoh₃

  let T₁ := S₂.image tau₂
  let T₄ := S₄.image tau₃
  have hT₁data := coherent_image_data S₂ tau tau₂ hcoh₂ hsource₁
  have hT₄data := coherent_image_data S₄ tau tau₃ hcoh₄ hsource₄
  have hT₁virtual : ∀ phi ∈ T₁, ClassFunction.IsVirtual phi := by
    simpa only [T₁] using hT₁data.1
  have hT₁orth : ∀ phi ∈ T₁, ∀ eta ∈ T₁,
      characterPairing phi eta = if phi = eta then 1 else 0 := by
    simpa only [T₁] using hT₁data.2.1
  have hT₄virtual : ∀ phi ∈ T₄, ClassFunction.IsVirtual phi := by
    simpa only [T₄] using hT₄data.1
  have hT₄orth : ∀ phi ∈ T₄, ∀ eta ∈ T₄,
      characterPairing phi eta = if phi = eta then 1 else 0 := by
    simpa only [T₄] using hT₄data.2.1
  have hT₁card : T₁.card = 2 * scale := by
    calc
      T₁.card = S₂.card := by simpa only [T₁] using hT₁data.2.2
      _ = 2 * scale := hcard₂
  have hphiT₁ : tau₂ psi ∈ T₁ :=
    Finset.mem_image.mpr ⟨psi, hpsi₂, rfl⟩
  have hdisjoint : (↑S₃ : Set (ClassFunction M ℂ)) ⊆
      (↑S₂ : Set (ClassFunction M ℂ))ᶜ := by
    intro chi hchi
    exact (Finset.mem_filter.mp hchi).2
  have hcrossSpan := coherent_ortho hsub hS₂ hcoh₂ hS₃ hcoh₃ hdisjoint
  have hcross : ∀ phi ∈ T₄, ∀ eta ∈ T₁,
      characterPairing phi eta = 0 := by
    intro phi hphi eta heta
    obtain ⟨chi, hchi₄, rfl⟩ := Finset.mem_image.mp hphi
    obtain ⟨zeta, hzeta₂, rfl⟩ := Finset.mem_image.mp heta
    rw [characterPairing_comm]
    exact hcrossSpan (tau₂ zeta)
      ⟨zeta, AddSubgroup.subset_closure hzeta₂, rfl⟩
      (tau₃ chi)
      ⟨chi, AddSubgroup.subset_closure
        ((Finset.mem_filter.mp hchi₄).1), rfl⟩

  let beta := pTypeCoreBeta lambda psi scale
  have hbetaSpan : beta ∈
      AddSubgroup.closure (↑S₀ : Set (ClassFunction M ℂ)) := by
    apply (AddSubgroup.closure (↑S₀ : Set (ClassFunction M ℂ))).sub_mem
    · exact AddSubgroup.subset_closure hlambda₀
    · simpa only [Nat.cast_smul_eq_nsmul] using
        (AddSubgroup.closure (↑S₀ : Set (ClassFunction M ℂ))).nsmul_mem
          (AddSubgroup.subset_closure hpsi₀) scale
  have hbetaOff : beta ∈
      ClassFunction.supportedOn (nonidentitySet M) := by
    rw [ClassFunction.mem_supportedOn_iff]
    intro x hx
    have hxOne : x = 1 := by simpa [nonidentitySet] using not_not.mp hx
    subst x
    exact pTypeCoreBeta_one_eq_zero lambda psi scale hdegreeBalance
  have hbetaVirtual : ClassFunction.IsVirtual beta :=
    (hsub.source_virtual lambda hlambda₀).sub
      ((hsub.source_virtual psi hpsi₀).natCast_smul scale)
  have htauBetaVirtual : ClassFunction.IsVirtual (tau beta) :=
    hsub.tau_virtual beta hbetaSpan hbetaOff
  have hlambdaNorm : characterPairing lambda lambda = 1 := by
    let chi : IrreducibleCharacter M ℂ := ⟨lambda, hlambdaIrr⟩
    exact IrreducibleCharacter.characterPairing_self chi
  have hpsiNorm : characterPairing psi psi = 1 := by
    let chi : IrreducibleCharacter M ℂ := ⟨psi, hpsiIrr⟩
    exact IrreducibleCharacter.characterPairing_self chi
  have hlambdaPsi : characterPairing lambda psi = 0 :=
    hsub.pairwise_orthogonal hlambda₀ hpsi₀
      (fun heq ↦ hlambdaNot (heq ▸ hpsi₂))
  have hpsiLambda : characterPairing psi lambda = 0 := by
    rw [characterPairing_comm]
    exact hlambdaPsi
  have hbetaNormSource : characterPairing beta beta =
      ((1 + scale ^ 2 : ℕ) : ℂ) := by
    simp only [beta, pTypeCoreBeta, pairing_sub_left, pairing_sub_right,
      characterPairing_smul_left, characterPairing_smul_right,
      hlambdaNorm, hpsiNorm, hlambdaPsi, hpsiLambda]
    push_cast
    ring
  have hbetaNorm : characterPairing (tau beta) (tau beta) =
      ((1 + scale ^ 2 : ℕ) : ℂ) := by
    rw [hsub.tau_isometry beta hbetaSpan hbetaOff
      beta hbetaSpan hbetaOff]
    exact hbetaNormSource

  have hbetaDiff : ∀ eta ∈ T₁, eta ≠ tau₂ psi →
      characterPairing (tau beta) (tau₂ psi - eta) =
        -(scale : ℂ) := by
    intro eta heta hne
    obtain ⟨zeta, hzeta₂, rfl⟩ := Finset.mem_image.mp heta
    have hzetaNe : zeta ≠ psi := by
      intro heq
      subst zeta
      exact hne rfl
    have hzeta₀ : zeta ∈ S₀ := hS₂.1 hzeta₂
    have hdiffSpan₂ : psi - zeta ∈
        AddSubgroup.closure (↑S₂ : Set (ClassFunction M ℂ)) :=
      (AddSubgroup.closure (↑S₂ : Set (ClassFunction M ℂ))).sub_mem
        (AddSubgroup.subset_closure hpsi₂)
        (AddSubgroup.subset_closure hzeta₂)
    have hdiffSpan₀ : psi - zeta ∈
        AddSubgroup.closure (↑S₀ : Set (ClassFunction M ℂ)) :=
      AddSubgroup.closure_mono hS₂.1 hdiffSpan₂
    have hzetaDegree : zeta 1 = ((D.q * a : ℕ) : ℂ) := by
      have hmem : zeta ∈ pTypeCoreDegreeSlice S₀ (D.q * a) := by
        rw [← rigid.current_eq_slice]
        exact hzeta₂
      exact (Finset.mem_filter.mp hmem).2
    have hdiffOff : psi - zeta ∈
        ClassFunction.supportedOn (nonidentitySet M) := by
      rw [ClassFunction.mem_supportedOn_iff]
      intro x hx
      have hxOne : x = 1 := by simpa [nonidentitySet] using not_not.mp hx
      subst x
      change psi 1 - zeta 1 = 0
      rw [hpsiDegree, hzetaDegree, sub_self]
    have hagree : tau₂ (psi - zeta) = tau (psi - zeta) :=
      hcoh₂.agrees (psi - zeta) hdiffSpan₂ hdiffOff
    have hpsiZeta : characterPairing psi zeta = 0 :=
      hsub.pairwise_orthogonal hpsi₀ hzeta₀ hzetaNe.symm
    have hlambdaZeta : characterPairing lambda zeta = 0 :=
      hsub.pairwise_orthogonal hlambda₀ hzeta₀
        (fun heq ↦ hlambdaNot (heq ▸ hzeta₂))
    rw [← map_sub, hagree,
      hsub.tau_isometry beta hbetaSpan hbetaOff
        (psi - zeta) hdiffSpan₀ hdiffOff]
    simp only [beta, pTypeCoreBeta, pairing_sub_left, pairing_sub_right,
      characterPairing_smul_left, hlambdaPsi, hlambdaZeta,
      hpsiNorm, hpsiZeta]
    ring

  have hlambdaInv₃ : ClassFunction.inverseLinear lambda ∈ S₃ :=
    hS₃.2 lambda hlambda₃
  have hlambdaInv₀ : ClassFunction.inverseLinear lambda ∈ S₀ :=
    hS₃.1 hlambdaInv₃
  have hlambdaInvSmall : ClassFunction.inverseLinear lambda ∈
      pTypeCoreFamily HU H H₀C :=
    seqInd_inverse_mem (k := ℂ) HU H H₀C hlambdaSmall
  have hlambdaInvIrr : IsIrreducibleCharacter M ℂ
      (ClassFunction.inverseLinear lambda) := by
    let chi : IrreducibleCharacter M ℂ := ⟨lambda, hlambdaIrr⟩
    change IsIrreducibleCharacter M ℂ
      (ClassFunction.inverseLinear (chi : ClassFunction M ℂ))
    rw [ClassFunction.inverseLinear_irreducible chi]
    exact (IrreducibleCharacter.dual chi).property
  have hlambdaInv₄ : ClassFunction.inverseLinear lambda ∈ S₄ := by
    apply Finset.mem_filter.mpr
    exact ⟨hlambdaInv₃, ⟨hlambdaInvSmall, hlambdaInvIrr⟩⟩
  let detector := tau₃ (lambda - ClassFunction.inverseLinear lambda)
  have hdetectorSpan : detector ∈
      AddSubgroup.closure (↑T₄ : Set (ClassFunction (⊤ : Subgroup G) ℂ)) := by
    dsimp only [detector]
    rw [map_sub]
    apply (AddSubgroup.closure
      (↑T₄ : Set (ClassFunction (⊤ : Subgroup G) ℂ))).sub_mem
    · exact AddSubgroup.subset_closure
        (Finset.mem_image.mpr ⟨lambda, hlambda₄, rfl⟩)
    · exact AddSubgroup.subset_closure
        (Finset.mem_image.mpr
          ⟨ClassFunction.inverseLinear lambda, hlambdaInv₄, rfl⟩)
  have hdetectorSourceSpan :
      lambda - ClassFunction.inverseLinear lambda ∈
        AddSubgroup.closure (↑S₃ : Set (ClassFunction M ℂ)) :=
    (AddSubgroup.closure (↑S₃ : Set (ClassFunction M ℂ))).sub_mem
      (AddSubgroup.subset_closure hlambda₃)
      (AddSubgroup.subset_closure hlambdaInv₃)
  have hdetectorSourceSpan₀ :
      lambda - ClassFunction.inverseLinear lambda ∈
        AddSubgroup.closure (↑S₀ : Set (ClassFunction M ℂ)) :=
    AddSubgroup.closure_mono hS₃.1 hdetectorSourceSpan
  have hlambdaInvDegree : ClassFunction.inverseLinear lambda 1 =
      ((D.q * u₀ : ℕ) : ℂ) :=
    rigid.remainder_degree (ClassFunction.inverseLinear lambda) hlambdaInv₃
  have hdetectorOff : lambda - ClassFunction.inverseLinear lambda ∈
      ClassFunction.supportedOn (nonidentitySet M) := by
    rw [ClassFunction.mem_supportedOn_iff]
    intro x hx
    have hxOne : x = 1 := by simpa [nonidentitySet] using not_not.mp hx
    subst x
    change lambda 1 - ClassFunction.inverseLinear lambda 1 = 0
    rw [hlambdaDegree, hlambdaInvDegree, sub_self]
  have hdetectorAgree : detector =
      tau (lambda - ClassFunction.inverseLinear lambda) :=
    hcoh₃.agrees (lambda - ClassFunction.inverseLinear lambda)
      hdetectorSourceSpan hdetectorOff
  have hlambdaInvPair : characterPairing lambda
      (ClassFunction.inverseLinear lambda) = 0 :=
    hsub.pairwise_orthogonal hlambda₀ hlambdaInv₀
      (hsub.inverse_ne lambda hlambda₀).symm
  have hpsiInvPair : characterPairing psi
      (ClassFunction.inverseLinear lambda) = 0 := by
    apply hsub.pairwise_orthogonal hpsi₀ hlambdaInv₀
    intro heq
    have heqInv : ClassFunction.inverseLinear psi = lambda := by
      calc
        ClassFunction.inverseLinear psi =
            ClassFunction.inverseLinear
              (ClassFunction.inverseLinear lambda) :=
          congrArg ClassFunction.inverseLinear heq
        _ = lambda := by
          ext x
          simp
    exact hlambdaNot (heqInv ▸ hS₂.2 psi hpsi₂)
  have hdetectorPair : characterPairing (tau beta) detector = 1 := by
    rw [hdetectorAgree,
      hsub.tau_isometry beta hbetaSpan hbetaOff
        (lambda - ClassFunction.inverseLinear lambda)
        hdetectorSourceSpan₀ hdetectorOff]
    simp only [beta, pTypeCoreBeta, pairing_sub_left, pairing_sub_right,
      characterPairing_smul_left, hlambdaNorm, hlambdaInvPair,
      hpsiLambda, hpsiInvPair]
    ring

  obtain ⟨Gamma, hGammaSpan, _hGammaNorm, b, hdecomp⟩ :=
    pTypeCore_bool_decomposition_of_orthogonal_splits
      T₄ T₁ hT₄virtual hT₄orth hT₁virtual hT₁orth hcross
      htauBetaVirtual hphiT₁ hT₁card hbetaNorm hbetaDiff
      ⟨detector, hdetectorSpan,
        by rw [hdetectorPair]; exact one_ne_zero⟩

  let alpha := pTypeCoreAlpha gamma psi
  have halphaFacts := alpha_target_facts
    ctx facts not_Galois S₂ rigid tau₃ R hsub hcoh₃ hpsi₂
  have halphaTauVirtual : ClassFunction.IsVirtual (tau alpha) := by
    simpa only [alpha, tau] using halphaFacts.1
  have halphaVirtual : ClassFunction.IsVirtual alpha :=
    (pTypeCoreGamma_isVirtual ctx facts not_Galois).sub
      (hsub.source_virtual psi hpsi₀)
  have halphaSupportSmall : alpha ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport M} := by
    simpa only [alpha, gamma] using pTypeCoreAlpha_supportedOn rigid hpsi₂
  have halphaSupport : alpha ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport0 M} :=
    supportedOn_FTsupport0_of_FTsupport halphaSupportSmall
  have hbetaSupportSmall : beta ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport M} := by
    have hprime : beta ∈ ClassFunction.supportedOn
        (primeDadeSupport M (FTsupport M)) := by
      apply (ClassFunction.supportedOn
        (R := ℂ) (primeDadeSupport M (FTsupport M))).sub_mem
      · exact pTypeCoreFamilyOfContext_supportedOn ctx facts hlambda₀
      · exact (ClassFunction.supportedOn
          (R := ℂ) (primeDadeSupport M (FTsupport M))).smul_mem
            (scale : ℂ)
            (pTypeCoreFamilyOfContext_supportedOn ctx facts hpsi₀)
    rw [ClassFunction.mem_supportedOn_iff]
    intro x hx
    by_cases hxOne : x = 1
    · subst x
      exact pTypeCoreBeta_one_eq_zero lambda psi scale hdegreeBalance
    · apply ClassFunction.eq_zero_of_mem_supportedOn hprime
      rw [mem_primeDadeSupport, not_or]
      exact ⟨fun hx' ↦ hxOne (Subtype.ext hx'), hx⟩
  have hbetaSupport : beta ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport0 M} :=
    supportedOn_FTsupport0_of_FTsupport hbetaSupportSmall
  have hGammaAlpha : characterPairing (tau alpha) Gamma = 0 := by
    apply pairing_zero_on_right_closure T₄ (tau alpha) ?_ hGammaSpan
    intro eta heta
    obtain ⟨zeta, hzeta₄, rfl⟩ := Finset.mem_image.mp heta
    exact halphaFacts.2.2 zeta (Finset.mem_filter.mp hzeta₄).1
  have halphaBeta : characterPairing (tau alpha) (tau beta) =
      (scale : ℂ) := by
    have hiso := Dade_isometry (FT_Dade0_hyp M ctx.maxM)
      alpha beta halphaSupport hbetaSupport
    rw [pTypeCore_starPairing_eq_pairing_of_virtual
          halphaTauVirtual htauBetaVirtual,
        pTypeCore_starPairing_eq_pairing_of_virtual
          halphaVirtual hbetaVirtual] at hiso
    rw [hiso]
    exact pTypeCore_alpha_beta_pairing gamma psi lambda scale
      (pTypeCoreGamma_pairing_family_eq_zero
        ctx facts not_Galois hlambda₀)
      (PTypeCoreSupportInternal.PTypeCoreRigidFacts.gamma_pairing_slice_eq_zero
        rigid hpsi₂)
      hpsiLambda hpsiNorm

  have halphaDiff : ∀ eta ∈ T₁, eta ≠ tau₂ psi →
      characterPairing (tau alpha) (tau₂ psi - eta) = -1 := by
    intro eta heta hne
    obtain ⟨zeta, hzeta₂, rfl⟩ := Finset.mem_image.mp heta
    have hzetaNe : zeta ≠ psi := by
      intro heq
      subst zeta
      exact hne rfl
    have hzeta₀ : zeta ∈ S₀ := hS₂.1 hzeta₂
    have hzetaDegree : zeta 1 = ((D.q * a : ℕ) : ℂ) := by
      have hmem : zeta ∈ pTypeCoreDegreeSlice S₀ (D.q * a) := by
        rw [← rigid.current_eq_slice]
        exact hzeta₂
      exact (Finset.mem_filter.mp hmem).2
    have hdiffSpan₂ : psi - zeta ∈
        AddSubgroup.closure (↑S₂ : Set (ClassFunction M ℂ)) :=
      (AddSubgroup.closure (↑S₂ : Set (ClassFunction M ℂ))).sub_mem
        (AddSubgroup.subset_closure hpsi₂)
        (AddSubgroup.subset_closure hzeta₂)
    have hdiffSpan₀ : psi - zeta ∈
        AddSubgroup.closure (↑S₀ : Set (ClassFunction M ℂ)) :=
      AddSubgroup.closure_mono hS₂.1 hdiffSpan₂
    have hdiffOff : psi - zeta ∈
        ClassFunction.supportedOn (nonidentitySet M) := by
      rw [ClassFunction.mem_supportedOn_iff]
      intro x hx
      have hxOne : x = 1 := by simpa [nonidentitySet] using not_not.mp hx
      subst x
      change psi 1 - zeta 1 = 0
      rw [hpsiDegree, hzetaDegree, sub_self]
    have hdiffSupport : psi - zeta ∈ ClassFunction.supportedOn
        {x : M | (x : G) ∈ FTsupport0 M} :=
      supportedOn_FTsupport0_of_FTsupport
        (pTypeCore_family_difference_supportedOn
          ctx facts hpsi₀ hzeta₀ (hpsiDegree.trans hzetaDegree.symm))
    have hdiffVirtual : ClassFunction.IsVirtual (psi - zeta) :=
      (hsub.source_virtual psi hpsi₀).sub
        (hsub.source_virtual zeta hzeta₀)
    have htauDiffVirtual : ClassFunction.IsVirtual (tau (psi - zeta)) :=
      hsub.tau_virtual (psi - zeta) hdiffSpan₀ hdiffOff
    have hagree : tau₂ (psi - zeta) = tau (psi - zeta) :=
      hcoh₂.agrees (psi - zeta) hdiffSpan₂ hdiffOff
    have hiso := Dade_isometry (FT_Dade0_hyp M ctx.maxM)
      alpha (psi - zeta) halphaSupport hdiffSupport
    rw [pTypeCore_starPairing_eq_pairing_of_virtual
          halphaTauVirtual htauDiffVirtual,
        pTypeCore_starPairing_eq_pairing_of_virtual
          halphaVirtual hdiffVirtual] at hiso
    rw [← map_sub, hagree, hiso]
    have hgammaPsi : characterPairing gamma psi = 0 := by
      simpa only [gamma] using
        PTypeCoreSupportInternal.PTypeCoreRigidFacts.gamma_pairing_slice_eq_zero
          rigid hpsi₂
    have hgammaZeta : characterPairing gamma zeta = 0 := by
      simpa only [gamma] using
        pTypeCoreGamma_pairing_family_eq_zero
          ctx facts not_Galois hzeta₀
    have hpsiZeta : characterPairing psi zeta = 0 :=
      hsub.pairwise_orthogonal hpsi₀ hzeta₀ hzetaNe.symm
    simp only [alpha, pTypeCoreAlpha, pairing_sub_left,
      pairing_sub_right, hgammaPsi, hgammaZeta, hpsiNorm, hpsiZeta]
    ring

  have hbFalse : b = false :=
    pTypeCore_bool_eq_false_of_alpha_pairing
      T₁ halphaTauVirtual (hT₁virtual (tau₂ psi) hphiT₁)
      hphiT₁ scale hscale hT₁card halphaDiff
      hGammaAlpha halphaBeta b hdecomp
  have hmapped : tau (lambda - (scale : ℂ) • psi) =
      Gamma - (scale : ℂ) • tau₂ psi := by
    change tau beta = Gamma - (scale : ℂ) • tau₂ psi
    rw [hdecomp, hbFalse]
    simp
  have hGammaPhi : characterPairing Gamma (tau₂ psi) = 0 := by
    apply pairing_zero_on_left_closure T₄ (tau₂ psi) ?_ hGammaSpan
    intro eta heta
    exact hcross eta heta (tau₂ psi) hphiT₁
  have htarget :
      characterPairing Gamma ((scale : ℂ) • tau₂ psi) = 0 := by
    rw [characterPairing_smul_right, hGammaPhi, mul_zero]
  let extension : PTypeCoreExtensionInput S₀ S₂ tau tau₂ :=
    { chi := lambda
      phi := psi
      scale := scale
      target := Gamma
      phi_mem := hpsi₂
      chi_mem := hlambda₀
      chi_not_mem := hlambdaNot
      degree_balance := hdegreeBalance
      target_orthogonal := htarget
      mapped_balance := hmapped }
  refine ⟨lambda, hlambda₀, hlambdaNot, ?_⟩
  exact pTypeCore_coherent_insert_of_extensionInput
    S₀ S₂ tau tau₂ R hsub hS₂ hcoh₂ extension

/-! ## The public one-step adapter -/

/-- One non-Galois progress step: either the degree-sum inequality extends
the current family immediately, or the rigid Boolean calculation does. -/
theorem pTypeCore_nonGalois_extension_step
    {G : Type} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (R : ClassFunction M ℂ → Finset (ClassFunction (⊤ : Subgroup G) ℂ))
    (hsub : subcoherent
      (↑(pTypeCoreFamilyOfContext ctx) : Set (ClassFunction M ℂ))
      (Dade (FT_Dade0_hyp M ctx.maxM)) R)
    (S₂ : Finset (ClassFunction M ℂ))
    (hbase :
      (↑(pTypeCoreDegreeSlice (pTypeCoreFamilyOfContext ctx)
        ((Ptype_factor_action ctx facts).q *
          pTypeNonGaloisIndex
            (Ptype_factor_action_hypotheses ctx facts) not_Galois)) :
          Set (ClassFunction M ℂ)) ⊆
        (↑S₂ : Set (ClassFunction M ℂ)))
    (hS₂ : cfConjC_subset
      (↑S₂ : Set (ClassFunction M ℂ))
      (↑(pTypeCoreFamilyOfContext ctx) : Set (ClassFunction M ℂ)))
    (tau₂ : ClassFunction M ℂ →ₗ[ℂ] ClassFunction (⊤ : Subgroup G) ℂ)
    (hcoh₂ : coherent_with
      (↑S₂ : Set (ClassFunction M ℂ))
      (nonidentitySet M) (Dade (FT_Dade0_hyp M ctx.maxM)) tau₂)
    (hremaining : ∃ chi ∈ pTypeCoreFamilyOfContext ctx, chi ∉ S₂) :
    ∃ chi : ClassFunction M ℂ,
      chi ∈ pTypeCoreFamilyOfContext ctx ∧ chi ∉ S₂ ∧
        coherent
          ({chi, ClassFunction.inverseLinear chi} ∪
            (↑S₂ : Set (ClassFunction M ℂ)))
          (nonidentitySet M)
          (Dade (FT_Dade0_hyp M ctx.maxM)) := by
  rcases pTypeCore_nonGalois_early_or_rigid
      ctx facts not_Galois S₂
      (Dade (FT_Dade0_hyp M ctx.maxM)) tau₂ R hsub
      hbase hS₂ hcoh₂ hremaining with hearly | rigid
  · exact hearly
  · exact rigid_extension
      ctx facts not_Galois S₂ tau₂ R hsub hS₂ hcoh₂ rigid

end PTypeCoreNonGaloisExtensionInternal

end

end Submission.OddOrder.PF
