import Submission.OddOrder.PF.Section12.FTType1NonFrobeniusGroupBridge
import Submission.OddOrder.PF.Section01.PrimitiveRootCharacterCongruence
import Submission.OddOrder.PF.Section01.PrimePrimitiveRootDivisibility

/-!
# Peterfalvi 12.13--12.16: the type-I character contradiction

The group-theoretic input is isolated in
`FTType1NonFrobeniusGroupBridge`.  This file supplies the character and
norm argument which turns that input into a contradiction.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open scoped BigOperators Classical Pointwise

variable {G : Type} [Group G] [Finite G] [IsMinSimpleOddGroup G]

local instance : Fintype G := Fintype.ofFinite G

/-! ## Generic local character lemmas -/

private theorem invDade_of_constant12
    {Γ : Type*} [Group Γ] [Fintype Γ]
    {Q L : Subgroup Γ} {A : Set Γ}
    (dd : DadeHypothesis Q L A) (chi : ClassFunction Q ℂ)
    {a : Γ} (ha : a ∈ A)
    (hchi : ∀ x : DadeSignalizer dd a,
      chi ⟨(x : Γ) * a,
        Q.mul_mem (Dade_signalizer_sub dd a x.property)
          (dd.2.1 (dd.1.1 ha))⟩ =
        chi ⟨a, dd.2.1 (dd.1.1 ha)⟩) :
    invDade dd chi ⟨a, dd.1.1 ha⟩ =
      chi ⟨a, dd.2.1 (dd.1.1 ha)⟩ := by
  rw [invDade_apply]
  change
    (if _ha : a ∈ A then
      (Nat.card (DadeSignalizer dd a) : ℂ)⁻¹ *
        ∑ x : DadeSignalizer dd a,
          chi ⟨(x : Γ) * a,
            Q.mul_mem (Dade_signalizer_sub dd a x.property)
              (dd.2.1 (dd.1.1 ha))⟩
    else 0) = chi ⟨a, dd.2.1 (dd.1.1 ha)⟩
  rw [dif_pos ha]
  rw [show (∑ x : DadeSignalizer dd a,
      chi ⟨(x : Γ) * a,
        Q.mul_mem (Dade_signalizer_sub dd a x.property)
          (dd.2.1 (dd.1.1 ha))⟩) =
      ∑ _x : DadeSignalizer dd a,
        chi ⟨a, dd.2.1 (dd.1.1 ha)⟩ by
    apply Finset.sum_congr rfl
    intro x _
    exact hchi x]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Nat.card_eq_fintype_card]
  field_simp [Nat.cast_ne_zero.mpr
    (Fintype.card_pos.ne' : Fintype.card (DadeSignalizer dd a) ≠ 0)]

private theorem restrict_virtual12
    {Q : Type} [Group Q] [Fintype Q] (S : Subgroup Q)
    {f : ClassFunction Q ℂ} (hf : ClassFunction.IsVirtual f) :
    ClassFunction.IsVirtual (ClassFunction.restrict S f) := by
  obtain ⟨v, rfl⟩ := hf
  refine ⟨VirtualCharacter.comap S.subtype v, ?_⟩
  rw [VirtualCharacter.realize_comap]
  ext x
  rfl

private theorem virtual_value_integral12
    {Q : Type} [Group Q] [Fintype Q]
    {f : ClassFunction Q ℂ} (hf : ClassFunction.IsVirtual f) (x : Q) :
    IsIntegral ℤ (f x) := by
  obtain ⟨v, rfl⟩ := hf
  induction v using Finsupp.induction with
  | zero => simpa using (isIntegral_zero : IsIntegral ℤ (0 : ℂ))
  | single_add chi n v hchi hn ih =>
      simp only [VirtualCharacter.realize_add,
        VirtualCharacter.realize_single, ClassFunction.add_apply,
        ClassFunction.smul_apply, smul_eq_mul]
      exact ((isIntegral_intCast n).mul (by
        rw [← chi.representation_character]
        exact representation_character_isIntegral
          chi.representation.ρ x)).add ih

private theorem starPairing_sub_left12
    {Q : Type*} [Group Q] [Fintype Q]
    (f g h : ClassFunction Q ℂ) :
    starCharacterPairing (f - g) h =
      starCharacterPairing f h - starCharacterPairing g h := by
  simp [sub_eq_add_neg, starCharacterPairing, twistedCharacterPairing,
    add_mul, Finset.sum_add_distrib]
  ring

private theorem starPairing_sub_right12
    {Q : Type*} [Group Q] [Fintype Q]
    (f g h : ClassFunction Q ℂ) :
    starCharacterPairing f (g - h) =
      starCharacterPairing f g - starCharacterPairing f h := by
  simp [sub_eq_add_neg, starCharacterPairing, twistedCharacterPairing,
    mul_add, Finset.sum_add_distrib]

private theorem starPairing_sum_left12
    {Q : Type*} [Group Q] [Fintype Q]
    {J : Type*} (s : Finset J) (f : J → ClassFunction Q ℂ)
    (g : ClassFunction Q ℂ) :
    starCharacterPairing (∑ i ∈ s, f i) g =
      ∑ i ∈ s, starCharacterPairing (f i) g := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, starCharacterPairing_add_left, ih,
        Finset.sum_insert hi]

private theorem starPairing_sum_right12
    {Q : Type*} [Group Q] [Fintype Q]
    (f : ClassFunction Q ℂ) {J : Type*}
    (s : Finset J) (g : J → ClassFunction Q ℂ) :
    starCharacterPairing f (∑ i ∈ s, g i) =
      ∑ i ∈ s, starCharacterPairing f (g i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, starCharacterPairing_add_right, ih,
        Finset.sum_insert hi]

private theorem normSq_add_of_star_orthogonal12
    {Q : Type*} [Group Q] [Fintype Q]
    (f g : ClassFunction Q ℂ)
    (hfg : starCharacterPairing f g = 0) :
    classFunctionNormSq (f + g) =
      classFunctionNormSq f + classFunctionNormSq g := by
  have hgf : starCharacterPairing g f = 0 := by
    rw [starCharacterPairing_conj_symm, hfg]
    simp
  rw [classFunctionNormSq_eq_re_starCharacterPairing,
    classFunctionNormSq_eq_re_starCharacterPairing,
    classFunctionNormSq_eq_re_starCharacterPairing,
    starCharacterPairing_add_left, starCharacterPairing_add_right,
    starCharacterPairing_add_right, hfg, hgf]
  simp

private theorem normSq_smul12
    {Q : Type*} [Group Q] [Fintype Q]
    (a : ℂ) (f : ClassFunction Q ℂ) :
    classFunctionNormSq (a • f) =
      Complex.normSq a * classFunctionNormSq f := by
  unfold classFunctionNormSq
  simp only [ClassFunction.smul_apply, smul_eq_mul, Complex.normSq_mul,
    Finset.mul_sum]
  ring

private theorem normSq_affine_integer12
    {Q : Type*} [Group Q] [Fintype Q]
    (f g : ClassFunction Q ℂ) (a : ℤ) (s : ℝ)
    (hff : classFunctionNormSq f = 1)
    (hgg : classFunctionNormSq g = s)
    (hfg : starCharacterPairing f g = 1)
    (hgf : starCharacterPairing g f = 1) :
    classFunctionNormSq (-f + (a : ℂ) • g) =
      1 + (a : ℝ) ^ 2 * s - 2 * (a : ℝ) := by
  have hAA :
      starCharacterPairing ((-1 : ℂ) • f) ((-1 : ℂ) • f) = 1 := by
    rw [starCharacterPairing_smul_left, starCharacterPairing_smul_right,
      starCharacterPairing_self_eq_classFunctionNormSq, hff]
    norm_num
  have hAB :
      starCharacterPairing ((-1 : ℂ) • f) ((a : ℂ) • g) =
        -(a : ℂ) := by
    rw [starCharacterPairing_smul_left, starCharacterPairing_smul_right,
      hfg]
    simp
  have hBA :
      starCharacterPairing ((a : ℂ) • g) ((-1 : ℂ) • f) =
        -(a : ℂ) := by
    rw [starCharacterPairing_smul_left, starCharacterPairing_smul_right,
      hgf]
    simp
  have hBB :
      starCharacterPairing ((a : ℂ) • g) ((a : ℂ) • g) =
        (a : ℂ) ^ 2 * (s : ℂ) := by
    rw [starCharacterPairing_smul_left, starCharacterPairing_smul_right,
      starCharacterPairing_self_eq_classFunctionNormSq, hgg]
    simp
    ring
  rw [← neg_one_smul ℂ f,
    classFunctionNormSq_eq_re_starCharacterPairing,
    starCharacterPairing_add_left, starCharacterPairing_add_right,
    starCharacterPairing_add_right, hAA, hAB, hBA, hBB]
  norm_num
  rw [show ((a : ℂ) ^ 2).re = (a : ℝ) ^ 2 by
    rw [← Complex.ofReal_intCast a, ← Complex.ofReal_pow,
      Complex.ofReal_re]]
  ring

private theorem normSq_sum_pairwise12
    {Q : Type*} [Group Q] [Fintype Q]
    {J : Type*} [DecidableEq J]
    (s : Finset J) (f : J → ClassFunction Q ℂ)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      starCharacterPairing (f i) (f j) = 0) :
    classFunctionNormSq (∑ i ∈ s, f i) =
      ∑ i ∈ s, classFunctionNormSq (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [classFunctionNormSq]
  | @insert i s hi ih =>
      have his : starCharacterPairing (f i) (∑ j ∈ s, f j) = 0 := by
        rw [starPairing_sum_right12]
        apply Finset.sum_eq_zero
        intro j hj
        exact horth i (Finset.mem_insert_self i s) j
          (Finset.mem_insert_of_mem hj) (fun hij ↦ hi (hij ▸ hj))
      rw [Finset.sum_insert hi, normSq_add_of_star_orthogonal12 _ _ his,
        Finset.sum_insert hi]
      congr 1
      exact ih fun a ha b hb hab ↦
        horth a (Finset.mem_insert_of_mem ha)
          b (Finset.mem_insert_of_mem hb) hab

/-- A virtual character constant on `A \ B` has an integral common value. -/
private theorem virtual_shell_value_integer12
    {Q : Type} [Group Q] [Fintype Q]
    (A B : Subgroup Q) (hBA : B ≤ A)
    {f : ClassFunction Q ℂ} (hf : ClassFunction.IsVirtual f)
    {x : Q} (hxA : x ∈ A) (hxB : x ∉ B)
    (hconst : ∀ y : Q, y ∈ A → y ∉ B → f y = f x) :
    ∃ n : ℤ, f x = (n : ℂ) := by
  classical
  have hfxInt := virtual_value_integral12 hf x
  apply (IsIntegral.exists_int_iff_exists_rat hfxInt).mp
  have hfA := restrict_virtual12 A hf
  have hfB := restrict_virtual12 B hf
  obtain ⟨a, ha⟩ :=
    PTypeCorePairingInternal.pTypeCore_virtual_pairing_isInt hfA
      (FTType1InfrastructureInternal.irreducibleIsVirtual
        (IrreducibleCharacter.trivial : IrreducibleCharacter A ℂ))
  obtain ⟨b, hb⟩ :=
    PTypeCorePairingInternal.pTypeCore_virtual_pairing_isInt hfB
      (FTType1InfrastructureInternal.irreducibleIsVirtual
        (IrreducibleCharacter.trivial : IrreducibleCharacter B ℂ))
  let shell := {y : A // (y : Q) ∉ B}
  have hshell : Nonempty shell := ⟨⟨⟨x, hxA⟩, hxB⟩⟩
  have hshellNe : Nat.card shell ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨hshell, inferInstance⟩
  have hsumB :
      (∑ y : {y : A // (y : Q) ∈ B}, f (y : Q)) =
        ∑ y : B, f (y : Q) := by
    let e : {y : A // (y : Q) ∈ B} ≃ B :=
      { toFun := fun y ↦ ⟨y, y.2⟩
        invFun := fun y ↦ ⟨⟨y, hBA y.2⟩, y.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    exact Fintype.sum_equiv e (fun y ↦ f (y : Q))
      (fun y ↦ f (y : Q)) (fun _ ↦ rfl)
  have hsplit :
      (∑ y : A, f (y : Q)) =
        (∑ y : B, f (y : Q)) + (Nat.card shell : ℂ) * f x := by
    calc
      (∑ y : A, f (y : Q)) =
          (∑ y : {y : A // (y : Q) ∈ B}, f (y : Q)) +
            ∑ y : shell, f (y : Q) :=
        (Fintype.sum_subtype_add_sum_subtype
          (fun y : A ↦ (y : Q) ∈ B) (fun y : A ↦ f (y : Q))).symm
      _ = (∑ y : B, f (y : Q)) + ∑ y : shell, f (y : Q) := by
        rw [hsumB]
      _ = (∑ y : B, f (y : Q)) + (Nat.card shell : ℂ) * f x := by
        congr 1
        calc
          (∑ y : shell, f (y : Q)) = ∑ _y : shell, f x := by
            apply Finset.sum_congr rfl
            intro y _
            exact hconst y y.1.2 y.2
          _ = (Nat.card shell : ℂ) * f x := by
            simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
              Nat.card_eq_fintype_card]
  have haverageA :
      (Nat.card A : ℂ) * (a : ℂ) = ∑ y : A, f (y : Q) := by
    rw [← ha]
    simp only [characterPairing, ClassFunction.restrict_apply,
      IrreducibleCharacter.trivial_apply, inv_one, mul_one]
    field_simp [Nat.cast_ne_zero.mpr (Nat.card_pos.ne' : Nat.card A ≠ 0)]
  have haverageB :
      (Nat.card B : ℂ) * (b : ℂ) = ∑ y : B, f (y : Q) := by
    rw [← hb]
    simp only [characterPairing, ClassFunction.restrict_apply,
      IrreducibleCharacter.trivial_apply, inv_one, mul_one]
    field_simp [Nat.cast_ne_zero.mpr (Nat.card_pos.ne' : Nat.card B ≠ 0)]
  let q : ℚ :=
    ((Nat.card A : ℚ) * (a : ℚ) - (Nat.card B : ℚ) * (b : ℚ)) /
      Nat.card shell
  refine ⟨q, ?_⟩
  dsimp only [q]
  simp only [Rat.cast_div, Rat.cast_sub, Rat.cast_mul,
    Rat.cast_natCast, Rat.cast_intCast]
  apply (eq_div_iff (Nat.cast_ne_zero.mpr hshellNe :
    (Nat.card shell : ℂ) ≠ 0)).2
  have hformula :
      (Nat.card shell : ℂ) * f x =
        (Nat.card A : ℂ) * (a : ℂ) - (Nat.card B : ℂ) * (b : ℂ) := by
    rw [haverageA, haverageB, hsplit]
    ring
  simpa only [mul_comm] using hformula

/-! ## Ambient/top transport and Fitting coherence -/

private noncomputable def characterSourceMap12 :
    ClassFunction G ℂ →ₗ[ℂ] ClassFunction (⊤ : Subgroup G) ℂ :=
  ClassFunction.comap Subgroup.topEquiv.toMonoidHom

private noncomputable def characterTargetMap12 :
    ClassFunction (⊤ : Subgroup G) ℂ →ₗ[ℂ] ClassFunction G ℂ :=
  ClassFunction.comap Subgroup.topEquiv.symm.toMonoidHom

@[simp] private theorem characterSource_target12
    (phi : ClassFunction (⊤ : Subgroup G) ℂ) :
    characterSourceMap12 (characterTargetMap12 phi) = phi := by
  ext x
  simpa [characterSourceMap12, characterTargetMap12,
    ClassFunction.comap_apply] using
      congrArg phi (Subgroup.topEquiv.symm_apply_apply x)

@[simp] private theorem characterTarget_source12
    (phi : ClassFunction G ℂ) :
    characterTargetMap12 (characterSourceMap12 phi) = phi := by
  ext x
  simpa [characterSourceMap12, characterTargetMap12,
    ClassFunction.comap_apply] using
      congrArg phi (Subgroup.topEquiv.apply_symm_apply x)

private theorem characterTarget_pairing12
    (phi psi : ClassFunction (⊤ : Subgroup G) ℂ) :
    characterPairing (characterTargetMap12 phi)
        (characterTargetMap12 psi) = characterPairing phi psi := by
  have hcard : Nat.card G = Nat.card (⊤ : Subgroup G) :=
    Nat.card_congr Subgroup.topEquiv.symm.toEquiv
  unfold characterPairing
  rw [hcard]
  congr 1
  refine Fintype.sum_equiv Subgroup.topEquiv.symm.toEquiv _ _ fun x ↦ ?_
  simp [characterTargetMap12, ClassFunction.comap_apply]

private theorem characterSource_pairing12
    (phi psi : ClassFunction G ℂ) :
    characterPairing (characterSourceMap12 phi)
        (characterSourceMap12 psi) = characterPairing phi psi := by
  rw [← characterTarget_pairing12
    (characterSourceMap12 phi) (characterSourceMap12 psi)]
  simp

private theorem characterSource_virtual12
    {phi : ClassFunction G ℂ} (hphi : ClassFunction.IsVirtual phi) :
    ClassFunction.IsVirtual (characterSourceMap12 phi) := by
  obtain ⟨z, rfl⟩ := hphi
  refine ⟨VirtualCharacter.comap Subgroup.topEquiv.toMonoidHom z, ?_⟩
  rw [VirtualCharacter.realize_comap]
  rfl

private theorem type1_fitting_coherence_top12
    {L : Subgroup G} (ctx : FTType1Context L)
    (nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (hcoh : coherent_with
      (FTType1SeqIndFamily L : Set (ClassFunction L ℂ))
      (nonidentitySet L) ctx.tau nu) :
    coherent_with
      (FTType1SeqIndFamily L : Set (ClassFunction L ℂ))
      (nonidentitySet L) (Dade (FT_DadeF_hyp L ctx.maxL))
      (characterSourceMap12.comp nu) := by
  refine ⟨?_, ?_, ?_⟩
  · intro phi hphi psi hpsi
    simpa only [LinearMap.comp_apply, characterSource_pairing12] using
      hcoh.isometry phi hphi psi hpsi
  · intro phi hphi
    exact characterSource_virtual12 (hcoh.mapsToVirtual phi hphi)
  · intro phi hphi hoff
    have hcoreSupport :
        phi ∈ ClassFunction.supportedOn (FTType1FittingIn L : Set L) := by
      have hclosure : ∀ {psi : ClassFunction L ℂ},
          psi ∈ AddSubgroup.closure
              (FTType1SeqIndFamily L : Set (ClassFunction L ℂ)) →
            psi ∈ ClassFunction.supportedOn
              (FTType1FittingIn L : Set L) := by
        intro psi hpsi
        induction hpsi using AddSubgroup.closure_induction with
        | mem xi hxi => exact seqInd_on (FTType1FittingIn L) hxi
        | zero => exact Submodule.zero_mem _
        | add x y hx hy ihx ihy => exact Submodule.add_mem _ ihx ihy
        | neg x hx ihx => exact Submodule.neg_mem _ ihx
      exact hclosure hphi
    have hsharpSupport : phi ∈ ClassFunction.supportedOn
        {x : L | (x : G) ∈ subgroupNonidentity (Fitting_core L)} := by
      rw [ClassFunction.mem_supportedOn_iff]
      intro x hx
      by_cases hxF : x ∈ FTType1FittingIn L
      · apply ClassFunction.eq_zero_of_mem_supportedOn hoff
        intro hxne
        have hxneG : (x : G) ≠ 1 := by
          intro hxOne
          apply hxne
          exact Subtype.ext hxOne
        exact hx ⟨hxF, hxneG⟩
      · exact ClassFunction.eq_zero_of_mem_supportedOn hcoreSupport hxF
    have hfullSupport : phi ∈ ClassFunction.supportedOn
        {x : L | (x : G) ∈ FTsupport L} := by
      rw [ClassFunction.mem_supportedOn_iff] at hsharpSupport ⊢
      intro x hx
      apply hsharpSupport
      intro hxSharp
      exact hx (Fcore_sub_FTsupp ctx.maxL hxSharp)
    change characterSourceMap12 (nu phi) = _
    rw [hcoh.agrees phi hphi hoff]
    change characterSourceMap12
      (characterTargetMap12 (Dade (FT_Dade_hyp L ctx.maxL) phi)) = _
    rw [characterSource_target12, FT_DadeE L ctx.maxL phi hfullSupport,
      ← FT_DadeF_E L ctx.maxL phi hsharpSupport]

/-! ## Frobenius transport and nonconjugacy -/

private theorem summaryFrobeniusData_isFrobeniusIn12
    {L : Subgroup G} (data : BGSummaryIIFrobeniusData L) :
    IsFrobeniusIn (Fitting_core L) data.complement L := by
  have hFL : Fitting_core L ≤ L := Fcore_sub L
  have hsup : Fitting_core L ⊔ data.complement = L := by
    apply le_antisymm (sup_le hFL data.complement_le)
    intro x hxL
    let xL : L := ⟨x, hxL⟩
    have hxTop : xL ∈ (⊤ : Subgroup L) := Subgroup.mem_top xL
    rw [← data.frobenius.isComplement.sup_eq_top,
      ← Subgroup.subgroupOf_sup hFL data.complement_le] at hxTop
    exact hxTop
  have hsd : IsInternalSemidirectProductIn
      (Fitting_core L) data.complement L :=
    ⟨hFL, data.complement_le, data.frobenius.kernel_normal,
      data.frobenius.isComplement⟩
  refine ⟨hsup, ?_⟩
  rw [hsup]
  exact ⟨hsd, data.frobenius⟩

private theorem isFrobeniusIn_map12
    {H U L : Subgroup G} (h : IsFrobeniusIn H U L) (e : G ≃* G) :
    IsFrobeniusIn (H.map e.toMonoidHom) (U.map e.toMonoidHom)
      (L.map e.toMonoidHom) := by
  let J := H ⊔ U
  let J' := H.map e.toMonoidHom ⊔ U.map e.toMonoidHom
  have hJ : J.map e.toMonoidHom = J' := by
    dsimp only [J, J']
    rw [Subgroup.map_sup]
  let eJ : J ≃* J' :=
    (e.subgroupMap J).trans (MulEquiv.subgroupCongr hJ)
  have hHmap :
      (H.subgroupOf J).map eJ.toMonoidHom =
        (H.map e.toMonoidHom).subgroupOf J' := by
    ext y
    rw [Subgroup.mem_map_equiv]
    change e.symm (y : G) ∈ H ↔
      (y : G) ∈ H.map e.toMonoidHom
    rw [Subgroup.mem_map_equiv]
  have hUmap :
      (U.subgroupOf J).map eJ.toMonoidHom =
        (U.map e.toMonoidHom).subgroupOf J' := by
    ext y
    rw [Subgroup.mem_map_equiv]
    change e.symm (y : G) ∈ U ↔
      (y : G) ∈ U.map e.toMonoidHom
    rw [Subgroup.mem_map_equiv]
  have hsd := FTContextInternal.semidirect_map_mulEquiv8 h.2.1 e
  have hfrob := FTContextInternal.frobenius_map_mulEquiv8 h.2.2 eJ
  rw [hHmap, hUmap] at hfrob
  refine ⟨?_, ?_, ?_⟩
  · rw [← Subgroup.map_sup, h.1]
  · simpa only [Subgroup.map_sup] using hsd
  · simpa only [J'] using hfrob

private theorem frobeniusIn_decomposition12
    {H U L : Subgroup G} (h : IsFrobeniusIn H U L) :
    IsFrobeniusDecomposition (H.subgroupOf L) (U.subgroupOf L) := by
  let J := H ⊔ U
  let e : J ≃* L := MulEquiv.subgroupCongr h.1
  have hFrob := FTContextInternal.frobenius_map_mulEquiv8 h.2.2 e
  have hHmap :
      (H.subgroupOf J).map e.toMonoidHom = H.subgroupOf L := by
    ext x
    rw [Subgroup.mem_map_equiv]
    rfl
  have hUmap :
      (U.subgroupOf J).map e.toMonoidHom = U.subgroupOf L := by
    ext x
    rw [Subgroup.mem_map_equiv]
    rfl
  rwa [hHmap, hUmap] at hFrob

private theorem witness_maximals_not_conjugate12
    {p : ℕ} {M P0 : Subgroup G}
    (ctx : FTType1NonFrobeniusContext p M P0)
    (w : NonFrobeniusFTType1Witness p M P0) :
    ¬ FTAmbientConjugate M w.L := by
  rintro ⟨g, hmap⟩
  obtain ⟨A, hAP0, hA⟩ := w.P0_rank_two.1
  have hpA : p ∣ Nat.card A := by
    rw [hA.card_eq]
    exact dvd_pow_self p (by omega : 2 ≠ 0)
  have hpL : p ∣ Nat.card (Fitting_core w.L) :=
    hpA.trans (Subgroup.card_dvd_of_le
      (hAP0.trans
        (FTType1NonFrobeniusInternal.p0_le_second_fitting12 ctx w)))
  have hcard : Nat.card (Fitting_core w.L) =
      Nat.card (Fitting_core M) := by
    rw [hmap, FcoreJ,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
  rw [hcard] at hpL
  exact (ctx.p_prime.coprime_iff_not_dvd.mp ctx.core_p_prime) hpL

private theorem ambient_conjugate_symm12
    {M L : Subgroup G} :
    FTAmbientConjugate M L → FTAmbientConjugate L M := by
  rintro ⟨x, rfl⟩
  refine ⟨x⁻¹, ?_⟩
  rw [Subgroup.map_map]
  ext y
  simp [MulAut.conj_apply, mul_assoc]

private theorem coherent_image_orthogonal12
    {L N : Subgroup G}
    (ctxL : FTType1Context L) (ctxN : FTType1Context N)
    (hnot : ¬ FTAmbientConjugate L N)
    (nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (hcoh : coherent_with
      (FTType1SeqIndFamily L : Set (ClassFunction L ℂ))
      (nonidentitySet L) ctxL.tau nu)
    {chi : ClassFunction L ℂ} (hchi : chi ∈ FTType1SeqIndFamily L) :
    FTType1OrthogonalToImages ctxN (nu chi) := by
  have hself : cfConjC_subset
      (FTType1SeqIndFamily L : Set (ClassFunction L ℂ))
      (FTType1SeqIndFamily L : Set (ClassFunction L ℂ)) := by
    have h := seqInd_conjC_subset1 (k := ℂ) (FTType1FittingIn L)
      ⊤ ⊤ ⊥ le_rfl
    refine ⟨?_, ?_⟩
    · simpa only [FTType1SeqIndFamily] using h.1
    · intro phi hphi
      change phi ∈ seqIndD (k := ℂ) (FTType1FittingIn L) ⊤ ⊥ at hphi
      change ClassFunction.inverseLinear phi ∈
        seqIndD (k := ℂ) (FTType1FittingIn L) ⊤ ⊥
      exact h.2 phi hphi
  obtain ⟨E, hER, hnu⟩ := mem_coherent_sum_subseq
    ctxL.R_spec.subcoherent_family hself hcoh hchi
  intro eta heta mu hmu
  rw [hnu]
  change characterPairingRight mu (∑ alpha ∈ E, alpha) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro alpha halpha
  exact FTtype1_seqInd_ortho ctxL ctxN hnot
    chi hchi eta heta alpha (hER halpha) mu hmu

/-! ## Reciprocal Dade evaluation -/

private theorem type1_rho_of_signalizer_constant12
    {M : Subgroup G} (ctxM : FTType1Context M)
    (psi : ClassFunction G ℂ) {g : G}
    (hg : g ∈ subgroupNonidentity (Fitting_core M))
    (hconst : ∀ z : G, z ∈ FTsignalizer M g →
      psi (z * g) = psi g) :
    ctxM.rho psi ⟨g, Fcore_sub M hg.1⟩ = psi g := by
  change invDade (FT_DadeF_hyp M ctxM.maxL)
      (characterSourceMap12 psi) ⟨g, Fcore_sub M hg.1⟩ = _
  apply invDade_of_constant12 (FT_DadeF_hyp M ctxM.maxL)
    (characterSourceMap12 psi) hg
  intro z
  have hz : (z : G) ∈ FTsignalizer M g := by
    rw [← def_FTsignalizerF M ctxM.maxL hg]
    exact z.property
  change psi ((z : G) * g) = psi g
  exact hconst (z : G) hz

private theorem rhoM_eq_on_fitting_nonidentity12
    {p : ℕ} {M P0 : Subgroup G}
    (ctx : FTType1NonFrobeniusContext p M P0)
    (w : NonFrobeniusFTType1Witness p M P0)
    {E : Subgroup G}
    (hFrobL : IsFrobeniusIn (Fitting_core w.L) E w.L)
    (nu : ClassFunction w.L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (hcoh : coherent_with
      (FTType1SeqIndFamily w.L : Set (ClassFunction w.L ℂ))
      (nonidentitySet w.L)
      (FTType1Context.tau ⟨w.L_maximal,
        FT_Frobenius_type1 ⟨w.L_maximal, ⟨E, hFrobL⟩⟩⟩) nu)
    {chi : ClassFunction w.L ℂ}
    (hchi : chi ∈ FTType1SeqIndFamily w.L) :
    ∀ (g : G) (hg : g ∈ subgroupNonidentity (Fitting_core M)),
      ctx.M_type_context.rho (nu chi) ⟨g, Fcore_sub M hg.1⟩ =
        nu chi g := by
  classical
  let ctxL : FTType1Context w.L :=
    ⟨w.L_maximal,
      FT_Frobenius_type1 ⟨w.L_maximal, ⟨E, hFrobL⟩⟩⟩
  have hnotLM : ¬ FTAmbientConjugate w.L M :=
    fun hLM ↦ witness_maximals_not_conjugate12 ctx w
      (ambient_conjugate_symm12 hLM)
  have hnotFrobM :=
    FTType1NonFrobeniusInternal.first_maximal_not_frobenius12 ctx w
  intro g hg
  apply type1_rho_of_signalizer_constant12 ctx.M_type_context
    (nu chi) hg
  intro z hz
  unfold FTsignalizer at hz
  split at hz
  · have hzOne : z = 1 := Subgroup.mem_bot.mp hz
    subst z
    simp
  · rename_i hcentNotM
    let facts := FTsupport_facts M ctx.M_type_context.maxL
    have hgOuter : g ∈ outerExceptionalSet M (FTsupport0 M) :=
      ⟨Fcore_sub_FTsupp0 ctx.M_type_context.maxL hg, hcentNotM⟩
    let data := facts.element_data g hgOuter
    let N := elementNormalizer15 g
    have hNmax : N ∈ minSimple_max_groups (G := G) := by
      simpa only [N] using
        (mem_uniq_mmax data.unique_maximal_centralizer).1
    have hNtype : FTtype N = 1 := by
      rcases data.type_one_or_two with h1 | h2
      · exact h1
      · exfalso
        apply hnotFrobM
        let frobData := data.typeTwo_frobenius h2
        exact ⟨frobData.complement,
          summaryFrobeniusData_isFrobeniusIn12 frobData⟩
    let ctxN : FTType1Context N := ⟨hNmax, hNtype⟩
    have hNnotFrob :
        ¬ ∃ R : Subgroup G, IsFrobeniusIn (Fitting_core N) R N := by
      rintro ⟨R, hR⟩
      let fctxN : FTFrobeniusContext N := ⟨hNmax, ⟨R, hR⟩⟩
      have hsupp : FTsupport N = FTsupport1 N := by
        calc
          FTsupport N = subgroupNonidentity (Fitting_core N) :=
            FTsupp_Frobenius fctxN
          _ = FTsupport1 N := (FTsupp1_type1 N hNtype).symm
      exact data.support_not_support1.2
        (hsupp ▸ data.support_not_support1.1)
    have hnotLN : ¬ FTAmbientConjugate w.L N := by
      rintro ⟨a, ha⟩
      apply hNnotFrob
      let e : G ≃* G := MulAut.conj a
      have hmap := isFrobeniusIn_map12 hFrobL e
      have hFmap := Fitting_core_map_mulEquiv w.L e
      refine ⟨E.map e.toMonoidHom, ?_⟩
      rw [ha, hFmap]
      exact hmap
    have horthN : FTType1OrthogonalToImages ctxN (nu chi) :=
      coherent_image_orthogonal12 ctxL ctxN hnotLN nu
        (by simpa only [ctxL] using hcoh) hchi
    have hzF : z ∈ Fitting_core N := by
      simpa only [N] using (mem_centralizerWithin.mp hz).1
    have hcomm : g * z = z * g :=
      (mem_centralizerWithin.mp hz).2 g (Subgroup.mem_zpowers g)
    have hgN : g ∈ N :=
      (FTsupp_sub N data.support_not_support1.1).1
    have hgNotF : g ∉ Fitting_core N := by
      intro hgF
      apply data.support_not_support1.2
      rw [FTsupp1_type1 N hNtype]
      exact ⟨hgF, (FTsupp_sub N data.support_not_support1.1).2⟩
    apply FTtype1_ortho_constant ctxN (nu chi) g horthN hgN hgNotF
    exact Set.mem_mul.mpr ⟨g, Set.mem_singleton g, z, hzF, hcomm⟩

private theorem rhoM_shell_structure12
    {p : ℕ} {M P0 : Subgroup G}
    (ctx : FTType1NonFrobeniusContext p M P0)
    (w : NonFrobeniusFTType1Witness p M P0)
    {E : Subgroup G}
    (hFrobL : IsFrobeniusIn (Fitting_core w.L) E w.L)
    (nu : ClassFunction w.L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (hcoh : coherent_with
      (FTType1SeqIndFamily w.L : Set (ClassFunction w.L ℂ))
      (nonidentitySet w.L)
      (FTType1Context.tau ⟨w.L_maximal,
        FT_Frobenius_type1 ⟨w.L_maximal, ⟨E, hFrobL⟩⟩⟩) nu)
    {chi : ClassFunction w.L ℂ}
    (hchi : chi ∈ FTType1SeqIndFamily w.L) :
    (∀ (g : G) (hg : g ∈ subgroupNonidentity (Fitting_core M)),
      ctx.M_type_context.rho (nu chi) ⟨g, Fcore_sub M hg.1⟩ =
        nu chi g) ∧
      (∀ x : G, x ∈ Fitting_core M →
        x ∉ derivedWithin (Fitting_core M) →
        ∀ y : G, y ∈ Fitting_core M →
          y ∉ derivedWithin (Fitting_core M) →
          nu chi x = nu chi y) ∧
      (∀ x : G, x ∈ Fitting_core M →
        x ∉ derivedWithin (Fitting_core M) →
        ∃ a : ℤ, nu chi x = (a : ℂ)) := by
  classical
  let ctxL : FTType1Context w.L :=
    ⟨w.L_maximal,
      FT_Frobenius_type1 ⟨w.L_maximal, ⟨E, hFrobL⟩⟩⟩
  have hnotLM : ¬ FTAmbientConjugate w.L M :=
    fun hLM ↦ witness_maximals_not_conjugate12 ctx w
      (ambient_conjugate_symm12 hLM)
  have horthM : FTType1OrthogonalToImages
      ctx.M_type_context (nu chi) :=
    coherent_image_orthogonal12 ctxL ctx.M_type_context hnotLM nu
      (by simpa only [ctxL] using hcoh) hchi
  have hrho := rhoM_eq_on_fitting_nonidentity12
    ctx w hFrobL nu hcoh hchi
  have hrhoConstant :=
    FtypeI_invDade_ortho_constant ctx.M_type_context (nu chi) horthM
  have hconstant :
      ∀ x : G, x ∈ Fitting_core M →
        x ∉ derivedWithin (Fitting_core M) →
        ∀ y : G, y ∈ Fitting_core M →
          y ∉ derivedWithin (Fitting_core M) →
          nu chi x = nu chi y := by
    intro x hxK hxD y hyK hyD
    have hxne : x ≠ 1 := fun hx1 ↦ hxD (by
      simpa only [hx1] using (derivedWithin (Fitting_core M)).one_mem)
    have hyne : y ≠ 1 := fun hy1 ↦ hyD (by
      simpa only [hy1] using (derivedWithin (Fitting_core M)).one_mem)
    let xM : M := ⟨x, Fcore_sub M hxK⟩
    let yM : M := ⟨y, Fcore_sub M hyK⟩
    calc
      nu chi x = ctx.M_type_context.rho (nu chi) xM :=
        (hrho x ⟨hxK, hxne⟩).symm
      _ = ctx.M_type_context.rho (nu chi) yM :=
        hrhoConstant xM ⟨hxK, hxD⟩ yM ⟨hyK, hyD⟩
      _ = nu chi y := hrho y ⟨hyK, hyne⟩
  refine ⟨hrho, hconstant, ?_⟩
  have hvirtual : ClassFunction.IsVirtual (nu chi) :=
    hcoh.mapsToVirtual chi (AddSubgroup.subset_closure hchi)
  intro x hxK hxD
  apply virtual_shell_value_integer12
    (Fitting_core M) (derivedWithin (Fitting_core M))
    (TypeSpecInternal.derivedWithin_le16_final (Fitting_core M))
    hvirtual hxK hxD
  intro y hyK hyD
  exact hconstant y hyK hyD x hxK hxD

/-! ## Witness position and the second signalizer -/

private theorem witness_x_fitting_position12
    {p : ℕ} {M P0 : Subgroup G}
    (ctx : FTType1NonFrobeniusContext p M P0)
    (w : NonFrobeniusFTType1Witness p M P0) :
    w.x ∈ P0 ∧ w.x ∈ M ∧ w.x ∈ w.L ∧
      w.x ∈ Fitting_core w.L ∧ w.x ∉ Fitting_core M := by
  letI : Fact p.Prime := ⟨ctx.p_prime⟩
  have hxP0 : w.x ∈ P0 :=
    Subgroup.map_subtype_le (omegaOne p P0) w.x_mem_omega
  have hP0M : P0 ≤ M := by
    obtain ⟨PM, hPM⟩ := ctx.sylow_P0
    rw [hPM]
    exact Subgroup.map_subtype_le (PM : Subgroup M)
  have hxFL : w.x ∈ Fitting_core w.L :=
    FTType1NonFrobeniusInternal.p0_le_second_fitting12 ctx w hxP0
  have hxNotFM : w.x ∉ Fitting_core M := by
    intro hxFM
    obtain ⟨a, hP0card⟩ := ctx.sylow_P0.isPGroup.exists_card_eq
    have hcop : Nat.Coprime
        (Nat.card (Fitting_core M)) (Nat.card P0) := by
      rw [hP0card]
      exact ctx.core_p_prime.symm.pow_right a
    have hinter : Fitting_core M ⊓ P0 = ⊥ :=
      Subgroup.inf_eq_bot_of_coprime hcop
    have hxInf : w.x ∈ Fitting_core M ⊓ P0 := ⟨hxFM, hxP0⟩
    rw [hinter] at hxInf
    exact w.x_ne_one (Subgroup.mem_bot.mp hxInf)
  exact ⟨hxP0, hP0M hxP0, Fcore_sub w.L hxFL, hxFL, hxNotFM⟩

private theorem rhoL_eq_psi_on_witness12
    {p : ℕ} {M P0 : Subgroup G}
    (ctx : FTType1NonFrobeniusContext p M P0)
    (w : NonFrobeniusFTType1Witness p M P0)
    (ctxL : FTType1Context w.L)
    (psi : ClassFunction G ℂ)
    (horthM : FTType1OrthogonalToImages ctx.M_type_context psi) :
    (∀ g : G, g ∈ Fitting_core M →
      psi (w.x * g) = psi w.x) ∧
      ctxL.rho psi
          ⟨w.x, Fcore_sub w.L
            (witness_x_fitting_position12 ctx w).2.2.2.1⟩ =
        psi w.x := by
  classical
  obtain ⟨hxP0, hxM, hxL, hxFL, hxNotFM⟩ :=
    witness_x_fitting_position12 ctx w
  have hcoset : ∀ g : G, g ∈ Fitting_core M →
      psi (w.x * g) = psi w.x := by
    intro g hg
    apply FTtype1_ortho_constant ctx.M_type_context psi w.x
      horthM hxM hxNotFM
    exact Set.mem_mul.mpr ⟨w.x, Set.mem_singleton w.x, g, hg, rfl⟩
  refine ⟨hcoset, ?_⟩
  apply type1_rho_of_signalizer_constant12 ctxL psi ⟨hxFL, w.x_ne_one⟩
  intro z hz
  have hxOuter : w.x ∈ outerExceptionalSet w.L (FTsupport0 w.L) :=
    ⟨Fcore_sub_FTsupp0 w.L_maximal ⟨hxFL, w.x_ne_one⟩,
      w.centralizer_not_le_L⟩
  let data :=
    (FTsupport_facts w.L w.L_maximal).element_data w.x hxOuter
  have hcentralizerM : centralizerOfElement8 w.x ≤ M :=
    (Subgroup.centralizer_le_normalizer
      (Subgroup.zpowers w.x : Set G)).trans w.normalizer_le_M
  have hMselected : M = elementNormalizer15 w.x :=
    eq_uniq_mmax data.unique_maximal_centralizer
      ctx.M_type_context.maxL hcentralizerM
  have hzCentral : z ∈ centralizerWithin
      (Fitting_core (elementNormalizer15 w.x))
      (Subgroup.zpowers w.x) := by
    simpa only [FTsignalizer, if_neg w.centralizer_not_le_L] using hz
  have hzK : z ∈ Fitting_core M := by
    simpa only [hMselected] using
      (mem_centralizerWithin.mp hzCentral).1
  have hzx : Commute z w.x :=
    ((mem_centralizerWithin.mp hzCentral).2 w.x
      (Subgroup.mem_zpowers w.x)).symm
  calc
    psi (z * w.x) = psi (w.x * z) := congrArg psi hzx.eq
    _ = psi w.x := hcoset z hzK

/-! ## Arithmetic elimination -/

private theorem odd_divisor_pm_one_half_bound12
    {p e : ℕ} (hp : p.Prime) (hpodd : Odd p) (heodd : Odd e)
    (hdiv : e ∣ p - 1 ∨ e ∣ p + 1) :
    2 * e ≤ p + 1 := by
  have hpgt2 : 2 < p := by
    rcases hpodd with ⟨q, hq⟩
    have hp2 := hp.two_le
    omega
  rcases hpodd with ⟨u, hu⟩
  rcases heodd with ⟨v, hv⟩
  rcases hdiv with hminus | hplus
  · obtain ⟨q, hq⟩ := hminus
    have hq0 : q ≠ 0 := by
      intro hzero
      subst q
      simp only [mul_zero] at hq
      omega
    have hq1 : q ≠ 1 := by
      intro hone
      subst q
      simp only [mul_one] at hq
      omega
    have hq2 : 2 ≤ q := by omega
    have hle : 2 * e ≤ p - 1 := by
      calc
        2 * e = e * 2 := Nat.mul_comm 2 e
        _ ≤ e * q := Nat.mul_le_mul_left e hq2
        _ = p - 1 := hq.symm
    omega
  · obtain ⟨q, hq⟩ := hplus
    have hq0 : q ≠ 0 := by
      intro hzero
      subst q
      simp only [mul_zero] at hq
      omega
    have hq1 : q ≠ 1 := by
      intro hone
      subst q
      simp only [mul_one] at hq
      omega
    have hq2 : 2 ≤ q := by omega
    calc
      2 * e = e * 2 := Nat.mul_comm 2 e
      _ ≤ e * q := Nat.mul_le_mul_left e hq2
      _ = p + 1 := hq.symm

private theorem dade_coefficient_zero12
    {p e h : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hepos : 0 < e) (heBound : 2 * e ≤ p + 1)
    (hhBound : p ^ 2 ≤ h) (a : ℤ)
    (haBound :
      (a : ℝ) ^ 2 * (((h : ℝ) - 1) / (e : ℝ)) -
          2 * (a : ℝ) ≤ (e : ℝ) - 1) :
    a = 0 := by
  by_contra ha0
  have hpgt2 : 2 < p := by
    rcases hpodd with ⟨q, hq⟩
    have hp2 := hp.two_le
    omega
  have hpReal : (3 : ℝ) ≤ p := by exact_mod_cast hpgt2
  have heReal : (0 : ℝ) < e := by exact_mod_cast hepos
  have heBoundReal : (2 : ℝ) * e ≤ p + 1 := by exact_mod_cast heBound
  have hhBoundReal : (p : ℝ) ^ 2 ≤ h := by exact_mod_cast hhBound
  have heSuccBound : (2 : ℝ) * ((e : ℝ) + 1) ≤ p + 3 := by
    linarith
  have hproduct :
      ((2 : ℝ) * e) * (2 * (e + 1)) ≤ (p + 1) * (p + 3) :=
    mul_le_mul heBoundReal heSuccBound (by positivity) (by positivity)
  have hpProduct :
      ((p : ℝ) + 1) * (p + 3) < 4 * (p ^ 2 - 1) := by
    nlinarith
  have heh : (e : ℝ) * (e + 1) < (h : ℝ) - 1 := by
    nlinarith
  have haSqInt : (1 : ℤ) ≤ a ^ 2 := by
    rw [one_le_sq_iff_one_le_abs]
    exact Int.one_le_abs ha0
  have haSq : (1 : ℝ) ≤ (a : ℝ) ^ 2 := by exact_mod_cast haSqInt
  have haSqPos : (0 : ℝ) < (a : ℝ) ^ 2 :=
    lt_of_lt_of_le zero_lt_one haSq
  have hstrict := mul_lt_mul_of_pos_left heh haSqPos
  have hshape :
      (e : ℝ) * (e - 1 + 2 * (a : ℝ)) ≤
        e * ((e + 1) * (a : ℝ) ^ 2) := by
    have hnonneg :
        0 ≤ (e : ℝ) * ((a : ℝ) ^ 2 - 1) +
          ((a : ℝ) - 1) ^ 2 := by positivity
    nlinarith
  have haClear :
      (a : ℝ) ^ 2 * ((h : ℝ) - 1) ≤
        ((e : ℝ) - 1 + 2 * (a : ℝ)) * e := by
    have hrearranged :
        ((a : ℝ) ^ 2 * ((h : ℝ) - 1)) / e ≤
          (e : ℝ) - 1 + 2 * (a : ℝ) := by
      calc
        ((a : ℝ) ^ 2 * ((h : ℝ) - 1)) / e =
            (a : ℝ) ^ 2 * (((h : ℝ) - 1) / e) := by ring
        _ ≤ (e : ℝ) - 1 + 2 * (a : ℝ) := by linarith
    exact (div_le_iff₀ heReal).mp hrearranged
  nlinarith

/-! ## Bounding the reciprocal-Dade coefficient -/

private theorem dade_ind1_coefficient_bound12
    {L : Subgroup G} (H : Subgroup L) [H.Normal]
    (dd : DadeHypothesis (⊤ : Subgroup G) L
      (subgroupNonidentity (H.map L.subtype)))
    (nuTop : ClassFunction L ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup G) ℂ)
    (hcoh : coherent_with
      (↑(seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥) :
        Set (ClassFunction L ℂ))
      (nonidentitySet L) (Dade dd) nuTop)
    (zeta : IrreducibleCharacter L ℂ)
    (hzeta : (zeta : ClassFunction L ℂ) ∈
      seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥)
    (hzeta1 : zeta 1 = (H.index : ℂ))
    (hself : ∀ {xi : ClassFunction L ℂ},
      xi ∈ seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥ →
        characterPairing xi xi = 1)
    (data : DadeInd1SubLinConclusion H dd nuTop zeta) :
    (data.coefficient : ℝ) ^ 2 *
          (((Nat.card H : ℝ) - 1) / (H.index : ℝ)) -
        2 * (data.coefficient : ℝ) ≤
      (H.index : ℝ) - 1 := by
  classical
  letI : Invertible (Nat.card L : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card H : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card (⊤ : Subgroup G) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let calS : Finset (ClassFunction L ℂ) :=
    seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥
  let ind1 : ClassFunction L ℂ := dadeInducedTrivial H
  let psi : ClassFunction (⊤ : Subgroup G) ℂ :=
    nuTop (zeta : ClassFunction L ℂ)
  let beta : ClassFunction (⊤ : Subgroup G) ℂ :=
    dadeInd1Beta H dd (zeta : ClassFunction L ℂ)
  let sumS : ClassFunction (⊤ : Subgroup G) ℂ :=
    dadeInd1CoherentSum H nuTop
  let oneTop : ClassFunction (⊤ : Subgroup G) ℂ :=
    ((IrreducibleCharacter.trivial :
      IrreducibleCharacter (⊤ : Subgroup G) ℂ) :
        ClassFunction (⊤ : Subgroup G) ℂ)
  let a : ℤ := data.coefficient
  have hsupportEq :
      {x : L | (x : G) ∈ subgroupNonidentity (H.map L.subtype)} =
        subgroupNonidentity H := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, hyx⟩, hx1⟩
      have hyxL : y = x := Subtype.ext hyx
      subst x
      exact ⟨hy, fun hy1 ↦ hx1 (by
        simpa using congrArg Subtype.val hy1)⟩
    · rintro ⟨hxH, hx1⟩
      refine ⟨⟨x, hxH, rfl⟩, ?_⟩
      intro hxG
      exact hx1 (Subtype.ext hxG)
  have hmemClosure {xi : ClassFunction L ℂ} (hxi : xi ∈ calS) :
      xi ∈ AddSubgroup.closure
        (↑calS : Set (ClassFunction L ℂ)) :=
    AddSubgroup.subset_closure hxi
  have hnuVirtual {xi : ClassFunction L ℂ} (hxi : xi ∈ calS) :
      ClassFunction.IsVirtual (nuTop xi) :=
    hcoh.mapsToVirtual xi (hmemClosure hxi)
  have hnuPair {xi mu : ClassFunction L ℂ}
      (hxi : xi ∈ calS) (hmu : mu ∈ calS) :
      starCharacterPairing (nuTop xi) (nuTop mu) =
        characterPairing xi mu := by
    rw [FTType1InfrastructureInternal.starPairingEqPairingOfRightVirtual
      (nuTop xi) (hnuVirtual hmu)]
    exact hcoh.isometry xi (hmemClosure hxi) mu (hmemClosure hmu)
  have horth : Set.Pairwise
      (↑calS : Set (ClassFunction L ℂ))
      (fun xi mu ↦ characterPairing xi mu = 0) :=
    seqInd_orthogonal H _
  have hnuNorm {xi : ClassFunction L ℂ} (hxi : xi ∈ calS) :
      classFunctionNormSq (nuTop xi) = 1 := by
    rw [classFunctionNormSq_eq_re_starCharacterPairing,
      hnuPair hxi hxi, hself hxi]
    norm_num
  have hindT : ind1 ∈ seqIndT (k := ℂ) H :=
    mem_seqIndT H IrreducibleCharacter.trivial
  have hindValue {x : L} (hx : x ∈ H) :
      ind1 x = (H.index : ℂ) := by
    unfold ind1 dadeInducedTrivial
    rw [ClassFunction.induce_apply_formula]
    have hconj (y : L) : y⁻¹ * x * y ∈ H := by
      simpa only [inv_inv] using
        (inferInstance : H.Normal).conj_mem x hx y⁻¹
    simp_rw [dif_pos (hconj _)]
    simp only [IrreducibleCharacter.trivial_apply, Finset.sum_const,
      nsmul_eq_mul, mul_one, Finset.card_univ]
    rw [← Nat.card_eq_fintype_card]
    have hHcard : (Nat.card H : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hcard :
        (H.index : ℂ) * (Nat.card H : ℂ) =
          (Nat.card L : ℂ) := by
      exact_mod_cast H.index_mul_card
    rw [← hcard]
    field_simp [hHcard]
  have hindVirtual : ClassFunction.IsVirtual ind1 :=
    seqInd_vcharW H hindT
  have hindSelf : starCharacterPairing ind1 ind1 = (H.index : ℂ) := by
    rw [FTType1InfrastructureInternal.starPairingEqPairingOfRightVirtual
      ind1 hindVirtual]
    unfold ind1 dadeInducedTrivial
    rw [ClassFunction.frobeniusReciprocity H]
    have hrestrict :
        ClassFunction.restrict H
            (ClassFunction.induce H
              ((IrreducibleCharacter.trivial :
                IrreducibleCharacter H ℂ) : ClassFunction H ℂ)) =
          (H.index : ℂ) •
            ((IrreducibleCharacter.trivial :
              IrreducibleCharacter H ℂ) : ClassFunction H ℂ) := by
      apply ClassFunction.ext
      intro x
      simpa only [ClassFunction.restrict_apply, ClassFunction.smul_apply,
        IrreducibleCharacter.trivial_apply, smul_eq_mul, mul_one,
        ind1, dadeInducedTrivial] using
          (hindValue (x := (x : L)) x.property)
    rw [hrestrict, characterPairing_smul_right,
      IrreducibleCharacter.characterPairing_self, mul_one]
  have hzetaVirtual : ClassFunction.IsVirtual
      (zeta : ClassFunction L ℂ) :=
    FTType1InfrastructureInternal.irreducibleIsVirtual zeta
  have hzetaSelf :
      starCharacterPairing (zeta : ClassFunction L ℂ) zeta = 1 := by
    rw [FTType1InfrastructureInternal.starPairingEqPairingOfRightVirtual
      (zeta : ClassFunction L ℂ) hzetaVirtual,
      zeta.characterPairing_self]
  have hzetaInd :
      starCharacterPairing (zeta : ClassFunction L ℂ) ind1 = 0 := by
    rw [FTType1InfrastructureInternal.starPairingEqPairingOfRightVirtual
      (zeta : ClassFunction L ℂ) hindVirtual]
    exact seqInd_ortho_Ind1 H (⊤ : Subgroup H) ⊥ hzeta
  have hindZeta :
      starCharacterPairing ind1 (zeta : ClassFunction L ℂ) = 0 := by
    rw [starCharacterPairing_conj_symm, hzetaInd]
    simp
  let alpha : ClassFunction L ℂ := ind1 - (zeta : ClassFunction L ℂ)
  have halphaOn : alpha ∈ ClassFunction.supportedOn
      {x : L | (x : G) ∈ subgroupNonidentity (H.map L.subtype)} := by
    rw [hsupportEq]
    exact cfInd1_sub_lin_on H (seqInd_subT H _ hzeta) hzeta1
  have halphaSelf :
      starCharacterPairing alpha alpha = (H.index : ℂ) + 1 := by
    unfold alpha
    rw [starPairing_sub_left12, starPairing_sub_right12,
      starPairing_sub_right12, hindSelf, hindZeta, hzetaInd, hzetaSelf]
    ring
  have hbetaSelf : starCharacterPairing beta beta =
      (H.index : ℂ) + 1 := by
    change starCharacterPairing (Dade dd alpha) (Dade dd alpha) = _
    rw [Dade_isometry dd alpha alpha halphaOn halphaOn, halphaSelf]
  have honeVirtual : ClassFunction.IsVirtual oneTop :=
    FTType1InfrastructureInternal.irreducibleIsVirtual
      (IrreducibleCharacter.trivial :
        IrreducibleCharacter (⊤ : Subgroup G) ℂ)
  have honeSelf : starCharacterPairing oneTop oneTop = 1 := by
    rw [FTType1InfrastructureInternal.starPairingEqPairingOfRightVirtual
      oneTop honeVirtual,
      IrreducibleCharacter.characterPairing_self]
  have honeBeta : starCharacterPairing oneTop beta = 1 := by
    calc
      starCharacterPairing oneTop beta =
          star (starCharacterPairing beta oneTop) :=
        starCharacterPairing_conj_symm oneTop beta
      _ = 1 := by rw [data.beta_pairing_one]; simp
  have hbetaMinusOneNorm :
      classFunctionNormSq (beta - oneTop) = (H.index : ℝ) := by
    have hpair : starCharacterPairing (beta - oneTop) (beta - oneTop) =
        (H.index : ℂ) := by
      rw [starPairing_sub_left12, starPairing_sub_right12,
        starPairing_sub_right12, hbetaSelf, data.beta_pairing_one,
        honeBeta, honeSelf]
      ring
    have hcast := starCharacterPairing_self_eq_classFunctionNormSq
      (beta - oneTop)
    rw [hpair] at hcast
    exact_mod_cast hcast.symm
  have hpsiNorm : classFunctionNormSq psi = 1 := hnuNorm hzeta
  have hpsiSum : starCharacterPairing psi sumS = 1 := by
    unfold psi sumS dadeInd1CoherentSum
    rw [starPairing_sum_right12]
    rw [Finset.sum_eq_single (zeta : ClassFunction L ℂ)]
    · rw [starCharacterPairing_smul_right, hnuPair hzeta hzeta,
        hself hzeta, hzeta1]
      have hindexNe : (H.index : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr H.index_ne_zero_of_finite
      simp [hindexNe]
    · intro xi hxi hne
      rw [starCharacterPairing_smul_right, hnuPair hzeta hxi,
        horth hzeta hxi hne.symm, mul_zero]
    · intro hzetaNot
      exact (hzetaNot hzeta).elim
  have hsumPsi : starCharacterPairing sumS psi = 1 := by
    calc
      starCharacterPairing sumS psi =
          star (starCharacterPairing psi sumS) :=
        starCharacterPairing_conj_symm sumS psi
      _ = 1 := by rw [hpsiSum]; simp
  have hdegreeSumComplex :
      (∑ xi ∈ calS, xi 1 ^ 2) =
        (H.index : ℂ) * ((Nat.card H : ℂ) - 1) := by
    calc
      (∑ xi ∈ calS, xi 1 ^ 2) =
          ∑ xi ∈ calS, xi 1 ^ 2 / characterPairing xi xi := by
        apply Finset.sum_congr rfl
        intro xi hxi
        rw [hself hxi, div_one]
      _ = (H.index : ℂ) * ((Nat.card H : ℂ) - 1) := by
        simpa only [calS] using sum_seqIndC1_square (k := ℂ) H
  have hdegreeNormSum :
      (∑ xi ∈ calS, Complex.normSq (xi 1)) =
        (H.index : ℝ) * ((Nat.card H : ℝ) - 1) := by
    calc
      (∑ xi ∈ calS, Complex.normSq (xi 1)) =
          ∑ xi ∈ calS, (xi 1 ^ 2).re := by
        apply Finset.sum_congr rfl
        intro xi hxi
        obtain ⟨n, hn⟩ := Cnat_seqInd1 H (seqInd_subT H _ hxi)
        rw [hn, Complex.normSq_natCast]
        norm_num [pow_two, Complex.mul_re]
      _ = (∑ xi ∈ calS, xi 1 ^ 2).re := by simp
      _ = (H.index : ℝ) * ((Nat.card H : ℝ) - 1) := by
        rw [hdegreeSumComplex]
        norm_num
  have hsumNorm :
      classFunctionNormSq sumS =
        ((Nat.card H : ℝ) - 1) / (H.index : ℝ) := by
    unfold sumS dadeInd1CoherentSum
    rw [normSq_sum_pairwise12]
    · calc
        (∑ xi ∈ calS,
            classFunctionNormSq
              ((xi 1 / (H.index : ℂ) /
                characterPairing xi xi) • nuTop xi)) =
            ∑ xi ∈ calS,
              Complex.normSq (xi 1 / (H.index : ℂ)) := by
          apply Finset.sum_congr rfl
          intro xi hxi
          rw [normSq_smul12, hnuNorm hxi, mul_one,
            hself hxi, div_one]
        _ = ((H.index : ℝ) ^ 2)⁻¹ *
            (∑ xi ∈ calS, Complex.normSq (xi 1)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro xi _
          rw [div_eq_mul_inv, Complex.normSq_mul,
            Complex.normSq_inv, Complex.normSq_natCast]
          ring
        _ = ((Nat.card H : ℝ) - 1) / (H.index : ℝ) := by
          rw [hdegreeNormSum]
          have heNat : 0 < H.index :=
            Nat.pos_of_ne_zero H.index_ne_zero_of_finite
          have he : (0 : ℝ) < H.index := by exact_mod_cast heNat
          field_simp [he.ne']
    · intro xi hxi mu hmu hne
      rw [starCharacterPairing_smul_left,
        starCharacterPairing_smul_right, hnuPair hxi hmu,
        horth hxi hmu hne, mul_zero, mul_zero]
  let v : ClassFunction (⊤ : Subgroup G) ℂ :=
    -psi + (a : ℂ) • sumS
  have hvNorm : classFunctionNormSq v =
      1 + (a : ℝ) ^ 2 *
          (((Nat.card H : ℝ) - 1) / (H.index : ℝ)) -
        2 * (a : ℝ) := by
    exact normSq_affine_integer12
      psi sumS a _ hpsiNorm hsumNorm hpsiSum hsumPsi
  have hsumGamma : starCharacterPairing sumS data.gamma = 0 := by
    unfold sumS dadeInd1CoherentSum
    rw [starPairing_sum_left12]
    apply Finset.sum_eq_zero
    intro xi hxi
    rw [starCharacterPairing_smul_left,
      data.image_orthogonal_gamma xi hxi, mul_zero]
  have hvGamma : starCharacterPairing v data.gamma = 0 := by
    unfold v
    rw [← neg_one_smul ℂ psi,
      starCharacterPairing_add_left,
      starCharacterPairing_smul_left,
      starCharacterPairing_smul_left,
      data.image_orthogonal_gamma (zeta : ClassFunction L ℂ) hzeta,
      hsumGamma]
    simp
  have hdecomp : beta - oneTop = v + data.gamma := by
    have hd := data.decomposition
    change beta = oneTop - psi + (a : ℂ) • sumS + data.gamma at hd
    rw [hd]
    unfold v
    abel
  have hvUpper : classFunctionNormSq v ≤ (H.index : ℝ) := by
    have hsplit : classFunctionNormSq (beta - oneTop) =
        classFunctionNormSq v + classFunctionNormSq data.gamma := by
      rw [hdecomp, normSq_add_of_star_orthogonal12 _ _ hvGamma]
    rw [hbetaMinusOneNorm] at hsplit
    nlinarith [classFunctionNormSq_nonneg data.gamma]
  simpa only [a] using (show
    (a : ℝ) ^ 2 *
          (((Nat.card H : ℝ) - 1) / (H.index : ℝ)) -
        2 * (a : ℝ) ≤ (H.index : ℝ) - 1 by
    rw [hvNorm] at hvUpper
    linarith)

private def type1FittingDadeHyp12
    (L : Subgroup G) (hL : L ∈ minSimple_max_groups (G := G)) :
    DadeHypothesis (⊤ : Subgroup G) L
      (subgroupNonidentity ((FTType1FittingIn L).map L.subtype)) := by
  simpa only [FTType1FittingIn,
    Subgroup.map_subgroupOf_eq_of_le (Fcore_sub L)] using
      FT_DadeF_hyp L hL

private theorem second_dade_coefficient_zero12
    {p : ℕ} {M P0 : Subgroup G}
    (ctx : FTType1NonFrobeniusContext p M P0)
    (w : NonFrobeniusFTType1Witness p M P0)
    {E : Subgroup G}
    (hFrobL : IsFrobeniusIn (Fitting_core w.L) E w.L)
    (hdiv : Nat.card E ∣ p - 1 ∨ Nat.card E ∣ p + 1)
    (nu : ClassFunction w.L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (hcoh : coherent_with
      (FTType1SeqIndFamily w.L : Set (ClassFunction w.L ℂ))
      (nonidentitySet w.L)
      (FTType1Context.tau ⟨w.L_maximal,
        FT_Frobenius_type1 ⟨w.L_maximal, ⟨E, hFrobL⟩⟩⟩) nu)
    (zeta : IrreducibleCharacter w.L ℂ)
    (hzeta : (zeta : ClassFunction w.L ℂ) ∈
      FTType1SeqIndFamily w.L)
    (hzeta1 : zeta 1 = ((FTType1FittingIn w.L).index : ℂ))
    (data : DadeInd1SubLinConclusion
      (FTType1FittingIn w.L)
      (type1FittingDadeHyp12 w.L w.L_maximal)
      (characterSourceMap12.comp nu) zeta) :
    data.coefficient = 0 := by
  classical
  letI : Invertible (Nat.card w.L : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let fctxL : FTFrobeniusContext w.L :=
    ⟨w.L_maximal, ⟨E, hFrobL⟩⟩
  let ctxL : FTType1Context w.L :=
    ⟨w.L_maximal, FT_Frobenius_type1 fctxL⟩
  let H : Subgroup w.L := FTType1FittingIn w.L
  let dd := type1FittingDadeHyp12 w.L w.L_maximal
  let nuTop : ClassFunction w.L ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup G) ℂ :=
    characterSourceMap12.comp nu
  letI : H.Normal := by
    simpa only [H, FTType1FittingIn] using Fcore_normal w.L
  have hcohTop : coherent_with
      (↑(seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥) :
        Set (ClassFunction w.L ℂ))
      (nonidentitySet w.L) (Dade dd) nuTop := by
    simpa only [H, dd, nuTop, FTType1SeqIndFamily, ctxL,
      type1FittingDadeHyp12, FTType1FittingIn,
      Subgroup.map_subgroupOf_eq_of_le (Fcore_sub w.L)] using
      type1_fitting_coherence_top12 ctxL nu
        (by simpa only [ctxL, fctxL] using hcoh)
  have hzetaS : (zeta : ClassFunction w.L ℂ) ∈
      seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥ := by
    simpa only [H, FTType1SeqIndFamily] using hzeta
  have hself {xi : ClassFunction w.L ℂ}
      (hxi : xi ∈ seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥) :
      characterPairing xi xi = 1 := by
    let xiIrr : IrreducibleCharacter w.L ℂ :=
      ⟨xi, (FT_Frobenius_coherence fctxL).seqInd_irreducible xi (by
        simpa only [H, FTType1SeqIndFamily] using hxi)⟩
    exact xiIrr.characterPairing_self
  have haBound :
      (data.coefficient : ℝ) ^ 2 *
          (((Nat.card H : ℝ) - 1) / (H.index : ℝ)) -
        2 * (data.coefficient : ℝ) ≤
      (H.index : ℝ) - 1 := by
    simpa only [H, dd, nuTop] using
      dade_ind1_coefficient_bound12 H dd nuTop hcohTop zeta
        hzetaS (by simpa only [H] using hzeta1) hself data
  have hEL : E ≤ w.L := le_sup_right.trans_eq hFrobL.1
  have hFrobHE : IsFrobeniusDecomposition H (E.subgroupOf w.L) :=
    frobeniusIn_decomposition12 hFrobL
  have hindex : H.index = Nat.card E :=
    hFrobHE.isComplement.symm.index_eq_card.trans
      (Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hEL)
  have hpodd : Odd p := by
    obtain ⟨A, hAP0, hA⟩ := w.P0_rank_two.1
    have hpA : p ∣ Nat.card A := by
      rw [hA.card_eq]
      exact dvd_pow_self p (by omega : 2 ≠ 0)
    exact Odd.of_dvd_nat (mFT_odd A) hpA
  have heodd : Odd (Nat.card E) := mFT_odd E
  have heBound : 2 * Nat.card E ≤ p + 1 :=
    odd_divisor_pm_one_half_bound12 ctx.p_prime hpodd heodd hdiv
  have hhBound : p ^ 2 ≤ Nat.card H := by
    obtain ⟨A, hAP0, hA⟩ := w.P0_rank_two.1
    have hAH : A ≤ Fitting_core w.L :=
      hAP0.trans
        (FTType1NonFrobeniusInternal.p0_le_second_fitting12 ctx w)
    have hdvd : p ^ 2 ∣ Nat.card (Fitting_core w.L) := by
      rw [← hA.card_eq]
      exact Subgroup.card_dvd_of_le hAH
    rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
      (Fcore_sub w.L)]
    exact Nat.le_of_dvd Nat.card_pos hdvd
  apply dade_coefficient_zero12 ctx.p_prime hpodd Nat.card_pos
    heBound hhBound data.coefficient
  simpa only [hindex] using haBound

/-! ## Recovering a coherent value after coefficient vanishing -/

private theorem invDade_coherent_value_of_coefficient_zero12
    {L : Subgroup G} (H : Subgroup L) [H.Normal]
    (dd : DadeHypothesis (⊤ : Subgroup G) L
      (subgroupNonidentity (H.map L.subtype)))
    (nuTop : ClassFunction L ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup G) ℂ)
    (hcoh : coherent_with
      (↑(seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥) :
        Set (ClassFunction L ℂ))
      (nonidentitySet L) (Dade dd) nuTop)
    (zeta : IrreducibleCharacter L ℂ)
    (hzeta : (zeta : ClassFunction L ℂ) ∈
      seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥)
    (hzeta1 : zeta 1 = (H.index : ℂ))
    (hself : ∀ {xi : ClassFunction L ℂ},
      xi ∈ seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥ →
        characterPairing xi xi = 1)
    (data : DadeInd1SubLinConclusion H dd nuTop zeta)
    (hcoeff : data.coefficient = 0)
    (x : L)
    (hx : (x : G) ∈ subgroupNonidentity (H.map L.subtype)) :
    invDade dd (nuTop (zeta : ClassFunction L ℂ)) x = zeta x := by
  classical
  letI : Invertible (Nat.card L : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card H : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card (⊤ : Subgroup G) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let calS : Finset (ClassFunction L ℂ) :=
    seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥
  let calT : Finset (ClassFunction L ℂ) := seqIndT (k := ℂ) H
  let ind1 : ClassFunction L ℂ := dadeInducedTrivial H
  let psiTop : ClassFunction (⊤ : Subgroup G) ℂ :=
    nuTop (zeta : ClassFunction L ℂ)
  let beta : ClassFunction (⊤ : Subgroup G) ℂ :=
    dadeInd1Beta H dd (zeta : ClassFunction L ℂ)
  have hmemClosure {xi : ClassFunction L ℂ} (hxi : xi ∈ calS) :
      xi ∈ AddSubgroup.closure
        (↑calS : Set (ClassFunction L ℂ)) :=
    AddSubgroup.subset_closure hxi
  have hnuVirtual {xi : ClassFunction L ℂ} (hxi : xi ∈ calS) :
      ClassFunction.IsVirtual (nuTop xi) :=
    hcoh.mapsToVirtual xi (hmemClosure hxi)
  have hnuPair {xi mu : ClassFunction L ℂ}
      (hxi : xi ∈ calS) (hmu : mu ∈ calS) :
      starCharacterPairing (nuTop xi) (nuTop mu) =
        characterPairing xi mu := by
    rw [FTType1InfrastructureInternal.starPairingEqPairingOfRightVirtual
      (nuTop xi) (hnuVirtual hmu)]
    exact hcoh.isometry xi (hmemClosure hxi) mu (hmemClosure hmu)
  have horth : Set.Pairwise
      (↑calS : Set (ClassFunction L ℂ))
      (fun xi mu ↦ characterPairing xi mu = 0) :=
    seqInd_orthogonal H _
  have hpsiSelf : starCharacterPairing psiTop psiTop = 1 := by
    rw [hnuPair hzeta hzeta, hself hzeta]
  have hzetaStarSelf :
      starCharacterPairing (zeta : ClassFunction L ℂ) zeta = 1 := by
    rw [FTType1InfrastructureInternal.starPairingEqPairingOfRightVirtual
      (zeta : ClassFunction L ℂ)
      (FTType1InfrastructureInternal.irreducibleIsVirtual zeta),
      hself hzeta]
  let oneTop : ClassFunction (⊤ : Subgroup G) ℂ :=
    ((IrreducibleCharacter.trivial :
      IrreducibleCharacter (⊤ : Subgroup G) ℂ) :
        ClassFunction (⊤ : Subgroup G) ℂ)
  have hpsiOne : starCharacterPairing psiTop oneTop = 0 :=
    data.image_orthogonal_one (zeta : ClassFunction L ℂ) hzeta
  have honePsi : starCharacterPairing oneTop psiTop = 0 := by
    rw [starCharacterPairing_conj_symm, hpsiOne]
    simp
  have hpsiGamma : starCharacterPairing psiTop data.gamma = 0 :=
    data.image_orthogonal_gamma (zeta : ClassFunction L ℂ) hzeta
  have hgammaPsi : starCharacterPairing data.gamma psiTop = 0 := by
    rw [starCharacterPairing_conj_symm, hpsiGamma]
    simp
  have hbetaPsi : starCharacterPairing beta psiTop = -1 := by
    have hd := data.decomposition
    change beta = oneTop - psiTop + (data.coefficient : ℂ) •
      dadeInd1CoherentSum H nuTop + data.gamma at hd
    rw [hd, hcoeff]
    simp only [Int.cast_zero, zero_smul, add_zero]
    rw [starCharacterPairing_add_left, starPairing_sub_left12,
      honePsi, hpsiSelf, hgammaPsi]
    ring
  have hindT : ind1 ∈ calT :=
    mem_seqIndT H IrreducibleCharacter.trivial
  have hindNotS : ind1 ∉ calS := by
    rw [show calS = calT.erase ind1 by
      simpa only [calS, calT, ind1, dadeInducedTrivial] using
        seqIndC1_rem (k := ℂ) H]
    simp
  have hcalTsplit : calT = insert ind1 calS := by
    calc
      calT = insert ind1 (calT.erase ind1) :=
        (Finset.insert_erase hindT).symm
      _ = insert ind1 calS := by
        rw [show calS = calT.erase ind1 by
          simpa only [calS, calT, ind1, dadeInducedTrivial] using
            seqIndC1_rem (k := ℂ) H]
  have hexp := invDade_seqInd_sum H dd ind1 calS psiTop
    hcalTsplit hindNotS
  have hindOne : ind1 1 = (H.index : ℂ) := by
    unfold ind1 dadeInducedTrivial
    rw [ClassFunction.induce_one]
    simp [IrreducibleCharacter.trivial_apply]
  have hindexNe : (H.index : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr H.index_ne_zero_of_finite
  have hcZeta : invDadeSeqIndCoefficient dd ind1 psiTop
      (zeta : ClassFunction L ℂ) = 1 := by
    unfold invDadeSeqIndCoefficient invDadeSeqIndAdjusted
    rw [hindOne, hzeta1, div_self hindexNe, one_smul]
    have hneg :
        (zeta : ClassFunction L ℂ) - ind1 =
          -(ind1 - (zeta : ClassFunction L ℂ)) := by abel
    rw [hneg, map_neg]
    change starCharacterPairing (-beta) psiTop = 1
    rw [← neg_one_smul ℂ beta,
      starCharacterPairing_smul_left, hbetaPsi]
    norm_num
  have hcOther {xi : ClassFunction L ℂ}
      (hxi : xi ∈ calS)
      (hxiNe : xi ≠ (zeta : ClassFunction L ℂ)) :
      invDadeSeqIndCoefficient dd ind1 psiTop xi = 0 := by
    let q : ℂ := xi 1 / (H.index : ℂ)
    let pi : ClassFunction L ℂ :=
      xi - q • (zeta : ClassFunction L ℂ)
    let alpha : ClassFunction L ℂ :=
      ind1 - (zeta : ClassFunction L ℂ)
    have hpiClosure : pi ∈ AddSubgroup.closure
        (↑calS : Set (ClassFunction L ℂ)) := by
      obtain ⟨n, hn⟩ := dvd_index_seqInd1 H (seqInd_subT H _ hxi)
      unfold pi q
      rw [hn]
      refine (AddSubgroup.closure
        (↑calS : Set (ClassFunction L ℂ))).sub_mem
          (hmemClosure hxi) ?_
      have hm := (AddSubgroup.closure
        (↑calS : Set (ClassFunction L ℂ))).nsmul_mem
          (hmemClosure hzeta) n
      rw [← Nat.cast_smul_eq_nsmul (R := ℂ) n
        (zeta : ClassFunction L ℂ)] at hm
      exact hm
    have hpiOn : pi ∈
        ClassFunction.supportedOn (nonidentitySet L) := by
      rw [ClassFunction.mem_supportedOn_iff]
      intro y hy
      have hy1 : y = 1 := by
        simpa [nonidentitySet] using not_not.mp hy
      subst y
      unfold pi q
      simp [hzeta1, hindexNe]
    have hagree : Dade dd pi = nuTop pi :=
      (hcoh.agrees pi hpiClosure hpiOn).symm
    have hadjusted : invDadeSeqIndAdjusted ind1 xi = pi - q • alpha := by
      unfold invDadeSeqIndAdjusted pi q alpha
      rw [hindOne]
      module
    have hpiPair : starCharacterPairing (nuTop pi) psiTop = -q := by
      unfold pi psiTop
      rw [map_sub, map_smul, starPairing_sub_left12,
        starCharacterPairing_smul_left,
        hnuPair hxi hzeta, horth hxi hzeta hxiNe,
        hnuPair hzeta hzeta, hself hzeta]
      ring
    unfold invDadeSeqIndCoefficient
    rw [hadjusted, map_sub, map_smul, hagree,
      starPairing_sub_left12, starCharacterPairing_smul_left]
    change starCharacterPairing (nuTop pi) psiTop -
      q * starCharacterPairing beta psiTop = 0
    rw [hpiPair, hbetaPsi]
    ring
  rw [hexp.value_on_support x hx]
  rw [Finset.sum_eq_single (zeta : ClassFunction L ℂ)]
  · rw [hcZeta, hzetaStarSelf]
    simp
  · intro xi hxi hxiNe
    rw [hcOther hxi hxiNe]
    simp
  · intro hzetaNot
    exact (hzetaNot hzeta).elim

/-! ## The coherent value on the witness coset -/

private theorem rhoL_coherent_value12
    {p : ℕ} {M P0 : Subgroup G}
    (ctx : FTType1NonFrobeniusContext p M P0)
    (w : NonFrobeniusFTType1Witness p M P0)
    {E : Subgroup G}
    (hFrobL : IsFrobeniusIn (Fitting_core w.L) E w.L)
    (hdiv : Nat.card E ∣ p - 1 ∨ Nat.card E ∣ p + 1)
    (nu : ClassFunction w.L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (hcoh : coherent_with
      (FTType1SeqIndFamily w.L : Set (ClassFunction w.L ℂ))
      (nonidentitySet w.L)
      (FTType1Context.tau ⟨w.L_maximal,
        FT_Frobenius_type1 ⟨w.L_maximal, ⟨E, hFrobL⟩⟩⟩) nu)
    (zeta : IrreducibleCharacter w.L ℂ)
    (hzeta : (zeta : ClassFunction w.L ℂ) ∈
      FTType1SeqIndFamily w.L)
    (hzeta1 : zeta 1 = ((FTType1FittingIn w.L).index : ℂ)) :
    let fctxL : FTFrobeniusContext w.L :=
      ⟨w.L_maximal, ⟨E, hFrobL⟩⟩
    let ctxL : FTType1Context w.L :=
      ⟨w.L_maximal, FT_Frobenius_type1 fctxL⟩
    (∀ g : G, g ∈ Fitting_core M →
      nu zeta (w.x * g) = zeta ⟨w.x,
        (witness_x_fitting_position12 ctx w).2.2.1⟩) ∧
      ctxL.rho (nu zeta)
          ⟨w.x, Fcore_sub w.L
            (witness_x_fitting_position12 ctx w).2.2.2.1⟩ =
        zeta ⟨w.x, (witness_x_fitting_position12 ctx w).2.2.1⟩ := by
  classical
  dsimp only
  letI : Invertible (Nat.card w.L : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let fctxL : FTFrobeniusContext w.L :=
    ⟨w.L_maximal, ⟨E, hFrobL⟩⟩
  let ctxL : FTType1Context w.L :=
    ⟨w.L_maximal, FT_Frobenius_type1 fctxL⟩
  let H : Subgroup w.L := FTType1FittingIn w.L
  let dd := type1FittingDadeHyp12 w.L w.L_maximal
  let nuTop : ClassFunction w.L ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup G) ℂ :=
    characterSourceMap12.comp nu
  letI : H.Normal := by
    simpa only [H, FTType1FittingIn] using Fcore_normal w.L
  have hcohTop : coherent_with
      (↑(seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥) :
        Set (ClassFunction w.L ℂ))
      (nonidentitySet w.L) (Dade dd) nuTop := by
    simpa only [H, dd, nuTop, FTType1SeqIndFamily, ctxL,
      type1FittingDadeHyp12, FTType1FittingIn,
      Subgroup.map_subgroupOf_eq_of_le (Fcore_sub w.L)] using
      type1_fitting_coherence_top12 ctxL nu
        (by simpa only [ctxL, fctxL] using hcoh)
  have hzetaS : (zeta : ClassFunction w.L ℂ) ∈
      seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥ := by
    simpa only [H, FTType1SeqIndFamily] using hzeta
  have hcalSgt1 :
      1 < (seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥).card := by
    have htwo := seqInd_nontrivial (k := ℂ) H (mFT_odd w.L)
      (⊤ : Subgroup H) ⊥ hzetaS
    omega
  let data := Dade_Ind1_sub_lin H dd nuTop zeta hcohTop
    hcalSgt1 hzetaS (by simpa only [H] using hzeta1)
  have hcoeff : data.coefficient = 0 :=
    second_dade_coefficient_zero12 ctx w hFrobL hdiv nu hcoh
      zeta hzeta hzeta1 data
  have hself {xi : ClassFunction w.L ℂ}
      (hxi : xi ∈ seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥) :
      characterPairing xi xi = 1 := by
    let xiIrr : IrreducibleCharacter w.L ℂ :=
      ⟨xi, (FT_Frobenius_coherence fctxL).seqInd_irreducible xi (by
        simpa only [H, FTType1SeqIndFamily] using hxi)⟩
    exact xiIrr.characterPairing_self
  obtain ⟨hxP0, hxM, hxL, hxFL, hxNotFM⟩ :=
    witness_x_fitting_position12 ctx w
  let xL : w.L := ⟨w.x, hxL⟩
  have hHmap : H.map w.L.subtype = Fitting_core w.L := by
    simpa only [H, FTType1FittingIn] using
      Subgroup.map_subgroupOf_eq_of_le (Fcore_sub w.L)
  have hxSupport : (xL : G) ∈
      subgroupNonidentity (H.map w.L.subtype) := by
    rw [hHmap]
    exact ⟨hxFL, w.x_ne_one⟩
  have hvalueTop : invDade dd
      (nuTop (zeta : ClassFunction w.L ℂ)) xL = zeta xL :=
    invDade_coherent_value_of_coefficient_zero12 H dd nuTop hcohTop
      zeta hzetaS (by simpa only [H] using hzeta1) hself data hcoeff
      xL hxSupport
  have hvalue : ctxL.rho (nu zeta) xL = zeta xL := by
    change invDade (FT_DadeF_hyp w.L w.L_maximal)
      (characterSourceMap12 (nu zeta)) xL = zeta xL
    simpa only [dd, nuTop, LinearMap.comp_apply,
      type1FittingDadeHyp12, FTType1FittingIn,
      Subgroup.map_subgroupOf_eq_of_le (Fcore_sub w.L)] using hvalueTop
  have hnotLM : ¬ FTAmbientConjugate w.L M :=
    fun hLM ↦ witness_maximals_not_conjugate12 ctx w
      (ambient_conjugate_symm12 hLM)
  have horthM : FTType1OrthogonalToImages
      ctx.M_type_context (nu zeta) :=
    coherent_image_orthogonal12 ctxL ctx.M_type_context hnotLM nu
      (by simpa only [ctxL, fctxL] using hcoh) hzeta
  obtain ⟨hcoset, hrho⟩ :=
    rhoL_eq_psi_on_witness12 ctx w ctxL (nu zeta) horthM
  have hpsiX : nu zeta w.x = zeta xL := hrho.symm.trans hvalue
  refine ⟨?_, ?_⟩
  · intro g hg
    exact (hcoset g hg).trans hpsiX
  · simpa only [xL] using hvalue

/-! ## Norm-tail infrastructure -/

@[simp] private theorem characterSource_apply12
    (phi : ClassFunction G ℂ) (x : (⊤ : Subgroup G)) :
    characterSourceMap12 phi x = phi (x : G) := rfl

private theorem characterSource_normSq12 (phi : ClassFunction G ℂ) :
    classFunctionNormSq (characterSourceMap12 phi) =
      classFunctionNormSq phi := by
  have hcard : Nat.card (⊤ : Subgroup G) = Nat.card G :=
    Nat.card_congr Subgroup.topEquiv.toEquiv
  unfold classFunctionNormSq
  rw [hcard]
  congr 1
  apply Fintype.sum_equiv Subgroup.topEquiv.toEquiv
  intro x
  simp [characterSourceMap12, ClassFunction.comap_apply]

private theorem witness_order12
    {p : ℕ} {M P0 : Subgroup G}
    (ctx : FTType1NonFrobeniusContext p M P0)
    (w : NonFrobeniusFTType1Witness p M P0) :
    orderOf w.x = p := by
  letI : Fact p.Prime := ⟨ctx.p_prime⟩
  obtain ⟨x0, hx0Omega, hx0⟩ := w.x_mem_omega
  letI : IsMulCommutative P0 := w.P0_abelian
  have hx0pow : x0 ^ p = 1 := by
    apply omegaOne_pow_eq_one_of_mul_closed p
    · intro a b ha hb
      have hab : Commute a b := Std.Commutative.comm a b
      simpa [ha, hb] using hab.mul_pow p
    · exact hx0Omega
  have hxpow : w.x ^ p = 1 := by
    rw [← hx0]
    exact congrArg P0.subtype hx0pow
  exact orderOf_eq_prime hxpow w.x_ne_one

private theorem integer_norm_lower12
    {p e : ℕ} (he : 1 ≤ e) (hbound : 2 * e ≤ p + 1)
    (b : ℤ) (hdiv : (p : ℤ) ∣ b - (e : ℤ)) :
    ((e : ℝ) - 1) ^ 2 ≤ Complex.normSq (b : ℂ) := by
  obtain ⟨a, ha⟩ := hdiv
  have hrelZ : b - (e : ℤ) = (p : ℤ) * a := ha
  have hrelR : (b : ℝ) - (e : ℝ) = (p : ℝ) * (a : ℝ) := by
    exact_mod_cast hrelZ
  have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hpR : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hboundR : 2 * (e : ℝ) ≤ (p : ℝ) + 1 := by
    exact_mod_cast hbound
  rw [Complex.normSq_intCast]
  by_cases ha0 : 0 ≤ a
  · have haR : (0 : ℝ) ≤ a := by exact_mod_cast ha0
    have hpa : (0 : ℝ) ≤ (p : ℝ) * (a : ℝ) :=
      mul_nonneg hpR haR
    nlinarith [sq_nonneg ((b : ℝ) - ((e : ℝ) - 1))]
  · have haOne : a ≤ -1 := by omega
    have haOneR : (a : ℝ) ≤ -1 := by exact_mod_cast haOne
    have hpa : (p : ℝ) * (a : ℝ) ≤ -(p : ℝ) := by
      nlinarith
    nlinarith [sq_nonneg ((b : ℝ) + ((e : ℝ) - 1))]

private theorem subgroup_shell_card12
    {Q : Type*} [Group Q] [Fintype Q]
    (M K D : Subgroup Q) (hKM : K ≤ M) (hDK : D ≤ K) :
    (Finset.univ.filter (fun y : M ↦
      (y : Q) ∈ K ∧ (y : Q) ∉ D)).card =
        Nat.card K - Nat.card D := by
  classical
  let shellM := {y : M // (y : Q) ∈ K ∧ (y : Q) ∉ D}
  let shellK := {y : K // (y : Q) ∉ D}
  let inD := {y : K // (y : Q) ∈ D}
  let eShell : shellM ≃ shellK :=
    { toFun := fun y ↦ ⟨⟨y, y.2.1⟩, y.2.2⟩
      invFun := fun y ↦
        ⟨⟨(y : Q), hKM y.1.2⟩, y.1.2, y.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let eD : inD ≃ D :=
    { toFun := fun y ↦ ⟨(y : Q), y.2⟩
      invFun := fun y ↦ ⟨⟨(y : Q), hDK y.2⟩, y.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  calc
    (Finset.univ.filter (fun y : M ↦
        (y : Q) ∈ K ∧ (y : Q) ∉ D)).card = Nat.card shellM := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ = Nat.card shellK := Nat.card_congr eShell
    _ = Nat.card K - Nat.card inD := by
      simpa only [shellK, inD, Nat.card_eq_fintype_card] using
        Fintype.card_subtype_compl (fun y : K ↦ (y : Q) ∈ D)
    _ = Nat.card K - Nat.card D := by rw [Nat.card_congr eD]

private theorem disjoint_mass_lt_total12
    {Q : Type*} [Group Q] [Fintype Q]
    (S₁ S₂ : Finset Q) (hdis : Disjoint S₁ S₂)
    (hone₁ : (1 : Q) ∉ S₁) (hone₂ : (1 : Q) ∉ S₂)
    (mass : Q → ℝ) (hmass : ∀ x, 0 ≤ mass x)
    (hone : 0 < mass 1) :
    (∑ x ∈ S₁, mass x) + (∑ x ∈ S₂, mass x) <
      ∑ x : Q, mass x := by
  have hsub : S₁ ∪ S₂ ⊆ (Finset.univ : Finset Q).erase 1 := by
    intro x hx
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ x⟩
    intro hxOne
    subst x
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hone₁ hx
    · exact hone₂ hx
  have hle :
      ∑ x ∈ S₁ ∪ S₂, mass x ≤
        ∑ x ∈ (Finset.univ : Finset Q).erase 1, mass x :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun x _ _ ↦ hmass x)
  have herase :
      (∑ x ∈ (Finset.univ : Finset Q).erase 1, mass x) +
          mass 1 = ∑ x : Q, mass x := by
    simpa using Finset.sum_erase_add
      (s := (Finset.univ : Finset Q)) (f := mass)
      (Finset.mem_univ (1 : Q))
  rw [← Finset.sum_union hdis]
  linarith

private theorem two_invDade_norm_lt_one12
    {Gamma : Type*} [Group Gamma] [Fintype Gamma]
    {Q L₁ L₂ : Subgroup Gamma} {A₁ A₂ : Set Gamma}
    (dd₁ : DadeHypothesis Q L₁ A₁)
    (dd₂ : DadeHypothesis Q L₂ A₂)
    (hdis : Disjoint (Dade_support dd₁) (Dade_support dd₂))
    (psi : ClassFunction Q ℂ)
    (hnorm : classFunctionNormSq psi = 1) (hpsiOne : psi 1 ≠ 0) :
    classFunctionNormSq (invDade dd₁ psi) +
        classFunctionNormSq (invDade dd₂ psi) < 1 := by
  classical
  let S₁ : Finset Q := Finset.univ.filter
    (fun y : Q ↦ (y : Gamma) ∈ Dade_support dd₁)
  let S₂ : Finset Q := Finset.univ.filter
    (fun y : Q ↦ (y : Gamma) ∈ Dade_support dd₂)
  let mass : Q → ℝ := fun y ↦ Complex.normSq (psi y)
  have hSdis : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro y hy₁ hy₂
    exact Set.disjoint_left.mp hdis
      (Finset.mem_filter.mp hy₁).2
      (Finset.mem_filter.mp hy₂).2
  have hone₁ : (1 : Q) ∉ S₁ := by
    intro hone
    apply not_support_Dade_1 dd₁
    have hcoeOne : ((1 : Q) : Gamma) = 1 := rfl
    rw [← hcoeOne]
    simpa only [S₁, Finset.mem_filter,
      Finset.mem_univ, true_and] using hone
  have hone₂ : (1 : Q) ∉ S₂ := by
    intro hone
    apply not_support_Dade_1 dd₂
    have hcoeOne : ((1 : Q) : Gamma) = 1 := rfl
    rw [← hcoeOne]
    simpa only [S₂, Finset.mem_filter,
      Finset.mem_univ, true_and] using hone
  have hstrict :
      (∑ y ∈ S₁, mass y) + (∑ y ∈ S₂, mass y) <
        ∑ y : Q, mass y :=
    disjoint_mass_lt_total12 S₁ S₂ hSdis hone₁ hone₂
      mass (fun y ↦ Complex.normSq_nonneg (psi y))
      (Complex.normSq_pos.mpr hpsiOne)
  have hcardPos : 0 < (Nat.card Q : ℝ) :=
    Nat.cast_pos.mpr Nat.card_pos
  have hsuppStrict :
      dadeSupportNormSq dd₁ psi + dadeSupportNormSq dd₂ psi < 1 := by
    unfold classFunctionNormSq at hnorm
    unfold dadeSupportNormSq
    change (Nat.card Q : ℝ)⁻¹ * (∑ y ∈ S₁, mass y) +
        (Nat.card Q : ℝ)⁻¹ * (∑ y ∈ S₂, mass y) < 1
    rw [← mul_add]
    have hscaled :=
      mul_lt_mul_of_pos_left hstrict (inv_pos.mpr hcardPos)
    rw [hnorm] at hscaled
    exact hscaled
  exact lt_of_le_of_lt
    (add_le_add
      (leC_cfnorm_invDade_support dd₁ psi).1
      (leC_cfnorm_invDade_support dd₂ psi).1)
    hsuppStrict

private theorem two_fitting_invDade_norm_lt_one12
    {M L : Subgroup G}
    (hmaxM : M ∈ minSimple_max_groups (G := G))
    (hmaxL : L ∈ minSimple_max_groups (G := G))
    (hdis : Disjoint
      (Dade_support (FT_DadeF_hyp M hmaxM))
      (Dade_support (FT_DadeF_hyp L hmaxL)))
    (psi : ClassFunction G ℂ)
    (hnorm : classFunctionNormSq psi = 1) (hpsiOne : psi 1 ≠ 0) :
    classFunctionNormSq
        (invDade (FT_DadeF_hyp M hmaxM) (characterSourceMap12 psi)) +
      classFunctionNormSq
        (invDade (FT_DadeF_hyp L hmaxL) (characterSourceMap12 psi)) < 1 := by
  apply two_invDade_norm_lt_one12
    (FT_DadeF_hyp M hmaxM) (FT_DadeF_hyp L hmaxL)
    hdis (characterSourceMap12 psi)
  · simpa only [characterSource_normSq12] using hnorm
  · change psi (((1 : (⊤ : Subgroup G)) : G)) ≠ 0
    have hcoeOne : ((1 : (⊤ : Subgroup G)) : G) = 1 := rfl
    simpa only [hcoeOne] using hpsiOne

private theorem fitting_dade_supports_disjoint12
    {p : ℕ} {M P0 : Subgroup G}
    (ctx : FTType1NonFrobeniusContext p M P0)
    (w : NonFrobeniusFTType1Witness p M P0)
    {E : Subgroup G}
    (hFrobL : IsFrobeniusIn (Fitting_core w.L) E w.L) :
    Disjoint
      (Dade_support (FT_DadeF_hyp M ctx.M_type_context.maxL))
      (Dade_support (FT_DadeF_hyp w.L w.L_maximal)) := by
  have htypeL : FTtype w.L = 1 := by
    let fctxL : FTFrobeniusContext w.L :=
      ⟨w.L_maximal, ⟨E, hFrobL⟩⟩
    exact FT_Frobenius_type1 fctxL
  rw [FT_DadeF_supportE M ctx.M_type_context.maxL,
    FT_DadeF_supportE w.L w.L_maximal]
  rw [← FTsupp1_type1 M ctx.M_type_context.type_one,
    ← FTsupp1_type1 w.L htypeL]
  exact FT_Dade1_support_disjoint
    ctx.M_type_context.maxL w.L_maximal
      (witness_maximals_not_conjugate12 ctx w)

private theorem fitting_shell_value_lower12
    {p : ℕ} {M P0 : Subgroup G}
    (ctx : FTType1NonFrobeniusContext p M P0)
    (w : NonFrobeniusFTType1Witness p M P0)
    {E : Subgroup G}
    (hFrobL : IsFrobeniusIn (Fitting_core w.L) E w.L)
    (hdiv : Nat.card E ∣ p - 1 ∨ Nat.card E ∣ p + 1)
    (psi : ClassFunction G ℂ)
    (hpsiVirtual : ClassFunction.IsVirtual psi)
    (zeta : IrreducibleCharacter w.L ℂ)
    (hzeta1 : zeta 1 = ((FTType1FittingIn w.L).index : ℂ))
    (hxL : w.x ∈ w.L)
    (hcoset : ∀ g : G, g ∈ Fitting_core M →
      psi (w.x * g) = zeta ⟨w.x, hxL⟩)
    (hconstant : ∀ x : G, x ∈ Fitting_core M →
      x ∉ derivedWithin (Fitting_core M) →
      ∀ y : G, y ∈ Fitting_core M →
        y ∉ derivedWithin (Fitting_core M) → psi x = psi y)
    (hinteger : ∀ x : G, x ∈ Fitting_core M →
      x ∉ derivedWithin (Fitting_core M) →
      ∃ b : ℤ, psi x = (b : ℂ)) :
    ∀ y : G, y ∈ Fitting_core M →
      y ∉ derivedWithin (Fitting_core M) →
      ((Nat.card E : ℝ) - 1) ^ 2 ≤ Complex.normSq (psi y) := by
  classical
  obtain ⟨g, hgCentral, hgNotDerived⟩ :=
    SetLike.not_le_iff_exists.mp w.core_centralizer_not_le_derived
  have hgK : g ∈ Fitting_core M := hgCentral.1
  have hxg : Commute w.x g := by
    show w.x * g = g * w.x
    exact Subgroup.mem_centralizer_iff.mp hgCentral.2 w.x
      (Subgroup.mem_zpowers w.x)
  obtain ⟨b, hb⟩ := hinteger g hgK hgNotDerived
  have hpOdd : Odd p := by
    obtain ⟨A, _hAP0, hA⟩ := w.P0_rank_two.1
    have hpA : p ∣ Nat.card A := by
      rw [hA.card_eq]
      exact dvd_pow_self p (by omega : 2 ≠ 0)
    exact Odd.of_dvd_nat (mFT_odd A) hpA
  have heBound : 2 * Nat.card E ≤ p + 1 :=
    odd_divisor_pm_one_half_bound12 ctx.p_prime hpOdd (mFT_odd E) hdiv
  let eps : ℂ := Complex.exp (2 * Real.pi * Complex.I / p)
  have heps : IsPrimitiveRoot eps p := by
    simpa only [eps] using
      Complex.isPrimitiveRoot_exp p ctx.p_prime.ne_zero
  let xL : w.L := ⟨w.x, hxL⟩
  have hxOrder : orderOf w.x = p := witness_order12 ctx w
  have hxOrderL : orderOf xL = p :=
    (orderOf_injective w.L.subtype w.L.subtype_injective xL).symm.trans
      hxOrder
  obtain ⟨vpsi, hvpsi⟩ := hpsiVirtual
  obtain ⟨vzeta, hvzeta⟩ :=
    FTType1InfrastructureInternal.irreducibleIsVirtual zeta
  have hmodPsi : IsIntegralModEq (1 - eps)
      (psi (w.x * g)) (psi g) := by
    have hmod := vchar_ker_mod_prim_of_isAlgClosed
      heps vpsi w.x g hxOrder hxg
    simpa only [hvpsi] using hmod
  have hmodZeta : IsIntegralModEq (1 - eps)
      (zeta xL) (zeta 1) := by
    have hmod := vchar_ker_mod_prim_of_isAlgClosed
      heps vzeta xL 1 hxOrderL (Commute.one_right xL)
    simpa only [hvzeta, mul_one] using hmod
  have hmodValue : IsIntegralModEq (1 - eps) (psi g) (zeta 1) :=
    hmodPsi.symm.trans
      ((IsIntegralModEq.of_eq (hcoset g hgK)).trans hmodZeta)
  have hEL : E ≤ w.L := le_sup_right.trans_eq hFrobL.1
  have hFrobHE : IsFrobeniusDecomposition
      (FTType1FittingIn w.L) (E.subgroupOf w.L) :=
    frobeniusIn_decomposition12 hFrobL
  have hindex : (FTType1FittingIn w.L).index = Nat.card E :=
    hFrobHE.isComplement.symm.index_eq_card.trans
      (Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hEL)
  have hmodDifference : IsIntegralModEq (1 - eps)
      ((b : ℂ) - (Nat.card E : ℂ)) 0 := by
    have hsub := hmodValue.sub
      (IsIntegralModEq.refl (1 - eps) (zeta 1))
    simpa only [hb, hzeta1, hindex, sub_self] using hsub
  have hpDiv : (p : ℤ) ∣ b - (Nat.card E : ℤ) := by
    apply int_eqAmod_prime_prim_of_isAlgClosed heps ctx.p_prime
    simpa only [Int.cast_sub, Int.cast_natCast] using hmodDifference
  have hbLower : ((Nat.card E : ℝ) - 1) ^ 2 ≤
      Complex.normSq (b : ℂ) :=
    integer_norm_lower12 Nat.card_pos heBound b hpDiv
  intro y hyK hyNotDerived
  rw [hconstant y hyK hyNotDerived g hgK hgNotDerived, hb]
  exact hbLower

private theorem invDade_norm_lower_on_finset12
    {Gamma : Type*} [Group Gamma] [Fintype Gamma]
    {Q L : Subgroup Gamma} {A : Set Gamma}
    (dd : DadeHypothesis Q L A) (psi : ClassFunction Q ℂ)
    (S : Finset L) (c : ℝ)
    (hS : ∀ y ∈ S, (y : Gamma) ∈ A)
    (hpoint : ∀ y ∈ S, c ≤ Complex.normSq (invDade dd psi y)) :
    (Nat.card L : ℝ)⁻¹ * (S.card : ℝ) * c ≤
      classFunctionNormSq (invDade dd psi) := by
  classical
  let support : Finset L := Finset.univ.filter
    (fun y : L ↦ (y : Gamma) ∈ A)
  have hsubset : S ⊆ support := by
    intro y hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, hS y hy⟩
  have hsumS :
      (S.card : ℝ) * c ≤
        ∑ y ∈ S, Complex.normSq (invDade dd psi y) := by
    calc
      (S.card : ℝ) * c = ∑ _y ∈ S, c := by simp
      _ ≤ ∑ y ∈ S, Complex.normSq (invDade dd psi y) :=
        Finset.sum_le_sum fun y hy ↦ hpoint y hy
  have hsumSupport :
      (∑ y ∈ S, Complex.normSq (invDade dd psi y)) ≤
        ∑ y ∈ support, Complex.normSq (invDade dd psi y) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun y _ _ ↦ Complex.normSq_nonneg _)
  have hscaled := mul_le_mul_of_nonneg_left
    (hsumS.trans hsumSupport)
    (inv_nonneg.mpr (Nat.cast_nonneg (Nat.card L)))
  rw [cfnormE_invDade]
  simpa only [support, mul_assoc] using hscaled

private theorem invDade_eq_of_support_eq12
    {Gamma : Type*} [Group Gamma] [Fintype Gamma]
    {Q L : Subgroup Gamma} {A B : Set Gamma}
    (hAB : A = B) (ddA : DadeHypothesis Q L A)
    (ddB : DadeHypothesis Q L B) (psi : ClassFunction Q ℂ) :
    invDade ddA psi = invDade ddB psi := by
  subst B
  rfl

private theorem first_fitting_norm_lower12
    {p : ℕ} {M P0 : Subgroup G}
    (ctx : FTType1NonFrobeniusContext p M P0)
    {E : Subgroup G}
    (psi : ClassFunction G ℂ)
    (hrho : ∀ (g : G) (hg : g ∈ subgroupNonidentity (Fitting_core M)),
      invDade (FT_DadeF_hyp M ctx.M_type_context.maxL)
          (characterSourceMap12 psi)
          ⟨g, Fcore_sub M hg.1⟩ = psi g)
    (hlower : ∀ y : G, y ∈ Fitting_core M →
      y ∉ derivedWithin (Fitting_core M) →
      ((Nat.card E : ℝ) - 1) ^ 2 ≤ Complex.normSq (psi y)) :
    (Nat.card M : ℝ)⁻¹ *
        (Nat.card (Fitting_core M) -
          Nat.card (derivedWithin (Fitting_core M)) : ℕ) *
        ((Nat.card E : ℝ) - 1) ^ 2 ≤
      classFunctionNormSq
        (invDade (FT_DadeF_hyp M ctx.M_type_context.maxL)
          (characterSourceMap12 psi)) := by
  classical
  let K := Fitting_core M
  let D := derivedWithin K
  let dd := FT_DadeF_hyp M ctx.M_type_context.maxL
  let shell : Finset M := Finset.univ.filter (fun y : M ↦
    (y : G) ∈ K ∧ (y : G) ∉ D)
  have hDK : D ≤ K :=
    TypeSpecInternal.derivedWithin_le16_final K
  have hcardShell : shell.card = Nat.card K - Nat.card D := by
    simpa only [shell, K, D] using
      subgroup_shell_card12 M K D (Fcore_sub M) hDK
  have hShellSupport : ∀ y ∈ shell,
      (y : G) ∈ subgroupNonidentity K := by
    intro y hy
    have hy' := (Finset.mem_filter.mp hy).2
    refine ⟨hy'.1, ?_⟩
    intro hyOne
    apply hy'.2
    rw [hyOne]
    exact D.one_mem
  have hpoint : ∀ y ∈ shell,
      ((Nat.card E : ℝ) - 1) ^ 2 ≤
        Complex.normSq (invDade dd (characterSourceMap12 psi) y) := by
    intro y hy
    have hy' := (Finset.mem_filter.mp hy).2
    have hySharp : (y : G) ∈ subgroupNonidentity K :=
      hShellSupport y hy
    rw [show invDade dd (characterSourceMap12 psi) y = psi (y : G) by
      simpa only [dd, K] using hrho (y : G) hySharp]
    exact hlower (y : G) hy'.1 hy'.2
  have hgeneric := invDade_norm_lower_on_finset12
    dd (characterSourceMap12 psi) shell
      (((Nat.card E : ℝ) - 1) ^ 2)
      hShellSupport hpoint
  simpa only [dd, K, D, hcardShell] using hgeneric

private theorem second_fitting_norm_lower12
    {p : ℕ} {M P0 : Subgroup G}
    (ctx : FTType1NonFrobeniusContext p M P0)
    (w : NonFrobeniusFTType1Witness p M P0)
    {E : Subgroup G}
    (hFrobL : IsFrobeniusIn (Fitting_core w.L) E w.L)
    (nu : ClassFunction w.L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (hcohTop : coherent_with
      (FTType1SeqIndFamily w.L : Set (ClassFunction w.L ℂ))
      (nonidentitySet w.L)
      (Dade (FT_DadeF_hyp w.L w.L_maximal))
      (characterSourceMap12.comp nu))
    (zeta : IrreducibleCharacter w.L ℂ)
    (hzeta : (zeta : ClassFunction w.L ℂ) ∈
      FTType1SeqIndFamily w.L)
    (hzeta1 : zeta 1 = ((FTType1FittingIn w.L).index : ℂ)) :
    1 - (Nat.card E : ℝ) /
        (Nat.card (Fitting_core w.L) : ℝ) ≤
      classFunctionNormSq
        (invDade (FT_DadeF_hyp w.L w.L_maximal)
          ((characterSourceMap12.comp nu) zeta)) := by
  classical
  let H : Subgroup w.L := FTType1FittingIn w.L
  let calS : Finset (ClassFunction w.L ℂ) :=
    seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥
  let dd := type1FittingDadeHyp12 w.L w.L_maximal
  let nuTop : ClassFunction w.L ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup G) ℂ :=
    characterSourceMap12.comp nu
  letI : H.Normal := by
    simpa only [H, FTType1FittingIn] using Fcore_normal w.L
  have hzetaS : (zeta : ClassFunction w.L ℂ) ∈ calS := by
    simpa only [calS, H, FTType1SeqIndFamily] using hzeta
  have hcohTop' : coherent_with
      (↑calS : Set (ClassFunction w.L ℂ))
      (nonidentitySet w.L) (Dade dd) nuTop := by
    simpa only [calS, H, dd, nuTop, FTType1SeqIndFamily,
      type1FittingDadeHyp12, FTType1FittingIn,
      Subgroup.map_subgroupOf_eq_of_le (Fcore_sub w.L)] using hcohTop
  have hcalSgt1 : 1 < calS.card := by
    have htwo := seqInd_nontrivial (k := ℂ) H (mFT_odd w.L)
      (⊤ : Subgroup H) ⊥ hzetaS
    change 1 < (seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥).card
    omega
  let data := Dade_Ind1_sub_lin H dd nuTop zeta hcohTop'
    hcalSgt1 hzetaS (by simpa only [H] using hzeta1)
  have hEL : E ≤ w.L := le_sup_right.trans_eq hFrobL.1
  have hFrobHE : IsFrobeniusDecomposition H (E.subgroupOf w.L) := by
    simpa only [H] using frobeniusIn_decomposition12 hFrobL
  have hbound : (H.index : ℝ) ≤
      ((Nat.card H : ℝ) - 1) / 2 :=
    odd_Frobenius_index_ler H (E.subgroupOf w.L)
      (mFT_odd w.L) hFrobHE
  have hindex : H.index = Nat.card E :=
    hFrobHE.isComplement.symm.index_eq_card.trans
      (Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hEL)
  have hcardH : Nat.card H = Nat.card (Fitting_core w.L) := by
    simpa only [H, FTType1FittingIn] using
      Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
        (Fcore_sub w.L)
  have hdata := (data.norm_bounds hbound).1
  have hsupport : subgroupNonidentity (H.map w.L.subtype) =
      subgroupNonidentity (Fitting_core w.L) := by
    simp only [H, FTType1FittingIn,
      Subgroup.map_subgroupOf_eq_of_le (Fcore_sub w.L)]
  have hinv : invDade dd (nuTop zeta) =
      invDade (FT_DadeF_hyp w.L w.L_maximal) (nuTop zeta) :=
    invDade_eq_of_support_eq12 hsupport dd
      (FT_DadeF_hyp w.L w.L_maximal) (nuTop zeta)
  rw [hinv] at hdata
  simpa only [nuTop, LinearMap.comp_apply, hindex, hcardH] using hdata

private theorem coherent_image_norm_one12
    {L : Subgroup G} {A : Set L}
    {tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    (nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (hcoh : coherent_with
      (FTType1SeqIndFamily L : Set (ClassFunction L ℂ))
      A tau nu)
    (zeta : IrreducibleCharacter L ℂ)
    (hzeta : (zeta : ClassFunction L ℂ) ∈
      FTType1SeqIndFamily L) :
    ClassFunction.IsVirtual (nu zeta) ∧
      classFunctionNormSq (nu zeta) = 1 ∧ nu zeta 1 ≠ 0 := by
  classical
  letI : Invertible (Nat.card L : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hmem : (zeta : ClassFunction L ℂ) ∈
      AddSubgroup.closure
        (FTType1SeqIndFamily L : Set (ClassFunction L ℂ)) :=
    AddSubgroup.subset_closure hzeta
  have hvirtual : ClassFunction.IsVirtual (nu zeta) :=
    hcoh.mapsToVirtual (zeta : ClassFunction L ℂ) hmem
  have hpair : characterPairing (nu zeta) (nu zeta) = 1 := by
    calc
      characterPairing (nu zeta) (nu zeta) =
          characterPairing (zeta : ClassFunction L ℂ)
            (zeta : ClassFunction L ℂ) :=
        hcoh.isometry (zeta : ClassFunction L ℂ) hmem
          (zeta : ClassFunction L ℂ) hmem
      _ = 1 := zeta.characterPairing_self
  have hnorm : classFunctionNormSq (nu zeta) = 1 := by
    rw [classFunctionNormSq_eq_re_starCharacterPairing,
      FTType1InfrastructureInternal.starPairingEqPairingOfRightVirtual
        (nu zeta) hvirtual,
      hpair]
    norm_num
  refine ⟨hvirtual, hnorm, ?_⟩
  obtain ⟨v, hv⟩ := hvirtual
  have hvNorm : normSq v = 1 := by
    apply Int.cast_injective (α := ℂ)
    calc
      (normSq v : ℂ) =
          characterPairing (VirtualCharacter.realize v)
            (VirtualCharacter.realize v) := by
        simpa [normSq] using
          (VirtualCharacter.characterPairing_realize v v).symm
      _ = 1 := by rw [hv]; exact hpair
      _ = ((1 : ℤ) : ℂ) := by norm_num
  have hone := VirtualCharacter.evalOne_ne_zero_of_normSq_eq_one v hvNorm
  simpa only [VirtualCharacter.evalOne_apply, hv] using hone

private theorem real_index_lt_four_of_norm12
    {m d i h e q : ℝ}
    (hm : 0 < m) (hd : 0 < d) (hh : 0 < h)
    (hq : 0 ≤ q) (hi : 0 ≤ i) (he : 3 ≤ e) (hile : i ≤ h)
    (hmul : m = d * q * i)
    (hnorm : m⁻¹ * (d * (q - 1)) * (e - 1) ^ 2 +
      (1 - e / h) < 1) :
    q < 4 := by
  have hscaled :=
    mul_lt_mul_of_pos_right hnorm (mul_pos hm hh)
  have hscaledLeft :
      (m⁻¹ * (d * (q - 1)) * (e - 1) ^ 2 +
          (1 - e / h)) * (m * h) =
        d * (q - 1) * (e - 1) ^ 2 * h + m * h - e * m := by
    field_simp [hm.ne', hh.ne']
    ring
  have hcore :
      d * (q - 1) * (e - 1) ^ 2 * h < e * m := by
    rw [hscaledLeft] at hscaled
    nlinarith
  rw [hmul] at hcore
  have hcancelD :
      (q - 1) * (e - 1) ^ 2 * h < q * i * e := by
    exact (mul_lt_mul_iff_of_pos_left hd).mp (by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hcore)
  have he0 : 0 ≤ e := le_trans (by norm_num) he
  have hrhs : q * i * e ≤ q * h * e := by gcongr
  have hcancelH : (q - 1) * (e - 1) ^ 2 < q * e := by
    exact (mul_lt_mul_iff_of_pos_right hh).mp (lt_of_lt_of_le
      (by simpa only [mul_assoc, mul_left_comm, mul_comm] using hcancelD)
      (by simpa only [mul_assoc, mul_left_comm, mul_comm] using hrhs))
  by_contra hq4
  have hq4' : 4 ≤ q := by linarith
  have hsquare : 0 ≤ (e - 1) ^ 2 := sq_nonneg _
  have heFactor : 0 ≤ (e - 3) * (3 * e - 1) :=
    mul_nonneg (by linarith) (by linarith)
  have heBound : 4 * e ≤ 3 * (e - 1) ^ 2 := by nlinarith
  have hqBound : 3 * q ≤ 4 * (q - 1) := by linarith
  have hfirst : 4 * q * e ≤ 3 * q * (e - 1) ^ 2 := by
    nlinarith [mul_nonneg hq (sub_nonneg.mpr heBound)]
  have hsecond : 3 * q * (e - 1) ^ 2 ≤
      4 * (q - 1) * (e - 1) ^ 2 :=
    mul_le_mul_of_nonneg_right hqBound hsquare
  have hcontra : q * e ≤ (q - 1) * (e - 1) ^ 2 := by
    nlinarith [hfirst.trans hsecond]
  exact (not_lt_of_ge hcontra) hcancelH

private theorem fitting_abelianization_lt_four12
    {p : ℕ} {M P0 : Subgroup G}
    (w : NonFrobeniusFTType1Witness p M P0)
    {E : Subgroup G}
    (hFrobL : IsFrobeniusIn (Fitting_core w.L) E w.L)
    (hsdM : IsInternalSemidirectProductIn
      (Fitting_core M) (M ⊓ w.L) M)
    (hinter : M ⊓ w.L ≤ Fitting_core w.L)
    (normM normL : ℝ)
    (hlowerM :
      (Nat.card M : ℝ)⁻¹ *
          (Nat.card (Fitting_core M) -
            Nat.card (derivedWithin (Fitting_core M)) : ℕ) *
          ((Nat.card E : ℝ) - 1) ^ 2 ≤ normM)
    (hlowerL :
      1 - (Nat.card E : ℝ) /
          (Nat.card (Fitting_core w.L) : ℝ) ≤ normL)
    (hupper : normM + normL < 1) :
    (_root_.commutator (Fitting_core M)).index < 4 := by
  classical
  let K := Fitting_core M
  let D := derivedWithin K
  let I := M ⊓ w.L
  let H := Fitting_core w.L
  let e := Nat.card E
  let q := (_root_.commutator K).index
  have hsum :
      (Nat.card M : ℝ)⁻¹ *
          (Nat.card K - Nat.card D : ℕ) * ((e : ℝ) - 1) ^ 2 +
        (1 - (e : ℝ) / (Nat.card H : ℝ)) < 1 :=
    lt_of_le_of_lt
      (add_le_add
        (by simpa only [K, D, e] using hlowerM)
        (by simpa only [H, e] using hlowerL))
      hupper
  have hcardD : Nat.card D =
      Nat.card (_root_.commutator K) := by
    simpa only [D, derivedWithin] using
      Subgroup.card_map_of_injective
        (K := _root_.commutator K) K.subtype_injective
  have hcardK : Nat.card K = Nat.card D * q := by
    rw [hcardD]
    exact (_root_.commutator K).card_mul_index.symm
  have hqOne : 1 ≤ q :=
    Nat.one_le_iff_ne_zero.mpr
      (_root_.commutator K).index_ne_zero_of_finite
  have hcardDiff : Nat.card K - Nat.card D =
      Nat.card D * (q - 1) := by
    rw [hcardK]
    rw [Nat.mul_sub_left_distrib, mul_one]
  have hIM : I ≤ M := by simpa only [I] using inf_le_left
  have hcardM : Nat.card M = Nat.card K * Nat.card I := by
    have hcomp := hsdM.2.2.2
    have hcompCard : (K.subgroupOf M).index =
        Nat.card (I.subgroupOf M) := by
      simpa only [K, I] using hcomp.symm.index_eq_card
    have hKcard : Nat.card (K.subgroupOf M) = Nat.card K :=
      Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
        (by simpa only [K] using Fcore_sub M)
    have hIcard : Nat.card (I.subgroupOf M) = Nat.card I :=
      Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hIM
    calc
      Nat.card M = Nat.card (K.subgroupOf M) *
          (K.subgroupOf M).index :=
        (K.subgroupOf M).card_mul_index.symm
      _ = Nat.card K * Nat.card I := by
        rw [hcompCard, hKcard, hIcard]
  have hcardM' : Nat.card M = Nat.card D * q * Nat.card I := by
    rw [hcardM, hcardK]
  have hIleH : Nat.card I ≤ Nat.card H :=
    Nat.le_of_dvd Nat.card_pos
      (Subgroup.card_dvd_of_le (by simpa only [I, H] using hinter))
  have heOdd : Odd e := by
    simpa only [e] using mFT_odd E
  have heOne : 1 < e := by
    have hEL : E ≤ w.L := le_sup_right.trans_eq hFrobL.1
    have hFrobHE : IsFrobeniusDecomposition
        (FTType1FittingIn w.L) (E.subgroupOf w.L) :=
      frobeniusIn_decomposition12 hFrobL
    have hsubOne : 1 < Nat.card (E.subgroupOf w.L) :=
      (E.subgroupOf w.L).one_lt_card_iff_ne_bot.mpr
        hFrobHE.complement_ne_bot
    simpa only [e,
      Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hEL] using
        hsubOne
  have heThree : 3 ≤ e := by
    obtain ⟨k, hk⟩ := heOdd
    omega
  rw [hcardDiff] at hsum
  have hsumR :
      (Nat.card M : ℝ)⁻¹ *
          ((Nat.card D : ℝ) * ((q : ℝ) - 1)) *
          ((e : ℝ) - 1) ^ 2 +
        (1 - (e : ℝ) / (Nat.card H : ℝ)) < 1 := by
    simpa only [Nat.cast_mul, Nat.cast_sub hqOne, Nat.cast_one] using hsum
  have hqR : (q : ℝ) < 4 :=
    real_index_lt_four_of_norm12
      (Nat.cast_pos.mpr Nat.card_pos)
      (Nat.cast_pos.mpr Nat.card_pos)
      (Nat.cast_pos.mpr Nat.card_pos)
      (Nat.cast_nonneg q)
      (Nat.cast_nonneg (Nat.card I))
      (by exact_mod_cast heThree)
      (by exact_mod_cast hIleH)
      (by exact_mod_cast hcardM')
      hsumR
  exact_mod_cast hqR

private theorem rel_index_card_map_quotient12
    {Q : Type*} [Group Q] [Finite Q]
    {N H : Subgroup Q} (hNnormal : N.Normal) (hNH : N ≤ H) :
    N.relIndex H = Nat.card (H.map (QuotientGroup.mk' N)) := by
  letI : N.Normal := hNnormal
  let qmap : Q →* Q ⧸ N := QuotientGroup.mk' N
  let f : H →* Q ⧸ N := qmap.comp H.subtype
  have hker : f.ker = N.subgroupOf H := by
    ext x
    change qmap (x : Q) = 1 ↔ (x : Q) ∈ N
    exact QuotientGroup.eq_one_iff (x : Q)
  have hrange : f.range = H.map qmap := by
    dsimp only [f]
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  calc
    N.relIndex H = (N.subgroupOf H).index := rfl
    _ = f.ker.index := congrArg Subgroup.index hker.symm
    _ = Nat.card f.range := Subgroup.index_ker f
    _ = Nat.card (H.map qmap) :=
      Nat.card_congr (MulEquiv.subgroupCongr hrange).toEquiv

private theorem frobenius_kernel_card_ge_four12
    {Q : Type*} [Group Q] [Finite Q]
    {K R : Subgroup Q} (hFrob : IsFrobeniusDecomposition K R)
    {p : ℕ} (hpThree : 3 ≤ p) (hpR : p ∣ Nat.card R) :
    4 ≤ Nat.card K := by
  letI := hFrob.conjugationAction
  let t := Nat.card
    (nonidentityFixedOneOrbitQuotient (G := R) (X := K))
  have hcard : Nat.card K = 1 + t * Nat.card R := by
    simpa only [t] using hFrob.kernel_card_eq_one_add_orbits_mul_card
  have hKone : 1 < Nat.card K :=
    K.one_lt_card_iff_ne_bot.mpr hFrob.kernel_ne_bot
  have hpLeR : p ≤ Nat.card R :=
    Nat.le_of_dvd Nat.card_pos hpR
  have htPos : 0 < t := by
    by_contra ht
    have htZero : t = 0 := Nat.eq_zero_of_not_pos ht
    rw [htZero, zero_mul, add_zero] at hcard
    omega
  have hRle : Nat.card R ≤ t * Nat.card R := by
    simpa only [one_mul] using
      Nat.mul_le_mul_right (Nat.card R) (Nat.one_le_iff_ne_zero.mpr htPos.ne')
  omega

private theorem small_abelianization_frobenius_contradiction12
    {p : ℕ} {M P0 : Subgroup G}
    (ctx : FTType1NonFrobeniusContext p M P0)
    (w : NonFrobeniusFTType1Witness p M P0)
    (hsdM : IsInternalSemidirectProductIn
      (Fitting_core M) (M ⊓ w.L) M)
    (hsmall : (_root_.commutator (Fitting_core M)).index < 4) : False := by
  classical
  let K := Fitting_core M
  let I := M ⊓ w.L
  obtain ⟨U, hTypeI⟩ :=
    (FTtypeP 1 M ctx.M_type_context.maxL).mpr
      ctx.M_type_context.type_one
  have hTypeFI : of_typeF M I :=
    compl_of_typeF M I U hsdM hTypeI.1
  obtain ⟨U0, hU0⟩ := hTypeFI.2.2.2.2
  let J := K ⊔ U0
  let KJ : Subgroup J := K.subgroupOf J
  let UJ : Subgroup J := U0.subgroupOf J
  have hFrob0 : IsFrobeniusDecomposition KJ UJ := by
    simpa only [J, KJ, UJ, K] using hU0.2.2.2
  let C : Subgroup KJ := _root_.commutator KJ
  let N : Subgroup J := C.map KJ.subtype
  letI : KJ.Normal := hFrob0.kernel_normal
  letI : C.Characteristic := by
    dsimp only [C]
    infer_instance
  letI : N.Normal := by
    dsimp only [N]
    infer_instance
  let eK : KJ ≃* K := Subgroup.subgroupOfEquivOfLe le_sup_left
  have hKJsol : IsSolvable KJ := by
    letI : Group.IsNilpotent K := Fcore_nil M
    exact isSolvable_of_injective eK.toMonoidHom eK.injective
  letI : IsSolvable KJ := hKJsol
  letI : Nontrivial KJ :=
    KJ.nontrivial_iff_ne_bot.mpr hFrob0.kernel_ne_bot
  have hCtop : C < (⊤ : Subgroup KJ) := by
    simpa only [C] using
      IsSolvable.commutator_lt_top_of_nontrivial KJ
  have hNK : N < KJ := by
    have hmap :=
      (Subgroup.map_lt_map_iff_of_injective KJ.subtype_injective).2 hCtop
    simpa only [N, ← MonoidHom.range_eq_map, KJ.range_subtype] using hmap
  let qmap : J →* J ⧸ N := QuotientGroup.mk' N
  let Kq : Subgroup (J ⧸ N) := KJ.map qmap
  let Rq : Subgroup (J ⧸ N) := UJ.map qmap
  have hFrobQ : IsFrobeniusDecomposition Kq Rq := by
    simpa only [qmap, Kq, Rq] using hFrob0.quotient hNK
  have hNsub : N.subgroupOf KJ = C := by
    dsimp only [N]
    exact Subgroup.comap_map_eq_self_of_injective
      KJ.subtype_injective C
  have hcardKq : Nat.card Kq = C.index := by
    have hrel := rel_index_card_map_quotient12
      (inferInstance : N.Normal) hNK.le
    calc
      Nat.card Kq = N.relIndex KJ := by
        simpa only [qmap, Kq] using hrel.symm
      _ = C.index := by
        change (N.subgroupOf KJ).index = C.index
        rw [hNsub]
  have hmapC : C.map eK.toMonoidHom = _root_.commutator K := by
    dsimp only [C]
    rw [map_commutator_eq,
      MonoidHom.range_eq_top.mpr eK.surjective]
    exact (_root_.commutator_def K).symm
  have hindexC : C.index = (_root_.commutator K).index := by
    calc
      C.index = (C.map eK.toMonoidHom).index :=
        (Subgroup.index_map_equiv C eK).symm
      _ = (_root_.commutator K).index :=
        congrArg Subgroup.index hmapC
  have hcardKqSmall : Nat.card Kq < 4 := by
    rw [hcardKq, hindexC]
    simpa only [K] using hsmall
  obtain ⟨_hxP0, hxM, hxL, _hxFL, _hxNotFM⟩ :=
    witness_x_fitting_position12 ctx w
  have hxI : w.x ∈ I := ⟨hxM, hxL⟩
  let xI : I := ⟨w.x, hxI⟩
  have hxIOrder : orderOf xI = p :=
    (orderOf_injective I.subtype I.subtype_injective xI).symm.trans
      (witness_order12 ctx w)
  have hpExpI : p ∣ Monoid.exponent I := by
    rw [← hxIOrder]
    exact Monoid.order_dvd_exponent xI
  have hpU0 : p ∣ Nat.card U0 := by
    have hpExpU0 : p ∣ Monoid.exponent U0 := by
      simpa only [hU0.2.1] using hpExpI
    exact hpExpU0.trans Group.exponent_dvd_nat_card
  have hRqInj : Function.Injective (qmap.subgroupMap UJ) := by
    simpa only [qmap] using
      hFrob0.quotientComplement_subgroupMap_injective hNK.le
  have hcardRq : Nat.card Rq = Nat.card U0 := by
    calc
      Nat.card Rq = Nat.card UJ := by
        let eRq : UJ ≃* UJ.map qmap :=
          MulEquiv.ofBijective (qmap.subgroupMap UJ)
            ⟨hRqInj, qmap.subgroupMap_surjective UJ⟩
        simpa only [Rq] using (Nat.card_congr eRq.toEquiv).symm
      _ = Nat.card U0 := by
        simpa only [UJ, J] using
          Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
            (show U0 ≤ K ⊔ U0 from le_sup_right)
  have hpRq : p ∣ Nat.card Rq := by
    simpa only [hcardRq] using hpU0
  have hpOdd : Odd p := by
    obtain ⟨A, _hAP0, hA⟩ := w.P0_rank_two.1
    have hpA : p ∣ Nat.card A := by
      rw [hA.card_eq]
      exact dvd_pow_self p (by omega : 2 ≠ 0)
    exact Odd.of_dvd_nat (mFT_odd A) hpA
  have hpThree : 3 ≤ p := by
    have hpTwo := ctx.p_prime.two_le
    obtain ⟨k, hk⟩ := hpOdd
    omega
  exact (not_lt_of_ge
    (frobenius_kernel_card_ge_four12 hFrobQ hpThree hpRq))
    hcardKqSmall

/-! ## Development boundary -/

private theorem nonFrobenius_character_core12
    {p : ℕ} {M P0 : Subgroup G}
    (ctx : FTType1NonFrobeniusContext p M P0)
    (w : NonFrobeniusFTType1Witness p M P0) : False := by
  classical
  obtain ⟨E, hFrobL, hsdM, hinter, _hEcyclic, hdiv⟩ :=
    FTType1NonFrobeniusInternal.nonFrobenius_group_bridge12 ctx w
  let fctxL : FTFrobeniusContext w.L :=
    ⟨w.L_maximal, ⟨E, hFrobL⟩⟩
  let ctxL : FTType1Context w.L :=
    ⟨w.L_maximal, FT_Frobenius_type1 fctxL⟩
  let H : Subgroup w.L := FTType1FittingIn w.L
  letI : H.Normal := by
    simpa only [H, FTType1FittingIn] using Fcore_normal w.L
  have hFrobHE : IsFrobeniusDecomposition H (E.subgroupOf w.L) := by
    simpa only [H] using frobeniusIn_decomposition12 hFrobL
  letI : IsSolvable w.L := mFT_sol (mmax_proper w.L_maximal)
  letI : IsSolvable H := inferInstance
  letI : Nontrivial H :=
    H.nontrivial_iff_ne_bot.mpr hFrobHE.kernel_ne_bot
  have hbot : (⊥ : Subgroup H) < ⊤ :=
    bot_lt_iff_ne_bot.mpr top_ne_bot
  obtain ⟨phi, hphi, hphiOne⟩ :=
    exists_linInd H (⊥ : Subgroup H) hbot
  have hphiFamily : phi ∈ FTType1SeqIndFamily w.L := by
    simpa only [H, FTType1SeqIndFamily] using hphi
  let zeta : IrreducibleCharacter w.L ℂ :=
    ⟨phi, (FT_Frobenius_coherence fctxL).seqInd_irreducible
      phi hphiFamily⟩
  have hzeta : (zeta : ClassFunction w.L ℂ) ∈
      FTType1SeqIndFamily w.L := by
    simpa only [zeta] using hphiFamily
  have hzeta1 : zeta 1 = ((FTType1FittingIn w.L).index : ℂ) := by
    simpa only [zeta, H] using hphiOne
  obtain ⟨nu, hcohFrob⟩ :=
    (FT_Frobenius_coherence fctxL).coherent_family
  have hcohL : coherent_with
      (FTType1SeqIndFamily w.L : Set (ClassFunction w.L ℂ))
      (nonidentitySet w.L) ctxL.tau nu := by
    simpa only [ctxL, fctxL, FTFrobeniusContext.tau,
      FTType1Context.tau] using hcohFrob
  have hcohTop : coherent_with
      (FTType1SeqIndFamily w.L : Set (ClassFunction w.L ℂ))
      (nonidentitySet w.L)
      (Dade (FT_DadeF_hyp w.L w.L_maximal))
      (characterSourceMap12.comp nu) :=
    type1_fitting_coherence_top12 ctxL nu hcohL
  obtain ⟨hpsiVirtual, hpsiNorm, hpsiOne⟩ :=
    coherent_image_norm_one12 nu hcohL zeta hzeta
  have hcohNeeded : coherent_with
      (FTType1SeqIndFamily w.L : Set (ClassFunction w.L ℂ))
      (nonidentitySet w.L)
      (FTType1Context.tau ⟨w.L_maximal,
        FT_Frobenius_type1 ⟨w.L_maximal, ⟨E, hFrobL⟩⟩⟩) nu := by
    simpa only [ctxL, fctxL] using hcohL
  obtain ⟨hrhoM, hconstant, hinteger⟩ :=
    rhoM_shell_structure12 ctx w hFrobL nu hcohNeeded hzeta
  obtain ⟨hcoset0, _hrhoL⟩ :=
    rhoL_coherent_value12 ctx w hFrobL hdiv nu hcohNeeded
      zeta hzeta hzeta1
  let hxL : w.x ∈ w.L :=
    (witness_x_fitting_position12 ctx w).2.2.1
  have hcoset : ∀ g : G, g ∈ Fitting_core M →
      nu zeta (w.x * g) = zeta ⟨w.x, hxL⟩ := by
    simpa only [hxL] using hcoset0
  have hlowerValue := fitting_shell_value_lower12
    ctx w hFrobL hdiv (nu zeta) hpsiVirtual zeta hzeta1 hxL
      hcoset hconstant hinteger
  have hrhoRaw : ∀ (g : G)
      (hg : g ∈ subgroupNonidentity (Fitting_core M)),
      invDade (FT_DadeF_hyp M ctx.M_type_context.maxL)
          (characterSourceMap12 (nu zeta))
          ⟨g, Fcore_sub M hg.1⟩ = nu zeta g := by
    intro g hg
    change ctx.M_type_context.rho (nu zeta)
      ⟨g, Fcore_sub M hg.1⟩ = nu zeta g
    exact hrhoM g hg
  let normM : ℝ := classFunctionNormSq
    (invDade (FT_DadeF_hyp M ctx.M_type_context.maxL)
      (characterSourceMap12 (nu zeta)))
  let normL : ℝ := classFunctionNormSq
    (invDade (FT_DadeF_hyp w.L w.L_maximal)
      (characterSourceMap12 (nu zeta)))
  have hlowerM :
      (Nat.card M : ℝ)⁻¹ *
          (Nat.card (Fitting_core M) -
            Nat.card (derivedWithin (Fitting_core M)) : ℕ) *
          ((Nat.card E : ℝ) - 1) ^ 2 ≤ normM := by
    simpa only [normM] using
      first_fitting_norm_lower12 ctx (E := E) (nu zeta)
        hrhoRaw hlowerValue
  have hlowerL :
      1 - (Nat.card E : ℝ) /
          (Nat.card (Fitting_core w.L) : ℝ) ≤ normL := by
    simpa only [normL, LinearMap.comp_apply] using
      second_fitting_norm_lower12 ctx w hFrobL nu hcohTop
        zeta hzeta hzeta1
  have hupper : normM + normL < 1 := by
    simpa only [normM, normL] using
      two_fitting_invDade_norm_lt_one12
        ctx.M_type_context.maxL w.L_maximal
        (fitting_dade_supports_disjoint12 ctx w hFrobL)
        (nu zeta) hpsiNorm hpsiOne
  have hsmall : (_root_.commutator (Fitting_core M)).index < 4 :=
    fitting_abelianization_lt_four12 w hFrobL hsdM hinter
      normM normL hlowerM hlowerL hupper
  exact small_abelianization_frobenius_contradiction12
    ctx w hsdM hsmall

/-! ## Mapped endpoints -/

theorem FTtype1_nonFrobenius_witness_contradiction
    {p : ℕ} {M P0 : Subgroup G}
    (ctx : FTType1NonFrobeniusContext p M P0)
    (w : NonFrobeniusFTType1Witness p M P0) : False :=
  nonFrobenius_character_core12 ctx w

theorem FTtype1_nonFrobenius_contradiction
    {p : ℕ} {M P0 : Subgroup G}
    (ctx : FTType1NonFrobeniusContext p M P0) : False := by
  obtain ⟨w⟩ := non_Frobenius_FTtype1_witness ctx
  exact FTtype1_nonFrobenius_witness_contradiction ctx w

end

end Submission.OddOrder.PF
