import Mathlib.Tactic
import Submission.OddOrder.BG.AppendixC
import Submission.OddOrder.PF.Section13.FTTypePSupportBridges

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.AppendixC
open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open scoped BigOperators Classical Pointwise

universe u

variable {G : Type} [Group G] [Finite G] [IsMinSimpleOddGroup G]

local instance (priority := 10) fgxFintype
    (X : Type*) [Finite X] : Fintype X :=
  Fintype.ofFinite X

local instance fgxInvertibleCard
    {Q : Type*} [Group Q] [Fintype Q] :
    Invertible (Nat.card Q : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-! Fresh public-API-only copies of PF13's private top-subgroup adapters. -/

private noncomputable def fgxSourceMap :
    ClassFunction G ℂ →ₗ[ℂ] ClassFunction (⊤ : Subgroup G) ℂ :=
  ClassFunction.comap Subgroup.topEquiv.toMonoidHom

private noncomputable def fgxTargetMap :
    ClassFunction (⊤ : Subgroup G) ℂ →ₗ[ℂ] ClassFunction G ℂ :=
  ClassFunction.comap Subgroup.topEquiv.symm.toMonoidHom

@[simp] private theorem fgx_source_target
    (f : ClassFunction (⊤ : Subgroup G) ℂ) :
    fgxSourceMap (fgxTargetMap f) = f := by
  ext x
  simpa [fgxSourceMap, fgxTargetMap, ClassFunction.comap_apply] using
    congrArg f (Subgroup.topEquiv.symm_apply_apply x)

@[simp] private theorem fgx_target_source
    (f : ClassFunction G ℂ) :
    fgxTargetMap (fgxSourceMap f) = f := by
  ext x
  simpa [fgxSourceMap, fgxTargetMap, ClassFunction.comap_apply] using
    congrArg f (Subgroup.topEquiv.apply_symm_apply x)

private theorem fgx_target_pairing
    (f g : ClassFunction (⊤ : Subgroup G) ℂ) :
    characterPairing (fgxTargetMap f) (fgxTargetMap g) =
      characterPairing f g := by
  have hcard : Nat.card G = Nat.card (⊤ : Subgroup G) :=
    Nat.card_congr Subgroup.topEquiv.symm.toEquiv
  unfold characterPairing
  rw [hcard]
  congr 1
  apply Fintype.sum_equiv Subgroup.topEquiv.symm.toEquiv
  intro x
  simp [fgxTargetMap, ClassFunction.comap_apply]

private theorem fgx_target_starPairing
    (f g : ClassFunction (⊤ : Subgroup G) ℂ) :
    starCharacterPairing (fgxTargetMap f) (fgxTargetMap g) =
      starCharacterPairing f g := by
  have hcard : Nat.card G = Nat.card (⊤ : Subgroup G) :=
    Nat.card_congr Subgroup.topEquiv.symm.toEquiv
  unfold starCharacterPairing twistedCharacterPairing
  rw [hcard]
  congr 1
  apply Fintype.sum_equiv Subgroup.topEquiv.symm.toEquiv
  intro x
  simp [fgxTargetMap, ClassFunction.comap_apply]

private theorem fgx_target_normSq
    (f : ClassFunction (⊤ : Subgroup G) ℂ) :
    classFunctionNormSq (fgxTargetMap f) = classFunctionNormSq f := by
  rw [classFunctionNormSq_eq_re_starCharacterPairing,
    fgx_target_starPairing,
    ← classFunctionNormSq_eq_re_starCharacterPairing]

private theorem fgx_source_pairing
    (f g : ClassFunction G ℂ) :
    characterPairing (fgxSourceMap f) (fgxSourceMap g) =
      characterPairing f g := by
  rw [← fgx_target_pairing (fgxSourceMap f) (fgxSourceMap g)]
  simp

private theorem fgx_target_virtual
    {f : ClassFunction (⊤ : Subgroup G) ℂ}
    (hf : ClassFunction.IsVirtual f) :
    ClassFunction.IsVirtual (fgxTargetMap f) := by
  obtain ⟨z, rfl⟩ := hf
  refine ⟨VirtualCharacter.comap
    Subgroup.topEquiv.symm.toMonoidHom z, ?_⟩
  rw [VirtualCharacter.realize_comap]
  rfl

private theorem fgx_source_virtual
    {f : ClassFunction G ℂ} (hf : ClassFunction.IsVirtual f) :
    ClassFunction.IsVirtual (fgxSourceMap f) := by
  obtain ⟨z, rfl⟩ := hf
  refine ⟨VirtualCharacter.comap Subgroup.topEquiv.toMonoidHom z, ?_⟩
  rw [VirtualCharacter.realize_comap]
  rfl

private theorem fgx_coherence_top
    {L : Subgroup G}
    {maxL : L ∈ minSimple_max_groups (G := G)}
    {tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    (hcoh : coherent_with
      (↑(FTType1SeqIndFamily L) : Set (ClassFunction L ℂ))
      (nonidentitySet L) (FTtype1Dade L maxL) tau) :
    coherent_with
      (↑(FTType1SeqIndFamily L) : Set (ClassFunction L ℂ))
      (nonidentitySet L) (Dade (FT_DadeF_hyp L maxL))
      (fgxSourceMap.comp tau) := by
  refine
    { isometry := ?_
      mapsToVirtual := ?_
      agrees := ?_ }
  · intro xi hxi mu hmu
    simpa [LinearMap.comp_apply] using
      (fgx_source_pairing (tau xi) (tau mu)).trans
        (hcoh.isometry xi hxi mu hmu)
  · intro xi hxi
    exact fgx_source_virtual (hcoh.mapsToVirtual xi hxi)
  · intro xi hxi hxiOn
    change fgxSourceMap (tau xi) = Dade (FT_DadeF_hyp L maxL) xi
    rw [hcoh.agrees xi hxi hxiOn]
    change fgxSourceMap
      (fgxTargetMap (Dade (FT_DadeF_hyp L maxL) xi)) = _
    exact fgx_source_target _

private theorem fgx_target_dadeInd1Beta
    {L : Subgroup G} (maxL : L ∈ minSimple_max_groups (G := G))
    (dd : DadeHypothesis (⊤ : Subgroup G) L
      (subgroupNonidentity
        ((FTType1FittingIn L).map L.subtype)))
    (phi : ClassFunction L ℂ) :
    fgxTargetMap
        (dadeInd1Beta (FTType1FittingIn L) dd phi) =
      FTtype1Dade L maxL (FTtype1Bridge L phi) := by
  simpa only [dadeInd1Beta, dadeInducedTrivial, FTtype1Dade,
    FTtype1Bridge, fgxTargetMap, LinearMap.comp_apply,
    FTType1FittingIn,
    Subgroup.map_subgroupOf_eq_of_le (Fcore_sub L)]

private theorem characterPairing_sub_left'
    {Q : Type*} [Group Q] [Fintype Q]
    (f g z : ClassFunction Q ℂ) :
    characterPairing (f - g) z =
      characterPairing f z - characterPairing g z := by
  change characterPairingRight z (f - g) = _
  exact map_sub (characterPairingRight z) f g

private theorem characterPairing_sub_right'
    {Q : Type*} [Group Q] [Fintype Q]
    (z f g : ClassFunction Q ℂ) :
    characterPairing z (f - g) =
      characterPairing z f - characterPairing z g := by
  change characterPairingLeft z (f - g) = _
  exact map_sub (characterPairingLeft z) f g

private theorem fgx_characterPairing_fintype_sum_left
    {Q I : Type*} [Group Q] [Fintype Q] [Fintype I]
    (f : I → ClassFunction Q ℂ) (g : ClassFunction Q ℂ) :
    characterPairing (∑ i, f i) g =
      ∑ i, characterPairing (f i) g := by
  change characterPairingRight g (∑ i, f i) = _
  exact map_sum (characterPairingRight g) f Finset.univ

private theorem fgx_characterPairing_fintype_sum_right
    {Q I : Type*} [Group Q] [Fintype Q] [Fintype I]
    (f : ClassFunction Q ℂ) (g : I → ClassFunction Q ℂ) :
    characterPairing f (∑ i, g i) =
      ∑ i, characterPairing f (g i) := by
  change characterPairingLeft f (∑ i, g i) = _
  exact map_sum (characterPairingLeft f) g Finset.univ

private theorem fgx_characterPairing_finset_sum_left
    {Q I : Type*} [Group Q] [Fintype Q]
    (s : Finset I) (f : I → ClassFunction Q ℂ)
    (g : ClassFunction Q ℂ) :
    characterPairing (∑ i ∈ s, f i) g =
      ∑ i ∈ s, characterPairing (f i) g := by
  exact map_sum (characterPairingRight g) (fun i ↦ f i) s

private theorem fgx_Dade_support_eq_of_set_eq
    {Γ : Type*} [Group Γ]
    {K L : Subgroup Γ} {A B : Set Γ}
    (hAB : A = B) (ddA : DadeHypothesis K L A)
    (ddB : DadeHypothesis K L B) :
    Dade_support ddA = Dade_support ddB := by
  subst B
  congr

/-! Sign and norm-one identification helpers for the final residual. -/

private theorem fgx_signed_norm_one_eq_of_pairing_one
    {Q : Type*} [Group Q] [Fintype Q]
    {f g : ClassFunction Q ℂ}
    (hfV : ClassFunction.IsVirtual f)
    (hfN : characterPairing f f = 1)
    (hgV : ClassFunction.IsVirtual g)
    (hgN : characterPairing g g = 1)
    (hfg : characterPairing f g = 1) : f = g := by
  obtain ⟨chi, eps, heps, hf⟩ :=
    FTType1InfrastructureInternal.existsSignedIrreducibleOfVirtualNormOne
      hfV hfN
  obtain ⟨psi, delta, hdelta, hg⟩ :=
    FTType1InfrastructureInternal.existsSignedIrreducibleOfVirtualNormOne
      hgV hgN
  rw [hf, hg] at hfg ⊢
  rcases heps with rfl | rfl <;>
    rcases hdelta with rfl | rfl <;>
    by_cases hchi : chi = psi <;>
    simp [characterPairing_smul_left, characterPairing_smul_right,
      IrreducibleCharacter.characterPairing_eq_ite, hchi] at hfg ⊢ <;>
    norm_num at hfg

private theorem fgx_signed_norm_one_eq_neg_of_pairing_neg_one
    {Q : Type*} [Group Q] [Fintype Q]
    {f g : ClassFunction Q ℂ}
    (hfV : ClassFunction.IsVirtual f)
    (hfN : characterPairing f f = 1)
    (hgV : ClassFunction.IsVirtual g)
    (hgN : characterPairing g g = 1)
    (hfg : characterPairing f g = -1) : f = -g := by
  have hnegV : ClassFunction.IsVirtual (-g) := hgV.neg
  have hnegN : characterPairing (-g) (-g) = 1 := by
    rw [← neg_one_smul ℂ g, characterPairing_smul_left,
      characterPairing_smul_right, hgN]
    norm_num
  have hpair : characterPairing f (-g) = 1 := by
    rw [← neg_one_smul ℂ g, characterPairing_smul_right, hfg]
    norm_num
  exact fgx_signed_norm_one_eq_of_pairing_one hfV hfN hnegV hnegN hpair

private theorem fgx_residual_identification
    {chi tauPhi tauInv : ClassFunction G ℂ}
    (hchiV : ClassFunction.IsVirtual chi)
    (hchiN : characterPairing chi chi = 1)
    (hphiV : ClassFunction.IsVirtual tauPhi)
    (hphiN : characterPairing tauPhi tauPhi = 1)
    (hinvV : ClassFunction.IsVirtual tauInv)
    (hinvN : characterPairing tauInv tauInv = 1)
    (hpair : characterPairing chi tauPhi = 1 ∨
      characterPairing chi tauInv = -1) :
    chi = tauPhi ∨ chi = -tauInv := by
  rcases hpair with hpair | hpair
  · exact Or.inl
      (fgx_signed_norm_one_eq_of_pairing_one
        hchiV hchiN hphiV hphiN hpair)
  · exact Or.inr
      (fgx_signed_norm_one_eq_neg_of_pairing_neg_one
        hchiV hchiN hinvV hinvN hpair)

/-! Convert a finite grid of integral signs to the exact Boolean syntax in
the PF14 conclusion. -/

private theorem fgx_bool_signed_rectangle
    {Q I J : Type*} [Group Q] [Fintype Q] [Fintype I] [Fintype J]
    (eta : I → J → ClassFunction Q ℂ)
    (s : I → J → ℤ) (hs : ∀ i j, IsSign (s i j)) :
    ∃ eps : I → J → Bool,
      (∑ i, ∑ j, (s i j : ℂ) • eta i j) =
        ∑ i, ∑ j, if eps i j then -(eta i j) else eta i j := by
  let eps : I → J → Bool := fun i j ↦ decide (s i j = -1)
  refine ⟨eps, ?_⟩
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rcases hs i j with hij | hij
  · simp [eps, hij]
  · calc
      (s i j : ℂ) • eta i j = (-1 : ℂ) • eta i j := by
        rw [hij]
        norm_num
      _ = -eta i j := neg_one_smul ℂ (eta i j)
      _ = (if eps i j then -(eta i j) else eta i j) := by
        simp [eps, hij]

/-! The numerical consequence of the semidirect-product disjunction in
`FTtypeII_support_facts`, including its conjugate branch. -/

private theorem fgx_type1CoreIndex_le_product
    {S T U V W W₁ W₂ L : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    {xdefW : IsInternalDirectProductIn W₂ W₁ W}
    (ctxS : FTTypePSetupContext S U W W₁ W₂ defW)
    (ctxT : FTTypePSetupContext T V W W₂ W₁ xdefW)
    (pairST : typeP_pair S T W W₁ W₂ defW)
    (Stype2 : FTtype S = 2)
    (maxNU_L : L ∈ minSimple_max_groups_of (G := G)
      (Subgroup.normalizer (U : Set G) : Set G)) :
    FTtype1CoreIndex L ≤ Nat.card W₂ * Nat.card W₁ := by
  obtain ⟨_hFrob, _hUL, hsd⟩ :=
    FTtypeII_support_facts ctxS T L Stype2 pairST maxNU_L
  obtain ⟨hq, hp⟩ :=
    FTtypeP_pair_primes S T W W₁ W₂ defW pairST
  have hqp : Nat.card W₁ ≠ Nat.card W₂ :=
    pairST.cyclic_ti.factor_card_ne
  rcases hsd with hsd | ⟨y, hyT, hsd⟩
  · have he : FTtype1CoreIndex L = Nat.card W₁ := by
      change ((Fitting_core L).subgroupOf L).index = Nat.card W₁
      exact hsd.2.2.2.symm.index_eq_card.trans
        (MathlibSupport.natCard_subgroupOf_eq hsd.2.1)
    rw [he]
    exact Nat.le_mul_of_pos_left (Nat.card W₁)
      (Nat.card_pos (α := W₂))
  · let Q : Subgroup G := Fitting_core T
    let W₂y : Subgroup G := conjugateSubgroup8 W₂ y
    letI : IsMulCommutative Q :=
      (FTtypeP_facts ctxT).2.2.2.2.1.commutative
    have hW₁Q : W₁ ≤ Q := ctxT.StypeP.2.2.2.1.2.2.1
    have hcardW₂y : Nat.card W₂y = Nat.card W₂ := by
      dsimp only [W₂y, conjugateSubgroup8]
      rw [Subgroup.card_map_of_injective (MulAut.conj y).injective]
    have hW₁cent : W₁ ≤ Subgroup.centralizer (W₂y : Set G) := by
      intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rcases hz with ⟨z₀, hz₀, rfl⟩
      have hyw : Commute y w := by
        exact congrArg Subtype.val
          (mul_comm' (⟨y, by simpa only [Q] using hyT⟩ : Q)
            (⟨w, hW₁Q hw⟩ : Q))
      have hwz : Commute w z₀ :=
        defW.commute ⟨w, hw⟩ ⟨z₀, hz₀⟩
      have hwConj : Commute w (y * z₀ * y⁻¹) :=
        (hyw.symm.mul_right hwz).mul_right hyw.symm.inv_right
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
        hwConj.symm.eq
    have hW₁norm : W₁ ≤ Subgroup.normalizer (W₂y : Set G) :=
      hW₁cent.trans (Subgroup.centralizer_le_normalizer (W₂y : Set G))
    have hcop : Nat.Coprime (Nat.card W₁) (Nat.card W₂y) := by
      rw [hcardW₂y]
      exact (Nat.coprime_primes hq hp).mpr hqp
    have hdis : Disjoint W₁ W₂y :=
      Subgroup.disjoint_of_coprime_natCard hcop
    have hjoin : Nat.card (W₁ ⊔ W₂y : Subgroup G) =
        Nat.card W₁ * Nat.card W₂ := by
      rw [natCard_sup_eq_mul_of_disjoint_of_le_normalizer hdis hW₁norm,
        hcardW₂y]
    have he : FTtype1CoreIndex L =
        Nat.card (W₁ ⊔ W₂y : Subgroup G) := by
      change ((Fitting_core L).subgroupOf L).index =
        Nat.card (W₁ ⊔ W₂y : Subgroup G)
      exact hsd.2.2.2.symm.index_eq_card.trans
        (MathlibSupport.natCard_subgroupOf_eq hsd.2.1)
    rw [he, hjoin, Nat.mul_comm]

/-! ## Cardinality adapters for the Type-P estimates -/

private theorem fullGalois_classSupport_card
    {A : Set G} {N : Subgroup G}
    (hTI : IsNormalizedTI A (⊤ : Subgroup G) N) :
    (classSupportWithin (⊤ : Subgroup G) A).ncard =
      A.ncard * N.index := by
  let action := subgroupConjugationActionOnAmbient (⊤ : Subgroup G)
  letI : SMul (⊤ : Subgroup G) G := action.toSMul
  letI : MulAction (⊤ : Subgroup G) G := action.toMulAction
  letI : MulAction (⊤ : Subgroup G) (Set G) := Set.mulActionSet
  have hpartition := normalizedTI_classSupport_partition hTI
  change IsSetPartition (MulAction.orbit (⊤ : Subgroup G) A)
      (classSupportWithin (⊤ : Subgroup G) A) ∧
    (MulAction.orbit (⊤ : Subgroup G) A).ncard =
      N.relIndex (⊤ : Subgroup G) at hpartition
  have horbitFinite :
      (MulAction.orbit (⊤ : Subgroup G) A).Finite := Set.toFinite _
  have hblock : ∀ B ∈ MulAction.orbit (⊤ : Subgroup G) A,
      B.ncard = A.ncard := by
    intro B hB
    rcases hB with ⟨x, rfl⟩
    exact Set.ncard_smul_set x A
  rw [← hpartition.1.1]
  have hunion : ⋃₀ (MulAction.orbit (⊤ : Subgroup G) A) =
      ⋃ B ∈ MulAction.orbit (⊤ : Subgroup G) A, B := by
    ext x
    simp
  rw [hunion]
  calc
    (⋃ B ∈ MulAction.orbit (⊤ : Subgroup G) A, B).ncard =
        ∑ᶠ B ∈ MulAction.orbit (⊤ : Subgroup G) A, B.ncard :=
      horbitFinite.ncard_biUnion
        (fun B _ ↦ Set.toFinite B) hpartition.1.2.1
    _ = ∑ᶠ _B ∈ MulAction.orbit (⊤ : Subgroup G) A, A.ncard :=
      finsum_mem_congr rfl hblock
    _ = (∑ᶠ _B ∈ MulAction.orbit (⊤ : Subgroup G) A, (1 : ℕ)) *
          A.ncard := by
      rw [finsum_mem_mul' (fun _B : Set G ↦ 1) A.ncard horbitFinite]
      simp
    _ = (MulAction.orbit (⊤ : Subgroup G) A).ncard * A.ncard := by
      rw [finsum_one]
    _ = N.relIndex (⊤ : Subgroup G) * A.ncard := by
      rw [hpartition.2]
    _ = A.ncard * N.index := by
      rw [N.relIndex_top_right, Nat.mul_comm]

private theorem fullGalois_nonidentity_card (H : Subgroup G) :
    (subgroupNonidentity H).ncard = Nat.card H - 1 := by
  have hone : (1 : G) ∈ (H : Set G) := H.one_mem
  rw [show subgroupNonidentity H = (H : Set G) \ {1} by
    ext x
    simp [subgroupNonidentity, nonidentitySet]]
  rw [Set.ncard_sdiff_singleton_of_mem hone, ← Nat.card_coe_set_eq,
    SetLike.coe_sort_coe]

/-! ## Supplementary Type-P estimates -/

/-- `PFsection14.v: FTtypeP_complV_ltr`.

Oddness strengthens the Frobenius complement bound enough to compare the
two reciprocal denominators. -/
theorem FTtypeP_complV_ltr
    {S U W W₁ W₂ Wn : Subgroup G}
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (maxS : S ∈ minSimple_max_groups (G := G))
    (StypeP : of_typeP S U W W₁ W₂ defW)
    (hWn : Nat.card Wn ≤ Nat.card W₁) :
    ((Nat.card U * Nat.card W₁ : ℕ) : ℝ)⁻¹ <
      ((2 * Nat.card Wn ^ 2 : ℕ) : ℝ)⁻¹ := by
  let ctx : FTTypePSetupContext S U W W₁ W₂ defW := ⟨maxS, StypeP⟩
  have hfrobProduct : PTypeFrobeniusProduct U W₁ :=
    Ptype_compl_Frobenius ctx.ptypeCtx
  let J : Subgroup G := U ⊔ W₁
  let UJ : Subgroup J := U.subgroupOf J
  let WJ : Subgroup J := W₁.subgroupOf J
  have hfrob : IsFrobeniusDecomposition UJ WJ := by
    simpa only [PTypeFrobeniusProduct, J, UJ, WJ] using hfrobProduct
  have hindex : UJ.index = Nat.card W₁ := by
    calc
      UJ.index = Nat.card WJ := hfrob.isComplement.symm.index_eq_card
      _ = Nat.card W₁ :=
        MathlibSupport.natCard_subgroupOf_eq
          (show W₁ ≤ J from le_sup_right)
  have hcardU : Nat.card UJ = Nat.card U :=
    MathlibSupport.natCard_subgroupOf_eq
      (show U ≤ J from le_sup_left)
  have hbound := odd_Frobenius_index_ler UJ WJ (mFT_odd J) hfrob
  rw [hindex, hcardU] at hbound
  have hqpos : (0 : ℝ) < Nat.card W₁ := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card W₁)
  have hWnpos : (0 : ℝ) < Nat.card Wn := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card Wn)
  have hWnReal : (Nat.card Wn : ℝ) ≤ Nat.card W₁ := by
    exact_mod_cast hWn
  have htwoq : (2 : ℝ) * Nat.card W₁ < Nat.card U := by
    nlinarith
  have hsquares :
      (Nat.card Wn : ℝ) ^ 2 ≤ (Nat.card W₁ : ℝ) ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ Nat.card Wn by positivity]
  have hscaled := mul_lt_mul_of_pos_right htwoq hqpos
  have hden :
      ((2 * Nat.card Wn ^ 2 : ℕ) : ℝ) <
        ((Nat.card U * Nat.card W₁ : ℕ) : ℝ) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    nlinarith
  have hdenpos : (0 : ℝ) < ((2 * Nat.card Wn ^ 2 : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using
      mul_pos (show (0 : ℝ) < 2 by norm_num) (pow_pos hWnpos 2)
  simpa only [one_div] using one_div_lt_one_div_of_lt hdenpos hden

/- The two kernel-triviality endpoints turn the faithful Galois action on the
F-core factor into an honest Frobenius action on the F-core itself. -/
private theorem typePGalois_fcore_frobenius14
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (hGal : ctx.galoisAlternative) :
    PTypeFrobeniusProduct ctx.P U := by
  let data := typeP_Galois_P ctx.actionHypotheses hGal
  have hreg : IsSemiregularConjugation ctx.P U := by
    intro x hx h hfix
    have hxC : x ∉ ctx.D.C := by
      intro hxC
      have hxKer : x ∈ (ptypeFCoreAction ctx.ptypeCtx).ker := by
        simpa only [Ptype_factor_action_C] using hxC
      have hxAmbient : (x : G) ∈ Ptype_Fcompl_kernel ctx.ptypeCtx :=
        ⟨x, hxKer, rfl⟩
      rw [Ptype_Fcompl_kernel_trivial ctx] at hxAmbient
      apply hx
      apply Subtype.ext
      exact Subgroup.mem_bot.mp hxAmbient
    let hbar : ptypeFCoreFactor ctx.ptypeCtx :=
      QuotientGroup.mk'
        ((Ptype_Fcore_kernel ctx.ptypeCtx).subgroupOf ctx.P) h
    have hbarFix : ctx.D.U_action x hbar = hbar := by
      change ptypeFCoreAction ctx.ptypeCtx x
          (QuotientGroup.mk'
            ((Ptype_Fcore_kernel ctx.ptypeCtx).subgroupOf ctx.P) h) =
        QuotientGroup.mk'
          ((Ptype_Fcore_kernel ctx.ptypeCtx).subgroupOf ctx.P) h
      rw [ptypeFCoreAction, subgroupConjugationFactorHom_apply_mk]
      apply QuotientGroup.eq.mpr
      change
        (((x : G) * (h : G) * (x : G)⁻¹)⁻¹ * (h : G)) ∈
          Ptype_Fcore_kernel ctx.ptypeCtx
      rw [hfix]
      simp
    have hbarOne : hbar = 1 :=
      PTypeGaloisLocalFrobeniusInternal.pTypeGalois_action_fixed_eq_one
        data x hbar hxC hbarFix
    have hhKernel : h ∈
        (Ptype_Fcore_kernel ctx.ptypeCtx).subgroupOf ctx.P :=
      QuotientGroup.eq_one_iff h |>.mp hbarOne
    have hhBot : (h : G) ∈ (⊥ : Subgroup G) := by
      rw [← Ptype_Fcore_kernel_trivial ctx]
      exact hhKernel
    apply Subtype.ext
    exact Subgroup.mem_bot.mp hhBot
  have hinner : IsInternalSemidirectProductIn ctx.P U ctx.PU :=
    ctx.StypeP.2.1.2.2.2
  have hnorm : U ≤ Subgroup.normalizer (ctx.P : Set G) :=
    hinner.2.1.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hinner.1).mp
        hinner.2.2.1)
  have hPne : ctx.P ≠ ⊥ := by
    intro hP
    apply ctx.StypeP.2.2.2.1.2.1
    rw [eq_bot_iff]
    exact ctx.StypeP.2.2.2.1.2.2.1.trans (le_of_eq hP)
  have hUne : U ≠ ⊥ :=
    (compl_of_typeII_IV S U W W₁ W₂ defW ctx.maxS ctx.StypeP
      ctx.notType5).2.1
  have hfrob := hreg.isFrobeniusDecomposition_sup hnorm hPne hUne
  rw [sup_comm U ctx.P] at hfrob
  exact hfrob

/- A nonidentity kernel element of a Frobenius decomposition has its whole
centralizer in the kernel. -/
private theorem typePGalois_centralizer_frobeniusKernel_le14
    {Q : Type*} [Group Q] [Finite Q]
    {K R : Subgroup Q}
    (hFrob : IsFrobeniusDecomposition K R)
    {z : Q} (hzK : z ∈ K) (hzOne : z ≠ 1) :
    Subgroup.centralizer (Subgroup.zpowers z : Set Q) ≤ K := by
  intro x hx
  by_contra hxK
  obtain ⟨k, r, hrR, hrx⟩ :=
    hFrob.exists_kernel_conjugate_complement_of_not_mem hxK
  have hrx' : (k : Q) * r * (k : Q)⁻¹ = x := by
    simpa [MulAut.conj_apply] using hrx
  let rR : R := ⟨r, hrR⟩
  have hrRne : rR ≠ 1 := by
    intro hrOne
    apply hxK
    have hrOneQ : r = 1 := congrArg Subtype.val hrOne
    have hxOne : x = 1 := by
      calc
        x = (k : Q) * r * (k : Q)⁻¹ := hrx'.symm
        _ = 1 := by rw [hrOneQ]; simp
    exact hxOne ▸ K.one_mem
  have hzKconj : (k : Q)⁻¹ * z * (k : Q) ∈ K := by
    simpa using hFrob.kernel_normal.conj_mem z hzK (k : Q)⁻¹
  let zK : K := ⟨(k : Q)⁻¹ * z * (k : Q), hzKconj⟩
  have hzKne : zK ≠ 1 := by
    intro hzKOne
    apply hzOne
    have hval := congrArg Subtype.val hzKOne
    dsimp only [zK] at hval
    calc
      z = (k : Q) * ((k : Q)⁻¹ * z * (k : Q)) * (k : Q)⁻¹ := by
        group
      _ = 1 := by rw [hval]; simp
  have hxcomm : Commute x z := by
    exact (Subgroup.mem_centralizer_iff.mp hx z
      (Subgroup.mem_zpowers z)).symm
  have hxfix : x * z * x⁻¹ = z := by
    calc
      x * z * x⁻¹ = z * x * x⁻¹ := by rw [hxcomm.eq]
      _ = z := by simp
  have hfix : (rR : Q) * (zK : Q) * (rR : Q)⁻¹ = (zK : Q) := by
    change r * ((k : Q)⁻¹ * z * (k : Q)) * r⁻¹ =
      (k : Q)⁻¹ * z * (k : Q)
    calc
      r * ((k : Q)⁻¹ * z * (k : Q)) * r⁻¹ =
          (k : Q)⁻¹ *
            (((k : Q) * r * (k : Q)⁻¹) * z *
              ((k : Q) * r * (k : Q)⁻¹)⁻¹) * (k : Q) := by
        group
      _ = (k : Q)⁻¹ * (x * z * x⁻¹) * (k : Q) := by rw [hrx']
      _ = (k : Q)⁻¹ * z * (k : Q) := by rw [hxfix]
  exact hzKne (hFrob.fixedPointFree rR hrRne zK hfix)

/- The outer semidirect product and Peterfalvi's coprime right-coset
partition put every element outside `S'` into an ambient conjugate of `W`. -/
private theorem typePGalois_outer_W_support14
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (z : S) (hzD : (z : G) ∉ derivedWithin S) :
    (z : G) ∈ classSupportWithin (⊤ : Subgroup G)
      (subgroupNonidentity W) := by
  rcases ctx.primeTI.semidirect_complement.2 z with
    ⟨⟨dS, xS⟩, hdxS⟩
  let d : derivedWithin S :=
    ⟨((dS : S) : G), dS.property⟩
  let x : W₁ :=
    ⟨((xS : S) : G), xS.property⟩
  have hzx : (d : G) * (x : G) = (z : G) := by
    simpa [d, x] using congrArg Subtype.val hdxS
  have hx : x ≠ 1 := by
    intro hxOne
    apply hzD
    have hzEq : (d : G) = (z : G) := by
      simpa [hxOne] using hzx
    rw [← hzEq]
    exact d.property
  have hxNorm :
      (x : G) ∈ Subgroup.normalizer (derivedWithin S : Set G) :=
    ctx.primeTI.group_le_normalizer_kernel
      (ctx.primeTI.complement_le_group x.property)
  have hxCop : Nat.Coprime (Nat.card (derivedWithin S)) (orderOf (x : G)) :=
    ctx.primeTI.kernel_complement_card_coprime.coprime_dvd_right
      (W₁.orderOf_dvd_natCard x.property)
  have hpart := partition_cent_rcoset
    (derivedWithin S) (x : G) hxNorm hxCop
  let conjugationAction :=
    subgroupConjugationActionOnAmbient (derivedWithin S)
  letI : SMul (derivedWithin S) G := conjugationAction.toSMul
  letI : MulAction (derivedWithin S) G := conjugationAction.toMulAction
  letI : MulAction (derivedWithin S) (Set G) := Set.mulActionSet
  let C := centralizerWithin (derivedWithin S) (Subgroup.zpowers (x : G))
  have hC : C = W₂ := ctx.primeTI.centralizer_kernel x hx
  have hzCoset :
      (z : G) ∈ (derivedWithin S : Set G) * ({(x : G)} : Set G) :=
    Set.mem_mul.mpr
      ⟨(d : G), d.property, (x : G), by simp, hzx⟩
  have hzUnion : (z : G) ∈
      ⋃₀ (MulAction.orbit (derivedWithin S)
        ((C : Set G) * ({(x : G)} : Set G))) := by
    rw [hpart.1.1]
    exact hzCoset
  rcases Set.mem_sUnion.mp hzUnion with ⟨A, hA, hzA⟩
  rcases hA with ⟨y, rfl⟩
  rcases Set.mem_smul_set.mp hzA with ⟨v, hv, hvz⟩
  rcases Set.mem_mul.mp hv with ⟨c, hc, t, ht, hct⟩
  have htEq : t = (x : G) := Set.mem_singleton_iff.mp ht
  subst t
  have hconj :
      (z : G) = (y : G) * (c * (x : G)) * (y : G)⁻¹ := by
    change (y : G) * v * (y : G)⁻¹ = (z : G) at hvz
    rw [← hvz, ← hct]
  have hcW₂ : c ∈ W₂ := by
    rw [← hC]
    exact hc
  have hcxW : c * (x : G) ∈ W :=
    W.mul_mem (defW.right_le hcW₂) (defW.left_le x.property)
  have hcxOne : c * (x : G) ≠ 1 := by
    intro hcx
    let c₂ : W₂ := ⟨c, hcW₂⟩
    have hprodOne : defW.mulEquiv (x, c₂) = 1 := by
      apply Subtype.ext
      change (x : G) * c = 1
      rw [(defW.commute x c₂).eq, hcx]
    have hpairOne : (x, c₂) = (1, 1) := by
      apply defW.mulEquiv.injective
      simpa using hprodOne
    apply hx
    exact congrArg Prod.fst hpairOne
  refine ⟨c * (x : G), ⟨hcxW, hcxOne⟩,
    (y : G)⁻¹, Subgroup.mem_top _, ?_⟩
  simpa only [inv_inv] using hconj.symm

theorem coprime_typeP_Galois_core
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (g : G)
    (hGal : ctx.galoisAlternative)
    (hW : g ∉ classSupportWithin (⊤ : Subgroup G)
      (subgroupNonidentity W))
    (hP : g ∉ classSupportWithin (⊤ : Subgroup G)
      (subgroupNonidentity ctx.P)) :
    Nat.Coprime (orderOf g) ctx.p := by
  by_contra hcop
  obtain ⟨_, _, _, _, _, hPcard, _, _, hTI, _⟩ :=
    FTtypeP_facts ctx
  have hprimes :=
    FTtypeP_primes S U W W₁ W₂ defW ctx.maxS ctx.StypeP
  have hq : ctx.q.Prime := hprimes.1
  have hp : ctx.p.Prime := hprimes.2
  letI : Fact ctx.p.Prime := ⟨hp⟩
  have hpOrder : ctx.p ∣ orderOf g := by
    by_contra hpNot
    apply hcop
    exact (hp.coprime_iff_not_dvd.mpr hpNot).symm
  let m : ℕ := orderOf g / ctx.p
  let a : G := g ^ m
  have haOrder : orderOf a = ctx.p :=
    orderOf_pow_orderOf_div (orderOf_pos g).ne' hpOrder
  have haOne : a ≠ 1 := by
    intro ha
    have haOrderOne : orderOf a = 1 := orderOf_eq_one_iff.mpr ha
    rw [haOrder] at haOrderOne
    exact hp.ne_one haOrderOne
  have haP : IsPElement ctx.p a := by
    refine ⟨1, ?_⟩
    simpa [haOrder] using pow_orderOf_eq_one a
  have hpCore : ctx.p ∈ primeSupport (Nat.card ctx.P) := by
    refine ⟨hp, ?_⟩
    rw [hPcard]
    exact dvd_pow_self ctx.p hq.ne_zero
  let PH : Sylow ctx.p ctx.P := Classical.choice Sylow.nonempty
  obtain ⟨PG, hPG⟩ :=
    FTContextInternal.exists_sylow_eq_map_of_sylow_hall8 hp
      (FTcore_facts S ctx.maxS).fittingCore_hall_G hpCore PH
  have hPGP : (PG : Subgroup G) ≤ ctx.P := by
    rw [hPG]
    exact Subgroup.map_subtype_le _
  have hAp : IsPGroup ctx.p (Subgroup.zpowers a) := haP.zpowers_isPGroup
  obtain ⟨P, hAP⟩ := hAp.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq G P PG
  let e : G ≃* G := MulAut.conj y
  let ac : G := e a
  let gc : G := e g
  have hPmap : (P : Subgroup G).map e.toMonoidHom =
      (PG : Subgroup G) := by
    change ((y • P : Sylow ctx.p G) : Subgroup G) = _
    exact congrArg (fun T : Sylow ctx.p G ↦ (T : Subgroup G)) hy
  have hacP : ac ∈ ctx.P := by
    have haA : a ∈ Subgroup.zpowers a := Subgroup.mem_zpowers a
    have haMap : e a ∈ (Subgroup.zpowers a).map e.toMonoidHom :=
      Subgroup.mem_map_of_mem e.toMonoidHom haA
    have hmaple : (Subgroup.zpowers a).map e.toMonoidHom ≤
        (PG : Subgroup G) := by
      rw [← hPmap]
      exact Subgroup.map_mono hAP
    exact hPGP (hmaple haMap)
  have hacOne : ac ≠ 1 := by
    simpa only [map_one] using e.injective.ne haOne
  have hag : Commute a g := by
    dsimp only [a]
    exact (Commute.refl g).pow_left m
  have hacgc : Commute ac gc := hag.map e.toMonoidHom
  have hacSupport0 : ac ∈ FTsupport0 S :=
    Fcore_sub_FTsupp0 ctx.maxS ⟨hacP, hacOne⟩
  have hgcS : gc ∈ S := by
    apply hTI.centralizerWithin_zpowers_le hacSupport0
    refine ⟨Subgroup.mem_top gc, ?_⟩
    intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (hacgc.zpow_left n).eq
  have hgOne : g ≠ 1 := by
    intro hg
    subst g
    exact hcop (by simp)
  have hgcOne : gc ≠ 1 := by
    simpa only [map_one] using e.injective.ne hgOne
  by_cases hgcD : gc ∈ derivedWithin S
  · have hFrob := typePGalois_fcore_frobenius14 ctx hGal
    let J : Subgroup G := ctx.P ⊔ U
    have hgcJ : gc ∈ J := by
      have hinner : IsInternalSemidirectProductIn ctx.P U ctx.PU :=
        ctx.StypeP.2.1.2.2.2
      rcases hinner.2.2.2.2 ⟨gc, hgcD⟩ with ⟨⟨p, u⟩, hpu⟩
      have hpuG : (p : G) * (u : G) = gc :=
        congrArg Subtype.val hpu
      rw [← hpuG]
      exact Subgroup.mul_mem_sup p.property u.property
    let acJ : J := ⟨ac, (show ctx.P ≤ J from le_sup_left) hacP⟩
    let gcJ : J := ⟨gc, hgcJ⟩
    have hacJKernel : acJ ∈ ctx.P.subgroupOf J := hacP
    have hacJOne : acJ ≠ 1 := by
      intro hacJ
      exact hacOne (congrArg (fun z : J ↦ (z : G)) hacJ)
    have hgcJCent : gcJ ∈ Subgroup.centralizer
        (Subgroup.zpowers acJ : Set J) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      apply Subtype.ext
      exact (hacgc.zpow_left n).eq
    have hgcPsub : gcJ ∈ ctx.P.subgroupOf J :=
      typePGalois_centralizer_frobeniusKernel_le14
        hFrob hacJKernel hacJOne hgcJCent
    apply hP
    refine ⟨gc, ⟨hgcPsub, hgcOne⟩, y, Subgroup.mem_top y, ?_⟩
    dsimp only [gc, e]
    simp only [MulAut.conj_apply]
    group
  · have hgcW := typePGalois_outer_W_support14 ctx ⟨gc, hgcS⟩ hgcD
    rcases hgcW with ⟨w, hw, z, _hz, hwgc⟩
    change z⁻¹ * w * z = gc at hwgc
    apply hW
    refine ⟨w, hw, z * y, Subgroup.mem_top (z * y), ?_⟩
    calc
      (z * y)⁻¹ * w * (z * y) = y⁻¹ * (z⁻¹ * w * z) * y := by
        group
      _ = y⁻¹ * gc * y := by rw [hwgc]
      _ = g := by
        dsimp only [gc, e]
        simp only [MulAut.conj_apply]
        group

/-- `PFsection14.v: FTtype2_cc_core_ler`.

The normalized-TI class-support formula and the two internal semidirect
products reduce the estimate to a cardinality inequality. -/
theorem FTtype2_cc_core_ler
    {S U W W₁ W₂ : Subgroup G}
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (maxS : S ∈ minSimple_max_groups (G := G))
    (StypeP : of_typeP S U W W₁ W₂ defW)
    (Stype2 : FTtype S = 2) :
    (Nat.card G : ℝ)⁻¹ *
        ((classSupportWithin (⊤ : Subgroup G)
          (subgroupNonidentity (Fitting_core S))).ncard : ℝ) ≤
      ((Nat.card U * Nat.card W₁ : ℕ) : ℝ)⁻¹ := by
  let P : Subgroup G := Fitting_core S
  let C : ℕ :=
    (classSupportWithin (⊤ : Subgroup G)
      (subgroupNonidentity P)).ncard
  let d : ℕ := Nat.card U * Nat.card W₁
  have hTI0 := (FTtypeII_ker_TI S maxS Stype2).2.2
  have hTI : IsNormalizedTI (subgroupNonidentity P)
      (⊤ : Subgroup G) S := by
    rw [FTsupp1_type2 S Stype2] at hTI0
    exact hTI0
  have hclass : C = (Nat.card P - 1) * S.index := by
    simpa only [C, fullGalois_nonidentity_card] using
      fullGalois_classSupport_card hTI
  have hOuter : IsInternalSemidirectProductIn
      (derivedWithin S) W₁ S := StypeP.1.2.2.2
  have hInner : IsInternalSemidirectProductIn
      P U (derivedWithin S) := StypeP.2.1.2.2.2
  have hcardOuter :
      Nat.card (derivedWithin S) * Nat.card W₁ = Nat.card S := by
    simpa only [MathlibSupport.natCard_subgroupOf_eq hOuter.1,
      MathlibSupport.natCard_subgroupOf_eq hOuter.2.1] using
        hOuter.2.2.2.card_mul
  have hcardInner : Nat.card P * Nat.card U =
      Nat.card (derivedWithin S) := by
    simpa only [MathlibSupport.natCard_subgroupOf_eq hInner.1,
      MathlibSupport.natCard_subgroupOf_eq hInner.2.1] using
        hInner.2.2.2.card_mul
  have hcardS : Nat.card P * d = Nat.card S := by
    calc
      Nat.card P * d =
          (Nat.card P * Nat.card U) * Nat.card W₁ := by
        simp only [d]
        ac_rfl
      _ = Nat.card (derivedWithin S) * Nat.card W₁ := by
        rw [hcardInner]
      _ = Nat.card S := hcardOuter
  have hnat : C * d ≤ Nat.card G := by
    rw [hclass]
    calc
      ((Nat.card P - 1) * S.index) * d ≤
          (Nat.card P * S.index) * d :=
        Nat.mul_le_mul_right d
          (Nat.mul_le_mul_right S.index (Nat.sub_le _ _))
      _ = (Nat.card P * d) * S.index := by ac_rfl
      _ = Nat.card S * S.index := by rw [hcardS]
      _ = Nat.card G := S.card_mul_index
  have hnatReal : (C : ℝ) * (d : ℝ) ≤ Nat.card G := by
    exact_mod_cast hnat
  have hGpos : (0 : ℝ) < Nat.card G := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card G)
  have hUpos : (0 : ℝ) < Nat.card U := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card U)
  have hW₁pos : (0 : ℝ) < Nat.card W₁ := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card W₁)
  have hdpos : (0 : ℝ) < d := by
    simpa only [d, Nat.cast_mul] using mul_pos hUpos hW₁pos
  change (Nat.card G : ℝ)⁻¹ * (C : ℝ) ≤ (d : ℝ)⁻¹
  calc
    (Nat.card G : ℝ)⁻¹ * (C : ℝ) =
        (C : ℝ) / Nat.card G := by
      rw [div_eq_mul_inv, mul_comm]
    _ ≤ (1 : ℝ) / d := by
      rw [div_le_div_iff₀ hGpos hdpos]
      simpa using hnatReal
    _ = (d : ℝ)⁻¹ := by rw [one_div]

private theorem fgx_frobeniusIn_decomposition
    {H E L : Subgroup G} (h : IsFrobeniusIn H E L) :
    IsFrobeniusDecomposition (H.subgroupOf L) (E.subgroupOf L) := by
  let J := H ⊔ E
  let e : J ≃* L := MulEquiv.subgroupCongr h.1
  have hfrob := FTContextInternal.frobenius_map_mulEquiv8 h.2.2 e
  have hHmap :
      (H.subgroupOf J).map e.toMonoidHom = H.subgroupOf L := by
    ext x
    rw [Subgroup.mem_map_equiv]
    rfl
  have hEmap :
      (E.subgroupOf J).map e.toMonoidHom = E.subgroupOf L := by
    ext x
    rw [Subgroup.mem_map_equiv]
    rfl
  rw [hHmap, hEmap] at hfrob
  exact hfrob

private theorem fgx_virtual_finset_sum
    {Q I : Type*} [Group Q] (s : Finset I)
    (f : I → ClassFunction Q ℂ)
    (hf : ∀ i ∈ s, ClassFunction.IsVirtual (f i)) :
    ClassFunction.IsVirtual (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (ClassFunction.IsVirtual.zero (H := Q))
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self _ _)).add
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

set_option maxHeartbeats 800000 in
theorem FTtype2_support_coherence
    {S T U V W W₁ W₂ L : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    {xdefW : IsInternalDirectProductIn W₂ W₁ W}
    (ctxS : FTTypePSetupContext S U W W₁ W₂ defW)
    (ctxT : FTTypePSetupContext T V W W₂ W₁ xdefW)
    (pairST : typeP_pair S T W W₁ W₂ defW)
    (Stype2 : FTtype S = 2)
    (maxNU_L : L ∈ minSimple_max_groups_of (G := G) (Subgroup.normalizer (U : Set G) : Set G))
    (tau₁L : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (phi : ClassFunction L ℂ)
    (cohL : coherent_with (↑(FTType1SeqIndFamily L) : Set (ClassFunction L ℂ)) (nonidentitySet L) (FTtype1Dade L maxNU_L.1) tau₁L)
    (Lphi : phi ∈ FTType1SeqIndFamily L)
    (phi1 : phi 1 = (FTtype1CoreIndex L : ℂ))
    (hub : (Nat.card U - 1) / Nat.card W₁ < (Nat.card (Fitting_core L) - 1) / FTtype1CoreIndex L)
    (hvb : (Nat.card V - 1) / Nat.card W₂ < (Nat.card (Fitting_core L) - 1) / FTtype1CoreIndex L) :
    FTtype1CoreIndex L = Nat.card W₂ * Nat.card W₁ ∧
      ∃ eps : IrreducibleCharacter W₁ ℂ → IrreducibleCharacter W₂ ℂ → Bool,
        ∃ chi : ClassFunction G ℂ,
          (chi = tau₁L phi ∨ chi = -tau₁L (ClassFunction.inverseLinear phi)) ∧
          FTtype1Dade L maxNU_L.1 (FTtype1Bridge L phi) =
            (∑ i, ∑ j, if eps i j then -(ctxS.eta i j) else ctxS.eta i j) - chi := by
  classical
  let maxL : L ∈ minSimple_max_groups (G := G) := maxNU_L.1
  obtain ⟨frobL, hUL, defL⟩ :=
    FTtypeII_support_facts ctxS T L Stype2 pairST maxNU_L
  let fctxL : FTFrobeniusContext L := ⟨maxL, frobL⟩
  have Ltype1 : FTtype L = 1 := FT_Frobenius_type1 fctxL
  letI : IsCyclic W₁ := ctxS.primeTI.complement_cyclic
  letI : IsCyclic W₂ := ctxS.primeTI.fixed_cyclic
  let pairTS : typeP_pair T S W W₂ W₁ xdefW :=
    typeP_pair_sym S T W W₁ W₂ defW xdefW pairST
  have factsS := FTtypeI_bridge_facts ctxS L maxL Ltype1 tau₁L phi cohL Lphi phi1
  have factsT := FTtypeI_bridge_facts ctxT L maxL Ltype1 tau₁L phi cohL Lphi phi1

  have hoddS : ∀ j : IrreducibleCharacter W₂ ℂ,
      j ≠ IrreducibleCharacter.trivial → oddCharacterPairing
        (FTtype1Dade L maxL (FTtype1Bridge L phi))
        (ctxS.eta IrreducibleCharacter.trivial j) := by
    intro j hj
    rcases factsS.2.2.2 with hbad | hgood
    · exfalso
      have hfloor :
          (((Nat.card (Fitting_core L) - 1) / FTtype1CoreIndex L : ℕ) : ℝ) ≤
            (((Nat.card (Fitting_core L) - 1 : ℕ) : ℝ) /
              (FTtype1CoreIndex L : ℝ)) := Nat.cast_div_le
      have hhub :
          ((((Nat.card U - 1) / Nat.card W₁ : ℕ) : ℝ) <
            (((Nat.card (Fitting_core L) - 1) / FTtype1CoreIndex L : ℕ) : ℝ)) := by
        exact_mod_cast hub
      exact (not_lt_of_ge (hfloor.trans hbad.2)) hhub
    · obtain ⟨n, hn⟩ := hgood.1
      exact ⟨n, by rw [factsS.2.2.1 j hj]; exact hn⟩
  have hoddT0 : ∀ i : IrreducibleCharacter W₁ ℂ,
      i ≠ IrreducibleCharacter.trivial → oddCharacterPairing
        (FTtype1Dade L maxL (FTtype1Bridge L phi))
        (ctxT.eta IrreducibleCharacter.trivial i) := by
    intro i hi
    rcases factsT.2.2.2 with hbad | hgood
    · exfalso
      have hfloor :
          (((Nat.card (Fitting_core L) - 1) / FTtype1CoreIndex L : ℕ) : ℝ) ≤
            (((Nat.card (Fitting_core L) - 1 : ℕ) : ℝ) /
              (FTtype1CoreIndex L : ℝ)) := Nat.cast_div_le
      have hhvb :
          ((((Nat.card V - 1) / Nat.card W₂ : ℕ) : ℝ) <
            (((Nat.card (Fitting_core L) - 1) / FTtype1CoreIndex L : ℕ) : ℝ)) := by
        exact_mod_cast hvb
      exact (not_lt_of_ge (hfloor.trans hbad.2)) hhvb
    · obtain ⟨n, hn⟩ := hgood.1
      exact ⟨n, by rw [factsT.2.2.1 i hi]; exact hn⟩
  have hetaSwap (i : IrreducibleCharacter W₁ ℂ)
      (j : IrreducibleCharacter W₂ ℂ) :
      ctxS.eta i j = ctxT.eta j i := by
    have hswap := CyclicTIHypothesis.cycTIisoC defW xdefW
      ctxS.primeDade.prDade_cycTI ctxT.primeDade.prDade_cycTI i j
    have hmapped := congrArg ctxS.targetMap hswap
    simpa only [FTTypePSetupContext.eta,
      CyclicTIIsometryData.cyclicTIImage,
      CyclicTIIsometryData.cyclicTISourceIrreducible,
      CyclicTIHypothesis.cyclicTIIsometry] using hmapped
  let H : Subgroup L := FTType1FittingIn L
  letI : H.Normal := by
    simpa only [H, FTType1FittingIn] using Fcore_normal L
  let dd : DadeHypothesis (⊤ : Subgroup G) L
      (subgroupNonidentity (H.map L.subtype)) := by
    simpa only [H, FTType1FittingIn,
      Subgroup.map_subgroupOf_eq_of_le (Fcore_sub L)] using
      FT_DadeF_hyp L maxL
  let nuTop := fgxSourceMap.comp tau₁L
  have hcohTop : coherent_with
      (↑(seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥) :
        Set (ClassFunction L ℂ))
      (nonidentitySet L) (Dade dd) nuTop := by
    simpa only [H, dd, FTType1SeqIndFamily, FTType1FittingIn,
      Subgroup.map_subgroupOf_eq_of_le (Fcore_sub L)] using
      fgx_coherence_top cohL
  have hphiMem : phi ∈ seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥ := by
    simpa only [H, FTType1SeqIndFamily] using Lphi
  have hsupportEq :
      {x : L | (x : G) ∈ subgroupNonidentity (H.map L.subtype)} =
        subgroupNonidentity H := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, hyx⟩, hx1⟩
      have : y = x := Subtype.ext hyx
      subst x
      refine ⟨hy, ?_⟩
      intro hy1
      exact hx1 (by simpa using congrArg Subtype.val hy1)
    · rintro ⟨hxH, hx1⟩
      refine ⟨⟨x, hxH, rfl⟩, ?_⟩
      intro hxG
      exact hx1 (Subtype.ext hxG)
  have hphiIndex : phi 1 = (H.index : ℂ) := by
    simpa only [H, FTtype1CoreIndex] using phi1
  obtain ⟨zBridge, hzBridge, hzBridgeOn⟩ :=
    cfInd1_sub_lin_vchar H hphiMem hphiIndex
  have hbridgeRealize : VirtualCharacter.realize zBridge =
      FTtype1Bridge L phi := by
    simpa only [H, FTtype1Bridge] using hzBridge
  have hbridgeVirtual :
      ClassFunction.IsVirtual (FTtype1Bridge L phi) :=
    ⟨zBridge, hbridgeRealize⟩
  have hbridgeOn : FTtype1Bridge L phi ∈
      ClassFunction.supportedOn
        {x : L | (x : G) ∈ subgroupNonidentity (H.map L.subtype)} := by
    rw [hsupportEq]
    simpa only [hbridgeRealize] using hzBridgeOn
  let phiIrr : IrreducibleCharacter L ℂ :=
    ⟨phi, FTtype1_Ind_irr L maxL Ltype1 phi Lphi⟩
  have hcal : 1 < (seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥).card := by
    have htwo := seqInd_nontrivial (k := ℂ) H (mFT_odd L)
      (⊤ : Subgroup H) ⊥ hphiMem
    omega
  let data : DadeInd1SubLinConclusion H dd nuTop phiIrr :=
    Dade_Ind1_sub_lin H dd nuTop phiIrr hcohTop hcal hphiMem
      (by simpa only [phiIrr] using hphiIndex)
  let beta : ClassFunction G ℂ :=
    FTtype1Dade L maxL (FTtype1Bridge L phi)
  let oneG : ClassFunction G ℂ :=
    ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
      ClassFunction G ℂ)
  let gamma : ClassFunction G ℂ := fgxTargetMap data.gamma
  have hbetaTarget :
      fgxTargetMap (dadeInd1Beta H dd phi) = beta := by
    simpa only [H, beta] using
      fgx_target_dadeInd1Beta maxL dd phi
  have hbetaTopEq : dadeInd1Beta H dd phi =
      Dade dd (FTtype1Bridge L phi) := by
    simpa only [dadeInd1Beta, dadeInducedTrivial, H, FTtype1Bridge]
  have hbetaVirtual : ClassFunction.IsVirtual beta := by
    rw [← hbetaTarget]
    exact fgx_target_virtual data.beta_virtual
  have honeTarget : fgxTargetMap
      (((IrreducibleCharacter.trivial :
        IrreducibleCharacter (⊤ : Subgroup G) ℂ) :
          ClassFunction (⊤ : Subgroup G) ℂ)) = oneG := by
    ext x
    simp [fgxTargetMap, oneG, IrreducibleCharacter.trivial_apply]
  have honeVirtual : ClassFunction.IsVirtual oneG :=
    ⟨Finsupp.single IrreducibleCharacter.trivial 1, by simp [oneG]⟩
  have heta00 : ctxS.eta IrreducibleCharacter.trivial
      IrreducibleCharacter.trivial = oneG := by
    change ctxS.targetMap
      (ctxS.isoG.linearMap
        (CyclicTIIsometryData.cyclicTISourceIrreducible
          (defW := defW)
          (IrreducibleCharacter.trivial,
            IrreducibleCharacter.trivial))) = oneG
    rw [show CyclicTIIsometryData.cyclicTISourceIrreducible
        (defW := defW)
        (IrreducibleCharacter.trivial,
          IrreducibleCharacter.trivial) =
        ((IrreducibleCharacter.trivial : IrreducibleCharacter W ℂ) :
          ClassFunction W ℂ) by
      exact congrArg
        (fun chi : IrreducibleCharacter W ℂ ↦
          (chi : ClassFunction W ℂ))
        (IrreducibleCharacter.cyclicTICharacter_trivial defW)]
    rw [ctxS.isoG.map_trivial]
    ext x
    simp [ClassFunction.comap_apply, oneG,
      IrreducibleCharacter.trivial_apply]
  have hetaVirtual (i : IrreducibleCharacter W₁ ℂ)
      (j : IrreducibleCharacter W₂ ℂ) :
      ClassFunction.IsVirtual (ctxS.eta i j) := by
    obtain ⟨chiTop, epsilon, _hepsilon, himage⟩ :=
      ctxS.isoG.cyclicTIImage_eq_signed_irreducible (i, j)
    have htop : ClassFunction.IsVirtual
        (ctxS.isoG.cyclicTIImage (i, j)) := by
      refine ⟨Finsupp.single chiTop epsilon, ?_⟩
      rw [VirtualCharacter.realize_single]
      exact himage.symm
    simpa only [FTTypePSetupContext.eta,
      FTTypePSetupContext.targetMap, fgxTargetMap] using
      fgx_target_virtual htop
  have hbetaZero : Set.EqOn
      (fun w : W ↦ dadeInd1Beta H dd phi
        ⟨w, ctxS.primeDade.prDade_cycTI.le_group w.property⟩)
      0 (cyclicTISetInW W W₁ W₂) := by
    intro w hw
    let wTop : (⊤ : Subgroup G) :=
      ⟨w, ctxS.primeDade.prDade_cycTI.le_group w.property⟩
    have hwClass : (w : G) ∈
        classSupportWithin (⊤ : Subgroup G) (W : Set G) :=
      ⟨(w : G), w.property, 1, Subgroup.mem_top 1, by simp⟩
    have hwNotFull : (w : G) ∉ FT_Dade_full_support L := by
      intro hwFull
      exact Set.disjoint_left.mp factsS.1 hwFull (Or.inr hwClass)
    have hwNotDade : (w : G) ∉ Dade_support dd := by
      intro hwDade
      apply hwNotFull
      have hwF : (w : G) ∈ FT_Dade_support L
          (subgroupNonidentity (Fitting_core L)) := by
        have hHmap : H.map L.subtype = Fitting_core L := by
          simpa only [H, FTType1FittingIn] using
            Subgroup.map_subgroupOf_eq_of_le (Fcore_sub L)
        have hsupport : Dade_support dd =
            Dade_support (FT_DadeF_hyp L maxL) :=
          fgx_Dade_support_eq_of_set_eq
            (congrArg subgroupNonidentity hHmap) dd
            (FT_DadeF_hyp L maxL)
        rw [hsupport, FT_DadeF_supportE L maxL] at hwDade
        exact hwDade
      exact FT_Dade_supportS L (Fcore_sub_FTsupp maxL) hwF
    change dadeInd1Beta H dd phi wTop = (0 : W → ℂ) w
    simp only [Pi.zero_apply]
    exact ClassFunction.eq_zero_of_mem_supportedOn
      (Dade_cfunS dd (dadeInducedTrivial H - phi)) hwNotDade
  let a : IrreducibleCharacter W₁ ℂ →
      IrreducibleCharacter W₂ ℂ → ℂ :=
    fun i j ↦ characterPairing beta (ctxS.eta i j)
  have ha00 : a IrreducibleCharacter.trivial
      IrreducibleCharacter.trivial = 1 := by
    have hstar : starCharacterPairing beta oneG = 1 := by
      rw [← hbetaTarget, ← honeTarget, fgx_target_starPairing]
      exact data.beta_pairing_one
    dsimp only [a]
    rw [heta00,
      ← PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
        hbetaVirtual honeVirtual]
    exact hstar
  have ha0j (j : IrreducibleCharacter W₂ ℂ)
      (hj : j ≠ IrreducibleCharacter.trivial) :
      oddCharacterPairing beta (ctxS.eta IrreducibleCharacter.trivial j) := by
    exact hoddS j hj
  have hai0 (i : IrreducibleCharacter W₁ ℂ)
      (hi : i ≠ IrreducibleCharacter.trivial) :
      oddCharacterPairing beta (ctxS.eta i IrreducibleCharacter.trivial) := by
    rw [hetaSwap i (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)]
    exact hoddT0 i hi
  have hsourcePair (i : IrreducibleCharacter W₁ ℂ)
      (j : IrreducibleCharacter W₂ ℂ) :
      characterPairing (dadeInd1Beta H dd phi)
          (ctxS.isoG.linearMap
            (IrreducibleCharacter.cyclicTICharacter defW i j :
              ClassFunction W ℂ)) = a i j := by
    dsimp only [a]
    rw [← hbetaTarget]
    simpa only [FTTypePSetupContext.eta,
      FTTypePSetupContext.targetMap, fgxTargetMap,
      CyclicTIIsometryData.cyclicTIImage,
      CyclicTIIsometryData.cyclicTISourceIrreducible] using
      (fgx_target_pairing (dadeInd1Beta H dd phi)
        (ctxS.isoG.linearMap
          (IrreducibleCharacter.cyclicTICharacter defW i j :
            ClassFunction W ℂ))).symm
  have haOdd (i : IrreducibleCharacter W₁ ℂ)
      (j : IrreducibleCharacter W₂ ℂ) :
      oddCharacterPairing beta (ctxS.eta i j) := by
    by_cases hi : i = IrreducibleCharacter.trivial
    · subst i
      by_cases hj : j = IrreducibleCharacter.trivial
      · subst j
        exact ⟨0, by simpa [a] using ha00⟩
      · exact ha0j j hj
    · by_cases hj : j = IrreducibleCharacter.trivial
      · subst j
        exact hai0 i hi
      · obtain ⟨m, hm⟩ := ha0j j hj
        obtain ⟨n, hn⟩ := hai0 i hi
        have hex := ctxS.isoG.pairing_exchange hbetaZero
          IrreducibleCharacter.trivial i
          IrreducibleCharacter.trivial j
        refine ⟨m + n, ?_⟩
        change a i j = (((2 * (m + n) + 1 : ℤ) : ℂ))
        rw [hsourcePair, hsourcePair, hsourcePair, hsourcePair] at hex
        have hm' : a IrreducibleCharacter.trivial j =
            (((2 * m + 1 : ℤ) : ℂ)) := by
          simpa only [a] using hm
        have hn' : a i IrreducibleCharacter.trivial =
            (((2 * n + 1 : ℤ) : ℂ)) := by
          simpa only [a] using hn
        rw [ha00, hm', hn'] at hex
        push_cast at hex ⊢
        linear_combination hex
  have hsExists (i : IrreducibleCharacter W₁ ℂ)
      (j : IrreducibleCharacter W₂ ℂ) :
      ∃ z : ℤ, a i j = (z : ℂ) := by
    obtain ⟨v, hv⟩ := hbetaVirtual
    obtain ⟨w, hw⟩ := hetaVirtual i j
    refine ⟨coeffDot v w, ?_⟩
    simpa only [a, hv, hw] using VirtualCharacter.characterPairing_realize v w
  let s : IrreducibleCharacter W₁ ℂ →
      IrreducibleCharacter W₂ ℂ → ℤ :=
    fun i j ↦ Classical.choose (hsExists i j)
  have haS (i : IrreducibleCharacter W₁ ℂ)
      (j : IrreducibleCharacter W₂ ℂ) : a i j = (s i j : ℂ) :=
    Classical.choose_spec (hsExists i j)
  have hsNe (i : IrreducibleCharacter W₁ ℂ)
      (j : IrreducibleCharacter W₂ ℂ) : s i j ≠ 0 := by
    obtain ⟨n, hn⟩ := haOdd i j
    intro hz
    change a i j = (((2 * n + 1 : ℤ) : ℂ)) at hn
    rw [haS i j, hz, Int.cast_zero] at hn
    have : (2 * n + 1 : ℤ) ≠ 0 := by omega
    exact this (Int.cast_injective (α := ℂ) (by simpa using hn.symm))
  let X : ClassFunction G ℂ :=
    ∑ i, ∑ j, (s i j : ℂ) • ctxS.eta i j
  have hetaOrtho (i k : IrreducibleCharacter W₁ ℂ)
      (j ell : IrreducibleCharacter W₂ ℂ) :
      characterPairing (ctxS.eta i j) (ctxS.eta k ell) =
        if (i, j) = (k, ell) then 1 else 0 :=
    FTTypePCyclicRectangleInternal.characterPairing_eta ctxS i k j ell
  have hXpair (i : IrreducibleCharacter W₁ ℂ)
      (j : IrreducibleCharacter W₂ ℂ) :
      characterPairing X (ctxS.eta i j) = (s i j : ℂ) := by
    dsimp only [X]
    rw [fgx_characterPairing_fintype_sum_left]
    rw [Finset.sum_eq_single i]
    · rw [fgx_characterPairing_fintype_sum_left,
        Finset.sum_eq_single j]
      · rw [characterPairing_smul_left, hetaOrtho,
          if_pos rfl, mul_one]
      · intro ell _ hell
        rw [characterPairing_smul_left, hetaOrtho,
          if_neg (by simp [hell]), mul_zero]
      · exact fun h ↦ (h (Finset.mem_univ j)).elim
    · intro k _ hki
      rw [fgx_characterPairing_fintype_sum_left]
      apply Finset.sum_eq_zero
      intro ell _
      rw [characterPairing_smul_left, hetaOrtho,
        if_neg (by simp [hki]), mul_zero]
    · exact fun h ↦ (h (Finset.mem_univ i)).elim
  let coherentSum : ClassFunction G ℂ :=
    fgxTargetMap (dadeInd1CoherentSum H nuTop)
  have hcoherentEta (i : IrreducibleCharacter W₁ ℂ)
      (j : IrreducibleCharacter W₂ ℂ) :
      characterPairing coherentSum (ctxS.eta i j) = 0 := by
    dsimp only [coherentSum, dadeInd1CoherentSum]
    rw [map_sum]
    rw [fgx_characterPairing_finset_sum_left]
    apply Finset.sum_eq_zero
    intro xi hxi
    have hxiL : xi ∈ FTType1SeqIndFamily L := by
      simpa only [H, FTType1SeqIndFamily] using hxi
    have hortho := factsS.2.1 (tau₁L xi) ⟨xi, hxiL, rfl⟩
      (ctxS.eta i j)
      (by
        rw [Finset.mem_coe, FTtypePCyclicImageFamily]
        exact Finset.mem_image.mpr
          ⟨(IrreducibleCharacter.cyclicTICharacter defW i j :
            ClassFunction W ℂ), Finset.mem_image.mpr
              ⟨IrreducibleCharacter.cyclicTICharacter defW i j,
                Finset.mem_univ _, rfl⟩, rfl⟩)
    rw [map_smul, characterPairing_smul_left]
    simp only [nuTop, LinearMap.comp_apply, fgx_target_source,
      hortho, mul_zero]
  have hdecomp : beta = oneG - tau₁L phi +
      (data.coefficient : ℂ) • coherentSum + gamma := by
    have h := congrArg fgxTargetMap data.decomposition
    rw [map_add, map_add, map_sub, map_smul, hbetaTarget, honeTarget] at h
    simpa only [nuTop, LinearMap.comp_apply, fgx_target_source,
      coherentSum, gamma, phiIrr] using h
  have htauPhiVirtual : ClassFunction.IsVirtual (tau₁L phi) :=
    cohL.mapsToVirtual phi (AddSubgroup.subset_closure Lphi)
  let alpha : ClassFunction G ℂ := gamma + oneG
  have halphaPair (i : IrreducibleCharacter W₁ ℂ)
      (j : IrreducibleCharacter W₂ ℂ) :
      characterPairing alpha (ctxS.eta i j) = (s i j : ℂ) := by
    have htau := factsS.2.1 (tau₁L phi) ⟨phi, Lphi, rfl⟩
      (ctxS.eta i j)
      (by
        rw [Finset.mem_coe, FTtypePCyclicImageFamily]
        exact Finset.mem_image.mpr
          ⟨(IrreducibleCharacter.cyclicTICharacter defW i j :
            ClassFunction W ℂ), Finset.mem_image.mpr
              ⟨IrreducibleCharacter.cyclicTICharacter defW i j,
                Finset.mem_univ _, rfl⟩, rfl⟩)
    have hb := congrArg
      (fun z ↦ characterPairing z (ctxS.eta i j)) hdecomp
    simp only [characterPairing_add_left, characterPairing_sub_left',
      characterPairing_smul_left, htau, hcoherentEta, mul_zero,
      sub_zero, zero_add, add_zero] at hb
    dsimp only [alpha]
    rw [characterPairing_add_left, add_comm, ← hb]
    simpa only [a] using haS i j
  let IJ := (Finset.univ : Finset (IrreducibleCharacter W₁ ℂ)).product
    (Finset.univ : Finset (IrreducibleCharacter W₂ ℂ))
  let etaPair : (IrreducibleCharacter W₁ ℂ ×
      IrreducibleCharacter W₂ ℂ) → ClassFunction G ℂ :=
    fun ij ↦ ctxS.eta ij.1 ij.2
  let Tgrid : Finset (ClassFunction G ℂ) := IJ.image etaPair
  have hetaInjective : Function.Injective etaPair := by
    rintro ⟨i, j⟩ ⟨k, ell⟩ heq
    by_contra hne
    have heq' : ctxS.eta i j = ctxS.eta k ell := by
      simpa only [etaPair] using heq
    have hp := congrArg
      (fun z ↦ characterPairing (ctxS.eta i j) z) heq'
    rw [hetaOrtho, if_pos rfl, hetaOrtho, if_neg hne] at hp
    exact one_ne_zero hp
  have hcardT : Tgrid.card = Nat.card W₂ * Nat.card W₁ := by
    dsimp only [Tgrid]
    rw [Finset.card_image_of_injective _ hetaInjective]
    dsimp only [IJ]
    change (Finset.univ ×ˢ Finset.univ).card = _
    rw [Finset.card_product, Finset.card_univ, Finset.card_univ,
      IrreducibleCharacter.card_eq_natCard_of_isCyclic,
      IrreducibleCharacter.card_eq_natCard_of_isCyclic, Nat.mul_comm]
  have hTVirtual : ∀ z ∈ Tgrid, ClassFunction.IsVirtual z := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨⟨i, j⟩, _hij, rfl⟩
    exact hetaVirtual i j
  have hTOrtho : ∀ z ∈ Tgrid, ∀ w ∈ Tgrid,
      characterPairing z w = if z = w then 1 else 0 := by
    intro z hz w hw
    rcases Finset.mem_image.mp hz with ⟨⟨i, j⟩, _hij, rfl⟩
    rcases Finset.mem_image.mp hw with ⟨⟨k, ell⟩, _hkl, rfl⟩
    change characterPairing (ctxS.eta i j) (ctxS.eta k ell) =
      if ctxS.eta i j = ctxS.eta k ell then 1 else 0
    rw [hetaOrtho]
    by_cases h : (i, j) = (k, ell)
    · have he : ctxS.eta i j = ctxS.eta k ell :=
        by simpa only [etaPair] using congrArg etaPair h
      rw [if_pos h, if_pos he]
    · have he : ctxS.eta i j ≠ ctxS.eta k ell := fun heq ↦
        h (hetaInjective (by simpa only [etaPair] using heq))
      rw [if_neg h, if_neg he]
  have hcoherentSumVirtual : ClassFunction.IsVirtual coherentSum := by
    dsimp only [coherentSum, dadeInd1CoherentSum]
    rw [map_sum]
    apply fgx_virtual_finset_sum
    intro xi hxi
    rw [map_smul]
    simp only [nuTop, LinearMap.comp_apply, fgx_target_source]
    have hxiL : xi ∈ FTType1SeqIndFamily L := by
      simpa only [H, FTType1SeqIndFamily] using hxi
    have hxiV := cohL.mapsToVirtual xi
      (AddSubgroup.subset_closure hxiL)
    obtain ⟨n, hn⟩ := dvd_index_seqInd1 H
      (by simpa only [seqIndD] using hxi)
    let xiIrr : IrreducibleCharacter L ℂ :=
      ⟨xi, FTtype1_Ind_irr L maxL Ltype1 xi hxiL⟩
    have hself : characterPairing xi xi = 1 := by
      simpa only [xiIrr] using xiIrr.characterPairing_self
    rw [hn, hself, div_one]
    simpa only [Nat.cast_smul_eq_nsmul] using hxiV.nsmul n
  have hgammaVirtual : ClassFunction.IsVirtual gamma := by
    have hcoeffV : ClassFunction.IsVirtual
        ((data.coefficient : ℂ) • coherentSum) := by
      simpa only [← Int.cast_smul_eq_zsmul ℂ] using
        hcoherentSumVirtual.zsmul data.coefficient
    have heq : gamma = beta - oneG + tau₁L phi -
        (data.coefficient : ℂ) • coherentSum := by
      rw [hdecomp]
      abel
    rw [heq]
    exact ((hbetaVirtual.sub honeVirtual).add htauPhiVirtual).sub hcoeffV
  have halphaVirtual : ClassFunction.IsVirtual alpha :=
    hgammaVirtual.add honeVirtual
  have hnonzero : ∀ z ∈ Tgrid, characterPairing alpha z ≠ 0 := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨⟨i, j⟩, _hij, rfl⟩
    rw [halphaPair i j]
    exact Int.cast_ne_zero.mpr (hsNe i j)
  have hgridLower : ((Nat.card W₂ * Nat.card W₁ : ℕ) : ℝ) ≤
      (characterPairing alpha alpha).re := by
    rw [← hcardT]
    exact PTypeCorePairingInternal.pTypeCore_orthonormal_card_le_norm
      Tgrid hTVirtual hTOrtho
      halphaVirtual hnonzero
  have hindexBound : (H.index : ℝ) ≤ ((Nat.card H : ℝ) - 1) / 2 := by
    obtain ⟨E, hE⟩ := frobL
    have hdecompF : IsFrobeniusDecomposition H (E.subgroupOf L) := by
      simpa only [H] using fgx_frobeniusIn_decomposition hE
    exact odd_Frobenius_index_ler H (E.subgroupOf L) (mFT_odd L) hdecompF
  have hgammaUpperTop : classFunctionNormSq data.gamma ≤
      (H.index : ℝ) - 1 := (data.norm_bounds hindexBound).2
  have hgammaNorm : (characterPairing gamma gamma).re =
      classFunctionNormSq data.gamma := by
    calc
      (characterPairing gamma gamma).re =
          (starCharacterPairing gamma gamma).re :=
        congrArg Complex.re
          (PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
            hgammaVirtual hgammaVirtual).symm
      _ = (starCharacterPairing data.gamma data.gamma).re := by
        simpa only [gamma] using congrArg Complex.re
          (fgx_target_starPairing data.gamma data.gamma)
      _ = classFunctionNormSq data.gamma :=
        (classFunctionNormSq_eq_re_starCharacterPairing data.gamma).symm
  have hgammaOne : characterPairing gamma oneG = 0 := by
    calc
      characterPairing gamma oneG = starCharacterPairing gamma oneG :=
        (PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
          hgammaVirtual honeVirtual).symm
      _ = starCharacterPairing data.gamma
          (((IrreducibleCharacter.trivial :
            IrreducibleCharacter (⊤ : Subgroup G) ℂ) :
              ClassFunction (⊤ : Subgroup G) ℂ)) := by
        dsimp only [gamma]
        rw [← honeTarget, fgx_target_starPairing]
      _ = 0 := data.gamma_pairing_one
  have halphaNorm : (characterPairing alpha alpha).re =
      (characterPairing gamma gamma).re + 1 := by
    dsimp only [alpha]
    rw [characterPairing_add_left, characterPairing_add_right,
      characterPairing_add_right, hgammaOne, characterPairing_comm oneG gamma,
      hgammaOne]
    simp [oneG]
  have hgridUpper : (characterPairing alpha alpha).re ≤
      (FTtype1CoreIndex L : ℝ) := by
    rw [halphaNorm, hgammaNorm]
    calc
      classFunctionNormSq data.gamma + 1 ≤
          ((H.index : ℝ) - 1) + 1 :=
        by nlinarith [hgammaUpperTop]
      _ = (H.index : ℝ) := by ring
      _ = (FTtype1CoreIndex L : ℝ) := by
        simp only [H, FTtype1CoreIndex]
  have hindexUpper := fgx_type1CoreIndex_le_product
    ctxS ctxT pairST Stype2 maxNU_L
  have hindexEq : FTtype1CoreIndex L = Nat.card W₂ * Nat.card W₁ := by
    exact Nat.le_antisymm hindexUpper (by
      exact_mod_cast hgridLower.trans hgridUpper)
  let Y : ClassFunction G ℂ := alpha - X
  have hXVirtual : ClassFunction.IsVirtual X := by
    dsimp only [X]
    apply fgx_virtual_finset_sum
    intro i _
    apply fgx_virtual_finset_sum
    intro j _
    simpa only [← Int.cast_smul_eq_zsmul ℂ] using
      (hetaVirtual i j).zsmul (s i j)
  have hYVirtual : ClassFunction.IsVirtual Y := halphaVirtual.sub hXVirtual
  have hYeta (i : IrreducibleCharacter W₁ ℂ)
      (j : IrreducibleCharacter W₂ ℂ) :
      characterPairing Y (ctxS.eta i j) = 0 := by
    dsimp only [Y]
    rw [characterPairing_sub_left', halphaPair, hXpair, sub_self]
  have hYX : characterPairing Y X = 0 := by
    dsimp only [X]
    rw [fgx_characterPairing_fintype_sum_right]
    apply Finset.sum_eq_zero
    intro i _
    rw [fgx_characterPairing_fintype_sum_right]
    apply Finset.sum_eq_zero
    intro j _
    rw [characterPairing_smul_right, hYeta, mul_zero]
  have hXY : characterPairing X Y = 0 := by
    rw [characterPairing_comm]
    exact hYX
  have halphaXY : alpha = X + Y := by
    dsimp only [Y]
    abel
  have hXSelf : characterPairing X X =
      ∑ i, ∑ j, ((s i j : ℂ) * (s i j : ℂ)) := by
    dsimp only [X]
    rw [fgx_characterPairing_fintype_sum_left]
    apply Finset.sum_congr rfl
    intro i _
    rw [fgx_characterPairing_fintype_sum_left]
    apply Finset.sum_congr rfl
    intro j _
    rw [characterPairing_smul_left, characterPairing_comm, hXpair]
  have hYnonneg : 0 ≤ (characterPairing Y Y).re := by
    rw [← PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
      hYVirtual hYVirtual, ← classFunctionNormSq_eq_re_starCharacterPairing]
    exact classFunctionNormSq_nonneg Y
  have halphaSplit : (characterPairing alpha alpha).re =
      (characterPairing X X).re + (characterPairing Y Y).re := by
    rw [halphaXY, characterPairing_add_left, characterPairing_add_right,
      characterPairing_add_right, hXY, hYX]
    simp
  have halphaExact : (characterPairing alpha alpha).re =
      (Nat.card W₂ * Nat.card W₁ : ℕ) := by
    apply le_antisymm
    · simpa only [hindexEq] using hgridUpper
    · exact hgridLower
  have hXLower :
      ((Nat.card W₂ * Nat.card W₁ : ℕ) : ℝ) ≤
        (characterPairing X X).re := by
    rw [hXSelf, Complex.re_sum]
    simp_rw [Complex.re_sum]
    norm_num only [Complex.intCast_re, Int.cast_ofNat, Complex.mul_re,
      Complex.intCast_im, mul_zero, zero_mul, sub_zero]
    have hone (i : IrreducibleCharacter W₁ ℂ)
        (j : IrreducibleCharacter W₂ ℂ) :
        (1 : ℝ) ≤ (s i j : ℝ) * (s i j : ℝ) := by
      exact_mod_cast (Int.add_one_le_iff.mpr (mul_self_pos.mpr (hsNe i j)))
    calc
      ((Nat.card W₂ * Nat.card W₁ : ℕ) : ℝ) =
          ∑ _i : IrreducibleCharacter W₁ ℂ,
            ∑ _j : IrreducibleCharacter W₂ ℂ, (1 : ℝ) := by
        simp [IrreducibleCharacter.card_eq_natCard_of_isCyclic, Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun i _ ↦
        Finset.sum_le_sum fun j _ ↦ hone i j
  have hYzeroNorm : (characterPairing Y Y).re = 0 := by
    nlinarith [halphaSplit, halphaExact, hXLower, hYnonneg]
  have hYzero : Y = 0 := by
    apply (classFunctionNormSq_eq_zero_iff Y).mp
    rw [classFunctionNormSq_eq_re_starCharacterPairing,
      PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
        hYVirtual hYVirtual]
    exact hYzeroNorm
  have hXeq : X = alpha := by
    rw [halphaXY, hYzero, add_zero]
  have hXNorm : characterPairing X X = (FTtype1CoreIndex L : ℂ) := by
    have hreal : (characterPairing X X).re = FTtype1CoreIndex L := by
      rw [hXeq, halphaExact, hindexEq]
    obtain ⟨v, hv⟩ := hXVirtual
    have hint := VirtualCharacter.characterPairing_realize v v
    rw [hv] at hint
    obtain ⟨z, hz⟩ : ∃ z : ℤ, characterPairing X X = (z : ℂ) :=
      ⟨normSq v, hint⟩
    rw [hz] at hreal ⊢
    exact congrArg ((↑) : ℤ → ℂ) (by exact_mod_cast hreal)
  have hsumSquaresZ :
      (∑ i, ∑ j, s i j * s i j) =
        ((Nat.card W₂ * Nat.card W₁ : ℕ) : ℤ) := by
    apply Int.cast_injective (α := ℂ)
    push_cast
    rw [← hXSelf, hXNorm, hindexEq]
    norm_num only [Nat.cast_mul]
  have hsSign (i : IrreducibleCharacter W₁ ℂ)
      (j : IrreducibleCharacter W₂ ℂ) : IsSign (s i j) := by
    have hsq : s i j * s i j = 1 := by
      by_contra hne
      have htwo : (2 : ℤ) ≤ s i j * s i j := by
        have hpos : 0 < s i j * s i j :=
          mul_self_pos.mpr (hsNe i j)
        omega
      have hrowStrict :
          (∑ _ell : IrreducibleCharacter W₂ ℂ, (1 : ℤ)) <
            ∑ ell, s i ell * s i ell := by
        apply Finset.sum_lt_sum
        · intro ell _
          exact Int.add_one_le_iff.mpr
            (mul_self_pos.mpr (hsNe i ell))
        · exact ⟨j, Finset.mem_univ _, htwo⟩
      have hstrict :
          (∑ _k : IrreducibleCharacter W₁ ℂ,
              ∑ _ell : IrreducibleCharacter W₂ ℂ, (1 : ℤ)) <
            ∑ k, ∑ ell, s k ell * s k ell := by
        apply Finset.sum_lt_sum
        · intro k _
          exact Finset.sum_le_sum fun ell _ ↦
            Int.add_one_le_iff.mpr
              (mul_self_pos.mpr (hsNe k ell))
        · exact ⟨i, Finset.mem_univ _, hrowStrict⟩
      rw [hsumSquaresZ] at hstrict
      simpa [IrreducibleCharacter.card_eq_natCard_of_isCyclic,
        Nat.mul_comm] using hstrict
    exact isSign_iff_sq_eq_one.mpr (by simpa only [pow_two] using hsq)
  let chi : ClassFunction G ℂ := X - beta
  have hchiVirtual : ClassFunction.IsVirtual chi := hXVirtual.sub hbetaVirtual
  have hXBeta : characterPairing X beta = characterPairing X X := by
    rw [hXSelf]
    dsimp only [X]
    rw [fgx_characterPairing_fintype_sum_left]
    apply Finset.sum_congr rfl
    intro i _
    rw [fgx_characterPairing_fintype_sum_left]
    apply Finset.sum_congr rfl
    intro j _
    have haS' : characterPairing beta (ctxS.eta i j) = (s i j : ℂ) := by
      simpa only [a] using haS i j
    rw [characterPairing_smul_left,
      characterPairing_comm (ctxS.eta i j) beta, haS']
  have hbetaX : characterPairing beta X = characterPairing X X := by
    rw [characterPairing_comm, hXBeta]
  have hphiIrr : IsIrreducibleCharacter L ℂ phi :=
    FTtype1_Ind_irr L maxL Ltype1 phi Lphi
  have hphiNorm : characterPairing phi phi = 1 := by
    let z : IrreducibleCharacter L ℂ := ⟨phi, hphiIrr⟩
    simpa only [z] using z.characterPairing_self
  have hphiInd : characterPairing phi (dadeInducedTrivial H) = 0 := by
    exact seqInd_ortho_Ind1 H (⊤ : Subgroup H) ⊥ hphiMem
  have hIndPhi : characterPairing (dadeInducedTrivial H) phi = 0 := by
    rw [characterPairing_comm, hphiInd]
  have htrivInertia : ClassFunction.inertia H
      (((IrreducibleCharacter.trivial : IrreducibleCharacter H ℂ) :
        ClassFunction H ℂ)) = ⊤ := by
    apply top_unique
    intro x _hx
    rw [ClassFunction.mem_inertia_iff]
    ext y
    simp [ClassFunction.normalConjugate_apply,
      IrreducibleCharacter.trivial_apply]
  have hIndNorm : characterPairing (dadeInducedTrivial H)
      (dadeInducedTrivial H) = (H.index : ℂ) := by
    change characterPairing
      (ClassFunction.induce H
        ((IrreducibleCharacter.trivial : IrreducibleCharacter H ℂ) :
          ClassFunction H ℂ))
      (ClassFunction.induce H
        ((IrreducibleCharacter.trivial : IrreducibleCharacter H ℂ) :
          ClassFunction H ℂ)) = _
    rw [ClassFunction.cfnorm_Ind_irr]
    unfold ClassFunction.inertiaIndex
    rw [htrivInertia, Subgroup.card_top, ← H.card_mul_index]
    exact_mod_cast Nat.mul_div_right H.index (Nat.card_pos (α := H))
  have hbridgeNorm : characterPairing (FTtype1Bridge L phi)
      (FTtype1Bridge L phi) = (FTtype1CoreIndex L + 1 : ℕ) := by
    change characterPairing (dadeInducedTrivial H - phi)
      (dadeInducedTrivial H - phi) = _
    rw [characterPairing_sub_left', characterPairing_sub_right',
      characterPairing_sub_right', hphiInd, hIndPhi,
      hphiNorm, hIndNorm]
    simp [H, FTtype1CoreIndex]
  have hbetaNorm : characterPairing beta beta =
      (FTtype1CoreIndex L + 1 : ℕ) := by
    rw [← PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
        hbetaVirtual hbetaVirtual,
      ← hbetaTarget, fgx_target_starPairing, hbetaTopEq,
      Dade_isometry dd _ _ hbridgeOn hbridgeOn,
      PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
        hbridgeVirtual hbridgeVirtual,
      hbridgeNorm]
  have hchiNorm : characterPairing chi chi = 1 := by
    dsimp only [chi]
    rw [characterPairing_sub_left', characterPairing_sub_right',
      characterPairing_sub_right', hXNorm, hXBeta, hbetaX, hbetaNorm,
      hXNorm]
    norm_num
  let invPhi : ClassFunction L ℂ := ClassFunction.inverseLinear phi
  have hInvMem : invPhi ∈ FTType1SeqIndFamily L := by
    simpa only [invPhi, H, FTType1SeqIndFamily] using
      seqInd_inverse_mem (k := ℂ) H (⊤ : Subgroup H) ⊥ hphiMem
  have hInvSeq : invPhi ∈ seqIndD (k := ℂ) H
      (⊤ : Subgroup H) ⊥ := by
    simpa only [H, FTType1SeqIndFamily] using hInvMem
  let invPhiIrr : IrreducibleCharacter L ℂ :=
    ⟨invPhi, FTtype1_Ind_irr L maxL Ltype1 invPhi hInvMem⟩
  have hphiVirtual : ClassFunction.IsVirtual phi :=
    ⟨Finsupp.single phiIrr 1, by simp [phiIrr]⟩
  have hInvVirtual : ClassFunction.IsVirtual invPhi :=
    ⟨Finsupp.single invPhiIrr 1, by simp [invPhiIrr]⟩
  have hdiffVirtual : ClassFunction.IsVirtual (phi - invPhi) :=
    hphiVirtual.sub hInvVirtual
  have hdiffSpan : phi - invPhi ∈ AddSubgroup.closure
      (↑(FTType1SeqIndFamily L) : Set (ClassFunction L ℂ)) :=
    (AddSubgroup.closure _).sub_mem
      (AddSubgroup.subset_closure Lphi)
      (AddSubgroup.subset_closure hInvMem)
  have hdiffSpanTop : phi - invPhi ∈ AddSubgroup.closure
      (↑(seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥) :
        Set (ClassFunction L ℂ)) := by
    simpa only [H, FTType1SeqIndFamily] using hdiffSpan
  have hdiffOn : phi - invPhi ∈
      ClassFunction.supportedOn (nonidentitySet L) := by
    simpa only [invPhi] using
      FTType1InfrastructureInternal.inverseSubSupported phi
  have hdiffOnCore : phi - invPhi ∈
      ClassFunction.supportedOn
        {x : L | (x : G) ∈ subgroupNonidentity (H.map L.subtype)} := by
    rw [hsupportEq, ClassFunction.mem_supportedOn_iff]
    intro x hx
    by_cases hxH : x ∈ H
    · have hx1 : x = 1 := by
        by_contra hxne
        exact hx ⟨hxH, hxne⟩
      subst x
      simp [invPhi]
    · have hp0 := ClassFunction.eq_zero_of_mem_supportedOn
        (seqInd_on H hphiMem) hxH
      have hi0 := ClassFunction.eq_zero_of_mem_supportedOn
        (seqInd_on H hInvSeq) hxH
      simp [ClassFunction.sub_apply, hp0, hi0]
  have hDadeDiffVirtual : ClassFunction.IsVirtual
      (Dade dd (phi - invPhi)) := by
    rw [← hcohTop.agrees (phi - invPhi) hdiffSpanTop hdiffOn]
    exact hcohTop.mapsToVirtual (phi - invPhi) hdiffSpanTop
  have hDadeBetaVirtual : ClassFunction.IsVirtual
      (dadeInd1Beta H dd phi) := by
    simpa only [phiIrr] using data.beta_virtual
  have hdiffTarget : tau₁L (phi - invPhi) =
      fgxTargetMap (Dade dd (phi - invPhi)) := by
    have htop := hcohTop.agrees (phi - invPhi) hdiffSpanTop hdiffOn
    have hamb := congrArg fgxTargetMap htop
    simpa only [nuTop, LinearMap.comp_apply, fgx_target_source] using hamb
  have hdiffBeta : characterPairing
      (tau₁L phi - tau₁L invPhi) beta = -1 := by
    rw [← map_sub, hdiffTarget, ← hbetaTarget,
      ← PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
        (fgx_target_virtual hDadeDiffVirtual)
        (fgx_target_virtual hDadeBetaVirtual),
      fgx_target_starPairing, hbetaTopEq,
      Dade_isometry dd _ _ hdiffOnCore hbridgeOn,
      PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
        hdiffVirtual hbridgeVirtual]
    rw [FTtype1Bridge, characterPairing_sub_left',
      characterPairing_sub_right', characterPairing_sub_right',
      seqInd_ortho_Ind1 H (⊤ : Subgroup H) ⊥ hphiMem,
      hphiNorm,
      seqInd_ortho_Ind1 H (⊤ : Subgroup H) ⊥ hInvSeq]
    have hcross : characterPairing invPhi phi = 0 := by
      rw [characterPairing_comm]
      simpa only [invPhi] using
        seqInd_conjC_ortho H (mFT_odd L)
          (⊤ : Subgroup H) ⊥ hphiMem
    rw [hcross]
    norm_num
  have hXtau (psi : ClassFunction L ℂ)
      (hpsi : psi ∈ FTType1SeqIndFamily L) :
      characterPairing X (tau₁L psi) = 0 := by
    dsimp only [X]
    rw [fgx_characterPairing_fintype_sum_left]
    apply Finset.sum_eq_zero
    intro i _
    rw [fgx_characterPairing_fintype_sum_left]
    apply Finset.sum_eq_zero
    intro j _
    rw [characterPairing_smul_left,
      characterPairing_comm (ctxS.eta i j) (tau₁L psi),
      factsS.2.1 (tau₁L psi) ⟨psi, hpsi, rfl⟩
      (ctxS.eta i j) (by
        rw [Finset.mem_coe, FTtypePCyclicImageFamily]
        exact Finset.mem_image.mpr
          ⟨(IrreducibleCharacter.cyclicTICharacter defW i j :
            ClassFunction W ℂ), Finset.mem_image.mpr
              ⟨IrreducibleCharacter.cyclicTICharacter defW i j,
                Finset.mem_univ _, rfl⟩, rfl⟩), mul_zero]
  have hdiffChi : characterPairing chi (tau₁L phi - tau₁L invPhi) = 1 := by
    dsimp only [chi]
    rw [characterPairing_sub_left',
      characterPairing_sub_right' X, hXtau phi Lphi,
      hXtau invPhi hInvMem, sub_self,
      characterPairing_comm beta (tau₁L phi - tau₁L invPhi),
      hdiffBeta]
    norm_num
  have htauInvVirtual : ClassFunction.IsVirtual (tau₁L invPhi) :=
    cohL.mapsToVirtual invPhi (AddSubgroup.subset_closure hInvMem)
  have htauPhiNorm : characterPairing (tau₁L phi) (tau₁L phi) = 1 := by
    rw [cohL.isometry phi (AddSubgroup.subset_closure Lphi)
      phi (AddSubgroup.subset_closure Lphi), hphiNorm]
  have hInvNorm : characterPairing invPhi invPhi = 1 := by
    simpa only [invPhi] using invPhiIrr.characterPairing_self
  have htauInvNorm : characterPairing (tau₁L invPhi) (tau₁L invPhi) = 1 := by
    rw [cohL.isometry invPhi (AddSubgroup.subset_closure hInvMem)
      invPhi (AddSubgroup.subset_closure hInvMem), hInvNorm]
  have htauCross : characterPairing (tau₁L phi) (tau₁L invPhi) = 0 := by
    rw [cohL.isometry phi (AddSubgroup.subset_closure Lphi)
      invPhi (AddSubgroup.subset_closure hInvMem)]
    simpa only [invPhi, characterPairing_comm] using
      seqInd_conjC_ortho H (mFT_odd L)
        (⊤ : Subgroup H) ⊥ hphiMem
  have hpairChoice : characterPairing chi (tau₁L phi) = 1 ∨
      characterPairing chi (tau₁L invPhi) = -1 := by
    obtain ⟨c, ec, hec, hc⟩ :=
      FTType1InfrastructureInternal.existsSignedIrreducibleOfVirtualNormOne
        hchiVirtual hchiNorm
    obtain ⟨p, ep, hep, hp⟩ :=
      FTType1InfrastructureInternal.existsSignedIrreducibleOfVirtualNormOne
        htauPhiVirtual htauPhiNorm
    obtain ⟨q, eq, heq, hq⟩ :=
      FTType1InfrastructureInternal.existsSignedIrreducibleOfVirtualNormOne
        htauInvVirtual htauInvNorm
    have hpq : p ≠ q := by
      intro hpq
      rw [hp, hq, hpq, characterPairing_smul_left,
        characterPairing_smul_right, q.characterPairing_self] at htauCross
      rcases hep with rfl | rfl <;> rcases heq with rfl | rfl <;>
        norm_num at htauCross
    have hdiffSigns :
        (ec : ℂ) *
          ((ep : ℂ) * characterPairing (c : ClassFunction G ℂ)
              (p : ClassFunction G ℂ) -
            (eq : ℂ) * characterPairing (c : ClassFunction G ℂ)
              (q : ClassFunction G ℂ)) = 1 := by
      simpa only [hc, hp, hq, characterPairing_sub_right',
        characterPairing_smul_left, characterPairing_smul_right] using
        hdiffChi
    by_cases hcp : c = p
    · left
      subst p
      have hcq : c ≠ q := hpq
      rw [c.characterPairing_self,
        IrreducibleCharacter.characterPairing_eq_zero hcq] at hdiffSigns
      rw [hc, hp, characterPairing_smul_left,
        characterPairing_smul_right, c.characterPairing_self]
      linear_combination hdiffSigns
    · by_cases hcq : c = q
      · right
        subst q
        rw [IrreducibleCharacter.characterPairing_eq_zero hcp,
          c.characterPairing_self] at hdiffSigns
        rw [hc, hq, characterPairing_smul_left,
          characterPairing_smul_right, c.characterPairing_self]
        linear_combination -hdiffSigns
      · rw [IrreducibleCharacter.characterPairing_eq_zero hcp,
          IrreducibleCharacter.characterPairing_eq_zero hcq] at hdiffSigns
        norm_num at hdiffSigns
  have hchiChoice : chi = tau₁L phi ∨ chi = -tau₁L invPhi :=
    fgx_residual_identification hchiVirtual hchiNorm
      htauPhiVirtual htauPhiNorm htauInvVirtual htauInvNorm hpairChoice
  obtain ⟨eps, heps⟩ := fgx_bool_signed_rectangle
    (fun i j ↦ ctxS.eta i j) s hsSign
  refine ⟨hindexEq, eps, chi, ?_, ?_⟩
  · simpa only [invPhi] using hchiChoice
  · have hbetaChi : beta = X - chi := by
      dsimp only [chi]
      abel
    change beta =
      (∑ i, ∑ j, if eps i j then -(ctxS.eta i j) else ctxS.eta i j) - chi
    rw [hbetaChi]
    simpa only [X] using
      congrArg (fun z : ClassFunction G ℂ ↦ z - chi) heps

/-! Fresh local analytic adapters used only by the cluster-C proof. -/

private theorem fgx_starPairing_sub_left
    {Q : Type u} [Group Q] [Fintype Q]
    (f g h : ClassFunction Q ℂ) :
    starCharacterPairing (f - g) h =
      starCharacterPairing f h - starCharacterPairing g h := by
  simp [sub_eq_add_neg, starCharacterPairing,
    twistedCharacterPairing, add_mul, Finset.sum_add_distrib]
  ring_nf

private theorem fgx_starPairing_sub_right
    {Q : Type u} [Group Q] [Fintype Q]
    (f g h : ClassFunction Q ℂ) :
    starCharacterPairing f (g - h) =
      starCharacterPairing f g - starCharacterPairing f h := by
  simp [sub_eq_add_neg, starCharacterPairing,
    twistedCharacterPairing, mul_add, Finset.sum_add_distrib]

private theorem fgx_starPairing_sum_left
    {Q : Type u} [Group Q] [Fintype Q]
    {I : Type*} (s : Finset I) (f : I → ClassFunction Q ℂ)
    (g : ClassFunction Q ℂ) :
    starCharacterPairing (∑ i ∈ s, f i) g =
      ∑ i ∈ s, starCharacterPairing (f i) g := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, starCharacterPairing_add_left, ih,
        Finset.sum_insert hi]

private theorem fgx_starPairing_sum_right
    {Q : Type u} [Group Q] [Fintype Q]
    (f : ClassFunction Q ℂ) {I : Type*}
    (s : Finset I) (g : I → ClassFunction Q ℂ) :
    starCharacterPairing f (∑ i ∈ s, g i) =
      ∑ i ∈ s, starCharacterPairing f (g i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, starCharacterPairing_add_right, ih,
        Finset.sum_insert hi]

private theorem fgx_normSq_add_of_orthogonal
    {Q : Type u} [Group Q] [Fintype Q]
    (f g : ClassFunction Q ℂ)
    (hfg : starCharacterPairing f g = 0) :
    classFunctionNormSq (f + g) =
      classFunctionNormSq f + classFunctionNormSq g := by
  have hgf : starCharacterPairing g f = 0 := by
    calc
      starCharacterPairing g f =
          star (starCharacterPairing f g) :=
        starCharacterPairing_conj_symm g f
      _ = 0 := by simp [hfg]
  rw [classFunctionNormSq_eq_re_starCharacterPairing,
    classFunctionNormSq_eq_re_starCharacterPairing,
    classFunctionNormSq_eq_re_starCharacterPairing,
    starCharacterPairing_add_left, starCharacterPairing_add_right,
    starCharacterPairing_add_right, hfg, hgf]
  simp

private theorem fgx_normSq_smul
    {Q : Type u} [Group Q] [Fintype Q]
    (a : ℂ) (f : ClassFunction Q ℂ) :
    classFunctionNormSq (a • f) =
      Complex.normSq a * classFunctionNormSq f := by
  unfold classFunctionNormSq
  simp only [ClassFunction.smul_apply, smul_eq_mul, Complex.normSq_mul,
    Finset.mul_sum]
  ring

private theorem fgx_normSq_sum_orthogonal
    {Q : Type u} [Group Q] [Fintype Q]
    {I : Type*} [DecidableEq I]
    (s : Finset I) (f : I → ClassFunction Q ℂ)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      starCharacterPairing (f i) (f j) = 0) :
    classFunctionNormSq (∑ i ∈ s, f i) =
      ∑ i ∈ s, classFunctionNormSq (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [classFunctionNormSq]
  | @insert i s hi ih =>
      have his : starCharacterPairing (f i) (∑ j ∈ s, f j) = 0 := by
        rw [fgx_starPairing_sum_right]
        apply Finset.sum_eq_zero
        intro j hj
        exact horth i (Finset.mem_insert_self i s) j
          (Finset.mem_insert_of_mem hj) (fun hij ↦ hi (hij ▸ hj))
      rw [Finset.sum_insert hi, fgx_normSq_add_of_orthogonal _ _ his,
        Finset.sum_insert hi]
      congr 1
      exact ih fun a ha b hb hab ↦
        horth a (Finset.mem_insert_of_mem ha)
          b (Finset.mem_insert_of_mem hb) hab

private theorem fgx_projection_le_norm
    {Q : Type u} [Group Q] [Fintype Q]
    {I : Type*} [DecidableEq I]
    (s : Finset I) (f : I → ClassFunction Q ℂ)
    (c : I → ℂ) (beta : ClassFunction Q ℂ)
    (horth : ∀ i ∈ s, ∀ j ∈ s,
      starCharacterPairing (f i) (f j) = if i = j then 1 else 0)
    (hpair : ∀ i ∈ s, starCharacterPairing beta (f i) = c i) :
    ∑ i ∈ s, Complex.normSq (c i) ≤ classFunctionNormSq beta := by
  classical
  let P : ClassFunction Q ℂ := ∑ i ∈ s, c i • f i
  let R : ClassFunction Q ℂ := beta - P
  have hPpair (j : I) (hj : j ∈ s) :
      starCharacterPairing P (f j) = c j := by
    dsimp only [P]
    rw [fgx_starPairing_sum_left, Finset.sum_eq_single j]
    · rw [starCharacterPairing_smul_left,
        horth j hj j hj, if_pos rfl, mul_one]
    · intro i hi hij
      rw [starCharacterPairing_smul_left,
        horth i hi j hj, if_neg hij]
      simp
    · exact fun h ↦ (h hj).elim
  have hRpair (j : I) (hj : j ∈ s) :
      starCharacterPairing R (f j) = 0 := by
    dsimp only [R]
    rw [fgx_starPairing_sub_left, hpair j hj, hPpair j hj, sub_self]
  have hRP : starCharacterPairing R P = 0 := by
    dsimp only [P]
    rw [fgx_starPairing_sum_right]
    apply Finset.sum_eq_zero
    intro i hi
    rw [starCharacterPairing_smul_right, hRpair i hi]
    simp
  have hPR : starCharacterPairing P R = 0 := by
    calc
      starCharacterPairing P R = star (starCharacterPairing R P) :=
        starCharacterPairing_conj_symm P R
      _ = 0 := by simp [hRP]
  have hdecomp : beta = P + R := by
    dsimp only [R]
    abel
  have hnormP : classFunctionNormSq P =
      ∑ i ∈ s, Complex.normSq (c i) := by
    dsimp only [P]
    rw [fgx_normSq_sum_orthogonal]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [fgx_normSq_smul,
        classFunctionNormSq_eq_re_starCharacterPairing,
        horth i hi i hi, if_pos rfl]
      norm_num
    · intro i hi j hj hij
      rw [starCharacterPairing_smul_left,
        starCharacterPairing_smul_right,
        horth i hi j hj, if_neg hij]
      simp
  rw [hdecomp, fgx_normSq_add_of_orthogonal _ _ hPR, hnormP]
  exact le_add_of_nonneg_right (classFunctionNormSq_nonneg R)

private theorem fgx_one_le_normSq_intCast
    (z : ℤ) (hz : z ≠ 0) :
    1 ≤ Complex.normSq (z : ℂ) := by
  rw [Complex.normSq_intCast]
  have hpos : 0 < z * z := mul_self_pos.mpr hz
  exact_mod_cast (Int.add_one_le_iff.mpr hpos)

private theorem fgx_seqInd_degree_normSq_sum
    {Q : Type u} [Group Q] [Fintype Q]
    (H : Subgroup Q) [H.Normal]
    (hirr : ∀ xi ∈ seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥,
      IsIrreducibleCharacter Q ℂ xi) :
    (∑ xi ∈ seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥,
        Complex.normSq (xi 1)) =
      (H.index : ℝ) * ((Nat.card H : ℝ) - 1) := by
  classical
  let calS := seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥
  have hself (xi : ClassFunction Q ℂ) (hxi : xi ∈ calS) :
      characterPairing xi xi = 1 := by
    let chi : IrreducibleCharacter Q ℂ :=
      ⟨xi, hirr xi (by simpa only [calS] using hxi)⟩
    simpa only [chi] using chi.characterPairing_self
  have hsquare : (∑ xi ∈ calS, xi 1 ^ 2) =
      (H.index : ℂ) * ((Nat.card H : ℂ) - 1) := by
    calc
      (∑ xi ∈ calS, xi 1 ^ 2) =
          ∑ xi ∈ calS, xi 1 ^ 2 / characterPairing xi xi := by
        apply Finset.sum_congr rfl
        intro xi hxi
        rw [hself xi hxi, div_one]
      _ = (H.index : ℂ) * ((Nat.card H : ℂ) - 1) := by
        simpa only [calS] using sum_seqIndC1_square (k := ℂ) H
  calc
    (∑ xi ∈ seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥,
        Complex.normSq (xi 1)) =
        ∑ xi ∈ calS, (xi 1 ^ 2).re := by
      apply Finset.sum_congr rfl
      intro xi hxi
      obtain ⟨n, hn⟩ := Cnat_seqInd1 H (seqInd_subT H _ hxi)
      rw [hn, Complex.normSq_natCast]
      norm_num [pow_two, Complex.mul_re]
    _ = (∑ xi ∈ calS, xi 1 ^ 2).re := by simp
    _ = ((H.index : ℂ) * ((Nat.card H : ℂ) - 1)).re := by rw [hsquare]
    _ = (H.index : ℝ) * ((Nat.card H : ℝ) - 1) := by norm_num

/-! The three requested PFsection14 declarations. -/

theorem disjoint_Dade_FTtype1
    {M L : Subgroup G}
    (maxM : M ∈ minSimple_max_groups (G := G))
    (maxL : L ∈ minSimple_max_groups (G := G))
    (Mtype1 : FTtype M = 1) (Ltype1 : FTtype L = 1)
    (hnot : ¬ FTAmbientConjugate M L) :
    Disjoint (Dade_support (FT_DadeF_hyp M maxM))
      (Dade_support (FT_DadeF_hyp L maxL)) := by
  have hsupportM : Dade_support (FT_DadeF_hyp M maxM) =
      FT_Dade1_support M := by
    calc
      Dade_support (FT_DadeF_hyp M maxM) =
          FT_Dade_support M (subgroupNonidentity (Fitting_core M)) :=
        FT_DadeF_supportE M maxM
      _ = FT_Dade_support M (FTsupport1 M) := by
        rw [FTsupp1_type1 M Mtype1]
      _ = FT_Dade1_support M := rfl
  have hsupportL : Dade_support (FT_DadeF_hyp L maxL) =
      FT_Dade1_support L := by
    calc
      Dade_support (FT_DadeF_hyp L maxL) =
          FT_Dade_support L (subgroupNonidentity (Fitting_core L)) :=
        FT_DadeF_supportE L maxL
      _ = FT_Dade_support L (FTsupport1 L) := by
        rw [FTsupp1_type1 L Ltype1]
      _ = FT_Dade1_support L := rfl
  rw [hsupportM, hsupportL]
  exact FT_Dade1_support_disjoint maxM maxL hnot

theorem coherent_FTtype1_ortho
    {M L : Subgroup G}
    (maxM : M ∈ minSimple_max_groups (G := G))
    (maxL : L ∈ minSimple_max_groups (G := G))
    (Mtype1 : FTtype M = 1) (Ltype1 : FTtype L = 1)
    (tau1M : ClassFunction M ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup G) ℂ)
    (tau1L : ClassFunction L ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup G) ℂ)
    (cohM : coherent_with
      (FTType1SeqIndFamily M : Set (ClassFunction M ℂ))
      (nonidentitySet M) (Dade (FT_DadeF_hyp M maxM)) tau1M)
    (cohL : coherent_with
      (FTType1SeqIndFamily L : Set (ClassFunction L ℂ))
      (nonidentitySet L) (Dade (FT_DadeF_hyp L maxL)) tau1L)
    (hnot : ¬ FTAmbientConjugate M L) :
    ∀ psi : ClassFunction M ℂ, psi ∈ FTType1SeqIndFamily M →
      ∀ phi : ClassFunction L ℂ, phi ∈ FTType1SeqIndFamily L →
        characterPairing (tau1M psi) (tau1L phi) = 0 := by
  intro psi hpsi phi hphi
  let KM : Subgroup M := FTType1FittingIn M
  let KL : Subgroup L := FTType1FittingIn L
  letI : KM.Normal := by
    simpa only [KM, FTType1FittingIn] using Fcore_normal M
  letI : KL.Normal := by
    simpa only [KL, FTType1FittingIn] using Fcore_normal L
  let chiM : IrreducibleCharacter M ℂ :=
    ⟨psi, FTtype1_Ind_irr M maxM Mtype1 psi hpsi⟩
  let chiL : IrreducibleCharacter L ℂ :=
    ⟨phi, FTtype1_Ind_irr L maxL Ltype1 phi hphi⟩
  exact disjoint_coherent_ortho
    (ddA₁ := FT_DadeF_hyp M maxM)
    (ddA₂ := FT_DadeF_hyp L maxL)
    (disjointA := disjoint_Dade_FTtype1
      maxM maxL Mtype1 Ltype1 hnot)
    (mFT_odd (⊤ : Subgroup G)) KM KL tau1M tau1L
    (by simpa only [KM, FTType1SeqIndFamily] using cohM)
    (by simpa only [KL, FTType1SeqIndFamily] using cohL)
    chiM chiL
    (by simpa only [chiM, KM, FTType1SeqIndFamily] using hpsi)
    (by simpa only [chiL, KL, FTType1SeqIndFamily] using hphi)

theorem coherent_FTtype1_core_ltr
    {M L : Subgroup G}
    (maxM : M ∈ minSimple_max_groups (G := G))
    (maxL : L ∈ minSimple_max_groups (G := G))
    (Mtype1 : FTtype M = 1) (Ltype1 : FTtype L = 1)
    (tau1M : ClassFunction M ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup G) ℂ)
    (tau1L : ClassFunction L ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup G) ℂ)
    (cohM : coherent_with
      (FTType1SeqIndFamily M : Set (ClassFunction M ℂ))
      (nonidentitySet M) (Dade (FT_DadeF_hyp M maxM)) tau1M)
    (cohL : coherent_with
      (FTType1SeqIndFamily L : Set (ClassFunction L ℂ))
      (nonidentitySet L) (Dade (FT_DadeF_hyp L maxL)) tau1L)
    (psi : ClassFunction M ℂ) (phi : ClassFunction L ℂ)
    (hpsi : psi ∈ FTType1SeqIndFamily M)
    (hphi : phi ∈ FTType1SeqIndFamily L)
    (psi1 : psi 1 = ((FTType1FittingIn M).index : ℂ))
    (phi1 : phi 1 = ((FTType1FittingIn L).index : ℂ))
    (hnot : ¬ FTAmbientConjugate M L)
    (ha : starCharacterPairing
      (Dade (FT_DadeF_hyp L maxL)
        (dadeInducedTrivial (FTType1FittingIn L) - phi))
      (tau1M psi) ≠ 0) :
    ((((Nat.card (Fitting_core M) - 1 : ℕ) : ℝ)) /
        ((FTType1FittingIn M).index : ℝ)) ≤
      ((FTType1FittingIn L).index : ℝ) - 1 := by
  classical
  let HM : Subgroup M := FTType1FittingIn M
  let HL : Subgroup L := FTType1FittingIn L
  let calM : Finset (ClassFunction M ℂ) :=
    seqIndD (k := ℂ) HM (⊤ : Subgroup HM) ⊥
  let calL : Finset (ClassFunction L ℂ) :=
    seqIndD (k := ℂ) HL (⊤ : Subgroup HL) ⊥
  have hHMmap : HM.map M.subtype = Fitting_core M := by
    simpa only [HM, FTType1FittingIn] using
      Subgroup.map_subgroupOf_eq_of_le (Fcore_sub M)
  have hHLmap : HL.map L.subtype = Fitting_core L := by
    simpa only [HL, FTType1FittingIn] using
      Subgroup.map_subgroupOf_eq_of_le (Fcore_sub L)
  let ddM : DadeHypothesis (⊤ : Subgroup G) M
      (subgroupNonidentity (HM.map M.subtype)) := by
    simpa only [hHMmap] using FT_DadeF_hyp M maxM
  let ddL : DadeHypothesis (⊤ : Subgroup G) L
      (subgroupNonidentity (HL.map L.subtype)) := by
    simpa only [hHLmap] using FT_DadeF_hyp L maxL
  letI : HM.Normal := by
    simpa only [HM, FTType1FittingIn] using Fcore_normal M
  letI : HL.Normal := by
    simpa only [HL, FTType1FittingIn] using Fcore_normal L
  have hpsi' : psi ∈ calM := by
    simpa only [calM, HM, FTType1SeqIndFamily] using hpsi
  have hphi' : phi ∈ calL := by
    simpa only [calL, HL, FTType1SeqIndFamily] using hphi
  have cohM' : coherent_with
      (↑calM : Set (ClassFunction M ℂ))
      (nonidentitySet M) (Dade ddM) tau1M := by
    simpa only [calM, HM, FTType1SeqIndFamily, ddM, hHMmap] using cohM
  have cohL' : coherent_with
      (↑calL : Set (ClassFunction L ℂ))
      (nonidentitySet L) (Dade ddL) tau1L := by
    simpa only [calL, HL, FTType1SeqIndFamily, ddL, hHLmap] using cohL
  let psiIrr : IrreducibleCharacter M ℂ :=
    ⟨psi, FTtype1_Ind_irr M maxM Mtype1 psi hpsi⟩
  let phiIrr : IrreducibleCharacter L ℂ :=
    ⟨phi, FTtype1_Ind_irr L maxL Ltype1 phi hphi⟩
  have hcalM : 1 < calM.card := by
    have htwo : 2 ≤ calM.card := by
      simpa only [calM] using
        seqInd_nontrivial (k := ℂ) HM (mFT_odd M)
          (⊤ : Subgroup HM) ⊥
          (by simpa only [calM] using hpsi')
    omega
  have hcalL : 1 < calL.card := by
    have htwo : 2 ≤ calL.card := by
      simpa only [calL] using
        seqInd_nontrivial (k := ℂ) HL (mFT_odd L)
          (⊤ : Subgroup HL) ⊥
          (by simpa only [calL] using hphi')
    omega
  let dataM : DadeInd1SubLinConclusion HM ddM tau1M psiIrr :=
    Dade_Ind1_sub_lin HM ddM tau1M psiIrr cohM' hcalM hpsi'
      (by simpa only [psiIrr, HM] using psi1)
  let dataL : DadeInd1SubLinConclusion HL ddL tau1L phiIrr :=
    Dade_Ind1_sub_lin HL ddL tau1L phiIrr cohL' hcalL hphi'
      (by simpa only [phiIrr, HL] using phi1)
  let betaL : ClassFunction (⊤ : Subgroup G) ℂ :=
    dadeInd1Beta HL ddL phi
  let gamma : ClassFunction (⊤ : Subgroup G) ℂ := dataL.gamma
  let a : ℂ := starCharacterPairing betaL (tau1M psi)
  have haNe : a ≠ 0 := by
    simpa only [a, betaL, dadeInd1Beta, HL, ddL, hHLmap] using ha
  have hsupportM : Dade_support ddM =
      Dade_support (FT_DadeF_hyp M maxM) := by
    exact fgx_Dade_support_eq_of_set_eq
      (congrArg subgroupNonidentity hHMmap) ddM
      (FT_DadeF_hyp M maxM)
  have hsupportL : Dade_support ddL =
      Dade_support (FT_DadeF_hyp L maxL) := by
    exact fgx_Dade_support_eq_of_set_eq
      (congrArg subgroupNonidentity hHLmap) ddL
      (FT_DadeF_hyp L maxL)
  have hdis : Disjoint (Dade_support ddL) (Dade_support ddM) := by
    rw [hsupportL, hsupportM]
    exact (disjoint_Dade_FTtype1 maxM maxL Mtype1 Ltype1 hnot).symm
  have hmemM {xi : ClassFunction M ℂ} (hxi : xi ∈ calM) :
      xi ∈ AddSubgroup.closure
        (↑calM : Set (ClassFunction M ℂ)) :=
    AddSubgroup.subset_closure hxi
  have hmemL {xi : ClassFunction L ℂ} (hxi : xi ∈ calL) :
      xi ∈ AddSubgroup.closure
        (↑calL : Set (ClassFunction L ℂ)) :=
    AddSubgroup.subset_closure hxi
  have hselfM {xi : ClassFunction M ℂ} (hxi : xi ∈ calM) :
      characterPairing xi xi = 1 := by
    let chi : IrreducibleCharacter M ℂ :=
      ⟨xi, FTtype1_Ind_irr M maxM Mtype1 xi
        (by simpa only [calM, HM, FTType1SeqIndFamily] using hxi)⟩
    simpa only [chi] using chi.characterPairing_self
  have hnuPairM {xi mu : ClassFunction M ℂ}
      (hxi : xi ∈ calM) (hmu : mu ∈ calM) :
      starCharacterPairing (tau1M xi) (tau1M mu) =
        characterPairing xi mu := by
    rw [PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
      (cohM'.mapsToVirtual xi (hmemM hxi))
      (cohM'.mapsToVirtual mu (hmemM hmu))]
    exact cohM'.isometry xi (hmemM hxi) mu (hmemM hmu)
  have hnuOrthonormal (xi : ClassFunction M ℂ) (hxi : xi ∈ calM)
      (mu : ClassFunction M ℂ) (hmu : mu ∈ calM) :
      starCharacterPairing (tau1M xi) (tau1M mu) =
        if xi = mu then 1 else 0 := by
    by_cases hEq : xi = mu
    · subst mu
      rw [hnuPairM hxi hxi, hselfM hxi, if_pos rfl]
    · rw [hnuPairM hxi hmu, seqInd_ortho HM hxi hmu hEq, if_neg hEq]
  have hcross {eta : ClassFunction L ℂ} (heta : eta ∈ calL)
      {xi : ClassFunction M ℂ} (hxi : xi ∈ calM) :
      starCharacterPairing (tau1L eta) (tau1M xi) = 0 := by
    rw [PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
      (cohL'.mapsToVirtual eta (hmemL heta))
      (cohM'.mapsToVirtual xi (hmemM hxi)), characterPairing_comm]
    exact coherent_FTtype1_ortho maxM maxL Mtype1 Ltype1
      tau1M tau1L cohM cohL hnot xi
        (by simpa only [calM, HM, FTType1SeqIndFamily] using hxi)
      eta (by simpa only [calL, HL, FTType1SeqIndFamily] using heta)
  have hsumCross {xi : ClassFunction M ℂ} (hxi : xi ∈ calM) :
      starCharacterPairing (dadeInd1CoherentSum HL tau1L)
        (tau1M xi) = 0 := by
    unfold dadeInd1CoherentSum
    rw [fgx_starPairing_sum_left]
    apply Finset.sum_eq_zero
    intro eta heta
    rw [starCharacterPairing_smul_left, hcross heta hxi]
    simp
  have honeCross {xi : ClassFunction M ℂ} (hxi : xi ∈ calM) :
      starCharacterPairing
          (((IrreducibleCharacter.trivial :
            IrreducibleCharacter (⊤ : Subgroup G) ℂ) :
              ClassFunction (⊤ : Subgroup G) ℂ))
        (tau1M xi) = 0 := by
    calc
      starCharacterPairing
          (((IrreducibleCharacter.trivial :
            IrreducibleCharacter (⊤ : Subgroup G) ℂ) :
              ClassFunction (⊤ : Subgroup G) ℂ))
          (tau1M xi) =
          star (starCharacterPairing (tau1M xi)
            (((IrreducibleCharacter.trivial :
              IrreducibleCharacter (⊤ : Subgroup G) ℂ) :
                ClassFunction (⊤ : Subgroup G) ℂ))) :=
        starCharacterPairing_conj_symm _ _
      _ = 0 := by rw [dataM.image_orthogonal_one xi hxi]; simp
  have hgammaPair {xi : ClassFunction M ℂ} (hxi : xi ∈ calM) :
      starCharacterPairing gamma (tau1M xi) =
        starCharacterPairing betaL (tau1M xi) := by
    have hdecomp : betaL =
        (((IrreducibleCharacter.trivial :
          IrreducibleCharacter (⊤ : Subgroup G) ℂ) :
            ClassFunction (⊤ : Subgroup G) ℂ)) - tau1L phi +
          (dataL.coefficient : ℂ) • dadeInd1CoherentSum HL tau1L +
          gamma := by
      simpa only [betaL, gamma, phiIrr] using dataL.decomposition
    symm
    rw [hdecomp, starCharacterPairing_add_left,
      starCharacterPairing_add_left, fgx_starPairing_sub_left,
      starCharacterPairing_smul_left, honeCross hxi,
      hcross hphi' hxi, hsumCross hxi]
    simp
  have hpsiOne : psi 1 = (HM.index : ℂ) := by
    simpa only [HM] using psi1
  have hcoeff {xi : ClassFunction M ℂ} (hxi : xi ∈ calM) :
      starCharacterPairing gamma (tau1M xi) =
        (a / (HM.index : ℂ)) * xi 1 := by
    rw [hgammaPair hxi]
    let pi : ClassFunction M ℂ := (psi 1) • xi - (xi 1) • psi
    have hpiClosure : pi ∈ AddSubgroup.closure
        (↑calM : Set (ClassFunction M ℂ)) := by
      obtain ⟨n, hn⟩ := Cnat_seqInd1 HM hxi
      unfold pi
      rw [hpsiOne, hn]
      have hleft := (AddSubgroup.closure
        (↑calM : Set (ClassFunction M ℂ))).nsmul_mem
          (hmemM hxi) HM.index
      have hright := (AddSubgroup.closure
        (↑calM : Set (ClassFunction M ℂ))).nsmul_mem
          (hmemM hpsi') n
      rw [← Nat.cast_smul_eq_nsmul (R := ℂ) HM.index xi] at hleft
      rw [← Nat.cast_smul_eq_nsmul (R := ℂ) n psi] at hright
      exact (AddSubgroup.closure
        (↑calM : Set (ClassFunction M ℂ))).sub_mem hleft hright
    have hpiOn : pi ∈ ClassFunction.supportedOn (nonidentitySet M) := by
      have hraw := sub_seqInd_on HM hxi hpsi'
      rw [ClassFunction.mem_supportedOn_iff] at hraw ⊢
      intro x hx
      apply hraw
      intro hxSharp
      apply hx
      simpa [nonidentitySet] using hxSharp.2
    have hagree : tau1M pi = Dade ddM pi :=
      cohM'.agrees pi hpiClosure hpiOn
    have hnuPiVirtual : ClassFunction.IsVirtual (tau1M pi) :=
      cohM'.mapsToVirtual pi hpiClosure
    have hzero : starCharacterPairing betaL (tau1M pi) = 0 := by
      rw [PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
        dataL.beta_virtual hnuPiVirtual, hagree]
      simpa only [betaL, dadeInd1Beta] using
        disjoint_Dade_ortho ddL ddM hdis
          (dadeInducedTrivial HL - phi) pi
    have hlinear : starCharacterPairing betaL (tau1M pi) =
        star (psi 1) * starCharacterPairing betaL (tau1M xi) -
          star (xi 1) * a := by
      unfold pi
      rw [map_sub, map_smul, map_smul, fgx_starPairing_sub_right,
        starCharacterPairing_smul_right,
        starCharacterPairing_smul_right]
    have hxiStar : star (xi 1) = xi 1 := by
      obtain ⟨n, hn⟩ := Cnat_seqInd1 HM hxi
      rw [hn]
      simp
    have hpsiStar : star (psi 1) = (HM.index : ℂ) := by
      rw [hpsiOne]
      simp
    have hrel : (HM.index : ℂ) *
        starCharacterPairing betaL (tau1M xi) = xi 1 * a := by
      have hrel0 : star (psi 1) *
            starCharacterPairing betaL (tau1M xi) -
          star (xi 1) * a = 0 := hlinear.symm.trans hzero
      rw [hpsiStar, hxiStar] at hrel0
      exact sub_eq_zero.mp hrel0
    have hindexNe : (HM.index : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr HM.index_ne_zero_of_finite
    calc
      starCharacterPairing betaL (tau1M xi) =
          (HM.index : ℂ)⁻¹ *
            ((HM.index : ℂ) *
              starCharacterPairing betaL (tau1M xi)) := by
        field_simp [hindexNe]
      _ = (HM.index : ℂ)⁻¹ * (xi 1 * a) := by rw [hrel]
      _ = (a / (HM.index : ℂ)) * xi 1 := by
        rw [div_eq_mul_inv]
        ring
  have hprojection :
      (∑ xi ∈ calM,
          Complex.normSq ((a / (HM.index : ℂ)) * xi 1)) ≤
        classFunctionNormSq gamma := by
    exact fgx_projection_le_norm calM tau1M
      (fun xi ↦ (a / (HM.index : ℂ)) * xi 1) gamma
      hnuOrthonormal (fun xi hxi ↦ hcoeff hxi)
  have hdegreeNormSum :
      (∑ xi ∈ calM, Complex.normSq (xi 1)) =
        (HM.index : ℝ) * ((Nat.card HM : ℝ) - 1) := by
    simpa only [calM] using
      fgx_seqInd_degree_normSq_sum HM
        (fun xi hxi ↦ FTtype1_Ind_irr M maxM Mtype1 xi
          (by simpa only [HM, FTType1SeqIndFamily] using hxi))
  have hindexPosNat : 0 < HM.index :=
    Nat.pos_of_ne_zero HM.index_ne_zero_of_finite
  have hindexPos : (0 : ℝ) < HM.index := by
    exact_mod_cast hindexPosNat
  have hsumCoeff :
      (∑ xi ∈ calM,
          Complex.normSq ((a / (HM.index : ℂ)) * xi 1)) =
        Complex.normSq a * ((Nat.card HM : ℝ) - 1) /
          (HM.index : ℝ) := by
    calc
      (∑ xi ∈ calM,
          Complex.normSq ((a / (HM.index : ℂ)) * xi 1)) =
          Complex.normSq (a / (HM.index : ℂ)) *
            ∑ xi ∈ calM, Complex.normSq (xi 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro xi _
        rw [Complex.normSq_mul]
      _ = Complex.normSq (a / (HM.index : ℂ)) *
          ((HM.index : ℝ) * ((Nat.card HM : ℝ) - 1)) := by
        rw [hdegreeNormSum]
      _ = Complex.normSq a * ((Nat.card HM : ℝ) - 1) /
          (HM.index : ℝ) := by
        rw [div_eq_mul_inv, Complex.normSq_mul, Complex.normSq_inv,
          Complex.normSq_natCast]
        field_simp [hindexPos.ne']
  obtain ⟨EL, hFrobInL⟩ := FTtype1_Frobenius L maxL Ltype1
  have hFrobL : IsFrobeniusDecomposition HL (EL.subgroupOf L) := by
    simpa only [HL, FTType1FittingIn] using
      fgx_frobeniusIn_decomposition hFrobInL
  have hindexBound : (HL.index : ℝ) ≤
      ((Nat.card HL : ℝ) - 1) / 2 :=
    odd_Frobenius_index_ler HL (EL.subgroupOf L) (mFT_odd L) hFrobL
  have hgammaUpper : classFunctionNormSq gamma ≤
      (HL.index : ℝ) - 1 := by
    simpa only [gamma] using (dataL.norm_bounds hindexBound).2
  have htauPsiVirtual : ClassFunction.IsVirtual (tau1M psi) :=
    cohM'.mapsToVirtual psi (hmemM hpsi')
  obtain ⟨n, hn⟩ :=
    PTypeCorePairingInternal.pTypeCore_virtual_pairing_isInt
      dataL.beta_virtual htauPsiVirtual
  have haEq : a = (n : ℂ) := by
    dsimp only [a]
    rw [PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
      dataL.beta_virtual htauPsiVirtual]
    exact hn
  have hnNe : n ≠ 0 := by
    intro hn0
    apply haNe
    rw [haEq, hn0]
    simp
  have haNorm : 1 ≤ Complex.normSq a := by
    rw [haEq]
    exact fgx_one_le_normSq_intCast n hnNe
  have hbaseNonneg :
      0 ≤ ((Nat.card HM : ℝ) - 1) / (HM.index : ℝ) := by
    have hcard : (1 : ℝ) ≤ Nat.card HM := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
    positivity
  have hlower :
      ((Nat.card HM : ℝ) - 1) / (HM.index : ℝ) ≤
        ∑ xi ∈ calM,
          Complex.normSq ((a / (HM.index : ℂ)) * xi 1) := by
    rw [hsumCoeff]
    simpa only [mul_div_assoc] using
      (le_mul_of_one_le_left hbaseNonneg haNorm)
  have hmain :
      ((Nat.card HM : ℝ) - 1) / (HM.index : ℝ) ≤
        (HL.index : ℝ) - 1 :=
    hlower.trans (hprojection.trans hgammaUpper)
  have hcardHM : Nat.card HM = Nat.card (Fitting_core M) := by
    simpa only [HM, FTType1FittingIn] using
      (Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
        (G := G) (H := Fitting_core M) (K := M) (Fcore_sub M))
  have hcardMOne : 1 ≤ Nat.card (Fitting_core M) :=
    Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  calc
    (((Nat.card (Fitting_core M) - 1 : ℕ) : ℝ) /
          ((FTType1FittingIn M).index : ℝ)) =
        ((Nat.card (Fitting_core M) : ℝ) - 1) /
          ((FTType1FittingIn M).index : ℝ) := by
      rw [Nat.cast_sub hcardMOne, Nat.cast_one]
    _ = ((Nat.card HM : ℝ) - 1) / (HM.index : ℝ) := by
      rw [hcardHM]
    _ ≤ (HL.index : ℝ) - 1 := hmain
    _ = ((FTType1FittingIn L).index : ℝ) - 1 := rfl

/-! ## The Appendix C exclusion -/

/-- `PFsection14.v: no_full_FT_Galois_structure`.

The full field-action alternative would force the larger prime complement
to have cardinality at most the smaller one, contrary to the Type-P
orientation. -/
theorem no_full_FT_Galois_structure
    {S T U W W₁ W₂ : Subgroup G}
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (maxS : S ∈ minSimple_max_groups (G := G))
    (StypeP : of_typeP S U W W₁ W₂ defW)
    (hq_lt_hp : Nat.card W₁ < Nat.card W₂) :
    ¬ ((∃ fieldModel : FiniteFieldImage (Fitting_core S) W₂ U,
          Nat.card (Fitting_core S) =
              Nat.card W₂ ^ Nat.card W₁ ∧
            Nat.card U = nU (Nat.card W₂) (Nat.card W₁) ∧
            (nU (Nat.card W₂) (Nat.card W₁)).Coprime
              (Nat.card W₂ - 1)) ∧
        IsElementaryAbelianGroup (Nat.card W₁) (Fitting_core T) ∧
        W₂ ≤ Subgroup.normalizer (Fitting_core T : Set G) ∧
        ∃ y : G, y ∈ Fitting_core T ∧
          appendixCP1 W₂ y ≤ Subgroup.normalizer (U : Set G)) := by
  rintro ⟨⟨fieldModel, hPcard, hUcard, hcoprime⟩,
    hQelementary, hW₂normalizesQ, hy⟩

  obtain ⟨hqPrime, hpPrime⟩ :=
    FTtypeP_primes S U W W₁ W₂ defW maxS StypeP
  letI : Fact (Nat.card W₂).Prime := ⟨hpPrime⟩
  letI : Fact (Nat.card W₁).Prime := ⟨hqPrime⟩

  have hfieldCardNat :
      Nat.card fieldModel.F = Nat.card W₂ ^ Nat.card W₁ :=
    fieldModel.natCard_P_eq_field.symm.trans hPcard
  have hfieldCardFin :
      Fintype.card fieldModel.F = Nat.card W₂ ^ Nat.card W₁ := by
    rw [Fintype.card_eq_nat_card]
    exact hfieldCardNat
  letI : CharP fieldModel.F (Nat.card W₂) :=
    charP_of_card_eq_prime_pow hfieldCardFin
  letI : Algebra (ZMod (Nat.card W₂)) fieldModel.F :=
    ZMod.algebra fieldModel.F (Nat.card W₂)

  have hproduct : IsInternalSemidirectProductIn
      (Fitting_core S) U (derivedWithin S) :=
    StypeP.2.1.2.2.2
  have hP_in_D : Fitting_core S ≤ derivedWithin S := hproduct.1
  have hU_in_D : U ≤ derivedWithin S := hproduct.2.1
  have hcomplement :
      ((Fitting_core S).subgroupOf (derivedWithin S)).IsComplement'
        (U.subgroupOf (derivedWithin S)) :=
    hproduct.2.2.2
  have hD_normalizes_P :
      derivedWithin S ≤
        Subgroup.normalizer (Fitting_core S : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP_in_D).mp
      hproduct.2.2.1
  have hU_normalizes_P :
      U ≤ Subgroup.normalizer (Fitting_core S : Set G) :=
    hU_in_D.trans hD_normalizes_P

  have hp_le_hq : Nat.card W₂ ≤ Nat.card W₁ :=
    prime_dim_normed_finField
      (p := Nat.card W₂) (q := Nat.card W₁)
      (H := derivedWithin S) (P := Fitting_core S)
      (P0 := W₂) (U := U) (Q := Fitting_core T)
      fieldModel hP_in_D hU_in_D hcomplement hU_normalizes_P
      hPcard hUcard hcoprime hQelementary hW₂normalizesQ hy
      (Submission.OddOrder.BG.AppendixC.FiniteFieldImage.BGappendixC3_step4
        (p := Nat.card W₂) (q := Nat.card W₁)
        (H := derivedWithin S) (P := Fitting_core S)
        (P0 := W₂) (U := U) (Q := Fitting_core T)
        fieldModel hP_in_D hU_in_D hcomplement hU_normalizes_P
        hPcard hUcard hcoprime hQelementary hW₂normalizesQ hq_lt_hp)
      (fun hfour ↦
        largeDegreeCharacterObligation
          (p := Nat.card W₂) (q := Nat.card W₁)
          (H := derivedWithin S) (P := Fitting_core S)
          (P0 := W₂) (U := U)
          fieldModel hP_in_D hU_in_D hcomplement hU_normalizes_P
          hPcard hUcard hq_lt_hp hfour)
  exact (Nat.not_lt_of_ge hp_le_hq) hq_lt_hp

end

end Submission.OddOrder.PF
