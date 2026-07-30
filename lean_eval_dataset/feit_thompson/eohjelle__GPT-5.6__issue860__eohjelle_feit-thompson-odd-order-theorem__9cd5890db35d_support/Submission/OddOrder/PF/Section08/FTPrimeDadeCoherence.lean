import Submission.OddOrder.PF.Section05.CoherenceExtension
import Submission.OddOrder.PF.Section07.DadeCoverSeqInd
import Submission.OddOrder.PF.Section08.FTTypeContexts

/-!
# Type-P prime-Dade coherence

This module assembles the Section 8 prime-Dade data attached to a type-P
maximal subgroup.  It first transports the exceptional type-P pair to a
chosen witness, then packages the cyclic-TI and prime-TI hypotheses, and
finally exposes the subcoherent family and the reduced-column consequences
used by the later Peterfalvi sections.
-/

namespace Submission.OddOrder.PF

open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section14
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open FTContextInternal
open scoped BigOperators Classical Pointwise

noncomputable section

universe u v

variable {Gamma : Type u} [Group Gamma] [Fintype Gamma]

local instance primeDadeCoherenceInvertibleCard
    {Q : Type v} [Group Q] [Fintype Q] :
    Invertible (Nat.card Q : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

@[simp]
private theorem conjugateSubgroup8_one8
    [IsMinSimpleOddGroup Gamma] (H : Subgroup Gamma) :
    conjugateSubgroup8 H 1 = H := by
  unfold conjugateSubgroup8
  convert H.map_id using 1
  ext x
  simp

private theorem FTtype_conjugate8
    [IsMinSimpleOddGroup Gamma] (H : Subgroup Gamma) (x : Gamma) :
    FTtype (conjugateSubgroup8 H x) = FTtype H := by
  simpa [conjugateSubgroup8, conjugateSubgroup16] using FTtypeJ H x

/-! ## The exceptional pair at a fixed type-P witness -/

/-- Simultaneous ambient conjugation preserves subgroup conjugacy. -/
private theorem areConjugateSubgroups_conjugate8
    [IsMinSimpleOddGroup Gamma]
    {A B : Subgroup Gamma} (hAB : AreConjugateSubgroups A B)
    (x : Gamma) :
    AreConjugateSubgroups (conjugateSubgroup8 A x)
      (conjugateSubgroup8 B x) := by
  rcases hAB with ⟨g, hg⟩
  have hg' : B = conjugateSubgroup8 A g := by
    simpa [conjugateSubgroup8] using hg
  refine ⟨x * g * x⁻¹, ?_⟩
  calc
    conjugateSubgroup8 B x =
        conjugateSubgroup8 (conjugateSubgroup8 A g) x := by rw [hg']
    _ = conjugateSubgroup8 A (x * g) :=
      conjugateSubgroup8_mul A g x
    _ = conjugateSubgroup8 A ((x * g * x⁻¹) * x) := by
      simp [mul_assoc]
    _ = conjugateSubgroup8 (conjugateSubgroup8 A x)
        (x * g * x⁻¹) :=
      (conjugateSubgroup8_mul A x (x * g * x⁻¹)).symm

/-- The exceptional pair is invariant under an ambient automorphism coming
from conjugation. -/
private theorem typePPair_conjugate8
    [IsMinSimpleOddGroup Gamma]
    {S T W W₁ W₂ : Subgroup Gamma}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (hpair : typeP_pair S T W W₁ W₂ defW) (x : Gamma) :
    typeP_pair
      (conjugateSubgroup8 S x) (conjugateSubgroup8 T x)
      (conjugateSubgroup8 W x) (conjugateSubgroup8 W₁ x)
      (conjugateSubgroup8 W₂ x)
      (directProduct_map_mulEquiv8 defW (MulAut.conj x)) := by
  let e : Gamma ≃* Gamma := MulAut.conj x
  change typeP_pair
    (S.map e.toMonoidHom) (T.map e.toMonoidHom)
    (W.map e.toMonoidHom) (W₁.map e.toMonoidHom)
    (W₂.map e.toMonoidHom)
    (directProduct_map_mulEquiv8 defW e)
  have htypeS : FTtype (S.map e.toMonoidHom) = FTtype S := by
    simpa [e, conjugateSubgroup8] using FTtype_conjugate8 S x
  have htypeT : FTtype (T.map e.toMonoidHom) = FTtype T := by
    simpa [e, conjugateSubgroup8] using FTtype_conjugate8 T x
  refine
    { cyclic_ti := ?_
      S_maximal := (mmaxJ S e).mpr hpair.S_maximal
      T_maximal := (mmaxJ T e).mpr hpair.T_maximal
      S_decomposition := ?_
      T_decomposition := ?_
      intersection_eq := ?_
      one_type_two := by
        simpa only [htypeS, htypeT] using hpair.one_type_two
      S_type_range := by
        simpa only [htypeS] using hpair.S_type_range
      T_type_range := by
        simpa only [htypeT] using hpair.T_type_range
      controls_non_type_one := ?_ }
  · refine
      { cyclic := (e.subgroupMap W).isCyclic.mp hpair.cyclic_ti.cyclic
        odd_card := ?_
        normedTI := ?_ }
    · rw [Subgroup.card_map_of_injective e.injective]
      exact hpair.cyclic_ti.odd_card
    · have hmap := isNormalizedTI_map_mulEquiv8
        hpair.cyclic_ti.normedTI e
      rw [cyclicTISet_map_mulEquiv8 W W₁ W₂ e]
      simpa [e, conjugateSubgroup8] using hmap
  · have hmap := semidirect_map_mulEquiv8 hpair.S_decomposition e
    change IsInternalSemidirectProductIn
      (derivedWithin (S.map e.toMonoidHom))
      (W₁.map e.toMonoidHom) (S.map e.toMonoidHom)
    rw [derivedWithin_map_mulEquiv_type8]
    exact hmap
  · have hmap := semidirect_map_mulEquiv8 hpair.T_decomposition e
    change IsInternalSemidirectProductIn
      (derivedWithin (T.map e.toMonoidHom))
      (W₂.map e.toMonoidHom) (T.map e.toMonoidHom)
    rw [derivedWithin_map_mulEquiv_type8]
    exact hmap
  · calc
      conjugateSubgroup8 S x ⊓ conjugateSubgroup8 T x =
          (S ⊓ T).map e.toMonoidHom :=
        (Subgroup.map_inf S T e.toMonoidHom e.injective).symm
      _ = conjugateSubgroup8 W x := by
        rw [hpair.intersection_eq]
        rfl
  · intro L hmaxL hnotL
    let L₀ := conjugateSubgroup8 L x⁻¹
    have hmaxL₀ : L₀ ∈ minSimple_max_groups (G := Gamma) :=
      (mmaxJ L (MulAut.conj x⁻¹)).mpr hmaxL
    have hnotL₀ : FTtype L₀ ≠ 1 := by
      intro hL₀
      apply hnotL
      calc
        FTtype L = FTtype L₀ := (FTtype_conjugate8 L x⁻¹).symm
        _ = 1 := hL₀
    have hL₀x : conjugateSubgroup8 L₀ x = L := by
      dsimp only [L₀]
      rw [conjugateSubgroup8_mul]
      rw [mul_inv_cancel, conjugateSubgroup8_one8]
    rcases hpair.controls_non_type_one L₀ hmaxL₀ hnotL₀ with hS | hT
    · left
      have h := areConjugateSubgroups_conjugate8 hS x
      rwa [hL₀x] at h
    · right
      have h := areConjugateSubgroups_conjugate8 hT x
      rwa [hL₀x] at h

/-- Move an exceptional pair whose first member is conjugate to `M` onto the
chosen type-P decomposition of `M`. -/
private theorem alignTypePPair8
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ S T Us Ws Ws₁ Ws₂ : Subgroup Gamma}
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (defWs : IsInternalDirectProductIn Ws₁ Ws₂ Ws)
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (pairST : typeP_pair S T Ws Ws₁ Ws₂ defWs)
    (hSM : AreConjugateSubgroups S M)
    (StypeP : of_typeP S Us Ws Ws₁ Ws₂ defWs) :
    ∃ T' : Subgroup Gamma,
      typeP_pair M T' W W₁ W₂ defW ∧
        ∃ xdefW : IsInternalDirectProductIn W₂ W₁ W,
          ∃ V : Subgroup Gamma, of_typeP T' V W W₂ W₁ xdefW := by
  rcases hSM with ⟨g, hMg⟩
  let eg : Gamma ≃* Gamma := MulAut.conj g
  let defWg : IsInternalDirectProductIn
      (conjugateSubgroup8 Ws₁ g) (conjugateSubgroup8 Ws₂ g)
      (conjugateSubgroup8 Ws g) := by
    simpa [eg, conjugateSubgroup8] using
      directProduct_map_mulEquiv8 defWs eg
  have pairG : typeP_pair
      (conjugateSubgroup8 S g) (conjugateSubgroup8 T g)
      (conjugateSubgroup8 Ws g) (conjugateSubgroup8 Ws₁ g)
      (conjugateSubgroup8 Ws₂ g) defWg := by
    simpa only [eg, defWg] using typePPair_conjugate8 pairST g
  obtain ⟨defWg', StypePg⟩ :=
    conj_of_typeP S Us Ws Ws₁ Ws₂ defWs StypeP g
  have hdef : defWg' = defWg := Subsingleton.elim _ _
  subst defWg'
  have hMg' : M = conjugateSubgroup8 S g := by
    simpa [conjugateSubgroup8] using hMg
  rw [← hMg'] at pairG StypePg
  obtain ⟨y, hyM, _hyU, hyW₁, hyW₂, hyW⟩ :=
    of_typeP_conj M U W W₁ W₂
      (conjugateSubgroup8 Us g) (conjugateSubgroup8 Ws g)
      (conjugateSubgroup8 Ws₁ g) (conjugateSubgroup8 Ws₂ g)
      defW defWg hmaxM MtypeP StypePg
  let T' := conjugateSubgroup8 (conjugateSubgroup8 T g) y⁻¹
  have hMfix : conjugateSubgroup8 M y⁻¹ = M :=
    conjugateSubgroup8_eq_self_of_mem_normalizer
      (Subgroup.le_normalizer (M.inv_mem hyM))
  have hWfix :
      conjugateSubgroup8 (conjugateSubgroup8 Ws g) y⁻¹ = W := by
    rw [← hyW, conjugateSubgroup8_mul]
    rw [inv_mul_cancel, conjugateSubgroup8_one8]
  have hW₁fix :
      conjugateSubgroup8 (conjugateSubgroup8 Ws₁ g) y⁻¹ = W₁ := by
    rw [← hyW₁, conjugateSubgroup8_mul]
    rw [inv_mul_cancel, conjugateSubgroup8_one8]
  have hW₂fix :
      conjugateSubgroup8 (conjugateSubgroup8 Ws₂ g) y⁻¹ = W₂ := by
    rw [← hyW₂, conjugateSubgroup8_mul]
    rw [inv_mul_cancel, conjugateSubgroup8_one8]
  have pairBack := typePPair_conjugate8 pairG y⁻¹
  have pairMT : typeP_pair M T' W W₁ W₂ defW := by
    simpa only [T', hMfix, hWfix, hW₁fix, hW₂fix] using pairBack
  let xdefW : IsInternalDirectProductIn W₂ W₁ W := defW.swap
  have pairTM : typeP_pair T' M W W₂ W₁ xdefW :=
    typeP_pair_sym M T' W W₁ W₂ defW xdefW pairMT
  obtain ⟨V, TtypeP⟩ := typeP_pairW T' M W W₂ W₁ xdefW pairTM
  exact ⟨T', pairMT, xdefW, V, TtypeP⟩

/-- `PFsection8.v: FT_cyclicTI_hyp`. -/
theorem FT_cyclicTI_hyp
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (MtypeP : of_typeP M U W W₁ W₂ defW) :
    CyclicTIHypothesis (⊤ : Subgroup Gamma) W W₁ W₂ defW :=
  (typeP_context M U W W₁ W₂ defW MtypeP).cyclic_ti

/-- `PFsection8.v: FTtypeP_pair_witness`, combining the exceptional-pair
alternative with the chosen type-P witness. -/
theorem FTtypeP_pair_witness
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW) :
    ∃ T : Subgroup Gamma,
      typeP_pair M T W W₁ W₂ defW ∧
        ∃ xdefW : IsInternalDirectProductIn W₂ W₁ W,
          ∃ V : Subgroup Gamma, of_typeP T V W W₂ W₁ xdefW := by
  have hnot1 := FTtypeP_neq1 M U W W₁ W₂ defW hmaxM MtypeP
  rcases (FTtypeP_pair_cases (G := Gamma)) with hAll | hExceptional
  · exact (hnot1 (hAll M hmaxM)).elim
  · rcases hExceptional with ⟨S, T, Us, Ws, Ws₁, Ws₂, defWs, pairST⟩
    let xdefWs : IsInternalDirectProductIn Ws₂ Ws₁ Ws := defWs.swap
    have pairTS : typeP_pair T S Ws Ws₂ Ws₁ xdefWs :=
      typeP_pair_sym S T Ws Ws₁ Ws₂ defWs xdefWs pairST
    obtain ⟨Us', StypeP⟩ := typeP_pairW S T Ws Ws₁ Ws₂ defWs pairST
    obtain ⟨Vs', TtypeP⟩ := typeP_pairW T S Ws Ws₂ Ws₁ xdefWs pairTS
    rcases pairST.controls_non_type_one M hmaxM hnot1 with hSM | hTM
    · exact alignTypePPair8 defW defWs hmaxM MtypeP pairST hSM StypeP
    · exact alignTypePPair8 defW xdefWs hmaxM MtypeP pairTS hTM TtypeP

/-- An element fixing all three displayed factors normalizes the cyclic-TI
set. -/
private theorem mem_normalizer_cyclicTISet_of_fixes8
    [IsMinSimpleOddGroup Gamma]
    {W W₁ W₂ : Subgroup Gamma} {x : Gamma}
    (hW : conjugateSubgroup8 W x = W)
    (hW₁ : conjugateSubgroup8 W₁ x = W₁)
    (hW₂ : conjugateSubgroup8 W₂ x = W₂) :
    x ∈ Subgroup.normalizer (cyclicTISet W W₁ W₂) := by
  let e : Gamma ≃* Gamma := MulAut.conj x
  have hW' : W.map e.toMonoidHom = W := by
    simpa only [e, conjugateSubgroup8] using hW
  have hW₁' : W₁.map e.toMonoidHom = W₁ := by
    simpa only [e, conjugateSubgroup8] using hW₁
  have hW₂' : W₂.map e.toMonoidHom = W₂ := by
    simpa only [e, conjugateSubgroup8] using hW₂
  have himage := cyclicTISet_map_mulEquiv8 W W₁ W₂ e
  rw [hW', hW₁', hW₂'] at himage
  apply Subgroup.mem_set_normalizer_iff.mpr
  intro a
  constructor
  · intro ha
    rw [himage]
    exact ⟨a, ha, by simp [e, MulAut.conj_apply]⟩
  · intro hxa
    have hea : e a ∈ cyclicTISet W W₁ W₂ := by
      simpa [e, MulAut.conj_apply] using hxa
    have heaImage : e a ∈ e '' cyclicTISet W W₁ W₂ := by
      rw [← himage]
      exact hea
    rcases heaImage with ⟨b, hb, hba⟩
    simpa only [e.injective hba] using hb

/-- `PFsection8.v: of_typeP_pair`, the converse form of the pair witness. -/
theorem of_typeP_pair
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    {T V : Subgroup Gamma}
    (xdefW : IsInternalDirectProductIn W₂ W₁ W)
    (hmaxT : T ∈ minSimple_max_groups (G := Gamma))
    (TtypeP : of_typeP T V W W₂ W₁ xdefW) :
    typeP_pair M T W W₁ W₂ defW := by
  obtain ⟨S, pairMS, xdefS, V₁, StypeP⟩ :=
    FTtypeP_pair_witness defW hmaxM MtypeP
  have hnotT := FTtypeP_neq1 T V W W₂ W₁ xdefW hmaxT TtypeP
  rcases pairMS.controls_non_type_one T hmaxT hnotT with hMT | hST
  · rcases hMT with ⟨x, hTx⟩
    have hTx' : T = conjugateSubgroup8 M x := by
      simpa [conjugateSubgroup8] using hTx
    obtain ⟨defWx, MtypePx⟩ :=
      conj_of_typeP M U W W₁ W₂ defW MtypeP x
    rw [← hTx'] at MtypePx
    obtain ⟨y, _hyT, _hyU, hyW₂, _hyW₁, _hyW⟩ :=
      of_typeP_conj T V W W₂ W₁
        (conjugateSubgroup8 U x) (conjugateSubgroup8 W x)
        (conjugateSubgroup8 W₁ x) (conjugateSubgroup8 W₂ x)
        xdefW defWx hmaxT TtypeP MtypePx
    have hcardW₂ : Nat.card (conjugateSubgroup8 W₂ y) = Nat.card W₂ :=
      Subgroup.card_map_of_injective (MulAut.conj y).injective
    have hcardW₁ : Nat.card (conjugateSubgroup8 W₁ x) = Nat.card W₁ :=
      Subgroup.card_map_of_injective (MulAut.conj x).injective
    have hcardEq : Nat.card W₂ = Nat.card W₁ := by
      calc
        Nat.card W₂ = Nat.card (conjugateSubgroup8 W₂ y) := hcardW₂.symm
        _ = Nat.card (conjugateSubgroup8 W₁ x) :=
          congrArg (fun H : Subgroup Gamma ↦ Nat.card H) hyW₂
        _ = Nat.card W₁ := hcardW₁
    exact (pairMS.cyclic_ti.factor_card_ne hcardEq.symm).elim
  · rcases hST with ⟨x, hTx⟩
    have hTx' : T = conjugateSubgroup8 S x := by
      simpa [conjugateSubgroup8] using hTx
    obtain ⟨xdefSx, StypePx⟩ :=
      conj_of_typeP S V₁ W W₂ W₁ xdefS StypeP x
    rw [← hTx'] at StypePx
    obtain ⟨y, hyT, _hyV, hyW₂, hyW₁, hyW⟩ :=
      of_typeP_conj T V W W₂ W₁
        (conjugateSubgroup8 V₁ x) (conjugateSubgroup8 W x)
        (conjugateSubgroup8 W₂ x) (conjugateSubgroup8 W₁ x)
        xdefW xdefSx hmaxT TtypeP StypePx
    let q : Gamma := x⁻¹ * y
    have hWq : conjugateSubgroup8 W q = W := by
      calc
        conjugateSubgroup8 W q =
            conjugateSubgroup8 (conjugateSubgroup8 W y) x⁻¹ :=
          (conjugateSubgroup8_mul W y x⁻¹).symm
        _ = conjugateSubgroup8 (conjugateSubgroup8 W x) x⁻¹ := by rw [hyW]
        _ = conjugateSubgroup8 W (x⁻¹ * x) :=
          conjugateSubgroup8_mul W x x⁻¹
        _ = W := by rw [inv_mul_cancel, conjugateSubgroup8_one8]
    have hW₁q : conjugateSubgroup8 W₁ q = W₁ := by
      calc
        conjugateSubgroup8 W₁ q =
            conjugateSubgroup8 (conjugateSubgroup8 W₁ y) x⁻¹ :=
          (conjugateSubgroup8_mul W₁ y x⁻¹).symm
        _ = conjugateSubgroup8 (conjugateSubgroup8 W₁ x) x⁻¹ := by rw [hyW₁]
        _ = conjugateSubgroup8 W₁ (x⁻¹ * x) :=
          conjugateSubgroup8_mul W₁ x x⁻¹
        _ = W₁ := by rw [inv_mul_cancel, conjugateSubgroup8_one8]
    have hW₂q : conjugateSubgroup8 W₂ q = W₂ := by
      calc
        conjugateSubgroup8 W₂ q =
            conjugateSubgroup8 (conjugateSubgroup8 W₂ y) x⁻¹ :=
          (conjugateSubgroup8_mul W₂ y x⁻¹).symm
        _ = conjugateSubgroup8 (conjugateSubgroup8 W₂ x) x⁻¹ := by rw [hyW₂]
        _ = conjugateSubgroup8 W₂ (x⁻¹ * x) :=
          conjugateSubgroup8_mul W₂ x x⁻¹
        _ = W₂ := by rw [inv_mul_cancel, conjugateSubgroup8_one8]
    have hqNorm : q ∈ Subgroup.normalizer (cyclicTISet W W₁ W₂) :=
      mem_normalizer_cyclicTISet_of_fixes8 hWq hW₁q hW₂q
    have hqW : q ∈ W := by
      have hqInf : q ∈ (⊤ : Subgroup Gamma) ⊓
          Subgroup.normalizer (cyclicTISet W W₁ W₂) :=
        ⟨Subgroup.mem_top q, hqNorm⟩
      rw [pairMS.cyclic_ti.normedTI.inf_normalizer_eq] at hqInf
      exact hqInf
    have hWT : W ≤ T := by
      rw [← directProduct_sup_eq8 xdefW]
      exact sup_le TtypeP.1.2.1.1
        (TtypeP.2.2.2.1.2.2.1.trans (Fcore_sub T))
    have hqT : q ∈ T := hWT hqW
    have hxInvT : x⁻¹ ∈ T := by
      have hxInvEq : x⁻¹ = q * y⁻¹ := by simp [q, mul_assoc]
      rw [hxInvEq]
      exact T.mul_mem hqT (T.inv_mem hyT)
    have hTfix : conjugateSubgroup8 T x⁻¹ = T :=
      conjugateSubgroup8_eq_self_of_mem_normalizer
        (Subgroup.le_normalizer hxInvT)
    have hTback : conjugateSubgroup8 T x⁻¹ = S := by
      rw [hTx', conjugateSubgroup8_mul]
      rw [inv_mul_cancel, conjugateSubgroup8_one8]
    have hSTeq : S = T := hTback.symm.trans hTfix
    simpa only [hSTeq] using pairMS

/-! ## Cyclic-TI and prime-TI data -/

private theorem secondDerivedWithin_le_derivedWithin8
    [IsMinSimpleOddGroup Gamma] (M : Subgroup Gamma) :
    secondDerivedWithin M ≤ derivedWithin M := by
  change (_root_.commutator (derivedWithin M)).map
      (derivedWithin M).subtype ≤ derivedWithin M
  exact Subgroup.map_subtype_le _

/-- `PFsection8.v: FT_primeTI_hyp`. -/
theorem FT_primeTI_hyp
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (MtypeP : of_typeP M U W W₁ W₂ defW) :
    PrimeTIHypothesis M (derivedWithin M) W W₁ W₂ defW := by
  obtain ⟨⟨hW₁cyclic, ⟨_, hW₁hall⟩, hW₁ne, hsemi⟩,
    _, _, ⟨hW₂cyclic, hW₂ne, _, hW₂second, hcentralizer⟩, _⟩ := MtypeP
  refine
    { semidirect := hsemi
      complement_ne_bot := hW₁ne
      complement_hall := hW₁hall
      complement_cyclic := hW₁cyclic
      fixed_ne_bot := hW₂ne
      fixed_le_kernel := hW₂second.trans
        (secondDerivedWithin_le_derivedWithin8 M)
      fixed_cyclic := hW₂cyclic
      centralizer_kernel := ?_
      odd_card := mFT_odd W }
  intro x hx
  have hxAmbient : (x : Gamma) ≠ 1 := by
    intro hxOne
    apply hx
    apply Subtype.ext
    exact hxOne
  exact hcentralizer (x : Gamma) ⟨x.property, hxAmbient⟩

/-! ## The two prime-Dade hypotheses -/

/-- `PFsection8.v: FTtypeP_supp0_def`. -/
theorem FTtypeP_supp0_def
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW) :
    FTsupport0 M =
      FTsupport M ∪ classSupportWithin M (cyclicTISet W W₁ W₂) := by
  have hdiff := FTsupp0_typeP M U W₁ W₂ W defW hmaxM MtypeP
  ext x
  constructor
  · intro hx
    by_cases hxSupport : x ∈ FTsupport M
    · exact Or.inl hxSupport
    · right
      simpa [cyclicTISet, ← hdiff] using
        (show x ∈ FTsupport0 M \ FTsupport M from ⟨hx, hxSupport⟩)
  · rintro (hxSupport | hxClass)
    · exact FTsupp_sub0 M hxSupport
    · have hxDiff : x ∈ FTsupport0 M \ FTsupport M := by
        rw [hdiff]
        simpa [cyclicTISet] using hxClass
      exact hxDiff.1

private theorem centralizerSupport_le_FTsupport8
    [IsMinSimpleOddGroup Gamma]
    {M H : Subgroup Gamma}
    (hnot1 : FTtype M ≠ 1)
    (hHsupport : subgroupNonidentity H ⊆ FTsupport1 M) :
    primeDadeCentralizerSupport (derivedWithin M) H ⊆ FTsupport M := by
  rintro x ⟨hxD, hx1, h, hhH, hh1, hxh⟩
  simp only [FTsupport, ftSupport, Set.mem_iUnion]
  refine ⟨h, hHsupport ⟨hhH, hh1⟩, ⟨⟨?_, ?_⟩, hx1⟩⟩
  · simpa [FTder, ftDerived, hnot1] using hxD
  · intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (hxh.zpow_right n).symm.eq

private theorem FTsupport_le_derived_diff_one8
    [IsMinSimpleOddGroup Gamma] {M : Subgroup Gamma}
    (hnot1 : FTtype M ≠ 1) :
    FTsupport M ⊆ (derivedWithin M : Set Gamma) \ {1} := by
  intro x hx
  simp only [FTsupport, ftSupport, Set.mem_iUnion] at hx
  rcases hx with ⟨h, _, hx⟩
  exact ⟨by simpa [FTder, ftDerived, hnot1] using hx.1.1, hx.2⟩

/-- `PFsection8.v: FT_Fcore_prime_Dade_def`. -/
theorem FT_Fcore_prime_Dade_def
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW) :
    PrimeDadeDefinition M (derivedWithin M) (Fitting_core M)
      (FTsupport M) (FTsupport0 M) W W₁ W₂ defW where
  normal_subgroup := ⟨Fcore_sub M, Fcore_normal M⟩
  fixed_le_subgroup := MtypeP.2.2.2.1.2.2.1
  subgroup_le_kernel := MtypeP.2.1.2.2.2.1
  normal_set := ⟨fun _ hx ↦ (FTsupp_sub M hx).1, FTsupp_norm M⟩
  centralizerSupport_le := centralizerSupport_le_FTsupport8
    (FTtypeP_neq1 M U W W₁ W₂ defW hmaxM MtypeP)
    (Fcore_sub_FTsupp1 hmaxM)
  set_le_kernel_diff_one := FTsupport_le_derived_diff_one8
    (FTtypeP_neq1 M U W W₁ W₂ defW hmaxM MtypeP)
  dadeSet_eq := FTtypeP_supp0_def defW hmaxM MtypeP

/-- `PFsection8.v: FT_prDade_hypF`. -/
def FT_prDade_hypF
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW) :
    PrimeDadeHypothesis (⊤ : Subgroup Gamma) M (derivedWithin M)
      (Fitting_core M) (FTsupport M) (FTsupport0 M) W W₁ W₂ defW where
  prDade_cycTI := FT_cyclicTI_hyp defW MtypeP
  prDade_prTI := FT_primeTI_hyp defW MtypeP
  prDade_hyp := FT_Dade0_hyp M hmaxM
  prDade_def := FT_Fcore_prime_Dade_def defW hmaxM MtypeP

/-- `PFsection8.v: FT_core_prime_Dade_def`. -/
theorem FT_core_prime_Dade_def
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW) :
    PrimeDadeDefinition M (derivedWithin M) (FTcore M)
      (FTsupport M) (FTsupport0 M) W W₁ W₂ defW where
  normal_subgroup := FTcore_normal M
  fixed_le_subgroup :=
    MtypeP.2.2.2.1.2.2.1.trans (Fcore_sub_FTcore hmaxM)
  subgroup_le_kernel := FTcore_sub_der1 hmaxM
  normal_set := ⟨fun _ hx ↦ (FTsupp_sub M hx).1, FTsupp_norm M⟩
  centralizerSupport_le := centralizerSupport_le_FTsupport8
    (FTtypeP_neq1 M U W W₁ W₂ defW hmaxM MtypeP) Set.Subset.rfl
  set_le_kernel_diff_one := FTsupport_le_derived_diff_one8
    (FTtypeP_neq1 M U W W₁ W₂ defW hmaxM MtypeP)
  dadeSet_eq := FTtypeP_supp0_def defW hmaxM MtypeP

/-- `PFsection8.v: FT_prDade_hyp`. -/
def FT_prDade_hyp
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW) :
    PrimeDadeHypothesis (⊤ : Subgroup Gamma) M (derivedWithin M)
      (FTcore M) (FTsupport M) (FTsupport0 M) W W₁ W₂ defW where
  prDade_cycTI := FT_cyclicTI_hyp defW MtypeP
  prDade_prTI := FT_primeTI_hyp defW MtypeP
  prDade_hyp := FT_Dade0_hyp M hmaxM
  prDade_def := FT_core_prime_Dade_def defW hmaxM MtypeP

/-! ## Canonical subcoherent families -/

section Coherence

variable {Gamma0 : Type} [Group Gamma0] [Fintype Gamma0]

/-- The normally induced kernel layer called `calS` in the source. -/
def FTtypePKernelLayer
    {G M K H W W₁ W₂ : Subgroup Gamma0}
    {A A₀ : Set Gamma0}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (pd : PrimeDadeHypothesis G M K H A A₀ W W₁ W₂ defW) :
    Set (ClassFunction M ℂ) :=
  ↑(seqIndD (k := ℂ) (K.subgroupOf M) pd.signalizerInKernel ⊥)

private theorem kernelLayer_conjugation_closed8
    {G M K H W W₁ W₂ : Subgroup Gamma0}
    {A A₀ : Set Gamma0}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (pd : PrimeDadeHypothesis G M K H A A₀ W W₁ W₂ defW) :
    cfConjC_subset (FTtypePKernelLayer pd) (FTtypePKernelLayer pd) := by
  refine ⟨Set.Subset.rfl, ?_⟩
  intro phi hphi
  exact seqInd_inverse_mem (k := ℂ)
    (K.subgroupOf M) pd.signalizerInKernel ⊥ hphi

private theorem kernelLayer_nonreal8
    {G M K H W W₁ W₂ : Subgroup Gamma0}
    {A A₀ : Set Gamma0}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (pd : PrimeDadeHypothesis G M K H A A₀ W W₁ W₂ defW)
    (hoddM : Odd (Nat.card M)) :
    ∀ phi ∈ FTtypePKernelLayer pd,
      ClassFunction.inverseLinear phi ≠ phi := by
  letI : (K.subgroupOf M).Normal := pd.prDade_prTI.kernel_normal
  intro phi hphi
  exact seqInd_conjC_neq (k := ℂ) (K.subgroupOf M) hoddM
    pd.signalizerInKernel ⊥ hphi

/-- `PFsection8.v: FTtypeP_coh_base_sig`. -/
theorem FTtypeP_coh_base_sig
    {G M K H W W₁ W₂ : Subgroup Gamma0}
    {A A₀ : Set Gamma0}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (pd : PrimeDadeHypothesis G M K H A A₀ W W₁ W₂ defW)
    (isoM : CyclicTIIsometryData (k := ℂ)
      pd.prDade_prTI.prime_cycTIhyp)
    (isoG : CyclicTIIsometryData (k := ℂ) pd.prDade_cycTI)
    (hoddM : Odd (Nat.card M)) :
    ∃ R : ClassFunction M ℂ → Finset (ClassFunction G ℂ),
      subcoherent (FTtypePKernelLayer pd) (Dade pd.prDade_hyp) R ∧
        (∀ phi ∈ FTtypePKernelLayer pd,
          IsIrreducibleCharacter M ℂ phi →
          ∀ w : IrreducibleCharacter W ℂ, ∀ alpha ∈ R phi,
            characterPairing alpha
              (isoG.linearMap (w : ClassFunction W ℂ)) = 0) ∧
        ∀ j : IrreducibleCharacter W₂ ℂ,
          R (pd.prDade_prTI.primeTIRed isoM j) =
            pd.primeDadeReducedImageFamily isoM isoG j := by
  exact pd.prDade_subcoherent isoM isoG (FTtypePKernelLayer pd)
    (kernelLayer_conjugation_closed8 pd) (kernelLayer_nonreal8 pd hoddM)

/-- `PFsection8.v: FTtypeP_coh_base`. -/
noncomputable def FTtypeP_coh_base
    {G M K H W W₁ W₂ : Subgroup Gamma0}
    {A A₀ : Set Gamma0}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (pd : PrimeDadeHypothesis G M K H A A₀ W W₁ W₂ defW)
    (isoM : CyclicTIIsometryData (k := ℂ)
      pd.prDade_prTI.prime_cycTIhyp)
    (isoG : CyclicTIIsometryData (k := ℂ) pd.prDade_cycTI)
    (hoddM : Odd (Nat.card M)) :
    ClassFunction M ℂ → Finset (ClassFunction G ℂ) :=
  Classical.choose (FTtypeP_coh_base_sig pd isoM isoG hoddM)

private theorem FTtypeP_coh_base_spec
    {G M K H W W₁ W₂ : Subgroup Gamma0}
    {A A₀ : Set Gamma0}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (pd : PrimeDadeHypothesis G M K H A A₀ W W₁ W₂ defW)
    (isoM : CyclicTIIsometryData (k := ℂ)
      pd.prDade_prTI.prime_cycTIhyp)
    (isoG : CyclicTIIsometryData (k := ℂ) pd.prDade_cycTI)
    (hoddM : Odd (Nat.card M)) :
    subcoherent (FTtypePKernelLayer pd) (Dade pd.prDade_hyp)
        (FTtypeP_coh_base pd isoM isoG hoddM) ∧
      (∀ phi ∈ FTtypePKernelLayer pd,
        IsIrreducibleCharacter M ℂ phi →
        ∀ w : IrreducibleCharacter W ℂ,
          ∀ alpha ∈ FTtypeP_coh_base pd isoM isoG hoddM phi,
            characterPairing alpha
              (isoG.linearMap (w : ClassFunction W ℂ)) = 0) ∧
      ∀ j : IrreducibleCharacter W₂ ℂ,
        FTtypeP_coh_base pd isoM isoG hoddM
            (pd.prDade_prTI.primeTIRed isoM j) =
          pd.primeDadeReducedImageFamily isoM isoG j :=
  Classical.choose_spec (FTtypeP_coh_base_sig pd isoM isoG hoddM)

/-- `PFsection8.v: FTtypeP_subcoherent`. -/
theorem FTtypeP_subcoherent
    {G M K H W W₁ W₂ : Subgroup Gamma0}
    {A A₀ : Set Gamma0}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (pd : PrimeDadeHypothesis G M K H A A₀ W W₁ W₂ defW)
    (isoM : CyclicTIIsometryData (k := ℂ)
      pd.prDade_prTI.prime_cycTIhyp)
    (isoG : CyclicTIIsometryData (k := ℂ) pd.prDade_cycTI)
    (hoddM : Odd (Nat.card M)) :
    subcoherent (FTtypePKernelLayer pd) (Dade pd.prDade_hyp)
      (FTtypeP_coh_base pd isoM isoG hoddM) :=
  (FTtypeP_coh_base_spec pd isoM isoG hoddM).1

/-- `PFsection8.v: FTtypeP_base_ortho`. -/
theorem FTtypeP_base_ortho
    {G M K H W W₁ W₂ : Subgroup Gamma0}
    {A A₀ : Set Gamma0}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (pd : PrimeDadeHypothesis G M K H A A₀ W W₁ W₂ defW)
    (isoM : CyclicTIIsometryData (k := ℂ)
      pd.prDade_prTI.prime_cycTIhyp)
    (isoG : CyclicTIIsometryData (k := ℂ) pd.prDade_cycTI)
    (hoddM : Odd (Nat.card M))
    {phi : ClassFunction M ℂ}
    (hphi : phi ∈ FTtypePKernelLayer pd)
    (hirr : IsIrreducibleCharacter M ℂ phi)
    (w : IrreducibleCharacter W ℂ)
    {alpha : ClassFunction G ℂ}
    (halpha : alpha ∈ FTtypeP_coh_base pd isoM isoG hoddM phi) :
    characterPairing alpha
      (isoG.linearMap (w : ClassFunction W ℂ)) = 0 :=
  (FTtypeP_coh_base_spec pd isoM isoG hoddM).2.1
    phi hphi hirr w alpha halpha

/-- `PFsection8.v: FTtypeP_base_TIred`. -/
theorem FTtypeP_base_TIred
    {G M K H W W₁ W₂ : Subgroup Gamma0}
    {A A₀ : Set Gamma0}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (pd : PrimeDadeHypothesis G M K H A A₀ W W₁ W₂ defW)
    (isoM : CyclicTIIsometryData (k := ℂ)
      pd.prDade_prTI.prime_cycTIhyp)
    (isoG : CyclicTIIsometryData (k := ℂ) pd.prDade_cycTI)
    (hoddM : Odd (Nat.card M))
    (j : IrreducibleCharacter W₂ ℂ) :
    FTtypeP_coh_base pd isoM isoG hoddM
        (pd.prDade_prTI.primeTIRed isoM j) =
      pd.primeDadeReducedImageFamily isoM isoG j :=
  (FTtypeP_coh_base_spec pd isoM isoG hoddM).2.2 j

/-! ## Coherent subfamilies -/

/-- `PFsection8.v: coherent_ortho_cycTIiso`. -/
theorem coherent_ortho_cycTIiso
    {G M K H W W₁ W₂ : Subgroup Gamma0}
    {A A₀ : Set Gamma0}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (pd : PrimeDadeHypothesis G M K H A A₀ W W₁ W₂ defW)
    (isoM : CyclicTIIsometryData (k := ℂ)
      pd.prDade_prTI.prime_cycTIhyp)
    (isoG : CyclicTIIsometryData (k := ℂ) pd.prDade_cycTI)
    (hoddM : Odd (Nat.card M))
    {S₁ : Set (ClassFunction M ℂ)}
    {tau₁ : ClassFunction M ℂ →ₗ[ℂ] ClassFunction G ℂ}
    (hS₁ : cfConjC_subset S₁ (FTtypePKernelLayer pd))
    (hcoh : coherent_with S₁ (nonidentitySet M)
      (Dade pd.prDade_hyp) tau₁)
    {phi : ClassFunction M ℂ}
    (hphi : phi ∈ S₁)
    (hirr : IsIrreducibleCharacter M ℂ phi)
    (w : IrreducibleCharacter W ℂ) :
    characterPairing (tau₁ phi)
      (isoG.linearMap (w : ClassFunction W ℂ)) = 0 := by
  obtain ⟨E, hER, hsum⟩ := mem_coherent_sum_subseq
    (FTtypeP_subcoherent pd isoM isoG hoddM) hS₁ hcoh hphi
  rw [hsum]
  rw [show characterPairing
      (∑ alpha ∈ E, alpha)
      (isoG.linearMap (w : ClassFunction W ℂ)) =
        ∑ alpha ∈ E, characterPairing alpha
          (isoG.linearMap (w : ClassFunction W ℂ)) from
    map_sum
      (characterPairingRight
        (isoG.linearMap (w : ClassFunction W ℂ)))
      (fun alpha ↦ alpha) E]
  apply Finset.sum_eq_zero
  intro alpha halpha
  exact FTtypeP_base_ortho pd isoM isoG hoddM
    (hS₁.1 hphi) hirr w (hER halpha)

/-- `PFsection8.v: FTtypeP_coherent_TIred`. -/
theorem FTtypeP_coherent_TIred
    {G M K H W W₁ W₂ : Subgroup Gamma0}
    {A A₀ : Set Gamma0}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (pd : PrimeDadeHypothesis G M K H A A₀ W W₁ W₂ defW)
    (isoM : CyclicTIIsometryData (k := ℂ)
      pd.prDade_prTI.prime_cycTIhyp)
    (isoG : CyclicTIIsometryData (k := ℂ) pd.prDade_cycTI)
    (hoddM : Odd (Nat.card M))
    (S₁ : Set (ClassFunction M ℂ))
    (tau₁ : ClassFunction M ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (zeta : IrreducibleCharacter M ℂ)
    (j : IrreducibleCharacter W₂ ℂ)
    (hS₁ : cfConjC_subset S₁ (FTtypePKernelLayer pd))
    (hcoh : coherent_with S₁ (nonidentitySet M)
      (Dade pd.prDade_hyp) tau₁)
    (hzeta : (zeta : ClassFunction M ℂ) ∈ S₁)
    (hmu : pd.prDade_prTI.primeTIRed isoM j ∈ S₁) :
    let k := IrreducibleCharacter.dual j
    tau₁ (pd.prDade_prTI.primeTIRed isoM j) =
        (pd.prDade_prTI.primeTISign isoM j : ℂ) •
          ∑ i : IrreducibleCharacter W₁ ℂ,
            isoG.cyclicTIImage (i, j) ∨
      tau₁ (pd.prDade_prTI.primeTIRed isoM j) =
          (-(pd.prDade_prTI.primeTISign isoM j : ℂ)) •
            ∑ i : IrreducibleCharacter W₁ ℂ,
              isoG.cyclicTIImage (i, k) ∧
        ∀ ell : IrreducibleCharacter W₂ ℂ,
          pd.prDade_prTI.primeTIRed isoM ell ∈ S₁ →
          pd.prDade_prTI.primeTIRed isoM ell 1 =
            pd.prDade_prTI.primeTIRed isoM j 1 →
          ell = j ∨ ell = k := by
  have hnonreal : ∀ phi ∈ S₁,
      ClassFunction.inverseLinear phi ≠ phi := by
    intro phi hphi
    exact kernelLayer_nonreal8 pd hoddM phi (hS₁.1 hphi)
  exact pd.coherent_prDade_TIred isoM isoG S₁ j tau₁
    hS₁ hnonreal ⟨zeta, hzeta⟩ hmu hcoh

end Coherence

/-! ## Reducible normally induced characters -/

section Counting

variable {Gamma0 : Type} [Group Gamma0] [Fintype Gamma0]

/-- `PFsection8.v: size_red_subseq_seqInd_typeP`. -/
theorem size_red_subseq_seqInd_typeP
    [IsMinSimpleOddGroup Gamma0]
    {M U W W₁ W₂ : Subgroup Gamma0}
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (calX : Finset
      (IrreducibleCharacter ((derivedWithin M).subgroupOf M) ℂ))
    (calS₁ : Finset (ClassFunction M ℂ))
    (hsub : calS₁ ⊆ seqInd ((derivedWithin M).subgroupOf M) calX)
    (hreducible : ∀ phi ∈ calS₁,
      ¬ IsIrreducibleCharacter M ℂ phi) :
    calS₁.card =
      (Finset.univ.filter fun chi : IrreducibleCharacter
          ((derivedWithin M).subgroupOf M) ℂ ↦
        ClassFunction.induce ((derivedWithin M).subgroupOf M)
          (chi : ClassFunction ((derivedWithin M).subgroupOf M) ℂ) ∈
            calS₁).card := by
  let K : Subgroup M := (derivedWithin M).subgroupOf M
  let pti : PrimeTIHypothesis M (derivedWithin M) W W₁ W₂ defW :=
    FT_primeTI_hyp defW MtypeP
  let iso := pti.prime_cycTIhyp.cyclicTIIsometryData (k := ℂ)
  let induceIrr := fun chi : IrreducibleCharacter K ℂ ↦
    ClassFunction.induce K (chi : ClassFunction K ℂ)
  let recover := fun phi : ClassFunction M ℂ ↦
    (Nat.card W₁ : ℂ)⁻¹ • ClassFunction.restrict K phi
  let selected := Finset.univ.filter fun chi : IrreducibleCharacter K ℂ ↦
    induceIrr chi ∈ calS₁
  have recover_induce (chi : IrreducibleCharacter K ℂ)
      (hchi : induceIrr chi ∈ calS₁) :
      recover (induceIrr chi) = (chi : ClassFunction K ℂ) := by
    rcases pti.prTIres_irr_cases iso chi with ⟨j, hj⟩ | ⟨hirr, _⟩
    · rw [hj]
      change (Nat.card W₁ : ℂ)⁻¹ •
          ClassFunction.restrict K
            (ClassFunction.induce K
              (pti.primeTI_Ires iso j : ClassFunction K ℂ)) =
        (pti.primeTI_Ires iso j : ClassFunction K ℂ)
      rw [show ClassFunction.induce K
          (pti.primeTI_Ires iso j : ClassFunction K ℂ) =
            pti.primeTIRed iso j by
        simpa only [K] using pti.cfInd_prTIres iso j]
      rw [show ClassFunction.restrict K (pti.primeTIRed iso j) =
          (Nat.card W₁ : ℂ) •
            (pti.primeTI_Ires iso j : ClassFunction K ℂ) by
        simpa only [K] using pti.cfRes_prTIred iso j]
      rw [smul_smul]
      simp [Nat.cast_ne_zero.mpr Nat.card_pos.ne']
    · exact (hreducible (induceIrr chi) hchi hirr).elim
  have hinjective : Set.InjOn induceIrr
      {chi | induceIrr chi ∈ calS₁} := by
    intro chi hchi psi hpsi heq
    apply Subtype.ext
    calc
      (chi : ClassFunction K ℂ) = recover (induceIrr chi) :=
        (recover_induce chi hchi).symm
      _ = recover (induceIrr psi) := congrArg recover heq
      _ = (psi : ClassFunction K ℂ) := recover_induce psi hpsi
  have himage : selected.image induceIrr = calS₁ := by
    ext phi
    constructor
    · intro hphi
      obtain ⟨chi, hchi, rfl⟩ := Finset.mem_image.mp hphi
      exact (Finset.mem_filter.mp hchi).2
    · intro hphi
      obtain ⟨chi, _, hchi⟩ := seqIndP.mp (hsub hphi)
      apply Finset.mem_image.mpr
      refine ⟨chi, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · simpa [induceIrr, hchi] using hphi
      · simpa [induceIrr] using hchi.symm
  have hinjectiveSelected : Set.InjOn induceIrr
      (↑selected : Set (IrreducibleCharacter K ℂ)) := by
    intro chi hchi psi hpsi heq
    apply hinjective
    · exact (Finset.mem_filter.mp hchi).2
    · exact (Finset.mem_filter.mp hpsi).2
    · exact heq
  calc
    calS₁.card = (selected.image induceIrr).card := by rw [himage]
    _ = selected.card := Finset.card_image_iff.mpr hinjectiveSelected
    _ = _ := by simp only [selected, K, induceIrr]

end Counting

/-! ## Type-II normalized-TI supports -/

private theorem normalizedTI_mono8
    {A A₀ : Set Gamma} {D L : Subgroup Gamma}
    (hA₀ : IsNormalizedTI A₀ D L)
    (hne : A.Nonempty) (hsub : A ⊆ A₀)
    (hnorm : L ≤ Subgroup.normalizer A) :
    IsNormalizedTI A D L := by
  refine ⟨hne, ?_, ?_⟩
  · intro x hx
    exact ⟨(hA₀.2.1 hx).1, hnorm hx⟩
  · intro g hg hoverlap
    apply hA₀.2.2 hg
    rcases hoverlap with ⟨x, hx, y, hy, hxy⟩
    exact ⟨x, hsub hx, y, hsub hy, hxy⟩

/-- `PFsection8.v: FTtypeII_ker_TI`, Peterfalvi (8.16). -/
theorem FTtypeII_ker_TI
    [IsMinSimpleOddGroup Gamma]
    (M : Subgroup Gamma)
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (htypeM : FTtype M = 2) :
    IsNormalizedTI (FTsupport0 M) ⊤ M ∧
      IsNormalizedTI (FTsupport M) ⊤ M ∧
      IsNormalizedTI (FTsupport1 M) ⊤ M := by
  obtain ⟨U, W, W₁, W₂, defW, hTypeII⟩ :=
    (FTtypeP 2 M hmaxM).mpr htypeM
  have hFittingTI :
      IsNormalizedTI (subgroupNonidentity (fittingWithin M)) ⊤ M :=
    hTypeII.1.2.2.2
  have hsignal : ∀ ⦃a : Gamma⦄, a ∈ FTsupport0 M →
      DadeSignalizer (FT_Dade0_hyp M hmaxM) a = ⊥ := by
    intro a ha
    rw [def_FTsignalizer0 M hmaxM ha]
    unfold FTsignalizer
    by_cases hcent : centralizerOfElement8 a ≤ M
    · rw [if_pos hcent]
    · have haSupport1 : a ∈ FTsupport1 M :=
        (FTsupport_facts M hmaxM).exceptional_subset_support1 ⟨ha, hcent⟩
      have haFcore : a ∈ subgroupNonidentity (Fitting_core M) := by
        rw [← FTsupp1_type2 M htypeM]
        exact haSupport1
      have haFitting : a ∈ subgroupNonidentity (fittingWithin M) :=
        ⟨Fcore_sub_Fitting M haFcore.1, haFcore.2⟩
      have hcentralizer : centralizerOfElement8 a ≤ M := by
        intro z hz
        apply hFittingTI.centralizerWithin_zpowers_le haFitting
        exact ⟨Subgroup.mem_top z, Subgroup.mem_centralizer_iff.mp hz⟩
      exact (hcent hcentralizer).elim
  have hne0 : (FTsupport0 M).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact FTsupp0_neq0 hmaxM
  have hTI0 : IsNormalizedTI (FTsupport0 M) ⊤ M :=
    (Dade_normedTI_P (FT_Dade0_hyp M hmaxM)).2 ⟨hne0, hsignal⟩
  have hsub10 : FTsupport1 M ⊆ FTsupport M := FTsupp1_sub hmaxM
  have hsub00 : FTsupport M ⊆ FTsupport0 M := FTsupp_sub0 M
  have hne1 : (FTsupport1 M).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact FTsupp1_neq0 hmaxM
  have hne : (FTsupport M).Nonempty := hne1.mono hsub10
  have hTI : IsNormalizedTI (FTsupport M) ⊤ M :=
    normalizedTI_mono8 hTI0 hne hsub00 (FTsupp_norm M)
  have hTI1 : IsNormalizedTI (FTsupport1 M) ⊤ M :=
    normalizedTI_mono8 hTI0 hne1 (hsub10.trans hsub00)
      (FTsupp1_norm M)
  exact ⟨hTI0, hTI, hTI1⟩

end

end Submission.OddOrder.PF
