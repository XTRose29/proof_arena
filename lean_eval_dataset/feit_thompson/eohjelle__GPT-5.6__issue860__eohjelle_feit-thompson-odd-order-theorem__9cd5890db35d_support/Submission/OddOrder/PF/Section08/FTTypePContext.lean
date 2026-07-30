import Submission.OddOrder.BG.Section16.TypeSpecAndFinalSummary
import Submission.OddOrder.PF.Section08.FTTypeFContext

/-!
# Peterfalvi Section 8: the type-P context

This module develops the type-P consequences of the Bender--Glauberman
classification.  It packages the exceptional pair, proves the incompatibility
of types P and F, transports type-P witnesses under conjugation, and constructs
the canonical contexts used by the later support and coherence phases.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.BG.Section12
open Submission.OddOrder.BG.Section14
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open FTContextInternal
open scoped BigOperators Classical Pointwise IsMulCommutative

universe u

variable {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]

/-- Monotonicity of the ambient derived subgroup. -/
private theorem derivedWithin_mono8 {A B : Subgroup G} (hAB : A ≤ B) :
    derivedWithin A ≤ derivedWithin B := by
  rw [derivedWithin, A.map_subtype_commutator,
    derivedWithin, B.map_subtype_commutator]
  exact Subgroup.commutator_mono hAB hAB

/-- A nontrivial subgroup contains a nonidentity ambient element. -/
private theorem exists_mem_ne_one8 {H : Subgroup G} (hH : H ≠ ⊥) :
    ∃ x : G, x ∈ H ∧ x ≠ 1 := by
  by_contra h
  push Not at h
  apply hH
  ext x
  constructor
  · intro hx
    exact Subgroup.mem_bot.mpr (h x hx)
  · intro hx
    simpa [Subgroup.mem_bot.mp hx] using H.one_mem

@[simp]
private theorem conjugateSubgroup8_one (H : Subgroup G) :
    conjugateSubgroup8 H 1 = H := by
  unfold conjugateSubgroup8
  convert H.map_id using 1
  ext x
  simp

/-! ## The exceptional type-P interface -/

/-- The exceptional alternative in Peterfalvi (8.8)(b), with each source
conjunct exposed as a named field. -/
structure TypePPair
    (S T W W₁ W₂ : Subgroup G)
    (defW : IsInternalDirectProductIn W₁ W₂ W) : Prop where
  cyclic_ti : CyclicTIHypothesis (⊤ : Subgroup G) W W₁ W₂ defW
  S_maximal : S ∈ minSimple_max_groups (G := G)
  T_maximal : T ∈ minSimple_max_groups (G := G)
  S_decomposition :
    IsInternalSemidirectProductIn (derivedWithin S) W₁ S
  T_decomposition :
    IsInternalSemidirectProductIn (derivedWithin T) W₂ T
  intersection_eq : S ⊓ T = W
  one_type_two : FTtype S = 2 ∨ FTtype T = 2
  S_type_range : 1 < FTtype S ∧ FTtype S ≤ 5
  T_type_range : 1 < FTtype T ∧ FTtype T ≤ 5
  controls_non_type_one : ∀ M : Subgroup G,
    M ∈ minSimple_max_groups (G := G) → FTtype M ≠ 1 →
      AreConjugateSubgroups S M ∨ AreConjugateSubgroups T M

/-- Exact source spelling of the exceptional type-P proposition. -/
abbrev typeP_pair
    (S T W W₁ W₂ : Subgroup G)
    (defW : IsInternalDirectProductIn W₁ W₂ W) : Prop :=
  TypePPair S T W W₁ W₂ defW

/-! ## Elementary type-P consequences -/

/-- A type-P maximal subgroup is solvable. -/
theorem of_typeP_sol (M U W W₁ W₂ : Subgroup G)
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (hP : of_typeP M U W W₁ W₂ defW) :
    IsSolvable M := by
  have hFne : Fitting_core M ≠ ⊥ := by
    intro hF
    exact hP.2.2.1.1 (hF ▸ inferInstance)
  have hFproper : Fitting_core M < ⊤ :=
    (mFT_sol_proper (Fitting_core M)).2 inferInstance
  have hNproper :
      Subgroup.normalizer (Fitting_core M : Set G) < ⊤ :=
    mFT_norm_proper (Fitting_core M) hFne hFproper
  have hMle : M ≤ Subgroup.normalizer (Fitting_core M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Fcore_sub M)).1
      (Fcore_normal M)
  exact mFT_sol (hMle.trans_lt hNproper)

/-- In a type-P decomposition, the second cyclic factor is the centralizer
of the first factor in the derived subgroup. -/
theorem typeP_cent_compl (M U W W₁ W₂ : Subgroup G)
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (hP : of_typeP M U W W₁ W₂ defW) :
    centralizerWithin (derivedWithin M) W₁ = W₂ := by
  obtain ⟨w₁, _, _, partner, _⟩ := hP
  obtain ⟨x, hx⟩ := W₁.isCyclic_iff_exists_zpowers_eq_top.mp w₁.1
  have hxW₁ : x ∈ W₁ := by
    rw [← hx]
    exact Subgroup.mem_zpowers x
  have hxne : x ≠ 1 := by
    intro h
    apply w₁.2.2.1
    rw [← hx, h, Subgroup.zpowers_one_eq_bot]
  calc
    centralizerWithin (derivedWithin M) W₁ =
        elementCentralizerWithin (derivedWithin M) x := by rw [← hx]
    _ = W₂ := partner.2.2.2.2 x ⟨hxW₁, hxne⟩

/-- The same centralizer can be computed inside the Fitting core. -/
theorem typeP_cent_core_compl (M U W W₁ W₂ : Subgroup G)
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (hP : of_typeP M U W W₁ W₂ defW) :
    centralizerWithin (Fitting_core M) W₁ = W₂ := by
  have hDerived := typeP_cent_compl M U W W₁ W₂ defW hP
  have hFle : Fitting_core M ≤ derivedWithin M :=
    (Fcore_sub_Fitting M).trans hP.2.2.1.2.2.2
  apply le_antisymm
  · exact (centralizerWithin_mono_left hFle).trans_eq hDerived
  · intro x hx
    refine ⟨hP.2.2.2.1.2.2.1 hx, ?_⟩
    have hx' : x ∈ centralizerWithin (derivedWithin M) W₁ := by
      rw [hDerived]
      exact hx
    exact hx'.2

/-- Type P and type F are mutually exclusive. -/
theorem typePF_exclusion
    (M U W W₁ W₂ K : Subgroup G)
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (hP : of_typeP M U W W₁ W₂ defW) :
    ¬ of_typeF M K := by
  intro hF
  let F := Fitting_core M
  let D := derivedWithin M
  obtain ⟨K₀, hK₀K, hExp, _, hFrob⟩ := hF.2.2.2.2
  obtain ⟨p, hp, hpW₁⟩ := Nat.exists_prime_and_dvd
    (W₁.one_lt_card_iff_ne_bot.mpr hP.1.2.2.1).ne'
  letI : Fact p.Prime := ⟨hp⟩
  have hCardF : Nat.card M = Nat.card F * Nat.card K := by
    calc
      Nat.card M =
          Nat.card ((Fitting_core M).subgroupOf M) *
            Nat.card (K.subgroupOf M) := hF.2.2.1.2.2.2.card_mul.symm
      _ = Nat.card F * Nat.card K := by
        rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
              hF.2.2.1.1,
          Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
              hF.2.2.1.2.1]
  have hCardD : Nat.card M = Nat.card D * Nat.card W₁ := by
    simpa [D,
      Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
        hP.1.2.2.2.1,
      Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
        hP.1.2.1.1] using
      hP.1.2.2.2.2.2.2.card_mul.symm
  have hCardU : Nat.card D = Nat.card F * Nat.card U := by
    simpa [F, D,
      Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
        hP.2.1.2.2.2.1,
      Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
        hP.2.1.2.1] using
      hP.2.1.2.2.2.2.2.2.card_mul.symm
  have hCardK : Nat.card K = Nat.card U * Nat.card W₁ := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := F))
    calc
      Nat.card F * Nat.card K = Nat.card M := hCardF.symm
      _ = Nat.card D * Nat.card W₁ := hCardD
      _ = (Nat.card F * Nat.card U) * Nat.card W₁ := by rw [hCardU]
      _ = Nat.card F * (Nat.card U * Nat.card W₁) := by
        rw [mul_assoc]
  have hpK : p ∣ Nat.card K := by
    rw [hCardK]
    exact dvd_mul_of_dvd_right hpW₁ _
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := K) p hpK
  have hpExp : p ∣ Monoid.exponent K := by
    rw [← hk]
    exact Monoid.order_dvd_exponent k
  have hpK₀ : p ∣ Nat.card K₀ :=
    (hExp ▸ hpExp).trans Group.exponent_dvd_nat_card
  obtain ⟨X, hXK₀, hXline⟩ :=
    TypeSpecInternal.exists_rankOneLineIn_of_primeSupport16
      (show p ∈ primeSupport (Nat.card K₀) from ⟨hp, hpK₀⟩)
  have hXM : X ≤ M := hXK₀.trans hK₀K |>.trans hF.2.2.1.2.1
  let pi := primeSupport (Nat.card W₁)
  have hXpi : IsPiNumber pi (Nat.card X) := by
    simpa [pi, hXline.card_eq] using
      (show IsPiNumber (primeSupport (Nat.card W₁)) p from
        fun q hq hqp ↦ by
          have hqpEq : q = p :=
            (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
          simpa [hqpEq] using
            (show p ∈ primeSupport (Nat.card W₁) from ⟨hp, hpW₁⟩))
  obtain ⟨a, hXW₁a, _, _, _, _, _⟩ :=
    exists_ambient_isHall_map_conj_ge_of_isSolvable
      hXM hP.1.2.1.1 (of_typeP_sol M U W W₁ W₂ defW hP)
        hXpi hP.1.2.1.2
  have hCentX : centralizerWithin F X = ⊥ := by
    apply le_bot_iff.mp
    intro z hz
    apply Subgroup.mem_bot.mpr
    have hXne : X ≠ ⊥ := hXline.ne_bot
    have hExists : ∃ x : G, x ∈ X ∧ x ≠ 1 := by
      by_contra h
      push_neg at h
      apply hXne
      ext x
      constructor
      · intro hx
        exact Subgroup.mem_bot.mpr (h x hx)
      · intro hx
        simpa [Subgroup.mem_bot.mp hx] using X.one_mem
    obtain ⟨x, hxX, hxne⟩ := hExists
    let xK₀ : K₀.subgroupOf (F ⊔ K₀) :=
      ⟨⟨x, (show K₀ ≤ F ⊔ K₀ from le_sup_right) (hXK₀ hxX)⟩,
        hXK₀ hxX⟩
    let zF : F.subgroupOf (F ⊔ K₀) :=
      ⟨⟨z, (show F ≤ F ⊔ K₀ from le_sup_left) hz.1⟩, hz.1⟩
    have hxK₀ne : xK₀ ≠ 1 := by
      intro h
      exact hxne (congrArg
        (fun y : K₀.subgroupOf (F ⊔ K₀) ↦ ((y : ↑(F ⊔ K₀)) : G)) h)
    have hfix : (xK₀ : ↑(F ⊔ K₀)) * (zF : ↑(F ⊔ K₀)) * xK₀⁻¹ = zF := by
      apply Subtype.ext
      change x * z * x⁻¹ = z
      rw [hz.2 x hxX]
      simp
    have hzOne := hFrob.fixedPointFree xK₀ hxK₀ne zF hfix
    exact congrArg (fun y : F.subgroupOf (F ⊔ K₀) ↦
      ((y : ↑(F ⊔ K₀)) : G)) hzOne
  let e : G ≃* G := MulAut.conj (a : G)
  have hFfix : F.map e.toMonoidHom = F := by
    exact conjugateSubgroup8_eq_self_of_mem_normalizer
      (((Subgroup.normal_subgroupOf_iff_le_normalizer (Fcore_sub M)).1
        (Fcore_normal M)) a.property)
  have hCentMap :
      centralizerWithin F (W₁.map e.toMonoidHom) =
        W₂.map e.toMonoidHom := by
    have hmap := congrArg (fun H : Subgroup G ↦ H.map e.toMonoidHom)
      (typeP_cent_core_compl M U W W₁ W₂ defW hP)
    rw [centralizerWithin_map_mulEquiv_type8, hFfix] at hmap
    exact hmap
  have hW₂ne : W₂.map e.toMonoidHom ≠ ⊥ :=
    (not_congr (Subgroup.map_eq_bot_iff_of_injective W₂ e.injective)).mpr
      hP.2.2.2.1.2.1
  apply hW₂ne
  apply le_bot_iff.mp
  rw [← hCentMap, ← hCentX]
  exact centralizerWithin_antitone_right hXW₁a

/-! ## Conjugacy and the local type-P context -/

/-- Every complement to the derived subgroup is conjugate, inside `M`, to
the complement belonging to a type-P witness. -/
theorem of_typeP_compl_conj (M U W W₁ W₂ : Subgroup G)
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (hP : of_typeP M U W W₁ W₂ defW)
    (W₁' : Subgroup G)
    (hW₁' : IsInternalSemidirectProductIn (derivedWithin M) W₁' M) :
    IsConjugateWithin8 M W₁ W₁' := by
  let pi := primeSupport (Nat.card W₁)
  let A : Subgroup M := W₁.subgroupOf M
  let B : Subgroup M := W₁'.subgroupOf M
  let D : Subgroup M := (derivedWithin M).subgroupOf M
  have hHallA : IsHall pi A := hP.1.2.1.2
  have hcard : Nat.card B = Nat.card A := by
    calc
      Nat.card B = D.index := hW₁'.2.2.2.symm.index_eq_card.symm
      _ = Nat.card A := hP.1.2.2.2.2.2.2.symm.index_eq_card
  have hindex : B.index = A.index := by
    calc
      B.index = Nat.card D := hW₁'.2.2.2.index_eq_card
      _ = A.index := hP.1.2.2.2.2.2.2.index_eq_card.symm
  have hHallB : IsHall pi B := by
    constructor
    · simpa [hcard] using hHallA.isPiNumber_card
    · simpa [hindex] using hHallA.isPiNumber_index
  obtain ⟨x, hx⟩ := exists_map_conj_eq_of_isHall_of_isSolvable
    (of_typeP_sol M U W W₁ W₂ defW hP) hHallA hHallB
  refine ⟨(x : G), x.property, ?_⟩
  exact ambient_conjugate_eq_of_subgroupOf8
    hP.1.2.1.1 hW₁'.2.1 x hx

/-- Conjugation by an ambient element preserves the type-P predicate. -/
theorem conj_of_typeP (M U W W₁ W₂ : Subgroup G)
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (hP : of_typeP M U W W₁ W₂ defW) (x : G) :
    ∃ defWx : IsInternalDirectProductIn
        (conjugateSubgroup8 W₁ x) (conjugateSubgroup8 W₂ x)
        (conjugateSubgroup8 W x),
      of_typeP (conjugateSubgroup8 M x) (conjugateSubgroup8 U x)
        (conjugateSubgroup8 W x) (conjugateSubgroup8 W₁ x)
        (conjugateSubgroup8 W₂ x) defWx := by
  unfold conjugateSubgroup8
  let e : G ≃* G := MulAut.conj x
  change ∃ defWx : IsInternalDirectProductIn
      (W₁.map e.toMonoidHom) (W₂.map e.toMonoidHom)
      (W.map e.toMonoidHom),
    of_typeP (M.map e.toMonoidHom) (U.map e.toMonoidHom)
      (W.map e.toMonoidHom) (W₁.map e.toMonoidHom)
      (W₂.map e.toMonoidHom) defWx
  let defWx := directProduct_map_mulEquiv8 defW e
  refine ⟨defWx, ?_⟩
  obtain ⟨hW₁, hU, hCore, hW₂, hTI⟩ := hP
  have hDer := derivedWithin_map_mulEquiv_type8 M e
  have hDer₂ := secondDerivedWithin_map_mulEquiv8 M e
  have hF := Fitting_core_map_mulEquiv M e
  have hFit := fittingWithin_map_mulEquiv8 M e
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨(e.subgroupMap W₁).isCyclic.mp hW₁.1, ?_, ?_, ?_⟩
    · refine ⟨Subgroup.map_mono hW₁.2.1.1, ?_⟩
      have hHall := isHall_map_mulEquiv8 (e.subgroupMap M) hW₁.2.1.2
      have hsub := subgroupOf_map_mulEquiv8 hW₁.2.1.1 e
      rw [hsub] at hHall
      rw [show Nat.card (W₁.map e.toMonoidHom) = Nat.card W₁ from
        Subgroup.card_map_of_injective e.injective]
      exact hHall
    · exact (not_congr
        (Subgroup.map_eq_bot_iff_of_injective W₁ e.injective)).mpr hW₁.2.2.1
    · simpa only [hDer] using semidirect_map_mulEquiv8 hW₁.2.2.2 e
  · refine ⟨?_, ?_, ?_, ?_⟩
    · letI : Group.IsNilpotent U := hU.1
      exact Group.nilpotent_of_mulEquiv (e.subgroupMap U)
    · simpa only [hDer] using Subgroup.map_mono hU.2.1
    · rw [← Subgroup.map_equiv_normalizer_eq U e]
      exact Subgroup.map_mono hU.2.2.1
    · simpa only [hF, hDer] using semidirect_map_mulEquiv8 hU.2.2.2 e
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hF]
      intro hcyclic
      exact hCore.1 ((e.subgroupMap (Fitting_core M)).isCyclic.mpr hcyclic)
    · simpa only [hDer₂, hFit] using Subgroup.map_mono hCore.2.1
    · rw [hF, hFit, ← centralizerWithin_map_mulEquiv_type8]
      simpa only [Subgroup.map_sup] using
        congrArg (fun H : Subgroup G ↦ H.map e.toMonoidHom) hCore.2.2.1
    · simpa only [hFit, hDer] using Subgroup.map_mono hCore.2.2.2
  · refine ⟨(e.subgroupMap W₂).isCyclic.mp hW₂.1, ?_, ?_, ?_, ?_⟩
    · exact (not_congr
        (Subgroup.map_eq_bot_iff_of_injective W₂ e.injective)).mpr hW₂.2.1
    · simpa only [hF] using Subgroup.map_mono hW₂.2.2.1
    · simpa only [hDer₂] using Subgroup.map_mono hW₂.2.2.2.1
    · intro y hy
      let y₀ : G := e.symm y
      have hyW₁ : y₀ ∈ W₁ := Subgroup.mem_map_equiv.mp hy.1
      have hyne : y₀ ≠ 1 := by
        intro h
        apply hy.2
        simpa [y₀] using congrArg e h
      have hmap := congrArg
        (fun H : Subgroup G ↦ H.map e.toMonoidHom)
        (hW₂.2.2.2.2 y₀ ⟨hyW₁, hyne⟩)
      rw [hDer]
      simpa only [elementCentralizerWithin_map_mulEquiv8, y₀,
        e.apply_symm_apply] using hmap
  · change IsNormalizedTI (cyclicTISet W W₁ W₂) ⊤ W at hTI
    have hmap := isNormalizedTI_map_mulEquiv8 hTI e
    change IsNormalizedTI
      (cyclicTISet (W.map e.toMonoidHom) (W₁.map e.toMonoidHom)
        (W₂.map e.toMonoidHom)) ⊤ (W.map e.toMonoidHom)
    rw [cyclicTISet_map_mulEquiv8 W W₁ W₂ e]
    simpa using hmap

/-- Peterfalvi (8.5): the Fitting decomposition, centralizer control, and
cyclic-TI conclusions extracted from a type-P witness. -/
theorem typeP_context
    (M U W W₁ W₂ : Subgroup G)
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (hP : of_typeP M U W W₁ W₂ defW) :
    TypePContext M U W W₁ W₂ defW := by
  let F := Fitting_core M
  let D := derivedWithin M
  let Fit := fittingWithin M
  let C := centralizerWithin U F
  let UF := U ⊓ Fit
  let hOuter := hP.1.2.2.2
  let hInner := hP.2.1.2.2.2
  let hCore := hP.2.2.1
  let hPartner := hP.2.2.2.1
  have hFleD : F ≤ D := hInner.1
  have hUleD : U ≤ D := hInner.2.1
  have hDleM : D ≤ M := hOuter.1
  have hFitD : Fit ≤ D := hCore.2.2.2
  have hFleFit : F ≤ Fit := Fcore_sub_Fitting M
  have hFitM : Fit ≤ M := hFitD.trans hDleM
  let pi := primeSupport (Nat.card F)
  have hHallFD : IsHall pi (F.subgroupOf D) :=
    isHall_subgroupOf_of_le8 hFleD hDleM (Fcore_Hall M)
  have hUpi : IsPiNumber piᶜ (Nat.card U) := by
    have hIndex : (F.subgroupOf D).index = Nat.card U := by
      calc
        (F.subgroupOf D).index = Nat.card (U.subgroupOf D) :=
          hInner.2.2.2.symm.index_eq_card
        _ = Nat.card U :=
          Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hUleD
    have h := hHallFD.isPiNumber_index
    rw [hIndex] at h
    exact h
  let FF : Subgroup Fit := F.subgroupOf Fit
  let UFF : Subgroup Fit := UF.subgroupOf Fit
  have hFFpi : IsPiNumber pi (Nat.card FF) := by
    rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hFleFit]
    exact IsPiNumber.primeSupport_self
  have hUFFpi : IsPiNumber piᶜ (Nat.card UFF) := by
    rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
      (show UF ≤ Fit from inf_le_right)]
    exact hUpi.of_dvd (Subgroup.card_dvd_of_le inf_le_left)
  letI : Group.IsNilpotent Fit := fittingWithin_isNilpotent M
  have hComm : FF ≤ Subgroup.centralizer (UFF : Set Fit) :=
    nilpotent_subgroups_commute_of_coprime_pi8 hFFpi hUFFpi
  have hUFleC : UF ≤ C := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    intro f hf
    let fFit : Fit := ⟨f, hFleFit hf⟩
    let xFit : Fit := ⟨x, hx.2⟩
    have hfCent : fFit ∈ Subgroup.centralizer (UFF : Set Fit) :=
      hComm (show fFit ∈ FF from hf)
    have hfx := Subgroup.mem_centralizer_iff.mp hfCent xFit hx
    exact congrArg Subtype.val hfx.symm
  have hCleUF : C ≤ UF := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    have hxM : x ∈ M := hDleM (hUleD hx.1)
    have hxCent : x ∈ centralizerWithin M F := ⟨hxM, hx.2⟩
    change x ∈ fittingWithin M
    rw [← hCore.2.2.1]
    exact (show centralizerWithin M F ≤
      F ⊔ centralizerWithin M F from le_sup_right) hxCent
  have hUF : UF = C := le_antisymm hUFleC hCleUF
  have hSupFUF : F ⊔ UF = Fit := by
    apply le_antisymm (sup_le hFleFit inf_le_right)
    intro z hz
    let zD : D := ⟨z, hFitD hz⟩
    obtain ⟨⟨f, u⟩, hfu⟩ := hInner.2.2.2.2 zD
    have hfuG : (f : G) * (u : G) = z := congrArg (fun y : D ↦ (y : G)) hfu
    have hfFit : (f : G) ∈ Fit := hFleFit f.property
    have huFit : (u : G) ∈ Fit := by
      have hu : (u : G) = (f : G)⁻¹ * z := by
        rw [← hfuG]
        simp
      rw [hu]
      exact Fit.mul_mem (Fit.inv_mem hfFit) hz
    rw [← hfuG]
    exact Subgroup.mul_mem_sup f.property ⟨u.property, huFit⟩
  have hSupFC : F ⊔ C = Fit := by simpa [← hUF] using hSupFUF
  have hDisFU : Disjoint F U :=
    ambient_disjoint_of_subgroupOf8 hFleD hUleD
      hInner.2.2.2.disjoint
  have hDisFC : Disjoint F C :=
    Disjoint.mono le_rfl (centralizerWithin_le_left U F) hDisFU
  have hCleFit : C ≤ Fit := hCleUF.trans inf_le_right
  have hDisSub : Disjoint (F.subgroupOf Fit) (C.subgroupOf Fit) := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro x hx
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    apply Subgroup.mem_bot.mp
    rw [← disjoint_iff.mp hDisFC]
    exact hx
  have hSupSub : F.subgroupOf Fit ⊔ C.subgroupOf Fit = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hFleFit hCleFit, hSupFC]
    exact Subgroup.subgroupOf_self Fit
  letI : (F.subgroupOf Fit).Normal :=
    TypeSpecInternal.normal_restrict16 (Fcore_normal M) hFleFit hFitM
  have hComp : (F.subgroupOf Fit).IsComplement' (C.subgroupOf Fit) := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hDisSub
    rw [← Subgroup.normal_mul, hSupSub]
    rfl
  have hDirect : IsInternalDirectProductIn F C Fit :=
    { left_le := hFleFit
      right_le := hCleFit
      complement := hComp
      commute := by
        intro f c
        exact c.property.2 f f.property }
  have hDerULeFit : derivedWithin U ≤ Fit := by
    apply (derivedWithin_mono8 hUleD).trans
    simpa only [D, secondDerivedWithin] using hCore.2.1
  have hDerULeC : derivedWithin U ≤ C := by
    rw [← hUF]
    have hDerULeU : derivedWithin U ≤ U := by
      unfold derivedWithin
      exact Subgroup.map_subtype_le _
    exact le_inf hDerULeU hDerULeFit
  have hDerCent :
      derivedWithin U ≤ Subgroup.centralizer (F : Set G) := by
    intro x hx
    exact (hDerULeC hx).2
  have hNotCent : U ≠ ⊥ →
      ¬ U ≤ Subgroup.centralizer (F : Set G) := by
    intro hUne hUcent
    let hDir : IsInternalDirectProductIn F U D :=
      { left_le := hFleD
        right_le := hUleD
        complement := hInner.2.2.2
        commute := by
          intro f u
          exact (Subgroup.mem_centralizer_iff.mp
            (hUcent u.property) f f.property) }
    have hDnil : Group.IsNilpotent D := by
      letI : Group.IsNilpotent F := Fcore_nil M
      letI : Group.IsNilpotent U := hP.2.1.1
      exact Group.nilpotent_of_mulEquiv hDir.mulEquiv
    let DM : Subgroup M := D.subgroupOf M
    have hCoprime : Nat.Coprime (Nat.card W₁) (Nat.card D) := by
      have h := hP.1.2.1.2.coprime_card_index
      rw [hOuter.2.2.2.index_eq_card,
        Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
          hP.1.2.1.1,
        Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hDleM] at h
      exact h
    have hHallCoprime : (Nat.card DM).Coprime DM.index := by
      change (Nat.card (D.subgroupOf M)).Coprime (D.subgroupOf M).index
      rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hDleM,
        hOuter.2.2.2.symm.index_eq_card,
        Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
          hP.1.2.1.1]
      exact hCoprime.symm
    have hDleF : D ≤ F :=
      Fcore_max (isHall_primeSupport DM hHallCoprime) hDleM
        hOuter.2.2.1 hDnil
    have hUleF : U ≤ F := hUleD.trans hDleF
    exact hUne (disjoint_self.mp (Disjoint.mono hUleF le_rfl hDisFU))
  have hCoprime : Nat.Coprime (Nat.card W₁) (Nat.card D) := by
    have h := hP.1.2.1.2.coprime_card_index
    rw [hOuter.2.2.2.index_eq_card,
      Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
        hP.1.2.1.1,
      Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hDleM] at h
    exact h
  have hW₂leD : W₂ ≤ D := hPartner.2.2.1.trans hFleD
  have hFactorsCoprime : Nat.Coprime (Nat.card W₁) (Nat.card W₂) :=
    hCoprime.coprime_dvd_right (Subgroup.card_dvd_of_le hW₂leD)
  have hWcyclic : IsCyclic W := by
    apply defW.mulEquiv.isCyclic.mp
    exact Group.isCyclic_prod_iff.mpr
      ⟨hP.1.1, hPartner.1, hFactorsCoprime⟩
  exact
    { fitting_decomposition := hDirect
      derived_centralizes_fitting := hDerCent
      nontrivial_not_le_centralizer := hNotCent
      normalized_ti := hP.2.2.2.2
      cyclic_ti :=
        { cyclic := hWcyclic
          odd_card := mFT_odd W
          normedTI := hP.2.2.2.2 } }

/-! ## Canonical witnesses and completion to the five FT types -/

/-- A non-type-I maximal subgroup admits a type-P witness. -/
theorem FTtypeP_witness (M : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hnot1 : FTtype M ≠ 1) :
    exists_typeP (of_typeP M) := by
  have hrange := FTtype_range M
  have hcases :
      FTtype M = 2 ∨ FTtype M = 3 ∨
        FTtype M = 4 ∨ FTtype M = 5 := by
    omega
  rcases hcases with h2 | h3 | h4 | h5
  · obtain ⟨U, W, W₁, W₂, defW, h⟩ := (FTtypeP 2 M hM).mpr h2
    exact ⟨U, W, W₁, W₂, defW, h.1.1⟩
  · obtain ⟨U, W, W₁, W₂, defW, h⟩ := (FTtypeP 3 M hM).mpr h3
    exact ⟨U, W, W₁, W₂, defW, h.1.1⟩
  · obtain ⟨U, W, W₁, W₂, defW, h⟩ := (FTtypeP 4 M hM).mpr h4
    exact ⟨U, W, W₁, W₂, defW, h.1.1⟩
  · obtain ⟨U, W, W₁, W₂, defW, h⟩ := (FTtypeP 5 M hM).mpr h5
    exact ⟨U, W, W₁, W₂, defW, h.1⟩

/-- Any two type-P witnesses for one maximal subgroup are conjugate inside
that subgroup, simultaneously on all four displayed subgroups. -/
theorem of_typeP_conj
    (M U W W₁ W₂ U' W' W₁' W₂' : Subgroup G)
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (defW' : IsInternalDirectProductIn W₁' W₂' W')
    (hM : M ∈ minSimple_max_groups (G := G))
    (hP : of_typeP M U W W₁ W₂ defW)
    (hP' : of_typeP M U' W' W₁' W₂' defW') :
    ∃ x ∈ M,
      conjugateSubgroup8 U x = U' ∧
      conjugateSubgroup8 W₁ x = W₁' ∧
      conjugateSubgroup8 W₂ x = W₂' ∧
      conjugateSubgroup8 W x = W' := by
  obtain ⟨x₂, hx₂M, hW₁x₂⟩ :=
    of_typeP_compl_conj M U W W₁ W₂ defW hP W₁' hP'.1.2.2.2
  let D := derivedWithin M
  let F := Fitting_core M
  let U₀' := conjugateSubgroup8 U' x₂⁻¹
  let hOuter := hP.1.2.2.2
  let hInner := hP.2.1.2.2.2
  have hDleM : D ≤ M := hOuter.1
  have hMnormD : M ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDleM).1
      hOuter.2.2.1
  have hFleM : F ≤ M := Fcore_sub M
  have hMnormF : M ≤ Subgroup.normalizer (F : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFleM).1
      (Fcore_normal M)
  have hDfix₂ : conjugateSubgroup8 D x₂⁻¹ = D :=
    conjugateSubgroup8_eq_self_of_mem_normalizer
      (hMnormD (M.inv_mem hx₂M))
  have hFfix₂ : conjugateSubgroup8 F x₂⁻¹ = F :=
    conjugateSubgroup8_eq_self_of_mem_normalizer
      (hMnormF (M.inv_mem hx₂M))
  have hU₀'sd : IsInternalSemidirectProductIn F U₀' D := by
    have hmap := semidirect_map_mulEquiv8 hP'.2.1.2.2.2
      (MulAut.conj x₂⁻¹)
    change IsInternalSemidirectProductIn
      (conjugateSubgroup8 (Fitting_core M) x₂⁻¹)
      (conjugateSubgroup8 U' x₂⁻¹)
      (conjugateSubgroup8 (derivedWithin M) x₂⁻¹) at hmap
    simpa only [F, D, U₀', hFfix₂, hDfix₂] using hmap
  let FD : Subgroup D := F.subgroupOf D
  have hFleD : F ≤ D := hInner.1
  have hUleD : U ≤ D := hInner.2.1
  have hU₀'leD : U₀' ≤ D := hU₀'sd.2.1
  letI : FD.Normal := hInner.2.2.1
  have hFDSol : IsSolvable FD := by
    letI : Group.IsNilpotent F := Fcore_nil M
    letI : IsSolvable F := inferInstance
    exact isSolvable_of_injective
      (Subgroup.subgroupOfEquivOfLe hFleD).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hFleD).injective
  letI : IsSolvable FD := hFDSol
  have hFHallD : IsHall (primeSupport (Nat.card F)) FD :=
    isHall_subgroupOf_of_le8 hFleD hDleM (Fcore_Hall M)
  obtain ⟨n, hn⟩ := Subgroup.solvable_complement_conjugacy
    hFHallD.coprime_card_index hInner.2.2.2 hU₀'sd.2.2.2
  have hU₀'n : U₀' = conjugateSubgroup8 U (n : G) :=
    (ambient_conjugate_eq_of_subgroupOf8 hUleD hU₀'leD n hn).symm
  let pi := primeSupport (Nat.card W₁)
  have hDpi : IsPiNumber piᶜ (Nat.card D) := by
    rw [← Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hDleM,
      ← hOuter.2.2.2.index_eq_card]
    exact hP.1.2.1.2.isPiNumber_index
  have hW₁pi : IsPiNumber pi (Nat.card W₁) :=
    IsPiNumber.primeSupport_self
  have hW₁normD : W₁ ≤ Subgroup.normalizer (D : Set G) :=
    hP.1.2.1.1.trans hMnormD
  have hW₁back : conjugateSubgroup8 W₁' x₂⁻¹ = W₁ := by
    rw [← hW₁x₂, conjugateSubgroup8_mul]
    rw [show x₂⁻¹ * x₂ = 1 by simp, conjugateSubgroup8_one]
  have hW₁normU₀' : W₁ ≤ Subgroup.normalizer (U₀' : Set G) := by
    have hmap := Subgroup.map_mono
      (f := (MulAut.conj x₂⁻¹).toMonoidHom) hP'.2.1.2.2.1
    rw [Subgroup.map_equiv_normalizer_eq U' (MulAut.conj x₂⁻¹)] at hmap
    change conjugateSubgroup8 W₁' x₂⁻¹ ≤
      Subgroup.normalizer (conjugateSubgroup8 U' x₂⁻¹ : Set G) at hmap
    simpa only [hW₁back, U₀'] using hmap
  let L := (D ⊔ W₁) ⊓ Subgroup.normalizer (U₀' : Set G)
  have hLM : L ≤ M :=
    inf_le_left.trans_eq (semidirect_sup_eq8 hOuter)
  have hLsol : IsSolvable L := by
    letI : IsSolvable M := of_typeP_sol M U W W₁ W₂ defW hP
    exact isSolvable_of_injective (Subgroup.inclusion hLM)
      (Subgroup.inclusion_injective hLM)
  obtain ⟨z, hz, hUz⟩ :=
    exists_centralizerWithin_conjugator_of_coprime_join
      (pi := pi) hW₁normD hDpi hW₁pi hP.2.1.2.2.1
        hW₁normU₀' hLsol (D.inv_mem (n : D).property)
        (by simpa [conjugateSubgroup8] using hU₀'n)
  let t : G := z⁻¹
  have htD : t ∈ D := D.inv_mem hz.1
  have htM : t ∈ M := hDleM htD
  have htCent : t ∈ Subgroup.centralizer (W₁ : Set G) :=
    (Subgroup.centralizer (W₁ : Set G)).inv_mem hz.2
  have hUt : conjugateSubgroup8 U t = U₀' := by
    change U.map (MulAut.conj z⁻¹).toMonoidHom = U₀'
    exact hUz.symm
  have hW₁t : conjugateSubgroup8 W₁ t = W₁ :=
    conjugateSubgroup8_eq_self_of_mem_normalizer
      ((Subgroup.centralizer_le_normalizer (W₁ : Set G)) htCent)
  let y : G := x₂ * t
  have hyM : y ∈ M := M.mul_mem hx₂M htM
  have hUy : conjugateSubgroup8 U y = U' := by
    rw [← conjugateSubgroup8_mul U t x₂, hUt]
    dsimp only [U₀']
    rw [conjugateSubgroup8_mul]
    rw [show x₂ * x₂⁻¹ = 1 by simp, conjugateSubgroup8_one]
  have hW₁y : conjugateSubgroup8 W₁ y = W₁' := by
    rw [← conjugateSubgroup8_mul W₁ t x₂, hW₁t, hW₁x₂]
  have hDfixy : conjugateSubgroup8 D y = D :=
    conjugateSubgroup8_eq_self_of_mem_normalizer (hMnormD hyM)
  have hW₂y : conjugateSubgroup8 W₂ y = W₂' := by
    have hcent := congrArg
      (fun H : Subgroup G ↦ conjugateSubgroup8 H y)
      (typeP_cent_compl M U W W₁ W₂ defW hP)
    change (centralizerWithin (derivedWithin M) W₁).map
      (MulAut.conj y).toMonoidHom =
        W₂.map (MulAut.conj y).toMonoidHom at hcent
    rw [centralizerWithin_map_mulEquiv_type8] at hcent
    change centralizerWithin (conjugateSubgroup8 D y)
      (conjugateSubgroup8 W₁ y) = conjugateSubgroup8 W₂ y at hcent
    rw [hDfixy, hW₁y,
      typeP_cent_compl M U' W' W₁' W₂' defW' hP'] at hcent
    exact hcent.symm
  have hWy : conjugateSubgroup8 W y = W' := by
    calc
      conjugateSubgroup8 W y =
          conjugateSubgroup8 (W₁ ⊔ W₂) y := by
        rw [directProduct_sup_eq8 defW]
      _ = conjugateSubgroup8 W₁ y ⊔ conjugateSubgroup8 W₂ y := by
        exact Subgroup.map_sup W₁ W₂ (MulAut.conj y).toMonoidHom
      _ = W₁' ⊔ W₂' := by rw [hW₁y, hW₂y]
      _ = W' := directProduct_sup_eq8 defW'
  exact ⟨y, hyM, hUy, hW₁y, hW₂y, hWy⟩

/-- Every type-P maximal subgroup has non-I FT type. -/
theorem FTtypeP_neq1
    (M U W W₁ W₂ : Subgroup G)
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hP : of_typeP M U W W₁ W₂ defW) :
    FTtype M ≠ 1 := by
  intro htype
  obtain ⟨V, hV⟩ := (FTtypeP 1 M hM).mpr htype
  exact typePF_exclusion M U W W₁ W₂ V defW hP hV.1

/-- A type-P witness whose maximal subgroup is not type V satisfies the
common type-II--IV predicate. -/
theorem compl_of_typeII_IV
    (M U W W₁ W₂ : Subgroup G)
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hP : of_typeP M U W W₁ W₂ defW)
    (hnot5 : FTtype M ≠ 5) :
    of_typeII_IV M U W W₁ W₂ defW := by
  have hnot1 := FTtypeP_neq1 M U W W₁ W₂ defW hM hP
  have hrange := FTtype_range M
  have hcases : FTtype M = 2 ∨ FTtype M = 3 ∨ FTtype M = 4 := by
    omega
  obtain ⟨U', W', W₁', W₂', defW', hExact⟩ :
      exists_typeP (of_typeII_IV M) := by
    rcases hcases with h2 | h3 | h4
    · obtain ⟨U', W', W₁', W₂', defW', h⟩ :=
        (FTtypeP 2 M hM).mpr h2
      exact ⟨U', W', W₁', W₂', defW', h.1⟩
    · obtain ⟨U', W', W₁', W₂', defW', h⟩ :=
        (FTtypeP 3 M hM).mpr h3
      exact ⟨U', W', W₁', W₂', defW', h.1⟩
    · obtain ⟨U', W', W₁', W₂', defW', h⟩ :=
        (FTtypeP 4 M hM).mpr h4
      exact ⟨U', W', W₁', W₂', defW', h.1⟩
  obtain ⟨x, hxM, hUx, hW₁x, _, _⟩ :=
    of_typeP_conj M U W W₁ W₂ U' W' W₁' W₂'
      defW defW' hM hP hExact.1
  refine ⟨hP, ?_, ?_, hExact.2.2.2⟩
  · intro hUbot
    apply hExact.2.1
    rw [← hUx, hUbot]
    simp [conjugateSubgroup8]
  · have hp := hExact.2.2.1
    rw [← hW₁x, conjugateSubgroup8,
      Subgroup.card_map_of_injective (MulAut.conj x).injective] at hp
    exact hp

/-- Complete a type-P witness of FT type II. -/
theorem compl_of_typeII
    (M U W W₁ W₂ : Subgroup G)
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hP : of_typeP M U W W₁ W₂ defW)
    (htype : FTtype M = 2) :
    of_typeII M U W W₁ W₂ defW := by
  obtain ⟨U', W', W₁', W₂', defW', hExact⟩ :=
    (FTtypeP 2 M hM).mpr htype
  obtain ⟨x, hxM, hUx, _, _, _⟩ :=
    of_typeP_conj M U W W₁ W₂ U' W' W₁' W₂'
      defW defW' hM hP hExact.1.1
  have hCommon := compl_of_typeII_IV M U W W₁ W₂ defW hM hP
    (by omega)
  have hComm : IsMulCommutative U := by
    have hmap : IsMulCommutative (conjugateSubgroup8 U x) := by
      rw [hUx]
      exact hExact.2.1
    exact isMulCommutative_of_mulEquiv8 hmap
      ((MulAut.conj x).subgroupMap U).symm
  have hNotNorm : ¬ Subgroup.normalizer (U : Set G) ≤ M :=
    (not_congr (normalizer_le_conjugate_iff8 hxM hUx)).mpr
      hExact.2.2.1
  have hDerivedSD : IsInternalSemidirectProductIn
      (Fitting_core (derivedWithin M)) U (derivedWithin M) := by
    rw [hExact.2.2.2.2]
    exact hP.2.1.2.2.2
  have hDerivedF : of_typeF (derivedWithin M) U :=
    compl_of_typeF (derivedWithin M) U U' hDerivedSD hExact.2.2.2.1
  exact ⟨hCommon, hComm, hNotNorm, hDerivedF, hExact.2.2.2.2⟩

/-- Complete a type-P witness of FT type III. -/
theorem compl_of_typeIII
    (M U W W₁ W₂ : Subgroup G)
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hP : of_typeP M U W W₁ W₂ defW)
    (htype : FTtype M = 3) :
    of_typeIII M U W W₁ W₂ defW := by
  obtain ⟨U', W', W₁', W₂', defW', hExact⟩ :=
    (FTtypeP 3 M hM).mpr htype
  obtain ⟨x, hxM, hUx, _, _, _⟩ :=
    of_typeP_conj M U W W₁ W₂ U' W' W₁' W₂'
      defW defW' hM hP hExact.1.1
  refine ⟨compl_of_typeII_IV M U W W₁ W₂ defW hM hP
    (by omega), ?_, ?_⟩
  · have hmap : IsMulCommutative (conjugateSubgroup8 U x) := by
      rw [hUx]
      exact hExact.2.1
    exact isMulCommutative_of_mulEquiv8 hmap
      ((MulAut.conj x).subgroupMap U).symm
  · exact (normalizer_le_conjugate_iff8 hxM hUx).mpr hExact.2.2

/-- Complete a type-P witness of FT type IV. -/
theorem compl_of_typeIV
    (M U W W₁ W₂ : Subgroup G)
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hP : of_typeP M U W W₁ W₂ defW)
    (htype : FTtype M = 4) :
    of_typeIV M U W W₁ W₂ defW := by
  obtain ⟨U', W', W₁', W₂', defW', hExact⟩ :=
    (FTtypeP 4 M hM).mpr htype
  obtain ⟨x, hxM, hUx, _, _, _⟩ :=
    of_typeP_conj M U W W₁ W₂ U' W' W₁' W₂'
      defW defW' hM hP hExact.1.1
  refine ⟨compl_of_typeII_IV M U W W₁ W₂ defW hM hP
    (by omega), ?_, ?_⟩
  · intro hComm
    apply hExact.2.1
    have hmap := isMulCommutative_of_mulEquiv8 hComm
      ((MulAut.conj x).subgroupMap U)
    change IsMulCommutative (conjugateSubgroup8 U x) at hmap
    rwa [hUx] at hmap
  · exact (normalizer_le_conjugate_iff8 hxM hUx).mpr hExact.2.2

/-- Complete a type-P witness of FT type V. -/
theorem compl_of_typeV
    (M U W W₁ W₂ : Subgroup G)
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hP : of_typeP M U W W₁ W₂ defW)
    (htype : FTtype M = 5) :
    of_typeV M U W W₁ W₂ defW := by
  obtain ⟨U', W', W₁', W₂', defW', hExact⟩ :=
    (FTtypeP 5 M hM).mpr htype
  obtain ⟨x, _, hUx, hW₁x, _, _⟩ :=
    of_typeP_conj M U W W₁ W₂ U' W' W₁' W₂'
      defW defW' hM hP hExact.1
  have hUbot : U = ⊥ := by
    have hMap : U.map (MulAut.conj x).toMonoidHom = ⊥ := by
      change conjugateSubgroup8 U x = ⊥
      rw [hUx, hExact.2.1]
    exact (Subgroup.map_eq_bot_iff_of_injective U
      (MulAut.conj x).injective).mp hMap
  have hCard : Nat.card W₁' = Nat.card W₁ := by
    rw [← hW₁x, conjugateSubgroup8,
      Subgroup.card_map_of_injective (MulAut.conj x).injective]
  exact ⟨hP, hUbot, by simpa [hCard] using hExact.2.2⟩

/-! ## The exceptional type-P pair -/

/-- Symmetry of the exceptional pair. -/
theorem typeP_pair_sym
    (S T W W₁ W₂ : Subgroup G)
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (xdefW : IsInternalDirectProductIn W₂ W₁ W)
    (hpair : typeP_pair S T W W₁ W₂ defW) :
    typeP_pair T S W W₂ W₁ xdefW := by
  have hdef : xdefW = defW.swap := Subsingleton.elim _ _
  subst xdefW
  exact
    { cyclic_ti := hpair.cyclic_ti.swap
      S_maximal := hpair.T_maximal
      T_maximal := hpair.S_maximal
      S_decomposition := hpair.T_decomposition
      T_decomposition := hpair.S_decomposition
      intersection_eq := by simpa [inf_comm] using hpair.intersection_eq
      one_type_two := hpair.one_type_two.elim Or.inr Or.inl
      S_type_range := hpair.T_type_range
      T_type_range := hpair.S_type_range
      controls_non_type_one := by
        intro M hM hnot
        rcases hpair.controls_non_type_one M hM hnot with hS | hT
        · exact Or.inr hS
        · exact Or.inl hT }

/-- Peterfalvi (8.8): either all maximal subgroups have type I, or an
exceptional type-P pair controls the non-type-I subgroups. -/
theorem FTtypeP_pair_cases :
    all_FTtype1 (G := G) ∨
      ∃ S T : Subgroup G,
        exists_typeP
          (fun _ W W₁ W₂ defW ↦ typeP_pair S T W W₁ W₂ defW) := by
  rcases (BGsummaryI (G := G)).type_classification with hAll | ⟨S, T, hpair⟩
  · exact Or.inl hAll
  · right
    refine ⟨S, T, S, hpair.W, hpair.W₁, hpair.W₂, hpair.direct_W, ?_⟩
    refine
      { cyclic_ti := ?_
        S_maximal := hpair.S_maximal
        T_maximal := hpair.T_maximal
        S_decomposition := hpair.S_decomposition
        T_decomposition := hpair.T_decomposition
        intersection_eq := hpair.intersection_eq
        one_type_two := hpair.one_type_two
        S_type_range := hpair.S_type_range
        T_type_range := hpair.T_type_range
        controls_non_type_one := ?_ }
    · exact
        { cyclic := hpair.W_cyclic
          odd_card := mFT_odd hpair.W
          normedTI := hpair.outside_normalizedTI }
    · intro M hM hnot
      obtain ⟨g, hg⟩ := hpair.controls_non_type_one hM hnot
      rcases hg with hg | hg
      · exact Or.inl ⟨g, hg.symm⟩
      · exact Or.inr ⟨g, hg.symm⟩

/-- Peterfalvi (8.9): the first member of an exceptional pair has a
type-P witness with the pair's displayed factors. -/
theorem typeP_pairW
    (S T W W₁ W₂ : Subgroup G)
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (hpair : typeP_pair S T W W₁ W₂ defW) :
    ∃ U : Subgroup G, of_typeP S U W W₁ W₂ defW := by
  have hSnot1 : FTtype S ≠ 1 := by
    have hrange := hpair.S_type_range
    omega
  obtain ⟨U', W', W₁', W₂', defW', hP'⟩ :=
    FTtypeP_witness S hpair.S_maximal hSnot1
  obtain ⟨y, hyS, hW₁y⟩ :=
    of_typeP_compl_conj S U' W' W₁' W₂' defW' hP' W₁
      hpair.S_decomposition
  let D := derivedWithin S
  let B := conjugateSubgroup8 W₂' y
  have hDleS : D ≤ S := hpair.S_decomposition.1
  have hDfix : conjugateSubgroup8 D y = D :=
    conjugateSubgroup8_eq_self_of_mem_normalizer
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hDleS).1
        hpair.S_decomposition.2.2.1 hyS)
  have hCentDB : centralizerWithin D W₁ = B := by
    have hmap := congrArg
      (fun H : Subgroup G ↦ conjugateSubgroup8 H y)
      (typeP_cent_compl S U' W' W₁' W₂' defW' hP')
    change (centralizerWithin (derivedWithin S) W₁').map
      (MulAut.conj y).toMonoidHom =
        W₂'.map (MulAut.conj y).toMonoidHom at hmap
    rw [centralizerWithin_map_mulEquiv_type8] at hmap
    change centralizerWithin (conjugateSubgroup8 D y)
      (conjugateSubgroup8 W₁' y) = B at hmap
    rw [hDfix, hW₁y] at hmap
    exact hmap
  have hBcyclic : IsCyclic B :=
    ((MulAut.conj y).subgroupMap W₂').isCyclic.mp hP'.2.2.2.1.1
  have hWleS : W ≤ S := by
    intro w hw
    have hwST : w ∈ S ⊓ T := by
      rw [hpair.intersection_eq]
      exact hw
    exact hwST.1
  have hW₂leS : W₂ ≤ S := defW.right_le.trans hWleS
  have hW₁leS : W₁ ≤ S := hpair.S_decomposition.2.1
  have hW₂leD : W₂ ≤ D := by
    let W₂S : Subgroup S := W₂.subgroupOf S
    let DS : Subgroup S := D.subgroupOf S
    have hcop : (Nat.card W₂S).Coprime DS.index := by
      rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hW₂leS,
        hpair.S_decomposition.2.2.2.symm.index_eq_card,
        Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hW₁leS]
      exact hpair.cyclic_ti.factor_card_coprime.symm
    have hle : W₂S ≤ DS :=
      le_normal_of_coprime_index8 hpair.S_decomposition.2.2.1 hcop
    intro w hw
    let wS : S := ⟨w, hW₂leS hw⟩
    exact hle (show wS ∈ W₂S from hw)
  have hW₂leB : W₂ ≤ B := by
    intro w hw
    rw [← hCentDB]
    refine ⟨hW₂leD hw, ?_⟩
    intro a ha
    exact defW.commute ⟨a, ha⟩ ⟨w, hw⟩ |>.eq
  obtain ⟨a₁, ha₁W₁, ha₁ne⟩ := exists_mem_ne_one8
    (W₁.one_lt_card_iff_ne_bot.mp hpair.cyclic_ti.one_lt_card_left)
  obtain ⟨a₂, ha₂W₂, ha₂ne⟩ := exists_mem_ne_one8
    (W₂.one_lt_card_iff_ne_bot.mp hpair.cyclic_ti.one_lt_card_right)
  let a₁W : W₁ := ⟨a₁, ha₁W₁⟩
  let a₂W : W₂ := ⟨a₂, ha₂W₂⟩
  let aW : W := defW.mulEquiv (a₁W, a₂W)
  have ha₁Wne : a₁W ≠ 1 := by
    intro h
    exact ha₁ne (congrArg Subtype.val h)
  have ha₂Wne : a₂W ≠ 1 := by
    intro h
    exact ha₂ne (congrArg Subtype.val h)
  have ha : (aW : G) ∈ cyclicTISet W W₁ W₂ := by
    apply mem_cyclicTISet.mpr
    refine ⟨aW.property, ?_, ?_⟩
    · intro haW₁
      exact ha₂Wne
        ((defW.mulEquiv_mem_left_iff (a₁W, a₂W)).mp haW₁)
    · intro haW₂
      exact ha₁Wne
        ((defW.mulEquiv_mem_right_iff (a₁W, a₂W)).mp haW₂)
  have hBleW : B ≤ W := by
    letI : IsCyclic B := hBcyclic
    letI : IsMulCommutative B := inferInstance
    intro b hb
    have hbCent : b ∈ centralizerWithin D W₁ := by
      rw [hCentDB]
      exact hb
    have hcomm₁ : Commute a₁ b := hbCent.2 a₁ ha₁W₁
    have hcomm₂ : Commute a₂ b := by
      let a₂B : B := ⟨a₂, hW₂leB ha₂W₂⟩
      let bB : B := ⟨b, hb⟩
      change a₂ * b = b * a₂
      exact congrArg Subtype.val (mul_comm a₂B bB)
    have hcommA : Commute (aW : G) b := by
      change (a₁ * a₂) * b = b * (a₁ * a₂)
      calc
        (a₁ * a₂) * b = a₁ * (a₂ * b) := by rw [mul_assoc]
        _ = a₁ * (b * a₂) := by rw [hcomm₂.eq]
        _ = (a₁ * b) * a₂ := by rw [mul_assoc]
        _ = (b * a₁) * a₂ := by rw [hcomm₁.eq]
        _ = b * (a₁ * a₂) := by rw [mul_assoc]
    apply hpair.cyclic_ti.normedTI.centralizerWithin_zpowers_le ha
    refine ⟨Subgroup.mem_top b, ?_⟩
    intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (hcommA.zpow_left n).eq
  have hDinfW : D ⊓ W = W₂ := by
    apply le_antisymm
    · intro z hz
      let zW : W := ⟨z, hz.2⟩
      obtain ⟨⟨a, b⟩, hab⟩ := defW.complement.2 zW
      have habG : (a : G) * (b : G) = z :=
        congrArg (fun w : W ↦ (w : G)) hab
      have haD : (a : G) ∈ D := by
        have haEq : (a : G) = z * (b : G)⁻¹ := by
          rw [← habG]
          simp
        rw [haEq]
        exact D.mul_mem hz.1 (D.inv_mem (hW₂leD b.property))
      have hDisDW₁ : Disjoint D W₁ :=
        ambient_disjoint_of_subgroupOf8 hDleS hW₁leS
          hpair.S_decomposition.2.2.2.disjoint
      have haOne : (a : G) = 1 := by
        apply Subgroup.mem_bot.mp
        rw [← disjoint_iff.mp hDisDW₁]
        exact ⟨haD, a.property⟩
      have hzb : z = (b : G) := by
        rw [← habG, haOne, one_mul]
      rw [hzb]
      exact b.property
    · intro z hz
      exact ⟨hW₂leD hz, defW.right_le hz⟩
  have hBleD : B ≤ D := by
    intro b hb
    have hbCent : b ∈ centralizerWithin D W₁ := by
      rw [hCentDB]
      exact hb
    exact hbCent.1
  have hBleW₂ : B ≤ W₂ := by
    intro b hb
    rw [← hDinfW]
    exact ⟨hBleD hb, hBleW hb⟩
  have hBeq : B = W₂ := le_antisymm hBleW₂ hW₂leB
  obtain ⟨defWy, hPy⟩ := conj_of_typeP S U' W' W₁' W₂' defW' hP' y
  have hSfix : conjugateSubgroup8 S y = S :=
    conjugateSubgroup8_eq_self_of_mem_normalizer
      (Subgroup.le_normalizer hyS)
  have hW₂y : conjugateSubgroup8 W₂' y = W₂ := hBeq
  have hWy : conjugateSubgroup8 W' y = W := by
    calc
      conjugateSubgroup8 W' y =
          conjugateSubgroup8 (W₁' ⊔ W₂') y := by
        rw [directProduct_sup_eq8 defW']
      _ = conjugateSubgroup8 W₁' y ⊔
          conjugateSubgroup8 W₂' y := by
        exact Subgroup.map_sup W₁' W₂' (MulAut.conj y).toMonoidHom
      _ = W₁ ⊔ W₂ := by rw [hW₁y, hW₂y]
      _ = W := directProduct_sup_eq8 defW
  refine ⟨conjugateSubgroup8 U' y, ?_⟩
  simpa only [hSfix, hW₁y, hW₂y, hWy] using hPy

end

end Submission.OddOrder.PF
