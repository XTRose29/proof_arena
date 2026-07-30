import Submission.OddOrder.BG.Section16.SummaryABC
import Submission.OddOrder.BG.Section16.TypeSpecAndFinalSummary
import Submission.OddOrder.BG.Section16.TypesAndSupport

/-!
# Peterfalvi Section 8: FT context definitions

This module is the dependency-first part of the Section 8 port.  It defines
the Peterfalvi signalizer and Dade support, records the type-F and type-P
result shapes, and supplies the subgroup transports shared by the later
theorem phases.

The transports live in `FTContextInternal`.  They are implementation API for
the split Section 8 modules, rather than additions to the mapped public API.
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
open scoped BigOperators Classical Pointwise IsMulCommutative

universe u

variable {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]

/-- Character-theoretic APIs use concrete finite enumerations.  The Section 8
interfaces are stated with `Finite`, so choose the canonical enumeration
locally whenever one is required. -/
local instance finiteFintype8 (K : Type*) [Finite K] : Fintype K :=
  Fintype.ofFinite K

/-! ## Definition 8.14 and source notation -/

/-- Ambient conjugation of a subgroup, corresponding to source notation
`M :^ x`. -/
def conjugateSubgroup8 (M : Subgroup G) (x : G) : Subgroup G :=
  M.map (MulAut.conj x).toMonoidHom

/-- Ambient conjugation of a set. -/
def conjugateSet8 (A : Set G) (x : G) : Set G :=
  (MulAut.conj x) '' A

/-- The full centralizer of an ambient element. -/
abbrev centralizerOfElement8 (x : G) : Subgroup G :=
  Subgroup.centralizer (Subgroup.zpowers x : Set G)

/-- The Peterfalvi signalizer attached to `M` at `x`. -/
def FTsignalizer (M : Subgroup G) (x : G) : Subgroup G :=
  if centralizerOfElement8 x ≤ M then
    ⊥
  else
    centralizerWithin (Fitting_core (elementNormalizer15 x))
      (Subgroup.zpowers x)

/-- `L` supports `M` when it contains the full centralizer of a supported
element whose full centralizer is not contained in `M`. -/
def FTsupports (M L : Subgroup G) : Prop :=
  ∃ x ∈ FTsupport M,
    ¬ centralizerOfElement8 x ≤ M ∧ centralizerOfElement8 x ≤ L

/-- The Dade support indexed by an FT support set. -/
def FT_Dade_support (M : Subgroup G) (A : Set G) : Set G :=
  {g | ∃ x ∈ A,
    g ∈ classSupportWithin (⊤ : Subgroup G)
      ((FTsignalizer M x : Set G) * ({x} : Set G))}

/-- Dade support indexed by `FTsupport1 M`. -/
abbrev FT_Dade1_support (M : Subgroup G) : Set G :=
  FT_Dade_support M (FTsupport1 M)

/-- Dade support indexed by the full FT support. -/
abbrev FT_Dade_full_support (M : Subgroup G) : Set G :=
  FT_Dade_support M (FTsupport M)

/-- Dade support indexed by `FTsupport0 M`. -/
abbrev FT_Dade0_support (M : Subgroup G) : Set G :=
  FT_Dade_support M (FTsupport0 M)

/-- Monotonicity of the Dade support in its indexing set. -/
theorem FT_Dade_supportS (M : Subgroup G) {A B : Set G}
    (hAB : A ⊆ B) :
    FT_Dade_support M A ⊆ FT_Dade_support M B := by
  rintro g ⟨x, hx, hg⟩
  exact ⟨x, hAB hx, hg⟩

/-! ## Structural interfaces used by the theorem phases -/

/-- A Frobenius decomposition displayed inside a common ambient subgroup. -/
def IsFrobeniusIn (H U M : Subgroup G) : Prop :=
  H ⊔ U = M ∧
    IsInternalSemidirectProductIn H U (H ⊔ U) ∧
    IsFrobeniusDecomposition
      (H.subgroupOf (H ⊔ U)) (U.subgroupOf (H ⊔ U))

/-- Every Sylow subgroup of `U` is cyclic. -/
def IsZGroup8 (U : Subgroup G) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p U), IsCyclic P

/-- Relative inertia of a character of the ambient Fitting core. -/
noncomputable def typeFInertiaWithin8
    (M U : Subgroup G)
    (i : IrreducibleCharacter (Fitting_core M) ℂ) : Subgroup G := by
  let H : Subgroup M := (Fitting_core M).subgroupOf M
  letI : H.Normal := by
    dsimp only [H]
    infer_instance
  let eH : H ≃* Fitting_core M :=
    Subgroup.subgroupOfEquivOfLe (Fcore_sub M)
  let iH : ClassFunction H ℂ :=
    ⟨fun h ↦ i (eH h), by
      intro x h
      change i (eH (x * h * x⁻¹)) = i (eH h)
      simpa only [map_mul, map_inv] using
        ClassFunction.conj_apply (i : ClassFunction (Fitting_core M) ℂ)
          (eH x) (eH h)⟩
  exact ((U.subgroupOf M) ⊓
    ClassFunction.inertia H iH).map M.subtype

/-- Conjugacy of ambient subgroups by an element of `M`. -/
def IsConjugateWithin8 (M A B : Subgroup G) : Prop :=
  ∃ x ∈ M, conjugateSubgroup8 A x = B

/-- A displayed Frobenius group satisfies the source type-F predicate. -/
theorem Frobenius_of_typeF (M U : Subgroup G)
    (hFrob : IsFrobeniusIn (Fitting_core M) U M) :
    of_typeF M U := by
  let H := Fitting_core M
  have hHU : H ⊔ U = M := hFrob.1
  have hsd : IsInternalSemidirectProductIn H U (H ⊔ U) := hFrob.2.1
  have hf : IsFrobeniusDecomposition
      (H.subgroupOf (H ⊔ U)) (U.subgroupOf (H ⊔ U)) := hFrob.2.2
  have hHne : H ≠ ⊥ := by
    intro hH
    apply hf.kernel_ne_bot
    ext x
    simp [hH]
  have hUne : U ≠ ⊥ := by
    intro hU
    apply hf.complement_ne_bot
    ext x
    simp [hU]
  have hsdM : IsInternalSemidirectProductIn H U M := by
    simpa only [hHU] using hsd
  refine ⟨hHne, hUne, hsdM, ?_, ?_⟩
  · refine ⟨⊥, bot_le, ?_, ?_, ?_⟩
    · infer_instance
    · infer_instance
    · intro x hx u hu
      have hxH : x ∈ H := hx.1
      have hx1 : x ≠ 1 := hx.2
      have huU : u ∈ U := hu.1
      let xH : H.subgroupOf (H ⊔ U) :=
        ⟨⟨x, (show H ≤ H ⊔ U from le_sup_left) hxH⟩, hxH⟩
      let uU : U.subgroupOf (H ⊔ U) :=
        ⟨⟨u, (show U ≤ H ⊔ U from le_sup_right) huU⟩, huU⟩
      have hcomm : Commute u x :=
        (Subgroup.mem_centralizer_iff.mp hu.2 x
          (Subgroup.mem_zpowers x)).symm
      have hfix :
          (uU : ↑(H ⊔ U)) * (xH : ↑(H ⊔ U)) *
              (uU : ↑(H ⊔ U))⁻¹ =
            (xH : ↑(H ⊔ U)) := by
        apply Subtype.ext
        change u * x * u⁻¹ = x
        calc
          u * x * u⁻¹ = x * u * u⁻¹ := by rw [hcomm.eq]
          _ = x := by simp
      have huOne : uU = 1 := by
        by_contra hu1
        have hxOne := hf.fixedPointFree uU hu1 xH hfix
        exact hx1 (congrArg (fun z : H.subgroupOf (H ⊔ U) ↦
          ((z : ↑(H ⊔ U)) : G)) hxOne)
      exact Subgroup.mem_bot.mpr
        (congrArg (fun z : U.subgroupOf (H ⊔ U) ↦
          ((z : ↑(H ⊔ U)) : G)) huOne)
  · exact ⟨U, le_rfl, rfl, hsd, hf⟩

/-- The conclusions of Peterfalvi (8.2). -/
structure TypeFContext (M U : Subgroup G) : Prop where
  complement_card :
    ∀ U₀ : Subgroup G,
      is_typeF_complement M U U₀ → Nat.card U₀ = Monoid.exponent U
  frobenius_iff_zgroup :
    IsFrobeniusIn (Fitting_core M) U M ↔ IsZGroup8 U
  inertia_le :
    ∀ (U₁ : Subgroup G) (i : IrreducibleCharacter (Fitting_core M) ℂ),
      is_typeF_inertia M U U₁ →
      i ≠ IrreducibleCharacter.trivial →
      typeFInertiaWithin8 M U i ≤ U₁

/-- The conclusions of Peterfalvi (8.5). -/
structure TypePContext
    (M U W W₁ W₂ : Subgroup G)
    (defW : IsInternalDirectProductIn W₁ W₂ W) : Prop where
  fitting_decomposition :
    IsInternalDirectProductIn (Fitting_core M)
      (centralizerWithin U (Fitting_core M)) (fittingWithin M)
  derived_centralizes_fitting :
    derivedWithin U ≤ Subgroup.centralizer (Fitting_core M : Set G)
  nontrivial_not_le_centralizer :
    U ≠ ⊥ → ¬ U ≤ Subgroup.centralizer (Fitting_core M : Set G)
  normalized_ti :
    IsNormalizedTI (cyclicTISet W W₁ W₂) ⊤ W
  cyclic_ti : CyclicTIHypothesis (⊤ : Subgroup G) W W₁ W₂ defW

/-- The source set `x ^: M`, expressed as right conjugates. -/
def conjugacyClassWithin8 (M : Subgroup G) (x : G) : Set G :=
  {y | ∃ m ∈ M, y = m⁻¹ * x * m}

/-- The `n`th derived term of `M`, mapped back to the ambient group. -/
def derivedSeriesWithin8 (M : Subgroup G) (n : ℕ) : Subgroup G :=
  (_root_.derivedSeries M n).map M.subtype

/-- Ambient-subgroup spelling of a Sylow subgroup of `H`. -/
def IsSylowWithin8 (p : ℕ) (S H : Subgroup G) : Prop :=
  ∃ P : Sylow p H, S = (P : Subgroup H).map H.subtype

/-! ## Reusable transports for the split Section 8 phases -/

namespace FTContextInternal

/-! ### Hall and Sylow bookkeeping -/

/-- Restrict a Hall subgroup along an intermediate subgroup. -/
theorem isHall_subgroupOf_of_le8
    {A B C : Subgroup G} (hAB : A ≤ B) (hBC : B ≤ C)
    {pi : Set ℕ} (hA : IsHall pi (A.subgroupOf C)) :
    IsHall pi (A.subgroupOf B) := by
  constructor
  · rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hAB]
    have hcard := hA.isPiNumber_card
    rwa [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
      (hAB.trans hBC)] at hcard
  · have hdvd : A.relIndex B ∣ A.relIndex C := by
      refine ⟨B.relIndex C, ?_⟩
      exact (A.relIndex_mul_relIndex B C hAB hBC).symm
    exact hA.isPiNumber_index.of_dvd hdvd

/-- Compose a Hall subgroup inside `B` with a Hall embedding of `B`. -/
theorem isHall_of_isHall_subgroupOf8
    {A B : Subgroup G} (hAB : A ≤ B)
    {pi rho : Set ℕ} (hpi : pi ⊆ rho)
    (hA : IsHall pi (A.subgroupOf B)) (hB : IsHall rho B) :
    IsHall pi A := by
  constructor
  · have hcard := hA.isPiNumber_card
    rwa [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hAB] at hcard
  · rw [← A.relIndex_mul_index hAB]
    apply hA.isPiNumber_index.mul
    apply hB.isPiNumber_index.mono
    intro p hpNotRho
    change p ∉ pi
    intro hpPi
    exact hpNotRho (hpi hpPi)

/-- A Sylow subgroup of a Hall subgroup maps to an ambient Sylow subgroup. -/
theorem exists_sylow_eq_map_of_sylow_hall8
    {K : Type u} [Group K] [Finite K]
    {pi : Set ℕ} {p : ℕ} (hp : p.Prime)
    {A : Subgroup K} (hA : IsHall pi A) (hpPi : p ∈ pi)
    (P : Sylow p A) :
    ∃ Q : Sylow p K,
      (Q : Subgroup K) = (P : Subgroup A).map A.subtype := by
  letI : Fact p.Prime := ⟨hp⟩
  let S : Subgroup K := (P : Subgroup A).map A.subtype
  have hSp : IsPGroup p S := P.isPGroup'.map A.subtype
  have hpAindex : ¬ p ∣ A.index := by
    intro hpIndex
    exact hA.isPiNumber_index hp hpIndex hpPi
  have hpSindex : ¬ p ∣ S.index := by
    dsimp only [S]
    rw [Subgroup.index_map_subtype]
    exact hp.not_dvd_mul P.not_dvd_index hpAindex
  exact ⟨hSp.toSylow hpSindex, rfl⟩

/-- A normal Hall subgroup contains every subgroup whose order uses only
its primes. -/
theorem isPiNumber_le_normal_isHall8
    {K : Type u} [Group K] [Finite K] {pi : Set ℕ}
    {A H : Subgroup K}
    (hHnormal : H.Normal) (hHHall : IsHall pi H)
    (hApi : IsPiNumber pi (Nat.card A)) : A ≤ H := by
  letI : H.Normal := hHnormal
  have hcop : (Nat.card A).Coprime H.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpA hpIndex
    exact hHHall.isPiNumber_index hp hpIndex (hApi hp hpA)
  intro x hx
  let q : K →* K ⧸ H := QuotientGroup.mk' H
  have horderA : orderOf (q x) ∣ Nat.card A :=
    (orderOf_map_dvd q x).trans (A.orderOf_dvd_natCard hx)
  have horderIndex : orderOf (q x) ∣ H.index := by
    simpa only [H.index_eq_card] using orderOf_dvd_natCard (q x)
  have horderOne : orderOf (q x) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horderA horderIndex
  exact (QuotientGroup.eq_one_iff x).mp
    (orderOf_eq_one_iff.mp horderOne)

/-- Coprimality with the index of a normal subgroup forces containment. -/
theorem le_normal_of_coprime_index8
    {K : Type u} [Group K] [Finite K] {A N : Subgroup K}
    (hNnormal : N.Normal)
    (hcop : (Nat.card A).Coprime N.index) : A ≤ N := by
  letI : N.Normal := hNnormal
  intro x hx
  let q : K →* K ⧸ N := QuotientGroup.mk' N
  have horderA : orderOf (q x) ∣ Nat.card A :=
    (orderOf_map_dvd q x).trans (A.orderOf_dvd_natCard hx)
  have horderIndex : orderOf (q x) ∣ N.index := by
    simpa only [N.index_eq_card] using orderOf_dvd_natCard (q x)
  have horderOne : orderOf (q x) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horderA horderIndex
  exact (QuotientGroup.eq_one_iff x).mp
    (orderOf_eq_one_iff.mp horderOne)

/-- The `pi`-core is Hall in a finite nilpotent group. -/
theorem piCore_isHall_of_isNilpotent8
    {K : Type u} [Group K] [Finite K] [Group.IsNilpotent K]
    (pi : Set ℕ) : IsHall pi (piCore pi K) := by
  refine ⟨piCore_isPiNumber pi, ?_⟩
  intro p hp hpIndex hpPi
  letI : Fact p.Prime := ⟨hp⟩
  let P : Sylow p K := Classical.choice Sylow.nonempty
  have hPnormal : (P : Subgroup K).Normal := by infer_instance
  have hPle : (P : Subgroup K) ≤ piCore pi K :=
    le_piCore hPnormal (P.isPGroup'.isPiNumber_natCard hpPi)
  exact P.not_dvd_index (hpIndex.trans (Subgroup.index_dvd_of_le hPle))

/-- Subgroups of coprime prime support commute inside a nilpotent group. -/
theorem nilpotent_subgroups_commute_of_coprime_pi8
    {K : Type u} [Group K] [Finite K] [Group.IsNilpotent K]
    {pi : Set ℕ} {A B : Subgroup K}
    (hA : IsPiNumber pi (Nat.card A))
    (hB : IsPiNumber piᶜ (Nat.card B)) :
    A ≤ Subgroup.centralizer (B : Set K) := by
  let O : Subgroup K := piCore pi K
  let O' : Subgroup K := piCore piᶜ K
  have hAO : A ≤ O :=
    isPiNumber_le_normal_isHall8 (by infer_instance)
      (piCore_isHall_of_isNilpotent8 pi) hA
  have hBO' : B ≤ O' :=
    isPiNumber_le_normal_isHall8 (by infer_instance)
      (piCore_isHall_of_isNilpotent8 piᶜ) hB
  have hdis : Disjoint O O' :=
    Subgroup.disjoint_of_coprime_natCard
      ((piCore_isPiNumber pi).coprime_compl
        (by simpa only [compl_compl] using
          (piCore_isPiNumber (G := K) piᶜ)))
  have hcomm := Subgroup.commute_of_normal_of_disjoint
    O O' (by infer_instance) (by infer_instance) hdis
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact (hcomm a b (hAO ha) (hBO' hb)).symm.eq

/-- Lift disjointness of two `subgroupOf` copies back to the ambient group. -/
theorem ambient_disjoint_of_subgroupOf8
    {A B K : Subgroup G} (hAK : A ≤ K) (hBK : B ≤ K)
    (hdis : Disjoint (A.subgroupOf K) (B.subgroupOf K)) :
    Disjoint A B := by
  rw [disjoint_iff]
  apply le_antisymm _ bot_le
  intro x hx
  apply Subgroup.mem_bot.mpr
  let xK : K := ⟨x, hAK hx.1⟩
  have hxK : xK ∈ (A.subgroupOf K) ⊓ (B.subgroupOf K) :=
    ⟨hx.1, hx.2⟩
  have hxOne : xK ∈ (⊥ : Subgroup K) := by
    rw [← disjoint_iff.mp hdis]
    exact hxK
  exact congrArg Subtype.val (Subgroup.mem_bot.mp hxOne)

/-! ### Conjugation and ambient equivalence -/

/-- Turn an intrinsic conjugacy equality in `M` into the corresponding
ambient equality. -/
theorem ambient_conjugate_eq_of_subgroupOf8
    {M A B : Subgroup G} (hAM : A ≤ M) (hBM : B ≤ M)
    (x : M)
    (hconj : B.subgroupOf M =
      (A.subgroupOf M).map (MulAut.conj x).toMonoidHom) :
    conjugateSubgroup8 A (x : G) = B := by
  apply le_antisymm
  · rintro y ⟨a, ha, rfl⟩
    let aM : M := ⟨a, hAM ha⟩
    have haMap : (MulAut.conj x) aM ∈ B.subgroupOf M := by
      rw [hconj]
      exact Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom ha
    exact haMap
  · intro y hy
    let yM : M := ⟨y, hBM hy⟩
    have hyMap : yM ∈
        (A.subgroupOf M).map (MulAut.conj x).toMonoidHom := by
      rw [← hconj]
      exact hy
    rcases hyMap with ⟨aM, haM, hay⟩
    refine ⟨(aM : G), haM, ?_⟩
    exact congrArg Subtype.val hay

/-- A subgroup conjugated by an element of its normalizer is unchanged. -/
theorem conjugateSubgroup8_eq_self_of_mem_normalizer
    {A : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (A : Set G)) :
    conjugateSubgroup8 A x = A :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp hx

/-- Composition law for the right-conjugation convention used here. -/
theorem conjugateSubgroup8_mul (A : Subgroup G) (x y : G) :
    conjugateSubgroup8 (conjugateSubgroup8 A x) y =
      conjugateSubgroup8 A (y * x) := by
  unfold conjugateSubgroup8
  rw [Subgroup.map_map]
  congr 1
  ext z
  simp [MulAut.conj_apply, mul_assoc]

/-- The ambient derived subgroup commutes with a group automorphism. -/
theorem derivedWithin_map_mulEquiv_type8
    (M : Subgroup G) (e : G ≃* G) :
    derivedWithin (M.map e.toMonoidHom) =
      (derivedWithin M).map e.toMonoidHom := by
  let eM : M ≃* M.map e.toMonoidHom := e.subgroupMap M
  have hcommutator :
      (_root_.commutator M).map eM.toMonoidHom =
        _root_.commutator (M.map e.toMonoidHom) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr eM.surjective]
    rfl
  unfold derivedWithin
  rw [← hcommutator, Subgroup.map_map, Subgroup.map_map]
  apply congrArg (fun f : M →* G ↦ (_root_.commutator M).map f)
  ext y
  rfl

/-- The second ambient derived subgroup commutes with a group automorphism. -/
theorem secondDerivedWithin_map_mulEquiv8
    (M : Subgroup G) (e : G ≃* G) :
    secondDerivedWithin (M.map e.toMonoidHom) =
      (secondDerivedWithin M).map e.toMonoidHom := by
  unfold secondDerivedWithin
  rw [derivedWithin_map_mulEquiv_type8,
    derivedWithin_map_mulEquiv_type8]

/-- Relative centralizers commute with an ambient automorphism. -/
theorem centralizerWithin_map_mulEquiv_type8
    (D A : Subgroup G) (e : G ≃* G) :
    (centralizerWithin D A).map e.toMonoidHom =
      centralizerWithin (D.map e.toMonoidHom)
        (A.map e.toMonoidHom) := by
  ext y
  rw [Subgroup.mem_map_equiv]
  constructor
  · intro hy
    refine ⟨Subgroup.mem_map_equiv.mpr hy.1, ?_⟩
    intro a ha
    have ha' : e.symm a ∈ A := Subgroup.mem_map_equiv.mp ha
    simpa using congrArg e (hy.2 (e.symm a) ha')
  · intro hy
    refine ⟨Subgroup.mem_map_equiv.mp hy.1, ?_⟩
    intro a ha
    have hea : e a ∈ A.map e.toMonoidHom :=
      Subgroup.mem_map_of_mem e.toMonoidHom ha
    simpa using congrArg e.symm (hy.2 (e a) hea)

/-- Element centralizers commute with an ambient automorphism. -/
theorem elementCentralizerWithin_map_mulEquiv8
    (D : Subgroup G) (a : G) (e : G ≃* G) :
    (elementCentralizerWithin D a).map e.toMonoidHom =
      elementCentralizerWithin (D.map e.toMonoidHom) (e a) := by
  change
    (centralizerWithin D (Subgroup.zpowers a)).map e.toMonoidHom =
      centralizerWithin (D.map e.toMonoidHom)
        (Subgroup.zpowers (e.toMonoidHom a))
  rw [centralizerWithin_map_mulEquiv_type8, MonoidHom.map_zpowers]

/-- Complementarity is invariant under a multiplicative equivalence. -/
theorem isComplement_map_mulEquiv8
    {K L : Type u} [Group K] [Group L]
    {A B : Subgroup K} (h : A.IsComplement' B) (e : K ≃* L) :
    (A.map e.toMonoidHom).IsComplement'
      (B.map e.toMonoidHom) := by
  let eA : A ≃ A.map e.toMonoidHom := (e.subgroupMap A).toEquiv
  let eB : B ≃ B.map e.toMonoidHom := (e.subgroupMap B).toEquiv
  let ep : A × B ≃
      (A.map e.toMonoidHom) × (B.map e.toMonoidHom) :=
    eA.prodCongr eB
  let f : A × B → K := fun z ↦ (z.1 : K) * (z.2 : K)
  let f' : (A.map e.toMonoidHom) ×
      (B.map e.toMonoidHom) → L :=
    fun z ↦ (z.1 : L) * (z.2 : L)
  have hf : Function.Bijective f := h
  have hfun : f' = e ∘ f ∘ ep.symm := by
    funext z
    change (z.1 : L) * (z.2 : L) =
      e (e.symm (z.1 : L) * e.symm (z.2 : L))
    simp only [map_mul, e.apply_symm_apply]
  apply (Subgroup.isComplement_iff_bijective _ _).mpr
  change Function.Bijective f'
  rw [hfun]
  exact e.bijective.comp (hf.comp ep.symm.bijective)

/-- Frobenius decompositions are invariant under a multiplicative
equivalence. -/
theorem frobenius_map_mulEquiv8
    {K L : Type u} [Group K] [Group L]
    {A B : Subgroup K}
    (h : IsFrobeniusDecomposition A B) (e : K ≃* L) :
    IsFrobeniusDecomposition
      (A.map e.toMonoidHom) (B.map e.toMonoidHom) := by
  refine
    { isComplement := isComplement_map_mulEquiv8 h.isComplement e
      kernel_normal := Subgroup.Normal.map h.kernel_normal
        e.toMonoidHom e.surjective
      kernel_ne_bot := (not_congr
        (Subgroup.map_eq_bot_iff_of_injective A e.injective)).mpr
          h.kernel_ne_bot
      complement_ne_bot := (not_congr
        (Subgroup.map_eq_bot_iff_of_injective B e.injective)).mpr
          h.complement_ne_bot
      fixedPointFree := ?_ }
  intro r hr k hfix
  let r₀ : B := (e.subgroupMap B).symm r
  let k₀ : A := (e.subgroupMap A).symm k
  have hr₀ : r₀ ≠ 1 := by
    intro hrOne
    apply hr
    simpa [r₀] using congrArg (e.subgroupMap B) hrOne
  have hfix₀ : (r₀ : K) * (k₀ : K) * (r₀ : K)⁻¹ = k₀ := by
    apply e.injective
    simpa [r₀, k₀] using hfix
  have hk₀ := h.fixedPointFree r₀ hr₀ k₀ hfix₀
  simpa [k₀] using congrArg (e.subgroupMap A) hk₀

/-- Mapping then taking `subgroupOf` agrees with taking `subgroupOf` and
mapping by the induced equivalence. -/
theorem subgroupOf_map_mulEquiv8
    {A K : Subgroup G} (hAK : A ≤ K) (e : G ≃* G) :
    (A.subgroupOf K).map (e.subgroupMap K).toMonoidHom =
      (A.map e.toMonoidHom).subgroupOf
        (K.map e.toMonoidHom) := by
  ext y
  rw [Subgroup.mem_map_equiv]
  change e.symm (y : G) ∈ A ↔ (y : G) ∈ A.map e.toMonoidHom
  rw [Subgroup.mem_map_equiv]

/-- Internal semidirect products commute with an ambient automorphism. -/
theorem semidirect_map_mulEquiv8
    {N H K : Subgroup G}
    (h : IsInternalSemidirectProductIn N H K) (e : G ≃* G) :
    IsInternalSemidirectProductIn
      (N.map e.toMonoidHom) (H.map e.toMonoidHom)
      (K.map e.toMonoidHom) := by
  let eK : K ≃* K.map e.toMonoidHom := e.subgroupMap K
  have hN := subgroupOf_map_mulEquiv8 h.1 e
  have hH := subgroupOf_map_mulEquiv8 h.2.1 e
  refine ⟨Subgroup.map_mono h.1, Subgroup.map_mono h.2.1, ?_, ?_⟩
  · rw [← hN]
    exact Subgroup.Normal.map h.2.2.1 eK.toMonoidHom eK.surjective
  · rw [← hN, ← hH]
    exact isComplement_map_mulEquiv8 h.2.2.2 eK

/-- Internal direct products commute with an ambient automorphism. -/
theorem directProduct_map_mulEquiv8
    {A B W : Subgroup G}
    (h : IsInternalDirectProductIn A B W) (e : G ≃* G) :
    IsInternalDirectProductIn
      (A.map e.toMonoidHom) (B.map e.toMonoidHom)
      (W.map e.toMonoidHom) := by
  let eW : W ≃* W.map e.toMonoidHom := e.subgroupMap W
  have hA := subgroupOf_map_mulEquiv8 h.left_le e
  have hB := subgroupOf_map_mulEquiv8 h.right_le e
  refine
    { left_le := Subgroup.map_mono h.left_le
      right_le := Subgroup.map_mono h.right_le
      complement := ?_
      commute := ?_ }
  · rw [← hA, ← hB]
    exact isComplement_map_mulEquiv8 h.complement eW
  · intro a b
    let a₀ : A := (e.subgroupMap A).symm a
    let b₀ : B := (e.subgroupMap B).symm b
    have hab := h.commute a₀ b₀
    simpa [a₀, b₀] using Commute.map hab e.toMonoidHom

/-- Hall subgroups commute with a multiplicative equivalence. -/
theorem isHall_map_mulEquiv8
    {K L : Type*} [Group K] [Group L] [Finite K] [Finite L]
    {pi : Set ℕ} {A : Subgroup K} (e : K ≃* L)
    (hA : IsHall pi A) : IsHall pi (A.map e.toMonoidHom) := by
  constructor
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hA.isPiNumber_card
  · have hindex : (A.map e.toMonoidHom).index = A.index :=
      Subgroup.index_map_equiv A e
    exact hindex.symm ▸ hA.isPiNumber_index

/-- The `p`-core is invariant under a multiplicative equivalence. -/
theorem pCore_map_mulEquiv8
    {K L : Type*} [Group K] [Group L] [Finite K] [Finite L]
    (p : ℕ) [Fact p.Prime] (e : K ≃* L) :
    (pCore p K).map e.toMonoidHom = pCore p L := by
  have hker : IsPGroup p e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]
    exact IsPGroup.of_bot
  exact map_pCore_eq_of_surjective_of_ker_isPGroup
    e.toMonoidHom e.surjective hker

/-- The intrinsic Fitting subgroup is invariant under a multiplicative
equivalence. -/
theorem fittingCore_map_mulEquiv8
    {K L : Type*} [Group K] [Group L] [Finite K] [Finite L]
    (e : K ≃* L) :
    (fittingCore K).map e.toMonoidHom = fittingCore L := by
  rw [fittingCore, fittingCore, Subgroup.map_iSup]
  apply iSup_congr
  intro p
  letI : Fact (p : ℕ).Prime := ⟨p.property⟩
  exact pCore_map_mulEquiv8 (p : ℕ) e

/-- The ambient Fitting subgroup commutes with an ambient automorphism. -/
theorem fittingWithin_map_mulEquiv8
    (M : Subgroup G) (e : G ≃* G) :
    fittingWithin (M.map e.toMonoidHom) =
      (fittingWithin M).map e.toMonoidHom := by
  let M' : Subgroup G := M.map e.toMonoidHom
  let eM : M ≃* M' := e.subgroupMap M
  have hfit :
      (fittingCore M).map eM.toMonoidHom = fittingCore M' :=
    fittingCore_map_mulEquiv8 eM
  change (fittingCore M').map M'.subtype =
    ((fittingCore M).map M.subtype).map e.toMonoidHom
  rw [← hfit, Subgroup.map_map, Subgroup.map_map]
  apply congrArg (fun f : M →* G ↦ (fittingCore M).map f)
  ext y
  rfl

/-- The cyclic-TI set commutes with an ambient automorphism. -/
theorem cyclicTISet_map_mulEquiv8
    (W W₁ W₂ : Subgroup G) (e : G ≃* G) :
    cyclicTISet (W.map e.toMonoidHom) (W₁.map e.toMonoidHom)
        (W₂.map e.toMonoidHom) =
      e '' cyclicTISet W W₁ W₂ := by
  ext y
  constructor
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rcases mem_cyclicTISet.mp hy with ⟨hyW, hyW₁, hyW₂⟩
    exact mem_cyclicTISet.mpr
      ⟨Subgroup.mem_map_equiv.mp hyW,
        fun h ↦ hyW₁ (Subgroup.mem_map_equiv.mpr h),
        fun h ↦ hyW₂ (Subgroup.mem_map_equiv.mpr h)⟩
  · rintro ⟨z, hz, rfl⟩
    rcases mem_cyclicTISet.mp hz with ⟨hzW, hzW₁, hzW₂⟩
    exact mem_cyclicTISet.mpr
      ⟨Subgroup.mem_map_of_mem e.toMonoidHom hzW,
        fun h ↦ hzW₁ (by simpa using Subgroup.mem_map_equiv.mp h),
        fun h ↦ hzW₂ (by simpa using Subgroup.mem_map_equiv.mp h)⟩

/-- Normalized-TI data commutes with an ambient automorphism. -/
theorem isNormalizedTI_map_mulEquiv8
    {A : Set G} {D L : Subgroup G}
    (h : IsNormalizedTI A D L) (e : G ≃* G) :
    IsNormalizedTI (e '' A)
      (D.map e.toMonoidHom) (L.map e.toMonoidHom) := by
  rw [isNormalizedTI_iff_mem_conj] at h ⊢
  refine ⟨h.1.image e, Subgroup.map_mono h.2.1, ?_⟩
  rintro _ ⟨a, ha, rfl⟩ g hg
  have hgD : e.symm g ∈ D := Subgroup.mem_map_equiv.mp hg
  have hmem := h.2.2 ha hgD
  constructor
  · rintro ⟨b, hb, hbeq⟩
    apply Subgroup.mem_map_equiv.mpr
    apply hmem.mp
    have heq : (e.symm g)⁻¹ * a * e.symm g = b := by
      apply e.injective
      simpa using hbeq.symm
    exact heq ▸ hb
  · intro hgL
    have hpre : (e.symm g)⁻¹ * a * e.symm g ∈ A :=
      hmem.mpr (Subgroup.mem_map_equiv.mp hgL)
    refine ⟨(e.symm g)⁻¹ * a * e.symm g, hpre, ?_⟩
    simp

/-! ### Product and normalizer consequences -/

/-- The two factors of an internal direct product generate its ambient
subgroup. -/
theorem directProduct_sup_eq8
    {A B W : Subgroup G} (h : IsInternalDirectProductIn A B W) :
    A ⊔ B = W := by
  apply le_antisymm (sup_le h.left_le h.right_le)
  intro w hw
  let wW : W := ⟨w, hw⟩
  obtain ⟨⟨a, b⟩, hab⟩ := h.complement.2 wW
  have haA : (a : G) ∈ A := a.property
  have hbB : (b : G) ∈ B := b.property
  have habG : (a : G) * (b : G) = w := congrArg Subtype.val hab
  rw [← habG]
  exact Subgroup.mul_mem_sup haA hbB

/-- The two factors of an internal semidirect product generate its ambient
subgroup. -/
theorem semidirect_sup_eq8
    {N H K : Subgroup G} (h : IsInternalSemidirectProductIn N H K) :
    N ⊔ H = K := by
  apply le_antisymm (sup_le h.1 h.2.1)
  intro k hk
  let kK : K := ⟨k, hk⟩
  obtain ⟨⟨n, a⟩, hna⟩ := h.2.2.2.2 kK
  have hnN : (n : G) ∈ N := n.property
  have haH : (a : G) ∈ H := a.property
  have hnaG : (n : G) * (a : G) = k := congrArg Subtype.val hna
  rw [← hnaG]
  exact Subgroup.mul_mem_sup hnN haH

/-- Commutativity transports across a multiplicative equivalence. -/
theorem isMulCommutative_of_mulEquiv8
    {K L : Type u} [Group K] [Group L]
    (hK : IsMulCommutative K) (e : K ≃* L) :
    IsMulCommutative L := by
  apply isMulCommutative_iff.mpr
  intro x y
  apply e.symm.injective
  simpa only [map_mul] using
    (isMulCommutative_iff.mp hK (e.symm x) (e.symm y))

/-- Conjugate subgroups have equivalent normalizer-containment statements
inside a subgroup fixed by the conjugator. -/
theorem normalizer_le_conjugate_iff8
    {M A B : Subgroup G} {x : G}
    (hxM : x ∈ M) (hAB : conjugateSubgroup8 A x = B) :
    Subgroup.normalizer (A : Set G) ≤ M ↔
      Subgroup.normalizer (B : Set G) ≤ M := by
  let e : G ≃* G := MulAut.conj x
  have hMfix : M.map e.toMonoidHom = M :=
    conjugateSubgroup8_eq_self_of_mem_normalizer
      (Subgroup.le_normalizer hxM)
  have hOne : conjugateSubgroup8 A 1 = A := by
    unfold conjugateSubgroup8
    convert A.map_id using 1
    ext z
    simp
  have hBA : conjugateSubgroup8 B x⁻¹ = A := by
    rw [← hAB, conjugateSubgroup8_mul]
    rw [inv_mul_cancel x]
    exact hOne
  constructor
  · intro h
    have hmap := Subgroup.map_mono (f := e.toMonoidHom) h
    rw [Subgroup.map_equiv_normalizer_eq A e, hMfix] at hmap
    change Subgroup.normalizer (conjugateSubgroup8 A x : Set G) ≤ M at hmap
    rw [hAB] at hmap
    exact hmap
  · intro h
    let e' : G ≃* G := MulAut.conj x⁻¹
    have hMfix' : M.map e'.toMonoidHom = M :=
      conjugateSubgroup8_eq_self_of_mem_normalizer
        (Subgroup.le_normalizer (M.inv_mem hxM))
    have hmap := Subgroup.map_mono (f := e'.toMonoidHom) h
    rw [Subgroup.map_equiv_normalizer_eq B e', hMfix'] at hmap
    change Subgroup.normalizer (conjugateSubgroup8 B x⁻¹ : Set G) ≤ M at hmap
    rw [hBA] at hmap
    exact hmap

/-! ### Type-F transport -/

/-- The type-F inertia predicate commutes with an ambient automorphism. -/
theorem isTypeFInertia_map_mulEquiv8
    {M U U₁ : Subgroup G}
    (h : is_typeF_inertia M U U₁) (e : G ≃* G) :
    is_typeF_inertia (M.map e.toMonoidHom)
      (U.map e.toMonoidHom) (U₁.map e.toMonoidHom) := by
  have hFcore := Fitting_core_map_mulEquiv M e
  have hsub := subgroupOf_map_mulEquiv8 h.1 e
  refine ⟨Subgroup.map_mono h.1, ?_, ?_, ?_⟩
  · rw [← hsub]
    exact Subgroup.Normal.map h.2.1 (e.subgroupMap U).toMonoidHom
      (e.subgroupMap U).surjective
  · exact isMulCommutative_of_mulEquiv8 h.2.2.1
      (e.subgroupMap U₁)
  · intro x hx
    let x₀ : G := e.symm x
    have hx₀F : x₀ ∈ Fitting_core M := by
      apply Subgroup.mem_map_equiv.mp
      rw [← hFcore]
      exact hx.1
    have hx₀ne : x₀ ≠ 1 := by
      intro hxOne
      apply hx.2
      simpa [x₀] using congrArg e hxOne
    have hmap := Subgroup.map_mono (f := e.toMonoidHom)
      (h.2.2.2 x₀ ⟨hx₀F, hx₀ne⟩)
    simpa only [elementCentralizerWithin_map_mulEquiv8, x₀,
      e.apply_symm_apply] using hmap

/-- The type-F complement predicate commutes with an ambient automorphism. -/
theorem isTypeFComplement_map_mulEquiv8
    {M U U₀ : Subgroup G}
    (h : is_typeF_complement M U U₀) (e : G ≃* G) :
    is_typeF_complement (M.map e.toMonoidHom)
      (U.map e.toMonoidHom) (U₀.map e.toMonoidHom) := by
  have hFcore := Fitting_core_map_mulEquiv M e
  refine ⟨Subgroup.map_mono h.1, ?_, ?_, ?_⟩
  · calc
      Monoid.exponent (U₀.map e.toMonoidHom) = Monoid.exponent U₀ :=
        (Monoid.exponent_eq_of_mulEquiv (e.subgroupMap U₀)).symm
      _ = Monoid.exponent U := h.2.1
      _ = Monoid.exponent (U.map e.toMonoidHom) :=
        Monoid.exponent_eq_of_mulEquiv (e.subgroupMap U)
  · have hmap := semidirect_map_mulEquiv8 h.2.2.1 e
    rw [Subgroup.map_sup] at hmap
    rw [hFcore]
    exact hmap
  · let J : Subgroup G := Fitting_core M ⊔ U₀
    let J' : Subgroup G :=
      Fitting_core (M.map e.toMonoidHom) ⊔ U₀.map e.toMonoidHom
    have hJ : J.map e.toMonoidHom = J' := by
      dsimp only [J, J']
      rw [Subgroup.map_sup, hFcore]
    let eJ : J ≃* J' :=
      (e.subgroupMap J).trans (MulEquiv.subgroupCongr hJ)
    have hmap := frobenius_map_mulEquiv8 h.2.2.2 eJ
    have hFmap :
        ((Fitting_core M).subgroupOf J).map eJ.toMonoidHom =
          (Fitting_core (M.map e.toMonoidHom)).subgroupOf J' := by
      ext y
      rw [Subgroup.mem_map_equiv]
      change e.symm (y : G) ∈ Fitting_core M ↔
        (y : G) ∈ Fitting_core (M.map e.toMonoidHom)
      rw [hFcore, Subgroup.mem_map_equiv]
    have hU₀map :
        (U₀.subgroupOf J).map eJ.toMonoidHom =
          (U₀.map e.toMonoidHom).subgroupOf J' := by
      ext y
      rw [Subgroup.mem_map_equiv]
      change e.symm (y : G) ∈ U₀ ↔
        (y : G) ∈ U₀.map e.toMonoidHom
      rw [Subgroup.mem_map_equiv]
    rw [hFmap, hU₀map] at hmap
    exact hmap

/-- The type-F predicate commutes with an ambient automorphism. -/
theorem ofTypeF_map_mulEquiv8
    {M U : Subgroup G} (h : of_typeF M U) (e : G ≃* G) :
    of_typeF (M.map e.toMonoidHom) (U.map e.toMonoidHom) := by
  have hFcore := Fitting_core_map_mulEquiv M e
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hFcore]
    exact (not_congr (Subgroup.map_eq_bot_iff_of_injective
      (Fitting_core M) e.injective)).mpr h.1
  · exact (not_congr
      (Subgroup.map_eq_bot_iff_of_injective U e.injective)).mpr h.2.1
  · have hmap := semidirect_map_mulEquiv8 h.2.2.1 e
    rw [hFcore]
    exact hmap
  · obtain ⟨U₁, hU₁⟩ := h.2.2.2.1
    exact ⟨U₁.map e.toMonoidHom,
      isTypeFInertia_map_mulEquiv8 hU₁ e⟩
  · obtain ⟨U₀, hU₀⟩ := h.2.2.2.2
    exact ⟨U₀.map e.toMonoidHom,
      isTypeFComplement_map_mulEquiv8 hU₀ e⟩

end FTContextInternal

end

end Submission.OddOrder.PF
