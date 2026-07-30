import Submission.OddOrder.BG.Section16.SummaryA
import Submission.OddOrder.MathlibSupport.AbelianPGroupRankThree
import Mathlib.GroupTheory.Exponent

/-!
# Bender--Glauberman Section 16: summary B

This phase packages the five conclusions of summary B for a kappa
complement.  The implementation is independent of the former combined
Section 16 draft and is based on the current Section 14--16 interfaces.
-/

namespace Submission.OddOrder.BG.Section16

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section09
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.BG.Section12
open Submission.OddOrder.BG.Section13
open Submission.OddOrder.BG.Section14
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.PF
open scoped Pointwise IsMulCommutative commutatorElement

noncomputable section

universe u

variable {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]

/-- The five numbered clauses of `BGsummaryB`. -/
structure BGSummaryB (M U : Subgroup G) : Prop where
  sylow_abelian_rank_le_two :
    ∀ (p : ℕ) [Fact p.Prime] (S : Sylow p U),
      IsMulCommutative (S : Subgroup U) ∧
        Group.rank (S : Subgroup U) ≤ 2
  fixedPointGenerated_abelian :
    IsMulCommutative (sigmaFixedPointGenerated M U)
  support_avoiding_exponent_witness :
    ∃ U₀ : Subgroup G, U₀ ≤ U ∧
      Monoid.exponent U₀ = Monoid.exponent U ∧
      Disjoint (U₀ : Set G) (FTsupport M)
  subgroup_centralizer_unique : ∀ {X : Subgroup G},
    X ≤ U → X ≠ ⊥ →
      centralizerWithin (sigmaCore M) X ≠ ⊥ →
      minSimple_max_groups_of (G := G)
        ((Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) = {M}
  support_difference_normalizedTI :
    FTsupport M ≠ FTsupport1 M →
      IsNormalizedTI (FTsupport M \ FTsupport1 M) ⊤ M

/-! ## The exponent witness -/

/-- A Frobenius complement to `sigmaCore M` contains no element of the
Section 16 support. -/
private theorem frobeniusComplement_disjoint_support
    {M V : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hFrob :
      IsFrobeniusDecomposition
        ((sigmaCore M).subgroupOf (sigmaCore M ⊔ V))
        (V.subgroupOf (sigmaCore M ⊔ V))) :
    Disjoint (V : Set G) (FTsupport M) := by
  classical
  rw [Set.disjoint_left]
  intro v hvV hvSupport
  simp only [FTsupport, ftSupport, Set.mem_iUnion] at hvSupport
  obtain ⟨x, hxCore, hvCentral⟩ := hvSupport
  have hxSigma : x ∈ sigmaCore M := by
    rw [← def_FTcore hM]
    exact hxCore.1
  let H : Subgroup G := sigmaCore M ⊔ V
  let vH : H :=
    ⟨v, (le_sup_right : V ≤ sigmaCore M ⊔ V) hvV⟩
  let xH : H :=
    ⟨x, (le_sup_left : sigmaCore M ≤ sigmaCore M ⊔ V) hxSigma⟩
  let vV : V.subgroupOf H := ⟨vH, hvV⟩
  let xSigma : (sigmaCore M).subgroupOf H := ⟨xH, hxSigma⟩
  have hvNe : vV ≠ 1 := by
    intro hvOne
    apply hvCentral.2
    exact congrArg (fun z : V.subgroupOf H ↦ ((z : H) : G)) hvOne
  have hxv : x * v = v * x :=
    hvCentral.1.2 x (Subgroup.mem_zpowers x)
  have hfixed :
      (vV : H) * (xSigma : H) * (vV : H)⁻¹ = xSigma := by
    apply Subtype.ext
    change v * x * v⁻¹ = x
    calc
      v * x * v⁻¹ = x * v * v⁻¹ := by rw [← hxv]
      _ = x := by simp
  have hxOne : xSigma = 1 :=
    hFrob.fixedPointFree vV hvNe xSigma hfixed
  apply hxCore.2
  exact congrArg
    (fun z : (sigmaCore M).subgroupOf H ↦ ((z : H) : G)) hxOne

/-! ## Sylow subgroups of the complement -/

/-- Sylow subgroups of the Hall complement are abelian and have rank at most
two. -/
private theorem complementSylow_abelian_rank_le_two
    {M U K : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hCompl : KappaComplement M U K)
    (p : ℕ) [Fact p.Prime] (S : Sylow p U) :
    IsMulCommutative (S : Subgroup U) ∧
      Group.rank (S : Subgroup U) ≤ 2 := by
  classical
  let P : Subgroup G := ambientSylow U S
  have hPU : P ≤ U := Subgroup.map_subtype_le (S : Subgroup U)
  have hPM : P ≤ M := hPU.trans hCompl.U_le_M
  have hPgroup : IsPGroup p P := S.isPGroup'.map U.subtype
  have hUPrimes :
      IsPiNumber (sigmaKappaPrimes M)ᶜ (Nat.card U) := by
    rw [← MathlibSupport.natCard_subgroupOf_eq hCompl.U_le_M]
    exact hCompl.hall_U.isPiNumber_card
  have hPPrimes :
      IsPiNumber (sigmaKappaPrimes M)ᶜ (Nat.card P) :=
    hUPrimes.of_dvd (Subgroup.card_dvd_of_le hPU)
  have hPSigmaCompl :
      IsPiNumber (sigmaPrimes M)ᶜ (Nat.card P) := by
    apply hPPrimes.mono
    intro q hq qSigma
    exact hq (Or.inl qSigma)
  have hPabelian : IsMulCommutative P :=
    sigma'_nil_abelian hM hPM hPSigmaCompl hPgroup.isNilpotent
  let e : (S : Subgroup U) ≃* P :=
    (S : Subgroup U).equivMapOfInjective U.subtype U.subtype_injective
  have hSabelian : IsMulCommutative (S : Subgroup U) := by
    rw [isMulCommutative_iff]
    intro a b
    apply e.injective
    simpa only [map_mul] using
      (isMulCommutative_iff.mp hPabelian (e a) (e b))
  refine ⟨hSabelian, ?_⟩
  by_contra hle
  have hRankThree : 3 ≤ Group.rank (S : Subgroup U) := by omega
  obtain ⟨E, hES, hErank⟩ :=
    exists_elementaryAbelian_rank_three_le_of_group_rank
      (S : Subgroup U) S.isPGroup' hSabelian hRankThree
  let EG : Subgroup G := E.map U.subtype
  have hEGP : EG ≤ P := Subgroup.map_mono hES
  have hEGM : EG ≤ M := hEGP.trans hPM
  have hEG : IsElementaryAbelianOfRank p 3 EG :=
    hErank.map_of_injective U.subtype U.subtype_injective
  have hpSigma : p ∈ sigmaPrimes M :=
    alpha_sub_sigma hM ⟨Fact.out, EG, hEGM, hEG⟩
  have hSnontrivial : (S : Subgroup U) ≠ ⊥ := by
    intro hSbot
    have hrankZero : Group.rank (S : Subgroup U) = 0 := by
      rw [hSbot]
      exact Group.rank_eq_zero _
    omega
  have hpCardP : p ∣ Nat.card P := by
    change p ∣ Nat.card ((S : Subgroup U).map U.subtype)
    rw [Subgroup.card_map_of_injective U.subtype_injective]
    exact S.isPGroup'.card_eq_or_dvd.resolve_left
      ((S : Subgroup U).one_lt_card_iff_ne_bot.mpr hSnontrivial).ne'
  exact hPPrimes Fact.out hpCardP (Or.inl hpSigma)

/-! ## Transport utilities for the normalized-TI clause -/

private theorem ftDerived_le_ambient (M : Subgroup G) : FTder M ≤ M := by
  by_cases hType : FTtype M = 1
  · simpa [FTder, ftDerived, hType]
  · rw [show FTder M = derivedWithin M by
      simp [FTder, ftDerived, hType]]
    unfold derivedWithin
    exact Subgroup.map_subtype_le (_root_.commutator M)

omit [Finite G] [IsMinSimpleOddGroup G] in
private theorem map_equiv_then_inverse
    (X : Subgroup G) (e : G ≃* G) :
    (X.map e.toMonoidHom).map e.symm.toMonoidHom = X := by
  exact
    (Subgroup.map_symm_eq_iff_map_eq X
      (H := X.map e.toMonoidHom) (e := e)).2 rfl

omit [Finite G] [IsMinSimpleOddGroup G] in
private theorem centralizer_map_equiv
    (X : Subgroup G) (e : G ≃* G) :
    (Subgroup.centralizer (X : Set G)).map e.toMonoidHom =
      Subgroup.centralizer (X.map e.toMonoidHom : Set G) := by
  ext y
  rw [Subgroup.mem_map_equiv]
  constructor
  · intro hy
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro z hz
    have hzBack : e.symm z ∈ X := Subgroup.mem_map_equiv.mp hz
    simpa using congrArg e (hy (e.symm z) hzBack)
  · intro hy
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro z hz
    have hzForward : e z ∈ X.map e.toMonoidHom :=
      Subgroup.mem_map_equiv.mpr (by simpa using hz)
    simpa using congrArg e.symm (hy (e z) hzForward)

private theorem primeSetComplementComponent_conj
    (pi : Set ℕ) (x z : G) :
    primeSetComplementComponent pi ((MulAut.conj z) x) =
      (MulAut.conj z) (primeSetComplementComponent pi x) := by
  unfold primeSetComplementComponent
  rw [primeSetComponent_conj]
  simp only [map_mul, map_inv]

private theorem mem_normalHall_of_pi_order
    {K : Type u} [Group K] [Finite K]
    {pi : Set ℕ} {H : Subgroup K}
    (hNormal : H.Normal) (hHall : IsHall pi H)
    {x : K} (hxPi : IsPiNumber pi (orderOf x)) :
    x ∈ H := by
  letI : H.Normal := hNormal
  have hcoprime : (orderOf x).Coprime H.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpOrder hpIndex
    exact hHall.isPiNumber_index hp hpIndex (hxPi hp hpOrder)
  let q : K →* K ⧸ H := QuotientGroup.mk' H
  have hOrderX : orderOf (q x) ∣ orderOf x := orderOf_map_dvd q x
  have hOrderIndex : orderOf (q x) ∣ H.index := by
    simpa only [H.index_eq_card] using orderOf_dvd_natCard (q x)
  have hOrderOne : orderOf (q x) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcoprime hOrderX hOrderIndex
  apply (QuotientGroup.eq_one_iff x).mp
  simpa [q] using orderOf_eq_one_iff.mp hOrderOne

/-! ## The unique maximal subgroup attached to an outer support element -/

private theorem supportDifference_uniqueCentralizer
    {M U K : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hCompl : KappaComplement M U K)
    {y : G} (hy : y ∈ FTsupport M \ FTsupport1 M) :
    minSimple_max_groups_of (G := G)
      (Subgroup.centralizer
        (Subgroup.zpowers (sigmaComplementComponent M y) : Set G) :
          Set G) = {M} := by
  classical
  have hDerived := sdprod_FTder hM hCompl
  have hDerivedM : FTder M ≤ M := ftDerived_le_ambient M
  have hUCompl :
      IsPiNumber (sigmaPrimes M)ᶜ (Nat.card U) := by
    rw [← MathlibSupport.natCard_subgroupOf_eq hCompl.U_le_M]
    apply hCompl.hall_U.isPiNumber_card.mono
    intro p hp pSigma
    exact hp (Or.inl pSigma)
  have hUHallDerived :
      IsHall (sigmaPrimes M)ᶜ (U.subgroupOf (FTder M)) := by
    constructor
    · rw [MathlibSupport.natCard_subgroupOf_eq hDerived.2.1]
      exact hUCompl
    · rw [hDerived.2.2.2.index_eq_card,
        MathlibSupport.natCard_subgroupOf_eq hDerived.1]
      simpa only [compl_compl] using sigmaCore_isPiNumber M
  have hDerivedSolvable : IsSolvable (FTder M) := by
    letI : IsSolvable M := mmax_sol hM
    exact solvable_of_solvable_injective
      (f := Subgroup.inclusion hDerivedM)
      (Subgroup.inclusion_injective hDerivedM)
  have hKappa := kappa_structure hM hCompl

  change y ∈ FTsupport M ∧ y ∉ FTsupport1 M at hy
  have hySupport := hy.1
  simp only [FTsupport, ftSupport, Set.mem_iUnion] at hySupport
  obtain ⟨x, hxCore, hyCentral⟩ := hySupport
  have hxSigma : x ∈ sigmaCore M := by
    rw [← def_FTcore hM]
    exact hxCore.1
  have hyM : y ∈ M := (FTsupp_sub M hy.1).1
  have hyDerived : y ∈ FTder M := hyCentral.1.1

  let u : G := sigmaComplementComponent M y
  have huPower : u ∈ Subgroup.zpowers y := by
    have hsPower : sigmaComponent M y ∈ Subgroup.zpowers y :=
      (primeSetComponent_spec (sigmaPrimes M) y).1
    change (sigmaComponent M y)⁻¹ * y ∈ Subgroup.zpowers y
    exact (Subgroup.zpowers y).mul_mem
      ((Subgroup.zpowers y).inv_mem hsPower)
      (Subgroup.mem_zpowers y)
  have huDerived : u ∈ FTder M :=
    (Subgroup.zpowers_le.mpr hyDerived) huPower
  have huNe : u ≠ 1 := by
    intro huOne
    have hComponent : sigmaComponent M y = y := by
      have hFactor := sigmaComponent_mul_complement M y
      simpa [u, huOne] using hFactor
    have hySigmaOrder :
        IsPiNumber (sigmaPrimes M) (orderOf y) := by
      rw [← hComponent]
      exact sigmaComponent_isPiNumber M y
    let yM : M := ⟨y, hyM⟩
    have hySigmaOrderM :
        IsPiNumber (sigmaPrimes M) (orderOf yM) := by
      simpa [yM] using hySigmaOrder
    have hySigmaM :
        yM ∈ (sigmaCore M).subgroupOf M :=
      mem_normalHall_of_pi_order (sigmaCore_normal M) (Msigma_Hall hM)
        hySigmaOrderM
    apply hy.2
    refine ⟨?_, hyCentral.2⟩
    rw [def_FTcore hM]
    exact hySigmaM

  let X : Subgroup G := Subgroup.zpowers u
  have hXDerived : X ≤ FTder M := Subgroup.zpowers_le.mpr huDerived
  have hXCompl :
      IsPiNumber (sigmaPrimes M)ᶜ (Nat.card X) := by
    simpa [X, u, Nat.card_zpowers] using
      sigmaComplementComponent_isPiNumber M y
  obtain ⟨z, hXUconj, _hUconjDerived, _hHallConj,
      _hFittingCard, _hFittingDvd, _hTransport⟩ :=
    exists_ambient_isHall_map_conj_ge_of_isSolvable
      (K := FTder M) (A := X) (H := U)
      hXDerived hDerived.2.1 hDerivedSolvable hXCompl hUHallDerived

  let c : G ≃* G := MulAut.conj (z : G)
  let e : G ≃* G := c.symm
  let Xc : Subgroup G := X.map e.toMonoidHom
  have hXcU : Xc ≤ U := by
    have hMapped := Subgroup.map_mono (f := e.toMonoidHom) hXUconj
    change X.map c.symm.toMonoidHom ≤
      (U.map c.toMonoidHom).map c.symm.toMonoidHom at hMapped
    rw [map_equiv_then_inverse U c] at hMapped
    exact hMapped
  have hXcNe : Xc ≠ ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective X e.injective).not.mpr
      (Subgroup.zpowers_ne_bot.mpr huNe)

  have hzM : (z : G) ∈ M := hDerivedM z.property
  have hSigmaNormalized :
      M ≤ Subgroup.normalizer (sigmaCore M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (sigmaCore_le M)).mp
      (sigmaCore_normal M)
  have hxSigmaConj : e x ∈ sigmaCore M := by
    have hxConj :=
      ((Subgroup.mem_set_normalizer_iff''.mp
        (hSigmaNormalized hzM)) x).mp hxSigma
    simpa [e, c, MulAut.conj_apply] using hxConj
  have hxy : Commute x y :=
    hyCentral.1.2 x (Subgroup.mem_zpowers x)
  have hxu : Commute x u := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp huPower
    rw [← hn]
    exact hxy.zpow_right n
  have hxCentralConj : e x ∈ centralizerWithin (sigmaCore M) Xc := by
    refine ⟨hxSigmaConj, ?_⟩
    intro w hw
    have hwBack : e.symm w ∈ X := Subgroup.mem_map_equiv.mp hw
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hwBack
    have hcomm := congrArg e ((hxu.zpow_right n).symm.eq)
    rw [hn] at hcomm
    simpa using hcomm
  have hxConjNe : e x ≠ 1 := by
    intro hxOne
    apply hxCore.2
    apply e.injective
    simpa using hxOne
  have hCentralConjNe :
      centralizerWithin (sigmaCore M) Xc ≠ ⊥ := by
    intro hbot
    have hxBot : e x ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact hxCentralConj
    exact hxConjNe (Subgroup.mem_bot.mp hxBot)

  have hControl := hKappa.U_subgroup_control hXcU hXcNe hCentralConjNe
  have hXBack : Xc.map e.symm.toMonoidHom = X := by
    exact map_equiv_then_inverse X e
  have hCentralizerBack :
      (Subgroup.centralizer (Xc : Set G)).map e.symm.toMonoidHom =
        Subgroup.centralizer (X : Set G) := by
    rw [centralizer_map_equiv, hXBack]
  have hMconj : M.map c.toMonoidHom = M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hzM)
  have hMBack : M.map e.symm.toMonoidHom = M := by
    simpa [e] using hMconj
  have hUniqueBack := def_uniq_mmaxJ e.symm hControl.1
  rw [hCentralizerBack, hMBack] at hUniqueBack
  exact hUniqueBack

private theorem supportDifference_normalizedTI
    {M U K : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hCompl : KappaComplement M U K)
    (hDiff : FTsupport M ≠ FTsupport1 M) :
    IsNormalizedTI (FTsupport M \ FTsupport1 M) ⊤ M := by
  classical
  let B : Set G := FTsupport M \ FTsupport1 M
  have hBNonempty : B.Nonempty := by
    have hNotSubset : ¬ FTsupport M ⊆ FTsupport1 M := by
      intro hSubset
      apply hDiff
      exact Set.Subset.antisymm hSubset (FTsupp1_sub hM)
    obtain ⟨y, hySupport, hyNotCore⟩ := Set.not_subset.mp hNotSubset
    exact ⟨y, hySupport, hyNotCore⟩
  have hUnique : ∀ {y : G}, y ∈ B →
      minSimple_max_groups_of (G := G)
        (Subgroup.centralizer
          (Subgroup.zpowers (sigmaComplementComponent M y) : Set G) :
            Set G) = {M} := by
    intro y hy
    exact supportDifference_uniqueCentralizer hM hCompl hy

  apply isNormalizedTI_iff_mem_conj.mpr
  refine ⟨hBNonempty, le_top, ?_⟩
  intro y hy g _hgTop
  constructor
  · intro hyConj
    let c : G ≃* G := MulAut.conj g⁻¹
    let u : G := sigmaComplementComponent M y
    let yg : G := g⁻¹ * y * g
    let ug : G := sigmaComplementComponent M yg
    let X : Subgroup G := Subgroup.zpowers u
    let Xg : Subgroup G := Subgroup.zpowers ug
    have hygB : yg ∈ B := by
      change g⁻¹ * y * g ∈ FTsupport M \ FTsupport1 M
      exact hyConj
    have huConj : ug = c u := by
      simpa [c, u, yg, ug, sigmaComplementComponent,
        MulAut.conj_apply] using
        (primeSetComplementComponent_conj
          (sigmaPrimes M) y g⁻¹)
    have hXmap : X.map c.toMonoidHom = Xg := by
      change (Subgroup.zpowers u).map c.toMonoidHom = Subgroup.zpowers ug
      rw [MonoidHom.map_zpowers]
      change Subgroup.zpowers (c u) = Subgroup.zpowers ug
      rw [huConj]
    have hCentralizerMap :
        (Subgroup.centralizer (X : Set G)).map c.toMonoidHom =
          Subgroup.centralizer (Xg : Set G) := by
      rw [centralizer_map_equiv, hXmap]
    have hTransport := def_uniq_mmaxJ c (hUnique hy)
    rw [hCentralizerMap, hUnique hygB] at hTransport
    have hMmap : M.map c.toMonoidHom = M :=
      (Set.singleton_injective hTransport).symm
    have hginvNormalizer : g⁻¹ ∈ Subgroup.normalizer (M : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hMmap
    have hginvM : g⁻¹ ∈ M := by
      rwa [norm_mmax hM] at hginvNormalizer
    simpa using M.inv_mem hginvM
  · intro hgM
    change y ∈ FTsupport M ∧ y ∉ FTsupport1 M at hy
    change g⁻¹ * y * g ∈ FTsupport M ∧
      g⁻¹ * y * g ∉ FTsupport1 M
    refine ⟨((Subgroup.mem_set_normalizer_iff''.mp
      (FTsupp_norm M hgM)) y).mp hy.1, ?_⟩
    intro hyCoreConj
    apply hy.2
    exact ((Subgroup.mem_set_normalizer_iff''.mp
      (FTsupp1_norm M hgM)) y).mpr hyCoreConj

/-- `BGsection16.v: BGsummaryB`. -/
theorem BGsummaryB
    {M U K : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hCompl : KappaComplement M U K) :
    BGSummaryB M U := by
  classical
  have hKappa := kappa_structure hM hCompl
  refine
    { sylow_abelian_rank_le_two := ?_
      fixedPointGenerated_abelian := hKappa.fixedPointGenerated_abelian
      support_avoiding_exponent_witness := ?_
      subgroup_centralizer_unique := ?_
      support_difference_normalizedTI := ?_ }
  · intro p _hp S
    exact complementSylow_abelian_rank_le_two hM hCompl p S
  · by_cases hUbot : U = ⊥
    · subst U
      refine ⟨⊥, bot_le, rfl, ?_⟩
      rw [Set.disjoint_left]
      intro x hxBot hxSupport
      exact (FTsupp_sub M hxSupport).2 (Subgroup.mem_bot.mp hxBot)
    · obtain ⟨V, hVU, hExponent, _hSemidirect, hFrobenius⟩ :=
        hKappa.exponent_frobenius hUbot
      exact ⟨V, hVU, hExponent,
        frobeniusComplement_disjoint_support hM hFrobenius⟩
  · intro X hXU hXne hCentralizer
    exact (hKappa.U_subgroup_control hXU hXne hCentralizer).1
  · intro hDiff
    exact supportDifference_normalizedTI hM hCompl hDiff

end

end Submission.OddOrder.BG.Section16
