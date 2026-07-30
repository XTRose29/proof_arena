import Submission.OddOrder.BG.Section16.TypeSpecInfrastructure

/-!
# The semantic specification of `FTtype`

This module proves Lemma 16.1 by constructing the five semantic witnesses from
the numerical value of `FTtype`, and by recovering that value from any such
witness.  The routine Hall, Sylow, quotient, and type-P facts are supplied by
`TypeSpecInfrastructure`.
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
open TypeSpecInternal
open scoped Pointwise IsMulCommutative commutatorElement

noncomputable section

universe u

variable {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]

namespace FTTypeSpecInternal

private theorem typeF_implies_typeFMaximal
    {M U : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hTypeF : of_typeF M U) :
    M ∈ typeFMaximalSubgroups (G := G) := by
  classical
  rcases hTypeF with
    ⟨hFne, hUne, hsd, _, U₀, hU₀U, hexp, hsd₀, hfrob⟩
  by_contra hnotF
  have hMP : M ∈ typePMaximalSubgroups (G := G) := ⟨hM, hnotF⟩
  obtain ⟨p, hpKappa⟩ := (PtypeP hM).1 hMP
  have hpM := kappa_pi hpKappa
  have hpF : ¬ p ∣ Nat.card (Fitting_core M) := by
    intro hpF
    exact (kappa_sigma' M hpKappa)
      ((sigmaCore_isPiNumber M).of_dvd
        (Subgroup.card_dvd_of_le (Fcore_sub_Msigma hM)) hpM.1 hpF)
  have hcardM : Nat.card M =
      Nat.card (Fitting_core M) * Nat.card U := by
    have hFcard : Nat.card ((Fitting_core M).subgroupOf M) =
        Nat.card (Fitting_core M) :=
      MathlibSupport.natCard_subgroupOf_eq hsd.1
    have hUcard : Nat.card (U.subgroupOf M) = Nat.card U :=
      MathlibSupport.natCard_subgroupOf_eq hsd.2.1
    calc
      Nat.card M = Nat.card ((Fitting_core M).subgroupOf M) *
          Nat.card (U.subgroupOf M) := hsd.2.2.2.card_mul.symm
      _ = Nat.card (Fitting_core M) * Nat.card U := by
        rw [hFcard, hUcard]
  have hpU : p ∣ Nat.card U := by
    rw [hcardM] at hpM
    exact (hpM.1.dvd_mul.mp hpM.2).resolve_left hpF
  letI : Fact p.Prime := ⟨hpM.1⟩
  obtain ⟨u, huOrder⟩ := exists_prime_orderOf_dvd_card' (G := U) p hpU
  have hpExpU : p ∣ Monoid.exponent U := by
    rw [← huOrder]
    exact Monoid.order_dvd_exponent u
  have hpU₀ : p ∣ Nat.card U₀ := by
    have hpExpU₀ : p ∣ Monoid.exponent U₀ := by
      rw [hexp]
      exact hpExpU
    exact hpExpU₀.trans Group.exponent_dvd_nat_card
  obtain ⟨X, hXU₀, hXline⟩ :=
    exists_rankOneLineIn_of_primeSupport16
      (show p ∈ primeSupport (Nat.card U₀) from ⟨hpM.1, hpU₀⟩)
  have hXU : X ≤ U := hXU₀.trans hU₀U
  have hXkappa : IsPiNumber (kappaPrimes M) (Nat.card X) := by
    simpa [hXline.card_eq] using
      (show IsPiNumber (kappaPrimes M) p from
        fun q hq hqp ↦ by
          have hqpEq : q = p :=
            (Nat.prime_dvd_prime_iff_eq hq hpM.1).mp hqp
          simpa [hqpEq] using hpKappa)
  have hXM : X ≤ M := hXU.trans hsd.2.1
  obtain ⟨K, hXK, hKM, hHallK⟩ :=
    MathlibSupport.exists_ambient_isHall_ge_of_isSolvable
      hXM (mmax_sol hM)
      (kappaPrimes M) hXkappa
  obtain ⟨V, hCompl⟩ := ex_kappa_compl hM hKM hHallK
  have hKne : K ≠ ⊥ := by
    intro hKbot
    exact hXline.ne_bot (le_bot_iff.mp (hXK.trans_eq hKbot))
  have hC := BGsummaryC hM hCompl hKne
  obtain ⟨x, hx1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp hXline.ne_bot
  obtain ⟨z, hz1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp hC.partner_ne_bot
  have hxX : (x : G) ∈ X := x.property
  have hzPartner : (z : G) ∈ pTypePartner M K := z.property
  have hxU₀ : (x : G) ∈ U₀ := hXU₀ hxX
  have hzF : (z : G) ∈ Fitting_core M := hC.partner_le_Fcore hzPartner
  have hzx : Commute (z : G) (x : G) :=
    (hC.join_direct.commute
      ⟨x, hXK hxX⟩ ⟨z, hzPartner⟩).symm
  let xU₀ : U₀.subgroupOf (Fitting_core M ⊔ U₀) :=
    ⟨⟨x, (le_sup_right : U₀ ≤ Fitting_core M ⊔ U₀) hxU₀⟩, hxU₀⟩
  let zF : (Fitting_core M).subgroupOf (Fitting_core M ⊔ U₀) :=
    ⟨⟨z, (le_sup_left : Fitting_core M ≤ Fitting_core M ⊔ U₀) hzF⟩,
      hzF⟩
  have hxU₀ne : xU₀ ≠ 1 := by
    intro hx
    apply hx1
    apply Subtype.ext
    exact congrArg
      (fun y : U₀.subgroupOf (Fitting_core M ⊔ U₀) ↦ (y : G)) hx
  have hzFix : xU₀.1 * zF.1 * xU₀.1⁻¹ = zF.1 := by
    apply Subtype.ext
    change (x : G) * (z : G) * (x : G)⁻¹ = (z : G)
    rw [hzx.eq.symm]
    simp
  have hzOne := hfrob.fixedPointFree xU₀ hxU₀ne zF hzFix
  apply hz1
  apply Subtype.ext
  exact congrArg
    (fun y : (Fitting_core M).subgroupOf (Fitting_core M ⊔ U₀) ↦
      (y : G)) hzOne

private theorem fcore_normalizedTI_of_fitting_normalizedTI
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hTI : IsNormalizedTI
      (subgroupNonidentity (fittingWithin M)) ⊤ M) :
    IsNormalizedTI (subgroupNonidentity (Fitting_core M)) ⊤ M := by
  apply isNormalizedTI_iff_mem_conj.mpr
  refine ⟨?_, le_top, ?_⟩
  · obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (Fcore_structure hM).Fcore_ne_bot
    exact ⟨(x : G), x.property,
      fun hx1 ↦ hx (Subtype.ext hx1)⟩
  · intro x hx g hg
    constructor
    · intro hxg
      have hxFit : x ∈ subgroupNonidentity (fittingWithin M) :=
        ⟨Fcore_sub_Fitting M hx.1, hx.2⟩
      have hxgFit : g⁻¹ * x * g ∈
          subgroupNonidentity (fittingWithin M) := by
        exact ⟨Fcore_sub_Fitting M hxg.1, by
          intro heq
          exact hx.2 (by
            simpa [mul_assoc] using
              congrArg (fun y ↦ g * y * g⁻¹) heq)⟩
      exact ((isNormalizedTI_iff_mem_conj.mp hTI).2.2 hxFit hg).1 hxgFit
    · intro hgM
      refine ⟨?_, ?_⟩
      · have hnorm : g ∈ Subgroup.normalizer
            (Fitting_core M : Set G) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer
            (Fcore_sub M)).1 (Fcore_normal M) hgM
        exact ((Subgroup.mem_set_normalizer_iff''.mp hnorm) x).1 hx.1
      · intro heq
        exact hx.2 (by
          simpa [mul_assoc] using
            congrArg (fun y ↦ g * y * g⁻¹) heq)

private theorem exists_nontrivial_fitting_intersection
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hnonTI : ¬ IsNormalizedTI
      (subgroupNonidentity (fittingWithin M)) ⊤ M) :
    ∃ g : G, g ∉ M ∧ nonTIFittingIntersection M g ≠ ⊥ := by
  classical
  by_contra hnone
  push_neg at hnone
  apply hnonTI
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (Fcore_structure hM).Fcore_ne_bot
    exact ⟨(x : G), Fcore_sub_Fitting M x.property,
      fun hx ↦ hx1 (Subtype.ext hx)⟩
  · intro g hgM
    refine ⟨trivial, ?_⟩
    apply Subgroup.mem_set_normalizer_iff''.mpr
    intro x
    have hgNorm : g ∈ Subgroup.normalizer
        (fittingWithin M : Set G) :=
      fittingWithin_le_normalizer M hgM
    constructor
    · intro hx
      refine ⟨((Subgroup.mem_set_normalizer_iff''.mp hgNorm) x).1 hx.1,
        ?_⟩
      intro heq
      exact hx.2 (by
        simpa [mul_assoc] using
          congrArg (fun z ↦ g * z * g⁻¹) heq)
    · intro hxg
      refine ⟨((Subgroup.mem_set_normalizer_iff''.mp hgNorm) x).2 hxg.1,
        ?_⟩
      intro hx1
      subst x
      simpa using hxg.2
  · intro g _ hoverlap
    by_contra hgM
    have hginvM : g⁻¹ ∉ M := by
      intro hginv
      exact hgM (by simpa using M.inv_mem hginv)
    rcases hoverlap with ⟨_, hxA, a, haA, rfl⟩
    have hmeet : g⁻¹ * a * g ∈
        nonTIFittingIntersection M g⁻¹ := by
      refine ⟨hxA.1, ?_⟩
      rw [conjugateSubgroup15]
      exact ⟨a, haA.1, by simp⟩
    have hconjNe : g⁻¹ * a * g ≠ 1 := by
      intro heq
      apply haA.2
      simpa [mul_assoc] using
        congrArg (fun z ↦ g * z * g⁻¹) heq
    have hmeetNe : nonTIFittingIntersection M g⁻¹ ≠ ⊥ := by
      rw [Subgroup.ne_bot_iff_exists_ne_one]
      refine ⟨⟨g⁻¹ * a * g, hmeet⟩, ?_⟩
      intro heq
      exact hconjNe (congrArg Subtype.val heq)
    exact hmeetNe (hnone g⁻¹ hginvM)

private theorem exists_nonTI_fcore_structure
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hnotTI : ¬ IsNormalizedTI
      (subgroupNonidentity (Fitting_core M)) ⊤ M) :
    ∃ g : G, g ∉ M ∧ NonTIFittingStructure M g := by
  have hnotFittingTI : ¬ IsNormalizedTI
      (subgroupNonidentity (fittingWithin M)) ⊤ M := by
    intro hTI
    exact hnotTI (fcore_normalizedTI_of_fitting_normalizedTI hM hTI)
  obtain ⟨g, hg, hmeet⟩ :=
    exists_nontrivial_fitting_intersection hM hnotFittingTI
  exact ⟨g, hg, nonTI_Fitting_structure hM hg hmeet⟩

private theorem exists_typeI_of_FTtype_one
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hF : M ∈ typeFMaximalSubgroups (G := G)) :
    ∃ U : Subgroup G, of_typeI M U := by
  classical
  obtain ⟨U, K, hCompl⟩ := kappa_witness hM
  have hKbot : K = ⊥ := (trivgFmax hM hCompl).1 hF
  have hUne : U ≠ ⊥ := (FmaxP hM hCompl).1 hF |>.2
  have hFcoreEq : Fitting_core M = sigmaCore M :=
    (Fcore_eq_Msigma hM).2
      (notP1type_Msigma_nil (Or.inl hF))
  have htype : FTtype M = 1 := (FTtype_Fmax hM).1 hF
  have hkappa := kappa_structure hM hCompl
  have hsd : IsInternalSemidirectProductIn (Fitting_core M) U M := by
    simpa [hFcoreEq, FTder, ftDerived, htype] using
      sdprod_FTder hM hCompl
  let U₁ : Subgroup G := sigmaFixedPointGenerated M U
  have hU₁U : U₁ ≤ U := by
    dsimp only [U₁]
    rw [sigmaFixedPointGenerated]
    apply (Subgroup.closure_le _).mpr
    rintro y ⟨x, hxSigma, hx1, hy⟩
    exact (centralizerWithin_le_left _ _) hy
  have hU₁normal : (U₁.subgroupOf U).Normal :=
    sigmaFixedPointGenerated_normal_in_complement16 hM hCompl
  have hInertia : is_typeF_inertia M U U₁ := by
    refine ⟨hU₁U, hU₁normal,
      by simpa [U₁] using hkappa.fixedPointGenerated_abelian, ?_⟩
    intro x hx
    dsimp only [U₁]
    rw [sigmaFixedPointGenerated]
    intro y hy
    exact Subgroup.subset_closure
      ⟨x, hFcoreEq ▸ hx.1, hx.2, hy⟩
  obtain ⟨U₀, hU₀U, hexp, hsd₀, hfrob⟩ :=
    hkappa.exponent_frobenius hUne
  have hComplement : is_typeF_complement M U U₀ :=
    ⟨hU₀U, hexp, by
      rw [hFcoreEq]
      exact hsd₀,
      by
        rw [hFcoreEq]
        exact hfrob⟩
  refine ⟨U, ⟨⟨(Fcore_structure hM).Fcore_ne_bot, hUne, hsd,
    ⟨U₁, hInertia⟩, ⟨U₀, hComplement⟩⟩, ?_⟩⟩
  by_cases hTI : IsNormalizedTI
      (subgroupNonidentity (Fitting_core M)) ⊤ M
  · exact Or.inl hTI
  · obtain ⟨g, hg, hNonTI⟩ := exists_nonTI_fcore_structure hM hTI
    rcases hNonTI.final_case with hAb | hNonab
    · exact Or.inr (Or.inl ⟨hAb.core_abelian,
        ⟨hAb.rank_two, hAb.rank_at_most_two⟩⟩)
    · rcases hNonab.conclusion with hExp | hExtra
      · right
        right
        refine ⟨?_, ?_⟩
        · intro p hpF
          rw [← semidirect_quotient_exponent16 hsd]
          exact hExp p hpF
        · let p := Nat.card (nonTIFittingIntersection M g)
          letI : Fact p.Prime := ⟨hNonab.p_prime⟩
          have hpF : p ∈ primeSupport (Nat.card (Fitting_core M)) := by
            have hpCore : p ∣ Nat.card
                (pCore p (Fitting_core M)) :=
              pCore_isPGroup.card_eq_or_dvd.resolve_left (by
                intro hcard
                apply hNonab.pcore_nonabelian
                rw [Subgroup.card_eq_one.mp hcard]
                infer_instance)
            exact ⟨hNonab.p_prime,
              hpCore.trans
                (pCore p (Fitting_core M)).card_subgroup_dvd_card⟩
          exact ⟨p, hpF, hNonab.pPrimeCore_cyclic⟩
      · exact (hExtra.2.1.1.2 hF).elim

private theorem canonical_typeP
    {M V U₀ K : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hCompl : KappaComplement M U₀ K)
    (hKne : K ≠ ⊥)
    (hVnil : Group.IsNilpotent V)
    (hVDer : V ≤ derivedWithin M)
    (hKnormV : K ≤ Subgroup.normalizer (V : Set G))
    (hFsd : IsInternalSemidirectProductIn
      (Fitting_core M) V (derivedWithin M)) :
    of_typeP M V (pTypeJoin M K) K (pTypePartner M K)
      (BGsummaryC hM hCompl hKne).join_direct := by
  classical
  have hA := BGsummaryA hM hCompl
  have hC := BGsummaryC hM hCompl hKne
  have hKHallSupport :
      IsHall (primeSupport (Nat.card K)) (K.subgroupOf M) := by
    simpa [MathlibSupport.natCard_subgroupOf_eq hCompl.K_le_M] using
      isHall_primeSupport (K.subgroupOf M)
        hCompl.hall_K.coprime_card_index
  obtain ⟨Mstar, hEmbed⟩ :=
    Ptype_embedding ((trivgPmax hM hCompl).2 hKne)
      hCompl.K_le_M hCompl.hall_K
  have hcentralizer : ∀ x ∈ subgroupNonidentity K,
      elementCentralizerWithin (derivedWithin M) x =
        pTypePartner M K := by
    intro x hx
    apply le_antisymm
    · intro z hz
      have hzM : z ∈ centralizerWithin M (Subgroup.zpowers x) :=
        ⟨derivedWithin_le16_final M hz.1, hz.2⟩
      rw [hEmbed.cyclicStructure.centralizer_left hx.1 hx.2] at hzM
      obtain ⟨parts, hparts⟩ :=
        hC.join_direct.mulEquiv.surjective ⟨z, hzM⟩
      let k : G := parts.1
      let ks : G := parts.2
      have hksDer : ks ∈ derivedWithin M :=
        secondDerived_le_derived16 M
          (hC.partner_le_secondDerived parts.2.property)
      have hkDer : k ∈ derivedWithin M := by
        have hzEq : z = k * ks := congrArg Subtype.val hparts.symm
        rw [show k = z * ks⁻¹ by rw [hzEq]; group]
        exact (derivedWithin M).mul_mem hz.1
          ((derivedWithin M).inv_mem hksDer)
      have hkBot : k = 1 := by
        have hdis := hEmbed.derived_sdprod.2.2.2.disjoint
        let kM : M := ⟨k, derivedWithin_le16_final M hkDer⟩
        have hkBotM : kM ∈ (⊥ : Subgroup M) :=
          hdis.le_bot ⟨hkDer, parts.1.property⟩
        exact congrArg Subtype.val (Subgroup.mem_bot.mp hkBotM)
      have hzEq : z = k * ks := congrArg Subtype.val hparts.symm
      have hzEq' : z = ks := by simpa [hkBot] using hzEq
      exact hzEq'.symm ▸ parts.2.property
    · intro z hz
      refine mem_centralizerWithin.mpr
        ⟨secondDerived_le_derived16 M
          (hC.partner_le_secondDerived hz), ?_⟩
      intro y hy
      have hyK : y ∈ K := Subgroup.zpowers_le.mpr hx.1 hy
      exact (hC.join_direct.commute ⟨y, hyK⟩ ⟨z, hz⟩).eq
  exact
    ⟨⟨hA.K_cyclic, ⟨hCompl.K_le_M, hKHallSupport⟩, hKne,
        hEmbed.derived_sdprod⟩,
      ⟨hVnil, hVDer, hKnormV, hFsd⟩,
      ⟨hC.Fcore_not_cyclic, hA.secondDerived_le_fitting,
        hA.Fcore_join_centralizer,
        hA.fitting_le_derived_of_K_ne_bot hKne⟩,
      ⟨hC.partner_cyclic, hC.partner_ne_bot,
        hC.partner_le_Fcore, hC.partner_le_secondDerived,
        hcentralizer⟩,
      hC.join_difference_normalizedTI⟩

/-- A complement to the Fitting core inside the derived subgroup, together
with the normalization data needed to manufacture a type-P witness. -/
private structure DerivedFcoreComplement (M K : Subgroup G) where
  complement : Subgroup G
  nilpotent : Group.IsNilpotent complement
  complement_le_derived : complement ≤ derivedWithin M
  K_normalizes : K ≤ Subgroup.normalizer (complement : Set G)
  decomposition : IsInternalSemidirectProductIn
    (Fitting_core M) complement (derivedWithin M)

private noncomputable def restrictFcoreComplement
    {M K C : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hCM : C ≤ M)
    (hKM : K ≤ M)
    (hKC : K ≤ C)
    (hComp : ((Fitting_core M).subgroupOf M).IsComplement'
      (C.subgroupOf M)) :
    DerivedFcoreComplement M K := by
  classical
  let D : Subgroup G := derivedWithin M
  let V : Subgroup G := C ⊓ D
  have hFD : Fitting_core M ≤ D :=
    (Fitting_structure hM).Fcore_le_derived
  have hDM : D ≤ M := derivedWithin_le16_final M
  have hVD : V ≤ D := inf_le_right
  have hFnormalD : ((Fitting_core M).subgroupOf D).Normal :=
    normal_restrict16 (Fcore_normal M) hFD hDM
  letI : ((Fitting_core M).subgroupOf D).Normal := hFnormalD
  have hVdecomp : IsInternalSemidirectProductIn
      (Fitting_core M) V D := by
    refine ⟨hFD, hVD, hFnormalD, ?_⟩
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    · rw [disjoint_iff]
      apply le_antisymm
      · intro z hz
        have hzM : (⟨z, hDM z.2⟩ : M) ∈
            (Fitting_core M).subgroupOf M ⊓ C.subgroupOf M :=
          ⟨hz.1, hz.2.1⟩
        have hzBot : (⟨z, hDM z.2⟩ : M) ∈ (⊥ : Subgroup M) := by
          rw [← disjoint_iff.mp hComp.disjoint]
          exact hzM
        have hzEqM : (⟨z, hDM z.2⟩ : M) = 1 :=
          Subgroup.mem_bot.mp hzBot
        have hzEqG : (z : G) = 1 :=
          congrArg (fun m : M ↦ (m : G)) hzEqM
        exact Subgroup.mem_bot.mpr (Subtype.ext hzEqG)
      · exact bot_le
    · apply Set.eq_univ_iff_forall.mpr
      intro d
      let dM : M := ⟨d, hDM d.2⟩
      obtain ⟨fc, hfc, _⟩ := hComp.existsUnique dM
      have hcD : ((fc.2 : M) : G) ∈ D := by
        have heq : (fc.2 : M) = (fc.1 : M)⁻¹ * dM := by
          rw [← hfc]
          simp
        change ((fc.2 : M) : G) ∈ D
        rw [heq]
        exact D.mul_mem (D.inv_mem (hFD fc.1.2)) d.2
      refine ⟨⟨(fc.1 : G), hFD fc.1.2⟩, fc.1.2,
        ⟨(fc.2 : G), hcD⟩, ⟨fc.2.2, hcD⟩, ?_⟩
      have hfcG : (fc.1 : G) * (fc.2 : G) = (d : G) :=
        congrArg (fun m : M ↦ (m : G)) hfc
      exact Subtype.ext hfcG
  have hKnormV : K ≤ Subgroup.normalizer (V : Set G) := by
    intro k hkK
    apply Subgroup.mem_set_normalizer_iff''.mpr
    intro v
    constructor
    · intro hv
      refine ⟨?_, ?_⟩
      · exact C.mul_mem (C.mul_mem (C.inv_mem (hKC hkK)) hv.1)
          (hKC hkK)
      · have hkM := hKM hkK
        have hnormD : k ∈ Subgroup.normalizer (D : Set G) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hDM).1
            (by simpa [D] using derivedWithin_normal16 M) hkM
        exact ((Subgroup.mem_set_normalizer_iff''.mp hnormD) v).1 hv.2
    · intro hv
      refine ⟨?_, ?_⟩
      · simpa [mul_assoc] using
          C.mul_mem (C.mul_mem (hKC hkK) hv.1)
            (C.inv_mem (hKC hkK))
      · have hkM := hKM hkK
        have hnormD : k ∈ Subgroup.normalizer (D : Set G) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hDM).1
            (by simpa [D] using derivedWithin_normal16 M) hkM
        exact ((Subgroup.mem_set_normalizer_iff''.mp hnormD) v).2 hv.2
  have hVnil : Group.IsNilpotent V := by
    letI : ((Fitting_core M).subgroupOf D).Normal := hVdecomp.2.2.1
    have hquot : Group.IsNilpotent
        (D ⧸ (Fitting_core M).subgroupOf D) := by
      simpa [D] using (Fitting_structure hM).derived_mod_Fcore_nilpotent
    letI : Group.IsNilpotent
        (D ⧸ (Fitting_core M).subgroupOf D) := hquot
    exact Group.nilpotent_of_mulEquiv
      (semidirectQuotientEquiv16 hVdecomp)
  exact
    { complement := V
      nilpotent := hVnil
      complement_le_derived := hVD
      K_normalizes := hKnormV
      decomposition := hVdecomp }

private noncomputable def chooseFcoreComplement
    {M K : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hKM : K ≤ M)
    (hHallK : IsHall (kappaPrimes M) (K.subgroupOf M)) :
    DerivedFcoreComplement M K := by
  classical
  letI : IsSolvable M := mmax_sol hM
  let FM : Subgroup M := (Fitting_core M).subgroupOf M
  let KM : Subgroup M := K.subgroupOf M
  letI : FM.Normal := Fcore_normal M
  have hFcop : (Nat.card FM).Coprime FM.index :=
    (Fcore_Hall M).coprime_card_index
  have hFKcop : (Nat.card FM).Coprime (Nat.card KM) := by
    have hFpi : IsPiNumber (sigmaPrimes M) (Nat.card FM) := by
      rw [MathlibSupport.natCard_subgroupOf_eq (Fcore_sub M)]
      exact (sigmaCore_isPiNumber M).of_dvd
        (Subgroup.card_dvd_of_le (Fcore_sub_Msigma hM))
    have hKpi : IsPiNumber (sigmaPrimes M)ᶜ (Nat.card KM) := by
      exact hHallK.isPiNumber_card.mono (kappa_sigma' M)
    exact hFpi.coprime_compl hKpi
  have hExists : ∃ CM : Subgroup M,
      FM.IsComplement' CM ∧ KM ≤ CM :=
    exists_right_complement_ge_of_coprime hFcop hFKcop
  let CM : Subgroup M := Classical.choose hExists
  have hSpec : FM.IsComplement' CM ∧ KM ≤ CM :=
    Classical.choose_spec hExists
  have hComp : FM.IsComplement' CM := hSpec.1
  have hKMC : KM ≤ CM := hSpec.2
  let C : Subgroup G := CM.map M.subtype
  have hCM : C ≤ M := Subgroup.map_subtype_le _
  have hKC : K ≤ C := by
    intro k hk
    let kM : M := ⟨k, hKM hk⟩
    have hkKM : kM ∈ KM := hk
    exact Subgroup.mem_map_of_mem M.subtype (hKMC hkKM)
  have hCompAmbient : FM.IsComplement' (C.subgroupOf M) := by
    have hCsub : C.subgroupOf M = CM :=
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective CM
    simpa [FM, hCsub] using hComp
  exact restrictFcoreComplement hM hCM hKM hKC hCompAmbient

/-- Canonical data attached to a type-P1 maximal subgroup.  This is
Type-valued because it carries the four chosen subgroups. -/
private structure CanonicalP1Witness (M : Subgroup G) where
  U : Subgroup G
  W : Subgroup G
  W₁ : Subgroup G
  W₂ : Subgroup G
  defW : IsInternalDirectProductIn W₁ W₂ W
  typeP : of_typeP M U W W₁ W₂ defW
  outer_decomposition :
    IsInternalSemidirectProductIn (derivedWithin M) W₁ M
  normalizer_le : Fitting_core M ≠ sigmaCore M →
    Subgroup.normalizer (U : Set G) ≤ M
  core_eq_iff_U_bot : Fitting_core M = sigmaCore M ↔ U = ⊥
  quotient_abelian_iff_U_abelian :
    fittingCoreQuotientAbelian M ↔ IsMulCommutative U
  K_prime_of_core_ne : Fitting_core M ≠ sigmaCore M →
    (Nat.card W₁).Prime
  fitting_TI_of_core_ne : Fitting_core M ≠ sigmaCore M →
    IsNormalizedTI (subgroupNonidentity (fittingWithin M)) ⊤ M

private noncomputable def canonicalP1Witness
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hP1 : M ∈ typeP1MaximalSubgroups (G := G)) :
    CanonicalP1Witness M := by
  classical
  have hExists : ∃ U₀ K : Subgroup G, KappaComplement M U₀ K :=
    kappa_witness hM
  let U₀ : Subgroup G := Classical.choose hExists
  have hKExists : ∃ K : Subgroup G, KappaComplement M U₀ K :=
    Classical.choose_spec hExists
  let K : Subgroup G := Classical.choose hKExists
  have hCompl₀ : KappaComplement M U₀ K :=
    Classical.choose_spec hKExists
  have hKne : K ≠ ⊥ := (P1maxP hM hCompl₀).1 hP1 |>.1
  have hU₀bot : U₀ = ⊥ := (P1maxP hM hCompl₀).1 hP1 |>.2
  let hCompl : KappaComplement M (⊥ : Subgroup G) K :=
    hU₀bot ▸ hCompl₀
  have hFC := chooseFcoreComplement hM hCompl.K_le_M hCompl.hall_K
  let V : Subgroup G := hFC.complement
  let W₁ : Subgroup G := K
  let W₂ : Subgroup G := pTypePartner M K
  let W : Subgroup G := pTypeJoin M K
  let defW : IsInternalDirectProductIn W₁ W₂ W := by
    simpa [W₁, W₂, W] using (BGsummaryC hM hCompl hKne).join_direct
  have hTypeP : of_typeP M V W W₁ W₂ defW := by
    simpa [V, W, W₁, W₂, defW] using
      canonical_typeP hM hCompl hKne hFC.nilpotent
        hFC.complement_le_derived hFC.K_normalizes hFC.decomposition
  have hFacts := typePFacts16 hM hTypeP
  have hSigmaDer := Msigma_eq_der1 hM hP1
  have hCases := hFacts.sigma_eq_derived_cases hSigmaDer
  have hNorm : Fitting_core M ≠ sigmaCore M →
      Subgroup.normalizer (V : Set G) ≤ M := by
    intro hCoreNe
    exact (hFacts.typeP1_iff.1 hP1).resolve_left
      (fun hVbot ↦ hCoreNe (hCases.1.2 hVbot))
  exact
    { U := V
      W := W
      W₁ := W₁
      W₂ := W₂
      defW := defW
      typeP := hTypeP
      outer_decomposition := hTypeP.1.2.2.2
      normalizer_le := hNorm
      core_eq_iff_U_bot := hCases.1
      quotient_abelian_iff_U_abelian := hCases.2
      K_prime_of_core_ne := by
        intro hne
        simpa [W₁] using
          (BGsummaryA hM hCompl).nonnilpotent_case hne |>.2.2
      fitting_TI_of_core_ne := by
        intro hne
        exact (BGsummaryA hM hCompl).nonnilpotent_case hne |>.2.1 }

private theorem exists_typeII_of_FTtype_two
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (htype : FTtype M = 2) :
    exists_typeP (of_typeII M) := by
  classical
  have hP2 : M ∈ typeP2MaximalSubgroups (G := G) :=
    (FTtype_P2max hM).2 htype
  obtain ⟨U, K, hCompl⟩ := kappa_witness hM
  have hKU := (P2maxP hM hCompl).1 hP2
  have hKne := hKU.1
  have hUne := hKU.2
  have hC := BGsummaryC hM hCompl hKne
  have hFcoreEq : Fitting_core M = sigmaCore M :=
    (Fcore_eq_Msigma hM).2
      (notP1type_Msigma_nil (Or.inr hP2))
  let W₁ : Subgroup G := K
  let W₂ : Subgroup G := pTypePartner M K
  let W : Subgroup G := pTypeJoin M K
  let defW : IsInternalDirectProductIn W₁ W₂ W := by
    simpa [W₁, W₂, W] using hC.join_direct
  have hUnil : Group.IsNilpotent U := by
    letI : IsMulCommutative U := hC.U_abelian
    infer_instance
  have hFsd : IsInternalSemidirectProductIn
      (Fitting_core M) U (derivedWithin M) := by
    simpa [hFcoreEq] using hC.sigma_U_derived
  have hTypeP : of_typeP M U W W₁ W₂ defW := by
    simpa [W, W₁, W₂, defW] using
      canonical_typeP hM hCompl hKne hUnil
        hC.sigma_U_derived.2.1
        (BGsummaryA hM hCompl).K_normalizes_U hFsd
  have hCommon : of_typeII_IV M U W W₁ W₂ defW :=
    ⟨hTypeP, hUne, by simpa [W₁] using
      (hC.nontrivial_U_case hUne).1,
      (hC.nontrivial_U_case hUne).2.1⟩
  have hDerivedCore : Fitting_core (derivedWithin M) = Fitting_core M := by
    let D : Subgroup G := derivedWithin M
    have hDerM : D ≤ M := derivedWithin_le16_final M
    have hFcoreMHallD : IsHall
        (primeSupport (Nat.card (Fitting_core M)))
        ((Fitting_core M).subgroupOf D) :=
      isHall_subgroupOf_chain16
        (Fitting_structure hM).Fcore_le_derived hDerM (Fcore_Hall M)
    have hDerHallM : IsHall (kappaPrimes M)ᶜ (D.subgroupOf M) :=
      semidirect_left_isHall_compl16
        hTypeP.1.2.2.2 hCompl.hall_K
    have hFcoreDpi :
        primeSupport (Nat.card (Fitting_core D)) ⊆
          (kappaPrimes M)ᶜ := by
      intro p hp
      have hpD : p ∣ Nat.card D :=
        hp.2.trans (Subgroup.card_dvd_of_le (Fcore_sub D))
      have hpDsub : p ∣ Nat.card (D.subgroupOf M) := by
        simpa [MathlibSupport.natCard_subgroupOf_eq hDerM] using hpD
      exact hDerHallM.isPiNumber_card hp.1 hpDsub
    have hFcoreDHallM : IsHall
        (primeSupport (Nat.card (Fitting_core D)))
        ((Fitting_core D).subgroupOf M) :=
      hall_of_le_hall_of_hall16 (Fcore_sub D) hDerM
        (Fcore_Hall D) hDerHallM hFcoreDpi
    have hFcoreDleM : Fitting_core D ≤ M :=
      (Fcore_sub D).trans hDerM
    have hFcoreDnormalM : ((Fitting_core D).subgroupOf M).Normal := by
      have hMnormD : M ≤ Subgroup.normalizer (D : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hDerM).1
          (by simpa [D] using derivedWithin_normal16 M)
      have hnormDleF :
          Subgroup.normalizer (D : Set G) ≤
            Subgroup.normalizer (Fitting_core D : Set G) := by
        have hchar := characteristic_map_subtype_le_normalizer16
          D ((Fitting_core D).subgroupOf D)
        rw [Subgroup.map_subgroupOf_eq_of_le (Fcore_sub D)] at hchar
        exact hchar
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hFcoreDleM).2
        (hMnormD.trans hnormDleF)
    apply le_antisymm
    · exact Fcore_max
        hFcoreDHallM hFcoreDleM hFcoreDnormalM (Fcore_nil D)
    · exact Fcore_max hFcoreMHallD
        (Fitting_structure hM).Fcore_le_derived
        (normal_restrict16 (Fcore_normal M)
          (Fitting_structure hM).Fcore_le_derived
          (derivedWithin_le16_final M))
        (Fcore_nil M)
  have hTypeFDerived : of_typeF (derivedWithin M) U := by
    let U₁ : Subgroup G := sigmaFixedPointGenerated M U
    obtain ⟨U₀, hU₀U, hexp, hsd₀, hfrob⟩ :=
      (kappa_structure hM hCompl).exponent_frobenius hUne
    refine ⟨by simpa [hDerivedCore] using
        (Fcore_structure hM).Fcore_ne_bot,
      hUne, by simpa [hDerivedCore] using hFsd, ?_, ?_⟩
    · refine ⟨U₁, ?_⟩
      exact ⟨sigmaFixedPointGenerated_le_complement16 hM hCompl,
        sigmaFixedPointGenerated_normal_in_complement16 hM hCompl,
        (kappa_structure hM hCompl).fixedPointGenerated_abelian,
        by
          intro x hx
          apply sigma_fixedPointGenerated_contains_centralizer16
          simpa [hDerivedCore, hFcoreEq] using hx⟩
    · refine ⟨U₀, hU₀U, hexp, ?_, ?_⟩
      · rw [hDerivedCore, hFcoreEq]
        exact hsd₀
      · rw [hDerivedCore, hFcoreEq]
        exact hfrob
  exact ⟨U, W, W₁, W₂, defW,
    hCommon, hC.U_abelian, hC.normalizer_U_not_le,
      hTypeFDerived, hDerivedCore⟩

private theorem exists_typeIII_of_FTtype_three
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (htype : FTtype M = 3) :
    exists_typeP (of_typeIII M) := by
  have hP1 : M ∈ typeP1MaximalSubgroups (G := G) :=
    (FTtype_P1max hM).2 (by omega)
  have hSigmaDer := Msigma_eq_der1 hM hP1
  have hnotPi : ¬ IsPiNumber (kappaPrimes M)ᶜ (Nat.card M) :=
    fun hpi ↦ hP1.1.2 ⟨hM, hpi⟩
  have hCoreNe : Fitting_core M ≠ sigmaCore M := by
    intro hEq
    have : FTtype M = 5 := by
      simp [FTtype, ftType, hnotPi, hSigmaDer, hEq]
    omega
  have hCoreDerNe : Fitting_core M ≠ derivedWithin M :=
    fun hEq ↦ hCoreNe (hEq.trans hSigmaDer.symm)
  have hQuot : fittingCoreQuotientAbelian M := by
    by_contra hnot
    have : FTtype M = 4 := by
      simp [FTtype, ftType, hnotPi, hSigmaDer, hCoreDerNe, hnot]
    omega
  let h := canonicalP1Witness hM hP1
  have hUne : h.U ≠ ⊥ := by
    intro hbot
    exact hCoreNe (h.core_eq_iff_U_bot.2 hbot)
  have hCommon : of_typeII_IV M h.U h.W h.W₁ h.W₂ h.defW :=
    ⟨h.typeP, hUne, h.K_prime_of_core_ne hCoreNe,
      h.fitting_TI_of_core_ne hCoreNe⟩
  exact ⟨h.U, h.W, h.W₁, h.W₂, h.defW, hCommon,
    h.quotient_abelian_iff_U_abelian.1 hQuot,
      h.normalizer_le hCoreNe⟩

private theorem exists_typeIV_of_FTtype_four
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (htype : FTtype M = 4) :
    exists_typeP (of_typeIV M) := by
  have hP1 : M ∈ typeP1MaximalSubgroups (G := G) :=
    (FTtype_P1max hM).2 (by omega)
  have hSigmaDer := Msigma_eq_der1 hM hP1
  have hnotPi : ¬ IsPiNumber (kappaPrimes M)ᶜ (Nat.card M) :=
    fun hpi ↦ hP1.1.2 ⟨hM, hpi⟩
  have hCoreNe : Fitting_core M ≠ sigmaCore M := by
    intro hEq
    have : FTtype M = 5 := by
      simp [FTtype, ftType, hnotPi, hSigmaDer, hEq]
    omega
  have hCoreDerNe : Fitting_core M ≠ derivedWithin M :=
    fun hEq ↦ hCoreNe (hEq.trans hSigmaDer.symm)
  have hQuot : ¬ fittingCoreQuotientAbelian M := by
    intro hquot
    have : FTtype M = 3 := by
      simp [FTtype, ftType, hnotPi, hSigmaDer, hCoreDerNe, hquot]
    omega
  let h := canonicalP1Witness hM hP1
  have hUne : h.U ≠ ⊥ := by
    intro hbot
    exact hCoreNe (h.core_eq_iff_U_bot.2 hbot)
  have hCommon : of_typeII_IV M h.U h.W h.W₁ h.W₂ h.defW :=
    ⟨h.typeP, hUne, h.K_prime_of_core_ne hCoreNe,
      h.fitting_TI_of_core_ne hCoreNe⟩
  exact ⟨h.U, h.W, h.W₁, h.W₂, h.defW, hCommon,
    fun hcomm ↦ hQuot (h.quotient_abelian_iff_U_abelian.2 hcomm),
      h.normalizer_le hCoreNe⟩

private theorem nonTI_prime_mem_fcore
    {M : Subgroup G} {g : G}
    (h : NonTIFittingNonabelianCase M g) :
    Nat.card (nonTIFittingIntersection M g) ∈
      primeSupport (Nat.card (Fitting_core M)) := by
  let p := Nat.card (nonTIFittingIntersection M g)
  letI : Fact p.Prime := ⟨h.p_prime⟩
  have hpCore : p ∣ Nat.card (pCore p (Fitting_core M)) :=
    pCore_isPGroup.card_eq_or_dvd.resolve_left (by
      intro hcard
      apply h.pcore_nonabelian
      rw [Subgroup.card_eq_one.mp hcard]
      infer_instance)
  exact ⟨h.p_prime,
    hpCore.trans (pCore p (Fitting_core M)).card_subgroup_dvd_card⟩

private theorem exists_typeV_of_FTtype_five
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (htype : FTtype M = 5) :
    exists_typeP (of_typeV M) := by
  classical
  have hP1 : M ∈ typeP1MaximalSubgroups (G := G) :=
    (FTtype_P1max hM).2 (by omega)
  have hSigmaDer := Msigma_eq_der1 hM hP1
  have hnotPi : ¬ IsPiNumber (kappaPrimes M)ᶜ (Nat.card M) :=
    fun hpi ↦ hP1.1.2 ⟨hM, hpi⟩
  have hCoreEq : Fitting_core M = sigmaCore M := by
    by_contra hne
    have hCoreDerNe : Fitting_core M ≠ derivedWithin M :=
      fun hEq ↦ hne (hEq.trans hSigmaDer.symm)
    have hvalue : FTtype M =
        if fittingCoreQuotientAbelian M then 3 else 4 := by
      simp [FTtype, ftType, hnotPi, hSigmaDer, hCoreDerNe]
    split at hvalue <;> omega
  let h := canonicalP1Witness hM hP1
  have hUbot : h.U = ⊥ := h.core_eq_iff_U_bot.1 hCoreEq
  have hOuter : IsInternalSemidirectProductIn
      (Fitting_core M) h.W₁ M := by
    simpa [hCoreEq, hSigmaDer] using h.outer_decomposition
  have hW₁cyclic : IsCyclic h.W₁ := h.typeP.1.1
  have hcardQuot : Nat.card
      (M ⧸ (Fitting_core M).subgroupOf M) = Nat.card h.W₁ :=
    semidirect_quotient_card16 hOuter
  have hexpQuot : Monoid.exponent
      (M ⧸ (Fitting_core M).subgroupOf M) = Nat.card h.W₁ := by
    rw [semidirect_quotient_exponent16 hOuter]
    letI : IsCyclic h.W₁ := hW₁cyclic
    exact IsCyclic.exponent_eq_card
  refine ⟨h.U, h.W, h.W₁, h.W₂, h.defW, h.typeP, hUbot, ?_⟩
  by_cases hTI : IsNormalizedTI
      (subgroupNonidentity (Fitting_core M)) ⊤ M
  · exact Or.inl hTI
  · obtain ⟨g, hg, hNonTI⟩ := exists_nonTI_fcore_structure hM hTI
    rcases hNonTI.final_case with hAb | hNonab
    · exact (hP1.1.2 hAb.typeF).elim
    · rcases hNonab.conclusion with hExp | hExtra
      · right
        left
        let p := Nat.card (nonTIFittingIntersection M g)
        refine ⟨p, nonTI_prime_mem_fcore hNonab, ?_,
          hNonab.pPrimeCore_cyclic⟩
        rw [← hexpQuot]
        exact hExp p (nonTI_prime_mem_fcore hNonab)
      · right
        right
        let p := Nat.card (nonTIFittingIntersection M g)
        refine ⟨p, nonTI_prime_mem_fcore hNonab,
          hExtra.1, ?_, hNonab.pPrimeCore_cyclic⟩
        rw [← hcardQuot]
        exact hExtra.2.2

private theorem typeI_iff_type_one
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    (∃ U : Subgroup G, of_typeI M U) ↔ FTtype M = 1 := by
  constructor
  · rintro ⟨U, hTypeI⟩
    exact (FTtype_Fmax hM).1
      (typeF_implies_typeFMaximal hM hTypeI.1)
  · intro htype
    exact exists_typeI_of_FTtype_one hM ((FTtype_Fmax hM).2 htype)

private theorem typeII_iff_type_two
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    exists_typeP (of_typeII M) ↔ FTtype M = 2 := by
  constructor
  · rintro ⟨U, W, W₁, W₂, defW,
      hCommon, hUcomm, hnorm, hTypeF, hCore⟩
    have hFacts := typePFacts16 hM hCommon.1
    have hnotP1 : M ∉ typeP1MaximalSubgroups (G := G) := by
      intro hP1
      rcases hFacts.typeP1_iff.1 hP1 with hUbot | hnormU
      · exact hCommon.2.1 hUbot
      · exact hnorm hnormU
    exact (FTtype_P2max hM).1 ⟨hFacts.typeP, hnotP1⟩
  · exact exists_typeII_of_FTtype_two hM

private theorem typeIII_iff_type_three
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    exists_typeP (of_typeIII M) ↔ FTtype M = 3 := by
  constructor
  · rintro ⟨U, W, W₁, W₂, defW, hCommon, hUcomm, hnorm⟩
    have hFacts := typePFacts16 hM hCommon.1
    have hP1 : M ∈ typeP1MaximalSubgroups (G := G) :=
      hFacts.typeP1_iff.2 (Or.inr hnorm)
    have hSigmaDer := Msigma_eq_der1 hM hP1
    have hCases := hFacts.sigma_eq_derived_cases hSigmaDer
    have hCoreNe : Fitting_core M ≠ sigmaCore M := by
      intro hEq
      exact hCommon.2.1 (hCases.1.1 hEq)
    have hCoreDerNe : Fitting_core M ≠ derivedWithin M :=
      fun hEq ↦ hCoreNe (hEq.trans hSigmaDer.symm)
    have hQuot : fittingCoreQuotientAbelian M := hCases.2.2 hUcomm
    have hnotPi : ¬ IsPiNumber (kappaPrimes M)ᶜ (Nat.card M) :=
      fun hpi ↦ hFacts.typeP.2 ⟨hM, hpi⟩
    simp [FTtype, ftType, hnotPi, hSigmaDer, hCoreDerNe, hQuot]
  · exact exists_typeIII_of_FTtype_three hM

private theorem typeIV_iff_type_four
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    exists_typeP (of_typeIV M) ↔ FTtype M = 4 := by
  constructor
  · rintro ⟨U, W, W₁, W₂, defW, hCommon, hUnotcomm, hnorm⟩
    have hFacts := typePFacts16 hM hCommon.1
    have hP1 : M ∈ typeP1MaximalSubgroups (G := G) :=
      hFacts.typeP1_iff.2 (Or.inr hnorm)
    have hSigmaDer := Msigma_eq_der1 hM hP1
    have hCases := hFacts.sigma_eq_derived_cases hSigmaDer
    have hCoreNe : Fitting_core M ≠ sigmaCore M := by
      intro hEq
      exact hCommon.2.1 (hCases.1.1 hEq)
    have hCoreDerNe : Fitting_core M ≠ derivedWithin M :=
      fun hEq ↦ hCoreNe (hEq.trans hSigmaDer.symm)
    have hQuot : ¬ fittingCoreQuotientAbelian M :=
      fun hquot ↦ hUnotcomm (hCases.2.1 hquot)
    have hnotPi : ¬ IsPiNumber (kappaPrimes M)ᶜ (Nat.card M) :=
      fun hpi ↦ hFacts.typeP.2 ⟨hM, hpi⟩
    simp [FTtype, ftType, hnotPi, hSigmaDer, hCoreDerNe, hQuot]
  · exact exists_typeIV_of_FTtype_four hM

private theorem typeV_iff_type_five
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    exists_typeP (of_typeV M) ↔ FTtype M = 5 := by
  constructor
  · rintro ⟨U, W, W₁, W₂, defW, hTypeP, hUbot, hAlt⟩
    have hFacts := typePFacts16 hM hTypeP
    have hP1 : M ∈ typeP1MaximalSubgroups (G := G) :=
      hFacts.typeP1_iff.2 (Or.inl hUbot)
    have hSigmaDer := Msigma_eq_der1 hM hP1
    have hCoreEq :=
      (hFacts.sigma_eq_derived_cases hSigmaDer).1.2 hUbot
    have hnotPi : ¬ IsPiNumber (kappaPrimes M)ᶜ (Nat.card M) :=
      fun hpi ↦ hFacts.typeP.2 ⟨hM, hpi⟩
    simp [FTtype, ftType, hnotPi, hSigmaDer, hCoreEq]
  · exact exists_typeV_of_FTtype_five hM

private theorem spec_index_range
    {i : ℕ} {M : Subgroup G} (h : ftTypeSpec i M) :
    1 ≤ i ∧ i ≤ 5 := by
  rcases i with _ | _ | _ | _ | _ | _ | i <;>
    simp [ftTypeSpec] at h ⊢

theorem semanticSpecification (i : ℕ) (M : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G)) :
    FTtype_spec i M ↔ FTtype M = i := by
  by_cases hi1 : i = 1
  · subst i
    simpa [FTtype_spec, ftTypeSpec] using typeI_iff_type_one hM
  by_cases hi2 : i = 2
  · subst i
    simpa [FTtype_spec, ftTypeSpec] using typeII_iff_type_two hM
  by_cases hi3 : i = 3
  · subst i
    simpa [FTtype_spec, ftTypeSpec] using typeIII_iff_type_three hM
  by_cases hi4 : i = 4
  · subst i
    simpa [FTtype_spec, ftTypeSpec] using typeIV_iff_type_four hM
  by_cases hi5 : i = 5
  · subst i
    simpa [FTtype_spec, ftTypeSpec] using typeV_iff_type_five hM
  constructor
  · intro hspec
    have hirange := spec_index_range hspec
    omega
  · intro htype
    have htrange := FTtype_range M
    omega

end FTTypeSpecInternal

/-- `BGsection16.v: FTtypeP`, Lemma 16.1. -/
theorem FTtypeP (i : ℕ) (M : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G)) :
    FTtype_spec i M ↔ FTtype M = i :=
  FTTypeSpecInternal.semanticSpecification i M hM

end

end Submission.OddOrder.BG.Section16
