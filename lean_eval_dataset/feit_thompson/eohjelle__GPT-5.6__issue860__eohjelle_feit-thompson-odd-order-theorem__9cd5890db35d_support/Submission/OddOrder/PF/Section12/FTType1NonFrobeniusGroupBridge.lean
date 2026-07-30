import Submission.OddOrder.PF.Section12.FTType1NonFrobeniusWitness
import Submission.OddOrder.PF.Section09.PTypeGaloisSubgroupAdapters
import Submission.OddOrder.BG.Section02.OddGL2CrossCharacteristicAbelian
import Submission.OddOrder.BG.Section04.RankTwoPGroupAutomorphismPrimes
import Submission.OddOrder.MathlibSupport.WielandtSolvableFixpoint

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section14
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open scoped Classical IsMulCommutative Pointwise

variable {G : Type} [Group G] [Finite G] [IsMinSimpleOddGroup G]

local instance : Fintype G := Fintype.ofFinite G

/-! ## Small Hall and witness adapters -/

/-- A `pi`-subgroup lies in a normal `pi`-Hall subgroup. -/
private theorem le_normal_isHall_of_isPiNumber12
    {pi : Set ℕ} {C K A : Subgroup G}
    (hKnormal : (K.subgroupOf C).Normal)
    (hKHall : IsHall pi (K.subgroupOf C))
    (hAC : A ≤ C) (hApi : IsPiNumber pi (Nat.card A)) :
    A ≤ K := by
  let KC : Subgroup C := K.subgroupOf C
  letI : KC.Normal := by simpa [KC] using hKnormal
  have hcop : (Nat.card A).Coprime KC.index := by
    apply Nat.coprime_of_dvd
    intro q hq hqA hqIndex
    exact (hKHall.isPiNumber_index hq hqIndex)
      (hApi hq hqA)
  intro x hxA
  let xC : C := ⟨x, hAC hxA⟩
  let quotientMap : C →* C ⧸ KC := QuotientGroup.mk' KC
  have horderA : orderOf (quotientMap xC) ∣ Nat.card A :=
    (orderOf_map_dvd quotientMap xC).trans (by
      simpa [xC] using A.orderOf_dvd_natCard hxA)
  have horderIndex : orderOf (quotientMap xC) ∣ KC.index := by
    simpa only [KC.index_eq_card] using
      orderOf_dvd_natCard (quotientMap xC)
  have horderOne : orderOf (quotientMap xC) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horderA horderIndex
  have hquotientOne : quotientMap xC = 1 :=
    orderOf_eq_one_iff.mp horderOne
  have hxKC : xC ∈ KC :=
    (QuotientGroup.eq_one_iff xC).mp (by
      change QuotientGroup.mk' KC xC = 1
      exact hquotientOne)
  exact hxKC

private theorem witness_x_mem_p0_12
    {p : ℕ} {M P0 : Subgroup G}
    (w : NonFrobeniusFTType1Witness p M P0) :
    w.x ∈ P0 := by
  obtain ⟨x0, hx0, hx⟩ := w.x_mem_omega
  rw [← hx]
  exact x0.property

private theorem witness_p0_le_M12
    {p : ℕ} {M P0 : Subgroup G}
    (ctx : FTType1NonFrobeniusContext p M P0) :
    P0 ≤ M := by
  obtain ⟨PM, hPM⟩ := ctx.sylow_P0
  rw [hPM]
  exact Subgroup.map_subtype_le (PM : Subgroup M)

private theorem witness_p0_not_cyclic12
    {p : ℕ} {M P0 : Subgroup G}
    (ctx : FTType1NonFrobeniusContext p M P0)
    (w : NonFrobeniusFTType1Witness p M P0) :
    ¬ IsCyclic P0 := by
  intro hcyclic
  obtain ⟨A, hAP0, hA⟩ := w.P0_rank_two.1
  letI : IsCyclic P0 := hcyclic
  exact hA.not_isCyclic ctx.p_prime
    (Subgroup.isCyclic_of_le hAP0)

private theorem derived_eq_bot_of_isMulCommutative12
    {A : Subgroup G} (hA : IsMulCommutative A) :
    derivedWithin A = ⊥ := by
  letI : IsMulCommutative A := hA
  simp only [derivedWithin, _root_.commutator_eq_bot,
    Subgroup.map_bot]

/-! ## Peterfalvi (12.10): the second maximal subgroup -/

/-- In the non-type-II branch of (12.10), the Section-11 Galois endpoint
makes the displayed complement cyclic. -/
private theorem typeP_complement_cyclic12
    {L U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (hmax : L ∈ minSimple_max_groups (G := G))
    (hP : of_typeP L U W W₁ W₂ defW)
    (hnot2 : FTtype L ≠ 2)
    (hnot5 : FTtype L ≠ 5) :
    IsCyclic U := by
  let pctx := Ptype_Fcore_context hmax defW hP hnot5
  let base : FTType34Base L U W W₁ W₂ defW :=
    ⟨hP, hnot2, pctx⟩
  have hType3 : FTtype L = 3 :=
    (FTtype34_structure base).2.2.1
  have hGal : typeP_Galois
      (Ptype_factor_action pctx
        (Ptype_Fcore_factor_facts pctx)) := by
    simpa only [pctx, base] using
      (FTtype34_structure base).2.2.2
  have hUcomm : IsMulCommutative U :=
    (compl_of_typeIII L U W W₁ W₂ defW
      hmax hP hType3).2.1
  have hDerivedU : derivedWithin U = ⊥ :=
    derived_eq_bot_of_isMulCommutative12 hUcomm
  have hAmbientKernel : Ptype_Fcompl_kernel pctx = ⊥ := by
    calc
      Ptype_Fcompl_kernel pctx = base.C :=
        Ptype_Fcompl_kernel_cent base
      _ = base.U' := (FTtype34_facts base).C_eq_derived_U
      _ = ⊥ := hDerivedU
  let facts := Ptype_Fcore_factor_facts pctx
  let D := Ptype_factor_action pctx facts
  have hDC : D.C = ⊥ := by
    change (ptypeFCoreAction pctx).ker = ⊥
    exact
      (Subgroup.map_eq_bot_iff_of_injective
        (ptypeFCoreAction pctx).ker U.subtype_injective).mp
        (by simpa only [Ptype_Fcompl_kernel] using hAmbientKernel)
  exact PTypeGaloisSubgroupAdaptersInternal.pTypeGalois_complement_cyclic_of_C_eq_bot
    (Ptype_factor_action_hypotheses pctx facts)
    (by simpa only [D, facts] using hGal) hDC

/-- The subgroup `P0` is contained in the Fitting core of the second
maximal subgroup.  This is the Hall-conjugacy paragraph in (12.10). -/
private theorem p0_le_second_fitting12_impl
    {p : ℕ} {M P0 : Subgroup G}
    (ctx : FTType1NonFrobeniusContext p M P0)
    (w : NonFrobeniusFTType1Witness p M P0) :
    P0 ≤ Fitting_core w.L := by
  classical
  letI : Fact p.Prime := ⟨ctx.p_prime⟩
  by_cases hType1 : FTtype w.L = 1
  · rw [← FTcore_type1 w.L hType1]
    exact w.P0_le_FTcore
  · by_cases hType2 : FTtype w.L = 2
    · rw [← FTcore_type2 w.L hType2]
      exact w.P0_le_FTcore
    · obtain ⟨U, W, W₁, W₂, defW, hP⟩ :=
        FTtypeP_witness w.L w.L_maximal hType1
      have hnot5 : FTtype w.L ≠ 5 :=
        FTtype5_exclusion w.L w.L_maximal
      let pctx := Ptype_Fcore_context w.L_maximal defW hP hnot5
      let base : FTType34Base w.L U W W₁ W₂ defW :=
        ⟨hP, hType2, pctx⟩
      have hType3 : FTtype w.L = 3 :=
        (FTtype34_structure base).2.2.1
      have hP0D : P0 ≤ derivedWithin w.L := by
        rw [← FTcore_type_gt2 w.L (by omega)]
        exact w.P0_le_FTcore
      let H := Fitting_core w.L
      let D := derivedWithin w.L
      have hHD : H ≤ D := hP.2.1.2.2.2.1
      have hUD : U ≤ D := hP.2.1.2.1
      have hDL : D ≤ w.L :=
        TypeSpecInternal.derivedWithin_le16_final w.L
      have hHhallD : IsHall (primeSupport (Nat.card H))
          (H.subgroupOf D) :=
        TypeSpecInternal.isHall_subgroupOf_chain16
          hHD hDL (Fcore_Hall w.L)
      have hHnormalD : (H.subgroupOf D).Normal :=
        hP.2.1.2.2.2.2.2.1
      have hUhallD : IsHall (primeSupport (Nat.card H))ᶜ
          (U.subgroupOf D) := by
        constructor
        · rw [← hP.2.1.2.2.2.2.2.2.symm.index_eq_card]
          exact hHhallD.isPiNumber_index
        · rw [hP.2.1.2.2.2.2.2.2.index_eq_card]
          simpa only [compl_compl] using hHhallD.isPiNumber_card
      have hUcyclic : IsCyclic U :=
        typeP_complement_cyclic12 w.L_maximal hP hType2 hnot5
      by_contra hP0H
      have hpNotH : p ∈ (primeSupport (Nat.card H))ᶜ := by
        intro hpH
        apply hP0H
        exact le_normal_isHall_of_isPiNumber12
          hHnormalD hHhallD hP0D
            (ctx.sylow_P0.isPGroup.isPiNumber_natCard hpH)
      have hP0compl : IsPiNumber (primeSupport (Nat.card H))ᶜ
          (Nat.card P0) :=
        ctx.sylow_P0.isPGroup.isPiNumber_natCard hpNotH
      have hDsol : IsSolvable D :=
        letI : IsSolvable w.L := mmax_sol w.L_maximal
        isSolvable_of_injective (Subgroup.inclusion hDL)
          (Subgroup.inclusion_injective hDL)
      obtain ⟨d, hP0Ud, -, -, -, -, -⟩ :=
        exists_ambient_isHall_map_conj_ge_of_isSolvable
          hP0D hUD hDsol hP0compl hUhallD
      let U' : Subgroup G :=
        U.map (MulAut.conj (d : G)).toMonoidHom
      let eU : U ≃* U' :=
        U.equivMapOfInjective (MulAut.conj (d : G)).toMonoidHom
          (MulAut.conj (d : G)).injective
      have hU'cyclic : IsCyclic U' := eU.isCyclic.mp hUcyclic
      have hP0cyclic : IsCyclic P0 := by
        letI : IsCyclic U' := hU'cyclic
        exact Subgroup.isCyclic_of_le hP0Ud
      exact witness_p0_not_cyclic12 ctx w hP0cyclic

/-- The second maximal subgroup has type I. -/
private theorem second_maximal_type_one12
    {p : ℕ} {M P0 : Subgroup G}
    (ctx : FTType1NonFrobeniusContext p M P0)
    (w : NonFrobeniusFTType1Witness p M P0) :
    FTtype w.L = 1 := by
  classical
  by_contra hType1
  obtain ⟨U, W, W₁, W₂, defW, hP⟩ :=
    FTtypeP_witness w.L w.L_maximal hType1
  have hnot5 : FTtype w.L ≠ 5 :=
    FTtype5_exclusion w.L w.L_maximal
  have hCommon := compl_of_typeII_IV
    w.L U W W₁ W₂ defW w.L_maximal hP hnot5
  have hxH : w.x ∈ Fitting_core w.L :=
    p0_le_second_fitting12_impl ctx w (witness_x_mem_p0_12 w)
  have hxFit : w.x ∈ subgroupNonidentity (fittingWithin w.L) :=
    ⟨Fcore_sub_Fitting w.L hxH, w.x_ne_one⟩
  apply w.centralizer_not_le_L
  intro y hy
  apply hCommon.2.2.2.centralizerWithin_zpowers_le hxFit
  exact ⟨Subgroup.mem_top y,
    Subgroup.mem_centralizer_iff.mp hy⟩

/-- The witness excludes the normalized-TI alternative for the second
type-I maximal subgroup. -/
private theorem second_fitting_not_normalizedTI12
    {p : ℕ} {M P0 : Subgroup G}
    (ctx : FTType1NonFrobeniusContext p M P0)
    (w : NonFrobeniusFTType1Witness p M P0) :
    ¬ IsNormalizedTI (subgroupNonidentity (Fitting_core w.L))
      (⊤ : Subgroup G) w.L := by
  intro hTI
  have hxH : w.x ∈ Fitting_core w.L :=
    p0_le_second_fitting12_impl ctx w (witness_x_mem_p0_12 w)
  apply w.centralizer_not_le_L
  intro y hy
  apply hTI.centralizerWithin_zpowers_le ⟨hxH, w.x_ne_one⟩
  exact ⟨Subgroup.mem_top y,
    Subgroup.mem_centralizer_iff.mp hy⟩

/-- The two factors in the type-F decomposition have coprime orders. -/
private theorem typeF_core_complement_coprime12
    {L U : Subgroup G} (hTypeF : of_typeF L U) :
    Nat.Coprime (Nat.card (Fitting_core L)) (Nat.card U) := by
  have hHall := (Fcore_Hall L).coprime_card_index
  rw [hTypeF.2.2.1.2.2.2.symm.index_eq_card] at hHall
  simpa only [MathlibSupport.natCard_subgroupOf_eq (Fcore_sub L),
    MathlibSupport.natCard_subgroupOf_eq hTypeF.2.2.1.2.1] using hHall

/-- The type-I alternatives and the rank-two automorphism theorem force
every prime in the complement to be smaller than the distinguished prime
`p`. -/
private theorem typeOne_complement_prime_lt12
    {p q : ℕ} {M P0 U : Subgroup G}
    (ctx : FTType1NonFrobeniusContext p M P0)
    (w : NonFrobeniusFTType1Witness p M P0)
    (hTypeI : of_typeI w.L U)
    (hq : q.Prime) (hqU : q ∣ Nat.card U) :
    q < p := by
  classical
  letI : Fact p.Prime := ⟨ctx.p_prime⟩
  let H := Fitting_core w.L
  have hP0H : P0 ≤ H := p0_le_second_fitting12_impl ctx w
  obtain ⟨A, hAP0, hA⟩ := w.P0_rank_two.1
  have hpA : p ∣ Nat.card A := by
    rw [hA.card_eq]
    exact dvd_pow_self p (by omega : 2 ≠ 0)
  have hpH : p ∣ Nat.card H :=
    hpA.trans (Subgroup.card_dvd_of_le (hAP0.trans hP0H))
  have hpSupportH : p ∈ primeSupport (Nat.card H) :=
    ⟨ctx.p_prime, hpH⟩
  have hCoreUcop := typeF_core_complement_coprime12 hTypeI.1
  have hqp : q ≠ p := by
    intro hqp
    subst q
    exact (Nat.not_coprime_of_dvd_of_dvd
      ctx.p_prime.one_lt hpH hqU) hCoreUcop
  letI : Fact q.Prime := ⟨hq⟩
  obtain ⟨u, huOrder⟩ :=
    exists_prime_orderOf_dvd_card' (G := U) q hqU
  have hqExponent : q ∣ Monoid.exponent U := by
    rw [← huOrder]
    exact Monoid.order_dvd_exponent u
  rcases hTypeI.2 with hTI | hOther
  · exact (second_fitting_not_normalizedTI12 ctx w hTI).elim
  · rcases hOther with hRankTwo | hExponent
    · let P : Subgroup G := (pCore p H).map H.subtype
      have hPH : P ≤ H := Subgroup.map_subtype_le _
      have hPp : IsPGroup p P := by
        simpa only [P] using pCore_isPGroup.map H.subtype
      have hP0P : P0 ≤ P := by
        letI : Group.IsNilpotent H := Fcore_nil w.L
        have hP0Hp : IsPGroup p (P0.subgroupOf H) :=
          ctx.sylow_P0.isPGroup.comap_subtype
        have hP0core : P0.subgroupOf H ≤ pCore p H :=
          hP0Hp.le_pCore_of_isNilpotent
        rw [← Subgroup.map_subgroupOf_eq_of_le hP0H]
        exact Subgroup.map_mono hP0core
      have hPodd : Odd (Nat.card P) := mFT_odd P
      have hPnoRankThree :
          ¬ ∃ E : Subgroup P,
            IsElementaryAbelianOfRank p 3 E := by
        rintro ⟨E, hE⟩
        let EG : Subgroup G := E.map P.subtype
        have hEG : IsElementaryAbelianOfRank p 3 EG :=
          hE.map_of_injective P.subtype P.subtype_injective
        exact hRankTwo.2.2 p ctx.p_prime
          ⟨EG, (Subgroup.map_subtype_le E).trans hPH, hEG⟩
      obtain ⟨U0, hU0⟩ := hTypeI.1.2.2.2.2
      have hUL : U ≤ w.L := hTypeI.1.2.2.1.2.1
      have hLnormH : w.L ≤ Subgroup.normalizer (H : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer (Fcore_sub w.L)).mp
          (Fcore_normal w.L)
      have hU0normP : U0 ≤ Subgroup.normalizer (P : Set G) :=
          (hU0.1.trans hUL).trans
          (hLnormH.trans
            (TypeSpecInternal.characteristic_map_subtype_le_normalizer16
              H (pCore p H)))
      let inclusionToNormalizer :
          U0 →* Subgroup.normalizer (P : Set G) :=
        { toFun := fun z ↦ ⟨z, hU0normP z.property⟩
          map_one' := rfl
          map_mul' := fun _ _ ↦ rfl }
      let action : U0 →* MulAut P :=
        P.normalizerMonoidHom.comp inclusionToNormalizer
      have hPne : P ≠ ⊥ := by
        intro hPbot
        apply hA.ne_bot
        rw [eq_bot_iff]
        exact (hAP0.trans hP0P).trans (by rw [hPbot])
      have hPnontrivial : Nontrivial P :=
        P.nontrivial_iff_ne_bot.mpr hPne
      obtain ⟨a, haP, haOne⟩ :=
        (Subgroup.nontrivial_iff_exists_ne_one P).mp hPnontrivial
      have hActionInjective : Function.Injective action := by
        rw [← MonoidHom.ker_eq_bot_iff]
        ext z
        change inclusionToNormalizer z ∈
            P.normalizerMonoidHom.ker ↔
          z ∈ (⊥ : Subgroup U0)
        rw [Subgroup.normalizerMonoidHom_ker]
        constructor
        · intro hzCentral
          apply Subgroup.mem_bot.mpr
          by_contra hzOne
          let J : Subgroup G := H ⊔ U0
          let zJ : U0.subgroupOf J :=
            ⟨⟨(z : G), (le_sup_right : U0 ≤ J) z.property⟩, z.property⟩
          let aJ : H.subgroupOf J :=
            ⟨⟨a, (le_sup_left : H ≤ J) (hPH haP)⟩, hPH haP⟩
          have hzJOne : zJ ≠ 1 := by
            intro hzJ
            apply hzOne
            apply Subtype.ext
            exact congrArg
              (fun t : U0.subgroupOf J ↦ (((t : J) : G))) hzJ
          have hza : Commute (z : G) a :=
            (Subgroup.mem_centralizer_iff.mp hzCentral a haP).symm
          have hfixed :
              (zJ : J) * (aJ : J) * (zJ : J)⁻¹ = (aJ : J) := by
            apply Subtype.ext
            change (z : G) * a * (z : G)⁻¹ = a
            calc
              (z : G) * a * (z : G)⁻¹ =
                  a * (z : G) * (z : G)⁻¹ := by rw [hza.eq]
              _ = a := by simp
          have haJOne := hU0.2.2.2.fixedPointFree
            zJ hzJOne aJ hfixed
          apply haOne
          exact congrArg
            (fun t : H.subgroupOf J ↦ (((t : J) : G))) haJOne
        · intro hzBot
          have hzOne : z = 1 := Subgroup.mem_bot.mp hzBot
          subst z
          simp
      have hqU0 : q ∣ Nat.card U0 := by
        apply hqExponent.trans
        rw [← hU0.2.1]
        exact Group.exponent_dvd_nat_card
      have hqAut : q ∣ Nat.card (MulAut P) :=
        hqU0.trans
          (Subgroup.card_dvd_of_injective action hActionInjective)
      exact (prime_dvd_mulAut_of_odd_pgroup_no_rank_three
        hPp hPodd hPnoRankThree hq hqAut hqp).2.1
    · have hqPred : q ∣ p - 1 :=
        hqExponent.trans (hExponent.1 p hpSupportH)
      have hpTwo : 2 ≤ p := ctx.p_prime.two_le
      exact lt_of_le_of_lt
        (Nat.le_of_dvd (by omega : 0 < p - 1) hqPred)
        (by omega)

/-- The second maximal subgroup is Frobenius with its Fitting core as
kernel. -/
private theorem second_maximal_frobenius12
    {p : ℕ} {M P0 : Subgroup G}
    (ctx : FTType1NonFrobeniusContext p M P0)
    (w : NonFrobeniusFTType1Witness p M P0) :
    ∃ E : Subgroup G,
      IsFrobeniusIn (Fitting_core w.L) E w.L := by
  classical
  have hTypeOne := second_maximal_type_one12 ctx w
  obtain ⟨U, hTypeI⟩ :=
    (FTtypeP 1 w.L w.L_maximal).mpr hTypeOne
  have hCoreUcop := typeF_core_complement_coprime12 hTypeI.1
  refine ⟨U, (typeF_context w.L U hTypeI.1).frobenius_iff_zgroup.mpr ?_⟩
  intro q hq Q
  have hQodd : Odd (Nat.card Q) :=
    Odd.of_dvd_nat (mFT_odd U)
      (Q : Subgroup U).card_subgroup_dvd_card
  apply (odd_pgroup_isCyclic_iff_no_elementaryAbelian_rank_two
    Q.isPGroup' hQodd).mpr
  rintro ⟨A, hA⟩
  let AU : Subgroup U := A.map (Q : Subgroup U).subtype
  let AG : Subgroup G := AU.map U.subtype
  have hAUrank : IsElementaryAbelianOfRank q 2 AU :=
    hA.map_of_injective (Q : Subgroup U).subtype
      (Q : Subgroup U).subtype_injective
  have hAGrank : IsElementaryAbelianOfRank q 2 AG :=
    hAUrank.map_of_injective U.subtype U.subtype_injective
  have hUL : U ≤ w.L := hTypeI.1.2.2.1.2.1
  have hAGL : AG ≤ w.L :=
    (Subgroup.map_subtype_le AU).trans hUL
  have hRankL : HasElementaryAbelianRankAtLeast q 2 w.L :=
    ⟨AG, hAGL, hAGrank⟩
  have hqA : q ∣ Nat.card A := by
    rw [hA.card_eq]
    exact dvd_pow_self q (by omega : 2 ≠ 0)
  have hqU : q ∣ Nat.card U :=
    (hqA.trans A.card_subgroup_dvd_card).trans
      (Q : Subgroup U).card_subgroup_dvd_card
  have hqLess : q < p :=
    typeOne_complement_prime_lt12 ctx w hTypeI hq.out hqU
  have hqCore := ctx.inductive_hypothesis
    hq.out hqLess w.L_maximal hTypeOne hRankL
  exact (Nat.not_coprime_of_dvd_of_dvd
    hq.out.one_lt hqCore.2 hqU) hCoreUcop

/-! ## Peterfalvi (12.11): the first maximal decomposition -/

/-- An ambient copy of a Sylow subgroup is maximal among the ambient
`p`-subgroups contained in the same overgroup. -/
private theorem ambientSylow_eq_of_le12
    {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (P : Sylow p H) {Q : Subgroup G}
    (hQp : IsPGroup p Q) (hQH : Q ≤ H)
    (hPQ : (P : Subgroup H).map H.subtype ≤ Q) :
    Q = (P : Subgroup H).map H.subtype := by
  let QH : Subgroup H := Q.subgroupOf H
  have hQHp : IsPGroup p QH :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQH).symm
  have hPQH : (P : Subgroup H) ≤ QH := by
    intro x hx
    exact hPQ ⟨x, hx, rfl⟩
  have hQHP : QH = (P : Subgroup H) :=
    P.is_maximal' hQHp hPQH
  calc
    Q = QH.map H.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le hQH).symm
    _ = (P : Subgroup H).map H.subtype :=
      congrArg (Subgroup.map H.subtype) hQHP

/-- An element commuting with `x` centralizes the cyclic subgroup generated
by `x`. -/
private theorem mem_elementCentralizer_of_commute12
    {Q : Type*} [Group Q] {x y : Q} (hxy : Commute x y) :
    x ∈ Subgroup.centralizer (Subgroup.zpowers y : Set Q) := by
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  exact (hxy.zpow_right n).symm

/-- The centralizer of a nonidentity Frobenius-kernel element is contained
in the kernel. -/
private theorem centralizer_frobeniusKernel_le12
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
  have hxcomm : Commute x z :=
    (Subgroup.mem_centralizer_iff.mp hx z
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

/-- Select a simple Maschke constituent while the representation is an
explicit parameter, so its group-algebra module instance remains visible. -/
private theorem exists_simple_maschke_submodule12
    {k H V : Type*} [Field k] [Group H] [Finite H]
    [AddCommGroup V] [Module k V] [Nontrivial V]
    [NeZero (Nat.card H : k)]
    (rho : Representation k H V) :
    ∃ m : Submodule (MonoidAlgebra k H) rho.asModule,
      IsSimpleModule (MonoidAlgebra k H) m ∧ Nontrivial m := by
  letI : Nontrivial rho.asModule :=
    Function.Injective.nontrivial rho.asModuleEquiv.symm.injective
  letI : IsSemisimpleModule (MonoidAlgebra k H) rho.asModule := by
    infer_instance
  obtain ⟨m, hm⟩ := IsSemisimpleModule.exists_simple_submodule
    (MonoidAlgebra k H) rho.asModule
  letI : IsSimpleModule (MonoidAlgebra k H) m := hm
  exact ⟨m, hm, IsSimpleModule.nontrivial (MonoidAlgebra k H) m⟩

/-- An elementary abelian `p`-group without a rank-three subgroup has
cardinality at most `p ^ 2`. -/
private theorem natCard_le_prime_sq_of_no_rank_three12
    {E : Type*} [Group E] [Finite E]
    {p : ℕ} [Fact p.Prime]
    (hEp : IsPGroup p E) (hcomm : IsMulCommutative E)
    (hpow : ∀ x : E, x ^ p = 1)
    (hrank : ¬ ∃ F : Subgroup E,
      IsElementaryAbelianOfRank p 3 F) :
    Nat.card E ≤ p ^ 2 := by
  classical
  letI : IsMulCommutative E := hcomm
  obtain ⟨n, hcard⟩ := hEp.exists_card_eq
  have hn : n ≤ 2 := by
    by_contra hnle
    have hthree : 3 ≤ n := by omega
    have htopcard : Nat.card (⊤ : Subgroup E) = p ^ n := by
      simpa using hcard
    obtain ⟨F, _hFtop, _hFnormal, hFcard⟩ :=
      exists_normal_subgroup_card_pow_le hEp (⊤ : Subgroup E)
        htopcard hthree
    apply hrank
    refine ⟨F,
      { isPGroup := hEp.to_subgroup F
        commutative := inferInstance
        pow_eq_one := ?_
        card_eq := hFcard }⟩
    intro x
    apply Subtype.ext
    exact hpow x
  rw [hcard]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hn

/-- The ambient image of `Omega_1(Z(P))` is nontrivial in a nontrivial
finite `p`-group. -/
private theorem omegaOneCenterAmbient_ne_bot12
    {K : Type*} [Group K] [Finite K]
    {p : ℕ} [Fact p.Prime] {P : Subgroup K}
    (hPp : IsPGroup p P) (hPne : P ≠ ⊥) :
    omegaOneCenterAmbient p P ≠ ⊥ := by
  letI : Nontrivial P := P.nontrivial_iff_ne_bot.mpr hPne
  let Z : Subgroup P := Subgroup.center P
  have hZne : Z ≠ ⊥ := by
    letI : Group.IsNilpotent P := hPp.isNilpotent
    exact Group.IsNilpotent.center_ne_bot P
  have hZp : IsPGroup p Z := hPp.to_subgroup Z
  have hZcard : Nat.card Z ≠ 1 :=
    (Z.one_lt_card_iff_ne_bot.mpr hZne).ne'
  have hOmegaNe : omegaOne p Z ≠ ⊥ :=
    omegaOne_ne_bot_of_isPGroup hZp hZcard
  have hCenterOmegaNe :
      Submission.OddOrder.BG.Section05.omegaOneCenter p P ≠ ⊥ := by
    dsimp [Submission.OddOrder.BG.Section05.omegaOneCenter, Z]
    exact (not_congr (Subgroup.map_eq_bot_iff_of_injective
      (omegaOne p (Subgroup.center P))
      (Subgroup.center P).subtype_injective)).mpr hOmegaNe
  dsimp [omegaOneCenterAmbient]
  exact (not_congr (Subgroup.map_eq_bot_iff_of_injective
    (Submission.OddOrder.BG.Section05.omegaOneCenter p P)
    P.subtype_injective)).mpr hCenterOmegaNe

/-- Orbit counting for a finite semiregular conjugation action. -/
private theorem semiregular_card_dvd_sub_one12
    {K : Type*} [Group K] [Finite K]
    {A R : Subgroup K}
    (hreg : IsSemiregularConjugation A R)
    (hnorm : R ≤ Subgroup.normalizer (A : Set K)) :
    Nat.card R ∣ Nat.card A - 1 := by
  letI := subgroupConjugationAction A R hnorm
  have hfixed : ∀ r : R, r ≠ 1 → ∀ a : A,
      r • a = a → a = 1 := by
    intro r hr a ha
    apply hreg r hr a
    simpa only [coe_subgroupConjugationAction_smul A R hnorm] using
      congrArg Subtype.val ha
  let t := Nat.card
    (nonidentityFixedOneOrbitQuotient (G := R) (X := A))
  have hcard : Nat.card A = 1 + t * Nat.card R := by
    simpa [t] using natCard_eq_one_add_fixedOneOrbits_mul_natCard
      (G := R) (X := A) (fun r ↦ smul_one r) hfixed
  refine ⟨t, ?_⟩
  rw [hcard]
  simp [Nat.mul_comm]

/-- The Summary-II complement attached to `w.x` is exactly `M ∩ w.L`. -/
private theorem fitting_complement_at_first_maximal12
    {p : ℕ} {M P0 E : Subgroup G}
    (ctx : FTType1NonFrobeniusContext p M P0)
    (w : NonFrobeniusFTType1Witness p M P0)
    (hFrob : IsFrobeniusIn (Fitting_core w.L) E w.L) :
    IsInternalSemidirectProductIn
      (Fitting_core M) (M ⊓ w.L) M := by
  classical
  let frobCtx : FTFrobeniusContext w.L :=
    ⟨w.L_maximal, ⟨E, hFrob⟩⟩
  have hTypeOne : FTtype w.L = 1 :=
    FT_Frobenius_type1 frobCtx
  have hxH : w.x ∈ Fitting_core w.L :=
    p0_le_second_fitting12_impl ctx w (witness_x_mem_p0_12 w)
  have hxSupport : w.x ∈ FTsupport w.L := by
    rw [show FTsupport w.L =
        subgroupNonidentity (Fitting_core w.L) by
      simpa only using FTsupp_Frobenius frobCtx]
    exact ⟨hxH, w.x_ne_one⟩
  have hxSupport0 : w.x ∈ FTsupport0 w.L := by
    rw [FTsupp0_type1 w.L hTypeOne]
    exact hxSupport
  let data := (FTsupport_facts w.L w.L_maximal).element_data w.x
    ⟨hxSupport0, w.centralizer_not_le_L⟩
  have hcentralizerM : elementCentralizer w.x ≤ M :=
    (Subgroup.centralizer_le_normalizer
      (Subgroup.zpowers w.x : Set G)).trans w.normalizer_le_M
  have hMnormalizer : M = elementNormalizer15 w.x :=
    eq_uniq_mmax data.unique_maximal_centralizer
      ctx.M_type_context.maxL hcentralizerM
  simpa only [← hMnormalizer, inf_comm] using
    data.fittingCore_complement

/-- A Frobenius presentation of the first maximal subgroup would force its
rank-two Sylow subgroup to be cyclic. -/
private theorem first_maximal_not_frobenius12_impl
    {p : ℕ} {M P0 : Subgroup G}
    (ctx : FTType1NonFrobeniusContext p M P0)
    (w : NonFrobeniusFTType1Witness p M P0) :
    ¬ ∃ E : Subgroup G,
      IsFrobeniusIn (Fitting_core M) E M := by
  classical
  letI : Fact p.Prime := ⟨ctx.p_prime⟩
  rintro ⟨E, hFrob⟩
  let K := Fitting_core M
  let pi := primeSupport (Nat.card K)
  have hTypeF : of_typeF M E := Frobenius_of_typeF M E hFrob
  have hZE8 : IsZGroup8 E :=
    (typeF_context M E hTypeF).frobenius_iff_zgroup.mp hFrob
  letI : IsZGroup E :=
    ⟨fun q hq Q ↦ by
      letI : Fact q.Prime := ⟨hq⟩
      exact hZE8 q Q⟩
  have hEM : E ≤ M := le_sup_right.trans_eq hFrob.1
  have hKHall : IsHall pi (K.subgroupOf M) := by
    simpa only [K, pi] using Fcore_Hall M
  have hsdM : IsInternalSemidirectProductIn K E M := by
    rw [← hFrob.1]
    simpa only [K] using hFrob.2.1
  have hComplement :
      (K.subgroupOf M).IsComplement' (E.subgroupOf M) := by
    exact hsdM.2.2.2
  have hEHall : IsHall piᶜ (E.subgroupOf M) := by
    constructor
    · rw [← hComplement.symm.index_eq_card]
      exact hKHall.isPiNumber_index
    · rw [hComplement.index_eq_card]
      simpa only [compl_compl] using hKHall.isPiNumber_card
  have hpCompl : p ∈ piᶜ := by
    intro hpK
    exact (ctx.p_prime.coprime_iff_not_dvd.mp ctx.core_p_prime) hpK.2
  have hP0pi : IsPiNumber piᶜ (Nat.card P0) :=
    ctx.sylow_P0.isPGroup.isPiNumber_natCard hpCompl
  obtain ⟨m, hP0Em, -, -, -, -, -⟩ :=
    exists_ambient_isHall_map_conj_ge_of_isSolvable
      (witness_p0_le_M12 ctx) hEM
      (mmax_sol ctx.M_type_context.maxL) hP0pi hEHall
  let E' : Subgroup G :=
    E.map (MulAut.conj (m : G)).toMonoidHom
  let eE : E ≃* E' :=
    E.equivMapOfInjective (MulAut.conj (m : G)).toMonoidHom
      (MulAut.conj (m : G)).injective
  letI : IsZGroup E' :=
    IsZGroup.of_injective (f := eE.symm.toMonoidHom) eE.symm.injective
  have hP0p : IsPGroup p (P0.subgroupOf E') :=
    ctx.sylow_P0.isPGroup.comap_subtype
  have hP0subCyclic : IsCyclic (P0.subgroupOf E') :=
    hP0p.isCyclic_of_isZGroup
  let eP0 : P0.subgroupOf E' ≃* P0 :=
    Subgroup.subgroupOfEquivOfLe hP0Em
  exact witness_p0_not_cyclic12 ctx w
    (eP0.isCyclic.mp hP0subCyclic)

/-- Peterfalvi (12.11): the complement supplied by Summary II for the first
maximal subgroup lies in the Fitting core of the second maximal subgroup. -/
private theorem intersection_le_second_fitting12
    {p : ℕ} {M P0 E : Subgroup G}
    (ctx : FTType1NonFrobeniusContext p M P0)
    (w : NonFrobeniusFTType1Witness p M P0)
    (hFrob : IsFrobeniusIn (Fitting_core w.L) E w.L) :
    M ⊓ w.L ≤ Fitting_core w.L := by
  classical
  letI : Fact p.Prime := ⟨ctx.p_prime⟩
  let H := Fitting_core w.L
  let K := Fitting_core M
  let I := M ⊓ w.L
  have hP0H : P0 ≤ H := p0_le_second_fitting12_impl ctx w
  have hP0M : P0 ≤ M := witness_p0_le_M12 ctx
  have hP0I : P0 ≤ I :=
    le_inf hP0M (hP0H.trans (Fcore_sub w.L))
  have hIL : I ≤ w.L := inf_le_right
  have hIM : I ≤ M := inf_le_left
  have hHnormal : (H.subgroupOf w.L).Normal := by
    dsimp only [H]
    infer_instance
  have hHHall : IsHall (primeSupport (Nat.card H))
      (H.subgroupOf w.L) := by
    simpa only [H] using Fcore_Hall w.L
  apply le_normal_isHall_of_isPiNumber12 hHnormal hHHall hIL
  intro q hq hqI
  by_contra hqH
  letI : Fact q.Prime := ⟨hq⟩
  have hqNotDvdH : ¬ q ∣ Nat.card H := by
    intro hqDvd
    exact hqH ⟨hq, hqDvd⟩
  obtain ⟨z, hzOrder⟩ :=
    exists_prime_orderOf_dvd_card' (G := I) q hqI
  have hzOrderG : orderOf (z : G) = q :=
    (orderOf_injective I.subtype I.subtype_injective z).trans hzOrder
  have hzNe : (z : G) ≠ 1 := by
    intro hzOne
    have : orderOf (z : G) = 1 := orderOf_eq_one_iff.mpr hzOne
    rw [hzOrderG] at this
    exact hq.ne_one this
  let A : Subgroup G := Subgroup.zpowers (z : G)
  have hAI : A ≤ I := Subgroup.zpowers_le.mpr z.property
  have hAM : A ≤ M := hAI.trans hIM
  have hAL : A ≤ w.L := hAI.trans hIL
  have hAcard : Nat.card A = q := by
    simpa only [A, Nat.card_zpowers] using hzOrderG
  have hAp : IsPGroup q A := by
    apply IsPGroup.of_card (n := 1)
    simpa only [pow_one] using hAcard
  have hAne : A ≠ ⊥ := by
    intro hAbot
    apply hzNe
    apply Subgroup.mem_bot.mp
    rw [← hAbot]
    exact Subgroup.mem_zpowers (z : G)

  let P : Subgroup G := (pCore p H).map H.subtype
  have hPH : P ≤ H := Subgroup.map_subtype_le _
  have hPp : IsPGroup p P := by
    simpa only [P] using pCore_isPGroup.map H.subtype
  have hP0P : P0 ≤ P := by
    letI : Group.IsNilpotent H := Fcore_nil w.L
    have hP0Hp : IsPGroup p (P0.subgroupOf H) :=
      ctx.sylow_P0.isPGroup.comap_subtype
    have hP0core : P0.subgroupOf H ≤ pCore p H :=
      hP0Hp.le_pCore_of_isNilpotent
    rw [← Subgroup.map_subgroupOf_eq_of_le hP0H]
    exact Subgroup.map_mono hP0core
  obtain ⟨PM, hPM⟩ := ctx.sylow_P0
  have hPinfM : (P ⊓ M : Subgroup G) = P0 := by
    have hInfp : IsPGroup p (P ⊓ M : Subgroup G) :=
      hPp.to_le inf_le_left
    have hEq := ambientSylow_eq_of_le12 PM hInfp inf_le_right (by
      rw [← hPM]
      exact le_inf hP0P hP0M)
    exact hEq.trans hPM.symm
  have hLnormH : w.L ≤ Subgroup.normalizer (H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Fcore_sub w.L)).mp
      (Fcore_normal w.L)
  have hLnormP : w.L ≤ Subgroup.normalizer (P : Set G) :=
    hLnormH.trans
      (TypeSpecInternal.characteristic_map_subtype_le_normalizer16
        H (pCore p H))
  have hAnormP0 : A ≤ Subgroup.normalizer (P0 : Set G) := by
    rw [← hPinfM]
    exact
      (le_inf (hAL.trans hLnormP) (hAM.trans Subgroup.le_normalizer)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
  have hAHcop : Nat.Coprime (Nat.card H) (Nat.card A) := by
    rw [hAcard]
    exact (hq.coprime_iff_not_dvd.mpr hqNotDvdH).symm
  have hAHdis : Disjoint H A :=
    Subgroup.disjoint_of_coprime_natCard hAHcop
  have hregP0A : IsSemiregularConjugation P0 A := by
    intro a ha k hfix
    by_contra hkOne
    let J : Subgroup G := Fitting_core w.L ⊔ E
    have haJ : (a : G) ∈ J := by
      change (a : G) ∈ Fitting_core w.L ⊔ E
      rw [hFrob.1]
      exact hAL a.property
    let aJ : J := ⟨(a : G), haJ⟩
    let kJ : (Fitting_core w.L).subgroupOf J :=
      ⟨⟨(k : G), (le_sup_left : Fitting_core w.L ≤ J)
          (hP0H k.property)⟩,
        hP0H k.property⟩
    have hkJne : (kJ : J) ≠ 1 := by
      intro hkJone
      apply hkOne
      apply Subtype.ext
      exact congrArg (fun t : J ↦ (t : G)) hkJone
    have hak : Commute aJ (kJ : J) := by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mp hfix
    have haCent : aJ ∈
        Subgroup.centralizer (Subgroup.zpowers (kJ : J) : Set J) :=
      mem_elementCentralizer_of_commute12 hak
    have haKernel : aJ ∈ (Fitting_core w.L).subgroupOf J :=
      centralizer_frobeniusKernel_le12 hFrob.2.2 kJ.property hkJne haCent
    have haInf : (a : G) ∈ H ⊓ A := ⟨haKernel, a.property⟩
    rw [disjoint_iff.mp hAHdis] at haInf
    exact ha (Subtype.ext (Subgroup.mem_bot.mp haInf))
  have hP0ne : P0 ≠ ⊥ := by
    intro hP0bot
    apply witness_p0_not_cyclic12 ctx w
    rw [hP0bot]
    infer_instance
  have hFrobP0A : IsFrobeniusDecomposition
      (P0.subgroupOf (P0 ⊔ A : Subgroup G))
      (A.subgroupOf (P0 ⊔ A : Subgroup G)) := by
    have hsupEq : A ⊔ P0 = P0 ⊔ A := sup_comm A P0
    rw [← hsupEq]
    exact hregP0A.isFrobeniusDecomposition_sup hAnormP0 hP0ne hAne

  have hsdI : IsInternalSemidirectProductIn K I M := by
    simpa only [K, I] using
      fitting_complement_at_first_maximal12 ctx w hFrob
  obtain ⟨U, hTypeI⟩ :=
    (FTtypeP 1 M ctx.M_type_context.maxL).mpr
      ctx.M_type_context.type_one
  have hTypeFI : of_typeF M I := by
    apply compl_of_typeF M I U hsdI hTypeI.1
  have hKIcop : Nat.Coprime (Nat.card K) (Nat.card I) := by
    simpa only [K] using typeF_core_complement_coprime12 hTypeFI
  have hsupI : (P0 ⊔ A : Subgroup G) ≤ I := sup_le hP0I hAI
  have hsupNormK : (P0 ⊔ A : Subgroup G) ≤
      Subgroup.normalizer (K : Set G) := by
    have hMnormK : M ≤ Subgroup.normalizer (K : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (Fcore_sub M)).mp
        (Fcore_normal M)
    exact hsupI.trans (hIM.trans hMnormK)
  have hKsupCop : Nat.Coprime (Nat.card K)
      (Nat.card (P0 ⊔ A : Subgroup G)) :=
    hKIcop.coprime_dvd_right (Subgroup.card_dvd_of_le hsupI)
  have hKsol : IsSolvable K := by
    letI : Group.IsNilpotent K := Fcore_nil M
    infer_instance
  have hCAne : centralizerWithin K A ≠ ⊥ := by
    intro hCAbot
    have hP0centK : P0 ≤ Subgroup.centralizer (K : Set G) :=
      (Frobenius_Wielandt_fixpoint hFrobP0A hsupNormK hKsupCop hKsol).2.1
        hCAbot
    obtain ⟨U0, hU0⟩ := hTypeFI.2.2.2.2
    obtain ⟨x0, hx0Omega, hx0⟩ := w.x_mem_omega
    letI : IsMulCommutative P0 := w.P0_abelian
    have hx0pow : x0 ^ p = 1 := by
      apply omegaOne_pow_eq_one_of_mul_closed p
      · intro a b ha hb
        rw [mul_pow, ha, hb, mul_one]
      · exact hx0Omega
    have hxpow : w.x ^ p = 1 := by
      rw [← hx0]
      exact congrArg P0.subtype hx0pow
    have hxOrder : orderOf w.x = p :=
      orderOf_eq_prime hxpow w.x_ne_one
    let xI : I := ⟨w.x, hP0I (witness_x_mem_p0_12 w)⟩
    have hxIOrder : orderOf xI = p :=
      (orderOf_injective I.subtype I.subtype_injective xI).symm.trans
        hxOrder
    have hpExpI : p ∣ Monoid.exponent I := by
      rw [← hxIOrder]
      exact Monoid.order_dvd_exponent xI
    have hpU0 : p ∣ Nat.card U0 := by
      have hpExpU0 : p ∣ Monoid.exponent U0 := by
        simpa only [hU0.2.1] using hpExpI
      exact hpExpU0.trans Group.exponent_dvd_nat_card
    obtain ⟨u, huOrder⟩ :=
      exists_prime_orderOf_dvd_card' (G := U0) p hpU0
    have huOrderG : orderOf (u : G) = p :=
      (orderOf_injective U0.subtype U0.subtype_injective u).trans huOrder
    have huNe : (u : G) ≠ 1 := by
      intro huOne
      have : orderOf (u : G) = 1 := orderOf_eq_one_iff.mpr huOne
      rw [huOrderG] at this
      exact ctx.p_prime.ne_one this
    let P1 : Subgroup G := Subgroup.zpowers (u : G)
    have hP1U0 : P1 ≤ U0 := Subgroup.zpowers_le.mpr u.property
    have hP1M : P1 ≤ M := (hP1U0.trans hU0.1).trans hIM
    have hP1card : Nat.card P1 = p := by
      simpa only [P1, Nat.card_zpowers] using huOrderG
    have hP1p : IsPGroup p P1 := by
      apply IsPGroup.of_card (n := 1)
      simpa only [pow_one] using hP1card
    have hP1ne : P1 ≠ ⊥ := by
      intro hP1bot
      apply huNe
      apply Subgroup.mem_bot.mp
      rw [← hP1bot]
      exact Subgroup.mem_zpowers (u : G)
    obtain ⟨m, hm⟩ :=
      exists_conjugate_le_sylow_map PM hP1M hP1p
    have hmP0 : ∀ a : G, a ∈ P1 →
        (m : G) * a * (m : G)⁻¹ ∈ P0 := by
      intro a ha
      rw [hPM]
      exact hm a ha
    have hMnormK : M ≤ Subgroup.normalizer (K : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (Fcore_sub M)).mp
        (Fcore_normal M)
    have hP1centK : P1 ≤ Subgroup.centralizer (K : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hmk : (m : G) * k * (m : G)⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hMnormK m.property) k).mp hk
      have hma := hmP0 a ha
      have hcommConj : Commute
          ((m : G) * a * (m : G)⁻¹)
          ((m : G) * k * (m : G)⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp (hP0centK hma)
          ((m : G) * k * (m : G)⁻¹) hmk).symm
      exact ((Commute.conj_iff (m : G)).mp hcommConj).symm.eq
    have hKnontrivial : Nontrivial K :=
      K.nontrivial_iff_ne_bot.mpr (by simpa only [K] using hTypeFI.1)
    obtain ⟨k, hkK, hkNe⟩ :=
      (Subgroup.nontrivial_iff_exists_ne_one K).mp hKnontrivial
    have hP1nontrivial : Nontrivial P1 :=
      P1.nontrivial_iff_ne_bot.mpr hP1ne
    obtain ⟨a, haP1, haNe⟩ :=
      (Subgroup.nontrivial_iff_exists_ne_one P1).mp hP1nontrivial
    let J : Subgroup G := K ⊔ U0
    let aJ : U0.subgroupOf J :=
      ⟨⟨a, (le_sup_right : U0 ≤ J) (hP1U0 haP1)⟩, hP1U0 haP1⟩
    let kJ : K.subgroupOf J :=
      ⟨⟨k, (le_sup_left : K ≤ J) hkK⟩, hkK⟩
    have haJNe : aJ ≠ 1 := by
      intro haOne
      exact haNe (congrArg (fun t : U0.subgroupOf J ↦ (((t : J) : G))) haOne)
    have hkJNe : kJ ≠ 1 := by
      intro hkOne
      exact hkNe (congrArg (fun t : K.subgroupOf J ↦ (((t : J) : G))) hkOne)
    have hak : Commute a k :=
      (Subgroup.mem_centralizer_iff.mp (hP1centK haP1) k hkK).symm
    have hfix : (aJ : J) * (kJ : J) * (aJ : J)⁻¹ = (kJ : J) := by
      apply Subtype.ext
      calc
        a * k * a⁻¹ = k * a * a⁻¹ := by rw [hak.eq]
        _ = k := by simp
    exact hkJNe (hU0.2.2.2.fixedPointFree aJ haJNe kJ hfix)

  have hCAnontrivial : Nontrivial (centralizerWithin K A) :=
    (centralizerWithin K A).nontrivial_iff_ne_bot.mpr hCAne
  obtain ⟨y, hyCA, hyNe⟩ :=
    (Subgroup.nontrivial_iff_exists_ne_one (centralizerWithin K A)).mp
      hCAnontrivial
  obtain ⟨U1, hU1⟩ := hTypeFI.2.2.2.1
  have hAU1 : A ≤ U1 := by
    intro a ha
    apply hU1.2.2.2 y ⟨hyCA.1, hyNe⟩
    refine ⟨hAI ha, ?_⟩
    exact mem_elementCentralizer_of_commute12
      (Subgroup.mem_centralizer_iff.mp hyCA.2 a ha)
  obtain ⟨y', hyCent, hyNotDerived⟩ :=
    SetLike.not_le_iff_exists.mp w.core_centralizer_not_le_derived
  have hy'Ne : y' ≠ 1 := by
    intro hyOne
    apply hyNotDerived
    rw [hyOne]
    exact (derivedWithin K).one_mem
  have hxU1 : w.x ∈ U1 := by
    apply hU1.2.2.2 y' ⟨hyCent.1, hy'Ne⟩
    refine ⟨hP0I (witness_x_mem_p0_12 w), ?_⟩
    exact mem_elementCentralizer_of_commute12
      (Subgroup.mem_centralizer_iff.mp hyCent.2 w.x
        (Subgroup.mem_zpowers w.x))
  have hAcommX : ∀ a : G, a ∈ A → Commute a w.x := by
    intro a ha
    have hcomm := isMulCommutative_iff.mp hU1.2.2.1
      (⟨a, hAU1 ha⟩ : U1) (⟨w.x, hxU1⟩ : U1)
    exact congrArg Subtype.val hcomm
  have hAH : A ≤ H := by
    intro a ha
    let J : Subgroup G := Fitting_core w.L ⊔ E
    have haJmem : a ∈ J := by
      change a ∈ Fitting_core w.L ⊔ E
      rw [hFrob.1]
      exact hAL ha
    let aJ : J := ⟨a, haJmem⟩
    let xJ : (Fitting_core w.L).subgroupOf J :=
      ⟨⟨w.x, (le_sup_left : Fitting_core w.L ≤ J)
          (hP0H (witness_x_mem_p0_12 w))⟩,
        hP0H (witness_x_mem_p0_12 w)⟩
    have hxJNe : (xJ : J) ≠ 1 := by
      intro hxOne
      exact w.x_ne_one
        (congrArg (fun t : J ↦ (t : G)) hxOne)
    have haCent : aJ ∈
        Subgroup.centralizer (Subgroup.zpowers (xJ : J) : Set J) := by
      apply mem_elementCentralizer_of_commute12
      apply Subtype.ext
      exact (hAcommX a ha).eq
    exact centralizer_frobeniusKernel_le12
      hFrob.2.2 xJ.property hxJNe haCent
  have hqDvdH : q ∣ Nat.card H := by
    rw [← hzOrderG]
    exact H.orderOf_dvd_natCard (hAH (Subgroup.mem_zpowers (z : G)))
  exact hqH ⟨hq, hqDvdH⟩

/-! ## Peterfalvi (12.12): the second Frobenius complement -/

/-- The Frobenius complement at the second maximal subgroup is cyclic, and
its order divides one of the two adjacent integers `p - 1` and `p + 1`. -/
private theorem second_complement_cyclic_divisibility12
    {p : ℕ} {M P0 E : Subgroup G}
    (ctx : FTType1NonFrobeniusContext p M P0)
    (w : NonFrobeniusFTType1Witness p M P0)
    (hFrob : IsFrobeniusIn (Fitting_core w.L) E w.L) :
    IsCyclic E ∧
      (Nat.card E ∣ p - 1 ∨ Nat.card E ∣ p + 1) := by
  classical
  letI : Fact p.Prime := ⟨ctx.p_prime⟩
  let H := Fitting_core w.L
  let I := M ⊓ w.L
  let P : Subgroup G := (pCore p H).map H.subtype
  let T : Subgroup G := omegaOneCenterAmbient p P
  let W0 : Subgroup P0 := omegaOne p P0
  let W : Subgroup G := W0.map P0.subtype

  have hP0H : P0 ≤ H := p0_le_second_fitting12_impl ctx w
  have hP0M : P0 ≤ M := witness_p0_le_M12 ctx
  have hP0I : P0 ≤ I :=
    le_inf hP0M (hP0H.trans (Fcore_sub w.L))
  have hEL : E ≤ w.L := by
    rw [← hFrob.1]
    exact le_sup_right
  have hLnormH : w.L ≤ Subgroup.normalizer (H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Fcore_sub w.L)).mp
      (Fcore_normal w.L)
  have hEnormH : E ≤ Subgroup.normalizer (H : Set G) :=
    hEL.trans hLnormH

  have hregHE : IsSemiregularConjugation H E := by
    intro e he h hfix
    let J : Subgroup G := H ⊔ E
    let eJ : E.subgroupOf J :=
      ⟨⟨(e : G), (le_sup_right : E ≤ J) e.property⟩, e.property⟩
    let hJ : H.subgroupOf J :=
      ⟨⟨(h : G), (le_sup_left : H ≤ J) h.property⟩, h.property⟩
    have heJ : eJ ≠ 1 := by
      intro heOne
      apply he
      apply Subtype.ext
      exact congrArg
        (fun z : E.subgroupOf J ↦ (((z : J) : G))) heOne
    have hfixJ :
        (eJ : J) * (hJ : J) * (eJ : J)⁻¹ = hJ := by
      apply Subtype.ext
      exact hfix
    have hhOne := hFrob.2.2.fixedPointFree eJ heJ hJ hfixJ
    apply Subtype.ext
    exact congrArg
      (fun z : H.subgroupOf J ↦ (((z : J) : G))) hhOne
  have hHEcop : Nat.Coprime (Nat.card H) (Nat.card E) :=
    hregHE.natCard_coprime hEnormH
  have hHEdis : Disjoint H E :=
    Subgroup.disjoint_of_coprime_natCard hHEcop

  have hPp : IsPGroup p P := by
    simpa only [P] using pCore_isPGroup.map H.subtype
  have hPH : P ≤ H := Subgroup.map_subtype_le _
  have hP0P : P0 ≤ P := by
    letI : Group.IsNilpotent H := Fcore_nil w.L
    have hP0Hp : IsPGroup p (P0.subgroupOf H) :=
      ctx.sylow_P0.isPGroup.comap_subtype
    have hP0core : P0.subgroupOf H ≤ pCore p H :=
      hP0Hp.le_pCore_of_isNilpotent
    rw [← Subgroup.map_subgroupOf_eq_of_le hP0H]
    exact Subgroup.map_mono hP0core
  obtain ⟨PM, hPM⟩ := ctx.sylow_P0
  have hPinfM : (P ⊓ M : Subgroup G) = P0 := by
    have hInfp : IsPGroup p (P ⊓ M : Subgroup G) :=
      hPp.to_le inf_le_left
    have hEq := ambientSylow_eq_of_le12 PM hInfp inf_le_right (by
      rw [← hPM]
      exact le_inf hP0P hP0M)
    exact hEq.trans hPM.symm

  have hTcenter : T ≤ centerWithin P := by
    simpa only [T] using omegaOneCenterAmbient_le_centerWithin p P
  have hTP : T ≤ P := hTcenter.trans (centralizerWithin_le_left P P)
  have hTcentX : T ≤
      Subgroup.centralizer (Subgroup.zpowers w.x : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hxt : Commute w.x t :=
      Subgroup.mem_centralizer_iff.mp (hTcenter ht).2 w.x
        (hP0P (witness_x_mem_p0_12 w))
    exact (hxt.zpow_left n).eq
  have hTM : T ≤ M :=
    hTcentX.trans
      ((Subgroup.centralizer_le_normalizer
        (Subgroup.zpowers w.x : Set G)).trans w.normalizer_le_M)
  have hTP0 : T ≤ P0 := by
    intro t ht
    have htInf : t ∈ P ⊓ M := ⟨hTP ht, hTM ht⟩
    rw [hPinfM] at htInf
    exact htInf

  letI : IsMulCommutative P0 := w.P0_abelian
  have hTcomm : IsMulCommutative T := by
    apply isMulCommutative_iff.mpr
    intro a b
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hTcenter a.property).2
      b (hTcenter b.property).1).symm
  letI : IsMulCommutative T := hTcomm
  have hTpow : ∀ t : T, t ^ p = 1 := by
    intro t
    rcases t.property with ⟨z, hz, hzt⟩
    have hzpow :=
      Submission.OddOrder.BG.Section05.omegaOneCenter_pow_eq_one
        (G := P) p ⟨z, hz⟩
    apply Subtype.ext
    change (t : G) ^ p = 1
    rw [← hzt]
    exact congrArg Subtype.val (congrArg Subtype.val hzpow)
  have hWP0 : W ≤ P0 := Subgroup.map_subtype_le W0
  have hWp : IsPGroup p W :=
    ctx.sylow_P0.isPGroup.to_le hWP0
  have hWcomm : IsMulCommutative W := by
    apply isMulCommutative_iff.mpr
    intro a b
    apply Subtype.ext
    change (a : G) * (b : G) = (b : G) * (a : G)
    exact congrArg (fun z : P0 => (z : G))
      (isMulCommutative_iff.mp w.P0_abelian
        (⟨a, hWP0 a.property⟩ : P0)
        (⟨b, hWP0 b.property⟩ : P0))
  have hWpow : ∀ z : W, z ^ p = 1 := by
    intro z
    rcases z.property with ⟨z0, hz0, hz⟩
    apply Subtype.ext
    change (z : G) ^ p = 1
    rw [← hz]
    exact congrArg P0.subtype
      (omegaOne_pow_eq_one_of_mul_closed p (by
        intro a b ha hb
        rw [mul_pow, ha, hb, mul_one]) hz0)
  have hTW : T ≤ W := by
    intro t ht
    refine ⟨⟨t, hTP0 ht⟩, ?_, rfl⟩
    apply mem_omegaOne_of_pow_eq_one p
    apply Subtype.ext
    change t ^ p = 1
    exact congrArg (fun z : T => (z : G)) (hTpow ⟨t, ht⟩)

  obtain ⟨A0, hA0P0, hA0⟩ := w.P0_rank_two.1
  have hA0W : A0 ≤ W := by
    intro a ha
    refine ⟨⟨a, hA0P0 ha⟩, ?_, rfl⟩
    apply mem_omegaOne_of_pow_eq_one p
    apply Subtype.ext
    change a ^ p = 1
    exact congrArg (fun z : A0 => (z : G))
      (hA0.pow_eq_one ⟨a, ha⟩)
  have hWlower : p ^ 2 ≤ Nat.card W := by
    rw [← hA0.card_eq]
    exact Nat.le_of_dvd (Nat.card_pos)
      (Subgroup.card_dvd_of_le hA0W)
  have hWnoRank : ¬ ∃ F : Subgroup W,
      IsElementaryAbelianOfRank p 3 F := by
    rintro ⟨F, hF⟩
    apply w.P0_rank_two.2
    let FG : Subgroup G := F.map W.subtype
    refine ⟨FG, ?_, ?_⟩
    · exact (Subgroup.map_subtype_le F).trans
        (Subgroup.map_subtype_le W0)
    · exact hF.map_of_injective W.subtype W.subtype_injective
  have hWupper : Nat.card W ≤ p ^ 2 :=
    natCard_le_prime_sq_of_no_rank_three12 hWp hWcomm hWpow hWnoRank
  have hWcard : Nat.card W = p ^ 2 :=
    le_antisymm hWupper hWlower
  have hPne : P ≠ ⊥ := by
    intro hPbot
    have hP0bot : P0 = ⊥ := le_bot_iff.mp (hP0P.trans_eq hPbot)
    exact witness_p0_not_cyclic12 ctx w (by rw [hP0bot]; infer_instance)
  have hTne : T ≠ ⊥ :=
    omegaOneCenterAmbient_ne_bot12 hPp hPne

  have hLnormP : w.L ≤ Subgroup.normalizer (P : Set G) :=
    hLnormH.trans
      (TypeSpecInternal.characteristic_map_subtype_le_normalizer16
        H (pCore p H))
  have hNormPT : Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer (T : Set G) := by
    let R : Subgroup P :=
      Submission.OddOrder.BG.Section05.omegaOneCenter p P
    haveI : R.Characteristic := by
      dsimp [R]
      infer_instance
    simpa only [T, omegaOneCenterAmbient, R] using
      TypeSpecInternal.characteristic_map_subtype_le_normalizer16 P R
  have hEnormT : E ≤ Subgroup.normalizer (T : Set G) :=
    hEL.trans (hLnormP.trans hNormPT)
  have hregTE : IsSemiregularConjugation T E :=
    hregHE.mono_left (hTP.trans hPH)
  have hTEcop : Nat.Coprime (Nat.card T) (Nat.card E) :=
    hregTE.natCard_coprime hEnormT
  have hTp : IsPGroup p T := hPp.to_le hTP
  have hpT : p ∣ Nat.card T :=
    hTp.card_eq_or_dvd.resolve_left
      (fun hcard ↦ hTne (Subgroup.card_eq_one.mp hcard))
  have hpE : ¬ p ∣ Nat.card E :=
    ctx.p_prime.coprime_iff_not_dvd.mp
      (hTEcop.coprime_dvd_left hpT)

  letI : Nontrivial T := T.nontrivial_iff_ne_bot.mpr hTne
  letI : Module (ZMod p) (Additive T) :=
    elementaryAbelianZModModule T p hTpow
  letI : MulDistribMulAction E T :=
    subgroupConjugationAction T E hEnormT
  let action : E →* MulAut T := MulDistribMulAction.toMulAut E T
  let rho : Representation (ZMod p) E (Additive T) :=
    elementaryAbelianActionRepresentation T E p action
  letI : NeZero (Nat.card E : ZMod p) :=
    NeZero.of_not_dvd (ZMod p) hpE
  obtain ⟨m, hm, hmNontrivial⟩ :=
    exists_simple_maschke_submodule12 rho
  let V : Subrepresentation rho := Subrepresentation.ofSubmodule' m
  let V0 : Type := {x : Additive T // x ∈ m}
  letI V0AddCommGroup : AddCommGroup V0 :=
    Submodule.addCommGroup V.toSubmodule
  letI V0Module : Module (ZMod p) V0 :=
    Submodule.module V.toSubmodule
  let rhoV : Representation (ZMod p) E V0 := V.toRepresentation
  have hrhoVIrreducible :=
    (irreducible_toRepresentation_iff_isSimpleModule_asSubmodule
      rho V).mpr hm
  letI rhoVIrreducible : Representation.IsIrreducible rhoV := by
    change Representation.IsIrreducible V.toRepresentation
    exact hrhoVIrreducible
  letI : Nontrivial m := hmNontrivial
  letI : Nontrivial V0 := by
    change Nontrivial ↥m
    exact hmNontrivial

  have hrhoV : Function.Injective rhoV := by
    intro a b hab
    obtain ⟨v, hv⟩ := exists_ne (0 : V0)
    have hfixV : rhoV (b⁻¹ * a) v = v := by
      rw [map_mul]
      change rhoV b⁻¹ (rhoV a v) = v
      rw [hab]
      simp
    have hfixAdd := congrArg Subtype.val hfixV
    change Additive.ofMul ((b⁻¹ * a) • v.1.toMul) = v.1 at hfixAdd
    have hfixTsub : (b⁻¹ * a) • v.1.toMul = v.1.toMul :=
      congrArg Additive.toMul hfixAdd
    have hfixAmbient :
        ((b⁻¹ * a : E) : G) * (v.1.toMul : G) *
            ((b⁻¹ * a : E) : G)⁻¹ = (v.1.toMul : G) := by
      calc
        ((b⁻¹ * a : E) : G) * (v.1.toMul : G) *
              ((b⁻¹ * a : E) : G)⁻¹ =
            (((b⁻¹ * a) • v.1.toMul : T) : G) :=
          (coe_subgroupConjugationAction_smul
            T E hEnormT (b⁻¹ * a) v.1.toMul).symm
        _ = (v.1.toMul : G) := congrArg Subtype.val hfixTsub
    have hbaOne : b⁻¹ * a = 1 := by
      by_contra hba
      have hvOne := hregTE (b⁻¹ * a) hba v.1.toMul hfixAmbient
      apply hv
      apply Subtype.ext
      exact congrArg Additive.ofMul hvOne
    exact (inv_mul_eq_one.mp hbaOne).symm

  let VT : Subgroup T := actionSubmoduleSubgroup action m
  let VG : Subgroup G := VT.map T.subtype
  let eVT : VT ≃ V0 :=
    { toFun := fun t ↦
        ⟨Additive.ofMul (t : T),
          (mem_actionSubmoduleSubgroup action m (t : T)).mp t.property⟩
      invFun := fun v ↦
        ⟨v.1.toMul,
          (mem_actionSubmoduleSubgroup action m v.1.toMul).mpr v.property⟩
      left_inv := fun t ↦ by ext; rfl
      right_inv := fun v ↦ by ext; rfl }
  have hVGcardBase : Nat.card VG = Nat.card V0 := by
    calc
      Nat.card VG = Nat.card VT :=
        Subgroup.card_map_of_injective T.subtype_injective
      _ = Nat.card V0 := Nat.card_congr eVT
  letI : Fintype V0 := Fintype.ofFinite V0
  letI : Module.Finite (ZMod p) V0 := by infer_instance
  let n := Module.finrank (ZMod p) V0
  have hVcard : Nat.card V0 = p ^ n := by
    simpa only [n, Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod p) (V := V0))
  have hVGcard : Nat.card VG = p ^ n := hVGcardBase.trans hVcard
  have hVGT : VG ≤ T := Subgroup.map_subtype_le VT
  have hVGW : VG ≤ W := hVGT.trans hTW
  have hEnormVG : E ≤ Subgroup.normalizer (VG : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro e he g hg
    rcases hg with ⟨t, ht, rfl⟩
    let ee : E := ⟨e, he⟩
    have hmapMem : action ee t ∈ VT.map (action ee).toMonoidHom :=
      ⟨t, ht, rfl⟩
    rw [actionSubmoduleSubgroup_invariant action m ee] at hmapMem
    refine ⟨action ee t, hmapMem, ?_⟩
    exact coe_subgroupConjugationAction_smul T E hEnormT ee t
  have hregVGE : IsSemiregularConjugation VG E :=
    hregTE.mono_left hVGT
  have hdivV : Nat.card E ∣ Nat.card VG - 1 :=
    semiregular_card_dvd_sub_one12 hregVGE hEnormVG
  have hnPos : 0 < n := Module.finrank_pos
  have hnLe : n ≤ 2 := by
    by_contra hnnot
    have hthree : 3 ≤ n := by omega
    have hpows : p ^ 3 ≤ p ^ n :=
      Nat.pow_le_pow_right ctx.p_prime.pos hthree
    have hcardLe : Nat.card VG ≤ Nat.card W :=
      Nat.le_of_dvd (Nat.card_pos) (Subgroup.card_dvd_of_le hVGW)
    have hbad : p ^ 3 ≤ p ^ 2 := by
      calc
        p ^ 3 ≤ p ^ n := hpows
        _ = Nat.card VG := hVGcard.symm
        _ ≤ Nat.card W := hcardLe
        _ = p ^ 2 := hWcard
    exact (not_lt_of_ge hbad)
      (Nat.pow_lt_pow_right ctx.p_prime.one_lt (by omega))
  have hnCases : n = 1 ∨ n = 2 := by omega

  have hEcomm : IsMulCommutative E := by
    rcases hnCases with hnOne | hnTwo
    · apply isMulCommutative_iff.mpr
      intro a b
      apply hrhoV
      simpa only [map_mul] using
        (endomorphisms_commute_of_finrank_eq_one hnOne
          (rhoV a) (rhoV b)).eq
    · exact
        Submission.OddOrder.BG.Section02.odd_faithful_finrank_two_isMulCommutative_of_not_dvd_charP
          rhoV hrhoV hnTwo (mFT_odd E) hpE
  letI : IsMulCommutative E := hEcomm
  have hZE8 : IsZGroup8 E :=
    (typeF_context w.L E
      (Frobenius_of_typeF w.L E hFrob)).frobenius_iff_zgroup.mp hFrob
  letI : IsZGroup E :=
    ⟨fun q hq Q ↦ by
      letI : Fact q.Prime := ⟨hq⟩
      exact hZE8 q Q⟩
  letI : Group.IsNilpotent E := by infer_instance
  have hEcyclic : IsCyclic E := by infer_instance

  rcases hnCases with hnOne | hnTwo
  · refine ⟨hEcyclic, Or.inl ?_⟩
    simpa only [hVGcard, hnOne, pow_one] using hdivV
  · have hVGW_eq : VG = W := by
      apply Subgroup.eq_of_le_of_card_ge hVGW
      rw [hVGcard, hnTwo, hWcard]
    have hdivSq : Nat.card E ∣ p ^ 2 - 1 := by
      simpa only [hVGcard, hnTwo] using hdivV

    letI rhoVAddCommGroup : AddCommGroup rhoV.asModule :=
      rhoV.instAddCommGroupAsModule
    letI rhoVAddCommMonoid : AddCommMonoid rhoV.asModule :=
      rhoV.instAddCommMonoidAsModule
    letI rhoVBaseModule := rhoV.instModuleAsModule
    letI rhoVAsModule := rhoV.instModuleMonoidAlgebraAsModule
    letI rhoVScalarTower :=
      rhoV.instIsScalarTowerMonoidAlgebraAsModule
    letI rhoVSMulComm :=
      @IsScalarTower.to_smulCommClass' (ZMod p) (inferInstance)
        (MonoidAlgebra (ZMod p) E) (inferInstance) (inferInstance)
        rhoV.asModule rhoVAddCommMonoid rhoVAsModule
        rhoVBaseModule rhoVScalarTower
    let F := @Module.End (MonoidAlgebra (ZMod p) E) rhoV.asModule
      (inferInstance) rhoVAddCommMonoid rhoVAsModule
    letI FField : Field F := finiteSchurField rhoV
    letI FSemiring : Semiring F := @Module.End.instSemiring
      (MonoidAlgebra (ZMod p) E) rhoV.asModule
      (inferInstance) rhoVAddCommMonoid rhoVAsModule
    letI FAddCommMonoid : AddCommMonoid F := FSemiring.toAddCommMonoid
    letI FSelfModule : @Module F F FSemiring FAddCommMonoid :=
      @Semiring.toModule F FSemiring
    letI FAlgebra := @Module.End.instAlgebra (ZMod p)
      (MonoidAlgebra (ZMod p) E) rhoV.asModule
      (inferInstance) (inferInstance) rhoVAddCommMonoid
      rhoVBaseModule rhoVAsModule rhoVSMulComm
      (inferInstance) rhoVScalarTower
    letI FModule : @Module F rhoV.asModule
        (inferInstance) rhoVAddCommMonoid :=
      @Module.End.applyModule
        (MonoidAlgebra (ZMod p) E) rhoV.asModule
        (inferInstance) rhoVAddCommMonoid rhoVAsModule
    letI FSmul : SMul F rhoV.asModule := FModule.toSMul
    letI rhoVFinite : Finite rhoV.asModule :=
      Finite.of_injective rhoV.asModuleEquiv rhoV.asModuleEquiv.injective
    letI : Finite (rhoV.asModule → rhoV.asModule) := by infer_instance
    letI FFinite : Finite F :=
      Finite.of_injective
        (fun f : F ↦ (f : rhoV.asModule → rhoV.asModule))
        (fun _ _ h ↦ DFunLike.coe_injective h)
    letI : Fintype F := Fintype.ofFinite F
    let toCenter : E →* Subgroup.center E :=
      { toFun := fun e ↦ ⟨e, by
            rw [Subgroup.mem_center_iff]
            intro y
            exact (mul_comm' e y).symm⟩
        map_one' := rfl
        map_mul' := fun _ _ ↦ rfl }
    have htoCenter : Function.Injective toCenter := by
      intro a b hab
      exact congrArg Subtype.val hab
    let psi : E →* Fˣ := (schurCenterCharacter rhoV).comp toCenter
    have hpsi : Function.Injective psi :=
      (schurCenterCharacter_injective_of_injective rhoV hrhoV).comp
        htoCenter
    let Afield : Subgroup Fˣ :=
      Submission.OddOrder.BG.AppendixC.primeFieldUnitRange p F
    let Bfield : Subgroup Fˣ := psi.range
    have hcardAfield : Nat.card Afield = p - 1 := by
      change Nat.card
        (Submission.OddOrder.BG.AppendixC.primeFieldUnitRange p F) = p - 1
      let f : (ZMod p)ˣ →* Fˣ :=
        Units.map (algebraMap (ZMod p) F).toMonoidHom
      have hf : Function.Injective f :=
        Units.map_injective (algebraMap (ZMod p) F).injective
      calc
        Nat.card Afield = Nat.card (ZMod p)ˣ :=
          (Nat.card_congr (f.ofInjective hf).toEquiv).symm
        _ = p - 1 := by rw [Nat.card_units, Nat.card_zmod]
    have hcardBfield : Nat.card Bfield = Nat.card E :=
      (Nat.card_congr (psi.ofInjective hpsi).toEquiv).symm
    have hABdisjoint : Disjoint Afield Bfield := by
      rw [Subgroup.disjoint_def]
      intro b hbA hbB
      rcases hbB with ⟨e, rfl⟩
      change psi e ∈
        Submission.OddOrder.BG.AppendixC.primeFieldUnitRange p F at hbA
      rcases hbA with ⟨c, hc⟩
      have hxVG : w.x ∈ VG := by
        rw [hVGW_eq]
        exact w.x_mem_omega
      rcases hxVG with ⟨xt, hxtVT, hxt⟩
      let xv : V0 :=
        ⟨Additive.ofMul xt,
          (mem_actionSubmoduleSubgroup action m xt).mp hxtVT⟩
      let xvM : rhoV.asModule := rhoV.asModuleEquiv.symm xv
      have hschur :=
        schurCenterCharacter_val_apply rhoV (toCenter e) xvM
      have htoCenterVal : ((toCenter e : Subgroup.center E) : E) = e := rfl
      rw [htoCenterVal] at hschur
      have hcval :
          algebraMap (ZMod p) F (c : ZMod p) = (psi e : F) :=
        congrArg Units.val hc
      have hscalarV : rhoV e xv = (c : ZMod p) • xv := by
        calc
          rhoV e xv =
              rhoV.asModuleEquiv ((psi e : F) xvM) := by
            simpa only [psi, MonoidHom.comp_apply, xvM,
              LinearEquiv.apply_symm_apply] using hschur.symm
          _ = rhoV.asModuleEquiv
              ((algebraMap (ZMod p) F (c : ZMod p) : F) xvM) := by
            rw [hcval]
          _ = (c : ZMod p) • xv := by
            rw [Module.algebraMap_end_apply, map_smul]
            simp only [xvM, LinearEquiv.apply_symm_apply]
      have hscalarAdd := congrArg Subtype.val hscalarV
      change Additive.ofMul (e • xt) =
        (c : ZMod p) • Additive.ofMul xt at hscalarAdd
      have hsmulPow :
          (c : ZMod p) • Additive.ofMul xt =
            Additive.ofMul (xt ^ (c : ZMod p).val) := by
        calc
          (c : ZMod p) • Additive.ofMul xt =
              ((c : ZMod p).val : ZMod p) • Additive.ofMul xt := by
            rw [ZMod.natCast_zmod_val]
          _ = Additive.ofMul (xt ^ (c : ZMod p).val) := by
            apply Additive.toMul.injective
            rw [Nat.cast_smul_eq_nsmul, toMul_nsmul, toMul_ofMul]
            simp only [toMul_ofMul]
      have hscalarT : e • xt = xt ^ (c : ZMod p).val := by
        exact congrArg Additive.toMul (hscalarAdd.trans hsmulPow)
      have hxtG : (xt : G) = w.x := by
        simpa only [Subgroup.coe_subtype] using hxt
      have hconj :
          (e : G) * w.x * (e : G)⁻¹ =
            w.x ^ (c : ZMod p).val := by
        calc
          (e : G) * w.x * (e : G)⁻¹ =
              (e : G) * (xt : G) * (e : G)⁻¹ := by rw [← hxtG]
          _ = ((e • xt : T) : G) :=
            (coe_subgroupConjugationAction_smul T E hEnormT e xt).symm
          _ = ((xt ^ (c : ZMod p).val : T) : G) :=
            congrArg Subtype.val hscalarT
          _ = w.x ^ (c : ZMod p).val := by
            exact congrArg (fun g : G ↦ g ^ (c : ZMod p).val) hxtG
      have hmapLe :
          (Subgroup.zpowers w.x).map
              (MulAut.conj (e : G)).toMonoidHom ≤
            Subgroup.zpowers w.x := by
        rw [MonoidHom.map_zpowers]
        apply Subgroup.zpowers_le.mpr
        change (e : G) * w.x * (e : G)⁻¹ ∈
          Subgroup.zpowers w.x
        rw [hconj]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers w.x) _
      have hmapEq :
          (Subgroup.zpowers w.x).map
              (MulAut.conj (e : G)).toMonoidHom =
            Subgroup.zpowers w.x := by
        apply Subgroup.eq_of_le_of_card_ge hmapLe
        rw [Subgroup.card_map_of_injective (MulAut.conj (e : G)).injective]
      have heNorm : (e : G) ∈
          Subgroup.normalizer (Subgroup.zpowers w.x : Set G) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmapEq
      have heM : (e : G) ∈ M := w.normalizer_le_M heNorm
      have heH : (e : G) ∈ H :=
        intersection_le_second_fitting12 ctx w hFrob ⟨heM, hEL e.property⟩
      have heBot : (e : G) ∈ (⊥ : Subgroup G) := by
        rw [← disjoint_iff.mp hHEdis]
        exact ⟨heH, e.property⟩
      have heOne : e = 1 := Subtype.ext (Subgroup.mem_bot.mp heBot)
      rw [heOne, map_one]
    let mulAB : Afield × Bfield →* Fˣ :=
      { toFun := fun z ↦ (z.1 : Fˣ) * (z.2 : Fˣ)
        map_one' := by simp
        map_mul' := by
          intro x y
          apply Units.ext
          exact mul_mul_mul_comm _ _ _ _ }
    have hmulAB : Function.Injective mulAB :=
      Subgroup.mul_injective_of_disjoint hABdisjoint
    letI : IsCyclic (Afield × Bfield) :=
      isCyclic_of_injective_ringHom
        ((Units.coeHom F).comp mulAB)
        (Units.val_injective.comp hmulAB)
    have hcopAB : Nat.Coprime (Nat.card Afield) (Nat.card Bfield) :=
      coprime_card_of_isCyclic_prod Afield Bfield
    have hcopE : Nat.Coprime (Nat.card E) (p - 1) := by
      rw [← hcardBfield, ← hcardAfield]
      exact hcopAB.symm
    have hfactor : p ^ 2 - 1 = (p + 1) * (p - 1) := by
      simpa using (Nat.sq_sub_sq p 1)
    have hdivPlus : Nat.card E ∣ p + 1 := by
      apply hcopE.dvd_of_dvd_mul_right
      rwa [← hfactor]
    exact ⟨hEcyclic, Or.inr hdivPlus⟩

namespace FTType1NonFrobeniusInternal

theorem p0_le_second_fitting12
    {p : ℕ} {M P0 : Subgroup G}
    (ctx : FTType1NonFrobeniusContext p M P0)
    (w : NonFrobeniusFTType1Witness p M P0) :
    P0 ≤ Fitting_core w.L := by
  exact p0_le_second_fitting12_impl ctx w

theorem first_maximal_not_frobenius12
    {p : ℕ} {M P0 : Subgroup G}
    (ctx : FTType1NonFrobeniusContext p M P0)
    (w : NonFrobeniusFTType1Witness p M P0) :
    ¬ ∃ E : Subgroup G,
      IsFrobeniusIn (Fitting_core M) E M := by
  exact first_maximal_not_frobenius12_impl ctx w

theorem nonFrobenius_group_bridge12
    {p : ℕ} {M P0 : Subgroup G}
    (ctx : FTType1NonFrobeniusContext p M P0)
    (w : NonFrobeniusFTType1Witness p M P0) :
    ∃ E,
      IsFrobeniusIn (Fitting_core w.L) E w.L ∧
      IsInternalSemidirectProductIn (Fitting_core M) (M ⊓ w.L) M ∧
      (M ⊓ w.L) ≤ Fitting_core w.L ∧
      IsCyclic E ∧
      (Nat.card E ∣ p - 1 ∨ Nat.card E ∣ p + 1) := by
  obtain ⟨E, hFrob⟩ := second_maximal_frobenius12 ctx w
  obtain ⟨hcyclic, hdiv⟩ :=
    second_complement_cyclic_divisibility12 ctx w hFrob
  exact ⟨E, hFrob,
    fitting_complement_at_first_maximal12 ctx w hFrob,
    intersection_le_second_fitting12 ctx w hFrob,
    hcyclic, hdiv⟩

end FTType1NonFrobeniusInternal

end

end Submission.OddOrder.PF
