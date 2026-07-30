import Submission.OddOrder.MathlibSupport.FittingSelfCentralizing
import Submission.OddOrder.MathlibSupport.Centralizer
import Submission.OddOrder.MathlibSupport.Solvability
import Submission.OddOrder.MathlibSupport.SubgroupCardinality

/-!
# Coprime centralizers of the Fitting subgroup

This is the Lean form of `BGsection1.coprime_cent_Fitting`.  The faithful
case follows the source proof: after reducing the acting group to a cyclic
group, form the coprime semidirect product, identify its Fitting subgroup
inside the normal factor prime by prime, and use the self-centralizing
property of the Fitting subgroup.  The general case is obtained by
quotienting by the action kernel.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v

private theorem map_pCore_equiv
    {G : Type u} {K : Type v} [Group G] [Group K]
    (p : ℕ) [Fact p.Prime] (e : G ≃* K) :
    (pCore p G).map e.toMonoidHom = pCore p K := by
  apply le_antisymm
  · exact le_pCore (pCore_isPGroup.map e.toMonoidHom)
      (Subgroup.Normal.map (by infer_instance) e.toMonoidHom e.surjective)
  · rw [← Subgroup.map_le_map_iff_of_injective
        (f := e.symm.toMonoidHom) e.symm.injective]
    have h : (pCore p K).map e.symm.toMonoidHom ≤ pCore p G :=
      le_pCore
        (pCore_isPGroup (p := p) (G := K) |>.map e.symm.toMonoidHom)
        (Subgroup.Normal.map
          (inferInstance : (pCore p K).Normal) e.symm.toMonoidHom
          e.symm.surjective)
    simpa [Subgroup.map_map] using h

private theorem map_fittingCore_equiv
    {G : Type u} {K : Type v} [Group G] [Group K]
    (e : G ≃* K) :
    (fittingCore G).map e.toMonoidHom = fittingCore K := by
  rw [fittingCore, fittingCore, Subgroup.map_iSup]
  apply iSup_congr
  intro p
  letI : Fact (p : ℕ).Prime := ⟨p.property⟩
  exact map_pCore_equiv (p : ℕ) e

private theorem coprime_cyclic_faithful_fitting_centralizer_eq_bot
    {G : Type u} [Group G] [Finite G]
    {A H : Subgroup G} [IsCyclic A]
    (hAH : A ≤ Subgroup.normalizer (H : Set G))
    (hcop : Nat.Coprime (Nat.card H) (Nat.card A))
    (hsol : IsSolvable H)
    (hfaith : centralizerWithin A H = ⊥) :
    centralizerWithin A ((fittingCore H).map H.subtype) = ⊥ := by
  classical
  let J : Subgroup G := A ⊔ H
  let AJ : Subgroup J := A.subgroupOf J
  let HJ : Subgroup J := H.subgroupOf J
  have hAJ : A ≤ J := le_sup_left
  have hHJ : H ≤ J := le_sup_right
  letI : HJ.Normal := by
    dsimp [HJ, J]
    exact Subgroup.normal_subgroupOf_sup_of_le_normalizer hAH
  have hcardAJ : Nat.card AJ = Nat.card A :=
    natCard_subgroupOf_eq hAJ
  have hcardHJ : Nat.card HJ = Nat.card H :=
    natCard_subgroupOf_eq hHJ
  have hcopJ : Nat.Coprime (Nat.card HJ) (Nat.card AJ) := by
    simpa [hcardHJ, hcardAJ] using hcop
  have hdisJ : Disjoint HJ AJ := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro x hx
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    apply Subgroup.mem_bot.mp
    rw [← disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)]
    exact hx
  have hsupJ : HJ ⊔ AJ = ⊤ := by
    change H.subgroupOf J ⊔ A.subgroupOf J = ⊤
    rw [← Subgroup.subgroupOf_sup hHJ hAJ]
    simp [J, sup_comm]
  have hcompJ : HJ.IsComplement' AJ := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisJ
    rw [← Subgroup.normal_mul HJ AJ, hsupJ]
    rfl
  let eAJ : AJ ≃* A := Subgroup.subgroupOfEquivOfLe hAJ
  letI : IsCyclic AJ := eAJ.isCyclic.mpr (inferInstance : IsCyclic A)
  letI : IsSolvable AJ := inferInstance
  let eHJ : HJ ≃* H := Subgroup.subgroupOfEquivOfLe hHJ
  letI : IsSolvable H := hsol
  letI : IsSolvable HJ :=
    solvable_of_solvable_injective (f := eHJ.toMonoidHom) eHJ.injective
  let eQuot : (J ⧸ HJ) ≃* AJ := hcompJ.symm.QuotientMulEquiv
  letI : IsSolvable (J ⧸ HJ) :=
    solvable_of_solvable_injective (f := eQuot.toMonoidHom) eQuot.injective
  letI : IsSolvable J :=
    isSolvable_of_normal_subgroup_and_quotient HJ

  have hFJH : fittingCore J ≤ HJ := by
    rw [fittingCore]
    apply iSup_le
    intro p
    letI : Fact (p : ℕ).Prime := ⟨p.property⟩
    by_cases hpH : (p : ℕ) ∣ Nat.card HJ
    · have hpA : ¬ (p : ℕ) ∣ Nat.card AJ :=
        p.property.coprime_iff_not_dvd.mp
          (hcopJ.coprime_dvd_left hpH)
      let P : Sylow (p : ℕ) HJ := default
      let PJ : Subgroup J := (P : Subgroup HJ).map HJ.subtype
      have hPJp : IsPGroup (p : ℕ) PJ :=
        P.isPGroup'.map HJ.subtype
      have hpPJindex : ¬ (p : ℕ) ∣ PJ.index := by
        rw [Subgroup.index_map_subtype, hcompJ.symm.index_eq_card]
        exact p.property.not_dvd_mul P.not_dvd_index hpA
      let S : Sylow (p : ℕ) J := hPJp.toSylow hpPJindex
      exact (pCore_le_sylow S).trans (by
        change PJ ≤ HJ
        exact Subgroup.map_subtype_le (P : Subgroup HJ))
    · let P : Sylow (p : ℕ) AJ := default
      let PJ : Subgroup J := (P : Subgroup AJ).map AJ.subtype
      have hPJp : IsPGroup (p : ℕ) PJ :=
        P.isPGroup'.map AJ.subtype
      have hpPJindex : ¬ (p : ℕ) ∣ PJ.index := by
        rw [Subgroup.index_map_subtype, hcompJ.index_eq_card]
        exact p.property.not_dvd_mul P.not_dvd_index hpH
      let S : Sylow (p : ℕ) J := hPJp.toSylow hpPJindex
      have hcoreA : pCore (p : ℕ) J ≤ AJ :=
        (pCore_le_sylow S).trans (by
          change PJ ≤ AJ
          exact Subgroup.map_subtype_le (P : Subgroup AJ))
      obtain ⟨n, hcardCore⟩ :=
        (pCore_isPGroup (p := (p : ℕ)) (G := J)).exists_card_eq
      have hcoreCop : Nat.Coprime
          (Nat.card (pCore (p : ℕ) J)) (Nat.card HJ) := by
        rw [hcardCore]
        exact (p.property.coprime_iff_not_dvd.mpr hpH).pow_left n
      have hdisCore : Disjoint (pCore (p : ℕ) J) HJ :=
        Subgroup.disjoint_of_coprime_natCard hcoreCop
      have hcomm := Subgroup.commute_of_normal_of_disjoint
        (pCore (p : ℕ) J) HJ (by infer_instance) (by infer_instance)
        hdisCore
      have hcoreBot : pCore (p : ℕ) J = ⊥ := by
        apply le_bot_iff.mp
        intro x hx
        have hxA : ((x : J) : G) ∈ A := hcoreA hx
        have hxCent : ((x : J) : G) ∈ centralizerWithin A H := by
          refine ⟨hxA, ?_⟩
          intro h hh
          let hJ : J := ⟨h, hHJ hh⟩
          have hhHJ : hJ ∈ HJ := hh
          exact congrArg Subtype.val (hcomm x hJ hx hhHJ).eq.symm
        rw [hfaith] at hxCent
        apply Subgroup.mem_bot.mpr
        apply Subtype.ext
        exact Subgroup.mem_bot.mp hxCent
      rw [hcoreBot]
      exact bot_le

  let FIn : Subgroup HJ := (fittingCore J).subgroupOf HJ
  letI : FIn.Normal := by
    dsimp [FIn]
    exact Subgroup.Normal.subgroupOf
      (inferInstance : (fittingCore J).Normal) HJ
  let eF : FIn ≃* fittingCore J :=
    Subgroup.subgroupOfEquivOfLe hFJH
  letI : Group.IsNilpotent FIn :=
    Group.nilpotent_of_mulEquiv eF.symm
  have hFInFit : FIn ≤ fittingCore HJ :=
    nilpotent_normal_le_fittingCore (by infer_instance) (by infer_instance)
  have hFJFit : fittingCore J ≤ (fittingCore HJ).map HJ.subtype := by
    intro x hx
    let xH : HJ := ⟨x, hFJH hx⟩
    exact ⟨xH, hFInFit hx, rfl⟩
  have hmapFit : (fittingCore HJ).map eHJ.toMonoidHom =
      fittingCore H := map_fittingCore_equiv eHJ

  apply le_bot_iff.mp
  intro x hx
  let xJ : J := ⟨x, hAJ hx.1⟩
  have hxAJ : xJ ∈ AJ := hx.1
  have hxCentFJ : xJ ∈ Subgroup.centralizer (fittingCore J : Set J) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hFJFit hy with ⟨yH, hyFit, hyEq⟩
    have hyMap : eHJ yH ∈ (fittingCore HJ).map eHJ.toMonoidHom :=
      Subgroup.mem_map_of_mem eHJ.toMonoidHom hyFit
    rw [hmapFit] at hyMap
    have hyAmbient : ((y : J) : G) ∈ (fittingCore H).map H.subtype := by
      refine ⟨eHJ yH, hyMap, ?_⟩
      exact congrArg Subtype.val hyEq
    apply Subtype.ext
    exact hx.2 ((y : J) : G) hyAmbient
  have hxFJ : xJ ∈ fittingCore J :=
    centralizer_fittingCore_le hxCentFJ
  have hxHJ : xJ ∈ HJ := hFJH hxFJ
  have hxBot : x ∈ (H ⊓ A : Subgroup G) := ⟨hxHJ, hx.1⟩
  have hdisHA : H ⊓ A = ⊥ :=
    disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)
  rw [hdisHA] at hxBot
  exact hxBot

private theorem coprime_faithful_fitting_centralizer_eq_bot
    {G : Type u} [Group G] [Finite G]
    {A H : Subgroup G}
    (hAH : A ≤ Subgroup.normalizer (H : Set G))
    (hcop : Nat.Coprime (Nat.card H) (Nat.card A))
    (hsol : IsSolvable H)
    (hfaith : centralizerWithin A H = ⊥) :
    centralizerWithin A ((fittingCore H).map H.subtype) = ⊥ := by
  classical
  apply le_bot_iff.mp
  intro x hx
  let X : Subgroup G := Subgroup.zpowers x
  have hXA : X ≤ A := Subgroup.zpowers_le.mpr hx.1
  have hXH : X ≤ Subgroup.normalizer (H : Set G) :=
    hXA.trans hAH
  have hcopX : Nat.Coprime (Nat.card H) (Nat.card X) :=
    hcop.coprime_dvd_right (Subgroup.card_dvd_of_le hXA)
  have hfaithX : centralizerWithin X H = ⊥ := by
    apply le_bot_iff.mp
    intro y hy
    have hyAH : y ∈ centralizerWithin A H := ⟨hXA hy.1, hy.2⟩
    rw [hfaith] at hyAH
    exact hyAH
  letI : IsCyclic X := inferInstance
  have hcyclic :=
    coprime_cyclic_faithful_fitting_centralizer_eq_bot
      hXH hcopX hsol hfaithX
  have hxX : x ∈ X := Subgroup.mem_zpowers x
  have hxCent : x ∈
      centralizerWithin X ((fittingCore H).map H.subtype) :=
    ⟨hxX, hx.2⟩
  rw [hcyclic] at hxCent
  exact hxCent

/-- If a finite solvable subgroup is normalized coprimely, every element of
the acting subgroup which centralizes its Fitting subgroup centralizes the
whole subgroup.  This is `BGsection1.coprime_cent_Fitting`. -/
theorem coprime_cent_fitting
    {G : Type u} [Group G] [Finite G]
    {A H : Subgroup G}
    (hAH : A ≤ Subgroup.normalizer (H : Set G))
    (hcop : Nat.Coprime (Nat.card H) (Nat.card A))
    (hsol : IsSolvable H) :
    centralizerWithin A ((fittingCore H).map H.subtype) ≤
      Subgroup.centralizer (H : Set G) := by
  classical
  let J : Subgroup G := A ⊔ H
  let AJ : Subgroup J := A.subgroupOf J
  let HJ : Subgroup J := H.subgroupOf J
  have hAJ : A ≤ J := le_sup_left
  have hHJ : H ≤ J := le_sup_right
  letI : HJ.Normal := by
    dsimp [HJ, J]
    exact Subgroup.normal_subgroupOf_sup_of_le_normalizer hAH
  have hcardAJ : Nat.card AJ = Nat.card A :=
    natCard_subgroupOf_eq hAJ
  have hcardHJ : Nat.card HJ = Nat.card H :=
    natCard_subgroupOf_eq hHJ
  have hcopJ : Nat.Coprime (Nat.card HJ) (Nat.card AJ) := by
    simpa [hcardHJ, hcardAJ] using hcop
  have hdisJ : Disjoint HJ AJ := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro x hx
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    apply Subgroup.mem_bot.mp
    rw [← disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)]
    exact hx
  have hsupJ : HJ ⊔ AJ = ⊤ := by
    change H.subgroupOf J ⊔ A.subgroupOf J = ⊤
    rw [← Subgroup.subgroupOf_sup hHJ hAJ]
    simp [J, sup_comm]

  let CJ : Subgroup J := centralizerWithin AJ HJ
  have hAJnormCJ : AJ ≤ Subgroup.normalizer (CJ : Set J) := by
    change AJ ≤ Subgroup.normalizer
      (AJ ⊓ Subgroup.centralizer (HJ : Set J) : Subgroup J)
    apply (le_inf AJ.le_normalizer
      (Subgroup.le_normalizer_of_normal :
        AJ ≤ Subgroup.normalizer
          (Subgroup.centralizer (HJ : Set J) : Set J))).trans
    exact Subgroup.inf_normalizer_le_normalizer_inf
  have hHJnormCJ : HJ ≤ Subgroup.normalizer (CJ : Set J) := by
    apply (show HJ ≤ Subgroup.centralizer (CJ : Set J) from ?_).trans
      (Subgroup.centralizer_le_normalizer (CJ : Set J))
    intro h hh
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (hc.2 h hh).symm
  letI : CJ.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    apply top_unique
    rw [← hsupJ]
    exact sup_le hHJnormCJ hAJnormCJ
  have hcardCJdvd : Nat.card CJ ∣ Nat.card AJ :=
    Subgroup.card_dvd_of_le (centralizerWithin_le_left AJ HJ)
  have hcopHC : Nat.Coprime (Nat.card HJ) (Nat.card CJ) :=
    hcopJ.coprime_dvd_right hcardCJdvd
  have hdisCH : Disjoint CJ HJ :=
    Subgroup.disjoint_of_coprime_natCard hcopHC.symm

  let q : J →* J ⧸ CJ := QuotientGroup.mk' CJ
  let Aq : Subgroup (J ⧸ CJ) := AJ.map q
  let Hq : Subgroup (J ⧸ CJ) := HJ.map q
  letI : Hq.Normal :=
    Subgroup.Normal.map (inferInstance : HJ.Normal) q
      (QuotientGroup.mk'_surjective CJ)
  have hAqHq : Aq ≤ Subgroup.normalizer (Hq : Set (J ⧸ CJ)) :=
    Subgroup.le_normalizer_of_normal
  have hcardHqDvd : Nat.card Hq ∣ Nat.card HJ :=
    Subgroup.card_map_dvd HJ q
  have hcardAqDvd : Nat.card Aq ∣ Nat.card AJ :=
    Subgroup.card_map_dvd AJ q
  have hcopq : Nat.Coprime (Nat.card Hq) (Nat.card Aq) :=
    (hcopJ.coprime_dvd_left hcardHqDvd).coprime_dvd_right hcardAqDvd
  let eHJ : HJ ≃* H := Subgroup.subgroupOfEquivOfLe hHJ
  letI : IsSolvable H := hsol
  letI : IsSolvable HJ :=
    solvable_of_solvable_injective (f := eHJ.toMonoidHom) eHJ.injective
  have hsolq : IsSolvable Hq :=
    solvable_of_surjective (f := q.subgroupMap HJ)
      (q.subgroupMap_surjective HJ)

  have hfaithq : centralizerWithin Aq Hq = ⊥ := by
    apply le_bot_iff.mp
    intro z hz
    rcases hz.1 with ⟨a, haAJ, haz⟩
    have haCJ : a ∈ CJ := by
      refine ⟨haAJ, ?_⟩
      intro h hh
      have hcommq := hz.2 (q h) (Subgroup.mem_map_of_mem q hh)
      rw [← haz] at hcommq
      let d : J := a * h * a⁻¹ * h⁻¹
      have hqd : q d = 1 := by
        dsimp [d]
        change q a * q h * (q a)⁻¹ * (q h)⁻¹ = 1
        rw [← hcommq]
        group
      have hdC : d ∈ CJ :=
        QuotientGroup.eq_one_iff d |>.mp hqd
      have hdH : d ∈ HJ := by
        dsimp [d]
        exact HJ.mul_mem
          ((inferInstance : HJ.Normal).conj_mem h hh a)
          (HJ.inv_mem hh)
      have hdOne : d = 1 := by
        apply Subgroup.mem_bot.mp
        rw [← disjoint_iff.mp hdisCH]
        exact ⟨hdC, hdH⟩
      have hcomm : a * h = h * a := by
        apply commutatorElement_eq_one_iff_mul_comm.mp
        simpa [d, commutatorElement_def] using hdOne
      exact hcomm.symm
    have hzaOne : q a = 1 :=
      QuotientGroup.eq_one_iff a |>.mpr haCJ
    apply Subgroup.mem_bot.mpr
    rw [← haz, hzaOne]

  have hqHJinj : Function.Injective (q.subgroupMap HJ) := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.ker_subgroupMap,
      QuotientGroup.ker_mk', Subgroup.subgroupOf_eq_bot]
    exact hdisCH
  let eHq : HJ ≃* Hq :=
    MulEquiv.ofBijective (q.subgroupMap HJ)
      ⟨hqHJinj, q.subgroupMap_surjective HJ⟩
  have hmapFitHJ : (fittingCore HJ).map eHJ.toMonoidHom =
      fittingCore H := map_fittingCore_equiv eHJ
  have hmapFitHq : (fittingCore HJ).map eHq.toMonoidHom =
      fittingCore Hq := map_fittingCore_equiv eHq
  have hfaithFit :=
    coprime_faithful_fitting_centralizer_eq_bot
      hAqHq hcopq hsolq hfaithq

  intro x hx
  let xJ : J := ⟨x, hAJ hx.1⟩
  have hxAJ : xJ ∈ AJ := hx.1
  have hqxCent : q xJ ∈
      centralizerWithin Aq ((fittingCore Hq).map Hq.subtype) := by
    refine ⟨Subgroup.mem_map_of_mem q hxAJ, ?_⟩
    intro y hy
    rcases hy with ⟨yq, hyFit, rfl⟩
    rw [← hmapFitHq] at hyFit
    rcases hyFit with ⟨yH, hyHJFit, hyEq⟩
    have hyMap : eHJ yH ∈ (fittingCore HJ).map eHJ.toMonoidHom :=
      Subgroup.mem_map_of_mem eHJ.toMonoidHom hyHJFit
    rw [hmapFitHJ] at hyMap
    have hyAmbient : (((yH : HJ) : J) : G) ∈
        (fittingCore H).map H.subtype :=
      ⟨eHJ yH, hyMap, rfl⟩
    have hcommJ : (yH : J) * xJ = xJ * (yH : J) := by
      apply Subtype.ext
      exact hx.2 (((yH : HJ) : J) : G) hyAmbient
    have hcommq := congrArg q hcommJ
    have hyEqVal : ((eHq yH : Hq) : J ⧸ CJ) = q (yH : J) := rfl
    have hyqVal : (yq : J ⧸ CJ) = q (yH : J) :=
      (congrArg Subtype.val hyEq).symm.trans hyEqVal
    change (yq : J ⧸ CJ) * q xJ = q xJ * (yq : J ⧸ CJ)
    rw [hyqVal]
    simpa using hcommq
  rw [hfaithFit] at hqxCent
  have hqxOne : q xJ = 1 := Subgroup.mem_bot.mp hqxCent
  have hxCJ : xJ ∈ CJ :=
    QuotientGroup.eq_one_iff xJ |>.mp hqxOne
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  let hJ : J := ⟨h, hHJ hh⟩
  have hhHJ : hJ ∈ HJ := hh
  exact congrArg Subtype.val (hxCJ.2 hJ hhHJ)

end Submission.OddOrder.MathlibSupport
