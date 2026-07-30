import Submission.OddOrder.MathlibSupport.CoprimeAbelianCentralizerGeneration
import Submission.OddOrder.MathlibSupport.CoprimeSolvableInvariantSylowExtension
import Submission.OddOrder.MathlibSupport.Centralizer
import Submission.OddOrder.MathlibSupport.SolvableQuotientCentralizer

/-!
# Centralizer generation for coprime abelian actions on solvable groups

This is the eliminator form of Bender--Glauberman Proposition 1.16 used in
Section 7.  The proof follows the source induction: invariant Sylow subgroups
handle the proper-subgroup branch, while a minimal invariant subgroup in the
center handles the p-group branch.  The latter is factored out and the
induction continues in the quotient.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G] [Finite G]

/-- The internal-centralizer form of the preceding quotient lifting lemma. -/
private theorem map_centralizerWithin_quotient_eq_of_coprime
    {K : Type*} [Group K] [Finite K] [IsSolvable K]
    {N Y R : Subgroup K} [N.Normal]
    (hNY : N ≤ Y)
    (hcop : Nat.Coprime (Nat.card N) (Nat.card R)) :
    (centralizerWithin Y R).map (QuotientGroup.mk' N) =
      centralizerWithin (Y.map (QuotientGroup.mk' N))
        (R.map (QuotientGroup.mk' N)) := by
  classical
  let q : K →* K ⧸ N := QuotientGroup.mk' N
  have hcent :=
    map_centralizer_quotient_eq_of_coprime hcop
  apply le_antisymm
  · rintro _ ⟨c, hc, rfl⟩
    refine ⟨⟨c, hc.1, rfl⟩, ?_⟩
    have hcmap : q c ∈ (Subgroup.centralizer (R : Set K)).map q :=
      ⟨c, hc.2, rfl⟩
    rwa [hcent] at hcmap
  · intro z hz
    have hzCent : z ∈ (Subgroup.centralizer (R : Set K)).map q := by
      rw [hcent]
      exact hz.2
    rcases hzCent with ⟨c, hcCent, hcz⟩
    rcases hz.1 with ⟨y, hy, hyz⟩
    have hqeq : q c = q y := hcz.trans hyz.symm
    have hdiff : c⁻¹ * y ∈ N := QuotientGroup.eq.mp hqeq
    have hcY : c ∈ Y := by
      rw [show c = y * (c⁻¹ * y)⁻¹ by group]
      exact Y.mul_mem hy (Y.inv_mem (hNY hdiff))
    exact ⟨c, ⟨hcY, hcCent⟩, hcz⟩

/-- Factoring a nontrivial normal subgroup contained in `E` strictly lowers
the cardinality of the image of `E`. -/
private theorem natCard_map_quotient_lt
    {K : Type*} [Group K] [Finite K]
    {D E : Subgroup K} [D.Normal] (hDE : D ≤ E) (hD : D ≠ ⊥) :
    Nat.card (E.map (QuotientGroup.mk' D)) < Nat.card E := by
  let q : K →* K ⧸ D := QuotientGroup.mk' D
  let f : E →* E.map q := q.subgroupMap E
  letI : Fintype E := Fintype.ofFinite E
  letI : Fintype (E.map q) := Fintype.ofFinite (E.map q)
  have hfSurjective : Function.Surjective f := q.subgroupMap_surjective E
  have hfNotInjective : ¬ Function.Injective f := by
    intro hf
    obtain ⟨d, hd⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD
    have hfd : f ⟨d, hDE d.property⟩ = f 1 := by
      apply Subtype.ext
      change q (d : K) = q 1
      rw [map_one]
      exact (QuotientGroup.eq_one_iff (N := D) (d : K)).mpr d.property
    have hdOne : (⟨d, hDE d.property⟩ : E) = 1 := hf hfd
    apply hd
    apply Subtype.ext
    exact congrArg (fun z : E ↦ (z : K)) hdOne
  simpa only [Nat.card_eq_fintype_card] using
    Fintype.card_lt_of_surjective_not_injective f hfSurjective hfNotInjective

omit [Finite G] in
/-- A cyclic quotient by a subgroup of a noncyclic group has nontrivial
kernel. -/
private theorem ne_bot_of_not_isCyclic_of_isCyclic_quotient
    {B C : Subgroup G} (hCnormal : (C.subgroupOf B).Normal)
    (hBnoncyclic : ¬ IsCyclic B)
    (hquotCyclic : IsCyclic (B ⧸ C.subgroupOf B)) : C ≠ ⊥ := by
  letI : (C.subgroupOf B).Normal := hCnormal
  intro hCbot
  subst C
  have hsubBot : (⊥ : Subgroup G).subgroupOf B = (⊥ : Subgroup B) := by
    ext x
    simp
  have hquotBot : IsCyclic (B ⧸ (⊥ : Subgroup B)) :=
    (QuotientGroup.quotientMulEquivOfEq hsubBot).isCyclic.mp hquotCyclic
  apply hBnoncyclic
  exact QuotientGroup.quotientBot.isCyclic.mp hquotBot

/-- Bender--Glauberman Proposition 1.16 in eliminator form. -/
theorem le_of_centralizerWithin_zpowers_le_of_coprime_abelian_solvable
    {G : Type u} [Group G] [Finite G] {A Y K : Subgroup G}
    (hAcomm : IsMulCommutative A)
    (hAncyc : ¬ IsCyclic A)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hcop : (Nat.card Y).Coprime (Nat.card A))
    (hYsol : IsSolvable Y)
    (hcent : ∀ a : G, a ∈ A → a ≠ 1 →
      centralizerWithin Y (Subgroup.zpowers a) ≤ K) :
    Y ≤ K := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∀ (G' : Type u) [Group G'] [Finite G']
      (A' Y' K' : Subgroup G'),
      Nat.card Y' = n →
      IsMulCommutative A' →
      (¬ IsCyclic A') →
      A' ≤ Subgroup.normalizer (Y' : Set G') →
      (Nat.card Y').Coprime (Nat.card A') →
      IsSolvable Y' →
      (∀ a : G', a ∈ A' → a ≠ 1 →
        centralizerWithin Y' (Subgroup.zpowers a) ≤ K') →
      Y' ≤ K'
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      dsimp only [P]
      intro G' _ _ A' Y' K' hcard hAcomm' hAncyc' hAY' hcop'
        hYsol' hcent'
      letI : IsMulCommutative A' := hAcomm'
      by_contra hYK
      let H : Subgroup Y' := K'.comap Y'.subtype
      have hHneTop : H ≠ ⊤ := by
        intro hHtop
        apply hYK
        intro y hy
        have hyH : (⟨y, hy⟩ : Y') ∈ H := by
          rw [hHtop]
          trivial
        exact hyH
      have hHindexNe : H.index ≠ 1 := by
        intro hindex
        exact hHneTop (Subgroup.index_eq_one.mp hindex)
      obtain ⟨p, hp, hpIndex⟩ :=
        Nat.ne_one_iff_exists_prime_dvd.mp hHindexNe
      letI : Fact p.Prime := ⟨hp⟩
      obtain ⟨S, hAnormS⟩ :=
        exists_sylow_normalized_of_coprime_of_isSolvable
          (p := p) hAY' hcop' hYsol'
      let S' : Subgroup G' :=
        (S : Subgroup Y').map Y'.subtype
      have hSY : S' ≤ Y' :=
        Subgroup.map_subtype_le (S : Subgroup Y')
      have hSp : IsPGroup p S' :=
        S.isPGroup'.map Y'.subtype
      by_cases hSeq : S' = Y'
      · have hYne : Y' ≠ ⊥ := by
          intro hYbot
          apply hYK
          rw [hYbot]
          exact bot_le
        have hYp : IsPGroup p Y' := by
          rw [← hSeq]
          exact hSp
        letI : Group.IsNilpotent Y' := hYp.isNilpotent
        letI : Nontrivial Y' := Y'.nontrivial_iff_ne_bot.mpr hYne
        have hcenterNe : centerWithin Y' ≠ ⊥ :=
          centerWithin_ne_bot Y' hYp
        have hAcenter :
            A' ≤ Subgroup.normalizer (centerWithin Y' : Set G') := by
          rw [Subgroup.le_normalizer_iff]
          intro a ha z hz
          refine ⟨?_, ?_⟩
          · exact (Subgroup.mem_normalizer_iff.mp (hAY' ha) z).mp hz.1
          · intro y hy
            have hainvN := hAY' (A'.inv_mem ha)
            have hy' : a⁻¹ * y * a ∈ Y' := by
              have :=
                (Subgroup.mem_normalizer_iff.mp hainvN y).mp hy
              simpa only [inv_inv] using this
            have hcomm := hz.2 (a⁻¹ * y * a) hy'
            calc
              y * (a * z * a⁻¹) =
                  a * ((a⁻¹ * y * a) * z) * a⁻¹ := by group
              _ = a * (z * (a⁻¹ * y * a)) * a⁻¹ := by rw [hcomm]
              _ = (a * z * a⁻¹) * y := by group
        obtain ⟨M, hMcenter, hMmin⟩ :=
          exists_minimalNormalUnder_le hcenterNe hAcenter
        have hMY : M ≤ Y' :=
          hMcenter.trans (centralizerWithin_le_left Y' Y')
        have hMp : IsPGroup p M := hYp.to_le hMY
        obtain ⟨C, hCA, hCnormal, hCcyclic, hCfixed⟩ :=
          exists_normal_cocyclic_centralizerWithin_ne_bot_of_isPGroup
            A' M hAcomm' hMmin.le_normalizer hMp hMmin.ne_bot
        have hCne : C ≠ ⊥ :=
          ne_bot_of_not_isCyclic_of_isCyclic_quotient
            hCnormal hAncyc' hCcyclic
        obtain ⟨aC, haCOne⟩ :=
          Subgroup.ne_bot_iff_exists_ne_one.mp hCne
        let a : G' := aC
        have haC : a ∈ C := aC.property
        have haOne : a ≠ 1 := by
          intro ha
          apply haCOne
          exact Subtype.ext ha
        let X : Subgroup G' := centralizerWithin M C
        have hXK : X ≤ K' := by
          apply (centralizerWithin_mono_left hMY).trans
          apply (centralizerWithin_antitone_right
            (Subgroup.zpowers_le.mpr haC)).trans
          exact hcent' a (hCA haC) haOne
        have hAX : A' ≤ Subgroup.normalizer (X : Set G') := by
          rw [Subgroup.le_normalizer_iff]
          intro g hg x hx
          refine ⟨(Subgroup.le_normalizer_iff.mp hMmin.le_normalizer
            g hg x hx.1), ?_⟩
          intro c hc
          have hgc : Commute g c := by
            exact congrArg Subtype.val
              (mul_comm (⟨g, hg⟩ : A') (⟨c, hCA hc⟩ : A'))
          have hcx : Commute c x := hx.2 c hc
          calc
            c * (g * x * g⁻¹) = (c * g) * x * g⁻¹ := by
              simp only [mul_assoc]
            _ = (g * c) * x * g⁻¹ := by rw [hgc.eq.symm]
            _ = g * (c * x) * g⁻¹ := by simp only [mul_assoc]
            _ = g * (x * c) * g⁻¹ := by rw [hcx.eq]
            _ = g * x * (c * g⁻¹) := by simp only [mul_assoc]
            _ = g * x * (g⁻¹ * c) := by rw [(hgc.symm.inv_right).eq]
            _ = (g * x * g⁻¹) * c := by simp only [mul_assoc]
        have hMX : M ≤ X := by
          apply hMmin.2.2 X (centralizerWithin_le_left M C) hCfixed
          intro g hg x hx
          exact (Subgroup.le_normalizer_iff.mp hAX g hg x hx)
        have hMK : M ≤ K' := hMX.trans hXK
        have hYM : Y' ≤ Subgroup.normalizer (M : Set G') := by
          rw [Subgroup.le_normalizer_iff]
          intro y hy m hm
          have hcomm := (hMcenter hm).2 y hy
          have heq : y * m * y⁻¹ = m := by
            calc
              y * m * y⁻¹ = m * y * y⁻¹ := by rw [hcomm]
              _ = m := by simp
          rw [heq]
          exact hm
        let J : Subgroup G' := A' ⊔ Y'
        have hAJ : A' ≤ J := le_sup_left
        have hYJ : Y' ≤ J := le_sup_right
        let AJ : Subgroup J := A'.subgroupOf J
        let YJ : Subgroup J := Y'.subgroupOf J
        let MJ : Subgroup J := M.subgroupOf J
        let KJ : Subgroup J := K'.comap J.subtype
        letI : YJ.Normal := by
          dsimp [YJ, J]
          exact Subgroup.normal_subgroupOf_sup_of_le_normalizer hAY'
        have hJnormM : J ≤ Subgroup.normalizer (M : Set G') :=
          sup_le hMmin.le_normalizer hYM
        letI : MJ.Normal := by
          dsimp [MJ]
          exact Subgroup.normal_subgroupOf_of_le_normalizer hJnormM
        have hMJYJ : MJ ≤ YJ := by
          intro m hm
          exact hMY hm
        have hMJKJ : MJ ≤ KJ := by
          intro m hm
          exact hMK hm
        have hMJne : MJ ≠ ⊥ := by
          intro hMJbot
          apply hMmin.ne_bot
          have hmap := congrArg (fun L : Subgroup J ↦ L.map J.subtype) hMJbot
          simpa [MJ, Subgroup.map_subgroupOf_eq_of_le
            (hMY.trans hYJ)] using hmap
        have hcopMA : (Nat.card M).Coprime (Nat.card A') :=
          hcop'.coprime_dvd_left (Subgroup.card_dvd_of_le hMY)
        have hcardMJ : Nat.card MJ = Nat.card M :=
          natCard_subgroupOf_eq (hMY.trans hYJ)
        have hcardAJ : Nat.card AJ = Nat.card A' :=
          natCard_subgroupOf_eq hAJ
        have hcopMJAJ : (Nat.card MJ).Coprime (Nat.card AJ) := by
          rw [hcardMJ, hcardAJ]
          exact hcopMA
        have hdisMJAJ : Disjoint MJ AJ :=
          Subgroup.disjoint_of_coprime_natCard hcopMJAJ
        let q : J →* J ⧸ MJ := QuotientGroup.mk' MJ
        let Aq : Subgroup (J ⧸ MJ) := AJ.map q
        let Yq : Subgroup (J ⧸ MJ) := YJ.map q
        let Kq : Subgroup (J ⧸ MJ) := KJ.map q
        have hqAinj : Function.Injective (q.subgroupMap AJ) := by
          rw [← MonoidHom.ker_eq_bot_iff, Subgroup.ker_subgroupMap,
            QuotientGroup.ker_mk', Subgroup.subgroupOf_eq_bot]
          exact hdisMJAJ
        have hAqncyc : ¬ IsCyclic Aq := by
          intro hAqcyc
          letI : IsCyclic Aq := hAqcyc
          have hAJcyc : IsCyclic AJ :=
            isCyclic_of_injective (q.subgroupMap AJ) hqAinj
          exact hAncyc'
            ((Subgroup.subgroupOfEquivOfLe hAJ).isCyclic.mp hAJcyc)
        have hAqcomm : IsMulCommutative Aq := inferInstance
        letI : Yq.Normal :=
          Subgroup.Normal.map (inferInstance : YJ.Normal) q
            (QuotientGroup.mk'_surjective MJ)
        have hAqYq : Aq ≤ Subgroup.normalizer (Yq : Set (J ⧸ MJ)) :=
          Subgroup.le_normalizer_of_normal
        let eYJ : YJ ≃* Y' := Subgroup.subgroupOfEquivOfLe hYJ
        letI : IsSolvable Y' := hYsol'
        letI : IsSolvable YJ :=
          solvable_of_solvable_injective (f := eYJ.toMonoidHom) eYJ.injective
        have hYqsol : IsSolvable Yq :=
          solvable_of_surjective (f := q.subgroupMap YJ)
            (q.subgroupMap_surjective YJ)
        have hcardYJ : Nat.card YJ = Nat.card Y' :=
          natCard_subgroupOf_eq hYJ
        have hYqdivY : Nat.card Yq ∣ Nat.card Y' := by
          rw [← hcardYJ]
          exact Subgroup.card_map_dvd YJ q
        have hAqdivA : Nat.card Aq ∣ Nat.card A' := by
          rw [← hcardAJ]
          exact Subgroup.card_map_dvd AJ q
        have hcopq : (Nat.card Yq).Coprime (Nat.card Aq) :=
          (hcop'.coprime_dvd_left hYqdivY).coprime_dvd_right hAqdivA
        have hAJYJ : AJ ⊔ YJ = ⊤ := by
          change A'.subgroupOf J ⊔ Y'.subgroupOf J = ⊤
          rw [← Subgroup.subgroupOf_sup hAJ hYJ]
          exact Subgroup.subgroupOf_self J
        let qY : J →* J ⧸ YJ := QuotientGroup.mk' YJ
        have hYJmap : YJ.map qY = ⊥ := by
          apply (Subgroup.map_eq_bot_iff YJ).mpr
          rw [QuotientGroup.ker_mk']
        have hAJmap : AJ.map qY = ⊤ := by
          have hmapSup : AJ.map qY ⊔ YJ.map qY = ⊤ := by
            rw [← Subgroup.map_sup, hAJYJ]
            exact Subgroup.map_top_of_surjective qY
              (QuotientGroup.mk'_surjective YJ)
          rwa [hYJmap, sup_bot_eq] at hmapSup
        let fAJ : AJ →* J ⧸ YJ := qY.comp AJ.subtype
        have hfAJ : Function.Surjective fAJ := by
          intro z
          have hz : z ∈ AJ.map qY := by
            rw [hAJmap]
            trivial
          rcases hz with ⟨a, ha, haz⟩
          exact ⟨⟨a, ha⟩, haz⟩
        letI : IsSolvable AJ :=
          isSolvable_of_comm fun x y ↦ mul_comm x y
        letI : IsSolvable (J ⧸ YJ) :=
          solvable_of_surjective (f := fAJ) hfAJ
        letI : IsSolvable J :=
          solvable_of_ker_le_range YJ.subtype qY (by
            rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
        have hcentq : ∀ aq : J ⧸ MJ, aq ∈ Aq → aq ≠ 1 →
            centralizerWithin Yq (Subgroup.zpowers aq) ≤ Kq := by
          intro aq haqA haqOne z hz
          rcases haqA with ⟨aJ, haAJ, haq⟩
          let aG : G' := (aJ : J)
          have haG : aG ∈ A' := haAJ
          have haGOne : aG ≠ 1 := by
            intro haOne
            apply haqOne
            rw [← haq]
            have haJOne : aJ = 1 := Subtype.ext haOne
            rw [haJOne, map_one]
          have hRleAJ : Subgroup.zpowers aJ ≤ AJ :=
            Subgroup.zpowers_le.mpr haAJ
          have hcopMJR :
              (Nat.card MJ).Coprime (Nat.card (Subgroup.zpowers aJ)) :=
            hcopMJAJ.coprime_dvd_right
              (Subgroup.card_dvd_of_le hRleAJ)
          have hmapCent :=
            map_centralizerWithin_quotient_eq_of_coprime
              hMJYJ hcopMJR
          have hmapCent' :
              (centralizerWithin YJ (Subgroup.zpowers aJ)).map q =
                centralizerWithin Yq (Subgroup.zpowers aq) := by
            calc
              (centralizerWithin YJ (Subgroup.zpowers aJ)).map q =
                  centralizerWithin Yq (Subgroup.zpowers (q aJ)) := by
                simpa only [q, Yq, MonoidHom.map_zpowers] using hmapCent
              _ = centralizerWithin Yq (Subgroup.zpowers aq) := by rw [haq]
          rw [← hmapCent'] at hz
          rcases hz with ⟨cJ, hcJ, hcz⟩
          refine ⟨cJ, ?_, hcz⟩
          change ((cJ : J) : G') ∈ K'
          apply hcent' aG haG haGOne
          refine ⟨hcJ.1, ?_⟩
          intro r hr
          obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hr
          have hc := hcJ.2 (aJ ^ m) (Subgroup.zpow_mem_zpowers aJ m)
          exact congrArg (fun t : J ↦ (t : G')) hc
        have hYqlt : Nat.card Yq < n := by
          have hlt := natCard_map_quotient_lt hMJYJ hMJne
          rw [hcardYJ, hcard] at hlt
          exact hlt
        have hYqKq : Yq ≤ Kq :=
          ih (Nat.card Yq) hYqlt (J ⧸ MJ) Aq Yq Kq rfl
            hAqcomm hAqncyc hAqYq hcopq hYqsol hcentq
        apply hYK
        intro y hy
        let yJ : J := ⟨y, hYJ hy⟩
        have hqyYq : q yJ ∈ Yq := ⟨yJ, hy, rfl⟩
        have hqyKq := hYqKq hqyYq
        rcases hqyKq with ⟨kJ, hkJ, hkqy⟩
        have hdiff : kJ⁻¹ * yJ ∈ MJ :=
          QuotientGroup.eq.mp (hkqy.trans rfl)
        have hdiffK : kJ⁻¹ * yJ ∈ KJ := hMJKJ hdiff
        have hyKJ : yJ ∈ KJ := by
          rw [show yJ = kJ * (kJ⁻¹ * yJ) by group]
          exact KJ.mul_mem hkJ hdiffK
        exact hyKJ
      · have hSlt : S' < Y' := lt_of_le_of_ne hSY hSeq
        have hScard : Nat.card S' < n := by
          rw [← hcard]
          exact natCard_subgroup_lt_of_lt hSlt
        have hScop : (Nat.card S').Coprime (Nat.card A') :=
          hcop'.coprime_dvd_left (Subgroup.card_dvd_of_le hSY)
        let toY : S' →* Y' := Subgroup.inclusion hSY
        letI : IsSolvable Y' := hYsol'
        have hSsol : IsSolvable S' :=
          solvable_of_solvable_injective (f := toY)
            (Subgroup.inclusion_injective hSY)
        have hcentS : ∀ a : G', a ∈ A' → a ≠ 1 →
            centralizerWithin S' (Subgroup.zpowers a) ≤ K' := by
          intro a ha haOne
          exact (centralizerWithin_mono_left hSY).trans
            (hcent' a ha haOne)
        have hSK : S' ≤ K' :=
          ih (Nat.card S') hScard G' A' S' K' rfl hAcomm'
            hAncyc' hAnormS hScop hSsol hcentS
        have hSH : (S : Subgroup Y') ≤ H := by
          intro s hs
          change (s : G') ∈ K'
          exact hSK ⟨s, hs, rfl⟩
        exact S.not_dvd_index
          (hpIndex.trans (Subgroup.index_dvd_of_le hSH))
  exact hP (Nat.card Y) G A Y K rfl hAcomm hAncyc hAY hcop hYsol hcent

end Submission.OddOrder.MathlibSupport
