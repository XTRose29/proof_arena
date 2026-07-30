import Submission.OddOrder.MathlibSupport.CoprimeAbelianCentralizerGenerationSolvable

/-!
# Centralizer generation from cocyclic subgroups

This is the specialized cocyclic-subgroup eliminator needed in
`BGsection9.v`.  A noncyclic coprime abelian group of automorphisms of a
finite solvable group generates that group from the fixed-point subgroups of
its normal cocyclic subgroups.  The upstream Bender--Glauberman Proposition
1.16 is more general; the theorem below records exactly the
noncyclic/solvable instance consumed by Lemma 9.5.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative

universe u

private theorem map_centralizerWithin_quotient_eq_of_coprime_cocyclic
    {K : Type u} [Group K] [Finite K] [IsSolvable K]
    {N Y R : Subgroup K} [N.Normal]
    (hNY : N ≤ Y)
    (hcop : Nat.Coprime (Nat.card N) (Nat.card R)) :
    (centralizerWithin Y R).map (QuotientGroup.mk' N) =
      centralizerWithin (Y.map (QuotientGroup.mk' N))
        (R.map (QuotientGroup.mk' N)) := by
  classical
  let q : K →* K ⧸ N := QuotientGroup.mk' N
  have hcent := map_centralizer_quotient_eq_of_coprime hcop
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

private theorem natCard_map_quotient_lt_cocyclic
    {K : Type u} [Group K] [Finite K]
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

/-- The specialized noncyclic/solvable cocyclic-subgroup eliminator used in
the proof of Bender--Glauberman Lemma 9.5. -/
theorem le_of_centralizerWithin_cocyclic_le_of_coprime_abelian_solvable
    {G : Type u} [Group G] [Finite G]
    {A Y K : Subgroup G}
    (hAcomm : IsMulCommutative A)
    (hAncyc : ¬ IsCyclic A)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hcop : Nat.Coprime (Nat.card Y) (Nat.card A))
    (hYsol : IsSolvable Y)
    (hcent : ∀ C : Subgroup G, C ≤ A →
      (C.subgroupOf A).Normal →
      IsCyclic (A ⧸ C.subgroupOf A) →
      centralizerWithin Y C ≤ K) :
    Y ≤ K := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∀ (G' : Type u) [Group G'] [Finite G']
      (A' Y' K' : Subgroup G') [IsMulCommutative A'],
      Nat.card Y' = n →
      (¬ IsCyclic A') →
      A' ≤ Subgroup.normalizer (Y' : Set G') →
      (Nat.card Y').Coprime (Nat.card A') →
      IsSolvable Y' →
      (∀ C : Subgroup G', C ≤ A' →
        (C.subgroupOf A').Normal →
        IsCyclic (A' ⧸ C.subgroupOf A') →
        centralizerWithin Y' C ≤ K') →
      Y' ≤ K'
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      dsimp only [P]
      intro G' _ _ A' Y' K' hAcomm' hcard hAncyc' hAY' hcop'
        hYsol' hcent'
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
      let S' : Subgroup G' := (S : Subgroup Y').map Y'.subtype
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
          refine ⟨(Subgroup.mem_normalizer_iff.mp (hAY' ha) z).mp hz.1, ?_⟩
          intro y hy
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
        let X : Subgroup G' := centralizerWithin M C
        have hXK : X ≤ K' :=
          (centralizerWithin_mono_left hMY).trans
            (hcent' C hCA hCnormal hCcyclic)
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
        let eAJ : A' ≃* AJ :=
          (Subgroup.subgroupOfEquivOfLe hAJ).symm
        let eMap : AJ ≃* Aq :=
          MulEquiv.ofBijective (q.subgroupMap AJ)
            ⟨hqAinj, q.subgroupMap_surjective AJ⟩
        let eAq : A' ≃* Aq := eAJ.trans eMap
        have heAq_apply (a : A') :
            ((eAq a : Aq) : J ⧸ MJ) = q (Subgroup.inclusion hAJ a) := by
          rfl
        have hcentq : ∀ Cq : Subgroup (J ⧸ MJ), Cq ≤ Aq →
            (Cq.subgroupOf Aq).Normal →
            IsCyclic (Aq ⧸ Cq.subgroupOf Aq) →
            centralizerWithin Yq Cq ≤ Kq := by
          intro Cq hCqA hCqnormal hCqcyclic
          let CAq : Subgroup Aq := Cq.subgroupOf Aq
          let CA' : Subgroup A' := CAq.comap eAq.toMonoidHom
          have hCA'normal : CA'.Normal := by
            dsimp only [CA']
            exact Subgroup.Normal.comap hCqnormal eAq.toMonoidHom
          let φ : A' →* Aq ⧸ CAq :=
            (QuotientGroup.mk' CAq).comp eAq.toMonoidHom
          have hφsurj : Function.Surjective φ :=
            (QuotientGroup.mk'_surjective CAq).comp eAq.surjective
          have hkerφ : φ.ker = CA' := by
            ext a
            change QuotientGroup.mk' CAq (eAq a) = 1 ↔ eAq a ∈ CAq
            exact QuotientGroup.eq_one_iff (eAq a)
          let eQuot : A' ⧸ CA' ≃* Aq ⧸ CAq :=
            (QuotientGroup.quotientMulEquivOfEq hkerφ.symm).trans
              (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj)
          have hCA'cyclic : IsCyclic (A' ⧸ CA') :=
            eQuot.isCyclic.mpr hCqcyclic
          let C : Subgroup G' := CA'.map A'.subtype
          have hCA : C ≤ A' := Subgroup.map_subtype_le CA'
          have hCsub : C.subgroupOf A' = CA' := by
            change (CA'.map A'.subtype).comap A'.subtype = CA'
            exact Subgroup.comap_map_eq_self_of_injective
              A'.subtype_injective CA'
          have hCnormal : (C.subgroupOf A').Normal := by
            rw [hCsub]
            exact hCA'normal
          have hCcyclic : IsCyclic (A' ⧸ C.subgroupOf A') := by
            exact (QuotientGroup.quotientMulEquivOfEq hCsub).isCyclic.mpr
              hCA'cyclic
          let iA : A' →* J := Subgroup.inclusion hAJ
          let CJ : Subgroup J := CA'.map iA
          have hCJleAJ : CJ ≤ AJ := by
            rintro _ ⟨a, ha, rfl⟩
            exact a.property
          have hCJmap : CJ.map q = Cq := by
            apply le_antisymm
            · rintro _ ⟨j, ⟨a, ha, rfl⟩, rfl⟩
              have hea : eAq a ∈ CAq := ha
              change ((eAq a : Aq) : J ⧸ MJ) ∈ Cq at hea
              rw [heAq_apply] at hea
              exact hea
            · intro x hx
              have hxAq : x ∈ Aq := hCqA hx
              let xa : Aq := ⟨x, hxAq⟩
              obtain ⟨a, ha⟩ := eAq.surjective xa
              have haCA' : a ∈ CA' := by
                change eAq a ∈ CAq
                rw [ha]
                exact hx
              refine ⟨iA a, ⟨a, haCA', rfl⟩, ?_⟩
              exact (heAq_apply a).symm.trans
                (congrArg Subtype.val ha)
          have hcopMJCJ : (Nat.card MJ).Coprime (Nat.card CJ) :=
            hcopMJAJ.coprime_dvd_right
              (Subgroup.card_dvd_of_le hCJleAJ)
          have hmapCent :=
            map_centralizerWithin_quotient_eq_of_coprime_cocyclic
              hMJYJ hcopMJCJ
          have hmapCent' :
              (centralizerWithin YJ CJ).map q =
                centralizerWithin Yq Cq := by
            rw [hmapCent, hCJmap]
          intro z hz
          rw [← hmapCent'] at hz
          rcases hz with ⟨cJ, hcJ, hcz⟩
          refine ⟨cJ, ?_, hcz⟩
          change ((cJ : J) : G') ∈ K'
          apply hcent' C hCA hCnormal hCcyclic
          refine ⟨hcJ.1, ?_⟩
          intro c hc
          rcases hc with ⟨a, haCA', rfl⟩
          have hiA : iA a ∈ CJ := ⟨a, haCA', rfl⟩
          exact congrArg Subtype.val (hcJ.2 (iA a) hiA)
        have hYqlt : Nat.card Yq < n := by
          have hlt := natCard_map_quotient_lt_cocyclic hMJYJ hMJne
          rw [hcardYJ, hcard] at hlt
          exact hlt
        letI : IsMulCommutative Aq := hAqcomm
        have hYqKq : Yq ≤ Kq :=
          ih (Nat.card Yq) hYqlt (J ⧸ MJ) Aq Yq Kq rfl
            hAqncyc hAqYq hcopq hYqsol hcentq
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
        have hcentS : ∀ C : Subgroup G', C ≤ A' →
            (C.subgroupOf A').Normal →
            IsCyclic (A' ⧸ C.subgroupOf A') →
            centralizerWithin S' C ≤ K' := by
          intro C hCA hCnormal hCcyclic
          exact (centralizerWithin_mono_left hSY).trans
            (hcent' C hCA hCnormal hCcyclic)
        have hSK : S' ≤ K' :=
          ih (Nat.card S') hScard G' A' S' K' rfl
            hAncyc' hAnormS hScop hSsol hcentS
        have hSH : (S : Subgroup Y') ≤ H := by
          intro s hs
          change (s : G') ∈ K'
          exact hSK ⟨s, hs, rfl⟩
        exact S.not_dvd_index
          (hpIndex.trans (Subgroup.index_dvd_of_le hSH))
  letI : IsMulCommutative A := hAcomm
  exact hP (Nat.card Y) G A Y K rfl hAncyc hAY hcop hYsol hcent

end Submission.OddOrder.MathlibSupport
