import Submission.OddOrder.BG.Section04.RankTwoMaximalPrimeCoreSylow
import Submission.OddOrder.BG.Section07.NormedTransSuperset
import Submission.OddOrder.BG.Section07.ThompsonTransitivity
import Submission.OddOrder.BG.Section09.AnyFittingRankThreeUniqueness
import Submission.OddOrder.MathlibSupport.ElementaryAbelianRankSylowTransport
import Submission.OddOrder.MathlibSupport.MaximalPrimeDivisor

/-!
# Bender--Glauberman Section 9: SCN rank-three Sylow normalizers

This file ports the first main block in the proof of Bender--Glauberman
Lemma 9.5.  If a rank-three SCN subgroup is not contained in a unique
maximal subgroup, then every maximal subgroup containing its centralizer
also contains the normalizer of the associated Sylow subgroup.
-/

namespace Submission.OddOrder.BG.Section09

open Submission.OddOrder
open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.MathlibSupport
open scoped Pointwise

universe u

/-- If a rank-three SCN subgroup is not uniquely maximal, no maximal
subgroup has Fitting subgroup of elementary-abelian `p`-rank at least
three.  This is the fact `FmCAp_le2` in `BGsection9.v`. -/
theorem no_fitting_rank_three_of_scn_not_unique
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {A : Subgroup G}
    (hSCN : IsSCN (P : Subgroup G) A)
    (hRankA : 3 ≤ Group.rank A)
    (hnotuniq : A ∉ minSimple_uniq_max_groups (G := G)) :
    ∀ {M : Subgroup G}, M ∈ minSimple_max_groups (G := G) →
      ¬ HasElementaryAbelianRankAtLeast p 3 (fittingWithin M) := by
  have hAp : IsPGroup p A :=
    IsPGroup.to_le P.isPGroup' hSCN.le_sylow
  obtain ⟨E, hEA, hE⟩ :=
    exists_elementaryAbelian_rank_three_le_of_group_rank
      A hAp hSCN.commutative hRankA
  intro M hM hRankF
  exact hnotuniq
    (any_rank3_Fitting_Uniqueness hM hRankF hAp ⟨E, hEA, hE⟩)

/-- `BGsection9.v: sNP_mCA`, the Sylow-normalizer containment in the first
part of the proof of Bender--Glauberman Lemma 9.5. -/
theorem normalizer_sylow_le_maximal_of_scn_not_unique
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {A : Subgroup G}
    (hSCN : IsSCN (P : Subgroup G) A)
    (hRankA : 3 ≤ Group.rank A)
    (hnotuniq : A ∉ minSimple_uniq_max_groups (G := G)) :
    ∀ {M : Subgroup G}, M ∈ minSimple_max_groups (G := G) →
      Subgroup.centralizer (A : Set G) ≤ M →
      Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ M := by
  classical
  intro M hM hCAM
  have hAp : IsPGroup p A :=
    IsPGroup.to_le P.isPGroup' hSCN.le_sylow
  obtain ⟨EA, hEAA, hEA⟩ :=
    exists_elementaryAbelian_rank_three_le_of_group_rank
      A hAp hSCN.commutative hRankA
  have hRankAea : HasElementaryAbelianRankAtLeast p 3 A :=
    ⟨EA, hEAA, hEA⟩
  have hAne : A ≠ ⊥ := by
    intro hAbot
    have hzero : Group.rank A = 0 := by
      rw [hAbot]
      exact Group.rank_eq_zero _
    omega
  letI : Nontrivial A := A.nontrivial_iff_ne_bot.mpr hAne
  have hsupport : primeSupport (Nat.card A) = {p} :=
    hAp.primeSupport_natCard_eq_singleton
  have hAat : A ∈ minSimple_SCN_at (G := G) 3 p :=
    ⟨P, hSCN, hRankA⟩
  have hcstrA : NormedConstrained A :=
    SCN_normed_constrained p P A hSCN (by omega)
  have hFnot :
      ¬ HasElementaryAbelianRankAtLeast p 3 (fittingWithin M) :=
    no_fitting_rank_three_of_scn_not_unique
      P hSCN hRankA hnotuniq hM

  have hNRM : ∀ {R : Subgroup G}, A ≤ R →
      R ≤ (P : Subgroup G) ⊓ M →
      Subgroup.normalizer (R : Set G) ≤ M := by
    intro R hAR hRPM
    have hRP : R ≤ (P : Subgroup G) := hRPM.trans inf_le_left
    have hRM : R ≤ M := hRPM.trans inf_le_right
    have hRp : IsPGroup p R :=
      IsPGroup.to_le P.isPGroup' hRP

    obtain ⟨q, hq, hqp, Q, hQmax, hNQ⟩ :
        ∃ q : ℕ, q.Prime ∧ q ≠ p ∧
          ∃ Q : Subgroup G,
            Q ∈ max_normed_pgroups (R : Set G) ({q} : Set ℕ) ∧
            Subgroup.normalizer (Q : Set G) ≤ M := by
      by_cases hFhigh : ∃ q : ℕ, q.Prime ∧
          HasElementaryAbelianRankAtLeast q 3 (fittingWithin M)
      · obtain ⟨q, hq, E, hEF, hE⟩ := hFhigh
        letI : Fact q.Prime := ⟨hq⟩
        have hqp : q ≠ p := by
          intro hqp
          subst q
          exact hFnot ⟨E, hEF, hE⟩
        let Oq : Subgroup G := (pCore q M).map M.subtype
        have hOqM : Oq ≤ M := by
          dsimp only [Oq]
          exact Subgroup.map_subtype_le _
        have hOqp : IsPGroup q Oq := by
          dsimp only [Oq]
          exact pCore_isPGroup.map M.subtype
        have hOqnormal : (Oq.subgroupOf M).Normal := by
          change (((pCore q M).map M.subtype).comap M.subtype).Normal
          rw [Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
          infer_instance
        have hEsub :
            IsElementaryAbelianOfRank q 3
              (E.subgroupOf (fittingWithin M)) :=
          hE.subgroupOf hEF
        have hEcore : E.subgroupOf (fittingWithin M) ≤
            pCore q (fittingWithin M) :=
          hEsub.isPGroup.le_pCore_of_isNilpotent
        have hEOq : E ≤ Oq := by
          rw [← Subgroup.map_subgroupOf_eq_of_le hEF]
          calc
            (E.subgroupOf (fittingWithin M)).map
                  (fittingWithin M).subtype ≤
                (pCore q (fittingWithin M)).map
                  (fittingWithin M).subtype :=
              Subgroup.map_mono hEcore
            _ = Oq := by
              simpa only [Oq] using
                map_pCore_fittingWithin_eq_map_pCore M q
        have hRankOq : HasElementaryAbelianRankAtLeast q 3 Oq :=
          ⟨E, hEOq, hE⟩
        have hOqne : Oq ≠ ⊥ := by
          intro hOqbot
          exact hE.ne_bot
            (eq_bot_iff.mpr (hEOq.trans hOqbot.le))
        have hRnormOq : R ≤ Subgroup.normalizer (Oq : Set G) := by
          exact hRM.trans
            ((Subgroup.normal_subgroupOf_iff_le_normalizer hOqM).mp
              hOqnormal)
        have hOqpi : IsPiNumber ({q} : Set ℕ) (Nat.card Oq) :=
          hOqp.isPiNumber_natCard (Set.mem_singleton q)
        obtain ⟨Q, hQmax, hOqQ⟩ :=
          max_normed_exists (R : Set G) ({q} : Set ℕ) Oq
            hOqpi hRnormOq
        have hQp : IsPGroup q Q :=
          isPGroup_of_isPiNumber_singleton (mem_max_normed hQmax).1
        have hQne : Q ≠ ⊥ := by
          intro hQbot
          exact hOqne (eq_bot_iff.mpr (hOqQ.trans hQbot.le))
        have hOquniq :
            Oq ∈ minSimple_uniq_max_groups (G := G) :=
          any_rank3_Fitting_Uniqueness hM ⟨E, hEF, hE⟩
            hOqp hRankOq
        have hOqdef :
            minSimple_max_groups_of (G := G) (Oq : Set G) = {M} :=
          def_uniq_mmax hOquniq hM hOqM
        have hNQproper : Subgroup.normalizer (Q : Set G) < ⊤ :=
          mFT_norm_proper Q hQne (mFT_pgroup_proper Q hQp)
        have hNQ : Subgroup.normalizer (Q : Set G) ≤ M :=
          sub_uniq_mmax hOqdef
            (hOqQ.trans Subgroup.le_normalizer) hNQproper
        exact ⟨q, hq, hqp, Q, hQmax, hNQ⟩
      · have hMcard : 1 < Nat.card M :=
          M.one_lt_card_iff_ne_bot.mpr (mmax_neq1 hM)
        obtain ⟨q, hq, hqM, hqmax⟩ :=
          exists_maximal_prime_divisor hMcard
        letI : Fact q.Prime := ⟨hq⟩
        have hRankCore : ∀ r : ℕ, r.Prime →
            ¬ ∃ E : Subgroup (fittingCore M),
              IsElementaryAbelianOfRank r 3 E := by
          intro r hr
          rintro ⟨E, hE⟩
          let EM : Subgroup M := E.map (fittingCore M).subtype
          let EG : Subgroup G := EM.map M.subtype
          have hEM : IsElementaryAbelianOfRank r 3 EM := by
            dsimp only [EM]
            exact hE.map_of_injective (fittingCore M).subtype
              (fittingCore M).subtype_injective
          have hEG : IsElementaryAbelianOfRank r 3 EG := by
            dsimp only [EG]
            exact hEM.map_of_injective M.subtype M.subtype_injective
          have hEGF : EG ≤ fittingWithin M := by
            dsimp only [EG, EM, fittingWithin]
            exact Subgroup.map_mono (Subgroup.map_subtype_le E)
          exact hFhigh ⟨r, hr, EG, hEGF, hEG⟩
        have hIndex : ¬ q ∣ (pCore q M).index :=
          rank2_max_pcore_Sylow hqmax (mFT_odd M) (mmax_sol hM)
            hRankCore
        let S : Sylow q M := pCore_isPGroup.toSylow hIndex
        let Oq : Subgroup G := (S : Subgroup M).map M.subtype
        have hOqM : Oq ≤ M := by
          dsimp only [Oq]
          exact Subgroup.map_subtype_le _
        have hOqp : IsPGroup q Oq := by
          dsimp only [Oq]
          exact S.isPGroup'.map M.subtype
        have hOqnormal : (Oq.subgroupOf M).Normal := by
          change ((((S : Subgroup M).map M.subtype).comap
            M.subtype)).Normal
          rw [Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
          change (pCore q M).Normal
          infer_instance
        have hOqF : Oq ≤ fittingWithin M := by
          dsimp only [Oq, S, fittingWithin]
          exact Subgroup.map_mono (pCore_le_fittingCore q)
        have hqp : q ≠ p := by
          intro hqp
          subst q
          have hNoFsub :
              ¬ ∃ E : Subgroup (fittingWithin M),
                IsElementaryAbelianOfRank p 3 E := by
            rintro ⟨E, hE⟩
            apply hFnot
            exact ⟨E.map (fittingWithin M).subtype,
              Subgroup.map_subtype_le E,
              hE.map_of_injective (fittingWithin M).subtype
                (fittingWithin M).subtype_injective⟩
          have hNoM :
              ¬ ∃ E : Subgroup M,
                IsElementaryAbelianOfRank p 3 E :=
            no_elementaryAbelian_rank_three_of_sylow_map_le
              S hOqF hNoFsub
          have hAM : A ≤ M :=
            (Subgroup.le_centralizer_iff_isMulCommutative.mpr
              hSCN.commutative).trans hCAM
          apply hNoM
          exact ⟨EA.subgroupOf M,
            hEA.subgroupOf (hEAA.trans hAM)⟩
        have hOqne : Oq ≠ ⊥ := by
          intro hOqbot
          have hSbot : (S : Subgroup M) = ⊥ :=
            (Subgroup.map_eq_bot_iff_of_injective
              (S : Subgroup M) M.subtype_injective).mp hOqbot
          exact S.ne_bot_of_dvd_card hqM hSbot
        have hNOq : Subgroup.normalizer (Oq : Set G) = M :=
          mmax_normal hM hOqM hOqnormal hOqne
        obtain ⟨T, hTOq⟩ :=
          mmax_sigma_Sylow hM S (by rw [hNOq])
        have hRnormOq : R ≤ Subgroup.normalizer (Oq : Set G) := by
          rw [hNOq]
          exact hRM
        have hOqpi : IsPiNumber ({q} : Set ℕ) (Nat.card Oq) :=
          hOqp.isPiNumber_natCard (Set.mem_singleton q)
        obtain ⟨Q, hQmax, hOqQ⟩ :=
          max_normed_exists (R : Set G) ({q} : Set ℕ) Oq
            hOqpi hRnormOq
        have hQp : IsPGroup q Q :=
          isPGroup_of_isPiNumber_singleton (mem_max_normed hQmax).1
        have hQeq : Q = Oq := by
          calc
            Q = (T : Subgroup G) :=
              T.is_maximal' hQp (hTOq.trans_le hOqQ)
            _ = Oq := hTOq
        have hNQ : Subgroup.normalizer (Q : Set G) ≤ M := by
          rw [hQeq, hNOq]
        exact ⟨q, hq, hqp, Q, hQmax, hNQ⟩

    letI : Fact q.Prime := ⟨hq⟩
    have hqA : q ∉ primeSupport (Nat.card A) := by
      rw [hsupport]
      simpa only [Set.mem_singleton_iff] using hqp
    have hARnormal : (A.subgroupOf R).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hAR).mpr
        (hRP.trans hSCN.le_normalizer)
    have hsnAR : (A.subgroupOf R).IsSubnormal :=
      hARnormal.isSubnormal
    have hRpi :
        IsPiNumber (primeSupport (Nat.card A)) (Nat.card R) := by
      rw [hsupport]
      exact hRp.isPiNumber_natCard (Set.mem_singleton p)
    have htransA : ∀ Q₁ Q₂ : Subgroup G,
        Q₁ ∈ max_normed_pgroups (A : Set G) ({q} : Set ℕ) →
        Q₂ ∈ max_normed_pgroups (A : Set G) ({q} : Set ℕ) →
        ∃ k : G, k ∈ centralPrimeComplementCore A ∧
          Q₂ = Q₁.map (MulAut.conj k⁻¹).toMonoidHom := by
      intro Q₁ Q₂ hQ₁ hQ₂
      obtain ⟨k, hk, hconj⟩ :=
        Thompson_transitivity p q A hAat hqp Q₁ Q₂ hQ₁ hQ₂
      refine ⟨k, ?_, hconj⟩
      rw [centralPrimeComplementCore_eq_map_pPrimeCore
        (p := p) A hsupport]
      exact hk
    have hsup :=
      normed_trans_superset A R hcstrA hqA hAR hsnAR hRpi htransA
    have hfactor := (hsup.2.2.2 Q hQmax).2
    have hcoreCent : centralPrimeComplementCore A ≤
        Subgroup.centralizer (A : Set G) := by
      exact primeSetCore_le _ _
    have hleft : centralizerWithin (centralPrimeComplementCore A) R ≤ M :=
      (centralizerWithin_le_left _ _).trans (hcoreCent.trans hCAM)
    intro x hx
    have hxprod : x ∈
        (centralizerWithin (centralPrimeComplementCore A) R : Set G) *
          ((Subgroup.normalizer (R : Set G) ⊓
            Subgroup.normalizer (Q : Set G) : Subgroup G) : Set G) := by
      rw [← hfactor]
      exact hx
    rcases hxprod with ⟨y, hy, z, hz, rfl⟩
    exact M.mul_mem (hleft hy) (hNQ hz.2)

  have hAM : A ≤ M :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr
      hSCN.commutative).trans hCAM
  have hNA : Subgroup.normalizer (A : Set G) ≤ M :=
    hNRM le_rfl (le_inf hSCN.le_sylow hAM)
  have hPM : (P : Subgroup G) ≤ M :=
    hSCN.le_normalizer.trans hNA
  exact hNRM hSCN.le_sylow (le_inf le_rfl hPM)

end Submission.OddOrder.BG.Section09
