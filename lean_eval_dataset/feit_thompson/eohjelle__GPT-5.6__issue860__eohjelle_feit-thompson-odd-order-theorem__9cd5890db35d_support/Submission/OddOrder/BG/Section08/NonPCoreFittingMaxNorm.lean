import Submission.OddOrder.BG.Section08.NonPCoreFittingConstrained
import Submission.OddOrder.BG.Section07.NormedConstrainedRankThreeTrans
import Submission.OddOrder.BG.Section07.NormedTransSuperset

/-!
# Bender--Glauberman Theorem 8.1(a): maximal normalized subgroups

This file ports the singleton maximal-normalized-family step in the proof of
Bender--Glauberman Theorem 8.1(a).
-/

namespace Submission.OddOrder.BG.Section08

open Submission.OddOrder
open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.BG.Section07

universe u

/-- For a prime outside the support of the constrained centralizer, the
trivial subgroup is the unique maximal subgroup normalized by that
centralizer. -/
theorem non_pcore_fitting_max_normed_eq_bot
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    (p : ℕ) [Fact p.Prime] (M A₀ : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hFp : ¬ IsPGroup p (fittingWithin M))
    (hA₀ : IsPMaxElem p (fittingWithin M) A₀)
    (hRank3 : ∃ E : Subgroup G,
      E ≤ A₀ ∧ IsElementaryAbelianOfRank p 3 E)
    (q : ℕ)
    (hq : q ∉ primeSupport
      (Nat.card (centralizerWithin (fittingWithin M) A₀))) :
    max_normed_pgroups
      (centralizerWithin (fittingWithin M) A₀ : Set G)
      ({q} : Set ℕ) = {⊥} := by
  classical
  let F : Subgroup G := fittingWithin M
  let A : Subgroup G := centralizerWithin F A₀
  let pi : Set ℕ := primeSupport (Nat.card A)
  let K : Subgroup G := centralPrimeComplementCore A
  have hA₀F : A₀ ≤ F := hA₀.le
  have hA₀A : A₀ ≤ A := by
    exact le_inf hA₀F
      (Subgroup.le_centralizer_iff_isMulCommutative.mpr
        hA₀.elementary.commutative)
  have hAF : A ≤ F := centralizerWithin_le_left F A₀
  have hpA : p ∈ pi := by
    simpa [A, F, pi] using
      (non_pcore_fitting_prime_mem p M A₀ hA₀ hRank3)
  have hCApi :
      IsPiNumber pi (Nat.card (Subgroup.centralizer (A : Set G))) := by
    simpa [A, F, pi] using
      (non_pcore_fitting_centralizer_isPiNumber
        M A₀ hM hA₀F hA₀A p hpA)
  have hKpi : IsPiNumber piᶜ (Nat.card K) := by
    simpa [K, centralPrimeComplementCore, pi] using
      (primeSetCore_isPiNumber piᶜ
        (Subgroup.centralizer (A : Set G)))
  have hKle : K ≤ Subgroup.centralizer (A : Set G) := by
    simpa [K, centralPrimeComplementCore, pi] using
      (primeSetCore_le piᶜ (Subgroup.centralizer (A : Set G)))
  have hKbot : K = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rw [Nat.eq_one_iff_not_exists_prime_dvd]
    intro r hr hrdvd
    exact (hKpi hr hrdvd)
      (hCApi hr (hrdvd.trans (Subgroup.card_dvd_of_le hKle)))
  have hcstrA : NormedConstrained A := by
    simpa [A, F] using
      (non_pcore_fitting_normedConstrained
        p M A₀ hM hFp hA₀ hRank3)
  have hRankA : ∃ (r : ℕ) (E : Subgroup G),
      r.Prime ∧ E ≤ A ∧ A ≤ Subgroup.centralizer (E : Set G) ∧
        IsElementaryAbelianOfRank r 3 E := by
    obtain ⟨E, hEA₀, hErank⟩ := hRank3
    refine ⟨p, E, Fact.out, hEA₀.trans hA₀A, ?_, hErank⟩
    have hAcentA₀ : A ≤ Subgroup.centralizer (A₀ : Set G) := by
      exact inf_le_right
    exact hAcentA₀.trans (Subgroup.centralizer_le hEA₀)
  have htransA : ∀ Q₁ Q₂ : Subgroup G,
      Q₁ ∈ max_normed_pgroups (A : Set G) ({q} : Set ℕ) →
      Q₂ ∈ max_normed_pgroups (A : Set G) ({q} : Set ℕ) →
      ∃ k : G, k ∈ K ∧
        Q₂ = Q₁.map (MulAut.conj k⁻¹).toMonoidHom := by
    simpa [K] using
      (normed_constrained_rank3_trans A hcstrA hq hRankA)
  obtain ⟨Q, hQmaxA, _hbotQ⟩ :=
    max_normed_exists (A : Set G) ({q} : Set ℕ) (⊥ : Subgroup G)
      (by simpa using (IsPiNumber.one (pi := ({q} : Set ℕ))))
      (by exact Subgroup.le_normalizer_of_normal)
  have huniqA :
      max_normed_pgroups (A : Set G) ({q} : Set ℕ) = {Q} := by
    ext R
    constructor
    · intro hR
      obtain ⟨k, hkK, hRQ⟩ := htransA Q R hQmaxA hR
      have hkBot : k ∈ (⊥ : Subgroup G) := by
        simpa [hKbot] using hkK
      have hk : k = 1 := Subgroup.mem_bot.mp hkBot
      subst k
      have hRQ' : R = Q := by
        have hconjOne :
            (MulAut.conj (1 : G)⁻¹).toMonoidHom = MonoidHom.id G := by
          ext x
          simp
        rw [hconjOne, Subgroup.map_id] at hRQ
        exact hRQ
      simpa [hRQ']
    · intro hR
      have hRQ : R = Q := Set.mem_singleton_iff.mp hR
      simpa [hRQ] using hQmaxA
  letI : Group.IsNilpotent F := by
    dsimp [F]
    infer_instance
  have hsnAF : (A.subgroupOf F).IsSubnormal := by
    let H : Subgroup F := A.subgroupOf F
    change H.IsSubnormal
    refine (measure (fun L : Subgroup F =>
      Nat.card F - Nat.card L)).wf.induction H ?_
    intro L ih
    by_cases hLtop : L = ⊤
    · simpa [hLtop]
    let N : Subgroup F := Subgroup.normalizer (L : Set F)
    have hLN : L < N := by
      exact Group.normalizerCondition_of_isNilpotent L
        (lt_top_iff_ne_top.mpr hLtop)
    have hNcardLe : Nat.card N ≤ Nat.card F := by
      exact Nat.le_of_dvd Nat.card_pos N.card_subgroup_dvd_card
    have hcardLt : Nat.card L < Nat.card N :=
      natCard_subgroup_lt_of_lt hLN
    have hmeasure : Nat.card F - Nat.card N <
        Nat.card F - Nat.card L := by
      omega
    have hNsn : N.IsSubnormal := ih N hmeasure
    have hLnormalN : (L.subgroupOf N).Normal := by
      apply (Subgroup.normal_subgroupOf_iff_le_normalizer hLN.le).2
      exact le_rfl
    exact Subgroup.IsSubnormal.step L N hLN.le hNsn hLnormalN
  have hFpi : IsPiNumber pi (Nat.card F) := by
    have hsupport : pi = primeSupport (Nat.card F) := by
      simpa [A, F, pi] using
        (non_pcore_fitting_primeSupport_eq M A₀ hA₀F)
    rw [hsupport]
    exact IsPiNumber.primeSupport_self
  have hsuperset :=
    normed_trans_superset A F hcstrA hq hAF hsnAF hFpi htransA
  have hincFA :
      max_normed_pgroups (F : Set G) ({q} : Set ℕ) ⊆
        max_normed_pgroups (A : Set G) ({q} : Set ℕ) := by
    exact hsuperset.2.2.1
  obtain ⟨QF, hQFmax, _hbotQF⟩ :=
    max_normed_exists (F : Set G) ({q} : Set ℕ) (⊥ : Subgroup G)
      (by simpa using (IsPiNumber.one (pi := ({q} : Set ℕ))))
      (by exact Subgroup.le_normalizer_of_normal)
  have hQFeq : QF = Q := by
    have hQFA := hincFA hQFmax
    rw [huniqA] at hQFA
    exact Set.mem_singleton_iff.mp hQFA
  have hFnormQ : F ≤ Subgroup.normalizer (Q : Set G) := by
    have hnorm := (mem_max_normed hQFmax).2
    simpa [hQFeq] using hnorm
  have huniqF :
      max_normed_pgroups (F : Set G) ({q} : Set ℕ) = {Q} :=
    max_normed_uniq A F Q ({q} : Set ℕ) huniqA hAF hFnormQ
  have hQmaxF : Q ∈
      max_normed_pgroups (F : Set G) ({q} : Set ℕ) := by
    rw [huniqF]
    exact Set.mem_singleton Q
  have hMnormQ : M ≤ Subgroup.normalizer (Q : Set G) := by
    intro x hxM
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hxF : x ∈ Subgroup.normalizer (F : Set G) :=
      fittingWithin_le_normalizer M hxM
    have hQxMax : Q.map (MulAut.conj x).toMonoidHom ∈
        max_normed_pgroups (F : Set G) ({q} : Set ℕ) :=
      (norm_acts_max_norm F Q ({q} : Set ℕ) x hxF).2 hQmaxF
    rw [huniqF] at hQxMax
    exact Set.mem_singleton_iff.mp hQxMax
  have hQbot : Q = ⊥ := by
    by_contra hQne
    have hQdata := mem_max_normed hQmaxA
    letI : Fact q.Prime :=
      ⟨prime_of_isPiNumber_singleton_of_ne_bot hQdata.1 hQne⟩
    have hQp : IsPGroup q Q :=
      isPGroup_of_isPiNumber_singleton hQdata.1
    have hQproper : Q < ⊤ := mFT_pgroup_proper Q hQp
    have hnormQ : Subgroup.normalizer (Q : Set G) = M :=
      mmax_norm hM hQne hQproper hMnormQ
    have hQM : Q ≤ M := Subgroup.le_normalizer.trans_eq hnormQ
    have hQnormalM : (Q.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQM).2 hMnormQ
    have hQsubp : IsPGroup q (Q.subgroupOf M) :=
      hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQM).symm
    have hQsubFit : Q.subgroupOf M ≤ fittingCore M := by
      exact nilpotent_normal_le_fittingCore hQnormalM hQsubp.isNilpotent
    have hQF : Q ≤ F := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hQM]
      dsimp [F, fittingWithin]
      exact Subgroup.map_mono hQsubFit
    have hqQ : q ∣ Nat.card Q :=
      hQp.card_eq_or_dvd.resolve_left
        (fun hcard => hQne (Subgroup.card_eq_one.mp hcard))
    apply hq
    rw [non_pcore_fitting_primeSupport_eq M A₀ hA₀F]
    exact ⟨Fact.out, hqQ.trans (Subgroup.card_dvd_of_le hQF)⟩
  simpa [A, F, hQbot] using huniqA

end Submission.OddOrder.BG.Section08
