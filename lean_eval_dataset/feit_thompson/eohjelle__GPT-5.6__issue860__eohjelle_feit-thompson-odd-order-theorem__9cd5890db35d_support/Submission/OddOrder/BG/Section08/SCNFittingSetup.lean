import Submission.OddOrder.BG.Section08.SCNFittingReduction
import Submission.OddOrder.BG.Section08.SCNFittingPuigCenter
import Submission.OddOrder.BG.Section07.ThompsonTransitivity

/-!
# Bender--Glauberman Theorem 8.1(b): SCN--Fitting setup

This file ports the common local setup in the SCN branch of
Bender--Glauberman Theorem 8.1(b).  It identifies the Fitting subgroup with
the mapped `p`-core, places the SCN subgroup inside it, upgrades the chosen
Sylow subgroup to the ambient group, kills the `p'`-core of the full
centralizer, and records the resulting singleton maximal-normalized family.
-/

namespace Submission.OddOrder.BG.Section08

open Submission.OddOrder
open Submission.OddOrder.BG.Section01
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.MathlibSupport

universe u

private theorem scn_fitting_reduction_data
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    (p : ℕ) [Fact p.Prime] (M : Subgroup G) (P : Sylow p M)
    (A : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hFp : IsPGroup p (fittingWithin M))
    (hSCN : IsSCN ((P : Subgroup M).map M.subtype) A)
    (hRankA : 3 ≤ Group.rank A) :
    A ≠ ⊥ ∧
      pPrimeCore p M = ⊥ ∧
      fittingWithin M = (pCore p M).map M.subtype ∧
      fittingWithin M ≤ (P : Subgroup M).map M.subtype ∧
      A ≤ fittingWithin M := by
  classical
  have hAne : A ≠ ⊥ := by
    intro hAbot
    have hzero : Group.rank A = 0 := by
      rw [hAbot]
      exact Group.rank_eq_zero _
    omega
  have hsol : IsSolvable M := mmax_sol hM
  have hcore : pPrimeCore p M = ⊥ :=
    pPrimeCore_eq_bot_of_fittingWithin_isPGroup p M hsol hFp
  have hfit : fittingWithin M = (pCore p M).map M.subtype :=
    fittingWithin_eq_map_pCore_of_isPGroup p M hsol hFp
  have hFP :
      fittingWithin M ≤ (P : Subgroup M).map M.subtype :=
    fittingWithin_le_map_sylow_of_isPGroup p M P hsol hFp
  have hAM : A ≤ M :=
    hSCN.le_sylow.trans (Subgroup.map_subtype_le (P : Subgroup M))
  let AM : Subgroup M := A.subgroupOf M
  have hAMP : AM ≤ (P : Subgroup M) := by
    intro a ha
    change (a : G) ∈ A at ha
    have haP := hSCN.le_sylow ha
    have haPcomap : a ∈
        ((P : Subgroup M).map M.subtype).comap M.subtype := haP
    rw [Subgroup.comap_map_eq_self_of_injective
      M.subtype_injective] at haPcomap
    exact haPcomap
  letI : IsMulCommutative A := hSCN.commutative
  have hAMcomm : IsMulCommutative AM := by
    apply isMulCommutative_iff.mpr
    intro x y
    apply Subtype.ext
    apply Subtype.ext
    change (x : G) * (y : G) = (y : G) * (x : G)
    exact congrArg Subtype.val
      (mul_comm' (⟨x, x.property⟩ : A) (⟨y, y.property⟩ : A))
  have hPnormAM :
      (P : Subgroup M) ≤ Subgroup.normalizer (AM : Set M) := by
    have hsub :
        (P : Subgroup M) ≤
          (Subgroup.normalizer (A : Set G)).subgroupOf M := by
      intro x hx
      exact hSCN.le_normalizer
        (Subgroup.mem_map_of_mem M.subtype hx)
    rwa [Subgroup.subgroupOf_normalizer_eq hAM] at hsub
  have hAMnormal : (AM.subgroupOf (P : Subgroup M)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAMP).mpr hPnormAM
  letI : IsSolvable M := hsol
  have hAMcore : AM ≤ pCore p M := by
    have hconstrained :=
      (Submission.OddOrder.BG.Section06.odd_p_abelian_constrained
        (G := M) (p := p) (mFT_odd M)) P AM hAMcomm hAMP hAMnormal
    rwa [pPrimePCore_eq_pCore_of_pPrimeCore_eq_bot hcore] at hconstrained
  have hAF : A ≤ fittingWithin M := by
    rw [hfit, ← Subgroup.map_subgroupOf_eq_of_le hAM]
    exact Subgroup.map_mono hAMcore
  exact ⟨hAne, hcore, hfit, hFP, hAF⟩

/-- In the SCN branch, the SCN subgroup lies in the Fitting subgroup of the
chosen maximal subgroup. -/
theorem scn_fitting_le
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    (p : ℕ) [Fact p.Prime] (M : Subgroup G) (P : Sylow p M)
    (A : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hFp : IsPGroup p (fittingWithin M))
    (hSCN : IsSCN ((P : Subgroup M).map M.subtype) A)
    (hRankA : 3 ≤ Group.rank A) :
    A ≤ fittingWithin M :=
  (scn_fitting_reduction_data p M P A hM hFp hSCN hRankA).2.2.2.2

/-- The full ambient centralizer of the SCN subgroup lies in the chosen
maximal subgroup. -/
theorem scn_fitting_centralizer_le
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    (p : ℕ) [Fact p.Prime] (M : Subgroup G) (P : Sylow p M)
    (A : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hFp : IsPGroup p (fittingWithin M))
    (hSCN : IsSCN ((P : Subgroup M).map M.subtype) A)
    (hRankA : 3 ≤ Group.rank A) :
    Subgroup.centralizer (A : Set G) ≤ M := by
  classical
  let F : Subgroup G := fittingWithin M
  let Z : Subgroup G := centerWithin F
  have hdata := scn_fitting_reduction_data p M P A hM hFp hSCN hRankA
  have hAne : A ≠ ⊥ := hdata.1
  have hFP : F ≤ (P : Subgroup M).map M.subtype := hdata.2.2.2.1
  have hAF : A ≤ F := hdata.2.2.2.2
  have hZA : Z ≤ A := by
    have hZcentral : Z ≤ centralizerWithin F A :=
      centerWithin_le_centralizerWithin hAF
    have hZP : Z ≤ centralizerWithin
        ((P : Subgroup M).map M.subtype) A :=
      hZcentral.trans (centralizerWithin_mono_left hFP)
    exact hZP.trans_eq hSCN.centralizerWithin_eq
  have hZF : Z ≤ F := centralizerWithin_le_left F F
  have hZM : Z ≤ M := hZF.trans (fittingWithin_le M)
  have hMnormF : M ≤ Subgroup.normalizer (F : Set G) := by
    simpa only [F] using fittingWithin_le_normalizer M
  have hMnormZ : M ≤ Subgroup.normalizer (Z : Set G) := by
    rw [show Z = (Subgroup.center F).map F.subtype from
      (map_center_eq_centerWithin F).symm,
      Subgroup.le_normalizer_iff]
    exact characteristic_map_subtype_invariant_under_normalizer
      F M (Subgroup.center F) hMnormF
  have hZnormalM : (Z.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZM).mpr hMnormZ
  have hFne : F ≠ ⊥ := fun hFbot => hAne (le_bot_iff.mp (hAF.trans_eq hFbot))
  letI : Nontrivial F := F.nontrivial_iff_ne_bot.mpr hFne
  have hZne : Z ≠ ⊥ := by
    simpa only [Z] using centerWithin_ne_bot F hFp
  have hnormZ : Subgroup.normalizer (Z : Set G) = M :=
    mmax_normal hM hZM hZnormalM hZne
  exact (Subgroup.centralizer_le hZA).trans
    ((Subgroup.centralizer_le_normalizer (Z : Set G)).trans_eq hnormZ)

/-- The chosen Sylow subgroup of the maximal subgroup is already an ambient
Sylow subgroup. -/
theorem scn_fitting_exists_ambient_sylow
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    (p : ℕ) [Fact p.Prime] (M : Subgroup G) (P : Sylow p M)
    (A : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hFp : IsPGroup p (fittingWithin M))
    (hSCN : IsSCN ((P : Subgroup M).map M.subtype) A)
    (hRankA : 3 ≤ Group.rank A) :
    ∃ Q : Sylow p G,
      (Q : Subgroup G) = (P : Subgroup M).map M.subtype := by
  have hdata := scn_fitting_reduction_data p M P A hM hFp hSCN hRankA
  exact exists_ambient_sylow_eq_map_of_pPrimeCore_eq_bot
    p M P hM hdata.2.1 hSCN.le_sylow hdata.1

/-- The `p'`-core of the full centralizer of the SCN subgroup is trivial. -/
theorem scn_fitting_central_pPrimeCore_eq_bot
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    (p : ℕ) [Fact p.Prime] (M : Subgroup G) (P : Sylow p M)
    (A : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hFp : IsPGroup p (fittingWithin M))
    (hSCN : IsSCN ((P : Subgroup M).map M.subtype) A)
    (hRankA : 3 ≤ Group.rank A) :
    (pPrimeCore p (Subgroup.centralizer (A : Set G))).map
      (Subgroup.centralizer (A : Set G)).subtype = ⊥ := by
  let C : Subgroup G := Subgroup.centralizer (A : Set G)
  have hdata := scn_fitting_reduction_data p M P A hM hFp hSCN hRankA
  have hAM : A ≤ M := hdata.2.2.2.2.trans (fittingWithin_le M)
  have hAp : IsPGroup p A :=
    IsPGroup.to_le (P.isPGroup'.map M.subtype) hSCN.le_sylow
  have hCM : C ≤ M := by
    simpa only [C] using
      scn_fitting_centralizer_le p M P A hM hFp hSCN hRankA
  have hwithin : centralizerWithin M A = C := by
    exact inf_eq_right.mpr hCM
  have hcore := map_pPrimeCore_centralizerWithin_le_map_pPrimeCore
    (p := p) (X := M) (R := A) hAM hAp (mmax_sol hM)
  rw [hwithin, hdata.2.1] at hcore
  have hcore' : (pPrimeCore p C).map C.subtype ≤ ⊥ := by
    simpa only [Subgroup.map_bot] using hcore
  exact le_bot_iff.mp hcore'

private theorem singleton_max_normed_of_trivial_transporter
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (q : ℕ)
    (htrans : ∀ Q₁ Q₂ : Subgroup G,
      Q₁ ∈ max_normed_pgroups (A : Set G) ({q} : Set ℕ) →
      Q₂ ∈ max_normed_pgroups (A : Set G) ({q} : Set ℕ) →
      ∃ k : G, k ∈ (⊥ : Subgroup G) ∧
        Q₂ = Q₁.map (MulAut.conj k⁻¹).toMonoidHom) :
    ∃ Q : Subgroup G,
      max_normed_pgroups (A : Set G) ({q} : Set ℕ) = {Q} := by
  classical
  obtain ⟨Q, hQmax, -⟩ :=
    max_normed_exists (A : Set G) ({q} : Set ℕ) (⊥ : Subgroup G)
      (by simpa using (IsPiNumber.one (pi := ({q} : Set ℕ))))
      (by exact Subgroup.le_normalizer_of_normal)
  refine ⟨Q, ?_⟩
  ext R
  constructor
  · intro hR
    obtain ⟨k, hk, hRQ⟩ := htrans Q R hQmax hR
    have hkOne : k = 1 := Subgroup.mem_bot.mp hk
    subst k
    have hconjOne :
        (MulAut.conj (1 : G)⁻¹).toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    rw [hconjOne, Subgroup.map_id] at hRQ
    exact Set.mem_singleton_iff.mpr hRQ
  · intro hR
    have hRQ : R = Q := Set.mem_singleton_iff.mp hR
    simpa [hRQ] using hQmax

/-- For every prime different from `p`, the trivial subgroup is the unique
maximal subgroup normalized by the SCN subgroup. -/
theorem scn_fitting_max_normed_eq_bot
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    (p : ℕ) [Fact p.Prime] (M : Subgroup G) (P : Sylow p M)
    (A : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hFp : IsPGroup p (fittingWithin M))
    (hSCN : IsSCN ((P : Subgroup M).map M.subtype) A)
    (hRankA : 3 ≤ Group.rank A)
    (q : ℕ) (hq : q ≠ p) :
    max_normed_pgroups (A : Set G) ({q} : Set ℕ) = {⊥} := by
  classical
  let F : Subgroup G := fittingWithin M
  obtain ⟨Qp, hQp⟩ :=
    scn_fitting_exists_ambient_sylow p M P A hM hFp hSCN hRankA
  have hSCNG : IsSCN (Qp : Subgroup G) A := by
    simpa only [hQp] using hSCN
  have hAat : A ∈ minSimple_SCN_at (G := G) 3 p :=
    ⟨Qp, hSCNG, hRankA⟩
  have hcore :
      (pPrimeCore p (Subgroup.centralizer (A : Set G))).map
        (Subgroup.centralizer (A : Set G)).subtype = ⊥ :=
    scn_fitting_central_pPrimeCore_eq_bot
      p M P A hM hFp hSCN hRankA
  have htrans : ∀ Q₁ Q₂ : Subgroup G,
      Q₁ ∈ max_normed_pgroups (A : Set G) ({q} : Set ℕ) →
      Q₂ ∈ max_normed_pgroups (A : Set G) ({q} : Set ℕ) →
      ∃ k : G, k ∈ (⊥ : Subgroup G) ∧
        Q₂ = Q₁.map (MulAut.conj k⁻¹).toMonoidHom := by
    simpa only [hcore] using
      (Thompson_transitivity p q A hAat hq)
  obtain ⟨Q, huniqA⟩ :=
    singleton_max_normed_of_trivial_transporter A q htrans
  have hQmaxA : Q ∈
      max_normed_pgroups (A : Set G) ({q} : Set ℕ) := by
    rw [huniqA]
    exact Set.mem_singleton Q
  have hAF : A ≤ F := by
    simpa only [F] using scn_fitting_le p M P A hM hFp hSCN hRankA
  have hFnormalizesA : F ≤ Subgroup.normalizer (A : Set G) := by
    exact (scn_fitting_reduction_data
      p M P A hM hFp hSCN hRankA).2.2.2.1.trans hSCN.le_normalizer
  have hFnormQ : F ≤ Subgroup.normalizer (Q : Set G) := by
    intro x hxF
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hQxMax : Q.map (MulAut.conj x).toMonoidHom ∈
        max_normed_pgroups (A : Set G) ({q} : Set ℕ) :=
      (norm_acts_max_norm A Q ({q} : Set ℕ) x
        (hFnormalizesA hxF)).2 hQmaxA
    rw [huniqA] at hQxMax
    exact Set.mem_singleton_iff.mp hQxMax
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
    have hQq : IsPGroup q Q :=
      isPGroup_of_isPiNumber_singleton hQdata.1
    have hQproper : Q < ⊤ := mFT_pgroup_proper Q hQq
    have hnormQ : Subgroup.normalizer (Q : Set G) = M :=
      mmax_norm hM hQne hQproper hMnormQ
    have hQM : Q ≤ M := Subgroup.le_normalizer.trans_eq hnormQ
    have hQnormalM : (Q.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQM).mpr hMnormQ
    have hQsubq : IsPGroup q (Q.subgroupOf M) :=
      hQq.of_equiv (Subgroup.subgroupOfEquivOfLe hQM).symm
    have hQsubCore : Q.subgroupOf M ≤ pCore q M :=
      le_pCore hQsubq hQnormalM
    have hQsubPrime : Q.subgroupOf M ≤ pPrimeCore p M :=
      hQsubCore.trans
        (pCore_le_pPrimeCore_of_ne (G := M) (p := p) (q := q) hq.symm)
    have hQsubBot : Q.subgroupOf M = ⊥ := by
      apply le_bot_iff.mp
      exact hQsubPrime.trans_eq
        (scn_fitting_reduction_data
          p M P A hM hFp hSCN hRankA).2.1
    apply hQne
    rw [← Subgroup.map_subgroupOf_eq_of_le hQM, hQsubBot]
    simp
  simpa [hQbot] using huniqA

private theorem map_pCore_eq_bot_of_isPPrimeSubgroup
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (X : Subgroup G)
    (hXp : IsPPrimeSubgroup p X) :
    (pCore p X).map X.subtype = ⊥ := by
  have hcoreCard : Nat.card (pCore p X) = 1 := by
    rcases (pCore_isPGroup (G := X) (p := p)).card_eq_or_dvd with h | h
    · exact h
    · have hpNot : ¬ p ∣ Nat.card X :=
        (Fact.out : p.Prime).coprime_iff_not_dvd.mp hXp
      exact (hpNot (h.trans (pCore p X).card_subgroup_dvd_card)).elim
  have hcoreBot : pCore p X = ⊥ := Subgroup.card_eq_one.mp hcoreCard
  simp [hcoreBot]

/-- A proper `p'`-subgroup normalized by `A` is trivial once all the
maximal normalized singleton families away from `p` are trivial. -/
theorem eq_bot_of_isPPrimeSubgroup_of_normalized_of_maxNormed
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    (p : ℕ) [Fact p.Prime] (A : Subgroup G)
    (hmax : ∀ q, q ≠ p →
      max_normed_pgroups (A : Set G) ({q} : Set ℕ) = {⊥})
    {X : Subgroup G} (hXproper : X < ⊤)
    (hXp : IsPPrimeSubgroup p X)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) :
    X = ⊥ := by
  classical
  apply eq_bot_of_fittingWithin_eq_bot_of_isSolvable X (mFT_sol hXproper)
  rw [fittingWithin, fittingCore, Subgroup.map_iSup]
  apply le_bot_iff.mp
  apply iSup_le
  intro q
  letI : Fact (q : ℕ).Prime := ⟨q.property⟩
  by_cases hqp : (q : ℕ) = p
  · simpa only [hqp] using
      (map_pCore_eq_bot_of_isPPrimeSubgroup p X hXp).le
  · let R : Subgroup G := (pCore (q : ℕ) X).map X.subtype
    have hRpi : IsPiNumber ({(q : ℕ)} : Set ℕ) (Nat.card R) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp
        ((pCore_isPGroup (G := X) (p := (q : ℕ))).map X.subtype)
      rw [hn]
      intro r hr hrdvd
      have hrq : r = (q : ℕ) :=
        Nat.prime_eq_prime_of_dvd_pow hr q.property hrdvd
      simp [hrq]
    have hAnormR : A ≤ Subgroup.normalizer (R : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      exact characteristic_map_subtype_invariant_under_normalizer
        X A (pCore (q : ℕ) X) hAX
    obtain ⟨Q, hQmax, hRQ⟩ :=
      max_normed_exists (A : Set G) ({(q : ℕ)} : Set ℕ) R
        hRpi hAnormR
    have hQbot : Q = ⊥ := by
      rw [hmax (q : ℕ) hqp] at hQmax
      exact Set.mem_singleton_iff.mp hQmax
    exact (le_bot_iff.mp (hRQ.trans_eq hQbot)).le

end Submission.OddOrder.BG.Section08
