import Submission.OddOrder.BG.Section10.SigmaComplementRank

/-!
# Bender--Glauberman Lemma 10.5, part 1

This file ports `BGsection10.v: sigma'_norm_mmax_rank2`.  If a `p`-subgroup
has its full ambient normalizer contained in the maximal subgroup `M`, then
`M` has `p`-rank exactly two.
-/

namespace Submission.OddOrder.BG.Section10

open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.MathlibSupport

universe u

private theorem subgroup_characteristic_of_isCyclic
    {C : Type*} [Group C] [IsCyclic C] (H : Subgroup C) :
    H.Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro e
  obtain ⟨m, hm⟩ := e.toMonoidHom.map_cyclic
  rintro _ ⟨x, hx, rfl⟩
  rw [hm]
  exact H.zpow_mem hx m

/-- `BGsection10.v: sigma'_norm_mmax_rank2`, Lemma 10.5, part 1.

The source states the conclusion as the numerical equality
`'r_p(M) = 2`; here it is expanded into elementary-abelian rank at least
two and not at least three. -/
theorem sigma_compl_normalizer_max_rank_two
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    {p : ℕ} [Fact p.Prime]
    (hpSigma : p ∉ sigmaPrimes M)
    {X : Subgroup G} (hXp : IsPGroup p X)
    (hNXM : Subgroup.normalizer (X : Set G) ≤ M) :
    HasElementaryAbelianPRankTwo p M := by
  have hXM : X ≤ M := Subgroup.le_normalizer.trans hNXM
  let XM : Subgroup M := X.subgroupOf M
  let eXM : XM ≃* X := Subgroup.subgroupOfEquivOfLe hXM
  have hXMp : IsPGroup p XM := hXp.of_equiv eXM.symm
  obtain ⟨P, hXMP⟩ := hXMp.exists_le_sylow
  let PG : Subgroup G := ambientSylow M P
  have hXPG : X ≤ PG := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hXM]
    exact Subgroup.map_mono hXMP
  have hPGM : PG ≤ M := by
    simpa [PG, ambientSylow] using
      (Subgroup.map_subtype_le (P : Subgroup M))
  have hPGp : IsPGroup p PG := P.isPGroup'.map M.subtype
  have hRankTwo : HasElementaryAbelianRankAtLeast p 2 M := by
    by_contra hnoRankTwo
    have hNoRankTwoPG :
        ¬ ∃ E : Subgroup PG, IsElementaryAbelianOfRank p 2 E := by
      rintro ⟨E, hE⟩
      let EG : Subgroup G := E.map PG.subtype
      have hEGPG : EG ≤ PG := Subgroup.map_subtype_le E
      have hEG : IsElementaryAbelianOfRank p 2 EG := by
        dsimp only [EG]
        exact hE.map_of_injective PG.subtype PG.subtype_injective
      exact hnoRankTwo ⟨EG, hEGPG.trans hPGM, hEG⟩
    have hPGcyclic : IsCyclic PG :=
      (odd_pgroup_isCyclic_iff_no_elementaryAbelian_rank_two
        hPGp (mFT_odd PG)).mpr hNoRankTwoPG
    letI : IsCyclic PG := hPGcyclic
    let R : Subgroup PG := X.subgroupOf PG
    letI : R.Characteristic := subgroup_characteristic_of_isCyclic R
    have hNormPGX :
        Subgroup.normalizer (PG : Set G) ≤
          Subgroup.normalizer (X : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro g hg x hx
      have hxR : x ∈ R.map PG.subtype := by
        simpa [R, Subgroup.map_subgroupOf_eq_of_le hXPG] using hx
      have hconj :=
        characteristic_map_subtype_invariant_under_normalizer
          PG (Subgroup.normalizer (PG : Set G)) R le_rfl
            g hg x hxR
      simpa [R, Subgroup.map_subgroupOf_eq_of_le hXPG] using hconj
    exact hpSigma ⟨Fact.out, P, by simpa [PG] using hNormPGX.trans hNXM⟩
  refine ⟨hRankTwo, ?_⟩
  intro hRankThree
  exact hpSigma (alpha_sub_sigma hM ⟨Fact.out, hRankThree⟩)

/-- Source-name alias for Lemma 10.5, part 1. -/
theorem sigma'_norm_mmax_rank2
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    {p : ℕ} [Fact p.Prime]
    (hpSigma : p ∉ sigmaPrimes M)
    {X : Subgroup G} (hXp : IsPGroup p X)
    (hNXM : Subgroup.normalizer (X : Set G) ≤ M) :
    HasElementaryAbelianPRankTwo p M :=
  sigma_compl_normalizer_max_rank_two hM hpSigma hXp hNXM

end Submission.OddOrder.BG.Section10
