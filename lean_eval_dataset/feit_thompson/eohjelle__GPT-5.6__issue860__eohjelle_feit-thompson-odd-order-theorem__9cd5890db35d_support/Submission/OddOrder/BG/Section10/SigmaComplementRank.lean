import Submission.OddOrder.BG.Section04.OddZGroupRankOne
import Submission.OddOrder.BG.Section07.SCNRankTwoSubgroup
import Submission.OddOrder.BG.Section10.AlphaComplementCentralizerUniqueness
import Submission.OddOrder.BG.Section10.AlphaSigmaCore
import Submission.OddOrder.MathlibSupport.CharacteristicUnderNormalizer
import Submission.OddOrder.MathlibSupport.Critical

/-!
# Bender--Glauberman Lemma 10.4

This file ports the four assertions in `BGsection10.v`, lines 513--581.
The numerical condition that the `p`-rank of a subgroup is exactly two is
expanded into the existence of a rank-two elementary-abelian subgroup and
the nonexistence of one of rank three, following the convention used in the
preceding sections.
-/

namespace Submission.OddOrder.BG.Section10

open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section05
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.MathlibSupport

universe u

/-- The proposition-valued form of MathComp's numerical equality
`'r_p(H) = 2`. -/
def HasElementaryAbelianPRankTwo
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) (H : Subgroup G) : Prop :=
  HasElementaryAbelianRankAtLeast p 2 H ∧
    ¬ HasElementaryAbelianRankAtLeast p 3 H

private theorem isNarrow_subgroup_iff_top
    {G : Type u} [Group G] {p : ℕ} [Fact p.Prime]
    (A : Subgroup G) :
    IsNarrow p A ↔ IsNarrow p (⊤ : Subgroup A) := by
  have hiff := isNarrow_map_iff_of_injective
    (p := p) A.subtype A.subtype_injective (⊤ : Subgroup A)
  have hmapTop :
      (⊤ : Subgroup A).map A.subtype = A := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [hmapTop] at hiff
  exact hiff

private theorem isNarrow_top_mapSylow_iff
    {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    {p : ℕ} [Fact p.Prime] (e : A ≃* B) (P : Sylow p A) :
    IsNarrow p (⊤ : Subgroup (P.mapSurjective
      (f := e.toMonoidHom) e.surjective)) ↔
      IsNarrow p (⊤ : Subgroup P) := by
  let Q : Sylow p B := P.mapSurjective
    (f := e.toMonoidHom) e.surjective
  let eP₀ : P ≃* ((P : Subgroup A).map e.toMonoidHom) :=
    e.subgroupMap (P : Subgroup A)
  let eP : P ≃* Q :=
    eP₀.trans (MulEquiv.subgroupCongr (by rfl))
  have hiff :=
    isNarrow_map_mulEquiv_iff (p := p) eP (⊤ : Subgroup P)
  rw [Subgroup.map_top_of_surjective eP.toMonoidHom eP.surjective] at hiff
  simpa [Q] using hiff

private theorem centralizerWithin_map_equiv
    {G : Type u} [Group G]
    {D S : Subgroup G} (e : G ≃* G)
    (hD : D.map e.toMonoidHom = D) :
    (centralizerWithin D S).map e.toMonoidHom =
      centralizerWithin D (S.map e.toMonoidHom) := by
  ext y
  rw [Subgroup.mem_map_equiv]
  constructor
  · intro hy
    refine ⟨?_, ?_⟩
    · have hyMap : y ∈ D.map e.toMonoidHom :=
        Subgroup.mem_map_equiv.mpr hy.1
      rwa [hD] at hyMap
    · intro z hz
      have hz' : e.symm z ∈ S := Subgroup.mem_map_equiv.mp hz
      have hcomm := hy.2 (e.symm z) hz'
      simpa using congrArg e hcomm
  · intro hy
    refine ⟨?_, ?_⟩
    · have hyMap : y ∈ D.map e.toMonoidHom := by
        rw [hD]
        exact hy.1
      exact Subgroup.mem_map_equiv.mp hyMap
    · intro z hz
      have hzMap : e z ∈ S.map e.toMonoidHom :=
        (Subgroup.mem_map_iff_mem e.injective).mpr hz
      have hcomm := hy.2 (e z) hzMap
      simpa using congrArg e.symm hcomm

private theorem sigmaCore_subgroupOf_le_commutator
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    (sigmaCore M).subgroupOf M ≤ _root_.commutator M := by
  have hmap :
      ((sigmaCore M).subgroupOf M).map M.subtype ≤
        (_root_.commutator M).map M.subtype := by
    rw [Subgroup.map_subgroupOf_eq_of_le (sigmaCore_le M)]
    exact Msigma_der1 hM
  exact (Subgroup.map_le_map_iff_of_injective
    M.subtype_injective).mp hmap

/-- `BGsection10.v: der1_quo_sigma'`, Lemma 10.4(a).

Every prime divisor of the abelianization of `M` is outside `sigma(M)`.
No primality hypothesis is needed in the statement: membership in
`sigma(M)` supplies it in the contradictory branch. -/
theorem der1_quo_sigma_compl
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    {p : ℕ}
    (hpAb : p ∣ Nat.card (M ⧸ _root_.commutator M)) :
    p ∉ sigmaPrimes M := by
  intro hpSigma
  let S : Subgroup M := (sigmaCore M).subgroupOf M
  have hSD : S ≤ _root_.commutator M := by
    simpa [S] using sigmaCore_subgroupOf_le_commutator hM
  have hpD : p ∣ (_root_.commutator M).index := by
    simpa only [Subgroup.index_eq_card] using hpAb
  have hpS : p ∣ S.index :=
    hpD.trans (Subgroup.index_dvd_of_le hSD)
  exact (Msigma_Hall hM).isPiNumber_index hpSigma.1 hpS hpSigma

/-- Source-name alias for Lemma 10.4(a). -/
theorem der1_quo_sigma'
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    {p : ℕ}
    (hpAb : p ∣ Nat.card (M ⧸ _root_.commutator M)) :
    p ∉ sigmaPrimes M :=
  der1_quo_sigma_compl hM hpAb

private theorem omegaOneCenterAmbient_ne_bot_of_sylow_ne_bot
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (P : Sylow p M) (hPne : (P : Subgroup M) ≠ ⊥) :
    omegaOneCenterAmbient p (ambientSylow M P) ≠ ⊥ := by
  let PG : Subgroup G := ambientSylow M P
  have hPGp : IsPGroup p PG := P.isPGroup'.map M.subtype
  have hPGne : PG ≠ ⊥ := by
    intro hPGbot
    apply hPne
    exact (Subgroup.map_eq_bot_iff_of_injective
      (P : Subgroup M) M.subtype_injective).mp hPGbot
  letI : Nontrivial PG :=
    (PG : Subgroup G).nontrivial_iff_ne_bot.mpr hPGne
  letI : Group.IsNilpotent PG := hPGp.isNilpotent
  let Z : Subgroup PG := Subgroup.center PG
  have hZne : Z ≠ ⊥ := by
    dsimp [Z]
    exact Group.IsNilpotent.center_ne_bot PG
  have hZp : IsPGroup p Z := hPGp.to_subgroup Z
  have hZcard : Nat.card Z ≠ 1 :=
    (Z.one_lt_card_iff_ne_bot.mpr hZne).ne'
  have hOmegaNe : omegaOne p Z ≠ ⊥ :=
    omegaOne_ne_bot_of_isPGroup hZp hZcard
  have hCenterOmegaNe :
      Submission.OddOrder.BG.Section05.omegaOneCenter p PG ≠ ⊥ := by
    dsimp [Submission.OddOrder.BG.Section05.omegaOneCenter, Z] at hOmegaNe ⊢
    exact (not_congr (Subgroup.map_eq_bot_iff_of_injective
      (omegaOne p (Subgroup.center PG))
      (Subgroup.center PG).subtype_injective)).mpr hOmegaNe
  dsimp [omegaOneCenterAmbient]
  exact (not_congr (Subgroup.map_eq_bot_iff_of_injective
    (Submission.OddOrder.BG.Section05.omegaOneCenter p PG)
    PG.subtype_injective)).mpr hCenterOmegaNe

/-- `BGsection10.v: cent1_sigma'_Zgroup`, Lemma 10.4(b).

For a nontrivial Sylow subgroup at a prime outside `sigma(M)`, one can
choose a nonidentity element in `Omega_1(Z(P))` whose full centralizer has
another maximal overgroup; its centralizer inside the alpha core is a
Z-group. -/
theorem cent1_sigma_compl_Zgroup
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    {p : ℕ} [Fact p.Prime]
    (hpSigma : p ∉ sigmaPrimes M)
    (P : Sylow p M) (hPne : (P : Subgroup M) ≠ ⊥) :
    ∃ x : G,
      x ∈ omegaOneCenterAmbient p (ambientSylow M P) ∧
      x ≠ 1 ∧
      minSimple_max_groups_of (G := G)
          (centralizerWithin (⊤ : Subgroup G)
            (Subgroup.zpowers x) : Set G) ≠ {M} ∧
      IsZGroup
        (centralizerWithin (alphaCore M) (Subgroup.zpowers x)) := by
  classical
  let PG : Subgroup G := ambientSylow M P
  let T : Subgroup G := omegaOneCenterAmbient p PG
  have hPGp : IsPGroup p PG := P.isPGroup'.map M.subtype
  have hPGM : PG ≤ M := by
    dsimp [PG, ambientSylow]
    exact Subgroup.map_subtype_le _
  have hTne : T ≠ ⊥ := by
    simpa [T, PG] using
      omegaOneCenterAmbient_ne_bot_of_sylow_ne_bot P hPne
  by_cases hex : ∃ x : G,
      x ∈ T ∧ x ≠ 1 ∧
      minSimple_max_groups_of (G := G)
          (centralizerWithin (⊤ : Subgroup G)
            (Subgroup.zpowers x) : Set G) ≠ {M}
  · obtain ⟨x, hxT, hxne, hxNotUnique⟩ := hex
    refine ⟨x, by simpa [T, PG] using hxT, hxne, hxNotUnique, ?_⟩
    have hTPG : T ≤ PG := by
      simpa [T, PG] using
        (omegaOneCenterAmbient_le_centerWithin p PG).trans
          (centralizerWithin_le_left PG PG)
    have hxPG : x ∈ PG := hTPG hxT
    have hxM : x ∈ M := hPGM hxPG
    let X : Subgroup G := Subgroup.zpowers x
    have hXM : X ≤ M := Subgroup.zpowers_le.mpr hxM
    have hXPG : X ≤ PG := Subgroup.zpowers_le.mpr hxPG
    have hXp : IsPGroup p X := hPGp.to_le hXPG
    have hpAlpha : p ∉ alphaPrimes M := by
      intro hp
      exact hpSigma (alpha_sub_sigma hM hp)
    have hXalphaCompl :
        IsPiNumber (alphaPrimes M)ᶜ (Nat.card X) :=
      hXp.isPiNumber_natCard hpAlpha
    let C : Subgroup G := centralizerWithin (alphaCore M) X
    have hCodd : Odd (Nat.card C) := mFT_odd C
    apply (odd_isZGroup_iff_sylow_no_elementaryAbelian_rank_two
      hCodd).mpr
    intro q hq Q
    rintro ⟨E, hE⟩
    let E₁ : Subgroup C := E.map (Q : Subgroup C).subtype
    let E₂ : Subgroup G := E₁.map C.subtype
    have hE₁ : IsElementaryAbelianOfRank q 2 E₁ := by
      dsimp [E₁]
      exact hE.map_of_injective (Q : Subgroup C).subtype
        (Q : Subgroup C).subtype_injective
    have hE₂ : IsElementaryAbelianOfRank q 2 E₂ := by
      dsimp [E₂]
      exact hE₁.map_of_injective C.subtype C.subtype_injective
    have hRankC : HasElementaryAbelianRankAtLeast q 2 C :=
      ⟨E₂, Subgroup.map_subtype_le E₁, hE₂⟩
    have hCUuniq := cent_alpha'_uniq hM hXM hXalphaCompl
      ⟨q, hq, by simpa [C] using hRankC⟩
    let CU : Subgroup G := centralizerWithin M X
    let CG : Subgroup G := centralizerWithin (⊤ : Subgroup G) X
    have hCUCG : CU ≤ CG := by
      dsimp [CU, CG]
      exact centralizerWithin_mono_left le_top
    have hXne : X ≠ ⊥ := by
      intro hXbot
      apply hxne
      exact Subgroup.mem_bot.mp (hXbot ▸ Subgroup.mem_zpowers x)
    have hCGproper : CG < ⊤ := by
      simpa [CG, centralizerWithin] using mFT_cent_proper X hXne
    have hCUfamily :
        minSimple_max_groups_of (G := G) (CU : Set G) = {M} := by
      apply def_uniq_mmax
      · simpa [CU] using hCUuniq
      · exact hM
      · dsimp [CU]
        exact centralizerWithin_le_left M X
    have hCGfamily :
        minSimple_max_groups_of (G := G) (CG : Set G) = {M} :=
      def_uniq_mmaxS hCUCG hCGproper hCUfamily
    apply hxNotUnique
    simpa [CG, X] using hCGfamily
  · have hUnique : ∀ x : G, x ∈ T → x ≠ 1 →
        minSimple_max_groups_of (G := G)
          (centralizerWithin (⊤ : Subgroup G)
            (Subgroup.zpowers x) : Set G) = {M} := by
      intro x hxT hxne
      by_contra hne
      exact hex ⟨x, hxT, hxne, hne⟩
    obtain ⟨yT, hyTne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hTne
    let y : G := yT
    have hyT : y ∈ T := yT.property
    have hyne : y ≠ 1 := by
      intro hy
      apply hyTne
      apply Subtype.ext
      exact hy
    have hnorm : Subgroup.normalizer (PG : Set G) ≤ M := by
      intro g hg
      let R : Subgroup PG :=
        Submission.OddOrder.BG.Section05.omegaOneCenter p PG
      let yg : G := g * y * g⁻¹
      haveI : R.Characteristic := by
        dsimp [R]
        infer_instance
      have hygT : yg ∈ T := by
        change yg ∈ R.map PG.subtype
        change y ∈ R.map PG.subtype at hyT
        exact characteristic_map_subtype_invariant_under_normalizer
          PG (Subgroup.normalizer (PG : Set G)) R le_rfl
            g hg y hyT
      have hygne : yg ≠ 1 := by
        intro hyg
        let e : G ≃* G := MulAut.conj g
        apply hyne
        apply e.injective
        simpa [e, yg, MulAut.conj_apply] using hyg
      let e : G ≃* G := MulAut.conj g
      have hCmap :
          (centralizerWithin (⊤ : Subgroup G)
              (Subgroup.zpowers y)).map e.toMonoidHom =
            centralizerWithin (⊤ : Subgroup G)
              (Subgroup.zpowers yg) := by
        have h := centralizerWithin_map_equiv
          (D := (⊤ : Subgroup G)) (S := Subgroup.zpowers y)
          e (by simp)
        simpa [e, yg, MonoidHom.map_zpowers, MulAut.conj_apply] using h
      have htransport := def_uniq_mmaxJ e (hUnique y hyT hyne)
      rw [hCmap, hUnique yg hygT hygne] at htransport
      have hMmap : M.map e.toMonoidHom = M :=
        (Set.singleton_injective htransport).symm
      have hgNormM : g ∈ Subgroup.normalizer (M : Set G) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr hMmap
      rwa [norm_mmax hM] at hgNormM
    exact (hpSigma ⟨Fact.out, P, by simpa [PG] using hnorm⟩).elim

/-- Source-name alias for Lemma 10.4(b). -/
theorem cent1_sigma'_Zgroup
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    {p : ℕ} [Fact p.Prime]
    (hpSigma : p ∉ sigmaPrimes M)
    (P : Sylow p M) (hPne : (P : Subgroup M) ≠ ⊥) :
    ∃ x : G,
      x ∈ omegaOneCenterAmbient p (ambientSylow M P) ∧
      x ≠ 1 ∧
      minSimple_max_groups_of (G := G)
          (centralizerWithin (⊤ : Subgroup G)
            (Subgroup.zpowers x) : Set G) ≠ {M} ∧
      IsZGroup
        (centralizerWithin (alphaCore M) (Subgroup.zpowers x)) :=
  cent1_sigma_compl_Zgroup hM hpSigma P hPne

/-- `BGsection10.v: sigma'_rank2_max`, Lemma 10.4(c), part 1. -/
theorem sigma_compl_rank2_max
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    {p : ℕ} [Fact p.Prime]
    (hpSigma : p ∉ sigmaPrimes M)
    (_hRank : HasElementaryAbelianPRankTwo p M)
    {A : Subgroup G} (hAM : A ≤ M)
    (hA : IsElementaryAbelianOfRank p 2 A) :
    IsPMaxElem p (⊤ : Subgroup G) A := by
  by_contra hnotMax
  have hAuniq : A ∈ minSimple_uniq_max_groups (G := G) :=
    Submission.OddOrder.BG.Section09.nonmaxElem2_Uniqueness hA hnotMax
  have hAfamily :
      minSimple_max_groups_of (G := G) (A : Set G) = {M} :=
    def_uniq_mmax hAuniq hM hAM
  let AM : Subgroup M := A.subgroupOf M
  let eAM : AM ≃* A := Subgroup.subgroupOfEquivOfLe hAM
  have hAMp : IsPGroup p AM := hA.isPGroup.of_equiv eAM.symm
  obtain ⟨P, hAMP⟩ := hAMp.exists_le_sylow
  let PG : Subgroup G := ambientSylow M P
  have hAPG : A ≤ PG := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hAM]
    exact Subgroup.map_mono hAMP
  have hPGp : IsPGroup p PG := P.isPGroup'.map M.subtype
  have hPGproper : PG < ⊤ := mFT_pgroup_proper PG hPGp
  have hPGfamily :
      minSimple_max_groups_of (G := G) (PG : Set G) = {M} :=
    def_uniq_mmaxS hAPG hPGproper hAfamily
  have hnorm : Subgroup.normalizer (PG : Set G) ≤ M :=
    uniq_mmax_norm_sub hPGfamily
  exact hpSigma ⟨Fact.out, P, by simpa [PG] using hnorm⟩

/-- Source-name alias for Lemma 10.4(c), part 1. -/
theorem sigma'_rank2_max
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    {p : ℕ} [Fact p.Prime]
    (hpSigma : p ∉ sigmaPrimes M)
    (hRank : HasElementaryAbelianPRankTwo p M)
    {A : Subgroup G} (hAM : A ≤ M)
    (hA : IsElementaryAbelianOfRank p 2 A) :
    IsPMaxElem p (⊤ : Subgroup G) A :=
  sigma_compl_rank2_max hM hpSigma hRank hAM hA

/-- `BGsection10.v: sigma'_rank2_beta'`, Lemma 10.4(c), part 2. -/
theorem sigma_compl_rank2_beta_compl
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    {p : ℕ} [Fact p.Prime]
    (hpSigma : p ∉ sigmaPrimes M)
    (hRank : HasElementaryAbelianPRankTwo p M) :
    p ∉ betaPrimes (⊤ : Subgroup G) := by
  intro hpBeta
  obtain ⟨A, hAM, hA⟩ := hRank.1
  have hAmax : IsPMaxElem p (⊤ : Subgroup G) A :=
    sigma_compl_rank2_max hM hpSigma hRank hAM hA
  obtain ⟨Q, hAQ⟩ := hA.isPGroup.exists_le_sylow
  have hQnarrow : IsNarrow p (Q : Subgroup G) := by
    intro _hRankThree
    exact ⟨A, hA, hAmax.of_le le_top hAQ⟩
  have hQtop : IsNarrow p (⊤ : Subgroup Q) :=
    (isNarrow_subgroup_iff_top (Q : Subgroup G)).mp hQnarrow
  let e : G ≃* (⊤ : Subgroup G) := Subgroup.topEquiv.symm
  let R : Sylow p (⊤ : Subgroup G) :=
    Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hRtop : IsNarrow p (⊤ : Subgroup R) := by
    exact (isNarrow_top_mapSylow_iff e Q).mpr hQtop
  exact hpBeta.2 R hRtop

/-- Source-name alias for Lemma 10.4(c), part 2. -/
theorem sigma'_rank2_beta'
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    {p : ℕ} [Fact p.Prime]
    (hpSigma : p ∉ sigmaPrimes M)
    (hRank : HasElementaryAbelianPRankTwo p M) :
    p ∉ betaPrimes (⊤ : Subgroup G) :=
  sigma_compl_rank2_beta_compl hM hpSigma hRank

end Submission.OddOrder.BG.Section10
