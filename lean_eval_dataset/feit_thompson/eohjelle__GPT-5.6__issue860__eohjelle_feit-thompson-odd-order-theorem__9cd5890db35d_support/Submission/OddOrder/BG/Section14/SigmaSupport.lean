import Submission.OddOrder.BG.Section14.SigmaDecompositionAndTypes
import Submission.OddOrder.BG.Section14.PTypeStructure
import Submission.OddOrder.PF.Section02.ClassSupportProperties
import Submission.OddOrder.MathlibSupport.SolvableHallConjugacyTransport
import Mathlib.Data.Set.Card.Arithmetic

/-!
# Bender--Glauberman Section 14: the sigma support

This file ports `BGsection14.v`, from `cent1_sub_uniq_sigma_mmax` through
`sigma_decomposition_dichotomy` (the supplement to Theorem 14.4,
Lemmas 14.5--14.6, and the intervening remarks).

The source writes `x *: 'R[x]` for the left coset represented below by
`({x} : Set G) * (ftSignalizer x : Set G)`.  Conjugation is represented by
`MulAut.conj`; consequently conjugating a set is ordinary `Set.image`.
-/

namespace Submission.OddOrder.BG.Section14

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section09
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.BG.Section12
open Submission.OddOrder.BG.Section13
open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.PF
open scoped BigOperators Classical Pointwise

noncomputable section

universe u

variable {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]

/-! ## Local transport adapters -/

private theorem centralizerWithin_map_mulEquiv
    (D S : Subgroup G) (e : G ≃* G) :
    (centralizerWithin D S).map e.toMonoidHom =
      centralizerWithin (D.map e.toMonoidHom)
        (S.map e.toMonoidHom) := by
  ext y
  rw [Subgroup.mem_map_equiv]
  constructor
  · intro hy
    refine ⟨Subgroup.mem_map_equiv.mpr hy.1, ?_⟩
    intro z hz
    have hz' : e.symm z ∈ S := Subgroup.mem_map_equiv.mp hz
    have hcomm := hy.2 (e.symm z) hz'
    simpa using congrArg e hcomm
  · intro hy
    refine ⟨Subgroup.mem_map_equiv.mp hy.1, ?_⟩
    intro z hz
    have hzMap : e z ∈ S.map e.toMonoidHom :=
      (Subgroup.mem_map_iff_mem e.injective).mpr hz
    have hcomm := hy.2 (e z) hzMap
    simpa using congrArg e.symm hcomm

private theorem centralizer_map_mulEquiv
    (A : Subgroup G) (e : G ≃* G) :
    (Subgroup.centralizer (A : Set G)).map e.toMonoidHom =
      Subgroup.centralizer (A.map e.toMonoidHom : Set G) := by
  ext y
  rw [Subgroup.mem_map_equiv]
  constructor
  · intro hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : e.symm z ∈ A := Subgroup.mem_map_equiv.mp hz
    have hcomm := Subgroup.mem_centralizer_iff.mp hy (e.symm z) hz'
    simpa using congrArg e hcomm
  · intro hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzMap : e z ∈ A.map e.toMonoidHom :=
      (Subgroup.mem_map_iff_mem e.injective).mpr hz
    have hcomm := Subgroup.mem_centralizer_iff.mp hy (e z) hzMap
    simpa using congrArg e.symm hcomm

private theorem image_mul_singleton_signalizer
    (e : G ≃* G) (x : G) (R : Subgroup G) :
    e '' (({x} : Set G) * (R : Set G)) =
      ({e x} : Set G) * (R.map e.toMonoidHom : Set G) := by
  ext y
  constructor
  · rintro ⟨_, ⟨a, ha, r, hr, rfl⟩, rfl⟩
    have ha' : a = x := Set.mem_singleton_iff.mp ha
    subst a
    exact ⟨e x, Set.mem_singleton _, e r,
      Subgroup.mem_map.mpr ⟨r, hr, rfl⟩, by simp⟩
  · rintro ⟨a, ha, r, hr, rfl⟩
    have ha' : a = e x := Set.mem_singleton_iff.mp ha
    subst a
    obtain ⟨r0, hr0, hr0r⟩ := Subgroup.mem_map.mp hr
    subst r
    refine ⟨x * r0, ⟨x, Set.mem_singleton _, r0, hr0, rfl⟩, ?_⟩
    exact e.map_mul x r0

private theorem isPiNumber_tau2_compl_sigma
    {M : Subgroup G} {x : G}
    (hx : IsPiNumber (tau2Primes M) (orderOf x)) :
    IsPiNumber (sigmaPrimes M)ᶜ (orderOf x) := by
  apply hx.mono
  intro p hp
  exact hp.2.1

private theorem isPiNumber_of_mem_sigmaCore
    {M : Subgroup G} (hM : M ∈ minSimple_max_groups (G := G))
    {x : G} (hx : x ∈ sigmaCore M) :
    IsPiNumber (sigmaPrimes M) (orderOf x) :=
  (sigmaCore_isPiNumber M).of_dvd
    ((sigmaCore M).orderOf_dvd_natCard hx)

private theorem mem_elementCentralizer_of_commute
    {x y : G} (hxy : Commute x y) :
    x ∈ elementCentralizer y := by
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rcases hz with ⟨n, rfl⟩
  exact (hxy.zpow_right n).eq.symm

/-! ## Equivariance of the signalizer and its cosets -/

/-- A useful supplement to Bender--Glauberman Theorem 14.4. -/
theorem cent1_sub_uniq_sigma_mmax
    {x : G} {M : Subgroup G}
    (hcard :
      (sigmaMaximalOvergroups (Subgroup.zpowers x : Set G)).ncard = 1)
    (hM : M ∈ sigmaMaximalOvergroups
      (Subgroup.zpowers x : Set G)) :
    Subgroup.centralizer (Subgroup.zpowers x : Set G) ≤ M := by
  classical
  obtain ⟨M0, hsingle⟩ := Set.ncard_eq_one.mp hcard
  have hMM0 : M = M0 := by
    rw [hsingle] at hM
    exact Set.mem_singleton_iff.mp hM
  subst M0
  have hmaxM : M ∈ minSimple_max_groups (G := G) := hM.1
  intro y hy
  rw [← norm_mmax hmaxM]
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  let e : G ≃* G := MulAut.conj y
  have hyx : Commute y x := by
    exact (Subgroup.mem_centralizer_iff.mp hy x
      (Subgroup.mem_zpowers x)).symm
  have hex : e x = x := by
    change y * x * y⁻¹ = x
    rw [hyx.eq]
    simp
  have hmapX :
      (Subgroup.zpowers x).map e.toMonoidHom = Subgroup.zpowers x := by
    rw [MonoidHom.map_zpowers]
    apply congrArg Subgroup.zpowers
    change e.toMonoidHom x = x
    exact hex
  have hmapM : M.map e.toMonoidHom ∈
      sigmaMaximalOvergroups (Subgroup.zpowers x : Set G) := by
    rw [← hmapX]
    exact (sigma_mmaxJ M (Subgroup.zpowers x : Set G) y).2 hM
  rw [hsingle] at hmapM
  exact Set.mem_singleton_iff.mp hmapM

/-- The signalizer centralizes its defining element. -/
theorem cent_FT_signalizer (x : G) :
    x ∈ Subgroup.centralizer (ftSignalizer x : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  exact (hr.2 x (Subgroup.mem_zpowers x)).symm

/-- The choice defining the signalizer base is equivariant once the
maximal overgroup supplied by Theorem 14.4 is known to be unique. -/
theorem FT_signalizer_baseJ (x z : G) :
    ftSignalizerBase ((MulAut.conj z) x) =
      (ftSignalizerBase x).map (MulAut.conj z).toMonoidHom := by
  classical
  let e : G ≃* G := MulAut.conj z
  have hzpowers :
      e '' (Subgroup.zpowers x : Set G) =
        (Subgroup.zpowers (e x) : Set G) := by
    change e.toMonoidHom '' (Subgroup.zpowers x : Set G) =
      (Subgroup.zpowers (e.toMonoidHom x) : Set G)
    rw [← Subgroup.coe_map, MonoidHom.map_zpowers]
  have hcardJ :
      (sigmaMaximalOvergroups (Subgroup.zpowers (e x) : Set G)).ncard =
        (sigmaMaximalOvergroups (Subgroup.zpowers x : Set G)).ncard := by
    rw [← hzpowers]
    exact card_sigma_mmaxJ (Subgroup.zpowers x : Set G) z
  by_cases hlarge :
      1 < (sigmaMaximalOvergroups
        (Subgroup.zpowers x : Set G)).ncard
  · by_cases hx1 : x = 1
    · subst x
      have hmaxEmpty :
          minSimple_max_groups_of (G := G)
            (Subgroup.centralizer
              (Subgroup.zpowers (1 : G) : Set G) : Set G) = ∅ := by
        ext L
        simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨hLmax, hcentL⟩
        apply (not_le_of_gt (mmax_proper hLmax))
        intro a _ha
        apply hcentL
        change a ∈ Subgroup.centralizer
          (Subgroup.zpowers (1 : G) : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        have hb1 : b = 1 := by simpa using hb
        subst b
        simp
      have hbaseOne : ftSignalizerBase (1 : G) = ⊥ := by
        unfold ftSignalizerBase
        split
        · rw [hmaxEmpty]
          change (if hS : (∅ : Set (Subgroup G)).Nonempty then
            Classical.choose hS else (⊥ : Subgroup G)) = ⊥
          simp
        · rw [hmaxEmpty]
          change (if hS : (∅ : Set (Subgroup G)).Nonempty then
            Classical.choose hS else (⊥ : Subgroup G)) = ⊥
          simp
      change ftSignalizerBase (e 1) =
        (ftSignalizerBase 1).map e.toMonoidHom
      rw [map_one, hbaseOne, Subgroup.map_bot]
    · have hnonempty :
          (sigmaMaximalOvergroups
            (Subgroup.zpowers x : Set G)).Nonempty := by
        exact (Set.ncard_pos (Set.toFinite _)).mp
          (lt_trans Nat.zero_lt_one hlarge)
      have hell : sigmaLength x = 1 :=
        ell_sigma1P.mpr ⟨hx1, hnonempty⟩
      have hellJ : sigmaLength (e x) = 1 := by
        simpa [e] using (ell_sigmaJ x z).trans hell
      have hlargeJ :
          1 < (sigmaMaximalOvergroups
            (Subgroup.zpowers (e x) : Set G)).ncard := by
        rwa [hcardJ]
      have hctx := (FT_signalizer_context hell).large hlarge
      have hctxJ := (FT_signalizer_context hellJ).large hlargeJ
      have hcentJ :
          (elementCentralizer x).map e.toMonoidHom =
            elementCentralizer (e x) := by
        simpa [elementCentralizer, MonoidHom.map_zpowers] using
          centralizer_map_mulEquiv (Subgroup.zpowers x) e
      have htransport :=
        def_uniq_mmaxJ e hctx.centralizer_maximal
      rw [hcentJ, hctxJ.centralizer_maximal] at htransport
      exact Set.singleton_injective htransport
  · have hlargeJ :
        ¬ 1 < (sigmaMaximalOvergroups
          (Subgroup.zpowers (e x) : Set G)).ncard := by
      simpa [hcardJ] using hlarge
    change ftSignalizerBase (e x) =
      (ftSignalizerBase x).map e.toMonoidHom
    simp [ftSignalizerBase, hlarge, hlargeJ]

/-- Conjugation covariance of the Feit--Thompson signalizer. -/
theorem FT_signalizerJ (x z : G) :
    ftSignalizer ((MulAut.conj z) x) =
      (ftSignalizer x).map (MulAut.conj z).toMonoidHom := by
  let e : G ≃* G := MulAut.conj z
  have hbase := FT_signalizer_baseJ x z
  have hcore :
      sigmaCore (ftSignalizerBase ((MulAut.conj z) x)) =
        (sigmaCore (ftSignalizerBase x)).map e.toMonoidHom := by
    rw [hbase]
    exact sigmaCore_map_mulEquiv (ftSignalizerBase x) e
  unfold ftSignalizer
  have hzpowers :
      Subgroup.zpowers ((MulAut.conj z) x) =
        (Subgroup.zpowers x).map e.toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    apply congrArg Subgroup.zpowers
    simp [e]
  rw [hcore, hzpowers]
  exact (centralizerWithin_map_mulEquiv
    (sigmaCore (ftSignalizerBase x)) (Subgroup.zpowers x) e).symm

/-- The individual signalizer coset commutes with conjugation. -/
theorem sigma_coverJ (x z : G) :
    ({(MulAut.conj z) x} : Set G) *
        (ftSignalizer ((MulAut.conj z) x) : Set G) =
      (MulAut.conj z) ''
        (({x} : Set G) * (ftSignalizer x : Set G)) := by
  rw [FT_signalizerJ]
  exact (image_mul_singleton_signalizer (MulAut.conj z)
    x (ftSignalizer x)).symm

/-- Conjugation covariance of the sigma support `M^~~`. -/
theorem sigma_supportJ (M : Subgroup G) (z : G) :
    sigmaCover (M.map (MulAut.conj z).toMonoidHom) =
      (MulAut.conj z) '' sigmaCover M := by
  classical
  let e : G ≃* G := MulAut.conj z
  have hcore :
      sigmaCore (M.map e.toMonoidHom) =
        (sigmaCore M).map e.toMonoidHom :=
    sigmaCore_map_mulEquiv M e
  ext g
  constructor
  · rintro ⟨y, hySigma, hy1, r, hr, rfl⟩
    rw [hcore] at hySigma
    obtain ⟨x, hxSigma, rfl⟩ := Subgroup.mem_map.mp hySigma
    have hx1 : x ≠ 1 := by
      intro hx
      subst x
      exact hy1 (by simp)
    have hr' : r ∈ ftSignalizer ((MulAut.conj z) x) := by
      simpa [e] using hr
    rw [FT_signalizerJ] at hr'
    obtain ⟨r0, hr0, rfl⟩ := Subgroup.mem_map.mp hr'
    refine ⟨x * r0, ⟨x, hxSigma, hx1, r0, hr0, rfl⟩, ?_⟩
    exact e.map_mul x r0
  · rintro ⟨g0, ⟨x, hxSigma, hx1, r, hr, rfl⟩, rfl⟩
    refine ⟨e x, ?_, ?_, e r, ?_, e.map_mul x r⟩
    · rw [hcore]
      exact Subgroup.mem_map_of_mem e.toMonoidHom hxSigma
    · simpa using e.injective.ne hx1
    · rw [FT_signalizerJ]
      exact Subgroup.mem_map_of_mem e.toMonoidHom hr

/-! ## Decomposition of a signalizer coset -/

/-- The adjusted form of the remark immediately before Bender--Glauberman
Lemma 14.5; it includes the case `x' = 1`. -/
theorem sigma_cover_decomposition
    {x x' : G} (hell : sigmaLength x = 1)
    (hx'R : x' ∈ ftSignalizer x) :
    sigmaDecomposition (x * x') =
      {x} ∪ ({x'} \ ({1} : Set G)) := by
  classical
  by_cases hx'1 : x' = 1
  · subst x'
    simpa using ell1_decomposition hell
  · have hRne : ftSignalizer x ≠ ⊥ := by
      intro hR
      rw [hR] at hx'R
      exact hx'1 (by simpa using hx'R)
    have hctx := FT_signalizer_context hell
    have hlarge :
        1 < (sigmaMaximalOvergroups
          (Subgroup.zpowers x : Set G)).ncard := by
      by_contra hnlarge
      exact hRne (hctx.small_signalizer hnlarge)
    have hlargeCtx := hctx.large hlarge
    let N : Subgroup G := ftSignalizerBase x
    have hNmax : N ∈ minSimple_max_groups (G := G) :=
      hlargeCtx.base_maximal
    have hx'SigmaMem : x' ∈ sigmaCore N := hx'R.1
    have hx'Sigma : IsPiNumber (sigmaPrimes N) (orderOf x') :=
      isPiNumber_of_mem_sigmaCore hNmax hx'SigmaMem
    have hxSigma' : IsPiNumber (sigmaPrimes N)ᶜ (orderOf x) :=
      isPiNumber_tau2_compl_sigma hlargeCtx.x_tau2
    have hcomm : Commute x x' :=
      hx'R.2 x (Subgroup.mem_zpowers x)
    have hcomponent : sigmaComponent N (x * x') = x' :=
      sigmaComponent_mul_eq_right_of_compl_left_of_sigma_right
        N hcomm hxSigma' hx'Sigma
    have hcomplement : sigmaComplementComponent N (x * x') = x :=
      sigmaComplementComponent_mul_eq_left_of_compl_left_of_sigma_right
        N hcomm hxSigma' hx'Sigma
    have hx'mem : x' ∈ sigmaDecomposition (x * x') := by
      have hm := mem_sigma_decomposition (x := x * x') hNmax
        (by simpa only [hcomponent] using hx'1)
      simpa only [hcomponent] using hm
    have hdiff :=
      sigma_decomposition_constt' (x := x * x') hNmax
    rw [hcomponent, hcomplement] at hdiff
    have hxdec : sigmaDecomposition x = {x} :=
      ell1_decomposition hell
    have hsingleton : ({x'} : Set G) ⊆ sigmaDecomposition (x * x') :=
      Set.singleton_subset_iff.mpr hx'mem
    calc
      sigmaDecomposition (x * x') =
          (sigmaDecomposition (x * x') \ {x'}) ∪ {x'} :=
        (Set.sdiff_union_of_subset hsingleton).symm
      _ = {x} ∪ {x'} := by rw [← hdiff, hxdec]
      _ = {x} ∪ ({x'} \ ({1} : Set G)) := by
        rw [Set.sdiff_singleton_eq_self]
        intro h1
        exact hx'1 (Set.mem_singleton_iff.mp h1).symm

/-- The nonidentity form of `sigma_cover_decomposition`. -/
theorem nt_sigma_cover_decomposition
    {x x' : G} (hell : sigmaLength x = 1)
    (hx'1 : x' ≠ 1) (hx'R : x' ∈ ftSignalizer x) :
    sigmaDecomposition (x * x') = ({x, x'} : Set G) := by
  rw [sigma_cover_decomposition hell hx'R,
    Set.sdiff_singleton_eq_self]
  · rfl
  · intro h1
    exact hx'1 (Set.mem_singleton_iff.mp h1).symm

/-- The base element of a signalizer coset is a constituent of every
element of that coset. -/
theorem mem_sigma_cover_decomposition
    {x g : G} (hell : sigmaLength x = 1)
    (hg : g ∈ ({x} : Set G) * (ftSignalizer x : Set G)) :
    x ∈ sigmaDecomposition g := by
  rcases hg with ⟨a, ha, x', hx'R, rfl⟩
  have hax : a = x := Set.mem_singleton_iff.mp ha
  subst a
  rw [sigma_cover_decomposition hell hx'R]
  exact Set.mem_union_left _ (Set.mem_singleton x)

/-- Every element of a signalizer coset has sigma length at most two. -/
theorem ell_sigma_cover
    {x g : G} (hell : sigmaLength x = 1)
    (hg : g ∈ ({x} : Set G) * (ftSignalizer x : Set G)) :
    sigmaLength g ≤ 2 := by
  rcases hg with ⟨a, ha, x', hx'R, rfl⟩
  have hax : a = x := Set.mem_singleton_iff.mp ha
  subst a
  rw [sigmaLength, sigma_cover_decomposition hell hx'R]
  have hright :
      ({x'} \ ({1} : Set G)).ncard ≤ 1 := by
    calc
      ({x'} \ ({1} : Set G)).ncard ≤ ({x'} : Set G).ncard :=
        Set.ncard_le_ncard Set.diff_subset (Set.finite_singleton x')
      _ = 1 := Set.ncard_singleton x'
  exact (Set.ncard_union_le {x} ({x'} \ ({1} : Set G))).trans
    (by simpa using Nat.add_le_add (by simp) hright)

/-- Every element of the sigma support of a maximal subgroup has sigma
length at most two. -/
theorem ell_sigma_support
    {M : Subgroup G} (hM : M ∈ minSimple_max_groups (G := G))
    {g : G} (hg : g ∈ sigmaCover M) :
    sigmaLength g ≤ 2 := by
  rcases hg with ⟨x, hxSigma, hx1, r, hr, rfl⟩
  apply ell_sigma_cover (x := x)
  · exact Msigma_ell1 hM hxSigma hx1
  · exact ⟨x, Set.mem_singleton x, r, hr, rfl⟩

/-! ## Disjointness and cardinality -/

/-- Bender--Glauberman Lemma 14.5(a). -/
theorem sigma_cover_disjoint
    {x y : G} (hellx : sigmaLength x = 1)
    (helly : sigmaLength y = 1) (hxy : x ≠ y) :
    Disjoint
      (({x} : Set G) * (ftSignalizer x : Set G))
      (({y} : Set G) * (ftSignalizer y : Set G)) := by
  classical
  rw [Set.disjoint_left]
  intro g hgx hgy
  rcases hgx with ⟨a, ha, x', hx'R, hgx⟩
  have hax : a = x := Set.mem_singleton_iff.mp ha
  subst a
  rcases hgy with ⟨b, hb, y', hy'R, hgy⟩
  have hby : b = y := Set.mem_singleton_iff.mp hb
  subst b
  have hx1 : x ≠ 1 := (ell_sigma1P.mp hellx).1
  have hy1 : y ≠ 1 := (ell_sigma1P.mp helly).1
  have hydec : y ∈ sigmaDecomposition g :=
    mem_sigma_cover_decomposition helly
      ⟨y, Set.mem_singleton y, y', hy'R, hgy⟩
  rw [← hgx, sigma_cover_decomposition hellx hx'R] at hydec
  have hyx' : y = x' := by
    rcases hydec with hyx | hyx'
    · exact (hxy (Set.mem_singleton_iff.mp hyx).symm).elim
    · exact Set.mem_singleton_iff.mp hyx'.1
  subst x'
  have hyRx : y ∈ ftSignalizer x := hx'R
  have hcomm : Commute x y :=
    hyRx.2 x (Subgroup.mem_zpowers x)
  have hy'x : y' = x := by
    apply mul_left_cancel (a := y)
    calc
      y * y' = g := hgy
      _ = x * y := hgx.symm
      _ = y * x := hcomm.eq
  subst y'
  have hxRy : x ∈ ftSignalizer y := hy'R
  have hctxx := FT_signalizer_context hellx
  have hctxy := FT_signalizer_context helly
  have hRxne : ftSignalizer x ≠ ⊥ := by
    intro hR
    rw [hR] at hyRx
    exact hy1 (by simpa using hyRx)
  have hRyne : ftSignalizer y ≠ ⊥ := by
    intro hR
    rw [hR] at hxRy
    exact hx1 (by simpa using hxRy)
  have hlargex :
      1 < (sigmaMaximalOvergroups
        (Subgroup.zpowers x : Set G)).ncard := by
    by_contra h
    exact hRxne (hctxx.small_signalizer h)
  have hlargey :
      1 < (sigmaMaximalOvergroups
        (Subgroup.zpowers y : Set G)).ncard := by
    by_contra h
    exact hRyne (hctxy.small_signalizer h)
  have hLx := hctxx.large hlargex
  have hLy := hctxy.large hlargey
  let Nx : Subgroup G := ftSignalizerBase x
  let Ny : Subgroup G := ftSignalizerBase y
  have hxNx : x ∈ Nx :=
    hLx.centralizer_le_base
      (mem_elementCentralizer_of_commute (Commute.refl x))
  have hxNy : x ∈ Ny :=
    hLy.centralizer_le_base (mem_elementCentralizer_of_commute hcomm)
  have hNxSigmaY : Nx ∈ sigmaMaximalOvergroups
      (Subgroup.zpowers y : Set G) := by
    refine ⟨hLx.base_maximal, ?_⟩
    exact Subgroup.zpowers_le.mpr hyRx.1
  have hlocal := hLy.overgroup_context hNxSigmaY
  have hxRel : x ∈ elementCentralizerWithin (Nx ⊓ Ny) y := by
    refine ⟨⟨hxNx, hxNy⟩, ?_⟩
    exact mem_elementCentralizer_of_commute hcomm
  have hxInf : x ∈ ftSignalizer y ⊓
      elementCentralizerWithin (Nx ⊓ Ny) y := ⟨hxRy, hxRel⟩
  rw [hlocal.centralizer_disjoint] at hxInf
  exact hx1 (by simpa using hxInf)

/-- Bender--Glauberman Lemma 14.5(b). -/
theorem sigma_support_disjoint
    {M₁ M₂ : Subgroup G}
    (hM₁ : M₁ ∈ minSimple_max_groups (G := G))
    (hM₂ : M₂ ∈ minSimple_max_groups (G := G))
    (hnotconj : ∀ z : G,
      M₂ ≠ M₁.map (MulAut.conj z).toMonoidHom) :
    Disjoint (sigmaCover M₁) (sigmaCover M₂) := by
  classical
  rw [Set.disjoint_left]
  intro g hg₁ hg₂
  rcases hg₁ with ⟨x, hxM₁, hx1, r, hr, rfl⟩
  rcases hg₂ with ⟨y, hyM₂, hy1, s, hs, hxy⟩
  have hellx : sigmaLength x = 1 :=
    Msigma_ell1 hM₁ hxM₁ hx1
  have helly : sigmaLength y = 1 :=
    Msigma_ell1 hM₂ hyM₂ hy1
  have hxeqy : x = y := by
    by_contra hne
    have hdis := sigma_cover_disjoint hellx helly hne
    exact (Set.disjoint_left.mp hdis)
      ⟨x, Set.mem_singleton x, r, hr, rfl⟩
      ⟨y, Set.mem_singleton y, s, hs, hxy.symm⟩
  subst y
  have horder : orderOf x ≠ 1 := by
    simpa [orderOf_eq_one_iff] using hx1
  obtain ⟨p, hp, hpOrder⟩ := Nat.exists_prime_and_dvd horder
  have hpM₁ : p ∈ sigmaPrimes M₁ :=
    isPiNumber_of_mem_sigmaCore hM₁ hxM₁ hp hpOrder
  have hpM₂ : p ∈ sigmaPrimes M₂ :=
    isPiNumber_of_mem_sigmaCore hM₂ hyM₂ hp hpOrder
  exact (Set.disjoint_left.mp
    (sigma_partition hM₁ hM₂ hnotconj)) hpM₁ hpM₂

private theorem subgroupNonidentity_ncard'
    (K : Subgroup G) :
    (subgroupNonidentity K).ncard = Nat.card K - 1 := by
  have hone : (1 : G) ∈ (K : Set G) := K.one_mem
  rw [show subgroupNonidentity K = (K : Set G) \ {1} by
    ext x
    simp [subgroupNonidentity, nonidentitySet]]
  rw [Set.ncard_sdiff_singleton_of_mem hone, ← Nat.card_coe_set_eq,
    SetLike.coe_sort_coe]

private theorem finsum_indicator_eq_ncard
    {α : Type*} (S : Set α) (hS : S.Finite) (P : α → Prop) :
    (∑ᶠ x ∈ S, if P x then (1 : ℕ) else 0) =
      {x | x ∈ S ∧ P x}.ncard := by
  classical
  have hsep : {x | x ∈ S ∧ P x}.Finite :=
    hS.subset (fun _ hx ↦ hx.1)
  rw [finsum_mem_eq_finite_toFinset_sum _ hS,
    Set.ncard_eq_toFinset_card _ hsep]
  rw [Finset.sum_boole]
  apply congrArg Finset.card
  ext x
  simp

/-- Bender--Glauberman Lemma 14.5(c).  The proof uses the incidence set
`(x,L)` where `L` is a conjugate of `M` and `x` is a nonidentity element
of `sigmaCore L`.  Counting first in `x` gives the signalizer cosets;
counting first in `L` gives the displayed product. -/
theorem card_class_support_sigma
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    (classSupportWithin (⊤ : Subgroup G) (sigmaCover M)).ncard =
      (Nat.card (sigmaCore M) - 1) * M.index := by
  classical
  let conjugationAction : MulDistribMulAction G G :=
    MulDistribMulAction.compHom G MulAut.conj
  letI : SMul G G := conjugationAction.toSMul
  letI : MulAction G G := conjugationAction.toMulAction
  letI : MulAction G (Subgroup G) := Subgroup.pointwiseMulAction
  let MsG : Set G :=
    classSupportWithin (⊤ : Subgroup G)
      (subgroupNonidentity (sigmaCore M))
  let coset (x : G) : Set G :=
    ({x} : Set G) * (ftSignalizer x : Set G)
  let MG : Set (Subgroup G) := MulAction.orbit G M
  let incidenceFiber (x : G) : Set (Subgroup G) :=
    {L | L ∈ MG ∧ x ∈ sigmaCore L}

  have hellMsG {x : G} (hx : x ∈ MsG) : sigmaLength x = 1 := by
    rcases hx with ⟨y, hy, z, _, rfl⟩
    have helly : sigmaLength y = 1 :=
      Msigma_ell1 hM hy.1 hy.2
    simpa using (ell_sigmaJ y z⁻¹).trans helly

  have hMsGne {x : G} (hx : x ∈ MsG) : x ≠ 1 := by
    rcases hx with ⟨y, hy, z, _, rfl⟩
    simpa using (MulAut.conj z⁻¹).injective.ne hy.2

  have hrepresentative {x : G} (hx : x ∈ MsG) :
      ∃ L ∈ MG, x ∈ sigmaCore L := by
    rcases hx with ⟨y, hy, z, _, rfl⟩
    refine ⟨z⁻¹ • M, ⟨z⁻¹, rfl⟩, ?_⟩
    change z⁻¹ * y * z ∈
      sigmaCore (M.map (MulAut.conj z⁻¹).toMonoidHom)
    rw [sigmaCore_map_mulEquiv]
    simpa [MulAut.conj_apply] using Subgroup.mem_map_of_mem
      (MulAut.conj z⁻¹).toMonoidHom hy.1

  have hMGmax {L : Subgroup G} (hL : L ∈ MG) :
      L ∈ minSimple_max_groups (G := G) := by
    rcases hL with ⟨z, rfl⟩
    exact (mmaxJ M (MulAut.conj z)).2 hM

  have hfiber {x : G} (hx : x ∈ MsG) :
      incidenceFiber x =
        sigmaMaximalOvergroups (Subgroup.zpowers x : Set G) := by
    ext L
    constructor
    · intro hL
      exact ⟨hMGmax hL.1, Subgroup.zpowers_le.mpr hL.2⟩
    · intro hL
      obtain ⟨L₀, hL₀MG, hxL₀⟩ := hrepresentative hx
      have hL₀ : L₀ ∈
          sigmaMaximalOvergroups (Subgroup.zpowers x : Set G) :=
        ⟨hMGmax hL₀MG, Subgroup.zpowers_le.mpr hxL₀⟩
      obtain ⟨r, hr, hconj⟩ :=
        (FT_signalizer_context (hellMsG hx)).basic.transitive hL₀ hL
      refine ⟨?_, hL.2 (Subgroup.mem_zpowers x)⟩
      rcases hL₀MG with ⟨z, hz⟩
      refine ⟨r * z, ?_⟩
      calc
        (r * z) • M = r • (z • M) := mul_smul r z M
        _ = r • L₀ := congrArg (fun K : Subgroup G ↦ r • K) hz
        _ = L := by
          change L₀.map (MulAut.conj r).toMonoidHom = L
          exact hconj.symm

  have hcoreClass {L : Subgroup G} (hL : L ∈ MG) :
      {x | x ∈ MsG ∧ x ∈ sigmaCore L} =
        subgroupNonidentity (sigmaCore L) := by
    ext x
    constructor
    · rintro ⟨hxMsG, hxL⟩
      exact ⟨hxL, hMsGne hxMsG⟩
    · rintro ⟨hxL, hx1⟩
      refine ⟨?_, hxL⟩
      rcases hL with ⟨z, rfl⟩
      change x ∈
        sigmaCore (M.map (MulAut.conj z).toMonoidHom) at hxL
      rw [sigmaCore_map_mulEquiv] at hxL
      let e : G ≃* G := MulAut.conj z
      let y : G := e.symm x
      have hyM : y ∈ sigmaCore M :=
        Subgroup.mem_map_equiv.mp hxL
      have hey : e y = x := e.apply_symm_apply x
      have hy1 : y ≠ 1 := by
        intro hy
        apply hx1
        rw [← hey, hy]
        simp
      refine ⟨y, ⟨hyM, hy1⟩, z⁻¹, by simp, ?_⟩
      simpa [e, y] using hey

  have hcoreCard {L : Subgroup G} (hL : L ∈ MG) :
      Nat.card (sigmaCore L) = Nat.card (sigmaCore M) := by
    rcases hL with ⟨z, rfl⟩
    change Nat.card
      (sigmaCore (M.map (MulAut.conj z).toMonoidHom)) = _
    rw [sigmaCore_map_mulEquiv,
      Subgroup.card_map_of_injective (MulAut.conj z).injective]

  have hstabilizer : MulAction.stabilizer G M = M := by
    ext z
    rw [MulAction.mem_stabilizer_iff]
    change
      (M.map (MulAut.conj z).toMonoidHom = M) ↔
        z ∈ M
    constructor
    · intro hmap
      have hzNorm : z ∈ Subgroup.normalizer (M : Set G) :=
        (@Subgroup.mem_normalizer_iff_map_conj_eq G _ M z).mpr hmap
      rwa [norm_mmax hM] at hzNorm
    · intro hzM
      apply (@Subgroup.mem_normalizer_iff_map_conj_eq G _ M z).mp
      rwa [norm_mmax hM]

  have hMGcard : MG.ncard = M.index := by
    change (MulAction.orbit G M).ncard = M.index
    rw [← MulAction.index_stabilizer G M, hstabilizer]

  have hfiberCount (x : G) :
      (incidenceFiber x).ncard =
        ∑ᶠ L ∈ MG, if x ∈ sigmaCore L then 1 else 0 := by
    change {L | L ∈ MG ∧ x ∈ sigmaCore L}.ncard = _
    exact (finsum_indicator_eq_ncard MG (Set.toFinite MG)
      (fun L ↦ x ∈ sigmaCore L)).symm

  have hclassFiberCount {L : Subgroup G} (hL : L ∈ MG) :
      (∑ᶠ x ∈ MsG, if x ∈ sigmaCore L then 1 else 0) =
        Nat.card (sigmaCore L) - 1 := by
    rw [finsum_indicator_eq_ncard MsG (Set.toFinite MsG),
      hcoreClass hL, subgroupNonidentity_ncard']

  have hincidenceCount :
      (∑ᶠ x ∈ MsG, Nat.card (ftSignalizer x)) =
        (Nat.card (sigmaCore M) - 1) * M.index := by
    calc
      (∑ᶠ x ∈ MsG, Nat.card (ftSignalizer x)) =
          ∑ᶠ x ∈ MsG, (incidenceFiber x).ncard := by
        apply finsum_mem_congr rfl
        intro x hx
        rw [hfiber hx]
        exact (FT_signalizer_context (hellMsG hx)).basic.card_eq
      _ = ∑ᶠ x ∈ MsG,
          ∑ᶠ L ∈ MG, if x ∈ sigmaCore L then 1 else 0 := by
        apply finsum_mem_congr rfl
        exact fun x _ ↦ hfiberCount x
      _ = ∑ᶠ L ∈ MG,
          ∑ᶠ x ∈ MsG, if x ∈ sigmaCore L then 1 else 0 :=
        finsum_mem_comm
          (fun x L ↦ if x ∈ sigmaCore L then (1 : ℕ) else 0)
          (Set.toFinite MsG) (Set.toFinite MG)
      _ = ∑ᶠ L ∈ MG, (Nat.card (sigmaCore L) - 1) := by
        apply finsum_mem_congr rfl
        exact fun L hL ↦ hclassFiberCount hL
      _ = ∑ᶠ _L ∈ MG, (Nat.card (sigmaCore M) - 1) := by
        apply finsum_mem_congr rfl
        intro L hL
        rw [hcoreCard hL]
      _ = MG.ncard * (Nat.card (sigmaCore M) - 1) := by
        rw [← finsum_one (s := MG),
          finsum_mem_mul' (fun _L : Subgroup G ↦ 1)
            (Nat.card (sigmaCore M) - 1) (Set.toFinite MG)]
        simp
      _ = (Nat.card (sigmaCore M) - 1) * M.index := by
        rw [hMGcard, Nat.mul_comm]

  have hpairwise : MsG.PairwiseDisjoint coset := by
    intro x hx y hy hxy
    exact sigma_cover_disjoint (hellMsG hx) (hellMsG hy) hxy

  have hsupport :
      classSupportWithin (⊤ : Subgroup G) (sigmaCover M) =
        ⋃ x ∈ MsG, coset x := by
    ext g
    constructor
    · rintro ⟨a, ⟨x, hxM, hx1, r, hr, rfl⟩, z, hz, rfl⟩
      apply Set.mem_iUnion₂.mpr
      refine ⟨(MulAut.conj z⁻¹) x, ?_, ?_⟩
      · refine ⟨x, ⟨hxM, hx1⟩, z, hz, ?_⟩
        simp [MulAut.conj_apply]
      · have himage :
            (MulAut.conj z⁻¹) (x * r) ∈
              ({(MulAut.conj z⁻¹) x} : Set G) *
                (ftSignalizer ((MulAut.conj z⁻¹) x) : Set G) := by
          rw [sigma_coverJ x z⁻¹]
          exact ⟨x * r,
            ⟨x, Set.mem_singleton x, r, hr, rfl⟩, rfl⟩
        simpa [coset, MulAut.conj_apply] using himage
    · intro hg
      obtain ⟨x, hxMsG, hg⟩ := Set.mem_iUnion₂.mp hg
      rcases hxMsG with ⟨y, hy, z, hz, rfl⟩
      have hxEq :
          (fun k : G ↦ k⁻¹ * y * k) z = (MulAut.conj z⁻¹) y := by
        simp [MulAut.conj_apply]
      rw [hxEq] at hg
      change g ∈
        ({(MulAut.conj z⁻¹) y} : Set G) *
          (ftSignalizer ((MulAut.conj z⁻¹) y) : Set G) at hg
      rw [sigma_coverJ y z⁻¹] at hg
      rcases hg with ⟨a, ha, rfl⟩
      refine ⟨a, ?_, z, hz, ?_⟩
      · rcases ha with ⟨b, hb, r, hr, rfl⟩
        have hby : b = y := Set.mem_singleton_iff.mp hb
        subst b
        exact ⟨y, hy.1, hy.2, r, hr, rfl⟩
      · simp [MulAut.conj_apply]

  have hcosetCard (x : G) :
      (coset x).ncard = Nat.card (ftSignalizer x) := by
    change (({x} : Set G) * (ftSignalizer x : Set G)).ncard = _
    rw [Set.singleton_mul,
      Set.ncard_image_of_injective _ (mul_right_injective x)]
    rfl

  rw [hsupport]
  calc
    (⋃ x ∈ MsG, coset x).ncard =
        ∑ᶠ x ∈ MsG, (coset x).ncard :=
      (Set.toFinite MsG).ncard_biUnion
        (fun x _ ↦ Set.toFinite (coset x)) hpairwise
    _ = ∑ᶠ x ∈ MsG, Nat.card (ftSignalizer x) := by
      apply finsum_mem_congr rfl
      exact fun x _ ↦ hcosetCard x
    _ = (Nat.card (sigmaCore M) - 1) * M.index := hincidenceCount

/-! ## The sigma-decomposition dichotomy -/

/-- Membership criterion used in the first half of Lemma 14.6: an ambient
`pi`-element lying in a group with a normal `pi`-Hall subgroup lies in that
Hall subgroup. -/
private theorem mem_normalHall_of_isPiNumber_order
    {pi : Set ℕ} {C K : Subgroup G}
    (hKC : K ≤ C) (hKnormal : (K.subgroupOf C).Normal)
    (hKHall : IsHall pi (K.subgroupOf C))
    {x : G} (hxC : x ∈ C)
    (hxPi : IsPiNumber pi (orderOf x)) :
    x ∈ K := by
  let KC : Subgroup C := K.subgroupOf C
  letI : KC.Normal := by simpa [KC] using hKnormal
  let xC : C := ⟨x, hxC⟩
  let qC : C →* C ⧸ KC := QuotientGroup.mk' KC
  have hxPiC : IsPiNumber pi (orderOf xC) := by
    simpa [xC] using hxPi
  have horderPi : IsPiNumber pi (orderOf (qC xC)) :=
    hxPiC.of_dvd (orderOf_map_dvd qC xC)
  have horderCompl : IsPiNumber piᶜ (orderOf (qC xC)) := by
    apply hKHall.isPiNumber_index.of_dvd
    have hdvd : orderOf (qC xC) ∣ KC.index := by
      rw [KC.index_eq_card]
      exact orderOf_dvd_natCard (qC xC)
    simpa [KC] using hdvd
  have horderOne : orderOf (qC xC) = 1 :=
    Nat.eq_one_of_dvd_coprimes
      (horderPi.coprime_compl horderCompl) dvd_rfl dvd_rfl
  have hqOne : qC xC = 1 := orderOf_eq_one_iff.mp horderOne
  have hxKC : xC ∈ KC :=
    (QuotientGroup.eq_one_iff xC).mp (by simpa [qC] using hqOne)
  exact hxKC

/-- The signalizer-coset alternative in Bender--Glauberman Lemma 14.6. -/
def SigmaSignalizerAlternative (g : G) : Prop :=
  ∃ x : G, sigmaLength x = 1 ∧
    x⁻¹ * g ∈ ftSignalizer x

/-- The nontrivial kappa-residual alternative in
Bender--Glauberman Lemma 14.6. -/
def SigmaKappaResidualAlternative (g : G) : Prop :=
  ∃ y : G, sigmaLength y = 1 ∧
    ∃ M : Subgroup G,
      M ∈ sigmaMaximalOvergroups
        (Subgroup.zpowers y : Set G) ∧
      y⁻¹ * g ≠ 1 ∧
      y⁻¹ * g ∈ elementCentralizerWithin M y ∧
      IsPiNumber (kappaPrimes M) (orderOf (y⁻¹ * g))

/-- Proposition-valued representation of the source's exclusive
sigma-decomposition sum.  `exhaustive` is the underlying disjunction and
`exclusive` is its mutual-exclusion clause. -/
structure SigmaDecompositionDichotomy (g : G) : Prop where
  exhaustive :
    SigmaSignalizerAlternative g ∨
      SigmaKappaResidualAlternative g
  exclusive :
    ¬ (SigmaSignalizerAlternative g ∧
      SigmaKappaResidualAlternative g)

/-- The exhaustive half of Bender--Glauberman Lemma 14.6.  This compatibility
form is useful to clients that only perform case analysis; the manifest-listed
`sigma_decomposition_dichotomy` below retains the source's exclusive sum. -/
theorem sigma_decomposition_dichotomy_or
    {g : G} (hg : g ≠ 1) :
    SigmaSignalizerAlternative g ∨
      SigmaKappaResidualAlternative g := by
  classical
  by_cases hsignal :
      ∃ x : G, sigmaLength x = 1 ∧
        x⁻¹ * g ∈ ftSignalizer x
  · exact Or.inl hsignal
  · right
    by_contra hkappa

    have hcomponentOne :
        ∀ (M : Subgroup G),
          M ∈ minSimple_max_groups (G := G) →
          g ∈ M → sigmaComponent M g = 1 := by
      intro M hM hgM
      let x : G := sigmaComponent M g
      let x' : G := sigmaComplementComponent M g
      change x = 1
      by_contra hx1
      have hxM : x ∈ M := by
        apply Subgroup.zpowers_le.mpr hgM
        exact (primeSetComponent_spec (sigmaPrimes M) g).1
      have hxSigma : x ∈ sigmaCore M := by
        exact mem_normalHall_of_isPiNumber_order
          (sigmaCore_le M) (sigmaCore_normal M) (Msigma_Hall hM)
          hxM (sigmaComponent_isPiNumber M g)
      have hellx : sigmaLength x = 1 :=
        Msigma_ell1 hM hxSigma hx1
      have hx'M : x' ∈ M := by
        dsimp [x']
        exact M.mul_mem (M.inv_mem hxM) hgM
      have hcomm : Commute x x' := by
        simpa [x, x'] using sigmaComponent_commute_complement M g
      have hfactor : x * x' = g := by
        simpa [x, x'] using sigmaComponent_mul_complement M g
      have hresidual : x⁻¹ * g = x' := by
        rw [← hfactor]
        simp

      have hx'R : x' ∈ ftSignalizer x := by
        by_cases hx'1 : x' = 1
        · simpa only [hx'1] using (ftSignalizer x).one_mem
        · have hx'Cent : x' ∈ elementCentralizerWithin M x := by
            refine ⟨hx'M, ?_⟩
            exact mem_elementCentralizer_of_commute hcomm.symm
          have halt := pi_of_cent_sigma hM hxSigma hx1
            hx'Cent hx'1 (sigmaComplementComponent_isPiNumber M g)
          rcases halt with hkappa' | ⟨hx'Tau2, hellx', huniqueM⟩
          · exfalso
            apply hkappa
            refine ⟨x, hellx, M, ?_, ?_, ?_, ?_⟩
            · exact ⟨hM, Subgroup.zpowers_le.mpr hxSigma⟩
            · simpa [hresidual] using hx'1
            · simpa [hresidual] using hx'Cent
            · simpa [hresidual] using hkappa'.1
          · have hlarge' :
                1 < (sigmaMaximalOvergroups
                  (Subgroup.zpowers x' : Set G)).ncard := by
              by_contra hnlarge
              have hnonempty := (ell_sigma1P.mp hellx').2
              have hcardOne :
                  (sigmaMaximalOvergroups
                    (Subgroup.zpowers x' : Set G)).ncard = 1 :=
                by
                  have hpos := hnonempty.ncard_pos
                  omega
              obtain ⟨N, hN⟩ := hnonempty
              have hcentN : elementCentralizer x' ≤ N :=
                cent1_sub_uniq_sigma_mmax hcardOne hN
              have hNM : N = M := by
                have hNuniq : N ∈
                    minSimple_max_groups_of (G := G)
                      ((elementCentralizer x' : Subgroup G) : Set G) :=
                  ⟨hN.1, hcentN⟩
                rw [huniqueM] at hNuniq
                exact Set.mem_singleton_iff.mp hNuniq
              have hx'SigmaM : x' ∈ sigmaCore M := by
                rw [← hNM]
                exact hN.2 (Subgroup.mem_zpowers x')
              have hx'Pi := isPiNumber_of_mem_sigmaCore hM hx'SigmaM
              have hx'Order : orderOf x' = 1 :=
                by
                  have hcop : (orderOf x').Coprime (orderOf x') := by
                    simpa [x'] using hx'Pi.coprime_compl
                      (sigmaComplementComponent_isPiNumber M g)
                  exact Nat.eq_one_of_dvd_coprimes hcop dvd_rfl dvd_rfl
              exact hx'1 (orderOf_eq_one_iff.mp hx'Order)
            have hlargeCtx :=
              (FT_signalizer_context hellx').large hlarge'
            have hbase : ftSignalizerBase x' = M := by
              apply Set.singleton_injective
              exact hlargeCtx.centralizer_maximal.symm.trans huniqueM
            have hxInR : x ∈ ftSignalizer x' := by
              rw [ftSignalizer, hbase]
              refine ⟨hxSigma, ?_⟩
              intro z hz
              rcases hz with ⟨n, rfl⟩
              exact (hcomm.zpow_right n).eq.symm
            have hback : x'⁻¹ * g = x := by
              rw [← hfactor, hcomm.eq]
              simp
            exact (hsignal ⟨x', hellx', by
              simpa [hback] using hxInR⟩).elim

      exact hsignal ⟨x, hellx, by
        simpa [hresidual] using hx'R⟩

    have hdecomp : (sigmaDecomposition g).Nonempty := by
      apply (Set.ncard_pos (Set.toFinite _)).mp
      have hlen : sigmaLength g ≠ 0 := by
        intro hzero
        exact hg ((ell_sigma0P g).mp hzero)
      simpa [sigmaLength] using Nat.pos_of_ne_zero hlen
    obtain ⟨x, hx1, M, hM, hxdef⟩ := hdecomp
    have hxPi : IsPiNumber (sigmaPrimes M) (orderOf x) := by
      rw [hxdef]
      exact sigmaComponent_isPiNumber M g
    have hcyclePi :
        IsPiNumber (sigmaPrimes M) (Nat.card (Subgroup.zpowers x)) := by
      simpa [Nat.card_zpowers] using hxPi
    have hcycleNe : Subgroup.zpowers x ≠ ⊥ := by
      intro hbot
      have hxbot : x ∈ (⊥ : Subgroup G) := by
        rw [← hbot]
        exact Subgroup.mem_zpowers x
      exact hx1 (by simpa using hxbot)
    obtain ⟨z, hz⟩ := (sigma_Jsub hM hcyclePi hcycleNe).1
    let L : Subgroup G := M.map (MulAut.conj z⁻¹).toMonoidHom
    have hLmax : L ∈ minSimple_max_groups (G := G) :=
      (mmaxJ M (MulAut.conj z⁻¹)).2 hM
    have hxSigmaL : x ∈ sigmaCore L := by
      have hxz : (MulAut.conj z) x ∈ sigmaCore M := by
        apply hz
        exact Subgroup.mem_map_of_mem
          (MulAut.conj z).toMonoidHom (Subgroup.mem_zpowers x)
      change x ∈ sigmaCore
        (M.map (MulAut.conj z⁻¹).toMonoidHom)
      rw [sigmaCore_map_mulEquiv]
      apply Subgroup.mem_map_equiv.mpr
      simpa using hxz
    have hcomponentL : sigmaComponent L g = x := by
      calc
        sigmaComponent L g = sigmaComponent M g := by
          unfold sigmaComponent
          rw [show sigmaPrimes L = sigmaPrimes M by
            simpa [L] using sigmaPrimes_conj M z⁻¹]
        _ = x := hxdef.symm
    have hellx : sigmaLength x = 1 :=
      Msigma_ell1 hLmax hxSigmaL hx1
    have hgNotL : g ∉ L := by
      intro hgL
      have hzero := hcomponentOne L hLmax hgL
      rw [hcomponentL] at hzero
      exact hx1 hzero
    have hxg : Commute x g := by
      have hxcycle : x ∈ Subgroup.zpowers g := by
        rw [hxdef]
        exact (primeSetComponent_spec (sigmaPrimes M) g).1
      rcases hxcycle with ⟨n, hn⟩
      rw [← hn]
      exact Commute.zpow_left (Commute.refl g) n
    have hLsigma : L ∈
        sigmaMaximalOvergroups (Subgroup.zpowers x : Set G) :=
      ⟨hLmax, Subgroup.zpowers_le.mpr hxSigmaL⟩
    have hlarge :
        1 < (sigmaMaximalOvergroups
          (Subgroup.zpowers x : Set G)).ncard := by
      by_contra hnlarge
      have hcardOne :
          (sigmaMaximalOvergroups
            (Subgroup.zpowers x : Set G)).ncard = 1 :=
        by
          have hpos := (show (sigmaMaximalOvergroups
            (Subgroup.zpowers x : Set G)).Nonempty from ⟨L, hLsigma⟩).ncard_pos
          omega
      have hcentL : elementCentralizer x ≤ L :=
        cent1_sub_uniq_sigma_mmax hcardOne hLsigma
      exact hgNotL (hcentL
        (mem_elementCentralizer_of_commute hxg.symm))

    have hlargeCtx := (FT_signalizer_context hellx).large hlarge
    let N : Subgroup G := ftSignalizerBase x
    have hNmax : N ∈ minSimple_max_groups (G := G) :=
      hlargeCtx.base_maximal
    have hgN : g ∈ N :=
      hlargeCtx.centralizer_le_base
        (mem_elementCentralizer_of_commute hxg.symm)
    have hlocal := hlargeCtx.overgroup_context hLsigma
    have hcomponentN : sigmaComponent N g = 1 :=
      hcomponentOne N hNmax hgN
    have hgSigmaN' :
        IsPiNumber (sigmaPrimes N)ᶜ (orderOf g) := by
      have hpi := sigmaComplementComponent_isPiNumber N g
      have hfac := sigmaComponent_mul_complement N g
      rw [hcomponentN, one_mul] at hfac
      simpa [hfac] using hpi

    let A : Subgroup G := Subgroup.zpowers g
    let H : Subgroup G := L ⊓ N
    have hAN : A ≤ N := Subgroup.zpowers_le.mpr hgN
    have hApi : IsPiNumber (sigmaPrimes N)ᶜ (Nat.card A) := by
      simpa [A, Nat.card_zpowers] using hgSigmaN'
    obtain ⟨t, hAHt, _, _, _, _, _⟩ :=
      exists_ambient_isHall_map_conj_ge_of_isSolvable
        (K := N) (A := A) (H := H)
        hAN inf_le_right (mmax_sol hNmax) hApi
          hlocal.hall_intersection
    let u : G := (t : N)
    have hgHt : g ∈ H.map (MulAut.conj u).toMonoidHom := by
      apply hAHt
      exact Subgroup.mem_zpowers g
    let Lu : Subgroup G := L.map (MulAut.conj u).toMonoidHom
    have hLuMax : Lu ∈ minSimple_max_groups (G := G) :=
      (mmaxJ L (MulAut.conj u)).2 hLmax
    have hgLu : g ∈ Lu :=
      (Subgroup.map_mono inf_le_left) hgHt
    have hzero := hcomponentOne Lu hLuMax hgLu
    have hcomponentLu : sigmaComponent Lu g = sigmaComponent L g := by
      unfold sigmaComponent
      rw [show sigmaPrimes Lu = sigmaPrimes L by
        simpa [Lu] using sigmaPrimes_conj L u]
    rw [hcomponentLu, hcomponentL] at hzero
    exact hx1 hzero

/-- Bender--Glauberman Lemma 14.6, including the source's exclusive-sum
conclusion.

The two alternatives cannot occur simultaneously: comparing their
sigma-decompositions either makes the kappa residual simultaneously a sigma
element, makes the signalizer base conjugate to its kappa overgroup and
forces a tau2 element to have complementary order, or puts one prime in two
disjoint sigma-prime sets. -/
theorem sigma_decomposition_dichotomy
    {g : G} (hg : g ≠ 1) :
    SigmaDecompositionDichotomy g := by
  classical
  refine ⟨sigma_decomposition_dichotomy_or hg, ?_⟩
  rintro ⟨⟨x, hellx, hxR⟩,
    ⟨y, helly, M, hMy, hy'1, hy'Cent, hy'Kappa⟩⟩
  let x' : G := x⁻¹ * g
  let y' : G := y⁻¹ * g
  change x' ∈ ftSignalizer x at hxR
  change y' ≠ 1 at hy'1
  change y' ∈ elementCentralizerWithin M y at hy'Cent
  change IsPiNumber (kappaPrimes M) (orderOf y') at hy'Kappa
  have hx1 : x ≠ 1 := (ell_sigma1P.mp hellx).1
  have hy1 : y ≠ 1 := (ell_sigma1P.mp helly).1
  have hgx : x * x' = g := by simp [x']
  have hgy : y * y' = g := by simp [y']
  have hcommx : Commute x x' :=
    hxR.2 x (Subgroup.mem_zpowers x)
  have hcommy : Commute y y' :=
    hy'Cent.2 y (Subgroup.mem_zpowers y)
  have hMmax : M ∈ minSimple_max_groups (G := G) := hMy.1
  have hySigma : y ∈ sigmaCore M :=
    hMy.2 (Subgroup.mem_zpowers y)
  have hySigmaPi : IsPiNumber (sigmaPrimes M) (orderOf y) :=
    (sigmaCore_isPiNumber M).of_dvd
      ((sigmaCore M).orderOf_dvd_natCard hySigma)
  have hy'SigmaCompl :
      IsPiNumber (sigmaPrimes M)ᶜ (orderOf y') :=
    hy'Kappa.mono (kappa_sigma' M)
  have hy'Tau2Compl :
      IsPiNumber (tau2Primes M)ᶜ (orderOf y') := by
    apply hy'Kappa.mono
    intro p hpKappa
    rcases kappa_tau13 hpKappa with hpTau1 | hpTau3
    · exact tau2'1 M hpTau1
    · intro hpTau2
      exact (tau3'2 M hpTau2) hpTau3
  have hyComponent : sigmaComponent M g = y := by
    calc
      sigmaComponent M g = sigmaComponent M (y' * y) := by
        rw [← hgy, hcommy.eq]
      _ = y :=
        sigmaComponent_mul_eq_right_of_compl_left_of_sigma_right
          M hcommy.symm hy'SigmaCompl hySigmaPi
  have hyDecomposition : y ∈ sigmaDecomposition g := by
    rw [← hyComponent]
    exact mem_sigma_decomposition hMmax
      (by simpa [hyComponent] using hy1)
  have hxDecomposition :
      sigmaDecomposition g =
        {x} ∪ ({x'} \ ({1} : Set G)) := by
    rw [← hgx]
    exact sigma_cover_decomposition hellx hxR
  have hMcentralizer :
      M ∈ minSimple_max_groups_of (G := G)
        ((elementCentralizer y : Subgroup G) : Set G) := by
    refine ⟨hMmax, ?_⟩
    rcases pi_of_cent_sigma hMmax hySigma hy1 hy'Cent hy'1
        hy'SigmaCompl with hKappa | hTau2
    · exact hKappa.2
    · have hy'Order : orderOf y' = 1 :=
        Nat.eq_one_of_dvd_coprimes
          (hTau2.1.coprime_compl hy'Tau2Compl) dvd_rfl dvd_rfl
      exact (hy'1 (orderOf_eq_one_iff.mp hy'Order)).elim

  rw [hxDecomposition] at hyDecomposition
  rcases hyDecomposition with hyx | hyx'
  · have hyEq : y = x := Set.mem_singleton_iff.mp hyx
    have hy'Eq : y' = x' := by simp [y', x', hyEq]
    have hRne : ftSignalizer x ≠ ⊥ := by
      intro hR
      rw [hR] at hxR
      have hx'1 : x' = 1 := by simpa using hxR
      exact hy'1 (hy'Eq.trans hx'1)
    have hlarge :
        1 < (sigmaMaximalOvergroups
          (Subgroup.zpowers x : Set G)).ncard := by
      by_contra hnlarge
      exact hRne
        ((FT_signalizer_context hellx).small_signalizer hnlarge)
    have hLarge := (FT_signalizer_context hellx).large hlarge
    have hMcentralizerX :
        M ∈ minSimple_max_groups_of (G := G)
          ((elementCentralizer x : Subgroup G) : Set G) := by
      simpa [hyEq] using hMcentralizer
    have hMbase : M = ftSignalizerBase x := by
      rw [hLarge.centralizer_maximal] at hMcentralizerX
      exact Set.mem_singleton_iff.mp hMcentralizerX
    have hx'Sigma : x' ∈ sigmaCore (ftSignalizerBase x) := hxR.1
    have hx'SigmaPi :
        IsPiNumber (sigmaPrimes (ftSignalizerBase x))
          (orderOf x') :=
      (sigmaCore_isPiNumber (ftSignalizerBase x)).of_dvd
        ((sigmaCore (ftSignalizerBase x)).orderOf_dvd_natCard hx'Sigma)
    have hx'SigmaCompl :
        IsPiNumber (sigmaPrimes (ftSignalizerBase x))ᶜ
          (orderOf x') := by
      have h := hy'Kappa.mono (kappa_sigma' M)
      simpa [hMbase, hy'Eq] using h
    have hx'Order : orderOf x' = 1 :=
      Nat.eq_one_of_dvd_coprimes
        (hx'SigmaPi.coprime_compl hx'SigmaCompl) dvd_rfl dvd_rfl
    exact hy'1 (hy'Eq.trans (orderOf_eq_one_iff.mp hx'Order))
  · have hyEq : y = x' := Set.mem_singleton_iff.mp hyx'.1
    have hx'1 : x' ≠ 1 := by simpa [hyEq] using hy1
    have hy'Eq : y' = x := by
      calc
        y' = x'⁻¹ * g := by simp [y', hyEq]
        _ = x'⁻¹ * (x * x') := by rw [hgx]
        _ = x := by rw [hcommx.eq]; simp
    have hRne : ftSignalizer x ≠ ⊥ := by
      intro hR
      rw [hR] at hxR
      exact hx'1 (by simpa using hxR)
    have hlarge :
        1 < (sigmaMaximalOvergroups
          (Subgroup.zpowers x : Set G)).ncard := by
      by_contra hnlarge
      exact hRne
        ((FT_signalizer_context hellx).small_signalizer hnlarge)
    have hLarge := (FT_signalizer_context hellx).large hlarge
    by_cases hconj : ∃ z : G,
        M = (ftSignalizerBase x).map
          (MulAut.conj z).toMonoidHom
    · obtain ⟨z, hMz⟩ := hconj
      have hxTau2Compl :
          IsPiNumber (tau2Primes (ftSignalizerBase x))ᶜ
            (orderOf x) := by
        have hTauEq : tau2Primes M =
            tau2Primes (ftSignalizerBase x) := by
          rw [hMz, tau2J]
        rw [← hTauEq]
        simpa only [hy'Eq] using hy'Tau2Compl
      have hxOrder : orderOf x = 1 :=
        Nat.eq_one_of_dvd_coprimes
          (hLarge.x_tau2.coprime_compl hxTau2Compl) dvd_rfl dvd_rfl
      exact hx1 (orderOf_eq_one_iff.mp hxOrder)
    · have hnotconj : ∀ z : G,
          M ≠ (ftSignalizerBase x).map
            (MulAut.conj z).toMonoidHom := by
        intro z hz
        exact hconj ⟨z, hz⟩
      have hx'SigmaBase : x' ∈ sigmaCore (ftSignalizerBase x) :=
        hxR.1
      have hx'SigmaM : x' ∈ sigmaCore M := by
        simpa [hyEq] using hySigma
      have horderNe : orderOf x' ≠ 1 := by
        simpa [orderOf_eq_one_iff] using hx'1
      obtain ⟨p, hp, hpOrder⟩ := Nat.exists_prime_and_dvd horderNe
      have hpBase : p ∈ sigmaPrimes (ftSignalizerBase x) :=
        (sigmaCore_isPiNumber (ftSignalizerBase x)) hp
          (hpOrder.trans
            ((sigmaCore (ftSignalizerBase x)).orderOf_dvd_natCard
              hx'SigmaBase))
      have hpM : p ∈ sigmaPrimes M :=
        (sigmaCore_isPiNumber M) hp
          (hpOrder.trans ((sigmaCore M).orderOf_dvd_natCard hx'SigmaM))
      exact (Set.disjoint_left.mp
        (sigma_partition hLarge.base_maximal hMmax hnotconj))
          hpBase hpM

/-- Compatibility alias for clients that used the temporary split name. -/
theorem sigma_decomposition_dichotomy_exclusive
    {g : G} (hg : g ≠ 1) :
    SigmaDecompositionDichotomy g :=
  sigma_decomposition_dichotomy hg

end

end Submission.OddOrder.BG.Section14
