import Submission.OddOrder.BG.Section09.RankThreeUniqueness
import Submission.OddOrder.BG.Section10.CorePredicates
import Submission.OddOrder.MathlibSupport.PGroupPrimeSupport

/-!
# Bender--Glauberman Section 10: maximal-subgroup core facts

This is the block of preliminary facts following the three core definitions
in `BGsection10.v`.  For a maximal subgroup, the prime predicates satisfy
`beta ⊆ alpha ⊆ sigma`; the corresponding core inclusions follow.  The
remaining results identify the Sylow subgroups selected by `sigma` and
compare the local `alpha` and `beta` predicates with their ambient versions.
-/

namespace Submission.OddOrder.BG.Section10

open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section05
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section09
open Submission.OddOrder.MathlibSupport
open scoped Pointwise

universe u

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

private theorem isNarrow_ambientSylow_iff
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (M : Subgroup G) (P : Sylow p M) :
    IsNarrow p (ambientSylow M P) ↔
      IsNarrow p (⊤ : Subgroup P) := by
  have hM : IsNarrow p (ambientSylow M P) ↔
      IsNarrow p (P : Subgroup M) := by
    simpa [ambientSylow] using
      (isNarrow_map_iff_of_injective
        (p := p) M.subtype M.subtype_injective (P : Subgroup M))
  have hP : IsNarrow p (P : Subgroup M) ↔
      IsNarrow p (⊤ : Subgroup P) :=
    isNarrow_subgroup_iff_top (P : Subgroup M)
  exact hM.trans hP

/-- The first inclusion in the preliminary remark on p. 70:
`beta(M) ⊆ alpha(M)`.  Maximality is not needed. -/
theorem beta_sub_alpha
    {G : Type u} [Group G] [Finite G] (M : Subgroup G) :
    betaPrimes M ⊆ alphaPrimes M := by
  classical
  intro p hp
  rcases hp with ⟨hp, hbeta⟩
  letI : Fact p.Prime := ⟨hp⟩
  let P : Sylow p M := Sylow.nonempty.some
  have hRankP : HasElementaryAbelianRankAtLeast p 3
      (⊤ : Subgroup P) := by
    by_contra hnoRank
    apply hbeta P
    intro hRank
    exact (hnoRank hRank).elim
  rcases hRankP with ⟨E, _hEtop, hE⟩
  let E₁ : Subgroup M := E.map (P : Subgroup M).subtype
  let E₂ : Subgroup G := E₁.map M.subtype
  have hE₁ : IsElementaryAbelianOfRank p 3 E₁ := by
    dsimp only [E₁]
    exact hE.map_of_injective (P : Subgroup M).subtype
      (P : Subgroup M).subtype_injective
  exact ⟨hp, E₂, Subgroup.map_subtype_le E₁,
    hE₁.map_of_injective M.subtype M.subtype_injective⟩

/-- The second inclusion in the preliminary remark on p. 70:
`alpha(M) ⊆ sigma(M)` for a maximal subgroup. -/
theorem alpha_sub_sigma
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    alphaPrimes M ⊆ sigmaPrimes M := by
  intro p hp
  rcases hp with ⟨hp, E, hEM, hE⟩
  letI : Fact p.Prime := ⟨hp⟩
  let EM : Subgroup M := E.subgroupOf M
  let eEM : EM ≃* E := Subgroup.subgroupOfEquivOfLe hEM
  have hEMp : IsPGroup p EM := hE.isPGroup.of_equiv eEM.symm
  obtain ⟨P, hEMP⟩ := hEMp.exists_le_sylow
  let PM : Subgroup G := ambientSylow M P
  have hEPM : E ≤ PM := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hEM]
    exact Subgroup.map_mono hEMP
  have hPMp : IsPGroup p PM := P.isPGroup'.map M.subtype
  have hPMproper : PM < ⊤ := mFT_pgroup_proper PM hPMp
  have hPMuniq : PM ∈ minSimple_uniq_max_groups (G := G) :=
    rank3_Uniqueness hPMproper ⟨p, hp, E, hEPM, hE⟩
  have hPMM : PM ≤ M := Subgroup.map_subtype_le (P : Subgroup M)
  have hPMfamily :
      minSimple_max_groups_of (G := G) (PM : Set G) = {M} :=
    def_uniq_mmax hPMuniq hM hPMM
  exact ⟨hp, P, uniq_mmax_norm_sub hPMfamily⟩

/-- The composite inclusion `beta(M) ⊆ sigma(M)`. -/
theorem beta_sub_sigma
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    betaPrimes M ⊆ sigmaPrimes M :=
  (beta_sub_alpha M).trans (alpha_sub_sigma hM)

private theorem primeSetCore_mono
    {G : Type u} [Group G] [Finite G]
    {pi rho : Set ℕ} (hpi : pi ⊆ rho) (M : Subgroup G) :
    primeSetCore pi M ≤ primeSetCore rho M := by
  rw [primeSetCore, primeSetCore]
  apply sSup_le
  intro K hK
  exact le_sSup ⟨hK.1, hK.2.1, IsPiNumber.mono hpi hK.2.2⟩

/-- `M_beta ⊆ M_alpha`. -/
theorem betaCore_le_alphaCore
    {G : Type u} [Group G] [Finite G] (M : Subgroup G) :
    betaCore M ≤ alphaCore M :=
  primeSetCore_mono (beta_sub_alpha M) M

/-- `BGsection10.v: Mbeta_sub_Malpha`. -/
theorem Mbeta_sub_Malpha
    {G : Type u} [Group G] [Finite G] (M : Subgroup G) :
    betaCore M ≤ alphaCore M :=
  betaCore_le_alphaCore M

/-- `M_alpha ⊆ M_sigma` for a maximal subgroup. -/
theorem alphaCore_le_sigmaCore
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    alphaCore M ≤ sigmaCore M :=
  primeSetCore_mono (alpha_sub_sigma hM) M

/-- `BGsection10.v: Malpha_sub_Msigma`. -/
theorem Malpha_sub_Msigma
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    alphaCore M ≤ sigmaCore M :=
  alphaCore_le_sigmaCore hM

/-- `M_beta ⊆ M_sigma` for a maximal subgroup. -/
theorem betaCore_le_sigmaCore
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    betaCore M ≤ sigmaCore M :=
  primeSetCore_mono (beta_sub_sigma hM) M

/-- `BGsection10.v: Mbeta_sub_Msigma`. -/
theorem Mbeta_sub_Msigma
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    betaCore M ≤ sigmaCore M :=
  betaCore_le_sigmaCore hM

private theorem ambientSylow_conj_of_smul_eq
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (M : Subgroup G)
    (P Q : Sylow p M) (m : M) (hm : m • Q = P) :
    ambientSylow M P =
      (ambientSylow M Q).map
        (MulAut.conj (m : G)).toMonoidHom := by
  have hPQ :
      (Q : Subgroup M).map (MulAut.conj m).toMonoidHom =
        (P : Subgroup M) := by
    change MulAut.conj m • (Q : Subgroup M) = (P : Subgroup M)
    rw [← Sylow.coe_subgroup_smul, hm]
  change (P : Subgroup M).map M.subtype =
    ((Q : Subgroup M).map M.subtype).map
      (MulAut.conj (m : G)).toMonoidHom
  rw [← hPQ, Subgroup.map_map, Subgroup.map_map]
  apply congrArg (fun f : M →* G ↦ (Q : Subgroup M).map f)
  ext x
  rfl

/-- The normalizer containment in the definition of `sigma` holds for
every Sylow `p`-subgroup of `M`, not only the chosen witness.  Maximality of
`M` is not needed. -/
theorem norm_sigma_Sylow
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G} {p : ℕ}
    (hp : p ∈ sigmaPrimes M) (P : Sylow p M) :
    Subgroup.normalizer (ambientSylow M P : Set G) ≤ M := by
  rcases hp with ⟨hp, Q, hNQ⟩
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M Q P
  let e : G ≃* G := MulAut.conj (m : G)
  have hPM := ambientSylow_conj_of_smul_eq M P Q m hm
  have hMmap : M.map e.toMonoidHom = M := by
    change e • M = M
    exact Subgroup.conj_smul_eq_self_of_mem m.property
  have hmapped := Subgroup.map_mono hNQ (f := e.toMonoidHom)
  rw [Subgroup.map_equiv_normalizer_eq (ambientSylow M Q) e,
    ← hPM, hMmap] at hmapped
  exact hmapped

/-- A `sigma(M)`-Sylow subgroup of a maximal subgroup is an ambient Sylow
subgroup of the minimal counterexample. -/
theorem sigma_Sylow_G
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G} {p : ℕ}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hp : p ∈ sigmaPrimes M) (P : Sylow p M) :
    ∃ Q : Sylow p G, (Q : Subgroup G) = ambientSylow M P := by
  letI : Fact p.Prime := ⟨hp.1⟩
  exact mmax_sigma_Sylow hM P (norm_sigma_Sylow hp P)

/-- A `sigma(M)`-Sylow subgroup of a maximal subgroup is nontrivial. -/
theorem sigma_Sylow_neq_bot
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G} {p : ℕ}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hp : p ∈ sigmaPrimes M) (P : Sylow p M) :
    ambientSylow M P ≠ ⊥ := by
  intro hPbot
  have hnorm := norm_sigma_Sylow hp P
  rw [hPbot, Subgroup.normalizer_eq_top] at hnorm
  exact (not_le_of_gt (mmax_proper hM)) hnorm

/-- `BGsection10.v: sigma_Sylow_neq1`. -/
theorem sigma_Sylow_neq1
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G} {p : ℕ}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hp : p ∈ sigmaPrimes M) (P : Sylow p M) :
    ambientSylow M P ≠ ⊥ :=
  sigma_Sylow_neq_bot hM hp P

/-- Intrinsic form of `sigma_Sylow_neq_bot`. -/
theorem sigma_Sylow_subgroup_neq_bot
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G} {p : ℕ}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hp : p ∈ sigmaPrimes M) (P : Sylow p M) :
    (P : Subgroup M) ≠ ⊥ := by
  intro hPbot
  apply sigma_Sylow_neq_bot hM hp P
  simp [ambientSylow, hPbot]

/-- `sigma(M)` is contained in the prime support of `M`. -/
theorem sigma_sub_primeSupport
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    sigmaPrimes M ⊆ primeSupport (Nat.card M) := by
  intro p hp
  letI : Fact p.Prime := ⟨hp.1⟩
  let P : Sylow p M := Sylow.nonempty.some
  have hPne : (P : Subgroup M) ≠ ⊥ :=
    sigma_Sylow_subgroup_neq_bot hM hp P
  letI : Nontrivial P :=
    (P : Subgroup M).nontrivial_iff_ne_bot.mpr hPne
  have hsupport : primeSupport (Nat.card P) = {p} :=
    P.isPGroup'.primeSupport_natCard_eq_singleton
  have hpP : p ∈ primeSupport (Nat.card P) := by
    rw [hsupport]
    exact Set.mem_singleton p
  exact ⟨hp.1,
    hpP.2.trans (natCard_subgroup_dvd_natCard (P : Subgroup M))⟩

/-- `BGsection10.v: sigma_sub_pi`. -/
theorem sigma_sub_pi
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    sigmaPrimes M ⊆ primeSupport (Nat.card M) :=
  sigma_sub_primeSupport hM

private theorem alpha_of_sigma_and_alpha_top
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G} {p : ℕ}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hsigma : p ∈ sigmaPrimes M)
    (halpha : p ∈ alphaPrimes (⊤ : Subgroup G)) :
    p ∈ alphaPrimes M := by
  rcases halpha with ⟨hp, E, _hEtop, hE⟩
  letI : Fact p.Prime := ⟨hp⟩
  rcases hsigma.2 with ⟨P, _hNP⟩
  obtain ⟨Q, hQ⟩ := sigma_Sylow_G hM hsigma P
  obtain ⟨R, hER⟩ := hE.isPGroup.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G R Q
  let F : Subgroup G := E.map (MulAut.conj x).toMonoidHom
  have hRQ :
      (R : Subgroup G).map (MulAut.conj x).toMonoidHom =
        (Q : Subgroup G) := by
    change MulAut.conj x • (R : Subgroup G) = (Q : Subgroup G)
    rw [← Sylow.coe_subgroup_smul, hx]
  have hFQ : F ≤ (Q : Subgroup G) := by
    exact (Subgroup.map_mono hER).trans_eq hRQ
  have hQM : (Q : Subgroup G) ≤ M := by
    rw [hQ]
    exact Subgroup.map_subtype_le (P : Subgroup M)
  exact ⟨hp, F, hFQ.trans hQM,
    hE.map_of_injective (MulAut.conj x).toMonoidHom
      (MulAut.conj x).injective⟩

/-- On a maximal subgroup, intersecting `sigma(M)` with the ambient
`alpha` predicate recovers `alpha(M)`. -/
theorem inter_sigma_alpha_eq_alpha
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    sigmaPrimes M ∩ alphaPrimes (⊤ : Subgroup G) = alphaPrimes M := by
  ext p
  constructor
  · rintro ⟨hsigma, halpha⟩
    exact alpha_of_sigma_and_alpha_top hM hsigma halpha
  · intro hp
    have hsigma := alpha_sub_sigma hM hp
    rcases hp with ⟨hprime, E, hEM, hE⟩
    exact ⟨hsigma, hprime, E, hEM.trans le_top, hE⟩

/-- `BGsection10.v: predI_sigma_alpha`. -/
theorem predI_sigma_alpha
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    sigmaPrimes M ∩ alphaPrimes (⊤ : Subgroup G) = alphaPrimes M :=
  inter_sigma_alpha_eq_alpha hM

private theorem not_isNarrow_sylow_of_mem_beta_top
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} (hp : p ∈ betaPrimes (⊤ : Subgroup G))
    (Q : Sylow p G) :
    ¬ IsNarrow p (Q : Subgroup G) := by
  letI : Fact p.Prime := ⟨hp.1⟩
  let e : G ≃* (⊤ : Subgroup G) := Subgroup.topEquiv.symm
  let P : Sylow p (⊤ : Subgroup G) :=
    Q.mapSurjective (f := e.toMonoidHom) e.surjective
  intro hQnarrow
  have hQtop : IsNarrow p (⊤ : Subgroup Q) :=
    (isNarrow_subgroup_iff_top (Q : Subgroup G)).mp hQnarrow
  have hPtop : IsNarrow p (⊤ : Subgroup P) := by
    exact (isNarrow_top_mapSylow_iff e Q).mpr hQtop
  exact hp.2 P hPtop

/-- On a maximal subgroup, intersecting `sigma(M)` with the ambient
`beta` predicate recovers `beta(M)`. -/
theorem inter_sigma_beta_eq_beta
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    sigmaPrimes M ∩ betaPrimes (⊤ : Subgroup G) = betaPrimes M := by
  ext p
  constructor
  · rintro ⟨hsigma, hbetaG⟩
    refine ⟨hbetaG.1, ?_⟩
    letI : Fact p.Prime := ⟨hbetaG.1⟩
    intro P hPnarrow
    obtain ⟨Q, hQ⟩ := sigma_Sylow_G hM hsigma P
    have hQnot := not_isNarrow_sylow_of_mem_beta_top hbetaG Q
    apply hQnot
    rw [hQ]
    exact (isNarrow_ambientSylow_iff M P).mpr hPnarrow
  · intro hbeta
    have hsigma : p ∈ sigmaPrimes M := beta_sub_sigma hM hbeta
    letI : Fact p.Prime := ⟨hbeta.1⟩
    let P : Sylow p M := Sylow.nonempty.some
    obtain ⟨Q, hQ⟩ := sigma_Sylow_G hM hsigma P
    have hQnot : ¬ IsNarrow p (Q : Subgroup G) := by
      rw [hQ]
      intro hPnarrow
      exact hbeta.2 P ((isNarrow_ambientSylow_iff M P).mp hPnarrow)
    exact ⟨hsigma, not_narrow_ideal Q hQnot⟩

/-- `BGsection10.v: predI_sigma_beta`. -/
theorem predI_sigma_beta
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    sigmaPrimes M ∩ betaPrimes (⊤ : Subgroup G) = betaPrimes M :=
  inter_sigma_beta_eq_beta hM

end Submission.OddOrder.BG.Section10
