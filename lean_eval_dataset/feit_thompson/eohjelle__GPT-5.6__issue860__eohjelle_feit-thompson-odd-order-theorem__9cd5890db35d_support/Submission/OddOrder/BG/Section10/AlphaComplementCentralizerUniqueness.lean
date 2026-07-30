import Submission.OddOrder.BG.Section09.RankThreeUniqueness
import Submission.OddOrder.BG.Section10.AlphaSigmaCore
import Submission.OddOrder.MathlibSupport.CoprimeSolvableInvariantSylowExtension
import Submission.OddOrder.MathlibSupport.ElementaryAbelianRankSylowTransport
import Submission.OddOrder.MathlibSupport.OddPGroupElementaryCentralizer

/-!
# Bender--Glauberman Lemma 10.3

Let `M` be a maximal subgroup of the minimal counterexample.  If an
`alpha(M)`-complement subgroup `X` is centralized, inside the alpha core,
by an elementary-abelian subgroup of rank two, then the centralizer of `X`
in `M` has a unique maximal overgroup.

The proof follows `BGsection10.v: cent_alpha'_uniq`.  The only sizeable
interface conversion is the local Hall--Sylow adapter below: it turns a
Sylow subgroup of the alpha core into a Sylow subgroup of `M`.  Keeping that
conversion local makes the mathematical argument independent of the exact
subgroup-of-subgroup representation used by the Hall API.
-/

namespace Submission.OddOrder.BG.Section10

open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section09
open Submission.OddOrder.MathlibSupport
open scoped Pointwise IsMulCommutative

universe u

private theorem exists_elementaryAbelian_rank_three_of_rank_two_lt
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B E : Subgroup G}
    (hB : IsElementaryAbelianOfRank p 2 B)
    (hE : IsElementaryAbelianGroup p E) (hBE : B < E) :
    ∃ F : Subgroup G,
      F ≤ E ∧ IsElementaryAbelianOfRank p 3 F := by
  obtain ⟨n, hEcard⟩ := hE.isPGroup.exists_card_eq
  have hpowlt : p ^ 2 < p ^ n := by
    simpa only [hB.card_eq, hEcard] using
      natCard_subgroup_lt_of_lt hBE
  have hn : 3 ≤ n := by
    by_contra hnot
    have hnle : n ≤ 2 := by omega
    exact (not_lt_of_ge
      (Nat.pow_le_pow_right (Fact.out : p.Prime).pos hnle)) hpowlt
  have hpThreeLe : p ^ 3 ≤ Nat.card E := by
    rw [hEcard]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hn
  obtain ⟨F₀, hF₀card⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card
      (G := E) (Fact.out : p.Prime) hE.isPGroup hpThreeLe
  have hF₀ : IsElementaryAbelianOfRank p 3 F₀ := by
    letI : IsMulCommutative E := hE.commutative
    refine
      { isPGroup := hE.isPGroup.to_subgroup F₀
        commutative := by infer_instance
        pow_eq_one := ?_
        card_eq := hF₀card }
    intro x
    apply Subtype.ext
    exact hE.pow_eq_one (x : E)
  let F : Subgroup G := F₀.map E.subtype
  exact ⟨F, Subgroup.map_subtype_le F₀,
    hF₀.map_of_injective E.subtype E.subtype_injective⟩

/-- A rank-two elementary subgroup is maximal in a `p`-group once its
centralizer contains no elementary-abelian subgroup of rank three. -/
private theorem isPMaxElem_of_no_rank_three_centralizerWithin
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {P B : Subgroup G}
    (hB : IsElementaryAbelianOfRank p 2 B) (hBP : B ≤ P)
    (hRank : ¬ HasElementaryAbelianRankAtLeast p 3
      (centralizerWithin P B)) :
    IsPMaxElem p P B := by
  refine ⟨⟨hBP, hB.toIsElementaryAbelianGroup⟩, ?_⟩
  intro E hE hBE
  apply le_antisymm ?_ hBE
  by_contra hnot
  have hBElt : B < E :=
    lt_of_le_of_ne hBE (fun hEq ↦ hnot hEq.ge)
  obtain ⟨F, hFE, hF⟩ :=
    exists_elementaryAbelian_rank_three_of_rank_two_lt
      hB hE.2 hBElt
  have hEC : E ≤ centralizerWithin P B := by
    intro x hx
    refine mem_centralizerWithin.mpr ⟨hE.1 hx, ?_⟩
    intro b hb
    letI : IsMulCommutative E := hE.2.commutative
    exact congrArg Subtype.val
      (mul_comm (⟨b, hBE hb⟩ : E) (⟨x, hx⟩ : E))
  exact hRank ⟨F, hFE.trans hEC, hF⟩

/-- Local adapter for the `subHall_Sylow` step in the Coq proof. -/
private theorem exists_sylow_eq_map_of_sylow_hall
    {H : Type u} [Group H] [Finite H]
    {pi : Set ℕ} {p : ℕ} (hp : p.Prime)
    {A : Subgroup H} (hA : IsHall pi A) (hpPi : p ∈ pi)
    (P : Sylow p A) :
    ∃ Q : Sylow p H,
      (Q : Subgroup H) = (P : Subgroup A).map A.subtype := by
  letI : Fact p.Prime := ⟨hp⟩
  let S : Subgroup H := (P : Subgroup A).map A.subtype
  have hSp : IsPGroup p S := by
    dsimp [S]
    exact P.isPGroup'.map A.subtype
  have hpAindex : ¬ p ∣ A.index := by
    intro hpIndex
    exact hA.isPiNumber_index hp hpIndex hpPi
  have hpSindex : ¬ p ∣ S.index := by
    dsimp [S]
    rw [Subgroup.index_map_subtype]
    exact hp.not_dvd_mul P.not_dvd_index hpAindex
  exact ⟨hSp.toSylow hpSindex, rfl⟩

/-- Every Sylow subgroup of `M` has rank at least three at a prime in
`alpha(M)`.  This is the cardinal-rank form of `rank_Sylow`. -/
private theorem sylow_has_rank_three_of_mem_alpha
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hpAlpha : p ∈ alphaPrimes M) (P : Sylow p M) :
    HasElementaryAbelianRankAtLeast p 3
      ((P : Subgroup M).map M.subtype) := by
  classical
  rcases hpAlpha with ⟨_hprime, E, hEM, hE⟩
  let EM : Subgroup M := E.subgroupOf M
  have hEMrank : IsElementaryAbelianOfRank p 3 EM :=
    hE.subgroupOf hEM
  obtain ⟨Q, hEMQ⟩ := hEMrank.isPGroup.exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M Q P
  let C : Subgroup M :=
    EM.map (MulAut.conj m).toMonoidHom
  have hQmap :
      (Q : Subgroup M).map (MulAut.conj m).toMonoidHom =
        (P : Subgroup M) := by
    change MulAut.conj m • (Q : Subgroup M) = (P : Subgroup M)
    rw [← Sylow.coe_subgroup_smul, hm]
  have hCP : C ≤ (P : Subgroup M) :=
    (Subgroup.map_mono hEMQ).trans_eq hQmap
  have hC : IsElementaryAbelianOfRank p 3 C :=
    hEMrank.map_of_injective (MulAut.conj m).toMonoidHom
      (MulAut.conj m).injective
  let D : Subgroup G := C.map M.subtype
  exact ⟨D, (Subgroup.map_mono hCP),
    hC.map_of_injective M.subtype M.subtype_injective⟩

/-- `BGsection10.v: cent_alpha'_uniq` (Bender--Glauberman Lemma 10.3).

The last hypothesis is the proposition-valued replacement for
`'r('C_(M`_alpha)(X)) >= 2`. -/
theorem cent_alpha_compl_uniq
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M X : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hXM : X ≤ M)
    (hXalphaCompl :
      IsPiNumber (alphaPrimes M)ᶜ (Nat.card X))
    (hRank : ∃ p : ℕ, p.Prime ∧
      HasElementaryAbelianRankAtLeast p 2
        (centralizerWithin (alphaCore M) X)) :
    centralizerWithin M X ∈
      minSimple_uniq_max_groups (G := G) := by
  classical
  rcases hRank with ⟨p, hp, B, hBC, hB⟩
  letI : Fact p.Prime := ⟨hp⟩
  let A : Subgroup M := (alphaCore M).subgroupOf M
  let XM : Subgroup M := X.subgroupOf M
  have hBA : B ≤ alphaCore M :=
    hBC.trans (centralizerWithin_le_left (alphaCore M) X)
  have hBM : B ≤ M := hBA.trans (alphaCore_le M)
  let BM : Subgroup M := B.subgroupOf M
  have hBMrank : IsElementaryAbelianOfRank p 2 BM :=
    hB.subgroupOf hBM
  have hBMA : BM ≤ A := by
    intro b hb
    exact hBA hb

  have hpBcard : p ∣ Nat.card B := by
    rw [hB.card_eq]
    exact dvd_pow_self p (by omega)
  have hpAcard : p ∣ Nat.card (alphaCore M) :=
    hpBcard.trans (Subgroup.card_dvd_of_le hBA)
  have hpAlpha : p ∈ alphaPrimes M :=
    alphaCore_isPiNumber M hp hpAcard

  have hCoreXcop :
      (Nat.card (alphaCore M)).Coprime (Nat.card X) := by
    apply Nat.coprime_of_dvd
    intro q hq hqCore hqX
    have hqAlpha : q ∈ alphaPrimes M :=
      alphaCore_isPiNumber M hq hqCore
    have hqCompl : q ∈ (alphaPrimes M)ᶜ :=
      hXalphaCompl hq hqX
    exact hqCompl hqAlpha
  have hAXMcop : (Nat.card A).Coprime (Nat.card XM) := by
    dsimp only [A, XM]
    rw [natCard_subgroupOf_eq (alphaCore_le M),
      natCard_subgroupOf_eq hXM]
    exact hCoreXcop

  have hAnormal : A.Normal := by
    simpa [A] using alphaCore_normal M
  have hXMnormA : XM ≤ Subgroup.normalizer (A : Set M) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hAnormal]
    exact le_top
  have hBMcentXM : BM ≤ Subgroup.centralizer (XM : Set M) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    apply Subtype.ext
    exact (mem_centralizerWithin.mp (hBC hb)).2 (x : G) hx
  have hXMnormBM : XM ≤ Subgroup.normalizer (BM : Set M) :=
    (Subgroup.le_centralizer_iff.mp hBMcentXM).trans
      (Subgroup.centralizer_le_normalizer (BM : Set M))
  have hAsol : IsSolvable A := by
    letI : IsSolvable M := mmax_sol hM
    infer_instance

  obtain ⟨P, hXMnormP, hBMP⟩ :=
    exists_normalized_sylow_ge_of_coprime_of_isSolvable
      (G := M) (A := XM) (L := A) (X := BM)
      hXMnormA hAXMcop hAsol hBMA hBMrank.isPGroup hXMnormBM
  let PM : Subgroup M := (P : Subgroup A).map A.subtype
  let PG : Subgroup G := PM.map M.subtype
  have hPMA : PM ≤ A := Subgroup.map_subtype_le (P : Subgroup A)
  have hPGA : PG ≤ alphaCore M := by
    calc
      PG = PM.map M.subtype := rfl
      _ ≤ A.map M.subtype := Subgroup.map_mono hPMA
      _ = alphaCore M :=
        Subgroup.map_subgroupOf_eq_of_le (alphaCore_le M)
  have hBPG : B ≤ PG := by
    calc
      B = BM.map M.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hBM).symm
      _ ≤ PM.map M.subtype := Subgroup.map_mono hBMP
      _ = PG := rfl

  have hCentralizerProper : centralizerWithin M X < ⊤ :=
    lt_of_le_of_lt (centralizerWithin_le_left M X) (mmax_proper hM)
  by_cases hRankThree :
      HasElementaryAbelianRankAtLeast p 3
        (centralizerWithin PG B)
  · have hRankB : ∃ q : ℕ, q.Prime ∧
        HasElementaryAbelianRankAtLeast q 2 B :=
      ⟨p, hp, B, le_rfl, hB⟩
    have hRankCentralizer : ∃ q : ℕ, q.Prime ∧
        HasElementaryAbelianRankAtLeast q 3
          (Subgroup.centralizer (B : Set G)) := by
      rcases hRankThree with ⟨E, hEC, hE⟩
      exact ⟨p, hp, E, hEC.trans inf_le_right, hE⟩
    have hBuniq : B ∈ minSimple_uniq_max_groups (G := G) :=
      cent_rank3_Uniqueness hRankB hRankCentralizer
    have hBCMX : B ≤ centralizerWithin M X :=
      hBC.trans (centralizerWithin_mono_left (alphaCore_le M))
    exact uniq_mmaxS hBCMX hCentralizerProper hBuniq
  · have hBmax : IsPMaxElem p PG B :=
      isPMaxElem_of_no_rank_three_centralizerWithin hB hBPG hRankThree
    have htorsion :
        pTorsionCentralizerWithin p PG B = (B : Set G) :=
      isPMaxElem_iff_pTorsionCentralizerWithin.mp hBmax
    have hBcentX : B ≤ Subgroup.centralizer (X : Set G) :=
      hBC.trans inf_le_right
    have hXcentB : X ≤ Subgroup.centralizer (B : Set G) :=
      Subgroup.le_centralizer_iff.mp hBcentX
    have hXfix : X ≤ Subgroup.centralizer
        (pTorsionCentralizerWithin p PG B) := by
      rw [htorsion]
      exact hXcentB

    have hXnormPG : X ≤ Subgroup.normalizer (PG : Set G) := by
      calc
        X = XM.map M.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hXM).symm
        _ ≤ (Subgroup.normalizer (PM : Set M)).map M.subtype :=
          Subgroup.map_mono hXMnormP
        _ ≤ Subgroup.normalizer (PG : Set G) := by
          simpa [PG] using Subgroup.le_normalizer_map M.subtype
    have hPGp : IsPGroup p PG := by
      dsimp [PG, PM]
      exact (P.isPGroup'.map A.subtype).map M.subtype
    have hPGXcop : (Nat.card PG).Coprime (Nat.card X) :=
      hCoreXcop.coprime_dvd_left (Subgroup.card_dvd_of_le hPGA)
    have hXcentPG : X ≤ Subgroup.centralizer (PG : Set G) :=
      coprime_odd_faithful_centralizes_of_pTorsionCentralizer
        ⟨hBPG, hB.toIsElementaryAbelianGroup⟩ hPGp hXnormPG
        hPGXcop (mFT_odd PG) hXfix
    have hPGcentX : PG ≤ Subgroup.centralizer (X : Set G) :=
      Subgroup.le_centralizer_iff.mp hXcentPG
    have hPGCMX : PG ≤ centralizerWithin M X := by
      exact le_inf (hPGA.trans (alphaCore_le M)) hPGcentX

    have hAHall : IsHall (alphaPrimes M) A := by
      simpa [A] using Malpha_Hall hM
    obtain ⟨Q, hQ⟩ :=
      exists_sylow_eq_map_of_sylow_hall hp hAHall hpAlpha P
    have hPGrank : HasElementaryAbelianRankAtLeast p 3 PG := by
      simpa [PG, PM, hQ] using
        sylow_has_rank_three_of_mem_alpha hpAlpha Q
    have hPGproper : PG < ⊤ :=
      lt_of_le_of_lt (hPGA.trans (alphaCore_le M)) (mmax_proper hM)
    have hPGuniq : PG ∈ minSimple_uniq_max_groups (G := G) :=
      rank3_Uniqueness hPGproper ⟨p, hp, hPGrank⟩
    exact uniq_mmaxS hPGCMX hCentralizerProper hPGuniq

/-- Source-name alias for downstream ports that follow the Coq file
literally. -/
theorem cent_alpha'_uniq
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M X : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hXM : X ≤ M)
    (hXalphaCompl :
      IsPiNumber (alphaPrimes M)ᶜ (Nat.card X))
    (hRank : ∃ p : ℕ, p.Prime ∧
      HasElementaryAbelianRankAtLeast p 2
        (centralizerWithin (alphaCore M) X)) :
    centralizerWithin M X ∈
      minSimple_uniq_max_groups (G := G) :=
  cent_alpha_compl_uniq hM hXM hXalphaCompl hRank

end Submission.OddOrder.BG.Section10
