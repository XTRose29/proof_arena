import Submission.OddOrder.BG.Section12.Tau2NormalizerFTType
import Submission.OddOrder.BG.Section10.BetaHallStructure
import Submission.OddOrder.BG.Section09.RankThreeUniqueness
import Submission.OddOrder.MathlibSupport.ComplementQuotient
import Submission.OddOrder.MathlibSupport.CommutatorSup
import Submission.OddOrder.MathlibSupport.CoprimeExtraspecialCentralizerGeneration
import Submission.OddOrder.MathlibSupport.ElementaryAbelianRankSylowTransport
import Submission.OddOrder.MathlibSupport.PGroupNormalizer
import Submission.OddOrder.MathlibSupport.PrimeComplement
import Submission.OddOrder.MathlibSupport.SylowIntersectionNormalizer

/-!
# Bender--Glauberman Section 12: nonabelian uniqueness

This file ports `BGsection12.v: nonabelian_Uniqueness` and
`cent_der_sigma_uniq` (Theorem 12.13 and Corollary 12.14).  A nonabelian
`p`-subgroup of the minimal counterexample has a unique maximal overgroup.
The corollary applies this to a Sylow subgroup of the sigma core and also
identifies the unique maximal overgroup of the centralizer of a rank-one
subgroup lying in its derived subgroup.
-/

namespace Submission.OddOrder.BG.Section12

open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section05
open Submission.OddOrder.BG.Section06
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section09
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.MathlibSupport
open scoped Pointwise IsMulCommutative

noncomputable section

universe u

/-! ### Interface adapters for the preceding Section 12 block -/

/-- Source-shaped form of Corollary 12.10(a). -/
private theorem sigmaCompl_nilpotent_isMulCommutative
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M N : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hNM : N ≤ M)
    (hNcompl : IsPiNumber (sigmaPrimes M)ᶜ (Nat.card N))
    (hNnil : Group.IsNilpotent N) :
    IsMulCommutative N :=
  sigma'_nil_abelian hM hNM hNcompl hNnil

/-- Source-shaped form of Corollary 12.10(d). -/
private theorem normalizer_le_of_noncyclic_sigma
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M P : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hM : M ∈ minSimple_max_groups (G := G))
    (hpSigma : p ∈ sigmaPrimes M)
    (hPp : IsPGroup p P) (hPM : P ≤ M)
    (hPcyc : ¬ IsCyclic P) :
    Subgroup.normalizer (P : Set G) ≤ M :=
  norm_noncyclic_sigma hM hpSigma hPp hPM hPcyc

/-- Proposition 12.4 in the proposition-valued rank language used by this
port.  The adapter is kept local because the preceding module owns the
choice between a bundled and an unbundled rendering of its second clause. -/
private theorem p2Elem_mmax_context
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M A : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hM : M ∈ minSimple_max_groups (G := G))
    (hAM : A ≤ M)
    (hA : IsElementaryAbelianOfRank p 2 A) :
    Subgroup.centralizer (A : Set G) ≤ M ∧
      ((∀ A₀ : Subgroup G, RankOneLineIn p A A₀ →
          minSimple_max_groups_of (G := G)
              (Subgroup.normalizer (A₀ : Set G) : Set G) ≠ {M}) →
        p ∈ sigmaPrimes M ∧ alphaCore M = ⊥ ∧
          Group.IsNilpotent (sigmaCore M)) :=
  p2Elem_mmax hM hAM hA

/-! ### Small transport lemmas -/

/-- Commutativity descends to a subgroup. -/
private theorem isMulCommutative_of_le
    {K : Type u} [Group K] {A B : Subgroup K}
    (hAB : A ≤ B) (hB : IsMulCommutative B) :
    IsMulCommutative A := by
  apply isMulCommutative_iff.mpr
  intro x y
  apply Subtype.ext
  change (x : K) * (y : K) = (y : K) * (x : K)
  exact congrArg (fun z : B ↦ (z : K))
    (isMulCommutative_iff.mp hB
      ⟨(x : K), hAB x.property⟩ ⟨(y : K), hAB y.property⟩)

/-- A noncommutative subgroup forces every overgroup to be
noncommutative. -/
private theorem not_isMulCommutative_of_le
    {K : Type u} [Group K] {A B : Subgroup K}
    (hAB : A ≤ B) (hA : ¬ IsMulCommutative A) :
    ¬ IsMulCommutative B := by
  intro hB
  exact hA (isMulCommutative_of_le hAB hB)

/-- Local `subHall_Sylow` adapter. -/
private theorem exists_sylow_eq_map_of_sylow_hall
    {K : Type u} [Group K] [Finite K]
    {pi : Set ℕ} {p : ℕ} (hp : p.Prime)
    {A : Subgroup K} (hA : IsHall pi A) (hpPi : p ∈ pi)
    (P : Sylow p A) :
    ∃ Q : Sylow p K,
      (Q : Subgroup K) = (P : Subgroup A).map A.subtype := by
  letI : Fact p.Prime := ⟨hp⟩
  let S : Subgroup K := (P : Subgroup A).map A.subtype
  have hSp : IsPGroup p S := P.isPGroup'.map A.subtype
  have hpAindex : ¬ p ∣ A.index := by
    intro hpIndex
    exact hA.isPiNumber_index hp hpIndex hpPi
  have hpSindex : ¬ p ∣ S.index := by
    dsimp only [S]
    rw [Subgroup.index_map_subtype]
    exact hp.not_dvd_mul P.not_dvd_index hpAindex
  exact ⟨hSp.toSylow hpSindex, rfl⟩

/-- A `pi`-subgroup lies in a normal `pi`-Hall subgroup. -/
private theorem isPiNumber_le_normal_isHall
    {K : Type u} [Group K] [Finite K] {pi : Set ℕ}
    {N L : Subgroup K} (hNnormal : N.Normal)
    (hNHall : IsHall pi N) (hLpi : IsPiNumber pi (Nat.card L)) :
    L ≤ N := by
  letI : N.Normal := hNnormal
  have hcop : (Nat.card L).Coprime N.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpL hpIndex
    exact hNHall.isPiNumber_index hp hpIndex (hLpi hp hpL)
  intro x hxL
  let q : K →* K ⧸ N := QuotientGroup.mk' N
  have horderL : orderOf (q x) ∣ Nat.card L :=
    (orderOf_map_dvd q x).trans (L.orderOf_dvd_natCard hxL)
  have horderIndex : orderOf (q x) ∣ N.index := by
    simpa only [N.index_eq_card] using orderOf_dvd_natCard (q x)
  have horderOne : orderOf (q x) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horderL horderIndex
  exact (QuotientGroup.eq_one_iff x).mp
    (by simpa [q] using orderOf_eq_one_iff.mp horderOne)

/-- The image of a rank-three subgroup of a Sylow subgroup is a rank-three
subgroup of its ambient copy. -/
private theorem mapped_rank_three
    {K : Type u} [Group K] [Finite K]
    {p : ℕ} [Fact p.Prime] (P : Sylow p K)
    {E : Subgroup P} (hE : IsElementaryAbelianOfRank p 3 E) :
    HasElementaryAbelianRankAtLeast p 3 (P : Subgroup K) := by
  let F : Subgroup K := E.map (P : Subgroup K).subtype
  exact ⟨F, Subgroup.map_subtype_le E,
    hE.map_of_injective (P : Subgroup K).subtype
      (P : Subgroup K).subtype_injective⟩

/-- Conjugacy of Sylow subgroups inside a nested subgroup, transported to
the ambient group. -/
private theorem ambient_map_sylow_conj_of_smul_eq
    {G : Type u} [Group G] {M : Subgroup G} {S : Subgroup M}
    {p : ℕ} (P Q : Sylow p S) (y : S)
    (hy : y • P = Q) :
    (((Q : Subgroup S).map S.subtype).map M.subtype) =
      (((P : Subgroup S).map S.subtype).map M.subtype).map
        (MulAut.conj (M.subtype (S.subtype y))).toMonoidHom := by
  let i : S →* G := M.subtype.comp S.subtype
  have hQP : (Q : Subgroup S) =
      (P : Subgroup S).map (MulAut.conj y).toMonoidHom := by
    change (Q : Subgroup S) =
      MulAut.conj y • (P : Subgroup S)
    rw [← Sylow.coe_subgroup_smul, hy]
  calc
    (((Q : Subgroup S).map S.subtype).map M.subtype) =
        (Q : Subgroup S).map i :=
      Subgroup.map_map (Q : Subgroup S) M.subtype S.subtype
    _ = ((P : Subgroup S).map (MulAut.conj y).toMonoidHom).map i := by
      rw [← hQP]
    _ = (P : Subgroup S).map
        (i.comp (MulAut.conj y).toMonoidHom) :=
      Subgroup.map_map (P : Subgroup S) i
        (MulAut.conj y).toMonoidHom
    _ = (P : Subgroup S).map
        ((MulAut.conj (M.subtype (S.subtype y))).toMonoidHom.comp i) := by
      rfl
    _ = ((P : Subgroup S).map i).map
        (MulAut.conj (M.subtype (S.subtype y))).toMonoidHom := by
      rw [Subgroup.map_map]
    _ = (((P : Subgroup S).map S.subtype).map M.subtype).map
        (MulAut.conj (M.subtype (S.subtype y))).toMonoidHom := by
      simpa only [i] using congrArg
        (fun U : Subgroup G ↦ U.map
          (MulAut.conj (M.subtype (S.subtype y))).toMonoidHom)
        (Subgroup.map_map (P : Subgroup S) M.subtype S.subtype).symm

/-- The proposition-valued version of the `narrow_centP` invocation in
Corollary 12.14. -/
private theorem isNarrow_top_of_rankOne_centralizer_no_rankThree
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {P X : Subgroup G}
    (hPp : IsPGroup p P) (hodd : Odd (Nat.card P))
    (hXP : X ≤ P) (hX : IsElementaryAbelianOfRank p 1 X)
    (hCentRank : ¬ HasElementaryAbelianRankAtLeast p 3
      (centralizerWithin P X)) :
    IsNarrow p (⊤ : Subgroup P) := by
  intro hRankP
  have hRankP' : ∃ E : Subgroup P,
      IsElementaryAbelianOfRank p 3 E := by
    rcases hRankP with ⟨E, _hEtop, hE⟩
    exact ⟨E, hE⟩
  let XP : Subgroup P := X.subgroupOf P
  have hXPcard : Nat.card XP = p := by
    simpa [XP, natCard_subgroupOf_eq hXP] using hX.card_eq
  refine ((narrow_centP hPp hodd hRankP').mpr ⟨XP, hXPcard, ?_⟩) hRankP
  rintro ⟨F, hFC, hF⟩
  let FG : Subgroup G := F.map P.subtype
  have hFGP : FG ≤ P := Subgroup.map_subtype_le F
  have hFGcent : FG ≤ Subgroup.centralizer (X : Set G) := by
    rintro _ ⟨f, hf, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    let xP : P := ⟨x, hXP hx⟩
    have hxXP : xP ∈ XP := hx
    exact congrArg Subtype.val
      ((mem_centralizerWithin.mp (hFC hf)).2 xP hxXP)
  have hFG : IsElementaryAbelianOfRank p 3 FG :=
    hF.map_of_injective P.subtype P.subtype_injective
  exact hCentRank ⟨FG, le_inf hFGP hFGcent, hFG⟩

/-- If a Sylow subgroup complements a normal `p'`-subgroup, its
intersection with the derived subgroup is its own derived subgroup.  Only
the containment needed below is stated. -/
private theorem le_mapped_sylow_commutator_of_primeComplement
    {K : Type u} [Group K] [Finite K]
    {p : ℕ} [Fact p.Prime] {D X : Subgroup K} [D.Normal]
    (P : Sylow p K) (hD : IsPrimeComplement p D)
    (hXP : X ≤ (P : Subgroup K))
    (hXder : X ≤ _root_.commutator K) :
    X ≤ (_root_.commutator P).map (P : Subgroup K).subtype := by
  classical
  let q : K →* K ⧸ D := QuotientGroup.mk' D
  have hcomp : D.IsComplement' (P : Subgroup K) :=
    (hD.sylow_isComplement (Fact.out : p.Prime) P).symm
  have hPmapTop : (P : Subgroup K).map q = ⊤ := by
    have hmapped := congrArg (Subgroup.map q) hcomp.sup_eq_top
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self,
      bot_sup_eq, Subgroup.map_top_of_surjective q
        (QuotientGroup.mk'_surjective D)] at hmapped
    exact hmapped
  let f : P →* K ⧸ D := q.comp (P : Subgroup K).subtype
  have hfrange : f.range = (P : Subgroup K).map q := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.property, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hmapPder : (_root_.commutator P).map f =
      _root_.commutator (K ⧸ D) := by
    rw [map_commutator_eq, hfrange, hPmapTop]
    rfl
  have hmapKder : (_root_.commutator K).map q =
      _root_.commutator (K ⧸ D) := by
    rw [map_commutator_eq,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective D)]
    rfl
  have hPinj : Function.Injective f := by
    intro a b hab
    apply hcomp.quotientMap_injective_on_right le_rfl
    change QuotientGroup.mk' D (a : K) =
      QuotientGroup.mk' D (b : K) at hab
    exact hab
  intro x hx
  have hqx : q x ∈ _root_.commutator (K ⧸ D) := by
    rw [← hmapKder]
    exact ⟨x, hXder hx, rfl⟩
  rw [← hmapPder] at hqx
  rcases hqx with ⟨y, hy, hyx⟩
  let xP : P := ⟨x, hXP hx⟩
  have hyxP : y = xP := hPinj (by simpa [f, xP] using hyx)
  exact ⟨y, hy, congrArg Subtype.val hyxP⟩

/-- The direct-product conclusion of Theorem 5.3(d) rules out rank three
when a nontrivial rank-one subgroup is already contained in the derived
subgroup. -/
private theorem no_rank_three_of_narrow_rankOne_le_commutator
    {K : Type u} [Group K] [Finite K]
    {p : ℕ} [Fact p.Prime] {X : Subgroup K}
    (hKp : IsPGroup p K) (hodd : Odd (Nat.card K))
    (hNarrow : IsNarrow p (⊤ : Subgroup K))
    (hX : IsElementaryAbelianOfRank p 1 X)
    (hXder : X ≤ _root_.commutator K)
    (hCentRank : ¬ ∃ F : Subgroup K,
      F ≤ centralizerWithin (⊤ : Subgroup K) X ∧
        IsElementaryAbelianOfRank p 3 F) :
    ¬ ∃ E : Subgroup K, IsElementaryAbelianOfRank p 3 E := by
  intro hRank
  have hparts := narrow_cent_dprod hKp hodd hRank hNarrow
    (by simpa using hX.card_eq) hCentRank
  have hdis : Disjoint X (_root_.commutator K) := hparts.2.1
  have hXbot : X = ⊥ := by
    rw [← le_bot_iff, ← disjoint_iff.mp hdis]
    exact le_inf le_rfl hXder
  exact hX.ne_bot hXbot

/-- Adding a commuting abelian factor does not enlarge the derived
subgroup. -/
private theorem commutator_sup_le_left_commutator_of_centralizer
    {G : Type u} [Group G] {S C : Subgroup G}
    (hCcomm : IsMulCommutative C)
    (hCS : C ≤ Subgroup.centralizer (S : Set G)) :
    ⁅S ⊔ C, S ⊔ C⁆ ≤ ⁅S, S⁆ := by
  let J : Subgroup G := S ⊔ C
  let SJ : Subgroup J := S.subgroupOf J
  let CJ : Subgroup J := C.subgroupOf J
  let N : Subgroup J := ⁅SJ, SJ⁆
  have hSJCsup : SJ ⊔ CJ = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_self J
  have hCJcentSJ : CJ ≤ Subgroup.centralizer (SJ : Set J) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hCS hc)
      (s : G) hs
  have hSJcentCJ : SJ ≤ Subgroup.centralizer (CJ : Set J) :=
    Subgroup.le_centralizer_iff.mp hCJcentSJ
  have hCJcomm : IsMulCommutative CJ := by
    apply isMulCommutative_iff.mpr
    intro x y
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : C ↦ (z : G))
      (isMulCommutative_iff.mp hCcomm
        ⟨(x : G), x.property⟩ ⟨(y : G), y.property⟩)
  have hNleSJ : N ≤ SJ := by
    dsimp only [N]
    simpa using (Subgroup.commutator_le_sup SJ SJ)
  have hSJnormN : SJ ≤ Subgroup.normalizer (N : Set J) := by
    dsimp only [N]
    exact Subgroup.normalizer_commutator_ge_left SJ SJ
  have hCJnormN : CJ ≤ Subgroup.normalizer (N : Set J) := by
    have hCJcentN : CJ ≤ Subgroup.centralizer (N : Set J) :=
      hCJcentSJ.trans (Subgroup.centralizer_le hNleSJ)
    exact hCJcentN.trans (Subgroup.centralizer_le_normalizer (N : Set J))
  letI : N.Normal := Subgroup.normalizer_eq_top_iff.mp (by
    apply top_unique
    rw [← hSJCsup]
    exact sup_le hSJnormN hCJnormN)
  have hSCbot : ⁅SJ, CJ⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hSJcentCJ
  have hCCbot : ⁅CJ, CJ⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.le_centralizer_iff_isMulCommutative.mpr hCJcomm)
  have hSall : ⁅SJ, SJ ⊔ CJ⁆ ≤ N :=
    commutator_sup_le_of_normal le_rfl (hSCbot.le.trans bot_le)
  have hCall : ⁅CJ, SJ ⊔ CJ⁆ ≤ N :=
    commutator_sup_le_of_normal
      (by simpa [Subgroup.commutator_comm] using hSCbot.le.trans bot_le)
      (hCCbot.le.trans bot_le)
  have hall : ⁅SJ ⊔ CJ, SJ ⊔ CJ⁆ ≤ N := by
    rw [Subgroup.commutator_comm]
    exact commutator_sup_le_of_normal
      (by simpa [Subgroup.commutator_comm] using hSall)
      (by simpa [Subgroup.commutator_comm] using hCall)
  have hmapped := Subgroup.map_mono hall (f := J.subtype)
  simpa [J, SJ, CJ, N, Subgroup.map_commutator,
    Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le] using hmapped

/-- In the low-rank central-product description, the derived subgroup of
the Sylow subgroup lies in its center. -/
private theorem mapped_commutator_le_centerWithin_of_rankTwo_sylow
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hNoRank : ¬ ∃ E : Subgroup P,
      IsElementaryAbelianOfRank p 3 E)
    (hPnoncomm : ¬ IsMulCommutative P) :
    (_root_.commutator P).map (P : Subgroup G).subtype ≤
      centerWithin (P : Subgroup G) := by
  classical
  obtain ⟨Q, C, hQnoncomm, hQcard, _hQexp, hCQ, hQC,
      hCcyclic, _hOmega⟩ :=
    mFT_rank2_Sylow_cprod P hNoRank hPnoncomm
  have hQP : Q ≤ (P : Subgroup G) := le_sup_left.trans_eq hQC
  have hQp : IsPGroup p Q := P.isPGroup'.to_le hQP
  have hQextra : IsExtraspecial Q :=
    isExtraspecial_of_isPGroup_of_natCard_eq_prime_cube_of_not_isMulCommutative
      hQp hQcard hQnoncomm
  have hCcomm : IsMulCommutative C := by
    letI : IsCyclic C := hCcyclic
    infer_instance
  have hder : ⁅(P : Subgroup G), (P : Subgroup G)⁆ ≤
      ⁅Q, Q⁆ := by
    rw [← hQC]
    exact commutator_sup_le_left_commutator_of_centralizer
      hCcomm hCQ
  have hQQ : ⁅Q, Q⁆ =
      (_root_.commutator Q).map Q.subtype := by
    exact (Subgroup.map_subtype_commutator Q).symm
  have hQcenter : ⁅Q, Q⁆ =
      (Subgroup.center Q).map Q.subtype := by
    rw [hQQ, hQextra.toIsSpecial.commutator_eq_center]
  have hcenterP : (Subgroup.center Q).map Q.subtype ≤
      centerWithin (P : Subgroup G) := by
    rintro z ⟨zQ, hzQ, rfl⟩
    have hzQP : (zQ : G) ∈ (P : Subgroup G) := hQP zQ.property
    refine ⟨hzQP, ?_⟩
    intro x hx
    have hQcentZ : Q ≤
        Subgroup.centralizer ({(zQ : G)} : Set G) := by
      intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      exact congrArg Subtype.val
        (Subgroup.mem_center_iff.mp hzQ ⟨q, hq⟩).symm
    have hCcentZ : C ≤
        Subgroup.centralizer ({(zQ : G)} : Set G) := by
      intro c hc
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      exact Subgroup.mem_centralizer_iff.mp (hCQ hc)
        (zQ : G) zQ.property
    have hxCent : x ∈
        Subgroup.centralizer ({(zQ : G)} : Set G) := by
      rw [← hQC] at hx
      exact (sup_le hQcentZ hCcentZ) hx
    exact (Subgroup.mem_centralizer_iff.mp hxCent
      (zQ : G) (Set.mem_singleton _)).symm
  rw [Subgroup.map_subtype_commutator]
  exact hder.trans (hQcenter.le.trans hcenterP)

/-! ### The rank-two overlap argument -/

/-- The elementary-abelian rank-two subgroup selected in the low-rank
branch of `mFT_rank2_Sylow_cprod`. -/
private theorem exists_rankTwo_in_primeCube_component
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {Q : Subgroup G}
    (hQp : IsPGroup p Q)
    (hQcard : Nat.card Q = p ^ 3)
    (hQexp : Monoid.exponent Q ∣ p)
    (hQnoncomm : ¬ IsMulCommutative Q) :
    ∃ A : Subgroup G, A ≤ Q ∧
      IsElementaryAbelianOfRank p 2 A := by
  classical
  have hQextra : IsExtraspecial Q :=
    isExtraspecial_of_isPGroup_of_natCard_eq_prime_cube_of_not_isMulCommutative
      hQp hQcard hQnoncomm
  let ZQ : Subgroup Q := Subgroup.center Q
  let Z : Subgroup G := ZQ.map Q.subtype
  have hZcard : Nat.card Z = p := by
    dsimp only [Z, ZQ]
    rw [Subgroup.card_map_of_injective Q.subtype_injective]
    exact hQextra.center_card_eq hQp
  have hZrank : IsElementaryAbelianOfRank p 1 Z :=
    isElementaryAbelianOfRank_one_of_card_eq_prime hZcard
  have hZQ : Z ≤ Q := Subgroup.map_subtype_le ZQ
  have hZcenter : Z ≤ centerWithin Q := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨z.2, ?_⟩
    intro q hq
    exact congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hz ⟨q, hq⟩)
  have hZneQ : Z ≠ Q := by
    intro hZQeq
    apply hQnoncomm
    apply isMulCommutative_iff.mpr
    intro x y
    apply Subtype.ext
    have hxZ : (x : G) ∈ Z := by rw [hZQeq]; exact x.property
    change (x : G) * (y : G) = (y : G) * (x : G)
    exact ((hZcenter hxZ).2 (y : G) y.property).symm
  obtain ⟨x, hxQ, hxZ⟩ := SetLike.exists_of_lt
    (lt_of_le_of_ne hZQ hZneQ)
  have hxne : x ≠ 1 := fun hx ↦ hxZ (hx ▸ Z.one_mem)
  let xQ : Q := ⟨x, hxQ⟩
  have hxpowQ : xQ ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hQexp xQ
  have hxpow : x ^ p = 1 := congrArg Subtype.val hxpowQ
  have hxorder : orderOf x = p :=
    ((Nat.dvd_prime (Fact.out : p.Prime)).mp
      (orderOf_dvd_of_pow_eq_one hxpow)).resolve_left
        (by simpa [orderOf_eq_one_iff] using hxne)
  let X : Subgroup G := Subgroup.zpowers x
  have hXcard : Nat.card X = p := by
    dsimp only [X]
    rw [Nat.card_zpowers, hxorder]
  have hXrank : IsElementaryAbelianOfRank p 1 X :=
    isElementaryAbelianOfRank_one_of_card_eq_prime hXcard
  have hXQ : X ≤ Q := Subgroup.zpowers_le.mpr hxQ
  have hXZdis : Disjoint X Z := by
    rw [disjoint_iff]
    by_contra hne
    have hcardNe : Nat.card (X ⊓ Z : Subgroup G) ≠ 1 :=
      fun hc ↦ hne (Subgroup.card_eq_one.mp hc)
    have hcardDvd : Nat.card (X ⊓ Z : Subgroup G) ∣ p := by
      simpa [hZcard] using
        Subgroup.card_dvd_of_le (inf_le_right : X ⊓ Z ≤ Z)
    have hcard : Nat.card (X ⊓ Z : Subgroup G) = p :=
      ((Nat.dvd_prime (Fact.out : p.Prime)).mp hcardDvd).resolve_left
        hcardNe
    have hinf : X ⊓ Z = X :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard, hXcard])
    have hxInZ : x ∈ Z := by
      have hxInf : x ∈ X ⊓ Z := by
        rw [hinf]
        exact Subgroup.mem_zpowers x
      exact hxInf.2
    exact hxZ hxInZ
  have hXZcomm : ∀ x ∈ X, ∀ z ∈ Z, Commute x z := by
    intro y hy z hz
    exact (hZcenter hz).2 y (hXQ hy)
  let A : Subgroup G := X ⊔ Z
  have hA : IsElementaryAbelianOfRank p 2 A := by
    let XQ : Subgroup Q := X.subgroupOf Q
    let ZQ : Subgroup Q := Z.subgroupOf Q
    have hXQrank : IsElementaryAbelianOfRank p 1 XQ :=
      hXrank.subgroupOf hXQ
    have hZQrank : IsElementaryAbelianOfRank p 1 ZQ :=
      hZrank.subgroupOf hZQ
    have hXZdisQ : Disjoint XQ ZQ := by
      rw [disjoint_iff]
      apply le_antisymm ?_ bot_le
      intro q hq
      apply Subgroup.mem_bot.mpr
      apply Subtype.ext
      have hqbot : (q : G) ∈ (⊥ : Subgroup G) := by
        rw [← disjoint_iff.mp hXZdis]
        exact ⟨hq.1, hq.2⟩
      exact Subgroup.mem_bot.mp hqbot
    have hXZcommQ : ∀ x ∈ XQ, ∀ z ∈ ZQ, Commute x z := by
      intro x hx z hz
      apply Subtype.ext
      exact (hXZcomm (x : G) hx (z : G) hz).eq
    have hAQ : IsElementaryAbelianOfRank p 2 (XQ ⊔ ZQ) := by
      simpa using
        isElementaryAbelianOfRank_sup_of_disjoint_of_commute
          (H := XQ) (K := ZQ) hQp hXQrank hZQrank hXZdisQ hXZcommQ
    have hmapped := hAQ.map_of_injective Q.subtype Q.subtype_injective
    simpa [A, XQ, ZQ, Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hXQ,
      Subgroup.map_subgroupOf_eq_of_le hZQ] using hmapped
  exact ⟨A, sup_le hXQ hZQ, hA⟩

/-- Every Sylow subgroup of `M` has rank at least three at a prime in
`alpha(M)`.  This is repeated locally because the corresponding adapters in
Section 10 are intentionally private. -/
private theorem sylow_has_rank_three_of_mem_alpha
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hpAlpha : p ∈ alphaPrimes M) (P : Sylow p M) :
    HasElementaryAbelianRankAtLeast p 3
      ((P : Subgroup M).map M.subtype) := by
  classical
  rcases hpAlpha with ⟨_hp, E, hEM, hE⟩
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
  let CG : Subgroup G := C.map M.subtype
  exact ⟨CG, Subgroup.map_mono hCP,
    hC.map_of_injective M.subtype M.subtype_injective⟩

/-- A rank-two elementary subgroup is maximal among elementary subgroups
when its centralizer in the containing `p`-group has no rank-three
elementary subgroup. -/
private theorem isPMaxElem_of_no_rank_three_centralizerWithin
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {P A : Subgroup G}
    (hA : IsElementaryAbelianOfRank p 2 A) (hAP : A ≤ P)
    (hRank : ¬ HasElementaryAbelianRankAtLeast p 3
      (centralizerWithin P A)) :
    IsPMaxElem p P A := by
  refine ⟨⟨hAP, hA.toIsElementaryAbelianGroup⟩, ?_⟩
  intro E hE hAE
  apply le_antisymm ?_ hAE
  by_contra hnot
  have hAEl : A < E :=
    lt_of_le_of_ne hAE (fun hEq ↦ hnot hEq.ge)
  obtain ⟨n, hEcard⟩ := hE.2.isPGroup.exists_card_eq
  have hpowlt : p ^ 2 < p ^ n := by
    simpa only [hA.card_eq, hEcard] using
      natCard_subgroup_lt_of_lt hAEl
  have hn : 3 ≤ n := by
    by_contra hn3
    have hn2 : n ≤ 2 := by omega
    exact (not_lt_of_ge
      (Nat.pow_le_pow_right (Fact.out : p.Prime).pos hn2)) hpowlt
  have hpThreeLe : p ^ 3 ≤ Nat.card E := by
    rw [hEcard]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hn
  obtain ⟨F₀, hF₀card⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card
      (G := E) (n := 3) (Fact.out : p.Prime) hE.2.isPGroup
      hpThreeLe
  have hF₀ : IsElementaryAbelianOfRank p 3 F₀ := by
    letI : IsMulCommutative E := hE.2.commutative
    refine
      { isPGroup := hE.2.isPGroup.to_subgroup F₀
        commutative := by infer_instance
        pow_eq_one := ?_
        card_eq := hF₀card }
    intro x
    apply Subtype.ext
    exact hE.2.pow_eq_one (x : E)
  let F : Subgroup G := F₀.map E.subtype
  have hFE : F ≤ E := Subgroup.map_subtype_le F₀
  have hF : IsElementaryAbelianOfRank p 3 F :=
    hF₀.map_of_injective E.subtype E.subtype_injective
  have hEC : E ≤ centralizerWithin P A := by
    intro x hx
    refine mem_centralizerWithin.mpr ⟨hE.1 hx, ?_⟩
    intro a ha
    letI : IsMulCommutative E := hE.2.commutative
    exact congrArg Subtype.val
      (mul_comm (⟨a, hAE ha⟩ : E) (⟨x, hx⟩ : E))
  exact hRank ⟨F, hFE.trans hEC, hF⟩

/-- The product argument at the end of the low-rank branch.  It is useful
to keep all changes of ambient group in one place: Lemma 6.5(b) is applied
inside the solvable group `M`, whereas the desired normalizer containment
is in `G`. -/
private theorem normalizer_le_other_max_of_alpha_sup_inf
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M H Z : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hZM : Z ≤ M) (hZMH : Z ≤ M ⊓ H)
    (hcop : (Nat.card (alphaCore M)).Coprime (Nat.card Z))
    (hcent : centralizerWithin (alphaCore M) Z ≤ H)
    (hsup : alphaCore M ⊔ (M ⊓ H) = M)
    (hNZM : Subgroup.normalizer (Z : Set G) ≤ M) :
    Subgroup.normalizer (Z : Set G) ≤ H := by
  classical
  let A : Subgroup M := (alphaCore M).subgroupOf M
  let U : Subgroup M := (M ⊓ H).subgroupOf M
  let ZM : Subgroup M := Z.subgroupOf M
  letI : A.Normal := by
    simpa [A] using alphaCore_normal M
  letI : IsSolvable M := mmax_sol hM
  have hmapTop : (⊤ : Subgroup M).map M.subtype = M := by
    ext x
    constructor
    · rintro ⟨m, _hm, rfl⟩
      exact m.property
    · intro hx
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
  have hAU : A ⊔ U = ⊤ := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_sup, hmapTop]
    simpa [A, U, inf_comm,
      Subgroup.map_subgroupOf_eq_of_le (alphaCore_le M),
      Subgroup.map_subgroupOf_eq_of_le inf_le_left] using hsup
  have hZMU : ZM ≤ U := by
    intro z hz
    exact hZMH hz
  have hcopM : (Nat.card A).Coprime (Nat.card ZM) := by
    simpa [A, ZM, natCard_subgroupOf_eq (alphaCore_le M),
      natCard_subgroupOf_eq hZM] using hcop
  have hprod := pprod_norm_coprime_prod
    (G := M) (K := A) (U := U) (H := ZM)
    hAU hZMU hcopM
  intro x hx
  have hxM : x ∈ M := hNZM hx
  let xM : M := ⟨x, hxM⟩
  have hxNormM : xM ∈ Subgroup.normalizer (ZM : Set M) := by
    have hxSub : xM ∈
        (Subgroup.normalizer (Z : Set G)).subgroupOf M := hx
    rwa [Subgroup.subgroupOf_normalizer_eq hZM] at hxSub
  have hxProd : xM ∈
      ((A ⊓ Subgroup.centralizer (ZM : Set M) : Subgroup M) : Set M) *
        ((U ⊓ Subgroup.normalizer (ZM : Set M) : Subgroup M) : Set M) := by
    rw [hprod]
    exact hxNormM
  rcases hxProd with ⟨a, ha, b, hb, hab⟩
  have haCent : (a : G) ∈ centralizerWithin (alphaCore M) Z := by
    refine ⟨ha.1, ?_⟩
    intro z hz
    let zM : M := ⟨z, hZM hz⟩
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp ha.2 zM hz)
  have haH : (a : G) ∈ H := hcent haCent
  have hbH : (b : G) ∈ H := hb.1.2
  have hxEq : x = (a : G) * (b : G) :=
    (congrArg Subtype.val hab).symm
  rw [hxEq]
  exact H.mul_mem haH hbH

/-- The quotient-action invocation in the source proof.  The preceding
Section 1 coprime-action API packages the passage from the extraspecial
component `Q` to the noncyclic abelian actor `Q / Z(Q)`.  Its fixed-point
subgroups lie in `H` by Proposition 12.4 applied to rank-two elementary
subgroups of `Q`. -/
private theorem alphaCore_center_centralizer_le_other_max
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M H Q C : Subgroup G} {p : ℕ} [Fact p.Prime]
    (P : Sylow p G)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hH : H ∈ minSimple_max_groups (G := G))
    (hPM : (P : Subgroup G) ≤ M)
    (hPH : (P : Subgroup G) ≤ H)
    (hNoRank : ¬ ∃ E : Subgroup P,
      IsElementaryAbelianOfRank p 3 E)
    (hQP : Q ≤ (P : Subgroup G)) (hQp : IsPGroup p Q)
    (hQnoncomm : ¬ IsMulCommutative Q)
    (hQcard : Nat.card Q = p ^ 3)
    (hQexp : Monoid.exponent Q ∣ p)
    (hCQ : C ≤ Subgroup.centralizer (Q : Set G))
    (hQC : Q ⊔ C = (P : Subgroup G)) :
    centralizerWithin (alphaCore M)
      (omegaOneCenterAmbient p (P : Subgroup G)) ≤ H := by
  classical
  let Z : Subgroup G := omegaOneCenterAmbient p (P : Subgroup G)
  change centralizerWithin (alphaCore M) Z ≤ H
  have hQextra : IsExtraspecial Q :=
    isExtraspecial_of_isPGroup_of_natCard_eq_prime_cube_of_not_isMulCommutative
      hQp hQcard hQnoncomm
  have hQM : Q ≤ M := hQP.trans hPM
  have hQH : Q ≤ H := hQP.trans hPH
  have hpNotAlpha : p ∉ alphaPrimes M := by
    intro hpAlpha
    let PM : Sylow p M := P.subtype hPM
    have hPMmap : (PM : Subgroup M).map M.subtype =
        (P : Subgroup G) := by
      dsimp only [PM]
      rw [Sylow.coe_subtype,
        Subgroup.map_subgroupOf_eq_of_le hPM]
    have hNoM : ¬ ∃ E : Subgroup M,
        IsElementaryAbelianOfRank p 3 E :=
      no_elementaryAbelian_rank_three_of_sylow_map_le PM
        (by rw [hPMmap]) hNoRank
    rcases hpAlpha.2 with ⟨E, hEM, hE⟩
    exact hNoM ⟨E.subgroupOf M, hE.subgroupOf hEM⟩
  have hcorePcop :
      (Nat.card (alphaCore M)).Coprime (Nat.card (P : Subgroup G)) :=
    (alphaCore_isPiNumber M).coprime_compl
      (P.isPGroup'.isPiNumber_natCard hpNotAlpha)
  have hcoreQcop :
      (Nat.card (alphaCore M)).Coprime (Nat.card Q) :=
    hcorePcop.coprime_dvd_right (Subgroup.card_dvd_of_le hQP)
  have hQnormCore :
      Q ≤ Subgroup.normalizer (alphaCore M : Set G) :=
    hQM.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (alphaCore_le M)).mp (alphaCore_normal M))
  have hfixed : ∀ A : Subgroup G, A ≤ Q →
      IsElementaryAbelianOfRank p 2 A →
      centralizerWithin (alphaCore M) A ≤ H := by
    intro A hAQ hA
    exact inf_le_right.trans
      (p2Elem_mmax_context hH (hAQ.trans hQH) hA).1
  exact
    le_of_rankTwo_centralizers_of_coprime_extraspecial_action
      (P := P) (Q := Q) (C := C) (Y := alphaCore M) (K := H)
      hQextra hQexp hNoRank hQP hCQ hQC hQnormCore hcoreQcop
      (mFT_sol (lt_of_le_of_lt
        ((centralizerWithin_le_left (alphaCore M) Z).trans
          (alphaCore_le M)) (mmax_proper hM)))
      hfixed

/-- The low-rank overlap step of Theorem 12.13. -/
private theorem rankTwo_nonabelian_sylow_maximal_eq
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    {M H : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hH : H ∈ minSimple_max_groups (G := G))
    (hPM : (P : Subgroup G) ≤ M)
    (hPH : (P : Subgroup G) ≤ H)
    (hNP : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ H ⊓ M)
    (hNoRank : ¬ ∃ E : Subgroup P,
      IsElementaryAbelianOfRank p 3 E)
    (hPnoncomm : ¬ IsMulCommutative P) :
    H = M := by
  classical
  by_contra hneHM
  obtain ⟨Q, C, hQnoncomm, hQcard, hQexp, hCQ, hQC,
      _hCcyclic, _hOmega⟩ :=
    mFT_rank2_Sylow_cprod P hNoRank hPnoncomm
  have hQP : Q ≤ (P : Subgroup G) :=
    le_sup_left.trans_eq hQC
  have hQp : IsPGroup p Q := P.isPGroup'.to_le hQP
  obtain ⟨A, hAQ, hA⟩ :=
    exists_rankTwo_in_primeCube_component
      hQp hQcard hQexp hQnoncomm
  have hAP : A ≤ (P : Subgroup G) := hAQ.trans hQP
  have hNoGlobal : ¬ ∃ E : Subgroup G,
      IsElementaryAbelianOfRank p 3 E := by
    rintro ⟨E, hE⟩
    obtain ⟨R, hER⟩ := hE.isPGroup.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R P
    let D : Subgroup G := E.map (MulAut.conj g).toMonoidHom
    have hRmap : (R : Subgroup G).map
        (MulAut.conj g).toMonoidHom = (P : Subgroup G) := by
      change MulAut.conj g • (R : Subgroup G) = (P : Subgroup G)
      rw [← Sylow.coe_subgroup_smul, hg]
    have hDP : D ≤ (P : Subgroup G) :=
      (Subgroup.map_mono hER).trans_eq hRmap
    have hD : IsElementaryAbelianOfRank p 3 D :=
      hE.map_of_injective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective
    exact hNoRank ⟨D.subgroupOf P, hD.subgroupOf hDP⟩
  have hNoCent : ¬ HasElementaryAbelianRankAtLeast p 3
      (centralizerWithin (⊤ : Subgroup G) A) := by
    rintro ⟨E, _hEC, hE⟩
    exact hNoGlobal ⟨E, hE⟩
  have hAmax : IsPMaxElem p (⊤ : Subgroup G) A :=
    isPMaxElem_of_no_rank_three_centralizerWithin hA le_top hNoCent
  obtain ⟨hZ, _hdecomp, htrans⟩ :=
    basic_p2maxElem_structure hA hAmax P.isPGroup' hAP hPnoncomm
  let Z : Subgroup G := omegaOneCenterAmbient p (P : Subgroup G)

  have hchoose :
      (∀ A₀ : Subgroup G, RankOneLineIn p A A₀ → A₀ ≠ Z →
        minSimple_max_groups_of (G := G)
          (Subgroup.normalizer (A₀ : Set G) : Set G) ≠ {M}) ∨
      (∀ A₀ : Subgroup G, RankOneLineIn p A A₀ → A₀ ≠ Z →
        minSimple_max_groups_of (G := G)
          (Subgroup.normalizer (A₀ : Set G) : Set G) ≠ {H}) := by
    by_contra hnot
    push_neg at hnot
    rcases hnot with ⟨⟨A₀, hA₀, hA₀Z, hA₀M⟩,
      ⟨A₁, hA₁, hA₁Z, hA₁H⟩⟩
    obtain ⟨x, hx, hA₁eq⟩ :=
      htrans A₀ A₁ hA₀ hA₀Z hA₁ hA₁Z
    let e : G ≃* G := MulAut.conj x⁻¹
    have hxM : x ∈ M := hPM hx.1
    have hMe : M.map e.toMonoidHom = M := by
      change e • M = M
      exact Subgroup.conj_smul_eq_self_of_mem (M.inv_mem hxM)
    have htransport := def_uniq_mmaxJ e hA₀M
    have hNe :
        (Subgroup.normalizer (A₀ : Set G)).map e.toMonoidHom =
          Subgroup.normalizer (A₁ : Set G) := by
      rw [Subgroup.map_equiv_normalizer_eq, hA₁eq]
    rw [hNe, hMe, hA₁H] at htransport
    exact hneHM (Set.singleton_injective htransport)

  have himpossible
      (L K : Subgroup G)
      (hL : L ∈ minSimple_max_groups (G := G))
      (hK : K ∈ minSimple_max_groups (G := G))
      (hPL : (P : Subgroup G) ≤ L)
      (hPK : (P : Subgroup G) ≤ K)
      (hNPKL : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ K ⊓ L)
      (hne : K ≠ L)
      (houtside : ∀ A₀ : Subgroup G, RankOneLineIn p A A₀ →
        A₀ ≠ Z →
        minSimple_max_groups_of (G := G)
          (Subgroup.normalizer (A₀ : Set G) : Set G) ≠ {L}) :
      False := by
    have hcenterK : centralizerWithin (alphaCore L) Z ≤ K := by
      simpa only [Z] using
        alphaCore_center_centralizer_le_other_max P hL hK hPL hPK
          hNoRank hQP hQp hQnoncomm hQcard hQexp hCQ hQC
    have hpNotAlpha : p ∉ alphaPrimes L := by
      intro hpAlpha
      let PL : Sylow p L := P.subtype hPL
      have hPLmap : (PL : Subgroup L).map L.subtype =
          (P : Subgroup G) := by
        dsimp only [PL]
        rw [Sylow.coe_subtype,
          Subgroup.map_subgroupOf_eq_of_le hPL]
      have hNoL :=
        no_elementaryAbelian_rank_three_of_sylow_map_le PL
          (by rw [hPLmap]) hNoRank
      rcases hpAlpha.2 with ⟨E, hEL, hE⟩
      exact hNoL ⟨E.subgroupOf L, hE.subgroupOf hEL⟩
    have hcoreZcop :
        (Nat.card (alphaCore L)).Coprime (Nat.card Z) :=
      (alphaCore_isPiNumber L).coprime_compl
        (hZ.isPGroup.isPiNumber_natCard hpNotAlpha)
    obtain ⟨hBetaSup, hAlphaBeta⟩ :=
      nonuniq_norm_Sylow_pprod hL hK hne P hNPKL
    have hAlphaSup : alphaCore L ⊔ (K ⊓ L) = L := by
      simpa [alphaCore, betaCore, hAlphaBeta] using hBetaSup
    have hcoreNe : alphaCore L ≠ ⊥ := by
      intro hbot
      have hKL : K ⊓ L = L := by
        simpa [hbot] using hAlphaSup
      have hLK : L ≤ K := by
        rw [← hKL]
        exact inf_le_left
      exact hne (eq_mmax hL hK hLK).symm
    have hNZneq :
        minSimple_max_groups_of (G := G)
          (Subgroup.normalizer (Z : Set G) : Set G) ≠ {L} := by
      intro hNZ
      have hNZL : Subgroup.normalizer (Z : Set G) ≤ L :=
        (mem_uniq_mmax hNZ).2
      have hZP : Z ≤ (P : Subgroup G) :=
        (omegaOneCenterAmbient_le_centerWithin p (P : Subgroup G)).trans
          (centralizerWithin_le_left (P : Subgroup G) (P : Subgroup G))
      have hZKL : Z ≤ L ⊓ K :=
        le_inf (hZP.trans hPL) (hZP.trans hPK)
      have hNZK : Subgroup.normalizer (Z : Set G) ≤ K :=
        normalizer_le_other_max_of_alpha_sup_inf hL
          (hZP.trans hPL) hZKL
          hcoreZcop hcenterK (by simpa [inf_comm] using hAlphaSup) hNZL
      exact hne (eq_uniq_mmax hNZ hK hNZK)
    have hallLines : ∀ A₀ : Subgroup G, RankOneLineIn p A A₀ →
        minSimple_max_groups_of (G := G)
          (Subgroup.normalizer (A₀ : Set G) : Set G) ≠ {L} := by
      intro A₀ hA₀
      by_cases hA₀Z : A₀ = Z
      · simpa [hA₀Z] using hNZneq
      · exact houtside A₀ hA₀ hA₀Z
    have hctx := p2Elem_mmax_context hL (hAP.trans hPL) hA
    have hcoreBot := (hctx.2 hallLines).2.1
    exact hcoreNe hcoreBot

  rcases hchoose with hMoutside | hHoutside
  · exact himpossible M H hM hH hPM hPH hNP hneHM hMoutside
  · exact himpossible H M hH hM hPH hPM
      (by simpa [inf_comm] using hNP) (Ne.symm hneHM)
      hHoutside

/-! ### Theorem 12.13 -/

/-- `BGsection12.v: nonabelian_Uniqueness` (Bender--Glauberman
Theorem 12.13). -/
theorem nonabelian_Uniqueness
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} [Fact p.Prime] {P : Subgroup G}
    (hPp : IsPGroup p P)
    (hPnoncomm : ¬ IsMulCommutative P) :
    P ∈ minSimple_uniq_max_groups (G := G) := by
  classical
  obtain ⟨M, hM, hPM⟩ :=
    mmax_exists P (mFT_pgroup_proper P hPp)
  have hpSigma (L : Subgroup G)
      (hL : L ∈ minSimple_max_groups (G := G))
      (hPL : P ≤ L) :
      p ∈ sigmaPrimes L := by
    by_contra hpNot
    have hcompl : IsPiNumber (sigmaPrimes L)ᶜ (Nat.card P) :=
      hPp.isPiNumber_natCard hpNot
    exact hPnoncomm
      (sigmaCompl_nilpotent_isMulCommutative hL hPL hcompl
        hPp.isNilpotent)
  have hpM : p ∈ sigmaPrimes M := hpSigma M hM hPM
  apply (uniq_mmax_subset1 hM hPM).mpr
  intro H hHfamily
  have hH : H ∈ minSimple_max_groups (G := G) := hHfamily.1
  have hPH : P ≤ H := hHfamily.2
  have hpH : p ∈ sigmaPrimes H := hpSigma H hH hPH
  let J : Subgroup G := M ⊓ H
  let PJ : Subgroup J := P.subgroupOf J
  have hPJp : IsPGroup p PJ := by
    exact hPp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (le_inf hPM hPH)).symm
  obtain ⟨R, hPJR⟩ := hPJp.exists_le_sylow
  let RG : Subgroup G := (R : Subgroup J).map J.subtype
  have hPRG : P ≤ RG := by
    change P ≤ (R : Subgroup J).map J.subtype
    rw [← Subgroup.map_subgroupOf_eq_of_le (le_inf hPM hPH)]
    exact Subgroup.map_mono hPJR
  have hRGM : RG ≤ M := by
    exact Subgroup.map_subtype_le (R : Subgroup J) |>.trans inf_le_left
  have hRGH : RG ≤ H := by
    exact Subgroup.map_subtype_le (R : Subgroup J) |>.trans inf_le_right
  have hRGp : IsPGroup p RG := R.isPGroup'.map J.subtype
  have hRGnoncomm : ¬ IsMulCommutative RG :=
    not_isMulCommutative_of_le hPRG hPnoncomm
  have hRGnoncyclic : ¬ IsCyclic RG := by
    intro hcyclic
    letI : IsCyclic RG := hcyclic
    exact hRGnoncomm (by infer_instance)
  have hNRGM : Subgroup.normalizer (RG : Set G) ≤ M :=
    normalizer_le_of_noncyclic_sigma hM hpM hRGp hRGM hRGnoncyclic
  have hNRGH : Subgroup.normalizer (RG : Set G) ≤ H :=
    normalizer_le_of_noncyclic_sigma hH hpH hRGp hRGH hRGnoncyclic
  have hNRG : Subgroup.normalizer (RG : Set G) ≤ H ⊓ M :=
    le_inf hNRGH hNRGM
  obtain ⟨PM, hPMRG⟩ :=
    exists_sylow_map_eq_of_sylow_inf_of_normalizer_le
      M H R hNRGH
  obtain ⟨S, hSRG⟩ := sigma_Sylow_G hM hpM PM
  have hRG_eq : (S : Subgroup G) = RG := by
    rw [hSRG, ambientSylow, hPMRG]
  have hSM : (S : Subgroup G) ≤ M := by
    rw [hRG_eq]
    exact hRGM
  have hSH : (S : Subgroup G) ≤ H := by
    rw [hRG_eq]
    exact hRGH
  by_cases hRank : ∃ E : Subgroup S,
      IsElementaryAbelianOfRank p 3 E
  · have hRankSG : HasElementaryAbelianRankAtLeast p 3
        (S : Subgroup G) := by
      rcases hRank with ⟨E, hE⟩
      exact mapped_rank_three S hE
    have hSuniq : (S : Subgroup G) ∈
        minSimple_uniq_max_groups (G := G) :=
      rank3_Uniqueness
        (mFT_pgroup_proper (S : Subgroup G) S.isPGroup')
        ⟨p, Fact.out, hRankSG⟩
    have hSfamily := def_uniq_mmax hSuniq hM hSM
    have hEq : H = M := eq_uniq_mmax hSfamily hH hSH
    simpa [hEq]
  · have hSnoncomm : ¬ IsMulCommutative S := by
      intro hcomm
      apply hRGnoncomm
      rw [← hRG_eq]
      exact hcomm
    have hEq : H = M :=
      rankTwo_nonabelian_sylow_maximal_eq S hM hH hSM hSH
        (by simpa [hRG_eq] using hNRG) hRank hSnoncomm
    simpa [hEq]

/-! ### Corollary 12.14 -/

/-- `BGsection12.v: cent_der_sigma_uniq` (Bender--Glauberman
Corollary 12.14).  The redundant source assumption `p ∈ sigma(M)` is
derived from the displayed disjunction. -/
theorem cent_der_sigma_uniq
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M X : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hM : M ∈ minSimple_max_groups (G := G))
    (hXM : X ≤ M)
    (hX : IsElementaryAbelianOfRank p 1 X)
    (hcase : p ∈ betaPrimes M ∨
      X ≤ (_root_.commutator (sigmaCore M)).map
        (sigmaCore M).subtype) :
    minSimple_max_groups_of (G := G)
        (Subgroup.centralizer (X : Set G) : Set G) = {M} ∧
      ∀ P : Sylow p ((sigmaCore M).subgroupOf M),
        minSimple_max_groups_of (G := G)
          ((((P : Subgroup ((sigmaCore M).subgroupOf M)).map
              ((sigmaCore M).subgroupOf M).subtype).map M.subtype :
            Subgroup G) : Set G) = {M} := by
  classical
  let S : Subgroup M := (sigmaCore M).subgroupOf M
  let XM : Subgroup M := X.subgroupOf M
  have hcase' := hcase
  have hXMp : IsPGroup p XM :=
    hX.isPGroup.of_equiv
      (Subgroup.subgroupOfEquivOfLe hXM).symm
  have hpSigma : p ∈ sigmaPrimes M := by
    rcases hcase with hpBeta | hXder
    · exact beta_sub_sigma hM hpBeta
    · have hpX : p ∣ Nat.card X := by
        rw [hX.card_eq]
        exact dvd_pow_self p (by omega)
      have hXsigma : X ≤ sigmaCore M :=
        hXder.trans (Subgroup.map_subtype_le (_root_.commutator
          (sigmaCore M)))
      exact sigmaCore_isPiNumber M Fact.out
        (hpX.trans (Subgroup.card_dvd_of_le hXsigma))
  have hSHall : IsHall (sigmaPrimes M) S := by
    simpa [S] using Msigma_Hall hM
  have hSnormal : S.Normal := by
    simpa [S] using sigmaCore_normal M
  have hXMS : XM ≤ S :=
    isPiNumber_le_normal_isHall hSnormal hSHall
      (hXMp.isPiNumber_natCard hpSigma)
  let XS : Subgroup S := XM.subgroupOf S
  have hXSp : IsPGroup p XS :=
    hXMp.of_equiv (Subgroup.subgroupOfEquivOfLe hXMS).symm
  obtain ⟨PS, hXSPS⟩ := hXSp.exists_le_sylow
  obtain ⟨PM, hPMPS⟩ := exists_sylow_eq_map_of_sylow_hall
    (Fact.out : p.Prime) hSHall hpSigma PS
  let PG : Subgroup G := (PM : Subgroup M).map M.subtype
  have hPGM : PG ≤ M := Subgroup.map_subtype_le (PM : Subgroup M)
  have hXMPS : XM ≤ (PS : Subgroup S).map S.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hXMS]
    exact Subgroup.map_mono hXSPS
  have hXPG : X ≤ PG := by
    calc
      X = XM.map M.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hXM).symm
      _ ≤ (((PS : Subgroup S).map S.subtype).map M.subtype) :=
        Subgroup.map_mono hXMPS
      _ = PG := by rw [← hPMPS]
  have hPGp : IsPGroup p PG := PM.isPGroup'.map M.subtype
  obtain ⟨T, hTPG⟩ := sigma_Sylow_G hM hpSigma PM
  have hTG : (T : Subgroup G) = PG := by
    simpa [PG, ambientSylow] using hTPG
  let CP : Subgroup G := centralizerWithin PG X
  have hCPp : IsPGroup p CP :=
    hPGp.to_le (centralizerWithin_le_left PG X)
  have hCPM : CP ≤ M :=
    (centralizerWithin_le_left PG X).trans hPGM
  have hCPCX : CP ≤ Subgroup.centralizer (X : Set G) := inf_le_right
  by_cases hCPRank : HasElementaryAbelianRankAtLeast p 3 CP
  · have hCPuniq : CP ∈ minSimple_uniq_max_groups (G := G) :=
      rank3_Uniqueness (mFT_pgroup_proper CP hCPp)
        ⟨p, Fact.out, hCPRank⟩
    have hCPfamily := def_uniq_mmax hCPuniq hM hCPM
    have hCentProper : Subgroup.centralizer (X : Set G) < ⊤ :=
      mFT_cent_proper X hX.ne_bot
    have hPGproper : PG < ⊤ := mFT_pgroup_proper PG hPGp
    have hCentFamily :=
      def_uniq_mmaxS hCPCX hCentProper hCPfamily
    have hPGFamily :=
      def_uniq_mmaxS (centralizerWithin_le_left PG X)
        hPGproper hCPfamily
    refine ⟨hCentFamily, ?_⟩
    intro PY
    obtain ⟨y, hy⟩ := MulAction.exists_smul_eq S PS PY
    let yG : G := M.subtype (S.subtype y)
    let e : G ≃* G := MulAut.conj yG
    have hyM : yG ∈ M := (S.subtype y).property
    have hMe : M.map e.toMonoidHom = M := by
      change e • M = M
      exact Subgroup.conj_smul_eq_self_of_mem hyM
    have hPYmap :
        (((PY : Subgroup S).map S.subtype).map M.subtype) =
          PG.map e.toMonoidHom := by
      simpa [e, yG, PG, ← hPMPS] using
        (ambient_map_sylow_conj_of_smul_eq PS PY y hy)
    have htransport := def_uniq_mmaxJ e hPGFamily
    rw [← hPYmap, hMe] at htransport
    exact htransport
  · have hNarrowPG : IsNarrow p (⊤ : Subgroup PG) :=
      isNarrow_top_of_rankOne_centralizer_no_rankThree
        hPGp (mFT_odd PG) hXPG hX hCPRank
    let ePM : PM ≃* PG :=
      (PM : Subgroup M).equivMapOfInjective
        M.subtype M.subtype_injective
    have hNarrowPM : IsNarrow p (⊤ : Subgroup PM) := by
      have hiff := isNarrow_map_mulEquiv_iff (p := p) ePM
        (⊤ : Subgroup PM)
      apply hiff.mp
      simpa [ePM, PG] using hNarrowPG
    have hpNotBeta : p ∉ betaPrimes M := by
      intro hpBeta
      exact hpBeta.2 PM hNarrowPM
    have hXder : X ≤
        (_root_.commutator (sigmaCore M)).map
          (sigmaCore M).subtype :=
      hcase'.resolve_left hpNotBeta
    let f : S →* G := M.subtype.comp S.subtype
    have hf : Function.Injective f :=
      M.subtype_injective.comp S.subtype_injective
    have hXSmap : XS.map f = X := by
      change XS.map (M.subtype.comp S.subtype) = X
      calc
        XS.map (M.subtype.comp S.subtype) =
            (XS.map S.subtype).map M.subtype := by
          rw [Subgroup.map_map]
        _ = XM.map M.subtype := by
          rw [Subgroup.map_subgroupOf_eq_of_le hXMS]
        _ = X := Subgroup.map_subgroupOf_eq_of_le hXM
    have hSderMap : (_root_.commutator S).map f =
        (_root_.commutator (sigmaCore M)).map
          (sigmaCore M).subtype := by
      change (_root_.commutator S).map
        (M.subtype.comp S.subtype) = _
      calc
        (_root_.commutator S).map (M.subtype.comp S.subtype) =
            ((_root_.commutator S).map S.subtype).map M.subtype := by
          rw [Subgroup.map_map]
        _ = ⁅(S : Subgroup M), (S : Subgroup M)⁆.map M.subtype := by
          rw [Subgroup.map_subtype_commutator]
        _ = ⁅(S : Subgroup M).map M.subtype,
              (S : Subgroup M).map M.subtype⁆ := by
          rw [Subgroup.map_commutator]
        _ = ⁅sigmaCore M, sigmaCore M⁆ := by
          rw [Subgroup.map_subgroupOf_eq_of_le (sigmaCore_le M)]
        _ = (_root_.commutator (sigmaCore M)).map
              (sigmaCore M).subtype := by
          rw [Subgroup.map_subtype_commutator]
    have hXSder : XS ≤ _root_.commutator S := by
      apply (Subgroup.map_le_map_iff_of_injective hf).mp
      rw [hXSmap, hSderMap]
      exact hXder
    let D : Subgroup S := pPrimeCore p S
    have hDcompl : IsPrimeComplement p D := by
      simpa [S, D] using (beta_max_pdiv hM hpNotBeta).2.1
    letI : D.Normal := by
      dsimp only [D]
      infer_instance
    have hXScomm :=
      le_mapped_sylow_commutator_of_primeComplement
        PS hDcompl hXSPS hXSder
    have hmapped₁ := Subgroup.map_mono hXScomm (f := S.subtype)
    have hmapped₂ := Subgroup.map_mono hmapped₁ (f := M.subtype)
    have hXcommPG : X ≤ ⁅PG, PG⁆ := by
      simpa [hXSmap, f, Subgroup.map_map,
        Subgroup.map_subtype_commutator, Subgroup.map_commutator,
        hPMPS, PG] using hmapped₂
    let XP : Subgroup PG := X.subgroupOf PG
    have hXPrank : IsElementaryAbelianOfRank p 1 XP :=
      hX.subgroupOf hXPG
    have hXPder : XP ≤ _root_.commutator PG := by
      apply (Subgroup.map_le_map_iff_of_injective
        PG.subtype_injective).mp
      rw [Subgroup.map_subgroupOf_eq_of_le hXPG,
        Subgroup.map_subtype_commutator]
      exact hXcommPG
    have hCentRankPG : ¬ ∃ F : Subgroup PG,
        F ≤ centralizerWithin (⊤ : Subgroup PG) XP ∧
          IsElementaryAbelianOfRank p 3 F := by
      rintro ⟨F, hFC, hF⟩
      let FG : Subgroup G := F.map PG.subtype
      have hFGP : FG ≤ PG := Subgroup.map_subtype_le F
      have hFGcent : FG ≤ Subgroup.centralizer (X : Set G) := by
        rintro _ ⟨a, ha, rfl⟩
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        let xP : PG := ⟨x, hXPG hx⟩
        have hxXP : xP ∈ XP := hx
        exact congrArg Subtype.val
          ((mem_centralizerWithin.mp (hFC ha)).2 xP hxXP)
      exact hCPRank ⟨FG, le_inf hFGP hFGcent,
        hF.map_of_injective PG.subtype PG.subtype_injective⟩
    have hNoRankPG : ¬ ∃ E : Subgroup PG,
        IsElementaryAbelianOfRank p 3 E :=
      no_rank_three_of_narrow_rankOne_le_commutator
        hPGp (mFT_odd PG) hNarrowPG hXPrank hXPder hCentRankPG
    have hPGnoncomm : ¬ IsMulCommutative PG := by
      intro hcomm
      letI : IsMulCommutative PG := hcomm
      have hXPbot : XP = ⊥ := by
        apply le_antisymm _ bot_le
        rw [_root_.commutator_eq_bot PG] at hXPder
        exact hXPder
      exact hXPrank.ne_bot hXPbot
    let eT : T ≃* PG := MulEquiv.subgroupCongr hTG
    have hNoRankT : ¬ ∃ E : Subgroup T,
        IsElementaryAbelianOfRank p 3 E := by
      rintro ⟨E, hE⟩
      let F : Subgroup PG := E.map eT.toMonoidHom
      exact hNoRankPG ⟨F,
        hE.map_of_injective eT.toMonoidHom eT.injective⟩
    have hTnoncomm : ¬ IsMulCommutative T := by
      intro hcomm
      apply hPGnoncomm
      apply isMulCommutative_iff.mpr
      intro x y
      have hxy := isMulCommutative_iff.mp hcomm
        (eT.symm x) (eT.symm y)
      exact eT.symm.injective (by simpa using hxy)
    have hXderT : X ≤
        (_root_.commutator T).map (T : Subgroup G).subtype := by
      rw [Subgroup.map_subtype_commutator, hTG]
      exact hXcommPG
    have hXcenter : X ≤ centerWithin PG := by
      have hcenterT :=
        mapped_commutator_le_centerWithin_of_rankTwo_sylow
          T hNoRankT hTnoncomm
      have hcenterEq : centerWithin (T : Subgroup G) =
          centerWithin PG := congrArg centerWithin hTG
      exact hXderT.trans (hcenterT.trans_eq hcenterEq)
    have hPGuniq : PG ∈ minSimple_uniq_max_groups (G := G) :=
      nonabelian_Uniqueness hPGp hPGnoncomm
    have hPGFamily := def_uniq_mmax hPGuniq hM hPGM
    have hXcentPG : X ≤ Subgroup.centralizer (PG : Set G) :=
      hXcenter.trans inf_le_right
    have hPGcentX : PG ≤ Subgroup.centralizer (X : Set G) :=
      Subgroup.le_centralizer_iff.mp hXcentPG
    have hCentFamily := def_uniq_mmaxS hPGcentX
      (mFT_cent_proper X hX.ne_bot) hPGFamily
    refine ⟨hCentFamily, ?_⟩
    intro PY
    obtain ⟨y, hy⟩ := MulAction.exists_smul_eq S PS PY
    let yG : G := M.subtype (S.subtype y)
    let e : G ≃* G := MulAut.conj yG
    have hyM : yG ∈ M := (S.subtype y).property
    have hMe : M.map e.toMonoidHom = M := by
      change e • M = M
      exact Subgroup.conj_smul_eq_self_of_mem hyM
    have hPYmap :
        (((PY : Subgroup S).map S.subtype).map M.subtype) =
          PG.map e.toMonoidHom := by
      simpa [e, yG, PG, ← hPMPS] using
        (ambient_map_sylow_conj_of_smul_eq PS PY y hy)
    have htransport := def_uniq_mmaxJ e hPGFamily
    rw [← hPYmap, hMe] at htransport
    exact htransport

end

end Submission.OddOrder.BG.Section12
