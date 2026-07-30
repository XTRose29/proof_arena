import Submission.OddOrder.BG.Section10.BasicMaximalStructure
import Submission.OddOrder.BG.Section10.SigmaDisjointness
import Submission.OddOrder.BG.Section11.ExceptionalSigmaNil
import Submission.OddOrder.MathlibSupport.CharacteristicUnderNormalizer
import Submission.OddOrder.MathlibSupport.CoprimeAbelianCentralizerGenerationSolvable
import Submission.OddOrder.MathlibSupport.ElementaryAbelianSup
import Submission.OddOrder.MathlibSupport.OddPGroupOmegaAction
import Submission.OddOrder.MathlibSupport.OmegaOneCyclicMaximal
import Submission.OddOrder.MathlibSupport.OmegaOneFunctorial
import Submission.OddOrder.MathlibSupport.RepresentationSubgroupRestriction
import Submission.OddOrder.MathlibSupport.SolvableHallContainment

/-!
# Bender--Glauberman Section 11: exceptional subgroup structure

This file ports `BGsection11.v: exceptional_Sylow_abelian`,
`exceptional_structure`, and `exceptional_mul_sigma_normal` (Theorem 11.5,
Corollary 11.6, and Theorem 11.7).
-/

namespace Submission.OddOrder.BG.Section11

open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative Pointwise

universe u

noncomputable section

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

private theorem exists_sylow_eq_map_of_sylow_hall
    {H : Type u} [Group H] [Finite H]
    {pi : Set ℕ} {p : ℕ} (hp : p.Prime)
    {A : Subgroup H} (hA : IsHall pi A) (hpPi : p ∈ pi)
    (P : Sylow p A) :
    ∃ Q : Sylow p H,
      (Q : Subgroup H) = (P : Subgroup A).map A.subtype := by
  letI : Fact p.Prime := ⟨hp⟩
  let S : Subgroup H := (P : Subgroup A).map A.subtype
  have hSp : IsPGroup p S := P.isPGroup'.map A.subtype
  have hpAindex : ¬ p ∣ A.index := by
    intro hpIndex
    exact hA.isPiNumber_index hp hpIndex hpPi
  have hpSindex : ¬ p ∣ S.index := by
    dsimp [S]
    rw [Subgroup.index_map_subtype]
    exact hp.not_dvd_mul P.not_dvd_index hpAindex
  exact ⟨hSp.toSylow hpSindex, rfl⟩

private theorem centralizerWithin_map_equiv
    {G : Type u} [Group G]
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

private theorem map_conj_map_conj
    {G : Type*} [Group G] (H : Subgroup G) (a b : G) :
    (H.map (MulAut.conj a).toMonoidHom).map
        (MulAut.conj b).toMonoidHom =
      H.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem map_conj_one
    {G : Type*} [Group G] (H : Subgroup G) :
    H.map (MulAut.conj 1).toMonoidHom = H := by
  convert H.map_id using 1
  ext x
  simp

private theorem characteristic_map_subtype_le_normalizer
    {G : Type*} [Group G] (E : Subgroup G)
    (R : Subgroup E) [R.Characteristic] :
    Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer (R.map E.subtype : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro r
  constructor
  · intro hr
    exact characteristic_map_subtype_invariant_under_normalizer
      E (Subgroup.normalizer (E : Set G)) R le_rfl g hg r hr
  · intro hr
    have hginv : g⁻¹ ∈ Subgroup.normalizer (E : Set G) :=
      (Subgroup.normalizer (E : Set G)).inv_mem hg
    have := characteristic_map_subtype_invariant_under_normalizer
      E (Subgroup.normalizer (E : Set G)) R le_rfl
      g⁻¹ hginv (g * r * g⁻¹) hr
    have hcancel : g⁻¹ * (g * r * g⁻¹) * (g⁻¹)⁻¹ = r := by group
    simpa only [hcancel] using this

private theorem omegaOneCenterAmbient_map_conj_eq
    {G : Type u} [Group G] (p : ℕ) (P : Subgroup G)
    {g : G} (hg : g ∈ Subgroup.normalizer (P : Set G)) :
    (omegaOneCenterAmbient p P).map
        (MulAut.conj g).toMonoidHom =
      omegaOneCenterAmbient p P := by
  let Z : Subgroup G := omegaOneCenterAmbient p P
  have hgZ : g ∈ Subgroup.normalizer (Z : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      exact characteristic_map_subtype_invariant_under_normalizer
        P (Subgroup.normalizer (P : Set G))
        (Submission.OddOrder.BG.Section05.omegaOneCenter p P)
        le_rfl g hg z hz
    · intro hz
      have hginv : g⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
        (Subgroup.normalizer (P : Set G)).inv_mem hg
      have := characteristic_map_subtype_invariant_under_normalizer
        P (Subgroup.normalizer (P : Set G))
        (Submission.OddOrder.BG.Section05.omegaOneCenter p P)
        le_rfl g⁻¹ hginv (g * z * g⁻¹) hz
      have hcancel : g⁻¹ * (g * z * g⁻¹) * (g⁻¹)⁻¹ = z := by group
      simpa only [Z, omegaOneCenterAmbient, hcancel] using this
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hgZ

private theorem isElementaryAbelianGroup_map_of_injective
    {G K : Type*} [Group G] [Group K]
    {p : ℕ} {E : Subgroup G}
    (hE : IsElementaryAbelianGroup p E)
    (f : G →* K) (_hf : Function.Injective f) :
    IsElementaryAbelianGroup p (E.map f) := by
  refine
    { isPGroup := hE.isPGroup.map f
      commutative := ?_
      pow_eq_one := ?_ }
  · letI : IsMulCommutative E := hE.commutative
    infer_instance
  · rintro ⟨_, x, hx, rfl⟩
    apply Subtype.ext
    have hxpow := congrArg Subtype.val (hE.pow_eq_one ⟨x, hx⟩)
    simpa using congrArg f hxpow

private theorem sup_eq_top_of_complementary_hall
    {K : Type u} [Group K] [Finite K]
    {pi : Set ℕ} {H L : Subgroup K}
    (hH : IsHall pi H) (hL : IsHall piᶜ L) :
    H ⊔ L = ⊤ := by
  apply Subgroup.index_eq_one.mp
  rw [Nat.eq_one_iff_not_exists_prime_dvd]
  intro q hq hqindex
  have hqHindex : q ∣ H.index :=
    hqindex.trans (Subgroup.index_dvd_of_le le_sup_left)
  have hqLindex : q ∣ L.index :=
    hqindex.trans (Subgroup.index_dvd_of_le le_sup_right)
  have hqNotPi : q ∈ piᶜ :=
    hH.isPiNumber_index hq hqHindex
  have hqNotNotPi : q ∈ (piᶜ)ᶜ :=
    hL.isPiNumber_index hq hqLindex
  exact hqNotNotPi hqNotPi

private theorem isPiNumber_le_normal_isHall
    {K : Type u} [Group K] [Finite K]
    {pi : Set ℕ} {B H : Subgroup K}
    (hHnormal : H.Normal)
    (hBpi : IsPiNumber pi (Nat.card B))
    (hH : IsHall pi H) :
    B ≤ H := by
  letI : H.Normal := hHnormal
  have hrelPi : IsPiNumber pi (H.relIndex (H ⊔ B)) := by
    rw [Subgroup.relIndex_sup_left]
    exact hBpi.of_dvd (Subgroup.relIndex_dvd_card H B)
  have hrelCompl : IsPiNumber piᶜ (H.relIndex (H ⊔ B)) :=
    hH.isPiNumber_index.of_dvd
      (Subgroup.relIndex_dvd_index_of_le le_sup_left)
  have hcop : (H.relIndex (H ⊔ B)).Coprime
      (H.relIndex (H ⊔ B)) :=
    hrelPi.coprime_compl hrelCompl
  have hone : H.relIndex (H ⊔ B) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop dvd_rfl dvd_rfl
  exact le_sup_right.trans (Subgroup.relIndex_eq_one.mp hone)

private theorem exists_ambient_sylow_eq_of_sylow_hall
    {G : Type u} [Group G] [Finite G]
    {pi : Set ℕ} {p : ℕ} (hp : p.Prime)
    {K H : Subgroup G} (hKH : K ≤ H)
    (hKHall : IsHall pi (K.subgroupOf H))
    (hpPi : p ∈ pi) (P : Sylow p K) :
    ∃ Q : Sylow p H,
      (Q : Subgroup H).map H.subtype =
        (P : Subgroup K).map K.subtype := by
  letI : Fact p.Prime := ⟨hp⟩
  let e : K.subgroupOf H ≃* K :=
    Subgroup.subgroupOfEquivOfLe hKH
  let P' : Sylow p (K.subgroupOf H) :=
    P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨Q, hQ⟩ :=
    exists_sylow_eq_map_of_sylow_hall hp hKHall hpPi P'
  refine ⟨Q, ?_⟩
  rw [hQ, Subgroup.map_map]
  simp only [P', Sylow.coe_mapSurjective, Subgroup.map_map]
  apply congrArg (fun f : K →* G ↦ (P : Subgroup K).map f)
  ext x
  rfl

private theorem subgroupOf_commutator_eq
    {G : Type*} [Group G]
    {J H R : Subgroup G} (hHJ : H ≤ J) (hRJ : R ≤ J) :
    (⁅H, R⁆ : Subgroup G).subgroupOf J =
      ⁅H.subgroupOf J, R.subgroupOf J⁆ := by
  apply Subgroup.map_injective J.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le
    ((Subgroup.commutator_le_sup H R).trans (sup_le hHJ hRJ))]
  exact
    (map_subgroupOf_commutator
      (J := J) (H := R) (R := H) hRJ hHJ).symm

private theorem rankTwo_distinct_lines_11
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {A X Z : Subgroup G}
    (hA : IsElementaryAbelianOfRank p 2 A)
    (hX : RankOneLineIn p A X) (hZ : RankOneLineIn p A Z)
    (hne : X ≠ Z) :
    Disjoint X Z ∧ X ⊔ Z = A := by
  have hdis : Disjoint X Z := by
    rw [disjoint_iff]
    by_contra hneBot
    have hdiv : Nat.card (X ⊓ Z : Subgroup G) ∣ p := by
      have hdivX : Nat.card (X ⊓ Z : Subgroup G) ∣ Nat.card X :=
        Subgroup.card_dvd_of_le inf_le_left
      simpa only [hX.2.card_eq, pow_one] using hdivX
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdiv with
      hcardOne | hcardP
    · exact hneBot (Subgroup.eq_bot_of_card_eq (X ⊓ Z) hcardOne)
    · have hInfX : X ⊓ Z = X := by
        apply Subgroup.eq_of_le_of_card_ge inf_le_left
        rw [hcardP, hX.2.card_eq, pow_one]
      have hXZ : X ≤ Z := by
        intro x hx
        have hxInf : x ∈ X ⊓ Z := by rw [hInfX]; exact hx
        exact hxInf.2
      have hcardEq : Nat.card X = Nat.card Z := by
        rw [hX.2.card_eq, hZ.2.card_eq]
      exact hne (Subgroup.eq_of_le_of_card_ge hXZ hcardEq.ge)
  refine ⟨hdis, ?_⟩
  apply Subgroup.eq_of_le_of_card_ge (sup_le hX.1 hZ.1)
  rw [natCard_sup_eq_mul_of_disjoint_of_commute hdis,
    hX.2.card_eq, hZ.2.card_eq, hA.card_eq, pow_one, pow_two]
  intro x hx y hy
  letI : IsMulCommutative A := hA.commutative
  exact congrArg Subtype.val
    (mul_comm (⟨x, hX.1 hx⟩ : A) ⟨y, hZ.1 hy⟩)

private theorem map_omegaOne_le_centralizerWithin_of_cyclic
    {G : Type u} [Group G] [Finite G]
    {q : ℕ} [Fact q.Prime] {Q A : Subgroup G}
    (hQp : IsPGroup q Q) (hQcyc : IsCyclic Q)
    (hQne : Q ≠ ⊥)
    (hCne : centralizerWithin Q A ≠ ⊥) :
    (omegaOne q Q).map Q.subtype ≤ centralizerWithin Q A := by
  letI : IsCyclic Q := hQcyc
  obtain ⟨c, hcne⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp hCne
  let cQ : Q := ⟨(c : G), c.property.1⟩
  let H : Subgroup Q := Subgroup.zpowers cQ
  have hcQne : cQ ≠ 1 := by
    intro h
    apply hcne
    apply Subtype.ext
    exact congrArg (fun z : Q ↦ (z : G)) h
  have hHne : H ≠ ⊥ := by
    simpa [H, Subgroup.zpowers_eq_bot] using hcQne
  have hHp : IsPGroup q H := hQp.to_subgroup H
  have hHcardNe : Nat.card H ≠ 1 :=
    (H.one_lt_card_iff_ne_bot.mpr hHne).ne'
  have hQcardNe : Nat.card Q ≠ 1 :=
    (Q.one_lt_card_iff_ne_bot.mpr hQne).ne'
  have hHOmegaCard : Nat.card (omegaOne q H) = q := by
    exact card_omegaOne_of_isCyclic_isPGroup
      (Fact.out : q.Prime) hHp hHcardNe
  have hQOmegaCard : Nat.card (omegaOne q Q) = q :=
    card_omegaOne_of_isCyclic_isPGroup
      (Fact.out : q.Prime) hQp hQcardNe
  let W : Subgroup Q := (omegaOne q H).map H.subtype
  have hWOmega : W ≤ omegaOne q Q := by
    exact map_omegaOne_le q H.subtype
  have hWcard : Nat.card W = q := by
    rw [Subgroup.card_map_of_injective H.subtype_injective,
      hHOmegaCard]
  have hWeq : W = omegaOne q Q := by
    apply Subgroup.eq_of_le_of_card_ge hWOmega
    rw [hWcard, hQOmegaCard]
  have hHC : H ≤ (centralizerWithin Q A).subgroupOf Q := by
    apply Subgroup.zpowers_le.mpr
    exact c.property
  rintro _ ⟨x, hx, rfl⟩
  have hxW : x ∈ W := by rw [hWeq]; exact hx
  rcases hxW with ⟨y, hy, rfl⟩
  exact hHC y.property

/-! ### Theorem 11.5 -/

/-- `BGsection11.v: exceptional_Sylow_abelian` (Theorem 11.5).

Every Sylow `p`-subgroup of an exceptional maximal subgroup is abelian.
The conclusion is stated for its ambient image, matching the subgroup
conventions used throughout Section 10. -/
theorem exceptional_Sylow_abelian
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} {M A₀ A : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hExc : exceptional_FTmaximal p M A₀ A)
    (P : Sylow p M) (hAP : A ≤ ambientSylow M P)
    (P₁ : Sylow p M) :
    IsMulCommutative (ambientSylow M P₁) := by
  classical
  letI : Fact p.Prime := ⟨hExc.prime⟩
  let PG : Subgroup G := ambientSylow M P
  have hPGp : IsPGroup p PG := by
    dsimp [PG, ambientSylow]
    exact P.isPGroup'.map M.subtype
  have hPGM : PG ≤ M := by
    dsimp [PG, ambientSylow]
    exact Subgroup.map_subtype_le (P : Subgroup M)
  have hAcomm : IsMulCommutative A := hExc.A_rank_two.commutative
  have hAncyc : ¬ IsCyclic A :=
    hExc.A_rank_two.not_isCyclic hExc.prime

  have nregA :
      ∀ {q : ℕ} [Fact q.Prime] (Q : Subgroup G),
        Q ≠ ⊥ → IsPGroup q Q →
        A ≤ Subgroup.normalizer (Q : Set G) →
        (Nat.card Q).Coprime (Nat.card A) →
        ∃ X : Subgroup G, X ≤ A ∧
          IsElementaryAbelianOfRank p 1 X ∧
          centralizerWithin Q X ≠ ⊥ := by
    intro q _ Q hQne hQp hAQ hcop
    by_contra hnone
    push_neg at hnone
    have hQsol : IsSolvable Q := by
      letI : Group.IsNilpotent Q := hQp.isNilpotent
      infer_instance
    have hQbot : Q ≤ (⊥ : Subgroup G) := by
      apply le_of_centralizerWithin_zpowers_le_of_coprime_abelian_solvable
        hAcomm hAncyc hAQ hcop hQsol
      intro a haA haOne
      have hapow : a ^ p = 1 := by
        exact congrArg Subtype.val
          (hExc.A_rank_two.pow_eq_one ⟨a, haA⟩)
      have hadvd : orderOf a ∣ p := orderOf_dvd_of_pow_eq_one hapow
      have haOrderNe : orderOf a ≠ 1 := by
        intro horder
        exact haOne (orderOf_eq_one_iff.mp horder)
      have haOrder : orderOf a = p :=
        ((Nat.dvd_prime hExc.prime).mp hadvd).resolve_left haOrderNe
      let X : Subgroup G := Subgroup.zpowers a
      have hXA : X ≤ A := Subgroup.zpowers_le.mpr haA
      have hXcard : Nat.card X = p := by
        simpa [X, Nat.card_zpowers] using haOrder
      have hXrank : IsElementaryAbelianOfRank p 1 X :=
        isElementaryAbelianOfRank_one_of_card_eq_prime hXcard
      exact (hnone X hXA hXrank).le
    exact hQne (le_bot_iff.mp hQbot)

  suffices hPGcomm : IsMulCommutative PG by
    obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M P P₁
    have hconj := ambientSylow_conj_of_smul_eq M P₁ P m hm
    let e : G ≃* G := MulAut.conj (m : G)
    haveI : IsMulCommutative PG := hPGcomm
    have hmapComm : IsMulCommutative (PG.map e.toMonoidHom) := by
      infer_instance
    exact hconj.symm ▸ hmapComm

  have hnotNormalizer :
      ¬ Subgroup.normalizer (PG : Set G) ≤ M := by
    simpa [PG] using
      sigma'_Sylow_contra hExc.prime P hExc.sigma_compl
  obtain ⟨g, hgN, hgM⟩ := Set.not_subset.mp hnotNormalizer
  let e : G ≃* G := MulAut.conj g⁻¹
  have hPGmap : PG.map e.toMonoidHom = PG := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mp
    exact (Subgroup.normalizer (PG : Set G)).inv_mem hgN
  have hAMg : A ≤ M.map e.toMonoidHom := by
    calc
      A ≤ PG := hAP
      _ = PG.map e.toMonoidHom := hPGmap.symm
      _ ≤ M.map e.toMonoidHom := Subgroup.map_mono hPGM

  let S : Subgroup G := sigmaCore M
  have hSne : S ≠ ⊥ := by
    simpa [S] using Msigma_neq1 hM
  have hScard : Nat.card S ≠ 1 :=
    (S.one_lt_card_iff_ne_bot.mpr hSne).ne'
  obtain ⟨q, hq, hqS⟩ := Nat.exists_prime_and_dvd hScard
  letI : Fact q.Prime := ⟨hq⟩
  have hqSigma : q ∈ sigmaPrimes M :=
    sigmaCore_isPiNumber M hq hqS
  have hMnormS : M ≤ Subgroup.normalizer (S : Set G) := by
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (sigmaCore_le M)).mp (sigmaCore_normal M)
  have hPGnormS : PG ≤ Subgroup.normalizer (S : Set G) :=
    hPGM.trans hMnormS
  have hcopSPG : (Nat.card S).Coprime (Nat.card PG) := by
    obtain ⟨n, hPGcard⟩ := IsPGroup.iff_card.mp hPGp
    apply Nat.coprime_of_dvd
    intro r hr hrS hrPG
    have hrSigma : r ∈ sigmaPrimes M :=
      sigmaCore_isPiNumber M hr hrS
    have hrpow : r ∣ p ^ n := by
      rwa [← hPGcard]
    have hrp : r = p :=
      Nat.prime_eq_prime_of_dvd_pow hr hExc.prime hrpow
    rw [hrp] at hrSigma
    exact hExc.sigma_compl hrSigma
  have hSproper : S < ⊤ :=
    lt_of_le_of_lt (sigmaCore_le M) (mmax_proper hM)
  obtain ⟨R₁, hPGR₁⟩ :=
    exists_sylow_normalized_of_coprime_of_isSolvable
      (p := q) hPGnormS hcopSPG (mFT_sol hSproper)
  obtain ⟨Q₁, hQ₁eq⟩ :=
    exists_sylow_eq_map_of_sylow_hall hq
      (Msigma_Hall_G hM) hqSigma R₁
  have hQ₁S : (Q₁ : Subgroup G) ≤ S := by
    rw [hQ₁eq]
    exact Subgroup.map_subtype_le (R₁ : Subgroup S)
  have hPGQ₁ : PG ≤
      Subgroup.normalizer ((Q₁ : Subgroup G) : Set G) := by
    rw [hQ₁eq]
    exact hPGR₁
  have hQ₁ne : (Q₁ : Subgroup G) ≠ ⊥ := by
    have hR₁ne : (R₁ : Subgroup S) ≠ ⊥ :=
      R₁.ne_bot_of_dvd_card hqS
    intro hbot
    apply hR₁ne
    apply (Subgroup.map_eq_bot_iff_of_injective
      (R₁ : Subgroup S) S.subtype_injective).mp
    simpa [hQ₁eq] using hbot
  have hAQ₁ : A ≤
      Subgroup.normalizer ((Q₁ : Subgroup G) : Set G) :=
    hAP.trans hPGQ₁
  have hcopSA : (Nat.card S).Coprime (Nat.card A) := by
    apply Nat.coprime_of_dvd
    intro r hr hrS hrA
    have hrSigma : r ∈ sigmaPrimes M :=
      sigmaCore_isPiNumber M hr hrS
    have hrpow : r ∣ p ^ 2 := by
      simpa only [hExc.A_rank_two.card_eq] using hrA
    have hrp : r = p :=
      Nat.prime_eq_prime_of_dvd_pow hr hExc.prime hrpow
    rw [hrp] at hrSigma
    exact hExc.sigma_compl hrSigma
  have hcopQ₁A :
      (Nat.card (Q₁ : Subgroup G)).Coprime (Nat.card A) :=
    hcopSA.coprime_dvd_left (Subgroup.card_dvd_of_le hQ₁S)
  obtain ⟨X₁, hX₁A, hX₁, hCX₁₁⟩ :=
    nregA (Q₁ : Subgroup G) hQ₁ne Q₁.isPGroup'
      hAQ₁ hcopQ₁A

  let Q₂ : Sylow q G :=
    Q₁.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ₂eq : (Q₂ : Subgroup G) =
      (Q₁ : Subgroup G).map e.toMonoidHom := by
    simp only [Q₂, Sylow.coe_mapSurjective]
  have hQ₂core : (Q₂ : Subgroup G) ≤
      sigmaCore (M.map e.toMonoidHom) := by
    rw [sigmaCore_map_mulEquiv, hQ₂eq]
    exact Subgroup.map_mono hQ₁S
  have hPGQ₂ : PG ≤
      Subgroup.normalizer ((Q₂ : Subgroup G) : Set G) := by
    have hmapped := Subgroup.map_mono hPGQ₁ (f := e.toMonoidHom)
    rw [Subgroup.map_equiv_normalizer_eq (Q₁ : Subgroup G) e,
      hPGmap, ← hQ₂eq] at hmapped
    exact hmapped
  have hAQ₂ : A ≤
      Subgroup.normalizer ((Q₂ : Subgroup G) : Set G) :=
    hAP.trans hPGQ₂
  have hQ₂ne : (Q₂ : Subgroup G) ≠ ⊥ := by
    rw [hQ₂eq]
    exact fun hbot ↦ hQ₁ne
      ((Subgroup.map_eq_bot_iff_of_injective
        (Q₁ : Subgroup G) e.injective).mp hbot)
  have hcopQ₂A :
      (Nat.card (Q₂ : Subgroup G)).Coprime (Nat.card A) := by
    rw [hQ₂eq, Subgroup.card_map_of_injective e.injective]
    exact hcopQ₁A
  obtain ⟨X₂, hX₂A, hX₂, hCX₂₂⟩ :=
    nregA (Q₂ : Subgroup G) hQ₂ne Q₂.isPGroup'
      hAQ₂ hcopQ₂A

  have hTI := exceptional_TIsigmaJ hM hExc P hAP hq Q₁ Q₂ g
    hgM hAMg hQ₁S hAQ₁ hQ₂core hAQ₂
  have hCX₂₁ : centralizerWithin (Q₁ : Subgroup G) X₂ = ⊥ := by
    rcases hTI.2 X₂ hX₂A hX₂ with h | h
    · exact h
    · exact (hCX₂₂ h).elim
  have hCX₁₂ : centralizerWithin (Q₂ : Subgroup G) X₁ = ⊥ := by
    rcases hTI.2 X₁ hX₁A hX₁ with h | h
    · exact (hCX₁₁ h).elim
    · exact h

  let Z : Subgroup G := omegaOneCenterAmbient p PG
  have hZmap : Z.map e.toMonoidHom = Z := by
    simpa [Z, e] using
      omegaOneCenterAmbient_map_conj_eq p PG
        ((Subgroup.normalizer (PG : Set G)).inv_mem hgN)
  have hCentMap :
      (centralizerWithin (Q₁ : Subgroup G) Z).map e.toMonoidHom =
        centralizerWithin (Q₂ : Subgroup G) Z := by
    simpa only [hQ₂eq, hZmap] using
      centralizerWithin_map_equiv (Q₁ : Subgroup G) Z e
  have hCentBotIff :
      centralizerWithin (Q₁ : Subgroup G) Z = ⊥ ↔
        centralizerWithin (Q₂ : Subgroup G) Z = ⊥ := by
    constructor
    · intro hbot
      rw [← hCentMap, hbot]
      simp
    · intro hbot
      apply (Subgroup.map_eq_bot_iff_of_injective
        (f := e.toMonoidHom)
        (centralizerWithin (Q₁ : Subgroup G) Z) e.injective).mp
      rw [hCentMap, hbot]
  have hX₁Z : X₁ ≠ Z := by
    intro h
    apply hCX₁₁
    rw [h, hCentBotIff]
    simpa [h] using hCX₁₂
  have hX₂Z : X₂ ≠ Z := by
    intro h
    apply hCX₂₂
    rw [h, ← hCentBotIff]
    simpa [h] using hCX₂₁

  by_contra hPGnoncomm
  obtain ⟨_, _, htrans⟩ :=
    basic_p2maxElem_structure hExc.A_rank_two
      (exceptional_pmaxElem hM hExc P hAP)
      hPGp hAP hPGnoncomm
  obtain ⟨x, hxP, hxmap⟩ :=
    htrans X₁ X₂ ⟨hX₁A, hX₁⟩ hX₁Z
      ⟨hX₂A, hX₂⟩ hX₂Z
  have hxQ₁ : x ∈
      Subgroup.normalizer ((Q₁ : Subgroup G) : Set G) :=
    hPGQ₁ hxP.1
  let ex : G ≃* G := MulAut.conj x⁻¹
  have hQ₁map : (Q₁ : Subgroup G).map ex.toMonoidHom =
      (Q₁ : Subgroup G) := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mp
    exact (Subgroup.normalizer ((Q₁ : Subgroup G) : Set G)).inv_mem hxQ₁
  have hCentXmap :
      (centralizerWithin (Q₁ : Subgroup G) X₁).map ex.toMonoidHom =
        centralizerWithin (Q₁ : Subgroup G) X₂ := by
    simpa only [hQ₁map, hxmap] using
      centralizerWithin_map_equiv (Q₁ : Subgroup G) X₁ ex
  apply hCX₁₁
  apply (Subgroup.map_eq_bot_iff_of_injective
    (f := ex.toMonoidHom)
    (centralizerWithin (Q₁ : Subgroup G) X₁) ex.injective).mp
  rw [hCentXmap, hCX₂₁]

/-! ### Corollary 11.6 -/

/-- `BGsection11.v: exceptional_structure` (Corollary 11.6).

The exceptional rank-two subgroup is the ambient first omega subgroup of
the chosen Sylow subgroup, acts fixed-point-freely on the sigma core, and
contains two distinct lines which also act fixed-point-freely there. -/
theorem exceptional_structure
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} {M A₀ A : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hExc : exceptional_FTmaximal p M A₀ A)
    (P : Sylow p M) (hAP : A ≤ ambientSylow M P) :
    let PG := ambientSylow M P
    let Omega := (omegaOne p PG).map PG.subtype
    A = Omega ∧
      centralizerWithin (sigmaCore M) A = ⊥ ∧
      ∃ A₁ A₂ : Subgroup G,
        A₁ ≤ A ∧ IsElementaryAbelianOfRank p 1 A₁ ∧
        A₂ ≤ A ∧ IsElementaryAbelianOfRank p 1 A₂ ∧
        A₁ ≠ A₂ ∧
        centralizerWithin (sigmaCore M) A₁ = ⊥ ∧
        centralizerWithin (sigmaCore M) A₂ = ⊥ := by
  classical
  letI : Fact p.Prime := ⟨hExc.prime⟩
  let PG : Subgroup G := ambientSylow M P
  let OmegaP : Subgroup PG := omegaOne p PG
  let Omega : Subgroup G := OmegaP.map PG.subtype
  have hPGp : IsPGroup p PG := by
    dsimp [PG, ambientSylow]
    exact P.isPGroup'.map M.subtype
  have hPGM : PG ≤ M := by
    dsimp [PG, ambientSylow]
    exact Subgroup.map_subtype_le (P : Subgroup M)
  have hPGcomm : IsMulCommutative PG :=
    exceptional_Sylow_abelian hM hExc P hAP P
  letI : IsMulCommutative PG := hPGcomm
  have hOmegaPpow : ∀ x : OmegaP, x ^ p = 1 := by
    intro x
    apply Subtype.ext
    apply omegaOne_pow_eq_one_of_mul_closed p
    · intro a b ha hb
      rw [mul_pow, ha, hb, one_mul]
    · exact x.property
  have hOmegaPel : IsElementaryAbelianGroup p OmegaP :=
    { isPGroup := omegaOne_isPGroup p hPGp
      commutative := by infer_instance
      pow_eq_one := hOmegaPpow }
  have hOmegael : IsElementaryAbelianGroup p Omega := by
    exact isElementaryAbelianGroup_map_of_injective
      hOmegaPel PG.subtype PG.subtype_injective
  have hAOmega : A ≤ Omega := by
    intro a ha
    let aP : PG := ⟨a, hAP ha⟩
    have haPow : aP ^ p = 1 := by
      apply Subtype.ext
      exact congrArg (fun z : A ↦ (z : G))
        (hExc.A_rank_two.pow_eq_one ⟨a, ha⟩)
    exact ⟨aP, mem_omegaOne_of_pow_eq_one p haPow, rfl⟩
  have hdefA : A = Omega := by
    have hmax := exceptional_pmaxElem hM hExc P hAP
    exact (hmax.2 Omega ⟨le_top, hOmegael⟩ hAOmega).symm

  let N : Subgroup G := Subgroup.normalizer (A : Set G)
  have hnormPGN : Subgroup.normalizer (PG : Set G) ≤ N := by
    dsimp [N]
    rw [hdefA]
    exact characteristic_map_subtype_le_normalizer PG OmegaP
  have hNnotM : ¬ N ≤ M := by
    intro hNM
    apply sigma'_Sylow_contra hExc.prime P hExc.sigma_compl
    exact hnormPGN.trans hNM
  let i : ℕ := M.relIndex N
  have hiNeOne : i ≠ 1 := by
    intro hi
    apply hNnotM
    exact Subgroup.relIndex_eq_one.mp (by simpa [i] using hi)
  have hiNeZero : i ≠ 0 := by
    intro hi
    have hiDvd : i ∣ Nat.card N := by
      simpa [i] using Subgroup.relIndex_dvd_card M N
    rw [hi] at hiDvd
    have hcardZero : Nat.card N = 0 := by simpa using hiDvd
    exact Nat.card_pos.ne' hcardZero
  have hiOne : 1 < i := by omega
  have hiOdd : Odd i := by
    apply (mFT_odd N).of_dvd_nat
    simpa [i] using Subgroup.relIndex_dvd_card M N
  have hiTwo : 2 < i := by
    by_contra hnot
    have hiEq : i = 2 := by omega
    exact hiOdd.not_two_dvd_nat (by simp [hiEq])

  let MN : Subgroup N := M.subgroupOf N
  letI : Fintype (N ⧸ MN) := Fintype.ofFinite (N ⧸ MN)
  have hquotTwo : 2 < Fintype.card (N ⧸ MN) := by
    rw [← Nat.card_eq_fintype_card]
    simpa [i, MN, Subgroup.relIndex, Subgroup.index] using hiTwo
  obtain ⟨c₀, c₁, c₂, hc₀₁, hc₀₂, hc₁₂⟩ :=
    Fintype.two_lt_card_iff.mp hquotTwo
  let oneCoset : N ⧸ MN := QuotientGroup.mk (1 : N)
  have htwoCosets :
      ∃ d₁ d₂ : N ⧸ MN,
        d₁ ≠ oneCoset ∧ d₂ ≠ oneCoset ∧ d₁ ≠ d₂ := by
    by_cases h₀ : c₀ = oneCoset
    · subst c₀
      exact ⟨c₁, c₂, hc₀₁.symm, hc₀₂.symm, hc₁₂⟩
    by_cases h₁ : c₁ = oneCoset
    · subst c₁
      exact ⟨c₀, c₂, h₀, hc₁₂.symm, hc₀₂⟩
    exact ⟨c₀, c₁, h₀, h₁, hc₀₁⟩
  obtain ⟨d₁, d₂, hd₁One, hd₂One, hd₁d₂⟩ := htwoCosets
  let g₁ : G := (((d₁.out : N) : G))⁻¹
  let g₂ : G := (((d₂.out : N) : G))⁻¹
  have hg₁N : g₁ ∈ N := by
    exact N.inv_mem d₁.out.property
  have hg₂N : g₂ ∈ N := by
    exact N.inv_mem d₂.out.property
  have hg₁M : g₁ ∉ M := by
    intro hgM
    apply hd₁One
    rw [← QuotientGroup.out_eq' d₁]
    apply QuotientGroup.eq.mpr
    simp only [mul_one]
    change (((d₁.out : N) : G))⁻¹ ∈ M
    simpa [g₁] using hgM
  have hg₂M : g₂ ∉ M := by
    intro hgM
    apply hd₂One
    rw [← QuotientGroup.out_eq' d₂]
    apply QuotientGroup.eq.mpr
    simp only [mul_one]
    change (((d₂.out : N) : G))⁻¹ ∈ M
    simpa [g₂] using hgM
  let e₁ : G ≃* G := MulAut.conj g₁⁻¹
  let e₂ : G ≃* G := MulAut.conj g₂⁻¹
  have hAmap₁ : A.map e₁.toMonoidHom = A := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mp
    exact N.inv_mem hg₁N
  have hAmap₂ : A.map e₂.toMonoidHom = A := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mp
    exact N.inv_mem hg₂N
  let A₁ : Subgroup G := A₀.map e₁.toMonoidHom
  let A₂ : Subgroup G := A₀.map e₂.toMonoidHom
  have hA₁A : A₁ ≤ A := by
    exact (Subgroup.map_mono hExc.A₀_le).trans (le_of_eq hAmap₁)
  have hA₂A : A₂ ≤ A := by
    exact (Subgroup.map_mono hExc.A₀_le).trans (le_of_eq hAmap₂)
  have hA₁rank : IsElementaryAbelianOfRank p 1 A₁ := by
    exact hExc.A₀_rank_one.map_of_injective
      e₁.toMonoidHom e₁.injective
  have hA₂rank : IsElementaryAbelianOfRank p 1 A₂ := by
    exact hExc.A₀_rank_one.map_of_injective
      e₂.toMonoidHom e₂.injective
  have hA₁neA₂ : A₁ ≠ A₂ := by
    intro hAeq
    let d : G := g₂ * g₁⁻¹
    have hmapd :
        A₀.map (MulAut.conj d).toMonoidHom = A₀ := by
      calc
        A₀.map (MulAut.conj d).toMonoidHom =
            (A₀.map (MulAut.conj g₁⁻¹).toMonoidHom).map
              (MulAut.conj g₂).toMonoidHom := by
                simpa [d] using
                  (map_conj_map_conj A₀ g₁⁻¹ g₂).symm
        _ = (A₀.map (MulAut.conj g₂⁻¹).toMonoidHom).map
              (MulAut.conj g₂).toMonoidHom := by
                exact congrArg
                  (fun H : Subgroup G ↦
                    H.map (MulAut.conj g₂).toMonoidHom) hAeq
        _ = A₀.map (MulAut.conj 1).toMonoidHom := by
              simpa only [mul_inv_cancel] using
                map_conj_map_conj A₀ g₂⁻¹ g₂
        _ = A₀ := map_conj_one A₀
    have hdNorm : d ∈ Subgroup.normalizer (A₀ : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmapd
    have hdM : d ∈ M := hExc.normalizer_A₀_le hdNorm
    apply hd₁d₂.symm
    rw [← QuotientGroup.out_eq' d₂,
      ← QuotientGroup.out_eq' d₁]
    apply QuotientGroup.eq.mpr
    change (((d₂.out : N) : G))⁻¹ * ((d₁.out : N) : G) ∈ M
    simpa [d, g₁, g₂] using hdM

  have hAMg₁ : A ≤ M.map e₁.toMonoidHom := by
    calc
      A = A.map e₁.toMonoidHom := hAmap₁.symm
      _ ≤ M.map e₁.toMonoidHom := Subgroup.map_mono hExc.A_le
  have hAMg₂ : A ≤ M.map e₂.toMonoidHom := by
    calc
      A = A.map e₂.toMonoidHom := hAmap₂.symm
      _ ≤ M.map e₂.toMonoidHom := Subgroup.map_mono hExc.A_le
  have hregA₁ : centralizerWithin (sigmaCore M) A₁ = ⊥ := by
    simpa [centralizerWithin, A₁, e₁] using
      (exceptional_TI_MsigmaJ hM hExc P hAP g₁ hg₁M hAMg₁).2
  have hregA₂ : centralizerWithin (sigmaCore M) A₂ = ⊥ := by
    simpa [centralizerWithin, A₂, e₂] using
      (exceptional_TI_MsigmaJ hM hExc P hAP g₂ hg₂M hAMg₂).2
  have hregA : centralizerWithin (sigmaCore M) A = ⊥ := by
    apply le_antisymm _ bot_le
    rw [← hregA₁]
    exact centralizerWithin_antitone_right hA₁A
  exact ⟨hdefA, hregA, A₁, A₂, hA₁A, hA₁rank,
    hA₂A, hA₂rank, hA₁neA₂, hregA₁, hregA₂⟩

/-! ### Theorem 11.7 -/

/-- `BGsection11.v: exceptional_mul_sigma_normal` (Theorem 11.7).

The product of the sigma core with the exceptional rank-two subgroup is
normal in the exceptional maximal subgroup. -/
theorem exceptional_mul_sigma_normal
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} {M A₀ A : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hExc : exceptional_FTmaximal p M A₀ A)
    (P : Sylow p M) (hAP : A ≤ ambientSylow M P) :
    ((sigmaCore M ⊔ A).subgroupOf M).Normal := by
  classical
  letI : Fact p.Prime := ⟨hExc.prime⟩
  let SM : Subgroup M := (sigmaCore M).subgroupOf M
  let AM : Subgroup M := A.subgroupOf M
  let PM : Subgroup M := (P : Subgroup M)
  have hSMHall : IsHall (sigmaPrimes M) SM := by
    simpa [SM] using Msigma_Hall hM
  have hAMP : AM ≤ PM := by
    apply (Subgroup.map_le_map_iff_of_injective
      M.subtype_injective).mp
    simpa [AM, PM, ambientSylow,
      Subgroup.map_subgroupOf_eq_of_le hExc.A_le] using hAP
  have hPMpi : IsPiNumber (sigmaPrimes M)ᶜ (Nat.card PM) :=
    P.isPGroup'.isPiNumber_natCard hExc.sigma_compl
  obtain ⟨E, hPME, hHallE⟩ :=
    exists_isHall_ge_of_isSolvable (mmax_sol hM)
      (sigmaPrimes M)ᶜ hPMpi
  have hAME : AM ≤ E := hAMP.trans hPME
  have hSMEsup : SM ⊔ E = ⊤ :=
    sup_eq_top_of_complementary_hall hSMHall hHallE
  letI : IsSolvable M := mmax_sol hM
  letI : IsSolvable E := isSolvable_subgroup_of_isSolvable E

  have hRankE :
      ∀ q : ℕ, q.Prime →
        ¬ ∃ F : Subgroup (fittingCore E),
          IsElementaryAbelianOfRank q 3 F := by
    intro q hq
    rintro ⟨F, hF⟩
    let FE : Subgroup E := F.map (fittingCore E).subtype
    let FM : Subgroup M := FE.map E.subtype
    let FG : Subgroup G := FM.map M.subtype
    have hFE : IsElementaryAbelianOfRank q 3 FE := by
      dsimp [FE]
      exact hF.map_of_injective (fittingCore E).subtype
        (fittingCore E).subtype_injective
    have hFM : IsElementaryAbelianOfRank q 3 FM := by
      dsimp [FM]
      exact hFE.map_of_injective E.subtype E.subtype_injective
    have hFG : IsElementaryAbelianOfRank q 3 FG := by
      dsimp [FG]
      exact hFM.map_of_injective M.subtype M.subtype_injective
    have hFGM : FG ≤ M := by
      dsimp [FG, FM, FE]
      exact Subgroup.map_subtype_le _
    have hqF : q ∣ Nat.card F := by
      rw [hF.card_eq]
      exact dvd_pow_self q (by omega)
    have hqE : q ∣ Nat.card E :=
      hqF.trans (F.card_subgroup_dvd_card.trans
        (fittingCore E).card_subgroup_dvd_card)
    have hqCompl : q ∈ (sigmaPrimes M)ᶜ :=
      hHallE.isPiNumber_card hq hqE
    exact hqCompl (alpha_sub_sigma hM
      ⟨hq, FG, hFGM, hFG⟩)

  let tau : Set ℕ := {q | p < q}
  let rho : Set ℕ := {q | p ≤ q}
  let K : Subgroup E := piCore tau E
  have hHallK : IsHall tau K := by
    have h := rank2_ge_pcore_Hall (G := E) (p + 1)
      (hHallE.odd_card (mFT_odd M))
      (inferInstance : IsSolvable E) hRankE
    simpa [tau, K, Nat.succ_le_iff] using h
  let PE : Sylow p E := P.subtype hPME
  let KPE : Subgroup E := K ⊔ (PE : Subgroup E)
  have hHallKPE : IsHall rho KPE := by
    have hKpi : IsPiNumber rho (Nat.card K) :=
      hHallK.isPiNumber_card.mono (by
        intro q hq
        exact (show p < q by simpa [tau] using hq).le)
    have hPEpi : IsPiNumber rho (Nat.card (PE : Subgroup E)) :=
      PE.isPGroup'.isPiNumber_natCard (by simp [rho])
    constructor
    · dsimp [KPE]
      exact isPiNumber_card_sup_of_normal_left
        (inferInstance : K.Normal) hKpi hPEpi
    · intro q hq hqIndex
      have hqKindex : q ∣ K.index :=
        hqIndex.trans (Subgroup.index_dvd_of_le le_sup_left)
      have hqPEindex : q ∣ (PE : Subgroup E).index :=
        hqIndex.trans (Subgroup.index_dvd_of_le le_sup_right)
      have hqNotTau : q ∈ tauᶜ :=
        hHallK.isPiNumber_index hq hqKindex
      have hqp : q ≠ p := by
        intro hqp
        subst q
        exact PE.not_dvd_index hqPEindex
      change q ∈ rhoᶜ
      change ¬ p ≤ q
      intro hpq
      exact hqNotTau (lt_of_le_of_ne hpq hqp.symm)
  have hHallRhoCore : IsHall rho (piCore rho E) :=
    rank2_ge_pcore_Hall (G := E) p
      (hHallE.odd_card (mFT_odd M))
      (inferInstance : IsSolvable E) hRankE
  have hKPECore : KPE ≤ piCore rho E :=
    isPiNumber_le_normal_isHall
      (inferInstance : (piCore rho E).Normal)
      hHallKPE.isPiNumber_card hHallRhoCore
  have hCoreKPE : piCore rho E ≤ KPE :=
    normal_isPiNumber_le_isHall
      (inferInstance : (piCore rho E).Normal)
      (piCore_isPiNumber rho) hHallKPE
  have hKPEeqCore : KPE = piCore rho E :=
    le_antisymm hKPECore hCoreKPE
  have hKPENormal : KPE.Normal := by
    rw [hKPEeqCore]
    infer_instance

  let KM : Subgroup M := K.map E.subtype
  let KP : Subgroup M := KM ⊔ PM
  have hKPmap : KPE.map E.subtype = KP := by
    dsimp [KPE, KP, KM, PE, PM]
    rw [Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hPME]
  have hKPLE : KP ≤ E := by
    apply sup_le
    · dsimp [KM]
      exact Subgroup.map_subtype_le K
    · exact hPME
  have hKPsub : KP.subgroupOf E = KPE := by
    apply Subgroup.map_injective E.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hKPLE, hKPmap]
  have hKPnormalE : (KP.subgroupOf E).Normal := by
    rw [hKPsub]
    exact hKPENormal
  have hEnormKP : E ≤ Subgroup.normalizer (KP : Set M) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKPLE).mp
      hKPnormalE

  by_cases hAK : AM ≤ Subgroup.centralizer (KM : Set M)
  · let PG : Subgroup G := ambientSylow M P
    have hPGcomm : IsMulCommutative PG :=
      exceptional_Sylow_abelian hM hExc P hAP P
    letI : IsMulCommutative PG := hPGcomm
    have hPMcomm : IsMulCommutative PM := by
      apply isMulCommutative_iff.mpr
      intro x y
      apply Subtype.ext
      let xG : PG := ⟨((x : M) : G), by
        exact ⟨x, x.property, rfl⟩⟩
      let yG : PG := ⟨((y : M) : G), by
        exact ⟨y, y.property, rfl⟩⟩
      apply M.subtype_injective
      exact congrArg Subtype.val (mul_comm xG yG)
    letI : IsMulCommutative PM := hPMcomm
    have hPMcentAM : PM ≤ Subgroup.centralizer (AM : Set M) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (congrArg Subtype.val
        (mul_comm (⟨x, hx⟩ : PM) ⟨a, hAMP ha⟩)).symm
    have hKMcentAM : KM ≤ Subgroup.centralizer (AM : Set M) :=
      Subgroup.le_centralizer_iff.mp hAK
    have hKPcentAM : KP ≤ Subgroup.centralizer (AM : Set M) :=
      sup_le hKMcentAM hPMcentAM
    have hAMKP : AM ≤ KP := hAMP.trans le_sup_right
    have hKPnormAM : KP ≤ Subgroup.normalizer (AM : Set M) :=
      hKPcentAM.trans (Subgroup.centralizer_le_normalizer (AM : Set M))
    have hAMnormalKP : (AM.subgroupOf KP).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hAMKP).mpr
        hKPnormAM

    let Core : Subgroup KP := pCore p KP
    let PKP : Sylow p KP := P.subtype le_sup_right
    have hCorePKP : Core ≤ (PKP : Subgroup KP) :=
      pCore_le_sylow PKP
    have hCoreComm : IsMulCommutative Core := by
      apply isMulCommutative_iff.mpr
      intro x y
      apply Subtype.ext
      apply Subtype.ext
      let xP : PM := ⟨((x : KP) : M), by
        have hx := hCorePKP x.property
        change (x : KP) ∈ (P : Subgroup M).subgroupOf KP at hx
        exact hx⟩
      let yP : PM := ⟨((y : KP) : M), by
        have hy := hCorePKP y.property
        change (y : KP) ∈ (P : Subgroup M).subgroupOf KP at hy
        exact hy⟩
      change ((x : KP) : M) * ((y : KP) : M) =
        ((y : KP) : M) * ((x : KP) : M)
      exact congrArg (fun z : PM ↦ (z : M)) (mul_comm xP yP)
    letI : IsMulCommutative Core := hCoreComm
    let W₀ : Subgroup KP := (omegaOne p Core).map Core.subtype
    have hOmegaCorePow : ∀ x : omegaOne p Core, x ^ p = 1 := by
      intro x
      apply Subtype.ext
      apply omegaOne_pow_eq_one_of_mul_closed p
      · intro a b ha hb
        rw [mul_pow, ha, hb, one_mul]
      · exact x.property
    have hOmegaCoreElem :
        IsElementaryAbelianGroup p (omegaOne p Core) :=
      { isPGroup := omegaOne_isPGroup p pCore_isPGroup
        commutative := by infer_instance
        pow_eq_one := hOmegaCorePow }
    have hW₀Elem : IsElementaryAbelianGroup p W₀ := by
      dsimp [W₀]
      exact isElementaryAbelianGroup_map_of_injective
        hOmegaCoreElem Core.subtype Core.subtype_injective
    let W : Subgroup M := W₀.map KP.subtype
    let WG : Subgroup G := W.map M.subtype
    have hWElem : IsElementaryAbelianGroup p W := by
      dsimp [W]
      exact isElementaryAbelianGroup_map_of_injective
        hW₀Elem KP.subtype KP.subtype_injective
    have hWGElem : IsElementaryAbelianGroup p WG := by
      dsimp [WG]
      exact isElementaryAbelianGroup_map_of_injective
        hWElem M.subtype M.subtype_injective
    let AMKP : Subgroup KP := AM.subgroupOf KP
    let eAM : AM ≃* A := Subgroup.subgroupOfEquivOfLe hExc.A_le
    let eAMKP : AMKP ≃* AM := Subgroup.subgroupOfEquivOfLe hAMKP
    have hAMKPp : IsPGroup p AMKP :=
      (hExc.A_rank_two.isPGroup.of_equiv eAM.symm).of_equiv
        eAMKP.symm
    have hAMKPCore : AMKP ≤ Core := by
      dsimp [Core]
      exact le_pCore hAMKPp hAMnormalKP
    have hAMW : AM ≤ W := by
      intro a ha
      let aKP : KP := ⟨(a : M), hAMKP ha⟩
      let aAMKP : AMKP := ⟨aKP, ha⟩
      let aCore : Core := ⟨aKP, hAMKPCore aAMKP.property⟩
      have haPow : aCore ^ p = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        apply M.subtype_injective
        exact congrArg Subtype.val
          (hExc.A_rank_two.pow_eq_one
            ⟨((a : M) : G), ha⟩)
      have haW₀ : aKP ∈ W₀ := by
        exact ⟨aCore, mem_omegaOne_of_pow_eq_one p haPow, rfl⟩
      exact ⟨aKP, haW₀, rfl⟩
    have hAWG : A ≤ WG := by
      intro a ha
      let aM : M := ⟨a, hExc.A_le ha⟩
      have haW : aM ∈ W := hAMW ha
      exact ⟨aM, haW, rfl⟩
    have hWGeqA : WG = A :=
      (exceptional_pmaxElem hM hExc P hAP).2 WG
        ⟨le_top, hWGElem⟩ hAWG
    have hWeqAM : W = AM := by
      apply Subgroup.map_injective M.subtype_injective
      simpa [WG, AM,
        Subgroup.map_subgroupOf_eq_of_le hExc.A_le] using hWGeqA
    letI : W₀.Characteristic := by
      dsimp [W₀]
      exact characteristic_map_subtype Core (omegaOne p Core)
    have hEnormW : E ≤ Subgroup.normalizer (W : Set M) := by
      exact hEnormKP.trans
        (characteristic_map_subtype_le_normalizer KP W₀)
    have hEnormAM : E ≤ Subgroup.normalizer (AM : Set M) := by
      rwa [← hWeqAM]
    have hSMnormal : SM.Normal := by
      simpa [SM] using sigmaCore_normal M
    have hEnormSM : E ≤ Subgroup.normalizer (SM : Set M) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hSMnormal]
      exact le_top
    have hEnormSup : E ≤
        Subgroup.normalizer ((SM ⊔ AM : Subgroup M) : Set M) :=
      (le_inf hEnormSM hEnormAM).trans
        (Subgroup.normalizer_inf_normalizer_le_normalizer_sup SM AM)
    have hSMnormSup : SM ≤
        Subgroup.normalizer ((SM ⊔ AM : Subgroup M) : Set M) :=
      le_sup_left.trans Subgroup.le_normalizer
    have htopNorm : (⊤ : Subgroup M) ≤
        Subgroup.normalizer ((SM ⊔ AM : Subgroup M) : Set M) := by
      rw [← hSMEsup]
      exact sup_le hSMnormSup hEnormSup
    have hnormal : (SM ⊔ AM).Normal :=
      Subgroup.normalizer_eq_top_iff.mp (top_unique htopNorm)
    rw [Subgroup.subgroupOf_sup (sigmaCore_le M) hExc.A_le]
    exact hnormal
  · let C : Subgroup M := centralizerWithin KM AM
    have hCindexNe : C.relIndex KM ≠ 1 := by
      intro hindex
      have hKMC : KM ≤ C := Subgroup.relIndex_eq_one.mp hindex
      apply hAK
      apply Subgroup.le_centralizer_iff.mpr
      exact hKMC.trans inf_le_right
    obtain ⟨q, hq, hqCindex⟩ :=
      Nat.exists_prime_and_dvd hCindexNe
    letI : Fact q.Prime := ⟨hq⟩
    have hqKM : q ∣ Nat.card KM :=
      hqCindex.trans (Subgroup.relIndex_dvd_card C KM)
    have hcardKM : Nat.card KM = Nat.card K := by
      dsimp [KM]
      exact Subgroup.card_map_of_injective E.subtype_injective
    have hqK : q ∣ Nat.card K := by
      rwa [hcardKM] at hqKM
    have hqTau : q ∈ tau :=
      hHallK.isPiNumber_card hq hqK
    have hpq : p ≠ q := ne_of_lt hqTau
    have hqCompl : q ∈ (sigmaPrimes M)ᶜ := by
      apply hHallE.isPiNumber_card hq
      exact hqKM.trans (Subgroup.card_dvd_of_le
        (le_sup_left.trans hKPLE))

    have hKME : KM ≤ E := le_sup_left.trans hKPLE
    have hKMsub : KM.subgroupOf E = K := by
      apply Subgroup.map_injective E.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le hKME]
    have hKMnormalE : (KM.subgroupOf E).Normal := by
      rw [hKMsub]
      infer_instance
    have hEnormKM : E ≤ Subgroup.normalizer (KM : Set M) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKME).mp
        hKMnormalE
    have hAMnormKM : AM ≤ Subgroup.normalizer (KM : Set M) :=
      hAME.trans hEnormKM
    have hcopKMAM : (Nat.card KM).Coprime (Nat.card AM) := by
      apply Nat.coprime_of_dvd
      intro r hr hrKM hrAM
      have hrK : r ∣ Nat.card K := by
        rwa [← hcardKM]
      have hrTau : r ∈ tau := hHallK.isPiNumber_card hr hrK
      have hrA : r ∣ Nat.card A := by
        simpa [AM, natCard_subgroupOf_eq hExc.A_le] using hrAM
      have hrPow : r ∣ p ^ 2 := by
        simpa only [hExc.A_rank_two.card_eq] using hrA
      have hrp : r = p :=
        Nat.prime_eq_prime_of_dvd_pow hr hExc.prime hrPow
      rw [hrp] at hrTau
      exact (lt_irrefl p hrTau).elim
    have hKMsol : IsSolvable KM :=
      isSolvable_subgroup_of_isSolvable KM
    obtain ⟨QK, hAMQK⟩ :=
      exists_sylow_normalized_of_coprime_of_isSolvable
        (p := q) hAMnormKM hcopKMAM hKMsol
    let QM₀ : Subgroup M := (QK : Subgroup KM).map KM.subtype
    have hHallKM : IsHall tau (KM.subgroupOf E) := by
      rw [hKMsub]
      exact hHallK
    obtain ⟨QE, hQE⟩ :=
      exists_ambient_sylow_eq_of_sylow_hall hq hKME
        hHallKM hqTau QK
    obtain ⟨QM, hQM⟩ :=
      exists_sylow_eq_map_of_sylow_hall hq hHallE hqCompl QE
    have hQM₀eq : (QM : Subgroup M) = QM₀ := by
      exact hQM.trans hQE
    let QG : Subgroup G := QM₀.map M.subtype
    have hQGq : IsPGroup q QG := by
      dsimp [QG, QM₀]
      exact (QK.isPGroup'.map KM.subtype).map M.subtype
    have hQGM : QG ≤ M := by
      dsimp [QG]
      exact Subgroup.map_subtype_le QM₀
    have hQKne : (QK : Subgroup KM) ≠ ⊥ :=
      QK.ne_bot_of_dvd_card hqKM
    have hQM₀ne : QM₀ ≠ ⊥ := by
      intro hbot
      apply hQKne
      apply (Subgroup.map_eq_bot_iff_of_injective
        (QK : Subgroup KM) KM.subtype_injective).mp
      simpa [QM₀] using hbot
    have hQGne : QG ≠ ⊥ := by
      intro hbot
      apply hQM₀ne
      apply (Subgroup.map_eq_bot_iff_of_injective
        QM₀ M.subtype_injective).mp
      simpa [QG] using hbot
    have hAQG : A ≤ Subgroup.normalizer (QG : Set G) := by
      calc
        A = AM.map M.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hExc.A_le).symm
        _ ≤ (Subgroup.normalizer (QM₀ : Set M)).map M.subtype :=
          Subgroup.map_mono (by simpa [QM₀] using hAMQK)
        _ ≤ Subgroup.normalizer (QG : Set G) := by
          simpa [QG] using QM₀.le_normalizer_map M.subtype

    have hAMnotCentQM₀ :
        ¬ AM ≤ Subgroup.centralizer (QM₀ : Set M) := by
      intro hcent
      have hQM₀KM : QM₀ ≤ KM := by
        dsimp [QM₀]
        exact Subgroup.map_subtype_le (QK : Subgroup KM)
      have hQM₀C : QM₀ ≤ C := by
        exact le_inf hQM₀KM (Subgroup.le_centralizer_iff.mp hcent)
      have hdivRel : C.relIndex KM ∣ QM₀.relIndex KM :=
        Subgroup.relIndex_dvd_of_le_left KM hQM₀C
      have hrelQM₀ : QM₀.relIndex KM = QK.index := by
        calc
          QM₀.relIndex KM =
              ((QK : Subgroup KM).map KM.subtype).relIndex
                ((⊤ : Subgroup KM).map KM.subtype) := by
                  rw [show QM₀ =
                    (QK : Subgroup KM).map KM.subtype from rfl,
                    ← MonoidHom.range_eq_map, Subgroup.range_subtype]
          _ = (QK : Subgroup KM).relIndex ⊤ :=
            Subgroup.relIndex_map_map_of_injective _ _
              KM.subtype_injective
          _ = QK.index :=
            (QK : Subgroup KM).relIndex_top_right
      apply QK.not_dvd_index
      rw [← hrelQM₀]
      exact hqCindex.trans hdivRel
    have hAnotCentQG :
        ¬ A ≤ Subgroup.centralizer (QG : Set G) := by
      intro hcent
      apply hAMnotCentQM₀
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      apply M.subtype_injective
      exact Subgroup.mem_centralizer_iff.mp
        (hcent ha) ((x : M) : G)
          ⟨x, hx, rfl⟩

    have hcopQGA : (Nat.card QG).Coprime (Nat.card A) := by
      obtain ⟨n, hQGcard⟩ := IsPGroup.iff_card.mp hQGq
      apply Nat.coprime_of_dvd
      intro r hr hrQ hrA
      have hrPowQ : r ∣ q ^ n := by
        rwa [← hQGcard]
      have hrq : r = q :=
        Nat.prime_eq_prime_of_dvd_pow hr hq hrPowQ
      have hrPowA : r ∣ p ^ 2 := by
        simpa only [hExc.A_rank_two.card_eq] using hrA
      have hrp : r = p :=
        Nat.prime_eq_prime_of_dvd_pow hr hExc.prime hrPowA
      exact hpq (hrp.symm.trans hrq)

    have hCQGne : centralizerWithin QG A ≠ ⊥ := by
      intro hCQGbot
      let Q₀ : Subgroup G := centerWithin QG
      have hQ₀QG : Q₀ ≤ QG := centralizerWithin_le_left QG QG
      letI : Nontrivial QG := QG.nontrivial_iff_ne_bot.mpr hQGne
      have hQ₀ne : Q₀ ≠ ⊥ := by
        dsimp [Q₀]
        exact centerWithin_ne_bot QG hQGq
      have hQ₀q : IsPGroup q Q₀ := hQGq.to_le hQ₀QG
      letI : IsSolvable Q₀ := by
        letI : Group.IsNilpotent Q₀ := hQ₀q.isNilpotent
        infer_instance
      have hAQ₀ : A ≤ Subgroup.normalizer (Q₀ : Set G) := by
        dsimp [Q₀]
        rw [← map_center_eq_centerWithin QG]
        exact hAQG.trans
          (characteristic_map_subtype_le_normalizer
            QG (Subgroup.center QG))
      have hCQ₀bot : centralizerWithin Q₀ A = ⊥ := by
        apply le_antisymm _ bot_le
        rw [← hCQGbot]
        exact centralizerWithin_mono_left hQ₀QG
      have hcopQ₀A : (Nat.card Q₀).Coprime (Nat.card A) :=
        hcopQGA.coprime_dvd_left (Subgroup.card_dvd_of_le hQ₀QG)
      have hcommAQ₀ : ⁅A, Q₀⁆ = Q₀ := by
        apply le_antisymm
        · exact Subgroup.le_normalizer_iff_commutator_le_right.mp hAQ₀
        · have hgen :=
            le_commutator_sup_centralizerWithin_of_coprime
              hAQ₀ hcopQ₀A
          simpa [hCQ₀bot] using hgen

      have hStructure := exceptional_structure hM hExc P hAP
      dsimp only at hStructure
      rcases hStructure with
        ⟨_, _, A₁, A₂, hA₁A, hA₁rank,
          hA₂A, hA₂rank, hA₁neA₂, hregA₁, hregA₂⟩
      have hA₁A₂ : A₁ ⊔ A₂ = A :=
        (rankTwo_distinct_lines_11 hExc.A_rank_two
          ⟨hA₁A, hA₁rank⟩ ⟨hA₂A, hA₂rank⟩
          hA₁neA₂).2
      have hQ₀M : Q₀ ≤ M := hQ₀QG.trans hQGM
      have hQ₀sigmaCompl :
          IsPiNumber (sigmaPrimes M)ᶜ (Nat.card Q₀) :=
        hQ₀q.isPiNumber_natCard hqCompl
      have hQ₀pCompl :
          IsPiNumber ({p} : Set ℕ)ᶜ (Nat.card Q₀) :=
        hQ₀q.isPiNumber_natCard (by simpa using hpq.symm)
      have hQ₀comm : IsMulCommutative Q₀ := inferInstance
      have hA₁MN :
          A₁ ≤ M ⊓ Subgroup.normalizer (Q₀ : Set G) :=
        le_inf (hA₁A.trans hExc.A_le) (hA₁A.trans hAQ₀)
      have hA₂MN :
          A₂ ≤ M ⊓ Subgroup.normalizer (Q₀ : Set G) :=
        le_inf (hA₂A.trans hExc.A_le) (hA₂A.trans hAQ₀)
      have hR₁ := commG_sigma'_1Elem_cyclic hM hQ₀M
        hQ₀sigmaCompl hExc.sigma_compl hA₁rank hA₁MN
        hregA₁ hQ₀pCompl hQ₀comm
      have hR₂ := commG_sigma'_1Elem_cyclic hM hQ₀M
        hQ₀sigmaCompl hExc.sigma_compl hA₂rank hA₂MN
        hregA₂ hQ₀pCompl hQ₀comm
      dsimp only at hR₁ hR₂
      let Q₀M : Subgroup M := Q₀.subgroupOf M
      let A₁M : Subgroup M := A₁.subgroupOf M
      let A₂M : Subgroup M := A₂.subgroupOf M
      let R₁M : Subgroup M := (⁅Q₀, A₁⁆).subgroupOf M
      let R₂M : Subgroup M := (⁅Q₀, A₂⁆).subgroupOf M
      let N : Subgroup M := R₁M ⊔ R₂M
      have hR₁normal : R₁M.Normal := by
        simpa [R₁M] using hR₁.2.2
      have hR₂normal : R₂M.Normal := by
        simpa [R₂M] using hR₂.2.2
      letI : R₁M.Normal := hR₁normal
      letI : R₂M.Normal := hR₂normal
      have hNnormal : N.Normal := by
        dsimp [N]
        infer_instance
      letI : N.Normal := hNnormal
      have hA₁A₂M : A₁M ⊔ A₂M = AM := by
        rw [← Subgroup.subgroupOf_sup
          (hA₁A.trans hExc.A_le) (hA₂A.trans hExc.A_le),
          hA₁A₂]
      have hcommQ₀A : ⁅Q₀, A⁆ = Q₀ := by
        rw [Subgroup.commutator_comm, hcommAQ₀]
      have hcommQ₀AM : ⁅Q₀M, AM⁆ = Q₀M := by
        rw [← subgroupOf_commutator_eq hQ₀M hExc.A_le,
          hcommQ₀A]
      have hQ₀MN : Q₀M ≤ N := by
        rw [← hcommQ₀AM, ← hA₁A₂M]
        apply commutator_sup_le_of_normal
        · rw [← subgroupOf_commutator_eq hQ₀M
            (hA₁A.trans hExc.A_le)]
          exact le_sup_left
        · rw [← subgroupOf_commutator_eq hQ₀M
            (hA₂A.trans hExc.A_le)]
          exact le_sup_right
      have hcommQ₀Ale : ⁅Q₀, A⁆ ≤ Q₀ :=
        Subgroup.le_normalizer_iff_commutator_le_left.mp hAQ₀
      have hNQ₀M : N ≤ Q₀M := by
        apply sup_le
        · dsimp [R₁M, Q₀M]
          exact Subgroup.subgroupOf_mono M
            ((Subgroup.commutator_mono le_rfl hA₁A).trans
              hcommQ₀Ale)
        · dsimp [R₂M, Q₀M]
          exact Subgroup.subgroupOf_mono M
            ((Subgroup.commutator_mono le_rfl hA₂A).trans
              hcommQ₀Ale)
      have hQ₀MeqN : Q₀M = N := le_antisymm hQ₀MN hNQ₀M
      have hQ₀Mnormal : Q₀M.Normal := by
        rw [hQ₀MeqN]
        exact hNnormal
      have hNQ₀eqM : Subgroup.normalizer (Q₀ : Set G) = M :=
        mmax_normal hM hQ₀M hQ₀Mnormal hQ₀ne
      have hNQGQ₀ : Subgroup.normalizer (QG : Set G) ≤
          Subgroup.normalizer (Q₀ : Set G) := by
        dsimp [Q₀]
        rw [← map_center_eq_centerWithin QG]
        exact characteristic_map_subtype_le_normalizer
          QG (Subgroup.center QG)
      have hNQGM : Subgroup.normalizer (QG : Set G) ≤ M := by
        rwa [← hNQ₀eqM]
      have hqSigma : q ∈ sigmaPrimes M := by
        refine ⟨hq, QM, ?_⟩
        simpa [ambientSylow, QG, hQM₀eq] using hNQGM
      exact hqCompl hqSigma

    have hQGnotCyclic : ¬ IsCyclic QG := by
      intro hQGcyclic
      have hOmegaCentWithin :=
        map_omegaOne_le_centralizerWithin_of_cyclic
          hQGq hQGcyclic hQGne hCQGne
      have hOmegaCent :
          (omegaOne q QG).map QG.subtype ≤
            Subgroup.centralizer (A : Set G) :=
        hOmegaCentWithin.trans inf_le_right
      have hACentOmega : A ≤ Subgroup.centralizer
          (((omegaOne q QG).map QG.subtype : Subgroup G) : Set G) :=
        Subgroup.le_centralizer_iff.mp hOmegaCent
      have hACentQG : A ≤ Subgroup.centralizer (QG : Set G) :=
        coprime_odd_faithful_omegaOne_of_odd_card
          hQGq hAQG hcopQGA (mFT_odd QG) hACentOmega
      exact hAnotCentQG hACentQG
    have hRankTwoQG :
        ∃ B₀ : Subgroup QG,
          IsElementaryAbelianOfRank q 2 B₀ := by
      by_contra hnone
      apply hQGnotCyclic
      exact (odd_pgroup_isCyclic_iff_no_elementaryAbelian_rank_two
        hQGq (mFT_odd QG)).2 hnone
    obtain ⟨B₀, hB₀⟩ := hRankTwoQG
    let B : Subgroup G := B₀.map QG.subtype
    have hB : IsElementaryAbelianOfRank q 2 B := by
      dsimp [B]
      exact hB₀.map_of_injective QG.subtype QG.subtype_injective
    have hBQG : B ≤ QG := by
      dsimp [B]
      exact Subgroup.map_subtype_le B₀
    have hBM : B ≤ M := hBQG.trans hQGM
    have hRankM : HasElementaryAbelianPRankTwo q M := by
      refine ⟨⟨B, hBM, hB⟩, ?_⟩
      rintro ⟨F, hFM, hF⟩
      exact hqCompl (alpha_sub_sigma hM
        ⟨hq, F, hFM, hF⟩)
    have hBmax : IsPMaxElem q (⊤ : Subgroup G) B :=
      sigma'_rank2_max hM hqCompl hRankM hBM hB
    have hCQGp : IsPGroup q (centralizerWithin QG A) :=
      hQGq.to_le (centralizerWithin_le_left QG A)
    have hqCQG : q ∣ Nat.card (centralizerWithin QG A) :=
      hCQGp.card_eq_or_dvd.resolve_left (by
        intro hcard
        exact hCQGne
          (Subgroup.eq_bot_of_card_eq (centralizerWithin QG A) hcard))
    have hqCA : q ∣
        Nat.card (Subgroup.centralizer (A : Set G)) :=
      hqCQG.trans (Subgroup.card_dvd_of_le inf_le_right)
    have hQGpi : IsPiNumber ({q} : Set ℕ) (Nat.card QG) :=
      hQGq.isPiNumber_natCard (Set.mem_singleton q)
    obtain ⟨Qstar, hQstarMax, hQGQstar⟩ :=
      max_normed_exists (A : Set G) ({q} : Set ℕ) QG
        hQGpi hAQG
    obtain ⟨Pstar, hAPstar, _, _, hNarrow⟩ :=
      max_normed_2Elem_signaliser hpq hExc.A_rank_two
        (exceptional_pmaxElem hM hExc P hAP)
        hQstarMax hqCA
    have hQstarNarrow :
        Submission.OddOrder.BG.Section05.IsNarrow q Qstar := by
      intro _
      exact ⟨B, hB,
        hBmax.of_le le_top (hBQG.trans hQGQstar)⟩
    have hPstarCent : (Pstar : Subgroup G) ≤
        Subgroup.centralizer (Qstar : Set G) :=
      hNarrow hQstarNarrow
    have hACentQG : A ≤ Subgroup.centralizer (QG : Set G) :=
      hAPstar.trans (hPstarCent.trans
        (Subgroup.centralizer_le hQGQstar))
    exact (hAnotCentQG hACentQG).elim

end

end Submission.OddOrder.BG.Section11
