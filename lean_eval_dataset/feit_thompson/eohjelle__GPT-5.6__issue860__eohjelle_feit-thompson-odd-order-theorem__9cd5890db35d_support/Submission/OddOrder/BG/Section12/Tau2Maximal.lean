import Submission.OddOrder.BG.Section12.SigmaComplementContext
import Submission.OddOrder.BG.Section09.RankThreeUniqueness
import Submission.OddOrder.BG.Section03.SemiregularConjugation
import Submission.OddOrder.MathlibSupport.CharacteristicUnderNormalizer
import Submission.OddOrder.MathlibSupport.CoprimeAbelianCocyclicCentralizerGeneration
import Submission.OddOrder.MathlibSupport.ElementaryAbelianSup
import Submission.OddOrder.MathlibSupport.PElementCyclic

/-!
# Bender--Glauberman Section 12: maximal subgroups at a tau-two prime

This file ports `BGsection12.v`, lines 487--753: Proposition 12.4,
Theorem 12.5, Corollary 12.6, and the two regularity assertions attached to
a decomposed sigma complement.  Numerical rank assertions from the source
are stated using elementary-abelian subgroups of fixed cardinal rank.
-/

namespace Submission.OddOrder.BG.Section12

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section05
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section09
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.BG.Section11
open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.PF
open scoped Pointwise IsMulCommutative

noncomputable section

universe u

private theorem map_conj_one_12_1
    {G : Type*} [Group G] (H : Subgroup G) :
    H.map (MulAut.conj 1).toMonoidHom = H := by
  convert H.map_id using 1
  ext x
  simp

/-- The proposition-valued form of Theorem 12.5(b)--(f). -/
structure Tau2Context
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G) (p : ℕ) (A : Subgroup G) : Prop where
  sylow_abelian :
    ∀ P : Sylow p M, IsMulCommutative (ambientSylow M P)
  omegaOne_eq :
    ∀ P : Sylow p M, A ≤ ambientSylow M P →
      (omegaOne p (ambientSylow M P)).map
        (ambientSylow M P).subtype = A
  normalizer_sylow_not_le :
    ∀ P : Sylow p M, A ≤ ambientSylow M P →
      ¬ Subgroup.normalizer (ambientSylow M P : Set G) ≤ M
  sigma_sup_A_normal :
    ((sigmaCore M ⊔ A).subgroupOf M).Normal
  centralizerWithin_eq_bot :
    centralizerWithin (sigmaCore M) A = ⊥
  maximal_intersection_eq_bot :
    ∀ {Mstar : Subgroup G},
      Mstar ∈ minSimple_max_groups_of (G := G) (A : Set G) →
      Mstar ≠ M →
      sigmaCore M ⊓ Mstar = ⊥
  exists_rankOne_regular :
    ∃ A₁ : Subgroup G, A₁ ≤ A ∧
      IsElementaryAbelianOfRank p 1 A₁ ∧
      centralizerWithin (sigmaCore M) A₁ = ⊥

/-- The proposition-valued form of Corollary 12.6(a), (b), (c), and (f). -/
structure Tau2ComplementContext
    {G : Type u} [Group G] [Finite G]
    (M E : Subgroup G) (p : ℕ) (A : Subgroup G) : Prop where
  A_le_E : A ≤ E
  A_normal : (A.subgroupOf E).Normal
  A_normalizer_le : E ≤ Subgroup.normalizer (A : Set G)
  rankOne_iff :
    ∀ X : Subgroup G,
      (X ≤ E ∧ IsElementaryAbelianOfRank p 1 X) ↔
      (X ≤ A ∧ IsElementaryAbelianOfRank p 1 X)
  centralizer_le_E : Subgroup.centralizer (A : Set G) ≤ E
  normalizer_inf_M_eq :
    Subgroup.normalizer (A : Set G) ⊓ M = E
  normalizer_not_le_M :
    ¬ Subgroup.normalizer (A : Set G) ≤ M
  line_centralizer_unique :
    ∀ {X : Subgroup G}, X ≤ E →
      IsElementaryAbelianOfRank p 1 X →
      centralizerWithin (sigmaCore M) X ≠ ⊥ →
      minSimple_max_groups_of (G := G)
        (Subgroup.centralizer (X : Set G) : Set G) = {M}
  disjoint_sigma_of_nonconj :
    ∀ {Mstar : Subgroup G},
      Mstar ∈ minSimple_max_groups (G := G) →
      (∀ g : G,
        Mstar ≠ M.map (MulAut.conj g).toMonoidHom) →
      sigmaCore M ⊓ sigmaCore Mstar = ⊥ ∧
        Disjoint (sigmaPrimes M) (sigmaPrimes Mstar)

/-- Corollary 12.6(d), (e), together with the containment used later in
Sections 12 and 13. -/
structure Tau2RegularContext
    {G : Type u} [Group G] [Finite G]
    (M E₁ E₂ E₃ : Subgroup G) (p : ℕ) (A : Subgroup G) : Prop where
  E₃_regular :
    IsSemiregularConjugation (sigmaCore M) E₃
  centralizer_E₁_regular :
    IsSemiregularConjugation (sigmaCore M)
      (centralizerWithin E₁ A)
  A_le_E₂ : A ≤ E₂

/-- A `pi`-subgroup is contained in a normal `pi`-Hall subgroup. -/
private theorem isPiNumber_le_normal_isHall_12_4
    {K : Type u} [Group K] [Finite K] {pi : Set ℕ}
    {N L : Subgroup K} (hNnormal : N.Normal)
    (hNHall : IsHall pi N) (hLpi : IsPiNumber pi (Nat.card L)) :
    L ≤ N := by
  letI : N.Normal := hNnormal
  have hcop : (Nat.card L).Coprime N.index := by
    apply Nat.coprime_of_dvd
    intro q hq hqL hqIndex
    exact hNHall.isPiNumber_index hq hqIndex (hLpi hq hqL)
  intro x hxL
  let quotientN : K →* K ⧸ N := QuotientGroup.mk' N
  have horderL : orderOf (quotientN x) ∣ Nat.card L :=
    (orderOf_map_dvd quotientN x).trans (L.orderOf_dvd_natCard hxL)
  have horderIndex : orderOf (quotientN x) ∣ N.index := by
    simpa only [N.index_eq_card] using orderOf_dvd_natCard (quotientN x)
  have horderOne : orderOf (quotientN x) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horderL horderIndex
  have hquotientOne : quotientN x = 1 :=
    orderOf_eq_one_iff.mp horderOne
  exact (QuotientGroup.eq_one_iff x).mp
    (by simpa [quotientN] using hquotientOne)

/-- A proper cocyclic subgroup of an elementary-abelian group of rank two
is a line. -/
private theorem rank_one_of_cocyclic_rank_two
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {A C : Subgroup G}
    (hA : IsElementaryAbelianOfRank p 2 A) (hCA : C ≤ A)
    (hCnormal : (C.subgroupOf A).Normal)
    (hquot : IsCyclic (A ⧸ C.subgroupOf A)) (hCne : C ≠ A) :
    IsElementaryAbelianOfRank p 1 C := by
  let CA : Subgroup A := C.subgroupOf A
  letI : CA.Normal := by simpa [CA] using hCnormal
  let Q := A ⧸ CA
  letI : IsCyclic Q := by simpa [Q, CA] using hquot
  letI : DecidableEq Q := Classical.decEq Q
  have hCgroup : IsElementaryAbelianGroup p C :=
    { isPGroup :=
        (hA.isPGroup.to_subgroup CA).of_equiv
          (Subgroup.subgroupOfEquivOfLe hCA)
      commutative := by
        letI : IsMulCommutative A := hA.commutative
        apply isMulCommutative_iff.mpr
        intro x y
        apply Subtype.ext
        exact congrArg (fun z : A ↦ (z : G))
          (mul_comm (⟨x, hCA x.property⟩ : A)
            (⟨y, hCA y.property⟩ : A))
      pow_eq_one := by
        intro x
        apply Subtype.ext
        exact congrArg (fun z : A ↦ (z : G))
          (hA.pow_eq_one (⟨x, hCA x.property⟩ : A)) }
  have hQp : IsPGroup p Q := by
    dsimp [Q]
    exact hA.isPGroup.to_quotient CA
  have hQpow : ∀ x : Q, x ^ p = 1 := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective CA x
    simpa only [map_pow, map_one] using
      congrArg (QuotientGroup.mk' CA) (hA.pow_eq_one a)
  have hQne : Nat.card Q ≠ 1 := by
    intro hcard
    have htop : CA = ⊤ := Subgroup.index_eq_one.mp (by
      simpa only [CA.index_eq_card, Q] using hcard)
    apply hCne
    apply le_antisymm hCA
    intro a ha
    have haCA : (⟨a, ha⟩ : A) ∈ CA := by rw [htop]; trivial
    exact haCA
  letI := Fintype.ofFinite Q
  have hQle : Nat.card Q ≤ p := by
    rw [Nat.card_eq_fintype_card]
    simpa only [hQpow, Finset.filter_true, Finset.card_univ] using
      (IsCyclic.card_pow_eq_one_le (α := Q)
        (Fact.out : p.Prime).pos)
  have hpQ : p ∣ Nat.card Q :=
    hQp.card_eq_or_dvd.resolve_left hQne
  have hQcard : Nat.card Q = p := by
    have hp_le : p ≤ Nat.card Q :=
      Nat.le_of_dvd (Nat.card_pos (α := Q)) hpQ
    exact Nat.le_antisymm hQle hp_le
  have hfactor : Nat.card A = Nat.card Q * Nat.card C := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup,
      Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
        (H := C) (K := A) hCA]
  have hCcard : Nat.card C = p := by
    have hm : p * Nat.card C = p * p := by
      calc
        p * Nat.card C = Nat.card Q * Nat.card C := by rw [hQcard]
        _ = Nat.card A := hfactor.symm
        _ = p * p := by rw [hA.card_eq, pow_two]
    exact Nat.mul_left_cancel (Fact.out : p.Prime).pos hm
  exact
    { isPGroup := hCgroup.isPGroup
      commutative := hCgroup.commutative
      pow_eq_one := hCgroup.pow_eq_one
      card_eq := by simpa using hCcard }

/-- A characteristic subgroup, mapped into an ambient group, is preserved
by the full ambient normalizer. -/
private theorem characteristic_map_subtype_le_normalizer_12
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
    have hcancel : g⁻¹ * (g * r * g⁻¹) * (g⁻¹)⁻¹ = r := by
      group
    simpa only [hcancel] using this

/-- The ambient image of `Omega_1(Z(P))` is nontrivial in a nontrivial
finite `p`-group. -/
private theorem omegaOneCenterAmbient_ne_bot_12
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {P : Subgroup G}
    (hPp : IsPGroup p P) (hPne : P ≠ ⊥) :
    omegaOneCenterAmbient p P ≠ ⊥ := by
  letI : Nontrivial P := P.nontrivial_iff_ne_bot.mpr hPne
  let Z : Subgroup P := Subgroup.center P
  have hZne : Z ≠ ⊥ := by
    letI : Group.IsNilpotent P := hPp.isNilpotent
    exact Group.IsNilpotent.center_ne_bot P
  have hZp : IsPGroup p Z := hPp.to_subgroup Z
  have hZcard : Nat.card Z ≠ 1 :=
    (Z.one_lt_card_iff_ne_bot.mpr hZne).ne'
  have hOmegaNe : omegaOne p Z ≠ ⊥ :=
    omegaOne_ne_bot_of_isPGroup hZp hZcard
  have hCenterOmegaNe :
      Submission.OddOrder.BG.Section05.omegaOneCenter p P ≠ ⊥ := by
    dsimp [Submission.OddOrder.BG.Section05.omegaOneCenter, Z]
    exact (not_congr (Subgroup.map_eq_bot_iff_of_injective
      (omegaOne p (Subgroup.center P))
      (Subgroup.center P).subtype_injective)).mpr hOmegaNe
  dsimp [omegaOneCenterAmbient]
  exact (not_congr (Subgroup.map_eq_bot_iff_of_injective
    (Submission.OddOrder.BG.Section05.omegaOneCenter p P)
    P.subtype_injective)).mpr hCenterOmegaNe

/-- If the alpha core is trivial, the derived subgroup of the maximal
subgroup is nilpotent. -/
private theorem commutator_isNilpotent_of_alphaCore_eq_bot_12
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hbot : alphaCore M = ⊥) :
    Group.IsNilpotent (_root_.commutator M) := by
  have hsubbot : (alphaCore M).subgroupOf M = ⊥ := by
    simp [hbot]
  have hqnil := Malpha_quo_nil hM
  let eQ :
      (M ⧸ (alphaCore M).subgroupOf M) ≃*
        (M ⧸ (⊥ : Subgroup M)) :=
    QuotientGroup.quotientMulEquivOfEq hsubbot
  have heQrange : eQ.toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr eQ.surjective
  have hmapQ :
      (_root_.commutator
          (M ⧸ (alphaCore M).subgroupOf M)).map
            eQ.toMonoidHom =
        _root_.commutator (M ⧸ (⊥ : Subgroup M)) := by
    simpa only [heQrange, _root_.commutator_def] using
      (map_commutator_eq
        (M ⧸ (alphaCore M).subgroupOf M) eQ.toMonoidHom)
  let eQD :
      _root_.commutator
          (M ⧸ (alphaCore M).subgroupOf M) ≃*
        _root_.commutator (M ⧸ (⊥ : Subgroup M)) :=
    (eQ.subgroupMap
      (_root_.commutator
        (M ⧸ (alphaCore M).subgroupOf M))).trans
      (MulEquiv.subgroupCongr hmapQ)
  letI : Group.IsNilpotent
      (_root_.commutator (M ⧸ (⊥ : Subgroup M))) :=
    Group.nilpotent_of_mulEquiv eQD
  let e : (M ⧸ (⊥ : Subgroup M)) ≃* M :=
    QuotientGroup.quotientBot
  have herange : e.toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr e.surjective
  have hmap :
      (_root_.commutator (M ⧸ (⊥ : Subgroup M))).map
          e.toMonoidHom = _root_.commutator M := by
    simpa only [herange, _root_.commutator_def] using
      (map_commutator_eq (M ⧸ (⊥ : Subgroup M)) e.toMonoidHom)
  let eD : _root_.commutator (M ⧸ (⊥ : Subgroup M)) ≃*
      _root_.commutator M :=
    (e.subgroupMap
      (_root_.commutator (M ⧸ (⊥ : Subgroup M)))).trans
      (MulEquiv.subgroupCongr hmap)
  exact Group.nilpotent_of_mulEquiv eD

/-- A rank-two elementary-abelian group contains a line. -/
private theorem exists_rank_one_le_rank_two_12
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : IsElementaryAbelianOfRank p 2 A) :
    ∃ X : Subgroup G, X ≤ A ∧
      IsElementaryAbelianOfRank p 1 X := by
  have hpLe : p ^ 1 ≤ Nat.card A := by
    rw [hA.card_eq]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
  obtain ⟨X₀, hX₀card⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card
      (G := A) (Fact.out : p.Prime) hA.isPGroup hpLe
  let X : Subgroup G := X₀.map A.subtype
  have hX₀ : IsElementaryAbelianOfRank p 1 X₀ := by
    letI : IsMulCommutative A := hA.commutative
    refine
      { isPGroup := hA.isPGroup.to_subgroup X₀
        commutative := by infer_instance
        pow_eq_one := ?_
        card_eq := hX₀card }
    intro x
    apply Subtype.ext
    exact hA.pow_eq_one (x : A)
  exact ⟨X, Subgroup.map_subtype_le X₀,
    hX₀.map_of_injective A.subtype A.subtype_injective⟩

/-- Put an ambient elementary-abelian subgroup into an ambient copy of a
Sylow subgroup of a subgroup. -/
private theorem exists_sylow_containing_12
    {G : Type u} [Group G] [Finite G]
    {M A : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hAM : A ≤ M) (hAp : IsPGroup p A) :
    ∃ P : Sylow p M, A ≤ ambientSylow M P := by
  let AM : Subgroup M := A.subgroupOf M
  let eA : AM ≃* A := Subgroup.subgroupOfEquivOfLe hAM
  have hAMp : IsPGroup p AM := hAp.of_equiv eA.symm
  obtain ⟨P, hAMP⟩ := hAMp.exists_le_sylow
  refine ⟨P, ?_⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hAM]
  exact Subgroup.map_mono hAMP

/-- Every Sylow subgroup at an alpha prime contains a rank-three
elementary-abelian subgroup. -/
private theorem sylow_has_rank_three_of_mem_alpha_12
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hpAlpha : p ∈ alphaPrimes M) (P : Sylow p M) :
    HasElementaryAbelianRankAtLeast p 3 (ambientSylow M P) := by
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
  let D : Subgroup G := C.map M.subtype
  exact ⟨D, Subgroup.map_mono hCP,
    hC.map_of_injective M.subtype M.subtype_injective⟩

/-- A nonunique normalizer of a line has a maximal overgroup different
from the prescribed maximal subgroup. -/
private theorem exists_other_maximal_over_line_normalizer_12
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M A C : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hM : M ∈ minSimple_max_groups (G := G))
    (hAll : ∀ {X : Subgroup G}, X ≤ A →
      IsElementaryAbelianOfRank p 1 X →
      minSimple_max_groups_of (G := G)
        (Subgroup.normalizer (X : Set G) : Set G) ≠ {M})
    (hCA : C ≤ A) (hC : IsElementaryAbelianOfRank p 1 C) :
    ∃ H : Subgroup G,
      H ∈ minSimple_max_groups (G := G) ∧ H ≠ M ∧
        Subgroup.normalizer (C : Set G) ≤ H := by
  classical
  have hCproper : C < ⊤ := mFT_pgroup_proper C hC.isPGroup
  have hNproper : Subgroup.normalizer (C : Set G) < ⊤ :=
    mFT_norm_proper C hC.ne_bot hCproper
  obtain ⟨H₀, hH₀, hNH₀⟩ :=
    mmax_exists (Subgroup.normalizer (C : Set G)) hNproper
  by_contra hnone
  have hH₀eq : H₀ = M := by
    by_contra hH₀ne
    exact hnone ⟨H₀, hH₀, hH₀ne, hNH₀⟩
  apply hAll hCA hC
  apply Set.Subset.antisymm
  · intro H hH
    have hHM : H = M := by
      by_contra hHne
      exact hnone ⟨H, hH.1, hHne, hH.2⟩
    simp [hHM]
  · intro H hH
    have hHM : H = M := Set.mem_singleton_iff.mp hH
    subst H
    exact ⟨hM, hH₀eq ▸ hNH₀⟩

/-- Under the nonuniqueness hypothesis, no centralizer of a line in `M`
has elementary-abelian rank three at any prime. -/
private theorem no_rank_three_centralizer_line_12
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M A C : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hM : M ∈ minSimple_max_groups (G := G))
    (hAll : ∀ {X : Subgroup G}, X ≤ A →
      IsElementaryAbelianOfRank p 1 X →
      minSimple_max_groups_of (G := G)
        (Subgroup.normalizer (X : Set G) : Set G) ≠ {M})
    (hCA : C ≤ A) (hC : IsElementaryAbelianOfRank p 1 C) :
    ∀ q : ℕ, q.Prime →
      ¬ HasElementaryAbelianRankAtLeast q 3
        (centralizerWithin M C) := by
  classical
  obtain ⟨H, hH, hHne, hNCH⟩ :=
    exists_other_maximal_over_line_normalizer_12 hM hAll hCA hC
  intro q hq hRank
  have hCentProper : centralizerWithin M C < ⊤ :=
    sub_mmax_proper hM (centralizerWithin_le_left M C)
  have hUnique : centralizerWithin M C ∈
      minSimple_uniq_max_groups (G := G) :=
    rank3_Uniqueness hCentProper ⟨q, hq, hRank⟩
  have hFamily : minSimple_max_groups_of (G := G)
      (centralizerWithin M C : Set G) = {M} :=
    def_uniq_mmax hUnique hM (centralizerWithin_le_left M C)
  have hCentH : centralizerWithin M C ≤ H := by
    intro x hx
    exact hNCH
      (Subgroup.centralizer_le_normalizer (C : Set G) hx.2)
  exact hHne (eq_uniq_mmax hFamily hH hCentH)

/-- Centralizer generation in the precise form used twice in Proposition
12.4. -/
private theorem core_le_centralizerWithin_of_nonunique_lines_12
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M A K : Subgroup G} {p : ℕ} [Fact p.Prime]
    {pi : Set ℕ}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hAM : A ≤ M) (hA : IsElementaryAbelianOfRank p 2 A)
    (hKM : K ≤ M) (hKnormal : (K.subgroupOf M).Normal)
    (hKpi : IsPiNumber pi (Nat.card K)) (hpCompl : p ∈ piᶜ)
    (hAll : ∀ {X : Subgroup G}, X ≤ A →
      IsElementaryAbelianOfRank p 1 X →
      minSimple_max_groups_of (G := G)
        (Subgroup.normalizer (X : Set G) : Set G) ≠ {M})
    (hline : ∀ {C H : Subgroup G}, C ≤ A →
      IsElementaryAbelianOfRank p 1 C →
      H ∈ minSimple_max_groups (G := G) → H ≠ M →
      Subgroup.normalizer (C : Set G) ≤ H →
      A ≤ Subgroup.centralizer ((K ⊓ H : Subgroup G) : Set G)) :
    K ≤ centralizerWithin M A := by
  classical
  have hAnormK : A ≤ Subgroup.normalizer (K : Set G) :=
    hAM.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp hKnormal)
  have hcop : (Nat.card K).Coprime (Nat.card A) :=
    hKpi.coprime_compl
      (hA.isPGroup.isPiNumber_natCard hpCompl)
  have hKsol : IsSolvable K :=
    mFT_sol (lt_of_le_of_lt hKM (mmax_proper hM))
  apply le_of_centralizerWithin_cocyclic_le_of_coprime_abelian_solvable
    hA.commutative (hA.not_isCyclic (Fact.out : p.Prime))
    hAnormK hcop hKsol
  intro C hCA hCnormal hquot
  by_cases hCeq : C = A
  · subst C
    exact centralizerWithin_mono_left hKM
  have hC : IsElementaryAbelianOfRank p 1 C :=
    rank_one_of_cocyclic_rank_two hA hCA hCnormal hquot hCeq
  obtain ⟨H, hH, hHne, hNCH⟩ :=
    exists_other_maximal_over_line_normalizer_12 hM hAll hCA hC
  have hACent := hline hCA hC hH hHne hNCH
  intro x hx
  refine ⟨hKM hx.1, ?_⟩
  intro a ha
  have hxH : x ∈ H :=
    hNCH (Subgroup.centralizer_le_normalizer (C : Set G) hx.2)
  exact (Subgroup.mem_centralizer_iff.mp (hACent ha)
    x ⟨hx.1, hxH⟩).symm

/-- Transport nilpotence from the derived subgroup to the sigma core. -/
private theorem sigmaCore_isNilpotent_of_alphaCore_eq_bot_12
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hbot : alphaCore M = ⊥) :
    Group.IsNilpotent (sigmaCore M) := by
  let D₀ : Subgroup M := _root_.commutator M
  let D : Subgroup G := D₀.map M.subtype
  have hD₀nil : Group.IsNilpotent D₀ :=
    commutator_isNilpotent_of_alphaCore_eq_bot_12 hM hbot
  have hDnil : Group.IsNilpotent D := by
    letI : Group.IsNilpotent D₀ := hD₀nil
    exact Group.nilpotent_of_mulEquiv
      (D₀.equivMapOfInjective M.subtype M.subtype_injective)
  have hSD : sigmaCore M ≤ D := by
    simpa [D, D₀] using Msigma_der1 hM
  let SD : Subgroup D := (sigmaCore M).subgroupOf D
  let eS : SD ≃* sigmaCore M := Subgroup.subgroupOfEquivOfLe hSD
  letI : Group.IsNilpotent D := hDnil
  letI : Group.IsNilpotent SD := inferInstance
  exact Group.nilpotent_of_mulEquiv eS

/-- Proposition 12.4 in the branch where every line has more than the
prescribed maximal subgroup above its normalizer. -/
private theorem p2Elem_mmax_all_lines_12
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M A : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hM : M ∈ minSimple_max_groups (G := G))
    (hAM : A ≤ M) (hA : IsElementaryAbelianOfRank p 2 A)
    (hAll : ∀ {A₀ : Subgroup G}, A₀ ≤ A →
      IsElementaryAbelianOfRank p 1 A₀ →
      minSimple_max_groups_of (G := G)
        (Subgroup.normalizer (A₀ : Set G) : Set G) ≠ {M}) :
    Subgroup.centralizer (A : Set G) ≤ M ∧
      p ∈ sigmaPrimes M ∧ alphaCore M = ⊥ ∧
        Group.IsNilpotent (sigmaCore M) := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨C, hCA, hC⟩ := exists_rank_one_le_rank_two_12 hA
  have hNoRankA : ∀ q : ℕ, q.Prime →
      ¬ HasElementaryAbelianRankAtLeast q 3
        (centralizerWithin M A) := by
    intro q hq hRank
    rcases hRank with ⟨F, hFC, hF⟩
    exact no_rank_three_centralizer_line_12 hM hAll hCA hC q hq
      ⟨F, hFC.trans (centralizerWithin_antitone_right hCA), hF⟩

  have hpSigma : p ∈ sigmaPrimes M := by
    by_contra hpNotSigma
    have hSigmaCent : sigmaCore M ≤ centralizerWithin M A :=
      core_le_centralizerWithin_of_nonunique_lines_12
        (pi := sigmaPrimes M) hM hAM hA (sigmaCore_le M)
        (sigmaCore_normal M) (sigmaCore_isPiNumber M)
        hpNotSigma hAll (by
          intro C H hCA hC hH hHne hNCH
          exact (nonuniq_p2Elem_cent_sigma hp hM hH hHne
            hAM hA hCA hC hNCH).1 hpNotSigma)
    have hNoRankTwo :=
      sub'cent_sigma_rank1 hM hAM
        (hA.isPGroup.isPiNumber_natCard hpNotSigma) p hp
    apply hNoRankTwo
    refine ⟨A, ?_, hA⟩
    intro a ha
    refine ⟨ha, ?_⟩
    intro s hs
    exact ((mem_centralizerWithin.mp (hSigmaCent hs)).2 a ha).symm

  obtain ⟨P, hAP⟩ :=
    exists_sylow_containing_12 hAM hA.isPGroup
  let PG : Subgroup G := ambientSylow M P
  have hPGp : IsPGroup p PG := by
    dsimp [PG, ambientSylow]
    exact P.isPGroup'.map M.subtype
  have hPGM : PG ≤ M := by
    dsimp [PG, ambientSylow]
    exact Subgroup.map_subtype_le (P : Subgroup M)
  have hPGne : PG ≠ ⊥ := by
    intro hbot
    apply hA.ne_bot
    exact eq_bot_iff.mpr (hAP.trans (le_of_eq hbot))
  let Z : Subgroup G := omegaOneCenterAmbient p PG
  have hZPG : Z ≤ PG :=
    (omegaOneCenterAmbient_le_centerWithin p PG).trans
      (centralizerWithin_le_left PG PG)
  have hZcenter : Z ≤ centerWithin PG :=
    omegaOneCenterAmbient_le_centerWithin p PG
  have hZpow : ∀ z : G, z ∈ Z → z ^ p = 1 := by
    intro z hz
    rcases hz with ⟨zP, hzP, rfl⟩
    have hzPPow :
        (⟨zP, hzP⟩ :
          Submission.OddOrder.BG.Section05.omegaOneCenter p PG) ^ p = 1 :=
      Submission.OddOrder.BG.Section05.omegaOneCenter_pow_eq_one
        (G := PG) p ⟨zP, hzP⟩
    exact congrArg
      (fun x : Submission.OddOrder.BG.Section05.omegaOneCenter p PG ↦
        (x : G)) hzPPow

  have hZA : Z ≤ A := by
    by_contra hnot
    obtain ⟨z, hzZ, hzA⟩ := Set.not_subset.mp hnot
    have hzNe : z ≠ 1 := fun hz ↦ hzA (hz ▸ A.one_mem)
    have hzOrder : orderOf z = p :=
      ((Nat.dvd_prime hp).mp
        (orderOf_dvd_of_pow_eq_one (hZpow z hzZ))).resolve_left
          (by simpa only [orderOf_eq_one_iff] using hzNe)
    let X : Subgroup G := Subgroup.zpowers z
    have hXcard : Nat.card X = p := by
      dsimp [X]
      rw [Nat.card_zpowers, hzOrder]
    have hX : IsElementaryAbelianOfRank p 1 X :=
      isElementaryAbelianOfRank_one_of_card_eq_prime hXcard
    have hXZ : X ≤ Z := Subgroup.zpowers_le.mpr hzZ
    have hXPG : X ≤ PG := hXZ.trans hZPG
    have hXAfalse : ¬ X ≤ A := by
      intro hXA
      exact hzA (hXA (Subgroup.mem_zpowers z))
    have hdisXA : Disjoint X A := by
      letI : Fact (Nat.card X).Prime := ⟨hXcard ▸ hp⟩
      rcases (A.subgroupOf X).eq_bot_or_eq_top_of_prime_card with
        hbot | htop
      · exact disjoint_comm.mp (Subgroup.subgroupOf_eq_bot.mp hbot)
      · exact (hXAfalse (Subgroup.subgroupOf_eq_top.mp htop)).elim
    have hXcentA : X ≤ Subgroup.centralizer (A : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact ((mem_centerWithin.mp (hZcenter (hXZ hx))).2 a
        (hAP ha))
    let AP : Subgroup PG := A.subgroupOf PG
    let XP : Subgroup PG := X.subgroupOf PG
    have hAPrank : IsElementaryAbelianOfRank p 2 AP :=
      hA.subgroupOf hAP
    have hXPrank : IsElementaryAbelianOfRank p 1 XP :=
      hX.subgroupOf hXPG
    have hdisP : Disjoint AP XP := by
      rw [Subgroup.disjoint_def]
      intro y hyAP hyXP
      apply Subtype.ext
      have hyG : (y : G) ∈ X ⊓ A := ⟨hyXP, hyAP⟩
      have hyBot : (y : G) ∈ (⊥ : Subgroup G) := by
        rw [← disjoint_iff.mp hdisXA]
        exact hyG
      exact Subgroup.mem_bot.mp hyBot
    have hcommP : ∀ a ∈ AP, ∀ x ∈ XP, Commute a x := by
      intro a ha x hx
      change a * x = x * a
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp (hXcentA hx) a ha
    have hSupRank : IsElementaryAbelianOfRank p 3 (AP ⊔ XP) := by
      simpa using
        (isElementaryAbelianOfRank_sup_of_disjoint_of_commute
          hPGp hAPrank hXPrank hdisP hcommP)
    let F : Subgroup G := (AP ⊔ XP).map PG.subtype
    have hF : IsElementaryAbelianOfRank p 3 F :=
      hSupRank.map_of_injective PG.subtype PG.subtype_injective
    have hF_eq : F = A ⊔ X := by
      dsimp [F, AP, XP]
      rw [Subgroup.map_sup,
        Subgroup.map_subgroupOf_eq_of_le hAP,
        Subgroup.map_subgroupOf_eq_of_le hXPG]
    have hFCent : F ≤ centralizerWithin M A := by
      rw [hF_eq]
      refine le_inf (sup_le hAM (hXPG.trans hPGM)) ?_
      exact sup_le
        (Subgroup.le_centralizer_iff_isMulCommutative.mpr
          hA.commutative)
        hXcentA
    exact hNoRankA p hp ⟨F, hFCent, hF⟩

  have hZne : Z ≠ ⊥ :=
    omegaOneCenterAmbient_ne_bot_12 hPGp hPGne
  obtain ⟨zZ, hzZne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  let z : G := zZ
  have hzZ : z ∈ Z := zZ.property
  have hzNe : z ≠ 1 := by
    intro hz
    apply hzZne
    apply Subtype.ext
    exact hz
  let X : Subgroup G := Subgroup.zpowers z
  have hzOrder : orderOf z = p :=
    ((Nat.dvd_prime hp).mp
      (orderOf_dvd_of_pow_eq_one (hZpow z hzZ))).resolve_left
        (by simpa only [orderOf_eq_one_iff] using hzNe)
  have hXcard : Nat.card X = p := by
    dsimp [X]
    rw [Nat.card_zpowers, hzOrder]
  have hX : IsElementaryAbelianOfRank p 1 X :=
    isElementaryAbelianOfRank_one_of_card_eq_prime hXcard
  have hXZ : X ≤ Z := Subgroup.zpowers_le.mpr hzZ
  have hXA : X ≤ A := hXZ.trans hZA
  have hPGCentX : PG ≤ centralizerWithin M X := by
    intro y hy
    refine ⟨hPGM hy, ?_⟩
    intro x hx
    exact ((mem_centerWithin.mp (hZcenter (hXZ hx))).2 y hy).symm
  have hpNotAlpha : p ∉ alphaPrimes M := by
    intro hpAlpha
    rcases sylow_has_rank_three_of_mem_alpha_12 hpAlpha P with
      ⟨F, hFPG, hF⟩
    exact no_rank_three_centralizer_line_12 hM hAll hXA hX p hp
      ⟨F, hFPG.trans hPGCentX, hF⟩

  have hAlphaCent : alphaCore M ≤ centralizerWithin M A :=
    core_le_centralizerWithin_of_nonunique_lines_12
      (pi := alphaPrimes M) hM hAM hA (alphaCore_le M)
      (alphaCore_normal M) (alphaCore_isPiNumber M)
      hpNotAlpha hAll (by
        intro C H hCA hC hH hHne hNCH
        exact (nonuniq_p2Elem_cent_sigma hp hM hH hHne
          hAM hA hCA hC hNCH).2 hpNotAlpha)

  have hAlphaBot : alphaCore M = ⊥ := by
    by_contra hAlphaNe
    have hcard : Nat.card (alphaCore M) ≠ 1 := by
      intro hc
      exact hAlphaNe (Subgroup.card_eq_one.mp hc)
    obtain ⟨q, hq, hqCard⟩ := Nat.exists_prime_and_dvd hcard
    letI : Fact q.Prime := ⟨hq⟩
    have hqAlpha : q ∈ alphaPrimes M :=
      alphaCore_isPiNumber M hq hqCard
    rcases hqAlpha.2 with ⟨E, hEM, hE⟩
    let EM : Subgroup M := E.subgroupOf M
    let AlphaM : Subgroup M := (alphaCore M).subgroupOf M
    have hEMpi : IsPiNumber (alphaPrimes M) (Nat.card EM) := by
      rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
        (H := E) (K := M) hEM]
      exact hE.isPGroup.isPiNumber_natCard hqAlpha
    have hEMAlpha : EM ≤ AlphaM :=
      isPiNumber_le_normal_isHall_12_4
        (by simpa [AlphaM] using alphaCore_normal M)
        (by simpa [AlphaM] using Malpha_Hall hM) hEMpi
    have hEAlpha : E ≤ alphaCore M := by
      intro e he
      exact hEMAlpha
        (show (⟨e, hEM he⟩ : M) ∈ EM from he)
    exact hNoRankA q hq ⟨E, hEAlpha.trans hAlphaCent, hE⟩

  have hSigmaNil : Group.IsNilpotent (sigmaCore M) :=
    sigmaCore_isNilpotent_of_alphaCore_eq_bot_12 hM hAlphaBot

  have hCentM : Subgroup.centralizer (A : Set G) ≤ M := by
    let SM : Subgroup M := (sigmaCore M).subgroupOf M
    let PM : Subgroup M := (P : Subgroup M)
    have hPMpi : IsPiNumber (sigmaPrimes M) (Nat.card PM) :=
      P.isPGroup'.isPiNumber_natCard hpSigma
    have hPMS : PM ≤ SM :=
      isPiNumber_le_normal_isHall_12_4
        (by simpa [SM] using sigmaCore_normal M)
        (by simpa [SM] using Msigma_Hall hM) hPMpi
    let PS : Subgroup SM := PM.subgroupOf SM
    have hPSp : IsPGroup p PS := by
      let ePS : PS ≃* PM := Subgroup.subgroupOfEquivOfLe hPMS
      exact P.isPGroup'.of_equiv ePS.symm
    have hpPSindex : ¬ p ∣ PS.index := by
      intro hpIndex
      apply P.not_dvd_index
      have hpRel : p ∣ PM.relIndex SM := by
        change p ∣ (PM.subgroupOf SM).index
        exact hpIndex
      exact hpRel.trans (Subgroup.relIndex_dvd_index_of_le hPMS)
    let PSM : Sylow p SM := hPSp.toSylow hpPSindex
    have hSMnil : Group.IsNilpotent SM := by
      let eSM : SM ≃* sigmaCore M :=
        Subgroup.subgroupOfEquivOfLe (sigmaCore_le M)
      letI : Group.IsNilpotent (sigmaCore M) := hSigmaNil
      exact Group.nilpotent_of_mulEquiv eSM.symm
    have hPScore : pCore p SM = PS := by
      letI : Group.IsNilpotent SM := hSMnil
      simpa [PSM] using pCore_eq_sylow_of_isNilpotent PSM
    have hPSchar : PS.Characteristic := by
      rw [← hPScore]
      infer_instance
    have hSMnormal : SM.Normal := by
      simpa [SM] using sigmaCore_normal M
    letI : SM.Normal := hSMnormal
    letI : PS.Characteristic := hPSchar
    have hPMnormal : PM.Normal := by
      have hmapNormal : (PS.map SM.subtype).Normal := inferInstance
      simpa [PS, Subgroup.map_subgroupOf_eq_of_le hPMS] using hmapNormal
    have hPGsubEq : PG.subgroupOf M = PM := by
      apply Subgroup.map_injective M.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le hPGM]
      change (P : Subgroup M).map M.subtype =
        (P : Subgroup M).map M.subtype
      rfl
    letI : PM.Normal := hPMnormal
    have hPGnormal : (PG.subgroupOf M).Normal := by
      rw [hPGsubEq]
      infer_instance
    have hNPG : Subgroup.normalizer (PG : Set G) = M :=
      mmax_normal hM hPGM hPGnormal hPGne
    have hNPGZ : Subgroup.normalizer (PG : Set G) ≤
        Subgroup.normalizer (Z : Set G) := by
      simpa [Z, omegaOneCenterAmbient] using
        characteristic_map_subtype_le_normalizer_12 PG
          (Submission.OddOrder.BG.Section05.omegaOneCenter p PG)
    have hMnormZ : M ≤ Subgroup.normalizer (Z : Set G) := by
      rw [← hNPG]
      exact hNPGZ
    have hZnormal : (Z.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (hZPG.trans hPGM)).mpr hMnormZ
    have hNZ : Subgroup.normalizer (Z : Set G) = M :=
      mmax_normal hM (hZPG.trans hPGM) hZnormal hZne
    exact (Subgroup.centralizer_le hZA).trans
      ((Subgroup.centralizer_le_normalizer (Z : Set G)).trans
        (le_of_eq hNZ))

  exact ⟨hCentM, hpSigma, hAlphaBot, hSigmaNil⟩

/-- `BGsection12.v: p2Elem_mmax`, Proposition 12.4. -/
theorem p2Elem_mmax
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
          Group.IsNilpotent (sigmaCore M)) := by
  classical
  constructor
  · by_cases hAll : ∀ A₀ : Subgroup G, RankOneLineIn p A A₀ →
        minSimple_max_groups_of (G := G)
          (Subgroup.normalizer (A₀ : Set G) : Set G) ≠ {M}
    · exact (p2Elem_mmax_all_lines_12 hM hAM hA
        (fun {_} hA₀A hA₀ ↦ hAll _ ⟨hA₀A, hA₀⟩)).1
    · push Not at hAll
      obtain ⟨A₀, hA₀line, hfamily⟩ := hAll
      have hNA₀M : Subgroup.normalizer (A₀ : Set G) ≤ M :=
        (mem_uniq_mmax hfamily).2
      exact (Subgroup.centralizer_le hA₀line.1).trans
        ((Subgroup.centralizer_le_normalizer (A₀ : Set G)).trans
          hNA₀M)
  · intro hAll
    exact (p2Elem_mmax_all_lines_12 hM hAM hA
      (fun {_} hA₀A hA₀ ↦ hAll _ ⟨hA₀A, hA₀⟩)).2

/-- A `tau₂` rank-two subgroup supplies the exceptional line used by the
Section 11 structure theorems. -/
private theorem exists_exceptional_line_of_tau2_12
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M A : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hM : M ∈ minSimple_max_groups (G := G))
    (hpTau : p ∈ tau2Primes M)
    (hAM : A ≤ M) (hA : IsElementaryAbelianOfRank p 2 A) :
    ∃ A₀ : Subgroup G, ∃ P : Sylow p M,
      exceptional_FTmaximal p M A₀ A ∧
        A ≤ ambientSylow M P := by
  classical
  have hnotAll : ¬ (∀ {A₀ : Subgroup G}, A₀ ≤ A →
      IsElementaryAbelianOfRank p 1 A₀ →
      minSimple_max_groups_of (G := G)
        (Subgroup.normalizer (A₀ : Set G) : Set G) ≠ {M}) := by
    intro hAll
    exact hpTau.2.1 ((p2Elem_mmax hM hAM hA).2
      (fun A₀ hA₀line ↦ hAll hA₀line.1 hA₀line.2)).1
  push Not at hnotAll
  obtain ⟨A₀, hA₀A, hA₀, hfamily⟩ := hnotAll
  have hNA₀M : Subgroup.normalizer (A₀ : Set G) ≤ M :=
    (mem_uniq_mmax hfamily).2
  have hExc : exceptional_FTmaximal p M A₀ A :=
    { prime := Fact.out
      sigma_compl := hpTau.2.1
      A_le := hAM
      A_rank_two := hA
      A₀_le := hA₀A
      A₀_rank_one := hA₀
      normalizer_A₀_le := hNA₀M }
  obtain ⟨P, hAP⟩ := exists_sylow_containing_12 hAM hA.isPGroup
  exact ⟨A₀, P, hExc, hAP⟩

/-- A normal nilpotent core contains the rank-two subgroup in a
normal ambient `p`-subgroup. -/
private theorem exists_normal_p_overgroup_in_nilpotent_core_12
    {G : Type u} [Group G] [Finite G]
    {H S A : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hSH : S ≤ H) (hSnormal : (S.subgroupOf H).Normal)
    (hSnil : Group.IsNilpotent S)
    (hAS : A ≤ S) (hAp : IsPGroup p A) :
    ∃ Q : Subgroup G, A ≤ Q ∧ Q ≤ S ∧ IsPGroup p Q ∧
      (Q.subgroupOf H).Normal := by
  let SS : Subgroup H := S.subgroupOf H
  let AH : Subgroup H := A.subgroupOf H
  have hAHSS : AH ≤ SS := by
    intro a ha
    exact hAS ha
  let AS : Subgroup SS := AH.subgroupOf SS
  have hASp : IsPGroup p AS := by
    let eAH : AH ≃* A :=
      Subgroup.subgroupOfEquivOfLe (hAS.trans hSH)
    have hAHp : IsPGroup p AH := hAp.of_equiv eAH.symm
    let eAS : AS ≃* AH :=
      Subgroup.subgroupOfEquivOfLe hAHSS
    exact hAHp.of_equiv eAS.symm
  obtain ⟨P, hASP⟩ := hASp.exists_le_sylow
  have hSSnil : Group.IsNilpotent SS := by
    let eSS : SS ≃* S := Subgroup.subgroupOfEquivOfLe hSH
    letI : Group.IsNilpotent S := hSnil
    exact Group.nilpotent_of_mulEquiv eSS.symm
  have hPCore : pCore p SS = (P : Subgroup SS) := by
    letI : Group.IsNilpotent SS := hSSnil
    exact pCore_eq_sylow_of_isNilpotent P
  have hPchar : (P : Subgroup SS).Characteristic := by
    rw [← hPCore]
    infer_instance
  letI : SS.Normal := hSnormal
  letI : (P : Subgroup SS).Characteristic := hPchar
  let PH : Subgroup H := (P : Subgroup SS).map SS.subtype
  have hPHnormal : PH.Normal := by
    dsimp [PH]
    infer_instance
  let Q : Subgroup G := PH.map H.subtype
  have hQS : Q ≤ S := by
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with ⟨y, hy, rfl⟩
    exact y.2
  have hQp : IsPGroup p Q :=
    (P.isPGroup'.map SS.subtype).map H.subtype
  have hAQ : A ≤ Q := by
    intro a ha
    let aH : H := ⟨a, hSH (hAS ha)⟩
    let aSS : SS := ⟨aH, hAS ha⟩
    have haAS : aSS ∈ AS := ha
    have haP : aSS ∈ (P : Subgroup SS) := hASP haAS
    have haPH : aH ∈ PH := ⟨aSS, haP, rfl⟩
    exact ⟨aH, haPH, rfl⟩
  have hQnormal : (Q.subgroupOf H).Normal := by
    have hcomap : Q.subgroupOf H = PH := by
      dsimp [Q]
      exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective PH
    rw [hcomap]
    exact hPHnormal
  exact ⟨Q, hAQ, hQS, hQp, hQnormal⟩

/-- `BGsection12.v: tau2_Msigma_nil`, Theorem 12.5(a). -/
theorem tau2_Msigma_nil
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G} {p : ℕ}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hpTau : p ∈ tau2Primes M) :
    Group.IsNilpotent (sigmaCore M) := by
  letI : Fact p.Prime := ⟨hpTau.1⟩
  rcases hpTau.2.2.1 with ⟨A, hAM, hA⟩
  obtain ⟨A₀, P, hExc, hAP⟩ :=
    exists_exceptional_line_of_tau2_12 hM hpTau hAM hA
  exact exceptional_sigma_nil hM hExc P hAP

/-- `BGsection12.v: tau2_context`, Theorem 12.5(b)--(f). -/
theorem tau2_context
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M A : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hM : M ∈ minSimple_max_groups (G := G))
    (hpTau : p ∈ tau2Primes M)
    (hAM : A ≤ M) (hA : IsElementaryAbelianOfRank p 2 A) :
    Tau2Context M p A := by
  classical
  obtain ⟨A₀, P₀, hExc, hAP₀⟩ :=
    exists_exceptional_line_of_tau2_12 hM hpTau hAM hA
  rcases exceptional_structure hM hExc P₀ hAP₀ with
    ⟨_hOmega₀, hRegA, A₁, A₂, hA₁A, hA₁,
      hA₂A, hA₂, hA₁neA₂, hRegA₁, hRegA₂⟩
  refine
    { sylow_abelian := ?_
      omegaOne_eq := ?_
      normalizer_sylow_not_le := ?_
      sigma_sup_A_normal :=
        exceptional_mul_sigma_normal hM hExc P₀ hAP₀
      centralizerWithin_eq_bot := hRegA
      maximal_intersection_eq_bot := ?_
      exists_rankOne_regular := ⟨A₁, hA₁A, hA₁, hRegA₁⟩ }
  · intro P
    exact exceptional_Sylow_abelian hM hExc P₀ hAP₀ P
  · intro P hAP
    exact (exceptional_structure hM hExc P hAP).1.symm
  · intro P _hAP
    exact sigma'_Sylow_contra (Fact.out : p.Prime) P hpTau.2.1
  · intro Mstar hMstarOf hMstarNe
    let T : Subgroup G := sigmaCore M ⊓ Mstar
    have hMstar : Mstar ∈ minSimple_max_groups (G := G) :=
      hMstarOf.1
    have hAMstar : A ≤ Mstar := hMstarOf.2
    by_cases hAllStar : ∀ {X : Subgroup G}, X ≤ A →
        IsElementaryAbelianOfRank p 1 X →
        minSimple_max_groups_of (G := G)
          (Subgroup.normalizer (X : Set G) : Set G) ≠ {Mstar}
    · have hStar := (p2Elem_mmax hMstar hAMstar hA).2
        (fun X hXline ↦ hAllStar hXline.1 hXline.2)
      have hpStarSigma : p ∈ sigmaPrimes Mstar := hStar.1
      have hStarNil : Group.IsNilpotent (sigmaCore Mstar) := hStar.2.2
      let SstarM : Subgroup Mstar :=
        (sigmaCore Mstar).subgroupOf Mstar
      let AstarM : Subgroup Mstar := A.subgroupOf Mstar
      have hAstarPi : IsPiNumber (sigmaPrimes Mstar)
          (Nat.card AstarM) := by
        rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
          (H := A) (K := Mstar) hAMstar]
        exact hA.isPGroup.isPiNumber_natCard hpStarSigma
      have hAstarS : AstarM ≤ SstarM :=
        isPiNumber_le_normal_isHall_12_4
          (by simpa [SstarM] using sigmaCore_normal Mstar)
          (by simpa [SstarM] using Msigma_Hall hMstar) hAstarPi
      have hASstar : A ≤ sigmaCore Mstar := by
        intro a ha
        exact hAstarS
          (show (⟨a, hAMstar ha⟩ : Mstar) ∈ AstarM from ha)
      obtain ⟨Q, hAQ, hQSstar, hQp, hQnormal⟩ :=
        exists_normal_p_overgroup_in_nilpotent_core_12
          (sigmaCore_le Mstar) (sigmaCore_normal Mstar)
          hStarNil hASstar hA.isPGroup
      have hMstarNormQ : Mstar ≤
          Subgroup.normalizer (Q : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer
          (hQSstar.trans (sigmaCore_le Mstar))).mp hQnormal
      have hAnormT : A ≤ Subgroup.normalizer (T : Set G) := by
        have hAnormS : A ≤
            Subgroup.normalizer (sigmaCore M : Set G) :=
          hAM.trans
            ((Subgroup.normal_subgroupOf_iff_le_normalizer
              (sigmaCore_le M)).mp (sigmaCore_normal M))
        have hAnormMstar : A ≤
            Subgroup.normalizer (Mstar : Set G) :=
          hAMstar.trans Subgroup.le_normalizer
        exact (le_inf hAnormS hAnormMstar).trans
          Subgroup.inf_normalizer_le_normalizer_inf
      have hcommT : ⁅T, A⁆ ≤ T :=
        Subgroup.le_normalizer_iff_commutator_le_left.mp hAnormT
      have hcommQ : ⁅T, A⁆ ≤ Q :=
        (Subgroup.commutator_mono le_rfl hAQ).trans
          (Subgroup.le_normalizer_iff_commutator_le_right.mp
            (inf_le_right.trans hMstarNormQ))
      have hTpi : IsPiNumber (sigmaPrimes M) (Nat.card T) :=
        (sigmaCore_isPiNumber M).of_dvd
          (Subgroup.card_dvd_of_le inf_le_left)
      have hQcompl : IsPiNumber (sigmaPrimes M)ᶜ (Nat.card Q) :=
        hQp.isPiNumber_natCard hpTau.2.1
      have hdis : Disjoint T Q :=
        Subgroup.disjoint_of_coprime_natCard
          (hTpi.coprime_compl hQcompl)
      have hcommBot : ⁅T, A⁆ = ⊥ := by
        apply le_antisymm ?_ bot_le
        exact (le_inf hcommT hcommQ).trans (disjoint_iff.mp hdis).le
      have hTCentA : T ≤ Subgroup.centralizer (A : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommBot
      apply le_antisymm ?_ bot_le
      rw [← hRegA]
      intro x hx
      exact ⟨hx.1, hTCentA hx⟩
    · push Not at hAllStar
      obtain ⟨X, hXA, hX, hfamily⟩ := hAllStar
      have hNXMstar : Subgroup.normalizer (X : Set G) ≤ Mstar :=
        (mem_uniq_mmax hfamily).2
      have hACentT : A ≤ Subgroup.centralizer (T : Set G) :=
        (nonuniq_p2Elem_cent_sigma (Fact.out : p.Prime)
          hM hMstar hMstarNe hAM hA hXA hX hNXMstar).1 hpTau.2.1
      apply le_antisymm ?_ bot_le
      rw [← hRegA]
      intro x hx
      refine ⟨hx.1, ?_⟩
      intro a ha
      exact (Subgroup.mem_centralizer_iff.mp (hACentT ha) x hx).symm

/-- `BGsection12.v: tau2_compl_context`, Corollary 12.6(a)--(c),(f). -/
theorem tau2_compl_context
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E A : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hpTau : p ∈ tau2Primes M)
    (hAE : A ≤ E) (hA : IsElementaryAbelianOfRank p 2 A) :
    Tau2ComplementContext M E p A := by
  classical
  have hAM : A ≤ M := hAE.trans hEM
  have hCtx := tau2_context hM hpTau hAM hA
  have hSD := sdprod_sigma hM hEM hHallE
  let SM : Subgroup M := (sigmaCore M).subgroupOf M
  let EM : Subgroup M := E.subgroupOf M
  let AM : Subgroup M := A.subgroupOf M
  have hSMnormal : SM.Normal := by
    simpa [SM] using sigmaCore_normal M
  letI : SM.Normal := hSMnormal
  have hSMdisEM : Disjoint SM EM := by
    simpa [SM, EM] using hSD.2.2.2.disjoint
  have hAMEM : AM ≤ EM := by
    intro a ha
    exact hAE ha
  have hInf : (SM ⊔ AM) ⊓ EM ≤ AM := by
    intro x hx
    rcases Subgroup.mem_sup_of_normal_left.mp hx.1 with
      ⟨s, hs, a, ha, hsa⟩
    have hsEM : s ∈ EM := by
      have hxa : x * a⁻¹ = s := by
        rw [← hsa]
        group
      rw [← hxa]
      exact EM.mul_mem hx.2 (EM.inv_mem (hAMEM ha))
    have hsOne : s = 1 := by
      have hsBot : s ∈ (⊥ : Subgroup M) := by
        rw [← disjoint_iff.mp hSMdisEM]
        exact ⟨hs, hsEM⟩
      exact Subgroup.mem_bot.mp hsBot
    rw [hsOne, one_mul] at hsa
    exact hsa ▸ ha
  have hConjA : ∀ e : G, e ∈ E → ∀ a : G, a ∈ A →
      e * a * e⁻¹ ∈ A := by
    intro e he a ha
    let eM : M := ⟨e, hEM he⟩
    let aM : M := ⟨a, hAM ha⟩
    have hU : (SM ⊔ AM).Normal := by
      simpa [SM, AM, Subgroup.subgroupOf_sup
        (sigmaCore_le M) hAM] using hCtx.sigma_sup_A_normal
    have hconjU : eM * aM * eM⁻¹ ∈ SM ⊔ AM :=
      hU.conj_mem aM
        ((show AM ≤ SM ⊔ AM from le_sup_right) (show aM ∈ AM from ha)) eM
    have hconjE : eM * aM * eM⁻¹ ∈ EM :=
      EM.mul_mem (EM.mul_mem he (hAMEM ha)) (EM.inv_mem he)
    exact hInf ⟨hconjU, hconjE⟩
  have hAnormal : (A.subgroupOf E).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hAE).mpr
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      exact hConjA e he a ha
    · intro ha
      have hback := hConjA e⁻¹ (E.inv_mem he)
        (e * a * e⁻¹) ha
      have hcancel : e⁻¹ * (e * a * e⁻¹) * (e⁻¹)⁻¹ = a := by
        group
      simpa only [hcancel] using hback
  have hEnormA : E ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAE).mp hAnormal

  have hRankOne : ∀ X : Subgroup G,
      (X ≤ E ∧ IsElementaryAbelianOfRank p 1 X) ↔
      (X ≤ A ∧ IsElementaryAbelianOfRank p 1 X) := by
    intro X
    constructor
    · rintro ⟨hXE, hX⟩
      have hXnormA : X ≤ Subgroup.normalizer (A : Set G) :=
        hXE.trans hEnormA
      have hSupP : IsPGroup p (A ⊔ X : Subgroup G) :=
        hA.isPGroup.to_sup_of_normal_left' hX.isPGroup hXnormA
      obtain ⟨P, hSupPsub⟩ :=
        exists_sylow_containing_12
          (sup_le hAM (hXE.trans hEM)) hSupP
      have hAP : A ≤ ambientSylow M P :=
        le_sup_left.trans hSupPsub
      have hOmega := hCtx.omegaOne_eq P hAP
      refine ⟨?_, hX⟩
      intro x hx
      rw [← hOmega]
      have hxSup : x ∈ A ⊔ X :=
        (show X ≤ A ⊔ X from le_sup_right) hx
      let xP : ambientSylow M P :=
        ⟨x, hSupPsub hxSup⟩
      have hxpow : xP ^ p = 1 := by
        apply Subtype.ext
        exact congrArg (fun y : X ↦ (y : G))
          (hX.pow_eq_one ⟨x, hx⟩)
      exact ⟨xP, mem_omegaOne_of_pow_eq_one p hxpow, rfl⟩
    · rintro ⟨hXA, hX⟩
      exact ⟨hXA.trans hAE, hX⟩

  have hNormInf : Subgroup.normalizer (A : Set G) ⊓ M = E := by
    apply le_antisymm ?_ (le_inf hEnormA hEM)
    intro x hx
    let xM : M := ⟨x, hx.2⟩
    have hxTop : xM ∈ SM ⊔ EM := by
      rw [hSD.2.2.2.sup_eq_top]
      trivial
    rcases Subgroup.mem_sup_of_normal_left.mp hxTop with
      ⟨s, hsS, e, heE, hse⟩
    have heNorm : (e : G) ∈ Subgroup.normalizer (A : Set G) :=
      hEnormA heE
    have hsEq : (s : G) = x * (e : G)⁻¹ := by
      have hseG := congrArg Subtype.val hse
      change (s : G) * (e : G) = x at hseG
      calc
        (s : G) = (s : G) * (e : G) * (e : G)⁻¹ := by group
        _ = x * (e : G)⁻¹ := by rw [hseG]
    have hsNorm : (s : G) ∈ Subgroup.normalizer (A : Set G) := by
      rw [hsEq]
      exact (Subgroup.normalizer (A : Set G)).mul_mem hx.1
        ((Subgroup.normalizer (A : Set G)).inv_mem heNorm)
    have hsCent : (s : G) ∈ centralizerWithin (sigmaCore M) A := by
      refine ⟨hsS, ?_⟩
      intro a ha
      have hconjA : (s : G) * a * (s : G)⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp hsNorm a).mp ha
      let c : G := (s : G) * a * (s : G)⁻¹ * a⁻¹
      have hcA : c ∈ A := A.mul_mem hconjA (A.inv_mem ha)
      have hcS : c ∈ sigmaCore M := by
        have hMnormS : M ≤
            Subgroup.normalizer (sigmaCore M : Set G) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer
            (sigmaCore_le M)).mp (sigmaCore_normal M)
        have haconj : a * (s : G)⁻¹ * a⁻¹ ∈ sigmaCore M :=
          (Subgroup.mem_normalizer_iff.mp (hMnormS (hAM ha))
            ((s : G)⁻¹)).mp (SM.inv_mem hsS)
        have hsSigma : (s : G) ∈ sigmaCore M := hsS
        have hprod : (s : G) * (a * (s : G)⁻¹ * a⁻¹) ∈
            sigmaCore M :=
          (sigmaCore M).mul_mem hsSigma haconj
        simpa only [c, mul_assoc] using hprod
      have hcEM : c ∈ E := hAE hcA
      have hcBot : c ∈ (⊥ : Subgroup G) := by
        have hcSMEM : (⟨c, hEM hcEM⟩ : M) ∈ SM ⊓ EM :=
          ⟨hcS, hcEM⟩
        have : (⟨c, hEM hcEM⟩ : M) ∈ (⊥ : Subgroup M) := by
          rw [← disjoint_iff.mp hSMdisEM]
          exact hcSMEM
        exact Subgroup.mem_bot.mpr
          (congrArg Subtype.val (Subgroup.mem_bot.mp this))
      have hcOne : c = 1 := Subgroup.mem_bot.mp hcBot
      dsimp [c] at hcOne
      calc
        a * (s : G) =
            ((s : G) * a * (s : G)⁻¹ * a⁻¹)⁻¹ *
              (s : G) * a := by group
        _ = (s : G) * a := by rw [hcOne, inv_one, one_mul]
    have hsOne : (s : G) = 1 := by
      have hsBot : (s : G) ∈ (⊥ : Subgroup G) := by
        rw [← hCtx.centralizerWithin_eq_bot]
        exact hsCent
      exact Subgroup.mem_bot.mp hsBot
    have hseG := congrArg Subtype.val hse
    change (s : G) * (e : G) = x at hseG
    have hxE : x = (e : G) := by
      calc
        x = (s : G) * (e : G) := hseG.symm
        _ = (e : G) := by rw [hsOne, one_mul]
    rw [hxE]
    exact heE

  have hCentE : Subgroup.centralizer (A : Set G) ≤ E := by
    intro x hx
    rw [← hNormInf]
    exact ⟨Subgroup.centralizer_le_normalizer (A : Set G) hx,
      (p2Elem_mmax hM hAM hA).1 hx⟩

  have hNormNotM : ¬ Subgroup.normalizer (A : Set G) ≤ M := by
    intro hNormM
    obtain ⟨P, hAP⟩ := exists_sylow_containing_12 hAM hA.isPGroup
    let PG : Subgroup G := ambientSylow M P
    have hOmega := hCtx.omegaOne_eq P hAP
    change (omegaOne p PG).map PG.subtype = A at hOmega
    have hNPGOmega : Subgroup.normalizer (PG : Set G) ≤
        Subgroup.normalizer
          (((omegaOne p PG).map PG.subtype : Subgroup G) : Set G) :=
      characteristic_map_subtype_le_normalizer_12 PG (omegaOne p PG)
    have hNPGA : Subgroup.normalizer (PG : Set G) ≤
        Subgroup.normalizer (A : Set G) := by
      rw [hOmega] at hNPGOmega
      exact hNPGOmega
    exact hCtx.normalizer_sylow_not_le P hAP (hNPGA.trans hNormM)

  refine
    { A_le_E := hAE
      A_normal := hAnormal
      A_normalizer_le := hEnormA
      rankOne_iff := hRankOne
      centralizer_le_E := hCentE
      normalizer_inf_M_eq := hNormInf
      normalizer_not_le_M := hNormNotM
      line_centralizer_unique := ?_
      disjoint_sigma_of_nonconj := ?_ }
  · intro X hXE hX hCSXne
    have hXA : X ≤ A := (hRankOne X).mp ⟨hXE, hX⟩ |>.1
    have hAcentX : A ≤ Subgroup.centralizer (X : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      letI : IsMulCommutative A := hA.commutative
      exact congrArg Subtype.val
        (mul_comm (⟨x, hXA hx⟩ : A) (⟨a, ha⟩ : A))
    have hCproper : Subgroup.centralizer (X : Set G) < ⊤ :=
      mFT_cent_proper X hX.ne_bot
    obtain ⟨H, hH, hCXH⟩ :=
      mmax_exists (Subgroup.centralizer (X : Set G)) hCproper
    have hHEq : H = M := by
      by_contra hHne
      have hAH : A ≤ H := hAcentX.trans hCXH
      have hInfBot := hCtx.maximal_intersection_eq_bot
        (Mstar := H) ⟨hH, hAH⟩ hHne
      apply hCSXne
      apply le_antisymm ?_ bot_le
      intro s hs
      have hsInf : s ∈ sigmaCore M ⊓ H :=
        ⟨hs.1, hCXH hs.2⟩
      rw [hInfBot] at hsInf
      exact hsInf
    have hCXM : Subgroup.centralizer (X : Set G) ≤ M := by
      rw [← hHEq]
      exact hCXH
    apply Set.Subset.antisymm
    · intro L hL
      have hLEq : L = M := by
        by_contra hLne
        have hAL : A ≤ L := hAcentX.trans hL.2
        have hInfBot := hCtx.maximal_intersection_eq_bot
          (Mstar := L) ⟨hL.1, hAL⟩ hLne
        apply hCSXne
        apply le_antisymm ?_ bot_le
        intro s hs
        have hsInf : s ∈ sigmaCore M ⊓ L :=
          ⟨hs.1, hL.2 hs.2⟩
        rw [hInfBot] at hsInf
        exact hsInf
      simp [hLEq]
    · intro L hL
      have hLM : L = M := Set.mem_singleton_iff.mp hL
      subst L
      exact ⟨hM, hCXM⟩
  · intro Mstar hMstar hnotconj
    exact (sigma_disjoint hM hMstar hnotconj).2.2
      (tau2_Msigma_nil hM hpTau)

/-- The common maximal-overgroup argument for the two regularity clauses
of Corollary 12.6. -/
private theorem tau2_semiregular_of_tau13_actor_12
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M A R : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hM : M ∈ minSimple_max_groups (G := G))
    (hpTau : p ∈ tau2Primes M)
    (hAM : A ≤ M) (hA : IsElementaryAbelianOfRank p 2 A)
    (hRM : R ≤ M)
    (hClass : ∀ {q : ℕ}, q.Prime → q ∣ Nat.card R →
      q ∈ tau1Primes M ∨ q ∈ tau3Primes M)
    (hAcentR : A ≤ Subgroup.centralizer (R : Set G)) :
    IsSemiregularConjugation (sigmaCore M) R := by
  classical
  have hCtx := tau2_context hM hpTau hAM hA
  intro r hrNe s hfix
  have hrGNe : (r : G) ≠ 1 := by
    intro hrOne
    apply hrNe
    exact Subtype.ext hrOne
  let X : Subgroup G := Subgroup.zpowers (r : G)
  have hXne : X ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hrGNe
  have hXcard : Nat.card X ≠ 1 := by
    intro hc
    exact hXne (Subgroup.card_eq_one.mp hc)
  obtain ⟨q, hq, hqX⟩ := Nat.exists_prime_and_dvd hXcard
  letI : Fact q.Prime := ⟨hq⟩
  let QX : Sylow q X := Classical.choice Sylow.nonempty
  let Q : Subgroup G := (QX : Subgroup X).map X.subtype
  have hQp : IsPGroup q Q := QX.isPGroup'.map X.subtype
  have hQX : Q ≤ X := Subgroup.map_subtype_le (QX : Subgroup X)
  have hQXne : (QX : Subgroup X) ≠ ⊥ :=
    QX.ne_bot_of_dvd_card hqX
  have hQne : Q ≠ ⊥ := by
    intro hbot
    exact hQXne ((Subgroup.map_eq_bot_iff_of_injective
      (QX : Subgroup X) X.subtype_injective).mp hbot)
  have hXR : X ≤ R := Subgroup.zpowers_le.mpr r.property
  have hQM : Q ≤ M := hQX.trans hXR |>.trans hRM
  have hNQproper : Subgroup.normalizer (Q : Set G) < ⊤ :=
    mFT_norm_proper Q hQne (mFT_pgroup_proper Q hQp)
  obtain ⟨H, hH, hNQH⟩ :=
    mmax_exists (Subgroup.normalizer (Q : Set G)) hNQproper
  have hqR : q ∣ Nat.card R :=
    hqX.trans (Subgroup.card_dvd_of_le hXR)
  have hnotConj : ∀ g : G,
      H ≠ M.map (MulAut.conj g).toMonoidHom :=
    mmax_norm_notJ hM hH hQp hQM hNQH
      (Or.inr (hClass hq hqR))
  have hHneM : H ≠ M := by
    intro hEq
    have h := hnotConj 1
    apply h
    exact hEq.trans (map_conj_one_12_1 M).symm
  have hAH : A ≤ H := by
    exact hAcentR.trans (Subgroup.centralizer_le hXR)
      |>.trans (Subgroup.centralizer_le hQX)
      |>.trans (Subgroup.centralizer_le_normalizer (Q : Set G))
      |>.trans hNQH
  have hInfBot : sigmaCore M ⊓ H = ⊥ :=
    hCtx.maximal_intersection_eq_bot ⟨hH, hAH⟩ hHneM
  have hrs : Commute (r : G) (s : G) := by
    change (r : G) * (s : G) = (s : G) * (r : G)
    calc
      (r : G) * (s : G) =
          ((r : G) * (s : G) * (r : G)⁻¹) * (r : G) := by group
      _ = (s : G) * (r : G) := by rw [hfix]
  have hsCentQ : (s : G) ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hQX hx)
    rw [← hn]
    exact (hrs.zpow_left n).eq
  have hsH : (s : G) ∈ H :=
    hNQH (Subgroup.centralizer_le_normalizer (Q : Set G) hsCentQ)
  have hsBot : (s : G) ∈ (⊥ : Subgroup G) := by
    rw [← hInfBot]
    exact ⟨s.property, hsH⟩
  apply Subtype.ext
  exact Subgroup.mem_bot.mp hsBot

/-- `BGsection12.v: tau2_regular`, Corollary 12.6(d),(e), including the
implicit containment `A ≤ E₂`. -/
theorem tau2_regular
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E E₁ E₂ E₃ A : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hM : M ∈ minSimple_max_groups (G := G))
    (hCompl : sigma_complement M E E₁ E₂ E₃)
    (hpTau : p ∈ tau2Primes M)
    (hAE : A ≤ E) (hA : IsElementaryAbelianOfRank p 2 A) :
    Tau2RegularContext M E₁ E₂ E₃ p A := by
  classical
  have hAM : A ≤ M := hAE.trans hCompl.E_le_M
  have hSigma := sigma_compl_context hM hCompl
  have hTau := tau2_compl_context hM hCompl.E_le_M
    hCompl.hall_E hpTau hAE hA
  have hAE₂ : A ≤ E₂ := by
    let AE : Subgroup E := A.subgroupOf E
    let E₂E : Subgroup E := E₂.subgroupOf E
    have hAEpi : IsPiNumber (tau2Primes M) (Nat.card AE) := by
      rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
        (H := A) (K := E) hAE]
      exact hA.isPGroup.isPiNumber_natCard hpTau
    have hsub : AE ≤ E₂E :=
      normal_isPiNumber_le_isHall hTau.A_normal hAEpi
        (by simpa [E₂E] using hCompl.hall_E₂)
    intro a ha
    have haE₂E : (⟨a, hAE ha⟩ : E) ∈ E₂E := hsub ha
    exact haE₂E

  have hE₃centA : A ≤ Subgroup.centralizer (E₃ : Set G) := by
    let E₃E : Subgroup E := E₃.subgroupOf E
    let AE : Subgroup E := A.subgroupOf E
    have hE₃pi : IsPiNumber (tau3Primes M) (Nat.card E₃E) :=
      hCompl.hall_E₃.isPiNumber_card
    have hApi : IsPiNumber (tau3Primes M)ᶜ (Nat.card AE) := by
      rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
        (H := A) (K := E) hAE]
      exact hA.isPGroup.isPiNumber_natCard (tau3'2 M hpTau)
    have hdis : Disjoint E₃E AE :=
      Subgroup.disjoint_of_coprime_natCard
        (hE₃pi.coprime_compl hApi)
    letI : E₃E.Normal := hSigma.E₃_normal
    letI : AE.Normal := hTau.A_normal
    have hcommBot : ⁅E₃E, AE⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_of_disjoint hdis
    have hcent : E₃E ≤ Subgroup.centralizer (AE : Set E) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommBot
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro e₃ he₃
    let aE : AE := ⟨⟨a, hAE ha⟩, ha⟩
    let e₃E : E₃E := ⟨⟨e₃, hCompl.E₃_le_E he₃⟩, he₃⟩
    exact congrArg (fun x : E ↦ (x : G))
      (Subgroup.mem_centralizer_iff.mp (hcent e₃E.property)
        aE aE.property) |>.symm

  have hE₃class : ∀ {q : ℕ}, q.Prime → q ∣ Nat.card E₃ →
      q ∈ tau1Primes M ∨ q ∈ tau3Primes M := by
    intro q hq hqE₃
    right
    apply hCompl.hall_E₃.isPiNumber_card hq
    rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
      (H := E₃) (K := E) hCompl.E₃_le_E]
    exact hqE₃

  let R₁ : Subgroup G := centralizerWithin E₁ A
  have hR₁M : R₁ ≤ M :=
    (centralizerWithin_le_left E₁ A).trans hCompl.E₁_le_E
      |>.trans hCompl.E_le_M
  have hAcentR₁ : A ≤ Subgroup.centralizer (R₁ : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact (hr.2 a ha).symm
  have hR₁class : ∀ {q : ℕ}, q.Prime → q ∣ Nat.card R₁ →
      q ∈ tau1Primes M ∨ q ∈ tau3Primes M := by
    intro q hq hqR
    left
    apply hCompl.hall_E₁.isPiNumber_card hq
    have hqE₁ : q ∣ Nat.card E₁ :=
      hqR.trans (Subgroup.card_dvd_of_le
        (centralizerWithin_le_left E₁ A))
    rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
      (H := E₁) (K := E) hCompl.E₁_le_E]
    exact hqE₁

  exact
    { E₃_regular :=
        tau2_semiregular_of_tau13_actor_12 hM hpTau hAM hA
          (hCompl.E₃_le_E.trans hCompl.E_le_M)
          hE₃class hE₃centA
      centralizer_E₁_regular := by
        simpa [R₁] using
          (tau2_semiregular_of_tau13_actor_12 hM hpTau hAM hA
            hR₁M hR₁class hAcentR₁)
      A_le_E₂ := hAE₂ }

end

end Submission.OddOrder.BG.Section12
