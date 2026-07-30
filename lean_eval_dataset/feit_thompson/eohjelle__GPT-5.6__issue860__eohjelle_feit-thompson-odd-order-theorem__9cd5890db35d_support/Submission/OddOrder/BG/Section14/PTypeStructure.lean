import Submission.OddOrder.BG.Section14.SigmaDecompositionAndTypes
import Submission.OddOrder.BG.Section13.TauRegularity
import Submission.OddOrder.BG.Section12.SigmaEmbedding
import Submission.OddOrder.BG.Section03.FrobeniusSolvableKernel
import Submission.OddOrder.PF.Section03.InternalDirectProduct
import Submission.OddOrder.PF.Section05.InducedIrreducibles
import Submission.OddOrder.MathlibSupport.NormalizedTI
import Submission.OddOrder.MathlibSupport.WielandtSolvableFixpoint
import Submission.OddOrder.MathlibSupport.CoprimeHallConjugatorAdjustment
import Submission.OddOrder.MathlibSupport.CoprimeSolvableInvariantSylowConjugacy

/-!
# Bender--Glauberman Section 14: the structure of P-type maximal subgroups

This file ports `BGsection14.v`, from `Ptype_structure` through
`FT_signalizer_context` (Proposition 14.2, Corollary 14.3, and Theorem
14.4).  The long nested conjunctions in the source are represented by
records.  In particular, `PTypeStructure` has fields corresponding to
parts (a)--(g) of Proposition 14.2, while `FTSignalizerContext` separates
the assertions which hold for every sigma-length-one element from the
assertions requiring more than one sigma-maximal overgroup.

MathComp's relative normalizers and centralizers are intersections with an
ambient subgroup.  The centralizer operation already has a common Lean
adapter, `centralizerWithin`; `normalizerWithin` below is its normalizer
analogue.  Conjugates use `MulAut.conj`; reversing the conjugating element
does not change any quantified TI or transitivity assertion.
-/

namespace Submission.OddOrder.BG.Section14

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section09
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.BG.Section11
open Submission.OddOrder.BG.Section12
open Submission.OddOrder.BG.Section13
open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.PF
open scoped Pointwise IsMulCommutative

noncomputable section

universe u

/-- The normalizer of `X` inside `M`; this is MathComp's `'N_M(X)`. -/
def normalizerWithin {G : Type u} [Group G]
    (M X : Subgroup G) : Subgroup G :=
  M ⊓ Subgroup.normalizer (X : Set G)

/-- The full centralizer of an element, expressed through its cyclic
subgroup. -/
abbrev elementCentralizer {G : Type u} [Group G] (x : G) : Subgroup G :=
  Subgroup.centralizer (Subgroup.zpowers x : Set G)

/-- The relative centralizer of an element. -/
abbrev elementCentralizerWithin {G : Type u} [Group G]
    (M : Subgroup G) (x : G) : Subgroup G :=
  centralizerWithin M (Subgroup.zpowers x)

/-- The subgroup denoted `Kstar = 'C_(M`_sigma)(K)` in Proposition 14.2. -/
abbrev pTypeCentralizer {G : Type u} [Group G] [Finite G]
    (M K : Subgroup G) : Subgroup G :=
  centralizerWithin (sigmaCore M) K

/-- Part (g) of `Ptype_structure`, isolated because all four conclusions
have the additional Type-P2 hypothesis. -/
structure PTypeTwoStructure
    {G : Type u} [Group G] [Finite G]
    (M K : Subgroup G) : Prop where
  sigma_eq_beta : sigmaPrimes M = betaPrimes M
  card_K_prime : Nat.Prime (Nat.card K)
  sigmaCore_nilpotent : Group.IsNilpotent (sigmaCore M)
  sigmaCore_normalizedTI :
    IsNormalizedTI (subgroupNonidentity (sigmaCore M)) ⊤ M

/-- The proposition-valued expansion of Proposition 14.2.

The two semidirect-product fields in part (a) spell out the nested source
display `M`_sigma ><| (U ><| K) = M`.  The ambient Sylow subgroup in part
(e) is `ambientSylow M S`, since a Mathlib `Sylow p M` lives in the subtype
`M`. -/
structure PTypeStructureData
    {G : Type u} [Group G] [Finite G]
    (M K : Subgroup G) : Type u where
  /- (a) -/
  U : Subgroup G
  complement : KappaComplement M U K
  U_K_sdprod : IsInternalSemidirectProductIn U K (U ⊔ K)
  sigma_UK_sdprod :
    IsInternalSemidirectProductIn (sigmaCore M) (U ⊔ K) M
  U_abelian : IsMulCommutative U
  sigma_K_prime : IsPrimeAction (sigmaCore M) K
  U_K_semiregular : IsSemiregularConjugation U K

  /- (b) -/
  normalizer_direct :
    IsInternalDirectProductIn K (pTypeCentralizer M K)
      (normalizerWithin M K)
  rankOne_normalizer :
    ∀ {p : ℕ} [Fact p.Prime] {X : Subgroup G},
      RankOneLineIn p K X →
      normalizerWithin M X = normalizerWithin M K ∧
        ∀ {Mstar : Subgroup G},
          Mstar ∈ minSimple_max_groups_of (G := G)
            (Subgroup.normalizer (X : Set G) : Set G) →
          X ≤ sigmaCore Mstar

  /- (c) -/
  Kstar_ne_bot : pTypeCentralizer M K ≠ ⊥
  Kstar_line_unique :
    ∀ {p : ℕ} [Fact p.Prime] {X : Subgroup G},
      RankOneLineIn p (pTypeCentralizer M K) X →
      minSimple_max_groups_of (G := G)
        (Subgroup.centralizer (X : Set G) : Set G) = {M}

  /- (d) -/
  Kstar_TI_outside :
    ∀ g : G, g ∉ M →
      pTypeCentralizer M K ⊓
          M.map
            (MulAut.conj g).toMonoidHom = ⊥
  K_TI_off_normalizer :
    ∀ g : G, g ∈ M →
      g ∉ Subgroup.normalizer (K : Set G) →
      K ⊓ K.map (MulAut.conj g).toMonoidHom = ⊥

  /- (e) -/
  Kstar_sylow_unique :
    ∀ {p : ℕ} [Fact p.Prime],
      p ∈ primeSupport (Nat.card (pTypeCentralizer M K)) →
      ∀ S : Sylow p M,
        minSimple_max_groups_of (G := G)
            ((ambientSylow M S : Subgroup G) : Set G) = {M} ∧
          ¬ (ambientSylow M S : Subgroup G) ≤ pTypeCentralizer M K

  /- (f) -/
  sigma_inter_Kstar_le :
    ∀ {Y : Subgroup G},
      IsPiNumber (sigmaPrimes M) (Nat.card Y) →
      Y ⊓ pTypeCentralizer M K ≠ ⊥ →
      Y ≤ sigmaCore M

  /- (g) -/
  typeP2 : M ∈ typeP2MaximalSubgroups → PTypeTwoStructure M K

/-- Proposition-valued packaging of the structure data.  Choice below
provides stable named projections while keeping proofs of the proposition
proof-irrelevant. -/
def PTypeStructure
    {G : Type u} [Group G] [Finite G]
    (M K : Subgroup G) : Prop :=
  Nonempty (PTypeStructureData M K)

namespace PTypeStructure

variable {G : Type u} [Group G] [Finite G] {M K : Subgroup G}

noncomputable def witness (h : PTypeStructure M K) :
    PTypeStructureData M K :=
  Classical.choice h

noncomputable def U (h : PTypeStructure M K) : Subgroup G :=
  h.witness.U

theorem complement (h : PTypeStructure M K) :
    KappaComplement M h.U K := h.witness.complement

theorem U_K_sdprod (h : PTypeStructure M K) :
    IsInternalSemidirectProductIn h.U K (h.U ⊔ K) :=
  h.witness.U_K_sdprod

theorem sigma_UK_sdprod (h : PTypeStructure M K) :
    IsInternalSemidirectProductIn (sigmaCore M) (h.U ⊔ K) M :=
  h.witness.sigma_UK_sdprod

theorem U_abelian (h : PTypeStructure M K) :
    IsMulCommutative h.U := h.witness.U_abelian

theorem sigma_K_prime (h : PTypeStructure M K) :
    IsPrimeAction (sigmaCore M) K := h.witness.sigma_K_prime

theorem U_K_semiregular (h : PTypeStructure M K) :
    IsSemiregularConjugation h.U K := h.witness.U_K_semiregular

theorem normalizer_direct (h : PTypeStructure M K) :
    IsInternalDirectProductIn K (pTypeCentralizer M K)
      (normalizerWithin M K) := h.witness.normalizer_direct

theorem rankOne_normalizer (h : PTypeStructure M K) :
    ∀ {p : ℕ} [Fact p.Prime] {X : Subgroup G},
      RankOneLineIn p K X →
      normalizerWithin M X = normalizerWithin M K ∧
        ∀ {Mstar : Subgroup G},
          Mstar ∈ minSimple_max_groups_of (G := G)
            (Subgroup.normalizer (X : Set G) : Set G) →
          X ≤ sigmaCore Mstar :=
  h.witness.rankOne_normalizer

theorem Kstar_ne_bot (h : PTypeStructure M K) :
    pTypeCentralizer M K ≠ ⊥ := h.witness.Kstar_ne_bot

theorem Kstar_line_unique (h : PTypeStructure M K) :
    ∀ {p : ℕ} [Fact p.Prime] {X : Subgroup G},
      RankOneLineIn p (pTypeCentralizer M K) X →
      minSimple_max_groups_of (G := G)
        (Subgroup.centralizer (X : Set G) : Set G) = {M} :=
  h.witness.Kstar_line_unique

theorem Kstar_TI_outside (h : PTypeStructure M K) :
    ∀ g : G, g ∉ M →
      pTypeCentralizer M K ⊓
          M.map (MulAut.conj g).toMonoidHom = ⊥ :=
  h.witness.Kstar_TI_outside

theorem K_TI_off_normalizer (h : PTypeStructure M K) :
    ∀ g : G, g ∈ M →
      g ∉ Subgroup.normalizer (K : Set G) →
      K ⊓ K.map (MulAut.conj g).toMonoidHom = ⊥ :=
  h.witness.K_TI_off_normalizer

theorem Kstar_sylow_unique (h : PTypeStructure M K) :
    ∀ {p : ℕ} [Fact p.Prime],
      p ∈ primeSupport (Nat.card (pTypeCentralizer M K)) →
      ∀ S : Sylow p M,
        minSimple_max_groups_of (G := G)
            ((ambientSylow M S : Subgroup G) : Set G) = {M} ∧
          ¬ (ambientSylow M S : Subgroup G) ≤ pTypeCentralizer M K :=
  h.witness.Kstar_sylow_unique

theorem sigma_inter_Kstar_le (h : PTypeStructure M K) :
    ∀ {Y : Subgroup G},
      IsPiNumber (sigmaPrimes M) (Nat.card Y) →
      Y ⊓ pTypeCentralizer M K ≠ ⊥ →
      Y ≤ sigmaCore M :=
  h.witness.sigma_inter_Kstar_le

theorem typeP2 (h : PTypeStructure M K) :
    M ∈ typeP2MaximalSubgroups → PTypeTwoStructure M K :=
  h.witness.typeP2

end PTypeStructure

/-- The proposition-valued form of the five conclusions in
`kappa_compl_context`. -/
structure KappaComplementContext
    {G : Type u} [Group G] [Finite G]
    (M U K : Subgroup G) : Prop where
  U_sup_K_le_M : U ⊔ K ≤ M
  hall_sigma_complement :
    IsHall (sigmaPrimes M)ᶜ ((U ⊔ K).subgroupOf M)
  U_K_sdprod : IsInternalSemidirectProductIn U K (U ⊔ K)
  sigma_UK_sdprod :
    IsInternalSemidirectProductIn (sigmaCore M) (U ⊔ K) M
  sigma_K_prime : IsPrimeAction (sigmaCore M) K
  U_K_semiregular : IsSemiregularConjugation U K
  U_abelian_of_K_ne_bot : K ≠ ⊥ → IsMulCommutative U

/-- The first, unconditional half of Theorem 14.4. -/
structure FTSignalizerBasicContext
    {G : Type u} [Group G] [Finite G]
    (x : G) (N R : Subgroup G) : Prop where
  R_le_centralizer : R ≤ elementCentralizer x
  R_normal : (R.subgroupOf (elementCentralizer x)).Normal
  R_hall :
    IsHall (sigmaPrimes N)
      (R.subgroupOf (elementCentralizer x))
  transitive :
    ∀ {M L : Subgroup G},
      M ∈ sigmaMaximalOvergroups (Subgroup.zpowers x : Set G) →
      L ∈ sigmaMaximalOvergroups (Subgroup.zpowers x : Set G) →
      ∃ r : G, r ∈ R ∧
        L = M.map (MulAut.conj r).toMonoidHom
  card_eq :
    Nat.card R =
      (sigmaMaximalOvergroups (Subgroup.zpowers x : Set G)).ncard

/-- The four conclusions of Theorem 14.4 attached to one member of
`'M_sigma[x]`.  `centralizer_disjoint` is the directly usable form of the
intersection clause contained in `centralizer_sdprod`. -/
structure FTSignalizerOvergroupContext
    {G : Type u} [Group G] [Finite G]
    (x : G) (N R M : Subgroup G) : Prop where
  centralizer_sdprod :
    IsInternalSemidirectProductIn R
      (elementCentralizerWithin (M ⊓ N) x)
      (elementCentralizer x)
  centralizer_disjoint :
    R ⊓ elementCentralizerWithin (M ⊓ N) x = ⊥
  tau2_subset_sigma : tau2Primes N ⊆ sigmaPrimes M
  beta_control :
    primeSupport (Nat.card M) ∩ sigmaPrimes N ⊆ betaPrimes N
  hall_intersection :
    IsHall (sigmaPrimes N)ᶜ ((M ⊓ N).subgroupOf N)

/-- The assertions in Theorem 14.4 which require more than one
sigma-maximal overgroup. -/
structure FTSignalizerLargeContext
    {G : Type u} [Group G] [Finite G]
    (x : G) (N R : Subgroup G) : Prop where
  centralizer_maximal :
    minSimple_max_groups_of (G := G)
      ((elementCentralizer x : Subgroup G) : Set G) = {N}
  signalizer_ne_bot : R ≠ ⊥
  x_tau2 : IsPiNumber (tau2Primes N) (orderOf x)
  base_maximal : N ∈ minSimple_max_groups (G := G)
  centralizer_le_base : elementCentralizer x ≤ N
  base_type :
    N ∈ typeFMaximalSubgroups ∪ typeP2MaximalSubgroups
  overgroup_context :
    ∀ {M : Subgroup G},
      M ∈ sigmaMaximalOvergroups (Subgroup.zpowers x : Set G) →
      FTSignalizerOvergroupContext x N R M

/-- The complete proposition-valued form of Theorem 14.4. -/
structure FTSignalizerContext
    {G : Type u} [Group G] [Finite G]
    (x : G) (N R : Subgroup G) : Prop where
  basic : FTSignalizerBasicContext x N R
  small_signalizer :
    ¬ 1 < (sigmaMaximalOvergroups
      (Subgroup.zpowers x : Set G)).ncard →
      R = ⊥
  large :
    1 < (sigmaMaximalOvergroups
      (Subgroup.zpowers x : Set G)).ncard →
      FTSignalizerLargeContext x N R

/-- The two factors of an internal semidirect product have trivial
intersection in the common ambient group. -/
theorem internalSemidirectProduct_inf_eq_bot
    {G : Type u} [Group G] {A B H : Subgroup G}
    (h : IsInternalSemidirectProductIn A B H) :
    A ⊓ B = ⊥ := by
  apply le_antisymm
  · intro x hx
    let xH : H := ⟨x, h.1 hx.1⟩
    have hxA : xH ∈ A.subgroupOf H := hx.1
    have hxB : xH ∈ B.subgroupOf H := hx.2
    have hxbot : xH ∈ (⊥ : Subgroup H) :=
      h.2.2.2.disjoint.le_bot ⟨hxA, hxB⟩
    have hxone : xH = 1 := by simpa using hxbot
    simpa [xH] using congrArg Subtype.val hxone
  · exact bot_le

/-! ## Elementary source adapters -/

/-- A nonidentity finite-order element has a prime divisor of its order.
This is the `pdiv #[x]` choice used repeatedly in the source. -/
theorem exists_prime_mem_primeSupport_orderOf
    {G : Type u} [Group G] {x : G} (hx : x ≠ 1) :
    ∃ p : ℕ, p ∈ primeSupport (orderOf x) := by
  have horder : orderOf x ≠ 1 := by
    simpa [orderOf_eq_one_iff] using hx
  obtain ⟨p, hp, hpOrder⟩ := Nat.exists_prime_and_dvd horder
  exact ⟨p, hp, hpOrder⟩

/-- Prime support of an element in a subgroup is contained in the prime
support of the subgroup order. -/
theorem primeSupport_orderOf_mem_of_mem
    {G : Type u} [Group G] [Finite G]
    {H : Subgroup G} {x : G} (hx : x ∈ H)
    {p : ℕ} (hp : p ∈ primeSupport (orderOf x)) :
    p ∈ primeSupport (Nat.card H) :=
  ⟨hp.1, hp.2.trans (H.orderOf_dvd_natCard hx)⟩

/-- Failure of the pi-number condition exposes a prime divisor outside
the selected prime set. -/
private theorem exists_primeSupport_not_mem_of_not_isPiNumber
    {pi : Set ℕ} {n : ℕ} (h : ¬ IsPiNumber pi n) :
    ∃ p : ℕ, p ∈ primeSupport n ∧ p ∉ pi := by
  simp only [IsPiNumber] at h
  push_neg at h
  obtain ⟨p, hp, hpn, hpNot⟩ := h
  exact ⟨p, ⟨hp, hpn⟩, hpNot⟩

/-- A prime divisor of `orderOf x` supplies an elementary-abelian line in
the cyclic subgroup generated by `x`. -/
theorem exists_rankOneLineIn_zpowers
    {G : Type u} [Group G] [Finite G]
    {x : G} {p : ℕ} (hp : p ∈ primeSupport (orderOf x)) :
    ∃ X : Subgroup G,
      IsElementaryAbelianOfRank p 1 X ∧ X ≤ Subgroup.zpowers x := by
  letI : Fact p.Prime := ⟨hp.1⟩
  let C : Subgroup G := Subgroup.zpowers x
  have hpC : p ∣ Nat.card C := by
    simpa [C, Nat.card_zpowers] using hp.2
  obtain ⟨y, hyOrder⟩ :=
    exists_prime_orderOf_dvd_card' (G := C) p hpC
  let X : Subgroup G := Subgroup.zpowers (y : G)
  have hXC : X ≤ C := Subgroup.zpowers_le.mpr y.property
  have hcardX : Nat.card X = p := by
    dsimp only [X]
    rw [Nat.card_zpowers]
    simpa using hyOrder
  exact ⟨X, isElementaryAbelianOfRank_one_of_card_eq_prime hcardX, hXC⟩

/-- Two members of a finite set of cardinality at most one coincide. -/
private theorem ncard_le_one_unique
    {A : Type*} [Finite A] {S : Set A} (hS : S.ncard ≤ 1)
    {a b : A} (ha : a ∈ S) (hb : b ∈ S) : a = b := by
  exact (Set.ncard_le_one_iff).mp hS ha hb

/-- In the small branch the definition of the selected signalizer base
reduces to the trivial subgroup. -/
private theorem ftSignalizerBase_eq_bot_of_ncard_le_one
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {x : G}
    (hsmall : (sigmaMaximalOvergroups
      (Subgroup.zpowers x : Set G)).ncard ≤ 1) :
    ftSignalizerBase x = ⊥ := by
  rw [ftSignalizerBase]
  simp only [if_neg (not_lt_of_ge hsmall)]

/-- Once the maximal overgroup of the full element centralizer is unique,
the choice in `ftSignalizerBase` is forced to be that subgroup. -/
private theorem ftSignalizerBase_eq_of_large_unique
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {x : G} {N : Subgroup G}
    (hlarge : 1 < (sigmaMaximalOvergroups
      (Subgroup.zpowers x : Set G)).ncard)
    (huniq : minSimple_max_groups_of (G := G)
    ((elementCentralizer x : Subgroup G) : Set G) = {N}) :
    ftSignalizerBase x = N := by
  classical
  rw [ftSignalizerBase, if_pos hlarge, huniq]
  change
    (if hS : ({N} : Set (Subgroup G)).Nonempty then
        Classical.choose hS else ⊥) = N
  split
  · rename_i hS
    exact Set.mem_singleton_iff.mp (Classical.choose_spec hS)
  · rename_i hS
    exact (hS ⟨N, Set.mem_singleton N⟩).elim

/-- An element commuting with `x` centralizes every power of `x`. -/
private theorem mem_elementCentralizer_of_commute
    {G : Type u} [Group G] {x y : G} (hxy : Commute x y) :
    x ∈ elementCentralizer y := by
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rcases hz with ⟨n, rfl⟩
  exact (hxy.zpow_right n).symm

/-- Both factors of an internal direct product are normal in the product.
They are the kernels of the opposite canonical projections. -/
private theorem internalDirectProduct_normal_factors_structure
    {G : Type u} [Group G] {A B W : Subgroup G}
    (h : IsInternalDirectProductIn A B W) :
    (A.subgroupOf W).Normal ∧ (B.subgroupOf W).Normal := by
  have hAker : A.subgroupOf W = h.rightProjection.ker := by
    ext w
    constructor
    · intro hw
      let a : A := ⟨w, hw⟩
      have hwa : h.leftEmbedding a = w := by
        apply Subtype.ext
        rfl
      change h.rightProjection w = 1
      rw [← hwa, h.rightProjection_leftEmbedding]
    · intro hw
      have hproj : h.rightProjection w = 1 := hw
      have hwa : w = h.leftEmbedding (h.leftProjection w) := by
        calc
          w = h.mulEquiv (h.leftProjection w, h.rightProjection w) :=
            (h.mulEquiv_projections w).symm
          _ = h.mulEquiv (h.leftProjection w, 1) := by rw [hproj]
          _ = h.leftEmbedding (h.leftProjection w) :=
            h.mulEquiv_apply_left (h.leftProjection w)
      change (w : G) ∈ A
      rw [hwa]
      exact (h.leftProjection w).property
  have hBker : B.subgroupOf W = h.leftProjection.ker := by
    ext w
    constructor
    · intro hw
      let b : B := ⟨w, hw⟩
      have hwb : h.rightEmbedding b = w := by
        apply Subtype.ext
        rfl
      change h.leftProjection w = 1
      rw [← hwb, h.leftProjection_rightEmbedding]
    · intro hw
      have hproj : h.leftProjection w = 1 := hw
      have hwb : w = h.rightEmbedding (h.rightProjection w) := by
        calc
          w = h.mulEquiv (h.leftProjection w, h.rightProjection w) :=
            (h.mulEquiv_projections w).symm
          _ = h.mulEquiv (1, h.rightProjection w) := by rw [hproj]
          _ = h.rightEmbedding (h.rightProjection w) :=
            h.mulEquiv_apply_right (h.rightProjection w)
      change (w : G) ∈ B
      rw [hwb]
      exact (h.rightProjection w).property
  constructor
  · rw [hAker]
    infer_instance
  · rw [hBker]
    infer_instance

/-- The two prime-set factors of an internal direct product are the
corresponding complementary Hall subgroups. -/
private theorem complementary_isHall_of_internalDirectProduct_structure
    {G : Type u} [Group G] [Finite G]
    {A B W : Subgroup G} {pi : Set ℕ}
    (h : IsInternalDirectProductIn A B W)
    (hA : IsPiNumber piᶜ (Nat.card A))
    (hB : IsPiNumber pi (Nat.card B)) :
    IsHall piᶜ (A.subgroupOf W) ∧
      IsHall pi (B.subgroupOf W) := by
  constructor
  · constructor
    · simpa [MathlibSupport.natCard_subgroupOf_eq h.left_le] using hA
    · rw [h.complement.symm.index_eq_card,
        MathlibSupport.natCard_subgroupOf_eq h.right_le]
      simpa only [compl_compl] using hB
  · constructor
    · simpa [MathlibSupport.natCard_subgroupOf_eq h.right_le] using hB
    · rw [h.complement.index_eq_card,
        MathlibSupport.natCard_subgroupOf_eq h.left_le]
      exact hA

/-- Element membership in a normal Hall subgroup follows from the prime
support of its order. -/
private theorem mem_normalHall_of_isPiNumber_order_structure
    {G : Type u} [Group G] [Finite G]
    {pi : Set ℕ} {K C : Subgroup G}
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
    simpa only [KC] using hdvd
  have horderOne : orderOf (qC xC) = 1 :=
    by simpa [Nat.Coprime] using
      horderPi.coprime_compl horderCompl
  have hqOne : qC xC = 1 := orderOf_eq_one_iff.mp horderOne
  have hxKC : xC ∈ KC :=
    (QuotientGroup.eq_one_iff xC).mp (by simpa [qC] using hqOne)
  exact hxKC

/-- Restricting a normal Hall subgroup to an intermediate subgroup gives
the corresponding Hall intersection. -/
private theorem isHall_inf_of_normal_le_structure
    {G : Type u} [Group G] [Finite G]
    {pi : Set ℕ} {H C M : Subgroup G}
    (hHM : H ≤ M) (hCM : C ≤ M)
    (hHnormal : (H.subgroupOf M).Normal)
    (hHHall : IsHall pi (H.subgroupOf M)) :
    IsHall pi ((H ⊓ C).subgroupOf C) := by
  constructor
  · rw [MathlibSupport.natCard_subgroupOf_eq inf_le_right]
    have hHpi : IsPiNumber pi (Nat.card H) := by
      simpa only [MathlibSupport.natCard_subgroupOf_eq hHM] using
        hHHall.isPiNumber_card
    exact hHpi.of_dvd (Subgroup.card_dvd_of_le inf_le_left)
  · change IsPiNumber piᶜ ((H ⊓ C).relIndex C)
    rw [Subgroup.inf_relIndex_right]
    let HM : Subgroup M := H.subgroupOf M
    let CM : Subgroup M := C.subgroupOf M
    letI : HM.Normal := by simpa [HM] using hHnormal
    have hdvd : HM.relIndex CM ∣ HM.index :=
      Subgroup.relIndex_dvd_index_of_normal HM CM
    have hrel : HM.relIndex CM = H.relIndex C := by
      simpa only [HM, CM] using Subgroup.relIndex_subgroupOf
        (H := H) hCM
    rw [hrel] at hdvd
    exact hHHall.isPiNumber_index.of_dvd hdvd

/-- If `H` is normal in `M`, its intersection with an intermediate
subgroup `C ≤ M` is normal in `C`. -/
private theorem normal_inf_subgroupOf_of_le_structure
    {G : Type u} [Group G] {M H C : Subgroup G}
    (hHM : H ≤ M) (hCM : C ≤ M)
    (hHnormal : (H.subgroupOf M).Normal) :
    ((H ⊓ C).subgroupOf C).Normal := by
  have hMnormH : M ≤ Subgroup.normalizer (H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).mp hHnormal
  apply Subgroup.normal_subgroupOf_of_le_normalizer
  intro c hc
  have hcH := Subgroup.mem_normalizer_iff.mp (hMnormH (hCM hc))
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    exact ⟨(hcH z).mp hz.1,
      C.mul_mem (C.mul_mem hc hz.2) (C.inv_mem hc)⟩
  · intro hz
    have hzC : z ∈ C := by
      have hconj : c⁻¹ * (c * z * c⁻¹) * c ∈ C :=
        C.mul_mem (C.mul_mem (C.inv_mem hc) hz.2) hc
      have heq : c⁻¹ * (c * z * c⁻¹) * c = z := by group
      simpa only [heq] using hconj
    exact ⟨(hcH z).mpr hz.1, hzC⟩

/-- Centralizing a subgroup contained in the complement of an internal
semidirect product restricts the decomposition to the corresponding
centralizers. -/
private theorem centralizerWithin_semidirectProduct_structure
    {G : Type u} [Group G]
    {A B N X : Subgroup G}
    (h : IsInternalSemidirectProductIn A B N)
    (hXB : X ≤ B) :
    IsInternalSemidirectProductIn
      (centralizerWithin A X) (centralizerWithin B X)
      (centralizerWithin N X) := by
  classical
  let C : Subgroup G := centralizerWithin N X
  let CA : Subgroup G := centralizerWithin A X
  let CB : Subgroup G := centralizerWithin B X
  have hCAN : CA ≤ C := inf_le_inf h.1 le_rfl
  have hCBN : CB ≤ C := inf_le_inf h.2.1 le_rfl
  have hCLeN : C ≤ N := centralizerWithin_le_left N X
  have hCAnormal : (CA.subgroupOf C).Normal := by
    have hnormal := normal_inf_subgroupOf_of_le_structure
      h.1 hCLeN h.2.2.1
    have hEq : A ⊓ C = CA := by
      change A ⊓ (N ⊓ Subgroup.centralizer (X : Set G)) =
        A ⊓ Subgroup.centralizer (X : Set G)
      rw [← inf_assoc, inf_eq_left.mpr h.1]
    rw [← hEq]
    exact hnormal
  have hdis : Disjoint (CA.subgroupOf C) (CB.subgroupOf C) := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro z hz
    have hzAB : (⟨(z : G), h.1 hz.1.1⟩ : N) ∈
        (A.subgroupOf N) ⊓ (B.subgroupOf N) :=
      ⟨hz.1.1, hz.2.1⟩
    have hzBot : (⟨(z : G), h.1 hz.1.1⟩ : N) ∈
        (⊥ : Subgroup N) :=
      h.2.2.2.disjoint.le_bot hzAB
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    exact congrArg (fun w : N ↦ (w : G))
      (Subgroup.mem_bot.mp hzBot)
  have hsup : CA.subgroupOf C ⊔ CB.subgroupOf C = ⊤ := by
    apply top_unique
    intro z _
    let zN : N := ⟨(z : G), hCLeN z.property⟩
    obtain ⟨⟨a, b⟩, hab⟩ := h.2.2.2.2 zN
    have haCent : (a : G) ∈ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      let tN : N := ⟨t, h.2.1 (hXB ht)⟩
      let tB : B.subgroupOf N := ⟨tN, hXB ht⟩
      have hza : (zN : G) = (a : G) * (b : G) := by
        exact congrArg Subtype.val hab.symm
      have htz : t * (zN : G) = (zN : G) * t := z.property.2 t ht
      have hconjA : tN * (a : N) * tN⁻¹ ∈ A.subgroupOf N :=
        h.2.2.1.conj_mem a a.property tN
      let a' : A.subgroupOf N :=
        ⟨tN * (a : N) * tN⁻¹, hconjA⟩
      let tb : B.subgroupOf N :=
        ⟨tN * (b : N), B.mul_mem tB.property b.property⟩
      let bt : B.subgroupOf N :=
        ⟨(b : N) * tN, B.mul_mem b.property tB.property⟩
      have hpairs : (a', tb) = (a, bt) := by
        apply h.2.2.2.1
        apply Subtype.ext
        change
          t * (a : G) * t⁻¹ * (t * (b : G)) =
            (a : G) * ((b : G) * t)
        rw [hza] at htz
        calc
          t * (a : G) * t⁻¹ * (t * (b : G)) =
              t * ((a : G) * (b : G)) := by group
          _ = (a : G) * (b : G) * t := htz
          _ = (a : G) * ((b : G) * t) := by group
      have htb : t * (b : G) = (b : G) * t := by
        have := congrArg (fun w : (A.subgroupOf N) ×
            (B.subgroupOf N) ↦ ((w.2 : N) : G)) hpairs
        simpa [tb, bt, tN] using this
      apply mul_right_cancel
      calc
        (t * (a : G)) * (b : G) =
            t * ((a : G) * (b : G)) := by group
        _ = ((a : G) * (b : G)) * t := by
          rw [hza] at htz
          exact htz
        _ = (a : G) * ((b : G) * t) := by group
        _ = (a : G) * (t * (b : G)) := by rw [htb]
        _ = ((a : G) * t) * (b : G) := by group
    have hbCent : (b : G) ∈ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      let tN : N := ⟨t, h.2.1 (hXB ht)⟩
      let tB : B.subgroupOf N := ⟨tN, hXB ht⟩
      have hza : (zN : G) = (a : G) * (b : G) := by
        exact congrArg Subtype.val hab.symm
      have htz : t * (zN : G) = (zN : G) * t := z.property.2 t ht
      have hconjA : tN * (a : N) * tN⁻¹ ∈ A.subgroupOf N :=
        h.2.2.1.conj_mem a a.property tN
      let a' : A.subgroupOf N :=
        ⟨tN * (a : N) * tN⁻¹, hconjA⟩
      let tb : B.subgroupOf N :=
        ⟨tN * (b : N), B.mul_mem tB.property b.property⟩
      let bt : B.subgroupOf N :=
        ⟨(b : N) * tN, B.mul_mem b.property tB.property⟩
      have hpairs : (a', tb) = (a, bt) := by
        apply h.2.2.2.1
        apply Subtype.ext
        change
          t * (a : G) * t⁻¹ * (t * (b : G)) =
            (a : G) * ((b : G) * t)
        rw [hza] at htz
        calc
          t * (a : G) * t⁻¹ * (t * (b : G)) =
              t * ((a : G) * (b : G)) := by group
          _ = (a : G) * (b : G) * t := htz
          _ = (a : G) * ((b : G) * t) := by group
      have := congrArg (fun w : (A.subgroupOf N) ×
          (B.subgroupOf N) ↦ ((w.2 : N) : G)) hpairs
      simpa [tb, bt, tN] using this
    let aC : C := ⟨(a : G), hCAN ⟨a.property, haCent⟩⟩
    let bC : C := ⟨(b : G), hCBN ⟨b.property, hbCent⟩⟩
    have haSub : aC ∈ CA.subgroupOf C := ⟨a.property, haCent⟩
    have hbSub : bC ∈ CB.subgroupOf C := ⟨b.property, hbCent⟩
    have habC : aC * bC = z := by
      apply Subtype.ext
      simpa [aC, bC] using congrArg Subtype.val hab
    rw [← habC]
    exact Subgroup.mul_mem_sup haSub hbSub
  refine ⟨hCAN, hCBN, hCAnormal, ?_⟩
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis
  letI : (CA.subgroupOf C).Normal := hCAnormal
  rw [← Subgroup.coe_mul_of_right_le_normalizer_left
    (CA.subgroupOf C) (CB.subgroupOf C)
      Subgroup.le_normalizer_of_normal]
  rw [hsup]
  rfl

/-- Hall subgroups transport through a multiplicative equivalence. -/
private theorem isHall_map_mulEquiv_structure
    {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    {pi : Set ℕ} {L : Subgroup A} (e : A ≃* B)
    (hL : IsHall pi L) :
    IsHall pi (L.map e.toMonoidHom) := by
  constructor
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hL.isPiNumber_card
  · have hindex : (L.map e.toMonoidHom).index = L.index :=
      Subgroup.index_map_equiv L e
    rw [hindex]
    exact hL.isPiNumber_index

/-- Relative Hall subgroups transport through an ambient equivalence. -/
private theorem isHall_subgroupOf_map_mulEquiv_structure
    {G : Type u} [Group G] [Finite G]
    {H L : Subgroup G} (hLH : L ≤ H)
    {pi : Set ℕ} (hL : IsHall pi (L.subgroupOf H))
    (e : G ≃* G) :
    IsHall pi
      ((L.map e.toMonoidHom).subgroupOf
        (H.map e.toMonoidHom)) := by
  let eH : H ≃* H.map e.toMonoidHom :=
    H.equivMapOfInjective e.toMonoidHom e.injective
  have hmap :
      (L.subgroupOf H).map eH.toMonoidHom =
        (L.map e.toMonoidHom).subgroupOf
          (H.map e.toMonoidHom) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      change e (y : G) ∈ L.map e.toMonoidHom
      have hyL : (y : G) ∈ L := hy
      exact Subgroup.mem_map_equiv.mpr (by simpa using hyL)
    · intro hz
      change (z : G) ∈ L.map e.toMonoidHom at hz
      have hz' := Subgroup.mem_map_equiv.mp hz
      let y : H := ⟨e.symm z, hLH hz'⟩
      refine ⟨y, hz', ?_⟩
      apply Subtype.ext
      change e (e.symm (z : G)) = (z : G)
      simp
  rw [← hmap]
  exact isHall_map_mulEquiv_structure eH hL

/-- Restricting a Hall subgroup to an intermediate ambient subgroup keeps it
Hall. -/
private theorem isHall_subgroupOf_intermediate_structure
    {G : Type u} [Group G] [Finite G]
    {pi : Set ℕ} {A B C : Subgroup G}
    (hAB : A ≤ B) (hBC : B ≤ C)
    (hA : IsHall pi (A.subgroupOf C)) :
    IsHall pi (A.subgroupOf B) := by
  constructor
  · simpa only [MathlibSupport.natCard_subgroupOf_eq hAB,
      MathlibSupport.natCard_subgroupOf_eq (hAB.trans hBC)] using
      hA.isPiNumber_card
  · have hdvd : A.relIndex B ∣ A.relIndex C := by
      refine ⟨B.relIndex C, ?_⟩
      exact (Subgroup.relIndex_mul_relIndex A B C hAB hBC).symm
    exact hA.isPiNumber_index.of_dvd hdvd

/-- A normal Hall subgroup is the unique Hall subgroup for its prime set. -/
private theorem normalHall_eq_isHall_structure
    {G : Type u} [Group G] [Finite G]
    {pi : Set ℕ} {A B H : Subgroup G}
    (hAH : A ≤ H) (hBH : B ≤ H)
    (hAnormal : (A.subgroupOf H).Normal)
    (hAHall : IsHall pi (A.subgroupOf H))
    (hBHall : IsHall pi (B.subgroupOf H)) :
    A = B := by
  let AH : Subgroup H := A.subgroupOf H
  let BH : Subgroup H := B.subgroupOf H
  have hAB : AH ≤ BH := normal_isPiNumber_le_isHall hAnormal
    hAHall.isPiNumber_card hBHall
  have hrelPi : IsPiNumber pi (AH.relIndex BH) :=
    hBHall.isPiNumber_card.of_dvd (Subgroup.relIndex_dvd_card AH BH)
  have hrelCompl : IsPiNumber piᶜ (AH.relIndex BH) :=
    hAHall.isPiNumber_index.of_dvd
      (Subgroup.relIndex_dvd_index_of_le hAB)
  have hrelOne : AH.relIndex BH = 1 :=
    by simpa [Nat.Coprime] using
      hrelPi.coprime_compl hrelCompl
  have hBA : BH ≤ AH := Subgroup.relIndex_eq_one.mp hrelOne
  apply le_antisymm
  · intro a ha
    exact hAB (show (⟨a, hAH ha⟩ : H) ∈ AH from ha)
  · intro b hb
    exact hBA (show (⟨b, hBH hb⟩ : H) ∈ BH from hb)

/-- Complements transport through a multiplicative equivalence. -/
private theorem isComplement_map_mulEquiv_structure
    {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    {K L : Subgroup A} (h : K.IsComplement' L) (e : A ≃* B) :
    (K.map e.toMonoidHom).IsComplement'
      (L.map e.toMonoidHom) := by
  apply Subgroup.isComplement'_of_card_mul_and_disjoint
  · rw [Subgroup.card_map_of_injective e.injective,
      Subgroup.card_map_of_injective e.injective, h.card_mul]
    exact Nat.card_congr e.toEquiv
  · exact Subgroup.disjoint_map e.injective h.disjoint

/-- `subgroupOf` commutes with transport through an equivalence. -/
private theorem subgroupOf_map_mulEquiv_structure
    {G : Type u} [Group G] {A H : Subgroup G}
    (hAH : A ≤ H) (e : G ≃* G) :
    (A.subgroupOf H).map (e.subgroupMap H).toMonoidHom =
      (A.map e.toMonoidHom).subgroupOf
        (H.map e.toMonoidHom) := by
  ext z
  rw [Subgroup.mem_map_equiv]
  change e.symm (z : G) ∈ A ↔
    (z : G) ∈ A.map e.toMonoidHom
  rw [Subgroup.mem_map_equiv]

/-- Internal semidirect products transport through an equivalence. -/
private theorem semidirectProduct_map_mulEquiv_structure
    {G : Type u} [Group G] [Finite G] {A B H : Subgroup G}
    (h : IsInternalSemidirectProductIn A B H) (e : G ≃* G) :
    IsInternalSemidirectProductIn
      (A.map e.toMonoidHom) (B.map e.toMonoidHom)
      (H.map e.toMonoidHom) := by
  let eH : H ≃* H.map e.toMonoidHom := e.subgroupMap H
  have hA := subgroupOf_map_mulEquiv_structure h.1 e
  have hB := subgroupOf_map_mulEquiv_structure h.2.1 e
  refine ⟨Subgroup.map_mono h.1, Subgroup.map_mono h.2.1, ?_, ?_⟩
  · rw [← hA]
    exact Subgroup.Normal.map h.2.2.1 eH.toMonoidHom eH.surjective
  · rw [← hA, ← hB]
    exact isComplement_map_mulEquiv_structure h.2.2.2 eH

/-- Semiregular conjugation transports through an equivalence. -/
private theorem semiregularConjugation_map_mulEquiv_structure
    {G : Type u} [Group G] {A B : Subgroup G}
    (h : IsSemiregularConjugation A B) (e : G ≃* G) :
    IsSemiregularConjugation
      (A.map e.toMonoidHom) (B.map e.toMonoidHom) := by
  intro b hb a hfix
  let b₀ : B := (e.subgroupMap B).symm b
  let a₀ : A := (e.subgroupMap A).symm a
  have hb₀ : b₀ ≠ 1 := by
    intro hbOne
    apply hb
    simpa [b₀] using congrArg (e.subgroupMap B) hbOne
  have hfix₀ : (b₀ : G) * (a₀ : G) * (b₀ : G)⁻¹ = a₀ := by
    apply e.injective
    simpa [b₀, a₀] using hfix
  have ha₀ := h b₀ hb₀ a₀ hfix₀
  simpa [a₀] using congrArg (e.subgroupMap A) ha₀

/-- The factors of an internal semidirect product generate its ambient
subgroup. -/
private theorem semidirectProduct_sup_eq_ambient
    {G : Type u} [Group G] {A B H : Subgroup G}
    (h : IsInternalSemidirectProductIn A B H) :
    A ⊔ B = H := by
  apply le_antisymm (sup_le h.1 h.2.1)
  intro z hz
  let zH : H := ⟨z, hz⟩
  have hzTop : zH ∈ (A.subgroupOf H) ⊔ (B.subgroupOf H) := by
    rw [h.2.2.2.sup_eq_top]
    exact Subgroup.mem_top zH
  have hzSub : zH ∈ (A ⊔ B).subgroupOf H := by
    rw [Subgroup.subgroupOf_sup h.1 h.2.1]
    exact hzTop
  exact hzSub

/-- Transport an intrinsic conjugacy equality in an ambient subgroup back
to the common group. -/
private theorem ambient_map_conj_eq_of_subgroupOf_structure
    {G : Type u} [Group G] {M A B : Subgroup G}
    (hAM : A ≤ M) (hBM : B ≤ M) (x : M)
    (hconj : B.subgroupOf M =
      (A.subgroupOf M).map (MulAut.conj x).toMonoidHom) :
    A.map (MulAut.conj (x : G)).toMonoidHom = B := by
  apply le_antisymm
  · intro y hy
    rcases hy with ⟨a, ha, rfl⟩
    let aM : M := ⟨a, hAM ha⟩
    have haMap : (MulAut.conj x) aM ∈ B.subgroupOf M := by
      rw [hconj]
      exact Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom ha
    exact haMap
  · intro y hy
    let yM : M := ⟨y, hBM hy⟩
    have hyMap : yM ∈
        (A.subgroupOf M).map (MulAut.conj x).toMonoidHom := by
      rw [← hconj]
      exact hy
    rcases hyMap with ⟨aM, haM, hay⟩
    refine ⟨(aM : G), haM, ?_⟩
    exact congrArg Subtype.val hay

/-- A nontrivial `p`-subgroup has a proper normalizer and hence a maximal
overgroup of that normalizer. -/
private theorem exists_maximalOvergroup_normalizer
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} {X : Subgroup G}
    [Fact p.Prime] (hXne : X ≠ ⊥) (hXp : IsPGroup p X) :
    ∃ M : Subgroup G,
      M ∈ minSimple_max_groups_of (G := G)
        (Subgroup.normalizer (X : Set G) : Set G) := by
  have hXproper : X < ⊤ := mFT_pgroup_proper X hXp
  have hNproper : Subgroup.normalizer (X : Set G) < ⊤ :=
    mFT_norm_proper X hXne hXproper
  exact mmax_exists (Subgroup.normalizer (X : Set G)) hNproper

/-- A nonidentity tau-two element has sigma length one.  This is the
construction in the first branch of Corollary 14.3: normalize a rank-two
tau-two subgroup, use Proposition 12.15 to move every tau-two prime into
the new sigma set, and finally conjugate the cyclic subgroup into the new
sigma core. -/
private theorem sigmaLength_eq_one_of_tau2_element
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G} (hM : M ∈ minSimple_max_groups (G := G))
    {y : G} (hyM : y ∈ M) (hy1 : y ≠ 1)
    (hyTau2 : IsPiNumber (tau2Primes M) (orderOf y)) :
    sigmaLength y = 1 := by
  classical
  obtain ⟨p, hpOrder⟩ := exists_prime_mem_primeSupport_orderOf hy1
  letI : Fact p.Prime := ⟨hpOrder.1⟩
  have hpTau2 : p ∈ tau2Primes M :=
    hyTau2 hpOrder.1 hpOrder.2
  obtain ⟨E, hEM, hHallE⟩ := ex_sigma_compl hM
  obtain ⟨A, hAE, _hAM, hA⟩ := ex_tau2Elem hEM hHallE hpTau2
  have hNAproper : Subgroup.normalizer (A : Set G) < ⊤ :=
    mFT_norm_proper A hA.ne_bot (mFT_pgroup_proper A hA.isPGroup)
  obtain ⟨H, hH, hNAH⟩ :=
    mmax_exists (Subgroup.normalizer (A : Set G)) hNAproper
  have hTau2Sigma : ∀ {q : ℕ}, q ∈ tau2Primes M →
      q ∈ sigmaPrimes H := by
    intro q hq
    exact (primes_norm_tau2Elem_tau2_classification
      hM hEM hHallE hpTau2 hAE hA hH hNAH hq).1
  have hySigmaH : IsPiNumber (sigmaPrimes H) (orderOf y) := by
    intro q hq hqOrder
    exact hTau2Sigma (hyTau2 hq hqOrder)
  have hZsigma : IsPiNumber (sigmaPrimes H)
      (Nat.card (Subgroup.zpowers y)) := by
    rw [Nat.card_zpowers]
    exact hySigmaH
  have hZne : Subgroup.zpowers y ≠ ⊥ :=
    Subgroup.zpowers_ne_bot.mpr hy1
  obtain ⟨z, hz⟩ := (sigma_Jsub hH hZsigma hZne).1
  let L : Subgroup G := H.map (MulAut.conj z⁻¹).toMonoidHom
  have hL : L ∈ minSimple_max_groups (G := G) :=
    (mmaxJ H (MulAut.conj z⁻¹)).mpr hH
  have hZL : Subgroup.zpowers y ≤ sigmaCore L := by
    intro a ha
    have hza : (MulAut.conj z) a ∈ sigmaCore H :=
      hz (Subgroup.mem_map_of_mem (MulAut.conj z).toMonoidHom ha)
    change a ∈ sigmaCore (H.map (MulAut.conj z⁻¹).toMonoidHom)
    rw [sigmaCore_conj]
    refine ⟨(MulAut.conj z) a, hza, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  exact (ell_sigma1P (x := y)).mpr ⟨hy1, L, hL, hZL⟩

/-- A prime divisor of a maximal subgroup outside sigma belongs either to
tau two or to the union of tau one and tau three. -/
private theorem prime_not_sigma_mem_tau2_or_tau13
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G} {p : ℕ}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hpM : p ∈ primeSupport (Nat.card M))
    (hpSigma : p ∉ sigmaPrimes M) :
    p ∈ tau2Primes M ∨ p ∈ tau13Primes M := by
  letI : Fact p.Prime := ⟨hpM.1⟩
  obtain ⟨x, hxorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := M) p hpM.2
  let X : Subgroup G := (Subgroup.zpowers x).map M.subtype
  have hXcard : Nat.card X = p := by
    dsimp only [X]
    rw [Subgroup.card_map_of_injective M.subtype_injective,
      Nat.card_zpowers, hxorder]
  have hXrank : IsElementaryAbelianOfRank p 1 X :=
    isElementaryAbelianOfRank_one_of_card_eq_prime hXcard
  have hRankOne : HasElementaryAbelianRankAtLeast p 1 M :=
    ⟨X, Subgroup.map_subtype_le _, hXrank⟩
  by_cases hRankTwo : HasElementaryAbelianRankAtLeast p 2 M
  · left
    refine ⟨hpM.1, hpSigma, hRankTwo, ?_⟩
    intro hRankThree
    exact hpSigma (alpha_sub_sigma hM ⟨hpM.1, hRankThree⟩)
  · right
    by_cases hpDer : p ∣ Nat.card (_root_.commutator M)
    · exact Or.inr ⟨hpM.1, hpSigma, hRankOne, hRankTwo, hpDer⟩
    · exact Or.inl ⟨hpM.1, hpSigma, hRankOne, hRankTwo, hpDer⟩

/-- The subgroup recorded by a kappa-complement product is its join. -/
private theorem kappaComplement_product_eq_sup
    {G : Type u} [Group G] [Finite G]
    {M U K E : Subgroup G}
    (hCompl : KappaComplement M U K)
    (hE : (E : Set G) = (U : Set G) * (K : Set G)) :
    E = U ⊔ K := by
  apply le_antisymm
  · intro z hz
    change z ∈ (E : Set G) at hz
    rw [hE] at hz
    rcases hz with ⟨u, hu, k, hk, rfl⟩
    exact (U ⊔ K).mul_mem
      ((show U ≤ U ⊔ K from le_sup_left) hu)
      ((show K ≤ U ⊔ K from le_sup_right) hk)
  · apply sup_le
    · intro u hu
      change u ∈ (E : Set G)
      rw [hE]
      exact ⟨u, hu, 1, K.one_mem, by simp⟩
    · intro k hk
      change k ∈ (E : Set G)
      rw [hE]
      exact ⟨1, U.one_mem, k, hk, by simp⟩

/-- The product in a kappa complement is a sigma complement. -/
private theorem kappaComplement_sup_hall_structure
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M U K : Subgroup G}
    (hCompl : KappaComplement M U K) :
    IsHall (sigmaPrimes M)ᶜ ((U ⊔ K).subgroupOf M) := by
  classical
  have hUKM : U ⊔ K ≤ M := sup_le hCompl.U_le_M hCompl.K_le_M
  obtain ⟨E, hE⟩ := hCompl.product_is_group
  have hEsup : E = U ⊔ K :=
    kappaComplement_product_eq_sup hCompl hE
  have hUcardSK : IsPiNumber (sigmaKappaPrimes M)ᶜ (Nat.card U) := by
    simpa only [MathlibSupport.natCard_subgroupOf_eq hCompl.U_le_M] using
      hCompl.hall_U.isPiNumber_card
  have hKcardKappa : IsPiNumber (kappaPrimes M) (Nat.card K) := by
    simpa only [MathlibSupport.natCard_subgroupOf_eq hCompl.K_le_M] using
      hCompl.hall_K.isPiNumber_card
  have hUcard : IsPiNumber (sigmaPrimes M)ᶜ (Nat.card U) := by
    apply hUcardSK.mono
    intro p hp
    change p ∉ sigmaPrimes M
    intro hpSigma
    exact hp (Or.inl hpSigma)
  have hKcard : IsPiNumber (sigmaPrimes M)ᶜ (Nat.card K) :=
    hKcardKappa.mono (kappa_sigma' M)
  have hcop : (Nat.card U).Coprime (Nat.card K) := by
    apply Nat.coprime_of_dvd
    intro p hp hpU hpK
    exact hUcardSK hp hpU (Or.inr (hKcardKappa hp hpK))
  have hcard : Nat.card (U ⊔ K : Subgroup G) =
      Nat.card U * Nat.card K := by
    have hUE : U ≤ E := by
      rw [hEsup]
      exact le_sup_left
    have hKE : K ≤ E := by
      rw [hEsup]
      exact le_sup_right
    let UE : Subgroup E := U.subgroupOf E
    let KE : Subgroup E := K.subgroupOf E
    have hdis : Disjoint U K :=
      Subgroup.disjoint_of_coprime_natCard hcop
    have hdisE : Disjoint UE KE := by
      rw [disjoint_iff]
      apply le_antisymm _ bot_le
      intro z hz
      apply Subgroup.mem_bot.mpr
      apply Subtype.ext
      have hzbot : (z : G) ∈ (⊥ : Subgroup G) := by
        rw [← disjoint_iff.mp hdis]
        exact ⟨hz.1, hz.2⟩
      exact Subgroup.mem_bot.mp hzbot
    have hcomp : UE.IsComplement' KE := by
      apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisE
      apply Set.eq_univ_iff_forall.mpr
      intro z
      have hzE : (z : G) ∈ E := z.property
      change (z : G) ∈ (E : Set G) at hzE
      rw [hE] at hzE
      rcases hzE with ⟨u, hu, k, hk, huk⟩
      refine ⟨⟨u, hUE hu⟩, hu, ⟨k, hKE hk⟩, hk, ?_⟩
      apply Subtype.ext
      exact huk
    rw [← hEsup]
    calc
      Nat.card E = Nat.card UE * Nat.card KE := hcomp.card_mul.symm
      _ = Nat.card U * Nat.card K := by
        rw [MathlibSupport.natCard_subgroupOf_eq hUE,
          MathlibSupport.natCard_subgroupOf_eq hKE]
  constructor
  · rw [MathlibSupport.natCard_subgroupOf_eq hUKM, hcard]
    exact hUcard.mul hKcard
  · intro p hp hpIndex
    let US : Subgroup M := U.subgroupOf M
    let KS : Subgroup M := K.subgroupOf M
    let ES : Subgroup M := (U ⊔ K).subgroupOf M
    have hUES : US ≤ ES := by
      intro u hu
      exact (show U ≤ U ⊔ K from le_sup_left) hu
    have hKES : KS ≤ ES := by
      intro k hk
      exact (show K ≤ U ⊔ K from le_sup_right) hk
    have hpUIndex : p ∣ US.index :=
      hpIndex.trans (Subgroup.index_dvd_of_le hUES)
    have hpSigmaKappa : p ∈ sigmaKappaPrimes M := by
      have hpCompl := hCompl.hall_U.isPiNumber_index hp hpUIndex
      simpa only [compl_compl] using hpCompl
    have hpKIndex : p ∣ KS.index :=
      hpIndex.trans (Subgroup.index_dvd_of_le hKES)
    have hpNotKappa : p ∈ (kappaPrimes M)ᶜ :=
      hCompl.hall_K.isPiNumber_index hp hpKIndex
    rcases hpSigmaKappa with hpSigma | hpKappa
    · simpa only [compl_compl] using hpSigma
    · exact (hpNotKappa hpKappa).elim

/-- A prime divisor of a subgroup order supplies an elementary-abelian
line in that subgroup. -/
private theorem exists_rankOne_le_of_prime_dvd_structure
    {G : Type u} [Group G] [Finite G]
    {H : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hpH : p ∣ Nat.card H) :
    ∃ X : Subgroup G, X ≤ H ∧ IsElementaryAbelianOfRank p 1 X := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := H) p hpH
  let X : Subgroup G := (Subgroup.zpowers x).map H.subtype
  have hXH : X ≤ H := Subgroup.map_subtype_le _
  have hXcard : Nat.card X = p := by
    dsimp only [X]
    rw [Subgroup.card_map_of_injective H.subtype_injective,
      Nat.card_zpowers, hx]
  exact ⟨X, hXH,
    isElementaryAbelianOfRank_one_of_card_eq_prime hXcard⟩

/-- A prime belonging to the prime set of a Hall subgroup, and dividing
the ambient group, divides the Hall subgroup itself. -/
private theorem prime_dvd_card_of_mem_isHall_structure
    {G : Type u} [Group G] [Finite G]
    {pi : Set ℕ} {A M : Subgroup G}
    (hAM : A ≤ M) (hA : IsHall pi (A.subgroupOf M))
    {p : ℕ} (hp : p.Prime) (hpPi : p ∈ pi)
    (hpM : p ∣ Nat.card M) : p ∣ Nat.card A := by
  have hpProd : p ∣
      Nat.card (A.subgroupOf M) * (A.subgroupOf M).index := by
    rw [(A.subgroupOf M).card_mul_index]
    exact hpM
  rcases hp.dvd_mul.mp hpProd with hpA | hpIndex
  · simpa only [MathlibSupport.natCard_subgroupOf_eq hAM] using hpA
  · exact (hA.isPiNumber_index hp hpIndex hpPi).elim

/-- An intermediate pi-subgroup containing an ambient pi-Hall subgroup is
that Hall subgroup. -/
private theorem intermediate_eq_isHall_of_isPiNumber_structure
    {G : Type u} [Group G] [Finite G]
    {pi : Set ℕ} {K E M : Subgroup G}
    (hKE : K ≤ E) (hEM : E ≤ M)
    (hK : IsHall pi (K.subgroupOf M))
    (hEpi : IsPiNumber pi (Nat.card E)) : E = K := by
  have hrelPi : IsPiNumber pi (K.relIndex E) :=
    hEpi.of_dvd (Subgroup.relIndex_dvd_card K E)
  have hrelCompl : IsPiNumber piᶜ (K.relIndex E) :=
    hK.isPiNumber_index.of_dvd (by
      have hsub : K.subgroupOf M ≤ E.subgroupOf M :=
        fun _ hx ↦ hKE hx
      simpa only [Subgroup.relIndex_subgroupOf hEM] using
        (Subgroup.relIndex_dvd_index_of_le hsub))
  have hone : K.relIndex E = 1 :=
    by simpa [Nat.Coprime] using
      hrelPi.coprime_compl hrelCompl
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hone) hKE

/-- Hall subgroups compose through an intermediate Hall subgroup. -/
private theorem isHall_tower_structure
    {G : Type u} [Group G] [Finite G]
    {pi rho : Set ℕ} {A E M : Subgroup G}
    (hAE : A ≤ E) (hEM : E ≤ M)
    (hA : IsHall pi (A.subgroupOf E))
    (hE : IsHall rho (E.subgroupOf M))
    (hpi : pi ⊆ rho) :
    IsHall pi (A.subgroupOf M) := by
  constructor
  · simpa only [MathlibSupport.natCard_subgroupOf_eq (hAE.trans hEM),
      MathlibSupport.natCard_subgroupOf_eq hAE] using hA.isPiNumber_card
  · rw [← Subgroup.relIndex_mul_index
      (show A.subgroupOf M ≤ E.subgroupOf M from
        fun _ hx ↦ hAE hx)]
    apply IsPiNumber.mul
    · rw [Subgroup.relIndex_subgroupOf hEM]
      change IsPiNumber piᶜ ((A.subgroupOf E).index)
      exact hA.isPiNumber_index
    · apply hE.isPiNumber_index.mono
      intro p hpNotRho hpPi
      exact hpNotRho (hpi hpPi)

/-- Restrict the complement of an internal semidirect product to a
subgroup of the complement. -/
private theorem semidirectProduct_restrict_right_structure
    {G : Type u} [Group G]
    {A B C : Subgroup G}
    (h : IsInternalSemidirectProductIn A B C)
    {D : Subgroup G} (hDB : D ≤ B) :
    IsInternalSemidirectProductIn A D (A ⊔ D) := by
  have hAC : A ≤ C := h.1
  have hDC : D ≤ C := hDB.trans h.2.1
  have hCnormA : C ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAC).mp h.2.2.1
  have hAnormal : (A.subgroupOf (A ⊔ D)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (sup_le Subgroup.le_normalizer
        (hDC.trans hCnormA))
  have hdis : Disjoint (A.subgroupOf (A ⊔ D))
      (D.subgroupOf (A ⊔ D)) := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro x hx
    have hxC : (⟨(x : G), (show A ⊔ D ≤ C from
        sup_le hAC hDC) x.property⟩ : C) ∈
        (A.subgroupOf C) ⊓ (B.subgroupOf C) :=
      ⟨hx.1, hDB hx.2⟩
    have hxBot := h.2.2.2.disjoint.le_bot hxC
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    exact congrArg (fun w : C ↦ (w : G))
      (Subgroup.mem_bot.mp hxBot)
  refine ⟨le_sup_left, le_sup_right, hAnormal, ?_⟩
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis
  letI : (A.subgroupOf (A ⊔ D)).Normal := hAnormal
  rw [← Subgroup.normal_mul,
    ← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
    Subgroup.subgroupOf_self]
  rfl

/-- A nontrivial semiregular actor has trivial full centralizer. -/
private theorem centralizerWithin_eq_bot_of_semiregular_actor_structure
    {G : Type u} [Group G] {A B : Subgroup G}
    (hreg : IsSemiregularConjugation A B) (hB : B ≠ ⊥) :
    centralizerWithin A B = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨bB, hbB1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp hB
  let xA : A := ⟨x, hx.1⟩
  have hcomm : (bB : G) * x = x * (bB : G) :=
    hx.2 (bB : G) bB.property
  have hfix : (bB : G) * (xA : G) * (bB : G)⁻¹ = xA := by
    change (bB : G) * x * (bB : G)⁻¹ = x
    rw [hcomm]
    simp
  have hxOne : xA = 1 := hreg bB hbB1 xA hfix
  simpa [xA] using congrArg Subtype.val hxOne

/-- Commutativity descends along subgroup containment. -/
private theorem isMulCommutative_of_le_structure
    {G : Type u} [Group G] {A B : Subgroup G}
    (hAB : A ≤ B) (hB : IsMulCommutative B) :
    IsMulCommutative A := by
  rw [isMulCommutative_iff] at hB ⊢
  intro x y
  apply A.subtype_injective
  exact congrArg Subtype.val
    (hB ⟨x, hAB x.property⟩ ⟨y, hAB y.property⟩)

/-- Rank-one centralizer calculations imply semiregularity of the whole
actor. -/
private theorem semiregular_of_rankOne_centralizers_structure
    {G : Type u} [Group G] [Finite G] {A B : Subgroup G}
    (hline : ∀ {p : ℕ} [Fact p.Prime] {X : Subgroup G},
      RankOneLineIn p B X → centralizerWithin A X = ⊥) :
    IsSemiregularConjugation A B := by
  intro b hb a hfix
  have hbG : (b : G) ≠ 1 := by
    intro hb1
    apply hb
    exact Subtype.ext hb1
  obtain ⟨p, hp⟩ := exists_prime_mem_primeSupport_orderOf hbG
  letI : Fact p.Prime := ⟨hp.1⟩
  obtain ⟨X, hX, hXcycle⟩ := exists_rankOneLineIn_zpowers hp
  have hXB : X ≤ B :=
    hXcycle.trans (Subgroup.zpowers_le.mpr b.property)
  have hab : Commute (b : G) (a : G) := by
    rw [Commute]
    calc
      (b : G) * (a : G) =
          ((b : G) * (a : G) * (b : G)⁻¹) * (b : G) := by
            simp [mul_assoc]
      _ = (a : G) * (b : G) := by rw [hfix]
  have haCent : (a : G) ∈ centralizerWithin A X := by
    refine ⟨a.property, ?_⟩
    intro x hx
    rcases Subgroup.mem_zpowers_iff.mp (hXcycle hx) with ⟨z, rfl⟩
    exact (hab.zpow_left z).eq
  have haBot : (a : G) ∈ (⊥ : Subgroup G) := by
    rw [← hline ⟨hXB, hX⟩]
    exact haCent
  apply Subtype.ext
  exact Subgroup.mem_bot.mp haBot

/-- Semiregularity on the two normalized factors of a semidirect product
implies semiregularity on their product. -/
private theorem semiregular_semidirectProduct_structure
    {G : Type u} [Group G]
    {A B N X : Subgroup G}
    (h : IsInternalSemidirectProductIn A B N)
    (hXA : X ≤ Subgroup.normalizer (A : Set G))
    (hXB : X ≤ Subgroup.normalizer (B : Set G))
    (hregA : IsSemiregularConjugation A X)
    (hregB : IsSemiregularConjugation B X) :
    IsSemiregularConjugation N X := by
  intro x hx n hfix
  let nN : N := ⟨n, n.property⟩
  obtain ⟨⟨a, b⟩, hab⟩ := h.2.2.2.2 nN
  let xa : A.subgroupOf N :=
    ⟨⟨(x : G) * (a : G) * (x : G)⁻¹,
      h.1 ((Subgroup.mem_normalizer_iff.mp (hXA x.property) (a : G)).mp
        a.property)⟩,
      (Subgroup.mem_normalizer_iff.mp (hXA x.property) (a : G)).mp
        a.property⟩
  let xb : B.subgroupOf N :=
    ⟨⟨(x : G) * (b : G) * (x : G)⁻¹,
      h.2.1 ((Subgroup.mem_normalizer_iff.mp (hXB x.property) (b : G)).mp
        b.property)⟩,
      (Subgroup.mem_normalizer_iff.mp (hXB x.property) (b : G)).mp
        b.property⟩
  have hpair : (xa, xb) = (a, b) := by
    apply h.2.2.2.1
    apply Subtype.ext
    have hn : (nN : G) = (a : G) * (b : G) :=
      congrArg Subtype.val hab.symm
    change
      ((x : G) * (a : G) * (x : G)⁻¹) *
          ((x : G) * (b : G) * (x : G)⁻¹) =
        (a : G) * (b : G)
    calc
      ((x : G) * (a : G) * (x : G)⁻¹) *
          ((x : G) * (b : G) * (x : G)⁻¹) =
          (x : G) * (nN : G) * (x : G)⁻¹ := by
            rw [hn]
            group
      _ = (nN : G) := hfix
      _ = (a : G) * (b : G) := hn
  have haFix : (x : G) * (a : G) * (x : G)⁻¹ = a := by
    exact congrArg (fun z : (A.subgroupOf N) ×
      (B.subgroupOf N) ↦ (((z.1 : N) : G))) hpair
  have hbFix : (x : G) * (b : G) * (x : G)⁻¹ = b := by
    exact congrArg (fun z : (A.subgroupOf N) ×
      (B.subgroupOf N) ↦ (((z.2 : N) : G))) hpair
  let aA : A := ⟨(a : G), a.property⟩
  let bB : B := ⟨(b : G), b.property⟩
  have haOne : aA = 1 := hregA x hx aA haFix
  have hbOne : bB = 1 := hregB x hx bB hbFix
  apply Subtype.ext
  have hn : (nN : G) = (a : G) * (b : G) :=
    congrArg Subtype.val hab.symm
  have haOneG : (a : G) = 1 :=
    congrArg (fun z : A ↦ (z : G)) haOne
  have hbOneG : (b : G) = 1 :=
    congrArg (fun z : B ↦ (z : G)) hbOne
  simpa [haOneG, hbOneG] using hn

/-- A semiregular internal semidirect product is a Frobenius
decomposition in its generated subgroup. -/
private theorem frobenius_of_semidirect_semiregular_structure
    {G : Type u} [Group G]
    {A B N : Subgroup G}
    (h : IsInternalSemidirectProductIn A B N)
    (hA : A ≠ ⊥) (hB : B ≠ ⊥)
    (hreg : IsSemiregularConjugation A B) :
    IsFrobeniusDecomposition (A.subgroupOf N) (B.subgroupOf N) := by
  refine
    { isComplement := h.2.2.2
      kernel_normal := h.2.2.1
      kernel_ne_bot := ?_
      complement_ne_bot := ?_
      fixedPointFree := ?_ }
  · intro hbot
    apply hA
    apply le_antisymm _ bot_le
    intro a ha
    let aN : N := ⟨a, h.1 ha⟩
    have haBot : aN ∈ (⊥ : Subgroup N) := by
      rw [← hbot]
      exact ha
    exact Subgroup.mem_bot.mpr
      (congrArg (fun z : N ↦ (z : G)) (Subgroup.mem_bot.mp haBot))
  · intro hbot
    apply hB
    apply le_antisymm _ bot_le
    intro b hb
    let bN : N := ⟨b, h.2.1 hb⟩
    have hbBot : bN ∈ (⊥ : Subgroup N) := by
      rw [← hbot]
      exact hb
    exact Subgroup.mem_bot.mpr
      (congrArg (fun z : N ↦ (z : G)) (Subgroup.mem_bot.mp hbBot))
  · intro b hb a hfix
    let bB : B := ⟨((b : N) : G), b.property⟩
    let aA : A := ⟨((a : N) : G), a.property⟩
    have hbB : bB ≠ 1 := by
      intro hb1
      apply hb
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : B ↦ (z : G)) hb1
    have ha1 := hreg bB hbB aA (by
      exact congrArg (fun z : N ↦ (z : G)) hfix)
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : A ↦ (z : G)) ha1

/-- Reassociate `S ⋊ (U ⋊ K)` as `(S ⋊ U) ⋊ K`. -/
private theorem semidirectProduct_reassociate_structure
    {G : Type u} [Group G]
    {S U K F M : Subgroup G}
    (hSF : IsInternalSemidirectProductIn S F M)
    (hUK : IsInternalSemidirectProductIn U K F) :
    IsInternalSemidirectProductIn (S ⊔ U) K M := by
  have hSU := semidirectProduct_restrict_right_structure hSF hUK.1
  have hSM : S ≤ M := hSF.1
  have hUM : U ≤ M := hUK.1.trans hSF.2.1
  have hKM : K ≤ M := hUK.2.1.trans hSF.2.1
  have hMnormS : M ≤ Subgroup.normalizer (S : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSM).mp hSF.2.2.1
  have hFnormU : F ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUK.1).mp hUK.2.2.1
  have hKnormSU : K ≤ Subgroup.normalizer ((S ⊔ U : Subgroup G) : Set G) := by
    exact (le_inf (hKM.trans hMnormS)
      (hUK.2.1.trans hFnormU)).trans
        (Subgroup.normalizer_inf_normalizer_le_normalizer_sup S U)
  have hMeq : M = S ⊔ (U ⊔ K) := by
    calc
      M = S ⊔ F := (semidirectProduct_sup_eq_ambient hSF).symm
      _ = S ⊔ (U ⊔ K) := by
        rw [semidirectProduct_sup_eq_ambient hUK]
  have hMnormSU : M ≤ Subgroup.normalizer ((S ⊔ U : Subgroup G) : Set G) := by
    rw [hMeq]
    exact sup_le
      (le_sup_left.trans Subgroup.le_normalizer)
      (sup_le (le_sup_right.trans Subgroup.le_normalizer) hKnormSU)
  have hAnormal : ((S ⊔ U).subgroupOf M).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (H := M) (N := S ⊔ U) hMnormSU
  have hdis : Disjoint ((S ⊔ U).subgroupOf M) (K.subgroupOf M) := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro x hx
    let xA : (S ⊔ U : Subgroup G) := ⟨(x : G), hx.1⟩
    obtain ⟨⟨s, u⟩, hsu⟩ := hSU.2.2.2.2 xA
    have hxsu : (x : G) = (s : G) * (u : G) :=
      congrArg Subtype.val hsu.symm
    have hsF : (s : G) ∈ F := by
      have hxuF : (x : G) * (u : G)⁻¹ ∈ F :=
        F.mul_mem (hUK.2.1 hx.2) (F.inv_mem (hUK.1 u.property))
      simpa [hxsu, mul_assoc] using hxuF
    have hsBot : (s : G) ∈ (⊥ : Subgroup G) := by
      have hsInf : (⟨(s : G), hSM s.property⟩ : M) ∈
          (S.subgroupOf M) ⊓ (F.subgroupOf M) :=
        ⟨s.property, hsF⟩
      have := hSF.2.2.2.disjoint.le_bot hsInf
      simpa using this
    have hsOne : (s : G) = 1 := Subgroup.mem_bot.mp hsBot
    have hxu : (x : G) = u := by simpa [hsOne] using hxsu
    have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
      have huK : (u : G) ∈ K := hxu ▸ hx.2
      have huInf : (⟨(u : G), hUK.1 u.property⟩ : F) ∈
          (U.subgroupOf F) ⊓ (K.subgroupOf F) :=
        ⟨u.property, huK⟩
      have := hUK.2.2.2.disjoint.le_bot huInf
      simpa [hxu] using this
    simpa using hxBot
  refine ⟨sup_le hSM hUM, hKM, hAnormal, ?_⟩
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis
  letI : ((S ⊔ U).subgroupOf M).Normal := hAnormal
  rw [← Subgroup.normal_mul]
  have hsup : (S ⊔ U).subgroupOf M ⊔ K.subgroupOf M = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (sup_le hSM hUM) hKM,
      sup_assoc, ← hMeq]
    exact Subgroup.subgroupOf_self M
  rw [hsup]
  rfl

/-- In the reassociated product, a nontrivial subgroup of the
semiregular actor has centralizer equal to the sigma centralizer of the
whole actor. -/
private theorem centralizer_reassociated_eq_structure
    {G : Type u} [Group G]
    {S U K A X : Subgroup G}
    (hSU : IsInternalSemidirectProductIn S U A)
    (hXK : X ≤ K) (hXne : X ≠ ⊥)
    (hKnormS : K ≤ Subgroup.normalizer (S : Set G))
    (hKnormU : K ≤ Subgroup.normalizer (U : Set G))
    (hprime : IsPrimeAction S K)
    (hreg : IsSemiregularConjugation U K) :
    centralizerWithin A X = centralizerWithin S K := by
  apply le_antisymm
  · intro z hz
    let zA : A := ⟨z, hz.1⟩
    obtain ⟨⟨s, u⟩, hsu⟩ := hSU.2.2.2.2 zA
    have hzsu : z = (s : G) * (u : G) :=
      congrArg Subtype.val hsu.symm
    have hcomponents (x : G) (hx : x ∈ X) :
        x * (s : G) * x⁻¹ = s ∧
          x * (u : G) * x⁻¹ = u := by
      let sx : S.subgroupOf A :=
        ⟨⟨x * (s : G) * x⁻¹,
          hSU.1 ((Subgroup.mem_normalizer_iff.mp
            (hKnormS (hXK hx)) (s : G)).mp s.property)⟩,
          (Subgroup.mem_normalizer_iff.mp
            (hKnormS (hXK hx)) (s : G)).mp s.property⟩
      let ux : U.subgroupOf A :=
        ⟨⟨x * (u : G) * x⁻¹,
          hSU.2.1 ((Subgroup.mem_normalizer_iff.mp
            (hKnormU (hXK hx)) (u : G)).mp u.property)⟩,
          (Subgroup.mem_normalizer_iff.mp
            (hKnormU (hXK hx)) (u : G)).mp u.property⟩
      have hxz : x * z * x⁻¹ = z := by
        have hcomm := hz.2 x hx
        calc
          x * z * x⁻¹ = z * x * x⁻¹ := by rw [hcomm]
          _ = z := by simp
      have hpair : (sx, ux) = (s, u) := by
        apply hSU.2.2.2.1
        apply Subtype.ext
        change (x * (s : G) * x⁻¹) *
            (x * (u : G) * x⁻¹) = (s : G) * (u : G)
        calc
          (x * (s : G) * x⁻¹) *
              (x * (u : G) * x⁻¹) = x * z * x⁻¹ := by
                rw [hzsu]
                group
          _ = z := hxz
          _ = (s : G) * (u : G) := hzsu
      exact ⟨congrArg (fun w : (S.subgroupOf A) ×
          (U.subgroupOf A) ↦ (((w.1 : A) : G))) hpair,
        congrArg (fun w : (S.subgroupOf A) ×
          (U.subgroupOf A) ↦ (((w.2 : A) : G))) hpair⟩
    obtain ⟨xX, hxX1⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.mp hXne
    let xK : K := ⟨(xX : G), hXK xX.property⟩
    let uU : U := ⟨(u : G), u.property⟩
    have hxK1 : xK ≠ 1 := by
      intro hx
      apply hxX1
      exact Subtype.ext (congrArg (fun k : K => (k : G)) hx)
    have hfixU : (xK : G) * (uU : G) * (xK : G)⁻¹ = uU := by
      simpa only [xK, uU] using
        (hcomponents (xX : G) xX.property).2
    have huOne : uU = 1 := hreg xK hxK1 uU hfixU
    have hzS : z ∈ S := by
      rw [hzsu, show (u : G) = 1 from
        congrArg (fun v : U => (v : G)) huOne]
      exact S.mul_mem s.property S.one_mem
    have hzCX : z ∈ centralizerWithin S X := ⟨hzS, hz.2⟩
    rw [hprime.centralizer_eq hXK hXne] at hzCX
    exact hzCX
  · intro z hz
    refine ⟨hSU.1 hz.1, ?_⟩
    exact (Subgroup.centralizer_le hXK) hz.2

/-- The coprime normalizer calculation used in Proposition 14.2(b).
This is the subgroup-theoretic content of the source identity
`coprime_norm_cent`: after conjugating the complement back by the
solvable normal factor, coprime conjugator adjustment makes the
conjugator centralize the prescribed normal subgroup of the complement. -/
private theorem normalizerWithin_eq_centralizer_sup_structure
    {G : Type u} [Group G] [Finite G]
    {A K M X : Subgroup G}
    (hsd : IsInternalSemidirectProductIn A K M)
    (hcop : (Nat.card A).Coprime (Nat.card K))
    (hsolM : IsSolvable M)
    (hXK : X ≤ K) (hXnormal : (X.subgroupOf K).Normal) :
    normalizerWithin M X = centralizerWithin A X ⊔ K := by
  classical
  have hMnormA : M ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hsd.1).mp hsd.2.2.1
  have hKnormX : K ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXK).mp hXnormal
  have hXnormK : X ≤ Subgroup.normalizer (K : Set G) :=
    hXK.trans Subgroup.le_normalizer
  apply le_antisymm
  · intro n hn
    let Kn : Subgroup G :=
      K.map (MulAut.conj n).toMonoidHom
    have hnNormA : n ∈ Subgroup.normalizer (A : Set G) :=
      hMnormA hn.1
    have hnNormM : n ∈ Subgroup.normalizer (M : Set G) :=
      Subgroup.le_normalizer hn.1
    have hAmap : A.map (MulAut.conj n).toMonoidHom = A :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hnNormA
    have hMmap : M.map (MulAut.conj n).toMonoidHom = M :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hnNormM
    have hsdKn : IsInternalSemidirectProductIn A Kn M := by
      have hmap :=
        semidirectProduct_map_mulEquiv_structure hsd (MulAut.conj n)
      simpa only [Kn, hAmap, hMmap] using hmap
    have hKnM : Kn ≤ M := hsdKn.2.1

    let AM : Subgroup M := A.subgroupOf M
    let KM : Subgroup M := K.subgroupOf M
    let KnM : Subgroup M := Kn.subgroupOf M
    letI : AM.Normal := by simpa only [AM] using hsd.2.2.1
    letI : IsSolvable M := hsolM
    letI : IsSolvable AM := isSolvable_subgroup_of_isSolvable AM
    have hcopIndex : (Nat.card AM).Coprime AM.index := by
      rw [hsd.2.2.2.symm.index_eq_card,
        MathlibSupport.natCard_subgroupOf_eq hsd.1,
        MathlibSupport.natCard_subgroupOf_eq hsd.2.1]
      exact hcop
    obtain ⟨a, ha⟩ :=
      Subgroup.solvable_complement_conjugacy hcopIndex
        hsd.2.2.2 hsdKn.2.2.2
    let aM : M := (a : AM)
    let aG : G := (aM : G)
    have haA : aG ∈ A := a.property
    have hKnConj :
        K.map (MulAut.conj aG).toMonoidHom = Kn := by
      exact ambient_map_conj_eq_of_subgroupOf_structure
        (G := G) (M := M) (A := K) (B := Kn)
        hsd.2.1 hKnM aM ha

    have hnMapX : X.map (MulAut.conj n).toMonoidHom = X :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hn.2
    have hXnormKn : X ≤ Subgroup.normalizer (Kn : Set G) := by
      have hmapped : X.map (MulAut.conj n).toMonoidHom ≤
          (Subgroup.normalizer (K : Set G)).map
            (MulAut.conj n).toMonoidHom :=
        Subgroup.map_mono hXnormK
      rw [Subgroup.map_equiv_normalizer_eq K (MulAut.conj n),
        hnMapX] at hmapped
      simpa only [Kn] using hmapped
    let pi : Set ℕ := primeSupport (Nat.card X)
    have hApi : IsPiNumber piᶜ (Nat.card A) := by
      intro q hq hqA hqPi
      apply (Nat.not_coprime_of_dvd_of_dvd hq.one_lt hqA
        (hqPi.2.trans (Subgroup.card_dvd_of_le hXK))) hcop
    have hXpi : IsPiNumber pi (Nat.card X) :=
      IsPiNumber.primeSupport_self
    have hXnormA : X ≤ Subgroup.normalizer (A : Set G) :=
      hXK.trans (hsd.2.1.trans hMnormA)
    have hAdjSol : IsSolvable
        (((A ⊔ X) ⊓ Subgroup.normalizer (Kn : Set G) :
          Subgroup G)) := by
      have hleM :
          ((A ⊔ X) ⊓ Subgroup.normalizer (Kn : Set G) :
            Subgroup G) ≤ M :=
        inf_le_left.trans (sup_le hsd.1 (hXK.trans hsd.2.1))
      letI : IsSolvable M := hsolM
      exact isSolvable_of_injective (Subgroup.inclusion hleM)
        (Subgroup.inclusion_injective hleM)
    have hKnBack :
        Kn = K.map (MulAut.conj (aG⁻¹)⁻¹).toMonoidHom := by
      simpa only [inv_inv] using hKnConj.symm
    obtain ⟨c, hc, hKnC⟩ :=
      exists_centralizerWithin_conjugator_of_coprime_join
        (pi := pi) hXnormA hApi hXpi hXnormK hXnormKn
          hAdjSol (A.inv_mem haA) hKnBack

    let t : G := c * n
    have htM : t ∈ M := M.mul_mem (hsd.1 hc.1) hn.1
    have htMap : K.map (MulAut.conj t).toMonoidHom = K := by
      calc
        K.map (MulAut.conj t).toMonoidHom =
            (K.map (MulAut.conj n).toMonoidHom).map
              (MulAut.conj c).toMonoidHom := by
          rw [Subgroup.map_map]
          congr 1
          ext z
          simp [t, MulAut.conj_apply, mul_assoc]
        _ = Kn.map (MulAut.conj c).toMonoidHom := by rw [show
              K.map (MulAut.conj n).toMonoidHom = Kn from rfl]
        _ = (K.map (MulAut.conj c⁻¹).toMonoidHom).map
              (MulAut.conj c).toMonoidHom := by rw [hKnC]
        _ = K := by
          rw [Subgroup.map_map]
          convert Subgroup.map_id K using 1
          ext z
          simp [MulAut.conj_apply, mul_assoc]
    have htNormK : t ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr htMap

    let tM : M := ⟨t, htM⟩
    obtain ⟨⟨a₀, k⟩, hak⟩ := hsd.2.2.2.2 tM
    have htEq : t = (a₀ : G) * (k : G) :=
      congrArg Subtype.val hak.symm
    have ha₀NormK : (a₀ : G) ∈
        Subgroup.normalizer (K : Set G) := by
      have hkNormK : (k : G) ∈ Subgroup.normalizer (K : Set G) :=
        Subgroup.le_normalizer k.property
      have hprod := (Subgroup.normalizer (K : Set G)).mul_mem htNormK
        ((Subgroup.normalizer (K : Set G)).inv_mem hkNormK)
      simpa [htEq] using hprod
    have hKnormA : K ≤ Subgroup.normalizer (A : Set G) :=
      hsd.2.1.trans hMnormA
    have ha₀CentK : (a₀ : G) ∈ Subgroup.centralizer (K : Set G) :=
      mem_centralizer_of_mem_of_mem_normalizer_of_coprime
        hKnormA hcop a₀.property ha₀NormK
    have htJoin : t ∈ centralizerWithin A X ⊔ K := by
      rw [htEq]
      apply (centralizerWithin A X ⊔ K).mul_mem
      · exact (show centralizerWithin A X ≤
          centralizerWithin A X ⊔ K from le_sup_left)
          ⟨a₀.property, (Subgroup.centralizer_le hXK) ha₀CentK⟩
      · exact (show K ≤ centralizerWithin A X ⊔ K from
          le_sup_right) k.property
    have hcInv : c⁻¹ ∈ centralizerWithin A X :=
      (centralizerWithin A X).inv_mem hc
    have hnEq : n = c⁻¹ * t := by simp [t]
    rw [hnEq]
    exact (centralizerWithin A X ⊔ K).mul_mem
      ((show centralizerWithin A X ≤ centralizerWithin A X ⊔ K from
        le_sup_left) hcInv) htJoin
  · apply sup_le
    · intro a ha
      exact ⟨hsd.1 ha.1,
        Subgroup.centralizer_le_normalizer (X : Set G) ha.2⟩
    · intro k hk
      exact ⟨hsd.2.1 hk, hKnormX hk⟩

/-- A centralizer in the normal factor and the complement form the direct
product occurring in Proposition 14.2(b). -/
private theorem directProduct_complement_centralizer_structure
    {G : Type u} [Group G]
    {A K M C N : Subgroup G}
    (hsd : IsInternalSemidirectProductIn A K M)
    (hC : C = centralizerWithin A K)
    (hN : N = C ⊔ K) :
    IsInternalDirectProductIn K C N := by
  subst C
  subst N
  have hdisAK : A ⊓ K = ⊥ := internalSemidirectProduct_inf_eq_bot hsd
  have hdis : Disjoint
      (K.subgroupOf (centralizerWithin A K ⊔ K))
      ((centralizerWithin A K).subgroupOf
        (centralizerWithin A K ⊔ K)) := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro z hz
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    apply Subgroup.mem_bot.mp
    rw [← hdisAK]
    exact ⟨hz.2.1, hz.1⟩
  have hcomp :
      (K.subgroupOf (centralizerWithin A K ⊔ K)).IsComplement'
        ((centralizerWithin A K).subgroupOf
          (centralizerWithin A K ⊔ K)) := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis
    have hnormK :
        (K.subgroupOf (centralizerWithin A K ⊔ K)).Normal := by
      apply Subgroup.normal_subgroupOf_of_le_normalizer
      apply sup_le
      · exact inf_le_right.trans
          (Subgroup.centralizer_le_normalizer (K : Set G))
      · exact Subgroup.le_normalizer
    letI :
        (K.subgroupOf (centralizerWithin A K ⊔ K)).Normal := hnormK
    rw [← Subgroup.normal_mul]
    rw [← Subgroup.subgroupOf_sup le_sup_right le_sup_left,
      sup_comm, Subgroup.subgroupOf_self]
    rfl
  refine
    { left_le := le_sup_right
      right_le := le_sup_left
      complement := hcomp
      commute := ?_ }
  intro k c
  change (k : G) * (c : G) = (c : G) * (k : G)
  exact c.property.2 (k : G) k.property

/-- Two normal rank-one `p`-lines in a group of elementary-abelian
`p`-rank one coincide.  Distinct lines would commute and generate an
elementary-abelian subgroup of rank two. -/
private theorem rankOne_eq_of_no_rankTwo_of_normal_structure
    {G : Type u} [Group G] [Finite G]
    {K X Y : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hNoRank : ¬ HasElementaryAbelianRankAtLeast p 2 K)
    (hX : RankOneLineIn p K X)
    (hY : RankOneLineIn p K Y)
    (hXnormal : (X.subgroupOf K).Normal)
    (hYnormal : (Y.subgroupOf K).Normal) :
    X = Y := by
  classical
  by_contra hne
  have hdis : Disjoint X Y := by
    have hXprime : (Nat.card X).Prime := by
      rw [hX.2.card_eq, pow_one]
      exact Fact.out
    letI : Fact (Nat.card X).Prime := ⟨hXprime⟩
    rcases (Y.subgroupOf X).eq_bot_or_eq_top_of_prime_card with
      hbot | htop
    · exact disjoint_comm.mp (Subgroup.subgroupOf_eq_bot.mp hbot)
    · have hXY : X ≤ Y := Subgroup.subgroupOf_eq_top.mp htop
      have hcard : Nat.card Y ≤ Nat.card X := by
        rw [hX.2.card_eq, hY.2.card_eq]
      exact (hne (Subgroup.eq_of_le_of_card_ge hXY hcard)).elim
  have hdisK :
      Disjoint (X.subgroupOf K) (Y.subgroupOf K) := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro z hz
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    apply Subgroup.mem_bot.mp
    rw [← disjoint_iff.mp hdis]
    exact hz
  have hcomm : ∀ x ∈ X, ∀ y ∈ Y, Commute x y := by
    intro x hx y hy
    let xK : K := ⟨x, hX.1 hx⟩
    let yK : K := ⟨y, hY.1 hy⟩
    have hxyK : Commute xK yK :=
      Subgroup.commute_of_normal_of_disjoint
        (X.subgroupOf K) (Y.subgroupOf K)
        hXnormal hYnormal hdisK xK yK hx hy
    exact congrArg Subtype.val hxyK.eq
  let L : Subgroup G := X ⊔ Y
  have hLcard : Nat.card L = p ^ 2 := by
    dsimp only [L]
    rw [natCard_sup_eq_mul_of_disjoint_of_commute hdis hcomm,
      hX.2.card_eq, hY.2.card_eq]
    simp [pow_two]
  have hLp : IsPGroup p L := IsPGroup.of_card (n := 2) hLcard
  let XL : Subgroup L := X.subgroupOf L
  let YL : Subgroup L := Y.subgroupOf L
  have hXLrank : IsElementaryAbelianOfRank p 1 XL := by
    apply isElementaryAbelianOfRank_one_of_card_eq_prime
    rw [MathlibSupport.natCard_subgroupOf_eq (show X ≤ L from le_sup_left),
      hX.2.card_eq, pow_one]
  have hYLrank : IsElementaryAbelianOfRank p 1 YL := by
    apply isElementaryAbelianOfRank_one_of_card_eq_prime
    rw [MathlibSupport.natCard_subgroupOf_eq (show Y ≤ L from le_sup_right),
      hY.2.card_eq, pow_one]
  have hdisL : Disjoint XL YL := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro z hz
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    apply Subgroup.mem_bot.mp
    rw [← disjoint_iff.mp hdis]
    exact hz
  have hcommL : ∀ x ∈ XL, ∀ y ∈ YL, Commute x y := by
    intro x hx y hy
    apply Subtype.ext
    exact (hcomm (x : G) hx (y : G) hy).eq
  have hsupRank : IsElementaryAbelianOfRank p 2 (XL ⊔ YL) := by
    simpa using
      (isElementaryAbelianOfRank_sup_of_disjoint_of_commute
        hLp hXLrank hYLrank hdisL hcommL)
  have hsupTop : XL ⊔ YL = ⊤ := by
    change X.subgroupOf L ⊔ Y.subgroupOf L = ⊤
    rw [← Subgroup.subgroupOf_sup
      (show X ≤ L from le_sup_left) (show Y ≤ L from le_sup_right)]
    exact Subgroup.subgroupOf_self L
  have htopRank : IsElementaryAbelianOfRank p 2 (⊤ : Subgroup L) := by
    simpa only [hsupTop] using hsupRank
  have hmappedRank : IsElementaryAbelianOfRank p 2
      ((⊤ : Subgroup L).map L.subtype) :=
    htopRank.map_of_injective L.subtype L.subtype_injective
  have hmapTop : (⊤ : Subgroup L).map L.subtype = L := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  apply hNoRank
  refine ⟨L, ?_, ?_⟩
  · exact sup_le hX.1 hY.1
  · simpa only [hmapTop] using hmappedRank

/-- Every pi-subgroup lies in a normal pi-Hall subgroup. -/
private theorem isPiNumber_le_normal_isHall_structure
    {G : Type u} [Group G] [Finite G] {pi : Set ℕ}
    {N L : Subgroup G} (hNnormal : N.Normal)
    (hNHall : IsHall pi N) (hLpi : IsPiNumber pi (Nat.card L)) :
    L ≤ N := by
  letI : N.Normal := hNnormal
  have hcop : (Nat.card L).Coprime N.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpL hpIndex
    exact hNHall.isPiNumber_index hp hpIndex (hLpi hp hpL)
  intro x hxL
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have horderL : orderOf (q x) ∣ Nat.card L :=
    (orderOf_map_dvd q x).trans (L.orderOf_dvd_natCard hxL)
  have horderIndex : orderOf (q x) ∣ N.index := by
    simpa only [N.index_eq_card] using orderOf_dvd_natCard (q x)
  have horderOne : orderOf (q x) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horderL horderIndex
  exact (QuotientGroup.eq_one_iff x).mp
    (by simpa [q] using orderOf_eq_one_iff.mp horderOne)

/-- A Sylow subgroup of a Hall subgroup is Sylow in the ambient finite
group whenever its prime belongs to the Hall prime set. -/
private theorem exists_sylow_eq_map_of_sylow_hall_structure
    {L : Type u} [Group L] [Finite L]
    {pi : Set ℕ} {p : ℕ} (hp : p.Prime)
    {B : Subgroup L} (hB : IsHall pi B) (hpPi : p ∈ pi)
    (P : Sylow p B) :
    ∃ Q : Sylow p L,
      (Q : Subgroup L) = (P : Subgroup B).map B.subtype := by
  letI : Fact p.Prime := ⟨hp⟩
  let R : Subgroup L := (P : Subgroup B).map B.subtype
  have hRp : IsPGroup p R := P.isPGroup'.map B.subtype
  have hpBindex : ¬ p ∣ B.index := by
    intro hpIndex
    exact hB.isPiNumber_index hp hpIndex hpPi
  have hpRindex : ¬ p ∣ R.index := by
    dsimp only [R]
    rw [Subgroup.index_map_subtype]
    exact hp.not_dvd_mul P.not_dvd_index hpBindex
  exact ⟨hRp.toSylow hpRindex, rfl⟩

/-- Same-ambient form of Sylow transport through a Hall subgroup. -/
private theorem exists_sylow_of_hall_with_same_ambient_structure
    {G : Type u} [Group G] [Finite G]
    {H K : Subgroup G} {pi : Set ℕ} {p : ℕ}
    (hp : p.Prime) (hHK : H ≤ K)
    (hHall : IsHall pi (H.subgroupOf K)) (hpPi : p ∈ pi)
    (P : Sylow p H) :
    ∃ Q : Sylow p K, ambientSylow K Q = ambientSylow H P := by
  letI : Fact p.Prime := ⟨hp⟩
  let HK : Subgroup K := H.subgroupOf K
  let e : H ≃* HK := (Subgroup.subgroupOfEquivOfLe hHK).symm
  let PHK : Sylow p HK :=
    P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨Q, hQ⟩ :=
    exists_sylow_eq_map_of_sylow_hall_structure hp hHall hpPi PHK
  refine ⟨Q, ?_⟩
  change (Q : Subgroup K).map K.subtype =
    (P : Subgroup H).map H.subtype
  rw [hQ, Subgroup.map_map]
  simp only [PHK, Sylow.coe_mapSurjective, Subgroup.map_map]
  apply congrArg (fun f : H →* G ↦ (P : Subgroup H).map f)
  ext x
  rfl

/-- Pull an inclusion in a conjugate subgroup back by the inverse
conjugation. -/
private theorem map_conj_inv_le_of_le_map_conj_structure
    {G : Type u} [Group G] {A B : Subgroup G} {g : G}
    (h : A ≤ B.map (MulAut.conj g).toMonoidHom) :
    A.map (MulAut.conj g⁻¹).toMonoidHom ≤ B := by
  rintro z ⟨a, ha, rfl⟩
  rcases h ha with ⟨b, hb, hba⟩
  have heq : g⁻¹ * a * (g⁻¹)⁻¹ = b := by
    rw [← hba]
    simp [MulAut.conj_apply, mul_assoc]
  change g⁻¹ * a * (g⁻¹)⁻¹ ∈ B
  rw [heq]
  exact hb

/-! ## Proposition 14.2 -/

/-- `BGsection14.v: Ptype_structure`, Proposition 14.2.

Containment of `K` in `M` is explicit in Lean; MathComp includes it in
the notation `kappa(M).-Hall(M) K`. -/
theorem Ptype_structure
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M K : Subgroup G}
    (hM : M ∈ typePMaximalSubgroups)
    (hKM : K ≤ M)
    (hK : IsHall (kappaPrimes M) (K.subgroupOf M)) :
    PTypeStructure M K := by
  classical
  have hmaxM : M ∈ minSimple_max_groups (G := G) := hM.1
  have hKne : K ≠ ⊥ := by
    intro hKbot
    have hF := (trivg_kappa hmaxM hKM hK).mp hKbot
    exact hM.2 hF

  /- The source first chooses a sigma complement `E` containing `K`, then
  its tau-one and tau-three Hall factors and finally the tau-two factor.
  Keeping these witnesses in scope is important: the same decomposition
  is used in parts (a), (b), (c), and (g). -/
  have hKsigmaCompl : IsPiNumber (sigmaPrimes M)ᶜ (Nat.card K) := by
    have hk := hK.isPiNumber_card
    rw [MathlibSupport.natCard_subgroupOf_eq hKM] at hk
    exact hk.mono (kappa_sigma' M)
  obtain ⟨E, hKE, hEM, hHallE⟩ :=
    MathlibSupport.exists_ambient_isHall_ge_of_isSolvable hKM (mmax_sol hmaxM)
      (sigmaPrimes M)ᶜ hKsigmaCompl
  obtain ⟨E₃, hE₃E, hHallE₃⟩ :=
    (ex_tau13_compl hEM hHallE).2
  have hKsol : IsSolvable K :=
    mFT_sol (lt_of_le_of_lt hKM (mmax_proper hmaxM))
  obtain ⟨F₁, hF₁K, hHallF₁⟩ :=
    MathlibSupport.exists_ambient_isHall_of_isSolvable hKsol (tau1Primes M)
  have hF₁E : F₁ ≤ E := hF₁K.trans hKE
  have hF₁tau1 : IsPiNumber (tau1Primes M) (Nat.card F₁) := by
    simpa only [MathlibSupport.natCard_subgroupOf_eq hF₁K] using
      hHallF₁.isPiNumber_card
  obtain ⟨E₁, hF₁E₁, hE₁E, hHallE₁⟩ :=
    MathlibSupport.exists_ambient_isHall_ge_of_isSolvable hF₁E
      (sigma_compl_sol hEM hHallE) (tau1Primes M) hF₁tau1
  obtain ⟨E₂, hE₂E, hHallE₂, hCompl⟩ :=
    ex_tau2_compl hEM hHallE hE₁E hHallE₁ hE₃E hHallE₃
  have hComplCtx := sigma_compl_context hmaxM hCompl

  have hE₁M : E₁ ≤ M := hE₁E.trans hEM
  have hE₃M : E₃ ≤ M := hE₃E.trans hEM

  /- `tau13_nonregular` is the dichotomy at the heart of the proof.  The
  package below is exactly the common data retained by the source after
  the two branches. -/
  obtain ⟨U, hKappaCompl, hUKsd, hSigmaUKsd, hUcomm, hPrime, hReg,
      hRankOneNorm, hE₁ne, hE₁K⟩ :
      ∃ U : Subgroup G,
        KappaComplement M U K ∧
        IsInternalSemidirectProductIn U K (U ⊔ K) ∧
        IsInternalSemidirectProductIn (sigmaCore M) (U ⊔ K) M ∧
        IsMulCommutative U ∧
        IsPrimeAction (sigmaCore M) K ∧
        IsSemiregularConjugation U K ∧
        (∀ {p : ℕ} [Fact p.Prime] {X : Subgroup G},
          RankOneLineIn p K X → (X.subgroupOf K).Normal) ∧
        E₁ ≠ ⊥ ∧ E₁ ≤ K := by
    by_cases hKt₁ : IsPiNumber (tau1Primes M) (Nat.card K)
    · have hKF₁ : K = F₁ := by
        exact intermediate_eq_isHall_of_isPiNumber_structure
          (K := F₁) (E := K) (M := K)
          hF₁K le_rfl hHallF₁ hKt₁
      have hKE₁ : K ≤ E₁ := hKF₁.le.trans hF₁E₁
      have hprimeE₁ : IsPrimeAction (sigmaCore M) E₁ :=
        tau1_primact_Msigma hmaxM hEM hHallE hE₁E hHallE₁

      let q : ℕ := Nat.minFac (Nat.card K)
      have hq : q.Prime :=
        Nat.minFac_prime (K.one_lt_card_iff_ne_bot.mpr hKne).ne'
      letI : Fact q.Prime := ⟨hq⟩
      have hqK : q ∣ Nat.card K := Nat.minFac_dvd (Nat.card K)
      obtain ⟨Y, hYK, hY⟩ :=
        exists_rankOne_le_of_prime_dvd_structure hq hqK
      have hqKappa : q ∈ kappaPrimes M := by
        have hKpi := hK.isPiNumber_card
        rw [MathlibSupport.natCard_subgroupOf_eq hKM] at hKpi
        exact hKpi hq hqK
      have hYlineM : RankOneLineIn q M Y :=
        ⟨hYK.trans hKM, hY⟩
      have hCYne : centralizerWithin (sigmaCore M) Y ≠ ⊥ :=
        kappa_nonregular hqKappa hYlineM

      have ht₁k : tau1Primes M ⊆ kappaPrimes M := by
        intro p hpTau₁
        letI : Fact p.Prime := ⟨hpTau₁.1⟩
        rcases hpTau₁.2.2.1 with ⟨P, hPM, hP⟩
        have hpP : p ∣ Nat.card P := by
          rw [hP.card_eq, pow_one]
        have hpM : p ∣ Nat.card M :=
          hpP.trans (Subgroup.card_dvd_of_le hPM)
        have hpE : p ∣ Nat.card E :=
          prime_dvd_card_of_mem_isHall_structure hEM hHallE
            hpTau₁.1 hpTau₁.2.1 hpM
        have hpE₁ : p ∣ Nat.card E₁ :=
          prime_dvd_card_of_mem_isHall_structure hE₁E hHallE₁
            hpTau₁.1 hpTau₁ hpE
        obtain ⟨X, hXE₁, hX⟩ :=
          exists_rankOne_le_of_prime_dvd_structure hpTau₁.1 hpE₁
        have hXE : X ≤ E := hXE₁.trans hE₁E
        have hCXE₁ := hprimeE₁.centralizer_eq hXE₁ hX.ne_bot
        have hCYE₁ := hprimeE₁.centralizer_eq
          (hYK.trans hKE₁) hY.ne_bot
        refine ⟨Or.inl hpTau₁, X, ⟨hXE.trans hEM, hX⟩, ?_⟩
        rw [hCXE₁, ← hCYE₁]
        exact hCYne

      have hE₁pi : IsPiNumber (kappaPrimes M) (Nat.card E₁) := by
        have hpi := hHallE₁.isPiNumber_card
        rw [MathlibSupport.natCard_subgroupOf_eq hE₁E] at hpi
        exact hpi.mono ht₁k
      have hE₁eqK : E₁ = K :=
        intermediate_eq_isHall_of_isPiNumber_structure
          hKE₁ hE₁M hK hE₁pi
      have hE₁ne : E₁ ≠ ⊥ := by simpa [hE₁eqK] using hKne

      let U : Subgroup G := E₃ ⊔ E₂
      have hUKsd : IsInternalSemidirectProductIn U K (U ⊔ K) := by
        have hsup : U ⊔ K = E := by
          simpa only [U, hE₁eqK] using
            semidirectProduct_sup_eq_ambient
              hComplCtx.E₃₂_E₁_sdprod
        simpa only [U, hE₁eqK, hsup] using
          hComplCtx.E₃₂_E₁_sdprod
      have hUKE : U ⊔ K = E := by
        simpa only [U, hE₁eqK] using
          semidirectProduct_sup_eq_ambient
            hComplCtx.E₃₂_E₁_sdprod
      have hUE : U ≤ E := by
        exact sup_le hE₃E hE₂E
      have hUM : U ≤ M := hUE.trans hEM
      have hSigmaUKsd :
          IsInternalSemidirectProductIn (sigmaCore M) (U ⊔ K) M := by
        simpa only [hUKE] using sdprod_sigma hmaxM hEM hHallE
      have hPrime : IsPrimeAction (sigmaCore M) K := by
        simpa only [← hE₁eqK] using hprimeE₁

      have hlineE₃ : ∀ {p : ℕ} [Fact p.Prime] {X : Subgroup G},
          RankOneLineIn p K X →
            centralizerWithin E₃ X = ⊥ := by
        intro p _ X hX
        have hpK : p ∣ Nat.card K := by
          have hpX : p ∣ Nat.card X := by
            rw [hX.2.card_eq, pow_one]
          exact hpX.trans (Subgroup.card_dvd_of_le hX.1)
        have hpTau₁ : p ∈ tau1Primes M := hKt₁ Fact.out hpK
        have hpKappa : p ∈ kappaPrimes M := by
          have hKpi := hK.isPiNumber_card
          rw [MathlibSupport.natCard_subgroupOf_eq hKM] at hKpi
          exact hKpi Fact.out hpK
        have hfixedX : centralizerWithin (sigmaCore M) X ≠ ⊥ :=
          kappa_nonregular hpKappa ⟨hX.1.trans hKM, hX.2⟩
        by_contra hCne
        let C : Subgroup G := centralizerWithin E₃ X
        let r : ℕ := Nat.minFac (Nat.card C)
        have hr : r.Prime :=
          Nat.minFac_prime (C.one_lt_card_iff_ne_bot.mpr hCne).ne'
        letI : Fact r.Prime := ⟨hr⟩
        have hrC : r ∣ Nat.card C := Nat.minFac_dvd (Nat.card C)
        obtain ⟨Z, hZC, hZ⟩ :=
          exists_rankOne_le_of_prime_dvd_structure hr hrC
        have hZE₃ : Z ≤ E₃ :=
          hZC.trans (centralizerWithin_le_left E₃ X)
        have hrTau₃ : r ∈ tau3Primes M := by
          have hrZ : r ∣ Nat.card Z := by
            rw [hZ.card_eq, pow_one]
          have hrE₃ : r ∣ Nat.card E₃ :=
            hrZ.trans (Subgroup.card_dvd_of_le hZE₃)
          have hpi := hHallE₃.isPiNumber_card
          rw [MathlibSupport.natCard_subgroupOf_eq hE₃E] at hpi
          exact hpi hr hrE₃
        have hZcentEX : Z ≤ centralizerWithin E X := by
          exact le_inf (hZE₃.trans hE₃E) (hZC.trans inf_le_right)
        have hCXZ : centralizerWithin (sigmaCore M) X ≤
            centralizerWithin (sigmaCore M) Z :=
          cent_tau1Elem_Msigma hmaxM hEM hHallE hpTau₁ hr
            ⟨hX.1.trans (hE₁eqK.ge.trans hE₁E), hX.2⟩
            ⟨hZcentEX, hZ⟩
        have hCZne : centralizerWithin (sigmaCore M) Z ≠ ⊥ := by
          intro hbot
          apply hfixedX
          apply le_antisymm
          · rw [hbot] at hCXZ
            exact hCXZ
          · exact bot_le
        have hrKappa : r ∈ kappaPrimes M :=
          ⟨Or.inr hrTau₃, Z,
            ⟨hZE₃.trans hE₃M, hZ⟩, hCZne⟩
        have hrM := kappa_pi hrKappa
        have hrK : r ∣ Nat.card K :=
          prime_dvd_card_of_mem_isHall_structure hKM hK hr
            hrKappa hrM.2
        exact (tau3'1 M (hKt₁ hr hrK)) hrTau₃

      have hlineE₂ : ∀ {p : ℕ} [Fact p.Prime] {X : Subgroup G},
          RankOneLineIn p K X →
            centralizerWithin E₂ X = ⊥ := by
        intro p _ X hX
        have hpK : p ∣ Nat.card K :=
          (by
            have hpX : p ∣ Nat.card X := by
              rw [hX.2.card_eq, pow_one]
            exact hpX.trans (Subgroup.card_dvd_of_le hX.1))
        have hpTau₁ : p ∈ tau1Primes M := hKt₁ Fact.out hpK
        have hpKappa : p ∈ kappaPrimes M := by
          have hKpi := hK.isPiNumber_card
          rw [MathlibSupport.natCard_subgroupOf_eq hKM] at hKpi
          exact hKpi Fact.out hpK
        have hfixedX : centralizerWithin (sigmaCore M) X ≠ ⊥ :=
          kappa_nonregular hpKappa ⟨hX.1.trans hKM, hX.2⟩
        by_contra hCne
        let C : Subgroup G := centralizerWithin E₂ X
        let r : ℕ := Nat.minFac (Nat.card C)
        have hr : r.Prime :=
          Nat.minFac_prime (C.one_lt_card_iff_ne_bot.mpr hCne).ne'
        letI : Fact r.Prime := ⟨hr⟩
        have hrC : r ∣ Nat.card C := Nat.minFac_dvd (Nat.card C)
        obtain ⟨Z, hZC, hZ⟩ :=
          exists_rankOne_le_of_prime_dvd_structure hr hrC
        have hZE₂ : Z ≤ E₂ :=
          hZC.trans (centralizerWithin_le_left E₂ X)
        have hrTau₂ : r ∈ tau2Primes M := by
          have hrZ : r ∣ Nat.card Z := by
            rw [hZ.card_eq, pow_one]
          have hrE₂ : r ∣ Nat.card E₂ :=
            hrZ.trans (Subgroup.card_dvd_of_le hZE₂)
          have hpi := hHallE₂.isPiNumber_card
          rw [MathlibSupport.natCard_subgroupOf_eq hE₂E] at hpi
          exact hpi hr hrE₂
        obtain ⟨A, hAE, _hAM, hA⟩ := ex_tau2Elem hEM hHallE hrTau₂
        have hTau := tau2_compl_context hmaxM hEM hHallE
          hrTau₂ hAE hA
        have hZA : Z ≤ A :=
          ((hTau.rankOne_iff Z).mp
            ⟨hZE₂.trans hE₂E, hZ⟩).1
        have hCAX : centralizerWithin A X ≠ ⊥ := by
          intro hbot
          have hZle : Z ≤ centralizerWithin A X :=
            le_inf hZA (hZC.trans inf_le_right)
          rw [hbot] at hZle
          exact hZ.ne_bot (le_bot_iff.mp hZle)
        exact hfixedX (tau12_regular hmaxM hEM hHallE hpTau₁
          ⟨hX.1.trans (hE₁eqK.ge.trans hE₁E), hX.2⟩
          hrTau₂ hAE hA hCAX)

      have hregE₃ : IsSemiregularConjugation E₃ K :=
        semiregular_of_rankOne_centralizers_structure hlineE₃
      have hregE₂ : IsSemiregularConjugation E₂ K :=
        semiregular_of_rankOne_centralizers_structure hlineE₂
      have hE₃E₂sd : IsInternalSemidirectProductIn E₃ E₂ U := by
        simpa only [U] using
          semidirectProduct_restrict_right_structure
            hComplCtx.E₃_E₂₁_sdprod le_sup_left
      have hKnormE₃ : K ≤ Subgroup.normalizer (E₃ : Set G) := by
        exact hKE.trans
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hE₃E).mp
            hComplCtx.E₃_normal)
      have hKnormE₂ : K ≤ Subgroup.normalizer (E₂ : Set G) := by
        have hE₂normal := hComplCtx.E₂₁_sdprod.2.2.1
        have hE₁normE₂ : E₁ ≤ Subgroup.normalizer (E₂ : Set G) :=
          le_sup_right.trans
            ((Subgroup.normal_subgroupOf_iff_le_normalizer
              hComplCtx.E₂₁_sdprod.1).mp hE₂normal)
        simpa only [← hE₁eqK] using hE₁normE₂
      have hReg : IsSemiregularConjugation U K :=
        semiregular_semidirectProduct_structure hE₃E₂sd
          hKnormE₃ hKnormE₂ hregE₃ hregE₂

      have hUcardPi : IsPiNumber (sigmaKappaPrimes M)ᶜ
          (Nat.card U) := by
        rw [← hE₃E₂sd.2.2.2.card_mul,
          MathlibSupport.natCard_subgroupOf_eq hE₃E₂sd.1,
          MathlibSupport.natCard_subgroupOf_eq hE₃E₂sd.2.1]
        apply IsPiNumber.mul
        · intro r hr hrE₃
          have hrTau₃ : r ∈ tau3Primes M := by
            have hpi := hHallE₃.isPiNumber_card
            rw [MathlibSupport.natCard_subgroupOf_eq hE₃E] at hpi
            exact hpi hr hrE₃
          intro hrSigmaKappa
          rcases hrSigmaKappa with hrSigma | hrKappa
          · exact hrTau₃.2.1 hrSigma
          · have hrK : r ∣ Nat.card K :=
              prime_dvd_card_of_mem_isHall_structure hKM hK hr
                hrKappa (kappa_pi hrKappa).2
            exact (tau3'1 M (hKt₁ hr hrK)) hrTau₃
        · intro r hr hrE₂
          have hrTau₂ : r ∈ tau2Primes M := by
            have hpi := hHallE₂.isPiNumber_card
            rw [MathlibSupport.natCard_subgroupOf_eq hE₂E] at hpi
            exact hpi hr hrE₂
          intro hrSigmaKappa
          rcases hrSigmaKappa with hrSigma | hrKappa
          · exact hrTau₂.2.1 hrSigma
          · rcases kappa_tau13 hrKappa with hrTau₁ | hrTau₃
            · exact (tau2'1 M hrTau₁) hrTau₂
            · exact (tau3'2 M hrTau₂) hrTau₃
      have hHallUE : IsHall (sigmaKappaPrimes M)ᶜ
          (U.subgroupOf E) := by
        constructor
        · simpa only [MathlibSupport.natCard_subgroupOf_eq hUE] using
            hUcardPi
        · change IsPiNumber (sigmaKappaPrimes M)ᶜᶜ (U.relIndex E)
          rw [← hUKE]
          change IsPiNumber (sigmaKappaPrimes M)ᶜᶜ
            ((U.subgroupOf (U ⊔ K)).index)
          rw [hUKsd.2.2.2.symm.index_eq_card,
            MathlibSupport.natCard_subgroupOf_eq
              (show K ≤ U ⊔ K from le_sup_right)]
          have hKpi := hK.isPiNumber_card
          rw [MathlibSupport.natCard_subgroupOf_eq hKM] at hKpi
          have hKsigmaKappa : IsPiNumber (sigmaKappaPrimes M)
              (Nat.card K) := by
            apply hKpi.mono
            intro p hp
            exact Or.inr hp
          simpa only [compl_compl] using hKsigmaKappa
      have hHallUM : IsHall (sigmaKappaPrimes M)ᶜ
          (U.subgroupOf M) :=
        isHall_tower_structure hUE hEM hHallUE hHallE
          (fun _ hp hpSigma ↦ hp (Or.inl hpSigma))
      have hKappaCompl : KappaComplement M U K := by
        refine
          { U_le_M := hUM
            hall_U := hHallUM
            K_le_M := hKM
            hall_K := hK
            product_is_group := ⟨U ⊔ K, ?_⟩ }
        exact Subgroup.coe_mul_of_right_le_normalizer_left U K
          (le_sup_right.trans
            ((Subgroup.normal_subgroupOf_iff_le_normalizer hUKsd.1).mp
              hUKsd.2.2.1))

      have hcopUK : (Nat.card U).Coprime (Nat.card K) := by
        apply Nat.coprime_of_dvd
        intro p hp hpU hpK
        have hpKappa : p ∈ kappaPrimes M := by
          have hKpi := hK.isPiNumber_card
          rw [MathlibSupport.natCard_subgroupOf_eq hKM] at hKpi
          exact hKpi hp hpK
        exact hUcardPi hp hpU (Or.inr hpKappa)
      have hKnormU : K ≤ Subgroup.normalizer (U : Set G) :=
        le_sup_right.trans
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hUKsd.1).mp
            hUKsd.2.2.1)
      have hcentUK : centralizerWithin U K = ⊥ :=
        centralizerWithin_eq_bot_of_semiregular_actor_structure hReg hKne
      have hUsol : IsSolvable U :=
        mFT_sol (lt_of_le_of_lt hUM (mmax_proper hmaxM))
      have hUcommLe : U ≤ ⁅K, U⁆ := by
        letI : IsSolvable U := hUsol
        have hdecomp :=
          le_commutator_sup_centralizerWithin_of_coprime hKnormU hcopUK
        simpa only [hcentUK, sup_bot_eq] using hdecomp
      let D : Subgroup G := (_root_.commutator E).map E.subtype
      have hUD : U ≤ D :=
        hUcommLe.trans
          ((Subgroup.commutator_mono hKE hUE).trans
            E.map_subtype_commutator.ge)
      have hDcomm : IsMulCommutative D := by
        letI : IsMulCommutative (_root_.commutator E) :=
          der_mmax_compl_abelian hmaxM hEM hHallE
        change IsMulCommutative
          ((_root_.commutator E).map E.subtype)
        infer_instance
      have hUcomm : IsMulCommutative U :=
        isMulCommutative_of_le_structure hUD hDcomm
      have hRankOneNorm : ∀ {p : ℕ} [Fact p.Prime]
          {X : Subgroup G}, RankOneLineIn p K X →
            (X.subgroupOf K).Normal := by
        intro p _ X hX
        letI : IsCyclic K := by
          exact hE₁eqK ▸ hComplCtx.E₁_cyclic
        letI : IsMulCommutative K := inferInstance
        apply Subgroup.normal_subgroupOf_of_le_normalizer
        intro k hk
        rw [Subgroup.mem_normalizer_iff]
        have hconj_of_mem {x : G} (hxK : x ∈ K) :
            k * x * k⁻¹ = x := by
          have hcomm : k * x = x * k :=
            congrArg Subtype.val
              (mul_comm (⟨k, hk⟩ : K) (⟨x, hxK⟩ : K))
          rw [hcomm]
          simp
        intro x
        constructor
        · intro hx
          rw [hconj_of_mem (hX.1 hx)]
          exact hx
        · intro hx
          have hxK : x ∈ K := by
            have hback := K.mul_mem
              (K.mul_mem (K.inv_mem hk) (hX.1 hx)) hk
            simpa [mul_assoc] using hback
          rw [hconj_of_mem hxK] at hx
          exact hx
      exact ⟨U, hKappaCompl, hUKsd, hSigmaUKsd, hUcomm,
        hPrime, hReg, hRankOneNorm, hE₁ne, hE₁eqK.le⟩
    · obtain ⟨p, hpK, hpNotTau₁⟩ :=
        exists_primeSupport_not_mem_of_not_isPiNumber hKt₁
      letI : Fact p.Prime := ⟨hpK.1⟩
      have hpKappa : p ∈ kappaPrimes M := by
        have hKpi := hK.isPiNumber_card
        rw [MathlibSupport.natCard_subgroupOf_eq hKM] at hKpi
        exact hKpi hpK.1 hpK.2
      have hpTau₃ : p ∈ tau3Primes M := by
        rcases kappa_tau13 hpKappa with hpTau₁ | hpTau₃
        · exact (hpNotTau₁ hpTau₁).elim
        · exact hpTau₃
      obtain ⟨X, hXK, hX⟩ :=
        exists_rankOne_le_of_prime_dvd_structure hpK.1 hpK.2
      have hXE : X ≤ E := hXK.trans hKE
      have hXE₃ : X ≤ E₃ := by
        let XE : Subgroup E := X.subgroupOf E
        let E₃E : Subgroup E := E₃.subgroupOf E
        have hXEpi : IsPiNumber (tau3Primes M) (Nat.card XE) := by
          rw [MathlibSupport.natCard_subgroupOf_eq hXE]
          exact hX.isPGroup.isPiNumber_natCard hpTau₃
        have hsub : XE ≤ E₃E :=
          isPiNumber_le_normal_isHall_structure
            (by simpa only [E₃E] using hComplCtx.E₃_normal)
            (by simpa only [E₃E] using hHallE₃) hXEpi
        intro x hx
        exact hsub (show (⟨x, hXE hx⟩ : E) ∈ XE from hx)
      have hfixedX : centralizerWithin (sigmaCore M) X ≠ ⊥ :=
        kappa_nonregular hpKappa ⟨hXK.trans hKM, hX⟩
      have hnotRegE₃ :
          ¬ IsSemiregularConjugation (sigmaCore M) E₃ := by
        intro hreg
        have hregX : IsSemiregularConjugation (sigmaCore M) X := by
          intro x hx a hfix
          let xE₃ : E₃ := ⟨x, hXE₃ x.property⟩
          have hxE₃ : xE₃ ≠ 1 := by
            intro hx1
            apply hx
            exact Subtype.ext
              (congrArg (fun z : E₃ => (z : G)) hx1)
          exact hreg xE₃ hxE₃ a hfix
        exact hfixedX
          (centralizerWithin_eq_bot_of_semiregular_actor_structure
            hregX hX.ne_bot)
      have hNonreg := tau13_nonregular hmaxM hCompl hnotRegE₃

      have hEpi : IsPiNumber (kappaPrimes M) (Nat.card E) := by
        intro q hq hqE
        letI : Fact q.Prime := ⟨hq⟩
        obtain ⟨Y, hYE, hY⟩ :=
          exists_rankOne_le_of_prime_dvd_structure hq hqE
        have hqTau₁₃ : q ∈ tau13Primes M := by
          have hcardE : Nat.card E = Nat.card E₃ * Nat.card E₁ := by
            calc
              Nat.card E =
                  Nat.card (E₃.subgroupOf E) *
                    Nat.card (E₁.subgroupOf E) :=
                hNonreg.E₃_E₁_sdprod.2.2.2.card_mul.symm
              _ = Nat.card E₃ * Nat.card E₁ := by
                rw [MathlibSupport.natCard_subgroupOf_eq
                    hNonreg.E₃_E₁_sdprod.1,
                  MathlibSupport.natCard_subgroupOf_eq
                    hNonreg.E₃_E₁_sdprod.2.1]
          rw [hcardE] at hqE
          rcases hq.dvd_mul.mp hqE with hqE₃ | hqE₁
          · right
            have hpi := hHallE₃.isPiNumber_card
            rw [MathlibSupport.natCard_subgroupOf_eq hE₃E] at hpi
            exact hpi hq hqE₃
          · left
            have hpi := hHallE₁.isPiNumber_card
            rw [MathlibSupport.natCard_subgroupOf_eq hE₁E] at hpi
            exact hpi hq hqE₁
        have hCXE := hNonreg.sigma_prime_action.centralizer_eq
          hXE hX.ne_bot
        have hCYE := hNonreg.sigma_prime_action.centralizer_eq
          hYE hY.ne_bot
        have hCYne : centralizerWithin (sigmaCore M) Y ≠ ⊥ := by
          rw [hCYE, ← hCXE]
          exact hfixedX
        exact ⟨hqTau₁₃, Y, ⟨hYE.trans hEM, hY⟩, hCYne⟩
      have hEK : E = K :=
        intermediate_eq_isHall_of_isPiNumber_structure
          hKE hEM hK hEpi
      have hE₁K : E₁ ≤ K := hE₁E.trans hEK.le

      let U : Subgroup G := ⊥
      have hUKsd : IsInternalSemidirectProductIn U K (U ⊔ K) := by
        have hnormal : ((⊥ : Subgroup G).subgroupOf K).Normal := by
          simpa using (Subgroup.normal_bot : (⊥ : Subgroup K).Normal)
        have hcomp : ((⊥ : Subgroup G).subgroupOf K).IsComplement'
            (K.subgroupOf K) := by
          simpa using (Subgroup.isComplement'_bot_left.mpr rfl :
            (⊥ : Subgroup K).IsComplement' ⊤)
        simpa only [U, bot_sup_eq] using
          (show IsInternalSemidirectProductIn (⊥ : Subgroup G) K K from
            ⟨bot_le, le_rfl, hnormal, hcomp⟩)
      have hSigmaUKsd :
          IsInternalSemidirectProductIn (sigmaCore M) (U ⊔ K) M := by
        simpa only [U, bot_sup_eq, ← hEK] using
          sdprod_sigma hmaxM hEM hHallE
      have hHallBotE : IsHall (sigmaKappaPrimes M)ᶜ
          ((⊥ : Subgroup G).subgroupOf E) := by
        constructor
        · simpa using
            (IsPiNumber.one (pi := (sigmaKappaPrimes M)ᶜ))
        · have hbot : (⊥ : Subgroup G).subgroupOf E =
              (⊥ : Subgroup E) := by
            ext z
            simp
          rw [hbot, Subgroup.index_bot]
          have hESigmaKappa : IsPiNumber (sigmaKappaPrimes M)
              (Nat.card E) := by
            apply hEpi.mono
            intro p hp
            exact Or.inr hp
          simpa only [compl_compl] using hESigmaKappa
      have hHallBotM : IsHall (sigmaKappaPrimes M)ᶜ
          ((⊥ : Subgroup G).subgroupOf M) :=
        isHall_tower_structure bot_le hEM hHallBotE hHallE
          (fun _ hp hpSigma ↦ hp (Or.inl hpSigma))
      have hKappaCompl : KappaComplement M U K :=
        { U_le_M := bot_le
          hall_U := by simpa only [U] using hHallBotM
          K_le_M := hKM
          hall_K := hK
          product_is_group := ⟨K, by simp [U]⟩ }
      have hPrime : IsPrimeAction (sigmaCore M) K := by
        simpa only [← hEK] using hNonreg.sigma_prime_action
      have hReg : IsSemiregularConjugation U K := by
        intro k hk u _
        exact Subsingleton.elim u 1
      have hUcomm : IsMulCommutative U := by
        simpa only [U] using (inferInstance : IsMulCommutative (⊥ : Subgroup G))
      have hRankOneNorm : ∀ {q : ℕ} [Fact q.Prime]
          {Y : Subgroup G}, RankOneLineIn q K Y →
            (Y.subgroupOf K).Normal := by
        intro q _ Y hY
        have hlineE : RankOneLineIn q E Y := by
          simpa only [hEK] using hY
        apply Subgroup.normal_subgroupOf_of_le_normalizer
        exact hEK.ge.trans
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hlineE.1).mp
            (hNonreg.rankOne_normal hlineE))
      exact ⟨U, hKappaCompl, hUKsd, hSigmaUKsd, hUcomm,
        hPrime, hReg, hRankOneNorm, hNonreg.E₁_ne_bot, hE₁K⟩

  /- Reassociate the decomposition as `(M_sigma ⋊ U) ⋊ K`.  All
  normalizer calculations below take place in this common product. -/
  let S : Subgroup G := sigmaCore M
  let A : Subgroup G := S ⊔ U
  have hSU : IsInternalSemidirectProductIn S U A := by
    simpa only [S, A] using
      semidirectProduct_restrict_right_structure hSigmaUKsd le_sup_left
  have hAKsd : IsInternalSemidirectProductIn A K M := by
    simpa only [S, A] using
      semidirectProduct_reassociate_structure hSigmaUKsd hUKsd
  have hMnormS : M ≤ Subgroup.normalizer (S : Set G) := by
    simpa only [S] using
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (sigmaCore_le M)).mp (sigmaCore_normal M)
  have hKnormS : K ≤ Subgroup.normalizer (S : Set G) :=
    hKM.trans hMnormS
  have hKnormU : K ≤ Subgroup.normalizer (U : Set G) := by
    exact le_sup_right.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hUKsd.1).mp
        hUKsd.2.2.1)

  have hScardPi : IsPiNumber (sigmaPrimes M) (Nat.card S) := by
    simpa only [S] using sigmaCore_isPiNumber M
  have hUcardPi : IsPiNumber (sigmaKappaPrimes M)ᶜ
      (Nat.card U) := by
    have hpi := hKappaCompl.hall_U.isPiNumber_card
    simpa only [MathlibSupport.natCard_subgroupOf_eq hKappaCompl.U_le_M] using hpi
  have hKcardPi : IsPiNumber (kappaPrimes M) (Nat.card K) := by
    have hpi := hK.isPiNumber_card
    simpa only [MathlibSupport.natCard_subgroupOf_eq hKM] using hpi
  have hcopSK : (Nat.card S).Coprime (Nat.card K) := by
    apply Nat.coprime_of_dvd
    intro p hp hpS hpK
    exact (kappa_sigma' M (hKcardPi hp hpK)) (hScardPi hp hpS)
  have hcopUK : (Nat.card U).Coprime (Nat.card K) := by
    apply Nat.coprime_of_dvd
    intro p hp hpU hpK
    exact hUcardPi hp hpU (Or.inr (hKcardPi hp hpK))
  have hcardA : Nat.card A = Nat.card S * Nat.card U := by
    calc
      Nat.card A =
          Nat.card (S.subgroupOf A) * Nat.card (U.subgroupOf A) :=
        hSU.2.2.2.card_mul.symm
      _ = Nat.card S * Nat.card U := by
        rw [MathlibSupport.natCard_subgroupOf_eq hSU.1,
          MathlibSupport.natCard_subgroupOf_eq hSU.2.1]
  have hcopAK : (Nat.card A).Coprime (Nat.card K) := by
    rw [hcardA]
    exact hcopSK.mul_left hcopUK

  have hNormalizer {X : Subgroup G}
      (hXK : X ≤ K) (hXne : X ≠ ⊥)
      (hXnormal : (X.subgroupOf K).Normal) :
      normalizerWithin M X = pTypeCentralizer M K ⊔ K := by
    calc
      normalizerWithin M X = centralizerWithin A X ⊔ K :=
        normalizerWithin_eq_centralizer_sup_structure
          hAKsd hcopAK (mmax_sol hmaxM) hXK hXnormal
      _ = pTypeCentralizer M K ⊔ K := by
        rw [centralizer_reassociated_eq_structure hSU hXK hXne
          hKnormS hKnormU hPrime hReg]
  have hKKnormal : (K.subgroupOf K).Normal := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  have hNKEq : normalizerWithin M K =
      pTypeCentralizer M K ⊔ K :=
    hNormalizer le_rfl hKne hKKnormal
  have hCentEq : pTypeCentralizer M K = centralizerWithin A K := by
    symm
    simpa only [S] using
      (centralizer_reassociated_eq_structure hSU le_rfl hKne
        hKnormS hKnormU hPrime hReg)
  have hNormDirect :
      IsInternalDirectProductIn K (pTypeCentralizer M K)
        (normalizerWithin M K) :=
    directProduct_complement_centralizer_structure hAKsd hCentEq hNKEq

  have hRankOneNormalizer :
      ∀ {p : ℕ} [Fact p.Prime] {X : Subgroup G},
        RankOneLineIn p K X →
        normalizerWithin M X = normalizerWithin M K ∧
          ∀ {Mstar : Subgroup G},
            Mstar ∈ minSimple_max_groups_of (G := G)
              (Subgroup.normalizer (X : Set G) : Set G) →
            X ≤ sigmaCore Mstar := by
    intro p _ X hX
    have hXnormal : (X.subgroupOf K).Normal := hRankOneNorm hX
    have hNX := hNormalizer hX.1 hX.2.ne_bot hXnormal
    refine ⟨hNX.trans hNKEq.symm, ?_⟩
    intro Mstar hMstar
    have hpX : p ∣ Nat.card X := by
      rw [hX.2.card_eq, pow_one]
    have hpK : p ∣ Nat.card K :=
      hpX.trans (Subgroup.card_dvd_of_le hX.1)
    have hpKappa : p ∈ kappaPrimes M := hKcardPi Fact.out hpK
    have hXE : X ≤ E := hX.1.trans hKE
    have hfixed : centralizerWithin (sigmaCore M) X ≠ ⊥ :=
      kappa_nonregular hpKappa ⟨hXE.trans hEM, hX.2⟩
    have hpSigma : p ∈ sigmaPrimes Mstar :=
      tau13_nonregular_sigma hmaxM hEM hHallE ⟨hXE, hX.2⟩
        (kappa_tau13 hpKappa) hfixed hMstar
    have hXMstar : X ≤ Mstar :=
      Subgroup.le_normalizer.trans hMstar.2
    let XS : Subgroup Mstar := X.subgroupOf Mstar
    let SS : Subgroup Mstar := (sigmaCore Mstar).subgroupOf Mstar
    have hXpi : IsPiNumber (sigmaPrimes Mstar) (Nat.card XS) := by
      rw [MathlibSupport.natCard_subgroupOf_eq hXMstar]
      exact hX.2.isPGroup.isPiNumber_natCard hpSigma
    have hXSle : XS ≤ SS :=
      isPiNumber_le_normal_isHall_structure
        (by simpa only [SS] using sigmaCore_normal Mstar)
        (by simpa only [SS] using Msigma_Hall hMstar.1) hXpi
    intro x hx
    exact hXSle (show (⟨x, hXMstar hx⟩ : Mstar) ∈ XS from hx)

  /- Fix the tau-one line used throughout parts (c), (e), and (g). -/
  let r : ℕ := Nat.minFac (Nat.card E₁)
  have hr : r.Prime :=
    Nat.minFac_prime (E₁.one_lt_card_iff_ne_bot.mpr hE₁ne).ne'
  letI : Fact r.Prime := ⟨hr⟩
  have hrE₁ : r ∣ Nat.card E₁ := Nat.minFac_dvd (Nat.card E₁)
  obtain ⟨Y₁, hY₁E₁, hY₁⟩ :=
    exists_rankOne_le_of_prime_dvd_structure hr hrE₁
  have hY₁K : Y₁ ≤ K := hY₁E₁.trans hE₁K
  have hrK : r ∣ Nat.card K :=
    hrE₁.trans (Subgroup.card_dvd_of_le hE₁K)
  have hrKappa : r ∈ kappaPrimes M := hKcardPi hr hrK
  have hY₁fixed : centralizerWithin (sigmaCore M) Y₁ ≠ ⊥ :=
    kappa_nonregular hrKappa
      ⟨hY₁K.trans hKM, hY₁⟩
  have hY₁centEq : centralizerWithin (sigmaCore M) Y₁ =
      pTypeCentralizer M K := by
    exact hPrime.centralizer_eq hY₁K hY₁.ne_bot
  have hKstarNe : pTypeCentralizer M K ≠ ⊥ := by
    rw [← hY₁centEq]
    exact hY₁fixed
  have hKstarUniq :
      ∀ {p : ℕ} [Fact p.Prime] {X : Subgroup G},
        RankOneLineIn p (pTypeCentralizer M K) X →
        minSimple_max_groups_of (G := G)
          (Subgroup.centralizer (X : Set G) : Set G) = {M} := by
    intro p _ X hX
    have hXcent : X ≤ centralizerWithin (sigmaCore M) Y₁ := by
      rw [hY₁centEq]
      exact hX.1
    exact (cent_cent_Msigma_tau1_uniq hmaxM hEM hHallE
      hE₁E hHallE₁ hY₁E₁ hY₁.ne_bot hXcent hX.2).1

  have hKstarTI :
      ∀ g : G, g ∉ M →
        pTypeCentralizer M K ⊓
            M.map (MulAut.conj g).toMonoidHom = ⊥ := by
    intro g hgM
    by_contra hInfNe
    let J : Subgroup G := pTypeCentralizer M K ⊓
      M.map (MulAut.conj g).toMonoidHom
    have hJne : J ≠ ⊥ := by simpa only [J] using hInfNe
    let p : ℕ := Nat.minFac (Nat.card J)
    have hp : p.Prime :=
      Nat.minFac_prime (J.one_lt_card_iff_ne_bot.mpr hJne).ne'
    letI : Fact p.Prime := ⟨hp⟩
    have hpJ : p ∣ Nat.card J := Nat.minFac_dvd (Nat.card J)
    obtain ⟨X, hXJ, hX⟩ :=
      exists_rankOne_le_of_prime_dvd_structure hp hpJ
    have hXKstar : X ≤ pTypeCentralizer M K :=
      hXJ.trans inf_le_left
    have hXMg : X ≤ M.map (MulAut.conj g).toMonoidHom :=
      hXJ.trans inf_le_right
    have hXS : X ≤ sigmaCore M :=
      hXKstar.trans (centralizerWithin_le_left (sigmaCore M) K)
    have hpX : p ∣ Nat.card X := by
      rw [hX.card_eq, pow_one]
    have hpS : p ∣ Nat.card (sigmaCore M) :=
      hpX.trans (Subgroup.card_dvd_of_le hXS)
    have hpSigma : p ∈ sigmaPrimes M :=
      sigmaCore_isPiNumber M hp hpS
    have huniq := hKstarUniq ⟨hXKstar, hX⟩
    have hCentXM : Subgroup.centralizer (X : Set G) ≤ M :=
      (mem_uniq_mmax huniq).2
    have hXM : X ≤ M := hXS.trans (sigmaCore_le M)
    have hXback : X.map (MulAut.conj g⁻¹).toMonoidHom ≤ M :=
      map_conj_inv_le_of_le_map_conj_structure hXMg
    obtain ⟨c, hc, m, hm, hg⟩ :=
      (sigma_group_trans hmaxM hpSigma hX.isPGroup).1
        g hXM hXback
    apply hgM
    rw [hg]
    exact M.mul_mem (hCentXM hc) hm

  have hKTI :
      ∀ g : G, g ∈ M →
        g ∉ Subgroup.normalizer (K : Set G) →
        K ⊓ K.map (MulAut.conj g).toMonoidHom = ⊥ := by
    intro g hgM hgNormK
    by_contra hInfNe
    let J : Subgroup G := K ⊓ K.map (MulAut.conj g).toMonoidHom
    have hJne : J ≠ ⊥ := by simpa only [J] using hInfNe
    let p : ℕ := Nat.minFac (Nat.card J)
    have hp : p.Prime :=
      Nat.minFac_prime (J.one_lt_card_iff_ne_bot.mpr hJne).ne'
    letI : Fact p.Prime := ⟨hp⟩
    have hpJ : p ∣ Nat.card J := Nat.minFac_dvd (Nat.card J)
    obtain ⟨X, hXJ, hX⟩ :=
      exists_rankOne_le_of_prime_dvd_structure hp hpJ
    have hXK : X ≤ K := hXJ.trans inf_le_left
    have hXKg : X ≤ K.map (MulAut.conj g).toMonoidHom :=
      hXJ.trans inf_le_right
    have hXline : RankOneLineIn p K X := ⟨hXK, hX⟩
    let Y : Subgroup G := X.map (MulAut.conj g⁻¹).toMonoidHom
    have hYK : Y ≤ K := by
      simpa only [Y] using
        map_conj_inv_le_of_le_map_conj_structure hXKg
    have hYrank : IsElementaryAbelianOfRank p 1 Y := by
      dsimp only [Y]
      exact hX.map_of_injective (MulAut.conj g⁻¹).toMonoidHom
        (MulAut.conj g⁻¹).injective
    have hYline : RankOneLineIn p K Y := ⟨hYK, hYrank⟩
    have hpX : p ∣ Nat.card X := by
      rw [hX.card_eq, pow_one]
    have hpKcard : p ∣ Nat.card K :=
      hpX.trans (Subgroup.card_dvd_of_le hXK)
    have hpKappa : p ∈ kappaPrimes M := hKcardPi hp hpKcard
    have hNoRankK : ¬ HasElementaryAbelianRankAtLeast p 2 K := by
      intro hRankK
      apply (rank_kappa hpKappa).2
      rcases hRankK with ⟨L, hLK, hL⟩
      exact ⟨L, hLK.trans hKM, hL⟩
    have hXY : X = Y :=
      rankOne_eq_of_no_rankTwo_of_normal_structure
        hNoRankK hXline hYline
          (hRankOneNorm hXline) (hRankOneNorm hYline)
    have hginvNormX : g⁻¹ ∈
        Subgroup.normalizer (X : Set G) := by
      apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      change X.map (MulAut.conj g⁻¹).toMonoidHom = X
      exact hXY.symm
    have hgNormX : g ∈ Subgroup.normalizer (X : Set G) := by
      have := (Subgroup.normalizer (X : Set G)).inv_mem hginvNormX
      simpa only [inv_inv] using this
    have hgNX : g ∈ normalizerWithin M X := ⟨hgM, hgNormX⟩
    have hNXNK := (hRankOneNormalizer hXline).1
    have hgNK : g ∈ normalizerWithin M K := by
      rw [← hNXNK]
      exact hgNX
    exact hgNormK hgNK.2

  have hrTau₁ : r ∈ tau1Primes M := by
    have hpi := hHallE₁.isPiNumber_card
    rw [MathlibSupport.natCard_subgroupOf_eq hE₁E] at hpi
    exact hpi hr hrE₁
  have hSylowUniq :
      ∀ {p : ℕ} [Fact p.Prime],
        p ∈ primeSupport (Nat.card (pTypeCentralizer M K)) →
        ∀ P : Sylow p M,
          minSimple_max_groups_of (G := G)
              ((ambientSylow M P : Subgroup G) : Set G) = {M} ∧
            ¬ (ambientSylow M P : Subgroup G) ≤
              pTypeCentralizer M K := by
    intro p _ hpKstar P
    obtain ⟨X, hXKstar, hX⟩ :=
      exists_rankOne_le_of_prime_dvd_structure
        (Fact.out : p.Prime) hpKstar.2
    have hpSigma : p ∈ sigmaPrimes M := by
      apply sigmaCore_isPiNumber M (Fact.out : p.Prime)
      exact hpKstar.2.trans
        (Subgroup.card_dvd_of_le
          (centralizerWithin_le_left (sigmaCore M) K))
    have hXcent : X ≤ centralizerWithin (sigmaCore M) Y₁ := by
      rw [hY₁centEq]
      exact hXKstar
    have hCent := cent_cent_Msigma_tau1_uniq hmaxM hEM hHallE
      hE₁E hHallE₁ hY₁E₁ hY₁.ne_bot hXcent hX
    let Cσ : Subgroup M := (sigmaCore M).subgroupOf M
    have hPpi : IsPiNumber (sigmaPrimes M)
        (Nat.card (P : Subgroup M)) :=
      P.isPGroup'.isPiNumber_natCard hpSigma
    have hPleCσ : (P : Subgroup M) ≤ Cσ :=
      isPiNumber_le_normal_isHall_structure
        (by simpa only [Cσ] using sigmaCore_normal M)
        (by simpa only [Cσ] using Msigma_Hall hmaxM) hPpi
    let Pσ : Sylow p Cσ := P.subtype hPleCσ
    have hPσambient :
        (((Pσ : Subgroup Cσ).map Cσ.subtype).map M.subtype :
            Subgroup G) = ambientSylow M P := by
      change (((P.subtype hPleCσ : Sylow p Cσ) : Subgroup Cσ).map
          Cσ.subtype).map M.subtype =
        (P : Subgroup M).map M.subtype
      rw [P.coe_subtype,
        Subgroup.map_subgroupOf_eq_of_le hPleCσ]
    have huniqP :
        minSimple_max_groups_of (G := G)
            ((ambientSylow M P : Subgroup G) : Set G) = {M} := by
      rw [← hPσambient]
      exact hCent.2 Pσ
    refine ⟨huniqP, ?_⟩
    intro hPleKstar
    let Ysub : Subgroup E₁ := Y₁.subgroupOf E₁
    have hYsubp : IsPGroup r Ysub := hY₁.isPGroup.comap_subtype
    obtain ⟨P₁, hY₁P₁⟩ := hYsubp.exists_le_sylow
    obtain ⟨PE, hPE⟩ :=
      exists_sylow_of_hall_with_same_ambient_structure
        hr hE₁E hHallE₁ hrTau₁ P₁
    obtain ⟨PM, hPM⟩ :=
      exists_sylow_of_hall_with_same_ambient_structure
        hr hEM hHallE hrTau₁.2.1 PE
    let R : Subgroup G := ambientSylow M PM
    have hReq : R = ambientSylow E₁ P₁ := hPM.trans hPE
    have hRE₁ : R ≤ E₁ := by
      rw [hReq]
      exact Subgroup.map_subtype_le _
    have hY₁R : Y₁ ≤ R := by
      rw [hReq]
      intro y hy
      let yE₁ : E₁ := ⟨y, hY₁E₁ hy⟩
      exact ⟨yE₁, hY₁P₁
        (show yE₁ ∈ Ysub from hy), rfl⟩
    have hRne : R ≠ ⊥ := by
      intro hRbot
      apply hY₁.ne_bot
      apply le_antisymm
      · rw [← hRbot]
        exact hY₁R
      · exact bot_le
    have hRp : IsPGroup r R := by
      change IsPGroup r ((PM : Subgroup M).map M.subtype)
      exact PM.isPGroup'.map M.subtype
    have hPNormR : ambientSylow M P ≤
        Subgroup.normalizer (R : Set G) := by
      intro s hs
      apply Subgroup.centralizer_le_normalizer (R : Set G)
      apply Subgroup.centralizer_le hRE₁
      apply Subgroup.centralizer_le hE₁K
      exact (hPleKstar hs).2
    have hNormRproper : Subgroup.normalizer (R : Set G) < ⊤ :=
      mFT_norm_proper R hRne (mFT_pgroup_proper R hRp)
    have hNormRM : Subgroup.normalizer (R : Set G) ≤ M :=
      sub_uniq_mmax huniqP hPNormR hNormRproper
    have hrSigma : r ∈ sigmaPrimes M :=
      ⟨hr, PM, by simpa only [R] using hNormRM⟩
    exact hrTau₁.2.1 hrSigma

  have hSigmaInter :
      ∀ {Y : Subgroup G},
        IsPiNumber (sigmaPrimes M) (Nat.card Y) →
        Y ⊓ pTypeCentralizer M K ≠ ⊥ →
        Y ≤ sigmaCore M := by
    intro Y hYsigma hYinf
    have hYne : Y ≠ ⊥ := by
      intro hYbot
      subst Y
      simp at hYinf
    obtain ⟨x, hx⟩ := (sigma_Jsub hmaxM hYsigma hYne).1
    by_cases hxinvM : x⁻¹ ∈ M
    · intro y hy
      have hxyS : x * y * x⁻¹ ∈ sigmaCore M :=
        hx (Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom hy)
      have hnorm := hMnormS hxinvM
      have hback :=
        (Subgroup.mem_normalizer_iff.mp hnorm (x * y * x⁻¹)).mp hxyS
      simpa [mul_assoc] using hback
    · have hYMx : Y ≤ M.map (MulAut.conj x⁻¹).toMonoidHom := by
        intro y hy
        let z : G := x * y * x⁻¹
        have hzS : z ∈ sigmaCore M :=
          hx (Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom hy)
        refine ⟨z, (sigmaCore_le M) hzS, ?_⟩
        simp [z, MulAut.conj_apply, mul_assoc]
      have hle : Y ⊓ pTypeCentralizer M K ≤
          pTypeCentralizer M K ⊓
            M.map (MulAut.conj x⁻¹).toMonoidHom := by
        intro y hy
        exact ⟨hy.2, hYMx hy.1⟩
      have hbot : Y ⊓ pTypeCentralizer M K = ⊥ := by
        apply le_antisymm
        · rw [hKstarTI x⁻¹ hxinvM] at hle
          exact hle
        · exact bot_le
      exact (hYinf hbot).elim

  have hP2 : M ∈ typeP2MaximalSubgroups (G := G) →
      PTypeTwoStructure M K := by
    intro hMP2
    have hSM : S ≤ M := by simpa only [S] using sigmaCore_le M
    have hUKM : U ⊔ K ≤ M := hSigmaUKsd.2.1
    have hHallUK : IsHall (sigmaPrimes M)ᶜ
        ((U ⊔ K).subgroupOf M) :=
      kappaComplement_sup_hall_structure hKappaCompl
    have hSnorm : (S.subgroupOf M).Normal := by
      simpa only [S] using sigmaCore_normal M
    have hUKnormS : U ⊔ K ≤ Subgroup.normalizer (S : Set G) :=
      hUKM.trans hMnormS
    have hSsol : IsSolvable S :=
      mFT_sol (lt_of_le_of_lt hSM (mmax_proper hmaxM))
    have hSnonbot : S ≠ ⊥ := by
      simpa only [S] using Msigma_neq1 hmaxM
    have hUne : U ≠ ⊥ := by
      intro hUbot
      exact hMP2.2 ((trivg_kappa_compl hmaxM hKappaCompl).mp hUbot)

    have hUcardNe : Nat.card U ≠ 1 :=
      fun hc ↦ hUne (Subgroup.card_eq_one.mp hc)
    obtain ⟨p, hp, hpU⟩ := Nat.exists_prime_and_dvd hUcardNe
    letI : Fact p.Prime := ⟨hp⟩
    have hpUSub : p ∣ Nat.card (U.subgroupOf M) := by
      simpa only [MathlibSupport.natCard_subgroupOf_eq hKappaCompl.U_le_M] using hpU
    have hpOutside : p ∈ (sigmaKappaPrimes M)ᶜ :=
      hKappaCompl.hall_U.isPiNumber_card hp hpUSub
    have hpNotSigma : p ∉ sigmaPrimes M :=
      fun h ↦ hpOutside (Or.inl h)
    have hpNotKappa : p ∉ kappaPrimes M :=
      fun h ↦ hpOutside (Or.inr h)
    have hpMcard : p ∣ Nat.card M :=
      hpU.trans (Subgroup.card_dvd_of_le hKappaCompl.U_le_M)
    let PU : Sylow p U := Classical.choice Sylow.nonempty
    obtain ⟨PM, hPM⟩ :=
      exists_sylow_of_hall_with_same_ambient_structure
        hp hKappaCompl.U_le_M hKappaCompl.hall_U hpOutside PU
    have hOmegaPM : sylowOmegaOne M PM ≤ ambientSylow M PM := by
      simpa only [sylowOmegaOne] using
        (Subgroup.map_subtype_le (omegaOne p (ambientSylow M PM)))
    have hPMU : ambientSylow M PM ≤ U := by
      rw [hPM]
      simpa only [ambientSylow] using
        (Subgroup.map_subtype_le (PU : Subgroup U))
    have hOmegaU : sylowOmegaOne M PM ≤ U :=
      hOmegaPM.trans hPMU
    have hFacts := sigma'_kappa'_facts PM hmaxM
      ⟨hp, hpMcard⟩ hpNotSigma hpNotKappa
    have hCentSU : centralizerWithin S U = ⊥ := by
      apply le_antisymm _ bot_le
      intro x hx
      have hxOmega : x ∈ centralizerWithin S (sylowOmegaOne M PM) :=
        ⟨hx.1, Subgroup.centralizer_le hOmegaU hx.2⟩
      have hFactCent :
          centralizerWithin S (sylowOmegaOne M PM) = ⊥ := by
        simpa only [S] using hFacts.sigma_centralizer
      rw [hFactCent] at hxOmega
      exact hxOmega
    have hNilS : Group.IsNilpotent S := by
      simpa only [S] using hFacts.sigma_nilpotent

    have hCentUK : centralizerWithin U K = ⊥ :=
      centralizerWithin_eq_bot_of_semiregular_actor_structure
        hReg hKne
    have hUsol : IsSolvable U :=
      mFT_sol (lt_of_le_of_lt hKappaCompl.U_le_M
        (mmax_proper hmaxM))
    have hUder : U ≤ ⁅K, U⁆ := by
      letI : IsSolvable U := hUsol
      have hdecomp :=
        le_commutator_sup_centralizerWithin_of_coprime
          hKnormU hcopUK
      simpa only [hCentUK, sup_bot_eq] using hdecomp
    let D : Subgroup G :=
      (_root_.commutator (U ⊔ K : Subgroup G)).map
        (U ⊔ K : Subgroup G).subtype
    have hUD : U ≤ D :=
      hUder.trans
        ((Subgroup.commutator_mono
            (show K ≤ U ⊔ K from le_sup_right)
            (show U ≤ U ⊔ K from le_sup_left)).trans
          (U ⊔ K : Subgroup G).map_subtype_commutator.ge)
    obtain ⟨H, hHS, hHHall, hDcentH⟩ :=
      der_compl_cent_beta' hmaxM hUKM hHallUK
    have hHcentD : H ≤ Subgroup.centralizer (D : Set G) := by
      apply Subgroup.le_centralizer_iff.mp
      simpa only [D] using hDcentH
    have hHcentU : H ≤ Subgroup.centralizer (U : Set G) :=
      hHcentD.trans (Subgroup.centralizer_le hUD)
    have hHbot : H = ⊥ := by
      apply le_antisymm _ bot_le
      intro x hx
      have hxCU : x ∈ centralizerWithin S U :=
        ⟨hHS hx, hHcentU hx⟩
      rw [hCentSU] at hxCU
      exact hxCU
    have hSbeta : IsPiNumber (betaPrimes M) (Nat.card S) := by
      have hindex := hHHall.isPiNumber_index
      simpa only [hHbot, Subgroup.bot_subgroupOf,
        Subgroup.index_bot, compl_compl] using hindex
    have hSigmaBeta : sigmaPrimes M = betaPrimes M := by
      apply Set.Subset.antisymm
      · intro q hqSigma
        have hqS : q ∈ primeSupport (Nat.card S) := by
          change q ∈ primeSupport (Nat.card (sigmaCore M))
          rw [pi_Msigma hmaxM]
          exact hqSigma
        exact hSbeta hqS.1 hqS.2
      · exact beta_sub_sigma hmaxM

    have hFrobUK :=
      frobenius_of_semidirect_semiregular_structure
        hUKsd hUne hKne hReg
    have hcopSUK :
        (Nat.card S).Coprime (Nat.card (U ⊔ K : Subgroup G)) := by
      simpa only [S] using coprime_sigma_compl hUKM hHallUK
    have hFixK : Nat.card S =
        Nat.card (centralizerWithin S K) ^ Nat.card K :=
      (Frobenius_Wielandt_fixpoint hFrobUK hUKnormS
        hcopSUK hSsol).2.2 hCentSU

    have hKcardNe : Nat.card K ≠ 1 :=
      fun hc ↦ hKne (Subgroup.card_eq_one.mp hc)
    obtain ⟨q, hq, hqK⟩ := Nat.exists_prime_and_dvd hKcardNe
    letI : Fact q.Prime := ⟨hq⟩
    obtain ⟨Q, hQK, hQ⟩ :=
      exists_rankOne_le_of_prime_dvd_structure hq hqK
    have hQcard : Nat.card Q = q := by
      simpa only [pow_one] using hQ.card_eq
    have hUQsd :=
      semidirectProduct_restrict_right_structure hUKsd hQK
    have hRegQ : IsSemiregularConjugation U Q := by
      intro x hx u hfix
      let xK : K := ⟨(x : G), hQK x.property⟩
      have hxK : xK ≠ 1 := by
        intro hx1
        apply hx
        apply Subtype.ext
        exact congrArg (fun k : K => (k : G)) hx1
      exact hReg xK hxK u hfix
    have hFrobUQ :=
      frobenius_of_semidirect_semiregular_structure
        hUQsd hUne hQ.ne_bot hRegQ
    have hUQleUK : U ⊔ Q ≤ U ⊔ K :=
      sup_le le_sup_left (hQK.trans le_sup_right)
    have hUQnormS : U ⊔ Q ≤ Subgroup.normalizer (S : Set G) :=
      hUQleUK.trans hUKnormS
    have hcopSUQ :
        (Nat.card S).Coprime (Nat.card (U ⊔ Q : Subgroup G)) :=
      hcopSUK.coprime_dvd_right (Subgroup.card_dvd_of_le hUQleUK)
    have hFixQ₀ : Nat.card S =
        Nat.card (centralizerWithin S Q) ^ Nat.card Q :=
      (Frobenius_Wielandt_fixpoint hFrobUQ hUQnormS
        hcopSUQ hSsol).2.2 hCentSU
    have hFixQ : Nat.card S =
        Nat.card (centralizerWithin S K) ^ q := by
      rw [hPrime.centralizer_eq hQK hQ.ne_bot, hQcard] at hFixQ₀
      exact hFixQ₀
    have hCKne : centralizerWithin S K ≠ ⊥ := by
      intro hbot
      have hScard : Nat.card S = 1 := by
        rw [hbot] at hFixK
        simpa using hFixK
      exact hSnonbot (Subgroup.card_eq_one.mp hScard)
    have hCKtwo : 2 ≤ Nat.card (centralizerWithin S K) :=
      (centralizerWithin S K).one_lt_card_iff_ne_bot.mpr hCKne
    have hKcard : Nat.card K = q :=
      Nat.pow_right_injective hCKtwo (hFixK.symm.trans hFixQ)
    have hKprime : (Nat.card K).Prime := by
      rw [hKcard]
      exact hq

    have hEmbed := sigma_compl_embedding hmaxM hUKM hHallUK
    have hTI : IsNormalizedTI (subgroupNonidentity S) ⊤ M := by
      apply isNormalizedTI_iff_mem_conj.mpr
      refine ⟨?_, le_top, ?_⟩
      · obtain ⟨xS, hxS1⟩ :=
          Subgroup.ne_bot_iff_exists_ne_one.mp hSnonbot
        have hxG1 : (xS : G) ≠ 1 := by
          intro hx
          apply hxS1
          exact Subtype.ext hx
        exact ⟨(xS : G),
          mem_subgroupNonidentity.mpr ⟨xS.property, hxG1⟩⟩
      · intro a ha g _
        rcases mem_subgroupNonidentity.mp ha with ⟨haS, ha1⟩
        constructor
        · intro hag
          by_contra hgM
          have hginvM : g⁻¹ ∉ M := by
            intro hginv
            exact hgM (by simpa using M.inv_mem hginv)
          let e : G ≃* G := MulAut.conj g⁻¹
          let x : G := e a
          rcases mem_subgroupNonidentity.mp hag with ⟨hxS₀, hx1₀⟩
          have hxS : x ∈ S := by
            simpa [x, e, MulAut.conj_apply] using hxS₀
          have hx1 : x ≠ 1 := by
            simpa [x, e, MulAut.conj_apply] using hx1₀
          let T : Subgroup G := S ⊓ M.map e.toMonoidHom
          have hxT : x ∈ T := by
            refine ⟨hxS, ?_⟩
            exact ⟨a, hSM haS, rfl⟩
          have hTcompl : IsPiNumber (betaPrimes M)ᶜ
              (Nat.card T) := by
            simpa only [T, S, e] using
              (hEmbed.2.2 g⁻¹ hginvM).2.1
          have hxBeta : IsPiNumber (betaPrimes M) (orderOf x) :=
            hSbeta.of_dvd (S.orderOf_dvd_natCard hxS)
          have hxBetaCompl : IsPiNumber (betaPrimes M)ᶜ
              (orderOf x) :=
            hTcompl.of_dvd (T.orderOf_dvd_natCard hxT)
          have hxOrder : orderOf x = 1 := by
            simpa [Nat.Coprime] using
              hxBeta.coprime_compl hxBetaCompl
          exact hx1 (orderOf_eq_one_iff.mp hxOrder)
        · intro hgM
          have hgNorm : g ∈ Subgroup.normalizer (S : Set G) :=
            hMnormS hgM
          have hconjS : g⁻¹ * a * g ∈ S :=
            ((Subgroup.mem_set_normalizer_iff''.mp hgNorm) a).mp haS
          refine mem_subgroupNonidentity.mpr ⟨hconjS, ?_⟩
          intro heq
          exact ha1 (by
            simpa [mul_assoc] using
              congrArg (fun z ↦ g * z * g⁻¹) heq)
    exact
      { sigma_eq_beta := hSigmaBeta
        card_K_prime := hKprime
        sigmaCore_nilpotent := by simpa only [S] using hNilS
        sigmaCore_normalizedTI := by simpa only [S] using hTI }
  exact ⟨
    { U := U
      complement := hKappaCompl
      U_K_sdprod := hUKsd
      sigma_UK_sdprod := hSigmaUKsd
      U_abelian := hUcomm
      sigma_K_prime := hPrime
      U_K_semiregular := hReg
      normalizer_direct := hNormDirect
      rankOne_normalizer := hRankOneNormalizer
      Kstar_ne_bot := hKstarNe
      Kstar_line_unique := hKstarUniq
      Kstar_TI_outside := hKstarTI
      K_TI_off_normalizer := hKTI
      Kstar_sylow_unique := hSylowUniq
      sigma_inter_Kstar_le := hSigmaInter
      typeP2 := hP2 }⟩

/-! ## The skolemized complement context -/

/-- `BGsection14.v: kappa_compl_context`, the skolemized form of
Proposition 14.2(a). -/
theorem kappa_compl_context
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M U K : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hCompl : KappaComplement M U K) :
    KappaComplementContext M U K := by
  classical
  by_cases hKbot : K = ⊥
  · subst K
    have hUK : U ⊔ (⊥ : Subgroup G) = U := sup_bot_eq U
    have hHallU_sigma :
        IsHall (sigmaPrimes M)ᶜ (U.subgroupOf M) := by
      have hHall := kappaComplement_sup_hall_structure hCompl
      simpa only [hUK] using hHall
    have hSigma := sdprod_sigma hM hCompl.U_le_M hHallU_sigma
    refine
      { U_sup_K_le_M := by simpa using hCompl.U_le_M
        hall_sigma_complement := by simpa using hHallU_sigma
        U_K_sdprod := ?_
        sigma_UK_sdprod := by simpa using hSigma
        sigma_K_prime := ?_
        U_K_semiregular := ?_
        U_abelian_of_K_ne_bot := fun h ↦ (h rfl).elim }
    · refine ⟨le_sup_left, bot_le, ?_, ?_⟩
      · rw [hUK, Subgroup.subgroupOf_self]
        infer_instance
      · rw [hUK]
        simpa using
          (Subgroup.isComplement'_top_bot :
            (⊤ : Subgroup U).IsComplement' ⊥)
    · intro X hX hXne
      have : X = ⊥ := le_bot_iff.mp hX
      exact (hXne this).elim
    · intro k hk
      exact (hk (Subsingleton.elim k 1)).elim
  · have hP : M ∈ typePMaximalSubgroups := by
      refine ⟨hM, ?_⟩
      intro hF
      have hKbot' := (trivg_kappa hM hCompl.K_le_M hCompl.hall_K).mpr hF
      exact hKbot hKbot'
    have hStruct :=
      Ptype_structure hP hCompl.K_le_M hCompl.hall_K
    let V : Subgroup G := hStruct.U
    let E : Subgroup G := U ⊔ K
    let F : Subgroup G := V ⊔ K
    have hEM : E ≤ M := sup_le hCompl.U_le_M hCompl.K_le_M
    have hFM : F ≤ M := sup_le hStruct.complement.U_le_M
      hStruct.complement.K_le_M
    have hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M) := by
      simpa only [E] using kappaComplement_sup_hall_structure hCompl
    have hHallF : IsHall (sigmaPrimes M)ᶜ (F.subgroupOf M) := by
      simpa only [F, V] using
        kappaComplement_sup_hall_structure hStruct.complement
    obtain ⟨aM, ha⟩ :=
      exists_map_conj_eq_of_isHall_of_isSolvable
        (mmax_sol hM) hHallF hHallE
    have hFa : F.map (MulAut.conj (aM : G)).toMonoidHom = E :=
      ambient_map_conj_eq_of_subgroupOf_structure hFM hEM aM ha
    have hKE : K ≤ E := le_sup_right
    have hKF : K ≤ F := le_sup_right
    have hHallKE : IsHall (kappaPrimes M) (K.subgroupOf E) :=
      isHall_subgroupOf_intermediate_structure hKE hEM hCompl.hall_K
    have hHallKF : IsHall (kappaPrimes M) (K.subgroupOf F) :=
      isHall_subgroupOf_intermediate_structure hKF hFM
        hStruct.complement.hall_K
    let Ka : Subgroup G :=
      K.map (MulAut.conj (aM : G)).toMonoidHom
    have hKaE : Ka ≤ E := by
      exact (Subgroup.map_mono hKF).trans_eq hFa
    have hHallKaE : IsHall (kappaPrimes M) (Ka.subgroupOf E) := by
      have hmap := isHall_subgroupOf_map_mulEquiv_structure
        hKF hHallKF (MulAut.conj (aM : G))
      rw [hFa] at hmap
      simpa only [Ka] using hmap
    obtain ⟨bE, hb⟩ :=
      exists_map_conj_eq_of_isHall_of_isSolvable
        (sigma_compl_sol hEM hHallE) hHallKaE hHallKE
    have hKab : Ka.map (MulAut.conj (bE : G)).toMonoidHom = K :=
      ambient_map_conj_eq_of_subgroupOf_structure hKaE hKE bE hb
    let c : G := (bE : G) * (aM : G)
    have hKc : K.map (MulAut.conj c).toMonoidHom = K := by
      calc
        K.map (MulAut.conj c).toMonoidHom =
            Ka.map (MulAut.conj (bE : G)).toMonoidHom := by
              change K.map (MulAut.conj c).toMonoidHom =
                (K.map (MulAut.conj (aM : G)).toMonoidHom).map
                  (MulAut.conj (bE : G)).toMonoidHom
              rw [Subgroup.map_map]
              congr 1
              ext z
              simp [c, MulAut.conj_apply, mul_assoc]
        _ = K := hKab
    have hEb : E.map (MulAut.conj (bE : G)).toMonoidHom = E :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (Subgroup.le_normalizer bE.property)
    have hFc : F.map (MulAut.conj c).toMonoidHom = E := by
      calc
        F.map (MulAut.conj c).toMonoidHom =
            (F.map (MulAut.conj (aM : G)).toMonoidHom).map
              (MulAut.conj (bE : G)).toMonoidHom := by
                rw [Subgroup.map_map]
                congr 1
                ext z
                simp [c, MulAut.conj_apply, mul_assoc]
        _ = E.map (MulAut.conj (bE : G)).toMonoidHom := by rw [hFa]
        _ = E := hEb
    let Vc : Subgroup G := V.map (MulAut.conj c).toMonoidHom
    have hSdVc : IsInternalSemidirectProductIn Vc K E := by
      have hmap := semidirectProduct_map_mulEquiv_structure
        hStruct.U_K_sdprod (MulAut.conj c)
      rw [hKc, hFc] at hmap
      simpa only [V, Vc, F] using hmap
    have hVE : V ≤ F := le_sup_left
    have hHallVF : IsHall (sigmaKappaPrimes M)ᶜ
        (V.subgroupOf F) :=
      isHall_subgroupOf_intermediate_structure hVE hFM
        hStruct.complement.hall_U
    have hHallVcE : IsHall (sigmaKappaPrimes M)ᶜ
        (Vc.subgroupOf E) := by
      have hmap := isHall_subgroupOf_map_mulEquiv_structure
        hVE hHallVF (MulAut.conj c)
      rw [hFc] at hmap
      simpa only [Vc] using hmap
    have hUE : U ≤ E := le_sup_left
    have hHallUE : IsHall (sigmaKappaPrimes M)ᶜ
        (U.subgroupOf E) :=
      isHall_subgroupOf_intermediate_structure hUE hEM hCompl.hall_U
    have hVeq : Vc = U :=
      normalHall_eq_isHall_structure hSdVc.1 hUE hSdVc.2.2.1
        hHallVcE hHallUE
    have hUKsd : IsInternalSemidirectProductIn U K (U ⊔ K) := by
      simpa only [E, hVeq] using hSdVc
    have hRegMap := semiregularConjugation_map_mulEquiv_structure
      hStruct.U_K_semiregular (MulAut.conj c)
    have hReg : IsSemiregularConjugation U K := by
      rw [hKc] at hRegMap
      simpa only [V, Vc, hVeq] using hRegMap
    have hUcomm : IsMulCommutative U := by
      rw [← hVeq]
      letI : IsMulCommutative V := by simpa only [V] using hStruct.U_abelian
      exact Subgroup.map_isMulCommutative V (MulAut.conj c).toMonoidHom
    refine
      { U_sup_K_le_M := sup_le hCompl.U_le_M hCompl.K_le_M
        hall_sigma_complement := kappaComplement_sup_hall_structure hCompl
        U_K_sdprod := hUKsd
        sigma_UK_sdprod :=
          sdprod_sigma hM (sup_le hCompl.U_le_M hCompl.K_le_M)
            (kappaComplement_sup_hall_structure hCompl)
        sigma_K_prime := hStruct.sigma_K_prime
        U_K_semiregular := hReg
        U_abelian_of_K_ne_bot := fun _ ↦ hUcomm }

/-! ## Corollary 14.3 -/

/-- `BGsection14.v: pi_of_cent_sigma`, Corollary 14.3. -/
theorem pi_of_cent_sigma
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G} (hM : M ∈ minSimple_max_groups (G := G))
    {x y : G}
    (hxSigma : x ∈ sigmaCore M) (hx1 : x ≠ 1)
    (hyCent : y ∈ elementCentralizerWithin M x) (hy1 : y ≠ 1)
    (hySigma' : IsPiNumber (sigmaPrimes M)ᶜ (orderOf y)) :
    (IsPiNumber (kappaPrimes M) (orderOf y) ∧
        elementCentralizer x ≤ M) ∨
      (IsPiNumber (tau2Primes M) (orderOf y) ∧
        sigmaLength y = 1 ∧
        minSimple_max_groups_of (G := G)
          ((elementCentralizer y : Subgroup G) : Set G) = {M}) := by
  classical
  by_cases hyTau2 : IsPiNumber (tau2Primes M) (orderOf y)
  · right
    have huniq :
        minSimple_max_groups_of (G := G)
          ((elementCentralizer y : Subgroup G) : Set G) = {M} := by
      have hsingle := cent1_nreg_sigma_uniq hM hyCent.1 hy1 hyTau2
        (by
          intro hcentBot
          have hxy : Commute x y :=
            Subgroup.mem_centralizer_iff.mp hyCent.2 x
              (Subgroup.mem_zpowers x)
          have hxCentY :
              x ∈ centralizerWithin (sigmaCore M) (Subgroup.zpowers y) :=
            ⟨hxSigma, mem_elementCentralizer_of_commute hxy⟩
          exact hx1 (by simpa [hcentBot] using hxCentY))
      simpa [elementCentralizer, Subgroup.zpowers_eq_closure,
        Subgroup.centralizer_closure] using hsingle
    refine ⟨hyTau2, ?_, huniq⟩
    exact sigmaLength_eq_one_of_tau2_element hM hyCent.1 hy1 hyTau2
  · obtain ⟨p, hpY, hpNotTau2⟩ :=
      exists_primeSupport_not_mem_of_not_isPiNumber hyTau2
    letI : Fact p.Prime := ⟨hpY.1⟩
    have hpM : p ∈ primeSupport (Nat.card M) :=
      primeSupport_orderOf_mem_of_mem hyCent.1 hpY
    have hpTau13 : p ∈ tau13Primes M := by
      exact (prime_not_sigma_mem_tau2_or_tau13 hM hpM
        (hySigma' hpY.1 hpY.2)).resolve_left hpNotTau2
    obtain ⟨X, hXline, hXcycle⟩ :=
      exists_rankOneLineIn_zpowers hpY
    have hXM : X ≤ M :=
      hXcycle.trans (Subgroup.zpowers_le.mpr hyCent.1)
    have hxy : Commute x y :=
      Subgroup.mem_centralizer_iff.mp hyCent.2 x
        (Subgroup.mem_zpowers x)
    have hpKappa : p ∈ kappaPrimes M := by
      refine ⟨hpTau13, X, ?_, ?_⟩
      · exact ⟨hXM, hXline⟩
      · intro hcentBot
        have hxCentX : x ∈ centralizerWithin (sigmaCore M) X :=
          ⟨hxSigma, fun z hz ↦
            Subgroup.mem_centralizer_iff.mp
              (mem_elementCentralizer_of_commute hxy) z
              (hXcycle hz)⟩
        exact hx1 (by simpa [hcentBot] using hxCentX)
    obtain ⟨K, hXK, hKM, hHallK⟩ :=
      MathlibSupport.exists_ambient_isHall_ge_of_isSolvable
        hXM (mmax_sol hM) (kappaPrimes M)
        (hXline.isPGroup.isPiNumber_natCard hpKappa)
    have hP : M ∈ typePMaximalSubgroups :=
      (PtypeP hM).2 ⟨p, hpKappa⟩
    have hStruct := Ptype_structure hP hKM hHallK
    have hXKline : RankOneLineIn p K X := ⟨hXK, hXline⟩
    have hNormEq := (hStruct.rankOne_normalizer hXKline).1
    have hCMyX :
        elementCentralizerWithin M y ≤ normalizerWithin M X := by
      intro z hz
      refine ⟨hz.1, ?_⟩
      exact (Subgroup.centralizer_le_normalizer (X : Set G))
        ((Subgroup.centralizer_le hXcycle) hz.2)
    have hCMy : elementCentralizerWithin M y ≤ normalizerWithin M K :=
      hCMyX.trans_eq hNormEq
    have hKsigmaCompl :
        IsPiNumber (sigmaPrimes M)ᶜ (Nat.card K) := by
      have hKappaCard :=
        hHallK.isPiNumber_card.mono (kappa_sigma' M)
      simpa only [MathlibSupport.natCard_subgroupOf_eq hKM] using hKappaCard
    have hKstarSigma :
        IsPiNumber (sigmaPrimes M)
          (Nat.card (pTypeCentralizer M K)) :=
      (sigmaCore_isPiNumber M).of_dvd
        (Subgroup.card_dvd_of_le
          (centralizerWithin_le_left (sigmaCore M) K))
    have hHallFactors :=
      complementary_isHall_of_internalDirectProduct_structure
        hStruct.normalizer_direct hKsigmaCompl hKstarSigma
    have hNormalFactors :=
      internalDirectProduct_normal_factors_structure
        hStruct.normalizer_direct
    left
    refine ⟨?_, ?_⟩
    · have hyCMy : y ∈ elementCentralizerWithin M y :=
        ⟨hyCent.1,
          mem_elementCentralizer_of_commute (Commute.refl y)⟩
      have hyNorm : y ∈ normalizerWithin M K := hCMy hyCMy
      have hyK : y ∈ K :=
        mem_normalHall_of_isPiNumber_order_structure
          hStruct.normalizer_direct.left_le hNormalFactors.1
          hHallFactors.1 hyNorm hySigma'
      have hKkappa : IsPiNumber (kappaPrimes M) (Nat.card K) := by
        simpa only [MathlibSupport.natCard_subgroupOf_eq hKM] using
          hHallK.isPiNumber_card
      exact hKkappa.of_dvd (K.orderOf_dvd_natCard hyK)
    · have hxKstar : Subgroup.zpowers x ≤ pTypeCentralizer M K := by
        have hxM : x ∈ M := (sigmaCore_le M) hxSigma
        have hxCMy : x ∈ elementCentralizerWithin M y :=
          ⟨hxM, mem_elementCentralizer_of_commute hxy⟩
        have hxNorm : x ∈ normalizerWithin M K := hCMy hxCMy
        have hxSigmaOrder :
            IsPiNumber (sigmaPrimes M) (orderOf x) :=
          (sigmaCore_isPiNumber M).of_dvd
            ((sigmaCore M).orderOf_dvd_natCard hxSigma)
        have hxKstar : x ∈ pTypeCentralizer M K :=
          mem_normalHall_of_isPiNumber_order_structure
            hStruct.normalizer_direct.right_le hNormalFactors.2
            hHallFactors.2 hxNorm hxSigmaOrder
        exact Subgroup.zpowers_le.mpr hxKstar
      obtain ⟨r, hrOrder⟩ := exists_prime_mem_primeSupport_orderOf hx1
      letI : Fact r.Prime := ⟨hrOrder.1⟩
      obtain ⟨Z, hZelem, hZx⟩ :=
        exists_rankOneLineIn_zpowers hrOrder
      have hZline : RankOneLineIn r (pTypeCentralizer M K) Z :=
        ⟨hZx.trans hxKstar, hZelem⟩
      have huniq := hStruct.Kstar_line_unique hZline
      exact (Subgroup.centralizer_le hZx).trans
        (mem_uniq_mmax huniq).2

/-! ## Theorem 14.4 -/

/-- `BGsection14.v: FT_signalizer_context`, Theorem 14.4. -/
theorem FT_signalizer_context
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {x : G} (hell : sigmaLength x = 1) :
    FTSignalizerContext x (ftSignalizerBase x) (ftSignalizer x) := by
  classical
  let N : Subgroup G := ftSignalizerBase x
  let R : Subgroup G := ftSignalizer x
  obtain ⟨hx1, ⟨M, hMmem⟩⟩ := (ell_sigma1P (x := x)).mp hell
  have hMmax : M ∈ minSimple_max_groups (G := G) := hMmem.1
  have hxSigma : Subgroup.zpowers x ≤ sigmaCore M := hMmem.2
  have hxM : x ∈ M := (sigmaCore_le M) (hxSigma (Subgroup.mem_zpowers x))

  by_cases hsmall :
      (sigmaMaximalOvergroups (Subgroup.zpowers x : Set G)).ncard ≤ 1
  · have hNbot : N = ⊥ := ftSignalizerBase_eq_bot_of_ncard_le_one hsmall
    have hSigmaNbot : sigmaCore N = ⊥ := by
      apply le_antisymm _ bot_le
      rw [← hNbot]
      exact sigmaCore_le N
    have hRbot : R = ⊥ := by
      change centralizerWithin (sigmaCore N) (Subgroup.zpowers x) = ⊥
      apply le_antisymm _ bot_le
      exact (centralizerWithin_le_left (sigmaCore N)
        (Subgroup.zpowers x)).trans hSigmaNbot.le
    have hSigmaBot : sigmaPrimes (⊥ : Subgroup G) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro p hpSigma
      rcases hpSigma with ⟨_, P, hNorm⟩
      have hAmb : ambientSylow (⊥ : Subgroup G) P = ⊥ := by
        apply le_antisymm (Subgroup.map_subtype_le _) bot_le
      have hxNorm : x ∈ Subgroup.normalizer
          ((ambientSylow (⊥ : Subgroup G) P : Subgroup G) : Set G) := by
        rw [hAmb, Subgroup.mem_normalizer_iff]
        intro z
        simp
      exact hx1 (Subgroup.mem_bot.mp (hNorm hxNorm))
    refine
      { basic :=
          { R_le_centralizer := by
              change R ≤ elementCentralizer x
              rw [hRbot]
              exact bot_le
            R_normal := by
              change (R.subgroupOf (elementCentralizer x)).Normal
              rw [hRbot]
              infer_instance
            R_hall := by
              change IsHall (sigmaPrimes N)
                (R.subgroupOf (elementCentralizer x))
              rw [hRbot, hNbot, hSigmaBot]
              constructor
              · simpa using (IsPiNumber.one (pi := (∅ : Set ℕ)))
              · intro p _ _
                simp
            transitive := ?_
            card_eq := ?_ }
        small_signalizer := fun _ ↦ hRbot
        large := fun hlarge ↦ (not_lt_of_ge hsmall hlarge).elim }
    · intro M₁ M₂ hM₁ hM₂
      have hset : sigmaMaximalOvergroups (Subgroup.zpowers x : Set G) = {M₁} := by
        apply Set.eq_singleton_iff_unique_mem.mpr
        refine ⟨hM₁, ?_⟩
        intro L hL
        exact ncard_le_one_unique hsmall hL hM₁
      have : M₂ = M₁ := by
        rw [hset] at hM₂
        simpa using hM₂
      subst M₂
      refine ⟨1, by simp [hRbot], ?_⟩
      convert (Subgroup.map_id M₁).symm using 1
      ext z
      simp [MulAut.conj_apply]
    · have hcardSet :
          (sigmaMaximalOvergroups (Subgroup.zpowers x : Set G)).ncard = 1 := by
        have hpos : 0 <
            (sigmaMaximalOvergroups (Subgroup.zpowers x : Set G)).ncard :=
          (Set.ncard_pos).mpr ⟨M, hMmem⟩
        omega
      change Nat.card R =
        (sigmaMaximalOvergroups (Subgroup.zpowers x : Set G)).ncard
      rw [hRbot, hcardSet]
      simp
  · have hlarge :
        1 < (sigmaMaximalOvergroups (Subgroup.zpowers x : Set G)).ncard := by
      omega
    obtain ⟨q, hqOrder⟩ := exists_prime_mem_primeSupport_orderOf hx1
    letI : Fact q.Prime := ⟨hqOrder.1⟩
    obtain ⟨X, hXline, hXcycle⟩ :=
      exists_rankOneLineIn_zpowers hqOrder
    obtain ⟨N₀, hN₀max, hNXN₀⟩ :=
      exists_maximalOvergroup_normalizer hXline.ne_bot hXline.isPGroup
    have hCXN₀ : Subgroup.centralizer (X : Set G) ≤ N₀ :=
      (Subgroup.centralizer_le_normalizer (X : Set G)).trans hNXN₀
    have hCxN₀ : elementCentralizer x ≤ N₀ :=
      (Subgroup.centralizer_le hXcycle).trans hCXN₀
    have hXSigmaM : X ≤ sigmaCore M := hXcycle.trans hxSigma
    have hqSigmaM : q ∈ sigmaPrimes M := by
      exact (sigmaCore_isPiNumber M).of_dvd
        ((sigmaCore M).orderOf_dvd_natCard
          (hxSigma (Subgroup.mem_zpowers x)))
          hqOrder.1 hqOrder.2
    have hMX : M ∈ sigmaMaximalOvergroups (X : Set G) :=
      ⟨hMmax, hXSigmaM⟩
    have hConjugateOvergroup :
        ∀ {L : Subgroup G},
          L ∈ sigmaMaximalOvergroups (X : Set G) →
          (∃ a : G, L = M.map (MulAut.conj a).toMonoidHom) ∧
            X ≤ L := by
      intro L hL
      have hXL : X ≤ L := hL.2.trans (sigmaCore_le L)
      refine ⟨?_, hXL⟩
      by_contra hnotConj
      push_neg at hnotConj
      have hdis := sigma_partition hMmax hL.1 hnotConj
      have hqSigmaL : q ∈ sigmaPrimes L := by
        apply sigmaCore_isPiNumber L hqOrder.1
        have hqX : q ∣ Nat.card X := by
          rw [hXline.card_eq, pow_one]
        exact hqX.trans (Subgroup.card_dvd_of_le hL.2)
      exact Set.disjoint_left.mp hdis hqSigmaM hqSigmaL
    have hTransCX :
        ∀ {L₁ L₂ : Subgroup G},
          L₁ ∈ sigmaMaximalOvergroups (X : Set G) →
          L₂ ∈ sigmaMaximalOvergroups (X : Set G) →
          ∃ c : G, c ∈ Subgroup.centralizer (X : Set G) ∧
            L₂ = L₁.map (MulAut.conj c).toMonoidHom := by
      intro L₁ L₂ hL₁ hL₂
      exact (sigma_group_trans hMmax hqSigmaM hXline.isPGroup).2.1
        (hConjugateOvergroup hL₁) (hConjugateOvergroup hL₂)
    have hCXnotM : ¬ Subgroup.centralizer (X : Set G) ≤ M := by
      intro hCXM
      have hset : sigmaMaximalOvergroups
          (Subgroup.zpowers x : Set G) = {M} := by
        apply Set.eq_singleton_iff_unique_mem.mpr
        refine ⟨hMmem, ?_⟩
        intro L hL
        have hLX : L ∈ sigmaMaximalOvergroups (X : Set G) :=
          ⟨hL.1, hXcycle.trans hL.2⟩
        obtain ⟨c, hcC, hLc⟩ := hTransCX hMX hLX
        have hcNorm : c ∈ Subgroup.normalizer (M : Set G) :=
          Subgroup.le_normalizer (hCXM hcC)
        have hMc : M.map (MulAut.conj c).toMonoidHom = M :=
          Subgroup.mem_normalizer_iff_map_conj_eq.mp hcNorm
        exact hLc.trans hMc
      rw [hset] at hlarge
      simpa using hlarge
    have hNnotM : N₀ ≠ M := by
      intro hNM
      exact hCXnotM (by simpa [hNM] using hCXN₀)
    have hXM : X ≤ M :=
      hXcycle.trans (hxSigma.trans (sigmaCore_le M))
    have hEmbed := sigma_subgroup_embedding
      hMmax hqSigmaM hXM hXline.isPGroup hXline.ne_bot
        ⟨hN₀max, hNXN₀⟩ hNnotM
    have hqNotSigmaN : q ∉ sigmaPrimes N₀ := by
      intro hqSigmaN
      exact Set.disjoint_left.mp
        (sigma_partition hMmax hN₀max hEmbed.1)
          hqSigmaM hqSigmaN
    let I : Subgroup G := M ⊓ N₀
    have hXI : X ≤ I :=
      le_inf hXM (Subgroup.le_normalizer.trans hNXN₀)
    let XI : Subgroup I := X.subgroupOf I
    have hXIq : IsPGroup q XI :=
      hXline.isPGroup.of_equiv
        (Subgroup.subgroupOfEquivOfLe hXI).symm
    obtain ⟨S, hXIS⟩ := hXIq.exists_le_sylow
    have hXS : X ≤ ambientSylow I S := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hXI]
      exact Subgroup.map_mono hXIS
    have hEmbedPart := hEmbed.2 S hXS
    have hEmbedBranch :
        q ∈ tau2Primes N₀ ∧
          primeSupport (Nat.card M) ∩ sigmaPrimes N₀ ⊆
            betaPrimes N₀ ∧
          IsHall (sigmaPrimes N₀)ᶜ ((M ⊓ N₀).subgroupOf N₀) := by
      simpa [I, hqNotSigmaN] using hEmbedPart.2.2
    have hqTau2N : q ∈ tau2Primes N₀ := hEmbedBranch.1
    have hBetaMN :
        primeSupport (Nat.card M) ∩ sigmaPrimes N₀ ⊆
          betaPrimes N₀ := hEmbedBranch.2.1
    have hHallMN :
        IsHall (sigmaPrimes N₀)ᶜ ((M ⊓ N₀).subgroupOf N₀) :=
      hEmbedBranch.2.2
    have hSdN :
        IsInternalSemidirectProductIn (sigmaCore N₀) (M ⊓ N₀) N₀ :=
      sdprod_sigma hN₀max inf_le_right hHallMN
    let R₀ : Subgroup G :=
      centralizerWithin (sigmaCore N₀) (Subgroup.zpowers x)
    have hR₀def : R₀ = centralizerWithin (sigmaCore N₀)
        (Subgroup.zpowers x) := rfl
    have hR₀le : R₀ ≤ elementCentralizer x := by
      rw [hR₀def]
      exact inf_le_right
    have hR₀normal :
        (R₀.subgroupOf (elementCentralizer x)).Normal := by
      rw [hR₀def]
      change
        ((sigmaCore N₀ ⊓ elementCentralizer x).subgroupOf
          (elementCentralizer x)).Normal
      exact normal_inf_subgroupOf_of_le_structure
        (sigmaCore_le N₀) hCxN₀ (sigmaCore_normal N₀)
    have hR₀Hall :
        IsHall (sigmaPrimes N₀)
          (R₀.subgroupOf (elementCentralizer x)) := by
      rw [hR₀def]
      change IsHall (sigmaPrimes N₀)
        ((sigmaCore N₀ ⊓ elementCentralizer x).subgroupOf
          (elementCentralizer x))
      exact isHall_inf_of_normal_le_structure
        (sigmaCore_le N₀) hCxN₀ (sigmaCore_normal N₀)
          (Msigma_Hall hN₀max)
    have hCxSd₀ :
        IsInternalSemidirectProductIn R₀
          (elementCentralizerWithin (M ⊓ N₀) x)
          (elementCentralizer x) := by
      rw [hR₀def]
      have hXMN₀ : Subgroup.zpowers x ≤ M ⊓ N₀ :=
        Subgroup.zpowers_le.mpr
          ⟨hxM, hCxN₀
            (mem_elementCentralizer_of_commute (Commute.refl x))⟩
      have hcentSd :=
        centralizerWithin_semidirectProduct_structure hSdN hXMN₀
      have hfull : centralizerWithin N₀ (Subgroup.zpowers x) =
          elementCentralizer x := inf_eq_right.mpr hCxN₀
      simpa only [hfull] using hcentSd
    have hTransR₀ :
        ∀ {L₁ L₂ : Subgroup G},
          L₁ ∈ sigmaMaximalOvergroups (Subgroup.zpowers x : Set G) →
          L₂ ∈ sigmaMaximalOvergroups (Subgroup.zpowers x : Set G) →
          ∃ r : G, r ∈ R₀ ∧
            L₂ = L₁.map (MulAut.conj r).toMonoidHom := by
      have hBase : ∀ {L : Subgroup G},
          L ∈ sigmaMaximalOvergroups (Subgroup.zpowers x : Set G) →
          ∃ r : G, r ∈ R₀ ∧
            L = M.map (MulAut.conj r).toMonoidHom := by
        intro L hL
        have hLX : L ∈ sigmaMaximalOvergroups (X : Set G) :=
          ⟨hL.1, hXcycle.trans hL.2⟩
        obtain ⟨u, huC, hLu⟩ := hTransCX hMX hLX
        let uN : N₀ := ⟨u, hCXN₀ huC⟩
        obtain ⟨⟨a, b⟩, hab⟩ := hSdN.2.2.2.2 uN
        have hu : (a : G) * (b : G) = u :=
          congrArg Subtype.val hab
        have hxL : x ∈ L :=
          (sigmaCore_le L) (hL.2 (Subgroup.mem_zpowers x))
        have hxMap : x ∈ M.map (MulAut.conj u).toMonoidHom := by
          rwa [hLu] at hxL
        rcases hxMap with ⟨m, hmM, hmx⟩
        have haConjM : (a : G)⁻¹ * x * (a : G) ∈ M := by
          have heq : (a : G)⁻¹ * x * (a : G) =
              (b : G) * m * (b : G)⁻¹ := by
            have hmx' : u * m * u⁻¹ = x := by
              simpa [MulAut.conj_apply] using hmx
            rw [← hmx', ← hu]
            group
          rw [heq]
          exact M.mul_mem
            (M.mul_mem b.property.1 hmM) (M.inv_mem b.property.1)
        let xN : N₀ :=
          ⟨x, hCxN₀
            (mem_elementCentralizer_of_commute (Commute.refl x))⟩
        let dN : N₀ :=
          (a : N₀)⁻¹ * xN * (a : N₀) * xN⁻¹
        have hdA : dN ∈ (sigmaCore N₀).subgroupOf N₀ := by
          have hxax : xN * (a : N₀) * xN⁻¹ ∈
              (sigmaCore N₀).subgroupOf N₀ :=
            hSdN.2.2.1.conj_mem a a.property xN
          have hprod := ((sigmaCore N₀).subgroupOf N₀).mul_mem
            (((sigmaCore N₀).subgroupOf N₀).inv_mem a.property) hxax
          simpa only [dN, mul_assoc] using hprod
        have hdM : (dN : G) ∈ M := by
          exact M.mul_mem haConjM (M.inv_mem hxM)
        have hdI : dN ∈ (M ⊓ N₀).subgroupOf N₀ :=
          ⟨hdM, dN.property⟩
        have hdBot : dN ∈ (⊥ : Subgroup N₀) :=
          hSdN.2.2.2.disjoint.le_bot ⟨hdA, hdI⟩
        have hdOne : (a : G)⁻¹ * x * (a : G) * x⁻¹ = 1 := by
          exact congrArg Subtype.val (Subgroup.mem_bot.mp hdBot)
        have hconj : (a : G)⁻¹ * x * (a : G) = x := by
          calc
            (a : G)⁻¹ * x * (a : G) =
                ((a : G)⁻¹ * x * (a : G) * x⁻¹) * x := by
                  group
            _ = 1 * x := by rw [hdOne]
            _ = x := one_mul x
        have hax : Commute (a : G) x := by
          change (a : G) * x = x * (a : G)
          calc
            (a : G) * x =
                (a : G) * ((a : G)⁻¹ * x * (a : G)) :=
              (congrArg (fun t : G => (a : G) * t) hconj).symm
            _ = x * (a : G) := by group
        have haR : (a : G) ∈ R₀ := by
          rw [hR₀def]
          exact ⟨a.property,
            mem_elementCentralizer_of_commute hax⟩
        have hbNorm : (b : G) ∈ Subgroup.normalizer (M : Set G) :=
          Subgroup.le_normalizer b.property.1
        have hMb : M.map (MulAut.conj (b : G)).toMonoidHom = M :=
          Subgroup.mem_normalizer_iff_map_conj_eq.mp hbNorm
        refine ⟨a, haR, ?_⟩
        calc
          L = M.map (MulAut.conj u).toMonoidHom := hLu
          _ = M.map (MulAut.conj ((a : G) * (b : G))).toMonoidHom := by
            rw [hu]
          _ = (M.map (MulAut.conj (b : G)).toMonoidHom).map
                (MulAut.conj (a : G)).toMonoidHom := by
            rw [Subgroup.map_map]
            congr 1
            ext z
            simp [MulAut.conj_apply, mul_assoc]
          _ = M.map (MulAut.conj (a : G)).toMonoidHom := by rw [hMb]
      intro L₁ L₂ hL₁ hL₂
      obtain ⟨r₁, hr₁, hL₁eq⟩ := hBase hL₁
      obtain ⟨r₂, hr₂, hL₂eq⟩ := hBase hL₂
      let r : G := r₂ * r₁⁻¹
      have hr : r ∈ R₀ := R₀.mul_mem hr₂ (R₀.inv_mem hr₁)
      refine ⟨r, hr, ?_⟩
      rw [hL₁eq, hL₂eq, Subgroup.map_map]
      congr 1
      ext z
      simp [r, MulAut.conj_apply, mul_assoc]
    have hCardR₀ : Nat.card R₀ =
        (sigmaMaximalOvergroups (Subgroup.zpowers x : Set G)).ncard := by
      let Ω : Set (Subgroup G) :=
        sigmaMaximalOvergroups (Subgroup.zpowers x : Set G)
      have hconjugateSet : ∀ r : R₀,
          conjugateSet (r : G) (Subgroup.zpowers x : Set G) =
            (Subgroup.zpowers x : Set G) := by
        intro r
        ext z
        constructor
        · rintro ⟨w, hw, rfl⟩
          have hwr : w * (r : G) = (r : G) * w :=
            Subgroup.mem_centralizer_iff.mp (hR₀le r.property) w hw
          have heq : (r : G) * w * (r : G)⁻¹ = w := by
            rw [← hwr]
            group
          simpa [conjugateSet, MulAut.conj_apply, heq] using hw
        · intro hz
          refine ⟨z, hz, ?_⟩
          have hzr : z * (r : G) = (r : G) * z :=
            Subgroup.mem_centralizer_iff.mp (hR₀le r.property) z hz
          change (r : G) * z * (r : G)⁻¹ = z
          rw [← hzr]
          group
      let f : R₀ → Ω := fun r ↦
        ⟨M.map (MulAut.conj (r : G)).toMonoidHom, by
          change M.map (MulAut.conj (r : G)).toMonoidHom ∈
            sigmaMaximalOvergroups (Subgroup.zpowers x : Set G)
          rw [← hconjugateSet r]
          exact (sigma_mmaxJ M (Subgroup.zpowers x : Set G) r).mpr hMmem⟩
      have hfSurj : Function.Surjective f := by
        intro L
        obtain ⟨r, hrR₀, hL⟩ := hTransR₀ hMmem L.property
        refine ⟨⟨r, hrR₀⟩, ?_⟩
        apply Subtype.ext
        exact hL.symm
      have hfInj : Function.Injective f := by
        intro r s hrs
        have hmapEq :
            M.map (MulAut.conj (r : G)).toMonoidHom =
              M.map (MulAut.conj (s : G)).toMonoidHom :=
          congrArg Subtype.val hrs
        let d : G := (r : G)⁻¹ * (s : G)
        have hdR₀ : d ∈ R₀ := R₀.mul_mem
          (R₀.inv_mem r.property) s.property
        have hmapd : M.map (MulAut.conj d).toMonoidHom = M := by
          calc
            M.map (MulAut.conj d).toMonoidHom =
                (M.map (MulAut.conj (s : G)).toMonoidHom).map
                  (MulAut.conj (r : G)⁻¹).toMonoidHom := by
                    rw [Subgroup.map_map]
                    congr 1
                    ext z
                    simp [d, MulAut.conj_apply, mul_assoc]
            _ = (M.map (MulAut.conj (r : G)).toMonoidHom).map
                  (MulAut.conj (r : G)⁻¹).toMonoidHom := by
                    rw [hmapEq]
            _ = M := by
              rw [Subgroup.map_map]
              convert Subgroup.map_id M using 1
              ext z
              simp [MulAut.conj_apply, mul_assoc]
        have hdNorm : d ∈ Subgroup.normalizer (M : Set G) :=
          Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmapd
        have hdM : d ∈ M := by
          rwa [norm_mmax hMmax] at hdNorm
        have hdSigmaG : d ∈ sigmaCore N₀ := by
          have hdR₀' := hdR₀
          rw [hR₀def] at hdR₀'
          exact hdR₀'.1
        let dN : N₀ := ⟨d, (sigmaCore_le N₀) hdSigmaG⟩
        have hdSigma : dN ∈ (sigmaCore N₀).subgroupOf N₀ := by
          exact hdSigmaG
        have hdMN : dN ∈ (M ⊓ N₀).subgroupOf N₀ :=
          ⟨hdM, dN.property⟩
        have hdBot : dN ∈ (⊥ : Subgroup N₀) :=
          hSdN.2.2.2.disjoint.le_bot ⟨hdSigma, hdMN⟩
        have hdOne : d = 1 :=
          congrArg Subtype.val (Subgroup.mem_bot.mp hdBot)
        apply Subtype.ext
        change (r : G) = (s : G)
        have : (r : G)⁻¹ * (s : G) = 1 := by
          simpa only [d] using hdOne
        exact inv_mul_eq_one.mp this
      have hcard := Nat.card_congr
        (Equiv.ofBijective f ⟨hfInj, hfSurj⟩)
      simpa only [Ω, Nat.card_coe_set_eq] using hcard
    have hR₀ne : R₀ ≠ ⊥ := by
      intro hR₀bot
      have : Nat.card R₀ = 1 := Subgroup.card_eq_one.mpr hR₀bot
      omega
    obtain ⟨yR, hyR1⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.mp hR₀ne
    let y : G := yR
    have hy1 : y ≠ 1 := by
      intro hy
      apply hyR1
      exact Subtype.ext hy
    have hyR₀ : y ∈ R₀ := yR.property
    rw [hR₀def] at hyR₀
    have hySigma : y ∈ sigmaCore N₀ := hyR₀.1
    have hxy : Commute x y :=
      Subgroup.mem_centralizer_iff.mp hyR₀.2 x
        (Subgroup.mem_zpowers x)
    have hxMN₀ : x ∈ M ⊓ N₀ :=
      ⟨hxM, hCxN₀ (mem_elementCentralizer_of_commute (Commute.refl x))⟩
    have hyCent : x ∈ elementCentralizerWithin N₀ y :=
      ⟨hxMN₀.2, mem_elementCentralizer_of_commute hxy⟩
    have hxSigma' : IsPiNumber (sigmaPrimes N₀)ᶜ (orderOf x) :=
      (by
        have hIcompl : IsPiNumber (sigmaPrimes N₀)ᶜ
            (Nat.card (M ⊓ N₀ : Subgroup G)) := by
          simpa only [MathlibSupport.natCard_subgroupOf_eq inf_le_right] using
            hHallMN.isPiNumber_card
        exact hIcompl.of_dvd
          ((M ⊓ N₀).orderOf_dvd_natCard hxMN₀))
    have hCentAlt :=
      pi_of_cent_sigma hN₀max hySigma hy1 hyCent hx1 hxSigma'
    rcases hCentAlt with hKappa | ⟨hxTau2, hxEll, hCentUnique⟩
    · have hqKappa : q ∈ kappaPrimes N₀ :=
        hKappa.1 hqOrder.1 hqOrder.2
      rcases kappa_tau13 hqKappa with hqTau1 | hqTau3
      · exact ((tau2'1 N₀ hqTau1) hqTau2N).elim
      · exact ((tau3'2 N₀ hqTau2N) hqTau3).elim
    have hTauSigmaM : tau2Primes N₀ ⊆ sigmaPrimes M := by
      intro p hpTauN
      letI : Fact p.Prime := ⟨hpTauN.1⟩
      obtain ⟨A, hAI, _hAN, hA⟩ :=
        ex_tau2Elem inf_le_right hHallMN hpTauN
      by_contra hpNotSigmaM
      have hpA : p ∣ Nat.card A := by
        rw [hA.card_eq]
        exact dvd_pow_self p (by omega)
      have hpM : p ∈ primeSupport (Nat.card M) :=
        ⟨hpTauN.1, hpA.trans
          (Subgroup.card_dvd_of_le (hAI.trans inf_le_left))⟩
      have hpTauM : p ∈ tau2Primes M := by
        rcases prime_not_sigma_mem_tau2_or_tau13 hMmax hpM hpNotSigmaM with
          hpTauM | hpTau13M
        · exact hpTauM
        · rcases hpTau13M with hpTau1M | hpTau3M
          · exact (hpTau1M.2.2.2.1
              ⟨A, hAI.trans inf_le_left, hA⟩).elim
          · exact (hpTau3M.2.2.2.1
              ⟨A, hAI.trans inf_le_left, hA⟩).elim
      have hTauComplN := tau2_compl_context hN₀max inf_le_right
        hHallMN hpTauN hAI hA
      have hxNormA : x ∈ Subgroup.normalizer (A : Set G) :=
        hTauComplN.A_normalizer_le hxMN₀
      have hXNormA : X ≤ Subgroup.normalizer (A : Set G) :=
        hXcycle.trans (Subgroup.zpowers_le.mpr hxNormA)
      have hAnormSigma :
          A ≤ Subgroup.normalizer (sigmaCore M : Set G) := by
        exact (hAI.trans inf_le_left).trans
          ((Subgroup.normal_subgroupOf_iff_le_normalizer
            (sigmaCore_le M)).mp (sigmaCore_normal M))
      have hcop :
          (Nat.card (sigmaCore M)).Coprime (Nat.card A) :=
        (sigmaCore_isPiNumber M).coprime_compl
          (hA.isPGroup.isPiNumber_natCard hpTauM.2.1)
      have hXcentA : X ≤ centralizerWithin (sigmaCore M) A := by
        refine le_inf hXSigmaM ?_
        intro z hz
        exact mem_centralizer_of_mem_of_mem_normalizer_of_coprime
          hAnormSigma hcop (hXSigmaM hz) (hXNormA hz)
      have hXbot : X ≤ ⊥ := by
        rw [← (tau2_context hMmax hpTauM
          (hAI.trans inf_le_left) hA).centralizerWithin_eq_bot]
        exact hXcentA
      exact hXline.ne_bot (le_bot_iff.mp hXbot)
    /- The source only identifies the chosen signalizer base after
    `pi_of_cent_sigma` has made the maximal overgroup of `C[x]` unique. -/
    have hNdef : N = N₀ :=
      ftSignalizerBase_eq_of_large_unique hlarge hCentUnique
    have hRdef : R = R₀ := by
      change centralizerWithin (sigmaCore N) (Subgroup.zpowers x) = R₀
      rw [hNdef, hR₀def]
    subst N₀
    subst R₀
    have hNtype :
        N ∈ typeFMaximalSubgroups ∪ typeP2MaximalSubgroups := by
      by_cases hNF : N ∈ typeFMaximalSubgroups (G := G)
      · exact Or.inl hNF
      · right
        have hNP : N ∈ typePMaximalSubgroups (G := G) :=
          ⟨hN₀max, hNF⟩
        refine ⟨hNP, ?_⟩
        rintro ⟨_, hSigmaKappaN⟩
        have hqNcard : q ∣ Nat.card N :=
          hqOrder.2.trans (N.orderOf_dvd_natCard hxMN₀.2)
        have hqSigmaKappa : q ∈ sigmaKappaPrimes N :=
          hSigmaKappaN hqOrder.1 hqNcard
        rcases hqSigmaKappa with hqSigma | hqKappa
        · exact hqNotSigmaN hqSigma
        · rcases kappa_tau13 hqKappa with hqTau1 | hqTau3
          · exact tau2'1 N hqTau1 hqTau2N
          · exact tau3'2 N hqTau2N hqTau3
    have hLocal :
        ∀ {L : Subgroup G},
          L ∈ sigmaMaximalOvergroups (Subgroup.zpowers x : Set G) →
          FTSignalizerOvergroupContext x N R L := by
      intro L hL
      obtain ⟨r, hrR, rfl⟩ := hTransR₀ hMmem hL
      have hrCent : r ∈ centralizerWithin (sigmaCore N)
          (Subgroup.zpowers x) := by
        rw [← hR₀def]
        exact hrR
      have hrSigma : r ∈ sigmaCore N := hrCent.1
      have hrN : r ∈ N := (sigmaCore_le N) hrSigma
      have hNmap :
          N.map (MulAut.conj r).toMonoidHom = N :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp
          (Subgroup.le_normalizer hrN)
      have hInfMap :
          (M ⊓ N).map (MulAut.conj r).toMonoidHom =
            M.map (MulAut.conj r).toMonoidHom ⊓ N := by
        rw [Subgroup.map_inf M N _ (MulAut.conj r).injective,
          hNmap]
      have hHallMap := isHall_subgroupOf_map_mulEquiv_structure
        inf_le_right hHallMN (MulAut.conj r)
      rw [hNmap, hInfMap] at hHallMap
      have hHall :
          IsHall (sigmaPrimes N)ᶜ
            ((M.map (MulAut.conj r).toMonoidHom ⊓ N).subgroupOf N) := by
        exact hHallMap
      have hxMapM : x ∈ M.map (MulAut.conj r).toMonoidHom := by
        refine ⟨x, hxM, ?_⟩
        change r * x * r⁻¹ = x
        have hxr : x * r = r * x :=
          Subgroup.mem_centralizer_iff.mp hrCent.2 x
            (Subgroup.mem_zpowers x)
        rw [← hxr]
        group
      have hXMapMN : Subgroup.zpowers x ≤
          M.map (MulAut.conj r).toMonoidHom ⊓ N :=
        Subgroup.zpowers_le.mpr
          ⟨hxMapM, hCxN₀
            (mem_elementCentralizer_of_commute (Commute.refl x))⟩
      have hSdMap : IsInternalSemidirectProductIn (sigmaCore N)
          (M.map (MulAut.conj r).toMonoidHom ⊓ N) N :=
        sdprod_sigma hN₀max inf_le_right hHall
      have hCentSd' :=
        centralizerWithin_semidirectProduct_structure hSdMap hXMapMN
      have hfull : centralizerWithin N (Subgroup.zpowers x) =
          elementCentralizer x := inf_eq_right.mpr hCxN₀
      have hCentSd :
          IsInternalSemidirectProductIn R
            (elementCentralizerWithin
              (M.map (MulAut.conj r).toMonoidHom ⊓ N) x)
            (elementCentralizer x) := by
        rw [← hR₀def, hfull] at hCentSd'
        exact hCentSd'
      have hTauSigma : tau2Primes N ⊆
          sigmaPrimes (M.map (MulAut.conj r).toMonoidHom) := by
        intro p hp
        simpa only [sigmaPrimes_conj] using hTauSigmaM hp
      have hBeta :
          primeSupport
                (Nat.card (M.map (MulAut.conj r).toMonoidHom)) ∩
              sigmaPrimes N ⊆
            betaPrimes N := by
        intro p hp
        rw [Subgroup.card_map_of_injective
          (MulAut.conj r).injective] at hp
        exact hBetaMN hp
      exact
        { centralizer_sdprod := hCentSd
          centralizer_disjoint :=
            internalSemidirectProduct_inf_eq_bot hCentSd
          tau2_subset_sigma := hTauSigma
          beta_control := hBeta
          hall_intersection := hHall }
    exact
      { basic :=
          { R_le_centralizer := hR₀le
            R_normal := hR₀normal
            R_hall := hR₀Hall
            transitive := hTransR₀
            card_eq := hCardR₀ }
        small_signalizer := fun hnotLarge ↦ (hnotLarge hlarge).elim
        large := fun _ ↦
          { centralizer_maximal := hCentUnique
            signalizer_ne_bot := hR₀ne
            x_tau2 := hxTau2
            base_maximal := hN₀max
            centralizer_le_base := hCxN₀
            base_type := hNtype
            overgroup_context := hLocal } }

end

end Submission.OddOrder.BG.Section14
