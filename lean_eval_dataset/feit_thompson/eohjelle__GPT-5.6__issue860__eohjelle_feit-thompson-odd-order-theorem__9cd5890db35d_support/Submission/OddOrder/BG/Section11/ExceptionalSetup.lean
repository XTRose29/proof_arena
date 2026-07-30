import Submission.OddOrder.BG.Section10.MaximalCoreFacts
import Submission.OddOrder.MathlibSupport.ElementaryAbelianFunctorial
import Submission.OddOrder.MathlibSupport.PMaxElem
import Submission.OddOrder.MathlibSupport.SubgroupCardinality

/-!
# Bender--Glauberman Section 11: exceptional maximal subgroups

This file ports the opening setup of `BGsection11.v`, through
`exceptional_pmaxElem`.  As elsewhere in this port, the numerical assertion
that the `p`-rank is exactly two is stated by exhibiting rank two and
excluding every elementary-abelian subgroup of cardinal rank three.
-/

namespace Submission.OddOrder.BG.Section11

open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative

universe u

/-- `BGsection11.v: exceptional_FTmaximal` (Hypothesis 11.1).

The two elementary-abelian membership conditions have been expanded into
their containment and cardinal-rank components.  Primality is recorded
explicitly: in MathComp it is implicit in membership in `'E_p^2(M)`. -/
structure exceptional_FTmaximal
    {G : Type u} [Group G]
    (p : ℕ) (M A₀ A : Subgroup G) : Prop where
  prime : p.Prime
  sigma_compl : p ∉ sigmaPrimes M
  A_le : A ≤ M
  A_rank_two : IsElementaryAbelianOfRank p 2 A
  A₀_le : A₀ ≤ A
  A₀_rank_one : IsElementaryAbelianOfRank p 1 A₀
  normalizer_A₀_le : Subgroup.normalizer (A₀ : Set G) ≤ M

/-- `BGsection11.v: sigma'_Sylow_contra`.

For a prime outside `sigma(M)`, the ambient normalizer of a Sylow subgroup
of `M` cannot be contained in `M`. -/
theorem sigma'_Sylow_contra
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) {M : Subgroup G} (P : Sylow p M)
    (hpSigma : p ∉ sigmaPrimes M) :
    ¬ Subgroup.normalizer (ambientSylow M P : Set G) ≤ M := by
  intro hnormalizer
  exact hpSigma ⟨hp, P, hnormalizer⟩

/-- `BGsection11.v: p_rank_exceptional`.

This is the exact cardinal-rank form of `r_p(M) = 2`: `M` contains an
elementary-abelian subgroup of rank two and contains none of rank three. -/
theorem p_rank_exceptional
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} {M A₀ A : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hExc : exceptional_FTmaximal p M A₀ A) :
    HasElementaryAbelianRankAtLeast p 2 M ∧
      ¬ HasElementaryAbelianRankAtLeast p 3 M := by
  constructor
  · exact ⟨A, hExc.A_le, hExc.A_rank_two⟩
  · intro hRankThree
    apply hExc.sigma_compl
    exact alpha_sub_sigma hM ⟨hExc.prime, hRankThree⟩

/-- A proper elementary-abelian overgroup of a rank-two subgroup contains
an elementary-abelian subgroup of rank three. -/
private theorem exists_rank_three_of_rank_two_lt
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {A E : Subgroup G}
    (hA : IsElementaryAbelianOfRank p 2 A)
    (hE : IsElementaryAbelianGroup p E) (hAE : A < E) :
    ∃ F : Subgroup G, F ≤ E ∧ IsElementaryAbelianOfRank p 3 F := by
  obtain ⟨n, hEcard⟩ := hE.isPGroup.exists_card_eq
  have hpowlt : p ^ 2 < p ^ n := by
    simpa only [hA.card_eq, hEcard] using
      natCard_subgroup_lt_of_lt hAE
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

/-- `BGsection11.v: exceptional_pmaxElem` (the third preliminary remark).

The chosen rank-two subgroup is maximal elementary abelian in the whole
minimal counterexample. -/
theorem exceptional_pmaxElem
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} {M A₀ A : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hExc : exceptional_FTmaximal p M A₀ A)
    (P : Sylow p M) (_hAP : A ≤ ambientSylow M P) :
    IsPMaxElem p (⊤ : Subgroup G) A := by
  letI : Fact p.Prime := ⟨hExc.prime⟩
  have hNoRankThree :
      ¬ HasElementaryAbelianRankAtLeast p 3 M :=
    (p_rank_exceptional hM hExc).2
  refine ⟨⟨le_top, hExc.A_rank_two.toIsElementaryAbelianGroup⟩, ?_⟩
  intro E hE hAE
  apply le_antisymm
  · by_contra hnotEA
    have hAElt : A < E :=
      lt_of_le_of_ne hAE (fun hEq ↦ hnotEA hEq.ge)
    have hEcentral : E ≤ Subgroup.centralizer (A₀ : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      letI : IsMulCommutative E := hE.2.commutative
      exact congrArg Subtype.val
        (mul_comm (⟨y, hAE (hExc.A₀_le hy)⟩ : E) ⟨x, hx⟩)
    have hEM : E ≤ M :=
      hEcentral.trans
        ((Subgroup.centralizer_le_normalizer (A₀ : Set G)).trans
          hExc.normalizer_A₀_le)
    obtain ⟨F, hFE, hF⟩ :=
      exists_rank_three_of_rank_two_lt
        hExc.A_rank_two hE.2 hAElt
    exact hNoRankThree ⟨F, hFE.trans hEM, hF⟩
  · exact hAE

end Submission.OddOrder.BG.Section11
