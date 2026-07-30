import Submission.OddOrder.BG.Section04.SCNRankThreeEmpty
import Submission.OddOrder.MathlibSupport.ElementaryAbelianFunctorial
import Submission.OddOrder.MathlibSupport.RankTwoCentralizerIndex
import Submission.OddOrder.MathlibSupport.SubgroupCardinality

/-!
# Elementary-abelian rank in a centralizer

If a finite `p`-group contains a normal elementary-abelian subgroup of rank
two and an elementary-abelian subgroup of rank three, then the centralizer of
the former inside the latter has elementary-abelian rank at least two.
-/

namespace Submission.OddOrder.MathlibSupport

open Submission.OddOrder.BG.Section04
open scoped IsMulCommutative

universe u

/-- A rank-three elementary-abelian subgroup contains a rank-two subgroup
centralizing any normal rank-two elementary-abelian subgroup of the ambient
finite `p`-group. -/
theorem hasElementaryAbelianRankAtLeast_two_centralizerWithin
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {P D E : Subgroup G}
    (hP : IsPGroup p P)
    (hEP : E ≤ P)
    (hDP : D ≤ P)
    (hDnormal : (D.subgroupOf P).Normal)
    (hD : IsElementaryAbelianOfRank p 2 D)
    (hE : IsElementaryAbelianOfRank p 3 E) :
    HasElementaryAbelianRankAtLeast p 2
      (centralizerWithin E D) := by
  classical
  let C : Subgroup G := centralizerWithin E D
  let Cₚ : Subgroup G := centralizerWithin P D

  have hC_eq : C = E ⊓ Cₚ := by
    ext x
    simp only [C, Cₚ, centralizerWithin, Subgroup.mem_inf]
    constructor
    · rintro ⟨hxE, hxD⟩
      exact ⟨hxE, hEP hxE, hxD⟩
    · rintro ⟨hxE, _hxP, hxD⟩
      exact ⟨hxE, hxD⟩

  have hCₚ_index : Cₚ.relIndex P ≤ p := by
    exact centralizerWithin_relIndex_le_prime_of_normal_rank_two
      hP hDP hDnormal hD
  have hCₚ_index_ne : Cₚ.relIndex P ≠ 0 := by
    change Nat.card (P ⧸ Cₚ.subgroupOf P) ≠ 0
    exact Nat.card_pos.ne'
  have hCₚ_index_E : Cₚ.relIndex E ≤ Cₚ.relIndex P :=
    Subgroup.relIndex_le_of_le_right hEP hCₚ_index_ne
  have hC_index : C.relIndex E ≤ p := by
    calc
      C.relIndex E = (E ⊓ Cₚ).relIndex E := by rw [hC_eq]
      _ = Cₚ.relIndex E := Subgroup.inf_relIndex_left E Cₚ
      _ ≤ Cₚ.relIndex P := hCₚ_index_E
      _ ≤ p := hCₚ_index

  have hCE : C ≤ E := by
    simpa only [C] using centralizerWithin_le_left E D
  have hcard_mul : Nat.card C * C.relIndex E = Nat.card E := by
    change Nat.card C * (C.subgroupOf E).index = Nat.card E
    rw [← natCard_subgroupOf_eq hCE]
    exact (C.subgroupOf E).card_mul_index
  have hcard_product : p ^ 3 ≤ Nat.card C * p := by
    calc
      p ^ 3 = Nat.card E := hE.card_eq.symm
      _ = Nat.card C * C.relIndex E := hcard_mul.symm
      _ ≤ Nat.card C * p := Nat.mul_le_mul_left _ hC_index
  have hcardC : p ^ 2 ≤ Nat.card C := by
    apply Nat.le_of_mul_le_mul_right _ (Fact.out : p.Prime).pos
    simpa only [pow_succ] using hcard_product

  have hCP : C ≤ P := hCE.trans hEP
  let CP : Subgroup P := C.subgroupOf P
  have hcardCP : p ^ 2 ≤ Nat.card CP := by
    change p ^ 2 ≤ Nat.card (C.subgroupOf P)
    rwa [natCard_subgroupOf_eq hCP]
  obtain ⟨F₀, hF₀CP, hF₀card⟩ :=
    Sylow.exists_subgroup_le_card_pow_prime_of_le_card
      (G := P) (Fact.out : p.Prime) hP hcardCP
  have hF₀E : ∀ x : F₀, ((x : P) : G) ∈ E := by
    intro x
    exact hCE (hF₀CP x.2)
  have hF₀ : IsElementaryAbelianOfRank p 2 F₀ := by
    refine
    { isPGroup := hP.to_subgroup F₀
      commutative := ?_
      pow_eq_one := ?_
      card_eq := hF₀card }
    · letI : IsMulCommutative E := hE.commutative
      apply isMulCommutative_iff.mpr
      intro x y
      apply Subtype.ext
      apply P.subtype_injective
      exact congrArg (fun z : E ↦ (z : G))
        (mul_comm (⟨x, hF₀E x⟩ : E) ⟨y, hF₀E y⟩)
    · intro x
      apply Subtype.ext
      apply P.subtype_injective
      exact congrArg (fun z : E ↦ (z : G))
        (hE.pow_eq_one ⟨x, hF₀E x⟩)

  let F : Subgroup G := F₀.map P.subtype
  have hFC : F ≤ C := by
    rintro x ⟨y, hy, rfl⟩
    exact hF₀CP hy
  refine ⟨F, hFC, ?_⟩
  exact hF₀.map_of_injective P.subtype P.subtype_injective

end Submission.OddOrder.MathlibSupport
