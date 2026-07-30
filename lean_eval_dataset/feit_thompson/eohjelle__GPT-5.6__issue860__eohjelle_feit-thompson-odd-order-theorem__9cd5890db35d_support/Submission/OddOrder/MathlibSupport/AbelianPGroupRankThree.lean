import Submission.OddOrder.MathlibSupport.ElementaryAbelianFunctorial
import Submission.OddOrder.MathlibSupport.HuppertAbelian
import Submission.OddOrder.MathlibSupport.MetacyclicRank

/-!
Extracting an elementary-abelian subgroup of rank three from a commutative
finite `p`-group of group rank at least three.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative

universe u

/-- A commutative finite `p`-subgroup of group rank at least three contains
an elementary-abelian subgroup of cardinal rank three. -/
theorem exists_elementaryAbelian_rank_three_le_of_group_rank
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (A : Subgroup G)
    (hAp : IsPGroup p A)
    (hAcomm : IsMulCommutative A)
    (hRank : 3 ≤ Group.rank A) :
    ∃ E : Subgroup G,
      E ≤ A ∧ IsElementaryAbelianOfRank p 3 E := by
  classical
  letI : IsMulCommutative A := hAcomm
  have hNotMetacyclic : ¬ IsMetacyclic A := by
    intro hMetacyclic
    have hRankLe : Group.rank A ≤ 2 :=
      rank_le_two_of_isMetacyclic hMetacyclic
    omega
  have hOmegaCard : p ^ 2 < Nat.card (omegaOne p A) := by
    by_contra hnot
    have hle : Nat.card (omegaOne p A) ≤ p ^ 2 :=
      Nat.le_of_not_gt hnot
    exact hNotMetacyclic
      (isMetacyclic_of_isMulCommutative_of_omegaOne_card_le_prime_sq
        hAp hle)
  have hOmegaP : IsPGroup p (omegaOne p A) :=
    omegaOne_isPGroup p hAp
  obtain ⟨n, hOmegaCardPow⟩ := hOmegaP.exists_card_eq
  have hn : 3 ≤ n := by
    have hpows : p ^ 2 < p ^ n := by
      simpa only [hOmegaCardPow] using hOmegaCard
    have : 2 < n :=
      (Nat.pow_lt_pow_iff_right (Fact.out : p.Prime).one_lt).mp hpows
    omega
  have hthreele : p ^ 3 ≤ Nat.card (omegaOne p A) := by
    rw [hOmegaCardPow]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hn
  obtain ⟨E₀, hE₀Omega, hE₀card⟩ :=
    Sylow.exists_subgroup_le_card_pow_prime_of_le_card
      (G := A) (Fact.out : p.Prime) hAp hthreele
  have hE₀pow : ∀ x : E₀, x ^ p = 1 := by
    intro x
    apply Subtype.ext
    have hxker : (x : A) ∈ (powMonoidHom p : A →* A).ker := by
      rw [← omegaOne_eq_powMonoidHom_ker]
      exact hE₀Omega x.property
    simpa using MonoidHom.mem_ker.mp hxker
  have hE₀ : IsElementaryAbelianOfRank p 3 E₀ :=
    { isPGroup := hAp.to_subgroup E₀
      commutative := by infer_instance
      pow_eq_one := hE₀pow
      card_eq := hE₀card }
  let E : Subgroup G := E₀.map A.subtype
  refine ⟨E, ?_, ?_⟩
  · exact Subgroup.map_subtype_le E₀
  · exact hE₀.map_of_injective A.subtype A.subtype_injective

end Submission.OddOrder.MathlibSupport
