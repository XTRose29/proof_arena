import Submission.OddOrder.MathlibSupport.Cardinality
import Submission.OddOrder.MathlibSupport.NormalElementaryAbelianRankTwo
import Submission.OddOrder.MathlibSupport.OmegaOneFunctorial
import Submission.OddOrder.MathlibSupport.OmegaOneSmallNilpotency

/-!
The first omega subgroup of the second upper-center in an odd `p`-group.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

theorem omegaOne_upperCentralSeries_two_not_isCyclic_of_normal_rank_two
    (hG : IsPGroup p G) (S : Subgroup G) [S.Normal]
    (hS : IsElementaryAbelianOfRank p 2 S) :
    ¬ IsCyclic (omegaOne p (Subgroup.upperCentralSeries G 2)) := by
  let Z2 := Subgroup.upperCentralSeries G 2
  have hSZ2 : S ≤ Z2 :=
    normal_elementaryAbelian_rank_two_le_upperCentralSeries_two hG S hS
  let S2 : Subgroup Z2 := S.subgroupOf Z2
  have hS2pow : ∀ x : S2, x ^ p = 1 := by
    intro x
    have hxG : ((x : G) ^ p) = 1 :=
      congrArg (fun z : S ↦ (z : G))
        (hS.pow_eq_one ⟨(x : G), x.2⟩)
    apply Subtype.ext
    apply Subtype.ext
    exact hxG
  have hS2le : S2 ≤ omegaOne p Z2 := by
    intro x hx
    apply mem_omegaOne_of_pow_eq_one
    have hxG : ((x : G) ^ p) = 1 :=
      congrArg (fun z : S ↦ (z : G))
        (hS.pow_eq_one ⟨(x : G), hx⟩)
    apply Subtype.ext
    exact hxG
  have hS2card : Nat.card S2 = p ^ 2 := by
    exact (natCard_subgroupOf_eq hSZ2).trans hS.card_eq
  intro hcyclic
  letI : IsCyclic (omegaOne p Z2) := hcyclic
  letI : IsCyclic S2 := Subgroup.isCyclic_of_le hS2le
  exact (not_isCyclic_of_card_prime_sq_of_pow_eq_one
    Fact.out hS2card hS2pow) inferInstance

/-- Conditional form of Bender-Glauberman Lemma 4.5(c): the normal
elementary abelian rank-two subgroup is the output of part (a). -/
theorem omegaOne_upperCentralSeries_two_structure_of_normal_rank_two
    (hG : IsPGroup p G) (hodd : Odd (Nat.card G))
    (S : Subgroup G) [S.Normal]
    (hS : IsElementaryAbelianOfRank p 2 S) :
    ¬ IsCyclic (omegaOne p (Subgroup.upperCentralSeries G 2)) ∧
      Monoid.exponent (omegaOne p (Subgroup.upperCentralSeries G 2)) ∣ p := by
  have hoddS : Odd (Nat.card S) := odd_natCard_subgroup S hodd
  have hoddPow : Odd (p ^ 2) := hS.card_eq ▸ hoddS
  have hpodd : Odd p :=
    (Nat.odd_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp hoddPow
  let Z2 := Subgroup.upperCentralSeries G 2
  have hpZ2 : IsPGroup p Z2 := hG.to_subgroup Z2
  have hclass2 : Group.nilpotencyClass Z2 ≤ 2 := by
    simpa [Z2] using
      (nilpotencyClass_upperCentralSeries_two_le (G := G))
  have hclass : Group.nilpotencyClass Z2 ≤ if 3 < p then 3 else 2 := by
    by_cases hp3 : 3 < p
    · rw [if_pos hp3]
      omega
    · rw [if_neg hp3]
      exact hclass2
  have hpow : ∀ z : Z2, z ∈ omegaOne p Z2 → z ^ p = 1 :=
    omegaOne_pow_eq_one_of_small_nilpotencyClass
      p Fact.out hpodd hpZ2 hclass
  refine ⟨omegaOne_upperCentralSeries_two_not_isCyclic_of_normal_rank_two
    hG S hS, ?_⟩
  exact exponent_omegaOne_dvd p (fun z ↦ hpow z z.2)

end Submission.OddOrder.MathlibSupport
