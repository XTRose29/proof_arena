import Submission.OddOrder.BG.Section05.OmegaUpperCentralIndex

/-!
Bender--Glauberman Lemma 5.2.
-/

namespace Submission.OddOrder.BG.Section05

open Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- `BGsection5.v: Ohm1_ucn_p2maxElem` (Bender--Glauberman Lemma 5.2).

Here `Z`, `W`, and `T` are expanded respectively as the mapped subgroups
`Ω₁(Z(G))`, `Ω₁(Z₂(G))`, and `C_G(W)`. -/
theorem Ohm1_ucn_p2maxElem
    (hG : IsPGroup p G) (hodd : Odd (Nat.card G))
    (hRank3 : ∃ A : Subgroup G, IsElementaryAbelianOfRank p 3 A)
    {E : Subgroup G} (hE : IsElementaryAbelianOfRank p 2 E)
    (hmax : IsPMaxElem p (⊤ : Subgroup G) E) :
    ¬ E ≤ omegaUpperCentralTwoCentralizer p G ∧
      Nat.card (omegaOneCenter p G) = p ∧
      IsElementaryAbelianOfRank p 2 (omegaOneUpperCentralTwo p G) ∧
      (omegaUpperCentralTwoCentralizer p G).Characteristic ∧
      (omegaUpperCentralTwoCentralizer p G).index = p := by
  refine ⟨
    not_le_omegaUpperCentralTwoCentralizer hG hodd hRank3 hE hmax,
    omegaOneCenter_card_eq_prime_of_rank_three_pmaxElem
      hG hRank3 hE hmax,
    omegaOneUpperCentralTwo_isElementaryAbelianOfRank_two
      hG hodd hRank3 hE hmax,
    ?_,
    omegaUpperCentralTwoCentralizer_index_eq_prime
      hG hodd hRank3 hE hmax⟩
  infer_instance

end Submission.OddOrder.BG.Section05
