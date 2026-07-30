import Submission.OddOrder.BG.Section04.NormalRankTwo
import Submission.OddOrder.MathlibSupport.UpperCentralOmegaOne

/-!
Bender--Glauberman Lemma 4.5(c), together with the reusable structural core
that accepts the normal rank-two subgroup from part (a) explicitly.
-/

namespace Submission.OddOrder.BG.Section04

open Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- `BGsection4.v: Ohm1_odd_ucn2`, with the normal rank-two subgroup from
part (a) made explicit. -/
theorem Ohm1_odd_ucn2_of_normal_p2Elem
    (hG : IsPGroup p G) (hodd : Odd (Nat.card G))
    (S : Subgroup G) [S.Normal]
    (hS : IsElementaryAbelianOfRank p 2 S) :
    ¬ IsCyclic (omegaOne p (Subgroup.upperCentralSeries G 2)) ∧
      Monoid.exponent (omegaOne p (Subgroup.upperCentralSeries G 2)) ∣ p :=
  omegaOne_upperCentralSeries_two_structure_of_normal_rank_two
    hG hodd S hS

/-- `BGsection4.v: Ohm1_odd_ucn2` (Bender--Glauberman Lemma 4.5(c)). -/
theorem Ohm1_odd_ucn2
    (hG : IsPGroup p G) (hodd : Odd (Nat.card G))
    (hncyc : ¬ IsCyclic G) :
    ¬ IsCyclic (omegaOne p (Subgroup.upperCentralSeries G 2)) ∧
      Monoid.exponent (omegaOne p (Subgroup.upperCentralSeries G 2)) ∣ p := by
  obtain ⟨S, hSnormal, hS⟩ := ex_odd_normal_p2Elem hG hodd hncyc
  letI : S.Normal := hSnormal
  exact Ohm1_odd_ucn2_of_normal_p2Elem hG hodd S hS

end Submission.OddOrder.BG.Section04
