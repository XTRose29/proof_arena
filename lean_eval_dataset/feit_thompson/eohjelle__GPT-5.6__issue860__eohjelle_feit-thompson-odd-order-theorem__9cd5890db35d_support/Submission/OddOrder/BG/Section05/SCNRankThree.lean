import Submission.OddOrder.BG.Section04.SCNRankThreeEmpty
import Submission.OddOrder.BG.Section05.NarrowMaximalElementary

/-!
Bender--Glauberman Lemma 5.1(a).
-/

namespace Submission.OddOrder.BG.Section05

open Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- `BGsection5.v: rank3_SCN3` (Bender--Glauberman Lemma 5.1(a)). -/
theorem rank3_SCN3 (hG : IsPGroup p G) (hodd : Odd (Nat.card G))
    (hRank3 : ∃ E : Subgroup G, IsElementaryAbelianOfRank p 3 E) :
    ∃ B : Subgroup G,
      Submission.OddOrder.BG.Section04.IsSCNAtLeastRank p 3 B := by
  by_contra hNoSCN
  have hNoRank3 :
      ¬ ∃ E : Subgroup G, IsElementaryAbelianOfRank p 3 E :=
    (Submission.OddOrder.BG.Section04.rank2_SCN3_empty hG hodd).mpr
      hNoSCN
  exact hNoRank3 hRank3

end Submission.OddOrder.BG.Section05
