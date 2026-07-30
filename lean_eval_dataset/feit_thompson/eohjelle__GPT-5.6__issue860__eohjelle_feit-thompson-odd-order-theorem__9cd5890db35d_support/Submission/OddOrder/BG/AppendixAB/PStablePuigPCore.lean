import Submission.OddOrder.BG.AppendixAB.PStableConstrained
import Submission.OddOrder.BG.AppendixAB.PuigPCore

/-!
The p-stable form of Bender-Glauberman Lemma B.3.
-/

namespace Submission.OddOrder.BG.AppendixAB

open Submission.OddOrder.BG.Section01
open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G]

theorem pCore_sylow_puig_sub_of_isPStable {p : ℕ} [Fact p.Prime]
    [IsSolvable G] (S : Sylow p G) (hstable : IsPStable p G)
    (hprimeCore : pPrimeCore p G = ⊥) :
    puigInf (S : Subgroup G) ≤ puigInf (pCore p G) ∧
      puig (pCore p G) ≤ puig (S : Subgroup G) :=
  pCore_sylow_puig_sub_of_constrained S
    (abelianGeneratedConstrained_of_isPStable hstable) hprimeCore

end Submission.OddOrder.BG.AppendixAB
