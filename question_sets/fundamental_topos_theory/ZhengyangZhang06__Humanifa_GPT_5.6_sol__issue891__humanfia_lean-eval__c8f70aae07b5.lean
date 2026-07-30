import ChallengeDeps
import Submission.SlicePowers

open LeanEval.ToposTheory
open _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace Submission

theorem fundamental_topos_theory {E : Type*} [Category E]
    (hE : IsTopos E) (X : E) : IsTopos (Over X) := by
  rcases hE with ⟨hfinite, cm, hclosed, hclassifier⟩
  letI : HasFiniteLimits E := hfinite
  letI : CartesianMonoidalCategory E := cm
  letI : MonoidalClosed E := hclosed.some
  letI : HasSubobjectClassifier E := hclassifier
  letI : Power.HasPowers E := Power.closedHasPowers
  letI : HasSubobjectClassifier (Over X) := SlicePowers.overHasSubobjectClassifier X
  letI : Power.HasPowers (Over X) := SlicePowers.overHasPowers X
  refine ⟨inferInstance, ?_⟩
  let cmOver := Over.cartesianMonoidalCategory X
  refine ⟨cmOver, ?_, inferInstance⟩
  letI : CartesianMonoidalCategory (Over X) := cmOver
  exact ⟨Exponentials.monoidalClosed⟩

end Submission
