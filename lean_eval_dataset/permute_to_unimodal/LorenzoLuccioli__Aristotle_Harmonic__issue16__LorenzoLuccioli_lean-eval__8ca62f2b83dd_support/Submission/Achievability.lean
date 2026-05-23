import Mathlib
import ChallengeDeps
import Submission.LisComplete
import Submission.LisSound
import Submission.Bridge
import Submission.LowerBound
import Submission.FillLemma
import Submission.MkUnimodal
import Submission.AchievabilityGlue
import Submission.NdsAssembly

/-!
# Achievability: there exists a unimodal permutation with ≤ minRearrange differences
-/

namespace Submission.Achievability

open LeanEval.ProgramVerification
open Submission.LowerBound (encodedSeq)
open Submission.MkUnimodal

/-- Key lemma: there exists S such that mkUnimodal n S has enough agreements with arr -/
lemma exists_good_split {n : Nat} (arr : Array Nat)
    (harr : arr.Perm (1...=n).toArray) (harr_size : arr.size = n) :
    ∃ S : Finset (Fin n),
      ((List.finRange n).filter (fun i =>
        (mkUnimodal n S).toArray[i.val]'(by simp [List.toArray, mkUnimodal_size]) =
        arr[i.val]'(by omega))).length ≥
      LisSound.lis (encodedSeq arr) :=
  NdsAssembly.exists_good_split arr harr harr_size

/-
The achievability theorem
-/
theorem achievability {arr : Array Nat}
    (harr : arr.Perm (1...=arr.size).toArray) :
    ∃ (x : Array Nat) (hx : x.Perm (1...=arr.size).toArray),
      Unimodal x ∧ differences (Vector.mk x (by simpa using hx.size_eq)) arr.toVector ≤ minRearrange arr := by
  obtain ⟨ S, hS ⟩ := exists_good_split arr harr rfl;
  refine' ⟨ ( mkUnimodal arr.size S ).toArray, _, _, _ ⟩;
  all_goals generalize_proofs at *;
  · grind +suggestions;
  · exact mkUnimodal_unimodal _ _;
  · have := @Submission.LowerBound.agreements_plus_differences arr.size ( Vector.mk ( mkUnimodal arr.size S ).toArray ‹_› ) arr.toVector;
    have := @Submission.Bridge.lis_eq ( encodedSeq arr ) ; simp_all +decide [ Submission.LowerBound.minRearrange_eq ] ;
    exact le_tsub_of_add_le_left ( by linarith )

end Submission.Achievability
