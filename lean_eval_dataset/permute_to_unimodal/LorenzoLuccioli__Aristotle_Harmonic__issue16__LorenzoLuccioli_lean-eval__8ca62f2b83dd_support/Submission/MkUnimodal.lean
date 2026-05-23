import Mathlib
import ChallengeDeps

/-!
# mkUnimodal: construct a unimodal permutation from a subset S ⊆ Fin n
-/

namespace Submission.MkUnimodal

open LeanEval.ProgramVerification

/-- For any S ⊆ Fin n, define a unimodal permutation.
    inc = sorted values from S (+1), dec = reverse sorted values from complement. -/
noncomputable def mkUnimodal (n : Nat) (S : Finset (Fin n)) : List Nat :=
  let inc := (S.sort (· ≤ ·)).map (fun i => i.val + 1)
  let dec := ((Finset.univ \ S).sort (· ≤ ·)).map (fun i => i.val + 1) |>.reverse
  inc ++ dec

lemma mkUnimodal_size (n : Nat) (S : Finset (Fin n)) :
    (mkUnimodal n S).length = n := by
  simp [mkUnimodal, List.length_append]
  rw [ Finset.card_sdiff ] ; simp +decide [ Finset.card_univ ];
  exact Nat.add_sub_of_le ( le_trans ( Finset.card_le_univ _ ) ( by norm_num ) )

lemma mkUnimodal_unimodal (n : Nat) (S : Finset (Fin n)) :
    Unimodal (mkUnimodal n S).toArray := by
  refine' ⟨ _, _, _, _, _ ⟩;
  exact S.sort ( · ≤ · ) |>.map ( fun i => i.val + 1 ) |>.toArray;
  exact ( ( Finset.univ \ S ).sort ( · ≤ · ) |> List.map ( fun i => i.val + 1 ) |> List.reverse ) |> List.toArray;
  · unfold mkUnimodal; aesop;
  · simp +decide [ List.pairwise_map, List.pairwise_iff_get ];
    intro i j hij;
    have := List.pairwise_iff_get.mp ( show List.Pairwise ( fun x y => x < y ) ( S.sort fun x1 x2 => x1 ≤ x2 ) from ?_ );
    · convert this ⟨ i, by simpa using i.2 ⟩ ⟨ j, by simpa using j.2 ⟩ hij;
    · convert S.sortedLT_sort using 1;
      grind;
  · simp +decide [ List.pairwise_reverse, List.pairwise_map ];
    convert Finset.sort_sorted_lt _ using 1;
    all_goals try exact Fin n;
    convert Iff.rfl;
    grind

lemma mkUnimodal_perm (n : Nat) (S : Finset (Fin n)) :
    (mkUnimodal n S).toArray.Perm (1...=n).toArray := by
  have h_perm : (mkUnimodal n S).toArray.Perm ((Finset.univ : Finset (Fin n)).toList.map (fun i => i.val + 1)).toArray := by
    have h_perm : List.Perm (S.sort (· ≤ ·) ++ ((Finset.univ \ S).sort (· ≤ ·)).reverse) (Finset.univ : Finset (Fin n)).toList := by
      rw [ List.perm_iff_count ];
      intro a; by_cases ha : a ∈ S <;> simp_all +decide [ List.Nodup.count, Finset.nodup_toList ] ;
    convert h_perm.map ( fun i : Fin n => i.val + 1 ) |> List.Perm.toArray using 1;
    unfold mkUnimodal; aesop;
  refine h_perm.trans ?_;
  convert List.Perm.map _ ?_ using 1;
  convert Array.perm_iff_toList_perm;
  rotate_left;
  exact List.finRange n;
  · rw [ ← Multiset.coe_eq_coe ] ; aesop;
  · refine' List.ext_get _ _ <;> simp +decide [ List.finRange_succ ];
    exact fun _ _ => add_comm _ _

end Submission.MkUnimodal
