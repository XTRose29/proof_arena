import Submission.OddOrder.PF.Section02.DadeExpansionRestriction

/-!
# Orbit stabilizers in the Dade expansion

The conjugation stabilizer in `L` of a nonempty Dade subset `B` is the
complement factor `L ⊓ normalizer B` in its set normalizer.  This file
packages that identification as a multiplicative equivalence and records the
cardinality equalities used when averaging the expansion over `L`-orbits.
-/

namespace Submission.OddOrder.PF

noncomputable section

universe u v

variable {Γ : Type u} [Group Γ]

private theorem Dade_set_complement_subgroupOf_eq_stabilizer
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (B : DadeSubset A) :
    letI : MulAction L (DadeSubset A) :=
      dadeSubsetConjugationAction ddA
    (DadeSetComplement ddA B).subgroupOf L =
      MulAction.stabilizer L B := by
  letI : MulAction L (DadeSubset A) :=
    dadeSubsetConjugationAction ddA
  ext x
  rw [MulAction.mem_stabilizer_iff]
  change (x : Γ) ∈ L ⊓ Subgroup.normalizer (B : Set Γ) ↔ x • B = B
  rw [Subgroup.mem_inf]
  simp only [x.property, true_and]
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  constructor
  · intro hx
    apply Subtype.ext
    simpa only [coe_dadeSubset_smul ddA] using hx
  · intro hx
    have hsets := congrArg (fun C : DadeSubset A => (C : Set Γ)) hx
    simpa only [coe_dadeSubset_smul ddA] using hsets

/-- The stabilizer in `L` of a Dade subset is multiplicatively equivalent to
the complement factor `L ⊓ normalizer B` in its set normalizer. -/
noncomputable def DadeSetComplementEquivStabilizer
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (B : DadeSubset A) :
    letI : MulAction L (DadeSubset A) :=
      dadeSubsetConjugationAction ddA
    DadeSetComplement ddA B ≃* MulAction.stabilizer L B := by
  letI : MulAction L (DadeSubset A) :=
    dadeSubsetConjugationAction ddA
  exact
    (Subgroup.subgroupOfEquivOfLe (H := DadeSetComplement ddA B)
        inf_le_left).symm.trans
      (MulEquiv.subgroupCongr
        (Dade_set_complement_subgroupOf_eq_stabilizer ddA B))

/-- The action stabilizer and the complement factor have the same cardinality. -/
theorem natCard_DadeSubset_stabilizer_eq_complement
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (B : DadeSubset A) :
    letI : MulAction L (DadeSubset A) :=
      dadeSubsetConjugationAction ddA
    Nat.card (MulAction.stabilizer L B) =
      Nat.card (DadeSetComplement ddA B) := by
  letI : MulAction L (DadeSubset A) :=
    dadeSubsetConjugationAction ddA
  exact Nat.card_congr (DadeSetComplementEquivStabilizer ddA B).toEquiv |>.symm

/-- Cast form of `natCard_DadeSubset_stabilizer_eq_complement`, for the
coefficient field in the orbit-average calculation. -/
theorem natCast_card_DadeSubset_stabilizer_eq_complement
    {G L : Subgroup Γ} {A : Set Γ}
    {k : Type v} [Semiring k]
    (ddA : DadeHypothesis G L A) (B : DadeSubset A) :
    letI : MulAction L (DadeSubset A) :=
      dadeSubsetConjugationAction ddA
    (Nat.card (MulAction.stabilizer L B) : k) =
      (Nat.card (DadeSetComplement ddA B) : k) := by
  letI : MulAction L (DadeSubset A) :=
    dadeSubsetConjugationAction ddA
  rw [natCard_DadeSubset_stabilizer_eq_complement ddA B]

end

end Submission.OddOrder.PF
