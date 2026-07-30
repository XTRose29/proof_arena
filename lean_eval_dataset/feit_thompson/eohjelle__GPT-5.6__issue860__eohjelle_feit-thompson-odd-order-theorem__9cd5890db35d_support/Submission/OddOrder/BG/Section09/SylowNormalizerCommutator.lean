import Mathlib.GroupTheory.Transfer
import Submission.OddOrder.BG.Section07.MinimalCounterexample

/-!
# Bender--Glauberman Section 9: Sylow-normalizer commutator

This is the nontriviality step for the subgroup denoted
`[~: P, 'N(P)]` in `BGsection9.v`.  If this commutator were trivial,
Burnside transfer would give a normal `p`-complement.  Simplicity forces
that complement to be trivial or the whole group, and both alternatives
contradict the hypotheses on the Sylow subgroup.
-/

namespace Submission.OddOrder.BG.Section09

open Submission.OddOrder.BG.Section07

universe u

/-- The commutator of a nontrivial Sylow subgroup with its ambient
normalizer is nontrivial in a minimal simple odd-order group. -/
theorem sylow_commutator_normalizer_ne_bot
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G)
    (hPne : (P : Subgroup G) ≠ ⊥) :
    ⁅(P : Subgroup G),
      Subgroup.normalizer ((P : Subgroup G) : Set G)⁆ ≠ ⊥ := by
  intro hcomm
  have hP_centralizes_normalizer :
      (P : Subgroup G) ≤
        Subgroup.centralizer
          (Subgroup.normalizer ((P : Subgroup G) : Set G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hnormalizer_centralizes_P :
      Subgroup.normalizer ((P : Subgroup G) : Set G) ≤
        Subgroup.centralizer ((P : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mp hP_centralizes_normalizer
  let K : Subgroup G :=
    (MonoidHom.transferSylow P hnormalizer_centralizes_P).ker
  have hKcomp : K.IsComplement' (P : Subgroup G) :=
    MonoidHom.ker_transferSylow_isComplement'
      P hnormalizer_centralizes_P
  have hKnormal : K.Normal := by
    dsimp only [K]
    infer_instance
  rcases hKnormal.eq_bot_or_eq_top with hKbot | hKtop
  · have hPtop : (P : Subgroup G) = ⊤ := by
      simpa only [hKbot, bot_sup_eq] using hKcomp.sup_eq_top
    exact (mFT_pgroup_proper (P : Subgroup G) P.isPGroup').ne hPtop
  · apply hPne
    simpa only [hKtop, top_inf_eq] using
      (disjoint_iff.mp hKcomp.disjoint)

end Submission.OddOrder.BG.Section09
