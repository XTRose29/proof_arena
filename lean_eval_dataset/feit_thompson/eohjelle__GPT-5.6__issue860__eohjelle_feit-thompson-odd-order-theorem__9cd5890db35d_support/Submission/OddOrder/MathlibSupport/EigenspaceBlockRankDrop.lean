import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic
import Submission.OddOrder.MathlibSupport.IndependentSubmoduleFinrank

/-!
Tight rank sums for a scalar line and equal-rank eigenspace blocks.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped BigOperators

universe u v w

/-- If a finite rank profile has lower bound `c` everywhere, lower bound
`c + 1` at one distinguished index, and the corresponding tight total,
then every lower bound is an equality. -/
theorem eq_of_tight_rank_sum
    {I : Type u} [Fintype I] [DecidableEq I]
    (rank : I -> Nat) (i0 : I) (c : Nat)
    (htotal : ∑ i : I, rank i = Fintype.card I * c + 1)
    (hlower : ∀ i : I, c ≤ rank i)
    (hlower0 : c + 1 ≤ rank i0) :
    rank i0 = c + 1 ∧ ∀ i : I, i ≠ i0 -> rank i = c := by
  let S : Finset I := Finset.univ.erase i0
  have hcard : 1 ≤ Fintype.card I :=
    Fintype.card_pos_iff.mpr ⟨i0⟩
  have hScard : S.card = Fintype.card I - 1 := by
    simp [S]
  have hsplit : ∑ i : I, rank i = rank i0 + ∑ i ∈ S, rank i := by
    rw [← Finset.sum_erase_add Finset.univ rank (Finset.mem_univ i0)]
    simp [S, add_comm]
  have hrest_lower : S.card * c ≤ ∑ i ∈ S, rank i := by
    calc
      S.card * c = ∑ _i ∈ S, c := by simp
      _ ≤ ∑ i ∈ S, rank i := by
        exact Finset.sum_le_sum fun i _ => hlower i
  have htight :
      Fintype.card I * c + 1 = (c + 1) + S.card * c := by
    rw [hScard]
    have hcardSplit := Nat.sub_add_cancel hcard
    nlinarith
  have hrank0 : rank i0 = c + 1 := by
    omega
  have hrest : ∑ i ∈ S, rank i = S.card * c := by
    omega
  refine ⟨hrank0, ?_⟩
  intro i hi
  have hiS : i ∈ S := by simp [S, hi]
  let T : Finset I := S.erase i
  have hTcard : T.card = S.card - 1 := by
    simp [T, hiS]
  have hsplitS :
      ∑ j ∈ S, rank j = rank i + ∑ j ∈ T, rank j := by
    rw [← Finset.sum_erase_add S rank hiS]
    simp [T, add_comm]
  have hTlower : T.card * c ≤ ∑ j ∈ T, rank j := by
    calc
      T.card * c = ∑ _j ∈ T, c := by simp
      _ ≤ ∑ j ∈ T, rank j := by
        exact Finset.sum_le_sum fun j _ => hlower j
  have hSpos : 1 ≤ S.card := by
    exact Finset.card_pos.mpr ⟨i, hiS⟩
  have htightS : S.card * c = c + T.card * c := by
    rw [hTcard]
    have hcardSplit := Nat.sub_add_cancel hSpos
    nlinarith
  have hiLower := hlower i
  omega

variable {k : Type u} {W : Type v} {I : Type w}
variable [Field k] [AddCommGroup W] [Module k W]

/-- Equal-rank blocks inside an independent spanning eigenspace family,
together with one extra scalar line and a tight ambient dimension, force
a one-dimensional rank drop away from the distinguished eigenspace. -/
theorem eigenspace_rank_drop_of_blocks
    [Fintype I] [DecidableEq I] [FiniteDimensional k W]
    (i0 : I) (c : Nat)
    (E B : I -> Submodule k W)
    (hindependent : iSupIndep E) (hspan : ⨆ i, E i = ⊤)
    (hB_le : ∀ i : I, B i ≤ E i)
    (hB_rank : ∀ i : I, Module.finrank k (B i) = c)
    (L : Submodule k W) (hL_le : L ≤ E i0)
    (hL_rank : Module.finrank k L = 1)
    (hL_disjoint : Disjoint L (B i0))
    (hambient : Module.finrank k W = Fintype.card I * c + 1) :
    Module.finrank k (E i0) = c + 1 ∧
      ∀ i : I, i ≠ i0 -> Module.finrank k (E i) = c := by
  have htotal :
      ∑ i : I, Module.finrank k (E i) = Fintype.card I * c + 1 := by
    rw [← hambient]
    exact (finrank_eq_sum_finrank_of_iSupIndep E hindependent hspan).symm
  have hlower (i : I) : c ≤ Module.finrank k (E i) := by
    rw [← hB_rank i]
    exact Submodule.finrank_mono (hB_le i)
  have hsupRank :
      Module.finrank k (L ⊔ B i0 : Submodule k W) = c + 1 := by
    have hdimension := L.finrank_sup_add_finrank_inf_eq (B i0)
    rw [hL_disjoint.eq_bot, finrank_bot, add_zero,
      hL_rank, hB_rank i0] at hdimension
    omega
  have hlower0 : c + 1 ≤ Module.finrank k (E i0) := by
    rw [← hsupRank]
    exact Submodule.finrank_mono (sup_le hL_le (hB_le i0))
  exact eq_of_tight_rank_sum
    (fun i => Module.finrank k (E i)) i0 c htotal hlower hlower0

end Submission.OddOrder.MathlibSupport
