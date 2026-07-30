import Submission.OddOrder.PF.Section02.DadeInduction
import Submission.OddOrder.PF.Section02.DadeReciprocity

/-!
# Peterfalvi 2.3 and 2.6 for normalized TI sets

A normalized trivial-intersection set contained in the nonidentity elements
supplies the Dade hypothesis with the constant trivial signalizer.  The Dade
map is therefore ordinary class-function induction, giving the identity and
isometry forms of Isaacs' Lemma 7.7.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.MathlibSupport
open scoped Classical

universe u v

/-- The existence part of Peterfalvi 2.3: a normalized TI set contained in
the nonidentity elements satisfies the Dade hypothesis. -/
theorem normedTI_Dade
    {Γ : Type u} [Group Γ] [Finite Γ]
    {G L : Subgroup Γ} {A : Set Γ}
    (hTI : IsNormalizedTI A G L)
    (hAG1 : A ⊆ (G : Set Γ) \ {(1 : Γ)}) :
    DadeHypothesis G L A := by
  have hmem := isNormalizedTI_iff_mem_conj.mp hTI
  have hLG : L ≤ G := hmem.2.1
  have hAL : A ⊆ (L : Set Γ) := by
    intro a ha
    have haG : a ∈ G := (hAG1 ha).1
    apply (hmem.2.2 ha haG).mp
    simpa using ha
  have hLN : L ≤ Subgroup.normalizer A := by
    intro x hx
    exact (hTI.2.1 hx).2
  have hnot1 : (1 : Γ) ∉ A := by
    intro h1
    exact (hAG1 h1).2 (Set.mem_singleton 1)
  refine ⟨⟨hAL, hLN⟩, hLG, hnot1, ?_, ?_⟩
  · intro x hx y hy hyG
    rcases hyG with ⟨g, hg, rfl⟩
    exact ⟨g, (hmem.2.2 hx hg).mp hy, rfl⟩
  · refine ⟨fun _ ↦ ⊥, ?_, ?_⟩
    · intro a ha
      have hCLG :
          centralizerWithin L (Subgroup.zpowers a) ≤
            centralizerWithin G (Subgroup.zpowers a) := by
        intro x hx
        exact ⟨hLG hx.1, hx.2⟩
      have hCGL :
          centralizerWithin G (Subgroup.zpowers a) ≤
            centralizerWithin L (Subgroup.zpowers a) := by
        intro x hx
        exact ⟨hTI.centralizerWithin_zpowers_le ha hx, hx.2⟩
      refine ⟨bot_le, hCLG, ?_, ?_⟩
      · dsimp
        rw [Subgroup.bot_subgroupOf]
        infer_instance
      · dsimp
        rw [Subgroup.bot_subgroupOf]
        apply Subgroup.isComplement'_bot_left.mpr
        apply Subgroup.subgroupOf_eq_top.mpr
        exact hCGL
    · intro a _ha b _hb
      dsimp
      rw [Subgroup.card_bot]
      exact Nat.coprime_one_left
        (Nat.card (centralizerWithin L (Subgroup.zpowers b)))

/-- The identity part of Isaacs' Lemma 7.7, including the identity element. -/
theorem normedTI_Ind_id1
    {Γ : Type u} [Group Γ] [Fintype Γ]
    {k : Type v} [Field k] [CharZero k]
    {G L : Subgroup Γ} {A : Set Γ}
    (hTI : IsNormalizedTI A G L)
    (hAG1 : A ⊆ (G : Set Γ) \ {(1 : Γ)})
    (alpha : ClassFunction L k)
    (halpha : alpha ∈
      ClassFunction.supportedOn {x : L | (x : Γ) ∈ A})
    (a : L) (ha : a = 1 ∨ (a : Γ) ∈ A) :
    let ddA := normedTI_Dade hTI hAG1
    ClassFunction.induce (L.subgroupOf G)
        (ClassFunction.toSubgroupOf L G ddA.2.1 alpha)
        ⟨a, ddA.2.1 a.property⟩ =
      alpha a := by
  dsimp only
  let ddA := normedTI_Dade hTI hAG1
  rw [← Dade_Ind ddA hTI alpha halpha]
  exact Dade_id1 ddA alpha halpha a ha

/-- The identity part of Isaacs' Lemma 7.7 on the normalized TI set. -/
theorem normedTI_Ind_id
    {Γ : Type u} [Group Γ] [Fintype Γ]
    {k : Type v} [Field k] [CharZero k]
    {G L : Subgroup Γ} {A : Set Γ}
    (hTI : IsNormalizedTI A G L)
    (hAG1 : A ⊆ (G : Set Γ) \ {(1 : Γ)})
    (alpha : ClassFunction L k)
    (halpha : alpha ∈
      ClassFunction.supportedOn {x : L | (x : Γ) ∈ A})
    (a : L) (ha : (a : Γ) ∈ A) :
    let ddA := normedTI_Dade hTI hAG1
    ClassFunction.induce (L.subgroupOf G)
        (ClassFunction.toSubgroupOf L G ddA.2.1 alpha)
        ⟨a, ddA.2.1 a.property⟩ =
      alpha a := by
  exact normedTI_Ind_id1 hTI hAG1 alpha halpha a (Or.inr ha)

/-- The isometry part of Isaacs' Lemma 7.7 for ordinary induction from the
relative normalizer of a normalized TI set. -/
theorem normedTI_isometry
    {Γ : Type u} [Group Γ] [Fintype Γ]
    {k : Type v} [Field k] [CharZero k] [StarRing k]
    {G L : Subgroup Γ} {A : Set Γ}
    (hTI : IsNormalizedTI A G L)
    (hAG1 : A ⊆ (G : Set Γ) \ {(1 : Γ)})
    (alpha beta : ClassFunction L k)
    (halpha : alpha ∈
      ClassFunction.supportedOn {x : L | (x : Γ) ∈ A})
    (hbeta : beta ∈
      ClassFunction.supportedOn {x : L | (x : Γ) ∈ A}) :
    let ddA := normedTI_Dade hTI hAG1
    starCharacterPairing
        (ClassFunction.induce (L.subgroupOf G)
          (ClassFunction.toSubgroupOf L G ddA.2.1 alpha))
        (ClassFunction.induce (L.subgroupOf G)
          (ClassFunction.toSubgroupOf L G ddA.2.1 beta)) =
      starCharacterPairing alpha beta := by
  dsimp only
  let ddA := normedTI_Dade hTI hAG1
  rw [← Dade_Ind ddA hTI alpha halpha,
    ← Dade_Ind ddA hTI beta hbeta]
  exact Dade_isometry ddA alpha beta halpha hbeta

end

end Submission.OddOrder.PF
