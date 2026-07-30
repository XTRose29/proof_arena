import Submission.OddOrder.MathlibSupport.Centralizer

/-!
# Peterfalvi 2.2: the hypotheses for the Dade isometry

This file ports the predicate in Peterfalvi Definition 2.2.  The signalizer
family in clauses (b) and (c) is kept under one existential quantifier, as in
the Coq source.
-/

namespace Submission.OddOrder.PF

open Submission.OddOrder.MathlibSupport

universe u

variable {Γ : Type u} [Group Γ]

/-- The conjugacy class of `x` under conjugation by elements of `K`. -/
def conjugacyClassWithin (K : Subgroup Γ) (x : Γ) : Set Γ :=
  (fun k : Γ => k⁻¹ * x * k) '' (K : Set Γ)

/-- `K` is the internal semidirect product of the normal factor `N` and the
complement `H`.

The factors are subgroups of the common ambient group `Γ`; `subgroupOf`
regards them as subgroups of `K`, where normality and complementarity are
asserted. -/
def IsInternalSemidirectProductIn
    (N H K : Subgroup Γ) : Prop :=
  N ≤ K ∧ H ≤ K ∧ (N.subgroupOf K).Normal ∧
    (N.subgroupOf K).IsComplement' (H.subgroupOf K)

/-- A family of signalizers satisfying Peterfalvi 2.2(b). -/
def IsDadeSignalizer
    (G L : Subgroup Γ) (A : Set Γ)
    (H : Γ → Subgroup Γ) : Prop :=
  ∀ ⦃a⦄, a ∈ A →
    IsInternalSemidirectProductIn (H a)
      (centralizerWithin L (Subgroup.zpowers a))
      (centralizerWithin G (Subgroup.zpowers a))

/-- Peterfalvi Definition 2.2: hypotheses under which the Dade isometry
relative to `G`, `L`, and `A` is defined.  Clause (a) says that two elements
of `A` conjugate under `G` are already conjugate under `L`. -/
def DadeHypothesis
    (G L : Subgroup Γ) (A : Set Γ) : Prop :=
  (A ⊆ (L : Set Γ) ∧ L ≤ Subgroup.normalizer A) ∧
  L ≤ G ∧ (1 : Γ) ∉ A ∧
  (∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ A →
    y ∈ conjugacyClassWithin G x → y ∈ conjugacyClassWithin L x) ∧
  ∃ H : Γ → Subgroup Γ,
    IsDadeSignalizer G L A H ∧
    ∀ ⦃a⦄, a ∈ A → ∀ ⦃b⦄, b ∈ A →
      Nat.Coprime (Nat.card (H a))
        (Nat.card (centralizerWithin L (Subgroup.zpowers b)))

end Submission.OddOrder.PF
