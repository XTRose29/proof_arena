import Submission.OddOrder.PF.Section02.DadeMap
import Submission.OddOrder.PF.Section01.ClassFunctionSupport

/-!
# Basic properties of the Dade map

The Dade map vanishes away from its defining support, is supported on the
nonidentity elements, and agrees with the original class function on the
distinguished set `A` (as well as at the identity for functions supported on
`A`).
-/

namespace Submission.OddOrder.PF

noncomputable section

universe u v

variable {Γ : Type u} [Group Γ]

/-- The Dade map vanishes outside its global support. -/
theorem Dade_eq_zero_of_not_mem
    [Finite Γ] {G L : Subgroup Γ} {A : Set Γ} {k : Type v} [Field k]
    (ddA : DadeHypothesis G L A) (alpha : ClassFunction L k)
    (x : G) (hx : (x : Γ) ∉ Dade_support ddA) :
    Dade ddA alpha x = 0 := by
  classical
  change (if _h : (x : Γ) ∈ Dade_support ddA then _ else 0) = 0
  simp [hx]

/-- On `A`, the Dade map agrees with the original class function. -/
theorem Dade_id
    [Finite Γ] {G L : Subgroup Γ} {A : Set Γ} {k : Type v} [Field k]
    (ddA : DadeHypothesis G L A) (alpha : ClassFunction L k)
    {a : Γ} (ha : a ∈ A) :
    Dade ddA alpha ⟨a, ddA.2.1 (ddA.1.1 ha)⟩ =
      alpha ⟨a, ddA.1.1 ha⟩ := by
  apply DadeE ddA alpha ha
  simpa using
    (mem_Dade_support1 ddA ha (DadeSignalizer ddA a).one_mem)

/-- The Dade map is supported on its global Dade support. -/
theorem Dade_cfunS
    [Finite Γ] {G L : Subgroup Γ} {A : Set Γ}
    {k : Type v} [Field k]
    (ddA : DadeHypothesis G L A) (alpha : ClassFunction L k) :
    Dade ddA alpha ∈
      ClassFunction.supportedOn {x : G | (x : Γ) ∈ Dade_support ddA} := by
  apply ClassFunction.mem_supportedOn_iff.mpr
  intro x hx
  exact Dade_eq_zero_of_not_mem ddA alpha x hx

/-- The Dade map is supported on the nonidentity elements of `G`. -/
theorem Dade_cfun
    [Finite Γ] {G L : Subgroup Γ} {A : Set Γ}
    {k : Type v} [Field k]
    (ddA : DadeHypothesis G L A) (alpha : ClassFunction L k) :
    Dade ddA alpha ∈ ClassFunction.supportedOn {x : G | x ≠ 1} := by
  apply ClassFunction.mem_supportedOn_iff.mpr
  intro x hx
  have hx1 : x = 1 := not_ne_iff.mp hx
  subst x
  apply Dade_eq_zero_of_not_mem ddA alpha
  simpa using not_support_Dade_1 ddA

/-- The Dade map vanishes at the identity. -/
theorem Dade1
    [Finite Γ] {G L : Subgroup Γ} {A : Set Γ}
    {k : Type v} [Field k]
    (ddA : DadeHypothesis G L A) (alpha : ClassFunction L k) :
    Dade ddA alpha (1 : G) = 0 := by
  apply Dade_eq_zero_of_not_mem ddA alpha
  simpa using not_support_Dade_1 ddA

/-- For a class function supported on `A`, the Dade map agrees with it both
on `A` and at the identity. -/
theorem Dade_id1
    [Finite Γ] {G L : Subgroup Γ} {A : Set Γ}
    {k : Type v} [Field k]
    (ddA : DadeHypothesis G L A) (alpha : ClassFunction L k)
    (halpha : alpha ∈ ClassFunction.supportedOn {x : L | (x : Γ) ∈ A})
    (a : L) (ha : a = 1 ∨ (a : Γ) ∈ A) :
    Dade ddA alpha ⟨a, ddA.2.1 a.property⟩ = alpha a := by
  rcases ha with rfl | ha
  · have hG :
        (⟨((1 : L) : Γ), ddA.2.1 (1 : L).property⟩ : G) = 1 := by
      ext
      simp
    rw [hG, Dade1 ddA alpha]
    symm
    apply ClassFunction.eq_zero_of_mem_supportedOn halpha
    simpa using ddA.2.2.1
  · simpa using Dade_id ddA alpha ha

end

end Submission.OddOrder.PF
