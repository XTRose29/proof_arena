import Submission.HopfGenLoopLift

open scoped ComplexConjugate

noncomputable section

namespace Submission.HopfFiberPhase

open Submission.Helpers

/-- The Hermitian phase carrying `z` to `w` when both points lie in the
same Hopf fiber. -/
def rawPhase (z w : SphereThree) : ℂ :=
  w.1 0 * conj (z.1 0) + w.1 1 * conj (z.1 1)

lemma rawPhase_circleAct (u : Circle) (z : SphereThree) :
    rawPhase z (circleAct u z) = (u : ℂ) := by
  let uC : ℂ := u
  let z₀ : ℂ := z.1 0
  let z₁ : ℂ := z.1 1
  change
    (uC * z₀) * conj z₀ + (uC * z₁) * conj z₁ = uC
  calc
    (uC * z₀) * conj z₀ + (uC * z₁) * conj z₁ =
        uC * (z₀ * conj z₀) + uC * (z₁ * conj z₁) := by ring
    _ =
        uC * (Complex.normSq z₀ : ℂ) +
          uC * (Complex.normSq z₁ : ℂ) := by
      rw [Complex.mul_conj, Complex.mul_conj]
    _ =
        uC *
          ((Complex.normSq z₀ + Complex.normSq z₁ : ℝ) : ℂ) := by
      push_cast
      ring
    _ = uC := by
      change
        uC *
            ((Complex.normSq (z.1 0) +
              Complex.normSq (z.1 1) : ℝ) : ℂ) =
          uC
      rw [sphereThree_normSq_add]
      simp

/-- The global circle-valued phase between two points in one Hopf
fiber. -/
def phase (z w : SphereThree) (h : hopfMap z = hopfMap w) :
    Circle := by
  let u : Circle :=
    Classical.choose (exists_circleAct_eq_of_hopfMap_eq h)
  have hu : circleAct u z = w :=
    Classical.choose_spec (exists_circleAct_eq_of_hopfMap_eq h)
  refine ⟨rawPhase z w, ?_⟩
  rw [← hu, rawPhase_circleAct]
  exact u.property

lemma phase_eq_of_circleAct_eq (z w : SphereThree)
    (h : hopfMap z = hopfMap w) (u : Circle)
    (hu : circleAct u z = w) :
    phase z w h = u := by
  apply Circle.ext
  change rawPhase z w = (u : ℂ)
  rw [← hu]
  exact rawPhase_circleAct u z

/-- Acting by the global phase carries the first fiber point to the
second. -/
lemma circleAct_phase (z w : SphereThree)
    (h : hopfMap z = hopfMap w) :
    circleAct (phase z w h) z = w := by
  obtain ⟨u, hu⟩ := exists_circleAct_eq_of_hopfMap_eq h
  rw [phase_eq_of_circleAct_eq z w h u hu]
  exact hu

@[simp]
lemma phase_self (z : SphereThree) :
    phase z z rfl = 1 := by
  exact phase_eq_of_circleAct_eq z z rfl 1 (circleAct_one z)

/-- The Hermitian formula makes the phase continuous even when both
points and the base of their Hopf fiber vary. -/
lemma continuous_phase {A : Type*} [TopologicalSpace A]
    {z w : A → SphereThree}
    (h : ∀ a, hopfMap (z a) = hopfMap (w a))
    (hz : Continuous z) (hw : Continuous w) :
    Continuous fun a => phase (z a) (w a) (h a) := by
  apply Continuous.subtype_mk
  change Continuous fun a => rawPhase (z a) (w a)
  unfold rawPhase
  fun_prop

end Submission.HopfFiberPhase
