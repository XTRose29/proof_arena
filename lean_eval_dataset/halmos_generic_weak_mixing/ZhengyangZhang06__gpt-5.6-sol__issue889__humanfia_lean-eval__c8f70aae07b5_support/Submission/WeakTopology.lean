import Submission.Helpers

open LeanEval.Dynamics.HalmosGenericWeakMixingProblem
open MeasureTheory Filter Topology
open scoped symmDiff

namespace Submission.WeakTopology

variable {X : Type*} [MeasurableSpace X]

def iteratePreimage {m : Measure X} (T : Automorphism m)
    (k : ℕ) (A : Set X) : Set X :=
  ((T.toEquiv : X → X)^[k]) ⁻¹' A

@[simp]
theorem iteratePreimage_zero {m : Measure X} (T : Automorphism m)
    (A : Set X) : iteratePreimage T 0 A = A := by
  simp [iteratePreimage]

theorem iteratePreimage_succ {m : Measure X} (T : Automorphism m)
    (k : ℕ) (A : Set X) :
    iteratePreimage T (k + 1) A =
      T.toEquiv ⁻¹' iteratePreimage T k A := by
  ext x
  simp only [iteratePreimage, Set.mem_preimage]
  rw [Function.iterate_succ_apply]

theorem measurableSet_iteratePreimage {m : Measure X}
    (T : Automorphism m) (k : ℕ) {A : Set X} (hA : MeasurableSet A) :
    MeasurableSet (iteratePreimage T k A) :=
  hA.preimage (T.measurePreserving.iterate k).measurable

def weakBall (m : Measure X) (S : Automorphism m)
    (A : Set X) (ε : ℝ) : Set (Automorphism m) :=
  {T | m ((T.toEquiv '' A) ∆ (S.toEquiv '' A)) < ENNReal.ofReal ε}

theorem isOpen_weakBall (m : Measure X) (S : Automorphism m)
    {A : Set X} (hA : MeasurableSet A) {ε : ℝ} (hε : 0 < ε) :
    IsOpen (weakBall m S A ε) := by
  apply TopologicalSpace.isOpen_generateFrom_of_mem
  exact ⟨S, A, ε, hA, hε, rfl⟩

theorem self_mem_weakBall (m : Measure X) (S : Automorphism m)
    (A : Set X) {ε : ℝ} (hε : 0 < ε) : S ∈ weakBall m S A ε := by
  simp [weakBall, hε, ENNReal.ofReal_pos]

theorem measureReal_lt_of_mem_weakBall (m : Measure X) [IsFiniteMeasure m]
    (S T : Automorphism m) (A : Set X) {ε : ℝ}
    (hT : T ∈ weakBall m S A ε) :
    m.real ((T.toEquiv '' A) ∆ (S.toEquiv '' A)) < ε :=
  (ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top m _)).mp hT

theorem measureReal_preimage_symmDiff (m : Measure X)
    (T : Automorphism m) (A B : Set X) :
    m.real ((T.toEquiv ⁻¹' A) ∆ (T.toEquiv ⁻¹' B)) =
      m.real (A ∆ B) := by
  rw [← Set.preimage_symmDiff]
  exact congrArg ENNReal.toReal (Helpers.Automorphism.measure_preimage T (A ∆ B))

theorem measureReal_inverse_preimage_symmDiff (m : Measure X)
    (S T : Automorphism m) (A : Set X) :
    m.real ((T.toEquiv ⁻¹' A) ∆ (S.toEquiv ⁻¹' A)) =
      m.real ((T.toEquiv '' (S.toEquiv ⁻¹' A)) ∆
        (S.toEquiv '' (S.toEquiv ⁻¹' A))) := by
  calc
    m.real ((T.toEquiv ⁻¹' A) ∆ (S.toEquiv ⁻¹' A)) =
        m.real (T.toEquiv ''
          ((T.toEquiv ⁻¹' A) ∆ (S.toEquiv ⁻¹' A))) := by
      exact congrArg ENNReal.toReal
        (Helpers.Automorphism.measure_image T _).symm
    _ = m.real ((T.toEquiv '' (T.toEquiv ⁻¹' A)) ∆
        (T.toEquiv '' (S.toEquiv ⁻¹' A))) := by
      rw [Set.image_symmDiff T.toEquiv.injective]
    _ = m.real (A ∆ (T.toEquiv '' (S.toEquiv ⁻¹' A))) := by
      congr 2
      ext x
      simp
    _ = m.real ((T.toEquiv '' (S.toEquiv ⁻¹' A)) ∆ A) := by
      rw [symmDiff_comm]
    _ = m.real ((T.toEquiv '' (S.toEquiv ⁻¹' A)) ∆
        (S.toEquiv '' (S.toEquiv ⁻¹' A))) := by
      congr 2
      ext x
      simp

theorem iteratePreimage_succ_distance_le (m : Measure X)
    [IsFiniteMeasure m]
    (S T : Automorphism m) (k : ℕ) (A : Set X) :
    m.real (iteratePreimage T (k + 1) A ∆
        iteratePreimage S (k + 1) A) ≤
      m.real (iteratePreimage T k A ∆ iteratePreimage S k A) +
        m.real ((T.toEquiv '' iteratePreimage S (k + 1) A) ∆
          (S.toEquiv '' iteratePreimage S (k + 1) A)) := by
  rw [iteratePreimage_succ, iteratePreimage_succ]
  refine (measureReal_symmDiff_le
    (s := T.toEquiv ⁻¹' iteratePreimage T k A)
    (t := T.toEquiv ⁻¹' iteratePreimage S k A)
    (S.toEquiv ⁻¹' iteratePreimage S k A)).trans ?_
  rw [measureReal_preimage_symmDiff,
    measureReal_inverse_preimage_symmDiff,
    ← iteratePreimage_succ S k A]

theorem exists_open_iteratePreimage_close (m : Measure X)
    [IsFiniteMeasure m]
    (S : Automorphism m) {A : Set X} (hA : MeasurableSet A)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set (Automorphism m), IsOpen U ∧ S ∈ U ∧
      ∀ T ∈ U,
        m.real (iteratePreimage T k A ∆ iteratePreimage S k A) < ε := by
  induction k generalizing ε with
  | zero =>
      refine ⟨Set.univ, isOpen_univ, Set.mem_univ S, ?_⟩
      intro T _
      simpa using hε
  | succ k ih =>
      have hhalf : 0 < ε / 2 := by positivity
      obtain ⟨U, hUopen, hSU, hU⟩ := ih hhalf
      let C := iteratePreimage S (k + 1) A
      have hC : MeasurableSet C := measurableSet_iteratePreimage S (k + 1) hA
      let V := weakBall m S C (ε / 2)
      have hVopen : IsOpen V := isOpen_weakBall m S hC hhalf
      have hSV : S ∈ V := self_mem_weakBall m S C hhalf
      refine ⟨U ∩ V, hUopen.inter hVopen, ⟨hSU, hSV⟩, ?_⟩
      intro T hT
      have hprev := hU T hT.1
      have hstep :
          m.real ((T.toEquiv '' C) ∆ (S.toEquiv '' C)) < ε / 2 :=
        measureReal_lt_of_mem_weakBall m S T C hT.2
      have hbound := iteratePreimage_succ_distance_le m S T k A
      change m.real (iteratePreimage T (k + 1) A ∆
          iteratePreimage S (k + 1) A) < ε
      change m.real (iteratePreimage T k A ∆ iteratePreimage S k A) < ε / 2 at hprev
      change m.real ((T.toEquiv '' iteratePreimage S (k + 1) A) ∆
          (S.toEquiv '' iteratePreimage S (k + 1) A)) < ε / 2 at hstep
      linarith

end Submission.WeakTopology
