import Submission.OddOrder.MathlibSupport.SquareZeroAnticommutator
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
The two-dimensional stable span attached to a square-zero pair.
-/

namespace Submission.OddOrder.MathlibSupport

variable {D V : Type*} [Field D] [AddCommGroup V] [Module D V]

/-- The span of `X u` and `Y (X u)`. -/
def squareZeroPairSpan (X Y : Module.End D V) (u : V) : Submodule D V :=
  Submodule.span D {X u, Y (X u)}

theorem squareZeroPairSpan_stable_left
    (X Y : Module.End D V) (u : V) (a : D)
    (hX : X * X = 0)
    (hA : anticommutator X Y = a • (1 : Module.End D V)) :
    squareZeroPairSpan X Y u ≤ (squareZeroPairSpan X Y u).comap X := by
  let v := X u
  let W := squareZeroPairSpan X Y u
  have hXv : X v = 0 := by
    have h := LinearMap.congr_fun hX u
    simpa [v, Module.End.mul_apply] using h
  have hXYv : X (Y v) = a • v := by
    have h := LinearMap.congr_fun hA v
    simpa [anticommutator, Module.End.mul_apply, hXv] using h
  intro w hw
  change X w ∈ W
  change w ∈ Submodule.span D {v, Y v} at hw
  induction hw using Submodule.span_induction with
  | mem z hz =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · rw [hXv]
        exact W.zero_mem
      · rw [hXYv]
        exact W.smul_mem a (Submodule.subset_span (Set.mem_insert _ _))
  | zero => simp
  | add x y _ _ hx hy => simpa using W.add_mem hx hy
  | smul c x _ hx => simpa using W.smul_mem c hx

theorem squareZeroPairSpan_stable_right
    (X Y : Module.End D V) (u : V)
    (hY : Y * Y = 0) :
    squareZeroPairSpan X Y u ≤ (squareZeroPairSpan X Y u).comap Y := by
  let v := X u
  let W := squareZeroPairSpan X Y u
  have hYYv : Y (Y v) = 0 := by
    have h := LinearMap.congr_fun hY v
    simpa [Module.End.mul_apply] using h
  intro w hw
  change Y w ∈ W
  change w ∈ Submodule.span D {v, Y v} at hw
  induction hw using Submodule.span_induction with
  | mem z hz =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      · rw [hYYv]
        exact W.zero_mem
  | zero => simp
  | add x y _ _ hx hy => simpa using W.add_mem hx hy
  | smul c x _ hx => simpa using W.smul_mem c hx

theorem finrank_squareZeroPairSpan_le_two
    (X Y : Module.End D V) (u : V) :
    Module.finrank D (squareZeroPairSpan X Y u) ≤ 2 := by
  classical
  have hcard : ({X u, Y (X u)} : Set V).toFinset.card ≤ 2 := by
    simpa using (Finset.card_le_two (a := X u) (b := Y (X u)))
  exact (finrank_span_le_card ({X u, Y (X u)} : Set V)).trans hcard

end Submission.OddOrder.MathlibSupport
