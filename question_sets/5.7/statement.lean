/-
Problem 7.

For any `k`-algebra `R` and any finite field extension `K/k`, show that
`rad R` is nilpotent if `rad (R^K)` is nilpotent, where `R^K` denotes the
scalar extension `R ⊗[k] K`.
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.TensorProduct.Basic

open scoped TensorProduct

set_option linter.unusedSectionVars false
noncomputable section

variable (k K R : Type*)
variable [Field k] [Field K] [CommRing R]
variable [Algebra k K] [Algebra k R] [FiniteDimensional k K]

/- We realize the scalar extension `R^K` as `R ⊗[k] K`. -/
local notation:100 R "^[" k "," K "]" => TensorProduct k R K

lemma isNilpotent_of_map_baseChange
    {I : Ideal R}
    (h : IsNilpotent (Ideal.map (algebraMap R (R^[k, K])) I)) :
    IsNilpotent I := by
  sorry

theorem jacobson_nilpotent_of_baseChange_jacobson_nilpotent
    (h : IsNilpotent (Ideal.map (algebraMap R (R^[k, K])) (Ring.jacobson R))) :
    IsNilpotent (Ring.jacobson R) := by
  sorry

/--
This is the faithfully-flat descent step needed for the textbook argument.
To obtain the literal statement from the image, one additionally needs the base-change inclusion
`map (Ring.jacobson R) ≤ Ring.jacobson (R ⊗[k] K)`.
-/
theorem textbook_statement :
    IsNilpotent (Ideal.map (algebraMap R (R^[k, K])) (Ideal.jacobson (⊥ : Ideal R))) →
      IsNilpotent (Ideal.jacobson (⊥ : Ideal R)) := by
  sorry
