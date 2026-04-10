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

/-
We realize the scalar extension `R^K` as `R ⊗[k] K`. This is canonically isomorphic to
`K ⊗[k] R`, but using `R ⊗[k] K` makes the `R`-algebra structure the standard one.
-/
local notation:100 R "^[" k "," K "]" => TensorProduct k R K

lemma isNilpotent_of_map_baseChange
    {I : Ideal R}
    (h : IsNilpotent (Ideal.map (algebraMap R (R^[k, K])) I)) :
    IsNilpotent I := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, le_antisymm ?_ bot_le⟩
  calc
    I ^ n = ((Ideal.map (algebraMap R (R^[k, K])) I).comap (algebraMap R (R^[k, K]))) ^ n := by
      rw [Ideal.comap_map_eq_self_of_faithfullyFlat (B := R^[k, K])]
    _ ≤ (((Ideal.map (algebraMap R (R^[k, K])) I) ^ n).comap (algebraMap R (R^[k, K]))) :=
      Ideal.le_comap_pow _ _
    _ = ⊥ := by
      rw [hn]
      change Ideal.comap (algebraMap R (R^[k, K])) (⊥ : Ideal (R^[k, K])) = ⊥
      rw [← RingHom.ker_eq_comap_bot]
      exact (RingHom.injective_iff_ker_eq_bot _).mp <|
        FaithfulSMul.algebraMap_injective R (R^[k, K])

theorem jacobson_nilpotent_of_baseChange_jacobson_nilpotent
    (h : IsNilpotent (Ideal.map (algebraMap R (R^[k, K])) (Ring.jacobson R))) :
    IsNilpotent (Ring.jacobson R) := by
  exact isNilpotent_of_map_baseChange (k := k) (K := K) (R := R) h

/--
This is the faithfully-flat descent step needed for the textbook argument.
To obtain the literal statement from the image, one additionally needs the base-change inclusion
`map (Ring.jacobson R) ≤ Ring.jacobson (R ⊗[k] K)`.
-/
theorem textbook_statement :
    IsNilpotent (Ideal.map (algebraMap R (R^[k, K])) (Ideal.jacobson (⊥ : Ideal R))) →
      IsNilpotent (Ideal.jacobson (⊥ : Ideal R)) := by
  simpa [Ideal.jacobson_bot] using
    (jacobson_nilpotent_of_baseChange_jacobson_nilpotent (k := k) (K := K) (R := R))
