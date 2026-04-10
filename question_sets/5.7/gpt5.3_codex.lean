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

local notation:100 R "^[" k "," K "]" => TensorProduct k R K

omit [FiniteDimensional k K] in
lemma isNilpotent_of_map_baseChange
    {I : Ideal R}
    (h : IsNilpotent (Ideal.map (algebraMap R (R^[k, K])) I)) :
    IsNilpotent I := by
  letI : Module.FaithfullyFlat R (R^[k, K]) :=
    Module.FaithfullyFlat.instTensorProduct (R := k) (M := K) (S := R)
  rcases h with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have hmap : Ideal.map (algebraMap R (R^[k, K])) (I ^ n) = ⊥ := by
    simpa [Ideal.map_pow] using hn
  have hle : I ^ n ≤ RingHom.ker (algebraMap R (R^[k, K])) := by
    rwa [Ideal.map_eq_bot_iff_le_ker] at hmap
  have hker : RingHom.ker (algebraMap R (R^[k, K])) = ⊥ := by
    have hker' :=
      (Ideal.comap_map_eq_self_of_faithfullyFlat
        (A := R) (B := R^[k, K]) (I := (⊥ : Ideal R)))
    simp at hker'
    exact hker'
  rw [hker] at hle
  exact le_antisymm hle bot_le

omit [FiniteDimensional k K] in
theorem jacobson_nilpotent_of_baseChange_jacobson_nilpotent
    (h : IsNilpotent (Ideal.map (algebraMap R (R^[k, K])) (Ring.jacobson R))) :
    IsNilpotent (Ring.jacobson R) := by
  exact isNilpotent_of_map_baseChange (k := k) (K := K) (R := R) (I := Ring.jacobson R) h

/--
This is the faithfully-flat descent step needed for the textbook argument.
To obtain the literal statement from the image, one additionally needs the base-change inclusion
`map (Ring.jacobson R) ≤ Ring.jacobson (R ⊗[k] K)`.
-/
theorem textbook_statement :
    IsNilpotent (Ideal.map (algebraMap R (R^[k, K])) (Ideal.jacobson (⊥ : Ideal R))) →
      IsNilpotent (Ideal.jacobson (⊥ : Ideal R)) := by
  intro h
  exact isNilpotent_of_map_baseChange
    (k := k) (K := K) (R := R) (I := Ideal.jacobson (⊥ : Ideal R)) h
