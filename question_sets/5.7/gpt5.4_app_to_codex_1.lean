import Mathlib

open scoped TensorProduct

theorem jacobson_nilpotent_of_tensorProduct
    (k K R : Type*)
    [Field k] [Field K] [CommRing R]
    [Algebra k K] [Algebra k R] [FiniteDimensional k K]
    (hK : IsNilpotent (Ring.jacobson (R ⊗[k] K))) :
    IsNilpotent (Ring.jacobson R) := by
  let f : R →+* R ⊗[k] K := algebraMap R (R ⊗[k] K)
  have hf : Function.Injective f := by
    simpa [f] using
      (Algebra.TensorProduct.includeLeft_injective (S := R) (algebraMap k K).injective)
  have hle : Ring.jacobson R ≤ Ideal.comap f (Ring.jacobson (R ⊗[k] K)) := by
    simpa [f] using (Ring.le_comap_jacobson (f := f))
  obtain ⟨n, hn⟩ := hK
  refine ⟨n, eq_bot_iff.mpr fun x hx => ?_⟩
  apply hf
  have hmap :
      Ideal.map f (Ring.jacobson R ^ n) ≤ Ring.jacobson (R ⊗[k] K) ^ n := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hle) n
  have hx' : f x ∈ Ideal.map f (Ring.jacobson R ^ n) := by
    exact Ideal.mem_map_of_mem _ hx
  have : f x ∈ (⊥ : Ideal (R ⊗[k] K)) := by
    exact hn ▸ hmap hx'
  simpa using this
