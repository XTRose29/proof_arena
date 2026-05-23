import Mathlib

namespace Submission.Helpers

open Polynomial Matrix Module

/-! ## Helper lemmas for the Brauer character theorem -/

/-- Every root of the characteristic polynomial of a linear map f with f^n = 1
    is an n-th root of unity. -/
lemma charpoly_root_isNthRootOfUnity
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : End ℂ V) (n : ℕ) (hn : 0 < n) (hf : f ^ n = 1)
    (r : ℂ) (hr : r ∈ f.charpoly.roots) :
    r ^ n = 1 := by
  obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 ∧ f v = r • v := by
    have h_eigenvalue : (f - r • 1).det = 0 := by
      rw [ LinearMap.det_eq_sign_charpoly_coeff ];
      have h_charpoly : LinearMap.charpoly (f - r • 1) = Polynomial.comp (LinearMap.charpoly f) (Polynomial.X + Polynomial.C r) := by
        exact?;
      simp_all +decide [ Polynomial.coeff_zero_eq_eval_zero ];
    have := LinearMap.isUnit_det ( f - r • 1 ) ; simp_all +decide [ isUnit_iff_ne_zero ] ;
    contrapose! this;
    exact ( LinearMap.isUnit_iff_ker_eq_bot _ ).mpr ( eq_bot_iff.mpr fun v hv => Classical.not_not.1 fun hv' => this v hv' <| by simpa [ sub_eq_zero ] using hv );
  have h_fn_v : f^[n] v = r^n • v := by
    refine' Nat.recOn n _ _ <;> simp_all +decide [ pow_succ, mul_assoc, Function.iterate_succ_apply' ];
    exact?;
  have h_fn_v_one : f^[n] v = v := by
    convert congr_arg ( fun g => g v ) hf;
    exact?;
  exact smul_left_injective _ hv.1 ( by simpa [ h_fn_v ] using h_fn_v_one )

/-- The trace of a linear map over ℂ equals the sum of roots of its characteristic polynomial. -/
lemma trace_eq_charpoly_roots_sum
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : End ℂ V) :
    LinearMap.trace ℂ V f = f.charpoly.roots.sum := by
  convert Matrix.trace_eq_sum_roots_charpoly ( LinearMap.toMatrix ( Module.Free.chooseBasis ℂ V ) ( Module.Free.chooseBasis ℂ V ) f );
  exact?

/-- CyclotomicField n ℚ has a primitive n-th root of unity when n > 0. -/
lemma exists_primitiveRoot_cyclotomicField (n : ℕ) (hn : 0 < n) :
    ∃ ζ : CyclotomicField n ℚ, IsPrimitiveRoot ζ n := by
  have hsplits : ((Polynomial.cyclotomic n ℚ).map (algebraMap ℚ (CyclotomicField n ℚ))).Splits :=
    (Polynomial.IsSplittingField.splittingField (Polynomial.cyclotomic n ℚ)).splits'
  have hdeg : ((Polynomial.cyclotomic n ℚ).map (algebraMap ℚ (CyclotomicField n ℚ))).degree ≠ 0 := by
    rw [Polynomial.degree_map]
    exact ne_of_gt (Polynomial.degree_cyclotomic_pos n ℚ hn)
  let ζ := Polynomial.rootOfSplits hsplits hdeg
  have hζ : Polynomial.eval ζ ((Polynomial.cyclotomic n ℚ).map (algebraMap ℚ (CyclotomicField n ℚ))) = 0 :=
    Polynomial.eval_rootOfSplits hsplits hdeg
  refine ⟨ζ, ?_⟩
  rw [← Polynomial.isRoot_cyclotomic_iff_charZero hn]
  rw [Polynomial.IsRoot]
  rw [← Polynomial.map_cyclotomic n (algebraMap ℚ (CyclotomicField n ℚ))]
  exact hζ

/-- For n > 0, every n-th root of unity in ℂ lies in the range of the canonical
    algebra map from CyclotomicField n ℚ to ℂ. -/
lemma root_of_unity_in_range (n : ℕ) (hn : 0 < n)
    (φ : CyclotomicField n ℚ →ₐ[ℚ] ℂ)
    (z : ℂ) (hz : z ^ n = 1) :
    z ∈ (φ : CyclotomicField n ℚ →+* ℂ).range := by
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_cyclotomicField n hn
  have hφζ : IsPrimitiveRoot (φ ζ) n := by
    convert hζ.map_of_injective φ.injective
  have hinj := hφζ.pow_inj
  have h_z_root : ∃ k : ℕ, k < n ∧ z = (φ ζ) ^ k := by
    have h_image_eq : Finset.image (fun k : ℕ => (φ ζ) ^ k) (Finset.range n) = Multiset.toFinset (Polynomial.roots (Polynomial.X ^ n - 1 : Polynomial ℂ)) := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · simp_all +decide [ Finset.subset_iff ]
        exact fun a ha => ⟨ ne_of_apply_ne ( Polynomial.eval 0 ) ( by norm_num [ hn.ne' ] ), by rw [ ← pow_mul, Nat.mul_comm, pow_mul, hφζ.pow_eq_one, one_pow, sub_self ] ⟩
      · rw [ Finset.card_image_of_injOn fun i hi j hj hij => hinj ( Finset.mem_range.mp hi ) ( Finset.mem_range.mp hj ) hij ] ; norm_num
        exact le_trans ( Multiset.toFinset_card_le _ ) ( le_trans ( Polynomial.card_roots' _ ) ( by erw [ Polynomial.natDegree_X_pow_sub_C ] ) )
    replace h_image_eq := Finset.ext_iff.mp h_image_eq z; simp_all +decide [ sub_eq_iff_eq_add ]
    exact h_image_eq.mpr ( ne_of_apply_ne Polynomial.natDegree <| by aesop ) |> fun ⟨ k, hk₁, hk₂ ⟩ => ⟨ k, hk₁, hk₂.symm ⟩
  exact h_z_root.elim fun k hk => ⟨ ζ ^ k, by aesop ⟩

end Submission.Helpers
