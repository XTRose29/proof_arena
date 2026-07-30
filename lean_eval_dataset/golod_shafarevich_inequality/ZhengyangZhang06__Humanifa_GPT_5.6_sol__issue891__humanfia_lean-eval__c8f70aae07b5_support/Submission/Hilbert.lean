import Submission.GroupAlgebra

namespace Submission.Hilbert

open Submission.GroupAlgebra

variable (k G : Type*) [Field k] [Group G]

/-- The powers of the augmentation ideal, regarded as vector subspaces. -/
noncomputable def augmentationPower (n : ℕ) : Submodule k (MonoidAlgebra k G) :=
  ((augmentationIdeal k G) ^ n).restrictScalars k

theorem augmentationPower_antitone : Antitone (augmentationPower k G) := by
  intro m n hmn
  exact Ideal.pow_le_pow_right hmn

theorem augmentation_surjective : Function.Surjective (augmentation k G) := by
  intro x
  refine ⟨MonoidAlgebra.single 1 x, ?_⟩
  simp [augmentation]

theorem augmentationPower_zero : augmentationPower k G 0 = ⊤ := by
  ext x
  change x ∈ augmentationIdeal k G ^ 0 ↔ _
  simp only [Submodule.pow_zero, Ideal.one_eq_top, Submodule.mem_top]

theorem augmentationPower_one :
    augmentationPower k G 1 = LinearMap.ker (augmentation k G).toLinearMap := by
  ext x
  change x ∈ augmentationIdeal k G ^ 1 ↔ augmentation k G x = 0
  rw [Submodule.pow_one]
  rfl

variable [Finite G]

/-- The degree-`n` coefficient of the augmentation-graded Hilbert series. -/
noncomputable def hilbertCoeff (n : ℕ) : ℕ :=
  Module.finrank k (augmentationPower k G n) -
    Module.finrank k (augmentationPower k G (n + 1))

theorem hilbertCoeff_zero : hilbertCoeff k G 0 = 1 := by
  have hdim := LinearMap.finrank_range_add_finrank_ker (augmentation k G).toLinearMap
  rw [LinearMap.range_eq_top.mpr (augmentation_surjective k G),
    finrank_top, Module.finrank_self] at hdim
  rw [hilbertCoeff, augmentationPower_zero, augmentationPower_one, finrank_top]
  omega

omit [Finite G] in
theorem hilbertCoeff_nonneg (n : ℕ) : 0 ≤ (hilbertCoeff k G n : ℝ) := by
  positivity

theorem hilbertCoeff_eventually_zero :
    {n | hilbertCoeff k G n ≠ 0}.Finite := by
  let f (n : ℕ) := Module.finrank k (augmentationPower k G n)
  have hf : Antitone f := fun _ _ h ↦
    Submodule.finrank_mono ((augmentationPower_antitone k G) h)
  let b := sInf (Set.range f)
  have hbmem : b ∈ Set.range f := Nat.sInf_mem ⟨f 0, Set.mem_range_self 0⟩
  obtain ⟨N, hN⟩ := hbmem
  apply Set.Finite.subset (Set.finite_Iio N)
  intro n hn
  change n < N
  by_contra hnot
  have hNn : N ≤ n := Nat.le_of_not_gt hnot
  have hnN : f n = f N := le_antisymm (hf hNn) (by
    exact hN.trans_le (Nat.sInf_le (Set.mem_range_self n)))
  have hsnN : f (n + 1) = f N := le_antisymm (hf (hNn.trans (Nat.le_succ n))) (by
    exact hN.trans_le (Nat.sInf_le (Set.mem_range_self (n + 1))))
  apply hn
  change f n - f (n + 1) = 0
  rw [hnN, hsnN, Nat.sub_self]

/-- The (finite) Hilbert series of the augmentation filtration. -/
noncomputable def hilbertPolynomial : Polynomial ℝ :=
  Polynomial.ofFinsupp <| Finsupp.ofSupportFinite
    (fun n ↦ (hilbertCoeff k G n : ℝ)) (by
      apply (hilbertCoeff_eventually_zero k G).subset
      intro n hn
      change (hilbertCoeff k G n : ℝ) ≠ 0 at hn
      change hilbertCoeff k G n ≠ 0
      exact_mod_cast hn)

theorem coeff_hilbertPolynomial (n : ℕ) :
    (hilbertPolynomial k G).coeff n = hilbertCoeff k G n := by
  change (Finsupp.ofSupportFinite (fun n ↦ (hilbertCoeff k G n : ℝ)) _) n = _
  rw [Finsupp.ofSupportFinite_coe]

end Submission.Hilbert
