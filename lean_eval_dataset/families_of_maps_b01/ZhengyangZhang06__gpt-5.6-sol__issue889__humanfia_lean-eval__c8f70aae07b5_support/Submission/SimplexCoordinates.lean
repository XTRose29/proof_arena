import Mathlib

open Set

namespace Submission.SimplexCoordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The affine combination map from the standard simplex on `D` to the
geometric simplex spanned by `D`. -/
noncomputable def combination (D : Finset E) : stdSimplex ℝ D → E :=
  fun w => ∑ i, w.1 i • i.1

theorem combination_mem (D : Finset E) (w : stdSimplex ℝ D) :
    combination D w ∈ convexHull ℝ (D : Set E) := by
  have h := affineCombination_mem_convexHull (s := Finset.univ)
    (v := ((↑) : D → E)) (w := w.1)
    (fun i _hi => w.2.1 i) (by simpa using w.2.2)
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using w.2.2)] at h
  simpa only [combination, Subtype.range_coe_subtype, Finset.setOf_mem,
    Finset.sum_filter] using h

theorem continuous_combination (D : Finset E) : Continuous (combination D) := by
  classical
  unfold combination
  apply continuous_finsetSum
  intro i _hi
  exact ((continuous_apply i).comp continuous_subtype_val).smul continuous_const

theorem injective_combination (D : Finset E)
    (hD : AffineIndependent ℝ ((↑) : D → E)) :
    Function.Injective (combination D) := by
  intro w z hwz
  apply Subtype.ext
  funext i
  have hwz' : Finset.univ.affineCombination ℝ ((↑) : D → E) w.1 =
      Finset.univ.affineCombination ℝ ((↑) : D → E) z.1 := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using w.2.2),
      Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using z.2.2)]
    exact hwz
  have hweights := (hD.affineCombination_eq_iff_eq
    (s := Finset.univ) (by simpa using w.2.2) (by simpa using z.2.2)).mp hwz'
  exact hweights i (Finset.mem_univ i)

theorem surjective_combination (D : Finset E) :
    Function.Surjective fun w : stdSimplex ℝ D =>
      (⟨combination D w, combination_mem D w⟩ : convexHull ℝ (D : Set E)) := by
  classical
  intro x
  have hx : x.1 ∈ convexHull ℝ (Set.range ((↑) : D → E)) := by
    simpa only [Subtype.range_coe_subtype, Finset.setOf_mem] using x.2
  rw [convexHull_range_eq_exists_affineCombination] at hx
  obtain ⟨s, w, hw_nonneg, hw_sum, hw_eq⟩ := hx
  let W : D → ℝ := fun i => if i ∈ s then w i else 0
  have hW_nonneg : ∀ i, 0 ≤ W i := by
    intro i
    by_cases hi : i ∈ s
    · simpa [W, hi] using hw_nonneg i hi
    · simp [W, hi]
  have hW_sum : ∑ i, W i = 1 := by
    calc
      ∑ i, W i = ∑ i ∈ s, W i := by
        symm
        apply Finset.sum_subset (Finset.subset_univ s)
        intro i _hi hi
        simp [W, hi]
      _ = ∑ i ∈ s, w i := by simp [W]
      _ = 1 := hw_sum
  let W' : stdSimplex ℝ D := ⟨W, hW_nonneg, hW_sum⟩
  refine ⟨W', Subtype.ext ?_⟩
  change combination D W' = x.1
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hw_sum] at hw_eq
  calc
    combination D W' = ∑ i ∈ s, W i • i.1 := by
      unfold combination
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro i _hi hi
      simp [W, hi]
    _ = ∑ i ∈ s, w i • i.1 := by simp [W]
    _ = x.1 := hw_eq

/-- Affine-independent finite simplices are homeomorphic to their standard
simplex of barycentric coordinates. -/
noncomputable def homeomorph (D : Finset E)
    (hD : AffineIndependent ℝ ((↑) : D → E)) :
    stdSimplex ℝ D ≃ₜ convexHull ℝ (D : Set E) := by
  let f : stdSimplex ℝ D → convexHull ℝ (D : Set E) :=
    fun w => ⟨combination D w, combination_mem D w⟩
  have hf_injective : Function.Injective f := by
    intro w z hwz
    apply injective_combination D hD
    exact congrArg Subtype.val hwz
  have hf_surjective : Function.Surjective f := by
    simpa only [f] using surjective_combination D
  let e : stdSimplex ℝ D ≃ convexHull ℝ (D : Set E) :=
    Equiv.ofBijective f ⟨hf_injective, hf_surjective⟩
  exact (continuous_combination D).subtype_mk _ |>.homeoOfEquivCompactToT2 (f := e)

@[simp]
theorem homeomorph_apply (D : Finset E)
    (hD : AffineIndependent ℝ ((↑) : D → E)) (w : stdSimplex ℝ D) :
    (homeomorph D hD w : E) = combination D w :=
  rfl

section Family

variable {ι : Type*} [Fintype ι]

/-- Affine combination for an arbitrary finite indexed family. -/
noncomputable def combinationOf (v : ι → E) (w : stdSimplex ℝ ι) : E :=
  ∑ i, w.1 i • v i

theorem combinationOf_mem (v : ι → E) (w : stdSimplex ℝ ι) :
    combinationOf v w ∈ convexHull ℝ (Set.range v) := by
  have h := affineCombination_mem_convexHull (s := Finset.univ) (v := v) (w := w.1)
    (fun i _hi => w.2.1 i) (by simpa using w.2.2)
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using w.2.2)] at h
  simpa only [combinationOf, Finset.coe_univ, Set.image_univ] using h

theorem continuous_combinationOf (v : ι → E) : Continuous (combinationOf v) := by
  classical
  unfold combinationOf
  apply continuous_finsetSum
  intro i _hi
  exact ((continuous_apply i).comp continuous_subtype_val).smul continuous_const

theorem combinationOf_map {κ : Type*} [Fintype κ] (f : κ → ι)
    (v : ι → E) (w : stdSimplex ℝ κ) :
    combinationOf v (stdSimplex.map f w) = combinationOf (v ∘ f) w := by
  classical
  unfold combinationOf
  change (∑ j, (FunOnFinite.linearMap ℝ ℝ f w.1) j • v j) =
    ∑ i, w.1 i • v (f i)
  simp only [FunOnFinite.linearMap_apply_apply]
  calc
    ∑ j, (∑ i with f i = j, w.1 i) • v j =
        ∑ j, ∑ i with f i = j, w.1 i • v j := by
      apply Fintype.sum_congr
      intro j
      rw [Finset.sum_smul]
    _ = ∑ j, ∑ i with f i = j, w.1 i • v (f i) := by
      apply Fintype.sum_congr
      intro j
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = ∑ i, w.1 i • v (f i) := by
      simpa using Finset.sum_fiberwise (Finset.univ : Finset κ) f
        (fun i => w.1 i • v (f i))

theorem injective_combinationOf (v : ι → E) (hv : AffineIndependent ℝ v) :
    Function.Injective (combinationOf v) := by
  intro w z hwz
  apply Subtype.ext
  funext i
  have hwz' : Finset.univ.affineCombination ℝ v w.1 =
      Finset.univ.affineCombination ℝ v z.1 := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using w.2.2),
      Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using z.2.2)]
    exact hwz
  have hweights := (hv.affineCombination_eq_iff_eq
    (s := Finset.univ) (by simpa using w.2.2) (by simpa using z.2.2)).mp hwz'
  exact hweights i (Finset.mem_univ i)

theorem surjective_combinationOf (v : ι → E) :
    Function.Surjective fun w : stdSimplex ℝ ι =>
      (⟨combinationOf v w, combinationOf_mem v w⟩ : convexHull ℝ (Set.range v)) := by
  classical
  intro x
  have hx : ∃ (s : Finset ι) (w : ι → ℝ),
      (∀ i ∈ s, 0 ≤ w i) ∧ ∑ i ∈ s, w i = 1 ∧
        s.affineCombination ℝ v w = x.1 := by
    simpa only [convexHull_range_eq_exists_affineCombination, Set.mem_setOf_eq] using x.2
  obtain ⟨s, w, hw_nonneg, hw_sum, hw_eq⟩ := hx
  let W : ι → ℝ := fun i => if i ∈ s then w i else 0
  have hW_nonneg : ∀ i, 0 ≤ W i := by
    intro i
    by_cases hi : i ∈ s
    · simpa [W, hi] using hw_nonneg i hi
    · simp [W, hi]
  have hW_sum : ∑ i, W i = 1 := by
    calc
      ∑ i, W i = ∑ i ∈ s, W i := by
        symm
        apply Finset.sum_subset (Finset.subset_univ s)
        intro i _hi hi
        simp [W, hi]
      _ = ∑ i ∈ s, w i := by simp [W]
      _ = 1 := hw_sum
  let W' : stdSimplex ℝ ι := ⟨W, hW_nonneg, hW_sum⟩
  refine ⟨W', Subtype.ext ?_⟩
  change combinationOf v W' = x.1
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hw_sum] at hw_eq
  calc
    combinationOf v W' = ∑ i ∈ s, W i • v i := by
      unfold combinationOf
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro i _hi hi
      simp [W, hi]
    _ = ∑ i ∈ s, w i • v i := by simp [W]
    _ = x.1 := hw_eq

noncomputable def homeomorphOf (v : ι → E) (hv : AffineIndependent ℝ v) :
    stdSimplex ℝ ι ≃ₜ convexHull ℝ (Set.range v) := by
  let f : stdSimplex ℝ ι → convexHull ℝ (Set.range v) :=
    fun w => ⟨combinationOf v w, combinationOf_mem v w⟩
  have hf_injective : Function.Injective f := by
    intro w z hwz
    apply injective_combinationOf v hv
    exact congrArg Subtype.val hwz
  have hf_surjective : Function.Surjective f := by
    simpa only [f] using surjective_combinationOf v
  let e : stdSimplex ℝ ι ≃ convexHull ℝ (Set.range v) :=
    Equiv.ofBijective f ⟨hf_injective, hf_surjective⟩
  exact (continuous_combinationOf v).subtype_mk _ |>.homeoOfEquivCompactToT2 (f := e)

@[simp]
theorem homeomorphOf_apply (v : ι → E) (hv : AffineIndependent ℝ v)
    (w : stdSimplex ℝ ι) :
    (homeomorphOf v hv w : E) = combinationOf v w :=
  rfl

end Family

end Submission.SimplexCoordinates
