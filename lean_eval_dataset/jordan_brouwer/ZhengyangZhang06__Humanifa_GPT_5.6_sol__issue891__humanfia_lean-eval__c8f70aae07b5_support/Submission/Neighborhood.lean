import Submission.Extension

namespace Submission.Helpers

open Set

/-- A retraction of an open Euclidean neighborhood of a compact set becomes
a straight-line deformation retraction after shrinking the neighborhood.
The conclusion records exactly the segment-containment fact needed to bundle
the deformation as a homotopy. -/
theorem exists_open_segment_neighborhood_of_compact_retraction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (ρ : C(U, K))
    (hρ : ∀ x, ∀ hx : x ∈ K, (ρ ⟨x, hKU hx⟩ : E) = x) :
    ∃ V : Set U, IsOpen V ∧
      (∀ x, ∀ hx : x ∈ K, (⟨x, hKU hx⟩ : U) ∈ V) ∧
      ∀ x : U, x ∈ V → ∀ t : unitInterval,
        AffineMap.lineMap (x : E) (ρ x : E) (t : ℝ) ∈ U := by
  obtain ⟨δ, hδ, hthickening⟩ :=
    hK.exists_thickening_subset_open hU hKU
  let V : Set U := {x | dist (x : E) (ρ x : E) < δ}
  have hVOpen : IsOpen V := by
    apply isOpen_lt
    · exact continuous_subtype_val.dist
        (continuous_subtype_val.comp ρ.continuous)
    · exact continuous_const
  refine ⟨V, hVOpen, ?_, ?_⟩
  · intro x hx
    change dist x (ρ ⟨x, hKU hx⟩ : E) < δ
    rw [hρ x hx, dist_self]
    exact hδ
  · intro x hxV t
    change dist (x : E) (ρ x : E) < δ at hxV
    apply hthickening
    rw [Metric.mem_thickening_iff]
    refine ⟨(ρ x : E), (ρ x).property, ?_⟩
    rw [dist_lineMap_right, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr t.property.2)]
    calc
      (1 - (t : ℝ)) * dist (x : E) (ρ x : E) ≤
          1 * dist (x : E) (ρ x : E) := by
        gcongr
        linarith [t.property.1]
      _ < δ := by simpa only [one_mul] using hxV

/-- The embedded sphere is a retract of an explicit open neighborhood.  The
retraction is obtained by normalizing the strict extension of the inverse
embedding. -/
theorem exists_open_neighborhood_retraction (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) (hinj : Function.Injective r) :
    ∃ (U : Set (EuclideanSpace ℝ (Fin d)))
        (_hU : IsOpen U) (hrU : Set.range r ⊆ U)
        (ρ : C(U, Metric.sphere
          (0 : EuclideanSpace ℝ (Fin d)) 1)),
      ∀ z, ρ ⟨r z, hrU ⟨z, rfl⟩⟩ = z := by
  obtain ⟨f, hf, _hfle, _hflt⟩ :=
    exists_strict_unitBall_extension d hd r hcont hinj
  let U : Set (EuclideanSpace ℝ (Fin d)) := {x | (1 / 2 : ℝ) < ‖f x‖}
  have hUopen : IsOpen U := by
    exact isOpen_lt continuous_const f.continuous.norm
  have hrU (z : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin d)) 1) : r z ∈ U := by
    change (1 / 2 : ℝ) < ‖f (r z)‖
    rw [hf z]
    have hznorm : ‖(z : EuclideanSpace ℝ (Fin d))‖ = 1 := by
      exact mem_sphere_zero_iff_norm.mp z.property
    norm_num [hznorm]
  let ρ : C(U, Metric.sphere
      (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    { toFun := fun x ↦ ⟨NormedSpace.normalize (f x), by
        rw [mem_sphere_zero_iff_norm]
        apply NormedSpace.norm_normalize
        exact norm_ne_zero_iff.mp <| ne_of_gt <|
          (show (0 : ℝ) < 1 / 2 by norm_num).trans x.2⟩
      continuous_toFun := by
        have hv : Continuous (fun x : U ↦ f x) :=
          f.continuous.comp continuous_subtype_val
        apply Continuous.subtype_mk
        change Continuous (fun x : U ↦ ‖f x‖⁻¹ • f x)
        exact (hv.norm.inv₀ fun x ↦ ne_of_gt <|
          (show (0 : ℝ) < 1 / 2 by norm_num).trans x.2).smul hv }
  have hrangeU : Set.range r ⊆ U := by
    rintro _ ⟨z, rfl⟩
    exact hrU z
  refine ⟨U, hUopen, hrangeU, ρ, ?_⟩
  intro z
  apply Subtype.ext
  change NormedSpace.normalize (f (r z)) = z
  rw [hf z]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one <|
    mem_sphere_zero_iff_norm.mp z.property

/-- Equivalently, the image itself is a retract of an open ambient
neighborhood. -/
theorem exists_open_neighborhood_range_retraction (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) (hinj : Function.Injective r) :
    ∃ (U : Set (EuclideanSpace ℝ (Fin d)))
        (_hU : IsOpen U) (hrU : Set.range r ⊆ U)
        (ρ : C(U, Set.range r)),
      ∀ z, ρ ⟨r z, hrU ⟨z, rfl⟩⟩ =
        ⟨r z, ⟨z, rfl⟩⟩ := by
  obtain ⟨U, hU, hrU, ρ, hρ⟩ :=
    exists_open_neighborhood_retraction d hd r hcont hinj
  let ρrange : C(U, Set.range r) :=
    { toFun := fun x ↦ ⟨r (ρ x), ⟨ρ x, rfl⟩⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact hcont.comp ρ.continuous }
  refine ⟨U, hU, hrU, ρrange, ?_⟩
  intro z
  apply Subtype.ext
  change r (ρ ⟨r z, hrU ⟨z, rfl⟩⟩) = r z
  rw [hρ z]

/-- The neighborhood may be restricted to the open connected component that
contains the connected embedded sphere, without losing its retraction. -/
theorem exists_connected_open_neighborhood_range_retraction
    (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) (hinj : Function.Injective r) :
    ∃ (U : Set (EuclideanSpace ℝ (Fin d)))
        (_hUOpen : IsOpen U) (_hUConnected : IsConnected U)
        (hrU : Set.range r ⊆ U) (ρ : C(U, Set.range r)),
      ∀ z, ρ ⟨r z, hrU ⟨z, rfl⟩⟩ =
        ⟨r z, ⟨z, rfl⟩⟩ := by
  obtain ⟨W, hWOpen, hrW, ρ, hρ⟩ :=
    exists_open_neighborhood_range_retraction d hd r hcont hinj
  have hrangeConnected := sphere_range_connected d hd r hcont
  obtain ⟨p, hpRange⟩ := hrangeConnected.nonempty
  have hpW : p ∈ W := hrW hpRange
  let U := connectedComponentIn W p
  have hUOpen : IsOpen U := hWOpen.connectedComponentIn
  have hUConnected : IsConnected U :=
    isConnected_connectedComponentIn_iff.mpr hpW
  have hrU : Set.range r ⊆ U :=
    hrangeConnected.isPreconnected.subset_connectedComponentIn
      hpRange hrW
  let ρU : C(U, Set.range r) :=
    { toFun := fun x ↦
        ρ ⟨x, connectedComponentIn_subset W p x.property⟩
      continuous_toFun := by
        apply ρ.continuous.comp
        exact continuous_subtype_val.subtype_mk _ }
  refine ⟨U, hUOpen, hUConnected, hrU, ρU, ?_⟩
  intro z
  apply Subtype.ext
  change (ρ ⟨r z, _⟩ : EuclideanSpace ℝ (Fin d)) = r z
  exact congrArg Subtype.val (hρ z)

/-- The neighborhood retraction of the embedded sphere can be accompanied by
an open sub-neighborhood on which straight-line interpolation to the
retraction remains in the original neighborhood. -/
theorem exists_open_neighborhood_range_retraction_with_segments
    (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) (hinj : Function.Injective r) :
    ∃ (U : Set (EuclideanSpace ℝ (Fin d)))
        (_hU : IsOpen U) (hrU : Set.range r ⊆ U)
        (ρ : C(U, Set.range r)),
      (∀ z, ρ ⟨r z, hrU ⟨z, rfl⟩⟩ =
        ⟨r z, ⟨z, rfl⟩⟩) ∧
      ∃ V : Set U, IsOpen V ∧
        (∀ z, (⟨r z, hrU ⟨z, rfl⟩⟩ : U) ∈ V) ∧
        ∀ x : U, x ∈ V → ∀ t : unitInterval,
          AffineMap.lineMap
            (x : EuclideanSpace ℝ (Fin d))
            (ρ x : EuclideanSpace ℝ (Fin d)) (t : ℝ) ∈ U := by
  obtain ⟨U, hU, hrU, ρ, hρ⟩ :=
    exists_open_neighborhood_range_retraction d hd r hcont hinj
  refine ⟨U, hU, hrU, ρ, hρ, ?_⟩
  have hρall : ∀ x, ∀ hx : x ∈ Set.range r,
      (ρ ⟨x, hrU hx⟩ : EuclideanSpace ℝ (Fin d)) = x := by
    rintro _ ⟨z, rfl⟩
    exact congrArg Subtype.val (hρ z)
  obtain ⟨V, hVOpen, hrangeV, hsegments⟩ :=
    exists_open_segment_neighborhood_of_compact_retraction
      (isCompact_range hcont) hU hrU ρ hρall
  refine ⟨V, hVOpen, ?_, hsegments⟩
  intro z
  exact hrangeV (r z) ⟨z, rfl⟩

end Submission.Helpers
