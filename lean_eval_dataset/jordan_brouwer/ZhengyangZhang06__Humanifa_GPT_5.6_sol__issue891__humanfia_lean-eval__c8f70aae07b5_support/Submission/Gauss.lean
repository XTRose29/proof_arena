import Submission.Helpers

namespace Submission.Helpers

open Set

private theorem gaussVector_ne_zero (d : ℕ)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (x : ((Set.range r)ᶜ : Set (EuclideanSpace ℝ (Fin d))))
    (z : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin d)) 1) :
    r z - (x : EuclideanSpace ℝ (Fin d)) ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  exact x.2 ⟨z, h⟩

/-- Looking from a point in the complement toward the embedded sphere and
normalizing gives a continuous self-map of the standard sphere. -/
noncomputable def gaussMap (d : ℕ)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r)
    (x : ((Set.range r)ᶜ : Set (EuclideanSpace ℝ (Fin d)))) :
    C(Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) where
  toFun z := ⟨NormedSpace.normalize (r z - (x : EuclideanSpace ℝ (Fin d))), by
    rw [mem_sphere_zero_iff_norm]
    exact NormedSpace.norm_normalize (gaussVector_ne_zero d r x z)⟩
  continuous_toFun := by
    have hv : Continuous
        (fun z ↦ r z - (x : EuclideanSpace ℝ (Fin d))) :=
      hcont.sub continuous_const
    apply Continuous.subtype_mk
    · change Continuous (fun z ↦
        ‖r z - (x : EuclideanSpace ℝ (Fin d))‖⁻¹ •
          (r z - (x : EuclideanSpace ℝ (Fin d))))
      exact (hv.norm.inv₀ fun z ↦
        norm_ne_zero_iff.mpr (gaussVector_ne_zero d r x z)).smul hv

/-- The Gauss maps vary continuously in both the complementary point and the
point of the source sphere. -/
noncomputable def gaussMapFamily (d : ℕ)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) :
    C(((Set.range r)ᶜ : Set (EuclideanSpace ℝ (Fin d))) × Metric.sphere
        (0 : EuclideanSpace ℝ (Fin d)) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) where
  toFun q := gaussMap d r hcont q.1 q.2
  continuous_toFun := by
    have hv : Continuous (fun q :
        ((Set.range r)ᶜ : Set (EuclideanSpace ℝ (Fin d))) × Metric.sphere
        (0 : EuclideanSpace ℝ (Fin d)) 1 ↦
        r q.2 - (q.1 : EuclideanSpace ℝ (Fin d))) :=
      (hcont.comp continuous_snd).sub
        (continuous_subtype_val.comp continuous_fst)
    apply Continuous.subtype_mk
    · change Continuous (fun q :
        ((Set.range r)ᶜ : Set (EuclideanSpace ℝ (Fin d))) × Metric.sphere
          (0 : EuclideanSpace ℝ (Fin d)) 1 ↦
        ‖r q.2 - (q.1 : EuclideanSpace ℝ (Fin d))‖⁻¹ •
          (r q.2 - (q.1 : EuclideanSpace ℝ (Fin d))))
      exact (hv.norm.inv₀ fun q ↦
        norm_ne_zero_iff.mpr (gaussVector_ne_zero d r q.1 q.2)).smul hv

/-- A path in the complement gives a homotopy between the Gauss maps at its
endpoints.  Thus any future degree invariant of these maps automatically
descends to complementary connected components. -/
noncomputable def gaussMapHomotopyOfPath (d : ℕ)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r)
    {x y : ((Set.range r)ᶜ : Set (EuclideanSpace ℝ (Fin d)))}
    (γ : Path x y) :
    (gaussMap d r hcont x).Homotopy (gaussMap d r hcont y) where
  toFun q := gaussMapFamily d r hcont (γ q.1, q.2)
  continuous_toFun :=
    (gaussMapFamily d r hcont).continuous.comp
      ((γ.continuous.comp continuous_fst).prodMk continuous_snd)
  map_zero_left z := by
    change gaussMap d r hcont (γ 0) z = gaussMap d r hcont x z
    rw [γ.source]
  map_one_left z := by
    change gaussMap d r hcont (γ 1) z = gaussMap d r hcont y z
    rw [γ.target]

/-- Gauss maps based at points in the same complementary connected component
are homotopic. -/
theorem gaussMap_homotopic_of_connectedComponent_eq (d : ℕ)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) (hinj : Function.Injective r)
    {x y : ((Set.range r)ᶜ : Set (EuclideanSpace ℝ (Fin d)))}
    (hxy : connectedComponent x = connectedComponent y) :
    ContinuousMap.Homotopic (gaussMap d r hcont x)
      (gaussMap d r hcont y) := by
  letI : LocPathConnectedSpace
      ((Set.range r)ᶜ : Set (EuclideanSpace ℝ (Fin d))) :=
    locPathConnectedSpace_compl_range_sphere_embedding d r hcont hinj
  have hjoined : Joined x y :=
    (connectedComponent_eq_iff_joined x y).mp hxy
  exact ⟨gaussMapHomotopyOfPath d r hcont hjoined.somePath⟩

/-- Homotopy classes of continuous self-maps of the relevant unit sphere. -/
def sphereSelfMapHomotopySetoid (d : ℕ) : Setoid
    C(Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) where
  r := ContinuousMap.Homotopic
  iseqv := ContinuousMap.Homotopic.equivalence

/-- The normalized Gauss construction descends from complementary points to
complementary connected components. -/
noncomputable def gaussClassMap (d : ℕ)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) (hinj : Function.Injective r) :
    ConnectedComponents
        ((Set.range r)ᶜ : Set (EuclideanSpace ℝ (Fin d))) →
      Quotient (sphereSelfMapHomotopySetoid d) :=
  Quotient.map
    (fun x ↦ gaussMap d r hcont x)
    (fun _x _y hxy ↦
      gaussMap_homotopic_of_connectedComponent_eq d r hcont hinj hxy)

/-- If the observation point has norm larger than every point of the embedded
sphere, its Gauss map is homotopic to a constant map. -/
theorem gaussMap_homotopic_const_of_norm (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r)
    (x : ((Set.range r)ᶜ : Set (EuclideanSpace ℝ (Fin d))))
    (hx : ∀ z, ‖r z‖ < ‖(x : EuclideanSpace ℝ (Fin d))‖) :
    ∃ c : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      ContinuousMap.Homotopic (gaussMap d r hcont x)
        (ContinuousMap.const _ c) := by
  obtain ⟨z₀, hz₀⟩ :=
    (isConnected_sphere (euclidean_rank_gt_one d hd) 0
      (show (0 : ℝ) ≤ 1 by norm_num)).nonempty
  let z : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 := ⟨z₀, hz₀⟩
  have hxzero : (x : EuclideanSpace ℝ (Fin d)) ≠ 0 := by
    intro hzero
    have h := hx z
    rw [hzero, norm_zero] at h
    exact (not_lt_of_ge (norm_nonneg (r z))) h
  let c : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 :=
    ⟨NormedSpace.normalize (-(x : EuclideanSpace ℝ (Fin d))), by
      rw [mem_sphere_zero_iff_norm]
      exact NormedSpace.norm_normalize (neg_ne_zero.mpr hxzero)⟩
  let v : unitInterval × Metric.sphere
      (0 : EuclideanSpace ℝ (Fin d)) 1 → EuclideanSpace ℝ (Fin d) :=
    fun q ↦ (1 - (q.1 : ℝ)) • r q.2 - (x : EuclideanSpace ℝ (Fin d))
  have hv_ne (q : unitInterval × Metric.sphere
      (0 : EuclideanSpace ℝ (Fin d)) 1) : v q ≠ 0 := by
    intro hq
    have heq : (x : EuclideanSpace ℝ (Fin d)) =
        (1 - (q.1 : ℝ)) • r q.2 := by
      exact (sub_eq_zero.mp hq).symm
    have ha0 : 0 ≤ 1 - (q.1 : ℝ) := sub_nonneg.mpr q.1.2.2
    have ha1 : 1 - (q.1 : ℝ) ≤ 1 := by linarith [q.1.2.1]
    have hnorm : ‖(x : EuclideanSpace ℝ (Fin d))‖ ≤ ‖r q.2‖ := by
      calc
        ‖(x : EuclideanSpace ℝ (Fin d))‖ =
            ‖(1 - (q.1 : ℝ)) • r q.2‖ := congrArg norm heq
        _ = (1 - (q.1 : ℝ)) * ‖r q.2‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha0]
        _ ≤ 1 * ‖r q.2‖ :=
          mul_le_mul_of_nonneg_right ha1 (norm_nonneg (r q.2))
        _ = ‖r q.2‖ := one_mul _
    exact (not_le_of_gt (hx q.2)) hnorm
  have hv : Continuous v := by
    dsimp [v]
    exact ((continuous_const.sub
      (continuous_subtype_val.comp continuous_fst)).smul
        (hcont.comp continuous_snd)).sub continuous_const
  refine ⟨c, ⟨{
    toFun := fun q ↦
      ⟨NormedSpace.normalize (v q), by
        rw [mem_sphere_zero_iff_norm]
        exact NormedSpace.norm_normalize (hv_ne q)⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      change Continuous (fun q ↦ ‖v q‖⁻¹ • v q)
      exact (hv.norm.inv₀ fun q ↦ norm_ne_zero_iff.mpr (hv_ne q)).smul hv
    map_zero_left := by
      intro w
      apply Subtype.ext
      simp [v, gaussMap]
    map_one_left := by
      intro w
      apply Subtype.ext
      simp [v, c]
  }⟩⟩

end Submission.Helpers
