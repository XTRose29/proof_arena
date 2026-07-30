import Mathlib

open scoped unitInterval

noncomputable section

namespace Submission.SphereHomotopy

open AffineMap

variable {A E : Type*} [TopologicalSpace A]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev UnitSphere :=
  Metric.sphere (0 : E) 1

omit [NormedSpace ℝ E] in
theorem norm_coe_unitSphere (y : UnitSphere (E := E)) :
    ‖(y : E)‖ = 1 := by
  have hy : dist (y : E) 0 = 1 := y.property
  simpa only [dist_zero_right] using hy

/-- The unnormalized affine interpolation between two sphere-valued maps. -/
def lineRaw (f g : C(A, UnitSphere (E := E))) (z : I × A) : E :=
  lineMap (f z.2 : E) (g z.2 : E) (z.1 : ℝ)

theorem continuous_lineRaw (f g : C(A, UnitSphere (E := E))) :
    Continuous (lineRaw f g) := by
  apply Continuous.lineMap
  · exact continuous_subtype_val.comp (f.continuous.comp continuous_snd)
  · exact continuous_subtype_val.comp (g.continuous.comp continuous_snd)
  · exact continuous_subtype_val.comp continuous_fst

theorem lineRaw_ne_zero (f g : C(A, UnitSphere (E := E)))
    (hfg : ∀ a, dist (f a) (g a) < 2) (z : I × A) :
    lineRaw f g z ≠ 0 := by
  intro hz
  have hleft :=
    dist_left_lineMap (f z.2 : E) (g z.2 : E) (z.1 : ℝ)
  have hright :=
    dist_right_lineMap (f z.2 : E) (g z.2 : E) (z.1 : ℝ)
  rw [lineRaw] at hz
  rw [hz, dist_zero_right, norm_coe_unitSphere] at hleft hright
  have ht0 : 0 ≤ (z.1 : ℝ) := z.1.property.1
  have ht1 : (z.1 : ℝ) ≤ 1 := z.1.property.2
  rw [Real.norm_eq_abs, abs_of_nonneg ht0] at hleft
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht1)] at hright
  have hdist :
      dist (f z.2 : E) (g z.2 : E) =
        dist (f z.2) (g z.2) :=
    rfl
  rw [hdist] at hleft hright
  linarith [hfg z.2]

/-- Normalize the affine interpolation between two pointwise non-antipodal
sphere-valued maps. -/
def normalizedLineHomotopy (f g : C(A, UnitSphere (E := E)))
    (hfg : ∀ a, dist (f a) (g a) < 2) :
    f.Homotopy g where
  toFun z :=
    ⟨NormedSpace.normalize (lineRaw f g z), by
      rw [Metric.mem_sphere, dist_zero_right]
      exact NormedSpace.norm_normalize (lineRaw_ne_zero f g hfg z)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    change Continuous
      (fun z => ‖lineRaw f g z‖⁻¹ • lineRaw f g z)
    exact
      ((continuous_lineRaw f g).norm.inv₀ fun z =>
        norm_ne_zero_iff.mpr (lineRaw_ne_zero f g hfg z)).smul
          (continuous_lineRaw f g)
  map_zero_left a := by
    apply Subtype.ext
    change NormedSpace.normalize (lineRaw f g (0, a)) = f a
    rw [lineRaw, show ((0 : I) : ℝ) = 0 by rfl, lineMap_apply_zero]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one (norm_coe_unitSphere (f a))
  map_one_left a := by
    apply Subtype.ext
    change NormedSpace.normalize (lineRaw f g (1, a)) = g a
    rw [lineRaw, show ((1 : I) : ℝ) = 1 by rfl, lineMap_apply_one]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one (norm_coe_unitSphere (g a))

/-- The normalized affine homotopy is relative to every set on which its
endpoint maps agree. -/
def normalizedLineHomotopyRel (f g : C(A, UnitSphere (E := E)))
    (hfg : ∀ a, dist (f a) (g a) < 2) (s : Set A)
    (hrel : ∀ a ∈ s, f a = g a) :
    f.HomotopyRel g s where
  toHomotopy := normalizedLineHomotopy f g hfg
  prop' t a ha := by
    apply Subtype.ext
    change
      NormedSpace.normalize
          (lineMap (f a : E) (g a : E) (t : ℝ)) =
        (f a : E)
    rw [congrArg Subtype.val (hrel a ha), lineMap_apply]
    simp only [vsub_self, smul_zero, zero_vadd]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one (norm_coe_unitSphere (g a))

theorem genLoop_homotopic_of_dist_lt_two
    {N : Type*} {x : UnitSphere (E := E)}
    (p q : GenLoop N (UnitSphere (E := E)) x)
    (hpq : ∀ t, dist (p t) (q t) < 2) :
    GenLoop.Homotopic p q := by
  refine ⟨normalizedLineHomotopyRel p.1 q.1 hpq (Cube.boundary N) ?_⟩
  intro t ht
  exact (p.property t ht).trans (q.property t ht).symm

end Submission.SphereHomotopy
