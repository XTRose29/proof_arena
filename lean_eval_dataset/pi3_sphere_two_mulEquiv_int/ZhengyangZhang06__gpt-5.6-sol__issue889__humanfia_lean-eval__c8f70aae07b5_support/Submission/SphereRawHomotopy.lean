import Mathlib
import Submission.SphereHomotopy

open scoped unitInterval

noncomputable section

namespace Submission.SphereRawHomotopy

open AffineMap
open Submission.SphereHomotopy

variable {A E : Type*} [TopologicalSpace A]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem map_ne_zero_of_dist_lt_one
    (f : C(A, UnitSphere (E := E))) (g : C(A, E))
    (hfg : ∀ a, dist (f a : E) (g a) < 1) (a : A) :
    g a ≠ 0 := by
  intro hzero
  have h := hfg a
  rw [hzero, dist_zero_right, norm_coe_unitSphere] at h
  linarith

/-- Normalize a continuous nonvanishing vector-valued map. -/
def normalizeMap (g : C(A, E)) (hg : ∀ a, g a ≠ 0) :
    C(A, UnitSphere (E := E)) where
  toFun a :=
    ⟨NormedSpace.normalize (g a), by
      rw [Metric.mem_sphere, dist_zero_right]
      exact NormedSpace.norm_normalize (hg a)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    change Continuous (fun a => ‖g a‖⁻¹ • g a)
    exact
      (g.continuous.norm.inv₀ fun a =>
        norm_ne_zero_iff.mpr (hg a)).smul g.continuous

/-- The affine line from a sphere-valued map to a nearby vector-valued map. -/
def rawLine (f : C(A, UnitSphere (E := E))) (g : C(A, E))
    (z : I × A) : E :=
  lineMap (f z.2 : E) (g z.2) (z.1 : ℝ)

theorem continuous_rawLine
    (f : C(A, UnitSphere (E := E))) (g : C(A, E)) :
    Continuous (rawLine f g) := by
  apply Continuous.lineMap
  · exact continuous_subtype_val.comp (f.continuous.comp continuous_snd)
  · exact g.continuous.comp continuous_snd
  · exact continuous_subtype_val.comp continuous_fst

theorem rawLine_ne_zero
    (f : C(A, UnitSphere (E := E))) (g : C(A, E))
    (hfg : ∀ a, dist (f a : E) (g a) < 1) (z : I × A) :
    rawLine f g z ≠ 0 := by
  intro hz
  have hleft :=
    dist_left_lineMap (f z.2 : E) (g z.2) (z.1 : ℝ)
  rw [rawLine] at hz
  rw [hz, dist_zero_right, norm_coe_unitSphere] at hleft
  have ht0 : 0 ≤ (z.1 : ℝ) := z.1.property.1
  have ht1 : (z.1 : ℝ) ≤ 1 := z.1.property.2
  rw [Real.norm_eq_abs, abs_of_nonneg ht0] at hleft
  have hprod :
      (z.1 : ℝ) * dist (f z.2 : E) (g z.2) < 1 := by
    calc
      (z.1 : ℝ) * dist (f z.2 : E) (g z.2) ≤
          1 * dist (f z.2 : E) (g z.2) :=
        mul_le_mul_of_nonneg_right ht1 dist_nonneg
      _ = dist (f z.2 : E) (g z.2) := one_mul _
      _ < 1 := hfg z.2
  linarith

/-- Normalized straight-line homotopy from a sphere-valued map to the
normalization of any vector-valued map less than distance one away. -/
def normalizedRawHomotopy
    (f : C(A, UnitSphere (E := E))) (g : C(A, E))
    (hfg : ∀ a, dist (f a : E) (g a) < 1) :
    f.Homotopy (normalizeMap g (map_ne_zero_of_dist_lt_one f g hfg)) where
  toFun z :=
    ⟨NormedSpace.normalize (rawLine f g z), by
      rw [Metric.mem_sphere, dist_zero_right]
      exact NormedSpace.norm_normalize (rawLine_ne_zero f g hfg z)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    change Continuous (fun z => ‖rawLine f g z‖⁻¹ • rawLine f g z)
    exact
      ((continuous_rawLine f g).norm.inv₀ fun z =>
        norm_ne_zero_iff.mpr (rawLine_ne_zero f g hfg z)).smul
          (continuous_rawLine f g)
  map_zero_left a := by
    apply Subtype.ext
    change NormedSpace.normalize (rawLine f g (0, a)) = f a
    rw [rawLine, show ((0 : I) : ℝ) = 0 by rfl, lineMap_apply_zero]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one (norm_coe_unitSphere (f a))
  map_one_left a := by
    apply Subtype.ext
    change
      NormedSpace.normalize (rawLine f g (1, a)) =
        NormedSpace.normalize (g a)
    rw [rawLine, show ((1 : I) : ℝ) = 1 by rfl, lineMap_apply_one]

/-- The normalized straight-line homotopy is relative to any set on which
the raw approximation agrees with the original sphere-valued map. -/
def normalizedRawHomotopyRel
    (f : C(A, UnitSphere (E := E))) (g : C(A, E))
    (hfg : ∀ a, dist (f a : E) (g a) < 1) (s : Set A)
    (hrel : ∀ a ∈ s, g a = (f a : E)) :
    f.HomotopyRel
      (normalizeMap g (map_ne_zero_of_dist_lt_one f g hfg)) s where
  toHomotopy := normalizedRawHomotopy f g hfg
  prop' t a ha := by
    apply Subtype.ext
    change
      NormedSpace.normalize
          (lineMap (f a : E) (g a) (t : ℝ)) =
        (f a : E)
    rw [hrel a ha, lineMap_apply]
    simp only [vsub_self, smul_zero, zero_vadd]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one (norm_coe_unitSphere (f a))

end Submission.SphereRawHomotopy
