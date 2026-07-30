import ChallengeDeps
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Module.Span
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open LeanEval.Geometry
open MeasureTheory Metric Set Function
open scoped RealInnerProductSpace

namespace Submission.Hyperplane

noncomputable section

/-- The hyperplane perpendicular to a chosen direction. -/
def perp {n : ℕ} (u : E n) : Submodule ℝ (E n) := (ℝ ∙ u)ᗮ

/-- Orthonormal coordinates on the hyperplane perpendicular to `u`. -/
def perpBasis {n : ℕ} (hn : 1 ≤ n) (u : E n) (hu : ‖u‖ = 1) :
    OrthonormalBasis (Fin (n - 1)) ℝ (perp u) := by
  letI : Fact (Module.finrank ℝ (E n) = (n - 1) + 1) := ⟨by simp [Nat.sub_add_cancel hn]⟩
  exact OrthonormalBasis.fromOrthogonalSpanSingleton (n - 1) (by
    intro hzero
    rw [hzero, norm_zero] at hu
    norm_num at hu)

/-- Unit-speed coordinates on the line spanned by `u`, regarded as the orthogonal complement
of `uᵊ`. -/
def lineEquiv {n : ℕ} (u : E n) (hu : ‖u‖ = 1) : ℝ ≃ₗᵢ[ℝ] (perp u)ᗮ :=
  (LinearIsometryEquiv.toSpanUnitSingleton u hu).trans
    (LinearIsometryEquiv.ofEq _ _ (by
      change (ℝ ∙ u) = ((ℝ ∙ u)ᗮ)ᗮ
      exact (Submodule.orthogonal_orthogonal (K := ℝ ∙ u)).symm))

/-- Orthogonal coordinates, with a transverse point followed by the coordinate in direction `u`. -/
def coords {n : ℕ} (hn : 1 ≤ n) (u : E n) (hu : ‖u‖ = 1) :
    E n ≃ₗᵢ[ℝ] WithLp 2 (E (n - 1) × ℝ) :=
  (perp u).orthogonalDecomposition.trans
    (LinearIsometryEquiv.withLpProdCongr 2 (perpBasis hn u hu).repr (lineEquiv u hu).symm)

/-- The measure-preserving parametrization `(z,t) ↦ z + t u` associated to `coords`. -/
def parametrization {n : ℕ} (hn : 1 ≤ n) (u : E n) (hu : ‖u‖ = 1) :
    E (n - 1) × ℝ ≃ᵐ E n :=
  (MeasurableEquiv.toLp 2 (E (n - 1) × ℝ)).trans (coords hn u hu).symm.toMeasurableEquiv

/-- Orthogonal projection written in Euclidean coordinates. -/
def projection {n : ℕ} (hn : 1 ≤ n) (u : E n) (hu : ‖u‖ = 1) (x : E n) : E (n - 1) :=
  (coords hn u hu x).fst

theorem measurePreserving_parametrization {n : ℕ} (hn : 1 ≤ n) (u : E n)
    (hu : ‖u‖ = 1) : MeasurePreserving (parametrization hn u hu) :=
  (LinearIsometryEquiv.measurePreserving (coords hn u hu).symm).comp
    (WithLp.volume_preserving_toLp (E (n - 1)) ℝ)

theorem projection_lipschitzWith {n : ℕ} (hn : 1 ≤ n) (u : E n) (hu : ‖u‖ = 1) :
    LipschitzWith 1 (projection hn u hu) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  change dist (coords hn u hu x).fst (coords hn u hu y).fst ≤ dist x y
  rw [dist_eq_norm, dist_eq_norm]
  have hsub : (coords hn u hu x).fst - (coords hn u hu y).fst =
      (coords hn u hu (x - y)).fst := by
    rw [map_sub]
    rfl
  rw [hsub]
  calc
    ‖(coords hn u hu (x - y)).fst‖ ≤ ‖coords hn u hu (x - y)‖ :=
      WithLp.norm_fst_le (E (n - 1)) _
    _ = ‖x - y‖ := (coords hn u hu).norm_map (x - y)

@[simp]
theorem projection_parametrization {n : ℕ} (hn : 1 ≤ n) (u : E n) (hu : ‖u‖ = 1)
    (z : E (n - 1)) (t : ℝ) :
    projection hn u hu (parametrization hn u hu (z, t)) = z := by
  simp [projection, parametrization]

theorem parametrization_apply {n : ℕ} (hn : 1 ≤ n) (u : E n) (hu : ‖u‖ = 1)
    (z : E (n - 1)) (t : ℝ) :
    parametrization hn u hu (z, t) =
      ((perpBasis hn u hu).repr.symm z : E n) + t • u := by
  change (perp u).orthogonalDecomposition.symm
      ((LinearIsometryEquiv.withLpProdCongr 2 (perpBasis hn u hu).repr
        (lineEquiv u hu).symm).symm (WithLp.toLp 2 (z, t))) = _
  rw [LinearIsometryEquiv.withLpProdCongr_symm_apply,
    Submodule.orthogonalDecomposition_symm_apply]
  simp [LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply, lineEquiv]

theorem parametrization_add_line {n : ℕ} (hn : 1 ≤ n) (u : E n) (hu : ‖u‖ = 1)
    (z : E (n - 1)) (s t : ℝ) :
    parametrization hn u hu (z, s + t) = parametrization hn u hu (z, s) + t • u := by
  simp only [parametrization_apply hn u hu, add_smul]
  abel

theorem norm_snd_le_parametrization {n : ℕ} (hn : 1 ≤ n) (u : E n) (hu : ‖u‖ = 1)
    (z : E (n - 1)) (t : ℝ) : ‖t‖ ≤ ‖parametrization hn u hu (z, t)‖ := by
  calc
    ‖t‖ ≤ ‖WithLp.toLp 2 (z, t)‖ := by
      simpa using WithLp.norm_snd_le (E (n - 1)) (WithLp.toLp 2 (z, t))
    _ = ‖parametrization hn u hu (z, t)‖ := by
      change ‖WithLp.toLp 2 (z, t)‖ = ‖(coords hn u hu).symm (WithLp.toLp 2 (z, t))‖
      rw [(coords hn u hu).symm.norm_map]

theorem parametrization_zero_inner {n : ℕ} (hn : 1 ≤ n) (u : E n) (hu : ‖u‖ = 1)
    (z : E (n - 1)) : ⟪parametrization hn u hu (z, 0), u⟫ = 0 := by
  rw [parametrization_apply]
  simp only [zero_smul, add_zero]
  exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp
    ((perpBasis hn u hu).repr.symm z).property

end

end Submission.Hyperplane
