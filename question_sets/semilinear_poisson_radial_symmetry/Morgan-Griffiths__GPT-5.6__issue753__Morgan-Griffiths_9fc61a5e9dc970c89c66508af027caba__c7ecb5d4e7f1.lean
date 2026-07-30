import Mathlib
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

-- BEGIN INLINED FILE: Mathlib/Support/semilinear_poisson_radial_symmetry_0e8f4ce1bc/Linearize.lean
open scoped NNReal

namespace SemilinearPoissonSupport

/-- Difference quotients of a Lipschitz real nonlinearity can be chosen at
zero differences too. This is the bounded coefficient in the reflected
linear equation. -/
lemma lipschitz_secant {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (a b : ℝ) :
    ∃ c : ℝ, |c| ≤ (K:ℝ) ∧ f a - f b = c * (a - b) := by
  by_cases hab : a = b
  · subst b
    refine ⟨0, ?_, ?_⟩
    · simpa using K.coe_nonneg
    · simp
  · refine ⟨(f a - f b) / (a - b), ?_, ?_⟩
    · have h := hf.norm_sub_le a b
      rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
      rw [abs_div]
      have hp : 0 < |a-b| := abs_pos.mpr (sub_ne_zero.mpr hab)
      apply (div_le_iff₀ hp).2
      simpa [mul_comm] using h
    · field_simp

end SemilinearPoissonSupport

-- END INLINED FILE: Mathlib/Support/semilinear_poisson_radial_symmetry_0e8f4ce1bc/Linearize.lean

-- BEGIN INLINED FILE: Mathlib/Support/semilinear_poisson_radial_symmetry_0e8f4ce1bc/Packaging.lean

/-!
Elementary order/topology part of the radial-profile conclusion.  These lemmas do
not use an elliptic maximum principle.  Keeping the endpoint (`closedBall`) bookkeeping
and the `NNReal` profile separate is useful: a moving-planes argument is normally proved
just on the *open* ball.
-/

open Metric
open scoped NNReal

namespace SemilinearPoissonSupport
lemma nonneg_closedBall {n:ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hpos : ∀ x ∈ ball (0:EuclideanSpace ℝ (Fin n)) 1, 0 < u x)
    (hzero : ∀ x ∈ sphere (0:EuclideanSpace ℝ (Fin n)) 1, u x = 0) :
    ∀ x ∈ closedBall (0:EuclideanSpace ℝ (Fin n)) 1, 0 ≤ u x := by
  intro x hx
  have hnorm : ‖x‖ ≤ (1:ℝ) := (mem_closedBall_zero_iff).1 hx
  rcases lt_or_eq_of_le hnorm with hlt | heq
  · exact (hpos x ((mem_ball_zero_iff).2 hlt)).le
  · have hs : x ∈ sphere (0:EuclideanSpace ℝ (Fin n)) 1 :=
      (mem_sphere_zero_iff_norm).2 heq
    rw [hzero x hs]

lemma unitvec {n:ℕ} (hn:0<n) : ∃ e : EuclideanSpace ℝ (Fin n), ‖e‖ = (1:ℝ) := by
  let i : Fin n := ⟨0, hn⟩
  refine ⟨EuclideanSpace.single i 1, ?_⟩
  rw [PiLp.norm_single]
  norm_num

lemma closed_line {n:ℕ} {e : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = (1:ℝ))
  {r:ℝ} (hr0:0≤r) (hr1:r≤1) :
  r • e ∈ closedBall (0:EuclideanSpace ℝ (Fin n)) 1 := by
    apply (mem_closedBall_zero_iff).2
    rw [norm_smul_of_nonneg hr0, he, mul_one]
    exact hr1

lemma norm_line {n:ℕ} {e : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = (1:ℝ))
  {r:ℝ} (hr0:0≤r) : ‖r • e‖ = r := by
  rw [norm_smul_of_nonneg hr0, he, mul_one]

lemma profile_build {n:ℕ} (hn:0<n) (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (h_nonneg : ∀ x ∈ closedBall (0:EuclideanSpace ℝ (Fin n)) 1, 0 ≤ u x)
    (h_eq : ∀ x ∈ closedBall (0:EuclideanSpace ℝ (Fin n)) 1,
                ∀ y ∈ closedBall (0:EuclideanSpace ℝ (Fin n)) 1,
                  ‖x‖ = ‖y‖ → u x = u y)
    (h_strict : ∀ x ∈ closedBall (0:EuclideanSpace ℝ (Fin n)) 1,
                ∀ y ∈ closedBall (0:EuclideanSpace ℝ (Fin n)) 1,
                  ‖x‖ < ‖y‖ → u y < u x) :
    ∃ v : ℝ → ℝ≥0,
       StrictAntiOn v (Set.Icc (0:ℝ) 1) ∧
       ∀ x ∈ closedBall (0:EuclideanSpace ℝ (Fin n)) 1, u x = v ‖x‖ := by
  classical
  obtain ⟨e, he⟩ := unitvec hn
  let v : ℝ → ℝ≥0 := fun r => Real.toNNReal (u (r • e))
  refine ⟨v, ?_, ?_⟩
  · intro a ha b hb hab
    have ha0 : 0 ≤ a := ha.1
    have ha1 : a ≤ (1:ℝ) := ha.2
    have hb0 : 0 ≤ b := hb.1
    have hb1 : b ≤ (1:ℝ) := hb.2
    have hxa : a • e ∈ closedBall (0:EuclideanSpace ℝ (Fin n)) 1 :=
      closed_line he ha0 ha1
    have hxb : b • e ∈ closedBall (0:EuclideanSpace ℝ (Fin n)) 1 :=
      closed_line he hb0 hb1
    have hnma : ‖a • e‖ = a := norm_line he ha0
    have hnmb : ‖b • e‖ = b := norm_line he hb0
    have hlt : u (b • e) < u (a • e) :=
      h_strict (a • e) hxa (b • e) hxb (by rw [hnma, hnmb]; exact hab)
    -- compare the coercions of the two nonnegative real values
    change Real.toNNReal (u (b • e)) < Real.toNNReal (u (a • e))
    apply (NNReal.coe_lt_coe).mp
    rw [Real.coe_toNNReal _ (h_nonneg _ hxb),
        Real.coe_toNNReal _ (h_nonneg _ hxa)]
    exact hlt
  · intro x hx
    have hxnorm0 : 0 ≤ ‖x‖ := norm_nonneg x
    have hxnorm1 : ‖x‖ ≤ (1:ℝ) := (mem_closedBall_zero_iff).1 hx
    have hy : (‖x‖ : ℝ) • e ∈ closedBall (0:EuclideanSpace ℝ (Fin n)) 1 :=
      closed_line he hxnorm0 hxnorm1
    have hux : u x = u ((‖x‖ : ℝ) • e) :=
      h_eq x hx _ hy (norm_line he hxnorm0).symm
    change u x = (↑(v ‖x‖) : ℝ)
    calc
      u x = u ((‖x‖ : ℝ) • e) := hux
      _ = (↑(Real.toNNReal (u ((‖x‖ : ℝ) • e))) : ℝ) :=
        (Real.coe_toNNReal _ (h_nonneg _ hy)).symm
      _ = (↑(v ‖x‖) : ℝ) := rfl


lemma extend_equal {n:ℕ} {u:EuclideanSpace ℝ (Fin n) → ℝ}
 (hzero: ∀ x ∈ sphere (0:EuclideanSpace ℝ (Fin n)) 1, u x = 0)
 (h_eq_open: ∀ x ∈ ball (0:EuclideanSpace ℝ (Fin n)) 1,
               ∀ y ∈ ball (0:EuclideanSpace ℝ (Fin n)) 1,
                  ‖x‖ = ‖y‖ → u x = u y) :
 ∀ x ∈ closedBall (0:EuclideanSpace ℝ (Fin n)) 1,
               ∀ y ∈ closedBall (0:EuclideanSpace ℝ (Fin n)) 1,
                  ‖x‖ = ‖y‖ → u x = u y := by
  intro x hx y hy hxy
  have hxle : ‖x‖ ≤ (1:ℝ) := (mem_closedBall_zero_iff).1 hx
  rcases lt_or_eq_of_le hxle with hxl | hxe
  · have hylt : ‖y‖ < (1:ℝ) := by rwa [← hxy]
    exact h_eq_open x ((mem_ball_zero_iff).2 hxl) y ((mem_ball_zero_iff).2 hylt) hxy
  · have hye : ‖y‖ = (1:ℝ) := hxy ▸ hxe -- wait hxy : norm x = norm y, hxy ▸? yields? hxy.subst?
    calc
      u x = 0 := hzero x ((mem_sphere_zero_iff_norm).2 hxe)
      _ = u y := (hzero y ((mem_sphere_zero_iff_norm).2 hye)).symm

lemma extend_strict {n:ℕ} {u:EuclideanSpace ℝ (Fin n) → ℝ}
 (hpos : ∀ x ∈ ball (0:EuclideanSpace ℝ (Fin n)) 1, 0 < u x)
 (hzero: ∀ x ∈ sphere (0:EuclideanSpace ℝ (Fin n)) 1, u x = 0)
 (h_strict_open: ∀ x ∈ ball (0:EuclideanSpace ℝ (Fin n)) 1,
               ∀ y ∈ ball (0:EuclideanSpace ℝ (Fin n)) 1,
                  ‖x‖ < ‖y‖ → u y < u x) :
 ∀ x ∈ closedBall (0:EuclideanSpace ℝ (Fin n)) 1,
               ∀ y ∈ closedBall (0:EuclideanSpace ℝ (Fin n)) 1,
                  ‖x‖ < ‖y‖ → u y < u x := by
  intro x hx y hy hxy
  have hyle : ‖y‖ ≤ (1:ℝ) := (mem_closedBall_zero_iff).1 hy
  have hxlt : ‖x‖ < (1:ℝ) := lt_of_lt_of_le hxy hyle
  have hxb : x ∈ ball (0:EuclideanSpace ℝ (Fin n)) 1 := (mem_ball_zero_iff).2 hxlt
  rcases lt_or_eq_of_le hyle with hyl | hye
  · exact h_strict_open x hxb y ((mem_ball_zero_iff).2 hyl) hxy
  · have hys : y ∈ sphere (0:EuclideanSpace ℝ (Fin n)) 1 :=
       (mem_sphere_zero_iff_norm).2 hye
    -- boundary zero < interior
    rw [hzero y hys]
    exact hpos x hxb


end SemilinearPoissonSupport

-- END INLINED FILE: Mathlib/Support/semilinear_poisson_radial_symmetry_0e8f4ce1bc/Packaging.lean

-- BEGIN INLINED FILE: Mathlib/Support/semilinear_poisson_radial_symmetry_0e8f4ce1bc/ReflectionGeometry.lean
open Metric Real

namespace SemilinearPoissonSupport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def refl0 (e z : E) : E := z - (2 * inner ℝ z e) • e

def refl (e : E) (t : ℝ) (z : E) : E :=
  z + (2 * (t - inner ℝ z e)) • e

lemma refl_zero_eq (e z : E) : refl e 0 z = refl0 e z := by
  dsimp [refl, refl0]
  -- z + (2 * (0-inner...)) • e = z - ...
  module

lemma refl_inner_line {e : E} (he : inner ℝ e e = 1)
 {b t : ℝ} : refl e t (b • e) = (2*t-b) • e := by
  dsimp [refl]
  rw [real_inner_smul_left, he]
  -- note real_inner_smul_left (x y r) for inner (r • x) y ; simp
  -- expression b * 1
  -- combine module
  module

lemma refl_mid_line {e : E} (he : inner ℝ e e = 1)
 {a b : ℝ} : refl e ((a+b)/2) (b • e) = a • e := by
  rw [refl_inner_line he]
  congr 1
  ring

lemma inner_unit_of_norm {e : E} (he:‖e‖ = (1:ℝ)) : inner ℝ e e = 1 := by
  rw [real_inner_self_eq_norm_sq]
  rw [he]
  norm_num

/-- unit direction along x-y -/
noncomputable def dir (x y : E) : E := (‖x-y‖)⁻¹ • (x-y)

lemma norm_dir {x y : E} (hxy : x ≠ y) : ‖dir x y‖ = (1:ℝ) := by
  have hpos : 0 < ‖x-y‖ := (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))
  rw [dir, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖x-y‖⁻¹)]
  -- norm_smul inverse
  field_simp

-- algebra identity for coefficient
lemma inner_sub_norm_sq {x y : E} (h : ‖x‖ = ‖y‖) :
    (2:ℝ) * inner ℝ x (x-y) = ‖x-y‖^2 := by
  rw [inner_sub_right, real_inner_self_eq_norm_sq]
  -- compute norm of sub via inner
  have hz := real_inner_self_eq_norm_sq (x-y)
  rw [inner_sub_left, inner_sub_right, inner_sub_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hz
  -- hz : (... ) = norm(x-y)^2? see
  rw [← hz]
  rw [h]
  rw [real_inner_comm (x) (y)] -- orientation?
  ring

lemma refl0_dir_maps {x y : E} (hxy : x ≠ y) (hn : ‖x‖ = ‖y‖) :
    refl0 (dir x y) x = y := by
  have hpos : 0 < ‖x-y‖ := (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))
  have hid : (2:ℝ) * inner ℝ x (x-y) = ‖x-y‖^2 := inner_sub_norm_sq hn
  dsimp [refl0, dir]
  rw [real_inner_smul_right]
  -- becomes x - (2 * (norm^-1 * inner ...)) • (norm^-1 • (x-y))
  rw [smul_smul]
  -- simplify coefficient
  have coef : (2 * (‖x-y‖⁻¹ * inner ℝ x (x-y))) * ‖x-y‖⁻¹ = (1:ℝ) := by
    calc
      _ = (2 * inner ℝ x (x-y)) * (‖x-y‖⁻¹)^2 := by ring
      _ = (‖x-y‖^2) * (‖x-y‖⁻¹)^2 := by rw [hid]
      _ = 1 := by
        field_simp
  rw [coef, one_smul]
  abel


lemma equal_norm_of_plane (u : E → ℝ)
 (hplane : ∀ e : E, ‖e‖ = (1:ℝ) →
      ∀ z ∈ Metric.ball (0:E) 1, u (refl0 e z) = u z) :
 ∀ x ∈ Metric.ball (0:E) 1, ∀ y ∈ Metric.ball (0:E) 1,
       ‖x‖ = ‖y‖ → u x = u y := by
  intro x hx y hy hn
  by_cases hxy : x = y
  · simpa [hxy]
  · have hp := hplane (dir x y) (norm_dir hxy) x hx
    rw [refl0_dir_maps hxy hn] at hp
    exact hp.symm

lemma strict_line_of_cap (u : E → ℝ)
 (hcap : ∀ e : E, ‖e‖ = (1:ℝ) →
          ∀ t : ℝ, 0 < t →
          ∀ z ∈ Metric.ball (0:E) 1,
            t < inner ℝ z e →
            u z < u (refl e t z)) :
 ∀ e : E, ‖e‖ = (1:ℝ) →
    ∀ a b : ℝ, 0 ≤ a → a < b → b < 1 →
      u (b • e) < u (a • e) := by
  intro e he a b ha hab hb
  have heinner : inner ℝ e e = 1 := inner_unit_of_norm he
  have hb0 : 0 ≤ b := le_trans ha (le_of_lt hab)
  have hmem : b • e ∈ Metric.ball (0:E) 1 := by
    apply (mem_ball_zero_iff).2
    rw [norm_smul_of_nonneg hb0, he, mul_one]
    exact hb
  have htpos : 0 < (a+b)/2 := by linarith
  have hinner : inner ℝ (b • e) e = b := by
    rw [real_inner_smul_left, heinner]
    simp
  have hlt : (a+b)/2 < inner ℝ (b • e) e := by rw [hinner]; linarith
  have hh := hcap e he ((a+b)/2) htpos (b • e) hmem hlt
  simpa [refl_mid_line heinner] using hh -- rw lemma more direct?


-- In a nonzero Euclidean space choose the first coordinate.
lemma unitvec_fin {n : ℕ} (hn : 0 < n) :
    ∃ e : EuclideanSpace ℝ (Fin n), ‖e‖ = (1:ℝ) := by
  let i : Fin n := ⟨0, hn⟩
  refine ⟨EuclideanSpace.single i 1, ?_⟩
  rw [PiLp.norm_single]
  norm_num

lemma strict_norm_of_cap_fin {n : ℕ} (hn : 0 < n)
 (u : EuclideanSpace ℝ (Fin n) → ℝ)
 (heq : ∀ x ∈ Metric.ball (0:EuclideanSpace ℝ (Fin n)) 1,
          ∀ y ∈ Metric.ball (0:EuclideanSpace ℝ (Fin n)) 1,
             ‖x‖ = ‖y‖ → u x = u y)
 (hcap : ∀ e : EuclideanSpace ℝ (Fin n), ‖e‖ = (1:ℝ) →
          ∀ t : ℝ, 0 < t →
          ∀ z ∈ Metric.ball (0:EuclideanSpace ℝ (Fin n)) 1,
            t < inner ℝ z e →
            u z < u (refl e t z)) :
 ∀ x ∈ Metric.ball (0:EuclideanSpace ℝ (Fin n)) 1,
   ∀ y ∈ Metric.ball (0:EuclideanSpace ℝ (Fin n)) 1,
      ‖x‖ < ‖y‖ → u y < u x := by
  obtain ⟨e, he⟩ := unitvec_fin hn
  intro x hx y hy hxy
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg _
  have hy0 : 0 ≤ ‖y‖ := norm_nonneg _
  have hx1 : ‖x‖ < (1:ℝ) := (mem_ball_zero_iff).1 hx
  have hy1 : ‖y‖ < (1:ℝ) := (mem_ball_zero_iff).1 hy
  have hxe : (‖x‖ : ℝ) • e ∈ Metric.ball (0:EuclideanSpace ℝ (Fin n)) 1 := by
    apply (mem_ball_zero_iff).2
    rw [norm_smul_of_nonneg hx0, he, mul_one]
    exact hx1
  have hye : (‖y‖ : ℝ) • e ∈ Metric.ball (0:EuclideanSpace ℝ (Fin n)) 1 := by
    apply (mem_ball_zero_iff).2
    rw [norm_smul_of_nonneg hy0, he, mul_one]
    exact hy1
  have hxnorm : ‖(‖x‖:ℝ) • e‖ = ‖x‖ := by
    rw [norm_smul_of_nonneg hx0, he, mul_one]
  have hynorm : ‖(‖y‖:ℝ) • e‖ = ‖y‖ := by
    rw [norm_smul_of_nonneg hy0, he, mul_one]
  have hx_eq := heq x hx _ hxe hxnorm.symm
  have hy_eq := heq y hy _ hye hynorm.symm
  have ray := strict_line_of_cap u hcap e he (‖x‖) (‖y‖) hx0 hxy hy1
  -- ray : u(y ray)<u(x ray)
  rw [← hx_eq, ← hy_eq] at ray
  exact ray

end SemilinearPoissonSupport

-- END INLINED FILE: Mathlib/Support/semilinear_poisson_radial_symmetry_0e8f4ce1bc/ReflectionGeometry.lean

-- BEGIN INLINED FILE: Mathlib/Support/semilinear_poisson_radial_symmetry_0e8f4ce1bc/LimitPlane.lean
open Metric Real
open Filter
open scoped Topology
namespace SemilinearPoissonSupport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma refl0_inner (e z : E) (he : inner ℝ e e = 1) :
    inner ℝ (refl0 e z) e = - inner ℝ z e := by
  dsimp [refl0]
  rw [inner_sub_left, real_inner_smul_left, he]
  ring

lemma refl0_invol (e z : E) (he : inner ℝ e e = 1) :
    refl0 e (refl0 e z) = z := by
  dsimp [refl0]
  -- inner for first reflect
  have hi : inner ℝ (z - (2*inner ℝ z e) • e) e = - inner ℝ z e := by
    rw [inner_sub_left, real_inner_smul_left, he]
    ring
  rw [hi]
  module

lemma refl0_norm (e z : E) (he : inner ℝ e e = 1) :
    ‖refl0 e z‖ = ‖z‖ := by
  have hsq : ‖refl0 e z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    dsimp [refl0]
    rw [inner_sub_left, inner_sub_right, inner_sub_right,
        real_inner_smul_left, real_inner_smul_right,
        real_inner_smul_left, real_inner_smul_right,
        he]
    -- note one cross inner e z -> commute
    rw [real_inner_comm e z]
    ring
  have h1 := norm_nonneg (refl0 e z)
  have h2 := norm_nonneg z
  nlinarith

lemma refl0_neg (e z : E) : refl0 (-e) z = refl0 e z := by
  dsimp [refl0]
  rw [inner_neg_right]
  -- scalars negative
  module

/-- A cap inequality for positive planes already implies a weak symmetry
inequality on the limiting plane, by taking `t ↓ 0`. -/
lemma le_refl0_of_cap (u : E → ℝ)
    (hcont : ∀ p ∈ Metric.ball (0:E) 1, ContinuousAt u p)
    (hcap : ∀ e : E, ‖e‖ = (1:ℝ) →
          ∀ t : ℝ, 0 < t →
          ∀ z ∈ Metric.ball (0:E) 1,
            t < inner ℝ z e →
            u z < u (refl e t z)) :
    ∀ e : E, ‖e‖ = (1:ℝ) →
       ∀ z ∈ Metric.ball (0:E) 1,
          0 < inner ℝ z e →
          u z ≤ u (refl0 e z) := by
  intro e he z hz hcpos
  let c : ℝ := inner ℝ z e
  have hc : 0 < c := by simpa [c] using hcpos
  have hei : inner ℝ e e = 1 := inner_unit_of_norm he
  -- sequence of positive parameters tending to zero
  let s : ℕ → ℝ := fun m => (c/2) * (1 / ((m:ℝ) + 1))
  have hs_tend : Tendsto s atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have h' := h.const_mul (c/2)
    -- normalize
    simpa [s] using h'
  have hs_pos (m : ℕ) : 0 < s m := by
    dsimp [s]
    positivity
  have hs_lt (m : ℕ) : s m < inner ℝ z e := by
    have hden : (1:ℝ) ≤ (m:ℝ)+1 := by exact_mod_cast (Nat.succ_pos m) -- wrong casts
    have hfrac : 1 / ((m:ℝ)+1) ≤ (1:ℝ) := by
      have hdenpos : (0:ℝ) < (1:ℝ) := one_pos
      have := one_div_le_one_div_of_le hdenpos hden
      simpa using this
    have hhalf : c/2 < c := by linarith
    have hbound : (c/2) * (1 / ((m:ℝ)+1)) ≤ c/2 := by
      nlinarith
    dsimp [s]
    nlinarith
  have hvec : Tendsto (fun m => refl e (s m) z) atTop (𝓝 (refl0 e z)) := by
    -- calculate directly from the definition
    have hsub : Tendsto (fun m => s m - inner ℝ z e) atTop
          (𝓝 (0 - inner ℝ z e)) := hs_tend.sub_const _
    have hmul : Tendsto (fun m => (2:ℝ) * (s m - inner ℝ z e)) atTop
          (𝓝 ((2:ℝ) * (0 - inner ℝ z e))) := hsub.const_mul 2
    have hsm : Tendsto (fun m => ((2:ℝ)*(s m - inner ℝ z e)) • e) atTop
          (𝓝 (((2:ℝ)*(0-inner ℝ z e)) • e)) := hmul.smul_const e
    have hadd : Tendsto (fun m => z + ((2:ℝ)*(s m - inner ℝ z e)) • e) atTop
          (𝓝 (z + ((2:ℝ)*(0-inner ℝ z e)) • e)) := hsm.const_add z
    -- simplify
    simpa [refl, refl0, sub_eq_add_neg] using hadd
  have hmem0 : refl0 e z ∈ Metric.ball (0:E) 1 := by
    have hz' : ‖z‖ < (1:ℝ) := (mem_ball_zero_iff).1 hz
    apply (mem_ball_zero_iff).2
    rw [refl0_norm e z hei]
    exact hz'
  have hulim : Tendsto (fun m => u (refl e (s m) z)) atTop
        (𝓝 (u (refl0 e z))) := (hcont _ hmem0).tendsto.comp hvec
  -- each cap inequality gives a lower bound on that sequence
  apply ge_of_tendsto hulim
  exact Filter.Eventually.of_forall (fun m =>
    (hcap e he (s m) (hs_pos m) z hz (hs_lt m)).le)

lemma plane0_of_cap (u : E → ℝ)
    (hcont : ∀ p ∈ Metric.ball (0:E) 1, ContinuousAt u p)
    (hcap : ∀ e : E, ‖e‖ = (1:ℝ) →
          ∀ t : ℝ, 0 < t →
          ∀ z ∈ Metric.ball (0:E) 1,
            t < inner ℝ z e →
            u z < u (refl e t z)) :
    ∀ e : E, ‖e‖ = (1:ℝ) →
       ∀ z ∈ Metric.ball (0:E) 1,
          u (refl0 e z) = u z := by
  intro e he z hz
  have hei : inner ℝ e e = 1 := inner_unit_of_norm he
  have hmem : refl0 e z ∈ Metric.ball (0:E) 1 := by
    apply (mem_ball_zero_iff).2
    rw [refl0_norm e z hei]
    exact (mem_ball_zero_iff).1 hz
  have hflip : inner ℝ (refl0 e z) e = - inner ℝ z e := refl0_inner e z hei
  by_cases hp : inner ℝ z e = 0
  · -- point on the plane is fixed
    have fix : refl0 e z = z := by
      dsimp [refl0]
      rw [hp]
      simp
    simp [fix]
  · rcases lt_or_gt_of_ne hp with hn | hp'
    · -- z has negative inner product; refl has positive
      have hpos' : 0 < inner ℝ (refl0 e z) e := by rw [hflip]; linarith
      have hle' := le_refl0_of_cap u hcont hcap e he (refl0 e z) hmem hpos'
      rw [refl0_invol e z hei] at hle'
      -- gives u(reflected) ≤ u z
      have hene : ‖(-e)‖ = (1:ℝ) := by simpa using he
      have hnegpos : 0 < inner ℝ z (-e) := by rw [inner_neg_right]; linarith
      have hle := le_refl0_of_cap u hcont hcap (-e) hene z hz hnegpos
      rw [refl0_neg e z] at hle
      exact le_antisymm hle' hle
    · -- z positive; same two inequalities in the reverse roles
      have hle := le_refl0_of_cap u hcont hcap e he z hz hp'
      have hene : ‖(-e)‖ = (1:ℝ) := by simpa using he
      have hnegpos : 0 < inner ℝ (refl0 e z) (-e) := by
        rw [inner_neg_right, hflip]
        linarith
      have hle' := le_refl0_of_cap u hcont hcap (-e) hene (refl0 e z) hmem hnegpos
      rw [refl0_neg e (refl0 e z), refl0_invol e z hei] at hle'
      exact le_antisymm hle' hle


/-- For a unit normal a ball has no cap with parameter at least `1`.
This lets the analytic part of moving planes work only with `0 < t < 1`. -/
lemma cap_all_of_small (u : E → ℝ)
    (hsmall : ∀ e : E, ‖e‖ = (1:ℝ) →
          ∀ t : ℝ, 0 < t → t < 1 →
          ∀ z ∈ Metric.ball (0:E) 1,
            t < inner ℝ z e →
            u z < u (refl e t z)) :
    ∀ e : E, ‖e‖ = (1:ℝ) →
          ∀ t : ℝ, 0 < t →
          ∀ z ∈ Metric.ball (0:E) 1,
            t < inner ℝ z e →
            u z < u (refl e t z) := by
  intro e he t ht z hz hzi
  have hile : inner ℝ z e ≤ ‖z‖ * ‖e‖ := real_inner_le_norm z e
  have hzlt : ‖z‖ < (1:ℝ) := (mem_ball_zero_iff).1 hz
  have hi : inner ℝ z e < (1:ℝ) := by rw [he, mul_one] at hile; linarith
  have ht' : t < (1:ℝ) := lt_trans hzi hi
  exact hsmall e he t ht ht' z hz hzi

end SemilinearPoissonSupport

-- END INLINED FILE: Mathlib/Support/semilinear_poisson_radial_symmetry_0e8f4ce1bc/LimitPlane.lean

-- BEGIN INLINED FILE: Mathlib/Support/semilinear_poisson_radial_symmetry_0e8f4ce1bc/CapGeometry.lean
open Metric Real
namespace SemilinearPoissonSupport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma refl_norm_sq (e z : E) (t : ℝ) (he : inner ℝ e e = 1) :
    ‖refl e t z‖^2 = ‖z‖^2 + 4*t*(t - inner ℝ z e) := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  dsimp [refl]
  rw [inner_add_left, inner_add_right, inner_add_right,
      real_inner_smul_left, real_inner_smul_right,
      real_inner_smul_left, real_inner_smul_right, he]
  rw [real_inner_comm e z]
  ring

lemma refl_norm_lt (e z : E) (t : ℝ)
    (he : inner ℝ e e = 1) (ht : 0 < t)
    (hz : t < inner ℝ z e) : ‖refl e t z‖ < ‖z‖ := by
  have hs := refl_norm_sq e z t he
  have ha := norm_nonneg (refl e t z)
  have hb := norm_nonneg z
  nlinarith

lemma refl_mem_ball (e z : E) (t : ℝ) (he : ‖e‖ = (1:ℝ))
    (ht : 0 < t) (hzmem : z ∈ Metric.ball (0:E) 1)
    (hz : t < inner ℝ z e) :
    refl e t z ∈ Metric.ball (0:E) 1 := by
  apply (mem_ball_zero_iff).2
  have hlt := refl_norm_lt e z t (inner_unit_of_norm he) ht hz
  exact lt_trans hlt ((mem_ball_zero_iff).1 hzmem)

lemma refl_inner (e z : E) (t : ℝ) (he : inner ℝ e e = 1) :
    inner ℝ (refl e t z) e = 2*t - inner ℝ z e := by
  dsimp [refl]
  rw [inner_add_left, real_inner_smul_left, he]
  ring

lemma refl_invol (e z : E) (t : ℝ) (he : inner ℝ e e = 1) :
    refl e t (refl e t z) = z := by
  dsimp [refl]
  have hi : inner ℝ (z + (2*(t - inner ℝ z e)) • e) e
            = 2*t - inner ℝ z e := by
    rw [inner_add_left, real_inner_smul_left, he]
    ring
  rw [hi]
  module

-- A point of the sphere in a nonempty cap reflects strictly inside the ball.
lemma refl_sphere_to_ball (e z : E) (t : ℝ) (he : ‖e‖ = (1:ℝ))
    (ht : 0 < t) (hzsphere : z ∈ Metric.sphere (0:E) 1)
    (hz : t < inner ℝ z e) :
    refl e t z ∈ Metric.ball (0:E) 1 := by
  apply (mem_ball_zero_iff).2
  have hs : ‖z‖ = (1:ℝ) := (mem_sphere_zero_iff_norm).1 hzsphere
  have hlt := refl_norm_lt e z t (inner_unit_of_norm he) ht hz
  simpa [hs] using hlt

end SemilinearPoissonSupport

-- END INLINED FILE: Mathlib/Support/semilinear_poisson_radial_symmetry_0e8f4ce1bc/CapGeometry.lean

-- BEGIN INLINED FILE: Mathlib/Support/semilinear_poisson_radial_symmetry_0e8f4ce1bc/AnalyticPrep.lean

open Metric Real
open scoped Topology InnerProductSpace
open Laplacian

namespace SemilinearPoissonSupport

/-- Trace of the Hessian is invariant under linear isometries.  This useful
pointwise version does not require differentiability; an equivalence works
for the junk values of `fderiv` too. -/
lemma laplacian_comp_linearIsometryEquiv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E ≃ₗᵢ[ℝ] E) (g : E → ℝ) (x : E) :
    Laplacian.laplacian (fun y => g (A y)) x =
      Laplacian.laplacian g (A x) := by
  let B : E ≃L[ℝ] E := A.toContinuousLinearEquiv
  let b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E :=
    stdOrthonormalBasis ℝ E
  have hiter : iteratedFDeriv ℝ 2 (g ∘ B) x =
      (iteratedFDeriv ℝ 2 g (B x)).compContinuousLinearMap
        (fun _ : Fin 2 => B.toContinuousLinearMap) := by
    have H := ContinuousLinearEquiv.iteratedFDerivWithin_comp_right
      (s := (Set.univ : Set E)) B g (uniqueDiffOn_univ:
        UniqueDiffOn ℝ (Set.univ : Set E)) (Set.mem_univ (B x)) 2
    -- the equivalence transports `univ` to `univ`.
    simpa [iteratedFDerivWithin_univ] using H
  have hfun : (fun y : E => g (A y)) = (g ∘ B) := by rfl
  rw [hfun,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
      (g ∘ B) b,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
      g (b.map A)]
  change (∑ i, (iteratedFDeriv ℝ 2 (g ∘ B) x)
        ![b i, b i]) =
       ∑ i, (iteratedFDeriv ℝ 2 g (B x))
        ![(b.map A) i, (b.map A) i]
  rw [hiter]
  congr 1
  funext i
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    OrthonormalBasis.map_apply, B]
  congr 1
  funext j
  fin_cases j <;> rfl

/-- Translation does not alter the trace, it only moves the evaluation
point.  No smoothness assumptions are needed for this pointwise congruence. -/
lemma laplacian_comp_add_left
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (g : E → ℝ) (a x : E) :
    Laplacian.laplacian (fun y => g (a + y)) x =
      Laplacian.laplacian g (a + x) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp [iteratedFDeriv_comp_add_left]

/-- The linear part of the reflection used by moving planes is the usual
Hilbert-space reflection in the orthogonal hyperplane.  Expressing it with a
`LinearIsometryEquiv` lets us use invariant formulas for the Laplacian. -/
lemma hyper_reflection_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (e z : E) (he : ‖e‖ = (1 : ℝ)) :
    ((ℝ ∙ e : Submodule ℝ E)ᗮ.reflection z) = refl0 e z := by
  -- reflection in the complement is minus reflection in the line
  rw [Submodule.reflection_orthogonal_apply]
  rw [Submodule.reflection_singleton_apply]
  dsimp [refl0]
  -- over the reals `⟪e,z⟫=⟪z,e⟫` and the denominator is one
  rw [he]
  simp [real_inner_comm]
  module

/-- Reflection across the plane through the origin preserves the Laplacian. -/
lemma laplacian_refl0
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (g : E → ℝ) (e z : E) (he : ‖e‖ = (1 : ℝ)) :
    Laplacian.laplacian (fun y => g (refl0 e y)) z =
      Laplacian.laplacian g (refl0 e z) := by
  let A : E ≃ₗᵢ[ℝ] E := (ℝ ∙ e : Submodule ℝ E)ᗮ.reflection
  have hz (y : E) : A y = refl0 e y := hyper_reflection_apply e y he
  have hfun : (fun y : E => g (refl0 e y)) = (fun y : E => g (A y)) := by
    funext y; rw [hz]
  rw [hfun, laplacian_comp_linearIsometryEquiv A]
  rw [hz]

/-- The affine reflection `refl e t` also preserves the Laplacian. -/
lemma laplacian_refl
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (g : E → ℝ) (e : E) (t : ℝ) (z : E) (he : ‖e‖ = (1 : ℝ)) :
    Laplacian.laplacian (fun y => g (refl e t y)) z =
      Laplacian.laplacian g (refl e t z) := by
  let A : E ≃ₗᵢ[ℝ] E := (ℝ ∙ e : Submodule ℝ E)ᗮ.reflection
  have hA (y : E) : A y = refl0 e y := hyper_reflection_apply e y he
  have hdecomp (y : E) : refl e t y = (2*t) • e + A y := by
    rw [hA]
    dsimp [refl, refl0]
    module
  have hfun : (fun y : E => g (refl e t y)) =
      (fun y : E => (fun v : E => g ((2*t) • e + v)) (A y)) := by
    funext y
    rw [hdecomp]
  rw [hfun]
  rw [laplacian_comp_linearIsometryEquiv A
    (fun v : E => g ((2*t) • e + v)) z]
  rw [laplacian_comp_add_left]
  rw [hdecomp]

end SemilinearPoissonSupport

namespace SemilinearPoissonSupport
open Metric
lemma contDiff_refl
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E) (t : ℝ) : ContDiff ℝ 2 (fun y : E => refl e t y) := by
  dsimp [SemilinearPoissonSupport.refl]
  have hre : (fun y : E => y + (2 * (t - inner ℝ y e)) • e) =
        (fun y : E => y + (2 * (t - (innerSL ℝ e) y)) • e) := by
    funext y
    simp [real_inner_comm]
  rw [hre]
  fun_prop

lemma contDiffAt_ball_of_closed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ}
    (hu : ContDiffOn ℝ 2 u (closedBall (0:E) 1))
    {x : E} (hx : x ∈ ball (0:E) 1) :
    ContDiffAt ℝ 2 u x := by
  apply hu.contDiffAt
  exact Filter.mem_of_superset (IsOpen.mem_nhds Metric.isOpen_ball hx)
    Metric.ball_subset_closedBall

/-- Subtracting a reflected solution satisfies the expected difference
Laplacian. This is the point where the equation becomes a scalar linear
one; the remaining difficulty of moving planes is a maximum principle. -/
lemma reflected_difference_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : ℝ → ℝ) (u : E → ℝ) (e : E) (t : ℝ) (x : E)
    (he : ‖e‖ = (1 : ℝ))
    (hu : ContDiffOn ℝ 2 u (closedBall (0:E) 1))
    (hx : x ∈ ball (0:E) 1)
    (hrx : refl e t x ∈ ball (0:E) 1)
    (hpde : ∀ y ∈ ball (0:E) 1,
      - Laplacian.laplacian u y = f (u y)) :
    - Laplacian.laplacian (fun y : E => u (refl e t y) - u y) x =
       f (u (refl e t x)) - f (u x) := by
  have hux : ContDiffAt ℝ 2 u x := contDiffAt_ball_of_closed hu hx
  have hur : ContDiffAt ℝ 2 u (refl e t x) :=
    contDiffAt_ball_of_closed hu hrx
  have hcomp : ContDiffAt ℝ 2 (fun y : E => u (refl e t y)) x := by
    have h := ContDiffAt.comp x hur (contDiff_refl e t).contDiffAt
    -- composition written out
    exact h
  have hsub := ContDiffAt.laplacian_sub hcomp hux
  have hfun : ((fun y : E => u (refl e t y)) - u) =
      (fun y : E => u (refl e t y) - u y) := by rfl
  -- identify the subtracted function and use invariance of trace
  rw [hfun] at hsub
  rw [hsub, laplacian_refl u e t x he]
  have h1 := hpde x hx
  have h2 := hpde (refl e t x) hrx
  linarith

end SemilinearPoissonSupport

namespace SemilinearPoissonSupport
open Filter Set Topology
/-- A convenient one-dimensional sign lemma for the trace maximum
principle.  It is deliberately formulated with the total derivative
`deriv`: no second differentiability assumption on the first derivative is
needed in the statement.  If that derivative is not differentiable its
`deriv` is zero, so only the strictly-negative case requires the usual
second-derivative test. -/
lemma deriv_deriv_nonneg_at_localMin {g : ℝ → ℝ} {x:ℝ}
 (hm : IsLocalMin g x) (hc : ContinuousAt g x) :
 0 ≤ deriv (deriv g) x := by
  by_contra hn
  have hneg : deriv (deriv g) x < 0 := lt_of_not_ge hn
  have hmax : IsLocalMax g x :=
    isLocalMax_of_deriv_deriv_neg hneg hm.deriv_eq_zero hc
  have hle : ∀ᶠ y in 𝓝 x, g y ≤ g x := hmax
  have hge : ∀ᶠ y in 𝓝 x, g x ≤ g y := hm
  have heqg : g =ᶠ[𝓝 x] (fun _ : ℝ => g x) := by
    filter_upwards [hle, hge] with y hy hz
    exact le_antisymm hy hz
  have hopen : ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧
       ∀ y ∈ U, g =ᶠ[𝓝 y] (fun _ : ℝ => g x) := by
    rcases (_root_.eventually_nhds_iff.mp heqg) with ⟨U, hU, Uo, hxU⟩
    refine ⟨U, Uo, hxU, ?_⟩
    intro y hy
    filter_upwards [Uo.mem_nhds hy] with z hz
    exact hU z hz
  rcases hopen with ⟨U,hU,hx,hall⟩
  have hder : deriv g =ᶠ[𝓝 x] (fun _ : ℝ => (0:ℝ)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    have L := (hall y hy).deriv_eq
    simpa using L
  have hzero : deriv (deriv g) x = 0 := by
    have H := hder.deriv_eq
    simpa using H
  linarith
end SemilinearPoissonSupport

-- END INLINED FILE: Mathlib/Support/semilinear_poisson_radial_symmetry_0e8f4ce1bc/AnalyticPrep.lean

-- BEGIN INLINED FILE: Mathlib/Support/semilinear_poisson_radial_symmetry_0e8f4ce1bc/MaximumPrep.lean
open scoped Topology InnerProductSpace NNReal
open Filter Set Real Metric Topology
namespace SemilinearPoissonSupport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma line_second_deriv {F:E→ℝ} (p b:E)
 (hF : ContDiffAt ℝ 2 F p) :
 deriv (deriv (fun s : ℝ => F (p + s • b))) 0 =
   iteratedFDeriv ℝ 2 F p ![b,b] := by
 let L : ℝ → E := fun s => p + s • b
 have hL (s:ℝ) : HasDerivAt L b s := by
   dsimp [L]
   convert ( (hasDerivAt_id s).smul_const b).const_add p using 1 <;> simp
 have hLp : L 0 = p := by simp [L]
 -- eventually differentiability
 have hev : ∀ᶠ s in 𝓝 (0:ℝ), ContDiffAt ℝ 2 F (L s) := by
   have H := hF.eventually (by norm_num : (2 : WithTop ℕ∞) ≠ (⊤ : ℕ∞))
   -- continuous L at 0
   have hc : ContinuousAt L 0 := (hL 0).continuousAt
   have ht : Tendsto L (𝓝 (0:ℝ)) (𝓝 p) := by
     convert hc.tendsto using 2 <;> simp [hLp]
   exact ht.eventually H
 have hder : (fun s :ℝ => deriv (fun r:ℝ => F (L r)) s) =ᶠ[𝓝 0]
       (fun s => fderiv ℝ F (L s) b) := by
   filter_upwards [hev] with s hs
   have hcomp : HasDerivAt (fun r:ℝ => F (L r)) ((fderiv ℝ F (L s)) b) s := by
      have A := (hs.differentiableAt (by norm_num : (2:WithTop ℕ∞) ≠ 0)).hasFDerivAt
      have B := hL s
      have C := A.comp s B.hasFDerivAt
      -- function comp def
      simpa [Function.comp_def, ContinuousLinearMap.comp_apply] using C.hasDerivAt
   exact hcomp.deriv
 have hqder : HasDerivAt (fun s : ℝ => (fderiv ℝ F (L s)) b)
       (((fderiv ℝ (fderiv ℝ F) p) b) b) 0 := by
   have hdF : DifferentiableAt ℝ (fderiv ℝ F) p :=
     (hF.fderiv_right (m:=1) (by norm_num : (1:WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)
   -- composition with L
   have hdF0 : DifferentiableAt ℝ (fderiv ℝ F) (L 0) := by simpa [hLp] using hdF
   have C := hdF0.hasFDerivAt.comp (0:ℝ) (hL 0).hasFDerivAt
   -- C : of fderiv F ∘ L, derivative ... as linear; scalar deriv vector = ... b
   have C' : HasDerivAt (fun s :ℝ => fderiv ℝ F (L s))
        ((fderiv ℝ (fderiv ℝ F) p) b) 0 := by
     simpa [Function.comp_def, hLp, ContinuousLinearMap.comp_apply] using C.hasDerivAt
   -- eval at b linear continuous map
   let ev : (E →L[ℝ] ℝ) →L[ℝ] ℝ := (ContinuousLinearMap.apply ℝ ℝ) b
   have D := ev.hasFDerivAt.comp (0:ℝ) C'.hasFDerivAt
   simpa [ev, Function.comp_def, ContinuousLinearMap.comp_apply] using D.hasDerivAt
 calc
  _ = deriv (fun s : ℝ => (fderiv ℝ F (L s)) b) 0 := hder.deriv_eq
  _ = _ := ?_
 simpa [iteratedFDeriv_two_apply] using hqder.deriv

lemma laplacian_nonneg_at_localMin {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [FiniteDimensional ℝ E]
 {F:E→ℝ} {p:E} (hF:ContDiffAt ℝ 2 F p)
 (hm : IsLocalMin F p) : 0 ≤ Laplacian.laplacian F p := by
  let B := stdOrthonormalBasis ℝ E
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis F B]
  -- finite sum nonneg
  apply Finset.sum_nonneg
  intro i hi
  let l : ℝ → E := fun s => p + s • (B i)
  have hlp : l 0 = p := by simp [l]
  have hld (s:ℝ) : HasDerivAt l (B i) s := by
    dsimp [l]
    convert ((hasDerivAt_id s).smul_const (B i)).const_add p using 1 <;> simp
  have hm' : IsLocalMin (fun s : ℝ => F (l s)) 0 := by
    have mp : IsLocalMin F (l 0) := by simpa [hlp] using hm
    simpa [Function.comp_def] using (mp.comp_continuous (hld 0).continuousAt)
  have hc' : ContinuousAt (fun s:ℝ => F (l s)) 0 := by
    have hc := hF.continuousAt
    have hlc := (hld 0).continuousAt
    have hp' : ContinuousAt F (l 0) := by simpa [hlp] using hc
    simpa [Function.comp_def] using hp'.comp_of_eq hlc rfl
  have hnon := deriv_deriv_nonneg_at_localMin hm' hc'
  have eqd := line_second_deriv (F:=F) p (B i) hF
  change 0 ≤ iteratedFDeriv ℝ 2 F p ![B i, B i]
  -- l same
  have ll : (fun s : ℝ => F (l s)) = (fun s : ℝ => F (p + s • (B i))) := by rfl
  rw [ll] at hnon
  linarith

open Metric Topology
lemma weak_barrier_minimum {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [FiniteDimensional ℝ E]
 {D C:Set E} (hDC : D ⊆ C) (hD : IsOpen D) (hC : IsCompact C) (hne : C.Nonempty)
 {F φ:E→ℝ} {L:ℝ}
 (Fc : ContinuousOn F C) (φc : ContinuousOn φ C)
 (φpos : ∀x∈C, 0 < φ x)
 (bdry : ∀ x∈ C \ D, 0 ≤ F x)
 (Fd : ∀ x∈D, ContDiffAt ℝ 2 F x) (φd : ∀ x∈D, ContDiffAt ℝ 2 φ x)
 (bar : ∀ x∈D, Laplacian.laplacian φ x = - L * φ x)
 (eqn : ∀ x∈D, ∃ c : ℝ, c < L ∧
       - Laplacian.laplacian F x = c * F x) :
 ∀ x∈D, 0 ≤ F x := by
 classical
 let q : E → ℝ := fun x => F x / φ x
 have qc : ContinuousOn q C := Fc.div φc (fun x hx => ne_of_gt (φpos x hx))
 obtain ⟨p,hpC,hp⟩ := hC.exists_isMinOn hne qc
 intro x hx
 by_contra neg
 have qxneg : q x < 0 := by
   dsimp [q]
   exact (div_neg_of_neg_of_pos (lt_of_not_ge neg) (φpos x (hDC hx)))
 have qpneg : q p < 0 := lt_of_le_of_lt (hp (hDC hx)) qxneg
 have hpD : p ∈ D := by
   by_contra no
   have H := bdry p ⟨hpC, no⟩
   have : 0 ≤ q p := div_nonneg H (le_of_lt (φpos p hpC))
   linarith
 let a := q p
 have ga : F p = a * φ p := by
   dsimp [a, q]
   exact (div_mul_cancel₀ _ (ne_of_gt (φpos p hpC))).symm

 have hloc : IsLocalMin (fun y => F y - a * φ y) p := by
   -- on D near p, q p ≤ q y and φ y positive
   have : ∀ᶠ y in 𝓝 p, 0 ≤ F y - a * φ y := by
    filter_upwards [hD.mem_nhds hpD] with y hy
    have hyC := hDC hy
    have hqy := hp hyC
    have hpp := φpos y hyC
    dsimp [q] at hqy
    dsimp [a, q]
    -- q p still expression
    dsimp [q, a] at *
    -- hqy: F p / φ p ≤ F y / φ y
    calc
      0 ≤ F y - (F p / φ p) * φ y := by
        apply sub_nonneg.mpr
        exact (by
          calc
            F p / φ p * φ y ≤ (F y / φ y) * φ y := mul_le_mul_of_nonneg_right hqy (le_of_lt hpp)
            _ = F y := by field_simp)
      _ = _ := rfl
   -- local min value 0
   have hz : (fun y => F y - a * φ y) p = 0 := by simp [ga]
   have Evt : ∀ᶠ y in 𝓝 p, (fun y => F y - a * φ y) p ≤
          (fun y => F y - a * φ y) y := by simpa [hz] using this
   exact Evt
 have cdF := Fd p hpD
 have cdφ := φd p hpD
 have cdg : ContDiffAt ℝ 2 (fun y => F y - a * φ y) p := by fun_prop
 have non := laplacian_nonneg_at_localMin cdg hloc
 -- laplacian linear
 have lapg : Laplacian.laplacian (fun y => F y - a * φ y) p =
          Laplacian.laplacian F p - a * Laplacian.laplacian φ p := by
   have sm : ContDiffAt ℝ 2 (fun y : E => a * φ y) p := by fun_prop
   have ss := cdF.laplacian_sub sm
   change Laplacian.laplacian (F - fun y => a * φ y) p = _
   rw [ss]
   -- lap of scalar fun
   have H := InnerProductSpace.laplacian_smul (f:=φ) a cdφ
   have fun_eq : (fun y : E => a * φ y) = a • φ := by funext y; simp [Pi.smul_apply, smul_eq_mul]
   rw [fun_eq]
   simpa [smul_eq_mul] using H
 rw [lapg, bar p hpD] at non
 obtain ⟨c,hc,hc_eq⟩ := eqn p hpD
 have lapF : Laplacian.laplacian F p = -(c * F p) := by linarith
 rw [lapF, ga] at non
 have ap : a < 0 := qpneg
 have ph : 0 < φ p := φpos p hpC
 -- algebra
 have hhneg : a * φ p < 0 := mul_neg_of_neg_of_pos ap ph
 have hhpos : 0 < L - c := sub_pos.mpr hc
 have hn2 : a * φ p * (L-c) < 0 := mul_neg_of_neg_of_pos hhneg hhpos
 have hEq : -(c * (a * φ p)) - a * (-L * φ p) = a * φ p * (L-c) := by ring
 rw [hEq] at non
 linarith


variable {n:ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
def capOpen (e:E) (t:ℝ) : Set E := ball 0 1 ∩ {x | t < inner ℝ x e}
def capClosed (e:E) (t:ℝ) : Set E := closedBall 0 1 ∩ {x | t ≤ inner ℝ x e}
lemma capOpen_open (e:E) (t:ℝ) : IsOpen (capOpen e t) := by
 apply IsOpen.inter Metric.isOpen_ball
 have hc : Continuous (fun x:E => inner ℝ x e) := by fun_prop
 exact isOpen_lt continuous_const hc
lemma capOpen_subset (e:E) (t:ℝ) : capOpen e t ⊆ capClosed e t := by
 intro x hx
 refine ⟨Metric.ball_subset_closedBall hx.1, ?_⟩
 change t ≤ inner ℝ x e
 exact le_of_lt hx.2
lemma capClosed_compact (e:E) (t:ℝ) : IsCompact (capClosed e t) := by
 apply IsCompact.inter_right (ProperSpace.isCompact_closedBall (0:E) 1)
 have hc : Continuous (fun x:E => inner ℝ x e) := by fun_prop
 exact isClosed_le continuous_const hc
-- boundary nonnegative
lemma reflected_boundary_nonneg
 (u:E→ℝ) (e:E) (t:ℝ) (he: ‖e‖ = (1:ℝ)) (ht: 0 < t)
 (upos: ∀ x∈ball (0:E) 1, 0 < u x)
 (uzero: ∀ x∈sphere (0:E) 1, u x = 0) :
 ∀ x∈ capClosed e t \ capOpen e t,
   0 ≤ u (refl e t x) - u x := by
 intro x hx
 have hnorm : ‖x‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hx.1.1
 have hip : t ≤ inner ℝ x e := hx.1.2
 have cases : ‖x‖ = 1 ∨ inner ℝ x e = t := by
   by_cases h1: ‖x‖ < 1
   · right
     by_contra hh
     have hlt : t < inner ℝ x e := lt_of_le_of_ne hip (Ne.symm hh)
     exact hx.2 ⟨(by simpa [mem_ball, dist_zero_right] using h1), hlt⟩
   · left; exact le_antisymm hnorm (not_lt.mp h1)
 rcases cases with hs | hp
 · have ux : u x = 0 := uzero x (by simpa [mem_sphere, dist_zero_right] using hs)
   rw [ux]
   by_cases hip_eq : inner ℝ x e = t
   · have hre : refl e t x = x := by dsimp [refl]; rw [hip_eq]; simp
     simp [hre, ux]
   have hiplt : t < inner ℝ x e := lt_of_le_of_ne hip (Ne.symm hip_eq)
   have hrlt : ‖refl e t x‖ < ‖x‖ := refl_norm_lt e x t (inner_unit_of_norm he) ht hiplt
   have hr1 : ‖refl e t x‖ < 1 := by simpa [hs] using hrlt
   have : 0 ≤ u (refl e t x) := le_of_lt (upos _ (by simpa [mem_ball, dist_zero_right] using hr1))

   linarith
 · have hre : refl e t x = x := by
     dsimp [refl]
     rw [hp]
     simp
   simp [hre]
end SemilinearPoissonSupport

-- END INLINED FILE: Mathlib/Support/semilinear_poisson_radial_symmetry_0e8f4ce1bc/MaximumPrep.lean

-- BEGIN INLINED FILE: Mathlib/Support/semilinear_poisson_radial_symmetry_0e8f4ce1bc/ThinMax.lean
open scoped Topology InnerProductSpace NNReal
open Filter Set Real Metric Topology
namespace SemilinearPoissonSupport

/-- Weak maximum with a supersolution barrier.  The equality version is
`weak_barrier_minimum`; a concave quadratic barrier is more convenient on a
thin slab, so we only require `Δ φ ≤ - L φ`. -/
lemma weak_barrier_minimum_le {E : Type*} [NormedAddCommGroup E]
 [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
 {D C : Set E} (hDC : D ⊆ C) (hD : IsOpen D) (hC : IsCompact C) (hne : C.Nonempty)
 {F φ : E → ℝ} {L : ℝ}
 (Fc : ContinuousOn F C) (φc : ContinuousOn φ C)
 (φpos : ∀ x ∈ C, 0 < φ x)
 (bdry : ∀ x ∈ C \ D, 0 ≤ F x)
 (Fd : ∀ x ∈ D, ContDiffAt ℝ 2 F x) (φd : ∀ x ∈ D, ContDiffAt ℝ 2 φ x)
 (bar : ∀ x ∈ D, Laplacian.laplacian φ x ≤ - L * φ x)
 (eqn : ∀ x ∈ D, ∃ c : ℝ, c < L ∧
       - Laplacian.laplacian F x = c * F x) :
 ∀ x ∈ D, 0 ≤ F x := by
 classical
 let q : E → ℝ := fun x => F x / φ x
 have qc : ContinuousOn q C := Fc.div φc (fun x hx => ne_of_gt (φpos x hx))
 obtain ⟨p,hpC,hp⟩ := hC.exists_isMinOn hne qc
 intro x hx
 by_contra neg
 have qxneg : q x < 0 := by
   dsimp [q]
   exact (div_neg_of_neg_of_pos (lt_of_not_ge neg) (φpos x (hDC hx)))
 have qpneg : q p < 0 := lt_of_le_of_lt (hp (hDC hx)) qxneg
 have hpD : p ∈ D := by
   by_contra no
   have H := bdry p ⟨hpC, no⟩
   have : 0 ≤ q p := div_nonneg H (le_of_lt (φpos p hpC))
   linarith
 let a := q p
 have ga : F p = a * φ p := by
   dsimp [a, q]
   exact (div_mul_cancel₀ _ (ne_of_gt (φpos p hpC))).symm
 have hloc : IsLocalMin (fun y => F y - a * φ y) p := by
   have hloc' : ∀ᶠ y in 𝓝 p, 0 ≤ F y - a * φ y := by
    filter_upwards [hD.mem_nhds hpD] with y hy
    have hyC := hDC hy
    have hqy := hp hyC
    have hpp := φpos y hyC
    dsimp [q] at hqy
    dsimp [a, q] at *
    calc
      0 ≤ F y - (F p / φ p) * φ y := by
        apply sub_nonneg.mpr
        exact (by
          calc
            F p / φ p * φ y ≤ (F y / φ y) * φ y :=
              mul_le_mul_of_nonneg_right hqy (le_of_lt hpp)
            _ = F y := by field_simp)
      _ = _ := rfl
   have hz : (fun y => F y - a * φ y) p = 0 := by simp [ga]
   have Evt : ∀ᶠ y in 𝓝 p, (fun y => F y - a * φ y) p ≤
          (fun y => F y - a * φ y) y := by simpa [hz] using hloc'
   exact Evt
 have cdF := Fd p hpD
 have cdφ := φd p hpD
 have cdg : ContDiffAt ℝ 2 (fun y => F y - a * φ y) p := by fun_prop
 have non := laplacian_nonneg_at_localMin cdg hloc
 have lapg : Laplacian.laplacian (fun y => F y - a * φ y) p =
          Laplacian.laplacian F p - a * Laplacian.laplacian φ p := by
   have sm : ContDiffAt ℝ 2 (fun y : E => a * φ y) p := by fun_prop
   have ss := cdF.laplacian_sub sm
   change Laplacian.laplacian (F - fun y => a * φ y) p = _
   rw [ss]
   have H := InnerProductSpace.laplacian_smul (f:=φ) a cdφ
   have fun_eq : (fun y : E => a * φ y) = a • φ := by funext y; simp [Pi.smul_apply, smul_eq_mul]
   rw [fun_eq]
   simpa [smul_eq_mul] using H
 rw [lapg] at non
 obtain ⟨c,hc,hce⟩ := eqn p hpD
 have lapF : Laplacian.laplacian F p = -(c * F p) := by linarith
 rw [lapF, ga] at non
 have ap : a < 0 := qpneg
 have ph : 0 < φ p := φpos p hpC
 have bl := bar p hpD
 -- `-a` is positive, so substituting the upper bound for Δφ improves
 -- the contradiction.
 have ub : -(c * (a * φ p)) - a * Laplacian.laplacian φ p
          ≤ -(c * (a * φ p)) - a * (-L * φ p) := by
   -- -a >0
   have ha0 : 0 ≤ -a := le_of_lt (neg_pos.mpr ap)
   nlinarith
 have bad : -(c * (a * φ p)) - a * (-L * φ p) < 0 := by
   have hhneg : a * φ p < 0 := mul_neg_of_neg_of_pos ap ph
   have hhpos : 0 < L - c := sub_pos.mpr hc
   have hn2 : a * φ p * (L-c) < 0 := mul_neg_of_neg_of_pos hhneg hhpos
   nlinarith
 linarith


/-- Supersolution form of `weak_barrier_minimum_le`.  A positive right-hand
side is useful when comparing with explicit Hopf barriers. -/
lemma weak_barrier_minimum_sup {E : Type*} [NormedAddCommGroup E]
 [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
 {D C : Set E} (hDC : D ⊆ C) (hD : IsOpen D) (hC : IsCompact C) (hne : C.Nonempty)
 {F φ : E → ℝ} {L : ℝ}
 (Fc : ContinuousOn F C) (φc : ContinuousOn φ C)
 (φpos : ∀ x ∈ C, 0 < φ x)
 (bdry : ∀ x ∈ C \ D, 0 ≤ F x)
 (Fd : ∀ x ∈ D, ContDiffAt ℝ 2 F x) (φd : ∀ x ∈ D, ContDiffAt ℝ 2 φ x)
 (bar : ∀ x ∈ D, Laplacian.laplacian φ x ≤ - L * φ x)
 (eqn : ∀ x ∈ D, ∃ c : ℝ, c < L ∧
       c * F x ≤ - Laplacian.laplacian F x) :
 ∀ x ∈ D, 0 ≤ F x := by
 classical
 let q : E → ℝ := fun x => F x / φ x
 have qc : ContinuousOn q C := Fc.div φc (fun x hx => ne_of_gt (φpos x hx))
 obtain ⟨p,hpC,hp⟩ := hC.exists_isMinOn hne qc
 intro x hx
 by_contra neg
 have qxneg : q x < 0 := by
   dsimp [q]
   exact (div_neg_of_neg_of_pos (lt_of_not_ge neg) (φpos x (hDC hx)))
 have qpneg : q p < 0 := lt_of_le_of_lt (hp (hDC hx)) qxneg
 have hpD : p ∈ D := by
   by_contra no
   have H := bdry p ⟨hpC, no⟩
   have : 0 ≤ q p := div_nonneg H (le_of_lt (φpos p hpC))
   linarith
 let a := q p
 have ga : F p = a * φ p := by
   dsimp [a, q]
   exact (div_mul_cancel₀ _ (ne_of_gt (φpos p hpC))).symm
 have hloc : IsLocalMin (fun y => F y - a * φ y) p := by
   have hloc' : ∀ᶠ y in 𝓝 p, 0 ≤ F y - a * φ y := by
    filter_upwards [hD.mem_nhds hpD] with y hy
    have hyC := hDC hy
    have hqy := hp hyC
    have hpp := φpos y hyC
    dsimp [q] at hqy
    dsimp [a, q] at *
    calc
      0 ≤ F y - (F p / φ p) * φ y := by
        apply sub_nonneg.mpr
        exact (by
          calc
            F p / φ p * φ y ≤ (F y / φ y) * φ y :=
              mul_le_mul_of_nonneg_right hqy (le_of_lt hpp)
            _ = F y := by field_simp)
      _ = _ := rfl
   have hz : (fun y => F y - a * φ y) p = 0 := by simp [ga]
   have Evt : ∀ᶠ y in 𝓝 p, (fun y => F y - a * φ y) p ≤
          (fun y => F y - a * φ y) y := by simpa [hz] using hloc'
   exact Evt
 have cdF := Fd p hpD
 have cdφ := φd p hpD
 have cdg : ContDiffAt ℝ 2 (fun y => F y - a * φ y) p := by fun_prop
 have non := laplacian_nonneg_at_localMin cdg hloc
 have lapg : Laplacian.laplacian (fun y => F y - a * φ y) p =
          Laplacian.laplacian F p - a * Laplacian.laplacian φ p := by
   have sm : ContDiffAt ℝ 2 (fun y : E => a * φ y) p := by fun_prop
   have ss := cdF.laplacian_sub sm
   change Laplacian.laplacian (F - fun y => a * φ y) p = _
   rw [ss]
   have H := InnerProductSpace.laplacian_smul (f:=φ) a cdφ
   have fun_eq : (fun y : E => a * φ y) = a • φ := by funext y; simp [Pi.smul_apply, smul_eq_mul]
   rw [fun_eq]
   simpa [smul_eq_mul] using H
 rw [lapg] at non
 obtain ⟨c,hc,hce⟩ := eqn p hpD
 have lapF : Laplacian.laplacian F p ≤ -(c * F p) := by linarith
 have non' : 0 ≤ -(c * F p) - a * Laplacian.laplacian φ p :=
   le_trans non (sub_le_sub_right lapF _)
 rw [ga] at non'
 have ap : a < 0 := qpneg
 have ph : 0 < φ p := φpos p hpC
 have bl := bar p hpD
 -- `-a` is positive, so substituting the upper bound for Δφ improves
 -- the contradiction.
 have ub : -(c * (a * φ p)) - a * Laplacian.laplacian φ p
          ≤ -(c * (a * φ p)) - a * (-L * φ p) := by
   -- -a >0
   have ha0 : 0 ≤ -a := le_of_lt (neg_pos.mpr ap)
   nlinarith
 have bad : -(c * (a * φ p)) - a * (-L * φ p) < 0 := by
   have hhneg : a * φ p < 0 := mul_neg_of_neg_of_pos ap ph
   have hhpos : 0 < L - c := sub_pos.mpr hc
   have hn2 : a * φ p * (L-c) < 0 := mul_neg_of_neg_of_pos hhneg hhpos
   nlinarith
 exact (not_lt_of_ge (le_trans non' ub) bad)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
def slabBarrier (e : E) (t r : ℝ) (x : E) : ℝ := r^2 - (inner ℝ x e - t)^2
lemma slab_cd (e : E) (t r:ℝ) (x:E) : ContDiffAt ℝ 2 (slabBarrier e t r) x := by

 have hi : ContDiff ℝ 2 (fun y : E => inner ℝ y e) := by
   have hi' : (fun y : E => inner ℝ y e) = (fun y : E => (innerSL ℝ e) y) := by
     funext y; simp [real_inner_comm]
   rw [hi']
   fun_prop
 have hiAt := hi.contDiffAt (x:=x)
 unfold slabBarrier
 fun_prop (disch := aesop)
lemma quad_deriv (a b d : ℝ) : deriv (deriv (fun s : ℝ => d^2 - (a + s*b)^2)) 0 = -2*b^2 := by
 have hfirst (s:ℝ) : HasDerivAt (fun r : ℝ => d^2 - (a + r*b)^2)
       (- 2 * (a + s*b) * b) s := by
   convert ( (hasDerivAt_const (x:=s) (c:=d^2)).sub
       (((hasDerivAt_const (x:=s) (c:=a)).add ((hasDerivAt_id s).mul_const b)).pow 2)) using 1
   · rfl
   · rfl
   · ext r; simp [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
   · simp [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply] <;> ring
 have hf : (deriv (fun r : ℝ => d^2 - (a + r*b)^2)) =
       (fun s => -2 * (a + s*b) * b) := by funext s; exact (hfirst s).deriv
 rw [hf]
 have hs : HasDerivAt (fun s : ℝ => -2 * (a + s*b) * b) (-2*b^2) 0 := by
   convert ( ( (hasDerivAt_const (x:=(0:ℝ)) (c:=(-2:ℝ))).mul
      ((hasDerivAt_const (x:=(0:ℝ)) (c:=a)).add ((hasDerivAt_id (0:ℝ)).mul_const b))).mul_const b) using 1
   · rfl
   · rfl
   · ext r; simp [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
   · simp [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply] <;> ring
 exact hs.deriv
lemma slab_lap (e : E) (t r:ℝ) (he : inner ℝ e e = 1) (x:E) :
  Laplacian.laplacian (slabBarrier e t r) x = -(2:ℝ) := by
 let B := stdOrthonormalBasis ℝ E
 rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (slabBarrier e t r) B]
 have each (i : Fin (Module.finrank ℝ E)) :
    iteratedFDeriv ℝ 2 (slabBarrier e t r) x ![B i,B i]
       = -(2:ℝ) * (inner ℝ (B i) e)^2 := by
   have hd := line_second_deriv (F:=slabBarrier e t r) x (B i) (slab_cd e t r x)
   have hfun : (fun s : ℝ => slabBarrier e t r (x + s • (B i))) =
         (fun s : ℝ => r^2 - ((inner ℝ x e - t) + s * (inner ℝ (B i) e))^2) := by
       funext s
       simp [slabBarrier, inner_add_left, real_inner_smul_left]
       ring
   rw [hfun, quad_deriv] at hd
   simpa [mul_pow] using hd.symm -- maybe
 change (∑ i, _) = _
 rw [Finset.sum_congr rfl (fun i hi => each i)]
 have hs' : (∑ i, (inner ℝ (B i) e)^2) = (1:ℝ) := by
   calc
    _ = ∑ i, inner ℝ e (B i) * inner ℝ (B i) e := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [real_inner_comm e (B i)]
        ring
    _ = inner ℝ e e := B.sum_inner_mul_inner e e
    _ = 1 := he
 calc
   _ = -(2:ℝ) * ∑ i, (inner ℝ (B i) e)^2 := by
     rw [Finset.mul_sum]
   _ = -(2:ℝ) := by rw [hs']; ring




/-- On a slab of width at most `1/(2*(K+1))` the zeroth order term cannot
create a negative minimum.  This is the elementary "narrow domain" lemma
used to start and to continue a moving plane.  We formulate it for arbitrary
open/compact sandwiches; in particular extra pieces of boundary can be
inserted without any regularity of that boundary. -/
lemma nonneg_on_thin {E : Type*} [NormedAddCommGroup E]
 [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
 (e : E) (he : inner ℝ e e = 1) (K lo : ℝ) (hK : 0 ≤ K)
 {D C : Set E} (hDC : D ⊆ C) (hD : IsOpen D) (hC : IsCompact C)
 (slab : ∀ x ∈ C, 0 ≤ inner ℝ x e - lo ∧
                         inner ℝ x e - lo ≤ (1/(K+1))/2)
 {F : E → ℝ} (Fc : ContinuousOn F C)
 (bdry : ∀ x ∈ C \ D, 0 ≤ F x)
 (Fd : ∀ x ∈ D, ContDiffAt ℝ 2 F x)
 (eqn : ∀ x ∈ D, ∃ c : ℝ, |c| ≤ K ∧
                - Laplacian.laplacian F x = c * F x) :
 ∀ x ∈ D, 0 ≤ F x := by
 classical
 intro x hx
 have Kp : 0 < K+1 := by linarith
 let r : ℝ := 1/(K+1)
 let L : ℝ := 2*(K+1)^2
 let φ : E → ℝ := slabBarrier e lo r
 have rpos : 0 < r := by dsimp [r]; positivity
 have rcalc : (K+1)^2 * r^2 = (1:ℝ) := by
   dsimp [r]
   field_simp
 have φpos : ∀ y ∈ C, 0 < φ y := by
   intro y hy
   obtain ⟨hy0,hy1⟩ := slab y hy
   dsimp [φ, slabBarrier]
   have : (inner ℝ y e - lo)^2 ≤ (r/2)^2 := by
     have hy1' : inner ℝ y e - lo ≤ r / 2 := by simpa [r] using hy1
     nlinarith
   nlinarith
 have φcon : ContinuousOn φ C := by
   have cd (y:E) : ContDiffAt ℝ 2 (slabBarrier e lo r) y := slab_cd e lo r y
   exact fun y hy => (cd y).continuousAt.continuousWithinAt
 have φder : ∀ y ∈ D, ContDiffAt ℝ 2 φ y := by
   intro y hy; exact slab_cd e lo r y
 have φbar : ∀ y ∈ D, Laplacian.laplacian φ y ≤ - L * φ y := by
   intro y hy
   have hyC := hDC hy
   obtain ⟨hy0,hy1⟩ := slab y hyC
   have upp : φ y ≤ r^2 := by
     dsimp [φ, slabBarrier]
     nlinarith [sq_nonneg (inner ℝ y e - lo)]
   have calcL : L * r^2 = (2:ℝ) := by dsimp [L]; nlinarith [rcalc]
   have lap := slab_lap e lo r he y
   dsimp [φ] at *
   -- `L` is positive; the maximum of φ is r²
   have Lpos : 0 ≤ L := by dsimp [L]; positivity
   rw [lap]
   nlinarith
 have ceqn : ∀ y ∈ D, ∃ c : ℝ, c < L ∧
              - Laplacian.laplacian F y = c * F y := by
   intro y hy
   obtain ⟨c,hc,eqc⟩ := eqn y hy
   refine ⟨c, ?_, eqc⟩
   have hc' := (le_trans (le_abs_self c) hc)
   dsimp [L]
   nlinarith [sq_nonneg K, Kp]
 have nne : C.Nonempty := ⟨x, hDC hx⟩
 exact weak_barrier_minimum_le hDC hD hC nne Fc φcon φpos bdry Fd φder φbar ceqn x hx

/-- Version of the thin-slab lemma for supersolutions.  It is often used
after subtracting a positive annular Hopf barrier. -/
lemma nonneg_on_thin_sup {E : Type*} [NormedAddCommGroup E]
 [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
 (e : E) (he : inner ℝ e e = 1) (K lo : ℝ) (hK : 0 ≤ K)
 {D C : Set E} (hDC : D ⊆ C) (hD : IsOpen D) (hC : IsCompact C)
 (slab : ∀ x ∈ C, 0 ≤ inner ℝ x e - lo ∧
                         inner ℝ x e - lo ≤ (1/(K+1))/2)
 {F : E → ℝ} (Fc : ContinuousOn F C)
 (bdry : ∀ x ∈ C \ D, 0 ≤ F x)
 (Fd : ∀ x ∈ D, ContDiffAt ℝ 2 F x)
 (eqn : ∀ x ∈ D, ∃ c : ℝ, |c| ≤ K ∧
                c * F x ≤ - Laplacian.laplacian F x) :
 ∀ x ∈ D, 0 ≤ F x := by
 classical
 intro x hx
 have Kp : 0 < K+1 := by linarith
 let r : ℝ := 1/(K+1)
 let L : ℝ := 2*(K+1)^2
 let φ : E → ℝ := slabBarrier e lo r
 have rpos : 0 < r := by dsimp [r]; positivity
 have rcalc : (K+1)^2 * r^2 = (1:ℝ) := by
   dsimp [r]
   field_simp
 have φpos : ∀ y ∈ C, 0 < φ y := by
   intro y hy
   obtain ⟨hy0,hy1⟩ := slab y hy
   dsimp [φ, slabBarrier]
   have : (inner ℝ y e - lo)^2 ≤ (r/2)^2 := by
     have hy1' : inner ℝ y e - lo ≤ r / 2 := by simpa [r] using hy1
     nlinarith
   nlinarith
 have φcon : ContinuousOn φ C := by
   have cd (y:E) : ContDiffAt ℝ 2 (slabBarrier e lo r) y := slab_cd e lo r y
   exact fun y hy => (cd y).continuousAt.continuousWithinAt
 have φder : ∀ y ∈ D, ContDiffAt ℝ 2 φ y := by
   intro y hy; exact slab_cd e lo r y
 have φbar : ∀ y ∈ D, Laplacian.laplacian φ y ≤ - L * φ y := by
   intro y hy
   have hyC := hDC hy
   obtain ⟨hy0,hy1⟩ := slab y hyC
   have upp : φ y ≤ r^2 := by
     dsimp [φ, slabBarrier]
     nlinarith [sq_nonneg (inner ℝ y e - lo)]
   have calcL : L * r^2 = (2:ℝ) := by dsimp [L]; nlinarith [rcalc]
   have lap := slab_lap e lo r he y
   dsimp [φ] at *
   -- `L` is positive; the maximum of φ is r²
   have Lpos : 0 ≤ L := by dsimp [L]; positivity
   rw [lap]
   nlinarith
 have ceqn : ∀ y ∈ D, ∃ c : ℝ, c < L ∧
              c * F y ≤ - Laplacian.laplacian F y := by
   intro y hy
   obtain ⟨c,hc,eqc⟩ := eqn y hy
   refine ⟨c, ?_, eqc⟩
   have hc' := (le_trans (le_abs_self c) hc)
   dsimp [L]
   nlinarith [sq_nonneg K, Kp]
 have nne : C.Nonempty := ⟨x, hDC hx⟩
 exact weak_barrier_minimum_sup hDC hD hC nne Fc φcon φpos bdry Fd φder φbar ceqn x hx
end SemilinearPoissonSupport

-- END INLINED FILE: Mathlib/Support/semilinear_poisson_radial_symmetry_0e8f4ce1bc/ThinMax.lean

-- BEGIN INLINED FILE: Mathlib/Support/semilinear_poisson_radial_symmetry_0e8f4ce1bc/NarrowCap.lean
open scoped Topology InnerProductSpace NNReal
open Filter Set Real Metric Topology
namespace SemilinearPoissonSupport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma refl_mem_closedBall' (e z : E) (t : ℝ) (he : ‖e‖ = (1:ℝ)) (ht : 0 ≤ t)
 (hz : z ∈ closedBall (0:E) 1) (hze : t ≤ inner ℝ z e) :
 refl e t z ∈ closedBall (0:E) 1 := by
 apply (mem_closedBall_zero_iff).2
 have h0 := norm_nonneg (refl e t z)
 have h1 := (mem_closedBall_zero_iff).1 hz
 have sq := refl_norm_sq e z t (inner_unit_of_norm he)
 have hz0 := norm_nonneg z
 nlinarith
lemma inner_le_one' (e x:E) (he: ‖e‖=(1:ℝ)) (hx : x ∈ closedBall (0:E) 1) :
 inner ℝ x e ≤ 1 := by
 have A := abs_real_inner_le_norm x e
 have x1 := (mem_closedBall_zero_iff).1 hx
 rw [he, mul_one] at A
 exact le_trans (le_abs_self _) (le_trans A x1)
lemma refl_cont' (e : E) (t:ℝ) : Continuous (fun x : E => refl e t x) := by
 dsimp [refl]
 have hi : Continuous (fun y : E => inner ℝ y e) := by
  have eqn : (fun y : E => inner ℝ y e) = (fun y : E => (innerSL ℝ e) y) := by
   funext y; simp [real_inner_comm]
  rw [eqn]; fun_prop
 fun_prop

/-- The honest starting piece of moving planes.  In a strip whose width is
at most `1/(2(K+1))`, a reflected difference is nonnegative.  Notice no
compact-support assumptions: the spherical part of the boundary is dealt
with separately by positivity of `u`. -/
lemma narrow_cap_nonnegative {n : ℕ}
 (f : ℝ → ℝ) (u : EuclideanSpace ℝ (Fin n) → ℝ) (e : EuclideanSpace ℝ (Fin n)) (t : ℝ) (K : ℝ≥0)
 (he : ‖e‖ = (1:ℝ)) (ht : 0 < t)
 (hwidth : 1 - t ≤ (1 / ((K:ℝ)+1))/2)
 (hf : LipschitzWith K f)
 (hu : ContDiffOn ℝ 2 u (closedBall (0:EuclideanSpace ℝ (Fin n)) 1))
 (upos : ∀ x ∈ ball (0:EuclideanSpace ℝ (Fin n)) 1, 0 < u x)
 (uzero : ∀ x ∈ sphere (0:EuclideanSpace ℝ (Fin n)) 1, u x = 0)
 (hpde : ∀ x ∈ ball (0:EuclideanSpace ℝ (Fin n)) 1,
             - Laplacian.laplacian u x = f (u x)) :
 ∀ z ∈ ball (0:EuclideanSpace ℝ (Fin n)) 1, t < inner ℝ z e →
       0 ≤ u (refl e t z) - u z := by
 classical
 let D : Set (EuclideanSpace ℝ (Fin n)) := capOpen e t
 let C : Set (EuclideanSpace ℝ (Fin n)) := capClosed e t
 let F : EuclideanSpace ℝ (Fin n) → ℝ := fun x => u (refl e t x) - u x
 have DC : D ⊆ C := capOpen_subset e t
 have op : IsOpen D := capOpen_open e t
 have cp : IsCompact C := capClosed_compact e t
 have slab : ∀ x ∈ C, 0 ≤ inner ℝ x e - t ∧
              inner ℝ x e - t ≤ (1/((K:ℝ)+1))/2 := by
   intro x hx
   have low : t ≤ inner ℝ x e := hx.2
   have up : inner ℝ x e ≤ 1 := inner_le_one' e x he hx.1
   constructor
   · linarith
   · linarith
 have Fcon : ContinuousOn F C := by
   have hucon := hu.continuousOn
   have hcsub : C ⊆ closedBall (0:EuclideanSpace ℝ (Fin n)) 1 := by intro x hx; exact hx.1
   have hure : ContinuousOn (fun x : EuclideanSpace ℝ (Fin n) => u (refl e t x)) C := by
     apply ContinuousOn.comp hucon (refl_cont' e t).continuousOn
     intro x hx
     exact refl_mem_closedBall' e x t he (le_of_lt ht) hx.1 hx.2
   exact hure.sub (hucon.mono hcsub)
 have Fbd : ∀ x ∈ C \ D, 0 ≤ F x := by
   simpa [F, C, D] using
     (reflected_boundary_nonneg u e t he ht upos uzero)
 have Fder : ∀ x ∈ D, ContDiffAt ℝ 2 F x := by
   intro x hx
   have hx' : x ∈ ball (0:EuclideanSpace ℝ (Fin n)) 1 := hx.1
   have hr' := refl_mem_ball e x t he ht hx' hx.2
   have hxC2 := contDiffAt_ball_of_closed hu hx'
   have hrC2 := contDiffAt_ball_of_closed hu hr'
   have comp : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => u (refl e t y)) x :=
        ContDiffAt.comp x hrC2 (contDiff_refl e t).contDiffAt
   exact comp.sub hxC2
 have Feq : ∀ x ∈ D, ∃ c : ℝ, |c| ≤ (K:ℝ) ∧
         - Laplacian.laplacian F x = c * F x := by
   intro x hx
   have hx' : x ∈ ball (0:EuclideanSpace ℝ (Fin n)) 1 := hx.1
   have hr' := refl_mem_ball e x t he ht hx' hx.2
   obtain ⟨c,hc,hce⟩ := lipschitz_secant hf (u (refl e t x)) (u x)
   refine ⟨c,hc,?_⟩
   have H := reflected_difference_eq f u e t x he hu hx' hr' hpde
   dsimp [F]
   rw [H, hce]
 have allnon := nonneg_on_thin e (inner_unit_of_norm he) (K:ℝ) t
       (by exact_mod_cast K.coe_nonneg) DC op cp slab Fcon Fbd Fder Feq
 intro z hz hzt
 exact allnon z ⟨hz,hzt⟩
end SemilinearPoissonSupport

-- END INLINED FILE: Mathlib/Support/semilinear_poisson_radial_symmetry_0e8f4ce1bc/NarrowCap.lean

-- BEGIN INLINED FILE: Mathlib/Support/semilinear_poisson_radial_symmetry_0e8f4ce1bc/Strong.lean
open scoped Topology InnerProductSpace NNReal
open Filter Set Real Metric Topology
namespace SemilinearPoissonSupport

/-- A very small (and handy) weak minimum principle.  The positive zeroth
order term removes all complications about the size of the set.  We state it
for a compact/open sandwich, since the closed annuli used in the strong
principle have exactly this form. -/
lemma weak_minimum_pos {E : Type*} [NormedAddCommGroup E]
 [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
 {V C : Set E} (hVC : V ⊆ C) (hV : IsOpen V) (hC : IsCompact C)
 {G : E → ℝ} {A : ℝ} (hA : 0 < A)
 (Gc : ContinuousOn G C)
 (bdry : ∀ x ∈ C \ V, 0 ≤ G x)
 (Gd : ∀ x ∈ V, ContDiffAt ℝ 2 G x)
 (ineq : ∀ x ∈ V, Laplacian.laplacian G x ≤ A * G x) :
 ∀ x ∈ V, 0 ≤ G x := by
  classical
  intro x hx
  by_contra negx
  have hne : C.Nonempty := ⟨x, hVC hx⟩
  obtain ⟨p, hpC, hp⟩ := hC.exists_isMinOn hne Gc
  have hpneg : G p < 0 := lt_of_le_of_lt (hp (hVC hx)) (lt_of_not_ge negx)
  have hpV : p ∈ V := by
    by_contra hp'
    have h := bdry p ⟨hpC, hp'⟩
    linarith
  have hloc : IsLocalMin G p := by
    have : ∀ᶠ y in 𝓝 p, G p ≤ G y := by
      filter_upwards [hV.mem_nhds hpV] with y hy
      exact hp (hVC hy)
    exact this
  have lap := laplacian_nonneg_at_localMin (Gd p hpV) hloc
  have bound := ineq p hpV
  have : G p < 0 := hpneg
  nlinarith

variable {E : Type*} [NormedAddCommGroup E]
 [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- squared distance as an algebraic expression.  In a real inner product
space it is smoother to differentiate this one than `dist`. -/
def sqc (a : E) (x : E) : ℝ := inner ℝ (x-a) (x-a)

def annBarrier (a : E) (R M : ℝ) (x : E) : ℝ :=
  let h := R^2 - sqc a x
  h + M*h^2

lemma sqc_norm (a x : E) : sqc a x = ‖x-a‖^2 := by
  simp [sqc, real_inner_self_eq_norm_sq]

lemma sqc_cd (a x : E) : ContDiffAt ℝ 2 (sqc a) x := by
  change ContDiffAt ℝ 2 (fun y : E => inner ℝ (y-a) (y-a)) x
  exact (by fun_prop : ContDiffAt ℝ 2 (fun y : E => y-a) x).inner ℝ (by fun_prop)

lemma annBarrier_cd (a : E) (R M : ℝ) (x : E) :
    ContDiffAt ℝ 2 (annBarrier a R M) x := by
  change ContDiffAt ℝ 2 (fun y : E =>
    (R^2 - sqc a y) + M * (R^2 - sqc a y)^2) x
  have hs := sqc_cd a x
  fun_prop

-- The one-dimensional polynomial identity used to take the trace.  Keeping
-- this lemma separate makes the Laplacian calculation below pleasantly
-- algebraic (no multivariable differentiation formula for products needed).
lemma poly_second (s q R M : ℝ) :
  deriv (deriv (fun r : ℝ =>
    let w := R^2 - (s + 2*r*q + r^2)
    w + M*w^2)) 0 =
    -2 - 4*M*(R^2-s) + 8*M*q^2 := by
  let W : ℝ → ℝ := fun r => R^2 - (s + 2*r*q + r^2)
  have hW (r:ℝ) : HasDerivAt W (-(2*q + 2*r)) r := by
    have hS : HasDerivAt (fun r : ℝ => s + 2*r*q + r^2)
          (2*q + 2*r) r := by
      convert
        (( (hasDerivAt_const (x:=r) (c:=s)).add
              ((hasDerivAt_id r).const_mul (2*q))).add
                ((hasDerivAt_id r).pow 2)) using 1 <;>
        first | rfl | (ext z; simp [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply] <;> ring) | (norm_num <;> ring)
    convert ((hasDerivAt_const (x:=r) (c:=R^2)).sub hS) using 1 <;>
      first | rfl | (ext z; simp [W, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply] <;> ring) | (norm_num [W] <;> ring)

  let H : ℝ → ℝ := fun r => W r + M * (W r)^2
  have hH (r:ℝ) : HasDerivAt H
       ((-(2*q+2*r)) + M*(2 * W r * (-(2*q+2*r)))) r := by
    convert (hW r).add (((hW r).pow 2).const_mul M) using 1 <;>
      first | rfl | (ext z; simp [H, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply] <;> ring) | (norm_num [H] <;> ring)
  have dH : deriv H = (fun r =>
       (-(2*q+2*r)) + M*(2 * W r * (-(2*q+2*r)))) :=
    funext (fun r => (hH r).deriv)
  change deriv (deriv H) 0 = _
  rw [dH]
  have hLin (r:ℝ) : HasDerivAt (fun r : ℝ => -(2*q+2*r)) (-2) r := by
    convert ((hasDerivAt_const (x:=r) (c:=(-2*q))).sub
        ((hasDerivAt_id r).const_mul 2)) using 1 <;>
      first | rfl | (ext z; simp [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply] <;> ring) | (norm_num <;> ring)
  have hcalc : HasDerivAt (fun r : ℝ =>
       (-(2*q+2*r)) + M*(2 * W r * (-(2*q+2*r))))
       (-2 + M*(2 * (-(2*q+2*(0:ℝ))) * (-(2*q+2*(0:ℝ))) +
                    2 * W 0 * (-2))) 0 := by
      convert (hLin 0).add
        ((((hW 0).const_mul 2).mul (hLin 0)).const_mul M) using 1 <;>
          first | rfl | (ext z; simp [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply] <;> ring) | (norm_num <;> ring)
  convert hcalc.deriv using 1 <;> dsimp [W] <;> ring

-- Formula for the Laplacian of the elementary annular barrier.
lemma annBarrier_lap (a : E) (R M : ℝ) (x : E) :
 Laplacian.laplacian (annBarrier a R M) x =
   - (2:ℝ) * (Module.finrank ℝ E) -
       4*M*(Module.finrank ℝ E)*(R^2 - sqc a x) +
       8*M*sqc a x := by
  classical
  let B := stdOrthonormalBasis ℝ E
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
        (annBarrier a R M) B]
  change (∑ i : Fin (Module.finrank ℝ E), _) = _
  have each (i : Fin (Module.finrank ℝ E)) :
    iteratedFDeriv ℝ 2 (annBarrier a R M) x ![B i, B i] =
       -2 - 4*M*(R^2-sqc a x) + 8*M*(inner ℝ (x-a) (B i))^2 := by
    have hd := line_second_deriv (F:=annBarrier a R M) x (B i)
       (annBarrier_cd a R M x)
    have hnorm : inner ℝ (B i) (B i) = (1:ℝ) := (by simpa [real_inner_self_eq_norm_sq] using congrArg (fun q : ℝ => q^2) (B.orthonormal.norm_eq_one i))
    -- expand the squared distance along the line
    have hline : (fun r : ℝ => annBarrier a R M (x + r • (B i))) =
        (fun r : ℝ =>
          let w := R^2 -
             (sqc a x + 2*r*(inner ℝ (x-a) (B i)) + r^2)
          w + M*w^2) := by
       funext r
       dsimp [annBarrier, sqc]
       -- bilinearity of the inner product
       rw [sub_eq_add_neg (x + r • (B i)) a]
       -- easier with sub_add
       have hx : x + r • (B i) - a = (x-a) + r • (B i) := by
         module
       have hx' : x + r • (B i) + -a = (x-a) + r • (B i) := by
         module
       rw [hx', inner_add_left, inner_add_right, inner_add_right,
           real_inner_smul_left, real_inner_smul_right,
           real_inner_smul_left, real_inner_smul_right, hnorm]
       rw [real_inner_comm (B i) (x-a)]
       ring
    rw [hline, poly_second] at hd
    simpa using hd.symm
  rw [Finset.sum_congr rfl (fun i hi => each i)]
  let N : ℝ := (Module.finrank ℝ E : ℝ)
  have hs : (∑ i : Fin (Module.finrank ℝ E),
        (inner ℝ (x-a) (B i))^2) = sqc a x := by
    -- resolution of the identity in an orthonormal basis
    have H := B.sum_inner_mul_inner (x-a) (x-a)
    -- make all factors have the same orientation
    calc
      _ = ∑ i : Fin (Module.finrank ℝ E),
          inner ℝ (x-a) (B i) * inner ℝ (B i) (x-a) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [real_inner_comm (B i) (x-a)]
            ring
      _ = inner ℝ (x-a) (x-a) := H
      _ = sqc a x := rfl
  have card : ((Finset.univ : Finset (Fin (Module.finrank ℝ E))).card : ℝ) =
       (Module.finrank ℝ E : ℝ) := by simp
  rw [Finset.sum_add_distrib]
  have hconst : (∑ _i : Fin (Module.finrank ℝ E),
          (-2 - 4*M*(R^2-sqc a x))) =
       (Module.finrank ℝ E : ℝ) * (-2 - 4*M*(R^2-sqc a x)) := by simp; ring
  rw [hconst]
  rw [← Finset.mul_sum]
  rw [hs]
  ring
/-- In the outer part of a sufficiently small ball the elementary quadratic
barrier is a subsolution of `Δ v = A v`. -/
lemma annBarrier_good (a x : E) (R A : ℝ) (hR : 0 < R)
 (hA : 0 < A) (hsmall : A*R^2 ≤ 1)
 (hout : sqc a x ≤ R^2)
 (hin : R^2 - sqc a x ≤ R^2 / ((Module.finrank ℝ E : ℝ)+2)) :
   A * annBarrier a R (((Module.finrank ℝ E : ℝ)+1)/R^2) x ≤
       Laplacian.laplacian
         (annBarrier a R (((Module.finrank ℝ E : ℝ)+1)/R^2)) x := by
  let n : ℝ := (Module.finrank ℝ E : ℝ)
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have hn2 : 0 < n+2 := by linarith
  have r2 : 0 < R^2 := sq_pos_of_pos hR
  let h : ℝ := R^2 - sqc a x
  have h0 : 0 ≤ h := by dsimp [h]; linarith
  have hs : sqc a x = R^2 - h := by dsimp [h]; ring
  have hh : (n+2)*h ≤ R^2 := by
    have := hin
    change R^2 - sqc a x ≤ R^2 / (n+2) at this
    have hh' := (le_div_iff₀ hn2).mp this
    dsimp [h]
    rw [mul_comm]
    simpa using hh'
  rw [annBarrier_lap]
  change A * (h + ( (n+1)/R^2)*h^2) ≤ _
  -- eliminate the denominator with a positive factor `R^2`
  have nn : 0 ≤ n+1 := by linarith
  have ah : 0 ≤ A*h := mul_nonneg (le_of_lt hA) h0
  have hRone : A* R^2 ≤ 1 := hsmall
  have calc8 : 4* R^2 ≤
       8* R^2 - (8+4*n)*h := by nlinarith
  -- the useful lower bound for the part carrying `(n+1)/R²`
  have major : 4*R^2 ≤ 8*(R^2-h) - 4*n*h := by nlinarith
  have target :
    A * (h + ((n+1)/R^2)*h^2) ≤
      -2*n - 4*((n+1)/R^2)*n*h +
        8*((n+1)/R^2)*(R^2-h) := by
    -- multiplication by the square radius clears the only denominators
    apply (mul_le_mul_iff_of_pos_left r2).mp
    field_simp
    -- everything left is polynomial; the crude bounds above suffice
    nlinarith [mul_nonneg nn
        (sub_nonneg.mpr major),
      mul_nonneg h0 (sub_nonneg.mpr hsmall),
      mul_nonneg (mul_nonneg nn h0) (sub_nonneg.mpr hsmall)]
  change A * (h + ((n+1)/R^2)*h^2) ≤ _
  convert target using 1 <;> dsimp [n, h] <;> ring


/-- Comparison with a sub-barrier for the operator `Δ-A`.
This elementary form is often the useful half of the strong minimum
principle: on a closed annulus one obtains a positive lower bound from the
inner circle and differentiates it at the outer one.-/
lemma compare_subbarrier
 {V C : Set E} (hVC : V ⊆ C) (hV : IsOpen V) (hC : IsCompact C)
 {F ψ : E → ℝ} {A ε : ℝ} (hA : 0 < A) (hε : 0 ≤ ε)
 (Fc : ContinuousOn F C) (ψc : ContinuousOn ψ C)
 (Fbd : ∀ x ∈ C \ V, ε * ψ x ≤ F x)
 (Fd : ∀ x ∈ V, ContDiffAt ℝ 2 F x)
 (ψd : ∀ x ∈ V, ContDiffAt ℝ 2 ψ x)
 (Fineq : ∀ x ∈ V, Laplacian.laplacian F x ≤ A * F x)
 (ψineq : ∀ x ∈ V, A * ψ x ≤ Laplacian.laplacian ψ x) :
 ∀ x ∈ V, ε * ψ x ≤ F x := by
 classical
 let G : E → ℝ := fun x => F x - ε * ψ x
 have Gc : ContinuousOn G C := by
   apply Fc.sub
   exact continuousOn_const.mul ψc
 have Gd : ∀ x ∈ V, ContDiffAt ℝ 2 G x := by
   intro x hx
   exact (Fd x hx).sub (by
     have h := ψd x hx
     fun_prop)
 have lap (x : E) (hx : x ∈ V) :
     Laplacian.laplacian G x =
       Laplacian.laplacian F x - ε * Laplacian.laplacian ψ x := by
   have hmul : ContDiffAt ℝ 2 (fun y : E => ε * ψ y) x := by
      have h := ψd x hx
      fun_prop
   change Laplacian.laplacian
      (F - fun y : E => ε * ψ y) x = _
   rw [(Fd x hx).laplacian_sub hmul]
   have H := InnerProductSpace.laplacian_smul (f:=ψ) ε (ψd x hx)
   have fn : (fun y : E => ε * ψ y) = ε • ψ := by
     funext y; simp [Pi.smul_apply, smul_eq_mul]
   rw [fn]
   simpa [smul_eq_mul] using H
 have Gineq : ∀ x ∈ V, Laplacian.laplacian G x ≤ A * G x := by
   intro x hx
   rw [lap x hx]
   dsimp [G]
   have h1 := Fineq x hx
   have h2 := ψineq x hx
   nlinarith [mul_nonneg hε (sub_nonneg.mpr h2)]
 have Gbd : ∀ x ∈ C \ V, 0 ≤ G x := by
   intro x hx
   dsimp [G]
   linarith [Fbd x hx]
 have Z := weak_minimum_pos hVC hV hC hA Gc Gbd Gd Gineq
 intro x hx
 have Q := Z x hx
 dsimp [G] at Q
 linarith


def annClosed (a : E) (l r : ℝ) : Set E :=
 {x | l ≤ sqc a x ∧ sqc a x ≤ r^2}
def annOpen (a : E) (l r : ℝ) : Set E :=
 {x | l < sqc a x ∧ sqc a x < r^2}
lemma sqc_cont (a : E) : Continuous (sqc a) := by
 rw [continuous_iff_continuousAt]
 intro x; exact (sqc_cd a x).continuousAt
lemma annOpen_open (a : E) (l r : ℝ) : IsOpen (annOpen a l r) := by
 exact IsOpen.inter (isOpen_lt continuous_const (sqc_cont a))
                   (isOpen_lt (sqc_cont a) continuous_const)
lemma annOpen_sub (a : E) (l r : ℝ) : annOpen a l r ⊆ annClosed a l r := by
 intro x hx; exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
lemma annClosed_compact (a : E) (l r : ℝ) (hr : 0 ≤ r) :
  IsCompact (annClosed a l r) := by
 -- the upper squared inequality puts the set in a compact ball
 have closed : IsClosed (annClosed a l r) :=
   (isClosed_le continuous_const (sqc_cont a)).inter
      (isClosed_le (sqc_cont a) continuous_const)
 refine (ProperSpace.isCompact_closedBall a r).of_isClosed_subset closed ?_
 intro x hx
 have hx' := hx.2
 have d : ‖x-a‖^2 ≤ r^2 := by simpa [sqc_norm] using hx'
 have hnon := norm_nonneg (x-a)
 have le : ‖x-a‖ ≤ r := by nlinarith
 simpa [mem_closedBall, dist_comm, dist_eq_norm, norm_sub_rev] using le


lemma annulus_barrier_compare
 (a : E) {F : E → ℝ} (R l A ε : ℝ)
 (hR : 0 < R) (hA : 0 < A) (hε : 0 ≤ ε) (hsmall : A*R^2 ≤ 1)
 (hl : R^2 - l ≤ R^2 / ((Module.finrank ℝ E : ℝ)+2))
 (Fc : ContinuousOn F (annClosed a l R))
 (Fbd : ∀ x ∈ annClosed a l R \ annOpen a l R,
       ε * annBarrier a R (((Module.finrank ℝ E : ℝ)+1)/R^2) x ≤ F x)
 (Fd : ∀ x ∈ annOpen a l R, ContDiffAt ℝ 2 F x)
 (Fi : ∀ x ∈ annOpen a l R,
      Laplacian.laplacian F x ≤ A * F x) :
 ∀ x ∈ annOpen a l R,
       ε * annBarrier a R (((Module.finrank ℝ E : ℝ)+1)/R^2) x ≤ F x := by
 let ψ : E → ℝ := annBarrier a R (((Module.finrank ℝ E : ℝ)+1)/R^2)
 apply compare_subbarrier
   (annOpen_sub a l R) (annOpen_open a l R)
     (annClosed_compact a l R (le_of_lt hR)) hA hε Fc
     (by intro x hx; exact (annBarrier_cd a R _ x).continuousAt.continuousWithinAt)
     Fbd Fd
     (by intro x hx; exact annBarrier_cd a R _ x)
     Fi
 intro x hx
 apply annBarrier_good a x R A hR hA hsmall (le_of_lt hx.2)
 linarith [hx.1]

end SemilinearPoissonSupport

-- END INLINED FILE: Mathlib/Support/semilinear_poisson_radial_symmetry_0e8f4ce1bc/Strong.lean

-- BEGIN INLINED FILE: Mathlib/Support/semilinear_poisson_radial_symmetry_0e8f4ce1bc/StrongMin.lean
open scoped Topology InnerProductSpace NNReal
open Filter Set Real Metric Topology
namespace SemilinearPoissonSupport
variable {E : Type*} [NormedAddCommGroup E]
 [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The elementary final, tangential, part of the Hopf annulus argument.
It is deliberately separated from the maximum/comparison argument.  If a
function has a (two-sided) differentiable minimum at a point of a sphere,
and it dominates a positive multiple of the standard annular subbarrier on
the inside of that sphere, it cannot vanish there.  No regularity of a
set boundary is involved here -- the point is an *interior* minimum later.
-/
lemma no_interior_zero_of_annbarrier
 (a p : E) {F : E → ℝ} (R ε : ℝ)
 (hR : 0 < R) (hε : 0 < ε)
 (hp : sqc a p = R^2)
 (hmin : IsLocalMin F p) (hder : DifferentiableAt ℝ F p)
 (hz : F p = 0)
 (cmp : ∀ x ∈ annOpen a
       (R^2 - R^2 / ((Module.finrank ℝ E : ℝ)+2)) R,
       ε * annBarrier a R (((Module.finrank ℝ E : ℝ)+1)/R^2) x ≤ F x) :
 False := by
 classical
 let N : ℝ := (Module.finrank ℝ E : ℝ)
 have N0 : 0 ≤ N := by dsimp [N]; exact_mod_cast (Nat.zero_le (Module.finrank ℝ E))
 have N2 : 0 < N + 2 := by linarith
 let v : E := a - p
 let X : ℝ → E := fun s => p + s • v
 let fline : ℝ → ℝ := fun s => F (X s)
 let ψline : ℝ → ℝ := fun s => annBarrier a R ((N+1)/R^2) (X s)
 -- along the line which goes into the ball the radius is `(1-s)R`.
 have xs (s : ℝ) : sqc a (X s) = (1-s)^2 * R^2 := by
   have hx : X s - a = (1-s) • (p-a) := by
     dsimp [X, v]
     module
   dsimp [sqc]
   rw [hx, inner_smul_left, inner_smul_right]
   have hpp : inner ℝ (p-a) (p-a) = R^2 := by
     simpa [sqc] using hp
   rw [hpp]
   simp
   ring
 have ψformula (s : ℝ) :
    ψline s = (R^2 - ((1-s)^2 * R^2)) +
        ((N+1)/R^2) * (R^2 - ((1-s)^2 * R^2))^2 := by
   simp [ψline, annBarrier, xs]
 have ψ0 : ψline 0 = 0 := by rw [ψformula]; ring
 have X0 : X 0 = p := by simp [X]
 have f0 : fline 0 = 0 := by simp [fline, X0, hz]
 -- points just to the right lie in the open annulus to which comparison
 -- applies.  The slightly wasteful `1/(2(N+2))` avoids any square roots.
 let δ : ℝ := 1 / (2 * (N+2))
 have δpos : 0 < δ := by dsimp [δ]; positivity
 have xin (s : ℝ) (s0 : 0 < s) (s1 : s < δ) :
      X s ∈ annOpen a (R^2 - R^2 / ((Module.finrank ℝ E : ℝ)+2)) R := by
   have slt : s < 1 := by
     dsimp [δ] at s1
     have : 1 / (2*(N+2)) ≤ (1:ℝ) := by
       apply (div_le_one (by linarith : (0:ℝ) < 2*(N+2))).2
       linarith
     linarith
   change R^2 - R^2 / ((Module.finrank ℝ E : ℝ)+2) < sqc a (X s) ∧
          sqc a (X s) < R^2
   have eqN : ((Module.finrank ℝ E : ℝ)+2) = N+2 := by rfl
   rw [xs, eqN]
   constructor
   · have two : 2*s < 1/(N+2) := by
       dsimp [δ] at s1
       calc
         2*s < 2 * (1/(2*(N+2))) :=
            mul_lt_mul_of_pos_left s1 (by norm_num)
         _ = 1/(N+2) := by field_simp
     have rpos : 0 < R^2 := sq_pos_of_pos hR
     have H : R^2 * (2*s - s^2) < R^2 * (1/(N+2)) := by
       apply (mul_lt_mul_of_pos_left _ rpos)
       nlinarith [sq_pos_of_pos s0]
     have H' : R^2 * (2*s-s^2) < R^2 / (N+2) := by
       convert H using 1 <;> ring
     calc
       R^2 - R^2 / (N+2) < R^2 - R^2 * (2*s-s^2) := sub_lt_sub_left H' _
       _ = (1-s)^2 * R^2 := by ring
   · have rpos : 0 < R^2 := sq_pos_of_pos hR
     have : (1-s)^2 < (1:ℝ) := by nlinarith
     nlinarith
 -- consequently `f-εψ` has a one-sided minimum at zero.
 let g : ℝ → ℝ := fun s => fline s - ε * ψline s
 have glower : IsLocalMinOn g (Ici (0:ℝ)) 0 := by
   have eventually : ∀ᶠ s in 𝓝[Ici (0:ℝ)] (0:ℝ),
       g 0 ≤ g s := by
     have evlt : Iio δ ∈ 𝓝 (0:ℝ) := Iio_mem_nhds δpos
     filter_upwards [(self_mem_nhdsWithin),
       (mem_of_superset (inter_mem (mem_nhdsWithin_of_mem_nhds evlt)
          (self_mem_nhdsWithin)) (inter_subset_left))] with s hs hslt
     -- the second filter above is merely the strict upper bound
     have slt : s < δ := hslt
     have snon : 0 ≤ s := hs
     by_cases se : s = 0
     · subst s; exact le_rfl
     have spos : 0 < s := lt_of_le_of_ne snon (Ne.symm se)
     have inA := xin s spos slt
     have comp := cmp (X s) inA
     have : ε * ψline s ≤ fline s := by
       convert comp using 1 <;> simp [ψline, fline, N]
     have gzero : g 0 = 0 := by simp [g, f0, ψ0]
     rw [gzero]
     dsimp [g]
     linarith
   -- local minimum-on is exactly an eventual inequality in the restricted
   -- neighbourhood filter.
   exact eventually
 -- the full line, on the other hand, has a two sided minimum because `F`
 -- does at `p`.
 have flmin : IsLocalMin fline 0 := by
   have xl : ContinuousAt X 0 := by
     dsimp [X]
     fun_prop
   have hpmin : IsLocalMin F (X 0) := by simpa [X0] using hmin
   have A := hpmin.comp_continuous xl
   simpa [fline, Function.comp_def] using A
 have fd : DifferentiableAt ℝ fline 0 := by
   have Xd : DifferentiableAt ℝ X 0 := by
     dsimp [X, v]
     fun_prop
   have hpder : DifferentiableAt ℝ F (X 0) := by simpa [X0] using hder
   have H := hpder.comp 0 Xd
   simpa [X0, fline, Function.comp_def] using H
 let d : ℝ := deriv fline 0
 have fh : HasDerivAt fline d 0 := fd.hasDerivAt
 have dz : d = 0 := flmin.deriv_eq_zero
 -- derivative of the explicit polynomial annulus on that line
 let w : ℝ → ℝ := fun s => R^2 - (1-s)^2 * R^2
 have wh : HasDerivAt w (2*R^2) 0 := by
   dsimp [w]
   convert ((hasDerivAt_const (x:=(0:ℝ)) (c:=R^2)).sub
       (((( (hasDerivAt_const (x:=(0:ℝ)) (c:=(1:ℝ))).sub
            (hasDerivAt_id (0:ℝ))).pow 2).mul_const (R^2)))) using 1 <;>
     first | rfl | (ext z; simp [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply] <;> ring) | (norm_num <;> ring)
 have ψh : HasDerivAt ψline (2*R^2) 0 := by
   have temp := wh.add ((wh.pow 2).const_mul ((N+1)/R^2))
   convert temp using 1 <;> try {rfl}
   · funext s
     rw [ψformula]
     simp [w, Pi.add_apply, Pi.pow_apply]
   · norm_num [w]
 have gh : HasDerivAt g (d - ε*(2*R^2)) 0 := by
   have temp := fh.sub (ψh.const_mul ε)
   convert temp using 1 <;> try {rfl} <;>
     first
     | rfl
     | (ext s; simp [g, Pi.sub_apply, Pi.mul_apply]; ring)
     | ring
 have tangent : (1:ℝ) ∈ posTangentConeAt (Ici (0:ℝ)) 0 := by
   have H := sub_mem_posTangentConeAt_of_openSegment_subset
       (x:=(0:ℝ)) (y:=(1:ℝ)) (s:=Ici (0:ℝ)) (by
         intro x hx
         have hx' := openSegment_subset_segment ℝ (0:ℝ) (1:ℝ) hx
         have hx'' : 0 ≤ x := by
           rw [segment_eq_Icc (by norm_num : (0:ℝ) ≤ 1)] at hx'
           exact hx'.1
         exact hx'')
   simpa using H
 have non := glower.hasFDerivWithinAt_nonneg
    gh.hasDerivWithinAt.hasFDerivWithinAt tangent
 have val : (ContinuousLinearMap.toSpanSingleton ℝ
      (d - ε*(2*R^2))) (1:ℝ) = d - ε*(2*R^2) := by simp
 rw [val] at non
 have rp : 0 < R^2 := sq_pos_of_pos hR
 nlinarith
end SemilinearPoissonSupport

namespace SemilinearPoissonSupport
variable {E : Type*} [NormedAddCommGroup E]
 [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
/-- A directly reusable Hopf-annulus version of the strong-minimum step.
All the hypotheses are on an *ordinary closed annulus*.  This is often a
cleaner interface than a smooth-boundary formulation: the containing domain
will be an open ball/cap. `Fmin` is automatic at an interior zero of a
nonnegative function.
-/
lemma no_zero_of_annulus
 (a p : E) {F : E → ℝ} (R A ε : ℝ)
 (hR : 0 < R) (hA : 0 < A) (hε : 0 < ε) (hsmall : A*R^2 ≤ 1)
 (hp : sqc a p = R^2)
 (Fc : ContinuousOn F (annClosed a
        (R^2 - R^2 / ((Module.finrank ℝ E : ℝ)+2)) R))
 (Fbd : ∀ x ∈ annClosed a
          (R^2 - R^2 / ((Module.finrank ℝ E : ℝ)+2)) R \
                      annOpen a (R^2 - R^2 / ((Module.finrank ℝ E : ℝ)+2)) R,
       ε * annBarrier a R (((Module.finrank ℝ E : ℝ)+1)/R^2) x ≤ F x)
 (Fd : ∀ x ∈ annOpen a
        (R^2 - R^2 / ((Module.finrank ℝ E : ℝ)+2)) R,
          ContDiffAt ℝ 2 F x)
 (Fi : ∀ x ∈ annOpen a
        (R^2 - R^2 / ((Module.finrank ℝ E : ℝ)+2)) R,
          Laplacian.laplacian F x ≤ A * F x)
 (Fmin : IsLocalMin F p) (Fder : DifferentiableAt ℝ F p)
 (Fzero : F p = 0) : False := by
 classical
 have cmp := annulus_barrier_compare a R
      (R^2 - R^2 / ((Module.finrank ℝ E : ℝ)+2)) A ε
      hR hA (le_of_lt hε) hsmall (by linarith) Fc Fbd Fd Fi
 exact no_interior_zero_of_annbarrier a p R ε hR hε hp Fmin Fder Fzero cmp

/-- Existence of the positive multiple required on the inner rim of an
annulus.  Compactness is the only point here; keeping it separate is useful
in sliding arguments where `F` depends on a parameter. -/
lemma annulus_inner_bound
  (a : E) {F : E → ℝ} (R : ℝ) (hR : 0 < R)
  (Fc : ContinuousOn F (annClosed a
        (R^2 - R^2 / ((Module.finrank ℝ E : ℝ)+2)) R))
  (Fnon : ∀ x ∈ annClosed a
        (R^2 - R^2 / ((Module.finrank ℝ E : ℝ)+2)) R, 0 ≤ F x)
  (Fin : ∀ x, sqc a x =
        (R^2 - R^2 / ((Module.finrank ℝ E : ℝ)+2)) → 0 < F x) :
  ∃ ε : ℝ, 0 < ε ∧
    ∀ x ∈ annClosed a
          (R^2 - R^2 / ((Module.finrank ℝ E : ℝ)+2)) R \
                    annOpen a (R^2 - R^2 / ((Module.finrank ℝ E : ℝ)+2)) R,
       ε * annBarrier a R (((Module.finrank ℝ E : ℝ)+1)/R^2) x ≤ F x := by
 classical
 let N : ℝ := (Module.finrank ℝ E : ℝ)
 have N0 : 0 ≤ N := by dsimp [N]; positivity
 have dpos : 0 < N+2 := by linarith
 let l : ℝ := R^2 - R^2/(N+2)
 have rpos : 0 < R^2 := sq_pos_of_pos hR
 have lr : l < R^2 := by dsimp [l]; have : 0 < R^2/(N+2) := div_pos rpos dpos; linarith
 let S : Set E := {x | x ∈ annClosed a l R ∧ sqc a x = l}
 have Sc : IsCompact S := by
   have base := annClosed_compact a l R (le_of_lt hR)
   have clos : IsClosed {x : E | sqc a x = l} :=
     isClosed_eq (sqc_cont a) continuous_const
   exact base.of_isClosed_subset (base.isClosed.inter clos)
       (by intro x hx; exact hx.1)
 -- If the level is empty there is nothing to check on that part of the
 -- boundary.  This also covers the zero-dimensional space.
 by_cases Sne : S.Nonempty
 · obtain ⟨q,hqS,hq⟩ := Sc.exists_isMinOn Sne
       (Fc.mono (by intro x hx; exact hx.1))
   have qpos : 0 < F q := by
     apply Fin q
     simpa [S, l, N] using hqS.2
   let W : ℝ := annBarrier a R ((N+1)/R^2) q
   -- one common upper bound for the barrier on the inner sphere; it is
   -- constant there, but using `|W|+1` avoids any normalisation algebra.
   let ε : ℝ := F q / (|W|+1)
   have den : 0 < |W|+1 := by positivity
   have ep : 0 < ε := div_pos qpos den
   refine ⟨ε, ep, ?_⟩
   intro x hx
   have bd : sqc a x = l ∨ sqc a x = R^2 := by
     have one := hx.1.1
     have two := hx.1.2
     have no := hx.2
     dsimp [annOpen] at no
     by_cases hxl : sqc a x = l
     · exact Or.inl hxl
     right
     have : ¬ sqc a x < R^2 := by
       intro h
       exact no ⟨lt_of_le_of_ne one (Ne.symm hxl), h⟩
     exact le_antisymm two (not_lt.mp this)
   rcases bd with il | ou
   · have xs : x ∈ S := by exact ⟨hx.1, il⟩
     have lo : F q ≤ F x := hq xs
     have same : annBarrier a R (((Module.finrank ℝ E : ℝ)+1)/R^2) x = W := by
       dsimp [W, annBarrier]
       rw [il, hqS.2]
     rw [same]
     have we : ε * W ≤ F q := by
       dsimp [ε]
       have ww : W ≤ |W|+1 := (by have H := le_abs_self W; linarith)
       have ff : 0 ≤ F q := le_of_lt qpos
       calc
        F q / (|W|+1) * W ≤ F q / (|W|+1) * (|W|+1) :=
          mul_le_mul_of_nonneg_left ww (le_of_lt ep)
        _ = F q := by field_simp
     linarith
   · have z : annBarrier a R (((Module.finrank ℝ E : ℝ)+1)/R^2) x = 0 := by
       simp [annBarrier, ou]
     rw [z, mul_zero]
     exact Fnon x hx.1
 · refine ⟨(1:ℝ), by norm_num, ?_⟩
   intro x hx
   have notin : sqc a x ≠ l := by
     intro e
     exact Sne ⟨x, hx.1, e⟩
   have out : sqc a x = R^2 := by
     have hle := hx.1.2
     have hlo := hx.1.1
     have ni := hx.2
     dsimp [annOpen] at ni
     have : ¬ sqc a x < R^2 := by
       intro h; exact ni ⟨lt_of_le_of_ne hlo (Ne.symm notin), h⟩
     exact le_antisymm hle (not_lt.mp this)
   have z : annBarrier a R (((Module.finrank ℝ E : ℝ)+1)/R^2) x = 0 := by
     simp [annBarrier, out]
   rw [z]; simp
   exact Fnon x hx.1
end SemilinearPoissonSupport
namespace SemilinearPoissonSupport
open Metric
variable {E : Type*} [NormedAddCommGroup E]
 [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
/-- Convenient combination.  In applications the inner sphere lies in the
strict-positive component, `F≥0` on the annulus, and the outer touching
point is interior to the original domain. -/
lemma annulus_touch_strong
 (a p : E) {F : E → ℝ} (R A : ℝ)
 (hR : 0 < R) (hA : 0 < A) (hsmall : A*R^2 ≤ 1)
 (hp : sqc a p = R^2)
 (Fc : ContinuousOn F (annClosed a
        (R^2 - R^2 / ((Module.finrank ℝ E : ℝ)+2)) R))
 (Fn : ∀ x ∈ annClosed a
        (R^2 - R^2 / ((Module.finrank ℝ E : ℝ)+2)) R, 0 ≤ F x)
 (Fin : ∀ x, sqc a x =
        (R^2 - R^2 / ((Module.finrank ℝ E : ℝ)+2)) → 0 < F x)
 (Fd : ∀ x ∈ annOpen a
        (R^2 - R^2 / ((Module.finrank ℝ E : ℝ)+2)) R, ContDiffAt ℝ 2 F x)
 (Fi : ∀ x ∈ annOpen a
        (R^2 - R^2 / ((Module.finrank ℝ E : ℝ)+2)) R,
            Laplacian.laplacian F x ≤ A * F x)
 (Fm : IsLocalMin F p) (Fder : DifferentiableAt ℝ F p)
 (Fz : F p = 0) : False := by
 obtain ⟨ε,e0,eb⟩ := annulus_inner_bound a R hR Fc Fn Fin
 exact no_zero_of_annulus a p R A ε hR hA e0 hsmall hp Fc eb Fd Fi Fm Fder Fz
end SemilinearPoissonSupport

-- END INLINED FILE: Mathlib/Support/semilinear_poisson_radial_symmetry_0e8f4ce1bc/StrongMin.lean

-- BEGIN INLINED FILE: Mathlib/Support/semilinear_poisson_radial_symmetry_0e8f4ce1bc/StrongDomain.lean
open scoped Topology InnerProductSpace NNReal
open Filter Set Real Metric Topology
namespace SemilinearPoissonSupport
variable {E : Type*} [NormedAddCommGroup E]
 [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A zero of a nonnegative subsolution is locally a zero.  This is the
local step in the strong minimum principle.  Its proof is the elementary
annular Hopf argument; keeping the domain open avoids any boundary
regularity. -/
lemma zero_near_of_nonnegative
 {D : Set E} (ho : IsOpen D) {F : E → ℝ} {A : ℝ} (hA : 0 < A)
 (Fc : ∀ x ∈ D, ContinuousAt F x)
 (Fn : ∀ x ∈ D, 0 ≤ F x)
 (Fd : ∀ x ∈ D, ContDiffAt ℝ 2 F x)
 (Fi : ∀ x ∈ D, Laplacian.laplacian F x ≤ A * F x)
 {p : E} (hp : p ∈ D) (hz : F p = 0) :
 ∃ r : ℝ, 0 < r ∧ ∀ x ∈ ball p r, F x = 0 := by
 classical
 obtain ⟨d, d0, hd⟩ := (Metric.isOpen_iff.mp ho) p hp
 have A1 : 0 < A+1 := by linarith
 let ρ : ℝ := min (d/2) (1/(A+1))
 have ρ0 : 0 < ρ := by
   dsimp [ρ]
   exact lt_min (by linarith) (by positivity)
 have ρd : ρ < d := by
   have hle : ρ ≤ d/2 := min_le_left _ _
   linarith
 have ballρ : closedBall p ρ ⊆ D :=
   fun x hx => hd (Metric.closedBall_subset_ball ρd hx)
 have ballρ2D : closedBall p (ρ/2) ⊆ D :=
   fun x hx => ballρ (Metric.closedBall_subset_closedBall (by linarith : ρ/2 ≤ ρ) hx)
 have smallρ : A * ρ^2 ≤ 1 := by
   have hle : ρ ≤ 1/(A+1) := min_le_right _ _
   have h0 : 0 ≤ ρ := le_of_lt ρ0
   have hsq : ρ^2 ≤ (1/(A+1))^2 := by nlinarith
   have base : A * (1/(A+1))^2 ≤ 1 := by
     have ap : 0 < (A+1)^2 := sq_pos_of_pos A1
     have hle' : A ≤ (A+1)^2 := by nlinarith [sq_nonneg A]
     calc
       A * (1/(A+1))^2 = A / (A+1)^2 := by field_simp
       _ ≤ 1 := (div_le_one ap).2 hle' 
   calc
     A * ρ^2 ≤ A * (1/(A+1))^2 := by nlinarith
     _ ≤ 1 := base
 refine ⟨ρ/4, by positivity, ?_⟩
 intro y hy
 have hynear : y ∈ closedBall p (ρ/2) := by
   have hdist : dist y p < ρ/4 := by simpa [mem_ball] using hy
   have : dist y p ≤ ρ/2 := by linarith
   simpa [mem_closedBall] using this
 have hyD : y ∈ D := ballρ2D hynear
 by_contra yn
 have ypos : 0 < F y := lt_of_le_of_ne (Fn y hyD) (Ne.symm yn)
 -- zeros in a fixed small closed ball form a compact set.  Choose one
 -- closest to `y`.
 let T : Set E := closedBall p (ρ/2) ∩ {x | F x = 0}
 have Tne : T.Nonempty := by
   refine ⟨p, ?_⟩
   change p ∈ closedBall p (ρ/2) ∩ {x : E | F x = 0}
   constructor
   · simp [show 0 ≤ ρ/2 by linarith]
   · exact hz
 have Fball : ContinuousOn F (closedBall p (ρ/2)) :=
   fun x hx => (Fc x (ballρ2D hx)).continuousWithinAt
 obtain ⟨u, hucl, hu⟩ :=
   (continuousOn_iff_isClosed.mp Fball) ({0} : Set ℝ) isClosed_singleton
 have Teq : T = closedBall p (ρ/2) ∩ u := by
   dsimp [T]
   ext x
   have heq : x ∈ F ⁻¹' ({0} : Set ℝ) ↔ F x = 0 := by simp
   -- `hu` identifies the relative preimage.
   have hpt := Set.ext_iff.mp hu x
   simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] at hpt
   constructor
   · rintro ⟨hb,hz'⟩
     exact ⟨hb, (hpt.mp ⟨hz', hb⟩).1⟩
   · rintro ⟨hb,hu'⟩
     exact ⟨hb, (hpt.mpr ⟨hu', hb⟩).1⟩
 have Tcomp : IsCompact T := by
   rw [Teq]
   exact (ProperSpace.isCompact_closedBall p (ρ/2)).inter_right hucl
 let g : E → ℝ := fun x => dist y x
 have gc : Continuous g := by
   dsimp [g]
   fun_prop
 obtain ⟨w, hwT, hmin⟩ := Tcomp.exists_isMinOn Tne gc.continuousOn
 have hwB : w ∈ closedBall p (ρ/2) := hwT.1
 have hwz : F w = 0 := hwT.2
 let R : ℝ := dist y w
 have Ry : R ≤ dist y p := by
   apply hmin
   change p ∈ T
   change p ∈ closedBall p (ρ/2) ∩ {x : E | F x = 0}
   constructor
   · simp [show 0 ≤ ρ/2 by linarith]
   · exact hz
 have yp : dist y p < ρ/4 := by simpa [mem_ball] using hy
 have Rlt : R < ρ/4 := lt_of_le_of_lt Ry yp
 have Rpos : 0 < R := by
   dsimp [R]
   exact dist_pos.mpr (by
     intro eyw
     subst w
     exact (ne_of_gt ypos) hwz)
 -- the entire touching ball is still in the small closed ball.
 have subball (x : E) (hx : x ∈ closedBall y R) :
       x ∈ closedBall p (ρ/2) := by
   have hxy : dist x y ≤ R := by
     simpa [mem_closedBall, dist_comm] using hx
   have tri : dist x p ≤ dist x y + dist y p := dist_triangle _ _ _
   have : dist x p ≤ ρ/2 := by linarith
   simpa [mem_closedBall] using this
 have xpos_inner (x : E) (hx : dist y x < R) : 0 < F x := by
   have xb : x ∈ closedBall y R := by
     have : dist x y ≤ R := by rw [dist_comm]; linarith
     simpa [mem_closedBall] using this
   have xp := subball x xb
   have xD := ballρ2D xp
   have xn := Fn x xD
   have nz : F x ≠ 0 := by
     intro ze
     have xt : x ∈ T := by
       change x ∈ closedBall p (ρ/2) ∩ {x : E | F x = 0}
       exact ⟨xp, ze⟩
     have mm := hmin xt
     dsimp [g, R] at mm hx
     linarith
   exact lt_of_le_of_ne xn (Ne.symm nz)
 have Rsmall : A * R^2 ≤ 1 := by
   have : R^2 ≤ ρ^2 := by nlinarith
   exact le_trans (by nlinarith : A * R^2 ≤ A * ρ^2) smallρ
 have sqrw (x : E) : sqc y x = dist y x ^ 2 := by
   rw [sqc_norm]
   rw [dist_eq_norm]
   rw [norm_sub_rev]
 -- verify the annulus data for the touching-ball lemma.
 let l : ℝ := R^2 - R^2 / ((Module.finrank ℝ E : ℝ)+2)
 have N0 : 0 ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast (Nat.zero_le _)
 have N2 : 0 < (Module.finrank ℝ E : ℝ)+2 := by linarith
 have lpos : 0 < l := by
   dsimp [l]
   have r2 : 0 < R^2 := sq_pos_of_pos Rpos
   have fraclt : R^2 / ((Module.finrank ℝ E : ℝ)+2) < R^2 :=
      (div_lt_self r2 (by linarith))
   linarith
 have annsub (x : E) (hx : x ∈ annClosed y l R) :
       x ∈ closedBall y R := by
   have hsq := hx.2
   rw [sqrw] at hsq
   have : dist y x ≤ R := by
     have dd := dist_nonneg (x:=y) (y:=x)
     nlinarith
   simpa [mem_closedBall, dist_comm] using this
 have ac : ContinuousOn F (annClosed y l R) := by
   intro x hx
   have xb := subball x (annsub x hx)
   exact (Fc x (ballρ2D xb)).continuousWithinAt
 have an : ∀ x ∈ annClosed y l R, 0 ≤ F x := by
   intro x hx
   exact Fn x (ballρ2D (subball x (annsub x hx)))
 have ai : ∀ x, sqc y x = l → 0 < F x := by
   intro x hxl
   apply xpos_inner x
   have rr : dist y x ^ 2 = l := by simpa [sqrw] using hxl
   have nn := dist_nonneg (x:=y) (y:=x)
   have llt : l < R^2 := by
     dsimp [l]
     have : 0 < R^2 / ((Module.finrank ℝ E : ℝ)+2) := div_pos (sq_pos_of_pos Rpos) N2
     linarith
   nlinarith
 have ad : ∀ x ∈ annOpen y l R, ContDiffAt ℝ 2 F x := by
   intro x hx
   have xb : x ∈ annClosed y l R := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
   exact Fd x (ballρ2D (subball x (annsub x xb)))
 have al : ∀ x ∈ annOpen y l R, Laplacian.laplacian F x ≤ A * F x := by
   intro x hx
   have xb : x ∈ annClosed y l R := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
   exact Fi x (ballρ2D (subball x (annsub x xb)))
 have wD : w ∈ D := ballρ2D hwB
 have wm : IsLocalMin F w := by
   have ev : ∀ᶠ x in 𝓝 w, F w ≤ F x := by
     filter_upwards [ho.mem_nhds wD] with x hx
     rw [hwz]
     exact Fn x hx
   exact ev
 have wd : DifferentiableAt ℝ F w := (Fd w wD).differentiableAt (by norm_num : (2:WithTop ℕ∞) ≠ 0)
 have wsq : sqc y w = R^2 := by simp [sqrw, R]
 have contra := annulus_touch_strong y w R A Rpos hA Rsmall wsq
     (by simpa [l] using ac)
     (by simpa [l] using an)
     (by simpa [l] using ai)
     (by simpa [l] using ad)
     (by simpa [l] using al) wm wd hwz
 exact contra.elim

/-- Strong minimum principle on a preconnected open domain. -/
lemma positive_everywhere_of_somewhere
 {D : Set E} (ho : IsOpen D) (hc : IsPreconnected D)
 {F : E → ℝ} {A : ℝ} (hA : 0 < A)
 (Fc : ∀ x ∈ D, ContinuousAt F x)
 (Fn : ∀ x ∈ D, 0 ≤ F x)
 (Fd : ∀ x ∈ D, ContDiffAt ℝ 2 F x)
 (Fi : ∀ x ∈ D, Laplacian.laplacian F x ≤ A * F x)
 {q : E} (qD : q ∈ D) (qp : 0 < F q) :
 ∀ x ∈ D, 0 < F x := by
 classical
 let U : Set E := D ∩ {x | 0 < F x}
 let Z : Set E := {x | x ∈ D ∧ F x = 0}
 have Uop : IsOpen U := by
   -- continuity is only needed at the points of `D`.
   rw [isOpen_iff_mem_nhds]
   intro x hx
   have xd := hx.1
   have xp := hx.2
   have ev : {y : E | 0 < F y} ∈ 𝓝 x :=
     (Fc x xd).preimage_mem_nhds (Ioi_mem_nhds xp)
   exact inter_mem (ho.mem_nhds xd) ev
 have Zop : IsOpen Z := by
   rw [isOpen_iff_mem_nhds]
   intro x hx
   obtain ⟨r,r0,hr⟩ := zero_near_of_nonnegative ho hA Fc Fn Fd Fi hx.1 hx.2
   have mem : ball x r ∩ D ∈ 𝓝 x := inter_mem
       (Metric.isOpen_ball.mem_nhds (by simpa using r0))
       (ho.mem_nhds hx.1)
   apply Filter.mem_of_superset mem
   intro y hy
   have ey := hr y hy.1
   exact ⟨hy.2, ey⟩
 -- separate the zero and positive parts
 have sub : D ⊆ U ∪ Z := by
   intro x xd
   have nx := Fn x xd
   rcases lt_or_eq_of_le nx with xp|xe
   · exact Or.inl ⟨xd, xp⟩
   · exact Or.inr ⟨xd, xe.symm⟩
 have dis : Disjoint U Z := by
   apply Set.disjoint_left.2
   intro x xu xz
   exact (ne_of_gt xu.2) xz.2
 have some : (D ∩ U).Nonempty := ⟨q,qD, qD, qp⟩
 have all := IsPreconnected.subset_left_of_subset_union Uop Zop dis sub some hc
 intro x xd
 exact (all xd).2
end SemilinearPoissonSupport

-- END INLINED FILE: Mathlib/Support/semilinear_poisson_radial_symmetry_0e8f4ce1bc/StrongDomain.lean

-- BEGIN INLINED FILE: Mathlib/Support/semilinear_poisson_radial_symmetry_0e8f4ce1bc/CapStrict.lean
open scoped Topology InnerProductSpace NNReal
open Filter Set Real Metric Topology
namespace SemilinearPoissonSupport
variable {n : ℕ}
/-- The strong step on one cap.  Once the weak inequality is known on the
whole cap, it is automatically strict. -/
lemma cap_positive_of_nonnegative
 (f : ℝ → ℝ) (u : EuclideanSpace ℝ (Fin n) → ℝ)
 (e : EuclideanSpace ℝ (Fin n)) (t : ℝ) (K : ℝ≥0)
 (he : ‖e‖ = (1:ℝ)) (ht : 0 < t) (ht1 : t < 1)
 (hf : LipschitzWith K f)
 (hu : ContDiffOn ℝ 2 u (closedBall (0:EuclideanSpace ℝ (Fin n)) 1))
 (upos : ∀ x ∈ ball (0:EuclideanSpace ℝ (Fin n)) 1, 0 < u x)
 (uzero : ∀ x ∈ sphere (0:EuclideanSpace ℝ (Fin n)) 1, u x = 0)
 (hpde : ∀ x ∈ ball (0:EuclideanSpace ℝ (Fin n)) 1,
             - Laplacian.laplacian u x = f (u x))
 (weak : ∀ x ∈ ball (0:EuclideanSpace ℝ (Fin n)) 1,
              t < inner ℝ x e → 0 ≤ u (refl e t x) - u x) :
 ∀ x ∈ ball (0:EuclideanSpace ℝ (Fin n)) 1,
              t < inner ℝ x e → 0 < u (refl e t x) - u x := by
 classical
 let D : Set (EuclideanSpace ℝ (Fin n)) := capOpen e t
 let F : EuclideanSpace ℝ (Fin n) → ℝ := fun x => u (refl e t x) - u x
 have Do : IsOpen D := capOpen_open e t
 have Dc : IsPreconnected D := by
   have lin : IsLinearMap ℝ (fun x : EuclideanSpace ℝ (Fin n) => inner ℝ x e) := by
     have eqn : (fun x : EuclideanSpace ℝ (Fin n) => inner ℝ x e) =
         (innerSL ℝ e : (EuclideanSpace ℝ (Fin n) → ℝ)) := by
           funext x; simp [real_inner_comm]
     rw [eqn]
     exact (innerSL ℝ e).toLinearMap.isLinear
   have cv : Convex ℝ D := by
     exact (convex_ball (0:EuclideanSpace ℝ (Fin n)) 1).inter
       (convex_halfSpace_gt lin t)
   exact cv.isPreconnected
 have reg (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ D) :
       ContDiffAt ℝ 2 F x := by
   have hr := refl_mem_ball e x t he ht hx.1 hx.2
   have ux := contDiffAt_ball_of_closed hu hx.1
   have ur := contDiffAt_ball_of_closed hu hr
   exact (ContDiffAt.comp x ur (contDiff_refl e t).contDiffAt).sub ux
 have con (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ D) :
       ContinuousAt F x := (reg x hx).continuousAt
 have non (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ D) : 0 ≤ F x := weak x hx.1 hx.2
 let A : ℝ := (K:ℝ) + 1
 have A0 : 0 < A := by have := K.coe_nonneg; dsimp [A]; exact add_pos_of_nonneg_of_pos this (by norm_num)
 have ieq (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ D) :
       Laplacian.laplacian F x ≤ A * F x := by
   have hr := refl_mem_ball e x t he ht hx.1 hx.2
   obtain ⟨c,hc,hce⟩ := lipschitz_secant hf (u (refl e t x)) (u x)
   have H := reflected_difference_eq f u e t x he hu hx.1 hr hpde
   have l : - Laplacian.laplacian F x = c * F x := by
     dsimp [F]
     rw [H, hce]
   have low' : -(K:ℝ) ≤ c := by
     have na : -|c| ≤ c := neg_abs_le c
     linarith
   have nx := non x hx
   dsimp [A]
   change Laplacian.laplacian F x ≤ ((K:ℝ)+1) * F x
   nlinarith
 -- find one positive point by approaching the spherical tip `e` from
 -- inside the cap.
 have tipnorm : ‖(e : EuclideanSpace ℝ (Fin n))‖ = (1:ℝ) := he
 have tipz : u e = 0 := uzero e (by simpa [mem_sphere] using he)
 have tipref_ball : refl e t e ∈ ball (0:EuclideanSpace ℝ (Fin n)) 1 := by
   -- its norm-squared is `(2t-1)^2 < 1`.
   apply (mem_ball_zero_iff).2
   have sq := refl_norm_sq e e t (inner_unit_of_norm he)
   have inn : inner ℝ e e = (1:ℝ) := inner_unit_of_norm he
   have n0 := norm_nonneg (refl e t e)
   have tt := norm_nonneg e
   -- rewrite with `‖e‖=1` in the formula
   rw [he] at sq
   nlinarith
 have tippos : 0 < F e := by
   dsimp [F]
   rw [tipz]
   simpa using (upos (refl e t e) tipref_ball)
 let C : Set (EuclideanSpace ℝ (Fin n)) := capClosed e t
 have ec : e ∈ C := by
   constructor
   · simpa [mem_closedBall] using (show ‖e‖ ≤ (1:ℝ) from le_of_eq he)
   · change t ≤ inner ℝ e e
     rw [inner_unit_of_norm he]; exact le_of_lt ht1
 have Fwithin : ContinuousWithinAt F C e := by
   have corefl : MapsTo (refl e t) C (closedBall (0:EuclideanSpace ℝ (Fin n)) 1) := by
     intro y hy
     exact refl_mem_closedBall' e y t he (le_of_lt ht) hy.1 hy.2
   have uce : ContinuousWithinAt u (closedBall (0:EuclideanSpace ℝ (Fin n)) 1)
          (refl e t e) := hu.continuousOn _ (Metric.ball_subset_closedBall tipref_ball)
   have recont : ContinuousWithinAt (fun y : EuclideanSpace ℝ (Fin n) => refl e t y) C e :=
      (refl_cont' e t).continuousAt.continuousWithinAt
   have one : ContinuousWithinAt (fun y : EuclideanSpace ℝ (Fin n) => u (refl e t y)) C e :=
      by
        simpa [Function.comp_def] using uce.comp recont corefl
   have two : ContinuousWithinAt u C e :=
      (hu.continuousOn _ ec.1).mono (by intro x hx; exact hx.1) -- continuousWithin at e? 
   exact one.sub two
 -- positivity is a relative neighbourhood of the tip.
 have ev : ∀ᶠ x in 𝓝[C] e, 0 < F x :=
   Fwithin (Ioi_mem_nhds tippos)
 obtain ⟨r, r0, hr⟩ : ∃ r : ℝ, 0 < r ∧ ball e r ∩ C ⊆ {x | 0 < F x} := by
   rcases (mem_nhdsWithin_iff_exists_mem_nhds_inter.mp ev) with ⟨ss,hs,hsub⟩
   rcases Metric.mem_nhds_iff.mp hs with ⟨r,r0,hr⟩
   refine ⟨r,r0, ?_⟩
   exact fun x hx => hsub ⟨hr hx.1, hx.2⟩
 -- select `s e` with `s<1` sufficiently close to `1`.
 let d : ℝ := min (r/2) ((1-t)/2)
 have d0 : 0 < d := by dsimp [d]; exact lt_min (by linarith) (by linarith)
 let s : ℝ := 1 - d/2
 have slt : s < 1 := by dsimp [s]; linarith
 have st : t < s := by
   have dle : d ≤ (1-t)/2 := min_le_right _ _
   dsimp [s]
   linarith
 let q : EuclideanSpace ℝ (Fin n) := s • e
 have qball : q ∈ ball (0:EuclideanSpace ℝ (Fin n)) 1 := by
   apply (mem_ball_zero_iff).2
   have s0 : 0 < s := lt_trans ht st
   dsimp [q]; rw [norm_smul, Real.norm_eq_abs, abs_of_pos s0, he]; nlinarith
 have qi : inner ℝ q e = s := by
   dsimp [q]; rw [real_inner_smul_left, real_inner_self_eq_norm_sq, he]; norm_num
 have qD : q ∈ D := ⟨qball, by simpa [qi] using st⟩
 have qclose : q ∈ ball e r := by
   have dsq : dist q e = |1-s| := by
     rw [dist_eq_norm]
     have eq : q - e = (s-1) • e := by dsimp [q]; module
     rw [eq, norm_smul, he, mul_one, Real.norm_eq_abs]
     rw [abs_sub_comm]
   rw [mem_ball, dsq, abs_of_pos (by linarith : 0 < 1-s)]
   have dle : d ≤ r/2 := min_le_left _ _
   dsimp [s]
   linarith
 have qpos : 0 < F q := hr ⟨qclose, (capOpen_subset e t qD)⟩
 have allpos := positive_everywhere_of_somewhere Do Dc A0 con non reg ieq qD qpos
 intro x hx hxt
 exact allpos x ⟨hx,hxt⟩
end SemilinearPoissonSupport

-- END INLINED FILE: Mathlib/Support/semilinear_poisson_radial_symmetry_0e8f4ce1bc/CapStrict.lean

-- BEGIN INLINED FILE: Mathlib/Support/semilinear_poisson_radial_symmetry_0e8f4ce1bc/CapCut.lean
open scoped Topology InnerProductSpace NNReal
open Filter Set Real Metric Topology
namespace SemilinearPoissonSupport
variable {n : ℕ}
/-- continuation thin-piece: a positive/nonnegative compact core and a
thin rim suffice for the weak cap inequality. -/
lemma cap_nonnegative_of_core
 (f : ℝ → ℝ) (u : EuclideanSpace ℝ (Fin n) → ℝ)
 (e : EuclideanSpace ℝ (Fin n)) (s B : ℝ) (K : ℝ≥0)
 (he : ‖e‖ = (1:ℝ)) (hs : 0 < s)
 (wide : B - s ≤ (1/((K:ℝ)+1))/2)
 (hf : LipschitzWith K f)
 (hu : ContDiffOn ℝ 2 u (closedBall (0:EuclideanSpace ℝ (Fin n)) 1))
 (upos : ∀ x ∈ ball (0:EuclideanSpace ℝ (Fin n)) 1, 0 < u x)
 (uzero : ∀ x ∈ sphere (0:EuclideanSpace ℝ (Fin n)) 1, u x = 0)
 (hpde : ∀ x ∈ ball (0:EuclideanSpace ℝ (Fin n)) 1,
             - Laplacian.laplacian u x = f (u x))
 (core : ∀ x ∈ closedBall (0:EuclideanSpace ℝ (Fin n)) 1,
                 B ≤ inner ℝ x e → 0 ≤ u (refl e s x) - u x) :
 ∀ x ∈ ball (0:EuclideanSpace ℝ (Fin n)) 1,
          s < inner ℝ x e → 0 ≤ u (refl e s x) - u x := by
 classical
 let D : Set (EuclideanSpace ℝ (Fin n)) :=
       {x | x ∈ ball (0:EuclideanSpace ℝ (Fin n)) 1 ∧ s < inner ℝ x e ∧ inner ℝ x e < B}
 let C : Set (EuclideanSpace ℝ (Fin n)) :=
       {x | x ∈ closedBall (0:EuclideanSpace ℝ (Fin n)) 1 ∧ s ≤ inner ℝ x e ∧ inner ℝ x e ≤ B}
 let F : EuclideanSpace ℝ (Fin n) → ℝ := fun x => u (refl e s x) - u x
 have op : IsOpen D := by
   have ic : Continuous (fun x : EuclideanSpace ℝ (Fin n) => inner ℝ x e) := by
     have eqn : (fun x : EuclideanSpace ℝ (Fin n) => inner ℝ x e) =
       (innerSL ℝ e : (EuclideanSpace ℝ (Fin n) → ℝ)) := by funext y;simp [real_inner_comm]
     rw [eqn]; fun_prop
   exact Metric.isOpen_ball.inter ((isOpen_lt continuous_const ic).inter
        (isOpen_lt ic continuous_const))
 have cp : IsCompact C := by
   have ic : Continuous (fun x : EuclideanSpace ℝ (Fin n) => inner ℝ x e) := by
     have eqn : (fun x : EuclideanSpace ℝ (Fin n) => inner ℝ x e) =
       (innerSL ℝ e : (EuclideanSpace ℝ (Fin n) → ℝ)) := by funext y;simp [real_inner_comm]
     rw [eqn]; fun_prop
   exact (ProperSpace.isCompact_closedBall (0:EuclideanSpace ℝ (Fin n)) 1).inter_right
     ((isClosed_le continuous_const ic).inter (isClosed_le ic continuous_const))
 have sub : D ⊆ C := by
   intro x hx
   exact ⟨Metric.ball_subset_closedBall hx.1, le_of_lt hx.2.1, le_of_lt hx.2.2⟩
 have slab : ∀ x ∈ C, 0 ≤ inner ℝ x e - s ∧ inner ℝ x e - s ≤ (1/((K:ℝ)+1))/2 := by
   intro x hx
   constructor
   · linarith [hx.2.1]
   · linarith [hx.2.2, wide]
 have fc : ContinuousOn F C := by
   intro x hx
   have ux := hu.continuousOn _ hx.1
   have urmem := refl_mem_closedBall' e x s he (le_of_lt hs) hx.1 hx.2.1
   have ur := hu.continuousOn _ urmem
   have hcomp : ContinuousWithinAt (fun y : EuclideanSpace ℝ (Fin n) => u (refl e s y)) C x := by
     simpa [Function.comp_def] using
       ur.comp ( (refl_cont' e s).continuousAt.continuousWithinAt )
        (by intro y hy; exact refl_mem_closedBall' e y s he (le_of_lt hs) hy.1 hy.2.1)
   exact hcomp.sub (ux.mono (by intro y hy; exact hy.1))
 have fd : ∀ x ∈ D, ContDiffAt ℝ 2 F x := by
   intro x hx
   have rr := refl_mem_ball e x s he hs hx.1 hx.2.1
   exact (ContDiffAt.comp x (contDiffAt_ball_of_closed hu rr)
        (contDiff_refl e s).contDiffAt).sub (contDiffAt_ball_of_closed hu hx.1)
 have feq : ∀ x ∈ D, ∃ c : ℝ, |c| ≤ (K:ℝ) ∧
       - Laplacian.laplacian F x = c * F x := by
   intro x hx
   have rr := refl_mem_ball e x s he hs hx.1 hx.2.1
   obtain ⟨c,hc,eq⟩ := lipschitz_secant hf (u (refl e s x)) (u x)
   refine ⟨c,hc,?_⟩
   dsimp [F]
   rw [reflected_difference_eq f u e s x he hu hx.1 rr hpde, eq]
 have bd : ∀ x ∈ C \ D, 0 ≤ F x := by
   intro x hx
   by_cases top : B ≤ inner ℝ x e
   · exact core x hx.1.1 top
   · have bot : inner ℝ x e = s ∨ x ∈ sphere (0:EuclideanSpace ℝ (Fin n)) 1 := by
       have notin := hx.2
       by_cases eqs : inner ℝ x e = s
       · exact Or.inl eqs
       right
       have : ¬ x ∈ ball (0:EuclideanSpace ℝ (Fin n)) 1 := by
         intro xb
         exact notin ⟨xb, lt_of_le_of_ne hx.1.2.1 (Ne.symm eqs),
             lt_of_le_of_ne (le_of_not_ge top) (by intro h; exact notin ⟨xb, lt_of_le_of_ne hx.1.2.1 (Ne.symm eqs), by linarith⟩)⟩
       have cb := (mem_closedBall_zero_iff).1 hx.1.1
       have nb := not_lt.mp (by simpa [mem_ball_zero_iff] using this)
       have normeq : ‖x‖ = (1:ℝ) := le_antisymm cb nb
       simpa [mem_sphere] using normeq
     rcases bot with eqs|sph
     · have same : refl e s x = x := by
         dsimp [refl]
         rw [eqs]
         simp
       simp [F, same]
     · have out : x ∈ capClosed e s \ capOpen e s := by
         constructor
         · exact ⟨hx.1.1, hx.1.2.1⟩
         · intro hxo
           have hlt : ‖x‖ < (1:ℝ) := (mem_ball_zero_iff).1 hxo.1
           have heq : ‖x‖ = (1:ℝ) := by simpa [mem_sphere] using sph
           linarith
       exact reflected_boundary_nonneg u e s he hs upos uzero x out
 have all := nonneg_on_thin e (inner_unit_of_norm he) (K:ℝ) s
       (by exact_mod_cast K.coe_nonneg) sub op cp slab fc bd fd feq
 intro x xb xi
 by_cases hi : B ≤ inner ℝ x e
 · exact core x (Metric.ball_subset_closedBall xb) hi
 · exact all x ⟨xb, xi, lt_of_not_ge hi⟩
end SemilinearPoissonSupport

-- END INLINED FILE: Mathlib/Support/semilinear_poisson_radial_symmetry_0e8f4ce1bc/CapCut.lean

-- BEGIN INLINED FILE: Mathlib/Support/semilinear_poisson_radial_symmetry_0e8f4ce1bc/Sliding.lean
open scoped Topology InnerProductSpace NNReal
open Filter Set Real Metric Topology
namespace SemilinearPoissonSupport
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

def GoodCap (u : EuclideanSpace ℝ (Fin n) → ℝ)
 (e : EuclideanSpace ℝ (Fin n)) (s : ℝ) : Prop :=
  ∀ x ∈ ball (0:EuclideanSpace ℝ (Fin n)) 1,
    s < inner ℝ x e → 0 ≤ u (refl e s x) - u x

lemma dist_refl_parameter {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
 (e x : E') (a b : ℝ) (he : ‖e‖ = (1:ℝ)) :
 dist (refl e a x) (refl e b x) = 2 * |a-b| := by
 rw [dist_eq_norm]
 have hh : refl e a x - refl e b x = (2*(a-b)) • e := by
   dsimp [refl]
   module
 rw [hh, norm_smul, he, mul_one, Real.norm_eq_abs, abs_mul]
 norm_num
lemma cont_refl_parameter {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
 (e x : E') : Continuous (fun s : ℝ => refl e s x) := by
 dsimp [refl]
 fun_prop

/-- Strict positivity on the outer compact core at a good plane.  The
spherical points are strict as well: their reflected points are inside. -/
lemma core_strict_at_good
 (f : ℝ → ℝ) (u : E → ℝ) (e : E) (s B : ℝ) (K : ℝ≥0)
 (he : ‖e‖ = (1:ℝ)) (s0 : 0 < s) (s1 : s < 1) (Bs : s < B) (B1 : B < 1)
 (hf : LipschitzWith K f)
 (hu : ContDiffOn ℝ 2 u (closedBall (0:E) 1))
 (upos : ∀ x ∈ ball (0:E) 1, 0 < u x)
 (uzero : ∀ x ∈ sphere (0:E) 1, u x = 0)
 (hpde : ∀ x ∈ ball (0:E) 1, -Laplacian.laplacian u x = f (u x))
 (good : GoodCap u e s) :
 ∀ x ∈ ({x : E | x ∈ closedBall (0:E) 1 ∧ B ≤ inner ℝ x e} : Set E),
    0 < u (refl e s x) - u x := by
 classical
 have strict := cap_positive_of_nonnegative f u e s K he s0 s1 hf hu upos uzero hpde good
 intro x hx
 by_cases xb : x ∈ ball (0:E) 1
 · exact strict x xb (lt_of_lt_of_le Bs hx.2)
 · have normle := (mem_closedBall_zero_iff).1 hx.1
   have normge : (1:ℝ) ≤ ‖x‖ := not_lt.mp (by simpa [mem_ball_zero_iff] using xb)
   have norme : ‖x‖ = (1:ℝ) := le_antisymm normle normge
   have sph : x ∈ sphere (0:E) 1 := by simpa [mem_sphere] using norme
   have rb : refl e s x ∈ ball (0:E) 1 := by
     apply (mem_ball_zero_iff).2
     have sq := refl_norm_sq e x s (inner_unit_of_norm he)
     rw [norme] at sq
     have rr := norm_nonneg (refl e s x)
     have inn : s < inner ℝ x e := lt_of_lt_of_le Bs hx.2
     nlinarith
   have zz := uzero x sph
   rw [zz]
   linarith [upos (refl e s x) rb]

/-- A good plane has a whole interval of nearby good positions.
The compact core is protected by strict positivity, and the thin complement
is `cap_nonnegative_of_core`. -/
lemma good_open_near
 (f : ℝ → ℝ) (u : E → ℝ) (e : E) (K : ℝ≥0)
 (he : ‖e‖ = (1:ℝ))
 (hf : LipschitzWith K f)
 (hu : ContDiffOn ℝ 2 u (closedBall (0:E) 1))
 (upos : ∀ x ∈ ball (0:E) 1, 0 < u x)
 (uzero : ∀ x ∈ sphere (0:E) 1, u x = 0)
 (hpde : ∀ x ∈ ball (0:E) 1, -Laplacian.laplacian u x = f (u x))
 {s : ℝ} (s0 : 0 < s) (s1 : s < 1) (good : GoodCap u e s) :
 ∃ ε : ℝ, 0 < ε ∧
   ∀ r : ℝ, |r-s| < ε → 0 < r → r < 1 → GoodCap u e r := by
 classical
 let w : ℝ := (1 / ((K:ℝ)+1))/2
 have kp : 0 < (K:ℝ)+1 := by have := K.coe_nonneg; linarith
 have w0 : 0 < w := by dsimp [w]; positivity
 let d : ℝ := min ((1-s)/2) (w/2)
 have d0 : 0 < d := by dsimp [d]; exact lt_min (by linarith) (by linarith)
 have dlew : d ≤ w/2 := min_le_right _ _
 have dle1 : d ≤ (1-s)/2 := min_le_left _ _
 let B : ℝ := s + d
 have Bs : s < B := by dsimp [B]; linarith
 have B1 : B < 1 := by dsimp [B]; linarith
 let Core : Set E := {x : E | x ∈ closedBall (0:E) 1 ∧ B ≤ inner ℝ x e}
 have ic : Continuous (fun x : E => inner ℝ x e) := by
   have eqn : (fun x : E => inner ℝ x e) = (innerSL ℝ e : E → ℝ) := by
     funext y; simp [real_inner_comm]
   rw [eqn]; fun_prop
 have ccomp : IsCompact Core :=
   (ProperSpace.isCompact_closedBall (0:E) 1).inter_right (isClosed_le continuous_const ic)
 have ene : e ∈ Core := by
   constructor
   · apply (mem_closedBall_zero_iff).2
     linarith
   · have ii := inner_unit_of_norm he
     rw [ii]
     exact le_of_lt B1
 have cne : Core.Nonempty := ⟨e, ene⟩
 let F : E → ℝ := fun x => u (refl e s x) - u x
 have fc : ContinuousOn F Core := by
   intro x hx
   have ux := hu.continuousOn x hx.1
   have rr := refl_mem_closedBall' e x s he (le_of_lt s0) hx.1
      (le_trans (le_of_lt Bs) hx.2)
   have ur := hu.continuousOn (refl e s x) rr
   have comp : ContinuousWithinAt (fun y : E => u (refl e s y)) Core x := by
     have maps : MapsTo (refl e s) Core (closedBall (0:E) 1) := by
       intro y hy
       exact refl_mem_closedBall' e y s he (le_of_lt s0) hy.1
         (le_trans (le_of_lt Bs) hy.2)
     simpa [Function.comp_def] using
       ur.comp ( (refl_cont' e s).continuousAt.continuousWithinAt ) maps
   exact comp.sub (ux.mono (by intro y hy; exact hy.1))
 obtain ⟨p,hpc,hmin⟩ := ccomp.exists_isMinOn cne fc
 have ppos0 := core_strict_at_good f u e s B K he s0 s1 Bs B1 hf hu upos uzero hpde good p hpc
 let m : ℝ := F p
 have mpos : 0 < m := ppos0
 have geF : ∀ x ∈ Core, m ≤ F x := hmin
 have uni : UniformContinuousOn u (closedBall (0:E) 1) :=
   (ProperSpace.isCompact_closedBall (0:E) 1).uniformContinuousOn_of_continuous hu.continuousOn
 obtain ⟨δ, δ0, hδ⟩ := (Metric.uniformContinuousOn_iff.mp uni) m mpos
 let eps : ℝ := min (δ/4) (min (d/2) (w/4))
 have eps0 : 0 < eps := by
   dsimp [eps]
   exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
 refine ⟨eps, eps0, ?_⟩
 intro r hr r0 r1
 have hrδ : |r-s| < δ/4 := lt_of_lt_of_le hr (min_le_left _ _)
 have hrd : |r-s| < d/2 :=
   lt_of_lt_of_le hr (le_trans (min_le_right _ _) (min_le_left _ _))
 have hrw : |r-s| < w/4 :=
   lt_of_lt_of_le hr (le_trans (min_le_right _ _) (min_le_right _ _))
 have rB : r < B := by
   have : r - s ≤ |r-s| := le_abs_self _
   dsimp [B]
   linarith
 have wide : B - r ≤ (1 / ((K:ℝ)+1))/2 := by
   change B - r ≤ w
   have hsrr : s - r ≤ |r-s| := by
     rw [abs_sub_comm]
     exact le_abs_self _
   dsimp [B]
   linarith
 have coreR : ∀ x ∈ closedBall (0:E) 1, B ≤ inner ℝ x e →
       0 ≤ u (refl e r x) - u x := by
   intro x xb xi
   have xc : x ∈ Core := ⟨xb, xi⟩
   have rs : refl e s x ∈ closedBall (0:E) 1 :=
     refl_mem_closedBall' e x s he (le_of_lt s0) xb (le_trans (le_of_lt Bs) xi)
   have rr : refl e r x ∈ closedBall (0:E) 1 :=
     refl_mem_closedBall' e x r he (le_of_lt r0) xb (le_trans (le_of_lt rB) xi)
   have dd : dist (refl e r x) (refl e s x) < δ := by
     rw [dist_refl_parameter e x r s he]
     linarith
   have ud := hδ (refl e r x) rr (refl e s x) rs dd
   rw [Real.dist_eq] at ud
   dsimp [m, F] at ud ⊢
   have lower := geF x xc
   dsimp [m, F] at lower
   have one : -(u (refl e s x) - u (refl e s p) + (u p - u x)) ≤ (0:ℝ) := by
     linarith
   -- simply use absolute distance and the minimum
   have dif : -m < u (refl e r x) - u (refl e s x) := by
     dsimp [m, F]
     have ab := (neg_lt_of_abs_lt ud)
     simpa using ab
   -- `F_s x ≥ m`
   change 0 ≤ u (refl e r x) - u x
   nlinarith
 exact cap_nonnegative_of_core f u e r B K he r0 wide hf hu upos uzero hpde coreR

/-- The bad set of positions is open: a negative value at one point
survives a small change of the parameter. -/
lemma bad_open
 (u : E → ℝ) (e : E)
 (he : ‖e‖ = (1:ℝ))
 (hu : ContDiffOn ℝ 2 u (closedBall (0:E) 1)) :
 IsOpen {s : ℝ | 0 < s ∧ s < 1 ∧ ¬ GoodCap u e s} := by
 classical
 rw [isOpen_iff_mem_nhds]
 intro s hs
 obtain ⟨s0,s1,ng⟩ := hs
 unfold GoodCap at ng
 push_neg at ng
 obtain ⟨x, xb, xi, xn⟩ := ng
 have rsb : refl e s x ∈ ball (0:E) 1 := refl_mem_ball e x s he s0 xb xi
 have cu : ContinuousAt u (refl e s x) :=
   (contDiffAt_ball_of_closed hu rsb).continuousAt
 have cpar : ContinuousAt (fun r : ℝ => u (refl e r x) - u x) s := by
   have one : ContinuousAt (fun r : ℝ => u (refl e r x)) s := by
     simpa [Function.comp_def] using (ContinuousAt.comp_of_eq (x:=s) cu (cont_refl_parameter e x).continuousAt rfl)
   exact one.sub continuousAt_const
 have evn : {r : ℝ | u (refl e r x) - u x < 0} ∈ 𝓝 s :=
   cpar.preimage_mem_nhds (Iio_mem_nhds xn)
 have ev0 : {r : ℝ | 0 < r} ∈ 𝓝 s := Ioi_mem_nhds s0
 have ev1 : {r : ℝ | r < 1} ∈ 𝓝 s := Iio_mem_nhds s1
 have evi : {r : ℝ | r < inner ℝ x e} ∈ 𝓝 s := Iio_mem_nhds xi
 filter_upwards [evn, ev0, ev1, evi] with r rn rzero rone ri
 refine ⟨rzero, rone, ?_⟩
 unfold GoodCap
 push_neg
 exact ⟨x, xb, ri, rn⟩

lemma good_set_open
 (f : ℝ → ℝ) (u : E → ℝ) (e : E) (K : ℝ≥0)
 (he : ‖e‖ = (1:ℝ)) (hf : LipschitzWith K f)
 (hu : ContDiffOn ℝ 2 u (closedBall (0:E) 1))
 (upos : ∀ x ∈ ball (0:E) 1, 0 < u x)
 (uzero : ∀ x ∈ sphere (0:E) 1, u x = 0)
 (hpde : ∀ x ∈ ball (0:E) 1, -Laplacian.laplacian u x = f (u x)) :
 IsOpen {s : ℝ | 0 < s ∧ s < 1 ∧ GoodCap u e s} := by
 classical
 rw [isOpen_iff_mem_nhds]
 intro s hs
 obtain ⟨s0,s1,sg⟩ := hs
 obtain ⟨ε, ε0, hε⟩ := good_open_near f u e K he hf hu upos uzero hpde s0 s1 sg
 let R : ℝ := min ε (min (s/2) ((1-s)/2))
 have R0 : 0 < R := by
   dsimp [R]; exact lt_min ε0 (lt_min (by linarith) (by linarith))
 apply Filter.mem_of_superset (Metric.ball_mem_nhds s R0)
 intro r hr
 have dr : |r-s| < R := by simpa [Real.dist_eq] using hr
 have de : |r-s| < ε := lt_of_lt_of_le dr (min_le_left _ _)
 have ds' : |r-s| < s/2 :=
   lt_of_lt_of_le dr (le_trans (min_le_right _ _) (min_le_left _ _))
 have d1 : |r-s| < (1-s)/2 :=
   lt_of_lt_of_le dr (le_trans (min_le_right _ _) (min_le_right _ _))
 have leabs : s-r ≤ |r-s| := by rw [abs_sub_comm]; exact le_abs_self _
 have leabs' : r-s ≤ |r-s| := le_abs_self _
 have r0 : 0 < r := by linarith
 have r1 : r < 1 := by linarith
 exact ⟨r0, r1, hε r de r0 r1⟩

/-- Sliding a plane all the way: good and bad positions are two disjoint
open pieces of `(0,1)`. -/
lemma sliding_cap_nonnegative
 (f : ℝ → ℝ) (u : E → ℝ) (e : E) (K : ℝ≥0)
 (he : ‖e‖ = (1:ℝ)) (hf : LipschitzWith K f)
 (hu : ContDiffOn ℝ 2 u (closedBall (0:E) 1))
 (upos : ∀ x ∈ ball (0:E) 1, 0 < u x)
 (uzero : ∀ x ∈ sphere (0:E) 1, u x = 0)
 (hpde : ∀ x ∈ ball (0:E) 1, -Laplacian.laplacian u x = f (u x)) :
 ∀ s : ℝ, 0 < s → s < 1 → GoodCap u e s := by
 classical
 let G : Set ℝ := {s : ℝ | 0 < s ∧ s < 1 ∧ GoodCap u e s}
 let V : Set ℝ := {s : ℝ | 0 < s ∧ s < 1 ∧ ¬ GoodCap u e s}
 have go : IsOpen G := good_set_open f u e K he hf hu upos uzero hpde
 have vo : IsOpen V := bad_open u e he hu
 have dis : Disjoint G V := by
   apply Set.disjoint_left.2
   intro x hx hy
   exact hy.2.2 hx.2.2
 have sub : Set.Ioo (0:ℝ) 1 ⊆ G ∪ V := by
   intro x hx
   by_cases gg : GoodCap u e x
   · left; exact ⟨hx.1, hx.2, gg⟩
   · right; exact ⟨hx.1, hx.2, gg⟩
 have some : (Set.Ioo (0:ℝ) 1 ∩ G).Nonempty := by
   have kp : 0 < (K:ℝ)+1 := by have := K.coe_nonneg; linarith
   let w : ℝ := (1 / ((K:ℝ)+1))/2
   have w0 : 0 < w := by dsimp [w]; positivity
   let a : ℝ := min (w/2) (1/2:ℝ)
   have a0 : 0 < a := by dsimp [a]; exact lt_min (by linarith) (by norm_num)
   have ale : a ≤ w/2 := min_le_left _ _
   have aone : a ≤ (1/2:ℝ) := min_le_right _ _
   let s : ℝ := 1 - a
   have s0 : 0 < s := by dsimp [s]; linarith
   have s1 : s < 1 := by dsimp [s]; linarith
   have wid : 1 - s ≤ (1 / ((K:ℝ)+1))/2 := by change 1-s ≤ w; dsimp [s]; linarith
   have initial : GoodCap u e s := by
     intro x xb xi
     exact narrow_cap_nonnegative f u e s K he s0 wid hf hu upos uzero hpde x xb xi
   refine ⟨s, ⟨s0,s1⟩, ?_⟩
   exact ⟨s0,s1,initial⟩
 have all := IsPreconnected.subset_left_of_subset_union go vo dis sub some
      (isPreconnected_Ioo : IsPreconnected (Set.Ioo (0:ℝ) 1))
 intro s s0 s1
 exact (all ⟨s0,s1⟩).2.2
end SemilinearPoissonSupport

-- END INLINED FILE: Mathlib/Support/semilinear_poisson_radial_symmetry_0e8f4ce1bc/Sliding.lean

namespace Submission

-- BEGIN INLINED FILE: Main.lean

namespace LeanEval
namespace Analysis
namespace PDE

/-!
# Radial symmetry for a semilinear Poisson equation

Suppose `u` is a positive solution to a semilinear Poisson PDE:

  `-Δ u = f(u)` in the open unit ball,
  `u = 0` on the boundary.

For Lipschitz `f`, every `C^2` solution on the closed ball is radial and
strictly decreasing as a function of the radius.
-/

open Metric
open scoped NNReal

/-- `u` solved a semilinear Poisson problem if `-Δ u = f(u)` in the open unit
ball and `u = 0` on the unit sphere. -/
def SolvesSemilinearPoisson {n : ℕ} (f : ℝ → ℝ) (u : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  (∀ x ∈ ball 0 1, -Laplacian.laplacian u x = f (u x)) ∧ ∀ x ∈ sphere 0 1, u x = 0



end PDE
end Analysis
end LeanEval

open LeanEval.Analysis.PDE
open Metric
open scoped NNReal
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem semilinear_poisson_radial_symmetry {n : ℕ} (hn : 0 < n)
    {f : ℝ → ℝ} (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_lipschitz : ∃ K : ℝ≥0, LipschitzWith K f)
    (hu_c2 : ContDiffOn ℝ 2 u (closedBall 0 1))
    (hu_solve : SolvesSemilinearPoisson f u)
    (hu_positive : ∀ x ∈ ball 0 1, 0 < u x) :
    ∃ v : ℝ → ℝ≥0,
      StrictAntiOn v (Set.Icc (0 : ℝ) 1) ∧
        ∀ x ∈ closedBall 0 1, u x = v ‖x‖ :=
/-ResultProofBegin-/by
  classical
  have hzero : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) 1, u x = 0 :=
    hu_solve.2
  have hnon : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
      0 ≤ u x :=
    SemilinearPoissonSupport.nonneg_closedBall hu_positive hzero

  have hcont : ∀ p ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1,
        ContinuousAt u p := by
    intro p hp
    apply hu_c2.continuousOn.continuousAt
    apply Filter.mem_of_superset (IsOpen.mem_nhds Metric.isOpen_ball hp)
    exact Metric.ball_subset_closedBall

  /- This is the analytic part of moving planes.  Notice the bounds `0<t<1`:
  caps with `t≥1` are empty.  Symmetry at the limiting plane is *not* an
  additional hypothesis below; Lemma `plane0_of_cap` obtains it from this
  strict cap inequality using continuity. -/
  have hcap_small :
      ∀ e : EuclideanSpace ℝ (Fin n), ‖e‖ = (1:ℝ) →
        ∀ t : ℝ, 0 < t → t < 1 →
        ∀ z ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1,
           t < inner ℝ z e →
           u z < u (SemilinearPoissonSupport.refl e t z) := by
    intro e he t ht ht_one z hz hze
    -- The reflected point is not an extra domain assumption.  A positive
    -- plane lowers the norm on its cap.
    have href_mem :
        SemilinearPoissonSupport.refl e t z ∈
          ball (0 : EuclideanSpace ℝ (Fin n)) 1 :=
      SemilinearPoissonSupport.refl_mem_ball e z t he ht hz hze
    have href_pos : 0 < u (SemilinearPoissonSupport.refl e t z) :=
      hu_positive _ href_mem
    have hz_pos : 0 < u z := hu_positive _ hz
    obtain ⟨K, hK⟩ := hf_lipschitz
    obtain ⟨c, hcK, hc⟩ :=
      SemilinearPoissonSupport.lipschitz_secant hK
        (u (SemilinearPoissonSupport.refl e t z)) (u z)
    have hz_pde := hu_solve.1 z hz
    have href_pde := hu_solve.1 _ href_mem
    -- The PDE does pass to the reflected difference: reflection is an affine
    -- isometry, hence commutes with the trace of the Hessian. This used to
    -- be implicit in the moving-planes setup; spelling it out removes a
    -- genuine analytic premise from the remaining maximum principle.
    have hdiff :
        - Laplacian.laplacian
          (fun y : EuclideanSpace ℝ (Fin n) =>
            u (SemilinearPoissonSupport.refl e t y) - u y) z =
          f (u (SemilinearPoissonSupport.refl e t z)) - f (u z) :=
      SemilinearPoissonSupport.reflected_difference_eq
        f u e t z he hu_c2 hz href_mem hu_solve.1
    have hlin :
        - Laplacian.laplacian
          (fun y : EuclideanSpace ℝ (Fin n) =>
            u (SemilinearPoissonSupport.refl e t y) - u y) z =
          c * (u (SemilinearPoissonSupport.refl e t z) - u z) := by
      rw [hdiff, hc]
    have hux : ContDiffAt ℝ 2 u z :=
      SemilinearPoissonSupport.contDiffAt_ball_of_closed hu_c2 hz
    have hur : ContDiffAt ℝ 2 u
        (SemilinearPoissonSupport.refl e t z) :=
      SemilinearPoissonSupport.contDiffAt_ball_of_closed hu_c2 href_mem
    have hw : ContDiffAt ℝ 2
        (fun y : EuclideanSpace ℝ (Fin n) =>
          u (SemilinearPoissonSupport.refl e t y) - u y) z := by
      have hR : ContDiffAt ℝ 2
          (fun y : EuclideanSpace ℝ (Fin n) =>
            u (SemilinearPoissonSupport.refl e t y)) z :=
        ContDiffAt.comp z hur
          (SemilinearPoissonSupport.contDiff_refl e t).contDiffAt
      exact hR.sub hux
    -- The remaining step is the weak/strong maximum principle on the cap;
    -- `hlin` is now an honest pointwise C² linear elliptic equation with the
    -- coefficient bound `hcK`.
    -- The elementary maximum principle now gives a completely usable
    -- starting interval for the plane.  Unlike a formal pointwise
    -- assumption, the same bound works simultaneously at every point of
    -- the cap; it is this uniformity (through the Lipschitz constant K)
    -- that one needs for the usual sliding argument.
    have hweak_cap
        (hh : 1 - t ≤ (1 / ((K:ℝ)+1))/2) :
        ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1,
          t < inner ℝ y e → u y ≤ u (SemilinearPoissonSupport.refl e t y) := by
      intro y hy hyt
      have H := SemilinearPoissonSupport.narrow_cap_nonnegative
        f u e t K he ht hh hK hu_c2 hu_positive hzero hu_solve.1
        y hy hyt
      linarith
    have hweak_of_width
        (hh : 1 - t ≤ (1 / ((K:ℝ)+1))/2) :
        u z ≤ u (SemilinearPoissonSupport.refl e t z) :=
      hweak_cap hh z hz hze

    -- A convenient zeroth-order version, used by the strong minimum/annulus
    -- argument.  Once the weak order on the whole cap is known, the
    -- reflected difference satisfies `ΔF ≤ (K+1)F`; the strict positivity
    -- problem is thus exactly the usual strong minimum principle for an
    -- operator with *positive* massive term.  This normalization avoids any
    -- sign assumptions on the Lipschitz secant.
    have hmass
        (hF : 0 ≤ u (SemilinearPoissonSupport.refl e t z) - u z) :
        Laplacian.laplacian
          (fun y : EuclideanSpace ℝ (Fin n) =>
            u (SemilinearPoissonSupport.refl e t y) - u y) z ≤
          ((K:ℝ)+1) *
            (u (SemilinearPoissonSupport.refl e t z) - u z) := by
      have cup : -(K:ℝ) ≤ c := by
        have H : - |c| ≤ c := neg_abs_le c
        linarith [hcK]
      have cf : -(c * (u (SemilinearPoissonSupport.refl e t z) - u z)) =
          Laplacian.laplacian
            (fun y : EuclideanSpace ℝ (Fin n) =>
              u (SemilinearPoissonSupport.refl e t y) - u y) z := by
        linarith [hlin]
      rw [← cf]
      have kk : 0 ≤ (K:ℝ) := by exact_mod_cast K.coe_nonneg
      nlinarith
    -- Tangential part of the strong principle is independent of the unknown
    -- secant; only ΔF ≤ A F is used.  The annulus lemma includes the compact
    -- inner-rim bound, so this remaining goal is now purely the sliding/
    -- domain step (producing such an annulus or the thin complement).
    have htangent
        (a p : EuclideanSpace ℝ (Fin n))
        (R A : ℝ) (R0 : 0 < R) (A0 : 0 < A) (small : A*R^2 ≤ 1)
        (outer : SemilinearPoissonSupport.sqc a p = R^2)
        (C0 : ContinuousOn
          (fun y : EuclideanSpace ℝ (Fin n) =>
             u (SemilinearPoissonSupport.refl e t y) - u y)
          (SemilinearPoissonSupport.annClosed a
            (R^2-R^2/((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)):ℝ)+2)) R))
        (N0 : ∀ x ∈ SemilinearPoissonSupport.annClosed a
            (R^2-R^2/((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)):ℝ)+2)) R,
            0 ≤ u (SemilinearPoissonSupport.refl e t x) - u x)
        (I0 : ∀ x, SemilinearPoissonSupport.sqc a x =
            R^2-R^2/((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)):ℝ)+2) →
            0 < u (SemilinearPoissonSupport.refl e t x) - u x)
        (D0 : ∀ x ∈ SemilinearPoissonSupport.annOpen a
            (R^2-R^2/((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)):ℝ)+2)) R,
          ContDiffAt ℝ 2
           (fun y : EuclideanSpace ℝ (Fin n) => u (SemilinearPoissonSupport.refl e t y)-u y) x)
        (L0 : ∀ x ∈ SemilinearPoissonSupport.annOpen a
            (R^2-R^2/((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)):ℝ)+2)) R,
          Laplacian.laplacian
            (fun y : EuclideanSpace ℝ (Fin n) => u (SemilinearPoissonSupport.refl e t y)-u y) x ≤
            A * (u (SemilinearPoissonSupport.refl e t x)-u x))
        (m0 : IsLocalMin
           (fun y : EuclideanSpace ℝ (Fin n) => u (SemilinearPoissonSupport.refl e t y)-u y) p)
        (d0 : DifferentiableAt ℝ
           (fun y : EuclideanSpace ℝ (Fin n) => u (SemilinearPoissonSupport.refl e t y)-u y) p)
        (z0 : u (SemilinearPoissonSupport.refl e t p)-u p = 0) : False := by
      exact SemilinearPoissonSupport.annulus_touch_strong a p R A R0 A0 small
        outer C0 N0 I0 D0 L0 m0 d0 z0
    by_cases width : 1 - t ≤ (1 / ((K:ℝ)+1))/2
    · have H := SemilinearPoissonSupport.cap_positive_of_nonnegative
          f u e t K he ht ht_one hK hu_c2 hu_positive hzero hu_solve.1
          (by
            intro x hx hxt
            have := hweak_cap width x hx hxt
            linarith)
      have H' := H z hz hze
      linarith
    · have hweak_slide :
          ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1,
            t < inner ℝ y e →
              0 ≤ u (SemilinearPoissonSupport.refl e t y) - u y := by
            intro y hy hiy
            exact SemilinearPoissonSupport.sliding_cap_nonnegative
              f u e K he hK hu_c2 hu_positive hzero hu_solve.1
                t ht ht_one y hy hiy
      have H := SemilinearPoissonSupport.cap_positive_of_nonnegative
          f u e t K he ht ht_one hK hu_c2 hu_positive hzero hu_solve.1 hweak_slide
      have H' := H z hz hze
      linarith

  have hcap :
      ∀ e : EuclideanSpace ℝ (Fin n), ‖e‖ = (1:ℝ) →
        ∀ t : ℝ, 0 < t →
        ∀ z ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1,
           t < inner ℝ z e →
           u z < u (SemilinearPoissonSupport.refl e t z) :=
    SemilinearPoissonSupport.cap_all_of_small u hcap_small
  have hplane :
      ∀ e : EuclideanSpace ℝ (Fin n), ‖e‖ = (1:ℝ) →
        ∀ z ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1,
           u (SemilinearPoissonSupport.refl0 e z) = u z :=
    SemilinearPoissonSupport.plane0_of_cap u hcont hcap

  have heq_open :
      ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1,
        ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1,
          ‖x‖ = ‖y‖ → u x = u y :=
    SemilinearPoissonSupport.equal_norm_of_plane u hplane
  have hlt_open :
      ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1,
        ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1,
          ‖x‖ < ‖y‖ → u y < u x :=
    SemilinearPoissonSupport.strict_norm_of_cap_fin hn u heq_open hcap
  have heq_closed :
      ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
        ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
          ‖x‖ = ‖y‖ → u x = u y :=
    SemilinearPoissonSupport.extend_equal hzero heq_open
  have hlt_closed :
      ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
        ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
          ‖x‖ < ‖y‖ → u y < u x :=
    SemilinearPoissonSupport.extend_strict hu_positive hzero hlt_open
  exact SemilinearPoissonSupport.profile_build hn u hnon heq_closed hlt_closed/-ResultProofEnd-/
/-ResultEnd-/
-- END INLINED FILE: Main.lean

end Submission
