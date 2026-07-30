import ChallengeDeps
import Mathlib
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

-- BEGIN INLINED FILE: Mathlib/Support/sobolev_embedding_morrey_853ace8d32/Kernel.lean
section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal
namespace MorreyTry

lemma measurable_norm_rpow_const {n : ℕ} (a : ℝ) :
    Measurable (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ a) := by
  have hb : Continuous (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖) :=
    continuous_norm
  by_cases h : 0 ≤ a
  · exact ((Real.continuous_rpow_const h).comp hb).measurable
  · have h' : 0 ≤ -a := le_of_lt (neg_pos.mpr (lt_of_not_ge h))
    have hm : Measurable (fun z : EuclideanSpace ℝ (Fin n) =>
        (‖z‖ ^ (-a))⁻¹) :=
      ((Real.continuous_rpow_const h').comp hb).measurable.inv
    convert hm using 1
    funext z
    have he := Real.rpow_neg (norm_nonneg (z : EuclideanSpace ℝ (Fin n))) (-a)
    simpa using he

noncomputable def kernel (n : ℕ) (R : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (Set.indicator (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)
    (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ (-(n:ℝ) + 1))) x

lemma kernel_nonneg (n : ℕ) (R : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ kernel n R x := by
  classical
  by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R
  · simp [kernel, hx, Real.rpow_nonneg]
  · simp [kernel, hx]

lemma kernel_meas (n : ℕ) (R : ℝ) :
    AEStronglyMeasurable (kernel n R) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  have hp : Measurable (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ (-(n:ℝ) + 1)) :=
    measurable_norm_rpow_const _
  exact (hp.indicator (measurableSet_ball)).aestronglyMeasurable

lemma kernel_integrable_pow (n : ℕ) (hn : 1 ≤ n) {R q : ℝ}
    (hq0 : 0 < q) (hq : ((n:ℝ) - 1) * q < n) :
    Integrable (fun z : EuclideanSpace ℝ (Fin n) => (kernel n R z) ^ q)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  have hdim : 1 ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    simpa using hn
  have hα : ((n:ℝ) - 1) * q < Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    simpa using hq
  have hmeas0 : AEStronglyMeasurable
      (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ ((-(n:ℝ) + 1) * q))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (measurable_norm_rpow_const _).aestronglyMeasurable
  have hloc : IntegrableOn
      (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ ((-(n:ℝ) + 1) * q))
      (Metric.ball 0 R) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply integrableOn_ball_of_norm_le_rpow (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      hdim (C := (1:ℝ)) (α := ((n:ℝ) - 1) * q) (r := R) hα
    · filter_upwards [] with z
      -- powers are nonnegative, norm equals itself
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      simp only [one_mul]
      have ha : ((-(n:ℝ) + 1) * q) = -(((n:ℝ) - 1) * q) := by ring
      rw [ha]
    · exact hmeas0
  have hind : Integrable
      ((Set.indicator (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)
        (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ ((-(n:ℝ) + 1) * q))))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    exact (integrable_indicator_iff (measurableSet_ball)).2 hloc
  have heq : (fun z : EuclideanSpace ℝ (Fin n) => (kernel n R z) ^ q) =
      Set.indicator (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)
        (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ ((-(n:ℝ) + 1) * q)) := by
    funext z
    by_cases hz : z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R
    · simp [kernel, hz, ← Real.rpow_mul (norm_nonneg _)]
    · have hqn : q ≠ 0 := ne_of_gt hq0
      simp [kernel, hz, Real.zero_rpow hqn]
  rw [heq]
  exact hind

lemma kernel_memLp (n : ℕ) (hn : 1 ≤ n) {R q : ℝ}
    (hq0 : 0 < q) (hq : ((n:ℝ) - 1) * q < n) :
    MemLp (kernel n R) (ENNReal.ofReal q)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hm := kernel_meas n R
  -- integrable_norm_rpow iff
  apply (integrable_norm_rpow_iff hm (by simpa using hq0) (by simp)).1
  -- show norm power equals pow from previous
  have hi := kernel_integrable_pow n hn (R:=R) hq0 hq
  have heq : (fun z : EuclideanSpace ℝ (Fin n) =>
      ‖kernel n R z‖ ^ (ENNReal.ofReal q).toReal) =
      (fun z => (kernel n R z) ^ q) := by
    funext z
    rw [ENNReal.toReal_ofReal (le_of_lt hq0)]
    rw [Real.norm_of_nonneg (kernel_nonneg n R z)]
  rwa [heq]
end MorreyTry
namespace MorreyTry
open Set Metric
lemma kernel_smul_pow {n : ℕ} {a q:ℝ} (ha:0<a)
    (z:EuclideanSpace ℝ (Fin n)) :
    (kernel n a (a • z)) ^ q =
      a ^ ((-(n:ℝ)+1)*q) * (kernel n 1 z) ^ q := by
  classical
  have hball : (a • z : EuclideanSpace ℝ (Fin n)) ∈ Metric.ball 0 a ↔
      z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    repeat' rw [mem_ball_zero_iff]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    -- a * ||z|| < a
    calc
      a * ‖z‖ < a ↔ ‖z‖ < 1 := by
        constructor
        · intro h; nlinarith
        · intro h; nlinarith
      _ ↔ _ := Iff.rfl
  by_cases hz : z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1
  · have hz' := hball.mpr hz
    -- expand
    simp [kernel, hz, hz', norm_smul, Real.norm_eq_abs, abs_of_pos ha]
        -- simp may do
    rw [Real.mul_rpow (le_of_lt ha) (norm_nonneg _)]
    -- expression ^ q: reorganize
    rw [Real.mul_rpow (Real.rpow_nonneg (le_of_lt ha) _)
          (Real.rpow_nonneg (norm_nonneg _) _)]
    -- exponents
    rw [← Real.rpow_mul (le_of_lt ha), ← Real.rpow_mul (norm_nonneg _)]
  · have hz' : (a • z : EuclideanSpace ℝ (Fin n)) ∉ Metric.ball 0 a := by
      exact fun h => hz (hball.mp h)
    have hqcas : True := trivial
    -- outside both kernels zero, but zero^q: RHS has positive a factor, zero^q;
    -- 0^0=1, then lhs=1 but rhs=a^... ; for q=0 exponent factor=1 OK.
    by_cases hq0 : q = 0
    · subst q; simp
    · simp [kernel, hz, hz', Real.zero_rpow hq0]

lemma kernel_integral_scale (n : ℕ) {a q : ℝ} (ha : 0 < a) :
    (∫ z : EuclideanSpace ℝ (Fin n), (kernel n a z) ^ q ∂volume) =
      a ^ ((n:ℝ) + ((-(n:ℝ)+1)*q)) *
        (∫ z : EuclideanSpace ℝ (Fin n), (kernel n 1 z) ^ q ∂volume) := by
  -- apply scaling on f(z)=kernel ... via smul
  have he := MeasureTheory.Measure.integral_comp_smul_of_nonneg
      (volume : Measure (EuclideanSpace ℝ (Fin n)))
      (fun z : EuclideanSpace ℝ (Fin n) => (kernel n a z) ^ q) a (hR:=le_of_lt ha)
  -- LHS equation: ∫ f(a•z) = (a^n)⁻¹ • ∫ f
  have hpoint : (fun z : EuclideanSpace ℝ (Fin n) => (kernel n a (a • z)) ^ q) =
      (fun z => a ^ ((-(n:ℝ)+1)*q) * (kernel n 1 z) ^ q) := by
    funext z; exact kernel_smul_pow ha z
  -- substitute and solve algebraically (a^n nonzero)
  have he' : a ^ ((-(n:ℝ)+1)*q) *
        (∫ z : EuclideanSpace ℝ (Fin n), (kernel n 1 z) ^ q ∂volume) =
      (a ^ n)⁻¹ * (∫ z : EuclideanSpace ℝ (Fin n), (kernel n a z) ^ q ∂volume) := by
    -- rewrite integral
    simpa [hpoint, MeasureTheory.integral_const_mul, smul_eq_mul]
      using he
  -- multiply by a^n
  have han : (a ^ (n:ℕ) : ℝ) ≠ 0 := pow_ne_zero _ (ne_of_gt ha)
  calc
    (∫ z : EuclideanSpace ℝ (Fin n), (kernel n a z) ^ q ∂volume) =
        (a ^ (n:ℕ) : ℝ) * ((a ^ (n:ℕ) : ℝ)⁻¹ *
          (∫ z : EuclideanSpace ℝ (Fin n), (kernel n a z) ^ q ∂volume)) := by
            rw [← mul_assoc, mul_inv_cancel₀ han, one_mul]
    _ = (a ^ (n:ℕ) : ℝ) *
        (a ^ ((-(n:ℝ)+1)*q) *
          (∫ z : EuclideanSpace ℝ (Fin n), (kernel n 1 z) ^ q ∂volume)) := by
          rw [he']
    _ = _ := by
      rw [← mul_assoc]
      congr 1
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_add ha]
end MorreyTry
namespace MorreyTry
open Set Metric
/-- Holder for the truncated Riesz kernel, with the moving/scaling part isolated. -/
lemma integral_norm_mul_kernel_le {n : ℕ} (hn : 1 ≤ n)
    {R p q : ℝ} (hpq : p.HolderConjugate q)
    (hqdim : ((n:ℝ)-1)*q < n) {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hh : MemLp h (ENNReal.ofReal p) volume) :
    (∫ z : EuclideanSpace ℝ (Fin n), ‖h z‖ * kernel n R z ∂volume) ≤
      (∫ z : EuclideanSpace ℝ (Fin n), ‖h z‖ ^ p ∂volume) ^ (1/p) *
       (∫ z : EuclideanSpace ℝ (Fin n), (kernel n R z) ^ q ∂volume) ^ (1/q) := by
  have hk := kernel_memLp n hn (R:=R) hpq.symm.pos hqdim
  have H := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq hpq hh hk
  -- simplify norm of nonnegative kernel
  simpa [Real.norm_of_nonneg (kernel_nonneg n R _)] using H

lemma integral_norm_mul_kernel_scale_le {n : ℕ} (hn : 1 ≤ n)
    {R p q : ℝ} (hR : 0 < R) (hpq : p.HolderConjugate q)
    (hqdim : ((n:ℝ)-1)*q < n) {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hh : MemLp h (ENNReal.ofReal p) volume) :
    (∫ z : EuclideanSpace ℝ (Fin n), ‖h z‖ * kernel n R z ∂volume) ≤
      (∫ z : EuclideanSpace ℝ (Fin n), ‖h z‖ ^ p ∂volume) ^ (1/p) *
       ( (R ^ ((n:ℝ) + ((-(n:ℝ)+1)*q)) *
          (∫ z : EuclideanSpace ℝ (Fin n), (kernel n 1 z) ^ q ∂volume))
          ^ (1/q)) := by
  rw [← kernel_integral_scale n hR]
  exact integral_norm_mul_kernel_le hn hpq hqdim hh
end MorreyTry

end
-- END INLINED FILE: Mathlib/Support/sobolev_embedding_morrey_853ace8d32/Kernel.lean

-- BEGIN INLINED FILE: Mathlib/Support/sobolev_embedding_morrey_853ace8d32/Morrey.lean
section
open MeasureTheory Set Filter intervalIntegral
open scoped ENNReal NNReal Interval Topology

namespace MorreySupport

abbrev EE (n:ℕ) := EuclideanSpace ℝ (Fin n)

lemma smooth_line_bound {n:ℕ} (u : EE n → ℝ)
    (hu : ContDiff ℝ (1:ℕ∞) u) (x h : EE n) :
    ‖u (x + h) - u x‖ ≤
      ∫ t : ℝ in (0)..(1),
        ‖fderiv ℝ u (x + t • h) h‖ := by
  let F : ℝ → ℝ := fun t => u (x + t • h)
  let B : ℝ → ℝ := fun t => ‖fderiv ℝ u (x + t • h) h‖
  have hx : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => x + t • h) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hcd : ContDiff ℝ (1:ℕ∞) F := hu.comp (hx.of_le (by simp))
  have hcontF : Continuous F := hcd.continuous
  have hdiff : Differentiable ℝ F := hcd.differentiable (by simp)
  have hfc : ContinuousOn F (Icc (0:ℝ) 1) := hcontF.continuousOn
  have hfd : DifferentiableOn ℝ F (Ioo (0:ℝ) 1) := hdiff.differentiableOn
  have hfderiv : ∀ t : ℝ, deriv F t = fderiv ℝ u (x + t • h) h := by
    intro t
    have hinner : HasDerivAt (fun t : ℝ => x + t • h) h t := by
      have hs : HasDerivAt (fun t : ℝ => t • h) h t := by
        simpa using (hasDerivAt_id t).smul_const h
      exact hs.const_add x
    have hu' : DifferentiableAt ℝ u (x + t • h) :=
      (hu.differentiable (by simp) _)
    have H := (hu'.hasFDerivAt.comp_hasDerivAt t hinner)
    exact H.deriv
  have hBcont : Continuous B := by
    have hc' : ContDiff ℝ (0:ℕ∞) (fderiv ℝ u) :=
      hu.fderiv_right (by
        change (↑((0:ℕ∞)+1) : WithTop ℕ∞) ≤ (↑(1:ℕ∞):WithTop ℕ∞)
        norm_num)
    have hc : Continuous (fderiv ℝ u) := hc'.continuous
    exact ((hc.comp hx.continuous).clm_apply continuous_const).norm
  have hBi : IntervalIntegrable B volume (0:ℝ) 1 :=
    hBcont.intervalIntegrable _ _
  have HH := norm_sub_le_integral_of_norm_deriv_le_of_le (f:=F) (B:=B)
      (a:= (0:ℝ)) (b:=1) (by norm_num) hfc hfd
      (by
        filter_upwards [] with t ht
        dsimp [B]
        rw [hfderiv t]) hBi
  simpa [F, B] using HH

end MorreySupport

namespace MorreySupport

/-- For Euclidean domain the norm of a scalar differential is bounded by the
sum of its coordinate differentials.  The deliberately non-sharp `ℓ¹`
constant avoids all choices of an orthonormal basis in Morrey estimates. -/
lemma opNorm_le_sum_coord {n : ℕ}
    (L : EE n →L[ℝ] ℝ) :
    ‖L‖ ≤ ∑ i : Fin n, ‖L (EuclideanSpace.single i (1:ℝ))‖ := by
  classical
  apply L.opNorm_le_bound (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro z
  have hz : (∑ i, (z i) • EuclideanSpace.single i (1:ℝ)) = z := by
    ext j
    have happ (w : Fin n → EuclideanSpace ℝ (Fin n)) :
        (∑ i, w i : EuclideanSpace ℝ (Fin n)) j = ∑ i, (w i) j := by
      classical
      suffices H : ∀ s : Finset (Fin n),
          (∑ i ∈ s, w i : EuclideanSpace ℝ (Fin n)) j = ∑ i ∈ s, (w i) j by
        simpa using H Finset.univ
      intro s
      induction s using Finset.induction with
      | empty => simp
      | @insert a s ha ih => simp [ha, PiLp.add_apply, ih]
    rw [happ]
    simp only [PiLp.smul_apply]
    change (∑ i : Fin n, z i * ((EuclideanSpace.single i (1:ℝ)) j)) = z j
    rw [Finset.sum_eq_single j]
    · simp
    · intro b hb hne
      rw [EuclideanSpace.single_apply, if_neg (Ne.symm hne)]
      simp
    · intro hn
      simp at hn
  conv_lhs => rw [← hz, map_sum]
  calc
   ‖∑ i, L ((z i) • EuclideanSpace.single i (1:ℝ))‖
       ≤ ∑ i, ‖L ((z i) • EuclideanSpace.single i (1:ℝ))‖ := norm_sum_le _ _
   _ = ∑ i, ‖z i‖ * ‖L (EuclideanSpace.single i (1:ℝ))‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_smul, norm_smul, Real.norm_eq_abs]
   _ ≤ ∑ i, ‖z‖ * ‖L (EuclideanSpace.single i (1:ℝ))‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le z i) (norm_nonneg _)
   _ = (∑ i, ‖L (EuclideanSpace.single i (1:ℝ))‖) * ‖z‖ := by
      calc
       _ = ‖z‖ * (∑ i, ‖L (EuclideanSpace.single i (1:ℝ))‖) := by rw [Finset.mul_sum]
       _ = _ := by ring

lemma fderiv_norm_le_sum_partial {n : ℕ} (u : EE n → ℝ) (x : EE n) :
    ‖fderiv ℝ u x‖ ≤
      ∑ i : Fin n, ‖fderiv ℝ u x (EuclideanSpace.single i (1:ℝ))‖ :=
  opNorm_le_sum_coord _

end MorreySupport

namespace MorreySupport

/-- Segment fundamental theorem, with coordinate partials instead of the
operator norm.  This is the convenient ACL input before averaging over
balls. -/
lemma smooth_line_bound_coord {n:ℕ} (u : EE n → ℝ)
    (hu : ContDiff ℝ (1:ℕ∞) u) (x h : EE n) :
    ‖u (x + h) - u x‖ ≤
      ∫ t : ℝ in (0)..(1),
        (∑ i : Fin n,
          ‖fderiv ℝ u (x + t • h) (EuclideanSpace.single i (1:ℝ))‖) * ‖h‖ := by
  classical
  refine (smooth_line_bound u hu x h).trans ?_
  apply intervalIntegral.integral_mono_on (by norm_num)
  · -- continuous hence interval-integrable first integrand
    have hcu : ContDiff ℝ (0:ℕ∞) (fderiv ℝ u) :=
      hu.fderiv_right (by
        change (↑((0:ℕ∞)+1) : WithTop ℕ∞) ≤ (↑(1:ℕ∞):WithTop ℕ∞)
        norm_num)
    have hx' : ContDiff ℝ (⊤:ℕ∞) (fun t : ℝ => x + t • h) :=
      contDiff_const.add (contDiff_id.smul contDiff_const)
    have hcL : Continuous (fun t : ℝ => fderiv ℝ u (x + t • h)) :=
      hcu.continuous.comp hx'.continuous
    have hv : Continuous (fun _ : ℝ => h) := continuous_const
    exact ((hcL.clm_apply hv).norm).intervalIntegrable _ _
  · -- finite sum of continuous partials, times a constant
    have hcu : ContDiff ℝ (0:ℕ∞) (fderiv ℝ u) :=
      hu.fderiv_right (by
        change (↑((0:ℕ∞)+1) : WithTop ℕ∞) ≤ (↑(1:ℕ∞):WithTop ℕ∞)
        norm_num)
    have hx' : ContDiff ℝ (⊤:ℕ∞) (fun t : ℝ => x + t • h) :=
      contDiff_const.add (contDiff_id.smul contDiff_const)
    have hcL : Continuous (fun t : ℝ => fderiv ℝ u (x + t • h)) :=
      hcu.continuous.comp hx'.continuous
    have hci (i : Fin n) : Continuous (fun t : ℝ =>
          ‖fderiv ℝ u (x + t • h) (EuclideanSpace.single i (1:ℝ))‖) :=
      (hcL.clm_apply continuous_const).norm
    have hcs : Continuous (fun t : ℝ =>
          ∑ i : Fin n,
            ‖fderiv ℝ u (x + t • h) (EuclideanSpace.single i (1:ℝ))‖) :=
      continuous_finset_sum _ (fun i _ => hci i)
    exact (hcs.mul continuous_const).intervalIntegrable _ _
  intro t ht
  calc
    ‖fderiv ℝ u (x + t • h) h‖
        ≤ ‖fderiv ℝ u (x + t • h)‖ * ‖h‖ :=
          ContinuousLinearMap.le_opNorm _ _
    _ ≤ (∑ i : Fin n,
          ‖fderiv ℝ u (x + t • h) (EuclideanSpace.single i (1:ℝ))‖) * ‖h‖ :=
      mul_le_mul_of_nonneg_right (fderiv_norm_le_sum_partial u _) (norm_nonneg _)

end MorreySupport
namespace MorreySupport

/-- Global dilation-translation change of variables.  We use the unrestricted
integral on the right when bounding the smaller moving balls; avoiding a
moving-domain change of variables is quite helpful in the Fubini step. -/
lemma integral_translate_dilate {n:ℕ} (H : EE n → ℝ)
    (x : EE n) (t:ℝ) :
    (∫ h : EE n, H (x + t • h) ∂volume) =
      |(t ^ n)⁻¹| * (∫ z : EE n, H z ∂volume) := by
  have A := Measure.integral_comp_smul (volume : Measure (EE n))
    (fun z : EE n => H (x + z)) t
  rw [finrank_euclideanSpace, Fintype.card_fin] at A
  simpa [MeasureTheory.integral_add_left_eq_self, smul_eq_mul] using A

end MorreySupport
namespace MorreySupport

lemma holderWith_of_nndist_le {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] {C t : NNReal} {F : X → Y}
    (h : ∀ x y, nndist (F x) (F y) ≤ C * (nndist x y) ^ (t : ℝ)) :
    HolderWith C t F := by
  intro x y
  rw [edist_nndist, edist_nndist]
  calc
    (↑(nndist (F x) (F y)) : ℝ≥0∞) ≤
        ↑(C * (nndist x y) ^ (t : ℝ)) := ENNReal.coe_le_coe.mpr (h x y)
    _ = (C : ℝ≥0∞) * (↑(nndist x y) : ℝ≥0∞) ^ (t : ℝ) := by
      rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg]
      exact NNReal.coe_nonneg _
    _ = _ := by rfl

/-- A fixed Hölder constant survives pointwise limits.  This is the exact
compactness step needed after a uniformly controlled net of mollifications;
only pointwise convergence is required once the common constant is known. -/
lemma holderWith_of_pointwise_limit
    {X Y ι : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {l : Filter ι} [l.NeBot] {C t : NNReal}
    {Fj : ι → X → Y} {F : X → Y}
    (hJ : ∀ j, HolderWith C t (Fj j))
    (hlim : ∀ x, Filter.Tendsto (fun j => Fj j x) l (nhds (F x))) :
    HolderWith C t F := by
  apply holderWith_of_nndist_le
  intro x y
  -- use the real distance for the limit; turn it back into `nndist` at the end
  have ht : Filter.Tendsto (fun j => dist (Fj j x) (Fj j y)) l
      (nhds (dist (F x) (F y))) :=
    Filter.Tendsto.dist (hlim x) (hlim y)
  have hreal : dist (F x) (F y) ≤ (C:ℝ) * (nndist x y : ℝ) ^ (t:ℝ) := by
    apply le_of_tendsto' ht
    intro j
    have hj := (hJ j).dist_le x y
    simpa using hj
  exact_mod_cast hreal

end MorreySupport
namespace MorreySupport
open Metric

/-- Fubini form of the segment estimate on a ball.  It separates completely
the elementary ACL/compact/Fubini part of the Morrey estimate from the
remaining one-variable singular integral.  `closedBall` is used to avoid any
boundary extension of integrability. -/
lemma smooth_ball_segment_bound {n:ℕ} (u : EE n → ℝ)
    (hu : ContDiff ℝ (1:ℕ∞) u) (x : EE n) (R:ℝ) :
    (∫ h : EE n in closedBall 0 R, ‖u (x+h) - u x‖ ∂volume) ≤
       ∫ t : ℝ in Set.Icc 0 1,
          ∫ h : EE n in closedBall 0 R,
            (∑ i : Fin n,
              ‖fderiv ℝ u (x + t • h) (EuclideanSpace.single i (1:ℝ))‖) * ‖h‖
            ∂volume ∂volume := by
  classical
  let A : EE n → ℝ := fun h => ‖u (x+h) - u x‖
  let W : EE n → ℝ → ℝ := fun h t =>
    (∑ i : Fin n, ‖fderiv ℝ u (x + t • h)
      (EuclideanSpace.single i (1:ℝ))‖) * ‖h‖
  have hd : ContDiff ℝ (0:ℕ∞) (fderiv ℝ u) :=
    hu.fderiv_right (by
      change (↑((0:ℕ∞)+1) : WithTop ℕ∞) ≤ (↑(1:ℕ∞):WithTop ℕ∞)
      norm_num)
  have hcA : Continuous A := by
    dsimp [A]
    have hcadd : Continuous (fun h : EE n => x + h) := continuous_const.add continuous_id
    exact ((hu.continuous.comp hcadd).sub continuous_const).norm
  have hcW : Continuous (Function.uncurry W : EE n × ℝ → ℝ) := by
    have harg : Continuous (fun w : EE n × ℝ => x + w.2 • w.1) :=
      continuous_const.add (continuous_snd.smul continuous_fst)
    have hclm : Continuous (fun w : EE n × ℝ => fderiv ℝ u (x + w.2 • w.1)) :=
      hd.continuous.comp harg
    have hi (i : Fin n) : Continuous (fun w : EE n × ℝ =>
        ‖fderiv ℝ u (x + w.2 • w.1) (EuclideanSpace.single i (1:ℝ))‖) :=
      (hclm.clm_apply continuous_const).norm
    change Continuous (fun w : EE n × ℝ =>
      (∑ i : Fin n, ‖fderiv ℝ u (x + w.2 • w.1)
        (EuclideanSpace.single i (1:ℝ))‖) * ‖w.1‖)
    exact (continuous_finset_sum _ (fun i _ => hi i)).mul continuous_fst.norm
  let B : Set (EE n) := closedBall 0 R
  let T : Set ℝ := Set.Icc 0 1
  have hB : IsCompact B := ProperSpace.isCompact_closedBall _ _
  have hT : IsCompact T := isCompact_Icc
  have hBm : MeasurableSet B := isClosed_closedBall.measurableSet
  have hTm : MeasurableSet T := measurableSet_Icc
  have hprod : IntegrableOn (Function.uncurry W) (B ×ˢ T)
      ((volume : Measure (EE n)).prod (volume : Measure ℝ)) :=
    ContinuousOn.integrableOn_compact (hB.prod hT) hcW.continuousOn
  have hrest : Integrable (Function.uncurry W)
      ((volume : Measure (EE n)).restrict B |>.prod
        ((volume : Measure ℝ).restrict T)) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact hprod
  have hGi : Integrable
      (fun h => ∫ t, W h t ∂((volume : Measure ℝ).restrict T))
      ((volume : Measure (EE n)).restrict B) :=
    hrest.integral_prod_left
  have hAi : IntegrableOn A B (volume : Measure (EE n)) :=
    ContinuousOn.integrableOn_compact hB hcA.continuousOn
  have hmono :
      (∫ h : EE n in B, A h ∂volume) ≤
      ∫ h : EE n in B, (∫ t : ℝ in T, W h t ∂volume) ∂volume := by
    apply setIntegral_mono_on hAi hGi hBm
    intro h hh
    have HL := smooth_line_bound_coord u hu x h
    -- write the ordinary interval integral as an integral on `Icc`; the
    -- singleton endpoint has zero volume.
    simpa [A, W, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      Measure.restrict_congr_set (MeasureTheory.Ioc_ae_eq_Icc :
        (Set.Ioc (0:ℝ) 1 : Set ℝ) =ᵐ[volume] Set.Icc 0 1)] using HL
  calc
    (∫ h : EE n in closedBall 0 R, ‖u (x+h) - u x‖ ∂volume)
        = ∫ h : EE n in B, A h ∂volume := by rfl
    _ ≤ ∫ h : EE n in B, (∫ t : ℝ in T, W h t ∂volume) ∂volume := hmono
    _ = ∫ t : ℝ in T, (∫ h : EE n in B, W h t ∂volume) ∂volume := by
      exact MeasureTheory.integral_integral_swap hrest
    _ = _ := by rfl

end MorreySupport

end
-- END INLINED FILE: Mathlib/Support/sobolev_embedding_morrey_853ace8d32/Morrey.lean

-- BEGIN INLINED FILE: Mathlib/Support/sobolev_embedding_morrey_853ace8d32/Scale.lean
section
open MeasureTheory Set Metric intervalIntegral
open scoped ENNReal NNReal
namespace MorreySupport
abbrev EX (n:ℕ) := EuclideanSpace ℝ (Fin n)

/-- The elementary finite-set Holder inequality in the form useful in the
Morrey proof.  This little lemma removes all the `indicator` / Bochner
integral bookkeeping: it is valid for an arbitrary measurable finite-measure
set. -/
lemma setIntegral_norm_le_Lp_mul_measure
    {n : ℕ} {s : Set (EX n)} (hs : MeasurableSet s)
    (hfin : (volume : Measure (EX n)) s ≠ ⊤)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    {A : EX n → ℝ} (hA : MemLp A (ENNReal.ofReal p) volume) :
    (∫ z : EX n in s, ‖A z‖ ∂volume) ≤
      (∫ z : EX n, ‖A z‖ ^ p ∂volume) ^ (1/p) *
        ((volume.real s : ℝ) ^ (1/q)) := by
  classical
  let oneS : EX n → ℝ := s.indicator (fun _ => (1:ℝ))
  have hmem : MemLp oneS (ENNReal.ofReal q) (volume : Measure (EX n)) := by
    exact memLp_indicator_const (ENNReal.ofReal q) hs (1:ℝ) (Or.inr hfin)
  have HH := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq hpq hA hmem
  -- the bounded factor is exactly the indicator of the set.
  have hleft :
      (∫ z : EX n, ‖A z‖ * ‖oneS z‖ ∂volume) =
        ∫ z : EX n in s, ‖A z‖ ∂volume := by
    rw [← MeasureTheory.integral_indicator hs]
    congr 1
    funext z
    by_cases hz : z ∈ s
    · simp [oneS, hz]
    · simp [oneS, hz]
  have hright :
      (∫ z : EX n, ‖oneS z‖ ^ q ∂volume) = volume.real s := by
    -- same computation, now with the `q`th power.  Positivity of the
    -- conjugate exponent is important at the zeros of the indicator.
    have hq0 : q ≠ 0 := ne_of_gt hpq.symm.pos
    have heq : (fun z : EX n => ‖oneS z‖ ^ q) =
        s.indicator (fun _ : EX n => (1:ℝ)) := by
      funext z
      by_cases hz : z ∈ s
      · simp [oneS, hz]
      · simp [oneS, hz, Real.zero_rpow hq0]
    rw [heq, MeasureTheory.integral_indicator hs]
    -- integral of the constant is the real measure
    simp [hfin]
  rw [hleft, hright] at HH
  exact HH
end MorreySupport
namespace MorreySupport
open Metric
/-- Change of variables in a ball under a positive homothety.  Stating it
with `closedBall` is handy: the preceding elementary segment lemma is a
literal integral on this compact set, so no boundary/null-set choices enter
later estimates. -/
lemma setIntegral_comp_smul_closedBall
    {n : ℕ} (A : EX n → ℝ) (x : EX n) {t R : ℝ}
    (ht : 0 < t) (hR : 0 ≤ R) :
    (∫ h : EX n in Metric.closedBall 0 R, A (x + t • h) ∂volume) =
      (t ^ n)⁻¹ *
        (∫ z : EX n in Metric.closedBall 0 (t*R), A (x + z) ∂volume) := by
  classical
  let S : Set (EX n) := Metric.closedBall (0 : EX n) (t*R)
  let G : EX n → ℝ := S.indicator (fun z => A (x + z))
  have he := MeasureTheory.Measure.integral_comp_smul_of_nonneg
      (volume : Measure (EX n)) G t (hR:= le_of_lt ht)
  rw [finrank_euclideanSpace, Fintype.card_fin] at he
  have heR (h : EX n) :
      (t • h : EX n) ∈ S ↔ h ∈ Metric.closedBall (0 : EX n) R := by
    dsimp [S]
    repeat' rw [mem_closedBall_zero_iff]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    -- multiplication by a positive number preserves the weak inequality
    constructor
    · intro H
      nlinarith
    · intro H
      nlinarith
  have hL : (fun h : EX n => G (t • h)) =
      (Metric.closedBall (0 : EX n) R).indicator
        (fun h : EX n => A (x + t • h)) := by
    funext h
    by_cases hh : h ∈ Metric.closedBall (0 : EX n) R
    · have hh' : (t • h : EX n) ∈ S := (heR h).2 hh
      simp [G, hh, hh']
    · have hh' : (t • h : EX n) ∉ S := fun H => hh ((heR h).1 H)
      simp [G, hh, hh']
  have hLint : (∫ h : EX n, G (t • h) ∂volume) =
      ∫ h : EX n in Metric.closedBall 0 R, A (x + t • h) ∂volume := by
    rw [hL, MeasureTheory.integral_indicator measurableSet_closedBall]
  have hRint : (∫ z : EX n, G z ∂volume) =
      ∫ z : EX n in Metric.closedBall 0 (t*R), A (x + z) ∂volume := by
    exact MeasureTheory.integral_indicator measurableSet_closedBall
  -- `•` on reals is multiplication.
  rw [hLint, hRint, smul_eq_mul] at he
  exact he
end MorreySupport
namespace MorreySupport
/-- Holder after the elementary homothety.  Notice the very useful `t` factor
has dimension `t⁻ⁿ`; at the next (one-dimensional) integration this combines
with the measure of the smaller ball.  No singular kernel or polar
coordinates are needed for this perfectly adequate, slightly nonsharp,
version of Morrey's estimate. -/
lemma setIntegral_norm_comp_add_smul_le
    {n : ℕ} {A : EX n → ℝ} {p q : ℝ}
    (hpq : p.HolderConjugate q)
    (hA : MemLp A (ENNReal.ofReal p) (volume : Measure (EX n)))
    (x : EX n) {t R : ℝ} (ht : 0 < t) (hR : 0 ≤ R) :
    (∫ h : EX n in Metric.closedBall 0 R, ‖A (x + t • h)‖ ∂volume) ≤
      (t ^ n)⁻¹ *
        ((∫ z : EX n, ‖A z‖ ^ p ∂volume) ^ (1/p) *
          ((volume.real (Metric.closedBall (0 : EX n) (t*R)) : ℝ) ^ (1/q))) := by
  classical
  let B : EX n → ℝ := fun z => A (x + z)
  have hB : MemLp B (ENNReal.ofReal p) (volume : Measure (EX n)) := by
    have H := hA.comp_measurePreserving
      (MeasureTheory.measurePreserving_add_left (volume : Measure (EX n)) x)
    simpa [B, Function.comp_def] using H
  have hpowe :
      (∫ z : EX n, ‖B z‖ ^ p ∂volume) =
        ∫ z : EX n, ‖A z‖ ^ p ∂volume := by
    have hemb : MeasurableEmbedding (fun z : EX n => x + z) :=
      (Homeomorph.addLeft x).measurableEmbedding
    have hp0 := (MeasureTheory.measurePreserving_add_left
          (volume : Measure (EX n)) x)
    simpa [B] using hp0.integral_comp hemb
      (fun z : EX n => (‖A z‖ ^ p : ℝ))
  have hfin : (volume : Measure (EX n))
      (Metric.closedBall (0 : EX n) (t*R)) ≠ ⊤ :=
    (measure_closedBall_lt_top).ne
  have HH := setIntegral_norm_le_Lp_mul_measure
      (n:=n) (s:=Metric.closedBall (0 : EX n) (t*R))
      measurableSet_closedBall hfin hpq hB
  rw [hpowe] at HH
  have hcv := setIntegral_comp_smul_closedBall
      (n:=n) (fun z : EX n => ‖B z‖) 0 ht hR
  -- the `0 +` in this formula was only used to hit the general change of
  -- variables lemma above.  Simplify it on both sides.
  simp only [zero_add] at hcv
  -- nonnegativity of the homothety coefficient permits multiplication of
  -- Holder's scalar inequality.
  calc
    (∫ h : EX n in Metric.closedBall 0 R, ‖A (x + t • h)‖ ∂volume)
        = (t ^ n)⁻¹ *
          (∫ z : EX n in Metric.closedBall 0 (t*R), ‖B z‖ ∂volume) := by
            simpa [B] using hcv
    _ ≤ (t ^ n)⁻¹ *
        ((∫ z : EX n, ‖A z‖ ^ p ∂volume) ^ (1/p) *
          ((volume.real (Metric.closedBall (0 : EX n) (t*R)) : ℝ) ^ (1/q))) := by
            have hnon : 0 ≤ (t ^ n)⁻¹ := by positivity
            exact mul_le_mul_of_nonneg_left HH hnon
end MorreySupport
namespace MorreySupport
lemma real_volume_closedBall_zero
    {n : ℕ} (s : ℝ) (hs : 0 ≤ s) :
    (volume : Measure (EX n)).real (Metric.closedBall 0 s) =
      s ^ n * (volume : Measure (EX n)).real
        (Metric.ball (0 : EX n) 1) := by
  simpa [finrank_euclideanSpace] using
    (MeasureTheory.Measure.addHaar_real_closedBall
      (volume : Measure (EX n)) (0 : EX n) hs)
end MorreySupport
namespace MorreySupport
lemma setIntegral_weight_norm_le_radius
    {n : ℕ} {A : EX n → ℝ} (hAc : Continuous A)
    (x : EX n) (t : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    (∫ h : EX n in Metric.closedBall 0 R,
       ‖A (x + t • h)‖ * ‖h‖ ∂volume) ≤
      R * (∫ h : EX n in Metric.closedBall 0 R,
        ‖A (x + t • h)‖ ∂volume) := by
  classical
  let C : Set (EX n) := Metric.closedBall 0 R
  have hcomp : IsCompact C := ProperSpace.isCompact_closedBall _ _
  have hcAarg : Continuous (fun h : EX n => A (x + t • h)) :=
    hAc.comp (continuous_const.add (continuous_const.smul continuous_id))
  have hI : IntegrableOn
      (fun h : EX n => ‖A (x + t • h)‖ * ‖h‖) C
        (volume : Measure (EX n)) :=
    ContinuousOn.integrableOn_compact hcomp
      ((hcAarg.norm.mul continuous_norm).continuousOn)
  have hJ : IntegrableOn
      (fun h : EX n => R * ‖A (x + t • h)‖) C
        (volume : Measure (EX n)) :=
    ContinuousOn.integrableOn_compact hcomp
      ((continuous_const.mul hcAarg.norm).continuousOn)
  calc
    (∫ h : EX n in Metric.closedBall 0 R,
        ‖A (x + t • h)‖ * ‖h‖ ∂volume)
       ≤ ∫ h : EX n in Metric.closedBall 0 R,
            R * ‖A (x + t • h)‖ ∂volume := by
          apply setIntegral_mono_on hI hJ measurableSet_closedBall
          intro h hh
          have hb : ‖h‖ ≤ R := by
            have H := (mem_closedBall_zero_iff.mp hh)
            exact H
          have hz : 0 ≤ ‖A (x + t • h)‖ := norm_nonneg _
          nlinarith
    _ = R * (∫ h : EX n in Metric.closedBall 0 R,
            ‖A (x + t • h)‖ ∂volume) := by
          rw [MeasureTheory.integral_const_mul]

/-- The weighted version for a continuous `L^p` function.  This is the
precise fixed-`t` estimate needed after the segment fundamental theorem.  The
singularity in the next integral is one-dimensional (`t^{-n/p}`), much
simpler to handle than polar coordinates. -/
lemma setIntegral_weight_comp_add_smul_le
    {n : ℕ} {A : EX n → ℝ} (hAc : Continuous A)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (hA : MemLp A (ENNReal.ofReal p) (volume : Measure (EX n)))
    (x : EX n) {t R : ℝ} (ht : 0 < t) (hR : 0 ≤ R) :
    (∫ h : EX n in Metric.closedBall 0 R,
       ‖A (x + t • h)‖ * ‖h‖ ∂volume) ≤
      R * ((t ^ n)⁻¹ *
        ((∫ z : EX n, ‖A z‖ ^ p ∂volume) ^ (1/p) *
          ((volume.real (Metric.closedBall (0 : EX n) (t*R)) : ℝ) ^ (1/q)))) := by
  calc
    (∫ h : EX n in Metric.closedBall 0 R,
       ‖A (x + t • h)‖ * ‖h‖ ∂volume)
      ≤ R * (∫ h : EX n in Metric.closedBall 0 R,
          ‖A (x + t • h)‖ ∂volume) :=
        setIntegral_weight_norm_le_radius hAc x t hR
    _ ≤ R * ((t ^ n)⁻¹ *
        ((∫ z : EX n, ‖A z‖ ^ p ∂volume) ^ (1/p) *
          ((volume.real (Metric.closedBall (0 : EX n) (t*R)) : ℝ) ^ (1/q)))) := by
          exact mul_le_mul_of_nonneg_left
            (setIntegral_norm_comp_add_smul_le hpq hA x ht hR) hR
end MorreySupport

end
-- END INLINED FILE: Mathlib/Support/sobolev_embedding_morrey_853ace8d32/Scale.lean

-- BEGIN INLINED FILE: Mathlib/Support/sobolev_embedding_morrey_853ace8d32/Endpoint.lean
section
open MeasureTheory Set Metric intervalIntegral
open scoped ENNReal NNReal
namespace MorreySupport
-- scalar simplification for one dimensional residual
lemma homothety_holder_scalar
    (n : ℕ) {p q : ℝ} (hpq : p.HolderConjugate q)
    {t R B : ℝ} (ht : 0 < t) (hR : 0 ≤ R) (hB : 0 ≤ B) :
    (t ^ n : ℝ)⁻¹ * ((((t*R)^n : ℝ) * B) ^ (1/q)) =
      (B ^ (1/q) * R ^ ((n:ℝ)/q)) * t ^ (-(n:ℝ)/p) := by
  have hp : 1 < p := hpq.lt
  have hpn : p ≠ 0 := by linarith
  have hq : 1 < q := hpq.symm.lt
  have hqn : q ≠ 0 := by linarith
  have ht0 : 0 ≤ t := le_of_lt ht
  have htR : 0 ≤ t*R := mul_nonneg ht0 hR
  have hpow : 0 ≤ (t*R)^n := pow_nonneg htR _
  have hexp : (-(n:ℝ) + (n:ℝ)/q) = -(n:ℝ)/p := by
    rw [hpq.conjugate_eq]
    field_simp
    ring
  rw [Real.mul_rpow hpow hB]
  rw [← Real.rpow_natCast_mul htR n (1/q)]
  rw [Real.mul_rpow ht0 hR]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_neg ht0]
  -- put the powers of t next to each other
  have hmul_t : t ^ (-(n:ℝ)) * t ^ ((n:ℝ) * (1/q)) =
      t ^ (-(n:ℝ)/p) := by
    rw [← Real.rpow_add ht]
    have he : (-(n:ℝ) + (n:ℝ) * (1/q)) = -(n:ℝ)/p := by
      convert hexp using 1 <;> field_simp <;> ring
    rw [he]
  calc
    t ^ (-(n:ℝ)) * (t ^ ((n:ℝ) * (1/q)) *
          R ^ ((n:ℝ) * (1/q)) * B ^ (1/q))
        = (t ^ (-(n:ℝ)) * t ^ ((n:ℝ) * (1/q))) *
            R ^ ((n:ℝ) * (1/q)) * B ^ (1/q) := by ring
    _ = (B ^ (1/q) * R ^ ((n:ℝ)/q)) * t ^ (-(n:ℝ)/p) := by
      rw [hmul_t]
      have hh : ((n:ℝ) * (1/q)) = (n:ℝ)/q := by field_simp
      rw [hh]
      ring
end MorreySupport
namespace MorreySupport
open MeasureTheory
lemma setIntegral_weight_comp_add_smul_le_rpow
    {n : ℕ} {A : EX n → ℝ} (hAc : Continuous A)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (hA : MemLp A (ENNReal.ofReal p) (volume : Measure (EX n)))
    (x : EX n) {t R : ℝ} (ht : 0 < t) (hR : 0 ≤ R) :
    (∫ h : EX n in Metric.closedBall 0 R,
       ‖A (x + t • h)‖ * ‖h‖ ∂volume) ≤
      (R * (∫ z : EX n, ‖A z‖ ^ p ∂volume) ^ (1/p) *
        ((volume : Measure (EX n)).real (Metric.ball (0 : EX n) 1)) ^ (1/q) *
          R ^ ((n:ℝ)/q)) * t ^ (-(n:ℝ)/p) := by
  have H := setIntegral_weight_comp_add_smul_le
    (n:=n) (A:=A) hAc hpq hA x ht hR
  calc
    (∫ h : EX n in Metric.closedBall 0 R,
       ‖A (x + t • h)‖ * ‖h‖ ∂volume)
      ≤ R * ((t ^ n)⁻¹ *
        ((∫ z : EX n, ‖A z‖ ^ p ∂volume) ^ (1/p) *
          (( (volume : Measure (EX n)).real
             (Metric.closedBall (0 : EX n) (t*R)) : ℝ) ^ (1/q)))) := H
    _ = (R * (∫ z : EX n, ‖A z‖ ^ p ∂volume) ^ (1/p) *
        ((volume : Measure (EX n)).real (Metric.ball (0 : EX n) 1)) ^ (1/q) *
          R ^ ((n:ℝ)/q)) * t ^ (-(n:ℝ)/p) := by
      rw [real_volume_closedBall_zero (t*R) (mul_nonneg (le_of_lt ht) hR)]
      have hs := homothety_holder_scalar n hpq ht hR
          (MeasureTheory.measureReal_nonneg :
            0 ≤ (volume : Measure (EX n)).real (Metric.ball (0 : EX n) 1))
      calc
        R * ((t ^ n)⁻¹ *
          ((∫ z : EX n, ‖A z‖ ^ p ∂volume) ^ (1/p) *
            (((t*R)^n * (volume : Measure (EX n)).real
                (Metric.ball (0 : EX n) 1)) ^ (1/q)))) =
          R * ((∫ z : EX n, ‖A z‖ ^ p ∂volume) ^ (1/p) *
            ((t ^ n)⁻¹ *
              (((t*R)^n * (volume : Measure (EX n)).real
                (Metric.ball (0 : EX n) 1)) ^ (1/q)))) := by ring
        _ = _ := by rw [hs]; ring
end MorreySupport
namespace MorreySupport
open MeasureTheory Set Metric intervalIntegral
lemma smooth_ball_segment_Lp_bound
    {n : ℕ} (u : EX n → ℝ) (hu : ContDiff ℝ (1 : ℕ∞) u)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (hLp : ∀ i : Fin n,
      MemLp (fun z : EX n => fderiv ℝ u z (EuclideanSpace.single i (1:ℝ)))
        (ENNReal.ofReal p) (volume : Measure (EX n)))
    (hnp : (n:ℝ)/p < 1)
    (x : EX n) {R : ℝ} (hR : 0 ≤ R) :
    (∫ h : EX n in Metric.closedBall 0 R, ‖u (x+h) - u x‖ ∂volume) ≤
      ((R * (∑ i : Fin n,
          (∫ z : EX n,
            ‖fderiv ℝ u z (EuclideanSpace.single i (1:ℝ))‖ ^ p ∂volume) ^ (1/p)) *
          ((volume : Measure (EX n)).real (Metric.ball (0 : EX n) 1)) ^ (1/q) *
          R ^ ((n:ℝ)/q))) *
        (1 / (1 - (n:ℝ)/p)) := by
  classical
  let T : Set ℝ := Set.Icc 0 1
  let B0 : Set (EX n) := Metric.closedBall 0 R
  -- The two-variable integrand in the ball lemma is continuous on the compact product.
  let W : EX n → ℝ → ℝ := fun h t =>
    (∑ i : Fin n,
       ‖fderiv ℝ u (x + t • h) (EuclideanSpace.single i (1:ℝ))‖) * ‖h‖
  have hd : ContDiff ℝ (0:ℕ∞) (fderiv ℝ u) :=
    hu.fderiv_right (by
      change (↑((0:ℕ∞)+1) : WithTop ℕ∞) ≤ (↑(1:ℕ∞):WithTop ℕ∞)
      norm_num)
  have hcW : Continuous (Function.uncurry W : EX n × ℝ → ℝ) := by
    have harg : Continuous (fun w : EX n × ℝ => x + w.2 • w.1) :=
      continuous_const.add (continuous_snd.smul continuous_fst)
    have hclm : Continuous (fun w : EX n × ℝ => fderiv ℝ u (x + w.2 • w.1)) :=
      hd.continuous.comp harg
    have hi (i : Fin n) : Continuous (fun w : EX n × ℝ =>
        ‖fderiv ℝ u (x + w.2 • w.1) (EuclideanSpace.single i (1:ℝ))‖) :=
      (hclm.clm_apply continuous_const).norm
    exact (continuous_finset_sum _ (fun i _ => hi i)).mul continuous_fst.norm
  have hB : IsCompact B0 := ProperSpace.isCompact_closedBall _ _
  have hT : IsCompact T := isCompact_Icc
  have hres : Integrable (Function.uncurry W)
      ((volume : Measure (EX n)).restrict B0 |>.prod
        ((volume : Measure ℝ).restrict T)) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact ContinuousOn.integrableOn_compact (hB.prod hT) hcW.continuousOn
  let G : ℝ → ℝ := fun t => ∫ h : EX n in B0, W h t ∂volume
  have hG : IntegrableOn G T (volume : Measure ℝ) := by
    have H := hres.integral_prod_right
    -- this is literally the definition of the restricted integrals
    change Integrable G ((volume : Measure ℝ).restrict T)
    simpa [G] using H
  let aexp : ℝ := -(n:ℝ)/p
  let D : ℝ :=
    R * (∑ i : Fin n,
        (∫ z : EX n,
          ‖fderiv ℝ u z (EuclideanSpace.single i (1:ℝ))‖ ^ p ∂volume) ^ (1/p)) *
        ((volume : Measure (EX n)).real (Metric.ball (0 : EX n) 1)) ^ (1/q) *
        R ^ ((n:ℝ)/q)
  -- equality of the inner integral with a finite sum. This is where the
  -- weighted one-function estimate from `Scale` can be applied entrywise.
  have hinner (t : ℝ) :
      G t = ∑ i : Fin n, ∫ h : EX n in B0,
        ‖(fun z : EX n => fderiv ℝ u z (EuclideanSpace.single i (1:ℝ)))
              (x + t • h)‖ * ‖h‖ ∂volume := by
    have hci (i : Fin n) : Continuous (fun h : EX n =>
        ‖(fun z : EX n => fderiv ℝ u z (EuclideanSpace.single i (1:ℝ)))
              (x + t • h)‖ * ‖h‖) := by
      have hA : Continuous (fun z : EX n =>
          fderiv ℝ u z (EuclideanSpace.single i (1:ℝ))) :=
        (hd.continuous.clm_apply continuous_const)
      exact ((hA.comp (continuous_const.add
        (continuous_const.smul continuous_id))).norm).mul continuous_norm
    have hIi (i : Fin n) : IntegrableOn (fun h : EX n =>
        ‖(fun z : EX n => fderiv ℝ u z (EuclideanSpace.single i (1:ℝ)))
              (x + t • h)‖ * ‖h‖) B0 (volume : Measure (EX n)) :=
      ContinuousOn.integrableOn_compact hB (hci i).continuousOn
    -- move the finite sum through the restricted integral
    have hh := MeasureTheory.integral_finset_sum
       (μ := (volume : Measure (EX n)).restrict B0) (Finset.univ : Finset (Fin n))
       (fun i _ => hIi i)
    -- rewrite the pointwise product `(sum) * ‖h‖`.
    change (∫ h : EX n in B0,
        (∑ i : Fin n,
          ‖fderiv ℝ u (x + t • h) (EuclideanSpace.single i (1:ℝ))‖) * ‖h‖ ∂volume) = _
    rw [← hh]
    congr 1
    funext h
    rw [Finset.sum_mul]
  have hpoint : ∀ t : ℝ, 0 < t →
      G t ≤ D * t ^ aexp := by
    intro t ht
    rw [hinner t]
    have Hsum : ∑ i : Fin n, (∫ h : EX n in B0,
        ‖(fun z : EX n => fderiv ℝ u z (EuclideanSpace.single i (1:ℝ)))
              (x + t • h)‖ * ‖h‖ ∂volume) ≤
        ∑ i : Fin n,
          ((R * (∫ z : EX n,
            ‖fderiv ℝ u z (EuclideanSpace.single i (1:ℝ))‖ ^ p ∂volume) ^ (1/p) *
            ((volume : Measure (EX n)).real (Metric.ball (0 : EX n) 1)) ^ (1/q) *
              R ^ ((n:ℝ)/q)) * t ^ (-(n:ℝ)/p)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hAc : Continuous (fun z : EX n =>
          fderiv ℝ u z (EuclideanSpace.single i (1:ℝ))) :=
        hd.continuous.clm_apply continuous_const
      simpa [B0] using
        (setIntegral_weight_comp_add_smul_le_rpow
          (n:=n) (A:= fun z : EX n =>
              fderiv ℝ u z (EuclideanSpace.single i (1:ℝ))) hAc hpq (hLp i)
              x ht hR)
    calc
      _ ≤ _ := Hsum
      _ = D * t ^ aexp := by
        dsimp [D, aexp]
        calc
          (∑ i : Fin n,
            ((R * (∫ z : EX n,
                ‖fderiv ℝ u z (EuclideanSpace.single i (1:ℝ))‖ ^ p ∂volume) ^ (1/p) *
                ((volume : Measure (EX n)).real (Metric.ball (0 : EX n) 1)) ^ (1/q) *
                R ^ ((n:ℝ)/q)) * t ^ (-(n:ℝ)/p))) =
            (∑ i : Fin n,
                (∫ z : EX n,
                  ‖fderiv ℝ u z (EuclideanSpace.single i (1:ℝ))‖ ^ p ∂volume) ^ (1/p)) *
              (R * ((volume : Measure (EX n)).real (Metric.ball (0 : EX n) 1)) ^ (1/q) *
                R ^ ((n:ℝ)/q) * t ^ (-(n:ℝ)/p)) := by
                  rw [Finset.sum_mul]
                  apply Finset.sum_congr rfl
                  intro i hi
                  ring
          _ = _ := by simp only [Real.norm_eq_abs]; ring
  have hexp : -1 < aexp := by
    dsimp [aexp]
    have hh : -(1:ℝ) < -((n:ℝ)/p) := neg_lt_neg hnp
    simpa [neg_div] using hh
  have hpowInt : IntervalIntegrable (fun t : ℝ => t ^ aexp)
        (volume : Measure ℝ) 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' hexp
  have hDI : IntegrableOn (fun t : ℝ => D * t ^ aexp) T
        (volume : Measure ℝ) := by
    have htemp : IntervalIntegrable (fun t : ℝ => D * t ^ aexp)
        (volume : Measure ℝ) 0 1 := hpowInt.const_mul _
    -- move from `Ioc` to `Icc`; the singleton endpoint is null.
    exact (integrableOn_Icc_iff_integrableOn_Ioc).2 htemp.1
  have hmono : (∫ t : ℝ in T, G t ∂volume) ≤
      ∫ t : ℝ in T, D * t ^ aexp ∂volume := by
    apply MeasureTheory.setIntegral_mono_ae_restrict hG hDI
    -- the endpoint 0 is irrelevant to the restricted measure
    have hne : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), t ≠ 0 := by
      rw [ae_iff]
      simpa using (measure_singleton (μ := (volume : Measure ℝ)) (0:ℝ))
    have hre : ∀ᵐ t : ℝ ∂(volume : Measure ℝ).restrict T,
          t ∈ T := MeasureTheory.ae_restrict_mem measurableSet_Icc
    have hne' : ∀ᵐ t : ℝ ∂(volume : Measure ℝ).restrict T, t ≠ 0 := by
      -- pull the ambient null singleton into the restriction
      have hle : (volume : Measure ℝ).restrict T ≤ (volume : Measure ℝ) :=
        Measure.restrict_le_self
      exact ae_mono hle hne
    filter_upwards [hre, hne'] with t htT ht0
    apply hpoint t
    have hnon : 0 ≤ t := htT.1
    exact lt_of_le_of_ne hnon (Ne.symm ht0)
  have hval : (∫ t : ℝ in T, D * t ^ aexp ∂volume) =
      D * (1 / (1 - (n:ℝ)/p)) := by
    have hEq : (∫ t : ℝ in T, D * t ^ aexp ∂volume) =
        ∫ t : ℝ in (0:ℝ)..1, D * t ^ aexp := by
      -- identify `Ioc` and `Icc` modulo the left endpoint
      have hx : (∫ t : ℝ in (0:ℝ)..1, D * t ^ aexp) =
          ∫ t : ℝ in T, D * t ^ aexp ∂volume := by
        rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
        dsimp [T]
        rw [Measure.restrict_congr_set
          (MeasureTheory.Ioc_ae_eq_Icc :
            (Set.Ioc (0:ℝ) 1 : Set ℝ) =ᵐ[volume] Set.Icc 0 1)]
      exact hx.symm
    rw [hEq]
    rw [intervalIntegral.integral_const_mul]
    have HH := integral_rpow (a:= (0:ℝ)) (b:=1) (r:=aexp)
        (Or.inl hexp)
    rw [HH]
    have hpos : 0 < 1 - (n:ℝ)/p := sub_pos.mpr hnp
    have hz : (0:ℝ) ^ (aexp + 1) = 0 := by
      rw [Real.zero_rpow]
      dsimp [aexp]
      linarith
    rw [Real.one_rpow, hz]
    dsimp [aexp]
    congr 1
    ring
  have Hball := smooth_ball_segment_bound u hu x R
  -- substitute the names of the two integrands in the elementary ball
  -- Fubini inequality, then perform the scalar integral.
  have Hball' :
      (∫ h : EX n in Metric.closedBall 0 R, ‖u (x+h) - u x‖ ∂volume) ≤
        ∫ t : ℝ in T, G t ∂volume := by
    simpa [G, W, T, B0] using Hball
  calc
    _ ≤ ∫ t : ℝ in T, G t ∂volume := Hball'
    _ ≤ ∫ t : ℝ in T, D * t ^ aexp ∂volume := hmono
    _ = D * (1 / (1 - (n:ℝ)/p)) := hval
end MorreySupport
namespace MorreySupport
-- cancellation of the volume factor in the two-ball average.  Keeping the
-- constant unsimplified (`K⁻¹ * K^(1/q)`) avoids any choice of roots at zero.
lemma normalize_two_ball
    (n : ℕ) {p q : ℝ} (hpq : p.HolderConjugate q)
    {R S K : ℝ} (hR : 0 < R) (hK : 0 < K) :
    (R*S*(K ^ (1/q))* R ^ ((n:ℝ)/q)) * (1 / (1 - (n:ℝ)/p)) +
      ((2*R)*S*(K ^ (1/q))* (2*R) ^ ((n:ℝ)/q)) *
        (1 / (1 - (n:ℝ)/p)) =
      (R ^ n * K) *
        ((S * K ^ (1/q) * K⁻¹ * (1 + 2 * (2:ℝ)^((n:ℝ)/q)) *
              (1 / (1 - (n:ℝ)/p))) * R ^ (1 - (n:ℝ)/p)) := by
  have hcoef : (n:ℝ)/q = (n:ℝ) - (n:ℝ)/p := by
    rw [hpq.conjugate_eq]
    have hp := hpq.lt
    field_simp
  have hR0 : 0 ≤ R := le_of_lt hR
  have h2 : (0:ℝ) ≤ 2 := by norm_num
  have hh : 1 - (n:ℝ)/p + (n:ℝ) = 1 + (n:ℝ)/q := by
    rw [hcoef]
    ring
  -- split the extra factor two and collect like r-powers of the positive radius
  rw [Real.mul_rpow h2 hR0]
  -- turn the natural power into an r-power and combine all R factors.
  rw [← Real.rpow_natCast]
  have hcR : R ^ (1 - (n:ℝ)/p) * R ^ (n:ℝ) =
      R ^ (1 + (n:ℝ)/q) := by
    rw [← Real.rpow_add hR]
    rw [hh]
  have hRone : R ^ (1 + (n:ℝ)/q) = R * R ^ ((n:ℝ)/q) := by
    rw [Real.rpow_add hR, Real.rpow_one]
  -- after these two identities the goal is plain commutative-semiring algebra.
  rw [hRone] at hcR
  have hKc : K⁻¹ * K = (1:ℝ) := by field_simp
  -- expose the product `R^(...) * R^n`
  calc
    (R*S*(K ^ (1/q))* R ^ ((n:ℝ)/q)) * (1 / (1 - (n:ℝ)/p)) +
      ((2*R)*S*(K ^ (1/q))* ((2:ℝ)^((n:ℝ)/q) * R ^ ((n:ℝ)/q))) *
        (1 / (1 - (n:ℝ)/p)) =
        (R * R ^ ((n:ℝ)/q)) *
          (S*K^(1/q) * (1+2*(2:ℝ)^((n:ℝ)/q)) *
            (1 / (1 - (n:ℝ)/p))) := by ring
    _ = _ := by
      -- replace the radius product and cancel K
      rw [← hcR]
      field_simp
end MorreySupport

end
-- END INLINED FILE: Mathlib/Support/sobolev_embedding_morrey_853ace8d32/Endpoint.lean

-- BEGIN INLINED FILE: Mathlib/Support/sobolev_embedding_morrey_853ace8d32/Pointwise.lean
section
open MeasureTheory Set Metric intervalIntegral
open scoped ENNReal NNReal
namespace MorreySupport
-- Same centre ball average trick: two point values can be compared using
-- the ball of radius |x-y| about the first point and the ball of radius
-- 2|x-y| about the second.  The proof is just triangle plus translation.
lemma pair_norm_mul_volume_le_ball
    {n : ℕ} {u : EX n → ℝ} (hu : Continuous u) (x y : EX n) :
    let R : ℝ := ‖x-y‖
    ‖u x-u y‖ * (volume : Measure (EX n)).real
          (Metric.closedBall (0 : EX n) R) ≤
      (∫ h : EX n in Metric.closedBall 0 R,
          ‖u (x+h) - u x‖ ∂volume) +
      (∫ h : EX n in Metric.closedBall 0 (2*R),
          ‖u (y+h) - u y‖ ∂volume) := by
  classical
  dsimp
  let R : ℝ := ‖x-y‖
  let C : Set (EX n) := Metric.closedBall (0 : EX n) R
  let v : EX n := x-y
  let Cy : Set (EX n) := Metric.closedBall v R
  let D : Set (EX n) := Metric.closedBall (0 : EX n) (2*R)
  have hR : 0 ≤ R := norm_nonneg _
  have hC : IsCompact C := ProperSpace.isCompact_closedBall _ _
  -- the translated ball is a subset of the radius 2R ball
  have hsub : Cy ⊆ D := by
    intro z hz
    have hz' : ‖z-v‖ ≤ R := (mem_closedBall_zero_iff.mp (by
      -- translate both sides by v
      -- below use the normed-group description of a ball at v
      -- `dist z v = ‖z-v‖`
      simpa [Cy, mem_closedBall, dist_eq_norm] using hz))
    -- the previous conversion was circuitous; `Cy` is centred at v,
    -- so directly simplify
    have hz'' : ‖z-v‖ ≤ R := by
      have H : dist z v ≤ R := by
        simpa [Cy, mem_closedBall] using hz
      simpa [dist_eq_norm] using H
    have hv : ‖v‖ = R := rfl
    change z ∈ Metric.closedBall (0 : EX n) (2*R)
    have htri : ‖z‖ ≤ ‖z-v‖ + ‖v‖ := by
      calc
        ‖z‖ = ‖(z-v)+v‖ := by congr 1; abel
        _ ≤ ‖z-v‖ + ‖v‖ := norm_add_le _ _
    have : ‖z‖ ≤ 2*R := by
      rw [hv] at htri
      linarith
    simpa [mem_closedBall, dist_eq_norm] using this
  -- translating by v sends C to Cy
  have hpre : (fun h : EX n => v + h) ⁻¹' Cy = C := by
    ext h
    change (v+h) ∈ Metric.closedBall v R ↔
      h ∈ Metric.closedBall (0 : EX n) R
    simp [mem_closedBall, dist_eq_norm]
  let F : EX n → ℝ := fun h => ‖u (x+h) - u x‖
  let Q : EX n → ℝ := fun h => ‖u (y+h) - u y‖
  let F2 : EX n → ℝ := fun h => ‖u (x+h) - u y‖
  have hF : Continuous F :=
    ((hu.comp (continuous_const.add continuous_id)).sub continuous_const).norm
  have hQ : Continuous Q :=
    ((hu.comp (continuous_const.add continuous_id)).sub continuous_const).norm
  have hF2 : Continuous F2 :=
    ((hu.comp (continuous_const.add continuous_id)).sub continuous_const).norm
  have hI : IntegrableOn F C (volume : Measure (EX n)) :=
    ContinuousOn.integrableOn_compact hC hF.continuousOn
  have hI2 : IntegrableOn F2 C (volume : Measure (EX n)) :=
    ContinuousOn.integrableOn_compact hC hF2.continuousOn
  -- triangle integrated over C
  have hconst :
      ‖u x-u y‖ * (volume : Measure (EX n)).real C ≤
        (∫ h : EX n in C, F h ∂volume) +
          (∫ h : EX n in C, F2 h ∂volume) := by
    have hK : IntegrableOn (fun _ : EX n => ‖u x-u y‖) C
        (volume : Measure (EX n)) := by
      exact ContinuousOn.integrableOn_compact hC continuous_const.continuousOn
    have hadd : IntegrableOn (fun z : EX n => F z + F2 z) C
        (volume : Measure (EX n)) := hI.add hI2
    calc
      ‖u x-u y‖ * (volume : Measure (EX n)).real C =
          ∫ h : EX n in C, (‖u x-u y‖ : ℝ) ∂volume := by
            rw [MeasureTheory.setIntegral_const]
            simp
            ring
      _ ≤ ∫ h : EX n in C, (F h + F2 h) ∂volume := by
        apply MeasureTheory.setIntegral_mono_on hK hadd
          (measurableSet_closedBall)
        intro h hh
        dsimp [F, F2]
        calc
          ‖u x - u y‖ = ‖(u x - u (x+h)) + (u (x+h) - u y)‖ := by ring
          _ ≤ ‖u x - u (x+h)‖ + ‖u (x+h) - u y‖ := norm_add_le _ _
          _ = ‖u (x+h) - u x‖ + ‖u (x+h)-u y‖ := by
             rw [norm_sub_rev]
      _ = (∫ h : EX n in C, F h ∂volume) +
            (∫ h : EX n in C, F2 h ∂volume) := by
        rw [MeasureTheory.integral_add hI hI2]
  have htrans : (∫ h : EX n in C, F2 h ∂volume) =
      ∫ z : EX n in Cy, Q z ∂volume := by
    have hmp := (MeasureTheory.measurePreserving_add_left
      (volume : Measure (EX n)) v)
    have hemb : MeasurableEmbedding (fun z : EX n => v + z) :=
      (Homeomorph.addLeft v).measurableEmbedding
    have hxid (h : EX n) : Q (v+h) = F2 h := by
      dsimp [Q, F2, v]
      congr 2
      abel
    have HE := hmp.setIntegral_preimage_emb hemb Q Cy
    rw [hpre] at HE
    -- simplify y + (v+h) = x+h
    simpa [hxid] using HE -- orientation?
  have hmonoQ : (∫ z : EX n in Cy, Q z ∂volume) ≤
      ∫ z : EX n in D, Q z ∂volume := by
    have hD : IsCompact D := ProperSpace.isCompact_closedBall _ _
    have hIQ : IntegrableOn Q D (volume : Measure (EX n)) :=
      ContinuousOn.integrableOn_compact hD hQ.continuousOn
    apply MeasureTheory.setIntegral_mono_set hIQ
      (by
        -- nonnegative on D
        filter_upwards [] with z
        change 0 ≤ Q z
        exact norm_nonneg _)
    filter_upwards [] with z hz
    exact hsub hz
  change ‖u x-u y‖ * (volume : Measure (EX n)).real C ≤
      (∫ h : EX n in C, F h ∂volume) +
        (∫ h : EX n in D, Q h ∂volume)
  exact hconst.trans (add_le_add_right (htrans.le.trans hmonoQ) _)
end MorreySupport
namespace MorreySupport
open MeasureTheory Metric Set
lemma smooth_pair_volume_mul_Lp_bound
    {n : ℕ} (u : EX n → ℝ) (hu : ContDiff ℝ (1:ℕ∞) u)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (hLp : ∀ i : Fin n,
      MemLp (fun z : EX n => fderiv ℝ u z (EuclideanSpace.single i (1:ℝ)))
        (ENNReal.ofReal p) (volume : Measure (EX n)))
    (hnp : (n:ℝ)/p < 1) (x y : EX n) :
    let R : ℝ := ‖x-y‖
    ‖u x-u y‖ * (volume : Measure (EX n)).real
          (Metric.closedBall (0 : EX n) R) ≤
      ((R * (∑ i : Fin n,
          (∫ z : EX n,
            ‖fderiv ℝ u z (EuclideanSpace.single i (1:ℝ))‖ ^ p ∂volume) ^ (1/p)) *
          ((volume : Measure (EX n)).real (Metric.ball (0 : EX n) 1)) ^ (1/q) *
          R ^ ((n:ℝ)/q))) * (1 / (1 - (n:ℝ)/p)) +
      (((2*R) * (∑ i : Fin n,
          (∫ z : EX n,
            ‖fderiv ℝ u z (EuclideanSpace.single i (1:ℝ))‖ ^ p ∂volume) ^ (1/p)) *
          ((volume : Measure (EX n)).real (Metric.ball (0 : EX n) 1)) ^ (1/q) *
          (2*R) ^ ((n:ℝ)/q))) * (1 / (1 - (n:ℝ)/p)) := by
  classical
  dsimp
  let R : ℝ := ‖x-y‖
  have hR : 0 ≤ R := norm_nonneg _
  have H0 := pair_norm_mul_volume_le_ball hu.continuous x y
  change ‖u x-u y‖ * (volume : Measure (EX n)).real
          (Metric.closedBall (0 : EX n) R) ≤ _
  calc
    ‖u x-u y‖ * (volume : Measure (EX n)).real
          (Metric.closedBall (0 : EX n) R) ≤
      (∫ h : EX n in Metric.closedBall 0 R,
          ‖u (x+h) - u x‖ ∂volume) +
      (∫ h : EX n in Metric.closedBall 0 (2*R),
          ‖u (y+h) - u y‖ ∂volume) := H0
    _ ≤ _ := add_le_add
      (smooth_ball_segment_Lp_bound u hu hpq hLp hnp x hR)
      (smooth_ball_segment_Lp_bound u hu hpq hLp hnp y
        (mul_nonneg (by norm_num) hR))
end MorreySupport
namespace MorreySupport
open MeasureTheory Metric Set
lemma smooth_pair_Lp_holder
    {n : ℕ} (u : EX n → ℝ) (hu : ContDiff ℝ (1:ℕ∞) u)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (hLp : ∀ i : Fin n,
      MemLp (fun z : EX n => fderiv ℝ u z (EuclideanSpace.single i (1:ℝ)))
        (ENNReal.ofReal p) (volume : Measure (EX n)))
    (hnp : (n:ℝ)/p < 1) (x y : EX n) :
    ‖u x-u y‖ ≤
      let S : ℝ := ∑ i : Fin n,
          (∫ z : EX n,
            ‖fderiv ℝ u z (EuclideanSpace.single i (1:ℝ))‖ ^ p ∂volume) ^ (1/p)
      let K : ℝ := (volume : Measure (EX n)).real
                         (Metric.ball (0 : EX n) 1)
      (S * K ^ (1/q) * K⁻¹ * (1 + 2 * (2:ℝ)^((n:ℝ)/q)) *
          (1 / (1 - (n:ℝ)/p))) * ‖x-y‖ ^ (1 - (n:ℝ)/p) := by
  classical
  let R : ℝ := ‖x-y‖
  let S : ℝ := ∑ i : Fin n,
          (∫ z : EX n,
            ‖fderiv ℝ u z (EuclideanSpace.single i (1:ℝ))‖ ^ p ∂volume) ^ (1/p)
  let K : ℝ := (volume : Measure (EX n)).real
                         (Metric.ball (0 : EX n) 1)
  change ‖u x-u y‖ ≤
      (S * K ^ (1/q) * K⁻¹ * (1 + 2 * (2:ℝ)^((n:ℝ)/q)) *
          (1 / (1 - (n:ℝ)/p))) * R ^ (1 - (n:ℝ)/p)
  have hK : 0 < K := by
    dsimp [K]
    rw [MeasureTheory.measureReal_def]
    apply ENNReal.toReal_pos
    · exact ne_of_gt (Metric.measure_ball_pos
          (volume : Measure (EX n)) (0 : EX n) (by norm_num))
    · exact (measure_ball_lt_top).ne
  by_cases hR0 : R = 0
  · have hxy : x = y := by
      have : ‖x-y‖ = 0 := hR0
      simpa using (sub_eq_zero.mp (norm_eq_zero.mp this))
    subst y
    have hz : 1 - (n:ℝ)/p ≠ 0 := ne_of_gt (sub_pos.mpr hnp)
    simp [R, Real.zero_rpow hz]
  have hR : 0 < R := (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hR0))
  have H := smooth_pair_volume_mul_Lp_bound u hu hpq hLp hnp x y
  change ‖u x-u y‖ * (volume : Measure (EX n)).real
          (Metric.closedBall (0 : EX n) R) ≤
      (R*S*K^(1/q)*R^((n:ℝ)/q)) * (1/(1-(n:ℝ)/p)) +
      ((2*R)*S*K^(1/q)*(2*R)^((n:ℝ)/q)) * (1/(1-(n:ℝ)/p)) at H
  rw [real_volume_closedBall_zero R (le_of_lt hR)] at H
  change ‖u x-u y‖ * (R^n * K) ≤ _ at H
  have HH := normalize_two_ball n hpq hR hK (S := S)
  rw [HH] at H
  have hc : 0 < R^n * K := mul_pos (by positivity) hK
  nlinarith
end MorreySupport

end
-- END INLINED FILE: Mathlib/Support/sobolev_embedding_morrey_853ace8d32/Pointwise.lean

-- BEGIN INLINED FILE: Mathlib/Support/sobolev_embedding_morrey_853ace8d32/Weak.lean
section
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal Topology
namespace MorreySupport
/-- Nonnegative bump viewed as a NNReal density.  This lets us apply Jensen to
its normalized integral rather than losing powers of the radius. -/
noncomputable def bumpNN {n : ℕ} (φ : ContDiffBump (0 : EX n)) : EX n → ℝ≥0 :=
  fun x => ⟨φ.normed volume x, φ.nonneg_normed x⟩
lemma bumpNN_coe {n : ℕ} (φ : ContDiffBump (0 : EX n)) (x : EX n) :
    (bumpNN φ x : ℝ) = φ.normed volume x := rfl
lemma bumpNN_meas {n : ℕ} (φ : ContDiffBump (0 : EX n)) :
    Measurable (bumpNN φ) := by
  have hc : Continuous (fun x : EX n => φ.normed volume x) := φ.continuous_normed
  change Measurable (fun x : EX n => (⟨φ.normed volume x, φ.nonneg_normed x⟩ : ℝ≥0))
  exact (Continuous.subtype_mk hc (fun x => φ.nonneg_normed x)).measurable

/-- The normalized bump density is a probability measure. -/
lemma bump_prob {n : ℕ} (φ : ContDiffBump (0 : EX n)) :
    IsProbabilityMeasure
      ((volume : Measure (EX n)).withDensity (fun x => (bumpNN φ x : ℝ≥0∞))) := by
  rw [isProbabilityMeasure_iff, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  have hi : Integrable (fun x : EX n => (bumpNN φ x : ℝ))
      (volume : Measure (EX n)) := by
    have h := (φ.integrable_normed (μ := (volume : Measure (EX n))))
    convert h using 1 <;> simp [bumpNN_coe]
  rw [lintegral_coe_eq_integral (bumpNN φ) hi]
  have he : (∫ x : EX n, (bumpNN φ x : ℝ) ∂(volume : Measure (EX n))) = 1 := by
    have h := (φ.integral_normed (μ := (volume : Measure (EX n))))
    convert h using 1 <;> simp [bumpNN_coe]
  rw [he, ENNReal.ofReal_one]

lemma norm_integral_bump_rpow_le {n : ℕ} (φ : ContDiffBump (0 : EX n))
    {v : EX n → ℝ} {p : ℝ} (hp : 1 ≤ p)
    (hv : Integrable v
      ((volume : Measure (EX n)).withDensity (fun x => (bumpNN φ x : ℝ≥0∞))))
    (hvp : Integrable (fun x => ‖v x‖ ^ p)
      ((volume : Measure (EX n)).withDensity (fun x => (bumpNN φ x : ℝ≥0∞)))) :
    ‖∫ x : EX n, (φ.normed volume x) * v x ∂(volume : Measure (EX n))‖ ^ p ≤
      ∫ x : EX n, (φ.normed volume x) * (‖v x‖ ^ p) ∂(volume : Measure (EX n)) := by
  let μφ : Measure (EX n) :=
    (volume : Measure (EX n)).withDensity (fun x => (bumpNN φ x : ℝ≥0∞))
  letI : IsProbabilityMeasure μφ := bump_prob φ
  have hn : ‖∫ x, v x ∂μφ‖ ≤ ∫ x, ‖v x‖ ∂μφ :=
    norm_integral_le_integral_norm v
  have hp0 : 0 ≤ p := (by linarith : (0:ℝ) ≤ p)
  have hpow : ‖∫ x, v x ∂μφ‖ ^ p ≤ (∫ x, ‖v x‖ ∂μφ) ^ p :=
    Real.rpow_le_rpow (norm_nonneg _) hn hp0
  have hw : Integrable (fun x => ‖v x‖) μφ := hv.norm
  have hwcomp : Integrable ((fun t : ℝ => t ^ p) ∘ (fun x => ‖v x‖)) μφ := by
    simpa [Function.comp_def] using hvp
  have hj : (∫ x, ‖v x‖ ∂μφ) ^ p ≤ ∫ x, (‖v x‖)^p ∂μφ := by
    simpa using ((convexOn_rpow hp).map_integral_le
      (Real.continuous_rpow_const hp0).continuousOn isClosed_Ici
      (by
        filter_upwards [] with x
        exact (norm_nonneg _ : (0:ℝ) ≤ ‖v x‖))
      hw hwcomp)
  have HH := hpow.trans hj
  -- express the probability integrals by their densities
  change
    ‖∫ x : EX n, v x ∂((volume : Measure (EX n)).withDensity
      (fun x => (bumpNN φ x : ℝ≥0∞)))‖ ^ p ≤
      ∫ x : EX n, ‖v x‖ ^ p ∂((volume : Measure (EX n)).withDensity
      (fun x => (bumpNN φ x : ℝ≥0∞))) at HH
  rw [integral_withDensity_eq_integral_smul (bumpNN_meas φ) v,
      integral_withDensity_eq_integral_smul (bumpNN_meas φ)
        (fun x : EX n => ‖v x‖ ^ p)] at HH
  simpa [bumpNN_coe, NNReal.smul_def, mul_comm] using HH

lemma translated_integrable_bump {n : ℕ} (φ : ContDiffBump (0 : EX n))
    {v : EX n → ℝ} {p : ℝ} (hp : 1 ≤ p) (hv : MemLp v (ENNReal.ofReal p)
      (volume : Measure (EX n))) (x : EX n) :
    Integrable (fun y : EX n => v (x-y))
      ((volume : Measure (EX n)).withDensity (fun y => (bumpNN φ y : ℝ≥0∞))) ∧
    Integrable (fun y : EX n => ‖v (x-y)‖ ^ p)
      ((volume : Measure (EX n)).withDensity (fun y => (bumpNN φ y : ℝ≥0∞))) := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hmem : MemLp (fun y : EX n => v (x-y)) (ENNReal.ofReal p)
      (volume : Measure (EX n)) := by
    have H := hv.comp_measurePreserving
      (Measure.measurePreserving_sub_left (volume : Measure (EX n)) x)
    simpa [Function.comp_def] using H
  have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p :=
    ENNReal.one_le_ofReal.mpr hp
  have hloc : LocallyIntegrable (fun y : EX n => v (x-y))
      (volume : Measure (EX n)) := hmem.locallyIntegrable hpE
  have hglobalp : Integrable (fun y : EX n => ‖v (x-y)‖ ^ p)
      (volume : Measure (EX n)) := by
    have T := hmem.integrable_norm_rpow (by simpa using hp0) (by simp)
    simpa [ENNReal.toReal_ofReal hp0.le] using T
  constructor
  · rw [integrable_withDensity_iff_integrable_smul (bumpNN_meas φ)]
    have H := hloc.integrable_smul_left_of_hasCompactSupport
      (φ.continuous_normed) (φ.hasCompactSupport_normed (μ := (volume : Measure (EX n))))
    simpa [NNReal.smul_def, bumpNN_coe] using H
  · rw [integrable_withDensity_iff_integrable_smul (bumpNN_meas φ)]
    have H := (hglobalp.locallyIntegrable).integrable_smul_left_of_hasCompactSupport
      (φ.continuous_normed) (φ.hasCompactSupport_normed (μ := (volume : Measure (EX n))))
    simpa [NNReal.smul_def, bumpNN_coe] using H
lemma convolution_mul_bump_eq {n : ℕ} (φ : ContDiffBump (0 : EX n))
    (v : EX n → ℝ) (x : EX n) :
    (MeasureTheory.convolution v (φ.normed volume)
      (ContinuousLinearMap.mul ℝ ℝ) volume) x =
      ∫ y : EX n, (φ.normed volume y) * v (x-y) ∂(volume : Measure (EX n)) := by
  have hmp := (Measure.measurePreserving_sub_left (volume : Measure (EX n)) x)
  have hemb : MeasurableEmbedding (fun y : EX n => x-y) :=
    (Homeomorph.subLeft x).measurableEmbedding
  have H := hmp.integral_comp hemb
    (fun a : EX n => v a * (φ.normed volume (x-a)))
  -- substituting `a=x-y` turns the kernel argument into y
  rw [MeasureTheory.convolution_def]
  simp only [ContinuousLinearMap.mul_apply']
  -- integral_comp states left(composed)=right
  rw [← H]
  congr 1
  funext y
  have he : x - (x - y) = y := by abel
  rw [he]
  ring
lemma convolution_mul_bump_point_rpow {n : ℕ} (φ : ContDiffBump (0 : EX n))
    {v : EX n → ℝ} {p : ℝ} (hp : 1 ≤ p)
    (hv : MemLp v (ENNReal.ofReal p) (volume : Measure (EX n)))
    (x : EX n) :
    ‖(MeasureTheory.convolution v (φ.normed volume)
      (ContinuousLinearMap.mul ℝ ℝ) volume) x‖ ^ p ≤
      ∫ y : EX n, (φ.normed volume y) * (‖v (x-y)‖ ^ p)
        ∂(volume : Measure (EX n)) := by
  rw [convolution_mul_bump_eq φ v]
  have HI := translated_integrable_bump φ hp hv x
  exact norm_integral_bump_rpow_le φ hp HI.1 HI.2
lemma bump_rpow_kernel_integrable_prod {n : ℕ} (φ : ContDiffBump (0 : EX n))
    {v : EX n → ℝ} {p : ℝ} (hp : 1 ≤ p)
    (hv : MemLp v (ENNReal.ofReal p) (volume : Measure (EX n))) :
    Integrable (fun z : EX n × EX n =>
        (φ.normed volume z.2) * (‖v (z.1-z.2)‖ ^ p))
       ((volume : Measure (EX n)).prod (volume : Measure (EX n))) := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  let w : EX n → ℝ := fun z => ‖v z‖ ^ p
  have hw : Integrable w (volume : Measure (EX n)) := by
    have T := hv.integrable_norm_rpow (by simpa using hp0) (by simp)
    simpa [w, ENNReal.toReal_ofReal hp0.le] using T
  have hcomp : AEStronglyMeasurable
      (fun z : EX n × EX n => w (z.1-z.2))
      ((volume : Measure (EX n)).prod (volume : Measure (EX n))) := by
    have H := hw.aestronglyMeasurable.comp_quasiMeasurePreserving
      (MeasureTheory.quasiMeasurePreserving_sub_of_right_invariant
        (volume : Measure (EX n)) (volume : Measure (EX n)))
    simpa [Function.comp_def] using H
  have hb : AEStronglyMeasurable
      (fun z : EX n × EX n => φ.normed volume z.2)
      ((volume : Measure (EX n)).prod (volume : Measure (EX n))) :=
    (φ.continuous_normed.comp continuous_snd).aestronglyMeasurable
  have HF : AEStronglyMeasurable
      (fun z : EX n × EX n => (φ.normed volume z.2) * w (z.1-z.2))
      ((volume : Measure (EX n)).prod (volume : Measure (EX n))) := hb.mul hcomp
  change Integrable (fun z : EX n × EX n => (φ.normed volume z.2) * w (z.1-z.2)) _
  rw [integrable_prod_iff' HF]
  constructor
  · filter_upwards [] with y
    have hi : Integrable (fun x : EX n => w (x-y)) (volume : Measure (EX n)) := by
      have hemb : MeasurableEmbedding (fun x : EX n => x + (-y)) :=
        (Homeomorph.addRight (-y)).measurableEmbedding
      have hmp := MeasureTheory.measurePreserving_add_right
        (volume : Measure (EX n)) (-y)
      have H := (hmp.integrable_comp_emb hemb (g:=w)).2 hw
      simpa [Function.comp_def, sub_eq_add_neg] using H
    exact hi.const_mul _
  · have heq : (fun y : EX n =>
          ∫ x : EX n, ‖(φ.normed volume y) * w (x-y)‖
                ∂(volume : Measure (EX n))) =
          (fun y : EX n => (φ.normed volume y) *
              (∫ x : EX n, w x ∂(volume : Measure (EX n)))) := by
        funext y
        have hh : (fun x : EX n => ‖(φ.normed volume y) * w (x-y)‖) =
            (fun x : EX n => (φ.normed volume y) * w (x-y)) := by
          funext x
          rw [Real.norm_of_nonneg (mul_nonneg (φ.nonneg_normed y)
            (Real.rpow_nonneg (norm_nonneg _) _))]
        rw [hh, integral_const_mul]
        have hemb : MeasurableEmbedding (fun x : EX n => x + (-y)) :=
          (Homeomorph.addRight (-y)).measurableEmbedding
        have hmp := MeasureTheory.measurePreserving_add_right
          (volume : Measure (EX n)) (-y)
        have H := hmp.integral_comp hemb w
        simpa [Function.comp_def, sub_eq_add_neg] using
          congrArg (fun t : ℝ => (φ.normed volume y) * t) H
    rw [heq]
    exact (φ.integrable_normed).mul_const _
lemma integral_bump_translate_rpow {n : ℕ} (φ : ContDiffBump (0 : EX n))
    {v : EX n → ℝ} {p : ℝ} (hp : 1 ≤ p)
    (hv : MemLp v (ENNReal.ofReal p) (volume : Measure (EX n))) :
    Integrable (fun x : EX n => ∫ y : EX n,
       (φ.normed volume y) * (‖v (x-y)‖ ^ p) ∂(volume : Measure (EX n)))
       (volume : Measure (EX n)) ∧
    (∫ x : EX n, ∫ y : EX n,
       (φ.normed volume y) * (‖v (x-y)‖ ^ p) ∂(volume : Measure (EX n))
       ∂(volume : Measure (EX n))) =
       ∫ x : EX n, ‖v x‖ ^ p ∂(volume : Measure (EX n)) := by
  let w : EX n → ℝ := fun x => ‖v x‖ ^ p
  have HF := bump_rpow_kernel_integrable_prod φ hp hv
  change Integrable (fun z : EX n × EX n => (φ.normed volume z.2) * w (z.1-z.2)) _ at HF
  constructor
  · exact HF.integral_prod_left
  · have HS := integral_integral_swap (μ:=(volume : Measure (EX n))) (ν:=(volume : Measure (EX n))) (f:= fun x y : EX n => (φ.normed volume y) * w (x-y)) HF
    change (∫ x : EX n, ∫ y : EX n, (φ.normed volume y) * w (x-y)
        ∂(volume : Measure (EX n)) ∂(volume : Measure (EX n))) = _
    change (∫ x : EX n, ∫ y : EX n, (φ.normed volume y) * w (x-y)
        ∂(volume : Measure (EX n)) ∂(volume : Measure (EX n))) =
      (∫ y : EX n, ∫ x : EX n, (φ.normed volume y) * w (x-y)
        ∂(volume : Measure (EX n)) ∂(volume : Measure (EX n))) at HS
    rw [HS]
    have heq : (fun y : EX n =>
        ∫ x : EX n, (φ.normed volume y) * w (x-y)
            ∂(volume : Measure (EX n))) =
        (fun y : EX n => (φ.normed volume y) *
             (∫ z : EX n, w z ∂(volume : Measure (EX n)))) := by
      funext y
      rw [integral_const_mul]
      have hmp := MeasureTheory.measurePreserving_add_right
        (volume : Measure (EX n)) (-y)
      have hemb : MeasurableEmbedding (fun x : EX n => x + (-y)) :=
        (Homeomorph.addRight (-y)).measurableEmbedding
      have H := hmp.integral_comp hemb w
      simpa [Function.comp_def, sub_eq_add_neg] using
        congrArg (fun t : ℝ => (φ.normed volume y) * t) H
    simp_rw [heq]
    rw [integral_mul_const (∫ z : EX n, w z ∂(volume : Measure (EX n))) (fun y : EX n => φ.normed volume y)]
    rw [φ.integral_normed]
    simp [w]
/-- Normalized convolution is a contraction for the real `p`-mass.  In particular
all smooth derivatives obtained by convolving weak derivatives have a bound
independent of the support radius of the bump. -/
lemma convolution_bump_rpow_le {n : ℕ} (φ : ContDiffBump (0 : EX n))
    {v : EX n → ℝ} {p : ℝ} (hp : 1 ≤ p)
    (hv : MemLp v (ENNReal.ofReal p) (volume : Measure (EX n))) :
    Integrable (fun x : EX n =>
      ‖(MeasureTheory.convolution v (φ.normed volume)
        (ContinuousLinearMap.mul ℝ ℝ) volume) x‖ ^ p)
       (volume : Measure (EX n)) ∧
    (∫ x : EX n, ‖(MeasureTheory.convolution v (φ.normed volume)
        (ContinuousLinearMap.mul ℝ ℝ) volume) x‖ ^ p
          ∂(volume : Measure (EX n))) ≤
      ∫ x : EX n, ‖v x‖ ^ p ∂(volume : Measure (EX n)) := by
  let U : EX n → ℝ := MeasureTheory.convolution v (φ.normed volume)
        (ContinuousLinearMap.mul ℝ ℝ) volume
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hloc := hv.locallyIntegrable (ENNReal.one_le_ofReal.mpr hp)
  have hUs : ContDiff ℝ (1 : ℕ∞) U :=
    φ.hasCompactSupport_normed.contDiff_convolution_right
        (ContinuousLinearMap.mul ℝ ℝ) hloc (φ.contDiff_normed)
  let A : EX n → ℝ := fun x => ∫ y : EX n,
       (φ.normed volume y) * (‖v (x-y)‖ ^ p) ∂(volume : Measure (EX n))
  have hA := (integral_bump_translate_rpow φ hp hv).1
  change Integrable A (volume : Measure (EX n)) at hA
  have hBcont : Continuous (fun x : EX n => ‖U x‖ ^ p) :=
    hUs.continuous.norm.rpow_const (fun _ => Or.inr hp0.le)
  have hle (x : EX n) : ‖U x‖ ^ p ≤ A x :=
    convolution_mul_bump_point_rpow φ hp hv x
  have hB : Integrable (fun x : EX n => ‖U x‖ ^ p)
        (volume : Measure (EX n)) := by
    apply Integrable.mono' hA hBcont.aestronglyMeasurable
    filter_upwards [] with x
    have hn : 0 ≤ ‖U x‖ ^ p := Real.rpow_nonneg (norm_nonneg _) _
    rw [Real.norm_of_nonneg hn]
    exact hle x
  constructor
  · exact hB
  · change (∫ x : EX n, ‖U x‖ ^ p ∂(volume : Measure (EX n))) ≤ _
    calc
      (∫ x : EX n, ‖U x‖ ^ p ∂(volume : Measure (EX n))) ≤
          ∫ x : EX n, A x ∂(volume : Measure (EX n)) :=
        integral_mono_ae hB hA (Filter.Eventually.of_forall hle)
      _ = _ := (integral_bump_translate_rpow φ hp hv).2
lemma convolution_bump_memLp {n : ℕ} (φ : ContDiffBump (0 : EX n))
    {v : EX n → ℝ} {p : ℝ} (hp : 1 ≤ p)
    (hv : MemLp v (ENNReal.ofReal p) (volume : Measure (EX n))) :
    MemLp (MeasureTheory.convolution v (φ.normed volume)
        (ContinuousLinearMap.mul ℝ ℝ) volume)
      (ENNReal.ofReal p) (volume : Measure (EX n)) := by
  let U : EX n → ℝ := MeasureTheory.convolution v (φ.normed volume)
        (ContinuousLinearMap.mul ℝ ℝ) volume
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hloc := hv.locallyIntegrable (ENNReal.one_le_ofReal.mpr hp)
  have hUs : ContDiff ℝ (1 : ℕ∞) U :=
    φ.hasCompactSupport_normed.contDiff_convolution_right
        (ContinuousLinearMap.mul ℝ ℝ) hloc (φ.contDiff_normed)
  apply (integrable_norm_rpow_iff hUs.continuous.aestronglyMeasurable
       (by simpa using hp0) (by simp)).1
  change Integrable (fun x : EX n => ‖U x‖ ^ (ENNReal.ofReal p).toReal) _
  simpa [ENNReal.toReal_ofReal hp0.le] using (convolution_bump_rpow_le φ hp hv).1
end MorreySupport

end
-- END INLINED FILE: Mathlib/Support/sobolev_embedding_morrey_853ace8d32/Weak.lean

-- BEGIN INLINED FILE: Mathlib/Support/sobolev_embedding_morrey_853ace8d32/Limit.lean
section
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal Topology
namespace MorreySupport
abbrev ET (n:ℕ) := EuclideanSpace ℝ (Fin n)
lemma holder_nndist_intro {X Y:Type*} [PseudoMetricSpace X]
 [PseudoMetricSpace Y] {C t:NNReal} {F:X→Y}
 (h: ∀ x y, nndist (F x) (F y) ≤ C * nndist x y ^ (t:ℝ)) :
 HolderWith C t F := by
  intro x y
  have hc : (↑(nndist (F x) (F y)) : ℝ≥0∞) ≤
      ↑(C * (nndist x y) ^ (t : ℝ)) := ENNReal.coe_le_coe.mpr (h x y)
  rw [edist_nndist, edist_nndist]
  calc
    (↑(nndist (F x) (F y)) : ℝ≥0∞) ≤
        ↑(C * (nndist x y) ^ (t : ℝ)) := hc
    _ = (C : ℝ≥0∞) * (↑(nndist x y) : ℝ≥0∞) ^ (t : ℝ) := by
      rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg]
      exact NNReal.coe_nonneg _
    _ = _ := by rfl

/-- Equi-Hölder continuous functions which converge almost everywhere have a
canonical continuous representative of the limit.  Moreover the convergence
is pointwise everywhere.  This is the elementary dense-extension part of the
weak Morrey argument. -/
lemma holder_ae_limit {n : ℕ} {F : ℕ → ET n → ℝ} {v : ET n → ℝ}
    {C t : NNReal} (ht : 0 < t)
    (hF : ∀ j, HolderWith C t (F j))
    (hae : ∀ᵐ x ∂(volume : Measure (ET n)),
       Tendsto (fun j => F j x) atTop (𝓝 (v x))) :
    ∃ G : ET n → ℝ,
      v =ᵐ[volume] G ∧ HolderWith C t G ∧
      (∀ x, Tendsto (fun j => F j x) atTop (𝓝 (G x))) := by
  classical
  let s : Set (ET n) := {x | Tendsto (fun j => F j x) atTop (𝓝 (v x))}
  have hs : Dense s := (volume : Measure (ET n)).dense_of_ae hae
  let f0 : s → ℝ := fun x => v x.1
  have hf0 : HolderWith C t f0 := by
    apply holder_nndist_intro
    intro x y
    have hx := x.2
    have hy := y.2
    change Tendsto (fun j => F j x.1) atTop (𝓝 (v x.1)) at hx
    change Tendsto (fun j => F j y.1) atTop (𝓝 (v y.1)) at hy
    have hl := hx.nndist hy
    apply le_of_tendsto hl
    exact Filter.Eventually.of_forall (fun j => hF j |>.nndist_le x.1 y.1)
  have hf0u : UniformContinuous f0 := hf0.uniformContinuous ht
  let G : ET n → ℝ := hs.extend f0
  have hGu : UniformContinuous G := hs.uniformContinuous_extend hf0u
  have hGcont : Continuous G := hGu.continuous
  have hEq (z : s) : G z = v z.1 := by
    exact hs.extend_of_ind hf0u z
  have hpt : ∀ x : ET n, Tendsto (fun j => F j x) atTop (𝓝 (G x)) := by
    intro x
    -- Compare at a nearby point of the full-measure dense set.  The same
    -- Hölder modulus works for every term of the sequence.
    rw [Metric.tendsto_atTop]
    intro ε hε
    -- choose a radius where the common Hölder modulus is < ε/3
    let δ : ℝ := (ε / (4 * ((C:ℝ) + 1))) ^ ((t:ℝ)⁻¹)
    have hden : 0 < ε / (4 * ((C:ℝ) + 1)) := by positivity
    have htR : 0 < (t:ℝ) := by exact_mod_cast ht
    have hδ : 0 < δ := by dsimp [δ]; positivity
    -- also use continuity of the extension at x
    have hgc : Tendsto G (𝓝 x) (𝓝 (G x)) := hGcont.continuousAt
    rcases (Metric.tendsto_nhds_nhds.mp hgc) (ε/4) (by linarith)
      with ⟨δg, hδg, hgg⟩
    have hbnon : (Metric.ball x (min δ δg)).Nonempty :=
      ⟨x, by simp [hδ, hδg]⟩
    rcases hs.exists_mem_open (Metric.isOpen_ball) hbnon with ⟨z, hz, hzx⟩
    have hzx' : dist z x < δ :=
      lt_of_lt_of_le (mem_ball.mp hzx) (min_le_left _ _)
    have hzxg : dist z x < δg :=
      lt_of_lt_of_le (mem_ball.mp hzx) (min_le_right _ _)
    have hsmall : (C:ℝ) * (dist z x) ^ (t:ℝ) < ε/4 := by
      have hdist : (dist z x) ^ (t:ℝ) < ε / (4*((C:ℝ)+1)) := by
        have := Real.rpow_lt_rpow (dist_nonneg) hzx' (by exact_mod_cast ht)
        -- δ^t is the chosen radius
        have heq : δ ^ (t:ℝ) = ε / (4*((C:ℝ)+1)) := by
          dsimp [δ]
          rw [← Real.rpow_mul (le_of_lt hden)]
          have : ((t:ℝ)⁻¹ * t) = 1 := by field_simp
          rw [this, Real.rpow_one]
        exact lt_of_lt_of_le this (le_of_eq heq)
      calc
        (C:ℝ) * (dist z x) ^ (t:ℝ)
            ≤ ((C:ℝ)+1) * (dist z x) ^ (t:ℝ) := by
                exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (dist_nonneg) _)
        _ < ((C:ℝ)+1) * (ε / (4*((C:ℝ)+1))) := by
                have : 0 < (C:ℝ)+1 := by positivity
                exact (mul_lt_mul_of_pos_left hdist this)
        _ = ε/4 := by field_simp
    have hterm (j : ℕ) : dist (F j x) (F j z) < ε/4 := by
      have hh := (hF j).nndist_le x z
      have hhR : dist (F j x) (F j z) ≤
          (C:ℝ) * (dist x z) ^ (t:ℝ) := by
        exact_mod_cast hh
      have he : dist x z = dist z x := dist_comm _ _
      rw [he] at hhR
      exact lt_of_le_of_lt hhR hsmall
    have hzg : dist (G z) (G x) < ε/4 := hgg hzxg
    have hzl : Tendsto (fun j => F j z) atTop (𝓝 (v z)) := hz
    change Tendsto (fun j => F j z) atTop (𝓝 (v z)) at hzl
    have heqz : G z = v z := hEq ⟨z,hz⟩
    have hev : ∀ᶠ j in atTop, dist (F j z) (v z) < ε/4 :=
      (Metric.tendsto_nhds.mp hzl) (ε/4) (by linarith)
    rcases (eventually_atTop.1 hev) with ⟨N,hN⟩
    refine ⟨N, ?_⟩
    intro j hj
    have hjz := hN j hj
    have htri : dist (F j x) (G x) ≤
        dist (F j x) (F j z) + dist (F j z) (v z) + dist (G z) (G x) := by
      calc
        dist (F j x) (G x) ≤ dist (F j x) (F j z) + dist (F j z) (G x) :=
          dist_triangle _ _ _
        _ ≤ dist (F j x) (F j z) +
              (dist (F j z) (v z) + dist (v z) (G x)) := by
          gcongr
          exact dist_triangle _ _ _
        _ = _ := by rw [← heqz]; ring
    linarith [hterm j, hjz, hzg]
  have hGhold : HolderWith C t G := by
    apply holder_nndist_intro
    intro x y
    have hl := (hpt x).nndist (hpt y)
    apply le_of_tendsto hl
    exact Filter.Eventually.of_forall (fun j => hF j |>.nndist_le x y)
  refine ⟨G, ?_, hGhold, hpt⟩
  filter_upwards [hae] with x hx
  have hx' : x ∈ s := hx
  have := hEq ⟨x, hx'⟩
  exact this.symm

/-- On a compact set, a pointwise limit of functions with a common Hölder
modulus is uniform.  We state this separately since it is also used for the
coordinate derivative array. -/
lemma holder_tendstoUniformlyOn_compact {X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {F : ℕ → X → Y} {G : X → Y} {C t : NNReal} (ht : 0 < t)
    (hF : ∀ j, HolderWith C t (F j)) (hG : HolderWith C t G)
    (hpt : ∀ x, Tendsto (fun j => F j x) atTop (𝓝 (G x)))
    {K : Set X} (hK : IsCompact K) :
    TendstoUniformlyOn F G atTop K := by
  classical
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- a uniform radius for all members of the family
  let δ : ℝ := (ε / (4 * ((C:ℝ)+1))) ^ ((t:ℝ)⁻¹)
  have hden : 0 < ε / (4*((C:ℝ)+1)) := by positivity
  have htR : 0 < (t:ℝ) := by exact_mod_cast ht
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall : ∀ {x y:X}, dist x y < δ →
      (C:ℝ) * (dist x y)^(t:ℝ) < ε/4 := by
    intro x y hxy
    have hpow : (dist x y)^(t:ℝ) < ε / (4*((C:ℝ)+1)) := by
      have HH := Real.rpow_lt_rpow (dist_nonneg) hxy (by exact_mod_cast ht)
      have heq : δ^(t:ℝ) = ε / (4*((C:ℝ)+1)) := by
        dsimp [δ]
        rw [← Real.rpow_mul (le_of_lt hden)]
        have : ((t:ℝ)⁻¹ * t) = 1 := by field_simp
        rw [this, Real.rpow_one]
      exact lt_of_lt_of_le HH (le_of_eq heq)
    calc
      (C:ℝ) * (dist x y)^(t:ℝ) ≤ ((C:ℝ)+1) * (dist x y)^(t:ℝ) := by
        exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (dist_nonneg) _)
      _ < ((C:ℝ)+1) * (ε/(4*((C:ℝ)+1))) :=
        (mul_lt_mul_of_pos_left hpow (by positivity))
      _ = ε/4 := by field_simp
  rcases (Metric.finite_approx_of_totallyBounded hK.totallyBounded) δ hδ
    with ⟨A,hAK,hAfin,hcover⟩
  have hall : ∀ a ∈ A, ∀ᶠ j in atTop, dist (G a) (F j a) < ε/2 := by
    intro a ha
    have hh := hpt a
    -- reverse order of dist
    simpa [dist_comm] using ((Metric.tendsto_nhds.mp hh) (ε/2) (by linarith))
  have hfin : ∀ᶠ j in atTop, ∀ a ∈ A, dist (G a) (F j a) < ε/2 :=
    (hAfin.eventually_all).2 hall
  filter_upwards [hfin] with j hj
  intro x hx
  have hx' := hcover hx
  simp only [mem_iUnion] at hx'
  rcases hx' with ⟨a, haA, hball⟩
  have hax : dist x a < δ := by
    have := (mem_ball.mp hball)
    simpa [dist_comm] using this
  have h1 : dist (F j x) (F j a) < ε/4 :=
    lt_of_le_of_lt (by
      have h := (hF j).nndist_le x a
      exact_mod_cast h) (hsmall hax)
  have h2 : dist (G x) (G a) < ε/4 :=
    lt_of_le_of_lt (by
      have h := hG.nndist_le x a
      exact_mod_cast h) (hsmall hax)
  have hmid := hj a haA
  have htri : dist (G x) (F j x) ≤
      dist (G x) (G a) + dist (G a) (F j a) + dist (F j a) (F j x) := by
    calc
      dist (G x) (F j x) ≤ dist (G x) (G a) + dist (G a) (F j x) := dist_triangle _ _ _
      _ ≤ dist (G x) (G a) + (dist (G a) (F j a) + dist (F j a) (F j x)) := by
        gcongr
        exact dist_triangle _ _ _
      _ = _ := by ring
  have h1' : dist (F j a) (F j x) < ε/4 := by simpa [dist_comm] using h1
  linarith
end MorreySupport
end
-- END INLINED FILE: Mathlib/Support/sobolev_embedding_morrey_853ace8d32/Limit.lean

-- BEGIN INLINED FILE: Mathlib/Support/sobolev_embedding_morrey_853ace8d32/Final.lean
section
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal Topology
namespace MorreySupport
abbrev EY (n : ℕ) := EuclideanSpace ℝ (Fin n)
noncomputable def coord {n : ℕ} (v : Fin n → ℝ) : EY n →L[ℝ] ℝ :=
  ∑ i, (v i) • (EuclideanSpace.proj i : EY n →L[ℝ] ℝ)
lemma coord_apply {n : ℕ} (v : Fin n → ℝ) (h : EY n) :
    coord v h = ∑ i, v i * h i := by
  classical
  simp [coord]
lemma coord_single {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    coord v (EuclideanSpace.single i (1:ℝ)) = v i := by
  classical
  simp [coord_apply, EuclideanSpace.single_apply]
-- derivatives are determined by coordinate axes
lemma fderiv_eq_coord {n : ℕ} {W : EY n → ℝ}
    {a : Fin n → EY n → ℝ}
    (h : ∀ i x, fderiv ℝ W x (EuclideanSpace.single i (1:ℝ)) = a i x)
    (x : EY n) : fderiv ℝ W x = coord (fun i => a i x) := by
  classical
  -- equality on basis vectors
  apply ContinuousLinearMap.ext
  intro u
  have hu := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr u
  -- repr is coordinate, basis is single
  have hu' : (∑ i : Fin n, (u i) • (EuclideanSpace.single i (1:ℝ))) = u := by
    simpa using hu
  rw [← hu']
  simp only [map_sum, map_smul, smul_eq_mul]
  simp [coord_apply, h]
  -- simp goal? 

lemma tendstoUniformlyOn_coord {n : ℕ} {ι : Type*} {l : Filter ι}
    (a : ι → Fin n → EY n → ℝ) (b : Fin n → EY n → ℝ)
    {K : Set (EY n)}
    (H : ∀ i, TendstoUniformlyOn (fun j x => a j i x) (b i) l K) :
    TendstoUniformlyOn (fun j x => coord (fun i => a j i x))
      (fun x => coord (fun i => b i x)) l K := by
  classical
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let M : ℝ := ∑ i : Fin n, ‖(EuclideanSpace.proj i : EY n →L[ℝ] ℝ)‖
  have hM : 0 ≤ M := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  let δ : ℝ := ε / (M+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hall : ∀ i : Fin n, ∀ᶠ j in l, ∀ x ∈ K, dist (b i x) (a j i x) < δ := by
    intro i
    exact (Metric.tendstoUniformlyOn_iff.mp (H i)) δ hδ
  have hall' : ∀ᶠ j in l, ∀ i : Fin n, ∀ x ∈ K, dist (b i x) (a j i x) < δ :=
    (Filter.eventually_all.2 hall)
  filter_upwards [hall'] with j hj
  intro x hx
  rw [dist_eq_norm]
  change ‖coord (fun i => b i x) - coord (fun i => a j i x)‖ < ε
  have heq : coord (fun i => b i x) - coord (fun i => a j i x) =
      ∑ i : Fin n, (b i x - a j i x) • (EuclideanSpace.proj i : EY n →L[ℝ] ℝ) := by
    simp [coord, Finset.sum_sub_distrib, sub_smul]
  rw [heq]
  calc
    ‖∑ i : Fin n, (b i x - a j i x) • (EuclideanSpace.proj i : EY n →L[ℝ] ℝ)‖
        ≤ ∑ i : Fin n, ‖(b i x - a j i x) • (EuclideanSpace.proj i : EY n →L[ℝ] ℝ)‖ :=
          norm_sum_le _ _
    _ ≤ ∑ i : Fin n, δ * ‖(EuclideanSpace.proj i : EY n →L[ℝ] ℝ)‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul]
      have hd := hj i x hx
      rw [Real.norm_eq_abs]
      have hh : |b i x - a j i x| < δ := by simpa [Real.dist_eq] using hd
      exact (mul_le_mul_of_nonneg_right hh.le (norm_nonneg _))
    _ = δ * M := by dsimp [M]; rw [Finset.mul_sum]
    _ < ε := by
      dsimp [δ]
      have : 0 < M + 1 := by linarith
      calc ε / (M+1) * M < ε / (M+1) * (M+1) :=
            mul_lt_mul_of_pos_left (by linarith) (by positivity)
        _ = ε := by field_simp

/-- On a finite Euclidean space, locally uniform convergence of all coordinate
partials is enough for the uniform limit derivative theorem. This is the
finite-dimensional packaging of that theorem used in the weak argument. -/
lemma hasFDerivAt_limit_coord {n : ℕ}
    (F : ℕ → EY n → ℝ) (G : EY n → ℝ)
    (a : ℕ → Fin n → EY n → ℝ) (b : Fin n → EY n → ℝ)
    (hF : ∀ j, ContDiff ℝ (1 : ℕ∞) (F j))
    (hc : ∀ j i x,
      fderiv ℝ (F j) x (EuclideanSpace.single i (1:ℝ)) = a j i x)
    (ha : ∀ i, ∀ K : Set (EY n), IsCompact K →
      TendstoUniformlyOn (fun j x => a j i x) (b i) atTop K)
    (hpt : ∀ x, Tendsto (fun j => F j x) atTop (𝓝 (G x)))
    (x : EY n) : HasFDerivAt G (coord (fun i => b i x)) x := by
  have hl : TendstoLocallyUniformlyOn
      (fun j z => coord (fun i => a j i z))
      (fun z => coord (fun i => b i z)) atTop (Set.univ : Set (EY n)) := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
    intro K hKu hK
    exact tendstoUniformlyOn_coord a b (K:=K) (fun i => ha i K hK)
  apply hasFDerivAt_of_tendstoLocallyUniformlyOn
      (l:=atTop) (f:=F) (g:=G)
      (f':= fun j z => coord (fun i => a j i z))
      (g':= fun z => coord (fun i => b i z)) (s:=Set.univ)
      isOpen_univ hl (fun j z hz => ?_) (fun z hz => hpt z) (Set.mem_univ x)
  have hd := (hF j).differentiable (by simp) z
  have heq : fderiv ℝ (F j) z = coord (fun i => a j i z) :=
    fderiv_eq_coord (hc j) z
  rw [← heq]
  exact hd.hasFDerivAt

/-- Finite linear combinations preserve a common Hölder exponent. The exact
coefficient is deliberately the (slightly loose) sum of norms, since it is
stable under adding the coordinate projections. -/
lemma holder_sum_smul {X Y ι : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [Fintype ι]
    {t : NNReal} (A : ι → NNReal) {u : ι → X → ℝ}
    (hu : ∀ i, HolderWith (A i) t (u i)) (y : ι → Y) :
    HolderWith (∑ i, A i * ‖y i‖₊) t
      (fun x => ∑ i, (u i x) • (y i)) := by
  classical
  apply holder_nndist_intro
  intro x z
  -- pass to the ordinary norm, where the triangle inequality is a
  -- finite-sum inequality
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_mul, NNReal.coe_sum, NNReal.coe_rpow, coe_nndist, coe_nnnorm]
  rw [dist_eq_norm]
  change ‖(∑ i, (u i x) • y i) - (∑ i, (u i z) • y i)‖ ≤
    (∑ i, (A i : ℝ) * ‖y i‖) * (dist x z) ^ (t:ℝ)
  have heq : (∑ i, (u i x) • y i) - (∑ i, (u i z) • y i) =
      ∑ i, (u i x - u i z) • y i := by
    simp [← Finset.sum_sub_distrib, sub_smul]
  rw [heq]
  calc
    ‖∑ i, (u i x - u i z) • y i‖ ≤
        ∑ i, ‖(u i x - u i z) • y i‖ := norm_sum_le _ _
    _ ≤ ∑ i, (A i : ℝ) * (dist x z) ^ (t:ℝ) * ‖y i‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul]
      have h := (hu i).nndist_le x z
      have h' : |u i x - u i z| ≤ (A i : ℝ) * (dist x z) ^ (t:ℝ) := by
        exact_mod_cast h
      simpa [Real.norm_eq_abs] using
        (mul_le_mul_of_nonneg_right h' (norm_nonneg (y i)))
    _ = (∑ i, (A i : ℝ) * ‖y i‖) * (dist x z) ^ (t:ℝ) := by
      push_cast
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring

lemma holder_coord {n : ℕ} {X : Type*} [PseudoMetricSpace X]
    {t : NNReal} (A : Fin n → NNReal) {u : Fin n → X → ℝ}
    (hu : ∀ i, HolderWith (A i) t (u i)) :
    HolderWith (∑ i, A i * ‖(EuclideanSpace.proj i : EY n →L[ℝ] ℝ)‖₊) t
      (fun x => coord (fun i => u i x)) := by
  have h := holder_sum_smul A hu
    (fun i => (EuclideanSpace.proj i : EY n →L[ℝ] ℝ))
  simpa [coord] using h

/-- The same finite-combination bound for bounded functions. -/
lemma norm_sum_smul_le_bound {X Y ι : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [Fintype ι]
    {u : ι → X → ℝ} (B : ι → ℝ) (hB : ∀ i x, ‖u i x‖ ≤ B i)
    (y : ι → Y) (x : X) :
    ‖∑ i, (u i x) • y i‖ ≤ ∑ i, B i * ‖y i‖ := by
  classical
  calc
    ‖∑ i, (u i x) • y i‖ ≤ ∑ i, ‖(u i x) • y i‖ := norm_sum_le _ _
    _ ≤ ∑ i, B i * ‖y i‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul]
      simpa using mul_le_mul_of_nonneg_right (hB i x) (norm_nonneg (y i))

end MorreySupport

end
-- END INLINED FILE: Mathlib/Support/sobolev_embedding_morrey_853ace8d32/Final.lean

-- BEGIN INLINED FILE: Mathlib/Support/sobolev_embedding_morrey_853ace8d32/Package.lean
section
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal Topology
namespace MorreySupport
abbrev EZ (n:ℕ) := EuclideanSpace ℝ (Fin n)
lemma holder_clm {X A B : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (L : A →L[ℝ] B) {u : X → A} {C s : NNReal}
    (h: HolderWith C s u) :
    HolderWith (‖L‖₊ * C) s (fun x => L (u x)) := by
  apply holder_nndist_intro
  intro x y
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_mul, NNReal.coe_rpow, coe_nndist, coe_nnnorm]
  rw [dist_eq_norm]
  have hL := L.le_opNorm (u x - u y)
  rw [map_sub] at hL
  calc
    ‖L (u x) - L (u y)‖ ≤ ‖L‖ * ‖u x - u y‖ := hL
    _ ≤ ‖L‖ * ((C:ℝ) * (dist x y) ^ (s:ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa [dist_eq_norm] using h.dist_le x y
    _ = (‖L‖ * (C:ℝ)) * (dist x y) ^ (s:ℝ) := by ring

lemma bound_clm {X A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (L:A→L[ℝ] B) (u:X→A) (M:ℝ) (h:∀x, ‖u x‖ ≤ M) :
    ∀ x, ‖L (u x)‖ ≤ ‖L‖ * M := by
  intro x
  exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (h x) (norm_nonneg _))

lemma holder_isometry {X A B : Type*} [PseudoMetricSpace X]
 [NormedAddCommGroup A] [NormedSpace ℝ A]
 [NormedAddCommGroup B] [NormedSpace ℝ B]
 (L : A ≃ₗᵢ[ℝ] B) {u:X→A} {C s:NNReal} (h:HolderWith C s u) :
 HolderWith C s (fun x => L (u x)) := by
  -- norm/dist is preserved
  apply holder_nndist_intro
  intro x y
  have hh := h.nndist_le x y
  -- convert through distance isometry
  have he : nndist (L (u x)) (L (u y)) = nndist (u x) (u y) := by
    apply NNReal.eq
    simp [dist_eq_norm, ← map_sub]
  rw [he]
  exact hh
lemma bound_isometry {X A B : Type*}
 [NormedAddCommGroup A] [NormedSpace ℝ A]
 [NormedAddCommGroup B] [NormedSpace ℝ B]
 (L : A ≃ₗᵢ[ℝ] B) (u:X→A) (M:ℝ) (h:∀x, ‖u x‖ ≤ M) :
 ∀ x, ‖L (u x)‖ ≤ M := by intro x; simpa using h x

lemma holder_fin_sum {X Y ι : Type*} [PseudoMetricSpace X]
 [NormedAddCommGroup Y] [NormedSpace ℝ Y] [Fintype ι]
 {s:NNReal} (A:ι→NNReal) (u:ι→X→Y) (h:∀i, HolderWith (A i) s (u i)) :
 HolderWith (∑ i, A i) s (fun x => ∑ i, u i x) := by
 classical
 have hv : ∀ v : Finset ι,
     HolderWith (∑ i ∈ v, A i) s (fun x => ∑ i ∈ v, u i x) := by
   intro v
   induction v using Finset.induction with
   | empty => simpa using (HolderWith.const (X:=X) (Y:=Y) (C:=0) (r:=s) (y:=0))
   | @insert a v ha ih =>
     have ha' := h a
     have H := ha'.add ih
     change HolderWith _ _ (fun x => u a x + ∑ i ∈ v, u i x) at H
     simpa [Finset.sum_insert ha] using H
 simpa using hv Finset.univ

lemma bound_fin_sum {X Y ι : Type*}
 [NormedAddCommGroup Y] [NormedSpace ℝ Y] [Fintype ι]
 (u:ι→X→Y) (B:ι→ℝ) (h:∀i x, ‖u i x‖ ≤ B i) :
 ∀ x, ‖∑ i, u i x‖ ≤ ∑ i, B i := by
 classical
 intro x
 exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i hi => h i x))

lemma iterated_smul_const {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
 [NormedAddCommGroup Y] [NormedSpace ℝ Y]
 (t:ℕ) (u:X→ℝ) (y:Y) (x:X) (hu: ContDiffAt ℝ (t:WithTop ℕ∞) u x) :
 iteratedFDeriv ℝ t (fun z => (u z) • y) x =
   (iteratedFDeriv ℝ t u x).smulRight y := by
 let L : ℝ →L[ℝ] Y := (ContinuousLinearMap.id ℝ ℝ).smulRight y
 have h := L.iteratedFDeriv_comp_left hu (i:=t) (le_rfl)
 have he : (fun z : X => u z • y) = (L ∘ u) := by
   funext z
   simp [L]
 rw [he, h]
 apply ContinuousMultilinearMap.ext
 intro v
 change ((iteratedFDeriv ℝ t u x) v • y) = _
 rfl

/-- A globally Holder continuous Lp scalar function on Euclidean space is bounded.
The bound need not be sharp; a unit ball average suffices. -/
lemma holder_memLp_bound {d:ℕ} {W : EZ d → ℝ}
    {C s : NNReal} {p:ℝ}
    (hp : 1 ≤ p) (hs : 0 < s)
    (hW : HolderWith C s W)
    (hLp : MemLp W (ENNReal.ofReal p) (volume : Measure (EZ d))) :
    ∃ M : ℝ, ∀ x, ‖W x‖ ≤ M := by
  classical
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  let F : EZ d → ℝ := fun z => ‖W z‖ ^ p
  have hFi : Integrable F (volume : Measure (EZ d)) := by
    dsimp [F]
    simpa [ENNReal.toReal_ofReal hp0.le] using
      hLp.integrable_norm_rpow (ENNReal.ofReal_eq_zero.not.mpr (not_le.mpr hp0)) (by simp)
  let K : ℝ := (volume : Measure (EZ d)).real (Metric.ball (0 : EZ d) 1)
  have hK : 0 < K := by
    dsimp [K]
    rw [MeasureTheory.measureReal_def]
    apply ENNReal.toReal_pos
    · exact ne_of_gt (Metric.measure_ball_pos (volume : Measure (EZ d)) (0 : EZ d) (by norm_num))
    · exact (measure_ball_lt_top).ne
  let T : ℝ := ∫ z : EZ d, F z ∂(volume : Measure (EZ d))
  have hT : 0 ≤ T := integral_nonneg_of_ae
      (Filter.Eventually.of_forall (fun z => Real.rpow_nonneg (norm_nonneg _) _))
  refine ⟨K⁻¹ * T + 1 + (C:ℝ), ?_⟩
  intro x
  let B := Metric.closedBall x (1:ℝ)
  have hBr : (volume : Measure (EZ d)).real B = K := by
    dsimp [B, K]
    simpa [finrank_euclideanSpace] using
      (MeasureTheory.Measure.addHaar_real_closedBall
        (volume : Measure (EZ d)) x (by norm_num : (0:ℝ) ≤ 1))
  have hB0 : (volume : Measure (EZ d)) B ≠ 0 := by
    intro hz
    have : (volume : Measure (EZ d)).real B = 0 := by simp [hz, MeasureTheory.measureReal_def]
    rw [hBr] at this
    linarith
  have hBtop : (volume : Measure (EZ d)) B ≠ ∞ := (measure_closedBall_lt_top).ne
  obtain ⟨y, hyB, hy⟩ := exists_le_setAverage hB0 hBtop hFi.integrableOn
  have hsetle : (∫ z : EZ d in B, F z ∂(volume : Measure (EZ d))) ≤ T :=
    setIntegral_le_integral hFi (Filter.Eventually.of_forall
      (fun z => Real.rpow_nonneg (norm_nonneg _) _))
  have hyF : F y ≤ K⁻¹ * T := by
    rw [setAverage_eq] at hy
    rw [hBr] at hy
    exact hy.trans (mul_le_mul_of_nonneg_left hsetle (by positivity))
  have norm_le_pow_add (a : ℝ) (ha : 0 ≤ a) : a ≤ a ^ p + 1 := by
    by_cases h1 : a ≤ 1
    · have hn : 0 ≤ a ^ p := Real.rpow_nonneg ha _
      linarith
    · have h1' : 1 ≤ a := le_of_lt (lt_of_not_ge h1)
      have hpow : a ^ (1:ℝ) ≤ a ^ p :=
        Real.rpow_le_rpow_of_exponent_le h1' hp
      simpa using (le_trans hpow (le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 1)))
  have hyN : ‖W y‖ ≤ K⁻¹ * T + 1 := by
    dsimp [F] at hyF
    have HH := norm_le_pow_add (‖W y‖) (norm_nonneg _)
    rw [Real.norm_eq_abs] at HH ⊢
    linarith
  have hxy : dist x y ≤ (1:ℝ) := by
    simpa [B, Metric.mem_closedBall, dist_comm] using hyB
  have hhold := hW.dist_le x y
  have hpow : dist x y ^ (s:ℝ) ≤ (1:ℝ) := by
    have hd0 : 0 ≤ dist x y := dist_nonneg
    have := Real.rpow_le_rpow hd0 hxy (by exact_mod_cast (le_of_lt hs))
    simpa using this
  have hdiff : ‖W x - W y‖ ≤ (C:ℝ) := by
    have := hhold.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
    simpa [dist_eq_norm] using this
  calc
    ‖W x‖ ≤ ‖W y‖ + ‖W x - W y‖ := by
      have := norm_add_le (W x - W y) (W y)
      simpa [sub_add_cancel, add_comm] using this
    _ ≤ (K⁻¹ * T + 1) + (C:ℝ) := add_le_add hyN hdiff
    _ = _ := rfl
end MorreySupport
namespace MorreySupport
lemma holder_smulRight {X U : Type*} {d : ℕ} [PseudoMetricSpace X]
 [NormedAddCommGroup U] [NormedSpace ℝ U]
 {u : X → U [×d]→L[ℝ] ℝ} {C s : NNReal}
 (v : U →L[ℝ] ℝ) (hu : HolderWith C s u) :
 HolderWith (C * ‖v‖₊) s (fun x => (u x).smulRight v) := by
 apply holder_nndist_intro
 intro x y
 apply NNReal.coe_le_coe.mp
 simp only [NNReal.coe_mul, NNReal.coe_rpow, coe_nndist, coe_nnnorm]
 rw [dist_eq_norm]
 have hd : (u x).smulRight v - (u y).smulRight v =
     (u x - u y).smulRight v := by ext w; simp [sub_smul]
 rw [hd, ContinuousMultilinearMap.norm_smulRight]
 have h := hu.dist_le x y
 rw [dist_eq_norm] at h
 calc
   ‖u x - u y‖ * ‖v‖ ≤ ((C:ℝ) * dist x y ^ (s:ℝ)) * ‖v‖ :=
     mul_le_mul_of_nonneg_right h (norm_nonneg _)
   _ = ((C:ℝ) * ‖v‖) * dist x y ^ (s:ℝ) := by ring
lemma bound_smulRight {X U : Type*} {d : ℕ}
 [NormedAddCommGroup U] [NormedSpace ℝ U]
 (v:U→L[ℝ] ℝ) (u:X→ U [×d]→L[ℝ] ℝ) (D:ℝ)
 (h:∀x, ‖u x‖ ≤ D) : ∀x, ‖(u x).smulRight v‖ ≤ D * ‖v‖ := by
 intro x
 rw [ContinuousMultilinearMap.norm_smulRight]
 exact mul_le_mul_of_nonneg_right (h x) (norm_nonneg _)
end MorreySupport

end
-- END INLINED FILE: Mathlib/Support/sobolev_embedding_morrey_853ace8d32/Package.lean

-- BEGIN INLINED FILE: Mathlib/Support/sobolev_embedding_morrey_853ace8d32/Top.lean
section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology
namespace MorreySupport

/-- If one further iterated derivative is uniformly bounded, the previous
one is globally Lipschitz.  This is the clean way of doing the last (integer)
step in the positive dimensional Morrey argument.  The curry convention for
`iteratedFDeriv` is an isometry, so no equivalence constants are lost. -/
lemma holder_one_iteratedFDeriv_of_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (t : ℕ) (u : E → F)
    (hu : ContDiff ℝ ((t+1 : ℕ) : ℕ∞) u)
    (D : ℝ) (hD : ∀ x, ‖iteratedFDeriv ℝ (t+1) u x‖ ≤ D) :
    HolderWith (⟨max D 0, le_max_right _ _⟩ : NNReal) 1
      (iteratedFDeriv ℝ t u) := by
  have hlt : (↑t : WithTop ℕ∞) <
      (↑(t+1 : ℕ) : ℕ∞) := by
    -- elaboration: the order variable of `ContDiff` is `WithTop ℕ∞`;
    -- the apparent `ℕ∞` in mathematical statements is coerced once.
    -- spell both coercions with `change` to keep simplification predictable.
    change (↑(t : ℕ∞) : WithTop ℕ∞) <
      (↑(↑(t+1 : ℕ) : ℕ∞) : WithTop ℕ∞)
    exact WithTop.coe_lt_coe.mpr (by exact_mod_cast (Nat.lt_succ_self t))
  have hdif : Differentiable ℝ (iteratedFDeriv ℝ t u) :=
    ContDiff.differentiable_iteratedFDeriv hlt hu
  have hb : ∀ x : E,
      ‖fderiv ℝ (iteratedFDeriv ℝ t u) x‖₊
        ≤ (⟨max D 0, le_max_right _ _⟩ : NNReal) := by
    intro x
    apply NNReal.coe_le_coe.mp
    -- coercing avoids simp's `norm_toNNReal`/`max_eq_...` rewrite
    change ‖fderiv ℝ (iteratedFDeriv ℝ t u) x‖ ≤ max D 0
    rw [norm_fderiv_iteratedFDeriv]
    exact (hD x).trans (le_max_left _ _)
  have hlip := lipschitzWith_of_nnnorm_fderiv_le hdif hb
  exact holderWith_one.mpr hlip

end MorreySupport

end
-- END INLINED FILE: Mathlib/Support/sobolev_embedding_morrey_853ace8d32/Top.lean

-- BEGIN INLINED MAIN PRELUDE

set_option maxHeartbeats 2500000


open LeanEval.Analysis.SobolevMorreyProblem
open MeasureTheory
open scoped ENNReal NNReal
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/

/-- Coordinate partials of a smooth test function commute.  The point which is a
little easy to miss when using `partialDeriv` rather than an iterated-derivative
notation is the derivative of the *application* of a CLM.  Applying
`fderiv_clm_apply` to the constant vector has zero first term; the second term
is the second derivative of the test function. -/
lemma compactSupport_partialDeriv {d : ℕ} {φ : E d → ℝ}
    (h : HasCompactSupport φ) (i : Fin d) :
    HasCompactSupport (partialDeriv i φ) := by
  unfold partialDeriv
  convert h.fderiv_apply ℝ (EuclideanSpace.single i (1 : ℝ)) using 1

lemma smooth_partialDeriv {d : ℕ} {φ : E d → ℝ}
    (h : ContDiff ℝ (⊤ : ℕ∞) φ) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (partialDeriv i φ) := by
  unfold partialDeriv
  have hord : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤
       (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
    change (↑((⊤ : ℕ∞) + 1) : WithTop ℕ∞) ≤
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
    exact WithTop.coe_le_coe.mpr (by simp)
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ φ) :=
    h.fderiv_right hord
  exact hf.clm_apply contDiff_const

lemma smooth_partialDeriv_comm {d : ℕ} (φ : E d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i j : Fin d) :
    partialDeriv i (partialDeriv j φ) =
      partialDeriv j (partialDeriv i φ) := by
  funext x
  let vi : E d := EuclideanSpace.single i (1 : ℝ)
  let vj : E d := EuclideanSpace.single j (1 : ℝ)
  change fderiv ℝ (fun x => fderiv ℝ φ x vj) x vi =
    fderiv ℝ (fun x => fderiv ℝ φ x vi) x vj
  have hc' : ContDiff ℝ (1 : ℕ∞) (fderiv ℝ φ) :=
    hφ.fderiv_right (by
      -- `ContDiff` uses `ℕ∞ω`; our smooth order is the copy of infinity in
      -- `ℕ∞`, not the analytic top of `ℕ∞ω`.
      change (↑((1 : ℕ∞) + 1) : WithTop ℕ∞) ≤
        (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  have hc : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    hc'.differentiable (by simp) x
  have hvj : DifferentiableAt ℝ (fun _ : E d => vj) x := differentiableAt_const _
  have hvi : DifferentiableAt ℝ (fun _ : E d => vi) x := differentiableAt_const _
  rw [fderiv_clm_apply hc hvj, fderiv_clm_apply hc hvi]
  simp [ContinuousLinearMap.flip_apply]
  have hs :=
    ((hφ.contDiffAt (x := x)).isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField]
      change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)).eq vi vj
  exact hs


/-- It is convenient to put smooth functions in a subtype.  On arbitrary
functions second partials need not commute (both sides are defined to be zero
when a derivative does not exist), while on this subtype the coordinate
derivatives are honest commuting endomorphisms.  This avoids a number of
pointwise smoothness hypotheses in the multi-index bookkeeping below. -/
def TestSmooth (d : ℕ) :=
  {φ : E d → ℝ // ContDiff ℝ (⊤ : ℕ∞) φ}

noncomputable def testPD {d : ℕ} (i : Fin d) : TestSmooth d → TestSmooth d :=
  fun f => ⟨partialDeriv i f.1, smooth_partialDeriv f.2 i⟩

lemma testPD_comm {d : ℕ} (i j : Fin d) :
    Function.Commute (testPD i : TestSmooth d → TestSmooth d) (testPD j) := by
  intro f
  apply Subtype.ext
  exact smooth_partialDeriv_comm f.1 f.2 i j

/-- The list expression underlying `mixedDeriv`, but acting on the smooth
subtype. -/
noncomputable def testMixedAux {d : ℕ} (l : List (Fin d)) (m : Fin d → ℕ) :
    TestSmooth d → TestSmooth d :=
  l.foldr (fun i T => (testPD i)^[m i] ∘ T) id

lemma testMixedAux_nil {d : ℕ} (m : Fin d → ℕ) :
    testMixedAux ([] : List (Fin d)) m = id := rfl
lemma testMixedAux_cons {d : ℕ} (i : Fin d) (l : List (Fin d)) (m : Fin d → ℕ) :
    testMixedAux (i :: l) m = (testPD i)^[m i] ∘ testMixedAux l m := rfl

/-- Forgetting the smooth subtype after applying the folded operators gives
exactly the original fold.  Notice `mixedDeriv` used a fold of applications;
`testMixedAux` is the same fold of composed endomorphisms. -/
lemma testMixedAux_val {d : ℕ} (l : List (Fin d)) (m : Fin d → ℕ)
    (φ : TestSmooth d) :
    (testMixedAux l m φ).1 =
      l.foldr (fun i ψ => (partialDeriv i)^[m i] ψ) (φ.1) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change (((testPD a)^[m a]) (testMixedAux l m φ)).1 = _
    have hit : ∀ t : ℕ, ∀ q : TestSmooth d,
        (((testPD a)^[t]) q).1 = ((partialDeriv a)^[t]) q.1 := by
      intro t
      induction t with
      | zero =>
        intro q
        rfl
      | succ t ht =>
        intro q
        -- Use the `f (f^[t] _)` form; on the subtype `testPD` has exactly
        -- the required underlying function.
        simp only [Function.iterate_succ_apply']
        change (partialDeriv a (((testPD a)^[t]) q).1) = _
        rw [ht]
    simpa [List.foldr] using (hit (m a) (testMixedAux l m φ)).trans
      (congrArg ((partialDeriv a)^[m a]) ih)

lemma testMixed_val {d : ℕ} (m : Fin d → ℕ) (φ : TestSmooth d) :
    (testMixedAux (List.finRange d) m φ).1 = mixedDeriv m φ.1 := by
  simp [mixedDeriv, testMixedAux_val]

/-- A coordinate partial commutes with the whole folded multi-index on
smooth functions.  This is the fundamental commutation fact used when
forming weak derivatives of an already-chosen weak derivative. -/
lemma testPD_comm_aux {d : ℕ} (l : List (Fin d))
    (m : Fin d → ℕ) (i : Fin d) :
    Function.Commute (testPD i : TestSmooth d → TestSmooth d)
      (testMixedAux l m) := by
  induction l with
  | nil =>
    -- every map commutes with id
    intro x; rfl
  | cons a l ih =>
    rw [testMixedAux_cons]
    exact ((testPD_comm i a).iterate_right (m a)).comp_right ih

/-- If a coordinate is absent from a list, raising just that exponent does
not change that part of the fold. -/
lemma testMixedAux_not_mem {d : ℕ} (l : List (Fin d))
    (m : Fin d → ℕ) (i : Fin d) (hi : i ∉ l) :
    testMixedAux l (fun j => m j + if j = i then 1 else 0) =
      testMixedAux l m := by
  classical
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha : a ≠ i := by
      intro h
      apply hi
      simp [h]
    have hl : i ∉ l := by
      intro h
      apply hi
      simp [h]
    rw [testMixedAux_cons, testMixedAux_cons]
    simp only [if_neg ha, Nat.add_zero]
    rw [ih hl]

/-- Incrementing a multi-index in one coordinate corresponds to one further
partial (on either side of the product, since all the factors commute).  The
`if` form of the increment is useful for the finite sum of coordinates. -/
lemma testMixedAux_succ {d : ℕ} (l : List (Fin d))
    (m : Fin d → ℕ) (i : Fin d) (hi : i ∈ l)
    (hnodup : l.Nodup) :
    testMixedAux l (fun j => m j + if j = i then 1 else 0) =
      (testPD i) ∘ testMixedAux l m := by
  classical
  induction l with
  | nil => cases hi
  | cons a l ih =>
    have hrest : l.Nodup := (List.nodup_cons.mp hnodup).2
    by_cases h : a = i
    · subst a
      have hnot : i ∉ l := (List.nodup_cons.mp hnodup).1
      have htail := testMixedAux_not_mem l m i hnot
      rw [testMixedAux_cons, testMixedAux_cons, htail]
      simp only [if_pos, Function.comp_apply]
      funext q
      change (((testPD i)^[m i + 1]) (testMixedAux l m q)) =
        testPD i (((testPD i)^[m i]) (testMixedAux l m q))
      rw [Function.iterate_succ_apply']
    · have hin : i ∈ l := (List.mem_cons.mp hi).resolve_left (fun h' => h h'.symm)
      have htail := ih hin hrest
      rw [testMixedAux_cons, testMixedAux_cons]
      simp only [if_neg h, Nat.add_zero, htail, Function.comp_apply]
      funext q
      change (((testPD a)^[m a])
          (testPD i (testMixedAux l m q))) =
        testPD i (((testPD a)^[m a]) (testMixedAux l m q))
      exact ((testPD_comm a i).iterate_left (m a)) (testMixedAux l m q)

/-- `mixedDeriv` is smooth when the input is smooth. -/
lemma smooth_mixedDeriv {d : ℕ} (m : Fin d → ℕ) {φ : E d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (mixedDeriv m φ) := by
  let q : TestSmooth d := ⟨φ, hφ⟩
  have h := (testMixedAux (List.finRange d) m q).2
  have he : (testMixedAux (List.finRange d) m q).1 = mixedDeriv m φ :=
    testMixed_val m q
  rw [he] at h
  exact h

/-- Compact support is also preserved by a folded mixed derivative.  This is
proved on a raw fold since no smoothness is needed. -/
lemma compactSupport_PD_iterate {d : ℕ} (i : Fin d) (t : ℕ)
    {φ : E d → ℝ} (hφ : HasCompactSupport φ) :
    HasCompactSupport (((partialDeriv i)^[t]) φ) := by
  induction t generalizing φ with
  | zero => simpa using hφ
  | succ t ht =>
    rw [Function.iterate_succ_apply']
    exact compactSupport_partialDeriv (ht hφ) i

lemma compactSupport_mixedDeriv {d : ℕ} (m : Fin d → ℕ) {φ : E d → ℝ}
    (hφ : HasCompactSupport φ) : HasCompactSupport (mixedDeriv m φ) := by
  unfold mixedDeriv
  generalize List.finRange d = l
  induction l with
  | nil => simpa using hφ
  | cons a l ih =>
    simp only [List.foldr]
    exact compactSupport_PD_iterate a (m a) (ih)

/-- On smooth functions the extra derivative may be placed on the input side
of the folded derivative. -/
lemma mixedDeriv_partial {d : ℕ} (m : Fin d → ℕ) (i : Fin d)
    (φ : E d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    mixedDeriv m (partialDeriv i φ) = partialDeriv i (mixedDeriv m φ) := by
  let q : TestSmooth d := ⟨φ, hφ⟩
  have hc := testPD_comm_aux (List.finRange d) m i
  have hv := hc q
  -- Subtype equality, then forget the subtype via `testMixed_val`.
  have hv' := congrArg Subtype.val hv
  have he : (mixedDeriv m (partialDeriv i φ)) = partialDeriv i (mixedDeriv m φ) := by
    simpa [testPD, testMixed_val] using hv'.symm
  exact he

/-- On a full `finRange`, raising the exponent at `i` is just applying a
further partial to the whole folded derivative. -/
lemma mixedDeriv_succ {d : ℕ} (m : Fin d → ℕ) (i : Fin d)
    (φ : E d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    mixedDeriv (fun j => m j + if j = i then 1 else 0) φ =
      partialDeriv i (mixedDeriv m φ) := by
  classical
  let q : TestSmooth d := ⟨φ, hφ⟩
  have hmem : i ∈ List.finRange d := List.mem_finRange i
  have hs := congrArg (fun F : TestSmooth d → TestSmooth d =>
      (F q).1) (testMixedAux_succ (List.finRange d) m i hmem
        (List.nodup_finRange d))
  simpa [Function.comp_apply, testPD, testMixed_val] using hs

/-- Consequently `D^m(∂ᵢφ)` is the same as the incremented mixed derivative
of `φ`.  Both sides here are those which occur in the distributional
integration-by-parts calculation. -/
lemma mixedDeriv_partial_eq_succ {d : ℕ} (m : Fin d → ℕ) (i : Fin d)
    (φ : E d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    mixedDeriv m (partialDeriv i φ) =
      mixedDeriv (fun j => m j + if j = i then 1 else 0) φ := by
  rw [mixedDeriv_partial m i φ hφ, mixedDeriv_succ m i φ hφ]

/-- A first-order coordinate multi-index has precisely the corresponding
classical partial on test functions. -/
lemma mixedDeriv_one {d : ℕ} (i : Fin d) (φ : E d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    mixedDeriv (fun j => if j = i then 1 else 0) φ =
      partialDeriv i φ := by
  have hs := mixedDeriv_succ (d := d) (fun _ : Fin d => (0 : ℕ)) i φ hφ
  -- the zero exponent fold is the identity
  have hz : mixedDeriv (fun _ : Fin d => (0 : ℕ)) φ = φ := by
    unfold mixedDeriv
    simp
  simpa [hz] using hs

/-- Finite-sum arithmetic for the incremented coordinate. -/
lemma sum_succ_multi {d : ℕ} (m : Fin d → ℕ) (i : Fin d) :
    (∑ j, (m j + if j = i then 1 else 0)) = (∑ j, m j) + 1 := by
  classical
  rw [Finset.sum_add_distrib]
  simp

lemma sum_one_multi {d : ℕ} (i : Fin d) :
    (∑ j : Fin d, (if j = i then 1 else 0)) = 1 := by
  classical
  simp

/-- Algebraic piece of iteration of weak derivatives.  If `v_m` and
`v_{m+e_i}` are locally integrable representatives of two derivatives of the
same function, the second really is the first weak derivative of `v_m`.
Nothing analytic is hidden here; it is just commuting smooth partials in the
test function.  This is the bookkeeping one needs before applying any
first-order Morrey or ACL lemma successively. -/
lemma IsWeakDeriv.step {d : ℕ} {f v w : E d → ℝ}
    (m : Fin d → ℕ) (i : Fin d)
    (hv : IsWeakDeriv f v m)
    (hw : IsWeakDeriv f w (fun j => m j + if j = i then 1 else 0)) :
    IsWeakDeriv v w (fun j => if j = i then 1 else 0) := by
  classical
  intro φ hφ hcomp
  have hpSmooth : ContDiff ℝ (⊤ : ℕ∞) (partialDeriv i φ) :=
    smooth_partialDeriv hφ i
  have hpComp : HasCompactSupport (partialDeriv i φ) :=
    compactSupport_partialDeriv hcomp i
  have A := hv (partialDeriv i φ) hpSmooth hpComp
  have B := hw φ hφ hcomp
  -- identify the common left integral
  rw [mixedDeriv_partial_eq_succ m i φ hφ] at A
  -- eliminate it between the equalities
  have AB :
      ((-1 : ℝ) ^ (∑ j, m j)) *
          (∫ x, v x * partialDeriv i φ x) =
        ((-1 : ℝ) ^ (∑ j, (m j + if j = i then 1 else 0))) *
          (∫ x, w x * φ x) := by
    calc
      _ = (∫ x, f x * mixedDeriv
            (fun j => m j + if j = i then 1 else 0) φ x) := A.symm
      _ = _ := B
  -- divide by the sign.  The signs are units ±1; doing this via the
  -- identity for the successor exponent keeps the proof purely in `ℝ`.
  have AB' :
      (∫ x, v x * partialDeriv i φ x) =
        (-1 : ℝ) * (∫ x, w x * φ x) := by
    -- write `(sum m)+1` on the right and cancel the common factor
    rw [sum_succ_multi m i, pow_succ] at AB
    have hn : ((-1 : ℝ) ^ (∑ j, m j)) ≠ 0 := pow_ne_zero _ (by norm_num)
    -- both sides have this same nonzero factor
    -- `pow_succ` put the extra `-1` at the end
    apply (mul_left_cancel₀ hn)
    -- goal after cancellation is in the orientation `a * _ = a * _`
    -- so use commutativity to match `AB`.
    simpa [mul_assoc, mul_left_comm, mul_comm] using AB
  -- unfold the one-coordinate mixed derivative and its sign
  -- (`IsWeakDeriv` asks for this exact product form).
  simpa [mixedDeriv_one i φ hφ, sum_one_multi i] using AB'


/-- For metric spaces it is often much easier to prove a Hölder estimate with
`nndist`.  This is the reverse direction of `HolderWith.nndist_le`; the latter
is in mathlib, but the elementary converse is also useful when doing explicit
estimates. -/
lemma holderWith_of_nndist {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] {C t : NNReal} {F : X → Y}
    (h : ∀ x y, nndist (F x) (F y) ≤ C * (nndist x y) ^ (t : ℝ)) :
    HolderWith C t F := by
  intro x y
  have hc : (↑(nndist (F x) (F y)) : ℝ≥0∞) ≤
      ↑(C * (nndist x y) ^ (t : ℝ)) := ENNReal.coe_le_coe.mpr (h x y)
  rw [edist_nndist, edist_nndist]
  -- after rewriting both extended distances there is just a coercion of the
  -- `NNReal` inequality above; keep this as an explicit conversion to avoid
  -- unfolding `HolderWith`'s extended-distance power simp loop.
  calc
    (↑(nndist (F x) (F y)) : ℝ≥0∞) ≤
        ↑(C * (nndist x y) ^ (t : ℝ)) := hc
    _ = (C : ℝ≥0∞) * (↑(nndist x y) : ℝ≥0∞) ^ (t : ℝ) := by
      rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg]
      exact NNReal.coe_nonneg _
    _ = _ := by rfl

/-- A global exponent can be lowered if the range is bounded.  On unit
scales this is simply monotonicity of `d^t`; on scales bigger than one it is
the crude `2 M` bound.  This small observation is important in the Morrey
regime: the first-order estimate gives exponent `1-n/p`, whereas the theorem
asks for every smaller positive exponent on all of `ℝⁿ`, not just on a ball. -/
lemma holderWith_lowerExponent_of_bounded {X Y : Type*}
    [MetricSpace X] [SeminormedAddCommGroup Y]
    {F : X → Y} {C M s t : NNReal}
    (hF : HolderWith C t F)
    (hM : ∀ x, ‖F x‖₊ ≤ M)
    (hs0 : 0 < s) (hst : s ≤ t) :
    HolderWith (C + (2 : NNReal) * M) s F := by
  -- work in nndist throughout; all powers are real powers of nonnegative
  -- reals, so there are no `∞` side conditions.
  apply holderWith_of_nndist
  intro x y
  set d : NNReal := nndist x y
  have hsR : (0 : ℝ) ≤ (s : ℝ) := NNReal.coe_nonneg s
  by_cases hd0 : d = 0
  · have hxy : x = y := nndist_eq_zero.mp hd0
    subst y
    simp [d]
  by_cases hd : d ≤ 1
  · have dp : 0 < d := (pos_iff_ne_zero.mpr hd0)
    have hpow : d ^ (t : ℝ) ≤ d ^ (s : ℝ) :=
      NNReal.rpow_le_rpow_of_exponent_ge dp hd (by exact_mod_cast hst)
    have h0C : (0 : NNReal) ≤ C := bot_le
    calc
      nndist (F x) (F y) ≤ C * d ^ (t : ℝ) := by
        simpa [d] using hF.nndist_le x y
      _ ≤ C * d ^ (s : ℝ) :=
        mul_le_mul_left' hpow C
      _ ≤ (C + (2 : NNReal) * M) * d ^ (s : ℝ) := by
        gcongr
        exact le_add_of_nonneg_right (by positivity)
  · have h1 : (1 : NNReal) ≤ d := le_of_lt (lt_of_not_ge hd)
    have hpow : (1 : NNReal) ≤ d ^ (s : ℝ) :=
      NNReal.one_le_rpow h1 hsR
    have hbd0 : nndist (F x) (F (x)) = 0 := by simp
    have hbounded : nndist (F x) (F y) ≤ (2 : NNReal) * M := by
      calc
        nndist (F x) (F y) ≤ nndist (F x) 0 + nndist 0 (F y) :=
          nndist_triangle _ _ _
        _ = ‖F x‖₊ + ‖F y‖₊ := by rw [nndist_zero_right, nndist_zero_left]
        _ ≤ M + M := add_le_add (hM x) (hM y)
        _ = (2 : NNReal) * M := by
          ring
    calc
      nndist (F x) (F y) ≤ (2 : NNReal) * M := hbounded
      _ ≤ C + (2 : NNReal) * M := le_add_of_nonneg_left (by positivity)
      _ ≤ (C + (2 : NNReal) * M) * d ^ (s : ℝ) := by
        have hnon : (0 : NNReal) ≤ C + (2 : NNReal) * M := bot_le
        nlinarith


/-- The sign in the mollifier test function.  Its `i`th derivative as a
function of the integration variable is the negative derivative of the
translated kernel. -/
lemma partialDeriv_comp_subLeft {d : ℕ} (ρ : E d → ℝ)
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (i : Fin d) (x : E d) :
    partialDeriv i (fun t : E d => ρ (x - t)) =
      fun t => -(partialDeriv i ρ (x - t)) := by
  funext t
  have ha : DifferentiableAt ℝ (fun z : E d => x - z) t :=
    differentiableAt_const _ |>.sub differentiableAt_id
  have hb : DifferentiableAt ℝ ρ (x - t) :=
    hρ.differentiable (by simp) (x - t)
  change fderiv ℝ (ρ ∘ (fun z : E d => x - z)) t
      (EuclideanSpace.single i (1 : ℝ)) = _
  rw [fderiv_comp t hb ha]
  -- the derivative of the inner reflection is `- id`
  rw [fderiv_const_sub, fderiv_id']
  simp [partialDeriv]

lemma smooth_subLeft {d : ℕ} (ρ : E d → ℝ)
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (x : E d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : E d => ρ (x - t)) := by
  change ContDiff ℝ (⊤ : ℕ∞) (ρ ∘ (fun t : E d => x - t))
  exact hρ.comp (contDiff_const.sub contDiff_id)

lemma compactSupport_subLeft {d : ℕ} (ρ : E d → ℝ)
    (hρ : HasCompactSupport ρ) (x : E d) :
    HasCompactSupport (fun t : E d => ρ (x - t)) := by
  have h := hρ.comp_homeomorph (Homeomorph.subLeft x)
  simpa [Function.comp_def] using h


open MeasureTheory
lemma partialDeriv_convolution_weak_one {d : ℕ}
    {v w : E d → ℝ} (i : Fin d)
    (hvloc : LocallyIntegrable v volume)
    (hweak : IsWeakDeriv v w (fun j => if j = i then 1 else 0))
    (ρ : E d → ℝ) (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hρc : HasCompactSupport ρ) :
    partialDeriv i
      (MeasureTheory.convolution v ρ (ContinuousLinearMap.mul ℝ ℝ) volume) =
      MeasureTheory.convolution w ρ (ContinuousLinearMap.mul ℝ ℝ) volume := by
  classical
  let e : E d := EuclideanSpace.single i (1 : ℝ)
  have hρone : ContDiff ℝ (1 : ℕ∞) ρ := hρ.of_le (by simp)
  have hρfcont : Continuous (fderiv ℝ ρ) :=
    hρone.continuous_fderiv (by simp)
  funext x
  have hf := hρc.hasFDerivAt_convolution_right
      (ContinuousLinearMap.mul ℝ ℝ) hvloc hρone x
  change fderiv ℝ
      (MeasureTheory.convolution v ρ (ContinuousLinearMap.mul ℝ ℝ) volume) x e = _
  rw [hf.fderiv]
  rw [MeasureTheory.convolution_precompR_apply
      (ContinuousLinearMap.mul ℝ ℝ) hvloc (hρc.fderiv ℝ) hρfcont x e]
  -- test the weak identity against `ρ (x-t)`
  have H := hweak (fun t : E d => ρ (x - t))
      (smooth_subLeft ρ hρ x) (compactSupport_subLeft ρ hρc x)
  rw [mixedDeriv_one i _ (smooth_subLeft ρ hρ x)] at H
  rw [partialDeriv_comp_subLeft ρ hρ i x] at H
  rw [sum_one_multi i] at H
  -- Expand the two convolutions into their integrals.  The sign on the
  -- differentiated test function cancels the weak-integration sign.
  simp only [MeasureTheory.convolution_def]
  simp [e, partialDeriv, mul_neg, MeasureTheory.integral_neg] at H ⊢
  exact H


lemma mul_flip_eq_lsmul :
    (ContinuousLinearMap.mul ℝ ℝ).flip = ContinuousLinearMap.lsmul ℝ ℝ := by
  ext a b
  simp

lemma convolution_mul_swap {d : ℕ} (f g : E d → ℝ) :
    MeasureTheory.convolution f g (ContinuousLinearMap.mul ℝ ℝ) volume =
      MeasureTheory.convolution g f (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  have h := MeasureTheory.convolution_flip
      (G := E d) (μ := volume) (f := f) (g := g)
        (ContinuousLinearMap.mul ℝ ℝ)
  rw [mul_flip_eq_lsmul] at h
  exact h.symm

/-- Normalized compact bump regularizations in the orientation used in
`partialDeriv_convolution_weak_one` converge almost everywhere to any locally
integrable scalar function.  Mathlib's differentiation theorem gives this
for `φ ⋆ f`; the flip above records that our `f ⋆ φ` convention is the same
for real scalars. -/
lemma ae_tendsto_convolution_mul_bump {d : ℕ} {ι : Type*}
    {u : E d → ℝ} (hu : LocallyIntegrable u volume)
    {φ : ι → ContDiffBump (0 : E d)} {l : Filter ι} {K : ℝ}
    (hφ : Filter.Tendsto (fun i => (φ i).rOut) l (nhds 0))
    (hφ' : ∀ᶠ i in l, (φ i).rOut ≤ K * (φ i).rIn) :
    ∀ᵐ x ∂(volume : Measure (E d)),
      Filter.Tendsto
        (fun i =>
          (MeasureTheory.convolution u ((φ i).normed volume)
            (ContinuousLinearMap.mul ℝ ℝ) volume) x)
        l (nhds (u x)) := by
  have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (μ := (volume : Measure (E d))) (g := u) hφ hφ' hu
  filter_upwards [h] with x hx
  have heq : (fun i =>
        (MeasureTheory.convolution u ((φ i).normed volume)
          (ContinuousLinearMap.mul ℝ ℝ) volume) x) =
      (fun i =>
        (MeasureTheory.convolution ((φ i).normed volume) u
          (ContinuousLinearMap.lsmul ℝ ℝ) volume) x) := by
    funext z
    rw [convolution_mul_swap]
  rw [heq]
  exact hx

/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/


-- END INLINED MAIN PRELUDE

namespace Submission

/-ResultBegin-/

theorem sobolev_embedding {n k r : ℕ} {α p : ℝ}
    (_hp : (n : ℝ) < p) (_hα : 0 < α) (_hα1 : α ≤ 1)
    (_hgap : (r : ℝ) + α < (k : ℝ) - n / p)
    (f : E n → ℝ) (_hf : MemSobolevWk k (ENNReal.ofReal p) f) :
    ∃ g : E n → ℝ, f =ᵐ[volume] g ∧ MemHolder r α g :=
/-ResultProofBegin-/(by
  classical
  by_cases hn : n = 0
  · subst n
    refine ⟨f, Filter.Eventually.of_forall (fun x => rfl), ?_⟩
    -- In dimension zero the source is a singleton.  This base case is worth
    -- splitting off; no integrability or analytic regularity is involved.
    -- In particular every function, and every one of its iterated
    -- derivatives (as a *function of the base point*), is constant.
    change
      ContDiff ℝ (r : ℕ∞) f ∧
        (∃ C : NNReal, HolderWith C α.toNNReal (iteratedFDeriv ℝ r f)) ∧
        ∀ j ≤ r, ∃ M : ℝ, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ M
    have hconst : f = (fun _ : E 0 => f 0) := by
      funext x
      have hx : x = (0 : E 0) := Subsingleton.elim _ _
      simp [hx]
    constructor
    · rw [hconst]
      exact contDiff_const
    constructor
    · refine ⟨0, ?_⟩
      intro x y
      have hxy : x = y := Subsingleton.elim _ _
      subst y
      simp
    · intro j hj
      refine ⟨‖iteratedFDeriv ℝ j f 0‖, ?_⟩
      intro x
      have hx : x = (0 : E 0) := Subsingleton.elim _ _
      simpa [hx]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hp1 : (1 : ℝ) ≤ p :=
      le_trans (by exact_mod_cast hn1) (le_of_lt _hp)
    have hpENN : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p :=
      ENNReal.one_le_ofReal.mpr hp1
    -- First take the zero-th weak derivative.  This removes a small but
    -- important nuisance in later regularity arguments: an element given by
    -- the definition has an actual globally L^p representative.  It is not
    -- just locally integrable.
    have hm0 : (∑ i : Fin n, (fun _ : Fin n => (0 : ℕ)) i) ≤ k := by
      simp
    obtain ⟨u, hu0, huLp⟩ := _hf.2 (fun _ : Fin n => (0 : ℕ)) hm0
    have huLoc : LocallyIntegrable u volume :=
      huLp.locallyIntegrable hpENN
    have hmixed0 :
        ∀ φ : E n → ℝ,
          mixedDeriv (fun _ : Fin n => (0 : ℕ)) φ = φ := by
      intro φ
      unfold mixedDeriv
      simp
    have h_pair : ∀ φ : E n → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ →
        (∫ x, f x * φ x) = ∫ x, u x * φ x := by
      intro φ hφ hφc
      simpa [hmixed0 φ] using hu0 φ hφ hφc
    have hfu : f =ᵐ[volume] u := by
      -- Faithfulness of the locally-integrable distribution.  This is why
      -- the `LocallyIntegrable` field in `MemSobolevWk` matters.
      apply ae_eq_of_integral_contDiff_smul_eq _hf.1 huLoc
      intro φ hφ hφc
      simpa [mul_comm] using h_pair φ hφ hφc
    -- Changing representatives preserves every weak derivative: the test
    -- integrands on the left hand side are a.e. equal.  We keep this stronger
    -- form of the data for the (Morrey) analytic step.
    have huW : MemSobolevWk k (ENNReal.ofReal p) u := by
      refine ⟨huLoc, ?_⟩
      intro m hm
      obtain ⟨v, hv, hvLp⟩ := _hf.2 m hm
      refine ⟨v, ?_, hvLp⟩
      intro φ hφ hφc
      have hv' := hv φ hφ hφc
      have hleft :
          (∫ x, f x * mixedDeriv m φ x) =
            ∫ x, u x * mixedDeriv m φ x := by
        apply integral_congr_ae
        filter_upwards [hfu] with x hx
        simp [hx]
      rw [← hleft]
      exact hv'
    -- In particular all derivatives through order `r + 1` are present.  It
    -- is occasionally easy to overlook this consequence of the real-valued
    -- gap hypothesis when using the definition with multiindices.
    have hp0 : (0 : ℝ) < p := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (Nat.zero_le n)
      exact lt_of_le_of_lt hn0 _hp
    have hdiv : (0 : ℝ) ≤ (n : ℝ) / p :=
      div_nonneg (by exact_mod_cast (Nat.zero_le n)) hp0.le
    have hrkltR : (r : ℝ) < (k : ℝ) := by
      have hkle : (k : ℝ) - n / p ≤ (k : ℝ) := sub_le_self _ hdiv
      linarith
    have hrk : r + 1 ≤ k :=
      (Nat.lt_iff_add_one_le.mp (by exact_mod_cast hrkltR))
    have hu_through_r1 :
        ∀ m : Fin n → ℕ, (∑ i, m i) ≤ r + 1 →
          ∃ v : E n → ℝ,
            IsWeakDeriv u v m ∧ MemLp v (ENNReal.ofReal p) volume := by
      intro m hm
      exact huW.2 m (hm.trans hrk)
    have huAll :
        ∀ m : Fin n → ℕ, (∑ i, m i) ≤ k →
          ∃ v : E n → ℝ, IsWeakDeriv u v m ∧
            MemLp v (ENNReal.ofReal p) volume ∧
            LocallyIntegrable v volume := by
      intro m hm
      obtain ⟨v, hv, hvLp⟩ := huW.2 m hm
      exact ⟨v, hv, hvLp, hvLp.locallyIntegrable hpENN⟩
    by_cases hzero : u =ᵐ[volume] (0 : E n → ℝ)
    · -- The zero class is an occasionally useful endpoint of the reduction.
      refine ⟨(fun _ : E n => (0 : ℝ)), hfu.trans hzero, ?_⟩
      change
        ContDiff ℝ (r : ℕ∞) (fun _ : E n => (0 : ℝ)) ∧
          (∃ C : NNReal,
            HolderWith C α.toNNReal
              (iteratedFDeriv ℝ r (fun _ : E n => (0 : ℝ)))) ∧
          ∀ j ≤ r, ∃ M : ℝ, ∀ x : E n,
            ‖iteratedFDeriv ℝ j (fun _ : E n => (0 : ℝ)) x‖ ≤ M
      constructor
      · exact contDiff_const
      constructor
      · refine ⟨0, ?_⟩
        intro x y
        simp
      · intro j hj
        refine ⟨0, ?_⟩
        intro x
        simp
    -- The zero-th/representative part of the distributional argument above
    -- is independent of any embedding estimate.  What remains is precisely
    -- the positive-dimensional, nonzero Morrey estimate for this globally
    -- L^p weak Sobolev representative (now one may restrict `huW` to the
    -- indicated orders).
    · -- A chosen, *coherent up to weak differentiation*, array of
      -- representatives is convenient for iterating a first-order Morrey
      -- or ACL lemma.  Coherence is not an extra hypothesis: it follows
      -- algebraically by testing with `∂ᵢφ` and commuting the smooth
      -- partials.  This point is independent of the analytic estimate, so
      -- spell it out before the remaining Morrey step.
      classical
      let I := {m : Fin n → ℕ // (∑ i, m i) ≤ k}
      have hchoice : ∀ a : I, ∃ v : E n → ℝ,
          IsWeakDeriv u v (a.1) ∧
            MemLp v (ENNReal.ofReal p) volume ∧ LocallyIntegrable v volume := by
        intro a
        exact huAll a.1 a.2
      choose V hVweak hVLp hVloc using hchoice
      -- `choose` grouped the last conjuncts; record projections with stable
      -- names for later analytic use.
      have Vweak (a : I) : IsWeakDeriv u (V a) a.1 := (hVweak a)
      have VLp (a : I) : MemLp (V a) (ENNReal.ofReal p) volume := hVLp a
      have Vloc (a : I) : LocallyIntegrable (V a) volume := hVloc a
      have Vstep : ∀ (m : Fin n → ℕ)
          (hm : (∑ i, m i) < k) (i : Fin n),
          IsWeakDeriv
            (V ⟨m, Nat.le_of_lt hm⟩)
            (V ⟨(fun j => m j + if j = i then 1 else 0), by
              rw [sum_succ_multi]
              exact (Nat.succ_le_of_lt hm)⟩)
            (fun j => if j = i then 1 else 0) := by
        intro m hm i
        exact IsWeakDeriv.step (m := m) i
          (Vweak ⟨m, Nat.le_of_lt hm⟩)
          (Vweak ⟨_, by
            rw [sum_succ_multi]
            exact Nat.succ_le_of_lt hm⟩)
      -- In particular the orders actually used for `C^r` lie in this
      -- family, as do their next coordinate derivatives.
      have Vthrough : ∀ (m : Fin n → ℕ)
          (hm : (∑ i, m i) ≤ r) (i : Fin n),
          ∃ a b : I, a.1 = m ∧
            b.1 = (fun j => m j + if j = i then 1 else 0) ∧
            IsWeakDeriv (V a) (V b) (fun j => if j = i then 1 else 0) ∧
            MemLp (V a) (ENNReal.ofReal p) volume ∧
            MemLp (V b) (ENNReal.ofReal p) volume := by
        intro m hm i
        have hmk : (∑ j, m j) < k :=
          lt_of_le_of_lt hm (Nat.lt_of_succ_le (hrk))
        let a : I := ⟨m, Nat.le_of_lt hmk⟩
        have hbproof : (∑ j, (m j + if j = i then 1 else 0)) ≤ k := by
          rw [sum_succ_multi]
          exact Nat.succ_le_of_lt hmk
        let b : I :=
          ⟨(fun j => m j + if j = i then 1 else 0), hbproof⟩
        refine ⟨a, b, rfl, rfl, ?_, VLp a, VLp b⟩
        exact Vstep m hmk i
      -- One may now regularize the entire array simultaneously.  Unlike an
      -- appeal to formal distribution theory, the following fact is a
      -- literal equality of classical derivatives for every smooth compact
      -- kernel; it follows by testing `Vstep` against `ρ (x-·)`.
      have Vmoll_smooth : ∀ (ρ : E n → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) ρ → HasCompactSupport ρ →
          ∀ a : I, ContDiff ℝ (⊤ : ℕ∞)
            (MeasureTheory.convolution (V a) ρ
              (ContinuousLinearMap.mul ℝ ℝ) volume) := by
        intro ρ hρ hρc a
        exact hρc.contDiff_convolution_right
          (ContinuousLinearMap.mul ℝ ℝ) (Vloc a) hρ
      have Vmoll_step : ∀ (ρ : E n → ℝ)
          (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ), HasCompactSupport ρ →
          ∀ (m : Fin n → ℕ)
            (hm : (∑ j, m j) < k) (i : Fin n),
            partialDeriv i
              (MeasureTheory.convolution (V ⟨m, Nat.le_of_lt hm⟩) ρ
                (ContinuousLinearMap.mul ℝ ℝ) volume) =
              MeasureTheory.convolution
                (V ⟨(fun j => m j + if j = i then 1 else 0), by
                    rw [sum_succ_multi]
                    exact Nat.succ_le_of_lt hm⟩) ρ
                (ContinuousLinearMap.mul ℝ ℝ) volume := by
        intro ρ hρ hρc m hm i
        exact partialDeriv_convolution_weak_one i (Vloc ⟨m, Nat.le_of_lt hm⟩)
          (Vstep m hm i) ρ hρ hρc
      have Vmoll_ae : ∀ {ι : Type} (φ : ι → ContDiffBump (0 : E n))
          {l : Filter ι} {K : ℝ},
          Filter.Tendsto (fun t => (φ t).rOut) l (nhds 0) →
          (∀ᶠ t in l, (φ t).rOut ≤ K * (φ t).rIn) →
          ∀ a : I, ∀ᵐ x ∂(volume : Measure (E n)),
            Filter.Tendsto
              (fun t =>
                (MeasureTheory.convolution (V a) ((φ t).normed volume)
                  (ContinuousLinearMap.mul ℝ ℝ) volume) x)
              l (nhds (V a x)) := by
        intro ι φ l K hφ hφ' a
        exact ae_tendsto_convolution_mul_bump (Vloc a) hφ hφ'
      -- What remains here is the genuinely analytic, positive-dimensional
      -- Morrey estimate for this coherent array of global `L^p` functions:
      -- construct a continuous representative for the order-zero member,
      -- get `1-n/p` estimates successively along `Vstep`, identify its
      -- classical derivatives, and lower the last exponent globally (the
      -- bounded-range lowering lemma above performs that final scalar
      -- step).  No consistency of weak multiindices is missing.
      -- The exponent algebra and the genuinely singular Hölder step of the
      -- first-order estimate can be stated independently of mollification.  We
      -- keep it for the chosen coherent array: a translated first derivative
      -- can be paired with the truncated Riesz kernel.  Its conjugate power
      -- is locally integrable exactly because n < p (the pole has order n-1).
      -- This is a useful hard prerequisite for the ball-averaging Morrey
      -- argument below, not an extra assumption.
      have hpgt1 : (1:ℝ) < p := by
        have hnr : (1:ℝ) ≤ n := by exact_mod_cast hn1
        exact lt_of_le_of_lt hnr _hp
      let q : ℝ := Real.conjExponent p
      have hpq : p.HolderConjugate q := by
        dsimp [q]
        exact Real.HolderConjugate.conjExponent hpgt1
      have hqdim : ((n:ℝ)-1) * q < n := by
        rw [hpq.conjugate_eq]
        have hd : 0 < p-1 := sub_pos.mpr hpgt1
        rw [← mul_div_assoc]
        apply (div_lt_iff₀ hd).2
        have hnr : (1:ℝ) ≤ n := by exact_mod_cast hn1
        nlinarith [_hp]
      have Vkernel : ∀ (a : I) (x : E n) (R : ℝ), 0 < R →
          (∫ z : E n, ‖V a (x + z)‖ * MorreyTry.kernel n R z ∂volume) ≤
            (∫ z : E n, ‖V a (x + z)‖ ^ p ∂volume) ^ (1/p) *
              ((R ^ ((n:ℝ) + ((-(n:ℝ)+1)*q)) *
                (∫ z : E n, (MorreyTry.kernel n 1 z)^q ∂volume)) ^ (1/q)) := by
        intro a x R hR
        have htrans : MemLp (fun z : E n => V a (x + z))
              (ENNReal.ofReal p) (volume : Measure (E n)) := by
          have hcomp := (VLp a).comp_measurePreserving
              (MeasureTheory.measurePreserving_add_left
                (volume : Measure (E n)) x)
          simpa [Function.comp_def] using hcomp
        exact MorreyTry.integral_norm_mul_kernel_scale_le hn1 hR hpq hqdim htrans
      have Vkernel' : ∀ (a : I) (x : E n) (R : ℝ), 0 < R →
          (∫ z : E n, ‖V a (x + z)‖ * MorreyTry.kernel n R z ∂volume) ≤
            (∫ z : E n, ‖V a z‖ ^ p ∂volume) ^ (1/p) *
              ((R ^ ((n:ℝ) + ((-(n:ℝ)+1)*q)) *
                (∫ z : E n, (MorreyTry.kernel n 1 z)^q ∂volume)) ^ (1/q)) := by
        intro a x R hR
        have hemb : MeasurableEmbedding
            (fun z : E n => x + z) :=
          (Homeomorph.addLeft x).measurableEmbedding
        have hpres := (MeasureTheory.measurePreserving_add_left
          (volume : Measure (E n)) x)
        have hpow : (∫ z : E n, ‖V a (x + z)‖ ^ p ∂volume) =
            (∫ z : E n, ‖V a z‖ ^ p ∂volume) := by
          simpa using hpres.integral_comp hemb
            (fun z : E n => (‖V a z‖ ^ p : ℝ))
        have HH := Vkernel a x R hR
        rw [hpow] at HH
        exact HH
      -- Normalizing the last display makes the characteristic Morrey
      -- exponent visible.  The scale factor is a fixed (finite) integral
      -- of the kernel on the unit ball.
      let Kq : ℝ :=
        (∫ z : E n, (MorreyTry.kernel n 1 z)^q ∂volume)
      have Kq0 : 0 ≤ Kq := by
        dsimp [Kq]
        apply MeasureTheory.integral_nonneg
        intro z
        exact Real.rpow_nonneg (MorreyTry.kernel_nonneg n 1 z) _
      have halg : ((n:ℝ) + ((-(n:ℝ)+1)*q)) * (1/q) =
          (1 - (n:ℝ)/p) := by
        have hpne : p ≠ 0 := ne_of_gt (lt_trans (by norm_num) hpgt1)
        have hdne : p - 1 ≠ 0 := by linarith [hpgt1]
        rw [hpq.conjugate_eq]
        field_simp
        ring
      have hscale : ∀ R : ℝ, 0 < R →
          ((R ^ ((n:ℝ) + ((-(n:ℝ)+1)*q)) * Kq) ^ (1/q)) =
            Kq ^ (1/q) * R ^ (1 - (n:ℝ)/p) := by
        intro R hR
        rw [Real.mul_rpow (Real.rpow_nonneg (le_of_lt hR) _) Kq0]
        rw [← Real.rpow_mul (le_of_lt hR)]
        rw [halg]
        ring
      have Vpotential : ∀ (a : I) (x : E n) (R : ℝ), 0 < R →
          (∫ z : E n, ‖V a (x + z)‖ * MorreyTry.kernel n R z ∂volume) ≤
            (∫ z : E n, ‖V a z‖ ^ p ∂volume) ^ (1/p) *
              (Kq ^ (1/q) * R ^ (1 - (n:ℝ)/p)) := by
        intro a x R hR
        have H := Vkernel' a x R hR
        have he : (∫ z : E n, (MorreyTry.kernel n 1 z)^q ∂volume) = Kq := rfl
        rw [he, hscale R hR] at H
        exact H
      -- For the analytic step the fundamental theorem on segments can now be
      -- used on every member of the array: all the scalar entries in its
      -- right hand side are the *neighbouring weak derivatives*.  Nothing
      -- about this calculation uses a representative or an a.e. choice.
      -- It is the ACL estimate on the smooth regularizations.
      have Vmoll_line : ∀ (ρ : E n → ℝ)
          (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ), HasCompactSupport ρ →
          ∀ (m : Fin n → ℕ) (hm : (∑ j, m j) < k) (x h : E n),
          ‖(MeasureTheory.convolution (V ⟨m, Nat.le_of_lt hm⟩) ρ
                (ContinuousLinearMap.mul ℝ ℝ) volume) (x + h) -
             (MeasureTheory.convolution (V ⟨m, Nat.le_of_lt hm⟩) ρ
                (ContinuousLinearMap.mul ℝ ℝ) volume) x‖ ≤
            ∫ t : ℝ in (0)..(1),
              (∑ i : Fin n,
                ‖(MeasureTheory.convolution
                  (V ⟨(fun j => m j + if j = i then 1 else 0), by
                    rw [sum_succ_multi]
                    exact Nat.succ_le_of_lt hm⟩) ρ
                    (ContinuousLinearMap.mul ℝ ℝ) volume)
                    (x + t • h)‖) * ‖h‖ := by
        intro ρ hρ hρc m hm x h
        let U : E n → ℝ :=
          MeasureTheory.convolution (V ⟨m, Nat.le_of_lt hm⟩) ρ
            (ContinuousLinearMap.mul ℝ ℝ) volume
        have hUs : ContDiff ℝ (⊤ : ℕ∞) U := Vmoll_smooth ρ hρ hρc _
        have hU1 : ContDiff ℝ (1 : ℕ∞) U := hUs.of_le (by simp)
        have H := MorreySupport.smooth_line_bound_coord U hU1 x h
        change ‖U (x+h) - U x‖ ≤ _
        change ‖U (x+h) - U x‖ ≤ _ at H
        -- Substitute each coordinate fderivative by the distributional
        -- derivative, for which the preceding test-function computation is
        -- an actual equality of functions.
        have heq (i : Fin n) (z : E n) :
            fderiv ℝ U z (EuclideanSpace.single i (1 : ℝ)) =
              (MeasureTheory.convolution
                (V ⟨(fun j => m j + if j = i then 1 else 0), by
                  rw [sum_succ_multi]
                  exact Nat.succ_le_of_lt hm⟩) ρ
                (ContinuousLinearMap.mul ℝ ℝ) volume) z := by
          have Hs := Vmoll_step ρ hρ hρc m hm i
          have Hz := congrFun Hs z
          exact Hz
        simpa [heq] using H
      have Vmoll_ball : ∀ (ρ : E n → ℝ)
          (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ)
          (m : Fin n → ℕ) (hm : (∑ j, m j) < k)
          (x : E n) (R:ℝ),
          (∫ h : E n in Metric.closedBall 0 R,
              ‖(MeasureTheory.convolution (V ⟨m, Nat.le_of_lt hm⟩) ρ
                (ContinuousLinearMap.mul ℝ ℝ) volume) (x+h) -
               (MeasureTheory.convolution (V ⟨m, Nat.le_of_lt hm⟩) ρ
                (ContinuousLinearMap.mul ℝ ℝ) volume) x‖ ∂volume) ≤
            ∫ t : ℝ in Set.Icc 0 1,
              ∫ h : E n in Metric.closedBall 0 R,
                (∑ i : Fin n,
                  ‖(MeasureTheory.convolution
                    (V ⟨(fun j => m j + if j = i then 1 else 0), by
                      rw [sum_succ_multi]
                      exact Nat.succ_le_of_lt hm⟩) ρ
                      (ContinuousLinearMap.mul ℝ ℝ) volume)
                      (x + t • h)‖) * ‖h‖ ∂volume ∂volume := by
        intro ρ hρ hρc m hm x R
        let U : E n → ℝ := MeasureTheory.convolution
          (V ⟨m, Nat.le_of_lt hm⟩) ρ (ContinuousLinearMap.mul ℝ ℝ) volume
        have hUs : ContDiff ℝ (⊤ : ℕ∞) U := Vmoll_smooth ρ hρ hρc _
        have H := MorreySupport.smooth_ball_segment_bound U
          (hUs.of_le (by simp)) x R
        have heq (i : Fin n) (z : E n) :
            fderiv ℝ U z (EuclideanSpace.single i (1 : ℝ)) =
              (MeasureTheory.convolution
                (V ⟨(fun j => m j + if j = i then 1 else 0), by
                  rw [sum_succ_multi]
                  exact Nat.succ_le_of_lt hm⟩) ρ
                (ContinuousLinearMap.mul ℝ ℝ) volume) z := by
          exact congrFun (Vmoll_step ρ hρ hρc m hm i) z
        simpa [U, heq] using H
      -- An economical way of estimating the right-hand side is first to
      -- rescale the ball at a *fixed* positive segment parameter.  The only
      -- small parameter left is then `t⁻ⁿ`; ordinary finite-measure Holder on
      -- the ball `t R` supplies the compensating `t^(n/q)`.  Recording this
      -- fact for every member of the weak array is useful since it makes the
      -- remaining endpoint of the Morrey argument strictly one-dimensional.
      have Vscale_ball : ∀ (a : I) (x : E n) (t R : ℝ), 0 < t → 0 ≤ R →
          (∫ h : E n in Metric.closedBall 0 R,
                ‖V a (x + t • h)‖ ∂volume) ≤
            (t ^ n)⁻¹ *
              ((∫ z : E n, ‖V a z‖ ^ p ∂volume) ^ (1/p) *
                (( (volume : Measure (E n)).real
                    (Metric.closedBall (0 : E n) (t*R)) : ℝ) ^ (1/q))) := by
        intro a x t R ht hR
        exact MorreySupport.setIntegral_norm_comp_add_smul_le
          hpq (VLp a) x ht hR
      have Vscale_volume : ∀ (t R : ℝ), 0 ≤ t → 0 ≤ R →
          ((volume : Measure (E n)).real
            (Metric.closedBall (0 : E n) (t*R))) =
            (t*R)^n *
              (volume : Measure (E n)).real
                (Metric.ball (0 : E n) 1) := by
        intro t R ht hR
        exact MorreySupport.real_volume_closedBall_zero (t*R)
          (mul_nonneg ht hR)
      -- The residual singularity in this rescaled proof is one-dimensional.
      -- This observation often considerably simplifies the final Morrey
      -- estimate: on `Icc (0) 1` it is simply the ordinary integral of
      -- `t^(-n/p)`.  It is finite precisely in the supercritical regime.
      have hnp : (n : ℝ) / p < 1 := by
        exact (div_lt_one hp0).2 _hp
      have hinterv :
          IntervalIntegrable (fun t : ℝ => t ^ (-(n:ℝ)/p))
            (volume : Measure ℝ) (0:ℝ) 1 := by
        have hh : (-1:ℝ) < -(n:ℝ)/p := by
          rw [neg_div]; exact neg_lt_neg hnp
        exact intervalIntegral.intervalIntegrable_rpow' hh
      have hinterv_val :
          (∫ t : ℝ in (0:ℝ)..1, t ^ (-(n:ℝ)/p)) =
            (1:ℝ) / (1 - (n:ℝ)/p) := by
        have hh : (-1:ℝ) < -(n:ℝ)/p := by
          rw [neg_div]; exact neg_lt_neg hnp
        rw [integral_rpow (Or.inl hh)]
        have hpos : 0 < 1 - (n:ℝ)/p := sub_pos.mpr hnp
        have hnot : 1 - (n:ℝ)/p ≠ 0 := ne_of_gt hpos
        rw [Real.one_rpow]
        have hz : (0:ℝ) ^ (-(n:ℝ)/p + 1) = 0 := by
          rw [Real.zero_rpow]
          linarith
        rw [hz]
        ring
      -- Finish the one-dimensional endpoint which was missing from the elementary
      -- ball/segment reduction: for a smooth function whose coordinate
      -- derivatives are globally in Lp, the averaged oscillation on a ball
      -- is controlled by their global Lp masses.  Here q is the conjugate of
      -- p fixed above.  The t=0 endpoint of the segment integral is harmless
      -- (a null singleton); the proof of this lemma integrates the rescaled
      -- Holder estimate on every t>0 against t^(-n/p).
      have smooth_ball_endpoint :
          ∀ (U : E n → ℝ), ContDiff ℝ (1 : ℕ∞) U →
            (∀ i : Fin n,
              MemLp (fun z : E n =>
                  fderiv ℝ U z (EuclideanSpace.single i (1:ℝ)))
                (ENNReal.ofReal p) (volume : Measure (E n))) →
            ∀ (x : E n) (R : ℝ), 0 ≤ R →
              (∫ h : E n in Metric.closedBall 0 R,
                   ‖U (x+h) - U x‖ ∂volume) ≤
                ((R * (∑ i : Fin n,
                    (∫ z : E n,
                      ‖fderiv ℝ U z (EuclideanSpace.single i (1:ℝ))‖ ^ p
                        ∂volume) ^ (1/p)) *
                    ((volume : Measure (E n)).real
                      (Metric.ball (0 : E n) 1)) ^ (1/q) *
                    R ^ ((n:ℝ)/q))) *
                  (1 / (1 - (n:ℝ)/p)) := by
        intro U hU hULp x R hR
        exact MorreySupport.smooth_ball_segment_Lp_bound
          U hU hpq hULp hnp x hR
      -- and, by averaging over the same translated ball, a two-point
      -- version.  The second integral is taken on the radius `2R` ball;
      -- translating the radius `R` ball about the first point lands there.
      have smooth_pair_endpoint :
          ∀ (U : E n → ℝ), ContDiff ℝ (1 : ℕ∞) U →
            (∀ i : Fin n,
              MemLp (fun z : E n =>
                  fderiv ℝ U z (EuclideanSpace.single i (1:ℝ)))
                (ENNReal.ofReal p) (volume : Measure (E n))) →
            ∀ x y : E n,
              let R : ℝ := ‖x-y‖
              ‖U x-U y‖ * (volume : Measure (E n)).real
                    (Metric.closedBall (0 : E n) R) ≤
                ((R * (∑ i : Fin n,
                    (∫ z : E n,
                      ‖fderiv ℝ U z (EuclideanSpace.single i (1:ℝ))‖ ^ p
                        ∂volume) ^ (1/p)) *
                    ((volume : Measure (E n)).real
                      (Metric.ball (0 : E n) 1)) ^ (1/q) *
                    R ^ ((n:ℝ)/q))) * (1 / (1 - (n:ℝ)/p)) +
                (((2*R) * (∑ i : Fin n,
                    (∫ z : E n,
                      ‖fderiv ℝ U z (EuclideanSpace.single i (1:ℝ))‖ ^ p
                        ∂volume) ^ (1/p)) *
                    ((volume : Measure (E n)).real
                      (Metric.ball (0 : E n) 1)) ^ (1/q) *
                    (2*R) ^ ((n:ℝ)/q))) * (1 / (1 - (n:ℝ)/p)) := by
        intro U hU hULp x y
        exact MorreySupport.smooth_pair_volume_mul_Lp_bound
          U hU hpq hULp hnp x y
      -- Cancelling the positive volume of the radius ball gives the actual
      -- characteristic Morrey exponent.  The arbitrary-looking factor 2 is
      -- only the translated-ball inclusion; no singular-kernel hypothesis is
      -- hidden in this estimate.
      have smooth_point_endpoint :
          ∀ (U : E n → ℝ), ContDiff ℝ (1 : ℕ∞) U →
            (∀ i : Fin n,
              MemLp (fun z : E n =>
                  fderiv ℝ U z (EuclideanSpace.single i (1:ℝ)))
                (ENNReal.ofReal p) (volume : Measure (E n))) →
            ∀ x y : E n,
              ‖U x-U y‖ ≤
                let S : ℝ := ∑ i : Fin n,
                    (∫ z : E n,
                      ‖fderiv ℝ U z (EuclideanSpace.single i (1:ℝ))‖ ^ p
                        ∂volume) ^ (1/p)
                let K0 : ℝ := (volume : Measure (E n)).real
                                  (Metric.ball (0 : E n) 1)
                (S * K0 ^ (1/q) * K0⁻¹ * (1 + 2 * (2:ℝ)^((n:ℝ)/q)) *
                    (1 / (1 - (n:ℝ)/p))) *
                  ‖x-y‖ ^ (1 - (n:ℝ)/p) := by
        intro U hU hULp x y
        exact MorreySupport.smooth_pair_Lp_holder U hU hpq hULp hnp x y

      -- Jensen's inequality for the *normalized* bump is needed here; a bound
      -- by its sup norm would blow up like `ε⁻ⁿ` and gives no limit.  The
      -- contraction lemma uses the bump as a probability density and Tonelli,
      -- so its constants are independent of its radii.
      have Vmoll_deriv_Lp : ∀ (φ : ContDiffBump (0 : E n))
          (m : Fin n → ℕ) (hm : (∑ j, m j) < k) (i : Fin n),
          MemLp (fun z : E n =>
            fderiv ℝ
              (MeasureTheory.convolution (V ⟨m, Nat.le_of_lt hm⟩)
                (φ.normed volume) (ContinuousLinearMap.mul ℝ ℝ) volume) z
                (EuclideanSpace.single i (1:ℝ)))
              (ENNReal.ofReal p) (volume : Measure (E n)) := by
        intro φ m hm i
        have he := Vmoll_step (φ.normed volume)
            (φ.contDiff_normed) (φ.hasCompactSupport_normed)
            m hm i
        have HC := MorreySupport.convolution_bump_memLp φ hp1
          (VLp ⟨(fun j => m j + if j = i then 1 else 0), by
            rw [sum_succ_multi]
            exact Nat.succ_le_of_lt hm⟩)
        -- `Vmoll_step` identifies the classical derivative with this
        -- mollified weak derivative exactly, not a.e.
        have he' := he
        change MemLp (partialDeriv i
              (MeasureTheory.convolution (V ⟨m, Nat.le_of_lt hm⟩)
                (φ.normed volume) (ContinuousLinearMap.mul ℝ ℝ) volume))
              (ENNReal.ofReal p) (volume : Measure (E n))
        rw [he']
        exact HC
      have Vmoll_deriv_mass : ∀ (φ : ContDiffBump (0 : E n))
          (m : Fin n → ℕ) (hm : (∑ j, m j) < k) (i : Fin n),
          (∫ z : E n,
            ‖fderiv ℝ
              (MeasureTheory.convolution (V ⟨m, Nat.le_of_lt hm⟩)
                (φ.normed volume) (ContinuousLinearMap.mul ℝ ℝ) volume) z
                (EuclideanSpace.single i (1:ℝ))‖ ^ p ∂volume) ≤
          (∫ z : E n,
            ‖V ⟨(fun j => m j + if j = i then 1 else 0), by
               rw [sum_succ_multi]; exact Nat.succ_le_of_lt hm⟩ z‖ ^ p
               ∂volume) := by
        intro φ m hm i
        have he := Vmoll_step (φ.normed volume)
            (φ.contDiff_normed) (φ.hasCompactSupport_normed) m hm i
        have HH := (MorreySupport.convolution_bump_rpow_le φ hp1
          (VLp ⟨(fun j => m j + if j = i then 1 else 0), by
            rw [sum_succ_multi]; exact Nat.succ_le_of_lt hm⟩)).2
        change (∫ z : E n,
            ‖(partialDeriv i
              (MeasureTheory.convolution (V ⟨m, Nat.le_of_lt hm⟩)
                (φ.normed volume) (ContinuousLinearMap.mul ℝ ℝ) volume)) z‖ ^ p
                ∂volume) ≤ _
        rw [he]
        exact HH
      -- Thus the smooth estimate is actually available for every normalized
      -- regularization of every member of the array, not just for compactly
      -- supported smooth *inputs*.  This is the first uniform estimate in the
      -- weak argument.
      have Vmoll_first_holder : ∀ (φ : ContDiffBump (0 : E n))
          (m : Fin n → ℕ) (hm : (∑ j, m j) < k) (x y : E n),
          let U : E n → ℝ :=
            MeasureTheory.convolution (V ⟨m, Nat.le_of_lt hm⟩)
              (φ.normed volume) (ContinuousLinearMap.mul ℝ ℝ) volume
          ‖U x - U y‖ ≤
            let S : ℝ := ∑ i : Fin n,
                (∫ z : E n,
                  ‖fderiv ℝ U z (EuclideanSpace.single i (1:ℝ))‖ ^ p
                     ∂volume) ^ (1/p)
            let K0 : ℝ := (volume : Measure (E n)).real
                                  (Metric.ball (0 : E n) 1)
            (S * K0 ^ (1/q) * K0⁻¹ * (1 + 2 * (2:ℝ)^((n:ℝ)/q)) *
                    (1 / (1 - (n:ℝ)/p))) *
              ‖x-y‖ ^ (1 - (n:ℝ)/p) := by
        intro φ m hm x y
        dsimp
        exact smooth_point_endpoint _
          ((Vmoll_smooth (φ.normed volume) φ.contDiff_normed
              φ.hasCompactSupport_normed _).of_le (by simp))
          (fun i => Vmoll_deriv_Lp φ m hm i) x y

      have Vmoll_uniform_holder : ∀ (φ : ContDiffBump (0 : E n))
          (m : Fin n → ℕ) (hm : (∑ j, m j) < k) (x y : E n),
          let U : E n → ℝ :=
            MeasureTheory.convolution (V ⟨m, Nat.le_of_lt hm⟩)
              (φ.normed volume) (ContinuousLinearMap.mul ℝ ℝ) volume
          ‖U x - U y‖ ≤
            let S : ℝ := ∑ i : Fin n,
                (∫ z : E n,
                  ‖V ⟨(fun j => m j + if j = i then 1 else 0), by
                    rw [sum_succ_multi]; exact Nat.succ_le_of_lt hm⟩ z‖ ^ p
                     ∂volume) ^ (1/p)
            let K0 : ℝ := (volume : Measure (E n)).real
                                  (Metric.ball (0 : E n) 1)
            (S * K0 ^ (1/q) * K0⁻¹ * (1 + 2 * (2:ℝ)^((n:ℝ)/q)) *
                    (1 / (1 - (n:ℝ)/p))) *
              ‖x-y‖ ^ (1 - (n:ℝ)/p) := by
        intro φ m hm x y
        dsimp
        let U : E n → ℝ :=
            MeasureTheory.convolution (V ⟨m, Nat.le_of_lt hm⟩)
              (φ.normed volume) (ContinuousLinearMap.mul ℝ ℝ) volume
        let K0 : ℝ := (volume : Measure (E n)).real
                                  (Metric.ball (0 : E n) 1)
        let S : ℝ := ∑ i : Fin n,
                (∫ z : E n,
                  ‖fderiv ℝ U z (EuclideanSpace.single i (1:ℝ))‖ ^ p
                     ∂volume) ^ (1/p)
        let T : ℝ := ∑ i : Fin n,
                (∫ z : E n,
                  ‖V ⟨(fun j => m j + if j = i then 1 else 0), by
                    rw [sum_succ_multi]; exact Nat.succ_le_of_lt hm⟩ z‖ ^ p
                     ∂volume) ^ (1/p)
        have H : ‖U x-U y‖ ≤
            (S * K0 ^ (1/q) * K0⁻¹ * (1 + 2 * (2:ℝ)^((n:ℝ)/q)) *
                    (1 / (1 - (n:ℝ)/p))) *
              ‖x-y‖ ^ (1 - (n:ℝ)/p) :=
          Vmoll_first_holder φ m hm x y
        have hp0' : 0 ≤ 1 / p := by
          positivity
        have hST : S ≤ T := by
          dsimp [S, T]
          apply Finset.sum_le_sum
          intro i hi
          apply Real.rpow_le_rpow (by
            apply MeasureTheory.integral_nonneg
            intro z
            positivity) (Vmoll_deriv_mass φ m hm i) hp0'
        have hK0 : 0 < K0 := by
          dsimp [K0]
          rw [MeasureTheory.measureReal_def]
          apply ENNReal.toReal_pos
          · exact ne_of_gt (Metric.measure_ball_pos
                (volume : Measure (E n)) (0 : E n) (by norm_num))
          · exact (measure_ball_lt_top).ne
        calc
          ‖U x-U y‖ ≤
            (S * K0 ^ (1/q) * K0⁻¹ * (1 + 2 * (2:ℝ)^((n:ℝ)/q)) *
                    (1 / (1 - (n:ℝ)/p))) *
              ‖x-y‖ ^ (1 - (n:ℝ)/p) := H
          _ ≤ (T * K0 ^ (1/q) * K0⁻¹ * (1 + 2 * (2:ℝ)^((n:ℝ)/q)) *
                    (1 / (1 - (n:ℝ)/p))) *
              ‖x-y‖ ^ (1 - (n:ℝ)/p) := by
            have hnpos : 0 ≤ 1 - (n:ℝ)/p := (sub_pos.mpr hnp).le
            gcongr

      /- Choose once and for all a standard family of normalized bumps.  The
      dense-limit lemma applies without any separability/subsequence choices:
      the differentiation theorem already gives convergence along the entire
      family almost everywhere. -/
      let φseq : ℕ → ContDiffBump (0 : E n) := fun j =>
        { rIn := ((j:ℝ)+1)⁻¹,
          rOut := 2*((j:ℝ)+1)⁻¹
          rIn_pos := by positivity
          rIn_lt_rOut := by
            have : 0 < ((j:ℝ)+1)⁻¹ := by positivity
            linarith }
      have hφout : Filter.Tendsto (fun j => (φseq j).rOut)
          Filter.atTop (nhds 0) := by
        have Htop : Filter.Tendsto (fun j : ℕ => (j:ℝ)+1)
              Filter.atTop Filter.atTop :=
          Filter.tendsto_atTop_add_const_right _ 1
            (tendsto_natCast_atTop_atTop)
        have Hinv : Filter.Tendsto (fun j : ℕ => ((j:ℝ)+1)⁻¹)
              Filter.atTop (nhds 0) := tendsto_inv_atTop_zero.comp Htop
        have H2 := Hinv.const_mul (2:ℝ)
        simpa [φseq] using H2
      have hφratio : ∀ᶠ j in Filter.atTop,
          (φseq j).rOut ≤ (2:ℝ) * (φseq j).rIn := by
        filter_upwards [] with j
        simp [φseq]

      let β : ℝ := 1 - (n:ℝ)/p
      have hβ : 0 < β := by dsimp [β]; exact sub_pos.mpr hnp
      let τ : NNReal := ⟨β, hβ.le⟩
      have hτ : 0 < τ := by exact_mod_cast hβ
      -- each index below top order has a fixed Hölder constant independent of
      -- the regularization radius
      let Bconst (m : Fin n → ℕ)
          (hm : (∑ j, m j) < k) : ℝ :=
          ((∑ i : Fin n,
                (∫ z : E n,
                  ‖V ⟨(fun j => m j + if j = i then 1 else 0), by
                    rw [sum_succ_multi]; exact Nat.succ_le_of_lt hm⟩ z‖ ^ p
                     ∂volume) ^ (1/p)) *
            ((volume : Measure (E n)).real (Metric.ball (0 : E n) 1)) ^ (1/q) *
            ((volume : Measure (E n)).real (Metric.ball (0 : E n) 1))⁻¹ *
            (1 + 2 * (2:ℝ)^((n:ℝ)/q)) * (1 / (1 - (n:ℝ)/p)))
      have Bnonneg (m : Fin n → ℕ) (hm : (∑ j, m j) < k) :
          0 ≤ Bconst m hm := by
        dsimp [Bconst]
        have hK : 0 ≤ (volume : Measure (E n)).real
            (Metric.ball (0 : E n) 1) := MeasureTheory.measureReal_nonneg
        have hp' : 0 ≤ (1/p) := by positivity
        have hq' : 0 ≤ (1/q) := by
          have := hpq.right_pos; positivity
        have hsum : 0 ≤ ∑ i : Fin n,
                (∫ z : E n,
                  ‖V ⟨(fun j => m j + if j = i then 1 else 0), by
                    rw [sum_succ_multi]; exact Nat.succ_le_of_lt hm⟩ z‖ ^ p
                     ∂volume) ^ (1/p) := by
          apply Finset.sum_nonneg
          intro i hi
          exact Real.rpow_nonneg (MeasureTheory.integral_nonneg (fun z => by positivity)) _
        have hlast : 0 ≤ 1 / (1 - (n:ℝ)/p) := by positivity
        have hpowtwo : 0 ≤ (2:ℝ)^((n:ℝ)/q) := by positivity
        positivity
      let Cconst (m : Fin n → ℕ) (hm : (∑ j, m j) < k) : NNReal :=
        ⟨Bconst m hm, Bnonneg m hm⟩
      let Ureg (j : ℕ) (m : Fin n → ℕ) (hm : (∑ z, m z) < k) :
          E n → ℝ :=
        MeasureTheory.convolution (V ⟨m, Nat.le_of_lt hm⟩)
          ((φseq j).normed volume) (ContinuousLinearMap.mul ℝ ℝ) volume
      have Uholder (m : Fin n → ℕ) (hm : (∑ z, m z) < k) (j : ℕ) :
          HolderWith (Cconst m hm) τ (Ureg j m hm) := by
        apply MorreySupport.holder_nndist_intro
        intro x y
        apply NNReal.coe_le_coe.mp
        -- express the real inequality already proved above
        have HH := Vmoll_uniform_holder (φseq j) m hm x y
        change dist (Ureg j m hm x) (Ureg j m hm y) ≤
            Bconst m hm * (dist x y) ^ β
        simpa [Ureg, Bconst, β, Real.dist_eq, dist_eq_norm, div_eq_mul_inv] using HH
      -- The missing weak-to-strong step is now a literal dense extension.
      -- In particular for every lower index there is a single continuous
      -- representative, convergence is at every point and on every compact.
      have Vrep : ∀ (m : Fin n → ℕ) (hm : (∑ z, m z) < k),
          ∃ G : E n → ℝ,
            (V ⟨m, Nat.le_of_lt hm⟩ =ᵐ[volume] G) ∧
            HolderWith (Cconst m hm) τ G ∧
            (∀ x, Filter.Tendsto (fun j => Ureg j m hm x)
                Filter.atTop (nhds (G x))) ∧
            (∀ K : Set (E n), IsCompact K →
               TendstoUniformlyOn (fun j => Ureg j m hm) G Filter.atTop K) := by
        intro m hm
        have hae := Vmoll_ae φseq hφout hφratio
            (⟨m, Nat.le_of_lt hm⟩ : I)
        obtain ⟨G,hGV,hGH,hpt⟩ :=
          MorreySupport.holder_ae_limit hτ (Uholder m hm) hae
        refine ⟨G, hGV, hGH, hpt, ?_⟩
        intro K hK
        exact MorreySupport.holder_tendstoUniformlyOn_compact hτ
          (Uholder m hm) hGH hpt hK

      -- the zero member of the array is the original representative; this
      -- follows again from faithfulness, not from any subsequence argument.
      have uVzero : u =ᵐ[volume]
          V (⟨(fun _ : Fin n => (0 : ℕ)), by simp⟩ : I) := by
        apply ae_eq_of_integral_contDiff_smul_eq huLoc
          (Vloc (⟨(fun _ : Fin n => (0 : ℕ)), by simp⟩ : I))
        intro ψ hψ hψc
        have H := Vweak (⟨(fun _ : Fin n => (0 : ℕ)), by simp⟩ : I) ψ hψ hψc
        simp [mixedDeriv] at H
        simpa [mul_comm] using H
      -- In particular the lowest member already supplies the honest C^0
      -- representative (and uniform convergence on compact sets), the piece
      -- of the weak argument that cannot be obtained by a pointwise choice
      -- of a representative.
      have hmlt0 : (∑ j : Fin n, (fun _ : Fin n => (0:ℕ)) j) < k := by
        simp
        exact lt_of_lt_of_le (Nat.zero_lt_succ r) hrk
      obtain ⟨Gzero, hzAE, hzH, hzpt, hzunif⟩ :=
         Vrep (fun _ : Fin n => (0:ℕ)) hmlt0
      have fzero : f =ᵐ[volume] Gzero := hfu.trans (uVzero.trans hzAE)
      choose G Gae Ghold Gpt Gunif using Vrep
      -- Fix representatives simultaneously for the strict lower indices. Uniform
      -- convergence of the neighboring arrays determines their differentials.
      have hstrict {m : Fin n → ℕ} (hm : (∑ i, m i) + 1 < k) :
          (∑ i, m i) < k := lt_trans (Nat.lt_succ_self _) hm
      have hinc {m : Fin n → ℕ} (hm : (∑ i, m i) + 1 < k) (i : Fin n) :
          (∑ j, (m j + if j = i then 1 else 0)) < k := by
        rw [sum_succ_multi]
        exact hm
      have G_deriv : ∀ (m : Fin n → ℕ) (hm : (∑ i, m i) + 1 < k) (x : E n),
          HasFDerivAt (G m (hstrict hm))
            (MorreySupport.coord
              (fun i => G (fun j => m j + if j = i then 1 else 0) (hinc hm i) x)) x := by
        intro m hm x
        let madd : Fin n → Fin n → ℕ := fun i j => m j + if j = i then 1 else 0
        have hstep (j : ℕ) (i : Fin n) (z : E n) :
            fderiv ℝ (Ureg j m (hstrict hm)) z
                 (EuclideanSpace.single i (1:ℝ)) =
                Ureg j (madd i) (hinc hm i) z := by
          exact congrFun (Vmoll_step ((φseq j).normed volume)
              ((φseq j).contDiff_normed) ((φseq j).hasCompactSupport_normed)
              m (hstrict hm) i) z
        apply MorreySupport.hasFDerivAt_limit_coord
          (F:= fun j => Ureg j m (hstrict hm))
          (G:= G m (hstrict hm))
          (a:= fun j i z => Ureg j (madd i) (hinc hm i) z)
          (b:= fun i => G (madd i) (hinc hm i))
          (fun j => (Vmoll_smooth ((φseq j).normed volume)
            ((φseq j).contDiff_normed) ((φseq j).hasCompactSupport_normed) _).of_le (by simp))
          (fun j i z => hstep j i z)
          (fun i K hK => Gunif (madd i) (hinc hm i) K hK)
          (fun z => Gpt m (hstrict hm) z) x

      have G_diff (m : Fin n → ℕ) (hm : (∑ i, m i) + 1 < k) :
          Differentiable ℝ (G m (hstrict hm)) :=
        fun x => (G_deriv m hm x).differentiableAt
      have G_fderiv (m : Fin n → ℕ) (hm : (∑ i, m i) + 1 < k) :
          fderiv ℝ (G m (hstrict hm)) =
            (fun x => MorreySupport.coord
              (fun i => G (fun j => m j + if j = i then 1 else 0) (hinc hm i) x)) := by
        funext x
        exact (G_deriv m hm x).fderiv
      -- All lower members are in fact classically as differentiable as their
      -- number of remaining neighbours. Induction only uses finite sums of
      -- coordinate projections.
      have G_cd : ∀ t : ℕ, ∀ (m : Fin n → ℕ), ∀ hm : (∑ i, m i) + t < k,
          ContDiff ℝ (t : ℕ∞) (G m (by omega)) := by
        intro t
        induction t with
        | zero =>
          intro m hm
          have hh := Ghold m (by simpa using hm)
          -- order zero is continuity
          exact contDiff_zero.mpr (hh.continuous hτ)
        | succ t ih =>
          intro m hm
          have hm1 : (∑ i, m i) + 1 < k := by omega
          have hstrict' : (∑ i, m i) < k := hstrict hm1
          change ContDiff ℝ ((↑(t:ℕ∞) : WithTop ℕ∞) + 1) _
          rw [contDiff_succ_iff_fderiv]
          refine ⟨G_diff m hm1, ?_, ?_⟩
          · intro ht; simp at ht
          rw [G_fderiv m hm1]
          -- commute coordinates with the finite sum definition of `coord`
          change ContDiff ℝ (t : ℕ∞)
            (fun x : E n => ∑ i : Fin n,
              (G (fun j => m j + if j = i then 1 else 0) (hinc hm1 i) x) •
                (EuclideanSpace.proj i : E n →L[ℝ] ℝ))
          apply ContDiff.sum
          intro i hi
          apply ContDiff.smul_const
          have hnext : (∑ j, (m j + if j = i then 1 else 0)) + t < k := by
            rw [sum_succ_multi]
            omega
          exact ih _ hnext
      let mzero : Fin n → ℕ := fun _ => 0
      have hrzero : (∑ i : Fin n, mzero i) + r < k := by
        simp [mzero]
        exact lt_of_lt_of_le (Nat.lt_add_one r) hrk
      have hzero' : (∑ i : Fin n, mzero i) < k := by omega
      let g : E n → ℝ := G mzero hzero'
      have fg : f =ᵐ[volume] g := by
        change f =ᵐ[volume] G mzero hzero'
        have HZ : (⟨mzero, Nat.le_of_lt hzero'⟩ : I) =
              (⟨(fun _ : Fin n => (0:ℕ)), by simp⟩ : I) := by
          apply Subtype.ext; rfl
        refine hfu.trans ?_
        -- identify the weak zero member first, then its continuous lift
        have HV := Gae mzero hzero'
        rw [HZ] at HV
        exact uVzero.trans HV
      have g_cd : ContDiff ℝ (r : ℕ∞) g := G_cd r mzero hrzero
      refine ⟨g, fg, g_cd, ?_⟩
      -- boundedness of every scalar member
      have Gbnd (m : Fin n → ℕ) (hm : (∑ i, m i) < k) :
          ∃ M : ℝ, ∀ x, ‖G m hm x‖ ≤ M := by
        have haev : MemLp (G m hm) (ENNReal.ofReal p) (volume : Measure (E n)) :=
          (memLp_congr_ae (Gae m hm)).1 (VLp ⟨m, Nat.le_of_lt hm⟩)
        exact MorreySupport.holder_memLp_bound hp1 hτ (Ghold m hm) haev
      -- Iterate the finite coordinate decomposition of the derivative.  At
      -- each stage the coefficients are multilinear scalar maps; adjoining
      -- one coordinate is `smulRight` followed by the curry isometry.
      have It : ∀ t : ℕ, ∀ (m : Fin n → ℕ) (hm : (∑ i, m i) + t < k),
          ∃ A : NNReal, ∃ D : ℝ,
            HolderWith A τ
              (fun x => iteratedFDeriv ℝ t (G m (by omega)) x) ∧
            (∀ x, ‖iteratedFDeriv ℝ t (G m (by omega)) x‖ ≤ D) := by
        intro t
        induction t with
        | zero =>
          intro m hm
          have hm0 : (∑ i, m i) < k := by simpa using hm
          obtain ⟨D,hD⟩ := Gbnd m hm0
          let iso := (continuousMultilinearCurryFin0 ℝ (E n) ℝ).symm
          refine ⟨Cconst m hm0, D, ?_, ?_⟩
          · have H := MorreySupport.holder_isometry iso (Ghold m hm0)
            -- zero iterated derivative is the uncurried value
            simpa [iso, iteratedFDeriv, ContinuousMultilinearMap.uncurry0] using H
          · intro x
            have H := MorreySupport.bound_isometry iso (G m hm0) D hD x
            simpa [iso, iteratedFDeriv, ContinuousMultilinearMap.uncurry0] using H
        | succ t ih =>
          intro m hm
          have hm1 : (∑ i, m i) + 1 < k := by omega
          have hm0 : (∑ i, m i) < k := by omega
          let madd : Fin n → Fin n → ℕ := fun i j => m j + if j = i then 1 else 0
          have hadd (i : Fin n) :
              (∑ j, madd i j) = (∑ j, m j) + 1 := by
            dsimp [madd]; exact sum_succ_multi m i
          have hnext (i : Fin n) : (∑ j, madd i j) + t < k := by
            rw [hadd i]; omega
          choose A D hAH hDH using (fun i : Fin n => ih (madd i) (hnext i))
          let Vt (i : Fin n) (x : E n) : E n [×t]→L[ℝ] (E n →L[ℝ] ℝ) :=
              (iteratedFDeriv ℝ t (G (madd i) (by
                have := hnext i; omega)) x).smulRight
                  (EuclideanSpace.proj i : E n →L[ℝ] ℝ)
          let Z (x : E n) : E n [×t]→L[ℝ] (E n →L[ℝ] ℝ) := ∑ i, Vt i x
          have hiH (i : Fin n) :
              HolderWith (A i * ‖(EuclideanSpace.proj i : E n →L[ℝ] ℝ)‖₊) τ (Vt i) := by
            dsimp [Vt]
            apply MorreySupport.holder_smulRight
            exact hAH i
          have hZH : HolderWith (∑ i : Fin n, A i * ‖(EuclideanSpace.proj i : E n →L[ℝ] ℝ)‖₊) τ Z := by
            simpa [Z] using MorreySupport.holder_fin_sum
              (fun i : Fin n => A i * ‖(EuclideanSpace.proj i : E n →L[ℝ] ℝ)‖₊) Vt hiH
          have hiD (i : Fin n) (x : E n) : ‖Vt i x‖ ≤ D i * ‖(EuclideanSpace.proj i : E n →L[ℝ] ℝ)‖ := by
            exact MorreySupport.bound_smulRight
              (EuclideanSpace.proj i : E n →L[ℝ] ℝ)
              (fun z => iteratedFDeriv ℝ t (G (madd i) (by
                have := hnext i; omega)) z) (D i) (hDH i) x
          have hZD : ∀ x, ‖Z x‖ ≤ ∑ i : Fin n, D i * ‖(EuclideanSpace.proj i : E n →L[ℝ] ℝ)‖ := by
            simpa [Z] using MorreySupport.bound_fin_sum Vt
              (fun i : Fin n => D i * ‖(EuclideanSpace.proj i : E n →L[ℝ] ℝ)‖) hiD
          let iso := (continuousMultilinearCurryRightEquiv' ℝ t (E n) ℝ).symm
          have heq : (fun x => iteratedFDeriv ℝ (t+1) (G m hm0) x) =
              (fun x => iso (Z x)) := by
            funext x
            rw [iteratedFDeriv_succ_eq_comp_right]
            change
              ((continuousMultilinearCurryRightEquiv' ℝ t (E n) ℝ).symm
                (iteratedFDeriv ℝ t (fun y => fderiv ℝ (G m hm0) y) x)) = _
            apply congrArg iso
            -- the first derivative is the finite coordinate sum
            have hfd := G_fderiv m hm1
            -- identify indices and use linearity of `iteratedFDeriv`
            have hfun : (fun y => fderiv ℝ (G m hm0) y) =
                (fun z : E n => ∑ i : Fin n,
                  (G (madd i) (by have := hnext i; omega) z) •
                    (EuclideanSpace.proj i : E n →L[ℝ] ℝ)) := by
              funext z
              have hz := congrFun hfd z
              simpa [MorreySupport.coord, madd] using hz
            rw [hfun]
            rw [iteratedFDeriv_sum]
            · simp only [Finset.sum_apply]
              change _ = ∑ i : Fin n, Vt i x
              apply Finset.sum_congr rfl
              intro i hi
              rw [MorreySupport.iterated_smul_const t
                (G (madd i) (by have := hnext i; omega))
                (EuclideanSpace.proj i : E n →L[ℝ] ℝ) x]
              exact (G_cd t (madd i) (hnext i)).contDiffAt
            · intro i hi
              apply ContDiff.smul_const
              exact G_cd t (madd i) (hnext i)
          refine ⟨∑ i : Fin n, A i * ‖(EuclideanSpace.proj i : E n →L[ℝ] ℝ)‖₊,
                    ∑ i : Fin n, D i * ‖(EuclideanSpace.proj i : E n →L[ℝ] ℝ)‖, ?_, ?_⟩
          · rw [heq]
            exact MorreySupport.holder_isometry iso hZH
          · intro x
            change ‖(fun z => iteratedFDeriv ℝ (t+1) (G m hm0) z) x‖ ≤ _
            rw [heq]
            exact MorreySupport.bound_isometry iso Z _ hZD x
      -- initial order r
      obtain ⟨Ar, Dr, hHr, hDr⟩ := It r mzero hrzero
      -- lower the exponent on the last derivative.  If this is the top
      -- available order the gap gives alpha < beta; otherwise one more
      -- bounded derivative makes it Lipschitz.
      have hαnn : 0 < α.toNNReal := by exact Real.toNNReal_pos.mpr _hα
      have topH : ∃ A : NNReal,
          HolderWith A α.toNNReal (iteratedFDeriv ℝ r g) := by
        by_cases hkedge : k = r + 1
        · have haβ : α.toNNReal ≤ τ := by
            apply NNReal.coe_le_coe.mp
            change (α.toNNReal : ℝ) ≤ (τ : ℝ)
            rw [Real.coe_toNNReal _ _hα.le]
            change α ≤ β
            dsimp [β]
            have H := _hgap
            rw [hkedge] at H
            push_cast at H
            linarith
          refine ⟨Ar + (2:NNReal) * ⟨max Dr 0, le_max_right _ _⟩, ?_⟩
          apply holderWith_lowerExponent_of_bounded hHr
          · intro x
            -- convert real bound to nnnorm
            apply NNReal.coe_le_coe.mp
            change ‖iteratedFDeriv ℝ r g x‖ ≤ max Dr 0
            change ‖iteratedFDeriv ℝ r (G mzero hzero') x‖ ≤ max Dr 0
            exact (hDr x).trans (le_max_left _ _)
          · exact hαnn
          · exact haβ
        · have hmextra : (∑ i : Fin n, mzero i) + (r+1) < k := by
            simp [mzero]
            omega
          -- differentiability of the rth iterated derivative and a uniform
          -- bound on its differential imply a global Lipschitz bound.
          -- use t+1 expansion constructed above, and the curry relation.
          obtain ⟨A1,D1,hH1,hD1⟩ := It (r+1) mzero hmextra
          have gmore : ContDiff ℝ ((r+1 : ℕ) : ℕ∞) g := by
            change ContDiff ℝ ((r+1 : ℕ) : ℕ∞) (G mzero hzero')
            exact G_cd (r+1) mzero hmextra
          have hD1' : ∀ x, ‖iteratedFDeriv ℝ (r+1) g x‖ ≤ D1 := by
            intro x
            change ‖iteratedFDeriv ℝ (r+1) (G mzero hzero') x‖ ≤ D1
            exact hD1 x
          have hOne : HolderWith (⟨max D1 0, le_max_right _ _⟩ : NNReal) 1
              (iteratedFDeriv ℝ r g) :=
            MorreySupport.holder_one_iteratedFDeriv_of_bound r g
              gmore D1 hD1'
          have ha1 : α.toNNReal ≤ (1 : NNReal) := by
            -- no truncation occurs since alpha is positive and at most one
            apply NNReal.coe_le_coe.mp
            change (α.toNNReal : ℝ) ≤ (1 : ℝ)
            rw [Real.coe_toNNReal _ _hα.le]
            exact _hα1
          let C1 : NNReal := ⟨max D1 0, le_max_right _ _⟩
          let M0 : NNReal := ⟨max Dr 0, le_max_right _ _⟩
          change ∃ A : NNReal,
            HolderWith A α.toNNReal (iteratedFDeriv ℝ r g)
          refine ⟨C1 + (2:NNReal) * M0, ?_⟩
          have hOne' : HolderWith C1 (1:NNReal)
                         (iteratedFDeriv ℝ r g) := hOne
          apply holderWith_lowerExponent_of_bounded (M:=M0) hOne'

          · intro x
            apply NNReal.coe_le_coe.mp
            change ‖iteratedFDeriv ℝ r g x‖ ≤ max Dr 0
            change ‖iteratedFDeriv ℝ r (G mzero hzero') x‖ ≤ max Dr 0
            exact (hDr x).trans (le_max_left _ _)
          · exact hαnn
          · exact ha1
      refine ⟨topH, ?_⟩
      intro j hj
      have hmj : (∑ i : Fin n, mzero i) + j < k := by
        simp [mzero]
        omega
      obtain ⟨Aj,Dj,hjH,hjD⟩ := It j mzero hmj
      exact ⟨Dj, hjD⟩)/-ResultProofEnd-/
/-ResultEnd-/

end Submission
