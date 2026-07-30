import Submission.Winding

namespace Submission.Separation

open Function Set
open Winding

noncomputable section

/-- The positively scaled standard circle. -/
def scaledCircle (R : ℝ) : C(Circle, ℂ) :=
  ContinuousMap.const Circle (R : ℂ) * circleCoe

@[simp]
theorem scaledCircle_apply (R : ℝ) (z : Circle) :
    scaledCircle R z = (R : ℂ) * (z : ℂ) := rfl

theorem scaledCircle_ne_zero {R : ℝ} (hR : R ≠ 0) (z : Circle) :
    scaledCircle R z ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr hR) (Circle.coe_ne_zero z)

theorem winding_scaledCircle {R : ℝ} (hR : 0 < R) :
    winding (scaledCircle R) (scaledCircle_ne_zero hR.ne') = 1 := by
  let c : C(Circle, ℂ) := ContinuousMap.const Circle (R : ℂ)
  have hc0 (z : Circle) : c z ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hclog : HasLog c :=
    ⟨ContinuousMap.const Circle (Complex.log (R : ℂ)), fun _ ↦
      Complex.exp_log (Complex.ofReal_ne_zero.mpr hR.ne')⟩
  have hcw : winding c hc0 = 0 :=
    (hasLog_iff_winding_eq_zero c hc0).mp hclog
  have hmul := winding_mul c circleCoe hc0 circleCoe_ne_zero
  have hsame : scaledCircle R = c * circleCoe := rfl
  calc
    winding (scaledCircle R) (scaledCircle_ne_zero hR.ne') =
        winding (c * circleCoe)
          (fun z ↦ mul_ne_zero (hc0 z) (circleCoe_ne_zero z)) :=
      winding_congr hsame _ _
    _ = winding c hc0 + winding circleCoe circleCoe_ne_zero := hmul
    _ = 1 := by rw [hcw, winding_circleCoe, zero_add]

theorem winding_scaledCircle_zpow {R : ℝ} (hR : 0 < R) (n : ℤ) :
    winding (zpowMap (scaledCircle R) (scaledCircle_ne_zero hR.ne') n)
      (zpowMap_ne_zero (scaledCircle R) (scaledCircle_ne_zero hR.ne') n) = n := by
  rw [winding_zpow, winding_scaledCircle hR, mul_one]

/-- A nonzero integer power about a point in a bounded open set cannot be
continued nonvanishingly across that set while retaining its boundary values. -/
theorem no_nonzero_extension_over_bounded_open
    (U : Set ℂ) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (x : ℂ) (hx : x ∈ U) (n : ℤ) (hn : n ≠ 0)
    (F : ℂ → ℂ) (hFcont : ContinuousOn F (closure U))
    (hF0 : ∀ z ∈ closure U, F z ≠ 0)
    (hfront : ∀ z ∈ frontier U, F z = (z - x) ^ n) : False := by
  classical
  have hxnot : x ∉ closure Uᶜ := by
    rw [closure_compl, hU.interior_eq]
    simpa using hx
  have hpow : ContinuousOn (fun z : ℂ ↦ (z - x) ^ n) (closure Uᶜ) :=
    (continuous_id.sub continuous_const).continuousOn.zpow₀ n fun z hz ↦
      Or.inl (sub_ne_zero.mpr fun hzx ↦ hxnot (hzx ▸ hz))
  let Kfun : ℂ → ℂ := U.piecewise F (fun z ↦ (z - x) ^ n)
  have hKcont : Continuous Kfun := by
    exact continuous_piecewise hfront hFcont hpow
  let K : C(ℂ, ℂ) := ⟨Kfun, hKcont⟩
  have hK0 (z : ℂ) : K z ≠ 0 := by
    by_cases hz : z ∈ U
    · simpa [K, Kfun, Set.piecewise, hz] using hF0 z (subset_closure hz)
    · change Kfun z ≠ 0
      rw [show Kfun z = (z - x) ^ n by simp [Kfun, hz]]
      exact zpow_ne_zero n (sub_ne_zero.mpr fun hzx ↦ hz (hzx.symm ▸ hx))
  obtain ⟨L, hL, _hLuniq⟩ :=
    Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts K
      (a₀ := (0 : ℂ)) (e₀ := Complex.log (K 0))
      (Complex.exp_log (hK0 0)) (fun z ↦ hK0 z)
  have hLexp (z : ℂ) : Complex.exp (L z) = K z := by
    exact congrFun hL.2 z
  obtain ⟨R, hRsub⟩ := hUb.closure.subset_ball x
  have hR : 0 < R := by
    have := hRsub (subset_closure hx)
    simpa only [Metric.mem_ball, dist_self] using this
  let b : C(Circle, ℂ) :=
    ContinuousMap.const Circle x + scaledCircle R
  have hbnot (z : Circle) : b z ∉ U := by
    intro hb
    have hball := hRsub (subset_closure hb)
    have hdist : dist x (b z) = R := by
      rw [dist_eq_norm]
      simp [b, abs_of_pos hR]
    rw [Metric.mem_ball, dist_comm, hdist] at hball
    exact (lt_irrefl R) hball
  let g : C(Circle, ℂ) := K.comp b
  have hg0 (z : Circle) : g z ≠ 0 := hK0 (b z)
  have hglog : HasLog g := by
    refine ⟨L.comp b, ?_⟩
    intro z
    simpa only [g, ContinuousMap.coe_comp, Function.comp_apply] using hLexp (b z)
  have hgw : winding g hg0 = 0 :=
    (hasLog_iff_winding_eq_zero g hg0).mp hglog
  have hgmap : g = zpowMap (scaledCircle R) (scaledCircle_ne_zero hR.ne') n := by
    ext z
    change Kfun (b z) = (scaledCircle R z) ^ n
    rw [show Kfun (b z) = (b z - x) ^ n by
      simp [Kfun, hbnot z]]
    congr 1
    simp [b]
  have hw := winding_congr hgmap hg0
    (zpowMap_ne_zero (scaledCircle R) (scaledCircle_ne_zero hR.ne') n)
  rw [hgw, winding_scaledCircle_zpow hR n] at hw
  exact hn hw.symm

end

end Submission.Separation
