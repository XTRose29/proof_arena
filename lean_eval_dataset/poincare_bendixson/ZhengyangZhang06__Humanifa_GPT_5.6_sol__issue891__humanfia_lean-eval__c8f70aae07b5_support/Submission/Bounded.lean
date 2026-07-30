import Submission.Factorization

namespace Submission.Bounded

open Function Set
open Winding Factorization Existence

noncomputable section

theorem HasLog.mul {u v : C(Circle, ℂ)} (hu : HasLog u) (hv : HasLog v) :
    HasLog (u * v) := by
  obtain ⟨l, hl⟩ := hu
  obtain ⟨m, hm⟩ := hv
  refine ⟨l + m, fun z ↦ ?_⟩
  simp only [ContinuousMap.add_apply, ContinuousMap.mul_apply, Complex.exp_add, hl, hm]

theorem hasLog_finsetProd {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (u : ι → C(Circle, ℂ)) (hu : ∀ i ∈ S, HasLog (u i)) :
    HasLog (∏ i ∈ S, u i) := by
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨0, ?_⟩
      simp
  | @insert a S ha ih =>
      rw [Finset.prod_insert ha]
      apply HasLog.mul
      · exact hu a (by simp)
      · exact ih fun i hi ↦ hu i (by simp [hi])

/-- A loop uniformly less than one unit from the tautological circle has winding one. -/
theorem winding_eq_one_of_close (u : C(Circle, ℂ))
    (hclose : ∀ z, ‖u z - (z : ℂ)‖ < 1) :
    ∃ hu0 : ∀ z, u z ≠ 0, winding u hu0 = 1 := by
  have hu0 (z : Circle) : u z ≠ 0 := by
    intro huz
    have hz := hclose z
    rw [huz, zero_sub, norm_neg] at hz
    have hnorm : ‖(z : ℂ)‖ = 1 := Circle.norm_coe z
    rw [hnorm] at hz
    exact (lt_irrefl 1) hz
  let q : C(Circle, ℂ) :=
    ⟨fun z ↦ 1 + (u z - (z : ℂ)) / (z : ℂ),
      continuous_const.add
        ((u.continuous.sub continuous_subtype_val).div₀ continuous_subtype_val
          (fun z ↦ Circle.coe_ne_zero z))⟩
  have hqsmall (z : Circle) : ‖(u z - (z : ℂ)) / (z : ℂ)‖ < 1 := by
    simpa [norm_div] using hclose z
  have hqslit (z : Circle) : q z ∈ Complex.slitPlane := by
    exact Complex.mem_slitPlane_of_norm_lt_one (hqsmall z)
  have hq0 (z : Circle) : q z ≠ 0 :=
    Complex.slitPlane_ne_zero (hqslit z)
  have hqlog : HasLog q :=
    ⟨⟨fun z ↦ Complex.log (q z), q.continuous.clog hqslit⟩,
      fun z ↦ Complex.exp_log (hq0 z)⟩
  have hqwind : winding q hq0 = 0 :=
    (hasLog_iff_winding_eq_zero q hq0).mp hqlog
  have humap : u = circleCoe * q := by
    ext z
    change u z = (z : ℂ) * (1 + (u z - (z : ℂ)) / (z : ℂ))
    field_simp [Circle.coe_ne_zero z]
    ring
  refine ⟨hu0, ?_⟩
  calc
    winding u hu0 = winding (circleCoe * q)
        (fun z ↦ mul_ne_zero (circleCoe_ne_zero z) (hq0 z)) :=
      winding_congr humap hu0 _
    _ = winding circleCoe circleCoe_ne_zero + winding q hq0 :=
      winding_mul circleCoe q circleCoe_ne_zero hq0
    _ = 1 := by rw [winding_circleCoe, hqwind, add_zero]

/-- An embedded circle in the complex plane has a bounded complementary component. -/
theorem exists_isBounded_connectedComponentIn_compl_range
    (r : C(Circle, ℂ)) (hinj : Function.Injective r) :
    ∃ x ∈ (Set.range r)ᶜ,
      Bornology.IsBounded (connectedComponentIn (Set.range r)ᶜ x) := by
  classical
  obtain ⟨ra⟩ := exists_regularApproximation r hinj
  let F : ℂ → ℂ := fun z ↦ ra.g z - ra.a
  let S : Finset ℂ := ra.roots_finite.toFinset
  let A : ℂ → ℂ ≃L[ℝ] ℂ := fun x ↦
    if hx : ra.g x = ra.a then
      (fderiv ℝ ra.g x).toContinuousLinearEquivOfDetNeZero (ra.regular x hx)
    else
      ContinuousLinearEquiv.refl ℝ ℂ
  have hF : Continuous F := ra.smooth'.continuous.sub continuous_const
  have hzeros (z : ℂ) : F z = 0 ↔ z ∈ S := by
    simp [F, S, sub_eq_zero]
  have hderiv (x : ℂ) (hx : x ∈ S) :
      HasFDerivAt F (A x : ℂ →L[ℝ] ℂ) x := by
    have hxroot : ra.g x = ra.a := by simpa [S] using hx
    have hg : HasFDerivAt ra.g (fderiv ℝ ra.g x) x :=
      (ra.smooth'.differentiable (by simp) x).hasFDerivAt
    simpa [F, A, hxroot] using hg.sub_const ra.a
  let Q : C(ℂ, ℂ) :=
    ⟨residual F S A, continuous_residual F S A hF hzeros hderiv⟩
  have hQ0 (z : ℂ) : Q z ≠ 0 := by
    exact residual_ne_zero F S A hzeros z
  let factor (x : ℂ) : C(Circle, ℂ) :=
    ⟨fun z ↦ A x (r z - x),
      (A x).continuous.comp (r.continuous.sub continuous_const)⟩
  let u : C(Circle, ℂ) :=
    ⟨fun z ↦ F (r z), hF.comp r.continuous⟩
  have huclose (z : Circle) : ‖u z - (z : ℂ)‖ < 1 := by
    simpa [u, F] using ra.close_on_curve z
  obtain ⟨hu0, huwinding⟩ := winding_eq_one_of_close u huclose
  have hufactor : u = Q.comp r * ∏ x ∈ S, factor x := by
    ext z
    simpa [u, Q, factor, linearProduct] using
      (residual_mul_linearProduct F S A hzeros (r z)).symm
  by_contra hb
  push Not at hb
  have hfactorLog (x : ℂ) (hx : x ∈ S) : HasLog (factor x) := by
    have hxroot : ra.g x = ra.a := by simpa [S] using hx
    have hxcompl : x ∈ (Set.range r)ᶜ := by
      rw [Set.mem_compl_iff]
      rintro ⟨z, hxz⟩
      have hgr : ra.g (r z) = ra.a := by rw [hxz]; exact hxroot
      have hc := ra.close_on_curve z
      rw [hgr, sub_self, zero_sub, norm_neg] at hc
      have hnorm : ‖(z : ℂ)‖ = 1 := Circle.norm_coe z
      rw [hnorm] at hc
      exact (lt_irrefl 1) hc
    have hwzero : windingAround r x hxcompl = 0 :=
      windingAround_eq_zero_of_not_isBounded_component r hxcompl (hb x hxcompl)
    have haround : HasLog (aroundMap r x) :=
      (hasLog_iff_winding_eq_zero (aroundMap r x)
        (aroundMap_ne_zero r hxcompl)).mpr hwzero
    obtain ⟨l, hl⟩ :=
      Submission.Existence.HasLog.comp_continuousLinearEquiv haround (A x)
    refine ⟨l, fun z ↦ ?_⟩
    simpa [factor, aroundMap] using hl z
  have hQlog : HasLog (Q.comp r) :=
    hasLog_comp_of_global Q hQ0 r
  have hproductLog : HasLog (∏ x ∈ S, factor x) :=
    hasLog_finsetProd S factor hfactorLog
  have hulog : HasLog u := by
    rw [hufactor]
    exact Submission.Bounded.HasLog.mul hQlog hproductLog
  have huzero : winding u hu0 = 0 :=
    (hasLog_iff_winding_eq_zero u hu0).mp hulog
  exact one_ne_zero (huwinding.symm.trans huzero)

theorem jordan_curve_complex (r : C(Circle, ℂ)) (hinj : Function.Injective r) :
    Nat.card (ConnectedComponents ((Set.range r)ᶜ : Set ℂ)) = 2 := by
  apply JordanHelpers.natCard_connectedComponents_compl_range_eq_two_of_bounded_component
  · rw [Complex.rank_real_complex]
    norm_num
  · exact r.continuous
  · exact exists_isBounded_connectedComponentIn_compl_range r hinj
  · intro x hx y hy hxb hyb
    exact Components.bounded_components_eq r hinj hx hy hxb hyb

end

end Submission.Bounded
