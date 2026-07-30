import Submission.Helpers
import Submission.MoserInvariant

open Set Function Matrix Metric Filter
open scoped ContDiff NNReal Topology
open LeanEval.Geometry.Darboux

namespace Submission.Darboux

noncomputable section

universe u

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

def affineHomeomorph (x : V) (e : V ≃L[ℝ] V) : V ≃ₜ V where
  toFun := Submission.LocalForms.affineMap x e
  invFun := fun y => e.symm (y - x)
  left_inv := by
    intro y
    simp [Submission.LocalForms.affineMap]
  right_inv := by
    intro y
    simp [Submission.LocalForms.affineMap]
  continuous_toFun := (Submission.LocalForms.affineMap_contDiff x e).continuous
  continuous_invFun := by
    have h : ContDiff ℝ ∞ (fun y : V => e.symm (y - x)) :=
      e.symm.contDiff.comp (contDiff_id.sub contDiff_const)
    exact h.continuous

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in theorem pair_eq (v : Fin 2 → V) :
    ![v 0, v 1] = v := by
  funext i
  fin_cases i <;> rfl

theorem darboux {n : ℕ} {U : Set (E n)} (hU : IsOpen U)
    (α : E n → E n [⋀^Fin 2]→L[ℝ] ℝ) (hα : IsSymplecticOn α U)
    {x : E n} (hx : x ∈ U) :
    ∃ φ : OpenPartialHomeomorph (E n) (E n),
      x ∈ φ.source ∧ φ.source ⊆ U ∧
      ContDiffOn ℝ ∞ (φ : E n → E n) φ.source ∧
      ContDiffOn ℝ ∞ (φ.symm : E n → E n) φ.target ∧
      ∀ z ∈ φ.target,
        IsDarbouxNormal
          ((α (φ.symm z)).compContinuousLinearMap
            (fderiv ℝ (φ.symm : E n → E n) z)) := by
  cases n with
  | zero =>
      exact Submission.Helpers.darbouxZero hU α x hx
  | succ n =>
      rcases hα with ⟨hαsmooth, hαclosed, hαnondeg⟩
      obtain ⟨e, heNormal⟩ := Submission.LinearNormal.exists_linear_normal
        (α x) (hαnondeg x hx)
      let D : Set (E (n + 1)) := Submission.LocalForms.coordinateDomain U x e
      let γ : E (n + 1) → E (n + 1) [⋀^Fin 2]→L[ℝ] ℝ :=
        Submission.LocalForms.normalizedForm α x e
      have hD : IsOpen D := by
        exact Submission.LocalForms.isOpen_coordinateDomain hU x e
      have h0D : (0 : E (n + 1)) ∈ D := by
        exact Submission.LocalForms.zero_mem_coordinateDomain hx e
      have hγ : ContDiffOn ℝ ∞ γ D := by
        exact Submission.LocalForms.normalizedForm_contDiffOn α hαsmooth x e
      have hγclosed : ∀ z ∈ D, extDeriv γ z = 0 := by
        intro z hz
        exact Submission.LocalForms.normalizedForm_closed
          hU α hαsmooth hαclosed x e z hz
      let ω₀ : E (n + 1) [⋀^Fin 2]→L[ℝ] ℝ := γ 0
      have hω₀Normal : IsDarbouxNormal ω₀ := by
        simpa [ω₀, γ, Submission.LocalForms.normalizedForm_zero] using heNormal
      have hω₀Nondeg : ∀ v : E (n + 1), v ≠ 0 →
          ∃ w : E (n + 1), ω₀ ![v, w] ≠ 0 := by
        simpa [ω₀, γ] using
          (Submission.LocalForms.normalizedForm_zero_nondegenerate
            α hαnondeg hx e)
      obtain ⟨global, r, hr, hglobal, hglobalEq, hglobalClosed, hrD⟩ :=
        Submission.LocalForms.exists_global_smooth_germ
          hD h0D γ hγ hγclosed
      let δ : E (n + 1) → E (n + 1) [⋀^Fin 2]→L[ℝ] ℝ := fun z =>
        global z - ω₀
      have hδ : ContDiff ℝ ∞ δ := by
        exact hglobal.sub contDiff_const
      have hδ0 : δ 0 = 0 := by
        have hg0 := hglobalEq (mem_ball_self hr)
        simp [δ, ω₀, hg0]
      have hδclosed : ∀ z ∈ ball (0 : E (n + 1)) r,
          extDeriv δ z = 0 := by
        intro z hz
        have hgdiff : DifferentiableAt ℝ global z :=
          hglobal.differentiable (by simp) z
        have hfun : δ = fun y => global y + (-ω₀) := by
          funext y
          exact sub_eq_add_neg _ _
        rw [hfun, extDeriv_fun_add hgdiff (differentiableAt_const (c := -ω₀)),
          hglobalClosed z hz]
        ext vec
        simp [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
      obtain ⟨f, ρ, hρ, L, K, hf, hfield, hinv, hzero, hbound, hlip⟩ :=
        Submission.MoserGlobal.exists_global_moserField
          ω₀ hω₀Nondeg δ hδ hδ0
      let R := min r ρ
      have hR : 0 < R := lt_min hr hρ
      let σ := R / Real.exp (K : ℝ)
      have hσ : 0 < σ := div_pos hR (Real.exp_pos _)
      let W : Set (E (n + 1)) := ball 0 σ
      have hW : IsOpen W := isOpen_ball
      have h0W : (0 : E (n + 1)) ∈ W := mem_ball_self hσ
      let flow := Submission.MoserGlobal.unitFlow f hf L K hbound hlip
      let H : E (n + 1) → E (n + 1) :=
        Submission.MoserSmoothFlow.unitTimeOneMap f hf L K hbound hlip
      have hflowR : ∀ y ∈ W, ∀ t : Icc (0 : ℝ) 1, flow t y ∈ ball 0 R := by
        intro y hy t
        rw [mem_ball, dist_zero_right]
        have hle := Submission.MoserInvariant.unitFlow_norm_le_exp
          f hf L K hbound hlip hzero y t
        have hynorm : ‖y‖ < σ := by
          simpa [W, mem_ball, dist_zero_right] using hy
        have hlt : ‖y‖ * Real.exp (K : ℝ) < R := by
          apply (lt_div_iff₀ (Real.exp_pos (K : ℝ))).mp
          simpa [σ] using hynorm
        exact hle.trans_lt hlt
      have hflowr : ∀ y ∈ W, ∀ t : Icc (0 : ℝ) 1, flow t y ∈ ball 0 r := by
        intro y hy t
        have h := hflowR y hy t
        rw [mem_ball] at h ⊢
        exact h.trans_le (min_le_left r ρ)
      have hflowρ : ∀ y ∈ W, ∀ t : Icc (0 : ℝ) 1, flow t y ∈ ball 0 ρ := by
        intro y hy t
        have h := hflowR y hy t
        rw [mem_ball] at h ⊢
        exact h.trans_le (min_le_right r ρ)
      have hcoordFlow : ∀ y ∈ W, ∀ t : Icc (0 : ℝ) 1, ∀ u v : E (n + 1),
          δ (flow t y) ![u, v] +
              (t : ℝ) * fderiv ℝ δ (flow t y) (f t (flow t y)) ![u, v] +
              Submission.MoserField.formPath ω₀ δ (t, flow t y)
                ![Submission.MoserFlow.spaceFDeriv f (t, flow t y) u, v] +
              Submission.MoserField.formPath ω₀ δ (t, flow t y)
                ![u, Submission.MoserFlow.spaceFDeriv f (t, flow t y) v] = 0 := by
        intro y hy t u v
        exact Submission.MoserInvariant.moser_coordinate_identity_of_mem
          ω₀ δ hδ r ρ hδclosed f hf hfield hinv t (flow t y)
            (hflowr y hy t) (hflowρ y hy t) u v
      have hHpull : ∀ y ∈ W,
          (γ (H y)).compContinuousLinearMap (fderiv ℝ H y) = ω₀ := by
        intro y hy
        have hpull := Submission.MoserInvariant.unitTimeOneMap_pullback_eq
          ω₀ δ hδ f hf L K hbound hlip y (hcoordFlow y hy)
        have hgend : global (H y) = γ (H y) := by
          apply hglobalEq
          simpa [H, flow, Submission.MoserSmoothFlow.unitTimeOneMap] using
            hflowr y hy Submission.MoserSmoothFlow.unitEndTime
        have hformOne : Submission.MoserField.formPath ω₀ δ (1, H y) = γ (H y) := by
          simp [Submission.MoserField.formPath, δ, hgend]
        rw [hformOne] at hpull
        have hformZero : Submission.MoserField.formPath ω₀ δ (0, y) = ω₀ := by
          simp [Submission.MoserField.formPath]
        rw [hformZero] at hpull
        ext vec
        simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
        rw [← pair_eq vec]
        have hcomp : fderiv ℝ H y ∘ ![vec 0, vec 1] =
            ![fderiv ℝ H y (vec 0), fderiv ℝ H y (vec 1)] := by
          funext i
          fin_cases i <;> rfl
        rw [hcomp]
        exact hpull (vec 0) (vec 1)
      let Hhomeo : E (n + 1) ≃ₜ E (n + 1) :=
        Submission.MoserDiffeomorph.timeOneHomeomorph f hf L K hbound hlip
      let A : E (n + 1) ≃ₜ E (n + 1) := affineHomeomorph x e
      let Fhomeo : E (n + 1) ≃ₜ E (n + 1) := Hhomeo.trans A
      have hFfun : (Fhomeo : E (n + 1) → E (n + 1)) =
          Submission.LocalForms.affineMap x e ∘ H := by
        funext y
        rfl
      let ψ : OpenPartialHomeomorph (E (n + 1)) (E (n + 1)) :=
        Fhomeo.toOpenPartialHomeomorph.restrOpen W hW
      let φ : OpenPartialHomeomorph (E (n + 1)) (E (n + 1)) := ψ.symm
      have hHsmooth : ContDiff ℝ ∞ H :=
        Submission.MoserSmoothFlow.unitTimeOneMap_contDiff
          f hf L K hbound hlip
      have hH0 : H 0 = 0 := by
        exact Submission.MoserGlobal.unitFlow_eq_of_equilibrium
          f hf L K hbound hlip hzero Submission.MoserSmoothFlow.unitEndTime
      have hFsmooth : ContDiff ℝ ∞ (Fhomeo : E (n + 1) → E (n + 1)) := by
        rw [hFfun]
        exact (Submission.LocalForms.affineMap_contDiff x e).comp hHsmooth
      have hAinv : ContDiff ℝ ∞ (fun y : E (n + 1) => e.symm (y - x)) :=
        e.symm.contDiff.comp (contDiff_id.sub contDiff_const)
      have hHinv : ContDiff ℝ ∞
          (Submission.MoserDiffeomorph.backwardMap f hf L K hbound hlip) :=
        Submission.MoserSmoothFlow.unitTimeOneMap_contDiff
          (Submission.MoserDiffeomorph.reverseField f)
          (Submission.MoserDiffeomorph.reverseField_contDiff f hf) L K
          (Submission.MoserDiffeomorph.reverseField_norm_le f L hbound)
          (Submission.MoserDiffeomorph.reverseField_lipschitz f K hlip)
      have hFinv : ContDiff ℝ ∞ (Fhomeo.symm : E (n + 1) → E (n + 1)) := by
        have hFinvfun : (Fhomeo.symm : E (n + 1) → E (n + 1)) =
            Submission.MoserDiffeomorph.backwardMap f hf L K hbound hlip ∘
              fun y => e.symm (y - x) := by
          funext y
          rfl
        rw [hFinvfun]
        exact hHinv.comp hAinv
      have h0source : (0 : E (n + 1)) ∈ ψ.source := by
        simpa [ψ] using h0W
      have hψ0 : ψ 0 = x := by
        change Submission.LocalForms.affineMap x e
          (Submission.MoserDiffeomorph.forwardMap f hf L K hbound hlip 0) = x
        have hforward0 : Submission.MoserDiffeomorph.forwardMap
            f hf L K hbound hlip 0 = 0 := hH0
        rw [hforward0]
        simp [Submission.LocalForms.affineMap]
      refine ⟨φ, ?_, ?_, ?_, ?_, ?_⟩
      · change x ∈ ψ.target
        rw [← hψ0]
        exact ψ.mapsTo h0source
      · intro y hy
        change y ∈ ψ.target at hy
        let z := ψ.symm y
        have hzsource : z ∈ ψ.source := ψ.mapsTo_symm hy
        have hzW : z ∈ W := by
          simpa [ψ, z] using hzsource
        have hzD : H z ∈ D := hrD (hflowr z hzW Submission.MoserSmoothFlow.unitEndTime)
        have hyEq : ψ z = y := ψ.right_inv hy
        rw [← hyEq]
        have hψz : ψ z = Submission.LocalForms.affineMap x e (H z) := by
          change Fhomeo z = Submission.LocalForms.affineMap x e (H z)
          exact congrFun hFfun z
        rw [hψz]
        exact hzD
      · simpa [φ, ψ] using hFinv.contDiffOn
      · simpa [φ, ψ] using hFsmooth.contDiffOn
      · intro z hz
        have hzW : z ∈ W := by
          simpa [φ, ψ] using hz
        have hFapply : Fhomeo z = Submission.LocalForms.affineMap x e (H z) := by
          exact congrFun hFfun z
        have hFderiv : fderiv ℝ (Fhomeo : E (n + 1) → E (n + 1)) z =
            e.toContinuousLinearMap.comp (fderiv ℝ H z) := by
          rw [hFfun]
          rw [fderiv_comp z
            ((Submission.LocalForms.affineMap_contDiff x e).differentiable (by simp) (H z))
            (hHsmooth.differentiable (by simp) z),
            Submission.LocalForms.fderiv_affineMap]
        have hformEq :
            (α (Submission.LocalForms.affineMap x e (H z))).compContinuousLinearMap
                (e.toContinuousLinearMap.comp (fderiv ℝ H z)) =
              (γ (H z)).compContinuousLinearMap (fderiv ℝ H z) := by
          ext vec
          simp [γ, Submission.LocalForms.normalizedForm,
            ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def]
        change IsDarbouxNormal
          ((α ((Fhomeo : E (n + 1) → E (n + 1)) z)).compContinuousLinearMap
            (fderiv ℝ (Fhomeo : E (n + 1) → E (n + 1)) z))
        rw [hFapply, hFderiv]
        rw [hformEq, hHpull z hzW]
        exact hω₀Normal

end

end Submission.Darboux
