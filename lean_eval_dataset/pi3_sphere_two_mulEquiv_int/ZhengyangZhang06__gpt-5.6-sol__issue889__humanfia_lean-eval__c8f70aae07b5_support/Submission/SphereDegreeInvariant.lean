import Submission.SphereDegreeForm

open scoped ContDiff RealInnerProductSpace

noncomputable section

namespace Submission.SphereDegreeInvariant

open Set
open Submission.SphereRegularApprox

variable {m : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : E → Target m} {x : E}

/-- The derivative of a unit-sphere-valued map is orthogonal to its value. -/
theorem inner_fderiv_eq_zero_of_norm_eq_one
    (hF : DifferentiableAt ℝ F x)
    (hnorm : ∀ z, ‖F z‖ = 1) (v : E) :
    inner ℝ (F x) ((fderiv ℝ F x) v) = 0 := by
  have hsq :
      (fun z => ‖F z‖ ^ 2) = (fun _ : E => (1 : ℝ)) := by
    funext z
    rw [hnorm z]
    norm_num
  have hd := hF.hasFDerivAt.norm_sq.fderiv
  rw [hsq, fderiv_const_apply] at hd
  have hv := congrArg (fun L : E →L[ℝ] ℝ => L v) hd
  have htwice :
      (2 : ℝ) * inner ℝ (F x) ((fderiv ℝ F x) v) = 0 := by
    simpa using hv.symm
  linarith

/-- Four (or, generally, `m + 2`) derivative vectors of a map into the
unit `m + 1` sphere are linearly dependent.  Consequently the ambient
determinant form vanishes on them. -/
theorem determinantForm_fderiv_eq_zero_of_norm_eq_one
    (hF : DifferentiableAt ℝ F x)
    (hnorm : ∀ z, ‖F z‖ = 1)
    (v : Fin (m + 2) → E) :
    SphereDegreeForm.determinantForm m
        (fun i => fderiv ℝ F x (v i)) = 0 := by
  let w : Fin (m + 2) → Target m :=
    fun i => fderiv ℝ F x (v i)
  have hw : ¬LinearIndependent ℝ w := by
    intro hli
    have hcard :
        Fintype.card (Fin (m + 2)) =
          Module.finrank ℝ (Target m) := by
      rw [Fintype.card_fin, finrank_euclideanSpace_fin]
    have hspan : Submodule.span ℝ (Set.range w) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank' hcard
    have hle :
        Submodule.span ℝ (Set.range w) ≤
          LinearMap.ker (innerₛₗ ℝ (F x)) := by
      apply Submodule.span_le.mpr
      rintro z ⟨i, rfl⟩
      change inner ℝ (F x) (w i) = 0
      exact inner_fderiv_eq_zero_of_norm_eq_one hF hnorm (v i)
    have hxker : F x ∈ LinearMap.ker (innerₛₗ ℝ (F x)) := by
      apply hle
      rw [hspan]
      trivial
    have hinner : inner ℝ (F x) (F x) = 0 := by
      simpa only [LinearMap.mem_ker, innerₛₗ_apply_apply] using hxker
    rw [real_inner_self_eq_norm_sq, hnorm x] at hinner
    norm_num at hinner
  exact
    (SphereDegreeForm.determinantForm m).toAlternatingMap.map_linearDependent
      w hw

/-- Pull back the radial volume form along an ambient map. -/
def pulledVolumeForm (F : E → Target m) (x : E) :
    E [⋀^Fin (m + 1)]→L[ℝ] ℝ :=
  (SphereDegreeForm.volumeForm m (F x)).compContinuousLinearMap
    (fderiv ℝ F x)

/-- Exterior differentiation commutes with this pullback. -/
theorem extDeriv_pulledVolumeForm
    (hF : ContDiffAt ℝ 2 F x) :
    extDeriv (pulledVolumeForm (m := m) F) x =
      (extDeriv (SphereDegreeForm.volumeForm m) (F x)).compContinuousLinearMap
        (fderiv ℝ F x) := by
  unfold pulledVolumeForm
  simpa only using
    (extDeriv_pullback
      (x := x)
      (SphereDegreeForm.volumeForm m).differentiableAt
      hF
      (by norm_num))

/-- The pullback of the radial volume form along a smooth sphere-valued map
is closed. -/
theorem extDeriv_pulledVolumeForm_eq_zero
    (hF : ContDiffAt ℝ 2 F x)
    (hnorm : ∀ z, ‖F z‖ = 1) :
    extDeriv (pulledVolumeForm (m := m) F) x = 0 := by
  rw [extDeriv_pulledVolumeForm hF]
  rw [SphereDegreeForm.extDeriv_volumeForm]
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.coe_smul, Pi.smul_apply]
  have hzero :
      SphereDegreeForm.determinantForm m
          ((fderiv ℝ F x : E → Target m) ∘ v) = 0 := by
    change
      SphereDegreeForm.determinantForm m
          (fun i => fderiv ℝ F x (v i)) = 0
    exact determinantForm_fderiv_eq_zero_of_norm_eq_one
      (hF.differentiableAt (by norm_num)) hnorm v
  rw [hzero]
  simp

/-- The standard coordinate frame of a real function space. -/
def standardFrame (k : Fin (m + 2)) :
    Fin (m + 2) → ℝ :=
  Pi.single k 1

/-- The signed coefficient of the pulled-back radial volume form obtained by
omitting the `i`-th coordinate vector. -/
def fluxComponent
    (F : (Fin (m + 2) → ℝ) → Target m)
    (i : Fin (m + 2)) (x : Fin (m + 2) → ℝ) : ℝ :=
  (-1 : ℝ) ^ i.val *
    pulledVolumeForm F x (i.removeNth (standardFrame (m := m)))

/-- The cofactor vector field associated to a sphere-valued ambient map. -/
def fluxField
    (F : (Fin (m + 2) → ℝ) → Target m)
    (x : Fin (m + 2) → ℝ) :
    Fin (m + 2) → ℝ :=
  fun i => fluxComponent F i x

theorem differentiable_pulledVolumeForm
    {F : (Fin (m + 2) → ℝ) → Target m}
    (hF : ContDiff ℝ ∞ F) :
    Differentiable ℝ (pulledVolumeForm F) := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ F) :=
    (contDiff_infty_iff_fderiv.mp hF).2
  intro x
  have hform :
      DifferentiableAt ℝ
        (fun y => SphereDegreeForm.volumeForm m (F y)) x :=
    (SphereDegreeForm.volumeForm m).differentiableAt.comp x <|
      (hF.differentiable (by simp)) x
  exact hform.continuousAlternatingMapCompContinuousLinearMap <|
    (hfd.differentiable (by simp)) x

theorem differentiable_fluxField
    {F : (Fin (m + 2) → ℝ) → Target m}
    (hF : ContDiff ℝ ∞ F) :
    Differentiable ℝ (fluxField F) := by
  intro x
  apply differentiableAt_pi.mpr
  intro i
  have hcomponent :
      DifferentiableAt ℝ
        (fun y =>
          pulledVolumeForm F y
            (i.removeNth (standardFrame (m := m)))) x := by
    apply
      ((differentiable_pulledVolumeForm hF) x
        |>.continuousAlternatingMap_apply)
    intro j
    fun_prop
  exact hcomponent.const_mul ((-1 : ℝ) ^ i.val)

/-- The divergence of the cofactor field is the exterior derivative of the
pulled-back radial form. -/
theorem divergence_fluxField
    {F : (Fin (m + 2) → ℝ) → Target m}
    (hF : ContDiff ℝ ∞ F) (x : Fin (m + 2) → ℝ) :
    (∑ i,
        fderiv ℝ (fluxField F) x (standardFrame (m := m) i) i) =
      extDeriv (pulledVolumeForm F) x
        (standardFrame (m := m)) := by
  rw [extDeriv_apply
    ((differentiable_pulledVolumeForm hF) x)]
  apply Finset.sum_congr rfl
  intro i _
  have hcoord :=
    congrArg
      (fun L :
        (Fin (m + 2) → ℝ) →L[ℝ] ℝ =>
          L (standardFrame (m := m) i))
      (fderiv_apply ((differentiable_fluxField hF) x) i)
  have hcomponent :
      DifferentiableAt ℝ
        (fun y =>
          pulledVolumeForm F y
            (i.removeNth (standardFrame (m := m)))) x := by
    apply
      ((differentiable_pulledVolumeForm hF) x
        |>.continuousAlternatingMap_apply)
    intro j
    fun_prop
  have hcoord' :
      fderiv ℝ (fun y => fluxField F y i) x
          (standardFrame (m := m) i) =
        fderiv ℝ (fluxField F) x
          (standardFrame (m := m) i) i := by
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply] using hcoord
  rw [← hcoord']
  simp only [fluxField, fluxComponent]
  rw [← Int.cast_smul_eq_zsmul ℝ]
  simpa only [smul_apply, Int.cast_pow, Int.cast_neg, Int.cast_one] using
    congrArg
      (fun L : (Fin (m + 2) → ℝ) →L[ℝ] ℝ =>
        L (standardFrame (m := m) i))
      (fderiv_const_mul hcomponent ((-1 : ℝ) ^ i.val))

/-- The cofactor field of a smooth sphere-valued map is divergence free. -/
theorem divergence_fluxField_eq_zero
    {F : (Fin (m + 2) → ℝ) → Target m}
    (hF : ContDiff ℝ ∞ F)
    (hnorm : ∀ x, ‖F x‖ = 1)
    (x : Fin (m + 2) → ℝ) :
    ∑ i,
        fderiv ℝ (fluxField F) x (standardFrame (m := m) i) i = 0 := by
  rw [divergence_fluxField hF x,
    extDeriv_pulledVolumeForm_eq_zero
      (hF.contDiffAt.of_le <|
        WithTop.coe_le_coe.mpr
          (show (2 : ℕ∞) ≤ ⊤ from le_top)) hnorm]
  rfl

/-- Divergence-free cofactors have zero total signed flux through a unit
cube. This is the analytic Stokes identity used for homotopy invariance. -/
theorem integral_flux_faces_eq_zero
    {F : (Fin (m + 2) → ℝ) → Target m}
    (hF : ContDiff ℝ ∞ F)
    (hnorm : ∀ x, ‖F x‖ = 1) :
    ∑ i : Fin (m + 2),
        ((∫ x in Set.Icc (0 : Fin (m + 1) → ℝ) 1,
            fluxField F (i.insertNth 1 x) i) -
          ∫ x in Set.Icc (0 : Fin (m + 1) → ℝ) 1,
            fluxField F (i.insertNth 0 x) i) = 0 := by
  let D : (Fin (m + 2) → ℝ) → ℝ :=
    fun x =>
      ∑ i,
        fderiv ℝ (fluxField F) x
          (standardFrame (m := m) i) i
  have hD : D = 0 := by
    funext x
    exact divergence_fluxField_eq_zero hF hnorm x
  have hIntegrable :
      MeasureTheory.IntegrableOn D
        (Set.Icc (0 : Fin (m + 2) → ℝ) 1) := by
    rw [hD]
    exact MeasureTheory.integrableOn_zero
  have hdiv :=
    MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable
      (n := m + 1)
      (a := (0 : Fin (m + 2) → ℝ))
      (b := (1 : Fin (m + 2) → ℝ))
      (by simp)
      (fluxField F)
      (fun x => fderiv ℝ (fluxField F) x)
      (∅ : Set (Fin (m + 2) → ℝ))
      Set.countable_empty
      (differentiable_fluxField hF).continuous.continuousOn
      (fun x _ =>
        ((differentiable_fluxField hF) x).hasFDerivAt)
      hIntegrable
  have hdiv' :
      (∫ x in Set.Icc (0 : Fin (m + 2) → ℝ) 1,
          ∑ i, fderiv ℝ (fluxField F) x
            (standardFrame (m := m) i) i) =
        ∑ i,
          ((∫ x in
                Set.Icc
                  ((0 : Fin (m + 2) → ℝ) ∘ i.succAbove)
                  ((1 : Fin (m + 2) → ℝ) ∘ i.succAbove),
              fluxField F (i.insertNth 1 x) i) -
            ∫ x in
                Set.Icc
                  ((0 : Fin (m + 2) → ℝ) ∘ i.succAbove)
                  ((1 : Fin (m + 2) → ℝ) ∘ i.succAbove),
              fluxField F (i.insertNth 0 x) i) := by
    simpa only [standardFrame, Nat.add_assoc,
      Pi.one_apply, Pi.zero_apply] using hdiv
  have hfaces :
      (∑ i,
          ((∫ x in
                Set.Icc
                  ((0 : Fin (m + 2) → ℝ) ∘ i.succAbove)
                  ((1 : Fin (m + 2) → ℝ) ∘ i.succAbove),
              fluxField F (i.insertNth 1 x) i) -
            ∫ x in
                Set.Icc
                  ((0 : Fin (m + 2) → ℝ) ∘ i.succAbove)
                  ((1 : Fin (m + 2) → ℝ) ∘ i.succAbove),
              fluxField F (i.insertNth 0 x) i)) = 0 := by
    rw [← hdiv']
    change (∫ x in Set.Icc (0 : Fin (m + 2) → ℝ) 1, D x) = 0
    simp [hD]
  simpa only [Function.comp_def, Pi.zero_def, Pi.one_def,
    Pi.one_apply, Pi.zero_apply] using hfaces

end Submission.SphereDegreeInvariant
