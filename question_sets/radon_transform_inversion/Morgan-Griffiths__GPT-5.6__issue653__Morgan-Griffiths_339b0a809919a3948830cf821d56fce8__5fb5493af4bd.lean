import Mathlib

namespace Submission

namespace LeanEval.Analysis.RadonTransform

/-!
# The Radon transform: Fourier-slice diagonalization and pseudo-inversion

`radon_can_be_diagonalized_and_pseudo_inverted`: the Fourier slice theorem
(`fourier1` of `radon φ(·,θ)` equals a 2D-Fourier slice of `φ`), together with
the existence of a left inverse of the Radon transform on Schwartz functions.
The trusted helpers (`radon`, `fourier1`, `fourier2`) are non-holes. Mathlib
has the 1D/2D Fourier transforms and Schwartz space but no Radon transform,
Fourier slice theorem, or filtered back-projection.

Category-(b) candidate from §100 of the Knill survey.
-/

open MeasureTheory Real Complex

/-- The **Radon transform** of `f : ℝ × ℝ → ℂ` at `(p, θ)`: the integral of `f`
along the line `x cos θ + y sin θ = p`. -/
noncomputable def radon (f : ℝ × ℝ → ℂ) (pθ : ℝ × ℝ) : ℂ :=
  ∫ t : ℝ, f (pθ.1 * Real.cos pθ.2 - t * Real.sin pθ.2,
              pθ.1 * Real.sin pθ.2 + t * Real.cos pθ.2)

/-- 1D Fourier transform (mathlib's `2π i` convention). -/
noncomputable def fourier1 (g : ℝ → ℂ) (k : ℝ) : ℂ :=
  ∫ p : ℝ, Complex.exp (-(2 * Real.pi * p * k) * Complex.I) * g p

/-- 2D Fourier transform of `f : ℝ × ℝ → ℂ` at `(k₁, k₂)`. -/
noncomputable def fourier2 (f : ℝ × ℝ → ℂ) (k : ℝ × ℝ) : ℂ :=
  ∫ x : ℝ × ℝ,
    Complex.exp (-(2 * Real.pi * (x.1 * k.1 + x.2 * k.2)) * Complex.I) * f x



end LeanEval.Analysis.RadonTransform

open LeanEval.Analysis.RadonTransform
open MeasureTheory Real Complex
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/


noncomputable def rotLE (θ : ℝ) : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) where
  toFun := fun z => (z.1 * Real.cos θ - z.2 * Real.sin θ,
                     z.1 * Real.sin θ + z.2 * Real.cos θ)
  invFun := fun z => (z.1 * Real.cos θ + z.2 * Real.sin θ,
                     - z.1 * Real.sin θ + z.2 * Real.cos θ)
  left_inv := by
    rintro ⟨x,y⟩
    dsimp
    have h := Real.sin_sq_add_cos_sq θ
    apply Prod.ext
    · dsimp
      calc
        (x * Real.cos θ - y * Real.sin θ) * Real.cos θ +
            (x * Real.sin θ + y * Real.cos θ) * Real.sin θ =
            x * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
        _ = x := by rw [h]; ring
    · dsimp
      calc
        -(x * Real.cos θ - y * Real.sin θ) * Real.sin θ +
            (x * Real.sin θ + y * Real.cos θ) * Real.cos θ =
            y * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
        _ = y := by rw [h]; ring
  right_inv := by
    rintro ⟨x,y⟩
    dsimp
    have h := Real.sin_sq_add_cos_sq θ
    apply Prod.ext
    · dsimp
      calc
        (x * Real.cos θ + y * Real.sin θ) * Real.cos θ -
            (-x * Real.sin θ + y * Real.cos θ) * Real.sin θ =
            x * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
        _ = x := by rw [h]; ring
    · dsimp
      calc
        (x * Real.cos θ + y * Real.sin θ) * Real.sin θ +
            (-x * Real.sin θ + y * Real.cos θ) * Real.cos θ =
            y * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
        _ = y := by rw [h]; ring
  map_add' := by
    rintro ⟨x,y⟩ ⟨u,v⟩
    apply Prod.ext <;> dsimp <;> ring
  map_smul' := by
    rintro c ⟨x,y⟩
    apply Prod.ext <;> dsimp <;> ring

lemma rotLE_apply (θ : ℝ) (z : ℝ × ℝ) :
    rotLE θ z = (z.1 * Real.cos θ - z.2 * Real.sin θ,
                     z.1 * Real.sin θ + z.2 * Real.cos θ) := rfl

noncomputable def basisProd : Module.Basis (Fin 2) ℝ (ℝ × ℝ) :=
  (Pi.basisFun ℝ (Fin 2)).map (LinearEquiv.finTwoArrow ℝ ℝ)

lemma basisProd_apply_zero : basisProd (0 : Fin 2) = ((1:ℝ), (0:ℝ)) := by
  simp [basisProd, Module.Basis.map_apply, Pi.basisFun_apply,
        LinearEquiv.finTwoArrow_apply, Pi.single_apply]
lemma basisProd_apply_one : basisProd (1 : Fin 2) = ((0:ℝ), (1:ℝ)) := by
  simp [basisProd, Module.Basis.map_apply, Pi.basisFun_apply,
        LinearEquiv.finTwoArrow_apply, Pi.single_apply]

lemma basisProd_repr_zero (z : ℝ × ℝ) : (basisProd.repr z) (0 : Fin 2) = z.1 := by
  simp [basisProd, Module.Basis.map_repr, Pi.basisFun_repr,
        LinearEquiv.finTwoArrow_symm_apply]
lemma basisProd_repr_one (z : ℝ × ℝ) : (basisProd.repr z) (1 : Fin 2) = z.2 := by
  simp [basisProd, Module.Basis.map_repr, Pi.basisFun_repr,
        LinearEquiv.finTwoArrow_symm_apply]

lemma rotLE_det (θ : ℝ) : LinearMap.det (rotLE θ : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) = 1 := by
  classical
  rw [← LinearMap.det_toMatrix basisProd]
  rw [Matrix.det_fin_two]
  -- unfold entries
  simp [LinearMap.toMatrix_apply, basisProd_apply_zero,
        basisProd_apply_one, basisProd_repr_zero, basisProd_repr_one, rotLE_apply]
  nlinarith [Real.sin_sq_add_cos_sq θ]

lemma rotLE_measurePreserving (θ : ℝ) :
    MeasurePreserving (rotLE θ) (volume : Measure (ℝ × ℝ)) volume := by
  -- measurability and determinant one
  refine ⟨((rotLE θ : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)).continuous_of_finiteDimensional).measurable, ?_⟩
  change Measure.map ((rotLE θ : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) : (ℝ × ℝ) → (ℝ × ℝ)) volume = volume
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (ℝ × ℝ)) (by rw [rotLE_det]; exact one_ne_zero)]
  rw [rotLE_det]
  norm_num

lemma rotLE_measurableEmbedding (θ : ℝ) : MeasurableEmbedding (rotLE θ : (ℝ × ℝ) → ℝ × ℝ) := by
  exact ((rotLE θ).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding)


lemma phase_norm (r : ℝ) : ‖Complex.exp ((r : ℂ) * Complex.I)‖ = (1 : ℝ) := by
  rw [Complex.norm_exp, Complex.mul_re]
  simp
lemma phase_cont (c : ℝ) :
    Continuous (fun z : ℝ × ℝ =>
      Complex.exp ((-(2 * Real.pi * z.1 * c) : ℝ) : ℂ) * (1:ℂ)) := by
  fun_prop
lemma phase'_cont (k : ℝ) :
    Continuous (fun z : ℝ × ℝ =>
      Complex.exp (( (-(2 * Real.pi * z.1 * k) : ℝ) : ℂ) * Complex.I)) := by
  fun_prop
lemma phase'_norm (k x : ℝ) :
    ‖Complex.exp (( (-(2 * Real.pi * x * k) : ℝ) : ℂ) * Complex.I)‖ = (1:ℝ) :=
  phase_norm _

lemma sliceIntegrable (φ : SchwartzMap (ℝ × ℝ) ℂ) (θ k : ℝ) :
    Integrable
      (fun z : ℝ × ℝ =>
        Complex.exp (((-(2 * Real.pi * z.1 * k) : ℝ) : ℂ) * Complex.I) *
          (φ : ℝ × ℝ → ℂ) (rotLE θ z)) (volume : Measure (ℝ × ℝ)) := by
  have hrot : Integrable
      ((fun x : ℝ × ℝ => (φ : ℝ × ℝ → ℂ) x) ∘ (rotLE θ))
      (volume : Measure (ℝ × ℝ)) :=
    ((rotLE_measurePreserving θ).integrable_comp_emb (rotLE_measurableEmbedding θ)).2 φ.integrable
  have hrot' : Integrable
      (fun z : ℝ × ℝ => (φ : ℝ × ℝ → ℂ) (rotLE θ z))
      (volume : Measure (ℝ × ℝ)) := by simpa [Function.comp_def] using hrot
  exact hrot'.bdd_mul (phase'_cont k).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => by rw [phase'_norm]))


lemma slice_eq (φ : SchwartzMap (ℝ × ℝ) ℂ) (θ k : ℝ) :
        fourier1 (fun p => radon (φ : ℝ × ℝ → ℂ) (p, θ)) k =
          fourier2 (φ : ℝ × ℝ → ℂ) (k * Real.cos θ, k * Real.sin θ) := by
  let F : ℝ × ℝ → ℂ := fun z =>
        Complex.exp (((-(2 * Real.pi * z.1 * k) : ℝ) : ℂ) * Complex.I) *
          (φ : ℝ × ℝ → ℂ) (rotLE θ z)
  let H : ℝ × ℝ → ℂ := fun x =>
        Complex.exp (((-(2 * Real.pi *
             (x.1 * (k * Real.cos θ) + x.2 * (k * Real.sin θ))) : ℝ) : ℂ) * Complex.I) *
          (φ : ℝ × ℝ → ℂ) x
  have hFi : Integrable F (volume : Measure (ℝ × ℝ)) := sliceIntegrable φ θ k
  have hprod :
      (∫ z : ℝ × ℝ, F z) =
        ∫ p : ℝ, ∫ t : ℝ, F (p,t) := by
    simpa [MeasureTheory.Measure.volume_eq_prod] using
      (integral_prod F (by simpa [MeasureTheory.Measure.volume_eq_prod] using hFi))
  have hrotpoint : F = H ∘ (rotLE θ) := by
    funext z
    dsimp [F, H, Function.comp_def]
    rw [rotLE_apply]
    dsimp
    have htrig := Real.sin_sq_add_cos_sq θ
    have hdot :
       (z.1 * Real.cos θ - z.2 * Real.sin θ) * (k * Real.cos θ) +
              (z.1 * Real.sin θ + z.2 * Real.cos θ) * (k * Real.sin θ) = z.1 * k := by
       calc
        _ = (z.1 * k) * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
        _ = _ := by rw [htrig]; ring
    rw [hdot]
    ring_nf
  have hchange : (∫ z : ℝ × ℝ, F z) = ∫ x : ℝ × ℝ, H x := by
    rw [hrotpoint]
    exact (rotLE_measurePreserving θ).integral_comp (rotLE_measurableEmbedding θ) H
  rw [fourier1, fourier2]
  calc
    _ = ∫ p : ℝ, ∫ t : ℝ, F (p,t) := by
      apply integral_congr_ae
      filter_upwards [] with p
      dsimp [F, radon, rotLE]
      -- coerce the real scalar exponent together
      push_cast
      rw [integral_const_mul]
    _ = ∫ z : ℝ × ℝ, F z := hprod.symm
    _ = ∫ x : ℝ × ℝ, H x := hchange
    _ = _ := by
      dsimp [H]
      congr 1
      funext x
      push_cast
      rfl


noncomputable def eprod : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ×ℝ) :=
 (EuclideanSpace.equiv (Fin 2) ℝ).trans (LinearEquiv.finTwoArrow ℝ ℝ).toContinuousLinearEquiv
lemma inner_e (u v : EuclideanSpace ℝ (Fin 2)) :
 inner ℝ u v = (eprod u).1 * (eprod v).1 + (eprod u).2 * (eprod v).2 := by
  simp [eprod, EuclideanSpace.inner_eq_star_dotProduct]
  ring
lemma eprod_mp : MeasurePreserving (eprod : EuclideanSpace ℝ (Fin 2) → ℝ × ℝ) := by
  exact (MeasureTheory.volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
lemma eprod_emb : MeasurableEmbedding (eprod : EuclideanSpace ℝ (Fin 2) → ℝ × ℝ) :=
 eprod.toHomeomorph.measurableEmbedding

noncomputable def phiE (φ : SchwartzMap (ℝ × ℝ) ℂ) :
 SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
 SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eprod φ

lemma fourierE_eq (φ : SchwartzMap (ℝ × ℝ) ℂ)
 (w : EuclideanSpace ℝ (Fin 2)) :
 FourierTransform.fourier (phiE φ : EuclideanSpace ℝ (Fin 2) → ℂ) w =
   fourier2 (φ : ℝ × ℝ → ℂ) (eprod w) := by
  rw [Real.fourier_eq]
  rw [fourier2]
  -- rewrite the integral on Euclidean space as change of variables
  let G : (ℝ × ℝ) → ℂ := fun x =>
    Complex.exp (-(2 * Real.pi * (x.1 * (eprod w).1 + x.2 * (eprod w).2)) * Complex.I) * (φ : ℝ × ℝ → ℂ) x
  change (∫ v : EuclideanSpace ℝ (Fin 2),
     Real.fourierChar (-inner ℝ v w) • (phiE φ : EuclideanSpace ℝ (Fin 2) → ℂ) v) = _
  change _ = ∫ x : ℝ × ℝ,
    Complex.exp (-(2 * Real.pi * (x.1 * (eprod w).1 + x.2 * (eprod w).2)) * Complex.I) * (φ : ℝ × ℝ → ℂ) x
  rw [← (eprod_mp.integral_comp eprod_emb G)]
  congr 1
  funext v
  dsimp [G, phiE]
  rw [Circle.smul_def, Real.fourierChar_apply, inner_e]
  congr 2
  push_cast
  ring

lemma fourier2_inj {φ ψ : SchwartzMap (ℝ × ℝ) ℂ}
 (h : fourier2 (φ : ℝ × ℝ → ℂ) = fourier2 (ψ : ℝ × ℝ → ℂ)) : φ = ψ := by
  have hE : (phiE φ) = (phiE ψ) := by
    apply (show Function.Injective
      (FourierTransform.fourier : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ → _)
       from Function.LeftInverse.injective
        (fun q : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ =>
          FourierPair.fourierInv_fourier_eq q))
    ext w
    change FourierTransform.fourier (phiE φ : EuclideanSpace ℝ (Fin 2) → ℂ) w =
      FourierTransform.fourier (phiE ψ : EuclideanSpace ℝ (Fin 2) → ℂ) w
    rw [fourierE_eq, fourierE_eq]
    exact congrFun h (eprod w)
  -- evaluate equality after change of variables
  ext x
  let y : EuclideanSpace ℝ (Fin 2) := eprod.symm x
  have := congrFun (congrArg (fun q : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ =>
      (q : EuclideanSpace ℝ (Fin 2) → ℂ)) hE) y
  simpa [phiE, y] using this


lemma exists_polar (u v : ℝ) :
    ∃ θ k : ℝ, (k * Real.cos θ, k * Real.sin θ) = (u,v) := by
  let z : ℂ := ⟨u,v⟩
  refine ⟨Complex.arg z, ‖z‖, ?_⟩
  apply Prod.ext
  · change ‖z‖ * Real.cos (Complex.arg z) = u
    simpa [z] using Complex.norm_mul_cos_arg z
  · change ‖z‖ * Real.sin (Complex.arg z) = v
    simpa [z] using Complex.norm_mul_sin_arg z


lemma radon_schwartz_injective :
    Function.Injective
      (fun φ : SchwartzMap (ℝ × ℝ) ℂ =>
        radon (φ : ℝ × ℝ → ℂ)) := by
  intro φ ψ hrad
  apply fourier2_inj
  funext ξ
  rcases ξ with ⟨u,v⟩
  obtain ⟨θ,k,hpol⟩ := exists_polar u v
  -- the hypothesis gives equality of every one-dimensional projection
  have hp :
      (fun p : ℝ => radon (φ : ℝ × ℝ → ℂ) (p, θ)) =
      (fun p : ℝ => radon (ψ : ℝ × ℝ → ℂ) (p, θ)) := by
    funext p
    exact congrFun hrad (p,θ)
  rw [← hpol]
  calc
    fourier2 (φ : ℝ × ℝ → ℂ) (k * Real.cos θ, k * Real.sin θ) =
        fourier1 (fun p => radon (φ : ℝ × ℝ → ℂ) (p,θ)) k :=
          (slice_eq φ θ k).symm
    _ = fourier1 (fun p => radon (ψ : ℝ × ℝ → ℂ) (p,θ)) k := by
          rw [hp]
    _ = fourier2 (ψ : ℝ × ℝ → ℂ) (k * Real.cos θ, k * Real.sin θ) :=
          slice_eq ψ θ k

/-ResultBegin-/

theorem radon_can_be_diagonalized_and_pseudo_inverted :
    (∀ φ : SchwartzMap (ℝ × ℝ) ℂ, ∀ θ k : ℝ,
        fourier1 (fun p => radon (φ : ℝ × ℝ → ℂ) (p, θ)) k =
          fourier2 (φ : ℝ × ℝ → ℂ) (k * Real.cos θ, k * Real.sin θ)) ∧
    (∃ Rinv : (ℝ × ℝ → ℂ) → (ℝ × ℝ → ℂ),
        ∀ φ : SchwartzMap (ℝ × ℝ) ℂ,
          Rinv (radon (φ : ℝ × ℝ → ℂ)) = (φ : ℝ × ℝ → ℂ)) :=
/-ResultProofBegin-/ by
  classical
  refine ⟨?_, ?_⟩
  · intro φ θ k
    exact slice_eq φ θ k
  · -- make a purely set-theoretic left inverse to the (now injective) transform
    let f : SchwartzMap (ℝ × ℝ) ℂ → (ℝ × ℝ → ℂ) :=
      fun q => radon (q : ℝ × ℝ → ℂ)
    have hf : Function.Injective f := by
      intro a b hab
      apply radon_schwartz_injective
      exact hab
    let g : (ℝ × ℝ → ℂ) → SchwartzMap (ℝ × ℝ) ℂ :=
      Function.invFun f
    have hg : Function.LeftInverse g f := by
      dsimp [g]
      exact Function.leftInverse_invFun hf
    refine ⟨(fun h => ((g h : SchwartzMap (ℝ × ℝ) ℂ) : ℝ × ℝ → ℂ)), ?_⟩
    intro φ
    have hh : g (radon (φ : ℝ × ℝ → ℂ)) = φ := by
      change g (f φ) = φ
      exact hg φ
    exact congrArg
      (fun q : SchwartzMap (ℝ × ℝ) ℂ => (q : ℝ × ℝ → ℂ)) hh /-ResultProofEnd-/
/-ResultEnd-/

end Submission
