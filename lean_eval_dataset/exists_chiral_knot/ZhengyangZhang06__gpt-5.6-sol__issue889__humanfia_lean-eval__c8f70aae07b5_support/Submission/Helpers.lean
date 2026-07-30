import ChallengeDeps
import Submission.Linking
import Submission.Orientation
import Submission.Signature

open LeanEval.KnotTheory

namespace Submission.Helpers

noncomputable section

/-- Coordinates of the standard `(2, 3)` torus knot before applying the `L2` wrapper. -/
def torusTrefoilCoords (t : ℝ) : Fin 3 → ℝ :=
  ![
    (2 + Real.cos (3 * t)) * Real.cos (2 * t),
    (2 + Real.cos (3 * t)) * Real.sin (2 * t),
    Real.sin (3 * t)]

/-- The standard `(2, 3)` torus-knot parametrization on a torus of major radius `2`. -/
def torusTrefoilCurve (t : ℝ) : R3 :=
  WithLp.toLp 2 (torusTrefoilCoords t)

/-- Coordinate velocity of `torusTrefoilCurve`. -/
def torusTrefoilVelocityCoords (t : ℝ) : Fin 3 → ℝ :=
  ![
    -3 * Real.sin (3 * t) * Real.cos (2 * t) -
      2 * (2 + Real.cos (3 * t)) * Real.sin (2 * t),
    -3 * Real.sin (3 * t) * Real.sin (2 * t) +
      2 * (2 + Real.cos (3 * t)) * Real.cos (2 * t),
    3 * Real.cos (3 * t)]

def torusTrefoilVelocity (t : ℝ) : R3 :=
  WithLp.toLp 2 (torusTrefoilVelocityCoords t)

theorem torusTrefoilCurve_contDiff : ContDiff ℝ (⊤ : ℕ∞) torusTrefoilCurve := by
  apply (contDiff_piLp 2).2
  intro i
  fin_cases i <;> simp [torusTrefoilCurve, torusTrefoilCoords] <;> fun_prop

theorem torusTrefoilCurve_periodic (t : ℝ) :
    torusTrefoilCurve (t + 2 * Real.pi) = torusTrefoilCurve t := by
  have h2 :
      2 * (t + 2 * Real.pi) = 2 * t + ((2 : ℕ) : ℝ) * (2 * Real.pi) := by
    norm_num
    ring
  have h3 :
      3 * (t + 2 * Real.pi) = 3 * t + ((3 : ℕ) : ℝ) * (2 * Real.pi) := by
    norm_num
    ring
  have hcos2 := Real.cos_add_nat_mul_two_pi (2 * t) 2
  have hsin2 := Real.sin_add_nat_mul_two_pi (2 * t) 2
  have hcos3 := Real.cos_add_nat_mul_two_pi (3 * t) 3
  have hsin3 := Real.sin_add_nat_mul_two_pi (3 * t) 3
  norm_num at hcos2 hsin2 hcos3 hsin3
  ext i
  fin_cases i <;>
    simp [torusTrefoilCurve, torusTrefoilCoords, h2, h3, hcos2, hsin2, hcos3, hsin3]

theorem torusTrefoilCurve_injOn :
    Set.InjOn torusTrefoilCurve (Set.Ico 0 (2 * Real.pi)) := by
  intro t ht u hu htu
  have hx := congrArg (fun p : R3 => p.ofLp 0) htu
  have hy := congrArg (fun p : R3 => p.ofLp 1) htu
  have hz := congrArg (fun p : R3 => p.ofLp 2) htu
  simp [torusTrefoilCurve, torusTrefoilCoords] at hx hy hz
  have hrt : 0 < 2 + Real.cos (3 * t) := by
    nlinarith [Real.neg_one_le_cos (3 * t)]
  have hru : 0 < 2 + Real.cos (3 * u) := by
    nlinarith [Real.neg_one_le_cos (3 * u)]
  have hr_sq : (2 + Real.cos (3 * t)) ^ 2 = (2 + Real.cos (3 * u)) ^ 2 := by
    calc
      (2 + Real.cos (3 * t)) ^ 2 =
          (2 + Real.cos (3 * t)) ^ 2 *
            (Real.sin (2 * t) ^ 2 + Real.cos (2 * t) ^ 2) := by
              rw [Real.sin_sq_add_cos_sq]
              ring
      _ = ((2 + Real.cos (3 * t)) * Real.cos (2 * t)) ^ 2 +
          ((2 + Real.cos (3 * t)) * Real.sin (2 * t)) ^ 2 := by ring
      _ = ((2 + Real.cos (3 * u)) * Real.cos (2 * u)) ^ 2 +
          ((2 + Real.cos (3 * u)) * Real.sin (2 * u)) ^ 2 := by rw [hx, hy]
      _ = (2 + Real.cos (3 * u)) ^ 2 *
          (Real.sin (2 * u) ^ 2 + Real.cos (2 * u) ^ 2) := by ring
      _ = (2 + Real.cos (3 * u)) ^ 2 := by
        rw [Real.sin_sq_add_cos_sq]
        ring
  have hr : 2 + Real.cos (3 * t) = 2 + Real.cos (3 * u) := by
    nlinarith
  have hcos3 : Real.cos (3 * t) = Real.cos (3 * u) := by linarith
  have hcos2 : Real.cos (2 * t) = Real.cos (2 * u) := by
    apply mul_left_cancel₀ (ne_of_gt hrt)
    simpa [hr] using hx
  have hsin2 : Real.sin (2 * t) = Real.sin (2 * u) := by
    apply mul_left_cancel₀ (ne_of_gt hrt)
    simpa [hr] using hy
  have hangle2 : ((2 * t : ℝ) : Real.Angle) = (2 * u : ℝ) :=
    Real.Angle.cos_sin_inj hcos2 hsin2
  have hangle3 : ((3 * t : ℝ) : Real.Angle) = (3 * u : ℝ) :=
    Real.Angle.cos_sin_inj hcos3 hz
  obtain ⟨k2, hk2⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hangle2
  obtain ⟨k3, hk3⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hangle3
  let q : ℤ := k3 - k2
  have hd : t - u = 2 * Real.pi * (q : ℝ) := by
    dsimp [q]
    push_cast
    linarith
  have htwo_pi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hd_lower : -(2 * Real.pi) < t - u := by linarith [ht.1, hu.2]
  have hd_upper : t - u < 2 * Real.pi := by linarith [hu.1, ht.2]
  have hq_lower : (-1 : ℝ) < (q : ℝ) := by
    apply lt_of_mul_lt_mul_left _ htwo_pi.le
    rw [← hd]
    simpa using hd_lower
  have hq_upper : (q : ℝ) < 1 := by
    apply lt_of_mul_lt_mul_left _ htwo_pi.le
    rw [← hd]
    simpa using hd_upper
  have hq_lower_int : (-1 : ℤ) < q := by exact_mod_cast hq_lower
  have hq_upper_int : q < (1 : ℤ) := by exact_mod_cast hq_upper
  have hq : q = 0 := by omega
  rw [hq, Int.cast_zero, mul_zero] at hd
  linarith

theorem torusTrefoilCurve_deriv_apply (t : ℝ) (i : Fin 3) :
    (deriv torusTrefoilCurve t).ofLp i = torusTrefoilVelocityCoords t i := by
  have hcurve : HasDerivAt torusTrefoilCurve (deriv torusTrefoilCurve t) t :=
    (torusTrefoilCurve_contDiff.differentiable (by simp)).differentiableAt.hasDerivAt
  have hproj :=
    ((EuclideanSpace.proj i).hasFDerivAt.comp t hcurve.hasFDerivAt).hasDerivAt
  have hcos3 :
      HasDerivAt (fun s : ℝ => Real.cos (3 * s)) (-3 * Real.sin (3 * t)) t := by
    simpa [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_cos (3 * t)).comp t ((hasDerivAt_id t).const_mul 3)
  have hsin3 :
      HasDerivAt (fun s : ℝ => Real.sin (3 * s)) (3 * Real.cos (3 * t)) t := by
    simpa [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_sin (3 * t)).comp t ((hasDerivAt_id t).const_mul 3)
  have hcos2 :
      HasDerivAt (fun s : ℝ => Real.cos (2 * s)) (-2 * Real.sin (2 * t)) t := by
    simpa [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_cos (2 * t)).comp t ((hasDerivAt_id t).const_mul 2)
  have hsin2 :
      HasDerivAt (fun s : ℝ => Real.sin (2 * s)) (2 * Real.cos (2 * t)) t := by
    simpa [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_sin (2 * t)).comp t ((hasDerivAt_id t).const_mul 2)
  have hr := (hasDerivAt_const t 2).add hcos3
  have hscalar :
      HasDerivAt (fun s => (torusTrefoilCurve s).ofLp i)
        (torusTrefoilVelocityCoords t i) t := by
    fin_cases i
    · change HasDerivAt
        (fun s : ℝ => (2 + Real.cos (3 * s)) * Real.cos (2 * s))
        (-3 * Real.sin (3 * t) * Real.cos (2 * t) -
          2 * (2 + Real.cos (3 * t)) * Real.sin (2 * t)) t
      have hprod := hr.mul hcos2
      refine (hprod.congr_of_eventuallyEq ?_).congr_deriv ?_
      · exact Filter.Eventually.of_forall fun _ => by rfl
      · simp only [Pi.add_apply]
        ring
    · change HasDerivAt
        (fun s : ℝ => (2 + Real.cos (3 * s)) * Real.sin (2 * s))
        (-3 * Real.sin (3 * t) * Real.sin (2 * t) +
          2 * (2 + Real.cos (3 * t)) * Real.cos (2 * t)) t
      have hprod := hr.mul hsin2
      refine (hprod.congr_of_eventuallyEq ?_).congr_deriv ?_
      · exact Filter.Eventually.of_forall fun _ => by rfl
      · simp only [Pi.add_apply]
        ring
    · change HasDerivAt (fun s : ℝ => Real.sin (3 * s)) (3 * Real.cos (3 * t)) t
      exact hsin3
  simpa [Function.comp_def] using hproj.unique hscalar

theorem torusTrefoilVelocity_ne_zero (t : ℝ) : torusTrefoilVelocity t ≠ 0 := by
  intro hzero
  have hx := congrArg (fun p : R3 => p.ofLp 0) hzero
  have hy := congrArg (fun p : R3 => p.ofLp 1) hzero
  simp [torusTrefoilVelocity] at hx hy
  have hidentity :
      -(torusTrefoilVelocityCoords t 0) * Real.sin (2 * t) +
        torusTrefoilVelocityCoords t 1 * Real.cos (2 * t) =
        2 * (2 + Real.cos (3 * t)) := by
    change
      -(-3 * Real.sin (3 * t) * Real.cos (2 * t) -
          2 * (2 + Real.cos (3 * t)) * Real.sin (2 * t)) * Real.sin (2 * t) +
        (-3 * Real.sin (3 * t) * Real.sin (2 * t) +
          2 * (2 + Real.cos (3 * t)) * Real.cos (2 * t)) * Real.cos (2 * t) =
        2 * (2 + Real.cos (3 * t))
    calc
      _ = 2 * (2 + Real.cos (3 * t)) *
          (Real.sin (2 * t) ^ 2 + Real.cos (2 * t) ^ 2) := by ring
      _ = 2 * (2 + Real.cos (3 * t)) := by rw [Real.sin_sq_add_cos_sq, mul_one]
  rw [hx, hy] at hidentity
  nlinarith [Real.neg_one_le_cos (3 * t)]

theorem torusTrefoilCurve_immersion (t : ℝ) : deriv torusTrefoilCurve t ≠ 0 := by
  intro hzero
  have hx : torusTrefoilVelocityCoords t 0 = 0 := by
    simpa [hzero] using (torusTrefoilCurve_deriv_apply t 0).symm
  have hy : torusTrefoilVelocityCoords t 1 = 0 := by
    simpa [hzero] using (torusTrefoilCurve_deriv_apply t 1).symm
  have hz : torusTrefoilVelocityCoords t 2 = 0 := by
    simpa [hzero] using (torusTrefoilCurve_deriv_apply t 2).symm
  apply torusTrefoilVelocity_ne_zero t
  ext i
  fin_cases i
  · simpa [torusTrefoilVelocity, torusTrefoilVelocityCoords] using hx
  · simpa [torusTrefoilVelocity, torusTrefoilVelocityCoords] using hy
  · simpa [torusTrefoilVelocity, torusTrefoilVelocityCoords] using hz

/-- The right-handed `(2, 3)` torus knot as a value of the benchmark's `Knot` structure. -/
def torusTrefoil : Knot where
  curve := torusTrefoilCurve
  smooth := torusTrefoilCurve_contDiff
  periodic := torusTrefoilCurve_periodic
  injOn := torusTrefoilCurve_injOn
  immersion := torusTrefoilCurve_immersion

theorem reflectZ_involutive (p : R3) : reflectZ (reflectZ p) = p := by
  ext i
  simp [reflectZ]
  split_ifs <;> simp_all

/-- Reflection through the `xy`-plane as a linear equivalence. -/
def reflectZLinearEquiv : R3 ≃ₗ[ℝ] R3 where
  toFun := reflectZ
  invFun := reflectZ
  left_inv := reflectZ_involutive
  right_inv := reflectZ_involutive
  map_add' := by
    intro p q
    ext i
    simp [reflectZ]
    split_ifs <;> simp_all
    ring
  map_smul' := by
    intro c p
    ext i
    simp [reflectZ]

def reflectZContinuousLinearEquiv : R3 ≃L[ℝ] R3 :=
  reflectZLinearEquiv.toContinuousLinearEquiv

@[simp] theorem reflectZLinearEquiv_det :
    reflectZLinearEquiv.toLinearMap.det = -1 := by
  rw [← LinearMap.det_toMatrix
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  rw [Matrix.det_fin_three]
  simp [LinearMap.toMatrix_apply, reflectZLinearEquiv, reflectZ,
    EuclideanSpace.basisFun_apply]

theorem frameDet_reflectZ (u v w : R3) :
    Orientation.frameDet (reflectZ u) (reflectZ v) (reflectZ w) =
      -Orientation.frameDet u v w := by
  have h := Orientation.frameDet_map reflectZLinearEquiv.toLinearMap u v w
  rw [reflectZLinearEquiv_det] at h
  simpa [reflectZLinearEquiv] using h

/-- The reflected knot, with the original parametrization retained. -/
def mirrorKnot (K : Knot) : Knot where
  curve := fun t => reflectZ (K.curve t)
  smooth := by
    change ContDiff ℝ (⊤ : ℕ∞) (reflectZContinuousLinearEquiv ∘ K.curve)
    exact reflectZContinuousLinearEquiv.contDiff.comp K.smooth
  periodic := by
    intro t
    simp [K.periodic]
  injOn := by
    intro t ht u hu h
    apply K.injOn ht hu
    exact reflectZLinearEquiv.injective h
  immersion := by
    intro t hzero
    have hk : HasDerivAt K.curve (deriv K.curve t) t :=
      (K.smooth.differentiable (by simp)).differentiableAt.hasDerivAt
    have hc :=
      ((reflectZContinuousLinearEquiv.hasFDerivAt).comp t hk.hasFDerivAt).hasDerivAt
    change deriv (reflectZContinuousLinearEquiv ∘ K.curve) t = 0 at hzero
    rw [hc.deriv] at hzero
    apply K.immersion t
    apply reflectZContinuousLinearEquiv.injective
    simpa using hzero

theorem mirrorKnot_deriv (K : Knot) (t : ℝ) :
    deriv (mirrorKnot K).curve t = reflectZ (deriv K.curve t) := by
  have hK : HasDerivAt K.curve (deriv K.curve t) t :=
    (K.smooth.differentiable (by simp) t).hasDerivAt
  have hcomp := reflectZContinuousLinearEquiv.hasFDerivAt.comp_hasDerivAt t hK
  simpa [mirrorKnot, Function.comp_def, reflectZContinuousLinearEquiv,
    reflectZLinearEquiv] using hcomp.deriv

theorem mirror_endpoint_tangent
    (K : Knot) (Phi : AmbientIsotopy) (sigma : CircleReparam)
    (hendpoint : ∀ t, Phi.H 1 (K.curve t) = reflectZ (K.curve (sigma.f t)))
    (t : ℝ) :
    Orientation.spatialFDeriv Phi 1 (K.curve t) (deriv K.curve t) =
      deriv sigma.f t • reflectZ (deriv K.curve (sigma.f t)) := by
  have h := Orientation.endpoint_tangent (K1 := K) (K2 := mirrorKnot K)
    Phi sigma (by simpa [mirrorKnot] using hendpoint) t
  rw [mirrorKnot_deriv] at h
  exact h

theorem chiral_iff_not_isotopic_mirror (K : Knot) :
    K.Chiral ↔ ¬K.Isotopic (mirrorKnot K) := by
  rfl

/-- The two properties of an integer-valued knot invariant needed to detect chirality. -/
structure MirrorOddInvariant where
  value : Knot → ℤ
  isotopy_invariant : ∀ {K₁ K₂}, K₁.Isotopic K₂ → value K₁ = value K₂
  mirror_neg : ∀ K, value (mirrorKnot K) = -value K

theorem chiral_of_mirrorOddInvariant_ne_zero
    (I : MirrorOddInvariant) (K : Knot) (hK : I.value K ≠ 0) : K.Chiral := by
  rw [chiral_iff_not_isotopic_mirror]
  intro hIso
  have hValue := I.isotopy_invariant hIso
  rw [I.mirror_neg] at hValue
  apply hK
  omega

/-- A real-valued variant, useful for integral invariants before integer normalization. -/
structure MirrorOddRealInvariant where
  value : Knot → ℝ
  isotopy_invariant : ∀ {K₁ K₂}, K₁.Isotopic K₂ → value K₁ = value K₂
  mirror_neg : ∀ K, value (mirrorKnot K) = -value K

theorem chiral_of_mirrorOddRealInvariant_ne_zero
    (I : MirrorOddRealInvariant) (K : Knot) (hK : I.value K ≠ 0) : K.Chiral := by
  rw [chiral_iff_not_isotopic_mirror]
  intro hIso
  have hValue := I.isotopy_invariant hIso
  rw [I.mirror_neg] at hValue
  apply hK
  linarith

end

end Submission.Helpers
