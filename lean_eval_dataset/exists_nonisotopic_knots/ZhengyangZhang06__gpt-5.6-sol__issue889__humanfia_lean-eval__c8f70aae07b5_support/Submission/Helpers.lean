import ChallengeDeps

open LeanEval.KnotTheory

namespace Submission.Helpers

noncomputable section

private def rawRoundCircle (t : ℝ) : Fin 3 → ℝ := fun i =>
  if i = 0 then Real.cos t else if i = 1 then Real.sin t else 0

private def rawRoundCircleVelocity (t : ℝ) : Fin 3 → ℝ := fun i =>
  if i = 0 then -Real.sin t else if i = 1 then Real.cos t else 0

/-- The standard unit circle in the `xy`-plane. -/
def roundCircleCurve (t : ℝ) : R3 :=
  WithLp.toLp 2 (rawRoundCircle t)

@[simp] theorem roundCircleCurve_apply_zero (t : ℝ) : roundCircleCurve t 0 = Real.cos t := by
  simp [roundCircleCurve, rawRoundCircle]

@[simp] theorem roundCircleCurve_apply_one (t : ℝ) : roundCircleCurve t 1 = Real.sin t := by
  simp [roundCircleCurve, rawRoundCircle]

@[simp] theorem roundCircleCurve_apply_two (t : ℝ) : roundCircleCurve t 2 = 0 := by
  simp [roundCircleCurve, rawRoundCircle]

private theorem roundCircleCurve_smooth : ContDiff ℝ (⊤ : ℕ∞) roundCircleCurve := by
  rw [contDiff_piLp 2]
  intro i
  fin_cases i
  · simpa [roundCircleCurve, rawRoundCircle] using
      (Real.contDiff_cos : ContDiff ℝ (⊤ : ℕ∞) Real.cos)
  · simpa [roundCircleCurve, rawRoundCircle] using
      (Real.contDiff_sin : ContDiff ℝ (⊤ : ℕ∞) Real.sin)
  · simpa [roundCircleCurve, rawRoundCircle] using
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) fun _ : ℝ => (0 : ℝ))

private theorem roundCircleCurve_periodic (t : ℝ) :
    roundCircleCurve (t + 2 * Real.pi) = roundCircleCurve t := by
  ext i
  fin_cases i <;> simp [roundCircleCurve, rawRoundCircle, Real.cos_add_two_pi,
    Real.sin_add_two_pi]

private theorem roundCircleCurve_injOn :
    Set.InjOn roundCircleCurve (Set.Ico 0 (2 * Real.pi)) := by
  intro s hs t ht hst
  have hcos : Real.cos s = Real.cos t := by
    simpa [roundCircleCurve, rawRoundCircle] using
      congrArg (fun p : R3 => p 0) hst
  have hsin : Real.sin s = Real.sin t := by
    simpa [roundCircleCurve, rawRoundCircle] using
      congrArg (fun p : R3 => p 1) hst
  have hexp : Circle.exp s = Circle.exp t := by
    apply Subtype.ext
    apply Complex.ext
    · simpa [Circle.coe_exp, Complex.exp_ofReal_mul_I_re] using hcos
    · simpa [Circle.coe_exp, Complex.exp_ofReal_mul_I_im] using hsin
  exact Circle.exp_injOn_Ico (by simp) hs ht hexp

private theorem roundCircleCurve_hasDerivAt (t : ℝ) :
    HasDerivAt roundCircleCurve (WithLp.toLp 2 (rawRoundCircleVelocity t)) t := by
  have hraw : HasDerivAt rawRoundCircle (rawRoundCircleVelocity t) t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa [rawRoundCircle, rawRoundCircleVelocity] using Real.hasDerivAt_cos t
    · simpa [rawRoundCircle, rawRoundCircleVelocity] using Real.hasDerivAt_sin t
    · simpa [rawRoundCircle, rawRoundCircleVelocity] using
        (hasDerivAt_const (x := t) (c := (0 : ℝ)))
  exact (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 (rawRoundCircle t)).comp_hasDerivAt t hraw

private theorem roundCircleCurve_immersion (t : ℝ) : deriv roundCircleCurve t ≠ 0 := by
  rw [(roundCircleCurve_hasDerivAt t).deriv]
  intro hzero
  have hsin : Real.sin t = 0 := by
    have h := congrArg (fun p : R3 => p 0) hzero
    simpa [rawRoundCircleVelocity] using h
  have hcos : Real.cos t = 0 := by
    have h := congrArg (fun p : R3 => p 1) hzero
    simpa [rawRoundCircleVelocity] using h
  nlinarith [Real.sin_sq_add_cos_sq t]

/-- A checked `Knot` witness for the round unknot. -/
def roundCircle : Knot where
  curve := roundCircleCurve
  smooth := roundCircleCurve_smooth
  periodic := roundCircleCurve_periodic
  injOn := roundCircleCurve_injOn
  immersion := roundCircleCurve_immersion

private def torusRadius (t : ℝ) : ℝ :=
  2 + Real.cos (3 * t)

private theorem torusRadius_pos (t : ℝ) : 0 < torusRadius t := by
  unfold torusRadius
  nlinarith [Real.neg_one_le_cos (3 * t)]

private def rawTorusKnot (t : ℝ) : Fin 3 → ℝ := fun i =>
  if i = 0 then torusRadius t * Real.cos (2 * t)
  else if i = 1 then torusRadius t * Real.sin (2 * t)
  else Real.sin (3 * t)

private def rawTorusKnotVelocity (t : ℝ) : Fin 3 → ℝ := fun i =>
  if i = 0 then
    (-3 * Real.sin (3 * t)) * Real.cos (2 * t) -
      2 * torusRadius t * Real.sin (2 * t)
  else if i = 1 then
    (-3 * Real.sin (3 * t)) * Real.sin (2 * t) +
      2 * torusRadius t * Real.cos (2 * t)
  else 3 * Real.cos (3 * t)

/-- A standard parametrization of the `(2,3)` torus knot. -/
def torusKnotCurve (t : ℝ) : R3 :=
  WithLp.toLp 2 (rawTorusKnot t)

private theorem torusKnotCurve_smooth : ContDiff ℝ (⊤ : ℕ∞) torusKnotCurve := by
  rw [contDiff_piLp 2]
  intro i
  fin_cases i <;> simp [torusKnotCurve, rawTorusKnot, torusRadius] <;> fun_prop

private theorem torusKnotCurve_periodic (t : ℝ) :
    torusKnotCurve (t + 2 * Real.pi) = torusKnotCurve t := by
  have htwo : 2 * (t + 2 * Real.pi) = 2 * t + (2 : ℕ) * (2 * Real.pi) := by ring
  have hthree : 3 * (t + 2 * Real.pi) = 3 * t + (3 : ℕ) * (2 * Real.pi) := by ring
  have hcos_two : Real.cos (2 * t + (2 : ℕ) * (2 * Real.pi)) = Real.cos (2 * t) :=
    Real.cos_add_nat_mul_two_pi _ _
  have hsin_two : Real.sin (2 * t + (2 : ℕ) * (2 * Real.pi)) = Real.sin (2 * t) :=
    Real.sin_add_nat_mul_two_pi _ _
  have hcos_three : Real.cos (3 * t + (3 : ℕ) * (2 * Real.pi)) = Real.cos (3 * t) :=
    Real.cos_add_nat_mul_two_pi _ _
  have hsin_three : Real.sin (3 * t + (3 : ℕ) * (2 * Real.pi)) = Real.sin (3 * t) :=
    Real.sin_add_nat_mul_two_pi _ _
  ext i
  fin_cases i
  · change (2 + Real.cos (3 * (t + 2 * Real.pi))) *
      Real.cos (2 * (t + 2 * Real.pi)) =
      (2 + Real.cos (3 * t)) * Real.cos (2 * t)
    rw [htwo, hthree, hcos_two, hcos_three]
  · change (2 + Real.cos (3 * (t + 2 * Real.pi))) *
      Real.sin (2 * (t + 2 * Real.pi)) =
      (2 + Real.cos (3 * t)) * Real.sin (2 * t)
    rw [htwo, hthree, hsin_two, hcos_three]
  · change Real.sin (3 * (t + 2 * Real.pi)) = Real.sin (3 * t)
    rw [hthree, hsin_three]

private theorem torusKnot_radial_sq (t : ℝ) :
    (rawTorusKnot t 0) ^ 2 + (rawTorusKnot t 1) ^ 2 = torusRadius t ^ 2 := by
  change (torusRadius t * Real.cos (2 * t)) ^ 2 +
      (torusRadius t * Real.sin (2 * t)) ^ 2 = torusRadius t ^ 2
  nlinarith [Real.sin_sq_add_cos_sq (2 * t)]

private theorem circleExp_eq_of_cos_sin_eq {s t : ℝ}
    (hcos : Real.cos s = Real.cos t) (hsin : Real.sin s = Real.sin t) :
    Circle.exp s = Circle.exp t := by
  apply Subtype.ext
  apply Complex.ext
  · simpa [Circle.coe_exp, Complex.exp_ofReal_mul_I_re] using hcos
  · simpa [Circle.coe_exp, Complex.exp_ofReal_mul_I_im] using hsin

private theorem torusKnotCurve_injOn :
    Set.InjOn torusKnotCurve (Set.Ico 0 (2 * Real.pi)) := by
  intro s hs t ht hst
  have hx : rawTorusKnot s 0 = rawTorusKnot t 0 := by
    simpa [torusKnotCurve] using congrArg (fun p : R3 => p 0) hst
  have hy : rawTorusKnot s 1 = rawTorusKnot t 1 := by
    simpa [torusKnotCurve] using congrArg (fun p : R3 => p 1) hst
  have hz : Real.sin (3 * s) = Real.sin (3 * t) := by
    simpa [torusKnotCurve, rawTorusKnot] using congrArg (fun p : R3 => p 2) hst
  have hx2 := congrArg (fun x : ℝ => x ^ 2) hx
  have hy2 := congrArg (fun x : ℝ => x ^ 2) hy
  have hradius_sq : torusRadius s ^ 2 = torusRadius t ^ 2 := by
    calc
      torusRadius s ^ 2 = (rawTorusKnot s 0) ^ 2 + (rawTorusKnot s 1) ^ 2 :=
        (torusKnot_radial_sq s).symm
      _ = (rawTorusKnot t 0) ^ 2 + (rawTorusKnot t 1) ^ 2 := by rw [hx2, hy2]
      _ = torusRadius t ^ 2 := torusKnot_radial_sq t
  have hradius : torusRadius s = torusRadius t := by
    nlinarith [torusRadius_pos s, torusRadius_pos t]
  have hcos_three : Real.cos (3 * s) = Real.cos (3 * t) := by
    unfold torusRadius at hradius
    linarith
  have hthree : Circle.exp (3 * s) = Circle.exp (3 * t) :=
    circleExp_eq_of_cos_sin_eq hcos_three hz
  have hcos_two : Real.cos (2 * s) = Real.cos (2 * t) := by
    have hx' : torusRadius t * Real.cos (2 * s) =
        torusRadius t * Real.cos (2 * t) := by
      simpa [rawTorusKnot, hradius] using hx
    exact mul_left_cancel₀ (torusRadius_pos t).ne' hx'
  have hsin_two : Real.sin (2 * s) = Real.sin (2 * t) := by
    have hy' : torusRadius t * Real.sin (2 * s) =
        torusRadius t * Real.sin (2 * t) := by
      simpa [rawTorusKnot, hradius] using hy
    exact mul_left_cancel₀ (torusRadius_pos t).ne' hy'
  have htwo : Circle.exp (2 * s) = Circle.exp (2 * t) :=
    circleExp_eq_of_cos_sin_eq hcos_two hsin_two
  have hbase : Circle.exp s = Circle.exp t := by
    calc
      Circle.exp s = Circle.exp (3 * s - 2 * s) := by
        congr 1
        ring
      _ = Circle.exp (3 * s) / Circle.exp (2 * s) := Circle.exp_sub _ _
      _ = Circle.exp (3 * t) / Circle.exp (2 * t) := by rw [hthree, htwo]
      _ = Circle.exp (3 * t - 2 * t) := (Circle.exp_sub _ _).symm
      _ = Circle.exp t := by
        congr 1
        ring
  exact Circle.exp_injOn_Ico (by simp) hs ht hbase

private theorem torusKnotCurve_hasDerivAt (t : ℝ) :
    HasDerivAt torusKnotCurve (WithLp.toLp 2 (rawTorusKnotVelocity t)) t := by
  have htwo : HasDerivAt (fun x : ℝ => 2 * x) 2 t := hasDerivAt_const_mul 2
  have hthree : HasDerivAt (fun x : ℝ => 3 * x) 3 t := hasDerivAt_const_mul 3
  have hcos_two : HasDerivAt (fun x : ℝ => Real.cos (2 * x))
      (-2 * Real.sin (2 * t)) t := by
    simpa only [Function.comp_def, mul_comm, mul_neg, neg_mul] using
      (Real.hasDerivAt_cos (2 * t)).comp t htwo
  have hsin_two : HasDerivAt (fun x : ℝ => Real.sin (2 * x))
      (2 * Real.cos (2 * t)) t := by
    simpa only [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_sin (2 * t)).comp t htwo
  have hcos_three : HasDerivAt (fun x : ℝ => Real.cos (3 * x))
      (-3 * Real.sin (3 * t)) t := by
    simpa only [Function.comp_def, mul_comm, mul_neg, neg_mul] using
      (Real.hasDerivAt_cos (3 * t)).comp t hthree
  have hsin_three : HasDerivAt (fun x : ℝ => Real.sin (3 * x))
      (3 * Real.cos (3 * t)) t := by
    simpa only [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_sin (3 * t)).comp t hthree
  have hradius : HasDerivAt torusRadius (-3 * Real.sin (3 * t)) t := by
    unfold torusRadius
    exact hcos_three.const_add 2
  have hraw : HasDerivAt rawTorusKnot (rawTorusKnotVelocity t) t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · have hprod := (hradius.mul hcos_two).congr_deriv (show
          (-3 * Real.sin (3 * t)) * Real.cos (2 * t) +
              torusRadius t * (-2 * Real.sin (2 * t)) =
            rawTorusKnotVelocity t 0 by
          simp [rawTorusKnotVelocity]
          ring)
      exact hprod
    · have hprod := (hradius.mul hsin_two).congr_deriv (show
          (-3 * Real.sin (3 * t)) * Real.sin (2 * t) +
              torusRadius t * (2 * Real.cos (2 * t)) =
            rawTorusKnotVelocity t 1 by
          simp [rawTorusKnotVelocity]
          ring)
      exact hprod
    · simpa [rawTorusKnot, rawTorusKnotVelocity] using hsin_three
  exact (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 (rawTorusKnot t)).comp_hasDerivAt t hraw

private theorem torusKnot_velocity_sq (t : ℝ) :
    (rawTorusKnotVelocity t 0) ^ 2 + (rawTorusKnotVelocity t 1) ^ 2 =
      (-3 * Real.sin (3 * t)) ^ 2 + (2 * torusRadius t) ^ 2 := by
  change ((-3 * Real.sin (3 * t)) * Real.cos (2 * t) -
      2 * torusRadius t * Real.sin (2 * t)) ^ 2 +
      ((-3 * Real.sin (3 * t)) * Real.sin (2 * t) +
        2 * torusRadius t * Real.cos (2 * t)) ^ 2 =
      (-3 * Real.sin (3 * t)) ^ 2 + (2 * torusRadius t) ^ 2
  nlinarith [Real.sin_sq_add_cos_sq (2 * t)]

private theorem torusKnotCurve_immersion (t : ℝ) : deriv torusKnotCurve t ≠ 0 := by
  rw [(torusKnotCurve_hasDerivAt t).deriv]
  intro hzero
  have hx : rawTorusKnotVelocity t 0 = 0 := by
    simpa using congrArg (fun p : R3 => p 0) hzero
  have hy : rawTorusKnotVelocity t 1 = 0 := by
    simpa using congrArg (fun p : R3 => p 1) hzero
  have hsq := torusKnot_velocity_sq t
  rw [hx, hy] at hsq
  have hpositive : 0 < (2 * torusRadius t) ^ 2 := by
    exact sq_pos_of_pos (mul_pos (by norm_num) (torusRadius_pos t))
  nlinarith

/-- A checked `Knot` witness for the right-handed trefoil type. -/
def torusKnot : Knot where
  curve := torusKnotCurve
  smooth := torusKnotCurve_smooth
  periodic := torusKnotCurve_periodic
  injOn := torusKnotCurve_injOn
  immersion := torusKnotCurve_immersion

open CategoryTheory
open scoped FundamentalGroupoid

/-- A homeomorphism induces an isomorphism of fundamental groups. -/
noncomputable def fundamentalGroupMulEquivOfHomeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (h x) := by
  let e := FundamentalGroupoidFunctor.equivOfHomotopyEquiv h.toHomotopyEquiv
  exact MulEquiv.ofBijective (e.functor.mapEnd (FundamentalGroupoid.mk x))
    (e.fullyFaithfulFunctor.map_bijective _ _)

/-- The endpoint at any time of an ambient isotopy is a homeomorphism. -/
noncomputable def ambientHomeomorph (Phi : AmbientIsotopy) (s : ℝ) : R3 ≃ₜ R3 where
  toFun := Phi.H s
  invFun := Phi.Hinv s
  left_inv := Phi.inv_left s
  right_inv := Phi.inv_right s
  continuous_toFun :=
    Phi.smooth.continuous.comp (continuous_const.prodMk continuous_id)
  continuous_invFun :=
    Phi.smooth_inv.continuous.comp (continuous_const.prodMk continuous_id)

private theorem isotopyData_range_eq {K1 K2 : Knot} (Phi : AmbientIsotopy)
    (sigma : CircleReparam)
    (hcurve : ∀ t, Phi.H 1 (K1.curve t) = K2.curve (sigma.f t)) :
    Phi.H 1 '' Set.range K1.curve = Set.range K2.curve := by
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨sigma.f t, (hcurve t).symm⟩
  · rintro _ ⟨u, rfl⟩
    refine ⟨K1.curve (sigma.finv u), ⟨sigma.finv u, rfl⟩, ?_⟩
    simpa [sigma.right_inv u] using hcurve (sigma.finv u)

/-- The topological complement of a knot image. -/
abbrev KnotComplement (K : Knot) := {x : R3 // x ∉ Set.range K.curve}

/-- Ambient-isotopic knots have homeomorphic complements. -/
noncomputable def isotopicComplementHomeomorph {K1 K2 : Knot}
    (h : K1.Isotopic K2) : KnotComplement K1 ≃ₜ KnotComplement K2 := by
  let Phi := Classical.choose h
  let sigma := Classical.choose (Classical.choose_spec h)
  have hcurve := Classical.choose_spec (Classical.choose_spec h)
  let e := ambientHomeomorph Phi 1
  apply e.subtype
  intro x
  have hrange := isotopyData_range_eq Phi sigma hcurve
  constructor
  · intro hx hmem
    rw [← hrange] at hmem
    rcases hmem with ⟨y, hy, hey⟩
    exact hx (e.injective hey ▸ hy)
  · intro hx hmem
    apply hx
    rw [← hrange]
    exact ⟨x, hmem, rfl⟩

/-- Every based fundamental group of a space is abelian. -/
def HasAbelianFundamentalGroups (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ x : X, ∀ a b : FundamentalGroup X x, a * b = b * a

private theorem hasAbelianFundamentalGroups_homeomorph_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    HasAbelianFundamentalGroups X ↔ HasAbelianFundamentalGroups Y := by
  constructor
  · intro h y a b
    let g := fundamentalGroupMulEquivOfHomeomorph e.symm y
    apply g.injective
    simpa only [map_mul] using h (e.symm y) (g a) (g b)
  · intro h x a b
    let g := fundamentalGroupMulEquivOfHomeomorph e x
    apply g.injective
    simpa only [map_mul] using h (e x) (g a) (g b)

/-- Abelianity of complement fundamental groups is an ambient-isotopy invariant. -/
theorem isotopic_hasAbelianFundamentalGroups_iff {K1 K2 : Knot}
    (h : K1.Isotopic K2) :
    HasAbelianFundamentalGroups (KnotComplement K1) ↔
      HasAbelianFundamentalGroups (KnotComplement K2) :=
  hasAbelianFundamentalGroups_homeomorph_iff (isotopicComplementHomeomorph h)

private def trefoilRelation : FreeGroup (Fin 2) :=
  FreeGroup.of 0 ^ 2 * (FreeGroup.of 1 ^ 3)⁻¹

/-- The standard two-generator, one-relation presentation of the trefoil group. -/
abbrev TrefoilGroup :=
  PresentedGroup ({trefoilRelation} : Set (FreeGroup (Fin 2)))

private def trefoilPermA : Equiv.Perm (Fin 3) :=
  Equiv.swap 0 1

private def trefoilPermB : Equiv.Perm (Fin 3) :=
  Equiv.swap 0 1 * Equiv.swap 1 2

private def trefoilPermOnGenerator : Fin 2 → Equiv.Perm (Fin 3) := fun i =>
  if i = 0 then trefoilPermA else trefoilPermB

private theorem trefoilPermA_sq : trefoilPermA ^ 2 = 1 := by
  decide

private theorem trefoilPermB_cube : trefoilPermB ^ 3 = 1 := by
  decide

private theorem trefoilRelation_maps_to_one :
    ∀ r ∈ ({trefoilRelation} : Set (FreeGroup (Fin 2))),
      FreeGroup.lift trefoilPermOnGenerator r = 1 := by
  intro r hr
  rw [Set.mem_singleton_iff] at hr
  subst r
  simp [trefoilRelation, trefoilPermOnGenerator, trefoilPermA_sq, trefoilPermB_cube]

private noncomputable def trefoilPermutationRepresentation :
    TrefoilGroup →* Equiv.Perm (Fin 3) :=
  PresentedGroup.toGroup trefoilRelation_maps_to_one

private theorem trefoilPermutationRepresentation_of_zero :
    trefoilPermutationRepresentation (PresentedGroup.of 0 : TrefoilGroup) = trefoilPermA := by
  simp [trefoilPermutationRepresentation, trefoilPermOnGenerator]

private theorem trefoilPermutationRepresentation_of_one :
    trefoilPermutationRepresentation (PresentedGroup.of 1 : TrefoilGroup) = trefoilPermB := by
  simp [trefoilPermutationRepresentation, trefoilPermOnGenerator]

/-- The two standard generators of the trefoil presentation do not commute. -/
theorem trefoilGroup_noncommuting_generators :
    (PresentedGroup.of 0 : TrefoilGroup) * PresentedGroup.of 1 ≠
      PresentedGroup.of 1 * PresentedGroup.of 0 := by
  intro h
  have himage := congrArg trefoilPermutationRepresentation h
  simp only [map_mul, trefoilPermutationRepresentation_of_zero,
    trefoilPermutationRepresentation_of_one] at himage
  exact (by decide : trefoilPermA * trefoilPermB ≠ trefoilPermB * trefoilPermA) himage

/-- The trefoil presentation is noncommutative. -/
theorem trefoilGroup_not_commutative :
    ¬ ∀ a b : TrefoilGroup, a * b = b * a := by
  intro h
  exact trefoilGroup_noncommuting_generators
    (h (PresentedGroup.of 0) (PresentedGroup.of 1))

/-- A space with a trefoil fundamental group at one basepoint cannot have all
fundamental groups abelian. -/
theorem not_hasAbelianFundamentalGroups_of_trefoilGroup
    {X : Type*} [TopologicalSpace X] (x : X)
    (e : FundamentalGroup X x ≃* TrefoilGroup) :
    ¬ HasAbelianFundamentalGroups X := by
  intro h
  apply trefoilGroup_not_commutative
  intro a b
  apply e.symm.injective
  simpa only [map_mul] using h x (e.symm a) (e.symm b)

/-- The two checked knot witnesses are non-isotopic once their complement
fundamental groups are identified with the standard algebraic models. -/
theorem roundCircle_not_isotopic_torusKnot_of_complement_groups
    (hround : HasAbelianFundamentalGroups (KnotComplement roundCircle))
    (x : KnotComplement torusKnot)
    (htrefoil : FundamentalGroup (KnotComplement torusKnot) x ≃* TrefoilGroup) :
    ¬ roundCircle.Isotopic torusKnot := by
  intro hisotopic
  have htorus := (isotopic_hasAbelianFundamentalGroups_iff hisotopic).mp hround
  exact not_hasAbelianFundamentalGroups_of_trefoilGroup x htrefoil htorus

/-- The benchmark conclusion reduced to the two complement computations. -/
theorem exists_nonisotopic_knots_of_complement_groups
    (hround : HasAbelianFundamentalGroups (KnotComplement roundCircle))
    (x : KnotComplement torusKnot)
    (htrefoil : FundamentalGroup (KnotComplement torusKnot) x ≃* TrefoilGroup) :
    ∃ K1 K2 : Knot, ¬ K1.Isotopic K2 :=
  ⟨roundCircle, torusKnot,
    roundCircle_not_isotopic_torusKnot_of_complement_groups hround x htrefoil⟩

end

end Submission.Helpers
