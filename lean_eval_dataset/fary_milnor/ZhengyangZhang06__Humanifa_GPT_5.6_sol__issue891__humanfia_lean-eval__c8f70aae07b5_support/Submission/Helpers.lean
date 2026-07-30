import ChallengeDeps

open LeanEval.Geometry.FaryMilnorProblem
open Set
open Filter
open scoped Real
open scoped Topology
open scoped RealInnerProductSpace
open WithLp

namespace Submission.Helpers

noncomputable def unitTangent (r : ℝ → Space) (t : ℝ) : Space :=
  ‖velocity r t‖⁻¹ • velocity r t

noncomputable def normalAcceleration (r : ℝ → Space) (t : ℝ) : Space :=
  acceleration r t -
    (inner ℝ (velocity r t) (acceleration r t) / ‖velocity r t‖ ^ 2) • velocity r t

noncomputable def height (r : ℝ → Space) (u : Space) (t : ℝ) : ℝ :=
  inner ℝ u (r t)

theorem curvature_nonneg (r : ℝ → Space) (t : ℝ) : 0 ≤ curvature r t := by
  exact div_nonneg (norm_nonneg _) (by positivity)

theorem totalCurvature_nonneg (r : ℝ → Space) : 0 ≤ totalCurvature r := by
  rw [totalCurvature]
  apply intervalIntegral.integral_nonneg_of_forall
  · simp [period, Real.pi_pos.le]
  · intro t
    exact mul_nonneg (curvature_nonneg r t) (norm_nonneg _)

theorem contDiff_velocity {r : ℝ → Space} (hknot : IsSmoothKnot r) :
    ContDiff ℝ ⊤ (velocity r) := by
  convert ContDiff.deriv' (n := ⊤) hknot.smooth using 1 <;> rfl

theorem contDiff_acceleration {r : ℝ → Space} (hknot : IsSmoothKnot r) :
    ContDiff ℝ ⊤ (acceleration r) := by
  convert ContDiff.deriv' (n := ⊤) (contDiff_velocity hknot) using 1 <;> rfl

theorem contDiff_unitTangent {r : ℝ → Space} (hknot : IsSmoothKnot r) :
    ContDiff ℝ ⊤ (unitTangent r) := by
  have hvelocity := contDiff_velocity hknot
  have hspeed : ContDiff ℝ ⊤ (fun t => ‖velocity r t‖) :=
    hvelocity.norm ℝ hknot.regular
  exact (hspeed.inv fun t => norm_ne_zero_iff.mpr (hknot.regular t)).smul hvelocity

theorem periodic_deriv {f : ℝ → Space} {p : ℝ} (hperiodic : Function.Periodic f p) :
    Function.Periodic (deriv f) p := by
  intro t
  have hfun : (fun x : ℝ => f (x + p)) = f := funext hperiodic
  have hderiv := congrArg (fun g : ℝ → Space => deriv g t) hfun
  rw [deriv_comp_add_const] at hderiv
  exact hderiv

theorem periodic_deriv_real {f : ℝ → ℝ} {p : ℝ}
    (hperiodic : Function.Periodic f p) :
    Function.Periodic (deriv f) p := by
  intro t
  have hfun : (fun x : ℝ => f (x + p)) = f := funext hperiodic
  have hderiv := congrArg (fun g : ℝ → ℝ => deriv g t) hfun
  rw [deriv_comp_add_const] at hderiv
  exact hderiv

theorem periodic_velocity {r : ℝ → Space} (hknot : IsSmoothKnot r) :
    Function.Periodic (velocity r) period := by
  simpa [velocity] using periodic_deriv hknot.periodic

theorem periodic_acceleration {r : ℝ → Space} (hknot : IsSmoothKnot r) :
    Function.Periodic (acceleration r) period := by
  simpa [acceleration] using periodic_deriv (periodic_velocity hknot)

theorem periodic_unitTangent {r : ℝ → Space} (hknot : IsSmoothKnot r) :
    Function.Periodic (unitTangent r) period := by
  intro t
  rw [unitTangent, unitTangent, periodic_velocity hknot t]

theorem continuous_deriv_unitTangent {r : ℝ → Space} (hknot : IsSmoothKnot r) :
    Continuous (deriv (unitTangent r)) := by
  exact (contDiff_unitTangent hknot).continuous_deriv (by simp)

theorem continuous_norm_deriv_unitTangent {r : ℝ → Space} (hknot : IsSmoothKnot r) :
    Continuous (fun t => ‖deriv (unitTangent r) t‖) :=
  (continuous_deriv_unitTangent hknot).norm

theorem hasDerivAt_curve {r : ℝ → Space} (hknot : IsSmoothKnot r) (t : ℝ) :
    HasDerivAt r (velocity r t) t := by
  have hdiff : DifferentiableAt ℝ r t :=
    (hknot.smooth.differentiable (by simp)).differentiableAt
  simpa [velocity] using hdiff.hasDerivAt

theorem hasDerivAt_height {r : ℝ → Space} (hknot : IsSmoothKnot r)
    (u : Space) (t : ℝ) :
    HasDerivAt (height r u) (inner ℝ u (velocity r t)) t := by
  convert (innerSL ℝ u).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_curve hknot t) using 1 <;> rfl

theorem periodic_height {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space) :
    Function.Periodic (height r u) period := by
  intro t
  simp [height, hknot.periodic t]

theorem continuous_height {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space) :
    Continuous (height r u) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_height hknot u t).continuousAt

theorem exists_isLocalMax_of_periodic {f : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hperiodic : Function.Periodic f p) (hcontinuous : Continuous f) :
    ∃ t, IsLocalMax f t := by
  obtain ⟨t, _ht, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr hp.le) hcontinuous.continuousOn
  refine ⟨t, ?_⟩
  have hglobal : IsMaxOn f univ t := by
    intro x _hx
    obtain ⟨y, hy, hxy⟩ := hperiodic.exists_mem_Ico₀ hp x
    change f x ≤ f t
    rw [hxy]
    exact hmax ⟨hy.1, hy.2.le⟩
  exact hglobal.isLocalMax (by simp)

theorem exists_isLocalMin_of_periodic {f : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hperiodic : Function.Periodic f p) (hcontinuous : Continuous f) :
    ∃ t, IsLocalMin f t := by
  obtain ⟨t, _ht, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr hp.le) hcontinuous.continuousOn
  refine ⟨t, ?_⟩
  have hglobal : IsMinOn f univ t := by
    intro x _hx
    obtain ⟨y, hy, hxy⟩ := hperiodic.exists_mem_Ico₀ hp x
    change f t ≤ f x
    rw [hxy]
    exact hmin ⟨hy.1, hy.2.le⟩
  exact hglobal.isLocalMin (by simp)

theorem exists_isLocalMax_height {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space) :
    ∃ t, IsLocalMax (height r u) t := by
  exact exists_isLocalMax_of_periodic (by simp [period, Real.pi_pos])
    (periodic_height hknot u) (continuous_height hknot u)

theorem exists_isLocalMin_height {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space) :
    ∃ t, IsLocalMin (height r u) t := by
  exact exists_isLocalMin_of_periodic (by simp [period, Real.pi_pos])
    (periodic_height hknot u) (continuous_height hknot u)

theorem exists_isMaxOn_univ_height_mem_Icc {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) :
    ∃ t ∈ Icc (0 : ℝ) period, IsMaxOn (height r u) univ t := by
  have hp : 0 < period := by simp [period, Real.pi_pos]
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr hp.le) (continuous_height hknot u).continuousOn
  refine ⟨t, ht, ?_⟩
  intro x _hx
  obtain ⟨y, hy, hxy⟩ := (periodic_height hknot u).exists_mem_Ico₀ hp x
  change height r u x ≤ height r u t
  rw [hxy]
  exact hmax ⟨hy.1, hy.2.le⟩

theorem exists_isMinOn_univ_height_mem_Icc {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) :
    ∃ t ∈ Icc (0 : ℝ) period, IsMinOn (height r u) univ t := by
  have hp : 0 < period := by simp [period, Real.pi_pos]
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr hp.le) (continuous_height hknot u).continuousOn
  refine ⟨t, ht, ?_⟩
  intro x _hx
  obtain ⟨y, hy, hxy⟩ := (periodic_height hknot u).exists_mem_Ico₀ hp x
  change height r u t ≤ height r u x
  rw [hxy]
  exact hmin ⟨hy.1, hy.2.le⟩

theorem inner_unitTangent_eq_zero_of_isLocalMax_height {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) (t : ℝ)
    (hmax : IsLocalMax (height r u) t) :
    inner ℝ u (unitTangent r t) = 0 := by
  have hzero := hmax.hasDerivAt_eq_zero (hasDerivAt_height hknot u t)
  simp [unitTangent, real_inner_smul_right, hzero]

theorem inner_unitTangent_eq_zero_of_isLocalMin_height {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) (t : ℝ)
    (hmin : IsLocalMin (height r u) t) :
    inner ℝ u (unitTangent r t) = 0 := by
  have hzero := hmin.hasDerivAt_eq_zero (hasDerivAt_height hknot u t)
  simp [unitTangent, real_inner_smul_right, hzero]

theorem inner_unitTangent_eq_zero_of_height_constant {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) (c : ℝ)
    (hconst : height r u = fun _ => c) (t : ℝ) :
    inner ℝ u (unitTangent r t) = 0 := by
  have hderiv := hasDerivAt_height hknot u t
  rw [hconst] at hderiv
  have hzero : inner ℝ u (velocity r t) = 0 :=
    hderiv.unique (hasDerivAt_const (x := t) (c := c))
  simp [unitTangent, real_inner_smul_right, hzero]

theorem exists_two_distinct_inner_unitTangent_eq_zero {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) :
    ∃ t₁ t₂ : ℝ,
      t₁ ∈ Ico (0 : ℝ) period ∧ t₂ ∈ Ico (0 : ℝ) period ∧ t₁ ≠ t₂ ∧
        inner ℝ u (unitTangent r t₁) = 0 ∧ inner ℝ u (unitTangent r t₂) = 0 := by
  have hp : 0 < period := by simp [period, Real.pi_pos]
  obtain ⟨tmax, _htmax, hmax⟩ := exists_isMaxOn_univ_height_mem_Icc hknot u
  obtain ⟨tmin, _htmin, hmin⟩ := exists_isMinOn_univ_height_mem_Icc hknot u
  by_cases hvalues : height r u tmax = height r u tmin
  · have hconstPoint : ∀ x, height r u x = height r u tmax := by
      intro x
      apply le_antisymm
      · exact hmax (by simp)
      · rw [hvalues]
        exact hmin (by simp)
    have hconst : height r u = fun _ => height r u tmax := funext hconstPoint
    refine ⟨0, period / 2, ⟨le_rfl, hp⟩, ?_, ?_,
      inner_unitTangent_eq_zero_of_height_constant hknot u _ hconst 0,
      inner_unitTangent_eq_zero_of_height_constant hknot u _ hconst (period / 2)⟩
    · constructor <;> linarith
    · linarith
  · have hzmax : inner ℝ u (unitTangent r tmax) = 0 :=
      inner_unitTangent_eq_zero_of_isLocalMax_height hknot u tmax
        (hmax.isLocalMax (by simp))
    have hzmin : inner ℝ u (unitTangent r tmin) = 0 :=
      inner_unitTangent_eq_zero_of_isLocalMin_height hknot u tmin
        (hmin.isLocalMin (by simp))
    have hpair : Function.Periodic
        (fun t => (height r u t, unitTangent r t)) period := by
      intro t
      apply Prod.ext
      · exact periodic_height hknot u t
      · exact periodic_unitTangent hknot t
    obtain ⟨t₁, ht₁, ht₁eq⟩ := hpair.exists_mem_Ico₀ hp tmax
    obtain ⟨t₂, ht₂, ht₂eq⟩ := hpair.exists_mem_Ico₀ hp tmin
    have ht₁height : height r u t₁ = height r u tmax := (congrArg Prod.fst ht₁eq).symm
    have ht₂height : height r u t₂ = height r u tmin := (congrArg Prod.fst ht₂eq).symm
    have ht₁tangent : unitTangent r t₁ = unitTangent r tmax :=
      (congrArg Prod.snd ht₁eq).symm
    have ht₂tangent : unitTangent r t₂ = unitTangent r tmin :=
      (congrArg Prod.snd ht₂eq).symm
    refine ⟨t₁, t₂, ht₁, ht₂, ?_, ?_, ?_⟩
    · intro ht
      apply hvalues
      rw [← ht₁height, ht, ht₂height]
    · rw [ht₁tangent]
      exact hzmax
    · rw [ht₂tangent]
      exact hzmin

noncomputable def directionalUnitTangent (r : ℝ → Space) (u : Space) (t : ℝ) : ℝ :=
  inner ℝ u (unitTangent r t)

theorem hasDerivAt_directionalUnitTangent {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) (t : ℝ) :
    HasDerivAt (directionalUnitTangent r u)
      (inner ℝ u (deriv (unitTangent r) t)) t := by
  have hdiff : HasDerivAt (unitTangent r) (deriv (unitTangent r) t) t :=
    (((contDiff_unitTangent hknot).differentiable (by simp)).differentiableAt).hasDerivAt
  convert (innerSL ℝ u).hasFDerivAt.comp_hasDerivAt t hdiff using 1 <;> rfl

theorem continuous_directionalUnitTangent {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) :
    Continuous (directionalUnitTangent r u) :=
  (innerSL ℝ u).continuous.comp (contDiff_unitTangent hknot).continuous

theorem periodic_directionalUnitTangent {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) :
    Function.Periodic (directionalUnitTangent r u) period := by
  intro t
  simp [directionalUnitTangent, periodic_unitTangent hknot t]

theorem periodic_deriv_directionalUnitTangent {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) :
    Function.Periodic (deriv (directionalUnitTangent r u)) period :=
  periodic_deriv_real (periodic_directionalUnitTangent hknot u)

theorem deriv_height_eq_speed_mul_directionalUnitTangent {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) (t : ℝ) :
    deriv (height r u) t =
      ‖velocity r t‖ * directionalUnitTangent r u t := by
  rw [(hasDerivAt_height hknot u t).deriv]
  simp [directionalUnitTangent, unitTangent, real_inner_smul_right,
    norm_ne_zero_iff.mpr (hknot.regular t)]

def tangentGreatCircleIntersections (r : ℝ → Space) (u : Space) : Set ℝ :=
  {t | t ∈ Ico (0 : ℝ) period ∧ directionalUnitTangent r u t = 0}

theorem two_le_ncard_tangentGreatCircleIntersections {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space)
    (hfinite : (tangentGreatCircleIntersections r u).Finite) :
    2 ≤ (tangentGreatCircleIntersections r u).ncard := by
  obtain ⟨t₁, t₂, ht₁, ht₂, hne, hz₁, hz₂⟩ :=
    exists_two_distinct_inner_unitTangent_eq_zero hknot u
  have hsubset : ({t₁, t₂} : Set ℝ) ⊆ tangentGreatCircleIntersections r u := by
    intro t ht
    rcases ht with rfl | ht
    · exact ⟨ht₁, hz₁⟩
    · have : t = t₂ := by simpa using ht
      subst t
      exact ⟨ht₂, hz₂⟩
  rw [← Set.ncard_pair hne]
  exact Set.ncard_le_ncard hsubset hfinite

def tangentGreatCircleIntersectionsIcc (r : ℝ → Space) (u : Space) : Set ℝ :=
  {t | t ∈ Icc (0 : ℝ) period ∧ directionalUnitTangent r u t = 0}

def IsNondegenerateDirection (r : ℝ → Space) (u : Space) : Prop :=
  ∀ t ∈ tangentGreatCircleIntersectionsIcc r u,
    inner ℝ u (deriv (unitTangent r) t) ≠ 0

theorem nonzero_of_isNondegenerateDirection {r : ℝ → Space}
    (hknot : IsSmoothKnot r) {u : Space}
    (hgeneric : IsNondegenerateDirection r u) : u ≠ 0 := by
  intro hu
  subst u
  obtain ⟨t, _t₂, ht, _ht₂, _hne, hz, _hz₂⟩ :=
    exists_two_distinct_inner_unitTangent_eq_zero hknot 0
  have htIcc : t ∈ tangentGreatCircleIntersectionsIcc r 0 :=
    ⟨⟨ht.1, ht.2.le⟩, hz⟩
  exact hgeneric t htIcc (by simp)

theorem directionalUnitTangent_smul (r : ℝ → Space) (u : Space)
    (c t : ℝ) :
    directionalUnitTangent r (c • u) t = c * directionalUnitTangent r u t := by
  simp [directionalUnitTangent, real_inner_smul_left]

theorem tangentGreatCircleIntersections_smul {r : ℝ → Space} {u : Space}
    {c : ℝ} (hc : c ≠ 0) :
    tangentGreatCircleIntersections r (c • u) =
      tangentGreatCircleIntersections r u := by
  ext t
  simp [tangentGreatCircleIntersections, directionalUnitTangent_smul, hc]

theorem tangentGreatCircleIntersectionsIcc_smul {r : ℝ → Space} {u : Space}
    {c : ℝ} (hc : c ≠ 0) :
    tangentGreatCircleIntersectionsIcc r (c • u) =
      tangentGreatCircleIntersectionsIcc r u := by
  ext t
  simp [tangentGreatCircleIntersectionsIcc, directionalUnitTangent_smul, hc]

theorem isNondegenerateDirection_smul_iff {r : ℝ → Space} {u : Space}
    {c : ℝ} (hc : c ≠ 0) :
    IsNondegenerateDirection r (c • u) ↔ IsNondegenerateDirection r u := by
  rw [IsNondegenerateDirection, IsNondegenerateDirection,
    tangentGreatCircleIntersectionsIcc_smul hc]
  simp [real_inner_smul_left, hc]

noncomputable def normalizedDirection (u : Space) : Space :=
  ‖u‖⁻¹ • u

theorem norm_normalizedDirection {u : Space} (hu : u ≠ 0) :
    ‖normalizedDirection u‖ = 1 := by
  simp [normalizedDirection, norm_smul, hu]

theorem tangentGreatCircleIntersections_normalizedDirection {r : ℝ → Space}
    {u : Space} (hu : u ≠ 0) :
    tangentGreatCircleIntersections r (normalizedDirection u) =
      tangentGreatCircleIntersections r u := by
  exact tangentGreatCircleIntersections_smul (inv_ne_zero (norm_ne_zero_iff.mpr hu))

theorem isNondegenerateDirection_normalizedDirection_iff {r : ℝ → Space}
    {u : Space} (hu : u ≠ 0) :
    IsNondegenerateDirection r (normalizedDirection u) ↔
      IsNondegenerateDirection r u := by
  exact isNondegenerateDirection_smul_iff (inv_ne_zero (norm_ne_zero_iff.mpr hu))

theorem isCompact_tangentGreatCircleIntersectionsIcc {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) :
    IsCompact (tangentGreatCircleIntersectionsIcc r u) := by
  apply isCompact_Icc.of_isClosed_subset
  · rw [tangentGreatCircleIntersectionsIcc]
    exact isClosed_Icc.inter
      (isClosed_eq (continuous_directionalUnitTangent hknot u) continuous_const)
  · intro t ht
    exact ht.1

theorem isDiscrete_tangentGreatCircleIntersectionsIcc_of_nondegenerate
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space)
    (hgeneric : IsNondegenerateDirection r u) :
    IsDiscrete (tangentGreatCircleIntersectionsIcc r u) := by
  apply IsDiscrete.of_nhdsWithin
  intro t ht
  rw [Filter.le_pure_iff]
  apply eventually_nhdsWithin_iff.2
  have hne := (hasDerivAt_directionalUnitTangent hknot u t).eventually_ne
    (hgeneric t ht) (c := 0)
  have hne' := eventually_nhdsWithin_iff.1 hne
  filter_upwards [hne'] with z hz
  intro hzmem
  change z = t
  by_contra hzt
  exact hz hzt hzmem.2

theorem finite_tangentGreatCircleIntersectionsIcc_of_nondegenerate
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space)
    (hgeneric : IsNondegenerateDirection r u) :
    (tangentGreatCircleIntersectionsIcc r u).Finite :=
  (isCompact_tangentGreatCircleIntersectionsIcc hknot u).finite
    (isDiscrete_tangentGreatCircleIntersectionsIcc_of_nondegenerate hknot u hgeneric)

theorem finite_tangentGreatCircleIntersections_of_nondegenerate
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space)
    (hgeneric : IsNondegenerateDirection r u) :
    (tangentGreatCircleIntersections r u).Finite := by
  apply (finite_tangentGreatCircleIntersectionsIcc_of_nondegenerate hknot u hgeneric).subset
  intro t ht
  exact ⟨⟨ht.1.1, ht.1.2.le⟩, ht.2⟩

theorem two_le_ncard_tangentGreatCircleIntersections_of_nondegenerate
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space)
    (hgeneric : IsNondegenerateDirection r u) :
    2 ≤ (tangentGreatCircleIntersections r u).ncard :=
  two_le_ncard_tangentGreatCircleIntersections hknot u
    (finite_tangentGreatCircleIntersections_of_nondegenerate hknot u hgeneric)

theorem eventually_sign_directionalUnitTangent_eq_of_nondegenerate
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space) {t : ℝ}
    (hgeneric : IsNondegenerateDirection r u)
    (ht : t ∈ tangentGreatCircleIntersectionsIcc r u) :
    (∀ᶠ x in 𝓝 t,
        SignType.sign (directionalUnitTangent r u x) = SignType.sign (x - t)) ∨
      (∀ᶠ x in 𝓝 t,
        SignType.sign (directionalUnitTangent r u x) = SignType.sign (t - x)) := by
  have hderiv := (hasDerivAt_directionalUnitTangent hknot u t).deriv
  have hne : deriv (directionalUnitTangent r u) t ≠ 0 := by
    rw [hderiv]
    exact hgeneric t ht
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · exact Or.inr (eventually_nhdsWithin_sign_eq_of_deriv_neg hneg ht.2)
  · exact Or.inl (eventually_nhdsWithin_sign_eq_of_deriv_pos hpos ht.2)

theorem deriv_mul_deriv_neg_of_consecutive_zeros {f : ℝ → ℝ} {a b : ℝ}
    (hf : Continuous f) (hab : a < b) (hfa : f a = 0) (hfb : f b = 0)
    (hda : deriv f a ≠ 0) (hdb : deriv f b ≠ 0)
    (hnozero : ∀ x ∈ Ioo a b, f x ≠ 0) :
    deriv f a * deriv f b < 0 := by
  have ham : a < (a + b) / 2 := by linarith
  have hmb : (a + b) / 2 < b := by linarith
  rcases lt_or_gt_of_ne hda with hdaNeg | hdaPos
  · rcases lt_or_gt_of_ne hdb with hdbNeg | hdbPos
    · exfalso
      have haSign : ∀ᶠ x in 𝓝[>] a,
          SignType.sign (f x) = SignType.sign (a - x) :=
        (eventually_nhdsWithin_sign_eq_of_deriv_neg hdaNeg hfa).filter_mono
          nhdsWithin_le_nhds
      have haBound : ∀ᶠ x in 𝓝[>] a, x < (a + b) / 2 :=
        (eventually_lt_nhds ham).filter_mono nhdsWithin_le_nhds
      have haEventually : ∀ᶠ x in 𝓝[>] a,
          SignType.sign (f x) = SignType.sign (a - x) ∧
            a < x ∧ x < (a + b) / 2 := by
        filter_upwards [haSign, self_mem_nhdsWithin, haBound] with x hs hax hxm
        exact ⟨hs, hax, hxm⟩
      obtain ⟨x, hxSign, hax, hxm⟩ := haEventually.exists
      have hxNeg : f x < 0 := sign_eq_neg_one_iff.mp (by
        rw [hxSign]
        exact sign_neg (sub_neg.mpr hax))
      have hbSign : ∀ᶠ y in 𝓝[<] b,
          SignType.sign (f y) = SignType.sign (b - y) :=
        (eventually_nhdsWithin_sign_eq_of_deriv_neg hdbNeg hfb).filter_mono
          nhdsWithin_le_nhds
      have hbBound : ∀ᶠ y in 𝓝[<] b, (a + b) / 2 < y :=
        (eventually_gt_nhds hmb).filter_mono nhdsWithin_le_nhds
      have hbEventually : ∀ᶠ y in 𝓝[<] b,
          SignType.sign (f y) = SignType.sign (b - y) ∧
            (a + b) / 2 < y ∧ y < b := by
        filter_upwards [hbSign, hbBound, self_mem_nhdsWithin] with y hs hmy hyb
        exact ⟨hs, hmy, hyb⟩
      obtain ⟨y, hySign, hmy, hyb⟩ := hbEventually.exists
      have hyPos : 0 < f y := sign_eq_one_iff.mp (by
        rw [hySign]
        exact sign_pos (sub_pos.mpr hyb))
      have hxy : x < y := hxm.trans hmy
      have hzeroImage : 0 ∈ f '' Icc x y :=
        intermediate_value_Icc hxy.le hf.continuousOn ⟨hxNeg.le, hyPos.le⟩
      obtain ⟨z, hz, hfz⟩ := hzeroImage
      exact hnozero z ⟨hax.trans_le hz.1, hz.2.trans_lt hyb⟩ hfz
    · exact mul_neg_of_neg_of_pos hdaNeg hdbPos
  · rcases lt_or_gt_of_ne hdb with hdbNeg | hdbPos
    · exact mul_neg_of_pos_of_neg hdaPos hdbNeg
    · exfalso
      have haSign : ∀ᶠ x in 𝓝[>] a,
          SignType.sign (f x) = SignType.sign (x - a) :=
        (eventually_nhdsWithin_sign_eq_of_deriv_pos hdaPos hfa).filter_mono
          nhdsWithin_le_nhds
      have haBound : ∀ᶠ x in 𝓝[>] a, x < (a + b) / 2 :=
        (eventually_lt_nhds ham).filter_mono nhdsWithin_le_nhds
      have haEventually : ∀ᶠ x in 𝓝[>] a,
          SignType.sign (f x) = SignType.sign (x - a) ∧
            a < x ∧ x < (a + b) / 2 := by
        filter_upwards [haSign, self_mem_nhdsWithin, haBound] with x hs hax hxm
        exact ⟨hs, hax, hxm⟩
      obtain ⟨x, hxSign, hax, hxm⟩ := haEventually.exists
      have hxPos : 0 < f x := sign_eq_one_iff.mp (by
        rw [hxSign]
        exact sign_pos (sub_pos.mpr hax))
      have hbSign : ∀ᶠ y in 𝓝[<] b,
          SignType.sign (f y) = SignType.sign (y - b) :=
        (eventually_nhdsWithin_sign_eq_of_deriv_pos hdbPos hfb).filter_mono
          nhdsWithin_le_nhds
      have hbBound : ∀ᶠ y in 𝓝[<] b, (a + b) / 2 < y :=
        (eventually_gt_nhds hmb).filter_mono nhdsWithin_le_nhds
      have hbEventually : ∀ᶠ y in 𝓝[<] b,
          SignType.sign (f y) = SignType.sign (y - b) ∧
            (a + b) / 2 < y ∧ y < b := by
        filter_upwards [hbSign, hbBound, self_mem_nhdsWithin] with y hs hmy hyb
        exact ⟨hs, hmy, hyb⟩
      obtain ⟨y, hySign, hmy, hyb⟩ := hbEventually.exists
      have hyNeg : f y < 0 := sign_eq_neg_one_iff.mp (by
        rw [hySign]
        exact sign_neg (sub_neg.mpr hyb))
      have hxy : x < y := hxm.trans hmy
      have hzeroImage : 0 ∈ f '' Icc x y :=
        intermediate_value_Icc' hxy.le hf.continuousOn ⟨hyNeg.le, hxPos.le⟩
      obtain ⟨z, hz, hfz⟩ := hzeroImage
      exact hnozero z ⟨hax.trans_le hz.1, hz.2.trans_lt hyb⟩ hfz

theorem pos_on_Ioo_of_deriv_pos_of_no_zeros {f : ℝ → ℝ} {a b : ℝ}
    (hf : Continuous f) (_hab : a < b) (hfa : f a = 0) (hda : 0 < deriv f a)
    (hnozero : ∀ x ∈ Ioo a b, f x ≠ 0) :
    ∀ x ∈ Ioo a b, 0 < f x := by
  intro x hx
  rcases (hnozero x hx).lt_or_gt with hxNeg | hxPos
  · have haSign : ∀ᶠ y in 𝓝[>] a,
        SignType.sign (f y) = SignType.sign (y - a) :=
      (eventually_nhdsWithin_sign_eq_of_deriv_pos hda hfa).filter_mono
        nhdsWithin_le_nhds
    have haBound : ∀ᶠ y in 𝓝[>] a, y < x :=
      (eventually_lt_nhds hx.1).filter_mono nhdsWithin_le_nhds
    have haEventually : ∀ᶠ y in 𝓝[>] a,
        SignType.sign (f y) = SignType.sign (y - a) ∧ a < y ∧ y < x := by
      filter_upwards [haSign, self_mem_nhdsWithin, haBound] with y hs hay hyx
      exact ⟨hs, hay, hyx⟩
    obtain ⟨y, hySign, hay, hyx⟩ := haEventually.exists
    have hyPos : 0 < f y := sign_eq_one_iff.mp (by
      rw [hySign]
      exact sign_pos (sub_pos.mpr hay))
    have hzeroImage : 0 ∈ f '' Icc y x :=
      intermediate_value_Icc' hyx.le hf.continuousOn ⟨hxNeg.le, hyPos.le⟩
    obtain ⟨z, hz, hfz⟩ := hzeroImage
    exact (hnozero z ⟨hay.trans_le hz.1, hz.2.trans_lt hx.2⟩ hfz).elim
  · exact hxPos

theorem neg_on_Ioo_of_deriv_neg_of_no_zeros {f : ℝ → ℝ} {a b : ℝ}
    (hf : Continuous f) (hab : a < b) (hfa : f a = 0) (hda : deriv f a < 0)
    (hnozero : ∀ x ∈ Ioo a b, f x ≠ 0) :
    ∀ x ∈ Ioo a b, f x < 0 := by
  have hpos := pos_on_Ioo_of_deriv_pos_of_no_zeros
    (f := fun x => -f x) hf.neg hab (by simp [hfa]) (by simpa [deriv.neg])
    (by
      intro x hx hzero
      exact hnozero x hx (neg_eq_zero.mp hzero))
  intro x hx
  have := hpos x hx
  simpa using this

theorem strictMonoOn_height_Icc_of_directional_deriv_pos_of_no_zeros
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hab : a < b) (hfa : directionalUnitTangent r u a = 0)
    (hda : 0 < deriv (directionalUnitTangent r u) a)
    (hnozero : ∀ x ∈ Ioo a b, directionalUnitTangent r u x ≠ 0) :
    StrictMonoOn (height r u) (Icc a b) := by
  have hpos := pos_on_Ioo_of_deriv_pos_of_no_zeros
    (continuous_directionalUnitTangent hknot u) hab hfa hda hnozero
  apply strictMonoOn_of_deriv_pos (convex_Icc a b) (continuous_height hknot u).continuousOn
  intro x hx
  rw [interior_Icc] at hx
  rw [deriv_height_eq_speed_mul_directionalUnitTangent hknot u x]
  exact mul_pos (norm_pos_iff.mpr (hknot.regular x)) (hpos x hx)

theorem strictAntiOn_height_Icc_of_directional_deriv_neg_of_no_zeros
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hab : a < b) (hfa : directionalUnitTangent r u a = 0)
    (hda : deriv (directionalUnitTangent r u) a < 0)
    (hnozero : ∀ x ∈ Ioo a b, directionalUnitTangent r u x ≠ 0) :
    StrictAntiOn (height r u) (Icc a b) := by
  have hneg := neg_on_Ioo_of_deriv_neg_of_no_zeros
    (continuous_directionalUnitTangent hknot u) hab hfa hda hnozero
  apply strictAntiOn_of_deriv_neg (convex_Icc a b) (continuous_height hknot u).continuousOn
  intro x hx
  rw [interior_Icc] at hx
  rw [deriv_height_eq_speed_mul_directionalUnitTangent hknot u x]
  exact mul_neg_of_pos_of_neg (norm_pos_iff.mpr (hknot.regular x)) (hneg x hx)

theorem even_ncard_tangentGreatCircleIntersections_of_nondegenerate
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space)
    (hgeneric : IsNondegenerateDirection r u) :
    Even (tangentGreatCircleIntersections r u).ncard := by
  classical
  let S := tangentGreatCircleIntersections r u
  have hfinite : S.Finite := by
    simpa [S] using finite_tangentGreatCircleIntersections_of_nondegenerate hknot u hgeneric
  let s : Finset ℝ := hfinite.toFinset
  have hs (x : ℝ) : x ∈ s ↔ x ∈ S := by simp [s]
  have htwo : 2 ≤ s.card := by
    simpa [s, S, Set.ncard_eq_toFinset_card _ hfinite] using
      two_le_ncard_tangentGreatCircleIntersections_of_nondegenerate hknot u hgeneric
  let m := s.card - 2
  have hm : s.card = m + 2 := by
    dsimp [m]
    omega
  let e : Fin (m + 2) ≃o {x // x ∈ s} := s.orderIsoOfFin hm
  have heS (i : Fin (m + 2)) : (e i : ℝ) ∈ S :=
    (hs _).mp (e i).property
  have hderivNe (i : Fin (m + 2)) :
      deriv (directionalUnitTangent r u) (e i) ≠ 0 := by
    rw [(hasDerivAt_directionalUnitTangent hknot u (e i)).deriv]
    exact hgeneric _ ⟨⟨(heS i).1.1, (heS i).1.2.le⟩, (heS i).2⟩
  have hmin (z : {x // x ∈ s}) : (e 0 : ℝ) ≤ z := by
    simpa using e.monotone (Fin.zero_le (e.symm z))
  have hmax (z : {x // x ∈ s}) : (z : ℝ) ≤ e (Fin.last (m + 1)) := by
    simpa using e.monotone (Fin.le_last (e.symm z))
  have hprodNeg (i : Fin (m + 2)) :
      deriv (directionalUnitTangent r u) (e i) *
          deriv (directionalUnitTangent r u) (e (finRotate (m + 2) i)) < 0 := by
    by_cases hi : i = Fin.last (m + 1)
    · subst i
      have hab : (e (Fin.last (m + 1)) : ℝ) < (e 0 : ℝ) + period := by
        have hlast := (heS (Fin.last (m + 1))).1.2
        have hzero := (heS 0).1.1
        linarith
      have hfa : directionalUnitTangent r u (e (Fin.last (m + 1))) = 0 :=
        (heS (Fin.last (m + 1))).2
      have hfb : directionalUnitTangent r u ((e 0 : ℝ) + period) = 0 := by
        rw [periodic_directionalUnitTangent hknot u (e 0)]
        exact (heS 0).2
      have hdb : deriv (directionalUnitTangent r u) ((e 0 : ℝ) + period) ≠ 0 := by
        rw [periodic_deriv_directionalUnitTangent hknot u (e 0)]
        exact hderivNe 0
      have hnozero : ∀ z ∈ Ioo (e (Fin.last (m + 1)) : ℝ) ((e 0 : ℝ) + period),
          directionalUnitTangent r u z ≠ 0 := by
        intro z hz hz0
        by_cases hzp : z < period
        · have hzIco : z ∈ Ico (0 : ℝ) period := by
            exact ⟨(heS (Fin.last (m + 1))).1.1.trans hz.1.le, hzp⟩
          have hzS : z ∈ S := ⟨hzIco, hz0⟩
          let zsub : {x // x ∈ s} := ⟨z, (hs z).mpr hzS⟩
          have hzle : z ≤ (e (Fin.last (m + 1)) : ℝ) := hmax zsub
          exact (not_lt_of_ge hzle) hz.1
        · have hpz : period ≤ z := le_of_not_gt hzp
          let z' := z - period
          have hz'zero : directionalUnitTangent r u z' = 0 := by
            have hper := periodic_directionalUnitTangent hknot u z'
            have hz'eq : z' + period = z := by dsimp [z']; ring
            rw [hz'eq] at hper
            rw [← hper]
            exact hz0
          have hz'Ico : z' ∈ Ico (0 : ℝ) period := by
            constructor
            · dsimp [z']
              linarith
            · have hzeroLt := (heS 0).1.2
              dsimp [z']
              linarith [hz.2]
          have hz'S : z' ∈ S := ⟨hz'Ico, hz'zero⟩
          let zsub : {x // x ∈ s} := ⟨z', (hs z').mpr hz'S⟩
          have hminle : (e 0 : ℝ) ≤ z' := hmin zsub
          have hz'lt : z' < (e 0 : ℝ) := by
            dsimp [z']
            linarith [hz.2]
          exact (not_lt_of_ge hminle) hz'lt
      have hneg := deriv_mul_deriv_neg_of_consecutive_zeros
        (continuous_directionalUnitTangent hknot u) hab hfa hfb
        (hderivNe (Fin.last (m + 1))) hdb hnozero
      rw [periodic_deriv_directionalUnitTangent hknot u (e 0)] at hneg
      simpa using hneg
    · have hrotVal : ((finRotate (m + 2) i : Fin (m + 2)) : ℕ) = i + 1 := by
        simpa using coe_finRotate_of_ne_last hi
      have hab : (e i : ℝ) < e (finRotate (m + 2) i) := by
        apply e.strictMono
        exact_mod_cast (show (i : ℕ) < (finRotate (m + 2) i : Fin (m + 2)) from by omega)
      have hnozero : ∀ z ∈ Ioo (e i : ℝ) (e (finRotate (m + 2) i)),
          directionalUnitTangent r u z ≠ 0 := by
        intro z hz hz0
        have hzIco : z ∈ Ico (0 : ℝ) period := by
          exact ⟨(heS i).1.1.trans hz.1.le,
            hz.2.trans (heS (finRotate (m + 2) i)).1.2⟩
        have hzS : z ∈ S := ⟨hzIco, hz0⟩
        let zsub : {x // x ∈ s} := ⟨z, (hs z).mpr hzS⟩
        have hik : i < e.symm zsub := by
          have h := e.symm.strictMono (show e i < zsub from hz.1)
          simpa using h
        have hkj : e.symm zsub < finRotate (m + 2) i := by
          have h := e.symm.strictMono
            (show zsub < e (finRotate (m + 2) i) from hz.2)
          simpa using h
        omega
      exact deriv_mul_deriv_neg_of_consecutive_zeros
        (continuous_directionalUnitTangent hknot u) hab (heS i).2
        (heS (finRotate (m + 2) i)).2 (hderivNe i)
        (hderivNe (finRotate (m + 2) i)) hnozero
  let g : Fin (m + 2) → ℝ :=
    fun i => Real.sign (deriv (directionalUnitTangent r u) (e i))
  have hflip (i : Fin (m + 2)) : g (finRotate (m + 2) i) = -g i := by
    change Real.sign
        (deriv (directionalUnitTangent r u) (e (finRotate (m + 2) i))) =
      -Real.sign (deriv (directionalUnitTangent r u) (e i))
    rcases (mul_neg_iff.mp (hprodNeg i)) with h | h
    · rw [Real.sign_of_neg h.2, Real.sign_of_pos h.1]
    · rw [Real.sign_of_pos h.2, Real.sign_of_neg h.1]
      norm_num
  have hperm : (∏ i, g (finRotate (m + 2) i)) = ∏ i, g i := by
    simpa using (finRotate (m + 2)).prod_comp Finset.univ g (by simp)
  have hEq : (∏ i, g i) = (-1 : ℝ) ^ (m + 2) * ∏ i, g i := calc
    _ = ∏ i, g (finRotate (m + 2) i) := hperm.symm
    _ = ∏ i, -g i := by
      apply Finset.prod_congr rfl
      intro i _hi
      exact hflip i
    _ = (-1 : ℝ) ^ (m + 2) * ∏ i, g i := by
      simpa using (Finset.prod_neg (s := Finset.univ) g)
  have hgNe (i : Fin (m + 2)) : g i ≠ 0 := by
    dsimp [g]
    rw [Real.sign_eq_zero_iff]
    exact hderivNe i
  have hprodNe : (∏ i, g i) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun i _hi => hgNe i
  have hpow : (-1 : ℝ) ^ (m + 2) = 1 := by
    apply mul_right_cancel₀ hprodNe
    simpa using hEq.symm
  have heven : Even (m + 2) :=
    (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℝ) ≠ 1)).mp hpow
  change Even S.ncard
  rw [Set.ncard_eq_toFinset_card S hfinite]
  change Even s.card
  rw [hm]
  exact heven

theorem ncard_tangentGreatCircleIntersections_eq_two_of_nondegenerate_of_lt_four
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space)
    (hgeneric : IsNondegenerateDirection r u)
    (hlt : (tangentGreatCircleIntersections r u).ncard < 4) :
    (tangentGreatCircleIntersections r u).ncard = 2 := by
  have hlo := two_le_ncard_tangentGreatCircleIntersections_of_nondegenerate
    hknot u hgeneric
  obtain ⟨k, hk⟩ := even_ncard_tangentGreatCircleIntersections_of_nondegenerate
    hknot u hgeneric
  omega

theorem hasDerivAt_velocity {r : ℝ → Space} (hknot : IsSmoothKnot r) (t : ℝ) :
    HasDerivAt (velocity r) (acceleration r t) t := by
  have hdiff : DifferentiableAt ℝ (velocity r) t :=
    ((contDiff_velocity hknot).differentiable (by simp)).differentiableAt
  simpa [acceleration] using hdiff.hasDerivAt

theorem hasDerivAt_speed {r : ℝ → Space} (hknot : IsSmoothKnot r) (t : ℝ) :
    HasDerivAt (fun x => ‖velocity r x‖)
      (inner ℝ (velocity r t) (acceleration r t) / ‖velocity r t‖) t := by
  have hspeedCont : ContDiff ℝ ⊤ (fun x => ‖velocity r x‖) :=
    (contDiff_velocity hknot).norm ℝ hknot.regular
  have hspeedDiff : DifferentiableAt ℝ (fun x => ‖velocity r x‖) t :=
    (hspeedCont.differentiable (by simp)).differentiableAt
  have hspeed := hspeedDiff.hasDerivAt
  have hspeedSq :
      HasDerivAt (fun x => ‖velocity r x‖ ^ 2)
        (2 * ‖velocity r t‖ * deriv (fun x => ‖velocity r x‖) t) t := by
    convert hspeed.mul hspeed using 1 <;> try rfl
    · ext x
      simp [pow_two]
    · ring
  have hderivEq := (hasDerivAt_velocity hknot t).norm_sq.unique hspeedSq
  have hspeedNe : ‖velocity r t‖ ≠ 0 := norm_ne_zero_iff.mpr (hknot.regular t)
  have hformula :
      deriv (fun x => ‖velocity r x‖) t =
        inner ℝ (velocity r t) (acceleration r t) / ‖velocity r t‖ := by
    rw [eq_div_iff hspeedNe]
    nlinarith
  rw [← hformula]
  exact hspeed

theorem hasDerivAt_deriv_height_of_directionalUnitTangent_eq_zero
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space) (t : ℝ)
    (hz : directionalUnitTangent r u t = 0) :
    HasDerivAt (deriv (height r u))
      (‖velocity r t‖ * inner ℝ u (deriv (unitTangent r) t)) t := by
  have heq : deriv (height r u) =
      fun x => ‖velocity r x‖ * directionalUnitTangent r u x := by
    funext x
    exact deriv_height_eq_speed_mul_directionalUnitTangent hknot u x
  rw [heq]
  have hprod := (hasDerivAt_speed hknot t).mul
    (hasDerivAt_directionalUnitTangent hknot u t)
  simp only [hz, mul_zero, zero_add] at hprod
  convert hprod using 1 <;> rfl

theorem deriv_height_eq_zero_of_directionalUnitTangent_eq_zero
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space) (t : ℝ)
    (hz : directionalUnitTangent r u t = 0) :
    deriv (height r u) t = 0 := by
  rw [deriv_height_eq_speed_mul_directionalUnitTangent hknot u t, hz, mul_zero]

theorem isLocalMin_height_of_directionalUnitTangent_deriv_pos
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space) (t : ℝ)
    (hz : directionalUnitTangent r u t = 0)
    (hpos : 0 < inner ℝ u (deriv (unitTangent r) t)) :
    IsLocalMin (height r u) t := by
  apply isLocalMin_of_deriv_deriv_pos
  · rw [(hasDerivAt_deriv_height_of_directionalUnitTangent_eq_zero
      hknot u t hz).deriv]
    exact mul_pos (norm_pos_iff.mpr (hknot.regular t)) hpos
  · exact deriv_height_eq_zero_of_directionalUnitTangent_eq_zero hknot u t hz
  · exact (continuous_height hknot u).continuousAt

theorem isLocalMax_height_of_directionalUnitTangent_deriv_neg
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space) (t : ℝ)
    (hz : directionalUnitTangent r u t = 0)
    (hneg : inner ℝ u (deriv (unitTangent r) t) < 0) :
    IsLocalMax (height r u) t := by
  apply isLocalMax_of_deriv_deriv_neg
  · rw [(hasDerivAt_deriv_height_of_directionalUnitTangent_eq_zero
      hknot u t hz).deriv]
    exact mul_neg_of_pos_of_neg (norm_pos_iff.mpr (hknot.regular t)) hneg
  · exact deriv_height_eq_zero_of_directionalUnitTangent_eq_zero hknot u t hz
  · exact (continuous_height hknot u).continuousAt

theorem isLocalMin_or_isLocalMax_height_of_nondegenerate
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space) {t : ℝ}
    (hgeneric : IsNondegenerateDirection r u)
    (ht : t ∈ tangentGreatCircleIntersectionsIcc r u) :
    IsLocalMin (height r u) t ∨ IsLocalMax (height r u) t := by
  rcases lt_or_gt_of_ne (hgeneric t ht) with hneg | hpos
  · exact Or.inr
      (isLocalMax_height_of_directionalUnitTangent_deriv_neg hknot u t ht.2 hneg)
  · exact Or.inl
      (isLocalMin_height_of_directionalUnitTangent_deriv_pos hknot u t ht.2 hpos)

theorem not_isLocalMin_and_isLocalMax_height_of_nondegenerate
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space) {t : ℝ}
    (hgeneric : IsNondegenerateDirection r u)
    (ht : t ∈ tangentGreatCircleIntersectionsIcc r u) :
    ¬ (IsLocalMin (height r u) t ∧ IsLocalMax (height r u) t) := by
  intro hboth
  have heq : height r u =ᶠ[nhds t] fun _ => height r u t := by
    filter_upwards [hboth.1, hboth.2] with x hmin hmax
    exact le_antisymm hmax hmin
  have hderivEq : deriv (height r u) =ᶠ[nhds t]
      deriv (fun _ => height r u t) := heq.deriv
  have hsecond : deriv (deriv (height r u)) t = 0 := by
    calc
      deriv (deriv (height r u)) t =
          deriv (deriv (fun _ => height r u t)) t := hderivEq.deriv_eq
      _ = 0 := by simp
  have hformula :=
    (hasDerivAt_deriv_height_of_directionalUnitTangent_eq_zero hknot u t ht.2).deriv
  have hmulzero : ‖velocity r t‖ * inner ℝ u (deriv (unitTangent r) t) = 0 :=
    hformula.symm.trans hsecond
  exact (mul_ne_zero (norm_ne_zero_iff.mpr (hknot.regular t)) (hgeneric t ht)) hmulzero

theorem inner_deriv_unitTangent_neg_of_isLocalMax_height
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space) {t : ℝ}
    (hgeneric : IsNondegenerateDirection r u)
    (ht : t ∈ tangentGreatCircleIntersectionsIcc r u)
    (hmax : IsLocalMax (height r u) t) :
    inner ℝ u (deriv (unitTangent r) t) < 0 := by
  rcases lt_or_gt_of_ne (hgeneric t ht) with hneg | hpos
  · exact hneg
  · exfalso
    exact not_isLocalMin_and_isLocalMax_height_of_nondegenerate
      hknot u hgeneric ht
      ⟨isLocalMin_height_of_directionalUnitTangent_deriv_pos hknot u t ht.2 hpos, hmax⟩

theorem inner_deriv_unitTangent_pos_of_isLocalMin_height
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space) {t : ℝ}
    (hgeneric : IsNondegenerateDirection r u)
    (ht : t ∈ tangentGreatCircleIntersectionsIcc r u)
    (hmin : IsLocalMin (height r u) t) :
    0 < inner ℝ u (deriv (unitTangent r) t) := by
  rcases lt_or_gt_of_ne (hgeneric t ht) with hneg | hpos
  · exfalso
    exact not_isLocalMin_and_isLocalMax_height_of_nondegenerate
      hknot u hgeneric ht
      ⟨hmin, isLocalMax_height_of_directionalUnitTangent_deriv_neg hknot u t ht.2 hneg⟩
  · exact hpos

theorem exists_height_max_min_of_ncard_intersections_eq_two
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space)
    (hgeneric : IsNondegenerateDirection r u)
    (hcard : (tangentGreatCircleIntersections r u).ncard = 2) :
    ∃ tmax tmin : ℝ,
      tmax ≠ tmin ∧ tmax ∈ Ico (0 : ℝ) period ∧ tmin ∈ Ico (0 : ℝ) period ∧
        tangentGreatCircleIntersections r u = {tmax, tmin} ∧
          IsLocalMax (height r u) tmax ∧ IsLocalMin (height r u) tmin := by
  let S := tangentGreatCircleIntersections r u
  obtain ⟨x, y, hxy, hSraw⟩ := Set.ncard_eq_two.mp (by simpa [S] using hcard)
  have hS : S = {x, y} := by simpa [S] using hSraw
  have hxS : x ∈ S := by rw [hS]; simp
  have hyS : y ∈ S := by rw [hS]; simp
  have hordered : ∀ {a b : ℝ}, a ∈ S → b ∈ S → a < b → S = {a, b} →
      (IsLocalMin (height r u) a ∧ IsLocalMax (height r u) b) ∨
        (IsLocalMax (height r u) a ∧ IsLocalMin (height r u) b) := by
    intro a b haS hbS hab hSab
    have haIcc : a ∈ tangentGreatCircleIntersectionsIcc r u :=
      ⟨⟨haS.1.1, haS.1.2.le⟩, haS.2⟩
    have hbIcc : b ∈ tangentGreatCircleIntersectionsIcc r u :=
      ⟨⟨hbS.1.1, hbS.1.2.le⟩, hbS.2⟩
    have hdaNe : deriv (directionalUnitTangent r u) a ≠ 0 := by
      rw [(hasDerivAt_directionalUnitTangent hknot u a).deriv]
      exact hgeneric a haIcc
    have hdbNe : deriv (directionalUnitTangent r u) b ≠ 0 := by
      rw [(hasDerivAt_directionalUnitTangent hknot u b).deriv]
      exact hgeneric b hbIcc
    have hnozero : ∀ z ∈ Ioo a b, directionalUnitTangent r u z ≠ 0 := by
      intro z hz hz0
      have hzIco : z ∈ Ico (0 : ℝ) period :=
        ⟨haS.1.1.trans hz.1.le, hz.2.trans hbS.1.2⟩
      have hzS : z ∈ S := ⟨hzIco, hz0⟩
      rw [hSab] at hzS
      rcases hzS with rfl | hzS
      · exact (lt_irrefl _ hz.1)
      · have : z = b := by simpa using hzS
        subst z
        exact (lt_irrefl _ hz.2)
    have hprod := deriv_mul_deriv_neg_of_consecutive_zeros
      (continuous_directionalUnitTangent hknot u) hab haS.2 hbS.2 hdaNe hdbNe hnozero
    have hdaEq := (hasDerivAt_directionalUnitTangent hknot u a).deriv
    have hdbEq := (hasDerivAt_directionalUnitTangent hknot u b).deriv
    rcases mul_neg_iff.mp hprod with h | h
    · left
      constructor
      · apply isLocalMin_height_of_directionalUnitTangent_deriv_pos hknot u a haS.2
        rw [← hdaEq]
        exact h.1
      · apply isLocalMax_height_of_directionalUnitTangent_deriv_neg hknot u b hbS.2
        rw [← hdbEq]
        exact h.2
    · right
      constructor
      · apply isLocalMax_height_of_directionalUnitTangent_deriv_neg hknot u a haS.2
        rw [← hdaEq]
        exact h.1
      · apply isLocalMin_height_of_directionalUnitTangent_deriv_pos hknot u b hbS.2
        rw [← hdbEq]
        exact h.2
  rcases lt_or_gt_of_ne hxy with hxylt | hyxlt
  · rcases hordered hxS hyS hxylt hS with h | h
    · refine ⟨y, x, hxy.symm, hyS.1, hxS.1, ?_, h.2, h.1⟩
      simpa [S, Set.pair_comm] using hSraw
    · exact ⟨x, y, hxy, hxS.1, hyS.1, hSraw, h.1, h.2⟩
  · have hSyx : S = {y, x} := by simpa [Set.pair_comm] using hS
    rcases hordered hyS hxS hyxlt hSyx with h | h
    · exact ⟨x, y, hxy, hxS.1, hyS.1, hSraw, h.2, h.1⟩
    · refine ⟨y, x, hxy.symm, hyS.1, hxS.1, ?_, h.1, h.2⟩
      simpa [S] using hSyx

theorem exists_two_monotone_height_arcs_of_ncard_intersections_eq_two
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space)
    (hgeneric : IsNondegenerateDirection r u)
    (hcard : (tangentGreatCircleIntersections r u).ncard = 2) :
    ∃ tmax tmin : ℝ,
      tmax ≠ tmin ∧ tmax ∈ Ico (0 : ℝ) period ∧ tmin ∈ Ico (0 : ℝ) period ∧
        tangentGreatCircleIntersections r u = {tmax, tmin} ∧
          IsLocalMax (height r u) tmax ∧ IsLocalMin (height r u) tmin ∧
            ((tmin < tmax ∧
                StrictMonoOn (height r u) (Icc tmin tmax) ∧
                StrictAntiOn (height r u) (Icc tmax (tmin + period))) ∨
              (tmax < tmin ∧
                StrictAntiOn (height r u) (Icc tmax tmin) ∧
                StrictMonoOn (height r u) (Icc tmin (tmax + period)))) := by
  obtain ⟨tmax, tmin, hne, htmax, htmin, hset, hmax, hmin⟩ :=
    exists_height_max_min_of_ncard_intersections_eq_two hknot u hgeneric hcard
  let S := tangentGreatCircleIntersections r u
  have hsetS : S = {tmax, tmin} := by simpa [S] using hset
  have htmaxS : tmax ∈ S := by rw [hsetS]; simp
  have htminS : tmin ∈ S := by rw [hsetS]; simp
  have htmaxIcc : tmax ∈ tangentGreatCircleIntersectionsIcc r u :=
    ⟨⟨htmax.1, htmax.2.le⟩, htmaxS.2⟩
  have htminIcc : tmin ∈ tangentGreatCircleIntersectionsIcc r u :=
    ⟨⟨htmin.1, htmin.2.le⟩, htminS.2⟩
  have hmaxDeriv : deriv (directionalUnitTangent r u) tmax < 0 := by
    rw [(hasDerivAt_directionalUnitTangent hknot u tmax).deriv]
    exact inner_deriv_unitTangent_neg_of_isLocalMax_height
      hknot u hgeneric htmaxIcc hmax
  have hminDeriv : 0 < deriv (directionalUnitTangent r u) tmin := by
    rw [(hasDerivAt_directionalUnitTangent hknot u tmin).deriv]
    exact inner_deriv_unitTangent_pos_of_isLocalMin_height
      hknot u hgeneric htminIcc hmin
  have hnoBetween : ∀ {a b : ℝ}, a ∈ S → b ∈ S → a < b → S = {a, b} →
      ∀ z ∈ Ioo a b, directionalUnitTangent r u z ≠ 0 := by
    intro a b haS hbS hab hpair z hz hz0
    have hzIco : z ∈ Ico (0 : ℝ) period :=
      ⟨haS.1.1.trans hz.1.le, hz.2.trans hbS.1.2⟩
    have hzS : z ∈ S := ⟨hzIco, hz0⟩
    rw [hpair] at hzS
    rcases hzS with rfl | hzS
    · exact (lt_irrefl _ hz.1)
    · have : z = b := by simpa using hzS
      subst z
      exact (lt_irrefl _ hz.2)
  have hnoWrap : ∀ {low high : ℝ}, low ∈ S → high ∈ S → low < high →
      S = {low, high} →
      ∀ z ∈ Ioo high (low + period), directionalUnitTangent r u z ≠ 0 := by
    intro low high hlowS hhighS hlowhigh hpair z hz hz0
    by_cases hzp : z < period
    · have hzIco : z ∈ Ico (0 : ℝ) period :=
        ⟨hhighS.1.1.trans hz.1.le, hzp⟩
      have hzS : z ∈ S := ⟨hzIco, hz0⟩
      rw [hpair] at hzS
      rcases hzS with rfl | hzS
      · exact (not_lt_of_ge hlowhigh.le) hz.1
      · have : z = high := by simpa using hzS
        subst z
        exact (lt_irrefl _ hz.1)
    · have hpz : period ≤ z := le_of_not_gt hzp
      let z' := z - period
      have hz'zero : directionalUnitTangent r u z' = 0 := by
        have hper := periodic_directionalUnitTangent hknot u z'
        have hz'eq : z' + period = z := by dsimp [z']; ring
        rw [hz'eq] at hper
        rw [← hper]
        exact hz0
      have hz'Ico : z' ∈ Ico (0 : ℝ) period := by
        constructor
        · dsimp [z']
          linarith
        · dsimp [z']
          linarith [hz.2, hlowS.1.2]
      have hz'S : z' ∈ S := ⟨hz'Ico, hz'zero⟩
      rw [hpair] at hz'S
      have hz'lt : z' < low := by
        dsimp [z']
        linarith [hz.2]
      rcases hz'S with hzEq | hzEq
      · have : z' = low := by simpa using hzEq
        have hcontra : low < low := this ▸ hz'lt
        exact (lt_irrefl _ hcontra)
      · have : z' = high := by simpa using hzEq
        have hcontra : high < low := this ▸ hz'lt
        exact (not_lt_of_ge hlowhigh.le) hcontra
  rcases lt_or_gt_of_ne hne with hmaxmin | hminmax
  · have hnoOrd := hnoBetween htmaxS htminS hmaxmin hsetS
    have hanti := strictAntiOn_height_Icc_of_directional_deriv_neg_of_no_zeros
      hknot u hmaxmin htmaxS.2 hmaxDeriv hnoOrd
    have hnoCyc := hnoWrap htmaxS htminS hmaxmin hsetS
    have hwrapLt : tmin < tmax + period := by linarith [htmin.2, htmax.1]
    have hmono := strictMonoOn_height_Icc_of_directional_deriv_pos_of_no_zeros
      hknot u hwrapLt htminS.2 hminDeriv hnoCyc
    exact ⟨tmax, tmin, hne, htmax, htmin, hset, hmax, hmin,
      Or.inr ⟨hmaxmin, hanti, hmono⟩⟩
  · have hsetSwap : S = {tmin, tmax} := by simpa [Set.pair_comm] using hsetS
    have hnoOrd := hnoBetween htminS htmaxS hminmax hsetSwap
    have hmono := strictMonoOn_height_Icc_of_directional_deriv_pos_of_no_zeros
      hknot u hminmax htminS.2 hminDeriv hnoOrd
    have hnoCyc := hnoWrap htminS htmaxS hminmax hsetSwap
    have hwrapLt : tmax < tmin + period := by linarith [htmax.2, htmin.1]
    have hanti := strictAntiOn_height_Icc_of_directional_deriv_neg_of_no_zeros
      hknot u hwrapLt htmaxS.2 hmaxDeriv hnoCyc
    exact ⟨tmax, tmin, hne, htmax, htmin, hset, hmax, hmin,
      Or.inl ⟨hminmax, hmono, hanti⟩⟩

theorem hasDerivAt_unitTangent {r : ℝ → Space} (hknot : IsSmoothKnot r) (t : ℝ) :
    HasDerivAt (unitTangent r)
      (‖velocity r t‖⁻¹ • acceleration r t +
        (-(inner ℝ (velocity r t) (acceleration r t) / ‖velocity r t‖) /
            ‖velocity r t‖ ^ 2) • velocity r t) t := by
  have hspeedNe : ‖velocity r t‖ ≠ 0 := norm_ne_zero_iff.mpr (hknot.regular t)
  have hinv := (hasDerivAt_speed hknot t).inv hspeedNe
  convert hinv.smul (hasDerivAt_velocity hknot t) using 1 <;> ext <;> rfl

theorem hasDerivAt_unitTangent_normal {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (t : ℝ) :
    HasDerivAt (unitTangent r)
      (‖velocity r t‖⁻¹ • normalAcceleration r t) t := by
  have hspeedNe : ‖velocity r t‖ ≠ 0 := norm_ne_zero_iff.mpr (hknot.regular t)
  convert hasDerivAt_unitTangent hknot t using 1
  ext i
  simp [normalAcceleration, smul_sub, smul_smul]
  field_simp [hspeedNe]
  ring

theorem inner_velocity_normalAcceleration {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (t : ℝ) :
    inner ℝ (velocity r t) (normalAcceleration r t) = 0 := by
  rw [normalAcceleration, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  field_simp [norm_ne_zero_iff.mpr (hknot.regular t)]
  ring

theorem cross_velocity_normalAcceleration {r : ℝ → Space} (t : ℝ) :
    toLp 2
        (crossProduct (ofLp (velocity r t)) (ofLp (acceleration r t))) =
      toLp 2
        (crossProduct (ofLp (velocity r t)) (ofLp (normalAcceleration r t))) := by
  simp [normalAcceleration]

theorem norm_cross_eq_speed_mul_norm_normalAcceleration {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (t : ℝ) :
    ‖toLp 2
        (crossProduct (ofLp (velocity r t)) (ofLp (acceleration r t)))‖ =
      ‖velocity r t‖ * ‖normalAcceleration r t‖ := by
  rw [cross_velocity_normalAcceleration]
  rw [InnerProductGeometry.norm_ofLp_crossProduct]
  have hangle :
      InnerProductGeometry.angle (velocity r t) (normalAcceleration r t) =
        Real.pi / 2 :=
    (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _).mp
      (inner_velocity_normalAcceleration hknot t)
  rw [hangle]
  simp

theorem norm_normalAcceleration {r : ℝ → Space} (hknot : IsSmoothKnot r) (t : ℝ) :
    ‖normalAcceleration r t‖ =
      ‖toLp 2
          (crossProduct (ofLp (velocity r t)) (ofLp (acceleration r t)))‖ /
        ‖velocity r t‖ := by
  rw [norm_cross_eq_speed_mul_norm_normalAcceleration hknot t]
  field_simp [norm_ne_zero_iff.mpr (hknot.regular t)]

theorem norm_deriv_unitTangent {r : ℝ → Space} (hknot : IsSmoothKnot r) (t : ℝ) :
    ‖deriv (unitTangent r) t‖ =
      ‖toLp 2
          (crossProduct (ofLp (velocity r t)) (ofLp (acceleration r t)))‖ /
        ‖velocity r t‖ ^ 2 := by
  rw [(hasDerivAt_unitTangent_normal hknot t).deriv, norm_smul,
    Real.norm_eq_abs, abs_inv, abs_norm, norm_normalAcceleration hknot t]
  field_simp [norm_ne_zero_iff.mpr (hknot.regular t)]

theorem norm_unitTangent {r : ℝ → Space} (hknot : IsSmoothKnot r) (t : ℝ) :
    ‖unitTangent r t‖ = 1 := by
  rw [unitTangent, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hknot.regular t))]

theorem speed_pos {r : ℝ → Space} (hknot : IsSmoothKnot r) (t : ℝ) :
    0 < ‖velocity r t‖ :=
  norm_pos_iff.mpr (hknot.regular t)

theorem curvature_mul_speed {r : ℝ → Space} (hknot : IsSmoothKnot r) (t : ℝ) :
    curvature r t * ‖velocity r t‖ =
      ‖toLp 2 (crossProduct (ofLp (velocity r t)) (ofLp (acceleration r t)))‖ /
        ‖velocity r t‖ ^ 2 := by
  unfold curvature
  field_simp [ne_of_gt (speed_pos hknot t)]

theorem totalCurvature_eq_integral_cross_div_speed_sq {r : ℝ → Space}
    (hknot : IsSmoothKnot r) :
    totalCurvature r =
      ∫ t in (0 : ℝ)..period,
        ‖toLp 2 (crossProduct (ofLp (velocity r t)) (ofLp (acceleration r t)))‖ /
          ‖velocity r t‖ ^ 2 := by
  rw [totalCurvature]
  simp_rw [curvature_mul_speed hknot]

theorem totalCurvature_eq_integral_norm_deriv_unitTangent {r : ℝ → Space}
    (hknot : IsSmoothKnot r) :
    totalCurvature r =
      ∫ t in (0 : ℝ)..period, ‖deriv (unitTangent r) t‖ := by
  rw [totalCurvature_eq_integral_cross_div_speed_sq hknot]
  simp_rw [norm_deriv_unitTangent hknot]

theorem integral_velocity_eq_zero {r : ℝ → Space} (hknot : IsSmoothKnot r) :
    (∫ t in (0 : ℝ)..period, velocity r t) = 0 := by
  change (∫ t in (0 : ℝ)..period, deriv r t) = 0
  rw [intervalIntegral.integral_deriv_of_contDiffOn_Icc
    (hknot.smooth.of_le (by simp)).contDiffOn (by simp [period, Real.pi_pos.le])]
  have hperiod : r period = r 0 := by simpa using hknot.periodic 0
  rw [hperiod]
  simp

theorem speed_smul_unitTangent {r : ℝ → Space} (hknot : IsSmoothKnot r) (t : ℝ) :
    ‖velocity r t‖ • unitTangent r t = velocity r t := by
  simp [unitTangent, norm_ne_zero_iff.mpr (hknot.regular t), smul_smul]

theorem integral_speed_smul_unitTangent_eq_zero {r : ℝ → Space}
    (hknot : IsSmoothKnot r) :
    (∫ t in (0 : ℝ)..period, ‖velocity r t‖ • unitTangent r t) = 0 := by
  simp_rw [speed_smul_unitTangent hknot]
  exact integral_velocity_eq_zero hknot

theorem zero_mem_closedConvexHull_range_unitTangent {r : ℝ → Space}
    (hknot : IsSmoothKnot r) :
    (0 : Space) ∈ closedConvexHull ℝ (range (unitTangent r)) := by
  by_contra hzero
  obtain ⟨f, u, hfu, hsep⟩ := geometric_hahn_banach_point_closed
    (convex_closedConvexHull (𝕜 := ℝ)) isClosed_closedConvexHull hzero
  have hu : 0 < u := by simpa using hfu
  have hpos : ∀ t : ℝ, 0 < f (‖velocity r t‖ • unitTangent r t) := by
    intro t
    rw [map_smul, smul_eq_mul]
    exact mul_pos (speed_pos hknot t) (hu.trans (hsep _ (subset_closedConvexHull ⟨t, rfl⟩)))
  have hcont : Continuous (fun t => f (‖velocity r t‖ • unitTangent r t)) := by
    exact f.continuous.comp
      ((contDiff_velocity hknot).continuous.norm.smul (contDiff_unitTangent hknot).continuous)
  have hint : IntervalIntegrable (fun t => f (‖velocity r t‖ • unitTangent r t))
      MeasureTheory.volume (0 : ℝ) period :=
    hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 period
  have hpositive : 0 < ∫ t in (0 : ℝ)..period,
      f (‖velocity r t‖ • unitTangent r t) :=
    intervalIntegral.intervalIntegral_pos_of_pos hint hpos (by simp [period, Real.pi_pos])
  have hzeroInt : (∫ t in (0 : ℝ)..period,
      f (‖velocity r t‖ • unitTangent r t)) = 0 := by
    have hvecInt : IntervalIntegrable
        (fun t => ‖velocity r t‖ • unitTangent r t)
        MeasureTheory.volume (0 : ℝ) period :=
      ((contDiff_velocity hknot).continuous.norm.smul
        (contDiff_unitTangent hknot).continuous).intervalIntegrable 0 period
    rw [f.intervalIntegral_comp_comm hvecInt]
    rw [integral_speed_smul_unitTangent_eq_zero hknot]
    simp
  linarith

theorem isUnknotted_of_nontrivial_curvature_gt {r : ℝ → Space}
    (hK : totalCurvature r ≤ 4 * Real.pi)
    (hgt : ¬ IsUnknotted r → 4 * Real.pi < totalCurvature r) :
    IsUnknotted r := by
  by_contra hnot
  exact (not_lt_of_ge hK) (hgt hnot)

theorem contDiff_standardCircle : ContDiff ℝ ⊤ standardCircle := by
  rw [contDiff_euclidean]
  intro i
  fin_cases i <;> simp [standardCircle] <;> fun_prop

def toLpContinuousLinearMap : (Fin 3 → ℝ) →L[ℝ] Space where
  toFun := toLp 2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

theorem hasDerivAt_standardCircle (t : ℝ) :
    HasDerivAt standardCircle (toLp 2 ![-Real.sin t, Real.cos t, 0]) t := by
  have hraw :
      HasDerivAt (fun t : ℝ => ![Real.cos t, Real.sin t, 0])
        ![-Real.sin t, Real.cos t, 0] t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa using Real.hasDerivAt_cos t
    · simpa using Real.hasDerivAt_sin t
    · simpa using hasDerivAt_const (x := t) (c := (0 : ℝ))
  convert toLpContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hraw using 1 <;>
    ext <;> rfl

theorem velocity_standardCircle (t : ℝ) :
    velocity standardCircle t = toLp 2 ![-Real.sin t, Real.cos t, 0] :=
  (hasDerivAt_standardCircle t).deriv

theorem hasDerivAt_velocity_standardCircle (t : ℝ) :
    HasDerivAt (velocity standardCircle)
      (toLp 2 ![-Real.cos t, -Real.sin t, 0]) t := by
  have hvelocity : velocity standardCircle =
      fun t : ℝ => toLp 2 ![-Real.sin t, Real.cos t, 0] :=
    funext velocity_standardCircle
  rw [hvelocity]
  have hraw :
      HasDerivAt (fun t : ℝ => ![-Real.sin t, Real.cos t, 0])
        ![-Real.cos t, -Real.sin t, 0] t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · convert (Real.hasDerivAt_sin t).neg using 1 <;> rfl
    · simpa using Real.hasDerivAt_cos t
    · simpa using hasDerivAt_const (x := t) (c := (0 : ℝ))
  convert toLpContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hraw using 1 <;>
    ext <;> rfl

theorem acceleration_standardCircle (t : ℝ) :
    acceleration standardCircle t = toLp 2 ![-Real.cos t, -Real.sin t, 0] :=
  (hasDerivAt_velocity_standardCircle t).deriv

theorem norm_velocity_standardCircle (t : ℝ) : ‖velocity standardCircle t‖ = 1 := by
  rw [velocity_standardCircle]
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_succ, Real.sin_sq_add_cos_sq]

theorem cross_velocity_acceleration_standardCircle (t : ℝ) :
    toLp 2
        (crossProduct (ofLp (velocity standardCircle t))
          (ofLp (acceleration standardCircle t))) =
      toLp 2 ![0, 0, 1] := by
  ext i
  fin_cases i
  · simp [velocity_standardCircle, acceleration_standardCircle, cross_apply]
  · simp [velocity_standardCircle, acceleration_standardCircle, cross_apply]
  · simp [velocity_standardCircle, acceleration_standardCircle, cross_apply]
    nlinarith [Real.sin_sq_add_cos_sq t]

theorem norm_cross_velocity_acceleration_standardCircle (t : ℝ) :
    ‖toLp 2
        (crossProduct (ofLp (velocity standardCircle t))
          (ofLp (acceleration standardCircle t)))‖ = 1 := by
  rw [cross_velocity_acceleration_standardCircle]
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_succ]

theorem curvature_standardCircle (t : ℝ) : curvature standardCircle t = 1 := by
  simp [curvature, norm_cross_velocity_acceleration_standardCircle,
    norm_velocity_standardCircle]

theorem totalCurvature_standardCircle : totalCurvature standardCircle = 2 * Real.pi := by
  simp [totalCurvature, curvature_standardCircle, norm_velocity_standardCircle, period]

theorem isSmoothKnot_standardCircle : IsSmoothKnot standardCircle where
  smooth := contDiff_standardCircle
  periodic := by
    intro t
    ext i
    fin_cases i <;> simp [standardCircle, period]
  injective_on_period := by
    intro x hx y hy hxy
    refine (injOn_circleMap_of_abs_sub_le' (c := 0) (R := 1) one_ne_zero ?_) hx hy ?_
    · simp [period]
    · apply Complex.ext
      · simpa [circleMap_zero_re, standardCircle] using
          congrArg (fun v : Space => v 0) hxy
      · simpa [circleMap_zero_im, standardCircle] using
          congrArg (fun v : Space => v 1) hxy
  regular := by
    intro t hzero
    have hsin : Real.sin t = 0 := by
      have := congrArg (fun v : Space => v 0) hzero
      simpa [velocity_standardCircle] using this
    have hcos : Real.cos t = 0 := by
      have := congrArg (fun v : Space => v 1) hzero
      simpa [velocity_standardCircle] using this
    nlinarith [Real.sin_sq_add_cos_sq t]

theorem isUnknotted_standardCircle : IsUnknotted standardCircle := by
  refine ⟨fun t _s => standardCircle t, ?_, ?_, ?_, ?_⟩
  · exact isSmoothKnot_standardCircle.smooth.comp contDiff_fst
  · intro t
    rfl
  · intro t
    rfl
  · intro _s _hs
    exact isSmoothKnot_standardCircle

end Submission.Helpers
