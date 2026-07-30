import Submission.BrouwerReduction
import Submission.Extension

namespace Submission.Helpers

open Set

/-- The canonical inclusion of the unit sphere into the closed unit ball. -/
def unitSphereClosedBallInclusion (d : ℕ) :
    C(Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) where
  toFun z := ⟨z, Metric.sphere_subset_closedBall z.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The no-retraction formulation for the boundary of the Euclidean unit
ball.  Keeping this as a proposition makes the remaining topological
obstruction explicit. -/
def NoUnitSphereRetraction (d : ℕ) : Prop :=
  ¬ ∃ ρ : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1),
    ∀ z, ρ (unitSphereClosedBallInclusion d z) = z

/-- The identity of the unit sphere is not homotopic to any constant map. -/
def UnitSphereIdentityEssential (d : ℕ) : Prop :=
  ∀ c : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
    ¬ ContinuousMap.Homotopic (ContinuousMap.id _)
      (ContinuousMap.const _ c)

/-- A self-map of the standard sphere is nullhomotopic when it is homotopic
to a constant map. -/
def SphereMapNullhomotopic (d : ℕ)
    (g : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1)) : Prop :=
  ∃ c, ContinuousMap.Homotopic g (ContinuousMap.const _ c)

/-- Restricting a closed-ball extension along radial segments supplies a
nullhomotopy of its boundary map. -/
theorem sphereMapNullhomotopic_of_closedBall_extension (d : ℕ)
    (g : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1))
    (G : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1))
    (hG : ∀ z, G (unitSphereClosedBallInclusion d z) = g z) :
    SphereMapNullhomotopic d g := by
  let center : Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin d)) 1 := ⟨0, by simp⟩
  refine ⟨G center, ⟨{
    toFun := fun q ↦ G ⟨(1 - (q.1 : ℝ)) •
        (q.2 : EuclideanSpace ℝ (Fin d)), by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
        Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr q.1.2.2),
        mem_sphere_zero_iff_norm.mp q.2.2]
      linarith [q.1.2.1]⟩
    continuous_toFun := by
      apply G.continuous.comp
      apply Continuous.subtype_mk
      exact (continuous_const.sub
        (continuous_subtype_val.comp continuous_fst)).smul
          (continuous_subtype_val.comp continuous_snd)
    map_zero_left := by
      intro z
      simpa [unitSphereClosedBallInclusion] using hG z
    map_one_left := by
      intro z
      change G ⟨(1 - (1 : ℝ)) •
        (z : EuclideanSpace ℝ (Fin d)), _⟩ = G center
      simp [center]
  }⟩⟩

/-- Essentiality of the identity map implies the usual no-retraction
statement.  Indeed, a retraction would contract the sphere by radially
contracting the ball and then applying the retraction. -/
theorem noUnitSphereRetraction_of_identityEssential (d : ℕ)
    (hessential : UnitSphereIdentityEssential d) :
    NoUnitSphereRetraction d := by
  rintro ⟨ρ, hρ⟩
  obtain ⟨c, hc⟩ := sphereMapNullhomotopic_of_closedBall_extension d
    (ContinuousMap.id _) ρ hρ
  exact hessential c hc

/-- The zero-sphere base case of sphere essentiality.  A homotopy from the
identity to a constant would give a path from a unit vector to its negative;
the unique coordinate of that path would have to pass through zero. -/
theorem unitSphereIdentityEssential_one : UnitSphereIdentityEssential 1 := by
  intro c hc
  obtain ⟨H⟩ := hc
  let z : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin 1)) 1 :=
    ⟨-(c : EuclideanSpace ℝ (Fin 1)), by
      rw [mem_sphere_zero_iff_norm, norm_neg]
      exact mem_sphere_zero_iff_norm.mp c.2⟩
  let p : Path z c := H.evalAt z
  let coordinate : unitInterval → ℝ :=
    fun t ↦ ((p t : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin 1)) 1) :
        EuclideanSpace ℝ (Fin 1)) 0
  have hcoordinate : Continuous coordinate := by
    exact (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous.comp
      (continuous_subtype_val.comp p.continuous)
  have hp0 : p 0 = z := p.source
  have hp1 : p 1 = c := p.target
  have hcoordinate0 : coordinate 0 =
      -((c : EuclideanSpace ℝ (Fin 1)) 0) := by
    dsimp [coordinate]
    rw [hp0]
    rfl
  have hcoordinate1 : coordinate 1 =
      (c : EuclideanSpace ℝ (Fin 1)) 0 := by
    dsimp [coordinate]
    rw [hp1]
  have hzero : 0 ∈ Set.range coordinate := by
    by_cases hc0 : 0 ≤ (c : EuclideanSpace ℝ (Fin 1)) 0
    · apply intermediate_value_univ (0 : unitInterval) 1 hcoordinate
      constructor
      · rw [hcoordinate0]
        exact neg_nonpos.mpr hc0
      · rw [hcoordinate1]
        exact hc0
    · have hc0' : (c : EuclideanSpace ℝ (Fin 1)) 0 ≤ 0 :=
        le_of_not_ge hc0
      apply intermediate_value_univ (1 : unitInterval) 0 hcoordinate
      constructor
      · rw [hcoordinate1]
        exact hc0'
      · rw [hcoordinate0]
        exact neg_nonneg.mpr hc0'
  obtain ⟨t, ht⟩ := hzero
  have hpzero : (p t : EuclideanSpace ℝ (Fin 1)) = 0 := by
    ext i
    fin_cases i
    simpa [coordinate] using ht
  have hnorm := mem_sphere_zero_iff_norm.mp (p t).2
  rw [hpzero, norm_zero] at hnorm
  norm_num at hnorm

/-- In particular, an interval cannot retract continuously onto its two
boundary points. -/
theorem noUnitSphereRetraction_one : NoUnitSphereRetraction 1 :=
  noUnitSphereRetraction_of_identityEssential 1
    unitSphereIdentityEssential_one

/-- Brouwer's fixed-point theorem rules out a retraction from every
finite-dimensional closed unit ball onto its boundary sphere. -/
theorem noUnitSphereRetraction_all (d : ℕ) : NoUnitSphereRetraction d := by
  rintro ⟨ρ, hρ⟩
  let K := Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1
  let ρambient : C(K, EuclideanSpace ℝ (Fin d)) :=
    { toFun := fun x ↦ (ρ x : EuclideanSpace ℝ (Fin d))
      continuous_toFun := continuous_subtype_val.comp ρ.continuous }
  obtain ⟨R, hR⟩ :=
    ρambient.exists_extension Metric.isClosed_closedBall.isClosedEmbedding_subtypeVal
  let g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun x ↦ -R x
  have hg_cont : Continuous g := R.continuous.neg
  have hg_maps : MapsTo g K K := by
    intro x hx
    have hRx : R x = ρ ⟨x, hx⟩ := by
      exact DFunLike.congr_fun hR ⟨x, hx⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖-R x‖ ≤ 1
    rw [norm_neg, hRx, mem_sphere_zero_iff_norm.mp (ρ ⟨x, hx⟩).2]
  obtain ⟨x, hx, hfix⟩ := brouwer_fixed_point_aux
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)
    (Metric.nonempty_closedBall.mpr (by norm_num)) g
    hg_cont.continuousOn hg_maps
  have hRx : R x = ρ ⟨x, hx⟩ :=
    DFunLike.congr_fun hR ⟨x, hx⟩
  have hxnorm : ‖x‖ = 1 := by
    rw [← hfix]
    change ‖-R x‖ = 1
    rw [norm_neg, hRx, mem_sphere_zero_iff_norm.mp (ρ ⟨x, hx⟩).2]
  let z : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 :=
    ⟨x, mem_sphere_zero_iff_norm.mpr hxnorm⟩
  have hρz : ρ (unitSphereClosedBallInclusion d z) = z := hρ z
  have hzBall : unitSphereClosedBallInclusion d z =
      (⟨x, hx⟩ : K) := by
    apply Subtype.ext
    rfl
  have hxneg : -x = x := by
    calc
      -x = -(ρ (unitSphereClosedBallInclusion d z) :
          EuclideanSpace ℝ (Fin d)) := by rw [hρz]
      _ = -R x := by
        rw [hzBall, ← hRx]
      _ = x := hfix
  have hxzero : x = 0 := by
    ext i
    have hi : -(x i) = x i := by
      simpa using congrArg
        (fun y : EuclideanSpace ℝ (Fin d) ↦ y i) hxneg
    have hi0 : x i = 0 := by
      linarith
    simpa using hi0
  rw [hxzero, norm_zero] at hxnorm
  norm_num at hxnorm

/-- A zero-free self-map of the closed ball which fixes its boundary would
normalize to a retraction onto the boundary. -/
theorem exists_zero_of_noUnitSphereRetraction (d : ℕ)
    (hno : NoUnitSphereRetraction d)
    (g : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1))
    (hfix : ∀ z, g (unitSphereClosedBallInclusion d z) =
      unitSphereClosedBallInclusion d z) :
    ∃ x, (g x : EuclideanSpace ℝ (Fin d)) = 0 := by
  by_contra hzero
  push Not at hzero
  apply hno
  let ρ : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    { toFun := fun x ↦
        ⟨NormedSpace.normalize (g x : EuclideanSpace ℝ (Fin d)), by
          rw [mem_sphere_zero_iff_norm]
          exact NormedSpace.norm_normalize (hzero x)⟩
      continuous_toFun := by
        have hg : Continuous
            (fun x ↦ (g x : EuclideanSpace ℝ (Fin d))) :=
          continuous_subtype_val.comp g.continuous
        apply Continuous.subtype_mk
        change Continuous (fun x ↦
          ‖(g x : EuclideanSpace ℝ (Fin d))‖⁻¹ •
            (g x : EuclideanSpace ℝ (Fin d)))
        exact (hg.norm.inv₀ fun x ↦
          norm_ne_zero_iff.mpr (hzero x)).smul hg }
  refine ⟨ρ, ?_⟩
  intro z
  apply Subtype.ext
  change NormedSpace.normalize
      (g (unitSphereClosedBallInclusion d z) :
        EuclideanSpace ℝ (Fin d)) = z
  rw [congrArg Subtype.val (hfix z)]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one
    (mem_sphere_zero_iff_norm.mp z.2)

/-- Extending both directions of a sphere embedding gives a self-map of the
standard closed ball which fixes every boundary point. -/
theorem exists_closedBall_selfMap_fixed_sphere (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) (hinj : Function.Injective r) :
    ∃ g : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1),
      ∀ z, g (unitSphereClosedBallInclusion d z) =
        unitSphereClosedBallInclusion d z := by
  obtain ⟨f, hf, hfle, _hflt⟩ :=
    exists_strict_unitBall_extension d hd r hcont hinj
  let rMap : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      EuclideanSpace ℝ (Fin d)) := ⟨r, hcont⟩
  have hinc : Topology.IsClosedEmbedding
      (unitSphereClosedBallInclusion d) :=
    (unitSphereClosedBallInclusion d).continuous.isClosedEmbedding (by
      intro z w hzw
      apply Subtype.ext
      exact congrArg
        (fun q : Metric.closedBall
          (0 : EuclideanSpace ℝ (Fin d)) 1 ↦
            (q : EuclideanSpace ℝ (Fin d))) hzw)
  obtain ⟨R, hR⟩ :=
    rMap.exists_extension hinc
  let g : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    { toFun := fun x ↦ ⟨f (R x), by
          rw [Metric.mem_closedBall, dist_zero_right]
          exact hfle (R x)⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact f.continuous.comp R.continuous }
  refine ⟨g, ?_⟩
  intro z
  apply Subtype.ext
  change f (R (unitSphereClosedBallInclusion d z)) = z
  have hRz : R (unitSphereClosedBallInclusion d z) = r z := by
    exact DFunLike.congr_fun hR z
  rw [hRz, hf z]

/-- Under the ball no-retraction obstruction, the strict inverse extension
has a zero away from the embedded sphere. -/
theorem exists_complement_zero_of_noUnitSphereRetraction
    (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) (hinj : Function.Injective r)
    (hno : NoUnitSphereRetraction d) :
    ∃ f : C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin d)),
      (∀ z, f (r z) = z) ∧
      (∀ x, ‖f x‖ ≤ 1) ∧
      (∀ x, x ∉ Set.range r → ‖f x‖ < 1) ∧
      ∃ y ∈ (Set.range r)ᶜ, f y = 0 := by
  obtain ⟨f, hf, hfle, hflt⟩ :=
    exists_strict_unitBall_extension d hd r hcont hinj
  let rMap : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      EuclideanSpace ℝ (Fin d)) := ⟨r, hcont⟩
  have hinc : Topology.IsClosedEmbedding
      (unitSphereClosedBallInclusion d) :=
    (unitSphereClosedBallInclusion d).continuous.isClosedEmbedding (by
      intro z w hzw
      apply Subtype.ext
      exact congrArg
        (fun q : Metric.closedBall
          (0 : EuclideanSpace ℝ (Fin d)) 1 ↦
            (q : EuclideanSpace ℝ (Fin d))) hzw)
  obtain ⟨R, hR⟩ :=
    rMap.exists_extension hinc
  let g : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    { toFun := fun x ↦ ⟨f (R x), by
          rw [Metric.mem_closedBall, dist_zero_right]
          exact hfle (R x)⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact f.continuous.comp R.continuous }
  have hfix : ∀ z, g (unitSphereClosedBallInclusion d z) =
      unitSphereClosedBallInclusion d z := by
    intro z
    apply Subtype.ext
    change f (R (unitSphereClosedBallInclusion d z)) = z
    have hRz : R (unitSphereClosedBallInclusion d z) = r z := by
      exact DFunLike.congr_fun hR z
    rw [hRz, hf z]
  obtain ⟨x, hx⟩ :=
    exists_zero_of_noUnitSphereRetraction d hno g hfix
  refine ⟨f, hf, hfle, hflt, R x, ?_, hx⟩
  rw [Set.mem_compl_iff]
  rintro ⟨z, hz⟩
  have hzero : (z : EuclideanSpace ℝ (Fin d)) = 0 := by
    rw [← hf z, hz]
    exact hx
  have hnorm := mem_sphere_zero_iff_norm.mp z.2
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

end Submission.Helpers
