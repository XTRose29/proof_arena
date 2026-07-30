import Submission.Inside

open LeanEval.Geometry.PicksTheorem

namespace Submission.Exterior

/-- The complement of a closed ball in the real plane is preconnected. -/
theorem isPreconnected_compl_closedBall
    (R : ℝ) (hR : 0 ≤ R) :
    IsPreconnected
      ((Metric.closedBall (0 : ℝ × ℝ) R)ᶜ) := by
  let radial :
      ((ℝ × ℝ) × ℝ) → (ℝ × ℝ) :=
    fun p => p.2 • p.1
  have hrank :
      1 < Module.rank ℝ (ℝ × ℝ) := by
    simp [rank_prod]
    norm_num
  have hsphere :
      IsPreconnected
        (Metric.sphere (0 : ℝ × ℝ) 1) :=
    isPreconnected_sphere hrank 0 1
  have hradii :
      IsPreconnected (Set.Ioi R) :=
    (convex_Ioi R).isPreconnected
  have hdomain :
      IsPreconnected
        (Metric.sphere (0 : ℝ × ℝ) 1 ×ˢ
          Set.Ioi R) :=
    hsphere.prod hradii
  have hradial :
      Continuous radial := by
    fun_prop
  have himage :
      radial ''
          (Metric.sphere (0 : ℝ × ℝ) 1 ×ˢ
            Set.Ioi R) =
        (Metric.closedBall (0 : ℝ × ℝ) R)ᶜ := by
    ext x
    constructor
    · rintro ⟨⟨u, r⟩, ⟨hu, hr⟩, rfl⟩
      change u ∈ Metric.sphere (0 : ℝ × ℝ) 1 at hu
      change R < r at hr
      dsimp [radial]
      rw [Set.mem_compl_iff,
        Metric.mem_closedBall]
      have huNorm : ‖u‖ = 1 := by
        exact mem_sphere_zero_iff_norm.mp hu
      have hrPos : 0 < r :=
        hR.trans_lt hr
      rw [dist_zero_right, norm_smul,
        Real.norm_eq_abs, abs_of_pos hrPos, huNorm,
        mul_one]
      exact not_le.mpr hr
    · intro hx
      have hxNorm : R < ‖x‖ := by
        rw [Set.mem_compl_iff,
          Metric.mem_closedBall, dist_zero_right,
          not_le] at hx
        exact hx
      have hxNormPos : 0 < ‖x‖ :=
        hR.trans_lt hxNorm
      let u : ℝ × ℝ := ‖x‖⁻¹ • x
      refine
        ⟨(u, ‖x‖), ?_, ?_⟩
      · refine ⟨?_, hxNorm⟩
        rw [mem_sphere_zero_iff_norm,
          norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hxNormPos),
          inv_mul_cancel₀ hxNormPos.ne']
      · dsimp [radial, u]
        rw [smul_smul,
          mul_inv_cancel₀ hxNormPos.ne',
          one_smul]
  rw [← himage]
  exact hdomain.image radial hradial.continuousOn

/-- The complement of a closed ball in the real plane is unbounded. -/
theorem not_isBounded_compl_closedBall
    (R : ℝ) :
    ¬ Bornology.IsBounded
      ((Metric.closedBall (0 : ℝ × ℝ) R)ᶜ) := by
  intro hbounded
  obtain ⟨C, hC⟩ := hbounded.exists_norm_le
  let a : ℝ := max R (max C 0) + 1
  have haR : R < a := by
    dsimp [a]
    linarith [le_max_left R (max C 0)]
  have haC : C < a := by
    dsimp [a]
    linarith [le_max_left C 0,
      le_max_right R (max C 0)]
  have haPos : 0 < a := by
    dsimp [a]
    linarith [le_max_right C 0,
      le_max_right R (max C 0)]
  have haNorm :
      ‖((a, 0) : ℝ × ℝ)‖ = a := by
    simp [Prod.norm_def, Real.norm_eq_abs,
      abs_of_pos haPos, haPos.le]
  have haOutside :
      ((a, 0) : ℝ × ℝ) ∈
        (Metric.closedBall (0 : ℝ × ℝ) R)ᶜ := by
    rw [Set.mem_compl_iff,
      Metric.mem_closedBall, dist_zero_right,
      haNorm]
    exact not_le.mpr haR
  have haBound := hC (a, 0) haOutside
  rw [haNorm] at haBound
  exact (not_lt_of_ge haBound) haC

/-- For a bounded obstacle, all unbounded complement components coincide.
Equivalently, `Inside.unboundedOutside` is one connected component. -/
theorem unboundedOutside_eq_connectedComponentIn
    {S : Set (ℝ × ℝ)}
    (hS : Bornology.IsBounded S) :
    ∃ p : ℝ × ℝ,
      p ∈ Inside.unboundedOutside S ∧
        Inside.unboundedOutside S =
          connectedComponentIn Sᶜ p := by
  obtain ⟨R, hR, hSR⟩ :=
    hS.subset_ball_lt 0 0
  let O : Set (ℝ × ℝ) :=
    (Metric.closedBall (0 : ℝ × ℝ) R)ᶜ
  have hOpreconnected :
      IsPreconnected O :=
    isPreconnected_compl_closedBall R hR.le
  have hOunbounded :
      ¬ Bornology.IsBounded O :=
    not_isBounded_compl_closedBall R
  have hOnonempty : O.Nonempty := by
    by_contra hOempty
    rw [Set.not_nonempty_iff_eq_empty] at hOempty
    apply hOunbounded
    rw [hOempty]
    exact Bornology.isBounded_empty
  have hOScompl : O ⊆ Sᶜ := by
    intro x hxO hxS
    exact
      hxO
        (Metric.ball_subset_closedBall
          (hSR hxS))
  obtain ⟨p, hpO⟩ := hOnonempty
  have hpScompl : p ∈ Sᶜ :=
    hOScompl hpO
  have hOcomponent :
      O ⊆ connectedComponentIn Sᶜ p :=
    hOpreconnected.subset_connectedComponentIn
      hpO hOScompl
  have hpComponentUnbounded :
      ¬ Bornology.IsBounded
        (connectedComponentIn Sᶜ p) := by
    intro hbounded
    exact hOunbounded (hbounded.subset hOcomponent)
  have hpOutside :
      p ∈ Inside.unboundedOutside S :=
    ⟨hpScompl, hpComponentUnbounded⟩
  refine ⟨p, hpOutside, ?_⟩
  ext x
  constructor
  · intro hxOutside
    have hcomponentMeets :
        (connectedComponentIn Sᶜ x ∩ O).Nonempty := by
      by_contra hdisjoint
      rw [Set.not_nonempty_iff_eq_empty] at hdisjoint
      have hcomponentSubset :
          connectedComponentIn Sᶜ x ⊆
            Metric.closedBall (0 : ℝ × ℝ) R := by
        intro y hyComponent
        by_contra hyBall
        have hyO : y ∈ O :=
          hyBall
        have hyInter :
            y ∈ connectedComponentIn Sᶜ x ∩ O :=
          ⟨hyComponent, hyO⟩
        rw [hdisjoint] at hyInter
        exact hyInter
      exact
        hxOutside.2
          (Metric.isBounded_closedBall.subset
            hcomponentSubset)
    obtain ⟨y, hyComponent, hyO⟩ :=
      hcomponentMeets
    have hpComponentY :
        p ∈ connectedComponentIn Sᶜ y :=
      hOpreconnected.subset_connectedComponentIn
        hyO hOScompl hpO
    have hxy :
        connectedComponentIn Sᶜ x =
          connectedComponentIn Sᶜ y :=
      connectedComponentIn_eq hyComponent
    have hpComponentX :
        p ∈ connectedComponentIn Sᶜ x := by
      rw [hxy]
      exact hpComponentY
    have hxp :
        connectedComponentIn Sᶜ x =
          connectedComponentIn Sᶜ p :=
      connectedComponentIn_eq hpComponentX
    have hxSelf :
        x ∈ connectedComponentIn Sᶜ x :=
      mem_connectedComponentIn hxOutside.1
    rw [hxp] at hxSelf
    exact hxSelf
  · intro hxComponent
    have hxScompl : x ∈ Sᶜ :=
      connectedComponentIn_subset Sᶜ p hxComponent
    refine ⟨hxScompl, ?_⟩
    intro hxBounded
    apply hpComponentUnbounded
    rw [connectedComponentIn_eq hxComponent]
    exact hxBounded

/-- The exterior selected by unbounded complement components of a bounded
planar obstacle is preconnected. -/
theorem isPreconnected_unboundedOutside
    {S : Set (ℝ × ℝ)}
    (hS : Bornology.IsBounded S) :
    IsPreconnected (Inside.unboundedOutside S) := by
  obtain ⟨p, _, hp⟩ :=
    unboundedOutside_eq_connectedComponentIn hS
  rw [hp]
  exact isPreconnected_connectedComponentIn

end Submission.Exterior
