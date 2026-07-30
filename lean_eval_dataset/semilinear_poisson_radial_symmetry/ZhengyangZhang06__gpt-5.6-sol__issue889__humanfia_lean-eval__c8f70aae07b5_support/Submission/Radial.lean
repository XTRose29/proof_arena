import Submission.MovingPlanes

namespace Submission.Helpers

open LeanEval.Analysis.PDE Metric
open Filter
open scoped InnerProductSpace NNReal Topology

variable {n : ℕ}

/-- Once an initial interval of planes can be moved, openness of both the
admissible and inadmissible positions propagates the comparison through the
connected interval `(0, 1)`. -/
lemma reflectedDifference_nonneg_every_positive_plane
    {f : ℝ → ℝ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f)
    (hu_c2 : ContDiffOn ℝ 2 u (closedBall 0 1))
    (hu_solve : SolvesSemilinearPoisson f u)
    (hu_positive : ∀ x ∈ ball 0 1, 0 < u x)
    (e : EuclideanSpace ℝ (Fin n)) (he : ‖e‖ = 1)
    (μ : ℝ) (hμ : 0 < μ) (hμone : μ < 1) :
    IsGoodPlane u e μ := by
  have hgoodOpen :
      IsOpen (goodPlaneSet u e) :=
    isOpen_goodPlaneSet hf hu_c2 hu_solve hu_positive he
  have hbadOpen :
      IsOpen (badPlaneSet u e) :=
    isOpen_badPlaneSet he hu_c2 hu_solve hu_positive
  have hdisjoint :
      Disjoint (goodPlaneSet u e) (badPlaneSet u e) := by
    rw [Set.disjoint_left]
    rintro ν ⟨_, _, hgood⟩ ⟨_, _, x, hx, hxneg⟩
    exact (not_lt_of_ge (hgood x hx)) hxneg
  have hcover :
      Set.Ioo (0 : ℝ) 1 ⊆
        goodPlaneSet u e ∪ badPlaneSet u e := by
    intro ν hν
    by_cases hgood : IsGoodPlane u e ν
    · exact Or.inl ⟨hν.1, hν.2, hgood⟩
    · rw [IsGoodPlane] at hgood
      push Not at hgood
      obtain ⟨x, hx, hxneg⟩ := hgood
      exact Or.inr ⟨hν.1, hν.2, x, hx, hxneg⟩
  obtain ⟨μ₀, hμ₀, hμ₀one, hinitial⟩ :=
    exists_initial_reflection_interval hf hu_c2 hu_solve
      hu_positive he
  have hμ₀good : μ₀ ∈ goodPlaneSet u e :=
    ⟨hμ₀, hμ₀one, hinitial μ₀ le_rfl hμ₀one⟩
  have hmeet :
      (Set.Ioo (0 : ℝ) 1 ∩ goodPlaneSet u e).Nonempty :=
    ⟨μ₀, ⟨hμ₀, hμ₀one⟩, hμ₀good⟩
  have hall :
      Set.Ioo (0 : ℝ) 1 ⊆ goodPlaneSet u e :=
    isPreconnected_Ioo.subset_left_of_subset_union
      hgoodOpen hbadOpen hdisjoint hcover hmeet
  exact (hall ⟨hμ, hμone⟩).2.2

lemma norm_planeReflect_zero
    (e x : EuclideanSpace ℝ (Fin n)) (he : ‖e‖ = 1) :
    ‖planeReflect e 0 x‖ = ‖x‖ := by
  rw [planeReflect_eq_linearPlaneReflect_add e 0 x he]
  simp

lemma planeReflect_neg_zero
    (e x : EuclideanSpace ℝ (Fin n)) :
    planeReflect (-e) 0 x = planeReflect e 0 x := by
  simp only [planeReflect, inner_neg_right, sub_zero, smul_neg]
  module

/-- The positive-plane comparisons extend to the central plane by continuity.
The boundary case follows directly from the Dirichlet condition. -/
lemma reflectedDifference_nonneg_at_zero_of_inner_pos
    {f : ℝ → ℝ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu_c2 : ContDiffOn ℝ 2 u (closedBall 0 1))
    (hu_solve : SolvesSemilinearPoisson f u)
    (e : EuclideanSpace ℝ (Fin n)) (he : ‖e‖ = 1)
    (hplanes : ∀ μ : ℝ, 0 < μ → μ < 1 → IsGoodPlane u e μ)
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
    (hxinner : 0 < ⟪x, e⟫_ℝ) :
    0 ≤ reflectedDifference u e 0 x := by
  have hxnormle : ‖x‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hx
  by_cases hxinside : ‖x‖ < 1
  · have hRinside :
        planeReflect e 0 x ∈
          ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      simpa [Metric.mem_ball, dist_zero_right,
        norm_planeReflect_zero e x he] using hxinside
    have hmap :
        ContDiffAt ℝ 2 (fun ν : ℝ ↦ planeReflect e ν x) 0 := by
      unfold planeReflect
      fun_prop
    have huR :
        ContDiffAt ℝ 2
          (fun ν : ℝ ↦ u (planeReflect e ν x)) 0 :=
      (contDiffAt_of_contDiffOn_closedBall hu_c2 hRinside).comp 0 hmap
    have hcont :
        ContinuousAt
          (fun ν : ℝ ↦ reflectedDifference u e ν x) 0 := by
      simpa [reflectedDifference] using
        huR.continuousAt.sub continuousAt_const
    by_contra hnonneg
    have hxneg : reflectedDifference u e 0 x < 0 :=
      lt_of_not_ge hnonneg
    have hnegative :
        {ν : ℝ | reflectedDifference u e ν x < 0} ∈ 𝓝 0 :=
      hcont (Iio_mem_nhds hxneg)
    obtain ⟨δ, hδ, hδnegative⟩ :=
      Metric.mem_nhds_iff.mp hnegative
    let ν : ℝ :=
      min (δ / 2) (min (⟪x, e⟫_ℝ / 2) (1 / 2))
    have hν : 0 < ν := by
      dsimp [ν]
      apply lt_min
      · linarith
      · apply lt_min
        · linarith
        · norm_num
    have hνδ : ν < δ := by
      have hle : ν ≤ δ / 2 := min_le_left _ _
      linarith
    have hνinner : ν ≤ ⟪x, e⟫_ℝ := by
      have hle : ν ≤ ⟪x, e⟫_ℝ / 2 :=
        (min_le_right _ _).trans (min_le_left _ _)
      linarith
    have hνone : ν < 1 := by
      have hle : ν ≤ (1 / 2 : ℝ) :=
        (min_le_right _ _).trans (min_le_right _ _)
      linarith
    have hνball : ν ∈ Metric.ball (0 : ℝ) δ := by
      simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hν] using hνδ
    have hνneg := hδnegative hνball
    have hνnonneg :=
      hplanes ν hν hνone x ⟨hx, hνinner⟩
    exact (not_lt_of_ge hνnonneg) hνneg
  · have hxnorm : ‖x‖ = 1 :=
      le_antisymm hxnormle (le_of_not_gt hxinside)
    have hxsphere :
        x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using hxnorm
    have hRsphere :
        planeReflect e 0 x ∈
          sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      simpa [Metric.mem_sphere, dist_zero_right,
        norm_planeReflect_zero e x he] using hxnorm
    have hRzero := hu_solve.2 _ hRsphere
    have hxzero := hu_solve.2 _ hxsphere
    simp [reflectedDifference, hRzero, hxzero]

/-- Central reflection preserves `u` on the positive side of its defining
hyperplane. The reverse inequality comes from applying the comparison in the
opposite direction at the reflected point. -/
lemma central_plane_reflection_invariant_of_inner_pos
    {f : ℝ → ℝ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu_c2 : ContDiffOn ℝ 2 u (closedBall 0 1))
    (hu_solve : SolvesSemilinearPoisson f u)
    (hplanes :
      ∀ (e : EuclideanSpace ℝ (Fin n)), ‖e‖ = 1 →
        ∀ μ : ℝ, 0 < μ → μ < 1 → IsGoodPlane u e μ)
    (e : EuclideanSpace ℝ (Fin n)) (he : ‖e‖ = 1)
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
    (hxpos : 0 < ⟪x, e⟫_ℝ) :
    u (planeReflect e 0 x) = u x := by
  have hforward :=
    reflectedDifference_nonneg_at_zero_of_inner_pos
      hu_c2 hu_solve e he (hplanes e he) hx hxpos
  let y := planeReflect e 0 x
  have hynorm : ‖y‖ = ‖x‖ := by
    exact norm_planeReflect_zero e x he
  have hxnormle : ‖x‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hx
  have hy :
      y ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right, hynorm] using hxnormle
  have hnege : ‖-e‖ = 1 := by
    simpa using he
  have hyinner : 0 < ⟪y, -e⟫_ℝ := by
    have hreflect := real_inner_planeReflect e 0 x he
    dsimp [y]
    rw [inner_neg_right, hreflect]
    linarith
  have hback :=
    reflectedDifference_nonneg_at_zero_of_inner_pos
      hu_c2 hu_solve (-e) hnege (hplanes (-e) hnege) hy hyinner
  have hreflectBack : planeReflect (-e) 0 y = x := by
    rw [planeReflect_neg_zero e y]
    simpa [y] using planeReflect_involutive e 0 he x
  rw [reflectedDifference] at hforward hback
  rw [hreflectBack] at hback
  dsimp [y] at hback
  linarith

/-- Reflection in every hyperplane through the origin preserves `u`. -/
lemma central_plane_reflection_invariant
    {f : ℝ → ℝ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu_c2 : ContDiffOn ℝ 2 u (closedBall 0 1))
    (hu_solve : SolvesSemilinearPoisson f u)
    (hplanes :
      ∀ (e : EuclideanSpace ℝ (Fin n)), ‖e‖ = 1 →
        ∀ μ : ℝ, 0 < μ → μ < 1 → IsGoodPlane u e μ)
    (e : EuclideanSpace ℝ (Fin n)) (he : ‖e‖ = 1)
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    u (planeReflect e 0 x) = u x := by
  by_cases hxpos : 0 < ⟪x, e⟫_ℝ
  · exact central_plane_reflection_invariant_of_inner_pos
      hu_c2 hu_solve hplanes e he hx hxpos
  · by_cases hxzero : ⟪x, e⟫_ℝ = 0
    · rw [planeReflect_eq_self e 0 x hxzero]
    · have hxneg : ⟪x, e⟫_ℝ < 0 :=
        lt_of_le_of_ne (le_of_not_gt hxpos) hxzero
      have hnege : ‖-e‖ = 1 := by
        simpa using he
      have hxnegpos : 0 < ⟪x, -e⟫_ℝ := by
        rw [inner_neg_right]
        linarith
      have hneg :=
        central_plane_reflection_invariant_of_inner_pos
          hu_c2 hu_solve hplanes (-e) hnege hx hxnegpos
      rw [planeReflect_neg_zero e x] at hneg
      exact hneg

/-- Values of `u` agree at points of the closed ball having the same norm. -/
lemma value_eq_of_norm_eq
    {f : ℝ → ℝ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu_c2 : ContDiffOn ℝ 2 u (closedBall 0 1))
    (hu_solve : SolvesSemilinearPoisson f u)
    (hplanes :
      ∀ (e : EuclideanSpace ℝ (Fin n)), ‖e‖ = 1 →
        ∀ μ : ℝ, 0 < μ → μ < 1 → IsGoodPlane u e μ)
    {x y : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
    (hnorm : ‖x‖ = ‖y‖) :
    u x = u y := by
  by_cases hxy : x = y
  · exact congrArg u hxy
  · obtain ⟨e, he, hreflect⟩ :=
      exists_unit_planeReflect_zero_eq hxy hnorm
    have hinvariant :=
      central_plane_reflection_invariant hu_c2 hu_solve hplanes e he hx
    rw [hreflect] at hinvariant
    exact hinvariant.symm

lemma norm_smul_unit_of_nonneg
    (e : EuclideanSpace ℝ (Fin n)) (he : ‖e‖ = 1)
    {r : ℝ} (hr : 0 ≤ r) :
    ‖r • e‖ = r := by
  rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_nonneg hr]

lemma radial_ray_nonneg
    {f : ℝ → ℝ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu_solve : SolvesSemilinearPoisson f u)
    (hu_positive : ∀ x ∈ ball 0 1, 0 < u x)
    (e : EuclideanSpace ℝ (Fin n)) (he : ‖e‖ = 1)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ u (r • e) := by
  have hrnorm : ‖r • e‖ = r :=
    norm_smul_unit_of_nonneg e he hr.1
  by_cases hrone : r = 1
  · have hrsphere :
        r • e ∈ sphere
          (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      simpa [Metric.mem_sphere, dist_zero_right, hrnorm] using hrone
    have hrzero := hu_solve.2 _ hrsphere
    simp [hrzero]
  · have hrlt : r < 1 := lt_of_le_of_ne hr.2 hrone
    have hrball :
        r • e ∈ ball
          (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      simpa [Metric.mem_ball, dist_zero_right, hrnorm] using hrlt
    exact (hu_positive _ hrball).le

lemma radial_ray_strictAnti
    {f : ℝ → ℝ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f)
    (hu_c2 : ContDiffOn ℝ 2 u (closedBall 0 1))
    (hu_solve : SolvesSemilinearPoisson f u)
    (hu_positive : ∀ x ∈ ball 0 1, 0 < u x)
    (hplanes :
      ∀ (e : EuclideanSpace ℝ (Fin n)), ‖e‖ = 1 →
        ∀ μ : ℝ, 0 < μ → μ < 1 → IsGoodPlane u e μ)
    (e : EuclideanSpace ℝ (Fin n)) (he : ‖e‖ = 1)
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) (hab : a < b) :
    u (b • e) < u (a • e) := by
  have hanorm : ‖a • e‖ = a :=
    norm_smul_unit_of_nonneg e he ha.1
  have hbnorm : ‖b • e‖ = b :=
    norm_smul_unit_of_nonneg e he hb.1
  by_cases hbone : b = 1
  · have hbsphere :
        b • e ∈ sphere
          (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      simpa [Metric.mem_sphere, dist_zero_right, hbnorm] using hbone
    have halt : a < 1 := hab.trans_le hb.2
    have haball :
        a • e ∈ ball
          (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      simpa [Metric.mem_ball, dist_zero_right, hanorm] using halt
    have hapos := hu_positive _ haball
    rw [hu_solve.2 _ hbsphere]
    exact hapos
  · have hblt : b < 1 := lt_of_le_of_ne hb.2 hbone
    let μ : ℝ := (a + b) / 2
    have hμ : 0 < μ := by
      dsimp [μ]
      nlinarith [ha.1]
    have hμone : μ < 1 := by
      dsimp [μ]
      nlinarith
    have hμb : μ < b := by
      dsimp [μ]
      linarith
    have hbcap : b • e ∈ openCap e μ := by
      constructor
      · simpa [Metric.mem_ball, dist_zero_right, hbnorm] using hblt
      · change μ < ⟪b • e, e⟫_ℝ
        rw [real_inner_smul_left, real_inner_self_eq_norm_sq, he]
        norm_num
        exact hμb
    have hstrict :=
      reflectedDifference_pos_of_nonneg hf hu_c2 hu_solve
        hu_positive he hμ hμone (hplanes e he μ hμ hμone)
        (b • e) hbcap
    have hreflect : planeReflect e μ (b • e) = a • e := by
      dsimp [μ]
      rw [planeReflect, real_inner_smul_left,
        real_inner_self_eq_norm_sq, he]
      norm_num
      module
    rw [reflectedDifference, hreflect] at hstrict
    exact sub_pos.mp hstrict

/-- The completed moving-plane argument, packaged in the benchmark's radial
profile form. -/
lemma exists_strictAnti_radial_profile
    (hn : 0 < n) {f : ℝ → ℝ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_lipschitz : ∃ K : ℝ≥0, LipschitzWith K f)
    (hu_c2 : ContDiffOn ℝ 2 u (closedBall 0 1))
    (hu_solve : SolvesSemilinearPoisson f u)
    (hu_positive : ∀ x ∈ ball 0 1, 0 < u x) :
    ∃ v : ℝ → ℝ≥0,
      StrictAntiOn v (Set.Icc (0 : ℝ) 1) ∧
        ∀ x ∈ closedBall 0 1, u x = v ‖x‖ := by
  obtain ⟨K, hf⟩ := hf_lipschitz
  have hplanes :
      ∀ (e : EuclideanSpace ℝ (Fin n)), ‖e‖ = 1 →
        ∀ μ : ℝ, 0 < μ → μ < 1 → IsGoodPlane u e μ := by
    intro e he μ hμ hμone
    exact reflectedDifference_nonneg_every_positive_plane
      hf hu_c2 hu_solve hu_positive e he μ hμ hμone
  have hfinrank :
      0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    simpa using hn
  let i : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :=
    ⟨0, hfinrank⟩
  let e : EuclideanSpace ℝ (Fin n) :=
    (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i
  have he : ‖e‖ = 1 := by
    dsimp [e]
    exact OrthonormalBasis.norm_eq_one _ _
  let v : ℝ → ℝ≥0 := fun r ↦
    ⟨max 0 (u (r • e)), le_max_left _ _⟩
  refine ⟨v, ?_, ?_⟩
  · intro a ha b hb hab
    have hstrict :=
      radial_ray_strictAnti hf hu_c2 hu_solve hu_positive
        hplanes e he ha hb hab
    have ha_nonneg :=
      radial_ray_nonneg hu_solve hu_positive e he ha
    have hb_nonneg :=
      radial_ray_nonneg hu_solve hu_positive e he hb
    change max 0 (u (b • e)) < max 0 (u (a • e))
    rw [max_eq_right hb_nonneg, max_eq_right ha_nonneg]
    exact hstrict
  · intro x hx
    have hxnormle : ‖x‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hx
    have hr : ‖x‖ ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨norm_nonneg x, hxnormle⟩
    have hr_nonneg :=
      radial_ray_nonneg hu_solve hu_positive e he hr
    have hraynorm : ‖‖x‖ • e‖ = ‖x‖ :=
      norm_smul_unit_of_nonneg e he (norm_nonneg x)
    have hradial :=
      value_eq_of_norm_eq hu_c2 hu_solve hplanes hx hraynorm.symm
    change u x = max 0 (u (‖x‖ • e))
    rw [max_eq_right hr_nonneg]
    exact hradial

end Submission.Helpers
