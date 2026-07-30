import ChallengeDeps
import Submission.StrongMaximum

namespace Submission.Helpers

open LeanEval.Analysis.PDE Metric
open Filter
open scoped InnerProductSpace NNReal Topology

section CapGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The closed cap cut from the unit ball by the plane
`⟪x, e⟫ = μ`. -/
def closedCap (e : E) (μ : ℝ) : Set E :=
  closedBall 0 1 ∩ {x | μ ≤ ⟪x, e⟫_ℝ}

/-- The interior of a moving-plane cap. -/
def openCap (e : E) (μ : ℝ) : Set E :=
  ball 0 1 ∩ {x | μ < ⟪x, e⟫_ℝ}

def closedTruncatedCap (e : E) (a b : ℝ) : Set E :=
  closedBall 0 1 ∩ {x | a ≤ ⟪x, e⟫_ℝ} ∩
    {x | ⟪x, e⟫_ℝ ≤ b}

def openTruncatedCap (e : E) (a b : ℝ) : Set E :=
  ball 0 1 ∩ {x | a < ⟪x, e⟫_ℝ} ∩
    {x | ⟪x, e⟫_ℝ < b}

omit [FiniteDimensional ℝ E] in
lemma isOpen_openCap (e : E) (μ : ℝ) :
    IsOpen (openCap e μ) := by
  apply isOpen_ball.inter
  exact isOpen_lt continuous_const (by fun_prop)

omit [FiniteDimensional ℝ E] in
lemma convex_openCap (e : E) (μ : ℝ) :
    Convex ℝ (openCap e μ) := by
  rw [openCap]
  apply (convex_ball (0 : E) 1).inter
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  by_cases ha0 : a = 0
  · subst a
    have hb1 : b = 1 := by linarith
    subst b
    simpa using hy
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hxa := mul_lt_mul_of_pos_left hx ha_pos
    have hyb := mul_le_mul_of_nonneg_left hy.le hb
    calc
      μ = (a + b) * μ := by rw [hab, one_mul]
      _ = a * μ + b * μ := by ring
      _ < a * ⟪x, e⟫_ℝ + b * ⟪y, e⟫_ℝ :=
        add_lt_add_of_lt_of_le hxa hyb

omit [FiniteDimensional ℝ E] in
lemma isPreconnected_openCap (e : E) (μ : ℝ) :
    IsPreconnected (openCap e μ) :=
  (convex_openCap e μ).isPreconnected

omit [FiniteDimensional ℝ E] in
lemma isOpen_openTruncatedCap (e : E) (a b : ℝ) :
    IsOpen (openTruncatedCap e a b) := by
  apply (isOpen_ball.inter
    (isOpen_lt continuous_const (by fun_prop))).inter
  exact isOpen_lt (by fun_prop) continuous_const

omit [FiniteDimensional ℝ E] in
lemma openTruncatedCap_subset_closedTruncatedCap (e : E) (a b : ℝ) :
    openTruncatedCap e a b ⊆ closedTruncatedCap e a b := by
  intro x hx
  change
    (x ∈ ball (0 : E) 1 ∧ a < ⟪x, e⟫_ℝ) ∧
      ⟪x, e⟫_ℝ < b at hx
  change
    (x ∈ closedBall (0 : E) 1 ∧ a ≤ ⟪x, e⟫_ℝ) ∧
      ⟪x, e⟫_ℝ ≤ b
  exact
    ⟨⟨Metric.ball_subset_closedBall hx.1.1, hx.1.2.le⟩, hx.2.le⟩

lemma isCompact_closedTruncatedCap (e : E) (a b : ℝ) :
    IsCompact (closedTruncatedCap e a b) := by
  apply ((isCompact_closedBall (0 : E) 1).inter_right
    (isClosed_le continuous_const (by fun_prop))).inter_right
  exact isClosed_le (by fun_prop) continuous_const

omit [FiniteDimensional ℝ E] in
lemma closedTruncatedCap_slab (e : E) (a b : ℝ) :
    ∀ x ∈ closedTruncatedCap e a b,
      a ≤ ⟪x, e⟫_ℝ ∧ ⟪x, e⟫_ℝ ≤ b := by
  intro x hx
  exact ⟨hx.1.2, hx.2⟩

omit [FiniteDimensional ℝ E] in
lemma closedTruncatedCap_subset_closedCap (e : E) (a b : ℝ) :
    closedTruncatedCap e a b ⊆ closedCap e a := by
  intro x hx
  exact ⟨hx.1.1, hx.1.2⟩

omit [FiniteDimensional ℝ E] in
lemma openCap_subset_closedCap (e : E) (μ : ℝ) :
    openCap e μ ⊆ closedCap e μ := by
  intro x hx
  exact
    ⟨ball_subset_closedBall hx.1,
      show μ ≤ ⟪x, e⟫_ℝ from hx.2.le⟩

lemma isCompact_closedCap (e : E) (μ : ℝ) :
    IsCompact (closedCap e μ) := by
  apply (isCompact_closedBall (0 : E) 1).inter_right
  exact isClosed_le continuous_const (by fun_prop)

omit [FiniteDimensional ℝ E] in
lemma closedCap_inner_le_one {e x : E} {μ : ℝ}
    (he : ‖e‖ = 1) (hx : x ∈ closedCap e μ) :
    ⟪x, e⟫_ℝ ≤ 1 := by
  have hxnorm : ‖x‖ ≤ 1 := by
    simpa [closedCap, mem_closedBall, dist_zero_right] using hx.1
  calc
    ⟪x, e⟫_ℝ ≤ ‖x‖ * ‖e‖ := real_inner_le_norm x e
    _ ≤ 1 := by rw [he, mul_one]; exact hxnorm

omit [FiniteDimensional ℝ E] in
lemma closedCap_slab {e : E} {μ : ℝ} (he : ‖e‖ = 1) :
    ∀ x ∈ closedCap e μ, μ ≤ ⟪x, e⟫_ℝ ∧ ⟪x, e⟫_ℝ ≤ 1 := by
  intro x hx
  exact ⟨hx.2, closedCap_inner_le_one he hx⟩

omit [FiniteDimensional ℝ E] in
lemma planeReflect_mem_closedBall {e x : E} {μ : ℝ}
    (he : ‖e‖ = 1) (hμ : 0 ≤ μ) (hx : x ∈ closedCap e μ) :
    planeReflect e μ x ∈ closedBall (0 : E) 1 := by
  have hreflect := norm_planeReflect_le e μ x he hμ hx.2
  have hxnorm : ‖x‖ ≤ 1 := by
    simpa [closedCap, mem_closedBall, dist_zero_right] using hx.1
  simpa [mem_closedBall, dist_zero_right] using hreflect.trans hxnorm

omit [FiniteDimensional ℝ E] in
lemma planeReflect_mem_ball_of_mem_openCap {e x : E} {μ : ℝ}
    (he : ‖e‖ = 1) (hμ : 0 < μ) (hx : x ∈ openCap e μ) :
    planeReflect e μ x ∈ ball (0 : E) 1 := by
  have hreflect := norm_planeReflect_lt e μ x he hμ hx.2
  have hxnorm : ‖x‖ < 1 := by
    simpa [openCap, mem_ball, dist_zero_right] using hx.1
  simpa [mem_ball, dist_zero_right] using hreflect.trans hxnorm

omit [FiniteDimensional ℝ E] in
lemma planeReflect_mem_ball_of_mem_sphere {e x : E} {μ : ℝ}
    (he : ‖e‖ = 1) (hμ : 0 < μ)
    (hxsphere : x ∈ sphere (0 : E) 1)
    (hxinner : μ < ⟪x, e⟫_ℝ) :
    planeReflect e μ x ∈ ball (0 : E) 1 := by
  have hreflect := norm_planeReflect_lt e μ x he hμ hxinner
  have hxnorm : ‖x‖ = 1 := by
    simpa [mem_sphere, dist_zero_right] using hxsphere
  simpa [mem_ball, dist_zero_right, hxnorm] using hreflect

omit [FiniteDimensional ℝ E] in
lemma planeReflect_sub_planeReflect (e x : E) (μ ν : ℝ) :
    planeReflect e μ x - planeReflect e ν x =
      (2 * (μ - ν)) • e := by
  simp only [planeReflect]
  module

omit [FiniteDimensional ℝ E] in
lemma dist_planeReflect_planeReflect (e x : E) (μ ν : ℝ)
    (he : ‖e‖ = 1) :
    dist (planeReflect e μ x) (planeReflect e ν x) =
      2 * |μ - ν| := by
  rw [dist_eq_norm, planeReflect_sub_planeReflect, norm_smul, he,
    mul_one, Real.norm_eq_abs]
  rw [abs_mul]
  norm_num

omit [FiniteDimensional ℝ E] in
lemma exists_unit_planeReflect_zero_eq {x y : E}
    (hxy : x ≠ y) (hnorm : ‖x‖ = ‖y‖) :
    ∃ e : E, ‖e‖ = 1 ∧ planeReflect e 0 x = y := by
  let d : E := x - y
  have hd : d ≠ 0 := sub_ne_zero.mpr hxy
  have hdnorm : ‖d‖ ≠ 0 := norm_ne_zero_iff.mpr hd
  let e : E := (‖d‖⁻¹ : ℝ) • d
  have hdnorm_pos : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have he : ‖e‖ = 1 := by
    dsimp [e]
    rw [norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hdnorm_pos, inv_mul_cancel₀ hdnorm]
  have hinner :
      2 * ⟪x, d⟫_ℝ = ‖d‖ ^ 2 := by
    dsimp [d]
    rw [inner_sub_right, real_inner_self_eq_norm_sq,
      norm_sub_sq_real]
    rw [hnorm]
    ring
  refine ⟨e, he, ?_⟩
  rw [planeReflect]
  dsimp [e]
  rw [real_inner_smul_right]
  simp only [sub_zero, smul_smul]
  have hcoef :
      2 * (‖d‖⁻¹ * ⟪x, d⟫_ℝ) * ‖d‖⁻¹ = 1 := by
    calc
      2 * (‖d‖⁻¹ * ⟪x, d⟫_ℝ) * ‖d‖⁻¹ =
          (2 * ⟪x, d⟫_ℝ) * ‖d‖⁻¹ ^ 2 := by ring
      _ = ‖d‖ ^ 2 * ‖d‖⁻¹ ^ 2 := by rw [hinner]
      _ = 1 := by field_simp [hdnorm]
  rw [hcoef, one_smul]
  dsimp [d]
  abel

end CapGeometry

section SecantCoefficient

/-- The divided difference of `f`, with value zero on the diagonal. -/
noncomputable def secantCoeff (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  if a = b then 0 else (f a - f b) / (a - b)

lemma secantCoeff_mul_sub (f : ℝ → ℝ) (a b : ℝ) :
    secantCoeff f a b * (a - b) = f a - f b := by
  by_cases h : a = b
  · simp [secantCoeff, h]
  · rw [secantCoeff, if_neg h]
    exact div_mul_cancel₀ _ (sub_ne_zero.mpr h)

lemma abs_secantCoeff_le {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (a b : ℝ) :
    |secantCoeff f a b| ≤ K := by
  by_cases h : a = b
  · simp [secantCoeff, h]
  · have habpos : 0 < |a - b| := abs_pos.mpr (sub_ne_zero.mpr h)
    have hlip : |f a - f b| ≤ (K : ℝ) * |a - b| := by
      simpa [Real.dist_eq] using hf.dist_le_mul a b
    rw [secantCoeff, if_neg h, abs_div]
    exact (div_le_iff₀ habpos).2 (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hlip)

end SecantCoefficient

section ReflectedDifference

variable {n : ℕ}

/-- Difference between the value at the reflected point and the original
point. -/
noncomputable def reflectedDifference
    (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (e : EuclideanSpace ℝ (Fin n)) (μ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  u (planeReflect e μ x) - u x

def IsGoodPlane
    (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (e : EuclideanSpace ℝ (Fin n)) (μ : ℝ) : Prop :=
  ∀ x ∈ closedCap e μ, 0 ≤ reflectedDifference u e μ x

def goodPlaneSet
    (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (e : EuclideanSpace ℝ (Fin n)) : Set ℝ :=
  {μ | 0 < μ ∧ μ < 1 ∧ IsGoodPlane u e μ}

def badPlaneSet
    (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (e : EuclideanSpace ℝ (Fin n)) : Set ℝ :=
  {μ | 0 < μ ∧ μ < 1 ∧
    ∃ x ∈ closedCap e μ, reflectedDifference u e μ x < 0}

lemma reflectedDifference_eq_zero_on_plane
    (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (e : EuclideanSpace ℝ (Fin n)) (μ : ℝ)
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : ⟪x, e⟫_ℝ = μ) :
    reflectedDifference u e μ x = 0 := by
  rw [reflectedDifference, planeReflect_eq_self e μ x hx]
  ring

lemma reflectedDifference_pos_on_sphere
    {f : ℝ → ℝ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {e x : EuclideanSpace ℝ (Fin n)} {μ : ℝ}
    (he : ‖e‖ = 1) (hμ : 0 < μ)
    (hu_solve : SolvesSemilinearPoisson f u)
    (hu_positive : ∀ y ∈ ball 0 1, 0 < u y)
    (hxsphere : x ∈ sphere 0 1)
    (hxinner : μ < ⟪x, e⟫_ℝ) :
    0 < reflectedDifference u e μ x := by
  have hreflect :
      planeReflect e μ x ∈ ball
        (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    planeReflect_mem_ball_of_mem_sphere he hμ hxsphere hxinner
  rw [reflectedDifference, hu_solve.2 x hxsphere]
  simpa using hu_positive (planeReflect e μ x) hreflect

lemma contDiffAt_of_contDiffOn_closedBall
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu_c2 : ContDiffOn ℝ 2 u (closedBall 0 1))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ ball 0 1) :
    ContDiffAt ℝ 2 u x :=
  hu_c2.contDiffAt (closedBall_mem_nhds_of_mem hx)

lemma contDiffAt_reflectedDifference
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {e x : EuclideanSpace ℝ (Fin n)} {μ : ℝ}
    (he : ‖e‖ = 1) (hμ : 0 < μ)
    (hu_c2 : ContDiffOn ℝ 2 u (closedBall 0 1))
    (hx : x ∈ openCap e μ) :
    ContDiffAt ℝ 2 (reflectedDifference u e μ) x := by
  have hxball : x ∈ ball
      (0 : EuclideanSpace ℝ (Fin n)) 1 := hx.1
  have hRball :
      planeReflect e μ x ∈ ball
        (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    planeReflect_mem_ball_of_mem_openCap he hμ hx
  have hRx : ContDiffAt ℝ 2 (planeReflect e μ) x := by
    unfold planeReflect
    fun_prop
  have huRx : ContDiffAt ℝ 2 (u ∘ planeReflect e μ) x :=
    (contDiffAt_of_contDiffOn_closedBall hu_c2 hRball).comp x hRx
  have hux : ContDiffAt ℝ 2 u x :=
    contDiffAt_of_contDiffOn_closedBall hu_c2 hxball
  change ContDiffAt ℝ 2 ((u ∘ planeReflect e μ) - u) x
  exact huRx.sub hux

lemma continuousAt_reflectedDifference_parameter
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {e x : EuclideanSpace ℝ (Fin n)} {μ : ℝ}
    (he : ‖e‖ = 1) (hμ : 0 < μ)
    (hu_c2 : ContDiffOn ℝ 2 u (closedBall 0 1))
    (hx : x ∈ openCap e μ) :
    ContinuousAt (fun ν ↦ reflectedDifference u e ν x) μ := by
  have hRball :
      planeReflect e μ x ∈ ball
        (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    planeReflect_mem_ball_of_mem_openCap he hμ hx
  have hmap :
      ContDiffAt ℝ 2 (fun ν : ℝ ↦ planeReflect e ν x) μ := by
    unfold planeReflect
    fun_prop
  have huR :
      ContDiffAt ℝ 2 (fun ν : ℝ ↦ u (planeReflect e ν x)) μ :=
    (contDiffAt_of_contDiffOn_closedBall hu_c2 hRball).comp μ hmap
  simpa [reflectedDifference] using
    huR.continuousAt.sub continuousAt_const

lemma reflectedDifference_equation
    {f : ℝ → ℝ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {e x : EuclideanSpace ℝ (Fin n)} {μ : ℝ}
    (he : ‖e‖ = 1) (hμ : 0 < μ)
    (hu_c2 : ContDiffOn ℝ 2 u (closedBall 0 1))
    (hu_solve : SolvesSemilinearPoisson f u)
    (hx : x ∈ openCap e μ) :
    Laplacian.laplacian (reflectedDifference u e μ) x +
        secantCoeff f (u (planeReflect e μ x)) (u x) *
          reflectedDifference u e μ x = 0 := by
  have hxball : x ∈ ball
      (0 : EuclideanSpace ℝ (Fin n)) 1 := hx.1
  have hRball :
      planeReflect e μ x ∈ ball
        (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    planeReflect_mem_ball_of_mem_openCap he hμ hx
  have hRx : ContDiffAt ℝ 2 (planeReflect e μ) x := by
    unfold planeReflect
    fun_prop
  have huRx : ContDiffAt ℝ 2 (u ∘ planeReflect e μ) x :=
    (contDiffAt_of_contDiffOn_closedBall hu_c2 hRball).comp x hRx
  have hux : ContDiffAt ℝ 2 u x :=
    contDiffAt_of_contDiffOn_closedBall hu_c2 hxball
  have hlap :
      Laplacian.laplacian (reflectedDifference u e μ) x =
        Laplacian.laplacian u (planeReflect e μ x) -
          Laplacian.laplacian u x := by
    change
      Laplacian.laplacian ((u ∘ planeReflect e μ) - u) x =
        Laplacian.laplacian u (planeReflect e μ x) -
          Laplacian.laplacian u x
    rw [huRx.laplacian_sub hux,
      laplacian_comp_planeReflect e μ he u x]
  have hpdeR := hu_solve.1 (planeReflect e μ x) hRball
  have hpdex := hu_solve.1 x hxball
  have hsec := secantCoeff_mul_sub f
    (u (planeReflect e μ x)) (u x)
  rw [hlap, reflectedDifference]
  linarith

lemma abs_reflected_secantCoeff_le
    {f : ℝ → ℝ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f)
    (e : EuclideanSpace ℝ (Fin n)) (μ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    |secantCoeff f (u (planeReflect e μ x)) (u x)| ≤ K :=
  abs_secantCoeff_le hf _ _

lemma continuousOn_reflectedDifference
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {e : EuclideanSpace ℝ (Fin n)} {μ : ℝ}
    (he : ‖e‖ = 1) (hμ : 0 ≤ μ)
    (hu_c2 : ContDiffOn ℝ 2 u (closedBall 0 1)) :
    ContinuousOn (reflectedDifference u e μ) (closedCap e μ) := by
  have hRcont : Continuous (planeReflect e μ) := by
    unfold planeReflect
    fun_prop
  have hmaps :
      Set.MapsTo (planeReflect e μ) (closedCap e μ)
        (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    intro x hx
    exact planeReflect_mem_closedBall he hμ hx
  have huRcont :
      ContinuousOn (u ∘ planeReflect e μ) (closedCap e μ) :=
    hu_c2.continuousOn.comp hRcont.continuousOn hmaps
  exact huRcont.sub (hu_c2.continuousOn.mono fun _ hx ↦ hx.1)

lemma negative_reflectedDifference_mem_openCap
    {f : ℝ → ℝ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {e x : EuclideanSpace ℝ (Fin n)} {μ : ℝ}
    (he : ‖e‖ = 1) (hμ : 0 < μ)
    (hu_solve : SolvesSemilinearPoisson f u)
    (hu_positive : ∀ y ∈ ball 0 1, 0 < u y)
    (hx : x ∈ closedCap e μ)
    (hxneg : reflectedDifference u e μ x < 0) :
    x ∈ openCap e μ := by
  have hxinner : μ < ⟪x, e⟫_ℝ := by
    apply lt_of_le_of_ne hx.2
    intro heq
    have hzero := reflectedDifference_eq_zero_on_plane u e μ heq.symm
    linarith
  have hxnorm_le : ‖x‖ ≤ 1 := by
    simpa [closedCap, mem_closedBall, dist_zero_right] using hx.1
  have hxnorm : ‖x‖ < 1 := by
    apply lt_of_le_of_ne hxnorm_le
    intro heq
    have hxsphere :
        x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      simpa [mem_sphere, dist_zero_right] using heq
    have hpos := reflectedDifference_pos_on_sphere he hμ hu_solve
      hu_positive hxsphere hxinner
    linarith
  constructor
  · simpa [mem_ball, dist_zero_right] using hxnorm
  · exact hxinner

lemma negative_reflectedDifference_is_interior
    {f : ℝ → ℝ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {e x : EuclideanSpace ℝ (Fin n)} {μ : ℝ}
    (he : ‖e‖ = 1) (hμ : 0 < μ)
    (hu_solve : SolvesSemilinearPoisson f u)
    (hu_positive : ∀ y ∈ ball 0 1, 0 < u y)
    (hx : x ∈ closedCap e μ)
    (hxneg : reflectedDifference u e μ x < 0) :
    closedCap e μ ∈ 𝓝 x := by
  have hxopen : x ∈ openCap e μ :=
    negative_reflectedDifference_mem_openCap he hμ hu_solve
      hu_positive hx hxneg
  exact mem_of_superset ((isOpen_openCap e μ).mem_nhds hxopen)
    (openCap_subset_closedCap e μ)

lemma isOpen_badPlaneSet
    {f : ℝ → ℝ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {e : EuclideanSpace ℝ (Fin n)}
    (he : ‖e‖ = 1)
    (hu_c2 : ContDiffOn ℝ 2 u (closedBall 0 1))
    (hu_solve : SolvesSemilinearPoisson f u)
    (hu_positive : ∀ y ∈ ball 0 1, 0 < u y) :
    IsOpen (badPlaneSet u e) := by
  rw [isOpen_iff_mem_nhds]
  intro μ hμ
  rcases hμ with ⟨hμpos, hμone, x, hxcap, hxneg⟩
  have hxopen :
      x ∈ openCap e μ :=
    negative_reflectedDifference_mem_openCap he hμpos hu_solve
      hu_positive hxcap hxneg
  have hcont :=
    continuousAt_reflectedDifference_parameter he hμpos hu_c2 hxopen
  have hneg :
      {ν : ℝ | reflectedDifference u e ν x < 0} ∈ 𝓝 μ :=
    hcont (Iio_mem_nhds hxneg)
  filter_upwards
    [Ioo_mem_nhds hμpos hμone, Iio_mem_nhds hxopen.2, hneg]
    with ν hν hνinner hνneg
  exact
    ⟨hν.1, hν.2, x,
      ⟨hxcap.1, show ν ≤ ⟪x, e⟫_ℝ from hνinner.le⟩, hνneg⟩

lemma reflectedDifference_nonneg_of_narrow_cap
    {f : ℝ → ℝ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {K : ℝ≥0} {e : EuclideanSpace ℝ (Fin n)} {μ α : ℝ}
    (hf : LipschitzWith K f)
    (hu_c2 : ContDiffOn ℝ 2 u (closedBall 0 1))
    (hu_solve : SolvesSemilinearPoisson f u)
    (hu_positive : ∀ y ∈ ball 0 1, 0 < u y)
    (he : ‖e‖ = 1) (hμ : 0 < μ) (hα : 0 < α)
    (hK : (K : ℝ) < α ^ 2)
    (hwidth : α * (1 - μ) < Real.pi / 2) :
    ∀ x ∈ closedCap e μ, 0 ≤ reflectedDifference u e μ x := by
  let c : EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦
    secantCoeff f (u (planeReflect e μ x)) (u x)
  apply nonneg_of_narrow_slab
    (S := closedCap e μ) (w := reflectedDifference u e μ)
    (c := c) (e := e) (a := μ) (b := 1) (α := α)
  · exact isCompact_closedCap e μ
  · exact closedCap_slab he
  · exact he
  · exact hα
  · exact hwidth
  · exact continuousOn_reflectedDifference he hμ.le hu_c2
  · intro x hx hxneg
    exact contDiffAt_reflectedDifference he hμ hu_c2
      (negative_reflectedDifference_mem_openCap he hμ hu_solve
        hu_positive hx hxneg)
  · intro x hx hxneg
    exact negative_reflectedDifference_is_interior he hμ hu_solve
      hu_positive hx hxneg
  · intro x hx hxneg
    have habs : |c x| ≤ K := abs_reflected_secantCoeff_le hf e μ x
    have hcle : c x ≤ K := le_trans (le_abs_self _) habs
    exact lt_of_le_of_lt hcle hK
  · intro x hx hxneg
    exact (reflectedDifference_equation he hμ hu_c2 hu_solve
      (negative_reflectedDifference_mem_openCap he hμ hu_solve
        hu_positive hx hxneg)).le

lemma reflectedDifference_nonneg_on_truncated_cap
    {f : ℝ → ℝ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {K : ℝ≥0} {e : EuclideanSpace ℝ (Fin n)}
    {μ T α : ℝ}
    (hf : LipschitzWith K f)
    (hu_c2 : ContDiffOn ℝ 2 u (closedBall 0 1))
    (hu_solve : SolvesSemilinearPoisson f u)
    (hu_positive : ∀ y ∈ ball 0 1, 0 < u y)
    (he : ‖e‖ = 1) (hμ : 0 < μ) (hα : 0 < α)
    (hK : (K : ℝ) < α ^ 2)
    (hwidth : α * (T - μ) < Real.pi / 2)
    (hupper : ∀ x ∈ closedTruncatedCap e μ T,
      ⟪x, e⟫_ℝ = T → 0 ≤ reflectedDifference u e μ x) :
    ∀ x ∈ closedTruncatedCap e μ T,
      0 ≤ reflectedDifference u e μ x := by
  let c : EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦
    secantCoeff f (u (planeReflect e μ x)) (u x)
  apply nonneg_of_narrow_slab
    (S := closedTruncatedCap e μ T)
    (w := reflectedDifference u e μ) (c := c)
    (e := e) (a := μ) (b := T) (α := α)
  · exact isCompact_closedTruncatedCap e μ T
  · exact closedTruncatedCap_slab e μ T
  · exact he
  · exact hα
  · exact hwidth
  · exact (continuousOn_reflectedDifference he hμ.le hu_c2).mono
      (closedTruncatedCap_subset_closedCap e μ T)
  · intro x hx hxneg
    have hxcap : x ∈ closedCap e μ :=
      closedTruncatedCap_subset_closedCap e μ T hx
    exact contDiffAt_reflectedDifference he hμ hu_c2
      (negative_reflectedDifference_mem_openCap he hμ hu_solve
        hu_positive hxcap hxneg)
  · intro x hx hxneg
    have hxcap : x ∈ closedCap e μ :=
      closedTruncatedCap_subset_closedCap e μ T hx
    have hxopen :=
      negative_reflectedDifference_mem_openCap he hμ hu_solve
        hu_positive hxcap hxneg
    have hupperlt : ⟪x, e⟫_ℝ < T := by
      apply lt_of_le_of_ne hx.2
      intro heq
      have := hupper x hx heq
      linarith
    apply Filter.mem_of_superset
      ((isOpen_openTruncatedCap e μ T).mem_nhds
        ⟨⟨hxopen.1, hxopen.2⟩, hupperlt⟩)
    exact openTruncatedCap_subset_closedTruncatedCap e μ T
  · intro x hx hxneg
    have habs : |c x| ≤ K :=
      abs_reflected_secantCoeff_le hf e μ x
    exact (le_trans (le_abs_self _) habs).trans_lt hK
  · intro x hx hxneg
    have hxcap : x ∈ closedCap e μ :=
      closedTruncatedCap_subset_closedCap e μ T hx
    exact (reflectedDifference_equation he hμ hu_c2 hu_solve
      (negative_reflectedDifference_mem_openCap he hμ hu_solve
        hu_positive hxcap hxneg)).le

lemma unit_mem_closedCap
    {e : EuclideanSpace ℝ (Fin n)} {μ : ℝ}
    (he : ‖e‖ = 1) (hμ : μ ≤ 1) :
    e ∈ closedCap e μ := by
  constructor
  · simp [Metric.mem_closedBall, dist_zero_right, he]
  · change μ ≤ ⟪e, e⟫_ℝ
    rw [real_inner_self_eq_norm_sq, he]
    norm_num
    exact hμ

lemma unit_mem_closure_openCap
    {e : EuclideanSpace ℝ (Fin n)} {μ : ℝ}
    (he : ‖e‖ = 1) (hμ : μ < 1) :
    e ∈ closure (openCap e μ) := by
  apply Metric.mem_closure_iff.2
  intro ε hε
  let δ : ℝ := min (1 / 2) (min (ε / 2) ((1 - μ) / 2))
  let y : EuclideanSpace ℝ (Fin n) := (1 - δ) • e
  have hδ : 0 < δ := by
    apply lt_min
    · norm_num
    · apply lt_min <;> linarith
  have hδhalf_le : δ ≤ (1 / 2 : ℝ) := min_le_left _ _
  have hδε : δ ≤ ε / 2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hδgap : δ ≤ (1 - μ) / 2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hδhalf : δ < 1 := by
    linarith [hδhalf_le]
  have hscalar : 0 < 1 - δ := by linarith
  refine ⟨y, ?_, ?_⟩
  · constructor
    · have hynorm : ‖y‖ = 1 - δ := by
        dsimp [y]
        rw [norm_smul, he, mul_one, Real.norm_eq_abs,
          abs_of_pos hscalar]
      simpa [Metric.mem_ball, dist_zero_right, hynorm] using
        (sub_lt_self (1 : ℝ) hδ)
    · change μ < ⟪y, e⟫_ℝ
      dsimp [y]
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq, he]
      norm_num
      linarith
  · rw [dist_eq_norm]
    have hy : e - y = δ • e := by
      dsimp [y]
      module
    rw [hy, norm_smul, he, mul_one, Real.norm_eq_abs,
      abs_of_pos hδ]
    linarith

lemma reflectedDifference_pos_of_nonneg
    {f : ℝ → ℝ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {K : ℝ≥0} {e : EuclideanSpace ℝ (Fin n)} {μ : ℝ}
    (hf : LipschitzWith K f)
    (hu_c2 : ContDiffOn ℝ 2 u (closedBall 0 1))
    (hu_solve : SolvesSemilinearPoisson f u)
    (hu_positive : ∀ y ∈ ball 0 1, 0 < u y)
    (he : ‖e‖ = 1) (hμ : 0 < μ) (hμone : μ < 1)
    (hnonneg :
      ∀ x ∈ closedCap e μ, 0 ≤ reflectedDifference u e μ x) :
    ∀ x ∈ openCap e μ, 0 < reflectedDifference u e μ x := by
  let c : EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦
    secantCoeff f (u (planeReflect e μ x)) (u x)
  let α : ℝ := Real.sqrt ((K : ℝ) + 1)
  have hbase : 0 < (K : ℝ) + 1 := by
    nlinarith [K.coe_nonneg]
  have hα : 0 < α := Real.sqrt_pos.2 hbase
  have hαsq : α ^ 2 = (K : ℝ) + 1 :=
    Real.sq_sqrt hbase.le
  have hstrong :=
    strong_maximum_principle_of_bounded_coeff
      (Ω := openCap e μ) (w := reflectedDifference u e μ)
      (c := c) (e := e) (K := (K : ℝ)) (α := α)
      (isOpen_openCap e μ) (isPreconnected_openCap e μ) he
      K.coe_nonneg hα (by rw [hαsq]; linarith)
      ((continuousOn_reflectedDifference he hμ.le hu_c2).mono
        (openCap_subset_closedCap e μ))
      (fun x hx ↦ contDiffAt_reflectedDifference he hμ hu_c2 hx)
      (fun x hx ↦ hnonneg x (openCap_subset_closedCap e μ hx))
      (fun x hx ↦ abs_reflected_secantCoeff_le hf e μ x)
      (fun x hx ↦ reflectedDifference_equation he hμ hu_c2
        hu_solve hx)
  rcases hstrong with hzero | hpos
  · have heclosed : e ∈ closedCap e μ :=
      unit_mem_closedCap he hμone.le
    have hcontWithin :
        ContinuousWithinAt (reflectedDifference u e μ)
          (openCap e μ) e :=
      ((continuousOn_reflectedDifference he hμ.le hu_c2)
        e heclosed).mono (openCap_subset_closedCap e μ)
    have hwezero :
        reflectedDifference u e μ e = 0 :=
      hcontWithin.eq_const_of_mem_closure
        (unit_mem_closure_openCap he hμone) hzero
    have hesphere :
        e ∈ sphere
          (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      simp [he]
    have heinner : μ < ⟪e, e⟫_ℝ := by
      rw [real_inner_self_eq_norm_sq, he]
      norm_num
      exact hμone
    have hboundary :=
      reflectedDifference_pos_on_sphere he hμ hu_solve hu_positive
        hesphere heinner
    linarith
  · exact hpos

lemma goodPlaneSet_mem_nhds
    {f : ℝ → ℝ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {K : ℝ≥0} {e : EuclideanSpace ℝ (Fin n)} {μ : ℝ}
    (hf : LipschitzWith K f)
    (hu_c2 : ContDiffOn ℝ 2 u (closedBall 0 1))
    (hu_solve : SolvesSemilinearPoisson f u)
    (hu_positive : ∀ y ∈ ball 0 1, 0 < u y)
    (he : ‖e‖ = 1)
    (hμgood : μ ∈ goodPlaneSet u e) :
    goodPlaneSet u e ∈ 𝓝 μ := by
  rcases hμgood with ⟨hμ, hμone, hgood⟩
  let α : ℝ := Real.sqrt ((K : ℝ) + 1)
  have hbase : 0 < (K : ℝ) + 1 := by
    nlinarith [K.coe_nonneg]
  have hα : 0 < α := Real.sqrt_pos.2 hbase
  have hαsq : α ^ 2 = (K : ℝ) + 1 :=
    Real.sq_sqrt hbase.le
  let ρ : ℝ :=
    min ((1 - μ) / 4)
      (min (μ / 4) (Real.pi / (16 * α)))
  have hρ : 0 < ρ := by
    apply lt_min
    · linarith
    · apply lt_min
      · linarith
      · exact div_pos Real.pi_pos (mul_pos (by norm_num) hα)
  have hρone : ρ ≤ (1 - μ) / 4 := min_le_left _ _
  have hρμ : ρ ≤ μ / 4 :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hρpi : ρ ≤ Real.pi / (16 * α) :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  let T : ℝ := μ + ρ
  have hμT : μ < T := by dsimp [T]; linarith
  have hTone : T < 1 := by dsimp [T]; linarith
  have hstrict :
      ∀ x ∈ openCap e μ, 0 < reflectedDifference u e μ x :=
    reflectedDifference_pos_of_nonneg hf hu_c2 hu_solve
      hu_positive he hμ hμone hgood
  have hcorePositive :
      ∀ x ∈ closedCap e T, 0 < reflectedDifference u e μ x := by
    intro x hx
    have hxnorm : ‖x‖ ≤ 1 := by
      simpa [closedCap, Metric.mem_closedBall, dist_zero_right] using
        hx.1
    rcases hxnorm.lt_or_eq with hxinside | hxsphere
    · apply hstrict x
      constructor
      · simpa [Metric.mem_ball, dist_zero_right] using hxinside
      · exact hμT.trans_le hx.2
    · have hxs :
          x ∈ sphere
            (0 : EuclideanSpace ℝ (Fin n)) 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using hxsphere
      exact reflectedDifference_pos_on_sphere he hμ hu_solve
        hu_positive hxs (hμT.trans_le hx.2)
  have hcoreCont :
      ContinuousOn (reflectedDifference u e μ) (closedCap e T) := by
    apply (continuousOn_reflectedDifference he hμ.le hu_c2).mono
    intro x hx
    exact ⟨hx.1, hμT.le.trans hx.2⟩
  obtain ⟨m, hm, hmlower⟩ :=
    (isCompact_closedCap e T).exists_forall_le'
      hcoreCont hcorePositive
  have huUniform :
      UniformContinuousOn u
        (closedBall
          (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    (isCompact_closedBall
      (0 : EuclideanSpace ℝ (Fin n)) 1)
      |>.uniformContinuousOn_of_continuous hu_c2.continuousOn
  obtain ⟨ηu, hηu, hηucontrol⟩ :=
    Metric.uniformContinuousOn_iff.mp huUniform (m / 2)
      (by linarith)
  let η : ℝ := min (ρ / 2) (min (μ / 2) (ηu / 4))
  have hη : 0 < η := by
    apply lt_min
    · linarith
    · apply lt_min <;> linarith
  have hηρ : η ≤ ρ / 2 := min_le_left _ _
  have hημ : η ≤ μ / 2 :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hηu' : η ≤ ηu / 4 :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  apply Metric.mem_nhds_iff.2
  refine ⟨η, hη, ?_⟩
  intro ν hνball
  have hclose : |ν - μ| < η := by
    simpa [Metric.mem_ball, Real.dist_eq] using hνball
  have hclose' := abs_lt.mp hclose
  have hν : 0 < ν := by
    nlinarith
  have hνone : ν < 1 := by
    nlinarith
  have hνT : ν < T := by
    dsimp [T]
    nlinarith
  have hcoreν :
      ∀ x ∈ closedCap e T,
        m / 2 < reflectedDifference u e ν x := by
    intro x hx
    have hxν : x ∈ closedCap e ν :=
      ⟨hx.1, hνT.le.trans hx.2⟩
    have hxμ : x ∈ closedCap e μ :=
      ⟨hx.1, hμT.le.trans hx.2⟩
    have hRν :=
      planeReflect_mem_closedBall he hν.le hxν
    have hRμ :=
      planeReflect_mem_closedBall he hμ.le hxμ
    have hRdist :
        dist (planeReflect e ν x) (planeReflect e μ x) < ηu := by
      rw [dist_planeReflect_planeReflect e x ν μ he]
      nlinarith
    have huclose :=
      hηucontrol (planeReflect e ν x) hRν
        (planeReflect e μ x) hRμ hRdist
    have huabs :
        |u (planeReflect e ν x) -
          u (planeReflect e μ x)| < m / 2 := by
      simpa [Real.dist_eq] using huclose
    have hmμ := hmlower x hx
    dsimp [reflectedDifference] at hmμ ⊢
    linarith [neg_lt_of_abs_lt huabs]
  have hstripWidth :
      α * (T - ν) < Real.pi / 2 := by
    have hgap : T - ν < 3 * ρ / 2 := by
      dsimp [T]
      nlinarith
    have hscaled :
        α * (T - ν) < α * (3 * ρ / 2) :=
      mul_lt_mul_of_pos_left hgap hα
    have hpi :
        α * (3 * ρ / 2) ≤ 3 * Real.pi / 32 := by
      have hscaledρ :=
        mul_le_mul_of_nonneg_left hρpi hα.le
      field_simp [hα.ne'] at hscaledρ ⊢
      nlinarith
    nlinarith [Real.pi_pos]
  have hstrip :
      ∀ x ∈ closedTruncatedCap e ν T,
        0 ≤ reflectedDifference u e ν x := by
    apply reflectedDifference_nonneg_on_truncated_cap
      hf hu_c2 hu_solve hu_positive he hν hα
      (by rw [hαsq]; linarith) hstripWidth
    intro x hx hxT
    have hxcore : x ∈ closedCap e T :=
      ⟨hx.1.1, hxT.ge⟩
    exact (lt_trans (half_pos hm) (hcoreν x hxcore)).le
  refine ⟨hν, hνone, ?_⟩
  intro x hx
  by_cases hxT : ⟪x, e⟫_ℝ ≤ T
  · exact hstrip x ⟨⟨hx.1, hx.2⟩, hxT⟩
  · exact
      (lt_trans (half_pos hm)
        (hcoreν x ⟨hx.1, le_of_not_ge hxT⟩)).le

lemma isOpen_goodPlaneSet
    {f : ℝ → ℝ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {K : ℝ≥0} {e : EuclideanSpace ℝ (Fin n)}
    (hf : LipschitzWith K f)
    (hu_c2 : ContDiffOn ℝ 2 u (closedBall 0 1))
    (hu_solve : SolvesSemilinearPoisson f u)
    (hu_positive : ∀ y ∈ ball 0 1, 0 < u y)
    (he : ‖e‖ = 1) :
    IsOpen (goodPlaneSet u e) :=
  isOpen_iff_mem_nhds.2 fun _ hμ ↦
    goodPlaneSet_mem_nhds hf hu_c2 hu_solve hu_positive he hμ

lemma exists_initial_reflection_interval
    {f : ℝ → ℝ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f)
    (hu_c2 : ContDiffOn ℝ 2 u (closedBall 0 1))
    (hu_solve : SolvesSemilinearPoisson f u)
    (hu_positive : ∀ y ∈ ball 0 1, 0 < u y)
    {e : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1) :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ μ₀ < 1 ∧
      ∀ μ : ℝ, μ₀ ≤ μ → μ < 1 →
        ∀ x ∈ closedCap e μ, 0 ≤ reflectedDifference u e μ x := by
  let α : ℝ := Real.sqrt ((K : ℝ) + 1)
  let δ : ℝ := min (1 / 2 : ℝ) (Real.pi / (4 * α))
  let μ₀ : ℝ := 1 - δ
  have hbase : 0 < (K : ℝ) + 1 := by
    nlinarith [K.coe_nonneg]
  have hα : 0 < α := by
    exact Real.sqrt_pos.2 hbase
  have hαsq : α ^ 2 = (K : ℝ) + 1 := by
    exact Real.sq_sqrt hbase.le
  have hδpos : 0 < δ := by
    apply lt_min
    · norm_num
    · exact div_pos Real.pi_pos (mul_pos (by norm_num) hα)
  have hδhalf : δ ≤ (1 / 2 : ℝ) := min_le_left _ _
  have hδpi : δ ≤ Real.pi / (4 * α) := min_le_right _ _
  have hμ₀pos : 0 < μ₀ := by
    dsimp [μ₀]
    nlinarith
  have hμ₀one : μ₀ < 1 := by
    dsimp [μ₀]
    linarith
  refine ⟨μ₀, hμ₀pos, hμ₀one, ?_⟩
  intro μ hμ₀μ hμone
  have hμpos : 0 < μ := lt_of_lt_of_le hμ₀pos hμ₀μ
  have hgap : 1 - μ ≤ δ := by
    dsimp [μ₀] at hμ₀μ
    linarith
  have hwidth_le : α * (1 - μ) ≤ Real.pi / 4 := by
    calc
      α * (1 - μ) ≤ α * δ :=
        mul_le_mul_of_nonneg_left hgap hα.le
      _ ≤ α * (Real.pi / (4 * α)) :=
        mul_le_mul_of_nonneg_left hδpi hα.le
      _ = Real.pi / 4 := by
        field_simp [hα.ne']
  have hwidth : α * (1 - μ) < Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  apply reflectedDifference_nonneg_of_narrow_cap hf hu_c2 hu_solve
    hu_positive he hμpos hα
  · rw [hαsq]
    linarith
  · exact hwidth

end ReflectedDifference

end Submission.Helpers
