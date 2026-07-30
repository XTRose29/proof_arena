import Submission.HolomorphicConvergence
import Submission.RiemannChain
import Submission.RiemannExtremal
import Submission.SchwarzStability

open Filter Function Metric Set
open scoped Topology

namespace Submission

noncomputable def ReachableNormalizedDiskEmbedding.phaseCorrectedInverse
    {E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (E : ReachableNormalizedDiskEmbedding E₀) (w : ℂ) : ℂ :=
  E.2.some.inverseMap (E.1.phaseFactor⁻¹ * w)

lemma ReachableNormalizedDiskEmbedding.phaseCorrectedInverse_mapsTo_unitBall
    {E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (E : ReachableNormalizedDiskEmbedding E₀) :
    MapsTo E.phaseCorrectedInverse (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
  apply E.2.some.inverseMap_mapsTo_unitBall.comp
  intro w hw
  rw [mem_ball_zero_iff, norm_mul, norm_inv, E.1.norm_phaseFactor, inv_one, one_mul]
  simpa [mem_ball_zero_iff] using hw

lemma ReachableNormalizedDiskEmbedding.phaseCorrectedInverse_differentiableOn
    {E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (E : ReachableNormalizedDiskEmbedding E₀) :
    DifferentiableOn ℂ E.phaseCorrectedInverse (ball (0 : ℂ) 1) := by
  apply E.2.some.inverseMap_differentiableOn.comp
  · fun_prop
  · intro w hw
    rw [mem_ball_zero_iff, norm_mul, norm_inv, E.1.norm_phaseFactor,
      inv_one, one_mul]
    simpa [mem_ball_zero_iff] using hw

@[simp]
lemma ReachableNormalizedDiskEmbedding.phaseCorrectedInverse_zero
    {E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (E : ReachableNormalizedDiskEmbedding E₀) :
    E.phaseCorrectedInverse 0 = 0 := by
  simp [phaseCorrectedInverse, E.2.some.inverseMap_zero]

lemma ReachableNormalizedDiskEmbedding.phaseCorrectedInverse_phaseNormalize
    {E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (E : ReachableNormalizedDiskEmbedding E₀) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) :
    E.phaseCorrectedInverse (E.1.phaseNormalize z) = E₀ z := by
  have hp : E.1.phaseFactor ≠ 0 := by
    rw [← norm_ne_zero_iff, E.1.norm_phaseFactor]
    norm_num
  rw [phaseCorrectedInverse, NormalizedDiskEmbedding.phaseNormalize,
    ← mul_assoc, inv_mul_cancel₀ hp, one_mul]
  exact E.2.some.inverseMap_apply hz

lemma tendstoLocallyUniformlyOn_phaseCorrectedInverse
    {E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    {E : ℕ → ReachableNormalizedDiskEmbedding E₀}
    (hE : Tendsto (fun j ↦ ‖deriv (E j).1.toFun 0‖) atTop (nhds 1)) :
    TendstoLocallyUniformlyOn
      (fun j ↦ (E j).phaseCorrectedInverse) E₀.toFun atTop
        (ball (0 : ℂ) 1) := by
  have hphase :=
    tendstoLocallyUniformlyOn_phaseNormalize_of_deriv_norm_tendsto_one
      (E := fun j ↦ (E j).1) hE
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball] at hphase ⊢
  intro K hKU hK
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · rw [tendstoUniformlyOn_iff]
    intro ε hε
    exact Eventually.of_forall fun j z hz ↦ hz.elim
  obtain ⟨z₀, hz₀, hz₀max⟩ :=
    hK.exists_isMaxOn hKne continuous_norm.continuousOn
  let r := ‖z₀‖
  let gap := 1 - r
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr1 : r < 1 := by
    simpa only [r, mem_ball_zero_iff] using hKU hz₀
  have hgap : 0 < gap := sub_pos.mpr hr1
  have hKr : ∀ z ∈ K, ‖z‖ ≤ r := by
    intro z hz
    exact hz₀max hz
  have hphaseK := hphase K hKU hK
  rw [tendstoUniformlyOn_iff] at hphaseK ⊢
  intro ε hε
  let δ := min (gap / 2) (ε * gap / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  filter_upwards [hphaseK δ hδ] with j hj
  intro z hz
  have hzNorm : ‖z‖ ≤ r := hKr z hz
  have hzBall : z ∈ ball (0 : ℂ) 1 := hKU hz
  have herror : dist ((E j).1.phaseNormalize z) z < δ := by
    simpa only [id_eq, dist_comm] using hj z hz
  have herrorGap : dist ((E j).1.phaseNormalize z) z < gap := by
    exact (herror.trans_le (min_le_left _ _)).trans (half_lt_self hgap)
  have hsmallBall : ball z gap ⊆ ball (0 : ℂ) 1 := by
    intro w hw
    rw [mem_ball, dist_zero_right]
    have hwz : ‖w - z‖ < gap := by
      simpa [dist_eq_norm] using hw
    calc
      ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
        simpa only [sub_add_cancel] using norm_add_le (w - z) z
      _ < gap + r := add_lt_add_of_lt_of_le hwz hzNorm
      _ = 1 := by simp [gap]
  have hmaps : MapsTo (E j).phaseCorrectedInverse (ball z gap)
      (closedBall ((E j).phaseCorrectedInverse z) 2) := by
    intro w hw
    have hAw := (E j).phaseCorrectedInverse_mapsTo_unitBall (hsmallBall hw)
    have hAz := (E j).phaseCorrectedInverse_mapsTo_unitBall hzBall
    rw [mem_closedBall]
    calc
      dist ((E j).phaseCorrectedInverse w)
          ((E j).phaseCorrectedInverse z) ≤
          ‖(E j).phaseCorrectedInverse w‖ +
            ‖(E j).phaseCorrectedInverse z‖ := dist_le_norm_add_norm _ _
      _ ≤ 2 := by
        rw [mem_ball_zero_iff] at hAw hAz
        linarith
  have hschwarz := Complex.dist_le_div_mul_dist_of_mapsTo_ball
    ((E j).phaseCorrectedInverse_differentiableOn.mono hsmallBall)
    hmaps herrorGap
  have hscaled : 2 / gap * δ ≤ ε := by
    calc
      2 / gap * δ ≤ 2 / gap * (ε * gap / 2) := by
        exact mul_le_mul_of_nonneg_left (min_le_right _ _)
          (div_nonneg (by norm_num) hgap.le)
      _ = ε := by field_simp
  rw [← (E j).phaseCorrectedInverse_phaseNormalize hzBall]
  exact hschwarz.trans_lt
    ((mul_lt_mul_of_pos_left herror (div_pos (by norm_num) hgap)).trans_le hscaled)

lemma exists_phaseCorrectedInverse_taylorCoeff_tendsto
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0) :
    ∃ E : ℕ → ReachableNormalizedDiskEmbedding E₀,
      TendstoLocallyUniformlyOn
          (fun j ↦ (E j).phaseCorrectedInverse) E₀.toFun atTop
            (ball (0 : ℂ) 1) ∧
        ∀ n : ℕ,
          Tendsto (fun j ↦ taylorCoeff (E j).phaseCorrectedInverse n) atTop
            (nhds (taylorCoeff E₀.toFun n)) := by
  rcases exists_reachableNormalizedDiskEmbeddings_exhausting_unitBall_tendsto_one E₀
      with ⟨E, hE, _⟩
  have hlocal := tendstoLocallyUniformlyOn_phaseCorrectedInverse hE
  refine ⟨E, hlocal, ?_⟩
  intro n
  exact tendsto_taylorCoeff_of_locallyUniformlyOn isOpen_ball
    (mem_ball_self zero_lt_one) hlocal
    (fun j ↦ (E j).phaseCorrectedInverse_differentiableOn) n

lemma ReachableNormalizedDiskEmbedding.phaseCorrectedInverse_deriv_ne_zero
    {E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (E : ReachableNormalizedDiskEmbedding E₀) :
    deriv E.phaseCorrectedInverse 0 ≠ 0 := by
  have hzero : (0 : ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
  have heq : EqOn
      (E.phaseCorrectedInverse ∘ E.1.phaseNormalize) E₀.toFun
      (ball (0 : ℂ) 1) := by
    intro z hz
    exact E.phaseCorrectedInverse_phaseNormalize hz
  have hderivEq := heq.deriv isOpen_ball hzero
  have hAAt : DifferentiableAt ℂ E.phaseCorrectedInverse 0 :=
    E.phaseCorrectedInverse_differentiableOn.differentiableAt
      (isOpen_ball.mem_nhds hzero)
  have hHAt : DifferentiableAt ℂ E.1.phaseNormalize 0 :=
    E.1.phaseNormalizedEmbedding.differentiableOn.differentiableAt
      (isOpen_ball.mem_nhds hzero)
  have hHzero : E.1.phaseNormalize 0 = 0 := by
    simp [NormalizedDiskEmbedding.phaseNormalize, E.1.map_base]
  have hAAt' : DifferentiableAt ℂ E.phaseCorrectedInverse
      (E.1.phaseNormalize 0) := by
    rw [hHzero]
    exact hAAt
  have hcomp : deriv (E.phaseCorrectedInverse ∘ E.1.phaseNormalize) 0 =
      deriv E.phaseCorrectedInverse 0 * deriv E.1.phaseNormalize 0 :=
    by
      simpa only [hHzero] using
        (hAAt'.hasDerivAt.comp 0 hHAt.hasDerivAt).deriv
  rw [hcomp] at hderivEq
  intro hzeroA
  rw [hzeroA, zero_mul] at hderivEq
  exact E₀.deriv_ne_zero hderivEq.symm

noncomputable def ReachableNormalizedDiskEmbedding.normalizedPhaseCorrectedInverse
    {E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (E : ReachableNormalizedDiskEmbedding E₀) (z : ℂ) : ℂ :=
  E.phaseCorrectedInverse z / deriv E.phaseCorrectedInverse 0

lemma taylorCoeff_div_const (f : ℂ → ℂ) (a : ℂ) (n : ℕ) :
    taylorCoeff (fun z ↦ f z / a) n = taylorCoeff f n / a := by
  rw [taylorCoeff, iteratedDeriv_div_const, taylorCoeff]
  ring

lemma ReachableNormalizedDiskEmbedding.taylorCoeff_normalizedPhaseCorrectedInverse
    {E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (E : ReachableNormalizedDiskEmbedding E₀) (n : ℕ) :
    taylorCoeff E.normalizedPhaseCorrectedInverse n =
      taylorCoeff E.phaseCorrectedInverse n /
        deriv E.phaseCorrectedInverse 0 := by
  exact taylorCoeff_div_const E.phaseCorrectedInverse
    (deriv E.phaseCorrectedInverse 0) n

@[simp]
lemma ReachableNormalizedDiskEmbedding.normalizedPhaseCorrectedInverse_zero
    {E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (E : ReachableNormalizedDiskEmbedding E₀) :
    E.normalizedPhaseCorrectedInverse 0 = 0 := by
  simp [normalizedPhaseCorrectedInverse]

lemma ReachableNormalizedDiskEmbedding.deriv_normalizedPhaseCorrectedInverse
    {E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (E : ReachableNormalizedDiskEmbedding E₀) :
    deriv E.normalizedPhaseCorrectedInverse 0 = 1 := by
  have hAAt : DifferentiableAt ℂ E.phaseCorrectedInverse 0 :=
    E.phaseCorrectedInverse_differentiableOn.differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self zero_lt_one))
  change deriv
    (fun z ↦ E.phaseCorrectedInverse z / deriv E.phaseCorrectedInverse 0) 0 = 1
  rw [(hAAt.hasDerivAt.div_const (deriv E.phaseCorrectedInverse 0)).deriv]
  exact div_self E.phaseCorrectedInverse_deriv_ne_zero

lemma exists_normalizedPhaseCorrectedInverse_taylorCoeff_tendsto
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0) :
    ∃ E : ℕ → ReachableNormalizedDiskEmbedding E₀,
      ∀ n : ℕ,
        Tendsto (fun j ↦ taylorCoeff (E j).normalizedPhaseCorrectedInverse n)
          atTop
          (nhds (taylorCoeff
            (fun z ↦ E₀ z / deriv E₀.toFun 0) n)) := by
  rcases exists_phaseCorrectedInverse_taylorCoeff_tendsto E₀ with
    ⟨E, _, hcoeff⟩
  refine ⟨E, ?_⟩
  have hderiv : Tendsto (fun j ↦ deriv (E j).phaseCorrectedInverse 0)
      atTop (nhds (deriv E₀.toFun 0)) := by
    simpa [taylorCoeff] using hcoeff 1
  intro n
  rw [taylorCoeff_div_const]
  simp_rw [
    ReachableNormalizedDiskEmbedding.taylorCoeff_normalizedPhaseCorrectedInverse]
  exact (hcoeff n).div hderiv E₀.deriv_ne_zero

end Submission
