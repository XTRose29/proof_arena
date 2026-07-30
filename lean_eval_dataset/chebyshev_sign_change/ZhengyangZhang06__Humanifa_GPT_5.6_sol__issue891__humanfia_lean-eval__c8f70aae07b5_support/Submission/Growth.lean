import Submission.Analytic

open MeasureTheory Set
open scoped Topology

namespace Submission.Growth

open Submission.Helpers

noncomputable def mellinStripBound (P : StrongFEPair ℂ) (a b : ℝ) : ℝ :=
  ∫ t : ℝ in Set.Ioi 0,
    t ^ (a - 1) * ‖P.f t‖ + t ^ (b - 1) * ‖P.f t‖

lemma mellinStripBound_integrable (P : StrongFEPair ℂ) (a b : ℝ) :
    IntegrableOn
      (fun t : ℝ => t ^ (a - 1) * ‖P.f t‖ + t ^ (b - 1) * ‖P.f t‖)
      (Set.Ioi 0) := by
  have haConv := (P.hasMellin (a : ℂ)).1
  have hbConv := (P.hasMellin (b : ℂ)).1
  have ha : IntegrableOn (fun t : ℝ => t ^ (a - 1) * ‖P.f t‖) (Set.Ioi 0) := by
    rw [MellinConvergent] at haConv
    rw [mellin_convergent_iff_norm Set.Subset.rfl measurableSet_Ioi
      P.hf_int.aestronglyMeasurable] at haConv
    simpa using haConv
  have hb : IntegrableOn (fun t : ℝ => t ^ (b - 1) * ‖P.f t‖) (Set.Ioi 0) := by
    rw [MellinConvergent] at hbConv
    rw [mellin_convergent_iff_norm Set.Subset.rfl measurableSet_Ioi
      P.hf_int.aestronglyMeasurable] at hbConv
    simpa using hbConv
  exact ha.add hb

lemma mellinStripBound_nonneg (P : StrongFEPair ℂ) (a b : ℝ) :
    0 ≤ mellinStripBound P a b := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro t ht
  exact add_nonneg
    (mul_nonneg (Real.rpow_nonneg ht.le _) (norm_nonneg _))
    (mul_nonneg (Real.rpow_nonneg ht.le _) (norm_nonneg _))

lemma norm_mellin_le_mellinStripBound (P : StrongFEPair ℂ) {a b : ℝ} {s : ℂ}
    (ha : a ≤ s.re) (hb : s.re ≤ b) :
    ‖mellin P.f s‖ ≤ mellinStripBound P a b := by
  rw [mellin, mellinStripBound]
  apply norm_integral_le_of_norm_le (mellinStripBound_integrable P a b)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht (s - 1)]
  change t ^ (s.re - 1) * ‖P.f t‖ ≤ _
  by_cases ht1 : 1 ≤ t
  · calc
      t ^ (s.re - 1) * ‖P.f t‖ ≤ t ^ (b - 1) * ‖P.f t‖ := by
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le (x := t) (y := s.re - 1) (z := b - 1)
            ht1 (by linarith))
          (norm_nonneg _)
      _ ≤ t ^ (a - 1) * ‖P.f t‖ + t ^ (b - 1) * ‖P.f t‖ :=
        le_add_of_nonneg_left (mul_nonneg (Real.rpow_nonneg ht.le _) (norm_nonneg _))
  · have ht1' : t ≤ 1 := le_of_not_ge ht1
    calc
      t ^ (s.re - 1) * ‖P.f t‖ ≤ t ^ (a - 1) * ‖P.f t‖ := by
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_ge (x := t) (y := s.re - 1) (z := a - 1)
            ht ht1' (by linarith))
          (norm_nonneg _)
      _ ≤ t ^ (a - 1) * ‖P.f t‖ + t ^ (b - 1) * ‖P.f t‖ :=
        le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg ht.le _) (norm_nonneg _))

lemma norm_strongFEPair_Lambda_le_mellinStripBound (P : StrongFEPair ℂ)
    {a b : ℝ} {s : ℂ} (ha : a ≤ s.re) (hb : s.re ≤ b) :
    ‖P.Λ s‖ ≤ mellinStripBound P a b := by
  exact norm_mellin_le_mellinStripBound P ha hb

noncomputable def mellinDerivStripBound (P : StrongFEPair ℂ) (a b : ℝ) : ℝ :=
  ∫ t : ℝ in Set.Ioi 0,
    t ^ (a - 1) * |Real.log t| * ‖P.f t‖ +
      t ^ (b - 1) * |Real.log t| * ‖P.f t‖

private lemma mellinConvergent_log_smul (P : StrongFEPair ℂ) (x : ℝ) :
    MellinConvergent (fun t : ℝ => Real.log t • P.f t) (x : ℂ) := by
  exact (mellin_hasDerivAt_of_isBigO_rpow
    (a := x + 1) (b := x - 1) (s := (x : ℂ)) P.hf_int
    (P.hf_top' (-(x + 1))) (by simp)
    (P.hf_zero' (-(x - 1))) (by simp)).1

lemma mellinDerivStripBound_integrable (P : StrongFEPair ℂ) (a b : ℝ) :
    IntegrableOn
      (fun t : ℝ =>
        t ^ (a - 1) * |Real.log t| * ‖P.f t‖ +
          t ^ (b - 1) * |Real.log t| * ‖P.f t‖)
      (Set.Ioi 0) := by
  let g : ℝ → ℂ := fun t => Real.log t • P.f t
  have haConv : MellinConvergent g (a : ℂ) := mellinConvergent_log_smul P a
  have hbConv : MellinConvergent g (b : ℂ) := mellinConvergent_log_smul P b
  have haInt : IntegrableOn (fun t : ℝ => (t : ℂ) ^ ((a : ℂ) - 1) • g t) (Set.Ioi 0) :=
    haConv
  have hbInt : IntegrableOn (fun t : ℝ => (t : ℂ) ^ ((b : ℂ) - 1) • g t) (Set.Ioi 0) :=
    hbConv
  have hgLoc : LocallyIntegrableOn g (Set.Ioi 0) := by
    simpa only [g] using P.hf_int.continuousOn_smul isOpen_Ioi.isLocallyClosed
      (Real.continuousOn_log.mono (subset_compl_singleton_iff.mpr self_notMem_Ioi))
  have haNorm := (mellin_convergent_iff_norm Set.Subset.rfl measurableSet_Ioi
    hgLoc.aestronglyMeasurable).mp haInt
  have hbNorm := (mellin_convergent_iff_norm Set.Subset.rfl measurableSet_Ioi
    hgLoc.aestronglyMeasurable).mp hbInt
  have ha : IntegrableOn
      (fun t : ℝ => t ^ (a - 1) * |Real.log t| * ‖P.f t‖) (Set.Ioi 0) := by
    simpa only [Complex.ofReal_re, g, norm_smul, Real.norm_eq_abs, mul_assoc] using haNorm
  have hb : IntegrableOn
      (fun t : ℝ => t ^ (b - 1) * |Real.log t| * ‖P.f t‖) (Set.Ioi 0) := by
    simpa only [Complex.ofReal_re, g, norm_smul, Real.norm_eq_abs, mul_assoc] using hbNorm
  exact ha.add hb

lemma mellinDerivStripBound_nonneg (P : StrongFEPair ℂ) (a b : ℝ) :
    0 ≤ mellinDerivStripBound P a b := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro t ht
  exact add_nonneg
    (mul_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (abs_nonneg _)) (norm_nonneg _))
    (mul_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (abs_nonneg _)) (norm_nonneg _))

private lemma deriv_strongFEPair_Lambda_eq_mellin_log
    (P : StrongFEPair ℂ) (s : ℂ) :
    deriv P.Λ s = mellin (fun t : ℝ => Real.log t • P.f t) s := by
  have h := mellin_hasDerivAt_of_isBigO_rpow
    (a := s.re + 1) (b := s.re - 1) (s := s) P.hf_int
    (P.hf_top' (-(s.re + 1))) (by simp)
    (P.hf_zero' (-(s.re - 1))) (by simp)
  rw [P.Λ_eq]
  exact h.2.deriv

lemma norm_deriv_strongFEPair_Lambda_le_mellinDerivStripBound
    (P : StrongFEPair ℂ) {a b : ℝ} {s : ℂ} (ha : a ≤ s.re) (hb : s.re ≤ b) :
    ‖deriv P.Λ s‖ ≤ mellinDerivStripBound P a b := by
  rw [deriv_strongFEPair_Lambda_eq_mellin_log, mellin, mellinDerivStripBound]
  apply norm_integral_le_of_norm_le (mellinDerivStripBound_integrable P a b)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht (s - 1), norm_smul,
    Real.norm_eq_abs]
  change t ^ (s.re - 1) * (|Real.log t| * ‖P.f t‖) ≤ _
  have hfactor : 0 ≤ |Real.log t| * ‖P.f t‖ := mul_nonneg (abs_nonneg _) (norm_nonneg _)
  by_cases ht1 : 1 ≤ t
  · calc
      t ^ (s.re - 1) * (|Real.log t| * ‖P.f t‖) ≤
          t ^ (b - 1) * (|Real.log t| * ‖P.f t‖) := by
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le (x := t) (y := s.re - 1) (z := b - 1)
            ht1 (by linarith)) hfactor
      _ = t ^ (b - 1) * |Real.log t| * ‖P.f t‖ := by ring
      _ ≤ t ^ (a - 1) * |Real.log t| * ‖P.f t‖ +
          t ^ (b - 1) * |Real.log t| * ‖P.f t‖ := by
        exact le_add_of_nonneg_left
          (mul_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (abs_nonneg _)) (norm_nonneg _))
  · have ht1' : t ≤ 1 := le_of_not_ge ht1
    calc
      t ^ (s.re - 1) * (|Real.log t| * ‖P.f t‖) ≤
          t ^ (a - 1) * (|Real.log t| * ‖P.f t‖) := by
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_ge (x := t) (y := s.re - 1) (z := a - 1)
            ht ht1' (by linarith)) hfactor
      _ = t ^ (a - 1) * |Real.log t| * ‖P.f t‖ := by ring
      _ ≤ t ^ (a - 1) * |Real.log t| * ‖P.f t‖ +
          t ^ (b - 1) * |Real.log t| * ‖P.f t‖ := by
        exact le_add_of_nonneg_right
          (mul_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (abs_nonneg _)) (norm_nonneg _))

noncomputable def completedHurwitzZetaOddStripBound
    (u : UnitAddCircle) (a b : ℝ) : ℝ :=
  mellinStripBound (HurwitzZeta.hurwitzOddFEPair u) ((a + 1) / 2) ((b + 1) / 2) / 2

lemma completedHurwitzZetaOddStripBound_nonneg
    (u : UnitAddCircle) (a b : ℝ) :
    0 ≤ completedHurwitzZetaOddStripBound u a b := by
  exact div_nonneg (mellinStripBound_nonneg _ _ _) (by norm_num)

lemma norm_completedHurwitzZetaOdd_le_stripBound
    (u : UnitAddCircle) {a b : ℝ} {s : ℂ} (ha : a ≤ s.re) (hb : s.re ≤ b) :
    ‖HurwitzZeta.completedHurwitzZetaOdd u s‖ ≤
      completedHurwitzZetaOddStripBound u a b := by
  rw [HurwitzZeta.completedHurwitzZetaOdd, completedHurwitzZetaOddStripBound, norm_div]
  have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [hnorm2]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply norm_strongFEPair_Lambda_le_mellinStripBound
  · norm_num [Complex.div_re]
    linarith
  · norm_num [Complex.div_re]
    linarith

noncomputable def chiFourHurwitzStripBound (a b : ℝ) : ℝ :=
  ∑ j : ZMod 4, ‖chiFour j‖ *
    completedHurwitzZetaOddStripBound (ZMod.toAddCircle j) a b

lemma chiFourHurwitzStripBound_nonneg (a b : ℝ) :
    0 ≤ chiFourHurwitzStripBound a b := by
  apply Finset.sum_nonneg
  intro j _hj
  exact mul_nonneg (norm_nonneg _) (completedHurwitzZetaOddStripBound_nonneg _ _ _)

noncomputable def chiFourCompletedStripBound (a b : ℝ) : ℝ :=
  (4 : ℝ) ^ (-a) * chiFourHurwitzStripBound a b

lemma chiFourCompletedStripBound_nonneg (a b : ℝ) :
    0 ≤ chiFourCompletedStripBound a b :=
  mul_nonneg (Real.rpow_nonneg (by norm_num) _) (chiFourHurwitzStripBound_nonneg a b)

lemma norm_chiFour_completedLFunction_le_stripBound
    {a b : ℝ} {s : ℂ} (ha : a ≤ s.re) (hb : s.re ≤ b) :
    ‖DirichletCharacter.completedLFunction chiFour s‖ ≤
      chiFourCompletedStripBound a b := by
  rw [DirichletCharacter.completedLFunction,
    ZMod.completedLFunction_def_odd chiFour_odd.to_fun]
  have hpow : ‖(4 : ℂ) ^ (-s)‖ ≤ (4 : ℝ) ^ (-a) := by
    change ‖((4 : ℝ) : ℂ) ^ (-s)‖ ≤ (4 : ℝ) ^ (-a)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    change (4 : ℝ) ^ (-s.re) ≤ (4 : ℝ) ^ (-a)
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hsum :
      ‖∑ j : ZMod 4,
          chiFour j * HurwitzZeta.completedHurwitzZetaOdd (ZMod.toAddCircle j) s‖ ≤
        chiFourHurwitzStripBound a b := by
    calc
      ‖∑ j : ZMod 4,
          chiFour j * HurwitzZeta.completedHurwitzZetaOdd (ZMod.toAddCircle j) s‖ ≤
          ∑ j : ZMod 4,
            ‖chiFour j * HurwitzZeta.completedHurwitzZetaOdd (ZMod.toAddCircle j) s‖ := by
        simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte] using
          norm_sum_le (Finset.univ : Finset (ZMod 4))
            (fun j => chiFour j *
              HurwitzZeta.completedHurwitzZetaOdd (ZMod.toAddCircle j) s)
      _ ≤ chiFourHurwitzStripBound a b := by
        apply Finset.sum_le_sum
        intro j _hj
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          (norm_completedHurwitzZetaOdd_le_stripBound (ZMod.toAddCircle j) ha hb)
          (norm_nonneg _)
  rw [norm_mul, chiFourCompletedStripBound]
  exact (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (by norm_num) _))

noncomputable def chiFourJensenLower (H : ℝ) : ℝ :=
  2 - 2 * (H + 4)

noncomputable def chiFourJensenUpper (H : ℝ) : ℝ :=
  2 + 2 * (H + 4)

noncomputable def chiFourJensenNormBound (H : ℝ) : ℝ :=
  1 + chiFourCompletedStripBound (chiFourJensenLower H) (chiFourJensenUpper H)

lemma one_le_chiFourJensenNormBound (H : ℝ) :
    1 ≤ chiFourJensenNormBound H := by
  exact le_add_of_nonneg_right
    (chiFourCompletedStripBound_nonneg (chiFourJensenLower H) (chiFourJensenUpper H))

private lemma re_mem_jensen_strip {H : ℝ} {z : ℂ}
    (hz : z ∈ Metric.sphere (2 : ℂ) (2 * (H + 4))) :
    chiFourJensenLower H ≤ z.re ∧ z.re ≤ chiFourJensenUpper H := by
  have hnorm : ‖z - 2‖ = 2 * (H + 4) := by
    simpa [Complex.dist_eq] using Metric.mem_sphere.mp hz
  have hre : |z.re - 2| ≤ 2 * (H + 4) := by
    calc
      |z.re - 2| = |(z - 2).re| := by simp
      _ ≤ ‖z - 2‖ := Complex.abs_re_le_norm _
      _ = 2 * (H + 4) := hnorm
  rw [abs_sub_le_iff] at hre
  constructor <;> dsimp [chiFourJensenLower, chiFourJensenUpper] <;> linarith

lemma norm_chiFour_completedLFunction_le_jensenNormBound
    {H : ℝ} {z : ℂ} (hz : z ∈ Metric.sphere (2 : ℂ) (2 * (H + 4))) :
    ‖DirichletCharacter.completedLFunction chiFour z‖ ≤ chiFourJensenNormBound H := by
  have hre := re_mem_jensen_strip hz
  exact (norm_chiFour_completedLFunction_le_stripBound hre.1 hre.2).trans
    (le_add_of_nonneg_left (by norm_num))

lemma chiFourNontrivialZeroMultisetInRectangle_card_le_explicit_jensen
    (H : ℝ) (hH : 0 ≤ H) :
    ((Submission.Analytic.chiFourNontrivialZeroMultisetInRectangle H).card : ℝ) ≤
      Real.log
          (chiFourJensenNormBound H /
            ‖DirichletCharacter.completedLFunction chiFour (2 : ℂ)‖) /
        Real.log 2 := by
  apply Submission.Analytic.chiFourNontrivialZeroMultisetInRectangle_card_le_jensen
    H (chiFourJensenNormBound H) hH (one_le_chiFourJensenNormBound H)
  intro z hz
  have hnorm : ‖z - 2‖ = 2 * (H + 2) := by
    simpa [Complex.dist_eq] using Metric.mem_sphere.mp hz
  have hre : |z.re - 2| ≤ 2 * (H + 2) := by
    calc
      |z.re - 2| = |(z - 2).re| := by simp
      _ ≤ ‖z - 2‖ := Complex.abs_re_le_norm _
      _ = 2 * (H + 2) := hnorm
  rw [abs_sub_le_iff] at hre
  apply (norm_chiFour_completedLFunction_le_stripBound (a := chiFourJensenLower H)
    (b := chiFourJensenUpper H) (s := z) (by
      dsimp [chiFourJensenLower]
      linarith) (by
      dsimp [chiFourJensenUpper]
      linarith)).trans
  exact le_add_of_nonneg_left (by norm_num)

lemma exists_chiFour_explicit_jensen_zero_avoiding_height
    (H : ℝ) (hH : 0 ≤ H) :
    ∃ T ∈ Set.Ioo H (H + 1),
      0 <
        (3 *
            (Real.log
                (chiFourJensenNormBound H /
                  ‖DirichletCharacter.completedLFunction chiFour (2 : ℂ)‖) /
              Real.log 2) +
          6)⁻¹ ∧
      ∀ s : ℂ, s ∈ Submission.Analytic.chiFourNontrivialZeroSet →
        (3 *
              (Real.log
                  (chiFourJensenNormBound H /
                    ‖DirichletCharacter.completedLFunction chiFour (2 : ℂ)‖) /
                Real.log 2) +
            6)⁻¹ ≤ |s.im - T| ∧
          (3 *
                (Real.log
                    (chiFourJensenNormBound H /
                      ‖DirichletCharacter.completedLFunction chiFour (2 : ℂ)‖) /
                  Real.log 2) +
              6)⁻¹ ≤ |s.im + T| := by
  apply Submission.Analytic.exists_chiFour_jensen_zero_avoiding_height
    H (chiFourJensenNormBound H) hH (one_le_chiFourJensenNormBound H)
  intro z hz
  exact norm_chiFour_completedLFunction_le_jensenNormBound hz

noncomputable def chiFourCompletedDerivativeStripBound (a b : ℝ) : ℝ :=
  chiFourCompletedStripBound (a - 1) (b + 1)

lemma chiFourCompletedDerivativeStripBound_nonneg (a b : ℝ) :
    0 ≤ chiFourCompletedDerivativeStripBound a b :=
  chiFourCompletedStripBound_nonneg (a - 1) (b + 1)

lemma norm_deriv_chiFour_completedLFunction_le_stripBound
    {a b : ℝ} {s : ℂ} (ha : a ≤ s.re) (hb : s.re ≤ b) :
    ‖deriv (DirichletCharacter.completedLFunction chiFour) s‖ ≤
      chiFourCompletedDerivativeStripBound a b := by
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (f := DirichletCharacter.completedLFunction chiFour) (c := s) (R := 1)
    (C := chiFourCompletedDerivativeStripBound a b) (by norm_num)
    (DirichletCharacter.differentiable_completedLFunction chiFour_ne_one).diffContOnCl
    (fun z hz => by
      have hnorm : ‖z - s‖ = 1 := by
        simpa [Complex.dist_eq] using Metric.mem_sphere.mp hz
      have hre : |z.re - s.re| ≤ 1 := by
        calc
          |z.re - s.re| = |(z - s).re| := by simp
          _ ≤ ‖z - s‖ := Complex.abs_re_le_norm _
          _ = 1 := hnorm
      rw [abs_sub_le_iff] at hre
      apply norm_chiFour_completedLFunction_le_stripBound <;> linarith)
  simpa using h

noncomputable def chiFourJensenDerivBound (H : ℝ) : ℝ :=
  1 + chiFourCompletedDerivativeStripBound (chiFourJensenLower H) (chiFourJensenUpper H)

lemma one_le_chiFourJensenDerivBound (H : ℝ) :
    1 ≤ chiFourJensenDerivBound H := by
  exact le_add_of_nonneg_right
    (chiFourCompletedDerivativeStripBound_nonneg
      (chiFourJensenLower H) (chiFourJensenUpper H))

lemma norm_deriv_chiFour_completedLFunction_le_jensenDerivBound
    {H : ℝ} {z : ℂ} (hz : z ∈ Metric.sphere (2 : ℂ) (2 * (H + 4))) :
    ‖deriv (DirichletCharacter.completedLFunction chiFour) z‖ ≤
      chiFourJensenDerivBound H := by
  have hre := re_mem_jensen_strip hz
  exact (norm_deriv_chiFour_completedLFunction_le_stripBound hre.1 hre.2).trans
    (le_add_of_nonneg_left (by norm_num))

def chiFourHorizontalEdges (T : ℝ) : Set ℂ :=
  ((fun x : ℝ => (x : ℂ) + T * Complex.I) '' Set.Icc (-1 / 2 : ℝ) (3 / 2 : ℝ)) ∪
    ((fun x : ℝ => (x : ℂ) - T * Complex.I) '' Set.Icc (-1 / 2 : ℝ) (3 / 2 : ℝ))

lemma chiFourHorizontalEdges_isCompact (T : ℝ) :
    IsCompact (chiFourHorizontalEdges T) := by
  apply IsCompact.union
  · exact isCompact_Icc.image (by fun_prop)
  · exact isCompact_Icc.image (by fun_prop)

lemma chiFourHorizontalEdges_nonempty (T : ℝ) :
    (chiFourHorizontalEdges T).Nonempty := by
  refine ⟨(0 : ℂ) + T * Complex.I, Set.mem_union_left _ ?_⟩
  exact ⟨0, by norm_num, rfl⟩

lemma chiFour_LFunction_ne_zero_on_horizontalEdges
    {T : ℝ}
    (havoidPlus : ∀ s : ℂ, s ∈ Submission.Analytic.chiFourNontrivialZeroSet → s.im ≠ T)
    (havoidMinus : ∀ s : ℂ, s ∈ Submission.Analytic.chiFourNontrivialZeroSet → s.im ≠ -T) :
    ∀ s ∈ chiFourHorizontalEdges T,
      DirichletCharacter.LFunction chiFour s ≠ 0 := by
  intro s hs
  rcases hs with hs | hs
  · rcases hs with ⟨x, hx, rfl⟩
    rcases hx with ⟨hx0, hx1⟩
    by_cases hnonpos : x ≤ 0
    · apply Submission.Analytic.chiFour_LFunction_ne_zero_of_neg_one_lt_re_of_re_le_zero
      · simp
        linarith
      · simpa using hnonpos
    · by_cases hone : 1 ≤ x
      · apply chiFour_LFunction_ne_zero_of_one_le_re
        simpa using hone
      · intro hzero
        have hs : (x : ℂ) + T * Complex.I ∈
            Submission.Analytic.chiFourNontrivialZeroSet := by
          refine ⟨by simp; linarith, by simp; linarith, hzero⟩
        exact havoidPlus _ hs (by simp)
  · rcases hs with ⟨x, hx, rfl⟩
    rcases hx with ⟨hx0, hx1⟩
    by_cases hnonpos : x ≤ 0
    · apply Submission.Analytic.chiFour_LFunction_ne_zero_of_neg_one_lt_re_of_re_le_zero
      · simp
        linarith
      · simpa using hnonpos
    · by_cases hone : 1 ≤ x
      · apply chiFour_LFunction_ne_zero_of_one_le_re
        simpa using hone
      · intro hzero
        have hs : (x : ℂ) - T * Complex.I ∈
            Submission.Analytic.chiFourNontrivialZeroSet := by
          refine ⟨by simp; linarith, by simp; linarith, hzero⟩
        exact havoidMinus _ hs (by simp)

lemma exists_chiFourNegLogDerivative_horizontal_bound
    {T : ℝ}
    (havoidPlus : ∀ s : ℂ, s ∈ Submission.Analytic.chiFourNontrivialZeroSet → s.im ≠ T)
    (havoidMinus : ∀ s : ℂ, s ∈ Submission.Analytic.chiFourNontrivialZeroSet → s.im ≠ -T) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ s ∈ chiFourHorizontalEdges T,
        ‖Submission.Analytic.chiFourNegLogDerivative s‖ ≤ C := by
  have hnonzero := chiFour_LFunction_ne_zero_on_horizontalEdges havoidPlus havoidMinus
  have hcontinuous : ContinuousOn
      (fun s => ‖Submission.Analytic.chiFourNegLogDerivative s‖)
      (chiFourHorizontalEdges T) :=
    (Submission.Analytic.chiFourNegLogDerivative_continuousOn.mono hnonzero).norm
  obtain ⟨s, hs, hmax⟩ := (chiFourHorizontalEdges_isCompact T).exists_isMaxOn
    (chiFourHorizontalEdges_nonempty T) hcontinuous
  exact ⟨‖Submission.Analytic.chiFourNegLogDerivative s‖, norm_nonneg _, hmax⟩

lemma exists_chiFour_explicit_height_with_horizontal_logDerivative_bound
    (H : ℝ) (hH : 0 ≤ H) :
    ∃ T ∈ Set.Ioo H (H + 1), ∃ C : ℝ, 0 ≤ C ∧
      ∀ s ∈ chiFourHorizontalEdges T,
        ‖Submission.Analytic.chiFourNegLogDerivative s‖ ≤ C := by
  obtain ⟨T, hT, hmargin, hsep⟩ :=
    exists_chiFour_explicit_jensen_zero_avoiding_height H hH
  have hplus : ∀ s : ℂ, s ∈ Submission.Analytic.chiFourNontrivialZeroSet → s.im ≠ T := by
    intro s hs heq
    have h := (hsep s hs).1
    rw [heq, sub_self, abs_zero] at h
    linarith
  have hminus : ∀ s : ℂ, s ∈ Submission.Analytic.chiFourNontrivialZeroSet → s.im ≠ -T := by
    intro s hs heq
    have h := (hsep s hs).2
    rw [heq, neg_add_cancel, abs_zero] at h
    linarith
  obtain ⟨C, hC, hbound⟩ :=
    exists_chiFourNegLogDerivative_horizontal_bound hplus hminus
  exact ⟨T, hT, C, hC, hbound⟩

end Submission.Growth
