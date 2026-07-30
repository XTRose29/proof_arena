import Submission.ZeroGrowth
import Submission.PrimeSeries

open Filter MeasureTheory Set

namespace Submission.Central

private lemma quarter_sin_even (m : ℕ) :
    Real.sin (2 * Real.pi * (1 / 4 : ℝ) * (2 * m : ℕ)) = 0 := by
  rw [show 2 * Real.pi * (1 / 4 : ℝ) * (2 * m : ℕ) = (m : ℝ) * Real.pi by
    push_cast
    ring]
  exact Real.sin_nat_mul_pi m

private lemma quarter_sin_odd (m : ℕ) :
    Real.sin (2 * Real.pi * (1 / 4 : ℝ) * (2 * m + 1 : ℕ)) = (-1 : ℝ) ^ m := by
  rw [show 2 * Real.pi * (1 / 4 : ℝ) * (2 * m + 1 : ℕ) =
      Real.pi / 2 + (m : ℝ) * Real.pi by
    push_cast
    ring]
  rw [Real.sin_add_nat_mul_pi, Real.sin_pi_div_two]
  ring

private noncomputable def quarterSinAmplitude (t : ℝ) (m : ℕ) : ℝ :=
  2 * (2 * m + 1) * Real.exp (-Real.pi * (2 * m + 1) ^ 2 * t)

private lemma quarterSinAmplitude_pos {t : ℝ} (m : ℕ) :
    0 < quarterSinAmplitude t m := by
  unfold quarterSinAmplitude
  positivity

private lemma quarterSinAmplitude_antitone {t : ℝ} (ht : 1 ≤ t) :
    Antitone (quarterSinAmplitude t) := by
  apply antitone_nat_of_succ_le
  intro m
  let a : ℝ := 2 * m + 1
  have ha : 1 ≤ a := by
    dsimp [a]
    norm_num
  let D : ℝ := 4 * Real.pi * (a + 1) * t
  have hD : 2 ≤ a * D := by
    have hpi : 3 ≤ Real.pi := Real.pi_gt_three.le
    calc
      2 ≤ 1 * 4 * 3 * 2 * 1 := by norm_num
      _ ≤ a * 4 * Real.pi * (a + 1) * t := by
        gcongr
        linarith
      _ = a * D := by dsimp [D]; ring
  have hcoeff : a + 2 ≤ a * Real.exp D := by
    calc
      a + 2 ≤ a * (D + 1) := by nlinarith
      _ ≤ a * Real.exp D :=
        mul_le_mul_of_nonneg_left (Real.add_one_le_exp D) (by positivity)
  unfold quarterSinAmplitude
  push_cast
  have hexp : D + (-Real.pi * (a + 2) ^ 2 * t) = -Real.pi * a ^ 2 * t := by
    dsimp [D]
    ring
  have htarget :
      2 * (a + 2) * Real.exp (-Real.pi * (a + 2) ^ 2 * t) ≤
        2 * a * Real.exp (-Real.pi * a ^ 2 * t) := by
    calc
      2 * (a + 2) * Real.exp (-Real.pi * (a + 2) ^ 2 * t) ≤
          2 * (a * Real.exp D) * Real.exp (-Real.pi * (a + 2) ^ 2 * t) := by
        gcongr
      _ = 2 * a * Real.exp (-Real.pi * a ^ 2 * t) := by
        rw [show 2 * (a * Real.exp D) * Real.exp (-Real.pi * (a + 2) ^ 2 * t) =
          2 * a * (Real.exp D * Real.exp (-Real.pi * (a + 2) ^ 2 * t)) by ring]
        rw [← Real.exp_add, hexp]
  dsimp [a] at htarget
  have hsucc : 2 * ((m : ℝ) + 1) + 1 = 2 * (m : ℝ) + 1 + 2 := by ring
  simpa only [hsucc] using htarget

private lemma sinKernel_quarter_pos {t : ℝ} (ht : 1 ≤ t) :
    0 < HurwitzZeta.sinKernel ((1 / 4 : ℝ) : UnitAddCircle) t := by
  let f : ℕ → ℝ := fun n =>
    2 * n * Real.sin (2 * Real.pi * (1 / 4 : ℝ) * n) *
      Real.exp (-Real.pi * n ^ 2 * t)
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hfull : HasSum f
      (HurwitzZeta.sinKernel ((1 / 4 : ℝ) : UnitAddCircle) t) := by
    simpa [f] using HurwitzZeta.hasSum_nat_sinKernel (1 / 4 : ℝ) htpos
  have heven : HasSum (fun m => f (2 * m)) 0 := by
    refine (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0).congr_fun ?_
    intro m
    symm
    dsimp [f]
    rw [quarter_sin_even]
    ring
  have hoddSummable : Summable (fun m => f (2 * m + 1)) :=
    hfull.summable.comp_injective fun m n h => by omega
  have hoddValue : ∑' m, f (2 * m + 1) =
      HurwitzZeta.sinKernel ((1 / 4 : ℝ) : UnitAddCircle) t := by
    have hsplit := heven.even_add_odd hoddSummable.hasSum
    have heq := hsplit.unique hfull
    simpa using heq
  have hodd : HasSum (fun m => (-1 : ℝ) ^ m * quarterSinAmplitude t m)
      (HurwitzZeta.sinKernel ((1 / 4 : ℝ) : UnitAddCircle) t) := by
    rw [← hoddValue]
    apply hoddSummable.hasSum.congr_fun
    intro m
    dsimp [f, quarterSinAmplitude]
    rw [quarter_sin_odd]
    push_cast
    ring
  have hlower := (quarterSinAmplitude_antitone ht).alternating_series_le_tendsto
    hodd.tendsto_sum_nat 1
  have hamp : quarterSinAmplitude t 1 < quarterSinAmplitude t 0 := by
    have hstrictExp :
        3 * Real.exp (-8 * Real.pi * t) < 1 := by
      have hx : 3 < Real.exp (8 * Real.pi * t) := by
        have hlinear : 25 ≤ 8 * Real.pi * t + 1 := by
          have hpi := Real.pi_gt_three
          nlinarith [mul_nonneg (sub_nonneg.mpr ht) Real.pi_pos.le]
        exact lt_of_lt_of_le (by norm_num) <|
          hlinear.trans (Real.add_one_le_exp (8 * Real.pi * t))
      rw [show -8 * Real.pi * t = -(8 * Real.pi * t) by ring, Real.exp_neg]
      simpa [div_eq_mul_inv] using (div_lt_one (Real.exp_pos (8 * Real.pi * t))).2 hx
    unfold quarterSinAmplitude
    norm_num
    rw [show -(Real.pi * 9 * t) = -(Real.pi * t) + (-8 * Real.pi * t) by ring,
      Real.exp_add]
    have hscaled := mul_lt_mul_of_pos_left hstrictExp
      (show 0 < 2 * Real.exp (-(Real.pi * t)) by positivity)
    nlinarith
  norm_num [Finset.sum_range_succ] at hlower
  linarith

private noncomputable def quarterOddPair (t : ℝ) (n : ℕ) : ℝ :=
  (n + 1 / 4 : ℝ) * Real.exp (-Real.pi * (n + 1 / 4 : ℝ) ^ 2 * t) -
    (n + 3 / 4 : ℝ) * Real.exp (-Real.pi * (n + 3 / 4 : ℝ) ^ 2 * t)

private lemma quarterOddPair_pos {t : ℝ} (ht : 1 ≤ t) (n : ℕ) :
    0 < quarterOddPair t n := by
  let a : ℝ := n + 1 / 4
  let D : ℝ := Real.pi * (a + 1 / 4) * t
  have ha : 1 / 4 ≤ a := by
    dsimp [a]
    have hn : 0 ≤ (n : ℝ) := by positivity
    linarith
  have hD : 3 / 2 < D := by
    dsimp [D]
    have hpi := Real.pi_gt_three
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) Real.pi_pos.le]
  have hbase : 0 ≤ 1 + D / 2 := by linarith
  have hexp3 : 3 < Real.exp D := by
    have hsquare : (1 + D / 2) ^ 2 ≤ Real.exp D := by
      calc
        (1 + D / 2) ^ 2 ≤ Real.exp (D / 2) ^ 2 := by
          gcongr
          simpa [add_comm] using Real.add_one_le_exp (D / 2)
        _ = Real.exp D := by
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring
    nlinarith
  have hcoeff : a + 1 / 2 < a * Real.exp D := by
    calc
      a + 1 / 2 ≤ 3 * a := by nlinarith
      _ < a * Real.exp D := by
        simpa [mul_comm] using
          mul_lt_mul_of_pos_left hexp3 (lt_of_lt_of_le (by norm_num) ha)
  have hexponent :
      D + (-Real.pi * (a + 1 / 2) ^ 2 * t) = -Real.pi * a ^ 2 * t := by
    dsimp [D]
    ring
  unfold quarterOddPair
  rw [show (n : ℝ) + 1 / 4 = a by rfl,
    show (n : ℝ) + 3 / 4 = a + 1 / 2 by dsimp [a]; ring]
  change 0 < a * Real.exp (-Real.pi * a ^ 2 * t) -
    (a + 1 / 2) * Real.exp (-Real.pi * (a + 1 / 2) ^ 2 * t)
  rw [sub_pos]
  calc
    (a + 1 / 2) * Real.exp (-Real.pi * (a + 1 / 2) ^ 2 * t) <
        (a * Real.exp D) * Real.exp (-Real.pi * (a + 1 / 2) ^ 2 * t) := by
      gcongr
    _ = a * Real.exp (-Real.pi * a ^ 2 * t) := by
      rw [mul_assoc, ← Real.exp_add, hexponent]

private lemma hasSum_quarterOddPair {t : ℝ} (ht : 0 < t) :
    HasSum (quarterOddPair t)
      (HurwitzZeta.oddKernel ((1 / 4 : ℝ) : UnitAddCircle) t) := by
  refine (HurwitzZeta.hasSum_int_oddKernel (1 / 4 : ℝ) ht).nat_add_neg_add_one.congr_fun ?_
  intro n
  unfold quarterOddPair
  push_cast
  ring_nf

private lemma oddKernel_quarter_pos_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    0 < HurwitzZeta.oddKernel ((1 / 4 : ℝ) : UnitAddCircle) t := by
  have hsum := hasSum_quarterOddPair (zero_lt_one.trans_le ht)
  have hfirst : 0 < quarterOddPair t 0 := quarterOddPair_pos ht 0
  have hnonneg : ∀ n, 0 ≤ quarterOddPair t n :=
    fun n => (quarterOddPair_pos ht n).le
  rw [← hsum.tsum_eq]
  exact hsum.summable.tsum_pos hnonneg 0 hfirst

private lemma oddKernel_quarter_pos {t : ℝ} (ht : 0 < t) :
    0 < HurwitzZeta.oddKernel ((1 / 4 : ℝ) : UnitAddCircle) t := by
  by_cases hlarge : 1 ≤ t
  · exact oddKernel_quarter_pos_of_one_le hlarge
  · have htOne : t < 1 := lt_of_not_ge hlarge
    have hinv : 1 ≤ 1 / t := by
      rw [le_div_iff₀ ht]
      linarith
    rw [HurwitzZeta.oddKernel_functional_equation]
    exact mul_pos (one_div_pos.mpr (Real.rpow_pos_of_pos ht (3 / 2 : ℝ)))
      (sinKernel_quarter_pos hinv)

private noncomputable def realMellinIntegrand (s t : ℝ) : ℝ :=
  t ^ ((s - 1) / 2) *
    HurwitzZeta.oddKernel ((1 / 4 : ℝ) : UnitAddCircle) t

private lemma realMellinIntegrand_pos {s t : ℝ} (ht : 0 < t) :
    0 < realMellinIntegrand s t := by
  unfold realMellinIntegrand
  exact mul_pos (Real.rpow_pos_of_pos ht _) (oddKernel_quarter_pos ht)

private lemma realMellinIntegrand_complex {s t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ ((((s : ℂ) + 1) / 2) - 1) *
        (HurwitzZeta.oddKernel ((1 / 4 : ℝ) : UnitAddCircle) t : ℂ) =
      (realMellinIntegrand s t : ℂ) := by
  unfold realMellinIntegrand
  rw [show (((s : ℂ) + 1) / 2) - 1 = (((s - 1) / 2 : ℝ) : ℂ) by
    push_cast
    ring,
    ← Complex.ofReal_cpow ht.le, Complex.ofReal_mul]

private lemma realMellinIntegral_pos (s : ℝ) :
    0 < ∫ t : ℝ in Ioi 0, realMellinIntegrand s t := by
  have hm := (HurwitzZeta.hurwitzOddFEPair
    ((1 / 4 : ℝ) : UnitAddCircle)).hasMellin (((s : ℂ) + 1) / 2)
  have hcomplex : IntegrableOn (fun t : ℝ =>
      (t : ℂ) ^ ((((s : ℂ) + 1) / 2) - 1) *
        (HurwitzZeta.oddKernel ((1 / 4 : ℝ) : UnitAddCircle) t : ℂ)) (Ioi 0) := by
    simpa [MellinConvergent, Function.comp_apply, smul_eq_mul] using hm.1
  have hint : IntegrableOn (realMellinIntegrand s) (Ioi 0) := by
    refine (integrableOn_congr_fun ?_ measurableSet_Ioi).mp hcomplex.re
    intro t ht
    change ((t : ℂ) ^ ((((s : ℂ) + 1) / 2) - 1) *
      (HurwitzZeta.oddKernel ((1 / 4 : ℝ) : UnitAddCircle) t : ℂ)).re =
        realMellinIntegrand s t
    rw [realMellinIntegrand_complex ht]
    simp
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi 0)] realMellinIntegrand s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (realMellinIntegrand_pos ht).le
  rw [integral_pos_iff_support_of_nonneg_ae hnonneg hint]
  have hsubset : Ioc (1 : ℝ) 2 ⊆ Function.support (realMellinIntegrand s) := by
    intro t ht
    exact (realMellinIntegrand_pos (zero_lt_one.trans ht.1)).ne'
  have hinterval : 0 < (volume.restrict (Ioi (0 : ℝ))) (Ioc 1 2) := by
    rw [Measure.restrict_apply measurableSet_Ioc]
    norm_num
  exact hinterval.trans_le (measure_mono hsubset)

private lemma completedHurwitzZetaOdd_quarter_real_re_pos (s : ℝ) :
    0 < (HurwitzZeta.completedHurwitzZetaOdd
      ((1 / 4 : ℝ) : UnitAddCircle) (s : ℂ)).re := by
  have hmellin :
      mellin (HurwitzZeta.hurwitzOddFEPair
        ((1 / 4 : ℝ) : UnitAddCircle)).f (((s : ℂ) + 1) / 2) =
        ((∫ t : ℝ in Ioi 0, realMellinIntegrand s t : ℝ) : ℂ) := by
    unfold mellin
    calc
      (∫ t : ℝ in Ioi 0, (t : ℂ) ^ ((((s : ℂ) + 1) / 2) - 1) •
          (HurwitzZeta.hurwitzOddFEPair
            ((1 / 4 : ℝ) : UnitAddCircle)).f t) =
          ∫ t : ℝ in Ioi 0, (realMellinIntegrand s t : ℂ) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        simp only [HurwitzZeta.hurwitzOddFEPair_f, Function.comp_apply, smul_eq_mul]
        exact realMellinIntegrand_complex ht
      _ = ((∫ t : ℝ in Ioi 0, realMellinIntegrand s t : ℝ) : ℂ) :=
        integral_ofReal
  rw [HurwitzZeta.completedHurwitzZetaOdd, StrongFEPair.Λ_eq]
  change 0 < (mellin (HurwitzZeta.hurwitzOddFEPair
    ((1 / 4 : ℝ) : UnitAddCircle)).f (((s : ℂ) + 1) / 2) / 2).re
  rw [hmellin]
  norm_num
  exact realMellinIntegral_pos s

private noncomputable def centralMellinIntegrand (t : ℝ) : ℝ :=
  t ^ (-1 / 4 : ℝ) *
    HurwitzZeta.oddKernel ((1 / 4 : ℝ) : UnitAddCircle) t

private lemma centralMellinIntegrand_pos {t : ℝ} (ht : 0 < t) :
    0 < centralMellinIntegrand t := by
  unfold centralMellinIntegrand
  exact mul_pos (Real.rpow_pos_of_pos ht _) (oddKernel_quarter_pos ht)

private lemma centralMellinIntegrand_complex {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ ((3 / 4 : ℂ) - 1) *
        (HurwitzZeta.oddKernel ((1 / 4 : ℝ) : UnitAddCircle) t : ℂ) =
      (centralMellinIntegrand t : ℂ) := by
  unfold centralMellinIntegrand
  rw [show (3 / 4 : ℂ) - 1 = ((-1 / 4 : ℝ) : ℂ) by norm_num,
    ← Complex.ofReal_cpow ht.le, Complex.ofReal_mul]

private lemma centralMellinIntegral_pos :
    0 < ∫ t : ℝ in Ioi 0, centralMellinIntegrand t := by
  have hm := (HurwitzZeta.hurwitzOddFEPair
    ((1 / 4 : ℝ) : UnitAddCircle)).hasMellin (3 / 4 : ℂ)
  have hcomplex : IntegrableOn (fun t : ℝ =>
      (t : ℂ) ^ ((3 / 4 : ℂ) - 1) *
        (HurwitzZeta.oddKernel ((1 / 4 : ℝ) : UnitAddCircle) t : ℂ)) (Ioi 0) := by
    simpa [MellinConvergent, Function.comp_apply, smul_eq_mul] using hm.1
  have hint : IntegrableOn centralMellinIntegrand (Ioi 0) := by
    refine (integrableOn_congr_fun ?_ measurableSet_Ioi).mp hcomplex.re
    intro t ht
    change ((t : ℂ) ^ ((3 / 4 : ℂ) - 1) *
      (HurwitzZeta.oddKernel ((1 / 4 : ℝ) : UnitAddCircle) t : ℂ)).re =
        centralMellinIntegrand t
    rw [centralMellinIntegrand_complex ht]
    simp
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi 0)] centralMellinIntegrand := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (centralMellinIntegrand_pos ht).le
  rw [integral_pos_iff_support_of_nonneg_ae hnonneg hint]
  have hsubset : Ioc (1 : ℝ) 2 ⊆ Function.support centralMellinIntegrand := by
    intro t ht
    exact (centralMellinIntegrand_pos (zero_lt_one.trans ht.1)).ne'
  have hinterval : 0 < (volume.restrict (Ioi (0 : ℝ))) (Ioc 1 2) := by
    rw [Measure.restrict_apply measurableSet_Ioc]
    norm_num
  exact hinterval.trans_le (measure_mono hsubset)

private lemma completedHurwitzZetaOdd_quarter_central_re_pos :
    0 < (HurwitzZeta.completedHurwitzZetaOdd
      ((1 / 4 : ℝ) : UnitAddCircle) (1 / 2 : ℂ)).re := by
  have hmellin :
      mellin (HurwitzZeta.hurwitzOddFEPair
        ((1 / 4 : ℝ) : UnitAddCircle)).f (3 / 4 : ℂ) =
        ((∫ t : ℝ in Ioi 0, centralMellinIntegrand t : ℝ) : ℂ) := by
    unfold mellin
    calc
      (∫ t : ℝ in Ioi 0, (t : ℂ) ^ ((3 / 4 : ℂ) - 1) •
          (HurwitzZeta.hurwitzOddFEPair
            ((1 / 4 : ℝ) : UnitAddCircle)).f t) =
          ∫ t : ℝ in Ioi 0, (centralMellinIntegrand t : ℂ) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        simp only [HurwitzZeta.hurwitzOddFEPair_f, Function.comp_apply, smul_eq_mul]
        exact centralMellinIntegrand_complex ht
      _ = ((∫ t : ℝ in Ioi 0, centralMellinIntegrand t : ℝ) : ℂ) :=
        integral_ofReal
  rw [HurwitzZeta.completedHurwitzZetaOdd]
  rw [StrongFEPair.Λ_eq]
  norm_num
  change 0 < (mellin (HurwitzZeta.hurwitzOddFEPair
    ((1 / 4 : ℝ) : UnitAddCircle)).f (3 / 4 : ℂ)).re
  rw [hmellin]
  norm_num
  exact centralMellinIntegral_pos

private lemma threeQuarter_eq_neg_quarter :
    ((3 / 4 : ℝ) : UnitAddCircle) = -((1 / 4 : ℝ) : UnitAddCircle) := by
  calc
    ((3 / 4 : ℝ) : UnitAddCircle) = ((-1 / 4 + 1 : ℝ) : UnitAddCircle) := by
      congr 1
      norm_num
    _ = ((-1 / 4 : ℝ) : UnitAddCircle) :=
      AddCircle.coe_add_period (1 : ℝ) (-1 / 4 : ℝ)
    _ = -((1 / 4 : ℝ) : UnitAddCircle) := by
      rw [show (-1 / 4 : ℝ) = -(1 / 4 : ℝ) by ring]
      exact AddCircle.coe_neg (1 : ℝ) (x := (1 / 4 : ℝ))

private lemma chiFour_completed_sum (s : ℂ) :
    (∑ j : ZMod 4, Submission.Helpers.chiFour j *
      HurwitzZeta.completedHurwitzZetaOdd (ZMod.toAddCircle j) s) =
        2 * HurwitzZeta.completedHurwitzZetaOdd
          ((1 / 4 : ℝ) : UnitAddCircle) s := by
  rw [← (ZMod.finEquiv 4).toEquiv.sum_comp]
  have hfin (j : Fin 4) : (ZMod.finEquiv 4) j = (j.val : ZMod 4) := by
    apply ZMod.val_injective
    change j.val = j.val % 4
    exact (Nat.mod_eq_of_lt j.isLt).symm
  have hfun :
      (fun j : Fin 4 => Submission.Helpers.chiFour ((ZMod.finEquiv 4).toEquiv j) *
        HurwitzZeta.completedHurwitzZetaOdd
          (ZMod.toAddCircle ((ZMod.finEquiv 4).toEquiv j)) s) =
      fun j : Fin 4 => Submission.Helpers.chiFour (j.val : ZMod 4) *
        HurwitzZeta.completedHurwitzZetaOdd
          (ZMod.toAddCircle (j.val : ZMod 4)) s := by
    funext j
    rw [show (ZMod.finEquiv 4).toEquiv j = (j.val : ZMod 4) by exact hfin j]
  rw [hfun]
  have hto (j : ℕ) :
      ZMod.toAddCircle (j : ZMod 4) = ((j / 4 : ℝ) : UnitAddCircle) :=
    ZMod.toAddCircle_natCast j
  norm_num [Fin.sum_univ_succ]
  have hto1 : ZMod.toAddCircle (1 : ZMod 4) =
      ((1 / 4 : ℝ) : UnitAddCircle) := by simpa using hto 1
  have hto2 : ZMod.toAddCircle (1 : ZMod 4) + ZMod.toAddCircle (1 : ZMod 4) =
      ((1 / 2 : ℝ) : UnitAddCircle) := by
    rw [hto1, ← AddCircle.coe_add]
    congr 1
    norm_num
  have hto3 : ZMod.toAddCircle (1 : ZMod 4) + ZMod.toAddCircle (1 : ZMod 4) +
      ZMod.toAddCircle (1 : ZMod 4) = ((3 / 4 : ℝ) : UnitAddCircle) := by
    rw [hto2, hto1, ← AddCircle.coe_add]
    congr 1
    norm_num
  rw [hto3, hto2, hto1]
  norm_num [Submission.Helpers.chiFour, ZMod.χ₄]
  rw [threeQuarter_eq_neg_quarter, HurwitzZeta.completedHurwitzZetaOdd_neg]
  ring

private lemma chiFour_completedLFunction_central_ne_zero :
    DirichletCharacter.completedLFunction Submission.Helpers.chiFour (1 / 2 : ℂ) ≠ 0 := by
  change ZMod.completedLFunction Submission.Helpers.chiFour (1 / 2 : ℂ) ≠ 0
  rw [ZMod.completedLFunction_def_odd Submission.Helpers.chiFour_odd.to_fun,
    chiFour_completed_sum]
  apply mul_ne_zero
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  · exact mul_ne_zero (by norm_num) <|
      ne_of_apply_ne Complex.re (ne_of_gt completedHurwitzZetaOdd_quarter_central_re_pos)

theorem chiFour_completedLFunction_real_ne_zero (s : ℝ) :
    DirichletCharacter.completedLFunction Submission.Helpers.chiFour (s : ℂ) ≠ 0 := by
  change ZMod.completedLFunction Submission.Helpers.chiFour (s : ℂ) ≠ 0
  rw [ZMod.completedLFunction_def_odd Submission.Helpers.chiFour_odd.to_fun,
    chiFour_completed_sum]
  apply mul_ne_zero
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  · exact mul_ne_zero (by norm_num) <|
      ne_of_apply_ne Complex.re
        (ne_of_gt (completedHurwitzZetaOdd_quarter_real_re_pos s))

theorem chiFour_LFunction_real_ne_zero {s : ℝ} (hs : -1 < s) :
    DirichletCharacter.LFunction Submission.Helpers.chiFour (s : ℂ) ≠ 0 := by
  rw [Submission.Analytic.chiFour_LFunction_eq_completed_mul_invGammaFactor]
  exact mul_ne_zero (chiFour_completedLFunction_real_ne_zero s)
    (Submission.Analytic.chiFour_invGammaFactor_ne_zero (by simpa using hs))

theorem chiFour_LFunction_central_ne_zero :
    DirichletCharacter.LFunction Submission.Helpers.chiFour (1 / 2 : ℂ) ≠ 0 := by
  rw [Submission.Analytic.chiFour_LFunction_eq_completed_mul_invGammaFactor]
  exact mul_ne_zero chiFour_completedLFunction_central_ne_zero
    (Submission.Analytic.chiFour_invGammaFactor_ne_zero (by norm_num))

theorem chiFourCentralMultiplicity_eq_zero :
    Submission.PrimeSeries.chiFourCentralMultiplicity = 0 := by
  rw [Submission.PrimeSeries.chiFourCentralMultiplicity,
    if_neg chiFour_LFunction_central_ne_zero]

end Submission.Central
