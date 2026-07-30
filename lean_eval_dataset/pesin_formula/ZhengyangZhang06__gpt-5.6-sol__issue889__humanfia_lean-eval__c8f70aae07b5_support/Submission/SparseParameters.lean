import Submission.SparseGeometry

namespace Submission.Helpers

open Filter

/-- A single exponent tolerance small enough for every Pesin-block and final
diameter estimate used below. -/
noncomputable def sparseEta
    (rate lam1 lam2 epsilon : ℝ) : ℝ :=
  min (min rate (min lam1 (-lam2))) epsilon / 100

lemma sparseEta_spec
    {rate lam1 lam2 epsilon : ℝ}
    (hrate : 0 < rate) (hlam1 : 0 < lam1) (hlam2 : lam2 < 0)
    (hepsilon : 0 < epsilon) :
    let eta := sparseEta rate lam1 lam2 epsilon
    0 < eta ∧
      8 * eta < lam1 - lam2 ∧
      lam2 + 6 * eta < 0 ∧
      -lam1 + 6 * eta < 0 ∧
      8 * eta < rate ∧
      6 * eta < epsilon / 16 := by
  dsimp only [sparseEta]
  have hbase :
      0 < min (min rate (min lam1 (-lam2))) epsilon := by
    exact lt_min
      (lt_min hrate (lt_min hlam1 (neg_pos.mpr hlam2))) hepsilon
  have heta :
      0 < min (min rate (min lam1 (-lam2))) epsilon / 100 :=
    div_pos hbase (by norm_num)
  have hle_rate :
      min (min rate (min lam1 (-lam2))) epsilon ≤ rate :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hle_lam1 :
      min (min rate (min lam1 (-lam2))) epsilon ≤ lam1 :=
    (min_le_left _ _).trans
      ((min_le_right rate _).trans (min_le_left _ _))
  have hle_lam2 :
      min (min rate (min lam1 (-lam2))) epsilon ≤ -lam2 :=
    (min_le_left _ _).trans
      ((min_le_right rate _).trans (min_le_right _ _))
  have hle_epsilon :
      min (min rate (min lam1 (-lam2))) epsilon ≤ epsilon :=
    min_le_right _ _
  refine ⟨heta, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- A positive bad-time density which is simultaneously negligible for the
diameter and cover-multiplicity estimates. -/
noncomputable def sparseBadDensity
    (epsilon diameterCoeff multiplicityCoeff : ℝ) : ℝ :=
  min 1
    (epsilon / (64 * (diameterCoeff + multiplicityCoeff + 1)))

lemma sparseBadDensity_spec
    {epsilon diameterCoeff multiplicityCoeff : ℝ}
    (hepsilon : 0 < epsilon)
    (hdiameterCoeff : 0 ≤ diameterCoeff)
    (hmultiplicityCoeff : 0 ≤ multiplicityCoeff) :
    let q := sparseBadDensity epsilon diameterCoeff multiplicityCoeff
    0 < q ∧ q ≤ 1 ∧
      q * diameterCoeff < epsilon / 64 ∧
      q * multiplicityCoeff < epsilon / 64 := by
  let A := diameterCoeff + multiplicityCoeff + 1
  have hA : 0 < A := by
    dsimp [A]
    linarith
  have hdenom : 0 < 64 * A := mul_pos (by norm_num) hA
  have hquot :
      0 < epsilon / (64 * A) := div_pos hepsilon hdenom
  have hq_pos :
      0 < min 1 (epsilon / (64 * A)) := lt_min zero_lt_one hquot
  have hq_one :
      min 1 (epsilon / (64 * A)) ≤ 1 := min_le_left _ _
  have hq_quot :
      min 1 (epsilon / (64 * A)) ≤ epsilon / (64 * A) :=
    min_le_right _ _
  have hdiam_lt_A : diameterCoeff < A := by
    dsimp [A]
    linarith
  have hmult_lt_A : multiplicityCoeff < A := by
    dsimp [A]
    linarith
  have hdiam_ratio : diameterCoeff / A < 1 :=
    (div_lt_one hA).2 hdiam_lt_A
  have hmult_ratio : multiplicityCoeff / A < 1 :=
    (div_lt_one hA).2 hmult_lt_A
  have hdiam :
      min 1 (epsilon / (64 * A)) * diameterCoeff <
        epsilon / 64 := by
    calc
      min 1 (epsilon / (64 * A)) * diameterCoeff ≤
          (epsilon / (64 * A)) * diameterCoeff := by
        gcongr
      _ = epsilon / 64 * (diameterCoeff / A) := by
        field_simp [hA.ne']
      _ < epsilon / 64 * 1 := by
        gcongr
      _ = epsilon / 64 := by ring
  have hmult :
      min 1 (epsilon / (64 * A)) * multiplicityCoeff <
        epsilon / 64 := by
    calc
      min 1 (epsilon / (64 * A)) * multiplicityCoeff ≤
          (epsilon / (64 * A)) * multiplicityCoeff := by
        gcongr
      _ = epsilon / 64 * (multiplicityCoeff / A) := by
        field_simp [hA.ne']
      _ < epsilon / 64 * 1 := by
        gcongr
      _ = epsilon / 64 := by ring
  simpa [sparseBadDensity, A] using
    And.intro hq_pos (And.intro hq_one (And.intro hdiam hmult))

/-- Choose a base-four refinement depth dominating every fixed secant-control
scale. -/
lemma exists_sparseDepth
    {M stableRate : ℝ} (_hM : 1 ≤ M) :
    ∃ D : ℕ, 0 < D ∧
      M ≤ (4 : ℝ) ^ D ∧
      4 * M ^ 2 ≤ (4 : ℝ) ^ D ∧
      4 * M ^ 2 * Real.exp (-stableRate) ≤ (4 : ℝ) ^ D := by
  let A :=
    max 1
      (max M
        (max (4 * M ^ 2)
          (4 * M ^ 2 * Real.exp (-stableRate))))
  have hA : 1 ≤ A := by
    exact le_max_left _ _
  obtain ⟨d, _hd_lower, hd_upper⟩ :=
    exists_nat_pow_near hA (by norm_num : (1 : ℝ) < 4)
  let D := d + 1
  have hdom : A ≤ (4 : ℝ) ^ D := by
    exact hd_upper.le
  refine ⟨D, by omega, ?_, ?_, ?_⟩
  · exact (le_max_of_le_right (le_max_left _ _)).trans hdom
  · exact
      (le_max_of_le_right
        (le_max_of_le_right (le_max_left _ _))).trans hdom
  · exact
      (le_max_of_le_right
        (le_max_of_le_right (le_max_right _ _))).trans hdom

/-- A local partition radius small enough for both short-edge controls. -/
noncomputable def sparseRadius
    (M stableRate : ℝ) (H : ℕ) : ℝ :=
  min (1 / M ^ H)
    (min 1
      (Real.exp (stableRate * H) /
        ((H : ℝ) * M * M ^ H * (2 * M) ^ (H + 1))))

lemma sparseRadius_spec
    {M stableRate : ℝ} {H : ℕ}
    (hM : 1 ≤ M) (hH : 0 < H) :
    let R := sparseRadius M stableRate H
    0 < R ∧ R ≤ 1 ∧ M ^ H * R ≤ 1 ∧
      H * (M * (M ^ H * R)) * (2 * M) ^ (H + 1) ≤
        Real.exp (stableRate * H) := by
  let coeff : ℝ :=
    (H : ℝ) * M * M ^ H * (2 * M) ^ (H + 1)
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
  have hcoeff : 0 < coeff := by
    dsimp [coeff]
    positivity
  have hfirst : 0 < 1 / M ^ H := by positivity
  have hthird :
      0 < Real.exp (stableRate * H) / coeff :=
    div_pos (Real.exp_pos _) hcoeff
  have hRpos :
      0 < min (1 / M ^ H)
        (min 1 (Real.exp (stableRate * H) / coeff)) :=
    lt_min hfirst (lt_min zero_lt_one hthird)
  have hRone :
      min (1 / M ^ H)
        (min 1 (Real.exp (stableRate * H) / coeff)) ≤ 1 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hRfirst :
      min (1 / M ^ H)
        (min 1 (Real.exp (stableRate * H) / coeff)) ≤
          1 / M ^ H :=
    min_le_left _ _
  have hRthird :
      min (1 / M ^ H)
        (min 1 (Real.exp (stableRate * H) / coeff)) ≤
          Real.exp (stableRate * H) / coeff :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hsmall : M ^ H *
      min (1 / M ^ H)
        (min 1 (Real.exp (stableRate * H) / coeff)) ≤ 1 := by
    calc
      M ^ H *
          min (1 / M ^ H)
            (min 1 (Real.exp (stableRate * H) / coeff)) ≤
          M ^ H * (1 / M ^ H) := by
        gcongr
      _ = 1 := by
        field_simp
  have herror :
      (H : ℝ) *
          (M * (M ^ H *
            min (1 / M ^ H)
              (min 1 (Real.exp (stableRate * H) / coeff)))) *
          (2 * M) ^ (H + 1) ≤
        Real.exp (stableRate * H) := by
    have := (le_div_iff₀ hcoeff).mp hRthird
    dsimp [coeff] at this
    nlinarith
  simpa [sparseRadius, coeff] using
    And.intro hRpos (And.intro hRone (And.intro hsmall herror))

/-- A coarse-grid spacing that absorbs the fixed path-comparison constants
and makes both coding contributions negligible. -/
lemma exists_sparseSpacing
    {stableRate unstableRate C qpath epsilon : ℝ}
    (_hstableRate : stableRate < 0)
    (_hunstableRate : unstableRate < 0)
    (hsumRate : stableRate + unstableRate < 0)
    (hC : 0 < C) (hqpath : 1 ≤ qpath) (hepsilon : 0 < epsilon) :
    ∃ H : ℕ, 0 < H ∧
      Real.log qpath / H < epsilon / 64 ∧
      Real.log 2 / H < epsilon / 64 ∧
      (∀ g : ℕ, H ≤ g →
        (4 * C) * qpath *
          Real.exp ((stableRate + unstableRate) * g) ≤ 1 / 4) ∧
      ∀ g : ℕ, H ≤ g →
        C * Real.exp (unstableRate * g) *
          Real.exp (stableRate * g) ≤ 1 / 2 := by
  have hqpath_pos : 0 < qpath := zero_lt_one.trans_le hqpath
  have hcrossConst : 0 < (4 * C) * qpath := by positivity
  have hsmallCross :=
    eventually_exp_neg_mul_add_lt
      (s := -(stableRate + unstableRate)) (neg_pos.mpr hsumRate)
      (by norm_num : (0 : ℝ) < 1 / 4)
      (Real.log ((4 * C) * qpath))
  have heventCross :
      ∀ᶠ g : ℕ in atTop,
        (4 * C) * qpath *
          Real.exp ((stableRate + unstableRate) * g) ≤ 1 / 4 := by
    filter_upwards [hsmallCross] with g hg
    rw [show
        (4 * C) * qpath *
            Real.exp ((stableRate + unstableRate) * (g : ℝ)) =
          Real.exp
            (-(-(stableRate + unstableRate)) * (g : ℝ) +
              Real.log ((4 * C) * qpath)) by
          rw [show
              -(-(stableRate + unstableRate)) * (g : ℝ) +
                  Real.log ((4 * C) * qpath) =
                Real.log ((4 * C) * qpath) +
                  (stableRate + unstableRate) * (g : ℝ) by ring,
            Real.exp_add, Real.exp_log hcrossConst]]
    exact hg.le
  have hunstableConst : 0 < C := hC
  have hsmallUnstable :=
    eventually_exp_neg_mul_add_lt
      (s := -(stableRate + unstableRate)) (neg_pos.mpr hsumRate)
      (by norm_num : (0 : ℝ) < 1 / 2)
      (Real.log C)
  have heventUnstable :
      ∀ᶠ g : ℕ in atTop,
        C * Real.exp (unstableRate * g) *
          Real.exp (stableRate * g) ≤ 1 / 2 := by
    filter_upwards [hsmallUnstable] with g hg
    rw [show
        C * Real.exp (unstableRate * (g : ℝ)) *
            Real.exp (stableRate * (g : ℝ)) =
          Real.exp
            (-(-(stableRate + unstableRate)) * (g : ℝ) +
              Real.log C) by
          rw [show
              -(-(stableRate + unstableRate)) * (g : ℝ) + Real.log C =
                Real.log C +
                  (unstableRate * (g : ℝ) +
                    stableRate * (g : ℝ)) by ring,
            Real.exp_add, Real.exp_add, Real.exp_log hunstableConst]
          ring]
    exact hg.le
  obtain ⟨Ncross, hNcross⟩ := eventually_atTop.1 heventCross
  obtain ⟨Nunstable, hNunstable⟩ :=
    eventually_atTop.1 heventUnstable
  have hlogq :
      ∀ᶠ H : ℕ in atTop,
        Real.log qpath / H < epsilon / 64 :=
    (tendsto_order.1
      (tendsto_const_div_atTop_nhds_zero_nat (Real.log qpath))).2
        _ (div_pos hepsilon (by norm_num))
  have hlog2 :
      ∀ᶠ H : ℕ in atTop,
        Real.log 2 / H < epsilon / 64 :=
    (tendsto_order.1
      (tendsto_const_div_atTop_nhds_zero_nat (Real.log 2))).2
        _ (div_pos hepsilon (by norm_num))
  have hcrossTail :
      ∀ᶠ H : ℕ in atTop, ∀ g : ℕ, H ≤ g →
        (4 * C) * qpath *
          Real.exp ((stableRate + unstableRate) * g) ≤ 1 / 4 := by
    filter_upwards [eventually_ge_atTop Ncross] with H hHN
    intro g hHg
    exact hNcross g (hHN.trans hHg)
  have hunstableTail :
      ∀ᶠ H : ℕ in atTop, ∀ g : ℕ, H ≤ g →
        C * Real.exp (unstableRate * g) *
          Real.exp (stableRate * g) ≤ 1 / 2 := by
    filter_upwards [eventually_ge_atTop Nunstable] with H hHN
    intro g hHg
    exact hNunstable g (hHN.trans hHg)
  have hall :
      ∀ᶠ H : ℕ in atTop,
        0 < H ∧
          Real.log qpath / H < epsilon / 64 ∧
          Real.log 2 / H < epsilon / 64 ∧
          (∀ g : ℕ, H ≤ g →
            (4 * C) * qpath *
              Real.exp ((stableRate + unstableRate) * g) ≤ 1 / 4) ∧
          ∀ g : ℕ, H ≤ g →
            C * Real.exp (unstableRate * g) *
              Real.exp (stableRate * g) ≤ 1 / 2 := by
    filter_upwards [eventually_gt_atTop 0, hlogq, hlog2,
      hcrossTail, hunstableTail] with H hH hq htwo hcross hunstable
    exact ⟨hH, hq, htwo, hcross, hunstable⟩
  exact hall.exists

end Submission.Helpers
