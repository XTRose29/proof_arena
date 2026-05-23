import Mathlib

open Real MeasureTheory Filter

namespace Submission.Helpers

-- Copy of the definition from ChallengeDeps for subagent access
noncomputable def heatSolution' (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  if 0 < t then
    (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) *
      ∫ y : ℝ, Real.exp (-((x - y) ^ 2) / (4 * t)) * f y
  else
    f x

/-! ## Basic integrability of the heat kernel integrand -/

lemma integrable_heat_integrand (f : ℝ → ℝ) (hf_cont : Continuous f)
    (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) (t : ℝ) (ht : 0 < t) (x : ℝ) :
    Integrable (fun y => exp (-((x - y) ^ 2) / (4 * t)) * f y) volume := by
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun y => Real.exp ( - ( x - y ) ^ 2 / ( 4 * t ) ) * hf_bdd.choose;
  · exact MeasureTheory.Integrable.mul_const ( by simpa [ div_eq_inv_mul ] using ( integrable_exp_neg_mul_sq ( by positivity ) ) |> ( fun h => h.comp_sub_left x ) ) _;
  · exact Continuous.aestronglyMeasurable ( by continuity );
  · filter_upwards [ ] using fun y => by rw [ Real.norm_eq_abs, abs_mul, abs_of_nonneg ( Real.exp_pos _ |> LT.lt.le ) ] ; exact mul_le_mul_of_nonneg_left ( hf_bdd.choose_spec y ) ( Real.exp_pos _ |> LT.lt.le ) ;

/-! ## Normalized Gaussian integral -/

lemma heat_kernel_integral_one (t : ℝ) (ht : 0 < t) (x : ℝ) :
    ((4 * π * t)⁻¹) ^ ((1 : ℝ) / 2) * ∫ y : ℝ, exp (-((x - y) ^ 2) / (4 * t)) = 1 := by
  have h_gauss : ∫ y, Real.exp (-((y) ^ 2) / (4 * t)) = Real.sqrt (4 * Real.pi * t) := by
    convert integral_gaussian ( 1 / ( 4 * t ) ) using 1 <;> norm_num [ div_eq_inv_mul ] ; ring;
  rw [ ← Real.sqrt_eq_rpow, MeasureTheory.integral_sub_left_eq_self fun y => Real.exp ( -y ^ 2 / ( 4 * t ) ), h_gauss ];
  rw [ ← Real.sqrt_mul ( by positivity ), inv_mul_cancel₀ ( by positivity ), Real.sqrt_one ]

/-! ## Spatial differentiation -/

lemma hasDerivAt_gaussian_x (t : ℝ) (ht : 0 < t) (x y : ℝ) :
    HasDerivAt (fun z => exp (-((z - y) ^ 2) / (4 * t)))
      (-(x - y) / (2 * t) * exp (-((x - y) ^ 2) / (4 * t))) x := by
  field_simp;
  convert HasDerivAt.exp ( HasDerivAt.neg ( HasDerivAt.div_const ( HasDerivAt.comp x ( hasDerivAt_pow 2 _ ) ( hasDerivAt_id' x |> HasDerivAt.sub <| hasDerivAt_const _ _ ) ) _ ) ) using 1 ; ring!;
  norm_num ; ring

lemma integrable_heat_deriv_x_integrand (f : ℝ → ℝ) (hf_cont : Continuous f)
    (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) (t : ℝ) (ht : 0 < t) (x : ℝ) :
    Integrable (fun y => -(x - y) / (2 * t) * exp (-((x - y) ^ 2) / (4 * t)) * f y) volume := by
  have h_integrable : Integrable (fun y => |y| * Real.exp (-y ^ 2 / (4 * t))) volume := by
    have := @integrable_rpow_mul_exp_neg_mul_sq;
    specialize @this ( 1 / ( 4 * t ) ) ( by positivity ) 1 ; norm_num at this;
    convert this.norm using 2 ; norm_num ; ring;
    norm_num;
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun y => |y - x| * Real.exp ( - ( y - x ) ^ 2 / ( 4 * t ) ) * hf_bdd.choose / ( 2 * t );
  · exact MeasureTheory.Integrable.div_const ( MeasureTheory.Integrable.mul_const ( by simpa using h_integrable.comp_sub_right x ) _ ) _;
  · exact Continuous.aestronglyMeasurable ( by continuity );
  · simp_all +decide [ abs_div, abs_mul, abs_neg, abs_of_pos, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
    filter_upwards [ ] with y using by rw [ show ( x - y ) ^ 2 = ( y - x ) ^ 2 by ring ] ; nlinarith [ hf_bdd.choose_spec y, show 0 ≤ |y - x| * ( t⁻¹ * ( 2⁻¹ * Real.exp ( - ( t⁻¹ * ( ( y - x ) ^ 2 * 4⁻¹ ) ) ) ) ) by positivity ] ;

lemma heat_deriv_x_dominated_bound (f : ℝ → ℝ) (hf_cont : Continuous f)
    (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) (t : ℝ) (ht : 0 < t) (x₀ : ℝ) :
    ∃ bound : ℝ → ℝ, Integrable bound volume ∧
      (∀ y : ℝ, ∀ z ∈ Metric.ball x₀ 1,
        ‖-(z - y) / (2 * t) * exp (-((z - y) ^ 2) / (4 * t)) * f y‖ ≤ bound y) := by
  obtain ⟨ M, hM ⟩ := hf_bdd;
  refine' ⟨ fun y => ( |x₀ - y| + 1 ) / ( 2 * t ) * Real.exp ( -max 0 ( |x₀ - y| - 1 ) ^ 2 / ( 4 * t ) ) * M, _, _ ⟩;
  · -- The function is dominated by an integrable function, so it is integrable.
    have h_dom : ∀ y, (|x₀ - y| + 1) / (2 * t) * Real.exp (-max 0 (|x₀ - y| - 1) ^ 2 / (4 * t)) ≤ (|x₀ - y| + 1) * Real.exp (-|x₀ - y| ^ 2 / (8 * t)) * (Real.exp (1 / (4 * t)) / (2 * t)) := by
      intro y
      have h_exp : Real.exp (-max 0 (|x₀ - y| - 1) ^ 2 / (4 * t)) ≤ Real.exp (-|x₀ - y| ^ 2 / (8 * t)) * Real.exp (1 / (4 * t)) := by
        rw [ ← Real.exp_add ];
        by_cases h : |x₀ - y| ≤ 1 <;> simp_all +decide [ div_eq_mul_inv ];
        · nlinarith [ abs_le.mp h, inv_pos.mpr ht, mul_inv_cancel₀ ht.ne', show ( x₀ - y ) ^ 2 ≤ 1 by nlinarith [ abs_le.mp h ] ];
        · rw [ max_eq_right ( by linarith ) ] ; ring_nf ; norm_num [ ht.le ];
          cases abs_cases ( x₀ - y ) <;> nlinarith [ inv_pos.2 ht, mul_inv_cancel₀ ht.ne', sq_nonneg ( x₀ - y - 2 ), sq_nonneg ( x₀ - y + 2 ) ];
      convert mul_le_mul_of_nonneg_left h_exp ( show 0 ≤ ( |x₀ - y| + 1 ) / ( 2 * t ) by positivity ) using 1 ; ring;
    -- The function $(|x₀ - y| + 1) * \exp(-|x₀ - y|^2 / (8 * t))$ is integrable.
    have h_integrable : Integrable (fun y => (|x₀ - y| + 1) * Real.exp (-|x₀ - y| ^ 2 / (8 * t))) volume := by
      have h_integrable : Integrable (fun y => (|y| + 1) * Real.exp (-|y| ^ 2 / (8 * t))) volume := by
        have h_integrable : Integrable (fun y => |y| * Real.exp (-|y| ^ 2 / (8 * t))) volume := by
          have := @integrable_rpow_mul_exp_neg_mul_sq;
          specialize @this ( 1 / ( 8 * t ) ) ( by positivity ) 1 ; norm_num at this;
          convert this.norm using 2 ; norm_num ; ring;
          norm_num;
        simp_all +decide [ add_mul ];
        simpa [ div_eq_inv_mul ] using ( integrable_exp_neg_mul_sq ( by positivity ) );
      convert h_integrable.comp_sub_left x₀ using 1;
    refine' MeasureTheory.Integrable.mono' ( h_integrable.mul_const ( Real.exp ( 1 / ( 4 * t ) ) / ( 2 * t ) * M ) ) _ _;
    · fun_prop;
    · filter_upwards [ ] with y using by rw [ Real.norm_of_nonneg ( mul_nonneg ( mul_nonneg ( div_nonneg ( by positivity ) ( by positivity ) ) ( Real.exp_nonneg _ ) ) ( by linarith [ abs_le.mp ( hM x₀ ) ] ) ) ] ; simpa only [ mul_assoc ] using mul_le_mul_of_nonneg_right ( h_dom y ) ( by linarith [ abs_le.mp ( hM x₀ ) ] ) ;
  · intro y z hz
    have hz_bound : |z - y| ≤ |x₀ - y| + 1 := by
      cases abs_cases ( z - y ) <;> cases abs_cases ( x₀ - y ) <;> linarith [ abs_lt.mp ( mem_ball_iff_norm.mp hz ) ]
    have h_exp_bound : Real.exp (-(z - y) ^ 2 / (4 * t)) ≤ Real.exp (-max 0 (|x₀ - y| - 1) ^ 2 / (4 * t)) := by
      have h_exp_bound : (z - y) ^ 2 ≥ (max 0 (|x₀ - y| - 1)) ^ 2 := by
        cases max_cases ( 0 : ℝ ) ( |x₀ - y| - 1 ) <;> cases abs_cases ( x₀ - y ) <;> cases abs_cases ( z - y ) <;> push_cast [ * ] at * <;> nlinarith [ abs_lt.mp ( mem_ball_iff_norm.mp hz ) ];
      exact Real.exp_le_exp.mpr ( by rw [ div_le_div_iff_of_pos_right ( by positivity ) ] ; linarith )
    have h_final_bound : |-(z - y) / (2 * t) * Real.exp (-(z - y) ^ 2 / (4 * t)) * f y| ≤ (|x₀ - y| + 1) / (2 * t) * Real.exp (-max 0 (|x₀ - y| - 1) ^ 2 / (4 * t)) * M := by
      norm_num [ abs_mul, abs_div, abs_neg, abs_of_pos ht ];
      gcongr;
      · rwa [ abs_sub_comm ];
      · exact hM y
    exact h_final_bound

set_option maxHeartbeats 400000 in
lemma hasDerivAt_heat_integral_x (f : ℝ → ℝ) (hf_cont : Continuous f)
    (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) (t : ℝ) (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun z => ∫ y : ℝ, exp (-((z - y) ^ 2) / (4 * t)) * f y)
      (∫ y : ℝ, -(x - y) / (2 * t) * exp (-((x - y) ^ 2) / (4 * t)) * f y) x := by
  have h_deriv : HasDerivAt (fun z => ∫ y, Real.exp (-((z - y) ^ 2) / (4 * t)) * f y) (∫ y, -(x - y) / (2 * t) * Real.exp (-((x - y) ^ 2) / (4 * t)) * f y) x := by
    have h_bound : ∃ bound : ℝ → ℝ, Integrable bound volume ∧ (∀ y, ∀ z ∈ Metric.ball x 1, ‖-(z - y) / (2 * t) * Real.exp (-((z - y) ^ 2) / (4 * t)) * f y‖ ≤ bound y) := by
      exact heat_deriv_x_dominated_bound f hf_cont hf_bdd t ht x
    obtain ⟨ bound, h_bound₁, h_bound₂ ⟩ := h_bound;
    have := @hasDerivAt_integral_of_dominated_loc_of_deriv_le;
    specialize this ( Metric.ball_mem_nhds x zero_lt_one ) ( show ∀ᶠ z in nhds x, AEStronglyMeasurable ( fun y => Real.exp ( - ( z - y ) ^ 2 / ( 4 * t ) ) * f y ) MeasureTheory.volume from Filter.Eventually.of_forall fun z => Continuous.aestronglyMeasurable ( by continuity ) ) ( show Integrable ( fun y => Real.exp ( - ( x - y ) ^ 2 / ( 4 * t ) ) * f y ) MeasureTheory.volume from by
                                                                                                                                                                                                                                                                                          exact integrable_heat_integrand f hf_cont hf_bdd t ht x ) ( show AEStronglyMeasurable ( fun y => - ( x - y ) / ( 2 * t ) * Real.exp ( - ( x - y ) ^ 2 / ( 4 * t ) ) * f y ) MeasureTheory.volume from by
                                                                                                                                                                                                                                                                                                                                                                                                            exact Continuous.aestronglyMeasurable ( by continuity ) ) ( show ∀ᵐ y ∂MeasureTheory.volume, ∀ z ∈ Metric.ball x 1, ‖- ( z - y ) / ( 2 * t ) * Real.exp ( - ( z - y ) ^ 2 / ( 4 * t ) ) * f y‖ ≤ bound y from by
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    exact Filter.Eventually.of_forall fun y z hz => h_bound₂ y z hz ) h_bound₁ ( show ∀ᵐ y ∂MeasureTheory.volume, ∀ z ∈ Metric.ball x 1, HasDerivAt ( fun z => Real.exp ( - ( z - y ) ^ 2 / ( 4 * t ) ) * f y ) ( - ( z - y ) / ( 2 * t ) * Real.exp ( - ( z - y ) ^ 2 / ( 4 * t ) ) * f y ) z from by
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            filter_upwards [ ] with y z hz using by convert HasDerivAt.mul ( hasDerivAt_gaussian_x t ht z y ) ( hasDerivAt_const _ _ ) using 1 ; ring; ) ; simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] ;
  exact h_deriv

/-! ## Second spatial derivative -/

lemma hasDerivAt_gaussian_x_deriv (t : ℝ) (ht : 0 < t) (x y : ℝ) :
    HasDerivAt (fun z => -(z - y) / (2 * t) * exp (-((z - y) ^ 2) / (4 * t)))
      (((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * exp (-((x - y) ^ 2) / (4 * t))) x := by
  norm_num +zetaDelta at *;
  convert HasDerivAt.mul ( HasDerivAt.div_const ( hasDerivAt_id' x |> HasDerivAt.const_sub y ) _ ) ( HasDerivAt.exp ( HasDerivAt.div_const ( HasDerivAt.neg ( hasDerivAt_pow 2 ( x - y ) |> HasDerivAt.comp x <| hasDerivAt_id' x |> HasDerivAt.sub <| hasDerivAt_const _ _ ) ) _ ) ) using 1 ; norm_num ; ring

lemma integrable_heat_deriv_xx_integrand (f : ℝ → ℝ) (hf_cont : Continuous f)
    (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) (t : ℝ) (ht : 0 < t) (x : ℝ) :
    Integrable (fun y => ((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) *
      exp (-((x - y) ^ 2) / (4 * t)) * f y) volume := by
  -- The term ((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * exp(-(x - y) ^ 2 / (4 * t)) is bounded and integrable.
  have h_integrable : Integrable (fun y => ((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * Real.exp (-(x - y) ^ 2 / (4 * t))) volume := by
    have h_integrable : MeasureTheory.Integrable (fun y => y^2 * Real.exp (-y^2 / (4 * t))) MeasureTheory.volume := by
      have := @integrable_rpow_mul_exp_neg_mul_sq;
      convert @this ( 1 / ( 4 * t ) ) ( by positivity ) 2 ( by norm_num ) using 3 ; ring;
      · norm_cast;
      · ring;
    have h_integrable : MeasureTheory.Integrable (fun y => (y^2 / (4 * t^2) - 1 / (2 * t)) * Real.exp (-y^2 / (4 * t))) MeasureTheory.volume := by
      simp_all +decide [ sub_mul, div_mul_eq_mul_div ];
      exact MeasureTheory.Integrable.sub ( h_integrable.div_const _ ) ( MeasureTheory.Integrable.const_mul ( by simpa [ div_eq_inv_mul ] using ( integrable_exp_neg_mul_sq ( by positivity ) ) ) _ );
    convert h_integrable.comp_sub_left x using 1;
  refine' h_integrable.norm.mul_const _ |> fun h => h.mono' _ _;
  exacts [ hf_bdd.choose, by exact MeasureTheory.AEStronglyMeasurable.mul ( h_integrable.aestronglyMeasurable ) ( hf_cont.aestronglyMeasurable ), Filter.Eventually.of_forall fun y => by simpa [ abs_mul ] using mul_le_mul_of_nonneg_left ( hf_bdd.choose_spec y ) ( by positivity ) ]

lemma heat_deriv_xx_dominated_bound (f : ℝ → ℝ) (hf_cont : Continuous f)
    (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) (t : ℝ) (ht : 0 < t) (x₀ : ℝ) :
    ∃ bound : ℝ → ℝ, Integrable bound volume ∧
      (∀ y : ℝ, ∀ z ∈ Metric.ball x₀ 1,
        ‖((z - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) *
          exp (-((z - y) ^ 2) / (4 * t)) * f y‖ ≤ bound y) := by
  refine' ⟨ _, _, _ ⟩;
  exact fun y => ( ( |x₀ - y| + 1 ) ^ 2 / ( 4 * t ^ 2 ) + 1 / ( 2 * t ) ) * Real.exp ( -max ( 0 : ℝ ) ( |x₀ - y| - 1 ) ^ 2 / ( 4 * t ) ) * hf_bdd.choose;
  · have h_integrable : MeasureTheory.Integrable (fun y => (|x₀ - y| + 1) ^ 2 * Real.exp (-max 0 (|x₀ - y| - 1) ^ 2 / (4 * t))) MeasureTheory.volume := by
      have h_integrable : MeasureTheory.Integrable (fun y => (|y| + 1) ^ 2 * Real.exp (-max 0 (|y| - 1) ^ 2 / (4 * t))) MeasureTheory.volume := by
        have h_integrable : MeasureTheory.Integrable (fun y => (|y| + 1)^2 * Real.exp (-|y|^2 / (16 * t))) MeasureTheory.volume := by
          have h_integrable : MeasureTheory.Integrable (fun y => y^2 * Real.exp (-y^2 / (16 * t))) MeasureTheory.volume ∧ MeasureTheory.Integrable (fun y => |y| * Real.exp (-y^2 / (16 * t))) MeasureTheory.volume ∧ MeasureTheory.Integrable (fun y => Real.exp (-y^2 / (16 * t))) MeasureTheory.volume := by
            refine' ⟨ _, _, _ ⟩;
            · have := @integrable_rpow_mul_exp_neg_mul_sq;
              convert @this ( 1 / ( 16 * t ) ) ( by positivity ) 2 ( by norm_num ) using 3 ; ring;
              · norm_cast;
              · ring;
            · have := @integrable_rpow_mul_exp_neg_mul_sq;
              specialize @this ( 1 / ( 16 * t ) ) ( by positivity ) 1 ; norm_num at this;
              convert this.norm using 2 ; norm_num ; ring;
              norm_num;
            · simpa [ div_eq_inv_mul ] using ( integrable_exp_neg_mul_sq ( by positivity ) );
          convert h_integrable.1.add ( h_integrable.2.1.const_mul 2 ) |> MeasureTheory.Integrable.add <| h_integrable.2.2 using 2 ; ring;
          norm_num ; ring;
        have h_integrable : ∀ y : ℝ, (|y| + 1)^2 * Real.exp (-max 0 (|y| - 1)^2 / (4 * t)) ≤ (|y| + 1)^2 * Real.exp (-|y|^2 / (16 * t)) * Real.exp (1 / t) := by
          intro y
          have h_exp : -max 0 (|y| - 1)^2 / (4 * t) ≤ -|y|^2 / (16 * t) + 1 / t := by
            field_simp;
            cases max_cases ( 0 : ℝ ) ( |y| - 1 ) <;> nlinarith [ abs_nonneg y, sq_nonneg ( |y| - 4 ) ];
          rw [ mul_assoc, ← Real.exp_add ] ; gcongr;
        refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun y => ( |y| + 1 ) ^ 2 * Real.exp ( -|y| ^ 2 / ( 16 * t ) ) * Real.exp ( 1 / t );
        · exact MeasureTheory.Integrable.mul_const ‹_› _;
        · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( by exact Measurable.pow_const ( by exact measurable_norm.add_const _ ) _ ) ( by exact Measurable.exp ( by exact Measurable.div_const ( by exact Measurable.neg ( by exact Measurable.pow_const ( by exact measurable_const.max ( measurable_norm.sub_const _ ) ) _ ) ) _ ) ) );
        · filter_upwards [ ] using fun x => by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact h_integrable x;
      convert h_integrable.comp_sub_left x₀ using 1;
    convert h_integrable.mul_const ( hf_bdd.choose / ( 4 * t ^ 2 ) ) |> ( fun h => h.add ( MeasureTheory.Integrable.mul_const ( show MeasureTheory.Integrable ( fun y => Real.exp ( -max 0 ( |x₀ - y| - 1 ) ^ 2 / ( 4 * t ) ) ) volume from ?_ ) ( hf_bdd.choose * ( 2 * t ) ⁻¹ ) ) ) using 2 ; ring;
    · norm_num ; ring;
    · refine' h_integrable.mono' _ _;
      · exact Measurable.aestronglyMeasurable ( by exact Measurable.exp ( by exact Measurable.div_const ( by exact Measurable.neg ( by exact Measurable.pow_const ( by exact Measurable.max measurable_const ( by exact Measurable.sub ( measurable_norm.comp ( measurable_const.sub measurable_id' ) ) measurable_const ) ) _ ) ) _ ) );
      · filter_upwards [ ] with y using by rw [ Real.norm_of_nonneg ( Real.exp_nonneg _ ) ] ; exact le_mul_of_one_le_left ( Real.exp_nonneg _ ) ( one_le_pow₀ ( by linarith [ abs_nonneg ( x₀ - y ) ] ) ) ;
  · intro y z hz
    have h_bound : |(z - y)^2 / (4 * t^2) - 1 / (2 * t)| ≤ (|x₀ - y| + 1)^2 / (4 * t^2) + 1 / (2 * t) := by
      have h_abs : |z - y| ≤ |x₀ - y| + 1 := by
        cases abs_cases ( z - y ) <;> cases abs_cases ( x₀ - y ) <;> linarith [ abs_lt.mp ( mem_ball_iff_norm.mp hz ) ];
      rw [ abs_le ];
      field_simp;
      constructor <;> nlinarith [ abs_le.mp h_abs, abs_mul_abs_self ( z - y ), abs_mul_abs_self ( x₀ - y ) ];
    have h_exp_bound : Real.exp (-(z - y)^2 / (4 * t)) ≤ Real.exp (-max (0 : ℝ) (|x₀ - y| - 1)^2 / (4 * t)) := by
      norm_num [ div_eq_mul_inv ] at *;
      exact mul_le_mul_of_nonneg_right ( by cases max_cases ( 0 : ℝ ) ( |x₀ - y| - 1 ) <;> cases abs_cases ( x₀ - y ) <;> cases abs_cases ( z - y ) <;> nlinarith [ abs_lt.mp hz ] ) ( by positivity );
    simp_all +decide [ abs_mul, abs_div ];
    exact mul_le_mul ( mul_le_mul h_bound ( Real.exp_le_exp.mpr h_exp_bound ) ( by positivity ) ( by positivity ) ) ( hf_bdd.choose_spec y ) ( by positivity ) ( by positivity )

lemma hasDerivAt_heat_integral_xx (f : ℝ → ℝ) (hf_cont : Continuous f)
    (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) (t : ℝ) (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun z => ∫ y : ℝ, -(z - y) / (2 * t) * exp (-((z - y) ^ 2) / (4 * t)) * f y)
      (∫ y : ℝ, ((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) *
        exp (-((x - y) ^ 2) / (4 * t)) * f y) x := by
  obtain ⟨ bound, hbound₁, hbound₂ ⟩ := heat_deriv_xx_dominated_bound f hf_cont hf_bdd t ht x;
  have := @hasDerivAt_integral_of_dominated_loc_of_deriv_le;
  contrapose! this;
  refine' ⟨ ℝ, inferInstance, MeasureTheory.MeasureSpace.volume, ℝ, inferInstance, ℝ, inferInstance, inferInstance, inferInstance, bound, _, x, Metric.ball x 1, Metric.ball_mem_nhds _ zero_lt_one, _, _, _ ⟩ <;> norm_num;
  use fun z y => -(z - y) / (2 * t) * Real.exp (-(z - y) ^ 2 / (4 * t)) * f y;
  · exact Filter.Eventually.of_forall fun z => Continuous.aestronglyMeasurable ( by continuity );
  · exact integrable_heat_deriv_x_integrand f hf_cont hf_bdd t ht x;
  · refine' ⟨ fun z y => ( ( z - y ) ^ 2 / ( 4 * t ^ 2 ) - 1 / ( 2 * t ) ) * Real.exp ( - ( z - y ) ^ 2 / ( 4 * t ) ) * f y, _, _, hbound₁, _, _ ⟩ <;> norm_num;
    · exact Continuous.aestronglyMeasurable ( by continuity );
    · filter_upwards [ ] with y using fun z hz => by simpa [ abs_mul, abs_div, abs_inv, abs_of_pos ht ] using hbound₂ y z hz;
    · refine' Filter.Eventually.of_forall fun y z hz => _;
      convert HasDerivAt.mul ( HasDerivAt.mul ( HasDerivAt.div_const ( hasDerivAt_id' z |> HasDerivAt.const_sub y ) _ ) ( HasDerivAt.exp ( HasDerivAt.div_const ( HasDerivAt.neg ( hasDerivAt_pow 2 ( z - y ) |> HasDerivAt.comp z <| hasDerivAt_id' z |> HasDerivAt.sub <| hasDerivAt_const _ _ ) ) _ ) ) ) ( hasDerivAt_const _ _ ) using 1 ; ring;
      norm_num ; ring;
    · intro h₁ h₂; convert this _ using 1; convert h₂ using 1; ring;
      · exact funext fun _ => by congr; ext; ring;
      · norm_num [ div_eq_mul_inv ]

/-! ## Time derivative -/

lemma hasDerivAt_heat_prefactor (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => ((4 * π * s)⁻¹) ^ ((1 : ℝ) / 2))
      (-(1 / (2 * t)) * ((4 * π * t)⁻¹) ^ ((1 : ℝ) / 2)) t := by
  convert HasDerivAt.rpow_const ( HasDerivAt.inv ( HasDerivAt.const_mul ( 4 * Real.pi ) ( hasDerivAt_id t ) ) ( by positivity ) ) _ using 1 <;> norm_num [ ht.ne' ];
  rw [ Real.rpow_neg ( by positivity ) ] ; ring;
  rw [ ← Real.sqrt_eq_rpow, ← Real.sqrt_div_self ] ; ring;
  grind

set_option maxHeartbeats 800000 in
lemma hasDerivAt_heat_integral_t (f : ℝ → ℝ) (hf_cont : Continuous f)
    (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) (t : ℝ) (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => ∫ y : ℝ, exp (-((x - y) ^ 2) / (4 * s)) * f y)
      (∫ y : ℝ, (x - y) ^ 2 / (4 * t ^ 2) * exp (-((x - y) ^ 2) / (4 * t)) * f y) t := by
  have h_deriv : HasDerivAt (fun s => ∫ y : ℝ, Real.exp (-((x - y) ^ 2) / (4 * s)) * f y) (∫ y : ℝ, (x - y) ^ 2 / (4 * t ^ 2) * Real.exp (-((x - y) ^ 2) / (4 * t)) * f y) t := by
    have h_bound : ∃ bound : ℝ → ℝ, Integrable bound volume ∧ (∀ y : ℝ, ∀ s ∈ Metric.ball t (t / 2), ‖(x - y) ^ 2 / (4 * s ^ 2) * Real.exp (-((x - y) ^ 2) / (4 * s)) * f y‖ ≤ bound y) := by
      refine' ⟨ fun y => ( x - y ) ^ 2 / ( t ^ 2 ) * Real.exp ( - ( x - y ) ^ 2 / ( 6 * t ) ) * hf_bdd.choose, _, _ ⟩;
      · have h_integrable : Integrable (fun y => (x - y) ^ 2 * Real.exp (-(x - y) ^ 2 / (6 * t))) volume := by
          have := @integrable_rpow_mul_exp_neg_mul_sq;
          convert @this ( 1 / ( 6 * t ) ) ( by positivity ) 2 ( by norm_num ) |> fun h => h.comp_sub_left x using 2 ; norm_num ; ring;
          norm_num;
        convert h_integrable.div_const ( t ^ 2 ) |> fun h => h.mul_const ( hf_bdd.choose ) using 2 ; ring;
      · intro y s hs
        have h_bound : (x - y) ^ 2 / (4 * s ^ 2) ≤ (x - y) ^ 2 / t ^ 2 := by
          gcongr ; nlinarith [ abs_lt.mp ( mem_ball_iff_norm.mp hs ) ]
        have h_exp_bound : Real.exp (-(x - y) ^ 2 / (4 * s)) ≤ Real.exp (-(x - y) ^ 2 / (6 * t)) := by
          norm_num at *;
          rw [ div_le_div_iff₀ ] <;> nlinarith [ abs_lt.mp hs, sq_nonneg ( x - y ) ]
        have h_abs : |f y| ≤ hf_bdd.choose := by
          exact hf_bdd.choose_spec y
        simp [h_bound, h_exp_bound, h_abs];
        gcongr
    obtain ⟨ bound, h_bound_integrable, h_bound ⟩ := h_bound;
    have h_deriv : ∀ᵐ y ∂volume, ∀ s ∈ Metric.ball t (t / 2), HasDerivAt (fun s => Real.exp (-((x - y) ^ 2) / (4 * s)) * f y) ((x - y) ^ 2 / (4 * s ^ 2) * Real.exp (-((x - y) ^ 2) / (4 * s)) * f y) s := by
      filter_upwards [ ] with y s hs;
      convert HasDerivAt.mul ( HasDerivAt.exp ( HasDerivAt.div ( hasDerivAt_const _ _ ) ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( hasDerivAt_id s ) ) _ ) ) ( hasDerivAt_const _ _ ) using 1 <;> norm_num ; ring;
      · norm_num;
      · linarith [ abs_lt.mp ( mem_ball_iff_norm.mp hs ) ];
    have := @hasDerivAt_integral_of_dominated_loc_of_deriv_le;
    specialize this ( Metric.ball_mem_nhds t ( half_pos ht ) ) ( Filter.Eventually.of_forall fun s => ?_ ) ( ?_ ) ( ?_ ) ( ?_ ) h_bound_integrable h_deriv;
    · exact Continuous.aestronglyMeasurable ( by exact Continuous.mul ( Real.continuous_exp.comp <| by continuity ) hf_cont );
    · exact integrable_heat_integrand f hf_cont hf_bdd t ht x;
    · exact Continuous.aestronglyMeasurable ( by exact Continuous.mul ( Continuous.mul ( Continuous.div_const ( by continuity ) _ ) ( Real.continuous_exp.comp ( by continuity ) ) ) hf_cont );
    · exact Filter.Eventually.of_forall fun y s hs => h_bound y s hs;
    · exact this.2;
  exact h_deriv

/- To apply the dominated convergence theorem, we need to find a dominating function for the derivative of the integrand.
  have h_dominate : ∃ bound : ℝ → ℝ, Integrable bound volume ∧ ∀ y ∈ Set.univ, ∀ s ∈ Set.Ioo (t / 2) (3 * t / 2), ‖deriv (fun s => Real.exp (-(x - y) ^ 2 / (4 * s))) s * f y‖ ≤ bound y := by
    -- The derivative of the integrand is bounded by $(x - y)^2 / (4 * (t / 2)^2) * \exp(-(x - y)^2 / (4 * (3 * t / 2))) * M$.
    use fun y => (x - y)^2 / (4 * (t / 2)^2) * Real.exp (-(x - y)^2 / (4 * (3 * t / 2))) * hf_bdd.choose;
    constructor;
    · have h_integrable : Integrable (fun y => (x - y)^2 * Real.exp (-(x - y)^2 / (4 * (3 * t / 2)))) volume := by
        have := @integrable_rpow_mul_exp_neg_mul_sq;
        specialize @this ( 1 / ( 4 * ( 3 * t / 2 ) ) ) ( by positivity ) 2 ; norm_num at this;
        convert this.comp_sub_left x using 2 ; ring;
      convert h_integrable.div_const ( 4 * ( t / 2 ) ^ 2 ) |> fun h => h.mul_const ( hf_bdd.choose ) using 2 ; ring;
    · intro y hy s hs; rw [ Real.norm_eq_abs, abs_mul ] ; gcongr;
      · norm_num [ div_eq_mul_inv, differentiableAt_inv, show s ≠ 0 by linarith [ hs.1 ] ];
        rw [ mul_comm ] ; gcongr;
        · linarith [ hs.1 ];
        · rw [ inv_mul_eq_div, mul_div, div_le_iff₀ ] <;> nlinarith [ hs.1, hs.2, mul_inv_cancel₀ ( ne_of_gt ht ), mul_inv_cancel₀ ( ne_of_gt ( by linarith [ hs.1 ] : 0 < s ) ) ];
      · exact hf_bdd.choose_spec y;
  -- Apply the dominated convergence theorem to interchange the limit and the integral.
  have h_dominated : Filter.Tendsto (fun h => ∫ y, (Real.exp (-(x - y) ^ 2 / (4 * (t + h))) - Real.exp (-(x - y) ^ 2 / (4 * t))) / h * f y) (nhdsWithin 0 {0}ᶜ) (nhds (∫ y, (x - y) ^ 2 / (4 * t ^ 2) * Real.exp (-(x - y) ^ 2 / (4 * t)) * f y)) := by
    refine' MeasureTheory.tendsto_integral_filter_of_dominated_convergence _ _ _ _ _;
    use h_dominate.choose;
    · exact Filter.Eventually.of_forall fun n => Continuous.aestronglyMeasurable ( by exact Continuous.mul ( Continuous.div_const ( by exact Continuous.sub ( Real.continuous_exp.comp <| by exact Continuous.div_const ( by continuity ) _ ) <| Real.continuous_exp.comp <| by exact Continuous.div_const ( by continuity ) _ ) _ ) hf_cont );
    · rw [ eventually_nhdsWithin_iff ];
      rw [ Metric.eventually_nhds_iff ];
      refine' ⟨ t / 2, half_pos ht, fun y hy hy' => Filter.Eventually.of_forall fun a => _ ⟩;
      -- Apply the mean value theorem to the interval $[t, t + y]$.
      obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo (min t (t + y)) (max t (t + y)), deriv (fun s => Real.exp (-(x - a) ^ 2 / (4 * s))) c = (Real.exp (-(x - a) ^ 2 / (4 * (t + y))) - Real.exp (-(x - a) ^ 2 / (4 * t))) / y := by
        cases max_cases t ( t + y ) <;> cases min_cases t ( t + y ) <;> simp_all +decide;
        · have := exists_deriv_eq_slope ( f := fun s => Real.exp ( - ( x - a ) ^ 2 / ( 4 * s ) ) ) ( show t + y < t by linarith );
          exact this ( continuousOn_of_forall_continuousAt fun s hs => ContinuousAt.rexp <| ContinuousAt.div continuousAt_const ( continuousAt_const.mul continuousAt_id ) <| by linarith [ hs.1, hs.2, abs_lt.mp hy ] ) ( fun s hs => DifferentiableAt.differentiableWithinAt <| by exact DifferentiableAt.exp <| DifferentiableAt.div ( differentiableAt_const _ ) ( differentiableAt_id.const_mul _ ) <| by linarith [ hs.1, hs.2, abs_lt.mp hy ] ) |> fun ⟨ c, hc₁, hc₂ ⟩ => ⟨ c, hc₁, by rw [ hc₂ ] ; rw [ ← neg_div_neg_eq ] ; ring ⟩;
        · have := exists_deriv_eq_slope ( f := fun s => Real.exp ( - ( x - a ) ^ 2 / ( 4 * s ) ) ) ( show t < t + y by linarith );
          exact this ( continuousOn_of_forall_continuousAt fun s hs => ContinuousAt.rexp <| ContinuousAt.div continuousAt_const ( continuousAt_const.mul continuousAt_id ) <| by linarith [ hs.1 ] ) ( fun s hs => DifferentiableAt.differentiableWithinAt <| by exact DifferentiableAt.exp <| DifferentiableAt.div ( differentiableAt_const _ ) ( differentiableAt_id.const_mul _ ) <| by linarith [ hs.1 ] ) |> fun ⟨ c, hc₁, hc₂ ⟩ => ⟨ c, hc₁, by simpa using hc₂ ⟩;
      have := h_dominate.choose_spec.2 a trivial c ⟨ by cases max_cases t ( t + y ) <;> cases min_cases t ( t + y ) <;> linarith [ hc.1.1, hc.1.2, abs_lt.mp hy ], by cases max_cases t ( t + y ) <;> cases min_cases t ( t + y ) <;> linarith [ hc.1.1, hc.1.2, abs_lt.mp hy ] ⟩ ; aesop;
    · exact h_dominate.choose_spec.1;
    · refine' Filter.Eventually.of_forall fun y => _;
      have h_deriv : HasDerivAt (fun s => Real.exp (-(x - y) ^ 2 / (4 * s))) ((x - y) ^ 2 / (4 * t ^ 2) * Real.exp (-(x - y) ^ 2 / (4 * t))) t := by
        convert HasDerivAt.exp ( HasDerivAt.div ( hasDerivAt_const _ _ ) ( HasDerivAt.const_mul 4 ( hasDerivAt_id t ) ) _ ) using 1 <;> norm_num [ ht.ne' ] ; ring;
      simpa [ div_eq_inv_mul ] using h_deriv.tendsto_slope_zero.mul_const ( f y );
  rw [ hasDerivAt_iff_tendsto_slope_zero ];
  refine' h_dominated.congr' _;
  rw [ Filter.EventuallyEq, eventually_nhdsWithin_iff ];
  filter_upwards [ Metric.ball_mem_nhds _ ( show 0 < t / 2 by positivity ) ] with h hh hh' ; rw [ ← MeasureTheory.integral_sub ];
  · simp +decide [ div_eq_inv_mul, mul_sub, sub_mul, mul_assoc, mul_comm, mul_left_comm, ← MeasureTheory.integral_const_mul ];
  · refine' integrable_heat_integrand f hf_cont hf_bdd ( t + h ) ( by linarith [ abs_lt.mp ( mem_ball_zero_iff.mp hh ) ] ) x;
  · exact integrable_heat_integrand f hf_cont hf_bdd t ht x
-/

/-
Old proof attempt for hasDerivAt_heat_integral_t:
  -- To apply the dominated convergence theorem, we need to show that the derivative of the integrand is bounded.
  have h_deriv_bound : ∃ C > 0, ∀ s ∈ Set.Ioo (t / 2) (t * 3 / 2), ∀ y, abs ((deriv (fun s => Real.exp (-(x - y) ^ 2 / (4 * s))) s) * f y) ≤ C * (1 + (x - y) ^ 2) * Real.exp (-(x - y) ^ 2 / (6 * t)) := by
    -- By definition of $f$, we know that $|f(y)| \leq M$ for some $M > 0$.
    obtain ⟨M, hM⟩ : ∃ M > 0, ∀ y, abs (f y) ≤ M := by
      exact ⟨ Max.max hf_bdd.choose 1, by positivity, fun y => le_trans ( hf_bdd.choose_spec y ) ( le_max_left _ _ ) ⟩;
    -- By definition of $f$, we know that $|deriv (fun s => Real.exp (-(x - y) ^ 2 / (4 * s))) s| \leq \frac{(x - y) ^ 2}{4s ^ 2} e^{-(x - y) ^ 2 / (4s)}$.
    have h_deriv_bound : ∀ s ∈ Set.Ioo (t / 2) (t * 3 / 2), ∀ y, abs (deriv (fun s => Real.exp (-(x - y) ^ 2 / (4 * s))) s) ≤ (x - y) ^ 2 / (4 * (t / 2) ^ 2) * Real.exp (-(x - y) ^ 2 / (4 * s)) := by
      intro s hs y; norm_num [ mul_comm, div_eq_mul_inv, differentiableAt_inv, show s ≠ 0 by linarith [ hs.1 ] ] ; ring_nf; norm_num [ abs_mul, abs_inv, abs_of_pos, ht, hs.1, hs.2 ] ;
      field_simp;
      rw [ div_le_iff₀ ] <;> nlinarith [ hs.1, hs.2, pow_pos ht 2, pow_pos ( sub_pos.mpr hs.1 ) 2, pow_pos ( sub_pos.mpr hs.2 ) 2, mul_le_mul_of_nonneg_left hs.1.le ( sq_nonneg ( x - y ) ), mul_le_mul_of_nonneg_left hs.2.le ( sq_nonneg ( x - y ) ) ];
    -- By combining the bounds, we get the desired inequality.
    have h_combined_bound : ∀ s ∈ Set.Ioo (t / 2) (t * 3 / 2), ∀ y, abs (deriv (fun s => Real.exp (-(x - y) ^ 2 / (4 * s))) s * f y) ≤ (x - y) ^ 2 / (4 * (t / 2) ^ 2) * M * Real.exp (-(x - y) ^ 2 / (6 * t)) := by
      intros s hs y
      have h_exp_bound : Real.exp (-(x - y) ^ 2 / (4 * s)) ≤ Real.exp (-(x - y) ^ 2 / (6 * t)) := by
        exact Real.exp_le_exp.mpr ( by rw [ div_le_div_iff₀ ] <;> nlinarith [ hs.1, hs.2 ] );
      rw [ abs_mul ];
      exact le_trans ( mul_le_mul ( h_deriv_bound s hs y ) ( hM.2 y ) ( by positivity ) ( by positivity ) ) ( by nlinarith [ show 0 ≤ ( x - y ) ^ 2 / ( 4 * ( t / 2 ) ^ 2 ) * M by exact mul_nonneg ( div_nonneg ( sq_nonneg _ ) ( by positivity ) ) hM.1.le ] );
    refine' ⟨ M / ( 4 * ( t / 2 ) ^ 2 ), div_pos hM.1 ( by positivity ), fun s hs y => le_trans ( h_combined_bound s hs y ) _ ⟩ ; ring_nf ; norm_num [ ht.ne' ];
    exact mul_nonneg ( mul_nonneg ( inv_nonneg.2 ( sq_nonneg _ ) ) hM.1.le ) ( Real.exp_nonneg _ );
  -- Apply the dominated convergence theorem to interchange the derivative and the integral.
  have h_dominated_convergence : Filter.Tendsto (fun h => ∫ y, (Real.exp (-(x - y) ^ 2 / (4 * (t + h))) - Real.exp (-(x - y) ^ 2 / (4 * t))) / h * f y) (nhdsWithin 0 {0}ᶜ) (nhds (∫ y, (x - y) ^ 2 / (4 * t ^ 2) * Real.exp (-(x - y) ^ 2 / (4 * t)) * f y)) := by
    refine' MeasureTheory.tendsto_integral_filter_of_dominated_convergence _ _ _ _ _;
    use fun y => h_deriv_bound.choose * ( 1 + ( x - y ) ^ 2 ) * Real.exp ( - ( x - y ) ^ 2 / ( 6 * t ) );
    · exact Filter.Eventually.of_forall fun n => Continuous.aestronglyMeasurable ( by continuity );
    · rw [ eventually_nhdsWithin_iff ];
      rw [ Metric.eventually_nhds_iff ];
      refine' ⟨ t / 2, half_pos ht, fun y hy hy' => Filter.Eventually.of_forall fun a => _ ⟩;
      -- Apply the mean value theorem to the interval $[t, t + y]$.
      obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo (min t (t + y)) (max t (t + y)), deriv (fun s => Real.exp (-(x - a) ^ 2 / (4 * s))) c = (Real.exp (-(x - a) ^ 2 / (4 * (t + y))) - Real.exp (-(x - a) ^ 2 / (4 * t))) / y := by
        cases max_cases t ( t + y ) <;> cases min_cases t ( t + y ) <;> simp_all +decide;
        · have := exists_deriv_eq_slope ( f := fun s => Real.exp ( - ( x - a ) ^ 2 / ( 4 * s ) ) ) ( show t + y < t by linarith );
          exact this ( continuousOn_of_forall_continuousAt fun s hs => ContinuousAt.rexp <| ContinuousAt.div continuousAt_const ( continuousAt_const.mul continuousAt_id ) <| by linarith [ hs.1, hs.2, abs_lt.mp hy ] ) ( fun s hs => DifferentiableAt.differentiableWithinAt <| by exact DifferentiableAt.exp <| DifferentiableAt.div ( differentiableAt_const _ ) ( differentiableAt_id.const_mul _ ) <| by linarith [ hs.1, hs.2, abs_lt.mp hy ] ) |> fun ⟨ c, hc₁, hc₂ ⟩ => ⟨ c, hc₁, by rw [ hc₂ ] ; rw [ ← neg_div_neg_eq ] ; ring ⟩;
        · have := exists_deriv_eq_slope ( f := fun s => Real.exp ( - ( x - a ) ^ 2 / ( 4 * s ) ) ) ( show t < t + y by linarith );
          exact this ( continuousOn_of_forall_continuousAt fun s hs => ContinuousAt.rexp <| ContinuousAt.div continuousAt_const ( continuousAt_const.mul continuousAt_id ) <| by linarith [ hs.1 ] ) ( fun s hs => DifferentiableAt.differentiableWithinAt <| by exact DifferentiableAt.exp <| DifferentiableAt.div ( differentiableAt_const _ ) ( differentiableAt_id.const_mul _ ) <| by linarith [ hs.1 ] ) |> fun ⟨ c, hc₁, hc₂ ⟩ => ⟨ c, hc₁, by simpa using hc₂ ⟩;
      rw [ ← hc.2 ];
      exact h_deriv_bound.choose_spec.2 c ⟨ by cases max_cases t ( t + y ) <;> cases min_cases t ( t + y ) <;> linarith [ hc.1.1, hc.1.2, abs_lt.mp hy ], by cases max_cases t ( t + y ) <;> cases min_cases t ( t + y ) <;> linarith [ hc.1.1, hc.1.2, abs_lt.mp hy ] ⟩ a;
    · have h_integrable : Integrable (fun y => (1 + y ^ 2) * Real.exp (-y ^ 2 / (6 * t))) volume := by
        have := @integrable_rpow_mul_exp_neg_mul_sq;
        convert MeasureTheory.Integrable.add ( this ( show 0 < 1 / ( 6 * t ) by positivity ) ( show -1 < 0 by norm_num ) ) ( this ( show 0 < 1 / ( 6 * t ) by positivity ) ( show -1 < 2 by norm_num ) ) using 2 ; ring;
        norm_num ; ring;
      convert h_integrable.const_mul ( h_deriv_bound.choose ) |> fun h => h.comp_sub_left x using 2 ; ring;
    · refine' Filter.Eventually.of_forall fun y => _;
      have h_deriv : HasDerivAt (fun s => Real.exp (-(x - y) ^ 2 / (4 * s))) ((x - y) ^ 2 / (4 * t ^ 2) * Real.exp (-(x - y) ^ 2 / (4 * t))) t := by
        convert HasDerivAt.exp ( HasDerivAt.div ( hasDerivAt_const _ _ ) ( HasDerivAt.const_mul 4 ( hasDerivAt_id t ) ) _ ) using 1 <;> norm_num [ ht.ne' ] ; ring;
      simpa [ div_eq_inv_mul ] using h_deriv.tendsto_slope_zero.mul_const ( f y );
  rw [ hasDerivAt_iff_tendsto_slope_zero ];
  refine' h_dominated_convergence.congr' _;
  rw [ Filter.EventuallyEq, eventually_nhdsWithin_iff ];
  rw [ Metric.eventually_nhds_iff ];
  refine' ⟨ t / 2, half_pos ht, fun y hy hy' => _ ⟩ ; rw [ ← MeasureTheory.integral_sub ];
  · simp +decide [ div_eq_inv_mul, mul_sub, sub_mul, mul_assoc, mul_comm, mul_left_comm, ← MeasureTheory.integral_const_mul ];
  · refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun z => Real.exp ( - ( x - z ) ^ 2 / ( 4 * ( t + y ) ) ) * hf_bdd.choose;
    · refine' MeasureTheory.Integrable.mul_const _ _;
      simpa [ div_eq_inv_mul ] using ( integrable_exp_neg_mul_sq ( by norm_num; linarith [ abs_lt.mp hy ] ) ) |> fun h => h.comp_sub_left x;
    · exact Continuous.aestronglyMeasurable ( by continuity );
    · filter_upwards [ ] using fun z => by simpa [ abs_mul ] using mul_le_mul_of_nonneg_left ( hf_bdd.choose_spec z ) ( Real.exp_pos _ |> le_of_lt ) ;
  · sorry
-/
lemma heat_time_deriv_eq_space_deriv (f : ℝ → ℝ) (hf_cont : Continuous f)
    (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) (t : ℝ) (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => heatSolution' f s x)
      (((4 * π * t)⁻¹) ^ ((1 : ℝ) / 2) *
        ∫ y : ℝ, ((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) *
          exp (-((x - y) ^ 2) / (4 * t)) * f y) t := by
  have h_deriv : HasDerivAt (fun s => ((4 * Real.pi * s)⁻¹) ^ ((1 : ℝ) / 2) * ∫ y : ℝ, Real.exp (-((x - y) ^ 2) / (4 * s)) * f y) ((4 * Real.pi * t)⁻¹ ^ (1 / 2 : ℝ) * ∫ y : ℝ, ((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * Real.exp (-(x - y) ^ 2 / (4 * t)) * f y) t := by
    convert HasDerivAt.mul ( hasDerivAt_heat_prefactor t ht ) ( hasDerivAt_heat_integral_t f hf_cont hf_bdd t ht x ) using 1;
    simp +decide [ sub_mul, mul_assoc, MeasureTheory.integral_const_mul ];
    rw [ MeasureTheory.integral_sub ];
    · norm_num [ MeasureTheory.integral_const_mul ] ; ring;
    · have := integrable_heat_deriv_xx_integrand f hf_cont hf_bdd t ht x;
      convert this.add ( show Integrable ( fun y => ( 1 / ( 2 * t ) ) * Real.exp ( - ( x - y ) ^ 2 / ( 4 * t ) ) * f y ) volume from ?_ ) using 2 ; ring;
      · norm_num ; ring;
      · have := integrable_heat_integrand f hf_cont hf_bdd t ht x;
        simpa only [ mul_assoc ] using this.const_mul _;
    · exact MeasureTheory.Integrable.const_mul ( MeasureTheory.Integrable.const_mul ( integrable_heat_integrand f hf_cont hf_bdd t ht x ) _ ) _;
  refine' h_deriv.congr_of_eventuallyEq _;
  filter_upwards [ lt_mem_nhds ht ] with s hs using if_pos hs

/-! ## Initial condition -/

lemma heat_initial_condition (f : ℝ → ℝ) (hf_cont : Continuous f)
    (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) (x : ℝ) :
    Tendsto (fun t : ℝ => heatSolution' f t x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f x)) := by
  -- By definition of $heatSolution'$, we have
  have h_def : ∀ t > 0, heatSolution' f t x = (1 / Real.sqrt (4 * Real.pi * t)) * ∫ y : ℝ, Real.exp (-((x - y) ^ 2) / (4 * t)) * f y := by
    unfold heatSolution';
    norm_num [ ← Real.sqrt_eq_rpow ];
    intro t ht; rw [ if_pos ht ] ; rw [ ← Real.sqrt_inv ] ; ring;
  -- Rewrite the integral using the substitution $y = x + \sqrt{4t}z$.
  have h_subst : ∀ t > 0, heatSolution' f t x = (1 / Real.sqrt Real.pi) * ∫ z : ℝ, Real.exp (-z ^ 2) * f (x + Real.sqrt (4 * t) * z) := by
    intro t ht
    rw [h_def t ht]
    have h_subst_step : ∫ y : ℝ, Real.exp (-((x - y) ^ 2) / (4 * t)) * f y = ∫ z : ℝ, Real.exp (-z ^ 2) * f (x + Real.sqrt (4 * t) * z) * Real.sqrt (4 * t) := by
      have h_subst_step : ∀ {g : ℝ → ℝ}, ∫ y : ℝ, g y = ∫ z : ℝ, g (x + Real.sqrt (4 * t) * z) * Real.sqrt (4 * t) := by
        intro g; rw [ MeasureTheory.integral_mul_const ] ; rw [ MeasureTheory.Measure.integral_comp_mul_left ( fun z => g ( x + z ) ) ] ; norm_num [ ht.le, ht.ne' ] ;
        rw [ abs_of_nonneg ( Real.sqrt_nonneg _ ), MeasureTheory.integral_add_left_eq_self ] ; ring ; norm_num [ ht.le, ht.ne' ];
      convert h_subst_step using 3 ; ring;
      grind;
    rw [ h_subst_step, MeasureTheory.integral_mul_const ] ; norm_num [ ht.le ] ; ring;
    rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.sqrt_pos.mpr ht ) ), one_mul ];
  -- By the dominated convergence theorem, we can interchange the limit and the integral.
  have h_dominated : Filter.Tendsto (fun t => ∫ z : ℝ, Real.exp (-z ^ 2) * f (x + Real.sqrt (4 * t) * z)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ z : ℝ, Real.exp (-z ^ 2) * f x)) := by
    refine' MeasureTheory.tendsto_integral_filter_of_dominated_convergence _ _ _ _ _;
    refine' fun z => Real.exp ( -z ^ 2 ) * hf_bdd.choose;
    · exact Filter.eventually_of_mem self_mem_nhdsWithin fun t ht => Continuous.aestronglyMeasurable ( by continuity );
    · filter_upwards [ self_mem_nhdsWithin ] with t ht using Filter.Eventually.of_forall fun z => by simpa [ abs_mul ] using mul_le_mul_of_nonneg_left ( hf_bdd.choose_spec _ ) ( by positivity ) ;
    · exact MeasureTheory.Integrable.mul_const ( by simpa using ( integrable_exp_neg_mul_sq ( zero_lt_one' ℝ ) ) ) _;
    · exact Filter.Eventually.of_forall fun z => tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num );
  rw [ Filter.tendsto_congr' ( Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun t ht => by rw [ h_subst t ht ] ) ] ; convert h_dominated.const_mul ( 1 / Real.sqrt Real.pi ) using 2 ; norm_num [ MeasureTheory.integral_mul_const ] ; ring;
  rw [ show ∫ a : ℝ, Real.exp ( -a ^ 2 ) = Real.sqrt Real.pi by simpa using integral_gaussian ( 1 : ℝ ) ] ; norm_num [ Real.sqrt_ne_zero'.mpr Real.pi_pos ]

end Submission.Helpers