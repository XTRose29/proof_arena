import Submission.FourierEstimates

open LeanEval.Dynamics
open MeasureTheory
open scoped ContDiff

namespace Submission.Majorant

noncomputable section

/-- Uniform derivative bounds for reciprocal on the half-line used by the
automatic-reducibility twist weight. -/
theorem norm_iteratedFDeriv_inv_le (n : ℕ) {x : ℝ}
    (hx : (1 : ℝ) / 4 ≤ x) :
    ‖iteratedFDeriv ℝ n Inv.inv x‖ ≤
      4 * weight 1 n * 4 ^ n := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hinv : x⁻¹ ≤ (4 : ℝ) := by
    rw [inv_le_iff_one_le_mul₀' hxpos]
    nlinarith
  have hz : |x ^ (-1 - n : ℤ)| = x⁻¹ * (x⁻¹) ^ n := by
    rw [abs_of_pos (zpow_pos hxpos _)]
    have hexp : (-1 - (n : ℤ)) = Int.negSucc n := by omega
    rw [hexp, zpow_negSucc, inv_pow, pow_succ]
    ring
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedDeriv_eq_iterate, iter_deriv_inv]
  have hfac := factorial_cast_le_weight_one n
  calc
    ‖(-1 : ℝ) ^ n * n.factorial * x ^ (-1 - n : ℤ)‖ =
        (n.factorial : ℝ) * x⁻¹ * (x⁻¹) ^ n := by
      simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow,
        Real.norm_eq_abs]
      rw [abs_of_nonneg (Nat.cast_nonneg _), hz]
      ring
    _ ≤ weight 1 n * 4 * 4 ^ n := by
      apply mul_le_mul
      · exact mul_le_mul hfac hinv (inv_nonneg.mpr hxpos.le)
          (weight_nonneg 1 n)
      · exact pow_le_pow_left₀ (inv_nonneg.mpr hxpos.le) hinv n
      · exact pow_nonneg (inv_nonneg.mpr hxpos.le) n
      · exact mul_nonneg (weight_nonneg 1 n) (by norm_num)
    _ = 4 * weight 1 n * 4 ^ n := by
      ring

/-- Reciprocal preserves a derivative majorant when the function stays
uniformly away from zero. -/
theorem Majorized.inv_of_ge_quarter {r : ℕ} {B S : ℝ} {g : ℝ → ℝ}
    (hg : Majorized r B S g) (hgs : ContDiff ℝ ∞ g)
    (hS : 0 ≤ S) (hpos : ∀ t, (1 : ℝ) / 4 ≤ g t) :
    Majorized (r + 2) 4 (4 * max 1 B * S) (fun t => (g t)⁻¹) := by
  intro n t
  let B₀ := max 1 B
  have hB₀ : 1 ≤ B₀ := le_max_left _ _
  have hBB₀ : B ≤ B₀ := le_max_right _ _
  have hrange : Set.range g ⊆ Set.Ioi (0 : ℝ) := by
    rintro _ ⟨x, rfl⟩
    exact lt_of_lt_of_le (by norm_num) (hpos x)
  have hinv : ContDiffOn ℝ ∞ Inv.inv (Set.Ioi (0 : ℝ)) :=
    (contDiffOn_inv (𝕜 := ℝ)).mono fun _ hx => hx.ne'
  have hC (i : ℕ) (hin : i ≤ n) :
      ‖iteratedFDerivWithin ℝ i Inv.inv (Set.Ioi (0 : ℝ)) (g t)‖ ≤
        4 * weight 1 n * 4 ^ n := by
    rw [iteratedFDerivWithin_of_isOpen i isOpen_Ioi (hrange ⟨t, rfl⟩)]
    apply (norm_iteratedFDeriv_inv_le i (hpos t)).trans
    have hw : weight 1 i ≤ weight 1 n := weight_order_mono hin
    have hp : (4 : ℝ) ^ i ≤ 4 ^ n :=
      pow_le_pow_right₀ (by norm_num) hin
    calc
      4 * weight 1 i * 4 ^ i = 4 * (weight 1 i * 4 ^ i) := by ring
      _ ≤ 4 * (weight 1 n * 4 ^ n) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul hw hp (pow_nonneg (by norm_num) i) (weight_nonneg 1 n))
          (by norm_num)
      _ = 4 * weight 1 n * 4 ^ n := by ring
  have hD (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDeriv ℝ i g t‖ ≤
        (B₀ * S * 2 ^ (r * n)) ^ i := by
    apply (hg i t).trans
    have hBpow : B ≤ B₀ ^ i := by
      calc
        B ≤ B₀ := hBB₀
        _ = B₀ ^ 1 := by ring
        _ ≤ B₀ ^ i := pow_le_pow_right₀ hB₀ hi
    have hweight : weight r i ≤ (2 ^ (r * n) : ℝ) ^ i := by
      unfold weight
      rw [← pow_mul]
      apply pow_le_pow_right₀ (by norm_num)
      have hi2 := Nat.mul_le_mul_left r (Nat.mul_le_mul_right i hin)
      simpa only [pow_two, mul_assoc] using hi2
    calc
      B * weight r i * S ^ i ≤
          B₀ ^ i * (2 ^ (r * n) : ℝ) ^ i * S ^ i := by
        gcongr
        exact weight_nonneg r i
      _ = (B₀ * S * 2 ^ (r * n)) ^ i := by
        rw [mul_pow, mul_pow]
        ring
  have hcomp := norm_iteratedFDeriv_comp_le' hrange
    isOpen_Ioi.uniqueDiffOn hinv hgs
    (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top)) t hC hD
  change ‖iteratedFDeriv ℝ n (Inv.inv ∘ g) t‖ ≤ _
  apply hcomp.trans
  have hfac : (n.factorial : ℝ) ≤ weight 1 n :=
    factorial_cast_le_weight_one n
  have hweights : weight 1 n * weight 1 n * weight r n =
      weight (r + 2) n := by
    rw [show r + 2 = 1 + 1 + r by omega, weight_add, weight_add]
  rw [mul_pow, ← weight_as_pow r n]
  calc
    (n.factorial : ℝ) * (4 * weight 1 n * 4 ^ n) *
        ((B₀ * S) ^ n * weight r n) =
      4 * ((n.factorial : ℝ) * weight 1 n * weight r n) *
        ((4 * B₀ * S) ^ n) := by
      rw [mul_pow, mul_pow]
      ring
    _ ≤ 4 * (weight 1 n * weight 1 n * weight r n) *
        ((4 * B₀ * S) ^ n) := by
      have hscale : 0 ≤ 4 * weight 1 n * weight r n *
          (4 * B₀ * S) ^ n := by
        exact mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) (weight_nonneg 1 n))
            (weight_nonneg r n))
          (pow_nonneg
            (mul_nonneg
              (mul_nonneg (by norm_num) (zero_le_one.trans hB₀)) hS) n)
      calc
        4 * ((n.factorial : ℝ) * weight 1 n * weight r n) *
              (4 * B₀ * S) ^ n =
            (n.factorial : ℝ) *
              (4 * weight 1 n * weight r n *
                (4 * B₀ * S) ^ n) := by ring
        _ ≤ weight 1 n *
              (4 * weight 1 n * weight r n *
                (4 * B₀ * S) ^ n) :=
          mul_le_mul_of_nonneg_right hfac hscale
        _ = 4 * (weight 1 n * weight 1 n * weight r n) *
              (4 * B₀ * S) ^ n := by ring
    _ = 4 * weight (r + 2) n * (4 * max 1 B * S) ^ n := by
      rw [hweights]

/-- A fixed positive Fourier-division constant associated to a Diophantine
rotation. -/
def solveConstant (α : ℝ) (hα : IsDiophantine α) : ℝ :=
  (exists_solve_majorant_constant hα).choose

theorem solveConstant_pos (α : ℝ) (hα : IsDiophantine α) :
    0 < solveConstant α hα :=
  (exists_solve_majorant_constant hα).choose_spec.1

theorem solve_majorized {α : ℝ} (hα : IsDiophantine α)
    {s : ℕ} {A R : ℝ} {g : ℝ → ℝ}
    (hg : Majorized s A R g) (hgs : ContDiff ℝ ∞ g)
    (hper : Function.Periodic g 1) (hA : 0 ≤ A) (hR : 0 ≤ R) :
    Majorized s
      (solveConstant α hα * A * 2 ^ (16 * s) * R ^ 4)
      ((2 * Real.pi) * 2 ^ (8 * s) * R)
      (Cohomological.solve α g) :=
  (exists_solve_majorant_constant hα).choose_spec.2
    hg hgs hper hA hR

theorem solveForward_majorized {α : ℝ} (hα : IsDiophantine α)
    {s : ℕ} {A R : ℝ} {g : ℝ → ℝ}
    (hg : Majorized s A R g) (hgs : ContDiff ℝ ∞ g)
    (hper : Function.Periodic g 1) (hA : 0 ≤ A) (hR : 0 ≤ R) :
    Majorized s
      (2 * (solveConstant α hα * A * 2 ^ (16 * s) * R ^ 4))
      ((2 * Real.pi) * 2 ^ (8 * s) * R)
      (Newton.solveForward α g) := by
  let H := solveConstant α hα * A * 2 ^ (16 * s) * R ^ 4
  let T := (2 * Real.pi) * 2 ^ (8 * s) * R
  have hsolve : Majorized s H T (Cohomological.solve α g) :=
    solve_majorized hα hg hgs hper hA hR
  have hsmooth := Cohomological.solve_contDiff hα hgs hper
  have hshiftSmooth : ContDiff ℝ ∞
      (fun t => Cohomological.solve α g (t - α)) :=
    hsmooth.comp (contDiff_id.sub contDiff_const)
  change Majorized s (2 * H) T
    (fun t => Cohomological.solve α g t -
      Cohomological.solve α g (t - α))
  simpa only [H, T, two_mul] using
    hsolve.sub (hsolve.shift_sub α) hsmooth hshiftSmooth

theorem solveBackward_majorized {α : ℝ} (hα : IsDiophantine α)
    {s : ℕ} {A R : ℝ} {g : ℝ → ℝ}
    (hg : Majorized s A R g) (hgs : ContDiff ℝ ∞ g)
    (hper : Function.Periodic g 1) (hA : 0 ≤ A) (hR : 0 ≤ R) :
    Majorized s
      (2 * (solveConstant α hα * A * 2 ^ (16 * s) * R ^ 4))
      ((2 * Real.pi) * 2 ^ (8 * s) * R)
      (Newton.solveBackward α g) := by
  let H := solveConstant α hα * A * 2 ^ (16 * s) * R ^ 4
  let T := (2 * Real.pi) * 2 ^ (8 * s) * R
  have hsolve : Majorized s H T (Cohomological.solve α g) :=
    solve_majorized hα hg hgs hper hA hR
  have hsmooth := Cohomological.solve_contDiff hα hgs hper
  have hshiftSmooth : ContDiff ℝ ∞
      (fun t => Cohomological.solve α g (t + α)) :=
    hsmooth.comp (contDiff_id.add contDiff_const)
  change Majorized s (2 * H) T
    (fun t => Cohomological.solve α g (t + α) -
      Cohomological.solve α g t)
  simpa only [H, T, two_mul] using
    (hsolve.shift α).sub hsolve hshiftSmooth hsmooth

theorem abs_periodMean_le {s : ℕ} {A R : ℝ} {g : ℝ → ℝ}
    (hg : Majorized s A R g) : |Nonlinear.periodMean g| ≤ A := by
  have hbound (t : ℝ) : ‖g t‖ ≤ A := by
    have h := hg 0 t
    norm_num [norm_iteratedFDeriv_eq_norm_iteratedDeriv, weight] at h
    exact h
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := (1 : ℝ)) (fun t _ => hbound t)
  simpa only [Nonlinear.periodMean, Real.norm_eq_abs, sub_zero,
    abs_one, mul_one] using h

/-- Positive-order derivative control with one power of the analytic radius
split off as a persistent derivative-size parameter. -/
def DerivativeMajorized (s : ℕ) (W R : ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ n, 1 ≤ n → ∀ t,
    ‖iteratedFDeriv ℝ n g t‖ ≤ W * weight s n * R ^ (n - 1)

theorem derivativeMajorized_zero (s : ℕ) (R : ℝ) :
    DerivativeMajorized s 0 R (fun _ : ℝ => 0) := by
  intro n _ t
  simp

theorem Majorized.derivativeMajorized {s : ℕ} {A R : ℝ} {g : ℝ → ℝ}
    (hg : Majorized s A R g) : DerivativeMajorized s (A * R) R g := by
  intro n hn t
  apply (hg n t).trans_eq
  have hpow : R ^ n = R ^ (n - 1) * R := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
  rw [hpow]
  ring

theorem DerivativeMajorized.add {s : ℕ} {W V R : ℝ} {g h : ℝ → ℝ}
    (hg : DerivativeMajorized s W R g)
    (hh : DerivativeMajorized s V R h)
    (hgs : ContDiff ℝ ∞ g) (hhs : ContDiff ℝ ∞ h) :
    DerivativeMajorized s (W + V) R (fun t => g t + h t) := by
  intro n hn t
  rw [show (fun t => g t + h t) = g + h by rfl,
    iteratedFDeriv_add
      (hgs.of_le (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top)))
      (hhs.of_le (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top))),
    Pi.add_apply]
  calc
    ‖iteratedFDeriv ℝ n g t + iteratedFDeriv ℝ n h t‖ ≤
        ‖iteratedFDeriv ℝ n g t‖ + ‖iteratedFDeriv ℝ n h t‖ :=
      norm_add_le _ _
    _ ≤ W * weight s n * R ^ (n - 1) +
        V * weight s n * R ^ (n - 1) :=
      add_le_add (hg n hn t) (hh n hn t)
    _ = (W + V) * weight s n * R ^ (n - 1) := by ring

theorem DerivativeMajorized.radius_mono {s : ℕ} {W R R' : ℝ}
    {g : ℝ → ℝ} (hg : DerivativeMajorized s W R g)
    (hW : 0 ≤ W) (hR : 0 ≤ R) (hRR' : R ≤ R') :
    DerivativeMajorized s W R' g := by
  intro n hn t
  apply (hg n hn t).trans
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hR hRR' (n - 1))
    (mul_nonneg hW (weight_nonneg s n))

theorem DerivativeMajorized.exponent_mono {s s' : ℕ} {W R : ℝ}
    {g : ℝ → ℝ} (hg : DerivativeMajorized s W R g)
    (hss' : s ≤ s') (hW : 0 ≤ W) (hR : 0 ≤ R) :
    DerivativeMajorized s' W R g := by
  intro n hn t
  exact (hg n hn t).trans <| by
    gcongr
    exact weight_exponent_mono hss'

theorem DerivativeMajorized.positive_id_add {s : ℕ} {W R : ℝ}
    {u : ℝ → ℝ} (hu : DerivativeMajorized s W R u)
    (hus : ContDiff ℝ ∞ u) (hW : 0 ≤ W) (hR : 0 ≤ R) :
    PositiveMajorized s (1 + W) (max 1 R) (fun t => t + u t) := by
  intro n hn t
  let K := max 1 R
  have hK : 1 ≤ K := le_max_left _ _
  have hRK : R ≤ K := le_max_right _ _
  have huK : DerivativeMajorized s W K u := hu.radius_mono hW hR hRK
  have hbase : 1 ≤ weight s n * K ^ n := by
    have hpow : (1 : ℝ) ≤ K ^ n := one_le_pow₀ hK
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ weight s n * K ^ n :=
        mul_le_mul (one_le_weight s n) hpow (by norm_num)
          (weight_nonneg s n)
  have htail : W * weight s n * K ^ (n - 1) ≤
      W * weight s n * K ^ n := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hW (weight_nonneg s n))
    exact pow_le_pow_right₀ hK (Nat.sub_le n 1)
  calc
    ‖iteratedFDeriv ℝ n (fun t => t + u t) t‖ =
        ‖iteratedFDeriv ℝ n id t + iteratedFDeriv ℝ n u t‖ := by
      rw [show (fun t => t + u t) = id + u by rfl,
        iteratedFDeriv_add (i := n) (f := id) (g := u)
          contDiff_id
          (hus.of_le
            (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top))),
        Pi.add_apply]
    _ ≤ ‖iteratedFDeriv ℝ n id t‖ + ‖iteratedFDeriv ℝ n u t‖ :=
      norm_add_le _ _
    _ ≤ 1 + W * weight s n * K ^ (n - 1) :=
      add_le_add (norm_iteratedFDeriv_id_le_one hn t) (huK n hn t)
    _ ≤ weight s n * K ^ n + W * weight s n * K ^ n :=
      add_le_add hbase htail
    _ = (1 + W) * weight s n * K ^ n := by ring

/-- Under the good-lift invariant, differentiating a degree-one lift costs
only a fixed exponential factor in the derivative-weight index and remains
linear in the analytic radius. -/
theorem liftDeriv_majorized_of_derivativeMajorized
    {s : ℕ} {W R : ℝ} {u : ℝ → ℝ}
    (hu : DerivativeMajorized s W R u) (hW : 0 ≤ W) (hR : 0 ≤ R)
    (hgood : Newton.GoodLift u) :
    Majorized s (3 / 2 + W * 2 ^ s) (2 ^ (2 * s) * R)
      (Newton.liftDeriv u) := by
  intro n t
  by_cases hn : n = 0
  · subst n
    simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      iteratedDeriv_zero, pow_zero, mul_one]
    rw [show weight s 0 = 1 by norm_num [weight], mul_one]
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [(hgood t).1])]
    exact (hgood t).2.trans <|
      le_add_of_nonneg_right
        (mul_nonneg hW (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) s))
  · have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have heq : iteratedDeriv n (Newton.liftDeriv u) t =
        iteratedDeriv (n + 1) u t := by
      rw [show Newton.liftDeriv u = fun x => 1 + deriv u x by rfl,
        iteratedDeriv_const_add (Nat.pos_of_ne_zero hn) (1 : ℝ),
        iteratedDeriv_succ']
    rw [heq, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hu' := hu (n + 1) (by omega) t
    simp only [Nat.add_sub_cancel] at hu'
    apply hu'.trans
    rw [weight_succ, mul_pow]
    have hcoef : W * 2 ^ s ≤ 3 / 2 + W * 2 ^ s := by linarith
    have hnon : 0 ≤ weight s n *
        ((2 : ℝ) ^ (2 * s)) ^ n * R ^ n := by
      exact mul_nonneg
        (mul_nonneg (weight_nonneg s n) (pow_nonneg (by norm_num) n))
        (pow_nonneg hR n)
    calc
      W * (2 ^ s * (2 ^ (2 * s)) ^ n * weight s n) * R ^ n =
          (W * 2 ^ s) *
            (weight s n * (2 ^ (2 * s)) ^ n * R ^ n) := by ring
      _ ≤ (3 / 2 + W * 2 ^ s) *
            (weight s n * (2 ^ (2 * s)) ^ n * R ^ n) :=
        mul_le_mul_of_nonneg_right hcoef hnon
      _ = (3 / 2 + W * 2 ^ s) * weight s n *
          ((2 ^ (2 * s)) ^ n * R ^ n) := by ring

theorem twistWeight_majorized_of_derivativeMajorized
    {α : ℝ} {s : ℕ} {W R : ℝ} {u : ℝ → ℝ}
    (hu : DerivativeMajorized s W R u) (hus : ContDiff ℝ ∞ u)
    (hW : 0 ≤ W) (hR : 0 ≤ R) (hgood : Newton.GoodLift u) :
    Majorized s ((3 / 2 + W * 2 ^ s) ^ 2)
      (4 * (2 ^ (2 * s) * R)) (Newton.twistWeight α u) := by
  have hl := liftDeriv_majorized_of_derivativeMajorized hu hW hR hgood
  have hls := Newton.liftDeriv_contDiff hus
  have hL : 0 ≤ 3 / 2 + W * 2 ^ s := by positivity
  have hT : 0 ≤ 2 ^ (2 * s) * R := by positivity
  change Majorized s ((3 / 2 + W * 2 ^ s) ^ 2)
    (4 * (2 ^ (2 * s) * R))
    (fun t => Newton.liftDeriv u t * Newton.liftDeriv u (t - α))
  simpa only [max_self, pow_two] using
    hl.mul (hl.shift_sub α) hls
      (hls.comp (contDiff_id.sub contDiff_const)) hL hL hT hT

theorem inverseTwistWeight_majorized_of_derivativeMajorized
    {α : ℝ} {s : ℕ} {W R : ℝ} {u : ℝ → ℝ}
    (hu : DerivativeMajorized s W R u) (hus : ContDiff ℝ ∞ u)
    (hW : 0 ≤ W) (hR : 0 ≤ R) (hgood : Newton.GoodLift u) :
    Majorized (s + 2) 4
      (16 * max 1 ((3 / 2 + W * 2 ^ s) ^ 2) *
        (2 ^ (2 * s) * R))
      (Newton.inverseTwistWeight α u) := by
  have htwist := twistWeight_majorized_of_derivativeMajorized
    (α := α) hu hus hW hR hgood
  have htwistSmooth := Newton.twistWeight_contDiff α hus
  have htwistPos (t : ℝ) : (1 : ℝ) / 4 ≤ Newton.twistWeight α u t := by
    calc
      (1 : ℝ) / 4 = (1 / 2) * (1 / 2) := by ring
      _ ≤ Newton.liftDeriv u t * Newton.liftDeriv u (t - α) := by
        exact mul_le_mul (hgood t).1 (hgood (t - α)).1
          (by norm_num) (by linarith [(hgood t).1])
      _ = Newton.twistWeight α u t := rfl
  change Majorized (s + 2) 4
    (16 * max 1 ((3 / 2 + W * 2 ^ s) ^ 2) *
      (2 ^ (2 * s) * R))
    (fun t => (Newton.twistWeight α u t)⁻¹)
  convert htwist.inv_of_ge_quarter htwistSmooth (by positivity) htwistPos using 1
  ring

theorem liftDeriv_majorized {s : ℕ} {U R : ℝ} {u : ℝ → ℝ}
    (hu : Majorized s U R u) (hus : ContDiff ℝ ∞ u) (hR : 0 ≤ R) :
    Majorized s (1 + U * R * 2 ^ s) (2 ^ (2 * s) * R)
      (Newton.liftDeriv u) := by
  have hT : 0 ≤ (2 : ℝ) ^ (2 * s) * R :=
    mul_nonneg (pow_nonneg (by norm_num) _) hR
  have hdu := hu.deriv
  have hdus : ContDiff ℝ ∞ (deriv u) :=
    (contDiff_infty_iff_deriv.mp hus).2
  change Majorized s (1 + U * R * 2 ^ s) (2 ^ (2 * s) * R)
    (fun t => 1 + deriv u t)
  simpa only [abs_one, one_mul] using
    (majorized_const s (a := (1 : ℝ)) hT).add hdu contDiff_const hdus

theorem twistWeight_majorized {α : ℝ} {s : ℕ} {U R : ℝ}
    {u : ℝ → ℝ} (hu : Majorized s U R u)
    (hus : ContDiff ℝ ∞ u) (hU : 0 ≤ U) (hR : 0 ≤ R) :
    Majorized s ((1 + U * R * 2 ^ s) ^ 2)
      (4 * (2 ^ (2 * s) * R)) (Newton.twistWeight α u) := by
  have hl := liftDeriv_majorized hu hus hR
  have hls := Newton.liftDeriv_contDiff hus
  have hL : 0 ≤ 1 + U * R * 2 ^ s := by positivity
  have hT : 0 ≤ 2 ^ (2 * s) * R := by positivity
  change Majorized s ((1 + U * R * 2 ^ s) ^ 2)
    (4 * (2 ^ (2 * s) * R))
    (fun t => Newton.liftDeriv u t * Newton.liftDeriv u (t - α))
  simpa only [max_self, pow_two] using
    hl.mul (hl.shift_sub α) hls
      (hls.comp (contDiff_id.sub contDiff_const)) hL hL hT hT

theorem inverseTwistWeight_majorized {α : ℝ} {s : ℕ} {U R : ℝ}
    {u : ℝ → ℝ} (hu : Majorized s U R u)
    (hus : ContDiff ℝ ∞ u) (hU : 0 ≤ U) (hR : 0 ≤ R)
    (hgood : Newton.GoodLift u) :
    Majorized (s + 2) 4
      (16 * max 1 ((1 + U * R * 2 ^ s) ^ 2) *
        (2 ^ (2 * s) * R))
      (Newton.inverseTwistWeight α u) := by
  have htwist := twistWeight_majorized (α := α) hu hus hU hR
  have htwistSmooth := Newton.twistWeight_contDiff α hus
  have htwistPos (t : ℝ) : (1 : ℝ) / 4 ≤ Newton.twistWeight α u t := by
    calc
      (1 : ℝ) / 4 = (1 / 2) * (1 / 2) := by ring
      _ ≤ Newton.liftDeriv u t * Newton.liftDeriv u (t - α) := by
        exact mul_le_mul (hgood t).1 (hgood (t - α)).1
          (by norm_num) (by linarith [(hgood t).1])
      _ = Newton.twistWeight α u t := rfl
  change Majorized (s + 2) 4
    (16 * max 1 ((1 + U * R * 2 ^ s) ^ 2) *
      (2 ^ (2 * s) * R))
    (fun t => (Newton.twistWeight α u t)⁻¹)
  convert htwist.inv_of_ge_quarter htwistSmooth (by positivity) htwistPos using 1
  ring

theorem four_ninths_le_inverseTwistWeight {α : ℝ} {u : ℝ → ℝ}
    (hgood : Newton.GoodLift u) (t : ℝ) :
    (4 : ℝ) / 9 ≤ Newton.inverseTwistWeight α u t := by
  have hupper : Newton.twistWeight α u t ≤ (9 : ℝ) / 4 := by
    calc
      Newton.twistWeight α u t =
          Newton.liftDeriv u t * Newton.liftDeriv u (t - α) := rfl
      _ ≤ (3 / 2 : ℝ) * (3 / 2) := by
        exact mul_le_mul (hgood t).2 (hgood (t - α)).2
          (by linarith [(hgood (t - α)).1]) (by norm_num)
      _ = 9 / 4 := by ring
  have hinv := inv_anti₀ (Newton.twistWeight_pos hgood t) hupper
  change (4 : ℝ) / 9 ≤ (Newton.twistWeight α u t)⁻¹
  have hconst : ((9 : ℝ) / 4)⁻¹ = 4 / 9 := by norm_num
  rw [← hconst]
  exact hinv

theorem four_ninths_le_inverseTwistWeight_mean {α : ℝ} {u : ℝ → ℝ}
    (hus : ContDiff ℝ ∞ u) (hgood : Newton.GoodLift u) :
    (4 : ℝ) / 9 ≤
      Nonlinear.periodMean (Newton.inverseTwistWeight α u) := by
  have hconst : IntervalIntegrable (fun _ : ℝ => (4 : ℝ) / 9)
      volume (0 : ℝ) 1 := continuous_const.intervalIntegrable 0 1
  have hinv : IntervalIntegrable (Newton.inverseTwistWeight α u)
      volume (0 : ℝ) 1 :=
    (Newton.inverseTwistWeight_contDiff α hus hgood).continuous.intervalIntegrable 0 1
  have hmono := intervalIntegral.integral_mono_on
    (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ))
    (by norm_num : (0 : ℝ) ≤ 1) hconst hinv
    (fun t _ => four_ninths_le_inverseTwistWeight hgood t)
  simpa only [Nonlinear.periodMean,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul] using hmono

theorem abs_normalizingConstant_le {α c : ℝ} {f u : ℝ → ℝ}
    {s : ℕ} {A R : ℝ}
    (hfirst : Majorized s A R (Newton.firstSolution α c f u))
    (hA : 0 ≤ A) (hus : ContDiff ℝ ∞ u)
    (hgood : Newton.GoodLift u) :
    |Newton.normalizingConstant α c f u| ≤ 9 * A := by
  have hfirstBound (t : ℝ) : ‖Newton.firstSolution α c f u t‖ ≤ A := by
    have h := hfirst 0 t
    norm_num [norm_iteratedFDeriv_eq_norm_iteratedDeriv, weight] at h
    exact h
  have hinvBound (t : ℝ) : ‖Newton.inverseTwistWeight α u t‖ ≤ 4 := by
    have htwist := by
      have h := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 4)
        (show (1 : ℝ) / 4 ≤ Newton.twistWeight α u t from by
          calc
            (1 : ℝ) / 4 = (1 / 2) * (1 / 2) := by ring
            _ ≤ Newton.liftDeriv u t * Newton.liftDeriv u (t - α) := by
              exact mul_le_mul (hgood t).1 (hgood (t - α)).1
                (by norm_num) (by linarith [(hgood t).1])
            _ = Newton.twistWeight α u t := rfl)
      simpa only using h
    rw [Real.norm_eq_abs, abs_of_pos (Newton.inverseTwistWeight_pos hgood t)]
    have hquarter : ((1 : ℝ) / 4)⁻¹ = 4 := by norm_num
    rw [← hquarter]
    simpa only [Newton.inverseTwistWeight] using htwist
  let N := Nonlinear.periodMean (fun t =>
    Newton.firstSolution α c f u t * Newton.inverseTwistWeight α u t)
  let B := Nonlinear.periodMean (Newton.inverseTwistWeight α u)
  have hN : |N| ≤ 4 * A := by
    have hbound (t : ℝ) :
        ‖Newton.firstSolution α c f u t *
          Newton.inverseTwistWeight α u t‖ ≤ 4 * A := by
      rw [norm_mul]
      calc
        ‖Newton.firstSolution α c f u t‖ *
            ‖Newton.inverseTwistWeight α u t‖ ≤ A * 4 :=
          mul_le_mul (hfirstBound t) (hinvBound t) (norm_nonneg _) hA
        _ = 4 * A := by ring
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (1 : ℝ)) (fun t _ => hbound t)
    simpa only [N, Nonlinear.periodMean, Real.norm_eq_abs,
      sub_zero, abs_one, mul_one] using h
  have hB : (4 : ℝ) / 9 ≤ B :=
    four_ninths_le_inverseTwistWeight_mean hus hgood
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  change |-N / B| ≤ 9 * A
  rw [abs_div, abs_neg, abs_of_pos hBpos]
  rw [div_le_iff₀ hBpos]
  calc
    |N| ≤ 4 * A := hN
    _ = 9 * A * ((4 : ℝ) / 9) := by ring
    _ ≤ 9 * A * B := by gcongr

def stepLiftAmplitude (s : ℕ) (W : ℝ) : ℝ :=
  3 / 2 + W * 2 ^ s

def stepLiftRadius (s : ℕ) (R : ℝ) : ℝ :=
  2 ^ (2 * s) * R

def firstRhsAmplitude (s : ℕ) (W E : ℝ) : ℝ :=
  stepLiftAmplitude s W * E

def firstRhsRadius (s : ℕ) (R : ℝ) : ℝ :=
  4 * max (stepLiftRadius s R) R

def firstSolutionAmplitude (α : ℝ) (hα : IsDiophantine α)
    (s : ℕ) (W E R : ℝ) : ℝ :=
  2 * (solveConstant α hα * firstRhsAmplitude s W E *
    2 ^ (16 * s) * firstRhsRadius s R ^ 4)

def firstSolutionRadius (s : ℕ) (R : ℝ) : ℝ :=
  (2 * Real.pi) * 2 ^ (8 * s) * firstRhsRadius s R

def inverseTwistRadius (s : ℕ) (W R : ℝ) : ℝ :=
  16 * max 1 ((stepLiftAmplitude s W) ^ 2) * stepLiftRadius s R

def secondBaseRadius (s : ℕ) (W R : ℝ) : ℝ :=
  max (firstSolutionRadius s R) (inverseTwistRadius s W R)

def secondRhsAmplitude (α : ℝ) (hα : IsDiophantine α)
    (s : ℕ) (W E R : ℝ) : ℝ :=
  40 * firstSolutionAmplitude α hα s W E R

def secondRhsRadius (s : ℕ) (W R : ℝ) : ℝ :=
  4 * secondBaseRadius s W R

def reducedAmplitude (α : ℝ) (hα : IsDiophantine α)
    (s : ℕ) (W E R : ℝ) : ℝ :=
  2 * (solveConstant α hα * secondRhsAmplitude α hα s W E R *
    2 ^ (16 * (s + 2)) * secondRhsRadius s W R ^ 4)

def reducedRadius (s : ℕ) (W R : ℝ) : ℝ :=
  (2 * Real.pi) * 2 ^ (8 * (s + 2)) * secondRhsRadius s W R

def stepAmplitude (α : ℝ) (hα : IsDiophantine α)
    (s : ℕ) (W E R : ℝ) : ℝ :=
  stepLiftAmplitude s W * reducedAmplitude α hα s W E R

def stepRadius (s : ℕ) (W R : ℝ) : ℝ :=
  4 * max (stepLiftRadius s R) (reducedRadius s W R)

/-- Fully quantitative bound for one automatically reduced Newton correction. -/
theorem step_majorized {α : ℝ} (hα : IsDiophantine α)
    (c : ℝ) {f u : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfper : Function.Periodic f 1)
    (_hfmean : ∫ t in (0 : ℝ)..1, f t = 0)
    (hus : ContDiff ℝ ∞ u) (huper : Function.Periodic u 1)
    (hgood : Newton.GoodLift u) {s : ℕ} {W E R : ℝ}
    (hu : DerivativeMajorized s W R u)
    (hres : Majorized s E R (Newton.residual α c f u))
    (hW : 0 ≤ W) (hE : 0 ≤ E) (hR : 0 ≤ R) :
    Majorized (s + 2) (stepAmplitude α hα s W E R)
      (stepRadius s W R) (Newton.step α c f u) := by
  let L := stepLiftAmplitude s W
  let T := stepLiftRadius s R
  let A₁ := firstSolutionAmplitude α hα s W E R
  let R₁ := firstSolutionRadius s R
  let Rᵢ := inverseTwistRadius s W R
  let Q := secondBaseRadius s W R
  let A₂ := reducedAmplitude α hα s W E R
  let R₂ := reducedRadius s W R
  have hL : 0 ≤ L := by unfold L stepLiftAmplitude; positivity
  have hT : 0 ≤ T := by unfold T stepLiftRadius; positivity
  have hFirstRhsR : 0 ≤ firstRhsRadius s R := by
    unfold firstRhsRadius
    positivity
  have hD : 0 ≤ solveConstant α hα := (solveConstant_pos α hα).le
  have hA₁ : 0 ≤ A₁ := by
    unfold A₁ firstSolutionAmplitude firstRhsAmplitude
    positivity
  have hR₁ : 0 ≤ R₁ := by
    unfold R₁ firstSolutionRadius
    positivity
  have hRᵢ : 0 ≤ Rᵢ := by
    unfold Rᵢ inverseTwistRadius
    positivity
  have hQ : 0 ≤ Q := by unfold Q secondBaseRadius; positivity
  have hA₂ : 0 ≤ A₂ := by
    unfold A₂ reducedAmplitude secondRhsAmplitude
    positivity
  have hR₂ : 0 ≤ R₂ := by
    unfold R₂ reducedRadius secondRhsRadius
    positivity
  have hl : Majorized s L T (Newton.liftDeriv u) := by
    simpa only [L, T, stepLiftAmplitude, stepLiftRadius] using
      liftDeriv_majorized_of_derivativeMajorized hu hW hR hgood
  have hls := Newton.liftDeriv_contDiff hus
  have hresSmooth := Newton.residual_contDiff α c hf hus
  have hresPer := Newton.residual_periodic α c hfper huper
  have hfirstRhs : Majorized s (firstRhsAmplitude s W E)
      (firstRhsRadius s R) (Newton.firstRhs α c f u) := by
    change Majorized s (L * E) (4 * max T R)
      (-(fun t => Newton.liftDeriv u t * Newton.residual α c f u t))
    simpa only [L, T, max_self] using
      (hl.mul hres hls hresSmooth hL hE hT hR).neg
  have hfirst : Majorized s A₁ R₁ (Newton.firstSolution α c f u) := by
    simpa only [A₁, R₁, firstSolutionAmplitude, firstSolutionRadius,
      Newton.firstSolution] using
      solveForward_majorized hα hfirstRhs
        (Newton.firstRhs_contDiff α c hf hus)
        (Newton.firstRhs_periodic α c hfper huper)
        (mul_nonneg hL hE) hFirstRhsR
  have hfirstSmooth := Newton.firstSolution_contDiff hα c hf hfper hus huper
  have hinv : Majorized (s + 2) 4 Rᵢ
      (Newton.inverseTwistWeight α u) := by
    simpa only [Rᵢ, inverseTwistRadius, stepLiftAmplitude,
      stepLiftRadius] using
      inverseTwistWeight_majorized_of_derivativeMajorized
        (α := α) hu hus hW hR hgood
  have hinvSmooth := Newton.inverseTwistWeight_contDiff α hus hgood
  have hfirstQ : Majorized (s + 2) A₁ Q
      (Newton.firstSolution α c f u) := by
    exact (hfirst.exponent_mono (by omega) hA₁ hR₁).radius_mono
      hA₁ hR₁ (le_max_left _ _)
  have hinvQ : Majorized (s + 2) 4 Q
      (Newton.inverseTwistWeight α u) :=
    hinv.radius_mono (by norm_num) hRᵢ (le_max_right _ _)
  have hnorm : |Newton.normalizingConstant α c f u| ≤ 9 * A₁ :=
    abs_normalizingConstant_le hfirst hA₁ hus hgood
  have hconst : Majorized (s + 2) (9 * A₁) Q
      (fun _ : ℝ => Newton.normalizingConstant α c f u) :=
    (majorized_const (s + 2) (a := Newton.normalizingConstant α c f u) hQ).amplitude_mono
      hnorm hQ
  have hz : Majorized (s + 2) (10 * A₁) Q
      (fun t => Newton.firstSolution α c f u t +
        Newton.normalizingConstant α c f u) := by
    have hadd := hfirstQ.add hconst hfirstSmooth contDiff_const
    have hamp : A₁ + 9 * A₁ = 10 * A₁ := by ring
    rw [← hamp]
    exact hadd
  have hsecond : Majorized (s + 2) (secondRhsAmplitude α hα s W E R)
      (secondRhsRadius s W R) (Newton.secondRhs α c f u) := by
    change Majorized (s + 2) (40 * A₁) (4 * Q)
      (fun t => (Newton.firstSolution α c f u t +
        Newton.normalizingConstant α c f u) *
          Newton.inverseTwistWeight α u t)
    have hprod := hz.mul hinvQ (hfirstSmooth.add contDiff_const) hinvSmooth
      (mul_nonneg (by norm_num) hA₁) (by norm_num) hQ hQ
    have hamp : 10 * A₁ * 4 = 40 * A₁ := by ring
    rw [← hamp]
    simpa only [max_self] using hprod
  have hsecondSmooth := Newton.secondRhs_contDiff hα c hf hfper hus huper hgood
  have hsecondPer := Newton.secondRhs_periodic α c (f := f) huper
  have hreduced : Majorized (s + 2) A₂ R₂
      (Newton.reducedUnknown α c f u) := by
    simpa only [A₂, R₂, reducedAmplitude, reducedRadius,
      Newton.reducedUnknown] using
      solveBackward_majorized hα hsecond hsecondSmooth hsecondPer
        (by unfold secondRhsAmplitude; positivity)
        (by unfold secondRhsRadius; positivity)
  have hreducedSmooth := Newton.reducedUnknown_contDiff
    hα c hf hfper hus huper hgood
  change Majorized (s + 2) (L * A₂) (4 * max T R₂)
    (fun t => Newton.liftDeriv u t * Newton.reducedUnknown α c f u t)
  have hl' := hl.exponent_mono (s' := s + 2) (by omega) hL hT
  simpa only [L, T, A₂, R₂, stepAmplitude, stepRadius, max_self] using
    hl'.mul hreduced hls hreducedSmooth hL hA₂ hT hR₂

end

end Submission.Majorant
