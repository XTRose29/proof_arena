import Submission.Majorant

open LeanEval.Dynamics
open MeasureTheory
open scoped ContDiff

namespace Submission.Majorant

noncomputable section

theorem weight_add (s r n : ℕ) :
    weight (s + r) n = weight s n * weight r n := by
  unfold weight
  rw [← pow_add]
  congr 1
  ring

theorem weight_order_mono {s i n : ℕ} (hin : i ≤ n) :
    weight s i ≤ weight s n := by
  unfold weight
  apply pow_le_pow_right₀ (by norm_num)
  gcongr

theorem weight_as_pow (s n : ℕ) :
    weight s n = (2 ^ (s * n) : ℝ) ^ n := by
  unfold weight
  rw [← pow_mul]
  congr 1
  ring

theorem factorial_le_two_pow_sq (n : ℕ) : n.factorial ≤ 2 ^ (n ^ 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.factorial_succ]
      calc
        (n + 1) * n.factorial ≤ 2 ^ n * 2 ^ (n ^ 2) :=
          Nat.mul_le_mul (nat_succ_le_two_pow n) ih
        _ = 2 ^ (n + n ^ 2) := by rw [← pow_add]
        _ ≤ 2 ^ ((n + 1) ^ 2) :=
          pow_le_pow_right₀ (by omega) (by nlinarith)

theorem factorial_cast_le_weight_one (n : ℕ) :
    (n.factorial : ℝ) ≤ weight 1 n := by
  unfold weight
  norm_num
  exact_mod_cast factorial_le_two_pow_sq n

/-- A majorant only for positive-order derivatives.  This is the appropriate
notion for lifts `t ↦ t + u t`, which are unbounded but have periodic bounded
derivatives. -/
def PositiveMajorized (s : ℕ) (A R : ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ n, 1 ≤ n → ∀ t,
    ‖iteratedFDeriv ℝ n g t‖ ≤ A * weight s n * R ^ n

theorem Majorized.positive {s : ℕ} {A R : ℝ} {g : ℝ → ℝ}
    (hg : Majorized s A R g) : PositiveMajorized s A R g := by
  intro n _ t
  exact hg n t

theorem norm_iteratedFDeriv_id_le_one {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    ‖iteratedFDeriv ℝ n id t‖ ≤ 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_id,
    if_neg (Nat.ne_of_gt hn)]
  split <;> simp

theorem one_le_weight (s n : ℕ) : 1 ≤ weight s n := by
  unfold weight
  exact one_le_pow₀ (by norm_num)

/-- Adding a bounded smooth periodic correction to the identity gives an
unbounded lift whose positive-order derivatives remain majorized. -/
theorem Majorized.positive_id_add {s : ℕ} {A R : ℝ} {u : ℝ → ℝ}
    (hu : Majorized s A R u) (hus : ContDiff ℝ ∞ u)
    (hA : 0 ≤ A) (hR : 0 ≤ R) :
    PositiveMajorized s (1 + A) (max 1 R) (fun t => t + u t) := by
  intro n hn t
  let K := max 1 R
  have hK : 1 ≤ K := le_max_left _ _
  have hRK : R ≤ K := le_max_right _ _
  have huK : Majorized s A K u := hu.radius_mono hA hR hRK
  have hX : 1 ≤ weight s n * K ^ n := by
    simpa only [one_mul] using
      mul_le_mul (one_le_weight s n) (one_le_pow₀ hK)
        (by norm_num : (0 : ℝ) ≤ 1) (weight_nonneg s n)
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
    _ ≤ 1 + A * weight s n * K ^ n :=
      add_le_add (norm_iteratedFDeriv_id_le_one hn t) (huK n t)
    _ = 1 + A * (weight s n * K ^ n) := by ring
    _ ≤ (1 + A) * (weight s n * K ^ n) := by
      calc
        1 + A * (weight s n * K ^ n) ≤
            weight s n * K ^ n + A * (weight s n * K ^ n) :=
          by simpa only [add_comm] using
            add_le_add_right hX (A * (weight s n * K ^ n))
        _ = (1 + A) * (weight s n * K ^ n) := by ring
    _ = (1 + A) * weight s n * K ^ n := by ring

theorem majorized_const (s : ℕ) {R a : ℝ} (hR : 0 ≤ R) :
    Majorized s |a| R (fun _ : ℝ => a) := by
  intro n t
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_const]
  by_cases hn : n = 0
  · subst n
    simp [weight]
  · rw [if_neg hn, norm_zero]
    exact mul_nonneg (mul_nonneg (abs_nonneg a) (weight_nonneg s n))
      (pow_nonneg hR n)

private def envelope (A B R S : ℝ) : ℝ :=
  max 1 (max A (max B (max R S)))

private theorem one_le_envelope (A B R S : ℝ) :
    1 ≤ envelope A B R S := le_max_left _ _

private theorem left_le_envelope (A B R S : ℝ) :
    A ≤ envelope A B R S :=
  (le_max_left A _).trans (le_max_right 1 _)

private theorem mid_le_envelope (A B R S : ℝ) :
    B ≤ envelope A B R S :=
  (le_max_left B _).trans
    ((le_max_right A _).trans (le_max_right 1 _))

private theorem radius_le_envelope (A B R S : ℝ) :
    R ≤ envelope A B R S :=
  (le_max_left R S).trans
    ((le_max_right B _).trans
      ((le_max_right A _).trans (le_max_right 1 _)))

private theorem second_radius_le_envelope (A B R S : ℝ) :
    S ≤ envelope A B R S :=
  (le_max_right R S).trans
    ((le_max_right B _).trans
      ((le_max_right A _).trans (le_max_right 1 _)))

/-- Composition of a globally majorized outer function with an inner function
whose positive-order derivatives are majorized. -/
theorem Majorized.comp_positive {s r : ℕ} {A B R S : ℝ}
    {f g : ℝ → ℝ} (hf : Majorized s A R f)
    (hg : PositiveMajorized r B S g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hA : 0 ≤ A) (hR : 0 ≤ R) (hS : 0 ≤ S) :
    Majorized (s + r + 1) A (envelope A B R S ^ 3) (f ∘ g) := by
  intro n t
  let K := envelope A B R S
  have hK : 1 ≤ K := one_le_envelope A B R S
  have hAK : A ≤ K := left_le_envelope A B R S
  have hBK : B ≤ K := mid_le_envelope A B R S
  have hRK : R ≤ K := radius_le_envelope A B R S
  have hSK : S ≤ K := second_radius_le_envelope A B R S
  have hC (i : ℕ) (hin : i ≤ n) :
      ‖iteratedFDeriv ℝ i f (g t)‖ ≤ A * weight s n * K ^ n := by
    apply (hf i (g t)).trans
    have hw : weight s i ≤ weight s n := weight_order_mono hin
    have hp : R ^ i ≤ K ^ n := by
      calc
        R ^ i ≤ K ^ i := pow_le_pow_left₀ hR hRK i
        _ ≤ K ^ n := pow_le_pow_right₀ hK hin
    calc
      A * weight s i * R ^ i = A * (weight s i * R ^ i) := by ring
      _ ≤ A * (weight s n * K ^ n) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hw hp (pow_nonneg hR i) (weight_nonneg s n)) hA
      _ = A * weight s n * K ^ n := by ring
  have hD (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDeriv ℝ i g t‖ ≤
        (K ^ 2 * 2 ^ (r * n)) ^ i := by
    apply (hg i hi t).trans
    have hBpow : B ≤ K ^ i := by
      calc
        B ≤ K := hBK
        _ = K ^ 1 := by ring
        _ ≤ K ^ i := pow_le_pow_right₀ hK hi
    have hweight : weight r i ≤ (2 ^ (r * n) : ℝ) ^ i := by
      unfold weight
      rw [← pow_mul]
      apply pow_le_pow_right₀ (by norm_num)
      have hi2 := Nat.mul_le_mul_left r (Nat.mul_le_mul_right i hin)
      simpa only [pow_two, mul_assoc] using hi2
    have hSpow : S ^ i ≤ K ^ i := pow_le_pow_left₀ hS hSK i
    calc
      B * weight r i * S ^ i ≤
          K ^ i * (2 ^ (r * n) : ℝ) ^ i * K ^ i := by
        gcongr
        exact weight_nonneg r i
      _ = (K ^ 2 * 2 ^ (r * n)) ^ i := by
        rw [mul_pow, pow_mul]
        ring
  have hcomp := norm_iteratedFDeriv_comp_le hfs hgs
    (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top)) t hC hD
  apply hcomp.trans
  have hfac : (n.factorial : ℝ) ≤ weight 1 n :=
    factorial_cast_le_weight_one n
  have hweights : weight 1 n * weight s n * weight r n =
      weight (s + r + 1) n := by
    rw [show s + r + 1 = 1 + s + r by omega,
      weight_add, weight_add]
  have hKpow : (K ^ 2) ^ n * K ^ n = (K ^ 3) ^ n := by
    rw [← mul_pow]
    congr 1
  rw [mul_pow, ← weight_as_pow r n]
  calc
    (n.factorial : ℝ) * (A * weight s n * K ^ n) *
        ((K ^ 2) ^ n * weight r n) =
      A * ((n.factorial : ℝ) * weight s n * weight r n) *
        ((K ^ 3) ^ n) := by
      calc
        (n.factorial : ℝ) * (A * weight s n * K ^ n) *
            ((K ^ 2) ^ n * weight r n) =
          A * ((n.factorial : ℝ) * weight s n * weight r n) *
            ((K ^ 2) ^ n * K ^ n) := by ring
        _ = A * ((n.factorial : ℝ) * weight s n * weight r n) *
            ((K ^ 3) ^ n) := by rw [hKpow]
    _ ≤ A * (weight 1 n * weight s n * weight r n) *
        ((K ^ 3) ^ n) := by
      have hnon : 0 ≤ A * weight s n * weight r n * (K ^ 3) ^ n :=
        mul_nonneg
          (mul_nonneg (mul_nonneg hA (weight_nonneg s n)) (weight_nonneg r n))
          (pow_nonneg (by positivity) n)
      calc
        A * ((n.factorial : ℝ) * weight s n * weight r n) * (K ^ 3) ^ n =
            (n.factorial : ℝ) *
              (A * weight s n * weight r n * (K ^ 3) ^ n) := by ring
        _ ≤ weight 1 n *
              (A * weight s n * weight r n * (K ^ 3) ^ n) :=
          mul_le_mul_of_nonneg_right hfac hnon
        _ = A * (weight 1 n * weight s n * weight r n) *
              (K ^ 3) ^ n := by ring
    _ = A * weight (s + r + 1) n * (K ^ 3) ^ n := by rw [hweights]

/-- A radius-sensitive version of `Majorized.comp_positive`.  Keeping the
four scale factors separate is important in the Newton iteration: the outer
function is fixed, so this estimate grows only linearly in the varying radius
of the inner function. -/
theorem Majorized.comp_positive_sharp {s r : ℕ} {A B R S : ℝ}
    {f g : ℝ → ℝ} (hf : Majorized s A R f)
    (hg : PositiveMajorized r B S g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hA : 0 ≤ A) (hR : 0 ≤ R) (hS : 0 ≤ S) :
    Majorized (s + r + 1) A
      (max 1 R * max 1 B * S) (f ∘ g) := by
  intro n t
  let R₀ := max 1 R
  let B₀ := max 1 B
  have hR₀ : 1 ≤ R₀ := le_max_left _ _
  have hB₀ : 1 ≤ B₀ := le_max_left _ _
  have hRR₀ : R ≤ R₀ := le_max_right _ _
  have hBB₀ : B ≤ B₀ := le_max_right _ _
  have hC (i : ℕ) (hin : i ≤ n) :
      ‖iteratedFDeriv ℝ i f (g t)‖ ≤
        A * weight s n * R₀ ^ n := by
    apply (hf i (g t)).trans
    have hw : weight s i ≤ weight s n := weight_order_mono hin
    have hp : R ^ i ≤ R₀ ^ n := by
      calc
        R ^ i ≤ R₀ ^ i := pow_le_pow_left₀ hR hRR₀ i
        _ ≤ R₀ ^ n := pow_le_pow_right₀ hR₀ hin
    calc
      A * weight s i * R ^ i = A * (weight s i * R ^ i) := by ring
      _ ≤ A * (weight s n * R₀ ^ n) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hw hp (pow_nonneg hR i) (weight_nonneg s n)) hA
      _ = A * weight s n * R₀ ^ n := by ring
  have hD (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDeriv ℝ i g t‖ ≤
        (B₀ * S * 2 ^ (r * n)) ^ i := by
    apply (hg i hi t).trans
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
  have hcomp := norm_iteratedFDeriv_comp_le hfs hgs
    (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top)) t hC hD
  apply hcomp.trans
  have hfac : (n.factorial : ℝ) ≤ weight 1 n :=
    factorial_cast_le_weight_one n
  have hweights : weight 1 n * weight s n * weight r n =
      weight (s + r + 1) n := by
    rw [show s + r + 1 = 1 + s + r by omega,
      weight_add, weight_add]
  rw [mul_pow, ← weight_as_pow r n]
  calc
    (n.factorial : ℝ) * (A * weight s n * R₀ ^ n) *
        ((B₀ * S) ^ n * weight r n) =
      A * ((n.factorial : ℝ) * weight s n * weight r n) *
        ((R₀ * B₀ * S) ^ n) := by
      rw [mul_pow, mul_pow]
      ring
    _ ≤ A * (weight 1 n * weight s n * weight r n) *
        ((R₀ * B₀ * S) ^ n) := by
      have hscale : 0 ≤ A * weight s n * weight r n *
          (R₀ * B₀ * S) ^ n := by
        exact mul_nonneg
          (mul_nonneg (mul_nonneg hA (weight_nonneg s n))
            (weight_nonneg r n))
          (pow_nonneg
            (mul_nonneg
              (mul_nonneg (zero_le_one.trans hR₀) (zero_le_one.trans hB₀)) hS) n)
      calc
        A * ((n.factorial : ℝ) * weight s n * weight r n) *
              (R₀ * B₀ * S) ^ n =
            (n.factorial : ℝ) *
              (A * weight s n * weight r n *
                (R₀ * B₀ * S) ^ n) := by ring
        _ ≤ weight 1 n *
              (A * weight s n * weight r n *
                (R₀ * B₀ * S) ^ n) :=
          mul_le_mul_of_nonneg_right hfac hscale
        _ = A * (weight 1 n * weight s n * weight r n) *
              (R₀ * B₀ * S) ^ n := by ring
    _ = A * weight (s + r + 1) n *
        (max 1 R * max 1 B * S) ^ n := by
      rw [hweights]

end

end Submission.Majorant
