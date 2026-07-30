import Submission.NonlinearOrbitGrowth
import Submission.PartitionSupport
import Mathlib.MeasureTheory.Measure.Support

namespace Submission.Helpers

open LeanEval.Dynamics Filter MeasureTheory Topology
open scoped ENNReal

lemma measure_image_iterate_eq
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (mu : Measure EucPlane) (hT : MeasurePreserving T mu mu)
    (A : Set EucPlane) (hA : MeasurableSet A) (n : ℕ) :
    mu (T^[n] '' A) = mu A := by
  have hT_inv : MeasurePreserving T_inv mu mu :=
    measurePreserving_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hT
  have hset : T^[n] '' A = T_inv^[n] ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change T_inv^[n] (T^[n] y) ∈ A
      simpa only [hT_left.iterate n y] using hy
    · intro hx
      exact ⟨T_inv^[n] x, hx, hT_right.iterate n x⟩
  rw [hset, (hT_inv.iterate n).measure_preimage hA.nullMeasurableSet]

lemma iInter_closedBall_one_div_nat_eq_singleton (z : EucPlane) :
    (⋂ n : ℕ, Metric.closedBall z (1 / (n + 1 : ℝ))) = {z} := by
  ext y
  simp only [Set.mem_iInter, Metric.mem_closedBall, Set.mem_singleton_iff]
  constructor
  · intro hy
    apply dist_eq_zero.mp
    have hr : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ))
        atTop (nhds 0) := by
      simpa [div_eq_mul_inv, Function.comp_def, Nat.cast_add, Nat.cast_one]
        using (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
          (tendsto_add_atTop_nat 1)
    exact le_antisymm (ge_of_tendsto' hr hy) dist_nonneg
  · rintro rfl n
    simp [show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity]

lemma measure_singleton_ne_zero_of_closedBall_lower_bound
    (mu : Measure EucPlane) [IsFiniteMeasure mu]
    (z : EucPlane) {c : ℝ≥0∞} (hc : c ≠ 0)
    (hball : ∀ n : ℕ,
      c ≤ mu (Metric.closedBall z (1 / (n + 1 : ℝ)))) :
    mu {z} ≠ 0 := by
  let B : ℕ → Set EucPlane := fun n =>
    Metric.closedBall z (1 / (n + 1 : ℝ))
  have hBmeas : ∀ n, MeasurableSet (B n) := fun _ => measurableSet_closedBall
  have hBanti : Antitone B := by
    intro m n hmn
    apply Metric.closedBall_subset_closedBall
    have hmpos : (0 : ℝ) < m + 1 := by positivity
    exact one_div_le_one_div_of_le hmpos (by exact_mod_cast Nat.add_le_add_right hmn 1)
  have hlim := tendsto_measure_iInter_atTop
    (μ := mu) (fun n => (hBmeas n).nullMeasurableSet) hBanti
      ⟨0, measure_ne_top mu _⟩
  have hle : c ≤ mu (⋂ n, B n) := ge_of_tendsto' hlim hball
  rw [show (⋂ n, B n) = {z} by
    simpa [B] using iInter_closedBall_one_div_nat_eq_singleton z] at hle
  intro hzero
  rw [hzero] at hle
  exact hc (bot_unique hle)

theorem exists_atom_of_integral_lyapunovUpperAt_neg
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    {lam : ℝ} (hlam : lam = ∫ x, lyapunovUpperAt T x ∂mu)
    (hlam_neg : lam < 0) :
    ∃ z : EucPlane, mu {z} ≠ 0 := by
  let rho := -lam / 2
  have hrho : 0 < rho := by dsimp [rho]; linarith
  have hrate : lam + rho < 0 := by dsimp [rho]; linarith
  obtain ⟨delta, hdelta, hgrowth⟩ := exists_ae_nonlinear_orbit_growth
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg hlam hrho
  have hall : ∀ᵐ x ∂mu,
      (∃ G : ℝ, 0 ≤ G ∧ ∀ m : ℕ, ∀ y ∈ K,
        dist x y * Real.exp (max 0 ((lam + rho) * m) + G) ≤ delta →
          dist (T^[m] x) (T^[m] y) ≤
            Real.exp ((lam + rho) * m + G) * dist x y) ∧
      x ∈ mu.support ∧ x ∈ K := by
    filter_upwards [hgrowth, Measure.support_mem_ae,
      mem_ae_iff.mpr hmu_supp] with x hxgrowth hxsupport hxK
    exact ⟨hxgrowth, hxsupport, hxK⟩
  obtain ⟨x, hxgrowth, hxsupport, hxK⟩ := hall.exists
  obtain ⟨G, hG, hxgrowth⟩ := hxgrowth
  let r := delta / (2 * Real.exp G)
  have hr : 0 < r := by
    dsimp [r]
    positivity
  let A := Metric.ball x r ∩ K
  have hAmeas : MeasurableSet A :=
    measurableSet_ball.inter hK_compact.isClosed.measurableSet
  have hballpos : 0 < mu (Metric.ball x r) :=
    (Measure.mem_support_iff_forall x).mp hxsupport _
      (Metric.ball_mem_nhds x hr)
  have hAeq : mu A = mu (Metric.ball x r) := by
    exact measure_inter_eq_of_compl_eq_zero mu hmu_supp _
  have hApos : 0 < mu A := hAeq.symm ▸ hballpos
  have horbitK (n : ℕ) : T^[n] x ∈ K := by
    rw [← image_iterate_eq_of_image_eq T hK_inv n]
    exact ⟨x, hxK, rfl⟩
  let radius : ℕ → ℝ := fun n => Real.exp ((lam + rho) * n + G) * r
  have hradius_pos (n : ℕ) : 0 < radius n := by
    dsimp [radius]
    positivity
  have himage (n : ℕ) : T^[n] '' A ⊆ Metric.closedBall (T^[n] x) (radius n) := by
    rintro z ⟨y, hy, rfl⟩
    have hxy : dist x y ≤ r := by
      simpa [dist_comm] using (Metric.mem_ball.mp hy.1).le
    have hsmall : dist x y *
        Real.exp (max 0 ((lam + rho) * n) + G) ≤ delta := by
      rw [max_eq_left (mul_nonpos_of_nonpos_of_nonneg hrate.le
        (Nat.cast_nonneg n))]
      calc
        dist x y * Real.exp (0 + G) = dist x y * Real.exp G := by rw [zero_add]
        _ ≤ r * Real.exp G :=
          mul_le_mul_of_nonneg_right hxy (Real.exp_nonneg G)
        _ = delta / 2 := by
          dsimp [r]
          field_simp [Real.exp_ne_zero G]
        _ ≤ delta := by linarith
    apply Metric.mem_closedBall.mpr
    rw [dist_comm]
    exact (hxgrowth n y hy.2 hsmall).trans
      (mul_le_mul_of_nonneg_left hxy (Real.exp_nonneg _))
  have hradius : Tendsto radius atTop (nhds 0) := by
    have hpow : Tendsto (fun n : ℕ => Real.exp (lam + rho) ^ n)
        atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_nonneg _)
        ((Real.exp_lt_one_iff).2 hrate)
    have hconst : Tendsto (fun _ : ℕ => Real.exp G * r) atTop
        (nhds (Real.exp G * r)) := tendsto_const_nhds
    convert hconst.mul hpow using 1
    · funext n
      dsimp [radius]
      rw [Real.exp_add, show (lam + rho) * (n : ℝ) =
        (n : ℝ) * (lam + rho) by ring, Real.exp_nat_mul]
      ring_nf
    · ring_nf
  obtain ⟨z, hzK, phi, hphi, hcenter⟩ :=
    hK_compact.tendsto_subseq horbitK
  have hradius_sub : Tendsto (radius ∘ phi) atTop (nhds 0) :=
    hradius.comp hphi.tendsto_atTop
  have hcenter_dist : Tendsto (fun n => dist z (T^[phi n] x))
      atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ => z) atTop (nhds z) :=
      tendsto_const_nhds
    simpa [Function.comp_def] using hconst.dist hcenter
  have hclosedBall (n : ℕ) :
      mu A ≤ mu (Metric.closedBall z (1 / (n + 1 : ℝ))) := by
    have heps : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    have hhalf : (0 : ℝ) < (1 / (n + 1 : ℝ)) / 2 := half_pos heps
    have hc : ∀ᶠ k : ℕ in atTop,
        dist z (T^[phi k] x) < (1 / (n + 1 : ℝ)) / 2 :=
      (tendsto_order.1 hcenter_dist).2 _ hhalf
    have hr' : ∀ᶠ k : ℕ in atTop,
        radius (phi k) < (1 / (n + 1 : ℝ)) / 2 :=
      (tendsto_order.1 hradius_sub).2 _ hhalf
    obtain ⟨k, hck, hrk⟩ := (hc.and hr').exists
    have hsubset : T^[phi k] '' A ⊆
        Metric.closedBall z (1 / (n + 1 : ℝ)) := by
      intro w hw
      have hwcenter := himage (phi k) hw
      rw [Metric.mem_closedBall] at hwcenter ⊢
      have hwcenter' : dist (T^[phi k] x) w ≤ radius (phi k) := by
        simpa [dist_comm] using hwcenter
      apply le_of_lt
      calc
        dist w z = dist z w := dist_comm _ _
        _ ≤ dist z (T^[phi k] x) + dist (T^[phi k] x) w :=
          dist_triangle _ _ _
        _ < (1 / (n + 1 : ℝ)) / 2 +
            (1 / (n + 1 : ℝ)) / 2 := add_lt_add hck
          (hwcenter'.trans_lt hrk)
        _ = 1 / (n + 1 : ℝ) := by ring
    calc
      mu A = mu (T^[phi k] '' A) :=
        (measure_image_iterate_eq T T_inv hT_smooth hT_inv_smooth
          hT_left hT_right mu hT A hAmeas (phi k)).symm
      _ ≤ mu (Metric.closedBall z (1 / (n + 1 : ℝ))) :=
        measure_mono hsubset
  exact ⟨z, measure_singleton_ne_zero_of_closedBall_lower_bound
    mu z hApos.ne' hclosedBall⟩

end Submission.Helpers
