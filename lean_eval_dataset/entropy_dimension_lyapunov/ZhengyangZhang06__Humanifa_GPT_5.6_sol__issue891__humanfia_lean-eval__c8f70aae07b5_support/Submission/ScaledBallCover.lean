import Submission.HausdorffCovers

namespace Submission.Helpers

open LeanEval.Dynamics
open scoped ENNReal

noncomputable def scaledNetRadius (R : ℝ) (n : ℕ) : ℝ := R / 4 ^ n

noncomputable def scaledNetCenters (F : Finset EucPlane) (c : EucPlane) (R : ℝ) :
    ℕ → Finset EucPlane
  | 0 => {c}
  | n + 1 => (scaledNetCenters F c R n).biUnion fun z =>
      F.image fun f => z + scaledNetRadius R n • f

lemma scaledNetRadius_pos {R : ℝ} (hR : 0 < R) (n : ℕ) :
    0 < scaledNetRadius R n := by
  exact div_pos hR (by positivity)

lemma scaledNetRadius_succ (R : ℝ) (n : ℕ) :
    scaledNetRadius R (n + 1) = scaledNetRadius R n / 4 := by
  simp only [scaledNetRadius, pow_succ]
  ring

lemma card_scaledNetCenters_le
    (F : Finset EucPlane) (c : EucPlane) (R : ℝ) (n : ℕ) :
    (scaledNetCenters F c R n).card ≤ F.card ^ n := by
  induction n with
  | zero => simp [scaledNetCenters]
  | succ n ih =>
      calc
        (scaledNetCenters F c R (n + 1)).card ≤
            ∑ z ∈ scaledNetCenters F c R n,
              (F.image fun f => z + scaledNetRadius R n • f).card := by
          exact Finset.card_biUnion_le
        _ ≤ ∑ _z ∈ scaledNetCenters F c R n, F.card := by
          apply Finset.sum_le_sum
          intro z hz
          exact Finset.card_image_le
        _ = (scaledNetCenters F c R n).card * F.card := by simp
        _ ≤ F.card ^ n * F.card := Nat.mul_le_mul_right _ ih
        _ = F.card ^ (n + 1) := by rw [pow_succ]

lemma exists_scaledNetCenter
    (F : Finset EucPlane)
    (hF : ∀ u : EucPlane, ‖u‖ ≤ 1 → ∃ f ∈ F, dist u f < 1 / 4)
    (c : EucPlane) {R : ℝ} (hR : 0 < R) :
    ∀ n x, dist x c ≤ R →
      ∃ z ∈ scaledNetCenters F c R n,
        dist x z ≤ scaledNetRadius R n := by
  intro n
  induction n with
  | zero =>
      intro x hx
      exact ⟨c, by simp [scaledNetCenters], by simpa [scaledNetRadius] using hx⟩
  | succ n ih =>
      intro x hx
      obtain ⟨z, hz, hxz⟩ := ih x hx
      let r := scaledNetRadius R n
      have hr : 0 < r := scaledNetRadius_pos hR n
      let u : EucPlane := r⁻¹ • (x - z)
      have hu_norm : ‖u‖ ≤ 1 := by
        dsimp [u]
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
        rw [inv_mul_le_one₀ hr]
        simpa [dist_eq_norm] using hxz
      obtain ⟨f, hfF, huf⟩ := hF u hu_norm
      let z' := z + r • f
      have hz' : z' ∈ scaledNetCenters F c R (n + 1) := by
        rw [scaledNetCenters]
        exact Finset.mem_biUnion.mpr ⟨z, hz,
          Finset.mem_image.mpr ⟨f, hfF, rfl⟩⟩
      have hru : r • u = x - z := by
        dsimp [u]
        rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      have hdiff : x - z' = r • (u - f) := by
        dsimp [z']
        rw [smul_sub, hru]
        abel
      have hxz' : dist x z' ≤ scaledNetRadius R (n + 1) := by
        have hstrict : dist x z' < r / 4 := by
          rw [dist_eq_norm, hdiff, norm_smul, Real.norm_eq_abs,
            abs_of_pos hr, ← dist_eq_norm]
          nlinarith
        rw [scaledNetRadius_succ]
        exact hstrict.le
      exact ⟨z', hz', hxz'⟩

noncomputable def scaledNetBalls (F : Finset EucPlane) (c : EucPlane) (R : ℝ)
    (n : ℕ) : Finset (Set EucPlane) :=
  (scaledNetCenters F c R n).image fun z =>
    Metric.closedBall z (scaledNetRadius R n)

lemma card_scaledNetBalls_le
    (F : Finset EucPlane) (c : EucPlane) (R : ℝ) (n : ℕ) :
    (scaledNetBalls F c R n).card ≤ F.card ^ n :=
  (Finset.card_image_le.trans (card_scaledNetCenters_le F c R n))

lemma measurableSet_of_mem_scaledNetBalls
    {F : Finset EucPlane} {c : EucPlane} {R : ℝ} {n : ℕ}
    {A : Set EucPlane} (hA : A ∈ scaledNetBalls F c R n) :
    MeasurableSet A := by
  obtain ⟨z, _hz, rfl⟩ := Finset.mem_image.mp hA
  exact measurableSet_closedBall

lemma scaledNetBalls_cover_closedBall
    (F : Finset EucPlane)
    (hF : ∀ u : EucPlane, ‖u‖ ≤ 1 → ∃ f ∈ F, dist u f < 1 / 4)
    (c : EucPlane) {R : ℝ} (hR : 0 < R) (n : ℕ) :
    Metric.closedBall c R ⊆ ⋃ A ∈ scaledNetBalls F c R n, A := by
  intro x hx
  obtain ⟨z, hz, hxz⟩ := exists_scaledNetCenter F hF c hR n x
    (Metric.mem_closedBall.mp hx)
  have hball : Metric.closedBall z (scaledNetRadius R n) ∈
      scaledNetBalls F c R n :=
    Finset.mem_image.mpr ⟨z, hz, rfl⟩
  exact Set.mem_iUnion_of_mem _ (Set.mem_iUnion_of_mem hball
    (Metric.mem_closedBall.mpr hxz))

lemma ediam_of_mem_scaledNetBalls
    {F : Finset EucPlane} {c : EucPlane} {R : ℝ} (hR : 0 < R)
    {n : ℕ} {A : Set EucPlane} (hA : A ∈ scaledNetBalls F c R n) :
    Metric.ediam A ≤ 2 * ENNReal.ofReal (scaledNetRadius R n) := by
  obtain ⟨z, _hz, rfl⟩ := Finset.mem_image.mp hA
  rw [← Metric.closedEBall_ofReal (scaledNetRadius_pos hR n).le]
  exact Metric.ediam_closedEBall_le

lemma exists_quarter_unit_net :
    ∃ F : Finset EucPlane,
      ∀ u : EucPlane, ‖u‖ ≤ 1 → ∃ f ∈ F, dist u f < 1 / 4 := by
  obtain ⟨t, _ht, ht_finite, hcover⟩ := finite_cover_balls_of_compact
    (isCompact_closedBall (0 : EucPlane) 1) (by norm_num : (0 : ℝ) < 1 / 4)
  let F : Finset EucPlane := ht_finite.toFinset
  refine ⟨F, ?_⟩
  intro u hu
  have hu_ball : u ∈ Metric.closedBall (0 : EucPlane) 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hu
  obtain ⟨f, hf⟩ := Set.mem_iUnion.mp (hcover hu_ball)
  obtain ⟨hft, huf⟩ := Set.mem_iUnion.mp hf
  exact ⟨f, by simpa [F] using hft, by simpa [Metric.mem_ball] using huf⟩

end Submission.Helpers
