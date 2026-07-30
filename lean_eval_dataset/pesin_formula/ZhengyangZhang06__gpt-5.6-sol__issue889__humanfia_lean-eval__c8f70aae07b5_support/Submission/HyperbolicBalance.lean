import Submission.CenteredEntropyLight

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter

noncomputable def balancedBackward (lam1 lam2 : ℝ) (L : ℕ) : ℕ :=
  ⌊lam1 / (lam1 - lam2) * (L : ℝ)⌋₊

noncomputable def balancedForward (lam1 lam2 : ℝ) (L : ℕ) : ℕ :=
  L - balancedBackward lam1 lam2 L

noncomputable def hyperbolicRate (lam1 lam2 : ℝ) : ℝ :=
  lam1 * (-lam2) / (lam1 - lam2)

lemma balancedBackward_le
    {lam1 lam2 : ℝ} (hlam1 : 0 < lam1) (hlam2 : lam2 < 0) (L : ℕ) :
    balancedBackward lam1 lam2 L ≤ L := by
  have hdenom : 0 < lam1 - lam2 := sub_pos.mpr (hlam2.trans hlam1)
  apply Nat.floor_le_of_le
  calc
    lam1 / (lam1 - lam2) * (L : ℝ) ≤ 1 * (L : ℝ) := by
      gcongr
      exact (div_le_one hdenom).2 (by linarith)
    _ = (L : ℝ) := one_mul _

lemma balancedBackward_add_balancedForward
    {lam1 lam2 : ℝ} (hlam1 : 0 < lam1) (hlam2 : lam2 < 0) (L : ℕ) :
    balancedBackward lam1 lam2 L + balancedForward lam1 lam2 L = L := by
  exact Nat.add_sub_of_le (balancedBackward_le hlam1 hlam2 L)

lemma tendsto_balancedBackward_div
    {lam1 lam2 : ℝ} (hlam1 : 0 < lam1) (hlam2 : lam2 < 0) :
    Tendsto
      (fun L : ℕ => (balancedBackward lam1 lam2 L : ℝ) / L)
      atTop (nhds (lam1 / (lam1 - lam2))) := by
  have hdenom : 0 < lam1 - lam2 := sub_pos.mpr (hlam2.trans hlam1)
  have hratio : 0 ≤ lam1 / (lam1 - lam2) :=
    (div_pos hlam1 hdenom).le
  simpa only [balancedBackward, Function.comp_def] using
    ((tendsto_nat_floor_mul_div_atTop (R := ℝ) hratio).comp
      tendsto_natCast_atTop_atTop)

lemma tendsto_balancedForward_div
    {lam1 lam2 : ℝ} (hlam1 : 0 < lam1) (hlam2 : lam2 < 0) :
    Tendsto
      (fun L : ℕ => (balancedForward lam1 lam2 L : ℝ) / L)
      atTop (nhds ((-lam2) / (lam1 - lam2))) := by
  have hback := tendsto_balancedBackward_div hlam1 hlam2
  have hlimit : 1 - lam1 / (lam1 - lam2) = (-lam2) / (lam1 - lam2) := by
    have hdenom : lam1 - lam2 ≠ 0 := (sub_pos.mpr (hlam2.trans hlam1)).ne'
    field_simp
    ring
  have hsub : Tendsto
      (fun L : ℕ => 1 - (balancedBackward lam1 lam2 L : ℝ) / L)
      atTop (nhds ((-lam2) / (lam1 - lam2))) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa only [hlimit] using hone.sub hback
  apply hsub.congr'
  filter_upwards [eventually_gt_atTop 0] with L hL
  have hback_le := balancedBackward_le hlam1 hlam2 L
  rw [balancedForward, Nat.cast_sub hback_le]
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  field_simp

lemma tendsto_balancedBackward_atTop
    {lam1 lam2 : ℝ} (hlam1 : 0 < lam1) (hlam2 : lam2 < 0) :
    Tendsto (balancedBackward lam1 lam2) atTop atTop := by
  have hdenom : 0 < lam1 - lam2 := sub_pos.mpr (hlam2.trans hlam1)
  exact tendsto_nat_floor_mul_atTop
    (lam1 / (lam1 - lam2)) (div_pos hlam1 hdenom)

lemma tendsto_balancedForward_atTop
    {lam1 lam2 : ℝ} (hlam1 : 0 < lam1) (hlam2 : lam2 < 0) :
    Tendsto (balancedForward lam1 lam2) atTop atTop := by
  have hratio := tendsto_balancedForward_div hlam1 hlam2
  have hdenom : 0 < lam1 - lam2 := sub_pos.mpr (hlam2.trans hlam1)
  have hforwardRatio : 0 < (-lam2) / (lam1 - lam2) :=
    div_pos (neg_pos.mpr hlam2) hdenom
  have hcast : Tendsto
      (fun L : ℕ => (balancedForward lam1 lam2 L : ℝ)) atTop atTop := by
    have hprod := hratio.pos_mul_atTop hforwardRatio
      (tendsto_natCast_atTop_atTop (R := ℝ))
    apply hprod.congr'
    filter_upwards [eventually_gt_atTop 0] with L hL
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
    field_simp
  exact tendsto_natCast_atTop_iff.mp hcast

lemma hyperbolicRate_pos
    {lam1 lam2 : ℝ} (hlam1 : 0 < lam1) (hlam2 : lam2 < 0) :
    0 < hyperbolicRate lam1 lam2 := by
  exact div_pos (mul_pos hlam1 (neg_pos.mpr hlam2))
    (sub_pos.mpr (hlam2.trans hlam1))

lemma hyperbolicRate_eq_harmonicMean_div_two
    (lam1 lam2 : ℝ) :
    hyperbolicRate lam1 lam2 = harmonicMeanLyapunov lam1 lam2 / 2 := by
  rw [hyperbolicRate, harmonicMeanLyapunov]
  ring

lemma hyperbolicRate_mul_le_forward_budget
    {lam1 lam2 : ℝ} (hlam1 : 0 < lam1) (hlam2 : lam2 < 0) (L : ℕ) :
    hyperbolicRate lam1 lam2 * L ≤
      lam1 * balancedForward lam1 lam2 L := by
  let x : ℝ := lam1 / (lam1 - lam2) * (L : ℝ)
  let m : ℕ := balancedBackward lam1 lam2 L
  have hdenom : 0 < lam1 - lam2 := sub_pos.mpr (hlam2.trans hlam1)
  have hx_nonneg : 0 ≤ x := by
    exact mul_nonneg (div_nonneg hlam1.le hdenom.le) (Nat.cast_nonneg L)
  have hm_le_x : (m : ℝ) ≤ x := by
    exact Nat.floor_le hx_nonneg
  have hmL : m ≤ L := balancedBackward_le hlam1 hlam2 L
  rw [balancedForward, Nat.cast_sub hmL]
  dsimp [hyperbolicRate, x, m]
  have hidentity :
      lam1 * (-lam2) / (lam1 - lam2) * (L : ℝ) =
        lam1 * ((L : ℝ) - lam1 / (lam1 - lam2) * (L : ℝ)) := by
    field_simp
    ring
  rw [hidentity]
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left hm_le_x (L : ℝ)) hlam1.le

lemma hyperbolicRate_mul_sub_stable_le_backward_budget
    {lam1 lam2 : ℝ} (hlam1 : 0 < lam1) (hlam2 : lam2 < 0) (L : ℕ) :
    hyperbolicRate lam1 lam2 * L - (-lam2) ≤
      (-lam2) * balancedBackward lam1 lam2 L := by
  let x : ℝ := lam1 / (lam1 - lam2) * (L : ℝ)
  let m : ℕ := balancedBackward lam1 lam2 L
  have hdenom : 0 < lam1 - lam2 := sub_pos.mpr (hlam2.trans hlam1)
  have hx_lt : x < (m : ℝ) + 1 := by
    exact Nat.lt_floor_add_one x
  have hstable_pos : 0 < -lam2 := neg_pos.mpr hlam2
  have hidentity :
      hyperbolicRate lam1 lam2 * (L : ℝ) = (-lam2) * x := by
    dsimp [hyperbolicRate, x]
    field_simp
  rw [hidentity]
  change (-lam2) * x - (-lam2) ≤ (-lam2) * (m : ℝ)
  nlinarith [mul_lt_mul_of_pos_left hx_lt hstable_pos]

lemma exists_balanced_entropy_light_atoms_limsup_ne_zero
    {M : Type*} [MeasurableSpace M]
    (mu : MeasureTheory.Measure M) [MeasureTheory.IsProbabilityMeasure mu]
    (T T_inv : M → M)
    (hT : MeasureTheory.MeasurePreserving T mu mu)
    (hT_inv : MeasureTheory.MeasurePreserving T_inv mu mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P)
    (hP_card : 1 < P.card)
    {lam1 lam2 epsilon : ℝ}
    (hlam1 : 0 < lam1) (hlam2 : lam2 < 0)
    (hepsilon : 0 < epsilon)
    (hepsilon_entropy : 2 * epsilon < entropyW mu T P) :
    ∃ N : ℕ → ℕ, Filter.Tendsto N Filter.atTop Filter.atTop ∧
      mu (Filter.limsup
        (fun k =>
          ⋃ A ∈ lightAtoms mu
              (centeredJoin T T_inv P
                (balancedBackward lam1 lam2 (N k))
                (balancedForward lam1 lam2 (N k)))
              ((entropyW mu T P - 2 * epsilon) * N k), A)
        Filter.atTop) ≠ 0 := by
  exact exists_centered_entropy_light_atoms_limsup_ne_zero
    mu T T_inv hT hT_inv P hP hP_card
      (balancedBackward lam1 lam2) (balancedForward lam1 lam2)
      (balancedBackward_add_balancedForward hlam1 hlam2)
      hepsilon hepsilon_entropy

end Submission.Helpers
