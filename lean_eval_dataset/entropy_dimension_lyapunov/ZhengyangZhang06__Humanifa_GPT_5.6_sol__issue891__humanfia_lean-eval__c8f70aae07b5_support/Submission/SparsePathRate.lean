import Submission.SparsePieceDiameter

namespace Submission.Helpers

open LeanEval.Dynamics

lemma pow_le_exp_eta_length
    {q eta : ℝ} {H L M k : ℕ}
    (hq : 1 ≤ q) (heta : 0 ≤ eta)
    (hlog : Real.log q ≤ eta * H)
    (hcard : M ≤ L / H + 1) (hk : k ≤ M) :
    q ^ k ≤ Real.exp (eta * (L + H)) := by
  have hq_pos : 0 < q := zero_lt_one.trans_le hq
  have hHM : H * M ≤ L + H := by
    calc
      H * M ≤ H * (L / H + 1) := Nat.mul_le_mul_left H hcard
      _ = H * (L / H) + H := by rw [Nat.mul_add, Nat.mul_one]
      _ ≤ L + H := Nat.add_le_add_right (Nat.mul_div_le L H) H
  have hHk : H * k ≤ L + H :=
    (Nat.mul_le_mul_left H hk).trans hHM
  have hexponent :
      Real.log q * k ≤ eta * (L + H) := by
    calc
      Real.log q * (k : ℝ) ≤ (eta * H) * k := by
        gcongr
      _ = eta * ((H * k : ℕ) : ℝ) := by
        push_cast
        ring
      _ ≤ eta * ((L : ℝ) + H) := by
        apply mul_le_mul_of_nonneg_left _ heta
        exact_mod_cast hHk
  calc
    q ^ k = (Real.exp (Real.log q)) ^ k := by rw [Real.exp_log hq_pos]
    _ = Real.exp (k * Real.log q) := by rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (eta * (L + H)) := by
      apply Real.exp_le_exp.mpr
      simpa [mul_comm] using hexponent

lemma sparse_stable_path_term_le
    {lam1 lam2 eta rate q : ℝ} {H L M k t m : ℕ}
    (hlam1 : 0 < lam1) (hlam2 : lam2 < 0) (heta : 0 ≤ eta)
    (hq : 1 ≤ q) (hlog : Real.log q ≤ eta * H)
    (hcard : M ≤ L / H + 1) (hk : k ≤ M)
    (htm : t ≤ m) (hmtH : m ≤ t + H) (htL : t ≤ L)
    (hbudget : rate * L - (-lam2) ≤ (-lam2) * m) :
    q ^ k * Real.exp ((lam2 + 6 * eta) * t) ≤
      Real.exp (-(rate - 7 * eta) * L +
        ((-lam2) * (H + 1) + lam1 * H + eta * H)) := by
  have hqpow := pow_le_exp_eta_length hq heta hlog hcard hk
  have hstable :
      (lam2 + 6 * eta) * (t : ℝ) ≤
        -rate * L + 6 * eta * L + (-lam2) * (H + 1) := by
    have htm_real : (t : ℝ) ≤ m := by exact_mod_cast htm
    have hmtH_real : (m : ℝ) ≤ t + H := by exact_mod_cast hmtH
    have htL_real : (t : ℝ) ≤ L := by exact_mod_cast htL
    nlinarith
  have hconstant_nonneg : 0 ≤ lam1 * (H : ℝ) :=
    mul_nonneg hlam1.le (Nat.cast_nonneg H)
  calc
    q ^ k * Real.exp ((lam2 + 6 * eta) * t) ≤
        Real.exp (eta * (L + H)) *
          Real.exp ((lam2 + 6 * eta) * t) := by
      gcongr
    _ = Real.exp
        (eta * (L + H) + (lam2 + 6 * eta) * t) := by
      rw [← Real.exp_add]
    _ ≤ Real.exp (-(rate - 7 * eta) * L +
        ((-lam2) * (H + 1) + lam1 * H + eta * H)) := by
      apply Real.exp_le_exp.mpr
      have := hstable
      nlinarith

lemma sparse_unstable_path_term_le
    {lam1 lam2 eta rate q : ℝ} {H L M k gap n : ℕ}
    (hlam1 : 0 < lam1) (hlam2 : lam2 < 0) (heta : 0 ≤ eta)
    (hq : 1 ≤ q) (hlog : Real.log q ≤ eta * H)
    (hcard : M ≤ L / H + 1) (hk : k ≤ M)
    (hnGap : n ≤ gap + H) (hgapL : gap ≤ L)
    (hbudget : rate * L ≤ lam1 * n) :
    q ^ k * Real.exp ((-lam1 + 6 * eta) * gap) ≤
      Real.exp (-(rate - 7 * eta) * L +
        ((-lam2) * (H + 1) + lam1 * H + eta * H)) := by
  have hqpow := pow_le_exp_eta_length hq heta hlog hcard hk
  have hunstable :
      (-lam1 + 6 * eta) * (gap : ℝ) ≤
        -rate * L + 6 * eta * L + lam1 * H := by
    have hnGap_real : (n : ℝ) ≤ gap + H := by exact_mod_cast hnGap
    have hgapL_real : (gap : ℝ) ≤ L := by exact_mod_cast hgapL
    nlinarith
  have hconstant_nonneg : 0 ≤ (-lam2) * ((H : ℝ) + 1) :=
    mul_nonneg (neg_nonneg.mpr hlam2.le) (by positivity)
  calc
    q ^ k * Real.exp ((-lam1 + 6 * eta) * gap) ≤
        Real.exp (eta * (L + H)) *
          Real.exp ((-lam1 + 6 * eta) * gap) := by
      gcongr
    _ = Real.exp
        (eta * (L + H) + (-lam1 + 6 * eta) * gap) := by
      rw [← Real.exp_add]
    _ ≤ Real.exp (-(rate - 7 * eta) * L +
        ((-lam2) * (H + 1) + lam1 * H + eta * H)) := by
      apply Real.exp_le_exp.mpr
      have := hunstable
      nlinarith

lemma finite_sparse_path_rate_bound
    {lam1 lam2 eta rate q Lip delta : ℝ}
    {H L M m n t gap : ℕ} (ic : Fin M)
    (hlam1 : 0 < lam1) (hlam2 : lam2 < 0)
    (heta : 0 ≤ eta) (hLip : 1 ≤ Lip) (hdelta : 0 ≤ delta)
    (hq : 1 ≤ q) (hlog : Real.log q ≤ eta * H)
    (hcard : M ≤ L / H + 1)
    (htm : t ≤ m) (hmtH : m ≤ t + H) (htL : t ≤ L)
    (hnGap : n ≤ gap + H) (hgapL : gap ≤ L)
    (hstableBudget : rate * L - (-lam2) ≤ (-lam2) * m)
    (hunstableBudget : rate * L ≤ lam1 * n)
    (hconstant :
      Lip ^ H * delta * 2 *
          Real.exp ((-lam2) * (H + 1) + lam1 * H + eta * H) ≤
        Real.exp (eta * L)) :
    Lip ^ H * delta *
        (q ^ ic.val * Real.exp ((lam2 + 6 * eta) * t) +
          q ^ (M - 1 - ic.val) *
            Real.exp ((-lam1 + 6 * eta) * gap)) ≤
      Real.exp (-(rate - 8 * eta) * L) := by
  let Kconst : ℝ := (-lam2) * (H + 1) + lam1 * H + eta * H
  have hleft := sparse_stable_path_term_le
    hlam1 hlam2 heta hq hlog hcard (Nat.le_of_lt ic.isLt)
      htm hmtH htL hstableBudget
  have hright := sparse_unstable_path_term_le
    hlam1 hlam2 heta hq hlog hcard
      (show M - 1 - ic.val ≤ M by omega)
      hnGap hgapL hunstableBudget
  have hsum :
      q ^ ic.val * Real.exp ((lam2 + 6 * eta) * t) +
          q ^ (M - 1 - ic.val) *
            Real.exp ((-lam1 + 6 * eta) * gap) ≤
        2 * Real.exp (-(rate - 7 * eta) * L + Kconst) := by
    dsimp [Kconst] at hleft hright ⊢
    nlinarith
  have hpref_nonneg : 0 ≤ Lip ^ H * delta :=
    mul_nonneg (pow_nonneg (zero_le_one.trans hLip) H) hdelta
  calc
    Lip ^ H * delta *
        (q ^ ic.val * Real.exp ((lam2 + 6 * eta) * t) +
          q ^ (M - 1 - ic.val) *
            Real.exp ((-lam1 + 6 * eta) * gap)) ≤
        Lip ^ H * delta *
          (2 * Real.exp (-(rate - 7 * eta) * L + Kconst)) :=
      mul_le_mul_of_nonneg_left hsum hpref_nonneg
    _ = (Lip ^ H * delta * 2 * Real.exp Kconst) *
        Real.exp (-(rate - 7 * eta) * L) := by
      rw [show -(rate - 7 * eta) * (L : ℝ) + Kconst =
        Kconst + (-(rate - 7 * eta) * L) by ring, Real.exp_add]
      ring
    _ ≤ Real.exp (eta * L) *
        Real.exp (-(rate - 7 * eta) * L) := by
      gcongr
    _ = Real.exp (-(rate - 8 * eta) * L) := by
      rw [← Real.exp_add]
      congr 1
      ring

end Submission.Helpers
