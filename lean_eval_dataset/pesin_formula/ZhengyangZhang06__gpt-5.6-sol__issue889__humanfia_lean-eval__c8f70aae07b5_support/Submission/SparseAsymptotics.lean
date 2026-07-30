import Submission.SparseCenterShadowing
import Submission.BalancedNonlinearOrbit

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter

/-- An integral upper budget for a real bad-time density. -/
noncomputable def sparseBadBudget (q : ℝ) (N : ℕ) : ℕ :=
  ⌈q * N⌉₊ + 1

lemma sparseBadBudget_cast_le
    {q : ℝ} (hq : 0 ≤ q) (N : ℕ) :
    (sparseBadBudget q N : ℝ) ≤ q * N + 2 := by
  have hceil :=
    (Nat.ceil_lt_add_one
      (mul_nonneg hq (Nat.cast_nonneg N))).le
  dsimp [sparseBadBudget]
  push_cast
  linarith

lemma nat_le_sparseBadBudget
    {q : ℝ} (hq_one : q ≤ 1)
    {N k : ℕ} (hk : (k : ℝ) ≤ q * (N + 1)) :
    k ≤ sparseBadBudget q N := by
  have hceil : q * (N : ℝ) ≤ (⌈q * (N : ℝ)⌉₊ : ℝ) := by
    exact_mod_cast Nat.le_ceil (q * (N : ℝ))
  have hk' : (k : ℝ) ≤ (sparseBadBudget q N : ℝ) := by
    dsimp [sparseBadBudget]
    push_cast
    nlinarith
  exact_mod_cast hk'

lemma tendsto_sparseBadBudget_div
    {q : ℝ} (hq : 0 ≤ q) :
    Tendsto (fun N : ℕ => (sparseBadBudget q N : ℝ) / N)
      atTop (nhds q) := by
  have hceil :
      Tendsto
        (fun N : ℕ => (⌈q * (N : ℝ)⌉₊ : ℝ) / N)
        atTop (nhds q) := by
    simpa [Function.comp_def] using
      (tendsto_nat_ceil_mul_div_atTop (R := ℝ) hq).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hone :
      Tendsto (fun N : ℕ => (1 : ℝ) / N) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have hsum := hceil.add hone
  rw [add_zero] at hsum
  convert hsum using 1
  funext N
  dsimp [sparseBadBudget]
  push_cast
  ring

/-- The logarithmic rate of the explicit sparse-piece cardinality bound. -/
noncomputable def sparseCoverRate
    (H D Fcard : ℕ) (qbad : ℝ) : ℝ :=
  Real.log 2 / H + (4 * D : ℝ) * qbad * Real.log Fcard

lemma eventually_sparseCoverCardBound_le_exp
    {qbad kappa : ℝ} (hqbad : 0 ≤ qbad)
    {H : ℕ} (hH : 0 < H) (D Fcard : ℕ) (hFcard : 0 < Fcard)
    (hrate : sparseCoverRate H D Fcard qbad < kappa) :
    ∀ᶠ N : ℕ in atTop,
      (H * (2 ^ (N / H + 1) *
        Fcard ^ (4 * D * sparseBadBudget qbad N)) : ℕ) ≤
          Real.exp (kappa * N) := by
  let base := sparseCoverRate H D Fcard qbad
  let G :=
    Real.log H + Real.log 2 +
      (8 * D : ℝ) * Real.log Fcard
  have hgap : 0 < kappa - base := by
    simpa [base] using sub_pos.mpr hrate
  have hsmall :=
    eventually_exp_neg_mul_add_lt hgap zero_lt_one G
  filter_upwards [hsmall] with N hsmallN
  let B := sparseBadBudget qbad N
  let Q := N / H + 1
  have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
  have hFreal : (0 : ℝ) < Fcard := by exact_mod_cast hFcard
  have hFone : (1 : ℝ) ≤ Fcard := by exact_mod_cast hFcard
  have hlogF : 0 ≤ Real.log (Fcard : ℝ) := Real.log_nonneg hFone
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hB :
      (B : ℝ) ≤ qbad * N + 2 := by
    simpa [B] using sparseBadBudget_cast_le hqbad N
  have hQ :
      (Q : ℝ) ≤ (N : ℝ) / H + 1 := by
    have hmul : (H : ℝ) * (N / H : ℕ) ≤ N := by
      exact_mod_cast Nat.mul_div_le N H
    dsimp [Q]
    push_cast
    gcongr
    apply (le_div_iff₀ hHreal).2
    simpa [mul_comm] using hmul
  have hexponent :
      Real.log H + Real.log 2 * (Q : ℝ) +
          Real.log Fcard * ((4 * D * B : ℕ) : ℝ) ≤
        base * N + G := by
    have hQpart :
        Real.log 2 * (Q : ℝ) ≤
          Real.log 2 * ((N : ℝ) / H + 1) := by
      gcongr
    have hBpart :
        Real.log Fcard * ((4 * D * B : ℕ) : ℝ) ≤
          Real.log Fcard * ((4 * D : ℝ) * (qbad * N + 2)) := by
      push_cast
      gcongr
    dsimp [base, sparseCoverRate, G]
    field_simp [hHreal.ne'] at hQpart ⊢
    nlinarith
  have hlinear :
      base * (N : ℝ) + G < kappa * N := by
    have hneg :
        -(kappa - base) * (N : ℝ) + G < 0 :=
      (Real.exp_lt_one_iff.mp hsmallN)
    nlinarith
  have hHexp :
      (H : ℝ) = Real.exp (Real.log H) :=
    (Real.exp_log hHreal).symm
  have h2exp :
      (2 : ℝ) ^ Q =
        Real.exp (Real.log 2 * (Q : ℝ)) := by
    calc
      (2 : ℝ) ^ Q =
          Real.exp (Real.log 2) ^ Q := by
            rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ = Real.exp ((Q : ℝ) * Real.log 2) :=
        (Real.exp_nat_mul _ _).symm
      _ = Real.exp (Real.log 2 * (Q : ℝ)) := by
        congr 1
        ring
  have hFexp :
      (Fcard : ℝ) ^ (4 * D * B) =
        Real.exp
          (Real.log Fcard * ((4 * D * B : ℕ) : ℝ)) := by
    calc
      (Fcard : ℝ) ^ (4 * D * B) =
          Real.exp (Real.log Fcard) ^ (4 * D * B) := by
            rw [Real.exp_log hFreal]
      _ = Real.exp
          (((4 * D * B : ℕ) : ℝ) * Real.log Fcard) :=
        (Real.exp_nat_mul _ _).symm
      _ = Real.exp
          (Real.log Fcard * ((4 * D * B : ℕ) : ℝ)) := by
        congr 1
        ring
  push_cast
  rw [hHexp, h2exp, hFexp, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  exact (by simpa [add_assoc] using hexponent.trans hlinear.le)

lemma eventually_sparseBadBudget_add_le_balancedBackward
    {lam1 lam2 qbad : ℝ}
    (hlam1 : 0 < lam1) (hlam2 : lam2 < 0) (hqbad : 0 ≤ qbad)
    (hqratio : qbad < lam1 / (lam1 - lam2))
    (H : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      sparseBadBudget qbad N + H ≤ balancedBackward lam1 lam2 N := by
  have hleft :
      Tendsto
        (fun N : ℕ =>
          ((sparseBadBudget qbad N + H : ℕ) : ℝ) / N)
        atTop (nhds qbad) := by
    have hbudget := tendsto_sparseBadBudget_div hqbad
    have hH :
        Tendsto (fun N : ℕ => (H : ℝ) / N) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (H : ℝ)
    have hsum := hbudget.add hH
    rw [add_zero] at hsum
    convert hsum using 1
    funext N
    push_cast
    ring
  have hright := tendsto_balancedBackward_div hlam1 hlam2
  have hlt := hleft.eventually_lt hright hqratio
  filter_upwards [hlt, eventually_gt_atTop 0] with N hltN hN
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hcast :
      ((sparseBadBudget qbad N + H : ℕ) : ℝ) <
        balancedBackward lam1 lam2 N := by
    exact (div_lt_div_iff_of_pos_right hNreal).mp hltN
  exact_mod_cast hcast.le

set_option maxHeartbeats 800000 in
/-- The explicit sparse-piece estimate decays at any rate below its two
asymptotic exponents. -/
lemma eventually_sparseCenterBound_le
    {lam1 lam2 eta qbad M R qpath Rdecay : ℝ}
    (hlam1 : 0 < lam1) (hlam2 : lam2 < 0)
    (heta : 0 < eta)
    (hqbad : 0 ≤ qbad)
    (hM : 1 ≤ M) (hR : 0 < R) (hqpath : 1 ≤ qpath)
    {H : ℕ} (hH : 0 < H)
    (hstableRate : lam2 + 6 * eta < 0)
    (hunstableRate : -lam1 + 6 * eta < 0)
    (hstableLoss :
      6 * eta +
          qbad * (Real.log M + 2 * (-lam2)) +
          Real.log qpath / H <
        hyperbolicRate lam1 lam2 - Rdecay)
    (hunstableLoss :
      6 * eta +
          qbad * (Real.log M + lam1) +
          Real.log qpath / H <
        hyperbolicRate lam1 lam2 - Rdecay) :
    ∀ᶠ N : ℕ in atTop,
      let B := sparseBadBudget qbad N
      let m := balancedBackward lam1 lam2 N
      let n := balancedForward lam1 lam2 N
      M ^ (B + H) * R *
          (qpath ^ (N / H + 1) *
              Real.exp ((lam2 + 6 * eta) *
                ((m : ℝ) - 2 * B - 2 * H)) +
            qpath ^ (N / H + 1) *
              Real.exp ((-lam1 + 6 * eta) *
                ((n : ℝ) - B - H))) ≤
        Real.exp (-Rdecay * N) := by
  let rate := hyperbolicRate lam1 lam2
  let lossS :=
    6 * eta + qbad * (Real.log M + 2 * (-lam2)) +
      Real.log qpath / H
  let lossU :=
    6 * eta + qbad * (Real.log M + lam1) +
      Real.log qpath / H
  let GS :=
    Real.log (2 * R) +
      (Real.log M + 2 * (-lam2)) * (H + 2) +
      Real.log qpath + (-lam2)
  let GU :=
    Real.log (2 * R) +
      (Real.log M + lam1) * (H + 2) +
      Real.log qpath
  have hgapS : 0 < rate - Rdecay - lossS := by
    simpa [rate, lossS] using hstableLoss
  have hgapU : 0 < rate - Rdecay - lossU := by
    simpa [rate, lossU] using hunstableLoss
  have heventS := eventually_exp_neg_mul_add_lt hgapS zero_lt_one GS
  have heventU := eventually_exp_neg_mul_add_lt hgapU zero_lt_one GU
  filter_upwards [heventS, heventU] with N hsmallS hsmallU
  dsimp only
  let B := sparseBadBudget qbad N
  let m := balancedBackward lam1 lam2 N
  let n := balancedForward lam1 lam2 N
  let Q := N / H + 1
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hqpos : 0 < qpath := lt_of_lt_of_le zero_lt_one hqpath
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  have hlogq : 0 ≤ Real.log qpath := Real.log_nonneg hqpath
  have hB :
      (B : ℝ) ≤ qbad * N + 2 := by
    simpa [B] using sparseBadBudget_cast_le hqbad N
  have hBH :
      ((B + H : ℕ) : ℝ) ≤ qbad * N + (H + 2) := by
    push_cast
    linarith
  have hQ :
      (Q : ℝ) ≤ (N : ℝ) / H + 1 := by
    have hmul : (H : ℝ) * (N / H : ℕ) ≤ N := by
      exact_mod_cast Nat.mul_div_le N H
    have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
    dsimp [Q]
    push_cast
    gcongr
    apply (le_div_iff₀ hHreal).2
    simpa [mul_comm] using hmul
  have hmN : (m : ℝ) ≤ N := by
    exact_mod_cast balancedBackward_le hlam1 hlam2 N
  have hnN : (n : ℝ) ≤ N := by
    dsimp [n]
    exact_mod_cast Nat.sub_le N (balancedBackward lam1 lam2 N)
  have hback :=
    hyperbolicRate_mul_sub_stable_le_backward_budget
      hlam1 hlam2 N
  have hforward :=
    hyperbolicRate_mul_le_forward_budget hlam1 hlam2 N
  have hstableBase :
      (lam2 + 6 * eta) * (m : ℝ) ≤
        -rate * N + (-lam2) + 6 * eta * N := by
    dsimp [rate] at hback ⊢
    norm_num [Nat.cast_ofNat] at hback
    nlinarith
  have hunstableBase :
      (-lam1 + 6 * eta) * (n : ℝ) ≤
        -rate * N + 6 * eta * N := by
    dsimp [rate] at hforward ⊢
    nlinarith
  have hstableCorrection :
      -(lam2 + 6 * eta) * (2 * (B + H : ℕ) : ℝ) ≤
        2 * (-lam2) * (qbad * N + (H + 2)) := by
    have hnegRate :
        0 ≤ -(lam2 + 6 * eta) := neg_nonneg.mpr hstableRate.le
    have hnegRate_le : -(lam2 + 6 * eta) ≤ -lam2 := by
      linarith
    have hright_nonneg : 0 ≤ qbad * (N : ℝ) + (H + 2) := by positivity
    calc
      -(lam2 + 6 * eta) * (2 * (B + H : ℕ) : ℝ) =
          2 * (-(lam2 + 6 * eta)) * ((B + H : ℕ) : ℝ) := by ring
      _ ≤ 2 * (-(lam2 + 6 * eta)) *
          (qbad * N + (H + 2)) := by
        gcongr
      _ ≤ 2 * (-lam2) * (qbad * N + (H + 2)) := by
        gcongr
  have hunstableCorrection :
      -(-lam1 + 6 * eta) * ((B + H : ℕ) : ℝ) ≤
        lam1 * (qbad * N + (H + 2)) := by
    have hnegRate :
        0 ≤ -(-lam1 + 6 * eta) := neg_nonneg.mpr hunstableRate.le
    have hnegRate_le : -(-lam1 + 6 * eta) ≤ lam1 := by
      linarith
    have hright_nonneg : 0 ≤ qbad * (N : ℝ) + (H + 2) := by positivity
    calc
      -(-lam1 + 6 * eta) * ((B + H : ℕ) : ℝ) ≤
          -(-lam1 + 6 * eta) * (qbad * N + (H + 2)) := by
        gcongr
      _ ≤ lam1 * (qbad * N + (H + 2)) := by
        gcongr
  have hstableExponent :
      Real.log (2 * R) +
          Real.log M * ((B + H : ℕ) : ℝ) +
          Real.log qpath * (Q : ℝ) +
          (lam2 + 6 * eta) * ((m : ℝ) - 2 * B - 2 * H) ≤
        (-rate + lossS) * N + GS := by
    have hMpart :
        Real.log M * ((B + H : ℕ) : ℝ) ≤
          Real.log M * (qbad * N + (H + 2)) := by
      gcongr
    have hqpart :
        Real.log qpath * (Q : ℝ) ≤
          Real.log qpath * ((N : ℝ) / H + 1) := by
      gcongr
    have hexpand :
        (lam2 + 6 * eta) * ((m : ℝ) - 2 * B - 2 * H) =
          (lam2 + 6 * eta) * (m : ℝ) -
            (lam2 + 6 * eta) * (2 * (B + H : ℕ) : ℝ) := by
      push_cast
      ring
    rw [hexpand]
    have hratePart :
        (lam2 + 6 * eta) * (m : ℝ) -
            (lam2 + 6 * eta) * (2 * (B + H : ℕ) : ℝ) ≤
          (-rate * N + (-lam2) + 6 * eta * N) +
            2 * (-lam2) * (qbad * N + (H + 2)) := by
      simpa only [sub_eq_add_neg, neg_mul] using
        add_le_add hstableBase hstableCorrection
    calc
      Real.log (2 * R) +
            Real.log M * ((B + H : ℕ) : ℝ) +
            Real.log qpath * (Q : ℝ) +
            ((lam2 + 6 * eta) * (m : ℝ) -
              (lam2 + 6 * eta) * (2 * (B + H : ℕ) : ℝ)) ≤
          Real.log (2 * R) +
            Real.log M * (qbad * N + (H + 2)) +
            Real.log qpath * ((N : ℝ) / H + 1) +
            ((-rate * N + (-lam2) + 6 * eta * N) +
              2 * (-lam2) * (qbad * N + (H + 2))) :=
        add_le_add (add_le_add (add_le_add le_rfl hMpart) hqpart)
          hratePart
      _ = (-rate + lossS) * N + GS := by
        dsimp [lossS, GS]
        ring
  have hunstableExponent :
      Real.log (2 * R) +
          Real.log M * ((B + H : ℕ) : ℝ) +
          Real.log qpath * (Q : ℝ) +
          (-lam1 + 6 * eta) * ((n : ℝ) - B - H) ≤
        (-rate + lossU) * N + GU := by
    have hMpart :
        Real.log M * ((B + H : ℕ) : ℝ) ≤
          Real.log M * (qbad * N + (H + 2)) := by
      gcongr
    have hqpart :
        Real.log qpath * (Q : ℝ) ≤
          Real.log qpath * ((N : ℝ) / H + 1) := by
      gcongr
    have hexpand :
        (-lam1 + 6 * eta) * ((n : ℝ) - B - H) =
          (-lam1 + 6 * eta) * (n : ℝ) -
            (-lam1 + 6 * eta) * ((B + H : ℕ) : ℝ) := by
      push_cast
      ring
    rw [hexpand]
    have hratePart :
        (-lam1 + 6 * eta) * (n : ℝ) -
            (-lam1 + 6 * eta) * ((B + H : ℕ) : ℝ) ≤
          (-rate * N + 6 * eta * N) +
            lam1 * (qbad * N + (H + 2)) := by
      simpa only [sub_eq_add_neg, neg_mul] using
        add_le_add hunstableBase hunstableCorrection
    calc
      Real.log (2 * R) +
            Real.log M * ((B + H : ℕ) : ℝ) +
            Real.log qpath * (Q : ℝ) +
            ((-lam1 + 6 * eta) * (n : ℝ) -
              (-lam1 + 6 * eta) * ((B + H : ℕ) : ℝ)) ≤
          Real.log (2 * R) +
            Real.log M * (qbad * N + (H + 2)) +
            Real.log qpath * ((N : ℝ) / H + 1) +
            ((-rate * N + 6 * eta * N) +
              lam1 * (qbad * N + (H + 2))) :=
        add_le_add (add_le_add (add_le_add le_rfl hMpart) hqpart)
          hratePart
      _ = (-rate + lossU) * N + GU := by
        dsimp [lossU, GU]
        ring
  have hMexp :
      M ^ (B + H) =
        Real.exp (Real.log M * ((B + H : ℕ) : ℝ)) := by
    calc
      M ^ (B + H) =
          Real.exp (Real.log M) ^ (B + H) := by
            rw [Real.exp_log hMpos]
      _ = Real.exp (((B + H : ℕ) : ℝ) * Real.log M) :=
        (Real.exp_nat_mul _ _).symm
      _ = Real.exp (Real.log M * ((B + H : ℕ) : ℝ)) := by
        congr 1
        ring
  have hqexp :
      qpath ^ Q = Real.exp (Real.log qpath * (Q : ℝ)) := by
    calc
      qpath ^ Q =
          Real.exp (Real.log qpath) ^ Q := by
            rw [Real.exp_log hqpos]
      _ = Real.exp ((Q : ℝ) * Real.log qpath) :=
        (Real.exp_nat_mul _ _).symm
      _ = Real.exp (Real.log qpath * (Q : ℝ)) := by
        congr 1
        ring
  have h2Rexp : 2 * R = Real.exp (Real.log (2 * R)) := by
    exact (Real.exp_log (mul_pos (by norm_num) hR)).symm
  let termS :=
    M ^ (B + H) * R *
      (qpath ^ Q *
        Real.exp ((lam2 + 6 * eta) *
          ((m : ℝ) - 2 * B - 2 * H)))
  let termU :=
    M ^ (B + H) * R *
      (qpath ^ Q *
        Real.exp ((-lam1 + 6 * eta) *
          ((n : ℝ) - B - H)))
  have htermS :
      2 * termS =
        Real.exp
          (Real.log (2 * R) +
            Real.log M * ((B + H : ℕ) : ℝ) +
            Real.log qpath * (Q : ℝ) +
            (lam2 + 6 * eta) * ((m : ℝ) - 2 * B - 2 * H)) := by
    dsimp [termS]
    rw [hMexp, hqexp]
    repeat' rw [Real.exp_add]
    rw [← h2Rexp]
    ring
  have htermU :
      2 * termU =
        Real.exp
          (Real.log (2 * R) +
            Real.log M * ((B + H : ℕ) : ℝ) +
            Real.log qpath * (Q : ℝ) +
            (-lam1 + 6 * eta) * ((n : ℝ) - B - H)) := by
    dsimp [termU]
    rw [hMexp, hqexp]
    repeat' rw [Real.exp_add]
    rw [← h2Rexp]
    ring
  have hsmallS' :
      Real.exp (-(rate - Rdecay - lossS) * N + GS) ≤ 1 :=
    hsmallS.le
  have hsmallU' :
      Real.exp (-(rate - Rdecay - lossU) * N + GU) ≤ 1 :=
    hsmallU.le
  have hS : 2 * termS ≤ Real.exp (-Rdecay * N) := by
    rw [htermS]
    apply (Real.exp_le_exp.mpr hstableExponent).trans
    rw [show (-rate + lossS) * (N : ℝ) + GS =
      -Rdecay * N + (-(rate - Rdecay - lossS) * N + GS) by ring,
      Real.exp_add]
    exact mul_le_of_le_one_right (Real.exp_nonneg _) hsmallS'
  have hU : 2 * termU ≤ Real.exp (-Rdecay * N) := by
    rw [htermU]
    apply (Real.exp_le_exp.mpr hunstableExponent).trans
    rw [show (-rate + lossU) * (N : ℝ) + GU =
      -Rdecay * N + (-(rate - Rdecay - lossU) * N + GU) by ring,
      Real.exp_add]
    exact mul_le_of_le_one_right (Real.exp_nonneg _) hsmallU'
  have hrewrite :
      M ^ (B + H) * R *
          (qpath ^ Q *
              Real.exp ((lam2 + 6 * eta) *
                ((m : ℝ) - 2 * B - 2 * H)) +
            qpath ^ Q *
              Real.exp ((-lam1 + 6 * eta) *
                ((n : ℝ) - B - H))) =
        termS + termU := by
    dsimp [termS, termU]
    ring
  rw [hrewrite]
  nlinarith

end Submission.Helpers
