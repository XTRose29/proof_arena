import Submission.Flow
import Submission.AnalyticMajorant

open LeanEval.Dynamics

namespace Submission.Majorant

noncomputable section

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

def iterationOrder (n : ℕ) : ℕ := 4 * n + 1

def radiusExponent (n : ℕ) : ℕ := 1000 * (n + 1) ^ 2

def lossExponent (n : ℕ) : ℕ := 20000 * (n + 4) ^ 2

def errorExponent (n : ℕ) : ℕ :=
  4 * 2 ^ n + 3 * lossExponent n

def errorBudget (B : ℝ) (n : ℕ) : ℝ :=
  B⁻¹ ^ errorExponent n

def incrementBudget (n : ℕ) : ℝ :=
  ((1 : ℝ) / 2) ^ (n + 4)

def radiusBudget (B : ℝ) (n : ℕ) : ℝ :=
  B ^ radiusExponent n

theorem nextExponent_iterationOrder (n : ℕ) :
    nextExponent 1 (iterationOrder n) = iterationOrder (n + 1) := by
  unfold nextExponent iterationOrder taylorRemainderExponent
    taylorKernelExponent
  omega

theorem radiusExponent_mono (n : ℕ) :
    radiusExponent n ≤ radiusExponent (n + 1) := by
  unfold radiusExponent
  simp only [pow_two]
  nlinarith

theorem radiusExponent_lt_lossExponent (n : ℕ) :
    radiusExponent n < lossExponent n := by
  unfold radiusExponent lossExponent
  simp only [pow_two]
  nlinarith

theorem scalar_loss_bound (n : ℕ) :
    164 * iterationOrder n + 16 * radiusExponent n + 133 ≤
      lossExponent n := by
  unfold iterationOrder radiusExponent lossExponent
  simp only [pow_two]
  nlinarith

theorem scalar_next_radius_bound (n : ℕ) :
    18 * iterationOrder n + radiusExponent n + 27 ≤
      radiusExponent (n + 1) := by
  unfold iterationOrder radiusExponent
  simp only [pow_two]
  nlinarith

theorem mul_le_pow_add {B x y : ℝ} {a b : ℕ}
    (hB : 0 ≤ B) (hy : 0 ≤ y)
    (hxa : x ≤ B ^ a) (hyb : y ≤ B ^ b) :
    x * y ≤ B ^ (a + b) := by
  calc
    x * y ≤ B ^ a * B ^ b := mul_le_mul hxa hyb hy (pow_nonneg hB a)
    _ = B ^ (a + b) := by rw [pow_add]

theorem pow_mono_exponent {B : ℝ} (hB : 1 ≤ B) {a b : ℕ} (hab : a ≤ b) :
    B ^ a ≤ B ^ b :=
  pow_le_pow_right₀ hB hab

theorem add_le_pow_succ {B x y : ℝ} {a : ℕ}
    (hB : 2 ≤ B)
    (hxa : x ≤ B ^ a) (hya : y ≤ B ^ a) :
    x + y ≤ B ^ (a + 1) := by
  have hB0 : 0 ≤ B := by linarith
  calc
    x + y ≤ B ^ a + B ^ a := add_le_add hxa hya
    _ = 2 * B ^ a := by ring
    _ ≤ B * B ^ a := mul_le_mul_of_nonneg_right hB (pow_nonneg hB0 a)
    _ = B ^ (a + 1) := by rw [pow_succ]; ring

theorem pow_pow_eq_pow_mul (B : ℝ) (a k : ℕ) :
    (B ^ a) ^ k = B ^ (a * k) := by
  rw [pow_mul]

theorem pow_mul_pow3 (B : ℝ) (a b c : ℕ) :
    B ^ a * B ^ b * B ^ c = B ^ (a + b + c) := by
  rw [pow_add, pow_add]

theorem pow_mul_pow4 (B : ℝ) (a b c d : ℕ) :
    B ^ a * B ^ b * B ^ c * B ^ d = B ^ (a + b + c + d) := by
  rw [pow_add, pow_add, pow_add]

theorem pow_mul_pow5 (B : ℝ) (a b c d e : ℕ) :
    B ^ a * B ^ b * B ^ c * B ^ d * B ^ e =
      B ^ (a + b + c + d + e) := by
  rw [pow_add, pow_add, pow_add, pow_add]

def kamBase (α : ℝ) (hα : IsDiophantine α) (F RF : ℝ) : ℝ :=
  max 64 (max (solveConstant α hα) (max F RF))

theorem kamBase_ge_sixty_four (α : ℝ) (hα : IsDiophantine α) (F RF : ℝ) :
    64 ≤ kamBase α hα F RF :=
  le_max_left _ _

theorem solveConstant_le_kamBase (α : ℝ) (hα : IsDiophantine α) (F RF : ℝ) :
    solveConstant α hα ≤ kamBase α hα F RF :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem left_le_kamBase (α : ℝ) (hα : IsDiophantine α) (F RF : ℝ) :
    F ≤ kamBase α hα F RF :=
  (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

theorem right_le_kamBase (α : ℝ) (hα : IsDiophantine α) (F RF : ℝ) :
    RF ≤ kamBase α hα F RF :=
  (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- Coarse scalar estimates for one Newton step.  The constants are
deliberately roomy: all losses fit into one `B^(20000(n+4)^2)` factor. -/
theorem newton_scalar_bounds {α : ℝ} (hα : IsDiophantine α)
    {B F RF W E R c : ℝ} {n : ℕ}
    (hB : 64 ≤ B) (hsolve : solveConstant α hα ≤ B)
    (hF : 0 ≤ F) (hFB : F ≤ B) (hRF : 0 ≤ RF) (hRFB : RF ≤ B)
    (hW : 0 ≤ W) (hW1 : W ≤ 1) (hE : 0 ≤ E) (_hE1 : E ≤ 1)
    (hsmall : B ^ lossExponent n * E ≤ 1)
    (hR1 : 1 ≤ R) (hR : R ≤ radiusBudget B n)
    (hc : |c| ≤ 1) :
    stepAmplitude α hα (iterationOrder n) W E R ≤
        B ^ lossExponent n * E ∧
    stepRadius (iterationOrder n) W R ≤ B ^ lossExponent n ∧
    reducedStepAmplitude α hα (iterationOrder n) W E R ≤
        B ^ lossExponent n * E ∧
    reducedStepRadius (iterationOrder n) W R ≤ B ^ lossExponent n ∧
    nextRadius α hα 1 (iterationOrder n) RF W E R ≤
        radiusBudget B (n + 1) ∧
    nextAmplitude α hα c 1 (iterationOrder n) F RF W E R ≤
        B ^ lossExponent n * E ^ 2 ∧
    stepAmplitude α hα (iterationOrder n) W E R *
        stepRadius (iterationOrder n) W R ≤
      B ^ lossExponent n * E ∧
    stepAmplitude α hα (iterationOrder n) W E R *
        weight (iterationOrder n + 2) 1 *
          stepRadius (iterationOrder n) W R ≤
      B ^ lossExponent n * E := by
  let s := iterationOrder n
  let rE := radiusExponent n
  have hB2 : 2 ≤ B := by linarith
  have hB4 : 4 ≤ B := by linarith
  have hB8 : 8 ≤ B := by linarith
  have hB16 : 16 ≤ B := by linarith
  have hB40 : 40 ≤ B := by linarith
  have hB1 : 1 ≤ B := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hs1 : 1 ≤ s := by unfold s iterationOrder; omega
  have hR0 : 0 ≤ R := zero_le_one.trans hR1
  have hD0 : 0 ≤ solveConstant α hα := (solveConstant_pos α hα).le
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have hpiB : 2 * Real.pi ≤ B := by
    nlinarith [Real.pi_le_four]
  have hL0 : 0 ≤ stepLiftAmplitude s W := by
    unfold stepLiftAmplitude
    positivity
  have hT0 : 0 ≤ stepLiftRadius s R := by
    unfold stepLiftRadius
    positivity
  have hFR0 : 0 ≤ firstRhsRadius s R := by
    unfold firstRhsRadius
    positivity
  have hFSA0 : 0 ≤ firstSolutionAmplitude α hα s W E R := by
    unfold firstSolutionAmplitude firstRhsAmplitude
    positivity
  have hFSR0 : 0 ≤ firstSolutionRadius s R := by
    unfold firstSolutionRadius
    positivity
  have hInvR0 : 0 ≤ inverseTwistRadius s W R := by
    unfold inverseTwistRadius
    positivity
  have hBaseR0 : 0 ≤ secondBaseRadius s W R := by
    unfold secondBaseRadius
    positivity
  have hSecondA0 : 0 ≤ secondRhsAmplitude α hα s W E R := by
    unfold secondRhsAmplitude
    positivity
  have hSecondR0 : 0 ≤ secondRhsRadius s W R := by
    unfold secondRhsRadius
    positivity
  have hRedA0 : 0 ≤ reducedAmplitude α hα s W E R := by
    unfold reducedAmplitude
    positivity
  have hRedR0 : 0 ≤ reducedRadius s W R := by
    unfold reducedRadius
    positivity
  have hStepA0 : 0 ≤ stepAmplitude α hα s W E R := by
    unfold stepAmplitude
    positivity
  have hStepR0 : 0 ≤ stepRadius s W R := by
    unfold stepRadius
    positivity
  have hReducedStepA0 : 0 ≤ reducedStepAmplitude α hα s W E R := by
    unfold reducedStepAmplitude
    positivity
  have hRpow : R ≤ B ^ rE := by simpa only [radiusBudget, rE] using hR
  have htwo (k : ℕ) : (2 : ℝ) ^ k ≤ B ^ k :=
    pow_le_pow_left₀ (by norm_num) hB2 k
  have hL : stepLiftAmplitude s W ≤ B ^ (s + 1) := by
    unfold stepLiftAmplitude
    have hWs : W * 2 ^ s ≤ B ^ s := by
      calc
        W * 2 ^ s ≤ 1 * B ^ s := mul_le_mul hW1 (htwo s)
          (pow_nonneg (by norm_num) s) (by norm_num)
        _ = B ^ s := one_mul _
    have htwoBs : (2 : ℝ) ≤ B ^ s := by
      calc
        (2 : ℝ) ≤ B := hB2
        _ = B ^ 1 := by ring
        _ ≤ B ^ s := pow_mono_exponent hB1 hs1
    calc
      3 / 2 + W * 2 ^ s ≤ 2 + B ^ s := by linarith
      _ ≤ B ^ s + B ^ s := by linarith
      _ = 2 * B ^ s := by ring
      _ ≤ B * B ^ s := mul_le_mul_of_nonneg_right hB2 (pow_nonneg hB0 s)
      _ = B ^ (s + 1) := by rw [pow_succ]; ring
  have hT : stepLiftRadius s R ≤ B ^ (2 * s + rE) := by
    unfold stepLiftRadius
    exact mul_le_pow_add hB0 hR0
      (htwo (2 * s)) hRpow
  have hRprom : R ≤ B ^ (2 * s + rE) :=
    hRpow.trans (pow_mono_exponent hB1 (by omega))
  have hFR : firstRhsRadius s R ≤ B ^ (2 * s + rE + 1) := by
    unfold firstRhsRadius
    calc
      4 * max (stepLiftRadius s R) R ≤ B * B ^ (2 * s + rE) := by
        gcongr
        exact max_le hT hRprom
      _ = B ^ (2 * s + rE + 1) := by rw [pow_succ]; ring
  have hFSamp : firstSolutionAmplitude α hα s W E R ≤
      B ^ (25 * s + 4 * rE + 7) * E := by
    unfold firstSolutionAmplitude firstRhsAmplitude
    calc
      2 * (solveConstant α hα * (stepLiftAmplitude s W * E) *
          2 ^ (16 * s) * firstRhsRadius s R ^ 4) ≤
        B * (B * (B ^ (s + 1) * E) * B ^ (16 * s) *
          (B ^ (2 * s + rE + 1)) ^ 4) := by
            gcongr
      _ = B ^ (25 * s + 4 * rE + 7) * E := by
        have hp := pow_mul_pow5 B 1 1 (s + 1) (16 * s)
          ((2 * s + rE + 1) * 4)
        rw [show (B ^ (2 * s + rE + 1)) ^ 4 =
          B ^ ((2 * s + rE + 1) * 4) by apply pow_pow_eq_pow_mul]
        calc
          B * (B * (B ^ (s + 1) * E) * B ^ (16 * s) *
              B ^ ((2 * s + rE + 1) * 4)) =
              (B ^ 1 * B ^ 1 * B ^ (s + 1) * B ^ (16 * s) *
                B ^ ((2 * s + rE + 1) * 4)) * E := by simp; ring
          _ = B ^ (1 + 1 + (s + 1) + 16 * s +
              (2 * s + rE + 1) * 4) * E := by rw [hp]
          _ = B ^ (25 * s + 4 * rE + 7) * E := by
            have hexp : 1 + 1 + (s + 1) + 16 * s +
                (2 * s + rE + 1) * 4 = 25 * s + 4 * rE + 7 := by omega
            rw [hexp]
  have hSecondAmp : secondRhsAmplitude α hα s W E R ≤
      B ^ (25 * s + 4 * rE + 8) * E := by
    unfold secondRhsAmplitude
    calc
      40 * firstSolutionAmplitude α hα s W E R ≤
          B * (B ^ (25 * s + 4 * rE + 7) * E) := by gcongr
      _ = B ^ (25 * s + 4 * rE + 8) * E := by
        calc
          B * (B ^ (25 * s + 4 * rE + 7) * E) =
              (B ^ 1 * B ^ (25 * s + 4 * rE + 7)) * E := by simp; ring
          _ = B ^ (1 + (25 * s + 4 * rE + 7)) * E := by rw [← pow_add]
          _ = B ^ (25 * s + 4 * rE + 8) * E := by
            have hexp : 1 + (25 * s + 4 * rE + 7) =
                25 * s + 4 * rE + 8 := by omega
            rw [hexp]
  have hFSR : firstSolutionRadius s R ≤ B ^ (10 * s + rE + 2) := by
    unfold firstSolutionRadius
    calc
      (2 * Real.pi) * 2 ^ (8 * s) * firstRhsRadius s R ≤
          B * B ^ (8 * s) * B ^ (2 * s + rE + 1) := by gcongr
      _ = B ^ (10 * s + rE + 2) := by
        calc
          B * B ^ (8 * s) * B ^ (2 * s + rE + 1) =
              B ^ 1 * B ^ (8 * s) * B ^ (2 * s + rE + 1) := by simp
          _ = B ^ (1 + 8 * s + (2 * s + rE + 1)) :=
            pow_mul_pow3 B _ _ _
          _ = B ^ (10 * s + rE + 2) := by congr 1; omega
  have hInvR : inverseTwistRadius s W R ≤ B ^ (4 * s + rE + 4) := by
    unfold inverseTwistRadius
    have hmaxL : max 1 (stepLiftAmplitude s W ^ 2) ≤ B ^ (2 * s + 2) := by
      apply max_le
      · exact (show (1 : ℝ) = B ^ 0 by simp) ▸
          pow_mono_exponent hB1 (by omega)
      · calc
          stepLiftAmplitude s W ^ 2 ≤ (B ^ (s + 1)) ^ 2 := by gcongr
          _ = B ^ (2 * s + 2) := by
            rw [pow_pow_eq_pow_mul]
            congr 1
            omega
    calc
      16 * max 1 (stepLiftAmplitude s W ^ 2) * stepLiftRadius s R ≤
          B * B ^ (2 * s + 2) * B ^ (2 * s + rE) := by gcongr
      _ = B ^ (4 * s + rE + 3) := by
        calc
          B * B ^ (2 * s + 2) * B ^ (2 * s + rE) =
              B ^ 1 * B ^ (2 * s + 2) * B ^ (2 * s + rE) := by simp
          _ = B ^ (1 + (2 * s + 2) + (2 * s + rE)) :=
            pow_mul_pow3 B _ _ _
          _ = B ^ (4 * s + rE + 3) := by congr 1; omega
      _ ≤ B ^ (4 * s + rE + 4) := pow_mono_exponent hB1 (by omega)
  have hBaseR : secondBaseRadius s W R ≤ B ^ (10 * s + rE + 4) := by
    unfold secondBaseRadius
    apply max_le
    · exact hFSR.trans (pow_mono_exponent hB1 (by omega))
    · exact hInvR.trans (pow_mono_exponent hB1 (by omega))
  have hSecondR : secondRhsRadius s W R ≤ B ^ (10 * s + rE + 5) := by
    unfold secondRhsRadius
    calc
      4 * secondBaseRadius s W R ≤ B * B ^ (10 * s + rE + 4) := by gcongr
      _ = B ^ (10 * s + rE + 5) := by rw [pow_succ]; ring
  have hRedAmp : reducedAmplitude α hα s W E R ≤
      B ^ (81 * s + 8 * rE + 62) * E := by
    unfold reducedAmplitude
    calc
      2 * (solveConstant α hα * secondRhsAmplitude α hα s W E R *
          2 ^ (16 * (s + 2)) * secondRhsRadius s W R ^ 4) ≤
        B * (B * (B ^ (25 * s + 4 * rE + 8) * E) *
          B ^ (16 * (s + 2)) * (B ^ (10 * s + rE + 5)) ^ 4) := by
            have hab : solveConstant α hα * secondRhsAmplitude α hα s W E R ≤
                B * (B ^ (25 * s + 4 * rE + 8) * E) :=
              mul_le_mul hsolve hSecondAmp hSecondA0 hB0
            have habp : solveConstant α hα * secondRhsAmplitude α hα s W E R *
                2 ^ (16 * (s + 2)) ≤
                (B * (B ^ (25 * s + 4 * rE + 8) * E)) *
                  B ^ (16 * (s + 2)) :=
              mul_le_mul hab (htwo _) (pow_nonneg (by norm_num) _)
                (mul_nonneg hB0 (mul_nonneg (pow_nonneg hB0 _) hE))
            have hpowR : secondRhsRadius s W R ^ 4 ≤
                (B ^ (10 * s + rE + 5)) ^ 4 :=
              pow_le_pow_left₀ hSecondR0 hSecondR 4
            apply mul_le_mul hB2
            · exact mul_le_mul habp hpowR (pow_nonneg hSecondR0 4)
                (mul_nonneg
                  (mul_nonneg hB0 (mul_nonneg (pow_nonneg hB0 _) hE))
                  (pow_nonneg hB0 _))
            · positivity
            · exact hB0
      _ = B ^ (81 * s + 8 * rE + 62) * E := by
        rw [show (B ^ (10 * s + rE + 5)) ^ 4 =
          B ^ ((10 * s + rE + 5) * 4) by apply pow_pow_eq_pow_mul]
        have hp := pow_mul_pow5 B 1 1 (25 * s + 4 * rE + 8)
          (16 * (s + 2)) ((10 * s + rE + 5) * 4)
        calc
          B * (B * (B ^ (25 * s + 4 * rE + 8) * E) *
              B ^ (16 * (s + 2)) * B ^ ((10 * s + rE + 5) * 4)) =
              (B ^ 1 * B ^ 1 * B ^ (25 * s + 4 * rE + 8) *
                B ^ (16 * (s + 2)) * B ^ ((10 * s + rE + 5) * 4)) * E := by
                  simp; ring
          _ = B ^ (1 + 1 + (25 * s + 4 * rE + 8) + 16 * (s + 2) +
              (10 * s + rE + 5) * 4) * E := by rw [hp]
          _ = B ^ (81 * s + 8 * rE + 62) * E := by
            have hexp : 1 + 1 + (25 * s + 4 * rE + 8) + 16 * (s + 2) +
                (10 * s + rE + 5) * 4 = 81 * s + 8 * rE + 62 := by omega
            rw [hexp]
  have hStepAmp : stepAmplitude α hα s W E R ≤
      B ^ (82 * s + 8 * rE + 63) * E := by
    unfold stepAmplitude
    calc
      stepLiftAmplitude s W * reducedAmplitude α hα s W E R ≤
          B ^ (s + 1) * (B ^ (81 * s + 8 * rE + 62) * E) := by
            exact mul_le_mul hL hRedAmp (by positivity) (pow_nonneg hB0 _)
      _ = B ^ (82 * s + 8 * rE + 63) * E := by
        calc
          B ^ (s + 1) * (B ^ (81 * s + 8 * rE + 62) * E) =
              (B ^ (s + 1) * B ^ (81 * s + 8 * rE + 62)) * E := by ring
          _ = B ^ ((s + 1) + (81 * s + 8 * rE + 62)) * E := by rw [← pow_add]
          _ = B ^ (82 * s + 8 * rE + 63) * E := by
            have hexp : (s + 1) + (81 * s + 8 * rE + 62) =
                82 * s + 8 * rE + 63 := by omega
            rw [hexp]
  have hRedR : reducedRadius s W R ≤ B ^ (18 * s + rE + 22) := by
    unfold reducedRadius
    calc
      (2 * Real.pi) * 2 ^ (8 * (s + 2)) * secondRhsRadius s W R ≤
          B * B ^ (8 * (s + 2)) * B ^ (10 * s + rE + 5) := by gcongr
      _ = B ^ (18 * s + rE + 22) := by
        calc
          B * B ^ (8 * (s + 2)) * B ^ (10 * s + rE + 5) =
              B ^ 1 * B ^ (8 * (s + 2)) * B ^ (10 * s + rE + 5) := by simp
          _ = B ^ (1 + 8 * (s + 2) + (10 * s + rE + 5)) :=
            pow_mul_pow3 B _ _ _
          _ = B ^ (18 * s + rE + 22) := by congr 1; omega
  have hStepR : stepRadius s W R ≤ B ^ (18 * s + rE + 23) := by
    unfold stepRadius
    have hTp : stepLiftRadius s R ≤ B ^ (18 * s + rE + 22) :=
      hT.trans (pow_mono_exponent hB1 (by omega))
    calc
      4 * max (stepLiftRadius s R) (reducedRadius s W R) ≤
          B * B ^ (18 * s + rE + 22) := by
            gcongr
            exact max_le hTp hRedR
      _ = B ^ (18 * s + rE + 23) := by rw [pow_succ]; ring
  have hInvLiftR : inverseLiftRadius s W R ≤ B ^ (3 * s + rE + 3) := by
    unfold inverseLiftRadius
    have hmaxL : max 1 (stepLiftAmplitude s W) ≤ B ^ (s + 1) := by
      exact max_le (one_le_pow₀ hB1) hL
    calc
      4 * max 1 (stepLiftAmplitude s W) * stepLiftRadius s R ≤
          B * B ^ (s + 1) * B ^ (2 * s + rE) := by gcongr
      _ = B ^ (3 * s + rE + 2) := by
        calc
          B * B ^ (s + 1) * B ^ (2 * s + rE) =
              B ^ 1 * B ^ (s + 1) * B ^ (2 * s + rE) := by simp
          _ = B ^ (1 + (s + 1) + (2 * s + rE)) := pow_mul_pow3 B _ _ _
          _ = B ^ (3 * s + rE + 2) := by congr 1; omega
      _ ≤ B ^ (3 * s + rE + 3) := pow_mono_exponent hB1 (by omega)
  have hReducedStepR : reducedStepRadius s W R ≤
      B ^ (18 * s + rE + 24) := by
    unfold reducedStepRadius
    have hIp : inverseLiftRadius s W R ≤ B ^ (18 * s + rE + 23) :=
      hInvLiftR.trans (pow_mono_exponent hB1 (by omega))
    calc
      4 * max (stepRadius s W R) (inverseLiftRadius s W R) ≤
          B * B ^ (18 * s + rE + 23) := by
            gcongr
            exact max_le hStepR hIp
      _ = B ^ (18 * s + rE + 24) := by rw [pow_succ]; ring
  have hC_loss : 82 * s + 8 * rE + 63 ≤ lossExponent n := by
    have hmaster : 164 * s + 16 * rE + 133 ≤ lossExponent n := by
      simpa only [s, rE] using scalar_loss_bound n
    omega
  have hSR_loss : 18 * s + rE + 23 ≤ lossExponent n := by
    have hmaster : 164 * s + 16 * rE + 133 ≤ lossExponent n := by
      simpa only [s, rE] using scalar_loss_bound n
    omega
  have hRSR_loss : 18 * s + rE + 24 ≤ lossExponent n := by
    have hmaster : 164 * s + 16 * rE + 133 ≤ lossExponent n := by
      simpa only [s, rE] using scalar_loss_bound n
    omega
  have hStepAmpLoss : stepAmplitude α hα s W E R ≤
      B ^ lossExponent n * E :=
    hStepAmp.trans <| mul_le_mul_of_nonneg_right
      (pow_mono_exponent hB1 hC_loss) hE
  have hStepAmpOne : stepAmplitude α hα s W E R ≤ 1 :=
    hStepAmpLoss.trans hsmall
  have hStepRLoss : stepRadius s W R ≤ B ^ lossExponent n :=
    hStepR.trans (pow_mono_exponent hB1 hSR_loss)
  have hReducedAmp : reducedStepAmplitude α hα s W E R ≤
      B ^ (82 * s + 8 * rE + 64) * E := by
    unfold reducedStepAmplitude
    calc
      4 * stepAmplitude α hα s W E R ≤
          B * (B ^ (82 * s + 8 * rE + 63) * E) := by gcongr
      _ = B ^ (82 * s + 8 * rE + 64) * E := by
        calc
          B * (B ^ (82 * s + 8 * rE + 63) * E) =
              (B ^ 1 * B ^ (82 * s + 8 * rE + 63)) * E := by simp; ring
          _ = B ^ (1 + (82 * s + 8 * rE + 63)) * E := by rw [← pow_add]
          _ = B ^ (82 * s + 8 * rE + 64) * E := by
            have hexp : 1 + (82 * s + 8 * rE + 63) =
                82 * s + 8 * rE + 64 := by omega
            rw [hexp]
  have hRedC_loss : 82 * s + 8 * rE + 64 ≤ lossExponent n := by
    have hmaster : 164 * s + 16 * rE + 133 ≤ lossExponent n := by
      simpa only [s, rE] using scalar_loss_bound n
    omega
  have hReducedAmpLoss : reducedStepAmplitude α hα s W E R ≤
      B ^ lossExponent n * E :=
    hReducedAmp.trans <| mul_le_mul_of_nonneg_right
      (pow_mono_exponent hB1 hRedC_loss) hE
  have hReducedRLoss : reducedStepRadius s W R ≤ B ^ lossExponent n :=
    hReducedStepR.trans (pow_mono_exponent hB1 hRSR_loss)
  have hDefR : defectRadius s W R ≤ B ^ (18 * s + rE + 25) := by
    unfold defectRadius
    have hTp : 2 ^ (2 * s) * R ≤ B ^ (18 * s + rE + 24) :=
      hT.trans (pow_mono_exponent hB1 (by omega))
    calc
      4 * max (2 ^ (2 * s) * R) (reducedStepRadius s W R) ≤
          B * B ^ (18 * s + rE + 24) := by
            gcongr
            exact max_le hTp hReducedStepR
      _ = B ^ (18 * s + rE + 25) := by rw [pow_succ]; ring
  have hSecondDR : secondDerivativeRadius 1 RF ≤ B ^ 2 := by
    unfold secondDerivativeRadius
    norm_num
    calc
      4 * (4 * RF) = 16 * RF := by ring
      _ ≤ B * B := mul_le_mul hB16 hRFB hRF hB0
      _ = B ^ 2 := by ring
  have hInput : max 1 (1 + W + stepAmplitude α hα s W E R) ≤ B := by
    apply max_le hB1
    have hthree : 1 + W + stepAmplitude α hα s W E R ≤ 3 := by
      linarith only [hW1, hStepAmpOne]
    exact hthree.trans (by linarith only [hB])
  have hInnerR : max (max 1 R) (stepRadius s W R) ≤
      B ^ (18 * s + rE + 23) := by
    apply max_le
    · rw [max_eq_right hR1]
      exact hRpow.trans (pow_mono_exponent hB1 (by omega))
    · exact hStepR
  have hKernelR : taylorKernelRadius 1 RF (1 + W)
      (stepAmplitude α hα s W E R) (max 1 R) (stepRadius s W R) ≤
      B ^ (18 * s + rE + 26) := by
    unfold taylorKernelRadius
    have hfirst : max 1 (secondDerivativeRadius 1 RF) ≤ B ^ 2 :=
      max_le (one_le_pow₀ hB1) hSecondDR
    calc
      max 1 (secondDerivativeRadius 1 RF) *
          max 1 (1 + W + stepAmplitude α hα s W E R) *
          max (max 1 R) (stepRadius s W R) ≤
        B ^ 2 * B * B ^ (18 * s + rE + 23) := by gcongr
      _ = B ^ (18 * s + rE + 26) := by
        calc
          B ^ 2 * B * B ^ (18 * s + rE + 23) =
              B ^ 2 * B ^ 1 * B ^ (18 * s + rE + 23) := by simp
          _ = B ^ (2 + 1 + (18 * s + rE + 23)) := pow_mul_pow3 B _ _ _
          _ = B ^ (18 * s + rE + 26) := by congr 1; omega
  have hTaylorR : taylorRemainderRadius 1 RF (1 + W)
      (stepAmplitude α hα s W E R) (max 1 R) (stepRadius s W R) ≤
      B ^ (18 * s + rE + 27) := by
    unfold taylorRemainderRadius
    have h4S : 4 * stepRadius s W R ≤ B ^ (18 * s + rE + 24) := by
      calc
        4 * stepRadius s W R ≤ B * B ^ (18 * s + rE + 23) := by gcongr
        _ = B ^ (18 * s + rE + 24) := by rw [pow_succ]; ring
    have h4Sp : 4 * stepRadius s W R ≤ B ^ (18 * s + rE + 26) :=
      h4S.trans (pow_mono_exponent hB1 (by omega))
    calc
      4 * max (4 * stepRadius s W R)
          (taylorKernelRadius 1 RF (1 + W)
            (stepAmplitude α hα s W E R) (max 1 R)
            (stepRadius s W R)) ≤
        B * B ^ (18 * s + rE + 26) := by
          gcongr
          exact max_le h4Sp hKernelR
      _ = B ^ (18 * s + rE + 27) := by rw [pow_succ]; ring
  have hNextRRaw : nextRadius α hα 1 s RF W E R ≤
      B ^ (18 * s + rE + 27) := by
    unfold nextRadius
    exact max_le
      (hDefR.trans (pow_mono_exponent hB1 (by omega))) hTaylorR
  have hNextRExp : 18 * s + rE + 27 ≤ radiusExponent (n + 1) := by
    simpa only [s, rE] using scalar_next_radius_bound n
  have hNextR : nextRadius α hα 1 s RF W E R ≤
      radiusBudget B (n + 1) := by
    unfold radiusBudget
    exact hNextRRaw.trans (pow_mono_exponent hB1 hNextRExp)
  have hSecondDA : secondDerivativeAmplitude 1 F RF ≤ B ^ 6 := by
    unfold secondDerivativeAmplitude
    norm_num
    calc
      F * RF * 2 * (4 * RF) * 2 ≤
          (B * B * B) * (B * B) * B := by gcongr
      _ = B ^ 6 := by ring
  have hDefAmp : defectAmplitude α hα s W E R ≤
      B ^ (83 * s + 9 * rE + 64) * E ^ 2 := by
    unfold defectAmplitude
    have hleft : E * R * 2 ^ s ≤ E * B ^ rE * B ^ s := by
      have hER : E * R ≤ E * B ^ rE :=
        mul_le_mul_of_nonneg_left hRpow hE
      exact mul_le_mul hER (htwo s) (pow_nonneg (by norm_num) s)
        (mul_nonneg hE (pow_nonneg hB0 rE))
    calc
      (E * R * 2 ^ s) * reducedStepAmplitude α hα s W E R ≤
          (E * B ^ rE * B ^ s) *
            (B ^ (82 * s + 8 * rE + 64) * E) :=
        mul_le_mul hleft hReducedAmp (by positivity)
          (by positivity)
      _ = B ^ (83 * s + 9 * rE + 64) * E ^ 2 := by
        calc
          (E * B ^ rE * B ^ s) *
              (B ^ (82 * s + 8 * rE + 64) * E) =
              (B ^ rE * B ^ s * B ^ (82 * s + 8 * rE + 64)) * E ^ 2 := by ring
          _ = B ^ (rE + s + (82 * s + 8 * rE + 64)) * E ^ 2 := by
            rw [pow_mul_pow3]
          _ = B ^ (83 * s + 9 * rE + 64) * E ^ 2 := by
            have hexp : rE + s + (82 * s + 8 * rE + 64) =
                83 * s + 9 * rE + 64 := by omega
            rw [hexp]
  have hTaylorAmp : taylorRemainderAmplitude 1 F RF
      (stepAmplitude α hα s W E R) ≤
      B ^ (164 * s + 16 * rE + 132) * E ^ 2 := by
    unfold taylorRemainderAmplitude
    have hStepSq : stepAmplitude α hα s W E R ^ 2 ≤
        (B ^ (82 * s + 8 * rE + 63) * E) ^ 2 :=
      pow_le_pow_left₀ hStepA0 hStepAmp 2
    have hSecondDA0 : 0 ≤ secondDerivativeAmplitude 1 F RF := by
      unfold secondDerivativeAmplitude
      positivity
    calc
      stepAmplitude α hα s W E R ^ 2 * secondDerivativeAmplitude 1 F RF ≤
          (B ^ (82 * s + 8 * rE + 63) * E) ^ 2 * B ^ 6 :=
        mul_le_mul hStepSq hSecondDA hSecondDA0 (sq_nonneg _)
      _ = B ^ (164 * s + 16 * rE + 132) * E ^ 2 := by
        rw [mul_pow, pow_pow_eq_pow_mul]
        calc
          B ^ ((82 * s + 8 * rE + 63) * 2) * E ^ 2 * B ^ 6 =
              (B ^ ((82 * s + 8 * rE + 63) * 2) * B ^ 6) * E ^ 2 := by ring
          _ = B ^ ((82 * s + 8 * rE + 63) * 2 + 6) * E ^ 2 := by rw [← pow_add]
          _ = B ^ (164 * s + 16 * rE + 132) * E ^ 2 := by
            have hexp : (82 * s + 8 * rE + 63) * 2 + 6 =
                164 * s + 16 * rE + 132 := by omega
            rw [hexp]
  have hDefLoss : 83 * s + 9 * rE + 65 ≤ lossExponent n := by
    have hmaster : 164 * s + 16 * rE + 133 ≤ lossExponent n := by
      simpa only [s, rE] using scalar_loss_bound n
    omega
  have hTaylorLoss : 164 * s + 16 * rE + 133 ≤ lossExponent n := by
    simpa only [s, rE] using scalar_loss_bound n
  have hLossPos : 1 ≤ lossExponent n := by
    unfold lossExponent
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hDefExp : 83 * s + 9 * rE + 64 ≤ lossExponent n - 1 := by
    omega
  have hTaylorExp : 164 * s + 16 * rE + 132 ≤ lossExponent n - 1 := by
    omega
  have hDefSmall : defectAmplitude α hα s W E R ≤
      B ^ (lossExponent n - 1) * E ^ 2 :=
    hDefAmp.trans <| mul_le_mul_of_nonneg_right
      (pow_mono_exponent hB1 hDefExp) (sq_nonneg E)
  have hTaylorAmp0 : 0 ≤ taylorRemainderAmplitude 1 F RF
      (stepAmplitude α hα s W E R) := by
    unfold taylorRemainderAmplitude secondDerivativeAmplitude
    positivity
  have hTaylorSmall : |c| * taylorRemainderAmplitude 1 F RF
      (stepAmplitude α hα s W E R) ≤
      B ^ (lossExponent n - 1) * E ^ 2 := by
    calc
      |c| * taylorRemainderAmplitude 1 F RF
          (stepAmplitude α hα s W E R) ≤
        1 * (B ^ (164 * s + 16 * rE + 132) * E ^ 2) := by
          exact mul_le_mul hc hTaylorAmp hTaylorAmp0 (by norm_num)
      _ ≤ B ^ (lossExponent n - 1) * E ^ 2 := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (pow_mono_exponent hB1 hTaylorExp) (sq_nonneg E)
  have hNextAmp : nextAmplitude α hα c 1 s F RF W E R ≤
      B ^ lossExponent n * E ^ 2 := by
    unfold nextAmplitude
    calc
      defectAmplitude α hα s W E R +
          |c| * taylorRemainderAmplitude 1 F RF
            (stepAmplitude α hα s W E R) ≤
        2 * (B ^ (lossExponent n - 1) * E ^ 2) := by
          linarith
      _ ≤ B * (B ^ (lossExponent n - 1) * E ^ 2) := by
        exact mul_le_mul_of_nonneg_right hB2
          (mul_nonneg (pow_nonneg hB0 _) (sq_nonneg E))
      _ = B ^ lossExponent n * E ^ 2 := by
        have he : lossExponent n = (lossExponent n - 1) + 1 := by omega
        calc
          B * (B ^ (lossExponent n - 1) * E ^ 2) =
              (B ^ (lossExponent n - 1) * B) * E ^ 2 := by ring
          _ = B ^ ((lossExponent n - 1) + 1) * E ^ 2 := by
            rw [pow_succ B (lossExponent n - 1)]
          _ = B ^ lossExponent n * E ^ 2 := by rw [← he]
  have hStepProd : stepAmplitude α hα s W E R * stepRadius s W R ≤
      B ^ (100 * s + 9 * rE + 86) * E := by
    calc
      stepAmplitude α hα s W E R * stepRadius s W R ≤
          (B ^ (82 * s + 8 * rE + 63) * E) *
            B ^ (18 * s + rE + 23) := by
              exact mul_le_mul hStepAmp hStepR hStepR0
                (mul_nonneg (pow_nonneg hB0 _) hE)
      _ = B ^ (100 * s + 9 * rE + 86) * E := by
        calc
          (B ^ (82 * s + 8 * rE + 63) * E) * B ^ (18 * s + rE + 23) =
              (B ^ (82 * s + 8 * rE + 63) * B ^ (18 * s + rE + 23)) * E := by ring
          _ = B ^ ((82 * s + 8 * rE + 63) + (18 * s + rE + 23)) * E := by
            rw [← pow_add B (82 * s + 8 * rE + 63) (18 * s + rE + 23)]
          _ = B ^ (100 * s + 9 * rE + 86) * E := by
            have hexp : (82 * s + 8 * rE + 63) + (18 * s + rE + 23) =
                100 * s + 9 * rE + 86 := by omega
            rw [hexp]
  have hProdLoss : 100 * s + 9 * rE + 86 ≤ lossExponent n := by
    have hmaster : 164 * s + 16 * rE + 133 ≤ lossExponent n := by
      simpa only [s, rE] using scalar_loss_bound n
    omega
  have hStepProdLoss : stepAmplitude α hα s W E R * stepRadius s W R ≤
      B ^ lossExponent n * E :=
    hStepProd.trans <| mul_le_mul_of_nonneg_right
      (pow_mono_exponent hB1 hProdLoss) hE
  have hWeightOne : weight (s + 2) 1 ≤ B ^ (s + 2) := by
    unfold weight
    norm_num
    exact htwo (s + 2)
  have hDerivProd : stepAmplitude α hα s W E R * weight (s + 2) 1 *
      stepRadius s W R ≤ B ^ (101 * s + 9 * rE + 88) * E := by
    have hAmpWeight : stepAmplitude α hα s W E R * weight (s + 2) 1 ≤
        (B ^ (82 * s + 8 * rE + 63) * E) * B ^ (s + 2) :=
      mul_le_mul hStepAmp hWeightOne (weight_nonneg _ _)
        (mul_nonneg (pow_nonneg hB0 _) hE)
    calc
      stepAmplitude α hα s W E R * weight (s + 2) 1 * stepRadius s W R ≤
        (B ^ (82 * s + 8 * rE + 63) * E) * B ^ (s + 2) *
          B ^ (18 * s + rE + 23) :=
        mul_le_mul hAmpWeight hStepR hStepR0
          (mul_nonneg (mul_nonneg (pow_nonneg hB0 _) hE) (pow_nonneg hB0 _))
      _ = B ^ (101 * s + 9 * rE + 88) * E := by
        calc
          (B ^ (82 * s + 8 * rE + 63) * E) * B ^ (s + 2) *
              B ^ (18 * s + rE + 23) =
              (B ^ (82 * s + 8 * rE + 63) * B ^ (s + 2) *
                B ^ (18 * s + rE + 23)) * E := by ring
          _ = B ^ ((82 * s + 8 * rE + 63) + (s + 2) +
              (18 * s + rE + 23)) * E := by rw [pow_mul_pow3]
          _ = B ^ (101 * s + 9 * rE + 88) * E := by
            have hexp : (82 * s + 8 * rE + 63) + (s + 2) +
                (18 * s + rE + 23) = 101 * s + 9 * rE + 88 := by omega
            rw [hexp]
  have hDerivLoss : 101 * s + 9 * rE + 88 ≤ lossExponent n := by
    have hmaster : 164 * s + 16 * rE + 133 ≤ lossExponent n := by
      simpa only [s, rE] using scalar_loss_bound n
    omega
  have hDerivProdLoss : stepAmplitude α hα s W E R * weight (s + 2) 1 *
      stepRadius s W R ≤ B ^ lossExponent n * E :=
    hDerivProd.trans <| mul_le_mul_of_nonneg_right
      (pow_mono_exponent hB1 hDerivLoss) hE
  simpa only [s] using ⟨hStepAmpLoss, hStepRLoss, hReducedAmpLoss,
    hReducedRLoss, hNextR, hNextAmp, hStepProdLoss, hDerivProdLoss⟩

end

end Submission.Majorant
