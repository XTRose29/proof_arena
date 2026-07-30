import Submission.DiscreteEnergy

open Filter Function Metric Set

namespace Submission

lemma taylorCoeff_normalizedRotate {H : ℂ → ℂ} {eta : ℂ} {n : ℕ}
    (hH : DifferentiableOn ℂ H (ball (0 : ℂ) 1))
    (heta : ‖eta‖ = 1) (hn : 0 < n) :
    taylorCoeff (normalizedRotate H eta) n =
      eta ^ (n - 1) * taylorCoeff H n := by
  have heta0 : eta ≠ 0 := norm_ne_zero_iff.mp (by rw [heta]; norm_num)
  have hcoeff := taylorCoeff_dilate (f := H) (c := eta) (n := n)
    hH heta.le heta0
  rw [show normalizedRotate H eta = dilate H eta by rfl, hcoeff]
  rcases n with _ | n
  · omega
  · rw [Nat.add_sub_cancel, pow_succ, mul_div_cancel_right₀ _ heta0]

lemma formalLogarithmicCoeff_scaled
    {a b : ℕ → ℂ} {eta : ℂ}
    (hb : ∀ n : ℕ, 0 < n → b n = eta ^ (n - 1) * a n) :
    ∀ n : ℕ, formalLogarithmicCoeff b n =
      eta ^ n * formalLogarithmicCoeff a n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp [formalLogarithmicCoeff]
      | succ n =>
          rw [formalLogarithmicCoeff, formalLogarithmicCoeff,
            hb (n + 2) (by omega)]
          have hsum :
              (∑ j ∈ Finset.range n,
                b (j + 2) *
                  (((n - j : ℕ) : ℂ) *
                    (2 * formalLogarithmicCoeff b (n - j)))) =
                eta ^ (n + 1) *
                  ∑ j ∈ Finset.range n,
                    a (j + 2) *
                      (((n - j : ℕ) : ℂ) *
                        (2 * formalLogarithmicCoeff a (n - j))) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            have hjn : j < n := Finset.mem_range.mp hj
            rw [hb (j + 2) (by omega), ih (n - j) (by omega)]
            have hexp : j + 2 - 1 + (n - j) = n + 1 := by omega
            have hpow : eta ^ (j + 2 - 1) * eta ^ (n - j) =
                eta ^ (n + 1) := by
              rw [← pow_add, hexp]
            calc
              eta ^ (j + 2 - 1) * a (j + 2) *
                    (((n - j : ℕ) : ℂ) *
                      (2 * (eta ^ (n - j) *
                        formalLogarithmicCoeff a (n - j)))) =
                  (eta ^ (j + 2 - 1) * eta ^ (n - j)) *
                    (a (j + 2) * (((n - j : ℕ) : ℂ) *
                      (2 * formalLogarithmicCoeff a (n - j)))) := by ring
              _ = _ := by rw [hpow]
          rw [hsum]
          have hexp : n + 2 - 1 = n + 1 := by omega
          rw [hexp]
          ring

lemma formalLogarithmicCoeff_normalizedRotate
    {H : ℂ → ℂ} {eta : ℂ}
    (hH : DifferentiableOn ℂ H (ball (0 : ℂ) 1))
    (heta : ‖eta‖ = 1) (n : ℕ) :
    formalLogarithmicCoeff (taylorCoeff (normalizedRotate H eta)) n =
      eta ^ n * formalLogarithmicCoeff (taylorCoeff H) n := by
  apply formalLogarithmicCoeff_scaled
  intro k hk
  exact taylorCoeff_normalizedRotate hH heta hk

lemma norm_formalLogarithmicCoeff_normalizedRotate
    {H : ℂ → ℂ} {eta : ℂ}
    (hH : DifferentiableOn ℂ H (ball (0 : ℂ) 1))
    (heta : ‖eta‖ = 1) (n : ℕ) :
    ‖formalLogarithmicCoeff (taylorCoeff (normalizedRotate H eta)) n‖ =
      ‖formalLogarithmicCoeff (taylorCoeff H) n‖ := by
  rw [formalLogarithmicCoeff_normalizedRotate hH heta, norm_mul, norm_pow, heta,
    one_pow, one_mul]

lemma vectorDeBrangesGap_eq_of_norm_eq {N : ℕ} {t : ℝ}
    {c d : LoewnerCoeffVector N}
    (hcd : ∀ k ∈ Finset.range N,
      ‖coeffVectorToSeq c (k + 1)‖ =
        ‖coeffVectorToSeq d (k + 1)‖) :
    vectorDeBrangesGap N t c = vectorDeBrangesGap N t d := by
  unfold vectorDeBrangesGap deBrangesEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [hcd k hk]

lemma vectorDeBrangesGap_formal_normalizedRotate {N : ℕ} {t : ℝ}
    {H : ℂ → ℂ} {eta : ℂ}
    (hH : DifferentiableOn ℂ H (ball (0 : ℂ) 1))
    (heta : ‖eta‖ = 1) :
    vectorDeBrangesGap N t
        (seqToCoeffVector N
          (formalLogarithmicCoeff (taylorCoeff (normalizedRotate H eta)))) =
      vectorDeBrangesGap N t
        (seqToCoeffVector N
          (formalLogarithmicCoeff (taylorCoeff H))) := by
  apply vectorDeBrangesGap_eq_of_norm_eq
  intro k hk
  have hkN : k + 1 < N + 1 := Nat.succ_lt_succ (Finset.mem_range.mp hk)
  simpa [coeffVectorToSeq, hkN] using
    norm_formalLogarithmicCoeff_normalizedRotate hH heta (k + 1)

noncomputable def fineLoewnerRadius (rho : ℝ) : ℝ :=
  2 * Real.sqrt rho / (1 + rho)

noncomputable def fineLoewnerMesh (rho : ℝ) : ℝ :=
  1 - fineLoewnerRadius rho

lemma fineLoewnerRadius_mul_gain {rho : ℝ} (hrho : 0 < rho) :
    fineLoewnerRadius rho * fineLoewnerGain rho = 1 := by
  have hsqrt : 0 < Real.sqrt rho := Real.sqrt_pos.2 hrho
  have hden : 1 + rho ≠ 0 := by positivity
  unfold fineLoewnerRadius fineLoewnerGain
  rw [div_mul_div_comm]
  field_simp [hden, hsqrt.ne']

lemma fineLoewnerRadius_pos {rho : ℝ} (hrho : 0 < rho) :
    0 < fineLoewnerRadius rho := by
  unfold fineLoewnerRadius
  positivity

lemma fineLoewnerRadius_lt_one {rho : ℝ} (hrho : 0 < rho)
    (hrho1 : rho < 1) : fineLoewnerRadius rho < 1 := by
  have hgain := one_lt_fineLoewnerGain hrho hrho1
  have hradius := fineLoewnerRadius_pos hrho
  have hproduct := fineLoewnerRadius_mul_gain hrho
  nlinarith

lemma fineLoewnerMesh_nonneg {rho : ℝ} (hrho : 0 < rho)
    (hrho1 : rho < 1) : 0 ≤ fineLoewnerMesh rho := by
  exact sub_nonneg.mpr (fineLoewnerRadius_lt_one hrho hrho1).le

lemma omittedPointStep_realRadius_eq_fineLoewnerRadius
    {E F : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    {rho : ℝ} (hrho : 0 < rho)
    (step : E.OmittedPointStep F) (ha : ‖step.a‖ = rho) :
    step.realRadius = fineLoewnerRadius rho := by
  have hbSq : ‖step.b‖ ^ 2 = rho := by
    have h := congrArg norm step.b_sq
    rw [norm_pow, norm_neg, ha] at h
    exact h
  have hb : ‖step.b‖ = Real.sqrt rho := by
    have hsqrtSq : (Real.sqrt rho) ^ 2 = rho := Real.sq_sqrt hrho.le
    nlinarith [norm_nonneg step.b, Real.sqrt_nonneg rho]
  unfold NormalizedDiskEmbedding.OmittedPointStep.realRadius fineLoewnerRadius
  rw [step.norm_contraction, hb, Real.sq_sqrt hrho.le]

noncomputable def fineReachIndex
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho < 1) : ℕ :=
  Nat.find (fineEmbeddingChain_eventually_reaches E₀ rho hrho hrho1)

lemma fineReachIndex_spec
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho < 1) :
    rho ≤ ‖deriv
      (fineEmbeddingChain E₀ rho hrho hrho1
        (fineReachIndex E₀ rho hrho hrho1)).toFun 0‖ := by
  exact Nat.find_spec (fineEmbeddingChain_eventually_reaches E₀ rho hrho hrho1)

lemma fineEmbeddingChain_before_reachIndex
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho < 1)
    {j : ℕ} (hj : j < fineReachIndex E₀ rho hrho hrho1) :
    ‖deriv (fineEmbeddingChain E₀ rho hrho hrho1 j).toFun 0‖ < rho := by
  exact lt_of_not_ge
    (Nat.find_min (fineEmbeddingChain_eventually_reaches E₀ rho hrho hrho1) hj)

noncomputable def fineChainStepBeforeIndex
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho < 1)
    (j : ℕ) (hj : j < fineReachIndex E₀ rho hrho hrho1) :
    (fineEmbeddingChain E₀ rho hrho hrho1 j).OmittedPointStep
      (fineEmbeddingChain E₀ rho hrho hrho1 (j + 1)) :=
  fineEmbeddingChainStep E₀ rho hrho hrho1 j
    (fineEmbeddingChain_before_reachIndex E₀ rho hrho hrho1 hj)

lemma fineChainStepBeforeIndex_a_norm
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho < 1)
    (j : ℕ) (hj : j < fineReachIndex E₀ rho hrho hrho1) :
    ‖(fineChainStepBeforeIndex E₀ rho hrho hrho1 j hj).a‖ = rho := by
  exact fineEmbeddingChainStep_a_norm E₀ rho hrho hrho1 j
    (fineEmbeddingChain_before_reachIndex E₀ rho hrho hrho1 hj)

lemma fineChainStepBeforeIndex_realRadius
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho < 1)
    (j : ℕ) (hj : j < fineReachIndex E₀ rho hrho hrho1) :
    (fineChainStepBeforeIndex E₀ rho hrho hrho1 j hj).realRadius =
      fineLoewnerRadius rho := by
  exact omittedPointStep_realRadius_eq_fineLoewnerRadius hrho _
    (fineChainStepBeforeIndex_a_norm E₀ rho hrho hrho1 j hj)

lemma fineEmbeddingChain_deriv_succ_beforeIndex
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho < 1)
    (j : ℕ) (hj : j < fineReachIndex E₀ rho hrho hrho1) :
    ‖deriv (fineEmbeddingChain E₀ rho hrho hrho1 (j + 1)).toFun 0‖ =
      fineLoewnerGain rho *
        ‖deriv (fineEmbeddingChain E₀ rho hrho hrho1 j).toFun 0‖ := by
  exact omittedPointStep_deriv_norm_eq_fineLoewnerGain hrho
    (fineChainStepBeforeIndex E₀ rho hrho hrho1 j hj)
    (fineChainStepBeforeIndex_a_norm E₀ rho hrho hrho1 j hj)

lemma fineEmbeddingChain_deriv_formula_toIndex
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho < 1)
    (j : ℕ) (hj : j ≤ fineReachIndex E₀ rho hrho hrho1) :
    ‖deriv (fineEmbeddingChain E₀ rho hrho hrho1 j).toFun 0‖ =
      fineLoewnerGain rho ^ j * ‖deriv E₀.toFun 0‖ := by
  induction j with
  | zero => simp [fineEmbeddingChain]
  | succ j ih =>
      rw [fineEmbeddingChain_deriv_succ_beforeIndex E₀ rho hrho hrho1 j (by omega),
        ih (by omega), pow_succ']
      ring

lemma fineReachIndex_mul_mesh_le
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho < 1) :
    (fineReachIndex E₀ rho hrho hrho1 : ℝ) * fineLoewnerMesh rho ≤
      1 / ‖deriv E₀.toFun 0‖ := by
  let m := fineReachIndex E₀ rho hrho hrho1
  let g := fineLoewnerGain rho
  let h := fineLoewnerMesh rho
  let d₀ := ‖deriv E₀.toFun 0‖
  have hg : 1 < g := one_lt_fineLoewnerGain hrho hrho1
  have hh : 0 ≤ h := fineLoewnerMesh_nonneg hrho hrho1
  have hd₀ : 0 < d₀ := norm_pos_iff.mpr E₀.deriv_ne_zero
  have hradiusProduct := fineLoewnerRadius_mul_gain hrho
  have hhg : h * g = g - 1 := by
    dsimp only [h, g]
    unfold fineLoewnerMesh
    rw [sub_mul, one_mul, hradiusProduct]
  have hh_le : h ≤ g - 1 := by
    calc
      h = h * 1 := by ring
      _ ≤ h * g := mul_le_mul_of_nonneg_left hg.le hh
      _ = g - 1 := hhg
  have hBernoulli : 1 + (m : ℝ) * (g - 1) ≤ g ^ m :=
    one_add_mul_sub_le_pow (by linarith : (-1 : ℝ) ≤ g) m
  have hmh : (m : ℝ) * h ≤ g ^ m := by
    have hmul := mul_le_mul_of_nonneg_left hh_le (Nat.cast_nonneg m)
    linarith
  have hterminal : g ^ m * d₀ ≤ 1 := by
    rw [← fineEmbeddingChain_deriv_formula_toIndex E₀ rho hrho hrho1 m le_rfl]
    exact normalizedDiskEmbedding_derivNorm_le_one_unitBall
      (fineEmbeddingChain E₀ rho hrho hrho1 m)
  apply (le_div_iff₀ hd₀).2
  calc
    (m : ℝ) * h * d₀ ≤ g ^ m * d₀ :=
      mul_le_mul_of_nonneg_right hmh hd₀.le
    _ ≤ 1 := hterminal

lemma normalizedRotateTaylorVector_mem_box
    {E₀ E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (reach : E₀.ReachableFrom E) {eta : ℂ} (heta : ‖eta‖ = 1) :
    taylorCoeff (normalizedRotate reach.normalizedInverse eta) ∈
      normalizedTaylorBox E₀ := by
  intro n hn
  rw [mem_closedBall, dist_zero_right]
  by_cases hn0 : n = 0
  · subst n
    rw [taylorCoeff_zero
      (normalizedRotate_zero reach.normalizedInverse_zero)]
    have hd : 0 < ‖deriv E₀.toFun 0‖ := norm_pos_iff.mpr E₀.deriv_ne_zero
    norm_num
  · rw [taylorCoeff_normalizedRotate
      reach.normalizedInverse_differentiableOn heta (Nat.pos_of_ne_zero hn0),
      norm_mul, norm_pow, heta, one_pow, one_mul]
    exact taylorCoeff_normalizedInverse_norm_le reach n

lemma formalCoeffVector_normalizedRotate_mem
    {E₀ E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (reach : E₀.ReachableFrom E) {eta : ℂ} (heta : ‖eta‖ = 1) (N : ℕ) :
    seqToCoeffVector N
        (formalLogarithmicCoeff
          (taylorCoeff (normalizedRotate reach.normalizedInverse eta))) ∈
      formalCoeffBody E₀ N := by
  refine ⟨taylorCoeff (normalizedRotate reach.normalizedInverse eta),
    normalizedRotateTaylorVector_mem_box reach heta, ?_⟩
  rfl

noncomputable def fineCoeffVector
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho < 1)
    (N j : ℕ) : LoewnerCoeffVector N :=
  seqToCoeffVector N
    (formalLogarithmicCoeff
      (taylorCoeff (fineEmbeddingReach E₀ rho hrho hrho1 j).normalizedInverse))

noncomputable def fineRotatedCoeffVector
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho < 1)
    (N j : ℕ) (hj : j < fineReachIndex E₀ rho hrho hrho1) :
    LoewnerCoeffVector N :=
  let step := fineChainStepBeforeIndex E₀ rho hrho hrho1 j hj
  seqToCoeffVector N
    (formalLogarithmicCoeff
      (taylorCoeff (normalizedRotate
        (fineEmbeddingReach E₀ rho hrho hrho1 j).normalizedInverse
        (starRingEnd ℂ step.canonicalOmega))))

lemma canonicalLoewnerCoeff_coeffVectorToSeq {N : ℕ}
    (a : ℕ → ℂ) (r omega : ℂ) (n : Fin (N + 1)) :
    canonicalLoewnerCoeff
        (coeffVectorToSeq (seqToCoeffVector N a)) r omega n =
      canonicalLoewnerCoeff a r omega n := by
  unfold canonicalLoewnerCoeff
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ (n : ℕ) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hkN : k < N + 1 := hkn.trans_lt n.isLt
  rw [coeffVectorToSeq]
  simp only [hkN, dite_true, seqToCoeffVector_apply]

lemma fineCoeffVector_mem_body
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho < 1)
    (N j : ℕ) : fineCoeffVector E₀ rho hrho hrho1 N j ∈
      formalCoeffBody E₀ N := by
  exact formalCoeffVector_normalizedInverse_mem
    (fineEmbeddingReach E₀ rho hrho hrho1 j) N

lemma fineRotatedCoeffVector_mem_body
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho < 1)
    (N j : ℕ) (hj : j < fineReachIndex E₀ rho hrho hrho1) :
    fineRotatedCoeffVector E₀ rho hrho hrho1 N j hj ∈
      formalCoeffBody E₀ N := by
  let step := fineChainStepBeforeIndex E₀ rho hrho hrho1 j hj
  exact formalCoeffVector_normalizedRotate_mem
    (fineEmbeddingReach E₀ rho hrho hrho1 j)
    (by rw [Complex.norm_conj, step.norm_canonicalOmega]) N

lemma fineCoeffVector_succ_eq_canonical
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho < 1)
    (N j : ℕ) (hj : j < fineReachIndex E₀ rho hrho hrho1) :
    fineCoeffVector E₀ rho hrho hrho1 N (j + 1) =
      vectorCanonicalCoeff (fineLoewnerRadius rho : ℂ)
        (fineChainStepBeforeIndex E₀ rho hrho hrho1 j hj).canonicalOmega
        (fineRotatedCoeffVector E₀ rho hrho hrho1 N j hj) := by
  let hlt := fineEmbeddingChain_before_reachIndex E₀ rho hrho hrho1 hj
  let step := fineChainStepBeforeIndex E₀ rho hrho hrho1 j hj
  have hreach := fineEmbeddingReach_succ_of_lt E₀ rho hrho hrho1 j hlt
  funext n
  simp only [fineCoeffVector, fineRotatedCoeffVector, vectorCanonicalCoeff,
    seqToCoeffVector_apply]
  rw [canonicalLoewnerCoeff_coeffVectorToSeq]
  change formalLogarithmicCoeff
      (taylorCoeff (fineEmbeddingReach E₀ rho hrho hrho1 (j + 1)).normalizedInverse)
        n =
    canonicalLoewnerCoeff
      (formalLogarithmicCoeff
        (taylorCoeff (normalizedRotate
          (fineEmbeddingReach E₀ rho hrho hrho1 j).normalizedInverse
          (starRingEnd ℂ step.canonicalOmega))))
      (fineLoewnerRadius rho : ℂ) step.canonicalOmega n
  rw [hreach]
  rw [show fineEmbeddingChainStep E₀ rho hrho hrho1 j hlt = step by rfl]
  rw [step.formalLogarithmicCoeff_step
    (fineEmbeddingReach E₀ rho hrho hrho1 j) n]
  rw [fineChainStepBeforeIndex_realRadius E₀ rho hrho hrho1 j hj]

lemma fineRotatedCoeffVector_gap_eq
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho < 1)
    (N j : ℕ) (hj : j < fineReachIndex E₀ rho hrho hrho1) (t : ℝ) :
    vectorDeBrangesGap N t
        (fineRotatedCoeffVector E₀ rho hrho hrho1 N j hj) =
      vectorDeBrangesGap N t
        (fineCoeffVector E₀ rho hrho hrho1 N j) := by
  let step := fineChainStepBeforeIndex E₀ rho hrho hrho1 j hj
  simpa only [fineRotatedCoeffVector, fineCoeffVector, step] using
    vectorDeBrangesGap_formal_normalizedRotate
      (N := N) (t := t)
      (fineEmbeddingReach E₀ rho hrho hrho1 j).normalizedInverse_differentiableOn
      (by rw [Complex.norm_conj, step.norm_canonicalOmega])

lemma taylorCoeff_id_eq_seriesUnitCoeff (n : ℕ) :
    taylorCoeff id n = seriesUnitCoeff n := by
  change taylorCoeff (fun z : ℂ ↦ z) n = seriesUnitCoeff n
  simpa [seriesUnitCoeff] using taylorCoeff_power_monomial 1 n

lemma formalLogarithmicCoeff_seriesUnitCoeff (n : ℕ) :
    formalLogarithmicCoeff seriesUnitCoeff n = 0 := by
  rcases n with _ | n
  · simp [formalLogarithmicCoeff]
  · simp [formalLogarithmicCoeff, seriesUnitCoeff]

lemma fineEmbeddingReach_zero_normalizedInverse
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho < 1) :
    (fineEmbeddingReach E₀ rho hrho hrho1 0).normalizedInverse = id := by
  funext z
  simp [fineEmbeddingReach,
    NormalizedDiskEmbedding.ReachableFrom.normalizedInverse,
    NormalizedDiskEmbedding.ReachableFrom.inverseMap]

lemma fineCoeffVector_zero
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho < 1) (N : ℕ) :
    fineCoeffVector E₀ rho hrho hrho1 N 0 = 0 := by
  funext n
  change formalLogarithmicCoeff
    (taylorCoeff (fineEmbeddingReach E₀ rho hrho hrho1 0).normalizedInverse) n = 0
  rw [fineEmbeddingReach_zero_normalizedInverse E₀ rho hrho hrho1]
  have htaylor : taylorCoeff id = seriesUnitCoeff := by
    funext k
    exact taylorCoeff_id_eq_seriesUnitCoeff k
  rw [htaylor, formalLogarithmicCoeff_seriesUnitCoeff]

lemma explicitDeBrangesWeight_nonneg (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ deBrangesWeight N (fun k ↦ explicitDeBrangesTau N k t) := by
  let W : ℝ → ℝ := fun u ↦
    deBrangesWeight N (fun k ↦ explicitDeBrangesTau N k u)
  let Wdot : ℝ → ℝ := fun u ↦
    deBrangesWeightRate N (fun k ↦ explicitDeBrangesTauDot N k u)
  have hW (u : ℝ) : HasDerivAt W (Wdot u) u := by
    exact hasDerivAt_deBrangesWeight fun k hk ↦
      hasDerivAt_explicitDeBrangesTau N (k + 1) u
  have hWdot (u : ℝ) (hu : 0 ≤ u) : Wdot u ≤ 0 := by
    unfold Wdot deBrangesWeightRate
    apply Finset.sum_nonpos
    intro k hk
    exact div_nonpos_of_nonpos_of_nonneg
      (explicitDeBrangesTauDot_nonpos_of_gasper satisfiesGasperIdentities
        (by omega) (Finset.mem_range.mp hk) hu)
      (Nat.cast_nonneg (k + 1))
  have hanti : AntitoneOn W (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · intro u hu
      exact (hW u).continuousAt.continuousWithinAt
    · intro u hu
      exact (hW u).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [(hW u).deriv]
      apply hWdot u
      have hu' : u ∈ Ioi 0 := by simpa only [interior_Ici] using hu
      exact hu'.le
  apply le_of_tendsto (explicitDeBrangesWeight_tendsto_zero N)
  filter_upwards [eventually_ge_atTop t] with u hu
  exact hanti (Set.mem_Ici.mpr ht) (Set.mem_Ici.mpr (ht.trans hu)) hu

lemma fineCoeffVector_zero_gap_nonpos
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho < 1)
    (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    vectorDeBrangesGap N t
      (fineCoeffVector E₀ rho hrho hrho1 N 0) ≤ 0 := by
  rw [fineCoeffVector_zero E₀ rho hrho hrho1 N]
  have hseq : coeffVectorToSeq (0 : LoewnerCoeffVector N) = 0 := by
    funext k
    unfold coeffVectorToSeq
    split <;> simp
  unfold vectorDeBrangesGap
  rw [hseq]
  simp [deBrangesEnergy]
  exact explicitDeBrangesWeight_nonneg N ht

noncomputable def fineEnergyDelta
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (N : ℕ) (eps : ℝ) (heps : 0 < eps) : ℝ :=
  Classical.choose (exists_vectorDeBrangesGap_canonical_step_delta
    E₀ N (1 / ‖deriv E₀.toFun 0‖) heps)

lemma fineEnergyDelta_pos
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (N : ℕ) (eps : ℝ) (heps : 0 < eps) :
    0 < fineEnergyDelta E₀ N eps heps :=
  (Classical.choose_spec (exists_vectorDeBrangesGap_canonical_step_delta
    E₀ N (1 / ‖deriv E₀.toFun 0‖) heps)).1

lemma fineEnergyDelta_step
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (N : ℕ) (eps : ℝ) (heps : 0 < eps)
    (t h : ℝ) (c : LoewnerCoeffVector N) (omega : ℂ)
    (ht : t ∈ Icc 0 (1 / ‖deriv E₀.toFun 0‖))
    (hh : h ∈ Icc 0 (1 / 2 : ℝ))
    (hc : c ∈ formalCoeffBody E₀ N) (homega : ‖omega‖ = 1)
    (hdelta : h < fineEnergyDelta E₀ N eps heps) :
    vectorDeBrangesGap N t
        (vectorCanonicalCoeff (((1 - h : ℝ) : ℂ)) omega c) ≤
      vectorDeBrangesGap N (t + h) c + eps * h := by
  exact (Classical.choose_spec
    (exists_vectorDeBrangesGap_canonical_step_delta
      E₀ N (1 / ‖deriv E₀.toFun 0‖) heps)).2
    t h c omega ht hh hc homega hdelta

lemma fineCoeffVector_gap_succ_le
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho < 1)
    (N : ℕ) (eps : ℝ) (heps : 0 < eps)
    (hmeshHalf : fineLoewnerMesh rho ≤ 1 / 2)
    (hmeshDelta : fineLoewnerMesh rho < fineEnergyDelta E₀ N eps heps)
    (j : ℕ) (hj : j < fineReachIndex E₀ rho hrho hrho1)
    (t : ℝ) (ht : t ∈ Icc 0 (1 / ‖deriv E₀.toFun 0‖)) :
    vectorDeBrangesGap N t
        (fineCoeffVector E₀ rho hrho hrho1 N (j + 1)) ≤
      vectorDeBrangesGap N (t + fineLoewnerMesh rho)
          (fineCoeffVector E₀ rho hrho hrho1 N j) +
        eps * fineLoewnerMesh rho := by
  let step := fineChainStepBeforeIndex E₀ rho hrho hrho1 j hj
  have hmeshNonneg := fineLoewnerMesh_nonneg hrho hrho1
  have hraw := fineEnergyDelta_step E₀ N eps heps t (fineLoewnerMesh rho)
    (fineRotatedCoeffVector E₀ rho hrho hrho1 N j hj)
    step.canonicalOmega ht ⟨hmeshNonneg, hmeshHalf⟩
    (fineRotatedCoeffVector_mem_body E₀ rho hrho hrho1 N j hj)
    step.norm_canonicalOmega hmeshDelta
  have hradius : (((1 - fineLoewnerMesh rho : ℝ) : ℂ)) =
      (fineLoewnerRadius rho : ℂ) := by
    unfold fineLoewnerMesh
    congr 1
    ring
  rw [hradius] at hraw
  rw [← fineCoeffVector_succ_eq_canonical
    E₀ rho hrho hrho1 N j hj] at hraw
  rw [fineRotatedCoeffVector_gap_eq
    E₀ rho hrho hrho1 N j hj (t + fineLoewnerMesh rho)] at hraw
  exact hraw

lemma fineTerminalCoeffVector_gap_le
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho < 1)
    (N : ℕ) (eps : ℝ) (heps : 0 < eps)
    (hmeshHalf : fineLoewnerMesh rho ≤ 1 / 2)
    (hmeshDelta : fineLoewnerMesh rho < fineEnergyDelta E₀ N eps heps) :
    vectorDeBrangesGap N 0
        (fineCoeffVector E₀ rho hrho hrho1 N
          (fineReachIndex E₀ rho hrho hrho1)) ≤
      eps / ‖deriv E₀.toFun 0‖ := by
  let m := fineReachIndex E₀ rho hrho hrho1
  let h := fineLoewnerMesh rho
  have hh : 0 ≤ h := fineLoewnerMesh_nonneg hrho hrho1
  have hmh : (m : ℝ) * h ≤ 1 / ‖deriv E₀.toFun 0‖ := by
    exact fineReachIndex_mul_mesh_le E₀ rho hrho hrho1
  have hind : ∀ j : ℕ, j ≤ m →
      vectorDeBrangesGap N (((m - j : ℕ) : ℝ) * h)
          (fineCoeffVector E₀ rho hrho hrho1 N j) ≤
        vectorDeBrangesGap N ((m : ℝ) * h)
            (fineCoeffVector E₀ rho hrho hrho1 N 0) +
          (j : ℝ) * eps * h := by
    intro j
    induction j with
    | zero =>
        intro hj
        simp
    | succ j ih =>
        intro hj
        have hjm : j < m := by omega
        have ih' := ih (by omega)
        let t : ℝ := (((m - (j + 1) : ℕ) : ℝ) * h)
        have ht0 : 0 ≤ t := mul_nonneg (Nat.cast_nonneg _) hh
        have htM : t ≤ (m : ℝ) * h := by
          apply mul_le_mul_of_nonneg_right _ hh
          exact_mod_cast Nat.sub_le m (j + 1)
        have ht : t ∈ Icc 0 (1 / ‖deriv E₀.toFun 0‖) :=
          ⟨ht0, htM.trans hmh⟩
        have hstep := fineCoeffVector_gap_succ_le E₀ rho hrho hrho1
          N eps heps hmeshHalf hmeshDelta j hjm t ht
        have hnat : m - (j + 1) + 1 = m - j := by omega
        have htime : t + h = (((m - j : ℕ) : ℝ) * h) := by
          dsimp only [t]
          calc
            ((m - (j + 1) : ℕ) : ℝ) * h + h =
                (((m - (j + 1) : ℕ) : ℝ) + 1) * h := by ring
            _ = ((m - (j + 1) + 1 : ℕ) : ℝ) * h := by push_cast; ring
            _ = ((m - j : ℕ) : ℝ) * h := by rw [hnat]
        rw [htime] at hstep
        calc
          vectorDeBrangesGap N (((m - (j + 1) : ℕ) : ℝ) * h)
              (fineCoeffVector E₀ rho hrho hrho1 N (j + 1)) =
              vectorDeBrangesGap N t
                (fineCoeffVector E₀ rho hrho hrho1 N (j + 1)) := rfl
          _ ≤ vectorDeBrangesGap N (((m - j : ℕ) : ℝ) * h)
                (fineCoeffVector E₀ rho hrho hrho1 N j) + eps * h := hstep
          _ ≤ (vectorDeBrangesGap N ((m : ℝ) * h)
                  (fineCoeffVector E₀ rho hrho hrho1 N 0) +
                (j : ℝ) * eps * h) + eps * h :=
              by linarith
          _ = vectorDeBrangesGap N ((m : ℝ) * h)
                (fineCoeffVector E₀ rho hrho hrho1 N 0) +
              ((j + 1 : ℕ) : ℝ) * eps * h := by push_cast; ring
  have hterminal := hind m le_rfl
  simp only [Nat.sub_self, Nat.cast_zero, zero_mul] at hterminal
  have hzero := fineCoeffVector_zero_gap_nonpos E₀ rho hrho hrho1 N
    (mul_nonneg (Nat.cast_nonneg m) hh)
  calc
    vectorDeBrangesGap N 0
        (fineCoeffVector E₀ rho hrho hrho1 N m) ≤
        vectorDeBrangesGap N ((m : ℝ) * h)
            (fineCoeffVector E₀ rho hrho hrho1 N 0) +
          (m : ℝ) * eps * h := hterminal
    _ ≤ 0 + (m : ℝ) * eps * h := by linarith
    _ = eps * ((m : ℝ) * h) := by ring
    _ ≤ eps * (1 / ‖deriv E₀.toFun 0‖) :=
      mul_le_mul_of_nonneg_left hmh heps.le
    _ = eps / ‖deriv E₀.toFun 0‖ := by ring

noncomputable def fineRho (j : ℕ) : ℝ :=
  1 - 1 / (((j + 1 : ℕ) : ℝ) + 1)

lemma fineRho_pos (j : ℕ) : 0 < fineRho j := by
  have hden : (1 : ℝ) < ((j + 1 : ℕ) : ℝ) + 1 := by
    norm_num
    positivity
  have hden0 : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) + 1 := by linarith
  have hfrac : 1 / (((j + 1 : ℕ) : ℝ) + 1) < 1 :=
    (div_lt_one hden0).2 hden
  unfold fineRho
  linarith

lemma fineRho_lt_one (j : ℕ) : fineRho j < 1 := by
  have hden : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) + 1 := by positivity
  have hfrac : 0 < 1 / (((j + 1 : ℕ) : ℝ) + 1) := one_div_pos.mpr hden
  unfold fineRho
  linarith

lemma tendsto_fineRho : Tendsto fineRho atTop (nhds 1) := by
  have hrecip :
      Tendsto (fun j : ℕ ↦ 1 / (((j + 1 : ℕ) : ℝ) + 1)) atTop (nhds 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (Filter.tendsto_add_atTop_nat 1)
  have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have ht := hone.sub hrecip
  norm_num at ht
  change Tendsto (fun j : ℕ ↦
    1 - 1 / (((j + 1 : ℕ) : ℝ) + 1)) atTop (nhds 1)
  convert ht using 1
  funext j
  push_cast
  simp [div_eq_mul_inv]

lemma tendsto_fineLoewnerRadius_fineRho :
    Tendsto (fun j ↦ fineLoewnerRadius (fineRho j)) atTop (nhds 1) := by
  have hcont : ContinuousAt fineLoewnerRadius 1 := by
    unfold fineLoewnerRadius
    exact (continuousAt_const.mul Real.continuous_sqrt.continuousAt).div
      (continuousAt_const.add continuousAt_id) (by norm_num)
  have ht := hcont.tendsto.comp tendsto_fineRho
  change Tendsto (fun j ↦ fineLoewnerRadius (fineRho j)) atTop
    (nhds (fineLoewnerRadius 1)) at ht
  norm_num [fineLoewnerRadius] at ht ⊢
  exact ht

lemma tendsto_fineLoewnerMesh_fineRho :
    Tendsto (fun j ↦ fineLoewnerMesh (fineRho j)) atTop (nhds 0) := by
  have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  simpa only [fineLoewnerMesh, sub_self] using
    hone.sub tendsto_fineLoewnerRadius_fineRho

noncomputable def fineTerminalEmbedding
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0) (j : ℕ) :
    NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0 :=
  fineEmbeddingChain E₀ (fineRho j) (fineRho_pos j) (fineRho_lt_one j)
    (fineReachIndex E₀ (fineRho j) (fineRho_pos j) (fineRho_lt_one j))

noncomputable def fineTerminalReach
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0) (j : ℕ) :
    E₀.ReachableFrom (fineTerminalEmbedding E₀ j) :=
  fineEmbeddingReach E₀ (fineRho j) (fineRho_pos j) (fineRho_lt_one j)
    (fineReachIndex E₀ (fineRho j) (fineRho_pos j) (fineRho_lt_one j))

lemma fineTerminalEmbedding_deriv_norm_lower
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0) (j : ℕ) :
    fineRho j ≤ ‖deriv (fineTerminalEmbedding E₀ j).toFun 0‖ := by
  exact fineReachIndex_spec E₀ (fineRho j) (fineRho_pos j) (fineRho_lt_one j)

lemma tendsto_fineTerminalEmbedding_deriv_norm
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0) :
    Tendsto (fun j ↦ ‖deriv (fineTerminalEmbedding E₀ j).toFun 0‖)
      atTop (nhds 1) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_fineRho
    tendsto_const_nhds
    (fun j ↦ fineTerminalEmbedding_deriv_norm_lower E₀ j)
    (fun j ↦ (fineTerminalEmbedding E₀ j).deriv_norm_le_one)

noncomputable def NormalizedDiskEmbedding.ReachableFrom.explicitPhaseCorrectedInverse
    {E₀ E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (reach : E₀.ReachableFrom E) (w : ℂ) : ℂ :=
  reach.inverseMap (E.phaseFactor⁻¹ * w)

lemma NormalizedDiskEmbedding.ReachableFrom.explicitPhaseCorrectedInverse_mapsTo_unitBall
    {E₀ E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (reach : E₀.ReachableFrom E) :
    MapsTo reach.explicitPhaseCorrectedInverse
      (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
  apply reach.inverseMap_mapsTo_unitBall.comp
  intro w hw
  rw [mem_ball_zero_iff, norm_mul, norm_inv, E.norm_phaseFactor,
    inv_one, one_mul]
  simpa [mem_ball_zero_iff] using hw

lemma NormalizedDiskEmbedding.ReachableFrom.explicitPhaseCorrectedInverse_differentiableOn
    {E₀ E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (reach : E₀.ReachableFrom E) :
    DifferentiableOn ℂ reach.explicitPhaseCorrectedInverse
      (ball (0 : ℂ) 1) := by
  apply reach.inverseMap_differentiableOn.comp
  · fun_prop
  · intro w hw
    rw [mem_ball_zero_iff, norm_mul, norm_inv, E.norm_phaseFactor,
      inv_one, one_mul]
    simpa [mem_ball_zero_iff] using hw

@[simp]
lemma NormalizedDiskEmbedding.ReachableFrom.explicitPhaseCorrectedInverse_zero
    {E₀ E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (reach : E₀.ReachableFrom E) :
    reach.explicitPhaseCorrectedInverse 0 = 0 := by
  simp [NormalizedDiskEmbedding.ReachableFrom.explicitPhaseCorrectedInverse,
    reach.inverseMap_zero]

lemma NormalizedDiskEmbedding.ReachableFrom.explicitPhaseCorrectedInverse_phaseNormalize
    {E₀ E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (reach : E₀.ReachableFrom E) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    reach.explicitPhaseCorrectedInverse (E.phaseNormalize z) = E₀ z := by
  have hp : E.phaseFactor ≠ 0 := by
    rw [← norm_ne_zero_iff, E.norm_phaseFactor]
    norm_num
  rw [NormalizedDiskEmbedding.ReachableFrom.explicitPhaseCorrectedInverse,
    NormalizedDiskEmbedding.phaseNormalize, ← mul_assoc, inv_mul_cancel₀ hp, one_mul]
  exact reach.inverseMap_apply hz

lemma tendstoLocallyUniformlyOn_explicitPhaseCorrectedInverse
    {E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    {E : ℕ → NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (reach : ∀ j, E₀.ReachableFrom (E j))
    (hE : Tendsto (fun j ↦ ‖deriv (E j).toFun 0‖) atTop (nhds 1)) :
    TendstoLocallyUniformlyOn
      (fun j ↦ (reach j).explicitPhaseCorrectedInverse) E₀.toFun atTop
        (ball (0 : ℂ) 1) := by
  have hphase :=
    tendstoLocallyUniformlyOn_phaseNormalize_of_deriv_norm_tendsto_one hE
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball] at hphase ⊢
  intro K hKU hK
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · rw [tendstoUniformlyOn_iff]
    intro epsilon hepsilon
    exact Eventually.of_forall fun j z hz ↦ hz.elim
  obtain ⟨z₀, hz₀, hz₀max⟩ :=
    hK.exists_isMaxOn hKne continuous_norm.continuousOn
  let r := ‖z₀‖
  let gap := 1 - r
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr1 : r < 1 := by
    simpa only [r, mem_ball_zero_iff] using hKU hz₀
  have hgap : 0 < gap := sub_pos.mpr hr1
  have hKr : ∀ z ∈ K, ‖z‖ ≤ r := by
    intro z hz
    exact hz₀max hz
  have hphaseK := hphase K hKU hK
  rw [tendstoUniformlyOn_iff] at hphaseK ⊢
  intro epsilon hepsilon
  let delta := min (gap / 2) (epsilon * gap / 2)
  have hdelta : 0 < delta := lt_min (by positivity) (by positivity)
  filter_upwards [hphaseK delta hdelta] with j hj
  intro z hz
  have hzNorm : ‖z‖ ≤ r := hKr z hz
  have hzBall : z ∈ ball (0 : ℂ) 1 := hKU hz
  have herror : dist ((E j).phaseNormalize z) z < delta := by
    simpa only [id_eq, dist_comm] using hj z hz
  have herrorGap : dist ((E j).phaseNormalize z) z < gap := by
    exact (herror.trans_le (min_le_left _ _)).trans (half_lt_self hgap)
  have hsmallBall : ball z gap ⊆ ball (0 : ℂ) 1 := by
    intro w hw
    rw [mem_ball, dist_zero_right]
    have hwz : ‖w - z‖ < gap := by
      simpa [dist_eq_norm] using hw
    calc
      ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
        simpa only [sub_add_cancel] using norm_add_le (w - z) z
      _ < gap + r := add_lt_add_of_lt_of_le hwz hzNorm
      _ = 1 := by simp [gap]
  have hmaps : MapsTo (reach j).explicitPhaseCorrectedInverse (ball z gap)
      (closedBall ((reach j).explicitPhaseCorrectedInverse z) 2) := by
    intro w hw
    have hAw := (reach j).explicitPhaseCorrectedInverse_mapsTo_unitBall
      (hsmallBall hw)
    have hAz := (reach j).explicitPhaseCorrectedInverse_mapsTo_unitBall hzBall
    rw [mem_closedBall]
    calc
      dist ((reach j).explicitPhaseCorrectedInverse w)
          ((reach j).explicitPhaseCorrectedInverse z) ≤
          ‖(reach j).explicitPhaseCorrectedInverse w‖ +
            ‖(reach j).explicitPhaseCorrectedInverse z‖ :=
        dist_le_norm_add_norm _ _
      _ ≤ 2 := by
        rw [mem_ball_zero_iff] at hAw hAz
        linarith
  have hschwarz := Complex.dist_le_div_mul_dist_of_mapsTo_ball
    ((reach j).explicitPhaseCorrectedInverse_differentiableOn.mono hsmallBall)
    hmaps herrorGap
  have hscaled : 2 / gap * delta ≤ epsilon := by
    calc
      2 / gap * delta ≤ 2 / gap * (epsilon * gap / 2) := by
        exact mul_le_mul_of_nonneg_left (min_le_right _ _)
          (div_nonneg (by norm_num) hgap.le)
      _ = epsilon := by field_simp
  rw [← (reach j).explicitPhaseCorrectedInverse_phaseNormalize hzBall]
  exact hschwarz.trans_lt
    ((mul_lt_mul_of_pos_left herror (div_pos (by norm_num) hgap)).trans_le hscaled)

lemma NormalizedDiskEmbedding.ReachableFrom.deriv_explicitPhaseCorrectedInverse
    {E₀ E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (reach : E₀.ReachableFrom E) :
    deriv reach.explicitPhaseCorrectedInverse 0 =
      deriv reach.inverseMap 0 * E.phaseFactor⁻¹ := by
  have hinv : DifferentiableAt ℂ reach.inverseMap 0 :=
    reach.inverseMap_differentiableOn.differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self zero_lt_one))
  have hinner : HasDerivAt (fun z : ℂ ↦ E.phaseFactor⁻¹ * z)
      E.phaseFactor⁻¹ 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_mul E.phaseFactor⁻¹
  change deriv (reach.inverseMap ∘ fun z : ℂ ↦ E.phaseFactor⁻¹ * z) 0 = _
  simpa using (hinv.hasDerivAt.comp_of_eq 0 hinner (by simp)).deriv

lemma NormalizedDiskEmbedding.ReachableFrom.deriv_explicitPhaseCorrectedInverse_ne_zero
    {E₀ E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (reach : E₀.ReachableFrom E) :
    deriv reach.explicitPhaseCorrectedInverse 0 ≠ 0 := by
  rw [reach.deriv_explicitPhaseCorrectedInverse]
  apply mul_ne_zero reach.inverseMap_deriv_ne_zero
  exact inv_ne_zero (norm_ne_zero_iff.mp (by rw [E.norm_phaseFactor]; norm_num))

noncomputable def NormalizedDiskEmbedding.ReachableFrom.explicitNormalizedPhaseCorrectedInverse
    {E₀ E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (reach : E₀.ReachableFrom E) (z : ℂ) : ℂ :=
  reach.explicitPhaseCorrectedInverse z /
    deriv reach.explicitPhaseCorrectedInverse 0

lemma NormalizedDiskEmbedding.ReachableFrom.taylorCoeff_explicitNormalizedPhaseCorrectedInverse
    {E₀ E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (reach : E₀.ReachableFrom E) (n : ℕ) :
    taylorCoeff reach.explicitNormalizedPhaseCorrectedInverse n =
      taylorCoeff reach.explicitPhaseCorrectedInverse n /
        deriv reach.explicitPhaseCorrectedInverse 0 := by
  exact taylorCoeff_div_const reach.explicitPhaseCorrectedInverse
    (deriv reach.explicitPhaseCorrectedInverse 0) n

lemma tendsto_explicitNormalizedPhaseCorrectedInverse_taylorCoeff
    {E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    {E : ℕ → NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (reach : ∀ j, E₀.ReachableFrom (E j))
    (hE : Tendsto (fun j ↦ ‖deriv (E j).toFun 0‖) atTop (nhds 1))
    (n : ℕ) :
    Tendsto
      (fun j ↦ taylorCoeff
        (reach j).explicitNormalizedPhaseCorrectedInverse n) atTop
      (nhds (taylorCoeff (fun z ↦ E₀ z / deriv E₀.toFun 0) n)) := by
  have hlocal := tendstoLocallyUniformlyOn_explicitPhaseCorrectedInverse reach hE
  have hcoeff : ∀ k : ℕ,
      Tendsto (fun j ↦ taylorCoeff (reach j).explicitPhaseCorrectedInverse k)
        atTop (nhds (taylorCoeff E₀.toFun k)) := by
    intro k
    exact tendsto_taylorCoeff_of_locallyUniformlyOn isOpen_ball
      (mem_ball_self zero_lt_one) hlocal
      (fun j ↦ (reach j).explicitPhaseCorrectedInverse_differentiableOn) k
  have hderiv : Tendsto
      (fun j ↦ deriv (reach j).explicitPhaseCorrectedInverse 0)
      atTop (nhds (deriv E₀.toFun 0)) := by
    simpa [taylorCoeff] using hcoeff 1
  rw [taylorCoeff_div_const]
  simp_rw [NormalizedDiskEmbedding.ReachableFrom.taylorCoeff_explicitNormalizedPhaseCorrectedInverse]
  exact (hcoeff n).div hderiv E₀.deriv_ne_zero

lemma NormalizedDiskEmbedding.ReachableFrom.explicitNormalizedPhaseCorrectedInverse_eq_rotate
    {E₀ E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (reach : E₀.ReachableFrom E) :
    reach.explicitNormalizedPhaseCorrectedInverse =
      normalizedRotate reach.normalizedInverse E.phaseFactor⁻¹ := by
  have heta : E.phaseFactor⁻¹ ≠ 0 :=
    inv_ne_zero (norm_ne_zero_iff.mp (by rw [E.norm_phaseFactor]; norm_num))
  funext z
  unfold NormalizedDiskEmbedding.ReachableFrom.explicitNormalizedPhaseCorrectedInverse
    normalizedRotate NormalizedDiskEmbedding.ReachableFrom.normalizedInverse
  rw [reach.deriv_explicitPhaseCorrectedInverse]
  unfold NormalizedDiskEmbedding.ReachableFrom.explicitPhaseCorrectedInverse
  field_simp [reach.inverseMap_deriv_ne_zero, heta]

lemma fineTerminal_normalized_gap_eq
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (N j : ℕ) (t : ℝ) :
    vectorDeBrangesGap N t
        (seqToCoeffVector N
          (formalLogarithmicCoeff
            (taylorCoeff
              (fineTerminalReach E₀ j).explicitNormalizedPhaseCorrectedInverse))) =
      vectorDeBrangesGap N t
        (fineCoeffVector E₀ (fineRho j) (fineRho_pos j) (fineRho_lt_one j)
          N (fineReachIndex E₀ (fineRho j) (fineRho_pos j) (fineRho_lt_one j))) := by
  rw [(fineTerminalReach E₀ j).explicitNormalizedPhaseCorrectedInverse_eq_rotate]
  exact vectorDeBrangesGap_formal_normalizedRotate
    (fineTerminalReach E₀ j).normalizedInverse_differentiableOn
    (by rw [norm_inv, (fineTerminalEmbedding E₀ j).norm_phaseFactor, inv_one])

lemma continuous_vectorDeBrangesGap (N : ℕ) (t : ℝ) :
    Continuous (vectorDeBrangesGap N t) := by
  rw [continuous_iff_continuousAt]
  intro c
  unfold vectorDeBrangesGap deBrangesEnergy
  apply ContinuousAt.sub
  · apply continuousAt_finsetSum_real
    intro k hk
    have hkN : k + 1 < N + 1 := Nat.succ_lt_succ (Finset.mem_range.mp hk)
    have hc : ContinuousAt
        (fun d : LoewnerCoeffVector N ↦ coeffVectorToSeq d (k + 1)) c :=
      continuousAt_coeffVectorToSeq hkN id continuousAt_id
    exact (continuousAt_const.mul continuousAt_const).mul (hc.norm.pow 2)
  · exact continuousAt_const

noncomputable def fineTerminalNormalizedCoeffVector
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (N j : ℕ) : LoewnerCoeffVector N :=
  seqToCoeffVector N
    (formalLogarithmicCoeff
      (taylorCoeff
        (fineTerminalReach E₀ j).explicitNormalizedPhaseCorrectedInverse))

lemma tendsto_fineTerminalNormalizedCoeffVector
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0) (N : ℕ) :
    Tendsto (fineTerminalNormalizedCoeffVector E₀ N) atTop
      (nhds (seqToCoeffVector N
        (formalLogarithmicCoeff
          (taylorCoeff (fun z ↦ E₀ z / deriv E₀.toFun 0))))) := by
  apply tendsto_pi_nhds.2
  intro n
  change Tendsto
    (fun j ↦ formalLogarithmicCoeff
      (taylorCoeff
        (fineTerminalReach E₀ j).explicitNormalizedPhaseCorrectedInverse) n)
    atTop
    (nhds (formalLogarithmicCoeff
      (taylorCoeff (fun z ↦ E₀ z / deriv E₀.toFun 0)) n))
  apply tendsto_formalLogarithmicCoeff
  intro k
  exact tendsto_explicitNormalizedPhaseCorrectedInverse_taylorCoeff
    (E := fineTerminalEmbedding E₀) (fineTerminalReach E₀)
    (tendsto_fineTerminalEmbedding_deriv_norm E₀) k

lemma tendsto_fineTerminalNormalizedGap
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0) (N : ℕ) :
    Tendsto (fun j ↦ vectorDeBrangesGap N 0
        (fineTerminalNormalizedCoeffVector E₀ N j)) atTop
      (nhds (vectorDeBrangesGap N 0
        (seqToCoeffVector N
          (formalLogarithmicCoeff
            (taylorCoeff (fun z ↦ E₀ z / deriv E₀.toFun 0)))))) := by
  exact (continuous_vectorDeBrangesGap N 0).continuousAt.tendsto.comp
    (tendsto_fineTerminalNormalizedCoeffVector E₀ N)

lemma normalizedEmbedding_formal_gap_nonpos
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0) (N : ℕ) :
    vectorDeBrangesGap N 0
        (seqToCoeffVector N
          (formalLogarithmicCoeff
            (taylorCoeff (fun z ↦ E₀ z / deriv E₀.toFun 0)))) ≤ 0 := by
  let d₀ := ‖deriv E₀.toFun 0‖
  have hd₀ : 0 < d₀ := norm_pos_iff.mpr E₀.deriv_ne_zero
  have happrox : ∀ eps : ℝ, 0 < eps →
      vectorDeBrangesGap N 0
          (seqToCoeffVector N
            (formalLogarithmicCoeff
              (taylorCoeff (fun z ↦ E₀ z / deriv E₀.toFun 0)))) ≤
        eps / d₀ := by
    intro eps heps
    have hhalf : ∀ᶠ j : ℕ in atTop,
        fineLoewnerMesh (fineRho j) ≤ 1 / 2 := by
      filter_upwards
        [tendsto_fineLoewnerMesh_fineRho.eventually_lt_const
          (by norm_num : (0 : ℝ) < 1 / 2)] with j hj
      exact hj.le
    have hdelta : ∀ᶠ j : ℕ in atTop,
        fineLoewnerMesh (fineRho j) < fineEnergyDelta E₀ N eps heps :=
      tendsto_fineLoewnerMesh_fineRho.eventually_lt_const
        (fineEnergyDelta_pos E₀ N eps heps)
    have hbound : ∀ᶠ j : ℕ in atTop,
        vectorDeBrangesGap N 0
            (fineTerminalNormalizedCoeffVector E₀ N j) ≤ eps / d₀ := by
      filter_upwards [hhalf, hdelta] with j hjHalf hjDelta
      change vectorDeBrangesGap N 0
        (seqToCoeffVector N
          (formalLogarithmicCoeff
            (taylorCoeff
              (fineTerminalReach E₀ j).explicitNormalizedPhaseCorrectedInverse))) ≤
        eps / d₀
      rw [fineTerminal_normalized_gap_eq E₀ N j 0]
      exact fineTerminalCoeffVector_gap_le E₀ (fineRho j)
        (fineRho_pos j) (fineRho_lt_one j) N eps heps hjHalf hjDelta
    exact le_of_tendsto (tendsto_fineTerminalNormalizedGap E₀ N) hbound
  refine le_of_forall_pos_le_add fun delta hdelta ↦ ?_
  have hbound := happrox (delta * d₀) (mul_pos hdelta hd₀)
  have heq : delta * d₀ / d₀ = delta := by field_simp
  simpa [heq] using hbound

lemma vectorFormalGap_zero_eq_milinFunctional
    {f L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R))
    (hL : DifferentiableOn ℂ L (ball 0 R)) (hL0 : L 0 = 0)
    (hf1 : taylorCoeff f 1 = 1)
    (hexp : ∀ z ∈ ball (0 : ℂ) R,
      Complex.exp (L z) = dslope f 0 z) (N : ℕ) :
    vectorDeBrangesGap N 0
        (seqToCoeffVector N
          (formalLogarithmicCoeff (taylorCoeff f))) =
      milinFunctional L N := by
  rw [milinFunctional_eq_weighted]
  unfold vectorDeBrangesGap deBrangesEnergy deBrangesWeight
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : k + 1 < N + 1 := Nat.succ_lt_succ (Finset.mem_range.mp hk)
  have hkLe : k + 1 ≤ N := Finset.mem_range.mp hk
  rw [show coeffVectorToSeq
      (seqToCoeffVector N (formalLogarithmicCoeff (taylorCoeff f))) (k + 1) =
        formalLogarithmicCoeff (taylorCoeff f) (k + 1) by
      simp [coeffVectorToSeq, hkN]]
  change
    ((k + 1 : ℕ) : ℝ) * explicitDeBrangesTau N (k + 1) 0 *
          ‖formalLogarithmicCoeff (taylorCoeff f) (k + 1)‖ ^ 2 -
        explicitDeBrangesTau N (k + 1) 0 / ((k + 1 : ℕ) : ℝ) = _
  rw [explicitDeBrangesTau_zero (by omega) hkLe,
    formalLogarithmicCoeff_eq_logarithmicCoeff hR hf hL hL0 hf1 hexp (k + 1)]
  have hsub : N - (k + 1) + 1 = N - k := by omega
  rw [hsub]
  ring

lemma satisfiesMilin_of_extended_normalized_univalent
    {f L : ℂ → ℂ} {R : ℝ} (hR1 : 1 < R)
    (hf : NormalizedUnivalentOn f R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) (hL0 : L 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) R,
      Complex.exp (L z) = dslope f 0 z) :
    SatisfiesMilin L := by
  rcases exists_scaledNormalizedDiskEmbedding hR1 hf with
    ⟨C, hC1, E₀, hE₀⟩
  have hC0 : (C : ℂ) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans hC1).ne'
  have hzeroR : (0 : ℂ) ∈ ball 0 R :=
    mem_ball_self (zero_lt_one.trans hR1)
  have hfAt : DifferentiableAt ℂ f 0 :=
    (hf.1 0 hzeroR).differentiableAt (isOpen_ball.mem_nhds hzeroR)
  have hEderiv : deriv E₀.toFun 0 = 1 / (C : ℂ) := by
    rw [hE₀]
    simpa only [hf.2.2.2, one_div] using
      (hfAt.hasDerivAt.div_const (C : ℂ)).deriv
  have hnormalized : (fun z ↦ E₀ z / deriv E₀.toFun 0) = f := by
    funext z
    rw [hEderiv, hE₀]
    field_simp [hC0]
  intro N
  have hgap := normalizedEmbedding_formal_gap_nonpos E₀ N
  rw [hnormalized] at hgap
  rw [vectorFormalGap_zero_eq_milinFunctional
    (zero_lt_one.trans hR1) hf.1 hL hL0
    (taylorCoeff_one hf.2.2.2) hexp N] at hgap
  exact hgap

lemma normalized_coeff_bound_of_extended_univalent
    {f L : ℂ → ℂ} {R : ℝ} (hR1 : 1 < R)
    (hf : NormalizedUnivalentOn f R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) (hL0 : L 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) R,
      Complex.exp (L z) = dslope f 0 z) (n : ℕ) :
    ‖taylorCoeff f n‖ ≤ n := by
  exact normalized_coeff_bound_of_milin_only (zero_lt_one.trans hR1)
    hf hL hL0 hexp
    (satisfiesMilin_of_extended_normalized_univalent hR1 hf hL hL0 hexp) n

lemma normalized_coeff_bound
    {f : ℂ → ℂ}
    (diff : DifferentiableOn ℂ f (ball 0 1))
    (inj : (ball (0 : ℂ) 1).InjOn f)
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1) (n : ℕ) :
    ‖taylorCoeff f n‖ ≤ n := by
  apply taylorCoeff_norm_le_of_extendedDisk diff inj h0 h1
  intro g R hR hg
  rcases exists_normalized_log_dslope (zero_lt_one.trans hR) hg with
    ⟨L, hL, hL0, hexp⟩
  exact normalized_coeff_bound_of_extended_univalent hR hg hL hL0 hexp n

end Submission
