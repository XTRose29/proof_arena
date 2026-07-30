import Submission.Frostman

namespace Submission.Helpers

open LeanEval.Dynamics
open MeasureTheory
open Filter Topology

lemma negMulLog_le_mul_add_exp_neg {p a : ℝ} (hp : 0 ≤ p) :
    Real.negMulLog p ≤ a * p + Real.exp (-a) := by
  by_cases hpzero : p = 0
  · subst p
    simpa using (Real.exp_pos (-a)).le
  have hqnonneg : 0 ≤ Real.exp a * p :=
    mul_nonneg (Real.exp_pos a).le hp
  have hbase := Real.negMulLog_le_one_sub_self hqnonneg
  have hid : Real.negMulLog p =
      Real.exp (-a) * Real.negMulLog (Real.exp a * p) + a * p := by
    simp only [Real.negMulLog_def]
    rw [Real.log_mul (Real.exp_ne_zero a) hpzero, Real.log_exp]
    rw [Real.exp_neg]
    field_simp
    ring
  rw [hid]
  calc
    Real.exp (-a) * Real.negMulLog (Real.exp a * p) + a * p ≤
        Real.exp (-a) * (1 - Real.exp a * p) + a * p := by
      gcongr
    _ ≤ a * p + Real.exp (-a) := by
      have hexp : Real.exp (-a) * Real.exp a = 1 := by
        rw [← Real.exp_add]
        simp
      rw [mul_sub, mul_one, ← mul_assoc, hexp, one_mul]
      linarith

lemma sum_negMulLog_le_mul_sum_add_card_exp_neg
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (Q : Finset (Set M)) (a : ℝ) :
    (∑ A ∈ Q, Real.negMulLog (mu.real A)) ≤
      a * (∑ A ∈ Q, mu.real A) + Q.card * Real.exp (-a) := by
  calc
    (∑ A ∈ Q, Real.negMulLog (mu.real A)) ≤
        ∑ A ∈ Q, (a * mu.real A + Real.exp (-a)) := by
      apply Finset.sum_le_sum
      intro A hA
      exact negMulLog_le_mul_add_exp_neg measureReal_nonneg
    _ = a * (∑ A ∈ Q, mu.real A) + Q.card * Real.exp (-a) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      simp

lemma negMulLog_le_mul_of_exp_neg_le
    {p c : ℝ} (hp : Real.exp (-c) ≤ p) :
    Real.negMulLog p ≤ c * p := by
  have hp_pos : 0 < p := (Real.exp_pos (-c)).trans_le hp
  have hlog : -c ≤ Real.log p :=
    (Real.le_log_iff_exp_le hp_pos).2 hp
  rw [Real.negMulLog_def]
  nlinarith [mul_le_mul_of_nonneg_left hlog hp_pos.le]

lemma partitionEntropy_le_threshold_add_light_mass
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    {P : Finset (Set M)} (hP : IsMeasurablePartition mu P)
    {c : ℝ} (hc : 0 ≤ c) (a : ℝ) :
    partitionEntropy mu P ≤
      c + a * (∑ A ∈ lightAtoms mu P c, mu.real A) +
        (lightAtoms mu P c).card * Real.exp (-a) := by
  classical
  have hsplit : partitionEntropy mu P =
      (∑ A ∈ lightAtoms mu P c, Real.negMulLog (mu.real A)) +
        ∑ A ∈ heavyAtoms mu P c, Real.negMulLog (mu.real A) := by
    rw [partitionEntropy]
    have h := Finset.sum_filter_add_sum_filter_not P
      (fun A => mu.real A < Real.exp (-c))
      (fun A => Real.negMulLog (mu.real A))
    simpa [lightAtoms, heavyAtoms, measureReal_def, not_lt] using h.symm
  have hlight :
      (∑ A ∈ lightAtoms mu P c, Real.negMulLog (mu.real A)) ≤
        a * (∑ A ∈ lightAtoms mu P c, mu.real A) +
          (lightAtoms mu P c).card * Real.exp (-a) :=
    sum_negMulLog_le_mul_sum_add_card_exp_neg mu (lightAtoms mu P c) a
  have hheavy_mass :
      (∑ A ∈ heavyAtoms mu P c, mu.real A) ≤ 1 :=
    sum_measureReal_subset_le_one mu hP (Finset.filter_subset _ _)
  have hheavy :
      (∑ A ∈ heavyAtoms mu P c, Real.negMulLog (mu.real A)) ≤ c := by
    calc
      (∑ A ∈ heavyAtoms mu P c, Real.negMulLog (mu.real A)) ≤
          ∑ A ∈ heavyAtoms mu P c, c * mu.real A := by
        apply Finset.sum_le_sum
        intro A hA
        apply negMulLog_le_mul_of_exp_neg_le
        exact (Finset.mem_filter.mp hA).2
      _ = c * (∑ A ∈ heavyAtoms mu P c, mu.real A) := by
        rw [Finset.mul_sum]
      _ ≤ c * 1 := mul_le_mul_of_nonneg_left hheavy_mass hc
      _ = c := mul_one c
  rw [hsplit]
  linarith

lemma lightAtoms_mass_lower_bound
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    {P : Finset (Set M)} (hP : IsMeasurablePartition mu P)
    {c a : ℝ} (hc : 0 ≤ c) (ha : 0 < a)
    (herror : (lightAtoms mu P c).card * Real.exp (-a) ≤ 1) :
    (partitionEntropy mu P - c - 1) / a ≤
      ∑ A ∈ lightAtoms mu P c, mu.real A := by
  apply (div_le_iff₀ ha).2
  have hentropy := partitionEntropy_le_threshold_add_light_mass mu hP hc a
  linarith

lemma measureReal_iUnion_lightAtoms
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsFiniteMeasure mu]
    {P : Finset (Set M)} (hP : IsMeasurablePartition mu P) (c : ℝ) :
    mu.real (⋃ A ∈ lightAtoms mu P c, A) =
      ∑ A ∈ lightAtoms mu P c, mu.real A := by
  have hpairwise : Set.Pairwise
      (lightAtoms mu P c : Set (Set M)) fun A B => AEDisjoint mu A B := by
    intro A hA B hB hAB
    exact hP.disjoint A (Finset.mem_filter.mp hA).1
      B (Finset.mem_filter.mp hB).1 hAB
  exact measureReal_biUnion_finset₀ hpairwise fun A hA =>
    (hP.measurable A (Finset.mem_filter.mp hA).1).nullMeasurableSet

lemma iteratedJoin_lightAtoms_mass_lower_bound
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : MeasurePreserving T mu mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P)
    {n : ℕ} (hn : 0 < n) (hP_card : 1 < P.card)
    {c : ℝ} (hc : 0 ≤ c) :
    (partitionEntropy mu (iteratedJoin T P n) - c - 1) /
        (n * Real.log (P.card : ℝ)) ≤
      mu.real
        (⋃ A ∈ lightAtoms mu (iteratedJoin T P n) c, A) := by
  classical
  let Q := lightAtoms mu (iteratedJoin T P n) c
  let a : ℝ := n * Real.log (P.card : ℝ)
  have hP_card_real : (1 : ℝ) < P.card := by exact_mod_cast hP_card
  have ha : 0 < a := mul_pos (Nat.cast_pos.mpr hn) (Real.log_pos hP_card_real)
  have hcard_nat : Q.card ≤ P.card ^ n := by
    exact (Finset.card_filter_le _ _).trans (card_iteratedJoin_le_pow T P n)
  have hcard : (Q.card : ℝ) ≤ (P.card : ℝ) ^ n := by
    exact_mod_cast hcard_nat
  have hexp : Real.exp (-a) = ((P.card : ℝ) ^ n)⁻¹ := by
    rw [show a = (n : ℝ) * Real.log (P.card : ℝ) by rfl]
    rw [Real.exp_neg, Real.exp_nat_mul,
      Real.exp_log (lt_trans zero_lt_one hP_card_real)]
  have herror : (Q.card : ℝ) * Real.exp (-a) ≤ 1 := by
    calc
      (Q.card : ℝ) * Real.exp (-a) ≤
          (P.card : ℝ) ^ n * Real.exp (-a) :=
        mul_le_mul_of_nonneg_right hcard (Real.exp_pos (-a)).le
      _ = 1 := by
        rw [hexp, mul_inv_cancel₀]
        positivity
  have hjoin := isMeasurablePartition_iteratedJoin mu T hT P hP n
  have hlower := lightAtoms_mass_lower_bound mu hjoin hc ha herror
  rw [measureReal_iUnion_lightAtoms mu hjoin c]
  simpa [Q, a] using hlower

lemma measure_limsup_ne_zero_of_measureReal_ge
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (U : ℕ → Set M) (hU : ∀ n, MeasurableSet (U n))
    {delta : ℝ} (hdelta_pos : 0 < delta)
    (hmeasure : ∀ n, delta ≤ mu.real (U n)) :
    mu (Filter.limsup U Filter.atTop) ≠ 0 := by
  apply measure_limsup_ne_zero_of_compl_measureReal_le mu U hU
    (show 1 - delta < 1 by linarith)
  intro n
  rw [measureReal_compl (hU n)]
  simpa using sub_le_sub_left (hmeasure n) 1

lemma exists_entropy_light_atoms_limsup_ne_zero
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : MeasurePreserving T mu mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P)
    (hP_card : 1 < P.card)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_entropy : 2 * epsilon < entropyW mu T P) :
    ∃ N : ℕ → ℕ, Filter.Tendsto N Filter.atTop Filter.atTop ∧
      (∀ k, epsilon / (2 * Real.log (P.card : ℝ)) ≤
        mu.real
          (⋃ A ∈ lightAtoms mu (iteratedJoin T P (N k))
            ((entropyW mu T P - 2 * epsilon) * N k), A)) ∧
      mu (Filter.limsup
          (fun k =>
            ⋃ A ∈ lightAtoms mu (iteratedJoin T P (N k))
              ((entropyW mu T P - 2 * epsilon) * N k), A)
          Filter.atTop) ≠ 0 := by
  classical
  let u : ℕ → ℝ := fun n => partitionEntropy mu (iteratedJoin T P n) / n
  let h : ℝ := entropyW mu T P
  have hu_lower : Filter.IsBoundedUnder (fun a b : ℝ => a ≥ b) Filter.atTop u :=
    Filter.isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall fun n =>
        div_nonneg (partitionEntropy_nonneg mu (iteratedJoin T P n))
          (Nat.cast_nonneg n))
  have hu_upper : Filter.IsBoundedUnder (fun a b : ℝ => a ≤ b) Filter.atTop u :=
    Filter.isBoundedUnder_of_eventually_le
      (Filter.Eventually.of_forall fun n => by
        calc
          u n ≤ Real.log
              (((iteratedJoin T P n).filter fun A => mu A ≠ 0).card : ℝ) / n := by
            exact div_le_div_of_nonneg_right
              (partitionEntropy_iteratedJoin_le_log_card_positive_atoms
                mu T hT P hP n) (Nat.cast_nonneg n)
          _ ≤ Real.log (P.card : ℝ) :=
            log_card_positive_iteratedJoin_div_le_log_card mu T hT P hP n)
  obtain ⟨l, hl_u, hl_top⟩ :=
    exists_seq_tendsto_limsup hu_lower.isCobounded_flip hu_upper
  have hl_h : Filter.Tendsto (fun k => u (l k)) Filter.atTop (𝓝 h) := by
    simpa [h, u, entropyW, Function.comp_def] using hl_u
  have hclose : ∀ᶠ k in Filter.atTop, h - epsilon < u (l k) :=
    (tendsto_order.1 hl_h).1 _ (sub_lt_self h hepsilon)
  obtain ⟨n0, hn0⟩ := exists_nat_ge (2 / epsilon)
  have hlarge : ∀ᶠ k in Filter.atTop, n0 ≤ l k :=
    hl_top (Filter.eventually_ge_atTop n0)
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.1 (hclose.and hlarge)
  let N : ℕ → ℕ := fun k => l (k + k0)
  have hN_top : Filter.Tendsto N Filter.atTop Filter.atTop := by
    exact hl_top.comp (tendsto_add_atTop_nat k0)
  let delta : ℝ := epsilon / (2 * Real.log (P.card : ℝ))
  have hP_card_real : (1 : ℝ) < P.card := by exact_mod_cast hP_card
  have hlog_pos : 0 < Real.log (P.card : ℝ) := Real.log_pos hP_card_real
  have hdelta_pos : 0 < delta := div_pos hepsilon (mul_pos zero_lt_two hlog_pos)
  let U : ℕ → Set M := fun k =>
    ⋃ A ∈ lightAtoms mu (iteratedJoin T P (N k))
      ((h - 2 * epsilon) * N k), A
  have hN_properties (k : ℕ) :
      h - epsilon < u (N k) ∧ n0 ≤ N k := by
    exact hk0 (k + k0) (Nat.le_add_left k0 k)
  have hN_pos (k : ℕ) : 0 < N k := by
    have hreal_large : 2 / epsilon ≤ (N k : ℝ) :=
      hn0.trans (by exact_mod_cast (hN_properties k).2)
    have htwo_pos : 0 < 2 / epsilon := div_pos zero_lt_two hepsilon
    exact_mod_cast htwo_pos.trans_le hreal_large
  have hU_measurable (k : ℕ) : MeasurableSet (U k) := by
    apply Finset.measurableSet_biUnion
    intro A hA
    exact measurableSet_of_mem_iteratedJoin T P hT.measurable hP.measurable
      (N k) (Finset.mem_filter.mp hA).1
  have hU_mass (k : ℕ) : delta ≤ mu.real (U k) := by
    have hc : 0 ≤ (h - 2 * epsilon) * N k := by
      have hh : 0 < h - 2 * epsilon := by
        dsimp [h]
        linarith
      exact mul_nonneg hh.le (Nat.cast_nonneg (N k))
    have hlower := iteratedJoin_lightAtoms_mass_lower_bound
      mu T hT P hP (hN_pos k) hP_card hc
    change delta ≤ mu.real (U k)
    apply le_trans ?_ hlower
    have hratio : h - epsilon <
        partitionEntropy mu (iteratedJoin T P (N k)) / N k := by
      exact (hN_properties k).1
    have hlarge_real : 2 ≤ epsilon * (N k : ℝ) := by
      have hreal_large : 2 / epsilon ≤ (N k : ℝ) :=
        hn0.trans (by exact_mod_cast (hN_properties k).2)
      simpa [mul_comm] using (div_le_iff₀ hepsilon).1 hreal_large
    dsimp [delta]
    have hdenom : 0 < (N k : ℝ) * Real.log (P.card : ℝ) :=
      mul_pos (Nat.cast_pos.mpr (hN_pos k)) hlog_pos
    apply (le_div_iff₀ hdenom).2
    have hentropy_lower :
        (h - epsilon) * (N k : ℝ) <
          partitionEntropy mu (iteratedJoin T P (N k)) := by
      exact (lt_div_iff₀ (Nat.cast_pos.mpr (hN_pos k))).1 hratio
    field_simp
    nlinarith
  refine ⟨N, hN_top, ?_, ?_⟩
  · simpa [U, delta, h] using hU_mass
  · exact measure_limsup_ne_zero_of_measureReal_ge mu U hU_measurable
      hdelta_pos hU_mass

end Submission.Helpers
