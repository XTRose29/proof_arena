import Submission.EntropySubadditive

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory Topology

lemma exists_eventually_entropy_light_atoms_limsup_ne_zero
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T T_inv : M → M)
    (hT_right : Function.RightInverse T_inv T)
    (hT : MeasurePreserving T mu mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P)
    (hP_card : 1 < P.card)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_entropy : 2 * epsilon < entropyW mu T P) :
    ∃ n0 : ℕ,
      (∀ k, epsilon / (2 * Real.log (P.card : ℝ)) ≤
        mu.real
          (⋃ A ∈ lightAtoms mu (iteratedJoin T P (k + n0))
            ((entropyW mu T P - 2 * epsilon) * (k + n0)), A)) ∧
      mu (limsup
          (fun k =>
            ⋃ A ∈ lightAtoms mu (iteratedJoin T P (k + n0))
              ((entropyW mu T P - 2 * epsilon) * (k + n0)), A)
          atTop) ≠ 0 := by
  classical
  let u : ℕ → ℝ := fun n => partitionEntropy mu (iteratedJoin T P n) / n
  let h : ℝ := entropyW mu T P
  have htend : Tendsto u atTop (nhds h) := by
    simpa [u, h] using
      tendsto_partitionEntropy_iteratedJoin_div_entropyW
        mu T T_inv hT_right hT P hP
  have hclose : ∀ᶠ n in atTop, h - epsilon < u n :=
    (tendsto_order.1 htend).1 _ (sub_lt_self h hepsilon)
  obtain ⟨nmin, hnmin⟩ := exists_nat_ge (2 / epsilon)
  have hlarge : ∀ᶠ n in atTop, nmin ≤ n := eventually_ge_atTop nmin
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 (hclose.and hlarge)
  let delta : ℝ := epsilon / (2 * Real.log (P.card : ℝ))
  let U : ℕ → Set M := fun k =>
    ⋃ A ∈ lightAtoms mu (iteratedJoin T P (k + n0))
      ((h - 2 * epsilon) * (k + n0)), A
  have hP_card_real : (1 : ℝ) < P.card := by exact_mod_cast hP_card
  have hlog_pos : 0 < Real.log (P.card : ℝ) := Real.log_pos hP_card_real
  have hdelta_pos : 0 < delta :=
    div_pos hepsilon (mul_pos zero_lt_two hlog_pos)
  have hN_properties (k : ℕ) :
      h - epsilon < u (k + n0) ∧ nmin ≤ k + n0 := by
    exact hn0 (k + n0) (Nat.le_add_left n0 k)
  have hN_pos (k : ℕ) : 0 < k + n0 := by
    have hreal_large : 2 / epsilon ≤ (k + n0 : ℝ) :=
      hnmin.trans (by exact_mod_cast (hN_properties k).2)
    have htwo_pos : 0 < 2 / epsilon := div_pos zero_lt_two hepsilon
    exact_mod_cast htwo_pos.trans_le hreal_large
  have hU_measurable (k : ℕ) : MeasurableSet (U k) := by
    apply Finset.measurableSet_biUnion
    intro A hA
    exact measurableSet_of_mem_iteratedJoin T P hT.measurable hP.measurable
      (k + n0) (Finset.mem_filter.mp hA).1
  have hU_mass (k : ℕ) : delta ≤ mu.real (U k) := by
    have hc : 0 ≤ (h - 2 * epsilon) * (k + n0) := by
      have hh : 0 < h - 2 * epsilon := by
        dsimp [h]
        linarith
      positivity
    have hlower := iteratedJoin_lightAtoms_mass_lower_bound
      mu T hT P hP (hN_pos k) hP_card hc
    change delta ≤ mu.real (U k)
    apply le_trans ?_ hlower
    have hratio : h - epsilon <
        partitionEntropy mu (iteratedJoin T P (k + n0)) / (k + n0) :=
      by simpa [u, Nat.cast_add] using (hN_properties k).1
    have hlarge_real : 2 ≤ epsilon * (k + n0 : ℝ) := by
      have hreal_large : 2 / epsilon ≤ (k + n0 : ℝ) :=
        hnmin.trans (by exact_mod_cast (hN_properties k).2)
      simpa [mul_comm] using (div_le_iff₀ hepsilon).1 hreal_large
    dsimp [delta]
    have hdenom :
        0 < ((k + n0 : ℕ) : ℝ) * Real.log (P.card : ℝ) :=
      mul_pos (Nat.cast_pos.mpr (hN_pos k)) hlog_pos
    norm_num [Nat.cast_add] at hdenom ⊢
    apply (le_div_iff₀ hdenom).2
    have hentropy_lower :
        (h - epsilon) * (k + n0 : ℝ) <
          partitionEntropy mu (iteratedJoin T P (k + n0)) := by
      have hNpos_real : 0 < (k : ℝ) + n0 := by
        exact_mod_cast hN_pos k
      exact (lt_div_iff₀ hNpos_real).1 hratio
    field_simp
    nlinarith
  refine ⟨n0, ?_, ?_⟩
  · simpa [U, delta, h] using hU_mass
  · exact measure_limsup_ne_zero_of_measureReal_ge mu U hU_measurable
      hdelta_pos hU_mass

lemma exists_eventually_centered_entropy_light_atoms_limsup_ne_zero
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T T_inv : M → M)
    (hT_right : Function.RightInverse T_inv T)
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P)
    (hP_card : 1 < P.card)
    (m n : ℕ → ℕ) (hsplit : ∀ L, m L + n L = L)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_entropy : 2 * epsilon < entropyW mu T P) :
    ∃ n0 : ℕ,
      mu (limsup
        (fun k =>
          ⋃ A ∈ lightAtoms mu
              (centeredJoin T T_inv P (m (k + n0)) (n (k + n0)))
              ((entropyW mu T P - 2 * epsilon) * (k + n0)), A)
        atTop) ≠ 0 := by
  obtain ⟨n0, hmass, _hlimsup⟩ :=
    exists_eventually_entropy_light_atoms_limsup_ne_zero
      mu T T_inv hT_right hT P hP hP_card hepsilon hepsilon_entropy
  let delta : ℝ := epsilon / (2 * Real.log (P.card : ℝ))
  let U : ℕ → Set M := fun k =>
    ⋃ A ∈ lightAtoms mu
        (centeredJoin T T_inv P (m (k + n0)) (n (k + n0)))
        ((entropyW mu T P - 2 * epsilon) * (k + n0)), A
  have hdelta_pos : 0 < delta := by
    have hP_card_real : (1 : ℝ) < P.card := by exact_mod_cast hP_card
    exact div_pos hepsilon (mul_pos zero_lt_two (Real.log_pos hP_card_real))
  have hU_measurable (k : ℕ) : MeasurableSet (U k) := by
    apply Finset.measurableSet_biUnion
    intro A hA
    exact (isMeasurablePartition_centeredJoin mu T T_inv hT hT_inv P hP
      (m (k + n0)) (n (k + n0))).measurable A (Finset.mem_filter.mp hA).1
  have hU_mass (k : ℕ) : delta ≤ mu.real (U k) := by
    calc
      delta ≤ mu.real
          (⋃ A ∈ lightAtoms mu (iteratedJoin T P (k + n0))
            ((entropyW mu T P - 2 * epsilon) * (k + n0)), A) := by
        simpa [delta] using hmass k
      _ = mu.real (U k) := by
        change mu.real
            (⋃ A ∈ lightAtoms mu (iteratedJoin T P (k + n0))
              ((entropyW mu T P - 2 * epsilon) * (k + n0)), A) =
          mu.real
            (⋃ A ∈ lightAtoms mu
              (centeredJoin T T_inv P (m (k + n0)) (n (k + n0)))
              ((entropyW mu T P - 2 * epsilon) * (k + n0)), A)
        rw [measureReal_iUnion_lightAtoms_centeredJoin mu T T_inv hT hT_inv
          P hP (m (k + n0)) (n (k + n0))
            ((entropyW mu T P - 2 * epsilon) * (k + n0))]
        rw [hsplit]
  exact ⟨n0, measure_limsup_ne_zero_of_measureReal_ge
    mu U hU_measurable hdelta_pos hU_mass⟩

end Submission.Helpers
