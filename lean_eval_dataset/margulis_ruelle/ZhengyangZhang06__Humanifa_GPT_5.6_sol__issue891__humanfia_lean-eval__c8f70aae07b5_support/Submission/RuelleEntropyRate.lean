import Submission.SpatialGenerator

namespace Submission.Helpers

open LeanEval.Dynamics Filter MeasureTheory

lemma conditionalObservationEntropy_mono_conditioning_comp
    {M I J K : Type*} [MeasurableSpace M]
    [Fintype I] [Fintype J] [Fintype K]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    [MeasurableSpace K] [MeasurableSingletonClass K]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (X : M → I) (hX : Measurable X)
    (Z : M → J) (hZ : Measurable Z)
    (f : J → K) :
    conditionalObservationEntropy mu X Z ≤
      conditionalObservationEntropy mu X (fun x => f (Z x)) := by
  let W : M → K × J := fun x => (f (Z x), Z x)
  have hW : Measurable W :=
    ((measurable_of_finite f).comp hZ).prodMk hZ
  have hW_entropy :
      observationEntropy mu W = observationEntropy mu Z := by
    simpa [W] using observationEntropy_graph mu f Z
  have hXW_entropy :
      observationEntropy mu (fun x => (X x, W x)) =
        observationEntropy mu (fun x => (X x, Z x)) := by
    let U : M → I × J := fun x => (X x, Z x)
    let g : I × J → K := fun p => f p.2
    let e : K × (I × J) ≃ I × (K × J) :=
      { toFun := fun p => (p.2.1, (p.1, p.2.2))
        invFun := fun p => (p.2.1, (p.1, p.2.2))
        left_inv := by intro p; rfl
        right_inv := by intro p; rfl }
    calc
      observationEntropy mu (fun x => (X x, W x)) =
          observationEntropy mu (fun x => e (g (U x), U x)) := by
        rfl
      _ = observationEntropy mu (fun x => (g (U x), U x)) :=
        observationEntropy_equiv mu e (fun x => (g (U x), U x))
      _ = observationEntropy mu U :=
        observationEntropy_graph mu g U
      _ = observationEntropy mu (fun x => (X x, Z x)) := rfl
  have heq :
      conditionalObservationEntropy mu X Z =
        conditionalObservationEntropy mu X W := by
    rw [conditionalObservationEntropy_eq_sub mu X hX Z hZ,
      conditionalObservationEntropy_eq_sub mu X hX W hW,
      hW_entropy, hXW_entropy]
  rw [heq]
  exact conditionalObservationEntropy_mono_conditioning
    mu X hX (fun x => f (Z x)) ((measurable_of_finite f).comp hZ) Z hZ

lemma observationEntropy_observationBlock_succ_le
    {M I : Type*} [MeasurableSpace M]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : MeasurePreserving T mu mu)
    (Y : M → I) (hY : Measurable Y) (n : ℕ) :
    observationEntropy mu (observationBlock T Y (n + 1)) ≤
      observationEntropy mu Y +
        n * conditionalObservationEntropy mu (fun x => Y (T x)) Y := by
  induction n with
  | zero =>
      let e : (Fin 1 → I) ≃ I :=
        { toFun := fun f => f 0
          invFun := fun i _ => i
          left_inv := by
            intro f
            funext j
            fin_cases j
            rfl
          right_inv := by intro i; rfl }
      have he := observationEntropy_equiv mu e (observationBlock T Y 1)
      simpa [e, observationBlock] using he.symm.le
  | succ n ih =>
      let pref : M → (Fin (n + 1) → I) :=
        observationBlock T Y (n + 1)
      let last : M → I := fun x => Y (T^[n + 1] x)
      let previous : (Fin (n + 1) → I) → I :=
        fun f => f (Fin.last n)
      have hpref : Measurable pref :=
        measurable_observationBlock T hT.measurable Y hY (n + 1)
      have hlast : Measurable last :=
        hY.comp (hT.measurable.iterate (n + 1))
      have hsplit :
          observationEntropy mu (observationBlock T Y (n + 2)) =
            observationEntropy mu (fun x => (pref x, last x)) := by
        have he := observationEntropy_equiv mu
          (finSuccLastEquiv I (n + 1))
          (observationBlock T Y (n + 2))
        rw [finSuccLastEquiv_observationBlock] at he
        exact he.symm
      have hcond :
          conditionalObservationEntropy mu last pref ≤
            conditionalObservationEntropy mu (fun x => Y (T x)) Y := by
        have hmono := conditionalObservationEntropy_mono_conditioning_comp
          mu last hlast pref hpref previous
        have hstationary :=
          conditionalObservationEntropy_comp_measurePreserving
            mu (T^[n]) (hT.iterate n) (fun x => Y (T x))
              (hY.comp hT.measurable) Y hY
        calc
          conditionalObservationEntropy mu last pref ≤
              conditionalObservationEntropy mu last
                (fun x => previous (pref x)) := hmono
          _ = conditionalObservationEntropy mu
                (fun x => Y (T x)) Y := by
            rw [← hstationary]
            congr 1
            funext x
            simp only [last, Function.iterate_succ_apply']
      calc
        observationEntropy mu (observationBlock T Y (n + 2)) =
            observationEntropy mu (fun x => (pref x, last x)) := hsplit
        _ = observationEntropy mu (fun x => (last x, pref x)) :=
          observationEntropy_pair_swap mu pref last
        _ = observationEntropy mu pref +
            conditionalObservationEntropy mu last pref :=
          observationEntropy_pair mu last hlast pref hpref
        _ ≤ (observationEntropy mu Y +
              n * conditionalObservationEntropy mu (fun x => Y (T x)) Y) +
            conditionalObservationEntropy mu (fun x => Y (T x)) Y :=
          add_le_add ih hcond
        _ = observationEntropy mu Y +
            (n.succ : ℝ) *
              conditionalObservationEntropy mu (fun x => Y (T x)) Y := by
          rw [Nat.cast_succ]
          ring

lemma entropyW_fiberPartition_le_one_step_conditional
    {M I : Type*} [MeasurableSpace M]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T T_inv : M → M)
    (hT_right : Function.RightInverse T_inv T)
    (hT : MeasurePreserving T mu mu)
    (Y : M → I) (hY : Measurable Y) :
    entropyW mu T (fiberPartition Y) ≤
      conditionalObservationEntropy mu (fun x => Y (T x)) Y := by
  let c := conditionalObservationEntropy mu (fun x => Y (T x)) Y
  let P := fiberPartition Y
  have hP : IsMeasurablePartition mu P :=
    isMeasurablePartition_fiberPartition mu Y hY
  have hleft := tendsto_partitionEntropy_iteratedJoin_div_entropyW
    mu T T_inv hT_right hT P hP
  have hright : Tendsto
      (fun n : ℕ => observationEntropy mu Y / n + c)
      atTop (nhds c) := by
    simpa using
      (tendsto_const_div_atTop_nhds_zero_nat
        (observationEntropy mu Y)).add tendsto_const_nhds
  have hbound : ∀ᶠ n : ℕ in atTop,
      partitionEntropy mu (iteratedJoin T P n) / n ≤
        observationEntropy mu Y / n + c := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    have hraw := observationEntropy_observationBlock_succ_le
      mu T hT Y hY m
    rw [observationEntropy_observationBlock_fiberPartition] at hraw
    have hmpos : (0 : ℝ) < m.succ := by positivity
    calc
      partitionEntropy mu (iteratedJoin T P m.succ) / (m.succ : ℝ) ≤
          (observationEntropy mu Y + m * c) / (m.succ : ℝ) :=
        div_le_div_of_nonneg_right hraw hmpos.le
      _ ≤ observationEntropy mu Y / (m.succ : ℝ) + c := by
        have hc : 0 ≤ c :=
          conditionalObservationEntropy_nonneg mu (fun x => Y (T x)) Y
        rw [Nat.cast_succ]
        field_simp
        nlinarith
  apply le_of_not_gt
  intro hgt
  let midpoint := (entropyW mu T P + c) / 2
  have hlower : c < midpoint := by
    dsimp [midpoint]
    linarith
  have hupper : midpoint < entropyW mu T P := by
    dsimp [midpoint]
    linarith
  have hleft_eventually : ∀ᶠ n : ℕ in atTop,
      midpoint <
        partitionEntropy mu (iteratedJoin T P n) / n :=
    (tendsto_order.1 hleft).1 midpoint hupper
  have hright_eventually : ∀ᶠ n : ℕ in atTop,
      observationEntropy mu Y / n + c < midpoint :=
    (tendsto_order.1 hright).2 midpoint hlower
  obtain ⟨n, hn, hln, hrn⟩ :=
    (hbound.and (hleft_eventually.and hright_eventually)).exists
  exact (not_lt_of_ge hn) (hrn.trans hln)

lemma negMulLog_le_mul_log_add_inv_sub
    {m p : ℝ} (hm : 0 < m) (hp : 0 ≤ p) :
    Real.negMulLog p ≤ p * Real.log m + m⁻¹ - p := by
  have h :=
    Real.negMulLog_le_one_sub_self (mul_nonneg hm.le hp : 0 ≤ m * p)
  rw [Real.negMulLog_mul] at h
  simp only [Real.negMulLog] at h ⊢
  apply le_of_mul_le_mul_left _ hm
  calc
    m * (-p * Real.log p) ≤ m * (p * Real.log m) + 1 - m * p := by
      linarith
    _ = m * (p * Real.log m + m⁻¹ - p) := by
      field_simp

lemma sum_negMulLog_le_log_nat_of_sum_eq_one
    {I : Type*} (s : Finset I) (p : I → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i)
    (hsum : ∑ i ∈ s, p i = 1)
    {N : ℕ} (hN : 0 < N) (hcard : s.card ≤ N) :
    (∑ i ∈ s, Real.negMulLog (p i)) ≤ Real.log N := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    (∑ i ∈ s, Real.negMulLog (p i)) ≤
        ∑ i ∈ s, (p i * Real.log N + (N : ℝ)⁻¹ - p i) :=
      Finset.sum_le_sum fun i hi =>
        negMulLog_le_mul_log_add_inv_sub hNreal (hp i hi)
    _ = Real.log N + (s.card : ℝ) * (N : ℝ)⁻¹ - 1 := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
        hsum]
      simp only [one_mul, Finset.sum_const, nsmul_eq_mul]
    _ ≤ Real.log N := by
      have hfraction : (s.card : ℝ) * (N : ℝ)⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one hNreal]
        exact_mod_cast hcard
      linarith

noncomputable def conditionalSupport
    {M I J : Type*} [MeasurableSpace M] [Fintype I]
    (mu : Measure M) (X : M → I) (Y : M → J) (y : J) : Finset I :=
  Finset.univ.filter fun i =>
    mu.real (Y ⁻¹' {y} ∩ X ⁻¹' {i}) ≠ 0

lemma conditionalEntropyRow_le_log_card_bound
    {M I J : Type*} [MeasurableSpace M] [Fintype I]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (X : M → I) (hX : Measurable X)
    (Y : M → J) (hY : Measurable Y)
    (y : J) {N : ℕ} (hN : 0 < N)
    (hcard : (conditionalSupport mu X Y y).card ≤ N) :
    (∑ i : I, Real.negMulLog
      (mu.real (Y ⁻¹' {y} ∩ X ⁻¹' {i}) /
        mu.real (Y ⁻¹' {y}))) ≤ Real.log N := by
  classical
  let row := mu.real (Y ⁻¹' {y})
  let p : I → ℝ := fun i =>
    mu.real (Y ⁻¹' {y} ∩ X ⁻¹' {i}) / row
  let s := conditionalSupport mu X Y y
  by_cases hrow : row = 0
  · have hjoint (i : I) :
        mu.real (Y ⁻¹' {y} ∩ X ⁻¹' {i}) = 0 :=
      measureReal_mono_null Set.inter_subset_left hrow
    have hlogN : 0 ≤ Real.log N := by
      apply Real.log_nonneg
      exact_mod_cast hN
    simpa [p, row, hrow, hjoint] using hlogN
  · have hrow_pos : 0 < row :=
      lt_of_le_of_ne measureReal_nonneg (Ne.symm hrow)
    have hsum_joint :
        ∑ i : I, mu.real (Y ⁻¹' {y} ∩ X ⁻¹' {i}) = row := by
      simpa [row] using sum_measureReal_inter_fibers
        mu X hX (hY (measurableSet_singleton y)) Set.univ
    have hsum_all : ∑ i : I, p i = 1 := by
      simp only [p, ← Finset.sum_div, hsum_joint]
      exact div_self hrow
    have hsum_support : ∑ i ∈ s, p i = 1 := by
      rw [← hsum_all]
      apply Finset.sum_subset
      · simp [s, conditionalSupport]
      · intro i _hi hi
        have hzero :
            mu.real (Y ⁻¹' {y} ∩ X ⁻¹' {i}) = 0 := by
          by_contra hne
          exact hi (by simp [s, conditionalSupport, hne])
        simp [p, hzero]
    have hp : ∀ i ∈ s, 0 ≤ p i := by
      intro i _hi
      exact div_nonneg measureReal_nonneg hrow_pos.le
    have hrestricted :
        (∑ i : I, Real.negMulLog (p i)) =
          ∑ i ∈ s, Real.negMulLog (p i) := by
      symm
      apply Finset.sum_subset
      · simp [s, conditionalSupport]
      · intro i _hi hi
        have hzero :
            mu.real (Y ⁻¹' {y} ∩ X ⁻¹' {i}) = 0 := by
          by_contra hne
          exact hi (by simp [s, conditionalSupport, hne])
        simp [p, hzero]
    change (∑ i : I, Real.negMulLog (p i)) ≤ Real.log N
    rw [hrestricted]
    exact sum_negMulLog_le_log_nat_of_sum_eq_one
      s p hp hsum_support hN hcard

lemma conditionalObservationEntropy_le_weighted_log_card
    {M I J : Type*} [MeasurableSpace M] [Fintype I] [Fintype J]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (X : M → I) (hX : Measurable X)
    (Y : M → J) (hY : Measurable Y)
    (N : J → ℕ) (hN : ∀ y, 0 < N y)
    (hcard : ∀ y, (conditionalSupport mu X Y y).card ≤ N y) :
    conditionalObservationEntropy mu X Y ≤
      ∑ y : J, mu.real (Y ⁻¹' {y}) * Real.log (N y) := by
  unfold conditionalObservationEntropy
  apply Finset.sum_le_sum
  intro y _hy
  exact mul_le_mul_of_nonneg_left
    (conditionalEntropyRow_le_log_card_bound
      mu X hX Y hY y (hN y) (hcard y))
    measureReal_nonneg

end Submission.Helpers
