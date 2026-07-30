import Submission.BrunBounds

open LeanEval.NumberTheory.BrunConstant
open Filter Finset Nat Real
open scoped ArithmeticFunction.omega BigOperators Topology

noncomputable section

namespace Submission.BrunSieve

theorem harmonicPartial_eq_harmonic (M : ℕ) :
    harmonicPartial M = (harmonic M : ℝ) := by
  rw [harmonicPartial, harmonic_eq_sum_Icc]
  simp only [posInterval, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

theorem mul_log_two_le_harmonicPartial (q : ℕ) :
    (q : ℝ) * Real.log 2 ≤ harmonicPartial (sieveWidth q) := by
  rw [harmonicPartial_eq_harmonic]
  calc
    (q : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ q) := by
      rw [Real.log_pow]
    _ ≤ Real.log (((2 ^ q + 1 : ℕ) : ℝ)) := by
      apply Real.log_le_log (by positivity)
      norm_cast
      omega
    _ = Real.log (((sieveWidth q + 1 : ℕ) : ℝ)) := by rfl
    _ ≤ (harmonic (sieveWidth q) : ℝ) := log_add_one_le_harmonic _

theorem mul_log_two_sq_le_eight_boundingSum (q : ℕ) :
    ((q : ℝ) * Real.log 2) ^ 2 ≤
      8 * Submission.Selberg.boundingSum (twinSieve q) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmul : 0 ≤ (q : ℝ) * Real.log 2 := mul_nonneg (by positivity) hlog.le
  have hharm := mul_log_two_le_harmonicPartial q
  calc
    ((q : ℝ) * Real.log 2) ^ 2 ≤ harmonicPartial (sieveWidth q) ^ 2 := by
      nlinarith
    _ ≤ 8 * squarefreeCoprimePairSum (sieveWidth q) :=
      harmonic_sq_le_eight_squarefree _
    _ ≤ 8 * Submission.Selberg.boundingSum (twinSieve q) := by
      gcongr
      exact squarefreeCoprimePairSum_le_boundingSum q

theorem twinStartCount_le_sieve_main_error (q : ℕ) :
    (#(twinStartsInBlock q) : ℝ) ≤
      (sieveBound q : ℝ) / Submission.Selberg.boundingSum (twinSieve q) +
        ((sieveLevelNat q + 1 : ℕ) : ℝ) ^ 4 := by
  calc
    (#(twinStartsInBlock q) : ℝ) ≤ (twinSieve q).toBoundingSieve.siftedSum :=
      twinStartCount_le_siftedSum q
    _ ≤ (twinSieve q).totalMass / Submission.Selberg.boundingSum (twinSieve q) +
        ∑ d ∈ divisors (twinSieve q).prodPrimes,
          if (d : ℝ) ≤ (twinSieve q).level then
            (3 : ℝ) ^ ω d *
              |(twinSieve q).toBoundingSieve.rem d|
          else 0 := Submission.Selberg.bound _
    _ ≤ (sieveBound q : ℝ) / Submission.Selberg.boundingSum (twinSieve q) +
        ((sieveLevelNat q + 1 : ℕ) : ℝ) ^ 4 := by
      change (sieveBound q : ℝ) / Submission.Selberg.boundingSum (twinSieve q) + _ ≤ _
      gcongr
      exact sieveError_le q

theorem sieveMain_le (q : ℕ) (hq : 0 < q) :
    (sieveBound q : ℝ) / Submission.Selberg.boundingSum (twinSieve q) ≤
      (8 * (sieveBound q : ℝ)) / (((q : ℝ) * Real.log 2) ^ 2) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : 0 < ((q : ℝ) * Real.log 2) ^ 2 := by positivity
  rw [div_le_div_iff₀ (Submission.Selberg.boundingSum_pos _) hden]
  have hX : 0 ≤ (sieveBound q : ℝ) := by positivity
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_left (mul_log_two_sq_le_eight_boundingSum q) hX

def blockContribution (q : ℕ) : ℝ :=
  ∑ n ∈ brunBlock q, twinPrimeReciprocalTerm n

theorem twinPrimeReciprocalTerm_nonneg (n : ℕ) : 0 ≤ twinPrimeReciprocalTerm n := by
  classical
  rw [twinPrimeReciprocalTerm]
  split_ifs
  · positivity
  · rfl

theorem twinPrimeReciprocalTerm_le_of_mem_block (q n : ℕ) (hn : n ∈ brunBlock q) :
    twinPrimeReciprocalTerm n ≤ 2 / ((blockBase ^ q : ℕ) : ℝ) := by
  classical
  rw [twinPrimeReciprocalTerm]
  split_ifs with hTwin
  swap
  · positivity
  have hnLower : blockBase ^ q ≤ n := (mem_Ico.mp hn).1
  have hbase : 0 < ((blockBase ^ q : ℕ) : ℝ) := by norm_num [blockBase]
  have hnLowerReal : ((blockBase ^ q : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnLower
  have hnTwoLowerReal : ((blockBase ^ q : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
    exact_mod_cast hnLower.trans (Nat.le_add_right n 2)
  have hfirst := one_div_le_one_div_of_le hbase hnLowerReal
  have hsecond := one_div_le_one_div_of_le hbase hnTwoLowerReal
  calc
    1 / (n : ℝ) + 1 / ((n + 2 : ℕ) : ℝ) ≤
        1 / ((blockBase ^ q : ℕ) : ℝ) + 1 / ((blockBase ^ q : ℕ) : ℝ) :=
      add_le_add hfirst hsecond
    _ = 2 / ((blockBase ^ q : ℕ) : ℝ) := by ring

theorem blockContribution_le_card (q : ℕ) :
    blockContribution q ≤
      (2 / ((blockBase ^ q : ℕ) : ℝ)) * (#(twinStartsInBlock q) : ℝ) := by
  classical
  calc
    blockContribution q =
        ∑ n ∈ brunBlock q,
          if IsTwinPrimeStart n then twinPrimeReciprocalTerm n else 0 := by
      rw [blockContribution]
      apply sum_congr rfl
      intro n hn
      by_cases hTwin : IsTwinPrimeStart n <;>
        simp [twinPrimeReciprocalTerm, hTwin]
    _ = ∑ n ∈ (brunBlock q).filter IsTwinPrimeStart,
        twinPrimeReciprocalTerm n := by
      rw [sum_filter]
    _ ≤ ∑ _n ∈ (brunBlock q).filter IsTwinPrimeStart,
        2 / ((blockBase ^ q : ℕ) : ℝ) := by
      gcongr with n hn
      exact twinPrimeReciprocalTerm_le_of_mem_block q n (mem_filter.mp hn).1
    _ = (2 / ((blockBase ^ q : ℕ) : ℝ)) *
        (#((brunBlock q).filter IsTwinPrimeStart) : ℝ) := by
      simp [mul_comm]

theorem blockContribution_le_raw (q : ℕ) (hq : 0 < q) :
    blockContribution q ≤
      (2 / ((blockBase ^ q : ℕ) : ℝ)) *
        ((8 * (sieveBound q : ℝ)) / (((q : ℝ) * Real.log 2) ^ 2) +
          ((sieveLevelNat q + 1 : ℕ) : ℝ) ^ 4) := by
  have hfactor : 0 ≤ 2 / ((blockBase ^ q : ℕ) : ℝ) := by positivity
  calc
    blockContribution q ≤
        (2 / ((blockBase ^ q : ℕ) : ℝ)) * (#(twinStartsInBlock q) : ℝ) :=
      blockContribution_le_card q
    _ ≤ (2 / ((blockBase ^ q : ℕ) : ℝ)) *
        ((sieveBound q : ℝ) / Submission.Selberg.boundingSum (twinSieve q) +
          ((sieveLevelNat q + 1 : ℕ) : ℝ) ^ 4) := by
      gcongr
      exact twinStartCount_le_sieve_main_error q
    _ ≤ (2 / ((blockBase ^ q : ℕ) : ℝ)) *
        ((8 * (sieveBound q : ℝ)) / (((q : ℝ) * Real.log 2) ^ 2) +
          ((sieveLevelNat q + 1 : ℕ) : ℝ) ^ 4) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (sieveMain_le q hq) le_rfl) hfactor

def blockMajorant (q : ℕ) : ℝ :=
  (16 * (blockBase : ℝ) / (Real.log 2) ^ 2) / (q : ℝ) ^ 2 +
    32 * ((1 : ℝ) / 16) ^ q

private theorem blockMain_eq (q : ℕ) (hq : 0 < q) :
    (2 / ((blockBase ^ q : ℕ) : ℝ)) *
        ((8 * (sieveBound q : ℝ)) / (((q : ℝ) * Real.log 2) ^ 2)) =
      (16 * (blockBase : ℝ) / (Real.log 2) ^ 2) / (q : ℝ) ^ 2 := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hlog0 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hbase0 : ((blockBase ^ q : ℕ) : ℝ) ≠ 0 := by norm_num [blockBase]
  rw [sieveBound, pow_succ]
  push_cast
  field_simp [hbase0]
  apply (div_eq_iff (by norm_num [blockBase])).2
  ring

private theorem sieveLevel_four_mul_sixteen_pow (q : ℕ) :
    sieveLevelNat q ^ 4 * 16 ^ q = blockBase ^ q := by
  change (((2 ^ q) ^ 4) ^ 4) * (2 ^ 4) ^ q = (2 ^ 20) ^ q
  rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_mul]
  congr 1
  omega

private theorem sieveLevel_add_one_pow_le (q : ℕ) :
    (sieveLevelNat q + 1) ^ 4 ≤ 16 * sieveLevelNat q ^ 4 := by
  have hlevel : 1 ≤ sieveLevelNat q := by
    apply Nat.one_le_iff_ne_zero.mpr
    norm_num [sieveLevelNat, sieveWidth]
  have hadd : sieveLevelNat q + 1 ≤ 2 * sieveLevelNat q := by omega
  calc
    (sieveLevelNat q + 1) ^ 4 ≤ (2 * sieveLevelNat q) ^ 4 :=
      Nat.pow_le_pow_left hadd 4
    _ = 16 * sieveLevelNat q ^ 4 := by ring

private theorem blockError_le (q : ℕ) :
    (2 / ((blockBase ^ q : ℕ) : ℝ)) *
        ((sieveLevelNat q + 1 : ℕ) : ℝ) ^ 4 ≤
      32 * ((1 : ℝ) / 16) ^ q := by
  have hfactor : 0 ≤ 2 / ((blockBase ^ q : ℕ) : ℝ) := by positivity
  have hlevel :
      (((sieveLevelNat q + 1 : ℕ) : ℝ) ^ 4) ≤
        16 * ((sieveLevelNat q : ℕ) : ℝ) ^ 4 := by
    exact_mod_cast sieveLevel_add_one_pow_le q
  calc
    (2 / ((blockBase ^ q : ℕ) : ℝ)) *
        ((sieveLevelNat q + 1 : ℕ) : ℝ) ^ 4 ≤
        (2 / ((blockBase ^ q : ℕ) : ℝ)) *
          (16 * ((sieveLevelNat q : ℕ) : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_left hlevel hfactor
    _ = 32 * ((1 : ℝ) / 16) ^ q := by
      have hbase0 : ((blockBase ^ q : ℕ) : ℝ) ≠ 0 := by norm_num [blockBase]
      have hsixteen0 : ((16 ^ q : ℕ) : ℝ) ≠ 0 := by positivity
      have hpower :
          ((sieveLevelNat q : ℕ) : ℝ) ^ 4 * ((16 ^ q : ℕ) : ℝ) =
            ((blockBase ^ q : ℕ) : ℝ) := by
        exact_mod_cast sieveLevel_four_mul_sixteen_pow q
      rw [div_pow, one_pow]
      push_cast
      field_simp [hbase0, hsixteen0]
      apply (div_eq_iff (by norm_num [blockBase])).2
      norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hpower
      rw [← hpower]
      ring

theorem blockContribution_le_majorant (q : ℕ) (hq : 0 < q) :
    blockContribution q ≤ blockMajorant q := by
  calc
    blockContribution q ≤
        (2 / ((blockBase ^ q : ℕ) : ℝ)) *
          ((8 * (sieveBound q : ℝ)) / (((q : ℝ) * Real.log 2) ^ 2) +
            ((sieveLevelNat q + 1 : ℕ) : ℝ) ^ 4) :=
      blockContribution_le_raw q hq
    _ = (16 * (blockBase : ℝ) / (Real.log 2) ^ 2) / (q : ℝ) ^ 2 +
        (2 / ((blockBase ^ q : ℕ) : ℝ)) *
          ((sieveLevelNat q + 1 : ℕ) : ℝ) ^ 4 := by
      rw [mul_add, blockMain_eq q hq]
    _ ≤ (16 * (blockBase : ℝ) / (Real.log 2) ^ 2) / (q : ℝ) ^ 2 +
        32 * ((1 : ℝ) / 16) ^ q := by
      exact add_le_add le_rfl (blockError_le q)
    _ = blockMajorant q := rfl

theorem summable_blockMajorant : Summable blockMajorant := by
  have hp : Summable (fun q : ℕ => 1 / (q : ℝ) ^ 2) :=
    summable_one_div_nat_pow.mpr (by norm_num)
  have hmain : Summable fun q : ℕ =>
      (16 * (blockBase : ℝ) / (Real.log 2) ^ 2) * (1 / (q : ℝ) ^ 2) :=
    hp.mul_left _
  have hgeom : Summable fun q : ℕ => 32 * ((1 : ℝ) / 16) ^ q :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  exact (hmain.add hgeom).congr fun q => by
    rw [blockMajorant]
    ring

theorem blockContribution_nonneg (q : ℕ) : 0 ≤ blockContribution q := by
  rw [blockContribution]
  apply sum_nonneg
  intro n hn
  exact twinPrimeReciprocalTerm_nonneg n

theorem summable_blockContribution : Summable blockContribution := by
  rw [← summable_nat_add_iff 1]
  exact Summable.of_nonneg_of_le
    (fun q => blockContribution_nonneg (q + 1))
    (fun q => blockContribution_le_majorant (q + 1) (by omega))
    ((summable_nat_add_iff 1).mpr summable_blockMajorant)

def partitionBlock (q : ℕ) : Finset ℕ :=
  if q = 0 then insert 0 (brunBlock 0) else brunBlock q

theorem existsUnique_mem_partitionBlock (n : ℕ) :
    ∃! q, n ∈ partitionBlock q := by
  by_cases hn : n = 0
  · subst n
    refine ⟨0, by simp [partitionBlock], ?_⟩
    intro q hq
    by_contra hq0
    have hqBlock : 0 ∈ brunBlock q := by
      simpa [partitionBlock, hq0] using hq
    have hqLower := (mem_Ico.mp hqBlock).1
    have hpow : 0 < blockBase ^ q := by norm_num [blockBase]
    omega
  · let q := Nat.log blockBase n
    have hbase : 1 < blockBase := by norm_num [blockBase]
    have hlower : blockBase ^ q ≤ n := Nat.pow_log_le_self blockBase hn
    have hupper : n < blockBase ^ (q + 1) := by
      simpa [q, Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self hbase n
    have hqBlock : n ∈ brunBlock q := by
      exact mem_Ico.mpr ⟨hlower, hupper⟩
    refine ⟨q, ?_, ?_⟩
    · by_cases hq0 : q = 0
      · change n ∈ if q = 0 then insert 0 (brunBlock 0) else brunBlock q
        rw [if_pos hq0]
        exact mem_insert.mpr (Or.inr (hq0 ▸ hqBlock))
      · simp [partitionBlock, hq0, hqBlock]
    · intro j hj
      have hjBlock : n ∈ brunBlock j := by
        by_cases hj0 : j = 0
        · subst j
          simpa [partitionBlock, hn] using hj
        · simpa [partitionBlock, hj0] using hj
      have hjBounds := mem_Ico.mp hjBlock
      have hjLog : Nat.log blockBase n = j :=
        Nat.log_eq_of_pow_le_of_lt_pow hjBounds.1 hjBounds.2
      simpa [q] using hjLog.symm

theorem sum_partitionBlock_eq_blockContribution (q : ℕ) :
    (∑ n ∈ partitionBlock q, twinPrimeReciprocalTerm n) = blockContribution q := by
  by_cases hq : q = 0
  · subst q
    simp [partitionBlock, blockContribution, brunBlock, blockBase,
      twinPrimeReciprocalTerm, IsTwinPrimeStart, Nat.not_prime_zero]
  · simp [partitionBlock, hq, blockContribution]

theorem summable_twinPrimeReciprocalTerm : Summable twinPrimeReciprocalTerm := by
  rw [summable_partition twinPrimeReciprocalTerm_nonneg existsUnique_mem_partitionBlock]
  constructor
  · intro q
    letI : Fintype (partitionBlock q : Set ℕ) :=
      (partitionBlock q).finite_toSet.fintype
    exact (hasSum_fintype _).summable
  · exact summable_blockContribution.congr fun q => by
      rw [Finset.tsum_subtype' (partitionBlock q) twinPrimeReciprocalTerm]
      exact (sum_partitionBlock_eq_blockContribution q).symm

end Submission.BrunSieve
