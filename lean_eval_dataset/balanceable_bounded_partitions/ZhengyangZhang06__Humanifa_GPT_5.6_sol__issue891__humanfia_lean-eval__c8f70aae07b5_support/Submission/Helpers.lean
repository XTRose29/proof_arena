import ChallengeDeps

open LeanEval.Combinatorics

namespace Submission.Helpers

theorem balanceable_of_submultiset_sum {m : ℕ} {p : (2 * m).Partition}
    {s : Multiset ℕ} (hs : s ≤ p.parts) (hssum : s.sum = m) : Balanceable p := by
  refine ⟨s, p.parts - s, ?_, ?_⟩
  · rw [Multiset.add_comm, Multiset.sub_add_cancel hs]
  · have hsum :
        (p.parts - s).sum + s.sum = p.parts.sum := by
      rw [← Multiset.sum_add, Multiset.sub_add_cancel hs]
    have hrest : (p.parts - s).sum = m := by
      have hsum' : (p.parts - s).sum + m = 2 * m := by
        simpa [hssum, p.parts_sum] using hsum
      omega
    rw [hssum, hrest]

theorem submultiset_sum_of_balanceable {m : ℕ} {p : (2 * m).Partition}
    (hp : Balanceable p) : ∃ s ≤ p.parts, s.sum = m := by
  rcases hp with ⟨s₁, s₂, hparts, hsum⟩
  refine ⟨s₁, ?_, ?_⟩
  · rw [← hparts]
    exact Multiset.le_add_right s₁ s₂
  · have hsum_parts : s₁.sum + s₂.sum = 2 * m := by
      rw [← Multiset.sum_add, hparts, p.parts_sum]
    omega

theorem not_balanceable_of_no_submultiset_sum {m : ℕ} {p : (2 * m).Partition}
    (h : ∀ s ≤ p.parts, s.sum ≠ m) : ¬ Balanceable p := by
  intro hp
  rcases submultiset_sum_of_balanceable hp with ⟨s, hs, hsum⟩
  exact h s hs hsum

theorem even_of_balanceable {n : ℕ} {p : n.Partition} (hp : Balanceable p) : Even n := by
  rcases hp with ⟨s₁, s₂, hparts, hsum⟩
  refine ⟨s₂.sum, ?_⟩
  rw [← p.parts_sum, ← hparts, Multiset.sum_add, hsum]

theorem lcm_Icc_pos (k : ℕ) (_hk : 0 < k) : 0 < (Finset.Icc 1 k).lcm id := by
  apply Nat.pos_of_ne_zero
  rw [Finset.lcm_ne_zero_iff]
  intro x hx
  exact Nat.ne_of_gt (Finset.mem_Icc.mp hx).1

theorem dvd_lcm_Icc {i k : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) :
    i ∣ (Finset.Icc 1 k).lcm id := by
  exact Finset.dvd_lcm (by simp [Finset.mem_Icc, hi, hik])

theorem exists_not_dvd_of_pos_lt_lcm {m k : ℕ} (hmpos : 0 < m)
    (hm : m < (Finset.Icc 1 k).lcm id) :
    ∃ i ∈ Finset.Icc 1 k, ¬ i ∣ m := by
  classical
  by_contra h
  push Not at h
  have hlcm_dvd : (Finset.Icc 1 k).lcm id ∣ m := by
    exact Finset.lcm_dvd h
  exact (not_le_of_gt hm) (Nat.le_of_dvd hmpos hlcm_dvd)

def onesPartition (n : ℕ) : n.Partition where
  parts := Multiset.replicate n 1
  parts_pos := by
    intro i hi
    exact Nat.lt_of_lt_of_eq zero_lt_one (Multiset.eq_of_mem_replicate hi).symm
  parts_sum := by
    simp

theorem bounded_onesPartition {n k : ℕ} (hk : 1 ≤ k) :
    Bounded k (onesPartition n) := by
  intro i hi
  rw [Multiset.eq_of_mem_replicate hi]
  exact hk

def quotRemParts (m i : ℕ) : Multiset ℕ :=
  Multiset.replicate ((2 * m) / i) i +
    if (2 * m) % i = 0 then 0 else ({(2 * m) % i} : Multiset ℕ)

theorem quotRemParts_sum (m i : ℕ) : (quotRemParts m i).sum = 2 * m := by
  by_cases hr : (2 * m) % i = 0
  · have hsum : ((2 * m) / i) * i = 2 * m := by
      have h := Nat.div_add_mod (2 * m) i
      rw [hr, add_zero] at h
      simpa [Nat.mul_comm] using h
    simp [quotRemParts, hr, hsum]
  · have hsum :
        ((2 * m) / i) * i + (2 * m) % i = 2 * m := by
      simpa [Nat.mul_comm] using Nat.div_add_mod (2 * m) i
    simp [quotRemParts, hr, hsum]

def quotRemPartition (m i : ℕ) (hi : 0 < i) : (2 * m).Partition where
  parts := quotRemParts m i
  parts_pos := by
    intro x hx
    unfold quotRemParts at hx
    by_cases hr : (2 * m) % i = 0
    · simp only [hr, ↓reduceIte, add_zero] at hx
      exact (Multiset.mem_replicate.mp hx).2 ▸ hi
    · simp only [hr, ↓reduceIte, Multiset.mem_add, Multiset.mem_replicate,
        Multiset.mem_singleton] at hx
      rcases hx with hx | hx
      · exact hx.2 ▸ hi
      · exact Nat.pos_of_ne_zero (by
          intro hzero
          exact hr (hx.symm.trans hzero))
  parts_sum := quotRemParts_sum m i

theorem bounded_quotRemPartition {m i k : ℕ} (hi : 0 < i) (hik : i ≤ k) :
    Bounded k (quotRemPartition m i hi) := by
  intro x hx
  change x ∈ quotRemParts m i at hx
  unfold quotRemParts at hx
  by_cases hr : (2 * m) % i = 0
  · simp only [hr, ↓reduceIte, add_zero] at hx
    exact (Multiset.mem_replicate.mp hx).2 ▸ hik
  · simp only [hr, ↓reduceIte, Multiset.mem_add, Multiset.mem_replicate,
      Multiset.mem_singleton] at hx
    rcases hx with hx | hx
    · exact hx.2 ▸ hik
    · simpa [hx] using (Nat.mod_lt (2 * m) hi).le.trans hik

theorem sum_modEq_zero_of_le_replicate {t : Multiset ℕ} {q i : ℕ}
    (ht : t ≤ Multiset.replicate q i) : t.sum ≡ 0 [MOD i] := by
  have ht_eq : t = Multiset.replicate t.card i := by
    rw [Multiset.eq_replicate_card]
    intro x hx
    exact Multiset.eq_of_mem_replicate (Multiset.mem_of_le ht hx)
  rw [Nat.modEq_zero_iff_dvd]
  refine ⟨t.card, ?_⟩
  rw [ht_eq, Multiset.sum_replicate, Nat.nsmul_eq_mul, Multiset.card_replicate, Nat.mul_comm]

private theorem le_replicate_of_le_replicate_add_singleton_of_notMem
    {t : Multiset ℕ} {q i r : ℕ}
    (ht : t ≤ Multiset.replicate q i + ({r} : Multiset ℕ)) (hr : r ∉ t) :
    t ≤ Multiset.replicate q i := by
  rw [Multiset.le_iff_count] at ht ⊢
  intro a
  by_cases har : a = r
  · subst a
    simp [Multiset.count_eq_zero_of_notMem hr]
  · have hta := ht a
    simpa [Multiset.count_add, Multiset.count_singleton, har] using hta

private theorem erase_le_replicate_of_le_replicate_add_singleton
    {t : Multiset ℕ} {q i r : ℕ}
    (ht : t ≤ Multiset.replicate q i + ({r} : Multiset ℕ)) :
    t.erase r ≤ Multiset.replicate q i := by
  rw [Multiset.le_iff_count] at ht ⊢
  intro a
  by_cases har : a = r
  · subst a
    have htr := ht r
    simp [Multiset.count_erase_self, Multiset.count_add] at htr ⊢
    omega
  · have hta := ht a
    simpa [Multiset.count_erase_of_ne har, Multiset.count_add, Multiset.count_singleton, har]
      using hta

theorem sum_modEq_quotRemParts {m i : ℕ} {t : Multiset ℕ}
    (ht : t ≤ quotRemParts m i) :
    t.sum ≡ 0 [MOD i] ∨ t.sum ≡ (2 * m) % i [MOD i] := by
  unfold quotRemParts at ht
  by_cases hr : (2 * m) % i = 0
  · left
    simp only [hr, ↓reduceIte, add_zero] at ht
    exact sum_modEq_zero_of_le_replicate ht
  · simp only [hr, ↓reduceIte] at ht
    by_cases hmem : (2 * m) % i ∈ t
    · right
      have herase :
          (t.erase ((2 * m) % i)).sum ≡ 0 [MOD i] :=
        sum_modEq_zero_of_le_replicate
          (erase_le_replicate_of_le_replicate_add_singleton ht)
      have hsum :
          t.sum = (2 * m) % i + (t.erase ((2 * m) % i)).sum := by
        rw [← Multiset.sum_cons, Multiset.cons_erase hmem]
      rw [hsum]
      exact (Nat.ModEq.refl ((2 * m) % i)).add herase
    · left
      exact sum_modEq_zero_of_le_replicate
        (le_replicate_of_le_replicate_add_singleton_of_notMem ht hmem)

theorem no_submultiset_sum_quotRemPartition {m i : ℕ} (hi : 0 < i)
    (hndvd : ¬ i ∣ m) :
    ∀ t ≤ (quotRemPartition m i hi).parts, t.sum ≠ m := by
  intro t ht hsum
  have hmod :
      t.sum ≡ 0 [MOD i] ∨ t.sum ≡ (2 * m) % i [MOD i] :=
    sum_modEq_quotRemParts (m := m) (i := i) (by simpa [quotRemPartition] using ht)
  rcases hmod with hzero | hrem
  · exact hndvd (Nat.modEq_zero_iff_dvd.mp (by simpa [hsum] using hzero))
  · have hm_mod : m ≡ (2 * m) % i [MOD i] := by
      simpa [hsum] using hrem
    have hm_two : m ≡ 2 * m [MOD i] :=
      hm_mod.trans (Nat.mod_modEq (2 * m) i)
    have hmle : m ≤ 2 * m := by omega
    have hdvd_sub : i ∣ 2 * m - m :=
      (Nat.modEq_iff_dvd' hmle).mp hm_two
    have hsub : 2 * m - m = m := by omega
    exact hndvd (by simpa [hsub] using hdvd_sub)

theorem not_balanceable_quotRemPartition {m i : ℕ} (hi : 0 < i)
    (hndvd : ¬ i ∣ m) : ¬ Balanceable (quotRemPartition m i hi) := by
  exact not_balanceable_of_no_submultiset_sum
    (no_submultiset_sum_quotRemPartition hi hndvd)

theorem not_balanceable_onesPartition_of_odd {n : ℕ} (hn : Odd n) :
    ¬ Balanceable (onesPartition n) := by
  intro hb
  exact (Nat.not_even_iff_odd.mpr hn) (even_of_balanceable hb)

theorem lower_bound_of_bounded_balanceable {k n : ℕ} (hk : 0 < k)
    (hnpos : 0 < n)
    (hbalance : ∀ p : n.Partition, Bounded k p → Balanceable p) :
    2 * (Finset.Icc 1 k).lcm id ≤ n := by
  by_contra hnot
  have hnlt : n < 2 * (Finset.Icc 1 k).lcm id := Nat.lt_of_not_ge hnot
  rcases Nat.even_or_odd n with hn_even | hn_odd
  · rcases hn_even with ⟨m, rfl⟩
    rw [show m + m = 2 * m by omega] at hnpos hnlt hbalance
    have hmpos : 0 < m := by omega
    have hmlt : m < (Finset.Icc 1 k).lcm id := by omega
    rcases exists_not_dvd_of_pos_lt_lcm hmpos hmlt with ⟨i, hi_mem, hndvd⟩
    have hi_pos : 0 < i := (Finset.mem_Icc.mp hi_mem).1
    have hik : i ≤ k := (Finset.mem_Icc.mp hi_mem).2
    exact not_balanceable_quotRemPartition hi_pos hndvd
      (hbalance (quotRemPartition m i hi_pos)
        (bounded_quotRemPartition hi_pos hik))
  · exact not_balanceable_onesPartition_of_odd hn_odd
      (hbalance (onesPartition n) (bounded_onesPartition hk))

end Submission.Helpers
