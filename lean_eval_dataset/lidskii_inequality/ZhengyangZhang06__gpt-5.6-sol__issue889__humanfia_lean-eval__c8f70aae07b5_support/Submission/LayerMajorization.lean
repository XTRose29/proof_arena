import Submission.Majorization

namespace Submission.LayerMajorization

open Submission.Majorization

def initialSegment {N : ℕ} (k : Fin N) (t : ℝ) (i : Fin N) : ℝ :=
  if i ≤ k then t else 0

lemma descending_layer_decomposition {N : ℕ} (c : Fin (N + 1) → ℝ) (i : Fin (N + 1)) :
    c i = c (Fin.last N) +
      ∑ k : Fin N, initialSegment k.castSucc
        (seqAt c k.val - seqAt c (k.val + 1)) i := by
  have hiN : i.val ≤ N := Nat.lt_succ_iff.mp i.isLt
  have hsum :
      ∑ k : Fin N, initialSegment k.castSucc
          (seqAt c k.val - seqAt c (k.val + 1)) i =
        ∑ k ∈ Finset.Ico i.val N, (seqAt c k - seqAt c (k + 1)) := by
    calc
      ∑ k : Fin N, initialSegment k.castSucc
          (seqAt c k.val - seqAt c (k.val + 1)) i =
          ∑ k ∈ Finset.range N,
            if i.val ≤ k then (seqAt c k - seqAt c (k + 1)) else 0 := by
        rw [← Fin.sum_univ_eq_sum_range
          (fun k ↦ if i.val ≤ k then (seqAt c k - seqAt c (k + 1)) else 0) N]
        apply Fintype.sum_congr
        intro k
        simp only [initialSegment]
        congr 1
      _ = ∑ k ∈ Finset.Ico i.val N, (seqAt c k - seqAt c (k + 1)) := by
        rw [← Finset.sum_filter]
        congr 1
        ext k
        simp [Finset.mem_Ico, and_comm]
  rw [hsum]
  have hrev :
      ∑ k ∈ Finset.Ico i.val N, (seqAt c k - seqAt c (k + 1)) =
        seqAt c i.val - seqAt c N := by
    rw [Finset.sum_Ico_eq_sub _ hiN, Finset.sum_range_sub', Finset.sum_range_sub']
    ring
  rw [hrev]
  have hi : seqAt c i.val = c i := by
    rw [seqAt_of_lt c i.isLt]
  have hlast : seqAt c N = c (Fin.last N) := by
    rw [seqAt_of_lt c (Nat.lt_succ_self N)]
    rfl
  rw [hi, hlast]
  ring

lemma prefix_sum_initialSegment {N : ℕ} (k : Fin N) (t : ℝ)
    (q : ℕ) (hq : q ≤ N) :
    ∑ i ∈ Finset.range q, seqAt (initialSegment k t) i =
      if q ≤ k.val + 1 then q * t else (k.val + 1) * t := by
  split_ifs with hqk
  · calc
      ∑ i ∈ Finset.range q, seqAt (initialSegment k t) i =
          ∑ _i ∈ Finset.range q, t := by
        apply Finset.sum_congr rfl
        intro i hi
        have hiq : i < q := Finset.mem_range.mp hi
        have hiN : i < N := lt_of_lt_of_le hiq hq
        rw [seqAt_of_lt (initialSegment k t) hiN]
        have hikNat : i ≤ k.val := by omega
        have hik : (⟨i, hiN⟩ : Fin N) ≤ k := Fin.mk_le_mk.mpr hikNat
        rw [initialSegment, if_pos hik]
      _ = q * t := by simp
  · have hkq : k.val + 1 ≤ q := by omega
    have hsubset : Finset.range (k.val + 1) ⊆ Finset.range q :=
      Finset.range_mono hkq
    calc
      ∑ i ∈ Finset.range q, seqAt (initialSegment k t) i =
          ∑ i ∈ Finset.range (k.val + 1), seqAt (initialSegment k t) i := by
        symm
        apply Finset.sum_subset hsubset
        intro i hiq hik
        have hiN : i < N := lt_of_lt_of_le (Finset.mem_range.mp hiq) hq
        rw [seqAt_of_lt (initialSegment k t) hiN]
        have hki' : k.val + 1 ≤ i := by
          simpa only [Finset.mem_range, not_lt] using hik
        have hki : k.val < i := by omega
        have hnotle : ¬(⟨i, hiN⟩ : Fin N) ≤ k :=
          not_le.mpr (Fin.mk_lt_mk.mpr hki)
        rw [initialSegment, if_neg hnotle]
      _ = ∑ _i ∈ Finset.range (k.val + 1), t := by
        apply Finset.sum_congr rfl
        intro i hi
        have hiN : i < N := lt_of_lt_of_le (Finset.mem_range.mp hi) (Nat.succ_le_iff.mpr k.isLt)
        rw [seqAt_of_lt (initialSegment k t) hiN]
        have hik : (⟨i, hiN⟩ : Fin N) ≤ k :=
          Fin.mk_le_mk.mpr (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
        rw [initialSegment, if_pos hik]
      _ = (k.val + 1) * t := by simp

lemma prefix_sum_le_of_bounds_total {N : ℕ} {d : Fin N → ℝ} {t : ℝ}
    (hd0 : ∀ i, 0 ≤ d i) (hdt : ∀ i, d i ≤ t) (k : Fin N)
    (hsum : ∑ i, d i = (k.val + 1) * t) (σ : Equiv.Perm (Fin N))
    (q : ℕ) (hq : q ≤ N) :
    ∑ i ∈ Finset.range q, seqAt (d ∘ σ) i ≤
      if q ≤ k.val + 1 then q * t else (k.val + 1) * t := by
  split_ifs with hqk
  · calc
      ∑ i ∈ Finset.range q, seqAt (d ∘ σ) i ≤ ∑ _i ∈ Finset.range q, t := by
        apply Finset.sum_le_sum
        intro i hi
        have hiN : i < N := lt_of_lt_of_le (Finset.mem_range.mp hi) hq
        rw [seqAt_of_lt (d ∘ σ) hiN]
        exact hdt _
      _ = q * t := by simp
  · calc
      ∑ i ∈ Finset.range q, seqAt (d ∘ σ) i ≤
          ∑ i ∈ Finset.range N, seqAt (d ∘ σ) i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hq)
        intro i hiN _
        rw [seqAt_of_lt (d ∘ σ) (Finset.mem_range.mp hiN)]
        exact hd0 _
      _ = ∑ i, d i := by
        calc
          ∑ i ∈ Finset.range N, seqAt (d ∘ σ) i = ∑ i, (d ∘ σ) i := by
            simpa only [id_eq] using (sum_seqAt id (d ∘ σ)).symm
          _ = ∑ i, d i := by
            simpa [Function.comp_def] using σ.sum_comp Finset.univ d
      _ = (k.val + 1) * t := hsum

lemma prefix_sum_le_initialSegment {N : ℕ} {d : Fin N → ℝ} {t : ℝ}
    (hd0 : ∀ i, 0 ≤ d i) (hdt : ∀ i, d i ≤ t) (k : Fin N)
    (hsum : ∑ i, d i = (k.val + 1) * t) (σ : Equiv.Perm (Fin N))
    (q : ℕ) (hq : q ≤ N) :
    ∑ i ∈ Finset.range q, seqAt (d ∘ σ) i ≤
      ∑ i ∈ Finset.range q, seqAt (initialSegment k t) i := by
  rw [prefix_sum_initialSegment k t q hq]
  exact prefix_sum_le_of_bounds_total hd0 hdt k hsum σ q hq

lemma prefix_sum_le_of_layer_decomposition {M L : ℕ} {x y : Fin M → ℝ}
    (m : ℝ) (d : Fin L → Fin M → ℝ) (rank : Fin L → Fin M) (t : Fin L → ℝ)
    (hd0 : ∀ l i, 0 ≤ d l i) (hdt : ∀ l i, d l i ≤ t l)
    (hsum : ∀ l, ∑ i, d l i = ((rank l).val + 1) * t l)
    (hx : ∀ i, x i = m + ∑ l, d l i)
    (hy : ∀ i, y i = m + ∑ l, initialSegment (rank l) (t l) i)
    (σ : Equiv.Perm (Fin M)) (q : ℕ) (hq : q ≤ M) :
    ∑ i ∈ Finset.range q, seqAt (x ∘ σ) i ≤
      ∑ i ∈ Finset.range q, seqAt y i := by
  have hleft :
      ∑ i ∈ Finset.range q, seqAt (x ∘ σ) i =
        q * m + ∑ l, ∑ i ∈ Finset.range q, seqAt (d l ∘ σ) i := by
    calc
      ∑ i ∈ Finset.range q, seqAt (x ∘ σ) i =
          ∑ i ∈ Finset.range q, (m + ∑ l, seqAt (d l ∘ σ) i) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hiM : i < M := lt_of_lt_of_le (Finset.mem_range.mp hi) hq
        rw [seqAt_of_lt (x ∘ σ) hiM]
        change x (σ ⟨i, hiM⟩) = m + ∑ l, seqAt (d l ∘ σ) i
        rw [hx]
        congr 1
        apply Fintype.sum_congr
        intro l
        rw [seqAt_of_lt (d l ∘ σ) hiM]
        rfl
      _ = q * m + ∑ l, ∑ i ∈ Finset.range q, seqAt (d l ∘ σ) i := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [Finset.sum_comm]
  have hright :
      ∑ i ∈ Finset.range q, seqAt y i =
        q * m + ∑ l, ∑ i ∈ Finset.range q,
          seqAt (initialSegment (rank l) (t l)) i := by
    calc
      ∑ i ∈ Finset.range q, seqAt y i =
          ∑ i ∈ Finset.range q,
            (m + ∑ l, seqAt (initialSegment (rank l) (t l)) i) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hiM : i < M := lt_of_lt_of_le (Finset.mem_range.mp hi) hq
        rw [seqAt_of_lt y hiM, hy]
        congr 1
        apply Fintype.sum_congr
        intro l
        rw [seqAt_of_lt (initialSegment (rank l) (t l)) hiM]
      _ = q * m + ∑ l, ∑ i ∈ Finset.range q,
          seqAt (initialSegment (rank l) (t l)) i := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [Finset.sum_comm]
  rw [hleft, hright]
  have hle :
      (∑ l, ∑ i ∈ Finset.range q, seqAt (d l ∘ σ) i) ≤
        ∑ l, ∑ i ∈ Finset.range q,
          seqAt (initialSegment (rank l) (t l)) i := by
    apply Finset.sum_le_sum
    intro l _
    exact prefix_sum_le_initialSegment (hd0 l) (hdt l) (rank l) (hsum l) σ q hq
  linarith

end Submission.LayerMajorization
