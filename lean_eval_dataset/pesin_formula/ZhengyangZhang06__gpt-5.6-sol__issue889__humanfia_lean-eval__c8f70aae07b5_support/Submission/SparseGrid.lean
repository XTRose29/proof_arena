import Submission.SparseNodeRecurrence

namespace Submission.Helpers

noncomputable def finiteBadCountNat (good : ℕ → Prop) (L : ℕ) : ℕ := by
  classical
  exact ((Finset.range L).filter fun i => ¬good i).card

noncomputable def gridIndexSet (H L : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range L).filter fun j => H * j < L

noncomputable def selectedGridIndices
    (H L : ℕ) (good : ℕ → Prop) : Finset ℕ := by
  classical
  exact (gridIndexSet H L).filter fun j => good (H * j)

noncomputable def badGridIndices
    (H L : ℕ) (good : ℕ → Prop) : Finset ℕ := by
  classical
  exact (gridIndexSet H L).filter fun j => ¬good (H * j)

lemma mem_gridIndexSet_iff {H L j : ℕ} :
    j ∈ gridIndexSet H L ↔ j < L ∧ H * j < L := by
  classical
  simp [gridIndexSet]

lemma card_gridIndexSet_le_div_add_one
    {H L : ℕ} (hH : 0 < H) :
    (gridIndexSet H L).card ≤ L / H + 1 := by
  classical
  calc
    (gridIndexSet H L).card ≤ (Finset.range (L / H + 1)).card := by
      apply Finset.card_le_card
      intro j hj
      have hj' := mem_gridIndexSet_iff.mp hj
      apply Finset.mem_range.mpr
      rw [Nat.lt_succ_iff]
      exact (Nat.le_div_iff_mul_le hH).2 (by
        simpa [Nat.mul_comm] using hj'.2.le)
    _ = L / H + 1 := Finset.card_range _

lemma length_le_mul_card_gridIndexSet
    {H L : ℕ} (hH : 0 < H) (hL : 0 < L) :
    L ≤ H * (gridIndexSet H L).card := by
  classical
  let q := (L - 1) / H
  have hsubset : Finset.range (q + 1) ⊆ gridIndexSet H L := by
    intro j hj
    have hjq : j ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hqmul : H * q ≤ L - 1 := by
      simpa [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le hH).mp (show q ≤ (L - 1) / H from le_rfl)
    have hjtime : H * j < L := by
      exact (Nat.mul_le_mul_left H hjq).trans_lt (by omega)
    have hjL : j < L :=
      (Nat.le_mul_of_pos_left j hH).trans_lt hjtime
    exact mem_gridIndexSet_iff.mpr ⟨hjL, hjtime⟩
  have hcard : q + 1 ≤ (gridIndexSet H L).card := by
    simpa using Finset.card_le_card hsubset
  have hmod : (L - 1) % H < H := Nat.mod_lt _ hH
  have hdecomp :
      (L - 1) % H + H * q = L - 1 := by
    simpa [q] using Nat.mod_add_div (L - 1) H
  calc
    L = (L - 1) % H + H * q + 1 := by omega
    _ ≤ H * q + H := by omega
    _ = H * (q + 1) := by rw [Nat.mul_add]; simp
    _ ≤ H * (gridIndexSet H L).card :=
      Nat.mul_le_mul_left H hcard

lemma selectedGridIndices_nonempty_of_weighted_bad_lt
    {H L B : ℕ} (hH : 0 < H) (hBL : B < L)
    (good : ℕ → Prop)
    (hbad : H * (badGridIndices H L good).card ≤ B) :
    (selectedGridIndices H L good).Nonempty := by
  classical
  by_contra hS
  have hSempty : selectedGridIndices H L good = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hS
  have hgridbad : gridIndexSet H L = badGridIndices H L good := by
    ext j
    constructor
    · intro hj
      have hjbad : ¬good (H * j) := by
        intro hjgood
        have hjs : j ∈ selectedGridIndices H L good := by
          exact Finset.mem_filter.mpr ⟨hj, hjgood⟩
        rw [hSempty] at hjs
        simp at hjs
      exact Finset.mem_filter.mpr ⟨hj, hjbad⟩
    · exact fun hj => (Finset.mem_filter.mp hj).1
  have hLpos : 0 < L := lt_of_le_of_lt (Nat.zero_le B) hBL
  have hlength := length_le_mul_card_gridIndexSet hH hLpos
  rw [hgridbad] at hlength
  omega

lemma exists_selectedGridIndex_before
    {H L j₀ : ℕ} (hH : 0 < H) (good : ℕ → Prop)
    (hj₀ : j₀ ∈ gridIndexSet H L)
    (hbadj :
      (badGridIndices H L good).card ≤ j₀) :
    ∃ q ∈ selectedGridIndices H L good,
      q ≤ j₀ ∧ j₀ - q ≤ (badGridIndices H L good).card := by
  classical
  let b := (badGridIndices H L good).card
  by_contra hnone
  have hsubset : Finset.Icc (j₀ - b) j₀ ⊆
      badGridIndices H L good := by
    intro q hq
    have hqIcc := Finset.mem_Icc.mp hq
    have hj₀' := mem_gridIndexSet_iff.mp hj₀
    have hqtime : H * q < L :=
      (Nat.mul_le_mul_left H hqIcc.2).trans_lt hj₀'.2
    have hqL : q < L :=
      (Nat.le_mul_of_pos_left q hH).trans_lt hqtime
    have hqgrid : q ∈ gridIndexSet H L :=
      mem_gridIndexSet_iff.mpr ⟨hqL, hqtime⟩
    have hqnotgood : ¬good (H * q) := by
      intro hqgood
      exact hnone ⟨q,
        Finset.mem_filter.mpr ⟨hqgrid, hqgood⟩,
        hqIcc.2, by omega⟩
    exact Finset.mem_filter.mpr ⟨hqgrid, hqnotgood⟩
  have hcard := Finset.card_le_card hsubset
  have hb_le : b ≤ j₀ := hbadj
  rw [Nat.card_Icc] at hcard
  dsimp [b] at hcard
  omega

private lemma tail_gap_le_budget_add_step
    {H L J q B : ℕ} (hL : 0 < L) (_hqJ : q ≤ J)
    (hdecomp : (L - 1) % H + H * J = L - 1)
    (hmod : (L - 1) % H < H)
    (hgap : H * (J - q) ≤ B) :
    L - H * q ≤ B + H := by
  have hmul : H * (J - q) = H * J - H * q :=
    Nat.mul_sub_left_distrib H J q
  omega

lemma exists_selectedGridIndex_center_with_endpoint_bounds
    {H m n B : ℕ} (hH : 0 < H) (hn : 0 < n) (hBm : B < m)
    (good : ℕ → Prop)
    (hbudget :
      H * (badGridIndices H (m + n) good).card ≤ B) :
    ∃ hS : (selectedGridIndices H (m + n) good).Nonempty,
      ∃ i : Fin (selectedGridIndices H (m + n) good).card,
        H * (selectedGridIndices H (m + n) good).orderEmbOfFin rfl
              ⟨0, Finset.card_pos.mpr hS⟩ ≤ B ∧
          H * (selectedGridIndices H (m + n) good).orderEmbOfFin rfl i ≤ m ∧
          m - H * (selectedGridIndices H (m + n) good).orderEmbOfFin rfl i ≤
            B + H ∧
          m + n -
              H * (selectedGridIndices H (m + n) good).orderEmbOfFin rfl
                ⟨(selectedGridIndices H (m + n) good).card - 1,
                  Nat.sub_lt (Finset.card_pos.mpr hS)
                    (Nat.succ_pos 0)⟩ ≤
            B + H := by
  classical
  let L := m + n
  let S := selectedGridIndices H L good
  let b := (badGridIndices H L good).card
  have hbudget' : H * b ≤ B := by
    simpa [b, L] using hbudget
  have hBL : B < L := hBm.trans (Nat.lt_add_of_pos_right hn)
  have hS : S.Nonempty := by
    apply selectedGridIndices_nonempty_of_weighted_bad_lt hH hBL
    simpa [L, b] using hbudget
  have hSpos : 0 < S.card := Finset.card_pos.mpr hS
  let first : Fin S.card := ⟨0, hSpos⟩
  let last : Fin S.card :=
    ⟨S.card - 1, Nat.sub_lt hSpos (Nat.succ_pos 0)⟩
  let j₀ := m / H
  have hj₀time : H * j₀ ≤ m := by
    exact Nat.mul_div_le m H
  have hj₀grid : j₀ ∈ gridIndexSet H L := by
    apply mem_gridIndexSet_iff.mpr
    have hj₀L : j₀ < L := by
      by_cases hj₀zero : j₀ = 0
      · simpa [hj₀zero, L] using Nat.add_pos_right m hn
      · exact (Nat.le_mul_of_pos_left j₀ hH).trans_lt
          (hj₀time.trans_lt (Nat.lt_add_of_pos_right hn))
    exact ⟨hj₀L, hj₀time.trans_lt (Nat.lt_add_of_pos_right hn)⟩
  have hbj₀ : b ≤ j₀ := by
    apply (Nat.le_div_iff_mul_le hH).2
    simpa [Nat.mul_comm] using (hbudget'.trans (Nat.le_of_lt hBm))
  obtain ⟨q, hqS, hqj₀, hj₀q⟩ :=
    exists_selectedGridIndex_before hH good hj₀grid hbj₀
  have hqi :
      q ∈ Finset.image (S.orderEmbOfFin rfl) Finset.univ := by
    simpa [S, L] using hqS
  obtain ⟨i, _hi, hiq⟩ := Finset.mem_image.mp hqi
  have hqindex :
      S.orderEmbOfFin rfl i = q := hiq
  have hbtime : H * b < L := by
    exact hbudget'.trans_lt hBL
  have hbL : b < L :=
    (Nat.le_mul_of_pos_left b hH).trans_lt hbtime
  have hbgrid : b ∈ gridIndexSet H L :=
    mem_gridIndexSet_iff.mpr ⟨hbL, hbtime⟩
  obtain ⟨qsmall, hqsmallS, hqsmallb, _hbqsmall⟩ :=
    exists_selectedGridIndex_before hH good hbgrid le_rfl
  have hqsmallImage :
      qsmall ∈ Finset.image (S.orderEmbOfFin rfl) Finset.univ := by
    simpa [S, L] using hqsmallS
  obtain ⟨ismall, _hismall, hismall⟩ :=
    Finset.mem_image.mp hqsmallImage
  have hfirst_le :
      S.orderEmbOfFin rfl first ≤ qsmall := by
    have hmono := (S.orderEmbOfFin rfl).monotone
      (show first ≤ ismall by
        apply Fin.le_iff_val_le_val.mpr
        simp [first])
    exact hmono.trans_eq hismall
  let J := (L - 1) / H
  have hJtime : H * J ≤ L - 1 := by
    simpa [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le hH).mp (show J ≤ (L - 1) / H from le_rfl)
  have hJL : J < L := by
    have hLpos : 0 < L := Nat.add_pos_right m hn
    exact (Nat.le_mul_of_pos_left J hH).trans_lt (by omega)
  have hJgrid : J ∈ gridIndexSet H L :=
    mem_gridIndexSet_iff.mpr ⟨hJL, by omega⟩
  have hbJ : b ≤ J := by
    apply (Nat.le_div_iff_mul_le hH).2
    simpa [Nat.mul_comm] using
      (hbudget'.trans (by omega : B ≤ L - 1))
  obtain ⟨qtail, hqtailS, hqtailJ, hJqtail⟩ :=
    exists_selectedGridIndex_before hH good hJgrid hbJ
  have hqtailImage :
      qtail ∈ Finset.image (S.orderEmbOfFin rfl) Finset.univ := by
    simpa [S, L] using hqtailS
  obtain ⟨itail, _hitail, hitail⟩ :=
    Finset.mem_image.mp hqtailImage
  have hitail_last : itail ≤ last := by
    apply Fin.le_iff_val_le_val.mpr
    dsimp [last]
    omega
  have hqtail_le_last :
      qtail ≤ S.orderEmbOfFin rfl last := by
    have hmono := (S.orderEmbOfFin rfl).monotone hitail_last
    exact hitail.symm.trans_le hmono
  have hcenterDecomp : m % H + H * j₀ = m := by
    simpa [j₀] using Nat.mod_add_div m H
  have hcenterMod : m % H < H := Nat.mod_lt m hH
  have hcenterGap :
      H * (j₀ - q) ≤ B := by
    calc
      H * (j₀ - q) ≤ H * b := Nat.mul_le_mul_left H hj₀q
      _ ≤ B := by simpa [b, L] using hbudget
  have hcenterMul :
      H * (j₀ - q) = H * j₀ - H * q := by
    exact Nat.mul_sub_left_distrib H j₀ q
  have hlastDecomp : (L - 1) % H + H * J = L - 1 := by
    simpa [J] using Nat.mod_add_div (L - 1) H
  have hlastMod : (L - 1) % H < H := Nat.mod_lt (L - 1) hH
  have htailMul :
      H * (J - qtail) = H * J - H * qtail := by
    exact Nat.mul_sub_left_distrib H J qtail
  have htailGap : H * (J - qtail) ≤ B := by
    calc
      H * (J - qtail) ≤ H * b := Nat.mul_le_mul_left H hJqtail
      _ ≤ B := by simpa [b, L] using hbudget
  refine ⟨by simpa [S, L] using hS, ?_⟩
  refine ⟨i, ?_, ?_, ?_, ?_⟩
  · have : H * S.orderEmbOfFin rfl first ≤ H * b :=
      Nat.mul_le_mul_left H (hfirst_le.trans hqsmallb)
    simpa [first, S, L, b] using this.trans (by
      simpa [b, L] using hbudget)
  · rw [hqindex]
    exact (Nat.mul_le_mul_left H hqj₀).trans hj₀time
  · rw [hqindex]
    omega
  · have hlastLower :
        H * qtail ≤ H * S.orderEmbOfFin rfl last :=
      Nat.mul_le_mul_left H hqtail_le_last
    exact (Nat.sub_le_sub_left hlastLower L).trans
      (tail_gap_le_budget_add_step (Nat.add_pos_right m hn) hqtailJ
        hlastDecomp hlastMod htailGap)

lemma mem_selectedGridIndices_iff
    {H L : ℕ} {good : ℕ → Prop} {j : ℕ} :
    j ∈ selectedGridIndices H L good ↔
      j < L ∧ H * j < L ∧ good (H * j) := by
  classical
  simp [selectedGridIndices, mem_gridIndexSet_iff, and_assoc]

lemma mem_badGridIndices_iff
    {H L : ℕ} {good : ℕ → Prop} {j : ℕ} :
    j ∈ badGridIndices H L good ↔
      j < L ∧ H * j < L ∧ ¬good (H * j) := by
  classical
  simp [badGridIndices, mem_gridIndexSet_iff, and_assoc]

lemma card_badGridIndices_le_finiteBadCountNat
    {H L : ℕ} (hH : 0 < H) (good : ℕ → Prop) :
    (badGridIndices H L good).card ≤ finiteBadCountNat good L := by
  classical
  let f : ℕ → ℕ := fun j => H * j
  have hf : Function.Injective f := by
    intro a b hab
    exact Nat.mul_left_cancel hH hab
  have hsubset : (badGridIndices H L good).image f ⊆
      (Finset.range L).filter fun i => ¬good i := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    have hj' := mem_badGridIndices_iff.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj'.2.1, hj'.2.2⟩
  rw [← Finset.card_image_of_injective (badGridIndices H L good) hf]
  exact Finset.card_le_card hsubset

lemma selectedGridIndices_disjoint_badGridIndices
    (H L : ℕ) (good : ℕ → Prop) :
    Disjoint (selectedGridIndices H L good) (badGridIndices H L good) := by
  classical
  rw [Finset.disjoint_left]
  intro j hjs hjb
  exact (mem_badGridIndices_iff.mp hjb).2.2
    (mem_selectedGridIndices_iff.mp hjs).2.2

lemma gridIndexSet_eq_selected_union_bad
    (H L : ℕ) (good : ℕ → Prop) :
    gridIndexSet H L =
      selectedGridIndices H L good ∪ badGridIndices H L good := by
  classical
  ext j
  by_cases hj : good (H * j) <;>
    simp [selectedGridIndices, badGridIndices, hj]

noncomputable def selectedGridIndex
    (H L : ℕ) (good : ℕ → Prop)
    (i : Fin (selectedGridIndices H L good).card) : ℕ :=
  (selectedGridIndices H L good).orderEmbOfFin rfl i

lemma selectedGridIndex_mem
    (H L : ℕ) (good : ℕ → Prop)
    (i : Fin (selectedGridIndices H L good).card) :
    selectedGridIndex H L good i ∈ selectedGridIndices H L good := by
  exact Finset.orderEmbOfFin_mem _ rfl i

lemma selectedGridIndex_lt
    (H L : ℕ) (good : ℕ → Prop)
    (i : Fin (selectedGridIndices H L good).card) :
    H * selectedGridIndex H L good i < L :=
  (mem_selectedGridIndices_iff.mp (selectedGridIndex_mem H L good i)).2.1

lemma selectedGridIndex_good
    (H L : ℕ) (good : ℕ → Prop)
    (i : Fin (selectedGridIndices H L good).card) :
    good (H * selectedGridIndex H L good i) :=
  (mem_selectedGridIndices_iff.mp (selectedGridIndex_mem H L good i)).2.2

lemma strictMono_selectedGridIndex
    (H L : ℕ) (good : ℕ → Prop) :
    StrictMono (selectedGridIndex H L good) :=
  (selectedGridIndices H L good).orderEmbOfFin rfl |>.strictMono

lemma strictMono_selectedGridTime
    {H : ℕ} (hH : 0 < H) (L : ℕ) (good : ℕ → Prop) :
    StrictMono (fun i : Fin (selectedGridIndices H L good).card =>
      H * selectedGridIndex H L good i) := by
  intro i j hij
  exact Nat.mul_lt_mul_of_pos_left
    (strictMono_selectedGridIndex H L good hij) hH

lemma card_Icc_sdiff_selectedGridIndices_le_badGridIndices
    {H L : ℕ} (hH : 0 < H) (good : ℕ → Prop)
    (hS : (selectedGridIndices H L good).Nonempty) :
    ((Finset.Icc
        ((selectedGridIndices H L good).min' hS)
        ((selectedGridIndices H L good).max' hS)) \
      selectedGridIndices H L good).card ≤
        (badGridIndices H L good).card := by
  classical
  apply Finset.card_le_card
  intro j hj
  have hjIcc := Finset.mem_Icc.mp (Finset.mem_sdiff.mp hj).1
  have hjnot := (Finset.mem_sdiff.mp hj).2
  have hmax_mem : (selectedGridIndices H L good).max' hS ∈
      selectedGridIndices H L good := Finset.max'_mem _ _
  have hmax_lt :=
    (mem_selectedGridIndices_iff.mp hmax_mem).2.1
  have hjtime : H * j < L :=
    (Nat.mul_le_mul_left H hjIcc.2).trans_lt hmax_lt
  have hjL : j < L := by
    exact (Nat.le_mul_of_pos_left j hH).trans_lt hjtime
  have hjgrid : j ∈ gridIndexSet H L :=
    mem_gridIndexSet_iff.mpr ⟨hjL, hjtime⟩
  have hjbad : ¬good (H * j) := by
    intro hjgood
    apply hjnot
    exact mem_selectedGridIndices_iff.mpr ⟨hjL, hjtime, hjgood⟩
  exact mem_badGridIndices_iff.mpr ⟨hjL, hjtime, hjbad⟩

lemma selectedGridIndex_span_sub_card_le_bad
    {H L : ℕ} (hH : 0 < H) (good : ℕ → Prop)
    (hS : (selectedGridIndices H L good).Nonempty) :
    (selectedGridIndices H L good).max' hS -
        (selectedGridIndices H L good).min' hS + 1 -
        (selectedGridIndices H L good).card ≤
      (badGridIndices H L good).card := by
  classical
  let S := selectedGridIndices H L good
  let a := S.min' hS
  let b := S.max' hS
  have hsub : S ⊆ Finset.Icc a b := by
    intro j hj
    exact Finset.mem_Icc.mpr ⟨Finset.min'_le S j hj, Finset.le_max' S j hj⟩
  have hab : a ≤ b := by
    exact Finset.min'_le S b (Finset.max'_mem S hS)
  have hcard : (Finset.Icc a b \ S).card = b - a + 1 - S.card := by
    rw [Finset.card_sdiff_of_subset hsub, Nat.card_Icc]
    omega
  rw [← hcard]
  exact card_Icc_sdiff_selectedGridIndices_le_badGridIndices hH good hS

lemma sum_range_succ_sub_eq
    (t : ℕ → ℕ) (N : ℕ) (ht : Monotone t) :
    (∑ i ∈ Finset.range N, (t (i + 1) - t i)) = t N - t 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have hstep := ht (Nat.le_succ N)
      have hzero := ht (Nat.zero_le N)
      rw [add_comm]
      exact tsub_add_tsub_cancel hstep hzero

lemma longGapSum_le_two_mul_of_missing
    {N H B : ℕ} (_hH : 0 < H)
    (q : ℕ → ℕ) (hq : Monotone q)
    (hqstep : ∀ i, i < N → q i < q (i + 1))
    (hmissing : q N - q 0 - N ≤ B) :
    (∑ i ∈ Finset.range N,
      if 1 < q (i + 1) - q i then
        H * (q (i + 1) - q i) else 0) ≤ 2 * H * B := by
  have hpoint (i : ℕ) (hi : i < N) :
      (if 1 < q (i + 1) - q i then
          H * (q (i + 1) - q i) else 0) ≤
        2 * H * (q (i + 1) - q i - 1) := by
    split_ifs with hi
    · have hk : q (i + 1) - q i ≤
          2 * (q (i + 1) - q i - 1) := by omega
      nlinarith
    · simp
  calc
    (∑ i ∈ Finset.range N,
        if 1 < q (i + 1) - q i then
          H * (q (i + 1) - q i) else 0) ≤
        ∑ i ∈ Finset.range N, 2 * H * (q (i + 1) - q i - 1) := by
      exact Finset.sum_le_sum fun i hi => hpoint i (Finset.mem_range.mp hi)
    _ = 2 * H *
        (∑ i ∈ Finset.range N, (q (i + 1) - q i - 1)) := by
      rw [Finset.mul_sum]
    _ = 2 * H * (q N - q 0 - N) := by
      congr 1
      have htel := sum_range_succ_sub_eq q N hq
      have hone_le : ∀ i ∈ Finset.range N,
          1 ≤ q (i + 1) - q i := by
        intro i hi
        have hiN := Finset.mem_range.mp hi
        exact Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt (hqstep i hiN))
      calc
        (∑ i ∈ Finset.range N, (q (i + 1) - q i - 1)) =
            (∑ i ∈ Finset.range N, (q (i + 1) - q i)) -
              ∑ _i ∈ Finset.range N, (1 : ℕ) :=
          Finset.sum_tsub_distrib _ hone_le
        _ = q N - q 0 - N := by rw [htel]; simp
    _ ≤ 2 * H * B := Nat.mul_le_mul_left (2 * H) hmissing

/-- The same missing-index estimate, indexed by the consecutive edges of a
finite strictly increasing path. -/
lemma longGapSum_fin_le_two_mul_of_missing
    {N H B : ℕ} (hH : 0 < H)
    (q : Fin (N + 1) → ℕ) (hq : StrictMono q)
    (hmissing : q (Fin.last N) - q 0 - N ≤ B) :
    (∑ i : Fin N,
      if 1 < q i.succ - q i.castSucc then
        H * (q i.succ - q i.castSucc) else 0) ≤ 2 * H * B := by
  let q' : ℕ → ℕ := fun i =>
    q ⟨min i N, Nat.lt_succ_of_le (min_le_right i N)⟩
  have hq'_mono : Monotone q' := by
    intro i j hij
    exact hq.monotone (min_le_min hij le_rfl)
  have hq'_step : ∀ i, i < N → q' i < q' (i + 1) := by
    intro i hi
    apply hq
    simp only [Fin.mk_lt_mk]
    rw [min_eq_left hi.le, min_eq_left (Nat.succ_le_iff.mpr hi)]
    omega
  have hq'_missing : q' N - q' 0 - N ≤ B := by
    have hN : q' N = q (Fin.last N) := by
      apply congrArg q
      apply Fin.ext
      simp
    have hzero : q' 0 = q 0 := by
      apply congrArg q
      apply Fin.ext
      simp
    rw [hN, hzero]
    exact hmissing
  have hmain := longGapSum_le_two_mul_of_missing
    hH q' hq'_mono hq'_step hq'_missing
  rw [← Fin.sum_univ_eq_sum_range] at hmain
  calc
    (∑ i : Fin N,
        if 1 < q i.succ - q i.castSucc then
          H * (q i.succ - q i.castSucc) else 0) =
        ∑ i : Fin N,
          if 1 < q' (i.val + 1) - q' i.val then
            H * (q' (i.val + 1) - q' i.val) else 0 := by
      apply Finset.sum_congr rfl
      intro i _hi
      have hqi : q' i.val = q i.castSucc := by
        apply congrArg q
        apply Fin.ext
        simp
      have hqis : q' (i.val + 1) = q i.succ := by
        apply congrArg q
        apply Fin.ext
        simp
      rw [hqi, hqis]
    _ ≤ 2 * H * B := hmain

/-- Long gaps between consecutive selected grid nodes are paid for by missing
grid indices, hence by bad grid nodes. -/
lemma selectedGridLongGapSum_le_bad
    {H L N : ℕ} (hH : 0 < H) (good : ℕ → Prop)
    (hcard : (selectedGridIndices H L good).card = N + 1) :
    (∑ i : Fin N,
      let q := (selectedGridIndices H L good).orderEmbOfFin hcard
      if 1 < q i.succ - q i.castSucc then
        H * (q i.succ - q i.castSucc) else 0) ≤
      2 * H * (badGridIndices H L good).card := by
  classical
  let S := selectedGridIndices H L good
  have hScard : S.card = N + 1 := by simpa [S] using hcard
  let q : Fin (N + 1) → ℕ := S.orderEmbOfFin hScard
  have hS : S.Nonempty := Finset.card_pos.mp (by rw [hScard]; omega)
  have hzero : q 0 = S.min' hS := by
    simpa [q] using
      (Finset.orderEmbOfFin_zero (s := S) hScard (Nat.succ_pos N))
  have hlast : q (Fin.last N) = S.max' hS := by
    have hlast' :=
      Finset.orderEmbOfFin_last (s := S) hScard (Nat.succ_pos N)
    rw [show Fin.last N =
      (⟨N + 1 - 1, Nat.sub_lt (Nat.succ_pos N) (Nat.succ_pos 0)⟩ :
        Fin (N + 1)) by apply Fin.ext; simp]
    simpa [q] using hlast'
  have hspan := selectedGridIndex_span_sub_card_le_bad hH good hS
  have hmissing : q (Fin.last N) - q 0 - N ≤
      (badGridIndices H L good).card := by
    rw [hzero, hlast]
    dsimp [S] at hspan ⊢
    omega
  simpa [q, S, hScard] using longGapSum_fin_le_two_mul_of_missing
    hH q (S.orderEmbOfFin hScard).strictMono hmissing

lemma longGapSum_fin_card_sub_one_le_two_mul_of_missing
    {M H B : ℕ} (hM : 0 < M) (hH : 0 < H)
    (q : Fin M → ℕ) (hq : StrictMono q)
    (hmissing :
      q ⟨M - 1, Nat.sub_lt hM (Nat.succ_pos 0)⟩ - q ⟨0, hM⟩ -
        (M - 1) ≤ B) :
    (∑ i : Fin (M - 1),
      if 1 < q ⟨i.val + 1, by omega⟩ - q ⟨i.val, by omega⟩ then
        H * (q ⟨i.val + 1, by omega⟩ - q ⟨i.val, by omega⟩) else 0) ≤
      2 * H * B := by
  cases M with
  | zero => simp at hM
  | succ N =>
      have hmain :
          (∑ i : Fin N,
            if 1 < q i.succ - q i.castSucc then
              H * (q i.succ - q i.castSucc) else 0) ≤
            2 * H * B :=
        longGapSum_fin_le_two_mul_of_missing hH q hq hmissing
      calc
        (∑ i : Fin (Nat.succ N - 1),
          if 1 < q ⟨i.val + 1, by omega⟩ - q ⟨i.val, by omega⟩ then
            H * (q ⟨i.val + 1, by omega⟩ - q ⟨i.val, by omega⟩) else 0) =
            ∑ i : Fin N,
              if 1 < q i.succ - q i.castSucc then
                H * (q i.succ - q i.castSucc) else 0 := by
          apply Finset.sum_congr rfl
          intro i _hi
          rfl
        _ ≤ 2 * H * B := hmain

end Submission.Helpers
