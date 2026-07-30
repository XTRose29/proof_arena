import Submission.Helpers

namespace Submission.Upper

theorem exists_nonempty_short_dvd_sum (a : ℕ) (ha : 0 < a) (s : Multiset ℕ)
    (hs : s ≠ 0) (hdiv : a ∣ s.sum) :
    ∃ t ≤ s, t ≠ 0 ∧ t.card ≤ a ∧ a ∣ t.sum := by
  by_cases hcard : s.card ≤ a
  · exact ⟨s, le_rfl, hs, hcard, hdiv⟩
  · let l := s.toList
    let f : Fin (a + 1) → Fin a := fun i =>
      ⟨(l.take i).sum % a, Nat.mod_lt _ ha⟩
    obtain ⟨i, j, hij, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
    have hsegment : ∀ i j : Fin (a + 1), i < j → f i = f j →
        ∃ t ≤ s, t ≠ 0 ∧ t.card ≤ a ∧ a ∣ t.sum := by
      intro i j hij hf
      let seg := (l.drop i).take (j - i)
      let t : Multiset ℕ := seg
      have hjlen : (j : ℕ) ≤ l.length := by
        have hj : (j : ℕ) ≤ a := Nat.le_of_lt_succ j.isLt
        simpa [l] using (show (j : ℕ) ≤ s.card by omega)
      have hseglen : seg.length = (j : ℕ) - i := by
        apply List.length_take_of_le
        simp only [List.length_drop]
        omega
      have ht_le : t ≤ s := by
        rw [← Multiset.coe_toList s]
        exact Multiset.coe_le.mpr
          ((List.take_sublist ((j : ℕ) - i) (l.drop i)).trans
            (List.drop_sublist i l)).subperm
      have ht_ne : t ≠ 0 := by
        intro ht
        have : t.card = 0 := by simp [ht]
        change seg.length = 0 at this
        omega
      have ht_card : t.card ≤ a := by
        change seg.length ≤ a
        rw [hseglen]
        exact le_trans (Nat.sub_le _ _) (Nat.le_of_lt_succ j.isLt)
      have htake : l.take j = l.take i ++ seg := by
        have hji : (j : ℕ) = i + ((j : ℕ) - i) := by omega
        rw [hji, List.take_add]
      have hsum : (l.take j).sum = (l.take i).sum + seg.sum := by
        rw [htake, List.sum_append]
      have hmods : (l.take i).sum % a = (l.take j).sum % a := by
        exact congrArg Fin.val hf
      have hmod : (l.take i).sum ≡ (l.take j).sum [MOD a] := hmods
      rw [hsum] at hmod
      have hzero : 0 ≡ seg.sum [MOD a] :=
        Nat.ModEq.add_left_cancel' (l.take i).sum (by simpa using hmod)
      exact ⟨t, ht_le, ht_ne, ht_card, Nat.modEq_zero_iff_dvd.mp hzero.symm⟩
    rcases lt_or_gt_of_ne hij with hij | hij
    · exact hsegment i j hij hf
    · exact hsegment j i hij hf.symm

theorem exists_weighted_submultiset_near (T k : ℕ) {α : Type*}
    (w : α → ℕ) (s : Multiset α) (hbound : ∀ x ∈ s, w x ≤ k) :
    ∃ u ≤ s, (u.map w).sum ≤ T ∧
      ((u.map w).sum = (s.map w).sum ∨ T < (u.map w).sum + k) := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨0, le_rfl, by simp⟩
  | @cons x s ih =>
      obtain ⟨u, hu, huT, hall | hnear⟩ := ih (fun y hy => hbound y (by simp [hy]))
      · by_cases hfit : w x + (u.map w).sum ≤ T
        · refine ⟨x ::ₘ u, Multiset.cons_le_cons x hu, ?_, Or.inl ?_⟩
          · simpa [add_comm] using hfit
          · simp only [Multiset.map_cons, Multiset.sum_cons]
            rw [hall]
        · refine ⟨u, hu.trans (Multiset.le_cons_self s x), huT, Or.inr ?_⟩
          have hx : w x ≤ k := hbound x (by simp)
          omega
      · exact ⟨u, hu.trans (Multiset.le_cons_self s x), huT, Or.inr hnear⟩

theorem exists_dvd_block_decomposition (a : ℕ) (ha : 0 < a) (s : Multiset ℕ)
    (hdiv : a ∣ s.sum) :
    ∃ blocks : Multiset (Multiset ℕ), blocks.sum = s ∧
      ∀ b ∈ blocks, b ≠ 0 ∧ b.card ≤ a ∧ a ∣ b.sum := by
  revert hdiv
  refine Multiset.strongInductionOn s ?_
  intro s ih hdiv
  by_cases hs : s = 0
  · exact ⟨0, by simp [hs]⟩
  · obtain ⟨t, hts, htne, htcard, htdiv⟩ :=
      exists_nonempty_short_dvd_sum a ha s hs hdiv
    let r := s - t
    have hrne : r ≠ s := by
      intro hrs
      have hcard := congrArg Multiset.card hrs
      rw [Multiset.card_sub hts] at hcard
      have htcardpos : 0 < t.card := Multiset.card_pos.mpr htne
      have htcardle : t.card ≤ s.card := Multiset.card_le_card hts
      omega
    have hrlt : r < s := lt_of_le_of_ne (Multiset.sub_le_self s t) hrne
    have hrsum : r.sum + t.sum = s.sum := by
      rw [← Multiset.sum_add, Multiset.sub_add_cancel hts]
    have hrdiv : a ∣ r.sum := by
      have hsub : a ∣ s.sum - t.sum := Nat.dvd_sub hdiv htdiv
      have heq : s.sum - t.sum = r.sum := by omega
      simpa [heq] using hsub
    obtain ⟨blocks, hblocks, hprops⟩ := ih r hrlt hrdiv
    refine ⟨t ::ₘ blocks, ?_, ?_⟩
    · simp only [Multiset.sum_cons, hblocks]
      rw [add_comm, Multiset.sub_add_cancel hts]
    · intro b hb
      rcases Multiset.mem_cons.mp hb with rfl | hb
      · exact ⟨htne, htcard, htdiv⟩
      · exact hprops b hb

theorem sum_flatten_eq_mul_sum_blockWeights (a : ℕ)
    {blocks : Multiset (Multiset ℕ)}
    (hdiv : ∀ b ∈ blocks, a ∣ b.sum) :
    blocks.sum.sum = a * (blocks.map fun b => b.sum / a).sum := by
  induction blocks using Multiset.induction_on with
  | empty => simp
  | @cons b blocks ih =>
      have hbdiv : a ∣ b.sum := hdiv b (by simp)
      have hrest : ∀ c ∈ blocks, a ∣ c.sum := by
        intro c hc
        exact hdiv c (by simp [hc])
      simp only [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_add]
      rw [ih hrest, Nat.mul_add, Nat.mul_div_cancel' hbdiv]

theorem blockWeight_pos (a : ℕ) (ha : 0 < a) {s : Multiset ℕ}
    (hpos : ∀ x ∈ s, 0 < x) {blocks : Multiset (Multiset ℕ)}
    (hblocks : blocks.sum = s) {b : Multiset ℕ} (hb : b ∈ blocks) (hbne : b ≠ 0)
    (hbdiv : a ∣ b.sum) : 0 < b.sum / a := by
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hbne
  have hb_le : b ≤ s := by
    rw [← hblocks]
    exact Multiset.le_sum_of_mem hb
  have hxpos : 0 < x := hpos x (Multiset.mem_of_le hb_le hx)
  have hxsum : x ≤ b.sum := Multiset.le_sum_of_mem hx
  exact Nat.div_pos (Nat.le_of_dvd (lt_of_lt_of_le hxpos hxsum) hbdiv) ha

theorem blockWeight_le (a k : ℕ) {s : Multiset ℕ}
    (hbound : ∀ x ∈ s, x ≤ k) {blocks : Multiset (Multiset ℕ)}
    (hblocks : blocks.sum = s) {b : Multiset ℕ} (hb : b ∈ blocks)
    (hbcard : b.card ≤ a) : b.sum / a ≤ k := by
  have hb_le : b ≤ s := by
    rw [← hblocks]
    exact Multiset.le_sum_of_mem hb
  have hsum : b.sum ≤ b.card * k := by
    simpa [nsmul_eq_mul] using
      Multiset.sum_le_card_nsmul b k
        (fun x hx => hbound x (Multiset.mem_of_le hb_le hx))
  apply Nat.div_le_of_le_mul
  exact hsum.trans (Nat.mul_le_mul_right k hbcard)

theorem flatten_le_of_le {u blocks : Multiset (Multiset ℕ)} (hu : u ≤ blocks) :
    u.sum ≤ blocks.sum := by
  have hsplit := Multiset.sub_add_cancel hu
  have hsums := congrArg Multiset.sum hsplit
  simp only [Multiset.sum_add] at hsums
  rw [← hsums]
  exact Multiset.le_add_left u.sum (blocks - u).sum

theorem exists_submultiset_sum_of_frequent {k L : ℕ} (hk : 0 < k)
    {s : Multiset ℕ} (hpos : ∀ x ∈ s, 0 < x) (hbound : ∀ x ∈ s, x ≤ k)
    (hsum : s.sum = 2 * L) {a : ℕ} (hcount : k ≤ s.count a)
    (hadiv : a ∣ L) : ∃ t ≤ s, t.sum = L := by
  let c := s.count a
  let r := s.filter fun x => ¬a = x
  have hacount : 0 < s.count a := lt_of_lt_of_le hk hcount
  have hamem : a ∈ s := Multiset.count_pos.mp hacount
  have ha : 0 < a := hpos a hamem
  have hsplit : Multiset.replicate c a + r = s := by
    rw [← Multiset.filter_eq s a]
    exact Multiset.filter_add_not (Eq a) s
  have hsum_split : c * a + r.sum = 2 * L := by
    rw [← hsum, ← hsplit, Multiset.sum_add, Multiset.sum_replicate, Nat.nsmul_eq_mul]
  let T := L / a
  have hLT : a * T = L := Nat.mul_div_cancel' hadiv
  by_cases hTc : T ≤ c
  · refine ⟨Multiset.replicate T a, ?_, ?_⟩
    · rw [← hsplit]
      exact (Multiset.replicate_mono a hTc).trans
        (Multiset.le_add_right (Multiset.replicate c a) r)
    · simp [Multiset.sum_replicate, Nat.mul_comm, hLT]
  · have hcT : c < T := Nat.lt_of_not_ge hTc
    have hrdiv : a ∣ r.sum := by
      have htotal : a ∣ 2 * L := dvd_mul_of_dvd_right hadiv 2
      have hcopies : a ∣ c * a := dvd_mul_left a c
      have hsub : a ∣ 2 * L - c * a := Nat.dvd_sub htotal hcopies
      have heq : 2 * L - c * a = r.sum := by omega
      simpa [heq] using hsub
    obtain ⟨blocks, hblocks, hprops⟩ := exists_dvd_block_decomposition a ha r hrdiv
    let w : Multiset ℕ → ℕ := fun b => b.sum / a
    have hwbound : ∀ b ∈ blocks, w b ≤ k := by
      intro b hb
      exact blockWeight_le a k (fun x hx => hbound x (Multiset.mem_of_mem_filter hx))
        hblocks hb (hprops b hb).2.1
    have hwpos : ∀ b ∈ blocks, 0 < w b := by
      intro b hb
      exact blockWeight_pos a ha (fun x hx => hpos x (Multiset.mem_of_mem_filter hx))
        hblocks hb (hprops b hb).1 (hprops b hb).2.2
    have hweight_eq : c + (blocks.map w).sum = 2 * T := by
      apply Nat.mul_left_cancel ha
      have hflat := sum_flatten_eq_mul_sum_blockWeights a
        (fun b hb => (hprops b hb).2.2)
      rw [hblocks] at hflat
      calc
        a * (c + (blocks.map w).sum) = c * a + r.sum := by
          rw [Nat.mul_add, Nat.mul_comm a c, hflat]
        _ = 2 * L := hsum_split
        _ = a * (2 * T) := by rw [← hLT]; ring
    have hweight_gt : T < (blocks.map w).sum := by omega
    obtain ⟨u, hu, huT, hall | hnear⟩ :=
      exists_weighted_submultiset_near T k w blocks hwbound
    · rw [hall] at huT
      exact (not_lt_of_ge huT hweight_gt).elim
    · let q := (u.map w).sum
      let x := T - q
      have hxle : x ≤ c := by
        dsimp [x, q]
        omega
      have hcopies : Multiset.replicate x a ≤ Multiset.replicate c a :=
        Multiset.replicate_mono a hxle
      have hu_flat : u.sum ≤ r := by
        rw [← hblocks]
        exact flatten_le_of_le hu
      refine ⟨Multiset.replicate x a + u.sum, ?_, ?_⟩
      · rw [← hsplit]
        exact add_le_add hcopies hu_flat
      · have hudiv : ∀ b ∈ u, a ∣ b.sum := by
          intro b hb
          exact (hprops b (Multiset.mem_of_le hu hb)).2.2
        have huflat := sum_flatten_eq_mul_sum_blockWeights a hudiv
        change u.sum.sum = a * q at huflat
        simp only [Multiset.sum_add, Multiset.sum_replicate, Nat.nsmul_eq_mul]
        rw [huflat]
        have hxq : x + q = T := by
          dsimp [x, q]
          omega
        calc
          x * a + a * q = a * (x + q) := by ring
          _ = a * T := by rw [hxq]
          _ = L := hLT

theorem eq_sum_replicate_count_Icc {k : ℕ} {s : Multiset ℕ}
    (hpos : ∀ x ∈ s, 0 < x) (hbound : ∀ x ∈ s, x ≤ k) :
    (∑ i ∈ Finset.Icc 1 k, Multiset.replicate (s.count i) i) = s := by
  have hsub : s.toFinset ⊆ Finset.Icc 1 k := by
    intro x hx
    have hxs : x ∈ s := Multiset.mem_toFinset.mp hx
    exact Finset.mem_Icc.mpr ⟨hpos x hxs, hbound x hxs⟩
  have hsum :
      (∑ i ∈ s.toFinset, Multiset.replicate (s.count i) i) =
        ∑ i ∈ Finset.Icc 1 k, Multiset.replicate (s.count i) i := by
    apply Finset.sum_subset hsub
    intro x _ hx
    have hxs : x ∉ s := by simpa using hx
    rw [Multiset.count_eq_zero_of_notMem hxs]
    simp
  calc
    (∑ i ∈ Finset.Icc 1 k, Multiset.replicate (s.count i) i) =
        ∑ i ∈ s.toFinset, Multiset.replicate (s.count i) i := hsum.symm
    _ = s := by simpa [Multiset.nsmul_singleton] using
      Multiset.toFinset_sum_count_nsmul_eq s

theorem sum_eq_sum_count_Icc {k : ℕ} {s : Multiset ℕ}
    (hpos : ∀ x ∈ s, 0 < x) (hbound : ∀ x ∈ s, x ≤ k) :
    s.sum = ∑ i ∈ Finset.Icc 1 k, s.count i * i := by
  have hrepr := congrArg Multiset.sum (eq_sum_replicate_count_Icc hpos hbound)
  simpa [Multiset.sum_sum, Multiset.sum_replicate, Nat.nsmul_eq_mul] using hrepr.symm

theorem sum_Icc_id_mul_two (k : ℕ) :
    (∑ i ∈ Finset.Icc 1 k, i) * 2 = k * (k + 1) := by
  have hIcc : Finset.Icc 1 k = (Finset.range (k + 1)).erase 0 := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_erase, Finset.mem_range]
    omega
  rw [hIcc]
  have herase :
      (∑ i ∈ (Finset.range (k + 1)).erase 0, i) =
        ∑ i ∈ Finset.range (k + 1), i := by
    exact Finset.sum_erase (Finset.range (k + 1)) (f := fun i : ℕ => i) rfl
  rw [herase]
  simpa [Nat.mul_comm] using Finset.sum_range_id_mul_two (k + 1)

theorem exists_frequent_of_sum_gt_capacity {k : ℕ} (hk : 0 < k)
    {s : Multiset ℕ} (hpos : ∀ x ∈ s, 0 < x) (hbound : ∀ x ∈ s, x ≤ k)
    (hlarge : (k - 1) * (∑ i ∈ Finset.Icc 1 k, i) < s.sum) :
    ∃ a, k ≤ s.count a := by
  by_contra h
  push Not at h
  have hcap : s.sum ≤ (k - 1) * (∑ i ∈ Finset.Icc 1 k, i) := by
    rw [sum_eq_sum_count_Icc hpos hbound]
    calc
      (∑ i ∈ Finset.Icc 1 k, s.count i * i) ≤
          ∑ i ∈ Finset.Icc 1 k, (k - 1) * i := by
        apply Finset.sum_le_sum
        intro i hi
        have hicount := h i
        exact Nat.mul_le_mul_right i (by omega)
      _ = (k - 1) * (∑ i ∈ Finset.Icc 1 k, i) := by
        rw [Finset.mul_sum]
  exact (not_lt_of_ge hcap hlarge).elim

theorem coprime_succ (n : ℕ) : Nat.Coprime n (n + 1) := by
  exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right n)

theorem top_three_product_le_two_lcm (k : ℕ) (hk : 6 ≤ k) :
    (k - 2) * (k - 1) * k ≤ 2 * (Finset.Icc 1 k).lcm id := by
  let L := (Finset.Icc 1 k).lcm id
  let A := (k - 2) * (k - 1)
  let g := Nat.gcd A k
  have hkprev : Nat.Coprime k (k - 1) := by
    have h := (coprime_succ (k - 1)).symm
    have heq : k - 1 + 1 = k := by omega
    simpa [heq] using h
  have hgk : g ∣ k := Nat.gcd_dvd_right A k
  have hgA : g ∣ A := Nat.gcd_dvd_left A k
  have hgprev : Nat.Coprime g (k - 1) := hkprev.of_dvd_left hgk
  have hgkm2 : g ∣ k - 2 := by
    apply hgprev.dvd_of_dvd_mul_right
    simpa [A] using hgA
  have hg2 : g ∣ 2 := by
    have hsub := Nat.dvd_sub hgk hgkm2
    have heq : k - (k - 2) = 2 := by omega
    simpa [heq] using hsub
  have hgle : g ≤ 2 := Nat.le_of_dvd (by norm_num) hg2
  have hpair : Nat.Coprime (k - 2) (k - 1) := by
    have h := coprime_succ (k - 2)
    have heq : k - 2 + 1 = k - 1 := by omega
    simpa [heq] using h
  have hkm2 : k - 2 ∣ L := by
    exact Submission.Helpers.dvd_lcm_Icc (by omega) (by omega)
  have hkm1 : k - 1 ∣ L := by
    exact Submission.Helpers.dvd_lcm_Icc (by omega) (by omega)
  have hk_dvd : k ∣ L := Submission.Helpers.dvd_lcm_Icc (by omega) le_rfl
  have hA : A ∣ L := by
    simpa [A] using hpair.mul_dvd_of_dvd_of_dvd hkm2 hkm1
  have hlcm_dvd : Nat.lcm A k ∣ L := Nat.lcm_dvd hA hk_dvd
  have hLpos : 0 < L := Submission.Helpers.lcm_Icc_pos k (by omega)
  have hlcm_le : Nat.lcm A k ≤ L := Nat.le_of_dvd hLpos hlcm_dvd
  calc
    (k - 2) * (k - 1) * k = A * k := by rfl
    _ = g * Nat.lcm A k := (Nat.gcd_mul_lcm A k).symm
    _ ≤ 2 * L := Nat.mul_le_mul hgle hlcm_le

theorem capacity_lt_two_lcm_of_five_le (k : ℕ) (hk : 5 ≤ k) :
    (k - 1) * (∑ i ∈ Finset.Icc 1 k, i) <
      2 * (Finset.Icc 1 k).lcm id := by
  rcases eq_or_lt_of_le hk with rfl | hk6
  · decide
  · have hprod := top_three_product_le_two_lcm k hk6
    have htri := sum_Icc_id_mul_two k
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (show 6 ≤ k by omega)
    have hm2 : m + 6 - 2 = m + 4 := by omega
    have hm1 : m + 6 - 1 = m + 5 := by omega
    rw [hm2, hm1] at hprod
    rw [hm1]
    ring_nf at hprod htri ⊢
    nlinarith

theorem exists_submultiset_sum_three {s : Multiset ℕ}
    (hpos : ∀ x ∈ s, 0 < x) (hbound : ∀ x ∈ s, x ≤ 3)
    (hsum : s.sum = 12) : ∃ t ≤ s, t.sum = 6 := by
  have hIcc : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hcounts := sum_eq_sum_count_Icc hpos hbound
  rw [hIcc] at hcounts
  simp at hcounts
  rw [hsum] at hcounts
  have hrepr := eq_sum_replicate_count_Icc hpos hbound
  rw [hIcc] at hrepr
  simp at hrepr
  have hmake : ∀ x₁ x₂ x₃,
      x₁ ≤ s.count 1 → x₂ ≤ s.count 2 → x₃ ≤ s.count 3 →
      x₁ * 1 + x₂ * 2 + x₃ * 3 = 6 → ∃ t ≤ s, t.sum = 6 := by
    intro x₁ x₂ x₃ hx₁ hx₂ hx₃ hxsum
    let t := Multiset.replicate x₁ 1 +
      (Multiset.replicate x₂ 2 + Multiset.replicate x₃ 3)
    refine ⟨t, ?_, ?_⟩
    · rw [← hrepr]
      exact add_le_add (Multiset.replicate_mono 1 hx₁)
        (add_le_add (Multiset.replicate_mono 2 hx₂)
          (Multiset.replicate_mono 3 hx₃))
    · simp only [t, Multiset.sum_add, Multiset.sum_replicate, Nat.nsmul_eq_mul]
      simpa [add_assoc] using hxsum
  by_cases h3two : 2 ≤ s.count 3
  · exact hmake 0 0 2 (by omega) (by omega) h3two (by norm_num)
  · have h3le : s.count 3 ≤ 1 := by omega
    by_cases h3one : 1 ≤ s.count 3
    · have h3eq : s.count 3 = 1 := by omega
      by_cases h1three : 3 ≤ s.count 1
      · exact hmake 3 0 1 h1three (by omega) h3one (by norm_num)
      · have h1le : s.count 1 ≤ 2 := by omega
        have h1pos : 1 ≤ s.count 1 := by omega
        have h2pos : 1 ≤ s.count 2 := by omega
        exact hmake 1 1 1 h1pos h2pos h3one (by norm_num)
    · have h3zero : s.count 3 = 0 := by omega
      by_cases h2three : 3 ≤ s.count 2
      · exact hmake 0 3 0 (by omega) h2three (by omega) (by norm_num)
      · have h2le : s.count 2 ≤ 2 := by omega
        have h1six : 6 ≤ s.count 1 := by omega
        exact hmake 6 0 0 h1six (by omega) (by omega) (by norm_num)

private theorem finite_counts_four :
    ∀ c₁ : Fin 25, ∀ c₂ : Fin 13, ∀ c₃ : Fin 9, ∀ c₄ : Fin 7,
      (c₁ : ℕ) * 1 + (c₂ : ℕ) * 2 + (c₃ : ℕ) * 3 + (c₄ : ℕ) * 4 = 24 →
      ∃ x₁ : Fin 13, ∃ x₂ : Fin 7, ∃ x₃ : Fin 5, ∃ x₄ : Fin 4,
        (x₁ : ℕ) ≤ c₁ ∧ (x₂ : ℕ) ≤ c₂ ∧ (x₃ : ℕ) ≤ c₃ ∧ (x₄ : ℕ) ≤ c₄ ∧
          (x₁ : ℕ) * 1 + (x₂ : ℕ) * 2 + (x₃ : ℕ) * 3 + (x₄ : ℕ) * 4 = 12 := by
  decide

theorem exists_submultiset_sum_four {s : Multiset ℕ}
    (hpos : ∀ x ∈ s, 0 < x) (hbound : ∀ x ∈ s, x ≤ 4)
    (hsum : s.sum = 24) : ∃ t ≤ s, t.sum = 12 := by
  have hIcc : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have hcounts := sum_eq_sum_count_Icc hpos hbound
  rw [hIcc] at hcounts
  simp at hcounts
  rw [hsum] at hcounts
  obtain ⟨x₁, x₂, x₃, x₄, hx₁, hx₂, hx₃, hx₄, hxsum⟩ :
      ∃ x₁ x₂ x₃ x₄,
        x₁ ≤ s.count 1 ∧ x₂ ≤ s.count 2 ∧ x₃ ≤ s.count 3 ∧ x₄ ≤ s.count 4 ∧
          x₁ * 1 + x₂ * 2 + x₃ * 3 + x₄ * 4 = 12 := by
    have hc₁ : s.count 1 ≤ 24 := by omega
    have hc₂ : s.count 2 ≤ 12 := by omega
    have hc₃ : s.count 3 ≤ 8 := by omega
    have hc₄ : s.count 4 ≤ 6 := by omega
    let c₁ : Fin 25 := ⟨s.count 1, by omega⟩
    let c₂ : Fin 13 := ⟨s.count 2, by omega⟩
    let c₃ : Fin 9 := ⟨s.count 3, by omega⟩
    let c₄ : Fin 7 := ⟨s.count 4, by omega⟩
    obtain ⟨x₁, x₂, x₃, x₄, hx₁, hx₂, hx₃, hx₄, hxsum⟩ :=
      finite_counts_four c₁ c₂ c₃ c₄ (by
        dsimp [c₁, c₂, c₃, c₄]
        omega)
    exact ⟨x₁, x₂, x₃, x₄, hx₁, hx₂, hx₃, hx₄, hxsum⟩
  have hrepr := eq_sum_replicate_count_Icc hpos hbound
  rw [hIcc] at hrepr
  simp at hrepr
  let t := Multiset.replicate x₁ 1 +
    (Multiset.replicate x₂ 2 +
      (Multiset.replicate x₃ 3 + Multiset.replicate x₄ 4))
  refine ⟨t, ?_, ?_⟩
  · rw [← hrepr]
    exact add_le_add (Multiset.replicate_mono 1 hx₁)
      (add_le_add (Multiset.replicate_mono 2 hx₂)
        (add_le_add (Multiset.replicate_mono 3 hx₃)
          (Multiset.replicate_mono 4 hx₄)))
  · simp only [t, Multiset.sum_add, Multiset.sum_replicate, Nat.nsmul_eq_mul]
    simpa [add_assoc] using hxsum

theorem exists_submultiset_sum_lcm_of_bounded (k : ℕ) (hk : 0 < k)
    {s : Multiset ℕ} (hpos : ∀ x ∈ s, 0 < x) (hbound : ∀ x ∈ s, x ≤ k)
    (hsum : s.sum = 2 * (Finset.Icc 1 k).lcm id) :
    ∃ t ≤ s, t.sum = (Finset.Icc 1 k).lcm id := by
  have hfrequent :
      (k - 1) * (∑ i ∈ Finset.Icc 1 k, i) <
          2 * (Finset.Icc 1 k).lcm id →
        ∃ t ≤ s, t.sum = (Finset.Icc 1 k).lcm id := by
    intro hcapacity
    have hlarge : (k - 1) * (∑ i ∈ Finset.Icc 1 k, i) < s.sum := by
      rw [hsum]
      exact hcapacity
    obtain ⟨a, hcount⟩ := exists_frequent_of_sum_gt_capacity hk hpos hbound hlarge
    have hamem : a ∈ s := Multiset.count_pos.mp (lt_of_lt_of_le hk hcount)
    have hadiv : a ∣ (Finset.Icc 1 k).lcm id :=
      Submission.Helpers.dvd_lcm_Icc (hpos a hamem) (hbound a hamem)
    exact exists_submultiset_sum_of_frequent hk hpos hbound hsum hcount hadiv
  by_cases hk5 : 5 ≤ k
  · exact hfrequent (capacity_lt_two_lcm_of_five_le k hk5)
  · have hklt : k < 5 := Nat.lt_of_not_ge hk5
    interval_cases k
    · exact hfrequent (by decide)
    · exact hfrequent (by decide)
    · apply exists_submultiset_sum_three hpos hbound
      have hL : (Finset.Icc 1 3).lcm id = 6 := by decide
      simpa [hL] using hsum
    · apply exists_submultiset_sum_four hpos hbound
      have hL : (Finset.Icc 1 4).lcm id = 12 := by decide
      simpa [hL] using hsum

end Submission.Upper
