import Submission.DeBrangesWeights

namespace Submission
open Finset

lemma deBranges_choose_telescoping_interior (k m r : ℕ) (hk : 0 < k)
    (hrm : r + 2 ≤ m) :
    ((m * (2 * k + m) : ℕ) : ℝ) *
        (((Nat.choose (2 * k + 2 * r) r : ℕ) : ℝ) *
            ((Nat.choose (2 * k + m + r + 1) (m - r) : ℕ) : ℝ) -
          ((Nat.choose (2 * k + 2 * r) r : ℕ) : ℝ) *
            ((Nat.choose (2 * k + m + r - 1) (m - 2 - r) : ℕ) : ℝ)) =
      ((2 * (k + m) : ℕ) : ℝ) *
        ((((r + 1 : ℕ) : ℝ) *
            ((Nat.choose (2 * k + 2 * (r + 1) - 1) (r + 1) : ℕ) : ℝ) *
            ((Nat.choose (2 * k + m + (r + 1) - 1) (m - (r + 1)) : ℕ) : ℝ)) +
          (((r : ℕ) : ℝ) *
            ((Nat.choose (2 * k + 2 * r - 1) r : ℕ) : ℝ) *
            ((Nat.choose (2 * k + m + r - 1) (m - r) : ℕ) : ℝ))) := by
  have h1 : r ≤ 2 * k + 2 * r := by omega
  have h2 : m - r ≤ 2 * k + m + r + 1 := by omega
  have h3 : m - 2 - r ≤ 2 * k + m + r - 1 := by omega
  have h4 : r + 1 ≤ 2 * k + 2 * (r + 1) - 1 := by omega
  have h5 : m - (r + 1) ≤ 2 * k + m + (r + 1) - 1 := by omega
  have h6 : r ≤ 2 * k + 2 * r - 1 := by omega
  have h7 : m - r ≤ 2 * k + m + r - 1 := by omega
  rw [Nat.cast_choose ℝ h1, Nat.cast_choose ℝ h2, Nat.cast_choose ℝ h3,
    Nat.cast_choose ℝ h4, Nat.cast_choose ℝ h5, Nat.cast_choose ℝ h6,
    Nat.cast_choose ℝ h7]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  simp only [show 2 * k + 2 * r - r = 2 * k + r by omega,
    show 2 * k + m + r + 1 - (m - r) = 2 * k + 2 * r + 1 by omega,
    show 2 * k + m + r - 1 - (m - 2 - r) = 2 * k + 2 * r + 1 by omega,
    show 2 * k + 2 * (r + 1) - 1 - (r + 1) = 2 * k + r by omega,
    show 2 * k + m + (r + 1) - 1 - (m - (r + 1)) = 2 * k + 2 * r + 1 by omega,
    show 2 * k + 2 * r - 1 - r = 2 * k + r - 1 by omega,
    show 2 * k + m + r - 1 - (m - r) = 2 * k + 2 * r - 1 by omega]
  have fA : Nat.factorial (2 * k + 2 * r) =
      (2 * k + 2 * r) * Nat.factorial (2 * k + 2 * r - 1) := by
    calc
      Nat.factorial (2 * k + 2 * r) =
          Nat.factorial ((2 * k + 2 * r - 1) + 1) := by
        congr 1
        omega
      _ = ((2 * k + 2 * r - 1) + 1) *
          Nat.factorial (2 * k + 2 * r - 1) := Nat.factorial_succ _
      _ = _ := by
        congr 1
        omega
  have fA1 : Nat.factorial (2 * k + 2 * r + 1) =
      (2 * k + 2 * r + 1) * (2 * k + 2 * r) *
        Nat.factorial (2 * k + 2 * r - 1) := by
    rw [Nat.factorial_succ, fA]
    ring
  have fP1 : Nat.factorial (2 * k + m + r) =
      (2 * k + m + r) * Nat.factorial (2 * k + m + r - 1) := by
    calc
      Nat.factorial (2 * k + m + r) =
          Nat.factorial ((2 * k + m + r - 1) + 1) := by
        congr 1
        omega
      _ = ((2 * k + m + r - 1) + 1) *
          Nat.factorial (2 * k + m + r - 1) := Nat.factorial_succ _
      _ = _ := by
        congr 1
        omega
  have fP2 : Nat.factorial (2 * k + m + r + 1) =
      (2 * k + m + r + 1) * (2 * k + m + r) *
        Nat.factorial (2 * k + m + r - 1) := by
    rw [Nat.factorial_succ, fP1]
    ring
  have fkr : Nat.factorial (2 * k + r) =
      (2 * k + r) * Nat.factorial (2 * k + r - 1) := by
    calc
      Nat.factorial (2 * k + r) = Nat.factorial ((2 * k + r - 1) + 1) := by
        congr 1
        omega
      _ = ((2 * k + r - 1) + 1) * Nat.factorial (2 * k + r - 1) :=
        Nat.factorial_succ _
      _ = _ := by
        congr 1
        omega
  have fr1 : Nat.factorial (r + 1) = (r + 1) * Nat.factorial r :=
    Nat.factorial_succ r
  have fq : Nat.factorial (m - r) =
      (m - r) * Nat.factorial (m - (r + 1)) := by
    calc
      Nat.factorial (m - r) = Nat.factorial ((m - (r + 1)) + 1) := by
        congr 1
        omega
      _ = ((m - (r + 1)) + 1) * Nat.factorial (m - (r + 1)) :=
        Nat.factorial_succ _
      _ = _ := by
        congr 1
        omega
  have fq1 : Nat.factorial (m - (r + 1)) =
      (m - (r + 1)) * Nat.factorial (m - 2 - r) := by
    calc
      Nat.factorial (m - (r + 1)) = Nat.factorial ((m - 2 - r) + 1) := by
        congr 1
        omega
      _ = ((m - 2 - r) + 1) * Nat.factorial (m - 2 - r) :=
        Nat.factorial_succ _
      _ = _ := by
        congr 1
        omega
  rw [show 2 * k + 2 * (r + 1) - 1 = 2 * k + 2 * r + 1 by omega,
    show 2 * k + m + (r + 1) - 1 = 2 * k + m + r by omega,
    ]
  field_simp [Nat.factorial_ne_zero]
  rw [fA, fA1, fP1, fP2, fkr, fr1, fq, fq1]
  push_cast
  rw [Nat.cast_sub (R := ℝ) (by omega : r ≤ m),
    Nat.cast_sub (R := ℝ) (by omega : r + 1 ≤ m)]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

lemma deBranges_choose_telescoping_last (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    ((m * (2 * k + m) : ℕ) : ℝ) *
        ((Nat.choose (2 * k + 2 * m) m : ℕ) : ℝ) =
      ((2 * (k + m) : ℕ) : ℝ) *
        (((m : ℕ) : ℝ) *
          ((Nat.choose (2 * k + 2 * m - 1) m : ℕ) : ℝ)) := by
  have hchoose := Nat.choose_mul_succ_eq (2 * k + 2 * m - 1) m
  have hchoose' :
      Nat.choose (2 * k + 2 * m - 1) m * (2 * k + 2 * m) =
        Nat.choose (2 * k + 2 * m) m * (2 * k + m) := by
    simpa only [show 2 * k + 2 * m - 1 + 1 = 2 * k + 2 * m by omega,
      show 2 * k + 2 * m - m = 2 * k + m by omega] using hchoose
  have hchooseQ := congrArg (fun n : ℕ => (n : ℝ)) hchoose'
  push_cast at hchooseQ
  calc
    ((m * (2 * k + m) : ℕ) : ℝ) *
        ((Nat.choose (2 * k + 2 * m) m : ℕ) : ℝ) =
      (m : ℝ) *
        (((Nat.choose (2 * k + 2 * m) m : ℕ) : ℝ) * (2 * k + m)) := by
          push_cast
          ring
    _ = (m : ℝ) *
        (((Nat.choose (2 * k + 2 * m - 1) m : ℕ) : ℝ) *
          (2 * k + 2 * m)) := by rw [← hchooseQ]
    _ = _ := by
      push_cast
      ring

lemma deBranges_choose_telescoping_penultimate (k m : ℕ) (hk : 0 < k) (hm : 1 < m) :
    ((m * (2 * k + m) : ℕ) : ℝ) *
        (((Nat.choose (2 * k + 2 * (m - 1)) (m - 1) : ℕ) : ℝ) *
          ((Nat.choose (2 * k + m + (m - 1) + 1) (m - (m - 1)) : ℕ) : ℝ)) =
      ((2 * (k + m) : ℕ) : ℝ) *
        ((((m : ℕ) : ℝ) *
            ((Nat.choose (2 * k + 2 * m - 1) m : ℕ) : ℝ)) +
          (((m - 1 : ℕ) : ℝ) *
            ((Nat.choose (2 * k + 2 * (m - 1) - 1) (m - 1) : ℕ) : ℝ) *
            ((Nat.choose (2 * k + m + (m - 1) - 1) (m - (m - 1)) : ℕ) : ℝ))) := by
  have hchooseA := Nat.add_one_mul_choose_eq (2 * k + 2 * m - 2) (m - 1)
  have hchooseA' :
      (2 * k + 2 * m - 1) * Nat.choose (2 * k + 2 * m - 2) (m - 1) =
        Nat.choose (2 * k + 2 * m - 1) m * m := by
    simpa only [show 2 * k + 2 * m - 2 + 1 = 2 * k + 2 * m - 1 by omega,
      show m - 1 + 1 = m by omega] using hchooseA
  have hchooseB := Nat.choose_mul_succ_eq (2 * k + 2 * m - 3) (m - 1)
  have hchooseB' :
      Nat.choose (2 * k + 2 * m - 3) (m - 1) * (2 * k + 2 * m - 2) =
        Nat.choose (2 * k + 2 * m - 2) (m - 1) * (2 * k + m - 1) := by
    simpa only [show 2 * k + 2 * m - 3 + 1 = 2 * k + 2 * m - 2 by omega,
      show 2 * k + 2 * m - 2 - (m - 1) = 2 * k + m - 1 by omega] using hchooseB
  have hchooseAQ := congrArg (fun n : ℕ => (n : ℝ)) hchooseA'
  have hchooseBQ := congrArg (fun n : ℕ => (n : ℝ)) hchooseB'
  push_cast at hchooseAQ hchooseBQ
  rw [Nat.cast_sub (R := ℝ) (by omega : 1 ≤ 2 * k + 2 * m)] at hchooseAQ
  rw [Nat.cast_sub (R := ℝ) (by omega : 2 ≤ 2 * k + 2 * m),
    Nat.cast_sub (R := ℝ) (by omega : 1 ≤ 2 * k + m)] at hchooseBQ
  push_cast at hchooseAQ hchooseBQ
  simp only [show m - (m - 1) = 1 by omega, Nat.choose_one_right,
    show 2 * k + 2 * (m - 1) = 2 * k + 2 * m - 2 by omega,
    show 2 * k + m + (m - 1) + 1 = 2 * k + 2 * m by omega,
    show 2 * k + m + (m - 1) - 1 = 2 * k + 2 * m - 2 by omega]
  rw [show 2 * k + 2 * m - 2 - 1 = 2 * k + 2 * m - 3 by omega]
  push_cast
  rw [show (m : ℝ) * ((Nat.choose (2 * k + 2 * m - 1) m : ℕ) : ℝ) =
      (2 * (k : ℝ) + 2 * (m : ℝ) - 1) *
        ((Nat.choose (2 * k + 2 * m - 2) (m - 1) : ℕ) : ℝ) by
      linarith only [hchooseAQ]]
  rw [Nat.cast_sub (R := ℝ) (by omega : 1 ≤ m),
    Nat.cast_sub (R := ℝ) (by omega : 2 ≤ 2 * k + 2 * m)]
  push_cast
  rw [mul_assoc ((m : ℝ) - 1), hchooseBQ]
  ring

noncomputable def deBrangesInitialTerm (k m r : ℕ) : ℝ :=
  if r ≤ m then
    (-1 : ℝ) ^ r * Nat.choose (2 * k + 2 * r) r *
      Nat.choose (2 * k + m + r + 1) (m - r)
  else 0

noncomputable def deBrangesInitialTelescoper (k m r : ℕ) : ℝ :=
  if 0 < r ∧ r ≤ m then
    -2 * (-1 : ℝ) ^ r * r * (k + m) *
      Nat.choose (2 * k + 2 * r - 1) r *
      Nat.choose (2 * k + m + r - 1) (m - r)
  else 0

lemma deBrangesInitialTerm_telescope (k m r : ℕ) (hk : 0 < k) (hm : 2 ≤ m)
    (hr : r ≤ m) :
    ((m * (2 * k + m) : ℕ) : ℝ) *
        (deBrangesInitialTerm k m r - deBrangesInitialTerm k (m - 2) r) =
      deBrangesInitialTelescoper k m (r + 1) - deBrangesInitialTelescoper k m r := by
  by_cases hrm' : r + 2 ≤ m
  ·
    have hrsmall : r ≤ m - 2 := by omega
    have hr1pos : 0 < r + 1 := by omega
    have hr1le : r + 1 ≤ m := by omega
    have hsign : (-1 : ℝ) ^ (r + 1) = -((-1 : ℝ) ^ r) := by
      rw [pow_succ]
      ring
    rw [deBrangesInitialTerm, if_pos hr, deBrangesInitialTerm, if_pos hrsmall,
      deBrangesInitialTelescoper, if_pos ⟨hr1pos, hr1le⟩]
    rw [show 2 * k + (m - 2) + r + 1 = 2 * k + m + r - 1 by omega]
    by_cases hr0 : 0 < r
    · rw [deBrangesInitialTelescoper, if_pos ⟨hr0, hr⟩, hsign]
      have h := deBranges_choose_telescoping_interior k m r hk hrm'
      push_cast at h ⊢
      linear_combination ((-1 : ℝ) ^ r) * h
    · have hrzero : r = 0 := by omega
      subst r
      simp only [deBrangesInitialTelescoper, lt_self_iff_false, false_and, if_false, pow_zero,
        Nat.cast_zero, mul_zero, sub_zero, Nat.zero_add, Nat.choose_zero_right]
      have h := deBranges_choose_telescoping_interior k m 0 hk hrm'
      push_cast at h ⊢
      norm_num at h ⊢
      simpa only [mul_assoc] using h
  · have hnear : m < r + 2 := lt_of_not_ge hrm'
    by_cases hre : r = m
    · subst r
      have hlast := deBranges_choose_telescoping_last k m hk (by omega)
      have hmnot : ¬m ≤ m - 2 := by omega
      rw [deBrangesInitialTerm, if_pos le_rfl, deBrangesInitialTerm, if_neg hmnot,
        deBrangesInitialTelescoper, if_neg (by omega), deBrangesInitialTelescoper, if_pos ⟨by omega, le_rfl⟩]
      simp only [Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, mul_one,
        zero_sub]
      push_cast at hlast ⊢
      linear_combination ((-1 : ℝ) ^ m) * hlast
    · have hrlt : r < m := lt_of_le_of_ne hr hre
      have hre' : r = m - 1 := by omega
      subst r
      have hpen := deBranges_choose_telescoping_penultimate k m hk (by omega)
      have hm1le : m - 1 ≤ m := by omega
      have hm1not : ¬m - 1 ≤ m - 2 := by omega
      have hm1pos : 0 < m - 1 := by omega
      have hsign : (-1 : ℝ) ^ m = -((-1 : ℝ) ^ (m - 1)) := by
        calc
          (-1 : ℝ) ^ m = (-1 : ℝ) ^ ((m - 1) + 1) := by congr 1; omega
          _ = -((-1 : ℝ) ^ (m - 1)) := by rw [pow_succ]; ring
      rw [deBrangesInitialTerm, if_pos hm1le, deBrangesInitialTerm, if_neg hm1not,
        deBrangesInitialTelescoper, if_pos ⟨by omega, by omega⟩,
        deBrangesInitialTelescoper, if_pos ⟨hm1pos, hm1le⟩]
      rw [show m - 1 + 1 = m by omega, hsign]
      simp only [Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, mul_one]
      push_cast at hpen ⊢
      linear_combination ((-1 : ℝ) ^ (m - 1)) * hpen

lemma sum_deBrangesInitialTerm_step (k m : ℕ) (hk : 0 < k) (hm : 2 ≤ m) :
    ∑ r ∈ range (m + 1), deBrangesInitialTerm k m r =
      ∑ r ∈ range (m - 2 + 1), deBrangesInitialTerm k (m - 2) r := by
  have hsubset : range (m - 2 + 1) ⊆ range (m + 1) := by
    exact range_mono (by omega)
  have hsupport :
      (∑ r ∈ range (m + 1), deBrangesInitialTerm k (m - 2) r) =
        ∑ r ∈ range (m - 2 + 1), deBrangesInitialTerm k (m - 2) r := by
    symm
    apply sum_subset hsubset
    intro r hrbig hrsmall
    have hrnot : ¬r ≤ m - 2 := by
      have hrnotmem : r ∉ range (m - 2 + 1) := by
        simpa only [mem_range] using hrsmall
      simpa only [mem_range, Nat.lt_add_one_iff] using hrnotmem
    simp [deBrangesInitialTerm, hrnot]
  have htelescope (a : ℕ → ℝ) (n : ℕ) :
      (∑ r ∈ range n, (a (r + 1) - a r)) = a n - a 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
        simp only [sum_range_succ]
        rw [ih]
        ring
  have hsum :
      (∑ r ∈ range (m + 1),
          ((m * (2 * k + m) : ℕ) : ℝ) *
            (deBrangesInitialTerm k m r - deBrangesInitialTerm k (m - 2) r)) =
        ∑ r ∈ range (m + 1),
          (deBrangesInitialTelescoper k m (r + 1) - deBrangesInitialTelescoper k m r) := by
    apply sum_congr rfl
    intro r hr
    exact deBrangesInitialTerm_telescope k m r hk hm
      (Nat.le_of_lt_succ (mem_range.mp hr))
  rw [← Finset.mul_sum, Finset.sum_sub_distrib,
    htelescope (deBrangesInitialTelescoper k m) (m + 1)] at hsum
  have htel0 : deBrangesInitialTelescoper k m 0 = 0 := by simp [deBrangesInitialTelescoper]
  have htelLast : deBrangesInitialTelescoper k m (m + 1) = 0 := by simp [deBrangesInitialTelescoper]
  rw [htel0, htelLast, sub_zero] at hsum
  have hfactor : (((m * (2 * k + m) : ℕ) : ℝ)) ≠ 0 := by positivity
  have heq :
      (∑ r ∈ range (m + 1), deBrangesInitialTerm k m r) =
        ∑ r ∈ range (m + 1), deBrangesInitialTerm k (m - 2) r := by
    apply sub_eq_zero.mp
    exact (mul_eq_zero.mp hsum).resolve_left hfactor
  rw [heq, hsupport]

lemma sum_deBrangesInitialTerm_even (k s : ℕ) (hk : 0 < k) :
    ∑ r ∈ range (2 * s + 1), deBrangesInitialTerm k (2 * s) r = 1 := by
  induction s with
  | zero => simp [deBrangesInitialTerm]
  | succ s ih =>
      have hstep := sum_deBrangesInitialTerm_step k (2 * s + 2) hk (by omega)
      rw [show 2 * (s + 1) = 2 * s + 2 by omega]
      calc
        (∑ r ∈ range (2 * s + 2 + 1), deBrangesInitialTerm k (2 * s + 2) r) =
            ∑ r ∈ range (2 * s + 2 - 2 + 1),
              deBrangesInitialTerm k (2 * s + 2 - 2) r := hstep
        _ = ∑ r ∈ range (2 * s + 1), deBrangesInitialTerm k (2 * s) r := by
          congr 3
        _ = 1 := ih

lemma sum_deBrangesInitialTerm_odd (k s : ℕ) (hk : 0 < k) :
    ∑ r ∈ range (2 * s + 1 + 1), deBrangesInitialTerm k (2 * s + 1) r = 0 := by
  induction s with
  | zero =>
      simp [deBrangesInitialTerm, Finset.sum_range_succ]
      ring
  | succ s ih =>
      have hstep := sum_deBrangesInitialTerm_step k (2 * s + 3) hk (by omega)
      rw [show 2 * (s + 1) + 1 = 2 * s + 3 by omega]
      calc
        (∑ r ∈ range (2 * s + 3 + 1), deBrangesInitialTerm k (2 * s + 3) r) =
            ∑ r ∈ range (2 * s + 3 - 2 + 1),
              deBrangesInitialTerm k (2 * s + 3 - 2) r := hstep
        _ = ∑ r ∈ range (2 * s + 1 + 1), deBrangesInitialTerm k (2 * s + 1) r := by
          congr 3
        _ = 0 := ih

lemma explicitDeBrangesQ_zero_eq_initial_sum {N k : ℕ} (hk : 0 < k) (hkN : k ≤ N) :
    explicitDeBrangesQ N k 0 =
      ∑ r ∈ range (N - k + 1), deBrangesInitialTerm k (N - k) r := by
  rw [explicitDeBrangesQ]
  simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
  rw [show N + 1 = k + (N - k + 1) by omega, sum_range_add]
  have hprefix :
      (∑ j ∈ range k, deBrangesQCoefficient N k j) = 0 := by
    apply sum_eq_zero
    intro j hj
    have hjlt : j < k := mem_range.mp hj
    have hjk : ¬k ≤ j := by omega
    simp [deBrangesQCoefficient, hjk]
  rw [hprefix, zero_add]
  apply sum_congr rfl
  intro r hr
  have hrle : r ≤ N - k := Nat.le_of_lt_succ (mem_range.mp hr)
  have hkrN : k + r ≤ N := by omega
  rw [deBrangesQCoefficient, if_pos ⟨hk, Nat.le_add_right k r, hkrN⟩]
  rw [deBrangesInitialTerm, if_pos hrle]
  simp only [show k + r - k = r by omega,
    show 2 * (k + r) = 2 * k + 2 * r by omega,
    show N + (k + r) + 1 = 2 * k + (N - k) + r + 1 by omega,
    show N - (k + r) = N - k - r by omega]

lemma explicitDeBrangesQ_zero_even {k s : ℕ} (hk : 0 < k) :
    explicitDeBrangesQ (k + 2 * s) k 0 = 1 := by
  rw [explicitDeBrangesQ_zero_eq_initial_sum hk (by omega)]
  have hsub : k + 2 * s - k = 2 * s := by omega
  rw [hsub]
  exact sum_deBrangesInitialTerm_even k s hk

lemma explicitDeBrangesQ_zero_odd {k s : ℕ} (hk : 0 < k) :
    explicitDeBrangesQ (k + (2 * s + 1)) k 0 = 0 := by
  rw [explicitDeBrangesQ_zero_eq_initial_sum hk (by omega)]
  have hsub : k + (2 * s + 1) - k = 2 * s + 1 := by omega
  rw [hsub]
  exact sum_deBrangesInitialTerm_odd k s hk

@[simp]
lemma explicitDeBrangesQ_terminal (N : ℕ) (t : ℝ) :
    explicitDeBrangesQ N (N + 1) t = 0 := by
  rw [explicitDeBrangesQ_eq_neg_tauDot_div (by omega)]
  simp

lemma explicitDeBrangesQ_zero_add_next {N k : ℕ} (hk : 0 < k) (hkN : k ≤ N) :
    explicitDeBrangesQ N k 0 + explicitDeBrangesQ N (k + 1) 0 = 1 := by
  rcases Nat.even_or_odd (N - k) with ⟨s, hs⟩ | ⟨s, hs⟩
  · have hN : N = k + 2 * s := by omega
    subst N
    rw [explicitDeBrangesQ_zero_even hk]
    by_cases hs0 : s = 0
    · subst s
      simp
    · obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs0
      rw [show k + 2 * (r + 1) = (k + 1) + (2 * r + 1) by omega]
      rw [explicitDeBrangesQ_zero_odd (by omega)]
      norm_num
  · have hN : N = k + (2 * s + 1) := by omega
    subst N
    rw [explicitDeBrangesQ_zero_odd hk]
    rw [show k + (2 * s + 1) = (k + 1) + 2 * s by omega]
    rw [explicitDeBrangesQ_zero_even (by omega)]
    norm_num

lemma explicitDeBrangesTau_zero_sub_next {N k : ℕ} (hk : 0 < k) (hkN : k ≤ N) :
    explicitDeBrangesTau N k 0 - explicitDeBrangesTau N (k + 1) 0 = 1 := by
  calc
    explicitDeBrangesTau N k 0 - explicitDeBrangesTau N (k + 1) 0 =
        -explicitDeBrangesTauDot N k 0 / (k : ℝ) -
          explicitDeBrangesTauDot N (k + 1) 0 / ((k + 1 : ℕ) : ℝ) :=
      explicitDeBranges_system_eq hk hkN 0
    _ = explicitDeBrangesQ N k 0 + explicitDeBrangesQ N (k + 1) 0 := by
      rw [explicitDeBrangesQ_eq_neg_tauDot_div hk,
        explicitDeBrangesQ_eq_neg_tauDot_div (by omega)]
      ring
    _ = 1 := explicitDeBrangesQ_zero_add_next hk hkN

lemma explicitDeBrangesTau_zero_add (k m : ℕ) (hk : 0 < k) :
    explicitDeBrangesTau (k + m) k 0 = ((m + 1 : ℕ) : ℝ) := by
  induction m generalizing k with
  | zero =>
      have hdiff := explicitDeBrangesTau_zero_sub_next (N := k) (k := k) hk le_rfl
      simpa using hdiff
  | succ m ih =>
      have hdiff := explicitDeBrangesTau_zero_sub_next
        (N := k + (m + 1)) (k := k) hk (by omega)
      have hnext := ih (k + 1) (by omega)
      have hindex : k + (m + 1) = (k + 1) + m := by omega
      calc
        explicitDeBrangesTau (k + (m + 1)) k 0 =
            explicitDeBrangesTau (k + (m + 1)) (k + 1) 0 + 1 := by linarith
        _ = explicitDeBrangesTau ((k + 1) + m) (k + 1) 0 + 1 := by rw [hindex]
        _ = ((m + 1 : ℕ) : ℝ) + 1 := by rw [hnext]
        _ = (((m + 1) + 1 : ℕ) : ℝ) := by push_cast; ring

lemma explicitDeBrangesTau_zero {N k : ℕ} (hk : 0 < k) (hkN : k ≤ N) :
    explicitDeBrangesTau N k 0 = ((N - k + 1 : ℕ) : ℝ) := by
  have hN : N = k + (N - k) := by omega
  conv_lhs => rw [hN]
  exact explicitDeBrangesTau_zero_add k (N - k) hk

end Submission
