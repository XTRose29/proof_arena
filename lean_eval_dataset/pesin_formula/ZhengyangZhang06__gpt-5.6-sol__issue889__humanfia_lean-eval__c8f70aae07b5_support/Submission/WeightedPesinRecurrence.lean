import Mathlib
import Mathlib.Analysis.SumIntegralExpDecay

namespace Submission.Helpers

lemma sum_range_exp_neg_succ_le {c : ℝ} (hc : 0 < c) (n : ℕ) :
    (∑ j ∈ Finset.range n, Real.exp (-c * (j + 1))) ≤ Real.exp c / c := by
  calc
    (∑ j ∈ Finset.range n, Real.exp (-c * (j + 1))) ≤
        ∑ j ∈ Finset.range n, Real.exp (-c * j) := by
      apply Finset.sum_le_sum
      intro j _hj
      apply Real.exp_le_exp.mpr
      have hj : (j : ℝ) ≤ (j + 1 : ℕ) := by
        exact_mod_cast Nat.le_succ j
      nlinarith
    _ ≤ Real.exp c / c := by
      simpa [Nat.Ico_zero_eq_range] using
        (sum_Ico_pow_mul_exp_neg_le (k := 0) (M := n) hc)

lemma sum_fin_lt_exp_neg_sub_le
    {N : ℕ} {c : ℝ} (hc : 0 < c) (i : Fin N) :
    (∑ j : Fin N, if j.val < i.val then
      Real.exp (-c * ((i.val - j.val : ℕ) : ℝ)) else 0) ≤
        Real.exp c / c := by
  let f : ℕ → ℝ := fun j => if j < i.val then
    Real.exp (-c * ((i.val - j : ℕ) : ℝ)) else 0
  change (∑ j : Fin N, f j.val) ≤ Real.exp c / c
  rw [Fin.sum_univ_eq_sum_range]
  have hsubset : Finset.range i.val ⊆ Finset.range N := by
    intro j hj
    exact Finset.mem_range.mpr ((Finset.mem_range.mp hj).trans i.isLt)
  have heq : (∑ j ∈ Finset.range N, f j) =
      ∑ j ∈ Finset.range i.val, f j := by
    symm
    apply Finset.sum_subset hsubset
    intro j hjN hjnot
    have hij : i.val ≤ j := Nat.le_of_not_gt fun hji =>
      hjnot (Finset.mem_range.mpr hji)
    simp [f, Nat.not_lt.mpr hij]
  rw [heq]
  have heq' : (∑ j ∈ Finset.range i.val, f j) =
      ∑ j ∈ Finset.range i.val,
        Real.exp (-c * ((i.val - j : ℕ) : ℝ)) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [f, Finset.mem_range.mp hj]
  rw [heq']
  have hreflect :
      (∑ j ∈ Finset.range i.val,
        Real.exp (-c * ((i.val - j : ℕ) : ℝ))) =
        ∑ j ∈ Finset.range i.val, Real.exp (-c * (j + 1)) := by
    calc
      (∑ j ∈ Finset.range i.val,
          Real.exp (-c * ((i.val - j : ℕ) : ℝ))) =
          ∑ j ∈ Finset.range i.val,
            Real.exp (-c * (((i.val - 1 - j : ℕ) : ℝ) + 1)) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjlt : j < i.val := Finset.mem_range.mp hj
        congr 2
        exact_mod_cast (show i.val - j = i.val - 1 - j + 1 by omega)
      _ = ∑ j ∈ Finset.range i.val, Real.exp (-c * (j + 1)) :=
        Finset.sum_range_reflect (fun j => Real.exp (-c * (j + 1))) i.val
  rw [hreflect]
  exact sum_range_exp_neg_succ_le hc i.val

lemma sum_fin_gt_exp_neg_sub_le
    {N : ℕ} {c : ℝ} (hc : 0 < c) (i : Fin N) :
    (∑ j : Fin N, if i.val < j.val then
      Real.exp (-c * ((j.val - i.val : ℕ) : ℝ)) else 0) ≤
        Real.exp c / c := by
  let f : ℕ → ℝ := fun j => if i.val < j then
    Real.exp (-c * ((j - i.val : ℕ) : ℝ)) else 0
  change (∑ j : Fin N, f j.val) ≤ Real.exp c / c
  rw [Fin.sum_univ_eq_sum_range]
  let s := Finset.Ico (i.val + 1) N
  have hsubset : s ⊆ Finset.range N := by
    intro j hj
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2
  have heq : (∑ j ∈ Finset.range N, f j) = ∑ j ∈ s, f j := by
    symm
    apply Finset.sum_subset hsubset
    intro j hjN hjnot
    have hji : j ≤ i.val := by
      by_contra h
      apply hjnot
      exact Finset.mem_Ico.mpr ⟨Nat.succ_le_iff.mpr (lt_of_not_ge h),
        Finset.mem_range.mp hjN⟩
    simp [f, Nat.not_lt.mpr hji]
  rw [heq]
  have heq' : (∑ j ∈ s, f j) =
      ∑ j ∈ s, Real.exp (-c * ((j - i.val : ℕ) : ℝ)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hij : i.val < j := Nat.lt_of_succ_le (Finset.mem_Ico.mp hj).1
    simp [f, hij]
  rw [heq']
  rw [Finset.sum_Ico_eq_sum_range]
  calc
    (∑ j ∈ Finset.range (N - (i.val + 1)),
        Real.exp (-c * (((i.val + 1 + j) - i.val : ℕ) : ℝ))) =
        ∑ j ∈ Finset.range (N - (i.val + 1)),
          Real.exp (-c * (j + 1)) := by
      apply Finset.sum_congr rfl
      intro j _hj
      congr 2
      exact_mod_cast (show i.val + 1 + j - i.val = j + 1 by omega)
    _ ≤ Real.exp c / c :=
      sum_range_exp_neg_succ_le hc (N - (i.val + 1))

lemma finite_weighted_maximum_le_two
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (d w : ι → ℝ) (kernel : ι → ι → ℝ)
    {A c : ℝ}
    (hd : ∀ i, 0 ≤ d i) (hw : ∀ i, 0 < w i)
    (hc : 0 ≤ c) (hc_half : c ≤ 1 / 2)
    (hkernel_nonneg : ∀ i j, 0 ≤ kernel i j)
    (hkernel_le : ∀ i, ∑ j, kernel i j * w j ≤ w i)
    (hstep : ∀ i,
      d i ≤ A * w i + c * ∑ j, kernel i j * d j) :
    ∀ i, d i ≤ 2 * A * w i := by
  classical
  let ratios : Finset ℝ := Finset.univ.image fun i => d i / w i
  have hratios_nonempty : ratios.Nonempty := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨d i / w i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  let M : ℝ := ratios.max' hratios_nonempty
  have hratio_le (i : ι) : d i / w i ≤ M := by
    apply Finset.le_max'
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hd_le (i : ι) : d i ≤ M * w i := by
    exact (div_le_iff₀ (hw i)).mp (hratio_le i)
  have hM_nonneg : 0 ≤ M := by
    obtain ⟨i, _hi, hMi⟩ := Finset.mem_image.mp
      (Finset.max'_mem ratios hratios_nonempty)
    change 0 ≤ ratios.max' hratios_nonempty
    rw [← hMi]
    exact div_nonneg (hd i) (hw i).le
  obtain ⟨i, _hi, hMi⟩ := Finset.mem_image.mp
    (Finset.max'_mem ratios hratios_nonempty)
  have hsum_le :
      (∑ j, kernel i j * d j) ≤
        M * ∑ j, kernel i j * w j := by
    calc
      (∑ j, kernel i j * d j) ≤
          ∑ j, kernel i j * (M * w j) := by
        apply Finset.sum_le_sum
        intro j _hj
        exact mul_le_mul_of_nonneg_left (hd_le j) (hkernel_nonneg i j)
      _ = M * ∑ j, kernel i j * w j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        ring
  have hM_step : M ≤ A + c * M := by
    have hi := hstep i
    have hdi_eq : d i = M * w i := by
      have hMiM : d i / w i = M := by simpa [M] using hMi
      exact (div_eq_iff (hw i).ne').mp hMiM
    have hscaled : M * w i ≤ (A + c * M) * w i := by
      calc
        M * w i = d i := hdi_eq.symm
        _ ≤ A * w i + c * ∑ j, kernel i j * d j := hi
        _ ≤ A * w i + c * (M * w i) := by
          gcongr
          exact hsum_le.trans
            (mul_le_mul_of_nonneg_left (hkernel_le i) hM_nonneg)
        _ = (A + c * M) * w i := by ring
    exact le_of_mul_le_mul_right hscaled (hw i)
  have hM_le : M ≤ 2 * A := by
    nlinarith
  intro j
  calc
    d j ≤ M * w j := hd_le j
    _ ≤ (2 * A) * w j :=
      mul_le_mul_of_nonneg_right hM_le (hw j).le

lemma finite_weighted_maximum_le_two_of_kernel_bound
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (d w : ι → ℝ) (kernel : ι → ι → ℝ)
    {A c S : ℝ}
    (hd : ∀ i, 0 ≤ d i) (hw : ∀ i, 0 < w i)
    (hc : 0 ≤ c) (hsmall : c * S ≤ 1 / 2)
    (hkernel_nonneg : ∀ i j, 0 ≤ kernel i j)
    (hkernel_le : ∀ i, ∑ j, kernel i j * w j ≤ S * w i)
    (hstep : ∀ i,
      d i ≤ A * w i + c * ∑ j, kernel i j * d j) :
    ∀ i, d i ≤ 2 * A * w i := by
  classical
  let ratios : Finset ℝ := Finset.univ.image fun i => d i / w i
  have hratios_nonempty : ratios.Nonempty := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨d i / w i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  let M : ℝ := ratios.max' hratios_nonempty
  have hratio_le (i : ι) : d i / w i ≤ M := by
    apply Finset.le_max'
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hd_le (i : ι) : d i ≤ M * w i := by
    exact (div_le_iff₀ (hw i)).mp (hratio_le i)
  have hM_nonneg : 0 ≤ M := by
    obtain ⟨i, _hi, hMi⟩ := Finset.mem_image.mp
      (Finset.max'_mem ratios hratios_nonempty)
    change 0 ≤ ratios.max' hratios_nonempty
    rw [← hMi]
    exact div_nonneg (hd i) (hw i).le
  obtain ⟨i, _hi, hMi⟩ := Finset.mem_image.mp
    (Finset.max'_mem ratios hratios_nonempty)
  have hsum_le :
      (∑ j, kernel i j * d j) ≤ M * S * w i := by
    calc
      (∑ j, kernel i j * d j) ≤
          ∑ j, kernel i j * (M * w j) := by
        apply Finset.sum_le_sum
        intro j _hj
        exact mul_le_mul_of_nonneg_left (hd_le j) (hkernel_nonneg i j)
      _ = M * ∑ j, kernel i j * w j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      _ ≤ M * (S * w i) :=
        mul_le_mul_of_nonneg_left (hkernel_le i) hM_nonneg
      _ = M * S * w i := by ring
  have hM_step : M ≤ A + c * S * M := by
    have hi := hstep i
    have hdi_eq : d i = M * w i := by
      have hMiM : d i / w i = M := by simpa [M] using hMi
      exact (div_eq_iff (hw i).ne').mp hMiM
    have hscaled : M * w i ≤ (A + c * S * M) * w i := by
      calc
        M * w i = d i := hdi_eq.symm
        _ ≤ A * w i + c * ∑ j, kernel i j * d j := hi
        _ ≤ A * w i + c * (M * S * w i) := by
          gcongr
        _ = (A + c * S * M) * w i := by ring
    exact le_of_mul_le_mul_right hscaled (hw i)
  have hM_le : M ≤ 2 * A := by
    nlinarith
  intro j
  calc
    d j ≤ M * w j := hd_le j
    _ ≤ (2 * A) * w j :=
      mul_le_mul_of_nonneg_right hM_le (hw j).le

noncomputable def twoSidedExpKernel {Q : ℕ} (a b : ℝ)
    (i j : Fin (Q + 1)) : ℝ :=
  (if j.val < i.val then
      Real.exp (a * ((i.val - j.val : ℕ) : ℝ)) else 0) +
    if i.val < j.val then
      Real.exp (b * ((j.val - i.val : ℕ) : ℝ)) else 0

noncomputable def twoSidedExpWeight {Q : ℕ} (a b rho : ℝ)
    (i : Fin (Q + 1)) : ℝ :=
  Real.exp ((a + rho) * i.val) +
    Real.exp ((b + rho) * ((Q - i.val : ℕ) : ℝ))

lemma twoSidedExpKernel_nonneg {Q : ℕ} (a b : ℝ)
    (i j : Fin (Q + 1)) :
    0 ≤ twoSidedExpKernel a b i j := by
  dsimp [twoSidedExpKernel]
  positivity

lemma twoSidedExpWeight_pos {Q : ℕ} (a b rho : ℝ)
    (i : Fin (Q + 1)) :
    0 < twoSidedExpWeight a b rho i := by
  dsimp [twoSidedExpWeight]
  positivity

lemma leftExpKernel_mul_weight_eq {Q : ℕ} (a b rho : ℝ)
    (i j : Fin (Q + 1)) (hji : j.val < i.val) :
    Real.exp (a * ((i.val - j.val : ℕ) : ℝ)) *
        twoSidedExpWeight a b rho j =
      Real.exp ((a + rho) * i.val) *
          Real.exp (-rho * ((i.val - j.val : ℕ) : ℝ)) +
        Real.exp ((b + rho) * ((Q - i.val : ℕ) : ℝ)) *
          Real.exp ((a + b + rho) * ((i.val - j.val : ℕ) : ℝ)) := by
  have hji_le : j.val ≤ i.val := Nat.le_of_lt hji
  have hiQ : i.val ≤ Q := Nat.le_of_lt_succ i.isLt
  have hjQ : j.val ≤ Q := hji_le.trans hiQ
  rw [twoSidedExpWeight, mul_add]
  congr 1
  · rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [Nat.cast_sub hji_le]
    ring
  · rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [Nat.cast_sub hiQ, Nat.cast_sub hjQ, Nat.cast_sub hji_le]
    ring

lemma rightExpKernel_mul_weight_eq {Q : ℕ} (a b rho : ℝ)
    (i j : Fin (Q + 1)) (hij : i.val < j.val) :
    Real.exp (b * ((j.val - i.val : ℕ) : ℝ)) *
        twoSidedExpWeight a b rho j =
      Real.exp ((a + rho) * i.val) *
          Real.exp ((a + b + rho) * ((j.val - i.val : ℕ) : ℝ)) +
        Real.exp ((b + rho) * ((Q - i.val : ℕ) : ℝ)) *
          Real.exp (-rho * ((j.val - i.val : ℕ) : ℝ)) := by
  have hij_le : i.val ≤ j.val := Nat.le_of_lt hij
  have hjQ : j.val ≤ Q := Nat.le_of_lt_succ j.isLt
  have hiQ : i.val ≤ Q := hij_le.trans hjQ
  rw [twoSidedExpWeight, mul_add]
  congr 1
  · rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [Nat.cast_sub hij_le]
    ring
  · rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [Nat.cast_sub hjQ, Nat.cast_sub hiQ, Nat.cast_sub hij_le]
    ring

lemma twoSidedExpKernel_weight_sum_le
    {Q : ℕ} {a b rho : ℝ} (hrho : 0 < rho)
    (hgap : a + b + rho < 0) (i : Fin (Q + 1)) :
    (∑ j, twoSidedExpKernel a b i j * twoSidedExpWeight a b rho j) ≤
      (Real.exp rho / rho +
          Real.exp (-(a + b + rho)) / (-(a + b + rho))) *
        twoSidedExpWeight a b rho i := by
  let ws := Real.exp ((a + rho) * i.val)
  let wu := Real.exp ((b + rho) * ((Q - i.val : ℕ) : ℝ))
  let Er := Real.exp rho / rho
  let Eg := Real.exp (-(a + b + rho)) / (-(a + b + rho))
  have hgap_pos : 0 < -(a + b + rho) := neg_pos.mpr hgap
  have hleft_rho :
      (∑ j : Fin (Q + 1), if j.val < i.val then
        Real.exp (-rho * ((i.val - j.val : ℕ) : ℝ)) else 0) ≤ Er := by
    exact sum_fin_lt_exp_neg_sub_le hrho i
  have hleft_gap :
      (∑ j : Fin (Q + 1), if j.val < i.val then
        Real.exp ((a + b + rho) * ((i.val - j.val : ℕ) : ℝ)) else 0) ≤ Eg := by
    simpa only [neg_mul, neg_neg] using
      (sum_fin_lt_exp_neg_sub_le hgap_pos i)
  have hright_rho :
      (∑ j : Fin (Q + 1), if i.val < j.val then
        Real.exp (-rho * ((j.val - i.val : ℕ) : ℝ)) else 0) ≤ Er := by
    exact sum_fin_gt_exp_neg_sub_le hrho i
  have hright_gap :
      (∑ j : Fin (Q + 1), if i.val < j.val then
        Real.exp ((a + b + rho) * ((j.val - i.val : ℕ) : ℝ)) else 0) ≤ Eg := by
    simpa only [neg_mul, neg_neg] using
      (sum_fin_gt_exp_neg_sub_le hgap_pos i)
  have hleft_eq :
      (∑ j : Fin (Q + 1),
        (if j.val < i.val then
          Real.exp (a * ((i.val - j.val : ℕ) : ℝ)) else 0) *
            twoSidedExpWeight a b rho j) =
        ws * (∑ j : Fin (Q + 1), if j.val < i.val then
          Real.exp (-rho * ((i.val - j.val : ℕ) : ℝ)) else 0) +
        wu * (∑ j : Fin (Q + 1), if j.val < i.val then
          Real.exp ((a + b + rho) * ((i.val - j.val : ℕ) : ℝ)) else 0) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    by_cases hji : j.val < i.val
    · simp only [hji, if_true]
      simpa [ws, wu] using leftExpKernel_mul_weight_eq a b rho i j hji
    · simp [hji]
  have hright_eq :
      (∑ j : Fin (Q + 1),
        (if i.val < j.val then
          Real.exp (b * ((j.val - i.val : ℕ) : ℝ)) else 0) *
            twoSidedExpWeight a b rho j) =
        ws * (∑ j : Fin (Q + 1), if i.val < j.val then
          Real.exp ((a + b + rho) * ((j.val - i.val : ℕ) : ℝ)) else 0) +
        wu * (∑ j : Fin (Q + 1), if i.val < j.val then
          Real.exp (-rho * ((j.val - i.val : ℕ) : ℝ)) else 0) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    by_cases hij : i.val < j.val
    · simp only [hij, if_true]
      simpa [ws, wu] using rightExpKernel_mul_weight_eq a b rho i j hij
    · simp [hij]
  have hws : 0 ≤ ws := Real.exp_nonneg _
  have hwu : 0 ≤ wu := Real.exp_nonneg _
  rw [show (∑ j, twoSidedExpKernel a b i j *
      twoSidedExpWeight a b rho j) =
      (∑ j, (if j.val < i.val then
          Real.exp (a * ((i.val - j.val : ℕ) : ℝ)) else 0) *
            twoSidedExpWeight a b rho j) +
      ∑ j, (if i.val < j.val then
          Real.exp (b * ((j.val - i.val : ℕ) : ℝ)) else 0) *
            twoSidedExpWeight a b rho j by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    simp only [twoSidedExpKernel]
    ring]
  rw [hleft_eq, hright_eq]
  change ws * _ + wu * _ + (ws * _ + wu * _) ≤ (Er + Eg) * (ws + wu)
  calc
    ws * _ + wu * _ + (ws * _ + wu * _) ≤
        ws * Er + wu * Eg + (ws * Eg + wu * Er) := by
      gcongr
    _ = (Er + Eg) * (ws + wu) := by ring

lemma finite_twoSided_quadratic_recurrence_le
    {Q : ℕ} (d : Fin (Q + 1) → ℝ)
    {a b rho C B delta : ℝ}
    (hd : ∀ i, 0 ≤ d i) (hd_delta : ∀ i, d i ≤ delta)
    (hrho : 0 < rho) (hgap : a + b + rho < 0)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hdelta : 0 ≤ delta)
    (hsmall : B * C * delta *
      (Real.exp rho / rho +
        Real.exp (-(a + b + rho)) / (-(a + b + rho))) ≤ 1 / 2)
    (hstep : ∀ i,
      d i ≤ C * delta *
          (Real.exp (a * i.val) +
            Real.exp (b * ((Q - i.val : ℕ) : ℝ))) +
        B * C * ∑ j, twoSidedExpKernel a b i j * d j ^ 2) :
    ∀ i, d i ≤ 2 * (C * delta) * twoSidedExpWeight a b rho i := by
  let S := Real.exp rho / rho +
    Real.exp (-(a + b + rho)) / (-(a + b + rho))
  have hweight_direct (i : Fin (Q + 1)) :
      Real.exp (a * i.val) +
          Real.exp (b * ((Q - i.val : ℕ) : ℝ)) ≤
        twoSidedExpWeight a b rho i := by
    apply add_le_add <;> apply Real.exp_le_exp.mpr
    · have hi : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
      nlinarith
    · have hi : (0 : ℝ) ≤ (Q - i.val : ℕ) := Nat.cast_nonneg _
      nlinarith
  have hsquare (j : Fin (Q + 1)) : d j ^ 2 ≤ delta * d j := by
    nlinarith [hd j, hd_delta j]
  apply finite_weighted_maximum_le_two_of_kernel_bound
    d (twoSidedExpWeight a b rho) (twoSidedExpKernel a b)
    hd (twoSidedExpWeight_pos a b rho)
    (mul_nonneg (mul_nonneg hB hC) hdelta) (by simpa [S, mul_assoc] using hsmall)
    (twoSidedExpKernel_nonneg a b)
    (fun i => by simpa [S] using twoSidedExpKernel_weight_sum_le hrho hgap i)
  intro i
  calc
    d i ≤ C * delta *
          (Real.exp (a * i.val) +
            Real.exp (b * ((Q - i.val : ℕ) : ℝ))) +
        B * C * ∑ j, twoSidedExpKernel a b i j * d j ^ 2 := hstep i
    _ ≤ C * delta * twoSidedExpWeight a b rho i +
        B * C * ∑ j, twoSidedExpKernel a b i j * (delta * d j) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (hweight_direct i)
          (mul_nonneg hC hdelta)
      · apply mul_le_mul_of_nonneg_left _ (mul_nonneg hB hC)
        apply Finset.sum_le_sum
        intro j _hj
        exact mul_le_mul_of_nonneg_left (hsquare j)
          (twoSidedExpKernel_nonneg a b i j)
    _ = (C * delta) * twoSidedExpWeight a b rho i +
        (B * C * delta) * ∑ j, twoSidedExpKernel a b i j * d j := by
      apply congrArg₂ (· + ·)
      · ring
      · calc
          B * C * ∑ j, twoSidedExpKernel a b i j * (delta * d j) =
              ∑ j, B * C *
                (twoSidedExpKernel a b i j * (delta * d j)) :=
            Finset.mul_sum _ _ _
          _ = ∑ j, (B * C * delta) *
                (twoSidedExpKernel a b i j * d j) := by
            apply Finset.sum_congr rfl
            intro j _hj
            ring
          _ = (B * C * delta) *
                ∑ j, twoSidedExpKernel a b i j * d j :=
            (Finset.mul_sum _ _ _).symm

end Submission.Helpers
