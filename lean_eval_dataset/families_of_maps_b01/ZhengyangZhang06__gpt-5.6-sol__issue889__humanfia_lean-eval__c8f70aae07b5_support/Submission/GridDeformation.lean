import Mathlib
import Submission.SimplexCoordinates

open Set Filter
open scoped Topology

namespace Submission.GridDeformation

/-- The piecewise-linear ramp that rises from `0` to `1` on the `j`th
subinterval of the uniform `n`-grid. -/
def ramp (n : ℕ) (j : Fin n) (s : ℝ) : ℝ :=
  max 0 (min 1 ((n : ℝ) * s - (j : ℝ)))

theorem continuous_ramp (n : ℕ) (j : Fin n) : Continuous (ramp n j) := by
  unfold ramp
  fun_prop

theorem ramp_nonneg (n : ℕ) (j : Fin n) (s : ℝ) : 0 ≤ ramp n j s := by
  simp [ramp]

theorem ramp_le_one (n : ℕ) (j : Fin n) (s : ℝ) : ramp n j s ≤ 1 := by
  simp [ramp]

theorem ramp_mono (n : ℕ) (j : Fin n) : Monotone (ramp n j) := by
  intro s t hst
  unfold ramp
  gcongr

@[simp]
theorem ramp_zero (n : ℕ) (j : Fin n) : ramp n j 0 = 0 := by
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  simp [ramp, hj]

@[simp]
theorem ramp_one {n : ℕ} (j : Fin n) : ramp n j 1 = 1 := by
  have hj : (j : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast j.isLt
  have h : (1 : ℝ) ≤ (n : ℝ) - (j : ℝ) := by linarith
  simp [ramp, h]

/-- The cumulative piecewise-linear redistribution determined by the weights
`r`. -/
def cdf {n : ℕ} (r : Fin n → ℝ) (s : ℝ) : ℝ :=
  ∑ j, r j * ramp n j s

theorem continuous_cdf {n : ℕ} (r : Fin n → ℝ) : Continuous (cdf r) := by
  unfold cdf
  apply continuous_finsetSum
  intro j _hj
  exact continuous_const.mul (continuous_ramp n j)

theorem continuous_cdf_family {n : ℕ} {X : Type*} [TopologicalSpace X]
    (r : X → Fin n → ℝ) (hr : ∀ j, Continuous fun x => r x j) :
    Continuous fun q : X × ℝ => cdf (r q.1) q.2 := by
  unfold cdf
  apply continuous_finsetSum
  intro j _hj
  exact ((hr j).comp continuous_fst).mul ((continuous_ramp n j).comp continuous_snd)

@[simp]
theorem cdf_zero {n : ℕ} (r : Fin n → ℝ) : cdf r 0 = 0 := by
  simp [cdf]

@[simp]
theorem cdf_one {n : ℕ} (r : Fin n → ℝ) :
    cdf r 1 = ∑ j, r j := by
  simp [cdf]

theorem cdf_mono {n : ℕ} (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j) :
    Monotone (cdf r) := by
  intro s t hst
  unfold cdf
  apply Finset.sum_le_sum
  intro j _hj
  exact mul_le_mul_of_nonneg_left (ramp_mono n j hst) (hr j)

theorem cdf_nonneg {n : ℕ} (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j) (s : ℝ) :
    0 ≤ cdf r s := by
  unfold cdf
  apply Finset.sum_nonneg
  intro j _hj
  exact mul_nonneg (hr j) (ramp_nonneg n j s)

theorem cdf_le_one {n : ℕ} (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j)
    (hrsum : ∑ j, r j = 1) (s : ℝ) : cdf r s ≤ 1 := by
  calc
    cdf r s ≤ ∑ j, r j * 1 := by
      unfold cdf
      apply Finset.sum_le_sum
      intro j _hj
      exact mul_le_mul_of_nonneg_left (ramp_le_one n j s) (hr j)
    _ = 1 := by simpa using hrsum

theorem ramp_eq_one_of_cell_lt {n : ℕ} {i j : Fin n} (hij : i < j)
    {s : ℝ} (hs : ((j : ℝ) / n : ℝ) ≤ s) : ramp n i s = 1 := by
  have hn : 0 < n := Nat.pos_of_ne_zero fun hn0 => by simpa [hn0] using j.isLt
  have hi : (i : ℝ) + 1 ≤ (j : ℝ) := by
    exact_mod_cast hij
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h : (1 : ℝ) ≤ (n : ℝ) * s - (i : ℝ) := by
    have : (j : ℝ) ≤ (n : ℝ) * s := by
      calc
        (j : ℝ) = (n : ℝ) * ((j : ℝ) / n) := by field_simp
        _ ≤ (n : ℝ) * s := mul_le_mul_of_nonneg_left hs hn0.le
    linarith
  simp [ramp, h]

theorem ramp_eq_zero_of_lt_cell {n : ℕ} {i j : Fin n} (hji : j < i)
    {s : ℝ} (hs : s ≤ (((j : ℕ) + 1 : ℕ) : ℝ) / n) : ramp n i s = 0 := by
  have hn : 0 < n := Nat.pos_of_ne_zero fun hn0 => by simpa [hn0] using i.isLt
  have hi : ((j : ℕ) + 1 : ℕ) ≤ i := Nat.succ_le_iff.mpr hji
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h : (n : ℝ) * s - (i : ℝ) ≤ 0 := by
    have : (n : ℝ) * s ≤ (((j : ℕ) + 1 : ℕ) : ℝ) := by
      calc
        (n : ℝ) * s ≤ (n : ℝ) * ((((j : ℕ) + 1 : ℕ) : ℝ) / n) :=
          mul_le_mul_of_nonneg_left hs hn0.le
        _ = (((j : ℕ) + 1 : ℕ) : ℝ) := by field_simp
    exact sub_nonpos.mpr (this.trans (by exact_mod_cast hi))
  simp [ramp, h]

/-- Away from its own grid interval, a ramp is constant across that
interval. -/
theorem ramp_eq_of_mem_same_cell {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {s t : ℝ}
    (hs0 : ((j : ℝ) / n : ℝ) ≤ s)
    (hs1 : s ≤ (((j : ℕ) + 1 : ℕ) : ℝ) / n)
    (ht0 : ((j : ℝ) / n : ℝ) ≤ t)
    (ht1 : t ≤ (((j : ℕ) + 1 : ℕ) : ℝ) / n) :
    ramp n i s = ramp n i t := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · rw [ramp_eq_one_of_cell_lt hij hs0, ramp_eq_one_of_cell_lt hij ht0]
  · rw [ramp_eq_zero_of_lt_cell hji hs1, ramp_eq_zero_of_lt_cell hji ht1]

/-- On the `j`th grid cell, the cumulative map is independent of the
coordinate when the `j`th weight vanishes. -/
theorem cdf_eq_of_eq_zero_of_mem_same_cell {n : ℕ} (r : Fin n → ℝ) (j : Fin n)
    (hrj : r j = 0) {s t : ℝ}
    (hs0 : ((j : ℝ) / n : ℝ) ≤ s)
    (hs1 : s ≤ (((j : ℕ) + 1 : ℕ) : ℝ) / n)
    (ht0 : ((j : ℝ) / n : ℝ) ≤ t)
    (ht1 : t ≤ (((j : ℕ) + 1 : ℕ) : ℝ) / n) :
    cdf r s = cdf r t := by
  unfold cdf
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hij : i = j
  · subst i
    simp [hrj]
  · rw [ramp_eq_of_mem_same_cell hij hs0 hs1 ht0 ht1]

section Simplex

/-- Extend a finite vector by zero to natural-number indices. -/
def coord {m : ℕ} (w : Fin (m + 1) → ℝ) (a : ℕ) : ℝ :=
  if h : a < m + 1 then w ⟨a, h⟩ else 0

@[simp]
theorem coord_fin {m : ℕ} (w : Fin (m + 1) → ℝ) (i : Fin (m + 1)) :
    coord w i = w i := by
  simp [coord, i.isLt]

/-- Prefix mass in the first `a` barycentric coordinates. -/
def prefixMass {m : ℕ} (w : Fin (m + 1) → ℝ) (a : ℕ) : ℝ :=
  ∑ i ∈ Finset.range a, coord w i

@[simp]
theorem prefixMass_zero {m : ℕ} (w : Fin (m + 1) → ℝ) : prefixMass w 0 = 0 := by
  simp [prefixMass]

theorem prefixMass_succ {m : ℕ} (w : Fin (m + 1) → ℝ) (a : ℕ) :
    prefixMass w (a + 1) = prefixMass w a + coord w a := by
  simp [prefixMass, Finset.sum_range_succ]

@[simp]
theorem prefixMass_fin_succ {m : ℕ} (w : Fin (m + 1) → ℝ) (i : Fin (m + 1)) :
    prefixMass w (i + 1) = prefixMass w i + w i := by
  rw [prefixMass_succ]
  simp

theorem prefixMass_total {m : ℕ} (w : Fin (m + 1) → ℝ) :
    prefixMass w (m + 1) = ∑ i, w i := by
  rw [prefixMass, ← Fin.sum_univ_eq_sum_range (fun a => coord w a) (m + 1)]
  apply Finset.sum_congr rfl
  intro i _hi
  simp

@[simp]
theorem prefixMass_total_stdSimplex {m : ℕ} (w : stdSimplex ℝ (Fin (m + 1))) :
    prefixMass w.1 (m + 1) = 1 := by
  rw [prefixMass_total]
  exact w.2.2

theorem continuous_prefixMass {m : ℕ} (a : ℕ) :
    Continuous fun w : stdSimplex ℝ (Fin (m + 1)) => prefixMass w.1 a := by
  unfold prefixMass
  apply continuous_finsetSum
  intro i hi
  have hi' : i < a := Finset.mem_range.mp hi
  unfold coord
  split_ifs with him
  · exact (continuous_apply (⟨i, him⟩ : Fin (m + 1))).comp continuous_subtype_val
  · exact continuous_const

/-- The new barycentric weights obtained by applying `cdf r` to all prefix
masses and taking successive differences. -/
def redistributedWeights {m n : ℕ} (r : Fin n → ℝ)
    (w : stdSimplex ℝ (Fin (m + 1))) (i : Fin (m + 1)) : ℝ :=
  cdf r (prefixMass w.1 (i + 1)) - cdf r (prefixMass w.1 i)

theorem redistributedWeights_nonneg {m n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ j, 0 ≤ r j) (w : stdSimplex ℝ (Fin (m + 1)))
    (i : Fin (m + 1)) : 0 ≤ redistributedWeights r w i := by
  unfold redistributedWeights
  apply sub_nonneg.mpr
  apply cdf_mono r hr
  rw [prefixMass_fin_succ]
  exact le_add_of_nonneg_right (w.2.1 i)

theorem sum_redistributedWeights {m n : ℕ} (r : Fin n → ℝ)
    (hrsum : ∑ j, r j = 1) (w : stdSimplex ℝ (Fin (m + 1))) :
    ∑ i, redistributedWeights r w i = 1 := by
  calc
    ∑ i, redistributedWeights r w i =
        ∑ i ∈ Finset.range (m + 1),
          ((fun a => cdf r (prefixMass w.1 a)) (i + 1) -
            (fun a => cdf r (prefixMass w.1 a)) i) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i _hi
      rfl
    _ = cdf r (prefixMass w.1 (m + 1)) - cdf r (prefixMass w.1 0) := by
      simpa only using
        (Finset.sum_range_sub (fun a => cdf r (prefixMass w.1 a)) (m + 1))
    _ = 1 := by
      rw [prefixMass_total_stdSimplex, prefixMass_zero, cdf_one, cdf_zero, hrsum, sub_zero]

/-- The cumulative grid deformation as a self-map of the standard simplex. -/
def redistribute {m n : ℕ} (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j)
    (hrsum : ∑ j, r j = 1) (w : stdSimplex ℝ (Fin (m + 1))) :
    stdSimplex ℝ (Fin (m + 1)) :=
  ⟨redistributedWeights r w, redistributedWeights_nonneg r hr w,
    sum_redistributedWeights r hrsum w⟩

@[simp]
theorem redistribute_apply {m n : ℕ} (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j)
    (hrsum : ∑ j, r j = 1) (w : stdSimplex ℝ (Fin (m + 1)))
    (i : Fin (m + 1)) :
    redistribute r hr hrsum w i = redistributedWeights r w i :=
  rfl

theorem continuous_redistributedWeights {m n : ℕ} (r : Fin n → ℝ)
    (i : Fin (m + 1)) :
    Continuous fun w : stdSimplex ℝ (Fin (m + 1)) => redistributedWeights r w i := by
  unfold redistributedWeights
  apply Continuous.sub
  · exact (continuous_cdf r).comp (continuous_prefixMass (i + 1))
  · exact (continuous_cdf r).comp (continuous_prefixMass i)

theorem continuous_redistribute {m n : ℕ} (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j)
    (hrsum : ∑ j, r j = 1) : Continuous (redistribute (m := m) r hr hrsum) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun i => continuous_redistributedWeights r i

theorem continuous_redistribute_family {m n : ℕ} {X : Type*} [TopologicalSpace X]
    (r : X → Fin n → ℝ) (hr_cont : ∀ j, Continuous fun x => r x j)
    (hr_nonneg : ∀ x j, 0 ≤ r x j) (hr_sum : ∀ x, ∑ j, r x j = 1) :
    Continuous fun q : X × stdSimplex ℝ (Fin (m + 1)) =>
      redistribute (r q.1) (hr_nonneg q.1) (hr_sum q.1) q.2 := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  change Continuous fun q : X × stdSimplex ℝ (Fin (m + 1)) =>
    cdf (r q.1) (prefixMass q.2.1 (i + 1)) -
      cdf (r q.1) (prefixMass q.2.1 i)
  apply Continuous.sub
  · exact (continuous_cdf_family r hr_cont).comp
      (continuous_fst.prodMk ((continuous_prefixMass (i + 1)).comp continuous_snd))
  · exact (continuous_cdf_family r hr_cont).comp
      (continuous_fst.prodMk ((continuous_prefixMass i).comp continuous_snd))

/-- A zero barycentric coordinate remains zero after redistribution. -/
theorem redistribute_eq_zero_of_eq_zero {m n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ j, 0 ≤ r j) (hrsum : ∑ j, r j = 1)
    (w : stdSimplex ℝ (Fin (m + 1))) (i : Fin (m + 1)) (hi : w i = 0) :
    redistribute r hr hrsum w i = 0 := by
  change cdf r (prefixMass w.1 (i + 1)) - cdf r (prefixMass w.1 i) = 0
  change w.1 i = 0 at hi
  rw [prefixMass_fin_succ, hi, add_zero, sub_self]

theorem coord_nonneg {m : ℕ} (w : stdSimplex ℝ (Fin (m + 1))) (a : ℕ) :
    0 ≤ coord w.1 a := by
  unfold coord
  split_ifs with ha
  · exact w.2.1 ⟨a, ha⟩
  · exact le_rfl

theorem prefixMass_mono {m : ℕ} (w : stdSimplex ℝ (Fin (m + 1))) :
    Monotone (prefixMass w.1) := by
  intro a b hab
  unfold prefixMass
  exact Finset.sum_mono_set_of_nonneg (coord_nonneg w) (Finset.range_mono hab)

theorem prefixMass_nonneg {m : ℕ} (w : stdSimplex ℝ (Fin (m + 1))) (a : ℕ) :
    0 ≤ prefixMass w.1 a := by
  simpa only [prefixMass_zero] using prefixMass_mono w (Nat.zero_le a)

theorem prefixMass_le_one {m : ℕ} (w : stdSimplex ℝ (Fin (m + 1)))
    {a : ℕ} (ha : a ≤ m + 1) : prefixMass w.1 a ≤ 1 := by
  rw [← prefixMass_total_stdSimplex w]
  exact prefixMass_mono w ha

/-- A uniform grid cell in an `m`-simplex records one grid interval for
each of its `m` nonconstant prefix coordinates. -/
abbrev GridCell (m n : ℕ) := Fin m → Fin n

def MemGridCell {m n : ℕ} (c : GridCell m n)
    (w : stdSimplex ℝ (Fin (m + 1))) : Prop :=
  ∀ a : Fin m,
    ((c a : ℝ) / n : ℝ) ≤ prefixMass w.1 (a + 1) ∧
      prefixMass w.1 (a + 1) ≤ (((c a : ℕ) + 1 : ℕ) : ℝ) / n

def GridCell.indices {m n : ℕ} (c : GridCell m n) : Finset (Fin n) :=
  Finset.univ.image c

theorem GridCell.card_indices_le {m n : ℕ} (c : GridCell m n) :
    c.indices.card ≤ m := by
  calc
    c.indices.card ≤ Finset.univ.card := Finset.card_image_le
    _ = m := Fintype.card_fin m

theorem exists_grid_index {n : ℕ} (hn : 0 < n) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∃ j : Fin n,
      ((j : ℝ) / n : ℝ) ≤ s ∧ s ≤ (((j : ℕ) + 1 : ℕ) : ℝ) / n := by
  let a : ℕ := Nat.floor ((n : ℝ) * s)
  let b : ℕ := min a (n - 1)
  have hb_lt : b < n := by
    exact lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hn Nat.zero_lt_one)
  let j : Fin n := ⟨b, hb_lt⟩
  refine ⟨j, ?_, ?_⟩
  · by_cases ha : a ≤ n - 1
    · have hb : b = a := min_eq_left ha
      have hfloor : (a : ℝ) ≤ (n : ℝ) * s := by
        exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) hs0)
      dsimp [j]
      rw [hb]
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      exact (div_le_iff₀ hnR).mpr (by simpa [mul_comm] using hfloor)
    · have hna : n ≤ a := by omega
      have hfloor : (a : ℝ) ≤ (n : ℝ) * s := by
        exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) hs0)
      have hs : s = 1 := by
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn
        have : (n : ℝ) ≤ (n : ℝ) * s :=
          (by exact_mod_cast hna : (n : ℝ) ≤ (a : ℝ)) |>.trans hfloor
        apply le_antisymm hs1
        nlinarith
      have hb : b = n - 1 := min_eq_right ((Nat.sub_le n 1).trans hna)
      subst s
      dsimp [j]
      rw [hb]
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      apply (div_le_iff₀ hnR).mpr
      norm_num
  · by_cases ha : a ≤ n - 1
    · have hb : b = a := min_eq_left ha
      have hceil : (n : ℝ) * s < (a : ℝ) + 1 := Nat.lt_floor_add_one _
      dsimp [j]
      rw [hb]
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      apply (le_div_iff₀ hnR).mpr
      exact (by simpa [mul_comm, Nat.cast_add, Nat.cast_one] using hceil.le)
    · have hna : n ≤ a := by omega
      have hb : b = n - 1 := min_eq_right ((Nat.sub_le n 1).trans hna)
      dsimp [j]
      rw [hb]
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      calc
        s ≤ 1 := hs1
        _ = ((((n - 1 : ℕ) + 1 : ℕ) : ℝ) / n) := by
          rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn.ne')]
          field_simp

theorem exists_mem_gridCell {m n : ℕ} (hn : 0 < n)
    (w : stdSimplex ℝ (Fin (m + 1))) :
    ∃ c : GridCell m n, MemGridCell c w := by
  have hindex : ∀ a : Fin m,
      ∃ j : Fin n,
        ((j : ℝ) / n : ℝ) ≤ prefixMass w.1 (a + 1) ∧
          prefixMass w.1 (a + 1) ≤ (((j : ℕ) + 1 : ℕ) : ℝ) / n := by
    intro a
    apply exists_grid_index hn (prefixMass_nonneg w (a + 1))
    apply prefixMass_le_one w
    omega
  choose c hc using hindex
  exact ⟨c, hc⟩

/-- A coordinate projection, extended by zero past the end of a finite
vector. -/
def coordCLM (m a : ℕ) : (Fin (m + 1) → ℝ) →L[ℝ] ℝ :=
  if h : a < m + 1 then ContinuousLinearMap.proj (R := ℝ) (⟨a, h⟩ : Fin (m + 1)) else 0

@[simp]
theorem coordCLM_apply {m : ℕ} (a : ℕ) (w : Fin (m + 1) → ℝ) :
    coordCLM m a w = coord w a := by
  unfold coordCLM coord
  split_ifs <;> rfl

/-- Prefix mass as a continuous linear functional. -/
def prefixCLM (m a : ℕ) : (Fin (m + 1) → ℝ) →L[ℝ] ℝ :=
  ∑ i ∈ Finset.range a, coordCLM m i

@[simp]
theorem prefixCLM_apply {m : ℕ} (a : ℕ) (w : Fin (m + 1) → ℝ) :
    prefixCLM m a w = prefixMass w a := by
  simp [prefixCLM, prefixMass]

/-- A grid cell as a subset of the ambient barycentric-coordinate vector
space. -/
def weightCell {m n : ℕ} (c : GridCell m n) : Set (Fin (m + 1) → ℝ) :=
  stdSimplex ℝ (Fin (m + 1)) ∩
    ⋂ a : Fin m,
      (prefixCLM m (a + 1)) ⁻¹'
        Icc (((c a : ℝ) / n : ℝ)) ((((c a : ℕ) + 1 : ℕ) : ℝ) / n)

theorem mem_weightCell_iff {m n : ℕ} (c : GridCell m n)
    (w : Fin (m + 1) → ℝ) :
    w ∈ weightCell c ↔
      w ∈ stdSimplex ℝ (Fin (m + 1)) ∧
        ∀ a : Fin m,
          ((c a : ℝ) / n : ℝ) ≤ prefixMass w (a + 1) ∧
            prefixMass w (a + 1) ≤ (((c a : ℕ) + 1 : ℕ) : ℝ) / n := by
  simp only [weightCell, mem_inter_iff, mem_iInter, mem_preimage, mem_Icc,
    prefixCLM_apply]

theorem mem_weightCell_coe_iff {m n : ℕ} (c : GridCell m n)
    (w : stdSimplex ℝ (Fin (m + 1))) :
    w.1 ∈ weightCell c ↔ MemGridCell c w := by
  rw [mem_weightCell_iff]
  simp [MemGridCell, w.2]

theorem convex_weightCell {m n : ℕ} (c : GridCell m n) :
    Convex ℝ (weightCell c) := by
  apply (convex_stdSimplex ℝ (Fin (m + 1))).inter
  exact convex_iInter fun a => (convex_Icc _ _).linear_preimage (prefixCLM m (a + 1)).toLinearMap

theorem isClosed_weightCell {m n : ℕ} (c : GridCell m n) :
    IsClosed (weightCell c) := by
  apply (isClosed_stdSimplex ℝ (Fin (m + 1))).inter
  exact isClosed_iInter fun a =>
    isClosed_Icc.preimage (prefixCLM m (a + 1)).continuous

theorem isCompact_weightCell {m n : ℕ} (c : GridCell m n) :
    IsCompact (weightCell c) := by
  exact IsCompact.of_isClosed_subset (isCompact_stdSimplex ℝ (Fin (m + 1)))
    (isClosed_weightCell c) inter_subset_left

/-- The endpoint values of the uniform `n`-grid on the unit interval. -/
noncomputable def gridValues (n : ℕ) : Finset ℝ :=
  (Finset.range (n + 1)).image fun a : ℕ => (a : ℝ) / (n : ℝ)

theorem lower_mem_gridValues {n : ℕ} (j : Fin n) :
    ((j : ℝ) / n : ℝ) ∈ gridValues n := by
  apply Finset.mem_image.mpr
  exact ⟨j.1, Finset.mem_range.mpr (j.isLt.trans_le (Nat.le_succ n)), rfl⟩

theorem upper_mem_gridValues {n : ℕ} (j : Fin n) :
    ((((j : ℕ) + 1 : ℕ) : ℝ) / n : ℝ) ∈ gridValues n := by
  apply Finset.mem_image.mpr
  exact ⟨j.1 + 1, Finset.mem_range.mpr (Nat.succ_le_succ j.isLt), rfl⟩

theorem strict_mem_grid_interval_of_not_mem_gridValues {n : ℕ} (j : Fin n) {s : ℝ}
    (hs : ((j : ℝ) / n : ℝ) ≤ s ∧
      s ≤ (((j : ℕ) + 1 : ℕ) : ℝ) / n)
    (hgrid : s ∉ gridValues n) :
    ((j : ℝ) / n : ℝ) < s ∧
      s < (((j : ℕ) + 1 : ℕ) : ℝ) / n := by
  constructor
  · exact hs.1.lt_of_ne fun h => hgrid (h ▸ lower_mem_gridValues j)
  · exact hs.2.lt_of_ne fun h => hgrid (h ▸ upper_mem_gridValues j)

theorem grid_interval_unique {n : ℕ} (hn : 0 < n) {s : ℝ} (hgrid : s ∉ gridValues n)
    {i j : Fin n}
    (hi : ((i : ℝ) / n : ℝ) ≤ s ∧
      s ≤ (((i : ℕ) + 1 : ℕ) : ℝ) / n)
    (hj : ((j : ℝ) / n : ℝ) ≤ s ∧
      s ≤ (((j : ℕ) + 1 : ℕ) : ℝ) / n) :
    i = j := by
  apply Fin.ext
  by_contra hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hs_i := strict_mem_grid_interval_of_not_mem_gridValues i hi hgrid
    have hs_j := strict_mem_grid_interval_of_not_mem_gridValues j hj hgrid
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hsucc : (i : ℕ) + 1 ≤ j := Nat.succ_le_iff.mpr hij
    have hle : ((((i : ℕ) + 1 : ℕ) : ℝ) / n : ℝ) ≤ (j : ℝ) / n := by
      exact (div_le_div_iff_of_pos_right hnR).mpr (by exact_mod_cast hsucc)
    linarith
  · have hs_i := strict_mem_grid_interval_of_not_mem_gridValues i hi hgrid
    have hs_j := strict_mem_grid_interval_of_not_mem_gridValues j hj hgrid
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hsucc : (j : ℕ) + 1 ≤ i := Nat.succ_le_iff.mpr hji
    have hle : ((((j : ℕ) + 1 : ℕ) : ℝ) / n : ℝ) ≤ (i : ℝ) / n := by
      exact (div_le_div_iff_of_pos_right hnR).mpr (by exact_mod_cast hsucc)
    linarith

def prefixSignature {m : ℕ} (w : Fin (m + 1) → ℝ) : Fin m → ℝ :=
  fun a => prefixMass w (a + 1)

theorem prefixSignature_injective {m : ℕ} :
    Set.InjOn prefixSignature (stdSimplex ℝ (Fin (m + 1))) := by
  intro w hw z hz hwz
  funext i
  have hleft : prefixMass w i = prefixMass z i := by
    by_cases hi : (i : ℕ) = 0
    · have hi' : i = 0 := Fin.ext hi
      subst i
      simp
    · have ha_lt : (i : ℕ) - 1 < m := by omega
      let a : Fin m := ⟨(i : ℕ) - 1, ha_lt⟩
      have ha_eq : (a : ℕ) + 1 = (i : ℕ) := by
        dsimp [a]
        omega
      simpa only [prefixSignature, ha_eq] using congrFun hwz a
  have hright : prefixMass w ((i : ℕ) + 1) = prefixMass z ((i : ℕ) + 1) := by
    by_cases hi : (i : ℕ) < m
    · let a : Fin m := ⟨i, hi⟩
      simpa only [prefixSignature] using congrFun hwz a
    · have hitop : (i : ℕ) = m := by omega
      rw [hitop, prefixMass_total, prefixMass_total]
      exact hw.2.trans hz.2.symm
  have hsw := prefixMass_fin_succ w i
  have hsz := prefixMass_fin_succ z i
  linarith

def gridPrefixPoints (m n : ℕ) : Set (Fin (m + 1) → ℝ) :=
  stdSimplex ℝ (Fin (m + 1)) ∩
    {w | ∀ a : Fin m, prefixSignature w a ∈ gridValues n}

theorem finite_gridPrefixPoints (m n : ℕ) : (gridPrefixPoints m n).Finite := by
  let target : Set (Fin m → ℝ) := Set.univ.pi fun _ => (gridValues n : Set ℝ)
  have htarget : target.Finite := Set.Finite.pi fun _ => (gridValues n).finite_toSet
  refine Set.Finite.of_finite_image (f := @prefixSignature m) (htarget.subset ?_) ?_
  · rintro y ⟨w, hw, rfl⟩
    intro a _ha
    exact hw.2 a
  · intro w hw z hz hwz
    exact prefixSignature_injective hw.1 hz.1 hwz

@[simp]
theorem zero_mem_gridValues {n : ℕ} : (0 : ℝ) ∈ gridValues n := by
  apply Finset.mem_image.mpr
  exact ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n), by simp⟩

@[simp]
theorem one_mem_gridValues {n : ℕ} (hn : 0 < n) : (1 : ℝ) ∈ gridValues n := by
  apply Finset.mem_image.mpr
  refine ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n), ?_⟩
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  exact div_self hn0

/-- Marks the complete plateau of prefix coordinates equal to the selected
prefix. Its discrete derivative gives a direction supported at the two ends
of that plateau. -/
noncomputable def prefixMarker {m : ℕ} (w : Fin (m + 1) → ℝ) (a : Fin m)
    (q : ℕ) : ℝ :=
  if prefixMass w q = prefixMass w (a + 1) then 1 else 0

@[simp]
theorem prefixMarker_selected {m : ℕ} (w : Fin (m + 1) → ℝ) (a : Fin m) :
    prefixMarker w a (a + 1) = 1 := by
  simp [prefixMarker]

theorem prefixMarker_zero {m n : ℕ} (w : stdSimplex ℝ (Fin (m + 1)))
    (a : Fin m) (hgrid : prefixMass w.1 (a + 1) ∉ gridValues n) :
    prefixMarker w.1 a 0 = 0 := by
  simp only [prefixMarker, prefixMass_zero]
  split_ifs with h
  · exact (hgrid (h.symm ▸ zero_mem_gridValues)).elim
  · rfl

theorem prefixMarker_total {m n : ℕ} (hn : 0 < n)
    (w : stdSimplex ℝ (Fin (m + 1))) (a : Fin m)
    (hgrid : prefixMass w.1 (a + 1) ∉ gridValues n) :
    prefixMarker w.1 a (m + 1) = 0 := by
  simp only [prefixMarker, prefixMass_total_stdSimplex]
  split_ifs with h
  · exact (hgrid (h.symm ▸ one_mem_gridValues hn)).elim
  · rfl

/-- Perturb the two ends of the plateau containing the selected prefix
coordinate. -/
noncomputable def perturbWeights {m : ℕ} (w : Fin (m + 1) → ℝ) (a : Fin m) (e : ℝ)
    (i : Fin (m + 1)) : ℝ :=
  w i + e * (prefixMarker w a (i + 1) - prefixMarker w a i)

@[simp]
theorem perturbWeights_zero {m : ℕ} (w : Fin (m + 1) → ℝ) (a : Fin m) :
    perturbWeights w a 0 = w := by
  funext i
  simp [perturbWeights]

theorem prefixMass_perturbWeights {m : ℕ} (w : Fin (m + 1) → ℝ)
    (a : Fin m) (e : ℝ) {q : ℕ} (hq : q ≤ m + 1) :
    prefixMass (perturbWeights w a e) q =
      prefixMass w q + e * (prefixMarker w a q - prefixMarker w a 0) := by
  rw [prefixMass]
  have hcoord : ∀ i ∈ Finset.range q,
      coord (perturbWeights w a e) i =
        coord w i + e * (prefixMarker w a (i + 1) - prefixMarker w a i) := by
    intro i hi
    have him : i < m + 1 := (Finset.mem_range.mp hi).trans_le hq
    simp [coord, perturbWeights, him]
  calc
    ∑ i ∈ Finset.range q, coord (perturbWeights w a e) i =
        ∑ i ∈ Finset.range q,
          (coord w i + e * (prefixMarker w a (i + 1) - prefixMarker w a i)) := by
            apply Finset.sum_congr rfl hcoord
    _ = prefixMass w q +
        e * ∑ i ∈ Finset.range q,
          (prefixMarker w a (i + 1) - prefixMarker w a i) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
            rfl
    _ = prefixMass w q + e * (prefixMarker w a q - prefixMarker w a 0) := by
      rw [Finset.sum_range_sub]

theorem perturbDirection_ne_zero_coord {m : ℕ}
    (w : stdSimplex ℝ (Fin (m + 1))) (a : Fin m) (i : Fin (m + 1))
    (hi : prefixMarker w.1 a (i + 1) - prefixMarker w.1 a i ≠ 0) :
    0 < w.1 i := by
  have hmono := prefixMass_mono w (Nat.le_succ i)
  have hsucc := prefixMass_fin_succ w.1 i
  by_cases hleft : prefixMass w.1 i = prefixMass w.1 (a + 1)
  · have hmarkleft : prefixMarker w.1 a i = 1 := by simp [prefixMarker, hleft]
    have hright : prefixMass w.1 (i + 1) ≠ prefixMass w.1 (a + 1) := by
      intro heq
      apply hi
      have hmarkright : prefixMarker w.1 a (i + 1) = 1 := by
        exact if_pos heq
      rw [hmarkright, hmarkleft]
      norm_num
    have hlt : prefixMass w.1 i < prefixMass w.1 (i + 1) :=
      lt_of_le_of_ne hmono fun h => hright (h.symm.trans hleft)
    linarith
  · have hmarkleft : prefixMarker w.1 a i = 0 := by simp [prefixMarker, hleft]
    have hright : prefixMass w.1 (i + 1) = prefixMass w.1 (a + 1) := by
      by_contra hne
      apply hi
      have hmarkright : prefixMarker w.1 a (i + 1) = 0 := by
        exact if_neg hne
      rw [hmarkright, hmarkleft]
      norm_num
    have hlt : prefixMass w.1 i < prefixMass w.1 (i + 1) :=
      lt_of_le_of_ne hmono fun h => hleft (h.trans hright)
    linarith

theorem eventually_perturbWeights_mem_weightCell {m n : ℕ} (hn : 0 < n)
    (c : GridCell m n) (w : stdSimplex ℝ (Fin (m + 1)))
    (hw : MemGridCell c w) (a : Fin m)
    (hgrid : prefixMass w.1 (a + 1) ∉ gridValues n) :
    ∀ᶠ e in 𝓝 0, perturbWeights w.1 a e ∈ weightCell c := by
  have hnonneg : ∀ᶠ e in 𝓝 0, ∀ i, 0 ≤ perturbWeights w.1 a e i := by
    rw [Filter.eventually_all]
    intro i
    let d := prefixMarker w.1 a (i + 1) - prefixMarker w.1 a i
    by_cases hd : d = 0
    · exact Filter.Eventually.of_forall fun e => by simp [perturbWeights, d, hd, w.2.1 i]
    · have hwi : 0 < w.1 i := perturbDirection_ne_zero_coord w a i hd
      have hcont : Continuous fun e : ℝ => perturbWeights w.1 a e i := by
        unfold perturbWeights
        fun_prop
      have hwi0 : 0 < perturbWeights w.1 a 0 i := by
        simpa [perturbWeights] using hwi
      exact (hcont.continuousAt.eventually (lt_mem_nhds hwi0)).mono fun _ he => he.le
  have hbounds : ∀ᶠ e in 𝓝 0, ∀ b : Fin m,
      ((c b : ℝ) / n : ℝ) ≤ prefixMass (perturbWeights w.1 a e) (b + 1) ∧
        prefixMass (perturbWeights w.1 a e) (b + 1) ≤
          (((c b : ℕ) + 1 : ℕ) : ℝ) / n := by
    rw [Filter.eventually_all]
    intro b
    by_cases hb : prefixMass w.1 (b + 1) = prefixMass w.1 (a + 1)
    · have hs := strict_mem_grid_interval_of_not_mem_gridValues (c b) (hw b)
          (hb ▸ hgrid)
      have hcont : Continuous fun e : ℝ =>
          prefixMass w.1 (b + 1) + e *
            (prefixMarker w.1 a (b + 1) - 0) := by fun_prop
      have hs0 : ((c b : ℝ) / n : ℝ) <
          prefixMass w.1 (b + 1) + 0 *
            (prefixMarker w.1 a (b + 1) - 0) := by simpa using hs.1
      have hs1 : prefixMass w.1 (b + 1) + 0 *
            (prefixMarker w.1 a (b + 1) - 0) <
          (((c b : ℕ) + 1 : ℕ) : ℝ) / n := by simpa using hs.2
      have hnear := hcont.continuousAt.eventually (Ioo_mem_nhds hs0 hs1)
      filter_upwards [hnear] with e he
      rw [prefixMass_perturbWeights w.1 a e (by omega), prefixMarker_zero w a hgrid]
      exact ⟨he.1.le, he.2.le⟩
    · exact Filter.Eventually.of_forall fun e => by
        rw [prefixMass_perturbWeights w.1 a e (by omega), prefixMarker_zero w a hgrid]
        simpa [prefixMarker, hb, Nat.cast_add, Nat.cast_one] using hw b
  filter_upwards [hnonneg, hbounds] with e he hbe
  apply (mem_weightCell_iff c _).mpr
  refine ⟨⟨he, ?_⟩, hbe⟩
  · rw [← prefixMass_total]
    rw [prefixMass_perturbWeights w.1 a e le_rfl,
      prefixMass_total_stdSimplex, prefixMarker_total hn w a hgrid,
      prefixMarker_zero w a hgrid]
    ring

/-- Every extreme point of a grid cell has all its nonconstant prefix
coordinates on the grid. -/
theorem extremePoints_weightCell_subset_gridPrefixPoints {m n : ℕ} (hn : 0 < n)
    (c : GridCell m n) :
    (weightCell c).extremePoints ℝ ⊆ gridPrefixPoints m n := by
  intro w hwext
  have hwcell : w ∈ weightCell c := hwext.1
  have hstd : w ∈ stdSimplex ℝ (Fin (m + 1)) :=
    (mem_weightCell_iff c w).mp hwcell |>.1
  refine ⟨hstd, ?_⟩
  intro a
  by_contra hgrid
  let ws : stdSimplex ℝ (Fin (m + 1)) := ⟨w, hstd⟩
  have hwgrid : MemGridCell c ws := by
    exact (mem_weightCell_coe_iff c ws).mp hwcell
  have hpert := eventually_perturbWeights_mem_weightCell hn c ws hwgrid a hgrid
  obtain ⟨l, u, hzero, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hpert
  let e : ℝ := min (-l) u / 2
  have hmin : 0 < min (-l) u := lt_min (neg_pos.mpr hzero.1) hzero.2
  have hepos : 0 < e := by
    exact div_pos hmin (by norm_num)
  have helt : e < min (-l) u := by
    dsimp [e]
    linarith
  have helu : e < u := helt.trans_le (min_le_right _ _)
  have helneg : e < -l := helt.trans_le (min_le_left _ _)
  have hplus : perturbWeights w a e ∈ weightCell c :=
    hsub ⟨hzero.1.trans (by positivity), helu⟩
  have hminus : perturbWeights w a (-e) ∈ weightCell c :=
    hsub ⟨(by linarith), (by linarith)⟩
  let v : Fin (m + 1) → ℝ := fun i =>
    e * (prefixMarker w a (i + 1) - prefixMarker w a i)
  have hplus_eq : perturbWeights w a e = w + v := by
    funext i
    simp [perturbWeights, v]
  have hminus_eq : perturbWeights w a (-e) = w - v := by
    funext i
    simp [perturbWeights, v]
    ring
  have hopen : w ∈ openSegment ℝ (perturbWeights w a e) (perturbWeights w a (-e)) := by
    rw [hplus_eq, hminus_eq]
    exact mem_openSegment_add_sub (𝕜 := ℝ) w v
  have heq : perturbWeights w a e = w := hwext.2 hplus hminus hopen
  have hpref := prefixMass_perturbWeights w a e (q := a + 1) (by omega)
  have hmarker0 : prefixMarker w a 0 = 0 := prefixMarker_zero ws a hgrid
  rw [prefixMarker_selected, hmarker0] at hpref
  have hprefeq := congrArg (fun z => prefixMass z (a + 1)) heq
  linarith

theorem finite_extremePoints_weightCell {m n : ℕ} (hn : 0 < n)
    (c : GridCell m n) : ((weightCell c).extremePoints ℝ).Finite :=
  (finite_gridPrefixPoints m n).subset
    (extremePoints_weightCell_subset_gridPrefixPoints hn c)

/-- The canonical finite vertex set of a grid cell. -/
noncomputable def cellVertices {m n : ℕ} (hn : 0 < n) (c : GridCell m n) :
    Finset (Fin (m + 1) → ℝ) :=
  (finite_extremePoints_weightCell hn c).toFinset

@[simp]
theorem coe_cellVertices {m n : ℕ} (hn : 0 < n) (c : GridCell m n) :
    (cellVertices hn c : Set (Fin (m + 1) → ℝ)) =
      (weightCell c).extremePoints ℝ :=
  (finite_extremePoints_weightCell hn c).coe_toFinset

theorem convexHull_cellVertices {m n : ℕ} (hn : 0 < n) (c : GridCell m n) :
    convexHull ℝ (cellVertices hn c : Set (Fin (m + 1) → ℝ)) = weightCell c := by
  rw [coe_cellVertices]
  have hclosed : IsClosed (convexHull ℝ ((weightCell c).extremePoints ℝ)) :=
    (finite_extremePoints_weightCell hn c).isClosed_convexHull ℝ
  calc
    convexHull ℝ ((weightCell c).extremePoints ℝ) =
        closure (convexHull ℝ ((weightCell c).extremePoints ℝ)) :=
      hclosed.closure_eq.symm
    _ = weightCell c :=
      closure_convexHull_extremePoints (isCompact_weightCell c) (convex_weightCell c)

/-- The exposed constraint in `weightCell c` imposed by the `a`th interval
of another cell `d`. -/
def commonFaceConstraint {m n : ℕ} (c d : GridCell m n) (a : Fin m) :
    Set (Fin (m + 1) → ℝ) :=
  if c a < d a then
    (prefixCLM m (a + 1)).toExposed (weightCell c)
  else if d a < c a then
    (-prefixCLM m (a + 1)).toExposed (weightCell c)
  else weightCell c

theorem isExposed_commonFaceConstraint {m n : ℕ} (c d : GridCell m n) (a : Fin m) :
    IsExposed ℝ (weightCell c) (commonFaceConstraint c d a) := by
  unfold commonFaceConstraint
  split_ifs
  · exact ContinuousLinearMap.toExposed.isExposed
  · exact ContinuousLinearMap.toExposed.isExposed
  · exact IsExposed.refl _

theorem upper_le_lower_of_lt {n : ℕ} (hn : 0 < n) {i j : Fin n} (hij : i < j) :
    ((((i : ℕ) + 1 : ℕ) : ℝ) / n : ℝ) ≤ (j : ℝ) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_le_div_iff_of_pos_right hnR).mpr
  exact_mod_cast Nat.succ_le_iff.mpr hij

theorem lower_le_lower_of_le {n : ℕ} (hn : 0 < n) {i j : Fin n} (hij : i ≤ j) :
    ((i : ℝ) / n : ℝ) ≤ (j : ℝ) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact (div_le_div_iff_of_pos_right hnR).mpr (by exact_mod_cast hij)

theorem upper_le_upper_of_le {n : ℕ} (hn : 0 < n) {i j : Fin n} (hij : i ≤ j) :
    ((((i : ℕ) + 1 : ℕ) : ℝ) / n : ℝ) ≤
      (((j : ℕ) + 1 : ℕ) : ℝ) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_le_div_iff_of_pos_right hnR).mpr
  exact_mod_cast Nat.succ_le_succ hij

theorem mem_commonFaceConstraint_iff {m n : ℕ} (hn : 0 < n)
    (c d : GridCell m n) (hinter : (weightCell c ∩ weightCell d).Nonempty)
    (a : Fin m) (x : Fin (m + 1) → ℝ) :
    x ∈ commonFaceConstraint c d a ↔
      x ∈ weightCell c ∧
        ((d a : ℝ) / n : ℝ) ≤ prefixMass x (a + 1) ∧
          prefixMass x (a + 1) ≤ (((d a : ℕ) + 1 : ℕ) : ℝ) / n := by
  obtain ⟨z, hzc, hzd⟩ := hinter
  have hzc' := (mem_weightCell_iff c z).mp hzc
  have hzd' := (mem_weightCell_iff d z).mp hzd
  unfold commonFaceConstraint
  split_ifs with hcd hdc
  · simp only [ContinuousLinearMap.toExposed, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hxc, hxmax⟩
      have hxc' := (mem_weightCell_iff c x).mp hxc
      have hupper := hxc'.2 a |>.2
      have hzlower := hzd'.2 a |>.1
      have hcross := upper_le_lower_of_lt hn hcd
      have hzle : prefixMass z (a + 1) ≤ prefixMass x (a + 1) := by
        simpa only [prefixCLM_apply] using hxmax z hzc
      refine ⟨hxc, hzlower.trans hzle, ?_⟩
      exact hupper.trans (upper_le_upper_of_le hn hcd.le)
    · rintro ⟨hxc, hxlower, _hxupper⟩
      refine ⟨hxc, ?_⟩
      intro y hyc
      have hyupper := (mem_weightCell_iff c y).mp hyc |>.2 a |>.2
      simpa only [prefixCLM_apply] using
        (hyupper.trans (upper_le_lower_of_lt hn hcd) |>.trans hxlower)
  · simp only [ContinuousLinearMap.toExposed, Set.mem_setOf_eq, neg_apply]
    constructor
    · rintro ⟨hxc, hxmin⟩
      have hxc' := (mem_weightCell_iff c x).mp hxc
      have hxlower := hxc'.2 a |>.1
      have hzupper := hzd'.2 a |>.2
      have hcross := upper_le_lower_of_lt hn hdc
      have hxle : prefixMass x (a + 1) ≤ prefixMass z (a + 1) := by
        have := hxmin z hzc
        simpa only [prefixCLM_apply, neg_le_neg_iff] using this
      refine ⟨hxc, ?_, hxle.trans hzupper⟩
      exact (lower_le_lower_of_le hn hdc.le).trans hxlower
    · rintro ⟨hxc, _hxlower, hxupper⟩
      refine ⟨hxc, ?_⟩
      intro y hyc
      have hylower := (mem_weightCell_iff c y).mp hyc |>.2 a |>.1
      have hxle : prefixMass x (a + 1) ≤ prefixMass y (a + 1) :=
        hxupper.trans (upper_le_lower_of_lt hn hdc) |>.trans hylower
      simpa only [prefixCLM_apply, neg_le_neg_iff] using hxle
  · have hac : c a = d a := le_antisymm (not_lt.mp hdc) (not_lt.mp hcd)
    constructor
    · intro hxc
      refine ⟨hxc, ?_⟩
      simpa only [← hac] using (mem_weightCell_iff c x).mp hxc |>.2 a
    · exact fun hx => hx.1

/-- A carrier-level common face. The explicit insertion of `weightCell c`
also handles zero-dimensional simplices. -/
noncomputable def commonFace {m n : ℕ} (c d : GridCell m n) :
    Set (Fin (m + 1) → ℝ) := by
  classical
  exact ⋂₀ (({weightCell c} : Finset (Set (Fin (m + 1) → ℝ))) ∪
    Finset.univ.image (commonFaceConstraint c d))

theorem mem_commonFace_iff {m n : ℕ} (c d : GridCell m n)
    (x : Fin (m + 1) → ℝ) :
    x ∈ commonFace c d ↔
      x ∈ weightCell c ∧ ∀ a : Fin m, x ∈ commonFaceConstraint c d a := by
  classical
  simp [commonFace]

theorem isExposed_commonFace {m n : ℕ} (c d : GridCell m n) :
    IsExposed ℝ (weightCell c) (commonFace c d) := by
  classical
  let F : Finset (Set (Fin (m + 1) → ℝ)) :=
    {weightCell c} ∪ Finset.univ.image (commonFaceConstraint c d)
  have hFne : F.Nonempty := by
    refine ⟨weightCell c, ?_⟩
    exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
  have hFexposed : ∀ A ∈ F, IsExposed ℝ (weightCell c) A := by
    intro A hA
    rw [Finset.mem_union, Finset.mem_singleton] at hA
    rcases hA with rfl | hA
    · exact IsExposed.refl _
    · obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hA
      exact isExposed_commonFaceConstraint c d a
  have h := IsExposed.sInter hFne hFexposed
  change IsExposed ℝ (weightCell c) (⋂₀ (F : Set (Set (Fin (m + 1) → ℝ)))) at h
  simpa [commonFace, F] using h

theorem commonFace_eq_inter {m n : ℕ} (hn : 0 < n) (c d : GridCell m n)
    (hinter : (weightCell c ∩ weightCell d).Nonempty) :
    commonFace c d = weightCell c ∩ weightCell d := by
  ext x
  rw [mem_commonFace_iff, mem_inter_iff]
  constructor
  · rintro ⟨hxc, hconstraints⟩
    refine ⟨hxc, (mem_weightCell_iff d x).mpr ⟨?_, ?_⟩⟩
    · exact (mem_weightCell_iff c x).mp hxc |>.1
    · intro a
      exact (mem_commonFaceConstraint_iff hn c d hinter a x).mp (hconstraints a) |>.2
  · rintro ⟨hxc, hxd⟩
    refine ⟨hxc, fun a => ?_⟩
    apply (mem_commonFaceConstraint_iff hn c d hinter a x).mpr
    exact ⟨hxc, (mem_weightCell_iff d x).mp hxd |>.2 a⟩

theorem isExposed_inter_weightCell_left {m n : ℕ} (hn : 0 < n)
    (c d : GridCell m n) :
    IsExposed ℝ (weightCell c) (weightCell c ∩ weightCell d) := by
  obtain hinter | hinter := (weightCell c ∩ weightCell d).eq_empty_or_nonempty
  · rw [hinter]
    exact isExposed_empty
  · rw [← commonFace_eq_inter hn c d hinter]
    exact isExposed_commonFace c d

theorem isExposed_inter_weightCell_right {m n : ℕ} (hn : 0 < n)
    (c d : GridCell m n) :
    IsExposed ℝ (weightCell d) (weightCell c ∩ weightCell d) := by
  rw [inter_comm]
  exact isExposed_inter_weightCell_left hn d c

theorem cdf_prefixMass_eq_of_mem_gridCell {m n : ℕ} (r : Fin n → ℝ)
    (hrsum : ∑ j, r j = 1) (c : GridCell m n)
    (hrzero : ∀ a, r (c a) = 0)
    {w z : stdSimplex ℝ (Fin (m + 1))}
    (hw : MemGridCell c w) (hz : MemGridCell c z)
    (q : ℕ) (hq : q ≤ m + 1) :
    cdf r (prefixMass w.1 q) = cdf r (prefixMass z.1 q) := by
  by_cases hq0 : q = 0
  · subst q
    simp
  by_cases hqtop : q = m + 1
  · subst q
    simp [hrsum]
  have hqle : q ≤ m := by omega
  have ha_lt : q - 1 < m := by omega
  let a : Fin m := ⟨q - 1, ha_lt⟩
  have ha_eq : (a : ℕ) + 1 = q := by
    dsimp [a]
    omega
  let j : Fin n := c a
  apply cdf_eq_of_eq_zero_of_mem_same_cell r j (hrzero a)
  · simpa only [j, ha_eq] using (hw a).1
  · simpa only [j, ha_eq] using (hw a).2
  · simpa only [j, ha_eq] using (hz a).1
  · simpa only [j, ha_eq] using (hz a).2

/-- On one grid cell, vanishing of its at-most-`m` selected weights makes
the redistributed point independent of the original point. -/
theorem redistribute_eq_of_mem_gridCell {m n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ j, 0 ≤ r j) (hrsum : ∑ j, r j = 1)
    (c : GridCell m n) (hrzero : ∀ a, r (c a) = 0)
    {w z : stdSimplex ℝ (Fin (m + 1))}
    (hw : MemGridCell c w) (hz : MemGridCell c z) :
    redistribute r hr hrsum w = redistribute r hr hrsum z := by
  apply Subtype.ext
  funext i
  change cdf r (prefixMass w.1 (i + 1)) - cdf r (prefixMass w.1 i) =
    cdf r (prefixMass z.1 (i + 1)) - cdf r (prefixMass z.1 i)
  rw [cdf_prefixMass_eq_of_mem_gridCell r hrsum c hrzero hw hz (i + 1) (by omega),
    cdf_prefixMass_eq_of_mem_gridCell r hrsum c hrzero hw hz i (by omega)]

end Simplex

end Submission.GridDeformation
