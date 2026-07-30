import ChallengeDeps

open LeanEval.Dynamics.LaxApproximation
open MeasureTheory Set
open scoped ENNReal

namespace Submission.Helpers

/-- The canonical representative of a point of the unit additive circle in `[0, 1)`. -/
noncomputable def circleRep (x : AddCircle (1 : ℝ)) : ℝ :=
  AddCircle.equivIco 1 0 x

lemma circleRep_nonneg (x : AddCircle (1 : ℝ)) : 0 ≤ circleRep x :=
  (AddCircle.equivIco 1 0 x).property.1

lemma circleRep_lt_one (x : AddCircle (1 : ℝ)) : circleRep x < 0 + 1 :=
  (AddCircle.equivIco 1 0 x).property.2

@[simp]
lemma circleRep_coe (x : AddCircle (1 : ℝ)) :
    ((circleRep x : ℝ) : AddCircle (1 : ℝ)) = x :=
  AddCircle.coe_equivIco

lemma measurable_circleRep : Measurable circleRep := by
  exact measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable

lemma circleRep_of_mem_Ico {r : ℝ} (hr : r ∈ Ico (0 : ℝ) (0 + 1)) :
    circleRep (r : AddCircle (1 : ℝ)) = r := by
  exact congrArg Subtype.val (AddCircle.equivIco_coe_eq hr)

/-- The index of the unique half-open grid cube containing `x`. -/
noncomputable def gridIndex (n : ℕ) (hn : 0 < n) {d : ℕ} (x : Torus d) :
    Fin d → Fin n := fun i =>
  ⟨⌊(n : ℝ) * circleRep (x i)⌋₊, by
    apply (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg n) (circleRep_nonneg (x i)))).2
    calc
      (n : ℝ) * circleRep (x i) < (n : ℝ) * (0 + 1) :=
        mul_lt_mul_of_pos_left (circleRep_lt_one (x i)) (Nat.cast_pos.mpr hn)
      _ = n := by norm_num⟩

lemma mem_cube_gridIndex (n : ℕ) (hn : 0 < n) {d : ℕ} (x : Torus d) :
    x ∈ cube n (gridIndex n hn x) := by
  intro i
  refine ⟨circleRep (x i), ?_, ?_, (circleRep_coe (x i)).symm⟩
  · apply (div_le_iff₀ (Nat.cast_pos.mpr hn)).2
    simpa [gridIndex, mul_comm] using
      (Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) (circleRep_nonneg (x i))))
  · apply (lt_div_iff₀ (Nat.cast_pos.mpr hn)).2
    simpa [gridIndex, mul_comm] using
      (Nat.lt_floor_add_one ((n : ℝ) * circleRep (x i)))

lemma gridIndex_eq_of_mem_cube (n : ℕ) (hn : 0 < n) {d : ℕ}
    {x : Torus d} {k : Fin d → Fin n} (hx : x ∈ cube n k) :
    gridIndex n hn x = k := by
  funext i
  obtain ⟨r, hkr, hrk, hxr⟩ := hx i
  have hr0 : 0 ≤ r := le_trans (by positivity : (0 : ℝ) ≤ (k i : ℝ) / n) hkr
  have hr1 : r < 0 + 1 := by
    calc
      r < ((k i : ℝ) + 1) / n := hrk
      _ ≤ 0 + 1 := by
        calc
          ((k i : ℝ) + 1) / n ≤ 1 := by
            apply (div_le_one (Nat.cast_pos.mpr hn)).2
            exact_mod_cast Nat.succ_le_iff.mpr (k i).isLt
          _ = 0 + 1 := by norm_num
  have hrep : circleRep (x i) = r := by
    rw [hxr]
    exact circleRep_of_mem_Ico ⟨hr0, hr1⟩
  apply Fin.ext
  change ⌊(n : ℝ) * circleRep (x i)⌋₊ = k i
  rw [hrep]
  apply Nat.floor_eq_on_Ico
  constructor
  · rw [div_le_iff₀ (Nat.cast_pos.mpr hn)] at hkr
    simpa [mul_comm] using hkr
  · rw [lt_div_iff₀ (Nat.cast_pos.mpr hn)] at hrk
    simpa [mul_comm] using hrk

lemma mem_cube_iff_gridIndex_eq (n : ℕ) (hn : 0 < n) {d : ℕ}
    {x : Torus d} {k : Fin d → Fin n} :
    x ∈ cube n k ↔ gridIndex n hn x = k := by
  constructor
  · exact gridIndex_eq_of_mem_cube n hn
  · rintro rfl
    exact mem_cube_gridIndex n hn x

lemma measurableSet_cube (n : ℕ) (hn : 0 < n) {d : ℕ} (k : Fin d → Fin n) :
    MeasurableSet (cube n k) := by
  have hf (i : Fin d) :
      Measurable (fun x : Torus d => ⌊(n : ℝ) * circleRep (x i)⌋₊) :=
    (measurable_const.mul
      (measurable_circleRep.comp (measurable_pi_apply i))).nat_floor
  have hcube : cube n k = ⋂ i : Fin d,
      (fun x : Torus d => ⌊(n : ℝ) * circleRep (x i)⌋₊) ⁻¹' {(k i).val} := by
    ext x
    rw [mem_cube_iff_gridIndex_eq n hn]
    simp only [mem_iInter, mem_preimage, mem_singleton_iff]
    constructor
    · intro hx i
      exact congrArg Fin.val (congrFun hx i)
    · intro hx
      funext i
      exact Fin.ext (hx i)
  rw [hcube]
  exact MeasurableSet.iInter fun i => (measurableSet_singleton (k i).val).preimage (hf i)

lemma measurable_gridIndex (n : ℕ) (hn : 0 < n) {d : ℕ} :
    Measurable (gridIndex n hn : Torus d → (Fin d → Fin n)) := by
  apply measurable_to_countable'
  intro k
  have hpre : (gridIndex n hn : Torus d → (Fin d → Fin n)) ⁻¹' {k} = cube n k := by
    ext x
    simpa only [mem_preimage, mem_singleton_iff] using
      (mem_cube_iff_gridIndex_eq n hn (x := x) (k := k)).symm
  rw [hpre]
  exact measurableSet_cube n hn k

lemma pairwise_disjoint_cube (n : ℕ) (hn : 0 < n) {d : ℕ} :
    Pairwise fun k l : Fin d → Fin n => Disjoint (cube n k) (cube n l) := by
  intro k l hkl
  rw [Set.disjoint_left]
  intro x hxk hxl
  apply hkl
  exact (gridIndex_eq_of_mem_cube n hn hxk).symm.trans
    (gridIndex_eq_of_mem_cube n hn hxl)

lemma iUnion_cube (n : ℕ) (hn : 0 < n) {d : ℕ} :
    (⋃ k : Fin d → Fin n, cube n k) = (Set.univ : Set (Torus d)) := by
  ext x
  simp only [mem_iUnion, mem_univ, iff_true]
  exact ⟨gridIndex n hn x, mem_cube_gridIndex n hn x⟩

/-- The real displacement which translates the `k`th grid interval to the `l`th one. -/
noncomputable def realGridShift (n : ℕ) {d : ℕ} (k l : Fin d → Fin n) (i : Fin d) : ℝ :=
  (((l i : ℤ) - (k i : ℤ) : ℤ) : ℝ) / (n : ℝ)

/-- Coordinatewise translation carrying grid cube `k` to grid cube `l`. -/
noncomputable def gridTranslate (n : ℕ) {d : ℕ} (k l : Fin d → Fin n) (x : Torus d) :
    Torus d := fun i => x i + (realGridShift n k l i : AddCircle (1 : ℝ))

lemma realGridShift_reverse (n : ℕ) {d : ℕ} (k l : Fin d → Fin n) (i : Fin d) :
    realGridShift n l k i = -realGridShift n k l i := by
  simp only [realGridShift]
  push_cast
  ring

lemma gridTranslate_reverse (n : ℕ) {d : ℕ} (k l : Fin d → Fin n) (x : Torus d) :
    gridTranslate n l k (gridTranslate n k l x) = x := by
  funext i
  change (x i + (realGridShift n k l i : AddCircle (1 : ℝ))) +
      (realGridShift n l k i : AddCircle (1 : ℝ)) = x i
  rw [realGridShift_reverse n k l i]
  rw [AddCircle.coe_neg]
  abel

lemma gridTranslate_mem_cube (n : ℕ) {d : ℕ} {k l : Fin d → Fin n} {x : Torus d}
    (hx : x ∈ cube n k) : gridTranslate n k l x ∈ cube n l := by
  intro i
  obtain ⟨r, hkr, hrk, hxr⟩ := hx i
  let s := r + realGridShift n k l i
  have hshift : realGridShift n k l i = (l i : ℝ) / n - (k i : ℝ) / n := by
    simp only [realGridShift]
    push_cast
    ring
  refine ⟨s, ?_, ?_, ?_⟩
  · dsimp only [s]
    rw [hshift]
    linarith
  · dsimp only [s]
    rw [hshift]
    have hk : ((k i : ℝ) + 1) / n = (k i : ℝ) / n + 1 / n := by ring
    have hl : ((l i : ℝ) + 1) / n = (l i : ℝ) / n + 1 / n := by ring
    rw [hk] at hrk
    rw [hl]
    linarith
  · dsimp only [s, gridTranslate]
    rw [hxr, ← AddCircle.coe_add]

lemma gridTranslate_mem_cube_iff (n : ℕ) {d : ℕ} (k l : Fin d → Fin n) (x : Torus d) :
    gridTranslate n k l x ∈ cube n l ↔ x ∈ cube n k := by
  constructor
  · intro hx
    have := gridTranslate_mem_cube (n := n) (k := l) (l := k) hx
    simpa only [gridTranslate_reverse n k l x] using this
  · exact gridTranslate_mem_cube (n := n) (k := k) (l := l)

lemma gridTranslate_preimage_cube (n : ℕ) {d : ℕ} (k l : Fin d → Fin n) :
    gridTranslate n k l ⁻¹' cube n l = cube n k := by
  ext x
  exact gridTranslate_mem_cube_iff n k l x

lemma measure_cube_eq (n : ℕ) {d : ℕ} (k l : Fin d → Fin n) :
    volume (cube n k) = volume (cube n l) := by
  rw [← gridTranslate_preimage_cube n k l]
  exact measure_preimage_add_right (volume : Measure (Torus d))
    (fun i => (realGridShift n k l i : AddCircle (1 : ℝ))) (cube n l)

end Submission.Helpers
