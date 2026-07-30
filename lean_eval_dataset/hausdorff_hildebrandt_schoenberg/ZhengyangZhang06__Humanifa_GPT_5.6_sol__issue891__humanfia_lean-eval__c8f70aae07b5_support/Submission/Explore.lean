import Submission.Helpers

open MeasureTheory

namespace Submission.Helpers

lemma choose_ratio_succ (m N r : ℕ) (hmr : m < r) (hrN : r ≤ N) :
    (r.choose (m + 1) : ℝ) / (N.choose (m + 1) : ℝ) =
      ((r.choose m : ℝ) / (N.choose m : ℝ)) *
        (((r - m : ℕ) : ℝ) / (N - m : ℕ)) := by
  have hmr' : m + 1 ≤ r := by omega
  have hmN' : m + 1 ≤ N := hmr'.trans hrN
  have hCr : (r.choose (m + 1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hmr'
  have hCN : (N.choose (m + 1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hmN'
  have hCrm : (r.choose m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (hmr.le)
  have hCNm : (N.choose m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (hmr.le.trans hrN)
  have hNm : ((N - m : ℕ) : ℝ) ≠ 0 := by
    norm_cast
    omega
  have hrEq : (r.choose (m + 1) : ℝ) * (m + 1 : ℝ) =
      (r.choose m : ℝ) * (r - m : ℕ) := by
    exact_mod_cast Nat.choose_succ_right_eq r m
  have hNEq : (N.choose (m + 1) : ℝ) * (m + 1 : ℝ) =
      (N.choose m : ℝ) * (N - m : ℕ) := by
    exact_mod_cast Nat.choose_succ_right_eq N m
  field_simp
  nlinarith

lemma ratio_sub_bound (m N r : ℕ) (hmr : m < r) (hrN : r ≤ N) :
    |((r - m : ℕ) : ℝ) / (N - m : ℕ) - (r : ℝ) / N| ≤
      (m : ℝ) / (N - m : ℕ) := by
  have hmN : m < N := hmr.trans_le hrN
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNm : (0 : ℝ) < (N - m : ℕ) := by
    exact_mod_cast (show 0 < N - m by omega)
  have hmrle : m ≤ r := hmr.le
  have hmNle : m ≤ N := hmN.le
  have hyx : ((r - m : ℕ) : ℝ) / (N - m : ℕ) ≤ (r : ℝ) / N := by
    rw [div_le_div_iff₀ hNm hN]
    push_cast [Nat.cast_sub hmrle, Nat.cast_sub hmNle]
    have hrNR : (r : ℝ) ≤ N := by exact_mod_cast hrN
    nlinarith
  rw [abs_of_nonpos (sub_nonpos.mpr hyx)]
  rw [neg_sub]
  rw [sub_le_iff_le_add, ← add_div]
  push_cast [Nat.cast_sub hmrle, Nat.cast_sub hmNle]
  rw [show (m : ℝ) + (r - m) = r by ring]
  have hNmR : (0 : ℝ) < N - m := sub_pos.mpr (by exact_mod_cast hmN)
  rw [div_le_div_iff₀ hN hNmR]
  gcongr
  exact sub_le_self _ (Nat.cast_nonneg m)

lemma choose_ratio_error (m N r : ℕ) (hmN : m < N) (hrN : r ≤ N) :
    |(r.choose m : ℝ) / (N.choose m : ℝ) - ((r : ℝ) / N) ^ m| ≤
      (m : ℝ) ^ 2 / (N - m : ℕ) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hmN' : m < N := by omega
      have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      have hden : (0 : ℝ) < (N - (m + 1) : ℕ) := by
        exact_mod_cast (show 0 < N - (m + 1) by omega)
      have hden' : (0 : ℝ) < (N - m : ℕ) := by
        exact_mod_cast (show 0 < N - m by omega)
      have hx0 : (0 : ℝ) ≤ (r : ℝ) / N := div_nonneg (by positivity) hN.le
      have hx1 : (r : ℝ) / N ≤ 1 := by
        rw [div_le_one hN]
        exact_mod_cast hrN
      by_cases hrm : r ≤ m
      · have hchoose : r.choose (m + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        rw [hchoose, Nat.cast_zero, zero_div, zero_sub, abs_neg]
        rw [abs_of_nonneg (pow_nonneg hx0 _)]
        calc
          ((r : ℝ) / N) ^ (m + 1) = ((r : ℝ) / N) ^ m * ((r : ℝ) / N) :=
            pow_succ _ _
          _ ≤ 1 * ((r : ℝ) / N) :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ hx0 hx1) hx0
          _ = (r : ℝ) / N := one_mul _
          _ ≤ (m : ℝ) / N := by
            exact (div_le_div_iff_of_pos_right hN).2 (by exact_mod_cast hrm)
          _ ≤ ((m + 1 : ℕ) : ℝ) ^ 2 / (N - (m + 1) : ℕ) := by
            rw [div_le_div_iff₀ hN hden]
            push_cast [Nat.cast_sub (show m + 1 ≤ N by omega)]
            have hmSq : (m : ℝ) ≤ (m + 1) ^ 2 := by nlinarith [sq_nonneg (m : ℝ)]
            calc
              (m : ℝ) * (N - (m + 1)) ≤ (m : ℝ) * N := by
                exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
              _ ≤ (m + 1) ^ 2 * N := by gcongr
      · have hmr : m < r := by omega
        let q : ℝ := (r.choose m : ℝ) / (N.choose m : ℝ)
        let x : ℝ := (r : ℝ) / N
        let y : ℝ := ((r - m : ℕ) : ℝ) / (N - m : ℕ)
        have hy0 : 0 ≤ y := div_nonneg (by positivity) hden'.le
        have hy1 : y ≤ 1 := by
          dsimp [y]
          rw [div_le_one hden']
          exact_mod_cast Nat.sub_le_sub_right hrN m
        have hqy :
            (r.choose (m + 1) : ℝ) / (N.choose (m + 1) : ℝ) = q * y := by
          simpa [q, y] using choose_ratio_succ m N r hmr hrN
        have hi := ih hmN'
        have hratio := ratio_sub_bound m N r hmr hrN
        change |q - x ^ m| ≤ (m : ℝ) ^ 2 / (N - m : ℕ) at hi
        change |y - x| ≤ (m : ℝ) / (N - m : ℕ) at hratio
        rw [hqy, pow_succ]
        change |q * y - x ^ m * x| ≤ _
        calc
          |q * y - x ^ m * x| = |(q - x ^ m) * y + x ^ m * (y - x)| := by
            congr 1
            ring
          _ ≤ |(q - x ^ m) * y| + |x ^ m * (y - x)| := abs_add_le _ _
          _ = |q - x ^ m| * |y| + |x ^ m| * |y - x| := by
            rw [abs_mul, abs_mul]
          _ ≤ ((m : ℝ) ^ 2 / (N - m : ℕ)) * 1 +
              1 * ((m : ℝ) / (N - m : ℕ)) := by
            apply add_le_add
            · exact mul_le_mul hi (by simpa [abs_of_nonneg hy0] using hy1)
                (abs_nonneg _) (by positivity)
            · exact mul_le_mul (by
                  rw [abs_of_nonneg (pow_nonneg hx0 _)]
                  exact pow_le_one₀ hx0 hx1) hratio (abs_nonneg _) zero_le_one
          _ ≤ ((m + 1 : ℕ) : ℝ) ^ 2 / (N - (m + 1) : ℕ) := by
            rw [mul_one, one_mul]
            rw [← add_div]
            rw [div_le_div_iff₀ hden' hden]
            push_cast [Nat.cast_sub (show m ≤ N by omega),
              Nat.cast_sub (show m + 1 ≤ N by omega)]
            nlinarith

lemma abs_prod_sub_prod_le_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : ι → ℝ) (hf : ∀ i, |f i| ≤ 1) (hg : ∀ i, |g i| ≤ 1) :
    |(∏ i, f i) - ∏ i, g i| ≤ ∑ i, |f i - g i| := by
  have habs_prod (s : Finset ι) : |∏ i ∈ s, f i| = ∏ i ∈ s, |f i| := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha, abs_mul, ih]
  have aux (s : Finset ι) (hf : ∀ i ∈ s, |f i| ≤ 1) (hg : ∀ i ∈ s, |g i| ≤ 1) :
      |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤ ∑ i ∈ s, |f i - g i| := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
        have hfp : |∏ i ∈ s, f i| ≤ 1 := by
          rw [habs_prod s]
          apply Finset.prod_le_one
          · intro i hi
            exact abs_nonneg _
          · intro i hi
            exact hf i (Finset.mem_insert_of_mem hi)
        have hga : |g a| ≤ 1 := hg a (Finset.mem_insert_self _ _)
        calc
          |f a * (∏ i ∈ s, f i) - g a * ∏ i ∈ s, g i| =
              |(f a - g a) * (∏ i ∈ s, f i) +
                g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)| := by
            congr 1
            ring
          _ ≤ |(f a - g a) * (∏ i ∈ s, f i)| +
              |g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)| := abs_add_le _ _
          _ = |f a - g a| * |∏ i ∈ s, f i| +
              |g a| * |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| := by
            rw [abs_mul, abs_mul]
          _ ≤ |f a - g a| * 1 + 1 * ∑ i ∈ s, |f i - g i| := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left hfp (abs_nonneg _)
            · exact mul_le_mul hga
                (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
                  (fun i hi => hg i (Finset.mem_insert_of_mem hi)))
                (abs_nonneg _) zero_le_one
          _ = |f a - g a| + ∑ i ∈ s, |f i - g i| := by ring
  simpa using aux Finset.univ (fun i _ => hf i) (fun i _ => hg i)

lemma product_choose_ratio_error {d : ℕ} (m k : Fin d → ℕ) (N : ℕ)
    (hN : (∑ i, m i) < N) (hk : k ≤ fun _ => N) :
    |(∏ i, ((N - k i).choose (m i) : ℝ) / (N.choose (m i) : ℝ)) -
        ∏ i, (((N - k i : ℕ) : ℝ) / N) ^ m i| ≤
      (∑ i, (m i : ℝ) ^ 2) / (N - ∑ i, m i : ℕ) := by
  classical
  let M : ℕ := ∑ i, m i
  have hmiM (i : Fin d) : m i ≤ M := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)
  have hmiN (i : Fin d) : m i < N := (hmiM i).trans_lt hN
  have hkiN (i : Fin d) : k i ≤ N := hk i
  have hrN (i : Fin d) : N - k i ≤ N := Nat.sub_le _ _
  have hden (i : Fin d) : (0 : ℝ) < N.choose (m i) := by
    exact_mod_cast Nat.choose_pos (hmiN i).le
  have hf (i : Fin d) :
      |((N - k i).choose (m i) : ℝ) / (N.choose (m i) : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg (by positivity) (hden i).le), div_le_one (hden i)]
    exact_mod_cast Nat.choose_le_choose (m i) (hrN i)
  have hx0 (i : Fin d) : (0 : ℝ) ≤ ((N - k i : ℕ) : ℝ) / N := by positivity
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hx1 (i : Fin d) : ((N - k i : ℕ) : ℝ) / N ≤ 1 := by
    rw [div_le_one hNp]
    exact_mod_cast hrN i
  calc
    |(∏ i, ((N - k i).choose (m i) : ℝ) / (N.choose (m i) : ℝ)) -
        ∏ i, (((N - k i : ℕ) : ℝ) / N) ^ m i| ≤
        ∑ i, |((N - k i).choose (m i) : ℝ) / (N.choose (m i) : ℝ) -
          (((N - k i : ℕ) : ℝ) / N) ^ m i| := by
      exact abs_prod_sub_prod_le_sum _ _ hf fun i => by
        rw [abs_of_nonneg (pow_nonneg (hx0 i) _)]
        exact pow_le_one₀ (hx0 i) (hx1 i)
    _ ≤ ∑ i, (m i : ℝ) ^ 2 / (N - m i : ℕ) := by
      apply Finset.sum_le_sum
      intro i _
      exact choose_ratio_error (m i) N (N - k i) (hmiN i) (hrN i)
    _ ≤ ∑ i, (m i : ℝ) ^ 2 / (N - M : ℕ) := by
      apply Finset.sum_le_sum
      intro i _
      have hNM : (0 : ℝ) < (N - M : ℕ) := by
        exact_mod_cast (show 0 < N - M by omega)
      have hdenle : (N - M : ℕ) ≤ N - m i := Nat.sub_le_sub_left (hmiM i) N
      exact div_le_div_of_nonneg_left (by positivity) hNM (by exact_mod_cast hdenle)
    _ = (∑ i, (m i : ℝ) ^ 2) / (N - ∑ i, m i : ℕ) := by
      rw [Finset.sum_div]

lemma product_choose_ratio_tendsto_zero {d : ℕ} (m : Fin d → ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ k : Fin d → ℕ, k ≤ (fun _ => N) →
      |(∏ i, ((N - k i).choose (m i) : ℝ) / (N.choose (m i) : ℝ)) -
          ∏ i, (((N - k i : ℕ) : ℝ) / N) ^ m i| < ε := by
  let M : ℕ := ∑ i, m i
  let B : ℝ := ∑ i, (m i : ℝ) ^ 2
  have hden : Filter.Tendsto (fun N : ℕ => ((N - M : ℕ) : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp (Filter.tendsto_sub_atTop_nat M)
  have hlim : Filter.Tendsto (fun N : ℕ => B / ((N - M : ℕ) : ℝ))
      Filter.atTop (nhds 0) := hden.const_div_atTop B
  filter_upwards [hlim.eventually (Iio_mem_nhds hε), Filter.eventually_gt_atTop M]
    with N hB hNM
  intro k hk
  exact (product_choose_ratio_error m k N hNM hk).trans_lt (by simpa [B, M] using hB)

open LeanEval.Analysis
open scoped NNReal BigOperators

abbrev CubePoint (d : ℕ) := {x : EuclideanSpace ℝ (Fin d) // x ∈ cube d}

noncomputable instance (d : ℕ) : CompactSpace (CubePoint d) :=
  isCompact_iff_compactSpace.mp (Submission.Helpers.isCompact_cube d)

noncomputable def gridPoint {d : ℕ} (N : ℕ) (k : Fin d → ℕ) : CubePoint d := by
  refine ⟨WithLp.toLp 2 (fun i => ((N - k i : ℕ) : ℝ) / N), ?_⟩
  intro i
  constructor
  · positivity
  · by_cases hN : N = 0
    · subst N
      simp
    · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hN)]
      exact_mod_cast Nat.sub_le N (k i)

noncomputable def posCoeff (x : ℝ) : ℝ≥0 :=
  ⟨(|x| + x) / 2, by nlinarith [neg_abs_le x]⟩

noncomputable def negCoeff (x : ℝ) : ℝ≥0 :=
  ⟨(|x| - x) / 2, by nlinarith [le_abs_self x]⟩

lemma coe_posCoeff_sub_negCoeff (x : ℝ) : (posCoeff x : ℝ) - negCoeff x = x := by
  change (|x| + x) / 2 - (|x| - x) / 2 = x
  ring

lemma coe_posCoeff_le_abs (x : ℝ) : (posCoeff x : ℝ) ≤ |x| := by
  change (|x| + x) / 2 ≤ |x|
  nlinarith [le_abs_self x]

lemma coe_negCoeff_le_abs (x : ℝ) : (negCoeff x : ℝ) ≤ |x| := by
  change (|x| - x) / 2 ≤ |x|
  nlinarith [neg_abs_le x]

noncomputable def finiteDirac {α : Type*} [MeasurableSpace α] (x : α) : FiniteMeasure α :=
  (MeasureTheory.diracProba x).toFiniteMeasure

noncomputable def atomicWeight {d : ℕ} (a : (Fin d → ℕ) → ℝ)
    (N : ℕ) (k : Fin d → ℕ) : ℝ :=
  (multiChoose (fun _ => N) k : ℝ) * diff a k (fun _ => N)

noncomputable def atomicPos {d : ℕ} (a : (Fin d → ℕ) → ℝ) (N : ℕ) :
    FiniteMeasure (CubePoint d) :=
  ∑ k ∈ Finset.Iic (fun _ : Fin d => N),
    posCoeff (atomicWeight a N k) • finiteDirac (gridPoint N k)

noncomputable def atomicNeg {d : ℕ} (a : (Fin d → ℕ) → ℝ) (N : ℕ) :
    FiniteMeasure (CubePoint d) :=
  ∑ k ∈ Finset.Iic (fun _ : Fin d => N),
    negCoeff (atomicWeight a N k) • finiteDirac (gridPoint N k)

lemma finiteDirac_mass {α : Type*} [MeasurableSpace α] (x : α) :
    (finiteDirac x).mass = 1 := by
  exact MeasureTheory.ProbabilityMeasure.mass_toFiniteMeasure _

lemma mass_finset_sum {α ι : Type*} [MeasurableSpace α] (s : Finset ι)
    (μ : ι → FiniteMeasure α) :
    (∑ i ∈ s, μ i).mass = ∑ i ∈ s, (μ i).mass := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, FiniteMeasure.mass]
      change (μ i + ∑ j ∈ s, μ j) Set.univ = _
      rw [FiniteMeasure.coeFn_add, Pi.add_apply]
      change (μ i).mass + (∑ j ∈ s, μ j).mass = _
      rw [ih]

lemma atomicPos_mass {d : ℕ} (a : (Fin d → ℕ) → ℝ) (N : ℕ) :
    (atomicPos a N).mass =
      ∑ k ∈ Finset.Iic (fun _ : Fin d => N), posCoeff (atomicWeight a N k) := by
  rw [atomicPos, mass_finset_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [FiniteMeasure.mass, FiniteMeasure.smul_apply]
  change posCoeff (atomicWeight a N k) * (finiteDirac (gridPoint N k)).mass = _
  rw [finiteDirac_mass, mul_one]

lemma atomicNeg_mass {d : ℕ} (a : (Fin d → ℕ) → ℝ) (N : ℕ) :
    (atomicNeg a N).mass =
      ∑ k ∈ Finset.Iic (fun _ : Fin d => N), negCoeff (atomicWeight a N k) := by
  rw [atomicNeg, mass_finset_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [FiniteMeasure.mass, FiniteMeasure.smul_apply]
  change negCoeff (atomicWeight a N k) * (finiteDirac (gridPoint N k)).mass = _
  rw [finiteDirac_mass, mul_one]

lemma hausdorff_bound_nonneg {d : ℕ} {a : (Fin d → ℕ) → ℝ} {C : ℝ}
    (hC : ∀ n, ∑ k ∈ Finset.Iic n,
      |(multiChoose n k : ℝ) * diff a k n| ≤ C) : 0 ≤ C := by
  refine le_trans ?_ (hC (fun _ => 0))
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma atomicPos_mass_le {d : ℕ} (a : (Fin d → ℕ) → ℝ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ n, ∑ k ∈ Finset.Iic n,
      |(multiChoose n k : ℝ) * diff a k n| ≤ C) (N : ℕ) :
    (atomicPos a N).mass ≤ ⟨C, hC0⟩ := by
  apply NNReal.coe_le_coe.mp
  rw [atomicPos_mass, NNReal.coe_sum]
  calc
    (∑ k ∈ Finset.Iic (fun _ : Fin d => N), (posCoeff (atomicWeight a N k) : ℝ)) ≤
        ∑ k ∈ Finset.Iic (fun _ : Fin d => N), |atomicWeight a N k| := by
      apply Finset.sum_le_sum
      intro k _
      exact coe_posCoeff_le_abs _
    _ ≤ C := hC (fun _ => N)

lemma atomicNeg_mass_le {d : ℕ} (a : (Fin d → ℕ) → ℝ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ n, ∑ k ∈ Finset.Iic n,
      |(multiChoose n k : ℝ) * diff a k n| ≤ C) (N : ℕ) :
    (atomicNeg a N).mass ≤ ⟨C, hC0⟩ := by
  apply NNReal.coe_le_coe.mp
  rw [atomicNeg_mass, NNReal.coe_sum]
  calc
    (∑ k ∈ Finset.Iic (fun _ : Fin d => N), (negCoeff (atomicWeight a N k) : ℝ)) ≤
        ∑ k ∈ Finset.Iic (fun _ : Fin d => N), |atomicWeight a N k| := by
      apply Finset.sum_le_sum
      intro k _
      exact coe_negCoeff_le_abs _
    _ ≤ C := hC (fun _ => N)

lemma exists_atomic_tendsto_ultrafilter {d : ℕ} (a : (Fin d → ℕ) → ℝ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ n, ∑ k ∈ Finset.Iic n,
      |(multiChoose n k : ℝ) * diff a k n| ≤ C) :
    ∃ μ ν : FiniteMeasure (CubePoint d), ∃ U : Ultrafilter ℕ, (U : Filter ℕ) ≤ Filter.atTop ∧
      Filter.Tendsto (fun n => (atomicPos a n, atomicNeg a n)) U (nhds (μ, ν)) := by
  let S : Set (FiniteMeasure (CubePoint d)) := {μ | μ.mass ≤ ⟨C, hC0⟩}
  have hS : IsCompact S :=
    isCompact_setOf_finiteMeasure_le_of_compactSpace _ ⟨C, hC0⟩
  have hpair : IsCompact (S ×ˢ S) := hS.prod hS
  have hmem (N : ℕ) : (atomicPos a N, atomicNeg a N) ∈ S ×ˢ S :=
    ⟨atomicPos_mass_le a hC0 hC N, atomicNeg_mass_le a hC0 hC N⟩
  obtain ⟨p, _hp, hp⟩ :=
    hpair.exists_mapClusterPt_of_frequently (l := Filter.atTop)
      (f := fun n => (atomicPos a n, atomicNeg a n)) (Filter.Frequently.of_forall hmem)
  obtain ⟨U, hU, hlim⟩ := mapClusterPt_iff_ultrafilter.mp hp
  exact ⟨p.1, p.2, U, hU, hlim⟩

noncomputable def cubeMonomialBCF {d : ℕ} (m : Fin d → ℕ) :
    BoundedContinuousFunction (CubePoint d) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => monomial m x.1, (Submission.Helpers.continuous_monomial m).comp continuous_subtype_val⟩

lemma cubeMonomialBCF_gridPoint {d : ℕ} (m k : Fin d → ℕ) (N : ℕ) :
    cubeMonomialBCF m (gridPoint N k) =
      ∏ i, (((N - k i : ℕ) : ℝ) / N) ^ m i := by
  rfl

lemma integral_finiteDirac {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (f : α → ℝ) (x : α) :
    ∫ y, f y ∂(finiteDirac x : Measure α) = f x := by
  exact MeasureTheory.integral_dirac f x

lemma integral_atomicPos {d : ℕ} (a : (Fin d → ℕ) → ℝ) (m : Fin d → ℕ) (N : ℕ) :
    ∫ x, cubeMonomialBCF m x ∂(atomicPos a N : Measure (CubePoint d)) =
      ∑ k ∈ Finset.Iic (fun _ : Fin d => N),
        (posCoeff (atomicWeight a N k) : ℝ) * cubeMonomialBCF m (gridPoint N k) := by
  rw [atomicPos, FiniteMeasure.toMeasure_sum]
  rw [MeasureTheory.integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro k _
    rw [FiniteMeasure.toMeasure_smul, MeasureTheory.integral_smul_nnreal_measure]
    change (posCoeff (atomicWeight a N k) : ℝ) *
        (∫ x, cubeMonomialBCF m x ∂(finiteDirac (gridPoint N k) : Measure (CubePoint d))) = _
    rw [integral_finiteDirac]
  · intro k _
    exact (cubeMonomialBCF m).integrable
      (μ := (posCoeff (atomicWeight a N k) • finiteDirac (gridPoint N k) :
        FiniteMeasure (CubePoint d)))

lemma integral_atomicNeg {d : ℕ} (a : (Fin d → ℕ) → ℝ) (m : Fin d → ℕ) (N : ℕ) :
    ∫ x, cubeMonomialBCF m x ∂(atomicNeg a N : Measure (CubePoint d)) =
      ∑ k ∈ Finset.Iic (fun _ : Fin d => N),
        (negCoeff (atomicWeight a N k) : ℝ) * cubeMonomialBCF m (gridPoint N k) := by
  rw [atomicNeg, FiniteMeasure.toMeasure_sum]
  rw [MeasureTheory.integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro k _
    rw [FiniteMeasure.toMeasure_smul, MeasureTheory.integral_smul_nnreal_measure]
    change (negCoeff (atomicWeight a N k) : ℝ) *
        (∫ x, cubeMonomialBCF m x ∂(finiteDirac (gridPoint N k) : Measure (CubePoint d))) = _
    rw [integral_finiteDirac]
  · intro k _
    exact (cubeMonomialBCF m).integrable
      (μ := (negCoeff (atomicWeight a N k) • finiteDirac (gridPoint N k) :
        FiniteMeasure (CubePoint d)))

lemma integral_atomic_sub {d : ℕ} (a : (Fin d → ℕ) → ℝ) (m : Fin d → ℕ) (N : ℕ) :
    (∫ x, cubeMonomialBCF m x ∂(atomicPos a N : Measure (CubePoint d))) -
        ∫ x, cubeMonomialBCF m x ∂(atomicNeg a N : Measure (CubePoint d)) =
      ∑ k ∈ Finset.Iic (fun _ : Fin d => N),
        atomicWeight a N k * ∏ i, (((N - k i : ℕ) : ℝ) / N) ^ m i := by
  rw [integral_atomicPos, integral_atomicNeg, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [cubeMonomialBCF_gridPoint]
  calc
    (posCoeff (atomicWeight a N k) : ℝ) *
          (∏ i, (((N - k i : ℕ) : ℝ) / N) ^ m i) -
        (negCoeff (atomicWeight a N k) : ℝ) *
          ∏ i, (((N - k i : ℕ) : ℝ) / N) ^ m i =
        ((posCoeff (atomicWeight a N k) : ℝ) - negCoeff (atomicWeight a N k)) *
          ∏ i, (((N - k i : ℕ) : ℝ) / N) ^ m i := by ring
    _ = atomicWeight a N k * ∏ i, (((N - k i : ℕ) : ℝ) / N) ^ m i := by
      rw [coe_posCoeff_sub_negCoeff]

lemma multiChoose_pos {d : ℕ} {m n : Fin d → ℕ} (hmn : m ≤ n) :
    0 < multiChoose n m := by
  unfold multiChoose
  exact Finset.prod_pos fun i _ => Nat.choose_pos (hmn i)

lemma bernstein_inversion_normalized {d : ℕ} (a : (Fin d → ℕ) → ℝ)
    {m n : Fin d → ℕ} (hmn : m ≤ n) :
    ∑ k ∈ Finset.Iic n,
        ((multiChoose n k : ℝ) * diff a k n) *
          ((multiChoose (n - k) m : ℝ) / (multiChoose n m : ℝ)) = a m := by
  have hden : (multiChoose n m : ℝ) ≠ 0 := by
    exact_mod_cast (multiChoose_pos hmn).ne'
  calc
    (∑ k ∈ Finset.Iic n,
        ((multiChoose n k : ℝ) * diff a k n) *
          ((multiChoose (n - k) m : ℝ) / (multiChoose n m : ℝ))) =
        (∑ k ∈ Finset.Iic n,
          (multiChoose n k : ℝ) * diff a k n * (multiChoose (n - k) m : ℝ)) /
            (multiChoose n m : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ((multiChoose n m : ℝ) * a m) / (multiChoose n m : ℝ) := by
      rw [Submission.Helpers.bernstein_inversion a hmn]
    _ = a m := by field_simp

lemma constant_multiChoose_ratio {d : ℕ} (N : ℕ) (k m : Fin d → ℕ) :
    (multiChoose ((fun _ : Fin d => N) - k) m : ℝ) /
        (multiChoose (fun _ : Fin d => N) m : ℝ) =
      ∏ i, ((N - k i).choose (m i) : ℝ) / (N.choose (m i) : ℝ) := by
  simp only [multiChoose, Nat.cast_prod, Pi.sub_apply]
  rw [Finset.prod_div_distrib]

lemma atomic_signed_moment_tendsto {d : ℕ} (a : (Fin d → ℕ) → ℝ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ n, ∑ k ∈ Finset.Iic n,
      |(multiChoose n k : ℝ) * diff a k n| ≤ C) (m : Fin d → ℕ) :
    Filter.Tendsto (fun N =>
      (∫ x, cubeMonomialBCF m x ∂(atomicPos a N : Measure (CubePoint d))) -
        ∫ x, cubeMonomialBCF m x ∂(atomicNeg a N : Measure (CubePoint d)))
      Filter.atTop (nhds (a m)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hCp : 0 < C + 1 := by linarith
  have hη : 0 < ε / (C + 1) := div_pos hε hCp
  filter_upwards [product_choose_ratio_tendsto_zero m (ε / (C + 1)) hη,
    Filter.eventually_gt_atTop (∑ i, m i)] with N happrox hNm
  rw [Real.dist_eq, integral_atomic_sub]
  let n : Fin d → ℕ := fun _ => N
  have hmn : m ≤ n := by
    intro i
    exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hNm.le
  have hexact := bernstein_inversion_normalized a hmn
  change |(∑ k ∈ Finset.Iic n, atomicWeight a N k *
      ∏ i, (((N - k i : ℕ) : ℝ) / N) ^ m i) - a m| < ε
  change (∑ k ∈ Finset.Iic n, atomicWeight a N k *
      ((multiChoose (n - k) m : ℝ) / (multiChoose n m : ℝ))) = a m at hexact
  rw [← hexact, ← Finset.sum_sub_distrib]
  calc
    |∑ k ∈ Finset.Iic n,
        (atomicWeight a N k * ∏ i, (((N - k i : ℕ) : ℝ) / N) ^ m i -
          atomicWeight a N k *
            ((multiChoose (n - k) m : ℝ) / (multiChoose n m : ℝ)))| ≤
        ∑ k ∈ Finset.Iic n,
          |atomicWeight a N k * ∏ i, (((N - k i : ℕ) : ℝ) / N) ^ m i -
            atomicWeight a N k *
              ((multiChoose (n - k) m : ℝ) / (multiChoose n m : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ Finset.Iic n, |atomicWeight a N k| *
        |(∏ i, (((N - k i : ℕ) : ℝ) / N) ^ m i) -
          ∏ i, ((N - k i).choose (m i) : ℝ) / (N.choose (m i) : ℝ)| := by
      apply Finset.sum_congr rfl
      intro k _
      rw [constant_multiChoose_ratio]
      rw [← mul_sub, abs_mul]
    _ ≤ ∑ k ∈ Finset.Iic n, |atomicWeight a N k| * (ε / (C + 1)) := by
      apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      rw [abs_sub_comm]
      exact (happrox k (Finset.mem_Iic.mp hk)).le
    _ = (ε / (C + 1)) * ∑ k ∈ Finset.Iic n, |atomicWeight a N k| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ (ε / (C + 1)) * C := by
      exact mul_le_mul_of_nonneg_left (hC n) hη.le
    _ < ε := by
      have hratio : C / (C + 1) < 1 := (div_lt_one hCp).2 (by linarith)
      calc
        (ε / (C + 1)) * C = ε * (C / (C + 1)) := by ring
        _ < ε * 1 := mul_lt_mul_of_pos_left hratio hε
        _ = ε := mul_one _

lemma momentOf_map_cube {d : ℕ} (μ : FiniteMeasure (CubePoint d)) (m : Fin d → ℕ) :
    momentOf (μ.map Subtype.val : Measure (EuclideanSpace ℝ (Fin d))) m =
      ∫ x, cubeMonomialBCF m x ∂(μ : Measure (CubePoint d)) := by
  have hae : ∀ᵐ y ∂(μ.map Subtype.val : Measure (EuclideanSpace ℝ (Fin d))), y ∈ cube d := by
    rw [FiniteMeasure.toMeasure_map]
    apply (MeasureTheory.ae_map_iff continuous_subtype_val.measurable.aemeasurable
      (Submission.Helpers.measurableSet_cube d)).2
    exact Filter.Eventually.of_forall fun x => x.property
  unfold momentOf
  rw [Measure.restrict_eq_self_of_ae_mem hae]
  rw [FiniteMeasure.toMeasure_map]
  exact MeasureTheory.integral_map continuous_subtype_val.measurable.aemeasurable
    (Submission.Helpers.continuous_monomial m).measurable.aestronglyMeasurable

lemma hausdorffBounded_momentConfiguration {d : ℕ} (a : (Fin d → ℕ) → ℝ) :
    HausdorffBounded a → IsMomentConfiguration a := by
  rintro ⟨C, hC⟩
  have hC0 : 0 ≤ C := hausdorff_bound_nonneg hC
  obtain ⟨μ, ν, U, hU, hlim⟩ := exists_atomic_tendsto_ultrafilter a hC0 hC
  let μE : FiniteMeasure (EuclideanSpace ℝ (Fin d)) := μ.map Subtype.val
  let νE : FiniteMeasure (EuclideanSpace ℝ (Fin d)) := ν.map Subtype.val
  refine ⟨μE, νE, inferInstance, inferInstance, fun m => ?_⟩
  rw [show momentOf (μE : Measure (EuclideanSpace ℝ (Fin d))) m =
      ∫ x, cubeMonomialBCF m x ∂(μ : Measure (CubePoint d)) by
        exact momentOf_map_cube μ m,
    show momentOf (νE : Measure (EuclideanSpace ℝ (Fin d))) m =
      ∫ x, cubeMonomialBCF m x ∂(ν : Measure (CubePoint d)) by
        exact momentOf_map_cube ν m]
  have hμlim : Filter.Tendsto (fun N => atomicPos a N) U (nhds μ) := by
    simpa [Function.comp_def] using (continuous_fst.tendsto (μ, ν)).comp hlim
  have hνlim : Filter.Tendsto (fun N => atomicNeg a N) U (nhds ν) := by
    simpa [Function.comp_def] using (continuous_snd.tendsto (μ, ν)).comp hlim
  have hμint := (MeasureTheory.FiniteMeasure.tendsto_iff_forall_integral_tendsto).mp hμlim
    (cubeMonomialBCF m)
  have hνint := (MeasureTheory.FiniteMeasure.tendsto_iff_forall_integral_tendsto).mp hνlim
    (cubeMonomialBCF m)
  have hweak := hμint.sub hνint
  have halgebra := (atomic_signed_moment_tendsto a hC0 hC m).mono_left hU
  exact (tendsto_nhds_unique halgebra hweak)

end Submission.Helpers
