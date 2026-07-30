import Submission.AnalyticComposition

open Filter Function Metric Set

namespace Submission

lemma taylorCoeff_add_formal {f g : ℂ → ℂ} {n : ℕ}
    (hf : ContDiffAt ℂ n f 0) (hg : ContDiffAt ℂ n g 0) :
    taylorCoeff (f + g) n = taylorCoeff f n + taylorCoeff g n := by
  unfold taylorCoeff
  rw [iteratedDeriv_add hf hg]
  ring

lemma taylorCoeff_sub_formal {f g : ℂ → ℂ} {n : ℕ}
    (hf : ContDiffAt ℂ n f 0) (hg : ContDiffAt ℂ n g 0) :
    taylorCoeff (f - g) n = taylorCoeff f n - taylorCoeff g n := by
  unfold taylorCoeff
  rw [iteratedDeriv_sub hf hg]
  ring

noncomputable def canonicalTransition (r omega z : ℂ) : ℂ :=
  z * (r + omega * z) / (1 + r * omega * z)

lemma canonicalTransition_zero (r omega : ℂ) :
    canonicalTransition r omega 0 = 0 := by
  simp [canonicalTransition]

lemma canonicalTransition_analyticAt (r omega : ℂ) :
    AnalyticAt ℂ (canonicalTransition r omega) 0 := by
  unfold canonicalTransition
  apply ((analyticAt_id.mul
    (analyticAt_const.add (analyticAt_const.mul analyticAt_id))).div
      (analyticAt_const.add
        ((analyticAt_const.mul analyticAt_const).mul analyticAt_id)))
  simp

lemma taylorCoeff_inv_one_add_mul (a : ℂ) (n : ℕ) :
    taylorCoeff (fun z : ℂ ↦ (1 + a * z)⁻¹) n = (-a) ^ n := by
  rw [show (fun z : ℂ ↦ (1 + a * z)⁻¹) =
      fun z ↦ (a * z + 1)⁻¹ by funext z; rw [add_comm],
    taylorCoeff, iteratedDeriv_eq_iterate,
    congrFun (iter_deriv_inv_linear n a 1) 0]
  simp only [mul_zero, zero_add, one_zpow, mul_one]
  field_simp [Nat.factorial_ne_zero]
  ring

lemma taylorCoeff_linear_quadratic (r omega : ℂ) (n : ℕ) :
    taylorCoeff (fun z : ℂ ↦ r * z + omega * z ^ 2) n =
      (if n = 1 then r else 0) + if n = 2 then omega else 0 := by
  rw [show (fun z : ℂ ↦ r * z + omega * z ^ 2) =
      (fun z ↦ r * z) + fun z ↦ omega * z ^ 2 by rfl]
  rw [taylorCoeff_add_formal (by fun_prop) (by fun_prop),
    taylorCoeff_const_mul_formal,
    taylorCoeff_const_mul_formal, taylorCoeff_power_monomial]
  have hid := taylorCoeff_power_monomial 1 n
  simp only [pow_one] at hid
  rw [hid]
  split_ifs <;> simp_all

lemma taylorCoeff_canonicalTransition (r omega : ℂ) (n : ℕ) :
    taylorCoeff (canonicalTransition r omega) n =
      canonicalTransitionCoeff r omega n := by
  have hfun : canonicalTransition r omega =
      (fun z : ℂ ↦ r * z + omega * z ^ 2) *
        fun z ↦ (1 + (r * omega) * z)⁻¹ := by
    funext z
    simp only [Pi.mul_apply]
    unfold canonicalTransition
    rw [div_eq_mul_inv]
    ring
  rw [hfun]
  have hnum (m : ℕ) :
      ContDiffAt ℂ m (fun z : ℂ ↦ r * z + omega * z ^ 2) 0 := by
    fun_prop
  have hden : AnalyticAt ℂ (fun z : ℂ ↦ (1 + r * omega * z)⁻¹) 0 := by
    apply (analyticAt_const.add
      ((analyticAt_const.mul analyticAt_const).mul analyticAt_id)).inv
    simp
  rcases n with _ | _ | n
  · rw [taylorCoeff_mul (hnum 0) hden.contDiffAt]
    simp [taylorCoeff_linear_quadratic,
      taylorCoeff_inv_one_add_mul, canonicalTransitionCoeff]
  · rw [taylorCoeff_mul (hnum 1) hden.contDiffAt]
    simp [Finset.sum_range_succ, taylorCoeff_linear_quadratic,
      taylorCoeff_inv_one_add_mul, canonicalTransitionCoeff]
  · rw [taylorCoeff_mul (hnum (n + 2)) hden.contDiffAt]
    rw [← Finset.sum_subset (s₁ := {1, 2}) (s₂ := Finset.range (n + 3))
      (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> simp) (by
        intro x hx hnot
        have hx1 : x ≠ 1 := by
          intro h
          exact hnot (by simp [h])
        have hx2 : x ≠ 2 := by
          intro h
          exact hnot (by simp [h])
        rw [taylorCoeff_linear_quadratic]
        simp [hx1, hx2])]
    rw [Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2)]
    simp [taylorCoeff_linear_quadratic, taylorCoeff_inv_one_add_mul]
    rw [canonicalTransitionCoeff]
    ring_nf

noncomputable def canonicalUpdatedLog
    (L : ℂ → ℂ) (r omega z : ℂ) : ℂ :=
  L (canonicalTransition r omega z) +
    Complex.log (1 + omega / r * z) -
      Complex.log (1 + r * omega * z)

lemma canonicalUpdatedLog_analyticAt
    {L : ℂ → ℂ} (hL : AnalyticAt ℂ L 0)
    {r omega : ℂ} (_hr : r ≠ 0) :
    AnalyticAt ℂ (canonicalUpdatedLog L r omega) 0 := by
  unfold canonicalUpdatedLog
  have hcomp := hL.comp_of_eq (canonicalTransition_analyticAt r omega)
    (canonicalTransition_zero r omega)
  have hlog₁ : AnalyticAt ℂ (fun z ↦ Complex.log (1 + omega / r * z)) 0 := by
    apply (by fun_prop : AnalyticAt ℂ (fun z ↦ 1 + omega / r * z) 0).clog
    simp
  have hlog₂ : AnalyticAt ℂ (fun z ↦ Complex.log (1 + r * omega * z)) 0 := by
    apply (by fun_prop : AnalyticAt ℂ (fun z ↦ 1 + r * omega * z) 0).clog
    simp
  exact (hcomp.add hlog₁).sub hlog₂

lemma canonicalUpdatedLog_zero
    {L : ℂ → ℂ} (hL0 : L 0 = 0) {r omega : ℂ} :
    canonicalUpdatedLog L r omega 0 = 0 := by
  simp [canonicalUpdatedLog, canonicalTransition_zero, hL0]

lemma seriesPowCoeff_scaled_unit (a : ℂ) (k n : ℕ) :
    seriesPowCoeff (fun d ↦ a * seriesUnitCoeff d) k n =
      if n = k then a ^ k else 0 := by
  induction k generalizing n with
  | zero => simp [seriesPowCoeff]
  | succ k ih =>
      rw [seriesPowCoeff, seriesMulCoeff]
      simp_rw [ih]
      by_cases hnk : n = k + 1
      · subst n
        rw [Finset.sum_eq_single 1]
        · simp [seriesUnitCoeff, pow_succ']
        · intro j hj hj1
          simp [seriesUnitCoeff, hj1]
        · exact fun hnot ↦ (hnot (by simp)).elim
      · rw [Finset.sum_eq_zero]
        · simp [hnk]
        · intro j hj
          by_cases hj1 : j = 1
          · subst j
            have hnpos : 0 < n := by
              have := Finset.mem_range.mp hj
              omega
            have hne : n - 1 ≠ k := by omega
            simp [seriesUnitCoeff, hne]
          · simp [seriesUnitCoeff, hj1]

lemma taylorCoeff_linear (a : ℂ) (n : ℕ) :
    taylorCoeff (fun z : ℂ ↦ a * z) n =
      a * seriesUnitCoeff n := by
  rw [show (fun z : ℂ ↦ a * z) = fun z ↦ a * z ^ 1 by
    funext z; simp]
  rw [taylorCoeff_const_mul_formal, taylorCoeff_power_monomial]
  rcases n with _ | _ | n <;> simp [seriesUnitCoeff]

lemma taylorCoeff_log_one_add (n : ℕ) :
    taylorCoeff (fun z : ℂ ↦ Complex.log (1 + z)) n =
      if n = 0 then 0 else -(-1 : ℂ) ^ n / n := by
  rcases n with _ | n
  · simp [taylorCoeff]
  · rw [if_neg (Nat.succ_ne_zero n)]
    rw [taylorCoeff]
    have hshift := congrFun (iteratedDeriv_comp_add_const (n + 1) Complex.log 1) 0
    simp only [zero_add] at hshift
    rw [show (fun z : ℂ ↦ Complex.log (1 + z)) =
      (fun z ↦ Complex.log (z + 1)) by funext z; rw [add_comm], hshift,
      iteratedDeriv_succ_log Complex.one_mem_slitPlane,
      Nat.factorial_succ]
    simp only [one_zpow]
    push_cast
    field_simp [Nat.factorial_ne_zero]
    ring

lemma taylorCoeff_log_one_add_mul (a : ℂ) (n : ℕ) :
    taylorCoeff (fun z : ℂ ↦ Complex.log (1 + a * z)) n =
      if n = 0 then 0 else -(-1 : ℂ) ^ n * a ^ n / n := by
  let g : ℂ → ℂ := fun w ↦ Complex.log (1 + w)
  let q : ℂ → ℂ := fun z ↦ a * z
  have hg : AnalyticAt ℂ g 0 := by
    dsimp only [g]
    apply (by fun_prop : AnalyticAt ℂ (fun w : ℂ ↦ 1 + w) 0).clog
    simp
  have hq : AnalyticAt ℂ q 0 := by
    dsimp only [q]
    fun_prop
  have hq0 : q 0 = 0 := by simp [q]
  rw [show (fun z : ℂ ↦ Complex.log (1 + a * z)) = g ∘ q by rfl,
    taylorCoeff_comp_eq_sum_seriesPowCoeff hg hq hq0]
  have hqcoeff : taylorCoeff q = fun d ↦ a * seriesUnitCoeff d := by
    funext d
    exact taylorCoeff_linear a d
  have hgcoeff : taylorCoeff g =
      fun d : ℕ ↦ if d = 0 then 0 else -(-1 : ℂ) ^ d / d := by
    funext d
    exact taylorCoeff_log_one_add d
  rw [hqcoeff, hgcoeff]
  simp_rw [seriesPowCoeff_scaled_unit]
  rw [Finset.sum_eq_single n]
  · by_cases hn : n = 0
    · simp [hn]
    · simp [hn]
      ring
  · intro k hk hkn
    simp [Ne.symm hkn]
  · exact fun hnot ↦ (hnot (by simp)).elim

lemma logarithmicCoeff_canonicalUpdatedLog
    {L : ℂ → ℂ} (hL : AnalyticAt ℂ L 0)
    {r omega : ℂ} (n : ℕ) :
    logarithmicCoeff (canonicalUpdatedLog L r omega) n =
      canonicalLoewnerCoeff (logarithmicCoeff L) r omega n := by
  unfold logarithmicCoeff canonicalUpdatedLog canonicalLoewnerCoeff
  rw [show (fun z ↦
      L (canonicalTransition r omega z) + Complex.log (1 + omega / r * z) -
        Complex.log (1 + r * omega * z)) =
      (L ∘ canonicalTransition r omega) +
        (fun z ↦ Complex.log (1 + omega / r * z)) -
          (fun z ↦ Complex.log (1 + r * omega * z)) by rfl]
  have hcomp : AnalyticAt ℂ (L ∘ canonicalTransition r omega) 0 :=
    hL.comp_of_eq (canonicalTransition_analyticAt r omega)
      (canonicalTransition_zero r omega)
  have hlog₁ : AnalyticAt ℂ
      (fun z ↦ Complex.log (1 + omega / r * z)) 0 := by
    apply (by fun_prop : AnalyticAt ℂ (fun z ↦ 1 + omega / r * z) 0).clog
    simp
  have hlog₂ : AnalyticAt ℂ
      (fun z ↦ Complex.log (1 + r * omega * z)) 0 := by
    apply (by fun_prop : AnalyticAt ℂ (fun z ↦ 1 + r * omega * z) 0).clog
    simp
  have hsum : ContDiffAt ℂ n
      ((L ∘ canonicalTransition r omega) +
        fun z ↦ Complex.log (1 + omega / r * z)) 0 := by
    exact hcomp.contDiffAt.add hlog₁.contDiffAt
  rw [taylorCoeff_sub_formal hsum hlog₂.contDiffAt,
    taylorCoeff_add_formal hcomp.contDiffAt hlog₁.contDiffAt,
    taylorCoeff_comp_eq_sum_seriesPowCoeff hL
      (canonicalTransition_analyticAt r omega)
      (canonicalTransition_zero r omega),
    taylorCoeff_log_one_add_mul, taylorCoeff_log_one_add_mul]
  have htrans : taylorCoeff (canonicalTransition r omega) =
      canonicalTransitionCoeff r omega := by
    funext d
    exact taylorCoeff_canonicalTransition r omega d
  rw [htrans]
  let S : ℂ := ∑ k ∈ Finset.range (n + 1),
    taylorCoeff L k * seriesPowCoeff (canonicalTransitionCoeff r omega) k n
  let A : ℂ := if n = 0 then 0 else -(-1 : ℂ) ^ n * (omega / r) ^ n / n
  let B : ℂ := if n = 0 then 0 else -(-1 : ℂ) ^ n * (r * omega) ^ n / n
  change (S + A - B) / 2 =
    (∑ k ∈ Finset.range (n + 1),
      (taylorCoeff L k / 2) *
        seriesPowCoeff (canonicalTransitionCoeff r omega) k n) +
      canonicalLogFactorCoeff r omega n
  rw [show (S + A - B) / 2 = S / 2 + (A - B) / 2 by ring]
  have hS : S / 2 = ∑ k ∈ Finset.range (n + 1),
      (taylorCoeff L k / 2) *
        seriesPowCoeff (canonicalTransitionCoeff r omega) k n := by
    dsimp only [S]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hS]
  apply congrArg₂ (fun x y : ℂ ↦ x + y) rfl
  dsimp only [A, B]
  rcases n with _ | n
  · simp [canonicalLogFactorCoeff]
  · simp only [Nat.succ_ne_zero, if_false, canonicalLogFactorCoeff]
    have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n
    have hrpow : (omega / r) ^ (n + 1) =
        omega ^ (n + 1) * r⁻¹ ^ (n + 1) := by
      rw [div_pow, inv_pow]
      ring
    rw [hrpow, mul_pow]
    field_simp [hn]
    ring

end Submission
