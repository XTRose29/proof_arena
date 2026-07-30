import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.GroupTheory.Perm.Centralizer
import Submission.Milin

namespace Submission

open Equiv
open Metric

noncomputable def orderedExpTerm (a : ℕ → ℂ) {n : ℕ}
    (c : OrderedFinpartition n) : ℂ :=
  (∏ j, ((c.partSize j).factorial : ℂ) * a (c.partSize j)) / n.factorial

noncomputable def orderedKoebeWeight {n : ℕ} (c : OrderedFinpartition n) : ℝ :=
  (∏ j, (((c.partSize j - 1).factorial : ℕ) : ℝ)) / n.factorial

lemma orderedFinpartition_sum_partSize {n : ℕ} (c : OrderedFinpartition n) :
    ∑ j, c.partSize j = n := by
  calc
    ∑ j, c.partSize j =
        Fintype.card ((j : Fin c.length) × Fin (c.partSize j)) := by simp
    _ = Fintype.card (Fin n) := Fintype.card_congr c.equivSigma
    _ = n := Fintype.card_fin n

lemma orderedKoebeWeight_pos {n : ℕ} (c : OrderedFinpartition n) :
    0 < orderedKoebeWeight c := by
  rw [orderedKoebeWeight]
  positivity

lemma orderedKoebeWeight_extendLeft {n : ℕ} (c : OrderedFinpartition n) :
    orderedKoebeWeight c.extendLeft = orderedKoebeWeight c / (n + 1) := by
  have hprod :
      (∏ j : Fin c.extendLeft.length,
          ((((c.extendLeft.partSize j - 1).factorial : ℕ) : ℝ))) =
        ∏ j : Fin c.length, ((((c.partSize j - 1).factorial : ℕ) : ℝ)) := by
    change (∏ j : Fin (c.length + 1),
        ((Nat.factorial
          ((Fin.cons (α := fun _ : Fin (c.length + 1) ↦ ℕ) 1
            (fun i ↦ c.partSize i)) j - 1) : ℕ) : ℝ)) = _
    rw [Fin.prod_univ_succ]
    simp
  rw [orderedKoebeWeight, orderedKoebeWeight]
  rw [hprod, Nat.factorial_succ]
  push_cast
  field_simp [Nat.factorial_ne_zero]

lemma orderedKoebeWeight_extendMiddle {n : ℕ} (c : OrderedFinpartition n)
    (k : Fin c.length) :
    orderedKoebeWeight (c.extendMiddle k) =
      (c.partSize k : ℝ) / (n + 1) * orderedKoebeWeight c := by
  have hprod :
      (∏ j : Fin (c.extendMiddle k).length,
          ((((c.extendMiddle k).partSize j - 1).factorial : ℕ) : ℝ)) =
        (c.partSize k : ℝ) *
          ∏ j : Fin c.length, ((((c.partSize j - 1).factorial : ℕ) : ℝ)) := by
    let q : Fin c.length → ℝ := fun j ↦
      (((c.partSize j - 1).factorial : ℕ) : ℝ)
    let q' : Fin c.length → ℝ := fun j ↦
      ((((Function.update c.partSize k (c.partSize k + 1)) j - 1).factorial : ℕ) : ℝ)
    change (∏ j, q' j) = (c.partSize k : ℝ) * ∏ j, q j
    have hqk : q' k = (c.partSize k : ℝ) * q k := by
      dsimp [q', q]
      simp only [Function.update_self]
      rw [show c.partSize k + 1 - 1 = c.partSize k by omega]
      exact_mod_cast (Nat.mul_factorial_pred (c.partSize_pos k).ne').symm
    have hrest :
        ∏ j ∈ (Finset.univ : Finset (Fin c.length)).erase k, q' j =
          ∏ j ∈ (Finset.univ : Finset (Fin c.length)).erase k, q j := by
      apply Finset.prod_congr rfl
      intro j hj
      have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
      simp [q', q, hjk]
    calc
      (∏ j, q' j) = q' k *
          ∏ j ∈ (Finset.univ : Finset (Fin c.length)).erase k, q' j :=
        (Finset.mul_prod_erase Finset.univ q' (Finset.mem_univ k)).symm
      _ = ((c.partSize k : ℝ) * q k) *
          ∏ j ∈ (Finset.univ : Finset (Fin c.length)).erase k, q j := by
        rw [hqk, hrest]
      _ = (c.partSize k : ℝ) *
          (q k * ∏ j ∈ (Finset.univ : Finset (Fin c.length)).erase k, q j) := by
        ring
      _ = (c.partSize k : ℝ) * ∏ j, q j := by
        rw [Finset.mul_prod_erase Finset.univ q (Finset.mem_univ k)]
  rw [orderedKoebeWeight, orderedKoebeWeight, hprod, Nat.factorial_succ]
  push_cast
  field_simp [Nat.factorial_ne_zero]

lemma orderedKoebeWeight_sum_extensions {n : ℕ} (c : OrderedFinpartition n) :
    ∑ o : Option (Fin c.length), orderedKoebeWeight (c.extend o) =
      orderedKoebeWeight c := by
  have hsum : ∑ k : Fin c.length, (c.partSize k : ℝ) = n := by
    exact_mod_cast orderedFinpartition_sum_partSize c
  rw [Fintype.sum_option]
  simp only [OrderedFinpartition.extend_none, OrderedFinpartition.extend_some,
    orderedKoebeWeight_extendLeft, orderedKoebeWeight_extendMiddle]
  rw [← Finset.sum_mul, ← Finset.sum_div, hsum]
  field_simp
  ring

lemma orderedKoebeWeight_sum (n : ℕ) :
    ∑ c : OrderedFinpartition n, orderedKoebeWeight c = 1 := by
  induction n with
  | zero => simp [orderedKoebeWeight]
  | succ n ih =>
      rw [← (OrderedFinpartition.extendEquiv n).sum_comp, Fintype.sum_sigma]
      simpa only [OrderedFinpartition.extendEquiv_apply,
        orderedKoebeWeight_sum_extensions] using ih

lemma iteratedDeriv_div_two_eq_factorial_mul_logarithmicCoeff
    (L : ℂ → ℂ) (n : ℕ) :
    iteratedDeriv n (fun z => L z / (2 : ℂ)) 0 =
      (n.factorial : ℂ) * logarithmicCoeff L n := by
  have hcoeff := taylorCoeff_div_two L n
  rw [taylorCoeff] at hcoeff
  calc
    iteratedDeriv n (fun z => L z / (2 : ℂ)) 0 =
        (iteratedDeriv n (fun z => L z / (2 : ℂ)) 0 / n.factorial) * n.factorial := by
      exact (div_mul_cancel₀ _ (mod_cast n.factorial_ne_zero)).symm
    _ = logarithmicCoeff L n * n.factorial := by rw [hcoeff]
    _ = (n.factorial : ℂ) * logarithmicCoeff L n := by ring

lemma taylorCoeff_halfExp_eq_sum_orderedExpTerm {L : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hL : DifferentiableOn ℂ L (ball 0 R)) (hL0 : L 0 = 0)
    (n : ℕ) :
    taylorCoeff (halfExp L) n =
      ∑ c : OrderedFinpartition n, orderedExpTerm (logarithmicCoeff L) c := by
  let u : ℂ → ℂ := fun z => L z / (2 : ℂ)
  have hzero : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hu : ContDiffAt ℂ n u 0 :=
    ((hL.div_const (2 : ℂ)).contDiffOn isOpen_ball).contDiffAt
      (isOpen_ball.mem_nhds hzero)
  have hfa := iteratedDeriv_comp_eq_sum_orderedFinpartition
    (i := n) (x := (0 : ℂ))
    (g := Complex.exp) (f := u) Complex.contDiff_exp.contDiffAt hu (by simp)
  change iteratedDeriv n (halfExp L) 0 / n.factorial = _
  change iteratedDeriv n (Complex.exp ∘ u) 0 / n.factorial = _
  rw [hfa, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _
  have hexp : iteratedDeriv c.length Complex.exp (u 0) = 1 := by
    rw [show u 0 = 0 by simp [u, hL0], iteratedDeriv_eq_iterate, Complex.iter_deriv_exp]
    simp
  rw [orderedExpTerm, hexp, one_mul]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  exact iteratedDeriv_div_two_eq_factorial_mul_logarithmicCoeff L (c.partSize j)

lemma iteratedDeriv_eq_factorial_mul_taylorCoeff (u : ℂ → ℂ) (n : ℕ) :
    iteratedDeriv n u 0 = (n.factorial : ℂ) * taylorCoeff u n := by
  rw [taylorCoeff]
  field_simp [Nat.factorial_ne_zero]

lemma taylorCoeff_exp_eq_sum_orderedExpTerm {u : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hu : DifferentiableOn ℂ u (ball 0 R)) (hu0 : u 0 = 0)
    (n : ℕ) :
    taylorCoeff (fun z ↦ Complex.exp (u z)) n =
      ∑ c : OrderedFinpartition n, orderedExpTerm (taylorCoeff u) c := by
  have hzero : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have huCont : ContDiffAt ℂ n u 0 :=
    (hu.contDiffOn isOpen_ball).contDiffAt (isOpen_ball.mem_nhds hzero)
  have hfa := iteratedDeriv_comp_eq_sum_orderedFinpartition
    (i := n) (x := (0 : ℂ)) (g := Complex.exp) (f := u)
    Complex.contDiff_exp.contDiffAt huCont (by simp)
  rw [taylorCoeff]
  change iteratedDeriv n (Complex.exp ∘ u) 0 / n.factorial = _
  rw [hfa, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _
  have hexp : iteratedDeriv c.length Complex.exp (u 0) = 1 := by
    rw [hu0, iteratedDeriv_eq_iterate, Complex.iter_deriv_exp]
    simp
  rw [orderedExpTerm, hexp, one_mul]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  exact iteratedDeriv_eq_factorial_mul_taylorCoeff u (c.partSize j)

noncomputable def majorantLog (a : ℕ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (N + 1),
    (((k : ℝ) * ‖a k‖ ^ 2 : ℝ) : ℂ) * z ^ k

lemma differentiable_majorantLog (a : ℕ → ℂ) (N : ℕ) :
    Differentiable ℂ (majorantLog a N) := by
  unfold majorantLog
  fun_prop

@[simp]
lemma majorantLog_zero (a : ℕ → ℂ) (N : ℕ) : majorantLog a N 0 = 0 := by
  rw [majorantLog]
  apply Finset.sum_eq_zero
  intro k _
  rcases k with _ | k <;> simp

lemma taylorCoeff_majorantLog (a : ℕ → ℂ) (N m : ℕ) (hm : m ≤ N) :
    taylorCoeff (majorantLog a N) m = (((m : ℝ) * ‖a m‖ ^ 2 : ℝ) : ℂ) := by
  rw [taylorCoeff]
  change iteratedDeriv m (fun z : ℂ ↦ ∑ k ∈ Finset.range (N + 1),
    (((k : ℝ) * ‖a k‖ ^ 2 : ℝ) : ℂ) * z ^ k) 0 / m.factorial = _
  have hcont : ∀ k ∈ Finset.range (N + 1),
      ContDiffAt ℂ m (fun z : ℂ ↦
        (((k : ℝ) * ‖a k‖ ^ 2 : ℝ) : ℂ) * z ^ k) 0 := by
    intro k hk
    fun_prop
  rw [iteratedDeriv_fun_sum hcont]
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
  rw [Finset.sum_eq_single m]
  · simp
    field_simp [Nat.factorial_ne_zero]
  · intro k hk hkm
    simp [Ne.symm hkm]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hm))).elim

lemma taylorCoeff_majorantLog_of_lt (a : ℕ → ℂ) (N m : ℕ) (hm : N < m) :
    taylorCoeff (majorantLog a N) m = 0 := by
  rw [taylorCoeff]
  change iteratedDeriv m (fun z : ℂ ↦ ∑ k ∈ Finset.range (N + 1),
    (((k : ℝ) * ‖a k‖ ^ 2 : ℝ) : ℂ) * z ^ k) 0 / m.factorial = 0
  have hcont : ∀ k ∈ Finset.range (N + 1),
      ContDiffAt ℂ m (fun z : ℂ ↦
        (((k : ℝ) * ‖a k‖ ^ 2 : ℝ) : ℂ) * z ^ k) 0 := by
    intro k hk
    fun_prop
  rw [iteratedDeriv_fun_sum hcont]
  rw [_root_.div_eq_zero_iff]
  left
  apply Finset.sum_eq_zero
  intro k hk
  have hkN : k ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hmk : m ≠ k := by omega
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
  simp [hmk]

noncomputable def truncateCoeff (a : ℕ → ℂ) (N k : ℕ) : ℂ :=
  if k ≤ N then a k else 0

lemma taylorCoeff_majorantLog_eq_truncated (a : ℕ → ℂ) (N m : ℕ) :
    taylorCoeff (majorantLog a N) m =
      (((m : ℝ) * ‖truncateCoeff a N m‖ ^ 2 : ℝ) : ℂ) := by
  by_cases hm : m ≤ N
  · rw [taylorCoeff_majorantLog a N m hm]
    simp [truncateCoeff, hm]
  · rw [taylorCoeff_majorantLog_of_lt a N m (by omega)]
    simp [truncateCoeff, hm]

lemma ordered_exp_cauchy_normalized {n : ℕ} (a : ℕ → ℂ) :
    ‖∑ c : OrderedFinpartition n, orderedExpTerm a c‖ ^ 2 ≤
      ∑ c : OrderedFinpartition n,
        ‖orderedExpTerm a c‖ ^ 2 / orderedKoebeWeight c := by
  exact weighted_norm_sum_sq_le Finset.univ (orderedExpTerm a) orderedKoebeWeight
    (fun c _ ↦ orderedKoebeWeight_pos c) (orderedKoebeWeight_sum n)

noncomputable def orderedMajorantTerm (a : ℕ → ℂ) {n : ℕ}
    (c : OrderedFinpartition n) : ℝ :=
  (∏ j, (c.partSize j : ℝ) * ((c.partSize j).factorial : ℝ) *
    ‖a (c.partSize j)‖ ^ 2) / n.factorial

lemma orderedExpTerm_sq_div_weight {n : ℕ} (a : ℕ → ℂ)
    (c : OrderedFinpartition n) :
    ‖orderedExpTerm a c‖ ^ 2 / orderedKoebeWeight c = orderedMajorantTerm a c := by
  rw [orderedExpTerm, orderedKoebeWeight, orderedMajorantTerm, norm_div, norm_prod]
  simp only [norm_mul, Complex.norm_natCast]
  let P : ℝ := ∏ j, ((c.partSize j).factorial : ℝ) * ‖a (c.partSize j)‖
  let Q : ℝ := ∏ j, ((c.partSize j - 1).factorial : ℝ)
  let S : ℝ := ∏ j, (c.partSize j : ℝ) * ((c.partSize j).factorial : ℝ) *
    ‖a (c.partSize j)‖ ^ 2
  change (P / n.factorial) ^ 2 / (Q / n.factorial) = S / n.factorial
  have hprod : P ^ 2 = Q * S := by
    dsimp [P, Q, S]
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    have hfac : ((c.partSize j).factorial : ℝ) =
        (c.partSize j : ℝ) * ((c.partSize j - 1).factorial : ℝ) := by
      exact_mod_cast (Nat.mul_factorial_pred (c.partSize_pos j).ne').symm
    rw [hfac]
    ring
  have hQ : Q ≠ 0 := by
    dsimp [Q]
    positivity
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  rw [div_pow, hprod]
  field_simp [hQ, hfac]

lemma orderedExpTerm_majorantLog (a : ℕ → ℂ) (N n : ℕ)
    (c : OrderedFinpartition n) :
    orderedExpTerm (taylorCoeff (majorantLog a N)) c =
      (orderedMajorantTerm (truncateCoeff a N) c : ℂ) := by
  rw [orderedExpTerm, orderedMajorantTerm]
  push_cast
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [taylorCoeff_majorantLog_eq_truncated]
  push_cast
  ring

noncomputable def expMajorantCoeff (a : ℕ → ℂ) (N n : ℕ) : ℝ :=
  ∑ c : OrderedFinpartition n, orderedMajorantTerm (truncateCoeff a N) c

lemma taylorCoeff_exp_majorantLog (a : ℕ → ℂ) (N n : ℕ) :
    taylorCoeff (fun z ↦ Complex.exp (majorantLog a N z)) n =
      (expMajorantCoeff a N n : ℂ) := by
  rw [taylorCoeff_exp_eq_sum_orderedExpTerm (R := 1) zero_lt_one
    (differentiable_majorantLog a N).differentiableOn (majorantLog_zero a N)]
  rw [expMajorantCoeff]
  push_cast
  apply Finset.sum_congr rfl
  intro c _
  exact orderedExpTerm_majorantLog a N n c

lemma expMajorantCoeff_nonneg (a : ℕ → ℂ) (N n : ℕ) :
    0 ≤ expMajorantCoeff a N n := by
  rw [expMajorantCoeff]
  apply Finset.sum_nonneg
  intro c _
  rw [orderedMajorantTerm]
  positivity

noncomputable def finiteMajorantEnergy (a : ℕ → ℂ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), (k : ℝ) * ‖a k‖ ^ 2

lemma majorantLog_one (a : ℕ → ℂ) (N : ℕ) :
    majorantLog a N 1 = (finiteMajorantEnergy a N : ℂ) := by
  rw [majorantLog, finiteMajorantEnergy]
  simp only [one_pow, mul_one]
  push_cast
  rfl

lemma hasSum_expMajorantCoeff (a : ℕ → ℂ) (N : ℕ) :
    HasSum (expMajorantCoeff a N) (Real.exp (finiteMajorantEnergy a N)) := by
  have hdiff : DifferentiableOn ℂ (fun z ↦ Complex.exp (majorantLog a N z))
      (ball 0 2) := by
    exact (differentiable_majorantLog a N).cexp.differentiableOn
  have hone : (1 : ℂ) ∈ ball 0 2 := by
    norm_num [mem_ball]
  have hTaylor := Complex.hasSum_taylorSeries_on_ball hdiff hone
  have hComplex : HasSum (fun n ↦ (expMajorantCoeff a N n : ℂ))
      (Complex.exp (majorantLog a N 1)) := HasSum.congr_fun hTaylor (fun n ↦ by
    simpa [taylorCoeff, smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm,
      mul_assoc] using (taylorCoeff_exp_majorantLog a N n).symm)
  rw [majorantLog_one, ← Complex.ofReal_exp] at hComplex
  simpa only using Complex.hasSum_ofReal.mp hComplex

lemma sum_expMajorantCoeff_le (a : ℕ → ℂ) (N M : ℕ) :
    ∑ n ∈ Finset.range (M + 1), expMajorantCoeff a N n ≤
      Real.exp (finiteMajorantEnergy a N) := by
  have hsum := hasSum_expMajorantCoeff a N
  calc
    ∑ n ∈ Finset.range (M + 1), expMajorantCoeff a N n ≤
        ∑' n, expMajorantCoeff a N n :=
      hsum.summable.sum_le_tsum _ (fun n _ ↦ expMajorantCoeff_nonneg a N n)
    _ = Real.exp (finiteMajorantEnergy a N) := hsum.tsum_eq

lemma orderedMajorantTerm_truncateCoeff {n : ℕ} (a : ℕ → ℂ) (N : ℕ)
    (hn : n ≤ N) (c : OrderedFinpartition n) :
    orderedMajorantTerm (truncateCoeff a N) c = orderedMajorantTerm a c := by
  rw [orderedMajorantTerm, orderedMajorantTerm]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  have hjN : c.partSize j ≤ N := (c.partSize_le j).trans hn
  simp [truncateCoeff, hjN]

lemma taylorCoeff_halfExp_sq_le_expMajorantCoeff {L : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hL : DifferentiableOn ℂ L (ball 0 R)) (hL0 : L 0 = 0)
    (N n : ℕ) (hn : n ≤ N) :
    ‖taylorCoeff (halfExp L) n‖ ^ 2 ≤ expMajorantCoeff (logarithmicCoeff L) N n := by
  calc
    ‖taylorCoeff (halfExp L) n‖ ^ 2 ≤
        ∑ c : OrderedFinpartition n,
          ‖orderedExpTerm (logarithmicCoeff L) c‖ ^ 2 / orderedKoebeWeight c :=
      by
        rw [taylorCoeff_halfExp_eq_sum_orderedExpTerm hR hL hL0]
        exact ordered_exp_cauchy_normalized _
    _ = ∑ c : OrderedFinpartition n,
        orderedMajorantTerm (logarithmicCoeff L) c := by
      apply Finset.sum_congr rfl
      intro c _
      exact orderedExpTerm_sq_div_weight _ c
    _ = expMajorantCoeff (logarithmicCoeff L) N n := by
      rw [expMajorantCoeff]
      apply Finset.sum_congr rfl
      intro c _
      exact (orderedMajorantTerm_truncateCoeff _ N hn c).symm

lemma finiteMajorantEnergy_succ (a : ℕ → ℂ) (N : ℕ) :
    finiteMajorantEnergy a (N + 1) = finiteMajorantEnergy a N +
      ((N + 1 : ℕ) : ℝ) * ‖a (N + 1)‖ ^ 2 := by
  simp [finiteMajorantEnergy, Finset.sum_range_succ]

lemma finiteMajorantEnergy_logarithmicCoeff (L : ℂ → ℂ) (N : ℕ) :
    finiteMajorantEnergy (logarithmicCoeff L) N = logarithmicEnergy L N := by
  induction N with
  | zero => simp [finiteMajorantEnergy, logarithmicEnergy]
  | succ N ih =>
      rw [finiteMajorantEnergy_succ, logarithmicEnergy_succ, ih]

lemma coeffSquareSum_le_exp_logarithmicEnergy {L : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hL : DifferentiableOn ℂ L (ball 0 R)) (hL0 : L 0 = 0)
    (N : ℕ) :
    coeffSquareSum L (N + 1) ≤ Real.exp (logarithmicEnergy L N) := by
  rw [coeffSquareSum]
  calc
    ∑ n ∈ Finset.range (N + 1), ‖taylorCoeff (halfExp L) n‖ ^ 2 ≤
        ∑ n ∈ Finset.range (N + 1), expMajorantCoeff (logarithmicCoeff L) N n := by
      apply Finset.sum_le_sum
      intro n hn
      exact taylorCoeff_halfExp_sq_le_expMajorantCoeff hR hL hL0 N n
        (Nat.le_of_lt_succ (Finset.mem_range.mp hn))
    _ ≤ Real.exp (finiteMajorantEnergy (logarithmicCoeff L) N) :=
      sum_expMajorantCoeff_le _ N N
    _ = Real.exp (logarithmicEnergy L N) := by
      rw [finiteMajorantEnergy_logarithmicCoeff]

noncomputable def quadraticLogarithmicEnergy (L : ℂ → ℂ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N,
    ((k + 1 : ℕ) : ℝ) ^ 2 * ‖logarithmicCoeff L (k + 1)‖ ^ 2

lemma reflected_quadraticLogarithmicEnergy (L : ℂ → ℂ) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1),
        ((n - i + 1 : ℕ) : ℝ) ^ 2 *
          ‖logarithmicCoeff L (n - i + 1)‖ ^ 2) =
      quadraticLogarithmicEnergy L (n + 1) := by
  simpa [quadraticLogarithmicEnergy, Nat.add_comm] using
    (Finset.sum_range_reflect
      (fun k ↦ ((k + 1 : ℕ) : ℝ) ^ 2 *
        ‖logarithmicCoeff L (k + 1)‖ ^ 2) (n + 1))

lemma halfExp_coeff_sharp_energy_bound {L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) ^ 2 * ‖taylorCoeff (halfExp L) (n + 1)‖ ^ 2 ≤
      coeffSquareSum L (n + 1) * quadraticLogarithmicEnergy L (n + 1) := by
  rw [← reflected_quadraticLogarithmicEnergy]
  have hnorm :
      ‖∑ i ∈ Finset.range (n + 1),
          taylorCoeff (halfExp L) i *
            ((n - i + 1 : ℕ) * logarithmicCoeff L (n - i + 1))‖ ≤
        ∑ i ∈ Finset.range (n + 1),
          ‖taylorCoeff (halfExp L) i‖ *
            (((n - i + 1 : ℕ) : ℝ) *
              ‖logarithmicCoeff L (n - i + 1)‖) := by
    calc
      _ ≤ ∑ i ∈ Finset.range (n + 1),
          ‖taylorCoeff (halfExp L) i *
            ((n - i + 1 : ℕ) * logarithmicCoeff L (n - i + 1))‖ :=
        norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [norm_mul, norm_natCast]
  calc
    ((n + 1 : ℕ) : ℝ) ^ 2 * ‖taylorCoeff (halfExp L) (n + 1)‖ ^ 2 =
        ‖((n + 1 : ℕ) : ℂ) * taylorCoeff (halfExp L) (n + 1)‖ ^ 2 := by
      rw [norm_mul, Complex.norm_natCast, mul_pow]
    _ = ‖∑ i ∈ Finset.range (n + 1),
          taylorCoeff (halfExp L) i *
            ((n - i + 1 : ℕ) * logarithmicCoeff L (n - i + 1))‖ ^ 2 := by
      rw [halfExp_coeff_recurrence hR hL n]
    _ ≤
        (∑ i ∈ Finset.range (n + 1),
          ‖taylorCoeff (halfExp L) i‖ *
            (((n - i + 1 : ℕ) : ℝ) *
              ‖logarithmicCoeff L (n - i + 1)‖)) ^ 2 := by
      gcongr
    _ ≤ (∑ i ∈ Finset.range (n + 1),
          ‖taylorCoeff (halfExp L) i‖ ^ 2) *
        ∑ i ∈ Finset.range (n + 1),
          ((n - i + 1 : ℕ) : ℝ) ^ 2 *
            ‖logarithmicCoeff L (n - i + 1)‖ ^ 2 := by
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      · intro i _
        positivity
      · intro i _
        positivity
      · intro i _
        ring_nf
        exact le_rfl
    _ = _ := by
      rw [coeffSquareSum]

lemma coeffSquareSum_pos {L : ℂ → ℂ} (hL0 : L 0 = 0) {N : ℕ} (hN : 0 < N) :
    0 < coeffSquareSum L N := by
  rw [coeffSquareSum]
  apply Finset.sum_pos'
  · intro i hi
    positivity
  · refine ⟨0, Finset.mem_range.mpr hN, ?_⟩
    simp [hL0]

lemma halfExp_coeff_ratio_le {L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) (hL0 : L 0 = 0) (n : ℕ) :
    ‖taylorCoeff (halfExp L) (n + 1)‖ ^ 2 / coeffSquareSum L (n + 1) ≤
      quadraticLogarithmicEnergy L (n + 1) / (((n + 1 : ℕ) : ℝ) ^ 2) := by
  have hsum : 0 < coeffSquareSum L (n + 1) := coeffSquareSum_pos hL0 (by omega)
  have hn : 0 < (((n + 1 : ℕ) : ℝ) ^ 2) := by positivity
  rw [div_le_div_iff₀ hsum hn]
  have h := halfExp_coeff_sharp_energy_bound hR hL n
  nlinarith

lemma log_one_add_tangent {r x : ℝ} (hr : 0 < r) (hx : 0 ≤ x) :
    Real.log (1 + x) - Real.log (1 + 1 / r) ≤
      r / (r + 1) * (x - 1 / r) := by
  have hx1 : 0 < 1 + x := by linarith
  have hr1 : 0 < 1 + 1 / r := by positivity
  calc
    Real.log (1 + x) - Real.log (1 + 1 / r) =
        Real.log ((1 + x) / (1 + 1 / r)) := by
      rw [Real.log_div hx1.ne' hr1.ne']
    _ ≤ (1 + x) / (1 + 1 / r) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hx1 hr1)
    _ = r / (r + 1) * (x - 1 / r) := by
      field_simp
      ring

noncomputable def normalizedCoeffLog (L : ℂ → ℂ) (N : ℕ) : ℝ :=
  Real.log (coeffSquareSum L N) - Real.log N

lemma normalizedCoeffLog_step {L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) (hL0 : L 0 = 0) (n : ℕ) :
    normalizedCoeffLog L (n + 2) - normalizedCoeffLog L (n + 1) ≤
      quadraticLogarithmicEnergy L (n + 1) /
          (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ)) -
        1 / ((n + 2 : ℕ) : ℝ) := by
  let S : ℝ := coeffSquareSum L (n + 1)
  let q : ℝ := ‖taylorCoeff (halfExp L) (n + 1)‖ ^ 2
  let d : ℝ := (n + 1 : ℕ)
  let D : ℝ := quadraticLogarithmicEnergy L (n + 1)
  have hS : 0 < S := by
    exact coeffSquareSum_pos hL0 (by omega)
  have hq : 0 ≤ q := by positivity
  have hd : 0 < d := by positivity
  have hsum : coeffSquareSum L (n + 2) = S + q := by
    simpa [S, q] using coeffSquareSum_succ L (n + 1)
  have hlogS : Real.log (S + q) - Real.log S = Real.log (1 + q / S) := by
    calc
      Real.log (S + q) - Real.log S = Real.log ((S + q) / S) := by
        rw [Real.log_div (add_pos_of_pos_of_nonneg hS hq).ne' hS.ne']
      _ = Real.log (1 + q / S) := by
        congr 1
        field_simp [hS.ne']
  have hlogNat :
      Real.log (((n + 2 : ℕ) : ℝ)) - Real.log (((n + 1 : ℕ) : ℝ)) =
        Real.log (1 + 1 / d) := by
    calc
      Real.log (((n + 2 : ℕ) : ℝ)) - Real.log (((n + 1 : ℕ) : ℝ)) =
          Real.log ((((n + 2 : ℕ) : ℝ)) / (((n + 1 : ℕ) : ℝ))) := by
        rw [Real.log_div (by positivity : (((n + 2 : ℕ) : ℝ)) ≠ 0)
          (by positivity : (((n + 1 : ℕ) : ℝ)) ≠ 0)]
      _ = Real.log (1 + 1 / d) := by
        congr 1
        dsimp [d]
        push_cast
        field_simp
        ring
  have hratio : q / S ≤ D / d ^ 2 := by
    simpa [q, S, D, d] using halfExp_coeff_ratio_le hR hL hL0 n
  calc
    normalizedCoeffLog L (n + 2) - normalizedCoeffLog L (n + 1) =
        (Real.log (S + q) - Real.log S) -
          (Real.log (((n + 2 : ℕ) : ℝ)) -
            Real.log (((n + 1 : ℕ) : ℝ))) := by
      rw [normalizedCoeffLog, normalizedCoeffLog, hsum]
      ring
    _ = Real.log (1 + q / S) - Real.log (1 + 1 / d) := by
      rw [hlogS, hlogNat]
    _ ≤ d / (d + 1) * (q / S - 1 / d) :=
      log_one_add_tangent hd (div_nonneg hq hS.le)
    _ ≤ d / (d + 1) * (D / d ^ 2 - 1 / d) := by
      gcongr
    _ = D / (d * (d + 1)) - 1 / (d + 1) := by
      field_simp [hd.ne']
    _ = quadraticLogarithmicEnergy L (n + 1) /
          (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ)) -
        1 / ((n + 2 : ℕ) : ℝ) := by
      dsimp [D, d]
      push_cast
      ring

noncomputable def lebedevExponent (L : ℂ → ℂ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N,
    (quadraticLogarithmicEnergy L (n + 1) /
        (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ)) -
      1 / ((n + 2 : ℕ) : ℝ))

lemma lebedevExponent_succ (L : ℂ → ℂ) (N : ℕ) :
    lebedevExponent L (N + 1) = lebedevExponent L N +
      (quadraticLogarithmicEnergy L (N + 1) /
          (((N + 1 : ℕ) : ℝ) * ((N + 2 : ℕ) : ℝ)) -
        1 / ((N + 2 : ℕ) : ℝ)) := by
  simp [lebedevExponent, Finset.sum_range_succ]
  ring

lemma normalizedCoeffLog_le_lebedevExponent {L : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hL : DifferentiableOn ℂ L (ball 0 R)) (hL0 : L 0 = 0)
    (N : ℕ) :
    normalizedCoeffLog L (N + 1) ≤ lebedevExponent L N := by
  induction N with
  | zero => simp [normalizedCoeffLog, lebedevExponent, hL0]
  | succ N ih =>
      calc
        normalizedCoeffLog L (N + 2) = normalizedCoeffLog L (N + 1) +
            (normalizedCoeffLog L (N + 2) - normalizedCoeffLog L (N + 1)) := by
          ring
        _ ≤ lebedevExponent L N +
            (quadraticLogarithmicEnergy L (N + 1) /
                (((N + 1 : ℕ) : ℝ) * ((N + 2 : ℕ) : ℝ)) -
              1 / ((N + 2 : ℕ) : ℝ)) :=
          add_le_add ih (normalizedCoeffLog_step hR hL hL0 N)
        _ = lebedevExponent L (N + 1) := by
          rw [lebedevExponent_succ]

lemma quadraticLogarithmicEnergy_succ (L : ℂ → ℂ) (N : ℕ) :
    quadraticLogarithmicEnergy L (N + 1) = quadraticLogarithmicEnergy L N +
      ((N + 1 : ℕ) : ℝ) ^ 2 * ‖logarithmicCoeff L (N + 1)‖ ^ 2 := by
  simp [quadraticLogarithmicEnergy, Finset.sum_range_succ]

lemma milinFunctional_add_quadratic (L : ℂ → ℂ) (N : ℕ) :
    milinFunctional L N + quadraticLogarithmicEnergy L (N + 1) -
        ((N + 1 : ℕ) : ℝ) =
      ((N + 1 : ℕ) : ℝ) *
        (logarithmicEnergy L (N + 1) - harmonicEnergy (N + 1)) := by
  induction N with
  | zero =>
      norm_num [milinFunctional, quadraticLogarithmicEnergy, logarithmicEnergy,
        harmonicEnergy]
  | succ N ih =>
      calc
        milinFunctional L (N + 1) + quadraticLogarithmicEnergy L (N + 2) -
            ((N + 2 : ℕ) : ℝ) =
          (milinFunctional L N + quadraticLogarithmicEnergy L (N + 1) -
              ((N + 1 : ℕ) : ℝ)) +
            (logarithmicEnergy L (N + 1) - harmonicEnergy (N + 1)) +
            ((N + 2 : ℕ) : ℝ) ^ 2 *
              ‖logarithmicCoeff L (N + 2)‖ ^ 2 - 1 := by
          rw [milinFunctional_succ, quadraticLogarithmicEnergy_succ]
          push_cast
          ring
        _ = ((N + 1 : ℕ) : ℝ) *
              (logarithmicEnergy L (N + 1) - harmonicEnergy (N + 1)) +
            (logarithmicEnergy L (N + 1) - harmonicEnergy (N + 1)) +
            ((N + 2 : ℕ) : ℝ) ^ 2 *
              ‖logarithmicCoeff L (N + 2)‖ ^ 2 - 1 := by
          rw [ih]
        _ = ((N + 2 : ℕ) : ℝ) *
            ((logarithmicEnergy L (N + 1) +
                ((N + 2 : ℕ) : ℝ) *
                  ‖logarithmicCoeff L (N + 2)‖ ^ 2) -
              (harmonicEnergy (N + 1) + 1 / ((N + 2 : ℕ) : ℝ))) := by
          push_cast
          field_simp
          ring
        _ = ((N + 2 : ℕ) : ℝ) *
            (logarithmicEnergy L (N + 2) - harmonicEnergy (N + 2)) := by
          rw [← logarithmicEnergy_succ L (N + 1), ← harmonicEnergy_succ (N + 1)]

lemma lebedevExponent_eq_milinFunctional (L : ℂ → ℂ) (N : ℕ) :
    lebedevExponent L N =
      milinFunctional L N / ((N + 1 : ℕ) : ℝ) := by
  induction N with
  | zero => simp [lebedevExponent, milinFunctional]
  | succ N ih =>
      rw [lebedevExponent_succ, ih, milinFunctional_succ]
      have hbridge := milinFunctional_add_quadratic L N
      have hD : quadraticLogarithmicEnergy L (N + 1) =
          ((N + 1 : ℕ) : ℝ) *
              (logarithmicEnergy L (N + 1) - harmonicEnergy (N + 1)) -
            milinFunctional L N + ((N + 1 : ℕ) : ℝ) := by
        linarith
      rw [hD]
      push_cast
      field_simp
      ring

lemma satisfiesLebedevMilin {L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) (hL0 : L 0 = 0) :
    SatisfiesLebedevMilin L := by
  intro N
  have hnormalized := normalizedCoeffLog_le_lebedevExponent hR hL hL0 N
  rw [lebedevExponent_eq_milinFunctional] at hnormalized
  have hsum : 0 < coeffSquareSum L (N + 1) := coeffSquareSum_pos hL0 (by omega)
  have hN : 0 < (((N + 1 : ℕ) : ℝ)) := by positivity
  have hlog : Real.log (coeffSquareSum L (N + 1)) ≤
      Real.log (((N + 1 : ℕ) : ℝ)) +
        milinFunctional L N / ((N + 1 : ℕ) : ℝ) := by
    rw [normalizedCoeffLog] at hnormalized
    linarith
  calc
    coeffSquareSum L (N + 1) =
        Real.exp (Real.log (coeffSquareSum L (N + 1))) :=
      (Real.exp_log hsum).symm
    _ ≤ Real.exp (Real.log (((N + 1 : ℕ) : ℝ)) +
        milinFunctional L N / ((N + 1 : ℕ) : ℝ)) :=
      Real.exp_le_exp.mpr hlog
    _ = ((N + 1 : ℕ) : ℝ) *
        Real.exp (milinFunctional L N / ((N + 1 : ℕ) : ℝ)) := by
      rw [Real.exp_add, Real.exp_log hN]

lemma normalized_coeff_bound_of_milin_only {f L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : NormalizedUnivalentOn f R) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hL0 : L 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z)
    (hmilin : SatisfiesMilin L) (n : ℕ) : ‖taylorCoeff f n‖ ≤ n := by
  exact normalized_coeff_bound_of_milin hR hf hL hexp hmilin
    (satisfiesLebedevMilin hR hL hL0) n

lemma taylorCoeff_halfExp_sq_le_ordered_majorant {L : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hL : DifferentiableOn ℂ L (ball 0 R)) (hL0 : L 0 = 0)
    (n : ℕ) :
    ‖taylorCoeff (halfExp L) n‖ ^ 2 ≤
      ∑ c : OrderedFinpartition n,
        ‖orderedExpTerm (logarithmicCoeff L) c‖ ^ 2 / orderedKoebeWeight c := by
  rw [taylorCoeff_halfExp_eq_sum_orderedExpTerm hR hL hL0]
  exact ordered_exp_cauchy_normalized _

noncomputable def partitionExpTerm {n : ℕ} (a : ℕ → ℂ) (p : n.Partition) : ℂ :=
  p.parts.toFinsupp.prod fun k c => a k ^ c / c.factorial

noncomputable def partitionKoebeWeight {n : ℕ} (p : n.Partition) : ℝ :=
  p.parts.toFinsupp.prod fun k c => 1 / ((k : ℝ) ^ c * c.factorial)

lemma partitionKoebeWeight_pos {n : ℕ} (p : n.Partition) :
    0 < partitionKoebeWeight p := by
  rw [partitionKoebeWeight, Finsupp.prod]
  apply Finset.prod_pos
  intro k hk
  have hk_parts : k ∈ p.parts := by
    simpa [Multiset.toFinsupp_support] using hk
  have hk_pos : 0 < k := p.parts_pos hk_parts
  positivity

lemma partitionKoebeWeight_eq {n : ℕ} (p : n.Partition) :
    partitionKoebeWeight p =
      1 / (((p.parts.prod : ℕ) : ℝ) *
        ∏ k ∈ p.parts.toFinset, ((p.parts.count k).factorial : ℝ)) := by
  rw [partitionKoebeWeight, Finsupp.prod]
  simp only [Multiset.toFinsupp_support, Multiset.toFinsupp_apply]
  rw [show ((p.parts.prod : ℕ) : ℝ) =
      ∏ k ∈ p.parts.toFinset, (k : ℝ) ^ p.parts.count k by
    exact_mod_cast Finset.prod_multiset_count p.parts]
  simp only [div_eq_mul_inv, one_mul, mul_inv, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib]

lemma multiset_eq_filter_two_add_ones {s : Multiset ℕ}
    (hs : ∀ k ∈ s, 0 < k) :
    s = s.filter (2 ≤ ·) + Multiset.replicate (s.count 1) 1 := by
  ext k
  rw [Multiset.count_add, Multiset.count_filter, Multiset.count_replicate]
  by_cases hk : 2 ≤ k
  · have hk1 : (1 : ℕ) ≠ k := by omega
    simp [hk, hk1]
  · have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with rfl | rfl
    · have h0 : 0 ∉ s := fun h => (Nat.lt_irrefl 0) (hs 0 h)
      simp [Multiset.count_eq_zero.mpr h0]
    · simp

lemma partition_parts_eq_nontrivial_add_ones {n : ℕ} (p : n.Partition) :
    p.parts = p.parts.filter (2 ≤ ·) + Multiset.replicate (p.parts.count 1) 1 :=
  multiset_eq_filter_two_add_ones (fun _ hk => p.parts_pos hk)

lemma partition_nontrivial_sum_add_count_one {n : ℕ} (p : n.Partition) :
    (p.parts.filter (2 ≤ ·)).sum + p.parts.count 1 = n := by
  simpa [p.parts_sum] using
    (congrArg Multiset.sum (partition_parts_eq_nontrivial_add_ones p)).symm

lemma partition_parts_prod_eq_nontrivial_prod {n : ℕ} (p : n.Partition) :
    p.parts.prod = (p.parts.filter (2 ≤ ·)).prod := by
  simpa using congrArg Multiset.prod (partition_parts_eq_nontrivial_add_ones p)

lemma partition_count_factorial_prod_eq {n : ℕ} (p : n.Partition) :
    (∏ k ∈ p.parts.toFinset, (p.parts.count k).factorial) =
      (p.parts.count 1).factorial *
        ∏ k ∈ (p.parts.filter (2 ≤ ·)).toFinset,
          ((p.parts.filter (2 ≤ ·)).count k).factorial := by
  by_cases h1 : 1 ∈ p.parts
  · have hfin : p.parts.toFinset =
        insert 1 (p.parts.filter (2 ≤ ·)).toFinset := by
      ext k
      simp only [Multiset.mem_toFinset, Finset.mem_insert, Multiset.mem_filter]
      constructor
      · intro hk
        by_cases hk1 : k = 1
        · exact Or.inl hk1
        · exact Or.inr ⟨hk, by have := p.parts_pos hk; omega⟩
      · rintro (rfl | ⟨hk, _⟩)
        · exact h1
        · exact hk
    have hnot : 1 ∉ (p.parts.filter (2 ≤ ·)).toFinset := by simp
    rw [hfin, Finset.prod_insert hnot]
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    have hk2 : 2 ≤ k := (Multiset.mem_filter.mp (Multiset.mem_toFinset.mp hk)).2
    simp [hk2]
  · have hc1 : p.parts.count 1 = 0 := Multiset.count_eq_zero.mpr h1
    have hp : p.parts = p.parts.filter (2 ≤ ·) := by
      simpa [hc1] using partition_parts_eq_nontrivial_add_ones p
    rw [hc1, Nat.factorial_zero, one_mul]
    conv_lhs => rw [hp]

lemma perm_partition_eq_iff_cycleType_eq {α : Type*} [Fintype α] [DecidableEq α]
    (p : (Fintype.card α).Partition) (σ : Equiv.Perm α) :
    σ.partition = p ↔ σ.cycleType = p.parts.filter (2 ≤ ·) := by
  constructor
  · intro h
    have hfilter := Equiv.Perm.filter_parts_partition_eq_cycleType (σ := σ)
    rw [h] at hfilter
    exact hfilter.symm
  · intro h
    apply Nat.Partition.ext
    have hsupp : σ.support.card = (p.parts.filter (2 ≤ ·)).sum := by
      rw [← Equiv.Perm.sum_cycleType, h]
    have hcount := partition_nontrivial_sum_add_count_one p
    have hsub : Fintype.card α - (p.parts.filter (2 ≤ ·)).sum =
        p.parts.count 1 := by omega
    calc
      σ.partition.parts = σ.cycleType +
          Multiset.replicate (Fintype.card α - σ.support.card) 1 :=
        Equiv.Perm.parts_partition
      _ = p.parts.filter (2 ≤ ·) + Multiset.replicate (p.parts.count 1) 1 := by
        rw [h, hsupp, hsub]
      _ = p.parts := (partition_parts_eq_nontrivial_add_ones p).symm

noncomputable def partitionPermFiber {α : Type*} [Fintype α] [DecidableEq α]
    (p : (Fintype.card α).Partition) : Finset (Equiv.Perm α) :=
  Finset.univ.filter fun σ => σ.partition = p

lemma partitionPermFiber_eq_cycleType {α : Type*} [Fintype α] [DecidableEq α]
    (p : (Fintype.card α).Partition) :
    partitionPermFiber p =
      Finset.univ.filter fun σ : Equiv.Perm α =>
        σ.cycleType = p.parts.filter (2 ≤ ·) := by
  ext σ
  simp [partitionPermFiber, perm_partition_eq_iff_cycleType_eq]

lemma partition_centralizerDenom_eq {n : ℕ} (p : n.Partition) :
    (n - (p.parts.filter (2 ≤ ·)).sum).factorial *
          (p.parts.filter (2 ≤ ·)).prod *
          (∏ k ∈ (p.parts.filter (2 ≤ ·)).toFinset,
            ((p.parts.filter (2 ≤ ·)).count k).factorial) =
      p.parts.prod * ∏ k ∈ p.parts.toFinset, (p.parts.count k).factorial := by
  have hsum := partition_nontrivial_sum_add_count_one p
  have hsub : n - (p.parts.filter (2 ≤ ·)).sum = p.parts.count 1 := by omega
  rw [hsub, partition_parts_prod_eq_nontrivial_prod,
    partition_count_factorial_prod_eq]
  ring

lemma partitionPermFiber_card_mul_denom {α : Type*} [Fintype α] [DecidableEq α]
    (p : (Fintype.card α).Partition) :
    (partitionPermFiber p).card *
        (p.parts.prod * ∏ k ∈ p.parts.toFinset, (p.parts.count k).factorial) =
      (Fintype.card α).factorial := by
  let m : Multiset ℕ := p.parts.filter (2 ≤ ·)
  have hm_sum : m.sum ≤ Fintype.card α := by
    have hsum := partition_nontrivial_sum_add_count_one p
    dsimp [m]
    omega
  have hm_parts : ∀ k ∈ m, 2 ≤ k := by
    intro k hk
    exact (Multiset.mem_filter.mp hk).2
  have hcard := Equiv.Perm.card_of_cycleType_mul_eq α m
  rw [if_pos ⟨hm_sum, hm_parts⟩] at hcard
  rw [partitionPermFiber_eq_cycleType]
  change _ * (p.parts.prod * _) = _
  rw [← partition_centralizerDenom_eq p]
  simpa [m, mul_assoc] using hcard

lemma partitionKoebeWeight_eq_card_div_factorial {α : Type*} [Fintype α]
    [DecidableEq α] (p : (Fintype.card α).Partition) :
    partitionKoebeWeight p =
      ((partitionPermFiber p).card : ℝ) / (Fintype.card α).factorial := by
  rw [partitionKoebeWeight_eq]
  have hcard := partitionPermFiber_card_mul_denom p
  have hparts : 0 < p.parts.prod :=
    Multiset.prod_pos fun k hk => p.parts_pos hk
  have hcounts :
      0 < ∏ k ∈ p.parts.toFinset, (p.parts.count k).factorial := by
    apply Finset.prod_pos
    intro k hk
    exact Nat.factorial_pos _
  have hdenom :
      (p.parts.prod * ∏ k ∈ p.parts.toFinset, (p.parts.count k).factorial : ℕ) ≠ 0 :=
    (Nat.mul_pos hparts hcounts).ne'
  have hfactorial : (Fintype.card α).factorial ≠ 0 := Nat.factorial_ne_zero _
  field_simp [hdenom, hfactorial]
  have hcard_comm :
      (Fintype.card α).factorial =
        (p.parts.prod * ∏ k ∈ p.parts.toFinset, (p.parts.count k).factorial) *
          (partitionPermFiber p).card := by
    rw [mul_comm]
    exact hcard.symm
  exact_mod_cast hcard_comm

lemma partitionKoebeWeight_sum_fintype (α : Type*) [Fintype α] [DecidableEq α] :
    ∑ p : (Fintype.card α).Partition, partitionKoebeWeight p = 1 := by
  have hcard :
      (Finset.univ : Finset (Equiv.Perm α)).card =
        ∑ p : (Fintype.card α).Partition, (partitionPermFiber p).card := by
    simpa [partitionPermFiber] using
      (Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset (Equiv.Perm α)))
        (t := (Finset.univ : Finset (Fintype.card α).Partition))
        (f := fun σ : Equiv.Perm α => σ.partition)
        (fun _ _ => Finset.mem_univ _))
  have hcard' :
      (∑ p : (Fintype.card α).Partition, (partitionPermFiber p).card) =
        (Fintype.card α).factorial := by
    rw [← hcard]
    exact Fintype.card_perm
  have hcardReal :
      (∑ p : (Fintype.card α).Partition, ((partitionPermFiber p).card : ℝ)) =
        ((Fintype.card α).factorial : ℝ) := by
    exact_mod_cast hcard'
  calc
    (∑ p : (Fintype.card α).Partition, partitionKoebeWeight p) =
        ∑ p : (Fintype.card α).Partition,
          ((partitionPermFiber p).card : ℝ) / (Fintype.card α).factorial := by
      apply Finset.sum_congr rfl
      intro p hp
      exact partitionKoebeWeight_eq_card_div_factorial p
    _ = (∑ p : (Fintype.card α).Partition, ((partitionPermFiber p).card : ℝ)) /
        (Fintype.card α).factorial := by
      rw [Finset.sum_div]
    _ = 1 := by
      rw [hcardReal, div_self]
      positivity

lemma partitionKoebeWeight_sum (n : ℕ) :
    ∑ p : n.Partition, partitionKoebeWeight p = 1 := by
  rw [← Fintype.card_fin n]
  exact partitionKoebeWeight_sum_fintype (Fin n)

lemma partition_exp_cauchy {n : ℕ} (a : ℕ → ℂ)
    (hweight : ∑ p : n.Partition, partitionKoebeWeight p = 1) :
    ‖∑ p : n.Partition, partitionExpTerm a p‖ ^ 2 ≤
      ∑ p : n.Partition, ‖partitionExpTerm a p‖ ^ 2 / partitionKoebeWeight p := by
  exact weighted_norm_sum_sq_le Finset.univ (partitionExpTerm a) partitionKoebeWeight
    (fun p hp => partitionKoebeWeight_pos p) hweight

lemma partition_exp_cauchy_normalized {n : ℕ} (a : ℕ → ℂ) :
    ‖∑ p : n.Partition, partitionExpTerm a p‖ ^ 2 ≤
      ∑ p : n.Partition, ‖partitionExpTerm a p‖ ^ 2 / partitionKoebeWeight p :=
  partition_exp_cauchy a (partitionKoebeWeight_sum n)

end Submission
