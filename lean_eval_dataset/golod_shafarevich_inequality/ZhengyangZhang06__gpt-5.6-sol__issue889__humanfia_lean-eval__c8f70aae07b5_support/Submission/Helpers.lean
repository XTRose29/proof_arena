import ChallengeDeps

namespace Submission.Helpers

open LeanEval.GroupTheory

section GeneratorRank

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DiscreteTopology G]

/-- In a discrete group, taking the topological closure does not change a subgroup. -/
theorem topologicalClosure_eq_self (H : Subgroup G) : H.topologicalClosure = H := by
  apply SetLike.ext'
  rw [Subgroup.topologicalClosure_coe, closure_discrete]

/-- A finite discrete group has a finite topological generating set. -/
theorem exists_finset_topologicalClosure_closure_eq_top [Finite G] :
    ∃ S : Finset G, (Subgroup.closure (S : Set G)).topologicalClosure = ⊤ := by
  classical
  letI := Fintype.ofFinite G
  refine ⟨Finset.univ, ?_⟩
  rw [topologicalClosure_eq_self]
  simp

/-- The infimum in `generatorRank` is attained for finite discrete groups. -/
theorem exists_generatorRank_finset [Finite G] :
    ∃ S : Finset G, S.card = generatorRank G ∧
      (Subgroup.closure (S : Set G)).topologicalClosure = ⊤ := by
  rw [generatorRank]
  have hne :
      {k : ℕ | ∃ S : Finset G, S.card = k ∧
        (Subgroup.closure (S : Set G)).topologicalClosure = ⊤}.Nonempty := by
    obtain ⟨S, hS⟩ := exists_finset_topologicalClosure_closure_eq_top G
    exact ⟨S.card, ⟨S, rfl, hS⟩⟩
  simpa only [Set.mem_setOf_eq] using Nat.sInf_mem hne

/-- A nontrivial finite discrete group needs at least one generator. -/
theorem generatorRank_pos [Finite G] [Nontrivial G] : 0 < generatorRank G := by
  obtain ⟨S, hcard, htop⟩ := exists_generatorRank_finset G
  rw [topologicalClosure_eq_self] at htop
  by_contra h
  have hrank : generatorRank G = 0 := Nat.eq_zero_of_not_pos h
  have hS : S = ∅ := Finset.card_eq_zero.mp (hcard.trans hrank)
  subst S
  simp only [Finset.coe_empty, Subgroup.closure_empty] at htop
  have hsub : Subsingleton G := ⟨fun a b ↦ by
    have ha : a = 1 := by
      have : a ∈ (⊥ : Subgroup G) := htop.symm ▸ Subgroup.mem_top a
      simpa using this
    have hb : b = 1 := by
      have : b ∈ (⊥ : Subgroup G) := htop.symm ▸ Subgroup.mem_top b
      simpa using this
    exact ha.trans hb.symm⟩
  exact not_subsingleton G hsub

end GeneratorRank

section GeneratorRankBounds

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Every finite topological generating set bounds `generatorRank` from above. -/
theorem generatorRank_le_card (S : Finset G)
    (hS : (Subgroup.closure (S : Set G)).topologicalClosure = ⊤) :
    generatorRank G ≤ S.card := by
  apply Nat.sInf_le
  exact ⟨S, rfl, hS⟩

end GeneratorRankBounds

section NumericalInequality

open Polynomial

private theorem coeff_quadratic_mul (d r : ℝ) (P : ℝ[X]) (n : ℕ) :
    ((1 - C d * X + C r * X ^ 2) * P).coeff (n + 2) =
      P.coeff (n + 2) - d * P.coeff (n + 1) + r * P.coeff n := by
  simp [sub_mul, add_mul, pow_two, mul_assoc]

private theorem eval_nonneg_of_coeff_nonneg (P : ℝ[X]) {t : ℝ} (ht : 0 ≤ t)
    (hP : ∀ n, 0 ≤ P.coeff n) : 0 ≤ P.eval t := by
  rw [eval_eq_sum, sum_def]
  exact Finset.sum_nonneg fun n _ ↦ mul_nonneg (hP n) (pow_nonneg ht n)

/-- The numerical last step in the Golod--Shafarevich argument.

If a finite Hilbert series starts with coefficients `1, d` and its coefficients
satisfy the Golod--Shafarevich recurrence with `r` relations, then
`d² < 4r`. -/
theorem golod_shafarevich_numeric {d r : ℝ} (hd : 0 < d)
    (P : ℝ[X]) (hP0 : P.coeff 0 = 1) (hP1 : P.coeff 1 = d)
    (hPnonneg : ∀ n, 0 ≤ P.coeff n)
    (hrec : ∀ n, 2 ≤ n →
      0 ≤ P.coeff n - d * P.coeff (n - 1) + r * P.coeff (n - 2)) :
    d ^ 2 < 4 * r := by
  by_contra hlt
  have hdisc : 4 * r ≤ d ^ 2 := le_of_not_gt hlt
  let q : ℝ[X] := 1 - C d * X + C r * X ^ 2
  let R : ℝ[X] := q * P
  have hR0 : R.coeff 0 = 1 := by
    simp [R, q, hP0]
  have hR1 : R.coeff 1 = 0 := by
    change ((1 - C d * X + C r * X ^ 2) * P).coeff 1 = 0
    rw [mul_coeff_one]
    simp [coeff_one, hP0, hP1]
  have hRnonneg : ∀ n, 0 ≤ R.coeff n := by
    intro n
    rcases n with _ | n
    · simp [hR0]
    rcases n with _ | n
    · simp [hR1]
    rw [show n + 1 + 1 = n + 2 by omega]
    change 0 ≤ ((1 - C d * X + C r * X ^ 2) * P).coeff (n + 2)
    rw [coeff_quadratic_mul]
    have hn := hrec (n + 2) (by omega)
    rw [show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega] at hn
    exact hn
  let t : ℝ := 2 / d
  have ht : 0 < t := div_pos (by norm_num) hd
  have hPeval : 0 ≤ P.eval t :=
    eval_nonneg_of_coeff_nonneg P ht.le hPnonneg
  have hReval_pos : 0 < R.eval t := by
    have hzero_mem : 0 ∈ R.support := by
      rw [mem_support_iff]
      rw [hR0]
      norm_num
    have hfirst : R.coeff 0 * t ^ 0 = 1 := by simp [hR0]
    calc
      0 < R.coeff 0 * t ^ 0 := by rw [hfirst]; norm_num
      _ ≤ R.eval t := by
        rw [eval_eq_sum, sum_def]
        exact Finset.single_le_sum
          (fun n _ ↦ mul_nonneg (hRnonneg n) (pow_nonneg ht.le n)) hzero_mem
  have hqeval : q.eval t ≤ 0 := by
    dsimp [q, t]
    simp only [eval_add, eval_sub, eval_one, eval_mul, eval_C, eval_X, eval_pow]
    field_simp [ne_of_gt hd]
    nlinarith
  have hReval_nonpos : R.eval t ≤ 0 := by
    change (q * P).eval t ≤ 0
    rw [eval_mul]
    exact mul_nonpos_of_nonpos_of_nonneg hqeval hPeval
  exact (not_lt_of_ge hReval_nonpos) hReval_pos

/-- The evaluation form of the numerical Golod--Shafarevich argument.  This
version is convenient for filtrations whose relation map need not be strict. -/
theorem golod_shafarevich_weighted_numeric {d r : ℝ} (hd : 0 < d)
    (P : ℝ[X]) (hPnonneg : ∀ n, 0 ≤ P.coeff n)
    (hweighted : let t := 2 / d
      1 ≤ (1 - d * t + r * t ^ 2) * P.eval t) :
    d ^ 2 < 4 * r := by
  by_contra hlt
  have hdisc : 4 * r ≤ d ^ 2 := le_of_not_gt hlt
  let t : ℝ := 2 / d
  have ht : 0 ≤ t := (div_pos (by norm_num) hd).le
  have hPeval : 0 ≤ P.eval t :=
    eval_nonneg_of_coeff_nonneg P ht hPnonneg
  have hquad : 1 - d * t + r * t ^ 2 ≤ 0 := by
    dsimp [t]
    field_simp [ne_of_gt hd]
    nlinarith
  have hnonpos : (1 - d * t + r * t ^ 2) * P.eval t ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hquad hPeval
  have := hweighted
  dsimp only at this
  linarith

end NumericalInequality

section FilteredWeights

/-- The weight of the first `N + 1` graded pieces of a finite descending
filtration, expressed recursively in terms of the dimensions of its filtered
pieces. -/
noncomputable def filteredWeight : ℕ → (ℕ → ℕ) → ℝ → ℝ
  | 0, u, _ => u 0
  | N + 1, u, t => (u 0 : ℝ) - u 1 +
      t * filteredWeight N (fun n ↦ u (n + 1)) t

theorem filteredWeight_nonneg {N : ℕ} {u : ℕ → ℕ} {t : ℝ}
    (hu : Antitone u) (ht : 0 ≤ t) : 0 ≤ filteredWeight N u t := by
  induction N generalizing u with
  | zero => simp [filteredWeight]
  | succ N ih =>
      rw [filteredWeight]
      have hdiff : 0 ≤ (u 0 : ℝ) - u 1 := by
        have hdim : u 1 ≤ u 0 := hu (Nat.zero_le 1)
        have hdim' : (u 1 : ℝ) ≤ u 0 := by
          exact_mod_cast hdim
        linarith
      have htail : Antitone (fun n ↦ u (n + 1)) := by
        intro a b hab
        exact hu (Nat.add_le_add_right hab 1)
      exact add_nonneg hdiff (mul_nonneg ht (ih htail))

theorem filteredWeight_add (N : ℕ) (u v : ℕ → ℕ) (t : ℝ) :
    filteredWeight N (fun n ↦ u n + v n) t =
      filteredWeight N u t + filteredWeight N v t := by
  induction N generalizing u v with
  | zero => simp [filteredWeight]
  | succ N ih =>
      rw [filteredWeight, filteredWeight, filteredWeight, ih]
      push_cast
      ring

theorem filteredWeight_nat_mul (N c : ℕ) (u : ℕ → ℕ) (t : ℝ) :
    filteredWeight N (fun n ↦ c * u n) t =
      c * filteredWeight N u t := by
  induction N generalizing u with
  | zero => simp [filteredWeight]
  | succ N ih =>
      rw [filteredWeight, filteredWeight, ih]
      push_cast
      ring

private theorem weighted_sum_range_succ (N : ℕ) (f : ℕ → ℝ) (t : ℝ) :
    (∑ n ∈ Finset.range (N + 1), f n * t ^ n) =
      f 0 + t * ∑ n ∈ Finset.range N, f (n + 1) * t ^ n := by
  induction N with
  | zero => simp
  | succ N ih =>
      calc
        (∑ n ∈ Finset.range (N + 1 + 1), f n * t ^ n) =
            (∑ n ∈ Finset.range (N + 1), f n * t ^ n) +
              f (N + 1) * t ^ (N + 1) := by
          rw [Finset.sum_range_succ]
        _ = (f 0 + t * ∑ n ∈ Finset.range N, f (n + 1) * t ^ n) +
              f (N + 1) * t ^ (N + 1) := by rw [ih]
        _ = f 0 + t * ∑ n ∈ Finset.range (N + 1), f (n + 1) * t ^ n := by
          rw [Finset.sum_range_succ
            (f := fun n ↦ f (n + 1) * t ^ n) N, pow_succ]
          ring

theorem filteredWeight_eq_sum_range (N : ℕ) (u : ℕ → ℕ) (t : ℝ) :
    filteredWeight N u t =
      (∑ n ∈ Finset.range N, ((u n : ℝ) - u (n + 1)) * t ^ n) +
        u N * t ^ N := by
  induction N generalizing u with
  | zero => simp [filteredWeight]
  | succ N ih =>
      rw [filteredWeight, ih, weighted_sum_range_succ]
      push_cast
      rw [pow_succ]
      ring

/-- Once a filtration has reached zero, adding one more zero graded piece
does not alter its finite weighted sum. -/
theorem filteredWeight_succ_eq_of_eq_zero (N : ℕ) (u : ℕ → ℕ) (t : ℝ)
    (hu : u (N + 1) = 0) :
    filteredWeight (N + 1) u t = filteredWeight N u t := by
  induction N generalizing u with
  | zero => simp [filteredWeight, hu]
  | succ N ih =>
      change (u 0 : ℝ) - u 1 +
          t * filteredWeight (N + 1) (fun n ↦ u (n + 1)) t =
        (u 0 : ℝ) - u 1 + t * filteredWeight N (fun n ↦ u (n + 1)) t
      rw [ih (fun n ↦ u (n + 1)) (by simpa [Nat.add_assoc] using hu)]

/-- Enlarging every positive filtered piece, while leaving the ambient
dimension fixed, can only decrease the weight when `0 ≤ t ≤ 1`. -/
theorem filteredWeight_le_of_le {N : ℕ} {u v : ℕ → ℕ} {t : ℝ}
    (huv : ∀ n, u n ≤ v n) (hzero : u 0 = v 0)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    filteredWeight N v t ≤ filteredWeight N u t := by
  have hstrong : ∀ (N : ℕ) (u v : ℕ → ℕ),
      (∀ n, u n ≤ v n) →
      -((v 0 : ℝ) - u 0) ≤ filteredWeight N u t - filteredWeight N v t := by
    intro M
    induction M with
    | zero =>
        intro u v huv
        simp [filteredWeight]
    | succ M ih =>
        intro u v huv
        rw [filteredWeight, filteredWeight]
        have htail := ih (fun n ↦ u (n + 1)) (fun n ↦ v (n + 1))
          (fun n ↦ huv (n + 1))
        have hdim : (u 1 : ℝ) ≤ v 1 := by exact_mod_cast huv 1
        nlinarith
  have h := hstrong N u v huv
  rw [hzero] at h
  linarith

end FilteredWeights

end Submission.Helpers
