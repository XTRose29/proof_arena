import ChallengeDeps

open LeanEval.NumberTheory.ChebyshevSignChangeProblem
open scoped ArithmeticFunction.vonMangoldt LSeries.notation

namespace Submission.Helpers

private abbrev primeInClass (a : ZMod 4) (p : ℕ) : Prop :=
  p.Prime ∧ (p : ZMod 4) = a

lemma primeCountingMod_eq_count (a : ZMod 4) (n : ℕ) :
    primeCountingMod a n = Nat.count (primeInClass a) (n + 1) := by
  rw [primeCountingMod, Nat.count_eq_card_filter_range]

lemma infinite_primes_one_mod_four :
    {p : ℕ | primeInClass 1 p}.Infinite :=
  Nat.infinite_setOf_prime_and_eq_mod isUnit_one

lemma infinite_primes_three_mod_four :
    {p : ℕ | primeInClass 3 p}.Infinite := by
  apply Nat.infinite_setOf_prime_and_eq_mod
  exact (ZMod.isUnit_iff_coprime 3 4).2 (by norm_num)

lemma surjective_primeCountingMod_one : Function.Surjective (primeCountingMod 1) := by
  intro k
  cases k with
  | zero =>
      refine ⟨0, ?_⟩
      norm_num [primeCountingMod_eq_count, Nat.count_succ, primeInClass]
  | succ k =>
      refine ⟨Nat.nth (primeInClass 1) k, ?_⟩
      rw [primeCountingMod_eq_count, Nat.count_nth_succ_of_infinite infinite_primes_one_mod_four]

lemma surjective_primeCountingMod_three : Function.Surjective (primeCountingMod 3) := by
  intro k
  cases k with
  | zero =>
      refine ⟨0, ?_⟩
      norm_num [primeCountingMod_eq_count, Nat.count_succ, primeInClass]
  | succ k =>
      refine ⟨Nat.nth (primeInClass 3) k, ?_⟩
      rw [primeCountingMod_eq_count,
        Nat.count_nth_succ_of_infinite infinite_primes_three_mod_four]

private lemma primeCountingMod_eq_count_add_ite (a : ZMod 4) (n : ℕ) :
    primeCountingMod a n =
      Nat.count (primeInClass a) n + if primeInClass a n then 1 else 0 := by
  rw [primeCountingMod_eq_count, Nat.count_succ]

lemma chebyshevLead_infinite_or_reverse_infinite :
    chebyshevLead.Infinite ∨
      {n : ℕ | primeCountingMod 3 n < primeCountingMod 1 n}.Infinite := by
  by_contra h
  push Not at h
  let reverseLead : Set ℕ := {n : ℕ | primeCountingMod 3 n < primeCountingMod 1 n}
  have hfinite : (chebyshevLead ∪ Nat.succ '' reverseLead).Finite :=
    h.1.union (h.2.image Nat.succ)
  obtain ⟨p, hp, hp_not_mem⟩ :=
    infinite_primes_three_mod_four.exists_notMem_finite hfinite
  change primeInClass 3 p at hp
  have hp_pos : 0 < p := hp.1.pos
  have hp_not_one : ¬primeInClass 1 p := by
    intro hp_one
    have : (3 : ZMod 4) = 1 := hp.2.symm.trans hp_one.2
    have hne : (3 : ZMod 4) ≠ 1 := by decide
    exact hne this
  have hp_not_lead : p ∉ chebyshevLead := by
    intro hp_lead
    exact hp_not_mem (Set.mem_union_left _ hp_lead)
  have hp_count_one : primeCountingMod 1 p = Nat.count (primeInClass 1) p := by
    rw [primeCountingMod_eq_count_add_ite, if_neg hp_not_one, add_zero]
  have hp_count_three : primeCountingMod 3 p = Nat.count (primeInClass 3) p + 1 := by
    rw [primeCountingMod_eq_count_add_ite, if_pos hp]
  have hpred_count_one :
      primeCountingMod 1 (p - 1) = Nat.count (primeInClass 1) p := by
    rw [primeCountingMod_eq_count]
    congr 1
    omega
  have hpred_count_three :
      primeCountingMod 3 (p - 1) = Nat.count (primeInClass 3) p := by
    rw [primeCountingMod_eq_count]
    congr 1
    omega
  have hpred_reverse : p - 1 ∈ reverseLead := by
    change primeCountingMod 3 (p - 1) < primeCountingMod 1 (p - 1)
    rw [hpred_count_one, hpred_count_three]
    rw [chebyshevLead, Set.mem_setOf_eq, hp_count_one, hp_count_three] at hp_not_lead
    omega
  apply hp_not_mem
  apply Set.mem_union_right chebyshevLead
  refine ⟨p - 1, hpred_reverse, ?_⟩
  omega

/-- The signed difference between the two residue-class prime counts. -/
noncomputable def primeRace (n : ℕ) : ℤ :=
  primeCountingMod 3 n - primeCountingMod 1 n

/-- The partial sum of the nontrivial quadratic character modulo four over primes. -/
def characterPrimeSum (n : ℕ) : ℤ :=
  ∑ p ∈ Finset.range (n + 1), if p.Prime then ZMod.χ₄ p else 0

private lemma class_indicator_sub_eq_neg_character (p : ℕ) :
    (if primeInClass 3 p then (1 : ℤ) else 0) -
        (if primeInClass 1 p then (1 : ℤ) else 0) =
      -(if p.Prime then ZMod.χ₄ p else 0) := by
  change (if p.Prime ∧ (p : ZMod 4) = 3 then (1 : ℤ) else 0) -
      (if p.Prime ∧ (p : ZMod 4) = 1 then (1 : ℤ) else 0) =
    -(if p.Prime then ZMod.χ₄ (p : ZMod 4) else 0)
  by_cases hp : p.Prime
  · simp only [hp, true_and, if_true]
    generalize (p : ZMod 4) = x
    fin_cases x <;> decide
  · simp [hp]

lemma primeRace_eq_neg_characterPrimeSum (n : ℕ) :
    primeRace n = -characterPrimeSum n := by
  classical
  unfold primeRace primeCountingMod characterPrimeSum
  rw [Finset.natCast_card_filter, Finset.natCast_card_filter,
    ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  exact class_indicator_sub_eq_neg_character p

/-- The nontrivial complex Dirichlet character modulo four. -/
noncomputable def chiFour : DirichletCharacter ℂ 4 :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

lemma chiFour_odd : chiFour.Odd := by
  change ((ZMod.χ₄ (-1 : ZMod 4) : ℤ) : ℂ) = -1
  rw [show (-1 : ZMod 4) = 3 by decide]
  norm_num [ZMod.χ₄]

lemma chiFour_ne_one : chiFour ≠ 1 := by
  intro h
  have hodd : (1 : DirichletCharacter ℂ 4).Odd := by
    simpa [h] using chiFour_odd
  have heven : (1 : DirichletCharacter ℂ 4).Even := by
    rw [DirichletCharacter.Even]
    exact MulChar.one_apply isUnit_one.neg
  exact (DirichletCharacter.not_even_and_odd (1 : DirichletCharacter ℂ 4)) ⟨heven, hodd⟩

private lemma chiFour_not_factorsThrough_two :
    ¬chiFour.FactorsThrough 2 := by
  rintro ⟨hdiv, ψ, hψ⟩
  have h1 : chiFour (1 : ℤ) = ψ (1 : ℤ) := by
    rw [hψ, DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ hdiv]
    norm_num
  have h3 : chiFour (3 : ℤ) = ψ (3 : ℤ) := by
    rw [hψ, DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ hdiv]
    norm_num
  have h13 : ψ (1 : ℤ) = ψ (3 : ℤ) := by
    exact congrArg ψ (by decide : ((1 : ℤ) : ZMod 2) = ((3 : ℤ) : ZMod 2))
  have := h1.trans (h13.trans h3.symm)
  have hchi1 : chiFour (1 : ℤ) = 1 := by norm_num [chiFour, ZMod.χ₄]
  have hchi3 : chiFour (3 : ℤ) = -1 := by norm_num [chiFour, ZMod.χ₄]
  rw [hchi1, hchi3] at this
  norm_num at this

lemma chiFour_isPrimitive : chiFour.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  have hcond_dvd : chiFour.conductor ∣ 4 :=
    DirichletCharacter.conductor_dvd_level chiFour
  have hcond_pos : 0 < chiFour.conductor :=
    Nat.pos_of_ne_zero (DirichletCharacter.conductor_ne_zero chiFour)
  have hcond_le : chiFour.conductor ≤ 4 := Nat.le_of_dvd (by norm_num) hcond_dvd
  interval_cases hcond : chiFour.conductor
  · exact (chiFour_ne_one <|
      (DirichletCharacter.eq_one_iff_conductor_eq_one).2 hcond).elim
  · exact (chiFour_not_factorsThrough_two <| by
      simpa [hcond] using DirichletCharacter.factorsThrough_conductor chiFour).elim
  · norm_num [hcond] at hcond_dvd
  · rfl

lemma chiFour_isQuadratic : chiFour.IsQuadratic :=
  ZMod.isQuadratic_χ₄.comp (Int.castRingHom ℂ)

lemma chiFour_inv : chiFour⁻¹ = chiFour :=
  chiFour_isQuadratic.inv

lemma chiFour_completedLFunction_one_sub (s : ℂ) :
    DirichletCharacter.completedLFunction chiFour (1 - s) =
      4 ^ (s - 1 / 2) * DirichletCharacter.rootNumber chiFour *
        DirichletCharacter.completedLFunction chiFour s := by
  simpa [chiFour_inv] using chiFour_isPrimitive.completedLFunction_one_sub s

lemma differentiable_chiFour_LFunction :
    Differentiable ℂ (DirichletCharacter.LFunction chiFour) :=
  DirichletCharacter.differentiable_LFunction chiFour_ne_one

lemma chiFour_LFunction_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    DirichletCharacter.LFunction chiFour s ≠ 0 :=
  DirichletCharacter.LFunction_ne_zero_of_one_le_re chiFour (.inl chiFour_ne_one) hs

lemma chiFour_LSeries_twist_vonMangoldt_eq {s : ℂ} (hs : 1 < s.re) :
    L (↗chiFour * ↗Λ) s = -deriv (L ↗chiFour) s / L ↗chiFour s :=
  DirichletCharacter.LSeries_twist_vonMangoldt_eq chiFour hs

lemma chiFour_LFunction_neg_one :
    DirichletCharacter.LFunction chiFour (-1) = 0 := by
  simpa using chiFour_odd.LFunction_neg_two_mul_nat_sub_one 0

lemma chebyshevLead_infinite_of_race_positive
    (h : ∀ N : ℕ, ∃ n > N, 0 < primeRace n) : chebyshevLead.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro N
  obtain ⟨n, hN, hn⟩ := h N
  refine ⟨n, ?_, hN⟩
  change primeCountingMod 1 n < primeCountingMod 3 n
  unfold primeRace at hn
  omega

lemma reverse_infinite_of_race_negative
    (h : ∀ N : ℕ, ∃ n > N, primeRace n < 0) :
    {n : ℕ | primeCountingMod 3 n < primeCountingMod 1 n}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro N
  obtain ⟨n, hN, hn⟩ := h N
  refine ⟨n, ?_, hN⟩
  change primeCountingMod 3 n < primeCountingMod 1 n
  unfold primeRace at hn
  omega

lemma chebyshev_sign_change_of_race_oscillation
    (hpos : ∀ N : ℕ, ∃ n > N, 0 < primeRace n)
    (hneg : ∀ N : ℕ, ∃ n > N, primeRace n < 0) :
    chebyshevLead.Infinite ∧
      {n : ℕ | primeCountingMod 3 n < primeCountingMod 1 n}.Infinite :=
  ⟨chebyshevLead_infinite_of_race_positive hpos,
    reverse_infinite_of_race_negative hneg⟩

end Submission.Helpers
