import ChallengeDeps

open LeanEval.NumberTheory.GaussWantzel

namespace Submission.Helpers

def IsTwoPower (a : ℕ) : Prop := ∃ k : ℕ, a = 2 ^ k

lemma isTwoPower_one : IsTwoPower 1 := ⟨0, by simp⟩

lemma IsTwoPower.mul {a b : ℕ} (ha : IsTwoPower a) (hb : IsTwoPower b) :
    IsTwoPower (a * b) := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  exact ⟨i + j, by simp [pow_add]⟩

lemma finset_prod_isTwoPower {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, IsTwoPower (f i)) : IsTwoPower (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using isTwoPower_one
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (hf a (Finset.mem_insert_self _ _)).mul
        (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

lemma fermatPrime_factor_isTwoPower {n p : ℕ} (hn : n ≠ 0)
    (hp_support : p ∈ n.factorization.support) (hp_fermat : FermatPrime p)
    (hp_squarefree : ¬p ^ 2 ∣ n) :
    IsTwoPower (p ^ (n.factorization p - 1) * (p - 1)) := by
  have hp : p.Prime := hp_fermat.1
  have hp_pos : 0 < n.factorization p := by
    exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp_support)
  have hp_not_two_le : ¬2 ≤ n.factorization p := by
    intro h
    exact hp_squarefree ((hp.pow_dvd_iff_le_factorization hn).2 h)
  have hp_fac : n.factorization p = 1 := by omega
  obtain ⟨m, hm⟩ := hp_fermat.2
  refine ⟨2 ^ m, ?_⟩
  rw [hp_fac]
  simp [hm]

lemma gaussWantzel_isTwoPower_totient {n : ℕ} (hgw : GaussWantzelNumber n) :
    IsTwoPower n.totient := by
  have hn : n ≠ 0 := Nat.ne_of_gt hgw.1
  rw [Nat.totient_eq_prod_factorization hn]
  change IsTwoPower
    (∏ p ∈ n.factorization.support, p ^ (n.factorization p - 1) * (p - 1))
  apply finset_prod_isTwoPower
  intro p hp_support
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_support
  have hp_dvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp_support
  obtain ⟨hp_kind, hp_squarefree⟩ := hgw.2 p hp hp_dvd
  rcases hp_kind with rfl | hp_fermat
  · exact ⟨n.factorization 2 - 1, by simp⟩
  · have hp_ne_two : p ≠ 2 := by
      obtain ⟨m, hm⟩ := hp_fermat.2
      rw [hm]
      have hexp_pos : 0 < (2 : ℕ) ^ m := pow_pos (by norm_num) _
      have htwo_le : 2 ≤ (2 : ℕ) ^ (2 ^ m) := by
        rw [show 2 ^ m = (2 ^ m - 1) + 1 by omega, pow_succ]
        have htail_pos : 0 < (2 : ℕ) ^ (2 ^ m - 1) := pow_pos (by norm_num) _
        omega
      omega
    exact fermatPrime_factor_isTwoPower hn hp_support hp_fermat
      (hp_squarefree hp_ne_two)

lemma prime_sub_one_isTwoPower_of_totient {n p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ n)
    {k : ℕ} (htot : n.totient = 2 ^ k) :
    IsTwoPower (p - 1) := by
  have hpdvd_tot : p - 1 ∣ n.totient := by
    rw [← Nat.totient_prime hp]
    exact Nat.totient_dvd_of_dvd hp_dvd
  rw [htot] at hpdvd_tot
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hpdvd_tot
  exact ⟨j, hj⟩

lemma fermatPrime_of_prime_sub_one_isTwoPower {p : ℕ} (hp : p.Prime) (hp_ne_two : p ≠ 2)
    (hpow : IsTwoPower (p - 1)) : FermatPrime p := by
  obtain ⟨a, ha⟩ := hpow
  have hp_two_lt : 2 < p := lt_of_le_of_ne hp.two_le hp_ne_two.symm
  have ha_ne : a ≠ 0 := by
    intro h
    simp [h] at ha
    omega
  have hp_eq : p = 2 ^ a + 1 := by omega
  obtain ⟨m, hm⟩ := Nat.pow_of_pow_add_prime (a := 2) one_lt_two ha_ne (hp_eq ▸ hp)
  exact ⟨hp, m, by simpa [hm] using hp_eq⟩

lemma odd_prime_square_not_dvd_of_totient_isTwoPower {n p k : ℕ} (hp : p.Prime)
    (hp_ne_two : p ≠ 2) (htot : n.totient = 2 ^ k) :
    ¬p ^ 2 ∣ n := by
  intro hp_sq
  have hp_dvd_tot : p ∣ n.totient := by
    have htot_dvd := Nat.totient_dvd_of_dvd hp_sq
    have hp_dvd_phi_sq : p ∣ (p ^ 2).totient := by
      rw [Nat.totient_prime_pow hp (by omega)]
      norm_num
    exact dvd_trans hp_dvd_phi_sq htot_dvd
  rw [htot] at hp_dvd_tot
  have hp_dvd_two : p ∣ 2 := hp.dvd_of_dvd_pow hp_dvd_tot
  rcases (Nat.dvd_prime Nat.prime_two).1 hp_dvd_two with hp_one | hp_two
  · exact hp.ne_one hp_one
  · exact hp_ne_two hp_two

lemma gaussWantzel_of_isTwoPower_totient {n : ℕ} (hn : 0 < n)
    (htot : IsTwoPower n.totient) : GaussWantzelNumber n := by
  obtain ⟨k, htot⟩ := htot
  refine ⟨hn, fun p hp hp_dvd ↦ ?_⟩
  constructor
  · by_cases hp_two : p = 2
    · exact Or.inl hp_two
    · exact Or.inr <| fermatPrime_of_prime_sub_one_isTwoPower hp hp_two <|
        prime_sub_one_isTwoPower_of_totient hp hp_dvd htot
  · intro hp_two
    exact odd_prime_square_not_dvd_of_totient_isTwoPower hp hp_two htot

theorem gaussWantzel_iff_isTwoPower_totient {n : ℕ} (hn : 0 < n) :
    GaussWantzelNumber n ↔ IsTwoPower n.totient :=
  ⟨gaussWantzel_isTwoPower_totient, gaussWantzel_of_isTwoPower_totient hn⟩

end Submission.Helpers
