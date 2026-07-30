import Submission.OddOrder.PF.Section01.IntegralLattice

/-!
# The column-pivot lemma

This file ports the combinatorial core of `PFsection3.v`, replacing the
source's private reflection language by statements directly about the free
integral lattice.  A vector of norm three is a signed three-element support.
The proof below works with those supports and their pairings.
-/

namespace Submission.OddOrder.PF

open Finsupp

noncomputable section

private theorem isSign_sq {a : ℤ} (ha : IsSign a) : a * a = 1 := by
  rcases ha with rfl | rfl <;> norm_num

private theorem isSign_neg {a : ℤ} (ha : IsSign a) : IsSign (-a) := by
  rcases ha with rfl | rfl <;> simp [IsSign]

/-- A vector of squared norm three has exactly three signed coordinates. -/
private theorem eq_sum_three_signed_singles_of_normSq_eq_three
    {κ : Type*} (f : IntegralLattice κ) (hf : normSq f = 3) :
    ∃ a b c ε δ γ,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      IsSign ε ∧ IsSign δ ∧ IsSign γ ∧
      f = single a ε + single b δ + single c γ := by
  classical
  induction f using Finsupp.induction with
  | zero =>
      simp [normSq, coeffDot] at hf
  | single_add i x f hi hx ih =>
      rw [normSq_single_add i x f hi] at hf
      have hx_lt : x ^ 2 < 4 := by
        linarith [normSq_nonneg f]
      have hx_sq : x ^ 2 = 1 := Int.sq_eq_one_of_sq_lt_four hx_lt hx
      have hf_two : normSq f = 2 := by
        linarith
      obtain ⟨j, k, δ, γ, hjk, hδ, hγ, rfl⟩ :=
        eq_sum_signed_singles_of_normSq_eq_two f hf_two
      have hij : i ≠ j := by
        intro h
        subst j
        apply hi
        simp [Finsupp.mem_support_iff, hjk, isSign_ne_zero hδ]
      have hik : i ≠ k := by
        intro h
        subst k
        apply hi
        simp [Finsupp.mem_support_iff, hij, isSign_ne_zero hγ]
      exact ⟨i, j, k, x, δ, γ, hij, hik, hjk,
        isSign_iff_sq_eq_one.mpr hx_sq, hδ, hγ, by simp [add_assoc]⟩

private theorem normSq_sum_three_signed_singles
    {κ : Type*} [DecidableEq κ]
    {a b c : κ} {ha : a ≠ b} {hac : a ≠ c} {hbc : b ≠ c}
    {ε δ γ : ℤ} (hε : IsSign ε) (hδ : IsSign δ) (hγ : IsSign γ) :
    normSq (single a ε + single b δ + single c γ : IntegralLattice κ) = 3 := by
  simp [normSq, coeffDot_add_left, coeffDot_add_right, ha, hac, hbc,
    isSign_sq hε, isSign_sq hδ, isSign_sq hγ]

/-- Three prescribed signed coefficients exhaust a norm-three vector. -/
private theorem eq_sum_three_of_signed_coefficients
    {κ : Type*} [DecidableEq κ]
    (f : IntegralLattice κ) {a b c : κ}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {ε δ γ : ℤ} (hε : IsSign ε) (hδ : IsSign δ) (hγ : IsSign γ)
    (hf : normSq f = 3) (hfa : f a = ε) (hfb : f b = δ) (hfc : f c = γ) :
    f = single a ε + single b δ + single c γ := by
  let s : IntegralLattice κ := single a ε + single b δ + single c γ
  have hs : normSq s = 3 :=
    normSq_sum_three_signed_singles (ha := hab) (hac := hac) (hbc := hbc) hε hδ hγ
  have hfs : coeffDot f s = 3 := by
    simp [s, coeffDot_add_right, hfa, hfb, hfc,
      isSign_sq hε, isSign_sq hδ, isSign_sq hγ]
  have hsf : coeffDot s f = 3 := by simpa [coeffDot_comm] using hfs
  have hff : coeffDot f f = 3 := hf
  have hss : coeffDot s s = 3 := hs
  have hz : normSq (f - s) = 0 := by
    simp only [sub_eq_add_neg, normSq, coeffDot_add_left, coeffDot_add_right,
      coeffDot_neg_left, coeffDot_neg_right, hff, hss, hfs, hsf]
    norm_num
  have : f - s = 0 := (normSq_eq_zero_iff (f - s)).mp hz
  exact sub_eq_zero.mp this

private theorem coeff_mem_sign_or_zero_of_normSq_eq_three
    {κ : Type*} [DecidableEq κ]
    (f : IntegralLattice κ) (hf : normSq f = 3) (q : κ) :
    f q = -1 ∨ f q = 0 ∨ f q = 1 := by
  obtain ⟨a, b, c, ε, δ, γ, hab, hac, hbc, hε, hδ, hγ, rfl⟩ :=
    eq_sum_three_signed_singles_of_normSq_eq_three f hf
  rcases hε with rfl | rfl <;>
    rcases hδ with rfl | rfl <;>
    rcases hγ with rfl | rfl <;>
    by_cases hqa : q = a <;>
    by_cases hqb : q = b <;>
    by_cases hqc : q = c <;>
    subst_vars <;> simp_all

private theorem sign_mul_coeff_mem_sign_or_zero_of_normSq_eq_three
    {κ : Type*} [DecidableEq κ]
    (f : IntegralLattice κ) (hf : normSq f = 3) (q : κ)
    {ε : ℤ} (hε : IsSign ε) :
    ε * f q = -1 ∨ ε * f q = 0 ∨ ε * f q = 1 := by
  rcases coeff_mem_sign_or_zero_of_normSq_eq_three f hf q with h | h | h <;>
    rcases hε with rfl | rfl <;> simp_all

private theorem eq_of_sign_mul_eq_one
    {a b : ℤ} (ha : IsSign a) (h : a * b = 1) : b = a := by
  rcases ha with rfl | rfl <;> omega

private theorem eq_neg_of_sign_mul_eq_neg_one
    {a b : ℤ} (ha : IsSign a) (h : a * b = -1) : b = -a := by
  rcases ha with rfl | rfl <;> omega

private theorem eq_zero_of_sign_mul_eq_zero
    {a b : ℤ} (ha : IsSign a) (h : a * b = 0) : b = 0 := by
  exact (mul_eq_zero.mp h).resolve_left (isSign_ne_zero ha)

/-- An opposite signed coordinate cannot occur in two entries on a line.

The perpendicular entry supplies the parity contradiction.  This is the
direct integral-lattice content of the small source lemma `unsat_J`. -/
private theorem no_opposite_first
    {κ : Type*} [DecidableEq κ]
    (a b d : IntegralLattice κ)
    {q₁ q₂ q₃ : κ} (hq₁₂ : q₁ ≠ q₂) (hq₁₃ : q₁ ≠ q₃)
    (hq₂₃ : q₂ ≠ q₃) {ε₁ ε₂ ε₃ : ℤ}
    (hε₁ : IsSign ε₁) (hε₂ : IsSign ε₂) (hε₃ : IsSign ε₃)
    (ha : a = single q₁ ε₁ + single q₂ ε₂ + single q₃ ε₃)
    (hnb : normSq b = 3)
    (hab : coeffDot a b = 1) (had : coeffDot a d = 1)
    (hbd : coeffDot b d = 0) :
    ε₁ * b q₁ ≠ -1 := by
  intro hop
  have hab' : ε₁ * b q₁ + ε₂ * b q₂ + ε₃ * b q₃ = 1 := by
    rw [ha] at hab
    simpa [coeffDot_add_left] using hab
  have ht₂ :=
    sign_mul_coeff_mem_sign_or_zero_of_normSq_eq_three b hnb q₂ hε₂
  have ht₃ :=
    sign_mul_coeff_mem_sign_or_zero_of_normSq_eq_three b hnb q₃ hε₃
  have ht₂one : ε₂ * b q₂ = 1 := by rcases ht₂ with h | h | h <;> omega
  have ht₃one : ε₃ * b q₃ = 1 := by rcases ht₃ with h | h | h <;> omega
  have hbq₁ : b q₁ = -ε₁ := eq_neg_of_sign_mul_eq_neg_one hε₁ hop
  have hbq₂ : b q₂ = ε₂ := eq_of_sign_mul_eq_one hε₂ ht₂one
  have hbq₃ : b q₃ = ε₃ := eq_of_sign_mul_eq_one hε₃ ht₃one
  have hb : b = single q₁ (-ε₁) + single q₂ ε₂ + single q₃ ε₃ :=
    eq_sum_three_of_signed_coefficients b hq₁₂ hq₁₃ hq₂₃
      (isSign_neg hε₁) hε₂ hε₃ hnb hbq₁ hbq₂ hbq₃
  have had' : ε₁ * d q₁ + ε₂ * d q₂ + ε₃ * d q₃ = 1 := by
    rw [ha] at had
    simpa [coeffDot_add_left] using had
  have hbd' : (-ε₁) * d q₁ + ε₂ * d q₂ + ε₃ * d q₃ = 0 := by
    rw [hb] at hbd
    simpa [coeffDot_add_left, coeffDot_neg_left] using hbd
  have hbd'' : -(ε₁ * d q₁) + ε₂ * d q₂ + ε₃ * d q₃ = 0 := by
    calc
      -(ε₁ * d q₁) + ε₂ * d q₂ + ε₃ * d q₃ =
          (-ε₁) * d q₁ + ε₂ * d q₂ + ε₃ * d q₃ := by ring
      _ = 0 := hbd'
  omega

/-- Two norm-three entries in one row or column have one, and only one,
common signed coordinate, provided there is an entry on a perpendicular line.
-/
private theorem line_meets_in_one_signed_coordinate
    {κ : Type*} [DecidableEq κ]
    (a b d : IntegralLattice κ)
    (hna : normSq a = 3) (hnb : normSq b = 3)
    (hab : coeffDot a b = 1) (had : coeffDot a d = 1)
    (hbd : coeffDot b d = 0) :
    ∃ q₁ q₂ q₃ ε₁ ε₂ ε₃,
      q₁ ≠ q₂ ∧ q₁ ≠ q₃ ∧ q₂ ≠ q₃ ∧
      IsSign ε₁ ∧ IsSign ε₂ ∧ IsSign ε₃ ∧
      a = single q₁ ε₁ + single q₂ ε₂ + single q₃ ε₃ ∧
      b q₁ = ε₁ ∧ b q₂ = 0 ∧ b q₃ = 0 := by
  obtain ⟨q₁, q₂, q₃, ε₁, ε₂, ε₃,
      hq₁₂, hq₁₃, hq₂₃, hε₁, hε₂, hε₃, ha⟩ :=
    eq_sum_three_signed_singles_of_normSq_eq_three a hna
  let t₁ := ε₁ * b q₁
  let t₂ := ε₂ * b q₂
  let t₃ := ε₃ * b q₃
  have ht₁ := sign_mul_coeff_mem_sign_or_zero_of_normSq_eq_three b hnb q₁ hε₁
  have ht₂ := sign_mul_coeff_mem_sign_or_zero_of_normSq_eq_three b hnb q₂ hε₂
  have ht₃ := sign_mul_coeff_mem_sign_or_zero_of_normSq_eq_three b hnb q₃ hε₃
  have hsum : t₁ + t₂ + t₃ = 1 := by
    rw [ha] at hab
    simpa [t₁, t₂, t₃, coeffDot_add_left] using hab
  have hn₁ : t₁ ≠ -1 :=
    no_opposite_first a b d hq₁₂ hq₁₃ hq₂₃ hε₁ hε₂ hε₃
      ha hnb hab had hbd
  have hn₂ : t₂ ≠ -1 := by
    apply no_opposite_first a b d hq₁₂.symm hq₂₃ hq₁₃ hε₂ hε₁ hε₃
      (by simpa [add_left_comm, add_comm, add_assoc] using ha) hnb hab had hbd
  have hn₃ : t₃ ≠ -1 := by
    apply no_opposite_first a b d hq₁₃.symm hq₂₃.symm hq₁₂ hε₃ hε₁ hε₂
      (by simpa [add_left_comm, add_comm, add_assoc] using ha) hnb hab had hbd
  have ht₁b : -1 ≤ t₁ ∧ t₁ ≤ 1 := by
    rcases ht₁ with h | h | h <;> constructor <;> dsimp [t₁] <;> omega
  have ht₂b : -1 ≤ t₂ ∧ t₂ ≤ 1 := by
    rcases ht₂ with h | h | h <;> constructor <;> dsimp [t₂] <;> omega
  have ht₃b : -1 ≤ t₃ ∧ t₃ ≤ 1 := by
    rcases ht₃ with h | h | h <;> constructor <;> dsimp [t₃] <;> omega
  have ht₁n : 0 ≤ t₁ := by omega
  have ht₂n : 0 ≤ t₂ := by omega
  have ht₃n : 0 ≤ t₃ := by omega
  have hcases : t₁ = 1 ∨ t₂ = 1 ∨ t₃ = 1 := by
    omega
  rcases hcases with h₁ | h₂ | h₃
  · have h₂z : t₂ = 0 := by
      omega
    have h₃z : t₃ = 0 := by omega
    exact ⟨q₁, q₂, q₃, ε₁, ε₂, ε₃,
      hq₁₂, hq₁₃, hq₂₃, hε₁, hε₂, hε₃, ha,
      eq_of_sign_mul_eq_one hε₁ h₁,
      eq_zero_of_sign_mul_eq_zero hε₂ h₂z,
      eq_zero_of_sign_mul_eq_zero hε₃ h₃z⟩
  · have h₁z : t₁ = 0 := by
      omega
    have h₃z : t₃ = 0 := by omega
    exact ⟨q₂, q₁, q₃, ε₂, ε₁, ε₃,
      hq₁₂.symm, hq₂₃, hq₁₃, hε₂, hε₁, hε₃,
      by simpa [add_left_comm, add_comm, add_assoc] using ha,
      eq_of_sign_mul_eq_one hε₂ h₂,
      eq_zero_of_sign_mul_eq_zero hε₁ h₁z,
      eq_zero_of_sign_mul_eq_zero hε₃ h₃z⟩
  · have h₁z : t₁ = 0 := by
      omega
    have h₂z : t₂ = 0 := by omega
    exact ⟨q₃, q₁, q₂, ε₃, ε₁, ε₂,
      hq₁₃.symm, hq₂₃.symm, hq₁₂, hε₃, hε₁, hε₂,
      by simpa [add_left_comm, add_comm, add_assoc] using ha,
      eq_of_sign_mul_eq_one hε₃ h₃,
      eq_zero_of_sign_mul_eq_zero hε₁ h₁z,
      eq_zero_of_sign_mul_eq_zero hε₂ h₂z⟩

private theorem support_card_eq_three_of_normSq_eq_three
    {κ : Type*} [DecidableEq κ]
    (f : IntegralLattice κ) (hf : normSq f = 3) : f.support.card = 3 := by
  obtain ⟨a, b, c, ε, δ, γ, hab, hac, hbc, hε, hδ, hγ, rfl⟩ :=
    eq_sum_three_signed_singles_of_normSq_eq_three f hf
  have hε₀ := isSign_ne_zero hε
  have hδ₀ := isSign_ne_zero hδ
  have hγ₀ := isSign_ne_zero hγ
  classical
  have hsupp :
      (single a ε + single b δ + single c γ : IntegralLattice κ).support = {a, b, c} := by
    ext q
    by_cases hqa : q = a <;> by_cases hqb : q = b <;> by_cases hqc : q = c <;>
      subst_vars <;> simp_all [Finsupp.mem_support_iff]
  rw [hsupp]
  simp [hab, hac, hbc]

private theorem at_most_three_nonzero
    {κ : Type*} [DecidableEq κ]
    (f : IntegralLattice κ) (hf : normSq f = 3)
    {a b c d : κ}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    f a = 0 ∨ f b = 0 ∨ f c = 0 ∨ f d = 0 := by
  by_contra h
  push_neg at h
  rcases h with ⟨ha₀, hb₀, hc₀, hd₀⟩
  have hs : ({a, b, c, d} : Finset κ) ⊆ f.support := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · simpa [Finsupp.mem_support_iff] using ha₀
    · simpa [Finsupp.mem_support_iff] using hb₀
    · simpa [Finsupp.mem_support_iff] using hc₀
    · simpa [Finsupp.mem_support_iff] using hd₀
  have hc := Finset.card_le_card hs
  rw [support_card_eq_three_of_normSq_eq_three f hf] at hc
  have : ({a, b, c, d} : Finset κ).card = 4 := by
    simp [hab, hac, had, hbc, hbd, hcd]
  omega

/-- Two distinct signed coefficients in a norm-three vector leave one signed
coordinate. -/
private theorem complete_two_signed_coefficients
    {κ : Type*} [DecidableEq κ]
    (f : IntegralLattice κ) (hf : normSq f = 3)
    {a b : κ} (hab : a ≠ b) {ε δ : ℤ}
    (hε : IsSign ε) (hδ : IsSign δ)
    (hfa : f a = ε) (hfb : f b = δ) :
    ∃ c γ, a ≠ c ∧ b ≠ c ∧ IsSign γ ∧
      f = single a ε + single b δ + single c γ := by
  let s : IntegralLattice κ := single a ε + single b δ
  have hss : coeffDot s s = 2 := by
    simp [s, coeffDot_add_left, coeffDot_add_right, hab,
      isSign_sq hε, isSign_sq hδ]
  have hfs : coeffDot f s = 2 := by
    simp [s, coeffDot_add_right, hfa, hfb, isSign_sq hε, isSign_sq hδ]
  have hsf : coeffDot s f = 2 := by simpa [coeffDot_comm] using hfs
  have hff : coeffDot f f = 3 := hf
  have hg : normSq (f - s) = 1 := by
    simp only [sub_eq_add_neg, normSq, coeffDot_add_left, coeffDot_add_right,
      coeffDot_neg_left, coeffDot_neg_right, hff, hss, hfs, hsf]
    norm_num
  obtain ⟨c, γ, hγ, hc⟩ := eq_signed_single_of_normSq_eq_one (f - s) hg
  have hrepr : f = single a ε + single b δ + single c γ := by
    calc
      f = s + (f - s) := by abel
      _ = s + single c γ := by rw [hc]
      _ = single a ε + single b δ + single c γ := rfl
  have hac : a ≠ c := by
    intro h
    subst c
    rw [hrepr] at hfa
    simp [hab, isSign_ne_zero hγ] at hfa
  have hbc : b ≠ c := by
    intro h
    subst c
    rw [hrepr] at hfb
    simp [hab, isSign_ne_zero hγ] at hfb
  exact ⟨c, γ, hac, hbc, hγ, hrepr⟩

private theorem complete_one_signed_coefficient
    {κ : Type*} [DecidableEq κ]
    (f : IntegralLattice κ) (hf : normSq f = 3)
    (a : κ) {ε : ℤ} (hε : IsSign ε) (hfa : f a = ε) :
    ∃ b c δ γ, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      IsSign δ ∧ IsSign γ ∧
      f = single a ε + single b δ + single c γ := by
  let s : IntegralLattice κ := single a ε
  have hss : coeffDot s s = 1 := by simp [s, isSign_sq hε]
  have hfs : coeffDot f s = 1 := by simp [s, hfa, isSign_sq hε]
  have hsf : coeffDot s f = 1 := by simpa [coeffDot_comm] using hfs
  have hff : coeffDot f f = 3 := hf
  have hg : normSq (f - s) = 2 := by
    simp only [sub_eq_add_neg, normSq, coeffDot_add_left, coeffDot_add_right,
      coeffDot_neg_left, coeffDot_neg_right, hff, hss, hfs, hsf]
    norm_num
  obtain ⟨b, c, δ, γ, hbc, hδ, hγ, hg'⟩ :=
    eq_sum_signed_singles_of_normSq_eq_two (f - s) hg
  have hrepr : f = single a ε + single b δ + single c γ := by
    calc
      f = s + (f - s) := by abel
      _ = s + (single b δ + single c γ) := by rw [hg']
      _ = single a ε + single b δ + single c γ := by simp [s, add_assoc]
  have hab : a ≠ b := by
    intro h
    subst b
    rw [hrepr] at hfa
    simp [hbc, isSign_ne_zero hδ] at hfa
  have hac : a ≠ c := by
    intro h
    subst c
    rw [hrepr] at hfa
    simp [hbc, isSign_ne_zero hγ] at hfa
  exact ⟨b, c, δ, γ, hab, hac, hbc, hδ, hγ, hrepr⟩

private theorem line_normalized_coefficients_onehot
    {κ : Type*} [DecidableEq κ]
    (a b d : IntegralLattice κ)
    {q₁ q₂ q₃ : κ} (hq₁₂ : q₁ ≠ q₂) (hq₁₃ : q₁ ≠ q₃)
    (hq₂₃ : q₂ ≠ q₃) {ε₁ ε₂ ε₃ : ℤ}
    (hε₁ : IsSign ε₁) (hε₂ : IsSign ε₂) (hε₃ : IsSign ε₃)
    (ha : a = single q₁ ε₁ + single q₂ ε₂ + single q₃ ε₃)
    (hnb : normSq b = 3)
    (hab : coeffDot a b = 1) (had : coeffDot a d = 1)
    (hbd : coeffDot b d = 0) :
    let t₁ := ε₁ * b q₁
    let t₂ := ε₂ * b q₂
    let t₃ := ε₃ * b q₃
    (t₁ = 0 ∨ t₁ = 1) ∧ (t₂ = 0 ∨ t₂ = 1) ∧
      (t₃ = 0 ∨ t₃ = 1) ∧ t₁ + t₂ + t₃ = 1 := by
  have ht₁ := sign_mul_coeff_mem_sign_or_zero_of_normSq_eq_three b hnb q₁ hε₁
  have ht₂ := sign_mul_coeff_mem_sign_or_zero_of_normSq_eq_three b hnb q₂ hε₂
  have ht₃ := sign_mul_coeff_mem_sign_or_zero_of_normSq_eq_three b hnb q₃ hε₃
  have hn₁ := no_opposite_first a b d hq₁₂ hq₁₃ hq₂₃
    hε₁ hε₂ hε₃ ha hnb hab had hbd
  have hn₂ := no_opposite_first a b d hq₁₂.symm hq₂₃ hq₁₃
    hε₂ hε₁ hε₃
    (by simpa [add_left_comm, add_comm, add_assoc] using ha) hnb hab had hbd
  have hn₃ := no_opposite_first a b d hq₁₃.symm hq₂₃.symm hq₁₂
    hε₃ hε₁ hε₂
    (by simpa [add_left_comm, add_comm, add_assoc] using ha) hnb hab had hbd
  have hs : ε₁ * b q₁ + ε₂ * b q₂ + ε₃ * b q₃ = 1 := by
    rw [ha] at hab
    simpa [coeffDot_add_left] using hab
  rcases ht₁ with h | h | h <;> rcases ht₂ with h' | h' | h' <;>
    rcases ht₃ with h'' | h'' | h'' <;> omega

/-- A convenient support-level form of `line_meets_in_one_signed_coordinate`. -/
private theorem line_common_coordinate_unique
    {κ : Type*} [DecidableEq κ]
    (a b d : IntegralLattice κ)
    (hna : normSq a = 3) (hnb : normSq b = 3)
    (hab : coeffDot a b = 1) (had : coeffDot a d = 1)
    (hbd : coeffDot b d = 0) :
    ∃ q ε, IsSign ε ∧ a q = ε ∧ b q = ε ∧
      ∀ p, a p ≠ 0 → b p ≠ 0 → p = q := by
  obtain ⟨q₁, q₂, q₃, ε₁, ε₂, ε₃,
      hq₁₂, hq₁₃, hq₂₃, hε₁, hε₂, hε₃,
      ha, hbq₁, hbq₂, hbq₃⟩ :=
    line_meets_in_one_signed_coordinate a b d hna hnb hab had hbd
  refine ⟨q₁, ε₁, hε₁, ?_, hbq₁, ?_⟩
  · simp [ha, hq₁₂, hq₁₃, hq₂₃, isSign_ne_zero hε₁]
  · intro p hap hbp
    have hp : p = q₁ ∨ p = q₂ ∨ p = q₃ := by
      by_contra h
      push_neg at h
      rw [ha] at hap
      simp [h.1, h.2.1, h.2.2] at hap
    rcases hp with rfl | rfl | rfl
    · rfl
    · exact (hbp hbq₂).elim
    · exact (hbp hbq₃).elim

private abbrev signedBasis {κ : Type*} [DecidableEq κ]
    (q : Fin 7 → κ) (ε : Fin 7 → ℤ) (i : Fin 7) : IntegralLattice κ :=
  single (q i) (ε i)

/-- The six-point (Pasch) alternative for four entries on a line has no
perpendicular dual entry. -/
private theorem no_pasched_dual
    {κ : Type*} [DecidableEq κ]
    (q : Fin 7 → κ) (ε : Fin 7 → ℤ)
    (f : IntegralLattice κ)
    (h₀ : coeffDot
      (signedBasis q ε 0 + signedBasis q ε 1 + signedBasis q ε 2) f = 1)
    (h₁ : coeffDot
      (signedBasis q ε 0 + signedBasis q ε 3 + signedBasis q ε 4) f = 0)
    (h₂ : coeffDot
      (signedBasis q ε 1 + signedBasis q ε 3 + signedBasis q ε 5) f = 0)
    (h₃ : coeffDot
      (signedBasis q ε 2 + signedBasis q ε 4 + signedBasis q ε 5) f = 0) :
    False := by
  simp only [signedBasis, coeffDot_add_left, coeffDot_single_left] at h₀ h₁ h₂ h₃
  omega

private theorem sum_normalized_coeff_sq_le_normSq
    {n : ℕ} {κ : Type*} [DecidableEq κ]
    (q : Fin n → κ) (hq : Function.Injective q)
    (ε : Fin n → ℤ) (hε : ∀ i, IsSign (ε i))
    (f : IntegralLattice κ) :
    ∑ i, (ε i * f (q i)) ^ 2 ≤ normSq f := by
  classical
  have himage :
      ∑ i, f (q i) ^ 2 = ∑ x ∈ Finset.image q Finset.univ, f x ^ 2 := by
    rw [Finset.sum_image]
    intro i _ j _ hij
    exact hq hij
  calc
    ∑ i, (ε i * f (q i)) ^ 2 = ∑ i, f (q i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_pow, show (ε i) ^ 2 = 1 by simpa [pow_two] using isSign_sq (hε i)]
      simp
    _ = ∑ x ∈ Finset.image q Finset.univ, f x ^ 2 := himage
    _ ≤ ∑ x ∈ Finset.image q Finset.univ ∪ f.support, f x ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      intro x _ _
      positivity
    _ = ∑ x ∈ f.support, f x ^ 2 := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro x hx hxs
      have : f x = 0 := by simpa [Finsupp.mem_support_iff] using hxs
      simp [this]
    _ = normSq f := (normSq_eq_sum f).symm

set_option maxHeartbeats 2000000 in
private theorem d2_dual_zero_coefficients
    {κ : Type*} [DecidableEq κ]
    (q : Fin 7 → κ) (hq : Function.Injective q)
    (ε : Fin 7 → ℤ) (hε : ∀ i, IsSign (ε i))
    (f : IntegralLattice κ) (hf : normSq f = 3)
    (h₀ : coeffDot
      (signedBasis q ε 0 + signedBasis q ε 1 + signedBasis q ε 2) f = 1)
    (h₁ : coeffDot
      (signedBasis q ε 0 + signedBasis q ε 3 + signedBasis q ε 4) f = 0)
    (h₂ : coeffDot
      (signedBasis q ε 1 + signedBasis q ε 3 + signedBasis q ε 5) f = 0)
    (h₃ : coeffDot
      (signedBasis q ε 2 + signedBasis q ε 3 + signedBasis q ε 6) f = 0) :
    let t := fun i : Fin 7 ↦ ε i * f (q i)
    (t 0 = 1 ∧ t 1 = 0 ∧ t 2 = 0 ∧ t 3 = 0 ∧
        t 4 = -1 ∧ t 5 = 0 ∧ t 6 = 0) ∨
    (t 0 = 0 ∧ t 1 = 1 ∧ t 2 = 0 ∧ t 3 = 0 ∧
        t 4 = 0 ∧ t 5 = -1 ∧ t 6 = 0) ∨
    (t 0 = 0 ∧ t 1 = 0 ∧ t 2 = 1 ∧ t 3 = 0 ∧
        t 4 = 0 ∧ t 5 = 0 ∧ t 6 = -1) := by
  let t := fun i : Fin 7 ↦ ε i * f (q i)
  have ht₀ := sign_mul_coeff_mem_sign_or_zero_of_normSq_eq_three f hf (q 0) (hε 0)
  have ht₁ := sign_mul_coeff_mem_sign_or_zero_of_normSq_eq_three f hf (q 1) (hε 1)
  have ht₂ := sign_mul_coeff_mem_sign_or_zero_of_normSq_eq_three f hf (q 2) (hε 2)
  have ht₃ := sign_mul_coeff_mem_sign_or_zero_of_normSq_eq_three f hf (q 3) (hε 3)
  have ht₄ := sign_mul_coeff_mem_sign_or_zero_of_normSq_eq_three f hf (q 4) (hε 4)
  have ht₅ := sign_mul_coeff_mem_sign_or_zero_of_normSq_eq_three f hf (q 5) (hε 5)
  have ht₆ := sign_mul_coeff_mem_sign_or_zero_of_normSq_eq_three f hf (q 6) (hε 6)
  simp only [signedBasis, coeffDot_add_left, coeffDot_single_left] at h₀ h₁ h₂ h₃
  have hs := sum_normalized_coeff_sq_le_normSq q hq ε hε f
  rw [hf] at hs
  simp [Fin.sum_univ_succ] at hs
  change t 0 ^ 2 + (t 1 ^ 2 + (t 2 ^ 2 + (t 3 ^ 2 +
    (t 4 ^ 2 + (t 5 ^ 2 + t 6 ^ 2))))) ≤ 3 at hs
  change t 0 + t 1 + t 2 = 1 at h₀
  change t 0 + t 3 + t 4 = 0 at h₁
  change t 1 + t 3 + t 5 = 0 at h₂
  change t 2 + t 3 + t 6 = 0 at h₃
  change t 0 = -1 ∨ t 0 = 0 ∨ t 0 = 1 at ht₀
  change t 1 = -1 ∨ t 1 = 0 ∨ t 1 = 1 at ht₁
  change t 2 = -1 ∨ t 2 = 0 ∨ t 2 = 1 at ht₂
  change t 3 = -1 ∨ t 3 = 0 ∨ t 3 = 1 at ht₃
  change t 4 = -1 ∨ t 4 = 0 ∨ t 4 = 1 at ht₄
  change t 5 = -1 ∨ t 5 = 0 ∨ t 5 = 1 at ht₅
  change t 6 = -1 ∨ t 6 = 0 ∨ t 6 = 1 at ht₆
  change
    (t 0 = 1 ∧ t 1 = 0 ∧ t 2 = 0 ∧ t 3 = 0 ∧
        t 4 = -1 ∧ t 5 = 0 ∧ t 6 = 0) ∨
    (t 0 = 0 ∧ t 1 = 1 ∧ t 2 = 0 ∧ t 3 = 0 ∧
        t 4 = 0 ∧ t 5 = -1 ∧ t 6 = 0) ∨
    (t 0 = 0 ∧ t 1 = 0 ∧ t 2 = 1 ∧ t 3 = 0 ∧
        t 4 = 0 ∧ t 5 = 0 ∧ t 6 = -1)
  rcases ht₀ with h | h | h <;> rcases ht₁ with h' | h' | h' <;>
    rcases ht₂ with h'' | h'' | h'' <;> rcases ht₃ with h₃' | h₃' | h₃' <;>
    rcases ht₄ with h₄' | h₄' | h₄' <;> rcases ht₅ with h₅' | h₅' | h₅' <;>
    rcases ht₆ with h₆' | h₆' | h₆' <;>
      norm_num [h, h', h'', h₃', h₄', h₅', h₆'] at hs <;>
      try omega <;> simp only [h, h', h'', h₃', h₄', h₅', h₆']

/-- The short arithmetic obstruction at the end of the exceptional `4 × 2`
case.  This replaces the last reflected branch of the Coq proof. -/
private theorem no_exceptional_fourth_against_e1
    {κ : Type*} [DecidableEq κ]
    (q : Fin 7 → κ) (hq : Function.Injective q)
    (ε : Fin 7 → ℤ) (hε : ∀ i, IsSign (ε i))
    (e : IntegralLattice κ) (he : normSq e = 3)
    (s₀ : ε 0 * e (q 0) + ε 1 * e (q 1) + ε 2 * e (q 2) = 0)
    (s₁ : ε 0 * e (q 0) + ε 3 * e (q 3) + ε 4 * e (q 4) = 0)
    (s₂ : ε 1 * e (q 1) + ε 3 * e (q 3) + ε 5 * e (q 5) = 0)
    (s₃ : ε 2 * e (q 2) + ε 3 * e (q 3) + ε 6 * e (q 6) = 1)
    (e₁ : ε 0 * e (q 0) - ε 1 * e (q 1) + ε 5 * e (q 5) = 1) :
    False := by
  let t := fun i : Fin 7 ↦ ε i * e (q i)
  change t 0 + t 1 + t 2 = 0 at s₀
  change t 0 + t 3 + t 4 = 0 at s₁
  change t 1 + t 3 + t 5 = 0 at s₂
  change t 2 + t 3 + t 6 = 1 at s₃
  change t 0 - t 1 + t 5 = 1 at e₁
  have ht₆ := sign_mul_coeff_mem_sign_or_zero_of_normSq_eq_three e he (q 6) (hε 6)
  change t 6 = -1 ∨ t 6 = 0 ∨ t 6 = 1 at ht₆
  have hb : t 1 = -1 := by rcases ht₆ with h | h | h <;> omega
  have ht₄ := sign_mul_coeff_mem_sign_or_zero_of_normSq_eq_three e he (q 4) (hε 4)
  have ht₂ := sign_mul_coeff_mem_sign_or_zero_of_normSq_eq_three e he (q 2) (hε 2)
  change t 4 = -1 ∨ t 4 = 0 ∨ t 4 = 1 at ht₄
  change t 2 = -1 ∨ t 2 = 0 ∨ t 2 = 1 at ht₂
  have ha : t 0 = 0 := by
    rcases ht₄ with h | h | h <;> rcases ht₂ with h' | h' | h' <;> omega
  have ht₁ : t 1 ≠ 0 := by omega
  have ht₂' : t 2 ≠ 0 := by omega
  have ht₃ : t 3 ≠ 0 := by omega
  have ht₄' : t 4 ≠ 0 := by omega
  have hdistinct (i j : Fin 7) (hij : i ≠ j) : q i ≠ q j := by
    intro h
    exact hij (hq h)
  have hz := at_most_three_nonzero e he
    (hdistinct 1 2 (by decide)) (hdistinct 1 3 (by decide))
    (hdistinct 1 4 (by decide)) (hdistinct 2 3 (by decide))
    (hdistinct 2 4 (by decide)) (hdistinct 3 4 (by decide))
  rcases hz with h | h | h | h
  · apply ht₁
    exact eq_zero_of_sign_mul_eq_zero (hε 1) (by simp [t, h])
  · apply ht₂'
    exact eq_zero_of_sign_mul_eq_zero (hε 2) (by simp [t, h])
  · apply ht₃
    exact eq_zero_of_sign_mul_eq_zero (hε 3) (by simp [t, h])
  · apply ht₄'
    exact eq_zero_of_sign_mul_eq_zero (hε 4) (by simp [t, h])

set_option maxHeartbeats 2000000 in
private theorem d2_dual_one_coefficients
    {κ : Type*} [DecidableEq κ]
    (q : Fin 7 → κ) (hq : Function.Injective q)
    (ε : Fin 7 → ℤ) (hε : ∀ i, IsSign (ε i))
    (f : IntegralLattice κ) (hf : normSq f = 3)
    (h₀ : coeffDot
      (signedBasis q ε 0 + signedBasis q ε 1 + signedBasis q ε 2) f = 0)
    (h₁ : coeffDot
      (signedBasis q ε 0 + signedBasis q ε 3 + signedBasis q ε 4) f = 1)
    (h₂ : coeffDot
      (signedBasis q ε 1 + signedBasis q ε 3 + signedBasis q ε 5) f = 0)
    (h₃ : coeffDot
      (signedBasis q ε 2 + signedBasis q ε 3 + signedBasis q ε 6) f = 0) :
    let t := fun i : Fin 7 ↦ ε i * f (q i)
    (t 0 = 1 ∧ t 1 = -1 ∧ t 2 = 0 ∧ t 3 = 0 ∧
        t 4 = 0 ∧ t 5 = 1 ∧ t 6 = 0) ∨
    (t 0 = 1 ∧ t 1 = 0 ∧ t 2 = -1 ∧ t 3 = 0 ∧
        t 4 = 0 ∧ t 5 = 0 ∧ t 6 = 1) ∨
    (t 0 = 0 ∧ t 1 = 0 ∧ t 2 = 0 ∧ t 3 = 1 ∧
        t 4 = 0 ∧ t 5 = -1 ∧ t 6 = -1) ∨
    (t 0 = 0 ∧ t 1 = 0 ∧ t 2 = 0 ∧ t 3 = 0 ∧
        t 4 = 1 ∧ t 5 = 0 ∧ t 6 = 0) := by
  let t := fun i : Fin 7 ↦ ε i * f (q i)
  have ht₀ := sign_mul_coeff_mem_sign_or_zero_of_normSq_eq_three f hf (q 0) (hε 0)
  have ht₁ := sign_mul_coeff_mem_sign_or_zero_of_normSq_eq_three f hf (q 1) (hε 1)
  have ht₂ := sign_mul_coeff_mem_sign_or_zero_of_normSq_eq_three f hf (q 2) (hε 2)
  have ht₃ := sign_mul_coeff_mem_sign_or_zero_of_normSq_eq_three f hf (q 3) (hε 3)
  have ht₄ := sign_mul_coeff_mem_sign_or_zero_of_normSq_eq_three f hf (q 4) (hε 4)
  have ht₅ := sign_mul_coeff_mem_sign_or_zero_of_normSq_eq_three f hf (q 5) (hε 5)
  have ht₆ := sign_mul_coeff_mem_sign_or_zero_of_normSq_eq_three f hf (q 6) (hε 6)
  simp only [signedBasis, coeffDot_add_left, coeffDot_single_left] at h₀ h₁ h₂ h₃
  have hs := sum_normalized_coeff_sq_le_normSq q hq ε hε f
  rw [hf] at hs
  simp [Fin.sum_univ_succ] at hs
  change t 0 ^ 2 + (t 1 ^ 2 + (t 2 ^ 2 + (t 3 ^ 2 +
    (t 4 ^ 2 + (t 5 ^ 2 + t 6 ^ 2))))) ≤ 3 at hs
  change t 0 + t 1 + t 2 = 0 at h₀
  change t 0 + t 3 + t 4 = 1 at h₁
  change t 1 + t 3 + t 5 = 0 at h₂
  change t 2 + t 3 + t 6 = 0 at h₃
  change t 0 = -1 ∨ t 0 = 0 ∨ t 0 = 1 at ht₀
  change t 1 = -1 ∨ t 1 = 0 ∨ t 1 = 1 at ht₁
  change t 2 = -1 ∨ t 2 = 0 ∨ t 2 = 1 at ht₂
  change t 3 = -1 ∨ t 3 = 0 ∨ t 3 = 1 at ht₃
  change t 4 = -1 ∨ t 4 = 0 ∨ t 4 = 1 at ht₄
  change t 5 = -1 ∨ t 5 = 0 ∨ t 5 = 1 at ht₅
  change t 6 = -1 ∨ t 6 = 0 ∨ t 6 = 1 at ht₆
  change
    (t 0 = 1 ∧ t 1 = -1 ∧ t 2 = 0 ∧ t 3 = 0 ∧
        t 4 = 0 ∧ t 5 = 1 ∧ t 6 = 0) ∨
    (t 0 = 1 ∧ t 1 = 0 ∧ t 2 = -1 ∧ t 3 = 0 ∧
        t 4 = 0 ∧ t 5 = 0 ∧ t 6 = 1) ∨
    (t 0 = 0 ∧ t 1 = 0 ∧ t 2 = 0 ∧ t 3 = 1 ∧
        t 4 = 0 ∧ t 5 = -1 ∧ t 6 = -1) ∨
    (t 0 = 0 ∧ t 1 = 0 ∧ t 2 = 0 ∧ t 3 = 0 ∧
        t 4 = 1 ∧ t 5 = 0 ∧ t 6 = 0)
  rcases ht₀ with h | h | h <;> rcases ht₁ with h' | h' | h' <;>
    rcases ht₂ with h'' | h'' | h'' <;> rcases ht₃ with h₃' | h₃' | h₃' <;>
    rcases ht₄ with h₄' | h₄' | h₄' <;> rcases ht₅ with h₅' | h₅' | h₅' <;>
    rcases ht₆ with h₆' | h₆' | h₆' <;>
      norm_num [h, h', h'', h₃', h₄', h₅', h₆'] at hs <;>
      try omega <;> simp only [h, h', h'', h₃', h₄', h₅', h₆']

private def exceptionalSource {κ : Type*} [DecidableEq κ]
    (q : Fin 7 → κ) (ε : Fin 7 → ℤ) : Fin 4 → IntegralLattice κ
  | 0 => signedBasis q ε 0 + signedBasis q ε 1 + signedBasis q ε 2
  | 1 => signedBasis q ε 0 + signedBasis q ε 3 + signedBasis q ε 4
  | 2 => signedBasis q ε 1 + signedBasis q ε 3 + signedBasis q ε 5
  | 3 => signedBasis q ε 2 + signedBasis q ε 3 + signedBasis q ε 6

/-- The non-Pasch exceptional source pattern has no norm-three dual column. -/
private theorem no_exceptional_dual_of_first_case
    {κ : Type*} [DecidableEq κ]
    (q : Fin 7 → κ) (hq : Function.Injective q)
    (ε : Fin 7 → ℤ) (hε : ∀ i, IsSign (ε i))
    (E : Fin 4 → IntegralLattice κ)
    (hnorm : ∀ i, normSq (E i) = 3)
    (hdual : ∀ i j, coeffDot (exceptionalSource q ε i) (E j) =
      if i = j then 1 else 0)
    (hpair : ∀ i j, i ≠ j → coeffDot (E i) (E j) = 1)
    (hcase :
      ε 0 * E 0 (q 0) = 1 ∧ ε 1 * E 0 (q 1) = 0 ∧
      ε 2 * E 0 (q 2) = 0 ∧ ε 3 * E 0 (q 3) = 0 ∧
      ε 4 * E 0 (q 4) = -1 ∧ ε 5 * E 0 (q 5) = 0 ∧
      ε 6 * E 0 (q 6) = 0) :
    False := by
  rcases hcase with ⟨h₀₀, h₀₁, h₀₂, h₀₃, h₀₄, h₀₅, h₀₆⟩
  have hqne (i j : Fin 7) (hij : i ≠ j) : q i ≠ q j := by
    intro h
    exact hij (hq h)
  have hE₀q₀ : E 0 (q 0) = ε 0 := eq_of_sign_mul_eq_one (hε 0) h₀₀
  have hE₀q₄ : E 0 (q 4) = -ε 4 :=
    eq_neg_of_sign_mul_eq_neg_one (hε 4) h₀₄
  obtain ⟨z, ζ, hq₀z, hq₄z, hζ, hE₀⟩ :=
    complete_two_signed_coefficients (E 0) (hnorm 0)
      (hqne 0 4 (by decide)) (hε 0) (isSign_neg (hε 4)) hE₀q₀ hE₀q₄
  have hE₀zero (k : Fin 7) (hk : k ≠ 0) (hk' : k ≠ 4)
      (hcoeff : ε k * E 0 (q k) = 0) : E 0 (q k) = 0 :=
    eq_zero_of_sign_mul_eq_zero (hε k) hcoeff
  have hz_ne (k : Fin 7) (hk : k ≠ 0) (hk' : k ≠ 4)
      (hcoeff : ε k * E 0 (q k) = 0) : z ≠ q k := by
    intro hzk
    have hzero := hE₀zero k hk hk' hcoeff
    rw [hE₀, hzk] at hzero
    have h0k : q 0 ≠ q k := hqne 0 k (Ne.symm hk)
    have h4k : q 4 ≠ q k := hqne 4 k (Ne.symm hk')
    simp [h0k, h4k, isSign_ne_zero hζ] at hzero
  have hE₁cases := d2_dual_one_coefficients q hq ε hε (E 1) (hnorm 1)
    (by simpa [exceptionalSource] using hdual 0 1)
    (by simpa [exceptionalSource] using hdual 1 1)
    (by simpa [exceptionalSource] using hdual 2 1)
    (by simpa [exceptionalSource] using hdual 3 1)
  rcases hE₁cases with hA | hB | hC | hD
  · rcases hA with ⟨h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆⟩
    have hE₁q₀ : E 1 (q 0) = ε 0 := eq_of_sign_mul_eq_one (hε 0) h₁₀
    have hE₁q₁ : E 1 (q 1) = -ε 1 :=
      eq_neg_of_sign_mul_eq_neg_one (hε 1) h₁₁
    have hE₁q₅ : E 1 (q 5) = ε 5 := eq_of_sign_mul_eq_one (hε 5) h₁₅
    have hE₁ : E 1 = signedBasis q ε 0 - signedBasis q ε 1 + signedBasis q ε 5 := by
      simpa [signedBasis, sub_eq_add_neg] using
        eq_sum_three_of_signed_coefficients (E 1)
          (hqne 0 1 (by decide)) (hqne 0 5 (by decide)) (hqne 1 5 (by decide))
          (hε 0) (isSign_neg (hε 1)) (hε 5) (hnorm 1)
          hE₁q₀ hE₁q₁ hE₁q₅
    have hp := hpair 1 3 (by decide)
    rw [hE₁] at hp
    simp only [sub_eq_add_neg, coeffDot_add_left, coeffDot_neg_left,
      signedBasis, coeffDot_single_left] at hp
    exact no_exceptional_fourth_against_e1 q hq ε hε (E 3) (hnorm 3)
      (by simpa [exceptionalSource, signedBasis, coeffDot_add_left] using hdual 0 3)
      (by simpa [exceptionalSource, signedBasis, coeffDot_add_left] using hdual 1 3)
      (by simpa [exceptionalSource, signedBasis, coeffDot_add_left] using hdual 2 3)
      (by simpa [exceptionalSource, signedBasis, coeffDot_add_left] using hdual 3 3) hp
  · rcases hB with ⟨h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆⟩
    have hE₁q₀ : E 1 (q 0) = ε 0 := eq_of_sign_mul_eq_one (hε 0) h₁₀
    have hE₁q₂ : E 1 (q 2) = -ε 2 :=
      eq_neg_of_sign_mul_eq_neg_one (hε 2) h₁₂
    have hE₁q₆ : E 1 (q 6) = ε 6 := eq_of_sign_mul_eq_one (hε 6) h₁₆
    have hE₁ : E 1 = signedBasis q ε 0 - signedBasis q ε 2 + signedBasis q ε 6 := by
      simpa [signedBasis, sub_eq_add_neg] using
        eq_sum_three_of_signed_coefficients (E 1)
          (hqne 0 2 (by decide)) (hqne 0 6 (by decide)) (hqne 2 6 (by decide))
          (hε 0) (isSign_neg (hε 2)) (hε 6) (hnorm 1)
          hE₁q₀ hE₁q₂ hE₁q₆
    have hp := hpair 1 2 (by decide)
    rw [hE₁] at hp
    simp only [sub_eq_add_neg, coeffDot_add_left, coeffDot_neg_left,
      signedBasis, coeffDot_single_left] at hp
    let p : Fin 7 → Fin 7 := ![0, 2, 1, 3, 4, 6, 5]
    have hp_inj : Function.Injective p := by decide
    exact no_exceptional_fourth_against_e1 (q ∘ p) (hq.comp hp_inj) (ε ∘ p)
      (fun i ↦ hε (p i)) (E 2) (hnorm 2)
      (by
        have h := hdual 0 2
        simp only [exceptionalSource, signedBasis, coeffDot_add_left,
          coeffDot_single_left] at h
        simp [p, Function.comp_apply]
        omega)
      (by simpa [p, exceptionalSource, signedBasis, coeffDot_add_left,
        Function.comp_apply] using hdual 1 2)
      (by simpa [p, exceptionalSource, signedBasis, coeffDot_add_left,
        Function.comp_apply, add_comm] using hdual 3 2)
      (by simpa [p, exceptionalSource, signedBasis, coeffDot_add_left,
        Function.comp_apply, add_comm] using hdual 2 2)
      (by simpa [p, Function.comp_apply, sub_eq_add_neg] using hp)
  · rcases hC with ⟨h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆⟩
    have hE₁q₃ : E 1 (q 3) = ε 3 := eq_of_sign_mul_eq_one (hε 3) h₁₃
    have hE₁q₅ : E 1 (q 5) = -ε 5 :=
      eq_neg_of_sign_mul_eq_neg_one (hε 5) h₁₅
    have hE₁q₆ : E 1 (q 6) = -ε 6 :=
      eq_neg_of_sign_mul_eq_neg_one (hε 6) h₁₆
    have hE₁ : E 1 = signedBasis q ε 3 - signedBasis q ε 5 - signedBasis q ε 6 := by
      simpa [signedBasis, sub_eq_add_neg, add_assoc] using
        eq_sum_three_of_signed_coefficients (E 1)
          (hqne 3 5 (by decide)) (hqne 3 6 (by decide)) (hqne 5 6 (by decide))
          (hε 3) (isSign_neg (hε 5)) (isSign_neg (hε 6)) (hnorm 1)
          hE₁q₃ hE₁q₅ hE₁q₆
    have hp := hpair 0 1 (by decide)
    rw [hE₀, hE₁] at hp
    simp [signedBasis, coeffDot_add_left, coeffDot_add_right, coeffDot_neg_left,
      coeffDot_neg_right, hqne, hz_ne 3 (by decide) (by decide) h₀₃,
      hz_ne 5 (by decide) (by decide) h₀₅,
      hz_ne 6 (by decide) (by decide) h₀₆] at hp
  · rcases hD with ⟨h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆⟩
    have hE₁q₄ : E 1 (q 4) = ε 4 := eq_of_sign_mul_eq_one (hε 4) h₁₄
    have hcontra := no_opposite_first (E 0) (E 1) (exceptionalSource q ε 0)
      hq₄z (hqne 4 0 (by decide)) hq₀z.symm
      (isSign_neg (hε 4)) hζ (hε 0)
      (by simpa [sub_eq_add_neg, add_left_comm, add_comm, add_assoc, signedBasis] using hE₀)
      (hnorm 1) (hpair 0 1 (by decide))
      (by simpa [coeffDot_comm] using hdual 0 0)
      (by simpa [coeffDot_comm] using hdual 0 1)
    apply hcontra
    rw [hE₁q₄]
    calc
      -ε 4 * ε 4 = -(ε 4 * ε 4) := by ring
      _ = -1 := by rw [isSign_sq (hε 4)]

set_option maxHeartbeats 2000000 in
private theorem no_exceptional_dual
    {κ : Type*} [DecidableEq κ]
    (q : Fin 7 → κ) (hq : Function.Injective q)
    (ε : Fin 7 → ℤ) (hε : ∀ i, IsSign (ε i))
    (E : Fin 4 → IntegralLattice κ)
    (hnorm : ∀ i, normSq (E i) = 3)
    (hdual : ∀ i j, coeffDot (exceptionalSource q ε i) (E j) =
      if i = j then 1 else 0)
    (hpair : ∀ i j, i ≠ j → coeffDot (E i) (E j) = 1) :
    False := by
  have hc := d2_dual_zero_coefficients q hq ε hε (E 0) (hnorm 0)
    (by simpa [exceptionalSource] using hdual 0 0)
    (by simpa [exceptionalSource] using hdual 1 0)
    (by simpa [exceptionalSource] using hdual 2 0)
    (by simpa [exceptionalSource] using hdual 3 0)
  rcases hc with hA | hB | hC
  · exact no_exceptional_dual_of_first_case q hq ε hε E hnorm hdual hpair hA
  · let p : Fin 7 → Fin 7 := ![1, 0, 2, 3, 5, 4, 6]
    let s : Fin 4 → Fin 4 := ![0, 2, 1, 3]
    have hp : Function.Injective p := by decide
    have hs : Function.Injective s := by decide
    have hsource (i : Fin 4) :
        exceptionalSource (q ∘ p) (ε ∘ p) i = exceptionalSource q ε (s i) := by
      fin_cases i <;>
        simp [p, s, exceptionalSource, signedBasis, Function.comp_apply,
          add_left_comm, add_comm, add_assoc]
    apply no_exceptional_dual_of_first_case (q ∘ p) (hq.comp hp) (ε ∘ p)
      (fun i ↦ hε (p i)) (fun i ↦ E (s i))
    · intro i
      exact hnorm (s i)
    · intro i j
      rw [hsource i]
      simpa only [hs.eq_iff] using hdual (s i) (s j)
    · intro i j hij
      have hsij : s i ≠ s j := fun h ↦ hij (hs h)
      exact hpair (s i) (s j) hsij
    · rcases hB with ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆⟩
      exact ⟨h₁, h₀, h₂, h₃, h₅, h₄, h₆⟩
  · let p : Fin 7 → Fin 7 := ![2, 1, 0, 3, 6, 5, 4]
    let s : Fin 4 → Fin 4 := ![0, 3, 2, 1]
    have hp : Function.Injective p := by decide
    have hs : Function.Injective s := by decide
    have hsource (i : Fin 4) :
        exceptionalSource (q ∘ p) (ε ∘ p) i = exceptionalSource q ε (s i) := by
      fin_cases i <;>
        simp [p, s, exceptionalSource, signedBasis, Function.comp_apply,
          add_left_comm, add_comm, add_assoc]
    apply no_exceptional_dual_of_first_case (q ∘ p) (hq.comp hp) (ε ∘ p)
      (fun i ↦ hε (p i)) (fun i ↦ E (s i))
    · intro i
      exact hnorm (s i)
    · intro i j
      rw [hsource i]
      simpa only [hs.eq_iff] using hdual (s i) (s j)
    · intro i j hij
      have hsij : s i ≠ s j := fun h ↦ hij (hs h)
      exact hpair (s i) (s j) hsij
    · rcases hC with ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆⟩
      exact ⟨h₂, h₁, h₀, h₃, h₆, h₅, h₄⟩

private theorem no_exceptional_dual_up_to_row_permutation
    {κ : Type*} [DecidableEq κ]
    (q : Fin 7 → κ) (hq : Function.Injective q)
    (ε : Fin 7 → ℤ) (hε : ∀ i, IsSign (ε i))
    (S E : Fin 4 → IntegralLattice κ)
    (s : Fin 4 → Fin 4) (hs : Function.Injective s)
    (hsource : ∀ i, exceptionalSource q ε i = S (s i))
    (hnormE : ∀ i, normSq (E i) = 3)
    (hdual : ∀ i j, coeffDot (S i) (E j) = if i = j then 1 else 0)
    (hpairE : ∀ i j, i ≠ j → coeffDot (E i) (E j) = 1) :
    False := by
  apply no_exceptional_dual q hq ε hε (fun i ↦ E (s i))
  · intro i
    exact hnormE (s i)
  · intro i j
    rw [hsource i]
    simpa only [hs.eq_iff] using hdual (s i) (s j)
  · intro i j hij
    exact hpairE (s i) (s j) (fun h ↦ hij (hs h))

set_option maxHeartbeats 4000000 in
/-- Once three entries on a line have the displayed seven-point
normalization and omit the first common point in the third entry, a fourth
entry and the perpendicular dual line cannot coexist. -/
private theorem no_fourth_completion_after_three_sources
    {κ : Type*} [DecidableEq κ]
    (q : Fin 6 → κ) (hq : Function.Injective q)
    (ε : Fin 6 → ℤ) (hε : ∀ i, IsSign (ε i))
    (S E : Fin 4 → IntegralLattice κ)
    (hS₀ : S 0 = single (q 0) (ε 0) + single (q 1) (ε 1) +
      single (q 2) (ε 2))
    (hS₁ : S 1 = single (q 0) (ε 0) + single (q 3) (ε 3) +
      single (q 4) (ε 4))
    (hS₂ : S 2 = single (q 1) (ε 1) + single (q 3) (ε 3) +
      single (q 5) (ε 5))
    (hnormS : ∀ i, normSq (S i) = 3)
    (hpairS : ∀ i j, i ≠ j → coeffDot (S i) (S j) = 1)
    (hnormE : ∀ i, normSq (E i) = 3)
    (hdual : ∀ i j, coeffDot (S i) (E j) = if i = j then 1 else 0)
    (hpairE : ∀ i j, i ≠ j → coeffDot (E i) (E j) = 1) :
    False := by
  have hqne (i j : Fin 6) (hij : i ≠ j) : q i ≠ q j := by
    intro h
    exact hij (hq h)
  have ht₀ := line_normalized_coefficients_onehot (S 0) (S 3) (E 0)
    (hqne 0 1 (by decide)) (hqne 0 2 (by decide)) (hqne 1 2 (by decide))
    (hε 0) (hε 1) (hε 2) hS₀ (hnormS 3)
    (hpairS 0 3 (by decide)) (by simpa using hdual 0 0)
    (by simpa using hdual 3 0)
  have ht₁ := line_normalized_coefficients_onehot (S 1) (S 3) (E 1)
    (hqne 0 3 (by decide)) (hqne 0 4 (by decide)) (hqne 3 4 (by decide))
    (hε 0) (hε 3) (hε 4) hS₁ (hnormS 3)
    (hpairS 1 3 (by decide)) (by simpa using hdual 1 1)
    (by simpa using hdual 3 1)
  have ht₂ := line_normalized_coefficients_onehot (S 2) (S 3) (E 2)
    (hqne 1 3 (by decide)) (hqne 1 5 (by decide)) (hqne 3 5 (by decide))
    (hε 1) (hε 3) (hε 5) hS₂ (hnormS 3)
    (hpairS 2 3 (by decide)) (by simpa using hdual 2 2)
    (by simpa using hdual 3 2)
  let t : Fin 6 → ℤ := fun i ↦ ε i * S 3 (q i)
  change (t 0 = 0 ∨ t 0 = 1) ∧ (t 1 = 0 ∨ t 1 = 1) ∧
    (t 2 = 0 ∨ t 2 = 1) ∧ t 0 + t 1 + t 2 = 1 at ht₀
  change (t 0 = 0 ∨ t 0 = 1) ∧ (t 3 = 0 ∨ t 3 = 1) ∧
    (t 4 = 0 ∨ t 4 = 1) ∧ t 0 + t 3 + t 4 = 1 at ht₁
  change (t 1 = 0 ∨ t 1 = 1) ∧ (t 3 = 0 ∨ t 3 = 1) ∧
    (t 5 = 0 ∨ t 5 = 1) ∧ t 1 + t 3 + t 5 = 1 at ht₂
  rcases ht₀ with ⟨ht₀, ht₁', ht₂', hs₀⟩
  rcases ht₁ with ⟨_, ht₃, ht₄, hs₁⟩
  rcases ht₂ with ⟨_, _, ht₅, hs₂⟩
  have hcases :
      (t 0 = 0 ∧ t 1 = 0 ∧ t 2 = 1 ∧ t 3 = 0 ∧ t 4 = 1 ∧ t 5 = 1) ∨
      (t 0 = 0 ∧ t 1 = 0 ∧ t 2 = 1 ∧ t 3 = 1 ∧ t 4 = 0 ∧ t 5 = 0) ∨
      (t 0 = 0 ∧ t 1 = 1 ∧ t 2 = 0 ∧ t 3 = 0 ∧ t 4 = 1 ∧ t 5 = 0) ∨
      (t 0 = 1 ∧ t 1 = 0 ∧ t 2 = 0 ∧ t 3 = 0 ∧ t 4 = 0 ∧ t 5 = 1) := by
    rcases ht₀ with h | h <;> rcases ht₁' with h' | h' <;>
      rcases ht₂' with h'' | h'' <;> rcases ht₃ with h₃ | h₃ <;>
      rcases ht₄ with h₄ | h₄ <;> rcases ht₅ with h₅ | h₅ <;> omega
  have coeff_one (i : Fin 6) (hi : t i = 1) : S 3 (q i) = ε i :=
    eq_of_sign_mul_eq_one (hε i) hi
  have coeff_zero (i : Fin 6) (hi : t i = 0) : S 3 (q i) = 0 :=
    eq_zero_of_sign_mul_eq_zero (hε i) hi
  rcases hcases with hP | hA | hB | hC
  · rcases hP with ⟨h₀, h₁, h₂, h₃, h₄, h₅⟩
    have hS₃ : S 3 = single (q 2) (ε 2) + single (q 4) (ε 4) +
        single (q 5) (ε 5) :=
      eq_sum_three_of_signed_coefficients (S 3)
        (hqne 2 4 (by decide)) (hqne 2 5 (by decide)) (hqne 4 5 (by decide))
        (hε 2) (hε 4) (hε 5) (hnormS 3)
        (coeff_one 2 h₂) (coeff_one 4 h₄) (coeff_one 5 h₅)
    exact no_pasched_dual
      ![q 0, q 1, q 2, q 3, q 4, q 5, q 5]
      ![ε 0, ε 1, ε 2, ε 3, ε 4, ε 5, ε 5] (E 0)
      (by simpa [signedBasis, hS₀] using hdual 0 0)
      (by simpa [signedBasis, hS₁] using hdual 1 0)
      (by simpa [signedBasis, hS₂] using hdual 2 0)
      (by simpa [signedBasis, hS₃] using hdual 3 0)
  · rcases hA with ⟨h₀, h₁, h₂, h₃, h₄, h₅⟩
    obtain ⟨z, ζ, h₂z, h₃z, hζ, hS₃⟩ :=
      complete_two_signed_coefficients (S 3) (hnormS 3)
        (hqne 2 3 (by decide)) (hε 2) (hε 3)
        (coeff_one 2 h₂) (coeff_one 3 h₃)
    let q₇ : Fin 7 → κ := ![q 0, q 1, q 2, q 3, q 4, q 5, z]
    let ε₇ : Fin 7 → ℤ := ![ε 0, ε 1, ε 2, ε 3, ε 4, ε 5, ζ]
    have hz (i : Fin 6) (hi₂ : i ≠ 2) (hi₃ : i ≠ 3)
        (hi : t i = 0) : z ≠ q i := by
      intro hzi
      have hzero := coeff_zero i hi
      rw [hS₃, hzi] at hzero
      simp [hqne 2 i (Ne.symm hi₂), hqne 3 i (Ne.symm hi₃),
        isSign_ne_zero hζ] at hzero
    have hz₀ : q 0 ≠ z := (hz 0 (by decide) (by decide) h₀).symm
    have hz₁ : q 1 ≠ z := (hz 1 (by decide) (by decide) h₁).symm
    have hz₄ : q 4 ≠ z := (hz 4 (by decide) (by decide) h₄).symm
    have hz₅ : q 5 ≠ z := (hz 5 (by decide) (by decide) h₅).symm
    have hq₇ : Function.Injective q₇ := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [q₇, hqne, hz₀, hz₁, hz₄, hz₅]
    have hε₇ : ∀ i, IsSign (ε₇ i) := by
      intro i
      fin_cases i <;> simp [ε₇, hε, hζ]
    let s : Fin 4 → Fin 4 := ![0, 1, 2, 3]
    apply no_exceptional_dual_up_to_row_permutation q₇ hq₇ ε₇ hε₇ S E s
      (by decide)
    · intro i
      fin_cases i <;> simp [q₇, ε₇, s, exceptionalSource, signedBasis,
        hS₀, hS₁, hS₂, hS₃, add_left_comm, add_comm, add_assoc]
    · exact hnormE
    · exact hdual
    · exact hpairE
  · rcases hB with ⟨h₀, h₁, h₂, h₃, h₄, h₅⟩
    obtain ⟨z, ζ, h₁z, h₄z, hζ, hS₃⟩ :=
      complete_two_signed_coefficients (S 3) (hnormS 3)
        (hqne 1 4 (by decide)) (hε 1) (hε 4)
        (coeff_one 1 h₁) (coeff_one 4 h₄)
    let q₇ : Fin 7 → κ := ![q 0, q 3, q 4, q 1, q 2, q 5, z]
    let ε₇ : Fin 7 → ℤ := ![ε 0, ε 3, ε 4, ε 1, ε 2, ε 5, ζ]
    have hz (i : Fin 6) (hi₁ : i ≠ 1) (hi₄ : i ≠ 4)
        (hi : t i = 0) : z ≠ q i := by
      intro hzi
      have hzero := coeff_zero i hi
      rw [hS₃, hzi] at hzero
      simp [hqne 1 i (Ne.symm hi₁), hqne 4 i (Ne.symm hi₄),
        isSign_ne_zero hζ] at hzero
    have hz₀ : q 0 ≠ z := (hz 0 (by decide) (by decide) h₀).symm
    have hz₂ : q 2 ≠ z := (hz 2 (by decide) (by decide) h₂).symm
    have hz₃ : q 3 ≠ z := (hz 3 (by decide) (by decide) h₃).symm
    have hz₅ : q 5 ≠ z := (hz 5 (by decide) (by decide) h₅).symm
    have hq₇ : Function.Injective q₇ := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [q₇, hqne, hz₀, hz₂, hz₃, hz₅]
    have hε₇ : ∀ i, IsSign (ε₇ i) := by
      intro i
      fin_cases i <;> simp [ε₇, hε, hζ]
    let s : Fin 4 → Fin 4 := ![1, 0, 2, 3]
    apply no_exceptional_dual_up_to_row_permutation q₇ hq₇ ε₇ hε₇ S E s
      (by decide)
    · intro i
      fin_cases i <;> simp [q₇, ε₇, s, exceptionalSource, signedBasis,
        hS₀, hS₁, hS₂, hS₃, add_left_comm, add_comm, add_assoc]
    · exact hnormE
    · exact hdual
    · exact hpairE
  · rcases hC with ⟨h₀, h₁, h₂, h₃, h₄, h₅⟩
    obtain ⟨z, ζ, h₀z, h₅z, hζ, hS₃⟩ :=
      complete_two_signed_coefficients (S 3) (hnormS 3)
        (hqne 0 5 (by decide)) (hε 0) (hε 5)
        (coeff_one 0 h₀) (coeff_one 5 h₅)
    let q₇ : Fin 7 → κ := ![q 1, q 3, q 5, q 0, q 2, q 4, z]
    let ε₇ : Fin 7 → ℤ := ![ε 1, ε 3, ε 5, ε 0, ε 2, ε 4, ζ]
    have hz (i : Fin 6) (hi₀ : i ≠ 0) (hi₅ : i ≠ 5)
        (hi : t i = 0) : z ≠ q i := by
      intro hzi
      have hzero := coeff_zero i hi
      rw [hS₃, hzi] at hzero
      simp [hqne 0 i (Ne.symm hi₀), hqne 5 i (Ne.symm hi₅),
        isSign_ne_zero hζ] at hzero
    have hz₁ : q 1 ≠ z := (hz 1 (by decide) (by decide) h₁).symm
    have hz₂ : q 2 ≠ z := (hz 2 (by decide) (by decide) h₂).symm
    have hz₃ : q 3 ≠ z := (hz 3 (by decide) (by decide) h₃).symm
    have hz₄ : q 4 ≠ z := (hz 4 (by decide) (by decide) h₄).symm
    have hq₇ : Function.Injective q₇ := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [q₇, hqne, hz₁, hz₂, hz₃, hz₄]
    have hε₇ : ∀ i, IsSign (ε₇ i) := by
      intro i
      fin_cases i <;> simp [ε₇, hε, hζ]
    let s : Fin 4 → Fin 4 := ![2, 0, 1, 3]
    apply no_exceptional_dual_up_to_row_permutation q₇ hq₇ ε₇ hε₇ S E s
      (by decide)
    · intro i
      fin_cases i <;> simp [q₇, ε₇, s, exceptionalSource, signedBasis,
        hS₀, hS₁, hS₂, hS₃, add_left_comm, add_comm, add_assoc]
    · exact hnormE
    · exact hdual
    · exact hpairE

set_option maxHeartbeats 1000000 in
private theorem no_third_omitting_common_normalized
    {κ : Type*} [DecidableEq κ]
    (q : Fin 5 → κ) (hq : Function.Injective q)
    (ε : Fin 5 → ℤ) (hε : ∀ i, IsSign (ε i))
    (S E : Fin 4 → IntegralLattice κ)
    (hS₀ : S 0 = single (q 0) (ε 0) + single (q 1) (ε 1) +
      single (q 2) (ε 2))
    (hS₁ : S 1 = single (q 0) (ε 0) + single (q 3) (ε 3) +
      single (q 4) (ε 4))
    (h₂₀ : S 2 (q 0) = 0) (h₂₁ : S 2 (q 1) = ε 1)
    (h₂₂ : S 2 (q 2) = 0) (h₂₃ : S 2 (q 3) = ε 3)
    (h₂₄ : S 2 (q 4) = 0)
    (hnormS : ∀ i, normSq (S i) = 3)
    (hpairS : ∀ i j, i ≠ j → coeffDot (S i) (S j) = 1)
    (hnormE : ∀ i, normSq (E i) = 3)
    (hdual : ∀ i j, coeffDot (S i) (E j) = if i = j then 1 else 0)
    (hpairE : ∀ i j, i ≠ j → coeffDot (E i) (E j) = 1) :
    False := by
  have hqne (i j : Fin 5) (hij : i ≠ j) : q i ≠ q j := by
    intro h
    exact hij (hq h)
  obtain ⟨z, ζ, h₁z, h₃z, hζ, hS₂⟩ :=
    complete_two_signed_coefficients (S 2) (hnormS 2)
      (hqne 1 3 (by decide)) (hε 1) (hε 3) h₂₁ h₂₃
  have hz (i : Fin 5) (hi₁ : i ≠ 1) (hi₃ : i ≠ 3)
      (hi : S 2 (q i) = 0) : q i ≠ z := by
    intro hiz
    rw [hS₂, ← hiz] at hi
    simp [hqne 1 i (Ne.symm hi₁), hqne 3 i (Ne.symm hi₃),
      isSign_ne_zero hζ] at hi
  have hz₀ : q 0 ≠ z := hz 0 (by decide) (by decide) h₂₀
  have hz₂ : q 2 ≠ z := hz 2 (by decide) (by decide) h₂₂
  have hz₄ : q 4 ≠ z := hz 4 (by decide) (by decide) h₂₄
  let q₆ : Fin 6 → κ := ![q 0, q 1, q 2, q 3, q 4, z]
  let ε₆ : Fin 6 → ℤ := ![ε 0, ε 1, ε 2, ε 3, ε 4, ζ]
  have hq₆ : Function.Injective q₆ := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [q₆, hqne, hz₀, hz₂, hz₄]
  have hε₆ : ∀ i, IsSign (ε₆ i) := by
    intro i
    fin_cases i <;> simp [ε₆, hε, hζ]
  exact no_fourth_completion_after_three_sources q₆ hq₆ ε₆ hε₆ S E
    (by simpa [q₆, ε₆] using hS₀)
    (by simpa [q₆, ε₆] using hS₁)
    (by simpa [q₆, ε₆] using hS₂)
    hnormS hpairS hnormE hdual hpairE

private theorem normalized_common_propagates_to_third
    {κ : Type*} [DecidableEq κ]
    (q : Fin 5 → κ) (hq : Function.Injective q)
    (ε : Fin 5 → ℤ) (hε : ∀ i, IsSign (ε i))
    (S E : Fin 4 → IntegralLattice κ)
    (hS₀ : S 0 = single (q 0) (ε 0) + single (q 1) (ε 1) +
      single (q 2) (ε 2))
    (hS₁ : S 1 = single (q 0) (ε 0) + single (q 3) (ε 3) +
      single (q 4) (ε 4))
    (hnormS : ∀ i, normSq (S i) = 3)
    (hpairS : ∀ i j, i ≠ j → coeffDot (S i) (S j) = 1)
    (hnormE : ∀ i, normSq (E i) = 3)
    (hdual : ∀ i j, coeffDot (S i) (E j) = if i = j then 1 else 0)
    (hpairE : ∀ i j, i ≠ j → coeffDot (E i) (E j) = 1) :
    S 2 (q 0) = ε 0 := by
  have hqne (i j : Fin 5) (hij : i ≠ j) : q i ≠ q j := by
    intro h
    exact hij (hq h)
  by_contra hcommon
  have ht₀ := line_normalized_coefficients_onehot (S 0) (S 2) (E 0)
    (hqne 0 1 (by decide)) (hqne 0 2 (by decide)) (hqne 1 2 (by decide))
    (hε 0) (hε 1) (hε 2) hS₀ (hnormS 2)
    (hpairS 0 2 (by decide)) (by simpa using hdual 0 0)
    (by simpa using hdual 2 0)
  have ht₁ := line_normalized_coefficients_onehot (S 1) (S 2) (E 1)
    (hqne 0 3 (by decide)) (hqne 0 4 (by decide)) (hqne 3 4 (by decide))
    (hε 0) (hε 3) (hε 4) hS₁ (hnormS 2)
    (hpairS 1 2 (by decide)) (by simpa using hdual 1 1)
    (by simpa using hdual 2 1)
  let t : Fin 5 → ℤ := fun i ↦ ε i * S 2 (q i)
  change (t 0 = 0 ∨ t 0 = 1) ∧ (t 1 = 0 ∨ t 1 = 1) ∧
    (t 2 = 0 ∨ t 2 = 1) ∧ t 0 + t 1 + t 2 = 1 at ht₀
  change (t 0 = 0 ∨ t 0 = 1) ∧ (t 3 = 0 ∨ t 3 = 1) ∧
    (t 4 = 0 ∨ t 4 = 1) ∧ t 0 + t 3 + t 4 = 1 at ht₁
  rcases ht₀ with ⟨ht₀, ht₁', ht₂, hs₀⟩
  rcases ht₁ with ⟨_, ht₃, ht₄, hs₁⟩
  have ht₀z : t 0 = 0 := by
    rcases ht₀ with h | h
    · exact h
    · exact (hcommon (eq_of_sign_mul_eq_one (hε 0) h)).elim
  have hA : (t 1 = 1 ∧ t 2 = 0) ∨ (t 1 = 0 ∧ t 2 = 1) := by
    rcases ht₁' with h | h <;> rcases ht₂ with h' | h' <;> omega
  have hB : (t 3 = 1 ∧ t 4 = 0) ∨ (t 3 = 0 ∧ t 4 = 1) := by
    rcases ht₃ with h | h <;> rcases ht₄ with h' | h' <;> omega
  have coeff_one (i : Fin 5) (hi : t i = 1) : S 2 (q i) = ε i :=
    eq_of_sign_mul_eq_one (hε i) hi
  have coeff_zero (i : Fin 5) (hi : t i = 0) : S 2 (q i) = 0 :=
    eq_zero_of_sign_mul_eq_zero (hε i) hi
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · rcases hA with ⟨h₁, h₂⟩
    rcases hB with ⟨h₃, h₄⟩
    exact no_third_omitting_common_normalized q hq ε hε S E hS₀ hS₁
      (coeff_zero 0 ht₀z) (coeff_one 1 h₁) (coeff_zero 2 h₂)
      (coeff_one 3 h₃) (coeff_zero 4 h₄)
      hnormS hpairS hnormE hdual hpairE
  · rcases hA with ⟨h₁, h₂⟩
    rcases hB with ⟨h₃, h₄⟩
    let p : Fin 5 → Fin 5 := ![0, 1, 2, 4, 3]
    exact no_third_omitting_common_normalized (q ∘ p) (hq.comp (by decide))
      (ε ∘ p) (fun i ↦ hε (p i)) S E
      (by simpa [p, Function.comp_apply] using hS₀)
      (by simpa [p, Function.comp_apply, add_left_comm, add_comm, add_assoc] using hS₁)
      (by simpa [p, Function.comp_apply] using coeff_zero 0 ht₀z)
      (by simpa [p, Function.comp_apply] using coeff_one 1 h₁)
      (by simpa [p, Function.comp_apply] using coeff_zero 2 h₂)
      (by simpa [p, Function.comp_apply] using coeff_one 4 h₄)
      (by simpa [p, Function.comp_apply] using coeff_zero 3 h₃)
      hnormS hpairS hnormE hdual hpairE
  · rcases hA with ⟨h₁, h₂⟩
    rcases hB with ⟨h₃, h₄⟩
    let p : Fin 5 → Fin 5 := ![0, 2, 1, 3, 4]
    exact no_third_omitting_common_normalized (q ∘ p) (hq.comp (by decide))
      (ε ∘ p) (fun i ↦ hε (p i)) S E
      (by simpa [p, Function.comp_apply, add_left_comm, add_comm, add_assoc] using hS₀)
      (by simpa [p, Function.comp_apply] using hS₁)
      (by simpa [p, Function.comp_apply] using coeff_zero 0 ht₀z)
      (by simpa [p, Function.comp_apply] using coeff_one 2 h₂)
      (by simpa [p, Function.comp_apply] using coeff_zero 1 h₁)
      (by simpa [p, Function.comp_apply] using coeff_one 3 h₃)
      (by simpa [p, Function.comp_apply] using coeff_zero 4 h₄)
      hnormS hpairS hnormE hdual hpairE
  · rcases hA with ⟨h₁, h₂⟩
    rcases hB with ⟨h₃, h₄⟩
    let p : Fin 5 → Fin 5 := ![0, 2, 1, 4, 3]
    exact no_third_omitting_common_normalized (q ∘ p) (hq.comp (by decide))
      (ε ∘ p) (fun i ↦ hε (p i)) S E
      (by simpa [p, Function.comp_apply, add_left_comm, add_comm, add_assoc] using hS₀)
      (by simpa [p, Function.comp_apply, add_left_comm, add_comm, add_assoc] using hS₁)
      (by simpa [p, Function.comp_apply] using coeff_zero 0 ht₀z)
      (by simpa [p, Function.comp_apply] using coeff_one 2 h₂)
      (by simpa [p, Function.comp_apply] using coeff_zero 1 h₁)
      (by simpa [p, Function.comp_apply] using coeff_one 4 h₄)
      (by simpa [p, Function.comp_apply] using coeff_zero 3 h₃)
      hnormS hpairS hnormE hdual hpairE

private theorem four_source_common_coordinate
    {κ : Type*} [DecidableEq κ]
    (S E : Fin 4 → IntegralLattice κ)
    (hnormS : ∀ i, normSq (S i) = 3)
    (hpairS : ∀ i j, i ≠ j → coeffDot (S i) (S j) = 1)
    (hnormE : ∀ i, normSq (E i) = 3)
    (hdual : ∀ i j, coeffDot (S i) (E j) = if i = j then 1 else 0)
    (hpairE : ∀ i j, i ≠ j → coeffDot (E i) (E j) = 1) :
    ∃ q ε, IsSign ε ∧ ∀ i, S i q = ε := by
  obtain ⟨q₀, q₁, q₂, ε₀, ε₁, ε₂,
      hq₀₁, hq₀₂, hq₁₂, hε₀, hε₁, hε₂,
      hS₀, h₁₀, h₁₁, h₁₂⟩ :=
    line_meets_in_one_signed_coordinate (S 0) (S 1) (E 0)
      (hnormS 0) (hnormS 1) (hpairS 0 1 (by decide))
      (by simpa using hdual 0 0) (by simpa using hdual 1 0)
  obtain ⟨q₃, q₄, ε₃, ε₄, hq₀₃, hq₀₄, hq₃₄,
      hε₃, hε₄, hS₁⟩ :=
    complete_one_signed_coefficient (S 1) (hnormS 1) q₀ hε₀ h₁₀
  have hq₁₃ : q₁ ≠ q₃ := by
    intro h
    subst q₃
    rw [hS₁] at h₁₁
    simp [hq₀₁, hq₃₄, isSign_ne_zero hε₃] at h₁₁
  have hq₁₄ : q₁ ≠ q₄ := by
    intro h
    subst q₄
    rw [hS₁] at h₁₁
    simp [hq₀₁, hq₃₄, isSign_ne_zero hε₄] at h₁₁
  have hq₂₃ : q₂ ≠ q₃ := by
    intro h
    subst q₃
    rw [hS₁] at h₁₂
    simp [hq₀₂, hq₃₄, isSign_ne_zero hε₃] at h₁₂
  have hq₂₄ : q₂ ≠ q₄ := by
    intro h
    subst q₄
    rw [hS₁] at h₁₂
    simp [hq₀₂, hq₃₄, isSign_ne_zero hε₄] at h₁₂
  let q : Fin 5 → κ := ![q₀, q₁, q₂, q₃, q₄]
  let ε : Fin 5 → ℤ := ![ε₀, ε₁, ε₂, ε₃, ε₄]
  have hq : Function.Injective q := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [q, hq₀₁, hq₀₂, hq₁₂, hq₀₃, hq₀₄, hq₃₄,
        hq₁₃, hq₁₄, hq₂₃, hq₂₄]
  have hε : ∀ i, IsSign (ε i) := by
    intro i
    fin_cases i <;> simp [ε, hε₀, hε₁, hε₂, hε₃, hε₄]
  have h₂₀ := normalized_common_propagates_to_third q hq ε hε S E
    (by simpa [q, ε] using hS₀) (by simpa [q, ε] using hS₁)
    hnormS hpairS hnormE hdual hpairE
  let s : Fin 4 → Fin 4 := ![0, 1, 3, 2]
  have hs : Function.Injective s := by decide
  have h₃₀ := normalized_common_propagates_to_third q hq ε hε
    (fun i ↦ S (s i)) (fun i ↦ E (s i))
    (by simpa [q, ε, s] using hS₀) (by simpa [q, ε, s] using hS₁)
    (fun i ↦ hnormS (s i))
    (fun i j hij ↦ hpairS (s i) (s j) (fun h ↦ hij (hs h)))
    (fun i ↦ hnormE (s i))
    (by
      intro i j
      simpa only [hs.eq_iff] using hdual (s i) (s j))
    (fun i j hij ↦ hpairE (s i) (s j) (fun h ↦ hij (hs h)))
  refine ⟨q₀, ε₀, hε₀, ?_⟩
  intro i
  fin_cases i
  · simpa [hS₀, hq₀₁, hq₀₂, isSign_ne_zero hε₀]
  · exact h₁₀
  · simpa [q, ε] using h₂₀
  · simpa [q, ε, s] using h₃₀

/-- A coordinate common to the four entries of one column cannot also occur
with the same sign at a corner of the other column. -/
private theorem no_corner_common
    {κ : Type*} [DecidableEq κ]
    (S E : Fin 4 → IntegralLattice κ)
    (hnormS : ∀ i, normSq (S i) = 3)
    (hpairS : ∀ i j, i ≠ j → coeffDot (S i) (S j) = 1)
    (hnormE : ∀ i, normSq (E i) = 3)
    (hdual : ∀ i j, coeffDot (S i) (E j) = if i = j then 1 else 0)
    {q : κ} {ε : ℤ} (hε : IsSign ε)
    (hcol : ∀ i, S i q = ε) (hcorner : E 0 q = ε) :
    False := by
  obtain ⟨a, b, δ, γ, hqa, hqb, hab, hδ, hγ, hE₀⟩ :=
    complete_one_signed_coefficient (E 0) (hnormE 0) q hε hcorner
  have hchoice (i : Fin 4) (hi : i ≠ 0) :
      (δ * S i a = -1 ∧ γ * S i b = 0) ∨
      (δ * S i a = 0 ∧ γ * S i b = -1) := by
    have hdot : coeffDot (E 0) (S i) = 0 := by
      simpa [coeffDot_comm, hi] using hdual i 0
    rw [hE₀] at hdot
    simp only [coeffDot_add_left, coeffDot_single_left] at hdot
    have hqprod : ε * S i q = 1 := by
      rw [hcol i]
      exact isSign_sq hε
    have ha := sign_mul_coeff_mem_sign_or_zero_of_normSq_eq_three
      (S i) (hnormS i) a hδ
    have hb := sign_mul_coeff_mem_sign_or_zero_of_normSq_eq_three
      (S i) (hnormS i) b hγ
    rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;> omega
  have contraA (i j : Fin 4) (hij : i ≠ j)
      (hi : δ * S i a = -1) (hj : δ * S j a = -1) : False := by
    obtain ⟨p, η, hη, hip, hjp, huniq⟩ :=
      line_common_coordinate_unique (S i) (S j) (E i)
        (hnormS i) (hnormS j) (hpairS i j hij)
        (by simpa using hdual i i)
        (by simpa [Ne.symm hij] using hdual j i)
    have hiq : S i q ≠ 0 := by rw [hcol i]; exact isSign_ne_zero hε
    have hjq : S j q ≠ 0 := by rw [hcol j]; exact isSign_ne_zero hε
    have hia : S i a ≠ 0 := by
      intro h
      simp [h] at hi
    have hja : S j a ≠ 0 := by
      intro h
      simp [h] at hj
    exact hqa ((huniq q hiq hjq).trans (huniq a hia hja).symm)
  have contraB (i j : Fin 4) (hij : i ≠ j)
      (hi : γ * S i b = -1) (hj : γ * S j b = -1) : False := by
    obtain ⟨p, η, hη, hip, hjp, huniq⟩ :=
      line_common_coordinate_unique (S i) (S j) (E i)
        (hnormS i) (hnormS j) (hpairS i j hij)
        (by simpa using hdual i i)
        (by simpa [Ne.symm hij] using hdual j i)
    have hiq : S i q ≠ 0 := by rw [hcol i]; exact isSign_ne_zero hε
    have hjq : S j q ≠ 0 := by rw [hcol j]; exact isSign_ne_zero hε
    have hib : S i b ≠ 0 := by
      intro h
      simp [h] at hi
    have hjb : S j b ≠ 0 := by
      intro h
      simp [h] at hj
    exact hqb ((huniq q hiq hjq).trans (huniq b hib hjb).symm)
  have h₁ := hchoice 1 (by decide)
  have h₂ := hchoice 2 (by decide)
  have h₃ := hchoice 3 (by decide)
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;>
    rcases h₃ with h₃ | h₃
  · exact contraA 1 2 (by decide) h₁.1 h₂.1
  · exact contraA 1 2 (by decide) h₁.1 h₂.1
  · exact contraA 1 3 (by decide) h₁.1 h₃.1
  · exact contraB 2 3 (by decide) h₂.2 h₃.2
  · exact contraA 2 3 (by decide) h₂.1 h₃.1
  · exact contraB 1 3 (by decide) h₁.2 h₃.2
  · exact contraB 1 2 (by decide) h₁.2 h₂.2
  · exact contraB 1 2 (by decide) h₁.2 h₂.2

private theorem corner_coefficient_zero
    {κ : Type*} [DecidableEq κ]
    (S E : Fin 4 → IntegralLattice κ)
    (hnormS : ∀ i, normSq (S i) = 3)
    (hpairS : ∀ i j, i ≠ j → coeffDot (S i) (S j) = 1)
    (hnormE : ∀ i, normSq (E i) = 3)
    (hdual : ∀ i j, coeffDot (S i) (E j) = if i = j then 1 else 0)
    {q : κ} {ε : ℤ} (hε : IsSign ε) (hcol : ∀ i, S i q = ε) :
    E 0 q = 0 := by
  obtain ⟨a, b, δ, γ, hqa, hqb, hab, hδ, hγ, hS₀⟩ :=
    complete_one_signed_coefficient (S 0) (hnormS 0) q hε (hcol 0)
  have hneg : ε * E 0 q ≠ -1 :=
    no_opposite_first (S 0) (E 0) (S 1) hqa hqb hab hε hδ hγ hS₀
      (hnormE 0) (by simpa using hdual 0 0) (hpairS 0 1 (by decide))
      (by simpa [coeffDot_comm] using hdual 1 0)
  have ht := sign_mul_coeff_mem_sign_or_zero_of_normSq_eq_three
    (E 0) (hnormE 0) q hε
  rcases ht with ht | ht | ht
  · exact (hneg ht).elim
  · exact eq_zero_of_sign_mul_eq_zero hε ht
  · exact (no_corner_common S E hnormS hpairS hnormE hdual hε hcol
      (eq_of_sign_mul_eq_one hε ht)).elim

private theorem four_by_two_first_column_coefficients
    {κ : Type*} [DecidableEq κ]
    (S E : Fin 4 → IntegralLattice κ)
    (hnormS : ∀ i, normSq (S i) = 3)
    (hpairS : ∀ i j, i ≠ j → coeffDot (S i) (S j) = 1)
    (hnormE : ∀ i, normSq (E i) = 3)
    (hdual : ∀ i j, coeffDot (S i) (E j) = if i = j then 1 else 0)
    (hpairE : ∀ i j, i ≠ j → coeffDot (E i) (E j) = 1) :
    ∃ q ε, IsSign ε ∧ (∀ i, S i q = ε) ∧ (∀ i, E i q = 0) := by
  obtain ⟨q, ε, hε, hcol⟩ :=
    four_source_common_coordinate S E hnormS hpairS hnormE hdual hpairE
  have permZero (s : Fin 4 → Fin 4) (hs : Function.Injective s) : E (s 0) q = 0 := by
    have hz := corner_coefficient_zero (fun i ↦ S (s i)) (fun i ↦ E (s i))
      (fun i ↦ hnormS (s i))
      (fun i j hij ↦ hpairS (s i) (s j) (fun h ↦ hij (hs h)))
      (fun i ↦ hnormE (s i))
      (by
        intro i j
        simpa only [hs.eq_iff] using hdual (s i) (s j))
      hε (fun i ↦ hcol (s i))
    exact hz
  refine ⟨q, ε, hε, hcol, ?_⟩
  intro i
  fin_cases i
  · simpa using permZero ![0, 1, 2, 3] (by decide)
  · simpa using permZero ![1, 0, 2, 3] (by decide)
  · simpa using permZero ![2, 0, 1, 3] (by decide)
  · simpa using permZero ![3, 0, 1, 2] (by decide)

private theorem four_by_two_first_column_pivot
    {κ : Type*} [DecidableEq κ]
    (B : Fin 4 → Fin 2 → IntegralLattice κ)
    (hgram : ∀ i j i' j',
      coeffDot (B i j) (B i' j') =
        ((if i = i' then 2 else 1) * (if j = j' then 2 else 1) - 1)) :
    ∃ q ε, IsSign ε ∧ ∀ i j,
      coeffDot (B i j) (single q ε) = if j = 0 then 1 else 0 := by
  let S : Fin 4 → IntegralLattice κ := fun i ↦ B i 0
  let E : Fin 4 → IntegralLattice κ := fun i ↦ B i 1
  have hnormS (i : Fin 4) : normSq (S i) = 3 := by
    simpa [S, normSq] using hgram i 0 i 0
  have hpairS (i j : Fin 4) (hij : i ≠ j) : coeffDot (S i) (S j) = 1 := by
    simpa [S, hij] using hgram i 0 j 0
  have hnormE (i : Fin 4) : normSq (E i) = 3 := by
    simpa [E, normSq] using hgram i 1 i 1
  have hpairE (i j : Fin 4) (hij : i ≠ j) : coeffDot (E i) (E j) = 1 := by
    simpa [E, hij] using hgram i 1 j 1
  have hdual (i j : Fin 4) : coeffDot (S i) (E j) = if i = j then 1 else 0 := by
    by_cases hij : i = j
    · subst j
      simpa [S, E] using hgram i 0 i 1
    · simpa [S, E, hij] using hgram i 0 j 1
  obtain ⟨q, ε, hε, hS, hE⟩ :=
    four_by_two_first_column_coefficients S E hnormS hpairS hnormE hdual hpairE
  refine ⟨q, ε, hε, ?_⟩
  intro i j
  fin_cases j
  · simp [coeffDot_single_right, S, hS i, isSign_sq hε]
  · simp [coeffDot_single_right, E, hE i]

private theorem common_signed_coordinate_eq
    {κ : Type*} [DecidableEq κ]
    (a b d : IntegralLattice κ)
    (hna : normSq a = 3) (hnb : normSq b = 3)
    (hab : coeffDot a b = 1) (had : coeffDot a d = 1)
    (hbd : coeffDot b d = 0)
    {q q' : κ} {ε ε' : ℤ} (hε : IsSign ε) (hε' : IsSign ε')
    (haq : a q = ε) (hbq : b q = ε)
    (haq' : a q' = ε') (hbq' : b q' = ε') :
    q = q' ∧ ε = ε' := by
  obtain ⟨p, η, hη, hap, hbp, huniq⟩ :=
    line_common_coordinate_unique a b d hna hnb hab had hbd
  have hqp := huniq q (by rw [haq]; exact isSign_ne_zero hε)
    (by rw [hbq]; exact isSign_ne_zero hε)
  have hq'p := huniq q' (by rw [haq']; exact isSign_ne_zero hε')
    (by rw [hbq']; exact isSign_ne_zero hε')
  have hqq' : q = q' := hqp.trans hq'p.symm
  refine ⟨hqq', ?_⟩
  calc
    ε = a q := haq.symm
    _ = a q' := by rw [hqq']
    _ = ε' := haq'

private theorem vector_four_injective
    {α : Type*} [DecidableEq α] {a b c d : α}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Function.Injective ![a, b, c, d] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all

private theorem column_pivot_of_four_le_rows
    {κ : Type*} [DecidableEq κ]
    {r c : ℕ} (hr₄ : 4 ≤ r) (hc₂ : 2 ≤ c)
    (B : Fin r → Fin c → IntegralLattice κ)
    (hgram : ∀ i j i' j',
      coeffDot (B i j) (B i' j') =
        ((if i = i' then 2 else 1) * (if j = j' then 2 else 1) - 1))
    (j₀ : Fin c) :
    ∃ q ε, IsSign ε ∧ ∀ i j,
      coeffDot (B i j) (single q ε) = if j = j₀ then 1 else 0 := by
  have hc : 1 < Fintype.card (Fin c) := by
    simpa only [Fintype.card_fin] using (show 1 < c by omega)
  obtain ⟨j₁, hj₁₀⟩ := Fintype.exists_ne_of_one_lt_card hc j₀
  have hj₀₁ : j₀ ≠ j₁ := hj₁₀.symm
  let rows₀ : Fin 4 ↪ Fin r := Fin.castLEEmb hr₄
  let cols₀ : Fin 2 → Fin c := ![j₀, j₁]
  have hcols₀ : Function.Injective cols₀ := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [cols₀]
  have hgram₀ (i j i' j') :
      coeffDot (B (rows₀ i) (cols₀ j)) (B (rows₀ i') (cols₀ j')) =
        ((if i = i' then 2 else 1) * (if j = j' then 2 else 1) - 1) := by
    simpa only [rows₀.injective.eq_iff, hcols₀.eq_iff] using
      hgram (rows₀ i) (cols₀ j) (rows₀ i') (cols₀ j')
  obtain ⟨q, ε, hε, hp₀⟩ := four_by_two_first_column_pivot
    (fun i j ↦ B (rows₀ i) (cols₀ j)) hgram₀
  have hbase (i : Fin 4) : B (rows₀ i) j₀ q = ε := by
    apply eq_of_sign_mul_eq_one hε
    simpa [cols₀, coeffDot_single_right, mul_comm] using hp₀ i 0
  let a := B (rows₀ 0) j₀
  let b := B (rows₀ 1) j₀
  let d := B (rows₀ 0) j₁
  have hna : normSq a = 3 := by simpa [a, normSq] using hgram (rows₀ 0) j₀ (rows₀ 0) j₀
  have hnb : normSq b = 3 := by simpa [b, normSq] using hgram (rows₀ 1) j₀ (rows₀ 1) j₀
  have hr₀₁ : rows₀ 0 ≠ rows₀ 1 := fun h ↦ (by decide : (0 : Fin 4) ≠ 1) (rows₀.injective h)
  have hr₀₂ : rows₀ 0 ≠ rows₀ 2 := fun h ↦ (by decide : (0 : Fin 4) ≠ 2) (rows₀.injective h)
  have hr₁₂ : rows₀ 1 ≠ rows₀ 2 := fun h ↦ (by decide : (1 : Fin 4) ≠ 2) (rows₀.injective h)
  have hab : coeffDot a b = 1 := by
    simpa [a, b, hr₀₁] using hgram (rows₀ 0) j₀ (rows₀ 1) j₀
  have had : coeffDot a d = 1 := by
    simpa [a, d, hj₀₁] using hgram (rows₀ 0) j₀ (rows₀ 0) j₁
  have hbd : coeffDot b d = 0 := by
    simpa [b, d, hr₀₁.symm, hj₀₁] using
      hgram (rows₀ 1) j₀ (rows₀ 0) j₁
  have restricted (rows : Fin 4 → Fin r) (hrows : Function.Injective rows)
      (hr₀ : rows 0 = rows₀ 0) (hr₁ : rows 1 = rows₀ 1)
      (j : Fin c) (hj : j ≠ j₀) :
      ∀ k l, coeffDot (B (rows k) (![j₀, j] l)) (single q ε) =
        if l = 0 then 1 else 0 := by
    let cols : Fin 2 → Fin c := ![j₀, j]
    have hcols : Function.Injective cols := by
      intro x y h
      fin_cases x <;> fin_cases y <;> simp_all [cols]
    have hgram' (i l i' l') :
        coeffDot (B (rows i) (cols l)) (B (rows i') (cols l')) =
          ((if i = i' then 2 else 1) * (if l = l' then 2 else 1) - 1) := by
      simpa only [hrows.eq_iff, hcols.eq_iff] using
        hgram (rows i) (cols l) (rows i') (cols l')
    obtain ⟨q', ε', hε', hp'⟩ := four_by_two_first_column_pivot
      (fun i l ↦ B (rows i) (cols l)) hgram'
    have hq'₀ : B (rows₀ 0) j₀ q' = ε' := by
      rw [← hr₀]
      apply eq_of_sign_mul_eq_one hε'
      simpa [cols, coeffDot_single_right, mul_comm] using hp' 0 0
    have hq'₁ : B (rows₀ 1) j₀ q' = ε' := by
      rw [← hr₁]
      apply eq_of_sign_mul_eq_one hε'
      simpa [cols, coeffDot_single_right, mul_comm] using hp' 1 0
    have heq := common_signed_coordinate_eq a b d hna hnb hab had hbd hε hε'
      (by simpa [a] using hbase 0) (by simpa [b] using hbase 1)
      (by simpa [a] using hq'₀) (by simpa [b] using hq'₁)
    rcases heq with ⟨rfl, rfl⟩
    simpa [cols] using hp'
  have hcol (i : Fin r) : coeffDot (B i j₀) (single q ε) = 1 := by
    by_cases hi₀ : i = rows₀ 0
    · subst i
      simpa [cols₀] using hp₀ 0 0
    by_cases hi₁ : i = rows₀ 1
    · subst i
      simpa [cols₀] using hp₀ 1 0
    by_cases hi₂ : i = rows₀ 2
    · subst i
      simpa [cols₀] using hp₀ 2 0
    let rows : Fin 4 → Fin r := ![rows₀ 0, rows₀ 1, rows₀ 2, i]
    have hrows : Function.Injective rows := by
      simpa [rows] using vector_four_injective hr₀₁ hr₀₂ (Ne.symm hi₀)
        hr₁₂ (Ne.symm hi₁) (Ne.symm hi₂)
    have h := restricted rows hrows (by simp [rows]) (by simp [rows]) j₁ hj₁₀ 3 0
    change coeffDot (B i j₀) (single q ε) = 1 at h
    exact h
  refine ⟨q, ε, hε, ?_⟩
  intro i j
  by_cases hj : j = j₀
  · subst j
    simpa using hcol i
  by_cases hi₀ : i = rows₀ 0
  · subst i
    have h := restricted rows₀ rows₀.injective rfl rfl j hj 0 1
    change coeffDot (B (rows₀ 0) j) (single q ε) = 0 at h
    rw [if_neg hj]
    exact h
  by_cases hi₁ : i = rows₀ 1
  · subst i
    have h := restricted rows₀ rows₀.injective rfl rfl j hj 1 1
    change coeffDot (B (rows₀ 1) j) (single q ε) = 0 at h
    rw [if_neg hj]
    exact h
  by_cases hi₂ : i = rows₀ 2
  · subst i
    have h := restricted rows₀ rows₀.injective rfl rfl j hj 2 1
    change coeffDot (B (rows₀ 2) j) (single q ε) = 0 at h
    rw [if_neg hj]
    exact h
  let rows : Fin 4 → Fin r := ![rows₀ 0, rows₀ 1, rows₀ 2, i]
  have hrows : Function.Injective rows := by
    simpa [rows] using vector_four_injective hr₀₁ hr₀₂ (Ne.symm hi₀)
      hr₁₂ (Ne.symm hi₁) (Ne.symm hi₂)
  have h := restricted rows hrows (by simp [rows]) (by simp [rows]) j hj 3 1
  change coeffDot (B i j) (single q ε) = 0 at h
  rw [if_neg hj]
  exact h

private theorem row_pivot_of_four_le_columns
    {κ : Type*} [DecidableEq κ]
    {r c : ℕ} (hc₄ : 4 ≤ c) (hr₂ : 2 ≤ r)
    (B : Fin r → Fin c → IntegralLattice κ)
    (hgram : ∀ i j i' j',
      coeffDot (B i j) (B i' j') =
        ((if i = i' then 2 else 1) * (if j = j' then 2 else 1) - 1))
    (i₀ : Fin r) :
    ∃ q ε, IsSign ε ∧ ∀ i j,
      coeffDot (B i j) (single q ε) = if i = i₀ then 1 else 0 := by
  have hgramT (j i j' i') :
      coeffDot (B i j) (B i' j') =
        ((if j = j' then 2 else 1) * (if i = i' then 2 else 1) - 1) := by
    simpa only [mul_comm] using hgram i j i' j'
  obtain ⟨q, ε, hε, hp⟩ := column_pivot_of_four_le_rows hc₄ hr₂
    (fun j i ↦ B i j) hgramT i₀
  exact ⟨q, ε, hε, fun i j ↦ hp j i⟩

private theorem column_pivot_of_two_rows
    {κ : Type*} [DecidableEq κ]
    {c : ℕ} (hc₄ : 4 ≤ c)
    (B : Fin 2 → Fin c → IntegralLattice κ)
    (hgram : ∀ i j i' j',
      coeffDot (B i j) (B i' j') =
        ((if i = i' then 2 else 1) * (if j = j' then 2 else 1) - 1))
    (j₀ : Fin c) :
    ∃ q ε, IsSign ε ∧ ∀ i j,
      coeffDot (B i j) (single q ε) = if j = j₀ then 1 else 0 := by
  obtain ⟨q₀, ε₀, hε₀, hp₀⟩ :=
    row_pivot_of_four_le_columns hc₄ (by omega) B hgram (0 : Fin 2)
  obtain ⟨q₁, ε₁, hε₁, hp₁⟩ :=
    row_pivot_of_four_le_columns hc₄ (by omega) B hgram (1 : Fin 2)
  have hq₀₀ (j : Fin c) : B 0 j q₀ = ε₀ := by
    apply eq_of_sign_mul_eq_one hε₀
    simpa [coeffDot_single_right, mul_comm] using hp₀ 0 j
  have hq₀₁ (j : Fin c) : B 1 j q₀ = 0 := by
    apply eq_zero_of_sign_mul_eq_zero hε₀
    simpa [coeffDot_single_right, mul_comm] using hp₀ 1 j
  have hq₁₀ (j : Fin c) : B 0 j q₁ = 0 := by
    apply eq_zero_of_sign_mul_eq_zero hε₁
    simpa [coeffDot_single_right, mul_comm] using hp₁ 0 j
  have hq₁₁ (j : Fin c) : B 1 j q₁ = ε₁ := by
    apply eq_of_sign_mul_eq_one hε₁
    simpa [coeffDot_single_right, mul_comm] using hp₁ 1 j
  have hc : 1 < Fintype.card (Fin c) := by
    simpa only [Fintype.card_fin] using (show 1 < c by omega)
  obtain ⟨j₁, hj₁₀⟩ := Fintype.exists_ne_of_one_lt_card hc j₀
  have hj₀₁ : j₀ ≠ j₁ := hj₁₀.symm
  let a := B 0 j₀
  let b := B 1 j₀
  let d := B 0 j₁
  have hna : normSq a = 3 := by
    simpa [a, normSq] using hgram 0 j₀ 0 j₀
  have hnb : normSq b = 3 := by
    simpa [b, normSq] using hgram 1 j₀ 1 j₀
  have hab : coeffDot a b = 1 := by
    simpa [a, b] using hgram 0 j₀ 1 j₀
  have had : coeffDot a d = 1 := by
    simpa [a, d, hj₀₁] using hgram 0 j₀ 0 j₁
  have hbd : coeffDot b d = 0 := by
    simpa [b, d, hj₀₁] using hgram 1 j₀ 0 j₁
  obtain ⟨q, ε, hε, haq, hbq, _⟩ :=
    line_common_coordinate_unique a b d hna hnb hab had hbd
  have haq' : B 0 j₀ q = ε := by simpa [a] using haq
  have hbq' : B 1 j₀ q = ε := by simpa [b] using hbq
  have hoff₀ (j : Fin c) (hj : j ≠ j₀) : B 0 j q = 0 := by
    by_contra hqj
    obtain ⟨p, η, hη, hap, hbp, huniq⟩ := line_common_coordinate_unique
      (B 0 j₀) (B 0 j) (B 1 j₀)
      (by simpa [normSq] using hgram 0 j₀ 0 j₀)
      (by simpa [normSq] using hgram 0 j 0 j)
      (by simpa [Ne.symm hj] using hgram 0 j₀ 0 j)
      (by simpa using hgram 0 j₀ 1 j₀)
      (by simpa [hj] using hgram 0 j 1 j₀)
    have hqp : q = p := huniq q
      (by rw [haq']; exact isSign_ne_zero hε) hqj
    have hq₀p : q₀ = p := huniq q₀
      (by rw [hq₀₀]; exact isSign_ne_zero hε₀)
      (by rw [hq₀₀]; exact isSign_ne_zero hε₀)
    have hqq₀ : q = q₀ := hqp.trans hq₀p.symm
    have hz := hq₀₁ j₀
    rw [← hqq₀, hbq'] at hz
    exact isSign_ne_zero hε hz
  have hoff₁ (j : Fin c) (hj : j ≠ j₀) : B 1 j q = 0 := by
    by_contra hqj
    obtain ⟨p, η, hη, hap, hbp, huniq⟩ := line_common_coordinate_unique
      (B 1 j₀) (B 1 j) (B 0 j₀)
      (by simpa [normSq] using hgram 1 j₀ 1 j₀)
      (by simpa [normSq] using hgram 1 j 1 j)
      (by simpa [Ne.symm hj] using hgram 1 j₀ 1 j)
      (by simpa using hgram 1 j₀ 0 j₀)
      (by simpa [hj] using hgram 1 j 0 j₀)
    have hqp : q = p := huniq q
      (by rw [hbq']; exact isSign_ne_zero hε) hqj
    have hq₁p : q₁ = p := huniq q₁
      (by rw [hq₁₁]; exact isSign_ne_zero hε₁)
      (by rw [hq₁₁]; exact isSign_ne_zero hε₁)
    have hqq₁ : q = q₁ := hqp.trans hq₁p.symm
    have hz := hq₁₀ j₀
    rw [← hqq₁, haq'] at hz
    exact isSign_ne_zero hε hz
  refine ⟨q, ε, hε, ?_⟩
  intro i j
  by_cases hj : j = j₀
  · subst j
    fin_cases i
    · simp [coeffDot_single_right, haq', isSign_sq hε]
    · simp [coeffDot_single_right, hbq', isSign_sq hε]
  · rw [if_neg hj]
    fin_cases i
    · simp [coeffDot_single_right, hoff₀ j hj]
    · simp [coeffDot_single_right, hoff₁ j hj]

/-- The column-pivot lemma for the rectangular Gram configuration used in
`PFsection3`: every chosen column is detected by a signed basis vector. -/
theorem column_pivot
    {κ : Type*} [DecidableEq κ]
    {r c : ℕ}
    (β : Fin r → Fin c → IntegralLattice κ)
    (hrOdd : Odd (r + 1)) (hcOdd : Odd (c + 1))
    (hr : 1 < r) (hc : 1 < c) (hrc : r ≠ c)
    (hgram : ∀ i j i' j',
      coeffDot (β i j) (β i' j') =
        ((if i = i' then 2 else 1) * (if j = j' then 2 else 1) - 1))
    (j₀ : Fin c) :
    ∃ q ε, IsSign ε ∧ ∀ i j,
      coeffDot (β i j) (single q ε) = if j = j₀ then 1 else 0 := by
  have hr_cases : r = 2 ∨ 4 ≤ r := by
    rcases hrOdd with ⟨k, hk⟩
    omega
  rcases hr_cases with rfl | hr₄
  · have hc₄ : 4 ≤ c := by
      rcases hcOdd with ⟨k, hk⟩
      omega
    exact column_pivot_of_two_rows hc₄ β hgram j₀
  · exact column_pivot_of_four_le_rows hr₄ (by omega) β hgram j₀

/-- The row-pivot form, obtained by transposing the rectangular Gram
configuration. -/
theorem row_pivot
    {κ : Type*} [DecidableEq κ]
    {r c : ℕ}
    (β : Fin r → Fin c → IntegralLattice κ)
    (hrOdd : Odd (r + 1)) (hcOdd : Odd (c + 1))
    (hr : 1 < r) (hc : 1 < c) (hrc : r ≠ c)
    (hgram : ∀ i j i' j',
      coeffDot (β i j) (β i' j') =
        ((if i = i' then 2 else 1) * (if j = j' then 2 else 1) - 1))
    (i₀ : Fin r) :
    ∃ q ε, IsSign ε ∧ ∀ i j,
      coeffDot (β i j) (single q ε) = if i = i₀ then 1 else 0 := by
  have hgramT (j i j' i') :
      coeffDot (β i j) (β i' j') =
        ((if j = j' then 2 else 1) * (if i = i' then 2 else 1) - 1) := by
    simpa only [mul_comm] using hgram i j i' j'
  obtain ⟨q, ε, hε, hp⟩ := column_pivot (fun j i ↦ β i j)
    hcOdd hrOdd hc hr (Ne.symm hrc) hgramT i₀
  exact ⟨q, ε, hε, fun i j ↦ hp j i⟩

end

end Submission.OddOrder.PF
