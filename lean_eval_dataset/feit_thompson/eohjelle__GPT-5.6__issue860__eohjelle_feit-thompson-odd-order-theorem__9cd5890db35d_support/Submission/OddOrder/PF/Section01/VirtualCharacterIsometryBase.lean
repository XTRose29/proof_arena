import Submission.OddOrder.PF.Section01.VirtualCharacterIsometry

/-!
The tuple-level integral-lattice form of Peterfalvi 1.4.

The input family abstracts the images under Peterfalvi's partial character
isometry of the differences `Chi_i - Chi_0`.  Pairing preservation says that
distinct nonbase images have pairing one; membership in the off-identity
virtual-character lattice supplies augmentation zero.  The conclusion is the
common signed-difference pattern with an injective target index map.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Finsupp

private theorem isSign_neg {ε : ℤ} (hε : IsSign ε) : IsSign (-ε) := by
  rcases hε with rfl | rfl <;> simp [IsSign]

private theorem smul_single_sub_single_reverse {ι : Type*} [DecidableEq ι]
    (ε : ℤ) (a b : ι) :
    ε • (single b 1 - single a 1 : IntegralLattice ι) =
      (-ε) • (single a 1 - single b 1) := by
  rw [neg_smul, ← smul_neg, neg_sub]

/-- A signed difference that pairs to one with two consistently oriented
anchor differences can itself be oriented with their common endpoint and
common sign.  This is the tuple induction step extracted from
`vchar_isometry_base4`. -/
private theorem align_signedDifference {ι : Type*} [DecidableEq ι]
    (σ δ : ℤ) (a c b n m : ι)
    (hσ : IsSign σ) (hδ : IsSign δ)
    (hac : a ≠ c) (hab : a ≠ b) (hcb : c ≠ b) (hnm : n ≠ m)
    (h₁ : coeffDot
      (δ • (single n 1 - single m 1 : IntegralLattice ι))
      (σ • (single a 1 - single b 1)) = 1)
    (h₂ : coeffDot
      (δ • (single n 1 - single m 1 : IntegralLattice ι))
      (σ • (single c 1 - single b 1)) = 1) :
    ∃ x, x ≠ b ∧
      δ • (single n 1 - single m 1 : IntegralLattice ι) =
        σ • (single x 1 - single b 1) := by
  rw [coeffDot_smul_left, coeffDot_smul_right] at h₁ h₂
  rcases hσ with rfl | rfl <;> rcases hδ with rfl | rfl
  · simp only [one_mul] at h₁ h₂
    have hb := vchar_isometry_base4 1 b a c n m (Or.inl rfl)
      hac hab hcb h₁ h₂
    have hmb : m = b := hb.1 rfl
    subst m
    exact ⟨n, hnm, by simp⟩
  · norm_num only [one_mul, neg_mul, neg_neg] at h₁ h₂
    have h₁' : coeffDot (single n 1 - single m 1 : IntegralLattice ι)
        (single a 1 - single b 1) = -1 := by linarith
    have h₂' : coeffDot (single n 1 - single m 1 : IntegralLattice ι)
        (single c 1 - single b 1) = -1 := by linarith
    have hb := vchar_isometry_base4 (-1) b a c n m (Or.inr rfl)
      hac hab hcb h₁' h₂'
    have hnb : n = b := hb.2 rfl
    subst n
    exact ⟨m, hnm.symm, by simp⟩
  · norm_num only [one_mul, neg_mul, neg_neg] at h₁ h₂
    have h₁' : coeffDot (single n 1 - single m 1 : IntegralLattice ι)
        (single a 1 - single b 1) = -1 := by linarith
    have h₂' : coeffDot (single n 1 - single m 1 : IntegralLattice ι)
        (single c 1 - single b 1) = -1 := by linarith
    have hb := vchar_isometry_base4 (-1) b a c n m (Or.inr rfl)
      hac hab hcb h₁' h₂'
    have hnb : n = b := hb.2 rfl
    subst n
    exact ⟨m, hnm.symm, by simp⟩
  · norm_num only [one_mul, neg_mul, neg_neg] at h₁ h₂
    have hb := vchar_isometry_base4 1 b a c n m (Or.inl rfl)
      hac hab hcb h₁ h₂
    have hmb : m = b := hb.1 rfl
    subst m
    exact ⟨n, hnm, by simp⟩

/-- The two-member case of Peterfalvi 1.4. -/
private theorem vchar_isometry_base_two {κ : Type*}
    (F : Fin 2 → IntegralLattice κ)
    (hzero : F 0 = 0)
    (hnorm : ∀ i, i ≠ 0 → normSq (F i) = 2)
    (hsum : ∀ i, coeffSum (F i) = 0) :
    ∃ μ : Fin 2 → κ, Function.Injective μ ∧
      ∃ ε : ℤ, IsSign ε ∧ ∀ i,
        F i = ε • (single (μ i) 1 - single (μ 0) 1) := by
  classical
  obtain ⟨a, b, ε, hab, hε, hF⟩ :=
    eq_sign_smul_single_sub_single_of_normSq_eq_two (F 1)
      (hnorm 1 (by decide)) (hsum 1)
  let μ : Fin 2 → κ := ![b, a]
  refine ⟨μ, ?_, ε, hε, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [μ]
  · intro i
    fin_cases i
    · simp [μ, hzero]
    · simpa [μ] using hF

/-- The at-least-three-member case of Peterfalvi 1.4. -/
private theorem vchar_isometry_base_three_add {r : ℕ} {κ : Type*}
    (F : Fin (r + 3) → IntegralLattice κ)
    (hzero : F 0 = 0)
    (hnorm : ∀ i, i ≠ 0 → normSq (F i) = 2)
    (hsum : ∀ i, coeffSum (F i) = 0)
    (hpair : ∀ i j, i ≠ 0 → j ≠ 0 → i ≠ j →
      coeffDot (F i) (F j) = 1) :
    ∃ μ : Fin (r + 3) → κ, Function.Injective μ ∧
      ∃ ε : ℤ, IsSign ε ∧ ∀ i,
        F i = ε • (single (μ i) 1 - single (μ 0) 1) := by
  classical
  let u : Fin (r + 3) := ⟨1, by omega⟩
  let v : Fin (r + 3) := ⟨2, by omega⟩
  have hu0 : u ≠ 0 := by simp [u]
  have hv0 : v ≠ 0 := by simp [v]
  have huv : u ≠ v := by simp [u, v]
  obtain ⟨a, b, c, ε, hab, hbc, hac, hε, hFu, hFv⟩ :=
    vchar_isometry_base3 (F u) (F v)
      (hnorm u hu0) (hsum u) (hnorm v hv0) (hsum v)
      (hpair u v hu0 hv0 huv)
  let σ : ℤ := -ε
  have hσ : IsSign σ := isSign_neg hε
  have hFu' : F u = σ • (single a 1 - single b 1) := by
    rw [hFu]
    exact smul_single_sub_single_reverse ε a b
  have hFv' : F v = σ • (single c 1 - single b 1) := by
    rw [hFv]
    exact smul_single_sub_single_reverse ε c b
  have hexists : ∀ q : Fin (r + 3), q ≠ 0 →
      ∃ x, x ≠ b ∧ F q = σ • (single x 1 - single b 1) := by
    intro q hq0
    by_cases hqu : q = u
    · subst q
      exact ⟨a, hab, hFu'⟩
    by_cases hqv : q = v
    · subst q
      exact ⟨c, hbc.symm, hFv'⟩
    obtain ⟨n, m, δ, hnm, hδ, hFq⟩ :=
      eq_sign_smul_single_sub_single_of_normSq_eq_two (F q)
        (hnorm q hq0) (hsum q)
    have hquPair : coeffDot (F q) (F u) = 1 :=
      hpair q u hq0 hu0 hqu
    have hqvPair : coeffDot (F q) (F v) = 1 :=
      hpair q v hq0 hv0 hqv
    rw [hFq, hFu'] at hquPair
    rw [hFq, hFv'] at hqvPair
    obtain ⟨x, hxb, hx⟩ := align_signedDifference σ δ a c b n m
      hσ hδ hac hab hbc.symm hnm hquPair hqvPair
    exact ⟨x, hxb, hFq.trans hx⟩
  let μ : Fin (r + 3) → κ := fun q ↦ if hq : q = 0 then b else (hexists q hq).choose
  have hμzero : μ 0 = b := by simp [μ]
  have hμne (q : Fin (r + 3)) (hq0 : q ≠ 0) : μ q ≠ b := by
    simpa [μ, hq0] using (hexists q hq0).choose_spec.1
  have hμrep (q : Fin (r + 3)) (hq0 : q ≠ 0) :
      F q = σ • (single (μ q) 1 - single b 1) := by
    simpa [μ, hq0] using (hexists q hq0).choose_spec.2
  refine ⟨μ, ?_, σ, hσ, ?_⟩
  · intro q s hqs
    by_cases hq0 : q = 0
    · subst q
      by_contra hs0
      exact hμne s (fun h ↦ hs0 h.symm) (by simpa [hμzero] using hqs.symm)
    by_cases hs0 : s = 0
    · subst s
      exact False.elim (hμne q hq0 (by simpa [hμzero] using hqs))
    by_contra hqne
    have hFqs : F q = F s := by
      rw [hμrep q hq0, hμrep s hs0, hqs]
    have hp := hpair q s hq0 hs0 hqne
    rw [← hFqs] at hp
    have hn := hnorm q hq0
    rw [normSq] at hn
    omega
  · intro q
    by_cases hq0 : q = 0
    · subst q
      simp [hzero, hμzero]
    · simpa [hμzero] using hμrep q hq0

/-- Tuple-level Peterfalvi 1.4 for the present integral-lattice API.

`F i` represents the image of `Chi_i - Chi_0`.  The three hypotheses after
`hzero` are precisely the norm, augmentation, and off-diagonal pairing facts
obtained from an isometry on the augmentation-zero virtual-character lattice.
-/
theorem vchar_isometry_base {m : ℕ} {κ : Type*}
    (F : Fin (m + 2) → IntegralLattice κ)
    (hzero : F 0 = 0)
    (hnorm : ∀ i, i ≠ 0 → normSq (F i) = 2)
    (hsum : ∀ i, coeffSum (F i) = 0)
    (hpair : ∀ i j, i ≠ 0 → j ≠ 0 → i ≠ j →
      coeffDot (F i) (F j) = 1) :
    ∃ μ : Fin (m + 2) → κ, Function.Injective μ ∧
      ∃ ε : ℤ, IsSign ε ∧ ∀ i,
        F i = ε • (single (μ i) 1 - single (μ 0) 1) := by
  cases m with
  | zero =>
      simpa using vchar_isometry_base_two F hzero hnorm hsum
  | succ r =>
      exact vchar_isometry_base_three_add (r := r) F hzero hnorm hsum hpair

end

end Submission.OddOrder.PF
