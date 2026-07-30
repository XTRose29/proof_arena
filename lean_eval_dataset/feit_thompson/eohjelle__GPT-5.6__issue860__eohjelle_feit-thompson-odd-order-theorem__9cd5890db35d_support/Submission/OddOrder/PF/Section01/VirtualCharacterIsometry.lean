import Submission.OddOrder.PF.Section01.VirtualCharacterNormTwo

/-!
The integral-lattice core of Peterfalvi 1.4.

The original argument only uses that norm-two, augmentation-zero virtual
characters are signed differences of two irreducibles and that the character
isometry preserves their pairings.  This file isolates that combinatorics from
the still-developing class-function support API.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Finsupp

/-- The coefficient pairing of two oriented basis differences. -/
theorem coeffDot_single_sub_single {ι : Type*} [DecidableEq ι]
    (a b c d : ι) :
    coeffDot (single a 1 - single b 1 : IntegralLattice ι)
        (single c 1 - single d 1) =
      (if a = c then 1 else 0) - (if a = d then 1 else 0) -
        (if b = c then 1 else 0) + (if b = d then 1 else 0) := by
  calc
    coeffDot (single a 1 - single b 1 : IntegralLattice ι)
        (single c 1 - single d 1) =
        coeffDot (single a 1) (single c 1) -
          coeffDot (single a 1) (single d 1) -
          coeffDot (single b 1) (single c 1) +
          coeffDot (single b 1) (single d 1) := by
      rw [sub_eq_add_neg, sub_eq_add_neg, coeffDot_add_left,
        coeffDot_add_right, coeffDot_add_right, coeffDot_neg_right,
        coeffDot_neg_left, coeffDot_neg_left, coeffDot_neg_right]
      ring
    _ = _ := by simp [single_apply]

/-- Peterfalvi's four-character comparison (`vchar_isometry_base4`).  If one
oriented basis difference has the same signed pairing with two differences
having a common negative endpoint, then it has that endpoint too (with the
orientation dictated by the sign). -/
theorem vchar_isometry_base4 {ι : Type*} [DecidableEq ι]
    (ε : ℤ) (i j k n m : ι) (hε : IsSign ε) (hjk : j ≠ k)
    (hji : j ≠ i) (hki : k ≠ i)
    (h₁ : coeffDot (single n 1 - single m 1 : IntegralLattice ι)
      (single j 1 - single i 1) = ε)
    (h₂ : coeffDot (single n 1 - single m 1 : IntegralLattice ι)
      (single k 1 - single i 1) = ε) :
    (ε = 1 → m = i) ∧ (ε = -1 → n = i) := by
  rcases hε with rfl | rfl
  · constructor
    · intro _
      by_contra hmi
      by_cases hnj : n = j <;> by_cases hnk : n = k <;>
        by_cases hni : n = i <;> by_cases hmj : m = j <;>
        by_cases hmk : m = k <;>
        simp_all [coeffDot_single_sub_single]
    · norm_num
  · constructor
    · norm_num
    · intro _
      by_contra hni
      by_cases hnj : n = j <;> by_cases hnk : n = k <;>
        by_cases hmj : m = j <;> by_cases hmk : m = k <;>
        by_cases hmi : m = i <;>
        simp_all [coeffDot_single_sub_single]

private theorem common_endpoint_of_coeffDot_eq_one {ι : Type*} [DecidableEq ι]
    (a b c d : ι) (hab : a ≠ b) (hcd : c ≠ d)
    (h : coeffDot (single a 1 - single b 1 : IntegralLattice ι)
      (single c 1 - single d 1) = 1) :
    a = c ∨ b = d := by
  by_cases hac : a = c <;> by_cases had : a = d <;>
    by_cases hbc : b = c <;> by_cases hbd : b = d <;>
    simp_all [coeffDot_single_sub_single]

private theorem crossed_endpoint_of_coeffDot_eq_neg_one {ι : Type*}
    [DecidableEq ι] (a b c d : ι) (hab : a ≠ b) (hcd : c ≠ d)
    (h : coeffDot (single a 1 - single b 1 : IntegralLattice ι)
      (single c 1 - single d 1) = -1) :
    a = d ∨ b = c := by
  by_cases hac : a = c <;> by_cases had : a = d <;>
    by_cases hbc : b = c <;> by_cases hbd : b = d <;>
    simp_all [coeffDot_single_sub_single]

/-- Peterfalvi's three-character comparison (`vchar_isometry_base3`).  Two
augmentation-zero norm-two lattice vectors with pairing one are consistently
oriented differences with one common endpoint. -/
theorem vchar_isometry_base3 {ι : Type*} (f f' : IntegralLattice ι)
    (hfnorm : normSq f = 2) (hfsum : coeffSum f = 0)
    (hf'norm : normSq f' = 2) (hf'sum : coeffSum f' = 0)
    (hpair : coeffDot f f' = 1) :
    ∃ i j k ε, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ IsSign ε ∧
      f = ε • (single j 1 - single i 1) ∧
      f' = ε • (single j 1 - single k 1) := by
  classical
  obtain ⟨a, b, ε, hab, hε, rfl⟩ :=
    eq_sign_smul_single_sub_single_of_normSq_eq_two f hfnorm hfsum
  obtain ⟨c, d, δ, hcd, hδ, rfl⟩ :=
    eq_sign_smul_single_sub_single_of_normSq_eq_two f' hf'norm hf'sum
  rw [coeffDot_smul_left, coeffDot_smul_right] at hpair
  rcases hε with rfl | rfl <;> rcases hδ with rfl | rfl
  · simp only [one_mul] at hpair
    rcases common_endpoint_of_coeffDot_eq_one a b c d hab hcd hpair with hac | hbd
    · subst c
      refine ⟨b, a, d, 1, hab.symm, hcd, ?_, Or.inl rfl, ?_, ?_⟩
      · intro hbd
        subst d
        simp [coeffDot_single_sub_single, hab, hab.symm] at hpair
      · simp
      · simp
    · subst d
      refine ⟨a, b, c, -1, hab, hcd.symm, ?_, Or.inr rfl, ?_, ?_⟩
      · intro hac
        subst c
        simp [coeffDot_single_sub_single, hab, hab.symm] at hpair
      · simp
      · simp
  · norm_num only [one_mul, neg_mul, neg_neg] at hpair
    have hpair' : coeffDot (single a 1 - single b 1 : IntegralLattice ι)
        (single c 1 - single d 1) = -1 := by linarith
    rcases crossed_endpoint_of_coeffDot_eq_neg_one a b c d hab hcd hpair' with had | hbc
    · subst d
      refine ⟨b, a, c, 1, hab.symm, hcd.symm, ?_, Or.inl rfl, ?_, ?_⟩
      · intro hbc
        subst c
        simp [coeffDot_single_sub_single, hab, hab.symm] at hpair'
      · simp
      · simp
    · subst c
      refine ⟨a, b, d, -1, hab, hcd, ?_, Or.inr rfl, ?_, ?_⟩
      · intro had
        subst d
        simp [coeffDot_single_sub_single, hab, hab.symm] at hpair'
      · simp
      · simp
  · norm_num only [one_mul, neg_mul, neg_neg] at hpair
    have hpair' : coeffDot (single a 1 - single b 1 : IntegralLattice ι)
        (single c 1 - single d 1) = -1 := by linarith
    rcases crossed_endpoint_of_coeffDot_eq_neg_one a b c d hab hcd hpair' with had | hbc
    · subst d
      refine ⟨b, a, c, -1, hab.symm, hcd.symm, ?_, Or.inr rfl, ?_, ?_⟩
      · intro hbc
        subst c
        simp [coeffDot_single_sub_single, hab, hab.symm] at hpair'
      · simp
      · simp
    · subst c
      refine ⟨a, b, d, 1, hab, hcd, ?_, Or.inl rfl, ?_, ?_⟩
      · intro had
        subst d
        simp [coeffDot_single_sub_single, hab, hab.symm] at hpair'
      · simp
      · simp
  · norm_num only [one_mul, neg_mul, neg_neg] at hpair
    rcases common_endpoint_of_coeffDot_eq_one a b c d hab hcd hpair with hac | hbd
    · subst c
      refine ⟨b, a, d, -1, hab.symm, hcd, ?_, Or.inr rfl, ?_, ?_⟩
      · intro hbd
        subst d
        simp [coeffDot_single_sub_single, hab, hab.symm] at hpair
      · simp
      · simp
    · subst d
      refine ⟨a, b, c, 1, hab, hcd.symm, ?_, Or.inl rfl, ?_, ?_⟩
      · intro hac
        subst c
        simp [coeffDot_single_sub_single, hab, hab.symm] at hpair
      · simp
      · simp

end

end Submission.OddOrder.PF
