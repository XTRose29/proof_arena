import Mathlib
import Submission.CubicQuartic
import Submission.NonsolvableQuintic

open Polynomial

namespace Submission.Helpers

noncomputable section

local notation "S" => solvableByRad ℚ ℂ

private theorem rational_mem (q : ℚ) : (q : ℂ) ∈ S :=
  (solvableByRad ℚ ℂ).algebraMap_mem q

private theorem radical_mem_of_pow_eq {x y : ℂ} {n : ℕ} (hn : n ≠ 0)
    (hxy : x ^ n = y) (hy : y ∈ S) : x ∈ S := by
  apply solvableByRad.rad_mem hn
  rw [hxy]
  exact hy

theorem linear_root_mem {a b x : ℂ} (ha : a ∈ S) (hb : b ∈ S) (ha0 : a ≠ 0)
    (hx : a * x + b = 0) : x ∈ S := by
  have hxeq : x = -b / a := by
    apply (eq_div_iff ha0).2
    linear_combination hx
  rw [hxeq]
  exact div_mem (neg_mem hb) ha

theorem quadratic_root_mem {a b c x : ℂ} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (ha0 : a ≠ 0) (hx : a * x ^ 2 + b * x + c = 0) : x ∈ S := by
  have hdisc : discrim a b c ∈ S := by
    rw [discrim]
    exact sub_mem (pow_mem hb 2) (mul_mem (mul_mem (rational_mem 4) ha) hc)
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (discrim a b c) (by norm_num : 0 < 2)
  have hs_mem : s ∈ S := radical_mem_of_pow_eq (by norm_num) hs hdisc
  have hs_sq : discrim a b c = s * s := by
    rw [← hs, pow_two]
  have hroots := (quadratic_eq_zero_iff ha0 hs_sq x).mp (by simpa [pow_two] using hx)
  have hden : 2 * a ∈ S := mul_mem (rational_mem 2) ha
  rcases hroots with hroot | hroot
  · rw [hroot]
    exact div_mem (add_mem (neg_mem hb) hs_mem) hden
  · rw [hroot]
    exact div_mem (sub_mem (neg_mem hb) hs_mem) hden

theorem cubic_root_mem {a b c d x : ℂ} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hd : d ∈ S) (ha0 : a ≠ 0) (hx : a * x ^ 3 + b * x ^ 2 + c * x + d = 0) :
    x ∈ S := by
  let p : ℂ := (3 * a * c - b ^ 2) / (9 * a ^ 2)
  let q : ℂ := (9 * a * b * c - 2 * b ^ 3 - 27 * a ^ 2 * d) / (54 * a ^ 3)
  have hp_mem : p ∈ S := by
    dsimp [p]
    exact div_mem
      (sub_mem (mul_mem (mul_mem (rational_mem 3) ha) hc) (pow_mem hb 2))
      (mul_mem (rational_mem 9) (pow_mem ha 2))
  have hq_mem : q ∈ S := by
    dsimp [q]
    exact div_mem
      (sub_mem
        (sub_mem (mul_mem (mul_mem (mul_mem (rational_mem 9) ha) hb) hc)
          (mul_mem (rational_mem 2) (pow_mem hb 3)))
        (mul_mem (mul_mem (rational_mem 27) (pow_mem ha 2)) hd))
      (mul_mem (rational_mem 54) (pow_mem ha 3))
  obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ 3
  have hω_mem : ω ∈ S :=
    radical_mem_of_pow_eq (by norm_num) hω.pow_eq_one (solvableByRad ℚ ℂ).one_mem
  have hshift : b / (3 * a) ∈ S :=
    div_mem hb (mul_mem (rational_mem 3) ha)
  by_cases hpz : 3 * a * c - b ^ 2 = 0
  · obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (2 * q) (by norm_num : 0 < 3)
    have hs_mem : s ∈ S :=
      radical_mem_of_pow_eq (by norm_num) hs (mul_mem (rational_mem 2) hq_mem)
    have hroots :=
      (Theorems100.cubic_eq_zero_iff_of_p_eq_zero a b c d ha0 hω hpz rfl hs x).mp hx
    rcases hroots with hroot | hroot | hroot
    · rw [hroot]
      exact sub_mem hs_mem hshift
    · rw [hroot]
      exact sub_mem (mul_mem hs_mem hω_mem) hshift
    · rw [hroot]
      exact sub_mem (mul_mem hs_mem (pow_mem hω_mem 2)) hshift
  · have hp0 : p ≠ 0 := by
      dsimp [p]
      exact div_ne_zero hpz (mul_ne_zero (by norm_num) (pow_ne_zero 2 ha0))
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (q ^ 2 + p ^ 3) (by norm_num : 0 < 2)
    have hr_mem : r ∈ S :=
      radical_mem_of_pow_eq (by norm_num) hr (add_mem (pow_mem hq_mem 2) (pow_mem hp_mem 3))
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (q + r) (by norm_num : 0 < 3)
    have hs_mem : s ∈ S :=
      radical_mem_of_pow_eq (by norm_num) hs (add_mem hq_mem hr_mem)
    have hs0 : s ≠ 0 := by
      intro hsz
      have hqr : q + r = 0 := by
        rw [← hs, hsz]
        norm_num
      have hp3 : p ^ 3 = 0 := by
        linear_combination (r - q) * hqr - hr
      exact hp0 ((pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hp3)
    let t : ℂ := p / s
    have ht_mem : t ∈ S := div_mem hp_mem hs_mem
    have ht : t * s = p := by simp [t, hs0]
    have hroots :=
      (Theorems100.cubic_eq_zero_iff a b c d ha0 hω rfl hp0 rfl hr hs ht x).mp hx
    rcases hroots with hroot | hroot | hroot
    · rw [hroot]
      exact sub_mem (sub_mem hs_mem ht_mem) hshift
    · rw [hroot]
      exact sub_mem
        (sub_mem (mul_mem hs_mem hω_mem) (mul_mem ht_mem (pow_mem hω_mem 2))) hshift
    · rw [hroot]
      exact sub_mem
        (sub_mem (mul_mem hs_mem (pow_mem hω_mem 2)) (mul_mem ht_mem hω_mem)) hshift

theorem quartic_root_mem {a b c d e x : ℂ} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hd : d ∈ S) (he : e ∈ S) (ha0 : a ≠ 0)
    (hx : a * x ^ 4 + b * x ^ 3 + c * x ^ 2 + d * x + e = 0) : x ∈ S := by
  let p : ℂ := (8 * a * c - 3 * b ^ 2) / (8 * a ^ 2)
  let q : ℂ := (b ^ 3 - 4 * a * b * c + 8 * a ^ 2 * d) / (8 * a ^ 3)
  let r : ℂ :=
    (16 * a * b ^ 2 * c + 256 * a ^ 3 * e - 3 * b ^ 4 - 64 * a ^ 2 * b * d) /
      (256 * a ^ 4)
  have hp_mem : p ∈ S := by
    dsimp [p]
    exact div_mem
      (sub_mem (mul_mem (mul_mem (rational_mem 8) ha) hc)
        (mul_mem (rational_mem 3) (pow_mem hb 2)))
      (mul_mem (rational_mem 8) (pow_mem ha 2))
  have hq_mem : q ∈ S := by
    dsimp [q]
    exact div_mem
      (add_mem
        (sub_mem (pow_mem hb 3)
          (mul_mem (mul_mem (mul_mem (rational_mem 4) ha) hb) hc))
        (mul_mem (mul_mem (rational_mem 8) (pow_mem ha 2)) hd))
      (mul_mem (rational_mem 8) (pow_mem ha 3))
  have hr_mem : r ∈ S := by
    dsimp [r]
    exact div_mem
      (sub_mem
        (sub_mem
          (add_mem
            (mul_mem (mul_mem (mul_mem (rational_mem 16) ha) (pow_mem hb 2)) hc)
            (mul_mem (mul_mem (rational_mem 256) (pow_mem ha 3)) he))
          (mul_mem (rational_mem 3) (pow_mem hb 4)))
        (mul_mem (mul_mem (mul_mem (rational_mem 64) (pow_mem ha 2)) hb) hd))
      (mul_mem (rational_mem 256) (pow_mem ha 4))
  have hshift : b / (4 * a) ∈ S :=
    div_mem hb (mul_mem (rational_mem 4) ha)
  by_cases hqz : b ^ 3 - 4 * a * b * c + 8 * a ^ 2 * d = 0
  · obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (p ^ 2 - 4 * r) (by norm_num : 0 < 2)
    have ht_mem : t ∈ S :=
      radical_mem_of_pow_eq (by norm_num) ht
        (sub_mem (pow_mem hp_mem 2) (mul_mem (rational_mem 4) hr_mem))
    obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq ((-p + t) / 2) (by norm_num : 0 < 2)
    have hv_mem : v ∈ S :=
      radical_mem_of_pow_eq (by norm_num) hv
        (div_mem (add_mem (neg_mem hp_mem) ht_mem) (rational_mem 2))
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq ((-p - t) / 2) (by norm_num : 0 < 2)
    have hw_mem : w ∈ S :=
      radical_mem_of_pow_eq (by norm_num) hw
        (div_mem (sub_mem (neg_mem hp_mem) ht_mem) (rational_mem 2))
    have hroots :=
      (Theorems100.quartic_eq_zero_iff_of_q_eq_zero a b c d e ha0 rfl hqz rfl ht hv hw x).mp hx
    rcases hroots with hroot | hroot | hroot | hroot
    · rw [hroot]
      exact sub_mem hv_mem hshift
    · rw [hroot]
      exact sub_mem (neg_mem hv_mem) hshift
    · rw [hroot]
      exact sub_mem hw_mem hshift
    · rw [hroot]
      exact sub_mem (neg_mem hw_mem) hshift
  · have hq0 : q ≠ 0 := by
      dsimp [q]
      exact div_ne_zero hqz (mul_ne_zero (by norm_num) (pow_ne_zero 3 ha0))
    let f : ℂ[X] :=
      X ^ 3 - C p * X ^ 2 - C (4 * r) * X + C (4 * p * r - q ^ 2)
    have hfdeg : f.degree = 3 := by
      dsimp [f]
      compute_degree!
    obtain ⟨u, hu'⟩ := IsAlgClosed.exists_root f (by rw [hfdeg]; norm_num)
    have hu : u ^ 3 - p * u ^ 2 - 4 * r * u + 4 * p * r - q ^ 2 = 0 := by
      simp only [f, IsRoot.def, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at hu'
      linear_combination hu'
    have hu_mem : u ∈ S := by
      apply cubic_root_mem
        (solvableByRad ℚ ℂ).one_mem
        (neg_mem hp_mem)
        (neg_mem (mul_mem (rational_mem 4) hr_mem))
        (sub_mem (mul_mem (mul_mem (rational_mem 4) hp_mem) hr_mem) (pow_mem hq_mem 2))
        one_ne_zero
      linear_combination hu
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (u - p) (by norm_num : 0 < 2)
    have hs_mem : s ∈ S :=
      radical_mem_of_pow_eq (by norm_num) hs (sub_mem hu_mem hp_mem)
    have hs0 : s ≠ 0 := by
      intro hsz
      have hup : u - p = 0 := by
        rw [← hs, hsz]
        norm_num
      have hq2 : q ^ 2 = 0 := by
        linear_combination (u ^ 2 - 4 * r) * hup - hu
      exact hq0 ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hq2)
    obtain ⟨v, hv⟩ :=
      IsAlgClosed.exists_pow_nat_eq (4 * s ^ 2 - 8 * (u - q / s)) (by norm_num : 0 < 2)
    have hv_mem : v ∈ S :=
      radical_mem_of_pow_eq (by norm_num) hv <| sub_mem
        (mul_mem (rational_mem 4) (pow_mem hs_mem 2))
        (mul_mem (rational_mem 8) (sub_mem hu_mem (div_mem hq_mem hs_mem)))
    obtain ⟨w, hw⟩ :=
      IsAlgClosed.exists_pow_nat_eq (4 * s ^ 2 - 8 * (u + q / s)) (by norm_num : 0 < 2)
    have hw_mem : w ∈ S :=
      radical_mem_of_pow_eq (by norm_num) hw <| sub_mem
        (mul_mem (rational_mem 4) (pow_mem hs_mem 2))
        (mul_mem (rational_mem 8) (add_mem hu_mem (div_mem hq_mem hs_mem)))
    have hroots :=
      (Theorems100.quartic_eq_zero_iff a b c d e ha0 rfl rfl hq0 rfl hu hs hv hw x).mp hx
    have hfour : (4 : ℂ) ∈ S := rational_mem 4
    rcases hroots with hroot | hroot | hroot | hroot
    · rw [hroot]
      exact sub_mem
        (div_mem (sub_mem (mul_mem (neg_mem (rational_mem 2)) hs_mem) hv_mem) hfour) hshift
    · rw [hroot]
      exact sub_mem
        (div_mem (add_mem (mul_mem (neg_mem (rational_mem 2)) hs_mem) hv_mem) hfour) hshift
    · rw [hroot]
      exact sub_mem
        (div_mem (sub_mem (mul_mem (rational_mem 2) hs_mem) hw_mem) hfour) hshift
    · rw [hroot]
      exact sub_mem
        (div_mem (add_mem (mul_mem (rational_mem 2) hs_mem) hw_mem) hfour) hshift

end

end Submission.Helpers
