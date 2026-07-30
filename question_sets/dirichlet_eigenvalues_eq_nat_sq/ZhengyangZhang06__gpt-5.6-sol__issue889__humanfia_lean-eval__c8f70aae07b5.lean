import Mathlib
import Submission.Helpers

open scoped Real

namespace Submission

open Set

theorem dirichlet_eigenvalues_eq_nat_sq (lam : ℝ) :
    (∃ (y : ℝ → ℝ) (J : Set ℝ),
        IsOpen J ∧ Set.Icc (0 : ℝ) Real.pi ⊆ J ∧
        (∀ x ∈ J, HasDerivAt y (deriv y x) x) ∧
        (∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x) ∧
        y 0 = 0 ∧ y Real.pi = 0 ∧
        ∃ x ∈ Set.Ioo (0 : ℝ) Real.pi, y x ≠ 0) ↔
      ∃ n : ℕ, 0 < n ∧ lam = (n : ℝ) ^ 2 := by
  constructor
  · rintro ⟨y, J, _, hJ, hy, hy', hy0, hypi, x, hx, hyx⟩
    have hyI : ∀ t ∈ Icc (0 : ℝ) Real.pi, HasDerivAt y (deriv y t) t :=
      fun t ht ↦ hy t (hJ ht)
    have hy'I : ∀ t ∈ Icc (0 : ℝ) Real.pi,
        HasDerivAt (deriv y) (-(lam * y t)) t :=
      fun t ht ↦ hy' t (hJ ht)
    have hxI : x ∈ Icc (0 : ℝ) Real.pi := ⟨hx.1.le, hx.2.le⟩
    have hpiI : Real.pi ∈ Icc (0 : ℝ) Real.pi := ⟨Real.pi_pos.le, le_rfl⟩
    rcases lt_trichotomy lam 0 with hlam | hlam | hlam
    · exfalso
      set a : ℝ := Real.sqrt (-lam) with ha
      have ha_pos : 0 < a := by
        rw [ha, Real.sqrt_pos]
        linarith
      have ha_sq : a ^ 2 = -lam := by
        rw [ha, Real.sq_sqrt]
        linarith
      have hlam_sq : lam = -(a ^ 2) := by linarith [ha_sq]
      have hscale_deriv : ∀ t : ℝ, HasDerivAt (fun u : ℝ ↦ a * u) a t := by
        intro t
        simpa using (hasDerivAt_id t).const_mul a
      have hsinh_deriv : ∀ t : ℝ, HasDerivAt (fun u ↦ Real.sinh (a * u))
          (a * Real.cosh (a * t)) t := by
        intro t
        simpa [Function.comp_def, mul_comm] using
          (Real.hasDerivAt_sinh (a * t)).comp t (hscale_deriv t)
      have hcosh_deriv : ∀ t : ℝ, HasDerivAt (fun u ↦ Real.cosh (a * u))
          (a * Real.sinh (a * t)) t := by
        intro t
        simpa [Function.comp_def, mul_comm] using
          (Real.hasDerivAt_cosh (a * t)).comp t (hscale_deriv t)
      have hg_deriv : ∀ t ∈ Icc (0 : ℝ) Real.pi,
          HasDerivAt
            (fun u ↦ deriv y u * Real.cosh (a * u) -
              a * (y u * Real.sinh (a * u))) 0 t := by
        intro t ht
        have hraw : HasDerivAt
            (fun u ↦ deriv y u * Real.cosh (a * u) -
              a * (y u * Real.sinh (a * u)))
            (-(lam * y t) * Real.cosh (a * t) +
              deriv y t * (a * Real.sinh (a * t)) -
              a * (deriv y t * Real.sinh (a * t) +
                y t * (a * Real.cosh (a * t)))) t := by
          exact ((hy'I t ht).fun_mul (hcosh_deriv t)).fun_sub
            (((hyI t ht).fun_mul (hsinh_deriv t)).const_mul a)
        apply hraw.congr_deriv
        rw [hlam_sq]
        ring
      have hh_deriv : ∀ t ∈ Icc (0 : ℝ) Real.pi,
          HasDerivAt
            (fun u ↦ deriv y u * Real.sinh (a * u) -
              a * (y u * Real.cosh (a * u))) 0 t := by
        intro t ht
        have hraw : HasDerivAt
            (fun u ↦ deriv y u * Real.sinh (a * u) -
              a * (y u * Real.cosh (a * u)))
            (-(lam * y t) * Real.sinh (a * t) +
              deriv y t * (a * Real.cosh (a * t)) -
              a * (deriv y t * Real.cosh (a * t) +
                y t * (a * Real.sinh (a * t)))) t := by
          exact ((hy'I t ht).fun_mul (hsinh_deriv t)).fun_sub
            (((hyI t ht).fun_mul (hcosh_deriv t)).const_mul a)
        apply hraw.congr_deriv
        rw [hlam_sq]
        ring
      have hg_const := Helpers.eq_left_of_hasDerivAt_zero hg_deriv
      have hh_const := Helpers.eq_left_of_hasDerivAt_zero hh_deriv
      have hg_eq : ∀ t ∈ Icc (0 : ℝ) Real.pi,
          deriv y t * Real.cosh (a * t) - a * (y t * Real.sinh (a * t)) = deriv y 0 := by
        intro t ht
        simpa [hy0] using hg_const t ht
      have hh_eq : ∀ t ∈ Icc (0 : ℝ) Real.pi,
          deriv y t * Real.sinh (a * t) - a * (y t * Real.cosh (a * t)) = 0 := by
        intro t ht
        simpa [hy0] using hh_const t ht
      have hy_formula : ∀ t ∈ Icc (0 : ℝ) Real.pi,
          a * y t = deriv y 0 * Real.sinh (a * t) := by
        intro t ht
        calc
          a * y t = a * y t *
              (Real.cosh (a * t) ^ 2 - Real.sinh (a * t) ^ 2) := by
                rw [Real.cosh_sq_sub_sinh_sq, mul_one]
          _ = (deriv y t * Real.cosh (a * t) - a * (y t * Real.sinh (a * t))) *
                Real.sinh (a * t) -
              (deriv y t * Real.sinh (a * t) - a * (y t * Real.cosh (a * t))) *
                Real.cosh (a * t) := by ring
          _ = deriv y 0 * Real.sinh (a * t) := by rw [hg_eq t ht, hh_eq t ht]; ring
      have hsinh_ne : Real.sinh (a * Real.pi) ≠ 0 :=
        Real.sinh_ne_zero.mpr (mul_ne_zero ha_pos.ne' Real.pi_ne_zero)
      have hmul : deriv y 0 * Real.sinh (a * Real.pi) = 0 := by
        calc
          deriv y 0 * Real.sinh (a * Real.pi) = a * y Real.pi :=
            (hy_formula Real.pi hpiI).symm
          _ = 0 := by rw [hypi, mul_zero]
      have hdy0 : deriv y 0 = 0 := (mul_eq_zero.mp hmul).resolve_right hsinh_ne
      have hayx : a * y x = 0 := by simpa [hdy0] using hy_formula x hxI
      exact hyx ((mul_eq_zero.mp hayx).resolve_left ha_pos.ne')
    · subst lam
      exfalso
      have hd_deriv : ∀ t ∈ Icc (0 : ℝ) Real.pi, HasDerivAt (deriv y) 0 t := by
        intro t ht
        simpa using hy'I t ht
      have hd_const := Helpers.eq_left_of_hasDerivAt_zero hd_deriv
      have hline_deriv : ∀ t ∈ Icc (0 : ℝ) Real.pi,
          HasDerivAt (fun u ↦ y u - deriv y 0 * u) 0 t := by
        intro t ht
        have hlinear : HasDerivAt (fun u : ℝ ↦ deriv y 0 * u) (deriv y 0) t := by
          simpa using (hasDerivAt_id t).const_mul (deriv y 0)
        have hraw : HasDerivAt (fun u ↦ y u - deriv y 0 * u)
            (deriv y t - deriv y 0) t := by
          exact (hyI t ht).fun_sub hlinear
        exact hraw.congr_deriv (sub_eq_zero.mpr (hd_const t ht))
      have hline_const := Helpers.eq_left_of_hasDerivAt_zero hline_deriv
      have hline_pi := hline_const Real.pi hpiI
      have hmul : deriv y 0 * Real.pi = 0 := by
        rw [hypi, hy0] at hline_pi
        linarith
      have hdy0 : deriv y 0 = 0 :=
        (mul_eq_zero.mp hmul).resolve_right Real.pi_ne_zero
      have hyx0 : y x = 0 := by simpa [hdy0, hy0] using hline_const x hxI
      exact hyx hyx0
    · set a : ℝ := Real.sqrt lam with ha
      have ha_pos : 0 < a := by rw [ha, Real.sqrt_pos]; exact hlam
      have ha_sq : a ^ 2 = lam := by rw [ha, Real.sq_sqrt hlam.le]
      have hscale_deriv : ∀ t : ℝ, HasDerivAt (fun u : ℝ ↦ a * u) a t := by
        intro t
        simpa using (hasDerivAt_id t).const_mul a
      have hsin_deriv : ∀ t : ℝ, HasDerivAt (fun u ↦ Real.sin (a * u))
          (a * Real.cos (a * t)) t := by
        intro t
        simpa [Function.comp_def, mul_comm] using
          (Real.hasDerivAt_sin (a * t)).comp t (hscale_deriv t)
      have hcos_deriv : ∀ t : ℝ, HasDerivAt (fun u ↦ Real.cos (a * u))
          (-(a * Real.sin (a * t))) t := by
        intro t
        have hraw := (Real.hasDerivAt_cos (a * t)).comp t (hscale_deriv t)
        have hvalue : -Real.sin (a * t) * a = -(a * Real.sin (a * t)) := by ring
        simpa [Function.comp_def] using hraw.congr_deriv hvalue
      have hg_deriv : ∀ t ∈ Icc (0 : ℝ) Real.pi,
          HasDerivAt
            (fun u ↦ deriv y u * Real.cos (a * u) +
              a * (y u * Real.sin (a * u))) 0 t := by
        intro t ht
        have hraw : HasDerivAt
            (fun u ↦ deriv y u * Real.cos (a * u) +
              a * (y u * Real.sin (a * u)))
            (-(lam * y t) * Real.cos (a * t) +
              deriv y t * (-(a * Real.sin (a * t))) +
              a * (deriv y t * Real.sin (a * t) +
                y t * (a * Real.cos (a * t)))) t := by
          exact ((hy'I t ht).fun_mul (hcos_deriv t)).fun_add
            (((hyI t ht).fun_mul (hsin_deriv t)).const_mul a)
        apply hraw.congr_deriv
        rw [← ha_sq]
        ring
      have hh_deriv : ∀ t ∈ Icc (0 : ℝ) Real.pi,
          HasDerivAt
            (fun u ↦ deriv y u * Real.sin (a * u) -
              a * (y u * Real.cos (a * u))) 0 t := by
        intro t ht
        have hraw : HasDerivAt
            (fun u ↦ deriv y u * Real.sin (a * u) -
              a * (y u * Real.cos (a * u)))
            (-(lam * y t) * Real.sin (a * t) +
              deriv y t * (a * Real.cos (a * t)) -
              a * (deriv y t * Real.cos (a * t) +
                y t * (-(a * Real.sin (a * t))))) t := by
          exact ((hy'I t ht).fun_mul (hsin_deriv t)).fun_sub
            (((hyI t ht).fun_mul (hcos_deriv t)).const_mul a)
        apply hraw.congr_deriv
        rw [← ha_sq]
        ring
      have hg_const := Helpers.eq_left_of_hasDerivAt_zero hg_deriv
      have hh_const := Helpers.eq_left_of_hasDerivAt_zero hh_deriv
      have hg_eq : ∀ t ∈ Icc (0 : ℝ) Real.pi,
          deriv y t * Real.cos (a * t) + a * (y t * Real.sin (a * t)) = deriv y 0 := by
        intro t ht
        simpa [hy0] using hg_const t ht
      have hh_eq : ∀ t ∈ Icc (0 : ℝ) Real.pi,
          deriv y t * Real.sin (a * t) - a * (y t * Real.cos (a * t)) = 0 := by
        intro t ht
        simpa [hy0] using hh_const t ht
      have hy_formula : ∀ t ∈ Icc (0 : ℝ) Real.pi,
          a * y t = deriv y 0 * Real.sin (a * t) := by
        intro t ht
        calc
          a * y t = a * y t *
              (Real.sin (a * t) ^ 2 + Real.cos (a * t) ^ 2) := by
                rw [Real.sin_sq_add_cos_sq, mul_one]
          _ = (deriv y t * Real.cos (a * t) + a * (y t * Real.sin (a * t))) *
                Real.sin (a * t) -
              (deriv y t * Real.sin (a * t) - a * (y t * Real.cos (a * t))) *
                Real.cos (a * t) := by ring
          _ = deriv y 0 * Real.sin (a * t) := by rw [hg_eq t ht, hh_eq t ht]; ring
      have hdy_ne : deriv y 0 ≠ 0 := by
        intro hdy0
        have hayx : a * y x = 0 := by simpa [hdy0] using hy_formula x hxI
        exact hyx ((mul_eq_zero.mp hayx).resolve_left ha_pos.ne')
      have hmul : deriv y 0 * Real.sin (a * Real.pi) = 0 := by
        calc
          deriv y 0 * Real.sin (a * Real.pi) = a * y Real.pi :=
            (hy_formula Real.pi hpiI).symm
          _ = 0 := by rw [hypi, mul_zero]
      have hsin : Real.sin (a * Real.pi) = 0 :=
        (mul_eq_zero.mp hmul).resolve_left hdy_ne
      obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hsin
      have hka : (k : ℝ) = a := mul_right_cancel₀ Real.pi_ne_zero hk
      have hk_pos_real : 0 < (k : ℝ) := by rw [hka]; exact ha_pos
      have hk_pos : 0 < k := by exact_mod_cast hk_pos_real
      have hk_toNat : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk_pos.le
      have hk_cast : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast hk_toNat
      refine ⟨k.toNat, by omega, ?_⟩
      calc
        lam = a ^ 2 := ha_sq.symm
        _ = (k : ℝ) ^ 2 := by rw [hka]
        _ = ((k.toNat : ℕ) : ℝ) ^ 2 := by rw [hk_cast]
  · rintro ⟨n, hn, rfl⟩
    let y : ℝ → ℝ := fun x ↦ Real.sin ((n : ℝ) * x)
    have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn
    have hinner : ∀ x : ℝ, HasDerivAt (fun t : ℝ ↦ (n : ℝ) * t) (n : ℝ) x := by
      intro x
      simpa using (hasDerivAt_id x).const_mul (n : ℝ)
    have hy_deriv : ∀ x : ℝ,
        HasDerivAt y ((n : ℝ) * Real.cos ((n : ℝ) * x)) x := by
      intro x
      simpa [y, Function.comp_def, mul_comm] using
        (Real.hasDerivAt_sin ((n : ℝ) * x)).comp x (hinner x)
    have deriv_y : deriv y = fun x ↦ (n : ℝ) * Real.cos ((n : ℝ) * x) := by
      funext x
      exact (hy_deriv x).deriv
    refine ⟨y, Set.univ, isOpen_univ, subset_univ _, ?_, ?_, ?_, ?_, ?_⟩
    · intro x _
      exact (hy_deriv x).differentiableAt.hasDerivAt
    · intro x _
      have hcos : HasDerivAt (fun t ↦ Real.cos ((n : ℝ) * t))
          (-((n : ℝ) * Real.sin ((n : ℝ) * x))) x := by
        have hraw := (Real.hasDerivAt_cos ((n : ℝ) * x)).comp x (hinner x)
        have hvalue : -Real.sin ((n : ℝ) * x) * (n : ℝ) =
            -((n : ℝ) * Real.sin ((n : ℝ) * x)) := by ring
        simpa [Function.comp_def] using hraw.congr_deriv hvalue
      have hsecond : HasDerivAt
          (fun t ↦ (n : ℝ) * Real.cos ((n : ℝ) * t))
          (-(((n : ℝ) ^ 2) * Real.sin ((n : ℝ) * x))) x := by
        apply (hcos.const_mul (n : ℝ)).congr_deriv
        ring
      rw [deriv_y]
      simpa [y] using hsecond
    · simp [y]
    · simp [y, Real.sin_nat_mul_pi]
    · refine ⟨Real.pi / (2 * (n : ℝ)), ?_, ?_⟩
      · have hden_pos : 0 < 2 * (n : ℝ) := by positivity
        have hn_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have hden_one : 1 < 2 * (n : ℝ) := by nlinarith
        constructor
        · exact div_pos Real.pi_pos hden_pos
        · rw [div_lt_iff₀ hden_pos]
          have hmul_pos : 0 < Real.pi * (2 * (n : ℝ) - 1) :=
            mul_pos Real.pi_pos (sub_pos.mpr hden_one)
          nlinarith
      · have hn_ne : (n : ℝ) ≠ 0 := hn_real.ne'
        have harg : (n : ℝ) * (Real.pi / (2 * (n : ℝ))) = Real.pi / 2 := by
          field_simp [hn_ne]
        simp [y, harg]

end Submission
