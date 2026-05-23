import Mathlib
import Submission.Helpers

open scoped Real

namespace Submission

theorem dirichlet_eigenvalues_eq_nat_sq (lam : ℝ) :
    (∃ (y : ℝ → ℝ) (J : Set ℝ),
        IsOpen J ∧ Set.Icc (0 : ℝ) Real.pi ⊆ J ∧
        (∀ x ∈ J, HasDerivAt y (deriv y x) x) ∧
        (∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x) ∧
        y 0 = 0 ∧ y Real.pi = 0 ∧
        ∃ x ∈ Set.Ioo (0 : ℝ) Real.pi, y x ≠ 0) ↔
      ∃ n : ℕ, 0 < n ∧ lam = (n : ℝ) ^ 2 := by
  constructor
  · -- Forward direction: nontrivial solution ⟹ lam = n².
    rintro ⟨y, J, hJ_open, hJ_sub, hy_diff, hy_diff2, hy_0, hy_pi, x_nz, hx_nz_in, hx_nz_neq⟩
    -- Pick a nontrivial point.
    obtain ⟨hx_nz_pos, hx_nz_lt⟩ := hx_nz_in
    have hx_nz_in_Icc : x_nz ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hx_nz_pos.le, hx_nz_lt.le⟩
    have hx_nz_in_J : x_nz ∈ J := hJ_sub hx_nz_in_Icc
    have h0_in_J : (0 : ℝ) ∈ J := hJ_sub ⟨le_refl _, Real.pi_pos.le⟩
    have hpi_in_J : Real.pi ∈ J := hJ_sub ⟨Real.pi_pos.le, le_refl _⟩
    -- Case-split on sign of lam.
    rcases lt_trichotomy lam 0 with hlam_neg | hlam_zero | hlam_pos
    · -- Case lam < 0. Show y ≡ 0 on Icc 0 π via Wronskian (using sinh/cosh).
      exfalso
      set k : ℝ := Real.sqrt (-lam) with hk_def
      have hneg_lam_pos : 0 < -lam := neg_pos.mpr hlam_neg
      have hk_pos : 0 < k := Real.sqrt_pos.mpr hneg_lam_pos
      have hk_sq : k ^ 2 = -lam := Real.sq_sqrt hneg_lam_pos.le
      have hk_sq' : k * k = -lam := by rw [← sq]; exact hk_sq
      -- Wronskian-style identities with sinh/cosh.
      let v : ℝ → ℝ := fun x => y x * (k * Real.cosh (k * x)) - deriv y x * Real.sinh (k * x)
      let w : ℝ → ℝ := fun x => y x * (k * Real.sinh (k * x)) - deriv y x * Real.cosh (k * x)
      have h_sinh_deriv : ∀ x : ℝ,
          HasDerivAt (fun z => Real.sinh (k * z)) (k * Real.cosh (k * x)) x := by
        intro x
        have hkx : HasDerivAt (fun z : ℝ => k * z) k x := by
          simpa using (hasDerivAt_id x).const_mul k
        have h := hkx.sinh
        convert h using 1; ring
      have h_cosh_deriv : ∀ x : ℝ,
          HasDerivAt (fun z => Real.cosh (k * z)) (k * Real.sinh (k * x)) x := by
        intro x
        have hkx : HasDerivAt (fun z : ℝ => k * z) k x := by
          simpa using (hasDerivAt_id x).const_mul k
        have h := hkx.cosh
        convert h using 1; ring
      have hv_deriv_zero : ∀ x ∈ J, HasDerivAt v 0 x := by
        intro x hx
        have hy_x := hy_diff x hx
        have hy_x' := hy_diff2 x hx
        have hsinh := h_sinh_deriv x
        have hcosh := h_cosh_deriv x
        have h_term1 : HasDerivAt (fun z => y z * (k * Real.cosh (k * z)))
            (deriv y x * (k * Real.cosh (k * x)) +
              y x * (k * (k * Real.sinh (k * x)))) x := by
          exact hy_x.mul (hcosh.const_mul k)
        have h_term2 : HasDerivAt (fun z => deriv y z * Real.sinh (k * z))
            (-(lam * y x) * Real.sinh (k * x) + deriv y x * (k * Real.cosh (k * x))) x :=
          hy_x'.mul hsinh
        have h_v : HasDerivAt v
            ((deriv y x * (k * Real.cosh (k * x)) + y x * (k * (k * Real.sinh (k * x))))
              - (-(lam * y x) * Real.sinh (k * x) + deriv y x * (k * Real.cosh (k * x)))) x :=
          h_term1.sub h_term2
        convert h_v using 1
        linear_combination (-y x * Real.sinh (k * x)) * hk_sq'
      have hw_deriv_zero : ∀ x ∈ J, HasDerivAt w 0 x := by
        intro x hx
        have hy_x := hy_diff x hx
        have hy_x' := hy_diff2 x hx
        have hsinh := h_sinh_deriv x
        have hcosh := h_cosh_deriv x
        have h_term1 : HasDerivAt (fun z => y z * (k * Real.sinh (k * z)))
            (deriv y x * (k * Real.sinh (k * x)) +
              y x * (k * (k * Real.cosh (k * x)))) x := by
          exact hy_x.mul (hsinh.const_mul k)
        have h_term2 : HasDerivAt (fun z => deriv y z * Real.cosh (k * z))
            (-(lam * y x) * Real.cosh (k * x) + deriv y x * (k * Real.sinh (k * x))) x :=
          hy_x'.mul hcosh
        have h_w : HasDerivAt w
            ((deriv y x * (k * Real.sinh (k * x)) + y x * (k * (k * Real.cosh (k * x))))
              - (-(lam * y x) * Real.cosh (k * x) + deriv y x * (k * Real.sinh (k * x)))) x :=
          h_term1.sub h_term2
        convert h_w using 1
        linear_combination (-y x * Real.cosh (k * x)) * hk_sq'
      -- v, w constant on [0, π].
      have h_Icc_subset_J : Set.Icc (0 : ℝ) Real.pi ⊆ J := hJ_sub
      have h_Icc_convex : Convex ℝ (Set.Icc (0 : ℝ) Real.pi) := convex_Icc _ _
      have h_v_diff : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, DifferentiableAt ℝ v x :=
        fun x hx => (hv_deriv_zero x (h_Icc_subset_J hx)).differentiableAt
      have h_w_diff : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, DifferentiableAt ℝ w x :=
        fun x hx => (hw_deriv_zero x (h_Icc_subset_J hx)).differentiableAt
      have h_v_deriv : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, deriv v x = 0 :=
        fun x hx => (hv_deriv_zero x (h_Icc_subset_J hx)).deriv
      have h_w_deriv : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, deriv w x = 0 :=
        fun x hx => (hw_deriv_zero x (h_Icc_subset_J hx)).deriv
      have h_v_const : ∀ a b, a ∈ Set.Icc (0 : ℝ) Real.pi → b ∈ Set.Icc (0 : ℝ) Real.pi →
          v a = v b := by
        intro a b ha hb
        have h_bound : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, ‖deriv v x‖ ≤ 0 :=
          fun x hx => by rw [h_v_deriv x hx]; simp
        have h := h_Icc_convex.norm_image_sub_le_of_norm_deriv_le h_v_diff h_bound ha hb
        simp at h
        linarith [norm_nonneg (v b - v a), abs_nonneg (v b - v a)]
      have h_w_const : ∀ a b, a ∈ Set.Icc (0 : ℝ) Real.pi → b ∈ Set.Icc (0 : ℝ) Real.pi →
          w a = w b := by
        intro a b ha hb
        have h_bound : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, ‖deriv w x‖ ≤ 0 :=
          fun x hx => by rw [h_w_deriv x hx]; simp
        have h := h_Icc_convex.norm_image_sub_le_of_norm_deriv_le h_w_diff h_bound ha hb
        simp at h
        linarith [norm_nonneg (w b - w a), abs_nonneg (w b - w a)]
      have h0_in_Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) Real.pi := ⟨le_refl _, Real.pi_pos.le⟩
      have hpi_in_Icc : Real.pi ∈ Set.Icc (0 : ℝ) Real.pi := ⟨Real.pi_pos.le, le_refl _⟩
      -- v(0) = 0, v(π) = -y'(π)·sinh(kπ); v constant ⟹ y'(π)·sinh(kπ) = 0; sinh(kπ) > 0 ⟹ y'(π) = 0.
      have h_v_0 : v 0 = 0 := by
        show y 0 * (k * Real.cosh (k * 0)) - deriv y 0 * Real.sinh (k * 0) = 0
        rw [hy_0]; simp
      have h_v_pi : v Real.pi = -(deriv y Real.pi * Real.sinh (k * Real.pi)) := by
        show y Real.pi * (k * Real.cosh (k * Real.pi))
            - deriv y Real.pi * Real.sinh (k * Real.pi)
            = -(deriv y Real.pi * Real.sinh (k * Real.pi))
        rw [hy_pi]; ring
      have h_sinh_kpi_pos : 0 < Real.sinh (k * Real.pi) :=
        Real.sinh_pos_iff.mpr (mul_pos hk_pos Real.pi_pos)
      have h_yp_pi : deriv y Real.pi = 0 := by
        have hr : deriv y Real.pi * Real.sinh (k * Real.pi) = 0 := by
          have := h_v_const 0 Real.pi h0_in_Icc hpi_in_Icc
          rw [h_v_0, h_v_pi] at this; linarith
        rcases mul_eq_zero.mp hr with hh | hh
        · exact hh
        · exact absurd hh h_sinh_kpi_pos.ne'
      -- w(0) = -y'(0); w(π) = 0 (using y(π) = 0 and y'(π) = 0).
      have h_w_0 : w 0 = -(deriv y 0) := by
        show y 0 * (k * Real.sinh (k * 0)) - deriv y 0 * Real.cosh (k * 0) = -(deriv y 0)
        rw [hy_0]; simp
      have h_w_pi : w Real.pi = 0 := by
        show y Real.pi * (k * Real.sinh (k * Real.pi))
            - deriv y Real.pi * Real.cosh (k * Real.pi) = 0
        rw [hy_pi, h_yp_pi]; simp
      have h_yp_0 : deriv y 0 = 0 := by
        have := h_w_const 0 Real.pi h0_in_Icc hpi_in_Icc
        rw [h_w_0, h_w_pi] at this; linarith
      -- Now v(0) = w(0) = 0 (using y'(0) = 0 in w).
      have h_v_xnz : v x_nz = 0 := by
        have := h_v_const 0 x_nz h0_in_Icc hx_nz_in_Icc
        rw [h_v_0] at this; linarith
      have h_w_0' : w 0 = 0 := by rw [h_w_0, h_yp_0]; simp
      have h_w_xnz : w x_nz = 0 := by
        have := h_w_const 0 x_nz h0_in_Icc hx_nz_in_Icc
        rw [h_w_0'] at this; linarith
      -- Algebra: y(x_nz) · k · (cosh² - sinh²) = y(x_nz) · k = 0.
      have h_alg : y x_nz * k = 0 := by
        have h_v_eq : y x_nz * (k * Real.cosh (k * x_nz))
            - deriv y x_nz * Real.sinh (k * x_nz) = 0 := h_v_xnz
        have h_w_eq : y x_nz * (k * Real.sinh (k * x_nz))
            - deriv y x_nz * Real.cosh (k * x_nz) = 0 := h_w_xnz
        have hcosh2_sinh2 := Real.cosh_sq_sub_sinh_sq (k * x_nz)
        linear_combination Real.cosh (k * x_nz) * h_v_eq
            - Real.sinh (k * x_nz) * h_w_eq - (y x_nz * k) * hcosh2_sinh2
      have hy_xnz_zero : y x_nz = 0 := by
        rcases mul_eq_zero.mp h_alg with h | h
        · exact h
        · exact absurd h hk_pos.ne'
      exact hx_nz_neq hy_xnz_zero
    · -- Case lam = 0. y'' = 0 ⟹ y' constant ⟹ y linear; boundary conditions force y = 0.
      exfalso
      -- deriv (deriv y) = 0 on J.
      have h_dd_zero : ∀ x ∈ J, HasDerivAt (deriv y) 0 x := by
        intro x hx
        have := hy_diff2 x hx
        rw [hlam_zero] at this; simpa using this
      -- deriv y is constant on Icc 0 π.
      have h_Icc_subset_J : Set.Icc (0 : ℝ) Real.pi ⊆ J := hJ_sub
      have h_Icc_convex : Convex ℝ (Set.Icc (0 : ℝ) Real.pi) := convex_Icc _ _
      have h_dy_diff : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, DifferentiableAt ℝ (deriv y) x :=
        fun x hx => (h_dd_zero x (h_Icc_subset_J hx)).differentiableAt
      have h_dy_deriv : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, deriv (deriv y) x = 0 :=
        fun x hx => (h_dd_zero x (h_Icc_subset_J hx)).deriv
      have h_dy_const : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, deriv y x = deriv y 0 := by
        intro x hx
        have h_bound : ∀ z ∈ Set.Icc (0 : ℝ) Real.pi, ‖deriv (deriv y) z‖ ≤ 0 :=
          fun z hz => by rw [h_dy_deriv z hz]; simp
        have h0_in_Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) Real.pi := ⟨le_refl _, Real.pi_pos.le⟩
        have h := h_Icc_convex.norm_image_sub_le_of_norm_deriv_le h_dy_diff h_bound h0_in_Icc hx
        simp at h
        linarith [norm_nonneg (deriv y x - deriv y 0), abs_nonneg (deriv y x - deriv y 0)]
      -- z(x) := y(x) - c·x, where c = deriv y 0.
      set c := deriv y 0 with hc_def
      let z : ℝ → ℝ := fun x => y x - c * x
      have hz_deriv : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, HasDerivAt z 0 x := by
        intro x hx
        have hy_x := hy_diff x (h_Icc_subset_J hx)
        have h_cx : HasDerivAt (fun x : ℝ => c * x) c x := by
          simpa using (hasDerivAt_id x).const_mul c
        have h_diff := hy_x.sub h_cx
        -- h_diff : HasDerivAt z (deriv y x - c) x
        have h_eq : deriv y x - c = 0 := by rw [h_dy_const x hx]; ring
        rw [← h_eq]; exact h_diff
      -- z is constant on Icc, z(0) = 0.
      have hz_diff : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, DifferentiableAt ℝ z x :=
        fun x hx => (hz_deriv x hx).differentiableAt
      have hz_deriv_zero : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, deriv z x = 0 :=
        fun x hx => (hz_deriv x hx).deriv
      have hz_const : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, z x = z 0 := by
        intro x hx
        have h_bound : ∀ z' ∈ Set.Icc (0 : ℝ) Real.pi, ‖deriv z z'‖ ≤ 0 :=
          fun z' hz' => by rw [hz_deriv_zero z' hz']; simp
        have h0_in_Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) Real.pi := ⟨le_refl _, Real.pi_pos.le⟩
        have h := h_Icc_convex.norm_image_sub_le_of_norm_deriv_le hz_diff h_bound h0_in_Icc hx
        simp at h
        linarith [norm_nonneg (z x - z 0), abs_nonneg (z x - z 0)]
      -- z(0) = y(0) - c·0 = 0.
      have hz_0 : z 0 = 0 := by show y 0 - c * 0 = 0; rw [hy_0]; ring
      -- y(x) = c·x on Icc.
      have hy_eq : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, y x = c * x := by
        intro x hx
        have hzx : z x = 0 := (hz_const x hx).trans hz_0
        show y x = c * x
        have : y x - c * x = 0 := hzx
        linarith
      -- y(π) = c·π = 0; π ≠ 0 ⟹ c = 0.
      have hpi_in_Icc : Real.pi ∈ Set.Icc (0 : ℝ) Real.pi := ⟨Real.pi_pos.le, le_refl _⟩
      have hc_zero : c = 0 := by
        have h := hy_eq Real.pi hpi_in_Icc
        rw [hy_pi] at h
        have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
        have : c * Real.pi = 0 := h.symm
        rcases mul_eq_zero.mp this with hh | hh
        · exact hh
        · exact absurd hh hpi_ne
      -- y(x_nz) = c · x_nz = 0.
      have : y x_nz = 0 := by
        rw [hy_eq x_nz hx_nz_in_Icc, hc_zero]; ring
      exact hx_nz_neq this
    · -- Case lam > 0. The substantive case: derive lam = n².
      set k : ℝ := Real.sqrt lam with hk_def
      have hk_pos : 0 < k := Real.sqrt_pos.mpr hlam_pos
      have hk_sq : k ^ 2 = lam := Real.sq_sqrt hlam_pos.le
      have hk_sq' : k * k = lam := by rw [← sq]; exact hk_sq
      -- Wronskian-style identities.
      -- v(x) := y(x)·k·cos(k·x) - y'(x)·sin(k·x).
      -- w(x) := -y(x)·k·sin(k·x) - y'(x)·cos(k·x).
      -- v'(x) = w'(x) = 0 on J. So v, w are constant on [0, π].
      let v : ℝ → ℝ := fun x => y x * (k * Real.cos (k * x)) - deriv y x * Real.sin (k * x)
      let w : ℝ → ℝ := fun x => -(y x * (k * Real.sin (k * x))) - deriv y x * Real.cos (k * x)
      -- HasDerivAt for sin(k·) and cos(k·).
      have h_sin_deriv : ∀ x : ℝ,
          HasDerivAt (fun z => Real.sin (k * z)) (k * Real.cos (k * x)) x := by
        intro x
        have hkx : HasDerivAt (fun z : ℝ => k * z) k x := by
          simpa using (hasDerivAt_id x).const_mul k
        have h := hkx.sin
        convert h using 1; ring
      have h_cos_deriv : ∀ x : ℝ,
          HasDerivAt (fun z => Real.cos (k * z)) (-(k * Real.sin (k * x))) x := by
        intro x
        have hkx : HasDerivAt (fun z : ℝ => k * z) k x := by
          simpa using (hasDerivAt_id x).const_mul k
        have h := hkx.cos
        convert h using 1; ring
      -- Compute v' on J.
      have hv_deriv_zero : ∀ x ∈ J, HasDerivAt v 0 x := by
        intro x hx
        have hy_x := hy_diff x hx
        have hy_x' := hy_diff2 x hx
        have hsin := h_sin_deriv x
        have hcos := h_cos_deriv x
        -- v = y * (k * cos(kx)) - (deriv y) * sin(kx)
        -- v' = y' * (k * cos(kx)) + y * (-k² * sin(kx)) - y'' * sin(kx) - y' * k * cos(kx)
        --    = y * (-k² * sin(kx)) - (-(lam * y)) * sin(kx)  (cancellations)
        --    = (-k² * y + lam * y) * sin(kx) = 0
        have h_term1 : HasDerivAt (fun z => y z * (k * Real.cos (k * z)))
            (deriv y x * (k * Real.cos (k * x)) +
              y x * (k * (-(k * Real.sin (k * x))))) x := by
          exact hy_x.mul (hcos.const_mul k)
        have h_term2 : HasDerivAt (fun z => deriv y z * Real.sin (k * z))
            (-(lam * y x) * Real.sin (k * x) + deriv y x * (k * Real.cos (k * x))) x :=
          hy_x'.mul hsin
        have h_v : HasDerivAt v
            ((deriv y x * (k * Real.cos (k * x)) + y x * (k * (-(k * Real.sin (k * x)))))
              - (-(lam * y x) * Real.sin (k * x) + deriv y x * (k * Real.cos (k * x)))) x :=
          h_term1.sub h_term2
        convert h_v using 1
        linear_combination (y x * Real.sin (k * x)) * hk_sq'
      -- Compute w' on J similarly.
      have hw_deriv_zero : ∀ x ∈ J, HasDerivAt w 0 x := by
        intro x hx
        have hy_x := hy_diff x hx
        have hy_x' := hy_diff2 x hx
        have hsin := h_sin_deriv x
        have hcos := h_cos_deriv x
        have h_term1 : HasDerivAt (fun z => y z * (k * Real.sin (k * z)))
            (deriv y x * (k * Real.sin (k * x)) +
              y x * (k * (k * Real.cos (k * x)))) x := by
          exact hy_x.mul (hsin.const_mul k)
        have h_term2 : HasDerivAt (fun z => deriv y z * Real.cos (k * z))
            (-(lam * y x) * Real.cos (k * x) + deriv y x * (-(k * Real.sin (k * x)))) x :=
          hy_x'.mul hcos
        have h_w : HasDerivAt w
            (-(deriv y x * (k * Real.sin (k * x)) +
              y x * (k * (k * Real.cos (k * x)))) -
              (-(lam * y x) * Real.cos (k * x) + deriv y x * (-(k * Real.sin (k * x))))) x := by
          exact h_term1.neg.sub h_term2
        convert h_w using 1
        linear_combination (y x * Real.cos (k * x)) * hk_sq'
      -- v, w constant on [0, π].
      have h_Icc_subset_J : Set.Icc (0 : ℝ) Real.pi ⊆ J := hJ_sub
      have h_Icc_convex : Convex ℝ (Set.Icc (0 : ℝ) Real.pi) := convex_Icc _ _
      have h_v_diff : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, DifferentiableAt ℝ v x :=
        fun x hx => (hv_deriv_zero x (h_Icc_subset_J hx)).differentiableAt
      have h_w_diff : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, DifferentiableAt ℝ w x :=
        fun x hx => (hw_deriv_zero x (h_Icc_subset_J hx)).differentiableAt
      have h_v_deriv : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, deriv v x = 0 :=
        fun x hx => (hv_deriv_zero x (h_Icc_subset_J hx)).deriv
      have h_w_deriv : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, deriv w x = 0 :=
        fun x hx => (hw_deriv_zero x (h_Icc_subset_J hx)).deriv
      have h_v_const : ∀ a b, a ∈ Set.Icc (0 : ℝ) Real.pi → b ∈ Set.Icc (0 : ℝ) Real.pi →
          v a = v b := by
        intro a b ha hb
        have h_bound : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, ‖deriv v x‖ ≤ 0 := by
          intro x hx; rw [h_v_deriv x hx]; simp
        have h := h_Icc_convex.norm_image_sub_le_of_norm_deriv_le h_v_diff h_bound ha hb
        simp at h
        linarith [norm_nonneg (v b - v a), abs_nonneg (v b - v a)]
      have h_w_const : ∀ a b, a ∈ Set.Icc (0 : ℝ) Real.pi → b ∈ Set.Icc (0 : ℝ) Real.pi →
          w a = w b := by
        intro a b ha hb
        have h_bound : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, ‖deriv w x‖ ≤ 0 := by
          intro x hx; rw [h_w_deriv x hx]; simp
        have h := h_Icc_convex.norm_image_sub_le_of_norm_deriv_le h_w_diff h_bound ha hb
        simp at h
        linarith [norm_nonneg (w b - w a), abs_nonneg (w b - w a)]
      -- Evaluate v, w at 0 and π.
      have h0_in_Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) Real.pi := ⟨le_refl _, Real.pi_pos.le⟩
      have hpi_in_Icc : Real.pi ∈ Set.Icc (0 : ℝ) Real.pi := ⟨Real.pi_pos.le, le_refl _⟩
      -- v(0) = y(0)·k·1 - y'(0)·0 = 0.
      have h_v_0 : v 0 = 0 := by
        show y 0 * (k * Real.cos (k * 0)) - deriv y 0 * Real.sin (k * 0) = 0
        rw [hy_0]; simp
      -- v(π) = y(π)·k·cos(k·π) - y'(π)·sin(k·π) = -y'(π)·sin(k·π).
      have h_v_pi : v Real.pi = -(deriv y Real.pi * Real.sin (k * Real.pi)) := by
        show y Real.pi * (k * Real.cos (k * Real.pi))
            - deriv y Real.pi * Real.sin (k * Real.pi)
            = -(deriv y Real.pi * Real.sin (k * Real.pi))
        rw [hy_pi]; ring
      -- From v(0) = v(π): y'(π)·sin(k·π) = 0.
      have h_relation_pi : deriv y Real.pi * Real.sin (k * Real.pi) = 0 := by
        have := h_v_const 0 Real.pi h0_in_Icc hpi_in_Icc
        rw [h_v_0, h_v_pi] at this
        linarith
      -- Case on sin(k·π).
      by_cases h_sin_kpi : Real.sin (k * Real.pi) = 0
      · -- sin(k·π) = 0 ⟹ k·π = m·π for m ∈ ℤ ⟹ k = m. With k > 0, m ≥ 1.
        rw [Real.sin_eq_zero_iff] at h_sin_kpi
        obtain ⟨m, hm_eq⟩ := h_sin_kpi
        have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
        have hk_eq_m : (m : ℝ) = k :=
          mul_right_cancel₀ hpi_ne hm_eq
        have hm_pos : 0 < m := by
          have : (0 : ℝ) < (m : ℝ) := hk_eq_m ▸ hk_pos
          exact_mod_cast this
        refine ⟨m.toNat, ?_, ?_⟩
        · omega
        · have h_cast : (m.toNat : ℝ) = (m : ℝ) := by
            have := Int.toNat_of_nonneg hm_pos.le
            exact_mod_cast this
          rw [h_cast, hk_eq_m, hk_sq]
      · -- sin(k·π) ≠ 0 ⟹ y'(π) = 0 ⟹ y'(0) = 0 (via w) ⟹ y ≡ 0 (Wronskian) ⟹ contradiction.
        exfalso
        have h_yp_pi : deriv y Real.pi = 0 := by
          rcases mul_eq_zero.mp h_relation_pi with h | h
          · exact h
          · exact absurd h h_sin_kpi
        -- w(0) = -(y(0)·k·sin(k·0)) - y'(0)·cos(k·0) = -y'(0).
        have h_w_0 : w 0 = -(deriv y 0) := by
          show -(y 0 * (k * Real.sin (k * 0))) - deriv y 0 * Real.cos (k * 0) = -(deriv y 0)
          rw [hy_0]; simp
        -- w(π) = -(y(π)·k·sin(k·π)) - y'(π)·cos(k·π).
        have h_w_pi : w Real.pi = 0 := by
          show -(y Real.pi * (k * Real.sin (k * Real.pi)))
              - deriv y Real.pi * Real.cos (k * Real.pi) = 0
          rw [hy_pi, h_yp_pi]; simp
        have h_yp_0 : deriv y 0 = 0 := by
          have := h_w_const 0 Real.pi h0_in_Icc hpi_in_Icc
          rw [h_w_0, h_w_pi] at this
          linarith
        -- Now both v(0) = 0 and w(0) = 0 from the original (v_0 already; w_0 needs y'(0) = 0).
        -- v(x_nz) = 0: y(x_nz)·k·cos(k·x_nz) - y'(x_nz)·sin(k·x_nz) = 0.
        have h_v_xnz : v x_nz = 0 := by
          have := h_v_const 0 x_nz h0_in_Icc hx_nz_in_Icc
          rw [h_v_0] at this; linarith
        have h_w_0' : w 0 = 0 := by rw [h_w_0, h_yp_0]; simp
        have h_w_xnz : w x_nz = 0 := by
          have := h_w_const 0 x_nz h0_in_Icc hx_nz_in_Icc
          rw [h_w_0'] at this; linarith
        -- Multiply v(x_nz) by cos and w(x_nz) by -sin, add: y(x_nz)·k = 0.
        have h_alg : y x_nz * k = 0 := by
          have h_v_eq : y x_nz * (k * Real.cos (k * x_nz))
              - deriv y x_nz * Real.sin (k * x_nz) = 0 := h_v_xnz
          have h_w_eq : -(y x_nz * (k * Real.sin (k * x_nz)))
              - deriv y x_nz * Real.cos (k * x_nz) = 0 := h_w_xnz
          -- (h_v_eq) * cos(k·x_nz) + (h_w_eq) * (-sin(k·x_nz)):
          -- = y·k·cos² - y'·sin·cos + y·k·sin² + y'·sin·cos = y·k·(cos² + sin²) = y·k.
          have hsin2_cos2 := Real.sin_sq_add_cos_sq (k * x_nz)
          linear_combination Real.cos (k * x_nz) * h_v_eq
              - Real.sin (k * x_nz) * h_w_eq - (y x_nz * k) * hsin2_cos2
        have hy_xnz_zero : y x_nz = 0 := by
          have : y x_nz * k = 0 := h_alg
          rcases mul_eq_zero.mp this with h | h
          · exact h
          · exact absurd h hk_pos.ne'
        exact hx_nz_neq hy_xnz_zero
  · -- Backward direction: lam = n² (n > 0) ⟹ sin(n·x) is a nontrivial Dirichlet solution.
    rintro ⟨n, hn_pos, hlam⟩
    subst hlam
    refine ⟨fun x => Real.sin ((n : ℝ) * x), Set.univ, isOpen_univ, Set.subset_univ _,
      ?_, ?_, ?_, ?_, ?_⟩
    · intro x _
      have hd : HasDerivAt (fun x : ℝ => Real.sin ((n : ℝ) * x))
          ((n : ℝ) * Real.cos ((n : ℝ) * x)) x := by
        have h1 : HasDerivAt (fun x : ℝ => (n : ℝ) * x) (n : ℝ) x := by
          simpa using (hasDerivAt_id x).const_mul (n : ℝ)
        have := h1.sin
        rw [mul_comm] at this; exact this
      rw [hd.deriv]; exact hd
    · intro x _
      have h_deriv_eq : ∀ z, deriv (fun x : ℝ => Real.sin ((n : ℝ) * x)) z
          = (n : ℝ) * Real.cos ((n : ℝ) * z) := by
        intro z
        have h2 : HasDerivAt (fun x : ℝ => Real.sin ((n : ℝ) * x))
            ((n : ℝ) * Real.cos ((n : ℝ) * z)) z := by
          have hh : HasDerivAt (fun x : ℝ => (n : ℝ) * x) (n : ℝ) z := by
            simpa using (hasDerivAt_id z).const_mul (n : ℝ)
          have := hh.sin
          rw [mul_comm] at this; exact this
        exact h2.deriv
      have h_dd : HasDerivAt (fun z : ℝ => (n : ℝ) * Real.cos ((n : ℝ) * z))
          (-((n : ℝ) ^ 2 * Real.sin ((n : ℝ) * x))) x := by
        have hh : HasDerivAt (fun x : ℝ => (n : ℝ) * x) (n : ℝ) x := by
          simpa using (hasDerivAt_id x).const_mul (n : ℝ)
        have := (hh.cos).const_mul (n : ℝ)
        convert this using 1
        ring
      have h_eq_fn : (fun z : ℝ => (n : ℝ) * Real.cos ((n : ℝ) * z))
          = deriv (fun x : ℝ => Real.sin ((n : ℝ) * x)) := by
        funext z; rw [h_deriv_eq]
      rw [← h_eq_fn]
      convert h_dd using 1
    · simp [Real.sin_zero]
    · show Real.sin ((n : ℝ) * Real.pi) = 0
      have : ((n : ℝ) * Real.pi) = ((n : ℤ) : ℝ) * Real.pi := by push_cast; ring
      rw [this]; exact Real.sin_int_mul_pi n
    · refine ⟨Real.pi / (2 * (n : ℝ)), ⟨?_, ?_⟩, ?_⟩
      · have h2n : (0 : ℝ) < 2 * n := by positivity
        exact div_pos Real.pi_pos h2n
      · have h2n : (0 : ℝ) < 2 * n := by positivity
        rw [div_lt_iff₀ h2n]
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
        nlinarith [Real.pi_pos]
      · show Real.sin ((n : ℝ) * (Real.pi / (2 * (n : ℝ)))) ≠ 0
        have h_eq : (n : ℝ) * (Real.pi / (2 * (n : ℝ))) = Real.pi / 2 := by
          have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hn_pos.ne'
          field_simp
        rw [h_eq, Real.sin_pi_div_two]
        norm_num

end Submission
