import Mathlib

namespace Submission

theorem sturm_separation (p q y₁ y₂ : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (J : Set ℝ) (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
    (hJ_sub : Set.Icc a b ⊆ J)
    (hp : ContinuousOn p J) (_hq : ContinuousOn q J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
    (hza : y₁ a = 0) (hzb : y₁ b = 0)
    (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0) :
    ∃! c, c ∈ Set.Ioo a b ∧ y₂ c = 0 := by
  let W : ℝ → ℝ := fun x ↦ y₁ x * deriv y₂ x - y₂ x * deriv y₁ x
  have hWderiv : ∀ x ∈ J, HasDerivAt W (-p x * W x) x := by
    intro x hx
    change HasDerivAt
      (fun z ↦ y₁ z * deriv y₂ z - y₂ z * deriv y₁ z)
      (-p x * (y₁ x * deriv y₂ x - y₂ x * deriv y₁ x)) x
    convert ((hy₁ x hx).mul (hy₂' x hx)).sub ((hy₂ x hx).mul (hy₁' x hx)) using 1
    all_goals try rfl
    ring
  obtain ⟨x₀, hx₀, hW₀⟩ := hW
  have hW₀' : W x₀ ≠ 0 := by
    simpa only [W] using hW₀

  let P : ℝ → ℝ := fun x ↦ ∫ t in x₀..x, p t
  have hPderiv : ∀ x ∈ J, HasDerivAt P (p x) x := by
    intro x hx
    have hseg : Set.uIcc x₀ x ⊆ J :=
      hJ_conn.ordConnected.uIcc_subset hx₀ hx
    have hpx : ContinuousAt p x :=
      hp.continuousAt (hJ_open.mem_nhds hx)
    change HasDerivAt (fun z ↦ ∫ t in x₀..z, p t) (p x) x
    exact intervalIntegral.integral_hasDerivAt_right
      ((hp.mono hseg).intervalIntegrable)
      (ContinuousOn.stronglyMeasurableAtFilter hJ_open hp x hx) hpx

  let F : ℝ → ℝ := fun x ↦ Real.exp (P x) * W x
  have hFderiv : ∀ x ∈ J, HasDerivAt F 0 x := by
    intro x hx
    change HasDerivAt (fun z ↦ Real.exp (P z) * W z) 0 x
    convert
      (((Real.hasDerivAt_exp (P x)).comp x (hPderiv x hx)).mul (hWderiv x hx)) using 1
    all_goals try rfl
    simp only [Function.comp_apply]
    ring
  have hFdiff : DifferentiableOn ℝ F J :=
    fun x hx ↦ (hFderiv x hx).differentiableAt.differentiableWithinAt
  have hFderiv_zero : Set.EqOn (deriv F) 0 J := by
    intro x hx
    simpa only [Pi.zero_apply] using (hFderiv x hx).deriv
  have hFconst (x : ℝ) (hx : x ∈ J) : F x = F x₀ :=
    hJ_open.is_const_of_deriv_eq_zero hJ_conn hFdiff hFderiv_zero hx hx₀
  have hF₀_ne : F x₀ ≠ 0 := by
    dsimp only [F]
    exact mul_ne_zero (Real.exp_ne_zero _) hW₀'
  have hW_ne : ∀ x ∈ J, W x ≠ 0 := by
    intro x hx hzero
    apply hF₀_ne
    rw [← hFconst x hx]
    simp only [F, hzero, mul_zero]

  have haJ : a ∈ J :=
    hJ_sub ⟨le_rfl, hab.le⟩
  have hbJ : b ∈ J :=
    hJ_sub ⟨hab.le, le_rfl⟩

  have h_exists : ∃ c, c ∈ Set.Ioo a b ∧ y₂ c = 0 := by
    by_contra hno
    have hno' : ∀ x, x ∈ Set.Ioo a b → y₂ x ≠ 0 := by
      intro x hx hzero
      exact hno ⟨x, hx, hzero⟩
    have hy₂a : y₂ a ≠ 0 := by
      intro hya
      apply hW_ne a haJ
      simp only [W, hza, hya, zero_mul, sub_self]
    have hy₂b : y₂ b ≠ 0 := by
      intro hyb
      apply hW_ne b hbJ
      simp only [W, hzb, hyb, zero_mul, sub_self]
    have hy₂ne : ∀ x ∈ Set.Icc a b, y₂ x ≠ 0 := by
      intro x hx
      by_cases hxa : x = a
      · simpa only [hxa] using hy₂a
      by_cases hxb : x = b
      · simpa only [hxb] using hy₂b
      exact hno' x ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩

    let R : ℝ → ℝ := fun x ↦ y₁ x / y₂ x
    have hRderiv : ∀ x ∈ Set.Icc a b, HasDerivAt R (-W x / y₂ x ^ 2) x := by
      intro x hx
      change HasDerivAt (fun z ↦ y₁ z / y₂ z)
        (-(y₁ x * deriv y₂ x - y₂ x * deriv y₁ x) / y₂ x ^ 2) x
      convert (hy₁ x (hJ_sub hx)).div (hy₂ x (hJ_sub hx)) (hy₂ne x hx) using 1
      all_goals try rfl
      ring
    have hRcont : ContinuousOn R (Set.Icc a b) :=
      HasDerivAt.continuousOn hRderiv
    have hRend : R a = R b := by
      simp only [R, hza, hzb, zero_div]
    obtain ⟨c, hc, hc0⟩ :=
      exists_hasDerivAt_eq_zero hab hRcont hRend
        (fun x hx ↦ hRderiv x (Set.Ioo_subset_Icc_self hx))
    have hratio_ne : -W c / y₂ c ^ 2 ≠ 0 :=
      div_ne_zero (neg_ne_zero.mpr (hW_ne c (hJ_sub (Set.Ioo_subset_Icc_self hc))))
        (pow_ne_zero 2 (hy₂ne c (Set.Ioo_subset_Icc_self hc)))
    exact hratio_ne hc0

  have h_no_two :
      ∀ ⦃u v : ℝ⦄, u ∈ Set.Ioo a b → v ∈ Set.Ioo a b → u < v →
        y₂ u = 0 → y₂ v = 0 → False := by
    intro u v hu hv huv hu0 hv0
    have hseg : Set.Icc u v ⊆ Set.Ioo a b := by
      intro x hx
      exact ⟨hu.1.trans_le hx.1, hx.2.trans_lt hv.2⟩
    have hy₁ne : ∀ x ∈ Set.Icc u v, y₁ x ≠ 0 :=
      fun x hx ↦ hne x (hseg hx)
    let R : ℝ → ℝ := fun x ↦ y₂ x / y₁ x
    have hRderiv : ∀ x ∈ Set.Icc u v, HasDerivAt R (W x / y₁ x ^ 2) x := by
      intro x hx
      have hxJ := hJ_sub (Set.Ioo_subset_Icc_self (hseg hx))
      change HasDerivAt (fun z ↦ y₂ z / y₁ z)
        ((y₁ x * deriv y₂ x - y₂ x * deriv y₁ x) / y₁ x ^ 2) x
      convert (hy₂ x hxJ).div (hy₁ x hxJ) (hy₁ne x hx) using 1
      all_goals try rfl
      ring
    have hRcont : ContinuousOn R (Set.Icc u v) :=
      HasDerivAt.continuousOn hRderiv
    have hRend : R u = R v := by
      simp only [R, hu0, hv0, zero_div]
    obtain ⟨c, hc, hc0⟩ :=
      exists_hasDerivAt_eq_zero huv hRcont hRend
        (fun x hx ↦ hRderiv x (Set.Ioo_subset_Icc_self hx))
    have hcab : c ∈ Set.Ioo a b :=
      hseg (Set.Ioo_subset_Icc_self hc)
    have hratio_ne : W c / y₁ c ^ 2 ≠ 0 :=
      div_ne_zero (hW_ne c (hJ_sub (Set.Ioo_subset_Icc_self hcab)))
        (pow_ne_zero 2 (hne c hcab))
    exact hratio_ne hc0

  obtain ⟨c, hc, hc0⟩ := h_exists
  refine ⟨c, ⟨hc, hc0⟩, ?_⟩
  intro d hd
  by_contra hdc
  rcases lt_or_gt_of_ne hdc with hlt | hgt
  · exact (h_no_two hd.1 hc hlt hd.2 hc0).elim
  · exact (h_no_two hc hd.1 hgt hc0 hd.2).elim

end Submission
