import Mathlib
namespace Submission

open scoped Real
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
lemma const_Icc_of_hasDerivAt_zero {f : ℝ → ℝ}
    (h : ∀ x ∈ Set.Icc (0:ℝ) Real.pi, HasDerivAt f 0 x) :
    ∀ x ∈ Set.Icc (0:ℝ) Real.pi, f x = f 0 := by
  intro x hx
  have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) Real.pi := ⟨le_rfl, le_of_lt Real.pi_pos⟩
  refine (convex_Icc (0:ℝ) Real.pi).is_const_of_fderivWithin_eq_zero
    (𝕜 := ℝ) ?_ ?_ hx h0
  · intro z hz
    exact (h z hz).differentiableAt.differentiableWithinAt
  · intro z hz
    rw [fderivWithin_eq_fderiv ((uniqueDiffOn_Icc Real.pi_pos) z hz)
      ((h z hz).differentiableAt)]
    simpa using (h z hz).hasFDerivAt.fderiv

lemma oscillatory_relation {y : ℝ → ℝ} {k : ℝ}
    (hy : ∀ x ∈ Set.Icc (0:ℝ) Real.pi, HasDerivAt y (deriv y x) x)
    (hyy : ∀ x ∈ Set.Icc (0:ℝ) Real.pi,
      HasDerivAt (deriv y) (-(k^2 * y x)) x)
    (hy0 : y 0 = 0) :
    ∀ x ∈ Set.Icc (0:ℝ) Real.pi,
      k * y x = (deriv y 0) * Real.sin (k*x) := by
  -- the two rotating first integrals are constant
  let A : ℝ → ℝ := fun t => deriv y t * Real.cos (k*t) + k * y t * Real.sin (k*t)
  let B : ℝ → ℝ := fun t => deriv y t * Real.sin (k*t) - k * y t * Real.cos (k*t)
  have harg (x : ℝ) : HasDerivAt (fun t : ℝ => k*t) k x := by
    simpa using (hasDerivAt_id x).const_mul k
  have hAder : ∀ x ∈ Set.Icc (0:ℝ) Real.pi, HasDerivAt A 0 x := by
    intro x hx
    have hs := (harg x).sin
    have hc := (harg x).cos
    have h1 := (hyy x hx).mul hc
    have h2 := ((hy x hx).const_mul k).mul hs
    have hadd := h1.add h2
    -- after cancelling the mixed terms the derivative is zero
    change HasDerivAt (fun t => deriv y t * Real.cos (k*t) + k * y t * Real.sin (k*t)) _ x at hadd
    have hv :
        (-(k^2 * y x)) * Real.cos (k*x) + deriv y x * (-Real.sin (k*x) * k) +
          (k * deriv y x * Real.sin (k*x) + k * y x * (Real.cos (k*x) * k)) = (0:ℝ) := by
      ring
    -- same displayed derivative as in `hadd`
    rw [hv] at hadd
    exact hadd
  have hBder : ∀ x ∈ Set.Icc (0:ℝ) Real.pi, HasDerivAt B 0 x := by
    intro x hx
    have hs := (harg x).sin
    have hc := (harg x).cos
    have h1 := (hyy x hx).mul hs
    have h2 := ((hy x hx).const_mul k).mul hc
    have hsub := h1.sub h2
    change HasDerivAt (fun t => deriv y t * Real.sin (k*t) - k * y t * Real.cos (k*t)) _ x at hsub
    have hv :
        (-(k^2 * y x)) * Real.sin (k*x) + deriv y x * (Real.cos (k*x) * k) -
          (k * deriv y x * Real.cos (k*x) + k * y x * (-Real.sin (k*x) * k)) = (0:ℝ) := by
      ring
    rw [hv] at hsub
    exact hsub
  have hA := const_Icc_of_hasDerivAt_zero hAder
  have hB := const_Icc_of_hasDerivAt_zero hBder
  intro x hx
  have ha := hA x hx
  have hb := hB x hx
  -- evaluate constants at zero
  dsimp [A] at ha
  dsimp [B] at hb
  -- trig at zero, y0
  have ha' : deriv y x * Real.cos (k*x) + k * y x * Real.sin (k*x) = deriv y 0 := by
    simpa [hy0] using ha
  have hb' : deriv y x * Real.sin (k*x) - k * y x * Real.cos (k*x) = 0 := by
    simpa [hy0] using hb
  have htr := Real.sin_sq_add_cos_sq (k*x)
  calc
    k * y x = k * y x * (Real.sin (k*x)^2 + Real.cos (k*x)^2) := by rw [htr]; ring
    _ = (deriv y x * Real.cos (k*x) + k * y x * Real.sin (k*x)) * Real.sin (k*x)
          - (deriv y x * Real.sin (k*x) - k * y x * Real.cos (k*x)) * Real.cos (k*x) := by ring
    _ = (deriv y 0) * Real.sin (k*x) := by rw [ha', hb']; ring

lemma growing_zero {y : ℝ → ℝ} {k : ℝ} (hk : 0 < k)
    (hy : ∀ x ∈ Set.Icc (0:ℝ) Real.pi, HasDerivAt y (deriv y x) x)
    (hyy : ∀ x ∈ Set.Icc (0:ℝ) Real.pi,
      HasDerivAt (deriv y) (k^2 * y x) x)
    (hy0 : y 0 = 0) (hypi : y Real.pi = 0) :
    ∀ x ∈ Set.Icc (0:ℝ) Real.pi, y x = 0 := by
  let C : ℝ → ℝ := fun t => (deriv y t - k * y t) * Real.exp (k*t)
  let D : ℝ → ℝ := fun t => (deriv y t + k * y t) * Real.exp ((-k)*t)
  have harg (x : ℝ) : HasDerivAt (fun t : ℝ => k*t) k x := by
    simpa using (hasDerivAt_id x).const_mul k
  have hCder : ∀ x ∈ Set.Icc (0:ℝ) Real.pi, HasDerivAt C 0 x := by
    intro x hx
    have he := (harg x).exp
    have hsub := (hyy x hx).sub ((hy x hx).const_mul k)
    have hm := hsub.mul he
    change HasDerivAt (fun t => (deriv y t - k * y t) * Real.exp (k*t))
      ((k^2 * y x - k * deriv y x) * Real.exp (k*x) +
          (deriv y x - k * y x) * (Real.exp (k*x) * k)) x at hm
    have hv :
        (k^2 * y x - k * deriv y x) * Real.exp (k*x) +
          (deriv y x - k * y x) * (Real.exp (k*x) * k) = (0:ℝ) := by ring
    rw [hv] at hm
    exact hm
  have hDder : ∀ x ∈ Set.Icc (0:ℝ) Real.pi, HasDerivAt D 0 x := by
    intro x hx
    have hneg : HasDerivAt (fun t : ℝ => (-k)*t) (-k) x := by
      simpa using (hasDerivAt_id x).const_mul (-k)
    have he := hneg.exp
    have hp := (hyy x hx).add ((hy x hx).const_mul k)
    have hm := hp.mul he
    change HasDerivAt (fun t => (deriv y t + k * y t) * Real.exp ((-k)*t))
      ((k^2 * y x + k * deriv y x) * Real.exp ((-k)*x) +
          (deriv y x + k * y x) * (Real.exp ((-k)*x) * (-k))) x at hm
    have hv :
        (k^2 * y x + k * deriv y x) * Real.exp ((-k)*x) +
          (deriv y x + k * y x) * (Real.exp ((-k)*x) * (-k)) = (0:ℝ) := by ring
    rw [hv] at hm
    exact hm
  have hC := const_Icc_of_hasDerivAt_zero hCder
  have hD := const_Icc_of_hasDerivAt_zero hDder
  have hpi : Real.pi ∈ Set.Icc (0:ℝ) Real.pi := ⟨le_of_lt Real.pi_pos, le_rfl⟩
  have hcpi := hC Real.pi hpi
  have hdpi := hD Real.pi hpi
  dsimp [C] at hcpi
  dsimp [D] at hdpi
  have hcpi' : deriv y Real.pi * Real.exp (k*Real.pi) = deriv y 0 := by
    simpa [hy0, hypi] using hcpi
  have hdpi' : deriv y Real.pi * Real.exp (-(k*Real.pi)) = deriv y 0 := by
    simpa [hy0, hypi] using hdpi
  have hltarg : -(k*Real.pi) < k*Real.pi := by
    have : 0 < k * Real.pi := mul_pos hk Real.pi_pos
    linarith
  have hne : Real.exp (k*Real.pi) ≠ Real.exp (-(k*Real.pi)) := by
    have hh : Real.exp (-(k*Real.pi)) < Real.exp (k*Real.pi) := (Real.exp_lt_exp).2 hltarg
    linarith
  have hderpi : deriv y Real.pi = 0 := by
    -- subtract the two equations
    rcases mul_eq_zero.mp (by
      have : deriv y Real.pi * (Real.exp (k*Real.pi) - Real.exp (-(k*Real.pi))) = 0 := by
        rw [mul_sub, hcpi', hdpi']; ring
      exact this) with h | h
    · exact h
    · exfalso
      apply hne
      exact sub_eq_zero.mp h
  have hd0 : deriv y 0 = 0 := by
    rw [← hcpi', hderpi, zero_mul]
  intro x hx
  have hc := hC x hx
  have hd := hD x hx
  dsimp [C] at hc
  dsimp [D] at hd
  have hc' : (deriv y x - k * y x) = 0 := by
    have htmp : (deriv y x - k * y x) * Real.exp (k*x) = 0 := by
      simpa [hy0, hd0] using hc
    exact (mul_eq_zero.mp htmp).resolve_right (Real.exp_ne_zero _)
  have hd' : (deriv y x + k * y x) = 0 := by
    have htmp : (deriv y x + k * y x) * Real.exp ((-k)*x) = 0 := by
      simpa [hy0, hd0] using hd
    exact (mul_eq_zero.mp htmp).resolve_right (Real.exp_ne_zero _)
  have : k * y x = 0 := by linarith
  exact (mul_eq_zero.mp this).resolve_left (ne_of_gt hk)

lemma flat_zero {y : ℝ → ℝ}
    (hy : ∀ x ∈ Set.Icc (0:ℝ) Real.pi, HasDerivAt y (deriv y x) x)
    (hyy0 : ∀ x ∈ Set.Icc (0:ℝ) Real.pi, HasDerivAt (deriv y) 0 x)
    (hy0 : y 0 = 0) (hypi : y Real.pi = 0) :
    ∀ x ∈ Set.Icc (0:ℝ) Real.pi, y x = 0 := by
  let d : ℝ := deriv y 0
  have hdc := const_Icc_of_hasDerivAt_zero hyy0
  let E : ℝ → ℝ := fun t => y t - d*t
  have hEder : ∀ x ∈ Set.Icc (0:ℝ) Real.pi, HasDerivAt E 0 x := by
    intro x hx
    have hsub := (hy x hx).sub ((hasDerivAt_id x).const_mul d)
    change HasDerivAt (fun t => y t - d*t) (deriv y x - d*1) x at hsub
    have hv : deriv y x = d := by
      dsimp [d]
      exact hdc x hx
    have hzero : deriv y x - d*1 = (0:ℝ) := by rw [hv]; ring
    rw [hzero] at hsub
    exact hsub
  have hE := const_Icc_of_hasDerivAt_zero hEder
  have hpi : Real.pi ∈ Set.Icc (0:ℝ) Real.pi := ⟨le_of_lt Real.pi_pos, le_rfl⟩
  have hepi := hE Real.pi hpi
  dsimp [E] at hepi
  have hd : d = 0 := by
    have hmul : d * Real.pi = 0 := by
      have : (0:ℝ) - d * Real.pi = 0 := by simpa [hy0, hypi] using hepi
      linarith
    exact (mul_eq_zero.mp hmul).resolve_right (ne_of_gt Real.pi_pos)
  intro x hx
  have he := hE x hx
  dsimp [E] at he
  simpa [hd, hy0] using he



/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem dirichlet_eigenvalues_eq_nat_sq (lam : ℝ) :
    (∃ (y : ℝ → ℝ) (J : Set ℝ),
        IsOpen J ∧ Set.Icc (0 : ℝ) Real.pi ⊆ J ∧
        (∀ x ∈ J, HasDerivAt y (deriv y x) x) ∧
        (∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x) ∧
        y 0 = 0 ∧ y Real.pi = 0 ∧
        ∃ x ∈ Set.Ioo (0 : ℝ) Real.pi, y x ≠ 0) ↔
      ∃ n : ℕ, 0 < n ∧ lam = (n : ℝ) ^ 2 :=
/-ResultProofBegin-/by
  constructor
  · rintro ⟨y, J, hJo, hinc, hyJ, hyyJ, hy0, hypi, hnon⟩
    have hy : ∀ x ∈ Set.Icc (0:ℝ) Real.pi, HasDerivAt y (deriv y x) x := by
      intro x hx; exact hyJ x (hinc hx)
    -- first rule out zero and negative values
    have hyyI : ∀ x ∈ Set.Icc (0:ℝ) Real.pi,
          HasDerivAt (deriv y) (-(lam * y x)) x := by
      intro x hx; exact hyyJ x (hinc hx)
    rcases hnon with ⟨x₀, hx₀, hnx₀⟩
    have hx₀c : x₀ ∈ Set.Icc (0:ℝ) Real.pi :=
      ⟨le_of_lt hx₀.1, le_of_lt hx₀.2⟩
    have hlampos : 0 < lam := by
      by_contra hnpos
      have hle : lam ≤ 0 := le_of_not_gt hnpos
      rcases lt_or_eq_of_le hle with hlt | hzero
      · -- negative: exponentials give only the zero solution
        let k : ℝ := Real.sqrt (-lam)
        have hk : 0 < k := by
          dsimp [k]
          exact Real.sqrt_pos.2 (by linarith)
        have hksq : k^2 = -lam := by
          dsimp [k]
          exact Real.sq_sqrt (by linarith)
        have hyyGrow : ∀ x ∈ Set.Icc (0:ℝ) Real.pi,
              HasDerivAt (deriv y) (k^2 * y x) x := by
          intro x hx
          have hv : -(lam * y x) = k^2 * y x := by
            rw [hksq]
            ring
          have hh := hyyI x hx
          rw [hv] at hh
          exact hh
        have hzall := growing_zero hk hy hyyGrow hy0 hypi
        exact hnx₀ (hzall x₀ hx₀c)
      · -- zero: affine function, both endpoints kill it
        have hyyFlat : ∀ x ∈ Set.Icc (0:ℝ) Real.pi,
              HasDerivAt (deriv y) 0 x := by
          intro x hx
          have hh := hyyI x hx
          rw [hzero] at hh
          simpa using hh
        have hzall := flat_zero hy hyyFlat hy0 hypi
        exact hnx₀ (hzall x₀ hx₀c)
    -- oscillating case
    let k : ℝ := Real.sqrt lam
    have hk : 0 < k := by
      dsimp [k]
      exact Real.sqrt_pos.2 hlampos
    have hksq : k^2 = lam := by
      dsimp [k]
      exact Real.sq_sqrt (le_of_lt hlampos)
    have hyyOsc : ∀ x ∈ Set.Icc (0:ℝ) Real.pi,
          HasDerivAt (deriv y) (-(k^2 * y x)) x := by
      intro x hx
      have hv : -(lam * y x) = -(k^2 * y x) := by rw [hksq]
      have hh := hyyI x hx
      rw [hv] at hh
      exact hh
    have hrel := oscillatory_relation hy hyyOsc hy0
    have hdne : deriv y 0 ≠ 0 := by
      intro hd
      have hr := hrel x₀ hx₀c
      rw [hd, zero_mul] at hr
      have hmul : k * y x₀ = 0 := by simpa using hr
      have : y x₀ = 0 := (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hk)
      exact hnx₀ this
    have hsin : Real.sin (k * Real.pi) = 0 := by
      have hr := hrel Real.pi ⟨le_of_lt Real.pi_pos, le_rfl⟩
      have hm : (deriv y 0) * Real.sin (k * Real.pi) = 0 := by
        rw [hypi, mul_zero] at hr
        exact hr.symm
      exact (mul_eq_zero.mp hm).resolve_left hdne
    rcases (Real.sin_eq_zero_iff).1 hsin with ⟨z, hz⟩
    have hzk : (z:ℝ) = k := by
      exact mul_right_cancel₀ (ne_of_gt Real.pi_pos) hz
    have hzpos : 0 < z := (Int.cast_pos.mp (by simpa [hzk] using hk : (0:ℝ) < (z:ℝ)))
    obtain ⟨n, hnz⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hzpos)
    -- replace the integer by a natural one
    subst z
    refine ⟨n, ?_, ?_⟩
    · exact_mod_cast hzpos
    · have hnk : (n:ℝ) = k := by simpa using hzk
      rw [← hksq, ← hnk]
  · rintro ⟨n, hn, hlam⟩
    let k : ℝ := (n:ℝ)
    have hk : 0 < k := by dsimp [k]; exact_mod_cast hn
    have hlamk : lam = k^2 := by simpa [k] using hlam
    let y : ℝ → ℝ := fun t => Real.sin (k*t)
    have harg (x : ℝ) : HasDerivAt (fun t : ℝ => k*t) k x := by
      simpa using (hasDerivAt_id x).const_mul k
    have hyspec (x : ℝ) : HasDerivAt y (Real.cos (k*x) * k) x := by
      simpa [y] using (harg x).sin
    have hderfun : deriv y = (fun t => Real.cos (k*t) * k) := by
      funext t
      exact (hyspec t).deriv
    refine ⟨y, Set.univ, isOpen_univ, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx; trivial
    · intro x hx
      have hd := hyspec x
      rw [(hyspec x).deriv]
      exact hd
    · intro x hx
      have hc : HasDerivAt (fun t : ℝ => Real.cos (k*t))
            (-Real.sin (k*x) * k) x := (harg x).cos
      have hm := hc.mul_const k
      change HasDerivAt (fun t : ℝ => Real.cos (k*t) * k)
          ((-Real.sin (k*x) * k) * k) x at hm
      have hv : ((-Real.sin (k*x) * k) * k) = -(lam * y x) := by
        dsimp [y]
        rw [hlamk]
        ring
      rw [hv] at hm
      rw [hderfun]
      exact hm
    · dsimp [y]
      simp
    · dsimp [y, k]
      exact Real.sin_nat_mul_pi n
    · refine ⟨Real.pi / (2*k), ?_, ?_⟩
      · have hk2 : 0 < 2*k := by linarith
        refine ⟨div_pos Real.pi_pos hk2, ?_⟩
        apply (div_lt_iff₀ hk2).2
        have h2 : 1 < 2*k := by
          have hkone : (1:ℝ) ≤ k := by
            dsimp [k]
            exact_mod_cast (Nat.one_le_iff_ne_zero.2 (Nat.ne_of_gt hn))
          linarith
        nlinarith [Real.pi_pos]
      · dsimp [y]
        have hv : k * (Real.pi / (2*k)) = Real.pi/2 := by
          field_simp
        rw [hv, Real.sin_pi_div_two]
        norm_num
/-ResultProofEnd-/
/-ResultEnd-/

end Submission
