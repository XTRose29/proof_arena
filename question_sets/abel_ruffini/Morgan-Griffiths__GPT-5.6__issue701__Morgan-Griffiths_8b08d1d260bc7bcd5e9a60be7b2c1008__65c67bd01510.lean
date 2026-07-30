import Mathlib
namespace Submission

open Polynomial
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/

-- elementary radical formulas used for degrees at most four
-- trial
lemma test_linear {p : ℚ[X]} (hp : p.natDegree = 1) (x : ℂ)
    (hx : aeval x p = 0) : x ∈ solvableByRad ℚ ℂ := by
  obtain ⟨a, ha, b, hab⟩ := (Polynomial.natDegree_eq_one (p := p)).1 hp
  have hx' : (algebraMap ℚ ℂ a) * x + algebraMap ℚ ℂ b = 0 := by
    have h := hx
    rw [← hab] at h
    simpa using h
  have ha' : (algebraMap ℚ ℂ a) ≠ 0 := (map_ne_zero (algebraMap ℚ ℂ)).2 ha
  have htmp : x * (algebraMap ℚ ℂ a) + (algebraMap ℚ ℂ b) = 0 := by
    simpa [mul_comm] using hx'
  have hmul : x * (algebraMap ℚ ℂ a) = -(algebraMap ℚ ℂ b) :=
    eq_neg_of_add_eq_zero_left htmp
  have hxval : x = -(algebraMap ℚ ℂ b) / (algebraMap ℚ ℂ a) := by
    exact (eq_div_iff ha').2 hmul
  rw [hxval]
  exact (solvableByRad ℚ ℂ).div_mem
    ((solvableByRad ℚ ℂ).neg_mem ((solvableByRad ℚ ℂ).algebraMap_mem b))
    ((solvableByRad ℚ ℂ).algebraMap_mem a)

lemma test_quad {p : ℚ[X]} (hp : p.natDegree = 2) (x : ℂ)
    (hx : aeval x p = 0) : x ∈ solvableByRad ℚ ℂ := by
  classical
  let a : ℚ := p.coeff 2
  let b : ℚ := p.coeff 1
  let c : ℚ := p.coeff 0
  have hp_le : p.natDegree ≤ 2 := by omega
  have hpform : p = C a * X^2 + C b * X + C c := by
    ext k
    by_cases hk : k ≤ 2
    · interval_cases k <;> simp [a, b, c]
    · have hk' : 2 < k := by omega
      have hzero : p.coeff k = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp_le hk')
      -- all the displayed coefficients also vanish above degree two
      -- simp expands coefficients of powers of X
      have hk0 : k ≠ 0 := by omega
      have hk1 : k ≠ 1 := by omega
      have h1k : (1:ℕ) ≠ k := by omega
      have hk2 : k ≠ 2 := by omega
      have h2k : (2:ℕ) ≠ k := by omega
      simp [coeff_add, coeff_C_mul_X, coeff_C_mul_X_pow, coeff_X, coeff_C,
        hk0, hk1, h1k, hk2, h2k, hzero]
  have hpx : (algebraMap ℚ ℂ a) * x^2 + (algebraMap ℚ ℂ b) * x +
       (algebraMap ℚ ℂ c) = 0 := by
    have h := hx
    rw [hpform] at h
    simpa using h
  have hpne : p ≠ 0 := by
    apply Polynomial.ne_zero_of_natDegree_gt (p:=p) (n:=0)
    omega
  have hlead : p.leadingCoeff ≠ 0 :=
    (Polynomial.leadingCoeff_ne_zero).2 hpne
  have ha0 : a ≠ 0 := by
    dsimp [a]
    have hco : p.coeff p.natDegree ≠ 0 := by
      simpa using hlead
    simpa [hp] using hco
  have ha0' : (algebraMap ℚ ℂ a) ≠ 0 := (map_ne_zero (algebraMap ℚ ℂ)).2 ha0
  let y : ℂ := (2:ℂ) * (algebraMap ℚ ℂ a) * x + (algebraMap ℚ ℂ b)
  have hy_eq : y^2 = (algebraMap ℚ ℂ b)^2 -
        (4:ℂ) * (algebraMap ℚ ℂ a) * (algebraMap ℚ ℂ c) := by
    dsimp [y]
    calc
      ((2:ℂ) * (algebraMap ℚ ℂ a) * x + (algebraMap ℚ ℂ b))^2 =
          (algebraMap ℚ ℂ b)^2 - (4:ℂ) * (algebraMap ℚ ℂ a) * (algebraMap ℚ ℂ c)
            + (4:ℂ) * (algebraMap ℚ ℂ a) *
              ((algebraMap ℚ ℂ a) * x^2 + (algebraMap ℚ ℂ b) * x +
               (algebraMap ℚ ℂ c)) := by ring
      _ = (algebraMap ℚ ℂ b)^2 - (4:ℂ) * (algebraMap ℚ ℂ a) *
            (algebraMap ℚ ℂ c) := by rw [hpx]; ring
  have hy_pow : y^2 ∈ solvableByRad ℚ ℂ := by
    rw [hy_eq]
    have hz := (solvableByRad ℚ ℂ).algebraMap_mem (b^2 - 4*a*c)
    simpa using hz
  have hy_mem : y ∈ solvableByRad ℚ ℂ :=
    solvableByRad.rad_mem (n:=2) (by decide) hy_pow
  have hden : (2:ℂ) * (algebraMap ℚ ℂ a) ≠ 0 :=
    mul_ne_zero (by norm_num) ha0'
  have hxval : x = (y - algebraMap ℚ ℂ b) /
        ((2:ℂ) * algebraMap ℚ ℂ a) := by
    apply (eq_div_iff hden).2
    dsimp [y]
    ring
  rw [hxval]
  have hbmem : (algebraMap ℚ ℂ b) ∈ solvableByRad ℚ ℂ :=
    (solvableByRad ℚ ℂ).algebraMap_mem b
  have hdenmem : ((2:ℂ) * (algebraMap ℚ ℂ a)) ∈ solvableByRad ℚ ℂ := by
    have hh := (solvableByRad ℚ ℂ).algebraMap_mem ((2:ℚ)*a)
    simpa using hh
  exact (solvableByRad ℚ ℂ).div_mem
     ((solvableByRad ℚ ℂ).sub_mem hy_mem hbmem) hdenmem

lemma depressed_exists (P Q : ℂ)
    (hPmem : P ∈ solvableByRad ℚ ℂ)
    (hQmem : Q ∈ solvableByRad ℚ ℂ) :
    ∃ t : ℂ, t ∈ solvableByRad ℚ ℂ ∧ t^3 + P*t + Q = 0 := by
  classical
  by_cases hP0 : P = 0
  · subst P
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (-Q) (n:=3) (by norm_num)
    refine ⟨u, ?_, ?_⟩
    · apply solvableByRad.rad_mem (n:=3) (by norm_num)
      rw [hu]
      exact (solvableByRad ℚ ℂ).neg_mem hQmem
    · rw [hu]
      ring
  · let D : ℂ := (Q/2)^2 + (P/3)^3
    have hDmem : D ∈ solvableByRad ℚ ℂ := by
      dsimp [D]
      have h2 : (2:ℂ) ∈ solvableByRad ℚ ℂ :=
        (solvableByRad ℚ ℂ).natCast_mem 2
      have h3 : (3:ℂ) ∈ solvableByRad ℚ ℂ :=
        (solvableByRad ℚ ℂ).natCast_mem 3
      exact (solvableByRad ℚ ℂ).add_mem
        (pow_mem ((solvableByRad ℚ ℂ).div_mem hQmem h2) 2)
        (pow_mem ((solvableByRad ℚ ℂ).div_mem hPmem h3) 3)
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq D (n:=2) (by norm_num)
    have hsmem : s ∈ solvableByRad ℚ ℂ :=
      solvableByRad.rad_mem (n:=2) (by norm_num) (by
        rw [hs]
        exact hDmem)
    let W : ℂ := -Q/2 + s
    have hWmem : W ∈ solvableByRad ℚ ℂ := by
      dsimp [W]
      exact (solvableByRad ℚ ℂ).add_mem
        ((solvableByRad ℚ ℂ).div_mem ((solvableByRad ℚ ℂ).neg_mem hQmem)
          ((solvableByRad ℚ ℂ).natCast_mem 2)) hsmem
    have hWmul : W * (-Q/2 - s) = -(P/3)^3 := by
      dsimp [W, D] at hs ⊢
      calc
        (-Q / 2 + s) * (-Q / 2 - s) = (-Q/2)^2 - s^2 := by ring
        _ = -(P/3)^3 := by rw [hs]; ring
    have hP3 : -(P/3)^3 ≠ (0:ℂ) := by
      apply neg_ne_zero.mpr
      apply pow_ne_zero
      exact div_ne_zero hP0 (by norm_num)
    have hW0 : W ≠ 0 := by
      intro h
      have hcontra := hWmul
      rw [h, zero_mul] at hcontra
      exact hP3 hcontra.symm
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq W (n:=3) (by norm_num)
    have humem : u ∈ solvableByRad ℚ ℂ :=
      solvableByRad.rad_mem (n:=3) (by norm_num) (by
        rw [hu]
        exact hWmem)
    have hu0 : u ≠ 0 := by
      intro h
      have h' := hu
      rw [h] at h'
      norm_num at h'
      exact hW0 h'.symm
    let v : ℂ := -P / (3*u)
    have hvmem : v ∈ solvableByRad ℚ ℂ := by
      dsimp [v]
      exact (solvableByRad ℚ ℂ).div_mem
        ((solvableByRad ℚ ℂ).neg_mem hPmem)
        ((solvableByRad ℚ ℂ).mul_mem ((solvableByRad ℚ ℂ).natCast_mem 3) humem)
    have hvprod : v^3 * u^3 = -(P/3)^3 := by
      dsimp [v]
      field_simp
      <;> ring
    have hv3 : v^3 = -Q/2 - s := by
      apply mul_right_cancel₀ (pow_ne_zero 3 hu0)
      calc
        v^3 * u^3 = -(P/3)^3 := hvprod
        _ = W * (-Q/2 - s) := hWmul.symm
        _ = (-Q/2 - s) * u^3 := by rw [hu]; ring
    have huv : u * v = -P/3 := by
      dsimp [v]
      field_simp
      <;> ring
    refine ⟨u+v, (solvableByRad ℚ ℂ).add_mem humem hvmem, ?_⟩
    have hsum : u^3 + v^3 = -Q := by
      rw [hu, hv3]
      dsimp [W]
      ring
    calc
      (u+v)^3 + P*(u+v) + Q =
          (u^3 + v^3) + ((3:ℂ)*(u*v)+P)*(u+v)+Q := by ring
      _ = 0 := by rw [hsum, huv]; ring

lemma depressed_root_mem (P Q z : ℂ)
    (hPmem : P ∈ solvableByRad ℚ ℂ)
    (hQmem : Q ∈ solvableByRad ℚ ℂ)
    (hz : z^3 + P*z + Q = 0) : z ∈ solvableByRad ℚ ℂ := by
  classical
  obtain ⟨t, htmem, ht⟩ := depressed_exists P Q hPmem hQmem
  have hfac : (z-t) * (z^2 + t*z + (t^2 + P)) = 0 := by
    calc
      (z-t) * (z^2 + t*z + (t^2 + P)) =
          (z^3 + P*z + Q) - (t^3 + P*t + Q) := by ring
      _ = 0 := by rw [hz, ht]; ring
  rcases mul_eq_zero.mp hfac with hzt | hq
  · have he : z = t := sub_eq_zero.mp hzt
    simpa [he] using htmem
  · let w : ℂ := (2:ℂ)*z + t
    have hw : w^2 = t^2 - (4:ℂ)*(t^2+P) := by
      dsimp [w]
      calc
        ((2:ℂ)*z+t)^2 = t^2 - (4:ℂ)*(t^2+P)
              + (4:ℂ)*(z^2 + t*z + (t^2+P)) := by ring
        _ = t^2 - (4:ℂ)*(t^2+P) := by rw [hq]; ring
    have hw_pow : w^2 ∈ solvableByRad ℚ ℂ := by
      rw [hw]
      exact (solvableByRad ℚ ℂ).sub_mem
        (pow_mem htmem 2)
        ((solvableByRad ℚ ℂ).mul_mem ((solvableByRad ℚ ℂ).natCast_mem 4)
          ((solvableByRad ℚ ℂ).add_mem (pow_mem htmem 2) hPmem))
    have hwmem : w ∈ solvableByRad ℚ ℂ :=
      solvableByRad.rad_mem (n:=2) (by norm_num) hw_pow
    have hval : z = (w-t) / (2:ℂ) := by
      dsimp [w]
      ring
    rw [hval]
    exact (solvableByRad ℚ ℂ).div_mem
      ((solvableByRad ℚ ℂ).sub_mem hwmem htmem)
      ((solvableByRad ℚ ℂ).natCast_mem 2)

lemma test_cubic {p : ℚ[X]} (hp : p.natDegree = 3) (x : ℂ)
    (hx : aeval x p = 0) : x ∈ solvableByRad ℚ ℂ := by
  classical
  let a : ℚ := p.coeff 3
  let b : ℚ := p.coeff 2
  let c : ℚ := p.coeff 1
  let d : ℚ := p.coeff 0
  have hp_le : p.natDegree ≤ 3 := by omega
  have hpform : p = C a * X^3 + C b * X^2 + C c * X + C d := by
    ext k
    by_cases hk : k ≤ 3
    · interval_cases k <;> simp [a,b,c,d]
    · have hk' : 3 < k := by omega
      have hzero : p.coeff k = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp_le hk')
      have hk0 : k ≠ 0 := by omega
      have hk1 : k ≠ 1 := by omega
      have h1k : (1:ℕ) ≠ k := by omega
      have hk2 : k ≠ 2 := by omega
      have h2k : (2:ℕ) ≠ k := by omega
      have hk3 : k ≠ 3 := by omega
      have h3k : (3:ℕ) ≠ k := by omega
      simp [coeff_add, coeff_C_mul_X, coeff_C_mul_X_pow, coeff_X, coeff_C,
        hk0, hk1, h1k, hk2, h2k, hk3, h3k, hzero]
  have hpx : (algebraMap ℚ ℂ a) * x^3 + (algebraMap ℚ ℂ b) * x^2 +
       (algebraMap ℚ ℂ c) * x + (algebraMap ℚ ℂ d) = 0 := by
    have h := hx
    rw [hpform] at h
    simpa using h
  have hpne : p ≠ 0 := by
    apply Polynomial.ne_zero_of_natDegree_gt (p:=p) (n:=0)
    omega
  have hlead : p.leadingCoeff ≠ 0 :=
    (Polynomial.leadingCoeff_ne_zero).2 hpne
  have ha0 : a ≠ 0 := by
    dsimp [a]
    have hco : p.coeff p.natDegree ≠ 0 := by simpa using hlead
    simpa [hp] using hco
  have ha0' : (algebraMap ℚ ℂ a) ≠ 0 := (map_ne_zero (algebraMap ℚ ℂ)).2 ha0
  -- scale-and-translate to a depressed cubic, avoiding any coefficient inverses
  let P : ℂ := (9:ℂ)*(algebraMap ℚ ℂ a)*(algebraMap ℚ ℂ c)
               - (3:ℂ)*(algebraMap ℚ ℂ b)^2
  let Q : ℂ := (2:ℂ)*(algebraMap ℚ ℂ b)^3
               - (9:ℂ)*(algebraMap ℚ ℂ a)*(algebraMap ℚ ℂ b)*(algebraMap ℚ ℂ c)
               + (27:ℂ)*(algebraMap ℚ ℂ a)^2*(algebraMap ℚ ℂ d)
  let z : ℂ := (3:ℂ)*(algebraMap ℚ ℂ a)*x + (algebraMap ℚ ℂ b)
  have hPmem : P ∈ solvableByRad ℚ ℂ := by
    have hh := (solvableByRad ℚ ℂ).algebraMap_mem (9*a*c - 3*b^2)
    dsimp [P]
    simpa using hh
  have hQmem : Q ∈ solvableByRad ℚ ℂ := by
    have hh := (solvableByRad ℚ ℂ).algebraMap_mem
      (2*b^3 - 9*a*b*c + 27*a^2*d)
    dsimp [Q]
    simpa using hh
  have hz : z^3 + P*z + Q = 0 := by
    dsimp [z, P, Q]
    linear_combination (27:ℂ)*(algebraMap ℚ ℂ a)^2 * hpx
  have hzmem : z ∈ solvableByRad ℚ ℂ :=
    depressed_root_mem P Q z hPmem hQmem hz
  have hden : (3:ℂ)*(algebraMap ℚ ℂ a) ≠ 0 :=
    mul_ne_zero (by norm_num) ha0'
  have hxval : x = (z - algebraMap ℚ ℂ b) /
       ((3:ℂ) * algebraMap ℚ ℂ a) := by
    apply (eq_div_iff hden).2
    dsimp [z]
    ring
  rw [hxval]
  exact (solvableByRad ℚ ℂ).div_mem
    ((solvableByRad ℚ ℂ).sub_mem hzmem ((solvableByRad ℚ ℂ).algebraMap_mem b))
    (by
      have hh := (solvableByRad ℚ ℂ).algebraMap_mem ((3:ℚ)*a)
      simpa using hh)

lemma monic_quad_mem (B C z : ℂ)
    (hB : B ∈ solvableByRad ℚ ℂ) (hC : C ∈ solvableByRad ℚ ℂ)
    (hz : z^2 + B*z + C = 0) : z ∈ solvableByRad ℚ ℂ := by
  let w : ℂ := (2:ℂ)*z + B
  have hw : w^2 = B^2 - (4:ℂ)*C := by
    dsimp [w]
    calc
      ((2:ℂ)*z+B)^2 = B^2 - (4:ℂ)*C + (4:ℂ)*(z^2+B*z+C) := by ring
      _ = B^2 - (4:ℂ)*C := by rw [hz]; ring
  have hw_pow : w^2 ∈ solvableByRad ℚ ℂ := by
    rw [hw]
    exact (solvableByRad ℚ ℂ).sub_mem (pow_mem hB 2)
      ((solvableByRad ℚ ℂ).mul_mem ((solvableByRad ℚ ℂ).natCast_mem 4) hC)
  have hwmem : w ∈ solvableByRad ℚ ℂ :=
    solvableByRad.rad_mem (n:=2) (by norm_num) hw_pow
  have hv : z = (w-B) / (2:ℂ) := by
    dsimp [w]
    ring
  rw [hv]
  exact (solvableByRad ℚ ℂ).div_mem ((solvableByRad ℚ ℂ).sub_mem hwmem hB)
    ((solvableByRad ℚ ℂ).natCast_mem 2)

lemma monic_cubic_exists (B C D : ℂ)
    (hB : B ∈ solvableByRad ℚ ℂ) (hC : C ∈ solvableByRad ℚ ℂ)
    (hD : D ∈ solvableByRad ℚ ℂ) :
    ∃ y : ℂ, y ∈ solvableByRad ℚ ℂ ∧ y^3 + B*y^2 + C*y + D = 0 := by
  let P : ℂ := (9:ℂ)*C - (3:ℂ)*B^2
  let Q : ℂ := (2:ℂ)*B^3 - (9:ℂ)*B*C + (27:ℂ)*D
  have hP : P ∈ solvableByRad ℚ ℂ := by
    dsimp [P]
    exact (solvableByRad ℚ ℂ).sub_mem
      ((solvableByRad ℚ ℂ).mul_mem ((solvableByRad ℚ ℂ).natCast_mem 9) hC)
      ((solvableByRad ℚ ℂ).mul_mem ((solvableByRad ℚ ℂ).natCast_mem 3) (pow_mem hB 2))
  have hQ : Q ∈ solvableByRad ℚ ℂ := by
    dsimp [Q]
    exact (solvableByRad ℚ ℂ).add_mem
      ((solvableByRad ℚ ℂ).sub_mem
        ((solvableByRad ℚ ℂ).mul_mem ((solvableByRad ℚ ℂ).natCast_mem 2) (pow_mem hB 3))
        ((solvableByRad ℚ ℂ).mul_mem
          ((solvableByRad ℚ ℂ).mul_mem
            ((solvableByRad ℚ ℂ).natCast_mem 9) hB) hC))
      ((solvableByRad ℚ ℂ).mul_mem ((solvableByRad ℚ ℂ).natCast_mem 27) hD)
  obtain ⟨z, hzmem, hz⟩ := depressed_exists P Q hP hQ
  let y : ℂ := (z-B)/(3:ℂ)
  refine ⟨y, ?_, ?_⟩
  · dsimp [y]
    exact (solvableByRad ℚ ℂ).div_mem ((solvableByRad ℚ ℂ).sub_mem hzmem hB)
      ((solvableByRad ℚ ℂ).natCast_mem 3)
  · dsimp [y]
    dsimp [P, Q] at hz
    -- the standard translation z=3y+B
    linear_combination hz / 27

lemma depressed_quartic_mem (p q r z : ℂ)
    (hp : p ∈ solvableByRad ℚ ℂ) (hq : q ∈ solvableByRad ℚ ℂ)
    (hr : r ∈ solvableByRad ℚ ℂ)
    (hz : z^4 + p*z^2 + q*z + r = 0) : z ∈ solvableByRad ℚ ℂ := by
  classical
  by_cases hq0 : q = 0
  · have hyq : (z^2)^2 + p*(z^2) + r = 0 := by
      -- the biquadratic case
      rw [hq0] at hz
      linear_combination hz
    have hpow : z^2 ∈ solvableByRad ℚ ℂ :=
      monic_quad_mem p r (z^2) hp hr hyq
    exact solvableByRad.rad_mem (n:=2) (by norm_num) hpow
  · have h2p : (2:ℂ)*p ∈ solvableByRad ℚ ℂ :=
      (solvableByRad ℚ ℂ).mul_mem ((solvableByRad ℚ ℂ).natCast_mem 2) hp
    have hmid : p^2-(4:ℂ)*r ∈ solvableByRad ℚ ℂ :=
      (solvableByRad ℚ ℂ).sub_mem (pow_mem hp 2)
        ((solvableByRad ℚ ℂ).mul_mem ((solvableByRad ℚ ℂ).natCast_mem 4) hr)
    have hlast : -(q^2) ∈ solvableByRad ℚ ℂ :=
      (solvableByRad ℚ ℂ).neg_mem (pow_mem hq 2)
    obtain ⟨y, hymem, hyeq⟩ := monic_cubic_exists ((2:ℂ)*p)
       (p^2-(4:ℂ)*r) (-(q^2)) h2p hmid hlast
    have hy0 : y ≠ 0 := by
      intro hh
      subst y
      have hzero : q^2 = 0 := by
        have := hyeq
        -- the constant term of the resolvent would vanish
        simpa using this
      have : q = 0 := (sq_eq_zero_iff).1 (by simpa [pow_two] using hzero)
      exact hq0 this
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq y (n:=2) (by norm_num)
    have humem : u ∈ solvableByRad ℚ ℂ :=
      solvableByRad.rad_mem (n:=2) (by norm_num) (by
        rw [hu]
        exact hymem)
    have hu0 : u ≠ 0 := by
      intro hh
      have h' := hu
      rw [hh] at h'
      norm_num at h'
      exact hy0 h'.symm
    let v : ℂ := (p + y - q/u)/2
    let w : ℂ := (p + y + q/u)/2
    have hvmem : v ∈ solvableByRad ℚ ℂ := by
      dsimp [v]
      exact (solvableByRad ℚ ℂ).div_mem
        ((solvableByRad ℚ ℂ).sub_mem ((solvableByRad ℚ ℂ).add_mem hp hymem)
          ((solvableByRad ℚ ℂ).div_mem hq humem))
        ((solvableByRad ℚ ℂ).natCast_mem 2)
    have hwmem : w ∈ solvableByRad ℚ ℂ := by
      dsimp [w]
      exact (solvableByRad ℚ ℂ).div_mem
        ((solvableByRad ℚ ℂ).add_mem ((solvableByRad ℚ ℂ).add_mem hp hymem)
          ((solvableByRad ℚ ℂ).div_mem hq humem))
        ((solvableByRad ℚ ℂ).natCast_mem 2)
    have hsum : v+w-u^2 = p := by
      dsimp [v, w]
      rw [hu]
      ring
    have hlin : u*(w-v)=q := by
      dsimp [v, w]
      field_simp
      <;> ring
    have hcalc : (p+y)^2*y - q^2 = (4:ℂ)*r*y := by
      linear_combination hyeq
    have hconst : v*w = r := by
      -- multiply by y to avoid the denominator u^2=y
      apply mul_right_cancel₀ hy0
      dsimp [v, w]
      field_simp
      calc
        ((p+y)*u-q)*((p+y)*u+q) = (p+y)^2*u^2-q^2 := by ring
        _ = (p+y)^2*y-q^2 := by rw [hu]
        _ = (4:ℂ)*r*y := hcalc
        _ = u^2 * 2^2 * r := by rw [hu]; ring
    have hfac : (z^2 + u*z + v) * (z^2 - u*z + w) = 0 := by
      calc
        (z^2 + u*z + v) * (z^2 - u*z + w) =
            z^4 + (v+w-u^2)*z^2 + (u*(w-v))*z + v*w := by ring
        _ = 0 := by rw [hsum, hlin, hconst]; exact hz
    rcases mul_eq_zero.mp hfac with hleft | hright
    · exact monic_quad_mem u v z humem hvmem hleft
    · have hright' : z^2 + (-u)*z + w = 0 := by
        convert hright using 1 <;> ring
      exact monic_quad_mem (-u) w z ((solvableByRad ℚ ℂ).neg_mem humem)
        hwmem hright'

lemma monic_quartic_mem (B C D E z : ℂ)
    (hB : B ∈ solvableByRad ℚ ℂ) (hC : C ∈ solvableByRad ℚ ℂ)
    (hD : D ∈ solvableByRad ℚ ℂ) (hE : E ∈ solvableByRad ℚ ℂ)
    (hz : z^4 + B*z^3 + C*z^2 + D*z + E = 0) : z ∈ solvableByRad ℚ ℂ := by
  let p : ℂ := C - (3:ℂ)*B^2/8
  let q : ℂ := D - B*C/2 + B^3/8
  let r : ℂ := E - B*D/4 + B^2*C/16 - (3:ℂ)*B^4/256
  let t : ℂ := z + B/4
  have hp : p ∈ solvableByRad ℚ ℂ := by
    dsimp [p]
    exact (solvableByRad ℚ ℂ).sub_mem hC
      ((solvableByRad ℚ ℂ).div_mem
        ((solvableByRad ℚ ℂ).mul_mem ((solvableByRad ℚ ℂ).natCast_mem 3)
          (pow_mem hB 2)) ((solvableByRad ℚ ℂ).natCast_mem 8))
  have hq : q ∈ solvableByRad ℚ ℂ := by
    dsimp [q]
    exact (solvableByRad ℚ ℂ).add_mem
      ((solvableByRad ℚ ℂ).sub_mem hD
        ((solvableByRad ℚ ℂ).div_mem ((solvableByRad ℚ ℂ).mul_mem hB hC)
          ((solvableByRad ℚ ℂ).natCast_mem 2)))
      ((solvableByRad ℚ ℂ).div_mem (pow_mem hB 3)
        ((solvableByRad ℚ ℂ).natCast_mem 8))
  have hr : r ∈ solvableByRad ℚ ℂ := by
    dsimp [r]
    exact (solvableByRad ℚ ℂ).sub_mem
      ((solvableByRad ℚ ℂ).add_mem
        ((solvableByRad ℚ ℂ).sub_mem hE
          ((solvableByRad ℚ ℂ).div_mem ((solvableByRad ℚ ℂ).mul_mem hB hD)
            ((solvableByRad ℚ ℂ).natCast_mem 4)))
        ((solvableByRad ℚ ℂ).div_mem ((solvableByRad ℚ ℂ).mul_mem (pow_mem hB 2) hC)
          ((solvableByRad ℚ ℂ).natCast_mem 16)))
      ((solvableByRad ℚ ℂ).div_mem
        ((solvableByRad ℚ ℂ).mul_mem ((solvableByRad ℚ ℂ).natCast_mem 3) (pow_mem hB 4))
        ((solvableByRad ℚ ℂ).natCast_mem 256))
  have ht : t^4 + p*t^2 + q*t + r = 0 := by
    dsimp [t, p, q, r]
    linear_combination hz
  have htmem : t ∈ solvableByRad ℚ ℂ := depressed_quartic_mem p q r t hp hq hr ht
  have hv : z = t - B/4 := by dsimp [t]; ring
  rw [hv]
  exact (solvableByRad ℚ ℂ).sub_mem htmem
    ((solvableByRad ℚ ℂ).div_mem hB ((solvableByRad ℚ ℂ).natCast_mem 4))

lemma test_quartic {P : ℚ[X]} (hPdeg : P.natDegree = 4) (x : ℂ)
    (hx : aeval x P = 0) : x ∈ solvableByRad ℚ ℂ := by
  classical
  let a : ℚ := P.coeff 4
  let b : ℚ := P.coeff 3
  let c : ℚ := P.coeff 2
  let d : ℚ := P.coeff 1
  let e : ℚ := P.coeff 0
  have hle : P.natDegree ≤ 4 := by omega
  have hform : P = C a * X^4 + C b * X^3 + C c * X^2 + C d * X + C e := by
    ext k
    by_cases hk : k ≤ 4
    · interval_cases k <;> simp [a,b,c,d,e]
    · have hk' : 4 < k := by omega
      have hzero : P.coeff k = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hle hk')
      have hk0 : k ≠ 0 := by omega
      have h1k : (1:ℕ) ≠ k := by omega
      have hk1 : k ≠ 1 := by omega
      have hk2 : k ≠ 2 := by omega
      have h2k : (2:ℕ) ≠ k := by omega
      have hk3 : k ≠ 3 := by omega
      have h3k : (3:ℕ) ≠ k := by omega
      have hk4 : k ≠ 4 := by omega
      have h4k : (4:ℕ) ≠ k := by omega
      simp [coeff_add, coeff_C_mul_X, coeff_C_mul_X_pow, coeff_X, coeff_C,
        hk0, hk1, h1k, hk2, h2k, hk3, h3k, hk4, h4k, hzero]
  have hpoly : (algebraMap ℚ ℂ a)*x^4 + (algebraMap ℚ ℂ b)*x^3
       + (algebraMap ℚ ℂ c)*x^2 + (algebraMap ℚ ℂ d)*x
       + (algebraMap ℚ ℂ e) = 0 := by
    have h := hx
    rw [hform] at h
    simpa using h
  have hpne : P ≠ 0 := by
    apply Polynomial.ne_zero_of_natDegree_gt (p:=P) (n:=0)
    omega
  have hlead : P.leadingCoeff ≠ 0 :=
    (Polynomial.leadingCoeff_ne_zero).2 hpne
  have ha : a ≠ 0 := by
    dsimp [a]
    have hco : P.coeff P.natDegree ≠ 0 := by simpa using hlead
    simpa [hPdeg] using hco
  have ha' : (algebraMap ℚ ℂ a) ≠ 0 := (map_ne_zero (algebraMap ℚ ℂ)).2 ha
  let B : ℂ := (algebraMap ℚ ℂ b) / (algebraMap ℚ ℂ a)
  let CC : ℂ := (algebraMap ℚ ℂ c) / (algebraMap ℚ ℂ a)
  let D : ℂ := (algebraMap ℚ ℂ d) / (algebraMap ℚ ℂ a)
  let E : ℂ := (algebraMap ℚ ℂ e) / (algebraMap ℚ ℂ a)
  have hB : B ∈ solvableByRad ℚ ℂ := by
    dsimp [B]
    exact (solvableByRad ℚ ℂ).div_mem ((solvableByRad ℚ ℂ).algebraMap_mem b)
      ((solvableByRad ℚ ℂ).algebraMap_mem a)
  have hC : CC ∈ solvableByRad ℚ ℂ := by
    dsimp [CC]
    exact (solvableByRad ℚ ℂ).div_mem ((solvableByRad ℚ ℂ).algebraMap_mem c)
      ((solvableByRad ℚ ℂ).algebraMap_mem a)
  have hD : D ∈ solvableByRad ℚ ℂ := by
    dsimp [D]
    exact (solvableByRad ℚ ℂ).div_mem ((solvableByRad ℚ ℂ).algebraMap_mem d)
      ((solvableByRad ℚ ℂ).algebraMap_mem a)
  have hE : E ∈ solvableByRad ℚ ℂ := by
    dsimp [E]
    exact (solvableByRad ℚ ℂ).div_mem ((solvableByRad ℚ ℂ).algebraMap_mem e)
      ((solvableByRad ℚ ℂ).algebraMap_mem a)
  apply monic_quartic_mem B CC D E x hB hC hD hE
  dsimp [B, CC, D, E]
  field_simp
  linear_combination hpoly



lemma root_four_pair {x y : ℝ} (hx : (5:ℝ)*x^4 - 4 = 0)
 (hy : (5:ℝ)*y^4 - 4 = 0) : x = y ∨ x = -y := by
 have he : x^4 = y^4 := by nlinarith
 have he2 : (x^2)^2 = (y^2)^2 := by nlinarith [he]
 rcases (sq_eq_sq_iff_eq_or_eq_neg.mp he2) with h | h
 · exact sq_eq_sq_iff_eq_or_eq_neg.mp h
 · have xx : 0 ≤ x^2 := sq_nonneg _
   have yy : 0 ≤ y^2 := sq_nonneg _
   have x0 : x = 0 := by nlinarith
   subst x
   norm_num at hx

noncomputable def dr : ℝ[X] := C 5 * X^4 - C 4
lemma drroot (x : ℝ) (hx : x ∈ (dr.rootSet ℝ)) : (5:ℝ)*x^4 - 4 = 0 := by
  have h := (Polynomial.mem_rootSet.1 hx).2
  simpa [dr, Polynomial.aeval_def] using h

lemma drcard : Fintype.card (dr.rootSet ℝ) ≤ 2 := by
 classical
 by_cases emp : (dr.rootSet ℝ).Nonempty
 · obtain ⟨a, ha⟩ := emp
   have sub : dr.rootSet ℝ ⊆ ({a, -a} : Set ℝ) := by
     intro x hx
     rcases root_four_pair (drroot x hx) (drroot a ha) with h|h
     · simp [h]
     · simp [h]
   -- ncard
   have nc := Set.ncard_le_ncard sub
   rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card'] at nc
   have r : ({a,-a} : Set ℝ).toFinset.card ≤ 2 := by
     classical
     have h := Finset.card_insert_le a ({-a} : Finset ℝ)
     simpa using h
   -- rootset fintype.card
   simpa using nc.trans r
 · have : dr.rootSet ℝ = ∅ := Set.not_nonempty_iff_eq_empty.mp emp
   simp [this]

noncomputable def ff : ℚ[X] := X^5 - C 4 * X + C 2
lemma ff_alt : ff = X^5 - (C 4 * X - C 2) := by dsimp [ff]; ring
lemma ds : (C (4:ℚ)*X-C 2).degree < (5:WithBot ℕ) := by compute_degree!
lemma ffdeg : ff.natDegree = 5 := by
 rw [ff_alt]
 apply natDegree_eq_of_degree_eq_some
 rw [degree_sub_eq_left_of_degree_lt]
 · simp
 · simpa using ds
lemma derivff : derivative ff = (C 5 * X^4 - C 4) := by
 dsimp [ff]
 simp [derivative_add, derivative_sub, derivative_pow]

/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem abel_ruffini (n : ℕ) (_hn : 1 ≤ n) :
    (∀ p : ℚ[X], p.natDegree = n → ∀ x : ℂ, aeval x p = 0 →
        x ∈ solvableByRad ℚ ℂ) ↔ n ≤ 4 :=
/-ResultProofBegin-/ by
  constructor
  · intro h
    by_contra hn4
    have hn5 : 5 ≤ n := by omega
    -- It remains to produce a nonsolvable quintic.  The padding argument below
    -- isolates precisely this missing base example.
    have bad5 : ∃ f : ℚ[X], f.natDegree = 5 ∧
        ∃ z : ℂ, aeval z f = 0 ∧ z ∉ solvableByRad ℚ ℂ := by
      classical
      -- we use the concrete Eisenstein polynomial X^5-4X+2.
      have hirr : Irreducible ff := by
        -- Eisenstein's criterion at the prime 2, first over the integers.
        -- The polynomial already is Eisenstein: all of its lower
        -- coefficients are even, and its constant coefficient is 2.
        let fz : ℤ[X] := X^5 - C 4 * X + C 2
        have fzdeg : fz.degree = (5 : WithBot ℕ) := by
          dsimp [fz]
          compute_degree!
        have fzm : fz.Monic := by
          dsimp [fz]
          have hq : ((- C (4:ℤ) * X + C 2) : ℤ[X]).degree <
              (5 : WithBot ℕ) := by
            compute_degree!
          have heq : (X^5 - (C (4:ℤ)) * X + C 2 : ℤ[X]) =
              X^5 + (- C (4:ℤ) * X + C 2) := by ring
          rw [heq]
          exact monic_X_pow_add hq
        have fzirr : Irreducible fz := by
          let I : Ideal ℤ := Ideal.span ({(2:ℤ)} : Set ℤ)
          have hI : I.IsPrime := by
            dsimp [I]
            exact (Ideal.span_singleton_prime
              (by norm_num : (2:ℤ) ≠ 0)).2 Int.prime_two
          have hleadI : fz.leadingCoeff ∉ I := by
            intro hm
            change fz.leadingCoeff ∈ Ideal.span ({(2:ℤ)} : Set ℤ) at hm
            rw [Ideal.mem_span_singleton, fzm.leadingCoeff] at hm
            norm_num at hm
          have hcoeffI : ∀ k : ℕ, (k : WithBot ℕ) < fz.degree →
              fz.coeff k ∈ I := by
            intro k hk
            rw [fzdeg] at hk
            have hk' : k < 5 := by exact_mod_cast hk
            interval_cases k <;>
              change fz.coeff _ ∈ Ideal.span ({(2:ℤ)} : Set ℤ) <;>
              rw [Ideal.mem_span_singleton] <;>
              norm_num [fz, coeff_add, coeff_sub, coeff_C_mul_X,
                coeff_X_pow, coeff_X, coeff_C]
          have hpos : (0 : WithBot ℕ) < fz.degree := by
            rw [fzdeg]
            decide
          have hconst : fz.coeff 0 ∉ I ^ 2 := by
            intro hm
            change fz.coeff 0 ∈ (Ideal.span ({(2:ℤ)} : Set ℤ)) ^ 2 at hm
            rw [Ideal.span_singleton_pow] at hm
            rw [Ideal.mem_span_singleton] at hm
            norm_num [fz, coeff_add, coeff_sub, coeff_C_mul_X,
              coeff_X_pow, coeff_C] at hm
          exact Polynomial.irreducible_of_eisenstein_criterion hI hleadI
            hcoeffI hpos hconst fzm.isPrimitive
        -- Gauss' lemma transports this to Q[X]; the map is our polynomial.
        have hmap : Polynomial.map (Int.castRingHom ℚ) fz = ff := by
          dsimp [fz, ff]
          simp [Polynomial.C_ofNat]
        have hmprim : fz.IsPrimitive := fzm.isPrimitive
        exact hmap ▸
          (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
            hmprim).1 fzirr
      have hcomplex : Fintype.card (ff.rootSet ℂ) = 5 := by
        classical
        -- `Fintype.card` of the subtype is best converted to `ncard`
        -- before rewriting the defining set (the rootSet instance is
        -- dependent on the set).  The underlying finset is the roots
        -- multiset with duplicates removed.
        calc
          Fintype.card (ff.rootSet ℂ) = (ff.rootSet ℂ).ncard := by
            rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
          _ = ((ff.aroots ℂ).toFinset : Finset ℂ).card := by
            rw [rootSet_def, Set.ncard_coe_finset]
          _ = (ff.aroots ℂ).card := by
            apply Multiset.toFinset_card_of_nodup
            simpa using
              (Polynomial.nodup_roots
                ((Polynomial.separable_map (algebraMap ℚ ℂ)).mpr hirr.separable))
          _ = 5 := by
            rw [← Polynomial.Splits.natDegree_eq_card_roots]
            · simpa [Polynomial.natDegree_map] using ffdeg
            · exact IsAlgClosed.splits _
      have hrealup : Fintype.card (ff.rootSet ℝ) ≤ 3 := by
        have hh := Polynomial.card_rootSet_le_derivative ff
        rw [derivff] at hh
        -- identify the derivative root set with the real-coefficient one.
        have heq : ((C 5 * X^4 - C 4) : ℚ[X]).rootSet ℝ = dr.rootSet ℝ := by
          classical
          have hq0 : (C (5:ℚ)* X^4 - C 4 : ℚ[X]) ≠ 0 := by
            intro hz
            have hcoef := congrArg (fun t : ℚ[X] => t.coeff 4) hz
            norm_num [coeff_sub, coeff_C_mul, coeff_X_pow, coeff_C] at hcoef
          have hr0 : dr ≠ 0 := by
            intro hz
            have hcoef := congrArg (fun t : ℝ[X] => t.coeff 4) hz
            norm_num [dr, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_C] at hcoef
          ext a
          constructor
          · intro ha
            obtain ⟨_, ha0⟩ := (Polynomial.mem_rootSet.mp ha)
            apply Polynomial.mem_rootSet.mpr
            refine ⟨hr0, ?_⟩
            simpa [dr, Polynomial.aeval_def] using ha0
          · intro ha
            obtain ⟨_, ha0⟩ := (Polynomial.mem_rootSet.mp ha)
            apply Polynomial.mem_rootSet.mpr
            refine ⟨hq0, ?_⟩
            simpa [dr, Polynomial.aeval_def] using ha0
        have hcard : Fintype.card (((C 5 * X^4 - C 4) : ℚ[X]).rootSet ℝ) =
            Fintype.card (dr.rootSet ℝ) := by
          calc
            Fintype.card (((C 5 * X^4 - C 4) : ℚ[X]).rootSet ℝ) =
                (((C 5 * X^4 - C 4) : ℚ[X]).rootSet ℝ).ncard := by
                  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
            _ = (dr.rootSet ℝ).ncard := by rw [heq]
            _ = Fintype.card (dr.rootSet ℝ) := by
                  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
        rw [hcard] at hh
        exact le_trans hh (by
          have hd := drcard
          omega : Fintype.card (dr.rootSet ℝ) + 1 ≤ 3)
      have rootI (a b : ℝ) (hab : a ≤ b)
          (ha : eval a (ff.map (algebraMap ℚ ℝ)) ≤ 0)
          (hb : 0 ≤ eval b (ff.map (algebraMap ℚ ℝ))) :
          ∃ x ∈ Set.Icc a b, aeval x ff = 0 := by
        have hi := intermediate_value_Icc hab (ff.map (algebraMap ℚ ℝ)).continuous.continuousOn
        have hz : (0:ℝ) ∈ Set.Icc (eval a (ff.map (algebraMap ℚ ℝ)))
             (eval b (ff.map (algebraMap ℚ ℝ))) := ⟨ha, hb⟩
        obtain ⟨x, hx, hx0⟩ := hi hz
        exact ⟨x, hx, by simpa [Polynomial.aeval_def] using hx0⟩
      obtain ⟨u, hu, hu0⟩ := rootI 1 2 (by norm_num) (by norm_num [ff]) (by norm_num [ff])
      obtain ⟨v, hv, hv0⟩ := rootI (-2) (-1) (by norm_num) (by norm_num [ff]) (by norm_num [ff])
      have huv : u ≠ v := by
        have h1 := hu.1
        have h2 := hv.2
        linarith
      have hreallo : 2 ≤ Fintype.card (ff.rootSet ℝ) := by
        have um : u ∈ ff.rootSet ℝ := mem_rootSet.mpr ⟨hirr.ne_zero, hu0⟩
        have vm : v ∈ ff.rootSet ℝ := mem_rootSet.mpr ⟨hirr.ne_zero, hv0⟩
        have sub : ({u,v} : Set ℝ) ⊆ ff.rootSet ℝ := by
          intro x hx; rcases hx with (rfl|hx)
          · exact um
          · have : x = v := by simpa using hx
            simpa [this] using vm
        have hc : ({u,v} : Set ℝ).ncard ≤ (ff.rootSet ℝ).ncard :=
          Set.ncard_le_ncard sub
        have pair : ({u,v} : Set ℝ).toFinset.card = 2 := by simp [huv]
        calc
          2 = ({u,v} : Set ℝ).ncard := by
            rw [Set.ncard_eq_toFinset_card', pair]
          _ ≤ (ff.rootSet ℝ).ncard := hc
          _ = Fintype.card (ff.rootSet ℝ) := by
            rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
      letI : Fact (ff.map (algebraMap ℚ ℂ)).Splits :=
        ⟨IsAlgClosed.splits _⟩
      have hbij : Function.Bijective (Polynomial.Gal.galActionHom ff ℂ) := by
        apply Polynomial.Gal.galActionHom_bijective_of_prime_degree' hirr
          (by simpa [ffdeg] using (show Nat.Prime 5 by decide))
        · omega
        · omega
      have hnsolv : ¬ IsSolvable ff.Gal := by
        intro hs
        letI : IsSolvable ff.Gal := hs
        letI : IsSolvable (Equiv.Perm (ff.rootSet ℂ)) :=
          solvable_of_surjective hbij.2
        let e : (ff.rootSet ℂ) ≃ Fin 5 := (Fintype.equivFin _).trans
          (Fin.castOrderIso hcomplex).toEquiv
        letI : IsSolvable (Equiv.Perm (Fin 5)) :=
          solvable_of_surjective (f := e.permCongrHom.toMonoidHom) e.permCongrHom.surjective
        exact Equiv.Perm.fin_5_not_solvable inferInstance
      by_contra all
      push_neg at all
      have every : ∀ x : ℂ, aeval x ff = 0 → x ∈ solvableByRad ℚ ℂ := by
        intro x hx
        exact all ff ffdeg x hx
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ ff (by
        exact ne_of_gt
          ((Polynomial.natDegree_pos_iff_degree_pos).mp (by
            rw [ffdeg]
            decide)))
      exact hnsolv (isSolvable_gal_of_irreducible (every z hz) hirr hz)
    obtain ⟨f, hf, z, hz, hznot⟩ := bad5
    have hf0 : f ≠ 0 := by
      intro hh
      subst f
      norm_num at hf
    let g : ℚ[X] := f * X^(n-5)
    have hpow0 : (X^(n-5) : ℚ[X]) ≠ 0 := pow_ne_zero _ X_ne_zero
    have hgdeg : g.natDegree = n := by
      dsimp [g]
      rw [Polynomial.natDegree_mul hf0 hpow0, hf, Polynomial.natDegree_X_pow]
      omega
    have hgz : aeval z g = 0 := by
      dsimp [g]
      rw [Polynomial.aeval_mul, hz]
      simp
    exact hznot (h g hgdeg z hgz)
  · intro hn4 p hp x hx
    have cases : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
    rcases cases with h1 | h2 | h3 | h4
    · exact test_linear (by simpa [h1] using hp) x hx
    · exact test_quad (by simpa [h2] using hp) x hx
    · exact test_cubic (by simpa [h3] using hp) x hx
    · exact test_quartic (by simpa [h4] using hp) x hx
/-ResultProofEnd-/
/-ResultEnd-/

end Submission
