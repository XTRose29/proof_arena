import Mathlib

namespace Submission

open Polynomial
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
noncomputable def cstar (n:ℕ) (p:ℂ[X]) : ℂ[X] := (p.map (starRingEnd ℂ)).reflect n

lemma circle_ne_zero (z:Circle) : (z:ℂ) ≠ 0 := by
  intro hz
  have h := z.norm_coe
  --simp ?
  rw [hz, norm_zero] at h
  norm_num at h

lemma circle_star_eq_inv (z:Circle) : starRingEnd ℂ (z:ℂ) = (z:ℂ)⁻¹ := by
  have hnorm : Complex.normSq (z:ℂ) = 1 := by
    -- sq_norm
    rw [← Complex.sq_norm]
    rw [z.norm_coe]
    norm_num
  -- inv_def
  rw [Complex.inv_def]
  -- goal conj = conj * ↑normsq⁻¹ order?
  rw [hnorm]
  norm_num

lemma eval_reflect_eq (n:ℕ) (p:ℂ[X]) (x:ℂ) (hx:x≠0) (hp:p.natDegree ≤ n) :
    (p.reflect n).eval x = x^n * p.eval (x⁻¹) := by
  letI : Invertible (x⁻¹) := invertibleOfNonzero (inv_ne_zero hx)
  have h := Polynomial.eval₂_reflect_mul_pow (RingHom.id ℂ) (x⁻¹) n p hp
  -- eval₂ id = eval
  -- #? simp
  -- ⅟ eq inv
  rw [invOf_eq_inv] at h
  -- ⅟ (x⁻¹) =? h becomes eval₂ id ((x⁻¹)⁻¹) (reflect) * (x⁻¹)^n =...
  -- simplify eval₂_at?
  -- simp at?
  -- draft
  have h' : (p.reflect n).eval x * (x⁻¹)^n = p.eval (x⁻¹) := by
    simpa using h
  have hmul : (x⁻¹)^n * x^n = (1:ℂ) := by
    rw [← mul_pow, inv_mul_cancel₀ hx, one_pow]
  calc
    _ = (p.reflect n).eval x * 1 := (mul_one _).symm
    _ = (p.reflect n).eval x * ((x⁻¹)^n * x^n) := by rw [hmul]
    _ = (p.reflect n).eval x * (x⁻¹)^n * x^n := by ring
    _ = p.eval (x⁻¹) * x^n := by rw [h']
    _ = _ := by ring

-- try cstar eval
lemma eval_cstar (n:ℕ) (p:ℂ[X]) (hp:p.natDegree ≤ n) (z:Circle) :
    (cstar n p).eval (z:ℂ) = (z:ℂ)^n * starRingEnd ℂ (p.eval (z:ℂ)) := by
  have hz : (z:ℂ) ≠ 0 := circle_ne_zero z
  have hdeg : (p.map (starRingEnd ℂ)).natDegree ≤ n :=
      le_trans (Polynomial.natDegree_map_le) hp
  rw [cstar]
  rw [eval_reflect_eq n (p.map (starRingEnd ℂ)) (z:ℂ) hz hdeg]
  -- need eval inverse
  -- eval_map
  rw [Polynomial.eval_map]
  -- eval₂ star ((z)⁻¹) p.
  rw [← circle_star_eq_inv z]
  -- now eval₂ star (star z) p = star (eval z p)
  -- eval₂_at_apply f z gives eval₂ f (f z) p = f (eval z p)
  rw [Polynomial.eval₂_at_apply]

-- norm relation final use!
lemma eval_cstar_mul (n:ℕ) (p:ℂ[X]) (hp:p.natDegree ≤ n) (z:Circle) :
    p.eval (z:ℂ) * (cstar n p).eval (z:ℂ) =
       (z:ℂ)^n * ((‖p.eval (z:ℂ)‖ ^ 2 : ℝ) : ℂ) := by
  rw [eval_cstar n p hp z]
  let a : ℂ := p.eval (z:ℂ)
  let x : ℂ := (z:ℂ)
  change a * (x^n * starRingEnd ℂ a) = x^n * ((‖a‖ ^ 2 : ℝ) : ℂ)
  calc
    _ = x^n * (a * starRingEnd ℂ a) := by ring
    _ = x^n * (Complex.normSq a : ℂ) := by rw [Complex.mul_conj]
    _ = _ := by rw [Complex.sq_norm]

lemma consequence (n:ℕ) (p q:ℂ[X]) (hp:p.natDegree ≤ n) (hq:q.natDegree ≤ n)
    (hfac : X^n - p * cstar n p = q * cstar n q) :
    ∀ z : Circle, ‖p.eval (z:ℂ)‖^2 + ‖q.eval (z:ℂ)‖^2 = (1:ℝ) := by
  intro z
  let x : ℂ := (z:ℂ)
  have hx : x ≠ 0 := circle_ne_zero z
  have h := congrArg (fun r : ℂ[X] => r.eval x) hfac
  -- simplify
  simp at h
  have hpz := eval_cstar_mul n p hp z
  have hqz := eval_cstar_mul n q hq z
  change x^n - p.eval x * (cstar n p).eval x = q.eval x * (cstar n q).eval x at h
  change p.eval x * (cstar n p).eval x = x^n * ((‖p.eval x‖ ^ 2 : ℝ) : ℂ) at hpz
  change q.eval x * (cstar n q).eval x = x^n * ((‖q.eval x‖ ^ 2 : ℝ) : ℂ) at hqz
  rw [hpz, hqz] at h
  have hxpow : x ^ n ≠ 0 := pow_ne_zero _ hx
  have hab : (((‖p.eval x‖ ^ 2 : ℝ)) : ℂ) +
               (((‖q.eval x‖ ^ 2 : ℝ)) : ℂ) = 1 := by
    apply (mul_left_cancel₀ hxpow)
    calc
      x^n * ((((‖p.eval x‖ ^ 2 : ℝ)) : ℂ) +
              (((‖q.eval x‖ ^ 2 : ℝ)) : ℂ)) =
          x^n * (((‖p.eval x‖ ^ 2 : ℝ)) : ℂ) +
          x^n * (((‖q.eval x‖ ^ 2 : ℝ)) : ℂ) := by ring
      _ = x^n := by linear_combination -h
      _ = x^n * 1 := by ring
  -- remove the local notation for the point and reflect the real embedding
  change ‖p.eval x‖^2 + ‖q.eval x‖^2 = (1:ℝ)
  exact_mod_cast hab

lemma deg0fac (p:ℂ[X]) (hp:p.natDegree ≤ 0)
 (hb:∀ z:Circle, ‖p.eval (z:ℂ)‖ ≤ 1) :
 ∃ q:ℂ[X], q.natDegree ≤ 0 ∧ X^0 - p * cstar 0 p = q * cstar 0 q := by
  classical
  let a : ℂ := p.coeff 0
  have eqp : p = C a := Polynomial.eq_C_of_natDegree_le_zero hp
  have ha : ‖a‖ ≤ (1:ℝ) := by
    have h := hb (1 : Circle)
    rw [eqp] at h
    simpa using h
  have hnon : 0 ≤ (1:ℝ) - ‖a‖^2 := by
    nlinarith [norm_nonneg a]
  let t : ℝ := Real.sqrt (1-‖a‖^2)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht : t^2 = (1:ℝ)-‖a‖^2 := by
    dsimp [t]
    exact Real.sq_sqrt hnon
  refine ⟨C (t:ℂ), ?_, ?_⟩
  · simp
  · -- polynomial identity constants
    rw [eqp]
    -- reduce star and casts
    simp [cstar]
    have hc : (1:ℂ) - a * starRingEnd ℂ a = (t:ℂ)*(t:ℂ) := by
      rw [Complex.mul_conj]
      -- express real square root identity and cast
      have hh : ((1:ℝ) - ‖a‖^2) = t*t := by nlinarith [ht]
      have hh' : (1:ℝ) - Complex.normSq a = t*t := by
        rw [← Complex.sq_norm]
        exact hh
      exact_mod_cast hh'
    -- functoriality of constants
    simpa using congrArg (fun u : ℂ => (Polynomial.C u)) hc


lemma cstar_invol (n:ℕ) (p:ℂ[X]) : cstar n (cstar n p) = p := by
  ext i
  simp [cstar]

lemma cstar_sub (n:ℕ) (p q:ℂ[X]) : cstar n (p-q)=cstar n p - cstar n q := by
  -- use neg etc
  ext i
  simp [cstar]

lemma cstar_mul (n m:ℕ) (p q:ℂ[X]) (hp:p.natDegree ≤ n) (hq:q.natDegree ≤ m) :
    cstar (n+m) (p*q) = cstar n p * cstar m q := by
  have hp' : (p.map (starRingEnd ℂ)).natDegree ≤ n :=
    le_trans Polynomial.natDegree_map_le hp
  have hq' : (q.map (starRingEnd ℂ)).natDegree ≤ m :=
    le_trans Polynomial.natDegree_map_le hq
  unfold cstar
  rw [Polynomial.map_mul]
  exact Polynomial.reflect_mul _ _ hp' hq'
lemma cstar_natDegree_le (n:ℕ) (p:ℂ[X]) (hp:p.natDegree ≤ n) :
    (cstar n p).natDegree ≤ n := by
  unfold cstar
  have h := (Polynomial.natDegree_reflect_le (N:=n) (p:=p.map (starRingEnd ℂ)))
  -- ≤ max n degmap
  exact h.trans_eq (max_eq_left (le_trans Polynomial.natDegree_map_le hp))

lemma cstar_X_mid (n:ℕ) : cstar (n+n) (X^n) = (X^n : ℂ[X]) := by
  simp [cstar, Polynomial.reflect_monomial, Polynomial.revAt_le (Nat.le_add_left n n)]
  -- maybe arithmetic
lemma cstar_F (n:ℕ) (p:ℂ[X]) (hp:p.natDegree ≤ n) :
    cstar (n+n) (X^n - p * cstar n p) = X^n - p * cstar n p := by
  rw [cstar_sub]
  rw [cstar_X_mid]
  rw [cstar_mul n n p (cstar n p) hp (cstar_natDegree_le n p hp)]
  rw [cstar_invol]
  ring
lemma eval_F (n:ℕ) (p:ℂ[X]) (hp:p.natDegree ≤ n) (z:Circle) :
    (X^n - p*cstar n p).eval (z:ℂ) =
      (z:ℂ)^n * (((1 - ‖p.eval (z:ℂ)‖^2 : ℝ)) : ℂ) := by
  let x : ℂ := (z:ℂ)
  have hh := eval_cstar_mul n p hp z
  change p.eval x * (cstar n p).eval x = x^n * ((‖p.eval x‖^2 : ℝ) : ℂ) at hh
  change (X^n - p*cstar n p).eval x = _
  simp
  change x^n - p.eval x * (cstar n p).eval x =
      x^n * (1 - (‖p.eval x‖:ℂ)^2)
  rw [hh]
  push_cast
  ring
lemma nonneg_circle_F (n:ℕ) (p:ℂ[X]) (hp:p.natDegree ≤ n)
 (hb:∀ z:Circle, ‖p.eval (z:ℂ)‖ ≤ 1) (z:Circle) :
   0 ≤ (1:ℝ)-‖p.eval (z:ℂ)‖^2 := by
  have h := hb z
  have hn := norm_nonneg (p.eval (z:ℂ))
  nlinarith
lemma deg_F (n:ℕ) (p:ℂ[X]) (hp:p.natDegree ≤ n) :
    (X^n - p*cstar n p).natDegree ≤ n+n := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply (max_le_iff).2
  constructor
  · simp
  · calc
     (p*cstar n p).natDegree ≤ p.natDegree + (cstar n p).natDegree := Polynomial.natDegree_mul_le
     _ ≤ n+n := Nat.add_le_add hp (cstar_natDegree_le n p hp)

lemma eval_cstar_general (n:ℕ) (p:ℂ[X]) (hp:p.natDegree ≤ n)
 (x:ℂ) (hx:x≠0) :
 (cstar n p).eval x = x^n * starRingEnd ℂ (p.eval ((starRingEnd ℂ x)⁻¹)) := by
  have hd : (p.map (starRingEnd ℂ)).natDegree ≤ n :=
    (Polynomial.natDegree_map_le).trans hp
  unfold cstar
  rw [eval_reflect_eq n (p.map (starRingEnd ℂ)) x hx hd]
  rw [Polynomial.eval_map]
  have hux : x⁻¹ = starRingEnd ℂ ((starRingEnd ℂ x)⁻¹) := by
    -- conj of conj inverse
    simp
  -- want rw hux and eval₂_at
  rw [hux, Polynomial.eval₂_at_apply]

lemma isRoot_symm (n:ℕ) (f:ℂ[X]) (hdeg:f.natDegree ≤ n+n)
    (hsym:cstar (n+n) f = f) (x:ℂ) (hx:x≠0) :
    f.IsRoot x ↔ f.IsRoot ((starRingEnd ℂ x)⁻¹) := by
  rw [Polynomial.IsRoot.def, Polynomial.IsRoot.def]
  have h := eval_cstar_general (n+n) f hdeg x hx
  rw [hsym] at h
  rw [h]
  rw [mul_eq_zero]
  simp [hx, map_eq_zero_iff]


lemma coeff_cstar (n:ℕ) (p:ℂ[X]) (i:ℕ) :
 (cstar n p).coeff i = starRingEnd ℂ (p.coeff (Polynomial.revAt n i)) := by
 simp [cstar]

lemma half_le_degree_selfstar (n:ℕ) (f:ℂ[X]) (hf:f≠0)
 (hdeg:f.natDegree ≤ n+n) (hsym:cstar (n+n) f = f) : n ≤ f.natDegree := by
  let d := f.natDegree
  have hdlead : f.coeff d ≠ 0 := by
    exact Polynomial.leadingCoeff_ne_zero.mpr hf
  have hdeg' : d ≤ n+n := hdeg
  let j := Polynomial.revAt (n+n) d
  have hj : j = n+n-d := Polynomial.revAt_le hdeg'
  have hcoeff : f.coeff j ≠ 0 := by
    have hh : (cstar (n+n) f).coeff j = starRingEnd ℂ (f.coeff d) := by
      rw [coeff_cstar]
      dsimp [j]
      rw [Polynomial.revAt_invol]
    rw [hsym] at hh
    -- hh : coeff f j = star...
    rw [hh]
    simp [hdlead]
  have hjle : j ≤ d := by
    by_contra hnot
    have hz := Polynomial.coeff_eq_zero_of_natDegree_lt (p:=f) (Nat.lt_of_not_ge hnot)
    exact hcoeff hz
  rw [hj] at hjle
  -- n+n-d ≤ d and d≤n+n implies n≤d
  omega

lemma trailing_selfstar (n:ℕ) (f:ℂ[X]) (hf:f≠0)
 (hdeg:f.natDegree ≤ n+n) (hsym:cstar (n+n) f = f) :
 f.natTrailingDegree = n+n - f.natDegree := by
  let d := f.natDegree
  have hd : d ≤ n+n := hdeg
  let j : ℕ := n+n-d
  have hjd : Polynomial.revAt (n+n) d = j :=
    Polynomial.revAt_le hd
  have hcj : f.coeff j ≠ 0 := by
    have hco : (cstar (n+n) f).coeff (Polynomial.revAt (n+n) d) =
        starRingEnd ℂ (f.coeff d) := by
      rw [coeff_cstar, Polynomial.revAt_invol]
    rw [hsym, hjd] at hco
    rw [hco]
    have hlead : f.coeff d ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr hf
    simp [hlead]
  have hz : ∀ m < j, f.coeff m = 0 := by
    intro m hm
    by_contra hmc
    have hmle : m ≤ n+n := by
      omega
    have hzbig : f.coeff (Polynomial.revAt (n+n) m) = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [Polynomial.revAt_le hmle]
      omega
    have hh : (cstar (n+n) f).coeff (Polynomial.revAt (n+n) m) =
        starRingEnd ℂ (f.coeff m) := by
      rw [coeff_cstar, Polynomial.revAt_invol]
    rw [hsym, hzbig] at hh
    have hh' : starRingEnd ℂ (f.coeff m) = 0 := hh.symm
    have hh'' : f.coeff m = 0 := by simpa using hh'
    exact hmc hh'' 
  have hlo : j ≤ f.natTrailingDegree :=
    Polynomial.le_natTrailingDegree hf hz
  have hhi : f.natTrailingDegree ≤ j := by
    apply Polynomial.natTrailingDegree_le_of_ne_zero
    exact hcj
  exact le_antisymm hhi hlo


open Polynomial Filter Set
lemma even_of_limit_nonneg {m : ℕ} {B : ℝ → ℝ} {b : ℝ}
    (hb : Tendsto B (nhds 0) (nhds b))
    (hb0 : b ≠ 0)
    (hpos : ∀ t : ℝ, 0 ≤ t^m * B t) : Even m := by
  by_contra he
  have ho : Odd m := Nat.not_even_iff_odd.1 he
  have eps : 0 < |b| := abs_pos.mpr hb0
  obtain ⟨δ, hδ, hclose⟩ := (Metric.tendsto_nhds_nhds.1 hb) |b| eps
  by_cases bp : 0 < b
  · let t : ℝ := - δ/2
    have ht : t < 0 := by dsimp [t]; linarith
    have htdist : dist t (0:ℝ) < δ := by
      rw [Real.dist_eq]
      dsimp [t]
      rw [abs_of_neg]
      · linarith
      · linarith
    have hBclose := hclose htdist
    rw [Real.dist_eq, abs_lt] at hBclose
    have hBt : 0 < B t := by
      have habs : |b| = b := abs_of_pos bp
      rw [habs] at hBclose
      linarith
    have hpow : t^m < 0 := ho.pow_neg ht
    have := hpos t
    exact (not_le_of_gt (mul_neg_of_neg_of_pos hpow hBt)) this
  · have bn : b < 0 := lt_of_le_of_ne (le_of_not_gt bp) hb0
    let t : ℝ := δ/2
    have ht : 0 < t := by dsimp [t]; linarith
    have htdist : dist t (0:ℝ) < δ := by
      rw [Real.dist_eq]
      dsimp [t]
      rw [abs_of_pos]
      · linarith
      · linarith
    have hBclose := hclose htdist
    rw [Real.dist_eq, abs_lt] at hBclose
    have hBt : B t < 0 := by
      have habs : |b| = -b := abs_of_neg bn
      rw [habs] at hBclose
      linarith
    have hpow : 0 < t^m := pow_pos ht _
    have := hpos t
    exact (not_le_of_gt (mul_neg_of_pos_of_neg hpow hBt)) this

-- denominator
lemma den_ne (t:ℝ) : (1 - (t:ℂ)*Complex.I) ≠ 0 := by
  intro h
  have hh := congrArg Complex.re h
  norm_num [Complex.sub_re, Complex.mul_re] at hh
-- norms equality
lemma norm_eq_den (t:ℝ) : ‖(1 + (t:ℂ)*Complex.I)‖ = ‖(1 - (t:ℂ)*Complex.I)‖ := by
  have h : Complex.normSq (1 + (t:ℂ)*Complex.I) =
     Complex.normSq (1 - (t:ℂ)*Complex.I) := by
       simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
          Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  have h2 : ‖(1 + (t:ℂ)*Complex.I)‖^2 = ‖(1 - (t:ℂ)*Complex.I)‖^2 := by
    simpa [Complex.sq_norm] using h -- sq_norm orientation
  nlinarith [norm_nonneg (1+(t:ℂ)*Complex.I), norm_nonneg (1-(t:ℂ)*Complex.I)]
lemma unorm (t:ℝ) : ‖(1 + (t:ℂ)*Complex.I)/(1 - (t:ℂ)*Complex.I)‖ = 1 := by
  rw [norm_div, norm_eq_den t]
  apply div_self
  exact (norm_ne_zero_iff.mpr (den_ne t))
-- build w
noncomputable def path (z:Circle) (t:ℝ) : Circle :=
 ⟨ (z:ℂ) * ((1 + (t:ℂ)*Complex.I)/(1 - (t:ℂ)*Complex.I)), by
   -- membership
   change _ ∈ Metric.sphere (0:ℂ) 1
   rw [mem_sphere_zero_iff_norm]
   change ‖(z:ℂ) * ((1 + (t:ℂ)*Complex.I)/(1 - (t:ℂ)*Complex.I))‖ = (1:ℝ)
   rw [norm_mul, z.norm_coe, unorm]; norm_num ⟩
lemma coepath (z:Circle) (t:ℝ) : (path z t:ℂ) =
 (z:ℂ) * ((1 + (t:ℂ)*Complex.I)/(1 - (t:ℂ)*Complex.I)) := rfl
noncomputable def L (a:ℂ) (t:ℝ) : ℂ := a * ( (2:ℂ)*Complex.I / (1 - (t:ℂ)*Complex.I))
lemma diffpath (z:Circle) (t:ℝ) : (path z t:ℂ) - (z:ℂ) = (t:ℂ) * L (z:ℂ) t := by
 rw [coepath]
 dsimp [L]
 have hh := den_ne t
 field_simp
 ring
lemma L_zero (a:ℂ) : L a 0 = a * (2*Complex.I) := by
 dsimp [L]
 norm_num
lemma L_ne (a:ℂ) (ha:a≠0) (t:ℝ) : L a t ≠ 0 := by
 dsimp [L]
 apply mul_ne_zero ha
 exact div_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (den_ne t)
-- continuity
lemma cont_w (z:Circle) : Continuous (fun t:ℝ => (path z t:ℂ)) := by
  -- expand and use div
  change Continuous (fun t:ℝ => (z:ℂ) * ((1 + (t:ℂ)*Complex.I)/(1 - (t:ℂ)*Complex.I)))
  have hnum : Continuous (fun t:ℝ => (1:ℂ) + (t:ℂ)*Complex.I) := by fun_prop
  have hden : Continuous (fun t:ℝ => (1:ℂ) - (t:ℂ)*Complex.I) := by fun_prop
  exact continuous_const.mul (hnum.div hden (fun t => den_ne t))
lemma even_root_circle (n:ℕ) (f:ℂ[X]) (hf:f≠0)
 (hval : ∀ u:Circle, ∃ r:ℝ, 0 ≤ r ∧ f.eval (u:ℂ) = (u:ℂ)^n * (r:ℂ))
 (z:Circle) : Even (f.rootMultiplicity (z:ℂ)) := by
 let a : ℂ := (z:ℂ)
 let m : ℕ := f.rootMultiplicity a
 let g : ℂ[X] := f /ₘ (X-C a)^m
 have hga : g.eval a ≠ 0 := by
   dsimp [g,m]
   exact Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero a hf
 have hfact : (X-C a)^m * g = f := by
   dsimp [g,m]
   exact Polynomial.pow_mul_divByMonic_rootMultiplicity_eq f a
 let bc : ℝ → ℂ := fun t => ((path z t:ℂ)⁻¹)^n * (L a t)^m * g.eval (path z t:ℂ)
 have hbc0 : bc 0 ≠ 0 := by
   dsimp [bc]
   -- path 0 coe a
   have hw0 : (path z 0:ℂ) = a := by simp [coepath, a]
   rw [hw0]
   exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (inv_ne_zero (by
      dsimp [a]; intro h; have hh:= z.norm_coe; rw [h,norm_zero] at hh; norm_num at hh)))
      (pow_ne_zero _ (L_ne a (by
        dsimp [a]; intro h; have hh:= z.norm_coe; rw [h,norm_zero] at hh; norm_num at hh) 0))) hga
 have hcont : Continuous bc := by
   dsimp [bc]
   have hw := cont_w z
   have ha : a ≠ 0 := by
     dsimp [a]; intro h; have hh:= z.norm_coe; rw [h,norm_zero] at hh; norm_num at hh
   have hwne : ∀ t:ℝ, (path z t:ℂ) ≠ 0 := fun t => by
     have hh := (path z t).norm_coe
     intro h; rw [h,norm_zero] at hh; norm_num at hh
   have hL : Continuous (fun t:ℝ => L a t) := by
     dsimp [L]
     have hd : Continuous (fun t:ℝ => (1:ℂ) - (t:ℂ)*Complex.I) := by fun_prop
     have hc : Continuous (fun t:ℝ => (2:ℂ)*Complex.I) := continuous_const
     exact continuous_const.mul (hc.div hd (fun t => den_ne t))
   exact ((hw.inv₀ hwne).pow n).mul (hL.pow m) |>.mul
     ((Polynomial.continuous_eval₂ g (RingHom.id ℂ)).comp hw)
 have hreal : ∀ t:ℝ, 0 ≤ (t^m) * (bc t).re := by
   intro t
   obtain ⟨r, hr, heqr⟩ := hval (path z t)
   have hwne : (path z t:ℂ) ≠ 0 := by
     intro h; have hh := (path z t).norm_coe
     rw [h,norm_zero] at hh; norm_num at hh
   have hev : f.eval (path z t:ℂ) = ((path z t:ℂ) - a)^m * g.eval (path z t:ℂ) := by
     rw [← hfact]
     simp
   have hR : (((path z t:ℂ)⁻¹)^n * f.eval (path z t:ℂ)) = (r:ℂ) := by
     rw [heqr]
     calc
       (↑(path z t))⁻¹ ^ n * (↑(path z t) ^ n * (r:ℂ)) =
          ((↑(path z t))⁻¹ ^ n * ↑(path z t)^n) * (r:ℂ) := by ring
       _ = (r:ℂ) := by rw [← mul_pow, inv_mul_cancel₀ hwne, one_pow, one_mul]
   have hB : ((r:ℂ)) = ((t:ℂ)^m) * bc t := by
     rw [← hR, hev, diffpath]
     dsimp [bc]
     push_cast
     -- rearrange, cancel w inverse product
     have hi : ((path z t:ℂ)⁻¹)^n * (path z t:ℂ)^n = 1 := by
       rw [← mul_pow, inv_mul_cancel₀ hwne, one_pow]
     -- diff gave (t:ℂ)* L, pow_mul
     rw [mul_pow]
     --? 
     -- simplify using no w factor? wait R no w factor after hev, hfact! same both sides no w cancel needed
     ring
   have hc : ((t:ℂ)^m) = ((t^m:ℝ):ℂ) := by norm_cast
   have hB' : (r:ℂ) = ((t^m:ℝ):ℂ) * bc t := by
     calc (r:ℂ) = ((t:ℂ)^m) * bc t := hB
          _ = _ := by rw [hc]
   have hre : r = t^m * (bc t).re := by
     calc
       r = (r:ℂ).re := by simp
       _ = (((t^m:ℝ):ℂ) * bc t).re := congrArg Complex.re hB'
       _ = _ := by rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring

   nlinarith
 have even_aux : ∀ {m:ℕ} {B:ℝ→ℝ} {b:ℝ},
    Tendsto B (nhds 0) (nhds b) → b ≠ 0 →
    (∀ t:ℝ, 0 ≤ t^m * B t) → Even m := by
      intro m B b hb hb0 hp
      exact even_of_limit_nonneg hb hb0 hp

 have him : ∀ t:ℝ, t ≠ 0 → (bc t).im = 0 := by
   intro t ht
   obtain ⟨r, hr, heqr⟩ := hval (path z t)
   have hwne : (path z t:ℂ) ≠ 0 := by
     intro h; have hh := (path z t).norm_coe; rw [h,norm_zero] at hh; norm_num at hh
   have hev : f.eval (path z t:ℂ) = ((path z t:ℂ) - a)^m * g.eval (path z t:ℂ) := by
     rw [← hfact]; simp
   have hR : (((path z t:ℂ)⁻¹)^n * f.eval (path z t:ℂ)) = (r:ℂ) := by
     rw [heqr]
     calc
       (↑(path z t))⁻¹ ^ n * (↑(path z t) ^ n * (r:ℂ)) =
         ((↑(path z t))⁻¹ ^ n * ↑(path z t)^n) * (r:ℂ) := by ring
       _ = (r:ℂ) := by rw [← mul_pow, inv_mul_cancel₀ hwne, one_pow, one_mul]
   have hB : (r:ℂ) = ((t:ℂ)^m) * bc t := by
     rw [← hR, hev, diffpath]
     dsimp [bc]
     rw [mul_pow]
     ring
   have hc : ((t:ℂ)^m) = ((t^m:ℝ):ℂ) := by norm_cast
   have hB' : (r:ℂ) = ((t^m:ℝ):ℂ) * bc t := by rw [← hc]; exact hB
   have himul : 0 = t^m * (bc t).im := by
     calc
       0 = (r:ℂ).im := by simp
       _ = (((t^m:ℝ):ℂ) * bc t).im := congrArg Complex.im hB'
       _ = _ := by rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring
   have htn : t^m ≠ 0 := pow_ne_zero _ ht
   exact (mul_eq_zero.mp himul.symm |>.resolve_left htn)
 have himfun : (fun t:ℝ => (bc t).im) = (fun _ => (0:ℝ)) := by
   apply Continuous.ext_on (dense_compl_singleton (0:ℝ)) (Complex.continuous_im.comp hcont) continuous_const
   intro t ht
   have ht' : t ≠ 0 := by simpa using ht
   exact him t ht'
 have hbim0 : (bc 0).im = 0 := congrFun himfun 0
 have hbre0 : (bc 0).re ≠ 0 := by
   intro h
   have hz0 : bc 0 = 0 := Complex.ext h hbim0
   exact hbc0 hz0
 have htend : Tendsto (fun t:ℝ => (bc t).re) (nhds 0) (nhds ((bc 0).re)) :=
    (Complex.continuous_re.comp hcont).continuousAt
 have hm : Even m := even_aux htend hbre0 hreal
 exact hm



lemma cstar_linear (x:ℂ) (hx:x≠0) :
 cstar 1 (X - C x) = C (-(starRingEnd ℂ x)) * (X - C ((starRingEnd ℂ x)⁻¹)) := by
  -- try
  unfold cstar
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  -- reflect term not linear need use sub? reflect_sub? simp?
  ext i
  by_cases hi0 : i = 0
  · subst i
    --simp?
    simp [Polynomial.coeff_reflect, Polynomial.revAt, hx]
  · have hi : 0 < i := Nat.pos_of_ne_zero hi0
    by_cases hi1 : i = 1
    · subst i
      simp [Polynomial.coeff_reflect, Polynomial.revAt, Polynomial.coeff_one, Polynomial.coeff_C]
    · have hi2 : 2 ≤ i := by omega
      -- coeff linear zero
      have hrev : Polynomial.revAt 1 i = i := by
        simp [Polynomial.revAt, show ¬ i ≤ 1 by omega]
      rw [Polynomial.coeff_reflect, hrev]
      -- simp coeff
      --
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_sub, Polynomial.coeff_C, Polynomial.coeff_X, hi0, hi1, show (1:ℕ) ≠ i by omega]
lemma cstar_pow_linear (x:ℂ) (hx:x≠0) : ∀ k:ℕ,
  cstar k ((X-C x)^k) = (C (-(starRingEnd ℂ x)))^k * (X-C ((starRingEnd ℂ x)⁻¹))^k := by
  intro k
  induction k with
  | zero => simp [cstar]
  | succ k ih =>
    calc
      cstar (k+1) ((X-C x)^(k+1)) =
          cstar (k+1) ((X-C x)^k * (X-C x)) := by rw [pow_succ]
      _ = cstar k ((X-C x)^k) * cstar 1 (X-C x) := by
          rw [cstar_mul k 1]
          · rw [(Polynomial.monic_X_sub_C x).natDegree_pow, Polynomial.natDegree_X_sub_C]; simp
          · rw [Polynomial.natDegree_X_sub_C]
      _ = (C (-(starRingEnd ℂ x)))^(k+1) * (X-C ((starRingEnd ℂ x)⁻¹))^(k+1) := by
          rw [ih, cstar_linear x hx]
          ring
lemma cstar_dvd_transfer (N:ℕ) (f:ℂ[X]) (hf:f≠0) (hdeg:f.natDegree ≤ N)
 (hsym:cstar N f = f) (x:ℂ) (hx:x≠0) (k:ℕ)
 (hk : (X-C x)^k ∣ f) :
 (X-C ((starRingEnd ℂ x)⁻¹))^k ∣ f := by
  rcases hk with ⟨g, hg⟩
  -- hg ?
  -- trace_state
  have hpkdeg : ((X-C x)^k : ℂ[X]).natDegree = k := by
    rw [(Polynomial.monic_X_sub_C x).natDegree_pow, Polynomial.natDegree_X_sub_C]
    simp
  have hpkzero : ((X-C x)^k : ℂ[X]) ≠ 0 := by
    exact pow_ne_zero _ (by exact Polynomial.X_sub_C_ne_zero x)
  have hgzero : g ≠ 0 := by
    intro hgz
    simp [hgz] at hg
    exact hf hg
  have hgfdeg : k + g.natDegree = f.natDegree := by
    rw [← hpkdeg, ← Polynomial.natDegree_mul hpkzero hgzero]
    rw [hg]
  have hgle : g.natDegree ≤ N-k := by
    omega
  -- transform
  have hh := congrArg (cstar N) hg
  -- use multiplicative splitting with k + (N-k)
  have hkN : k ≤ N := by omega -- since hdeg etc hgfdeg
  have hsum : k + (N-k) = N := Nat.add_sub_of_le hkN
  have htrans : cstar N (((X-C x)^k) * g) =
      cstar k ((X-C x)^k) * cstar (N-k) g := by
    rw [← cstar_mul k (N-k) ((X-C x)^k) g]
    · rw [hsum]
    · rw [hpkdeg]
    · exact hgle
  have heq : f = cstar k ((X-C x)^k) * cstar (N-k) g := by
    calc
      f = cstar N f := hsym.symm
      _ = cstar N (((X-C x)^k)*g) := congrArg (cstar N) hg
      _ = _ := htrans
  rw [cstar_pow_linear x hx k] at heq
  -- heq f = C^k * A^k * cstar ... ; produce dvd
  refine ⟨ (C (-(starRingEnd ℂ x)))^k * cstar (N-k) g, ?_ ⟩
  -- orientation target f =? goal
  -- trace
  calc
    f = (C (-(starRingEnd ℂ x)))^k * (X-C ((starRingEnd ℂ x)⁻¹))^k * cstar (N-k) g := heq
    _ = _ := by ring
lemma rootMultiplicity_selfstar (N:ℕ) (f:ℂ[X]) (hf:f≠0) (hdeg:f.natDegree ≤ N)
 (hsym:cstar N f = f) (x:ℂ) (hx:x≠0) :
 f.rootMultiplicity x = f.rootMultiplicity ((starRingEnd ℂ x)⁻¹) := by
  let y : ℂ := (starRingEnd ℂ x)⁻¹
  have hy : y ≠ 0 := by dsimp [y]; simp [hx]
  have hyy : (starRingEnd ℂ y)⁻¹ = x := by
    dsimp [y]
    simp [hx]
  change f.rootMultiplicity x = f.rootMultiplicity y
  apply le_antisymm
  · rw [Polynomial.le_rootMultiplicity_iff hf]
    exact cstar_dvd_transfer N f hf hdeg hsym x hx
      (f.rootMultiplicity x) ((Polynomial.le_rootMultiplicity_iff hf).1 (le_refl (f.rootMultiplicity x)))
  · rw [Polynomial.le_rootMultiplicity_iff hf]
    rw [← hyy]
    apply cstar_dvd_transfer N f hf hdeg hsym y hy
      (f.rootMultiplicity y)
    exact ((Polynomial.le_rootMultiplicity_iff hf).1 (le_refl (f.rootMultiplicity y)))


-- The involution of a non-zero complex zero across the unit circle.
noncomputable def tau (x : ℂ) : ℂ := (starRingEnd ℂ x)⁻¹
lemma tau_tau (x : ℂ) : tau (tau x) = x := by
  simp [tau]
lemma tau_inj : Function.Injective tau := by
  intro x y h
  calc
    x = tau (tau x) := (tau_tau x).symm
    _ = tau (tau y) := congrArg tau h
    _ = y := tau_tau y
lemma tau_zero : tau 0 = 0 := by simp [tau]
lemma tau_ne_zero {x : ℂ} (hx : x ≠ 0) : tau x ≠ 0 := by
  simp [tau, hx]
lemma norm_tau (x : ℂ) : ‖tau x‖ = ‖x‖⁻¹ := by
  simp [tau]
lemma tau_of_norm_one {x : ℂ} (hx : ‖x‖ = (1:ℝ)) : tau x = x := by
  have hsq : Complex.normSq x = 1 := by
    rw [← Complex.sq_norm, hx]
    norm_num
  -- inverse of a conjugate, when the norm square is one
  rw [tau, Complex.inv_def]
  -- normSq (conj x) = normSq x
  rw [Complex.normSq_conj]
  rw [hsq]
  norm_num

-- A multiset product of the monic linear factors.
noncomputable def linprod (s : Multiset ℂ) : ℂ[X] :=
  (s.map (fun x : ℂ => X - C x)).prod
lemma linprod_add (s t : Multiset ℂ) : linprod (s+t) = linprod s * linprod t := by
  simp [linprod, Multiset.map_add, Multiset.prod_add]
lemma linprod_zero_repl (k : ℕ) : linprod (Multiset.replicate k (0:ℂ)) = (X:ℂ[X])^k := by
  induction k with
  | zero => simp [linprod]
  | succ k ih =>
      rw [Multiset.replicate_succ]
      rw [show (0:ℂ) ::ₘ Multiset.replicate k 0 = ((0:ℂ)::ₘ 0) + Multiset.replicate k 0 by simp,
          linprod_add, ih]
      simp [linprod, pow_succ, mul_comm]
lemma linprod_monic (s : Multiset ℂ) : (linprod s).Monic := by
  induction s using Multiset.induction_on with
  | empty => simp [linprod]
  | @cons x s ih =>
      rw [show x ::ₘ s = (x ::ₘ 0) + s by simp, linprod_add]
      simpa [linprod] using (Polynomial.monic_X_sub_C x).mul ih
lemma natDegree_linprod (s : Multiset ℂ) : (linprod s).natDegree = s.card := by
  induction s using Multiset.induction_on with
  | empty => simp [linprod]
  | @cons x s ih =>
      rw [show x ::ₘ s = (x ::ₘ 0) + s by simp, linprod_add]
      have he1 : linprod (x ::ₘ (0:Multiset ℂ)) = (X - C x : ℂ[X]) := by simp [linprod]
      rw [he1, (Polynomial.monic_X_sub_C x).natDegree_mul (linprod_monic s), ih,
          Polynomial.natDegree_X_sub_C]
      simp; omega
lemma coeff0_linprod_ne (s : Multiset ℂ) (hs : ∀ x ∈ s, x ≠ (0:ℂ)) :
    (linprod s).coeff 0 ≠ 0 := by
  -- use the multiplicative formula for evaluation at zero
  rw [Polynomial.coeff_zero_eq_eval_zero, linprod, Polynomial.eval_multiset_prod]
  -- every factor at zero is `-x`
  simp only [Multiset.map_map]
  have hall : ∀ u ∈ (s.map (fun x : ℂ => Polynomial.X - Polynomial.C x)).map
       (Polynomial.eval (0:ℂ)), u ≠ 0 := by
    intro u hu
    rcases Multiset.mem_map.1 hu with ⟨p, hp, rfl⟩
    rcases Multiset.mem_map.1 hp with ⟨x, hx, rfl⟩
    simp [hs x hx]
  apply Multiset.prod_ne_zero
  intro h0
  exact (hall 0 (by simpa [Multiset.map_map] using h0)) rfl

-- reflecting a product of non-zero linear factors
lemma cstar_linprod (s : Multiset ℂ) (hs : ∀ x ∈ s, x ≠ (0:ℂ)) :
    cstar s.card (linprod s) =
      C ((s.map (fun x : ℂ => -(starRingEnd ℂ x))).prod) *
        linprod (s.map tau) := by
  induction s using Multiset.induction_on with
  | empty => simp [linprod, cstar]
  | @cons x s ih =>
      have hx : x ≠ (0:ℂ) := hs x (by simp)
      have hs' : ∀ y ∈ s, y ≠ (0:ℂ) := by intro y hy; exact hs y (by simp [hy])
      have hd1 : (X - C x : ℂ[X]).natDegree ≤ 1 := by
        rw [Polynomial.natDegree_X_sub_C]
      -- split the padded reciprocal into the first and the remaining factor
      rw [Multiset.card_cons]
      rw [show x ::ₘ s = (x ::ₘ 0) + s by simp, linprod_add]
      have he1 : linprod (x ::ₘ (0:Multiset ℂ)) = (X - C x : ℂ[X]) := by simp [linprod]
      rw [he1]
      have hdegs : (linprod s).natDegree ≤ s.card := by rw [natDegree_linprod]
      -- it is slightly more convenient to split `1+card` and commute
      rw [show s.card + 1 = 1 + s.card by omega]
      rw [cstar_mul 1 s.card (X-C x) (linprod s) hd1 hdegs]
      rw [cstar_linear x hx, ih hs']
      -- expand both maps and products by the head element
      simp [linprod, tau, mul_assoc, mul_left_comm, mul_comm]

lemma cstar_pad (e n : ℕ) (he : e ≤ n) (r : ℂ[X]) (hr : r.natDegree ≤ e) :
    cstar n r = (X:ℂ[X])^(n-e) * cstar e r := by
  have hsum : (n-e)+e = n := Nat.sub_add_cancel he
  have hone : (1:ℂ[X]).natDegree ≤ n-e := by simp
  have h := cstar_mul (n-e) e (1:ℂ[X]) r hone hr
  simp [hsum, cstar, mul_comm] at h ⊢
  -- the simp above knows the reciprocal of one
  exact h

-- Infinitely many points of the circle (the rational parametrisation is injective on ℝ).
lemma path_one_inj : Function.Injective (path (1:Circle)) := by
  intro t s h
  have hh := congrArg (fun u : Circle => (u:ℂ)) h
  change ((1:Circle):ℂ) * ((1 + (t:ℂ)*Complex.I)/(1 - (t:ℂ)*Complex.I)) =
    ((1:Circle):ℂ) * ((1 + (s:ℂ)*Complex.I)/(1 - (s:ℂ)*Complex.I)) at hh
  simp at hh
  have hh' := (div_eq_div_iff (den_ne t) (den_ne s)).1 hh
  have hres : (t:ℂ) = (s:ℂ) := by
    apply (mul_left_cancel₀ (a:= (2:ℂ)*Complex.I)
      (by exact mul_ne_zero (by norm_num) Complex.I_ne_zero))
    linear_combination hh'
  exact_mod_cast hres
lemma infinite_circle : Infinite Circle := by
  exact Infinite.of_injective (path (1:Circle)) path_one_inj

/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem exists_complementary_polynomial_on_unit_circle (P : ℂ[X])
    (hP : ∀ z : Circle, ‖P.eval (z : ℂ)‖ ≤ 1) :
    ∃ Q : ℂ[X],
      Q.natDegree ≤ P.natDegree ∧
        ∀ z : Circle, ‖P.eval (z : ℂ)‖ ^ 2 + ‖Q.eval (z : ℂ)‖ ^ 2 = 1 :=
/-ResultProofBegin-/ by
  classical
  by_cases hzero : P = 0
  · subst P
    refine ⟨1, by simp, ?_⟩
    intro z
    simp
  let n : ℕ := P.natDegree
  have hp : P.natDegree ≤ n := by simp [n]
  have hfac : ∃ q : ℂ[X], q.natDegree ≤ n ∧
          X^n - P * cstar n P = q * cstar n q := by
    by_cases hn : n = 0
    · have hp0 : P.natDegree ≤ 0 := hp.trans (by simpa [hn])
      have h0 := deg0fac P hp0 hP
      simpa [hn] using h0
    -- the zero Laurent polynomial has the zero factor.
    by_cases hzF : X^n - P * cstar n P = 0
    · refine ⟨0, ?_, ?_⟩
      · simp
      · simpa [hzF]
    -- collect the exact algebraic/positivity Fejér--Riesz subproblem;
    -- all coercions to the circle and padding in the reciprocal have been removed.
    have hdegF : (X^n - P * cstar n P).natDegree ≤ n+n :=
      deg_F n P hp
    have hsymF : cstar (n+n) (X^n - P * cstar n P) =
          X^n - P * cstar n P := cstar_F n P hp
    have hvalF : ∀ z : Circle,
        (X^n - P * cstar n P).eval (z:ℂ) =
        (z:ℂ)^n * (((1 - ‖P.eval (z:ℂ)‖^2 : ℝ)) : ℂ) :=
      eval_F n P hp
    have hposF : ∀ z : Circle, 0 ≤ (1:ℝ) - ‖P.eval (z:ℂ)‖^2 :=
      nonneg_circle_F n P hp hP
    have hlowerF : n ≤ (X^n - P * cstar n P).natDegree :=
      half_le_degree_selfstar n (X^n - P * cstar n P) hzF hdegF hsymF
    have htrailF : (X^n - P * cstar n P).natTrailingDegree =
        n+n - (X^n - P * cstar n P).natDegree :=
      trailing_selfstar n (X^n - P * cstar n P) hzF hdegF hsymF
    have hsplitsF : (X^n - P * cstar n P).Splits := by
      simpa using
        (IsAlgClosed.splits_codomain (f:= RingHom.id ℂ)
          (X^n - P * cstar n P))
    have hformulaF : X^n - P * cstar n P =
        C (X^n - P * cstar n P).leadingCoeff *
          (Multiset.map (fun x : ℂ => X - C x)
            (X^n - P * cstar n P).roots).prod :=
      Polynomial.eq_prod_roots_of_splits hsplitsF
    have hzeroMultF : (X^n - P * cstar n P).rootMultiplicity 0 =
        n+n - (X^n - P * cstar n P).natDegree := by
      rw [Polynomial.rootMultiplicity_eq_natTrailingDegree']
      exact htrailF
    have hrootF : ∀ {x : ℂ}, x ≠ 0 →
        ((X^n - P * cstar n P).IsRoot x ↔
          (X^n - P * cstar n P).IsRoot ((starRingEnd ℂ x)⁻¹)) := by
      intro x hx
      exact isRoot_symm n (X^n - P * cstar n P) hdegF hsymF x hx
    have hrootmultF : ∀ {x : ℂ}, x ≠ 0 →
        (X^n - P * cstar n P).rootMultiplicity x =
        (X^n - P * cstar n P).rootMultiplicity ((starRingEnd ℂ x)⁻¹) := by
      intro x hx
      exact rootMultiplicity_selfstar (n+n) _ hzF hdegF hsymF x hx
    have hevenF : ∀ z : Circle,
        Even ((X^n - P * cstar n P).rootMultiplicity (z:ℂ)) := by
      intro z
      apply even_root_circle n (X^n - P * cstar n P) hzF
        (z := z)
      intro u
      refine ⟨(1 - ‖P.eval (u:ℂ)‖^2 : ℝ), hposF u, ?_⟩
      exact hvalF u
    let f : ℂ[X] := X^n - P * cstar n P
    have hf : f ≠ 0 := by simpa [f] using hzF
    have hfd : f.natDegree ≤ n+n := by simpa [f] using hdegF
    have hflo : n ≤ f.natDegree := by simpa [f] using hlowerF
    have hfm0 : f.rootMultiplicity 0 = n+n - f.natDegree := by
      simpa [f] using hzeroMultF
    have hfs : f.Splits := by simpa [f] using hsplitsF
    have hcntroots : f.roots.card = f.natDegree := by
      exact Polynomial.splits_iff_card_roots.mp hfs
    have hrmult : ∀ {x:ℂ}, x ≠ 0 →
        f.rootMultiplicity (tau x) = f.rootMultiplicity x := by
      intro x hx
      have h := hrootmultF (x:=x) hx
      -- just a change of notation
      simpa [f, tau] using h.symm
    have heven : ∀ (z:Circle), Even (f.rootMultiplicity (z:ℂ)) := by
      intro z; simpa [f] using hevenF z
    let R : Multiset ℂ := f.roots
    let S : Finset ℂ := R.toFinset
    let takeN : ℂ → ℕ := fun x =>
       if x = 0 then 0 else
       if ‖x‖ < (1:ℝ) then R.count x
       else if ‖x‖ = (1:ℝ) then (R.count x)/2 else 0
    let M : Multiset ℂ := S.val.bind
        (fun x => Multiset.replicate (takeN x) x)
    have countM (a:ℂ) : M.count a = if a ∈ S then takeN a else 0 := by
      classical
      dsimp [M]
      rw [Multiset.count_bind]
      change (∑ x ∈ S, Multiset.count a
        (Multiset.replicate (takeN x) x)) = _
      by_cases ha : a ∈ S
      · rw [if_pos ha]
        have hh := Finset.sum_eq_single_of_mem a ha
          (fun b hb hba =>
            (show Multiset.count a (Multiset.replicate (takeN b) b) = 0 by
              simp [Multiset.count_replicate, hba]))
        rw [hh]
        simp
      · rw [if_neg ha]
        have hh : ∀ b ∈ S, Multiset.count a
            (Multiset.replicate (takeN b) b) = 0 := by
          intro b hb
          have hba : b ≠ a := by intro e; subst b; contradiction
          simp [Multiset.count_replicate, hba]
        simpa [hh] using (Finset.sum_eq_zero hh)
    have notS_count {a:ℂ} (ha:a ∉ S) : R.count a = 0 := by
      apply Multiset.count_eq_zero_of_notMem
      intro h
      exact ha ((Multiset.mem_toFinset).2 h)
    have countM_zero : M.count (0:ℂ) = 0 := by
      by_cases h0 : (0:ℂ) ∈ S
      · simp [countM, h0, takeN]
      · simp [countM, h0]
    have M_nezero : ∀ x ∈ M, x ≠ (0:ℂ) := by
      intro x hx h0
      subst x
      have := Multiset.count_pos.mpr hx
      simpa [countM_zero] using this
    have countR_tau {x:ℂ} (hx:x≠0) : R.count (tau x) = R.count x := by
      change Multiset.count (tau x) f.roots = Multiset.count x f.roots
      simp [Polynomial.count_roots, hrmult hx]
    have count_map_tau (a:ℂ) : (M.map tau).count a = M.count (tau a) := by
      have hh := Multiset.count_map_eq_count' tau M tau_inj (tau a)
      simpa [tau_tau] using hh
    have countM_lt {a:ℂ} (ha0:a≠0) (ha:‖a‖ < (1:ℝ)) : M.count a = R.count a := by
      by_cases hS : a ∈ S
      · simp [countM, hS, takeN, ha0, ha]
      · rw [countM, if_neg hS, notS_count hS]
    have countM_eq {a:ℂ} (ha0:a≠0) (ha:‖a‖ = (1:ℝ)) : M.count a = R.count a / 2 := by
      by_cases hS : a ∈ S
      · simp [countM, hS, takeN, ha0, (show ¬ ‖a‖ < (1:ℝ) by linarith), ha]
      · rw [countM, if_neg hS, notS_count hS]
    have countM_gt {a:ℂ} (ha: (1:ℝ) < ‖a‖) : M.count a = 0 := by
      have ha0 : a ≠ 0 := (norm_pos_iff.mp (by linarith : 0 < ‖a‖))
      by_cases hS : a ∈ S
      · simp [countM, hS, takeN, ha0, (show ¬ ‖a‖ < (1:ℝ) by linarith),
              (show ‖a‖ ≠ (1:ℝ) by linarith)]
      · simp [countM, hS]
    let j : ℕ := n+n - f.natDegree
    have countR0 : R.count (0:ℂ) = j := by
      dsimp [R, j]
      rw [Polynomial.count_roots]
      exact hfm0
    have Rsplit : R = Multiset.replicate j (0:ℂ) + M + (M.map tau) := by
      apply Multiset.ext.mpr
      intro a
      by_cases ha0 : a = 0
      · subst a
        simp [Multiset.count_add, countR0, countM_zero, count_map_tau,
              tau_zero, Multiset.count_replicate]
      · have ha0' : (0:ℂ) ≠ a := Ne.symm ha0
        have hpa : 0 < ‖a‖ := norm_pos_iff.mpr ha0
        rcases lt_trichotomy ‖a‖ (1:ℝ) with hal | hae | hag
        · have ht : (1:ℝ) < ‖tau a‖ := by
            rw [norm_tau]
            exact (one_lt_inv₀ hpa).2 hal
          have hma := countM_lt ha0 hal
          have hmt := countM_gt ht
          simp [Multiset.count_add, Multiset.count_replicate,
             ha0, ha0', hma, count_map_tau, hmt]
        · have htself : tau a = a := tau_of_norm_one hae
          have hma := countM_eq ha0 hae
          let u : Circle := ⟨a, (mem_sphere_zero_iff_norm.2 hae)⟩
          have hev : Even (R.count a) := by
            dsimp [R]
            rw [Polynomial.count_roots]
            simpa [u] using (heven u)
          have hhalf : R.count a / 2 + R.count a / 2 = R.count a := by
            have hh := Nat.two_mul_div_two_of_even hev
            omega
          simp [Multiset.count_add, Multiset.count_replicate,
                ha0, ha0', hma, count_map_tau, htself]
          omega
        · have ht : ‖tau a‖ < (1:ℝ) := by
            rw [norm_tau]
            exact (inv_lt_one₀ hpa).2 hag
          have hta0 : tau a ≠ 0 := tau_ne_zero ha0
          have hma := countM_gt hag
          have hmt := countM_lt hta0 ht
          have hrt := countR_tau ha0
          simp [Multiset.count_add, Multiset.count_replicate,
                ha0, ha0', hma, count_map_tau, hmt, hrt]
    let e : ℕ := M.card
    have hcard : f.natDegree = j + e + e := by
      have hh := congrArg Multiset.card Rsplit
      dsimp [R] at hh
      -- use the number of roots in a splitting polynomial
      simp [Multiset.card_add] at hh
      dsimp [e]
      simpa [hcntroots] using hh
    have he : e = f.natDegree - n := by
      dsimp [j] at hcard
      omega
    have hen : e ≤ n := by omega
    have hje : n - e = j := by
      dsimp [j]
      omega
    let r : ℂ[X] := linprod M
    let rt : ℂ[X] := linprod (M.map tau)
    let k : ℂ := (M.map (fun x : ℂ => -(starRingEnd ℂ x))).prod
    have hrdeg : r.natDegree = e := by simp [r, e, natDegree_linprod]
    have hk : k ≠ 0 := by
      dsimp [k]
      apply Multiset.prod_ne_zero
      intro hz
      rcases Multiset.mem_map.1 hz with ⟨x, hx, heq⟩
      have hx0 := M_nezero x hx
      have : -(starRingEnd ℂ x) ≠ 0 := by simp [hx0]
      exact this heq
    have hform : f = C f.leadingCoeff * ((X:ℂ[X])^j * r * rt) := by
      calc
        f = C f.leadingCoeff * linprod R := by
          simpa [f, R, linprod] using hformulaF
        _ = C f.leadingCoeff * ((X:ℂ[X])^j * r * rt) := by
          rw [Rsplit, linprod_add, linprod_add, linprod_zero_repl]
    have hcstr : cstar n r = (X:ℂ[X])^j * C k * rt := by
      calc
       cstar n r = (X:ℂ[X])^(n-e) * cstar e r :=
         cstar_pad e n hen r (by rw [hrdeg])
       _ = (X:ℂ[X])^j * cstar e r := by rw [hje]
       _ = (X:ℂ[X])^j * C k * rt := by
         dsimp [r, rt, k]
         rw [cstar_linprod M M_nezero]
         ring
    have hprod : r * cstar n r = C k * ((X:ℂ[X])^j * r * rt) := by
      rw [hcstr]
      ring
    let c : ℂ := f.leadingCoeff / k
    have hmain : f = C c * (r * cstar n r) := by
      rw [hform, hprod]
      dsimp [c]
      have hh : f.leadingCoeff / k * k = f.leadingCoeff := by
        field_simp
      calc
        C f.leadingCoeff * (X^j * r * rt) = (C (f.leadingCoeff / k) * C k) * (X^j * r * rt) := by
            rw [← Polynomial.C_mul, hh]
        _ = C (f.leadingCoeff / k) * (C k * (X^j * r * rt)) := by ring
    -- Choose a point of the circle which is not a zero.  There are infinitely
    -- many such points and only finitely many roots of a nonzero polynomial.
    letI : Infinite Circle := infinite_circle
    let bad : Set Circle := {z | f.IsRoot (z:ℂ)}
    have hbad : bad.Finite := by
      change ((fun z : Circle => (z:ℂ)) ⁻¹' {x : ℂ | f.IsRoot x}).Finite
      have hi : Function.Injective (fun z : Circle => (z:ℂ)) := by
        intro a b h
        exact Subtype.ext h
      exact Set.Finite.preimage hi.injOn (Polynomial.finite_setOf_isRoot hf)
    obtain ⟨z, hzmem⟩ := (Set.infinite_univ.diff hbad).nonempty
    have hzbad : z ∉ bad := hzmem.2
    have hznz : f.eval (z:ℂ) ≠ 0 := by
      intro h
      apply hzbad
      change f.IsRoot (z:ℂ)
      exact h
    let w : ℂ := (z:ℂ)
    have hw : w ≠ 0 := circle_ne_zero z
    let s0 : ℝ := 1 - ‖P.eval w‖^2
    let t0 : ℝ := ‖r.eval w‖^2
    have hvs : f.eval w = w^n * (s0:ℂ) := by
      simpa [f, w, s0] using (hvalF z)
    have hsnon : s0 ≠ 0 := by
      intro h
      apply hznz
      change f.eval w = 0
      rw [hvs, h]
      simp
    have hspos : 0 < s0 := by
      have hh := hposF z
      change 0 ≤ s0 at hh
      exact lt_of_le_of_ne hh (Ne.symm hsnon)
    have hrg := eval_cstar_mul n r (by omega : r.natDegree ≤ n) z
    change r.eval w * (cstar n r).eval w = w^n * (t0:ℂ) at hrg
    have hevmain : f.eval w = c * (w^n * (t0:ℂ)) := by
      calc
        f.eval w = (C c * (r * cstar n r)).eval w :=
          congrArg (fun u : ℂ[X] => u.eval w) hmain
        _ = c * (r.eval w * (cstar n r).eval w) := by simp
        _ = c * (w^n * (t0:ℂ)) := by rw [hrg]
    have hct : (s0:ℂ) = c * (t0:ℂ) := by
      apply (mul_left_cancel₀ (pow_ne_zero n hw))
      calc
        w^n * (s0:ℂ) = f.eval w := hvs.symm
        _ = c * (w^n * (t0:ℂ)) := hevmain
        _ = w^n * (c * (t0:ℂ)) := by ring
    have htn : t0 ≠ 0 := by
      intro ht
      have hs : (s0:ℂ) = 0 := by simpa [ht] using hct
      exact hsnon (by exact_mod_cast hs)
    have htpos : 0 < t0 := by
      have ht : 0 ≤ t0 := by
        dsimp [t0]
        positivity
      exact lt_of_le_of_ne ht (Ne.symm htn)
    have hc : c = ((s0 / t0 : ℝ) : ℂ) := by
      apply (mul_right_cancel₀ ( (by exact_mod_cast htn) : (t0:ℂ) ≠ 0))
      calc
        c * (t0:ℂ) = (s0:ℂ) := hct.symm
        _ = ((s0 / t0 : ℝ) : ℂ) * (t0:ℂ) := by
          have hr : (s0 / t0) * t0 = s0 := by
            field_simp
          exact_mod_cast hr.symm
    let u : ℝ := Real.sqrt (s0/t0)
    have hu : u * u = s0/t0 := by
      dsimp [u]
      exact Real.mul_self_sqrt (by positivity)
    have hqstar : cstar n (C (u:ℂ) * r) = C (u:ℂ) * cstar n r := by
      have hm := cstar_mul 0 n (C (u:ℂ)) r (by simp) (by omega : r.natDegree ≤ n)
      simpa [cstar] using hm
    refine ⟨C (u:ℂ) * r, ?_, ?_⟩
    · calc
        (C (u:ℂ) * r).natDegree ≤ (C (u:ℂ)).natDegree + r.natDegree :=
          Polynomial.natDegree_mul_le
        _ ≤ n := by simp [hrdeg, hen]
    · change f = (C (u:ℂ) * r) * cstar n (C (u:ℂ) * r)
      rw [hmain, hqstar, hc]
      -- all constants left are real ones
      have huc : (u:ℂ) * (u:ℂ) = ((s0/t0:ℝ):ℂ) := by
        exact_mod_cast hu
      calc
        C (↑(s0 / t0) : ℂ) * (r * cstar n r) =
            (C (u:ℂ) * r) * (C (u:ℂ) * cstar n r) := by
              calc
                C (↑(s0 / t0) : ℂ) * (r * cstar n r) =
                    (C (u:ℂ) * C (u:ℂ)) * (r * cstar n r) := by
                       rw [← Polynomial.C_mul, huc]
                _ = (C (u:ℂ) * r) * (C (u:ℂ) * cstar n r) := by ring
        _ = _ := rfl
  obtain ⟨q, hq, hf⟩ := hfac
  refine ⟨q, ?_, ?_⟩
  · simpa [n] using hq
  · exact consequence n P q hp hq hf
/-ResultProofEnd-/
/-ResultEnd-/

end Submission
