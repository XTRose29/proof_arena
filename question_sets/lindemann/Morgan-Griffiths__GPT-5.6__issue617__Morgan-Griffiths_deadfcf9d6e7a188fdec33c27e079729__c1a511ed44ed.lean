import Mathlib
import Submission.Helpers

open Polynomial

namespace Submission

/-ResultProofDefinitionsBegin-/
noncomputable section
open scoped Nat

private def lindemannAuxPoly (d : ℕ) : ℤ[X] :=
  ∏ k ∈ Finset.Icc 1 d, (X - C (k:ℤ))

lemma aux_eval_zero (d : ℕ) : (lindemannAuxPoly d).eval 0 ≠ 0 := by
  classical
  simp [lindemannAuxPoly, Polynomial.eval_prod, Finset.prod_ne_zero_iff, Nat.one_le_iff_ne_zero]
  intro a ha hd
  exact ha

lemma aux_root (d k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ d) :
    (k:ℂ) ∈ (lindemannAuxPoly d).aroots ℂ := by
  classical
  rw [Polynomial.mem_aroots]
  constructor
  · intro h
    exact aux_eval_zero d (by simp [h])
  · simp [lindemannAuxPoly]
    exact Finset.prod_eq_zero (Finset.mem_Icc.mpr ⟨hk1, hk⟩) (by simp)

lemma no_rel_exp_one_complex :
    ∀ q : ℤ[X], Polynomial.aeval (Complex.exp (1:ℂ)) q = 0 → q = 0 := by
  classical
  by_contra! H
  let prop : ℕ → Prop := fun d => ∃ q : ℤ[X], q ≠ 0 ∧ Polynomial.aeval (Complex.exp (1:ℂ)) q = 0 ∧ q.natDegree = d
  have hex : ∃ d, prop d := by
    obtain ⟨q, hq, hn⟩ := H
    exact ⟨q.natDegree, q, hn, hq, rfl⟩
  let d := Nat.find hex
  obtain ⟨q, hq0, hqr, hd⟩ := Nat.find_spec hex
  have hqconst : q.coeff 0 ≠ 0 := by
    intro h0
    obtain ⟨r, hr⟩ := Polynomial.X_dvd_iff.mpr h0
    -- hr : q = ?
    rw [hr, Polynomial.aeval_mul] at hqr
    have hr0 : r ≠ 0 := by
      intro hh
      apply hq0
      simp [hr, hh]
    have hrr : Polynomial.aeval (Complex.exp (1:ℂ)) r = 0 := by
      rcases mul_eq_zero.mp hqr with h | h
      · simpa using h
      · exact h
    have hle : Nat.find hex ≤ r.natDegree :=
      Nat.find_min' hex (show prop r.natDegree from ⟨r, hr0, hrr, rfl⟩)
    have hdegmul : q.natDegree = r.natDegree + 1 := by
      rw [hr, Polynomial.natDegree_X_mul hr0]
    omega
  have hdpos : 0 < q.natDegree := by
    by_contra hn
    have hz : q.natDegree = 0 := Nat.eq_zero_of_not_pos hn
    have heq := Polynomial.eq_C_of_natDegree_eq_zero hz
    rw [heq, Polynomial.aeval_C] at hqr
    apply hqconst
    exact (RingHom.injective_int (algebraMap ℤ ℂ)) (by simpa using hqr)
  -- set up indices and relation
  have hpow (i : ℕ) : (Complex.exp (1:ℂ)) ^ i = Complex.exp (i:ℂ) := by
    rw [← Complex.exp_nat_mul]
    simp
  have hrel0 : (∑ i ∈ Finset.range (q.natDegree+1),
      (q.coeff i : ℂ) * Complex.exp (i:ℂ)) = 0 := by
    rw [Polynomial.aeval_eq_sum_range] at hqr
    -- normalize the terms of the Taylor expression
    simpa [mul_comm, hpow] using hqr
  let I : Finset ℕ := Finset.Icc 1 q.natDegree
  have hfin : (Finset.range (q.natDegree+1)).erase 0 = I := by
    ext i
    simp [I]
    omega
  have hzmem : 0 ∈ Finset.range (q.natDegree+1) := by simp
  have hrel : (q.coeff 0 : ℂ) +
      (∑ i ∈ I, (q.coeff i : ℂ) * Complex.exp (i:ℂ)) = 0 := by
    have hs := Finset.sum_erase_add (Finset.range (q.natDegree+1))
       (fun i : ℕ => (q.coeff i : ℂ) * Complex.exp (i:ℂ)) hzmem
    rw [hfin] at hs
    -- now compare with the complete zero sum
    rw [← hs] at hrel0
    simpa [add_comm] using hrel0
  let A : ℝ := ∑ i ∈ I, |(q.coeff i : ℝ)|
  obtain ⟨c, hc⟩ := LindemannWeierstrass.exp_polynomial_approx
      (lindemannAuxPoly q.natDegree) (aux_eval_zero _)
  have hev : ∀ᶠ m : ℕ in Filter.atTop,
      A * |c| ^ m / (m-1)! < (1:ℝ) := by
    have ht := FloorSemiring.tendsto_mul_pow_div_factorial_sub_atTop
        (K := ℝ) A |c| 1
    exact ht.eventually_lt_const (by norm_num)
  obtain ⟨B, hB⟩ := (Filter.eventually_atTop.1 hev)
  let T := max B (max ((lindemannAuxPoly q.natDegree).eval 0).natAbs.succ
                          (q.coeff 0).natAbs.succ)
  obtain ⟨p, hpT, hpprime⟩ := Nat.exists_infinite_primes T
  have hpB : B ≤ p := le_trans (le_max_left _ _) hpT
  have hsmall : A * |c| ^ p / (p-1)! < (1:ℝ) := hB p hpB
  have hpF : ((lindemannAuxPoly q.natDegree).eval 0).natAbs < p := by
    have hx : ((lindemannAuxPoly q.natDegree).eval 0).natAbs.succ ≤ T :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    omega
  have hpq : (q.coeff 0).natAbs < p := by
    have hx : (q.coeff 0).natAbs.succ ≤ T :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    omega
  obtain ⟨n, hn, g, hgdeg, hg⟩ := hc p hpF hpprime
  have hbound (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ q.natDegree) :
      ‖(n:ℂ) * Complex.exp (k:ℂ) - (p:ℕ) *
        Polynomial.aeval (k:ℂ) g‖ ≤ |c| ^ p / (p-1)! := by
    have hh := @hg (k:ℂ) (aux_root q.natDegree k hk1 hk)
    -- normalize the scalar actions
    -- enlarge the exponential bound to an absolute value
    have hcp : c ^ p ≤ |c| ^ p := by
      simpa [abs_pow] using (le_abs_self (c ^ p))
    calc
      ‖(n:ℂ) * Complex.exp (k:ℂ) - (p:ℕ) *
          Polynomial.aeval (k:ℂ) g‖
          ≤ c ^ p / (p-1)! := by simpa [nsmul_eq_mul, zsmul_eq_mul] using hh
      _ ≤ |c| ^ p / (p-1)! := by
        gcongr
  have hae (k : ℕ) : Polynomial.aeval (k:ℂ) g = ((g.eval (k:ℤ) : ℤ) : ℂ) := by
    simpa using
      (Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval
        (R := ℤ) (A := ℂ) (k:ℤ) g)
  have herror (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ q.natDegree) :
      ‖(p:ℕ) * ((g.eval (k:ℤ) : ℤ) : ℂ) - (n:ℂ) * Complex.exp (k:ℂ)‖
        ≤ |c| ^ p / (p-1)! := by
    have hh := hbound k hk1 hk
    rw [hae] at hh
    rw [← norm_neg]
    convert hh using 1 <;> ring
  let W : ℤ := n * q.coeff 0 + (p:ℤ) *
        (∑ i ∈ I, q.coeff i * g.eval (i:ℤ))
  have hpa : ¬ (p:ℤ) ∣ q.coeff 0 := by
    intro hdiv
    have hdiv' : p ∣ (q.coeff 0).natAbs := (Int.natCast_dvd).1 hdiv
    exact (Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr hqconst) hpq) hdiv'
  have hpint : Prime (p:ℤ) := (Nat.prime_iff_prime_int.mp hpprime)
  have hW0 : W ≠ 0 := by
    intro hzero
    have hsum : (p:ℤ) ∣ (p:ℤ) *
        (∑ i ∈ I, q.coeff i * g.eval (i:ℤ)) := dvd_mul_right _ _
    have heq : n * q.coeff 0 = -((p:ℤ) *
        (∑ i ∈ I, q.coeff i * g.eval (i:ℤ))) := by
      simpa [W] using congrArg (fun z : ℤ => z - (p:ℤ) *
        (∑ i ∈ I, q.coeff i * g.eval (i:ℤ))) hzero
    have hdiv : (p:ℤ) ∣ n * q.coeff 0 := by
      rw [heq]
      exact dvd_neg.mpr hsum
    exact (hpint.not_dvd_mul hn hpa) hdiv
  have hWcast : (W:ℂ) =
      ∑ i ∈ I, (q.coeff i:ℂ) *
        ((p:ℕ) * ((g.eval (i:ℤ) : ℤ):ℂ) - (n:ℂ) * Complex.exp (i:ℂ)) := by
    dsimp [W]
    push_cast
    have hreln :
        ∑ i ∈ I, (q.coeff i:ℂ) * Complex.exp (i:ℂ) =
          -(q.coeff 0 : ℂ) := by
        exact eq_neg_of_add_eq_zero_right hrel
    -- keep the two scalar sums intact

    -- expand the sums; the exponential part collapses by the relation
    calc
      (n:ℂ) * (q.coeff 0:ℂ) + (p:ℂ) *
             (∑ i ∈ I, (q.coeff i:ℂ) * ((g.eval (i:ℤ) : ℤ):ℂ)) =
        (p:ℂ) * (∑ i ∈ I, (q.coeff i:ℂ) * ((g.eval (i:ℤ) : ℤ):ℂ)) -
             (n:ℂ) * (∑ i ∈ I, (q.coeff i:ℂ) * Complex.exp (i:ℂ)) := by
               rw [hreln]
               ring
      _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have hnorm : ‖(W:ℂ)‖ ≤ A * (|c| ^ p / (p-1)!) := by
    rw [hWcast]
    calc
      ‖∑ i ∈ I, (q.coeff i:ℂ) *
        ((p:ℕ) * ((g.eval (i:ℤ) : ℤ):ℂ) - (n:ℂ) * Complex.exp (i:ℂ))‖
          ≤ ∑ i ∈ I, |(q.coeff i:ℝ)| * (|c| ^ p / (p-1)!) := by
            apply norm_sum_le_of_le I
            intro i hi
            have hi' : 1 ≤ i ∧ i ≤ q.natDegree := Finset.mem_Icc.mp hi
            calc
              ‖(q.coeff i:ℂ) * ((p:ℕ) * ((g.eval (i:ℤ) : ℤ):ℂ) -
                   (n:ℂ) * Complex.exp (i:ℂ))‖ =
                  |(q.coeff i:ℝ)| *
                    ‖((p:ℕ) * ((g.eval (i:ℤ) : ℤ):ℂ) - (n:ℂ) * Complex.exp (i:ℂ))‖ := by
                      rw [norm_mul, Complex.norm_intCast]
              _ ≤ |(q.coeff i:ℝ)| * (|c| ^ p / (p-1)!) := by
                    gcongr
                    exact herror i hi'.1 hi'.2
      _ = _ := by rw [Finset.sum_mul]
  have hcontr : ‖(W:ℂ)‖ < 1 := lt_of_le_of_lt hnorm (by
    -- reassociate the product
    simpa [div_eq_mul_inv, mul_assoc, A] using hsmall)
  have hlarge : (1:ℝ) ≤ ‖(W:ℂ)‖ := by
    rw [Complex.norm_intCast]
    -- a nonzero integer has absolute value at least one
    have hz : (1:ℤ) ≤ |W| := Int.one_le_abs hW0
    exact_mod_cast hz
  exact (not_lt_of_ge hlarge) hcontr

lemma transcendental_exp_one_real : Transcendental ℤ (Real.exp 1) := by
  classical
  apply (transcendental_iff).2
  intro P hP
  apply no_rel_exp_one_complex P
  have hcast := congrArg (fun x : ℝ => (x:ℂ)) hP
  -- rewrite the evaluation after applying the real embedding
  simpa [Polynomial.aeval_eq_sum_range, Complex.ofReal_exp, ← Complex.exp_nat_mul] using hcast

lemma algebraicZ_complex_of_real {x : ℝ} (hx : IsAlgebraic ℤ x) :
    IsAlgebraic ℤ (x:ℂ) := by
  classical
  rcases hx with ⟨P, h0, h⟩
  refine ⟨P, h0, ?_⟩
  have hc := congrArg (fun z : ℝ => (z:ℂ)) h
  simpa [Polynomial.aeval_eq_sum_range] using hc

lemma algebraic_I_Z : IsAlgebraic ℤ Complex.I := by
  refine ⟨(X^2 + C 1 : ℤ[X]), ?_, ?_⟩
  · intro h
    have hd := congrArg (fun p : ℤ[X] => p.coeff 2) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_one] at hd
  · simp [Polynomial.aeval_def]


/-- A convenient arithmetic last step in the Hermite--Lindemann argument.

`exp_polynomial_approx` is useful with any *finite* exponential
relation, not just with the rational integers as exponents.  The
point is that the only algebra in the last step is that the same
linear combination of evaluations of an integral polynomial is an
integer.  Keeping this lemma over a finite *index type* rather than a
finset of complex numbers is useful (conjugates and also sums of
conjugates naturally occur as multisets). -/
private lemma no_integer_exponential_relation
    (ι : Type*) [Fintype ι]
    (r : ι → ℂ) (a : ι → ℤ) (b : ℤ)
    (hb : b ≠ 0)
    (f : ℤ[X]) (hf : f.eval 0 ≠ 0)
    (hr : ∀ i, r i ∈ f.aroots ℂ)
    (hrel : (b : ℂ) + ∑ i, (a i : ℂ) * Complex.exp (r i) = 0)
    (hint : ∀ G : ℤ[X], ∃ t : ℤ,
      (t : ℂ) = ∑ i, (a i : ℂ) * Polynomial.aeval (r i) G) : False := by
  classical
  -- This is precisely the elementary ``integer of absolute value less
  -- than one'' part of the usual proof.  Notice that no choice of an
  -- ordering, nor distinctness of the roots, enters it.
  let A : ℝ := ∑ i : ι, |(a i : ℝ)|
  obtain ⟨c, hc⟩ := LindemannWeierstrass.exp_polynomial_approx f hf
  have hev : ∀ᶠ m : ℕ in Filter.atTop,
      A * |c| ^ m / (m - 1)! < (1 : ℝ) := by
    have ht := FloorSemiring.tendsto_mul_pow_div_factorial_sub_atTop
      (K := ℝ) A |c| 1
    exact ht.eventually_lt_const (by norm_num)
  obtain ⟨B, hB⟩ := (Filter.eventually_atTop.1 hev)
  let T : ℕ := max B (max (f.eval 0).natAbs.succ b.natAbs.succ)
  obtain ⟨p, hpT, hpprime⟩ := Nat.exists_infinite_primes T
  have hpB : B ≤ p := le_trans (le_max_left _ _) hpT
  have hpF : (f.eval 0).natAbs < p := by
    have h : (f.eval 0).natAbs.succ ≤ T :=
      le_trans (le_max_left _ _) (le_max_right B _)
    omega
  have hpb : b.natAbs < p := by
    have h : b.natAbs.succ ≤ T :=
      le_trans (le_max_right _ _) (le_max_right B _)
    omega
  have hsmall : A * |c| ^ p / (p - 1)! < (1 : ℝ) := hB p hpB
  obtain ⟨n, hn, g, hgdeg, hg⟩ := hc p hpF hpprime
  have herr (i : ι) :
      ‖(p : ℕ) * Polynomial.aeval (r i) g -
          (n : ℂ) * Complex.exp (r i)‖ ≤ |c| ^ p / (p - 1)! := by
    have hh := @hg (r i) (hr i)
    have hcp : c ^ p ≤ |c| ^ p := by
      simpa [abs_pow] using (le_abs_self (c ^ p))
    -- the estimate in the analytic lemma has the two terms in the
    -- opposite order.
    rw [← norm_neg]
    calc
      ‖-((p : ℕ) * Polynomial.aeval (r i) g -
          (n : ℂ) * Complex.exp (r i))‖ =
          ‖(n : ℂ) * Complex.exp (r i) -
              (p : ℕ) * Polynomial.aeval (r i) g‖ := by congr 1 <;> ring
      _ ≤ c ^ p / (p - 1)! := by
        simpa [nsmul_eq_mul, zsmul_eq_mul] using hh
      _ ≤ |c| ^ p / (p - 1)! := by gcongr
  obtain ⟨s, hs⟩ := hint g
  let W : ℤ := n * b + (p : ℤ) * s
  have hpint : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpprime
  have hpnb : ¬ (p : ℤ) ∣ b := by
    intro h
    have h' : p ∣ b.natAbs := (Int.natCast_dvd).1 h
    exact (Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr hb) hpb) h'
  have hW : W ≠ 0 := by
    intro h0
    have hd : (p : ℤ) ∣ n * b := by
      have he : n * b = - ((p : ℤ) * s) := by
        have hsub := congrArg (fun x : ℤ => x - (p : ℤ) * s) h0
        simpa [W] using hsub
      rw [he]
      exact dvd_neg.mpr (dvd_mul_right _ _)
    exact (hpint.not_dvd_mul hn hpnb) hd
  have hcast : (W : ℂ) =
      ∑ i : ι, (a i : ℂ) *
        ((p : ℕ) * Polynomial.aeval (r i) g -
          (n : ℂ) * Complex.exp (r i)) := by
    dsimp [W]
    push_cast
    have hre : (∑ i : ι, (a i : ℂ) * Complex.exp (r i)) = -(b : ℂ) :=
      eq_neg_of_add_eq_zero_right hrel
    rw [hs]
    calc
      (n : ℂ) * (b : ℂ) + (p : ℂ) *
          (∑ i : ι, (a i : ℂ) * Polynomial.aeval (r i) g) =
        (p : ℂ) * (∑ i : ι, (a i : ℂ) * Polynomial.aeval (r i) g) -
          (n : ℂ) * (∑ i : ι, (a i : ℂ) * Complex.exp (r i)) := by
            rw [hre]
            ring
      _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have hnorm : ‖(W : ℂ)‖ ≤ A * (|c| ^ p / (p - 1)!) := by
    rw [hcast]
    calc
      ‖(∑ i : ι, (a i : ℂ) *
          ((p : ℕ) * Polynomial.aeval (r i) g -
            (n : ℂ) * Complex.exp (r i)))‖
        ≤ ∑ i : ι, |(a i : ℝ)| * (|c| ^ p / (p - 1)!) := by
          apply norm_sum_le_of_le (Finset.univ)
          intro i hi
          calc
            ‖(a i : ℂ) *
                ((p : ℕ) * Polynomial.aeval (r i) g -
                  (n : ℂ) * Complex.exp (r i))‖ =
              |(a i : ℝ)| *
                ‖((p : ℕ) * Polynomial.aeval (r i) g -
                  (n : ℂ) * Complex.exp (r i))‖ := by
                    rw [norm_mul, Complex.norm_intCast]
            _ ≤ |(a i : ℝ)| * (|c| ^ p / (p - 1)!) := by
                  gcongr
                  exact herr i
      _ = A * (|c| ^ p / (p - 1)!) := by
        dsimp [A]
        rw [Finset.sum_mul]
  have hlt : ‖(W : ℂ)‖ < 1 :=
    lt_of_le_of_lt hnorm (by
      simpa [A, div_eq_mul_inv, mul_assoc] using hsmall)
  have hge : (1 : ℝ) ≤ ‖(W : ℂ)‖ := by
    rw [Complex.norm_intCast]
    have h : (1 : ℤ) ≤ |W| := Int.one_le_abs hW
    exact_mod_cast h
  exact (not_lt_of_ge hge) hlt


/-- There is a *single* integer polynomial, not vanishing at zero, on
whose complex roots one can put any prescribed finite family of
nonzero algebraic integers.  Taking the product is much handier than
continually enlarging the polynomial in the analytic argument. -/
private lemma polynomial_for_integral_family
    (ι : Type*) [Fintype ι] (u : ι → ℂ)
    (hu : ∀ i, IsIntegral ℤ (u i)) (hu0 : ∀ i, u i ≠ 0) :
    ∃ F : ℤ[X], F.eval 0 ≠ 0 ∧ ∀ i, u i ∈ F.aroots ℂ := by
  classical
  have hmin (i : ι) : (minpoly ℤ (u i)).eval 0 ≠ 0 := by
    intro h0
    have hX : (Polynomial.X : ℤ[X]) ∣ minpoly ℤ (u i) :=
      Polynomial.X_dvd_iff.mpr (by
        simpa [Polynomial.coeff_zero_eq_eval_zero] using h0)
    have hback : minpoly ℤ (u i) ∣ (Polynomial.X : ℤ[X]) :=
      (Polynomial.irreducible_X : Irreducible (Polynomial.X : ℤ[X])).dvd_symm
        (minpoly.irreducible (hu i)) hX
    obtain ⟨Q, hQ⟩ := hback
    have hxz : u i = 0 := by
      calc
        u i = Polynomial.aeval (u i) (Polynomial.X : ℤ[X]) :=
          (Polynomial.aeval_X _).symm
        _ = Polynomial.aeval (u i) (minpoly ℤ (u i) * Q) := by rw [hQ]
        _ = 0 := by rw [Polynomial.aeval_mul, minpoly.aeval]; simp
    exact hu0 i hxz
  let F : ℤ[X] := ∏ i : ι, minpoly ℤ (u i)
  have hmon : F.Monic := by
    dsimp [F]
    exact Polynomial.monic_prod_of_monic Finset.univ _ (by intro j hj; exact minpoly.monic (hu j))
  refine ⟨F, ?_, ?_⟩
  · dsimp [F]
    rw [Polynomial.eval_prod]
    exact Finset.prod_ne_zero_iff.mpr (by
      intro i hi
      exact hmin i)
  intro i
  rw [Polynomial.mem_aroots]
  constructor
  · exact hmon.ne_zero
  · dsimp [F]
    change (Polynomial.aeval (u i)) (∏ j ∈ Finset.univ, minpoly ℤ (u j)) = 0
    rw [map_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact minpoly.aeval ℤ (u i)


-- Evaluation of a symmetric integral polynomial on all the roots of a monic
-- integral polynomial is again a rational integer.
private lemma symmetric_eval_on_monic_roots
    (P : ℤ[X]) (hmon : P.Monic) (d : ℕ) (x : Fin d → ℂ)
    (hx : Finset.univ.val.map x = P.aroots ℂ)
    (Q : MvPolynomial (Fin d) ℤ) (hQ : Q.IsSymmetric) :
    ∃ t : ℤ, (t : ℂ) = MvPolynomial.eval₂ (algebraMap ℤ ℂ) x Q := by
  classical
  -- write a symmetric polynomial as a polynomial in the elementary ones
  have hsur : Function.Surjective (MvPolynomial.esymmAlgHom (Fin d) ℤ d) :=
    MvPolynomial.esymmAlgHom_surjective (R := ℤ) (σ := Fin d)
      (n := d) (by simp)
  obtain ⟨q, hq⟩ := hsur (⟨Q, hQ⟩ :
    MvPolynomial.symmetricSubalgebra (Fin d) ℤ)
  have hqv : MvPolynomial.aeval
      (fun i : Fin d => MvPolynomial.esymm (Fin d) ℤ (i.val + 1)) q = Q := by
    have hh := congrArg (fun z : MvPolynomial.symmetricSubalgebra (Fin d) ℤ =>
      (z : MvPolynomial (Fin d) ℤ)) hq
    simpa [MvPolynomial.esymmAlgHom_apply] using hh
  let p : ℂ[X] := P.map (algebraMap ℤ ℂ)
  have hpmon : p.Monic := hmon.map _
  have hpne : p ≠ 0 := hpmon.ne_zero
  have hroots : p.roots = Finset.univ.val.map x := by
    simpa [p, Polynomial.aroots_def] using hx.symm
  have hd : p.natDegree = d := by
    have hspl : p.Splits := IsAlgClosed.splits p
    have hcard : p.roots.card = p.natDegree :=
      (Polynomial.splits_iff_card_roots (f := p)).mp hspl
    rw [hroots] at hcard
    simpa using hcard.symm
  let v : Fin d → ℤ := fun i =>
    ((-1 : ℤ) ^ (i.val + 1)) * P.coeff (d - (i.val + 1))
  have hes (i : Fin d) :
      MvPolynomial.eval₂ (algebraMap ℤ ℂ) x
          (MvPolynomial.esymm (Fin d) ℤ (i.val + 1)) = (v i : ℂ) := by
    -- Vieta, with the roots listed by `x`
    rw [← MvPolynomial.aeval_def, MvPolynomial.aeval_esymm_eq_multiset_esymm]
    change (Finset.univ.val.map x).esymm (i.val + 1) = (v i : ℂ)
    rw [← hroots]
    have hr : i.val + 1 ≤ p.natDegree := by
      rw [hd]
      omega
    have hv := Polynomial.coeff_eq_esymm_roots_of_card
      (p := p)
      ((Polynomial.splits_iff_card_roots (f := p)).mp (IsAlgClosed.splits p))
      (k := p.natDegree - (i.val + 1)) (by omega)
    -- solve the Vieta equality for the elementary coefficient; the sign is its own inverse
    have hv' :
        p.roots.esymm (i.val + 1) =
          ((-1 : ℂ) ^ (i.val + 1)) * p.coeff (p.natDegree - (i.val + 1)) := by
      -- `natDegree - (natDegree-r)=r`
      have hsub : p.natDegree - (p.natDegree - (i.val + 1)) = i.val + 1 := by omega
      rw [hsub] at hv
      -- monic removes the leading coefficient
      rw [hpmon.leadingCoeff] at hv
      -- hv : coeff = 1 * sign * esymm
      -- multiply by the sign
      calc
        p.roots.esymm (i.val + 1) =
            (((-1 : ℂ) ^ (i.val + 1)) ^ (2:ℕ)) *
                p.roots.esymm (i.val + 1) := by
                  have hs : (((-1 : ℂ) ^ (i.val + 1)) ^ (2:ℕ)) = 1 := by
                    rw [pow_two, ← mul_pow]
                    norm_num
                  rw [hs, one_mul]
        _ = ((-1 : ℂ) ^ (i.val + 1)) * p.coeff (p.natDegree - (i.val + 1)) := by
          rw [hv]
          ring
    rw [hv']
    dsimp [v, p]
    -- coefficients commute with the integer embedding
    rw [Polynomial.coeff_map]
    have hdd : (P.map (Int.castRingHom ℂ)).natDegree = d := hd
    rw [hdd]
    simp
  -- now evaluate `q` at the integer elementary coefficients
  refine ⟨MvPolynomial.eval v q, ?_⟩
  -- evaluating a polynomial in the elementary coefficients commutes with eval
  have hfun :
      (MvPolynomial.eval₂ (algebraMap ℤ ℂ) x Q) =
        MvPolynomial.eval₂ (algebraMap ℤ ℂ)
          (fun i : Fin d => (v i : ℂ)) q := by
    rw [← hqv]
    -- composition of evaluation with substitution
    change MvPolynomial.eval₂Hom (algebraMap ℤ ℂ) x
      ((MvPolynomial.aeval
        (fun i : Fin d => MvPolynomial.esymm (Fin d) ℤ (i.val+1))) q) = _
    rw [MvPolynomial.aeval_eq_bind₁]
    rw [MvPolynomial.eval₂Hom_bind₁]
    change
      MvPolynomial.eval₂ (algebraMap ℤ ℂ)
        (fun i : Fin d =>
          MvPolynomial.eval₂ (algebraMap ℤ ℂ) x
            (MvPolynomial.esymm (Fin d) ℤ (i.val+1))) q = _
    simp_rw [hes]
  -- casts of the integer evaluation of `q`
  have hcast :
      ((MvPolynomial.eval v q : ℤ) : ℂ) =
        MvPolynomial.eval₂ (algebraMap ℤ ℂ) (fun i : Fin d => (v i : ℂ)) q := by
    have hh := MvPolynomial.map_eval₂Hom (RingHom.id ℤ) v
      (algebraMap ℤ ℂ) q
    simpa [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_id] using hh
  exact hcast.trans hfun.symm


private def subsetPoly (d : ℕ) (k : ℤ) (G : ℤ[X]) : MvPolynomial (Fin d) ℤ :=
  ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
    MvPolynomial.C (k ^ S.card) *
      Polynomial.aeval (∑ i ∈ S, MvPolynomial.X i) G

private lemma subsetPoly_eval (d : ℕ) (k : ℤ) (G : ℤ[X]) (x : Fin d → ℂ) :
    MvPolynomial.eval₂ (algebraMap ℤ ℂ) x (subsetPoly d k G) =
      ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
        (k : ℂ) ^ S.card *
          Polynomial.aeval (∑ i ∈ S, x i) G := by
  classical
  dsimp [subsetPoly]
  -- the evaluation map is a ring hom
  change MvPolynomial.eval₂Hom (algebraMap ℤ ℂ) x
    (∑ S ∈ _, _) = _
  simp only [map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [MvPolynomial.eval₂Hom_C]
  rw [map_pow]
  congr 1
  -- polynomial evaluation commutes with the multivariable evaluation
  induction G using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add]
      change MvPolynomial.eval₂Hom (algebraMap ℤ ℂ) x
        ((Polynomial.aeval (∑ i ∈ S, MvPolynomial.X i)) p) +
        MvPolynomial.eval₂Hom (algebraMap ℤ ℂ) x
        ((Polynomial.aeval (∑ i ∈ S, MvPolynomial.X i)) q) = _
      rw [hp, hq]
  | monomial n z =>
      simp [Polynomial.aeval_def, map_sum]
      -- remaining constant coefficient
      exact Or.inl (by
        change MvPolynomial.eval₂Hom (algebraMap ℤ ℂ) x
          (MvPolynomial.C z) = (z : ℂ)
        simp)


private lemma subsetPoly_symmetric (d : ℕ) (k : ℤ) (G : ℤ[X]) :
    (subsetPoly d k G).IsSymmetric := by
  classical
  intro e
  dsimp [subsetPoly]
  simp only [map_sum, map_mul, MvPolynomial.rename_C]
  -- the same sum, with S replaced by its image
  apply Finset.sum_bij
    (fun S _ => S.map e.toEmbedding)
  · intro S hS
    exact Finset.mem_powerset.mpr (by intro z hz; simp)
  · intro A hA B hB heq
    have := congrArg (fun t : Finset (Fin d) => t.map e.symm.toEmbedding) heq
    simpa using this
  · intro S hS
    refine ⟨S.map e.symm.toEmbedding,
      Finset.mem_powerset.mpr (by intro z hz; simp), ?_⟩
    ext z
    simp
  · intro S hS
    have hsum :
        (MvPolynomial.rename (e : Fin d → Fin d)) (∑ i ∈ S, (MvPolynomial.X i : MvPolynomial (Fin d) ℤ)) =
          ∑ j ∈ S.map e.toEmbedding, (MvPolynomial.X j : MvPolynomial (Fin d) ℤ) := by
      simp [Finset.sum_map]
    have hpoly :
        (MvPolynomial.rename (e : Fin d → Fin d))
            (Polynomial.aeval (∑ i ∈ S, (MvPolynomial.X i : MvPolynomial (Fin d) ℤ)) G) =
          Polynomial.aeval (∑ j ∈ S.map e.toEmbedding, (MvPolynomial.X j : MvPolynomial (Fin d) ℤ)) G := by
      simp only [Polynomial.aeval_def]
      change ((MvPolynomial.rename (e : Fin d → Fin d)).toRingHom)
        (Polynomial.eval₂ (algebraMap ℤ _) _ G) = _
      rw [Polynomial.hom_eval₂]
      have hc : ((MvPolynomial.rename (e : Fin d → Fin d)).toRingHom).comp
          (algebraMap ℤ (MvPolynomial (Fin d) ℤ)) =
            algebraMap ℤ (MvPolynomial (Fin d) ℤ) := by
              ext z
              simp
      rw [hc]
      change Polynomial.eval₂ (algebraMap ℤ (MvPolynomial (Fin d) ℤ))
        ((MvPolynomial.rename (e : Fin d → Fin d))
          (∑ i ∈ S, (MvPolynomial.X i : MvPolynomial (Fin d) ℤ))) G = _
      rw [hsum]
    simp only [Finset.card_map]
    rw [hpoly]
-- A two-sided variant of `subsetPoly`: it is useful when some of the
-- exponent zero terms cancel in `∏ (1-exp z)`.  Multiplying by the
-- expression with all exponents negated makes its constant coefficient a
-- sum of squares.
private def pairSubsetPoly (d : ℕ) (k : ℤ) (G : ℤ[X]) : MvPolynomial (Fin d) ℤ :=
  ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
    ∑ T ∈ (Finset.univ : Finset (Fin d)).powerset,
      MvPolynomial.C (k ^ S.card * k ^ T.card) *
        Polynomial.aeval
          ((∑ i ∈ S, (MvPolynomial.X i : MvPolynomial (Fin d) ℤ)) -
           (∑ i ∈ T, (MvPolynomial.X i : MvPolynomial (Fin d) ℤ))) G

private lemma pairSubsetPoly_eval (d : ℕ) (k : ℤ) (G : ℤ[X]) (x : Fin d → ℂ) :
    MvPolynomial.eval₂ (algebraMap ℤ ℂ) x (pairSubsetPoly d k G) =
      ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
        ∑ T ∈ (Finset.univ : Finset (Fin d)).powerset,
          (k : ℂ) ^ S.card * (k : ℂ) ^ T.card *
            Polynomial.aeval
              ((∑ i ∈ S, x i) - (∑ i ∈ T, x i)) G := by
  classical
  dsimp [pairSubsetPoly]
  change MvPolynomial.eval₂Hom (algebraMap ℤ ℂ) x (∑ S ∈ _, ∑ T ∈ _, _) = _
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro T hT
  -- evaluate the coefficient and then commute polynomial evaluation with a
  -- ring hom. Writing this out avoids any choices of an ordering of roots.
  simp only [map_mul, MvPolynomial.eval₂Hom_C]
  simp only [map_pow]
  -- it remains to commute evaluation at a polynomial variable
  congr 1
  simp only [Polynomial.aeval_def]
  change MvPolynomial.eval₂Hom (algebraMap ℤ ℂ) x
      (Polynomial.eval₂ (algebraMap ℤ (MvPolynomial (Fin d) ℤ))
        ((∑ i ∈ S, (MvPolynomial.X i : MvPolynomial (Fin d) ℤ)) -
         (∑ i ∈ T, (MvPolynomial.X i : MvPolynomial (Fin d) ℤ))) G) = _
  rw [Polynomial.hom_eval₂]
  have hc : (MvPolynomial.eval₂Hom (algebraMap ℤ ℂ) x).comp
      (algebraMap ℤ (MvPolynomial (Fin d) ℤ)) = algebraMap ℤ ℂ := by
    ext z
    simp
  rw [hc]
  simp

private lemma pairSubsetPoly_symmetric (d : ℕ) (k : ℤ) (G : ℤ[X]) :
    (pairSubsetPoly d k G).IsSymmetric := by
  classical
  intro e
  dsimp [pairSubsetPoly]
  simp only [map_sum, map_mul, MvPolynomial.rename_C]
  apply Finset.sum_bij
    (fun S _ => S.map e.toEmbedding)
  · intro S hS
    exact Finset.mem_powerset.mpr (by intro z hz; simp)
  · intro A hA B hB heq
    have hh := congrArg (fun t : Finset (Fin d) => t.map e.symm.toEmbedding) heq
    simpa using hh
  · intro S hS
    refine ⟨S.map e.symm.toEmbedding,
      Finset.mem_powerset.mpr (by intro z hz; simp), ?_⟩
    ext z
    simp
  · intro S hS
    -- and use the same change of variables in the inner sum
    apply Finset.sum_bij
      (fun T _ => T.map e.toEmbedding)
    · intro T hT
      exact Finset.mem_powerset.mpr (by intro z hz; simp)
    · intro A hA B hB heq
      have hh := congrArg (fun t : Finset (Fin d) => t.map e.symm.toEmbedding) heq
      simpa using hh
    · intro T hT
      refine ⟨T.map e.symm.toEmbedding,
        Finset.mem_powerset.mpr (by intro z hz; simp), ?_⟩
      ext z
      simp
    · intro T hT
      have hsumS :
          (MvPolynomial.rename (e : Fin d → Fin d))
             (∑ i ∈ S, (MvPolynomial.X i : MvPolynomial (Fin d) ℤ)) =
             ∑ i ∈ S.map e.toEmbedding,
               (MvPolynomial.X i : MvPolynomial (Fin d) ℤ) := by
            simp [Finset.sum_map]
      have hsumT :
          (MvPolynomial.rename (e : Fin d → Fin d))
             (∑ i ∈ T, (MvPolynomial.X i : MvPolynomial (Fin d) ℤ)) =
             ∑ i ∈ T.map e.toEmbedding,
               (MvPolynomial.X i : MvPolynomial (Fin d) ℤ) := by
            simp [Finset.sum_map]
      have hpoly :
          (MvPolynomial.rename (e : Fin d → Fin d))
            (Polynomial.aeval
              ((∑ i ∈ S, (MvPolynomial.X i : MvPolynomial (Fin d) ℤ)) -
               (∑ i ∈ T, (MvPolynomial.X i : MvPolynomial (Fin d) ℤ))) G) =
            Polynomial.aeval
              ((∑ i ∈ S.map e.toEmbedding,
                    (MvPolynomial.X i : MvPolynomial (Fin d) ℤ)) -
               (∑ i ∈ T.map e.toEmbedding,
                    (MvPolynomial.X i : MvPolynomial (Fin d) ℤ))) G := by
        simp only [Polynomial.aeval_def]
        change ((MvPolynomial.rename (e : Fin d → Fin d)).toRingHom)
            (Polynomial.eval₂ (algebraMap ℤ _) _ G) = _
        rw [Polynomial.hom_eval₂]
        have hc : ((MvPolynomial.rename (e : Fin d → Fin d)).toRingHom).comp
            (algebraMap ℤ (MvPolynomial (Fin d) ℤ)) =
              algebraMap ℤ (MvPolynomial (Fin d) ℤ) := by
                ext z
                simp
        rw [hc]
        change Polynomial.eval₂ (algebraMap ℤ (MvPolynomial (Fin d) ℤ))
           ((MvPolynomial.rename (e : Fin d → Fin d))
              ((∑ i ∈ S, (MvPolynomial.X i : MvPolynomial (Fin d) ℤ)) -
               (∑ i ∈ T, (MvPolynomial.X i : MvPolynomial (Fin d) ℤ)))) G = _
        rw [map_sub, hsumS, hsumT]
      simp only [Finset.card_map]
      rw [hpoly]
-- For algebraic integers this is precisely the missing symmetric-function
-- step after `exp_polynomial_approx`: the conjugates give algebraic
-- integers to which the factorial estimate is applied.
lemma lindemann_integral_obstruction {w : ℂ}
    (hw : IsIntegral ℤ w) (hw0 : w ≠ 0) :
    Complex.exp w ≠ (1:ℂ) ∧ Complex.exp w ≠ (-1:ℂ) := by
  classical
  /-
  This is the purely algebraic (conjugates) part that has to go before the
  analytic estimate.  It is quite important here that the statement says
  *evaluations of every integral polynomial*, not merely that each exponent
  is integral.  Sums of values at one algebraic integer need not be
  rational; the multiset of all conjugates is what makes the value a
  rational integer.  Keeping the multiplicities by indexing with `Fin m`
  avoids the usually false removal-of-duplicates step.
  -/
  have hsymmetric :
      ∀ ε : ℂ, (ε = (1 : ℂ) ∨ ε = (-1 : ℂ)) →
        Complex.exp w = ε →
        ∃ m : ℕ, ∃ u : Fin m → ℂ, ∃ a : Fin m → ℤ, ∃ b : ℤ,
            b ≠ 0 ∧
            (∀ j, IsIntegral ℤ (u j)) ∧
            (∀ j, u j ≠ 0) ∧
            ((b : ℂ) + ∑ j, (a j : ℂ) * Complex.exp (u j) = 0) ∧
            (∀ G : ℤ[X], ∃ t : ℤ,
              (t : ℂ) = ∑ j, (a j : ℂ) * Polynomial.aeval (u j) G) := by
        intro ε hε he
        -- The multiset of conjugates.  Working with `aroots` makes it a
        -- multiset, so no separability choice is needed here.
        let P : ℤ[X] := minpoly ℤ w
        let R : Multiset ℂ := P.aroots ℂ
        have hPne : P ≠ 0 := minpoly.ne_zero hw
        have hPmon : P.Monic := minpoly.monic hw
        have hP0 : P.eval 0 ≠ 0 := by
          intro h0
          have hX : (Polynomial.X : ℤ[X]) ∣ P :=
            Polynomial.X_dvd_iff.mpr (by
              simpa [Polynomial.coeff_zero_eq_eval_zero] using h0)
          have hback : P ∣ (Polynomial.X : ℤ[X]) :=
            (Polynomial.irreducible_X : Irreducible (Polynomial.X : ℤ[X])).dvd_symm
              (minpoly.irreducible hw) hX
          obtain ⟨q, hq⟩ := hback
          apply hw0
          calc
            w = Polynomial.aeval w (Polynomial.X : ℤ[X]) :=
              (Polynomial.aeval_X _).symm
            _ = Polynomial.aeval w (P * q) := by rw [hq]
            _ = 0 := by
              dsimp [P]
              rw [Polynomial.aeval_mul, minpoly.aeval]
              simp
        have hwR : w ∈ R :=
          Polynomial.mem_aroots.mpr ⟨hPne, by
            dsimp [P]
            exact minpoly.aeval ℤ w⟩
        have hRint : ∀ z ∈ R, IsIntegral ℤ z := by
          intro z hz
          have ez : Polynomial.aeval z P = 0 :=
            (Polynomial.mem_aroots.mp hz).2
          exact ⟨P, hPmon, by
            simpa [Polynomial.aeval_def] using ez⟩
        have hR0 : ∀ z ∈ R, z ≠ 0 := by
          intro z hz hz0
          subst z
          have ez : Polynomial.aeval (0 : ℂ) P = 0 :=
            (Polynomial.mem_aroots.mp hz).2
          have ec : ((P.eval (0 : ℤ) : ℤ) : ℂ) = 0 := by
            have ez' : Polynomial.aeval ((algebraMap ℤ ℂ) (0 : ℤ)) P = 0 := by
              simpa using ez
            rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval
              (R := ℤ) (A := ℂ)] at ez'
            exact ez'
          have ec' : P.eval (0 : ℤ) = 0 := by
            exact_mod_cast ec
          exact hP0 ec'
        -- An actual tuple of roots to which the fundamental theorem of
        -- symmetric polynomials applies.  `roots` is a multiset; a list and
        -- `get` record all its multiplicities (using `toFinset` here would
        -- be a serious error).
        let L : List ℂ := R.toList
        let d : ℕ := L.length
        let x : Fin d → ℂ := L.get
        have hxR : Finset.univ.val.map x = R := by
          dsimp [x, d, L]
          rw [Fin.univ_val_map, List.ofFn_get]
          exact Multiset.coe_toList R
        have hxint (i : Fin d) : IsIntegral ℤ (x i) := by
          apply hRint (x i)
          rw [← hxR]
          exact Multiset.mem_map_of_mem x (Finset.mem_univ i)
        have hx0 (i : Fin d) : x i ≠ 0 := by
          apply hR0 (x i)
          rw [← hxR]
          exact Multiset.mem_map_of_mem x (Finset.mem_univ i)
        have hxw : ∃ i : Fin d, x i = w := by
          have hw' : w ∈ Finset.univ.val.map x := by
            rw [hxR]
            exact hwR
          rcases Multiset.mem_map.mp hw' with ⟨i, hi, hiw⟩
          exact ⟨i, hiw⟩
        let β : Finset (Fin d) → ℂ := fun S => ∑ i ∈ S, x i
        have hβint (S : Finset (Fin d)) : IsIntegral ℤ (β S) := by
          dsimp [β]
          -- algebraic integers form a ring
          classical
          induction S using Finset.induction_on with
          | empty => simpa using (isIntegral_zero : IsIntegral ℤ (0 : ℂ))
          | @insert i S hi ih =>
              rw [Finset.sum_insert hi]
              exact (hxint i).add ih
        -- At this point only the finite, symmetric-polynomial step remains:
        -- take the sums indexed by subsets of `R` in
        -- `∏ z ∈ R, (1 ± exp z)`.  Vieta shows that the displayed
        -- evaluation, for every `G`, is a rational *integer* (all the
        -- sums are integral by `hRint`).  Zero sums contribute the
        -- nonzero constant term; they must not be discarded as a set.
        let k : ℤ := if ε = (1 : ℂ) then -1 else 1
        have hk : k = -1 ∨ k = 1 := by
          dsimp [k]
          by_cases h : ε = (1 : ℂ)
          · left; simp [h]
          · right; simp [h]
        have hk0 : k ≠ 0 := by
          rcases hk with h | h <;> simp [h]
        have hfac : (k : ℂ) * ε + 1 = 0 := by
          rcases hε with h | h
          · have kk : k = -1 := by simp [k, h]
            rw [h, kk]
            norm_num
          · have hn : ε ≠ (1 : ℂ) := by
              rw [h]
              norm_num
            have kk : k = 1 := by simp [k, hn]
            rw [h, kk]
            norm_num
        let U : Finset (Finset (Fin d)) :=
          (Finset.univ : Finset (Fin d)).powerset
        let gam : Finset (Fin d) → ℤ := fun S => k ^ S.card
        let V : Finset ℂ := U.image β
        let cc : ℂ → ℤ := fun z =>
          ∑ S ∈ U.filter (fun S => β S = z), gam S

        -- A real linear functional which is nonzero on every one of the
        -- finitely many roots. It picks out a unique smallest subset sum.
        let Treal : ℝ :=
          (∑ i : Fin d, |(x i).re| / |(x i).im|) + 1
        let phi : ℂ → ℝ := fun z => z.re + Treal * z.im
        have hterm (i : Fin d) :
            0 ≤ |(x i).re| / |(x i).im| :=
          div_nonneg (abs_nonneg _) (abs_nonneg _)
        have hterm_le (i : Fin d) :
            |(x i).re| / |(x i).im| ≤
              ∑ j : Fin d, |(x j).re| / |(x j).im| := by
          exact Finset.single_le_sum (fun j hj => hterm j)
            (Finset.mem_univ i)
        have hterm_lt (i : Fin d) :
            |(x i).re| / |(x i).im| < Treal := by
          dsimp [Treal]
          linarith [hterm_le i]
        have hphi (i : Fin d) : phi (x i) ≠ 0 := by
          by_cases hi : (x i).im = 0
          · have hr : (x i).re ≠ 0 := by
              intro hr
              apply hx0 i
              apply Complex.ext
              · simpa [hr]
              · simpa [hi]
            dsimp [phi]
            simp [hi, hr]
          · have him : 0 < |(x i).im| := abs_pos.mpr hi
            have hlt : |(x i).re| < Treal * |(x i).im| :=
              (div_lt_iff₀ him).mp (hterm_lt i)
            have htpos : 0 < Treal :=
              lt_of_le_of_lt (hterm i) (hterm_lt i)
            intro hzero
            have heq : (x i).re = -(Treal * (x i).im) := by
              dsimp [phi] at hzero
              linarith
            have habs : |(x i).re| = Treal * |(x i).im| := by
              rw [heq, abs_neg, abs_mul, abs_of_pos htpos]
            exact (ne_of_lt hlt) habs
        have hphisum (S : Finset (Fin d)) :
            phi (β S) = ∑ i ∈ S, phi (x i) := by
          dsimp [phi, β]
          simp [Finset.mul_sum, Finset.sum_add_distrib]
        let S0 : Finset (Fin d) :=
          Finset.univ.filter (fun i : Fin d => phi (x i) < 0)
        have hS0 : S0 ∈ U := by
          dsimp [U]
          exact Finset.mem_powerset.mpr (Finset.subset_univ _)
        have hm0 (i : Fin d) : i ∈ S0 ↔ phi (x i) < 0 := by
          simp [S0]
        have hunique (S : Finset (Fin d)) (heq : β S = β S0) : S = S0 := by
          have heqs : (∑ i ∈ S, phi (x i)) =
              ∑ i ∈ S0, phi (x i) := by
            have hh := congrArg phi heq
            simpa [hphisum] using hh
          by_contra hne
          have hall : ¬ (∀ i : Fin d, i ∈ S ↔ i ∈ S0) := by
            intro h
            exact hne (Finset.ext h)
          obtain ⟨j, hj⟩ := (Classical.not_forall).1 hall
          have hle (i : Fin d) :
              (if phi (x i) < 0 then phi (x i) else 0) ≤
                (if i ∈ S then phi (x i) else 0) := by
            by_cases hn : phi (x i) < 0
            · by_cases hs : i ∈ S
              · simp [hn, hs]
              · simp [hn, hs, le_of_lt hn]
            · have hp : 0 < phi (x i) :=
                lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm (hphi i))
              by_cases hs : i ∈ S
              · simp [hn, hs, le_of_lt hp]
              · simp [hn, hs]
          have hltj :
              (if phi (x j) < 0 then phi (x j) else 0) <
                (if j ∈ S then phi (x j) else 0) := by
            by_cases hn : phi (x j) < 0
            · have hj0 : j ∈ S0 := (hm0 j).2 hn
              have hjs : j ∉ S := by
                intro h
                apply hj
                exact ⟨fun _ => hj0, fun _ => h⟩
              simp [hn, hjs]
            · have hj0 : j ∉ S0 := by simpa [hm0] using hn
              have hjs : j ∈ S := by
                by_contra hh
                apply hj
                constructor <;> intro hbad
                · exact (hh hbad).elim
                · exact (hj0 hbad).elim
              have hp : 0 < phi (x j) :=
                lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm (hphi j))
              simp [hn, hjs, hp]
          have hltall :
              (∑ i : Fin d, if phi (x i) < 0 then phi (x i) else 0) <
                ∑ i : Fin d, if i ∈ S then phi (x i) else 0 := by
            exact Finset.sum_lt_sum (s := (Finset.univ : Finset (Fin d)))
              (fun i hi => hle i) ⟨j, Finset.mem_univ _, hltj⟩
          have hsum0 :
              (∑ i : Fin d, if phi (x i) < 0 then phi (x i) else 0) =
                ∑ i ∈ S0, phi (x i) := by
            symm
            simpa [S0] using
              (Finset.sum_filter
                (s := (Finset.univ : Finset (Fin d)))
                (fun i : Fin d => phi (x i) < 0)
                (fun i => phi (x i)))
          have hsumS :
              (∑ i : Fin d, if i ∈ S then phi (x i) else 0) =
                ∑ i ∈ S, phi (x i) := by
            simpa using
              (Finset.sum_ite_mem (Finset.univ : Finset (Fin d)) S
                (fun i => phi (x i)))
          rw [hsum0, hsumS] at hltall
          linarith
        have hcc0 : cc (β S0) = gam S0 := by
          have hfilt : U.filter (fun S => β S = β S0) = {S0} := by
            ext S
            simp only [Finset.mem_filter, Finset.mem_singleton]
            constructor
            · intro h
              exact hunique S h.2
            · intro h; subst S
              exact ⟨hS0, rfl⟩
          dsimp [cc]
          rw [hfilt]
          simp
        have hccne : cc (β S0) ≠ 0 := by
          rw [hcc0]
          dsimp [gam]
          exact pow_ne_zero _ hk0
        have hV0 : β S0 ∈ V :=
          Finset.mem_image.mpr ⟨S0, hS0, rfl⟩

        let b0 : ℤ := ∑ z ∈ V, (cc z) ^ (2:ℕ)
        have hbpos : 0 < b0 := by
          dsimp [b0]
          apply Finset.sum_pos'
          · intro z hz
            exact sq_nonneg (cc z)
          · exact ⟨β S0, hV0, sq_pos_of_ne_zero hccne⟩
        have hbne : b0 ≠ 0 := ne_of_gt hbpos

        let D : Finset (Finset (Fin d) × Finset (Fin d)) := U.product U
        let vv : (Finset (Fin d) × Finset (Fin d)) → ℂ :=
          fun q => β q.1 - β q.2
        let aa0 : (Finset (Fin d) × Finset (Fin d)) → ℤ :=
          fun q => gam q.1 * gam q.2
        let NZ : Finset (Finset (Fin d) × Finset (Fin d)) :=
          D.filter (fun q => vv q ≠ 0)
        -- constant coefficient of the two-sided product
        have hbsum : b0 =
            ∑ q ∈ D.filter (fun q => vv q = 0), aa0 q := by
          -- first group equal subset sums
          have hone (S : Finset (Fin d)) :
              (∑ T ∈ U, if β S = β T then gam S * gam T else 0) =
                gam S * cc (β S) := by
            calc
              (∑ T ∈ U, if β S = β T then gam S * gam T else 0) =
                  ∑ T ∈ U.filter (fun T => β T = β S),
                    gam S * gam T := by
                      rw [Finset.sum_filter]
                      apply Finset.sum_congr rfl
                      intro t ht
                      by_cases h : β t = β S
                      · simp only [h, ↓reduceIte]
                      · have hh : ¬ β S = β t := by intro he'; exact h he'.symm
                        simp [h, hh]
              _ = gam S * cc (β S) := by
                    dsimp [cc]
                    rw [Finset.mul_sum]
          have hgroup :
              (∑ z ∈ V, cc z * cc z) =
                ∑ S ∈ U, gam S * cc (β S) := by
            calc
              (∑ z ∈ V, cc z * cc z) =
                  ∑ z ∈ V, ∑ S ∈ U.filter (fun S => β S = z),
                    gam S * cc z := by
                      apply Finset.sum_congr rfl
                      intro z hz
                      dsimp [cc]
                      rw [Finset.sum_mul]
              _ = ∑ z ∈ V, ∑ S ∈ U,
                    if β S = z then gam S * cc z else 0 := by
                      apply Finset.sum_congr rfl
                      intro z hz
                      rw [Finset.sum_filter]
              _ = ∑ S ∈ U, ∑ z ∈ V,
                    if β S = z then gam S * cc z else 0 := by
                      rw [Finset.sum_comm]
              _ = ∑ S ∈ U, gam S * cc (β S) := by
                      apply Finset.sum_congr rfl
                      intro S hS
                      have hmem : β S ∈ V :=
                        Finset.mem_image.mpr ⟨S, hS, rfl⟩
                      classical
                      calc
                        (∑ z ∈ V,
                          if β S = z then gam S * cc z else 0) =
                            (if β S = β S then
                              gam S * cc (β S) else 0) := by
                                apply Finset.sum_eq_single_of_mem (β S) hmem
                                intro z hz hne
                                have h : ¬ β S = z := by
                                  intro h'
                                  exact hne h'.symm
                                simp [h]
                        _ = gam S * cc (β S) := by simp
          dsimp [b0]
          -- turn squares into products and use the preceding grouping twice
          rw [show (∑ z ∈ V, cc z ^ (2:ℕ)) =
                ∑ z ∈ V, cc z * cc z by
                  apply Finset.sum_congr rfl
                  intro z hz
                  rw [pow_two]]
          rw [hgroup]
          -- ungroup the second variable, then identify a filtered product
          -- with the product-finset sum
          dsimp [D, vv, aa0]
          rw [Finset.sum_filter]
          rw [Finset.sum_product]
          apply Finset.sum_congr rfl
          intro S hS
          -- the equality test `β S - β T = 0` is `β S = β T`
          simpa [sub_eq_zero] using (hone S).symm

        -- expansion of the analytic exponential product
        have hexp :
            (∏ i : Fin d, ((k : ℂ) * Complex.exp (x i) + 1)) =
              ∑ S ∈ U, (k : ℂ) ^ S.card * Complex.exp (β S) := by
          classical
          dsimp [U]
          rw [Finset.prod_add (fun i : Fin d =>
                (k : ℂ) * Complex.exp (x i)) (fun _ => (1 : ℂ))]
          apply Finset.sum_congr rfl
          intro S hS
          simp [Finset.prod_mul_distrib, ← Complex.exp_sum, β]
        have hexpn :
            (∏ i : Fin d, ((k : ℂ) * Complex.exp (-(x i)) + 1)) =
              ∑ S ∈ U, (k : ℂ) ^ S.card * Complex.exp (-(β S)) := by
          classical
          dsimp [U]
          rw [Finset.prod_add (fun i : Fin d =>
                (k : ℂ) * Complex.exp (-(x i))) (fun _ => (1 : ℂ))]
          apply Finset.sum_congr rfl
          intro S hS
          simp [Finset.prod_mul_distrib, ← Complex.exp_sum, β,
            Finset.sum_neg_distrib]
        have hprod0 :
            (∏ i : Fin d, ((k : ℂ) * Complex.exp (x i) + 1)) = 0 := by
          obtain ⟨i, hi⟩ := hxw
          apply Finset.prod_eq_zero (Finset.mem_univ i)
          rw [hi, he]
          exact hfac
        have htotal :
            (∑ q ∈ D, (aa0 q : ℂ) * Complex.exp (vv q)) = 0 := by
          dsimp [D]
          rw [Finset.sum_product]
          calc
            (∑ S ∈ U, ∑ T ∈ U,
              (aa0 (S,T) : ℂ) * Complex.exp (vv (S,T))) =
                (∑ S ∈ U, (k : ℂ)^S.card * Complex.exp (β S)) *
                  (∑ T ∈ U, (k : ℂ)^T.card * Complex.exp (-(β T))) := by
                    rw [Finset.sum_mul]
                    apply Finset.sum_congr rfl
                    intro S hS
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro T hT
                    dsimp [aa0, gam, vv]
                    push_cast
                    rw [sub_eq_add_neg, Complex.exp_add]
                    ring_nf
            _ = 0 := by rw [← hexp, ← hexpn, hprod0, zero_mul]
        have hzeroCast :
            (b0 : ℂ) =
              ∑ q ∈ D.filter (fun q => vv q = 0),
                (aa0 q : ℂ) * Complex.exp (vv q) := by
          calc
            (b0 : ℂ) =
                ((∑ q ∈ D.filter (fun q => vv q = 0), aa0 q : ℤ) : ℂ) := by
                  rw [hbsum]
            _ = ∑ q ∈ D.filter (fun q => vv q = 0), (aa0 q : ℂ) := by
                  push_cast
                  rfl
            _ = _ := by
                  apply Finset.sum_congr rfl
                  intro q hq
                  have hz : vv q = 0 := (Finset.mem_filter.mp hq).2
                  simp [hz]
        have hrelNZ :
            (b0 : ℂ) +
              ∑ q ∈ NZ, (aa0 q : ℂ) * Complex.exp (vv q) = 0 := by
          have hh := Finset.sum_filter_add_sum_filter_not
            D (fun q => vv q = 0)
              (fun q => (aa0 q : ℂ) * Complex.exp (vv q))
          rw [← hzeroCast] at hh
          have hnzEq : D.filter (fun q => ¬ vv q = 0) = NZ := by
            ext q
            simp [NZ]
          rw [hnzEq, htotal] at hh
          exact hh

        -- index the non-zero pairs by a `Fin`; this retains all multiplicity
        let m : ℕ := Fintype.card {q // q ∈ NZ}
        let ee : Fin m ≃ {q // q ∈ NZ} :=
          (Fintype.equivFin {q // q ∈ NZ}).symm
        let u : Fin m → ℂ := fun j => vv (ee j).1
        let a : Fin m → ℤ := fun j => aa0 (ee j).1
        have hindex (F : (Finset (Fin d) × Finset (Fin d)) → ℂ) :
            (∑ j : Fin m, F (ee j).1) = ∑ q ∈ NZ, F q := by
          calc
            (∑ j : Fin m, F (ee j).1) =
                ∑ q : {q // q ∈ NZ}, F q.1 :=
                  Equiv.sum_comp ee (fun q : {q // q ∈ NZ} => F q.1)
            _ = _ := by
              symm
              exact Finset.sum_subtype NZ (fun q => Iff.rfl) F
        refine ⟨m, u, a, b0, hbne, ?_, ?_, ?_, ?_⟩
        · intro j
          dsimp [u]
          rcases (ee j).2 with hj
          have hmem := (Finset.mem_filter.mp hj).1
          have h1 : (ee j).1.1 ∈ U :=
            (Finset.mem_product.mp hmem).1
          have h2 : (ee j).1.2 ∈ U :=
            (Finset.mem_product.mp hmem).2
          dsimp [vv]
          exact (hβint _).sub (hβint _)
        · intro j
          dsimp [u]
          exact (Finset.mem_filter.mp (ee j).2).2
        · -- the exponential relation
          change (b0 : ℂ) +
            ∑ j : Fin m,
              (aa0 (ee j).1 : ℂ) * Complex.exp (vv (ee j).1) = 0
          rw [hindex (fun q => (aa0 q : ℂ) * Complex.exp (vv q))]
          exact hrelNZ
        · intro G
          obtain ⟨tt, htt⟩ :=
            symmetric_eval_on_monic_roots P hPmon d x hxR
              (pairSubsetPoly d k G) (pairSubsetPoly_symmetric d k G)
          have htotalG : (tt : ℂ) =
              ∑ q ∈ D,
                (aa0 q : ℂ) * Polynomial.aeval (vv q) G := by
            rw [pairSubsetPoly_eval] at htt
            rw [htt]
            dsimp [D]
            rw [Finset.sum_product]
            apply Finset.sum_congr rfl
            intro S hS
            apply Finset.sum_congr rfl
            intro T hT
            dsimp [aa0, gam, vv, β]
            push_cast
            ring
          have hzeroG :
              ∑ q ∈ D.filter (fun q => vv q = 0),
                  (aa0 q : ℂ) * Polynomial.aeval (vv q) G =
                (b0 : ℂ) * ((G.eval (0 : ℤ) : ℤ) : ℂ) := by
            have hev0 : Polynomial.aeval (0 : ℂ) G =
                ((G.eval (0 : ℤ) : ℤ) : ℂ) := by
              simpa using
                (Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval
                  (R := ℤ) (A := ℂ) (0 : ℤ) G)
            calc
              (∑ q ∈ D.filter (fun q => vv q = 0),
                  (aa0 q : ℂ) * Polynomial.aeval (vv q) G) =
                (∑ q ∈ D.filter (fun q => vv q = 0), (aa0 q : ℂ)) *
                  ((G.eval (0 : ℤ) : ℤ) : ℂ) := by
                    rw [Finset.sum_mul]
                    apply Finset.sum_congr rfl
                    intro q hq
                    have hz : vv q = 0 := (Finset.mem_filter.mp hq).2
                    simp [hz, hev0]
              _ = _ := by
                    have hzsum : (∑ q ∈ D.filter (fun q => vv q = 0),
                          (aa0 q : ℂ)) = (b0 : ℂ) := by
                      symm
                      calc
                        (b0 : ℂ) =
                            ((∑ q ∈ D.filter (fun q => vv q = 0), aa0 q : ℤ) : ℂ) := by
                              rw [hbsum]
                        _ = _ := by
                              push_cast
                              rfl
                    rw [hzsum]
          have hgnz :
              (∑ q ∈ NZ, (aa0 q : ℂ) * Polynomial.aeval (vv q) G) =
                (tt : ℂ) - (b0 : ℂ) * ((G.eval (0 : ℤ) : ℤ) : ℂ) := by
            have hsp := Finset.sum_filter_add_sum_filter_not
              D (fun q => vv q = 0)
                (fun q => (aa0 q : ℂ) * Polynomial.aeval (vv q) G)
            have hnzEq : D.filter (fun q => ¬ vv q = 0) = NZ := by
              ext q
              simp [NZ]
            rw [hnzEq, htotalG.symm, hzeroG] at hsp
            linear_combination hsp
          refine ⟨tt - b0 * G.eval (0 : ℤ), ?_⟩
          change (((tt - b0 * G.eval (0 : ℤ) : ℤ) : ℂ)) =
            ∑ j : Fin m,
              (aa0 (ee j).1 : ℂ) * Polynomial.aeval (vv (ee j).1) G
          rw [hindex (fun q =>
            (aa0 q : ℂ) * Polynomial.aeval (vv q) G)]
          push_cast
          -- use the just computed non-zero part
          simpa using hgnz.symm

  have himpossible (ε : ℂ) (hε : ε = (1 : ℂ) ∨ ε = (-1 : ℂ))
      (he : Complex.exp w = ε) : False := by
    obtain ⟨m, u, a, b, hb, hu, hu0, hrel, hint⟩ := hsymmetric ε hε he
    obtain ⟨F, hF, hFu⟩ := polynomial_for_integral_family (Fin m) u hu hu0
    exact no_integer_exponential_relation (Fin m) u a b hb F hF hFu hrel hint
  constructor
  · intro h
    exact himpossible 1 (Or.inl rfl) h
  · intro h
    exact himpossible (-1) (Or.inr rfl) h

lemma algZ_exp_not_neg_one {z : ℂ} (hz : IsAlgebraic ℤ z) (hz0 : z ≠ 0) :
    Complex.exp z ≠ (-1:ℂ) := by
  intro he
  obtain ⟨y, hy, hyi⟩ := hz.exists_integral_multiple
  have hyc : (y:ℂ) ≠ 0 := by
    exact_mod_cast hy
  have hwy : (y • z) ≠ (0:ℂ) := by
    rw [Algebra.smul_def]
    exact mul_ne_zero hyc hz0
  obtain ⟨hnotone, hnotneg⟩ := lindemann_integral_obstruction hyi hwy
  have ee : Complex.exp (y • z) = (-1:ℂ)^y := by
    rw [Algebra.smul_def]
    change Complex.exp ((y:ℂ) * z) = _
    rw [Complex.exp_int_mul z y, he]
  have hsquare : (((-1:ℂ)^y)) ^ (2:ℕ) = 1 := by
    -- square of any integral power of -1
    change (((-1:ℂ)^y)) ^ (2:ℤ) = 1
    rw [← zpow_mul]
    rw [mul_comm]
    rw [zpow_mul]
    norm_num
  have hor : ((-1:ℂ)^y) = 1 ∨ ((-1:ℂ)^y) = -1 := sq_eq_one_iff.mp (by
    exact hsquare)
  rcases hor with h | h
  · exact hnotone (ee.trans h)
  · exact hnotneg (ee.trans h)

lemma transcendental_pi_real : Transcendental ℤ Real.pi := by
  intro hpi
  have hzc : IsAlgebraic ℤ (Real.pi:ℂ) := algebraicZ_complex_of_real hpi
  have hz : IsAlgebraic ℤ ((Real.pi:ℂ) * Complex.I) := hzc.mul algebraic_I_Z
  have hnz : (Real.pi:ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) Complex.I_ne_zero
  exact algZ_exp_not_neg_one hz hnz Complex.exp_pi_mul_I

end
/-ResultProofDefinitionsEnd-/


theorem lindemann :
    Transcendental ℤ (Real.exp 1) ∧ Transcendental ℤ Real.pi :=  by
  exact ⟨transcendental_exp_one_real, transcendental_pi_real⟩


end Submission
