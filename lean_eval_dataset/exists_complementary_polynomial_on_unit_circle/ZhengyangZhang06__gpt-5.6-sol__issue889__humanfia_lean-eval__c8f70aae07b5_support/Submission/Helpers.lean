import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Polynomial
open Filter Topology
open scoped ComplexConjugate
open scoped Topology

noncomputable section

namespace Submission.Helpers

def cayley (n : ℕ) (p : ℂ[X]) : ℂ[X] :=
  MvPolynomial.aeval ![X - C Complex.I, X + C Complex.I] (p.homogenize n)

def conjPoly (p : ℂ[X]) : ℂ[X] := p.map (starRingEnd ℂ)

@[simp] lemma conjPoly_conjPoly (p : ℂ[X]) : conjPoly (conjPoly p) = p := by
  ext n
  simp [conjPoly]

lemma eval_conjPoly_ofReal (p : ℂ[X]) (x : ℝ) :
    (conjPoly p).eval (x : ℂ) = conj (p.eval (x : ℂ)) := by
  simpa [conjPoly] using p.eval_map_apply (starRingEnd ℂ) (x : ℂ)

lemma cayley_eq_sum (p : ℂ[X]) (n : ℕ) :
    cayley n p =
      ∑ ij ∈ Finset.antidiagonal n,
        C (p.coeff ij.1) * (X - C Complex.I) ^ ij.1 * (X + C Complex.I) ^ ij.2 := by
  simp [cayley, Polynomial.homogenize, MvPolynomial.aeval_def]
  simp only [mul_assoc]

lemma natDegree_cayley_le (p : ℂ[X]) (n : ℕ) : (cayley n p).natDegree ≤ n := by
  rw [cayley_eq_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro ij hij
  rw [Finset.mem_antidiagonal] at hij
  calc
    (C (p.coeff ij.1) * (X - C Complex.I : ℂ[X]) ^ ij.1 *
        (X + C Complex.I : ℂ[X]) ^ ij.2).natDegree
        ≤ ((X - C Complex.I : ℂ[X]) ^ ij.1 *
          (X + C Complex.I : ℂ[X]) ^ ij.2).natDegree := by
          rw [mul_assoc]
          exact Polynomial.natDegree_C_mul_le _ _
    _ ≤ ((X - C Complex.I : ℂ[X]) ^ ij.1).natDegree +
        ((X + C Complex.I : ℂ[X]) ^ ij.2).natDegree := Polynomial.natDegree_mul_le
    _ ≤ ij.1 * (X - C Complex.I : ℂ[X]).natDegree +
        ij.2 * (X + C Complex.I : ℂ[X]).natDegree :=
          Nat.add_le_add Polynomial.natDegree_pow_le Polynomial.natDegree_pow_le
    _ ≤ ij.1 * 1 + ij.2 * 1 := by
          gcongr <;> simp
    _ = n := by omega

lemma cayley_mul (p q : ℂ[X]) (m n : ℕ) (hp : p.natDegree ≤ m)
    (hq : q.natDegree ≤ n) :
    cayley (m + n) (p * q) = cayley m p * cayley n q := by
  simp [cayley, Polynomial.homogenize_mul p q hp hq]

lemma cayley_sub (p q : ℂ[X]) (n : ℕ) :
    cayley n (p - q) = cayley n p - cayley n q := by
  simp [cayley, Polynomial.homogenize_sub]

lemma cayley_X_pow (n : ℕ) :
    cayley (2 * n) (X ^ n : ℂ[X]) = (X ^ 2 + 1) ^ n := by
  simp [cayley, two_mul, MvPolynomial.aeval_def]
  rw [← mul_pow]
  congr 1
  calc
    (X - C Complex.I) * (X + C Complex.I) = X ^ 2 - (C Complex.I) ^ 2 := by ring
    _ = X ^ 2 + 1 := by rw [← map_pow, Complex.I_sq]; simp

lemma cayley_star (p : ℂ[X]) (n : ℕ) :
    cayley n ((conjPoly p).reflect n) = conjPoly (cayley n p) := by
  simp [cayley, Polynomial.homogenize, MvPolynomial.aeval_def, conjPoly]
  rw [Polynomial.map_sum]
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C]
  simp_rw [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
  simp only [show (starRingEnd ℂ) Complex.I = -Complex.I by simp, C_neg,
    sub_neg_eq_add]
  conv_rhs => rw [← Finset.Nat.sum_antidiagonal_swap]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [Finset.mem_antidiagonal] at hij
  rw [Polynomial.revAt_le (by omega)]
  simp only [Prod.swap]
  have hsub : n - ij.1 = ij.2 := by omega
  rw [hsub]
  ring

lemma conjPoly_sub (p q : ℂ[X]) : conjPoly (p - q) = conjPoly p - conjPoly q := by
  simp [conjPoly, Polynomial.map_sub]

lemma conjPoly_mul (p q : ℂ[X]) : conjPoly (p * q) = conjPoly p * conjPoly q := by
  simp [conjPoly, Polynomial.map_mul]

lemma conjPoly_X_sq_add_one_pow (n : ℕ) :
    conjPoly ((X ^ 2 + 1 : ℂ[X]) ^ n) = (X ^ 2 + 1) ^ n := by
  simp [conjPoly, Polynomial.map_pow, Polynomial.map_add]

lemma eval_cayley (p : ℂ[X]) (n : ℕ) (t : ℂ) (hp : p.natDegree ≤ n)
    (ht : t + Complex.I ≠ 0) :
    (cayley n p).eval t = p.eval ((t - Complex.I) / (t + Complex.I)) * (t + Complex.I) ^ n := by
  simp only [cayley, MvPolynomial.aeval_def]
  change (Polynomial.evalRingHom t)
      ((MvPolynomial.eval₂Hom (algebraMap ℂ ℂ[X])
        ![X - C Complex.I, X + C Complex.I]) (p.homogenize n)) = _
  rw [MvPolynomial.map_eval₂Hom]
  convert Polynomial.eval_homogenize hp ![t - Complex.I, t + Complex.I]
      (by simpa using ht) using 1
  rw [← MvPolynomial.eval₂_id]
  change MvPolynomial.eval₂ ((Polynomial.evalRingHom t).comp (algebraMap ℂ ℂ[X]))
      (fun i => Polynomial.eval t (![X - C Complex.I, X + C Complex.I] i))
      (p.homogenize n) = _
  rw [show (Polynomial.evalRingHom t).comp (algebraMap ℂ ℂ[X]) = RingHom.id ℂ by
    ext x
    simp]
  apply MvPolynomial.eval₂_congr
  intro i _ _
  fin_cases i <;> simp
  simp

lemma cayley_injective_on {p q : ℂ[X]} {n : ℕ} (hp : p.natDegree ≤ n)
    (hq : q.natDegree ≤ n) (h : cayley n p = cayley n q) : p = q := by
  apply Polynomial.eq_of_infinite_eval_eq p q
  refine (Set.finite_singleton (1 : ℂ)).infinite_compl.mono ?_
  intro z hz
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
  let t := Complex.I * (1 + z) / (1 - z)
  have hzden : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have ht : t + Complex.I ≠ 0 := by
    have ht_eq : t + Complex.I = 2 * Complex.I / (1 - z) := by
      dsimp [t]
      field_simp [hzden]
      ring
    rw [ht_eq]
    exact div_ne_zero (by norm_num) hzden
  have hfrac : (t - Complex.I) / (t + Complex.I) = z := by
    dsimp [t]
    field_simp [hzden]
    ring
  have he := congr_arg (Polynomial.eval t) h
  rw [eval_cayley p n t hp ht, eval_cayley q n t hq ht, hfrac] at he
  exact mul_right_cancel₀ (pow_ne_zero n ht) he

lemma exists_conj_factor : ∀ n : ℕ, ∀ f : ℝ[X],
    (∀ x : ℝ, 0 ≤ f.eval x) → f.natDegree ≤ 2 * n →
      ∃ q : ℂ[X], q.natDegree ≤ n ∧ q * conjPoly q = f.map (algebraMap ℝ ℂ) := by
  intro n
  induction n with
  | zero =>
      intro f hf hdeg
      let c := f.eval 0
      have hc : 0 ≤ c := hf 0
      have hdeg0 : f.natDegree = 0 := Nat.eq_zero_of_le_zero (by simpa using hdeg)
      have hfC : f = C c := by
        simpa [c, coeff_zero_eq_eval_zero] using eq_C_of_natDegree_eq_zero hdeg0
      refine ⟨C (Real.sqrt c : ℂ), by simp, ?_⟩
      rw [hfC]
      simp only [conjPoly, Polynomial.map_C, Complex.conj_ofReal]
      rw [← C_mul]
      congr 1
      change (↑(Real.sqrt c) : ℂ) * ↑(Real.sqrt c) = (↑c : ℂ)
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc]
  | succ n ih =>
      intro f hf hdeg
      by_cases hsmall : f.natDegree ≤ 2 * n
      · obtain ⟨q, hqdeg, hq⟩ := ih f hf hsmall
        exact ⟨q, hqdeg.trans (Nat.le_succ n), hq⟩
      have hf0 : f ≠ 0 := by
        intro hzero
        apply hsmall
        simp [hzero]
      have hnatpos : 0 < f.natDegree := by omega
      have hdegree : 0 < f.degree := natDegree_pos_iff_degree_pos.mp hnatpos
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ f hdegree.ne'
      by_cases hzim : z.im = 0
      · let a := z.re
        have hza : (a : ℂ) = z := by
          apply Complex.ext
          · rfl
          · simpa [a] using hzim.symm
        have hroot : f.IsRoot a := by
          rw [← hza] at hz
          change (aeval (algebraMap ℝ ℂ a)) f = 0 at hz
          rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval] at hz
          exact (algebraMap ℝ ℂ).injective (by simpa using hz)
        have hlocal : IsLocalMin f.eval a := by
          apply Filter.Eventually.of_forall
          intro x
          change f.eval a ≤ f.eval x
          rw [hroot.eq_zero]
          exact hf x
        have hderiv : f.derivative.IsRoot a :=
          hlocal.hasDerivAt_eq_zero (f.hasDerivAt a)
        have hmult : 2 ≤ f.rootMultiplicity a := by
          have := (one_lt_rootMultiplicity_iff_isRoot hf0).2 ⟨hroot, hderiv⟩
          omega
        obtain ⟨g, hfg⟩ := (le_rootMultiplicity_iff hf0).1 hmult
        let d : ℝ[X] := (X - C a) ^ 2
        have hfactor : f = d * g := by simpa [d] using hfg
        have hd0 : d ≠ 0 := pow_ne_zero 2 (X_sub_C_ne_zero a)
        have hg0 : g ≠ 0 := by
          intro hg
          apply hf0
          simp [hfactor, hg]
        have hgdeg : g.natDegree ≤ 2 * n := by
          rw [hfactor, natDegree_mul hd0 hg0] at hdeg
          have hddeg : d.natDegree = 2 := by simp [d]
          omega
        have hg_ne (x : ℝ) (hxa : x ≠ a) : 0 ≤ g.eval x := by
          have hx := hf x
          rw [hfactor, eval_mul] at hx
          have hdpos : 0 < d.eval x := by
            simpa [d] using sq_pos_of_ne_zero (sub_ne_zero.mpr hxa)
          exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hx) hdpos
        have hg : ∀ x : ℝ, 0 ≤ g.eval x := by
          intro x
          by_cases hxa : x = a
          · subst x
            have htend : Tendsto g.eval (𝓝[≠] a) (𝓝 (g.eval a)) :=
              g.continuous.continuousAt.tendsto.mono_left inf_le_left
            have hevent : ∀ᶠ x in 𝓝[≠] a, g.eval x ∈ Set.Ici 0 := by
              filter_upwards [self_mem_nhdsWithin] with x hx
              exact hg_ne x (by simpa using hx)
            exact isClosed_Ici.mem_of_tendsto htend hevent
          · exact hg_ne x hxa
        obtain ⟨q, hqdeg, hq⟩ := ih g hg hgdeg
        let l : ℂ[X] := X - C (a : ℂ)
        refine ⟨l * q, ?_, ?_⟩
        · calc
            (l * q).natDegree ≤ l.natDegree + q.natDegree := natDegree_mul_le
            _ ≤ 1 + n := Nat.add_le_add (by simp [l]) hqdeg
            _ = n + 1 := by omega
        · rw [hfactor, Polynomial.map_mul]
          calc
            l * q * conjPoly (l * q) = (l * conjPoly l) * (q * conjPoly q) := by
              simp [conjPoly, Polynomial.map_mul]
              ring
            _ = (l * conjPoly l) * Polynomial.map (algebraMap ℝ ℂ) g := by rw [hq]
            _ = Polynomial.map (algebraMap ℝ ℂ) d *
                Polynomial.map (algebraMap ℝ ℂ) g := by
              congr 1
              simp [l, d, conjPoly]
              ring
      · let d : ℝ[X] := X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2)
        obtain ⟨g, hfg⟩ := f.quadratic_dvd_of_aeval_eq_zero_im_ne_zero hz hzim
        have hfactor : f = d * g := by simpa [d] using hfg
        have hddeg : d.natDegree = 2 := by
          dsimp [d]
          compute_degree <;> norm_num
        have hd0 : d ≠ 0 := by
          intro hd
          rw [hd, natDegree_zero] at hddeg
          omega
        have hg0 : g ≠ 0 := by
          intro hg
          apply hf0
          simp [hfactor, hg]
        have hgdeg : g.natDegree ≤ 2 * n := by
          rw [hfactor, natDegree_mul hd0 hg0] at hdeg
          omega
        have hdpos (x : ℝ) : 0 < d.eval x := by
          simp only [d, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
          nlinarith [sq_nonneg (x - z.re), sq_pos_of_ne_zero hzim]
        have hg : ∀ x : ℝ, 0 ≤ g.eval x := by
          intro x
          have hx := hf x
          rw [hfactor, eval_mul] at hx
          exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hx) (hdpos x)
        obtain ⟨q, hqdeg, hq⟩ := ih g hg hgdeg
        let l : ℂ[X] := X - C (conj z)
        refine ⟨l * q, ?_, ?_⟩
        · calc
            (l * q).natDegree ≤ l.natDegree + q.natDegree := natDegree_mul_le
            _ ≤ 1 + n := Nat.add_le_add (by simp [l]) hqdeg
            _ = n + 1 := by omega
        · rw [hfactor, Polynomial.map_mul]
          have hdmap : d.map (algebraMap ℝ ℂ) =
              (X - C (conj z)) * (X - C z) := by
            calc
              d.map (algebraMap ℝ ℂ) =
                  X ^ 2 - C (↑(2 * z.re) : ℂ) * X + C ((‖z‖ : ℂ) ^ 2) := by
                    simp [d]
              _ = (X - C (conj z)) * (X - C z) := by
                rw [← Complex.add_conj, map_add, ← Complex.mul_conj', map_mul]
                ring
          calc
            l * q * conjPoly (l * q) = (l * conjPoly l) * (q * conjPoly q) := by
              simp [conjPoly, Polynomial.map_mul]
              ring
            _ = (l * conjPoly l) * Polynomial.map (algebraMap ℝ ℂ) g := by rw [hq]
            _ = Polynomial.map (algebraMap ℝ ℂ) d *
                Polynomial.map (algebraMap ℝ ℂ) g := by
              rw [hdmap]
              simp [l, conjPoly]

noncomputable def realPartPoly (p : ℂ[X]) : ℝ[X] :=
  p.sum fun n z => monomial n z.re

@[simp] lemma coeff_realPartPoly (p : ℂ[X]) (n : ℕ) :
    (realPartPoly p).coeff n = (p.coeff n).re := by
  classical
  rw [realPartPoly, coeff_sum]
  simp only [coeff_monomial]
  rw [sum_def]
  by_cases hn : n ∈ p.support
  · rw [Finset.sum_eq_single n]
    · simp
    · intro m hm hmn
      simp [hmn]
    · exact fun h => (h hn).elim
  · rw [Finset.sum_eq_zero]
    · have hcoeff : p.coeff n = 0 := by
        by_contra hne
        exact hn (mem_support_iff.mpr hne)
      rw [hcoeff]
      simp
    · intro m hm
      have hmn : m ≠ n := by
        intro h
        exact hn (h ▸ hm)
      simp [hmn]

lemma natDegree_realPartPoly_le (p : ℂ[X]) :
    (realPartPoly p).natDegree ≤ p.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  simp [coeff_eq_zero_of_natDegree_lt hn]

lemma map_realPartPoly_eq_of_conjPoly_eq {p : ℂ[X]} (hp : conjPoly p = p) :
    (realPartPoly p).map (algebraMap ℝ ℂ) = p := by
  ext n
  have hc := congr_arg (Polynomial.coeff · n) hp
  simp [conjPoly] at hc
  have him : (p.coeff n).im = 0 := by
    have hi := congr_arg Complex.im hc
    simp at hi
    linarith
  apply Complex.ext
  · simp
  · simp [him]

lemma natDegree_conjPoly (p : ℂ[X]) : (conjPoly p).natDegree = p.natDegree := by
  simp [conjPoly]

lemma natDegree_star_le (p : ℂ[X]) (n : ℕ) (hp : p.natDegree ≤ n) :
    ((conjPoly p).reflect n).natDegree ≤ n := by
  refine natDegree_reflect_le.trans ?_
  simp [natDegree_conjPoly, hp]

lemma cayley_residual_formula (p : ℂ[X]) (n : ℕ) (hp : p.natDegree ≤ n) :
    cayley (2 * n) (X ^ n - p * (conjPoly p).reflect n) =
      (X ^ 2 + 1) ^ n - cayley n p * conjPoly (cayley n p) := by
  rw [cayley_sub, cayley_X_pow]
  have hs : ((conjPoly p).reflect n).natDegree ≤ n := natDegree_star_le p n hp
  have hmul := cayley_mul p ((conjPoly p).reflect n) n n hp hs
  rw [show n + n = 2 * n by omega] at hmul
  rw [hmul, show cayley n ((conjPoly p).reflect n) = conjPoly (cayley n p) by
    exact cayley_star p n]

lemma conjPoly_cayley_residual (p : ℂ[X]) (n : ℕ) (hp : p.natDegree ≤ n) :
    conjPoly (cayley (2 * n) (X ^ n - p * (conjPoly p).reflect n)) =
      cayley (2 * n) (X ^ n - p * (conjPoly p).reflect n) := by
  rw [cayley_residual_formula p n hp]
  rw [conjPoly_sub, conjPoly_mul, conjPoly_X_sq_add_one_pow, conjPoly_conjPoly]
  ring

noncomputable def realCayleyCircle (x : ℝ) : Circle :=
  ⟨((x : ℂ) - Complex.I) / ((x : ℂ) + Complex.I), by
    change ((x : ℂ) - Complex.I) / ((x : ℂ) + Complex.I) ∈ Metric.sphere 0 1
    rw [mem_sphere_zero_iff_norm]
    rw [norm_div]
    have hminus : ‖(x : ℂ) - Complex.I‖ = Real.sqrt (x ^ 2 + 1) := by
      calc
        ‖(x : ℂ) - Complex.I‖ = ‖(x : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I‖ := by
          congr 1
          norm_num
          ring
        _ = Real.sqrt (x ^ 2 + (-1 : ℝ) ^ 2) := Complex.norm_add_mul_I x (-1)
        _ = Real.sqrt (x ^ 2 + 1) := by norm_num
    have hplus : ‖(x : ℂ) + Complex.I‖ = Real.sqrt (x ^ 2 + 1) := by
      calc
        ‖(x : ℂ) + Complex.I‖ = ‖(x : ℂ) + ((1 : ℝ) : ℂ) * Complex.I‖ := by
          congr 1
          norm_num
        _ = Real.sqrt (x ^ 2 + (1 : ℝ) ^ 2) := Complex.norm_add_mul_I x 1
        _ = Real.sqrt (x ^ 2 + 1) := by norm_num
    rw [hminus, hplus, div_self]
    positivity⟩

@[simp] lemma coe_realCayleyCircle (x : ℝ) :
    (realCayleyCircle x : ℂ) = ((x : ℂ) - Complex.I) / ((x : ℂ) + Complex.I) := rfl

lemma normSq_pow (z : ℂ) (n : ℕ) : Complex.normSq (z ^ n) = Complex.normSq z ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, Complex.normSq_mul, ih]

noncomputable def residualReal (p : ℂ[X]) (n : ℕ) : ℝ[X] :=
  realPartPoly (cayley (2 * n) (X ^ n - p * (conjPoly p).reflect n))

lemma map_residualReal (p : ℂ[X]) (n : ℕ) (hp : p.natDegree ≤ n) :
    (residualReal p n).map (algebraMap ℝ ℂ) =
      cayley (2 * n) (X ^ n - p * (conjPoly p).reflect n) := by
  exact map_realPartPoly_eq_of_conjPoly_eq (conjPoly_cayley_residual p n hp)

lemma natDegree_residualReal_le (p : ℂ[X]) (n : ℕ) :
    (residualReal p n).natDegree ≤ 2 * n :=
  (natDegree_realPartPoly_le _).trans (natDegree_cayley_le _ _)

lemma residualReal_nonneg (p : ℂ[X]) (n : ℕ) (hp : p.natDegree ≤ n)
    (hbound : ∀ z : Circle, ‖p.eval (z : ℂ)‖ ≤ 1) (x : ℝ) :
    0 ≤ (residualReal p n).eval x := by
  let A := cayley n p
  let R := X ^ n - p * (conjPoly p).reflect n
  let S := cayley (2 * n) R
  have ht : (x : ℂ) + Complex.I ≠ 0 := by
    intro h
    have hi := congr_arg Complex.im h
    simp at hi
  have hA : A.eval (x : ℂ) =
      p.eval (realCayleyCircle x : ℂ) * ((x : ℂ) + Complex.I) ^ n := by
    simpa [A, coe_realCayleyCircle] using eval_cayley p n (x : ℂ) hp ht
  have hnormSqAdd : Complex.normSq ((x : ℂ) + Complex.I) = x ^ 2 + 1 := by
    convert Complex.normSq_add_mul_I x 1 using 1 <;> norm_num
  have hAnormSq : Complex.normSq (A.eval (x : ℂ)) =
      ‖p.eval (realCayleyCircle x : ℂ)‖ ^ 2 * (x ^ 2 + 1) ^ n := by
    rw [hA, Complex.normSq_mul, normSq_pow, hnormSqAdd,
      Complex.normSq_eq_norm_sq]
  have hSformula : S = (X ^ 2 + 1) ^ n - A * conjPoly A := by
    simpa [S, R, A] using cayley_residual_formula p n hp
  have hSeval : S.eval (x : ℂ) =
      (((x ^ 2 + 1) ^ n *
        (1 - ‖p.eval (realCayleyCircle x : ℂ)‖ ^ 2) : ℝ) : ℂ) := by
    calc
      S.eval (x : ℂ) = ((x : ℂ) ^ 2 + 1) ^ n -
          A.eval (x : ℂ) * conj (A.eval (x : ℂ)) := by
            rw [hSformula]
            simp [eval_conjPoly_ofReal]
      _ = (((x ^ 2 + 1) ^ n : ℝ) : ℂ) -
          (Complex.normSq (A.eval (x : ℂ)) : ℂ) := by
            rw [mul_comm, ← Complex.normSq_eq_conj_mul_self]
            norm_cast
      _ = (((x ^ 2 + 1) ^ n - Complex.normSq (A.eval (x : ℂ)) : ℝ) : ℂ) := by
            norm_cast
      _ = (((x ^ 2 + 1) ^ n *
          (1 - ‖p.eval (realCayleyCircle x : ℂ)‖ ^ 2) : ℝ) : ℂ) := by
            rw [hAnormSq]
            congr 1
            ring
  have hmap := map_residualReal p n hp
  have hrealEval : (residualReal p n).eval x =
      (x ^ 2 + 1) ^ n * (1 - ‖p.eval (realCayleyCircle x : ℂ)‖ ^ 2) := by
    apply (algebraMap ℝ ℂ).injective
    calc
      algebraMap ℝ ℂ ((residualReal p n).eval x) =
          ((residualReal p n).map (algebraMap ℝ ℂ)).eval (x : ℂ) := by
            simpa using ((residualReal p n).eval_map_apply (algebraMap ℝ ℂ) x).symm
      _ = S.eval (x : ℂ) := by simpa [S, R] using congr_arg (Polynomial.eval (x : ℂ)) hmap
      _ = _ := hSeval
  rw [hrealEval]
  exact mul_nonneg (by positivity) <| sub_nonneg.mpr <| by
    have hb := hbound (realCayleyCircle x)
    nlinarith [norm_nonneg (p.eval (realCayleyCircle x : ℂ))]

noncomputable def homogeneousSubst (n : ℕ) (p u v : ℂ[X]) : ℂ[X] :=
  MvPolynomial.aeval ![u, v] (p.homogenize n)

lemma natDegree_homogeneousSubst_le (n : ℕ) (p u v : ℂ[X])
    (hu : u.natDegree ≤ 1) (hv : v.natDegree ≤ 1) :
    (homogeneousSubst n p u v).natDegree ≤ n := by
  rw [show homogeneousSubst n p u v =
      ∑ ij ∈ Finset.antidiagonal n, C (p.coeff ij.1) * u ^ ij.1 * v ^ ij.2 by
    simp [homogeneousSubst, Polynomial.homogenize, MvPolynomial.aeval_def]
    simp only [mul_assoc]]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro ij hij
  rw [Finset.mem_antidiagonal] at hij
  calc
    (C (p.coeff ij.1) * u ^ ij.1 * v ^ ij.2).natDegree
        ≤ (u ^ ij.1 * v ^ ij.2).natDegree := by
          rw [mul_assoc]
          exact Polynomial.natDegree_C_mul_le _ _
    _ ≤ (u ^ ij.1).natDegree + (v ^ ij.2).natDegree := natDegree_mul_le
    _ ≤ ij.1 * u.natDegree + ij.2 * v.natDegree :=
      Nat.add_le_add natDegree_pow_le natDegree_pow_le
    _ ≤ ij.1 * 1 + ij.2 * 1 := by gcongr
    _ = n := by omega

lemma eval_homogeneousSubst (n : ℕ) (p u v : ℂ[X]) (z : ℂ)
    (hp : p.natDegree ≤ n) (hv : v.eval z ≠ 0) :
    (homogeneousSubst n p u v).eval z =
      p.eval (u.eval z / v.eval z) * v.eval z ^ n := by
  simp only [homogeneousSubst, MvPolynomial.aeval_def]
  change (Polynomial.evalRingHom z)
      ((MvPolynomial.eval₂Hom (algebraMap ℂ ℂ[X]) ![u, v]) (p.homogenize n)) = _
  rw [MvPolynomial.map_eval₂Hom]
  convert Polynomial.eval_homogenize hp ![u.eval z, v.eval z] (by simpa using hv) using 1
  · rw [← MvPolynomial.eval₂_id]
    change MvPolynomial.eval₂ ((Polynomial.evalRingHom z).comp (algebraMap ℂ ℂ[X]))
        (fun i => Polynomial.eval z (![u, v] i)) (p.homogenize n) = _
    rw [show (Polynomial.evalRingHom z).comp (algebraMap ℂ ℂ[X]) = RingHom.id ℂ by
      ext x
      simp]
    apply MvPolynomial.eval₂_congr
    intro i _ _
    fin_cases i <;> simp
  · simp

noncomputable def uncayley (n : ℕ) (p : ℂ[X]) : ℂ[X] :=
  C (((2 : ℂ) * Complex.I)⁻¹ ^ n) *
    homogeneousSubst n p (C Complex.I * (X + 1)) (1 - X)

lemma natDegree_uncayley_le (n : ℕ) (p : ℂ[X]) : (uncayley n p).natDegree ≤ n := by
  refine natDegree_C_mul_le _ _ |>.trans ?_
  apply natDegree_homogeneousSubst_le
  · exact (natDegree_C_mul_le _ _).trans <|
      (natDegree_add_le (X : ℂ[X]) 1).trans (by norm_num)
  · exact (natDegree_sub_le (1 : ℂ[X]) X).trans (by norm_num)

lemma cayley_uncayley {p : ℂ[X]} {n : ℕ} (hp : p.natDegree ≤ n) :
    cayley n (uncayley n p) = p := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine (Set.finite_singleton (-Complex.I)).infinite_compl.mono ?_
  intro t htmem
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at htmem
  change (cayley n (uncayley n p)).eval t = p.eval t
  have ht : t + Complex.I ≠ 0 := by
    intro h
    exact htmem (eq_neg_of_add_eq_zero_left h)
  let z := (t - Complex.I) / (t + Complex.I)
  have h1mz : 1 - z = 2 * Complex.I / (t + Complex.I) := by
    dsimp [z]
    field_simp [ht]
    ring
  have hv : 1 - z ≠ 0 := by
    rw [h1mz]
    exact div_ne_zero (by norm_num) ht
  have hratio : Complex.I * (z + 1) / (1 - z) = t := by
    dsimp [z]
    field_simp [ht]
    ring
  have hhom := eval_homogeneousSubst n p
    (C Complex.I * (X + 1)) (1 - X) z hp (by simpa using hv)
  have hunc : (uncayley n p).eval z =
      ((2 : ℂ) * Complex.I)⁻¹ ^ n * (p.eval t * (1 - z) ^ n) := by
    rw [uncayley, eval_mul, eval_C, hhom]
    simp only [eval_mul, eval_C, eval_add, eval_X, eval_one, eval_sub]
    rw [hratio]
  have hcancel :
      ((2 : ℂ) * Complex.I)⁻¹ ^ n *
          (((2 : ℂ) * Complex.I / (t + Complex.I)) ^ n) *
          (t + Complex.I) ^ n = 1 := by
    rw [← mul_pow, ← mul_pow]
    field_simp [ht]
    simp
  rw [eval_cayley (uncayley n p) n t (natDegree_uncayley_le n p) ht,
    hunc, h1mz]
  calc
    ((2 * Complex.I)⁻¹ ^ n) *
          (p.eval t * (2 * Complex.I / (t + Complex.I)) ^ n) *
          (t + Complex.I) ^ n =
        p.eval t * (((2 * Complex.I)⁻¹ ^ n) *
          (2 * Complex.I / (t + Complex.I)) ^ n *
          (t + Complex.I) ^ n) := by ring
    _ = p.eval t := by rw [hcancel, mul_one]

lemma eval_reflect_conjPoly_circle (p : ℂ[X]) (n : ℕ) (hp : p.natDegree ≤ n)
    (z : Circle) :
    ((conjPoly p).reflect n).eval (z : ℂ) =
      (z : ℂ) ^ n * conj (p.eval (z : ℂ)) := by
  have hcz : conj (z : ℂ) ≠ 0 := by simp
  letI : Invertible (conj (z : ℂ)) := invertibleOfNonzero hcz
  have hinv : ⅟ (conj (z : ℂ)) = (z : ℂ) := by
    rw [invOf_eq_inv]
    calc
      (conj (z : ℂ))⁻¹ = ((z⁻¹ : Circle) : ℂ)⁻¹ := by
        rw [Circle.coe_inv_eq_conj]
      _ = (((z⁻¹)⁻¹ : Circle) : ℂ) := (Circle.coe_inv (z⁻¹)).symm
      _ = (z : ℂ) := by simp
  have heval : (conjPoly p).eval (conj (z : ℂ)) =
      conj (p.eval (z : ℂ)) := by
    simp [conjPoly]
  have hreflect :
      ((conjPoly p).reflect n).eval (z : ℂ) * conj (z : ℂ) ^ n =
        conj (p.eval (z : ℂ)) := by
    simpa only [eval₂_id, hinv, heval] using
      eval₂_reflect_mul_pow (RingHom.id ℂ) (conj (z : ℂ)) n (conjPoly p)
        (by rw [natDegree_conjPoly]; exact hp)
  have hunit : conj (z : ℂ) * (z : ℂ) = 1 := by
    calc
      conj (z : ℂ) * (z : ℂ) = (Complex.normSq (z : ℂ) : ℂ) :=
        Complex.normSq_eq_conj_mul_self.symm
      _ = 1 := by norm_cast; exact Circle.normSq_coe z
  calc
    ((conjPoly p).reflect n).eval (z : ℂ) =
        ((conjPoly p).reflect n).eval (z : ℂ) * 1 := by ring
    _ = ((conjPoly p).reflect n).eval (z : ℂ) *
        (conj (z : ℂ) ^ n * (z : ℂ) ^ n) := by
          rw [← mul_pow, hunit, one_pow]
    _ = (((conjPoly p).reflect n).eval (z : ℂ) * conj (z : ℂ) ^ n) *
        (z : ℂ) ^ n := by ring
    _ = conj (p.eval (z : ℂ)) * (z : ℂ) ^ n := by rw [hreflect]
    _ = (z : ℂ) ^ n * conj (p.eval (z : ℂ)) := by ring

lemma exists_complementary_factor (p : ℂ[X]) (n : ℕ) (hp : p.natDegree ≤ n)
    (hbound : ∀ z : Circle, ‖p.eval (z : ℂ)‖ ≤ 1) :
    ∃ q : ℂ[X], q.natDegree ≤ n ∧
      X ^ n - p * (conjPoly p).reflect n = q * (conjPoly q).reflect n := by
  obtain ⟨a, hadeg, ha⟩ := exists_conj_factor n (residualReal p n)
    (residualReal_nonneg p n hp hbound) (natDegree_residualReal_le p n)
  let q := uncayley n a
  have hqdeg : q.natDegree ≤ n := natDegree_uncayley_le n a
  refine ⟨q, hqdeg, ?_⟩
  have hqstar : ((conjPoly q).reflect n).natDegree ≤ n :=
    natDegree_star_le q n hqdeg
  have hleftdeg : (X ^ n - p * (conjPoly p).reflect n).natDegree ≤ 2 * n := by
    have hX : (X ^ n : ℂ[X]).natDegree ≤ n := by simp
    have hpstar : (p * (conjPoly p).reflect n).natDegree ≤ n + n :=
      natDegree_mul_le.trans (Nat.add_le_add hp (natDegree_star_le p n hp))
    exact (natDegree_sub_le (X ^ n : ℂ[X]) (p * (conjPoly p).reflect n)).trans <|
      max_le (hX.trans (by omega)) (hpstar.trans (by omega))
  have hrightdeg : (q * (conjPoly q).reflect n).natDegree ≤ 2 * n :=
    natDegree_mul_le.trans <| (Nat.add_le_add hqdeg hqstar).trans (by omega)
  apply cayley_injective_on hleftdeg hrightdeg
  have hmul := cayley_mul q ((conjPoly q).reflect n) n n hqdeg hqstar
  rw [show n + n = 2 * n by omega] at hmul
  rw [hmul, cayley_star q n, cayley_uncayley hadeg]
  exact (map_residualReal p n hp).symm.trans ha.symm

theorem complementary_polynomial (P : ℂ[X])
    (hP : ∀ z : Circle, ‖P.eval (z : ℂ)‖ ≤ 1) :
    ∃ Q : ℂ[X],
      Q.natDegree ≤ P.natDegree ∧
        ∀ z : Circle, ‖P.eval (z : ℂ)‖ ^ 2 + ‖Q.eval (z : ℂ)‖ ^ 2 = 1 := by
  let n := P.natDegree
  obtain ⟨Q, hQdeg, hfactor⟩ := exists_complementary_factor P n (by simp [n]) hP
  refine ⟨Q, by simpa [n] using hQdeg, ?_⟩
  intro z
  have heval := congr_arg (Polynomial.eval (z : ℂ)) hfactor
  simp only [eval_sub, eval_pow, eval_X, eval_mul] at heval
  rw [eval_reflect_conjPoly_circle P n (by simp [n]),
    eval_reflect_conjPoly_circle Q n hQdeg] at heval
  have hcancel :
      1 - P.eval (z : ℂ) * conj (P.eval (z : ℂ)) =
        Q.eval (z : ℂ) * conj (Q.eval (z : ℂ)) := by
    apply mul_left_cancel₀ (pow_ne_zero n (Circle.coe_ne_zero z))
    calc
      (z : ℂ) ^ n *
          (1 - P.eval (z : ℂ) * conj (P.eval (z : ℂ))) =
        (z : ℂ) ^ n - P.eval (z : ℂ) *
          ((z : ℂ) ^ n * conj (P.eval (z : ℂ))) := by ring
      _ = Q.eval (z : ℂ) * ((z : ℂ) ^ n * conj (Q.eval (z : ℂ))) := heval
      _ = (z : ℂ) ^ n *
          (Q.eval (z : ℂ) * conj (Q.eval (z : ℂ))) := by ring
  have hPnorm : P.eval (z : ℂ) * conj (P.eval (z : ℂ)) =
      (Complex.normSq (P.eval (z : ℂ)) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  have hQnorm : Q.eval (z : ℂ) * conj (Q.eval (z : ℂ)) =
      (Complex.normSq (Q.eval (z : ℂ)) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  rw [hPnorm, hQnorm] at hcancel
  have hreal : 1 - Complex.normSq (P.eval (z : ℂ)) =
      Complex.normSq (Q.eval (z : ℂ)) := by
    simpa using congr_arg Complex.re hcancel
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  linarith

end Submission.Helpers
