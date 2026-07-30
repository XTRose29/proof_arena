import Mathlib

-- BEGIN INLINED FILE: Mathlib/Support/lindemann_weierstrass_047b40c6f1/Arithmetic.lean
open Polynomial
open scoped BigOperators
namespace LindemannSupport
noncomputable section
lemma norm_aux {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : ι → ℂ) (hb : Function.Injective b)
    (a : ι → ℤ) (i₀ : ι) (hb0 : b i₀ = 0)
    (N : ℤ) (p : ℕ) (gp : ℤ[X]) (E : ℝ)
    (hE : ∀ i : ι, b i ≠ 0 →
      ‖N • Complex.exp (b i) - p • Polynomial.aeval (b i) gp‖ ≤ E)
    (hzero : (∑ i, (a i : ℂ) * Complex.exp (b i)) = 0) :
    ‖(N : ℂ) * (a i₀ : ℂ) +
        ∑ i ∈ (Finset.univ.erase i₀),
           (a i : ℂ) * ((p : ℂ) * Polynomial.aeval (b i) gp)‖
      ≤ (∑ i ∈ (Finset.univ.erase i₀), ‖(a i : ℂ)‖) * E := by
  classical
  let s : Finset ι := Finset.univ.erase i₀
  have hbi {i : ι} (hi : i ∈ s) : b i ≠ 0 := by
    dsimp [s] at hi
    have hne : i ≠ i₀ := (Finset.mem_erase.mp hi).1
    intro hz
    exact hne (hb (hz.trans hb0.symm))
  -- split original vanishing relation
  have hrel : (a i₀ : ℂ) + ∑ i ∈ s, (a i : ℂ) * Complex.exp (b i) = 0 := by
    have hsplit := Finset.add_sum_erase (Finset.univ) (fun i : ι => (a i : ℂ) * Complex.exp (b i)) (Finset.mem_univ i₀)
    -- hsplit : term i₀ + ... = total
    simpa [s, hb0] using hsplit.trans hzero
  have hDelta :
      (N : ℂ) * (a i₀ : ℂ) +
          ∑ i ∈ s, (a i : ℂ) * ((p : ℂ) * Polynomial.aeval (b i) gp)
        = - ∑ i ∈ s, (a i : ℂ) *
            ((N : ℂ) * Complex.exp (b i) - (p : ℂ) * Polynomial.aeval (b i) gp) := by
    -- multiply hrel by N and rearrange sums
    -- use ring normal forms with sums
    calc
      (N : ℂ) * (a i₀ : ℂ) + ∑ i ∈ s, (a i : ℂ) * ((p : ℂ) * Polynomial.aeval (b i) gp)
          = -(N : ℂ) * (∑ i ∈ s, (a i : ℂ) * Complex.exp (b i))
              + ∑ i ∈ s, (a i : ℂ) * ((p : ℂ) * Polynomial.aeval (b i) gp) := by
                have hiso : (a i₀ : ℂ) = - ∑ i ∈ s, (a i : ℂ) * Complex.exp (b i) :=
                  eq_neg_of_add_eq_zero_left hrel
                rw [hiso]
                ring
      _ = - ∑ i ∈ s, (a i : ℂ) *
            ((N : ℂ) * Complex.exp (b i) - (p : ℂ) * Polynomial.aeval (b i) gp) := by
          -- distribute sums
          simp_rw [Finset.mul_sum]
          rw [← Finset.sum_neg_distrib]
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          ring
  rw [show Finset.univ.erase i₀ = s by rfl]
  rw [hDelta]
  rw [norm_neg]
  refine (norm_sum_le s (fun i => (a i : ℂ) *
            ((N : ℂ) * Complex.exp (b i) - (p : ℂ) * Polynomial.aeval (b i) gp))).trans ?_
  -- sum norm products ≤ sum norms times E
  calc
    (∑ i ∈ s, ‖(a i : ℂ) * ((N : ℂ) * Complex.exp (b i) - (p : ℂ) * Polynomial.aeval (b i) gp)‖)
        ≤ ∑ i ∈ s, ‖(a i : ℂ)‖ * E := by
          apply Finset.sum_le_sum
          intro i hi
          rw [norm_mul]
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          simpa [zsmul_eq_mul, nsmul_eq_mul] using (hE i (hbi hi))
    _ = (∑ i ∈ s, ‖(a i : ℂ)‖) * E := by
          rw [Finset.sum_mul]
end
end LindemannSupport
namespace LindemannSupport
noncomputable section
open Polynomial
lemma integer_poly_aeval_integral {z : ℂ} (hz : IsIntegral ℤ z) (g : ℤ[X]) :
    IsIntegral ℤ (Polynomial.aeval z g) := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq =>
      -- aeval additive
      rw [map_add]
      exact hp.add hq
  | monomial n r =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
        Polynomial.aeval_C, Polynomial.aeval_X]
      exact (isIntegral_intCast r).mul (hz.pow n)
end
end LindemannSupport
namespace LindemannSupport
noncomputable section
/-- If a complex algebraic integer becomes a rational integer after multiplication by
 a nonzero integer d, then d divides that integer. This is the elementary
 `ℚ ∩ algebraicIntegers = ℤ` fact in the form used by the mod-p step. -/
lemma int_dvd_of_integral_mul_eq {z : ℂ} (hz : IsIntegral ℤ z)
    {d m : ℤ} (hd : d ≠ 0) (h : (d : ℂ) * z = (m : ℂ)) : d ∣ m := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hzq : z = ((m : ℚ) / (d : ℚ) : ℚ) := by
    -- this casts? RHS coerces to ℂ automatically via expected z? annotations
    apply (mul_left_cancel₀ hdC)
    -- goal d*z = d*(q.cast)
    rw [h]
    push_cast
    field_simp
  obtain ⟨k, hk⟩ := (IsIntegral.exists_int_iff_exists_rat hz).1 ⟨((m : ℚ)/(d : ℚ)), hzq⟩
  have hm : d * k = m := by
    apply (Int.cast_injective : Function.Injective (fun x : ℤ => (x : ℂ)))
    -- multiply d to hk
    push_cast
    rw [← h, hk]
  exact ⟨k, hm.symm⟩
end
end LindemannSupport
namespace LindemannSupport
noncomputable section
open Polynomial
open scoped BigOperators
lemma isIntegral_finset_sum {ι : Type} {s : Finset ι} {z : ι → ℂ}
    (hz : ∀ i ∈ s, IsIntegral ℤ (z i)) :
    IsIntegral ℤ (∑ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isIntegral_zero : IsIntegral ℤ (0:ℂ))
  | @insert a t ha ih =>
    rw [Finset.sum_insert ha]
    exact (hz a (by simp)).add (ih (fun i hi => hz i (by simp [hi])))

lemma combination_ne_zero_mod_prime {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : ι → ℂ) (a : ι → ℤ) (i₀ : ι)
    (N : ℤ) (p : ℕ) (gp : ℤ[X])
    (hp : Nat.Prime p)
    (hN : ¬ (p : ℤ) ∣ N) (ha : ¬ (p : ℤ) ∣ a i₀)
    (hint : ∀ i ∈ (Finset.univ.erase i₀),
        IsIntegral ℤ (Polynomial.aeval (b i) gp)) :
    (N : ℂ) * (a i₀ : ℂ) +
       ∑ i ∈ (Finset.univ.erase i₀),
          (a i : ℂ) * ((p : ℂ) * Polynomial.aeval (b i) gp) ≠ 0 := by
  classical
  let s : Finset ι := Finset.univ.erase i₀
  let z : ℂ := ∑ i ∈ s, (a i : ℂ) * Polynomial.aeval (b i) gp
  have hz : IsIntegral ℤ z := by
    dsimp [z]
    apply isIntegral_finset_sum
    intro i hi
    exact (isIntegral_intCast (a i)).mul (hint i hi)
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  intro hzero
  have hmul : (p : ℂ) * z = (-(N * a i₀) : ℤ) := by
    dsimp [z]
    push_cast
    -- derive by commuting multiplication into sum from hzero
    have hz0 :
        (N : ℂ) * (a i₀ : ℂ) +
           ∑ i ∈ s, (a i : ℂ) * ((p : ℂ) * Polynomial.aeval (b i) gp) = 0 := by
      simpa [s] using hzero
    -- distribute
    -- maybe goal p*sum = ...; ring using hz0 after sum; need manipulate termwise commutativity
    -- get identity sum term = p * sum
    have heq :
        (∑ i ∈ s, (a i : ℂ) * ((p : ℂ) * Polynomial.aeval (b i) gp)) =
        (p : ℂ) * ∑ i ∈ s, (a i : ℂ) * Polynomial.aeval (b i) gp := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi'
          ring
    rw [heq] at hz0
    -- should ring from hz0
    linear_combination hz0
  have hdvdneg : (p : ℤ) ∣ -(N * a i₀) := int_dvd_of_integral_mul_eq hz hpZ hmul
  have hdvd : (p : ℤ) ∣ N * a i₀ := (dvd_neg.mp hdvdneg)
  have hpor := (Prime.dvd_mul (Nat.prime_iff_prime_int.mp hp)).1 hdvd
  exact hpor.elim hN ha
end
end LindemannSupport
namespace LindemannSupport
noncomputable section
open Polynomial
open scoped BigOperators
lemma combination_ne_zero_mod_prime_of_integral_roots {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : ι → ℂ) (a : ι → ℤ) (i₀ : ι)
    (N : ℤ) (p : ℕ) (gp : ℤ[X])
    (hp : Nat.Prime p)
    (hN : ¬ (p : ℤ) ∣ N) (ha : ¬ (p : ℤ) ∣ a i₀)
    (hb : ∀ i, i ≠ i₀ → IsIntegral ℤ (b i)) :
    (N : ℂ) * (a i₀ : ℂ) +
       ∑ i ∈ (Finset.univ.erase i₀),
          (a i : ℂ) * ((p : ℂ) * Polynomial.aeval (b i) gp) ≠ 0 := by
  apply combination_ne_zero_mod_prime b a i₀ N p gp hp hN ha
  intro i hi
  have hne : i ≠ i₀ := (Finset.mem_erase.mp hi).1
  exact integer_poly_aeval_integral (hb i hne) gp
end
end LindemannSupport

namespace LindemannSupport
noncomputable section
open Polynomial
open scoped BigOperators
lemma scaled_eval_integral {z : ℂ} (L : ℤ)
    (hz : IsIntegral ℤ ((L : ℂ) * z)) (g : ℤ[X])
    (D : ℕ) (hg : g.natDegree ≤ D) :
    IsIntegral ℤ ((L : ℂ) ^ D * Polynomial.aeval z g) := by
  classical
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
  rw [Finset.mul_sum]
  apply isIntegral_finset_sum
  intro i hi
  have hi' : i ≤ D := by
    have hir : i < g.natDegree + 1 := Finset.mem_range.mp hi
    omega
  have heq : (L : ℂ)^D * ((algebraMap ℤ ℂ) (g.coeff i) * z ^ i)
        = (L : ℂ)^(D-i) * (g.coeff i : ℂ) * (((L : ℂ) * z)^i) := by
          have hsum : D-i+i = D := Nat.sub_add_cancel hi'
          calc
            (L : ℂ)^D * ((algebraMap ℤ ℂ) (g.coeff i) * z ^ i)
                = ((L : ℂ)^(D-i) * (L:ℂ)^i) * ((g.coeff i : ℂ)*z^i) := by
                    rw [← pow_add, hsum]; rfl
            _ = (L : ℂ)^(D-i) * (g.coeff i : ℂ) * (((L : ℂ) * z)^i) := by
                    rw [mul_pow]
                    ring
  rw [heq]
  rw [mul_assoc]
  exact ((isIntegral_intCast L).pow (D-i)).mul
        ((isIntegral_intCast (g.coeff i)).mul (hz.pow i))

lemma integral_lc_mul_of_aroot (f : ℤ[X]) {r : ℂ} (hr : r ∈ f.aroots ℂ) :
  IsIntegral ℤ ((f.leadingCoeff : ℂ) * r) := by
  have hr' := (Polynomial.mem_aroots.mp hr).2
  have h := isIntegral_leadingCoeff_smul (R:=ℤ) (S:=ℂ) f r hr'
  simpa [Algebra.smul_def] using h

end
end LindemannSupport
namespace LindemannSupport
noncomputable section
open Polynomial
open scoped BigOperators
/-- Clearing the leading coefficient before the mod-p step. Roots of an integer
polynomial need not be integers; after `L*x` is integral, multiplying evaluations
of a degree `D` polynomial by `L^D` restores exactly the same elementary
nondivisibility argument. -/
lemma combination_ne_zero_mod_prime_scaled {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : ι → ℂ) (a : ι → ℤ) (i₀ : ι)
    (N L : ℤ) (p D : ℕ) (gp : ℤ[X])
    (hp : Nat.Prime p)
    (hN : ¬ (p : ℤ) ∣ N) (ha : ¬ (p : ℤ) ∣ a i₀)
    (hL : ¬ (p : ℤ) ∣ L)
    (hdeg : gp.natDegree ≤ D)
    (hb : ∀ i ∈ (Finset.univ.erase i₀),
        IsIntegral ℤ ((L : ℂ) * b i)) :
    (N : ℂ) * (a i₀ : ℂ) +
       ∑ i ∈ (Finset.univ.erase i₀),
          (a i : ℂ) * ((p : ℂ) * Polynomial.aeval (b i) gp) ≠ 0 := by
  classical
  let s : Finset ι := Finset.univ.erase i₀
  -- the sum after multiplying by the common denominator is integral
  let z : ℂ := ∑ i ∈ s, (a i : ℂ) *
                          ((L : ℂ)^D * Polynomial.aeval (b i) gp)
  have hz : IsIntegral ℤ z := by
    dsimp [z]
    apply isIntegral_finset_sum
    intro i hi
    exact (isIntegral_intCast (a i)).mul
        (scaled_eval_integral L (hb i hi) gp D hdeg)
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  intro hzero
  have hz0 :
        (N : ℂ) * (a i₀ : ℂ) +
           ∑ i ∈ s, (a i : ℂ) * ((p : ℂ) * Polynomial.aeval (b i) gp) = 0 := by
      simpa [s] using hzero
  have hmul : (p : ℂ) * z =
        (-(L^D * N * a i₀) : ℤ) := by
    dsimp [z]
    push_cast
    -- multiplication by `L^D` on the equation above
    have hz0' :
        (L : ℂ)^D *
          ((N : ℂ) * (a i₀ : ℂ) +
           ∑ i ∈ s, (a i : ℂ) * ((p : ℂ) * Polynomial.aeval (b i) gp)) = 0 := by
              rw [hz0]
              ring
    -- move the constant term to the other side; finite sums are commutative
    rw [Finset.mul_sum]
    -- goal has p*sum..., whereas hz0' has sum with L outside ; distribute there
    rw [mul_add] at hz0'; rw [Finset.mul_sum] at hz0'
    -- rearrange termwise summands
    have hrew :
       (∑ i ∈ s, (L : ℂ)^D *
              ((a i : ℂ) * ((p : ℂ) * Polynomial.aeval (b i) gp))) =
       (∑ i ∈ s, (p : ℂ) *
              ((a i : ℂ) * ((L : ℂ)^D * Polynomial.aeval (b i) gp))) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
    rw [hrew] at hz0'
    -- target and hz0' are now the same sum
    linear_combination hz0'
  have hdiv : (p : ℤ) ∣ -(L^D * N * a i₀) :=
    int_dvd_of_integral_mul_eq hz hpZ hmul
  have hdiv' : (p : ℤ) ∣ L^D * N * a i₀ := dvd_neg.mp hdiv
  have hp' : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  have cases1 : (p:ℤ) ∣ L^D ∨ (p:ℤ) ∣ N ∨ (p:ℤ) ∣ a i₀ := by
    rcases (Prime.dvd_mul hp').1 hdiv' with hprod | ha'
    · rcases (Prime.dvd_mul hp').1 hprod with hpow | hN'
      · exact Or.inl hpow
      · exact Or.inr (Or.inl hN')
    · exact Or.inr (Or.inr ha')
  rcases cases1 with hpow | hcases
  · have hor : (p:ℤ) ∣ L := (Prime.dvd_of_dvd_pow hp' hpow)
    exact hL hor
  · exact hcases.elim hN ha
end
end LindemannSupport

namespace LindemannSupport
open Filter
/-- Elementary factorial domination in exactly the `(p-1)!` indexing of the
analytic estimate.  In particular one must not replace that denominator by
`p-1`: the factorial is what gives convergence. -/
lemma tendsto_const_mul_pow_div_factorial_sub_one (A B : ℝ) :
    Filter.Tendsto (fun p : ℕ => A * (B ^ p / (↑((p-1).factorial) : ℝ)))
      Filter.atTop (nhds 0) := by
  apply (Filter.tendsto_add_atTop_iff_nat 1).1
  have h :=
    (FloorSemiring.tendsto_pow_div_factorial_atTop (K:=ℝ) B).const_mul (A*B)
  have h' : Filter.Tendsto
      (fun n : ℕ => (A*B) * (B^n / (↑(n.factorial) : ℝ)))
      Filter.atTop (nhds (0:ℝ)) := by
    simpa using h
  convert h' using 1
  ext n
  simp [pow_succ]
  ring

lemma eventually_const_mul_pow_div_factorial_sub_one_lt_one (A B : ℝ) :
    ∀ᶠ p : ℕ in Filter.atTop,
      A * (B ^ p / (↑((p-1).factorial) : ℝ)) < 1 :=
  Filter.Tendsto.eventually_lt_const (by norm_num)
    (tendsto_const_mul_pow_div_factorial_sub_one A B)
end LindemannSupport

namespace LindemannSupport
open Polynomial
open scoped BigOperators
/-- Besides its nondivisibility, the denominator-cleared small quantity is an
algebraic integer.  This is the form whose conjugates enter the norm. -/
lemma combination_scaled_integral {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : ι → ℂ) (a : ι → ℤ) (i₀ : ι)
    (N L : ℤ) (p D : ℕ) (gp : ℤ[X])
    (hdeg : gp.natDegree ≤ D)
    (hb : ∀ i ∈ (Finset.univ.erase i₀), IsIntegral ℤ ((L : ℂ) * b i)) :
  IsIntegral ℤ ((L:ℂ)^D *
    ((N : ℂ) * (a i₀ : ℂ) +
       ∑ i ∈ (Finset.univ.erase i₀),
          (a i : ℂ) * ((p : ℂ) * Polynomial.aeval (b i) gp))) := by
  classical
  let s : Finset ι := Finset.univ.erase i₀
  rw [mul_add]
  apply IsIntegral.add
  · have hcast : IsIntegral ℤ ((L:ℂ)^D) := (isIntegral_intCast L).pow D
    exact hcast.mul ((isIntegral_intCast N).mul (isIntegral_intCast (a i₀)))
  · rw [Finset.mul_sum]
    apply isIntegral_finset_sum
    intro i hi
    have heq :
        (L : ℂ)^D * ((a i : ℂ) * ((p : ℂ) * Polynomial.aeval (b i) gp)) =
          (a i : ℂ) * ((p : ℂ) *
             ((L : ℂ)^D * Polynomial.aeval (b i) gp)) := by ring
    rw [heq]
    have hi' := scaled_eval_integral L (hb i hi) gp D hdeg
    have hp' : IsIntegral ℤ (p:ℂ) := by
      simpa using (isIntegral_intCast (p:ℤ) : IsIntegral ℤ (p:ℂ))
    exact (isIntegral_intCast (a i)).mul (hp'.mul hi')
end LindemannSupport

-- END INLINED FILE: Mathlib/Support/lindemann_weierstrass_047b40c6f1/Arithmetic.lean

-- BEGIN INLINED FILE: Mathlib/Support/lindemann_weierstrass_047b40c6f1/Combinatorial.lean

/-!
Some purely algebraic reductions for the Lindemann--Weierstrass proof.  We keep the
analytic/non-vanishing assertion separate; these lemmas say precisely why the
usual *linear* version for algebraic exponents implies the algebraic-independence
formulation.
-/
open scoped BigOperators
open Polynomial

namespace LindemannSupport

open scoped ComplexConjugate

/-- The (rational coefficient) linear version of the exponential theorem.  Notice
that the coefficients here are only in `ℚ`; this is already enough for converting
the polynomial assertion. -/
def RationalExpLinearIndependent : Prop :=
  ∀ (ι : Type) [Fintype ι], ∀ b : ι → ℂ,
    (∀ i, IsAlgebraic ℚ (b i)) → Function.Injective b →
      LinearIndependent ℚ (fun i => Complex.exp (b i))

noncomputable section

variable {ι : Type} [Fintype ι]

/-- exponent belonging to a monomial.  We use the finite sum over all variables
rather than the support of the finsupp; this avoids a number of support changes in
linear-independence arguments. -/
def monomialExponent (v : ι → ℂ) (d : ι →₀ ℕ) : ℂ :=
  ∑ i : ι, (d i : ℚ) • v i

lemma monomialExponent_eq_support (v : ι → ℂ) (d : ι →₀ ℕ) :
    monomialExponent v d = ∑ i ∈ d.support, (d i : ℚ) • v i := by
  classical
  unfold monomialExponent
  -- all entries off the support of a finsupp are zero
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i hi hi'
  have hzero : d i = 0 := by
    apply not_ne_iff.mp
    intro hn
    exact hi' (Finsupp.mem_support_iff.mpr hn)
  -- `sum_subset` adds the entries of the right-hand (larger) sum
  -- (`hi` is membership in `univ \ support`).
  simp [hzero]

/-- Linear independence of the variables separates two monomials: their associated
linear combinations of the variables have the same value only if all their natural
exponents agree. -/
lemma monomialExponent_injective (v : ι → ℂ)
    (hv : LinearIndependent ℚ v) :
    Function.Injective (monomialExponent v : (ι →₀ ℕ) → ℂ) := by
  classical
  intro d e hde
  have hzero :
      ∑ i : ι, ((d i : ℚ) - (e i : ℚ)) • v i = (0 : ℂ) := by
    have hde' : (∑ i : ι, (d i : ℚ) • v i) = ∑ i : ι, (e i : ℚ) • v i := by
      simpa [monomialExponent] using hde
    -- subtract the two sums
    simpa [sub_smul, Finset.sum_sub_distrib] using sub_eq_zero.mpr hde'
  have hcoord : ∀ i : ι, (d i : ℚ) - (e i : ℚ) = 0 :=
    (Fintype.linearIndependent_iff.mp hv _ hzero)
  ext i
  have hrat : (d i : ℚ) = (e i : ℚ) := sub_eq_zero.mp (hcoord i)
  exact_mod_cast hrat

/-- The natural exponent product in one monomial, evaluated on exponentials, is
the exponential of its linear combination. -/
lemma monomial_exp_product (v : ι → ℂ) (d : ι →₀ ℕ) :
    (∏ i ∈ d.support, Complex.exp (v i) ^ (d i)) =
       Complex.exp (monomialExponent v d) := by
  classical
  rw [monomialExponent_eq_support]
  rw [Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i hi
  -- a rational cast of a natural scalar acts as repeated addition; both are
  -- the ordinary natural multiple in `ℂ`.
  rw [Nat.cast_smul_eq_nsmul ℚ]
  simpa using (Complex.exp_nsmul (v i) (d i)).symm

lemma monomialExponent_isAlgebraic (v : ι → ℂ)
    (hv : ∀ i, IsAlgebraic ℚ (v i)) (d : ι →₀ ℕ) :
    IsAlgebraic ℚ (monomialExponent v d) := by
  classical
  unfold monomialExponent
  -- algebraic elements form a subring; use induction on the finite sum (we
  -- spell it out as this is often useful without any `Fintype` order).
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
      simp [isAlgebraic_zero]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hv a |>.smul (d a : ℚ)).add ih

/-- Expanding a multivariable polynomial on exponentials. -/
lemma aeval_exp_eq_sum (v : ι → ℂ) (p : MvPolynomial ι ℚ) :
    MvPolynomial.aeval (fun i => Complex.exp (v i)) p =
       ∑ d ∈ p.support,
          (algebraMap ℚ ℂ (p.coeff d)) * Complex.exp (monomialExponent v d) := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  exact monomial_exp_product v d

/-- The linear version for rational coefficients is enough for the multivariable
polynomial version. This lemma is deliberately parameterized by the analytic
assertion; the long arithmetic/analytic argument proving that assertion does not
intervene in this combinatorial reduction. -/
theorem algebraicIndependent_exp_of_rational_linear
    (H : RationalExpLinearIndependent)
    (v : ι → ℂ) (hv_alg : ∀ i, IsAlgebraic ℚ (v i))
    (hv_ind : LinearIndependent ℚ v) :
    AlgebraicIndependent ℚ (fun i => Complex.exp (v i)) := by
  classical
  -- it is convenient to use the kernel-zero form
  rw [algebraicIndependent_iff]
  intro p hp
  by_contra hp0
  have hsupport : p.support.Nonempty := MvPolynomial.support_nonempty.mpr hp0
  let β : {d // d ∈ p.support} → ℂ := fun d => monomialExponent v d.1
  have hβ_alg : ∀ d, IsAlgebraic ℚ (β d) := fun d => monomialExponent_isAlgebraic v hv_alg d.1
  have hβ_inj : Function.Injective β := fun d e h =>
    Subtype.ext ((monomialExponent_injective v hv_ind) h)
  have hLI : LinearIndependent ℚ (fun d : {d // d ∈ p.support} => Complex.exp (β d)) :=
    H _ β hβ_alg hβ_inj
  have hsum0 :
      ∑ d : {d // d ∈ p.support},
        (p.coeff d.1 : ℚ) • Complex.exp (β d) = (0 : ℂ) := by
    -- `aeval_exp_eq_sum` above is a sum over `support`; rewrite as the finite
    -- sum over the subtype.
    have h := hp
    rw [aeval_exp_eq_sum v p] at h
    classical
    have hx :
        (∑ d : {d // d ∈ p.support},
          (algebraMap ℚ ℂ (p.coeff d.1)) *
             Complex.exp (monomialExponent v d.1)) = (0 : ℂ) := by
      calc
        _ = ∑ d ∈ p.support,
            (algebraMap ℚ ℂ (p.coeff d)) *
             Complex.exp (monomialExponent v d) :=
               Finset.sum_coe_sort p.support _
        _ = 0 := h
    -- coe of a rational is the scalar action
    simpa [β, Algebra.smul_def] using hx
  have hvanish : ∀ d : {d // d ∈ p.support}, (p.coeff d.1 : ℚ) = 0 :=
    (Fintype.linearIndependent_iff.mp hLI _ hsum0)
  obtain ⟨d, hd⟩ := hsupport
  exact (MvPolynomial.mem_support_iff.mp hd) (hvanish ⟨d, hd⟩)

end
end LindemannSupport

-- END INLINED FILE: Mathlib/Support/lindemann_weierstrass_047b40c6f1/Combinatorial.lean

-- BEGIN INLINED FILE: Mathlib/Support/lindemann_weierstrass_047b40c6f1/RationalReduction.lean

open scoped BigOperators

namespace LindemannSupport
noncomputable section

/-- The integer-coefficient nonvanishing statement.  It is a convenient arithmetic
version of the hard assertion: all exponents are algebraic and distinct. -/
def IntegerExpNonzero : Prop :=
  ∀ (ι : Type) [Fintype ι], ∀ b : ι → ℂ,
    (∀ i, IsAlgebraic ℚ (b i)) → Function.Injective b →
    ∀ a : ι → ℤ, (∃ i, a i ≠ 0) →
       (∑ i, (a i : ℂ) * Complex.exp (b i)) ≠ 0

variable {ι : Type} [Fintype ι]

private def commonDen (c : ι → ℚ) : ℕ := ∏ i, (c i).den
private noncomputable def exceptDen (c : ι → ℚ) (i : ι) : ℕ := by
  classical
  exact ∏ j ∈ (Finset.univ.erase i), (c j).den
private def clearCoeff (c : ι → ℚ) (i : ι) : ℤ :=
  (exceptDen c i : ℤ) * (c i).num

private lemma commonDen_ne_zero (c : ι → ℚ) : commonDen c ≠ 0 := by
  classical
  unfold commonDen
  exact Finset.prod_ne_zero_iff.mpr (fun i hi => Rat.den_nz _)

private lemma clearCoeff_rat (c : ι → ℚ) (i : ι) :
    (commonDen c : ℚ) * c i = (clearCoeff c i : ℤ) := by
  classical
  -- expose the product of all other denominators
  have hp := Finset.prod_erase_mul (Finset.univ : Finset ι) (fun j => (c j).den)
        (Finset.mem_univ i)
  have hp' : exceptDen c i * (c i).den = commonDen c := by
    simpa [exceptDen, commonDen] using hp
  -- cast the equality to `ℚ` and then use `q * q.den = q.num`.
  have hpq : (commonDen c : ℚ) =
      (exceptDen c i : ℚ) * ((c i).den : ℚ) := by
    exact_mod_cast hp'.symm
  rw [hpq]
  unfold clearCoeff
  push_cast
  rw [mul_assoc]
  rw [mul_comm ((c i).den : ℚ) (c i)]
  rw [Rat.mul_den_eq_num]

private lemma clearCoeff_nonzero {c : ι → ℚ} {i : ι} (hi : c i ≠ 0) :
    clearCoeff c i ≠ 0 := by
  classical
  -- equality after casting; multiplication by a common nonzero denominator is
  -- injective in a field.
  intro h
  have hrat : (commonDen c : ℚ) * c i = (0 : ℚ) := by
    rw [clearCoeff_rat c i, h]
    simp
  have : (commonDen c : ℚ) ≠ 0 := by
    exact_mod_cast (commonDen_ne_zero c)
  exact hi (mul_eq_zero.mp hrat |>.resolve_left this)

/-- Clearing denominators in a finite rational linear combination.  It is useful
independently of exponentials, so stated for an arbitrary family of complex
numbers. -/
lemma exists_integer_relation_of_rat_relation
    (z : ι → ℂ) (c : ι → ℚ)
    (hc : ∃ i, c i ≠ 0)
    (h : (∑ i, (c i) • z i) = (0 : ℂ)) :
    ∃ a : ι → ℤ, (∃ i, a i ≠ 0) ∧
      ∑ i, (a i : ℂ) * z i = 0 := by
  classical
  let D : ℚ := (commonDen c : ℕ)
  let a : ι → ℤ := clearCoeff c
  refine ⟨a, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hc
    exact ⟨i, clearCoeff_nonzero hi⟩
  · -- multiply the given equality by the common rational denominator
    have hz : D • (∑ i, c i • z i) = (0 : ℂ) := by
      rw [h, smul_zero]
    rw [Finset.smul_sum] at hz
    -- termwise, the new rational scalar is the integer coefficient
    have term (i : ι) : D • c i • z i = (a i : ℂ) * z i := by
      rw [← mul_smul]
      -- identify the rational scalar after clearing denominators
      have hiq : D * c i = (a i : ℤ) := by
        simpa [D, a] using clearCoeff_rat c i
      rw [hiq]
      -- a rational cast of an integer scalar in `ℂ`
      simp [Algebra.smul_def]
    simpa [term] using hz

/-- Thus it suffices to prove the theorem for integer coefficients. -/
theorem rationalLinear_of_integerNonzero
    (H : IntegerExpNonzero) : RationalExpLinearIndependent := by
  classical
  intro κ inst b hb_alg hb_inj
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  by_contra hi
  have hex : ∃ j, c j ≠ 0 := ⟨i, hi⟩
  obtain ⟨a, ha, ha0⟩ :=
    exists_integer_relation_of_rat_relation (fun j => Complex.exp (b j)) c hex hc
  exact (H _ b hb_alg hb_inj a ha) ha0

end
end LindemannSupport

namespace LindemannSupport
noncomputable section

/-- Integer formulation with a distinguished constant term.  All the
number-theoretic approximation arguments start in precisely this situation: one
coefficient belongs to the exponent `0`, and that coefficient is nonzero. -/
def IntegerExpWithConstantNonzero : Prop :=
  ∀ (ι : Type) [Fintype ι], ∀ b : ι → ℂ,
    (∀ i, IsAlgebraic ℚ (b i)) → Function.Injective b →
    ∀ a : ι → ℤ, ∀ i₀ : ι, b i₀ = 0 → a i₀ ≠ 0 →
       (∑ i, (a i : ℂ) * Complex.exp (b i)) ≠ 0

/-- A relation can always be translated by any exponent carrying a nonzero
coefficient; the exponential never vanishes.  Consequently the distinguished
constant-term case is enough. -/
theorem integerNonzero_of_withConstant
    (H : IntegerExpWithConstantNonzero) : IntegerExpNonzero := by
  classical
  intro ι inst b hb_alg hb_inj a ha
  obtain ⟨i₀, hi₀⟩ := ha
  let b' : ι → ℂ := fun i => b i - b i₀
  have hb'_alg : ∀ i, IsAlgebraic ℚ (b' i) := by
    intro i
    -- `sub` is available for algebraic elements over a field
    exact (hb_alg i).sub (hb_alg i₀)
  have hb'_inj : Function.Injective b' := by
    intro i j hij
    have : b i = b j := sub_left_inj.mp hij
    exact hb_inj this
  have hb'0 : b' i₀ = 0 := sub_self _
  have hNZ := H _ b' hb'_alg hb'_inj a i₀ hb'0 hi₀
  -- turn a hypothetical relation for the un-translated exponents into one for
  -- `b'`, by multiplying by `exp (-b i₀)`.
  intro hsum
  apply hNZ
  have hmul : (∑ i, (a i : ℂ) * Complex.exp (b i)) *
        Complex.exp (-(b i₀)) = (0 : ℂ) := by simp [hsum]
  rw [Finset.sum_mul] at hmul
  -- simplification is arranged term by term so as not to change the set of
  -- indices of the sum
  -- `exp(u-v) = exp u * exp (-v)`.
  simpa [b', Complex.exp_sub, div_eq_mul_inv, Complex.exp_neg, mul_assoc] using hmul

end
end LindemannSupport

-- END INLINED FILE: Mathlib/Support/lindemann_weierstrass_047b40c6f1/RationalReduction.lean

-- BEGIN INLINED FILE: Mathlib/Support/lindemann_weierstrass_047b40c6f1/RootPolynomial.lean

open Polynomial

namespace LindemannSupport
noncomputable section

/-- Remove all factors `X` from an integer polynomial without losing a specified
*nonzero* complex root.  This small device is handy because the approximation
lemma excludes zero roots. -/
lemma remove_zero_factors {r : ℂ} (hr0 : r ≠ 0) :
    ∀ p : ℤ[X], p ≠ 0 → Polynomial.aeval r p = 0 →
      ∃ q : ℤ[X], q.eval 0 ≠ 0 ∧ Polynomial.aeval r q = 0 := by
  classical
  intro p
  induction hN : p.natDegree using Nat.strong_induction_on generalizing p with
  | h N ih =>
    intro hp hroot
    by_cases hc : p.eval 0 = 0
    · -- divide off one copy of `X`
      let q : ℤ[X] := p /ₘ (X - C 0)
      have hroot0 : p.IsRoot 0 := by simpa [Polynomial.IsRoot] using hc
      have hfac : (X - C 0) * q = p := by
        dsimp [q]
        exact (Polynomial.mul_divByMonic_eq_iff_isRoot).2 hroot0
      have hq : q ≠ 0 := by
        intro h
        have : p = 0 := by simpa [h] using hfac.symm
        exact hp this
      have hdeg : q.natDegree < p.natDegree := by
        have hm : (X - C (0:ℤ)).natDegree + q.natDegree = p.natDegree := by
          rw [← hfac]
          rw [Polynomial.natDegree_mul (by simp) hq]
        rw [Polynomial.natDegree_X_sub_C] at hm
        omega
      have hqroot : Polynomial.aeval r q = 0 := by
        have h := congrArg (Polynomial.aeval r) hfac
        -- the embedding of `X` evaluates to `r`
        simp [map_mul, hroot] at h
        exact h.resolve_left hr0
      -- the recursive call decreases degree by exactly one
      exact ih q.natDegree (by simpa [hN] using hdeg) q rfl hq hqroot
    · exact ⟨p, hc, hroot⟩

/-- Every nonzero algebraic exponent is a root of an integer polynomial whose
constant term is nonzero.  Coefficients need not be monic: this is why the
analytic lemma works with `ℤ[X]`. -/
lemma intPolynomial_for_nonzero_algebraic {r : ℂ}
    (hr : IsAlgebraic ℚ r) (hr0 : r ≠ 0) :
    ∃ q : ℤ[X], q.eval 0 ≠ 0 ∧ r ∈ q.aroots ℂ := by
  classical
  have hrZ : IsAlgebraic ℤ r :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).2 hr
  obtain ⟨p, hp, hx⟩ := hrZ
  obtain ⟨q, hq0, hqx⟩ := remove_zero_factors hr0 p hp hx
  refine ⟨q, hq0, ?_⟩
  have hq : q ≠ 0 := by
    intro h
    apply hq0
    simp [h]
  exact Polynomial.mem_aroots.mpr ⟨hq, hqx⟩

end
end LindemannSupport

namespace LindemannSupport
noncomputable section
open Polynomial
open scoped BigOperators

/-- A single integer polynomial can contain any prescribed finite collection of
nonzero algebraic exponents. -/
lemma intPolynomial_for_family {ι : Type} [Fintype ι]
    (b : ι → ℂ) (hb : ∀ i, IsAlgebraic ℚ (b i)) :
    ∃ f : ℤ[X], f.eval 0 ≠ 0 ∧
       ∀ i, b i ≠ 0 → b i ∈ f.aroots ℂ := by
  classical
  have hex : ∀ i : ι, ∃ q : ℤ[X], q.eval 0 ≠ 0 ∧
          (b i ≠ 0 → Polynomial.aeval (b i) q = 0) := by
    intro i
    by_cases hi : b i = 0
    · refine ⟨1, by simp, fun h => (h hi).elim⟩
    · obtain ⟨q, h0, hroot⟩ := intPolynomial_for_nonzero_algebraic (hb i) hi
      exact ⟨q, h0, fun _ => (Polynomial.mem_aroots.mp hroot).2⟩
  choose q hq0 hqx using hex
  refine ⟨∏ i, q i, ?_, ?_⟩
  · simp_rw [Polynomial.eval_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun i hi => hq0 i)
  intro i hi
  apply Polynomial.mem_aroots.mpr
  refine ⟨?_, ?_⟩
  · intro hz
    have hz0 : (∏ j, q j).eval 0 = 0 := by simp [hz]
    have hz' : ∏ j, (q j).eval 0 = 0 := by simpa [Polynomial.eval_prod] using hz0
    exact (Finset.prod_ne_zero_iff.mpr (fun j hj => hq0 j)) hz'
  · simp_rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hqx i hi)

end
end LindemannSupport

namespace LindemannSupport
noncomputable section
open Polynomial
open scoped BigOperators

/-- The last arithmetic/analytic core can assume a common integer polynomial for
all nonzero exponents.  This exactly matches `exp_polynomial_approx`: that lemma
only promises an estimate at roots of one such polynomial. -/
def IntegerExpWithRootPolynomial : Prop :=
  ∀ (ι : Type) [Fintype ι], ∀ b : ι → ℂ,
    Function.Injective b →
    ∀ a : ι → ℤ, ∀ i₀ : ι, b i₀ = 0 → a i₀ ≠ 0 →
    ∀ f : ℤ[X], f.eval 0 ≠ 0 →
      (∀ i, b i ≠ 0 → b i ∈ f.aroots ℂ) →
       (∑ i, (a i : ℂ) * Complex.exp (b i)) ≠ 0

lemma withConstant_of_rootPolynomial
    (H : IntegerExpWithRootPolynomial) : IntegerExpWithConstantNonzero := by
  classical
  intro ι inst b hb hb_inj a i₀ hb0 ha0
  obtain ⟨f, hf0, hroots⟩ := intPolynomial_for_family b hb
  exact H _ b hb_inj a i₀ hb0 ha0 f hf0 hroots

end
end LindemannSupport

-- END INLINED FILE: Mathlib/Support/lindemann_weierstrass_047b40c6f1/RootPolynomial.lean

-- BEGIN INLINED FILE: Mathlib/Support/lindemann_weierstrass_047b40c6f1/SymmetricCore.lean
open Polynomial
open scoped BigOperators
namespace LindemannSupport
noncomputable section

/-- The very last analytic argument becomes elementary as soon as the
coefficient--weighted values at the roots are rational.  This is a convenient
interface for the (quite separate) Galois symmetrisation.  Notice the factor
`max ‖leadingCoeff f‖ 1`: roots of an integer polynomial are not necessarily
algebraic integers. -/
theorem no_vanishing_of_rational_root_sums
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : ι → ℂ) (hb : Function.Injective b)
    (a : ι → ℤ) (i₀ : ι) (hb0 : b i₀ = 0) (ha0 : a i₀ ≠ 0)
    (f : ℤ[X]) (hf0 : f.eval 0 ≠ 0)
    (hf : ∀ i, b i ≠ 0 → b i ∈ f.aroots ℂ)
    (hrat : ∀ g : ℤ[X], ∃ q : ℚ,
      (∑ k ∈ (Finset.univ.erase i₀),
        (a k : ℂ) * Polynomial.aeval (b k) g) = (q : ℂ)) :
    (∑ i, (a i : ℂ) * Complex.exp (b i)) ≠ 0 := by
  classical
  let A : ℝ := ∑ k ∈ (Finset.univ.erase i₀), ‖(a k : ℂ)‖
  let B : ℝ := max ‖(f.leadingCoeff : ℂ)‖ 1
  have hB : 0 ≤ B := le_trans (norm_nonneg _) (le_max_left _ _)
  have hB1 : 1 ≤ B := le_max_right _ _
  obtain ⟨c, hc⟩ := LindemannWeierstrass.exp_polynomial_approx f hf0
  let C : ℝ := |c|
  have hC : 0 ≤ C := abs_nonneg _
  -- Leave enough room in the choice of the prime to clear all denominators.
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
    (eventually_const_mul_pow_div_factorial_sub_one_lt_one A (B ^ f.natDegree * C))
  obtain ⟨p, hp, pp⟩ :=
    Nat.exists_infinite_primes
      (max (max (max (Polynomial.eval 0 f).natAbs (a i₀).natAbs)
        f.leadingCoeff.natAbs) T + 1)
  have hp0 : p > (Polynomial.eval 0 f).natAbs :=
    lt_of_lt_of_le
      (Nat.lt_succ_of_le
        (le_trans
          (le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
          (Nat.le_max_left _ _))) hp
  obtain ⟨N, hN, gp, hdeg, hgp⟩ := hc p hp0 pp
  let D : ℕ := p * f.natDegree - 1
  have hD : D ≤ p * f.natDegree := Nat.sub_le _ _
  have hflead : f.leadingCoeff ≠ 0 := by
    apply Polynomial.leadingCoeff_ne_zero.mpr
    intro h
    apply hf0
    simp [h]
  have hpa : ¬ (p : ℤ) ∣ a i₀ := by
    intro h
    have hn : p ∣ (a i₀).natAbs := Int.natCast_dvd.mp h
    have hle : p ≤ (a i₀).natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.mpr ha0) hn
    have hlt : (a i₀).natAbs < p :=
      lt_of_lt_of_le
        (Nat.lt_succ_of_le
          (le_trans
            (le_trans (Nat.le_max_right (Polynomial.eval 0 f).natAbs _)
              (Nat.le_max_left _ _))
            (Nat.le_max_left _ _))) hp
    exact (not_lt_of_ge hle) hlt
  have hpL : ¬ (p : ℤ) ∣ f.leadingCoeff := by
    intro h
    have hn : p ∣ f.leadingCoeff.natAbs := Int.natCast_dvd.mp h
    have hle : p ≤ f.leadingCoeff.natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.mpr hflead) hn
    have hlt : f.leadingCoeff.natAbs < p :=
      lt_of_lt_of_le
        (Nat.lt_succ_of_le
          (le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))) hp
    exact (not_lt_of_ge hle) hlt
  have happrox : ∀ k : ι, b k ≠ 0 →
        ‖N • Complex.exp (b k) - p • Polynomial.aeval (b k) gp‖
            ≤ C ^ p / (↑((p - 1).factorial) : ℝ) := by
    intro k hk
    have h := hgp (hf k hk)
    refine h.trans ?_
    have hfac : (0:ℝ) ≤ (↑((p-1).factorial) : ℝ) := by positivity
    have hpow : c ^ p ≤ C ^ p := by
      dsimp [C]
      calc
        c ^ p ≤ |c ^ p| := le_abs_self _
        _ = |c| ^ p := abs_pow _ _
    gcongr
  -- common small quantity
  let Δ : ℂ := (N : ℂ) * (a i₀ : ℂ) +
       ∑ k ∈ (Finset.univ.erase i₀),
          (a k : ℂ) * ((p : ℂ) * Polynomial.aeval (b k) gp)
  have hne : Δ ≠ 0 := by
    dsimp [Δ]
    apply combination_ne_zero_mod_prime_scaled b a i₀ N f.leadingCoeff p D gp
      pp hN hpa hpL hdeg
    intro k hk
    have hki : k ≠ i₀ := (Finset.mem_erase.mp hk).1
    have hk0 : b k ≠ 0 := by
      intro h
      exact hki (hb (h.trans hb0.symm))
    exact integral_lc_mul_of_aroot f (hf k hk0)
  have hint : IsIntegral ℤ ((f.leadingCoeff : ℂ)^D * Δ) := by
    dsimp [Δ]
    apply combination_scaled_integral b a i₀ N f.leadingCoeff p D gp hdeg
    intro k hk
    have hki : k ≠ i₀ := (Finset.mem_erase.mp hk).1
    have hk0 : b k ≠ 0 := by
      intro h
      exact hki (hb (h.trans hb0.symm))
    exact integral_lc_mul_of_aroot f (hf k hk0)
  intro hvan
  have hsmall : ‖Δ‖ ≤ A * (C ^ p / (↑((p-1).factorial) : ℝ)) := by
    dsimp [Δ, A]
    exact norm_aux b hb a i₀ hb0 N p gp _ happrox hvan
  -- rationality and integrality turn the scaled quantity into an honest integer
  obtain ⟨q, hq⟩ := hrat gp
  have hratΔ : ∃ r : ℚ, Δ = (r : ℂ) := by
    refine ⟨(N : ℚ) * (a i₀ : ℚ) + (p : ℚ) * q, ?_⟩
    dsimp [Δ]
    -- originally the sum has `p` inside each summand.
    have heq :
        (∑ k ∈ (Finset.univ.erase i₀),
          (a k : ℂ) * ((p : ℂ) * Polynomial.aeval (b k) gp)) =
        (p : ℂ) * ∑ k ∈ (Finset.univ.erase i₀),
          (a k : ℂ) * Polynomial.aeval (b k) gp := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [heq, hq]
    push_cast
    ring
  obtain ⟨r, hr⟩ := hratΔ
  have hratW : ∃ u : ℚ, (f.leadingCoeff : ℂ)^D * Δ = (u : ℂ) := by
    refine ⟨(f.leadingCoeff : ℚ)^D * r, ?_⟩
    rw [hr]
    push_cast
    rfl
  obtain ⟨m, hm⟩ := (IsIntegral.exists_int_iff_exists_rat hint).mp hratW
  have hm0 : m ≠ 0 := by
    intro hm0
    have hz : (f.leadingCoeff : ℂ)^D * Δ = 0 := by simp [hm, hm0]
    exact hne ((mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ (by exact_mod_cast hflead)))
  have hlower : (1:ℝ) ≤ ‖(f.leadingCoeff : ℂ)^D * Δ‖ := by
    rw [hm, Complex.norm_intCast]
    have : (1:ℝ) ≤ |(m : ℝ)| := by
      have hnat : 1 ≤ m.natAbs := (Int.natAbs_pos.mpr hm0)
      have hrabs : |(m : ℝ)| = (m.natAbs : ℕ) := by
        calc
          |(m:ℝ)| = ((|m| : ℤ) : ℝ) := by simp
          _ = ((m.natAbs : ℤ) : ℝ) := by congr 1; exact Int.abs_eq_natAbs m
          _ = (m.natAbs : ℕ) := by simp
      rw [hrabs]
      exact_mod_cast hnat
    simpa using this
  have hpT : T ≤ p :=
    le_trans
      (le_trans (Nat.le_max_right
        (max (max (Polynomial.eval 0 f).natAbs (a i₀).natAbs)
          f.leadingCoeff.natAbs) _) (Nat.le_add_right _ _)) hp
  have htail : A * ((B ^ f.natDegree * C) ^ p /
          (↑((p-1).factorial) : ℝ)) < 1 := hT p hpT
  have hupper : ‖(f.leadingCoeff : ℂ)^D * Δ‖ < 1 := by
    rw [norm_mul, norm_pow]
    have hLD : ‖(f.leadingCoeff : ℂ)‖ ^ D ≤ (B ^ f.natDegree) ^ p := by
      calc
        ‖(f.leadingCoeff : ℂ)‖ ^ D ≤ B ^ D :=
          pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) D
        _ ≤ B ^ (p * f.natDegree) := by
          exact pow_le_pow_right₀ hB1 hD
        _ = (B ^ f.natDegree) ^ p := by rw [mul_comm, pow_mul]
    have hnon : 0 ≤ C ^ p / (↑((p-1).factorial) : ℝ) := by positivity
    calc
      ‖(f.leadingCoeff : ℂ)‖ ^ D * ‖Δ‖
          ≤ (B ^ f.natDegree) ^ p *
              (A * (C ^ p / (↑((p-1).factorial) : ℝ))) := by
                exact mul_le_mul hLD hsmall (norm_nonneg _) (by positivity)
      _ = A * ((B ^ f.natDegree * C)^p /
                  (↑((p-1).factorial) : ℝ)) := by ring
      _ < 1 := htail
  exact (not_lt_of_ge hlower) hupper

end
end LindemannSupport

-- END INLINED FILE: Mathlib/Support/lindemann_weierstrass_047b40c6f1/SymmetricCore.lean

-- BEGIN INLINED FILE: Mathlib/Support/lindemann_weierstrass_047b40c6f1/Symmetrization.lean
open Polynomial
open scoped BigOperators
namespace LindemannSupport
noncomputable section

lemma single_sum_ne_zero {ι K R : Type} [Fintype ι] [DecidableEq ι]
    [DecidableEq K] [Semiring R] [AddCommMonoid K]
    (u : ι → K) (hu : Function.Injective u)
    (a : ι → R) (j : ι) (ha : a j ≠ 0) :
    (∑ i, AddMonoidAlgebra.single (u i) (a i)) ≠ 0 := by
  classical
  intro h
  have h' : (∑ i, (AddMonoidAlgebra.single (u i) (a i)) (u j)) = 0 := by
    have hh :
        (Finsupp.applyAddHom (M:=R) (u j))
            (∑ i, AddMonoidAlgebra.single (u i) (a i)) =
          (Finsupp.applyAddHom (M:=R) (u j)) 0 := congrArg _ h
    rw [map_sum] at hh
    simpa using hh
  have hx : (∑ i, (AddMonoidAlgebra.single (u i) (a i)) (u j)) = a j := by
    calc
      _ = ∑ i, if u i = u j then a i else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Finsupp.single_apply
      _ = a j := by simp [hu.eq_iff]
  rw [hx] at h'
  exact ha h'

/-- Product of all Galois translates of a formal exponential sum.  We keep it
in the additive monoid algebra; no analytic assertion is hidden in this
definition. -/
noncomputable def galoisProduct {K : Type} [Field K] [Algebra ℚ K]
    [Finite (K ≃ₐ[ℚ] K)] {ι : Type} [Fintype ι]
    (u : ι → K) (a : ι → ℤ) : AddMonoidAlgebra ℤ K := by
  classical
  letI : Fintype (K ≃ₐ[ℚ] K) := Fintype.ofFinite _
  exact ∏ σ : (K ≃ₐ[ℚ] K), ∑ i, AddMonoidAlgebra.single (σ (u i)) (a i)

lemma galoisProduct_ne_zero {K : Type} [Field K] [CharZero K] [Algebra ℚ K]
    [Finite (K ≃ₐ[ℚ] K)] {ι : Type} [Fintype ι]
    (u : ι → K) (hu : Function.Injective u)
    (a : ι → ℤ) (j : ι) (ha : a j ≠ 0) :
    galoisProduct u a ≠ 0 := by
  classical
  letI : Fintype (K ≃ₐ[ℚ] K) := Fintype.ofFinite _
  unfold galoisProduct
  -- Finsupp convolution over a characteristic-zero field's additive group has
  -- no zero divisors (unique sums).
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro σ hσ
  exact single_sum_ne_zero (fun i => σ (u i)) (fun i k h => hu (σ.injective h)) a j ha

/-- A translate of the Galois product by another automorphism is the same
formal sum.  This is useful: applying an integral polynomial to its support
will therefore land in the fixed field. -/
lemma map_galoisProduct {K : Type} [Field K] [Algebra ℚ K]
    [Finite (K ≃ₐ[ℚ] K)] {ι : Type} [Fintype ι]
    (u : ι → K) (a : ι → ℤ) (τ : K ≃ₐ[ℚ] K) :
    AddMonoidAlgebra.mapDomainRingHom ℤ
      τ.toRingEquiv.toAddEquiv.toAddMonoidHom (galoisProduct u a)
      = galoisProduct u a := by
  classical
  letI : Fintype (K ≃ₐ[ℚ] K) := Fintype.ofFinite _
  unfold galoisProduct
  rw [map_prod]
  -- the action on a single monomial just moves its exponent
  have hterm (σ : K ≃ₐ[ℚ] K) :
      (AddMonoidAlgebra.mapDomainRingHom ℤ
        τ.toRingEquiv.toAddEquiv.toAddMonoidHom)
          (∑ i, AddMonoidAlgebra.single (σ (u i)) (a i)) =
        (∑ i, AddMonoidAlgebra.single ((τ * σ) (u i)) (a i)) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [AddMonoidAlgebra.mapDomainRingHom_apply,
        AddMonoidAlgebra.mapDomain_single]
    rfl
  simp_rw [hterm]
  -- left multiplication by τ permutes the finite automorphism group
  let e : (K ≃ₐ[ℚ] K) ≃ (K ≃ₐ[ℚ] K) :=
    Equiv.mulLeft τ
  exact Fintype.prod_equiv e _ _ (by
    intro σ
    rfl)

/-- Evaluation of the product at the complex exponential.  If one translate
of the original formal relation vanishes, the whole product does. -/
lemma eval_galoisProduct_zero {K : Type} [Field K] [Algebra ℚ K]
    [Finite (K ≃ₐ[ℚ] K)] {ι : Type} [Fintype ι]
    (e : K →ₐ[ℚ] ℂ) (u : ι → K) (a : ι → ℤ)
    (h : (∑ i, (a i : ℂ) * Complex.exp (e (u i))) = 0) :
    (AddMonoidAlgebra.lift ℤ ℂ K
      { toFun := fun t : Multiplicative K => Complex.exp (e t.toAdd)
        map_one' := by simp
        map_mul' := by intro x y; simpa using Complex.exp_add (e x.toAdd) (e y.toAdd) })
      (galoisProduct u a) = 0 := by
  classical
  letI : Fintype (K ≃ₐ[ℚ] K) := Fintype.ofFinite _
  let ev : AddMonoidAlgebra ℤ K →ₐ[ℤ] ℂ :=
    (AddMonoidAlgebra.lift ℤ ℂ K
      { toFun := fun t : Multiplicative K => Complex.exp (e t.toAdd)
        map_one' := by simp
        map_mul' := by intro x y; simpa using Complex.exp_add (e x.toAdd) (e y.toAdd) })
  change ev (galoisProduct u a) = 0
  unfold galoisProduct
  rw [map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ (1 : K ≃ₐ[ℚ] K))
  rw [map_sum]
  -- cast of a coefficient is the ordinary product
  simpa [ev, AddMonoidAlgebra.lift_single, Algebra.smul_def] using h

end
end LindemannSupport

namespace LindemannSupport
noncomputable section
/-- A polynomial-weighted sum of an invariant formal sum is in the rational
fixed field. This is the exact rationality input of the Hermite estimate. -/
lemma weighted_sum_mem_fixed
    {K : Type} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (F : AddMonoidAlgebra ℤ K)
    (hF : ∀ τ : K ≃ₐ[ℚ] K,
      AddMonoidAlgebra.mapDomainRingHom ℤ
        τ.toRingEquiv.toAddEquiv.toAddMonoidHom F = F)
    (g : ℤ[X]) :
    ∃ q : ℚ, F.sum (fun x n => (n : K) * Polynomial.aeval x g) =
      (algebraMap ℚ K) q := by
  classical
  have hfix : ∀ τ : K ≃ₐ[ℚ] K,
      τ (F.sum (fun x n => (n : K) * Polynomial.aeval x g)) =
        F.sum (fun x n => (n : K) * Polynomial.aeval x g) := by
    intro τ
    -- evaluation of an integral polynomial commutes with a rational embedding
    have hev (x : K) :
        τ (Polynomial.aeval x g) = Polynomial.aeval (τ x) g := by
      rw [Polynomial.aeval_def, Polynomial.aeval_def]
      calc
        τ (Polynomial.eval₂ (algebraMap ℤ K) x g) =
            Polynomial.eval₂
              (τ.toRingEquiv.toRingHom.comp (algebraMap ℤ K)) (τ x) g :=
              Polynomial.hom_eval₂ g (algebraMap ℤ K)
                τ.toRingEquiv.toRingHom x
        _ = Polynomial.eval₂ (algebraMap ℤ K) (τ x) g := by
              congr 1
              ext z
              simp
    calc
      τ (F.sum (fun x n => (n : K) * Polynomial.aeval x g)) =
          F.sum (fun x n => τ ((n : K) * Polynomial.aeval x g)) := by
            classical
            simp only [Finsupp.sum, map_sum]
      _ = F.sum (fun x n => (n : K) * Polynomial.aeval (τ x) g) := by
            apply Finset.sum_congr rfl
            intro x hx
            simp [hev]
      _ = (AddMonoidAlgebra.mapDomain
                (fun x : K => τ x) F).sum
              (fun x n => (n : K) * Polynomial.aeval x g) := by
            symm
            exact Finsupp.sum_mapDomain_index_inj τ.injective
      _ = F.sum (fun x n => (n : K) * Polynomial.aeval x g) := by
            have hm : AddMonoidAlgebra.mapDomain (fun x : K => τ x) F = F := by
              simpa [AddMonoidAlgebra.mapDomainRingHom_apply] using hF τ
            rw [hm]
  have hrange : F.sum (fun x n => (n : K) * Polynomial.aeval x g) ∈
      Set.range (algebraMap ℚ K) :=
    (IsGalois.mem_range_algebraMap_iff_fixed _).2 hfix
  rcases hrange with ⟨q,hq⟩
  exact ⟨q, hq.symm⟩

lemma galoisProduct_weighted_rational
    {K : Type} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K] [IsGalois ℚ K]
    {ι : Type} [Fintype ι] (u : ι → K) (a : ι → ℤ) (g : ℤ[X]) :
    ∃ q : ℚ, (galoisProduct u a).sum
      (fun x n => (n : K) * Polynomial.aeval x g) = (q : K) := by
  simpa using (weighted_sum_mem_fixed _ (map_galoisProduct u a) g)

end
end LindemannSupport

-- END INLINED FILE: Mathlib/Support/lindemann_weierstrass_047b40c6f1/Symmetrization.lean

-- BEGIN INLINED FILE: Mathlib/Support/lindemann_weierstrass_047b40c6f1/GaloisReduction.lean

open Polynomial
open scoped BigOperators
set_option synthInstance.maxHeartbeats 200000
namespace LindemannSupport
noncomputable section

/-- Negation, as an additive endomorphism of an additive commutative group. -/
def negHom (K : Type*) [AddCommGroup K] : K →+ K :=
{ toFun := fun x => -x
  map_zero' := neg_zero
  map_add' := by intro x y; simp [add_comm] }

lemma negHom_apply {K : Type*} [AddCommGroup K] (x : K) : negHom K x = -x := rfl
lemma negHom_injective {K : Type*} [AddCommGroup K] : Function.Injective (negHom K) := by
  exact neg_injective

/-- Reflect a formal additive exponential polynomial. -/
def reflect {K : Type*} [AddCommGroup K] (F : AddMonoidAlgebra ℤ K) :
    AddMonoidAlgebra ℤ K :=
  AddMonoidAlgebra.mapDomainRingHom ℤ (negHom K) F

lemma reflect_apply {K : Type*} [AddCommGroup K]
    (F : AddMonoidAlgebra ℤ K) (x : K) : reflect F x = F (-x) := by
  classical
  have h := @Finsupp.mapDomain_apply K K ℤ _ (negHom K)
        (negHom_injective (K:=K)) F (-x)
  simpa [reflect, AddMonoidAlgebra.mapDomainRingHom_apply, negHom_apply] using h

lemma reflect_invariant {K : Type*} [Field K] [Algebra ℚ K]
    (F : AddMonoidAlgebra ℤ K)
    (hF : ∀ τ : K ≃ₐ[ℚ] K,
      AddMonoidAlgebra.mapDomainRingHom ℤ
        τ.toRingEquiv.toAddEquiv.toAddMonoidHom F = F) :
    ∀ τ : K ≃ₐ[ℚ] K,
      AddMonoidAlgebra.mapDomainRingHom ℤ
        τ.toRingEquiv.toAddEquiv.toAddMonoidHom (reflect F) = reflect F := by
  classical
  intro τ
  let t : K →+ K := τ.toRingEquiv.toAddEquiv.toAddMonoidHom
  let ν : K →+ K := negHom K
  have hcomm : t.comp ν = ν.comp t := by
    ext x
    change τ (-x) = -(τ x)
    exact map_neg τ x
  change AddMonoidAlgebra.mapDomainRingHom ℤ t
      (AddMonoidAlgebra.mapDomainRingHom ℤ ν F) =
      AddMonoidAlgebra.mapDomainRingHom ℤ ν F
  calc
    _ = AddMonoidAlgebra.mapDomainRingHom ℤ (t.comp ν) F := by
      have hc := AddMonoidAlgebra.mapDomainRingHom_comp (R:=ℤ) t ν
      -- the composition lemma is stated as equality of ring homs
      symm
      exact DFunLike.congr_fun hc F
    _ = AddMonoidAlgebra.mapDomainRingHom ℤ (ν.comp t) F := by rw [hcomm]
    _ = AddMonoidAlgebra.mapDomainRingHom ℤ ν
          (AddMonoidAlgebra.mapDomainRingHom ℤ t F) := by
      have hc := AddMonoidAlgebra.mapDomainRingHom_comp (R:=ℤ) ν t
      exact DFunLike.congr_fun hc F
    _ = _ := by rw [hF τ]

lemma product_reflect_invariant {K : Type*} [Field K] [Algebra ℚ K]
    (F : AddMonoidAlgebra ℤ K)
    (hF : ∀ τ : K ≃ₐ[ℚ] K,
      AddMonoidAlgebra.mapDomainRingHom ℤ
        τ.toRingEquiv.toAddEquiv.toAddMonoidHom F = F) :
    ∀ τ : K ≃ₐ[ℚ] K,
      AddMonoidAlgebra.mapDomainRingHom ℤ
        τ.toRingEquiv.toAddEquiv.toAddMonoidHom (F * reflect F) = F * reflect F := by
  intro τ
  rw [map_mul, hF τ, reflect_invariant F hF τ]

/-- The constant coefficient of `F * reflect F` is the sum of the integral squares
of the coefficients of `F`.  This innocuous observation supplies a genuinely
nonzero constant term without translating the invariant polynomial. -/
lemma product_reflect_zero_coeff {K : Type*} [Field K]
    (F : AddMonoidAlgebra ℤ K) :
    (F * reflect F) 0 = F.sum (fun _ n => n * n) := by
  classical
  rw [AddMonoidAlgebra.mul_apply]
  -- unwrap the outer sums
  change (F.sum (fun x r =>
      (reflect F).sum (fun y s => if x + y = 0 then r * s else 0))) = _
  apply Finsupp.sum_congr
  intro x hx
  change (Finsupp.mapDomain (negHom K) F).sum
      (fun y s => if x + y = 0 then F x * s else 0) = F x * F x
  rw [Finsupp.sum_mapDomain_index_inj (negHom_injective (K:=K))]
  change F.sum (fun y s => if x + -y = 0 then F x * s else 0) = F x * F x
  classical
  change (∑ y ∈ F.support, if x + -y = 0 then F x * F y else 0) = _
  simp [add_neg_eq_zero, Finset.sum_ite_eq, hx]

lemma product_reflect_const_ne_zero {K : Type*} [Field K]
    (F : AddMonoidAlgebra ℤ K) (h : F ≠ 0) : (F * reflect F) 0 ≠ 0 := by
  classical
  rw [product_reflect_zero_coeff]
  change (∑ x ∈ F.support, F x * F x) ≠ 0
  have hs : F.support.Nonempty := Finsupp.support_nonempty_iff.mpr h
  have hpos : 0 < ∑ x ∈ F.support, F x * F x := by
    apply Finset.sum_pos'
    · intro i hi
      exact mul_self_nonneg _
    · rcases hs with ⟨x, hx⟩
      exact ⟨x, hx, mul_self_pos.mpr (Finsupp.mem_support_iff.mp hx)⟩
  exact ne_of_gt hpos

/-- Evaluation of a formal additive exponential sum is its finite support sum. -/
lemma eval_as_sum {K : Type*} [Field K] [Algebra ℚ K]
    (e : K →ₐ[ℚ] ℂ) (F : AddMonoidAlgebra ℤ K) :
    (AddMonoidAlgebra.lift ℤ ℂ K
      { toFun := fun t : Multiplicative K => Complex.exp (e t.toAdd)
        map_one' := by simp
        map_mul' := by intro x y; simpa using Complex.exp_add (e x.toAdd) (e y.toAdd) }) F =
      F.sum (fun x n => (n : ℂ) * Complex.exp (e x)) := by
  classical
  let φ : Multiplicative K →* ℂ :=
      { toFun := fun t : Multiplicative K => Complex.exp (e t.toAdd)
        map_one' := by simp
        map_mul' := by intro x y; simpa using Complex.exp_add (e x.toAdd) (e y.toAdd) }
  change (AddMonoidAlgebra.lift ℤ ℂ K φ) F = _
  rw [AddMonoidAlgebra.lift_apply]
  apply Finsupp.sum_congr
  intro x hx
  change (F x) • φ (Multiplicative.ofAdd x) = _
  simp [Algebra.smul_def, φ]


/-- Symmetrisation once the exponents lie in a finite Galois field embedded in `ℂ`. -/
lemma galois_exp_sum_ne_zero
    {K : Type} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (e : K →ₐ[ℚ] ℂ) {ι : Type} [Fintype ι]
    (u : ι → K) (hu : Function.Injective u)
    (a : ι → ℤ) (j : ι) (ha : a j ≠ 0) :
    (∑ i, (a i : ℂ) * Complex.exp (e (u i))) ≠ 0 := by
  classical
  intro hv
  letI : CharZero K := charZero_of_injective_algebraMap (R:=ℚ) (A:=K) (RingHom.injective (algebraMap ℚ K))
  let F : AddMonoidAlgebra ℤ K := galoisProduct u a
  have hF0 : F ≠ 0 := galoisProduct_ne_zero u hu a j ha
  let H : AddMonoidAlgebra ℤ K := F * reflect F
  have hz0 : H 0 ≠ 0 := product_reflect_const_ne_zero F hF0
  have hinvF : ∀ τ : K ≃ₐ[ℚ] K,
      AddMonoidAlgebra.mapDomainRingHom ℤ
        τ.toRingEquiv.toAddEquiv.toAddMonoidHom F = F := map_galoisProduct u a
  have hinvH : ∀ τ : K ≃ₐ[ℚ] K,
      AddMonoidAlgebra.mapDomainRingHom ℤ
        τ.toRingEquiv.toAddEquiv.toAddMonoidHom H = H :=
    product_reflect_invariant F hinvF
  -- its complex evaluation vanishes
  let ev : AddMonoidAlgebra ℤ K →ₐ[ℤ] ℂ :=
    AddMonoidAlgebra.lift ℤ ℂ K
      { toFun := fun t : Multiplicative K => Complex.exp (e t.toAdd)
        map_one' := by simp
        map_mul' := by intro x y; simpa using Complex.exp_add (e x.toAdd) (e y.toAdd) }
  have hevF : ev F = 0 := by
    exact eval_galoisProduct_zero e u a hv
  have hevH : ev H = 0 := by
    dsimp [H]
    rw [map_mul, hevF]
    simp
  have hsumH : H.sum (fun x n => (n : ℂ) * Complex.exp (e x)) = 0 := by
    rw [← eval_as_sum e H]
    exact hevH
  -- turn the support into an honest finite list of distinct exponents
  let J := {x : K // x ∈ H.support}
  letI : Fintype J := Fintype.ofFinset H.support (fun x => Iff.rfl)
  let b' : J → ℂ := fun x => e (x : K)
  let a' : J → ℤ := fun x => H (x : K)
  have hzeroMem : (0:K) ∈ H.support := Finsupp.mem_support_iff.mpr hz0
  let j0 : J := ⟨0, hzeroMem⟩
  have hb'inj : Function.Injective b' := by
    intro x y h
    apply Subtype.ext
    exact e.injective h
  have hb'0 : b' j0 = 0 := by simp [b', j0]
  have ha'0 : a' j0 ≠ 0 := by simpa [a', j0] using hz0
  have hb'alg : ∀ k : J, IsAlgebraic ℚ (b' k) := by
    intro k
    -- a finite extension over Q has only algebraic elements
    have hk : IsIntegral ℚ (k : K) :=
      (Algebra.IsAlgebraic.isAlgebraic (R:=ℚ) (A:=K) (k : K)).isIntegral
    exact (IsIntegral.map e hk).isAlgebraic
  obtain ⟨f, hf0, hfroot⟩ := intPolynomial_for_family b' hb'alg
  have hrat : ∀ g : ℤ[X], ∃ q : ℚ,
      (∑ k ∈ (Finset.univ.erase j0),
        (a' k : ℂ) * Polynomial.aeval (b' k) g) = (q : ℂ) := by
    intro g
    obtain ⟨q, hq⟩ := weighted_sum_mem_fixed H hinvH g
    -- separate the constant term and then apply the embedding
    let term : K → K := fun x => (H x : K) * Polynomial.aeval x g
    have hq' : (∑ x ∈ H.support, term x) = (q : K) := by
      simpa [Finsupp.sum, term] using hq
    have hqJ : (∑ k : J, term (k : K)) = (q : K) := by
      rw [show (Finset.univ : Finset J) = H.support.attach from
        Finset.univ_eq_attach _]
      have hat := Finset.sum_attach H.support term
      rw [hat]
      exact hq'
    have hsep :
        (∑ k ∈ (Finset.univ.erase j0), term (k : K)) =
          (q : K) - term 0 := by
      have hm := (Finset.sum_erase_add _ _ (Finset.mem_univ j0) :
        (∑ k ∈ (Finset.univ.erase j0), term (k : K)) + term (j0 : K) =
          ∑ k : J, term (k : K))
      rw [hqJ] at hm
      exact eq_sub_of_add_eq hm
    let z : ℤ := g.coeff 0
    have ht0 : term 0 = (algebraMap ℚ K) ((H 0 : ℤ) * z) := by
      dsimp [term, z]
      simp [Polynomial.aeval_def]
    refine ⟨q - ((H 0 : ℤ) * z), ?_⟩
    have hsep' : (∑ k ∈ (Finset.univ.erase j0), term (k : K)) =
        (algebraMap ℚ K) (q - ((H 0 : ℤ) * z)) := by
      rw [hsep, ht0]
      simp
    have hc := congrArg e hsep'
    have hcomm (x : K) :
        e (Polynomial.aeval x g) = Polynomial.aeval (e x) g := by
      rw [Polynomial.aeval_def, Polynomial.aeval_def]
      calc
        e (Polynomial.eval₂ (algebraMap ℤ K) x g) =
            Polynomial.eval₂
              (e.toRingHom.comp (algebraMap ℤ K)) (e x) g :=
                Polynomial.hom_eval₂ g (algebraMap ℤ K) e.toRingHom x
        _ = Polynomial.eval₂ (algebraMap ℤ ℂ) (e x) g := by
              congr 1
              ext t
              simp
    -- expand the embedding over the finite sum
    simp only [map_sum, map_mul] at hc
    change (∑ k ∈ (Finset.univ.erase j0),
      (H (k:K) : ℂ) * Polynomial.aeval (e (k:K)) g) = _
    -- identify each mapped term
    simpa [term, hcomm] using hc
  have hno := no_vanishing_of_rational_root_sums b' hb'inj a' j0 hb'0 ha'0
       f hf0 hfroot hrat
  apply hno
  -- the displayed support sum is exactly the evaluation computed above
  change (∑ x : J, (a' x : ℂ) * Complex.exp (b' x)) = 0
  change (∑ x : J, (H (x:K) : ℂ) * Complex.exp (e (x:K))) = 0
  rw [show (Finset.univ : Finset J) = H.support.attach from
    Finset.univ_eq_attach _]
  have hat := Finset.sum_attach H.support
    (fun x : K => (H x : ℂ) * Complex.exp (e x))
  -- use the explicit attach identity
  rw [hat]
  simpa [Finsupp.sum] using hsumH


/-- Distinct algebraic complex exponents with one nonzero integral coefficient
cannot have a vanishing exponential sum.  The field used in the finite
symmetrisation is the normal closure of their span *inside the algebraic
numbers in* `ℂ`; thus it carries both a genuine embedding into `ℂ` and a
finite Galois action. -/
lemma algebraic_exp_sum_ne_zero
    {ι : Type} [Fintype ι]
    (b : ι → ℂ) (hb : ∀ i, IsAlgebraic ℚ (b i))
    (hbi : Function.Injective b)
    (a : ι → ℤ) (j : ι) (ha : a j ≠ 0) :
    (∑ i, (a i : ℂ) * Complex.exp (b i)) ≠ 0 := by
  classical
  -- Work in the relative algebraic closure; it is an absolute algebraic
  -- closure in this situation.
  let A : Type := ↥(algebraicClosure ℚ ℂ)
  letI : IsAlgClosure ℚ A := algebraicClosure.isAlgClosure ℚ ℂ
  letI : IsGalois ℚ A := IsAlgClosure.isGalois ℚ A
  let v : ι → A := fun i => ⟨b i, mem_algebraicClosure_iff.mpr (hb i)⟩
  let s : Set A := Set.range v
  letI : Finite (s : Set A) := (Set.finite_range v).to_subtype
  let L : FiniteGaloisIntermediateField ℚ A :=
      FiniteGaloisIntermediateField.adjoin ℚ s
  let K : Type := L.toIntermediateField
  letI : FiniteDimensional ℚ K := L.finiteDimensional
  letI : IsGalois ℚ K := L.isGalois
  let inc₁ : K →ₐ[ℚ] A := IntermediateField.val L.toIntermediateField
  let inc₂ : A →ₐ[ℚ] ℂ := IntermediateField.val (algebraicClosure ℚ ℂ)
  let e : K →ₐ[ℚ] ℂ := inc₂.comp inc₁
  let u : ι → K := fun i =>
    ⟨v i, FiniteGaloisIntermediateField.subset_adjoin ℚ s
      (by exact ⟨i, rfl⟩)⟩
  have heu (i : ι) : e (u i) = b i := rfl
  have hui : Function.Injective u := by
    intro i k h
    apply hbi
    have := congrArg e h
    simpa [heu] using this
  have hres := galois_exp_sum_ne_zero e u hui a j ha
  -- The inclusion maps are literally inclusions of subfields.
  simpa [heu] using hres

end
end LindemannSupport

-- END INLINED FILE: Mathlib/Support/lindemann_weierstrass_047b40c6f1/GaloisReduction.lean

namespace Submission

-- BEGIN INLINED FILE: Main.lean

open Polynomial
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem lindemann_weierstrass {n : ℕ} (x : Fin n → ℂ)
    (h_alg : ∀ i, IsAlgebraic ℚ (x i))
    (h_lin : LinearIndependent ℚ x) :
    AlgebraicIndependent ℚ (fun i => Complex.exp (x i)) :=
/-ResultProofBegin-/by
  -- First remove the multivariable-polynomial bookkeeping.  It only needs the
  -- rational-coefficient linear form of the exponential theorem.
  refine
    LindemannSupport.algebraicIndependent_exp_of_rational_linear ?_ x h_alg h_lin
  -- In a finite linear relation clear all denominators, and translate a term with
  -- nonzero coefficient to exponent zero.  An integer polynomial containing the
  -- other exponents exists (over `ℤ`, it need not be monic).
  apply LindemannSupport.rationalLinear_of_integerNonzero
  apply LindemannSupport.integerNonzero_of_withConstant
  apply LindemannSupport.withConstant_of_rootPolynomial
  -- The remaining goal is the arithmetic/analytic core for the roots of this
  -- fixed integer polynomial.  In the vacuous one-term case no approximation is
  -- needed.
  classical
  intro ι inst b hb_inj a i₀ hb0 ha0 f hf0 hf
  by_cases hm : ∃ j : ι, j ≠ i₀ ∧ a j ≠ 0
  · -- at this point there is a genuine nonzero root of `f`, and a second
    -- genuinely nonzero coefficient; this is the case to which
    -- `LindemannWeierstrass.exp_polynomial_approx` applies
    obtain ⟨j, hj, hja⟩ := hm
    have hj0 : b j ≠ 0 := by
      intro h
      exact hj (hb_inj (h.trans hb0.symm))
    have hjroot : b j ∈ f.aroots ℂ := hf j hj0
    obtain ⟨c, hc⟩ := LindemannWeierstrass.exp_polynomial_approx f hf0
    -- We shall actually take the prime far enough into the approximation so
    -- that the factorial estimate beats the fixed finite sum of coefficients.
    obtain ⟨P, hP⟩ := Filter.eventually_atTop.mp
      (LindemannSupport.eventually_const_mul_pow_div_factorial_sub_one_lt_one
        (∑ k ∈ (Finset.univ.erase i₀), ‖(a k : ℂ)‖) c)
    -- We may choose the auxiliary prime beyond the constant coefficient and the
    -- distinguished integer as well.  The resulting `gp` approximates
    -- simultaneously *all* the other exponents, since they are roots of `f`.
    obtain ⟨p, hp, pp⟩ :=
      Nat.exists_infinite_primes
        (max (max (max (Polynomial.eval 0 f).natAbs (a i₀).natAbs)
          f.leadingCoeff.natAbs) P + 1)
    have hp0 : p > (Polynomial.eval 0 f).natAbs :=
      lt_of_lt_of_le
        (Nat.lt_succ_of_le
          (le_trans
            (le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
            (Nat.le_max_left _ _))) hp
    obtain ⟨N, hNdiv, gp, hgpdeg, hgp⟩ := hc p hp0 pp
    have hgp' : ∀ k : ι, b k ≠ 0 →
        ‖N • Complex.exp (b k) - p • Polynomial.aeval (b k) gp‖
            ≤ c ^ p / (↑((p - 1).factorial) : ℝ) := by
      intro k hk
      exact hgp (hf k hk)
    -- If a relation vanished, the integer singled out at exponent zero would be
    -- almost a `p`-multiple of the values of `gp` at all the other exponents.
    -- The following is the elementary triangle-inequality part of the usual
    -- Hermite argument; importantly it uses the *factorial* estimate unchanged.
    intro hvan
    have hpa0 : ¬ (p : ℤ) ∣ a i₀ := by
      intro hdiv
      have hnat : p ∣ (a i₀).natAbs := (Int.natCast_dvd.mp hdiv)
      have hle : p ≤ (a i₀).natAbs :=
        Nat.le_of_dvd (Int.natAbs_pos.mpr ha0) hnat
      have hlt : (a i₀).natAbs < p :=
        lt_of_lt_of_le
          (Nat.lt_succ_of_le
            (le_trans
              (le_trans (Nat.le_max_right (Polynomial.eval 0 f).natAbs _)
                (Nat.le_max_left _ _))
              (Nat.le_max_left _ _))) hp
      exact (not_lt_of_ge hle) hlt
    have hsmall :
        ‖(N : ℂ) * (a i₀ : ℂ) +
           ∑ k ∈ (Finset.univ.erase i₀),
             (a k : ℂ) * ((p : ℂ) * Polynomial.aeval (b k) gp)‖
          ≤ (∑ k ∈ (Finset.univ.erase i₀), ‖(a k : ℂ)‖) *
              (c ^ p / (↑((p - 1).factorial) : ℝ)) := by
        exact LindemannSupport.norm_aux b hb_inj a i₀ hb0 N p gp
          (c ^ p / (↑((p - 1).factorial) : ℝ)) hgp' hvan
    have hpP : P ≤ p :=
      le_trans (le_trans (Nat.le_max_right
          (max (max (Polynomial.eval 0 f).natAbs (a i₀).natAbs)
            f.leadingCoeff.natAbs) _) (Nat.le_add_right _ _)) hp
    have hnorm_lt_one :
        ‖(N : ℂ) * (a i₀ : ℂ) +
           ∑ k ∈ (Finset.univ.erase i₀),
             (a k : ℂ) * ((p : ℂ) * Polynomial.aeval (b k) gp)‖ < 1 := by
      refine lt_of_le_of_lt hsmall ?_
      exact hP p hpP
    -- Non-monic polynomials require one small denominator step before reducing
    -- modulo the auxiliary prime.  A root `r` of an integral polynomial `f`
    -- has `f.leadingCoeff * r` integral.  Multiplying the value of any degree
    -- `D` integral polynomial at this root by `f.leadingCoeff ^ D` is
    -- therefore integral.  In particular the expression whose norm occurs
    -- in `hsmall` really is nonzero: after this common multiplication its
    -- constant summand is `N * a₀ * f.leadingCoeff ^ D`, and `p` divides
    -- none of those three integers.
    have hflead : f.leadingCoeff ≠ 0 := by
      apply Polynomial.leadingCoeff_ne_zero.mpr
      intro h
      apply hf0
      simp [h]
    have hpL : ¬ (p : ℤ) ∣ f.leadingCoeff := by
      intro hdiv
      have hnat : p ∣ f.leadingCoeff.natAbs := (Int.natCast_dvd.mp hdiv)
      have hle : p ≤ f.leadingCoeff.natAbs :=
        Nat.le_of_dvd (Int.natAbs_pos.mpr hflead) hnat
      have hlt : f.leadingCoeff.natAbs < p :=
        lt_of_lt_of_le
          (Nat.lt_succ_of_le
            (le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))) hp
      exact (not_lt_of_ge hle) hlt
    have hDelta_ne :
        (N : ℂ) * (a i₀ : ℂ) +
           ∑ k ∈ (Finset.univ.erase i₀),
             (a k : ℂ) * ((p : ℂ) * Polynomial.aeval (b k) gp) ≠ 0 := by
      apply
        LindemannSupport.combination_ne_zero_mod_prime_scaled b a i₀ N
          f.leadingCoeff p (p * f.natDegree - 1) gp pp hNdiv hpa0 hpL hgpdeg
      intro k hk
      have hk' : k ≠ i₀ := (Finset.mem_erase.mp hk).1
      have hb' : b k ≠ 0 := by
        intro hz
        exact hk' (hb_inj (hz.trans hb0.symm))
      exact LindemannSupport.integral_lc_mul_of_aroot f (hf k hb')
    have hDelta_int :
        IsIntegral ℤ ((f.leadingCoeff : ℂ)^(p * f.natDegree - 1) *
          ((N : ℂ) * (a i₀ : ℂ) +
             ∑ k ∈ (Finset.univ.erase i₀),
               (a k : ℂ) * ((p : ℂ) * Polynomial.aeval (b k) gp))) := by
      apply
        LindemannSupport.combination_scaled_integral b a i₀ N f.leadingCoeff p
          (p * f.natDegree - 1) gp hgpdeg
      intro k hk
      have hk' : k ≠ i₀ := (Finset.mem_erase.mp hk).1
      have hb' : b k ≠ 0 := by
        intro hz
        exact hk' (hb_inj (hz.trans hb0.symm))
      exact LindemannSupport.integral_lc_mul_of_aroot f (hf k hb')
    -- If the formal root sum is rational the last analytic step can now be
    -- completed, even for non-monic `f`: one must beat `|leadingCoeff|^D` as
    -- well as one.  This lemma contains that denominator calculation.  What
    -- remains is precisely the Galois symmetrisation of a relation not already
    -- invariant.
    classical
    by_cases hrat : ∀ g : ℤ[X], ∃ q : ℚ,
        (∑ k ∈ (Finset.univ.erase i₀),
          (a k : ℂ) * Polynomial.aeval (b k) g) = (q : ℂ)
    · exact (LindemannSupport.no_vanishing_of_rational_root_sums
          b hb_inj a i₀ hb0 ha0 f hf0 hf hrat) hvan
    · -- For a general alleged relation one first takes the nonzero product of
      -- its formal Galois translates in `AddMonoidAlgebra ℤ K`, and multiplies
      -- by the reversed product.  That invariant relation has a nonzero
      -- constant coefficient and satisfies `hrat`; see
      -- `map_galoisProduct`, `galoisProduct_weighted_rational`.  Pulling the
      -- finite normal closure of the `b k` into `ℂ` is the remaining step.
      have hbAlg : ∀ k : ι, IsAlgebraic ℚ (b k) := by
        intro k
        by_cases hz : b k = 0
        · rw [hz]
          exact isAlgebraic_zero
        · have hr := hf k hz
          have hZ : IsAlgebraic ℤ (b k) :=
            ⟨f, (Polynomial.mem_aroots.mp hr).1,
                (Polynomial.mem_aroots.mp hr).2⟩
          exact (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).1 hZ
      exact (LindemannSupport.algebraic_exp_sum_ne_zero
        b hbAlg hb_inj a i₀ ha0) hvan
  · push_neg at hm
    have hsingle : (∑ i, (a i : ℂ) * Complex.exp (b i)) =
          (a i₀ : ℂ) * Complex.exp (b i₀) := by
      apply Finset.sum_eq_single i₀
      · intro j hjmem hjne
        have hzero : a j = 0 := hm j hjne
        simp [hzero]
      · simp
    rw [hsingle]
    simp [hb0, ha0]
/-ResultProofEnd-/
/-ResultEnd-/
-- END INLINED FILE: Main.lean

end Submission
