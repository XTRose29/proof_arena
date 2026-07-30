import Mathlib

namespace Submission

namespace LeanEval
namespace Analysis

/-!
# The Hausdorff moment problem on the cube

`hausdorff_hildebrandt_schoenberg` is the Hausdorff–Hildebrandt–Schoenberg
theorem (1933): a multi-indexed real sequence is the moment sequence of a
signed bounded-variation Borel measure on the unit cube `Iᵈ = [0,1]ᵈ` iff it is
*Hausdorff bounded*. `hausdorff_positivity` is the Hausdorff positivity
criterion (1921): it comes from a *positive* finite measure iff it is completely
monotone (all iterated backward differences nonnegative).

A signed bounded-variation measure is encoded by its Jordan decomposition (a
difference of two finite positive measures); the moment integrals are taken over
the cube, so only the restriction to `Iᵈ` matters; the iterated backward
difference `Δᵏ` is given in closed form (the `ℕ`-subtraction `n − j` is genuine
in the `k ≤ n` regime the criteria use).

Mathlib has `SignedMeasure`, Jordan decomposition, finite measures, and set
integrals — enough to *state* the theorem — but no moment-problem machinery
(no Hausdorff/Hamburger/Stieltjes moment problem, no completely-monotone
sequences). The helper definitions below (`cube`, `monomial`, `momentOf`,
`IsMomentConfiguration`, `multiChoose`, `diff`, `HausdorffBounded`,
`IsPositiveMomentConfiguration`) are trusted (non-holes).

These are category-(b) candidates from §115 of the Knill survey
(`sections/115-moments.md`).
-/

open MeasureTheory
open scoped BigOperators NNReal

/-- The closed unit cube `Iᵈ = [0,1]ᵈ ⊆ ℝᵈ`. -/
def cube (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) := {x | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}

/-- The monomial `xⁿ = ∏ᵢ xᵢ^{nᵢ}` indexed by a multi-index `n ∈ ℕᵈ`. -/
def monomial {d : ℕ} (n : Fin d → ℕ) (x : EuclideanSpace ℝ (Fin d)) : ℝ := ∏ i, (x i) ^ (n i)

/-- The `n`-th moment `∫_{Iᵈ} xⁿ dμ` of a (positive) measure `μ`, integrated
over the cube. -/
noncomputable def momentOf {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) (n : Fin d → ℕ) : ℝ :=
  ∫ x in cube d, monomial n x ∂μ

/-- The multi-index binomial coefficient `C(n,k) = ∏ᵢ C(nᵢ, kᵢ)`. -/
def multiChoose {d : ℕ} (n k : Fin d → ℕ) : ℕ := ∏ i, (n i).choose (k i)

/-- The iterated **backward** partial difference `(Δᵏa)ₙ`, in closed form
`∑_{0 ≤ j ≤ k} (−1)^{|k−j|} C(k,j) a_{n−j}` — the iterate of
`(Δᵢa)ₙ = a_{n−eᵢ} − aₙ`. The `ℕ`-subtraction `n − j` is genuine whenever
`k ≤ n` (the regime used below). -/
noncomputable def diff {d : ℕ} (a : (Fin d → ℕ) → ℝ) (k n : Fin d → ℕ) : ℝ :=
  ∑ j ∈ Finset.Iic k,
    (-1 : ℝ) ^ (∑ i, (k i - j i)) * (multiChoose k j : ℝ) * a (n - j)

/-- `a` is a **positive** moment configuration: realized by a single finite
*positive* measure on the cube. -/
def IsPositiveMomentConfiguration {d : ℕ} (a : (Fin d → ℕ) → ℝ) : Prop :=
  ∃ μ : Measure (EuclideanSpace ℝ (Fin d)), IsFiniteMeasure μ ∧ ∀ n, a n = momentOf μ n



end Analysis
end LeanEval

open LeanEval.Analysis
open MeasureTheory
open scoped BigOperators NNReal
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/

namespace LeanEval.Analysis
lemma piFinset_Iic {d} (k:Fin d→ℕ) :
 (Fintype.piFinset (fun i : Fin d => Finset.Iic (k i))) = Finset.Iic k := by
 classical
 ext j
 simp only [Fintype.mem_piFinset, Finset.mem_Iic]
 constructor
 · intro h i; exact h i
 · intro h i; exact h i

lemma prod_term {d} (k n j : Fin d → ℕ) (x : EuclideanSpace ℝ (Fin d)) :
 (-1 : ℝ) ^ (∑ i, (k i - j i)) * (multiChoose k j : ℝ) * monomial (fun i => n i - j i) x
 = ∏ i, ((-1 : ℝ)^(k i-j i) * ((k i).choose (j i) : ℝ) * (x i)^(n i-j i)) := by
  classical
  simp only [multiChoose, monomial, Nat.cast_prod]
  rw [← Finset.prod_pow_eq_pow_sum]
  simp_rw [← Finset.prod_mul_distrib]
  -- left grouping?
lemma uni (k n : ℕ) (hkn:k≤n) (x:ℝ) :
 (∑ j ∈ Finset.Iic k, (-1:ℝ)^(k-j) * (k.choose j : ℝ) * x^(n-j)) =
 x^(n-k) * (1-x)^k := by
 classical
 have hi : Finset.Iic k = Finset.range (k+1) := by
   ext j
   simp [Finset.mem_Iic]
 rw [hi]
 -- rewrite
 have hsplit : ∀ j ∈ Finset.range (k+1), n-j = (n-k) + (k-j) := by
   intro j hj
   have hjk : j ≤ k := by simpa [Nat.lt_succ_iff] using (Finset.mem_range.mp hj)
   omega
 calc
  (∑ j ∈ Finset.range (k+1), (-1:ℝ)^(k-j) * (k.choose j : ℝ) * x^(n-j))
      = ∑ j ∈ Finset.range (k+1),
          x^(n-k) * ((-1:ℝ)^(k-j) * (k.choose j : ℝ) * x^(k-j)) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hsplit j hj, pow_add]
            ring
  _ = x^(n-k) * ∑ j ∈ Finset.range (k+1), ((-1:ℝ)^(k-j) * (k.choose j : ℝ) * x^(k-j)) := by
            rw [Finset.mul_sum]
            -- notation sum twice sums? mul_sum s f for no double binder; our sum uses ∑ j in = ok
  _ = x^(n-k) * (1-x)^k := by
            congr 1
            have hp := add_pow (1:ℝ) (-x) k
            -- hp : (1 + -x)^k = sum 1^m * (-x)^... * choose
            -- commute
            rw [sub_eq_add_neg]
            -- goal sum = (1 + -x)^k
            rw [hp]
            apply Finset.sum_congr rfl
            intro j hj
            have : (-x)^(k-j) = (-1:ℝ)^(k-j) * x^(k-j) := by
              -- -x = (-1)*x
              rw [show -x = (-1:ℝ)*x by ring, mul_pow]
            rw [this]
            simp
            ring
lemma multialg {d} (k n : Fin d → ℕ) (hkn:k≤n) (x : EuclideanSpace ℝ (Fin d)) :
 (∑ j ∈ Finset.Iic k,
   (-1:ℝ)^(∑ i, (k i - j i)) * (multiChoose k j : ℝ) * monomial (n-j) x)
 = monomial (n-k) x * ∏ i, (1-x i)^(k i) := by
 classical
 -- expand summands into a product
 calc
  (∑ j ∈ Finset.Iic k,
   (-1:ℝ)^(∑ i, (k i - j i)) * (multiChoose k j : ℝ) * monomial (n-j) x)
   = ∑ j ∈ Finset.Iic k,
       ∏ i, ((-1:ℝ)^(k i-j i) * ((k i).choose (j i) : ℝ) * (x i)^(n i-j i)) := by
         apply Finset.sum_congr rfl
         intro j hj
         
         have he : (n - j) = (fun i => n i - j i) := by rfl
         simpa [he] using (prod_term k n j x)
  _ = ∏ i, ∑ t ∈ Finset.Iic (k i),
          ((-1:ℝ)^(k i-t) * ((k i).choose t : ℝ) * (x i)^(n i-t)) := by
        -- use prod_univ_sum backwards
        rw [Finset.prod_univ_sum]
        rw [piFinset_Iic]
  _ = ∏ i, ((x i)^(n i-k i) * (1-x i)^(k i)) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact uni (k i) (n i) (hkn i) (x i)
  _ = monomial (n-k) x * ∏ i, (1-x i)^(k i) := by
        simp only [monomial]
        rw [← Finset.prod_mul_distrib]
        rfl


lemma cube_eq_preimage (d:ℕ) : cube d = (PiLp.homeomorph (p:= (2:ENNReal)) (fun _ : Fin d => ℝ)) ⁻¹' Set.Icc (0 : Fin d → ℝ) 1 := by
 ext x
 simp only [cube, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Icc]
 change (∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1) ↔ _
 change _ ↔ (0 ≤ (fun i => x.ofLp i)) ∧ ((fun i => x.ofLp i) ≤ (1 : Fin d → ℝ))
 constructor
 · intro h; exact ⟨fun i => (h i).1, fun i => (h i).2⟩
 · intro h i; exact ⟨h.1 i, h.2 i⟩
lemma cube_compact (d:ℕ) : IsCompact (cube d) := by
 rw [cube_eq_preimage]
 exact (PiLp.homeomorph (p:= (2:ENNReal)) (fun _ : Fin d => ℝ)).isCompact_preimage.2 isCompact_Icc
lemma continuous_monomial {d} (n:Fin d→ℕ) : Continuous (monomial n) := by
 unfold monomial
 fun_prop
lemma integrable_monomial {d} (μ:Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure μ] (n:Fin d→ℕ) :
 Integrable (monomial n) (μ.restrict (cube d)) := by
 -- convert integrableOn
 have h : IntegrableOn (monomial n) (cube d) μ :=
   ContinuousOn.integrableOn_compact (μ:=μ) (cube_compact d) (continuous_monomial n).continuousOn
 exact h


lemma diff_moment {d} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure μ]
 (k n : Fin d → ℕ) :
 diff (fun r => momentOf μ r) k n =
  ∫ x in cube d, ∑ j ∈ Finset.Iic k,
       (-1:ℝ)^(∑ i, (k i - j i)) * (multiChoose k j : ℝ) * monomial (n-j) x ∂μ := by
 classical
 unfold diff
 let c : (Fin d → ℕ) → ℝ := fun j => (-1:ℝ)^(∑ i, (k i - j i)) * (multiChoose k j : ℝ)
 change (∑ j ∈ Finset.Iic k, c j * momentOf μ (n-j)) = _
 have hj (j : Fin d → ℕ) : Integrable (fun x => c j * monomial (n-j) x) (μ.restrict (cube d)) := by
   exact (integrable_monomial μ (n-j)).const_mul _
 rw [MeasureTheory.integral_finset_sum]
 · apply Finset.sum_congr rfl
   intro j hjmem
   change c j * momentOf μ (n-j) = _
   simp only [momentOf]
   rw [MeasureTheory.integral_const_mul]
 · intro j hjmem
   exact hj j
lemma diff_moment_eq {d} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure μ]
 (k n : Fin d → ℕ) (h: k ≤ n) :
 diff (fun r => momentOf μ r) k n =
  ∫ x in cube d, monomial (n-k) x * ∏ i, (1-x i)^(k i) ∂μ := by
 rw [diff_moment]
 simp_rw [multialg k n h]
lemma integrand_nonneg {d} (k n : Fin d → ℕ)
 (x:EuclideanSpace ℝ (Fin d)) (hx:x∈cube d) :
 0 ≤ monomial (n-k) x * ∏ i, (1-x i)^(k i) := by
 have hxi : ∀ i : Fin d, 0 ≤ x i ∧ x i ≤ 1 := by
   intro i
   simpa [cube, Set.mem_Icc] using hx i
 apply mul_nonneg
 · -- monomial
   unfold monomial
   exact Finset.prod_nonneg (fun i hi => pow_nonneg (hxi i).1 _)
 · exact Finset.prod_nonneg (fun i hi => pow_nonneg (sub_nonneg.mpr (hxi i).2) _)

lemma moment_diff_nonneg {d} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure μ]
 (k n : Fin d → ℕ) (h:k≤n) :
 0 ≤ diff (fun r => momentOf μ r) k n := by
 rw [diff_moment_eq μ k n h]
 exact MeasureTheory.setIntegral_nonneg (cube_compact d).measurableSet
   (fun x hx => integrand_nonneg k n x hx)


lemma diff_zero {d} (a : (Fin d → ℕ) → ℝ) (n : Fin d → ℕ) : diff a 0 n = a n := by
  classical
  have hz : Finset.Iic (0 : Fin d → ℕ) = {0} := by
    ext j
    simp only [Finset.mem_Iic, Finset.mem_singleton]
    constructor
    · intro h; exact le_antisymm h (by intro i; exact Nat.zero_le _)
    · intro h; simpa [h]
  rw [diff, hz]
  simp [multiChoose]

lemma bernstein_weight_nonneg {d} {a : (Fin d → ℕ) → ℝ}
    (ha : ∀ k n : Fin d → ℕ, k ≤ n → 0 ≤ diff a k n)
    (N r : Fin d → ℕ) :
    0 ≤ (multiChoose N r : ℝ) * diff a (N - r) N := by
  apply mul_nonneg
  · exact_mod_cast (Nat.zero_le (multiChoose N r))
  · apply ha
    intro i
    exact Nat.sub_le _ _


/-- A useful zero-extension lemma for the rectangular binomial coefficients. -/
lemma multiChoose_zero {d : ℕ} {u v : Fin d → ℕ} (h : ¬ v ≤ u) :
    multiChoose u v = 0 := by
  classical
  simp only [Pi.le_def] at h
  push_neg at h
  rcases h with ⟨i, hi⟩
  unfold multiChoose
  exact Finset.prod_eq_zero (Finset.mem_univ i) (Nat.choose_eq_zero_of_lt hi)

/-- Choosing two disjoint subsets is symmetric in the two subsets.  We use the
version with no side conditions; the `choose`'s are zero outside the range. -/
lemma choose_choose_symm (n s p : ℕ) :
    n.choose s * (n-s).choose p = n.choose p * (n-p).choose s := by
  have h1 := Nat.choose_mul (n:=n) (k:=s+p) (s:=s) (by omega : s ≤ s+p)
  have h2 := Nat.choose_mul (n:=n) (k:=p+s) (s:=p) (by omega : p ≤ p+s)
  rw [Nat.add_sub_cancel_left] at h1
  rw [Nat.add_sub_cancel_left] at h2
  rw [← h1, ← h2]
  rw [Nat.add_comm p s]
  rw [Nat.choose_symm_add]

lemma multiChoose_choose_symm {d : ℕ} (n s p : Fin d → ℕ) :
    (multiChoose n s : ℝ) * (multiChoose (n-s) p : ℝ) =
      (multiChoose n p : ℝ) * (multiChoose (n-p) s : ℝ) := by
  classical
  simp only [multiChoose, Nat.cast_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  norm_cast
  exact choose_choose_symm (n i) (s i) (p i)

/-- The elementary alternating binomial sum, in a rectangular box. -/
lemma alt_multi {d : ℕ} (u : Fin d → ℕ) :
 (∑ s ∈ Finset.Iic u,
     (-1 : ℝ)^(∑ i, (u i - s i)) * (multiChoose u s : ℝ))
       = if u = 0 then 1 else 0 := by
  classical
  -- the box is a product of one-dimensional boxes
  calc
    (∑ s ∈ Finset.Iic u,
       (-1 : ℝ)^(∑ i, (u i - s i)) * (multiChoose u s : ℝ))
       = ∑ s ∈ Finset.Iic u,
           ∏ i, ((-1 : ℝ)^(u i - s i) * ((u i).choose (s i) : ℝ)) := by
            apply Finset.sum_congr rfl
            intro s hs
            simp only [multiChoose, Nat.cast_prod]
            rw [← Finset.prod_pow_eq_pow_sum]
            rw [← Finset.prod_mul_distrib]
    _ = ∏ i, ∑ t ∈ Finset.Iic (u i),
             ((-1 : ℝ)^(u i - t) * ((u i).choose t : ℝ)) := by
            rw [Finset.prod_univ_sum]
            rw [piFinset_Iic]
    _ = ∏ i, (0:ℝ)^(u i) := by
            apply Finset.prod_congr rfl
            intro i hi
            have h := uni (u i) (u i) (le_rfl) (1:ℝ)
            simpa using h
    _ = if u = 0 then 1 else 0 := by
            by_cases h0 : u = 0
            · subst u
              simp
            · have hex : ∃ i, u i ≠ 0 := by
                by_contra hn
                push_neg at hn
                exact h0 (funext hn)
              rcases hex with ⟨i, hi⟩
              have hz : (0:ℝ)^(u i) = 0 := zero_pow hi
              rw [if_neg h0]
              exact Finset.prod_eq_zero (Finset.mem_univ i) hz

/-- Binomial inversion, simultaneously in all coordinates.  This is the small
algebraic heart of the Bernstein construction.  Written this way there are no
boundary terms: outside a smaller rectangle the binomial coefficient is zero. -/
lemma binomial_diff_sum {d : ℕ} (a : (Fin d → ℕ) → ℝ) (k n : Fin d → ℕ)
    (hkn : k ≤ n) :
   (∑ s ∈ Finset.Iic k, (multiChoose k s : ℝ) * diff a (k-s) n)
        = a (n-k) := by
  classical
  -- It is convenient to extend every inner sum to the same rectangle.
  have hsub (s : Fin d → ℕ) : Finset.Iic (k-s) ⊆ Finset.Iic k := by
    intro j hj
    have hj' : j ≤ k-s := (Finset.mem_Iic.mp hj)
    exact Finset.mem_Iic.mpr (le_trans hj' (by intro i; exact Nat.sub_le _ _))
  have hext (s : Fin d → ℕ) (F : (Fin d → ℕ) → ℝ)
      (hF : ∀ j, ¬ j ≤ k-s → F j = 0) :
      (∑ j ∈ Finset.Iic (k-s), F j) = ∑ j ∈ Finset.Iic k, F j := by
    apply Finset.sum_subset (hsub s)
    intro j hj hjnot
    apply hF j
    exact fun hle => hjnot (Finset.mem_Iic.mpr hle)
  -- expand `diff` and use the zero extension
  calc
    (∑ s ∈ Finset.Iic k, (multiChoose k s : ℝ) * diff a (k-s) n)
       = ∑ s ∈ Finset.Iic k, ∑ j ∈ Finset.Iic k,
            (multiChoose k s : ℝ) *
             ((-1:ℝ)^(∑ i, ((k-s) i - j i)) *
               (multiChoose (k-s) j : ℝ) * a (n-j)) := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [diff]
          rw [hext s (fun j =>
             (-1:ℝ)^(∑ i, ((k-s) i - j i)) *
                (multiChoose (k-s) j : ℝ) * a (n-j))]
          · rw [Finset.mul_sum]
          · intro j hj
            have z : multiChoose (k-s) j = 0 := multiChoose_zero hj
            simp [z]
    _ = ∑ j ∈ Finset.Iic k, ∑ s ∈ Finset.Iic k,
            (multiChoose k s : ℝ) *
             ((-1:ℝ)^(∑ i, ((k-s) i - j i)) *
               (multiChoose (k-s) j : ℝ) * a (n-j)) := by
          rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.Iic k,
            ((multiChoose k j : ℝ) * a (n-j)) *
              (∑ s ∈ Finset.Iic k,
                 (-1:ℝ)^(∑ i, ((k-j) i - s i)) *
                    (multiChoose (k-j) s : ℝ)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s hs
          have hpow :
              (∑ i, ((k-s) i - j i)) =
                ∑ i, ((k-j) i - s i) := by
                apply Finset.sum_congr rfl
                intro i hi
                change k i - s i - j i = k i - j i - s i
                omega
          have hch := multiChoose_choose_symm k s j
          rw [hpow]
          -- only commuting scalar factors now
          calc
            _ = ((multiChoose k s : ℝ) * (multiChoose (k-s) j : ℝ)) *
                  (((-1:ℝ)^(∑ i, ((k-j) i - s i))) * a (n-j)) := by ring
            _ = ((multiChoose k j : ℝ) * (multiChoose (k-j) s : ℝ)) *
                  (((-1:ℝ)^(∑ i, ((k-j) i - s i))) * a (n-j)) := by rw [hch]
            _ = _ := by ring
    _ = ∑ j ∈ Finset.Iic k,
           ((multiChoose k j : ℝ) * a (n-j)) *
              (if k-j = 0 then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro j hj
          congr 1
          -- discard the zero coefficients outside the smaller box
          symm
          calc
            (if k-j = 0 then (1:ℝ) else 0)
               = ∑ s ∈ Finset.Iic (k-j),
                    (-1:ℝ)^(∑ i, ((k-j) i - s i)) *
                       (multiChoose (k-j) s : ℝ) := (alt_multi (k-j)).symm
            _ = ∑ s ∈ Finset.Iic k,
                    (-1:ℝ)^(∑ i, ((k-j) i - s i)) *
                       (multiChoose (k-j) s : ℝ) := by
                  apply Finset.sum_subset
                  · intro s hs'
                    exact Finset.mem_Iic.mpr
                      (le_trans (Finset.mem_Iic.mp hs') (by intro i; exact Nat.sub_le _ _))
                  · intro s hs1 hs2
                    have hn : ¬ s ≤ k-j := fun hle => hs2 (Finset.mem_Iic.mpr hle)
                    have z : multiChoose (k-j) s = 0 := multiChoose_zero hn
                    simp [z]
    _ = a (n-k) := by
          have hk_mem : k ∈ Finset.Iic k := Finset.mem_Iic.mpr (le_rfl)
          rw [Finset.sum_eq_single_of_mem k hk_mem]
          · simp [multiChoose]
          · intro b hb hbne
            have hle : b ≤ k := Finset.mem_Iic.mp hb
            have hne : k - b ≠ 0 := by
              intro hz
              have hge : k ≤ b := by
                intro i
                have hz' : k i - b i = 0 := congr_fun hz i
                exact Nat.le_of_sub_eq_zero hz'
              exact hbne (le_antisymm hle hge)
            simp [hne]


lemma multiChoose_mul {d : ℕ} (N r m : Fin d → ℕ) (hmr : m ≤ r) :
    (multiChoose N r : ℝ) * (multiChoose r m : ℝ) =
       (multiChoose N m : ℝ) * (multiChoose (N-m) (r-m) : ℝ) := by
  classical
  simp only [multiChoose, Nat.cast_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  norm_cast
  exact Nat.choose_mul (hmr i)

/-- Factorial Bernstein moments.  This exact finite identity is often the most
useful form of the Hausdorff construction. -/
lemma bernstein_choose_moment {d : ℕ} (a : (Fin d → ℕ) → ℝ)
    (N m : Fin d → ℕ) (hmN : m ≤ N) :
 (∑ r ∈ Finset.Iic N,
      ((multiChoose N r : ℝ) * (multiChoose r m : ℝ)) * diff a (N-r) N)
       = (multiChoose N m : ℝ) * a m := by
  classical
  -- terms with `m` not below `r` are zero
  calc
    (∑ r ∈ Finset.Iic N,
      ((multiChoose N r : ℝ) * (multiChoose r m : ℝ)) * diff a (N-r) N)
       = ∑ r ∈ Finset.Icc m N,
          ((multiChoose N r : ℝ) * (multiChoose r m : ℝ)) * diff a (N-r) N := by
            symm
            apply Finset.sum_subset
            · intro r hr
              exact Finset.mem_Iic.mpr (Finset.mem_Icc.mp hr).2
            · intro r hr hnot
              have hn : ¬ m ≤ r := by
                intro hmr
                exact hnot (Finset.mem_Icc.mpr ⟨hmr, Finset.mem_Iic.mp hr⟩)
              have z : multiChoose r m = 0 := multiChoose_zero hn
              simp [z]
    _ = ∑ s ∈ Finset.Iic (N-m),
          ((multiChoose N m : ℝ) * (multiChoose (N-m) s : ℝ)) *
             diff a ((N-m)-s) N := by
            -- translation `s ↦ m+s` identifies the two boxes
            symm
            apply Finset.sum_bij (fun s hs => m+s)
            · intro s hs
              have hs' : s ≤ N-m := Finset.mem_Iic.mp hs
              apply Finset.mem_Icc.mpr
              constructor
              · intro i; exact Nat.le_add_right _ _
              · intro i
                have H := Nat.add_le_of_le_sub (hmN i) (hs' i)
                -- `H : s i + m i ≤ N i`
                simpa [add_comm] using H
            · intro s₁ h₁ s₂ h₂ he
              funext i
              have hi : (m+s₁) i = (m+s₂) i := congr_fun he i
              exact Nat.add_left_cancel hi
            · intro r hr
              have hr' := Finset.mem_Icc.mp hr
              refine ⟨r-m, Finset.mem_Iic.mpr ?_, ?_⟩
              · intro i
                exact Nat.sub_le_sub_right (hr'.2 i) (m i)
              · funext i
                change m i + (r i - m i) = r i
                exact Nat.add_sub_of_le (hr'.1 i)
            · intro s hs
              have hs' : s ≤ N-m := Finset.mem_Iic.mp hs
              have hmr : m ≤ m+s := by
                intro i; exact Nat.le_add_right _ _
              rw [multiChoose_mul N (m+s) m hmr]
              have hsub : (m+s)-m = s := by
                funext i
                exact Nat.add_sub_cancel_left _ _
              have hsub2 : N-(m+s) = (N-m)-s := by
                funext i
                change N i - (m i + s i) = N i - m i - s i
                omega
              rw [hsub, hsub2]
    _ = (multiChoose N m : ℝ) *
          (∑ s ∈ Finset.Iic (N-m),
             (multiChoose (N-m) s : ℝ) * diff a ((N-m)-s) N) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro s hs
            ring
    _ = (multiChoose N m : ℝ) * a m := by
            have hkn : N-m ≤ N := by
              intro i; exact Nat.sub_le _ _
            rw [binomial_diff_sum a (N-m) N hkn]
            have hh : N - (N-m) = m := by
              funext i
              exact Nat.sub_sub_self (hmN i)
            rw [hh]

/-- The total Bernstein mass is independent of the level. -/
lemma bernstein_mass {d : ℕ} (a : (Fin d → ℕ) → ℝ) (N : Fin d → ℕ) :
 (∑ r ∈ Finset.Iic N, (multiChoose N r : ℝ) * diff a (N-r) N)
    = a 0 := by
  simpa using (binomial_diff_sum a N N (by intro i; exact le_rfl))

/-- Multiplication in the falling-factorial basis. -/
lemma mul_descFactorial (t j : ℕ) :
    t * t.descFactorial j =
       t.descFactorial (j+1) + j * t.descFactorial j := by
  by_cases h : j ≤ t
  · rw [Nat.descFactorial_succ]
    rw [← Nat.add_mul, Nat.sub_add_cancel h]
  · have hlt : t < j := lt_of_not_ge h
    have h1 : t.descFactorial j = 0 :=
      Nat.descFactorial_eq_zero_iff_lt.mpr hlt
    simp [h1]


lemma cast_desc_prod (t m : ℕ) :
    (t.descFactorial m : ℝ) = ∏ j ∈ Finset.range m, ((t:ℝ) - (j:ℝ)) := by
  rw [← descPochhammer_eval_eq_descFactorial ℝ t m]
  rw [descPochhammer_eval_eq_prod_range]

/-- Normalized falling factorials are products of equally spaced factors; this
is handy for the final elementary limit estimate. -/
lemma cast_desc_div (t m q : ℕ) :
    (t.descFactorial m : ℝ) / (q:ℝ)^m =
      ∏ j ∈ Finset.range m, ((t:ℝ)/(q:ℝ) - (j:ℝ)/(q:ℝ)) := by
  rw [cast_desc_prod]
  have hq : (q:ℝ)^m = ∏ _j ∈ Finset.range m, (q:ℝ) := by simp
  rw [hq, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  rw [sub_div]


def multiDesc {d : ℕ} (r m : Fin d → ℕ) : ℝ :=
  ∏ i, (r i).descFactorial (m i)

lemma multiDesc_eq {d : ℕ} (r m : Fin d → ℕ) :
    multiDesc r m = (∏ i, ((m i).factorial : ℝ)) * (multiChoose r m : ℝ) := by
  classical
  unfold multiDesc multiChoose
  simp only [Nat.cast_prod, Nat.cast_ofNat, Nat.cast_mul]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  norm_cast
  exact Nat.descFactorial_eq_factorial_mul_choose _ _

lemma bernstein_desc_moment {d : ℕ} (a : (Fin d → ℕ) → ℝ)
    (N m : Fin d → ℕ) (hm : m ≤ N) :
 (∑ r ∈ Finset.Iic N,
       ((multiChoose N r : ℝ) * diff a (N-r) N) * multiDesc r m)
        = multiDesc N m * a m := by
  classical
  have h := bernstein_choose_moment a N m hm
  have D := (∏ i, ((m i).factorial : ℝ))
  simp_rw [multiDesc_eq]
  -- we'll rearrange the finite sum and use `h`
  calc
    (∑ r ∈ Finset.Iic N,
       (↑(multiChoose N r) * diff a (N-r) N) *
          ((∏ i, ((m i).factorial : ℝ)) * (multiChoose r m : ℝ)))
       = (∏ i, ((m i).factorial : ℝ)) *
            (∑ r ∈ Finset.Iic N,
               ((multiChoose N r : ℝ) * (multiChoose r m : ℝ)) * diff a (N-r) N) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro r hr
            ring
    _ = (∏ i, ((m i).factorial : ℝ)) *
          ((multiChoose N m : ℝ) * a m) := by rw [h]
    _ = ((∏ i, ((m i).factorial : ℝ)) * (multiChoose N m : ℝ)) * a m := by ring

def level {d : ℕ} (q : ℕ) : Fin d → ℕ := fun _ => q

noncomputable def gridPoint {d : ℕ} (q : ℕ) (r : Fin d → ℕ)
    (hr : r ∈ Finset.Iic (level (d:=d) q)) :
      {x : EuclideanSpace ℝ (Fin d) // x ∈ cube d} := by
  classical
  let y : EuclideanSpace ℝ (Fin d) :=
    WithLp.toLp (2:ENNReal) (fun i : Fin d => (r i : ℝ) / (q : ℝ))
  refine ⟨y, ?_⟩
  intro i
  change (r i : ℝ) / (q : ℝ) ∈ Set.Icc (0:ℝ) 1
  have hle : r i ≤ q := (Finset.mem_Iic.mp hr) i
  constructor
  · exact div_nonneg (by positivity) (by positivity)
  · by_cases hq : q = 0
    · have hr0 : r i = 0 := by omega
      simp [hr0, hq]
    · apply (div_le_iff₀ (by exact_mod_cast (Nat.zero_lt_of_ne_zero hq))).2
      norm_num
      exact_mod_cast hle

@[simp] lemma gridPoint_apply {d : ℕ} (q : ℕ) (r : Fin d → ℕ)
    (hr : r ∈ Finset.Iic (level (d:=d) q)) (i : Fin d) :
    ((↑(gridPoint q r hr) : EuclideanSpace ℝ (Fin d)) i) = (r i : ℝ) / (q : ℝ) := by
  rfl

noncomputable def atom {d : ℕ} (q : ℕ) (r : Fin d → ℕ)
    (hr : r ∈ Finset.Iic (level (d:=d) q)) :
    FiniteMeasure {x : EuclideanSpace ℝ (Fin d) // x ∈ cube d} :=
  ⟨Measure.dirac (gridPoint q r hr), inferInstance⟩

noncomputable def bernMeasure {d : ℕ} (a : (Fin d → ℕ) → ℝ)
    (q : ℕ) : FiniteMeasure {x : EuclideanSpace ℝ (Fin d) // x ∈ cube d} :=
  ∑ r ∈ Finset.Iic (level (d:=d) q),
     if h : r ∈ Finset.Iic (level (d:=d) q) then
       Real.toNNReal ((multiChoose (level (d:=d) q) r : ℝ) *
          diff a (level (d:=d) q - r) (level (d:=d) q)) • atom q r h
     else 0

lemma grid_monomial {d : ℕ} (q : ℕ) (r n : Fin d → ℕ)
    (hr : r ∈ Finset.Iic (level (d:=d) q)) :
    monomial n ((gridPoint q r hr :
      {x : EuclideanSpace ℝ (Fin d) // x ∈ cube d}) :
        EuclideanSpace ℝ (Fin d)) = ∏ i, ((r i : ℝ) / q)^(n i) := by
  unfold monomial
  apply Finset.prod_congr rfl
  intro i hi
  rw [gridPoint_apply]

open scoped ENNReal
lemma bern_integral {d : ℕ} {a : (Fin d → ℕ) → ℝ}
    (ha : ∀ k n : Fin d → ℕ, k ≤ n → 0 ≤ diff a k n)
    (q : ℕ) (n : Fin d → ℕ) :
 (∫ x : {x : EuclideanSpace ℝ (Fin d) // x ∈ cube d},
       monomial n (x : EuclideanSpace ℝ (Fin d)) ∂(bernMeasure a q : Measure _))
   = ∑ r ∈ Finset.Iic (level (d:=d) q),
       ((multiChoose (level (d:=d) q) r : ℝ) *
          diff a (level (d:=d) q-r) (level (d:=d) q)) *
            (∏ i, ((r i : ℝ)/q)^(n i)) := by
  classical
  let X := {x : EuclideanSpace ℝ (Fin d) // x ∈ cube d}
  letI : CompactSpace X := isCompact_iff_compactSpace.mp (cube_compact d)
  let p : BoundedContinuousFunction X ℝ :=
    BoundedContinuousFunction.mkOfCompact
      ⟨(fun x : X => monomial n (x : EuclideanSpace ℝ (Fin d))),
        (continuous_monomial n).comp continuous_subtype_val⟩
  have hf (ν : FiniteMeasure X) :
      Integrable (fun x : X => monomial n (x : EuclideanSpace ℝ (Fin d)))
        (ν : Measure X) := by
      exact p.integrable (ν : Measure X)
  -- first split the finite measure sum
  change (∫ x : X, monomial n (x : EuclideanSpace ℝ (Fin d))
       ∂(bernMeasure a q : Measure X)) = _
  simp only [bernMeasure, FiniteMeasure.toMeasure_sum]
  rw [MeasureTheory.integral_finset_sum_measure]
  · apply Finset.sum_congr rfl
    intro r hr
    -- remove the decidable guard in the definition
    simp only [hr, dite_true, ite_true]
    rw [FiniteMeasure.toMeasure_smul]
    rw [MeasureTheory.integral_smul_nnreal_measure]
    -- the atom is a dirac
    change (Real.toNNReal
          ((multiChoose (level (d:=d) q) r : ℝ) *
             diff a (level (d:=d) q-r) (level (d:=d) q)) : ℝ) •
        (∫ x : X, monomial n (x : EuclideanSpace ℝ (Fin d))
             ∂Measure.dirac (gridPoint q r hr)) = _
    rw [MeasureTheory.integral_dirac]
    have hw : 0 ≤ (multiChoose (level (d:=d) q) r : ℝ) *
             diff a (level (d:=d) q-r) (level (d:=d) q) :=
      bernstein_weight_nonneg ha _ _
    simp only [smul_eq_mul]
    rw [Real.coe_toNNReal _ hw]
    rw [grid_monomial q r n hr]
  · intro r hr
    simp only [hr, dite_true, ite_true]
    change Integrable (fun x : X => monomial n
       (x : EuclideanSpace ℝ (Fin d)))
       ((Real.toNNReal ((multiChoose (level (d:=d) q) r : ℝ) *
          diff a (level (d:=d) q-r) (level (d:=d) q))) •
          (atom q r hr : Measure X))
    -- it is integrable for every finite measure
    rw [← FiniteMeasure.toMeasure_smul]
    exact hf _

lemma bern_mass_real {d : ℕ} {a : (Fin d → ℕ) → ℝ}
    (ha : ∀ k n : Fin d → ℕ, k ≤ n → 0 ≤ diff a k n)
    (q : ℕ) : ((bernMeasure a q).mass : ℝ) = a 0 := by
  classical
  have h := bern_integral ha q (0 : Fin d → ℕ)
  have rh :
      (∑ r ∈ Finset.Iic (level (d:=d) q),
       ((multiChoose (level (d:=d) q) r : ℝ) *
          diff a (level (d:=d) q-r) (level (d:=d) q)) *
            (∏ i : Fin d, ((r i : ℝ)/q) ^ ((0 : Fin d → ℕ) i))) = a 0 := by
        simpa using (bernstein_mass a (level (d:=d) q))
  rw [rh] at h
  -- the left hand side is just the integral of the constant one
  have h' : (∫ _ : {x : EuclideanSpace ℝ (Fin d) // x ∈ cube d}, (1:ℝ)
       ∂(bernMeasure a q : Measure _)) = a 0 := by
        simpa [monomial] using h
  rw [MeasureTheory.integral_const, MeasureTheory.measureReal_def] at h'
  -- translate from `measure univ` to the finite-measure mass
  rw [← FiniteMeasure.ennreal_mass, ENNReal.coe_toReal] at h'
  simpa [smul_eq_mul] using h'
lemma bern_mass_nnreal {d : ℕ} {a : (Fin d → ℕ) → ℝ}
    (ha : ∀ k n : Fin d → ℕ, k ≤ n → 0 ≤ diff a k n)
    (ha0 : 0 ≤ a 0) (q : ℕ) :
    (bernMeasure a q).mass = Real.toNNReal (a 0) := by
  apply_fun ((↑) : NNReal → ℝ)
  · simpa [Real.coe_toNNReal _ ha0] using bern_mass_real ha q
  · exact NNReal.coe_injective
def deg {d : ℕ} (m : Fin d → ℕ) : ℕ := ∑ i, m i

lemma bern_scaled_desc {d : ℕ} (a : (Fin d → ℕ) → ℝ)
    (q : ℕ) (m : Fin d → ℕ) (hm : ∀ i, m i ≤ q) :
 (∑ r ∈ Finset.Iic (level (d:=d) q),
       ((multiChoose (level (d:=d) q) r : ℝ) *
          diff a (level (d:=d) q-r) (level (d:=d) q)) *
          (multiDesc r m / (q:ℝ)^(deg m)))
       = (multiDesc (level (d:=d) q) m / (q:ℝ)^(deg m)) * a m := by
  classical
  have h := bernstein_desc_moment a (level (d:=d) q) m hm
  calc
    (∑ r ∈ Finset.Iic (level (d:=d) q),
       ((multiChoose (level (d:=d) q) r : ℝ) *
          diff a (level (d:=d) q-r) (level (d:=d) q)) *
          (multiDesc r m / (q:ℝ)^(deg m)))
     = (∑ r ∈ Finset.Iic (level (d:=d) q),
       ((multiChoose (level (d:=d) q) r : ℝ) *
          diff a (level (d:=d) q-r) (level (d:=d) q)) *
          multiDesc r m) / (q:ℝ)^(deg m) := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro r hr
            ring
    _ = (multiDesc (level (d:=d) q) m * a m) / (q:ℝ)^(deg m) := by rw [h]
    _ = (multiDesc (level (d:=d) q) m / (q:ℝ)^(deg m)) * a m := by ring
open Filter Topology in
/-- Compactness package for the converse: it is enough to manufacture finite
measures on the (compact) cube whose polynomial moments converge.  Notice that
they need not converge as measures; a cluster filter is enough. -/
lemma of_subtype_moment_limit {d : ℕ} (a : (Fin d → ℕ) → ℝ)
    (μs : ℕ → FiniteMeasure {x : EuclideanSpace ℝ (Fin d) // x ∈ cube d})
    (C : ℝ≥0)
    (hC : ∀ q, (μs q).mass ≤ C)
    (hlim : ∀ n,
      Tendsto (fun q => ∫ x : {x : EuclideanSpace ℝ (Fin d) // x ∈ cube d},
          monomial n (x : EuclideanSpace ℝ (Fin d)) ∂(μs q : Measure _)) atTop
        (𝓝 (a n))) :
    IsPositiveMomentConfiguration a := by
  classical
  let X : Type := {x : EuclideanSpace ℝ (Fin d) // x ∈ cube d}
  letI : CompactSpace X := isCompact_iff_compactSpace.mp (cube_compact d)
  -- regard our sequence in this abbreviated compact type
  let u : ℕ → FiniteMeasure X := μs
  let S : Set (FiniteMeasure X) := {ν | ν.mass ≤ C}
  have hS : IsCompact S := isCompact_setOf_finiteMeasure_le_of_compactSpace X C
  let l : Filter (FiniteMeasure X) := Filter.map u atTop
  haveI : l.NeBot := (Filter.NeBot.map (by infer_instance : (atTop : Filter ℕ).NeBot) u)
  have hls : l ≤ Filter.principal S := by
    rw [Filter.le_principal_iff]
    change ∀ᶠ q in atTop, u q ∈ S
    exact Filter.Eventually.of_forall (fun q => hC q)
  obtain ⟨ν, hνS, hνcl⟩ := hS.exists_clusterPt hls
  let g : Filter (FiniteMeasure X) := 𝓝 ν ⊓ l
  haveI : g.NeBot := hνcl
  -- On a compact space the monomials are bounded continuous functions, so
  -- integration of them is continuous for the weak topology.
  let p (n : Fin d → ℕ) : BoundedContinuousFunction X ℝ :=
    BoundedContinuousFunction.mkOfCompact
      ⟨(fun x : X => monomial n (x : EuclideanSpace ℝ (Fin d))),
        (continuous_monomial n).comp continuous_subtype_val⟩
  let L (n : Fin d → ℕ) (ν' : FiniteMeasure X) : ℝ :=
    ∫ x : X, p n x ∂(ν' : Measure X)
  have L_eq (n : Fin d → ℕ) (ν' : FiniteMeasure X) : L n ν' =
      ∫ x : {x : EuclideanSpace ℝ (Fin d) // x ∈ cube d},
        monomial n (x : EuclideanSpace ℝ (Fin d)) ∂(ν' : Measure X) := by
    rfl
  have hLa : ∀ n, L n ν = a n := by
    intro n
    have hal : Tendsto (L n) l (𝓝 (a n)) := by
      change Filter.map (L n) (Filter.map u atTop) ≤ 𝓝 (a n)
      -- this is just the assumed scalar convergence
      simpa [Filter.Tendsto, Filter.map_map, Function.comp_def, u, L, p, X] using hlim n
    have hag : Tendsto (L n) g (𝓝 (a n)) :=
      hal.mono_left inf_le_right
    have hcont : Continuous (L n) := by
      exact MeasureTheory.FiniteMeasure.continuous_integral_boundedContinuousFunction (p n)
    have hν : Tendsto (L n) g (𝓝 (L n ν)) :=
      (hcont.tendsto ν).mono_left inf_le_left
    exact tendsto_nhds_unique hν hag
  -- push the cluster measure forward to the ambient Euclidean space
  let v : FiniteMeasure (EuclideanSpace ℝ (Fin d)) :=
    ν.map (fun x : X => (x : EuclideanSpace ℝ (Fin d)))
  refine ⟨(v : Measure (EuclideanSpace ℝ (Fin d))), inferInstance, ?_⟩
  intro n
  have hv : momentOf (v : Measure (EuclideanSpace ℝ (Fin d))) n = L n ν := by
    -- all of `v` is on the cube
    unfold momentOf
    change (∫ y in cube d, monomial n y ∂Measure.map (fun x : X =>
      (x : EuclideanSpace ℝ (Fin d))) (ν : Measure X)) = _
    rw [MeasureTheory.setIntegral_map]
    · have hpre : (fun x : X => (x : EuclideanSpace ℝ (Fin d))) ⁻¹' cube d = (Set.univ : Set X) := by
        ext x
        simp [x.property]
      rw [hpre]
      simp
      rfl
    · exact (cube_compact d).measurableSet
    · exact (continuous_monomial n).aestronglyMeasurable
    · exact continuous_subtype_val.aemeasurable
  exact (hLa n).symm.trans hv.symm -- fix orientation


/- Elementary estimates used in the last, scalar, part of the Bernstein argument. -/
lemma desc_div_succ (t m q : ℕ) :
    (t.descFactorial (m+1) : ℝ) / (q:ℝ)^(m+1) =
      ((t.descFactorial m : ℝ) / (q:ℝ)^m) *
        ((t:ℝ)/(q:ℝ) - (m:ℝ)/(q:ℝ)) := by
  rw [cast_desc_div, cast_desc_div]
  rw [Finset.prod_range_succ]

lemma desc_div_bounds (t m q : ℕ) (hq : 1 ≤ q) (ht : t ≤ q) :
    0 ≤ (t.descFactorial m : ℝ) / (q:ℝ)^m ∧
    (t.descFactorial m : ℝ) / (q:ℝ)^m ≤ 1 := by
  have hq' : 0 < (q:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hpow : 0 < (q:ℝ)^m := pow_pos hq' _
  constructor
  · exact div_nonneg (by exact_mod_cast (Nat.zero_le (t.descFactorial m))) hpow.le
  · apply (div_le_iff₀ hpow).2
    have hn : t.descFactorial m ≤ q^m :=
      le_trans (Nat.descFactorial_le_pow t m) (Nat.pow_le_pow_left ht m)
    have hr : (t.descFactorial m : ℝ) ≤ (q:ℝ)^m := by
      exact_mod_cast hn
    simpa using hr

lemma ratio_bounds (t q : ℕ) (hq : 1 ≤ q) (ht : t ≤ q) :
    0 ≤ (t:ℝ)/(q:ℝ) ∧ (t:ℝ)/(q:ℝ) ≤ 1 := by
  have hq' : 0 < (q:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  constructor
  · exact div_nonneg (by exact_mod_cast (Nat.zero_le t)) hq'.le
  · apply (div_le_iff₀ hq').2
    norm_num
    exact_mod_cast ht

lemma pow_desc_approx (t m q : ℕ) (hq : 1 ≤ q) (ht : t ≤ q) :
    |((t:ℝ)/(q:ℝ))^m - (t.descFactorial m : ℝ) / (q:ℝ)^m| ≤
       (m:ℝ)^2 / (q:ℝ) := by
  have hq' : 0 < (q:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hz := ratio_bounds t q hq ht
  induction m with
  | zero =>
      norm_num
  | succ m ih =>
      have hD := desc_div_bounds t m q hq ht
      have hzabs : |(t:ℝ)/(q:ℝ)| ≤ 1 := by rw [abs_of_nonneg hz.1]; exact hz.2
      have hDabs : |(t.descFactorial m : ℝ) / (q:ℝ)^m| ≤ 1 := by
        rw [abs_of_nonneg hD.1]
        exact hD.2
      have hmq : 0 ≤ (m:ℝ)/(q:ℝ) := div_nonneg (by positivity) hq'.le
      rw [desc_div_succ]
      rw [pow_succ]
      have hident :
          ((t:ℝ)/(q:ℝ))^m * ((t:ℝ)/(q:ℝ)) -
            ((t.descFactorial m : ℝ)/(q:ℝ)^m) *
               ((t:ℝ)/(q:ℝ) - (m:ℝ)/(q:ℝ)) =
          ((t:ℝ)/(q:ℝ)) *
             (((t:ℝ)/(q:ℝ))^m - (t.descFactorial m : ℝ)/(q:ℝ)^m) +
             ((t.descFactorial m : ℝ)/(q:ℝ)^m) * ((m:ℝ)/(q:ℝ)) := by
            ring
      rw [hident]
      calc
        |((t:ℝ)/(q:ℝ)) *
             (((t:ℝ)/(q:ℝ))^m - (t.descFactorial m : ℝ)/(q:ℝ)^m) +
             ((t.descFactorial m : ℝ)/(q:ℝ)^m) * ((m:ℝ)/(q:ℝ))|
          ≤ |((t:ℝ)/(q:ℝ)) *
             (((t:ℝ)/(q:ℝ))^m - (t.descFactorial m : ℝ)/(q:ℝ)^m)| +
             |((t.descFactorial m : ℝ)/(q:ℝ)^m) * ((m:ℝ)/(q:ℝ))| :=
               abs_add_le _ _
        _ = |(t:ℝ)/(q:ℝ)| *
              |((t:ℝ)/(q:ℝ))^m - (t.descFactorial m : ℝ)/(q:ℝ)^m| +
              |(t.descFactorial m : ℝ)/(q:ℝ)^m| * |(m:ℝ)/(q:ℝ)| := by
                repeat' rw [abs_mul]
        _ ≤ 1 * ((m:ℝ)^2/(q:ℝ)) + 1 * ((m:ℝ)/(q:ℝ)) := by
                have hab := ih
                have hmabs : |(m:ℝ)/(q:ℝ)| = (m:ℝ)/(q:ℝ) := abs_of_nonneg hmq
                rw [hmabs]
                gcongr
        _ ≤ ((m+1:ℕ):ℝ)^2 / (q:ℝ) := by
                have : (0:ℝ) < (q:ℝ) := hq'
                -- just clear the positive denominator
                apply (le_div_iff₀ this).2
                field_simp
                ring_nf
                push_cast
                nlinarith [show (0:ℝ) ≤ (m:ℝ) by exact_mod_cast (Nat.zero_le m)]


lemma abs_prod_sub_prod_le_sum_of_unit
    {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1)
    (hg : ∀ i ∈ s, 0 ≤ g i ∧ g i ≤ 1) :
    |(∏ i ∈ s, f i) - (∏ i ∈ s, g i)| ≤
       ∑ i ∈ s, |f i - g i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert b s hb ih =>
      have hfb := hf b (by simp)
      have hgb := hg b (by simp)
      have hfs : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1 :=
        fun i hi => hf i (by simp [hi])
      have hgs : ∀ i ∈ s, 0 ≤ g i ∧ g i ≤ 1 :=
        fun i hi => hg i (by simp [hi])
      have hi := ih hfs hgs
      have hQ0 : 0 ≤ ∏ i ∈ s, g i :=
        Finset.prod_nonneg (fun i hi => (hgs i hi).1)
      have hQ1 : (∏ i ∈ s, g i) ≤ (1:ℝ) :=
        Finset.prod_le_one (fun i hi => (hgs i hi).1)
          (fun i hi => (hgs i hi).2)
      have hident :
          f b * (∏ i ∈ s, f i) - g b * (∏ i ∈ s, g i) =
            f b * ((∏ i ∈ s, f i) - (∏ i ∈ s, g i)) +
              (f b - g b) * (∏ i ∈ s, g i) := by ring
      simp only [Finset.prod_insert, Finset.sum_insert, hb, not_false_eq_true]
      rw [hident]
      calc
        |f b * ((∏ i ∈ s, f i) - (∏ i ∈ s, g i)) +
              (f b - g b) * (∏ i ∈ s, g i)|
          ≤ |f b * ((∏ i ∈ s, f i) - (∏ i ∈ s, g i))| +
              |(f b - g b) * (∏ i ∈ s, g i)| := abs_add_le _ _
        _ = f b * |(∏ i ∈ s, f i) - (∏ i ∈ s, g i)| +
               |f b - g b| * (∏ i ∈ s, g i) := by
                rw [abs_mul, abs_mul, abs_of_nonneg hfb.1, abs_of_nonneg hQ0]
        _ ≤ 1 * (∑ i ∈ s, |f i - g i|) + |f b - g b| * 1 := by
                gcongr <;> try { exact hfb.2 }
        _ = |f b - g b| + ∑ i ∈ s, |f i - g i| := by ring


lemma multiDesc_div_eq {d : ℕ} (r m : Fin d → ℕ) (q : ℕ) :
    multiDesc r m / (q:ℝ)^(deg m) =
      ∏ i, ((r i).descFactorial (m i) : ℝ) / (q:ℝ)^(m i) := by
  classical
  unfold multiDesc deg
  rw [Finset.prod_div_distrib]
  rw [Finset.prod_pow_eq_pow_sum]

lemma multi_pow_desc_approx {d : ℕ} (r n : Fin d → ℕ) (q : ℕ)
    (hq : 1 ≤ q) (hr : r ≤ level (d:=d) q) :
    |(∏ i, ((r i:ℝ)/(q:ℝ))^(n i)) -
        multiDesc r n / (q:ℝ)^(deg n)| ≤
      (∑ i, ((n i:ℝ)^2)) / (q:ℝ) := by
  classical
  rw [multiDesc_div_eq]
  have hf : ∀ i ∈ (Finset.univ : Finset (Fin d)),
        0 ≤ ((r i:ℝ)/(q:ℝ))^(n i) ∧
          ((r i:ℝ)/(q:ℝ))^(n i) ≤ 1 := by
    intro i hi
    have hz := ratio_bounds (r i) q hq (hr i)
    exact ⟨pow_nonneg hz.1 _, pow_le_one₀ hz.1 hz.2⟩
  have hg : ∀ i ∈ (Finset.univ : Finset (Fin d)),
        0 ≤ ((r i).descFactorial (n i) : ℝ)/(q:ℝ)^(n i) ∧
          ((r i).descFactorial (n i) : ℝ)/(q:ℝ)^(n i) ≤ 1 := by
    intro i hi
    exact desc_div_bounds (r i) (n i) q hq (hr i)
  calc
    |(∏ i, ((r i:ℝ)/(q:ℝ))^(n i)) -
       (∏ i, ((r i).descFactorial (n i) : ℝ)/(q:ℝ)^(n i))|
      ≤ ∑ i, |((r i:ℝ)/(q:ℝ))^(n i) -
            ((r i).descFactorial (n i) : ℝ)/(q:ℝ)^(n i)| :=
        abs_prod_sub_prod_le_sum_of_unit _ _ _ hf hg
    _ ≤ ∑ i, ((n i:ℝ)^2)/(q:ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          exact pow_desc_approx (r i) (n i) q hq (hr i)
    _ = (∑ i, (n i:ℝ)^2)/(q:ℝ) := by
          rw [Finset.sum_div]


open Filter Topology
lemma tendsto_level_desc {d : ℕ} (n : Fin d → ℕ) :
    Tendsto (fun q : ℕ => multiDesc (level (d:=d) q) n / (q:ℝ)^(deg n))
      atTop (𝓝 1) := by
  classical
  let S : ℝ := ∑ i : Fin d, (n i : ℝ)^2
  have hupper : Tendsto (fun q : ℕ => S / (q:ℝ)) atTop (𝓝 0) := by
    have h := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h' := (tendsto_const_nhds.mul h :
       Tendsto (fun q : ℕ => S * (1 / (q:ℝ))) atTop (𝓝 (S * 0)))
    simpa [div_eq_mul_inv] using h'
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _q : ℕ => (0:ℝ)) atTop (𝓝 0))
      hupper
  · exact Filter.Eventually.of_forall (fun q =>
      (by exact norm_nonneg _))
  · filter_upwards [Filter.eventually_atTop.2 ⟨1, fun b hb => hb⟩] with q hq
    have hq' : 0 < (q:ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
    have hp := multi_pow_desc_approx (level (d:=d) q) n q hq (by
      intro i; exact le_rfl)
    have hprod :
        (∏ i : Fin d, (((level (d:=d) q) i : ℝ)/(q:ℝ))^(n i)) = (1:ℝ) := by
          have hne : (q:ℝ) ≠ 0 := ne_of_gt hq'
          simp [level, hne]
    rw [hprod] at hp
    simpa [Real.norm_eq_abs, abs_sub_comm] using hp


lemma abs_weighted_sum_sub {ι : Type*} (s : Finset ι)
    (w P Q : ι → ℝ) (E : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hPQ : ∀ i ∈ s, |P i - Q i| ≤ E) :
    |(∑ i ∈ s, w i * P i) - (∑ i ∈ s, w i * Q i)| ≤
       (∑ i ∈ s, w i) * E := by
  classical
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ i ∈ s, (w i * P i - w i * Q i)|
      ≤ ∑ i ∈ s, |w i * P i - w i * Q i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, w i * E := by
        apply Finset.sum_le_sum
        intro i hi
        have heq : w i * P i - w i * Q i = w i * (P i - Q i) := by ring
        rw [heq, abs_mul, abs_of_nonneg (hw i hi)]
        exact mul_le_mul_of_nonneg_left (hPQ i hi) (hw i hi)
    _ = (∑ i ∈ s, w i) * E := by rw [Finset.sum_mul]

lemma bern_power_error {d : ℕ} (a : (Fin d → ℕ) → ℝ)
    (ha : ∀ k n : Fin d → ℕ, k ≤ n → 0 ≤ diff a k n)
    (q : ℕ) (n : Fin d → ℕ) (hq : 1 ≤ q) :
    |(∑ r ∈ Finset.Iic (level (d:=d) q),
        ((multiChoose (level (d:=d) q) r : ℝ) *
          diff a (level (d:=d) q-r) (level (d:=d) q)) *
            (∏ i, ((r i : ℝ)/(q:ℝ))^(n i))) -
      (∑ r ∈ Finset.Iic (level (d:=d) q),
        ((multiChoose (level (d:=d) q) r : ℝ) *
          diff a (level (d:=d) q-r) (level (d:=d) q)) *
            (multiDesc r n / (q:ℝ)^(deg n)))| ≤
       (a 0) * ((∑ i, (n i : ℝ)^2)/(q:ℝ)) := by
  classical
  let s : Finset (Fin d → ℕ) := Finset.Iic (level (d:=d) q)
  let w : (Fin d → ℕ) → ℝ := fun r =>
     (multiChoose (level (d:=d) q) r : ℝ) *
          diff a (level (d:=d) q-r) (level (d:=d) q)
  let P : (Fin d → ℕ) → ℝ := fun r => ∏ i, ((r i : ℝ)/(q:ℝ))^(n i)
  let Q : (Fin d → ℕ) → ℝ := fun r => multiDesc r n / (q:ℝ)^(deg n)
  let E : ℝ := (∑ i, (n i : ℝ)^2)/(q:ℝ)
  have hw : ∀ r ∈ s, 0 ≤ w r := by
    intro r hr
    exact bernstein_weight_nonneg ha _ _
  have hpq : ∀ r ∈ s, |P r - Q r| ≤ E := by
    intro r hr
    exact multi_pow_desc_approx r n q hq (Finset.mem_Iic.mp hr)
  have hh := abs_weighted_sum_sub s w P Q E hw hpq
  change |(∑ r ∈ s, w r * P r) -
      (∑ r ∈ s, w r * Q r)| ≤ _
  calc
    |(∑ r ∈ s, w r * P r) - (∑ r ∈ s, w r * Q r)|
       ≤ (∑ r ∈ s, w r) * E := hh
    _ = (a 0) * E := by
          dsimp [s, w]
          rw [bernstein_mass a (level (d:=d) q)]
    _ = (a 0) * ((∑ i, (n i : ℝ)^2)/(q:ℝ)) := rfl


open Filter Topology
lemma bern_power_tendsto {d : ℕ} (a : (Fin d → ℕ) → ℝ)
    (ha : ∀ k n : Fin d → ℕ, k ≤ n → 0 ≤ diff a k n)
    (n : Fin d → ℕ) :
    Tendsto (fun q : ℕ =>
       ∑ r ∈ Finset.Iic (level (d:=d) q),
         ((multiChoose (level (d:=d) q) r : ℝ) *
           diff a (level (d:=d) q-r) (level (d:=d) q)) *
             (∏ i, ((r i : ℝ)/(q:ℝ))^(n i))) atTop (𝓝 (a n)) := by
  classical
  let F : ℕ → ℝ := fun q =>
       ∑ r ∈ Finset.Iic (level (d:=d) q),
         ((multiChoose (level (d:=d) q) r : ℝ) *
           diff a (level (d:=d) q-r) (level (d:=d) q)) *
             (∏ i, ((r i : ℝ)/(q:ℝ))^(n i))
  let G : ℕ → ℝ := fun q =>
       ∑ r ∈ Finset.Iic (level (d:=d) q),
         ((multiChoose (level (d:=d) q) r : ℝ) *
           diff a (level (d:=d) q-r) (level (d:=d) q)) *
             (multiDesc r n / (q:ℝ)^(deg n))
  let S : ℝ := ∑ i, (n i : ℝ)^2
  have hup : Tendsto (fun q : ℕ => (a 0) * (S / (q:ℝ))) atTop (𝓝 0) := by
    have h := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h' := (tendsto_const_nhds.mul h :
      Tendsto (fun q : ℕ => ((a 0) * S) * (1 / (q:ℝ)))
        atTop (𝓝 (((a 0) * S) * 0)))
    simpa [div_eq_mul_inv, mul_assoc] using h'
  have habs : Tendsto (fun q : ℕ => |F q - G q|) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
       (tendsto_const_nhds : Tendsto (fun _q : ℕ => (0:ℝ)) atTop (𝓝 0)) hup
    · exact Filter.Eventually.of_forall (fun q => abs_nonneg _)
    · filter_upwards [Filter.eventually_atTop.2 ⟨1, fun b hb => hb⟩] with q hq
      simpa [F, G, S] using (bern_power_error a ha q n hq)
  have hz : Tendsto (fun q : ℕ => F q - G q) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa [Real.norm_eq_abs] using habs
  have hm_ev : ∀ᶠ q : ℕ in atTop, ∀ i : Fin d, n i ≤ q := by
    refine Filter.eventually_atTop.2 ⟨Finset.univ.sup n, ?_⟩
    intro q hq i
    exact (Finset.le_sup (s:=Finset.univ) (f:=n) (Finset.mem_univ i)).trans hq
  have hGeq : G =ᶠ[atTop]
      (fun q : ℕ => (multiDesc (level (d:=d) q) n / (q:ℝ)^(deg n)) * a n) := by
    filter_upwards [hm_ev] with q hq
    simpa [G] using (bern_scaled_desc a q n hq)
  have hprod : Tendsto
       (fun q : ℕ => (multiDesc (level (d:=d) q) n / (q:ℝ)^(deg n)) * a n)
       atTop (𝓝 (a n)) := by
    simpa using (Filter.Tendsto.mul_const (a n) (tendsto_level_desc (d:=d) n))
  have hG : Tendsto G atTop (𝓝 (a n)) :=
    Filter.Tendsto.congr' hGeq.symm hprod
  have hsum := hz.add hG
  have hF : Tendsto F atTop (𝓝 (a n)) := by
    simpa using hsum
  exact hF

end LeanEval.Analysis

/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem hausdorff_positivity {d : ℕ} (a : (Fin d → ℕ) → ℝ) :
    IsPositiveMomentConfiguration a ↔ ∀ k n : Fin d → ℕ, k ≤ n → 0 ≤ diff a k n :=
/-ResultProofBegin-/by
  constructor
  · intro h
    rcases h with ⟨μ, hμ, ha⟩
    letI := hμ
    have hae : a = (fun r => momentOf μ r) := funext ha
    subst a
    intro k n hkn
    exact LeanEval.Analysis.moment_diff_nonneg μ k n hkn
  · intro hmono
    classical
    have ha_nonneg (n : Fin d → ℕ) : 0 ≤ a n := by
      have hz : (0 : Fin d → ℕ) ≤ n := by
        intro i
        exact Nat.zero_le _
      simpa [LeanEval.Analysis.diff_zero] using hmono (0 : Fin d → ℕ) n hz
    refine LeanEval.Analysis.of_subtype_moment_limit a
      (LeanEval.Analysis.bernMeasure a)
      (Real.toNNReal (a 0)) ?_ ?_
    · intro q
      rw [LeanEval.Analysis.bern_mass_nnreal hmono (ha_nonneg 0) q]
    · intro n
      have he :
          (fun q => ∫ x : {x : EuclideanSpace ℝ (Fin d) // x ∈ cube d},
                monomial n (x : EuclideanSpace ℝ (Fin d))
                   ∂(LeanEval.Analysis.bernMeasure a q : Measure _)) =
            (fun q => ∑ r ∈ Finset.Iic (LeanEval.Analysis.level (d:=d) q),
               ((multiChoose (LeanEval.Analysis.level (d:=d) q) r : ℝ) *
                  diff a (LeanEval.Analysis.level (d:=d) q-r)
                            (LeanEval.Analysis.level (d:=d) q)) *
                    (∏ i, ((r i : ℝ)/q)^(n i))) := by
            funext q
            exact LeanEval.Analysis.bern_integral hmono q n
      rw [he]
      -- At this point only the classical scalar Bernstein/factorial limit is
      -- left. `bernstein_desc_moment` and `bern_scaled_desc` above give its
      -- exact factorial moments.
      exact LeanEval.Analysis.bern_power_tendsto a hmono n
/-ResultProofEnd-/
/-ResultEnd-/

end Submission
