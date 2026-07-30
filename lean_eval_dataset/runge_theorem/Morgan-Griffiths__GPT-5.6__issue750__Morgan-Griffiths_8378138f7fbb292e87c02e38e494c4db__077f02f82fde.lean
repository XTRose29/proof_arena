import Mathlib

-- BEGIN INLINED FILE: Mathlib/Support/runge_theorem_ac7707d823/Rational.lean

open scoped Polynomial BigOperators
open Polynomial Finset

noncomputable section

namespace RungeSupport

/-- The common denominator for a finite collection of simple poles. -/
def poleDenom {n : ℕ} (b : Fin n → ℂ) : ℂ[X] :=
  ∏ i : Fin n, (X - C (b i))

/-- The numerator obtained by putting a finite sum of simple poles over a common
 denominator. The convention `∑ a_i/(z-b_i)` is useful for Cauchy sums. -/
def poleNumer {n : ℕ} (a b : Fin n → ℂ) : ℂ[X] :=
  ∑ i : Fin n, C (a i) * ∏ j ∈ (Finset.univ.erase i), (X - C (b j))

@[simp] lemma eval_poleDenom {n : ℕ} (b : Fin n → ℂ) (z : ℂ) :
    (poleDenom b).eval z = ∏ i : Fin n, (z - b i) := by
  classical
  simp [poleDenom, Polynomial.eval_prod]

@[simp] lemma eval_poleNumer {n : ℕ} (a b : Fin n → ℂ) (z : ℂ) :
    (poleNumer a b).eval z =
      ∑ i : Fin n, a i * ∏ j ∈ (Finset.univ.erase i), (z - b j) := by
  classical
  simp [poleNumer, Polynomial.eval_finset_sum, Polynomial.eval_prod]

/-- Putting a finite Cauchy sum over its common denominator. There is no
assumption that the poles are distinct. Repetitions just give a non-reduced
fraction, which is quite convenient. -/
lemma poleNumer_div_poleDenom {n : ℕ} (a b : Fin n → ℂ) {z : ℂ}
    (hz : ∀ i, z - b i ≠ 0) :
    (poleNumer a b).eval z / (poleDenom b).eval z =
      ∑ i : Fin n, a i / (z - b i) := by
  classical
  simp only [eval_poleNumer, eval_poleDenom]
  -- It is useful to cancel a single factor of the denominator in each
  -- summand, rather than clearing all denominators at once: this also deals
  -- uniformly with repeated poles and with the empty product.
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hiu : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
  -- split the denominator product into the factor at `i` and its complement
  have hprod : (∏ j : Fin n, (z - b j)) =
      (z - b i) * (∏ j ∈ (Finset.univ.erase i), (z - b j)) := by
    classical
    -- `prod_erase_mul` is phrased with the erased product first.
    have := (Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
      (fun j : Fin n => (z - b j)) hiu)
    -- lemma: f i * ∏ (erase) = ∏ univ
    -- reorder to our convention
    simpa [mul_comm, mul_left_comm, mul_assoc] using this.symm
  rw [hprod]
  -- a_i * B / ((z-b_i)*B) = a_i/(z-b_i)
  have hB : (∏ j ∈ (Finset.univ.erase i), (z - b j)) ≠ 0 := by
    classical
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact hz _
  simpa [mul_assoc] using (mul_div_mul_right (a i) (z - b i) hB)

/-- A finite simple-pole approximation is already a polynomial quotient with
no zeros of the denominator on the compact set. This purely algebraic
packaging lemma keeps all of the analytic work in the (usually easier to
manipulate) Cauchy-sum form.

We use denominators `z - b i`. A term with the opposite convention is of
course obtained by negating its coefficient. Repeated poles and zero
coefficients are allowed. -/
lemma of_fin_cauchy_approx
    (K : Set ℂ) (f : ℂ → ℂ) (ε : ℝ) {n : ℕ}
    (a b : Fin n → ℂ)
    (hb : ∀ i z, z ∈ K → z ≠ b i)
    (happrox : ∀ z ∈ K,
      ‖f z - (∑ i : Fin n, a i / (z - b i))‖ < ε) :
    ∃ p q : ℂ[X], (∀ z ∈ K, q.eval z ≠ 0) ∧
      (∀ z ∈ K, ‖f z - p.eval z / q.eval z‖ < ε) := by
  classical
  refine ⟨poleNumer a b, poleDenom b, ?_, ?_⟩
  · intro z hz
    rw [eval_poleDenom]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact sub_ne_zero.mpr (hb i z hz)
  · intro z hzK
    have hz : ∀ i : Fin n, z - b i ≠ 0 := fun i => sub_ne_zero.mpr (hb i z hzK)
    rw [poleNumer_div_poleDenom a b hz]
    exact happrox z hzK


/-- Index-set variant of `of_fin_cauchy_approx`. Keeping this small wrapper is
pleasant when several contours have first been approximated independently:
their disjoint union is naturally a sigma type. -/
lemma of_fintype_cauchy_approx
    (K : Set ℂ) (f : ℂ → ℂ) (ε : ℝ)
    {ι : Type*} [Fintype ι]
    (a b : ι → ℂ)
    (hb : ∀ i z, z ∈ K → z ≠ b i)
    (happrox : ∀ z ∈ K,
      ‖f z - (∑ i : ι, a i / (z - b i))‖ < ε) :
    ∃ p q : ℂ[X], (∀ z ∈ K, q.eval z ≠ 0) ∧
      (∀ z ∈ K, ‖f z - p.eval z / q.eval z‖ < ε) := by
  classical
  let e := Fintype.equivFin ι
  let aa : Fin (Fintype.card ι) → ℂ := fun k => a (e.symm k)
  let bb : Fin (Fintype.card ι) → ℂ := fun k => b (e.symm k)
  apply of_fin_cauchy_approx K f ε aa bb
  · intro i z hz
    exact hb (e.symm i) z hz
  · intro z hz
    have heq : (∑ k : Fin (Fintype.card ι), aa k / (z - bb k)) =
        ∑ i : ι, a i / (z - b i) := by
      -- reindex by the chosen equivalence
      symm
      exact Fintype.sum_equiv e
        (fun i : ι => a i / (z - b i))
        (fun k : Fin (Fintype.card ι) => aa k / (z - bb k))
        (by intro i; simp [aa, bb, e])
    simpa [heq] using happrox z hz

end RungeSupport

end

-- END INLINED FILE: Mathlib/Support/runge_theorem_ac7707d823/Rational.lean

-- BEGIN INLINED FILE: Mathlib/Support/runge_theorem_ac7707d823/Rect.lean

open scoped BigOperators Interval Real ComplexConjugate
open Set MeasureTheory intervalIntegral

noncomputable section

namespace RungeSupport

/-- Boundary integral of the axis parallel rectangle `[a,b]×[c,d]`. This is
exactly the convention used in `Complex.integral_boundary_rect...`. Keeping
coordinates real is much less cumbersome when many neighbouring squares
cancel. -/
def rectInt (F : ℂ → ℂ) (a b c d : ℝ) : ℂ :=
    (∫ x : ℝ in a..b, F (x + c * Complex.I)) -
    (∫ x : ℝ in a..b, F (x + d * Complex.I)) +
    Complex.I * (∫ y : ℝ in c..d, F (b + y * Complex.I)) -
    Complex.I * (∫ y : ℝ in c..d, F (a + y * Complex.I))

lemma rectInt_eq_zero_of_differentiableOn
    (F : ℂ → ℂ) (a b c d : ℝ)
    (hF : DifferentiableOn ℂ F
      (Set.uIcc a b ×ℂ Set.uIcc c d)) :
    rectInt F a b c d = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    F (⟨a,c⟩ : ℂ) (⟨b,d⟩ : ℂ) (by simpa using hF)
  simpa [rectInt, mul_comm] using h

/-- Horizontal splitting of a rectangle. Only its two vertical sides are
split integrals; the new horizontal side cancels identically. -/
lemma rectInt_horizontal (F : ℂ → ℂ) (a b c e d : ℝ)
    (ha : IntervalIntegrable (fun y : ℝ => F (a + y * Complex.I)) volume c e)
    (ha' : IntervalIntegrable (fun y : ℝ => F (a + y * Complex.I)) volume e d)
    (hb : IntervalIntegrable (fun y : ℝ => F (b + y * Complex.I)) volume c e)
    (hb' : IntervalIntegrable (fun y : ℝ => F (b + y * Complex.I)) volume e d) :
    rectInt F a b c d = rectInt F a b c e + rectInt F a b e d := by
  dsimp [rectInt]
  rw [← intervalIntegral.integral_add_adjacent_intervals ha ha',
      ← intervalIntegral.integral_add_adjacent_intervals hb hb']
  ring

/-- Vertical splitting. Its requirements are just those for the top and
bottom horizontal edges. No integrability of the new side is necessary,
because it cancels literally. -/
lemma rectInt_vertical (F : ℂ → ℂ) (a e b c d : ℝ)
    (hc : IntervalIntegrable (fun x : ℝ => F (x + c * Complex.I)) volume a e)
    (hc' : IntervalIntegrable (fun x : ℝ => F (x + c * Complex.I)) volume e b)
    (hd : IntervalIntegrable (fun x : ℝ => F (x + d * Complex.I)) volume a e)
    (hd' : IntervalIntegrable (fun x : ℝ => F (x + d * Complex.I)) volume e b) :
    rectInt F a b c d = rectInt F a e c d + rectInt F e b c d := by
  dsimp [rectInt]
  rw [← intervalIntegral.integral_add_adjacent_intervals hc hc',
      ← intervalIntegral.integral_add_adjacent_intervals hd hd']
  ring

end RungeSupport

end

-- END INLINED FILE: Mathlib/Support/runge_theorem_ac7707d823/Rect.lean

-- BEGIN INLINED FILE: Mathlib/Support/runge_theorem_ac7707d823/CauchyApprox.lean

open scoped BigOperators Interval Real Topology ComplexConjugate
open Set MeasureTheory Filter Polynomial
open intervalIntegral

noncomputable section

namespace RungeSupport

/-- A uniform Riemann-sum lemma, recorded with the sample points and real
weights exposed. The elementary statement is quite handy when one integrates
Cauchy kernels: the sample points do not depend on the parameter in the
compact set. Notice the closed interval in `hH`; no hypotheses away from the
interval are needed. -/
lemma exists_riemann_sum_uniform
    (K : Set ℂ) (hK : IsCompact K) (A B : ℝ) (hAB : A ≤ B)
    (H : ℝ × ℂ → ℂ)
    (hH : ContinuousOn H (Set.Icc A B ×ˢ K))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∃ t : Fin n → ℝ, ∃ d : Fin n → ℝ,
      (∀ i, t i ∈ Set.Icc A B) ∧
      ∀ z ∈ K,
        ‖(∫ x : ℝ in A..B, H (x,z)) -
            ∑ i : Fin n, (d i : ℂ) * H (t i, z)‖ < ε := by
  classical
  rcases eq_or_lt_of_le hAB with rfl | hlt
  · refine ⟨0, Fin.elim0, Fin.elim0, ?_, ?_⟩
    · intro i; exact Fin.elim0 i
    · intro z hz
      simp [hε]
  ·
    have hL : 0 < B - A := sub_pos.mpr hlt
    let L : ℝ := B - A
    -- reserve a factor of two in the modulus, so that the final estimate is
    -- strict without making any choice of tags.
    let η : ℝ := ε / (2 * L)
    have hη : 0 < η := by
      dsimp [η, L]
      positivity
    have hcomp : IsCompact (Set.Icc A B ×ˢ K) := isCompact_Icc.prod hK
    have hu : UniformContinuousOn H (Set.Icc A B ×ˢ K) :=
      hcomp.uniformContinuousOn_of_continuous hH
    rcases (Metric.uniformContinuousOn_iff.mp hu) η hη with ⟨δ, hδ, hmod⟩
    obtain ⟨m : ℕ, hm⟩ := exists_nat_gt (L / δ)
    let N : ℕ := m + 1
    have hN : 0 < (N:ℝ) := by
      dsimp [N]
      exact_mod_cast (Nat.succ_pos m)
    have hmesh : L / (N:ℝ) < δ := by
      have hgt : L / δ < (N:ℝ) :=
        lt_trans hm (by exact_mod_cast (Nat.lt_succ_self m))
      -- both sides are positive
      apply (div_lt_iff₀ hN).2
      have ht := (div_lt_iff₀ hδ).1 hgt
      simpa [mul_comm] using ht
    let step : ℝ := L / (N:ℝ)
    have hstep : 0 < step := div_pos hL hN
    let x : ℕ → ℝ := fun k => A + (k:ℝ) * step
    have hx0 : x 0 = A := by simp [x]
    have hxN : x N = B := by
      dsimp [x, step, L]
      field_simp
      <;> ring
    have hx_succ (k : ℕ) : x (k+1) - x k = step := by
      dsimp [x]
      push_cast
      ring
    have hxle {k : ℕ} (hk : k ≤ N) : A ≤ x k ∧ x k ≤ B := by
      constructor
      · dsimp [x]
        exact le_add_of_nonneg_right (mul_nonneg (by exact_mod_cast (Nat.zero_le k)) hstep.le)
      · rw [← hxN]
        dsimp [x]
        gcongr
    -- the promised tags are the left endpoints of the equal subintervals
    refine ⟨N,
      (fun i : Fin N => x i.val),
      (fun _ : Fin N => step), ?_, ?_⟩
    · intro i
      exact hxle (Nat.le_of_lt i.isLt)
    intro z hzK
    let F : ℝ → ℂ := fun r => H (r,z)
    have hF : ContinuousOn F (Set.Icc A B) := by
      have hc : Continuous (fun r : ℝ => (r,z)) :=
        continuous_id.prodMk continuous_const
      have hmapp : Set.MapsTo (fun r : ℝ => (r,z)) (Set.Icc A B)
          (Set.Icc A B ×ˢ K) := by
        intro r hr; exact ⟨hr, hzK⟩
      simpa [F, Function.comp_def] using
        hH.comp hc.continuousOn hmapp

    have hInt (u v : ℝ) (huv : Set.uIcc u v ⊆ Set.Icc A B) :
        IntervalIntegrable F volume u v :=
      (hF.mono huv).intervalIntegrable
    have hIntCell (k : ℕ) (hk : k < N) :
        IntervalIntegrable F volume (x k) (x (k+1)) := by
      have hsle : x k ≤ x (k+1) := by
        have hp : 0 < x (k+1) - x k := by rw [hx_succ]; exact hstep
        linarith
      have hc : ContinuousOn F (Set.Icc (x k) (x (k+1))) :=
        hF.mono (by
          intro r hr
          have h₁ := hxle (Nat.le_of_lt hk)
          have h₂ := hxle (by omega : k+1 ≤ N)
          exact ⟨h₁.1.trans hr.1, hr.2.trans h₂.2⟩)
      exact hc.intervalIntegrable_of_Icc hsle

    have hsumInt :
        (∑ k ∈ Finset.range N, ∫ r : ℝ in x k..x (k+1), F r) =
          ∫ r : ℝ in A..B, F r := by
      simpa [hx0, hxN] using
        (intervalIntegral.sum_integral_adjacent_intervals
          (f := F) (a := x) (n := N) hIntCell)
    -- On each interval the oscillation from its left endpoint is at most η.
    have herr (k : ℕ) (hk : k < N) :
        ‖(∫ r : ℝ in x k..x (k+1), F r) -
            (step : ℂ) * F (x k)‖ ≤ η * step := by
      have hconst :
          (∫ _r : ℝ in x k..x (k+1), F (x k)) =
            (step : ℂ) * F (x k) := by
        rw [intervalIntegral.integral_const]
        rw [hx_succ]
        -- for complex-valued integrals scalar multiplication by a real is
        -- multiplication by its real cast
        simp
      rw [← hconst]
      have hdiff :
          (∫ r : ℝ in x k..x (k+1), (F r - F (x k))) =
            (∫ r : ℝ in x k..x (k+1), F r) -
              (∫ _r : ℝ in x k..x (k+1), F (x k)) := by
        apply intervalIntegral.integral_sub
        · exact hIntCell k hk
        · exact continuousOn_const.intervalIntegrable
      rw [← hdiff]
      have hosc : ∀ r ∈ Ι (x k) (x (k+1)), ‖F r - F (x k)‖ ≤ η := by
        intro r hr
        have hkk := hxle (Nat.le_of_lt hk)
        have hk1 := hxle (by omega : k+1 ≤ N)
        have horder : x k ≤ x (k+1) := by
          have : 0 < x (k+1) - x k := by simpa [hx_succ] using hstep
          linarith
        have hir : r ∈ Set.Icc (x k) (x (k+1)) := by
          -- `Ι` is the unordered interval Ioc; it is contained in the Icc
          have hh : r ∈ Set.uIcc (x k) (x (k+1)) := uIoc_subset_uIcc hr
          simpa [uIcc_of_le horder] using hh
        have hrAB : r ∈ Set.Icc A B :=
          ⟨hkk.1.trans hir.1, hir.2.trans hk1.2⟩
        have hxAB : (x k) ∈ Set.Icc A B := hkk
        have hp1 : (r,z) ∈ (Set.Icc A B ×ˢ K) := ⟨hrAB, hzK⟩
        have hp0 : (x k,z) ∈ (Set.Icc A B ×ˢ K) := ⟨hxAB, hzK⟩
        have hdprod : dist (r,z) (x k,z) < δ := by
          -- the product metric is the max metric
          have hrd : dist r (x k) ≤ step := by
            rw [Real.dist_eq]
            have : x k ≤ r ∧ r ≤ x (k+1) := hir
            rw [abs_of_nonneg (sub_nonneg.mpr this.1)]
            linarith [hx_succ k]
          have : dist r (x k) < δ := lt_of_le_of_lt hrd hmesh
          simpa [Prod.dist_eq, this.le, max_lt_iff] using this
        have hltη := hmod (r,z) hp1 (x k,z) hp0 hdprod
        exact le_of_lt (by simpa [F, dist_eq_norm] using hltη)
      have := intervalIntegral.norm_integral_le_of_norm_le_const hosc
      simpa [abs_of_pos hstep, hx_succ] using this
    -- sum the estimates. This last, harmless inequality is often a useful
    -- way of using the uniform-continuity version of Riemann sums.
    have hrewrite :
        (∫ r : ℝ in A..B, F r) -
            ∑ i : Fin N, (step : ℂ) * F (x i.val) =
          ∑ k ∈ Finset.range N,
            ((∫ r : ℝ in x k..x (k+1), F r) - (step : ℂ) * F (x k)) := by
      classical
      rw [← hsumInt]
      -- convert the `Fin` sum to a range sum
      have hfins : (∑ i : Fin N, (step : ℂ) * F (x i.val)) =
          ∑ k ∈ Finset.range N, (step : ℂ) * F (x k) :=
        Fin.sum_univ_eq_sum_range (fun k => (step : ℂ) * F (x k)) N
      rw [hfins, Finset.sum_sub_distrib]
    -- use the triangle inequality for the (finite) sum
    calc
      ‖(∫ x_1 : ℝ in A..B, H (x_1, z)) -
          ∑ i : Fin N, ((step : ℝ) : ℂ) * H (x i.val, z)‖ =
          ‖∑ k ∈ Finset.range N,
            ((∫ r : ℝ in x k..x (k+1), F r) - (step : ℂ) * F (x k))‖ := by
              simpa [F] using congrArg norm hrewrite
      _ ≤ ∑ k ∈ Finset.range N,
            ‖(∫ r : ℝ in x k..x (k+1), F r) - (step : ℂ) * F (x k)‖ := by
              exact norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range N, η * step := by
              apply Finset.sum_le_sum
              intro i hi
              exact herr i (Finset.mem_range.mp hi)
      _ < ε := by
            -- `N * step = L`; our choice of η left a factor of two.
            have hprod : (N:ℝ) * step = L := by
              dsimp [step]
              field_simp
            rw [Finset.sum_const]
            rw [Finset.card_range]
            simp only [nsmul_eq_mul]
            -- help `norm_num`/`field_simp` with the reserved factor
            push_cast
            rw [mul_left_comm (N:ℝ) η step, hprod]
            dsimp [η]
            have hLp : 0 < L := by dsimp [L]; linarith
            have hLn : L ≠ 0 := ne_of_gt hLp
            have heq : L * (ε / (2 * L)) = ε / 2 := by
              field_simp [hLn]

            -- multiplication was commuted when the constant sum was expanded
            rw [mul_comm (ε / (2 * L)) L, heq]
            linarith


/-- Riemann sums for one (real-parametrised) Cauchy integral. The curve need
not be smooth; the coefficient `c` already includes its differential. The
only point that matters for this lemma is that it miss the compact set of
parameters. All the nodes of the approximating Cauchy sum are *on* the
curve, hence off that set as well. -/
lemma exists_fin_kernel_sum
    (K : Set ℂ) (hK : IsCompact K) (A B : ℝ) (hAB : A ≤ B)
    (c γ : ℝ → ℂ)
    (hc : ContinuousOn c (Set.Icc A B))
    (hγ : ContinuousOn γ (Set.Icc A B))
    (hout : ∀ t ∈ Set.Icc A B, γ t ∉ K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∃ a b : Fin n → ℂ,
      (∀ i z, z ∈ K → z ≠ b i) ∧
      ∀ z ∈ K,
        ‖(∫ t : ℝ in A..B, c t / (z - γ t)) -
            ∑ i : Fin n, a i / (z - b i)‖ < ε := by
  classical
  let H : ℝ × ℂ → ℂ := fun q => c q.1 / (q.2 - γ q.1)
  have hcont : ContinuousOn H (Set.Icc A B ×ˢ K) := by
    have hp1 : ContinuousOn (fun q : ℝ × ℂ => c q.1)
        (Set.Icc A B ×ˢ K) :=
      hc.comp continuous_fst.continuousOn (fun q hq => hq.1)
    have hpγ : ContinuousOn (fun q : ℝ × ℂ => γ q.1)
        (Set.Icc A B ×ˢ K) :=
      hγ.comp continuous_fst.continuousOn (fun q hq => hq.1)
    have hp2 : ContinuousOn (fun q : ℝ × ℂ => q.2 - γ q.1)
        (Set.Icc A B ×ˢ K) :=
      continuous_snd.continuousOn.sub hpγ
    exact hp1.div hp2 (by
      intro q hq hzero
      have heq : q.2 = γ q.1 := sub_eq_zero.mp hzero
      exact (hout q.1 hq.1) (by simpa [heq] using hq.2))
  obtain ⟨n, t, d, ht, hs⟩ :=
    exists_riemann_sum_uniform K hK A B hAB H hcont hε
  refine ⟨n, (fun i => (d i : ℂ) * c (t i)),
              (fun i => γ (t i)), ?_, ?_⟩
  · intro i z hz heq
    exact (hout (t i) (ht i)) (by simpa [heq] using hz)
  · intro z hz
    simpa [H, mul_div_assoc] using hs z hz

end RungeSupport

end

-- END INLINED FILE: Mathlib/Support/runge_theorem_ac7707d823/CauchyApprox.lean

-- BEGIN INLINED FILE: Mathlib/Support/runge_theorem_ac7707d823/RectCauchy.lean
open scoped BigOperators Interval Real ComplexConjugate
open Set MeasureTheory intervalIntegral
noncomputable section
namespace RungeSupport
lemma inv_bottom_sub_top (r t : ℝ) (hr : r ≠ 0) :
    (((t:ℂ) - (r:ℂ)*Complex.I)⁻¹ - ((t:ℂ) + (r:ℂ)*Complex.I)⁻¹)
      = (( (2*r) / (r^2 + t^2) : ℝ) : ℂ) * Complex.I := by
  have hm : (t:ℂ) - (r:ℂ)*Complex.I ≠ 0 := by
    intro h; have hi := congrArg Complex.im h
    simp at hi
    exact hr hi
  have hp : (t:ℂ) + (r:ℂ)*Complex.I ≠ 0 := by
    intro h; have hi := congrArg Complex.im h
    simp at hi
    exact hr hi
  have hreal : r^2 + t^2 ≠ 0 := by positivity
  have hD : ((r:ℂ)^2 + (t:ℂ)^2) ≠ 0 := by
    exact_mod_cast hreal
  push_cast
  field_simp [hm, hp, hD]
  ring_nf
  simp [pow_succ, Complex.I_mul_I]
lemma inv_right_sub_left (r t : ℝ) (hr : r ≠ 0) :
    Complex.I * (((r:ℂ) + (t:ℂ)*Complex.I)⁻¹) -
      Complex.I * (((-r:ℝ):ℂ) + (t:ℂ)*Complex.I)⁻¹ =
        (((2*r)/(r^2+t^2):ℝ):ℂ) * Complex.I := by
  have hm : ((r:ℂ) + (t:ℂ)*Complex.I) ≠ 0 := by
    intro h; have hi := congrArg Complex.re h
    simp at hi
    exact hr hi
  have hp : (((-r:ℝ):ℂ) + (t:ℂ)*Complex.I) ≠ 0 := by
    intro h; have hi := congrArg Complex.re h
    simp at hi
    exact hr hi
  have hreal : r^2 + t^2 ≠ 0 := by positivity
  have hD : ((r:ℂ)^2 + (t:ℂ)^2) ≠ 0 := by exact_mod_cast hreal
  push_cast
  field_simp [hm, hp, hD]
  ring_nf
  have hm' : (r:ℂ) + Complex.I * (t:ℂ) ≠ 0 := by rwa [mul_comm]
  have hp' : (-(r:ℂ)) + Complex.I * (t:ℂ) ≠ 0 := by
    simpa [mul_comm] using hp
  field_simp [hm', hp']
  ring_nf
  simp [pow_succ, Complex.I_mul_I]

lemma rectInt_inv_origin (r : ℝ) (hr : 0 < r) :
    rectInt (fun w : ℂ => w⁻¹) (-r) r (-r) r = 2 * Real.pi * Complex.I := by
  have hn : r ≠ 0 := ne_of_gt hr
  have cb : Continuous (fun t : ℝ => (((t:ℂ) - (r:ℂ)*Complex.I)⁻¹)) :=
    ( (Complex.continuous_ofReal.sub continuous_const).inv₀
      (by intro t h; have hh:= congrArg Complex.im h; simp at hh; exact hn hh))
  have ct : Continuous (fun t : ℝ => (((t:ℂ) + (r:ℂ)*Complex.I)⁻¹)) :=
    ( (Complex.continuous_ofReal.add continuous_const).inv₀
      (by intro t h; have hh:= congrArg Complex.im h; simp at hh; exact hn hh))
  have cr : Continuous (fun t : ℝ => (((r:ℂ) + (t:ℂ)*Complex.I)⁻¹)) :=
    ( (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).inv₀
      (by intro t h; have hh:= congrArg Complex.re h; simp at hh; exact hn hh))
  have cl : Continuous (fun t : ℝ => ((((-r:ℝ):ℂ) + (t:ℂ)*Complex.I)⁻¹)) :=
    ( (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).inv₀
      (by intro t h; have hh:= congrArg Complex.re h; simp at hh; exact hn hh))
  have hb : IntervalIntegrable _ MeasureTheory.volume (-r) r := cb.intervalIntegrable _ _
  have ht : IntervalIntegrable _ MeasureTheory.volume (-r) r := ct.intervalIntegrable _ _
  have hri : IntervalIntegrable _ MeasureTheory.volume (-r) r := cr.intervalIntegrable _ _
  have hli : IntervalIntegrable _ MeasureTheory.volume (-r) r := cl.intervalIntegrable _ _
  dsimp [rectInt]
  simp only [Complex.ofReal_neg, neg_mul, one_div]
  have hb' : IntervalIntegrable (fun t : ℝ => ((t:ℂ) + -((r:ℂ)*Complex.I))⁻¹)
      MeasureTheory.volume (-r) r := by simpa [sub_eq_add_neg] using hb
  -- split the two opposite sides into integrals of their pointwise difference
  rw [← intervalIntegral.integral_sub hb' ht]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  rw [add_sub_assoc]
  rw [← intervalIntegral.integral_sub]
  · -- both parenthesized integrals have the same pointwise integrand
    have eval1 :
        (∫ x : ℝ in -r..r,
          (((x:ℂ) - (r:ℂ)*Complex.I)⁻¹ -
             ((x:ℂ) + (r:ℂ)*Complex.I)⁻¹)) =
        (∫ x : ℝ in -r..r,
          (((((2*r)/(r^2+x^2):ℝ):ℂ) * Complex.I))) := by
      apply intervalIntegral.integral_congr
      intro x _
      exact inv_bottom_sub_top r x hn
    have eval2 :
        (∫ x : ℝ in -r..r,
          (Complex.I * (((r:ℂ) + (x:ℂ)*Complex.I)⁻¹) -
           Complex.I * ((((-r:ℝ):ℂ) + (x:ℂ)*Complex.I)⁻¹))) =
        (∫ x : ℝ in -r..r,
          (((((2*r)/(r^2+x^2):ℝ):ℂ) * Complex.I))) := by
      apply intervalIntegral.integral_congr
      intro x _
      exact inv_right_sub_left r x hn
    have ev1 :
        (∫ x : ℝ in -r..r,
          (((x:ℂ) + -((r:ℂ)*Complex.I))⁻¹ -
             ((x:ℂ) + (r:ℂ)*Complex.I)⁻¹)) =
        (∫ x : ℝ in -r..r,
          (((((2*r)/(r^2+x^2):ℝ):ℂ) * Complex.I))) := by
            simpa [sub_eq_add_neg] using eval1
    have ev2 :
        (∫ x : ℝ in -r..r,
          (Complex.I * (((r:ℂ) + (x:ℂ)*Complex.I)⁻¹) -
           Complex.I * ((-(r:ℂ)) + (x:ℂ)*Complex.I)⁻¹)) =
        (∫ x : ℝ in -r..r,
          (((((2*r)/(r^2+x^2):ℝ):ℂ) * Complex.I))) := by
            simpa using eval2
    rw [ev1, ev2]
    -- evaluate the one real integral
    have realcalc :
        (∫ x : ℝ in -r..r, (2*r) / (r^2+x^2)) = Real.pi := by
      have hbase := integral_div_sq_add_sq (a:= -r) (b:=r) (c:=r)
      have hmul :
          (fun x : ℝ => (2*r)/(r^2+x^2)) =
          (fun x : ℝ => 2 * (r/(r^2+x^2))) := by
            funext x; ring
      rw [hmul, intervalIntegral.integral_const_mul, hbase]
      rw [div_self hn, neg_div, div_self hn]
      rw [Real.arctan_one, Real.arctan_neg, Real.arctan_one]
      ring
    have compcalc :
        (∫ x : ℝ in -r..r,
          (((((2*r)/(r^2+x^2):ℝ):ℂ) * Complex.I))) =
          (Real.pi:ℂ) * Complex.I := by
      rw [intervalIntegral.integral_mul_const]
      rw [intervalIntegral.integral_ofReal]
      rw [realcalc]
    rw [compcalc]
    ring
  · exact hri.const_mul Complex.I
  · simpa using (hli.const_mul Complex.I)

end RungeSupport

end

-- END INLINED FILE: Mathlib/Support/runge_theorem_ac7707d823/RectCauchy.lean

-- BEGIN INLINED FILE: Mathlib/Support/runge_theorem_ac7707d823/Local.lean

open scoped BigOperators Interval Real ComplexConjugate
open Set MeasureTheory intervalIntegral
noncomputable section
namespace RungeSupport

-- elementary parametrisation of a rectangle side
private lemma horiz_maps (a b y:ℝ) :
    Set.MapsTo (fun x : ℝ => (x:ℂ) + (y:ℂ)*Complex.I)
      (Set.uIcc a b) (Set.uIcc a b ×ℂ Set.uIcc y y) := by
  intro x hx
  exact (Complex.mem_reProdIm).2 ⟨by simpa, by simp⟩

lemma rect_cont_horiz (F : ℂ → ℂ) (a b c d y:ℝ)
    (hy : y ∈ Set.uIcc c d)
    (hF : ContinuousOn F (Set.uIcc a b ×ℂ Set.uIcc c d)) :
    ContinuousOn (fun x : ℝ => F ((x:ℂ)+(y:ℂ)*Complex.I)) (Set.uIcc a b) := by
  have hmap : Set.MapsTo (fun x : ℝ => (x:ℂ)+(y:ℂ)*Complex.I)
      (Set.uIcc a b) (Set.uIcc a b ×ℂ Set.uIcc c d) := by
    intro x hx
    exact (Complex.mem_reProdIm).2 ⟨by simpa, by simpa⟩
  have hc : Continuous (fun x : ℝ => (x:ℂ)+(y:ℂ)*Complex.I) :=
    Complex.continuous_ofReal.add continuous_const
  simpa [Function.comp_def] using hF.comp hc.continuousOn hmap

lemma rect_cont_vert (F : ℂ → ℂ) (a b c d x:ℝ)
    (hx : x ∈ Set.uIcc a b)
    (hF : ContinuousOn F (Set.uIcc a b ×ℂ Set.uIcc c d)) :
    ContinuousOn (fun y : ℝ => F ((x:ℂ)+(y:ℂ)*Complex.I)) (Set.uIcc c d) := by
  have hmap : Set.MapsTo (fun y : ℝ => (x:ℂ)+(y:ℂ)*Complex.I)
      (Set.uIcc c d) (Set.uIcc a b ×ℂ Set.uIcc c d) := by
    intro y hy
    exact (Complex.mem_reProdIm).2 ⟨by simpa, by simpa⟩
  have hc : Continuous (fun y : ℝ => (x:ℂ)+(y:ℂ)*Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  simpa [Function.comp_def] using hF.comp hc.continuousOn hmap

lemma rect_horiz_integrable (F : ℂ → ℂ) (a b c d y:ℝ)
    (hy : y ∈ Set.uIcc c d)
    (hF : ContinuousOn F (Set.uIcc a b ×ℂ Set.uIcc c d)) :
    IntervalIntegrable (fun x : ℝ => F ((x:ℂ)+(y:ℂ)*Complex.I)) volume a b :=
  (rect_cont_horiz F a b c d y hy hF).intervalIntegrable

lemma rect_vert_integrable (F : ℂ → ℂ) (a b c d x:ℝ)
    (hx : x ∈ Set.uIcc a b)
    (hF : ContinuousOn F (Set.uIcc a b ×ℂ Set.uIcc c d)) :
    IntervalIntegrable (fun y : ℝ => F ((x:ℂ)+(y:ℂ)*Complex.I)) volume c d :=
  (rect_cont_vert F a b c d x hx hF).intervalIntegrable

/-- A version of Cauchy--Goursat for the divided difference.  `dslope` is the
removable value of `(f w - f z)/(w-z)`; using it rather than an arbitrary value
at `z` makes the continuity hypothesis at a grid line automatic.  Notice
that only differentiability at the points of the closed rectangle (and at
`z`) is used. -/
lemma rectInt_dslope_zero (f : ℂ → ℂ) (z : ℂ) (a b c d : ℝ)
    (hz : DifferentiableAt ℂ f z)
    (hf : ∀ w ∈ (Set.uIcc a b ×ℂ Set.uIcc c d), DifferentiableAt ℂ f w) :
    rectInt (dslope f z) a b c d = 0 := by
  have hcont : ContinuousOn (dslope f z)
      (Set.uIcc a b ×ℂ Set.uIcc c d) := by
    intro w hw
    by_cases h : w = z
    · subst w
      exact (continuousAt_dslope_same.2 hz).continuousWithinAt
    · exact (continuousAt_dslope_of_ne h).2 (hf w hw).continuousAt |>.continuousWithinAt
  have hdiff :
      ∀ w ∈ (Set.Ioo (min a b) (max a b) ×ℂ
          Set.Ioo (min c d) (max c d)) \ ({z} : Set ℂ),
        DifferentiableAt ℂ (dslope f z) w := by
    intro w hw
    have hwrect : w ∈ (Set.uIcc a b ×ℂ Set.uIcc c d) := by
      have hr := (Complex.mem_reProdIm).1 hw.1
      apply (Complex.mem_reProdIm).2
      constructor
      · -- unordered closed interval
        simpa [Set.uIcc, Set.mem_Icc] using (show min a b ≤ w.re ∧ w.re ≤ max a b from ⟨le_of_lt hr.1.1, le_of_lt hr.1.2⟩)
      · have hi := hr.2
        simpa [Set.uIcc, Set.mem_Icc] using (show min c d ≤ w.im ∧ w.im ≤ max c d from ⟨le_of_lt hi.1, le_of_lt hi.2⟩)
    have hne : w ≠ z := by
      intro h; apply hw.2; simpa [h]
    exact (differentiableAt_dslope_of_ne hne).2 (hf w hwrect)
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
      (dslope f z) (⟨a,c⟩ : ℂ) (⟨b,d⟩ : ℂ) ({z} : Set ℂ)
      (Set.countable_singleton z) (by simpa using hcont) (by simpa using hdiff)
  simpa [rectInt] using h

/-- Linearity, in a form that doesn't require any global integrability, just
continuity on the closed rectangle.  This is useful since all the functions
appearing on a tiling are only specified there. -/
lemma rectInt_add_of_continuousOn (F G : ℂ → ℂ) (a b c d : ℝ)
    (hF : ContinuousOn F (Set.uIcc a b ×ℂ Set.uIcc c d))
    (hG : ContinuousOn G (Set.uIcc a b ×ℂ Set.uIcc c d)) :
    rectInt (fun w => F w + G w) a b c d =
      rectInt F a b c d + rectInt G a b c d := by
  have hyc : c ∈ Set.uIcc c d := left_mem_uIcc
  have hyd : d ∈ Set.uIcc c d := right_mem_uIcc
  have hxa : a ∈ Set.uIcc a b := left_mem_uIcc
  have hxb : b ∈ Set.uIcc a b := right_mem_uIcc
  have Fc := rect_horiz_integrable F a b c d c hyc hF
  have Fd := rect_horiz_integrable F a b c d d hyd hF
  have Gc := rect_horiz_integrable G a b c d c hyc hG
  have Gd := rect_horiz_integrable G a b c d d hyd hG
  have Fb := rect_vert_integrable F a b c d b hxb hF
  have Fa := rect_vert_integrable F a b c d a hxa hF
  have Gb := rect_vert_integrable G a b c d b hxb hG
  have Ga := rect_vert_integrable G a b c d a hxa hG
  dsimp [rectInt]
  rw [intervalIntegral.integral_add Fc Gc, intervalIntegral.integral_add Fd Gd,
      intervalIntegral.integral_add Fb Gb, intervalIntegral.integral_add Fa Ga]
  ring

lemma rectInt_const_mul (A : ℂ) (F : ℂ → ℂ) (a b c d : ℝ) :
    rectInt (fun w => A * F w) a b c d = A * rectInt F a b c d := by
  dsimp [rectInt]
  simp only [intervalIntegral.integral_const_mul]
  ring

/-- Translation of the inverse-square computation in `RectCauchy`.
The square is centered at an arbitrary complex point. -/
lemma rectInt_inv_center (z : ℂ) (r : ℝ) (hr : 0 < r) :
    rectInt (fun w : ℂ => (w - z)⁻¹)
      (z.re-r) (z.re+r) (z.im-r) (z.im+r) =
       2 * Real.pi * Complex.I := by
  -- translating four ordinary real interval integrals has no hypotheses
  have hor (y : ℝ) :
      (∫ x : ℝ in z.re-r..z.re+r,
        (((x:ℂ) + (y:ℂ)*Complex.I) - z)⁻¹) =
      (∫ x : ℝ in -r..r,
        ((x:ℂ) + ((y-z.im:ℝ):ℂ)*Complex.I)⁻¹) := by
    have E := intervalIntegral.integral_comp_add_right
      (f := fun x : ℝ => (((x:ℂ) + (y:ℂ)*Complex.I) - z)⁻¹)
      (a := -r) (b := r) z.re
    -- E has the reverse orientation of the desired equation
    rw [show -r + z.re = z.re-r by ring,
        show r + z.re = z.re+r by ring] at E
    rw [← E]
    apply intervalIntegral.integral_congr
    intro x hx
    apply congrArg Inv.inv
      (by apply Complex.ext <;> simp <;> ring)
  have ver (x : ℝ) :
      (∫ y : ℝ in z.im-r..z.im+r,
        (((x:ℂ) + (y:ℂ)*Complex.I) - z)⁻¹) =
      (∫ y : ℝ in -r..r,
        ((((x-z.re:ℝ):ℂ) + (y:ℂ)*Complex.I))⁻¹) := by
    have E := intervalIntegral.integral_comp_add_right
      (f := fun y : ℝ => (((x:ℂ) + (y:ℂ)*Complex.I) - z)⁻¹)
      (a := -r) (b := r) z.im
    rw [show -r + z.im = z.im-r by ring,
        show r + z.im = z.im+r by ring] at E
    rw [← E]
    apply intervalIntegral.integral_congr
    intro y hy
    apply congrArg Inv.inv
      (by apply Complex.ext <;> simp <;> ring)
  -- replace the four sides, then invoke the origin computation
  dsimp [rectInt]
  rw [hor (z.im-r), hor (z.im+r), ver (z.re+r), ver (z.re-r)]
  have base := rectInt_inv_origin r hr
  dsimp [rectInt] at base
  simpa using base

end RungeSupport

namespace RungeSupport
open Set MeasureTheory intervalIntegral

-- the inverse kernel is holomorphic on any rectangle which misses its pole
lemma rectInt_inv_zero_of_not_mem (z : ℂ) (a b c d : ℝ)
    (hz : z ∉ (Set.uIcc a b ×ℂ Set.uIcc c d)) :
    rectInt (fun w : ℂ => (w-z)⁻¹) a b c d = 0 := by
  apply rectInt_eq_zero_of_differentiableOn
  intro w hw
  have hne : w - z ≠ 0 := sub_ne_zero.mpr (by
    intro e; apply hz; simpa [e] using hw)
  have hs : DifferentiableWithinAt ℂ (fun u : ℂ => u-z) (Set.uIcc a b ×ℂ Set.uIcc c d) w :=
    differentiableWithinAt_id.sub_const z
  exact hs.inv hne

lemma inv_horiz_integrable_of_ne (z : ℂ) (y : ℝ) (hy : y ≠ z.im)
    (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => (((x:ℂ)+(y:ℂ)*Complex.I)-z)⁻¹)
      MeasureTheory.volume a b := by
  have hc0 : Continuous (fun x : ℝ => (x:ℂ)+(y:ℂ)*Complex.I-z) :=
    (Complex.continuous_ofReal.add continuous_const).sub continuous_const
  have hn : ∀ x : ℝ, (x:ℂ)+(y:ℂ)*Complex.I-z ≠ 0 := by
    intro x h
    have hi := congrArg Complex.im h
    simp at hi
    exact hy (sub_eq_zero.mp hi)
  exact (hc0.inv₀ hn).intervalIntegrable _ _
lemma inv_vert_integrable_of_ne (z : ℂ) (x : ℝ) (hx : x ≠ z.re)
    (c d : ℝ) :
    IntervalIntegrable (fun y : ℝ => (((x:ℂ)+(y:ℂ)*Complex.I)-z)⁻¹)
      MeasureTheory.volume c d := by
  have hc0 : Continuous (fun y : ℝ => (x:ℂ)+(y:ℂ)*Complex.I-z) :=
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).sub continuous_const
  have hn : ∀ y : ℝ, (x:ℂ)+(y:ℂ)*Complex.I-z ≠ 0 := by
    intro y h
    have hi := congrArg Complex.re h
    simp at hi
    exact hx (sub_eq_zero.mp hi)
  exact (hc0.inv₀ hn).intervalIntegrable _ _

/-- Shrinking the two real bounds past bands not containing the pole doesn't
change the boundary integral of the inverse. -/
lemma rectInt_inv_shrink_x (z : ℂ) (a l u b c d : ℝ)
    (hc : c < z.im) (hd : z.im < d)
    (hal : a ≤ l) (hl : l < z.re) (hu : z.re < u) (hub : u ≤ b) :
    rectInt (fun w : ℂ => (w-z)⁻¹) a b c d =
      rectInt (fun w : ℂ => (w-z)⁻¹) l u c d := by
  let F : ℂ → ℂ := fun w => (w-z)⁻¹
  have nc : c ≠ z.im := ne_of_lt hc
  have nd : d ≠ z.im := ne_of_gt hd
  have intc (p q:ℝ) : IntervalIntegrable (fun x:ℝ=> F ((x:ℂ)+(c:ℂ)*Complex.I)) volume p q :=
    inv_horiz_integrable_of_ne z c nc p q
  have intd (p q:ℝ) : IntervalIntegrable (fun x:ℝ=> F ((x:ℂ)+(d:ℂ)*Complex.I)) volume p q :=
    inv_horiz_integrable_of_ne z d nd p q
  have e1 := rectInt_vertical F a l b c d (intc a l) (intc l b) (intd a l) (intd l b)
  have e2 := rectInt_vertical F l u b c d (intc l u) (intc u b) (intd l u) (intd u b)
  have za : z ∉ (Set.uIcc a l ×ℂ Set.uIcc c d) := by
    intro h; have h' := (Complex.mem_reProdIm).1 h
    have hre : z.re ≤ l := by
      have lu : a ≤ l := hal
      have ht := h'.1
      rw [Set.uIcc_of_le hal] at ht
      exact ht.2
    exact (not_le_of_gt hl) hre
  have zb : z ∉ (Set.uIcc u b ×ℂ Set.uIcc c d) := by
    intro h; have h' := (Complex.mem_reProdIm).1 h
    have hb' : u ≤ b := hub
    have hre : u ≤ z.re := by
      have ht := h'.1
      rw [Set.uIcc_of_le hb'] at ht
      exact ht.1
    exact (not_le_of_gt hu) hre
  have z1 : rectInt F a l c d = 0 := rectInt_inv_zero_of_not_mem z a l c d za
  have z2 : rectInt F u b c d = 0 := rectInt_inv_zero_of_not_mem z u b c d zb
  dsimp [F] at e1 e2 z1 z2 ⊢
  rw [e1, e2, z1, z2]
  abel

lemma rectInt_inv_shrink_y (z : ℂ) (a b c l u d : ℝ)
    (ha : a < z.re) (hb : z.re < b)
    (hcl : c ≤ l) (hl : l < z.im) (hu : z.im < u) (hud : u ≤ d) :
    rectInt (fun w : ℂ => (w-z)⁻¹) a b c d =
      rectInt (fun w : ℂ => (w-z)⁻¹) a b l u := by
  let F : ℂ → ℂ := fun w => (w-z)⁻¹
  have na : a ≠ z.re := ne_of_lt ha
  have nb : b ≠ z.re := ne_of_gt hb
  have inta (p q:ℝ) : IntervalIntegrable (fun y:ℝ=> F ((a:ℂ)+(y:ℂ)*Complex.I)) volume p q :=
    inv_vert_integrable_of_ne z a na p q
  have intb (p q:ℝ) : IntervalIntegrable (fun y:ℝ=> F ((b:ℂ)+(y:ℂ)*Complex.I)) volume p q :=
    inv_vert_integrable_of_ne z b nb p q
  have e1 := rectInt_horizontal F a b c l d (inta c l) (inta l d) (intb c l) (intb l d)
  have e2 := rectInt_horizontal F a b l u d (inta l u) (inta u d) (intb l u) (intb u d)
  have za : z ∉ (Set.uIcc a b ×ℂ Set.uIcc c l) := by
    intro h; have h' := (Complex.mem_reProdIm).1 h
    have him : z.im ≤ l := by
      have hh : c ≤ l := hcl
      have ht := h'.2
      rw [Set.uIcc_of_le hcl] at ht
      exact ht.2
    exact (not_le_of_gt hl) him
  have zb : z ∉ (Set.uIcc a b ×ℂ Set.uIcc u d) := by
    intro h; have h' := (Complex.mem_reProdIm).1 h
    have hh : u ≤ d := hud
    have him : u ≤ z.im := by
      have ht := h'.2
      rw [Set.uIcc_of_le hud] at ht
      exact ht.1
    exact (not_le_of_gt hu) him
  have z1 : rectInt F a b c l = 0 := rectInt_inv_zero_of_not_mem z a b c l za
  have z2 : rectInt F a b u d = 0 := rectInt_inv_zero_of_not_mem z a b u d zb
  dsimp [F] at e1 e2 z1 z2 ⊢
  rw [e1, e2, z1, z2]
  abel

/-- Winding of any (not necessarily centred) axis rectangle at an interior
point.  The proof cuts off four pole-free bands and appeals just to the
centred elementary calculation. -/
lemma rectInt_inv_interior (z : ℂ) (a b c d : ℝ)
    (ha : a < z.re) (hb : z.re < b)
    (hc : c < z.im) (hd : z.im < d) :
    rectInt (fun w : ℂ => (w-z)⁻¹) a b c d = 2*Real.pi*Complex.I := by
  let r : ℝ := min (min (z.re-a) (b-z.re)) (min (z.im-c) (d-z.im)) / 2
  have hr : 0 < r := by
    dsimp [r]
    have : 0 < min (min (z.re-a) (b-z.re)) (min (z.im-c) (d-z.im)) := by
      simp [lt_min_iff, sub_pos.mpr ha, sub_pos.mpr hb, sub_pos.mpr hc, sub_pos.mpr hd]
    linarith
  have rle1 : r ≤ z.re-a := by
    dsimp [r]
    have h : 0 < z.re-a := sub_pos.mpr ha
    have hm : min (min (z.re-a) (b-z.re)) (min (z.im-c) (d-z.im)) ≤ z.re-a :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have rle2 : r ≤ b-z.re := by
    dsimp [r]
    have h : 0 < b-z.re := sub_pos.mpr hb
    have hm : min (min (z.re-a) (b-z.re)) (min (z.im-c) (d-z.im)) ≤ b-z.re :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  have rle3 : r ≤ z.im-c := by
    dsimp [r]
    have h : 0 < z.im-c := sub_pos.mpr hc
    have hm : min (min (z.re-a) (b-z.re)) (min (z.im-c) (d-z.im)) ≤ z.im-c :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have rle4 : r ≤ d-z.im := by
    dsimp [r]
    have h : 0 < d-z.im := sub_pos.mpr hd
    have hm : min (min (z.re-a) (b-z.re)) (min (z.im-c) (d-z.im)) ≤ d-z.im :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  have ex := rectInt_inv_shrink_x z a (z.re-r) (z.re+r) b c d hc hd
      (by linarith) (by linarith [hr]) (by linarith [hr]) (by linarith)
  have ey := rectInt_inv_shrink_y z (z.re-r) (z.re+r) c (z.im-r) (z.im+r) d
      (by linarith [hr]) (by linarith [hr]) (by linarith) (by linarith [hr])
      (by linarith [hr]) (by linarith)
  rw [ex, ey]
  exact rectInt_inv_center z r hr
end RungeSupport
namespace RungeSupport
open Set MeasureTheory intervalIntegral

lemma continuousOn_dslope_rect (f : ℂ → ℂ) (z : ℂ) (a b c d : ℝ)
    (hz : DifferentiableAt ℂ f z)
    (hf : ∀ w ∈ (Set.uIcc a b ×ℂ Set.uIcc c d), DifferentiableAt ℂ f w) :
    ContinuousOn (dslope f z) (Set.uIcc a b ×ℂ Set.uIcc c d) := by
  intro w hw
  by_cases h : w = z
  · subst w
    exact (continuousAt_dslope_same.2 hz).continuousWithinAt
  · exact ((continuousAt_dslope_of_ne h).2 (hf w hw).continuousAt).continuousWithinAt

/-- Cauchy's formula on one closed rectangle.  This is the local version used
in a square tiling.  It deliberately asks for differentiability only at the
points of the rectangle; in an open analytic set these are obtained simply
by containment. -/
lemma rectInt_cauchy_interior (f : ℂ → ℂ) (z : ℂ) (a b c d : ℝ)
    (ha : a < z.re) (hb : z.re < b) (hc : c < z.im) (hd : z.im < d)
    (hz : DifferentiableAt ℂ f z)
    (hf : ∀ w ∈ (Set.uIcc a b ×ℂ Set.uIcc c d), DifferentiableAt ℂ f w) :
    rectInt (fun w : ℂ => f w / (w-z)) a b c d =
      f z * (2*Real.pi*Complex.I) := by
  let Q : ℂ → ℂ := fun w => f z * (w-z)⁻¹
  let H : ℂ → ℂ := dslope f z
  let D : ℂ → ℂ := fun w => f w / (w-z)
  have hH : ContinuousOn H (Set.uIcc a b ×ℂ Set.uIcc c d) :=
    continuousOn_dslope_rect f z a b c d hz hf
  have point (w : ℂ) (hw : w ≠ z) : D w = Q w + H w := by
    dsimp [D, Q, H]
    rw [dslope_of_ne f hw]
    dsimp [slope]
    field_simp
    ring
  have hcne : c ≠ z.im := ne_of_lt hc
  have hdne : d ≠ z.im := ne_of_gt hd
  have hane : a ≠ z.re := ne_of_lt ha
  have hbne : b ≠ z.re := ne_of_gt hb
  have hori (y : ℝ) (ym : y ∈ Set.uIcc c d) (hy : y ≠ z.im) :
      (∫ x : ℝ in a..b, D ((x:ℂ)+(y:ℂ)*Complex.I)) =
       (∫ x : ℝ in a..b, Q ((x:ℂ)+(y:ℂ)*Complex.I)) +
       (∫ x : ℝ in a..b, H ((x:ℂ)+(y:ℂ)*Complex.I)) := by
    have q : IntervalIntegrable (fun x : ℝ => Q ((x:ℂ)+(y:ℂ)*Complex.I)) volume a b := by
      change IntervalIntegrable
        (fun x : ℝ => f z * ((((x:ℂ)+(y:ℂ)*Complex.I)-z)⁻¹)) volume a b
      exact (inv_horiz_integrable_of_ne z y hy a b).const_mul (f z)
    have hh : IntervalIntegrable (fun x : ℝ => H ((x:ℂ)+(y:ℂ)*Complex.I)) volume a b :=
      rect_horiz_integrable H a b c d y ym hH
    rw [← intervalIntegral.integral_add q hh]
    apply intervalIntegral.integral_congr
    intro x hx
    exact point _ (by
      intro e
      have h' := congrArg Complex.im e
      simp at h'
      exact hy h')
  have vert (x : ℝ) (xm : x ∈ Set.uIcc a b) (hx : x ≠ z.re) :
      (∫ y : ℝ in c..d, D ((x:ℂ)+(y:ℂ)*Complex.I)) =
       (∫ y : ℝ in c..d, Q ((x:ℂ)+(y:ℂ)*Complex.I)) +
       (∫ y : ℝ in c..d, H ((x:ℂ)+(y:ℂ)*Complex.I)) := by
    have q : IntervalIntegrable (fun y : ℝ => Q ((x:ℂ)+(y:ℂ)*Complex.I)) volume c d := by
      change IntervalIntegrable
        (fun y : ℝ => f z * ((((x:ℂ)+(y:ℂ)*Complex.I)-z)⁻¹)) volume c d
      exact (inv_vert_integrable_of_ne z x hx c d).const_mul (f z)
    have hh : IntervalIntegrable (fun y : ℝ => H ((x:ℂ)+(y:ℂ)*Complex.I)) volume c d :=
      rect_vert_integrable H a b c d x xm hH
    rw [← intervalIntegral.integral_add q hh]
    apply intervalIntegral.integral_congr
    intro y hy
    exact point _ (by
      intro e
      have h' := congrArg Complex.re e
      simp at h'
      exact hx h')
  have split : rectInt D a b c d = rectInt Q a b c d + rectInt H a b c d := by
    dsimp [rectInt]
    rw [hori c left_mem_uIcc hcne, hori d right_mem_uIcc hdne,
        vert b right_mem_uIcc hbne, vert a left_mem_uIcc hane]
    ring
  change rectInt D a b c d = _
  rw [split]
  have hQ : rectInt Q a b c d = f z * (2*Real.pi*Complex.I) := by
    change rectInt (fun w : ℂ => f z * (w-z)⁻¹) a b c d = _
    rw [rectInt_const_mul, rectInt_inv_interior z a b c d ha hb hc hd]
  have hHzero : rectInt H a b c d = 0 :=
    rectInt_dslope_zero f z a b c d hz hf
  rw [hQ, hHzero, add_zero]
end RungeSupport

end

-- END INLINED FILE: Mathlib/Support/runge_theorem_ac7707d823/Local.lean

-- BEGIN INLINED FILE: Mathlib/Support/runge_theorem_ac7707d823/Reduction.lean

open scoped BigOperators Polynomial Interval
open Set MeasureTheory Polynomial intervalIntegral

noncomputable section

namespace RungeSupport

/-- A convenient, quite weak version of the contour reduction of Runge's
 theorem. Once a function on a compact set has been written as finitely many
 Cauchy integrals along arcs that avoid the set, no analysis remains: uniform
 Riemann sums give simple poles and a common denominator gives polynomials.
 The hard geometric/Cauchy step in the usual proof is exactly producing the
 data `hrep`; the lemma deliberately packages everything after that step. -/
lemma of_contour_representation
    (K : Set ℂ) (hK : IsCompact K) (f : ℂ → ℂ)
    (m : ℕ) (c γ : Fin m → ℝ → ℂ)
    (hc : ∀ j, ContinuousOn (c j) (Set.Icc (0:ℝ) 1))
    (hγ : ∀ j, ContinuousOn (γ j) (Set.Icc (0:ℝ) 1))
    (hout : ∀ j t, t ∈ Set.Icc (0:ℝ) 1 → γ j t ∉ K)
    (hrep : ∀ z ∈ K, f z =
      ∑ j : Fin m, (∫ t : ℝ in (0:ℝ)..1, c j t / (z - γ j t)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p q : ℂ[X], (∀ z ∈ K, q.eval z ≠ 0) ∧
      (∀ z ∈ K, ‖f z - p.eval z / q.eval z‖ < ε) := by
  classical
  -- Give each of the `m` arcs a little less than ε/(m+1) of error.
  let e : ℝ := ε / (m + 1 : ℕ)
  have he : 0 < e := by
    dsimp [e]
    positivity
  have each (j : Fin m) : ∃ n : ℕ, ∃ a b : Fin n → ℂ,
      (∀ i z, z ∈ K → z ≠ b i) ∧
      ∀ z ∈ K,
        ‖(∫ t : ℝ in (0:ℝ)..1, c j t / (z - γ j t)) -
            ∑ i : Fin n, a i / (z - b i)‖ < e :=
    exists_fin_kernel_sum K hK 0 1 (by norm_num)
      (c j) (γ j) (hc j) (hγ j) (hout j) he
  choose n a b hb happ using each
  -- The disjoint union of the small Cauchy sums is again a finite Cauchy
  -- sum. Working with a `Sigma` avoids bookkeeping about partial sums.
  let ι := (j : Fin m) × Fin (n j)
  let aa : ι → ℂ := fun i => a i.1 i.2
  let bb : ι → ℂ := fun i => b i.1 i.2
  apply of_fintype_cauchy_approx K f ε aa bb
  · intro i z hz
    exact hb i.1 i.2 z hz
  · intro z hz
    have hcalc : f z - (∑ i : ι, aa i / (z - bb i)) =
        ∑ j : Fin m,
          ((∫ t : ℝ in (0:ℝ)..1, c j t / (z - γ j t)) -
              ∑ k : Fin (n j), a j k / (z - b j k)) := by
      rw [hrep z hz]
      classical
      -- flatten the sum over the sigma type
      change (∑ j : Fin m, (∫ t : ℝ in (0:ℝ)..1, c j t / (z - γ j t))) -
          (∑ i : (j : Fin m) × Fin (n j),
            a i.1 i.2 / (z - b i.1 i.2)) = _
      have hsg :
          (∑ i : (j : Fin m) × Fin (n j),
            a i.1 i.2 / (z - b i.1 i.2)) =
            ∑ j : Fin m, ∑ k : Fin (n j), a j k / (z - b j k) := by
        classical
        -- expand the two Fintype sums as sums over `univ`
        have hh := Finset.sum_sigma'
          (Finset.univ : Finset (Fin m))
          (fun j : Fin m => (Finset.univ : Finset (Fin (n j))))
          (fun j (k : Fin (n j)) => a j k / (z - b j k))
        simpa [Finset.univ_sigma_univ] using hh.symm
      rw [hsg]
      rw [Finset.sum_sub_distrib]
    rw [hcalc]
    calc
      ‖∑ j : Fin m,
          ((∫ t : ℝ in (0:ℝ)..1, c j t / (z - γ j t)) -
              ∑ k : Fin (n j), a j k / (z - b j k))‖
        ≤ ∑ j : Fin m,
          ‖((∫ t : ℝ in (0:ℝ)..1, c j t / (z - γ j t)) -
              ∑ k : Fin (n j), a j k / (z - b j k))‖ := by
            exact norm_sum_le _ _
      _ < ε := by
        have hle : (∑ j : Fin m,
          ‖((∫ t : ℝ in (0:ℝ)..1, c j t / (z - γ j t)) -
              ∑ k : Fin (n j), a j k / (z - b j k))‖)
            ≤ ∑ _j : Fin m, e := by
          exact Finset.sum_le_sum (fun j hj => le_of_lt (happ j z hz))
        refine lt_of_le_of_lt hle ?_
        -- m copies of ε/(m+1) are bounded by ε.
        simp only [Finset.sum_const_zero, Finset.sum_const]
        simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        dsimp [e]
        have hmpos : (0:ℝ) < (m:ℝ) + 1 := by positivity
        have hmul : (m:ℝ) * (ε / ((m + 1 : ℕ):ℝ)) < ε := by
          have : (m:ℝ) < (m:ℝ) + 1 := by linarith
          calc
            (m:ℝ) * (ε / ((m + 1 : ℕ):ℝ))
                = ε * ((m:ℝ) / ((m:ℝ) + 1)) := by
                    push_cast
                    ring
            _ < ε := by
              have hfrac : (m:ℝ) / ((m:ℝ)+1) < 1 := (div_lt_one hmpos).2 (by linarith)
              have hnon : 0 < ε := hε
              nlinarith
        exact (by simpa using hmul)

end RungeSupport

end

-- END INLINED FILE: Mathlib/Support/runge_theorem_ac7707d823/Reduction.lean

-- BEGIN INLINED FILE: Mathlib/Support/runge_theorem_ac7707d823/Mesh.lean
open scoped BigOperators Interval Real
open Set MeasureTheory intervalIntegral
noncomputable section
namespace RungeSupport

lemma dist_mk_le_taxicab (x y u v : ℝ) :
 dist ((x:ℂ)+(y:ℂ)*Complex.I) ((u:ℂ)+(v:ℂ)*Complex.I) ≤ |x-u| + |y-v| := by
 rw [dist_eq_norm]
 have eqn : ((x:ℂ)+(y:ℂ)*Complex.I) - ((u:ℂ)+(v:ℂ)*Complex.I) =
    ((x-u:ℝ):ℂ) + ((y-v:ℝ):ℂ)*Complex.I := by
      push_cast
      ring
 rw [eqn]
 calc
  _ ≤ ‖((x-u:ℝ):ℂ)‖ + ‖((y-v:ℝ):ℂ)*Complex.I‖ := norm_add_le _ _
  _ = _ := by
    have h1 : ‖((x-u:ℝ):ℂ)‖ = |x-u| := by rw [Complex.norm_real, Real.norm_eq_abs]
    have h2 : ‖((y-v:ℝ):ℂ)‖ = |y-v| := by rw [Complex.norm_real, Real.norm_eq_abs]
    rw [norm_mul, Complex.norm_I, mul_one, h1, h2]

def meshCoord (A s : ℝ) (i : ℕ) : ℝ := A + (i:ℝ)*s
def meshSquare (A s : ℝ) (i j : ℕ) : Set ℂ :=
  (Set.Icc (meshCoord A s i) (meshCoord A s (i+1))) ×ℂ
    (Set.Icc (meshCoord A s j) (meshCoord A s (j+1)))

lemma meshCoord_succ (A s : ℝ) (i:ℕ) :
  meshCoord A s (i+1) = meshCoord A s i + s := by
  dsimp [meshCoord]
  push_cast
  ring

lemma mem_meshSquare {A s : ℝ} {i j : ℕ} {w : ℂ} :
 w ∈ meshSquare A s i j ↔
  meshCoord A s i ≤ w.re ∧ w.re ≤ meshCoord A s i + s ∧
  meshCoord A s j ≤ w.im ∧ w.im ≤ meshCoord A s j + s := by
  rw [meshSquare, Complex.mem_reProdIm]
  simp only [Set.mem_Icc, meshCoord_succ]
  aesop

/-- Every cell that meets `K` lies in the closed `2s` collar.  Proving this
once avoids all square-root estimates later in the tiling: the taxicab bound
is plenty. -/
lemma meshSquare_subset_cthickening
    (K : Set ℂ) {A s : ℝ} (hs : 0 ≤ s) {i j : ℕ}
    (hit : (K ∩ meshSquare A s i j).Nonempty) :
    meshSquare A s i j ⊆ Metric.cthickening (2*s) K := by
  rcases hit with ⟨z, hzK, hzs⟩
  intro w hw
  have zw := (mem_meshSquare.mp hw)
  have zz := (mem_meshSquare.mp hzs)
  have hre : |w.re-z.re| ≤ s := by
    rw [abs_le]
    constructor <;> linarith [zw.1, zw.2.1, zz.1, zz.2.1]
  have him : |w.im-z.im| ≤ s := by
    rw [abs_le]
    constructor <;> linarith [zw.2.2.1, zw.2.2.2, zz.2.2.1, zz.2.2.2]
  apply Metric.mem_cthickening_of_dist_le w z (2*s) K hzK
  calc
   dist w z = dist ((w.re:ℂ)+(w.im:ℂ)*Complex.I)
       ((z.re:ℂ)+(z.im:ℂ)*Complex.I) := by rw [Complex.re_add_im, Complex.re_add_im]
   _ ≤ |w.re-z.re| + |w.im-z.im| := dist_mk_le_taxicab _ _ _ _
   _ ≤ 2*s := by linarith

lemma meshCoord_strictMono (A : ℝ) {s : ℝ} (hs : 0 < s) :
    StrictMono (meshCoord A s) := by
  intro i k h
  dsimp [meshCoord]
  have : (i:ℝ) < (k:ℝ) := by exact_mod_cast h
  nlinarith

/-- A coordinate in the open big box belongs to one of its `N` cells.  We
use natural floor rather than integers because the outer box has a genuine
left end. The half-open inequalities are stronger than what subsequent edge
arguments need. -/
lemma exists_mesh_index {A s x : ℝ} (hs : 0 < s) {N : ℕ}
    (hl : A < x) (hu : x < meshCoord A s N) :
    ∃ i : ℕ, i < N ∧ meshCoord A s i ≤ x ∧ x < meshCoord A s (i+1) := by
  let y : ℝ := (x-A)/s
  have hy : 0 ≤ y := by dsimp [y]; exact (div_nonneg (sub_nonneg.mpr (le_of_lt hl)) (le_of_lt hs))
  let i : ℕ := ⌊y⌋₊
  have lower : (i:ℝ) ≤ y := Nat.floor_le hy
  have upper : y < (i:ℝ)+1 := Nat.lt_floor_add_one y
  have yN : y < (N:ℝ) := by
    dsimp [y, meshCoord] at *
    apply (div_lt_iff₀ hs).2
    have H := hu
    -- casts are harmless here
    linarith
  have iN : i < N := (Nat.floor_lt hy).2 yN
  refine ⟨i, iN, ?_, ?_⟩
  · dsimp [meshCoord]
    dsimp [y] at lower
    apply (le_div_iff₀ hs).mp at lower
    nlinarith
  · rw [meshCoord_succ]
    dsimp [meshCoord]
    dsimp [y] at upper
    apply (div_lt_iff₀ hs).mp at upper
    nlinarith

lemma mesh_point_in_square {A s : ℝ} (hs : 0 < s) {N : ℕ}
    {z : ℂ}
    (hzr : z.re ∈ Set.Ioo A (meshCoord A s N))
    (hzi : z.im ∈ Set.Ioo A (meshCoord A s N)) :
    ∃ i j : ℕ, i < N ∧ j < N ∧ z ∈ meshSquare A s i j := by
  rcases exists_mesh_index hs hzr.1 hzr.2 with ⟨i, hi, hil, hiu⟩
  rcases exists_mesh_index hs hzi.1 hzi.2 with ⟨j, hj, hjl, hju⟩
  refine ⟨i,j,hi,hj,(mem_meshSquare).2 ?_⟩
  constructor
  · exact hil
  constructor
  · rw [← meshCoord_succ]; exact le_of_lt hiu
  constructor
  · exact hjl
  · rw [← meshCoord_succ]; exact le_of_lt hju

end RungeSupport
namespace RungeSupport
/-- A finite positive mesh with small side covering a nonempty compact set.
The coordinates of every point are in the *open* large box; the spare unit in
`R=B+1` is very convenient at the outer edges. -/
lemma exists_small_mesh (K : Set ℂ) (hK : IsCompact K) (h0 : K.Nonempty)
    (d : ℝ) (hd : 0 < d) :
    ∃ (A s : ℝ) (N : ℕ), 0 < s ∧ 2*s < d ∧
       ∀ z ∈ K, z.re ∈ Set.Ioo A (meshCoord A s N) ∧
                       z.im ∈ Set.Ioo A (meshCoord A s N) := by
  obtain ⟨B, hB⟩ := (Metric.isBounded_iff_subset_ball (0:ℂ)).1 hK.isBounded
  obtain ⟨w, hw⟩ := h0
  have Bp : 0 < B := by
    have H := hB hw
    have nn : 0 ≤ dist w (0:ℂ) := dist_nonneg
    rw [Metric.mem_ball] at H
    simpa [dist_comm] using (lt_of_le_of_lt nn (by simpa [dist_comm] using H))
  let R : ℝ := B + 1
  have Rp : 0 < R := by dsimp [R]; linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (max (4*R/d) (1:ℝ))
  let N : ℕ := n
  have NN : 0 < (N:ℝ) := lt_trans (by norm_num : (0:ℝ)<1)
        (lt_of_le_of_lt (le_max_right _ _) hn)
  let s : ℝ := 2*R/(N:ℝ)
  have sp : 0 < s := by dsimp [s]; positivity
  have sd : 2*s < d := by
    have H : 4*R/d < (N:ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
    dsimp [s]
    have := (div_lt_iff₀ (show (0:ℝ)<d from hd)).1 H
    calc
      2 * (2*R / (N:ℝ)) = (4*R) / (N:ℝ) := by ring
      _ < d := (div_lt_iff₀ NN).2 (by nlinarith)
  refine ⟨-R, s, N, sp, sd, ?_⟩
  have top : meshCoord (-R) s N = R := by
    dsimp [meshCoord, s]
    field_simp
    ring
  intro z hz
  have hzB := hB hz
  rw [Metric.mem_ball] at hzB
  have znorm : ‖z‖ < B := by simpa [dist_comm] using hzB
  rw [top]
  constructor
  · have ar := (Complex.abs_re_le_norm z).trans_lt znorm
    rw [abs_lt] at ar
    constructor <;> dsimp [R] <;> linarith [ar.1, ar.2]
  · have ai := (Complex.abs_im_le_norm z).trans_lt znorm
    rw [abs_lt] at ai
    constructor <;> dsimp [R] <;> linarith [ai.1, ai.2]
end RungeSupport
namespace RungeSupport
/-- On an internal horizontal grid edge a point of `K` witnesses *both*
adjacent squares. Thus after cancellation no retained internal edge contains a
point of K, including at its end points. -/
lemma mesh_horizontal_two_hits (K : Set ℂ) {A s : ℝ} {i j : ℕ}
    (hs : 0 ≤ s) (hj : 0 < j) {x : ℝ}
    (hx0 : meshCoord A s i ≤ x)
    (hx1 : x ≤ meshCoord A s (i+1))
    (hk : ((x:ℂ)+(meshCoord A s j:ℂ)*Complex.I) ∈ K) :
    (K ∩ meshSquare A s i j).Nonempty ∧
    (K ∩ meshSquare A s i (j-1)).Nonempty := by
  let w : ℂ := (x:ℂ)+(meshCoord A s j:ℂ)*Complex.I
  have wm : w ∈ K := hk
  have one : w ∈ meshSquare A s i j := (mem_meshSquare).2
    ⟨by simpa [w], by simpa [w, meshCoord_succ] using hx1,
     by simp [w], by simp [w, hs]⟩
  have pred : (j-1)+1 = j := by omega
  have two : w ∈ meshSquare A s i (j-1) := (mem_meshSquare).2
    ⟨by simpa [w], by simpa [w, meshCoord_succ] using hx1,
     by
       have ht : meshCoord A s (j-1) ≤ meshCoord A s j := by
         rw [← pred, meshCoord_succ]
         exact le_add_of_nonneg_right hs
       simpa [w] using ht,
     by rw [← meshCoord_succ, pred]; simp [w]⟩
  exact ⟨⟨w, wm, one⟩, ⟨w, wm, two⟩⟩

lemma mesh_vertical_two_hits (K : Set ℂ) {A s : ℝ} {i j : ℕ}
    (hs : 0 ≤ s) (hi : 0 < i) {y : ℝ}
    (hy0 : meshCoord A s j ≤ y) (hy1 : y ≤ meshCoord A s (j+1))
    (hk : (((meshCoord A s i:ℝ):ℂ)+(y:ℂ)*Complex.I) ∈ K) :
    (K ∩ meshSquare A s i j).Nonempty ∧
    (K ∩ meshSquare A s (i-1) j).Nonempty := by
  let w : ℂ := (meshCoord A s i:ℂ)+(y:ℂ)*Complex.I
  have pred : (i-1)+1 = i := by omega
  have one : w ∈ meshSquare A s i j := (mem_meshSquare).2
    ⟨by simp [w], by simp [w, hs], by simpa [w],
     by simpa [w, meshCoord_succ] using hy1⟩
  have two : w ∈ meshSquare A s (i-1) j := (mem_meshSquare).2
    ⟨by
       have ht : meshCoord A s (i-1) ≤ meshCoord A s i := by
         rw [← pred, meshCoord_succ]
         exact le_add_of_nonneg_right hs
       simpa [w] using ht,
     by rw [← meshCoord_succ, pred]; simp [w], by simpa [w],
     by simpa [w, meshCoord_succ] using hy1⟩
  exact ⟨⟨w, hk, one⟩, ⟨w, hk, two⟩⟩
end RungeSupport

end

-- END INLINED FILE: Mathlib/Support/runge_theorem_ac7707d823/Mesh.lean

-- BEGIN INLINED FILE: Mathlib/Support/runge_theorem_ac7707d823/Boundary.lean
open scoped BigOperators Interval Real
open Set MeasureTheory intervalIntegral
noncomputable section
namespace RungeSupport
attribute [local instance] Classical.propDecidable Classical.decEq

/-- coefficients of horizontal and vertical grid edges for an arbitrary predicate
of kept cells.  Indices for horizontal are `i<N, j≤N`, vertical `i≤N,j<N`. -/
def hcoef (P : ℕ → ℕ → Prop)
    (N i j : ℕ) : ℂ :=
  (if j < N ∧ P i j then 1 else 0) -
  (if 0 < j ∧ P i (j-1) then 1 else 0)

def vcoef (P : ℕ → ℕ → Prop)
    (N i j : ℕ) : ℂ :=
  (if 0 < i ∧ P (i-1) j then 1 else 0) -
  (if i < N ∧ P i j then 1 else 0)

-- convenience decidability

lemma hcoef_mul_sum (P : ℕ → ℕ → Prop)
    (N i : ℕ) (E : ℕ → ℂ) :
    ∑ j ∈ Finset.range (N+1), hcoef P N i j * E j =
      (∑ j ∈ Finset.range N, if P i j then E j else 0) -
      (∑ j ∈ Finset.range N, if P i j then E (j+1) else 0) := by
  classical
  have first :
      (∑ j ∈ Finset.range (N+1),
        if j < N ∧ P i j then E j else 0) =
      ∑ j ∈ Finset.range N, if P i j then E j else 0 := by
    rw [Finset.sum_range_succ]
    simp
    apply Finset.sum_congr rfl
    intro k hk
    simp [(Finset.mem_range.mp hk)]
  have second :
      (∑ j ∈ Finset.range (N+1),
        if 0 < j ∧ P i (j-1) then E j else 0) =
      ∑ j ∈ Finset.range N, if P i j then E (j+1) else 0 := by
    rw [Finset.sum_range_succ']
    simp
  -- distribute the two halves
  rw [← first, ← second]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  dsimp [hcoef]
  by_cases h1 : j < N ∧ P i j <;> by_cases h2 : 0 < j ∧ P i (j-1) <;> simp [h1, h2]

lemma vcoef_mul_sum (P : ℕ → ℕ → Prop)
    (N j : ℕ) (E : ℕ → ℂ) :
    ∑ i ∈ Finset.range (N+1), vcoef P N i j * E i =
      (∑ i ∈ Finset.range N, if P i j then E (i+1) else 0) -
      (∑ i ∈ Finset.range N, if P i j then E i else 0) := by
  classical
  have first :
      (∑ i ∈ Finset.range (N+1),
        if 0 < i ∧ P (i-1) j then E i else 0) =
      ∑ i ∈ Finset.range N, if P i j then E (i+1) else 0 := by
    rw [Finset.sum_range_succ']
    simp
  have second :
      (∑ i ∈ Finset.range (N+1),
        if i < N ∧ P i j then E i else 0) =
      ∑ i ∈ Finset.range N, if P i j then E i else 0 := by
    rw [Finset.sum_range_succ]
    simp
    apply Finset.sum_congr rfl
    intro k hk
    simp [(Finset.mem_range.mp hk)]
  rw [← first, ← second, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp [vcoef]
  by_cases h1 : 0 < i ∧ P (i-1) j <;> by_cases h2 : i < N ∧ P i j <;> simp [h1, h2]

/-- edge integrals in real coordinates -/
def hedge (A s : ℝ) (F : ℂ → ℂ) (i j : ℕ) : ℂ :=
  ∫ x : ℝ in meshCoord A s i..meshCoord A s (i+1),
      F ((x:ℂ) + (meshCoord A s j : ℂ) * Complex.I)
def vedge (A s : ℝ) (F : ℂ → ℂ) (i j : ℕ) : ℂ :=
  ∫ y : ℝ in meshCoord A s j..meshCoord A s (j+1),
      F ((meshCoord A s i : ℂ) + (y:ℂ) * Complex.I)

def cellsum (A s : ℝ) (N : ℕ) (P : ℕ → ℕ → Prop)
    (F : ℂ → ℂ) : ℂ :=
  ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
    if P i j then
      rectInt F (meshCoord A s i) (meshCoord A s (i+1))
        (meshCoord A s j) (meshCoord A s (j+1))
    else 0

def edgesum (A s : ℝ) (N : ℕ) (P : ℕ → ℕ → Prop)
    (F : ℂ → ℂ) : ℂ :=
  (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range (N+1),
      hcoef P N i j * hedge A s F i j) +
    Complex.I *
      (∑ j ∈ Finset.range N, ∑ i ∈ Finset.range (N+1),
        vcoef P N i j * vedge A s F i j)

lemma rectInt_mesh (A s : ℝ) (F : ℂ → ℂ) (i j : ℕ) :
    rectInt F (meshCoord A s i) (meshCoord A s (i+1))
        (meshCoord A s j) (meshCoord A s (j+1)) =
      hedge A s F i j - hedge A s F i (j+1) +
      Complex.I * vedge A s F (i+1) j -
      Complex.I * vedge A s F i j := by
  rfl

/-- Pure finite cancellation: the sum of all kept oriented rectangles is the
sum over lattice edges with incidence coefficients.  No integrability hypotheses
are involved here. -/
lemma cellsum_eq_edgesum (A s : ℝ) (N : ℕ)
    (P : ℕ → ℕ → Prop) (F : ℂ → ℂ) :
    cellsum A s N P F = edgesum A s N P F := by
  classical
  -- reduce rows of horizontal contribution and columns of vertical
  dsimp [cellsum, edgesum]
  -- expand rectangles under cell indicators
  simp_rw [rectInt_mesh]
  -- distribute row-wise; reorganize vertical by transposing finite sums
  -- First express as sum horizontal plus I times vertical using ring.
  let H : ℕ → ℕ → ℂ := fun i j =>
    if P i j then hedge A s F i j - hedge A s F i (j+1) else 0
  let V : ℕ → ℕ → ℂ := fun i j =>
    if P i j then vedge A s F (i+1) j - vedge A s F i j else 0
  have point (i j : ℕ) :
      (if P i j then
          hedge A s F i j - hedge A s F i (j+1) +
            Complex.I * vedge A s F (i+1) j -
            Complex.I * vedge A s F i j else 0)
        = H i j + Complex.I * V i j := by
      dsimp [H,V]
      split_ifs <;> ring
  simp_rw [point]
  simp_rw [Finset.sum_add_distrib]
  simp_rw [← Finset.mul_sum]
  -- after the simplifications sums are separated
  -- horizontal rows
  have hrow (i : ℕ) :
      ∑ j ∈ Finset.range N, H i j =
        ∑ j ∈ Finset.range (N+1), hcoef P N i j * hedge A s F i j := by
    dsimp [H]
    -- split if over difference
    rw [hcoef_mul_sum P N i]
    
    -- each indicator of a difference is the difference of indicators
    have t (j : ℕ) :
        (if P i j then hedge A s F i j - hedge A s F i (j+1) else 0)
        = (if P i j then hedge A s F i j else 0) -
          (if P i j then hedge A s F i (j+1) else 0) := by
          split_ifs <;> ring
    simp_rw [t]
    rw [Finset.sum_sub_distrib]
  have hrows :
      (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, H i j) =
       ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range (N+1),
          hcoef P N i j * hedge A s F i j := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hrow i
  have vcol (j : ℕ) :
      ∑ i ∈ Finset.range N, V i j =
        ∑ i ∈ Finset.range (N+1), vcoef P N i j * vedge A s F i j := by
    dsimp [V]
    rw [vcoef_mul_sum P N j]
    have t (i : ℕ) :
        (if P i j then vedge A s F (i+1) j - vedge A s F i j else 0)
        = (if P i j then vedge A s F (i+1) j else 0) -
          (if P i j then vedge A s F i j else 0) := by
          split_ifs <;> ring
    simp_rw [t]
    rw [Finset.sum_sub_distrib]
  have swap :
      (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, V i j) =
      ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range N, V i j := by
    exact Finset.sum_comm
  rw [hrows, swap]
  simp_rw [vcol]


end RungeSupport

namespace RungeSupport
attribute [local instance] Classical.propDecidable Classical.decEq

def meshHit (K : Set ℂ) (A s : ℝ) (i j : ℕ) : Prop :=
  (K ∩ meshSquare A s i j).Nonempty

/-- Nonzero edge coefficients are exactly the uncancelled boundary edges; they
miss K on their *closed* segment. Endpoint control is useful for contours. -/
lemma hcoef_edge_avoids (K : Set ℂ) (A s : ℝ) (N i j : ℕ) (hs : 0 ≤ s)
    (hbox : ∀ z ∈ K, z.re ∈ Set.Ioo A (meshCoord A s N) ∧
                       z.im ∈ Set.Ioo A (meshCoord A s N))
    (hn : hcoef (meshHit K A s) N i j ≠ 0) :
    ∀ x ∈ Set.Icc (meshCoord A s i) (meshCoord A s (i+1)),
      ((x:ℂ) + (meshCoord A s j : ℂ) * Complex.I) ∉ K := by
  classical
  intro x hx hk
  have b := hbox _ hk
  -- endpoints of the outside box do not meet K
  by_cases j0 : j = 0
  · subst j
    have : A < A := by simpa [meshCoord] using b.2.1
    exact (lt_irrefl _ this)
  by_cases jN : j = N
  · subst j
    have : meshCoord A s N < meshCoord A s N := by simpa using b.2.2
    exact (lt_irrefl _ this)
  have jp : 0 < j := (Nat.pos_iff_ne_zero.mpr j0)
  have jl : j < N := by
    -- coordinate of a K point precludes j>N
    have coord : meshCoord A s j < meshCoord A s N := by simpa using b.2.2
    by_contra h
    have ge : N ≤ j := Nat.le_of_not_gt h
    have mono : meshCoord A s N ≤ meshCoord A s j := by
      dsimp [meshCoord]
      simpa [add_comm] using (add_le_add_left (mul_le_mul_of_nonneg_right (by exact_mod_cast ge : (N:ℝ) ≤ (j:ℝ)) hs) A)
    exact (not_le_of_gt coord) mono
  have two := mesh_horizontal_two_hits K (A:=A) (s:=s) (i:=i) (j:=j)
      hs jp hx.1 (by simpa [meshCoord_succ] using hx.2) hk
  have zz : hcoef (meshHit K A s) N i j = 0 := by
    dsimp [hcoef]
    simp [jl, jp, meshHit, two.1, two.2]
  exact hn zz

lemma vcoef_edge_avoids (K : Set ℂ) (A s : ℝ) (N i j : ℕ) (hs : 0 ≤ s)
    (hbox : ∀ z ∈ K, z.re ∈ Set.Ioo A (meshCoord A s N) ∧
                       z.im ∈ Set.Ioo A (meshCoord A s N))
    (hn : vcoef (meshHit K A s) N i j ≠ 0) :
    ∀ y ∈ Set.Icc (meshCoord A s j) (meshCoord A s (j+1)),
      ((meshCoord A s i : ℂ) + (y:ℂ) * Complex.I) ∉ K := by
  classical
  intro y hy hk
  have b := hbox _ hk
  by_cases i0 : i = 0
  · subst i
    have : A < A := by simpa [meshCoord] using b.1.1
    exact (lt_irrefl _ this)
  by_cases iN : i = N
  · subst i
    have : meshCoord A s N < meshCoord A s N := by simpa using b.1.2
    exact (lt_irrefl _ this)
  have ip : 0 < i := Nat.pos_iff_ne_zero.mpr i0
  have il : i < N := by
    have coord : meshCoord A s i < meshCoord A s N := by simpa using b.1.2
    by_contra h
    have ge : N ≤ i := Nat.le_of_not_gt h
    have mono : meshCoord A s N ≤ meshCoord A s i := by
      dsimp [meshCoord]
      simpa [add_comm] using (add_le_add_left (mul_le_mul_of_nonneg_right (by exact_mod_cast ge : (N:ℝ) ≤ (i:ℝ)) hs) A)
    exact (not_le_of_gt coord) mono
  have two := mesh_vertical_two_hits K (A:=A) (s:=s) (i:=i) (j:=j)
      hs ip (by exact hy.1) (by simpa [meshCoord_succ] using hy.2) hk
  have zz : vcoef (meshHit K A s) N i j = 0 := by
    dsimp [vcoef]
    simp [il, ip, meshHit, two.1, two.2]
  exact hn zz
end RungeSupport

namespace RungeSupport
attribute [local instance] Classical.propDecidable Classical.decEq
open Set MeasureTheory intervalIntegral

lemma not_mem_meshSquare_of_strict_indices {A s : ℝ} (hs : 0 < s)
    {z : ℂ} {i₀ j₀ i j : ℕ}
    (hzx : z.re ∈ Set.Ioo (meshCoord A s i₀) (meshCoord A s (i₀+1)))
    (hzy : z.im ∈ Set.Ioo (meshCoord A s j₀) (meshCoord A s (j₀+1)))
    (hneq : (i,j) ≠ (i₀,j₀)) :
    z ∉ (Set.uIcc (meshCoord A s i) (meshCoord A s (i+1)) ×ℂ
           Set.uIcc (meshCoord A s j) (meshCoord A s (j+1))) := by
  intro hz
  have zi := (Complex.mem_reProdIm).1 hz
  have mono := meshCoord_strictMono A hs
  have mnon : Monotone (meshCoord A s) := mono.monotone
  have ordx : meshCoord A s i ≤ meshCoord A s (i+1) :=
    mnon (Nat.le_add_right _ _)
  have ordy : meshCoord A s j ≤ meshCoord A s (j+1) :=
    mnon (Nat.le_add_right _ _)
  rw [Set.uIcc_of_le ordx] at zi
  rw [Set.uIcc_of_le ordy] at zi
  by_cases eqi : i = i₀
  · have nej : j ≠ j₀ := by intro h; exact hneq (by simp [eqi,h])
    rcases lt_or_gt_of_ne nej with lt | gt
    · have bound : j+1 ≤ j₀ := by omega
      have mm := mnon bound
      exact (not_le_of_gt hzy.1) (le_trans zi.2.2 mm)
    · have bound : j₀+1 ≤ j := by omega
      have mm := mnon bound
      exact (not_le_of_gt hzy.2) (le_trans mm zi.2.1)
  · rcases lt_or_gt_of_ne eqi with lt | gt
    · have bound : i+1 ≤ i₀ := by omega
      have mm := mnon bound
      exact (not_le_of_gt hzx.1) (le_trans zi.1.2 mm)
    · have bound : i₀+1 ≤ i := by omega
      have mm := mnon bound
      exact (not_le_of_gt hzx.2) (le_trans mm zi.1.1)

/-- Off the grid all closed-cell kernels other than the unique containing cell
are holomorphic, so their rectangle integrals vanish. This isolates the only
geometric use of Cauchy's formula before the boundary limit. -/
lemma cellsum_cauchy_offgrid
    (A s : ℝ) (N : ℕ) (hs : 0 < s)
    (P : ℕ → ℕ → Prop) (f : ℂ → ℂ)
    (hf : ∀ {i j : ℕ}, i < N → j < N → P i j →
      ∀ w ∈ meshSquare A s i j, DifferentiableAt ℂ f w)
    {z : ℂ} {i₀ j₀ : ℕ} (hi₀ : i₀ < N) (hj₀ : j₀ < N)
    (hzx : z.re ∈ Set.Ioo (meshCoord A s i₀) (meshCoord A s (i₀+1)))
    (hzy : z.im ∈ Set.Ioo (meshCoord A s j₀) (meshCoord A s (j₀+1)))
    (hP : P i₀ j₀) :
    cellsum A s N P (fun w : ℂ => f w / (w-z)) =
      f z * (2*Real.pi*Complex.I) := by
  classical
  dsimp [cellsum]
  have hzmem : z ∈ meshSquare A s i₀ j₀ := by
    apply (mem_meshSquare).2
    rw [meshCoord_succ] at hzx hzy
    exact ⟨le_of_lt hzx.1, le_of_lt hzx.2,
      le_of_lt hzy.1, le_of_lt hzy.2⟩
  have hzat : DifferentiableAt ℂ f z := hf hi₀ hj₀ hP z hzmem
  have term (i j : ℕ) (hi : i < N) (hj : j < N) :
      (if P i j then
        rectInt (fun w : ℂ => f w / (w-z))
          (meshCoord A s i) (meshCoord A s (i+1))
          (meshCoord A s j) (meshCoord A s (j+1)) else 0)
       = if i = i₀ ∧ j = j₀ then f z * (2*Real.pi*Complex.I) else 0 := by
    by_cases eq : i = i₀ ∧ j = j₀
    · rcases eq with ⟨rfl,rfl⟩
      simp [hP]
      apply rectInt_cauchy_interior f z _ _ _ _
          hzx.1 hzx.2 hzy.1 hzy.2 hzat
      intro w hw
      apply hf hi₀ hj₀ hP w
      -- ordered square agrees with uIcc
      
      have ox : meshCoord A s i ≤ meshCoord A s (i+1) := by rw [meshCoord_succ]; linarith
      have oy : meshCoord A s j ≤ meshCoord A s (j+1) := by rw [meshCoord_succ]; linarith
      simpa [meshSquare, Set.uIcc_of_le ox, Set.uIcc_of_le oy] using hw
    · have nez : z ∉ (Set.uIcc (meshCoord A s i) (meshCoord A s (i+1)) ×ℂ
           Set.uIcc (meshCoord A s j) (meshCoord A s (j+1))) :=
        not_mem_meshSquare_of_strict_indices hs hzx hzy (by
          intro e; apply eq; exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩)
      simp only [if_neg eq]
      by_cases hp : P i j
      · simp only [hp, ↓reduceIte]
        apply rectInt_eq_zero_of_differentiableOn
        intro w hw
        have ox : meshCoord A s i ≤ meshCoord A s (i+1) := by rw [meshCoord_succ]; linarith
        have oy : meshCoord A s j ≤ meshCoord A s (j+1) := by rw [meshCoord_succ]; linarith
        have fw := hf hi hj hp w (by simpa [meshSquare, Set.uIcc_of_le ox, Set.uIcc_of_le oy] using hw)
        have wz : w - z ≠ 0 := by
          intro e; apply nez
          have wz' : w = z := sub_eq_zero.mp e
          simpa [wz'] using hw
        exact (fw.div (differentiableAt_id.sub_const z) wz).differentiableWithinAt
      · simp [hp]
  -- sum the terms; exactly one row and column survives
  have each :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      (if i = i₀ ∧ j = j₀ then f z * (2*Real.pi*Complex.I) else 0)) =
      f z * (2*Real.pi*Complex.I) := by
    classical
    -- simp sums with a single support
    calc
      _ = ∑ i ∈ Finset.range N,
          (if i = i₀ then f z * (2*Real.pi*Complex.I) else 0) := ?_
      _ = _ := by
        -- one i survives
        simp [Finset.sum_ite_irrel, hi₀]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : i = i₀
    · subst i
      simp [Finset.sum_ite_irrel, hj₀]
    · simp [h]
  calc
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      (if P i j then
        rectInt (fun w : ℂ => f w / (w-z))
          (meshCoord A s i) (meshCoord A s (i+1))
          (meshCoord A s j) (meshCoord A s (j+1)) else 0)) =
      (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        (if i = i₀ ∧ j = j₀ then f z * (2*Real.pi*Complex.I) else 0)) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          exact term i j (Finset.mem_range.1 hi) (Finset.mem_range.1 hj)
    _ = _ := each

end RungeSupport

namespace RungeSupport
open Set MeasureTheory intervalIntegral
open scoped BigOperators Interval Real
noncomputable section

def hpath (A s : ℝ) (i j : ℕ) (t : ℝ) : ℂ :=
  ((meshCoord A s i + s*t : ℝ) : ℂ) + (meshCoord A s j : ℂ) * Complex.I
def vpath (A s : ℝ) (i j : ℕ) (t : ℝ) : ℂ :=
  (meshCoord A s i : ℂ) + ((meshCoord A s j + s*t : ℝ) : ℂ) * Complex.I

lemma continuous_hpath (A s : ℝ) (i j : ℕ) : Continuous (hpath A s i j) := by
  unfold hpath
  fun_prop
lemma continuous_vpath (A s : ℝ) (i j : ℕ) : Continuous (vpath A s i j) := by
  unfold vpath
  fun_prop

lemma hpath_range (A s : ℝ) (hs : 0 ≤ s) (i j : ℕ)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    meshCoord A s i ≤ (meshCoord A s i + s*t) ∧
     meshCoord A s i + s*t ≤ meshCoord A s (i+1) := by
  rw [meshCoord_succ]
  constructor
  · nlinarith [ht.1]
  · nlinarith [ht.2]
lemma vpath_range (A s : ℝ) (hs : 0 ≤ s) (i j : ℕ)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    meshCoord A s j ≤ (meshCoord A s j + s*t) ∧
     meshCoord A s j + s*t ≤ meshCoord A s (j+1) := by
  rw [meshCoord_succ]
  constructor <;> nlinarith [ht.1, ht.2]

/-- Real affine change of variables for a horizontal mesh side. There is no
regularity assumption on the integrand. -/
lemma hedge_change (A s : ℝ) (i j : ℕ) (G : ℂ → ℂ) :
    (s:ℂ) * (∫ t : ℝ in (0:ℝ)..1, G (hpath A s i j t)) =
      hedge A s G i j := by
  let g : ℝ → ℂ := fun x => G ((x:ℂ) + (meshCoord A s j : ℂ)*Complex.I)
  have h := intervalIntegral.smul_integral_comp_add_mul g s (meshCoord A s i)
      (a:= (0:ℝ)) (b:= (1:ℝ))
  -- convert real smul into multiplication in ℂ
  have ha : meshCoord A s i + s * (0:ℝ) = meshCoord A s i := by ring
  have hb : meshCoord A s i + s * (1:ℝ) = meshCoord A s (i+1) := by
    rw [meshCoord_succ]; ring
  -- same path after unfolding
  simpa [g, hpath, hedge, ha, hb, meshCoord_succ, mul_comm] using h

lemma vedge_change (A s : ℝ) (i j : ℕ) (G : ℂ → ℂ) :
    (s:ℂ) * (∫ t : ℝ in (0:ℝ)..1, G (vpath A s i j t)) =
      vedge A s G i j := by
  let g : ℝ → ℂ := fun y => G ((meshCoord A s i:ℂ) + (y:ℂ)*Complex.I)
  have h := intervalIntegral.smul_integral_comp_add_mul g s (meshCoord A s j)
      (a:= (0:ℝ)) (b:= (1:ℝ))
  have ha : meshCoord A s j + s * (0:ℝ) = meshCoord A s j := by ring
  have hb : meshCoord A s j + s * (1:ℝ) = meshCoord A s (j+1) := by
    rw [meshCoord_succ]; ring
  simpa [g, vpath, vedge, ha, hb, meshCoord_succ, mul_comm] using h
end
end RungeSupport
namespace RungeSupport
open Set MeasureTheory intervalIntegral
open scoped BigOperators Interval Real
noncomputable section
/-- A retained horizontal side, after affine parameterization, contributes
its coefficient times the usual Cauchy kernel. `cauchyDen` need not be nonzero
for this change-of-variable identity. -/
lemma horizontal_kernel_change (A s : ℝ) (i j : ℕ)
    (k cauchyDen : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    (∫ t : ℝ in (0:ℝ)..1,
       ((-(k*(s:ℂ))/cauchyDen) * f (hpath A s i j t)) /
          (z - hpath A s i j t)) =
      (k/cauchyDen) *
        hedge A s (fun w : ℂ => f w / (w-z)) i j := by
  let D : ℂ → ℂ := fun w => f w / (w-z)
  have point (w : ℂ) :
      ((-(k*(s:ℂ))/cauchyDen) * f w) / (z-w)
        = (k/cauchyDen) * (s:ℂ) * D w := by
    dsimp [D]
    rw [show z-w = -(w-z) by ring]
    simp only [div_eq_mul_inv, inv_neg]
    ring
  have eqint :
      (∫ t : ℝ in (0:ℝ)..1,
       ((-(k*(s:ℂ))/cauchyDen) * f (hpath A s i j t)) /
          (z - hpath A s i j t)) =
      ∫ t : ℝ in (0:ℝ)..1,
        ((k/cauchyDen) * (s:ℂ)) * D (hpath A s i j t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    simpa [mul_assoc] using point (hpath A s i j t)
  rw [eqint]
  rw [intervalIntegral.integral_const_mul]
  have ch := hedge_change A s i j D
  rw [← ch]
  ring

lemma vertical_kernel_change (A s : ℝ) (i j : ℕ)
    (k cauchyDen : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    (∫ t : ℝ in (0:ℝ)..1,
       ((-(k*(s:ℂ))/cauchyDen) * f (vpath A s i j t)) /
          (z - vpath A s i j t)) =
      (k/cauchyDen) *
        vedge A s (fun w : ℂ => f w / (w-z)) i j := by
  let D : ℂ → ℂ := fun w => f w / (w-z)
  have point (w : ℂ) :
      ((-(k*(s:ℂ))/cauchyDen) * f w) / (z-w)
        = (k/cauchyDen) * (s:ℂ) * D w := by
    dsimp [D]
    rw [show z-w = -(w-z) by ring]
    simp only [div_eq_mul_inv, inv_neg]
    ring
  have eqint :
      (∫ t : ℝ in (0:ℝ)..1,
       ((-(k*(s:ℂ))/cauchyDen) * f (vpath A s i j t)) /
          (z - vpath A s i j t)) =
      ∫ t : ℝ in (0:ℝ)..1,
        ((k/cauchyDen) * (s:ℂ)) * D (vpath A s i j t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    simpa [mul_assoc] using point (vpath A s i j t)
  rw [eqint]
  rw [intervalIntegral.integral_const_mul]
  have ch := vedge_change A s i j D
  rw [← ch]
  ring
end
end RungeSupport

end

-- END INLINED FILE: Mathlib/Support/runge_theorem_ac7707d823/Boundary.lean

-- BEGIN INLINED FILE: Mathlib/Support/runge_theorem_ac7707d823/Finish.lean
open scoped Topology
open Set MeasureTheory intervalIntegral
open scoped BigOperators Interval Real
noncomputable section
namespace RungeSupport

/-- an elementary continuity lemma for Cauchy kernels on a compact real arc. -/
lemma continuousAt_interval_kernel (a b : ℝ) (u v : ℝ → ℂ) (z₀ : ℂ)
    (hu : ContinuousOn u (Set.uIcc a b))
    (hv : ContinuousOn v (Set.uIcc a b))
    (hz : ∀ t ∈ Set.uIcc a b, v t ≠ z₀) :
    ContinuousAt (fun z : ℂ => ∫ t : ℝ in a..b, u t / (v t - z)) z₀ := by
  classical
  let T : Set ℂ := v '' (Set.uIcc a b)
  have hTc : IsCompact T := by
    dsimp [T]
    exact isCompact_uIcc.image_of_continuousOn hv
  have hTn : T.Nonempty := by
    refine ⟨v a, ?_⟩
    exact ⟨a, Set.left_mem_uIcc, rfl⟩
  have hzT : z₀ ∉ T := by
    intro h
    rcases h with ⟨t, ht, htv⟩
    exact hz t ht (by simpa using htv)
  let r : ℝ := Metric.infDist z₀ T
  have hr : 0 < r := by
    dsimp [r]
    exact (hTc.isClosed.notMem_iff_infDist_pos hTn).1 hzT
  obtain ⟨C, hC⟩ := bddAbove_def.mp
      (isCompact_uIcc.bddAbove_image hu.norm)
  have hCu (t : ℝ) (ht : t ∈ Set.uIcc a b) : ‖u t‖ ≤ C :=
    hC _ ⟨t, ht, rfl⟩
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hCu a Set.left_mem_uIcc)
  have near_den {z : ℂ} (hz' : z ∈ Metric.ball z₀ (r/2))
      {t : ℝ} (ht : t ∈ Set.uIcc a b) : r/2 ≤ ‖v t - z‖ := by
    have d0 : r ≤ dist z₀ (v t) := by
      dsimp [r]
      exact Metric.infDist_le_dist_of_mem (show v t ∈ T from ⟨t, ht, rfl⟩)
    have dz : dist z z₀ < r/2 := Metric.mem_ball.mp hz'
    have tri : dist z₀ (v t) ≤ dist z₀ z + dist z (v t) := dist_triangle _ _ _
    simp only [Complex.dist_eq] at d0 dz tri
    rw [norm_sub_rev z (v t)] at tri
    -- convert the middle norm to distance commutation
    have dz' : ‖z₀ - z‖ < r/2 := by
      simpa [Complex.dist_eq, norm_sub_rev] using dz
    linarith
  -- apply dominated-continuity to the interval integral
  refine intervalIntegral.continuousAt_of_dominated_interval (μ := MeasureTheory.volume)
    (F := fun z t => u t / (v t - z)) (bound := fun _ : ℝ => C / (r/2))
    (a := a) (b := b) ?_ ?_ (intervalIntegral.intervalIntegrable_const) ?_
  · filter_upwards [Metric.ball_mem_nhds z₀ (by linarith : 0 < r/2)] with z hzball
    have hn (t : ℝ) (ht : t ∈ Set.uIcc a b) : v t - z ≠ 0 := by
      have hden := near_den hzball ht
      have pos : 0 < ‖v t - z‖ := lt_of_lt_of_le (by linarith : 0 < r/2) hden
      exact sub_ne_zero.mpr (by
        intro e
        have : ‖v t - z‖ = 0 := by rw [e, sub_self, norm_zero]
        linarith)
    have hco : ContinuousOn (fun t => u t / (v t - z)) (Set.uIcc a b) := by
      have hsub : ContinuousOn (fun t => v t - z) (Set.uIcc a b) :=
        hv.sub continuousOn_const
      exact hu.div hsub hn
    exact (hco.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [Metric.ball_mem_nhds z₀ (by linarith : 0 < r/2)] with z hzball
    filter_upwards [] with t ht
    have ht' : t ∈ Set.uIcc a b := Set.uIoc_subset_uIcc ht
    rw [norm_div]
    exact div_le_div₀ hC0 (hCu t ht') (by linarith : 0 < r/2)
      (near_den hzball ht')
  · filter_upwards [] with t ht
    have ht' : t ∈ Set.uIcc a b := Set.uIoc_subset_uIcc ht
    have hne : v t - z₀ ≠ 0 := sub_ne_zero.mpr (hz t ht')
    fun_prop

end RungeSupport
namespace RungeSupport
open Filter
lemma eq_of_continuousAt_of_eq_on_rect (g h : ℂ → ℂ) (z : ℂ)
    (hg : ContinuousAt g z) (hh : ContinuousAt h z)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hx : z.re ∈ Set.Icc a b) (hy : z.im ∈ Set.Icc c d)
    (heq : ∀ w : ℂ, w.re ∈ Set.Ioo a b → w.im ∈ Set.Ioo c d → g w = h w) :
    g z = h z := by
  let xm : ℝ := (a+b)/2
  let ym : ℝ := (c+d)/2
  have hxm : xm ∈ Set.Ioo a b := by dsimp [xm]; constructor <;> linarith
  have hym : ym ∈ Set.Ioo c d := by dsimp [ym]; constructor <;> linarith
  let tt : ℕ → ℝ := fun n => 1 / ((n:ℝ)+1)
  have ht : Tendsto tt atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have htpos (n : ℕ) : 0 < tt n := by dsimp [tt]; positivity
  have htle (n : ℕ) : tt n ≤ 1 := by
    dsimp [tt]
    have h : (1:ℝ) ≤ (n:ℝ)+1 := by exact_mod_cast (Nat.le_add_left 1 n)
    exact (div_le_one₀ (by positivity)).2 h
  let xx : ℕ → ℝ := fun n => z.re + tt n * (xm - z.re)
  let yy : ℕ → ℝ := fun n => z.im + tt n * (ym - z.im)
  have hxx (n : ℕ) : xx n ∈ Set.Ioo a b := by
    dsimp [xx]
    have tp := htpos n
    have tl := htle n
    constructor
    · nlinarith [hx.1, hxm.1]
    · nlinarith [hx.2, hxm.2]
  have hyy (n : ℕ) : yy n ∈ Set.Ioo c d := by
    dsimp [yy]
    have tp := htpos n
    have tl := htle n
    constructor
    · nlinarith [hy.1, hym.1]
    · nlinarith [hy.2, hym.2]
  let zz : ℕ → ℂ := fun n => (xx n : ℂ) + (yy n : ℂ) * Complex.I
  have zz_re (n) : (zz n).re = xx n := by simp [zz]
  have zz_im (n) : (zz n).im = yy n := by simp [zz]
  have tx : Tendsto xx atTop (𝓝 z.re) := by
    dsimp [xx]
    convert tendsto_const_nhds.add (ht.mul_const (xm - z.re)) using 1 <;> simp
  have ty : Tendsto yy atTop (𝓝 z.im) := by
    dsimp [yy]
    convert tendsto_const_nhds.add (ht.mul_const (ym - z.im)) using 1 <;> simp
  have tz : Tendsto zz atTop (𝓝 z) := by
    have tx' : Tendsto (fun n => (xx n : ℂ)) atTop (𝓝 (z.re : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp tx
    have ty' : Tendsto (fun n => (yy n : ℂ)) atTop (𝓝 (z.im : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp ty
    have tadd := tx'.add (ty'.mul_const Complex.I)
    have hzext : (z.re : ℂ) + (z.im : ℂ) * Complex.I = z := by
      apply Complex.ext <;> simp
    simpa [zz, hzext] using tadd
  have eqn : ∀ n, g (zz n) = h (zz n) := by
    intro n
    apply heq
    · simpa [zz_re] using hxx n
    · simpa [zz_im] using hyy n
  have tg : Tendsto (fun n => g (zz n)) atTop (𝓝 (g z)) := hg.tendsto.comp tz
  have th : Tendsto (fun n => h (zz n)) atTop (𝓝 (h z)) := hh.tendsto.comp tz
  have ee : (fun n => g (zz n)) = (fun n => h (zz n)) := funext eqn
  rw [ee] at tg
  exact tendsto_nhds_unique tg th
end RungeSupport
namespace RungeSupport
lemma exists_fin_contours_of_fintype {ι : Type*} [Fintype ι]
    (K : Set ℂ) (f : ℂ → ℂ) (c γ : ι → ℝ → ℂ)
    (hc : ∀ j, ContinuousOn (c j) (Set.Icc (0:ℝ) 1))
    (hγ : ∀ j, ContinuousOn (γ j) (Set.Icc (0:ℝ) 1))
    (hout : ∀ j t, t ∈ Set.Icc (0:ℝ) 1 → γ j t ∉ K)
    (hrep : ∀ z ∈ K, f z = ∑ j : ι, (∫ t : ℝ in (0:ℝ)..1, c j t / (z - γ j t))) :
    ∃ m : ℕ, ∃ c' γ' : Fin m → ℝ → ℂ,
          (∀ j, ContinuousOn (c' j) (Set.Icc (0:ℝ) 1)) ∧
          (∀ j, ContinuousOn (γ' j) (Set.Icc (0:ℝ) 1)) ∧
          (∀ j t, t ∈ Set.Icc (0:ℝ) 1 → γ' j t ∉ K) ∧
          ∀ z ∈ K, f z = ∑ j : Fin m, (∫ t : ℝ in (0:ℝ)..1, c' j t / (z - γ' j t)) := by
  classical
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun j => c (e.symm j), fun j => γ (e.symm j),
      (fun j => hc _), (fun j => hγ _), (fun j t ht => hout _ t ht), ?_⟩
  intro z hz
  rw [hrep z hz]
  exact Fintype.sum_equiv e _ _ (by intro i; simp)
end RungeSupport

end

-- END INLINED FILE: Mathlib/Support/runge_theorem_ac7707d823/Finish.lean

-- BEGIN INLINED FILE: Mathlib/Support/runge_theorem_ac7707d823/Package.lean
open scoped BigOperators Interval Real
open Set MeasureTheory intervalIntegral
noncomputable section
namespace RungeSupport

abbrev EdgeIndex (N : ℕ) := (Fin N × Fin (N+1)) ⊕ (Fin (N+1) × Fin N)

def edgeCoeff (P : ℕ → ℕ → Prop) (N : ℕ) (u : EdgeIndex N) : ℂ :=
  match u with
  | Sum.inl ij => hcoef P N ij.1 ij.2
  | Sum.inr ij => vcoef P N ij.1 ij.2

abbrev ActiveEdge (P : ℕ → ℕ → Prop) (N : ℕ) :=
  {u : EdgeIndex N // edgeCoeff P N u ≠ 0}

def edgeWeight (P : ℕ → ℕ → Prop) (N : ℕ) (u : EdgeIndex N) : ℂ :=
  match u with
  | Sum.inl ij => hcoef P N ij.1 ij.2
  | Sum.inr ij => Complex.I * vcoef P N ij.1 ij.2

def edgePath (A s : ℝ) {N : ℕ} (u : EdgeIndex N) (t : ℝ) : ℂ :=
  match u with
  | Sum.inl ij => hpath A s ij.1 ij.2 t
  | Sum.inr ij => vpath A s ij.1 ij.2 t

def cDen : ℂ := (2:ℂ) * (Real.pi:ℂ) * Complex.I

-- A nonzero horizontal coefficient has a neighbouring retained cell.
lemma hcoef_adj {P : ℕ → ℕ → Prop} {N i j : ℕ}
    (hn : hcoef P N i j ≠ 0) :
    (j < N ∧ P i j) ∨ (0 < j ∧ P i (j-1)) := by
  classical
  by_contra H
  have h1 : ¬(j < N ∧ P i j) := by tauto
  have h2 : ¬(0 < j ∧ P i (j-1)) := by tauto
  exact hn (by simp [hcoef, h1, h2])

lemma vcoef_adj {P : ℕ → ℕ → Prop} {N i j : ℕ}
    (hn : vcoef P N i j ≠ 0) :
    (0 < i ∧ P (i-1) j) ∨ (i < N ∧ P i j) := by
  classical
  by_contra H
  have h1 : ¬(0 < i ∧ P (i-1) j) := by tauto
  have h2 : ¬(i < N ∧ P i j) := by tauto
  exact hn (by simp [vcoef, h1, h2])

/-- continuity of f on a horizontal live edge, inherited from a neighbouring cell. -/
lemma continuousOn_hpath_comp_of_live
    {A s : ℝ} {N : ℕ} (hs : 0 < s)
    {P : ℕ → ℕ → Prop} {f : ℂ → ℂ}
    (hf : ∀ {i j : ℕ}, i < N → j < N → P i j →
        ∀ w ∈ meshSquare A s i j, DifferentiableAt ℂ f w)
    {i j : ℕ} (hi : i < N) (hj : j < N+1)
    (hn : hcoef P N i j ≠ 0) :
    ContinuousOn (fun t : ℝ => f (hpath A s i j t)) (Set.Icc (0:ℝ) 1) := by
  classical
  -- use full continuity at every parameter: f is differentiable on an adjacent retained square
  apply continuousOn_of_forall_continuousAt
  intro t ht
  have tr := hpath_range A s (le_of_lt hs) i j ht
  rcases hcoef_adj hn with low | up
  · -- cell just above the edge, row j
    have hm : hpath A s i j t ∈ meshSquare A s i j := by
      apply (mem_meshSquare).2
      have H : meshCoord A s i ≤ meshCoord A s i + s*t ∧
          meshCoord A s i + s*t ≤ meshCoord A s i + s ∧
          meshCoord A s j ≤ meshCoord A s j ∧
          meshCoord A s j ≤ meshCoord A s j + s := by
        constructor
        · exact tr.1
        constructor
        · rw [← meshCoord_succ]
          exact tr.2
        constructor
        · rfl
        · linarith
      simpa [hpath] using H
    have fw := hf hi low.1 low.2 (hpath A s i j t) hm
    exact fw.continuousAt.comp_of_eq (continuous_hpath A s i j).continuousAt (by rfl)
  · -- cell below: row j-1 ends exactly at this edge
    have jp : 0 < j := up.1
    have jl : j-1 < N := by omega
    have jeq : j-1+1 = j := by omega
    have basej : meshCoord A s (j-1) + s = meshCoord A s j := by
      rw [← meshCoord_succ, jeq]
    have hm : hpath A s i j t ∈ meshSquare A s i (j-1) := by
      apply (mem_meshSquare).2
      have H : meshCoord A s i ≤ meshCoord A s i + s*t ∧
          meshCoord A s i + s*t ≤ meshCoord A s i + s ∧
          meshCoord A s (j-1) ≤ meshCoord A s j ∧
          meshCoord A s j ≤ meshCoord A s (j-1) + s := by
        constructor
        · exact tr.1
        constructor
        · rw [← meshCoord_succ]
          exact tr.2
        constructor
        · linarith [basej, hs]
        · exact le_of_eq basej.symm
      simpa [hpath] using H
    have fw := hf hi jl up.2 (hpath A s i j t) hm
    exact fw.continuousAt.comp_of_eq (continuous_hpath A s i j).continuousAt (by rfl)

lemma continuousOn_vpath_comp_of_live
    {A s : ℝ} {N : ℕ} (hs : 0 < s)
    {P : ℕ → ℕ → Prop} {f : ℂ → ℂ}
    (hf : ∀ {i j : ℕ}, i < N → j < N → P i j →
        ∀ w ∈ meshSquare A s i j, DifferentiableAt ℂ f w)
    {i j : ℕ} (hi : i < N+1) (hj : j < N)
    (hn : vcoef P N i j ≠ 0) :
    ContinuousOn (fun t : ℝ => f (vpath A s i j t)) (Set.Icc (0:ℝ) 1) := by
  classical
  apply continuousOn_of_forall_continuousAt
  intro t ht
  have tr := vpath_range A s (le_of_lt hs) i j ht
  rcases vcoef_adj hn with left | right
  · have ip : 0 < i := left.1
    have il : i-1 < N := by omega
    have ieq : i-1+1 = i := by omega
    have basei : meshCoord A s (i-1) + s = meshCoord A s i := by
      rw [← meshCoord_succ, ieq]
    have hm : vpath A s i j t ∈ meshSquare A s (i-1) j := by
      apply (mem_meshSquare).2
      have H : meshCoord A s (i-1) ≤ meshCoord A s i ∧
          meshCoord A s i ≤ meshCoord A s (i-1) + s ∧
          meshCoord A s j ≤ meshCoord A s j + s*t ∧
          meshCoord A s j + s*t ≤ meshCoord A s j + s := by
        constructor
        · linarith [basei, hs]
        constructor
        · exact le_of_eq basei.symm
        constructor
        · exact tr.1
        · rw [← meshCoord_succ]
          exact tr.2
      simpa [vpath] using H
    have fw := hf il hj left.2 (vpath A s i j t) hm
    exact fw.continuousAt.comp_of_eq (continuous_vpath A s i j).continuousAt (by rfl)
  · have il : i < N := right.1
    have hm : vpath A s i j t ∈ meshSquare A s i j := by
      apply (mem_meshSquare).2
      have H : meshCoord A s i ≤ meshCoord A s i ∧
          meshCoord A s i ≤ meshCoord A s i + s ∧
          meshCoord A s j ≤ meshCoord A s j + s*t ∧
          meshCoord A s j + s*t ≤ meshCoord A s j + s := by
        constructor
        · rfl
        constructor
        · linarith
        constructor
        · exact tr.1
        · rw [← meshCoord_succ]
          exact tr.2
      simpa [vpath] using H
    have fw := hf il hj right.2 (vpath A s i j t) hm
    exact fw.continuousAt.comp_of_eq (continuous_vpath A s i j).continuousAt (by rfl)

end RungeSupport

namespace RungeSupport
lemma cDen_ne_zero : cDen ≠ 0 := by
  dsimp [cDen]
  exact mul_ne_zero (mul_ne_zero (by norm_num)
    ((Complex.ofReal_ne_zero).2 Real.pi_ne_zero)) Complex.I_ne_zero
end RungeSupport

namespace RungeSupport
lemma exists_mesh_contours
    (K : Set ℂ) (A s : ℝ) (N : ℕ) (P : ℕ → ℕ → Prop) (f : ℂ → ℂ)
    (hs : 0 < s)
    (hf : ∀ {i j : ℕ}, i < N → j < N → P i j →
        ∀ w ∈ meshSquare A s i j, DifferentiableAt ℂ f w)
    (ha : ∀ {i j : ℕ}, i < N → j < N+1 → hcoef P N i j ≠ 0 →
        ∀ x ∈ Set.Icc (meshCoord A s i) (meshCoord A s (i+1)),
          ((x:ℂ) + (meshCoord A s j:ℂ)*Complex.I) ∉ K)
    (hb : ∀ {i j : ℕ}, i < N+1 → j < N → vcoef P N i j ≠ 0 →
        ∀ y ∈ Set.Icc (meshCoord A s j) (meshCoord A s (j+1)),
          ((meshCoord A s i:ℂ) + (y:ℂ)*Complex.I) ∉ K)
    (hall : ∀ z ∈ K,
       edgesum A s N P (fun w : ℂ => f w / (w-z)) = f z * cDen) :
    ∃ m : ℕ, ∃ c γ : Fin m → ℝ → ℂ,
          (∀ j, ContinuousOn (c j) (Set.Icc (0:ℝ) 1)) ∧
          (∀ j, ContinuousOn (γ j) (Set.Icc (0:ℝ) 1)) ∧
          (∀ j t, t ∈ Set.Icc (0:ℝ) 1 → γ j t ∉ K) ∧
          ∀ z ∈ K, f z = ∑ j : Fin m, (∫ t : ℝ in (0:ℝ)..1, c j t / (z - γ j t)) := by
 classical
 let gam : ActiveEdge P N → ℝ → ℂ := fun u => edgePath A s u.1
 let cc : ActiveEdge P N → ℝ → ℂ := fun u t =>
       (-(edgeWeight P N u.1 * (s:ℂ)) / cDen) * f (edgePath A s u.1 t)
 apply exists_fin_contours_of_fintype K f cc gam
 · intro u
   rcases u with ⟨u,hu⟩
   rcases u with ij | ij
   · rcases ij with ⟨i,j⟩
     change hcoef P N (i:ℕ) (j:ℕ) ≠ 0 at hu
     have H := continuousOn_hpath_comp_of_live hs hf i.isLt j.isLt hu
     exact H.const_mul _
   · rcases ij with ⟨i,j⟩
     change vcoef P N (i:ℕ) (j:ℕ) ≠ 0 at hu
     have H := continuousOn_vpath_comp_of_live hs hf i.isLt j.isLt hu
     exact H.const_mul _
 · intro u
   rcases u with ⟨u,hu⟩
   rcases u with ij | ij
   · rcases ij with ⟨i,j⟩
     exact (continuous_hpath A s i j).continuousOn
   · rcases ij with ⟨i,j⟩
     exact (continuous_vpath A s i j).continuousOn
 · intro u t ht
   rcases u with ⟨u,hu⟩
   rcases u with ij | ij
   · rcases ij with ⟨i,j⟩
     change hcoef P N (i:ℕ) (j:ℕ) ≠ 0 at hu
     have tr := hpath_range A s (le_of_lt hs) (i:ℕ) (j:ℕ) ht
     have av := ha i.isLt j.isLt hu (meshCoord A s i + s*t)
       (by exact ⟨tr.1, tr.2⟩)
     exact av
   · rcases ij with ⟨i,j⟩
     change vcoef P N (i:ℕ) (j:ℕ) ≠ 0 at hu
     have tr := vpath_range A s (le_of_lt hs) (i:ℕ) (j:ℕ) ht
     have av := hb i.isLt j.isLt hu (meshCoord A s j + s*t)
       (by exact ⟨tr.1, tr.2⟩)
     exact av
 · intro z hz
   let G : EdgeIndex N → ℂ := fun u =>
     match u with
     | Sum.inl ij =>
          (hcoef P N ij.1 ij.2 / cDen) *
            hedge A s (fun w : ℂ => f w / (w-z)) ij.1 ij.2
     | Sum.inr ij =>
          ((Complex.I * vcoef P N ij.1 ij.2) / cDen) *
            vedge A s (fun w : ℂ => f w / (w-z)) ij.1 ij.2
   have one (u : ActiveEdge P N) :
       (∫ t : ℝ in (0:ℝ)..1, cc u t / (z - gam u t)) = G u.1 := by
     rcases u with ⟨u,hu⟩
     rcases u with ij | ij
     · rcases ij with ⟨i,j⟩
       simpa [cc, gam, edgeWeight, edgePath, G] using
         (horizontal_kernel_change A s (i:ℕ) (j:ℕ)
           (hcoef P N (i:ℕ) (j:ℕ)) cDen f z)
     · rcases ij with ⟨i,j⟩
       simpa [cc, gam, edgeWeight, edgePath, G] using
         (vertical_kernel_change A s (i:ℕ) (j:ℕ)
           (Complex.I * vcoef P N (i:ℕ) (j:ℕ)) cDen f z)
   have sumone : (∑ u : ActiveEdge P N,
       (∫ t : ℝ in (0:ℝ)..1, cc u t / (z - gam u t))) =
       ∑ u : ActiveEdge P N, G u.1 := by
     apply Finset.sum_congr rfl
     intro u hu
     exact one u
   rw [sumone]
   -- prove equals f z with complement and edgesum
   have kill (u : {u : EdgeIndex N // ¬ edgeCoeff P N u ≠ 0}) :
       G u.1 = 0 := by
     rcases u with ⟨u, hu⟩
     rcases u with ij | ij
     · rcases ij with ⟨i,j⟩
       change ¬ hcoef P N (i:ℕ) (j:ℕ) ≠ 0 at hu
       have hzero : hcoef P N (i:ℕ) (j:ℕ) = 0 := not_ne_iff.mp hu
       simp [G, hzero]
     · rcases ij with ⟨i,j⟩
       change ¬ vcoef P N (i:ℕ) (j:ℕ) ≠ 0 at hu
       have hzero : vcoef P N (i:ℕ) (j:ℕ) = 0 := not_ne_iff.mp hu
       simp [G, hzero]
   have split : (∑ u : ActiveEdge P N, G u.1) =
        ∑ u : EdgeIndex N, G u := by
     have h := Fintype.sum_subtype_add_sum_subtype
       (fun u : EdgeIndex N => edgeCoeff P N u ≠ 0) G
     have zc : (∑ u : {u : EdgeIndex N // ¬ edgeCoeff P N u ≠ 0}, G u.1) = 0 := by
       simpa using (Finset.sum_eq_zero (s := Finset.univ)
          (fun u _ => kill u))
     rw [zc] at h
     simpa using h
   -- orientation now
   rw [split]
   -- try expand the two orientations over the rectangular ranges
   have expand : (∑ u : EdgeIndex N, G u) =
       ( (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range (N+1),
            hcoef P N i j * hedge A s (fun w : ℂ => f w / (w-z)) i j) / cDen) +
       ( (Complex.I * (∑ j ∈ Finset.range N, ∑ i ∈ Finset.range (N+1),
            vcoef P N i j * vedge A s (fun w : ℂ => f w / (w-z)) i j)) / cDen) := by
     classical
     -- first expand the sum type and the products of fins
     rw [Fintype.sum_sum_type]
     rw [Fintype.sum_prod_type]
     rw [Fintype.sum_prod_type]
     -- turn bounded fin sums into ranges
     -- distribute the common denominator through the finite sums
     simp [G, div_eq_mul_inv, ← Finset.sum_mul, ← Finset.mul_sum]
     simp_rw [← Fin.sum_univ_eq_sum_range]
     have shift (a b : ℂ) : a * cDen⁻¹ * b = (a*b) * cDen⁻¹ := by ring
     simp_rw [shift]
     simp [← Finset.sum_mul, ← Finset.mul_sum]
     left
     calc
       (∑ i : Fin (N+1), ∑ j : Fin N,
          Complex.I * vcoef P N (i:ℕ) (j:ℕ) *
             vedge A s (fun w : ℂ => f w * (w-z)⁻¹) (i:ℕ) (j:ℕ)) =
         ∑ j : Fin N, ∑ i : Fin (N+1),
          Complex.I * vcoef P N (i:ℕ) (j:ℕ) *
             vedge A s (fun w : ℂ => f w * (w-z)⁻¹) (i:ℕ) (j:ℕ) := by
                exact Finset.sum_comm
       _ = _ := by
          simp [Finset.mul_sum, mul_assoc]
   rw [expand]
   have hhall := hall z hz
   -- all terms are a common denominator; use the edge sum identity
   have eform :
       ((∑ i ∈ Finset.range N, ∑ j ∈ Finset.range (N+1),
            hcoef P N i j * hedge A s (fun w : ℂ => f w / (w-z)) i j) / cDen) +
       ((Complex.I * (∑ j ∈ Finset.range N, ∑ i ∈ Finset.range (N+1),
            vcoef P N i j * vedge A s (fun w : ℂ => f w / (w-z)) i j)) / cDen)
       = (edgesum A s N P (fun w : ℂ => f w / (w-z))) / cDen := by
         simp [edgesum]
         ring
   rw [eform]
   rw [hhall]
   apply (eq_div_iff cDen_ne_zero).2
   ring

end RungeSupport

end

-- END INLINED FILE: Mathlib/Support/runge_theorem_ac7707d823/Package.lean

namespace Submission

-- BEGIN INLINED FILE: Main.lean

open scoped Polynomial
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem runge (K : Set ℂ) (_hK : IsCompact K) (U : Set ℂ) (_hU : IsOpen U)
    (_hKU : K ⊆ U) (f : ℂ → ℂ) (_hf : AnalyticOnNhd ℂ f U)
    (ε : ℝ) (_hε : 0 < ε) :
    ∃ p q : ℂ[X], (∀ z ∈ K, q.eval z ≠ 0) ∧
      (∀ z ∈ K, ‖f z - p.eval z / q.eval z‖ < ε) :=
/-ResultProofBegin-/by
  classical
  by_cases h0 : K.Nonempty
  ·
    -- This is the geometric (Cauchy) part of the theorem. Everything after it
    -- is just uniform Riemann sums and a common denominator; see
    -- `RungeSupport.of_contour_representation`.
    have hchains :
        ∃ m : ℕ, ∃ c γ : Fin m → ℝ → ℂ,
          (∀ j, ContinuousOn (c j) (Set.Icc (0:ℝ) 1)) ∧
          (∀ j, ContinuousOn (γ j) (Set.Icc (0:ℝ) 1)) ∧
          (∀ j t, t ∈ Set.Icc (0:ℝ) 1 → γ j t ∉ K) ∧
          ∀ z ∈ K, f z =
            ∑ j : Fin m, (∫ t : ℝ in (0:ℝ)..1, c j t / (z - γ j t)) := by
      -- A compact collar keeps all the eventual small squares inside the
      -- domain of analyticity. Working on a closed collar is handy for both
      -- uniform continuity and finiteness of the grid.
      obtain ⟨d, hd, hband⟩ := _hK.exists_cthickening_subset_open _hU _hKU
      let L : Set ℂ := Metric.cthickening d K
      have hLc : IsCompact L := by
        dsimp [L]
        exact _hK.cthickening
      have hKin : K ⊆ L := by
        dsimp [L]
        exact Metric.self_subset_cthickening K
      have hLU : L ⊆ U := by simpa [L] using hband
      have hdiff : DifferentiableOn ℂ f L :=
        (_hf.mono hLU).differentiableOn
      have hcont : ContinuousOn f L := hdiff.continuousOn
      -- What remains is the geometric Cauchy lemma: tile a smaller collar
      -- by squares, sum Cauchy--Goursat on the squares, and keep the uncancelled
      -- boundary edges. Each such edge admits the parametrisation used below
      -- and misses `K`. The support lemmas compile all the later approximation
      -- and denominator steps, so this is the sole outstanding ingredient.
      -- choose once and for all a genuinely small finite box mesh.  A hit
      -- square is contained in the analytic collar; these facts are the
      -- local inputs to the remaining edge/cancellation argument.
      obtain ⟨A, s, N, hs, hsd, hbox⟩ :=
        RungeSupport.exists_small_mesh K _hK h0 d hd
      have hcell
          {i j : ℕ} (hi : i < N) (hj : j < N)
          (hit : (K ∩ RungeSupport.meshSquare A s i j).Nonempty) :
          ∀ w ∈ RungeSupport.meshSquare A s i j, DifferentiableAt ℂ f w := by
        intro w hw
        have hw' : w ∈ Metric.cthickening (2*s) K :=
          RungeSupport.meshSquare_subset_cthickening K (le_of_lt hs) hit hw
        have hwL : w ∈ L :=
          (Metric.cthickening_mono (le_of_lt hsd) K) hw'
        exact (_hf w (hLU hwL)).differentiableAt
      have hkAt (z : ℂ) (hzK : z ∈ K) : DifferentiableAt ℂ f z :=
        (_hf z (_hKU hzK)).differentiableAt
      -- On every hit square the divided difference has zero boundary
      -- integral, even for a point of K on a grid line.  `dslope` supplies
      -- the removable value there; this is the reason the later tiling has
      -- no degeneracy convention at vertices.
      have hremove (z : ℂ) (hzK : z ∈ K) {i j : ℕ}
          (hi : i < N) (hj : j < N)
          (hit : (K ∩ RungeSupport.meshSquare A s i j).Nonempty) :
          RungeSupport.rectInt (dslope f z)
            (RungeSupport.meshCoord A s i) (RungeSupport.meshCoord A s (i+1))
            (RungeSupport.meshCoord A s j) (RungeSupport.meshCoord A s (j+1)) = 0 := by
        apply RungeSupport.rectInt_dslope_zero f z
        · exact hkAt z hzK
        intro w hw
        apply hcell hi hj hit w
        -- the ordered endpoints of a mesh interval give exactly this cell
        have hsx : RungeSupport.meshCoord A s i ≤ RungeSupport.meshCoord A s (i+1) := by
          rw [RungeSupport.meshCoord_succ]; linarith
        have hsy : RungeSupport.meshCoord A s j ≤ RungeSupport.meshCoord A s (j+1) := by
          rw [RungeSupport.meshCoord_succ]; linarith
        rw [RungeSupport.meshSquare, Complex.mem_reProdIm]
        have hr := (Complex.mem_reProdIm).1 hw
        simpa [Set.uIcc_of_le hsx, Set.uIcc_of_le hsy] using hr
      -- Off grid lines the other local summand is precisely the one-square
      -- Cauchy formula.  The finite edge proof only has to keep the boundary
      -- edges of the hit squares and compute their winding; no local analytic
      -- step remains.
      have hone {i j : ℕ} (hi : i < N) (hj : j < N)
          (hit : (K ∩ RungeSupport.meshSquare A s i j).Nonempty)
          (z : ℂ) (hzK : z ∈ K)
          (hzr : z.re ∈ Set.Ioo (RungeSupport.meshCoord A s i)
                         (RungeSupport.meshCoord A s (i+1)))
          (hzi : z.im ∈ Set.Ioo (RungeSupport.meshCoord A s j)
                         (RungeSupport.meshCoord A s (j+1))) :
          RungeSupport.rectInt (fun w : ℂ => f w / (w-z))
            (RungeSupport.meshCoord A s i) (RungeSupport.meshCoord A s (i+1))
            (RungeSupport.meshCoord A s j) (RungeSupport.meshCoord A s (j+1)) =
              f z * (2*Real.pi*Complex.I) := by
        apply RungeSupport.rectInt_cauchy_interior f z _ _ _ _
            hzr.1 hzr.2 hzi.1 hzi.2 (hkAt z hzK)
        intro w hw
        apply hcell hi hj hit w
        have hsx : RungeSupport.meshCoord A s i ≤ RungeSupport.meshCoord A s (i+1) := by
          rw [RungeSupport.meshCoord_succ]; linarith
        have hsy : RungeSupport.meshCoord A s j ≤ RungeSupport.meshCoord A s (j+1) := by
          rw [RungeSupport.meshCoord_succ]; linarith
        rw [RungeSupport.meshSquare, Complex.mem_reProdIm]
        have hr := (Complex.mem_reProdIm).1 hw
        simpa [Set.uIcc_of_le hsx, Set.uIcc_of_le hsy] using hr
      -- Package the pure finite cancellation now.  `meshHit` marks the cells
      -- we kept.  Nonzero incidence coefficients are precisely closed edges
      -- of the union; even their endpoints miss K.  This is the useful
      -- combinatorial part of the remaining boundary argument.
      let P : ℕ → ℕ → Prop := RungeSupport.meshHit K A s
      have hcellP {i j : ℕ} (hi : i < N) (hj : j < N) (hp : P i j) :
          ∀ w ∈ RungeSupport.meshSquare A s i j,
            DifferentiableAt ℂ f w := by
        exact hcell hi hj (by simpa [P, RungeSupport.meshHit] using hp)
      have hhedge_away {i j : ℕ}
          (hn : RungeSupport.hcoef P N i j ≠ 0) :
          ∀ x ∈ Set.Icc (RungeSupport.meshCoord A s i)
                        (RungeSupport.meshCoord A s (i+1)),
            ((x:ℂ) + (RungeSupport.meshCoord A s j:ℂ)*Complex.I) ∉ K := by
        exact RungeSupport.hcoef_edge_avoids K A s N i j (le_of_lt hs)
          hbox (by simpa [P] using hn)
      have hvedge_away {i j : ℕ}
          (hn : RungeSupport.vcoef P N i j ≠ 0) :
          ∀ y ∈ Set.Icc (RungeSupport.meshCoord A s j)
                        (RungeSupport.meshCoord A s (j+1)),
            ((RungeSupport.meshCoord A s i:ℂ) + (y:ℂ)*Complex.I) ∉ K := by
        exact RungeSupport.vcoef_edge_avoids K A s N i j (le_of_lt hs)
          hbox (by simpa [P] using hn)
      have hcancel (F : ℂ → ℂ) :
          RungeSupport.cellsum A s N P F =
            RungeSupport.edgesum A s N P F :=
        RungeSupport.cellsum_eq_edgesum A s N P F
      -- Away from a lattice line there is exactly one square with a pole. All
      -- other summands vanish by Cauchy--Goursat; the unique one is `hone`.
      -- The lemma proves this directly from the local differentiability so it
      -- also applies to nearby points not lying in K.
      have hoffgrid {z : ℂ} {i j : ℕ} (hi : i < N) (hj : j < N)
          (hx : z.re ∈ Set.Ioo (RungeSupport.meshCoord A s i)
                           (RungeSupport.meshCoord A s (i+1)))
          (hy : z.im ∈ Set.Ioo (RungeSupport.meshCoord A s j)
                           (RungeSupport.meshCoord A s (j+1)))
          (hp : P i j) :
          RungeSupport.edgesum A s N P (fun w : ℂ => f w / (w-z)) =
            f z * (2*Real.pi*Complex.I) := by
        rw [← hcancel]
        exact RungeSupport.cellsum_cauchy_offgrid A s N hs P f
          (by intro i' j' hi' hj' h'; exact hcellP hi' hj' h')
          hi hj hx hy hp
      -- nonzero sides inherit continuity of f from an adjacent retained square.
      have hadj {i j : ℕ} (hn : RungeSupport.hcoef P N i j ≠ 0) :
          (j < N ∧ P i j) ∨ (0 < j ∧ P i (j-1)) := by
        by_contra H
        have h1 : ¬(j < N ∧ P i j) := by tauto
        have h2 : ¬(0 < j ∧ P i (j-1)) := by tauto
        exact hn (by simp [RungeSupport.hcoef, h1, h2])
      have vadj {i j : ℕ} (hn : RungeSupport.vcoef P N i j ≠ 0) :
          (0 < i ∧ P (i-1) j) ∨ (i < N ∧ P i j) := by
        by_contra H
        have h1 : ¬(0 < i ∧ P (i-1) j) := by tauto
        have h2 : ¬(i < N ∧ P i j) := by tauto
        exact hn (by simp [RungeSupport.vcoef, h1, h2])
      -- The unweighted edge kernels are continuous at every point of K; the
      -- dominated interval lemma isolates precisely the small topological step
      -- needed to pass from open cells to their faces.
      have hHcont (z : ℂ) (hz : z ∈ K) {i j : ℕ}
          (hi : i < N) (hj : j < N+1)
          (hn : RungeSupport.hcoef P N i j ≠ 0) :
          ContinuousAt (fun q : ℂ =>
            RungeSupport.hedge A s (fun w : ℂ => f w / (w-q)) i j) z := by
        let pt : ℝ → ℂ := fun x => (x:ℂ) + (RungeSupport.meshCoord A s j:ℂ)*Complex.I
        have ord : RungeSupport.meshCoord A s i ≤ RungeSupport.meshCoord A s (i+1) := by
          rw [RungeSupport.meshCoord_succ]; linarith
        have hav : ∀ x ∈ Set.uIcc (RungeSupport.meshCoord A s i)
                          (RungeSupport.meshCoord A s (i+1)), pt x ≠ z := by
          intro x hx e
          have hx' : x ∈ Set.Icc (RungeSupport.meshCoord A s i)
                          (RungeSupport.meshCoord A s (i+1)) := by simpa [Set.uIcc_of_le ord] using hx
          have away := hhedge_away hn x hx'
          apply away
          change pt _ ∈ K
          rw [e]
          exact hz
        have hpcont : ContinuousOn pt (Set.uIcc (RungeSupport.meshCoord A s i)
                          (RungeSupport.meshCoord A s (i+1))) := by
          unfold pt; fun_prop
        have hfpt : ContinuousOn (fun x => f (pt x))
              (Set.uIcc (RungeSupport.meshCoord A s i) (RungeSupport.meshCoord A s (i+1))) := by
          apply continuousOn_of_forall_continuousAt
          intro x hx
          have hx' : x ∈ Set.Icc (RungeSupport.meshCoord A s i)
                            (RungeSupport.meshCoord A s (i+1)) := by simpa [Set.uIcc_of_le ord] using hx
          rcases hadj hn with hb | ht
          · have hj' := hb.1
            have hm : pt x ∈ RungeSupport.meshSquare A s i j := by
              apply (RungeSupport.mem_meshSquare).2
              have xu : x ≤ RungeSupport.meshCoord A s i + s := by
                rw [← RungeSupport.meshCoord_succ]; exact hx'.2
              simpa [pt] using
                (show RungeSupport.meshCoord A s i ≤ x ∧
                    x ≤ RungeSupport.meshCoord A s i + s ∧
                    RungeSupport.meshCoord A s j ≤ RungeSupport.meshCoord A s j ∧
                    RungeSupport.meshCoord A s j ≤ RungeSupport.meshCoord A s j + s
                    from ⟨hx'.1, xu, le_rfl, by linarith⟩)
            have fw := hcellP hi hj' hb.2 (pt x) hm
            exact fw.continuousAt.comp_of_eq (by fun_prop) (by rfl)
          · have jp := ht.1
            have jl : j-1 < N := by omega
            have hm : pt x ∈ RungeSupport.meshSquare A s i (j-1) := by
              apply (RungeSupport.mem_meshSquare).2
              have xu : x ≤ RungeSupport.meshCoord A s i + s := by
                rw [← RungeSupport.meshCoord_succ]; exact hx'.2
              have jeq : j-1+1 = j := by omega
              have basej : RungeSupport.meshCoord A s (j-1) + s =
                    RungeSupport.meshCoord A s j := by
                rw [← RungeSupport.meshCoord_succ, jeq]
              -- the old row ends exactly at j
              simpa [pt, basej] using
                (show RungeSupport.meshCoord A s i ≤ x ∧
                    x ≤ RungeSupport.meshCoord A s i + s ∧
                    RungeSupport.meshCoord A s (j-1) ≤ RungeSupport.meshCoord A s j ∧
                    RungeSupport.meshCoord A s j ≤ RungeSupport.meshCoord A s (j-1) + s
                    from ⟨hx'.1, xu, by linarith [basej, hs], le_of_eq basej.symm⟩)
            have fw := hcellP hi jl ht.2 (pt x) hm
            exact fw.continuousAt.comp_of_eq (by fun_prop) (by rfl)
        exact RungeSupport.continuousAt_interval_kernel _ _ _ _ z hfpt hpcont hav
      have hVcont (z : ℂ) (hz : z ∈ K) {i j : ℕ}
          (hi : i < N+1) (hj : j < N)
          (hn : RungeSupport.vcoef P N i j ≠ 0) :
          ContinuousAt (fun q : ℂ =>
            RungeSupport.vedge A s (fun w : ℂ => f w / (w-q)) i j) z := by
        let pt : ℝ → ℂ := fun y => (RungeSupport.meshCoord A s i:ℂ) + (y:ℂ)*Complex.I
        have ord : RungeSupport.meshCoord A s j ≤ RungeSupport.meshCoord A s (j+1) := by
          rw [RungeSupport.meshCoord_succ]; linarith
        have hav : ∀ y ∈ Set.uIcc (RungeSupport.meshCoord A s j)
                          (RungeSupport.meshCoord A s (j+1)), pt y ≠ z := by
          intro y hy e
          have hy' : y ∈ Set.Icc (RungeSupport.meshCoord A s j)
                          (RungeSupport.meshCoord A s (j+1)) := by simpa [Set.uIcc_of_le ord] using hy
          have away := hvedge_away hn y hy'
          apply away
          change pt _ ∈ K
          rw [e]
          exact hz
        have hpcont : ContinuousOn pt (Set.uIcc (RungeSupport.meshCoord A s j)
                          (RungeSupport.meshCoord A s (j+1))) := by
          unfold pt; fun_prop
        have hfpt : ContinuousOn (fun y => f (pt y))
              (Set.uIcc (RungeSupport.meshCoord A s j) (RungeSupport.meshCoord A s (j+1))) := by
          apply continuousOn_of_forall_continuousAt
          intro y hy
          have hy' : y ∈ Set.Icc (RungeSupport.meshCoord A s j)
                            (RungeSupport.meshCoord A s (j+1)) := by simpa [Set.uIcc_of_le ord] using hy
          rcases vadj hn with hl | hr
          · have il : i-1 < N := by omega
            have ei : i-1+1 = i := by omega
            have hm : pt y ∈ RungeSupport.meshSquare A s (i-1) j := by
              apply (RungeSupport.mem_meshSquare).2
              have yu : y ≤ RungeSupport.meshCoord A s j + s := by
                rw [← RungeSupport.meshCoord_succ]; exact hy'.2
              have ibase : RungeSupport.meshCoord A s (i-1) + s =
                    RungeSupport.meshCoord A s i := by
                rw [← RungeSupport.meshCoord_succ, ei]
              simpa [pt, ibase] using
                (show RungeSupport.meshCoord A s (i-1) ≤ RungeSupport.meshCoord A s i ∧
                    RungeSupport.meshCoord A s i ≤ RungeSupport.meshCoord A s (i-1)+s ∧
                    RungeSupport.meshCoord A s j ≤ y ∧
                    y ≤ RungeSupport.meshCoord A s j+s
                  from ⟨by linarith [ibase, hs], le_of_eq ibase.symm, hy'.1, yu⟩)
            have fw := hcellP il hj hl.2 (pt y) hm
            exact fw.continuousAt.comp_of_eq (by fun_prop) (by rfl)
          · have il := hr.1
            have hm : pt y ∈ RungeSupport.meshSquare A s i j := by
              apply (RungeSupport.mem_meshSquare).2
              have yu : y ≤ RungeSupport.meshCoord A s j + s := by
                rw [← RungeSupport.meshCoord_succ]; exact hy'.2
              simpa [pt] using
                (show RungeSupport.meshCoord A s i ≤ RungeSupport.meshCoord A s i ∧
                    RungeSupport.meshCoord A s i ≤ RungeSupport.meshCoord A s i+s ∧
                    RungeSupport.meshCoord A s j ≤ y ∧
                    y ≤ RungeSupport.meshCoord A s j+s
                  from ⟨le_rfl, by linarith, hy'.1, yu⟩)
            have fw := hcellP il hj hr.2 (pt y) hm
            exact fw.continuousAt.comp_of_eq (by fun_prop) (by rfl)
        exact RungeSupport.continuousAt_interval_kernel _ _ _ _ z hfpt hpcont hav
      have fincont (z : ℂ) {α : Type} (S : Finset α) (g : α → ℂ → ℂ)
          (hg : ∀ i ∈ S, ContinuousAt (g i) z) :
          ContinuousAt (fun q => ∑ i ∈ S, g i q) z := by
        change Filter.Tendsto _ _ _
        convert tendsto_finset_sum S (fun i hi => hg i hi) using 1
      have hEcont (z : ℂ) (hz : z ∈ K) :
          ContinuousAt (fun q : ℂ => RungeSupport.edgesum A s N P
            (fun w : ℂ => f w / (w-q))) z := by
        unfold RungeSupport.edgesum
        apply ContinuousAt.add
        · apply fincont
          intro i hi
          have hi' := Finset.mem_range.mp hi
          apply fincont
          intro j hj
          have hj' := Finset.mem_range.mp hj
          by_cases hn : RungeSupport.hcoef P N i j = 0
          · simpa [hn] using (continuousAt_const (x:=z) (y:=(0:ℂ)))
          · exact (hHcont z hz hi' hj' hn).const_mul _
        · apply ContinuousAt.const_mul
          apply fincont
          intro j hj
          have hj' := Finset.mem_range.mp hj
          apply fincont
          intro i hi
          have hi' := Finset.mem_range.mp hi
          by_cases hn : RungeSupport.vcoef P N i j = 0
          · simpa [hn] using (continuousAt_const (x:=z) (y:=(0:ℂ)))
          · exact (hVcont z hz hi' hj' hn).const_mul _
      -- Consequently the off-grid evaluation extends across the whole grid.
      have hall (z : ℂ) (hz : z ∈ K) :
          RungeSupport.edgesum A s N P (fun w : ℂ => f w / (w-z)) =
            f z * (2*Real.pi*Complex.I) := by
        obtain ⟨i,j,hi,hj,hmem⟩ :=
          RungeSupport.mesh_point_in_square (A:=A) (s:=s) hs (hbox z hz).1 (hbox z hz).2
        have hp : P i j := by
          dsimp [P, RungeSupport.meshHit]
          exact ⟨z, hz, hmem⟩
        have xy := (RungeSupport.mem_meshSquare.mp hmem)
        have lx : z.re ∈ Set.Icc (RungeSupport.meshCoord A s i)
              (RungeSupport.meshCoord A s (i+1)) := by
          rw [RungeSupport.meshCoord_succ]
          exact ⟨xy.1, xy.2.1⟩
        have ly : z.im ∈ Set.Icc (RungeSupport.meshCoord A s j)
              (RungeSupport.meshCoord A s (j+1)) := by
          rw [RungeSupport.meshCoord_succ]
          exact ⟨xy.2.2.1, xy.2.2.2⟩
        apply RungeSupport.eq_of_continuousAt_of_eq_on_rect
          (fun q : ℂ => RungeSupport.edgesum A s N P (fun w : ℂ => f w/(w-q)))
          (fun q : ℂ => f q * (2*Real.pi*Complex.I)) z (hEcont z hz)
          ((hkAt z hz).continuousAt.mul_const _) (by rw [RungeSupport.meshCoord_succ]; linarith)
            (by rw [RungeSupport.meshCoord_succ]; linarith) lx ly
        intro w wx wy
        exact hoffgrid hi hj wx wy hp
      refine RungeSupport.exists_mesh_contours K A s N P f hs ?_ ?_ ?_ ?_
      · intro i j hi hj hp w hw
        exact hcellP hi hj hp w hw
      · intro i j hi hj hn
        exact hhedge_away hn
      · intro i j hi hj hn
        exact hvedge_away hn
      · intro z hz
        simpa [RungeSupport.cDen] using (hall z hz)
    rcases hchains with ⟨m, c, γ, hc, hγ, hout, hrep⟩
    exact RungeSupport.of_contour_representation K _hK f m c γ
      hc hγ hout hrep _hε
  ·
    have hempty : K = ∅ := Set.not_nonempty_iff_eq_empty.mp h0
    subst K
    exact ⟨0, 1, by simp, by simp⟩
/-ResultProofEnd-/
/-ResultEnd-/
-- END INLINED FILE: Main.lean

end Submission
