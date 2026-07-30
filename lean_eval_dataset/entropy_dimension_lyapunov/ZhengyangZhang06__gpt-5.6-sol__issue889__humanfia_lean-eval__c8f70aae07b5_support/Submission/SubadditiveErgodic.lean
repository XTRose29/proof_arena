import Submission.LyapunovJacobian

namespace Submission.Helpers

open Filter MeasureTheory

/-- The subadditivity convention satisfied by logarithmic derivative norms. -/
def IsSubadditiveCocycle {M : Type*} (T : M → M) (f : ℕ → M → ℝ) : Prop :=
  ∀ m n x, f (m + n) x ≤ f m (T^[n] x) + f n x

lemma subadditiveCocycle_block_mul
    {M : Type*} {T : M → M} {f : ℕ → M → ℝ}
    (hzero : ∀ x, f 0 x = 0) (hsub : IsSubadditiveCocycle T f)
    (r q : ℕ) (x : M) :
    f (q * r) x ≤ ∑ k ∈ Finset.range q, f r (T^[k * r] x) := by
  induction q with
  | zero => simp [hzero]
  | succ q ih =>
      have hadd := hsub r (q * r) x
      rw [show r + q * r = (q + 1) * r by ring] at hadd
      calc
        f ((q + 1) * r) x ≤ f r (T^[q * r] x) + f (q * r) x := hadd
        _ ≤ f r (T^[q * r] x) +
            ∑ k ∈ Finset.range q, f r (T^[k * r] x) :=
          add_le_add (le_refl _) ih
        _ = ∑ k ∈ Finset.range (q + 1), f r (T^[k * r] x) := by
          rw [Finset.sum_range_succ]
          abel

lemma sum_range_rectangle_mod
    (a : ℕ → ℝ) {q r : ℕ} (hr : 0 < r) :
    (∑ j ∈ Finset.range r, ∑ k ∈ Finset.range q, a (j + k * r)) =
      ∑ i ∈ Finset.range (q * r), a i := by
  classical
  rw [Finset.sum_sigma']
  apply Finset.sum_bij
      (fun p _hp => p.1 + p.2 * r)
  · rintro ⟨j, k⟩ hp
    rw [Finset.mem_sigma] at hp
    rw [Finset.mem_range]
    have hj : j < r := Finset.mem_range.mp hp.1
    have hk : k < q := Finset.mem_range.mp hp.2
    nlinarith [Nat.mul_lt_mul_of_pos_right hk hr]
  · rintro ⟨j₁, k₁⟩ hp₁ ⟨j₂, k₂⟩ hp₂ heq
    rw [Finset.mem_sigma] at hp₁ hp₂
    have hj₁ : j₁ < r := Finset.mem_range.mp hp₁.1
    have hj₂ : j₂ < r := Finset.mem_range.mp hp₂.1
    have hj : j₁ = j₂ := by
      have hmod := congrArg (fun n : ℕ => n % r) heq
      simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj₁,
        Nat.mod_eq_of_lt hj₂] using hmod
    subst j₂
    have hmul : k₁ * r = k₂ * r := Nat.add_left_cancel heq
    have hk : k₁ = k₂ := Nat.mul_right_cancel hr hmul
    subst k₂
    rfl
  · intro i hi
    have hi' : i < q * r := Finset.mem_range.mp hi
    let j := i % r
    let k := i / r
    have hj : j < r := Nat.mod_lt i hr
    have hk : k < q := (Nat.div_lt_iff_lt_mul hr).2 hi'
    refine ⟨⟨j, k⟩, Finset.mem_sigma.mpr
      ⟨Finset.mem_range.mpr hj, Finset.mem_range.mpr hk⟩, ?_⟩
    dsimp [j, k]
    simpa [Nat.mul_comm] using Nat.mod_add_div i r
  · rintro ⟨j, k⟩ hp
    rfl

lemma subadditiveCocycle_mul_le_birkhoffSum_add
    {M : Type*} {T : M → M} {f : ℕ → M → ℝ}
    (hzero : ∀ x, f 0 x = 0) (hsub : IsSubadditiveCocycle T f)
    {D : ℝ} (hD : 0 ≤ D)
    (hshift : ∀ n j x, f n x ≤ f n (T^[j] x) + D * j)
    {r : ℕ} (hr : 0 < r) (q : ℕ) (x : M) :
    (r : ℝ) * f (q * r) x ≤
      birkhoffSum T (f r) (q * r) x + D * (r : ℝ) ^ 2 := by
  calc
    (r : ℝ) * f (q * r) x =
        ∑ j ∈ Finset.range r, f (q * r) x := by simp
    _ ≤ ∑ j ∈ Finset.range r,
        (f (q * r) (T^[j] x) + D * j) := by
      exact Finset.sum_le_sum fun j _hj => hshift (q * r) j x
    _ ≤ ∑ j ∈ Finset.range r,
        ((∑ k ∈ Finset.range q,
            f r (T^[k * r] (T^[j] x))) + D * j) := by
      exact Finset.sum_le_sum fun j _hj =>
        add_le_add (subadditiveCocycle_block_mul hzero hsub r q (T^[j] x))
          (le_refl _)
    _ = (∑ j ∈ Finset.range r, ∑ k ∈ Finset.range q,
          f r (T^[j + k * r] x)) +
        D * ∑ j ∈ Finset.range r, (j : ℝ) := by
      simp_rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro k hk
        rw [← Function.iterate_add_apply]
        rw [Nat.add_comm (k * r) j]
    _ = birkhoffSum T (f r) (q * r) x +
        D * ∑ j ∈ Finset.range r, (j : ℝ) := by
      rw [sum_range_rectangle_mod (fun i => f r (T^[i] x)) hr]
      rfl
    _ ≤ birkhoffSum T (f r) (q * r) x + D * (r : ℝ) ^ 2 := by
      have hsum : ∑ j ∈ Finset.range r, (j : ℝ) ≤ (r : ℝ) ^ 2 := by
        calc
          ∑ j ∈ Finset.range r, (j : ℝ) ≤
              ∑ _j ∈ Finset.range r, (r : ℝ) := by
            exact Finset.sum_le_sum fun j hj => by
              exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hj))
          _ = (r : ℝ) ^ 2 := by simp [pow_two]
      exact add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left hsum hD)

noncomputable def cocycleCheapSet
    {M : Type*} (f : ℕ → M → ℝ) (a : ℝ) (N : ℕ) : Set M :=
  ⋃ n ∈ Finset.Icc 1 N, {x | f n x ≤ a * n}

noncomputable def cocycleBadIndicator
    {M : Type*} (f : ℕ → M → ℝ) (a : ℝ) (N : ℕ) : M → ℝ :=
  (cocycleCheapSet f a N)ᶜ.indicator 1

lemma cocycleBadIndicator_nonneg
    {M : Type*} (f : ℕ → M → ℝ) (a : ℝ) (N : ℕ) (x : M) :
    0 ≤ cocycleBadIndicator f a N x := by
  classical
  rw [cocycleBadIndicator, Set.indicator_apply]
  split <;> simp

lemma cocycleBadIndicator_eq_one_of_not_mem
    {M : Type*} {f : ℕ → M → ℝ} {a : ℝ} {N : ℕ} {x : M}
    (hx : x ∉ cocycleCheapSet f a N) :
    cocycleBadIndicator f a N x = 1 := by
  simp [cocycleBadIndicator, hx]

lemma measurableSet_cocycleCheapSet
    {M : Type*} [MeasurableSpace M] {f : ℕ → M → ℝ}
    (hf : ∀ n, Measurable (f n)) (a : ℝ) (N : ℕ) :
    MeasurableSet (cocycleCheapSet f a N) := by
  apply Finset.measurableSet_biUnion
  intro n hn
  exact measurableSet_le (hf n) measurable_const

lemma measurable_cocycleBadIndicator
    {M : Type*} [MeasurableSpace M] {f : ℕ → M → ℝ}
    (hf : ∀ n, Measurable (f n)) (a : ℝ) (N : ℕ) :
    Measurable (cocycleBadIndicator f a N) := by
  exact measurable_const.indicator
    (measurableSet_cocycleCheapSet hf a N).compl

lemma integral_cocycleBadIndicator
    {M : Type*} [MeasurableSpace M] (mu : Measure M)
    {f : ℕ → M → ℝ} (hf : ∀ n, Measurable (f n)) (a : ℝ) (N : ℕ) :
    ∫ x, cocycleBadIndicator f a N x ∂mu =
      mu.real (cocycleCheapSet f a N)ᶜ := by
  exact integral_indicator_one (measurableSet_cocycleCheapSet hf a N).compl

lemma monotone_cocycleCheapSet
    {M : Type*} (f : ℕ → M → ℝ) (a : ℝ) :
    Monotone (cocycleCheapSet f a) := by
  intro N L hNL x hx
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hn, hxcheap⟩ := Set.mem_iUnion.mp hxn
  apply Set.mem_iUnion_of_mem n
  apply Set.mem_iUnion_of_mem
    (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,
      (Finset.mem_Icc.mp hn).2.trans hNL⟩)
  exact hxcheap

lemma mem_iUnion_cocycleCheapSet_iff
    {M : Type*} (f : ℕ → M → ℝ) (a : ℝ) (x : M) :
    x ∈ ⋃ N : ℕ, cocycleCheapSet f a N ↔
      ∃ n : ℕ, 0 < n ∧ f n x ≤ a * n := by
  constructor
  · intro hx
    obtain ⟨N, hxN⟩ := Set.mem_iUnion.mp hx
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hxN
    obtain ⟨hn, hxcheap⟩ := Set.mem_iUnion.mp hxn
    exact ⟨n, (Finset.mem_Icc.mp hn).1, hxcheap⟩
  · rintro ⟨n, hn, hxcheap⟩
    apply Set.mem_iUnion_of_mem n
    apply Set.mem_iUnion_of_mem n
    apply Set.mem_iUnion_of_mem (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩)
    exact hxcheap

lemma subadditiveCocycle_shift_le_of_map_diff
    {M : Type*} {T : M → M} {f : ℕ → M → ℝ}
    {D : ℝ} (hmap : ∀ n x, |f n (T x) - f n x| ≤ D) :
    ∀ n j x, f n x ≤ f n (T^[j] x) + D * j := by
  intro n j
  induction j with
  | zero => intro x; simp
  | succ j ih =>
      intro x
      have hstep : f n (T^[j] x) ≤ f n (T^[j + 1] x) + D := by
        have h := neg_le_of_abs_le (hmap n (T^[j] x))
        rw [Function.iterate_succ_apply']
        linarith
      calc
        f n x ≤ f n (T^[j] x) + D * j := ih x
        _ ≤ (f n (T^[j + 1] x) + D) + D * j :=
          add_le_add hstep (le_refl _)
        _ = f n (T^[j + 1] x) + D * ((j + 1 : ℕ) : ℝ) := by
          rw [Nat.cast_add, Nat.cast_one]
          ring

lemma abs_cocycle_div_le
    {M : Type*} {f : ℕ → M → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hbound : ∀ n x, |f n x| ≤ B * n)
    (n : ℕ) (x : M) :
    |f n x / n| ≤ B := by
  cases n with
  | zero => simp [hB]
  | succ n =>
      have hn : (0 : ℝ) < n + 1 := by positivity
      rw [abs_div]
      norm_num [Nat.cast_add, Nat.cast_one]
      rw [abs_of_pos hn]
      exact (div_le_iff₀ hn).2 (by
        simpa [mul_comm] using hbound (n + 1) x)

lemma tendsto_cocycle_div_map_sub
    {M : Type*} {T : M → M} {f : ℕ → M → ℝ}
    {D : ℝ} (hmap : ∀ n x, |f n (T x) - f n x| ≤ D) (x : M) :
    Tendsto (fun n => f n (T x) / n - f n x / n) atTop (nhds 0) := by
  have hbound : ∀ n, |f n (T x) / n - f n x / n| ≤ D / n := by
    intro n
    cases n with
    | zero => simp
    | succ n =>
        have hn : (0 : ℝ) < n + 1 := by positivity
        rw [← sub_div, abs_div]
        norm_num [Nat.cast_add, Nat.cast_one]
        rw [abs_of_pos hn]
        exact div_le_div_of_nonneg_right (hmap (n + 1) x) hn.le
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact squeeze_zero (fun n => abs_nonneg _)
    hbound (by simpa using tendsto_const_div_atTop_nhds_zero_nat D)

lemma limsup_eq_of_tendsto_sub_zero
    {u v : ℕ → ℝ}
    (hv_lower : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop v)
    (hv_upper : IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop v)
    (h : Tendsto (u - v) atTop (nhds 0)) :
    limsup u atTop = limsup v atTop := by
  have huv : u = v + (u - v) := by
    funext n
    simp
  rw [huv, limsup_add_eq_add_of_tendsto hv_lower hv_upper h]
  simp

lemma liminf_eq_of_tendsto_sub_zero
    {u v : ℕ → ℝ}
    (hu_lower : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop u)
    (hu_upper : IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop u)
    (hv_lower : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop v)
    (hv_upper : IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop v)
    (h : Tendsto (u - v) atTop (nhds 0)) :
    liminf u atTop = liminf v atTop := by
  have hneg : Tendsto ((-u) - (-v)) atTop (nhds 0) := by
    have : (-u) - (-v) = -(u - v) := by
      funext n
      simp only [Pi.sub_apply, Pi.neg_apply]
      ring
    rw [this]
    change Tendsto (fun n => -(u n - v n)) atTop (nhds 0)
    simpa using h.neg
  have hnv_lower : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop (-v) := by
    obtain ⟨b, hb⟩ := hv_upper.eventually_le
    apply isBoundedUnder_of_eventually_ge (a := -b)
    exact hb.mono fun n hn => by simpa using neg_le_neg hn
  have hnv_upper : IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop (-v) := by
    obtain ⟨b, hb⟩ := hv_lower.eventually_ge
    apply isBoundedUnder_of_eventually_le (a := -b)
    exact hb.mono fun n hn => by simpa using neg_le_neg hn
  have hlimsup := limsup_eq_of_tendsto_sub_zero
    hnv_lower hnv_upper hneg
  have hu_neg := limsup_const_sub atTop u 0 hu_upper.isCobounded_flip hu_lower
  have hv_neg := limsup_const_sub atTop v 0 hv_upper.isCobounded_flip hv_lower
  have hneg_eq : limsup (-u) atTop = -liminf u atTop := by
    change limsup (fun n => -u n) atTop = -liminf u atTop
    simpa only [zero_sub] using hu_neg
  have hneg_eq' : limsup (-v) atTop = -liminf v atTop := by
    change limsup (fun n => -v n) atTop = -liminf v atTop
    simpa only [zero_sub] using hv_neg
  rw [hneg_eq, hneg_eq'] at hlimsup
  exact neg_inj.mp hlimsup

def nextMultiple (r n : ℕ) : ℕ := (n / r + 1) * r

lemma le_nextMultiple {r : ℕ} (hr : 0 < r) (n : ℕ) :
    n ≤ nextMultiple r n := by
  have hmod := Nat.mod_lt n hr
  calc
    n = n % r + r * (n / r) := (Nat.mod_add_div n r).symm
    _ ≤ r + r * (n / r) := Nat.add_le_add_right hmod.le _
    _ = nextMultiple r n := by
      unfold nextMultiple
      ring

lemma nextMultiple_sub_le {r : ℕ} (hr : 0 < r) (n : ℕ) :
    nextMultiple r n - n ≤ r := by
  have hmod := Nat.mod_lt n hr
  have hupper : nextMultiple r n ≤ n + r := by
    calc
      nextMultiple r n = r * (n / r) + r := by
        unfold nextMultiple
        ring
      _ ≤ n + r := by
        have hdiv : r * (n / r) ≤ n := by
          calc
            r * (n / r) ≤ n % r + r * (n / r) := Nat.le_add_left _ _
            _ = n := Nat.mod_add_div n r
        exact Nat.add_le_add_right hdiv r
  have hlower := le_nextMultiple hr n
  omega

lemma tendsto_nextMultiple_atTop {r : ℕ} (hr : 0 < r) :
    Tendsto (nextMultiple r) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop b] with n hn
  exact hn.trans (le_nextMultiple hr n)

lemma tendsto_nextMultiple_div {r : ℕ} (hr : 0 < r) :
    Tendsto (fun n : ℕ => (nextMultiple r n : ℝ) / n)
      atTop (nhds 1) := by
  have herror : Tendsto
      (fun n : ℕ => (nextMultiple r n : ℝ) / n - 1)
      atTop (nhds 0) := by
    apply squeeze_zero'
      (f := fun n : ℕ => (nextMultiple r n : ℝ) / n - 1)
      (g := fun n : ℕ => (r : ℝ) / n)
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
      apply sub_nonneg.mpr
      apply (le_div_iff₀ hnreal).2
      norm_num
      exact_mod_cast le_nextMultiple hr n
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
      have hgap : (nextMultiple r n : ℝ) - n ≤ r := by
        rw [← Nat.cast_sub (le_nextMultiple hr n)]
        exact_mod_cast nextMultiple_sub_le hr n
      rw [div_sub_one hnreal.ne']
      exact (div_le_div_iff_of_pos_right hnreal).2 hgap
    · simpa using tendsto_const_div_atTop_nhds_zero_nat (r : ℝ)
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have h := hconst.add herror
  convert h using 1
  · funext n
    ring
  · ring_nf

lemma ae_limsup_subadditiveCocycle_div_le_integral
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    (f : ℕ → M → ℝ) (hf : ∀ n, Measurable (f n))
    (hzero : ∀ x, f 0 x = 0) (hsub : IsSubadditiveCocycle T f)
    {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hbound : ∀ n x, |f n x| ≤ B * n)
    (hmap : ∀ n x, |f n (T x) - f n x| ≤ D)
    (hpad : ∀ n s x, f n x ≤ f (n + s) x + B * s)
    {r : ℕ} (hr : 0 < r) :
    ∀ᵐ x ∂mu, limsup (fun n => f n x / n) atTop ≤
      (∫ y, f r y ∂mu) / r := by
  have hfr : Integrable (f r) mu := by
    apply Integrable.of_bound (hf r).aestronglyMeasurable (B * r)
    exact Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hbound r x
  have havg := ae_tendsto_birkhoffAverage_integral
    mu T hT hErg (f r) (hf r) hfr
  filter_upwards [havg] with x hxavg
  let N : ℕ → ℕ := nextMultiple r
  let u : ℕ → ℝ := fun n => f n x / n
  let rhs : ℕ → ℝ := fun n =>
    birkhoffAverage ℝ T (f r) (N n) x * ((N n : ℝ) / n) / r +
      (D + B) * r / n
  have hN_tend : Tendsto N atTop atTop := tendsto_nextMultiple_atTop hr
  have hratio : Tendsto (fun n : ℕ => (N n : ℝ) / n) atTop (nhds 1) :=
    tendsto_nextMultiple_div hr
  have hrhs : Tendsto rhs atTop (nhds ((∫ y, f r y ∂mu) / r)) := by
    have havgN := hxavg.comp hN_tend
    have hmain := (havgN.mul hratio).div_const (r : ℝ)
    have herr : Tendsto (fun n : ℕ => (D + B) * r / n) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat ((D + B) * r)
    simpa [rhs] using hmain.add herr
  have hpoint : u ≤ᶠ[atTop] rhs := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    let q := n / r + 1
    have hN : N n = q * r := rfl
    have hnN : n ≤ N n := le_nextMultiple hr n
    have hgap : N n - n ≤ r := nextMultiple_sub_le hr n
    have hpad' := hpad n (N n - n) x
    rw [Nat.add_sub_of_le hnN] at hpad'
    rw [Nat.cast_sub hnN] at hpad'
    have hblock := subadditiveCocycle_mul_le_birkhoffSum_add
      hzero hsub hD
      (subadditiveCocycle_shift_le_of_map_diff hmap) hr q x
    rw [← hN] at hblock
    have hscaled : (r : ℝ) * f n x ≤
        birkhoffSum T (f r) (N n) x + (D + B) * (r : ℝ) ^ 2 := by
      calc
        (r : ℝ) * f n x ≤
            (r : ℝ) * (f (N n) x + B * (N n - n)) :=
          mul_le_mul_of_nonneg_left hpad' (Nat.cast_nonneg r)
        _ ≤ (r : ℝ) * f (N n) x + B * (r : ℝ) ^ 2 := by
          have hgap_real : (N n : ℝ) - n ≤ r := by
            rw [← Nat.cast_sub hnN]
            exact_mod_cast hgap
          have hmul := mul_le_mul_of_nonneg_left hgap_real hB
          nlinarith
        _ ≤ birkhoffSum T (f r) (N n) x + D * (r : ℝ) ^ 2 +
            B * (r : ℝ) ^ 2 := add_le_add hblock (le_refl _)
        _ = birkhoffSum T (f r) (N n) x + (D + B) * (r : ℝ) ^ 2 := by ring
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    have hrreal : (0 : ℝ) < r := by exact_mod_cast hr
    have hNpos : (0 : ℝ) < N n := by
      exact_mod_cast lt_of_lt_of_le hn hnN
    dsimp [u, rhs]
    have havg_eq : birkhoffSum T (f r) (N n) x =
        (N n : ℝ) * birkhoffAverage ℝ T (f r) (N n) x := by
      simp [birkhoffAverage, smul_eq_mul]
      field_simp
    rw [havg_eq] at hscaled
    rw [div_le_iff₀ hnreal]
    have hdivr : f n x ≤
        ((N n : ℝ) * birkhoffAverage ℝ T (f r) (N n) x +
          (D + B) * (r : ℝ) ^ 2) / r := by
      have := (div_le_div_iff_of_pos_right hrreal).2 hscaled
      simpa [hrreal.ne'] using this
    calc
      f n x ≤ ((N n : ℝ) * birkhoffAverage ℝ T (f r) (N n) x +
          (D + B) * (r : ℝ) ^ 2) / r := hdivr
      _ = (birkhoffAverage ℝ T (f r) (N n) x * ((N n : ℝ) / n) / r +
            (D + B) * r / n) * n := by
        field_simp [hnreal.ne', hrreal.ne']
  have hu_lower : IsBoundedUnder (fun a b : ℝ => a ≥ b) atTop u :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall fun n =>
      neg_le_of_abs_le (abs_cocycle_div_le hB hbound n x))
  have hu_upper : IsBoundedUnder (fun a b : ℝ => a ≤ b) atTop u :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun n =>
      le_of_abs_le (abs_cocycle_div_le hB hbound n x))
  rw [limsup_le_iff hu_lower.isCobounded_flip hu_upper]
  intro y hy
  have hyrhs : ∀ᶠ n in atTop, rhs n < y := (tendsto_order.1 hrhs).2 y hy
  filter_upwards [hpoint, hyrhs] with n hn hn'
  exact hn.trans_lt hn'

lemma birkhoffSum_tail_le
    {M : Type*} (T : M → M) (g : M → ℝ) (hg : ∀ x, 0 ≤ g x)
    {n m : ℕ} (hnm : n ≤ m) (x : M) :
    birkhoffSum T g (m - n) (T^[n] x) ≤ birkhoffSum T g m x := by
  have hadd := birkhoffSum_add T g n (m - n) x
  rw [Nat.add_sub_of_le hnm] at hadd
  rw [hadd]
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun i _hi => hg _)

lemma subadditiveCocycle_stopping_bound
    {M : Type*} {T : M → M} {f : ℕ → M → ℝ}
    (hzero : ∀ x, f 0 x = 0) (hsub : IsSubadditiveCocycle T f)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ n x, |f n x| ≤ B * n)
    (a : ℝ) (N m : ℕ) (x : M) :
    f m x ≤ a * m + (B + |a|) * N +
      (B + |a|) * birkhoffSum T (cocycleBadIndicator f a N) m x := by
  let C : ℝ := B + |a|
  have hC : 0 ≤ C := add_nonneg hB (abs_nonneg a)
  change f m x ≤ a * m + C * N +
    C * birkhoffSum T (cocycleBadIndicator f a N) m x
  induction m using Nat.strong_induction_on generalizing x with
  | h m ih =>
      cases m with
      | zero =>
        rw [hzero]
        simp only [Nat.cast_zero, mul_zero, zero_add, birkhoffSum, Finset.range_zero,
          Finset.sum_empty, mul_zero, add_zero]
        exact mul_nonneg hC (Nat.cast_nonneg N)
      | succ p =>
          norm_num [Nat.cast_add, Nat.cast_one] at *
          by_cases hx : x ∈ cocycleCheapSet f a N
          · obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
            obtain ⟨hn, hxcheap⟩ := Set.mem_iUnion.mp hxn
            have hnIcc := Finset.mem_Icc.mp hn
            by_cases hnm : n ≤ p + 1
            · have hsub' := hsub (p + 1 - n) n x
              rw [Nat.sub_add_cancel hnm] at hsub'
              have hsub_lt : p + 1 - n < p + 1 := by omega
              have htail := ih (p + 1 - n) (by omega) (T^[n] x)
              calc
                f (p + 1) x ≤ f (p + 1 - n) (T^[n] x) + f n x := hsub'
                _ ≤ (a * ((p + 1 - n : ℕ) : ℝ) + C * N +
                      C * birkhoffSum T (cocycleBadIndicator f a N)
                        (p + 1 - n) (T^[n] x)) + a * n := by
                  exact add_le_add htail hxcheap
                _ ≤ a * ((p : ℝ) + 1) + C * N +
                    C * birkhoffSum T (cocycleBadIndicator f a N) (p + 1) x := by
                  have htail_le := birkhoffSum_tail_le T
                    (cocycleBadIndicator f a N) (cocycleBadIndicator_nonneg f a N)
                    hnm x
                  have htail_mul := mul_le_mul_of_nonneg_left htail_le hC
                  have hcast : ((p + 1 - n : ℕ) : ℝ) + n = (p : ℝ) + 1 := by
                    exact_mod_cast Nat.sub_add_cancel hnm
                  calc
                    (a * ((p + 1 - n : ℕ) : ℝ) + C * N +
                        C * birkhoffSum T (cocycleBadIndicator f a N)
                          (p + 1 - n) (T^[n] x)) + a * n =
                        a * (((p + 1 - n : ℕ) : ℝ) + n) + C * N +
                          C * birkhoffSum T (cocycleBadIndicator f a N)
                            (p + 1 - n) (T^[n] x) := by ring
                    _ = a * ((p : ℝ) + 1) + C * N +
                        C * birkhoffSum T (cocycleBadIndicator f a N)
                          (p + 1 - n) (T^[n] x) := by rw [hcast]
                    _ ≤ a * ((p : ℝ) + 1) + C * N +
                        C * birkhoffSum T (cocycleBadIndicator f a N) (p + 1) x :=
                      add_le_add (le_refl _) htail_mul
            · have hmp : p + 1 < n := lt_of_not_ge hnm
              have hmN : p + 1 ≤ N := hmp.le.trans hnIcc.2
              have hfupper : f (p + 1) x ≤ B * ((p + 1 : ℕ) : ℝ) :=
                (le_abs_self _).trans (hbound (p + 1) x)
              norm_num [Nat.cast_add, Nat.cast_one] at hfupper
              have hmNreal : ((p + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hmN
              have hcoef : B - a ≤ C := by
                dsimp [C]
                linarith [neg_abs_le a]
              have hprod : (B - a) * ((p + 1 : ℕ) : ℝ) ≤ C * N :=
                mul_le_mul hcoef hmNreal (Nat.cast_nonneg _) hC
              norm_num [Nat.cast_add, Nat.cast_one] at hprod
              have hbase : B * ((p : ℝ) + 1) ≤
                  a * ((p : ℝ) + 1) + C * N := by
                calc
                  B * ((p : ℝ) + 1) =
                      a * ((p : ℝ) + 1) +
                        (B - a) * ((p : ℝ) + 1) := by ring
                  _ ≤ a * ((p : ℝ) + 1) + C * N :=
                    add_le_add (le_refl _) hprod
              have hbad_nonneg : 0 ≤
                  birkhoffSum T (cocycleBadIndicator f a N) (p + 1) x := by
                exact Finset.sum_nonneg fun i _hi =>
                  cocycleBadIndicator_nonneg f a N _
              calc
                f (p + 1) x ≤ B * ((p : ℝ) + 1) := hfupper
                _ ≤ a * ((p : ℝ) + 1) + C * N := hbase
                _ ≤ a * ((p : ℝ) + 1) + C * N + C *
                    birkhoffSum T (cocycleBadIndicator f a N) (p + 1) x :=
                  le_add_of_nonneg_right (mul_nonneg hC hbad_nonneg)
          · have hsub' := hsub p 1 x
            have htail := ih p (by omega) (T x)
            have hfone : f 1 x ≤ B := by
              simpa using (le_abs_self (f 1 x)).trans (hbound 1 x)
            have hbad : cocycleBadIndicator f a N x = 1 :=
              cocycleBadIndicator_eq_one_of_not_mem hx
            have hpay : B ≤ a + C := by
              dsimp [C]
              linarith [neg_abs_le a]
            rw [show p + 1 = p + 1 by rfl] at hsub'
            calc
              f (p + 1) x ≤ f p (T x) + f 1 x := hsub'
              _ ≤ (a * p + C * N +
                    C * birkhoffSum T (cocycleBadIndicator f a N) p (T x)) + B := by
                exact add_le_add htail hfone
              _ ≤ (a * p + C * N +
                    C * birkhoffSum T (cocycleBadIndicator f a N) p (T x)) +
                    (a + C) := add_le_add (le_refl _) hpay
              _ = a * ((p : ℝ) + 1) + C * N + C *
                    birkhoffSum T (cocycleBadIndicator f a N) (p + 1) x := by
                rw [birkhoffSum_succ', hbad]
                ring

theorem ae_tendsto_subadditiveCocycle_div_limsup
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    (f : ℕ → M → ℝ) (hf : ∀ n, Measurable (f n))
    (hzero : ∀ x, f 0 x = 0) (hsub : IsSubadditiveCocycle T f)
    {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hbound : ∀ n x, |f n x| ≤ B * n)
    (hmap : ∀ n x, |f n (T x) - f n x| ≤ D)
    (hpad : ∀ n s x, f n x ≤ f (n + s) x + B * s) :
    ∀ᵐ x ∂mu, Tendsto (fun n => f n x / n) atTop
      (nhds (limsup (fun n => f n x / n) atTop)) := by
  let u : M → ℕ → ℝ := fun x n => f n x / n
  let upper : M → ℝ := fun x => limsup (u x) atTop
  let lower : M → ℝ := fun x => liminf (u x) atTop
  have hu_measurable (n : ℕ) : Measurable fun x => u x n := by
    exact (hf n).div_const n
  have hupper_measurable : Measurable upper := by
    exact Measurable.limsup hu_measurable
  have hlower_measurable : Measurable lower := by
    exact Measurable.liminf hu_measurable
  have hu_abs (x : M) (n : ℕ) : |u x n| ≤ B :=
    abs_cocycle_div_le hB hbound n x
  have hu_lower (x : M) :
      IsBoundedUnder (fun a b : ℝ => a ≥ b) atTop (u x) :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall fun n =>
      neg_le_of_abs_le (hu_abs x n))
  have hu_upper (x : M) :
      IsBoundedUnder (fun a b : ℝ => a ≤ b) atTop (u x) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun n =>
      le_of_abs_le (hu_abs x n))
  have hupper_map (x : M) : upper (T x) = upper x := by
    apply limsup_eq_of_tendsto_sub_zero (hu_lower x) (hu_upper x)
    change Tendsto (fun n => f n (T x) / n - f n x / n) atTop (nhds 0)
    exact tendsto_cocycle_div_map_sub hmap x
  have hlower_map (x : M) : lower (T x) = lower x := by
    apply liminf_eq_of_tendsto_sub_zero
      (hu_lower (T x)) (hu_upper (T x)) (hu_lower x) (hu_upper x)
    change Tendsto (fun n => f n (T x) / n - f n x / n) atTop (nhds 0)
    exact tendsto_cocycle_div_map_sub hmap x
  obtain ⟨c, hc⟩ := hErg.ae_eq_const_of_ae_eq_comp_ae
    hupper_measurable.aestronglyMeasurable
    (Eventually.of_forall hupper_map)
  obtain ⟨d, hd⟩ := hErg.ae_eq_const_of_ae_eq_comp_ae
    hlower_measurable.aestronglyMeasurable
    (Eventually.of_forall hlower_map)
  have hdc : d ≤ c := by
    have hae : ∀ᵐ x ∂mu, d ≤ c := by
      filter_upwards [hc, hd] with x hcx hdx
      have hcx' : upper x = c := by simpa [Function.const_def] using hcx
      have hdx' : lower x = d := by simpa [Function.const_def] using hdx
      rw [← hcx', ← hdx']
      exact liminf_le_limsup (hu_upper x) (hu_lower x)
    exact hae.exists.choose_spec
  have hupper_integral (r : ℕ) (hr : 0 < r) :
      c ≤ (∫ y, f r y ∂mu) / r := by
    have haeUpper := ae_limsup_subadditiveCocycle_div_le_integral
      mu T hT hErg f hf hzero hsub hB hD hbound hmap hpad hr
    have hae : ∀ᵐ x ∂mu, c ≤ (∫ y, f r y ∂mu) / r := by
      filter_upwards [hc, haeUpper] with x hcx hx
      have hcx' : upper x = c := by simpa [Function.const_def] using hcx
      rw [← hcx']
      simpa [upper, u] using hx
    exact hae.exists.choose_spec
  have hcd : c ≤ d := by
    by_contra hnot
    have hdc' : d < c := lt_of_not_ge hnot
    let a : ℝ := (c + d) / 2
    let C : ℝ := B + |a|
    have hda : d < a := by dsimp [a]; linarith
    have hac : a < c := by dsimp [a]; linarith
    have hC : 0 ≤ C := add_nonneg hB (abs_nonneg a)
    have hfullUnion : mu (⋃ N : ℕ, cocycleCheapSet f a N)ᶜ = 0 := by
      apply mem_ae_iff.mp
      filter_upwards [hd] with x hdx
      rw [mem_iUnion_cocycleCheapSet_iff]
      have hliminf : liminf (u x) atTop < a := by
        have hdx' : lower x = d := by simpa [Function.const_def] using hdx
        change lower x < a
        rw [hdx']
        exact hda
      have hfreq : ∃ᶠ n in atTop, u x n < a :=
        frequently_lt_of_liminf_lt (hu_upper x).isCobounded_flip hliminf
      obtain ⟨n, hnlt, hnpos⟩ :=
        (hfreq.and_eventually (eventually_gt_atTop 0)).exists
      have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
      refine ⟨n, hnpos, le_of_lt ?_⟩
      exact (div_lt_iff₀ hnreal).mp (by simpa [u] using hnlt)
    have hbad_tend : Tendsto
        (fun N => mu.real (cocycleCheapSet f a N)ᶜ)
        atTop (nhds 0) := by
      have hinter : ⋂ N : ℕ, (cocycleCheapSet f a N)ᶜ =
          (⋃ N : ℕ, cocycleCheapSet f a N)ᶜ := by simp
      have hmeasure := tendsto_measure_iInter_atTop
        (μ := mu)
        (fun N => (measurableSet_cocycleCheapSet hf a N).compl.nullMeasurableSet)
        (fun N L hNL => Set.compl_subset_compl.mpr
          (monotone_cocycleCheapSet f a hNL))
        ⟨0, measure_ne_top mu _⟩
      rw [hinter, hfullUnion] at hmeasure
      change Tendsto (fun N => (mu (cocycleCheapSet f a N)ᶜ).toReal)
        atTop (nhds 0)
      exact (ENNReal.tendsto_toReal_zero_iff
        (fun N => measure_ne_top mu (cocycleCheapSet f a N)ᶜ)).2 hmeasure
    have hboundN (N : ℕ) :
        c ≤ a + C * mu.real (cocycleCheapSet f a N)ᶜ := by
      have hbad_meas := measurable_cocycleBadIndicator hf a N
      have hbad_int : Integrable (cocycleBadIndicator f a N) mu := by
        apply Integrable.of_bound hbad_meas.aestronglyMeasurable 1
        exact Filter.Eventually.of_forall fun x => by
          have hnonneg := cocycleBadIndicator_nonneg f a N x
          have hle : cocycleBadIndicator f a N x ≤ 1 := by
            classical
            rw [cocycleBadIndicator, Set.indicator_apply]
            split <;> simp
          simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
      have hfor_m : ∀ m : ℕ, 0 < m →
          c ≤ a + C * N / m +
            C * mu.real (cocycleCheapSet f a N)ᶜ := by
        intro m hm
        have hfm : Integrable (f m) mu := by
          apply Integrable.of_bound (hf m).aestronglyMeasurable (B * m)
          exact Filter.Eventually.of_forall fun x => by
            simpa [Real.norm_eq_abs] using hbound m x
        have hsumInt := integrable_birkhoffSum hT hbad_int m
        have hpoint := subadditiveCocycle_stopping_bound
          hzero hsub hB hbound a N m
        have hintegral : (∫ x, f m x ∂mu) ≤
            a * m + C * N + C *
              (m * mu.real (cocycleCheapSet f a N)ᶜ) := by
          have hconstInt : Integrable
              (fun _ : M => a * (m : ℝ) + C * (N : ℝ)) mu :=
            integrable_const _
          have hvarInt : Integrable
              (fun x => C * birkhoffSum T (cocycleBadIndicator f a N) m x) mu :=
            hsumInt.const_mul C
          have hrhsInt : Integrable
              (fun x => a * (m : ℝ) + C * (N : ℝ) + C *
                birkhoffSum T (cocycleBadIndicator f a N) m x) mu :=
            hconstInt.add hvarInt
          calc
            (∫ x, f m x ∂mu) ≤
                ∫ x, a * m + C * N + C *
                  birkhoffSum T (cocycleBadIndicator f a N) m x ∂mu := by
              apply integral_mono hfm hrhsInt
              intro x
              simpa [C] using hpoint x
            _ = a * m + C * N + C *
                (m * mu.real (cocycleCheapSet f a N)ᶜ) := by
              rw [integral_add hconstInt hvarInt, integral_const,
                integral_const_mul, integral_birkhoffSum hT hbad_int m,
                integral_cocycleBadIndicator mu hf a N]
              simp [measureReal_def]
        have hc_m := hupper_integral m hm
        have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
        calc
          c ≤ (∫ x, f m x ∂mu) / m := hc_m
          _ ≤ (a * m + C * N + C *
                (m * mu.real (cocycleCheapSet f a N)ᶜ)) / m :=
            div_le_div_of_nonneg_right hintegral hmreal.le
          _ = a + C * N / m +
                C * mu.real (cocycleCheapSet f a N)ᶜ := by
            field_simp [hmreal.ne']
      have htend : Tendsto
          (fun m : ℕ => a + C * N / m +
            C * mu.real (cocycleCheapSet f a N)ᶜ)
          atTop (nhds (a + C * mu.real (cocycleCheapSet f a N)ᶜ)) := by
        have hz := tendsto_const_div_atTop_nhds_zero_nat (C * N)
        simpa only [add_zero] using
          (tendsto_const_nhds.add hz).add tendsto_const_nhds
      apply ge_of_tendsto htend
      filter_upwards [eventually_gt_atTop 0] with m hm
      exact hfor_m m hm
    have hlimit : Tendsto
        (fun N => a + C * mu.real (cocycleCheapSet f a N)ᶜ)
        atTop (nhds a) := by
      simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hbad_tend)
    have hca : c ≤ a := ge_of_tendsto' hlimit hboundN
    exact (not_le_of_gt hac) hca
  have hcd_eq : c = d := le_antisymm hcd hdc
  filter_upwards [hc, hd] with x hcx hdx
  have heq : liminf (u x) atTop = limsup (u x) atTop := by
    have hcx' : upper x = c := by simpa [Function.const_def] using hcx
    have hdx' : lower x = d := by simpa [Function.const_def] using hdx
    change lower x = upper x
    rw [hdx', hcx', hcd_eq]
  apply tendsto_order.2
  constructor
  · intro b hb
    apply eventually_lt_of_lt_liminf
    · rw [heq]
      exact hb
    · exact hu_lower x
  · intro b hb
    exact eventually_lt_of_limsup_lt hb (hu_upper x)

end Submission.Helpers
