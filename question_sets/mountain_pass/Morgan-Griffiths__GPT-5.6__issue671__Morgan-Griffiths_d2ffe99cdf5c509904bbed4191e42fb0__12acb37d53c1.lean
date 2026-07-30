import Mathlib

namespace Submission

namespace LeanEval
namespace Analysis
namespace MountainPassProblem

/-!
# Mountain Pass Theorem (Ambrosetti–Rabinowitz 1973)

A `C¹` functional `f` on a real Banach space `E` satisfying the
Palais–Smale compactness condition and having a *mountain range*
geometry separating two points `a, b` admits a critical point at the
mini-max level `c = inf_γ sup_t f(γ t)`, and `c ≥ ε > 0`.
Ambrosetti–Rabinowitz 1973. The statement is listed as §119 in Knill's
*Some Fundamental Theorems in Mathematics*.

Knill writes the far point condition as "`f(b) ≤ 0` for some `|b| > ε`".
The radius of the sphere is `r`, not `ε`, so `|b| > ε` is a
transcription slip for `r < ‖b − a‖`. The faithful condition encoded
here is the translated Ambrosetti–Rabinowitz geometry: `f a = 0`,
`f ≥ ε` on `Metric.sphere a r`, and `r < ‖b − a‖`.
-/

open scoped unitInterval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- `x` is a **critical point** of `f` when `f'(x) = 0`. -/
def IsCriticalPoint (f : E → ℝ) (x : E) : Prop :=
  fderiv ℝ f x = 0

/-- `f` satisfies **Palais–Smale**: every sequence along which `f` is
bounded and `f'` tends to `0` admits a convergent subsequence. -/
def PalaisSmale (f : E → ℝ) : Prop :=
  ∀ u : ℕ → E, (∃ M : ℝ, ∀ k, |f (u k)| ≤ M) →
      Filter.Tendsto (fun k => fderiv ℝ f (u k)) Filter.atTop (nhds 0) →
      ∃ (x : E) (φ : ℕ → ℕ), StrictMono φ ∧
        Filter.Tendsto (u ∘ φ) Filter.atTop (nhds x)

/-- `a, b` are separated by a **mountain range** at height `ε`, radius
`r`: `f a = 0`, `f ≥ ε > 0` on the sphere `S_r(a)`, and `f b ≤ 0` for
some `b` strictly outside that sphere. -/
def MountainRange (f : E → ℝ) (a b : E) (ε r : ℝ) : Prop :=
  f a = 0 ∧ 0 < ε ∧ 0 < r ∧
    (∀ y ∈ Metric.sphere a r, ε ≤ f y) ∧ r < ‖b - a‖ ∧ f b ≤ 0

/-- The **mini-max value** over continuous paths from `a` to `b`:
`c = inf_γ sup_t f(γ t)`. -/
noncomputable def mountainPassLevel (f : E → ℝ) (a b : E) : ℝ :=
  ⨅ γ : Path a b, ⨆ t : I, f (γ t)



end MountainPassProblem
end Analysis
end LeanEval

open LeanEval.Analysis.MountainPassProblem
open scoped unitInterval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/

/-- A continuous path from the centre to a point outside the ball meets its
    boundary.  The domain of a `Path` is the (preconnected) compact unit
    interval; phrasing the argument there avoids choosing a parametrisation
    on all of `ℝ`. -/
lemma path_meets_sphere {a b : E} {r : ℝ} (hr : 0 < r)
    (hb : r < ‖b - a‖) (γ : Path a b) :
    ∃ t : I, γ t ∈ Metric.sphere a r := by
  let d : I → ℝ := fun t => dist (γ t) a
  have hd : Continuous d := by
    dsimp [d]
    fun_prop
  have h0 : d (0 : I) ≤ (fun _ : I => r) 0 := by
    change dist (γ (0 : I)) a ≤ r
    rw [γ.source]
    simpa using (le_of_lt hr)
  have h1 : (fun _ : I => r) 1 ≤ d (1 : I) := by
    change r ≤ dist (γ (1 : I)) a
    rw [γ.target, dist_eq_norm]
    exact le_of_lt hb
  obtain ⟨t, ht⟩ :=
    intermediate_value_univ₂ (X := I) (α := ℝ) hd continuous_const h0 h1
  refine ⟨t, ?_⟩
  apply (Metric.mem_sphere).2
  exact ht

/-- The values of a continuous real function on any path are bounded above.
    This is often the useful way to use the conditionally complete `iSup`
    on `ℝ`. -/
lemma bddAbove_path_values {a b : E} {f : E → ℝ}
    (hf : Continuous f) (γ : Path a b) :
    BddAbove (Set.range (fun t : I => f (γ t))) := by
  have hc : Continuous (fun t : I => f (γ t)) := hf.comp γ.continuous
  have hK : IsCompact (Set.range (fun t : I => f (γ t))) := by
    simpa only [Set.image_univ] using (isCompact_univ.image hc)
  exact hK.bddAbove

/-- The elementary, geometric half of the mountain pass argument.  It is
    independent of compactness: every individual path crosses the high
    sphere. -/
lemma mountainPassLevel_ge_of_continuous (f : E → ℝ) (hf : Continuous f)
    {a b : E} {ε r : ℝ} (hmr : MountainRange f a b ε r) :
    ε ≤ mountainPassLevel f a b := by
  rcases hmr with ⟨ha, hε, hr, hsph, hb, hfb⟩
  -- the affine segment supplies non-emptiness of the type of paths; this is
  -- needed for the conditionally complete infimum on the reals.
  letI : Nonempty (Path a b) := ⟨Path.segment a b⟩
  -- now bound each of the suprema from below
  unfold mountainPassLevel
  apply le_ciInf
  intro γ
  obtain ⟨t, ht⟩ := path_meets_sphere (a := a) (b := b) hr hb γ
  have hval : ε ≤ f (γ t) := hsph _ ht
  exact le_trans hval (le_ciSup (bddAbove_path_values hf γ) t)



/-- Once a Palais--Smale sequence at a prescribed level has been found, the
    rather useful part of the Palais--Smale hypothesis is completely
    sequential.  Notice that neither compactness of level sets nor a choice
    of a minimizing point is needed here. -/
lemma critical_of_ps_sequence (f : E → ℝ) (hf : ContDiff ℝ 1 f)
    (hps : PalaisSmale f) {c : ℝ} (u : ℕ → E)
    (hu : Filter.Tendsto (fun n => f (u n)) Filter.atTop (nhds c))
    (hu' : Filter.Tendsto (fun n => fderiv ℝ f (u n))
      Filter.atTop (nhds 0)) :
    ∃ x : E, IsCriticalPoint f x ∧ f x = c := by
  have hb : ∃ M : ℝ, ∀ k, |f (u k)| ≤ M := by
    have hb' : Bornology.IsBounded (Set.range (fun n : ℕ => f (u n))) :=
      Metric.isBounded_range_of_tendsto (fun n : ℕ => f (u n)) hu
    obtain ⟨R, hR⟩ :=
      (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hb'
    refine ⟨R, ?_⟩
    intro k
    have hk : f (u k) ∈ Metric.closedBall (0 : ℝ) R :=
      hR (Set.mem_range_self k)
    have hk' : dist (f (u k)) 0 ≤ R := (Metric.mem_closedBall).1 hk
    simpa [Real.dist_eq] using hk'
  obtain ⟨x, φ, hφ, hx⟩ := hps u hb hu'
  have hφ' : Filter.Tendsto φ Filter.atTop Filter.atTop := hφ.tendsto_atTop
  have hfc : Filter.Tendsto (fun n => f (u (φ n))) Filter.atTop (nhds c) := by
    simpa [Function.comp_def] using hu.comp hφ'
  have hfx : Filter.Tendsto (fun n => f (u (φ n)))
      Filter.atTop (nhds (f x)) := by
    simpa [Function.comp_def] using
      hf.continuous.continuousAt.tendsto.comp hx
  have heq : f x = c := tendsto_nhds_unique hfx hfc
  have hdc : Continuous (fderiv ℝ f) :=
    hf.continuous_fderiv (by exact one_ne_zero)
  have hd0 : Filter.Tendsto (fun n => fderiv ℝ f (u (φ n)))
      Filter.atTop (nhds 0) := by
    simpa [Function.comp_def] using hu'.comp hφ'
  have hdx : Filter.Tendsto (fun n => fderiv ℝ f (u (φ n)))
      Filter.atTop (nhds (fderiv ℝ f x)) := by
    simpa [Function.comp_def] using hdc.continuousAt.tendsto.comp hx
  refine ⟨x, ?_, heq⟩
  exact tendsto_nhds_unique hdx hd0


/-- On a single path the supremum in the definition really is a maximum.
    This also records the upper bound needed by lemmas about the
    conditionally-complete supremum of reals. -/
lemma path_height_attained {f : E → ℝ} (hf : Continuous f)
    {a b : E} (γ : Path a b) :
    ∃ t : I, (⨆ s : I, f (γ s)) = f (γ t) ∧
      ∀ s : I, f (γ s) ≤ f (γ t) := by
  have hc : Continuous (fun s : I => f (γ s)) := hf.comp γ.continuous
  obtain ⟨t, ht, hmax⟩ :=
    (isCompact_univ.exists_isMaxOn (by exact ⟨(0 : I), Set.mem_univ _⟩)
      hc.continuousOn)
  have hmax' : ∀ s : I, f (γ s) ≤ f (γ t) := by
    intro s
    exact hmax (Set.mem_univ s)
  refine ⟨t, ?_, hmax'⟩
  apply le_antisymm
  · exact ciSup_le hmax'
  · exact le_ciSup (bddAbove_path_values hf γ) t

/-- There are paths of height arbitrarily close to the minimax value,
from above.  Writing down the bounded-below argument is important for
`ℝ`'s conditional infimum. -/
lemma exists_path_height_lt (f : E → ℝ) (hf : Continuous f)
    {a b : E} {ε r d : ℝ} (hmr : MountainRange f a b ε r)
    (hd : 0 < d) :
    ∃ γ : Path a b,
      (⨆ t : I, f (γ t)) < mountainPassLevel f a b + d := by
  letI : Nonempty (Path a b) := ⟨Path.segment a b⟩
  have hlower : ε ≤ mountainPassLevel f a b :=
    mountainPassLevel_ge_of_continuous f hf hmr
  have hbdd : BddBelow
      (Set.range (fun γ : Path a b => (⨆ t : I, f (γ t)))) := by
    refine ⟨ε, ?_⟩
    rintro z ⟨γ, rfl⟩
    rcases hmr with ⟨ha, hε, hr, hsph, hb, hfb⟩
    obtain ⟨t, ht⟩ := path_meets_sphere (a := a) (b := b) hr hb γ
    exact le_trans (hsph _ ht)
      (le_ciSup (bddAbove_path_values hf γ) t)
  have hlt : (⨅ γ : Path a b, (⨆ t : I, f (γ t)))
      < mountainPassLevel f a b + d := by
    rw [mountainPassLevel]
    exact lt_add_of_pos_right _ hd
  simpa [mountainPassLevel] using
    ((ciInf_lt_iff hbdd).1 (by simpa [mountainPassLevel] using hlt))


/-- A convenient sequential form of the approximate-critical-point step.
    Neither minimax arguments nor compactness enter this lemma; it just turns
    the usual `1/(n+1)` approximations into the two convergences in a
    Palais--Smale sequence. -/
lemma ps_sequence_of_approx (f : E → ℝ) (c : ℝ)
    (h : ∀ d : ℝ, 0 < d → ∃ x : E,
      |f x - c| < d ∧ ‖fderiv ℝ f x‖ < d) :
    ∃ u : ℕ → E,
      Filter.Tendsto (fun n => f (u n)) Filter.atTop (nhds c) ∧
      Filter.Tendsto (fun n => fderiv ℝ f (u n))
        Filter.atTop (nhds 0) := by
  classical
  have hd (n : ℕ) : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by
    positivity
  choose u hu using (fun n : ℕ => h ((1 : ℝ) / ((n : ℝ) + 1)) (hd n))
  have ht : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
      Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨u, ?_, ?_⟩
  · apply (tendsto_iff_norm_sub_tendsto_zero).2
    have hz : Filter.Tendsto (fun n : ℕ => ‖f (u n) - c‖)
        Filter.atTop (nhds 0) := by
      apply squeeze_zero (fun n => norm_nonneg _)
        (fun n => ?_) ht
      simpa [Real.norm_eq_abs] using (le_of_lt (hu n).1)
    exact hz
  · apply squeeze_zero_norm (f := fun n => fderiv ℝ f (u n))
      (a := fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) ?_ ht
    intro n
    exact le_of_lt (hu n).2


/-- In particular the number `c` is a genuine value limit (without the
    derivative assertion): points on almost optimal paths have values
    arbitrarily close to it. -/
lemma exists_point_near_mountainPassLevel (f : E → ℝ) (hf : Continuous f)
    {a b : E} {ε r d : ℝ} (hmr : MountainRange f a b ε r)
    (hd : 0 < d) : ∃ x : E, |f x - mountainPassLevel f a b| < d := by
  letI : Nonempty (Path a b) := ⟨Path.segment a b⟩
  obtain ⟨γ, hγ⟩ := exists_path_height_lt f hf hmr hd
  obtain ⟨t, ht, _⟩ := path_height_attained hf γ
  have hb : BddBelow
      (Set.range (fun γ : Path a b => (⨆ t : I, f (γ t)))) := by
    rcases hmr with ⟨ha, hε, hr, hsph, hb', hfb⟩
    refine ⟨ε, ?_⟩
    rintro z ⟨p, rfl⟩
    obtain ⟨u, hu⟩ := path_meets_sphere (a := a) (b := b) hr hb' p
    exact le_trans (hsph _ hu)
      (le_ciSup (bddAbove_path_values hf p) u)
  have hbelow : mountainPassLevel f a b ≤ f (γ t) := by
    rw [mountainPassLevel]
    have hi : (⨅ p : Path a b, ⨆ t : I, f (p t)) ≤
        (⨆ t : I, f (γ t)) := ciInf_le hb γ
    simpa [ht] using hi
  refine ⟨γ t, ?_⟩
  rw [abs_lt]
  constructor
  · -- the lower bound is even zero
    have hnon : 0 ≤ f (γ t) - mountainPassLevel f a b := sub_nonneg.2 hbelow
    exact lt_of_lt_of_le (neg_lt_zero.mpr hd) hnon
  · have hh : f (γ t) < mountainPassLevel f a b + d := by
      simpa [ht] using hγ
    linarith


/-- From the definition of the operator norm, a functional whose norm is
larger than `q` has, on the unit sphere, a direction in which its value is
larger than `q`.  This little lemma is the local linear ingredient in
pseudo-gradient/deformation arguments; it does not use a Hilbert-space
identification. -/
lemma exists_unit_apply_gt {L : E →L[ℝ] ℝ} {q : ℝ}
    (hq : 0 ≤ q) (hL : q < ‖L‖) :
    ∃ v : E, ‖v‖ = 1 ∧ q < L v := by
  classical
  have habs : ∃ v : E, ‖v‖ = 1 ∧ q < ‖L v‖ := by
    by_contra hn
    push Not at hn
    have hop : ‖L‖ ≤ q := by
      apply L.opNorm_le_bound hq
      intro x
      by_cases hx : x = 0
      · simp [hx, hq]
      · have hxnorm : 0 < ‖x‖ := (norm_pos_iff.mpr hx)
        let y : E := (‖x‖)⁻¹ • x
        have hy : ‖y‖ = 1 := by
          simp [y, norm_smul, abs_of_nonneg (le_of_lt hxnorm), hx]
        have hyy : ‖L y‖ ≤ q := hn y hy
        -- Undo the normalization.
        have hcal : ‖L y‖ = (‖x‖)⁻¹ * ‖L x‖ := by
          rw [show L y = (‖x‖)⁻¹ • L x by simp [y]]
          rw [norm_smul]
          have hx0 : 0 ≤ ‖x‖ := norm_nonneg _
          simp [abs_inv, abs_of_nonneg hx0]
        rw [hcal] at hyy
        have hmul : ‖L x‖ ≤ q * ‖x‖ := by
          have := (mul_le_mul_of_nonneg_right hyy (le_of_lt hxnorm))
          -- cancellation of the normalization factor
          have hxne : ‖x‖ ≠ 0 := ne_of_gt hxnorm
          have heqi : ‖L x‖ = ‖x‖⁻¹ * ‖L x‖ * ‖x‖ := by
            calc
              ‖L x‖ = ‖L x‖ * (‖x‖⁻¹ * ‖x‖) := by
                simp [hxne]
              _ = ‖x‖⁻¹ * ‖L x‖ * ‖x‖ := by ring
          rw [heqi]
          exact this
        exact hmul
    exact (not_lt_of_ge hop hL)
  obtain ⟨v, hv, hlarge⟩ := habs
  -- choose a sign; the norm inequality is about absolute value on `ℝ`.
  have hab : q < |L v| := by simpa [Real.norm_eq_abs] using hlarge
  by_cases hs : 0 ≤ L v
  · exact ⟨v, hv, lt_of_lt_of_le hab (le_of_eq (abs_of_nonneg hs))⟩
  · have hs' : L v ≤ 0 := le_of_not_ge hs
    refine ⟨-v, by simpa using hv, ?_⟩
    have : q < -(L v) := by simpa [abs_of_nonpos hs'] using hab
    simpa using this

/-- The other order inequality for a fixed path. -/
lemma mountainPassLevel_le_height (f : E → ℝ) (hf : Continuous f)
    {a b : E} {ε r : ℝ} (hmr : MountainRange f a b ε r)
    (γ : Path a b) :
    mountainPassLevel f a b ≤ (⨆ t : I, f (γ t)) := by
  letI : Nonempty (Path a b) := ⟨γ⟩
  rcases hmr with ⟨ha, he, hr, hs, hb, hfb⟩
  have hbelow : BddBelow
      (Set.range (fun p : Path a b => (⨆ t : I, f (p t)))) := by
    refine ⟨ε, ?_⟩
    rintro _ ⟨p, rfl⟩
    obtain ⟨t, ht⟩ := path_meets_sphere (a := a) (b := b) hr hb p
    exact le_trans (hs _ ht) (le_ciSup (bddAbove_path_values hf p) t)
  exact ciInf_le hbelow γ


/-- A useful first (purely topological) part of the deformation argument.
If the differential is uniformly different from zero on a strip, one can
choose a *continuous* field of convex combinations of good directions.
The construction uses a partition of unity; no vector is chosen
continuously by norm-attainment.  It is often the step of the mountain
pass proof where a Hilbert-space gradient would otherwise be silently
used. -/
lemma exists_continuous_strip_direction (f : E → ℝ) (hf : ContDiff ℝ 1 f)
    (c d : ℝ) (hd : 0 < d)
    (hn : ∀ x : E, |f x - c| < d → d ≤ ‖fderiv ℝ f x‖) :
    ∃ (V : E → E) (δ : C(E, ℝ)),
      Continuous V ∧ (∀ x, 0 < δ x) ∧
      (∀ x, ‖V x‖ ≤ 1) ∧
      (∀ x, |f x - c| ≤ d / 2 →
        ∀ y ∈ Metric.closedBall x (δ x),
          d / 3 ≤ (fderiv ℝ f y) (V x)) := by
  classical
  let good : Set E := {x | |f x - c| < d}
  have hdc : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by exact one_ne_zero)
  -- For every point of the strip choose a direction with ample slack.
  have hex (x : E) (hx : x ∈ good) :
      ∃ v : E, ‖v‖ = 1 ∧ (3*d/4 : ℝ) < (fderiv ℝ f x) v := by
    have hh : d ≤ ‖fderiv ℝ f x‖ := hn x hx
    apply exists_unit_apply_gt (E := E) (L := fderiv ℝ f x)
      (q := (3*d/4 : ℝ)) (by linarith)
    linarith
  let w : Option E → E
    | none => 0
    | some x => if hx : x ∈ good then Classical.choose (hex x hx) else 0
  have hw (x : E) (hx : x ∈ good) :
      ‖w (some x)‖ = 1 ∧ (3*d/4 : ℝ) < (fderiv ℝ f x) (w (some x)) := by
    dsimp [w]
    split <;> rename_i h
    · exact Classical.choose_spec (hex x h)
    · exact False.elim (h hx)
  -- the open cover consists of good-direction neighbourhoods and one
  -- extra, zero, direction off the smaller closed strip
  let U : Option E → Set E
    | none => {x | |f x - c| > d / 2}
    | some x => if x ∈ good then
        {y | d / 2 < (fderiv ℝ f y) (w (some x))} else ∅
  have hU : ∀ i, IsOpen (U i) := by
    intro i
    cases i with
    | none =>
        dsimp [U]
        exact isOpen_lt continuous_const
          ((hf.continuous.sub continuous_const).abs)
    | some x =>
        dsimp [U]
        split <;> rename_i hx
        · exact isOpen_lt continuous_const (hdc.clm_apply continuous_const)
        · exact isOpen_empty
  have hcover : (Set.univ : Set E) ⊆ ⋃ i, U i := by
    intro x hx
    by_cases hs : |f x - c| ≤ d / 2
    · have hg : x ∈ good := by
        change |f x - c| < d
        linarith
      have hgt := (hw x hg).2
      have hin : x ∈ U (some x) := by
        dsimp [U]
        simp [hg]
        linarith
      exact Set.mem_iUnion.2 ⟨some x, hin⟩
    · have hin : x ∈ U none := by
        change |f x - c| > d / 2
        linarith
      exact Set.mem_iUnion.2 ⟨none, hin⟩
  obtain ⟨ρ, hρ⟩ :=
    PartitionOfUnity.exists_isSubordinate (ι := Option E)
      (X := E) (s := (Set.univ : Set E)) isClosed_univ U hU hcover
  have hfin := ρ.locallyFinite_tsupport
  -- Enlarge the neighbourhoods a little bit; on their closures a
  -- uniform (but point-dependent) radius may be chosen continuously.
  let W : Option E → Set E
    | none => Set.univ
    | some x => {y | d / 3 < (fderiv ℝ f y) (w (some x))}
  have hW : ∀ i, IsOpen (W i) := by
    intro i
    cases i with
    | none => exact isOpen_univ
    | some x =>
      exact isOpen_lt continuous_const (hdc.clm_apply continuous_const)
  have hsub : ∀ i, tsupport (ρ i) ⊆ W i := by
    intro i z hz
    have hz' := hρ i hz
    cases i with
    | none => trivial
    | some x =>
      dsimp [U] at hz'
      dsimp [W]
      split at hz'
      · change d / 2 < (fderiv ℝ f z) (w (some x)) at hz'
        have hh : d / 3 < d / 2 := by linarith
        exact hh.trans hz' 
      · exact False.elim (by simpa using hz')
  obtain ⟨δ, hδ, hδU⟩ :=
    Metric.exists_continuous_real_forall_closedBall_subset
      (K := fun i : Option E => tsupport (ρ i)) (U := W)
      (fun i => isClosed_closure) hW hsub hfin
  let V : E → E := fun x => ∑ᶠ i : Option E, (ρ i x) • w i
  have hVc : Continuous V := by
    dsimp [V]
    apply ρ.continuous_finsum_smul
    intro i z hz
    exact continuousAt_const
  refine ⟨V, δ, hVc, hδ, ?_, ?_⟩
  · intro x
    rw [show V x = ∑ i ∈ ρ.finsupport x, (ρ i x) • w i by
      dsimp [V]; exact (ρ.sum_finsupport_smul_eq_finsum (fun i _ => w i)).symm]
    calc
      ‖∑ i ∈ ρ.finsupport x, ρ i x • w i‖
          ≤ ∑ i ∈ ρ.finsupport x, ‖ρ i x • w i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ ρ.finsupport x, (ρ i x) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_smul]
        have hle : ‖w i‖ ≤ 1 := by
          cases i with
          | none => simp [w]
          | some z =>
            by_cases hz : z ∈ good
            · have hz' := (hw z hz).1
              simpa [w, hz] using hz'.le
            · simp [w, hz]
        rw [Real.norm_eq_abs, abs_of_nonneg (ρ.nonneg i x)]
        exact (mul_le_of_le_one_right (ρ.nonneg i x) hle)
      _ = 1 := ρ.sum_finsupport (by trivial)
  · intro x hx y hy
    -- At a point of the closed inner strip the extra index `none`
    -- has zero weight.  Every remaining summand has derivative at least
    -- `d/3` throughout the chosen ball.
    have hnone : ρ none x = 0 := by
      by_contra hne
      have hmem : x ∈ tsupport (ρ none) :=
        subset_closure (hne)
      have := hρ none hmem
      change |f x - c| > d / 2 at this
      linarith
    have hterm : ∀ i ∈ ρ.finsupport x,
        d / 3 ≤ (fderiv ℝ f y) (w i) := by
      intro i hi
      have hi' : x ∈ tsupport (ρ i) := by
        exact subset_closure ((ρ.mem_finsupport x).1 hi)
      have hy' : y ∈ W i := hδU i x hi' hy
      cases i with
      | none =>
          have : ρ none x ≠ 0 := (ρ.mem_finsupport x).1 hi
          exact False.elim (this hnone)
      | some z =>
          dsimp [W] at hy'
          exact le_of_lt hy'
    -- linearity turns the finite convex sum into the same convex sum
    -- of scalar values.
    rw [show V x = ∑ i ∈ ρ.finsupport x, (ρ i x) • w i by
      dsimp [V]; exact (ρ.sum_finsupport_smul_eq_finsum (fun i _ => w i)).symm]
    rw [map_sum]
    -- estimate the weighted scalar sum
    have hsum :
        ∑ i ∈ ρ.finsupport x, (ρ i x) * (d / 3)
          ≤ ∑ i ∈ ρ.finsupport x, (ρ i x) *
              ((fderiv ℝ f y) (w i)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hterm i hi) (ρ.nonneg i x)
    have hone : ∑ i ∈ ρ.finsupport x, ρ i x = 1 :=
      ρ.sum_finsupport (by trivial)
    -- `map_smul` on a real functional and elementary finite-sum algebra
    calc
      d / 3 = ∑ i ∈ ρ.finsupport x, (ρ i x) * (d / 3) := by
        rw [← Finset.sum_mul, hone, one_mul]
      _ ≤ ∑ i ∈ ρ.finsupport x, (ρ i x) *
              ((fderiv ℝ f y) (w i)) := hsum
      _ = _ := by simp [map_smul]


/-- Discrete version of the pseudogradient construction.  The step length
is allowed to vary with the point (so an ODE is not involved). -/
lemma exists_strip_descent_step (f : E → ℝ) (hf : ContDiff ℝ 1 f)
    (c d : ℝ) (hd : 0 < d)
    (hn : ∀ x : E, |f x - c| < d → d ≤ ‖fderiv ℝ f x‖) :
    ∃ (T : E → E) (step : E → ℝ),
      Continuous T ∧ Continuous step ∧
      (∀ x, 0 ≤ step x) ∧
      (∀ x, |f x - c| < d / 2 → 0 < step x) ∧
      (∀ x, d / 2 ≤ |f x - c| → T x = x ∧ step x = 0) ∧
      (∀ x, ‖T x - x‖ ≤ step x) ∧
      (∀ x, d / 3 * step x ≤ f x - f (T x)) := by
  classical
  obtain ⟨V, δ, hVc, hδ, hVn, hVd⟩ :=
    exists_continuous_strip_direction (E:=E) f hf c d hd hn
  let cut : E → ℝ := fun x => max 0 ((d / 2 - |f x - c|) / (d / 2))
  have hcutc : Continuous cut := by
    dsimp [cut]
    fun_prop
  have hcut0 (x : E) : 0 ≤ cut x := le_max_left _ _
  have hcut1 (x : E) : cut x ≤ 1 := by
    dsimp [cut]
    apply (max_le_iff).2
    constructor
    · exact zero_le_one
    · apply (div_le_one (by linarith : 0 < d/2)).2
      have := abs_nonneg (f x - c)
      linarith
  have hcut_pos {x : E} (hx : |f x - c| < d / 2) : 0 < cut x := by
    dsimp [cut]
    exact lt_max_of_lt_right (div_pos (sub_pos.mpr hx) (by linarith))
  have hcut_z {x : E} (hx : d / 2 ≤ |f x - c|) : cut x = 0 := by
    dsimp [cut]
    rw [max_eq_left]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (by linarith)
  let step : E → ℝ := fun x => (δ x / 2) * cut x
  have hstepc : Continuous step := by
    dsimp [step]
    exact (δ.continuous.div_const (2:ℝ)).mul hcutc
  have hstep0 (x : E) : 0 ≤ step x := by
    dsimp [step]
    exact mul_nonneg (by have := hδ x; linarith) (hcut0 x)
  have hstep_pos {x : E} (hx : |f x - c| < d / 2) : 0 < step x := by
    dsimp [step]
    exact mul_pos (by have := hδ x; linarith) (hcut_pos hx)
  have hstep_le (x : E) : step x ≤ δ x := by
    dsimp [step]
    calc
      δ x / 2 * cut x ≤ δ x / 2 * 1 :=
        mul_le_mul_of_nonneg_left (hcut1 x) (by linarith [hδ x])
      _ ≤ δ x := by linarith [hδ x]
  let T : E → E := fun x => x - (step x) • V x
  have hTc : Continuous T := by
    dsimp [T]
    exact continuous_id.sub (hstepc.smul hVc)
  refine ⟨T, step, hTc, hstepc, hstep0,
    (fun x hx => hstep_pos hx), ?_, ?_, ?_⟩
  · intro x hx
    have hz : cut x = 0 := hcut_z hx
    have hs : step x = 0 := by simp [step, hz]
    simp [T, hs]
  · intro x
    dsimp [T]
    have hn' := hVn x
    -- the distance moved is no more than the chosen step
    rw [sub_sub_cancel_left]
    rw [norm_neg, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (hstep0 x)]
    exact mul_le_of_le_one_right (hstep0 x) hn'
  · intro x
    by_cases hz : step x = 0
    · simp [T, hz]
    · have hspos : 0 < step x := lt_of_le_of_ne (hstep0 x) (Ne.symm hz)
      have hband : |f x - c| ≤ d / 2 := by
        by_contra hh
        have hh' : d / 2 ≤ |f x - c| := le_of_lt (lt_of_not_ge hh)
        have : step x = 0 := by simp [step, hcut_z hh']
        exact hz this
      -- Any point of the segment stays in all the balls used for the
      -- convex-combination estimate.
      have hball : ∀ t ∈ Set.Icc (0:ℝ) (step x),
          x - t • V x ∈ Metric.closedBall x (δ x) := by
        intro t ht
        apply (Metric.mem_closedBall).2
        rw [dist_eq_norm]
        calc
          ‖x - t • V x - x‖ = |t| * ‖V x‖ := by
            rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs]
          _ ≤ t := by
            rw [abs_of_nonneg ht.1]
            exact mul_le_of_le_one_right ht.1 (hVn x)
          _ ≤ δ x := ht.2.trans (hstep_le x)
      let g : ℝ → ℝ := fun t => f (x - t • V x) + (d / 3) * t
      have hgcont : Continuous g := by
        dsimp [g]
        fun_prop
      have hder (t : ℝ) : HasDerivAt (fun s : ℝ => x - s • V x) (- V x) t := by
        simpa using ((hasDerivAt_id t).smul_const (V x)).const_sub x
      have hdg (t : ℝ) :
          HasDerivAt g (- (fderiv ℝ f (x - t • V x)) (V x) + d/3) t := by
        have hfa : DifferentiableAt ℝ f (x - t • V x) := (hf.differentiable (by exact one_ne_zero)) _
        have hcomp := hfa.hasFDerivAt.comp t (hder t).hasFDerivAt
        have hcomp' := hcomp.hasDerivAt
        dsimp [Function.comp_def] at hcomp'
        -- chain rule and the derivative of a linear function of time
        convert hcomp'.add ((hasDerivAt_id t).const_mul (d/3)) using 1 <;>
          try {rfl} <;> try {ext z; rfl}
        simp [map_neg]
      have hanti : AntitoneOn g (Set.Icc (0:ℝ) (step x)) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
          hgcont.continuousOn
        · intro t ht
          exact (hdg t).differentiableAt.differentiableWithinAt
        · intro t ht
          rw [interior_Icc] at ht
          have hmem : t ∈ Set.Icc (0:ℝ) (step x) :=
            ⟨le_of_lt ht.1, le_of_lt ht.2⟩
          rw [(hdg t).deriv]
          have hl := hVd x hband (x - t • V x) (hball t hmem)
          linarith
      have hh := hanti (by exact ⟨le_rfl, le_of_lt hspos⟩)
        (by exact ⟨le_of_lt hspos, le_rfl⟩) (le_of_lt hspos)
      change f (x - step x • V x) + d / 3 * step x ≤
          f (x - (0:ℝ) • V x) + d / 3 * 0 at hh
      have hh' : f (x - step x • V x) + d / 3 * step x ≤ f x := by
        simpa using hh
      change d / 3 * step x ≤ f x - f (T x)
      dsimp [T]
      linarith

/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem mountain_pass (f : E → ℝ) (_hf : ContDiff ℝ 1 f) (_hps : PalaisSmale f)
    {a b : E} {ε r : ℝ} (_hmr : MountainRange f a b ε r) :
    ∃ x : E, IsCriticalPoint f x ∧
      f x = mountainPassLevel f a b ∧ ε ≤ mountainPassLevel f a b :=
/-ResultProofBegin-/by
  have hc : ε ≤ mountainPassLevel f a b :=
    mountainPassLevel_ge_of_continuous f _hf.continuous _hmr
  have happ : ∀ d : ℝ, 0 < d → ∃ x : E,
      |f x - mountainPassLevel f a b| < d ∧ ‖fderiv ℝ f x‖ < d := by
    classical
    by_contra hn
    push Not at hn
    obtain ⟨d, hd, hstrip⟩ := hn
    -- Shrink the strip once. This harmless normalization is what makes the
    -- deformation fix both endpoints (their values are at most zero).
    have heps : 0 < ε := _hmr.2.1
    let D : ℝ := min (d/2) (ε/2)
    have hD : 0 < D := by dsimp [D]; exact lt_min (by linarith) (by linarith)
    have hDlt : D < ε := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hDle : D ≤ d := le_trans (min_le_left _ _) (by linarith)
    have hDstrip : ∀ x : E, |f x - mountainPassLevel f a b| < D →
        D ≤ ‖fderiv ℝ f x‖ := by
      intro x hx
      exact le_trans hDle (hstrip x (lt_of_lt_of_le hx hDle))
    -- A discrete descent map is enough.  Unlike a flow it only uses
    -- continuous partitions of unity, available on an arbitrary Banach
    -- space.  `step` is strictly positive in the smaller strip; the last
    -- inequality is the telescoping length estimate for its iterates.
    obtain ⟨T, step, hT, hstepc, hstep0, hstepp, hfix, hmove, hdrop⟩ :=
      exists_strip_descent_step (E:=E) f _hf
        (mountainPassLevel f a b) D hD hDstrip
    have hdown (x : E) : f (T x) ≤ f x := by
      have h := hdrop x
      have hn : 0 ≤ D / 3 * step x :=
        mul_nonneg (by linarith) (hstep0 x)
      linarith
    have hlength (x : E) :
        D / 3 * ‖T x - x‖ ≤ f x - f (T x) :=
      le_trans (mul_le_mul_of_nonneg_left (hmove x)
        (by linarith : 0 ≤ D / 3)) (hdrop x)
    have hTa : T a = a := by
      have hx : D / 2 ≤ |f a - mountainPassLevel f a b| := by
        have ha : f a = 0 := _hmr.1
        rw [ha]
        rw [abs_of_nonpos (by linarith [hc] : (0:ℝ) - mountainPassLevel f a b ≤ 0)]
        linarith
      exact (hfix a hx).1
    have hTb : T b = b := by
      have hx : D / 2 ≤ |f b - mountainPassLevel f a b| := by
        have hb : f b ≤ 0 := _hmr.2.2.2.2.2
        rw [abs_of_nonpos (by linarith [hc] : f b - mountainPassLevel f a b ≤ 0)]
        linarith [hc]
      exact (hfix b hx).1
    obtain ⟨γ, hγ⟩ := exists_path_height_lt f _hf.continuous _hmr
      (by linarith : 0 < D / 4)
    obtain ⟨t, ht, htmax⟩ := path_height_attained _hf.continuous γ
    have hall : ∀ s : I,
        f (γ s) < mountainPassLevel f a b + D / 4 := by
      intro s
      have := htmax s
      have hm : f (γ t) < mountainPassLevel f a b + D/4 := by
        simpa [ht] using hγ
      linarith
    -- It remains to iterate this *one* map, not to solve an ODE.
    -- For each iterate the values decrease and travelled lengths telescope:
    have hiter (x : E) (n : ℕ) :
        f ((T^[n+1]) x) ≤ f ((T^[n]) x) := by
      induction n with
      | zero => simpa using hdown x
      | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        exact hdown _
    have hitermono (x : E) : Antitone (fun n : ℕ => f ((T^[n]) x)) := by
      apply antitone_nat_of_succ_le
      intro n
      convert hiter x n using 1 <;> simp [Nat.add_comm]
    -- Compactness of the high part of this path will turn pointwise escape
    -- of these discrete trajectories into one common iterate.
    let K : Set I := {s | mountainPassLevel f a b ≤ f (γ s)}
    have hK : IsCompact K := by
      have hcl : IsClosed K :=
        isClosed_le continuous_const (_hf.continuous.comp γ.continuous)
      exact hcl.isCompact
    -- Every point of the high part eventually drops strictly below the
    -- minimax level.  Fixing such a point, write its iterates as a sequence.
    have hesc : ∀ s : I, s ∈ K →
        ∃ n : ℕ, f ((T^[n]) (γ s)) < mountainPassLevel f a b := by
      intro s hs
      by_contra hno
      push Not at hno
      let u : ℕ → E := fun n => (T^[n]) (γ s)
      let v : ℕ → ℝ := fun n => f (u n)
      have hu_succ (n : ℕ) : u (n+1) = T (u n) := by
        dsimp [u]
        simpa [Nat.add_comm] using (Function.iterate_succ_apply' T n (γ s))
      have hv_succ (n : ℕ) : v (n+1) = f (T (u n)) := by
        simp [v, hu_succ]
      have hvlow (n : ℕ) : mountainPassLevel f a b ≤ v n := by
        dsimp [v, u]
        exact hno n
      have hvmono : Antitone v := by
        intro i j hij
        dsimp [v, u]
        exact hitermono (γ s) hij
      have hvup (n : ℕ) : v n < mountainPassLevel f a b + D / 4 := by
        have hle : v n ≤ v 0 := hvmono (Nat.zero_le n)
        have hz : v 0 < mountainPassLevel f a b + D / 4 := by
          simpa [v, u] using (hall s)
        exact lt_of_le_of_lt hle hz
      have hvband (n : ℕ) : |f (u n) - mountainPassLevel f a b| < D / 2 := by
        have h1 : mountainPassLevel f a b ≤ f (u n) := by
          simpa [v] using hvlow n
        have h2 : f (u n) < mountainPassLevel f a b + D / 4 := by
          simpa [v] using hvup n
        rw [abs_lt]
        constructor <;> linarith
      have Apos : 0 < D / 3 := by linarith
      -- lengths of successive links are controlled by the loss of value
      have hlink (n : ℕ) :
          ‖u (n+1) - u n‖ ≤ (v n - v (n+1)) / (D/3) := by
        apply (le_div_iff₀ Apos).2
        have hh := hlength (u n)
        -- rewrite the next terms of the two sequences
        rw [hu_succ, hv_succ]
        -- the factor on the left is written on the other side above
        simpa [v, mul_comm] using hh
      have hlong : ∀ m n : ℕ, n ≤ m →
          ‖u m - u n‖ ≤ (v n - v m) / (D/3) := by
        intro m
        induction m with
        | zero =>
            intro n hn0
            have hn : n = 0 := Nat.eq_zero_of_le_zero hn0
            subst n
            simp
        | succ m ih =>
            intro n hn
            by_cases heq : n = m+1
            · subst n
              simp
            · have hn' : n ≤ m := by omega
              calc
                ‖u (m+1) - u n‖ =
                    ‖(u (m+1) - u m) + (u m - u n)‖ := by
                      congr 1 <;> noncomm_ring
                _ ≤ ‖u (m+1) - u m‖ + ‖u m - u n‖ :=
                    norm_add_le _ _
                _ ≤ (v m - v (m+1)) / (D/3) +
                    (v n - v m) / (D/3) :=
                    add_le_add (hlink m) (ih n hn')
                _ = (v n - v (m+1)) / (D/3) := by ring
      -- the decreasing sequence of values has a real limit
      have hvbdd : BddBelow (Set.range v) := by
        refine ⟨mountainPassLevel f a b, ?_⟩
        rintro _ ⟨n, rfl⟩
        exact hvlow n
      let L : ℝ := ⨅ n : ℕ, v n
      have hvlim : Filter.Tendsto v Filter.atTop (nhds L) := by
        dsimp [L]
        exact tendsto_atTop_ciInf hvmono hvbdd
      have hLle (n : ℕ) : L ≤ v n := hvmono.le_of_tendsto hvlim n
      -- finite length now makes the iterates a Cauchy sequence
      have huc : CauchySeq u := by
        apply (Metric.cauchySeq_iff').2
        intro e he
        have htol : 0 < e * (D/3) := mul_pos he Apos
        have hev : ∀ᶠ n : ℕ in Filter.atTop, v n < L + e * (D/3) :=
          (tendsto_order.1 hvlim).2 _ (lt_add_of_pos_right _ htol)
        obtain ⟨N, hN⟩ := (Filter.eventually_atTop.1 hev)
        refine ⟨N, ?_⟩
        intro n hn
        rw [dist_eq_norm]
        have hmain := hlong n N hn
        have hle : (v N - v n) / (D/3) ≤ (v N - L) / (D/3) :=
          (div_le_div_of_nonneg_right (sub_le_sub_left (hLle n) _) (le_of_lt Apos))
        have hlt : (v N - L) / (D/3) < e := by
          apply (div_lt_iff₀ Apos).2
          have := hN N (le_rfl)
          nlinarith [Apos]
        exact lt_of_le_of_lt (le_trans hmain hle) hlt
      obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete huc
      have hvz : Filter.Tendsto v Filter.atTop (nhds (f z)) := by
        simpa [v, Function.comp_def] using _hf.continuous.continuousAt.tendsto.comp hz
      have hzlow : mountainPassLevel f a b ≤ f z :=
        ge_of_tendsto hvz (Filter.Eventually.of_forall hvlow)
      have hzup : f z ≤ mountainPassLevel f a b + D / 4 :=
        le_of_tendsto hvz (Filter.Eventually.of_forall (fun n => le_of_lt (hvup n)))
      have hzband : |f z - mountainPassLevel f a b| < D / 2 := by
        rw [abs_lt]
        constructor <;> linarith
      have hposz : 0 < step z := hstepp z hzband
      -- but the losses tend to zero, forcing all step sizes to tend to zero
      have hvl2 : L = f z := tendsto_nhds_unique hvlim hvz
      have hvnext : Filter.Tendsto (fun n : ℕ => v (n+1))
          Filter.atTop (nhds L) := by
        simpa [Function.comp_def] using hvlim.comp (Filter.tendsto_add_atTop_nat 1)
      have hdiff0 : Filter.Tendsto (fun n : ℕ => (v n - v (n+1)) / (D/3))
          Filter.atTop (nhds 0) := by
        convert (hvlim.sub hvnext).div_const (D/3) using 1 <;> simp
      have hstep_lim : Filter.Tendsto (fun n : ℕ => step (u n))
          Filter.atTop (nhds 0) := by
        apply squeeze_zero (fun n => hstep0 _) (fun n => ?_) hdiff0
        apply (le_div_iff₀ Apos).2
        have hh := hdrop (u n)
        rw [hv_succ]
        simpa [v, mul_comm] using hh
      have hstep_z : Filter.Tendsto (fun n : ℕ => step (u n))
          Filter.atTop (nhds (step z)) :=
        hstepc.continuousAt.tendsto.comp hz
      have : step z = 0 := tendsto_nhds_unique hstep_z hstep_lim
      exact (ne_of_gt hposz) this
    -- These open sets form an increasing cover of the compact high part;
    -- a finite subcover can be replaced by a single (later) iterate.
    let U : ℕ → Set I := fun n => {s | f ((T^[n]) (γ s)) < mountainPassLevel f a b}
    have hUopen : ∀ n, IsOpen (U n) := by
      intro n
      dsimp [U]
      exact isOpen_lt
        ((_hf.continuous.comp ((hT.iterate n).comp γ.continuous)))
        continuous_const
    have hcov : K ⊆ ⋃ n, U n := by
      intro s hs
      obtain ⟨n, hn⟩ := hesc s hs
      exact Set.mem_iUnion.2 ⟨n, hn⟩
    obtain ⟨tt, htt⟩ := hK.elim_finite_subcover U hUopen hcov
    let N : ℕ := ∑ n ∈ tt, n
    have htN {n : ℕ} (hn : n ∈ tt) : n ≤ N := by
      dsimp [N]
      exact Finset.single_le_sum (fun i hi => Nat.zero_le i) hn
    have hNK : ∀ s : I, s ∈ K →
        f ((T^[N]) (γ s)) < mountainPassLevel f a b := by
      intro s hs
      have hm := htt hs
      simp only [Set.mem_iUnion] at hm
      rcases hm with ⟨n, hn⟩
      rcases hn with ⟨hnt, hns⟩
      have hle := hitermono (γ s) (htN hnt)
      change f ((T^[n]) (γ s)) < mountainPassLevel f a b at hns
      exact lt_of_le_of_lt hle hns
    have hNall : ∀ s : I,
        f ((T^[N]) (γ s)) < mountainPassLevel f a b := by
      intro s
      by_cases hs : s ∈ K
      · exact hNK s hs
      · have hs' : f (γ s) < mountainPassLevel f a b := by
          change ¬ mountainPassLevel f a b ≤ f (γ s) at hs
          exact lt_of_not_ge hs
        have hle := hitermono (γ s) (Nat.zero_le N)
        have hle' : f ((T^[N]) (γ s)) ≤ f (γ s) := by
          simpa using hle
        exact lt_of_le_of_lt hle' hs'
    have hfa : ∀ n : ℕ, (T^[n]) a = a := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => simp [Function.iterate_succ_apply', ih, hTa]
    have hfb' : ∀ n : ℕ, (T^[n]) b = b := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => simp [Function.iterate_succ_apply', ih, hTb]
    let p : Path a b :=
      Path.mk
        ⟨(fun s : I => (T^[N]) (γ s)), (hT.iterate N).comp γ.continuous⟩
        (by simpa using hfa N) (by simpa using hfb' N)
    obtain ⟨q, hq, hqmax⟩ := path_height_attained _hf.continuous p
    have hlt : (⨆ s : I, f (p s)) < mountainPassLevel f a b := by
      rw [hq]
      exact hNall q
    have hle := mountainPassLevel_le_height f _hf.continuous _hmr p
    exact (not_lt_of_ge hle) hlt
  obtain ⟨u, hu, hu'⟩ :=
    ps_sequence_of_approx f (mountainPassLevel f a b) happ
  obtain ⟨x, hx, hxc⟩ :=
    critical_of_ps_sequence f _hf _hps u hu hu'
  exact ⟨x, hx, hxc, hc⟩
/-ResultProofEnd-/
/-ResultEnd-/

end Submission
