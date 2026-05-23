import Mathlib.Analysis.Calculus.Deriv.Basic

namespace Submission

/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/

open Lean Elab Command

/-
The template fixes the only ordinary import above.  This command makes available
the standard mathlib files used below: quotient derivative rules, Rolle's
theorem, and the ODE uniqueness theorem used for Abel's identity.
-/
syntax (name := import_sturm_extra) "#import_sturm_extra" : command
@[command_elab import_sturm_extra] unsafe def elabImportSturmExtra : CommandElab :=
    fun _stx => do
  Lean.enableInitializersExecution
  let imports : Array Import := #[
    { module := `Mathlib.Analysis.Calculus.Deriv.Inv },
    { module := `Mathlib.Analysis.Calculus.LocalExtr.Rolle },
    { module := `Mathlib.Analysis.ODE.Gronwall }]
  let env ← importModules imports (← getOptions) (loadExts := true)
  setEnv env

#import_sturm_extra

open Set
open scoped NNReal

/-- The Wronskian of two scalar functions. -/
noncomputable def wronskian (y₁ y₂ : ℝ → ℝ) : ℝ → ℝ :=
  fun x => y₁ x * deriv y₂ x - y₂ x * deriv y₁ x

/-- Abel's pointwise Wronskian identity: `W' = -p W`. -/
lemma hasDerivAt_wronskian
    (p q y₁ y₂ : ℝ → ℝ) (J : Set ℝ)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁)
      (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂)
      (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (x : ℝ) (hx : x ∈ J) :
    HasDerivAt (fun t => wronskian y₁ y₂ t)
      (-(p x) * wronskian y₁ y₂ x) x := by
  unfold wronskian
  convert ((hy₁ x hx).mul (hy₂' x hx)).sub ((hy₂ x hx).mul (hy₁' x hx)) using 1
  ring

/-- A bounded coefficient gives a Lipschitz bound for the linear vector field `z ↦ -p t * z`. -/
lemma linear_lipschitzOnWith_of_bound_at {p : ℝ → ℝ} {α β C t : ℝ}
    (hC : ∀ t ∈ Set.Icc α β, ‖p t‖ ≤ C) (ht : t ∈ Set.Icc α β) :
    LipschitzOnWith (⟨max C 0, le_max_right C 0⟩ : ℝ≥0)
      (fun z : ℝ => -p t * z) Set.univ := by
  refine LipschitzWith.lipschitzOnWith ?_
  refine LipschitzWith.of_dist_le_mul ?_
  intro z w
  have hp_bound : ‖p t‖ ≤ ((⟨max C 0, le_max_right C 0⟩ : ℝ≥0) : ℝ) :=
    (hC t ht).trans (le_max_left C 0)
  calc
    dist (-p t * z) (-p t * w) = ‖(-p t) * (z - w)‖ := by
      rw [dist_eq_norm]
      congr 1
      ring
    _ = ‖p t‖ * ‖z - w‖ := by rw [norm_mul, norm_neg]
    _ ≤ ((⟨max C 0, le_max_right C 0⟩ : ℝ≥0) : ℝ) * dist z w := by
      rw [dist_eq_norm]
      exact mul_le_mul_of_nonneg_right hp_bound (norm_nonneg _)

lemma linear_lipschitzOnWith_of_bound_Ico {p : ℝ → ℝ} {α β C : ℝ}
    (hC : ∀ t ∈ Set.Icc α β, ‖p t‖ ≤ C) :
    ∀ t ∈ Set.Ico α β,
      LipschitzOnWith (⟨max C 0, le_max_right C 0⟩ : ℝ≥0)
        (fun z : ℝ => -p t * z) Set.univ := by
  intro t ht
  exact linear_lipschitzOnWith_of_bound_at hC (Ico_subset_Icc_self ht)

lemma linear_lipschitzOnWith_of_bound_Ioc {p : ℝ → ℝ} {α β C : ℝ}
    (hC : ∀ t ∈ Set.Icc α β, ‖p t‖ ≤ C) :
    ∀ t ∈ Set.Ioc α β,
      LipschitzOnWith (⟨max C 0, le_max_right C 0⟩ : ℝ≥0)
        (fun z : ℝ => -p t * z) Set.univ := by
  intro t ht
  exact linear_lipschitzOnWith_of_bound_at hC (Ioc_subset_Icc_self ht)

/-- If the Wronskian vanishes at the left endpoint, it vanishes on the whole interval. -/
lemma wronskian_eq_zero_on_Icc_right
    (p q y₁ y₂ : ℝ → ℝ) {J : Set ℝ} {α β : ℝ}
    (hseg : Set.Icc α β ⊆ J) (hp : ContinuousOn p J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁)
      (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂)
      (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (hWα : wronskian y₁ y₂ α = 0) :
    ∀ t ∈ Set.Icc α β, wronskian y₁ y₂ t = 0 := by
  let W := wronskian y₁ y₂
  have hpI : ContinuousOn p (Set.Icc α β) := hp.mono hseg
  rcases isCompact_Icc.exists_bound_of_continuousOn hpI with ⟨C, hC⟩
  have hWcont : ContinuousOn W (Set.Icc α β) := by
    exact HasDerivAt.continuousOn
      (fun t ht => hasDerivAt_wronskian p q y₁ y₂ J hy₁ hy₁' hy₂ hy₂' t (hseg ht))
  have hzero_cont : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Set.Icc α β) :=
    continuousOn_const
  have hWderiv : ∀ t ∈ Set.Ico α β,
      HasDerivWithinAt W ((fun t z => -p t * z) t (W t)) (Set.Ici t) t := by
    intro t ht
    have htIcc : t ∈ Set.Icc α β := Ico_subset_Icc_self ht
    simpa [W, mul_assoc] using
      (hasDerivAt_wronskian p q y₁ y₂ J hy₁ hy₁' hy₂ hy₂' t
        (hseg htIcc)).hasDerivWithinAt
  have h0deriv : ∀ t ∈ Set.Ico α β,
      HasDerivWithinAt (fun _ : ℝ => (0 : ℝ))
        ((fun t z => -p t * z) t ((fun _ : ℝ => (0 : ℝ)) t)) (Set.Ici t) t := by
    intro t ht
    simpa using (hasDerivAt_const (t) (0 : ℝ)).hasDerivWithinAt
  have hfs : ∀ t ∈ Set.Ico α β, W t ∈ (fun _ : ℝ => Set.univ) t := by
    intro t ht
    trivial
  have hgs : ∀ t ∈ Set.Ico α β,
      (fun _ : ℝ => (0 : ℝ)) t ∈ (fun _ : ℝ => Set.univ) t := by
    intro t ht
    trivial
  have heqon := ODE_solution_unique_of_mem_Icc_right
    (v := fun t z : ℝ => -p t * z) (s := fun _ : ℝ => Set.univ)
    (K := (⟨max C 0, le_max_right C 0⟩ : ℝ≥0))
    (a := α) (b := β) (f := W) (g := fun _ : ℝ => (0 : ℝ))
    (linear_lipschitzOnWith_of_bound_Ico hC) hWcont hWderiv hfs hzero_cont h0deriv
    hgs (by simpa [W] using hWα)
  intro t ht
  exact heqon ht

/-- If the Wronskian vanishes at the right endpoint, it vanishes on the whole interval. -/
lemma wronskian_eq_zero_on_Icc_left
    (p q y₁ y₂ : ℝ → ℝ) {J : Set ℝ} {α β : ℝ}
    (hseg : Set.Icc α β ⊆ J) (hp : ContinuousOn p J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁)
      (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂)
      (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (hWβ : wronskian y₁ y₂ β = 0) :
    ∀ t ∈ Set.Icc α β, wronskian y₁ y₂ t = 0 := by
  let W := wronskian y₁ y₂
  have hpI : ContinuousOn p (Set.Icc α β) := hp.mono hseg
  rcases isCompact_Icc.exists_bound_of_continuousOn hpI with ⟨C, hC⟩
  have hWcont : ContinuousOn W (Set.Icc α β) := by
    exact HasDerivAt.continuousOn
      (fun t ht => hasDerivAt_wronskian p q y₁ y₂ J hy₁ hy₁' hy₂ hy₂' t (hseg ht))
  have hzero_cont : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Set.Icc α β) :=
    continuousOn_const
  have hWderiv : ∀ t ∈ Set.Ioc α β,
      HasDerivWithinAt W ((fun t z => -p t * z) t (W t)) (Set.Iic t) t := by
    intro t ht
    have htIcc : t ∈ Set.Icc α β := Ioc_subset_Icc_self ht
    simpa [W, mul_assoc] using
      (hasDerivAt_wronskian p q y₁ y₂ J hy₁ hy₁' hy₂ hy₂' t
        (hseg htIcc)).hasDerivWithinAt
  have h0deriv : ∀ t ∈ Set.Ioc α β,
      HasDerivWithinAt (fun _ : ℝ => (0 : ℝ))
        ((fun t z => -p t * z) t ((fun _ : ℝ => (0 : ℝ)) t)) (Set.Iic t) t := by
    intro t ht
    simpa using (hasDerivAt_const (t) (0 : ℝ)).hasDerivWithinAt
  have hfs : ∀ t ∈ Set.Ioc α β, W t ∈ (fun _ : ℝ => Set.univ) t := by
    intro t ht
    trivial
  have hgs : ∀ t ∈ Set.Ioc α β,
      (fun _ : ℝ => (0 : ℝ)) t ∈ (fun _ : ℝ => Set.univ) t := by
    intro t ht
    trivial
  have heqon := ODE_solution_unique_of_mem_Icc_left
    (v := fun t z : ℝ => -p t * z) (s := fun _ : ℝ => Set.univ)
    (K := (⟨max C 0, le_max_right C 0⟩ : ℝ≥0))
    (a := α) (b := β) (f := W) (g := fun _ : ℝ => (0 : ℝ))
    (linear_lipschitzOnWith_of_bound_Ioc hC) hWcont hWderiv hfs hzero_cont h0deriv
    hgs (by simpa [W] using hWβ)
  intro t ht
  exact heqon ht

/-- Abel's nonvanishing consequence for the Wronskian. -/
theorem wronskian_ne_on_of_exists_ne
    (p q y₁ y₂ : ℝ → ℝ) {J : Set ℝ} (_hJ_open : IsOpen J)
    (hJ_conn : IsPreconnected J) (hp : ContinuousOn p J) (_hq : ContinuousOn q J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁)
      (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂)
      (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (hW : ∃ x₀ ∈ J, wronskian y₁ y₂ x₀ ≠ 0) :
    ∀ x ∈ J, wronskian y₁ y₂ x ≠ 0 := by
  rcases hW with ⟨x₀, hx₀J, hWx₀⟩
  intro x hxJ hWx
  by_cases hle : x ≤ x₀
  · have hseg : Set.Icc x x₀ ⊆ J := by
      have hseg_u := hJ_conn.ordConnected.uIcc_subset hxJ hx₀J
      simpa [Set.uIcc_of_le hle] using hseg_u
    have hzero_on := wronskian_eq_zero_on_Icc_right p q y₁ y₂
      (J := J) (α := x) (β := x₀) hseg hp hy₁ hy₁' hy₂ hy₂' hWx
    exact hWx₀ (hzero_on x₀ ⟨hle, le_rfl⟩)
  · have hx₀le : x₀ ≤ x := le_of_lt (lt_of_not_ge hle)
    have hseg : Set.Icc x₀ x ⊆ J := by
      have hseg_u := hJ_conn.ordConnected.uIcc_subset hx₀J hxJ
      simpa [Set.uIcc_of_le hx₀le] using hseg_u
    have hzero_on := wronskian_eq_zero_on_Icc_left p q y₁ y₂
      (J := J) (α := x₀) (β := x) hseg hp hy₁ hy₁' hy₂ hy₂' hWx
    exact hWx₀ (hzero_on x₀ ⟨le_rfl, hx₀le⟩)

/-- The left endpoint belongs to an ambient set containing `[a,b]`. -/
lemma left_mem_of_Icc_subset {a b : ℝ} {J : Set ℝ} (hab : a < b)
    (hJ_sub : Set.Icc a b ⊆ J) : a ∈ J := by
  exact hJ_sub ⟨le_rfl, le_of_lt hab⟩

/-- The right endpoint belongs to an ambient set containing `[a,b]`. -/
lemma right_mem_of_Icc_subset {a b : ℝ} {J : Set ℝ} (hab : a < b)
    (hJ_sub : Set.Icc a b ⊆ J) : b ∈ J := by
  exact hJ_sub ⟨le_of_lt hab, le_rfl⟩

/-- Interior and endpoint nonvanishing imply closed-interval nonvanishing. -/
lemma ne_on_Icc_of_ne_endpoints_and_ne_Ioo {f : ℝ → ℝ} {a b : ℝ}
    (_hab : a < b) (ha : f a ≠ 0) (hb : f b ≠ 0)
    (hmid : ∀ x ∈ Set.Ioo a b, f x ≠ 0) :
    ∀ x ∈ Set.Icc a b, f x ≠ 0 := by
  intro x hx
  rcases hx with ⟨hax, hxb⟩
  rcases lt_or_eq_of_le hax with hlt | rfl
  · rcases lt_or_eq_of_le hxb with hxlt | rfl
    · exact hmid x ⟨hlt, hxlt⟩
    · exact hb
  · exact ha

/-- A subinterval with endpoints in `(a,b)` lies in an ambient set containing `[a,b]`. -/
lemma Icc_subset_J_of_Ioo_endpoints {a b c d : ℝ} {J : Set ℝ}
    (hc : c ∈ Set.Ioo a b) (hd : d ∈ Set.Ioo a b)
    (hJ_sub : Set.Icc a b ⊆ J) : Set.Icc c d ⊆ J := by
  intro x hx
  exact hJ_sub ⟨le_trans (le_of_lt hc.1) hx.1, le_trans hx.2 (le_of_lt hd.2)⟩

/-- A subinterval with endpoints in `(a,b)` is contained in `(a,b)`. -/
lemma Icc_subset_Ioo_of_Ioo_endpoints {a b c d : ℝ}
    (hc : c ∈ Set.Ioo a b) (hd : d ∈ Set.Ioo a b) :
    Set.Icc c d ⊆ Set.Ioo a b := by
  intro x hx
  exact ⟨lt_of_lt_of_le hc.1 hx.1, lt_of_le_of_lt hx.2 hd.2⟩

/-- At a zero of the first function, nonzero Wronskian forces the second function nonzero. -/
lemma y₂_ne_of_wronskian_ne_at_zero_of_y₁ {y₁ y₂ : ℝ → ℝ} {x : ℝ}
    (hy₁x : y₁ x = 0) (hWx : wronskian y₁ y₂ x ≠ 0) : y₂ x ≠ 0 := by
  intro hy₂x
  apply hWx
  simp [wronskian, hy₁x, hy₂x]

/-- Swapping the two functions negates the Wronskian. -/
lemma neg_wronskian_swap (y₁ y₂ : ℝ → ℝ) (x : ℝ) :
    wronskian y₂ y₁ x = - wronskian y₁ y₂ x := by
  unfold wronskian
  ring

/-- Differentiability on an ambient set gives continuity on a subinterval. -/
lemma continuousOn_Icc_of_hasDerivAt_on {f f' : ℝ → ℝ} {α β : ℝ} {J : Set ℝ}
    (hseg : Set.Icc α β ⊆ J)
    (hf : ∀ x ∈ J, HasDerivAt f (f' x) x) :
    ContinuousOn f (Set.Icc α β) := by
  exact (HasDerivAt.continuousOn hf).mono hseg

/-- Quotient-Rolle lemma: if `u` vanishes at both endpoints and `v` is nonzero
on the closed interval, then the Wronskian of `u` and `v` vanishes inside. -/
theorem exists_wronskian_zero_of_quotient
    {J : Set ℝ} {u v : ℝ → ℝ} {α β : ℝ}
    (hαβ : α < β) (hseg : Set.Icc α β ⊆ J)
    (hu : ∀ x ∈ J, HasDerivAt u (deriv u x) x)
    (hv : ∀ x ∈ J, HasDerivAt v (deriv v x) x)
    (hv_ne : ∀ x ∈ Set.Icc α β, v x ≠ 0)
    (huα : u α = 0) (huβ : u β = 0) :
    ∃ c, c ∈ Set.Ioo α β ∧ wronskian u v c = 0 := by
  let r : ℝ → ℝ := fun x => u x / v x
  have hucont : ContinuousOn u (Set.Icc α β) :=
    continuousOn_Icc_of_hasDerivAt_on (f' := deriv u) hseg hu
  have hvcont : ContinuousOn v (Set.Icc α β) :=
    continuousOn_Icc_of_hasDerivAt_on (f' := deriv v) hseg hv
  have hrcont : ContinuousOn r (Set.Icc α β) := by
    exact hucont.div hvcont hv_ne
  have hrend : r α = r β := by
    simp [r, huα, huβ]
  have hrderiv : ∀ x ∈ Set.Ioo α β,
      HasDerivAt r ((deriv u x * v x - u x * deriv v x) / (v x)^2) x := by
    intro x hx
    have hxIcc : x ∈ Set.Icc α β := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    simpa [r, div_eq_mul_inv, sq] using
      (hu x (hseg hxIcc)).div (hv x (hseg hxIcc)) (hv_ne x hxIcc)
  rcases exists_hasDerivAt_eq_zero hαβ hrcont hrend hrderiv with ⟨c, hc, hdc⟩
  refine ⟨c, hc, ?_⟩
  have hvc : v c ≠ 0 := hv_ne c ⟨le_of_lt hc.1, le_of_lt hc.2⟩
  have hnum : deriv u c * v c - u c * deriv v c = 0 := by
    have hpow : (v c)^2 ≠ 0 := pow_ne_zero 2 hvc
    rcases (div_eq_zero_iff.mp hdc) with hnum | hden
    · exact hnum
    · exact False.elim (hpow hden)
  unfold wronskian
  linarith

/-- Two zeros of `y₂` in `(a,b)` must coincide. -/
lemma two_zeros_eq_of_wronskian_ne
    {J : Set ℝ} {a b c d : ℝ} {y₁ y₂ : ℝ → ℝ}
    (hJ_sub : Set.Icc a b ⊆ J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hW_ne : ∀ x ∈ J, wronskian y₁ y₂ x ≠ 0)
    (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0)
    (hc : c ∈ Set.Ioo a b ∧ y₂ c = 0)
    (hd : d ∈ Set.Ioo a b ∧ y₂ d = 0) : c = d := by
  by_contra hcd
  rcases lt_or_gt_of_ne hcd with hcltd | hdltc
  · have hseg : Set.Icc c d ⊆ J := Icc_subset_J_of_Ioo_endpoints hc.1 hd.1 hJ_sub
    have hy₁_ne : ∀ x ∈ Set.Icc c d, y₁ x ≠ 0 := by
      intro x hx
      exact hne x ((Icc_subset_Ioo_of_Ioo_endpoints hc.1 hd.1) hx)
    rcases exists_wronskian_zero_of_quotient (J := J) (u := y₂) (v := y₁)
        hcltd hseg hy₂ hy₁ hy₁_ne hc.2 hd.2 with ⟨e, he, hWe⟩
    have heJ : e ∈ J := hseg ⟨le_of_lt he.1, le_of_lt he.2⟩
    have hW12e : wronskian y₁ y₂ e = 0 := by
      have hneg : - wronskian y₁ y₂ e = 0 := by
        rw [neg_wronskian_swap] at hWe
        exact hWe
      exact neg_eq_zero.mp hneg
    exact hW_ne e heJ hW12e
  · have hseg : Set.Icc d c ⊆ J := Icc_subset_J_of_Ioo_endpoints hd.1 hc.1 hJ_sub
    have hy₁_ne : ∀ x ∈ Set.Icc d c, y₁ x ≠ 0 := by
      intro x hx
      exact hne x ((Icc_subset_Ioo_of_Ioo_endpoints hd.1 hc.1) hx)
    rcases exists_wronskian_zero_of_quotient (J := J) (u := y₂) (v := y₁)
        hdltc hseg hy₂ hy₁ hy₁_ne hd.2 hc.2 with ⟨e, he, hWe⟩
    have heJ : e ∈ J := hseg ⟨le_of_lt he.1, le_of_lt he.2⟩
    have hW12e : wronskian y₁ y₂ e = 0 := by
      have hneg : - wronskian y₁ y₂ e = 0 := by
        rw [neg_wronskian_swap] at hWe
        exact hWe
      exact neg_eq_zero.mp hneg
    exact hW_ne e heJ hW12e

/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/
theorem sturm_separation (p q y₁ y₂ : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (J : Set ℝ) (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
    (hJ_sub : Set.Icc a b ⊆ J)
    (hp : ContinuousOn p J) (hq : ContinuousOn q J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
    (hza : y₁ a = 0) (hzb : y₁ b = 0)
    (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0) :
    ∃! c, c ∈ Set.Ioo a b ∧ y₂ c = 0 :=
/-ResultProofBegin-/by
  have hW' : ∃ x₀ ∈ J, wronskian y₁ y₂ x₀ ≠ 0 := by
    simpa [wronskian] using hW
  have hW_ne : ∀ x ∈ J, wronskian y₁ y₂ x ≠ 0 :=
    wronskian_ne_on_of_exists_ne p q y₁ y₂ hJ_open hJ_conn hp hq
      hy₁ hy₁' hy₂ hy₂' hW'
  have hex : ∃ c, c ∈ Set.Ioo a b ∧ y₂ c = 0 := by
    by_contra hno
    have hy₂_ne_Ioo : ∀ x ∈ Set.Ioo a b, y₂ x ≠ 0 := by
      intro x hx hzero
      exact hno ⟨x, hx, hzero⟩
    have haJ : a ∈ J := left_mem_of_Icc_subset hab hJ_sub
    have hbJ : b ∈ J := right_mem_of_Icc_subset hab hJ_sub
    have hy₂a : y₂ a ≠ 0 :=
      y₂_ne_of_wronskian_ne_at_zero_of_y₁ hza (hW_ne a haJ)
    have hy₂b : y₂ b ≠ 0 :=
      y₂_ne_of_wronskian_ne_at_zero_of_y₁ hzb (hW_ne b hbJ)
    have hy₂_ne_Icc : ∀ x ∈ Set.Icc a b, y₂ x ≠ 0 :=
      ne_on_Icc_of_ne_endpoints_and_ne_Ioo hab hy₂a hy₂b hy₂_ne_Ioo
    rcases exists_wronskian_zero_of_quotient (J := J) (u := y₁) (v := y₂)
        hab hJ_sub hy₁ hy₂ hy₂_ne_Icc hza hzb with ⟨c, hc, hWc⟩
    have hcJ : c ∈ J := hJ_sub ⟨le_of_lt hc.1, le_of_lt hc.2⟩
    exact hW_ne c hcJ hWc
  rcases hex with ⟨c, hc⟩
  refine ExistsUnique.intro c hc ?_
  intro d hd
  exact (two_zeros_eq_of_wronskian_ne hJ_sub hy₁ hy₂ hW_ne hne hc hd).symm/-ResultProofEnd-/
/-ResultEnd-/
end Submission