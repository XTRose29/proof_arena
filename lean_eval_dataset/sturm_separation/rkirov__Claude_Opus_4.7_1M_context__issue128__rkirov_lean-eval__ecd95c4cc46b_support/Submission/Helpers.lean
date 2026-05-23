import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field

open Filter Topology Set

namespace Submission.Helpers

/-- The Wronskian of two functions. -/
noncomputable def W (y₁ y₂ : ℝ → ℝ) (x : ℝ) : ℝ :=
  y₁ x * deriv y₂ x - y₂ x * deriv y₁ x

variable {p q y₁ y₂ : ℝ → ℝ} {a b : ℝ}

/-- Liouville: `W' = -p · W` on `J`. -/
lemma hasDerivAt_W
    (J : Set ℝ)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
    {x : ℝ} (hx : x ∈ J) :
    HasDerivAt (W y₁ y₂) (-(p x) * W y₁ y₂ x) x := by
  have h₁ := (hy₁ x hx).mul (hy₂' x hx)
  have h₂ := (hy₂ x hx).mul (hy₁' x hx)
  have hsub := h₁.sub h₂
  convert hsub using 1
  show -(p x) * W y₁ y₂ x =
      deriv y₁ x * deriv y₂ x + y₁ x * -(p x * deriv y₂ x + q x * y₂ x) -
      (deriv y₂ x * deriv y₁ x + y₂ x * -(p x * deriv y₁ x + q x * y₁ x))
  simp [W]
  ring

/-- `W` is continuous on `J`. -/
lemma continuousOn_W
    (J : Set ℝ)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x) :
    ContinuousOn (W y₁ y₂) J := fun x hx =>
  (hasDerivAt_W J hy₁ hy₁' hy₂ hy₂' hx).continuousAt.continuousWithinAt

/-- ODE uniqueness on `Icc a b` for the linear field `v(t, x) = -(p t) · x`.
If a continuous `f : ℝ → ℝ` satisfies `f' = -p · f` on `J ⊇ Icc a b` and `f a = 0`, then
`f ≡ 0` on `Icc a b`. -/
private lemma linear_ode_zero_of_left_zero
    (J : Set ℝ)
    (hp_cont : ContinuousOn p (Icc a b))
    (hJ_sub : Icc a b ⊆ J)
    (hab : a ≤ b)
    {f : ℝ → ℝ}
    (hf' : ∀ x ∈ J, HasDerivAt f (-(p x) * f x) x)
    (h0 : f a = 0) :
    ∀ x ∈ Icc a b, f x = 0 := by
  obtain ⟨xMax, _, hxMaxMax⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hab) hp_cont.norm
  set K : NNReal := ⟨|p xMax|, abs_nonneg _⟩ with hK_def
  have hp_le : ∀ t ∈ Icc a b, ‖p t‖ ≤ (K : ℝ) := fun t ht => hxMaxMax ht
  have hlip_v : ∀ t ∈ Icc a b, LipschitzOnWith K (fun x : ℝ => -(p t) * x) Set.univ := by
    intro t ht
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x _ y _
    rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_right (hp_le t ht) (abs_nonneg _)
  have hf_deriv : ∀ x ∈ Icc a b, HasDerivAt f (-(p x) * f x) x := fun x hx =>
    hf' x (hJ_sub hx)
  have hf_cont : ContinuousOn f (Icc a b) := fun x hx =>
    (hf_deriv x hx).continuousAt.continuousWithinAt
  have hzero_cont : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc a b) := continuousOn_const
  -- Apply ODE_solution_unique_of_mem_Icc_right on Icc a b with base point a.
  have heqon : EqOn f (fun _ : ℝ => (0 : ℝ)) (Icc a b) := by
    apply ODE_solution_unique_of_mem_Icc_right
      (v := fun t x => -(p t) * x) (s := fun _ => Set.univ) (K := K)
    · intro t ht
      exact hlip_v t ⟨ht.1, le_of_lt ht.2⟩
    · exact hf_cont
    · intro t ht
      exact (hf_deriv t ⟨ht.1, le_of_lt ht.2⟩).hasDerivWithinAt
    · intros; trivial
    · exact hzero_cont
    · intro t _
      have : HasDerivAt (fun _ : ℝ => (0 : ℝ)) (-(p t) * 0) t := by
        simpa using hasDerivAt_const t (0 : ℝ)
      exact this.hasDerivWithinAt
    · intros; trivial
    · simpa using h0
  intro x hx
  exact heqon hx

/-- Symmetric: if `f a = 0` is replaced by `f b = 0`. -/
private lemma linear_ode_zero_of_right_zero
    (J : Set ℝ)
    (hp_cont : ContinuousOn p (Icc a b))
    (hJ_sub : Icc a b ⊆ J)
    (hab : a ≤ b)
    {f : ℝ → ℝ}
    (hf' : ∀ x ∈ J, HasDerivAt f (-(p x) * f x) x)
    (h0 : f b = 0) :
    ∀ x ∈ Icc a b, f x = 0 := by
  obtain ⟨xMax, _, hxMaxMax⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hab) hp_cont.norm
  set K : NNReal := ⟨|p xMax|, abs_nonneg _⟩ with hK_def
  have hp_le : ∀ t ∈ Icc a b, ‖p t‖ ≤ (K : ℝ) := fun t ht => hxMaxMax ht
  have hlip_v : ∀ t ∈ Icc a b, LipschitzOnWith K (fun x : ℝ => -(p t) * x) Set.univ := by
    intro t ht
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x _ y _
    rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_right (hp_le t ht) (abs_nonneg _)
  have hf_deriv : ∀ x ∈ Icc a b, HasDerivAt f (-(p x) * f x) x := fun x hx =>
    hf' x (hJ_sub hx)
  have hf_cont : ContinuousOn f (Icc a b) := fun x hx =>
    (hf_deriv x hx).continuousAt.continuousWithinAt
  have heqon : EqOn f (fun _ : ℝ => (0 : ℝ)) (Icc a b) := by
    apply ODE_solution_unique_of_mem_Icc_left
      (v := fun t x => -(p t) * x) (s := fun _ => Set.univ) (K := K)
    · intro t ht
      exact hlip_v t ⟨le_of_lt ht.1, ht.2⟩
    · exact hf_cont
    · intro t ht
      exact (hf_deriv t ⟨le_of_lt ht.1, ht.2⟩).hasDerivWithinAt
    · intros; trivial
    · exact continuousOn_const
    · intro t _
      have : HasDerivAt (fun _ : ℝ => (0 : ℝ)) (-(p t) * 0) t := by
        simpa using hasDerivAt_const t (0 : ℝ)
      exact this.hasDerivWithinAt
    · intros; trivial
    · simpa using h0
  intro x hx
  exact heqon hx

/-- ODE uniqueness: if `W` vanishes at any point of `Icc a b`, then `W ≡ 0` on `Icc a b`. -/
lemma W_eq_zero_of_zero_at
    (J : Set ℝ)
    (hp_cont : ContinuousOn p (Icc a b))
    (hJ_sub : Icc a b ⊆ J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (hab : a ≤ b) {c : ℝ} (hcMem : c ∈ Icc a b) (hWc : W y₁ y₂ c = 0) :
    ∀ x ∈ Icc a b, W y₁ y₂ x = 0 := by
  have hac : a ≤ c := hcMem.1
  have hcb : c ≤ b := hcMem.2
  have hW' : ∀ x ∈ J, HasDerivAt (W y₁ y₂) (-(p x) * W y₁ y₂ x) x := fun x hx =>
    hasDerivAt_W J hy₁ hy₁' hy₂ hy₂' hx
  -- On Icc c b: W(c) = 0 ⟹ W ≡ 0 on Icc c b.
  have hsub_right : Icc c b ⊆ Icc a b := Icc_subset_Icc_left hac
  have h_right : ∀ x ∈ Icc c b, W y₁ y₂ x = 0 :=
    linear_ode_zero_of_left_zero J (hp_cont.mono hsub_right) (hsub_right.trans hJ_sub) hcb hW' hWc
  -- On Icc a c: W(c) = 0 ⟹ W ≡ 0 on Icc a c.
  have hsub_left : Icc a c ⊆ Icc a b := Icc_subset_Icc_right hcb
  have h_left : ∀ x ∈ Icc a c, W y₁ y₂ x = 0 :=
    linear_ode_zero_of_right_zero J (hp_cont.mono hsub_left) (hsub_left.trans hJ_sub) hac hW' hWc
  -- Combine.
  intro x hx
  rcases le_or_gt x c with hxc | hxc
  · exact h_left x ⟨hx.1, hxc⟩
  · exact h_right x ⟨le_of_lt hxc, hx.2⟩

/-- The dichotomy: `W` is either everywhere zero or never zero on `Icc a b`. -/
lemma W_dichotomy
    (J : Set ℝ)
    (hp_cont : ContinuousOn p (Icc a b))
    (hJ_sub : Icc a b ⊆ J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (hab : a ≤ b) :
    (∀ x ∈ Icc a b, W y₁ y₂ x = 0) ∨ (∀ x ∈ Icc a b, W y₁ y₂ x ≠ 0) := by
  classical
  by_cases h : ∃ c ∈ Icc a b, W y₁ y₂ c = 0
  · left
    obtain ⟨c, hcMem, hWc⟩ := h
    exact W_eq_zero_of_zero_at J hp_cont hJ_sub hy₁ hy₁' hy₂ hy₂' hab hcMem hWc
  · right
    intro x hx hWx
    exact h ⟨x, hx, hWx⟩

/-- Bridge: from `hW` (nonvanishing somewhere in `J`), conclude `W ≠ 0` everywhere on
`Icc a b`. The argument: enlarge `Icc a b` to a closed interval `Icc α β ⊆ J` containing
`x₀`; apply the dichotomy on the enlarged interval. The preconnectedness of `J` provides
`Icc (min a x₀) (max b x₀) ⊆ J` directly via `IsPreconnected.Icc_subset`. -/
lemma W_nonzero_on_Icc
    (J : Set ℝ) (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
    (hp_cont : ContinuousOn p J)
    (hJ_sub : Icc a b ⊆ J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (hW : ∃ x₀ ∈ J, W y₁ y₂ x₀ ≠ 0)
    (hab : a ≤ b) :
    ∀ x ∈ Icc a b, W y₁ y₂ x ≠ 0 := by
  classical
  obtain ⟨x₀, hx₀J, hWx₀⟩ := hW
  -- Form the convex hull of {x₀} ∪ Icc a b: Icc (min a x₀) (max b x₀).
  set α := min a x₀ with hα_def
  set β := max b x₀ with hβ_def
  have hαa : α ≤ a := min_le_left _ _
  have hbβ : b ≤ β := le_max_left _ _
  have hx₀α : α ≤ x₀ := min_le_right _ _
  have hx₀β : x₀ ≤ β := le_max_right _ _
  have hαβ : α ≤ β := le_trans hαa (le_trans hab hbβ)
  -- α, β ∈ J via preconnectedness (α = min a x₀ is either a or x₀, both in J; similarly β).
  have ha_in : a ∈ J := hJ_sub ⟨le_refl a, hab⟩
  have hb_in : b ∈ J := hJ_sub ⟨hab, le_refl b⟩
  have hα_in : α ∈ J := by
    by_cases h : a ≤ x₀
    · simp [α, min_eq_left h, ha_in]
    · push_neg at h
      simp [α, min_eq_right h.le, hx₀J]
  have hβ_in : β ∈ J := by
    by_cases h : b ≤ x₀
    · simp [β, max_eq_right h, hx₀J]
    · push_neg at h
      simp [β, max_eq_left h.le, hb_in]
  -- Icc α β ⊆ J via preconnectedness.
  have hContain : Icc α β ⊆ J := hJ_conn.Icc_subset hα_in hβ_in
  -- Apply dichotomy on Icc α β.
  have hsub_ab : Icc a b ⊆ Icc α β := Icc_subset_Icc hαa hbβ
  have hp_cont_αβ : ContinuousOn p (Icc α β) := hp_cont.mono hContain
  have hx₀_in : x₀ ∈ Icc α β := ⟨hx₀α, hx₀β⟩
  have hdich :=
    W_dichotomy J hp_cont_αβ hContain hy₁ hy₁' hy₂ hy₂' hαβ
  rcases hdich with hzero | hnz
  · exfalso; exact hWx₀ (hzero x₀ hx₀_in)
  · intro x hx
    exact hnz x (hsub_ab hx)

/-- Helper: For `f : ℝ → ℝ` continuous on `Icc a b`, with right derivative bounded by
`K · ‖f‖`, if `f a = 0` then `f ≡ 0` on `Icc a b`. (Wraps mathlib's
`eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right`.) -/
private lemma _root_.eq_zero_of_norm_deriv_bound_left {f f' : ℝ → ℝ} {K a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (ha : f a = 0)
    (bound : ∀ x ∈ Ico a b, ‖f' x‖ ≤ K * ‖f x‖) :
    ∀ x ∈ Icc a b, f x = 0 :=
  eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hf hf' ha bound

/-- Time-reversed: if `f b = 0` instead. -/
private lemma _root_.eq_zero_of_norm_deriv_bound_right {f f' : ℝ → ℝ} {K a b : ℝ}
    (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ioc a b, HasDerivAt f (f' x) x)
    (hb : f b = 0)
    (bound : ∀ x ∈ Ioc a b, ‖f' x‖ ≤ K * ‖f x‖) :
    ∀ x ∈ Icc a b, f x = 0 := by
  -- Apply to g(s) := f(a + b - s) on Icc a b.
  set g : ℝ → ℝ := fun s => f (a + b - s) with hg_def
  set g' : ℝ → ℝ := fun s => -f' (a + b - s) with hg'_def
  have hmaps : MapsTo (fun s : ℝ => a + b - s) (Icc a b) (Icc a b) :=
    fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hg_cont : ContinuousOn g (Icc a b) :=
    hf.comp ((continuous_const.sub continuous_id).continuousOn) hmaps
  have hg_deriv : ∀ x ∈ Ico a b, HasDerivWithinAt g (g' x) (Ici x) x := by
    intro x hx
    have hx_in : a + b - x ∈ Ioc a b :=
      ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hsub : HasDerivAt (fun s : ℝ => a + b - s) (-1) x := by
      have h1 : HasDerivAt (fun s : ℝ => a + b - s) (0 - 1) x :=
        (hasDerivAt_const x (a + b)).sub (hasDerivAt_id x)
      simpa using h1
    have hcomp := (hf' (a + b - x) hx_in).comp x hsub
    convert hcomp.hasDerivWithinAt using 1
    show -f' (a + b - x) = f' (a + b - x) * -1
    ring
  have hg_a : g a = 0 := by show f (a + b - a) = 0; simp [hb]
  have hg_bound : ∀ x ∈ Ico a b, ‖g' x‖ ≤ K * ‖g x‖ := by
    intro x hx
    have hx_in : a + b - x ∈ Ioc a b :=
      ⟨by linarith [hx.2], by linarith [hx.1]⟩
    show ‖-f' (a + b - x)‖ ≤ K * ‖f (a + b - x)‖
    rw [norm_neg]
    exact bound _ hx_in
  have hg_zero := eq_zero_of_norm_deriv_bound_left hg_cont hg_deriv hg_a hg_bound
  intro x hx
  have hx_rev : a + b - x ∈ Icc a b := hmaps hx
  have hgrev := hg_zero (a + b - x) hx_rev
  show f x = 0
  have : g (a + b - x) = f (a + b - (a + b - x)) := rfl
  rw [this] at hgrev
  have hxx : a + b - (a + b - x) = x := by ring
  rw [hxx] at hgrev
  exact hgrev

/-- The energy bound: `|E'(x)| ≤ K · E(x)` for `E(x) := y₁(x)^2 + (deriv y₁ x)^2`. -/
private lemma energy_deriv_bound
    {p q y₁ : ℝ → ℝ} {a b : ℝ}
    (J : Set ℝ) (hJ_sub : Icc a b ⊆ J)
    (hp_cont : ContinuousOn p J) (hq_cont : ContinuousOn q J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hab : a ≤ b) :
    ∃ K : ℝ, 0 ≤ K ∧
      ContinuousOn (fun x => (y₁ x)^2 + (deriv y₁ x)^2) (Icc a b) ∧
      (∀ x ∈ Icc a b, HasDerivAt (fun s => (y₁ s)^2 + (deriv y₁ s)^2)
          (2 * y₁ x * deriv y₁ x +
            2 * deriv y₁ x * (-(p x * deriv y₁ x + q x * y₁ x))) x) ∧
      (∀ x ∈ Icc a b,
        ‖2 * y₁ x * deriv y₁ x + 2 * deriv y₁ x * (-(p x * deriv y₁ x + q x * y₁ x))‖
          ≤ K * ‖(y₁ x)^2 + (deriv y₁ x)^2‖) := by
  obtain ⟨xp, _, hxp⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr hab) (hp_cont.mono hJ_sub).norm
  obtain ⟨xq, _, hxq⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr hab) (hq_cont.mono hJ_sub).norm
  set K_p : ℝ := |p xp| with hKp_def
  set K_q : ℝ := |q xq| with hKq_def
  have hKp_le : ∀ x ∈ Icc a b, |p x| ≤ K_p := fun x hx => hxp hx
  have hKq_le : ∀ x ∈ Icc a b, |q x| ≤ K_q := fun x hx => hxq hx
  have hKp_nn : (0:ℝ) ≤ K_p := abs_nonneg _
  have hKq_nn : (0:ℝ) ≤ K_q := abs_nonneg _
  set K : ℝ := 1 + 2 * K_p + K_q with hK_def
  have hKnn : (0:ℝ) ≤ K := by simp [hK_def]; linarith
  have hE_nn : ∀ x, 0 ≤ (y₁ x)^2 + (deriv y₁ x)^2 := fun x => by positivity
  have hy₁_cont : ContinuousOn y₁ (Icc a b) := fun x hx =>
    ((hy₁ x (hJ_sub hx)).continuousAt).continuousWithinAt
  have hy₁'_cont : ContinuousOn (deriv y₁) (Icc a b) := fun x hx =>
    ((hy₁' x (hJ_sub hx)).continuousAt).continuousWithinAt
  refine ⟨K, hKnn, ?_, ?_, ?_⟩
  · exact (hy₁_cont.pow 2).add (hy₁'_cont.pow 2)
  · intro x hx
    have hxJ := hJ_sub hx
    have h1 : HasDerivAt (fun s => (y₁ s)^2) (2 * y₁ x * deriv y₁ x) x := by
      simpa using (hy₁ x hxJ).pow 2
    have h2 : HasDerivAt (fun s => (deriv y₁ s)^2)
        (2 * deriv y₁ x * (-(p x * deriv y₁ x + q x * y₁ x))) x := by
      simpa using (hy₁' x hxJ).pow 2
    exact h1.add h2
  · intro x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hE_nn x)]
    have hKp_x : |p x| ≤ K_p := hKp_le x hx
    have hKq_x : |q x| ≤ K_q := hKq_le x hx
    set u : ℝ := y₁ x
    set v : ℝ := deriv y₁ x
    have hexpand : 2 * u * v + 2 * v * (-(p x * v + q x * u)) =
        2 * u * v - 2 * (p x) * v^2 - 2 * (q x) * u * v := by ring
    rw [hexpand]
    have htri : |2 * u * v - 2 * (p x) * v^2 - 2 * (q x) * u * v|
        ≤ |2 * u * v| + |2 * (p x) * v^2| + |2 * (q x) * u * v| := by
      have h1 : |2 * u * v - 2 * (p x) * v^2 - 2 * (q x) * u * v|
          ≤ |2 * u * v - 2 * (p x) * v^2| + |2 * (q x) * u * v| := by
        have := abs_sub (2 * u * v - 2 * (p x) * v^2) (2 * (q x) * u * v)
        linarith [this]
      have h2 : |2 * u * v - 2 * (p x) * v^2| ≤ |2 * u * v| + |2 * (p x) * v^2| := by
        have := abs_sub (2 * u * v) (2 * (p x) * v^2)
        linarith [this]
      linarith
    have huv : |2 * u * v| ≤ u^2 + v^2 := by
      have h := two_mul_le_add_sq u v
      have h' := two_mul_le_add_sq (-u) v
      have hru : (-u)^2 = u^2 := neg_pow_two u
      rw [hru] at h'
      rcases le_or_gt 0 (u * v) with hp | hn
      · rw [abs_of_nonneg (by nlinarith)]; linarith
      · rw [abs_of_neg (by nlinarith)]; nlinarith
    have hpv2 : |2 * (p x) * v^2| ≤ 2 * K_p * v^2 := by
      rw [show (2 * p x * v^2 : ℝ) = 2 * v^2 * (p x) from by ring,
          abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * v^2)]
      nlinarith [sq_nonneg v]
    have hquv : |2 * (q x) * u * v| ≤ K_q * (u^2 + v^2) := by
      have hsum_nn : (0:ℝ) ≤ u^2 + v^2 := by positivity
      have h_q_2uv : |q x * (2 * u * v)| ≤ K_q * (u^2 + v^2) := by
        rw [abs_mul]
        have := mul_le_mul hKq_x huv (abs_nonneg _) hKq_nn
        exact this
      have hrw : 2 * q x * u * v = q x * (2 * u * v) := by ring
      rw [hrw]; exact h_q_2uv
    calc |2 * u * v - 2 * (p x) * v^2 - 2 * (q x) * u * v|
        ≤ |2 * u * v| + |2 * (p x) * v^2| + |2 * (q x) * u * v| := htri
      _ ≤ (u^2 + v^2) + 2 * K_p * v^2 + K_q * (u^2 + v^2) := by linarith
      _ ≤ K * (u^2 + v^2) := by
          have hu2_nn : (0:ℝ) ≤ u^2 := sq_nonneg _
          have hv2_nn : (0:ℝ) ≤ v^2 := sq_nonneg _
          simp only [hK_def]; nlinarith

/-- If `y₁(a) = 0` and `deriv y₁ a = 0`, then `y₁ ≡ 0` on `Icc a b`. -/
private lemma y₁_eq_zero_on_Icc_of_zero_at_left
    (J : Set ℝ) (hJ_sub : Icc a b ⊆ J)
    (hp_cont : ContinuousOn p J) (hq_cont : ContinuousOn q J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hab : a ≤ b)
    (hza : y₁ a = 0) (hda : deriv y₁ a = 0) :
    ∀ x ∈ Icc a b, y₁ x = 0 := by
  obtain ⟨K, _, hE_cont, hE_deriv, hE_bound⟩ :=
    energy_deriv_bound J hJ_sub hp_cont hq_cont hy₁ hy₁' hab
  -- E(a) = 0
  have hE_a : (y₁ a)^2 + (deriv y₁ a)^2 = 0 := by simp [hza, hda]
  -- E ≡ 0 on Icc a b
  have hE_zero := eq_zero_of_norm_deriv_bound_left hE_cont
    (fun x hx => (hE_deriv x ⟨hx.1, le_of_lt hx.2⟩).hasDerivWithinAt)
    hE_a
    (fun x hx => hE_bound x ⟨hx.1, le_of_lt hx.2⟩)
  -- Extract y₁(x) = 0 from E(x) = 0
  intro x hx
  have hEx : (y₁ x)^2 + (deriv y₁ x)^2 = 0 := hE_zero x hx
  have hy2 : (y₁ x)^2 = 0 := by
    have h1 : (0:ℝ) ≤ (y₁ x)^2 := sq_nonneg _
    have h2 : (0:ℝ) ≤ (deriv y₁ x)^2 := sq_nonneg _
    linarith
  exact pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0) |>.mp hy2

/-- If `y₁(b) = 0` and `deriv y₁ b = 0`, then `y₁ ≡ 0` on `Icc a b`. -/
private lemma y₁_eq_zero_on_Icc_of_zero_at_right
    (J : Set ℝ) (hJ_sub : Icc a b ⊆ J)
    (hp_cont : ContinuousOn p J) (hq_cont : ContinuousOn q J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hab : a ≤ b)
    (hzb : y₁ b = 0) (hdb : deriv y₁ b = 0) :
    ∀ x ∈ Icc a b, y₁ x = 0 := by
  obtain ⟨K, _, hE_cont, hE_deriv, hE_bound⟩ :=
    energy_deriv_bound J hJ_sub hp_cont hq_cont hy₁ hy₁' hab
  have hE_b : (y₁ b)^2 + (deriv y₁ b)^2 = 0 := by simp [hzb, hdb]
  have hE_zero := eq_zero_of_norm_deriv_bound_right hab hE_cont
    (fun x hx => hE_deriv x ⟨le_of_lt hx.1, hx.2⟩)
    hE_b
    (fun x hx => hE_bound x ⟨le_of_lt hx.1, hx.2⟩)
  intro x hx
  have hEx : (y₁ x)^2 + (deriv y₁ x)^2 = 0 := hE_zero x hx
  have hy2 : (y₁ x)^2 = 0 := by
    have h1 : (0:ℝ) ≤ (y₁ x)^2 := sq_nonneg _
    have h2 : (0:ℝ) ≤ (deriv y₁ x)^2 := sq_nonneg _
    linarith
  exact pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0) |>.mp hy2

/-- `deriv y₁ a ≠ 0`. -/
lemma deriv_y₁_a_ne_zero
    (J : Set ℝ) (hJ_sub : Icc a b ⊆ J)
    (hp_cont : ContinuousOn p J) (hq_cont : ContinuousOn q J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hab : a < b)
    (hza : y₁ a = 0)
    (hne : ∀ x ∈ Ioo a b, y₁ x ≠ 0) :
    deriv y₁ a ≠ 0 := by
  intro hda
  have h := y₁_eq_zero_on_Icc_of_zero_at_left J hJ_sub hp_cont hq_cont hy₁ hy₁' hab.le hza hda
  obtain ⟨c, hc⟩ := nonempty_Ioo.mpr hab
  exact hne c hc (h c ⟨le_of_lt hc.1, le_of_lt hc.2⟩)

/-- `deriv y₁ b ≠ 0`. -/
lemma deriv_y₁_b_ne_zero
    (J : Set ℝ) (hJ_sub : Icc a b ⊆ J)
    (hp_cont : ContinuousOn p J) (hq_cont : ContinuousOn q J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hab : a < b)
    (hzb : y₁ b = 0)
    (hne : ∀ x ∈ Ioo a b, y₁ x ≠ 0) :
    deriv y₁ b ≠ 0 := by
  intro hdb
  have h := y₁_eq_zero_on_Icc_of_zero_at_right J hJ_sub hp_cont hq_cont hy₁ hy₁' hab.le hzb hdb
  obtain ⟨c, hc⟩ := nonempty_Ioo.mpr hab
  exact hne c hc (h c ⟨le_of_lt hc.1, le_of_lt hc.2⟩)

/-- `y₂(a) ≠ 0`: from `W(a) = -y₂(a)·deriv y₁ a ≠ 0` and `deriv y₁ a ≠ 0`. -/
lemma y₂_a_ne_zero
    (J : Set ℝ) (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
    (hp_cont : ContinuousOn p J) (hq_cont : ContinuousOn q J)
    (hJ_sub : Icc a b ⊆ J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (hW : ∃ x₀ ∈ J, W y₁ y₂ x₀ ≠ 0)
    (hab : a < b)
    (hza : y₁ a = 0) (hzb : y₁ b = 0)
    (hne : ∀ x ∈ Ioo a b, y₁ x ≠ 0) :
    y₂ a ≠ 0 := by
  intro hy₂a
  have hWa_ne : W y₁ y₂ a ≠ 0 := W_nonzero_on_Icc J hJ_open hJ_conn hp_cont hJ_sub
    hy₁ hy₁' hy₂ hy₂' hW hab.le a (left_mem_Icc.mpr hab.le)
  apply hWa_ne
  -- W(a) = y₁(a) · deriv y₂ a − y₂(a) · deriv y₁ a = 0 - 0 · ... = 0
  show y₁ a * deriv y₂ a - y₂ a * deriv y₁ a = 0
  rw [hza, hy₂a]; ring

/-- `y₂(b) ≠ 0`: similar to a-side. -/
lemma y₂_b_ne_zero
    (J : Set ℝ) (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
    (hp_cont : ContinuousOn p J) (hq_cont : ContinuousOn q J)
    (hJ_sub : Icc a b ⊆ J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (hW : ∃ x₀ ∈ J, W y₁ y₂ x₀ ≠ 0)
    (hab : a < b)
    (hza : y₁ a = 0) (hzb : y₁ b = 0)
    (hne : ∀ x ∈ Ioo a b, y₁ x ≠ 0) :
    y₂ b ≠ 0 := by
  intro hy₂b
  have hWb_ne : W y₁ y₂ b ≠ 0 := W_nonzero_on_Icc J hJ_open hJ_conn hp_cont hJ_sub
    hy₁ hy₁' hy₂ hy₂' hW hab.le b (right_mem_Icc.mpr hab.le)
  apply hWb_ne
  show y₁ b * deriv y₂ b - y₂ b * deriv y₁ b = 0
  rw [hzb, hy₂b]; ring

/-- A continuous function on `Icc a b` that's never zero has constant strict sign. -/
private lemma constant_sign_of_continuous_ne_zero
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hne : ∀ x ∈ Icc a b, f x ≠ 0) :
    (∀ x ∈ Icc a b, 0 < f x) ∨ (∀ x ∈ Icc a b, f x < 0) := by
  classical
  by_contra hc
  push_neg at hc
  obtain ⟨⟨x₁, hx₁_in, hx₁⟩, ⟨x₂, hx₂_in, hx₂⟩⟩ := hc
  have hx₁_neg : f x₁ < 0 := lt_of_le_of_ne hx₁ (hne x₁ hx₁_in)
  have hx₂_pos : 0 < f x₂ := lt_of_le_of_ne hx₂ (Ne.symm (hne x₂ hx₂_in))
  have huIcc_sub : uIcc x₁ x₂ ⊆ Icc a b := uIcc_subset_Icc hx₁_in hx₂_in
  have hf_uIcc : ContinuousOn f (uIcc x₁ x₂) := hf.mono huIcc_sub
  have h0_in : (0:ℝ) ∈ uIcc (f x₁) (f x₂) := by
    have h_lt : f x₁ < f x₂ := lt_trans hx₁_neg hx₂_pos
    rw [uIcc_of_le h_lt.le]
    exact ⟨hx₁_neg.le, hx₂_pos.le⟩
  obtain ⟨c, hc_in, hc_zero⟩ := intermediate_value_uIcc hf_uIcc h0_in
  exact hne c (huIcc_sub hc_in) hc_zero

/-- The quotient `y₂/y₁` has derivative `W/y₁²` on `Ioo a b`. -/
lemma hasDerivAt_quotient
    (J : Set ℝ) (hJ_sub : Icc a b ⊆ J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hne : ∀ x ∈ Ioo a b, y₁ x ≠ 0)
    {x : ℝ} (hx : x ∈ Ioo a b) :
    HasDerivAt (fun s => y₂ s / y₁ s) (W y₁ y₂ x / (y₁ x)^2) x := by
  have hxJ : x ∈ J := hJ_sub ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hy₁x_ne : y₁ x ≠ 0 := hne x hx
  have hd := (hy₂ x hxJ).div (hy₁ x hxJ) hy₁x_ne
  show HasDerivAt (fun s => y₂ s / y₁ s) (W y₁ y₂ x / (y₁ x)^2) x
  have heq : (deriv y₂ x * y₁ x - y₂ x * deriv y₁ x) / y₁ x ^ 2 = W y₁ y₂ x / (y₁ x)^2 := by
    simp [W]; ring
  rw [← heq]
  exact hd

/-- `y₂/y₁` is strictly monotone on `Ioo a b` (either strictly increasing or strictly
decreasing), since its derivative `-W/y₁²` has constant sign there. -/
lemma quotient_strictMono_or_strictAnti
    (J : Set ℝ) (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
    (hp_cont : ContinuousOn p J) (hq_cont : ContinuousOn q J)
    (hJ_sub : Icc a b ⊆ J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (hW : ∃ x₀ ∈ J, W y₁ y₂ x₀ ≠ 0)
    (hab : a < b)
    (hne : ∀ x ∈ Ioo a b, y₁ x ≠ 0) :
    StrictMonoOn (fun s => y₂ s / y₁ s) (Ioo a b) ∨
    StrictAntiOn (fun s => y₂ s / y₁ s) (Ioo a b) := by
  have hWnz : ∀ x ∈ Icc a b, W y₁ y₂ x ≠ 0 :=
    W_nonzero_on_Icc J hJ_open hJ_conn hp_cont hJ_sub hy₁ hy₁' hy₂ hy₂' hW hab.le
  have hW_cont_Icc : ContinuousOn (W y₁ y₂) (Icc a b) :=
    fun x hx => ((hasDerivAt_W J hy₁ hy₁' hy₂ hy₂' (hJ_sub hx)).continuousAt).continuousWithinAt
  -- W has constant strict sign on Icc a b.
  have hWsign := constant_sign_of_continuous_ne_zero hab.le hW_cont_Icc hWnz
  -- The quotient's derivative is W/y₁².
  have hQuot_deriv : ∀ x ∈ Ioo a b, HasDerivAt (fun s => y₂ s / y₁ s)
      (W y₁ y₂ x / (y₁ x)^2) x :=
    fun x hx => hasDerivAt_quotient J hJ_sub hy₁ hy₂ hne hx
  -- Continuity of y₂/y₁ on Icc Ioo a b.
  have hQuot_cont : ContinuousOn (fun s => y₂ s / y₁ s) (Ioo a b) := fun x hx =>
    ((hQuot_deriv x hx).continuousAt).continuousWithinAt
  have hConvex : Convex ℝ (Ioo a b) := convex_Ioo a b
  have hInterior : interior (Ioo a b) = Ioo a b := isOpen_Ioo.interior_eq
  -- The derivative function for y₂/y₁ on Ioo a b.
  set qd : ℝ → ℝ := fun x => W y₁ y₂ x / (y₁ x)^2 with hqd_def
  have hQuot_derivWithin : ∀ x ∈ interior (Ioo a b),
      HasDerivWithinAt (fun s => y₂ s / y₁ s) (qd x) (interior (Ioo a b)) x := by
    intro x hx_int
    rw [hInterior] at hx_int
    exact (hQuot_deriv x hx_int).hasDerivWithinAt
  rcases hWsign with hWpos | hWneg
  · -- W > 0 ⟹ qd > 0 ⟹ StrictMono
    left
    refine strictMonoOn_of_hasDerivWithinAt_pos (f' := qd) hConvex hQuot_cont
      hQuot_derivWithin ?_
    intro x hx_int
    rw [hInterior] at hx_int
    have hxIcc : x ∈ Icc a b := ⟨le_of_lt hx_int.1, le_of_lt hx_int.2⟩
    have hWpos_x : 0 < W y₁ y₂ x := hWpos x hxIcc
    have hy₁ne : y₁ x ≠ 0 := hne x hx_int
    have hy₁sq : 0 < (y₁ x)^2 := by
      have : (y₁ x)^2 ≠ 0 := pow_ne_zero 2 hy₁ne
      exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm this)
    show 0 < qd x
    exact div_pos hWpos_x hy₁sq
  · -- W < 0 ⟹ qd < 0 ⟹ StrictAnti
    right
    refine strictAntiOn_of_hasDerivWithinAt_neg (f' := qd) hConvex hQuot_cont
      hQuot_derivWithin ?_
    intro x hx_int
    rw [hInterior] at hx_int
    have hxIcc : x ∈ Icc a b := ⟨le_of_lt hx_int.1, le_of_lt hx_int.2⟩
    have hWneg_x : W y₁ y₂ x < 0 := hWneg x hxIcc
    have hy₁ne : y₁ x ≠ 0 := hne x hx_int
    have hy₁sq : 0 < (y₁ x)^2 := by
      have : (y₁ x)^2 ≠ 0 := pow_ne_zero 2 hy₁ne
      exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm this)
    show qd x < 0
    exact div_neg_of_neg_of_pos hWneg_x hy₁sq

/-- Constant sign on `Ioo`: continuous + never zero. -/
private lemma constant_sign_on_Ioo
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Ioo a b))
    (hne : ∀ x ∈ Ioo a b, f x ≠ 0) :
    (∀ x ∈ Ioo a b, 0 < f x) ∨ (∀ x ∈ Ioo a b, f x < 0) := by
  classical
  by_contra hc
  push_neg at hc
  obtain ⟨⟨x₁, hx₁_in, hx₁⟩, ⟨x₂, hx₂_in, hx₂⟩⟩ := hc
  have hx₁_neg : f x₁ < 0 := lt_of_le_of_ne hx₁ (hne x₁ hx₁_in)
  have hx₂_pos : 0 < f x₂ := lt_of_le_of_ne hx₂ (Ne.symm (hne x₂ hx₂_in))
  have huIcc_sub : uIcc x₁ x₂ ⊆ Ioo a b := by
    intro z hz
    rw [uIcc, mem_Icc] at hz
    obtain ⟨hz1, hz2⟩ := hz
    refine ⟨lt_of_lt_of_le ?_ hz1, lt_of_le_of_lt hz2 ?_⟩
    · exact lt_min hx₁_in.1 hx₂_in.1
    · exact max_lt hx₁_in.2 hx₂_in.2
  have hf_uIcc : ContinuousOn f (uIcc x₁ x₂) := hf.mono huIcc_sub
  have h_lt : f x₁ < f x₂ := lt_trans hx₁_neg hx₂_pos
  have h0_in : (0:ℝ) ∈ uIcc (f x₁) (f x₂) := by
    rw [uIcc_of_le h_lt.le]
    exact ⟨hx₁_neg.le, hx₂_pos.le⟩
  obtain ⟨c, hc_in, hc_zero⟩ := intermediate_value_uIcc hf_uIcc h0_in
  exact hne c (huIcc_sub hc_in) hc_zero

/-- If `y₁ a = 0`, `y₁ > 0` near `a` from the right, and `deriv y₁ a ≠ 0`, then `0 < deriv y₁ a`. -/
private lemma deriv_at_a_pos_of_pos_nearby
    (J : Set ℝ) (hJ_sub : Icc a b ⊆ J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hab : a < b) (hza : y₁ a = 0)
    (hpos : ∀ x ∈ Ioo a b, 0 < y₁ x)
    (hne : deriv y₁ a ≠ 0) :
    0 < deriv y₁ a := by
  have ha_in : a ∈ J := hJ_sub (left_mem_Icc.mpr hab.le)
  have hda : HasDerivAt y₁ (deriv y₁ a) a := hy₁ a ha_in
  have hslope := hda.tendsto_slope
  have hsub_ne : 𝓝[Ioi a] a ≤ 𝓝[≠] a :=
    nhdsWithin_mono _ (fun x hx => ne_of_gt hx)
  have hslope_right : Tendsto (slope y₁ a) (𝓝[Ioi a] a) (𝓝 (deriv y₁ a)) :=
    hslope.mono_left hsub_ne
  have h_in : ∀ᶠ y in 𝓝[Ioi a] a, y ∈ Ioo a b := by
    have h_Ioi : ∀ᶠ y in 𝓝[Ioi a] a, y ∈ Ioi a := self_mem_nhdsWithin
    have h_Iio_nhd : ∀ᶠ y in 𝓝 a, y < b := eventually_lt_nhds hab
    have h_Iio : ∀ᶠ y in 𝓝[Ioi a] a, y < b :=
      h_Iio_nhd.filter_mono nhdsWithin_le_nhds
    filter_upwards [h_Ioi, h_Iio] with y hyi hyio
    exact ⟨hyi, hyio⟩
  have h_slope_nn : ∀ᶠ y in 𝓝[Ioi a] a, 0 ≤ slope y₁ a y := by
    filter_upwards [h_in] with y hy
    have hya : a < y := hy.1
    have hy_pos : 0 < y₁ y := hpos y hy
    show 0 ≤ slope y₁ a y
    rw [slope_def_field, hza, sub_zero]
    have hinv : (0:ℝ) ≤ (y - a)⁻¹ := le_of_lt (inv_pos.mpr (sub_pos.mpr hya))
    exact div_nonneg hy_pos.le (sub_nonneg.mpr hya.le)
  have h_ge : 0 ≤ deriv y₁ a := ge_of_tendsto hslope_right h_slope_nn
  exact lt_of_le_of_ne h_ge (Ne.symm hne)

/-- If `y₁ b = 0`, `y₁ > 0` near `b` from the left, and `deriv y₁ b ≠ 0`, then `deriv y₁ b < 0`. -/
private lemma deriv_at_b_neg_of_pos_nearby
    (J : Set ℝ) (hJ_sub : Icc a b ⊆ J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hab : a < b) (hzb : y₁ b = 0)
    (hpos : ∀ x ∈ Ioo a b, 0 < y₁ x)
    (hne : deriv y₁ b ≠ 0) :
    deriv y₁ b < 0 := by
  have hb_in : b ∈ J := hJ_sub (right_mem_Icc.mpr hab.le)
  have hdb : HasDerivAt y₁ (deriv y₁ b) b := hy₁ b hb_in
  have hslope := hdb.tendsto_slope
  have hsub_ne : 𝓝[Iio b] b ≤ 𝓝[≠] b :=
    nhdsWithin_mono _ (fun x hx => ne_of_lt hx)
  have hslope_left : Tendsto (slope y₁ b) (𝓝[Iio b] b) (𝓝 (deriv y₁ b)) :=
    hslope.mono_left hsub_ne
  have h_in : ∀ᶠ y in 𝓝[Iio b] b, y ∈ Ioo a b := by
    have h_Iio : ∀ᶠ y in 𝓝[Iio b] b, y ∈ Iio b := self_mem_nhdsWithin
    have h_Ioi_nhd : ∀ᶠ y in 𝓝 b, a < y := eventually_gt_nhds hab
    have h_Ioi : ∀ᶠ y in 𝓝[Iio b] b, a < y :=
      h_Ioi_nhd.filter_mono nhdsWithin_le_nhds
    filter_upwards [h_Iio, h_Ioi] with y hyi hyio
    exact ⟨hyio, hyi⟩
  have h_slope_np : ∀ᶠ y in 𝓝[Iio b] b, slope y₁ b y ≤ 0 := by
    filter_upwards [h_in] with y hy
    have hyb : y < b := hy.2
    have hy_pos : 0 < y₁ y := hpos y hy
    show slope y₁ b y ≤ 0
    rw [slope_def_field, hzb, sub_zero]
    have hsub_neg : y - b < 0 := sub_neg.mpr hyb
    exact (div_neg_of_pos_of_neg hy_pos hsub_neg).le
  have h_le : deriv y₁ b ≤ 0 := le_of_tendsto hslope_left h_slope_np
  exact lt_of_le_of_ne h_le hne

/-- If y₁ < 0 instead: deriv y₁ a < 0. -/
private lemma deriv_at_a_neg_of_neg_nearby
    (J : Set ℝ) (hJ_sub : Icc a b ⊆ J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hab : a < b) (hza : y₁ a = 0)
    (hneg : ∀ x ∈ Ioo a b, y₁ x < 0)
    (hne : deriv y₁ a ≠ 0) :
    deriv y₁ a < 0 := by
  -- Apply the positive-side version to -y₁.
  set z : ℝ → ℝ := fun x => -y₁ x with hz_def
  have hz_J : ∀ x ∈ J, HasDerivAt z (-(deriv y₁ x)) x := fun x hx =>
    (hy₁ x hx).neg
  have hz_a : z a = 0 := by simp [hz_def, hza]
  have hz_pos : ∀ x ∈ Ioo a b, 0 < z x := fun x hx => by
    show 0 < -y₁ x; linarith [hneg x hx]
  have hz_deriv_eq : deriv z a = -(deriv y₁ a) := by
    have := (hy₁ a (hJ_sub (left_mem_Icc.mpr hab.le))).neg
    exact this.deriv
  have hz_ne : deriv z a ≠ 0 := by rw [hz_deriv_eq]; intro h; exact hne (neg_eq_zero.mp h)
  -- Use deriv_at_a_pos_of_pos_nearby with z, but we need ∀ x ∈ J, HasDerivAt z (deriv z x) x.
  have hz_full : ∀ x ∈ J, HasDerivAt z (deriv z x) x := fun x hx => by
    have := hz_J x hx
    have hd : deriv z x = -(deriv y₁ x) := this.deriv
    rw [hd]; exact this
  have h := deriv_at_a_pos_of_pos_nearby (y₁ := z) (a := a) (b := b)
    J hJ_sub hz_full hab hz_a hz_pos hz_ne
  rw [hz_deriv_eq] at h
  linarith

/-- If y₁ < 0 instead: deriv y₁ b > 0. -/
private lemma deriv_at_b_pos_of_neg_nearby
    (J : Set ℝ) (hJ_sub : Icc a b ⊆ J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hab : a < b) (hzb : y₁ b = 0)
    (hneg : ∀ x ∈ Ioo a b, y₁ x < 0)
    (hne : deriv y₁ b ≠ 0) :
    0 < deriv y₁ b := by
  set z : ℝ → ℝ := fun x => -y₁ x with hz_def
  have hz_b : z b = 0 := by simp [hz_def, hzb]
  have hz_pos : ∀ x ∈ Ioo a b, 0 < z x := fun x hx => by
    show 0 < -y₁ x; linarith [hneg x hx]
  have hz_deriv_eq : deriv z b = -(deriv y₁ b) := by
    have := (hy₁ b (hJ_sub (right_mem_Icc.mpr hab.le))).neg
    exact this.deriv
  have hz_ne : deriv z b ≠ 0 := by rw [hz_deriv_eq]; intro h; exact hne (neg_eq_zero.mp h)
  have hz_full : ∀ x ∈ J, HasDerivAt z (deriv z x) x := fun x hx => by
    have := (hy₁ x hx).neg
    have hd : deriv z x = -(deriv y₁ x) := this.deriv
    rw [hd]; exact this
  have h := deriv_at_b_neg_of_pos_nearby (y₁ := z) (a := a) (b := b)
    J hJ_sub hz_full hab hz_b hz_pos hz_ne
  rw [hz_deriv_eq] at h
  linarith

/-- y₁'(a) and y₁'(b) have opposite signs. -/
lemma deriv_y₁_a_b_opposite_signs
    (J : Set ℝ) (hJ_open : IsOpen J)
    (hp_cont : ContinuousOn p J) (hq_cont : ContinuousOn q J)
    (hJ_sub : Icc a b ⊆ J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hab : a < b)
    (hza : y₁ a = 0) (hzb : y₁ b = 0)
    (hne : ∀ x ∈ Ioo a b, y₁ x ≠ 0) :
    deriv y₁ a * deriv y₁ b < 0 := by
  have hda_ne : deriv y₁ a ≠ 0 := deriv_y₁_a_ne_zero J hJ_sub hp_cont hq_cont
    hy₁ hy₁' hab hza hne
  have hdb_ne : deriv y₁ b ≠ 0 := deriv_y₁_b_ne_zero J hJ_sub hp_cont hq_cont
    hy₁ hy₁' hab hzb hne
  -- y₁ continuous on Ioo, never zero on Ioo, so constant sign.
  have hy₁_cont_Ioo : ContinuousOn y₁ (Ioo a b) := fun x hx =>
    ((hy₁ x (hJ_sub ⟨le_of_lt hx.1, le_of_lt hx.2⟩)).continuousAt).continuousWithinAt
  rcases constant_sign_on_Ioo hy₁_cont_Ioo hne with hpos | hneg
  · have hda_pos : 0 < deriv y₁ a :=
      deriv_at_a_pos_of_pos_nearby J hJ_sub hy₁ hab hza hpos hda_ne
    have hdb_neg : deriv y₁ b < 0 :=
      deriv_at_b_neg_of_pos_nearby J hJ_sub hy₁ hab hzb hpos hdb_ne
    exact mul_neg_of_pos_of_neg hda_pos hdb_neg
  · have hda_neg : deriv y₁ a < 0 :=
      deriv_at_a_neg_of_neg_nearby J hJ_sub hy₁ hab hza hneg hda_ne
    have hdb_pos : 0 < deriv y₁ b :=
      deriv_at_b_pos_of_neg_nearby J hJ_sub hy₁ hab hzb hneg hdb_ne
    exact mul_neg_of_neg_of_pos hda_neg hdb_pos

/-- y₂(a) · y₂(b) < 0. -/
lemma y₂_a_b_opposite_signs
    (J : Set ℝ) (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
    (hp_cont : ContinuousOn p J) (hq_cont : ContinuousOn q J)
    (hJ_sub : Icc a b ⊆ J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (hW : ∃ x₀ ∈ J, W y₁ y₂ x₀ ≠ 0)
    (hab : a < b)
    (hza : y₁ a = 0) (hzb : y₁ b = 0)
    (hne : ∀ x ∈ Ioo a b, y₁ x ≠ 0) :
    y₂ a * y₂ b < 0 := by
  have hWa_ne : W y₁ y₂ a ≠ 0 := W_nonzero_on_Icc J hJ_open hJ_conn hp_cont hJ_sub
    hy₁ hy₁' hy₂ hy₂' hW hab.le a (left_mem_Icc.mpr hab.le)
  have hWb_ne : W y₁ y₂ b ≠ 0 := W_nonzero_on_Icc J hJ_open hJ_conn hp_cont hJ_sub
    hy₁ hy₁' hy₂ hy₂' hW hab.le b (right_mem_Icc.mpr hab.le)
  have hWab_pos : 0 < W y₁ y₂ a * W y₁ y₂ b := by
    -- W has constant sign on Icc a b.
    have hWnz : ∀ x ∈ Icc a b, W y₁ y₂ x ≠ 0 :=
      W_nonzero_on_Icc J hJ_open hJ_conn hp_cont hJ_sub hy₁ hy₁' hy₂ hy₂' hW hab.le
    have hW_cont_Icc : ContinuousOn (W y₁ y₂) (Icc a b) :=
      fun x hx => ((hasDerivAt_W J hy₁ hy₁' hy₂ hy₂' (hJ_sub hx)).continuousAt).continuousWithinAt
    have hWsign := constant_sign_of_continuous_ne_zero hab.le hW_cont_Icc hWnz
    rcases hWsign with hp | hn
    · exact mul_pos (hp a (left_mem_Icc.mpr hab.le)) (hp b (right_mem_Icc.mpr hab.le))
    · exact mul_pos_of_neg_of_neg (hn a (left_mem_Icc.mpr hab.le)) (hn b (right_mem_Icc.mpr hab.le))
  have hda_db_neg : deriv y₁ a * deriv y₁ b < 0 :=
    deriv_y₁_a_b_opposite_signs J hJ_open hp_cont hq_cont hJ_sub
      hy₁ hy₁' hab hza hzb hne
  -- Algebraic identity: W(a) · W(b) = y₂(a) · y₂(b) · deriv y₁ a · deriv y₁ b.
  have hidentity : W y₁ y₂ a * W y₁ y₂ b = y₂ a * y₂ b * (deriv y₁ a * deriv y₁ b) := by
    show (y₁ a * deriv y₂ a - y₂ a * deriv y₁ a) * (y₁ b * deriv y₂ b - y₂ b * deriv y₁ b)
        = y₂ a * y₂ b * (deriv y₁ a * deriv y₁ b)
    rw [hza, hzb]; ring
  -- W(a)·W(b) > 0 and y₁'(a)·y₁'(b) < 0 ⟹ y₂(a)·y₂(b) < 0.
  rw [hidentity] at hWab_pos
  -- hWab_pos: 0 < y₂ a * y₂ b * (deriv y₁ a * deriv y₁ b)
  -- with deriv y₁ a * deriv y₁ b < 0, conclude y₂ a * y₂ b < 0.
  have hd_ne : deriv y₁ a * deriv y₁ b ≠ 0 := hda_db_neg.ne
  nlinarith [hda_db_neg, hWab_pos]

/-- Existence of a zero of y₂ in (a, b). -/
lemma exists_zero_y₂
    (J : Set ℝ) (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
    (hp_cont : ContinuousOn p J) (hq_cont : ContinuousOn q J)
    (hJ_sub : Icc a b ⊆ J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (hW : ∃ x₀ ∈ J, W y₁ y₂ x₀ ≠ 0)
    (hab : a < b)
    (hza : y₁ a = 0) (hzb : y₁ b = 0)
    (hne : ∀ x ∈ Ioo a b, y₁ x ≠ 0) :
    ∃ c ∈ Ioo a b, y₂ c = 0 := by
  have hsign := y₂_a_b_opposite_signs J hJ_open hJ_conn hp_cont hq_cont hJ_sub
    hy₁ hy₁' hy₂ hy₂' hW hab hza hzb hne
  have hy₂_cont : ContinuousOn y₂ (Icc a b) := fun x hx =>
    ((hy₂ x (hJ_sub hx)).continuousAt).continuousWithinAt
  -- Apply IVT: y₂(a) and y₂(b) have opposite signs (product < 0).
  have h0 : (0:ℝ) ∈ Ioo (min (y₂ a) (y₂ b)) (max (y₂ a) (y₂ b)) := by
    refine ⟨?_, ?_⟩
    · rcases le_or_gt (y₂ a) (y₂ b) with h | h
      · rw [min_eq_left h]
        nlinarith [hsign]
      · rw [min_eq_right h.le]
        nlinarith [hsign]
    · rcases le_or_gt (y₂ a) (y₂ b) with h | h
      · rw [max_eq_right h]
        nlinarith [hsign]
      · rw [max_eq_left h.le]
        nlinarith [hsign]
  -- Apply intermediate_value_Ioo'
  rcases le_total (y₂ a) (y₂ b) with hyy | hyy
  · -- y₂ a ≤ y₂ b
    have h0' : (0:ℝ) ∈ Ioo (y₂ a) (y₂ b) := by
      have h1 : min (y₂ a) (y₂ b) = y₂ a := min_eq_left hyy
      have h2 : max (y₂ a) (y₂ b) = y₂ b := max_eq_right hyy
      rw [h1, h2] at h0; exact h0
    obtain ⟨c, hc_in, hc_zero⟩ := intermediate_value_Ioo hab.le hy₂_cont h0'
    exact ⟨c, hc_in, hc_zero⟩
  · -- y₂ b ≤ y₂ a
    have h0' : (0:ℝ) ∈ Ioo (y₂ b) (y₂ a) := by
      have h1 : min (y₂ a) (y₂ b) = y₂ b := min_eq_right hyy
      have h2 : max (y₂ a) (y₂ b) = y₂ a := max_eq_left hyy
      rw [h1, h2] at h0; exact h0
    obtain ⟨c, hc_in, hc_zero⟩ := intermediate_value_Ioo' hab.le hy₂_cont h0'
    exact ⟨c, hc_in, hc_zero⟩

/-- Uniqueness: y₂ has at most one zero in `Ioo a b`. -/
lemma unique_zero_y₂
    (J : Set ℝ) (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
    (hp_cont : ContinuousOn p J) (hq_cont : ContinuousOn q J)
    (hJ_sub : Icc a b ⊆ J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (hW : ∃ x₀ ∈ J, W y₁ y₂ x₀ ≠ 0)
    (hab : a < b)
    (hne : ∀ x ∈ Ioo a b, y₁ x ≠ 0)
    {c₁ c₂ : ℝ} (hc₁ : c₁ ∈ Ioo a b) (hc₂ : c₂ ∈ Ioo a b)
    (h₁ : y₂ c₁ = 0) (h₂ : y₂ c₂ = 0) :
    c₁ = c₂ := by
  have hquot := quotient_strictMono_or_strictAnti J hJ_open hJ_conn hp_cont hq_cont hJ_sub
    hy₁ hy₁' hy₂ hy₂' hW hab hne
  have hy₁_c₁ : y₁ c₁ ≠ 0 := hne c₁ hc₁
  have hy₁_c₂ : y₁ c₂ ≠ 0 := hne c₂ hc₂
  have heq : y₂ c₁ / y₁ c₁ = y₂ c₂ / y₁ c₂ := by rw [h₁, h₂]; simp
  rcases hquot with h | h
  · exact h.injOn hc₁ hc₂ heq
  · exact h.injOn hc₁ hc₂ heq

end Submission.Helpers
