import Mathlib

open scoped Real
open Set Real

namespace Submission.Helpers

/-! ## Forward direction helpers -/

/-
sin(n*x) has derivative n*cos(n*x)
-/
lemma hasDerivAt_sin_mul (n : ℝ) (x : ℝ) :
    HasDerivAt (fun x => sin (n * x)) (n * cos (n * x)) x := by
  simpa [ mul_comm n ] using HasDerivAt.sin ( HasDerivAt.const_mul n ( hasDerivAt_id x ) )

/-
n*cos(n*x) has derivative -(n^2 * sin(n*x))
-/
lemma hasDerivAt_ncos_mul (n : ℝ) (x : ℝ) :
    HasDerivAt (fun x => n * cos (n * x)) (-(n ^ 2 * sin (n * x))) x := by
  convert HasDerivAt.const_mul n ( HasDerivAt.cos ( hasDerivAt_id' x |> HasDerivAt.const_mul n ) ) using 1 ; ring

/-- deriv of sin(n*x) is n*cos(n*x) -/
lemma deriv_sin_mul (n : ℝ) (x : ℝ) :
    deriv (fun x => sin (n * x)) x = n * cos (n * x) :=
  (hasDerivAt_sin_mul n x).deriv

/-
For n > 0, there exists a point in (0, π) where sin(n*x) ≠ 0
-/
lemma sin_mul_nonzero_in_Ioo {n : ℕ} (hn : 0 < n) :
    ∃ x ∈ Ioo (0 : ℝ) π, sin (↑n * x) ≠ 0 := by
  refine' ⟨ Real.pi / 2 / n, _, _ ⟩ <;> norm_num [ mul_div_cancel₀, hn.ne' ];
  exact ⟨ by positivity, by rw [ div_lt_iff₀ ( by positivity ) ] ; nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ⟩

/-
The forward direction: if λ = n² for some positive n, then there's a non-trivial solution
-/
lemma forward_direction {lam : ℝ} {n : ℕ} (hn : 0 < n) (hlam : lam = (n : ℝ) ^ 2) :
    ∃ (y : ℝ → ℝ) (J : Set ℝ),
      IsOpen J ∧ Icc (0 : ℝ) π ⊆ J ∧
      (∀ x ∈ J, HasDerivAt y (deriv y x) x) ∧
      (∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x) ∧
      y 0 = 0 ∧ y π = 0 ∧
      ∃ x ∈ Ioo (0 : ℝ) π, y x ≠ 0 := by
  refine' ⟨ fun x => Real.sin ( n * x ), Set.univ, isOpen_univ, Set.subset_univ _, _, _, _, _, _ ⟩ <;> norm_num;
  · fun_prop;
  · intro x;
    rw [ show deriv ( fun x => sin ( n * x ) ) = fun x => n * cos ( n * x ) by funext; simp +decide [ mul_comm ] ] ; simpa [ hlam, mul_assoc, mul_comm, mul_left_comm ] using hasDerivAt_ncos_mul n x;
  · exact sin_mul_nonzero_in_Ioo hn

/-! ## Backward direction helpers -/

/-
Key uniqueness lemma: if g'' + λg = 0 on an open set J ⊇ [0,π] with λ > 0,
    g(0) = 0, g'(0) = 0, then g = 0 on [0, π]
-/
lemma ode_uniqueness_pos {g : ℝ → ℝ} {lam : ℝ} {J : Set ℝ}
    (hJ : IsOpen J) (hJI : Icc 0 π ⊆ J)
    (hlam : 0 < lam)
    (hg_diff : ∀ x ∈ J, HasDerivAt g (deriv g x) x)
    (hg'_diff : ∀ x ∈ J, HasDerivAt (deriv g) (-(lam * g x)) x)
    (hg0 : g 0 = 0) (hg'0 : deriv g 0 = 0) :
    ∀ x ∈ Icc (0 : ℝ) π, g x = 0 := by
  -- Define the energy function E(x) = g(x)^2 + (deriv g x)^2 / lam.
  set E : ℝ → ℝ := fun x => g x^2 + (deriv g x)^2 / lam;
  have hE_diff : DifferentiableOn ℝ E (Set.Icc 0 Real.pi) := by
    exact fun x hx => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.add ( DifferentiableAt.pow ( hg_diff x ( hJI hx ) |> HasDerivAt.differentiableAt ) 2 ) ( DifferentiableAt.div_const ( DifferentiableAt.pow ( hg'_diff x ( hJI hx ) |> HasDerivAt.differentiableAt ) 2 ) _ ) );
  have hE_deriv_zero : ∀ x ∈ Set.Ioo 0 Real.pi, deriv E x = 0 := by
    intro x hx; erw [ deriv_add ] <;> norm_num [ hg_diff x ( hJI <| Set.Ioo_subset_Icc_self hx ) |> HasDerivAt.differentiableAt, hg'_diff x ( hJI <| Set.Ioo_subset_Icc_self hx ) |> HasDerivAt.differentiableAt, hlam.ne' ] ; ring;
    rw [ hg'_diff x ( hJI <| Set.Ioo_subset_Icc_self hx ) |> HasDerivAt.deriv ] ; ring;
    norm_num [ hlam.ne' ];
  have hE_const : ∀ x ∈ Set.Icc 0 Real.pi, E x = E 0 := by
    intro x hx
    by_contra hE_neq;
    have := exists_deriv_eq_slope E ( show x > 0 from hx.1.lt_of_ne ( by aesop_cat ) ) ; simp_all +decide [ sub_eq_iff_eq_add ] ;
    exact absurd ( this ( hE_diff.continuousOn.mono ( Set.Icc_subset_Icc le_rfl hx.2 ) ) ( hE_diff.mono ( Set.Ioo_subset_Icc_self.trans ( Set.Icc_subset_Icc le_rfl hx.2 ) ) ) ) ( by rintro ⟨ c, ⟨ hc0, hcx ⟩, hcd ⟩ ; rw [ hE_deriv_zero c hc0 ( by linarith ) ] at hcd; rw [ eq_div_iff ] at hcd <;> cases lt_or_gt_of_ne hE_neq <;> nlinarith );
  have hE_zero : ∀ x ∈ Set.Icc 0 Real.pi, E x = 0 := by
    grind +locals;
  have hg_zero : ∀ x ∈ Set.Icc 0 Real.pi, g x = 0 := by
    exact fun x hx => by have := hE_zero x hx; exact eq_zero_of_mul_self_eq_zero ( by nlinarith [ show 0 ≤ deriv g x ^ 2 / lam by positivity ] ) ;;
  exact hg_zero;

/-
If λ ≤ 0, any solution with y(0) = 0, y(π) = 0 is trivial
-/
lemma backward_nonpos {y : ℝ → ℝ} {lam : ℝ} {J : Set ℝ}
    (hJ : IsOpen J) (hJI : Icc 0 π ⊆ J)
    (hlam : lam ≤ 0)
    (hy_diff : ∀ x ∈ J, HasDerivAt y (deriv y x) x)
    (hy'_diff : ∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x)
    (hy0 : y 0 = 0) (hypi : y π = 0) :
    ∀ x ∈ Icc (0 : ℝ) π, y x = 0 := by
  -- Since $y^2$ is convex on $[0, \pi]$ and $y^2(0) = y^2(\pi) = 0$, we can apply the definition of convexity to conclude that $y^2(x) = 0$ for all $x \in [0, \pi]$.
  have h_convex : ConvexOn ℝ (Set.Icc 0 Real.pi) (fun x => y x ^ 2) := by
    apply_rules [ convexOn_of_deriv2_nonneg, convex_Icc ];
    · exact ContinuousOn.pow ( continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt ( hy_diff x ( hJI hx ) ) ) _;
    · exact fun x hx => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.pow ( hy_diff x ( hJI <| interior_subset hx ) |> HasDerivAt.differentiableAt ) _ );
    · norm_num +zetaDelta at *;
      refine' DifferentiableOn.congr _ _;
      exacts [ fun x => 2 * y x * deriv y x, fun x hx => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.mul ( DifferentiableAt.mul ( differentiableAt_const _ ) ( hy_diff x ( hJI <| Set.Ioo_subset_Icc_self hx ) ) ) ( hy'_diff x ( hJI <| Set.Ioo_subset_Icc_self hx ) |> HasDerivAt.differentiableAt ) ), fun x hx => by norm_num [ hy_diff x ( hJI <| Set.Ioo_subset_Icc_self hx ) ] ];
    · -- By definition of $y$, we know that its second derivative is given by $y''(x) = -\lambda y(x)$.
      have h_second_deriv : ∀ x ∈ J, deriv^[2] (fun x => y x ^ 2) x = 2 * (deriv y x) ^ 2 + 2 * y x * (-(lam * y x)) := by
        intro x hx; norm_num [ sq, mul_assoc, mul_comm, mul_left_comm, hy_diff x hx |> HasDerivAt.differentiableAt, hy'_diff x hx |> HasDerivAt.differentiableAt ] ; ring;
        convert HasDerivAt.deriv ( HasDerivAt.congr_of_eventuallyEq _ <| Filter.eventuallyEq_of_mem ( hJ.mem_nhds hx ) fun u hu => show deriv ( fun x => y x ^ 2 ) u = 2 * y u * deriv y u from ?_ ) using 1;
        · convert HasDerivAt.mul ( HasDerivAt.const_mul 2 ( hy_diff x hx ) ) ( hy'_diff x hx ) using 1 ; ring;
        · norm_num [ hy_diff u hu |> HasDerivAt.differentiableAt ];
      exact fun x hx => h_second_deriv x ( hJI <| interior_subset hx ) ▸ by nlinarith [ mul_self_nonneg ( y x ), mul_le_mul_of_nonneg_left hlam ( sq_nonneg ( y x ) ) ] ;
  intro x hx; have := h_convex.2 ( Set.left_mem_Icc.mpr Real.pi_pos.le ) ( Set.right_mem_Icc.mpr Real.pi_pos.le ) ; simp_all +decide [ ConvexOn ] ;
  convert this ( show 0 ≤ 1 - x / Real.pi by exact sub_nonneg.2 <| div_le_one_of_le₀ hx.2 <| by positivity ) ( show 0 ≤ x / Real.pi by exact div_nonneg hx.1 <| by positivity ) ( by ring ) using 1 ; ring_nf ; norm_num [ Real.pi_pos.ne' ]

/-
If λ > 0, any solution with y(0) = 0 equals (y'(0)/√λ) * sin(√λ * x) on [0,π]
-/
lemma solution_is_sin_mul {y : ℝ → ℝ} {lam : ℝ} {J : Set ℝ}
    (hJ : IsOpen J) (hJI : Icc 0 π ⊆ J)
    (hlam : 0 < lam)
    (hy_diff : ∀ x ∈ J, HasDerivAt y (deriv y x) x)
    (hy'_diff : ∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x)
    (hy0 : y 0 = 0) :
    ∀ x ∈ Icc (0 : ℝ) π, y x = (deriv y 0 / √lam) * sin (√lam * x) := by
  -- Define g(x) = y(x) - (deriv y 0 / √lam) * sin(√lam * x).
  set g : ℝ → ℝ := fun x => y x - (deriv y 0 / Real.sqrt lam) * Real.sin (Real.sqrt lam * x);
  -- Show that g satisfies g'' + lam*g = 0 with g(0) = 0, g'(0) = 0.
  have hg_diff : ∀ x ∈ J, HasDerivAt g (deriv g x) x := by
    exact fun x hx => hasDerivAt_deriv_iff.mpr ( by exact DifferentiableAt.sub ( hy_diff x hx |> HasDerivAt.differentiableAt ) ( DifferentiableAt.mul ( differentiableAt_const _ ) ( DifferentiableAt.sin ( differentiableAt_id.const_mul _ ) ) ) )
  have hg'_diff : ∀ x ∈ J, HasDerivAt (deriv g) (-(lam * g x)) x := by
    -- By definition of $g$, we know that its derivative is $g'(x) = y'(x) - (deriv y 0) * cos(√lam * x)$.
    have hg'_def : ∀ x ∈ J, deriv g x = deriv y x - (deriv y 0) * Real.cos (Real.sqrt lam * x) := by
      intro x hx
      have hyd := hy_diff x hx |> HasDerivAt.differentiableAt
      have : deriv g x = deriv y x - deriv y 0 / √lam * (√lam * cos (√lam * x)) := by
        erw [deriv_sub] <;> [skip; exact hyd; exact DifferentiableAt.mul (differentiableAt_const _) (DifferentiableAt.sin (differentiableAt_id.const_mul _))]
        congr 1
        exact (HasDerivAt.const_mul (deriv y 0 / √lam) (hasDerivAt_sin_mul (√lam) x)).deriv
      rw [this]
      have hsqrt_ne : (√lam : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hlam)
      field_simp
    intro x hx; convert HasDerivAt.congr_of_eventuallyEq ( HasDerivAt.sub ( hy'_diff x hx ) ( HasDerivAt.const_mul ( deriv y 0 ) ( HasDerivAt.cos ( HasDerivAt.const_mul ( Real.sqrt lam ) ( hasDerivAt_id x ) ) ) ) ) ( Filter.eventuallyEq_of_mem ( hJ.mem_nhds hx ) hg'_def ) using 1 ; ring;
    grind
  have hg0 : g 0 = 0 := by
    aesop
  have hg'0 : deriv g 0 = 0 := by
    convert HasDerivAt.deriv ( HasDerivAt.sub ( hy_diff 0 ( hJI ( by norm_num; positivity ) ) ) ( HasDerivAt.const_mul ( deriv y 0 / Real.sqrt lam ) ( HasDerivAt.sin ( HasDerivAt.const_mul ( Real.sqrt lam ) ( hasDerivAt_id 0 ) ) ) ) ) using 1 ; norm_num [ hy0, hlam.le, hlam.ne' ];
  exact fun x hx => sub_eq_zero.mp ( ode_uniqueness_pos hJ hJI hlam hg_diff hg'_diff hg0 hg'0 x hx )

/-
If sin(a * π) = 0 and a > 0, then a is a positive natural number
-/
lemma pos_real_sin_pi_eq_zero {a : ℝ} (ha : 0 < a) (h : sin (a * π) = 0) :
    ∃ n : ℕ, 0 < n ∧ a = ↑n := by
  obtain ⟨ n, hn ⟩ := Real.sin_eq_zero_iff.mp h;
  exact ⟨ n.natAbs, Int.natAbs_pos.mpr ( by rintro rfl; norm_num at hn; nlinarith [ Real.pi_pos ] ), by cases n <;> norm_num at * <;> nlinarith [ Real.pi_pos ] ⟩

/-
The backward direction: if there's a non-trivial solution, then λ = n²
-/
lemma backward_direction (lam : ℝ)
    (h : ∃ (y : ℝ → ℝ) (J : Set ℝ),
      IsOpen J ∧ Icc (0 : ℝ) π ⊆ J ∧
      (∀ x ∈ J, HasDerivAt y (deriv y x) x) ∧
      (∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x) ∧
      y 0 = 0 ∧ y π = 0 ∧
      ∃ x ∈ Ioo (0 : ℝ) π, y x ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ lam = (n : ℝ) ^ 2 := by
  obtain ⟨ y, J, hJ, hJI, hy_diff, hy'_diff, hy0, hypi, hx, hx' ⟩ := h;
  by_cases hlam : lam ≤ 0;
  · exact False.elim <| hx'.2 <| backward_nonpos hJ hJI hlam hy_diff hy'_diff hy0 hypi hx <| Set.Ioo_subset_Icc_self hx'.1;
  · -- By solution_is_sin_mul, y(x) = (deriv y 0 / √lam) * sin(√lam * x) on [0,π].
    have h_sol : ∀ x ∈ Set.Icc 0 Real.pi, y x = (deriv y 0 / Real.sqrt lam) * Real.sin (Real.sqrt lam * x) := by
      apply solution_is_sin_mul hJ hJI (by linarith) hy_diff hy'_diff hy0;
    -- Since $y(\pi) = 0$, we have $(deriv y 0 / \sqrt{lam}) * \sin(\sqrt{lam} * \pi) = 0$.
    have h_sin_zero : Real.sin (Real.sqrt lam * Real.pi) = 0 := by
      grind;
    obtain ⟨ n, hn ⟩ := pos_real_sin_pi_eq_zero ( Real.sqrt_pos.mpr ( lt_of_not_ge hlam ) ) h_sin_zero;
    exact ⟨ n, hn.1, by rw [ ← hn.2, Real.sq_sqrt ( le_of_not_ge hlam ) ] ⟩

end Submission.Helpers