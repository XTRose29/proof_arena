import Mathlib
import ChallengeDeps

open LeanEval.KnotTheory
open Real Set

namespace Submission.Helpers

/-! ## Curve definitions -/

noncomputable def mkR3 (x y z : ℝ) : R3 :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm ![x, y, z]

noncomputable def circleXY (t : ℝ) : R3 := mkR3 (cos t) (sin t) 0

noncomputable def circleXY10 (t : ℝ) : R3 := mkR3 (cos t) (sin t) 10

noncomputable def hopfCircle (t : ℝ) : R3 := mkR3 (1 + cos t) 0 (sin t)

/-! ## Knot properties for circleXY -/

lemma circleXY_smooth : ContDiff ℝ (⊤ : ℕ∞) circleXY := by
  apply_rules [ ContDiff.comp, contDiff_pi ];
  fun_prop;
  any_goals apply_rules [ ContDiff.comp, contDiff_id, contDiff_const ];
  exact contDiff_pi.mpr fun i => by fin_cases i <;> [ exact Real.contDiff_cos; exact Real.contDiff_sin; exact contDiff_const ] ;

lemma circleXY_periodic : ∀ t, circleXY (t + 2 * π) = circleXY t := by
  unfold circleXY;
  norm_num [ mkR3 ]

lemma circleXY_injOn : InjOn circleXY (Ico 0 (2 * π)) := by
  intro s hs t ht h_eq;
  unfold circleXY at h_eq;
  unfold mkR3 at h_eq; simp_all +decide [ ← List.ofFn_inj ] ;
  have h_eq : Real.cos (s - t) = 1 := by
    rw [ Real.cos_sub ] ; nlinarith [ Real.sin_sq_add_cos_sq s, Real.sin_sq_add_cos_sq t ];
  rw [ Real.cos_eq_one_iff ] at h_eq ; obtain ⟨ k, hk ⟩ := h_eq ; rcases k with ⟨ _ | k ⟩ <;> norm_num at hk <;> nlinarith [ Real.pi_pos ]

lemma circleXY_immersion : ∀ t, deriv circleXY t ≠ 0 := by
  have h_deriv : ∀ t, deriv circleXY t = mkR3 (-Real.sin t) (Real.cos t) 0 := by
    intro t;
    refine' HasDerivAt.deriv _;
    rw [ hasDerivAt_iff_tendsto ];
    have h_deriv : HasDerivAt (fun x' => Real.cos x') (-Real.sin t) t ∧ HasDerivAt (fun x' => Real.sin x') (Real.cos t) t := by
      exact ⟨ Real.hasDerivAt_cos t, Real.hasDerivAt_sin t ⟩;
    have h_deriv : Filter.Tendsto (fun x' => ‖x' - t‖⁻¹ * ‖(Real.cos x' - Real.cos t) - (x' - t) * (-Real.sin t)‖) (nhds t) (nhds 0) ∧ Filter.Tendsto (fun x' => ‖x' - t‖⁻¹ * ‖(Real.sin x' - Real.sin t) - (x' - t) * (Real.cos t)‖) (nhds t) (nhds 0) := by
      simp_all +decide [ hasDerivAt_iff_tendsto ];
    convert Filter.Tendsto.sqrt ( Filter.Tendsto.add ( h_deriv.1.pow 2 ) ( h_deriv.2.pow 2 ) ) using 2 <;> norm_num [ EuclideanSpace.norm_eq, Fin.sum_univ_three ];
    unfold circleXY mkR3; norm_num [ abs_mul, abs_inv ] ; ring;
    simp +zetaDelta at *;
    rw [ ← mul_add, Real.sqrt_mul ( by positivity ), Real.sqrt_inv, Real.sqrt_sq_eq_abs ] ; ring;
  intro t; specialize h_deriv t; by_contra h; simp_all +decide [ funext_iff, Fin.forall_fin_succ ] ;
  injection h_deriv.symm with h ; have := Real.sin_sq_add_cos_sq t ; aesop

/-! ## Knot properties for circleXY10 -/

lemma circleXY10_smooth : ContDiff ℝ (⊤ : ℕ∞) circleXY10 := by
  have h_circleXY10_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun t => circleXY10 t) := by
    have h_translation : ContDiff ℝ (⊤ : ℕ∞) (fun p : R3 => p + mkR3 0 0 10) := by
      fun_prop
    convert h_translation.comp ( show ContDiff ℝ ( ⊤ : ℕ∞ ) ( fun t => circleXY t ) from circleXY_smooth ) using 1;
    ext t i; fin_cases i <;> norm_num [ circleXY, circleXY10, mkR3 ] ;
  exact h_circleXY10_smooth

lemma circleXY10_periodic : ∀ t, circleXY10 (t + 2 * π) = circleXY10 t := by
  unfold circleXY10;
  aesop

lemma circleXY10_injOn : InjOn circleXY10 (Ico 0 (2 * π)) := by
  intro x hx y hy hxy;
  unfold circleXY10 at hxy;
  unfold mkR3 at hxy;
  simp_all +decide [ funext_iff, Fin.forall_fin_succ ];
  rw [ Real.cos_eq_cos_iff, Real.sin_eq_sin_iff ] at hxy;
  rcases hxy with ⟨ ⟨ k, rfl | rfl ⟩, ⟨ l, hl | hl ⟩ ⟩ <;> rcases k with ⟨ _ | k ⟩ <;> norm_num at * <;> try nlinarith;
  · rcases l with ⟨ _ | l ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
  · norm_cast at hl; omega;

lemma circleXY10_immersion : ∀ t, deriv circleXY10 t ≠ 0 := by
  intro t;
  convert circleXY_immersion t using 1;
  unfold circleXY10 circleXY;
  unfold mkR3;
  rw [ show ( fun t => ( EuclideanSpace.equiv ( Fin 3 ) ℝ ).symm ![cos t, sin t, 10] ) = fun t => ( EuclideanSpace.equiv ( Fin 3 ) ℝ ).symm ![cos t, sin t, 0] + ( EuclideanSpace.equiv ( Fin 3 ) ℝ ).symm ![0, 0, 10] by ext t i; fin_cases i <;> norm_num ] ; erw [ deriv_add_const ]

/-! ## Knot properties for hopfCircle -/

lemma hopfCircle_smooth : ContDiff ℝ (⊤ : ℕ∞) hopfCircle := by
  refine' contDiff_iff_contDiffAt.2 fun x => _;
  refine' ContDiffAt.congr_of_eventuallyEq _ _;
  exact fun t => WithLp.toLp 2 ( fun i : Fin 3 => if i = 0 then 1 + Real.cos t else if i = 1 then 0 else Real.sin t );
  · refine' ContDiffAt.comp x _ _;
    · exact ContDiff.contDiffAt PiLp.contDiff_toLp;
    · exact contDiffAt_pi.mpr fun i => by fin_cases i <;> [ exact ContDiffAt.add contDiffAt_const ( Real.contDiff_cos.contDiffAt ) ; exact contDiffAt_const; exact Real.contDiff_sin.contDiffAt ] ;
  · filter_upwards [ ] with t using by ext i; fin_cases i <;> rfl;

lemma hopfCircle_periodic : ∀ t, hopfCircle (t + 2 * π) = hopfCircle t := by
  unfold hopfCircle;
  norm_num [ mkR3 ]

lemma hopfCircle_injOn : InjOn hopfCircle (Ico 0 (2 * π)) := by
  intro s hs t ht h_eq;
  unfold hopfCircle at h_eq;
  have h_cos_sin : Real.cos s = Real.cos t ∧ Real.sin s = Real.sin t := by
    unfold mkR3 at h_eq; simp_all +decide [ funext_iff, Fin.forall_fin_succ ] ;
  have h_eq : Real.cos (s - t) = 1 := by
    rw [ Real.cos_sub, h_cos_sin.1, h_cos_sin.2 ] ; ring;
    norm_num;
  rw [ Real.cos_eq_one_iff ] at h_eq ; obtain ⟨ k, hk ⟩ := h_eq ; rcases k with ⟨ _ | k ⟩ <;> norm_num at hk <;> nlinarith [ Real.pi_pos, hs.1, hs.2, ht.1, ht.2 ]

lemma hopfCircle_immersion : ∀ t, deriv hopfCircle t ≠ 0 := by
  intro t
  have h_deriv : deriv (fun t => mkR3 (1 + Real.cos t) 0 (Real.sin t)) t = mkR3 (-Real.sin t) 0 (Real.cos t) := by
    convert HasDerivAt.deriv ( _ ) using 1;
    rw [ hasDerivAt_iff_tendsto ];
    have h_deriv : HasDerivAt (fun t => 1 + Real.cos t) (-Real.sin t) t ∧ HasDerivAt (fun t => Real.sin t) (Real.cos t) t := by
      exact ⟨ by simpa using HasDerivAt.const_add 1 ( Real.hasDerivAt_cos t ), Real.hasDerivAt_sin t ⟩;
    have := h_deriv.1.isLittleO.tendsto_div_nhds_zero; have := h_deriv.2.isLittleO.tendsto_div_nhds_zero; simp_all +decide [ EuclideanSpace.norm_eq, Fin.sum_univ_three ];
    simp_all +decide [ div_eq_inv_mul, mkR3 ];
    have := Filter.Tendsto.sqrt ( Filter.Tendsto.add ( ‹Filter.Tendsto ( fun x => ( x - t ) ⁻¹ * ( cos x - cos t + ( x - t ) * sin t ) ) ( nhds t ) ( nhds 0 ) ›.pow 2 ) ( ‹Filter.Tendsto ( fun x => ( x - t ) ⁻¹ * ( sin x - sin t - ( x - t ) * cos t ) ) ( nhds t ) ( nhds 0 ) ›.pow 2 ) ) ; simp_all +decide [ mul_pow, abs_mul, abs_inv ] ;
    convert this using 2 ; norm_num [ ← mul_add, Real.sqrt_mul ( sq_nonneg _ ), Real.sqrt_sq_eq_abs ];
    rw [ Real.sqrt_mul ( by positivity ), Real.sqrt_inv, Real.sqrt_sq_eq_abs ];
  unfold hopfCircle;
  simp_all +decide [ mkR3 ];
  exact fun h₁ h₂ => absurd ( Real.sin_sq_add_cos_sq t ) ( by norm_num [ h₁, h₂ ] )

/-! ## Knot and TwoLink instances -/

noncomputable def knotCircleXY : Knot where
  curve := circleXY
  smooth := circleXY_smooth
  periodic := circleXY_periodic
  injOn := circleXY_injOn
  immersion := circleXY_immersion

noncomputable def knotCircleXY10 : Knot where
  curve := circleXY10
  smooth := circleXY10_smooth
  periodic := circleXY10_periodic
  injOn := circleXY10_injOn
  immersion := circleXY10_immersion

noncomputable def knotHopfCircle : Knot where
  curve := hopfCircle
  smooth := hopfCircle_smooth
  periodic := hopfCircle_periodic
  injOn := hopfCircle_injOn
  immersion := hopfCircle_immersion

lemma unlink_disjoint :
    Disjoint (range circleXY) (range circleXY10) := by
      unfold circleXY circleXY10;
      unfold mkR3;
      norm_num [ Set.disjoint_left ]

lemma hopf_disjoint :
    Disjoint (range circleXY) (range hopfCircle) := by
      norm_num [ Set.disjoint_left, circleXY, hopfCircle ];
      intro a x h; simp_all +decide [ funext_iff, Fin.forall_fin_succ, mkR3 ] ;
      cases le_or_gt 0 ( Real.cos a ) <;> cases le_or_gt 0 ( Real.cos x ) <;> nlinarith [ Real.sin_sq_add_cos_sq a, Real.sin_sq_add_cos_sq x ]

noncomputable def theUnlink : TwoLink where
  K := knotCircleXY
  L := knotCircleXY10
  disjoint := unlink_disjoint

noncomputable def theHopfLink : TwoLink where
  K := knotCircleXY
  L := knotHopfCircle
  disjoint := hopf_disjoint

/-! ## Covering space argument for non-isotopy

We use the covering space lifting theorem from Mathlib to show that the
unlink and Hopf link are not isotopic. The key idea:

1. If they were isotopic via Φ, the diffeomorphism Φ.H 1 would map the flat
   disk bounded by circleXY10 to a "disk" bounded by hopfCircle, disjoint
   from circleXY.
2. Composing with a projection Ψ : ℝ³ \ range(circleXY) → Circle gives
   a continuous map from ℂ to Circle.
3. On the unit circle, this map wraps around once (has degree 1).
4. By the covering space lifting theorem for ℝ → Circle (which Mathlib has),
   we get a continuous lift ℂ → ℝ. The lift on the boundary gives a
   contradiction: the lifted angle at a single point must equal both
   τ.f(0) and τ.f(2π) = τ.f(0) + 2π.
-/

/-- The component extraction function for R3. -/
noncomputable def R3coord (i : Fin 3) (p : R3) : ℝ := (EuclideanSpace.equiv (Fin 3) ℝ) p i

lemma mkR3_coord (x y z : ℝ) (i : Fin 3) :
    R3coord i (mkR3 x y z) = ![x, y, z] i := by
  simp [R3coord, mkR3]

/-
Key topological lemma: a continuous map ℂ → Circle cannot restrict to a
"degree 1" map on the unit circle.

The proof uses the covering space lifting theorem from Mathlib:
- ℂ is simply connected and locally path connected
- Circle.exp : ℝ → Circle is a covering map
- Any continuous map ℂ → Circle lifts to ℂ → ℝ
- The lift on the unit circle produces a contradiction (0 = 2π)
-/
lemma no_degree_one_extension
    (F : C(ℂ, Circle))
    (g : ℝ → ℝ) (g_cont : Continuous g)
    (g_period : ∀ t, g (t + 2 * Real.pi) = g t + 2 * Real.pi)
    (h_agree : ∀ t : ℝ, F (↑(Circle.exp t) : ℂ) = Circle.exp (g t)) :
    False := by
      obtain ⟨θ, hθ⟩ : ∃ θ : C(ℂ, ℝ), θ 1 = g 0 ∧ ∀ z : ℂ, Circle.exp (θ z) = F z := by
        have := @IsCoveringMap.existsUnique_continuousMap_lifts;
        specialize this ( Circle.isCoveringMap_exp ) F 1 ( g 0 );
        exact ExistsUnique.exists ( this ( by simpa using h_agree 0 |> Eq.symm ) ) |> fun ⟨ θ, hθ ⟩ => ⟨ θ, hθ.1, fun z => congr_fun hθ.2 z ⟩;
      -- By the properties of the covering map, we have that θ (Circle.exp t) - g t is an integer multiple of 2π.
      have h_diff : ∀ t : ℝ, ∃ n : ℤ, θ (Circle.exp t) - g t = n * (2 * Real.pi) := by
        intro t
        have h_diff : Circle.exp (θ (Circle.exp t)) = Circle.exp (g t) := by
          rw [ hθ.2, h_agree ];
        rw [ Circle.exp_eq_exp ] at h_diff;
        exact ⟨ h_diff.choose, sub_eq_iff_eq_add'.mpr h_diff.choose_spec ⟩;
      choose n hn using h_diff;
      -- Since $n(t)$ is continuous and takes integer values, it must be constant.
      have h_const : ∃ c : ℤ, ∀ t : ℝ, n t = c := by
        have h_const : Continuous n := by
          have h_const : Continuous (fun t : ℝ => (θ (Circle.exp t) - g t) / (2 * Real.pi)) := by
            fun_prop (disch := norm_num);
          rw [ Metric.continuous_iff ] at *;
          simp_all +decide [ mul_div_cancel_right₀ _ ( by positivity : ( 2 * Real.pi ) ≠ 0 ) ];
        have h_const : IsPreconnected (Set.range n) := by
          exact isPreconnected_range h_const;
        have := h_const.subsingleton;
        exact ⟨ n 0, fun t => this ( Set.mem_range_self t ) ( Set.mem_range_self 0 ) ⟩;
      obtain ⟨ c, hc ⟩ := h_const; have := hn 0; have := hn ( 2 * Real.pi ) ; simp_all +decide [ sub_eq_iff_eq_add ] ;
      exact absurd ( g_period 0 ) ( by norm_num; linarith [ Real.pi_pos ] )

/-- Retraction from ℂ to the closed unit disk. -/
noncomputable def diskRetract (z : ℂ) : ℂ :=
  if ‖z‖ ≤ 1 then z else z / ‖z‖

lemma diskRetract_continuous : Continuous diskRetract := by
  refine' continuous_iff_continuousAt.mpr _;
  intro x
  by_cases hx : ‖x‖ ≤ 1;
  · by_cases hx' : ‖x‖ = 1;
    · refine' ContinuousAt.congr _ _;
      exact fun z => z / max 1 ‖z‖;
      · exact ContinuousAt.div continuousAt_id ( Complex.continuous_ofReal.continuousAt.comp <| ContinuousAt.sup continuousAt_const <| continuousAt_id.norm ) <| by norm_num [ hx' ];
      · filter_upwards [ Metric.ball_mem_nhds x zero_lt_one ] with z hz;
        unfold diskRetract;
        split_ifs <;> simp_all +decide [ div_eq_mul_inv ];
        exact Or.inl <| le_of_lt ‹_›;
    · exact ContinuousAt.congr ( continuousAt_id ) ( Filter.EventuallyEq.symm <| Filter.eventuallyEq_of_mem ( IsOpen.mem_nhds ( isOpen_lt continuous_norm continuous_const ) <| lt_of_le_of_ne hx hx' ) fun y hy => if_pos hy.out.le );
  · refine' ContinuousAt.congr _ _;
    exact fun z => z / ‖z‖;
    · exact ContinuousAt.div continuousAt_id ( Complex.continuous_ofReal.continuousAt.comp <| continuous_norm.continuousAt ) <| by norm_cast; linarith;
    · filter_upwards [ IsOpen.mem_nhds ( isOpen_lt continuous_const continuous_norm ) ( not_le.mp hx ) ] with z hz using by unfold diskRetract; aesop;

lemma diskRetract_norm_le_one (z : ℂ) : ‖diskRetract z‖ ≤ 1 := by
  unfold diskRetract;
  split_ifs <;> simp +decide [ *, norm_div ];
  exact div_self_le_one _

lemma diskRetract_on_circle (z : ℂ) (hz : ‖z‖ = 1) : diskRetract z = z := by
  unfold diskRetract; aesop;

/-- Embed a complex number in ℝ³ at height 10. -/
noncomputable def embedR3 (z : ℂ) : R3 := mkR3 z.re z.im 10

lemma embedR3_continuous : Continuous embedR3 := by
  refine' Continuous.comp _ _;
  · fun_prop;
  · exact continuous_pi_iff.mpr fun i => by fin_cases i <;> continuity;

/-- The projection map from ℝ³ \ range(circleXY) to ℂ \ {0},
    sending (x,y,z) to (√(x²+y²) - 1) + z*I. -/
noncomputable def projToC (p : R3) : ℂ :=
  (Real.sqrt (R3coord 0 p ^ 2 + R3coord 1 p ^ 2) - 1) + R3coord 2 p * Complex.I

lemma projToC_continuous : Continuous projToC := by
  refine' Continuous.add _ _;
  · refine' Continuous.sub _ continuous_const;
    refine' Complex.continuous_ofReal.comp ( Continuous.sqrt _ );
    exact Continuous.add ( Continuous.pow ( by exact continuous_apply _ |> Continuous.comp <| by continuity ) _ ) ( Continuous.pow ( by exact continuous_apply _ |> Continuous.comp <| by continuity ) _ );
  · exact Continuous.mul ( Complex.continuous_ofReal.comp <| by exact continuous_apply _ |> Continuous.comp <| by exact ( by continuity ) ) continuous_const

/-
Points not on circleXY have nonzero projToC.
-/
lemma projToC_ne_zero_of_not_on_circleXY (p : R3) (hp : p ∉ range circleXY) :
    projToC p ≠ 0 := by
      contrapose! hp;
      simp_all +decide [ Complex.ext_iff, projToC ];
      have h_eq : ∃ θ : ℝ, R3coord 0 p = Real.cos θ ∧ R3coord 1 p = Real.sin θ := by
        rw [ sub_eq_zero ] at hp;
        use ( Complex.arg ( R3coord 0 p + R3coord 1 p * Complex.I ) );
        rw [ Complex.cos_arg, Complex.sin_arg ] <;> norm_num [ Complex.ext_iff ];
        · norm_num [ Complex.normSq, Complex.norm_def, ← sq, hp ];
        · aesop;
      obtain ⟨ θ, hθ₀, hθ₁ ⟩ := h_eq; use θ; ext i; fin_cases i <;> simp +decide [ *, circleXY ] ;
      · exact hθ₀.symm;
      · exact hθ₁.symm;
      · exact hp.2.symm

/-
projToC applied to hopfCircle(t) gives (cos t + sin t * I).
-/
lemma projToC_hopfCircle (t : ℝ) :
    projToC (hopfCircle t) = Complex.exp (t * Complex.I) := by
      unfold projToC;
      unfold R3coord; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, mkR3 ] ; ring;
      unfold hopfCircle; norm_num [ mkR3 ] ; ring;
      exact ⟨ by rw [ show 1 + cos t * 2 + cos t ^ 2 = ( 1 + cos t ) ^ 2 by ring, Real.sqrt_sq ] <;> nlinarith [ Real.cos_sq' t ], rfl ⟩

/-
The ambient diffeomorphism Φ.H 1 maps the complement of range(circleXY)
    to itself, when Φ.H 1 preserves range(circleXY).
-/
lemma diffeo_preserves_complement
    (Φ : AmbientIsotopy) (σ : CircleReparam)
    (hK : ∀ t, Φ.H 1 (circleXY t) = circleXY (σ.f t))
    (p : R3) (hp : p ∉ range circleXY) :
    Φ.H 1 p ∉ range circleXY := by
      intro hq;
      -- Since Φ.H 1 is injective, if Φ.H 1 p = circleXY (σ.f t), then p must equal circleXY t.
      obtain ⟨t, ht⟩ : ∃ t, Φ.H 1 p = circleXY (σ.f t) := by
        obtain ⟨ t, ht ⟩ := hq;
        use σ.finv t;
        rw [ ← ht, σ.right_inv ];
      have h_inj : ∀ x y, Φ.H 1 x = Φ.H 1 y → x = y := by
        exact fun x y hxy => by have := Φ.inv_left 1 x; have := Φ.inv_left 1 y; aesop;
      exact hp ⟨ t, h_inj _ _ <| by aesop ⟩

/-
The flat disk {(u, v, 10) | u² + v² ≤ 1} avoids range(circleXY).
-/
lemma embedR3_avoids_circleXY (z : ℂ) : embedR3 z ∉ range circleXY := by
  unfold embedR3;
  unfold circleXY mkR3; norm_num [ EuclideanSpace.norm_eq ] ;

/-- The underlying function of constructF -/
noncomputable def constructF_fun
    (Φ : AmbientIsotopy) (σ : CircleReparam)
    (hK : ∀ t, Φ.H 1 (circleXY t) = circleXY (σ.f t))
    (z : ℂ) : ℂ :=
  let w := projToC (Φ.H 1 (embedR3 (diskRetract z)))
  w / (‖w‖ : ℝ)

lemma constructF_fun_ne_zero
    (Φ : AmbientIsotopy) (σ : CircleReparam)
    (hK : ∀ t, Φ.H 1 (circleXY t) = circleXY (σ.f t))
    (z : ℂ) : projToC (Φ.H 1 (embedR3 (diskRetract z))) ≠ 0 :=
  projToC_ne_zero_of_not_on_circleXY _ (diffeo_preserves_complement Φ σ hK _ (embedR3_avoids_circleXY _))

lemma constructF_fun_mem_circle
    (Φ : AmbientIsotopy) (σ : CircleReparam)
    (hK : ∀ t, Φ.H 1 (circleXY t) = circleXY (σ.f t))
    (z : ℂ) : constructF_fun Φ σ hK z ∈ Metric.sphere (0 : ℂ) 1 := by
  unfold constructF_fun
  rw [Metric.mem_sphere, Complex.dist_eq, sub_zero, norm_div]
  simp [Complex.norm_real]
  exact constructF_fun_ne_zero Φ σ hK z

lemma constructF_continuous_aux
    (Φ : AmbientIsotopy) (σ : CircleReparam)
    (hK : ∀ t, Φ.H 1 (circleXY t) = circleXY (σ.f t)) :
    Continuous (constructF_fun Φ σ hK) := by
  unfold constructF_fun
  apply Continuous.div
  · exact projToC_continuous.comp
      (Φ.smooth.continuous.comp (continuous_const.prodMk (embedR3_continuous.comp diskRetract_continuous)))
  · exact (Complex.continuous_ofReal.comp (projToC_continuous.comp
      (Φ.smooth.continuous.comp (continuous_const.prodMk (embedR3_continuous.comp diskRetract_continuous)))).norm)
  · intro x
    simp
    exact constructF_fun_ne_zero Φ σ hK x

/-- Construct the continuous map F : C(ℂ, Circle) from the isotopy data.
    F = normalize ∘ projToC ∘ Φ.H 1 ∘ embedR3 ∘ diskRetract -/
noncomputable def constructF
    (Φ : AmbientIsotopy) (σ : CircleReparam)
    (hK : ∀ t, Φ.H 1 (circleXY t) = circleXY (σ.f t)) : C(ℂ, Circle) where
  toFun z := ⟨constructF_fun Φ σ hK z, constructF_fun_mem_circle Φ σ hK z⟩
  continuous_toFun := Continuous.subtype_mk (constructF_continuous_aux Φ σ hK) _

/-
The constructed map F satisfies F(Circle.exp t) = Circle.exp(τ.f t)
    for the isotopy data.
-/
lemma constructF_on_circle
    (Φ : AmbientIsotopy) (σ τ : CircleReparam)
    (hK : ∀ t, Φ.H 1 (circleXY t) = circleXY (σ.f t))
    (hL : ∀ t, Φ.H 1 (circleXY10 t) = hopfCircle (τ.f t))
    (t : ℝ) :
    constructF Φ σ hK (↑(Circle.exp t) : ℂ) = Circle.exp (τ.f t) := by
      apply Subtype.ext
      show constructF_fun Φ σ hK ↑(Circle.exp t) = ↑(Circle.exp (τ.f t))
      unfold constructF_fun
      -- By definition of `diskRetract`, we know that `diskRetract (Circle.exp t) = Circle.exp t`.
      have h_diskRetract : diskRetract (Circle.exp t) = Circle.exp t := by
        exact diskRetract_on_circle _ ( by simp +decide [ Complex.norm_exp ] );
      -- By definition of `embedR3`, we know that `embedR3 (Circle.exp t) = circleXY10 t`.
      have h_embedR3 : embedR3 (Circle.exp t) = circleXY10 t := by
        unfold embedR3 circleXY10; simp +decide [ Complex.exp_re, Complex.exp_im ] ;
      rw [h_diskRetract, h_embedR3];
      rw [ hL, projToC_hopfCircle ] ; norm_num [ Complex.norm_exp ]

/-- The main result: the unlink and Hopf link are not isotopic.

Proof: Assume isotopy via Φ with reparametrizations σ, τ. Construct a
continuous map F : C(ℂ, Circle) that restricts to Circle.exp ∘ τ.f on
the unit circle. Since τ.f has period shift 2π (τ.f(t+2π) = τ.f(t)+2π),
the no_degree_one_extension lemma gives a contradiction. -/
theorem unlink_not_isotopic_hopf : ¬ theUnlink.Isotopic theHopfLink := by
  intro ⟨Φ, σ, τ, hK, hL⟩
  exact no_degree_one_extension
    (constructF Φ σ hK) τ.f τ.smooth.continuous τ.periodic
    (constructF_on_circle Φ σ τ hK hL)

end Submission.Helpers