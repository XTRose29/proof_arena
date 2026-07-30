import ChallengeDeps

open Filter Set
open scoped Topology

namespace Submission.Helpers

/-- A convenient strict form of Ekeland's variational principle.  The
parameter `slope` is the coefficient of the metric penalty. -/
theorem exists_strict_approximate_minimizer
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (F : X → ℝ) (hF : Continuous F) (hF_below : BddBelow (range F))
    (x₀ : X) {slope : ℝ} (hslope : 0 < slope) :
    ∃ x : X, F x ≤ F x₀ ∧
      ∀ y : X, y ≠ x → F x < F y + slope * dist x y := by
  let S : X → Set X :=
    fun x => {y | F y + slope * dist x y ≤ F x}
  have hself (x : X) : x ∈ S x := by
    simp [S]
  have htrans {x y z : X} (hy : y ∈ S x) (hz : z ∈ S y) : z ∈ S x := by
    dsimp [S] at hy hz ⊢
    have hdist := dist_triangle x y z
    nlinarith [mul_le_mul_of_nonneg_left hdist hslope.le]
  have hclosed (x : X) : IsClosed (S x) := by
    exact isClosed_le (hF.add (continuous_const.mul (continuous_const.dist continuous_id)))
      continuous_const
  have himage_nonempty (x : X) : (F '' S x).Nonempty :=
    ⟨F x, x, hself x, rfl⟩
  have himage_below (x : X) : BddBelow (F '' S x) :=
    hF_below.mono (image_subset_range F (S x))
  let error : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have herror_pos (n : ℕ) : 0 < error n := by
    positivity
  have happrox (n : ℕ) (x : X) :
      ∃ y ∈ S x, F y < sInf (F '' S x) + error n := by
    have hinf_lt : sInf (F '' S x) < sInf (F '' S x) + error n := by
      linarith [herror_pos n]
    obtain ⟨v, hv_image, hv_lt⟩ :=
      exists_lt_of_csInf_lt (himage_nonempty x) hinf_lt
    obtain ⟨y, hy, rfl⟩ := hv_image
    exact ⟨y, hy, hv_lt⟩
  let pick : ℕ → X → X := fun n x => (happrox n x).choose
  have hpick_mem (n : ℕ) (x : X) : pick n x ∈ S x :=
    (happrox n x).choose_spec.1
  have hpick_lt (n : ℕ) (x : X) :
      F (pick n x) < sInf (F '' S x) + error n :=
    (happrox n x).choose_spec.2
  let u : ℕ → X := fun n => Nat.rec x₀ (fun n x => pick n x) n
  have hu_zero : u 0 = x₀ := rfl
  have hu_succ (n : ℕ) : u (n + 1) = pick n (u n) := by
    rfl
  have hu_step (n : ℕ) : u (n + 1) ∈ S (u n) := by
    rw [hu_succ]
    exact hpick_mem n (u n)
  have hu_nested {n m : ℕ} (hnm : n ≤ m) : u m ∈ S (u n) := by
    induction m with
    | zero =>
        have hn : n = 0 := Nat.eq_zero_of_le_zero hnm
        subst n
        exact hself _
    | succ m ih =>
        rcases Nat.eq_or_lt_of_le hnm with rfl | hnm'
        · exact hself _
        · exact htrans (ih (Nat.le_of_lt_succ hnm')) (hu_step m)
  have hclose (n : ℕ) {y : X} (hy : y ∈ S (u (n + 1))) :
      dist (u (n + 1)) y < error n / slope := by
    have hy_old : y ∈ S (u n) := htrans (hu_step n) hy
    have hinf_le : sInf (F '' S (u n)) ≤ F y :=
      csInf_le (himage_below (u n)) ⟨y, hy_old, rfl⟩
    have hdrop : slope * dist (u (n + 1)) y ≤ F (u (n + 1)) - F y := by
      dsimp [S] at hy
      linarith
    have happ : F (u (n + 1)) < sInf (F '' S (u n)) + error n := by
      rw [hu_succ]
      exact hpick_lt n (u n)
    rw [lt_div_iff₀ hslope]
    linarith
  have hu_cauchy : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (mul_pos hslope (half_pos hε))
    refine ⟨N + 1, fun m hm n hn => ?_⟩
    have hm_mem : u m ∈ S (u (N + 1)) :=
      hu_nested hm
    have hn_mem : u n ∈ S (u (N + 1)) :=
      hu_nested hn
    calc
      dist (u m) (u n) ≤ dist (u m) (u (N + 1)) + dist (u (N + 1)) (u n) :=
        dist_triangle _ _ _
      _ = dist (u (N + 1)) (u m) + dist (u (N + 1)) (u n) := by
        rw [dist_comm (u m)]
      _ < error N / slope + error N / slope :=
        add_lt_add (hclose N hm_mem) (hclose N hn_mem)
      _ < ε := by
        dsimp [error] at hN ⊢
        rw [← add_div, div_lt_iff₀ hslope]
        nlinarith
  obtain ⟨x, hu_lim⟩ := cauchySeq_tendsto_of_complete hu_cauchy
  have hx_mem (n : ℕ) : x ∈ S (u n) := by
    apply (hclosed (u n)).mem_of_tendsto hu_lim
    filter_upwards [eventually_ge_atTop n] with m hm
    exact hu_nested hm
  have hx_value : F x ≤ F x₀ := by
    rw [← hu_zero]
    have hx := hx_mem 0
    dsimp [S] at hx
    have hdist_nonneg : 0 ≤ dist (u 0) x := dist_nonneg
    nlinarith [mul_nonneg hslope.le hdist_nonneg]
  refine ⟨x, hx_value, fun y hy_ne => ?_⟩
  by_contra hlt
  have hy_mem_x : y ∈ S x := by
    dsimp [S]
    exact le_of_not_gt hlt
  have hy_mem (n : ℕ) : y ∈ S (u n) :=
    htrans (hx_mem n) hy_mem_x
  have hdist_lim : Tendsto (fun n => dist (u (n + 1)) y) atTop (𝓝 0) := by
    have hupper : ∀ n, dist (u (n + 1)) y ≤ error n / slope :=
      fun n => (hclose n (hy_mem (n + 1))).le
    have herr_lim : Tendsto (fun n => error n / slope) atTop (𝓝 0) := by
      simpa [error] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const slope
    exact squeeze_zero'
      (Eventually.of_forall fun _ => dist_nonneg)
      (Eventually.of_forall hupper) herr_lim
  have hdist_lim' : Tendsto (fun n => dist (u (n + 1)) y) atTop (𝓝 (dist x y)) :=
    (continuous_id.dist continuous_const).tendsto x |>.comp
      (hu_lim.comp (tendsto_add_atTop_nat 1))
  have hxy_dist : dist x y = 0 :=
    tendsto_nhds_unique hdist_lim' hdist_lim
  exact hy_ne (eq_of_dist_eq_zero hxy_dist).symm

open LeanEval.Analysis.MountainPassProblem
open scoped unitInterval

variable {E : Type*} [NormedAddCommGroup E]
  [hE_space : NormedSpace ℝ E]

/-- Continuous bounded paths with prescribed endpoints, represented as a
closed subspace of the Banach space of bounded continuous functions. -/
abbrev AdmissiblePath (a b : E) :=
  {g : BoundedContinuousFunction I E // g 0 = a ∧ g 1 = b}

omit [NormedSpace ℝ E] in
instance admissiblePathCompleteSpace (a b : E) [CompleteSpace E] :
    CompleteSpace (AdmissiblePath a b) := by
  let s : Set (BoundedContinuousFunction I E) :=
    {g | g 0 = a ∧ g 1 = b}
  have hs : IsClosed s := by
    exact (isClosed_eq (by fun_prop) (by fun_prop)).inter
      (isClosed_eq (by fun_prop) (by fun_prop))
  change CompleteSpace s
  exact IsClosed.completeSpace_coe (hs := hs)

/-- The maximum value of `f` along an admissible path. -/
noncomputable def pathHeight {a b : E} (f : E → ℝ) (g : AdmissiblePath a b) : ℝ :=
  ⨆ t : I, f (g.1 t)

omit [NormedSpace ℝ E] in
theorem continuous_pathHeight {a b : E} {f : E → ℝ} (hf : Continuous f) :
    Continuous (pathHeight (a := a) (b := b) f) := by
  have heq :
      pathHeight (a := a) (b := b) f =
        fun g => sSup ((fun t : I => f (g.1 t)) '' univ) := by
    funext g
    rw [pathHeight, ← sSup_range]
    simp
  rw [heq]
  exact isCompact_univ.continuous_sSup (by fun_prop)

/-- Turn a bundled `Path` into the closed-subspace representation used by
the variational argument. -/
def admissiblePathOfPath {a b : E} (γ : Path a b) : AdmissiblePath a b :=
  ⟨BoundedContinuousFunction.mkOfCompact γ.toContinuousMap, by
    constructor
    · exact γ.source
    · exact γ.target⟩

omit [NormedSpace ℝ E] in
@[simp]
theorem admissiblePathOfPath_apply {a b : E} (γ : Path a b) (t : I) :
    (admissiblePathOfPath γ).1 t = γ t :=
  rfl

/-- Turn an admissible bounded continuous function back into a bundled
`Path`. -/
def pathOfAdmissiblePath {a b : E} (g : AdmissiblePath a b) : Path a b where
  toFun := g.1
  continuous_toFun := g.1.continuous
  source' := g.2.1
  target' := g.2.2

omit [NormedSpace ℝ E] in
@[simp]
theorem pathOfAdmissiblePath_apply {a b : E} (g : AdmissiblePath a b) (t : I) :
    pathOfAdmissiblePath g t = g.1 t :=
  rfl

omit [NormedSpace ℝ E] in
theorem exists_admissiblePath_mem_sphere {a b : E} {r : ℝ}
    (g : AdmissiblePath a b) (hr : 0 < r) (hrb : r < ‖b - a‖) :
    ∃ t : I, g.1 t ∈ Metric.sphere a r := by
  let d : I → ℝ := fun t => dist (g.1 t) a
  have hd : Continuous d := by
    fun_prop
  have hrIcc : r ∈ Icc (d 0) (d 1) := by
    constructor
    · simpa [d, g.2.1] using hr.le
    · simpa [d, g.2.2, dist_eq_norm] using hrb.le
  obtain ⟨t, ht⟩ := intermediate_value_univ (0 : I) (1 : I) hd hrIcc
  refine ⟨t, ?_⟩
  change dist (g.1 t) a = r
  exact ht

omit [NormedSpace ℝ E] in
theorem epsilon_le_pathHeight {a b : E} {ε r : ℝ} {f : E → ℝ}
    (hf : Continuous f) (hmr : MountainRange f a b ε r)
    (g : AdmissiblePath a b) :
    ε ≤ pathHeight f g := by
  rcases hmr with ⟨-, -, hr, hsphere, hrb, -⟩
  obtain ⟨t, ht⟩ := exists_admissiblePath_mem_sphere g hr hrb
  have hbdd : BddAbove (range fun s : I => f (g.1 s)) :=
    (isCompact_range (hf.comp g.1.continuous)).bddAbove
  exact (hsphere (g.1 t) ht).trans (le_ciSup hbdd t)

include hE_space in
theorem epsilon_le_mountainPassLevel {a b : E} {ε r : ℝ} {f : E → ℝ}
    (hf : Continuous f) (hmr : MountainRange f a b ε r) :
    ε ≤ mountainPassLevel f a b := by
  letI : Nonempty (Path a b) := ⟨Path.segment a b⟩
  rw [mountainPassLevel]
  apply le_ciInf
  intro γ
  exact epsilon_le_pathHeight hf hmr (admissiblePathOfPath γ)

/-- If the derivative is larger than `q` at every maximum of a path,
there is a continuous unit-bounded direction field, fixed at the
endpoints, which decreases `f` at all of those maxima. -/
theorem exists_path_descent_direction {a b : E} {f : E → ℝ}
    (hf : Continuous f) (hf' : Continuous (fderiv ℝ f))
    (g : AdmissiblePath a b) {c q : ℝ}
    (ha : f a < c) (hb : f b < c)
    (hc : ∀ t : I, f (g.1 t) ≤ c)
    (hlarge : ∀ t : I, f (g.1 t) = c → q < ‖fderiv ℝ f (g.1 t)‖) :
    ∃ V : I → E, Continuous V ∧ V 0 = 0 ∧ V 1 = 0 ∧
      (∀ t, ‖V t‖ ≤ 1) ∧
      ∀ t, f (g.1 t) = c → fderiv ℝ f (g.1 t) (V t) ≤ -q := by
  classical
  let K : Set I := {t | f (g.1 t) = c}
  let L : I → E →L[ℝ] ℝ := fun t => fderiv ℝ f (g.1 t)
  have hraw (t : K) : ∃ v : E, ‖v‖ < 1 ∧ q < ‖L t.1 v‖ :=
    (L t.1).exists_lt_apply_of_lt_opNorm (hlarge t.1 t.2)
  let raw : K → E := fun t => (hraw t).choose
  have hraw_norm (t : K) : ‖raw t‖ < 1 :=
    (hraw t).choose_spec.1
  have hraw_apply (t : K) : q < ‖L t.1 (raw t)‖ :=
    (hraw t).choose_spec.2
  let direction : K → E :=
    fun t => if L t.1 (raw t) ≤ 0 then raw t else -raw t
  have hdirection_norm (t : K) : ‖direction t‖ < 1 := by
    dsimp [direction]
    split_ifs <;> simpa using hraw_norm t
  have hdirection_apply (t : K) : L t.1 (direction t) < -q := by
    have happ := hraw_apply t
    dsimp [direction]
    split_ifs with hsign
    · rw [Real.norm_eq_abs, abs_of_nonpos hsign] at happ
      linarith
    · have hsign' : 0 < L t.1 (raw t) := lt_of_not_ge hsign
      rw [Real.norm_eq_abs, abs_of_pos hsign'] at happ
      simp only [map_neg]
      linarith
  let endpointMax : ℝ := max (f a) (f b)
  have hendpoint : endpointMax < c := max_lt ha hb
  let U : Option K → Set I
    | none => {t | f (g.1 t) < c}
    | some k =>
        {t | L t (direction k) < -q} ∩ {t | endpointMax < f (g.1 t)}
  have hL_cont : Continuous L := by
    dsimp [L]
    exact hf'.comp g.1.continuous
  have hU_open : ∀ i, IsOpen (U i) := by
    intro i
    cases i with
    | none =>
        exact isOpen_Iio.preimage (hf.comp g.1.continuous)
    | some k =>
        exact (isOpen_Iio.preimage (hL_cont.eval_const (direction k))).inter
          (isOpen_Ioi.preimage (hf.comp g.1.continuous))
  have hU_cover : (univ : Set I) ⊆ ⋃ i, U i := by
    rintro t -
    by_cases ht : f (g.1 t) < c
    · exact mem_iUnion.2 ⟨none, ht⟩
    · have htc : f (g.1 t) = c := le_antisymm (hc t) (le_of_not_gt ht)
      let k : K := ⟨t, htc⟩
      refine mem_iUnion.2 ⟨some k, ?_⟩
      exact ⟨hdirection_apply k, by simpa [htc] using hendpoint⟩
  obtain ⟨ρ, hρ⟩ :=
    PartitionOfUnity.exists_isSubordinate isClosed_univ U hU_open hU_cover
  let v : Option K → E
    | none => 0
    | some k => direction k
  let V : I → E := fun t => ∑ᶠ i, ρ i t • v i
  have hV_cont : Continuous V := by
    exact ρ.continuous_finsum_smul fun _ _ _ => continuousAt_const
  have hv_norm (i : Option K) : ‖v i‖ ≤ 1 := by
    cases i with
    | none => simp [v]
    | some k => exact (hdirection_norm k).le
  have hweight_zero (e : I) (he : e = 0 ∨ e = 1) (k : K) :
      ρ (some k) e = 0 := by
    by_contra hne
    have he_support : e ∈ Function.support (ρ (some k)) := hne
    have he_U : e ∈ U (some k) :=
      hρ (some k) (subset_closure he_support)
    rcases he with rfl | rfl
    · have := he_U.2
      simp [endpointMax, g.2.1] at this
    · have := he_U.2
      simp [endpointMax, g.2.2] at this
  have hV_endpoint (e : I) (he : e = 0 ∨ e = 1) : V e = 0 := by
    dsimp [V]
    apply finsum_eq_zero_of_forall_eq_zero
    intro i
    cases i with
    | none => simp [v]
    | some k => simp [hweight_zero e he k]
  have hV_norm (t : I) : ‖V t‖ ≤ 1 := by
    dsimp [V]
    rw [← ρ.sum_finsupport_smul_eq_finsum (fun i _ => v i)]
    calc
      ‖∑ i ∈ ρ.finsupport t, ρ i t • v i‖
          ≤ ∑ i ∈ ρ.finsupport t, ‖ρ i t • v i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ ρ.finsupport t, ρ i t := by
        apply Finset.sum_le_sum
        intro i hi
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ρ.nonneg i t)]
        nlinarith [ρ.nonneg i t, hv_norm i]
      _ = 1 := ρ.sum_finsupport (mem_univ t)
  have hV_decrease (t : I) (ht : f (g.1 t) = c) :
      L t (V t) ≤ -q := by
    dsimp [V]
    rw [← ρ.sum_finsupport_smul_eq_finsum (fun i _ => v i)]
    simp only [map_sum, map_smul, smul_eq_mul]
    calc
      ∑ i ∈ ρ.finsupport t, ρ i t * L t (v i)
          ≤ ∑ i ∈ ρ.finsupport t, ρ i t * (-q) := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hzero : ρ i t = 0
        · simp [hzero]
        · apply mul_le_mul_of_nonneg_left _ (ρ.nonneg i t)
          have ht_support : t ∈ Function.support (ρ i) := hzero
          have ht_U : t ∈ U i := hρ i (subset_closure ht_support)
          cases i with
          | none => exact False.elim ((ne_of_lt ht_U) ht)
          | some k =>
              simpa [v] using ht_U.1.le
      _ = -q := by
        rw [← Finset.sum_mul]
        simp [ρ.sum_finsupport (mem_univ t)]
  exact ⟨V, hV_cont, hV_endpoint 0 (Or.inl rfl),
    hV_endpoint 1 (Or.inr rfl), hV_norm, hV_decrease⟩

/-- A continuous direction field which is uniformly descending on every
maximizer produces a nearby admissible path whose penalized height is
strictly smaller. -/
theorem exists_path_with_penalized_height_lt {a b : E} {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (g : AdmissiblePath a b) {c q : ℝ}
    (hq : 0 < q) (hc_eq : pathHeight f g = c)
    (V : I → E) (hV_cont : Continuous V) (hV_zero : V 0 = 0)
    (hV_one : V 1 = 0) (hV_norm : ∀ t, ‖V t‖ ≤ 1)
    (hV_decrease :
      ∀ t, f (g.1 t) = c → fderiv ℝ f (g.1 t) (V t) ≤ -q) :
    ∃ g' : AdmissiblePath a b,
      pathHeight f g' + (q / 2) * dist g g' < c := by
  classical
  have hf_cont : Continuous f := hf.continuous
  have hf'_cont : Continuous (fderiv ℝ f) :=
    hf.continuous_fderiv one_ne_zero
  have hf_diff : Differentiable ℝ f :=
    (contDiff_one_iff_fderiv.mp hf).1
  let value : I → ℝ := fun t => f (g.1 t)
  let derivValue : I → ℝ := fun t => fderiv ℝ f (g.1 t) (V t)
  have hvalue_cont : Continuous value := by
    fun_prop
  have hderivValue_cont : Continuous derivValue := by
    fun_prop
  have hvalue_le (t : I) : value t ≤ c := by
    rw [← hc_eq]
    have hbdd : BddAbove (range value) :=
      (isCompact_range hvalue_cont).bddAbove
    exact le_ciSup hbdd t
  let nearMax : Set I := {t | derivValue t < -(7 * q / 8)}
  let controlled : Set I := {t | derivValue t ≤ -(7 * q / 8)}
  have hnear_open : IsOpen nearMax :=
    isOpen_Iio.preimage hderivValue_cont
  have hcontrolled_compact : IsCompact controlled := by
    exact (isClosed_le hderivValue_cont continuous_const).isCompact
  have hmax_near {t : I} (ht : value t = c) : t ∈ nearMax := by
    dsimp [nearMax]
    have hdec := hV_decrease t ht
    linarith
  let jointDerivative : I × ℝ → ℝ :=
    fun p => fderiv ℝ f (g.1 p.1 + p.2 • V p.1) (V p.1)
  have hjointDerivative_cont : Continuous jointDerivative := by
    fun_prop
  have hcontrolled_product :
      controlled ×ˢ ({0} : Set ℝ) ⊆
        jointDerivative ⁻¹' Iio (-(3 * q / 4)) := by
    rintro ⟨t, s⟩ ⟨ht, rfl⟩
    dsimp [controlled, jointDerivative, derivValue] at ht ⊢
    simpa using lt_of_le_of_lt ht (by linarith : -(7 * q / 8) < -(3 * q / 4))
  obtain ⟨uD, vD, huD_open, hvD_open, hcontrolled_uD, hzero_vD, huvD⟩ :=
    generalized_tube_lemma hcontrolled_compact isCompact_singleton
      (isOpen_Iio.preimage hjointDerivative_cont) hcontrolled_product
  have hvD_nhds : vD ∈ 𝓝 (0 : ℝ) :=
    hvD_open.mem_nhds (hzero_vD rfl)
  obtain ⟨δD, hδD_pos, hδD⟩ := Metric.mem_nhds_iff.mp hvD_nhds
  let away : Set I := nearMaxᶜ
  have haway_compact : IsCompact away :=
    hnear_open.isClosed_compl.isCompact
  have hgap :
      ∃ gap : ℝ, 0 < gap ∧ ∀ t ∈ away, value t ≤ c - gap := by
    by_cases hne : away.Nonempty
    · obtain ⟨t, htaway, htmax⟩ :=
        haway_compact.exists_isMaxOn hne hvalue_cont.continuousOn
      have htc : value t < c := by
        exact lt_of_le_of_ne (hvalue_le t) fun heq => htaway (hmax_near heq)
      refine ⟨c - value t, sub_pos.mpr htc, fun s hs => ?_⟩
      simpa using htmax hs
    · refine ⟨1, one_pos, fun t ht => ?_⟩
      exact False.elim (hne ⟨t, ht⟩)
  obtain ⟨gap, hgap_pos, haway_gap⟩ := hgap
  let jointChange : ℝ × I → ℝ :=
    fun p => f (g.1 p.2 + p.1 • V p.2) - f (g.1 p.2)
  have hjointChange_cont : Continuous jointChange := by
    fun_prop
  have hchange_product :
      ({0} : Set ℝ) ×ˢ away ⊆ jointChange ⁻¹' Iio (gap / 2) := by
    rintro ⟨s, t⟩ ⟨rfl, ht⟩
    simp [jointChange, hgap_pos]
  obtain ⟨uC, vC, huC_open, hvC_open, hzero_uC, haway_vC, huvC⟩ :=
    generalized_tube_lemma isCompact_singleton haway_compact
      (isOpen_Iio.preimage hjointChange_cont) hchange_product
  have huC_nhds : uC ∈ 𝓝 (0 : ℝ) :=
    huC_open.mem_nhds (hzero_uC rfl)
  obtain ⟨δC, hδC_pos, hδC⟩ := Metric.mem_nhds_iff.mp huC_nhds
  let δG : ℝ := 2 * gap / (3 * q)
  have hδG_pos : 0 < δG := by
    positivity
  let step : ℝ := min δD (min δC δG) / 2
  have hstep_pos : 0 < step := by
    dsimp [step]
    positivity
  have hstep_D : step < δD := by
    dsimp [step]
    have hmin_pos : 0 < min δD (min δC δG) := by
      positivity
    nlinarith [min_le_left δD (min δC δG)]
  have hstep_C : step < δC := by
    dsimp [step]
    have hmin_pos : 0 < min δD (min δC δG) := by
      positivity
    nlinarith [min_le_right δD (min δC δG),
      min_le_left δC δG]
  have hstep_G : step < δG := by
    dsimp [step]
    have hmin_pos : 0 < min δD (min δC δG) := by
      positivity
    nlinarith [min_le_right δD (min δC δG),
      min_le_right δC δG]
  have hscalar_deriv (t : I) (s : ℝ) :
      HasDerivAt (fun z : ℝ => f (g.1 t + z • V t))
        (jointDerivative (t, s)) s := by
    have hline :
        HasDerivAt (fun z : ℝ => g.1 t + z • V t) (V t) s :=
      by
        simpa using
          ((hasDerivAt_id s).smul_const (V t)).const_add (g.1 t)
    simpa [jointDerivative, Function.comp_def] using
      (hf_diff.differentiableAt.hasFDerivAt.comp_hasDerivAt s hline)
  have hnear_drop (t : I) (ht : t ∈ nearMax) :
      f (g.1 t + step • V t) ≤ c - (3 * q / 4) * step := by
    have ht_controlled : t ∈ controlled := by
      dsimp [controlled, nearMax] at ht ⊢
      exact ht.le
    have ht_uD : t ∈ uD := hcontrolled_uD ht_controlled
    let scalar : ℝ → ℝ := fun s => f (g.1 t + s • V t)
    have hscalar_cont : Continuous scalar := by
      fun_prop
    have hscalar_diff : Differentiable ℝ scalar :=
      fun s => (hscalar_deriv t s).differentiableAt
    obtain ⟨s, hs, hslope⟩ :=
      exists_deriv_eq_slope scalar hstep_pos hscalar_cont.continuousOn
        hscalar_diff.differentiableOn
    have hs_vD : s ∈ vD := by
      apply hδD
      rw [mem_ball_zero_iff, Real.norm_eq_abs]
      have hs_nonneg : 0 ≤ s := hs.1.le
      rw [abs_of_nonneg hs_nonneg]
      exact hs.2.trans hstep_D
    have hderiv_lt : jointDerivative (t, s) < -(3 * q / 4) :=
      huvD ⟨ht_uD, hs_vD⟩
    have hslope_lt :
        (scalar step - scalar 0) / (step - 0) < -(3 * q / 4) := by
      rw [← hslope, (hscalar_deriv t s).deriv]
      exact hderiv_lt
    have hchange :
        scalar step - scalar 0 < -(3 * q / 4) * step := by
      rw [sub_zero] at hslope_lt
      exact (div_lt_iff₀ hstep_pos).mp hslope_lt
    dsimp [scalar] at hchange
    simp only [zero_smul, add_zero] at hchange
    have hbase := hvalue_le t
    dsimp [value] at hbase
    linarith
  have haway_drop (t : I) (ht : t ∈ away) :
      f (g.1 t + step • V t) ≤ c - (3 * q / 4) * step := by
    have hstep_uC : step ∈ uC := by
      apply hδC
      rw [mem_ball_zero_iff, Real.norm_eq_abs, abs_of_pos hstep_pos]
      exact hstep_C
    have ht_vC : t ∈ vC := haway_vC ht
    have hchange : jointChange (step, t) < gap / 2 :=
      huvC ⟨hstep_uC, ht_vC⟩
    have hbase := haway_gap t ht
    dsimp [value] at hbase
    have hsmall : (3 * q / 4) * step < gap / 2 := by
      have hqne : q ≠ 0 := ne_of_gt hq
      dsimp [δG] at hstep_G
      calc
        (3 * q / 4) * step
            < (3 * q / 4) * (2 * gap / (3 * q)) :=
          mul_lt_mul_of_pos_left hstep_G (by positivity)
        _ = gap / 2 := by
          (field_simp [hqne]; norm_num)
    dsimp [jointChange] at hchange
    linarith
  let w : BoundedContinuousFunction I E :=
    BoundedContinuousFunction.mkOfCompact ⟨V, hV_cont⟩
  have hw_norm : ‖w‖ ≤ 1 :=
    (BoundedContinuousFunction.norm_le zero_le_one).mpr hV_norm
  let g' : AdmissiblePath a b :=
    ⟨g.1 + step • w, by
      constructor
      · simp [w, hV_zero, g.2.1]
      · simp [w, hV_one, g.2.2]⟩
  have hg'_apply (t : I) :
      g'.1 t = g.1 t + step • V t := by
    rfl
  have hg'_height :
      pathHeight f g' ≤ c - (3 * q / 4) * step := by
    rw [pathHeight]
    apply ciSup_le
    intro t
    rw [hg'_apply]
    by_cases ht : t ∈ nearMax
    · exact hnear_drop t ht
    · exact haway_drop t ht
  have hdist : dist g g' ≤ step := by
    change dist g.1 (g.1 + step • w) ≤ step
    have hmul : step * ‖w‖ ≤ step := by
      simpa using mul_le_mul_of_nonneg_left hw_norm hstep_pos.le
    simpa [dist_eq_norm, norm_smul, Real.norm_eq_abs,
      abs_of_pos hstep_pos] using hmul
  refine ⟨g', ?_⟩
  calc
    pathHeight f g' + (q / 2) * dist g g'
        ≤ (c - (3 * q / 4) * step) + (q / 2) * step := by
          gcongr
    _ < c := by
      nlinarith

/-- The minimax value admits a Palais--Smale sequence. -/
theorem exists_mountainPass_palaisSmale_sequence
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) [CompleteSpace E]
    {a b : E} {ε r : ℝ} (hmr : MountainRange f a b ε r) :
    ∃ u : ℕ → E,
      Tendsto (fun n => f (u n)) atTop
        (𝓝 (mountainPassLevel f a b)) ∧
      Tendsto (fun n => fderiv ℝ f (u n)) atTop (𝓝 0) ∧
      ∃ M : ℝ, ∀ n, |f (u n)| ≤ M := by
  classical
  let c : ℝ := mountainPassLevel f a b
  have hc_lower : ε ≤ c :=
    epsilon_le_mountainPassLevel hf.continuous hmr
  have hε : 0 < ε := hmr.2.1
  have hc_pos : 0 < c := hε.trans_le hc_lower
  have hfa : f a = 0 := hmr.1
  have hfb : f b ≤ 0 := hmr.2.2.2.2.2
  have hheight_lower (g : AdmissiblePath a b) : ε ≤ pathHeight f g :=
    epsilon_le_pathHeight hf.continuous hmr g
  have hheight_bdd :
      BddBelow (range (pathHeight (a := a) (b := b) f)) := by
    exact ⟨ε, by rintro - ⟨g, rfl⟩; exact hheight_lower g⟩
  let error : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have herror_pos (n : ℕ) : 0 < error n := by
    positivity
  have hnear_path (n : ℕ) :
      ∃ γ : Path a b,
        (⨆ t : I, f (γ t)) < c + error n := by
    letI : Nonempty (Path a b) := ⟨Path.segment a b⟩
    apply exists_lt_of_ciInf_lt
    rw [show (⨅ γ : Path a b, ⨆ t : I, f (γ t)) = c by
      rfl]
    linarith [herror_pos n]
  have hpoint (n : ℕ) :
      ∃ x : E, c ≤ f x ∧ f x < c + error n ∧
        ‖fderiv ℝ f x‖ ≤ error n := by
    obtain ⟨γ₀, hγ₀⟩ := hnear_path n
    let g₀ : AdmissiblePath a b := admissiblePathOfPath γ₀
    have hg₀_height : pathHeight f g₀ < c + error n := by
      simpa only [g₀, pathHeight, admissiblePathOfPath_apply] using hγ₀
    obtain ⟨g, hg_le, hg_variational⟩ :=
      exists_strict_approximate_minimizer
        (pathHeight (a := a) (b := b) f)
        (continuous_pathHeight hf.continuous) hheight_bdd g₀
        (half_pos (herror_pos n))
    have hg_lower : c ≤ pathHeight f g := by
      rw [show c = ⨅ γ : Path a b, ⨆ t : I, f (γ t) by rfl]
      have hpath_bdd :
          BddBelow (range fun γ : Path a b => ⨆ t : I, f (γ t)) :=
        ⟨ε, by
          rintro - ⟨γ, rfl⟩
          simpa only [pathHeight, admissiblePathOfPath_apply] using
            epsilon_le_pathHeight hf.continuous hmr
              (admissiblePathOfPath γ)⟩
      simpa only [pathHeight, pathOfAdmissiblePath_apply] using
        ciInf_le hpath_bdd (pathOfAdmissiblePath g)
    have hg_upper : pathHeight f g < c + error n :=
      hg_le.trans_lt hg₀_height
    have ha_height : f a < pathHeight f g := by
      rw [hfa]
      exact hc_pos.trans_le hg_lower
    have hb_height : f b < pathHeight f g :=
      hfb.trans_lt (hc_pos.trans_le hg_lower)
    have hsmall :
        ∃ t : I, f (g.1 t) = pathHeight f g ∧
          ‖fderiv ℝ f (g.1 t)‖ ≤ error n := by
      by_contra hnone
      push Not at hnone
      obtain ⟨V, hV_cont, hV_zero, hV_one, hV_norm, hV_decrease⟩ :=
        exists_path_descent_direction hf.continuous
          (hf.continuous_fderiv one_ne_zero) g
          ha_height hb_height
          (fun t => by
            have hbdd : BddAbove (range fun s : I => f (g.1 s)) :=
              (isCompact_range (hf.continuous.comp g.1.continuous)).bddAbove
            exact le_ciSup hbdd t)
          hnone
      obtain ⟨g', hg'⟩ :=
        exists_path_with_penalized_height_lt hf g (herror_pos n)
          rfl V hV_cont hV_zero hV_one hV_norm hV_decrease
      have hg'_ne : g' ≠ g := by
        intro heq
        subst g'
        simp at hg'
      have := hg_variational g' hg'_ne
      linarith
    obtain ⟨t, ht_height, ht_deriv⟩ := hsmall
    refine ⟨g.1 t, ?_, ?_, ht_deriv⟩
    · simpa [ht_height] using hg_lower
    · simpa [ht_height] using hg_upper
  let u : ℕ → E := fun n => (hpoint n).choose
  have hu_lower (n : ℕ) : c ≤ f (u n) :=
    (hpoint n).choose_spec.1
  have hu_upper (n : ℕ) : f (u n) < c + error n :=
    (hpoint n).choose_spec.2.1
  have hu_deriv (n : ℕ) : ‖fderiv ℝ f (u n)‖ ≤ error n :=
    (hpoint n).choose_spec.2.2
  have herror_lim : Tendsto error atTop (𝓝 0) := by
    simpa [error] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hu_value_lim : Tendsto (fun n => f (u n)) atTop (𝓝 c) := by
    have hupper_lim :
        Tendsto (fun n : ℕ => c + error n) atTop (𝓝 c) := by
      simpa only [add_zero] using
        ((tendsto_const_nhds :
            Tendsto (fun _ : ℕ => c) atTop (𝓝 c)).add herror_lim)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hupper_lim
      hu_lower (fun n => (hu_upper n).le)
  have hu_deriv_norm_lim :
      Tendsto (fun n => ‖fderiv ℝ f (u n)‖) atTop (𝓝 0) :=
    squeeze_zero'
      (Eventually.of_forall fun _ => norm_nonneg _)
      (Eventually.of_forall hu_deriv) herror_lim
  have hu_deriv_lim :
      Tendsto (fun n => fderiv ℝ f (u n)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hu_deriv_norm_lim
  have hu_bounded : ∃ M : ℝ, ∀ n, |f (u n)| ≤ M := by
    refine ⟨|c| + 1, fun n => abs_le.2 ⟨?_, ?_⟩⟩
    · have hc_abs : -|c| ≤ c := neg_abs_le c
      linarith [hu_lower n]
    · have herr_le : error n ≤ 1 := by
        dsimp [error]
        rw [div_le_one (by positivity)]
        norm_num
      have hc_le_abs : c ≤ |c| := le_abs_self c
      linarith [hu_upper n]
  exact ⟨u, hu_value_lim, hu_deriv_lim, hu_bounded⟩

/-- The compactness condition turns the minimax Palais--Smale sequence
into a critical point at the minimax value. -/
theorem exists_criticalPoint_at_mountainPassLevel
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) (hps : PalaisSmale f)
    [CompleteSpace E]
    {a b : E} {ε r : ℝ} (hmr : MountainRange f a b ε r) :
    ∃ x : E, IsCriticalPoint f x ∧
      f x = mountainPassLevel f a b := by
  obtain ⟨u, hu_value, hu_deriv, hu_bounded⟩ :=
    exists_mountainPass_palaisSmale_sequence f hf hmr
  obtain ⟨x, φ, hφ, hu_subseq⟩ := hps u hu_bounded hu_deriv
  have hφ_top : Tendsto φ atTop atTop :=
    hφ.tendsto_atTop
  have hvalue_subseq :
      Tendsto (fun n => f ((u ∘ φ) n)) atTop
        (𝓝 (mountainPassLevel f a b)) := by
    simpa [Function.comp_def] using hu_value.comp hφ_top
  have hvalue_x :
      Tendsto (fun n => f ((u ∘ φ) n)) atTop (𝓝 (f x)) :=
    hf.continuous.continuousAt.tendsto.comp hu_subseq
  have hx_value : f x = mountainPassLevel f a b :=
    tendsto_nhds_unique hvalue_x hvalue_subseq
  have hderiv_subseq :
      Tendsto (fun n => fderiv ℝ f ((u ∘ φ) n)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using hu_deriv.comp hφ_top
  have hderiv_x :
      Tendsto (fun n => fderiv ℝ f ((u ∘ φ) n)) atTop
        (𝓝 (fderiv ℝ f x)) :=
    (hf.continuous_fderiv one_ne_zero).continuousAt.tendsto.comp hu_subseq
  have hx_deriv : fderiv ℝ f x = 0 :=
    tendsto_nhds_unique hderiv_x hderiv_subseq
  exact ⟨x, hx_deriv, hx_value⟩

end Submission.Helpers
