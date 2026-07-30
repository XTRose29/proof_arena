import Mathlib

-- BEGIN INLINED FILE: Mathlib/Support/choquet_representation_theorem_b02f2de268/Foundation.lean

open MeasureTheory Set
open scoped ENNReal Topology

/- Some elementary lemmas used in the metrizable version of Choquet's theorem.  The
   sets below are the usual compact exhaustion of the non extreme points.  Keeping
   all three variables in the parameter space, rather than choosing witnesses, is
   a useful way of getting closed/compact sets without a selection theorem. -/

namespace ChoquetAux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A convenient positive sequence.  The first few of the `bad` sets below are
allowed to be empty; the union is what matters. -/
noncomputable def eps (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

lemma eps_pos (n : ℕ) : 0 < eps n := by
  dsimp [eps]
  positivity

lemma eps_le_one (n : ℕ) : eps n ≤ 1 := by
  dsimp [eps]
  have h : (1:ℝ) ≤ (n:ℝ) + 1 := by exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  exact (inv_le_one₀ (by positivity : 0 < (n:ℝ)+1)).2 h

lemma exists_eps_le {a : ℝ} (ha : 0 < a) : ∃ n : ℕ, eps n ≤ a := by
  obtain ⟨n : ℕ, hn : a⁻¹ < n⟩ := exists_nat_gt a⁻¹
  refine ⟨n, ?_⟩
  dsimp [eps]
  have hn' : a⁻¹ < (n:ℝ) + 1 := lt_trans hn (by linarith)
  have ha' : 0 < (n:ℝ) + 1 := by positivity
  exact le_of_lt ((inv_lt_comm₀ ha ha').1 hn')

-- keep a variant with a strict bound; it is often handier when a coefficient
-- comes from an open segment.
lemma exists_eps_lt {a : ℝ} (ha : 0 < a) : ∃ n : ℕ, eps n < a := by
  obtain ⟨n : ℕ, hn : a⁻¹ < n⟩ := exists_nat_gt a⁻¹
  refine ⟨n, ?_⟩
  dsimp [eps]
  have hn' : a⁻¹ < (n:ℝ) + 1 := lt_trans hn (by linarith)
  have ha' : 0 < (n:ℝ) + 1 := by positivity
  exact (inv_lt_comm₀ ha ha').1 hn'

/-- Points for which a quantitatively non-trivial open chord witnesses
non-extremality.  The weak bounds on the coefficient and on the distance are
crucial: for a compact `K`, this is a compact set. -/
def bad (K : Set E) (n : ℕ) : Set E :=
  {x | ∃ u ∈ K, ∃ v ∈ K, ∃ t : ℝ,
      eps n ≤ t ∧ t ≤ 1 - eps n ∧ eps n ≤ ‖u - x‖ ∧
        x = AffineMap.lineMap u v t}

lemma bad_mem {K : Set E} {n : ℕ} {x : E} (hx : x ∈ bad K n) :
    ∃ u ∈ K, ∃ v ∈ K, ∃ t : ℝ,
      eps n ≤ t ∧ t ≤ 1 - eps n ∧ eps n ≤ ‖u - x‖ ∧
        x = AffineMap.lineMap u v t := hx

private lemma lineMap_cont :
    Continuous (fun p : (E × E) × ℝ => AffineMap.lineMap p.1.1 p.1.2 p.2) := by
  -- in a vector space the line map is `t • (v-u) + u`
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  fun_prop

/-- The witness sets `bad K n` are compact.  Notice that no measurability or
choice of a chord is involved in this lemma. -/
lemma bad_isCompact {K : Set E} (hK : IsCompact K) (n : ℕ) : IsCompact (bad K n) := by
  let F : (E × E) × ℝ → E := fun p => AffineMap.lineMap p.1.1 p.1.2 p.2
  let T : Set ((E × E) × ℝ) :=
    ((K ×ˢ K) ×ˢ Icc (eps n) (1 - eps n)) ∩
      {p | eps n ≤ ‖p.1.1 - F p‖}
  have hF : Continuous F := lineMap_cont
  have hT : IsCompact T := by
    apply IsCompact.inter_right ((hK.prod hK).prod isCompact_Icc)
    -- the last condition is closed
    have hnorm : Continuous (fun p : (E × E) × ℝ => ‖p.1.1 - F p‖) :=
      ((continuous_fst.comp continuous_fst).sub hF).norm
    exact isClosed_le continuous_const hnorm
  have heq : bad K n = F '' T := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨u, hu, v, hv, t, ht0, ht1, hd, rfl⟩
      refine ⟨⟨⟨u, v⟩, t⟩, ?_, rfl⟩
      refine ⟨?_, ?_⟩
      · exact ⟨⟨hu, hv⟩, ht0, ht1⟩
      · -- the distance is written with `F`
        exact hd
    · rintro ⟨⟨⟨u, v⟩, t⟩, hp, rfl⟩
      rcases hp with ⟨hprod, hd⟩
      rcases hprod with ⟨⟨hu, hv⟩, ht0, ht1⟩
      exact ⟨u, hu, v, hv, t, ht0, ht1, hd, rfl⟩
  rw [heq]
  exact hT.image hF

/-- A `bad` point is not extreme.  Convexity is not used in this direction;
only the open chord in `K` matters. -/
lemma bad_not_extreme {K : Set E} {n : ℕ} {x : E}
    (hx : x ∈ bad K n) : x ∉ K.extremePoints ℝ := by
  rcases hx with ⟨u, hu, v, hv, t, ht0, ht1, hd, hline⟩
  have htpos : 0 < t := lt_of_lt_of_le (eps_pos n) ht0
  have htlt : t < (1:ℝ) := lt_of_le_of_lt ht1 (sub_lt_self (1:ℝ) (eps_pos n))
  have hxseg : x ∈ openSegment ℝ u v := by
    rw [openSegment_eq_image_lineMap]
    refine ⟨t, ⟨htpos, htlt⟩, ?_⟩
    exact hline.symm
  intro hxext
  have hu' : u = x := (mem_extremePoints_iff_left.1 hxext).2 u hu v hv hxseg
  have hpos := eps_pos n
  have hzero : ‖u - x‖ = 0 := by rw [hu']; simp
  linarith

/-- Conversely, a point of `K` which is not extreme lies in one of the compact
bad sets.  This is just the open line segment characterization of extreme
points, plus Archimedean quantitative bounds. -/
lemma mem_iUnion_bad_iff {K : Set E} (hcvx : Convex ℝ K) {x : E} :
    x ∈ K ∧ x ∉ K.extremePoints ℝ ↔ x ∈ ⋃ n : ℕ, bad K n := by
  classical
  constructor
  · rintro ⟨hxK, hx⟩
    have hnot : ¬ (x ∈ K ∧
        ∀ u ∈ K, ∀ v ∈ K, x ∈ openSegment ℝ u v → u = x) := by
      intro h
      exact hx (mem_extremePoints_iff_left.2 h)
    push_neg at hnot
    rcases hnot hxK with ⟨u, hu, v, hv, hxseg, hune⟩
    rw [openSegment_eq_image_lineMap] at hxseg
    rcases hxseg with ⟨t, ⟨ht0, ht1⟩, htline⟩
    have hnorm : 0 < ‖u - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hune)
    have hpos : 0 < min t (min (1-t) ‖u - x‖) := by
      have hrest : 0 < 1 - t := sub_pos.mpr ht1
      exact lt_min ht0 (lt_min hrest hnorm)
    obtain ⟨n : ℕ, hn⟩ := exists_eps_le hpos
    refine mem_iUnion.2 ⟨n, ?_⟩
    refine ⟨u, hu, v, hv, t, ?_, ?_, ?_, htline.symm⟩
    · exact le_trans hn (min_le_left _ _)
    · have h : eps n ≤ (1 - t) := le_trans (le_trans hn (min_le_right _ _))
          (min_le_left _ _)
      linarith
    · exact le_trans (le_trans hn (min_le_right _ _)) (min_le_right _ _)
  · intro hx
    rcases mem_iUnion.1 hx with ⟨n, hn⟩
    have hnot := bad_not_extreme hn
    rcases hn with ⟨u, hu, v, hv, t, ht0, ht1, hd, hline⟩
    have hxK : x ∈ K := by
      rw [hline]
      apply hcvx.lineMap_mem hu hv
      refine ⟨?_, ?_⟩
      · exact le_trans (le_of_lt (eps_pos n)) ht0
      · exact le_trans ht1 (by linarith [eps_pos n])
    exact ⟨hxK, hnot⟩

end ChoquetAux

namespace ChoquetAux
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma iUnion_bad_eq {K : Set E} (hK : Convex ℝ K) :
    (⋃ n : ℕ, bad K n) = K \ K.extremePoints ℝ := by
  ext x
  change x ∈ (⋃ n : ℕ, bad K n) ↔ _
  rw [← mem_iUnion_bad_iff (x:=x) hK]
  simp only [mem_diff]

lemma measurableSet_iUnion_bad [MeasurableSpace E] [BorelSpace E]
    {K : Set E} (hK : IsCompact K) : MeasurableSet (⋃ n : ℕ, bad K n) := by
  exact MeasurableSet.iUnion (fun n => (bad_isCompact hK n).isClosed.measurableSet)

lemma measurableSet_extremePoints [MeasurableSpace E] [BorelSpace E]
    {K : Set E} (hK : IsCompact K) (hc : Convex ℝ K) :
    MeasurableSet (K.extremePoints ℝ) := by
  have hdiff : (⋃ n : ℕ, bad K n) = K \ K.extremePoints ℝ := iUnion_bad_eq hc
  -- solve for the extreme points inside K
  have hsub : K.extremePoints ℝ ⊆ K := extremePoints_subset
  have heq : K.extremePoints ℝ = K \ (⋃ n : ℕ, bad K n) := by
    rw [hdiff]
    ext x
    by_cases hx : x ∈ K <;> by_cases he : x ∈ K.extremePoints ℝ
    · simp [hx, he]
    · simp [hx, he]
    · exact (False.elim (hx (hsub he)))
    · simp [hx, he]
  rw [heq]
  exact hK.isClosed.measurableSet.diff (measurableSet_iUnion_bad hK)

lemma measure_compl_extreme_of
    [MeasurableSpace E] [BorelSpace E]
    {K : Set E} (hK : IsCompact K) (hc : Convex ℝ K)
    (μ : Measure E) (μK : μ Kᶜ = 0)
    (hbad : ∀ n, μ (bad K n) = 0) :
    μ (K.extremePoints ℝ)ᶜ = 0 := by
  have hu : μ (⋃ n : ℕ, bad K n) = 0 :=
    measure_iUnion_null (fun n => hbad n)
  have hdecomp : (K.extremePoints ℝ)ᶜ ⊆ Kᶜ ∪ (⋃ n : ℕ, bad K n) := by
    rw [iUnion_bad_eq hc]
    intro p hp
    by_cases h : p ∈ K
    · exact Or.inr ⟨h, hp⟩
    · exact Or.inl h
  exact measure_mono_null hdecomp (measure_union_null μK hu)

lemma measure_bad_of_compl_extreme
    [MeasurableSpace E] [BorelSpace E]
    {K : Set E} (μ : Measure E) (hμ : μ (K.extremePoints ℝ)ᶜ = 0) :
    ∀ n, μ (bad K n) = 0 := by
  intro n
  apply measure_mono_null ?_ hμ
  intro p hp he
  exact (bad_not_extreme hp) he

end ChoquetAux

namespace ChoquetAux
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The elementary convex tests used in a maximal-measure proof. A square of
the distance is preferable here to the distance itself: for the centre at an
endpoint of a chord the Jensen gap has a uniform positive formula even when
the norm of the Banach space is not strictly convex. -/
def squareDist (c y : E) : ℝ := ‖y - c‖ ^ 2

lemma squareDist_cont (c : E) : Continuous (squareDist c : E → ℝ) := by
  unfold squareDist
  fun_prop

lemma squareDist_gap {u v x : E} {t : ℝ}
    (hx : x = AffineMap.lineMap u v t) :
    (1-t) * squareDist u u + t * squareDist u v - squareDist u x
      = t * (1-t) * ‖v-u‖^2 := by
  have hxu : x - u = t • (v-u) := by
    rw [hx, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    module
  rw [squareDist, squareDist, squareDist, sub_self, norm_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0), mul_zero,
      zero_add, hxu, norm_smul]
  -- after pulling the non-negative scalar out of the norm this is an identity
  have habs : |t| ^ 2 = t ^ 2 := sq_abs t
  rw [mul_pow, Real.norm_eq_abs, habs]
  ring

/-- A witness in `bad K n` gives not merely a strict Jensen gap for one of
these tests: the gap for the test centred at its left endpoint is bounded
below by `eps n ^ 4`.  This quantitative, uniform version is what makes the
finite-cover/maximal-measure argument possible. -/
lemma bad_has_squareDist_gap {K : Set E} {n : ℕ} {x : E} (hx : x ∈ bad K n) :
    ∃ u ∈ K, ∃ v ∈ K, ∃ t : ℝ,
      eps n ≤ t ∧ t ≤ 1 - eps n ∧ x = AffineMap.lineMap u v t ∧
      eps n ^ 4 ≤
        (1-t) * squareDist u u + t * squareDist u v - squareDist u x := by
  rcases hx with ⟨u, hu, v, hv, t, ht0, ht1, hd, hline⟩
  refine ⟨u, hu, v, hv, t, ht0, ht1, hline, ?_⟩
  rw [squareDist_gap hline]
  have htp : 0 < t := lt_of_lt_of_le (eps_pos n) ht0
  have hxu : x - u = t • (v-u) := by
    rw [hline, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    module
  have hd' : eps n ≤ ‖v-u‖ := by
    have hab : ‖u-x‖ = t * ‖v-u‖ := by
      rw [norm_sub_rev, hxu, norm_smul, Real.norm_eq_abs, abs_of_pos htp]
    rw [hab] at hd
    have htle : t ≤ 1 := le_trans ht1 (by linarith [eps_pos n])
    nlinarith [norm_nonneg (v-u)]
  have h1 : eps n ≤ 1-t := by linarith
  have ep : 0 ≤ eps n := (eps_pos n).le
  have nd : 0 ≤ ‖v-u‖ := norm_nonneg _
  calc
    eps n ^ 4 = eps n * eps n * eps n ^ 2 := by ring
    _ ≤ t * (1-t) * ‖v-u‖^2 := by
      have hn : 0 ≤ t * (1-t) := mul_nonneg (le_trans ep ht0) (le_trans ep h1)
      gcongr

end ChoquetAux

-- END INLINED FILE: Mathlib/Support/choquet_representation_theorem_b02f2de268/Foundation.lean

-- BEGIN INLINED FILE: Mathlib/Support/choquet_representation_theorem_b02f2de268/Reduction.lean

open MeasureTheory Set Topology Filter

namespace ChoquetAux

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The inclusion of a compact set has separable range, hence is strongly
measurable for every measure on the set.  We will use this repeatedly when
passing between measures on `K` and on the ambient Banach space; no separability
of the ambient space is needed. -/
lemma aestronglyMeasurable_subtype_val {K : Set X} (hK : IsCompact K)
    (ν : Measure K) : AEStronglyMeasurable (fun p : K => (p:X)) ν := by
  -- the `aemeasurable + separable range` criterion avoids the (false)
  -- second countability instance on the ambient space.
  apply (aestronglyMeasurable_iff_aemeasurable_separable).2
  refine ⟨measurable_subtype_coe.aemeasurable, ?_⟩
  refine ⟨K, hK.isSeparable, ?_⟩
  filter_upwards [] with p
  exact p.property

/-- Mapping a measure on `K` to the ambient space preserves its barycenter and
reduces support on the extreme points to the compact bad sets.  This is a handy
small reduction: all subsequent weak-compactness/maximal-measure arguments can
be carried out on the compact metric type `K`. -/
lemma of_subtype_probability
    {K : Set X} (hK : IsCompact K) (hc : Convex ℝ K) {x : X}
    (ν : ProbabilityMeasure K)
    (hbad : ∀ n, (ν : Measure K) {p | (p:X) ∈ bad K n} = 0)
    (hbar : x = ∫ p : K, (p:X) ∂(ν : Measure K)) :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧
      μ (K.extremePoints ℝ)ᶜ = 0 ∧
      x = ∫ y, y ∂μ := by
  let val : K → X := fun p => (p:X)
  have hval : Measurable val := measurable_subtype_coe
  classical
  let μ : Measure X := Measure.map val (ν : Measure K)
  haveI hp : IsProbabilityMeasure μ :=
    Measure.isProbabilityMeasure_map hval.aemeasurable
  have μK : μ Kᶜ = 0 := by
    dsimp [μ]
    rw [Measure.map_apply hval hK.isClosed.measurableSet.compl]
    have he : val ⁻¹' Kᶜ = (∅ : Set K) := by
      ext p
      simp [val, p.property]
    rw [he]
    simp
  have μbad : ∀ n, μ (bad K n) = 0 := by
    intro n
    dsimp [μ]
    rw [Measure.map_apply hval (bad_isCompact hK n).isClosed.measurableSet]
    exact hbad n
  refine ⟨μ, hp, measure_compl_extreme_of hK hc μ μK μbad, ?_⟩
  -- Unlike in a separable Banach space the continuous identity on `X` need
  -- not globally be strongly measurable.  Its a.e. measurability for this
  -- pushed measure follows from the compact range on `K`.
  have hvs : AEStronglyMeasurable val (ν : Measure K) :=
    aestronglyMeasurable_subtype_val hK _
  have hid : AEStronglyMeasurable (id : X → X) μ := by
    dsimp [μ]
    exact AEStronglyMeasurable.aestronglyMeasurable_id_map hvs
  have himap : (∫ y : X, (id y) ∂μ) =
      ∫ p : K, (id (val p)) ∂(ν : Measure K) := by
    dsimp [μ]
    exact MeasureTheory.integral_map hval.aemeasurable
      (by
        -- `μ` is definitionally this map above
        exact
          (AEStronglyMeasurable.aestronglyMeasurable_id_map hvs))
  calc
    x = ∫ p : K, (id (val p)) ∂(ν : Measure K) := by
      simpa [id, val] using hbar
    _ = ∫ y : X, (id y) ∂μ := himap.symm
    _ = ∫ y : X, y ∂μ := by simp [id]

end ChoquetAux

-- END INLINED FILE: Mathlib/Support/choquet_representation_theorem_b02f2de268/Reduction.lean

-- BEGIN INLINED FILE: Mathlib/Support/choquet_representation_theorem_b02f2de268/Admissible.lean

open MeasureTheory Set Topology Filter
open BoundedContinuousFunction

namespace ChoquetAux

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Scalar moment equations for the barycenter, on the compact type itself.
Keeping equations for *all* continuous linear forms makes this definition
work without separability of the ambient Banach space. -/
def admissible (K : Set X) (x : X) : Set (ProbabilityMeasure K) :=
  {ν | ∀ ℓ : X →L[ℝ] ℝ,
    (∫ p : K, ℓ (p:X) ∂(ν : Measure K)) = ℓ x}

lemma admissible_closed {K : Set X} (hK : IsCompact K) (x : X) :
    IsClosed (admissible K x) := by
  classical
  letI : CompactSpace K := (isCompact_iff_compactSpace).1 hK
  have hsingle (ℓ : X →L[ℝ] ℝ) :
      IsClosed {ν : ProbabilityMeasure K |
        (∫ p : K, ℓ (p:X) ∂(ν : Measure K)) = ℓ x} := by
    let f : C(K, ℝ) := ⟨(fun p : K => ℓ (p:X)),
      ℓ.continuous.comp continuous_subtype_val⟩
    let g : K →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact f
    have hcont : Continuous (fun ν : ProbabilityMeasure K =>
        ∫ p : K, ℓ (p:X) ∂(ν : Measure K)) := by
      have h := ProbabilityMeasure.continuous_integral_boundedContinuousFunction g
      exact h
    exact isClosed_eq hcont continuous_const
  have heq : admissible K x = ⋂ (ℓ : X →L[ℝ] ℝ),
      {ν : ProbabilityMeasure K |
        (∫ p : K, ℓ (p:X) ∂(ν : Measure K)) = ℓ x} := by
    ext ν
    simp [admissible]
  rw [heq]
  exact isClosed_iInter hsingle

lemma admissible_compact {K : Set X} (hK : IsCompact K) (x : X) :
    IsCompact (admissible K x) := by
  classical
  letI : CompactSpace K := (isCompact_iff_compactSpace).1 hK
  exact (admissible_closed hK x).isCompact

lemma admissible_nonempty {K : Set X} (hK : IsCompact K)
    {x : X} (hx : x ∈ K) : (admissible K x).Nonempty := by
  classical
  let q : K := ⟨x, hx⟩
  haveI : MeasurableSingletonClass K := by infer_instance
  let ν : ProbabilityMeasure K :=
    ⟨Measure.dirac q, inferInstance⟩
  refine ⟨ν, ?_⟩
  intro ℓ
  change (∫ p : K, ℓ (p:X) ∂(Measure.dirac q)) = ℓ x
  rw [MeasureTheory.integral_dirac]

/-- If a measure on the compact type satisfies the scalar equations, then its
vector integral is its prescribed barycenter. -/
lemma integral_val_eq_of_admissible
    {K : Set X} (hK : IsCompact K) {x : X} {ν : ProbabilityMeasure K}
    (hν : ν ∈ admissible K x) :
    (∫ p : K, (p:X) ∂(ν : Measure K)) = x := by
  -- The integral exists: the continuous inclusion has compact range.
  have hmeas : AEStronglyMeasurable (fun p : K => (p:X)) (ν : Measure K) :=
    aestronglyMeasurable_subtype_val hK _
  haveI : IsFiniteMeasure (ν : Measure K) := by infer_instance
  have hbound : ∃ C : ℝ, ∀ p : K, ‖(p:X)‖ ≤ C := by
    have hb : IsCompact ((fun z : X => ‖z‖) '' K) :=
      hK.image (by fun_prop)
    rcases hb.bddAbove with ⟨C, hC⟩
    refine ⟨C, fun p => hC ?_⟩
    exact ⟨(p:X), p.property, rfl⟩
  rcases hbound with ⟨C, hC⟩
  have hint : Integrable (fun p : K => (p:X)) (ν : Measure K) :=
    Integrable.of_bound hmeas C (Filter.Eventually.of_forall hC)
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 ?_
  intro ell
  have hmom := hν ell
  -- commuting a bounded linear functional with the Bochner integral

  exact (ell.integral_comp_comm hint).symm.trans hmom

end ChoquetAux

namespace ChoquetAux
open BoundedContinuousFunction
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]

/-- On the compact space of representing probability measures every continuous
scalar test function has a maximizing representing measure.  This is the
cheap compactness part of the usual maximal-measure proof and is occasionally
useful before one builds a Choquet-order maximal measure. -/
lemma exists_maximizer
    {K : Set X} (hK : IsCompact K) {x : X} (hx : x ∈ K) (f : C(K, ℝ)) :
    ∃ ν ∈ admissible K x, ∀ ξ ∈ admissible K x,
       (∫ p : K, f p ∂(ξ : Measure K)) ≤
       (∫ p : K, f p ∂(ν : Measure K)) := by
  classical
  letI : CompactSpace K := (isCompact_iff_compactSpace).1 hK
  let bf : K →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact f
  let F : ProbabilityMeasure K → ℝ := fun μ => ∫ p : K, bf p ∂(μ : Measure K)
  have hF : Continuous F :=
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction bf
  obtain ⟨ν, hν, hmax⟩ := (admissible_compact hK x).exists_isMaxOn
    (admissible_nonempty hK hx) hF.continuousOn
  refine ⟨ν, hν, ?_⟩
  intro ξ hξ
  exact hmax hξ
end ChoquetAux

-- END INLINED FILE: Mathlib/Support/choquet_representation_theorem_b02f2de268/Admissible.lean

-- BEGIN INLINED FILE: Mathlib/Support/choquet_representation_theorem_b02f2de268/Dilation.lean

open MeasureTheory Set Topology Filter
open scoped ENNReal

namespace ChoquetAux
section replace
variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable {ι : Type*}

/-- A completely elementary finite dilation. On a collection of (disjoint)
measurable pieces `A i` it throws the mass onto a chord `[u i,v i]`; off
these pieces the measure is left alone.  We use ENNReal coefficients, so the
construction does not need auxiliary finite-measure instances. -/
noncomputable def finiteReplace (μ : Measure Ω) (s : Finset ι)
    (A : ι → Set Ω) (u v : ι → Ω) (t : ι → ℝ) : Measure Ω :=
  μ.restrict (⋃ i ∈ s, A i)ᶜ +
    ∑ i ∈ s,
      ((ENNReal.ofReal (1 - t i) * μ (A i)) • Measure.dirac (u i) +
       (ENNReal.ofReal (t i) * μ (A i)) • Measure.dirac (v i))

variable [DecidableEq ι]

lemma finiteReplace_apply_univ (μ : Measure Ω) (s : Finset ι)
    (A : ι → Set Ω) (u v : ι → Ω) (t : ι → ℝ) :
    (finiteReplace μ s A u v t) univ =
      μ ((⋃ i ∈ s, A i)ᶜ) +
      ∑ i ∈ s,
        ((ENNReal.ofReal (1-t i) * μ (A i)) +
         (ENNReal.ofReal (t i) * μ (A i))) := by
  classical
  simp [finiteReplace, MeasureTheory.Measure.restrict_apply_univ,
    MeasureTheory.Measure.finset_sum_apply]

lemma finiteReplace_isProbability (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Finset ι) (A : ι → Set Ω) (u v : ι → Ω) (t : ι → ℝ)
    (hdis : (↑s : Set ι).PairwiseDisjoint A)
    (hmeas : ∀ i ∈ s, MeasurableSet (A i))
    (ht0 : ∀ i ∈ s, 0 ≤ t i) (ht1 : ∀ i ∈ s, t i ≤ 1) :
    IsProbabilityMeasure (finiteReplace μ s A u v t) := by
  classical
  apply (isProbabilityMeasure_iff).2
  rw [finiteReplace_apply_univ]
  have hsum : μ (⋃ i ∈ s, A i) = ∑ i ∈ s, μ (A i) :=
    measure_biUnion_finset hdis hmeas
  have hU : MeasurableSet (⋃ i ∈ s, A i) := Set.Finite.measurableSet_biUnion s.finite_toSet hmeas
  have hcomp : μ (⋃ i ∈ s, A i) + μ ((⋃ i ∈ s, A i)ᶜ) = μ univ :=
    measure_add_measure_compl hU
  have hone : μ univ = (1:ENNReal) := measure_univ
  have hterm (i) (hi : i ∈ s) :
      ENNReal.ofReal (1 - t i) * μ (A i) + ENNReal.ofReal (t i) * μ (A i)
        = μ (A i) := by
    rw [← add_mul]
    have h0 := ht0 i hi
    have h1 := ht1 i hi
    have ha : ENNReal.ofReal (1 - t i) + ENNReal.ofReal (t i)
        = ENNReal.ofReal ((1-t i) + t i) := by
      rw [ENNReal.ofReal_add (by linarith) h0]
    rw [ha]
    norm_num
  have hfin' :
      (∑ i ∈ s,
        (ENNReal.ofReal (1 - t i) * μ (A i) +
         ENNReal.ofReal (t i) * μ (A i))) = μ (⋃ i ∈ s, A i) := by
    classical
    calc
      _ = ∑ i ∈ s, μ (A i) := by
        apply Finset.sum_congr rfl
        intro i hi
        -- here the outer sum has been flattened by notation `∑ i ∈ s`
        exact hterm i hi
      _ = _ := hsum.symm
  rw [hfin', hone] at *
  -- exchange the order in the complement formula
  simpa [add_comm] using hcomp

lemma finiteReplace_integral (μ : Measure Ω) [IsFiniteMeasure μ]
    (s : Finset ι) (A : ι → Set Ω) (u v : ι → Ω) (t : ι → ℝ)
    (f : Ω → ℝ) (hf : Integrable f μ)
    (ht0 : ∀ i ∈ s, 0 ≤ t i) (ht1 : ∀ i ∈ s, t i ≤ 1) :
    (∫ z, f z ∂(finiteReplace μ s A u v t)) =
      (∫ z in (⋃ i ∈ s, A i)ᶜ, f z ∂μ) +
      ∑ i ∈ s, μ.real (A i) * ((1-t i) * f (u i) + t i * f (v i)) := by
  classical
  let U : Set Ω := ⋃ i ∈ s, A i
  have hdir (z : Ω) : Integrable f (Measure.dirac z) :=
    MeasureTheory.integrable_dirac (by simp)
  have hc1 (i : ι) : ENNReal.ofReal (1-t i) * μ (A i) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · simp
    · exact measure_ne_top _ _
  have hc2 (i : ι) : ENNReal.ofReal (t i) * μ (A i) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · simp
    · exact measure_ne_top _ _
  let m : ι → Measure Ω := fun i =>
    (ENNReal.ofReal (1-t i) * μ (A i)) • Measure.dirac (u i) +
    (ENNReal.ofReal (t i) * μ (A i)) • Measure.dirac (v i)
  have hm (i : ι) : Integrable f (m i) := by
    exact (integrable_add_measure.mpr ⟨(hdir (u i)).smul_measure (hc1 i),
        (hdir (v i)).smul_measure (hc2 i)⟩)
  have hall : ∀ r : Finset ι, Integrable f (∑ i ∈ r, m i) := by
    intro r
    induction r using Finset.induction_on with
    | empty => simp
    | @insert a r ha ih =>
      simp only [Finset.sum_insert ha]
      exact integrable_add_measure.mpr ⟨hm a, ih⟩
  have hsum : Integrable f (∑ i ∈ s, m i) := hall s
  have hr : Integrable f (μ.restrict Uᶜ) := hf.integrableOn
  -- split the sum of measures
  have hsplit :
      (∫ z, f z ∂(finiteReplace μ s A u v t)) =
      (∫ z, f z ∂(μ.restrict Uᶜ)) + (∫ z, f z ∂(∑ i ∈ s, m i)) := by
    simpa [finiteReplace, U, m] using
      (MeasureTheory.integral_add_measure hr hsum)
  rw [hsplit]
  have hfsum :
      (∫ z, f z ∂(∑ i ∈ s, m i)) = ∑ i ∈ s, (∫ z, f z ∂(m i)) := by
    -- `integral_finset_sum_measure` has the doubled sum notation
    exact MeasureTheory.integral_finset_sum_measure (by
      intro i hi; exact hm i)
  rw [hfsum]
  -- compute one chord integral
  apply congrArg (fun a => (∫ z in Uᶜ, f z ∂μ) + a) ?_
  apply Finset.sum_congr rfl
  intro i hi
  -- and the inner sum binder
  change (∫ z, f z ∂(m i)) = μ.real (A i) * ((1 - t i) * f (u i) + t i * f (v i))
  dsimp [m]
  rw [MeasureTheory.integral_add_measure
      ((hdir (u i)).smul_measure (hc1 i))
      ((hdir (v i)).smul_measure (hc2 i))]
  simp only [MeasureTheory.integral_smul_measure, MeasureTheory.integral_dirac]
  -- scalar multiplication on the real line
  simp only [smul_eq_mul, ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal (by linarith [ht1 i hi]),
      ENNReal.toReal_ofReal (ht0 i hi)]
  simp only [MeasureTheory.Measure.real_def]
  ring

end replace
end ChoquetAux

namespace ChoquetAux

open Metric
/-- A compact Borel subset of a metric space has finite partitions into small
Borel pieces, with a chosen point of the piece. This form (indices `Fin N`)
is convenient for the elementary dilations above. -/
lemma compact_small_partition
    {P : Type*} [MetricSpace P] [MeasurableSpace P] [BorelSpace P]
    (B : Set P) (hB : IsCompact B) {r : ℝ} (hr : 0 < r) :
    ∃ (N : ℕ) (q : Fin N → P) (A : Fin N → Set P),
      (∀ i, q i ∈ B) ∧
      (∀ i, MeasurableSet (A i)) ∧
      (Set.univ.PairwiseDisjoint A) ∧
      (⋃ i, A i) = B ∧
      (∀ i, ∀ z ∈ A i, dist z (q i) < r) := by
  classical
  obtain ⟨cent, hcentB, hcentfin, hcov⟩ := hB.finite_cover_balls hr
  let s : Finset P := hcentfin.toFinset
  have hs (z : P) : z ∈ s ↔ z ∈ cent := hcentfin.mem_toFinset
  let N := s.card
  let e : Fin N ≃ {z // z ∈ s} := (s.equivFin).symm
  let q : Fin N → P := fun i => (e i).val
  have hq (i : Fin N) : q i ∈ B := hcentB ((hs _).1 (e i).property)
  have hcover : ∀ z ∈ B, ∃ i : Fin N, z ∈ Metric.ball (q i) r := by
    intro z hz
    rcases Set.mem_iUnion.1 (hcov hz) with ⟨a, ha⟩
    rcases Set.mem_iUnion.1 ha with ⟨haC, hza⟩
    let a' : {z // z ∈ s} := ⟨a, (hs _).2 haC⟩
    refine ⟨e.symm a', ?_⟩
    simpa [q, a', e] using hza
  let prev (i : Fin N) : Set P := ⋃ j : Fin N, ⋃ (_h : j < i), Metric.ball (q j) r
  let A : Fin N → Set P := fun i =>
    (B ∩ Metric.ball (q i) r) \ prev i
  have hprev (i : Fin N) : MeasurableSet (prev i) := by
    dsimp [prev]
    exact MeasurableSet.iUnion (fun j =>
      MeasurableSet.iUnion (fun hj => measurableSet_ball))
  have hAmeas (i : Fin N) : MeasurableSet (A i) :=
    ((hB.isClosed.measurableSet.inter measurableSet_ball).diff (hprev i))
  have hAdis : Set.univ.PairwiseDisjoint A := by
    intro i _ j _ hij
    apply Set.disjoint_left.2
    intro z hzi hzj
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hh : z ∈ prev j := by
        dsimp [prev]
        exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hlt, hzi.1.2⟩⟩
      exact hzj.2 hh
    · have hh : z ∈ prev i := by
        dsimp [prev]
        exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hgt, hzj.1.2⟩⟩
      exact hzi.2 hh
  have hAunion : (⋃ i, A i) = B := by
    apply Set.Subset.antisymm
    · intro z hz
      rcases Set.mem_iUnion.1 hz with ⟨i, hi⟩
      exact hi.1.1
    · intro z hz
      obtain ⟨j0, hj0⟩ := hcover z hz
      let T : Finset (Fin N) := Finset.univ.filter (fun j => z ∈ Metric.ball (q j) r)
      have hT : T.Nonempty := by
        refine ⟨j0, ?_⟩
        simp [T, Metric.mem_ball.mp hj0]
      let i : Fin N := T.min' hT
      have hiT : i ∈ T := T.min'_mem hT
      have hiball : z ∈ Metric.ball (q i) r := by
        simpa [T] using hiT
      have hiprev : z ∉ prev i := by
        intro hp
        rcases Set.mem_iUnion.1 hp with ⟨j, hj⟩
        rcases Set.mem_iUnion.1 hj with ⟨hji, hjball⟩
        have hjT : j ∈ T := by simp [T, Metric.mem_ball.mp hjball]
        have hle : i ≤ j := T.min'_le j hjT
        exact (not_le_of_gt hji) hle
      exact Set.mem_iUnion.2 ⟨i, ⟨⟨hz, hiball⟩, hiprev⟩⟩
  refine ⟨N, q, A, hq, hAmeas, hAdis, hAunion, ?_⟩
  intro i z hz
  have hb : z ∈ Metric.ball (q i) r := hz.1.2
  simpa [Metric.mem_ball, dist_comm] using hb
end ChoquetAux

namespace ChoquetAux
open MeasureTheory Set
variable {P : Type*} [MeasurableSpace P] [MeasurableSingletonClass P]
variable {ι : Type*} [DecidableEq ι]
/-- Quantitative estimate for a finite replacement. The error is just the
oscillation on the small cells; this is the part of the usual maximal measure
proof which does *not* require a measurable selection of chords. -/
lemma finiteReplace_gain (μ : Measure P) [IsFiniteMeasure μ]
    (s : Finset ι) (A : ι → Set P) (q u v : ι → P) (t : ι → ℝ)
    (f : P → ℝ) (hf : Integrable f μ)
    (hdis : (↑s : Set ι).PairwiseDisjoint A)
    (hA : ∀ i ∈ s, MeasurableSet (A i))
    (ht0 : ∀ i ∈ s, 0 ≤ t i) (ht1 : ∀ i ∈ s, t i ≤ 1)
    (d g : ℝ) (hd : 0 ≤ d)
    (hloc : ∀ i ∈ s, ∀ z ∈ A i, f z ≤ f (q i) + d)
    (hchord : ∀ i ∈ s,
      f (q i) + g ≤ (1-t i) * f (u i) + t i * f (v i)) :
    (∫ z, f z ∂μ) + (g-d) * μ.real (⋃ i ∈ s, A i) ≤
      (∫ z, f z ∂(finiteReplace μ s A u v t)) := by
  classical
  let U : Set P := ⋃ i ∈ s, A i
  have hU : MeasurableSet U := Set.Finite.measurableSet_biUnion s.finite_toSet hA
  have hUi :
      (∫ z, f z ∂μ) = (∫ z in U, f z ∂μ) + (∫ z in Uᶜ, f z ∂μ) :=
    (integral_add_compl hU hf).symm
  have hUsum : (∫ z in U, f z ∂μ) = ∑ i ∈ s, (∫ z in A i, f z ∂μ) := by
    exact MeasureTheory.integral_biUnion_finset s hA hdis
      (by intro i hi; exact hf.integrableOn)
  have hreal : μ.real U = ∑ i ∈ s, μ.real (A i) :=
    measureReal_biUnion_finset hdis hA
  have hcell (i : ι) (hi : i ∈ s) :
      (∫ z in A i, f z ∂μ) ≤ μ.real (A i) * (f (q i) + d) := by
    have hc := setIntegral_mono_on (μ:=μ)
      (hf.integrableOn) (integrableOn_const) (hA i hi) (hloc i hi)
    simpa [MeasureTheory.setIntegral_const, mul_comm] using hc
  rw [finiteReplace_integral μ s A u v t f hf ht0 ht1, hUi, hUsum, hreal]
  change (∑ i ∈ s, ∫ z in A i, f z ∂μ) + (∫ z in Uᶜ, f z ∂μ) +
      (g - d) * (∑ i ∈ s, μ.real (A i)) ≤
    (∫ z in Uᶜ, f z ∂μ) +
      ∑ i ∈ s, μ.real (A i) * ((1 - t i) * f (u i) + t i * f (v i))
  rw [Finset.mul_sum]
  have key (i : ι) (hi : i ∈ s) :
      (∫ z in A i, f z ∂μ) + (g-d) * μ.real (A i)
        ≤ μ.real (A i) * ((1 - t i) * f (u i) + t i * f (v i)) := by
    have hm : 0 ≤ μ.real (A i) := measureReal_nonneg
    calc
      _ ≤ μ.real (A i) * (f (q i) + d) + (g-d)* μ.real (A i) :=
        add_le_add (hcell i hi) (le_rfl)
      _ = μ.real (A i) * (f (q i) + g) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hchord i hi) hm
  have sumkey : (∑ i ∈ s, ((∫ z in A i, f z ∂μ) + (g-d) * μ.real (A i))) ≤
      ∑ i ∈ s, μ.real (A i) * ((1-t i) * f (u i) + t i * f (v i)) := by
    exact Finset.sum_le_sum (fun i hi => key i hi)
  rw [Finset.sum_add_distrib] at sumkey
  linarith
end ChoquetAux

namespace ChoquetAux
open MeasureTheory Set Metric
/-- Applying the compact partition once. No selection theorem is involved:
the only choices of witnesses are at finitely many centres of the partition. -/
lemma exists_finite_dilation
    {P : Type*} [MetricSpace P] [MeasurableSpace P] [BorelSpace P]
    (B : Set P) (hB : IsCompact B) (μ : ProbabilityMeasure P)
    (f : P → ℝ) (hf : Integrable f (μ : Measure P))
    {r : ℝ} (hr : 0 < r) (d g : ℝ) (hd : 0 ≤ d)
    (hosc : ∀ x y : P, dist x y < r → f x ≤ f y + d)
    (hwit : ∀ z ∈ B, ∃ u v : P, ∃ t : ℝ,
       0 ≤ t ∧ t ≤ 1 ∧ f z + g ≤ (1-t)*f u + t*f v) :
    ∃ ξ : ProbabilityMeasure P,
      (∫ z, f z ∂(μ : Measure P)) + (g-d) * (μ : Measure P).real B
       ≤ (∫ z, f z ∂(ξ : Measure P)) := by
  classical
  obtain ⟨N, q, A, hq, hAm, hAd, hAU, hdist⟩ := compact_small_partition B hB hr
  choose u v t ht0 ht1 hgain using fun i : Fin N => hwit (q i) (hq i)
  let m : Measure P := finiteReplace (μ : Measure P) Finset.univ A u v t
  have hprob : IsProbabilityMeasure m := by
    apply finiteReplace_isProbability (μ : Measure P) Finset.univ A u v t
    · simpa using hAd
    · intro i hi; exact hAm i
    · intro i hi; exact ht0 i
    · intro i hi; exact ht1 i
  let ξ : ProbabilityMeasure P := ⟨m, hprob⟩
  refine ⟨ξ, ?_⟩
  have hest := finiteReplace_gain (μ : Measure P) Finset.univ A q u v t f hf
    (by simpa using hAd) (by intro i hi; exact hAm i)
    (by intro i hi; exact ht0 i) (by intro i hi; exact ht1 i)
    d g hd
    (by intro i hi z hz; exact hosc z (q i) (hdist i z hz))
    (by intro i hi; exact hgain i)
  simpa [ξ, m, hAU] using hest
end ChoquetAux

-- END INLINED FILE: Mathlib/Support/choquet_representation_theorem_b02f2de268/Dilation.lean

-- BEGIN INLINED FILE: Mathlib/Support/choquet_representation_theorem_b02f2de268/Maximal.lean

open MeasureTheory Set Topology Filter
open scoped ENNReal
open BoundedContinuousFunction

namespace ChoquetAux

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A finite partition dilation, made with actual affine chords, has a quantitative
moment error in addition to the gain for the test function.  This is the small
extra estimate needed to take limits: the individual choices of the two ends of
a chord are only at the finitely many centres of a partition. -/
lemma exists_finite_dilation_moments
    {K : Set X} (hK : IsCompact K)
    (B : Set K) (hB : IsCompact B) (μ : ProbabilityMeasure K)
    (f : C(K, ℝ))
    {r : ℝ} (hr : 0 < r) (d g : ℝ) (hd : 0 ≤ d)
    (hosc : ∀ z w : K, dist z w < r → f z ≤ f w + d)
    (hwit : ∀ z ∈ B, ∃ u v : K, ∃ t : ℝ,
       0 ≤ t ∧ t ≤ 1 ∧
       (z : X) = AffineMap.lineMap (u:X) (v:X) t ∧
       f z + g ≤ (1-t)*f u + t*f v) :
    ∃ ξ : ProbabilityMeasure K,
      (∫ z : K, f z ∂(μ : Measure K)) +
          (g-d) * (μ : Measure K).real B ≤
            (∫ z : K, f z ∂(ξ : Measure K)) ∧
      ∀ ℓ : X →L[ℝ] ℝ,
        |(∫ z : K, ℓ (z:X) ∂(ξ : Measure K)) -
          (∫ z : K, ℓ (z:X) ∂(μ : Measure K))| ≤ ‖ℓ‖ * r := by
  classical
  letI : CompactSpace K := (isCompact_iff_compactSpace).1 hK
  obtain ⟨N, q, A, hq, hAm, hAd, hAU, hdist⟩ := compact_small_partition B hB hr
  choose u v t ht0 ht1 hline hgain using
    (fun i : Fin N => hwit (q i) (hq i))
  let m : Measure K := finiteReplace (μ : Measure K) Finset.univ A u v t
  have hprob : IsProbabilityMeasure m := by
    apply finiteReplace_isProbability (μ : Measure K) Finset.univ A u v t
    · simpa using hAd
    · intro i hi; exact hAm i
    · intro i hi; exact ht0 i
    · intro i hi; exact ht1 i
  let ξ : ProbabilityMeasure K := ⟨m, hprob⟩
  refine ⟨ξ, ?_, ?_⟩
  · have hf' : Integrable (fun z : K => f z) (μ : Measure K) := by
      let bf : K →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact f
      change Integrable ((BoundedContinuousFunction.mkOfCompact f : K →ᵇ ℝ) : K → ℝ) (μ : Measure K)
      exact BoundedContinuousFunction.integrable (μ : Measure K) _
    have hest := finiteReplace_gain (μ : Measure K) Finset.univ A q u v t
      (fun z : K => f z) hf'
      (by simpa using hAd) (by intro i hi; exact hAm i)
      (by intro i hi; exact ht0 i) (by intro i hi; exact ht1 i)
      d g hd
      (by intro i hi z hz; exact hosc z (q i) (hdist i z hz))
      (by intro i hi; exact hgain i)
    simpa [ξ, m, hAU] using hest
  · intro ℓ
    let h : K → ℝ := fun z => ℓ (z:X)
    have hhint : Integrable h (μ : Measure K) := by
      let ch : C(K,ℝ) :=
        ⟨(fun z : K => ℓ (z:X)), ℓ.continuous.comp continuous_subtype_val⟩
      let bh : K →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ch
      change Integrable ((BoundedContinuousFunction.mkOfCompact ch : K →ᵇ ℝ) : K → ℝ) (μ : Measure K)
      exact BoundedContinuousFunction.integrable (μ : Measure K) _
    let D : ℝ := ‖ℓ‖ * r
    have hD : 0 ≤ D := mul_nonneg (norm_nonneg _) (le_of_lt hr)
    have hclose (i : Fin N) (z : K) (hz : z ∈ A i) :
        |h z - h (q i)| ≤ D := by
      have hzdist : ‖(z:X) - (q i:X)‖ < r := by
        simpa [Subtype.dist_eq, dist_eq_norm] using (hdist i z hz)
      have hop := ℓ.le_opNorm ((z:X) - (q i:X))
      have hz' : |h z - h (q i)| = ‖ℓ ((z:X) - (q i:X))‖ := by
        dsimp [h]
        rw [map_sub]
      rw [hz']
      exact hop.trans (mul_le_mul_of_nonneg_left hzdist.le (norm_nonneg _))
    have hmeasU : MeasurableSet (⋃ i ∈ (Finset.univ : Finset (Fin N)), A i) :=
      Set.Finite.measurableSet_biUnion (Finset.univ : Finset (Fin N)).finite_toSet
        (by intro i hi; exact hAm i)
    let U : Set K := ⋃ i ∈ (Finset.univ : Finset (Fin N)), A i
    have hU : U = B := by simpa [U] using hAU
    have hintsplit :
        (∫ z : K, h z ∂(μ : Measure K)) =
          (∫ z in Uᶜ, h z ∂(μ : Measure K)) +
          ∑ i ∈ (Finset.univ : Finset (Fin N)), (∫ z in A i, h z ∂(μ : Measure K)) := by
      have hme : MeasurableSet U := by simpa [U] using hmeasU
      have hc := (integral_add_compl hme hhint).symm
      have hs : (∫ z in U, h z ∂(μ : Measure K)) =
          ∑ i ∈ (Finset.univ : Finset (Fin N)), ∫ z in A i, h z ∂(μ : Measure K) :=
        MeasureTheory.integral_biUnion_finset _
          (by intro i hi; exact hAm i) (by
            change (Set.univ : Set (Fin N)).Pairwise (Function.onFun Disjoint A) at hAd
            simpa only [Finset.coe_univ] using hAd)
          (by intro i hi; exact hhint.integrableOn)
      -- rearrange the complement first
      rw [hs] at hc
      linarith
    have hcent (i : Fin N) :
        (1-t i) * h (u i) + t i * h (v i) = h (q i) := by
      -- linearity of the moment along the chosen chord
      have hqline := hline i
      -- lineMap is `t • (v-u) + u`
      -- apply the continuous linear functional
      change (1-t i) * ℓ (u i : X) + t i * ℓ (v i : X) = ℓ (q i : X)
      rw [hqline, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
      -- all the operations commute with ℓ
      simp only [map_add, map_sub, ContinuousLinearMap.map_smul]
      -- scalar multiplication in ℝ
      simp only [smul_eq_mul]
      ring
    have hxisplit :
        (∫ z : K, h z ∂(ξ : Measure K)) =
          (∫ z in Uᶜ, h z ∂(μ : Measure K)) +
            ∑ i ∈ (Finset.univ : Finset (Fin N)),
              (μ : Measure K).real (A i) * h (q i) := by
      have hi := finiteReplace_integral (μ : Measure K)
          (Finset.univ : Finset (Fin N)) A u v t h hhint
          (by intro i hi; exact ht0 i) (by intro i hi; exact ht1 i)
      -- replace the chord values by the centre
      change (∫ z : K, h z ∂(ξ : Measure K)) = _
      change (∫ z : K, h z ∂m) = _
      rw [hi]
      change (∫ z in (⋃ i ∈ (Finset.univ : Finset (Fin N)), A i)ᶜ,
          h z ∂(μ : Measure K)) + _ = _
      dsimp [U]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi'
      rw [hcent i]
    have hreal : (μ : Measure K).real B =
        ∑ i ∈ (Finset.univ : Finset (Fin N)), (μ : Measure K).real (A i) := by
      have hh := measureReal_biUnion_finset (μ := (μ : Measure K))
        (s := (Finset.univ : Finset (Fin N))) (f := A)
        (by simpa using hAd) (by intro i hi; exact hAm i)
      simpa [hAU] using hh
    have hBmass : (μ : Measure K).real B ≤ 1 := by
      have hm := measureReal_mono (μ := (μ : Measure K)) (s₁ := B) (s₂ := Set.univ)
        (Set.subset_univ _)
      simpa using hm
    have hcell_upper (i : Fin N) :
        (∫ z in A i, h z ∂(μ : Measure K)) ≤
          (μ : Measure K).real (A i) * h (q i) +
            D * (μ : Measure K).real (A i) := by
      have hp : ∀ z ∈ A i, h z ≤ h (q i) + D := by
        intro z hz
        have hc := (abs_le.mp (hclose i z hz)).2
        -- `hc : h z - h(q) ≤ D`
        linarith
      have hmono := setIntegral_mono_on (μ := (μ : Measure K))
        hhint.integrableOn (integrableOn_const) (hAm i) hp
      -- integral of a constant
      calc
        _ ≤ (μ : Measure K).real (A i) * (h (q i) + D) :=
          (by simpa [MeasureTheory.setIntegral_const, mul_comm]
            using hmono)
        _ = _ := by ring
    have hcell_lower (i : Fin N) :
        (μ : Measure K).real (A i) * h (q i) ≤
          (∫ z in A i, h z ∂(μ : Measure K)) +
            D * (μ : Measure K).real (A i) := by
      have hp : ∀ z ∈ A i, h (q i) - D ≤ h z := by
        intro z hz
        have hc := (abs_sub_le_iff.mp (hclose i z hz)).2
        -- `h(q)-h(z) ≤ D`
        linarith
      have hmono := setIntegral_mono_on (μ := (μ : Measure K))
        (integrableOn_const) hhint.integrableOn (hAm i) hp
      -- rearrange
      calc
        (μ : Measure K).real (A i) * h (q i)
            = (μ : Measure K).real (A i) * (h (q i) - D) +
                D * (μ : Measure K).real (A i) := by ring
        _ ≤ (∫ z in A i, h z ∂(μ : Measure K)) +
                D * (μ : Measure K).real (A i) :=
          add_le_add (by simpa [MeasureTheory.setIntegral_const,
            mul_comm] using hmono) (le_rfl)
    have hup : (∫ z : K, h z ∂(ξ : Measure K)) -
            (∫ z : K, h z ∂(μ : Measure K)) ≤ D := by
      rw [hxisplit, hintsplit]
      have s := Finset.sum_le_sum
          (s := (Finset.univ : Finset (Fin N)))
          (fun i hi => hcell_lower i)
      -- centres minus cells are bounded by total mass
      have hrw : D * (∑ i ∈ (Finset.univ : Finset (Fin N)),
              (μ : Measure K).real (A i)) ≤ D := by
        have := hBmass
        rw [hreal] at this
        nlinarith
      rw [Finset.mul_sum] at hrw
      rw [Finset.sum_add_distrib] at s
      -- a bit of elementary book-keeping
      linarith
    have hlo : -D ≤ (∫ z : K, h z ∂(ξ : Measure K)) -
            (∫ z : K, h z ∂(μ : Measure K)) := by
      rw [hxisplit, hintsplit]
      have s := Finset.sum_le_sum
          (s := (Finset.univ : Finset (Fin N)))
          (fun i hi => hcell_upper i)
      have hrw : D * (∑ i ∈ (Finset.univ : Finset (Fin N)),
              (μ : Measure K).real (A i)) ≤ D := by
        have := hBmass
        rw [hreal] at this
        nlinarith
      rw [Finset.mul_sum] at hrw
      rw [Finset.sum_add_distrib] at s
      linarith
    exact (abs_le.2 ⟨hlo, hup⟩)

/-- The compact-limit step of the maximal-measure argument.  A fixed positive
Jensen gap on a compact set is incompatible with maximality among representing
measures.  The auxiliary finite dilations need not represent the point: their
linear moments are within `‖ℓ‖ r`, and hence their compact limit does. -/
lemma maximizer_zero_of_uniform_gap
    {K : Set X} (hK : IsCompact K) {x : X}
    (B : Set K) (hB : IsCompact B)
    (f : C(K,ℝ)) {g : ℝ} (hg : 0 < g)
    (μ : ProbabilityMeasure K) (hμ : μ ∈ admissible K x)
    (hmax : ∀ ξ ∈ admissible K x,
        (∫ z : K, f z ∂(ξ : Measure K)) ≤
          (∫ z : K, f z ∂(μ : Measure K)))
    (hwit : ∀ z ∈ B, ∃ u v : K, ∃ t : ℝ,
       0 ≤ t ∧ t ≤ 1 ∧
       (z : X) = AffineMap.lineMap (u:X) (v:X) t ∧
       f z + g ≤ (1-t)*f u + t*f v) :
    (μ : Measure K) B = 0 := by
  classical
  letI : CompactSpace K := (isCompact_iff_compactSpace).1 hK
  -- one uniform oscillation radius for the maximizing test
  have huc : UniformContinuous (fun z : K => f z) :=
    CompactSpace.uniformContinuous_of_continuous f.continuous
  obtain ⟨a, ha, ha'⟩ := (Metric.uniformContinuous_iff.1 huc) (g/2) (by linarith)
  -- shrink the mesh to zero without leaving this radius
  let r : ℕ → ℝ := fun n => a * (1 / ((n:ℝ) + 1))
  have hrpos (n : ℕ) : 0 < r n := by
    dsimp [r]
    positivity
  have hrlim : Tendsto r atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => (1:ℝ) / ((n:ℝ)+1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [r] using h0.const_mul a
  have hrle (n : ℕ) : r n ≤ a := by
    dsimp [r]
    have : (1:ℝ) / ((n:ℝ)+1) ≤ 1 := by
      have hp : (1:ℝ) ≤ (n:ℝ)+1 := by exact le_add_of_nonneg_left (Nat.cast_nonneg _)
      exact (div_le_one (by positivity)).2 hp
    nlinarith
  have hosc (n : ℕ) : ∀ z w : K, dist z w < r n → f z ≤ f w + g/2 := by
    intro z w hz
    have hab := ha' ((lt_of_lt_of_le hz (hrle n)))
    rw [Real.dist_eq] at hab
    linarith [(abs_le.mp (le_of_lt hab)).2]
  have happ (n : ℕ) : ∃ ξ : ProbabilityMeasure K,
      (∫ z : K, f z ∂(μ : Measure K)) +
          (g/2) * (μ : Measure K).real B ≤
             (∫ z : K, f z ∂(ξ : Measure K)) ∧
      ∀ ℓ : X →L[ℝ] ℝ,
        |(∫ z : K, ℓ (z:X) ∂(ξ : Measure K)) -
          (∫ z : K, ℓ (z:X) ∂(μ : Measure K))| ≤ ‖ℓ‖ * r n := by
    have h := exists_finite_dilation_moments (X:=X) hK B hB μ f
        (hrpos n) (g/2) g (by linarith) (hosc n) hwit
    rcases h with ⟨ξ, h1, h2⟩
    refine ⟨ξ, ?_, h2⟩
    convert h1 using 1 <;> ring
  choose ξ hgain hmom using happ
  obtain ⟨ν, hνuniv, φ, hφ, hφlim⟩ :=
    (isSeqCompact_univ : IsSeqCompact (Set.univ : Set (ProbabilityMeasure K)))
      (x := ξ) (by intro n; exact Set.mem_univ _)
  have hFcont : Continuous (fun ρ : ProbabilityMeasure K =>
      ∫ z : K, f z ∂(ρ : Measure K)) := by
    let bf : K →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact f
    change Continuous (fun ρ : ProbabilityMeasure K =>
      ∫ z : K, (BoundedContinuousFunction.mkOfCompact f) z ∂(ρ : Measure K))
    exact ProbabilityMeasure.continuous_integral_boundedContinuousFunction _
  have hνgain : (∫ z : K, f z ∂(μ : Measure K)) +
          (g/2) * (μ : Measure K).real B ≤
             (∫ z : K, f z ∂(ν : Measure K)) := by
    have ht := hFcont.continuousAt.tendsto.comp hφlim
    exact ge_of_tendsto ht (Filter.Eventually.of_forall (fun n => hgain (φ n)))
  have hνadm : ν ∈ admissible K x := by
    intro ell
    let ch : C(K,ℝ) :=
      ⟨(fun z : K => ell (z:X)), ell.continuous.comp continuous_subtype_val⟩
    let bh : K →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ch
    have hc : Continuous (fun ρ : ProbabilityMeasure K =>
        ∫ z : K, ell (z:X) ∂(ρ : Measure K)) := by
      simpa [bh, ch] using
        (ProbabilityMeasure.continuous_integral_boundedContinuousFunction bh)
    let M : ProbabilityMeasure K → ℝ := fun ρ =>
        ∫ z : K, ell (z:X) ∂(ρ : Measure K)
    have ht1 : Tendsto (fun n => M (ξ (φ n)) - M μ) atTop (𝓝 (M ν - M μ)) := by
      have ht := hc.continuousAt.tendsto.comp hφlim
      exact ht.sub tendsto_const_nhds
    have hb (n : ℕ) : ‖M (ξ (φ n)) - M μ‖ ≤ ‖ell‖ * r (φ n) := by
      simpa [M, Real.norm_eq_abs] using hmom (φ n) ell
    have ht0 : Tendsto (fun n => M (ξ (φ n)) - M μ) atTop (𝓝 0) := by
      apply squeeze_zero_norm hb
      simpa [Function.comp_def] using (hrlim.comp hφ.tendsto_atTop).const_mul ‖ell‖
    have heq : M ν - M μ = 0 := tendsto_nhds_unique ht1 ht0
    have hM : M μ = ell x := hμ ell
    change M ν = ell x
    linarith
  have hcomp := hmax ν hνadm
  have hmass : (μ : Measure K).real B = 0 := by
    have : (g/2) * (μ : Measure K).real B ≤ 0 := by linarith
    have hn : 0 ≤ (μ : Measure K).real B := measureReal_nonneg
    nlinarith
  -- convert `toReal = 0` back to measure-zero
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 hmass

end ChoquetAux

-- END INLINED FILE: Mathlib/Support/choquet_representation_theorem_b02f2de268/Maximal.lean

-- BEGIN INLINED FILE: Mathlib/Support/choquet_representation_theorem_b02f2de268/StrictGeom.lean
open Set Topology Filter MeasureTheory
namespace ChoquetAux
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Squared distance to any fixed centre is convex, even though the norm on
`X` is not assumed strictly convex. -/
lemma squareDist_line_nonneg (c u v x : X) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : x = AffineMap.lineMap u v t) :
    0 ≤ (1-t) * squareDist c u + t * squareDist c v - squareDist c x := by
  have hxu : x - c = (1-t) • (u-c) + t • (v-c) := by
    rw [hx, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    module
  have hnorm : ‖x-c‖ ≤ (1-t)*‖u-c‖ + t*‖v-c‖ := by
    rw [hxu]
    calc
      _ ≤ ‖(1-t) • (u-c)‖ + ‖t • (v-c)‖ := norm_add_le _ _
      _ = (1-t)*‖u-c‖ + t*‖v-c‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith), abs_of_nonneg ht0]
  unfold squareDist
  -- already in the orientation `· - c`
  let A := ‖u-c‖
  let B := ‖v-c‖
  let W := ‖x-c‖
  have hn : 0 ≤ (1-t)*A + t*B :=
    add_nonneg (mul_nonneg (by linarith) (norm_nonneg _))
      (mul_nonneg ht0 (norm_nonneg _))
  have hw : 0 ≤ W := norm_nonneg _
  have hsq : ((1-t)*A + t*B)^2 ≤ (1-t)*A^2 + t*B^2 := by
    have hp : 0 ≤ t * (1-t) * (A-B)^2 :=
      mul_nonneg (mul_nonneg ht0 (by linarith)) (sq_nonneg _)
    nlinarith
  change 0 ≤ (1-t)*A^2 + t*B^2 - W^2
  nlinarith

/-- The gap depends continuously on the centre; hence a centre which gives a
positive Jensen gap can be replaced by one from any dense set. This is the
small geometric observation behind the countable strict test. -/
lemma exists_gap_of_dense
    {D : Set X} (hD : Dense D)
    {u v x : X} {t : ℝ} (hx : x = AffineMap.lineMap u v t)
    (ht0 : 0 < t) (ht1 : t < 1) (huv : u ≠ v) :
    ∃ c ∈ D,
      0 < (1-t) * squareDist c u + t * squareDist c v - squareDist c x := by
  let G : X → ℝ := fun c =>
    (1-t) * squareDist c u + t * squareDist c v - squareDist c x
  have hcont : Continuous G := by
    dsimp [G, squareDist]
    fun_prop
  have hGu : 0 < G u := by
    have hgap := squareDist_gap (u:=u) (v:=v) hx
    -- the centre in the foundation lemma is the left endpoint
    dsimp [G]
    rw [hgap]
    have hn : 0 < ‖v-u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm huv))
    positivity
  have hnon : ((fun c : X => G c) ⁻¹' Set.Ioi 0).Nonempty :=
    ⟨u, hGu⟩
  have hopen : IsOpen ((fun c : X => G c) ⁻¹' Set.Ioi 0) :=
    isOpen_Ioi.preimage hcont
  rcases hD.exists_mem_open hopen hnon with ⟨c, hcD, hc⟩
  exact ⟨c, hcD, hc⟩
end ChoquetAux

namespace ChoquetAux
open Topology Set
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {K : Set X}
/-- On a nonempty compact metrizable set the standard countable list of
centres already detects every nontrivial chord.  This lets one use a series
(or lexicographic maxima) rather than uncountably many tests. -/
lemma denseSeq_detects_chord [TopologicalSpace.SeparableSpace K] (hK : IsCompact K) [Nonempty K]
    {u v z : K} {t : ℝ} (hz : (z:X) = AffineMap.lineMap (u:X) (v:X) t)
    (ht : 0 < t) (ht' : t < 1) (huv : (u:X) ≠ (v:X)) :
    ∃ i : ℕ, 0 <
      (1-t) * squareDist (TopologicalSpace.denseSeq K i : X) (u:X) +
        t * squareDist (TopologicalSpace.denseSeq K i : X) (v:X) -
          squareDist (TopologicalSpace.denseSeq K i : X) (z:X) := by
  classical
  let G : K → ℝ := fun c =>
    (1-t) * squareDist (c:X) (u:X) + t * squareDist (c:X) (v:X) -
      squareDist (c:X) (z:X)
  have hcont : Continuous G := by dsimp [G, squareDist]; fun_prop
  have huval : 0 < G u := by
    dsimp [G]
    rw [squareDist_gap hz]
    have hn : 0 < ‖(v:X)-(u:X)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm huv))
    positivity
  have hopen : IsOpen (G ⁻¹' Set.Ioi 0) := isOpen_Ioi.preimage hcont
  have hne : (G ⁻¹' Set.Ioi 0).Nonempty := ⟨u, huval⟩
  have hdense : DenseRange (TopologicalSpace.denseSeq K) :=
    TopologicalSpace.denseRange_denseSeq K
  obtain ⟨i, hi⟩ := hdense.exists_mem_open hopen hne
  exact ⟨i, hi⟩
end ChoquetAux

-- END INLINED FILE: Mathlib/Support/choquet_representation_theorem_b02f2de268/StrictGeom.lean

-- BEGIN INLINED FILE: Mathlib/Support/choquet_representation_theorem_b02f2de268/StrictTest.lean

open Set Topology Filter MeasureTheory
open scoped Topology BigOperators
namespace ChoquetAux

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {K : Set X}

/-- On a compact metrizable set there is one continuous convex test which is
strict on every nontrivial chord in the ambient Banach space.  The point of
using all the squared distances (with summable positive weights) instead of
`‖·‖^2` is that no strict convexity of the norm is required. -/
lemma exists_strict_test [CompactSpace K] [Nonempty K]
    (hK : IsCompact K) :
    ∃ f : C(K, ℝ), ∀ {u v z : K} {t : ℝ},
      0 < t → t < 1 → (u:X) ≠ (v:X) →
      (z:X) = AffineMap.lineMap (u:X) (v:X) t →
      0 < (1-t) * f u + t * f v - f z := by
  classical
  -- centres from the countable dense set on the compact metric space
  let phi : ℕ → C(K, ℝ) := fun i =>
    ⟨(fun y : K =>
        squareDist (TopologicalSpace.denseSeq K i : X) (y:X)),
      (squareDist_cont (TopologicalSpace.denseSeq K i : X)).comp
        continuous_subtype_val⟩
  let w : ℕ → ℝ := fun i => (1/2:ℝ)^i
  let F : ℕ → C(K, ℝ) := fun i => (w i) • (phi i)

  -- Uniform boundedness of all squared distances on the compact product
  -- supplies convergence in the sup norm.
  have hb : ∃ C : ℝ, 0 ≤ C ∧
      ∀ c y : K, squareDist (c:X) (y:X) ≤ C := by
    have hc : Continuous (fun p : K × K =>
        squareDist (p.1:X) (p.2:X)) := by
      dsimp [squareDist]
      fun_prop
    have hbb : BddAbove ((fun p : K × K =>
        squareDist (p.1:X) (p.2:X)) '' Set.univ) :=
      IsCompact.bddAbove_image (K:= (Set.univ : Set (K × K)))
        isCompact_univ hc.continuousOn
    rcases (bddAbove_def.1 hbb) with ⟨C0, hC0⟩
    refine ⟨max C0 0, le_max_right _ _, ?_⟩
    intro c y
    have hle : squareDist (c:X) (y:X) ≤ C0 :=
      hC0 _ ⟨⟨c,y⟩, Set.mem_univ _, rfl⟩
    exact le_trans hle (le_max_left _ _)
  rcases hb with ⟨C, hC, hbound⟩

  have hphi : ∀ i : ℕ, ‖phi i‖ ≤ C := by
    intro i
    apply (ContinuousMap.norm_le (phi i) hC).2
    intro y
    have hp : 0 ≤ squareDist (TopologicalSpace.denseSeq K i : X) (y:X) := by
      dsimp [squareDist]
      positivity
    change ‖squareDist (TopologicalSpace.denseSeq K i : X) (y:X)‖ ≤ C
    rw [Real.norm_eq_abs, abs_of_nonneg hp]
    exact hbound _ _

  have hw : Summable (fun i : ℕ => (1/2:ℝ)^i) := summable_geometric_two
  have hmaj : Summable (fun i : ℕ => C * (1/2:ℝ)^i) := hw.mul_left C
  have hnorm : ∀ i : ℕ, ‖F i‖ ≤ C * (1/2:ℝ)^i := by
    intro i
    have hwi : 0 ≤ w i := by
      dsimp [w]
      positivity
    dsimp [F]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hwi]
    -- the order of the two factors in the majorant is immaterial
    simpa [w, mul_comm] using (mul_le_mul_of_nonneg_left (hphi i) hwi)
  have hsum : Summable F := Summable.of_norm_bounded hmaj hnorm

  refine ⟨∑' i : ℕ, F i, ?_⟩
  intro u v z t ht ht' huv hz

  have heval (y : K) :
      ( (∑' i : ℕ, F i) : C(K, ℝ)) y =
        ∑' i : ℕ, (w i) *
          squareDist (TopologicalSpace.denseSeq K i : X) (y:X) := by
    have hh := (ContinuousMap.evalCLM ℝ y).map_tsum hsum
    -- evaluation is a continuous linear functional on the sup norm
    simpa [F, phi, smul_eq_mul] using hh
  have hseval (y : K) :
      Summable (fun i : ℕ => (w i) *
        squareDist (TopologicalSpace.denseSeq K i : X) (y:X)) := by
    have hh := (ContinuousMap.evalCLM ℝ y).summable hsum
    simpa [F, phi, smul_eq_mul] using hh

  let A : ℕ → ℝ := fun i => (w i) *
      squareDist (TopologicalSpace.denseSeq K i : X) (u:X)
  let B : ℕ → ℝ := fun i => (w i) *
      squareDist (TopologicalSpace.denseSeq K i : X) (v:X)
  let D : ℕ → ℝ := fun i => (w i) *
      squareDist (TopologicalSpace.denseSeq K i : X) (z:X)
  have hA : Summable A := by simpa [A] using hseval u
  have hB : Summable B := by simpa [B] using hseval v
  have hD : Summable D := by simpa [D] using hseval z

  let q : ℕ → ℝ := fun i => (w i) *
       ((1-t) * squareDist (TopologicalSpace.denseSeq K i : X) (u:X) +
        t * squareDist (TopologicalSpace.denseSeq K i : X) (v:X) -
          squareDist (TopologicalSpace.denseSeq K i : X) (z:X))
  -- It is also useful to view `q` as a linear combination of three
  -- convergent evaluation series.
  have hq_eq : q = (fun i : ℕ =>
      ((1-t) * A i + t * B i) - D i) := by
    funext i
    dsimp [q, A, B, D]
    ring
  have hq : Summable q := by
    rw [hq_eq]
    exact ((hA.mul_left (1-t)).add (hB.mul_left t)).sub hD

  have hgap_as_sum :
      (1-t) * ( (∑' i : ℕ, F i) : C(K, ℝ)) u +
        t * ( (∑' i : ℕ, F i) : C(K, ℝ)) v -
          ( (∑' i : ℕ, F i) : C(K, ℝ)) z
        = ∑' i : ℕ, q i := by
    rw [heval u, heval v, heval z]
    -- write the real arithmetic as an identity of sums of the series
    -- `A`, `B`, and `D`
    change (1-t) * (∑' i : ℕ, A i) + t * (∑' i : ℕ, B i) -
        (∑' i : ℕ, D i) = ∑' i : ℕ, q i
    rw [hq_eq]
    -- the library versions of `tsum_add` and `tsum_sub` are namespaced by
    -- a summability proof
    rw [((hA.mul_left (1-t)).add (hB.mul_left t)).tsum_sub hD,
        (hA.mul_left (1-t)).tsum_add (hB.mul_left t)]
    -- scalar multiplication is just multiplication in `ℝ`
    -- and the constants can be taken outside the sum
    simp [tsum_mul_left]
  rw [hgap_as_sum]

  have hnon : ∀ i : ℕ, 0 ≤ q i := by
    intro i
    dsimp [q]
    have hi := squareDist_line_nonneg
      (TopologicalSpace.denseSeq K i : X) (u:X) (v:X) (z:X)
      (le_of_lt ht) (le_of_lt ht') hz
    have hwpos : 0 ≤ w i := by
      dsimp [w]
      positivity
    exact mul_nonneg hwpos hi

  obtain ⟨i, hi⟩ := denseSeq_detects_chord (K:=K) hK hz ht ht' huv
  have hpos : 0 < q i := by
    dsimp [q]
    have hwpos : 0 < w i := by
      dsimp [w]
      positivity
    exact mul_pos hwpos hi
  have hle : q i ≤ ∑' j : ℕ, q j := by
    have hs := Summable.sum_le_tsum (f:=q) ({i} : Finset ℕ)
        (by intro j hj; exact hnon j) hq
    simpa using hs
  exact lt_of_lt_of_le hpos hle

end ChoquetAux


namespace ChoquetAux
open Set Topology
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {K : Set X}

/-- Compactness upgrades a strict Jensen inequality on every open chord to a
uniform one on each of the quantitative bad sets.  We use the compact set of
all four witnesses `(u,v,z,t)`; this avoids any (nonexistent) continuous
choice of a chord. -/
lemma uniform_bad_of_strict [CompactSpace K]
    (f : C(K, ℝ))
    (hstrict : ∀ {u v z : K} {t : ℝ},
      0 < t → t < 1 → (u:X) ≠ (v:X) →
      (z:X) = AffineMap.lineMap (u:X) (v:X) t →
      0 < (1-t) * f u + t * f v - f z) :
    ∀ n : ℕ, ∃ g : ℝ, 0 < g ∧
      ∀ z : K, (z:X) ∈ bad K n →
        ∃ u v : K, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
          (z:X) = AffineMap.lineMap (u:X) (v:X) t ∧
          f z + g ≤ (1-t) * f u + t * f v := by
  classical
  intro n
  -- the parameter order is `((u,v),z),t`
  let line : (((K × K) × K) × ℝ) → X := fun p =>
    AffineMap.lineMap (p.1.1.1:X) (p.1.1.2:X) p.2
  let S : Set (((K × K) × K) × ℝ) :=
    ((((Set.univ : Set ((K × K) × K)) ×ˢ
        (Set.Icc (eps n) (1 - eps n))) ∩
        {p | eps n ≤ ‖(p.1.1.1:X) - (p.1.2:X)‖}) ∩
        {p | (p.1.2:X) = line p})
  let G : (((K × K) × K) × ℝ) → ℝ := fun p =>
    (1-p.2) * f p.1.1.1 + p.2 * f p.1.1.2 - f p.1.2

  have hline : Continuous line := by
    dsimp [line]
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    fun_prop
  have hdist : IsClosed
      ({p : (((K × K) × K) × ℝ) |
          eps n ≤ ‖(p.1.1.1:X) - (p.1.2:X)‖}) := by
    exact isClosed_le continuous_const (by fun_prop)
  have heq : IsClosed
      ({p : (((K × K) × K) × ℝ) |
          (p.1.2:X) = line p}) := by
    exact isClosed_eq (by fun_prop) hline
  have hbase : IsCompact
      ((Set.univ : Set ((K × K) × K)) ×ˢ
        (Set.Icc (eps n) (1 - eps n))) :=
    isCompact_univ.prod isCompact_Icc
  have hS : IsCompact S := by
    dsimp [S]
    exact (hbase.inter_right hdist).inter_right heq
  have hG : Continuous G := by
    dsimp [G]
    fun_prop

  -- On the witness set the four inequalities indeed describe a nontrivial
  -- open chord.
  have hpos : ∀ p ∈ S, 0 < G p := by
    intro p hp
    rcases hp with ⟨⟨hpbase, hd⟩, hzline⟩
    rcases hpbase with ⟨_, ht0, ht1⟩
    change eps n ≤ ‖(p.1.1.1:X) - (p.1.2:X)‖ at hd
    change (p.1.2:X) = line p at hzline
    have ht : 0 < p.2 := lt_of_lt_of_le (eps_pos n) ht0
    have ht' : p.2 < (1:ℝ) :=
      lt_of_le_of_lt ht1 (sub_lt_self (1:ℝ) (eps_pos n))
    have hneuz : (p.1.1.1:X) ≠ (p.1.2:X) := by
      intro h
      have hh : ‖(p.1.1.1:X) - (p.1.2:X)‖ = 0 := by rw [h]; simp
      have ep := eps_pos n
      linarith
    have huv : (p.1.1.1:X) ≠ (p.1.1.2:X) := by
      intro h
      have hz' : (p.1.2:X) = (p.1.1.1:X) := by
        -- the equation in `S` becomes a constant line map
        have hzv : (p.1.2:X) = (p.1.1.2:X) := by
          -- rewriting the left endpoint to the right one makes the line constant
          dsimp [line] at hzline
          rw [h] at hzline
          simpa [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
            using hzline
        exact hzv.trans h.symm
      exact hneuz hz'.symm
    apply hstrict ht ht' huv
    change (p.1.2:X) = line p at hzline
    simpa [line] using hzline

  by_cases hN : S.Nonempty
  · obtain ⟨a, ha, hamin⟩ := hS.exists_isMinOn hN hG.continuousOn
    refine ⟨G a, hpos a ha, ?_⟩
    intro z hz
    -- any witness supplied by `bad` gives a point of `S`
    rcases hz with ⟨u, hu, v, hv, t, ht0, ht1, hd, hzt⟩
    let u' : K := ⟨u, hu⟩
    let v' : K := ⟨v, hv⟩
    let p : (((K × K) × K) × ℝ) := ⟨⟨⟨u', v'⟩, z⟩, t⟩
    have hp : p ∈ S := by
      change p ∈
        ((((Set.univ : Set ((K × K) × K)) ×ˢ
          (Set.Icc (eps n) (1 - eps n))) ∩
            {p : (((K × K) × K) × ℝ) |
              eps n ≤ ‖(p.1.1.1:X) - (p.1.2:X)‖}) ∩
            {p : (((K × K) × K) × ℝ) | (p.1.2:X) = line p})
      refine ⟨⟨⟨Set.mem_univ _, ht0, ht1⟩, ?_⟩, ?_⟩
      · change eps n ≤ ‖u - (z:X)‖
        exact hd
      · change (z:X) = line p
        simpa [line, p, u', v'] using hzt
    refine ⟨u', v', t, ?_, ?_, ?_, ?_⟩
    · exact le_trans (le_of_lt (eps_pos n)) ht0
    · exact le_trans ht1 (by linarith [eps_pos n])
    · simpa [u', v'] using hzt
    · have hm : G a ≤ G p := hamin hp
      dsimp [G, p] at hm
      linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro z hz
    rcases hz with ⟨u, hu, v, hv, t, ht0, ht1, hd, hzt⟩
    let u' : K := ⟨u, hu⟩
    let v' : K := ⟨v, hv⟩
    let p : (((K × K) × K) × ℝ) := ⟨⟨⟨u', v'⟩, z⟩, t⟩
    exfalso
    apply hN
    refine ⟨p, ?_⟩
    change p ∈
      ((((Set.univ : Set ((K × K) × K)) ×ˢ
        (Set.Icc (eps n) (1 - eps n))) ∩
          {p : (((K × K) × K) × ℝ) |
            eps n ≤ ‖(p.1.1.1:X) - (p.1.2:X)‖}) ∩
          {p : (((K × K) × K) × ℝ) | (p.1.2:X) = line p})
    refine ⟨⟨⟨Set.mem_univ _, ht0, ht1⟩, ?_⟩, ?_⟩
    · change eps n ≤ ‖u - (z:X)‖
      exact hd
    · change (z:X) = line p
      simpa [line, p, u', v'] using hzt

end ChoquetAux

-- END INLINED FILE: Mathlib/Support/choquet_representation_theorem_b02f2de268/StrictTest.lean

namespace Submission

-- BEGIN INLINED FILE: Main.lean

open MeasureTheory

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem choquet [MeasurableSpace X] [BorelSpace X]
    (K : Set X) (hK_cpt : IsCompact K) (hK_cvx : Convex ℝ K)
    {x : X} (hx : x ∈ K) :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧
      μ (K.extremePoints ℝ)ᶜ = 0 ∧
      x = ∫ y, y ∂μ :=
/-ResultProofBegin-/by
  classical
  -- It suffices to construct a probability measure on the compact metric
  -- subtype.  Scalar moment equations form a nonempty compact set there; the
  -- remaining assertion below is precisely the maximal-measure (Choquet)
  -- step, now reduced to the countable compact exhaustion `bad K n` of the
  -- non-extreme points.
  have hcore : ∃ ν : ProbabilityMeasure K,
      ν ∈ ChoquetAux.admissible K x ∧
      ∀ n : ℕ, (ν : Measure K)
        {p | (p:X) ∈ ChoquetAux.bad K n} = 0 := by
    letI : CompactSpace K := (isCompact_iff_compactSpace).1 hK_cpt
    -- The only geometric ingredient left is a single continuous strictly
    -- convex test on the compact metrizable set.  A convenient construction
    -- is the rapidly converging sum of squared distances to a dense
    -- sequence; its restriction to every nontrivial affine segment has a
    -- strict Jensen gap.  We isolate its quantitative form here.
    have hstrict : ∃ f : C(K,ℝ), ∀ n : ℕ, ∃ g : ℝ, 0 < g ∧
        ∀ z : K, (z:X) ∈ ChoquetAux.bad K n →
          ∃ u v : K, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
            (z:X) = AffineMap.lineMap (u:X) (v:X) t ∧
            f z + g ≤ (1-t) * f u + t * f v := by
      letI : Nonempty K := ⟨⟨x, hx⟩⟩
      obtain ⟨f, hf⟩ := ChoquetAux.exists_strict_test (K:=K) hK_cpt
      refine ⟨f, ?_⟩
      exact ChoquetAux.uniform_bad_of_strict (K:=K) f hf
    rcases hstrict with ⟨f, hf⟩
    obtain ⟨ν, hν, hmax⟩ := ChoquetAux.exists_maximizer hK_cpt hx f
    refine ⟨ν, hν, ?_⟩
    intro n
    rcases hf n with ⟨g, hg, hgaps⟩
    let B : Set K := {p : K | (p:X) ∈ ChoquetAux.bad K n}
    have hB : IsCompact B := by
      have hc : IsClosed B :=
        (ChoquetAux.bad_isCompact hK_cpt n).isClosed.preimage continuous_subtype_val
      exact hc.isCompact
    have hw : ∀ z ∈ B, ∃ u v : K, ∃ t : ℝ,
        0 ≤ t ∧ t ≤ 1 ∧ (z:X) = AffineMap.lineMap (u:X) (v:X) t ∧
          f z + g ≤ (1-t)*f u + t*f v := by
      intro z hz
      exact hgaps z hz
    exact ChoquetAux.maximizer_zero_of_uniform_gap (X:=X) hK_cpt
      (x:=x) B hB f hg ν hν hmax hw

  rcases hcore with ⟨ν, hν, hbad⟩
  exact ChoquetAux.of_subtype_probability hK_cpt hK_cvx ν hbad
    (ChoquetAux.integral_val_eq_of_admissible hK_cpt hν).symm
/-ResultProofEnd-/
/-ResultEnd-/
-- END INLINED FILE: Main.lean

end Submission
