import Mathlib

namespace Submission

namespace LeanEval
namespace Dynamics

/-!
# Moran's equality for affine-symmetric iterated function systems

`moran_equality_affine` is the equality case of the Moran–Hutchinson dimension
theorem (Moran 1946, Hutchinson 1981): for an iterated function system on `ℝᵈ`
whose maps are affine with a common contraction factor `λ ∈ (0,1)` and
orthogonal linear parts, satisfying the open set condition, the Hausdorff
dimension of the attractor equals the similarity dimension — here
`−log n / log λ`.

The trusted helper definitions (`IsAttractor`, `IsAffineSymmetricIFS`,
`OpenSetCondition`) are non-holes. Mathlib has `dimH`, `μH[d]`,
`ContractingWith`, and the Hausdorff (e)metric on compacts, but no iterated
function systems, Hutchinson operator, attractor, or similarity dimension.

This is a category-(b) candidate from §105 of the Knill survey
(`sections/105-fractals.md`). (The general Moran–Hutchinson *inequality* and the
Cantor-set example, the section's other statements, are not included here.)
-/

open scoped Topology ENNReal NNReal
open MeasureTheory

/-- A set `S ⊆ X` is an **attractor** of the IFS `f : Fin n → X → X` if it is
nonempty compact and fixed by the Hutchinson operator `H(A) = ⋃ᵢ fᵢ(A)`. -/
def IsAttractor {X : Type*} [TopologicalSpace X] {n : ℕ}
    (f : Fin n → X → X) (S : Set X) : Prop :=
  IsCompact S ∧ S.Nonempty ∧ S = ⋃ i, f i '' S

/-- An IFS on `ℝᵈ` is **affine-symmetric** with common contraction factor
`λ ∈ (0,1)` if each map is `fᵢ(x) = λ · Aᵢ(x) + βᵢ` with `Aᵢ` a linear isometry
(orthogonal transformation) and `βᵢ` a translation. -/
def IsAffineSymmetricIFS {d n : ℕ}
    (f : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (lam : ℝ) :
    Prop :=
  0 < lam ∧ lam < 1 ∧
  ∃ A : Fin n → (EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)),
    ∃ β : Fin n → EuclideanSpace ℝ (Fin d),
      ∀ i x, f i x = lam • A i x + β i

/-- The **open set condition**: a nonempty open `G` with `fᵢ(G) ⊆ G` for all `i`
and the images `fᵢ(G)` pairwise disjoint. -/
def OpenSetCondition {d n : ℕ}
    (f : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∃ G : Set (EuclideanSpace ℝ (Fin d)), IsOpen G ∧ G.Nonempty ∧
    (∀ i, f i '' G ⊆ G) ∧
    (∀ i j : Fin n, i ≠ j → Disjoint (f i '' G) (f j '' G))



end Dynamics
end LeanEval

open LeanEval.Dynamics
open scoped Topology ENNReal NNReal
open MeasureTheory
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/

/-- An affine homothety followed by a linear isometry has exactly the
announced Lipschitz constant.  Keeping the real number in the subtype is
rather useful later, when taking diameters. -/
lemma affine_isometry_lipschitz {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] (c : ℝ) (hc : 0 < c)
    (A : E →ₗᵢ[ℝ] E) (b : E) :
    LipschitzWith (⟨c, le_of_lt hc⟩ : ℝ≥0) (fun x : E => c • A x + b) := by
  -- use the real-valued formulation of `LipschitzWith`, to avoid
  -- edistance coercions
  refine (lipschitzWith_iff_dist_le_mul).2 ?_
  intro x y
  have hd : dist (c • A x + b) (c • A y + b) = c * dist x y := by
    calc
      dist (c • A x + b) (c • A y + b)
          = dist (c • A x) (c • A y) := by
              simpa using (dist_add_right (c • A x) (c • A y) b)
      _ = ‖c • A x - c • A y‖ := by rw [dist_eq_norm]
      _ = ‖c • (A x - A y)‖ := by rw [smul_sub]
      _ = ‖c‖ * ‖A x - A y‖ := by rw [norm_smul]
      _ = c * ‖A x - A y‖ := by rw [Real.norm_eq_abs, abs_of_pos hc]
      _ = c * ‖A (x - y)‖ := by rw [A.map_sub]
      _ = c * ‖x - y‖ := by rw [A.norm_map]
      _ = c * dist x y := by rw [dist_eq_norm]
  rw [hd]
  change c * dist x y ≤ c * dist x y
  exact le_rfl


/-- Composition along a *finite* word.  The first letter is the outside
map; this convention makes the induction on coverings particularly clean. -/
def ifsWord {X : Type*} {m : ℕ} (g : Fin m → X → X) : List (Fin m) → X → X
  | [], x => x
  | i :: w, x => g i (ifsWord g w x)

@[simp] lemma ifsWord_nil {X : Type*} {m : ℕ} (g : Fin m → X → X) :
    ifsWord g [] = id := by rfl
@[simp] lemma ifsWord_cons {X : Type*} {m : ℕ} (g : Fin m → X → X)
    (i : Fin m) (w : List (Fin m)) :
    ifsWord g (i :: w) = g i ∘ ifsWord g w := by rfl

/-- Lipschitz constants multiply on finite cylinders. -/
lemma ifsWord_lipschitz {X : Type*} [PseudoEMetricSpace X]
    {m : ℕ} (g : Fin m → X → X) (K : ℝ≥0)
    (hg : ∀ i, LipschitzWith K (g i)) :
    ∀ w : List (Fin m), LipschitzWith (K ^ w.length) (ifsWord g w)
  := by
    intro w
    induction w with
    | nil =>
        change ∀ x y : X, edist x y ≤ (1 : ℝ≥0∞) * edist x y
        intro x y
        simp
    | cons i w ih =>
      -- `comp` uses the same outer-to-inner order as `ifsWord`.
      simpa [ifsWord, List.length_cons, pow_succ', mul_comm, Function.comp_def] using
        ( (hg i).comp ih )

/-- The fixed-set equation may be iterated to any finite level.  Encoding
level `k` words as functions from `Fin k` makes the index of the covering
fintype, a useful input to `hausdorffMeasure_le_liminf_sum`.  No
continuity/disjointness is needed for this purely set-theoretic fact. -/
lemma iUnion_ifsWord_image {X : Type*} {m : ℕ}
    (g : Fin m → X → X) (T : Set X)
    (hT : T = ⋃ i, g i '' T) :
    ∀ k : ℕ, T = ⋃ w : Fin k → Fin m, ifsWord g (List.ofFn w) '' T := by
  classical
  intro k
  induction k with
  | zero =>
      apply Set.Subset.antisymm
      · intro x hx
        let w : Fin 0 → Fin m := Fin.elim0
        have hword : ifsWord g (List.ofFn w) x = x := by rfl
        exact Set.mem_iUnion.2 ⟨w, ⟨x, hx, hword⟩⟩
      · intro x hx
        rcases Set.mem_iUnion.1 hx with ⟨w, hw⟩
        rcases hw with ⟨y, hy, hxy⟩
        have hw0 : w = (Fin.elim0 : Fin 0 → Fin m) := Subsingleton.elim _ _
        subst w
        change y = x at hxy
        simpa [← hxy] using hy
  | succ k ih =>
      -- Rewrite the first-level equation, then use the induction hypothesis
      -- inside each image.  A word at level `k+1` is `Fin.cons i w`.
      apply Set.Subset.antisymm
      · intro x hx
        rw [hT] at hx
        rcases Set.mem_iUnion.1 hx with ⟨i, hi⟩
        rcases hi with ⟨y, hy, hyx⟩
        -- apply the level-k cover to `y`
        rw [ih] at hy
        rcases Set.mem_iUnion.1 hy with ⟨w, hw⟩
        rcases hw with ⟨z, hz, hzy⟩
        let w' : Fin (k+1) → Fin m := Fin.cons i w
        refine Set.mem_iUnion.2 ⟨w', ?_⟩
        refine ⟨z, hz, ?_⟩
        have hlist' : List.ofFn w' = i :: List.ofFn w :=
          List.ofFn_cons i w
        change ifsWord g (List.ofFn w') z = x
        rw [hlist']
        change g i (ifsWord g (List.ofFn w) z) = x
        calc
          g i (ifsWord g (List.ofFn w) z) = g i y := congrArg (g i) hzy
          _ = x := hyx
      · intro x hx
        rcases Set.mem_iUnion.1 hx with ⟨w', hw'⟩
        rcases hw' with ⟨z, hz, hzx⟩
        let i : Fin m := w' 0
        let w : Fin k → Fin m := fun a => w' a.succ
        have hwcons : w' = Fin.cons i w := by
          funext t
          refine Fin.cases ?_ (fun j => ?_) t
          · rfl
          · rfl
        have hword : g i (ifsWord g (List.ofFn w) z) = x := by
          have hlist : List.ofFn w' = i :: List.ofFn w := by
            rw [hwcons, List.ofFn_cons]
          change ifsWord g (List.ofFn w') z = x at hzx
          simpa [hlist] using hzx
        have hy : ifsWord g (List.ofFn w) z ∈ T := by
          rw [ih]
          exact Set.mem_iUnion.2 ⟨w, ⟨z, hz, rfl⟩⟩
        rw [hT]
        exact Set.mem_iUnion.2 ⟨i, ⟨_, hy, hword⟩⟩

lemma ediam_ifsWord_image_le {X : Type*} [PseudoEMetricSpace X]
    {m : ℕ} (g : Fin m → X → X) (K : ℝ≥0)
    (hg : ∀ i, LipschitzWith K (g i)) (T : Set X)
    (w : List (Fin m)) :
    Metric.ediam (ifsWord g w '' T) ≤ (K : ℝ≥0∞) ^ w.length * Metric.ediam T := by
  have h := (ifsWord_lipschitz g K hg w).ediam_image_le T
  simpa using h


/-- Images of `G` stay in `G` at every cylinder. -/
lemma ifsWord_subset {X : Type*} {m : ℕ}
    (g : Fin m → X → X) (G : Set X)
    (hinto : ∀ i, g i '' G ⊆ G) :
    ∀ w : List (Fin m), ifsWord g w '' G ⊆ G := by
  intro w
  induction w with
  | nil =>
      intro x hx
      rcases hx with ⟨y, hy, rfl⟩
      exact hy
  | cons i w ih =>
      intro x hx
      rcases hx with ⟨y, hy, rfl⟩
      apply hinto i
      exact ⟨ifsWord g w y, ih ⟨y, hy, rfl⟩, rfl⟩

lemma disjoint_ifsWords {X : Type*} {m : ℕ}
    (g : Fin m → X → X) (G : Set X)
    (hinto : ∀ i, g i '' G ⊆ G)
    (hdis : ∀ i j : Fin m, i ≠ j → Disjoint (g i '' G) (g j '' G))
    (hinj : ∀ i, Function.Injective (g i)) :
    ∀ {u v : List (Fin m)}, u.length = v.length → u ≠ v →
      Disjoint (ifsWord g u '' G) (ifsWord g v '' G) := by
  -- Equality of lengths is used only to expose the second head.
  intro u
  induction u with
  | nil =>
    intro v hv huv
    have he : v = [] := List.length_eq_zero_iff.1 hv.symm
    exact False.elim (huv (by simpa [he]))
  | cons i u ih =>
    intro v hlen hne
    cases v with
    | nil => simp at hlen
    | cons j v =>
      have htail : u.length = v.length := by simpa using hlen
      have himg (a : Fin m) (w : List (Fin m)) :
          ifsWord g (a :: w) '' G = g a '' (ifsWord g w '' G) := by
        simpa [ifsWord, Function.comp_def] using
          (Set.image_image (g a) (ifsWord g w) G).symm
      rw [himg, himg]
      by_cases hij : i = j
      · subst j
        apply Set.disjoint_image_of_injective (hinj i)
        apply ih htail
        intro heq
        exact hne (by simp [heq])
      · apply Disjoint.mono ?_ ?_ (hdis i j hij)
        · exact Set.image_mono (ifsWord_subset g G hinto u)
        · exact Set.image_mono (ifsWord_subset g G hinto v)

lemma pairwise_disjoint_level {X : Type*} {m : ℕ}
    (g : Fin m → X → X) (G : Set X)
    (hinto : ∀ i, g i '' G ⊆ G)
    (hdis : ∀ i j : Fin m, i ≠ j → Disjoint (g i '' G) (g j '' G))
    (hinj : ∀ i, Function.Injective (g i))
    {k : ℕ} (u v : Fin k → Fin m) (huv : u ≠ v) :
      Disjoint (ifsWord g (List.ofFn u) '' G)
        (ifsWord g (List.ofFn v) '' G) := by
  apply disjoint_ifsWords g G hinto hdis hinj (by simp)
  exact fun e => huv (List.ofFn_injective e)

lemma affine_isometry_injective {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (c : ℝ) (hc : 0 < c)
    (A : E →ₗᵢ[ℝ] E) (b : E) :
    Function.Injective (fun x : E => c • A x + b) := by
  intro x y hxy
  have hs : c • A x = c • A y := add_right_cancel hxy
  have ha : A x = A y :=
    (smul_right_injective E (ne_of_gt hc)) hs
  exact A.injective ha

open Filter in
/-- Cylinder coverings give the finite-measure half at every nonnegative
exponent satisfying the elementary Moran inequality.  Boundedness supplies
the finite diameter used in the limiting cover. -/
lemma hausdorffMeasure_ifs_le {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {m : ℕ} (g : Fin m → X → X) (T : Set X)
    (hT : T = ⋃ i, g i '' T) (hb : Bornology.IsBounded T)
    (K : ℝ≥0) (hg : ∀ i, LipschitzWith K (g i))
    (hK : (K : ℝ≥0∞) < 1)
    (s : ℝ) (hs : 0 ≤ s)
    (hcrit : (m : ℝ≥0∞) * (K : ℝ≥0∞) ^ s ≤ 1) :
    μH[s] T ≤ Metric.ediam T ^ s := by
  classical
  let D : ℝ≥0∞ := Metric.ediam T
  let q : ℝ≥0∞ := (K : ℝ≥0∞)
  let r : ℕ → ℝ≥0∞ := fun k => q ^ k * D
  have hD : D ≠ ⊤ := by simpa [D] using hb.ediam_ne_top
  have hr : Tendsto r atTop (𝓝 0) := by
    have hq : q < (1 : ℝ≥0∞) := by simpa [q] using hK
    have hp := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq
    have hc : Tendsto (fun _k : ℕ => D) atTop (𝓝 D) := tendsto_const_nhds
    have hm := ENNReal.Tendsto.mul hp (Or.inr hD) hc (Or.inr (by simp : (0 : ℝ≥0∞) ≠ ⊤))
    simpa [r] using hm
  let t : (k : ℕ) → (Fin k → Fin m) → Set X :=
    fun k w => ifsWord g (List.ofFn w) '' T
  have ht : ∀ k : ℕ, ∀ w : Fin k → Fin m, Metric.ediam (t k w) ≤ r k := by
    intro k w
    have hw := ediam_ifsWord_image_le g K hg T (List.ofFn w)
    simpa [t, r, q, D] using hw
  have hst : ∀ k : ℕ, T ⊆ ⋃ w : Fin k → Fin m, t k w := by
    intro k
    have hc := iUnion_ifsWord_image g T hT k
    rw [hc]
  have hle : μH[s] T ≤
      liminf (fun k : ℕ => ∑ w : Fin k → Fin m, Metric.ediam (t k w) ^ s) atTop :=
    MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum s T r hr t
      (Filter.Eventually.of_forall ht)
      (Filter.Eventually.of_forall hst)
  have hkbound : ∀ k : ℕ,
       (∑ w : Fin k → Fin m, Metric.ediam (t k w) ^ s) ≤ D ^ s := by
    intro k
    calc
      (∑ w : Fin k → Fin m, Metric.ediam (t k w) ^ s)
          ≤ ∑ _w : Fin k → Fin m, (q ^ k * D) ^ s := by
              refine Finset.sum_le_sum ?_
              intro w hw
              exact ENNReal.rpow_le_rpow (ht k w) hs
      _ = (m : ℝ≥0∞)^ k * (q ^ k * D) ^ s := by
              simp [Finset.sum_const, nsmul_eq_mul]
      _ = ((m : ℝ≥0∞) * q ^ s) ^ k * D ^ s := by
              rw [ENNReal.mul_rpow_of_nonneg _ _ hs]
              have hqpow : (q ^ k) ^ s = (q ^ s) ^ k := by
                rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
                rw [mul_comm]
                rw [ENNReal.rpow_mul, ENNReal.rpow_natCast]
              rw [hqpow, mul_pow]
              ac_rfl
      _ ≤ D ^ s := by
             have hc' : (m : ℝ≥0∞) * q ^ s ≤ 1 := by simpa [q] using hcrit
             have hp' := pow_le_pow_left' hc' k
             have hm' := mul_le_mul_right' hp' (D ^ s)
             simpa using hm'
  have hlim :
      liminf (fun k : ℕ => ∑ w : Fin k → Fin m, Metric.ediam (t k w) ^ s) atTop
        ≤ D ^ s := by
    refine Filter.liminf_le_of_le (f := atTop)
      (u := fun k : ℕ => ∑ w : Fin k → Fin m, Metric.ediam (t k w) ^ s)
      (a := D ^ s) (h := ?_)
    intro b hbe
    obtain ⟨k, hk₁, hk₂⟩ :=
      (Filter.Eventually.exists (hbe.and (Filter.Eventually.of_forall hkbound)))
    exact hk₁.trans hk₂
  exact hle.trans (by simpa [D] using hlim)


/-- A convenient mass-distribution implication, independent of the IFS.
A global diameter bound is a little stronger than the usual small-ball
hypothesis, but any Frostman probability satisfies this after increasing the
constant. -/
lemma le_dimH_of_mass_bound {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (d : ℝ≥0) (T : Set X) (μ : Measure X) (C : ℝ≥0∞)
    (hC0 : C ≠ 0) (hCt : C ≠ ⊤)
    (hTmeas : MeasurableSet T) (hμT : μ T ≠ 0)
    (hb : ∀ t : Set X, μ t ≤ C * Metric.ediam t ^ (d:ℝ)) :
    (d : ℝ≥0∞) ≤ dimH T := by
  apply le_dimH_of_hausdorffMeasure_ne_zero (d := d)
  have hl : (C⁻¹ • μ) ≤ μH[(d:ℝ)] := by
    apply MeasureTheory.Measure.le_hausdorffMeasure (d:ℝ) (C⁻¹ • μ) 1 (by simp)
    intro t ht
    rw [Measure.smul_apply, smul_eq_mul]
    calc
      C⁻¹ * μ t ≤ C⁻¹ * (C * Metric.ediam t ^ (d:ℝ)) :=
        mul_le_mul_left' (hb t) _
      _ = Metric.ediam t ^ (d:ℝ) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hC0 hCt, one_mul]
  intro hz
  have hz' : (C⁻¹ • μ) T = 0 := by
    apply le_zero_iff.mp
    have hh := (MeasureTheory.Measure.le_iff.1 hl) T hTmeas
    simpa [hz] using hh
  rw [Measure.smul_apply, smul_eq_mul] at hz'
  have hh := (mul_eq_zero.mp hz')
  have hi : C⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hCt
  exact hμT (hh.resolve_left hi)



/-- The metric information in an affine cylinder is an equality, not just a
Lipschitz inequality.  This little observation is useful in the separation
argument for the open set condition. -/
lemma ifsWord_dist_eq {X : Type*} [PseudoMetricSpace X]
    {m : ℕ} (g : Fin m → X → X) (c : ℝ)
    (hg : ∀ i x y, dist (g i x) (g i y) = c * dist x y) :
    ∀ (w : List (Fin m)) (x y : X),
      dist (ifsWord g w x) (ifsWord g w y) = c ^ w.length * dist x y := by
  intro w
  induction w with
  | nil =>
      intro x y
      simp [ifsWord]
  | cons i w ih =>
      intro x y
      change dist (g i (ifsWord g w x)) (g i (ifsWord g w y)) = _
      rw [hg i, ih]
      simp [List.length_cons, pow_succ']
      ring

/-- Onto maps remain onto on a finite cylinder.  Surjectivity is the small
point needed to use whole balls, rather than just subsets of balls. -/
lemma ifsWord_surjective {X : Type*} {m : ℕ} (g : Fin m → X → X)
    (hg : ∀ i, Function.Surjective (g i)) :
    ∀ w : List (Fin m), Function.Surjective (ifsWord g w) := by
  intro w
  induction w with
  | nil =>
      intro x
      exact ⟨x, rfl⟩
  | cons i w ih =>
      exact (hg i).comp ih

/-- In finite dimension a (self) affine homothety by a nonzero scalar and a
linear isometry is onto.  The finite-dimensional hypothesis is important:
an isometry of an infinite dimensional space into itself need not be onto. -/
lemma affine_isometry_surjective {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (c : ℝ) (hc : 0 < c) (A : E →ₗᵢ[ℝ] E) (b : E) :
    Function.Surjective (fun x : E => c • A x + b) := by
  intro y
  have honto : Function.Surjective (A : E →ₗ[ℝ] E) :=
    LinearMap.surjective_of_injective A.injective
  obtain ⟨x, hx⟩ := honto (c⁻¹ • (y - b))
  refine ⟨x, ?_⟩
  change c • A x + b = y
  change A x = c⁻¹ • (y - b) at hx
  rw [hx, smul_smul]
  have hc0 : c ≠ 0 := ne_of_gt hc
  rw [mul_inv_cancel₀ hc0, one_smul, sub_add_cancel]

/-- Exact image of an open ball by a similarity cylinder.  We state this for
a metric space: only the distance equality, onto-ness, and positivity of the
single ratio are used. -/
lemma ifsWord_image_ball_eq {X : Type*} [PseudoMetricSpace X]
    {m : ℕ} (g : Fin m → X → X) (c : ℝ) (hc : 0 < c)
    (hd : ∀ i x y, dist (g i x) (g i y) = c * dist x y)
    (ho : ∀ i, Function.Surjective (g i))
    (w : List (Fin m)) (x : X) (r : ℝ) :
    ifsWord g w '' Metric.ball x r =
      Metric.ball (ifsWord g w x) (c ^ w.length * r) := by
  have hp : 0 < c ^ w.length := pow_pos hc _
  have he (a b : X) :
      dist (ifsWord g w a) (ifsWord g w b) = c ^ w.length * dist a b :=
    ifsWord_dist_eq g c hd w a b
  apply Set.Subset.antisymm
  · rintro z ⟨y, hy, rfl⟩
    have hy' : dist x y < r := by simpa [Metric.mem_ball, dist_comm] using hy
    have hm : c ^ w.length * dist x y < c ^ w.length * r :=
      mul_lt_mul_of_pos_left hy' hp
    simpa [Metric.mem_ball, dist_comm, he] using hm
  · intro z hz
    have hz' : dist (ifsWord g w x) z < c ^ w.length * r := by
      simpa [Metric.mem_ball, dist_comm] using hz
    obtain ⟨y, hy⟩ := (ifsWord_surjective g ho w z)
    subst z
    have hm : c ^ w.length * dist x y < c ^ w.length * r := by
      simpa [he] using hz'
    have hy' : dist x y < r := lt_of_mul_lt_mul_left hm hp.le
    exact ⟨y, (by simpa [Metric.mem_ball, dist_comm] using hy'), rfl⟩

/-- Distance equality for the generators in the problem. -/
lemma affine_isometry_dist_eq {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] (c : ℝ) (hc : 0 < c)
    (A : E →ₗᵢ[ℝ] E) (b : E) (x y : E) :
    dist (c • A x + b) (c • A y + b) = c * dist x y := by
  calc
    dist (c • A x + b) (c • A y + b)
        = dist (c • A x) (c • A y) := by
            simpa using (dist_add_right (c • A x) (c • A y) b)
    _ = ‖c • A x - c • A y‖ := by rw [dist_eq_norm]
    _ = ‖c • (A x - A y)‖ := by rw [smul_sub]
    _ = ‖c‖ * ‖A x - A y‖ := by rw [norm_smul]
    _ = c * ‖A x - A y‖ := by rw [Real.norm_eq_abs, abs_of_pos hc]
    _ = c * ‖A (x-y)‖ := by rw [A.map_sub]
    _ = c * ‖x-y‖ := by rw [A.norm_map]
    _ = c * dist x y := by rw [dist_eq_norm]


/-- The same-level packing estimate supplied by the open set condition.  The
form with volumes (rather than a rounded natural-number constant) is handy:
the factor `μ (ball 0 1)` has already been cancelled.  `T` need not be
invariant.  It only supplies points, uniformly at distance at most `R` from
the chosen point of the feasible open ball.

Thus the lemma can be used with `T` the compact attractor.  Notice that the
finiteness assertion is completely uniform in the level `k`. -/
lemma osc_level_volume_bound {d m : ℕ}
    (g : Fin m → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (c : ℝ) (hc : 0 < c)
    (A : Fin m →
      (EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)))
    (b : Fin m → EuclideanSpace ℝ (Fin d))
    (hform : ∀ i x, g i x = c • A i x + b i)
    (G : Set (EuclideanSpace ℝ (Fin d)))
    (hinto : ∀ i, g i '' G ⊆ G)
    (hdis : ∀ i j : Fin m, i ≠ j → Disjoint (g i '' G) (g j '' G))
    (x : EuclideanSpace ℝ (Fin d)) (ρ : ℝ) (hρ : 0 < ρ)
    (hx : Metric.ball x ρ ⊆ G)
    (T : Set (EuclideanSpace ℝ (Fin d))) (R : ℝ) (hR0 : 0 ≤ R)
    (hR : ∀ y ∈ T, dist x y ≤ R)
    (k : ℕ) (z : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : 0 ≤ r) :
    let W : Finset (Fin k → Fin m) :=
      @Finset.filter (Fin k → Fin m)
        (fun w => (ifsWord g (List.ofFn w) '' T ∩ Metric.closedBall z r).Nonempty)
        (Classical.decPred _) Finset.univ
    (W.card : ℝ≥0∞) * ENNReal.ofReal ((c ^ k * ρ) ^ d) ≤
      ENNReal.ofReal ((c ^ k * (ρ + R) + r) ^ d) := by
  classical
  let W : Finset (Fin k → Fin m) :=
      @Finset.filter (Fin k → Fin m)
        (fun w => (ifsWord g (List.ofFn w) '' T ∩ Metric.closedBall z r).Nonempty)
        (Classical.decPred _) Finset.univ
  dsimp
  -- distance and onto information for a single letter
  have hd1 : ∀ i u v, dist (g i u) (g i v) = c * dist u v := by
    intro i u v
    simpa [hform] using affine_isometry_dist_eq c hc (A i) (b i) u v
  have ho1 : ∀ i, Function.Surjective (g i) := by
    intro i
    have h := affine_isometry_surjective c hc (A i) (b i)
    -- do not rewrite the function under binders in the finite-dimensional
    -- proof above; extensionality is simpler here
    have he : g i = (fun u => c • A i u + b i) := funext (hform i)
    simpa [he] using h
  have hi1 : ∀ i, Function.Injective (g i) := by
    intro i
    have h := affine_isometry_injective c hc (A i) (b i)
    have he : g i = (fun u => c • A i u + b i) := funext (hform i)
    simpa [he] using h
  have hck : 0 < c ^ k := pow_pos hc _
  have hsmall : 0 < c ^ k * ρ := mul_pos hck hρ
  have hbig : 0 < c ^ k * (ρ + R) + r := by
    have h₁ : 0 < ρ + R := add_pos_of_pos_of_nonneg hρ hR0
    have h₂ : 0 < c ^ k * (ρ + R) := mul_pos hck h₁
    exact add_pos_of_pos_of_nonneg h₂ hr
  -- the chosen indices have centres close to `z`
  have hcent : ∀ w ∈ W,
      dist (ifsWord g (List.ofFn w) x) z ≤ c ^ k * R + r := by
    intro w hw
    have hw' :
        (ifsWord g (List.ofFn w) '' T ∩ Metric.closedBall z r).Nonempty :=
      (Finset.mem_filter.1 hw).2
    obtain ⟨p, hpT, hpz⟩ := hw'
    obtain ⟨y, hy, hyeq⟩ := hpT
    subst p
    have hz' : dist (ifsWord g (List.ofFn w) y) z ≤ r :=
      (Metric.mem_closedBall.1 hpz)
    have hxy := hR y hy
    have heq :
        dist (ifsWord g (List.ofFn w) x)
          (ifsWord g (List.ofFn w) y) = c ^ k * dist x y := by
      have h := ifsWord_dist_eq g c hd1 (List.ofFn w) x y
      simpa using h
    calc
      dist (ifsWord g (List.ofFn w) x) z
          ≤ dist (ifsWord g (List.ofFn w) x)
                (ifsWord g (List.ofFn w) y)
              + dist (ifsWord g (List.ofFn w) y) z :=
            dist_triangle _ _ _
      _ ≤ c ^ k * R + r := by
            rw [heq]
            exact add_le_add (mul_le_mul_of_nonneg_left hxy hck.le) hz'
  -- Distinct cylinders contain disjoint genuine balls of radius `c^k ρ`.
  have D : Set.Pairwise (↑W : Set (Fin k → Fin m))
      (fun u v : Fin k → Fin m =>
        Disjoint (Metric.ball (ifsWord g (List.ofFn u) x) (c ^ k * ρ))
          (Metric.ball (ifsWord g (List.ofFn v) x) (c ^ k * ρ))) := by
    intro u hu v hv huv
    have hlev := pairwise_disjoint_level g G hinto hdis hi1 u v huv
    have hu' := ifsWord_image_ball_eq g c hc hd1 ho1
      (List.ofFn u) x ρ
    have hv' := ifsWord_image_ball_eq g c hc hd1 ho1
      (List.ofFn v) x ρ
    -- both small balls live inside the old disjoint open cylinders
    apply Disjoint.mono ?_ ?_ hlev
    · have hu'' :
          ifsWord g (List.ofFn u) '' Metric.ball x ρ =
            Metric.ball (ifsWord g (List.ofFn u) x) (c ^ k * ρ) := by
            simpa using hu'
      rw [← hu'']
      exact Set.image_mono hx
    · have hv'' :
          ifsWord g (List.ofFn v) '' Metric.ball x ρ =
            Metric.ball (ifsWord g (List.ofFn v) x) (c ^ k * ρ) := by
            simpa using hv'
      rw [← hv'']
      exact Set.image_mono hx
  -- All of those balls are in one slightly larger ball.
  let U : Set (EuclideanSpace ℝ (Fin d)) :=
    ⋃ w ∈ W, Metric.ball (ifsWord g (List.ofFn w) x) (c ^ k * ρ)
  have hU : U ⊆ Metric.ball z (c ^ k * (ρ + R) + r) := by
    dsimp [U]
    refine Set.iUnion₂_subset (fun w hw => ?_)
    apply Metric.ball_subset_ball'
    have hh := hcent w hw
    calc
      c ^ k * ρ + dist (ifsWord g (List.ofFn w) x) z
          ≤ c ^ k * ρ + (c ^ k * R + r) := add_le_add le_rfl hh
      _ = c ^ k * (ρ + R) + r := by ring
  -- The usual volume computation.  Using `addHaar_ball_of_pos` avoids a
  -- separate calculation of the Euclidean unit-ball constant; it is positive
  -- and finite, so may be cancelled.
  let μ : Measure (EuclideanSpace ℝ (Fin d)) := Measure.addHaar
  have I :
      (W.card : ℝ≥0∞) *
            ENNReal.ofReal ((c ^ k * ρ) ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)))) *
            μ (Metric.ball 0 1) ≤
        ENNReal.ofReal ((c ^ k * (ρ + R) + r) ^
          (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)))) * μ (Metric.ball 0 1) := by
    calc
      (W.card : ℝ≥0∞) *
            ENNReal.ofReal ((c ^ k * ρ) ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)))) *
            μ (Metric.ball 0 1) = μ U := by
              rw [show U = ⋃ w ∈ W,
                    Metric.ball (ifsWord g (List.ofFn w) x) (c ^ k * ρ) by rfl]
              rw [MeasureTheory.measure_biUnion_finset D
                    (fun w _ => measurableSet_ball)]
              have hbv (w : Fin k → Fin m) :
                  μ (Metric.ball (ifsWord g (List.ofFn w) x) (c ^ k * ρ)) =
                    ENNReal.ofReal ((c ^ k * ρ) ^
                      (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)))) *
                      μ (Metric.ball 0 1) := by
                    simpa [μ] using
                      (μ.addHaar_ball_of_pos
                        (ifsWord g (List.ofFn w) x) hsmall)
              -- a constant value for every summand
              simp_rw [hbv]
              simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (Metric.ball z (c ^ k * (ρ + R) + r)) :=
            measure_mono hU
      _ = ENNReal.ofReal ((c ^ k * (ρ + R) + r) ^
              (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)))) * μ (Metric.ball 0 1) := by
            simpa [μ] using (μ.addHaar_ball_of_pos z hbig)
  have J :
      (W.card : ℝ≥0∞) *
            ENNReal.ofReal ((c ^ k * ρ) ^
              (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)))) ≤
        ENNReal.ofReal ((c ^ k * (ρ + R) + r) ^
          (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)))) := by
    -- `ball 0 1` has positive finite Haar measure in every finite-dimensional
    -- real normed space (also in dimension zero).
    have hpμ : μ (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ 0 :=
      (Metric.measure_ball_pos μ (0 : EuclideanSpace ℝ (Fin d))
        (by norm_num)).ne'
    have htμ : μ (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ ⊤ :=
      (measure_ball_lt_top).ne
    exact (ENNReal.mul_le_mul_iff_left hpμ htμ).1 I
  simpa [W, finrank_euclideanSpace] using J


/-- A scale-free reading of `osc_level_volume_bound`.  If the inspecting ball
has radius at most the cylinder ratio `c^k`, it meets at most
`((ρ+R+1)/ρ)^d` cylinders at that level.  This (with harmless integer
rounding) is the bounded-overlap constant in the OSC proof. -/
lemma osc_level_card_bound {d m : ℕ}
    (g : Fin m → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (c : ℝ) (hc : 0 < c)
    (A : Fin m → (EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin d)))
    (b : Fin m → EuclideanSpace ℝ (Fin d))
    (hform : ∀ i x, g i x = c • A i x + b i)
    (G : Set (EuclideanSpace ℝ (Fin d)))
    (hinto : ∀ i, g i '' G ⊆ G)
    (hdis : ∀ i j : Fin m, i ≠ j → Disjoint (g i '' G) (g j '' G))
    (x : EuclideanSpace ℝ (Fin d)) (ρ : ℝ) (hρ : 0 < ρ)
    (hx : Metric.ball x ρ ⊆ G)
    (T : Set (EuclideanSpace ℝ (Fin d))) (R : ℝ) (hR0 : 0 ≤ R)
    (hR : ∀ y ∈ T, dist x y ≤ R)
    (k : ℕ) (z : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : 0 ≤ r)
    (hrk : r ≤ c ^ k) :
    let W : Finset (Fin k → Fin m) :=
      @Finset.filter (Fin k → Fin m)
        (fun w => (ifsWord g (List.ofFn w) '' T ∩ Metric.closedBall z r).Nonempty)
        (Classical.decPred _) Finset.univ
    (W.card : ℝ) ≤ ((ρ + R + 1) / ρ) ^ d := by
  classical
  let W : Finset (Fin k → Fin m) :=
      @Finset.filter (Fin k → Fin m)
        (fun w => (ifsWord g (List.ofFn w) '' T ∩ Metric.closedBall z r).Nonempty)
        (Classical.decPred _) Finset.univ
  change (W.card : ℝ) ≤ _
  have J :
    (W.card : ℝ≥0∞) * ENNReal.ofReal ((c ^ k * ρ) ^ d) ≤
      ENNReal.ofReal ((c ^ k * (ρ + R) + r) ^ d) := by
    simpa [W] using
      (osc_level_volume_bound g c hc A b hform G hinto hdis
        x ρ hρ hx T R hR0 hR k z r hr)
  let u : ℝ := c ^ k
  let B : ℝ := ρ + R + 1
  have hu : 0 < u := by dsimp [u]; exact pow_pos hc _
  have hB : 0 < B := by
    dsimp [B]
    linarith
  have hsmall' : 0 < u * ρ := mul_pos hu hρ
  have hlarge' : 0 ≤ u * B := (mul_pos hu hB).le
  have hrad : c ^ k * (ρ + R) + r ≤ u * B := by
    dsimp [u, B]
    nlinarith [pow_pos hc k]
  have hpow : (c ^ k * (ρ + R) + r) ^ d ≤ (u * B) ^ d := by
    exact pow_le_pow_left₀ (by positivity : 0 ≤ c ^ k * (ρ+R)+r)
      hrad d
  have J' :
      (W.card : ℝ≥0∞) * ENNReal.ofReal ((u * ρ) ^ d) ≤
        ENNReal.ofReal ((u * B) ^ d) := by
    have htail := ENNReal.ofReal_le_ofReal hpow
    have J0 := J.trans htail
    simpa [u, B] using J0
  have Jr : (W.card : ℝ) * ((u * ρ) ^ d) ≤ (u * B) ^ d := by
    have ht : ENNReal.ofReal ((u * B) ^ d) ≠ (⊤ : ℝ≥0∞) :=
      ENNReal.ofReal_ne_top
    have htr := ENNReal.toReal_mono ht J'
    simpa [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (pow_nonneg hsmall'.le d),
      ENNReal.toReal_ofReal (pow_nonneg hlarge' d)] using htr
  have hden : 0 < (u * ρ) ^ d := pow_pos hsmall' _
  have Jdiv : (W.card : ℝ) ≤ (u * B) ^ d / (u * ρ) ^ d :=
    (le_div_iff₀ hden).2 Jr
  have heq : (u * B) ^ d / (u * ρ) ^ d = (B / ρ) ^ d := by
    rw [← div_pow]
    have hu0 : u ≠ 0 := ne_of_gt hu
    have hρ0 : ρ ≠ 0 := ne_of_gt hρ
    congr 1
    field_simp
  convert (Jdiv.trans_eq heq) using 1 <;> rfl


@[simp] lemma ifsWord_append {X : Type*} {m : ℕ}
    (g : Fin m → X → X) (u v : List (Fin m)) (x : X) :
    ifsWord g (u ++ v) x = ifsWord g u (ifsWord g v x) := by
  induction u with
  | nil => rfl
  | cons i u ih =>
      change g i (ifsWord g (u ++ v) x) = g i (ifsWord g u (ifsWord g v x))
      rw [ih]

/-- Addresses give Cauchy sequences before a coding map is chosen.  The
estimate only needs a bound at the one base point; all the powers come from
the outside common prefix. -/
lemma cauchySeq_ifsPrefix {X : Type*} [PseudoMetricSpace X]
    {m : ℕ} (g : Fin m → X → X) (c C : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hd : ∀ i x y, dist (g i x) (g i y) = c * dist x y)
    (p : X) (hbase : ∀ i, dist p (g i p) ≤ C)
    (a : ℕ → Fin m) :
    CauchySeq (fun k =>
      ifsWord g (List.ofFn (fun i : Fin k => a (i : ℕ))) p) := by
  let q : ℕ → X := fun k =>
      ifsWord g (List.ofFn (fun i : Fin k => a (i : ℕ))) p
  change CauchySeq q
  apply cauchySeq_of_le_geometric c C hc1
  intro k
  have hlist :
      List.ofFn (fun i : Fin (k+1) => a (i : ℕ)) =
        (List.ofFn (fun i : Fin k => a (i : ℕ))) ++ [a k] := by
    rw [List.ofFn_succ', List.concat_eq_append]
    rfl
  change dist (ifsWord g (List.ofFn (fun i : Fin k => a (i : ℕ))) p)
      (ifsWord g (List.ofFn (fun i : Fin (k+1) => a (i : ℕ))) p) ≤ _
  rw [hlist, ifsWord_append]
  change dist (ifsWord g (List.ofFn (fun i : Fin k => a (i : ℕ))) p)
      (ifsWord g (List.ofFn (fun i : Fin k => a (i : ℕ))) (g (a k) p)) ≤ _
  rw [ifsWord_dist_eq g c hd]
  have hcp : 0 ≤ c ^ (List.ofFn (fun i : Fin k => a (i : ℕ))).length :=
    (pow_nonneg hc0 _)
  have hh := mul_le_mul_of_nonneg_left (hbase (a k)) hcp
  simpa [mul_comm] using hh


/-- A finite prefix evaluation is a measurable function on the address space.
It only uses finitely many coordinates, so no regularity of the maps is
needed here. -/
lemma measurable_ifsPrefix {X : Type*} [MeasurableSpace X]
    {m : ℕ} (g : Fin m → X → X) (p : X) (k : ℕ) :
    Measurable (fun a : (ℕ → Fin m) =>
      ifsWord g (List.ofFn (fun i : Fin k => a (i : ℕ))) p) := by
  let r : (ℕ → Fin m) → (Fin k → Fin m) :=
    fun a i => a (i : ℕ)
  have hr : Measurable r := by
    apply measurable_pi_lambda
    intro i
    exact measurable_pi_apply (i : ℕ)
  have hv : Measurable (fun w : (Fin k → Fin m) =>
      ifsWord g (List.ofFn w) p) :=
    measurable_of_finite _
  exact hv.comp hr

/-- The elementary cylinder in the address space determined by the first
`k` coordinates. -/
def prefixCylinder {m : ℕ} {k : ℕ} (w : Fin k → Fin m) :
    Set (ℕ → Fin m) := {a | ∀ i : Fin k, a (i : ℕ) = w i}

lemma measurableSet_prefixCylinder {m k : ℕ} (w : Fin k → Fin m) :
    MeasurableSet (prefixCylinder w) := by
  classical
  -- it is a finite intersection of coordinate singletons
  have hr : Measurable (fun a : (ℕ → Fin m) =>
      (fun i : Fin k => a (i : ℕ))) := by
    apply measurable_pi_lambda
    intro i
    exact measurable_pi_apply (i : ℕ)
  have hs : MeasurableSet ({w} : Set (Fin k → Fin m)) :=
    MeasurableSet.singleton w
  have he : prefixCylinder w = (fun a : (ℕ → Fin m) =>
      (fun i : Fin k => a (i : ℕ))) ⁻¹' ({w} : Set (Fin k → Fin m)) := by
    ext a
    simp [prefixCylinder, funext_iff]
  rw [he]
  exact hr hs


/-- Under fair independent digits a prefix has mass `m^{-k}`.  Stating the
calculation separately keeps all conversions between `Fin k` and a `range`
in one place. -/
lemma infinitePi_uniform_prefix {m : ℕ} [NeZero m]
    {k : ℕ} (w : Fin k → Fin m) :
    let u : Measure (Fin m) := (PMF.uniformOfFintype (Fin m)).toMeasure
    (Measure.infinitePi (fun _ : ℕ => u)) (prefixCylinder w) =
      ((m : ℝ≥0∞)⁻¹) ^ k := by
  classical
  dsimp
  let u : Measure (Fin m) := (PMF.uniformOfFintype (Fin m)).toMeasure
  haveI hu : IsProbabilityMeasure u := by
    dsimp [u]
    infer_instance
  let t : (i : ℕ) → Set (Fin m) := fun i =>
    if h : i < k then {w ⟨i,h⟩} else Set.univ
  have he : prefixCylinder w = Set.pi (↑(Finset.range k) : Set ℕ) t := by
    ext a
    constructor
    · intro ha i hi
      have hik : i < k := (Finset.mem_range.1 hi)
      -- `Set.pi` asks membership in the corresponding singleton
      simp [t, hik, ha ⟨i,hik⟩]
    · intro ha i
      have hi : (i : ℕ) ∈ Finset.range k := Finset.mem_range.2 i.isLt
      have hh := ha i hi
      simpa [t, i.isLt] using hh
  change (Measure.infinitePi (fun _ : ℕ => u)) (prefixCylinder w) = _
  rw [he]
  have hs : ∀ i ∈ (Finset.range k), MeasurableSet (t i) := by
    intro i hi
    have hik : i < k := Finset.mem_range.1 hi
    simp [t, hik]
  rw [Measure.infinitePi_pi (fun _ : ℕ => u) hs]
  -- every factor is a singleton in the uniform law
  have hv : ∀ i ∈ Finset.range k, u (t i) = (m : ℝ≥0∞)⁻¹ := by
    intro i hi
    have hik : i < k := Finset.mem_range.1 hi
    simp [t, hik, u, PMF.toMeasure_apply_singleton,
      PMF.uniformOfFintype_apply]
  classical
  calc
    (∏ i ∈ Finset.range k, u (t i))
        = ∏ _i ∈ Finset.range k, ((m : ℝ≥0∞)⁻¹) := by
            apply Finset.prod_congr rfl
            intro i hi
            exact hv i hi
    _ = ((m : ℝ≥0∞)⁻¹) ^ k := by simp


lemma continuous_ifsWord {X : Type*} [TopologicalSpace X]
    {m : ℕ} (g : Fin m → X → X) (hg : ∀ i, Continuous (g i))
    (w : List (Fin m)) : Continuous (ifsWord g w) := by
  induction w with
  | nil => exact continuous_id
  | cons i w ih => exact (hg i).comp ih

/-- A limit address lies in its (closed, compact) prefix cylinder. -/
lemma limit_mem_prefix_image {X : Type*} [MetricSpace X]
    {m : ℕ} (g : Fin m → X → X)
    (hg : ∀ i, Continuous (g i))
    (S : Set X) (hS : IsCompact S)
    (hinto : ∀ i, g i '' S ⊆ S) (p : X) (hp : p ∈ S)
    (a : ℕ → Fin m) (q : X)
    (hq : Filter.Tendsto
      (fun j => ifsWord g (List.ofFn (fun i : Fin j => a (i : ℕ))) p)
        Filter.atTop (𝓝 q)) (k : ℕ) :
    q ∈ ifsWord g (List.ofFn (fun i : Fin k => a (i : ℕ))) '' S := by
  let w : Fin k → Fin m := fun i => a (i : ℕ)
  let F : X → X := ifsWord g (List.ofFn w)
  have hcont : Continuous F := continuous_ifsWord g hg _
  have hclosed : IsClosed (F '' S) := (hS.image hcont).isClosed
  -- keep only terms whose index is of the form `k+j`
  have hq' : Filter.Tendsto
      (fun j : ℕ => ifsWord g
        (List.ofFn (fun i : Fin (j+k) => a (i : ℕ))) p)
        Filter.atTop (𝓝 q) := by
    exact hq.comp (Filter.tendsto_add_atTop_nat k)
  have hin (j : ℕ) :
      ifsWord g (List.ofFn (fun i : Fin (j+k) => a (i : ℕ))) p
        ∈ F '' S := by
    let v : Fin j → Fin m := fun i => a (k + (i : ℕ))
    have happ : List.ofFn (fun i : Fin (k+j) => a (i : ℕ)) =
        List.ofFn w ++ List.ofFn v := by
      have he : (fun i : Fin (k+j) => a (i : ℕ)) = Fin.append w v := by
        funext i
        refine Fin.addCases ?_ ?_ i
        · intro t
          rw [Fin.append_left]
          rfl
        · intro t
          rw [Fin.append_right]
          rfl
      rw [he, List.ofFn_fin_append]
    have htail : ifsWord g (List.ofFn v) p ∈ S :=
      ifsWord_subset g S hinto _ ⟨p, hp, rfl⟩
    have hident : j + k = k + j := Nat.add_comm _ _
    -- switch the order of the two summands for `happ`
    have hall : List.ofFn (fun i : Fin (j+k) => a (i : ℕ)) =
        List.ofFn (fun i : Fin (k+j) => a (i : ℕ)) := by
      -- casting `Fin` leaves the underlying natural number unchanged
      exact List.ofFn_congr hident _
    refine ⟨ifsWord g (List.ofFn v) p, htail, ?_⟩
    -- `ifsWord_append` is stated pointwise
    change F (ifsWord g (List.ofFn v) p) = _
    dsimp [F]
    rw [← ifsWord_append]
    rw [← happ, ← hall]
  exact hclosed.mem_of_tendsto hq' (Filter.Eventually.of_forall hin)
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem moran_equality_affine {d n : ℕ} (hn : 1 ≤ n)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (h_aff : IsAffineSymmetricIFS f lam)
    (h_osc : OpenSetCondition f)
    {S : Set (EuclideanSpace ℝ (Fin d))} (hS : IsAttractor f S) :
    dimH S = ENNReal.ofReal (- Real.log n / Real.log lam) :=
/-ResultProofBegin-/by
  classical
  rcases h_aff with ⟨hl0, hl1, A, b, hform⟩
  rcases hS with ⟨hcomp, hne, hfix⟩
  have hLip (i : Fin n) :
      LipschitzWith (⟨lam, le_of_lt hl0⟩ : ℝ≥0) (f i) := by
    have heq : f i = (fun x => lam • A i x + b i) :=
      funext (fun x => hform i x)
    rw [heq]
    exact affine_isometry_lipschitz lam hl0 (A i) (b i)
  by_cases hn1 : n = 1
  · subst n
    have hfix0 : S = f (0 : Fin 1) '' S := by
      apply Set.Subset.antisymm
      · intro x hx
        rw [hfix] at hx
        rcases Set.mem_iUnion.1 hx with ⟨i, hi⟩
        have hi0 : i = (0 : Fin 1) := Fin.eq_zero i
        simpa [hi0] using hi
      · intro x hx
        rw [hfix]
        exact Set.mem_iUnion.2 ⟨(0 : Fin 1), hx⟩
    have hdiam : Metric.diam S ≤ lam * Metric.diam S := by
      have hd := (hLip (0 : Fin 1)).diam_image_le S hcomp.isBounded
      calc
        Metric.diam S = Metric.diam (f (0 : Fin 1) '' S) := congrArg Metric.diam hfix0
        _ ≤ lam * Metric.diam S := hd
    have hd0 : Metric.diam S = 0 := by
      have hnon : 0 ≤ Metric.diam S := Metric.diam_nonneg
      nlinarith
    have hsub : S.Subsingleton := by
      rcases Set.subsingleton_or_nontrivial S with h | h
      · exact h
      · have hp := Metric.diam_pos h hcomp.isBounded
        rw [hd0] at hp
        exact False.elim ((lt_irrefl 0) hp)
    calc
      dimH S = 0 := dimH_subsingleton hsub
      _ = ENNReal.ofReal (- Real.log (1 : ℕ) / Real.log lam) := by norm_num
  · have hn2 : 2 ≤ n := by omega
    by_cases hd : d = 0
    · subst d
      rcases h_osc with ⟨G, hGo, hG, hinto, hdis⟩
      have h0lt : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn2
      have h1lt : 1 < n := lt_of_lt_of_le (by decide : 1 < 2) hn2
      let i : Fin n := ⟨0, h0lt⟩
      let j : Fin n := ⟨1, h1lt⟩
      have hij : i ≠ j := by
        intro e
        have ev : i.val = j.val := congrArg Fin.val e
        change (0:ℕ) = 1 at ev
        omega
      have emp := hdis i j hij
      rcases hG with ⟨x, hx⟩
      have hi : f i x ∈ f i '' G := ⟨x, hx, rfl⟩
      have hj : f j x ∈ f j '' G := ⟨x, hx, rfl⟩
      have exy : f i x = f j x := Subsingleton.elim _ _
      have hj' : f i x ∈ f j '' G := exy.symm ▸ hj
      exact False.elim ((Set.disjoint_left.1 emp) hi hj')
    · -- The cylinder construction gives the upper estimate without OSC.
      let sig : ℝ := - Real.log (n:ℝ) / Real.log lam
      let K : ℝ≥0 := ⟨lam, le_of_lt hl0⟩
      have hnreal : (1:ℝ) < (n:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hn2)
      have hlneg : Real.log lam < 0 := Real.log_neg hl0 hl1
      have hspos : 0 < sig := by
        dsimp [sig]
        have hp : 0 < Real.log (n:ℝ) := Real.log_pos hnreal
        have hminus : - Real.log (n:ℝ) < 0 := neg_neg_of_pos hp
        exact div_pos_of_neg_of_neg hminus hlneg
      have hs : 0 ≤ sig := le_of_lt hspos
      have hK : (K : ℝ≥0∞) < 1 := by
        -- the coe order on the subtype is the ordinary positive number
        exact_mod_cast hl1
      have hcrit0 : (n : ℝ≥0∞) * (K : ℝ≥0∞) ^ sig = 1 := by
        apply (ENNReal.toReal_eq_one_iff _).1
        rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
        rw [← ENNReal.toReal_rpow]
        change (n : ℝ) * lam ^ (- Real.log (n:ℝ) / Real.log lam) = 1
        rw [Real.rpow_def_of_pos hl0]
        have hlog : Real.log lam ≠ 0 := hlneg.ne
        have he : Real.log lam * (- Real.log (n:ℝ) / Real.log lam) = - Real.log (n:ℝ) := by
          field_simp
        rw [he, Real.exp_neg, Real.exp_log (by exact_mod_cast (by omega : 0 < n))]
        have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
        exact mul_inv_cancel₀ hn0
      have hmu : μH[sig] S ≤ Metric.ediam S ^ sig := by
        apply hausdorffMeasure_ifs_le f S hfix hcomp.isBounded K hLip hK sig hs
        exact le_of_eq hcrit0
      let sNN : ℝ≥0 := ⟨sig, hs⟩
      have hnotop : μH[(sNN:ℝ)] S ≠ (⊤ : ℝ≥0∞) := by
        have hbfin := hcomp.isBounded.ediam_ne_top
        have hpow : Metric.ediam S ^ sig < (⊤ : ℝ≥0∞) :=
          ENNReal.rpow_lt_top_of_nonneg hs hbfin
        have hlt : μH[sig] S < (⊤ : ℝ≥0∞) := lt_of_le_of_lt hmu hpow
        change μH[sig] S ≠ (⊤ : ℝ≥0∞)
        exact hlt.ne
      have hupper : dimH S ≤ ENNReal.ofReal sig := by
        have h := dimH_le_of_hausdorffMeasure_ne_top (s := S) (d := sNN) hnotop
        have heq : ENNReal.ofReal sig = (sNN : ℝ≥0∞) :=
          ENNReal.ofReal_eq_coe_nnreal hs
        simpa [heq] using h
      -- the reverse bound is the OSC (mass-distribution) half.
      change dimH S = ENNReal.ofReal sig
      refine le_antisymm hupper ?_
      rw [ENNReal.ofReal_eq_coe_nnreal hs]
      -- Choose once and for all an OSC ball and a bound for the attractor.
      -- `osc_level_card_bound` then gives the genuine uniform bounded-overlap
      -- statement; no separation of the compact (closed) cylinders is being
      -- assumed here.
      rcases h_osc with ⟨G, hGo, hGne, hinto, hdis⟩
      obtain ⟨x, hxG⟩ := hGne
      obtain ⟨rho, hrho, hxball⟩ := (Metric.isOpen_iff.1 hGo) x hxG
      obtain ⟨R, hRpos, hSR⟩ := hcomp.isBounded.subset_closedBall_lt 0 x
      have hR : ∀ y ∈ S, dist x y ≤ R := by
        intro y hy
        have hy' := hSR hy
        have hh := (Metric.mem_closedBall.1 hy')
        simpa [dist_comm] using hh
      have hpack : ∀ (k : ℕ) (z : EuclideanSpace ℝ (Fin d))
          (r : ℝ), 0 ≤ r -> r ≤ lam ^ k ->
          let W : Finset (Fin k → Fin n) :=
            @Finset.filter (Fin k → Fin n)
              (fun w =>
                (ifsWord f (List.ofFn w) '' S ∩
                  Metric.closedBall z r).Nonempty)
              (Classical.decPred _) Finset.univ
          (W.card : ℝ) ≤ ((rho + R + 1) / rho) ^ d := by
        intro k z r hr hrk
        exact osc_level_card_bound f lam hl0 A b hform G hinto hdis
          x rho hrho hxball S R (le_of_lt hRpos) hR k z r hr hrk
      have hintoS : ∀ i, f i '' S ⊆ S := by
        intro i y hy
        rw [hfix]
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      obtain ⟨p, hpS⟩ := hne
      have hbase : ∀ i : Fin n, dist p (f i p) ≤ Metric.diam S := by
        intro i
        exact Metric.dist_le_diam_of_mem hcomp.isBounded hpS
          (hintoS i ⟨p, hpS, rfl⟩)
      have hdist : ∀ i u v, dist (f i u) (f i v) = lam * dist u v := by
        intro i u v
        simpa [hform] using affine_isometry_dist_eq lam hl0 (A i) (b i) u v
      -- Existence of every address point is not a compactness black box: the
      -- common-prefix geometric estimate is a genuine Cauchy proof.  The
      -- eventual push-forward measure will be based on these limits.
      have haddress : ∀ a : ℕ → Fin n,
          CauchySeq (fun k =>
            ifsWord f (List.ofFn (fun t : Fin k => a (t : ℕ))) p) := by
        intro a
        exact cauchySeq_ifsPrefix f lam (Metric.diam S) (le_of_lt hl0) hl1
          hdist p hbase a
      have haddress_limit : ∀ a : ℕ → Fin n,
          ∃ q : EuclideanSpace ℝ (Fin d),
            Filter.Tendsto
              (fun k => ifsWord f (List.ofFn (fun t : Fin k => a (t : ℕ))) p)
              Filter.atTop (𝓝 q) := by
        intro a
        exact cauchySeq_tendsto_of_complete (haddress a)
      have haddress_mem : ∀ (a : ℕ → Fin n) (k : ℕ),
          ifsWord f (List.ofFn (fun t : Fin k => a (t : ℕ))) p ∈ S := by
        intro a k
        exact ifsWord_subset f S hintoS _ ⟨p, hpS, rfl⟩
      letI : NeZero n := ⟨by omega⟩
      let u : Measure (Fin n) := (PMF.uniformOfFintype (Fin n)).toMeasure
      haveI hu : IsProbabilityMeasure u := by dsimp [u]; infer_instance
      let ν : Measure (ℕ → Fin n) := Measure.infinitePi (fun _ : ℕ => u)
      haveI hν : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
      let φ : (ℕ → Fin n) → EuclideanSpace ℝ (Fin d) := fun a =>
        Classical.choose (haddress_limit a)
      have hφlim (a : ℕ → Fin n) :
          Filter.Tendsto
            (fun k => ifsWord f
              (List.ofFn (fun t : Fin k => a (t : ℕ))) p)
            Filter.atTop (𝓝 (φ a)) :=
        Classical.choose_spec (haddress_limit a)
      have hφmeas : Measurable φ := by
        apply measurable_of_tendsto_metrizable
          (f := fun k a =>
            ifsWord f (List.ofFn (fun t : Fin k => a (t : ℕ))) p)
        · intro k
          exact measurable_ifsPrefix f p k
        · rw [tendsto_pi_nhds]
          intro a
          exact hφlim a
      have hfcont : ∀ i, Continuous (f i) :=
        fun i => (hLip i).continuous
      have hφprefix (a : ℕ → Fin n) (k : ℕ) :
          φ a ∈ ifsWord f
            (List.ofFn (fun i : Fin k => a (i : ℕ))) '' S := by
        exact limit_mem_prefix_image f hfcont S hcomp hintoS p hpS a (φ a)
          (hφlim a) k
      have hφS (a : ℕ → Fin n) : φ a ∈ S :=
        hcomp.isClosed.mem_of_tendsto (hφlim a)
          (Filter.Eventually.of_forall (haddress_mem a))
      let μ : Measure (EuclideanSpace ℝ (Fin d)) := Measure.map φ ν
      have hμdef (t : Set (EuclideanSpace ℝ (Fin d))) (ht : MeasurableSet t) :
          μ t = ν (φ ⁻¹' t) := by
        exact Measure.map_apply hφmeas ht
      haveI hμprob : IsProbabilityMeasure μ :=
        Measure.isProbabilityMeasure_map hφmeas.aemeasurable
      have hμS : μ S ≠ 0 := by
        have hm : μ S = 1 := by
          rw [hμdef S hcomp.isClosed.measurableSet]
          have he : φ ⁻¹' S = Set.univ := by
            ext a; simp [hφS]
          simp [he]
        simp [hm]
      -- First the elementary ball bound at an arbitrary fixed level.
      have hball_level (k : ℕ) (z : EuclideanSpace ℝ (Fin d)) (r : ℝ)
          (hr : 0 ≤ r) (hrk : r ≤ lam ^ k) :
          μ (Metric.closedBall z r) ≤
            ENNReal.ofReal (((rho + R + 1) / rho) ^ d) *
              ((n : ℝ≥0∞)⁻¹) ^ k := by
        let W : Finset (Fin k → Fin n) :=
          @Finset.filter (Fin k → Fin n)
            (fun w => (ifsWord f (List.ofFn w) '' S ∩
                Metric.closedBall z r).Nonempty)
            (Classical.decPred _) Finset.univ
        have hWreal : (W.card : ℝ) ≤ ((rho + R + 1) / rho) ^ d := by
          simpa [W] using (hpack k z r hr hrk)
        have hW : (W.card : ℝ≥0∞) ≤
            ENNReal.ofReal (((rho + R + 1) / rho) ^ d) := by
          have hc0 : 0 ≤ (W.card : ℝ) := by exact_mod_cast (Nat.zero_le W.card)
          have := ENNReal.ofReal_le_ofReal hWreal
          simpa [ENNReal.ofReal_natCast] using this
        have hsub : φ ⁻¹' (Metric.closedBall z r) ⊆
              ⋃ w ∈ W, prefixCylinder w := by
          intro a ha
          let w : Fin k → Fin n := fun i => a (i : ℕ)
          have hnon : (ifsWord f (List.ofFn w) '' S ∩
                Metric.closedBall z r).Nonempty :=
            ⟨φ a, hφprefix a k, ha⟩
          have hw : w ∈ W := Finset.mem_filter.2
            ⟨Finset.mem_univ _, hnon⟩
          exact Set.mem_iUnion.2 ⟨w, Set.mem_iUnion.2 ⟨hw, by
            intro i; rfl⟩⟩
        calc
          μ (Metric.closedBall z r)
              = ν (φ ⁻¹' (Metric.closedBall z r)) :=
                  hμdef _ measurableSet_closedBall
          _ ≤ ν (⋃ w ∈ W, prefixCylinder w) := measure_mono hsub
          _ ≤ ∑ w ∈ W, ν (prefixCylinder w) :=
                measure_biUnion_finset_le _ _
          _ = (W.card : ℝ≥0∞) * ((n : ℝ≥0∞)⁻¹) ^ k := by
                have hv (w : Fin k → Fin n) :
                    ν (prefixCylinder w) = ((n : ℝ≥0∞)⁻¹) ^ k := by
                  simpa [ν, u] using (infinitePi_uniform_prefix w)
                simp_rw [hv]
                simp [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ENNReal.ofReal (((rho + R + 1) / rho) ^ d) *
                  ((n : ℝ≥0∞)⁻¹) ^ k :=
                mul_le_mul_right' hW _
      -- The similarity equation in an `ENNReal` form convenient for powers.
      let qlam : ℝ≥0∞ := ENNReal.ofReal lam
      let Bc : ℝ≥0∞ := ENNReal.ofReal (((rho + R + 1) / rho) ^ d)
      have hq : (K : ℝ≥0∞) = qlam := by
        dsimp [K, qlam]
        rw [ENNReal.coe_nnreal_eq]
        rfl
      have hrel : qlam ^ sig = (n : ℝ≥0∞)⁻¹ := by
        apply ENNReal.eq_inv_of_mul_eq_one_left
        -- the order of the two factors in `hcrit0` was opposite
        simpa [hq] using (show
          qlam ^ sig * (n : ℝ≥0∞) = 1 by
            simpa [hq, mul_comm] using hcrit0)
      have hq0 : qlam ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hl0)
      have hqt : qlam ≠ (⊤ : ℝ≥0∞) := by simp [qlam]
      have hninv : (n : ℝ≥0∞)⁻¹ < 1 := by
        rw [ENNReal.inv_lt_one]
        exact_mod_cast (show 1 < n from lt_of_lt_of_le (by decide : 1 < 2) hn2)
      have hzero (z : EuclideanSpace ℝ (Fin d)) :
          μ (Metric.closedBall z 0) = 0 := by
        apply le_zero_iff.mp
        have hpw := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hninv
        have htB : Bc ≠ (⊤ : ℝ≥0∞) := by simp [Bc]
        have htt : Filter.Tendsto
            (fun j : ℕ => Bc * ((n : ℝ≥0∞)⁻¹) ^ j)
              Filter.atTop (𝓝 0) := by
          have := ENNReal.Tendsto.const_mul hpw (Or.inr htB)
          simpa using this
        have hle : μ (Metric.closedBall z 0) ≤ (0:ℝ≥0∞) := by
          apply ge_of_tendsto' htt
          intro j
          simpa [Bc] using (hball_level j z 0 (by norm_num)
          (by exact (pow_pos hl0 _).le))
        exact hle
      -- For a strictly positive radius below one, take the last level whose
      -- ratio is still at least that radius.
      have hball_small (z : EuclideanSpace ℝ (Fin d)) (r : ℝ)
          (hr0 : 0 < r) (hr1 : r ≤ 1) :
          μ (Metric.closedBall z r) ≤
            (Bc * qlam ^ (-sig)) * (ENNReal.ofReal r) ^ sig := by
        have hex : ∃ t : ℕ, lam ^ t < r :=
          exists_pow_lt_of_lt_one hr0 hl1
        let t : ℕ := Nat.find hex
        have htl : lam ^ t < r := Nat.find_spec hex
        have htpos : 0 < t := by
          have hn0 : ¬ (lam ^ (0:ℕ) < r) := by simp [not_lt.mpr hr1]
          exact Nat.pos_of_ne_zero (fun e => hn0 (e ▸ htl))
        let j : ℕ := t - 1
        have htj : t = j + 1 := by
          dsimp [j]
          omega
        have hrj : r ≤ lam ^ j := by
          by_contra hh
          have hh' : lam ^ j < r := lt_of_not_ge hh
          have hmin := Nat.find_min' hex hh'
          -- `j=t-1` is smaller
          dsimp [j] at hmin
          omega
        have hjlam : lam ^ j ≤ r / lam := by
          have hm : lam ^ j * lam < r := by
            calc lam ^ j * lam = lam ^ (j+1) := (pow_succ _ _).symm
                 _ = lam ^ t := by rw [htj]
                 _ < r := htl
          exact (le_div_iff₀ hl0).2 (le_of_lt hm)
        have hof : ENNReal.ofReal (lam ^ j) ≤
              ENNReal.ofReal r * qlam⁻¹ := by
          have hnonr : 0 ≤ r := hr0.le
          have hid : ENNReal.ofReal (r / lam) =
                ENNReal.ofReal r * qlam⁻¹ := by
            rw [div_eq_mul_inv, ENNReal.ofReal_mul hnonr,
              ENNReal.ofReal_inv_of_pos hl0]
          rw [← hid]
          exact ENNReal.ofReal_le_ofReal hjlam
        have hp : ( (n : ℝ≥0∞)⁻¹) ^ j ≤
              (ENNReal.ofReal r * qlam⁻¹) ^ sig := by
          have hh := ENNReal.rpow_le_rpow hof hs
          have heq : ((n : ℝ≥0∞)⁻¹) ^ j =
                (ENNReal.ofReal (lam ^ j)) ^ sig := by
            have hpof : ENNReal.ofReal (lam ^ j) = qlam ^ j := by
              rw [ENNReal.ofReal_pow (le_of_lt hl0)]
            rw [hpof, ← hrel]
            calc
              (qlam ^ sig) ^ j = qlam ^ (sig * (j:ℝ)) := by
                rw [ENNReal.rpow_mul, ENNReal.rpow_natCast]
              _ = qlam ^ ((j:ℝ) * sig) := by rw [mul_comm]
              _ = (qlam ^ j) ^ sig := by
                rw [ENNReal.rpow_mul, ENNReal.rpow_natCast]
          simpa [heq] using hh
        calc
          μ (Metric.closedBall z r)
              ≤ Bc * ((n : ℝ≥0∞)⁻¹)^j := by
                  simpa [Bc] using hball_level j z r hr0.le hrj
          _ ≤ Bc * (ENNReal.ofReal r * qlam⁻¹)^sig :=
                mul_le_mul_left' hp _
          _ = (Bc * qlam ^ (-sig)) * (ENNReal.ofReal r) ^ sig := by
                rw [ENNReal.mul_rpow_of_nonneg _ _ hs]
                rw [ENNReal.inv_rpow, ← ENNReal.rpow_neg]
                ac_rfl
      have hball (z : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : 0 ≤ r) :
          μ (Metric.closedBall z r) ≤
            (1 + Bc * qlam ^ (-sig)) * (ENNReal.ofReal r) ^ sig := by
        rcases hr.eq_or_lt with hz | hz
        · subst r
          rw [hzero z]
          simp [hspos.ne']
        by_cases hr1 : r ≤ 1
        · have hh := hball_small z r hz hr1
          exact hh.trans (by
            refine mul_le_mul_right' ?_ _
            exact le_add_left (le_rfl))
        · have h1 : (1 : ℝ≥0∞) ≤ (ENNReal.ofReal r) ^ sig := by
            have hr' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
              have : (1:ℝ) ≤ r := le_of_lt (lt_of_not_ge hr1)
              simpa using ENNReal.ofReal_le_ofReal this
            simpa using ENNReal.rpow_le_rpow hr' hs
          calc
            μ (Metric.closedBall z r) ≤ 1 := by
              have hp := measure_mono (μ := μ)
                (Set.subset_univ (s := Metric.closedBall z r))
              simpa using hp
            _ ≤ (1 + Bc * qlam ^ (-sig)) *
                  (ENNReal.ofReal r) ^ sig := by
                calc
                  (1:ℝ≥0∞) ≤ 1 * (ENNReal.ofReal r)^sig := by simpa using h1
                  _ ≤ (1 + Bc * qlam ^ (-sig)) *
                        (ENNReal.ofReal r)^sig := by
                    exact mul_le_mul_right' (by exact self_le_add_right (1:ℝ≥0∞) _) _
      -- A set of finite ediameter lies in the closed ball about any of its
      -- points with radius its (real) diameter.
      let C0 : ℝ≥0∞ := 1 + Bc * qlam ^ (-sig)
      have hC0z : C0 ≠ 0 := by
        dsimp [C0]
        exact ne_of_gt (by
          have h : (0:ℝ≥0∞) < 1 := by norm_num
          exact h.trans_le (self_le_add_right (1:ℝ≥0∞) _))
      have hC0t : C0 ≠ (⊤ : ℝ≥0∞) := by
        dsimp [C0, Bc, qlam]
        have hh : (ENNReal.ofReal lam) ^ (-sig) ≠ (⊤ : ℝ≥0∞) := by
          exact ENNReal.rpow_ne_top_of_ne_zero
            (ne_of_gt (ENNReal.ofReal_pos.mpr hl0)) (by simp)
        exact ENNReal.add_ne_top.mpr ⟨by simp,
          ENNReal.mul_ne_top (by simp) hh⟩
      have hall (tset : Set (EuclideanSpace ℝ (Fin d))) :
          μ tset ≤ C0 * Metric.ediam tset ^ (sNN:ℝ) := by
        change μ tset ≤ C0 * Metric.ediam tset ^ sig
        by_cases ht : tset.Nonempty
        · obtain ⟨z, hz⟩ := ht
          by_cases hfin : Metric.ediam tset = (⊤ : ℝ≥0∞)
          · rw [hfin, ENNReal.top_rpow_of_pos hspos,
              ENNReal.mul_top hC0z]
            exact le_top
          · have hsub : tset ⊆ Metric.closedBall z (Metric.diam tset) := by
              intro y hy
              exact Metric.mem_closedBall'.2
                (Metric.dist_le_diam_of_mem'
                  hfin hz hy)
            have hmain := (measure_mono hsub).trans
              (hball z (Metric.diam tset) Metric.diam_nonneg)
            have hed : ENNReal.ofReal (Metric.diam tset) =
                  Metric.ediam tset := by
              exact ENNReal.ofReal_toReal hfin
            simpa [C0, sNN, hed] using hmain
        · have hem : tset = ∅ := Set.not_nonempty_iff_eq_empty.mp ht
          simp [hem, C0, hspos.ne']
      exact le_dimH_of_mass_bound sNN S μ C0 hC0z hC0t
        hcomp.isClosed.measurableSet hμS hall
/-ResultProofEnd-/
/-ResultEnd-/

end Submission
