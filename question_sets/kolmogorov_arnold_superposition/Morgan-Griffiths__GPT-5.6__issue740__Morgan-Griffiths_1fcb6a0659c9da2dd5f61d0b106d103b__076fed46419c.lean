import Mathlib

-- BEGIN INLINED FILE: Mathlib/Support/kolmogorov_arnold_superposition_7c7ff433f4/Basic.lean

/-!
Small elementary facts used in a constructive treatment of the Lorentz
superposition problem.  In particular it is rather convenient to have an
explicit retraction onto the cube.  Defining it coordinatewise, as opposed to
using an existence of an extension theorem, has two useful features: the
proof only uses `ContinuousOn`, and values at the end points can be read off
without any choices.
-/

open scoped BigOperators

namespace KAS

/-- The elementary retraction of the line onto `[0,1]`.  I use `max` second;
this convention makes rewriting its two inequalities especially simple. -/
def clip (t : ℝ) : ℝ := max 0 (min t 1)

@[simp] theorem clip_of_mem {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    clip t = t := by
  unfold clip
  rw [min_eq_left h1, max_eq_right h0]

@[simp] theorem clip_zero : clip (0 : ℝ) = 0 := by
  simp [clip]

@[simp] theorem clip_one : clip (1 : ℝ) = 1 := by
  simp [clip]

theorem clip_mem (t : ℝ) : clip t ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · -- either the argument is non-negative, or the maximum is zero
    exact (max_le (by norm_num) (min_le_right _ _))

theorem continuous_clip : Continuous clip := by
  unfold clip
  fun_prop

/-- Coordinatewise retraction onto the closed cube. -/
def clipVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => clip (x i)

@[simp] theorem clipVec_apply {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    clipVec x i = clip (x i) := rfl

theorem continuous_clipVec {n : ℕ} :
    Continuous (clipVec : (Fin n → ℝ) → (Fin n → ℝ)) := by
  apply continuous_pi
  intro i
  exact continuous_clip.comp (continuous_apply i)

theorem clipVec_mem {n : ℕ} (x : Fin n → ℝ) :
    clipVec x ∈ Set.Icc (0 : Fin n → ℝ) 1 := by
  constructor <;> intro i
  · exact (clip_mem (x i)).1
  · exact (clip_mem (x i)).2

@[simp] theorem clipVec_of_mem {n : ℕ} {x : Fin n → ℝ}
    (h : x ∈ Set.Icc (0 : Fin n → ℝ) 1) : clipVec x = x := by
  funext i
  exact clip_of_mem (h.1 i) (h.2 i)

/-- A continuous-on function on the cube has this particularly simple
continuous extension. No separation/extension machinery is needed for this
one (we never ask the extension to have prescribed values outside). -/
def cubeExtension {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  f (clipVec x)

theorem continuous_cubeExtension {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContinuousOn f (Set.Icc (0 : Fin n → ℝ) 1)) :
    Continuous (cubeExtension f) := by
  change Continuous (f ∘ clipVec)
  exact hf.comp_continuous continuous_clipVec clipVec_mem

@[simp] theorem cubeExtension_of_mem {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    {x : Fin n → ℝ} (hx : x ∈ Set.Icc (0 : Fin n → ℝ) 1) :
    cubeExtension f x = f x := by
  change f (clipVec x) = f x
  rw [clipVec_of_mem hx]

/-- A cutoff which is one on `[0,1]` and zero at `2`.  It is not important
what it does elsewhere.  Not clipping it at zero makes several continuity
arguments a little shorter. -/
def gate (t : ℝ) : ℝ := min 1 (2 - t)

theorem continuous_gate : Continuous gate := by
  unfold gate
  fun_prop

@[simp] theorem gate_two : gate (2 : ℝ) = 0 := by
  norm_num [gate]

@[simp] theorem gate_of_unit {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    gate t = 1 := by
  unfold gate
  have : (1 : ℝ) ≤ 2 - t := by linarith
  exact min_eq_left this

end KAS

-- END INLINED FILE: Mathlib/Support/kolmogorov_arnold_superposition_7c7ff433f4/Basic.lean

-- BEGIN INLINED FILE: Mathlib/Support/kolmogorov_arnold_superposition_7c7ff433f4/OneDim.lean

open scoped BigOperators
namespace KAS

/-- The particularly degenerate (one coordinate) instance needs no
superposition at all.  Still, in the usual arity there are three summands and
only one outer function.  Sending the two unused summands to the point `2`
and multiplying the extension by `gate` is a useful little way to meet the
single-outer-function convention exactly. -/
theorem one_dim
    (f : (Fin 1 → ℝ) → ℝ)
    (hf : ContinuousOn f (Set.Icc (0 : Fin 1 → ℝ) 1)) :
    ∃ (g : ℝ → ℝ) (φ : Fin 3 → Fin 1 → ℝ → ℝ),
      Continuous g ∧ (∀ k l, Continuous (φ k l)) ∧
      ∀ x ∈ Set.Icc (0 : Fin 1 → ℝ) 1,
        f x = ∑ k, g (∑ l, φ k l (x l)) := by
  classical
  -- Regard a real in the unit interval as the one-coordinate point of the
  -- cube.  The clipping outside of it is what permits use of `ContinuousOn`.
  let A : ℝ → (Fin 1 → ℝ) := fun t _ => clip t
  have hA : Continuous A := by
    apply continuous_pi
    intro i
    exact continuous_clip.comp continuous_id
  have hAmem (t : ℝ) : A t ∈ Set.Icc (0 : Fin 1 → ℝ) 1 := by
    constructor <;> intro i
    · exact (clip_mem t).1
    · exact (clip_mem t).2
  have hFA : Continuous (fun t : ℝ => f (A t)) := by
    change Continuous (f ∘ A)
    exact hf.comp_continuous hA hAmem
  let g : ℝ → ℝ := fun t => gate t * f (A t)
  have hg : Continuous g := by
    dsimp [g]
    exact continuous_gate.mul hFA
  let φ : Fin 3 → Fin 1 → ℝ → ℝ :=
    fun k _ t => if k = (0 : Fin 3) then t else 2
  have hφ : ∀ k l, Continuous (φ k l) := by
    intro k l
    classical
    by_cases h : k = (0 : Fin 3)
    · simp [φ, h]; fun_prop
    · simp [φ, h]; fun_prop
  refine ⟨g, φ, hg, hφ, ?_⟩
  intro x hx
  have hx0 : 0 ≤ x 0 := hx.1 0
  have hx1 : x 0 ≤ 1 := hx.2 0
  have hAx : A (x 0) = x := by
    funext i
    have hi : i = (0 : Fin 1) := Fin.ext (by omega)
    subst i
    change clip (x 0) = x 0
    exact clip_of_mem hx0 hx1
  have hgx : g (x 0) = f x := by
    dsimp [g]
    rw [gate_of_unit hx0 hx1, one_mul, hAx]
  have hg2 : g 2 = 0 := by
    dsimp [g]
    rw [gate_two, zero_mul]
  -- There is one `l`.  Writing this once avoids any reasoning about a
  -- multiset of inactive coordinates.
  have hinner0 : (∑ l : Fin 1, φ 0 l (x l)) = x 0 := by
    classical
    simp [φ]
  have hinner_ne (k : Fin 3) (hk : k ≠ (0 : Fin 3)) :
      (∑ l : Fin 1, φ k l (x l)) = 2 := by
    classical
    simp [φ, hk]
  -- Finally enumerate the three layers.  `Fin.sum_univ_succ` twice (or
  -- `decide`'s `simp` version) reduces this to the three displayed values.
  -- `simp` knows the numeral elements of `Fin 3` are not zero.
  have hval (k : Fin 3) :
      g (∑ l, φ k l (x l)) = if k = (0 : Fin 3) then f x else 0 := by
    by_cases hk : k = (0 : Fin 3)
    · subst k
      rw [if_pos rfl, hinner0, hgx]
    · rw [hinner_ne k hk, hg2]
      simp [hk]
  -- Summing the point-mass expression also has the advantage not to rely on
  -- any particular representation of the two nonzero elements of `Fin 3`.
  calc
    f x = ∑ k : Fin 3, (if k = (0 : Fin 3) then f x else 0) := by
      symm
      simp
    _ = ∑ k : Fin 3, g (∑ l, φ k l (x l)) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact (hval k).symm

end KAS

-- END INLINED FILE: Mathlib/Support/kolmogorov_arnold_superposition_7c7ff433f4/OneDim.lean

-- BEGIN INLINED FILE: Mathlib/Support/kolmogorov_arnold_superposition_7c7ff433f4/Reduction.lean

open scoped BigOperators
open Classical

namespace KAS

/-- A finite closed cover is enough when checking `ContinuousOn`.  This little
lemma is often less awkward than building a subtype paste. -/
lemma continuousOn_biUnion_finset {α β ι : Type*}
    [TopologicalSpace α] [TopologicalSpace β]
    [DecidableEq ι]
    (p : ι → Set α) (c : ∀ i, IsClosed (p i)) (u : Finset ι)
    (v : α → β) (h : ∀ i ∈ u, ContinuousOn v (p i)) :
    ContinuousOn v (⋃ i ∈ u, p i) := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | @insert a u ha ih =>
      rw [Finset.set_biUnion_insert]
      exact (h a (by simp)).union_of_isClosed
        (ih (fun i hi => h i (by simp [hi]))) (c a) (by
          -- a finite union of closed sets is closed, by the analogous induction
          -- (using the finite-set lemma avoids a second recursion hypothesis).
          exact Set.Finite.isClosed_biUnion u.finite_toSet
            (by
              intro i hi
              exact c i))

/-- The finite union of a collection of closed sets, in `Finset` notation. -/
lemma isClosed_biUnion_finset {α ι : Type*} [TopologicalSpace α]
    [DecidableEq ι]
    (p : ι → Set α) (c : ∀ i, IsClosed (p i)) (u : Finset ι) :
    IsClosed (⋃ i ∈ u, p i) :=
  Set.Finite.isClosed_biUnion u.finite_toSet (by
    intro i hi
    exact c i)

private lemma abs_sum_le_sum_abs' {ι : Type*} (u : Finset ι) (a : ι → ℝ) :
    |∑ i ∈ u, a i| ≤ ∑ i ∈ u, |a i| := by
  simpa using (Finset.abs_sum_le_sum_abs (fun i : ι => a i) u)

/-- A uniformly large positive number for the finitely many one-coordinate
functions.  Strict positivity for every summand is useful as well as the
bound; it makes all of the gaps below genuinely open, even if some of the
functions vanish. -/
lemma finite_coordinate_bound {n m : ℕ}
    (φ : Fin m → Fin n → ℝ → ℝ)
    (hφ : ∀ k l, Continuous (φ k l)) :
    ∃ D : Fin m → Fin n → ℝ,
      (∀ k l, 0 ≤ D k l) ∧
      (∀ k l t, t ∈ Set.Icc (0 : ℝ) 1 → |φ k l t| ≤ D k l) := by
  classical
  have hb (k : Fin m) (l : Fin n) :
      ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, |φ k l t| ≤ C := by
    obtain ⟨C,hC⟩ := (isCompact_Icc.exists_bound_of_continuousOn
      (hφ k l).continuousOn)
    refine ⟨C, ?_⟩
    intro t ht
    simpa [Real.norm_eq_abs] using hC t ht
  choose C hC using hb
  refine ⟨fun k l => |C k l| + 1, ?_, ?_⟩
  · intro k l; positivity
  · intro k l t ht
    calc
      |φ k l t| ≤ C k l := hC k l t ht
      _ ≤ |C k l| + 1 := by
        have := le_abs_self (C k l)
        linarith

/-- The only purpose of the following, slightly technical, lemma is to
separate the outer functions.  It is independent of the difficult covering
part of the superposition theorem.

Very often a construction naturally gives `q+1` different outer functions.
On a compact cube the inner sums are bounded. Translate those sums into
parallel disjoint intervals of the real line, paste the finitely many outer
functions on the intervals, and extend the paste off the intervals.  The
inner translations can be shared equally among the coordinates.  Thus the
"one outer function" convention does not cost anything (as long as there is
a coordinate).
-/
theorem merge_outer {n m : ℕ} (hn : 1 ≤ n)
    (g : Fin m → ℝ → ℝ) (hg : ∀ k, Continuous (g k))
    (φ : Fin m → Fin n → ℝ → ℝ) (hφ : ∀ k l, Continuous (φ k l)) :
    ∃ (G : ℝ → ℝ) (ψ : Fin m → Fin n → ℝ → ℝ),
      Continuous G ∧ (∀ k l, Continuous (ψ k l)) ∧
      ∀ (x : Fin n → ℝ), x ∈ Set.Icc (0 : Fin n → ℝ) 1 →
        ∀ k, G (∑ l, ψ k l (x l)) = g k (∑ l, φ k l (x l)) := by
  classical
  obtain ⟨D,hD0,hD⟩ := finite_coordinate_bound φ hφ
  -- A common bound is easier to use than row-dependent gaps.
  let B : ℝ := ∑ k : Fin m, ∑ l : Fin n, D k l
  have hnonrow (k : Fin m) : 0 ≤ ∑ l : Fin n, D k l := by
    exact Finset.sum_nonneg fun i hi => hD0 k i
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact Finset.sum_nonneg fun i hi => hnonrow i
  have hrow (k : Fin m) : (∑ l : Fin n, D k l) ≤ B := by
    dsimp [B]
    exact Finset.single_le_sum (fun j hj => hnonrow j) (Finset.mem_univ k)
  have hys (k : Fin m) (x : Fin n → ℝ)
      (hx : x ∈ Set.Icc (0 : Fin n → ℝ) 1) :
      |∑ l : Fin n, φ k l (x l)| ≤ B := by
    calc
      |∑ l : Fin n, φ k l (x l)| ≤ ∑ l : Fin n, |φ k l (x l)| := by
        simpa using (Finset.abs_sum_le_sum_abs (fun l : Fin n => φ k l (x l)) Finset.univ)
      _ ≤ ∑ l : Fin n, D k l := by
        exact Finset.sum_le_sum fun l hl => hD k l (x l) ⟨hx.1 l, hx.2 l⟩
      _ ≤ B := hrow k
  -- consecutive centers with a gap of one
  let s : Fin m → ℝ := fun k => (2*B + 1) * (k.val : ℝ)
  let I : Fin m → Set ℝ := fun k => Set.Icc (s k - B) (s k + B)
  have hIclosed (k : Fin m) : IsClosed (I k) := isClosed_Icc
  have hsep {i j : Fin m} (hij : i.val < j.val) :
      s i + B < s j - B := by
    have hj : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hij)
    have hgap : 0 < (1 : ℝ) := by norm_num
    dsimp [s]
    nlinarith
  have huniq {t : ℝ} {i j : Fin m}
      (hi : t ∈ I i) (hj : t ∈ I j) : i = j := by
    by_contra ne
    have hcases : i.val < j.val ∨ j.val < i.val := lt_or_gt_of_ne (fun h => ne (Fin.ext h))
    cases hcases with
    | inl hlt =>
        have h := hsep hlt
        have h1 := hi.2
        have h2 := hj.1
        linarith
    | inr hlt =>
        have h := hsep hlt
        have h1 := hj.2
        have h2 := hi.1
        linarith
  -- Define the pasted value by choosing the (unique) interval which contains
  -- the point.  Only its behaviour on the closed union matters.
  let S : Set ℝ := ⋃ k : Fin m, I k
  have hSclosed : IsClosed S := by
    -- use the finite-set form to avoid any local finiteness hypotheses
    classical
    have hu : S = ⋃ k ∈ (Finset.univ : Finset (Fin m)), I k := by simp [S]
    rw [hu]
    exact isClosed_biUnion_finset I hIclosed Finset.univ
  let v : ℝ → ℝ := fun t =>
    if h : ∃ k : Fin m, t ∈ I k then
      g (Classical.choose h) (t - s (Classical.choose h))
    else 0
  have hvone (k : Fin m) {t : ℝ} (ht : t ∈ I k) :
      v t = g k (t - s k) := by
    dsimp [v]
    have h : ∃ i : Fin m, t ∈ I i := ⟨k, ht⟩
    simp only [dif_pos h]
    have heq : Classical.choose h = k := huniq (Classical.choose_spec h) ht
    -- the `h` used by `dif_pos` is definitional for the branch
    simp [heq]
  have hv_on (k : Fin m) : ContinuousOn v (I k) := by
    -- first the continuous formula on the interval, then pointwise equality
    have hc : Continuous (fun t : ℝ => g k (t - s k)) :=
      (hg k).comp (by fun_prop)
    exact hc.continuousOn.congr (by
      intro t ht
      exact (hvone k ht))
  have hvS : ContinuousOn v S := by
    classical
    have hu : S = ⋃ k ∈ (Finset.univ : Finset (Fin m)), I k := by simp [S]
    rw [hu]
    exact continuousOn_biUnion_finset I hIclosed Finset.univ v (by
      intro i hi
      exact hv_on i)
  -- Tietze is just a concise way of filling the gaps; linear interpolation
  -- gives the same map on this finite union of intervals.
  let vv : C(S, ℝ) :=
    ⟨(fun z : S => v z), (continuousOn_iff_continuous_restrict.mp hvS)⟩
  obtain ⟨GG, hGG⟩ := ContinuousMap.exists_restrict_eq hSclosed vv
  let G : ℝ → ℝ := GG
  have hG : Continuous G := GG.continuous
  have hGv {t : ℝ} (ht : t ∈ S) : G t = v t := by
    have he := DFunLike.congr_fun hGG (⟨t,ht⟩ : S)
    exact he
  -- Split a center equally among all coordinates. The nonempty-coordinate
  -- assumption is used exactly here.
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))
  let ψ : Fin m → Fin n → ℝ → ℝ :=
    fun k l t => φ k l t + s k / (n : ℝ)
  have hψ : ∀ k l, Continuous (ψ k l) := by
    intro k l
    dsimp [ψ]
    exact (hφ k l).add continuous_const
  refine ⟨G, ψ, hG, hψ, ?_⟩
  intro x hx k
  let y : ℝ := ∑ l : Fin n, φ k l (x l)
  have hy : |y| ≤ B := hys k x hx
  have hsum : (∑ l : Fin n, ψ k l (x l)) = y + s k := by
    dsimp [ψ, y]
    rw [Finset.sum_add_distrib]
    simp [nsmul_eq_mul]
    exact mul_div_cancel₀ (s k) hn0
    -- division by the nonzero number of coordinates is legitimate
  have hmem : y + s k ∈ I k := by
    change s k - B ≤ y + s k ∧ y + s k ≤ s k + B
    have ha := (abs_le.mp hy)
    constructor <;> linarith
  calc
    G (∑ l : Fin n, ψ k l (x l)) = G (y + s k) := by rw [hsum]
    _ = v (y + s k) := hGv (by
      -- one of the intervals in the union
      exact Set.mem_iUnion.mpr ⟨k, hmem⟩)
    _ = g k ((y + s k) - s k) := hvone k hmem
    _ = g k (∑ l, φ k l (x l)) := by simp [y]

/-- Summing the pointwise conclusion of `merge_outer`. -/
theorem merge_outer_sum {n m : ℕ} (hn : 1 ≤ n)
    (g : Fin m → ℝ → ℝ) (hg : ∀ k, Continuous (g k))
    (φ : Fin m → Fin n → ℝ → ℝ) (hφ : ∀ k l, Continuous (φ k l)) :
    ∃ (G : ℝ → ℝ) (ψ : Fin m → Fin n → ℝ → ℝ),
      Continuous G ∧ (∀ k l, Continuous (ψ k l)) ∧
      ∀ (x : Fin n → ℝ), x ∈ Set.Icc (0 : Fin n → ℝ) 1 →
        (∑ k, G (∑ l, ψ k l (x l))) =
          ∑ k, g k (∑ l, φ k l (x l)) := by
  obtain ⟨G,ψ,hG,hψ,h⟩ := merge_outer hn g hg φ hφ
  exact ⟨G,ψ,hG,hψ, by
    intro x hx
    exact Finset.sum_congr rfl (by
      intro i hi
      exact h x hx i)⟩

end KAS

-- END INLINED FILE: Mathlib/Support/kolmogorov_arnold_superposition_7c7ff433f4/Reduction.lean

-- BEGIN INLINED FILE: Mathlib/Support/kolmogorov_arnold_superposition_7c7ff433f4/Convergence.lean

open scoped BigOperators Topology
open Classical Filter

namespace KAS

/-- Iterating a (uniformly bounded) approximation with a *fixed* list of
inner sums. This isolates the rather innocuous analytic limiting argument
from covering/coding arguments which produce the sums.

It is useful to ask the approximating outer functions to be bounded on the
whole real line. They can always be made so by Tietze on the compact pieces.
We then sum them in the Banach space of bounded continuous functions; thus no
local uniform-limit bookkeeping is hidden in the lemma. -/
theorem geometric_limit_fixed_inner {n m : ℕ}
    (θ C R : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (φ : Fin m → Fin n → ℝ → ℝ) (hφ : ∀ k l, Continuous (φ k l))
    (f : (Fin n → ℝ) → ℝ)
    (hf : ContinuousOn f (Set.Icc (0 : Fin n → ℝ) 1))
    (hfR : ∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1, |f x| ≤ R)
    (step : ∀ (r : (Fin n → ℝ) → ℝ) (T : ℝ),
      0 ≤ T → ContinuousOn r (Set.Icc (0 : Fin n → ℝ) 1) →
      (∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1, |r x| ≤ T) →
      ∃ a : Fin m → (BoundedContinuousFunction ℝ ℝ),
        (∀ k, ‖a k‖ ≤ C*T) ∧
        ∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1,
          |r x - ∑ k, a k (∑ l, φ k l (x l))| ≤ θ*T) :
    ∃ (a : Fin m → ℝ → ℝ),
      (∀ k, Continuous (a k)) ∧
      ∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1,
        f x = ∑ k, a k (∑ l, φ k l (x l)) := by
  classical
  let Q : Set (Fin n → ℝ) := Set.Icc (0 : Fin n → ℝ) 1
  let Y : Fin m → (Fin n → ℝ) → ℝ :=
    fun k x => ∑ l : Fin n, φ k l (x l)
  have hY (k : Fin m) : Continuous (Y k) := by
    dsimp [Y]
    exact continuous_finset_sum Finset.univ (by
      intro i hi
      exact (hφ k i).comp (continuous_apply i))
  have hpow (q : ℕ) : 0 ≤ θ^q * R := mul_nonneg (pow_nonneg hθ0 q) hR
  let Good (q : ℕ) (r : (Fin n → ℝ) → ℝ) : Prop :=
       ContinuousOn r Q ∧ ∀ x ∈ Q, |r x| ≤ θ^q * R
  -- A choice at bad states is irrelevant: by induction the actual states
  -- are all good. It makes the recursive definition pleasantly plain.
  let chooseA (q : ℕ) (r : (Fin n → ℝ) → ℝ) : Fin m → (BoundedContinuousFunction ℝ ℝ) :=
    dite (Good q r)
      (fun h => Classical.choose (step r (θ^q * R) (hpow q) h.1 h.2))
      (fun _ => 0)
  have choice_spec (q) (r) (hr : Good q r) :
      (∀ k, ‖chooseA q r k‖ ≤ C * (θ^q * R)) ∧
      ∀ x ∈ Q,
        |r x - ∑ k, chooseA q r k (Y k x)| ≤ θ * (θ^q * R) := by
    dsimp [chooseA]
    simp only [dif_pos hr]
    have hs := Classical.choose_spec (step r (θ^q * R) (hpow q) hr.1 hr.2)
    exact hs
  let next (q : ℕ) (r : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
    fun x => r x - ∑ k, chooseA q r k (Y k x)
  let rr : ℕ → ((Fin n → ℝ) → ℝ) := Nat.rec f (fun q r => next q r)
  have rr_zero : rr 0 = f := rfl
  have rr_succ (q) : rr (q+1) = next q (rr q) := by
    -- `Nat.rec` uses the previous remainder at the next stage
    simp [rr]
  have rr_good : ∀ q, Good q (rr q) := by
    intro q
    induction q with
    | zero =>
      refine ⟨?_, ?_⟩
      · simpa [Q, rr_zero] using hf
      · intro x hx
        simpa [rr_zero] using (hfR x hx)
    | succ q iq =>
      have hs := choice_spec q (rr q) iq
      have hc : ContinuousOn
          (fun x : (Fin n → ℝ) => ∑ k, chooseA q (rr q) k (Y k x)) Q := by
        have hc' : Continuous
          (fun x : (Fin n → ℝ) => ∑ k, chooseA q (rr q) k (Y k x)) :=
          continuous_finset_sum Finset.univ (by
            intro k hk
            exact (chooseA q (rr q) k).continuous.comp (hY k))
        exact hc'.continuousOn
      refine ⟨?_, ?_⟩
      · rw [rr_succ]
        exact iq.1.sub hc
      · intro x hx
        rw [rr_succ]
        have hb := hs.2 x hx
        change |(next q (rr q)) x| ≤ θ^(q+1) * R
        change |rr q x - ∑ k, chooseA q (rr q) k (Y k x)| ≤ _
        calc
          |rr q x - ∑ k, chooseA q (rr q) k (Y k x)|
              ≤ θ * (θ^q * R) := hb
          _ = θ^(q+1) * R := by ring
  let A : ℕ → Fin m → (BoundedContinuousFunction ℝ ℝ) := fun q => chooseA q (rr q)
  have hAnorm (q) (k : Fin m) : ‖A q k‖ ≤ (C * R) * θ^q := by
    have z := (choice_spec q (rr q) (rr_good q)).1 k
    dsimp [A]
    -- the term `chooseA` is the one in `z`
    calc
      ‖chooseA q (rr q) k‖ ≤ C * (θ^q * R) := z
      _ = (C*R) * θ^q := by ring
  have hAsum (k : Fin m) : Summable (fun q => A q k) := by
    apply Summable.of_norm
    -- compare with a scalar geometric series
    refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hAnorm i k) ?_
    exact (summable_geometric_of_lt_one hθ0 hθ1).mul_left (C*R)
  let aa : Fin m → (BoundedContinuousFunction ℝ ℝ) := fun k => ∑' q, A q k
  have haa_cont (k : Fin m) : Continuous (fun t : ℝ => aa k t) :=
    (aa k).continuous
  refine ⟨fun k t => aa k t, haa_cont, ?_⟩
  intro x hx
  -- summation at a point commutes with the BCF sum
  have heval (k : Fin m) (z : ℝ) :
      aa k z = ∑' q, A q k z := by
    dsimp [aa]
    exact ContinuousLinearMap.map_tsum
      (BoundedContinuousFunction.evalCLM ℝ z) (hAsum k)
  have hsmall : Tendsto (fun q : ℕ => θ^q * R) atTop (𝓝 0) := by
    convert (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).mul_const R using 1
    ring_nf
  -- The partial sums telescope by construction.
  have telesc (q : ℕ) :
      rr q x = f x - ∑ k : Fin m, (∑ i ∈ Finset.range q, A i k (Y k x)) := by
    induction q with
    | zero => simp [rr_zero]
    | succ q ih =>
      rw [rr_succ]
      change rr q x - ∑ k, A q k (Y k x) = _
      rw [ih]
      have row :
          (∑ k : Fin m, (∑ i ∈ Finset.range (q+1), A i k (Y k x))) =
          (∑ k : Fin m, (∑ i ∈ Finset.range q, A i k (Y k x))) +
            ∑ k : Fin m, A q k (Y k x) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.sum_range_succ]
      rw [row]
      ring

  have hrzero : Tendsto (fun q : ℕ => rr q x) atTop (𝓝 0) := by
    -- squeeze the absolute value using the geometric remainder estimate
    have habs : ∀ q, |rr q x| ≤ θ^q * R :=
      fun q => (rr_good q).2 x hx
    have ht : Tendsto (fun q : ℕ => |rr q x|) atTop (𝓝 0) := by
      exact squeeze_zero' (Filter.Eventually.of_forall (fun q => abs_nonneg _))
        (Filter.Eventually.of_forall habs) hsmall
    -- `|u|` and the metric distance to zero coincide on `ℝ`
    rw [tendsto_iff_dist_tendsto_zero]
    simpa [Real.dist_eq, sub_zero] using ht
  -- finite rows of convergent column sums converge to the rowwise sums
  have hlimrow : Tendsto
      (fun q : ℕ => ∑ k : Fin m, (∑ i ∈ Finset.range q, A i k (Y k x)))
      atTop (𝓝 (∑ k : Fin m, aa k (Y k x))) := by
    have hk (k : Fin m) : Tendsto
        (fun q : ℕ => ∑ i ∈ Finset.range q, A i k (Y k x)) atTop
        (𝓝 (aa k (Y k x))) := by
      rw [heval]
      have ev := ContinuousLinearMap.map_tsum
        (BoundedContinuousFunction.evalCLM ℝ (Y k x)) (hAsum k)
      -- the mapped family has the usual sequence of partial sums
      have sm : Summable (fun i => A i k (Y k x)) :=
        by
          simpa [Function.comp_def] using
            ((hAsum k).map (BoundedContinuousFunction.evalCLM ℝ (Y k x))
              (BoundedContinuousFunction.evalCLM ℝ (Y k x)).continuous)
      exact sm.hasSum.tendsto_sum_nat
    exact tendsto_finset_sum (Finset.univ : Finset (Fin m))
      (fun k hk' => hk k)
  have hdiff : Tendsto
      (fun q : ℕ => f x - ∑ k : Fin m, (∑ i ∈ Finset.range q, A i k (Y k x)))
      atTop (𝓝 (f x - ∑ k : Fin m, aa k (Y k x))) :=
    tendsto_const_nhds.sub hlimrow
  have hz : f x - ∑ k : Fin m, aa k (Y k x) = 0 := by
    exact tendsto_nhds_unique hdiff (by simpa [telesc] using hrzero)
  have : f x = ∑ k : Fin m, aa k (Y k x) := sub_eq_zero.mp hz
  simpa [Y] using this

end KAS

-- END INLINED FILE: Mathlib/Support/kolmogorov_arnold_superposition_7c7ff433f4/Convergence.lean

-- BEGIN INLINED FILE: Mathlib/Support/kolmogorov_arnold_superposition_7c7ff433f4/CoverReduction.lean

open scoped BigOperators
open Classical

/-!
The covering (combinatorial) part of the superposition construction is rather
separate from the analytic one.  This file records a useful precise interface.
At a level of the construction a layer has finitely many *cells*.  The cells
are small compact subsets of the cube; the image of two different cells in a
single layer, by its inner sum, is disjoint.  A cube point is in cells from at
least `n+1` of the `2*n+1` layers.  No compatibility between different levels
is needed for the elementary ``one step'' estimate.

Keeping the cells (instead of just their centres) in this statement is
important: assigning a constant to their compact images is a continuous
closed-set prescription, so that Tietze fills the gaps.  The lemma below is
often a handy way to use the separating-cover lemma.
-/
namespace KAS

variable {n : ℕ}

/-- The inner sum associated to a row of one-coordinate functions. -/
def innerSum (p : Fin (2*n+1) → Fin n → ℝ → ℝ)
    (k : Fin (2*n+1)) (x : Fin n → ℝ) : ℝ :=
  ∑ l, p k l (x l)

lemma continuous_innerSum (p : Fin (2*n+1) → Fin n → ℝ → ℝ)
    (hp : ∀ k l, Continuous (p k l)) (k : Fin (2*n+1)) :
    Continuous (innerSum p k) := by
  classical
  unfold innerSum
  exact continuous_finset_sum _ (fun i _ =>
    (hp k i).comp (continuous_apply i))

/-- Data of one finite separating cover.  Empty cells are allowed; this makes
padding an indexing family painless.  A nonempty cell comes with all the usual
conditions. -/
structure SeparatingCover (n : ℕ)
    (p : Fin (2*n+1) → Fin n → ℝ → ℝ) (δ : ℝ) where
  /-- same finite index type for all rows; rows may pad by empty cells -/
  N : ℕ
  cell : Fin (2*n+1) → Fin N → Set (Fin n → ℝ)
  cell_compact : ∀ k i, IsCompact (cell k i)
  cell_subset : ∀ k i, cell k i ⊆ Set.Icc (0 : Fin n → ℝ) 1
  cell_small : ∀ k i, ∀ x ∈ cell k i, ∀ z ∈ cell k i,
      dist x z < δ
  many : ∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1,
      n+1 ≤ (Finset.univ.filter (fun k : Fin (2*n+1) =>
        ∃ i : Fin N, x ∈ cell k i)).card
  separate : ∀ (k : Fin (2*n+1)) {i j : Fin N}, i ≠ j →
      Disjoint (innerSum p k '' cell k i) (innerSum p k '' cell k j)

/-- There are arbitrarily fine separating covers for these fixed inner
functions. -/
def HasSeparatingCovers (n : ℕ)
    (p : Fin (2*n+1) → Fin n → ℝ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → Nonempty (SeparatingCover n p δ)

-- Some elementary closed-pasting lemmas used by the reduction.

private lemma compact_image_row
    (p : Fin (2*n+1) → Fin n → ℝ → ℝ)
    (hp : ∀ k l, Continuous (p k l))
    {δ : ℝ} (D : SeparatingCover n p δ)
    (k : Fin (2*n+1)) (i : Fin D.N) :
    IsCompact (innerSum p k '' D.cell k i) := by
  exact (D.cell_compact k i).image (continuous_innerSum p hp k)

/-- A clipped continuous real function, with a symmetric bound. -/
private def symmClip (b t : ℝ) : ℝ := max (-b) (min t b)

private lemma continuous_symmClip {b : ℝ} : Continuous (symmClip b) := by
  unfold symmClip
  fun_prop

private lemma symmClip_bounds {b t : ℝ} (hb : 0 ≤ b) :
    -b ≤ symmClip b t ∧ symmClip b t ≤ b := by
  dsimp [symmClip]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_right _ _)

@[simp] private lemma symmClip_of_mem {b t : ℝ}
    (h1 : -b ≤ t) (h2 : t ≤ b) : symmClip b t = t := by
  unfold symmClip
  rw [min_eq_left h2, max_eq_right h1]

/-- Continuous and globally bounded extension of constants prescribed on the
compact and pairwise disjoint row images.  Empty cells cause no trouble; on a
nonempty image the indicated value is attained everywhere. -/
private lemma row_constants
    (p : Fin (2*n+1) → Fin n → ℝ → ℝ)
    (hp : ∀ k l, Continuous (p k l))
    {δ : ℝ} (D : SeparatingCover n p δ)
    (k : Fin (2*n+1))
    (val : Fin D.N → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hval : ∀ i, |val i| ≤ b) :
    ∃ A : BoundedContinuousFunction ℝ ℝ,
      ‖A‖ ≤ b ∧
      ∀ i, ∀ t ∈ innerSum p k '' D.cell k i, A t = val i := by
  classical
  let I : Fin D.N → Set ℝ := fun i => innerSum p k '' D.cell k i
  have hIc (i : Fin D.N) : IsClosed (I i) :=
    (compact_image_row p hp D k i).isClosed
  have hdis {i j : Fin D.N} (hij : i ≠ j) : Disjoint (I i) (I j) :=
    D.separate k hij
  have huniq {t : ℝ} {i j : Fin D.N} (hi : t ∈ I i) (hj : t ∈ I j) : i = j := by
    by_contra ne
    have hd := Set.disjoint_left.1 (hdis ne) hi hj
    exact False.elim hd
  let S : Set ℝ := ⋃ i : Fin D.N, I i
  have hS : IsClosed S := by
    classical
    have : S = ⋃ i ∈ (Finset.univ : Finset (Fin D.N)), I i := by simp [S]
    rw [this]
    exact isClosed_biUnion_finset I hIc Finset.univ
  let v : ℝ → ℝ := fun t =>
    if h : ∃ i : Fin D.N, t ∈ I i then val (Classical.choose h) else 0
  have hv_one (i : Fin D.N) {t : ℝ} (hi : t ∈ I i) : v t = val i := by
    dsimp [v]
    have h : ∃ j : Fin D.N, t ∈ I j := ⟨i, hi⟩
    simp only [dif_pos h]
    have heq : Classical.choose h = i := huniq (Classical.choose_spec h) hi
    simp [heq]
  have hvI (i : Fin D.N) : ContinuousOn v (I i) := by
    have heq : Set.EqOn v (fun _ : ℝ => val i) (I i) := by
      intro t ht
      exact hv_one i ht
    exact continuousOn_const.congr heq
  -- easier prove with congr
  have hvS : ContinuousOn v S := by
    classical
    have : S = ⋃ i ∈ (Finset.univ : Finset (Fin D.N)), I i := by simp [S]
    rw [this]
    exact continuousOn_biUnion_finset I hIc Finset.univ v (by
      intro i hi; exact hvI i)
  let vv : C(S, ℝ) :=
    ⟨(fun z : S => v z), (continuousOn_iff_continuous_restrict.mp hvS)⟩
  obtain ⟨GG, hGG⟩ := ContinuousMap.exists_restrict_eq hS vv
  let w : ℝ → ℝ := fun t => symmClip b (GG t)
  have hw : Continuous w := continuous_symmClip.comp GG.continuous
  have hwb (t : ℝ) : |w t| ≤ b := by
    have hh := symmClip_bounds (t := GG t) hb
    simpa [w, abs_le] using hh
  have hwo (i : Fin D.N) {t : ℝ} (ht : t ∈ I i) : w t = val i := by
    have h_eq : GG t = v t := by
      have e := DFunLike.congr_fun hGG (⟨t, (Set.mem_iUnion.mpr ⟨i, ht⟩ : t ∈ S)⟩ : S)
      exact e
    have hv := hv_one i ht
    have hle := abs_le.mp (hval i)
    dsimp [w]
    rw [h_eq, hv]
    exact symmClip_of_mem hle.1 hle.2
  let A : BoundedContinuousFunction ℝ ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨w, hw⟩ (2*b)
      (by
        intro x y
        -- the easy diameter bound is twice the pointwise bound
        have hx := hwb x
        have hy := hwb y
        calc
          dist (w x) (w y) = |w x - w y| := by rw [Real.dist_eq]
          _ ≤ |w x| + |w y| := abs_sub _ _
          _ ≤ b + b := add_le_add hx hy
          _ = 2*b := by ring)
  refine ⟨A, ?_, ?_⟩
  · -- norm estimate via pointwise bounds
    refine (BoundedContinuousFunction.norm_le hb).2 ?_
    intro t
    simpa [A, Real.norm_eq_abs] using hwb t
  · intro i t ht
    change w t = val i
    exact hwo i ht

-- arithmetic/cardinality facts for the `n+1`-out-of-`2n+1` counting estimate
private lemma bad_card_le {n : ℕ} {u : Finset (Fin (2*n+1))}
    (h : n+1 ≤ u.card) :
    (uᶜ : Finset (Fin (2*n+1))).card ≤ n := by
  classical
  rw [Finset.card_compl]
  simp only [Fintype.card_fin]
  omega

/-- The analytic one-step estimate from separating covers.  Notice that the
covering property is uniform in `r` whereas the row constants are chosen for
`r`; this is exactly what is needed for a contraction iteration with fixed
inner functions. -/
theorem cover_step
    {n : ℕ}
    (p : Fin (2*n+1) → Fin n → ℝ → ℝ)
    (hp : ∀ k l, Continuous (p k l))
    (hcover : HasSeparatingCovers n p) :
    ∀ (r : (Fin n → ℝ) → ℝ),
      ContinuousOn r (Set.Icc (0 : Fin n → ℝ) 1) →
      (∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1, |r x| ≤ (1:ℝ)) →
      ∃ A : Fin (2*n+1) → BoundedContinuousFunction ℝ ℝ,
        (∀ k, ‖A k‖ ≤ (1:ℝ)) ∧
        ∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1,
          |r x - ∑ k, A k (innerSum p k x)|
            ≤ 1 - 1 / (2 * (2*(n:ℝ)+1)) := by
  classical
  let M : ℝ := (2*(n:ℝ)+1)
  have hM : 0 < M := by dsimp [M]; have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg _; linarith
  intro r hr hb
  have huc : UniformContinuousOn r (Set.Icc (0 : Fin n → ℝ) 1) :=
    (isCompact_Icc.uniformContinuousOn_of_continuous hr)
  let η : ℝ := 1 / (2*M)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨d, hd, hmod⟩ := (Metric.uniformContinuousOn_iff.mp huc) η hη
  obtain ⟨D⟩ := hcover d hd
  -- a centre in each (nonempty) cell; for empty cells the value is chosen as zero
  let c (k : Fin (2*n+1)) (i : Fin D.N) : ℝ :=
    if h : (D.cell k i).Nonempty then r (Classical.choose h) / M else 0
  have hc (k : Fin (2*n+1)) (i : Fin D.N) : |c k i| ≤ 1/M := by
    dsimp [c]
    split_ifs with hne
    · have hm := hb (Classical.choose hne) (D.cell_subset k i (Classical.choose_spec hne))
      have heq : |r (Classical.choose hne) / M| = |r (Classical.choose hne)| / M := by
        rw [abs_div, abs_of_pos hM]
      rw [heq]
      exact (div_le_div_of_nonneg_right hm (le_of_lt hM))
    · have : 0 ≤ (1/M : ℝ) := by positivity
      simpa using this
  choose A hA_norm hA using (fun k : Fin (2*n+1) =>
    row_constants p hp D k (c k) (1/M) (by positivity : (0:ℝ) ≤ 1/M) (hc k))
  refine ⟨A, ?_, ?_⟩
  · intro k
    exact (hA_norm k).trans (by
      have : (1/M:ℝ) ≤ 1 := by
        have : (1:ℝ) ≤ M := by dsimp [M]; have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg _; linarith
        exact (div_le_one hM).2 this
      simpa using this)
  intro x hx
  let good : Finset (Fin (2*n+1)) :=
    Finset.univ.filter (fun k : Fin (2*n+1) => ∃ i : Fin D.N, x ∈ D.cell k i)
  have hgood : n+1 ≤ good.card := D.many x hx
  have hbad : (goodᶜ : Finset (Fin (2*n+1))).card ≤ n := bad_card_le hgood
  -- each summand is compared with `r x / M`
  have good_one (k : Fin (2*n+1)) (hk : k ∈ good) :
      |r x / M - A k (innerSum p k x)| ≤ η / M := by
    have hex : ∃ i : Fin D.N, x ∈ D.cell k i := (Finset.mem_filter.mp hk).2
    obtain ⟨i, hi⟩ := hex
    have hne : (D.cell k i).Nonempty := ⟨x, hi⟩
    have hcentre : Classical.choose hne ∈ D.cell k i := Classical.choose_spec hne
    have hsmall : dist x (Classical.choose hne) < d :=
      D.cell_small k i x hi (Classical.choose hne) hcentre
    have hclose : dist (r x) (r (Classical.choose hne)) < η :=
      hmod x hx _ (D.cell_subset k i hcentre) hsmall
    have himg : innerSum p k x ∈ innerSum p k '' D.cell k i :=
      ⟨x, hi, rfl⟩
    have hAeq : A k (innerSum p k x) = c k i := hA k i _ himg
    have hceq : c k i = r (Classical.choose hne) / M := by
      dsimp [c]
      simp [hne]
    rw [hAeq, hceq]
    have : |r x - r (Classical.choose hne)| < η := by
      simpa [Real.dist_eq] using hclose
    have hcalc : |r x / M - r (Classical.choose hne) / M|
          = |r x - r (Classical.choose hne)| / M := by
      rw [← sub_div]
      rw [abs_div, abs_of_pos hM]
    rw [hcalc]
    exact (le_of_lt ( (div_lt_div_iff_of_pos_right hM).2 this))
  have bad_one (k : Fin (2*n+1)) :
      |r x / M - A k (innerSum p k x)| ≤ 2 / M := by
    have hrx : |r x| ≤ 1 := hb x hx
    have ha : |A k (innerSum p k x)| ≤ 1/M := by
      simpa [Real.norm_eq_abs] using
        (BoundedContinuousFunction.norm_coe_le_norm (A k) (innerSum p k x) |>.trans (hA_norm k))
    calc
      |r x / M - A k (innerSum p k x)|
          ≤ |r x / M| + |A k (innerSum p k x)| := abs_sub _ _
      _ ≤ (1/M) + (1/M) := by
        have hdiv : |r x / M| = |r x| / M := by rw [abs_div, abs_of_pos hM]
        rw [hdiv]
        exact add_le_add (div_le_div_of_nonneg_right hrx (le_of_lt hM)) ha
      _ = 2 / M := by ring
  have hsplit :
      ∑ k : Fin (2*n+1), (r x / M - A k (innerSum p k x))
        = r x - ∑ k, A k (innerSum p k x) := by
    rw [Finset.sum_sub_distrib]
    have hcard : (Finset.univ : Finset (Fin (2*n+1))).card = 2*n+1 := by simp
    have heq : (∑ _k : Fin (2*n+1), r x / M) = r x := by
      simp [M]
      field_simp
      <;> ring
    -- field_simp may have nonzero? keep explicit below
    rw [heq]
  -- split the absolute sum into good and bad rows
  calc
    |r x - ∑ k, A k (innerSum p k x)|
        = |∑ k : Fin (2*n+1), (r x / M - A k (innerSum p k x))| := by rw [hsplit]
    _ ≤ ∑ k : Fin (2*n+1), |r x / M - A k (innerSum p k x)| := by
      simpa using (Finset.abs_sum_le_sum_abs
        (fun k : Fin (2*n+1) => r x / M - A k (innerSum p k x)) Finset.univ)
    _ = (∑ k ∈ good, |r x / M - A k (innerSum p k x)|)
          + (∑ k ∈ goodᶜ, |r x / M - A k (innerSum p k x)|) := by
      -- univ is the disjoint union of `good` and its complement
      have hdj : Disjoint good (goodᶜ : Finset (Fin (2*n+1))) := by
        rw [Finset.compl_eq_univ_sdiff]
        exact Finset.disjoint_sdiff
      have hu : good ∪ (goodᶜ : Finset (Fin (2*n+1))) = Finset.univ := by
        rw [Finset.compl_eq_univ_sdiff, Finset.union_sdiff_self_eq_union]
        simp
      rw [← hu, Finset.sum_union hdj]
    _ ≤ (good.card : ℝ) * (η / M) + ((goodᶜ : Finset (Fin (2*n+1))).card : ℝ) * (2 / M) := by
      gcongr
      · simpa [nsmul_eq_mul] using
          (Finset.sum_le_card_nsmul good
            (fun k : Fin (2*n+1) => |r x / M - A k (innerSum p k x)|)
            (η / M) (by
              intro k hk; exact good_one k hk))
      · simpa [nsmul_eq_mul] using
          (Finset.sum_le_card_nsmul (goodᶜ : Finset (Fin (2*n+1)))
            (fun k : Fin (2*n+1) => |r x / M - A k (innerSum p k x)|)
            (2 / M) (by
              intro k hk; exact bad_one k))
    _ ≤ (2*(n:ℝ)+1) * (η / M) + (n:ℝ) * (2 / M) := by
      have hgcard : (good.card : ℝ) ≤ 2*(n:ℝ)+1 := by
        have : good.card ≤ 2*n+1 := by
          simpa using (Finset.card_le_card (Finset.subset_univ good))
        exact_mod_cast this
      have hbcard : (((goodᶜ : Finset (Fin (2*n+1))).card : ℕ) : ℝ) ≤ (n:ℝ) := by
        exact_mod_cast hbad
      have hcoef1 : 0 ≤ η / M := by positivity
      have hcoef2 : 0 ≤ (2:ℝ) / M := by positivity
      exact add_le_add
        (mul_le_mul_of_nonneg_right hgcard hcoef1)
        (mul_le_mul_of_nonneg_right hbcard hcoef2)
    _ = 1 - 1 / (2 * (2*(n:ℝ)+1)) := by
      dsimp [M, η]
      field_simp
      <;> ring

end KAS

-- END INLINED FILE: Mathlib/Support/kolmogorov_arnold_superposition_7c7ff433f4/CoverReduction.lean

-- BEGIN INLINED FILE: Mathlib/Support/kolmogorov_arnold_superposition_7c7ff433f4/Scaling.lean
open scoped BigOperators
namespace KAS
open Classical
/-- Rescaling reduces the approximation step to norm at most one. -/
theorem normalize_step {n m : ℕ} (θ : ℝ)
    (p : Fin m → Fin n → ℝ → ℝ)
    (u : ∀ (r : (Fin n → ℝ) → ℝ),
      ContinuousOn r (Set.Icc (0 : Fin n → ℝ) 1) →
      (∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1, |r x| ≤ (1:ℝ)) →
      ∃ A : Fin m → BoundedContinuousFunction ℝ ℝ,
        (∀ k, ‖A k‖ ≤ (1:ℝ)) ∧
        ∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1,
          |r x - ∑ k, A k (∑ l, p k l (x l))| ≤ θ) :
    ∀ (r : (Fin n → ℝ) → ℝ) (T : ℝ),
      0 < T → ContinuousOn r (Set.Icc (0 : Fin n → ℝ) 1) →
      (∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1, |r x| ≤ T) →
      ∃ A : Fin m → BoundedContinuousFunction ℝ ℝ,
        (∀ k, ‖A k‖ ≤ (1:ℝ) * T) ∧
        ∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1,
          |r x - ∑ k, A k (∑ l, p k l (x l))| ≤ θ*T := by
  classical
  intro r T hT hc hb
  let r' : (Fin n → ℝ) → ℝ := fun x => (T⁻¹) * r x
  have hc' : ContinuousOn r' (Set.Icc (0 : Fin n → ℝ) 1) :=
    continuousOn_const.mul hc
  have hb' : ∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1, |r' x| ≤ (1:ℝ) := by
    intro x hx
    dsimp [r']
    rw [abs_mul, abs_of_pos (inv_pos.mpr hT)]
    exact (inv_mul_le_one₀ hT).2 (hb x hx)
  obtain ⟨b,hbnorm,herr⟩ := u r' hc' hb'
  let A : Fin m → BoundedContinuousFunction ℝ ℝ := fun k => T • b k
  refine ⟨A, ?_, ?_⟩
  · intro k
    dsimp [A]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hT]
    have := hbnorm k
    nlinarith [norm_nonneg (b k)]
  · intro x hx
    have he := herr x hx
    dsimp [r'] at he
    have hsum : (∑ k, A k (∑ l, p k l (x l))) =
        T * (∑ k, b k (∑ l, p k l (x l))) := by
      dsimp [A]
      simp [Finset.mul_sum]
    rw [hsum]
    have hi : T⁻¹ * r x - ∑ k, b k (∑ l, p k l (x l)) =
        T⁻¹ * (r x - T * (∑ k, b k (∑ l, p k l (x l)))) := by
      field_simp
      <;> ring
    rw [hi, abs_mul, abs_of_pos (inv_pos.mpr hT)] at he
    have := (mul_le_mul_of_nonneg_left he (le_of_lt hT))
    field_simp at this
    simpa [mul_comm] using this
end KAS

-- END INLINED FILE: Mathlib/Support/kolmogorov_arnold_superposition_7c7ff433f4/Scaling.lean

-- BEGIN INLINED FILE: Mathlib/Support/kolmogorov_arnold_superposition_7c7ff433f4/Strands.lean

open scoped BigOperators
open Classical
namespace KAS

/-- The box cut out by the one-dimensional strands of a row.  Intersecting the
cube here, rather than at the end of the proof, both deals with the two end
points and gives compactness for free. -/
def strandBox (n L : ℕ)
    (s : Fin (2*n+1) → Fin L → Set ℝ)
    (k : Fin (2*n+1)) (a : Fin n → Fin L) : Set (Fin n → ℝ) :=
  {x | x ∈ Set.Icc (0 : Fin n → ℝ) 1 ∧ ∀ l, x l ∈ s k (a l)}

lemma mem_strandBox {n L : ℕ}
    {s : Fin (2*n+1) → Fin L → Set ℝ}
    {k : Fin (2*n+1)} {a : Fin n → Fin L} {x : Fin n → ℝ} :
    x ∈ strandBox n L s k a ↔
      x ∈ Set.Icc (0 : Fin n → ℝ) 1 ∧ ∀ l, x l ∈ s k (a l) := Iff.rfl

lemma strandBox_subset {n L : ℕ}
    {s : Fin (2*n+1) → Fin L → Set ℝ}
    (k : Fin (2*n+1)) (a : Fin n → Fin L) :
    strandBox n L s k a ⊆ Set.Icc (0 : Fin n → ℝ) 1 := by
  intro x hx; exact hx.1

lemma strandBox_compact {n L : ℕ}
    (s : Fin (2*n+1) → Fin L → Set ℝ)
    (hs : ∀ k i, IsClosed (s k i))
    (k : Fin (2*n+1)) (a : Fin n → Fin L) :
    IsCompact (strandBox n L s k a) := by
  let T : Set (Fin n → ℝ) := ⋂ l : Fin n, (fun x : Fin n → ℝ => x l) ⁻¹' s k (a l)
  have hT : IsClosed T := by
    dsimp [T]
    exact isClosed_iInter (fun l => (hs k (a l)).preimage (continuous_apply l))
  have heq : strandBox n L s k a = Set.Icc (0 : Fin n → ℝ) 1 ∩ T := by
    ext x
    simp [strandBox, T]
  rw [heq]
  exact isCompact_Icc.inter_right hT

lemma strandBox_small {n L : ℕ} {d : ℝ} (hd : 0 < d)
    (s : Fin (2*n+1) → Fin L → Set ℝ)
    (hs : ∀ k i, ∀ t ∈ s k i, ∀ u ∈ s k i, dist t u < d)
    (k : Fin (2*n+1)) (a : Fin n → Fin L)
    {x z : Fin n → ℝ}
    (hx : x ∈ strandBox n L s k a)
    (hz : z ∈ strandBox n L s k a) : dist x z < d := by
  rw [dist_pi_lt_iff hd]
  intro l
  exact hs k (a l) (x l) (hx.2 l) (z l) (hz.2 l)

/-- One level presented one dimension at a time.  For a real coordinate at
most one row can miss a strand.  The last field is the actual arithmetic
separation of box images; it is the part arranged by the little perturbations
in the inner functions. -/
structure StrandLevel (n : ℕ)
    (p : Fin (2*n+1) → Fin n → ℝ → ℝ) (d : ℝ) where
  L : ℕ
  seg : Fin (2*n+1) → Fin L → Set ℝ
  seg_closed : ∀ k i, IsClosed (seg k i)
  seg_small : ∀ k i, ∀ t ∈ seg k i, ∀ u ∈ seg k i, dist t u < d
  misses : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    (Finset.univ.filter (fun k : Fin (2*n+1) =>
      ¬ ∃ i : Fin L, t ∈ seg k i)).card ≤ 1
  separated : ∀ (k : Fin (2*n+1))
      {a b : Fin n → Fin L}, a ≠ b →
      Disjoint (innerSum p k '' strandBox n L seg k a)
               (innerSum p k '' strandBox n L seg k b)

def HasStrandLevels (n : ℕ)
    (p : Fin (2*n+1) → Fin n → ℝ → ℝ) : Prop :=
  ∀ d : ℝ, 0 < d → Nonempty (StrandLevel n p d)

private lemma boxes_many {n : ℕ}
    (p : Fin (2*n+1) → Fin n → ℝ → ℝ)
    {d : ℝ} (E : StrandLevel n p d)
    (x : Fin n → ℝ) (hx : x ∈ Set.Icc (0 : Fin n → ℝ) 1) :
    n+1 ≤ (Finset.univ.filter (fun k : Fin (2*n+1) =>
        ∃ a : Fin n → Fin E.L, x ∈ strandBox n E.L E.seg k a)).card := by
  classical
  -- missed rows of a coordinate
  let bad (l : Fin n) : Finset (Fin (2*n+1)) :=
    Finset.univ.filter (fun k : Fin (2*n+1) =>
      ¬ ∃ i : Fin E.L, x l ∈ E.seg k i)
  have hbad (l : Fin n) : (bad l).card ≤ 1 := by
    dsimp [bad]
    exact E.misses (x l) ⟨hx.1 l, hx.2 l⟩
  let U : Finset (Fin (2*n+1)) :=
    Finset.univ.biUnion bad
  have hU : U.card ≤ n := by
    calc
      U.card ≤ ∑ l : Fin n, (bad l).card := by
        dsimp [U]
        simpa using (Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin n))) (t := bad))
      _ ≤ ∑ _l : Fin n, 1 := by
        exact Finset.sum_le_sum (fun l hl => hbad l)
      _ = n := by simp
  let G : Finset (Fin (2*n+1)) :=
       Finset.univ.filter (fun k : Fin (2*n+1) =>
        ∃ a : Fin n → Fin E.L, x ∈ strandBox n E.L E.seg k a)
  have hcomp : (Gᶜ : Finset (Fin (2*n+1))) ⊆ U := by
    intro k hk
    have hk' : ¬ ∃ a : Fin n → Fin E.L, x ∈ strandBox n E.L E.seg k a := by
      have := (Finset.mem_compl.mp hk)
      have : k ∉ G := this
      simpa [G] using this
    have hex : ∃ l : Fin n, ¬ ∃ i : Fin E.L, x l ∈ E.seg k i := by
      classical
      by_contra h
      push_neg at h
      choose a ha using h
      apply hk'
      refine ⟨a, ?_⟩
      exact ⟨hx, ha⟩
    obtain ⟨l, hl⟩ := hex
    have hbmem : k ∈ bad l := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩
    exact (Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, hbmem⟩)
  have hc : (Gᶜ : Finset (Fin (2*n+1))).card ≤ n :=
    (Finset.card_le_card hcomp).trans hU
  have htot : G.card + (Gᶜ : Finset (Fin (2*n+1))).card = 2*n+1 := by
    have hle : G.card ≤ 2*n+1 := by
      simpa using (Finset.card_le_card (Finset.subset_univ G))
    rw [Finset.card_compl]
    simp only [Fintype.card_fin]
    omega
  change n+1 ≤ G.card
  omega

/-- Variant with the positivity needed by `dist_pi_lt_iff`; it keeps the
slightly smaller definition of `StrandLevel`. -/
noncomputable def strandLevel_toCover_of_pos {n : ℕ}
    {p : Fin (2*n+1) → Fin n → ℝ → ℝ} {d : ℝ}
    (hd : 0 < d) (E : StrandLevel n p d) : SeparatingCover n p d := by
  classical
  let e := Fintype.equivFin (Fin n → Fin E.L)
  let get (i : Fin (Fintype.card (Fin n → Fin E.L))) : Fin n → Fin E.L := e.symm i
  let C (k : Fin (2*n+1)) (i : Fin (Fintype.card (Fin n → Fin E.L))) :
      Set (Fin n → ℝ) := strandBox n E.L E.seg k (get i)
  refine
    { N := Fintype.card (Fin n → Fin E.L)
      cell := C
      cell_compact := ?_
      cell_subset := ?_
      cell_small := ?_
      many := ?_
      separate := ?_ }
  · intro k i; exact strandBox_compact E.seg E.seg_closed k (get i)
  · intro k i; exact strandBox_subset k (get i)
  · intro k i x hx z hz; exact strandBox_small hd E.seg E.seg_small k (get i) hx hz
  · intro x hx
    have hb := boxes_many p E x hx
    have hiff (k : Fin (2*n+1)) :
        (∃ i : Fin (Fintype.card (Fin n → Fin E.L)), x ∈ C k i) ↔
        (∃ a : Fin n → Fin E.L, x ∈ strandBox n E.L E.seg k a) := by
      constructor
      · rintro ⟨i, hi⟩; exact ⟨get i, hi⟩
      · rintro ⟨a, ha⟩; exact ⟨e a, by simpa [C, get, e] using ha⟩
    -- extensionality of the filters is more reliable than simp with an iff lemma
    have filt :
       (Finset.univ.filter (fun k : Fin (2*n+1) => ∃ i, x ∈ C k i)) =
       (Finset.univ.filter (fun k : Fin (2*n+1) => ∃ a : Fin n → Fin E.L,
          x ∈ strandBox n E.L E.seg k a)) := by
      ext k
      simp [hiff]
    simpa [filt] using hb
  · intro k i j hij
    have hne : get i ≠ get j := by
      intro hh
      exact hij (e.symm.injective hh)
    exact E.separated k hne

lemma strand_to_covers {n : ℕ}
    {p : Fin (2*n+1) → Fin n → ℝ → ℝ}
    (h : HasStrandLevels n p) : HasSeparatingCovers n p := by
  intro d hd
  obtain ⟨E⟩ := h d hd
  exact ⟨strandLevel_toCover_of_pos hd E⟩

end KAS

-- END INLINED FILE: Mathlib/Support/kolmogorov_arnold_superposition_7c7ff433f4/Strands.lean

-- BEGIN INLINED FILE: Mathlib/Support/kolmogorov_arnold_superposition_7c7ff433f4/Staggered.lean

open scoped BigOperators
open Classical
namespace KAS

private def rows (n : ℕ) : ℝ := (2*(n:ℝ)+1)

private lemma rows_pos (n : ℕ) : 0 < rows n := by
  dsimp [rows]; have : 0 ≤ (n:ℝ) := Nat.cast_nonneg _; linarith

/-- Equally spaced closed strands.  Row `0` has its little gap just before an
integer; row `k+1` has it in the `k`-th `1/(2n+1)` slot after an integer.
Indices `-1,...,q` suffice on the unit interval, hence the `q+2`. -/
def staggerSeg (n q : ℕ) (k : Fin (2*n+1))
    (a : Fin (q+2)) : Set ℝ :=
  Set.Icc
    (((a.val:ℝ)-1 + (k.val:ℝ) / rows n) / (q:ℝ))
    (((a.val:ℝ)-1 + ((k.val:ℝ)+2*(n:ℝ)) / rows n) / (q:ℝ))

lemma staggerSeg_closed (n q : ℕ) (k : Fin (2*n+1)) (a : Fin (q+2)) :
    IsClosed (staggerSeg n q k a) := isClosed_Icc

lemma staggerSeg_disjoint {n q : ℕ} (hq : 0 < q)
    (k : Fin (2*n+1)) {a b : Fin (q+2)} (hab : a ≠ b) :
    Disjoint (staggerSeg n q k a) (staggerSeg n q k b) := by
  have hm : 0 < rows n := rows_pos n
  have hQ : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hw : (2*(n:ℝ)) / rows n < 1 := by
    apply (div_lt_iff₀ hm).2
    dsimp [rows]
    linarith
  apply Set.disjoint_left.mpr
  intro t ha hb
  change _ ≤ t ∧ t ≤ _ at ha
  change _ ≤ t ∧ t ≤ _ at hb
  have hcases : a.val < b.val ∨ b.val < a.val := by
    rcases lt_or_gt_of_ne (fun h => hab (Fin.ext h)) with h|h
    · exact Or.inl h
    · exact Or.inr h
  rcases hcases with hlt | hlt
  · have hgap :
        (((a.val:ℝ)-1 + ((k.val:ℝ)+2*(n:ℝ)) / rows n) / (q:ℝ)) <
        (((b.val:ℝ)-1 + (k.val:ℝ) / rows n) / (q:ℝ)) := by
        apply (div_lt_div_iff_of_pos_right hQ).2
        have hi : (a.val:ℝ) + 1 ≤ (b.val:ℝ) := by exact_mod_cast hlt
        have hsplit : (((k.val:ℝ)+2*(n:ℝ)) / rows n) =
            (k.val:ℝ) / rows n + (2*(n:ℝ)) / rows n := by ring
        rw [hsplit]
        linarith
    linarith
  · have hgap :
        (((b.val:ℝ)-1 + ((k.val:ℝ)+2*(n:ℝ)) / rows n) / (q:ℝ)) <
        (((a.val:ℝ)-1 + (k.val:ℝ) / rows n) / (q:ℝ)) := by
        apply (div_lt_div_iff_of_pos_right hQ).2
        have hi : (b.val:ℝ) + 1 ≤ (a.val:ℝ) := by exact_mod_cast hlt
        have hsplit : (((k.val:ℝ)+2*(n:ℝ)) / rows n) =
            (k.val:ℝ) / rows n + (2*(n:ℝ)) / rows n := by ring
        rw [hsplit]
        linarith
    linarith

/-- Every staggered segment has a point (its left endpoint). -/
lemma staggerSeg_nonempty {n q : ℕ} (hq : 0 < q)
    (k : Fin (2*n+1)) (a : Fin (q+2)) : (staggerSeg n q k a).Nonempty := by
  have hm : 0 < rows n := rows_pos n
  have hQ : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  refine ⟨(((a.val:ℝ)-1 + (k.val:ℝ) / rows n) / (q:ℝ)), ?_⟩
  change _ ≤ _ ∧ _ ≤ _
  refine ⟨le_rfl, ?_⟩
  apply (div_le_div_iff_of_pos_right hQ).2
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hkn : (k.val:ℝ) ≤ (k.val:ℝ) + 2*(n:ℝ) := by linarith
  have hf : (k.val:ℝ) / rows n ≤ ((k.val:ℝ)+2*(n:ℝ)) / rows n :=
    (div_le_div_iff_of_pos_right hm).2 hkn
  linarith

/-- All segments live in a fixed compact interval.  This is useful for doing
uniform approximations of continuous one-variable functions; no global
uniform-continuity hypothesis is needed. -/
lemma staggerSeg_bounds {n q : ℕ} (hq : 0 < q)
    (k : Fin (2*n+1)) (a : Fin (q+2)) :
    staggerSeg n q k a ⊆ Set.Icc (-1 : ℝ) 3 := by
  intro t ht
  change _ ≤ t ∧ t ≤ _ at ht
  have hm : 0 < rows n := rows_pos n
  have hQ : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hqone : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have haka0 : 0 ≤ (a.val:ℝ) := Nat.cast_nonneg _
  have haTopNat : a.val ≤ q+1 := by omega
  have haTop : (a.val:ℝ) ≤ (q:ℝ)+1 := by exact_mod_cast haTopNat
  have hk0 : 0 ≤ (k.val:ℝ) := Nat.cast_nonneg _
  have hkTopNat : k.val ≤ 2*n := by omega
  have hkTop : (k.val:ℝ) ≤ 2*(n:ℝ) := by exact_mod_cast hkTopNat
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hfrac0 : 0 ≤ (k.val:ℝ) / rows n := le_of_lt hm |> (fun _ => by positivity)
  have hfrac2_non : 0 ≤ ((k.val:ℝ)+2*(n:ℝ)) / rows n := by positivity
  have hfrac2_lt : ((k.val:ℝ)+2*(n:ℝ)) / rows n < 2 := by
    apply (div_lt_iff₀ hm).2
    dsimp [rows]
    linarith
  constructor
  · -- lower endpoint at least `-1`
    have hlower : (-1:ℝ) ≤ (((a.val:ℝ)-1 + (k.val:ℝ)/rows n) / (q:ℝ)) :=
      (le_div_iff₀ hQ).2 (by
        have : (-(q:ℝ)) ≤ (a.val:ℝ)-1 + (k.val:ℝ)/rows n := by linarith
        simpa using this)
    exact hlower.trans ht.1
  · have hupper : (((a.val:ℝ)-1 + ((k.val:ℝ)+2*(n:ℝ))/rows n) / (q:ℝ)) < 3 := by
      apply (div_lt_iff₀ hQ).2
      -- the numerator is strictly smaller than q+2, hence below 3q
      have : (a.val:ℝ)-1 + ((k.val:ℝ)+2*(n:ℝ))/rows n < (q:ℝ)+2 := by linarith
      nlinarith
    exact le_of_lt (lt_of_le_of_lt ht.2 hupper)

lemma staggerSeg_small {n q : ℕ} (hq : 0 < q) {d : ℝ}
    (hd : (1:ℝ)/(q:ℝ) < d) (k : Fin (2*n+1)) (a : Fin (q+2)) :
    ∀ t ∈ staggerSeg n q k a, ∀ u ∈ staggerSeg n q k a, dist t u < d := by
  intro t ht u hu
  have hQ : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hm : 0 < rows n := rows_pos n
  have hwidth :
      (((a.val:ℝ)-1 + ((k.val:ℝ)+2*(n:ℝ)) / rows n) / (q:ℝ)) -
      (((a.val:ℝ)-1 + (k.val:ℝ) / rows n) / (q:ℝ))
        < (1:ℝ)/(q:ℝ) := by
    have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
    dsimp [rows]
    have hklt : (k.val:ℝ) < 2*(n:ℝ)+1 := by
      exact_mod_cast k.isLt
    -- width is actually `2n/(2n+1)/q`
    have hproper : 2*(n:ℝ) < 2*(n:ℝ)+1 := by linarith
    field_simp
    -- denominators positive; `field_simp` clears both
    nlinarith
  have ht' := ht
  change _ ≤ t ∧ t ≤ _ at ht'
  have hu' := hu
  change _ ≤ u ∧ u ≤ _ at hu'
  rw [Real.dist_eq]
  rw [abs_lt]
  constructor
  · have : t - u > -(1/(q:ℝ)) := by linarith
    linarith
  · have : t - u < (1/(q:ℝ)) := by linarith
    linarith

-- choose the interval immediately following the integer `z`
private lemma floor_index {q : ℕ} (hq : 0 < q)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    let z : ℤ := ⌊(q:ℝ)*t⌋
    0 ≤ z ∧ z.toNat ≤ q := by
  dsimp
  have hQ : (0:ℝ) ≤ (q:ℝ) := by exact_mod_cast (Nat.zero_le q)
  have hnon : (0:ℝ) ≤ (q:ℝ)*t := mul_nonneg hQ ht.1
  have hz0 : (0:ℤ) ≤ ⌊(q:ℝ)*t⌋ := (Int.floor_nonneg.mpr hnon)
  refine ⟨hz0, ?_⟩
  have hupp : (q:ℝ)*t < (q:ℝ)+1 := by
    have h : (q:ℝ)*t ≤ (q:ℝ) := by
      have hqR : (0:ℝ) ≤ (q:ℝ) := hQ
      nlinarith [ht.2]
    linarith
  have hzlt : ⌊(q:ℝ)*t⌋ < (q:ℤ)+1 :=
    (Int.floor_lt.mpr (by
      exact_mod_cast hupp))
  have hzle : ⌊(q:ℝ)*t⌋ ≤ (q:ℤ) := by omega
  have : (⌊(q:ℝ)*t⌋).toNat ≤ q := (Int.toNat_le.mpr hzle)
  exact this

private lemma floor_remainder {q : ℕ} (t : ℝ) :
    let z : ℝ := (⌊(q:ℝ)*t⌋ : ℤ)
    0 ≤ (q:ℝ)*t - z ∧ (q:ℝ)*t - z < 1 := by
  dsimp
  constructor
  · change 0 ≤ (q:ℝ)*t - (↑⌊(q:ℝ)*t⌋ : ℝ)
    exact sub_nonneg.mpr (Int.floor_le _)
  · change (q:ℝ)*t - (↑⌊(q:ℝ)*t⌋ : ℝ) < 1
    linarith [Int.lt_floor_add_one ((q:ℝ)*t)]

/-- If a coordinate is not in a strand of row zero, its remainder lies in the
last little slot. -/
private lemma miss_zero {n q : ℕ} (hq : 0 < q)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hmiss : ¬ ∃ a : Fin (q+2), t ∈ staggerSeg n q (⟨0, by omega⟩ : Fin (2*n+1)) a) :
    let z : ℝ := (⌊(q:ℝ)*t⌋ : ℤ)
    2*(n:ℝ) / rows n < (q:ℝ)*t - z := by
  dsimp
  let zz : ℤ := ⌊(q:ℝ)*t⌋
  change 2*(n:ℝ) / rows n < (q:ℝ)*t - (zz:ℝ)
  have hz := floor_index hq ht
  change 0 ≤ zz ∧ zz.toNat ≤ q at hz
  let a : Fin (q+2) := ⟨zz.toNat + 1, by omega⟩
  have hzcast : (zz.toNat : ℝ) = (zz : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg hz.1)
  have hQ : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have rem := floor_remainder (q := q) t
  change 0 ≤ (q:ℝ)*t - (zz:ℝ) ∧ (q:ℝ)*t - (zz:ℝ) < 1 at rem
  have hnmem : t ∉ staggerSeg n q (⟨0, by omega⟩ : Fin (2*n+1)) a := by
    intro ha; exact hmiss ⟨a, ha⟩
  -- the left endpoint is the integer `zz`; failure is therefore to its right
  have hleft :
      (((a.val:ℝ)-1 + (0:ℝ)/rows n)/(q:ℝ)) ≤ t := by
    dsimp [a]
    norm_num
    -- simp of casts
    push_cast
    rw [hzcast]
    apply (div_le_iff₀ hQ).2
    linarith
  have hrightfail : t >
      (((a.val:ℝ)-1 + ((0:ℝ)+2*(n:ℝ))/rows n)/(q:ℝ)) := by
    have hnot : ¬ ( (((a.val:ℝ)-1 + (0:ℝ)/rows n)/(q:ℝ)) ≤ t ∧
        t ≤ (((a.val:ℝ)-1 + ((0:ℝ)+2*(n:ℝ))/rows n)/(q:ℝ))) := by
      change ¬ (_ ≤ t ∧ t ≤ _) at hnmem
      simpa using hnmem
    have : ¬ t ≤ (((a.val:ℝ)-1 + ((0:ℝ)+2*(n:ℝ))/rows n)/(q:ℝ)) :=
      fun hle => hnot ⟨hleft, hle⟩
    linarith
  dsimp [a] at hrightfail
  norm_num at hrightfail
  push_cast at hrightfail
  rw [hzcast] at hrightfail
  have := (div_lt_iff₀ hQ).1 hrightfail
  linarith

private lemma miss_pos {n q : ℕ} (hq : 0 < q)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (k : Fin (2*n+1)) (hk : 0 < k.val)
    (hmiss : ¬ ∃ a : Fin (q+2), t ∈ staggerSeg n q k a) :
    let z : ℝ := (⌊(q:ℝ)*t⌋ : ℤ)
    ((k.val:ℝ)-1) / rows n < (q:ℝ)*t - z ∧
      (q:ℝ)*t - z < (k.val:ℝ) / rows n := by
  dsimp
  let zz : ℤ := ⌊(q:ℝ)*t⌋
  change ((k.val:ℝ)-1) / rows n < (q:ℝ)*t - (zz:ℝ) ∧
      (q:ℝ)*t - (zz:ℝ) < (k.val:ℝ) / rows n
  have hz := floor_index hq ht
  change 0 ≤ zz ∧ zz.toNat ≤ q at hz
  have hzcast : (zz.toNat : ℝ) = (zz : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg hz.1)
  have hQ : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hm : 0 < rows n := rows_pos n
  have rem := floor_remainder (q := q) t
  change 0 ≤ (q:ℝ)*t - (zz:ℝ) ∧ (q:ℝ)*t - (zz:ℝ) < 1 at rem
  have hk_le : (k.val:ℝ) ≤ 2*(n:ℝ) := by
    have : k.val < 2*n+1 := k.isLt
    exact_mod_cast (by omega : k.val ≤ 2*n)
  constructor
  · -- previous interval (index `zz-1`) excludes all remainders below
    let a : Fin (q+2) := ⟨zz.toNat, by omega⟩
    have hnmem : t ∉ staggerSeg n q k a := by intro ha; exact hmiss ⟨a, ha⟩
    have hL : (((a.val:ℝ)-1 + (k.val:ℝ)/rows n)/(q:ℝ)) ≤ t := by
      apply (div_le_iff₀ hQ).2
      dsimp [a]; push_cast; rw [hzcast]
      have hfrac : (k.val:ℝ) / rows n ≤ 1 := (div_le_one (rows_pos n)).2 (by
        dsimp [rows]; linarith)
      linarith
    have hnotR : ¬ t ≤ (((a.val:ℝ)-1 + ((k.val:ℝ)+2*(n:ℝ))/rows n)/(q:ℝ)) := by
      intro hle; exact hnmem ⟨hL, hle⟩
    have hgt : t > (((a.val:ℝ)-1 + ((k.val:ℝ)+2*(n:ℝ))/rows n)/(q:ℝ)) := lt_of_not_ge hnotR
    have hh := (div_lt_iff₀ hQ).1 hgt
    dsimp [a] at hh; push_cast at hh; rw [hzcast] at hh
    -- right endpoint remainder is `(k-1)/rows`
    dsimp [rows] at *
    field_simp at *
    nlinarith
  · -- current interval (index `zz`) excludes all larger remainders
    let a : Fin (q+2) := ⟨zz.toNat + 1, by omega⟩
    have hnmem : t ∉ staggerSeg n q k a := by intro ha; exact hmiss ⟨a, ha⟩
    have hR : t ≤ (((a.val:ℝ)-1 + ((k.val:ℝ)+2*(n:ℝ))/rows n)/(q:ℝ)) := by
      apply (le_div_iff₀ hQ).2
      dsimp [a]; push_cast; rw [hzcast]
      have hbig : rows n ≤ (k.val:ℝ) + 2*(n:ℝ) := by
        dsimp [rows]
        have hkR : (1:ℝ) ≤ k.val := by exact_mod_cast hk
        linarith
      have hfrac : 1 ≤ ((k.val:ℝ)+2*(n:ℝ))/rows n :=
        (le_div_iff₀ (rows_pos n)).2 (by simpa using hbig)
      linarith
    have hnotL : ¬ (((a.val:ℝ)-1 + (k.val:ℝ)/rows n)/(q:ℝ)) ≤ t := by
      intro hle; exact hnmem ⟨hle, hR⟩
    have hlt : t < (((a.val:ℝ)-1 + (k.val:ℝ)/rows n)/(q:ℝ)) := lt_of_not_ge hnotL
    have hh := (lt_div_iff₀ hQ).1 hlt
    dsimp [a] at hh; push_cast at hh; rw [hzcast] at hh
    linarith

lemma staggerSeg_misses {n q : ℕ} (hq : 0 < q) (t : ℝ)
    (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (Finset.univ.filter (fun k : Fin (2*n+1) =>
      ¬ ∃ a : Fin (q+2), t ∈ staggerSeg n q k a)).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro i hi j hj
  have mi : ¬ ∃ a : Fin (q+2), t ∈ staggerSeg n q i a := (Finset.mem_filter.mp hi).2
  have mj : ¬ ∃ a : Fin (q+2), t ∈ staggerSeg n q j a := (Finset.mem_filter.mp hj).2
  by_cases iz : i.val = 0
  · have ie : i = ⟨0, by omega⟩ := Fin.ext iz
    rw [ie] at mi ⊢
    have hiR := miss_zero (n:=n) hq ht mi
    by_cases jz : j.val = 0
    · exact Fin.ext (by simpa using jz.symm) -- check
    · have jp : 0 < j.val := Nat.pos_of_ne_zero jz
      have hjR := miss_pos (n:=n) hq ht j jp mj
      have jle : (j.val:ℝ) ≤ 2*(n:ℝ) := by
        exact_mod_cast (by omega : j.val ≤ 2*n)
      have hm := rows_pos n
      have hc : (j.val:ℝ) / rows n ≤ (2*(n:ℝ)) / rows n :=
        div_le_div_of_nonneg_right jle (le_of_lt hm)
      exfalso
      linarith [hjR.2, hiR]
  · have ip : 0 < i.val := Nat.pos_of_ne_zero iz
    have hiR := miss_pos (n:=n) hq ht i ip mi
    by_cases jz : j.val = 0
    · have je : j = ⟨0, by omega⟩ := Fin.ext jz
      rw [je] at mj ⊢
      have hjR := miss_zero (n:=n) hq ht mj
      have ile : (i.val:ℝ) ≤ 2*(n:ℝ) := by
        exact_mod_cast (by omega : i.val ≤ 2*n)
      have hm := rows_pos n
      have hc : (i.val:ℝ) / rows n ≤ (2*(n:ℝ)) / rows n :=
        div_le_div_of_nonneg_right ile (le_of_lt hm)
      exfalso
      linarith [hiR.2, hjR]
    · have jp : 0 < j.val := Nat.pos_of_ne_zero jz
      have hjR := miss_pos (n:=n) hq ht j jp mj
      -- the open slots `((k-1)/m,k/m)` are disjoint
      have hm := rows_pos n
      have : i.val = j.val := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hle : (i.val:ℝ) ≤ (j.val:ℝ)-1 := by
            have hh : (i.val:ℝ)+1 ≤ (j.val:ℝ) := by exact_mod_cast (by omega : i.val + 1 ≤ j.val)
            linarith
          have hc : (i.val:ℝ) / rows n ≤ ((j.val:ℝ)-1) / rows n :=
            div_le_div_of_nonneg_right hle (le_of_lt hm)
          exfalso
          linarith [hiR.2, hjR.1]
        · have hle : (j.val:ℝ) ≤ (i.val:ℝ)-1 := by
            have hh : (j.val:ℝ)+1 ≤ (i.val:ℝ) := by exact_mod_cast (by omega : j.val + 1 ≤ i.val)
            linarith
          have hc : (j.val:ℝ) / rows n ≤ ((i.val:ℝ)-1) / rows n :=
            div_le_div_of_nonneg_right hle (le_of_lt hm)
          exfalso
          linarith [hjR.2, hiR.1]
      exact Fin.ext this

/-- What remains of the construction after choosing the standard staggered
intervals: the inner sums have disjoint images on the boxes of every sufficiently
fine grid.  In applications one obtains this by the successive small digit
perturbations of the plateau functions. -/
def DigitSeparated (n : ℕ)
    (p : Fin (2*n+1) → Fin n → ℝ → ℝ) : Prop :=
  ∀ B : ℕ, ∃ q : ℕ, B < q ∧ 0 < q ∧
    ∀ (k : Fin (2*n+1)) {a b : Fin n → Fin (q+2)}, a ≠ b →
      Disjoint (innerSum p k '' strandBox n (q+2) (staggerSeg n q) k a)
               (innerSum p k '' strandBox n (q+2) (staggerSeg n q) k b)

lemma digitSeparated_strands {n : ℕ}
    {p : Fin (2*n+1) → Fin n → ℝ → ℝ}
    (h : DigitSeparated n p) : HasStrandLevels n p := by
  intro d hd
  obtain ⟨B, hB⟩ := exists_nat_gt ((1:ℝ)/d)
  obtain ⟨q, hBq, hq, hsep⟩ := h B
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hlarge : (1:ℝ)/(q:ℝ) < d := by
    have hqd : (1:ℝ)/d < (q:ℝ) := lt_trans hB (by exact_mod_cast hBq)
    exact (div_lt_iff₀ hqR).2 (by
      have hh : (1:ℝ) < (q:ℝ) * d := (div_lt_iff₀ hd).1 hqd
      nlinarith)
  exact ⟨{
    L := q+2
    seg := staggerSeg n q
    seg_closed := staggerSeg_closed n q
    seg_small := staggerSeg_small hq hlarge
    misses := staggerSeg_misses hq
    separated := hsep }⟩

end KAS

-- END INLINED FILE: Mathlib/Support/kolmogorov_arnold_superposition_7c7ff433f4/Staggered.lean

-- BEGIN INLINED FILE: Mathlib/Support/kolmogorov_arnold_superposition_7c7ff433f4/DigitsPrep.lean

open scoped BigOperators
open Classical
namespace KAS

/-- A marked point in each staggered segment.  We deliberately choose it
abstractly; all that is ever used is small diameter of the segment. -/
noncomputable def staggerSample {n q : ℕ} (hq : 0 < q)
    (k : Fin (2*n+1)) (a : Fin (q+2)) : ℝ :=
  Classical.choose (staggerSeg_nonempty hq k a)

lemma staggerSample_mem {n q : ℕ} (hq : 0 < q)
    (k : Fin (2*n+1)) (a : Fin (q+2)) :
    staggerSample hq k a ∈ staggerSeg n q k a :=
  Classical.choose_spec (staggerSeg_nonempty hq k a)

/-- The harmless mixed radix perturbation used at one level of the
construction. Arrays of segment indices have different sums of these codes.
Working with natural numbers first avoids rational-independence bookkeeping. -/
def radixCode (q : ℕ) {n : ℕ} (l : Fin n) (a : Fin (q+2)) : ℝ :=
  (a.val:ℝ) * (((q+2) ^ l.val : ℕ) : ℝ)

lemma radixCode_inj_sum {n q : ℕ} {a b : Fin n → Fin (q+2)} (h : a ≠ b) :
    (∑ l, radixCode q l (a l)) ≠ (∑ l, radixCode q l (b l)) := by
  classical
  intro he
  have he' : (∑ l : Fin n, (( (a l).val * (q+2) ^ l.val : ℕ) : ℝ)) =
      (∑ l : Fin n, (( (b l).val * (q+2) ^ l.val : ℕ) : ℝ)) := by
    simpa [radixCode, Nat.cast_mul, Nat.cast_pow] using he
  have hnat : (∑ l : Fin n, (a l).val * (q+2) ^ l.val) =
      (∑ l : Fin n, (b l).val * (q+2) ^ l.val) := by
    exact_mod_cast he'
  have hv : finFunctionFinEquiv a = finFunctionFinEquiv b := by
    apply Fin.ext
    simpa [finFunctionFinEquiv_apply] using hnat
  exact h ((finFunctionFinEquiv).injective hv)
end KAS

namespace KAS
open Classical

/-- The closed union of the strands of one row at one level. -/
def rowSet (n q : ℕ) (k : Fin (2*n+1)) : Set ℝ :=
  ⋃ a : Fin (q+2), staggerSeg n q k a

lemma rowSet_closed (n q : ℕ) (k : Fin (2*n+1)) :
    IsClosed (rowSet n q k) := by
  classical
  unfold rowSet
  apply isClosed_iUnion_of_finite
  intro a
  exact staggerSeg_closed n q k a

lemma mem_rowSet {n q : ℕ} {k : Fin (2*n+1)} {t : ℝ} :
    t ∈ rowSet n q k ↔ ∃ a : Fin (q+2), t ∈ staggerSeg n q k a := by
  classical simp [rowSet]

/-- On the union, a single component is clopen.  For a finite closed
pairwise-disjoint family this saves unpleasant interpolation bookkeeping. -/
def rowPiece {n q : ℕ} (k : Fin (2*n+1)) (a : Fin (q+2)) :
    Set (rowSet n q k) := {x | (x:ℝ) ∈ staggerSeg n q k a}

lemma rowPiece_closed {n q : ℕ} (k : Fin (2*n+1)) (a : Fin (q+2)) :
    IsClosed (rowPiece k a) := by
  exact (staggerSeg_closed n q k a).preimage (continuous_subtype_val)

lemma rowPiece_clopen {n q : ℕ} (hq : 0 < q)
    (k : Fin (2*n+1)) (a : Fin (q+2)) :
    IsClopen (rowPiece k a) := by
  classical
  have hclosed := rowPiece_closed k a
  have hcomp : (rowPiece k a)ᶜ =
      ⋃ b : {b : Fin (q+2) // b ≠ a}, rowPiece k (b:Fin (q+2)) := by
    ext x
    constructor
    · intro hx
      have hxnot : (x:ℝ) ∉ staggerSeg n q k a := by
        simpa [rowPiece] using hx
      obtain ⟨b, hb⟩ := (mem_rowSet.mp x.property)
      have hne : b ≠ a := by intro hba; apply hxnot; simpa [hba] using hb
      exact Set.mem_iUnion.mpr ⟨⟨b,hne⟩, hb⟩
    · intro hx
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hx
      have hbmem : (x:ℝ) ∈ staggerSeg n q k (b:Fin (q+2)) := hb
      have hnot : (x:ℝ) ∉ staggerSeg n q k a := by
        intro ha
        have hd := staggerSeg_disjoint (n:=n) (q:=q) hq k b.property
        exact (Set.disjoint_left.mp hd hbmem ha)
      simpa [rowPiece] using hnot
  have hccomp : IsClosed ((rowPiece k a)ᶜ) := by
    rw [hcomp]
    apply isClosed_iUnion_of_finite
    intro b
    exact rowPiece_closed k (b:Fin (q+2))
  have hopen : IsOpen (rowPiece k a) := (isClosed_compl_iff.mp hccomp)
  exact ⟨hclosed, hopen⟩

/-- A correction prescribed separately on every component of a row. -/
noncomputable def rowCorrection {n q : ℕ} (hq : 0 < q)
    (k : Fin (2*n+1)) (u : BoundedContinuousFunction ℝ ℝ)
    (c : Fin (q+2) → ℝ) (x : rowSet n q k) : ℝ :=
  ∑ a : Fin (q+2), if (x:ℝ) ∈ staggerSeg n q k a then c a - u x else 0

lemma rowCorrection_on {n q : ℕ} (hq : 0 < q)
    (k : Fin (2*n+1)) (u : BoundedContinuousFunction ℝ ℝ)
    (c : Fin (q+2) → ℝ) (a : Fin (q+2))
    (x : ℝ) (hx : x ∈ staggerSeg n q k a) :
    rowCorrection hq k u c ⟨x, (mem_rowSet).2 ⟨a,hx⟩⟩ = c a - u x := by
  classical
  unfold rowCorrection
  classical
  -- exactly one disjoint interval contains `x`
  rw [Fintype.sum_eq_single a]
  · simp [hx]
  · intro b hba
    have hnot : x ∉ staggerSeg n q k b := by
      intro hb
      have hd := staggerSeg_disjoint (n:=n) (q:=q) hq k hba
      exact (Set.disjoint_left.mp hd hb hx)
    simp [hnot]

lemma rowCorrection_continuous {n q : ℕ} (hq : 0 < q)
    (k : Fin (2*n+1)) (u : BoundedContinuousFunction ℝ ℝ)
    (c : Fin (q+2) → ℝ) :
    Continuous (rowCorrection hq k u c) := by
  classical
  unfold rowCorrection
  apply continuous_finset_sum
  intro a ha
  -- On the row subtype this condition is clopen, hence has empty frontier.
  have hc : IsClopen (rowPiece k a) := rowPiece_clopen hq k a
  have hfr : frontier (rowPiece k a) = (∅ : Set (rowSet n q k)) :=
    (isClopen_iff_frontier_eq_empty.mp hc)
  have hfg : ∀ x ∈ frontier (rowPiece k a),
      (fun x : rowSet n q k => c a - u x) x = (fun _ : rowSet n q k => (0:ℝ)) x := by
    intro x hx
    rw [hfr] at hx
    exact False.elim (by simpa using hx)
  exact Continuous.if hfg
    (continuous_const.sub (u.continuous.comp continuous_subtype_val))
    continuous_const

/-- Bounded extension of the row correction. We keep it in the bounded
continuous space so the sup-norm controls all later levels. -/
lemma rowCorrection_extension {n q : ℕ} (hq : 0 < q)
    (k : Fin (2*n+1)) (u : BoundedContinuousFunction ℝ ℝ)
    (c : Fin (q+2) → ℝ) {E : ℝ} (hE : 0 ≤ E)
    (hclose : ∀ a : Fin (q+2), ∀ t ∈ staggerSeg n q k a,
        |c a - u t| ≤ E) :
    ∃ w : BoundedContinuousFunction ℝ ℝ,
      ‖w‖ ≤ E ∧
      (∀ a : Fin (q+2), ∀ t ∈ staggerSeg n q k a,
          w t = c a - u t) := by
  classical
  let w0 : BoundedContinuousFunction (rowSet n q k) ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (rowCorrection hq k u c) (rowCorrection_continuous hq k u c) E (by
        intro x
        obtain ⟨a, ha⟩ := mem_rowSet.mp x.property
        rw [rowCorrection_on hq k u c a (x:ℝ) ha]
        simpa [Real.norm_eq_abs] using hclose a (x:ℝ) ha)
  obtain ⟨w, hw, hrestrict⟩ :=
    BoundedContinuousFunction.exists_norm_eq_restrict_eq_of_closed w0 (rowSet_closed n q k)
  refine ⟨w, ?_, ?_⟩
  · -- the extension theorem preserves the norm
    rw [hw]
    exact (BoundedContinuousFunction.norm_le hE).2 (by
      intro x
      change ‖rowCorrection hq k u c x‖ ≤ E
      obtain ⟨a,ha⟩ := mem_rowSet.mp x.property
      rw [rowCorrection_on hq k u c a (x:ℝ) ha]
      simpa [Real.norm_eq_abs] using hclose a (x:ℝ) ha)
  · intro a t ht
    have hz : (⟨t, (mem_rowSet).2 ⟨a,ht⟩⟩ : rowSet n q k) =
        ⟨t, (mem_rowSet).2 ⟨a,ht⟩⟩ := rfl
    have hh := congrArg (fun z : BoundedContinuousFunction (rowSet n q k) ℝ =>
          z ⟨t, (mem_rowSet).2 ⟨a,ht⟩⟩) hrestrict
    change w t = rowCorrection hq k u c ⟨t, (mem_rowSet).2 ⟨a,ht⟩⟩ at hh
    simpa [rowCorrection_on hq k u c a t ht] using hh

end KAS
namespace KAS
open Classical

/-- Simultaneous modulus on the fixed compact interval for a finite table of
continuous functions. -/
lemma table_modulus {I J : Type*} [Fintype I] [Fintype J]
    (u : I → J → BoundedContinuousFunction ℝ ℝ) {e : ℝ} (he : 0 < e) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ i j, ∀ x ∈ Set.Icc (-1:ℝ) 3, ∀ y ∈ Set.Icc (-1:ℝ) 3,
        dist x y < δ → dist (u i j x) (u i j y) < e := by
  classical
  have hloc (i : I) (j : J) :
      ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Set.Icc (-1:ℝ) 3, ∀ y ∈ Set.Icc (-1:ℝ) 3,
        dist x y < δ → dist (u i j x) (u i j y) < e := by
    have hu :=
      (isCompact_Icc.uniformContinuousOn_of_continuous (s := Set.Icc (-1:ℝ) 3) 
        (u i j).continuous.continuousOn)
    exact (Metric.uniformContinuousOn_iff.mp hu) e he
  choose d hdpos hd using hloc
  -- take a positive number below the finite sum of the reciprocals' maximum;
  -- `min'` on the finite nonempty augmented set is convenient even when an
  -- index type is empty.
  let T : Finset ℝ := {1} ∪
    (Finset.univ.biUnion (fun i : I =>
       Finset.univ.image (fun j : J => min 1 (d i j))))
  have hT : T.Nonempty := by simp [T]
  obtain ⟨δ, hδmem, hδle⟩ := Finset.exists_min_image T (fun x : ℝ => x) hT
  have hδ1 : δ ≤ 1 := by
    have hm : (1:ℝ) ∈ T := by simp [T]
    have := hδle 1 hm
    simpa using this
  have hTpos : ∀ z ∈ T, 0 < z := by
    intro z hz
    simp [T] at hz
    rcases hz with hz | hz
    · simpa [hz]
    · obtain ⟨i, j, rfl⟩ := hz
      exact lt_min (by linarith) (hdpos i j)
  have hδpos' : 0 < δ := hTpos δ hδmem
  refine ⟨δ, hδpos', ?_⟩
  intro i j x hx y hy hxy
  apply hd i j x hx y hy
  have hminmem : min 1 (d i j) ∈ T := by simp [T]
  have hle := hδle _ hminmem
  have hδmin : δ ≤ min 1 (d i j) := by simpa using hle
  exact lt_of_lt_of_le hxy (le_trans hδmin (min_le_right _ _))

/-- Finite level of plateau functions. -/
structure Plateau (n q : ℕ) where
  funs : Fin (2*n+1) → Fin n → BoundedContinuousFunction ℝ ℝ
  vals : Fin (2*n+1) → Fin n → Fin (q+2) → ℝ
  on_seg : ∀ k l a, ∀ t ∈ staggerSeg n q k a, funs k l t = vals k l a
  values_separate : ∀ k {a b : Fin n → Fin (q+2)}, a ≠ b →
    (∑ l, vals k l (a l)) ≠ (∑ l, vals k l (b l))

/-- Avoid a finite list of forbidden real numbers while staying in any small
positive interval. -/
lemma small_avoid (s : Finset ℝ) {e : ℝ} (he : 0 < e) :
    ∃ t : ℝ, 0 < t ∧ t < e ∧ t ∉ s := by
  obtain ⟨t, ht, hts⟩ := (Set.Ioo_infinite he).exists_notMem_finset s
  exact ⟨t, ht.1, ht.2, hts⟩

end KAS
namespace KAS
open Classical

lemma radixCode_nonneg {n q : ℕ} (l : Fin n) (a : Fin (q+2)) :
    0 ≤ radixCode q l a := by unfold radixCode; positivity

lemma radixCode_lt_pow {n q : ℕ} (hn : 0 < n) (l : Fin n) (a : Fin (q+2)) :
    radixCode q l a < (((q+2)^n : ℕ) : ℝ) := by
  have hbase : 0 < q+2 := by omega
  have ha : a.val < q+2 := a.isLt
  have hmul : a.val * (q+2)^l.val < (q+2)^(l.val+1) := by
    rw [pow_succ]
    nlinarith [Nat.zero_lt_two, (pow_pos hbase l.val)]
  have hpow : (q+2)^(l.val+1) ≤ (q+2)^n :=
    Nat.pow_le_pow_right hbase (by omega)
  have hh : a.val * (q+2)^l.val < (q+2)^n := lt_of_lt_of_le hmul hpow
  simpa [radixCode, Nat.cast_mul, Nat.cast_pow] using (by exact_mod_cast hh : (((a.val * (q+2)^l.val : ℕ) : ℝ) < (((q+2)^n : ℕ) : ℝ)))

/-- One can make every row constant with distinct mixed-radix values on an
arbitrarily fine staggered grid, perturbing a given finite table by any
prescribed sup norm. This is the finite skeleton of the infinite digit
construction. -/
lemma exists_plateau_near {n : ℕ} (hn : 0 < n)
    (u : Fin (2*n+1) → Fin n → BoundedContinuousFunction ℝ ℝ)
    (B : ℕ) {e : ℝ} (he : 0 < e) :
    ∃ q : ℕ, B < q ∧ 0 < q ∧
      ∃ P : Plateau n q,
        ∀ k l, ‖P.funs k l - u k l‖ ≤ e/2 := by
  classical
  obtain ⟨δ, hδ, hmod⟩ := table_modulus u (by linarith [he] : 0 < e/4)
  obtain ⟨q, hqbig⟩ := exists_nat_gt (max (B:ℝ) (1/δ))
  have hBq : B < q := by exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hqbig)
  have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le _) hBq
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hsmall : (1:ℝ)/(q:ℝ) < δ := by
    have hgt : (1/δ) < (q:ℝ) := lt_of_le_of_lt (le_max_right _ _) hqbig
    apply (div_lt_iff₀ hqR).2
    have := (div_lt_iff₀ hδ).1 hgt
    nlinarith
  let base (k : Fin (2*n+1)) (l : Fin n) (a : Fin (q+2)) : ℝ :=
      u k l (staggerSample hq k a)
  have hvar (k : Fin (2*n+1)) (l : Fin n) (a : Fin (q+2))
      (t : ℝ) (ht : t ∈ staggerSeg n q k a) :
      |base k l a - u k l t| < e/4 := by
    have hs := staggerSample_mem (n:=n) hq k a
    have hsK := staggerSeg_bounds hq k a hs
    have htK := staggerSeg_bounds hq k a ht
    have hdxy := staggerSeg_small (n:=n) hq hsmall k a
      (staggerSample hq k a) hs t ht
    have hh := hmod k l (staggerSample hq k a) hsK t htK hdxy
    simpa [base, Real.dist_eq] using hh
  let val0 (k : Fin (2*n+1)) (A : Fin n → Fin (q+2)) : ℝ :=
      ∑ l, base k l (A l)
  let code (A : Fin n → Fin (q+2)) : ℝ := ∑ l, radixCode q l (A l)
  let bad : Finset ℝ :=
      Finset.univ.biUnion (fun k : Fin (2*n+1) =>
        Finset.univ.biUnion (fun A : (Fin n → Fin (q+2)) =>
          Finset.univ.image (fun C : (Fin n → Fin (q+2)) =>
            - (val0 k A - val0 k C) / (code A - code C))))
  have hpowpos : (0:ℝ) < (((q+2)^n : ℕ) : ℝ) := by positivity
  have hbudget : 0 < (e/4) / (((q+2)^n : ℕ) : ℝ) := by positivity
  obtain ⟨τ, hτ, hτsmall, hτbad⟩ := small_avoid bad hbudget
  let vals (k : Fin (2*n+1)) (l : Fin n) (a : Fin (q+2)) : ℝ :=
       base k l a + τ * radixCode q l a
  have hsep (k : Fin (2*n+1)) {A C : Fin n → Fin (q+2)} (hne : A ≠ C) :
       (∑ l, vals k l (A l)) ≠ (∑ l, vals k l (C l)) := by
    have hdif : code A - code C ≠ 0 :=
      sub_ne_zero.mpr (radixCode_inj_sum hne)
    intro hh
    have heq : (val0 k A - val0 k C) + τ * (code A - code C) = 0 := by
      dsimp [vals] at hh
      dsimp [val0, code]
      simp only [Finset.sum_add_distrib] at hh
      simp only [← Finset.mul_sum] at hh
      linear_combination hh
    have htbad : τ = -(val0 k A - val0 k C) / (code A - code C) := by
      apply (eq_div_iff hdif).2
      linarith
    apply hτbad
    rw [htbad]
    simp [bad]
  have hclose (k : Fin (2*n+1)) (l : Fin n) (a : Fin (q+2))
      (t : ℝ) (ht : t ∈ staggerSeg n q k a) :
      |vals k l a - u k l t| ≤ e/2 := by
    have hv := hvar k l a t ht
    have hc0 := radixCode_nonneg (n:=n) (q:=q) l a
    have hc1 := radixCode_lt_pow (q:=q) hn l a
    have hmul : τ * radixCode q l a < e/4 := by
      have hle : τ * radixCode q l a <
          ((e/4) / (((q+2)^n : ℕ) : ℝ)) * (((q+2)^n : ℕ) : ℝ) := by
        by_cases hz : radixCode q l a = 0
        · simp [hz]; exact mul_pos (by simpa [Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat] using hbudget) (by simpa [Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat] using hpowpos)
        · have hcp : 0 < radixCode q l a := lt_of_le_of_ne hc0 (Ne.symm hz)
          exact lt_of_le_of_lt
            (mul_le_mul_of_nonneg_left (le_of_lt hc1) (le_of_lt hτ))
            (mul_lt_mul_of_pos_right hτsmall hpowpos)
      convert hle using 1 <;> field_simp <;> ring
    have hnon : 0 ≤ τ * radixCode q l a := mul_nonneg (le_of_lt hτ) hc0
    calc
      |vals k l a - u k l t| =
          |(base k l a - u k l t) + τ * radixCode q l a| := by
            unfold vals; congr 1 <;> ring
      _ ≤ |base k l a - u k l t| + |τ * radixCode q l a| := abs_add_le _ _
      _ ≤ e/2 := by rw [abs_of_nonneg hnon]; linarith
  -- extend corrections for every entry of the finite table
  choose w hw hwon using fun k : Fin (2*n+1) => fun l : Fin n =>
    rowCorrection_extension (n:=n) hq k (u k l) (vals k l)
      (le_of_lt (by linarith [he] : 0 < e/2)) (hclose k l)
  let vf (k : Fin (2*n+1)) (l : Fin n) := u k l + w k l
  let P : Plateau n q :=
    { funs := vf
      vals := vals
      on_seg := by
        intro k l a t ht
        change (u k l + w k l) t = vals k l a
        change u k l t + w k l t = _
        rw [hwon k l a t ht]
        ring
      values_separate := hsep }
  refine ⟨q, hBq, hq, P, ?_⟩
  intro k l
  change ‖(u k l + w k l) - u k l‖ ≤ _
  simpa using hw k l

end KAS
namespace KAS
open Classical

def tabToP {n : ℕ}
    (u : Fin (2*n+1) → Fin n → BoundedContinuousFunction ℝ ℝ) :
    Fin (2*n+1) → Fin n → ℝ → ℝ := fun k l => u k l

/-- Every plateau has a positive arithmetic gap, chosen uniformly over its
finite table of row boxes. -/
lemma plateau_gap {n q : ℕ} (P : Plateau n q) :
    ∃ g : ℝ, 0 < g ∧ ∀ k (a b : Fin n → Fin (q+2)), a ≠ b →
      g ≤ |(∑ l, P.vals k l (a l)) - (∑ l, P.vals k l (b l))| := by
  classical
  let S : Finset ℝ := {1} ∪
    (Finset.univ.biUnion (fun k : Fin (2*n+1) =>
      Finset.univ.biUnion (fun a : (Fin n → Fin (q+2)) =>
        (Finset.univ.filter (fun b : (Fin n → Fin (q+2)) => b ≠ a)).image
          (fun b => |(∑ l, P.vals k l (a l)) - (∑ l, P.vals k l (b l))|))))
  have hS : S.Nonempty := by simp [S]
  obtain ⟨g, hg, hleast⟩ := Finset.exists_min_image S (fun x : ℝ => x) hS
  have hposmem : ∀ z ∈ S, 0 < z := by
    intro z hz
    simp [S] at hz
    rcases hz with hz | ⟨k,a,b,hba,rfl⟩
    · simpa [hz]
    · exact abs_pos.mpr (sub_ne_zero.mpr (P.values_separate k (Ne.symm hba)))
  have hgp : 0 < g := hposmem g hg
  refine ⟨g, hgp, ?_⟩
  intro k a b hab
  have hm : |(∑ l, P.vals k l (a l)) - (∑ l, P.vals k l (b l))| ∈ S := by
    simp [S]
    exact Or.inr ⟨k,a,b,Ne.symm hab, rfl⟩
  simpa using hleast _ hm

lemma sum_error {n q : ℕ}
    (hn : 0 < n) (P : Plateau n q)
    (v : Fin (2*n+1) → Fin n → BoundedContinuousFunction ℝ ℝ)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hne : ∀ k l, dist (v k l) (P.funs k l) < ρ)
    (k : Fin (2*n+1)) (a : Fin n → Fin (q+2))
    (x : Fin n → ℝ)
    (hx : ∀ l, x l ∈ staggerSeg n q k (a l)) :
    |(∑ l, v k l (x l)) - (∑ l, P.vals k l (a l))| < (n:ℝ)*ρ := by
  have hi (l : Fin n) : |v k l (x l) - P.vals k l (a l)| < ρ := by
    rw [← P.on_seg k l (a l) (x l) (hx l)]
    rw [← Real.dist_eq]
    exact lt_of_le_of_lt
      ((BoundedContinuousFunction.dist_le (dist_nonneg)).1 le_rfl (x l)) (hne k l)
  have hsum :
      |∑ l : Fin n, (v k l (x l) - P.vals k l (a l))| ≤
        ∑ l : Fin n, |v k l (x l) - P.vals k l (a l)| := by
    simpa [Real.norm_eq_abs] using
      (norm_sum_le (Finset.univ : Finset (Fin n))
        (fun l => (v k l (x l) - P.vals k l (a l))))
  rw [← Finset.sum_sub_distrib]
  exact lt_of_le_of_lt hsum (by
    have : (∑ l : Fin n, |v k l (x l) - P.vals k l (a l)|) <
        ∑ _l : Fin n, ρ := Finset.sum_lt_sum (fun l _ => le_of_lt (hi l))
          ⟨⟨0, hn⟩, Finset.mem_univ _, hi ⟨0, hn⟩⟩
    simpa using this)

end KAS
namespace KAS
open Classical
lemma close_plateau_separates {n q : ℕ} (hn : 0 < n)
    (P : Plateau n q)
    (v : Fin (2*n+1) → Fin n → BoundedContinuousFunction ℝ ℝ)
    {g ρ : ℝ} (hρ : 0 < ρ)
    (hgap : ∀ k (a b : Fin n → Fin (q+2)), a ≠ b →
      g ≤ |(∑ l, P.vals k l (a l)) - (∑ l, P.vals k l (b l))|)
    (hlarge : 2*(n:ℝ)*ρ < g)
    (hne : ∀ k l, dist (v k l) (P.funs k l) < ρ) :
    ∀ k {a b : Fin n → Fin (q+2)}, a ≠ b →
      Disjoint
       (innerSum (tabToP v) k '' strandBox n (q+2) (staggerSeg n q) k a)
       (innerSum (tabToP v) k '' strandBox n (q+2) (staggerSeg n q) k b) := by
  classical
  intro k a b hab
  apply Set.disjoint_left.mpr
  intro t ht hu
  rcases ht with ⟨x,hx,rfl⟩
  rcases hu with ⟨y,hy,heq⟩
  have hxerr := sum_error hn P v (le_of_lt hρ) hne k a x hx.2
  have hyerr := sum_error hn P v (le_of_lt hρ) hne k b y hy.2
  change (∑ l, v k l (y l)) = (∑ l, v k l (x l)) at heq
  have hg := hgap k a b hab
  have tri :
      |(∑ l, P.vals k l (a l)) - (∑ l, P.vals k l (b l))| <
        2*(n:ℝ)*ρ := by
    calc
      |(∑ l, P.vals k l (a l)) - (∑ l, P.vals k l (b l))| =
        |((∑ l, v k l (x l)) - (∑ l, P.vals k l (a l))) -
          ((∑ l, v k l (y l)) - (∑ l, P.vals k l (b l)))| := by rw [heq]; rw [← abs_neg]; congr 1 <;> ring
      _ ≤ |((∑ l, v k l (x l)) - (∑ l, P.vals k l (a l)))| +
          |((∑ l, v k l (y l)) - (∑ l, P.vals k l (b l)))| := abs_sub _ _
      _ < 2*(n:ℝ)*ρ := by linarith
  linarith
end KAS
namespace KAS
open Classical
/-- Stability packaged as an actual open ball in the finite table space. -/
lemma plateau_ball {n q : ℕ} (hn : 0 < n) (P : Plateau n q) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ (v : Fin (2*n+1) → Fin n → BoundedContinuousFunction ℝ ℝ),
         dist v P.funs < ρ →
        ∀ k {a b : Fin n → Fin (q+2)}, a ≠ b →
          Disjoint
           (innerSum (tabToP v) k '' strandBox n (q+2) (staggerSeg n q) k a)
           (innerSum (tabToP v) k '' strandBox n (q+2) (staggerSeg n q) k b) := by
  obtain ⟨g,hg,hgap⟩ := plateau_gap P
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  let ρ : ℝ := g / (4*(n:ℝ))
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  refine ⟨ρ, hρ, ?_⟩
  intro v hv
  apply close_plateau_separates hn P v hρ hgap
    (by dsimp [ρ]; field_simp; linarith)
  intro k l
  exact lt_of_le_of_lt (dist_le_pi_dist v P.funs k |> fun t =>
      le_trans (dist_le_pi_dist (v k) (P.funs k) l) t) hv
end KAS

-- END INLINED FILE: Mathlib/Support/kolmogorov_arnold_superposition_7c7ff433f4/DigitsPrep.lean

-- BEGIN INLINED FILE: Mathlib/Support/kolmogorov_arnold_superposition_7c7ff433f4/BaireDigits.lean

open scoped BigOperators
namespace KAS
open Classical

/-- The Banach space of tables of one-variable functions.  The finite products
use the sup metric, exactly the one used in `plateau_ball`. -/
abbrev DigitTable (n : ℕ) :=
  Fin (2*n+1) → Fin n → BoundedContinuousFunction ℝ ℝ

/-- Separation at a specified grid. -/
def GridSep (n q : ℕ) (v : DigitTable n) : Prop :=
  ∀ (k : Fin (2*n+1)) {a b : Fin n → Fin (q+2)}, a ≠ b →
    Disjoint
       (innerSum (tabToP v) k '' strandBox n (q+2) (staggerSeg n q) k a)
       (innerSum (tabToP v) k '' strandBox n (q+2) (staggerSeg n q) k b)

/-- For a prescribed lower bound on the level, take the union of all the
balls furnished by finite plateaux.  Using this smaller open set, rather than
all separating tables, avoids any compact-image arguments: the stability
lemma for a plateau is precisely the radius of one of these balls. -/
def digitGood (n B : ℕ) : Set (DigitTable n) :=
  {v | ∃ q : ℕ, B < q ∧
      ∃ P : Plateau n q, ∃ r : ℝ, 0 < r ∧
        dist v P.funs < r ∧
        ∀ w : DigitTable n, dist w P.funs < r → GridSep n q w}

set_option synthInstance.maxHeartbeats 400000 in
lemma digitGood_open (n B : ℕ) : IsOpen (digitGood n B) := by
  classical
  apply Metric.isOpen_iff.mpr
  intro v hv
  rcases hv with ⟨q,hq,P,r,hr,hv,hstable⟩
  refine ⟨r - dist v P.funs, sub_pos.mpr hv, ?_⟩
  intro w hw
  have hwv : dist w v < r - dist v P.funs := Metric.mem_ball.mp hw
  have hwt : dist w P.funs < r := by
    have hh := dist_triangle w v P.funs
    linarith
  exact ⟨q, hq, P, r, hr, hwt, hstable⟩

set_option synthInstance.maxHeartbeats 400000 in
lemma digitGood_dense {n : ℕ} (hn : 0 < n) (B : ℕ) : Dense (digitGood n B) := by
  classical
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro u
  refine Metric.mem_closure_iff.mpr ?_
  intro e he
  obtain ⟨q,hBq,hq,P,hnear⟩ :=
    exists_plateau_near (n:=n) hn u B he
  obtain ⟨r,hr,hstable⟩ := plateau_ball hn P
  refine ⟨P.funs, ?_, ?_⟩
  · refine ⟨q, hBq, P, r, hr, ?_, ?_⟩
    · simpa using hr
    · intro w hw
      exact hstable w hw
  · have he0 : 0 ≤ e/2 := by linarith
    have hle : dist u P.funs ≤ e/2 := by
      apply (dist_pi_le_iff he0).2
      intro k
      apply (dist_pi_le_iff he0).2
      intro l
      have hh := hnear k l
      -- the estimate supplied at the construction is written with the
      -- arguments reversed.
      simpa [dist_eq_norm, norm_sub_rev] using hh
    linarith

set_option synthInstance.maxHeartbeats 800000 in
/-- A single continuous table belongs to all the dense open unions; its rows
therefore separate boxes on arbitrarily fine staggered grids. -/
lemma exists_digit_table {n : ℕ} (hn : 0 < n) :
    ∃ p : Fin (2*n+1) → Fin n → ℝ → ℝ,
      (∀ k l, Continuous (p k l)) ∧ DigitSeparated n p := by
  classical
  have ho : ∀ B : ℕ, IsOpen (digitGood n B) := fun B => digitGood_open n B
  have hd : ∀ B : ℕ, Dense (digitGood n B) := fun B => digitGood_dense hn B
  have hall : Dense (⋂ B : ℕ, digitGood n B) :=
    dense_iInter_of_isOpen_nat ho hd
  have hnon : (⋂ B : ℕ, digitGood n B : Set (DigitTable n)).Nonempty :=
    hall.nonempty
  rcases hnon with ⟨v,hv⟩
  refine ⟨tabToP v, ?_, ?_⟩
  · intro k l
    exact (v k l).continuous
  · intro B
    have hB : v ∈ digitGood n B := Set.mem_iInter.mp hv B
    rcases hB with ⟨q,hBq,P,r,hr,hvP,hstab⟩
    refine ⟨q, hBq, Nat.zero_lt_of_lt hBq, ?_⟩
    exact hstab v hvP

end KAS

-- END INLINED FILE: Mathlib/Support/kolmogorov_arnold_superposition_7c7ff433f4/BaireDigits.lean

namespace Submission

-- BEGIN INLINED FILE: Main.lean

open scoped BigOperators
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem kolmogorov_arnold (n : ℕ) (_hn : 1 ≤ n)
    (f : (Fin n → ℝ) → ℝ) (_hf : ContinuousOn f (Set.Icc 0 1)) :
    ∃ (g : ℝ → ℝ) (φ : Fin (2 * n + 1) → Fin n → ℝ → ℝ),
      Continuous g ∧ (∀ k l, Continuous (φ k l)) ∧
      ∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1,
        f x = ∑ k, g (∑ l, φ k l (x l)) :=
/-ResultProofBegin-/by
  rcases Nat.eq_or_lt_of_le _hn with h | h
  · subst n
    simpa using (KAS.one_dim f _hf)
  · -- In higher arity it is enough to construct a representation with
    -- layer-dependent outer functions.  Separating their compact ranges on
    -- the real line removes that harmless convention issue.
    classical
    -- A limiting argument also need not be redone in the covering proof.
    -- With fixed inner sums, a uniformly bounded contraction approximation
    -- can be iterated inside the Banach space of bounded continuous functions.
    obtain ⟨R₀,hR₀⟩ :=
      (isCompact_Icc.exists_bound_of_continuousOn _hf)
    let R : ℝ := |R₀|
    have hR : 0 ≤ R := abs_nonneg _
    have hfR : ∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1, |f x| ≤ R := by
      intro x hx
      calc
        |f x| = ‖f x‖ := by rw [Real.norm_eq_abs]
        _ ≤ R₀ := hR₀ x hx
        _ ≤ |R₀| := le_abs_self _
    let θ : ℝ := 1 - 1 / (4 * (n : ℝ) + 2)
    have den : 0 < (4 * (n : ℝ) + 2) := by positivity
    have hθ0 : 0 ≤ θ := by
      dsimp [θ]
      have : (1 : ℝ) ≤ 4 * (n : ℝ) + 2 := by have h : 0 ≤ (n : ℝ) := Nat.cast_nonneg _; linarith
      have := (div_le_one den).2 this
      linarith
    have hθ1 : θ < 1 := by
      dsimp [θ]
      have : 0 < (1:ℝ) / (4 * (n : ℝ) + 2) := by positivity
      linarith
    have approx_unit :
      ∃ p : Fin (2*n+1) → Fin n → ℝ → ℝ,
        (∀ k l, Continuous (p k l)) ∧
        (∀ (r : (Fin n → ℝ) → ℝ),
          ContinuousOn r (Set.Icc (0 : Fin n → ℝ) 1) →
          (∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1, |r x| ≤ (1:ℝ)) →
          ∃ A : Fin (2*n+1) → BoundedContinuousFunction ℝ ℝ,
            (∀ k, ‖A k‖ ≤ (1:ℝ)) ∧
            ∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1,
              |r x - ∑ k, A k (∑ l, p k l (x l))| ≤ θ) := by
      obtain ⟨p, hp, hc⟩ :
          ∃ p : Fin (2*n+1) → Fin n → ℝ → ℝ,
            (∀ k l, Continuous (p k l)) ∧ KAS.DigitSeparated n p := by
        have hn0 : 0 < n := lt_trans Nat.zero_lt_one h
        exact KAS.exists_digit_table hn0
      have hc0 : KAS.HasStrandLevels n p := KAS.digitSeparated_strands hc
      have hc' : KAS.HasSeparatingCovers n p := KAS.strand_to_covers hc0
      refine ⟨p, hp, ?_⟩
      intro r hr hb
      have he : (2*(2*(n:ℝ)+1)) = 4*(n:ℝ)+2 := by ring
      simpa [KAS.innerSum, θ, he] using
        (KAS.cover_step p hp hc' r hr hb)
    rcases approx_unit with ⟨p,hp,hu⟩
    have approx_pos :
      ∃ p : Fin (2*n+1) → Fin n → ℝ → ℝ,
        (∀ k l, Continuous (p k l)) ∧
        (∀ (r : (Fin n → ℝ) → ℝ) (T : ℝ),
          0 < T → ContinuousOn r (Set.Icc (0 : Fin n → ℝ) 1) →
          (∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1, |r x| ≤ T) →
          ∃ A : Fin (2*n+1) → BoundedContinuousFunction ℝ ℝ,
            (∀ k, ‖A k‖ ≤ (1:ℝ) * T) ∧
            ∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1,
              |r x - ∑ k, A k (∑ l, p k l (x l))| ≤ θ*T) :=
      ⟨p,hp,KAS.normalize_step θ p hu⟩
    rcases approx_pos with ⟨p,hp,hpos⟩
    have approx :
      ∀ (r : (Fin n → ℝ) → ℝ) (T : ℝ),
          0 ≤ T → ContinuousOn r (Set.Icc (0 : Fin n → ℝ) 1) →
          (∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1, |r x| ≤ T) →
          ∃ A : Fin (2*n+1) → BoundedContinuousFunction ℝ ℝ,
            (∀ k, ‖A k‖ ≤ (1:ℝ) * T) ∧
            ∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1,
              |r x - ∑ k, A k (∑ l, p k l (x l))| ≤ θ*T := by
      intro r T hT hr hb
      rcases hT.eq_or_lt with h0 | hposT
      · subst T
        refine ⟨0, ?_, ?_⟩
        · intro k; simp
        · intro x hx
          have hz : r x = 0 := by
            have hz' : |r x| = 0 := le_antisymm (hb x hx) (abs_nonneg _)
            exact (abs_eq_zero.mp hz')
          simp [hz]
      · exact hpos r T hposT hr hb
    obtain ⟨a,ha,hfa⟩ :=
      KAS.geometric_limit_fixed_inner θ 1 R hθ0 hθ1 (by norm_num) hR
        p hp f _hf hfR approx
    have H :
        ∃ (a : Fin (2 * n + 1) → ℝ → ℝ)
          (p : Fin (2 * n + 1) → Fin n → ℝ → ℝ),
          (∀ k, Continuous (a k)) ∧ (∀ k l, Continuous (p k l)) ∧
          ∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1,
            f x = ∑ k, a k (∑ l, p k l (x l)) :=
      ⟨a,p,ha,hp,hfa⟩
    rcases H with ⟨a,p,ha,hp,hfp⟩
    obtain ⟨G,ψ,hG,hψ,hEq⟩ := KAS.merge_outer_sum _hn a ha p hp
    refine ⟨G, ψ, hG, hψ, ?_⟩
    intro x hx
    calc
      f x = ∑ k, a k (∑ l, p k l (x l)) := hfp x hx
      _ = ∑ k, G (∑ l, ψ k l (x l)) := (hEq x hx).symm
/-ResultProofEnd-/
/-ResultEnd-/
-- END INLINED FILE: Main.lean

end Submission
