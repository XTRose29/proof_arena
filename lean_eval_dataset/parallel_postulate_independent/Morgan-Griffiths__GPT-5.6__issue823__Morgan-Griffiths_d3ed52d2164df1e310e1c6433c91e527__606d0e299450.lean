import ChallengeDeps
import Mathlib

-- BEGIN INLINED FILE: Mathlib/Support/parallel_postulate_independent_6d58d2ed72/Affine.lean
section

noncomputable section
namespace LeanEval.Geometry
/-- The convex, inclusive affine betweenness in a real vector space.  The
coefficient is assigned to the *right*-hand end. -/
def AffineBetween (V : Type*) [AddCommGroup V] [Module ℝ V]
    (a b c : V) : Prop :=
    ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ b = (1-u) • a + u • c

section
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

@[simp] theorem affineBetween_left (a c : V) : AffineBetween V a a c := by
  refine ⟨0, by positivity, by norm_num, ?_⟩
  simp

@[simp] theorem affineBetween_right (a c : V) : AffineBetween V a c c := by
  refine ⟨1, by positivity, by norm_num, ?_⟩
  simp

/-- Identity of betweenness (`A6`) is just cancellation of the two barycentric
coefficients when the outer endpoints agree. -/
theorem AffineBetween.id_ax (a b : V) (h : AffineBetween V a b a) : a = b := by
  rcases h with ⟨u, hu0, hu1, rfl⟩
  -- `(1-u) a + u a = a` by linearity
  calc
    a = (1:ℝ) • a := by simp
    _ = (1-u+u) • a := by congr 1; ring
    _ = (1-u) • a + u • a := by rw [add_smul]

@[simp] theorem AffineBetween.swap (a b c : V) :
    AffineBetween V a b c ↔ AffineBetween V c b a := by
  constructor
  · rintro ⟨u, hu0, hu1, rfl⟩
    refine ⟨1-u, sub_nonneg.mpr hu1, by linarith, ?_⟩
    simp [sub_smul, add_comm]
  · rintro ⟨u, hu0, hu1, rfl⟩
    refine ⟨1-u, sub_nonneg.mpr hu1, by linarith, ?_⟩
    simp [sub_smul, add_comm]

/-- Convex-combination betweenness has Tarski's inner Pasch axiom in every
real affine space. This is the purely affine (distance-free) ingredient used
in the coordinate/Klein constructions. -/
theorem AffineBetween.inner_pasch
    (a b c p q : V)
    (hp : AffineBetween V a p c) (hq : AffineBetween V b q c) :
    ∃ x, AffineBetween V p x b ∧ AffineBetween V q x a := by
  rcases hp with ⟨u, hu0, hu1, rfl⟩
  rcases hq with ⟨v, hv0, hv1, rfl⟩
  -- The barycentric denominator `d = u + v - u*v`.  Except in the endpoint
  -- case `u=v=0`, it is positive.  The intersection is
  -- `(1-α) p + α b = (1-β) q + β a` with
  -- `1-α = v/d` and `β = (v/d)(1-u)`.
  by_cases hd : u + v - u*v = 0
  · have huv : u = 0 ∧ v = 0 := by
      have hnonneg := mul_nonneg hu0 hv0
      by_cases U : u = 0
      · have : v = 0 := by simpa [U] using hd
        exact ⟨U, this⟩
      · have up : 0 < u := lt_of_le_of_ne hu0 (Ne.symm U)
        -- rewrite d = u + v*(1-u), both summands are non-negative
        have oneu : 0 ≤ 1-u := sub_nonneg.mpr hu1
        have term : 0 ≤ v*(1-u) := mul_nonneg hv0 oneu
        have eq' : u + v*(1-u) = 0 := by linarith
        linarith
    rcases huv with ⟨rfl, rfl⟩
    -- p=a and q=b: either endpoint is an intersection
    refine ⟨a, ?_, ?_⟩ <;> simp
  · have oneu : 0 ≤ 1-u := sub_nonneg.mpr hu1
    have onev : 0 ≤ 1-v := sub_nonneg.mpr hv1
    have Dnon : 0 ≤ u + v - u*v := by nlinarith
    have Dpos : 0 < u + v - u*v := lt_of_le_of_ne Dnon (Ne.symm hd)
    let k : ℝ := v / (u + v - u*v)
    let α : ℝ := 1-k
    let β : ℝ := k*(1-u)
    have k0 : 0 ≤ k := by dsimp [k]; positivity
    have kd : k * (u + v - u*v) = v := by
      dsimp [k]
      have hden : u + v - v*u ≠ 0 := by nlinarith
      field_simp

    have k1 : k ≤ 1 := by
      apply (le_of_sub_nonneg ?_)
      -- easier from k*(...) = v and 0<=u*(1-v)
      rw [sub_nonneg]
      have : v ≤ u + v - u*v := by nlinarith
      exact (div_le_one Dpos).2 this
    have a0 : 0 ≤ α := by dsimp [α]; linarith
    have a1 : α ≤ 1 := by dsimp [α]; linarith
    have b0 : 0 ≤ β := by dsimp [β]; positivity
    have b1 : β ≤ 1 := by
      dsimp [β]
      calc
        k * (1-u) ≤ 1 * (1-u) := mul_le_mul_of_nonneg_right k1 oneu
        _ = (1-u) := one_mul _
        _ ≤ 1 := by linarith
    have id₁ : (1-α) = k := by dsimp [α]; ring
    have id₂ : (1-β)*v = k*u := by
      dsimp [β]
      nlinarith
    have id₃ : α = (1-β)*(1-v) := by
      dsimp [α, β]
      nlinarith
    -- use the first affine expression for x
    refine ⟨(1-α) • ((1-u) • a + u • c) + α • b, ?_, ?_⟩
    · exact ⟨α, a0, a1, rfl⟩
    · refine ⟨β, b0, b1, ?_⟩
      -- both expressions have the same coefficients on `a`, `b`, `c`
      -- by `id₁`–`id₃`; rearrange using `smul_smul`.
      calc
        (1 - α) • ((1 - u) • a + u • c) + α • b
            = ((1-α)*(1-u)) • a + ((1-α)*u) • c + α • b := by
                -- scalar distribution in the left affine expression
                simp [smul_add, smul_smul]
        _ = β • a + ((1-β)*v) • c + ((1-β)*(1-v)) • b := by
              -- coefficients from the solved denominator
              rw [id₁]
              rw [id₃, id₂]
        _ = (1 - β) • ((1 - v) • b + v • c) + β • a := by
              simp [smul_add, smul_smul]
              ac_rfl
end
end LeanEval.Geometry

namespace LeanEval.Geometry
noncomputable section
-- Segment extension for ordinary metric affine spaces.  Keeping this lemma
-- in naked `dist` form lets it feed structures with any packaging of the
-- metric congruence relation.
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma AffineBetween.segment_metric (a b c d : V) :
    ∃ x, AffineBetween V a b x ∧ dist b x = dist c d := by
  classical
  by_cases hab : a = b
  · subst b
    refine ⟨a + (d-c), affineBetween_left _ _, ?_⟩
    simp only [dist_eq_norm]
    -- `a - (a + ...) = -(d-c)`
    rw [sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg]
    exact norm_sub_rev _ _
  · have vne : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    have nv : 0 < ‖b-a‖ := norm_pos_iff.mpr vne
    let t : ℝ := ‖d-c‖ / ‖b-a‖
    have t0 : 0 ≤ t := by dsimp [t]; positivity
    let u : ℝ := 1 / (1 + t)
    have u0 : 0 ≤ u := by dsimp [u]; positivity
    have u1 : u ≤ 1 := by
      dsimp [u]
      exact (div_le_one (by positivity)).mpr (by linarith)
    refine ⟨b + t • (b-a), ?_, ?_⟩
    · refine ⟨u, u0, u1, ?_⟩
      dsimp [u]
      -- elementary affine arithmetic; `module` after clearing the scalar
      -- fraction avoids all vector cancellation issues.
      have den : (1+t) ≠ 0 := ne_of_gt (by linarith)
      -- write both sides after scalar cancellation
      calc
        b = a + (b-a) := by abel
        _ = a + ((1/(1+t))*(1+t)) • (b-a) := by
              rw [div_mul_cancel₀ (1:ℝ) den]
              simp
        _ = (1-(1/(1+t))) • a + (1/(1+t)) • (b + t • (b-a)) := by
              module
    · rw [dist_eq_norm, dist_eq_norm]
      -- `b - (b + tv) = -(tv)`
      rw [sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg t0]
      dsimp [t]
      field_simp
      -- denominator cancellation of the nonzero `‖b-a‖`
      exact norm_sub_rev _ _
end
end LeanEval.Geometry

namespace LeanEval.Geometry
section
/-- The usual affine plane has actual noncollinear points; unlike a pure
linear-order model this discharges the lower-dimension axiom. -/
lemma affine_plane_lower :
    ∃ a b c : ℝ × ℝ,
      ¬ AffineBetween (ℝ × ℝ) a b c ∧
      ¬ AffineBetween (ℝ × ℝ) b c a ∧
      ¬ AffineBetween (ℝ × ℝ) c a b := by
  refine ⟨(1,0), (0,1), (0,0), ?_, ?_, ?_⟩
  all_goals
    intro h
    rcases h with ⟨u, hu, hu', hEq⟩
    -- A spare coordinate suffices in each of the three cases.
    have h1 := congrArg Prod.fst hEq
    have h2 := congrArg Prod.snd hEq
    dsimp at h1 h2
  · linarith
  · linarith
  · linarith
end
end LeanEval.Geometry

namespace LeanEval.Geometry
noncomputable section
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Tarski's Euclidean (parallel) axiom for a *whole* real affine vector
space with the usual segment betweenness.  This elementary computation is
also useful in the Klein-model comparison: the step that fails in a
convex restricted carrier is that the extensions `x,y` below leave it.
The same scalar `1/u` extends both rays. -/
lemma AffineBetween.euclidean_ax
    (a b c d t : V)
    (hadt : AffineBetween V a d t)
    (hbdc : AffineBetween V b d c)
    (had : a ≠ d) :
    ∃ x y, AffineBetween V a b x ∧
      AffineBetween V a c y ∧ AffineBetween V x t y := by
  rcases hadt with ⟨u, hu0, hu1, hd⟩
  rcases hbdc with ⟨v, hv0, hv1, hd'⟩
  -- `u` cannot be zero: the first endpoint of a non-degenerate ray.
  have une : u ≠ 0 := by
    intro h
    have da : d = a := by simpa [h] using hd
    exact had da.symm
  let s : ℝ := 1 / u
  -- Extend the two rays by the *same* factor.  Their affine
  -- coefficients in `t` are then just `1-v,v`.
  let x : V := (1-s) • a + s • b
  let y : V := (1-s) • a + s • c
  have bx : b = (1-u) • a + u • x := by
    dsimp [x, s]
    -- this is module arithmetic plus the cancellation `u*(1/u)=1`.
    have us : u * (1/u) = (1:ℝ) := by field_simp
    have coeff : (1-u) + u * (1-(1/u)) = (0:ℝ) := by
      calc
        (1-u) + u * (1-(1/u)) = 1 - u*(1/u) := by ring
        _ = 0 := by rw [us]; ring
    -- expose the two coefficients of `a` and `b` explicitly before
    -- using the scalar equalities above (`module` cannot know that
    -- the variable `u` is invertible).
    calc
      b = (0:ℝ) • a + (1:ℝ) • b := by simp
      _ = ((1-u) + u * (1-(1/u))) • a + (u*(1/u)) • b := by rw [coeff, us]
      _ = (1-u) • a + u • ((1-(1/u)) • a + (1/u) • b) := by module
  have cy : c = (1-u) • a + u • y := by
    dsimp [y, s]
    have us : u * (1/u) = (1:ℝ) := by field_simp
    have coeff : (1-u) + u * (1-(1/u)) = (0:ℝ) := by
      calc
        (1-u) + u * (1-(1/u)) = 1 - u*(1/u) := by ring
        _ = 0 := by rw [us]; ring
    calc
      c = (0:ℝ) • a + (1:ℝ) • c := by simp
      _ = ((1-u) + u * (1-(1/u))) • a + (u*(1/u)) • c := by rw [coeff, us]
      _ = (1-u) • a + u • ((1-(1/u)) • a + (1/u) • c) := by module
  have dt : d = (1-u) • a + u • ((1-v) • x + v • y) := by
    -- substitute the two descriptions of `d`; both expressions have
    -- coefficients `(1-u),u*(1-v),u*v` on `a,b,c`.
    -- It is convenient to first use `hbdc` and then `bx,cy`.
    calc
      d = (1-v) • b + v • c := hd'
      _ = (1-u) • a + u • ((1-v) • x + v • y) := by
        rw [bx, cy]
        module
  have ty : t = (1-v) • x + v • y := by
    -- compare the two expressions for `d` and cancel the nonzero
    -- scalar `u`; in a module over a field it is cancellable.
    -- subtraction in the module removes the common `a` term.
    have eqs : u • (t - ((1-v) • x + v • y)) = (0 : V) := by
      -- `dt` and `hd` share the first summand
      rw [hd] at dt
      -- eliminate the common first addend
      have : u • t = u • ((1-v) • x + v • y) := by
        exact add_left_cancel dt
      -- distributivity of smul over subtraction
      simpa [smul_sub] using (sub_eq_zero.mpr this)
    have hz : t - ((1-v) • x + v • y) = (0 : V) := by
      -- scalar zero is the only way a nonzero field scalar kills a vector
      exact (smul_eq_zero.mp eqs).resolve_left une
    exact sub_eq_zero.mp hz
  refine ⟨x, y, ?_, ?_, ?_⟩
  · exact ⟨u, hu0, hu1, bx⟩
  · exact ⟨u, hu0, hu1, cy⟩
  · exact ⟨v, hv0, hv1, ty⟩
end
end LeanEval.Geometry

end

end
-- END INLINED FILE: Mathlib/Support/parallel_postulate_independent_6d58d2ed72/Affine.lean

-- BEGIN INLINED FILE: Mathlib/Support/parallel_postulate_independent_6d58d2ed72/LengthCongruence.lean
section

namespace LeanEval.Geometry

/-! If one works with a scalar ``Cayley--Klein invariant'' rather than a
`MetricSpace` instance, the first three congruence axioms do not involve any
betweenness.  This is a handy way of separating the genuinely geometric
parts of the bounded-domain construction (extension, five segment, and the
bisector theorem). We state it for an arbitrary codomain with a distinguished
zero; no metric regularity is used. -/

/-- Segment congruence from a scalar code.  In the Klein calculation `L` can
be squared hyperbolic sine/cosh, avoiding square roots. -/
def LengthCongruent {M : Type*} {R : Type*} (L : M → M → R)
    (a b c d : M) : Prop := L a b = L c d

section
variable {M : Type*} {R : Type*}
variable (L : M → M → R)

/-- Equality of a symmetric segment code gives Tarski A1. -/
lemma LengthCongruent.refl_of_symm
    (hL : ∀ a b, L a b = L b a) (a b : M) :
    LengthCongruent L a b b a := by
  exact hL _ _

/-- Equality of a code gives the transitivity axiom in the useful
orientation (no symmetry assumption is needed here). -/
lemma LengthCongruent.trans_ax' (a b c d e f : M)
    (hcd : LengthCongruent L a b c d)
    (hef : LengthCongruent L a b e f) :
    LengthCongruent L c d e f := by
  exact hcd.symm.trans hef

/-- For identity it suffices that the diagonal code is zero and that it
separates its own endpoints. This formulation is convenient for rational
cross-ratio formulae, well before a triangle inequality is available. -/
lemma LengthCongruent.id_of_zero [Zero R]
    (diag : ∀ a, L a a = 0)
    (sep : ∀ {a b}, L a b = 0 → a = b)
    (a b c : M)
    (h : LengthCongruent L a b c c) : a = b := by
  apply sep
  exact h.trans (diag _)

end
end LeanEval.Geometry

end
-- END INLINED FILE: Mathlib/Support/parallel_postulate_independent_6d58d2ed72/LengthCongruence.lean

-- BEGIN INLINED FILE: Mathlib/Support/parallel_postulate_independent_6d58d2ed72/MetricCongruence.lean
section

namespace LeanEval.Geometry

/- Squared-distances package the first three congruence axioms for analytic
models.  These tiny lemmas avoid repeatedly unfolding the congruence when
constructing affine/hyperbolic models in the worker development. -/
section
variable {M : Type*} [PseudoMetricSpace M]

/-- congruence relation obtained from the ambient metric -/
def MetricCongruent (a b c d : M) : Prop := dist a b = dist c d

theorem MetricCongruent.refl_ax (a b : M) : MetricCongruent a b b a := by
  unfold MetricCongruent
  exact dist_comm _ _

theorem MetricCongruent.trans_ax
    (a b c d e f : M)
    (h₁ : MetricCongruent a b c d) (h₂ : MetricCongruent a b e f) :
    MetricCongruent c d e f := by
  exact h₁.symm.trans h₂
end

section
variable {M : Type*} [MetricSpace M]

theorem MetricCongruent.id_ax
    (a b c : M) (h : MetricCongruent a b c c) : a = b := by
  -- a metric has no nontrivial zero-length segments
  have hz : dist a b = 0 := by simpa [MetricCongruent] using h
  exact dist_eq_zero.mp hz
end

end LeanEval.Geometry

end
-- END INLINED FILE: Mathlib/Support/parallel_postulate_independent_6d58d2ed72/MetricCongruence.lean

-- BEGIN INLINED FILE: Mathlib/Support/parallel_postulate_independent_6d58d2ed72/EuclideanInner.lean
section

namespace LeanEval.Geometry
noncomputable section
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The polarization argument needed in Tarski's five-segment lemma, isolated
from the affine bookkeeping.  An equality of the three side lengths of the
triangles `(0,v,w)` and `(0,V,W)` determines the scalar product; hence all
points at the same parameter on their base lines have the same distance to
`w` resp. `W`. -/
lemma inner_trilaterate_scalar (v w v' w' : V) (r : ℝ)
    (hv : ‖v‖ = ‖v'‖) (hw : ‖w‖ = ‖w'‖)
    (hvw : ‖v - w‖ = ‖v' - w'‖) :
    ‖r • v - w‖ = ‖r • v' - w'‖ := by
  have hv2 : inner ℝ v v = inner ℝ v' v' := by
    calc
      inner ℝ v v = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq _
      _ = ‖v'‖ ^ 2 := congrArg (fun x : ℝ => x^2) hv
      _ = inner ℝ v' v' := (real_inner_self_eq_norm_sq _).symm
  have hw2 : inner ℝ w w = inner ℝ w' w' := by
    calc
      inner ℝ w w = ‖w‖ ^ 2 := real_inner_self_eq_norm_sq _
      _ = ‖w'‖ ^ 2 := congrArg (fun x : ℝ => x^2) hw
      _ = inner ℝ w' w' := (real_inner_self_eq_norm_sq _).symm
  have hdiff : inner ℝ (v-w) (v-w) =
      inner ℝ (v'-w') (v'-w') := by
    calc
      inner ℝ (v-w) (v-w) = ‖v-w‖ ^ 2 := real_inner_self_eq_norm_sq _
      _ = ‖v'-w'‖ ^ 2 := congrArg (fun x : ℝ => x^2) hvw
      _ = inner ℝ (v'-w') (v'-w') := (real_inner_self_eq_norm_sq _).symm
  have hin : inner ℝ v w = inner ℝ v' w' := by
    simp only [inner_sub_sub_self] at hdiff
    -- over reals the two mixed terms are the same
    rw [real_inner_comm v w, real_inner_comm v' w'] at hdiff
    nlinarith
  -- expand squares of the requested pair
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  -- convert both squares to real inner products
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  -- expansion and bilinearity
  -- all scalar products are real, so no conjugates
  simp only [inner_sub_sub_self, inner_smul_left, inner_smul_right,
    conj_trivial]
  rw [real_inner_comm v w, real_inner_comm v' w']
  rw [hv2, hw2, hin]

/-- Write the right endpoint of a nontrivial affine segment in terms of the
first two points.  This is deliberately formulated in an arbitrary module;
it is the division step often hidden in paper proofs of the five-segment
axiom. -/
lemma AffineBetween.endpoint_parameter
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (a b c : W) (hab : a ≠ b)
    (h : AffineBetween W a b c) :
    ∃ k : ℝ, 1 ≤ k ∧ c = a + k • (b-a) := by
  rcases h with ⟨u, hu0, hu1, hb⟩
  have une : u ≠ 0 := by
    intro z
    have : b = a := by simpa [z] using hb
    exact hab this.symm
  have up : 0 < u := lt_of_le_of_ne hu0 (Ne.symm une)
  refine ⟨1/u, (le_div_iff₀ up).2 ?_, ?_⟩
  · simpa using hu1
  -- solve the affine equation for the other endpoint
  -- first write the equation in difference form
  have ba : b - a = u • (c - a) := by
    rw [hb]
    module
  calc
    c = a + (c-a) := by abel
    _ = a + ((1/u)*u) • (c-a) := by
          rw [div_mul_cancel₀ (1:ℝ) une]
          simp
    _ = a + (1/u) • (u • (c-a)) := by rw [smul_smul]
    _ = a + (1/u) • (b-a) := by rw [← ba]

/-- Base and outward excess of a segment at parameter `k`. -/
lemma endpoint_distances
    (a b c : V) (k : ℝ) (hk : 1 ≤ k)
    (hc : c = a + k • (b-a)) :
    dist b c = (k-1) * dist a b := by
  have k0 : 0 ≤ k-1 := sub_nonneg.mpr hk
  rw [hc, dist_eq_norm, dist_eq_norm]
  -- after rewriting vectors, this is homogeneity of the norm
  have heq : b - (a + k • (b-a)) = (1-k) • (b-a) := by module
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
  rw [show a-b = -(b-a) by module, norm_neg]
  ring

/-- Analytic five-segment axiom in a real inner product affine space, in
`dist` form. It can be used with `MetricCongruent` immediately. -/
lemma affine_inner_five_segment
    (a b c d a' b' c' d' : V) (habne : a ≠ b)
    (hbc : AffineBetween V a b c)
    (hbc' : AffineBetween V a' b' c')
    (hab : dist a b = dist a' b')
    (hbcd : dist b c = dist b' c')
    (had : dist a d = dist a' d')
    (hbd : dist b d = dist b' d') : dist c d = dist c' d' := by
  -- the first base is nonzero, so the congruent second is too
  have abpos : 0 < dist a b := dist_pos.mpr habne
  have abne' : a' ≠ b' := by
    intro e
    have : dist a b = 0 := by simpa [e] using hab
    linarith
  obtain ⟨k, hk, hc⟩ := AffineBetween.endpoint_parameter a b c habne hbc
  obtain ⟨l, hl, hc'⟩ := AffineBetween.endpoint_parameter a' b' c' abne' hbc'
  have bk : dist b c = (k-1)*dist a b :=
    endpoint_distances a b c k hk hc
  have bl : dist b' c' = (l-1)*dist a' b' :=
    endpoint_distances a' b' c' l hl hc'
  have kl : k = l := by
    rw [bk, bl, ← hab] at hbcd
    have := abpos
    nlinarith
  subst l
  -- translate everything to vectors from the first endpoints
  have tri := inner_trilaterate_scalar (b-a) (d-a) (b'-a') (d'-a') k
  have hbase : ‖b-a‖ = ‖b'-a'‖ := by
    -- orientation of `dist_eq_norm` is `a-b`, so reverse
    rw [← norm_neg (b-a), ← norm_neg (b'-a')]
    simpa [dist_eq_norm] using hab
  have hwing : ‖d-a‖ = ‖d'-a'‖ := by
    -- `had` gives `a-d`; take negatives
    simpa [dist_eq_norm, norm_sub_rev] using had
  have hop : ‖(b-a) - (d-a)‖ = ‖(b'-a') - (d'-a')‖ := by
    have e1 : b-a - (d-a) = b - d := by module
    have e2 : b'-a' - (d'-a') = b' - d' := by module
    rw [e1, e2]
    simpa [dist_eq_norm] using hbd
  have H := tri hbase hwing hop
  -- the norm vectors in `H` are just distances from `c` and `c'`
  rw [hc, hc', dist_eq_norm, dist_eq_norm]
  have e1 : (a + k • (b-a)) - d = k • (b-a) - (d-a) := by module
  have e2 : (a' + k • (b'-a')) - d' = k • (b'-a') - (d'-a') := by module
  rw [e1, e2]
  exact H

end
end LeanEval.Geometry

namespace LeanEval.Geometry
noncomputable section
open scoped RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The familiar perpendicular-bisector calculation, independent of the
ambient dimension.  Subtracting two equal-distance equations gives an
orthogonality equation on their difference. -/
lemma equidistant_orthogonal (p q a b : V)
    (ha : dist p a = dist q a) (hb : dist p b = dist q b) :
    inner ℝ (q-p) (b-a) = 0 := by
  have A : inner ℝ (p-a) (p-a) = inner ℝ (q-a) (q-a) := by
    calc
      inner ℝ (p-a) (p-a) = ‖p-a‖ ^ 2 := real_inner_self_eq_norm_sq _
      _ = ‖q-a‖ ^ 2 := congrArg (fun x : ℝ => x^2) (by simpa [dist_eq_norm] using ha)
      _ = inner ℝ (q-a) (q-a) := (real_inner_self_eq_norm_sq _).symm
  have B : inner ℝ (p-b) (p-b) = inner ℝ (q-b) (q-b) := by
    calc
      inner ℝ (p-b) (p-b) = ‖p-b‖ ^ 2 := real_inner_self_eq_norm_sq _
      _ = ‖q-b‖ ^ 2 := congrArg (fun x : ℝ => x^2) (by simpa [dist_eq_norm] using hb)
      _ = inner ℝ (q-b) (q-b) := (real_inner_self_eq_norm_sq _).symm
  -- expand both equations.  In a real inner product space the mixed
  -- terms are symmetric.
  simp only [inner_sub_sub_self] at A B
  -- also expand the target
  simp only [inner_sub_left, inner_sub_right]
  -- normalize equations in the same orientation as the target
  rw [real_inner_comm p a, real_inner_comm q a] at A
  rw [real_inner_comm p b, real_inner_comm q b] at B
  -- the self terms in `a,b` cancel between sides; subtract the two
  -- displayed equations.
  linarith

/-- Three points whose two differences from the first point are scalar
multiples have one between the other two (non-strict betweenness).  The cyclic
form is exactly what Tarski's upper-dimension axiom uses. -/
lemma affinely_collinear_of_multiple
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (a b c : W) (r : ℝ) (h : c-a = r • (b-a)) :
    AffineBetween W a b c ∨ AffineBetween W b c a ∨ AffineBetween W c a b := by
  by_cases r0 : 0 ≤ r
  · by_cases r1 : r ≤ 1
    · -- c between a,b; reverse endpoints to get the second cyclic form
      right; left
      apply (AffineBetween.swap b c a).2
      refine ⟨r, r0, r1, ?_⟩
      calc
        c = a + (c-a) := by abel
        _ = a + r • (b-a) := by rw [h]
        _ = (1-r) • a + r • b := by module
    · -- b between a,c, with parameter `1/r`
      left
      have rp : 0 < r := by linarith
      have rinv0 : 0 ≤ (1/r : ℝ) := by positivity
      have rinv1 : (1/r : ℝ) ≤ 1 := (div_le_one rp).2 (le_of_not_ge r1)
      refine ⟨1/r, rinv0, rinv1, ?_⟩
      calc
        b = a + (b-a) := by abel
        _ = a + (1/r) • (r • (b-a)) := by rw [smul_smul, div_mul_cancel₀ (1:ℝ) (ne_of_gt rp)]; simp
        _ = a + (1/r) • (c-a) := by rw [← h]
        _ = (1-(1/r)) • a + (1/r) • c := by module
  · -- a between c and b
    right; right
    have rn : r < 0 := lt_of_not_ge r0
    -- `a = (1-u)c + u b` with `u = -r/(1-r)`
    let u : ℝ := (-r) / (1-r)
    have den : 0 < 1-r := by linarith
    have u0 : 0 ≤ u := by dsimp [u]; exact div_nonneg (by linarith) (le_of_lt den)
    have u1 : u ≤ 1 := by
      dsimp [u]; exact (div_le_one den).2 (by linarith)
    refine ⟨u, u0, u1, ?_⟩
    -- substitute `c = a + r(b-a)` and clear scalar coefficients
    have hc : c = a + r • (b-a) := by
      calc c = a + (c-a) := by abel
           _ = a + r • (b-a) := by rw [h]
    rw [hc]
    have zu : (1-u)*r + u = (0:ℝ) := by
      dsimp [u]
      field_simp
      <;> ring
    calc
      a = a + (((1-u)*r + u) • (b-a)) := by rw [zu]; simp
      _ = (1-u) • (a + r • (b-a)) + u • b := by module
end
end LeanEval.Geometry

namespace LeanEval.Geometry
noncomputable section
open scoped RealInnerProductSpace
abbrev Plane2 := EuclideanSpace ℝ (Fin 2)

lemma plane2_ext {x y : Plane2}
    (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  apply PiLp.ext
  intro i
  fin_cases i <;> assumption

/-- The orthogonal complement of a nonzero vector in the coordinate plane is
one-dimensional. We give a coordinate proof to avoid any finite-dimensional
choice, which also keeps the subsequent betweenness parameter explicit. -/
lemma plane2_kernel_multiple (v w z : Plane2)
    (hv : v ≠ 0) (hw0 : w ≠ 0)
    (hw : inner ℝ v w = 0) (hz : inner ℝ v z = 0) :
    ∃ r : ℝ, z = r • w := by
  have W : v 0 * w 0 + v 1 * w 1 = 0 := by
    -- `PiLp.inner_apply` orders the real inner product oppositely; commute
    simpa [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]
      using hw
  have Z : v 0 * z 0 + v 1 * z 1 = 0 := by
    simpa [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]
      using hz
  by_cases vzero : v 0 = 0
  · have vne : v 1 ≠ 0 := by
      intro e
      apply hv
      exact plane2_ext vzero e
    have w1 : w 1 = 0 := by
      rw [vzero] at W
      -- only the second coordinate remains
      apply (mul_eq_zero.mp (by linarith : v 1 * w 1 = 0)).resolve_left vne
    have z1 : z 1 = 0 := by
      rw [vzero] at Z
      apply (mul_eq_zero.mp (by linarith : v 1 * z 1 = 0)).resolve_left vne
    have wne : w 0 ≠ 0 := by
      intro e
      apply hw0
      exact plane2_ext e w1
    refine ⟨z 0 / w 0, ?_⟩
    apply plane2_ext
    · change z 0 = (z 0 / w 0) * w 0
      exact (div_mul_cancel₀ _ wne).symm
    · change z 1 = (z 0 / w 0) * w 1
      simp [w1, z1]
  · -- here the first component of every orthogonal vector is fixed by its
    -- second.  A nonzero such vector has nonzero second component.
    have wne : w 1 ≠ 0 := by
      intro e
      have f : w 0 = 0 := by
        rw [e] at W
        apply (mul_eq_zero.mp (by linarith : v 0 * w 0 = 0)).resolve_left vzero
      apply hw0
      exact plane2_ext f e
    refine ⟨z 1 / w 1, ?_⟩
    apply plane2_ext
    · -- solve the first coordinate using the two orthogonality equations
      change z 0 = (z 1 / w 1) * w 0
      have id : z 0 * w 1 = z 1 * w 0 := by
        -- eliminate the nonzero `v 0`
        have : v 0 * (z 0 * w 1 - z 1 * w 0) = 0 := by
          linear_combination w 1 * Z - z 1 * W
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left vzero)
      calc
        z 0 = (z 0 * w 1) / w 1 := by field_simp
        _ = (z 1 * w 0) / w 1 := by rw [id]
        _ = (z 1 / w 1) * w 0 := by ring
    · change z 1 = (z 1 / w 1) * w 1
      exact (div_mul_cancel₀ _ wne).symm

/-- Upper-dimension axiom for the real coordinate plane, in analytic form. -/
lemma plane2_upper
    (a b c p q : Plane2) (hpq : p ≠ q)
    (ha : dist p a = dist q a)
    (hb : dist p b = dist q b)
    (hc : dist p c = dist q c) :
    AffineBetween Plane2 a b c ∨ AffineBetween Plane2 b c a ∨
      AffineBetween Plane2 c a b := by
  by_cases hba : b = a
  · subst b
    left
    exact affineBetween_left _ _
  have horth1 : inner ℝ (q-p) (b-a) = 0 :=
    equidistant_orthogonal p q a b ha hb
  have horth2 : inner ℝ (q-p) (c-a) = 0 :=
    equidistant_orthogonal p q a c ha hc
  have vp : (q-p : Plane2) ≠ 0 := sub_ne_zero.mpr hpq.symm
  have wp : (b-a : Plane2) ≠ 0 := sub_ne_zero.mpr hba
  obtain ⟨r, hr⟩ := plane2_kernel_multiple (q-p) (b-a) (c-a)
    vp wp horth1 horth2
  exact affinely_collinear_of_multiple a b c r hr
end
end LeanEval.Geometry

namespace LeanEval.Geometry
noncomputable section
open scoped RealInnerProductSpace
/-- Non-collinear coordinate vertices for the Hilbert norm plane. -/
lemma plane2_lower :
    ∃ a b c : Plane2,
      ¬ AffineBetween Plane2 a b c ∧
      ¬ AffineBetween Plane2 b c a ∧
      ¬ AffineBetween Plane2 c a b := by
  let A : Plane2 := EuclideanSpace.single (𝕜:=ℝ) (0 : Fin 2) 1
  let B : Plane2 := EuclideanSpace.single (𝕜:=ℝ) (1 : Fin 2) 1
  let Z : Plane2 := 0
  refine ⟨A, B, Z, ?_, ?_, ?_⟩
  all_goals
    intro h
    rcases h with ⟨u, hu, hu', hEq⟩
    have h0 := congrArg (fun v : Plane2 => v 0) hEq
    have h1 := congrArg (fun v : Plane2 => v 1) hEq
    dsimp [A, B, Z] at h0 h1
    simp at h0 h1
  · linarith
end
end LeanEval.Geometry

end
-- END INLINED FILE: Mathlib/Support/parallel_postulate_independent_6d58d2ed72/EuclideanInner.lean

-- BEGIN INLINED FILE: Mathlib/Support/parallel_postulate_independent_6d58d2ed72/KleinLengthBasic.lean
section

/-!
Elementary part of the Klein metric.  This file is deliberately parameterised by an
inner product space; no argument here uses coordinates of the plane.  To use it in
coordinates one simply takes `V = EuclideanSpace ℝ (Fin 2)`.  The point set of the
open ball, its (inclusive) affine betweenness relation, and the convenient segment
code `sinh(d)^2` are named explicitly below.
-/
noncomputable section
namespace LeanEval.Geometry
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Points of the open Klein ball. We use the square of the norm; it is the
form in which the projective formula has no square roots. -/
def GenericKleinDisk (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] :=
  {x : V // inner ℝ x x < 1}

/-- Chords, with the ordinary inclusive affine parameter. -/
def GenericKleinBetween (a b c : GenericKleinDisk V) : Prop :=
  AffineBetween V a.1 b.1 c.1

/-- `sinh d` squared on the Klein ball.  This is monotone in the true distance,
so that equality, zeroes and constructing a point on a ray can be performed
without any logarithms or square roots in the distance itself. -/
def GenericKleinLength (a b : GenericKleinDisk V) : ℝ :=
  (1 - inner ℝ a.1 b.1)^2 /
      ((1 - inner ℝ a.1 a.1) * (1 - inner ℝ b.1 b.1)) - 1

@[simp] lemma klein_inner_lt_one (a : GenericKleinDisk V) : inner ℝ a.1 a.1 < 1 := a.2
lemma klein_one_sub_pos (a : GenericKleinDisk V) : 0 < 1 - inner ℝ a.1 a.1 := sub_pos.mpr a.2

lemma GenericKleinLength.symm (a b : GenericKleinDisk V) :
    GenericKleinLength a b = GenericKleinLength b a := by
  unfold GenericKleinLength
  rw [real_inner_comm a.1 b.1]
  rw [mul_comm]

@[simp] lemma GenericKleinLength.diag (a : GenericKleinDisk V) : GenericKleinLength a a = 0 := by
  unfold GenericKleinLength
  have h : 1 - inner ℝ a.1 a.1 ≠ 0 := ne_of_gt (klein_one_sub_pos a)
  field_simp
  ring

/-- The elementary two identities used repeatedly with the projective
formula.  If `s=<a,a>`, `t=<b,b>`, `i=<a,b>`, the Cauchy determinant is at
most `s*D` where `D=<a-b,a-b>`, and is nonnegative. -/
lemma klein_det_bounds (a b : GenericKleinDisk V) :
    let s := inner ℝ a.1 a.1
    let t := inner ℝ b.1 b.1
    let i := inner ℝ a.1 b.1
    let D := inner ℝ (a.1-b.1) (a.1-b.1)
    let E := s*t - i^2
    0 ≤ E ∧ E ≤ s*D ∧ D = s+t-2*i := by
  dsimp
  have C := real_inner_mul_inner_self_le a.1 b.1
  have Dexpand : inner ℝ (a.1 - b.1) (a.1 - b.1) =
        inner ℝ a.1 a.1 + inner ℝ b.1 b.1 - 2 * inner ℝ a.1 b.1 := by
    simp only [inner_sub_sub_self]
    rw [real_inner_comm b.1 a.1]
    ring
  constructor
  · nlinarith
  constructor
  · have sq : 0 ≤ (inner ℝ a.1 a.1 - inner ℝ a.1 b.1)^2 := sq_nonneg _
    rw [Dexpand]
    nlinarith
  · exact Dexpand

lemma GenericKleinLength.nonneg (a b : GenericKleinDisk V) : 0 ≤ GenericKleinLength a b := by
  classical
  have hbounds := klein_det_bounds a b
  dsimp at hbounds
  rcases hbounds with ⟨hE,hED,hD⟩
  have hs0 : 0 ≤ inner ℝ a.1 a.1 := real_inner_self_nonneg
  have hs1 : inner ℝ a.1 a.1 < 1 := a.2
  have ht1 : inner ℝ b.1 b.1 < 1 := b.2
  have hd0 : 0 ≤ inner ℝ (a.1-b.1) (a.1-b.1) := real_inner_self_nonneg
  have hDE : inner ℝ a.1 a.1 * inner ℝ b.1 b.1 -
        (inner ℝ a.1 b.1)^2 ≤ inner ℝ (a.1-b.1) (a.1-b.1) := by
    calc
      _ ≤ inner ℝ a.1 a.1 * inner ℝ (a.1-b.1) (a.1-b.1) := hED
      _ ≤ 1 * inner ℝ (a.1-b.1) (a.1-b.1) :=
        mul_le_mul_of_nonneg_right (le_of_lt hs1) hd0
      _ = _ := by ring
  have num : 0 ≤ (1 - inner ℝ a.1 b.1)^2 -
      (1 - inner ℝ a.1 a.1) * (1 - inner ℝ b.1 b.1) := by
    nlinarith
  -- divide by the positive denominator
  unfold GenericKleinLength
  have den : 0 < (1 - inner ℝ a.1 a.1) * (1 - inner ℝ b.1 b.1) :=
    mul_pos (sub_pos.mpr hs1) (sub_pos.mpr ht1)
  apply (sub_nonneg).2
  exact (le_div_iff₀ den).2 (by nlinarith)

/-- Zero Klein distance separates points.  One does not need equality in
Cauchy--Schwarz: the stronger inequality `E ≤ sD` and `s<1` immediately
force `D=0`. -/
theorem GenericKleinLength.eq_of_zero {a b : GenericKleinDisk V}
    (h : GenericKleinLength a b = 0) : a = b := by
  classical
  have hbounds := klein_det_bounds a b
  dsimp at hbounds
  rcases hbounds with ⟨hE,hED,hD⟩
  have hs0 : 0 ≤ inner ℝ a.1 a.1 := real_inner_self_nonneg
  have hs1 : inner ℝ a.1 a.1 < 1 := a.2
  have ht1 : inner ℝ b.1 b.1 < 1 := b.2
  have hd0 : 0 ≤ inner ℝ (a.1-b.1) (a.1-b.1) := real_inner_self_nonneg
  have den : 0 < (1 - inner ℝ a.1 a.1) * (1 - inner ℝ b.1 b.1) :=
    mul_pos (sub_pos.mpr hs1) (sub_pos.mpr ht1)
  have equation : (1 - inner ℝ a.1 b.1)^2 =
      (1-inner ℝ a.1 a.1)*(1-inner ℝ b.1 b.1) := by
    unfold GenericKleinLength at h
    have h' : (1 - inner ℝ a.1 b.1)^2 /
          ((1-inner ℝ a.1 a.1)*(1-inner ℝ b.1 b.1)) = 1 := by linarith
    simpa using (div_eq_iff (ne_of_gt den)).mp h'
  have DE : inner ℝ (a.1-b.1) (a.1-b.1) =
          inner ℝ a.1 a.1 * inner ℝ b.1 b.1 -
            (inner ℝ a.1 b.1)^2 := by
    nlinarith
  have Dzero : inner ℝ (a.1-b.1) (a.1-b.1) = 0 := by
    nlinarith
  have vzero : a.1-b.1 = 0 := (inner_self_eq_zero).mp Dzero
  apply Subtype.ext
  exact sub_eq_zero.mp vzero

/-! We next isolate the only ingredient for segment construction: every ray
from an interior point has an endpoint on the unit sphere. The existence
proof, via a quadratic and the intermediate value theorem, works in every
real inner product space. The vector for the ray will always be `b-a`; when
`a=b` one supplies any nonzero direction separately. -/

/-- Endpoint lemma.  Starting from `b` in an interior ball and a nonzero
vector `v`, there are a positive parameter `α` and `e=b+αv` on the sphere. -/
lemma klein_ray_endpoint (b : GenericKleinDisk V) {v : V} (hv : v ≠ 0) :
    ∃ α : ℝ, 0 < α ∧ inner ℝ (b.1 + α • v) (b.1 + α • v) = 1 := by
  classical
  let A : ℝ := inner ℝ v v
  have Apos : 0 < A := (real_inner_self_pos).2 hv
  let q : ℝ := inner ℝ b.1 v
  -- a very large parameter; its clumsy shape avoids any formula for the
  -- quadratic root and gives especially easy lower estimates.
  let T : ℝ := (2 * |q| + 2) / A + 2
  have Tpos : 0 < T := by
    dsimp [T]
    positivity
  have Tge : 2 ≤ T := by
    dsimp [T]
    have : 0 ≤ (2 * |q| + 2) / A := by positivity
    linarith
  let F : ℝ → ℝ := fun s => inner ℝ (b.1 + s • v) (b.1 + s • v)
  have F_cont : Continuous F := by
    dsimp [F]
    fun_prop
  have F_formula (s:ℝ) : F s = inner ℝ b.1 b.1 + 2*s*q + s^2*A := by
    dsimp [F, q, A]
    -- expansion in a real inner-product space
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, conj_trivial]
    rw [real_inner_comm v b.1]
    ring
  have F0 : F 0 < 1 := by simpa [F_formula] using b.2
  have FT : 1 ≤ F T := by
    have habs : -|q| ≤ q := neg_abs_le _
    have hx : 2*|q| + 2 < T*A := by
      dsimp [T]
      have : A ≠ 0 := ne_of_gt Apos
      field_simp
      nlinarith
    have hnon : 0 ≤ inner ℝ b.1 b.1 := real_inner_self_nonneg
    rw [F_formula]
    have htp := Tpos
    nlinarith
  have Lone : (1:ℝ) ∈ Set.Icc (F 0) (F T) := ⟨le_of_lt F0, FT⟩
  have hit := intermediate_value_Icc (show (0:ℝ) ≤ T from le_of_lt Tpos)
      F_cont.continuousOn Lone
  rcases hit with ⟨α, hαI, hαval⟩
  have αpos : 0 < α := by
    rcases hαI with ⟨α0, αT⟩
    by_contra hh
    have az : α = 0 := le_antisymm (not_lt.mp hh) α0
    have : F 0 = 1 := by simpa [az] using hαval
    linarith
  refine ⟨α, αpos, ?_⟩
  exact hαval

/-- A boundary point cannot make angle 0 with an interior point. This strict
inequality is what keeps the final rational equation nonsingular. -/
lemma klein_inner_boundary_lt_one (b : GenericKleinDisk V) (e : V)
    (he : inner ℝ e e = 1) : inner ℝ b.1 e < 1 := by
  have C := real_inner_mul_inner_self_le b.1 e
  rw [he, mul_one] at C
  have sb : inner ℝ b.1 b.1 < 1 := b.2
  by_contra h
  have h' : (1:ℝ) ≤ inner ℝ b.1 e := not_lt.mp h
  have sq : 1 ≤ inner ℝ b.1 e * inner ℝ b.1 e := by nlinarith
  nlinarith

/-- Along the chord `x=(1-u)b+u e`, from an interior point to a boundary
point, all proper parameters are interior. This algebraic proof of
convexity is included to avoid carrying a topology on the subtype. -/
lemma klein_chord_mem (b : GenericKleinDisk V) {e : V}
    (he : inner ℝ e e = 1) {u : ℝ} (hu : 0 ≤ u) (hu' : u < 1) :
    inner ℝ ((1-u) • b.1 + u • e) ((1-u) • b.1 + u • e) < 1 := by
  have sb := b.2
  have ub : 0 ≤ 1-u := sub_nonneg.mpr (le_of_lt hu')
  have hbe := klein_inner_boundary_lt_one b e he
  -- expansion and strict convexity. The cross term has coefficient ≥0 and
  -- can be replaced by 1; one of the `(1-u)^2` terms is already strict.
  have expand : inner ℝ ((1-u) • b.1 + u • e) ((1-u) • b.1 + u • e) =
        (1-u)^2 * inner ℝ b.1 b.1 + 2*u*(1-u)*inner ℝ b.1 e + u^2 := by
    -- expand bilinearly; `he` removes the `e,e` term
    simp only [inner_add_left,inner_add_right,inner_smul_left,inner_smul_right, conj_trivial]
    rw [real_inner_comm e b.1, he]
    ring
  rw [expand]
  -- Keep a positive coefficient, and use `sb` on `(1-u)^2`; this coefficient
  -- is nonzero since `u<1`.
  have coeffpos : 0 < (1-u)^2 := by
    have : 0 < 1-u := sub_pos.mpr hu'
    positivity
  have hcross : 0 ≤ 2*u*(1-u) := by positivity
  nlinarith

/-- Closed expression for the length on one such boundary chord. -/
lemma klein_length_on_chord (b : GenericKleinDisk V) (e : V)
    (he : inner ℝ e e = 1) {u : ℝ} (hu : 0 ≤ u) (hu' : u < 1) :
    let x : GenericKleinDisk V :=
      ⟨(1-u) • b.1 + u • e, klein_chord_mem b he hu hu'⟩
    GenericKleinLength b x =
      (u*(1-inner ℝ b.1 e))^2 /
        (((1-u)*(1-inner ℝ b.1 b.1)) *
          ((1-u)*(1-inner ℝ b.1 b.1) + 2*u*(1-inner ℝ b.1 e))) := by
  dsimp
  classical
  have hb : 0 < 1-inner ℝ b.1 b.1 := klein_one_sub_pos b
  have hbe : 0 < 1-inner ℝ b.1 e := sub_pos.mpr (klein_inner_boundary_lt_one b e he)
  have Apos : 0 < (1-u)*(1-inner ℝ b.1 b.1) :=
    mul_pos (sub_pos.mpr hu') hb
  have Dpos : 0 < (1-u)*(1-inner ℝ b.1 b.1) + 2*u*(1-inner ℝ b.1 e) := by
    have : 0 ≤ 2*u*(1-inner ℝ b.1 e) := by positivity
    linarith
  unfold GenericKleinLength
  -- two one-line expansions. They are named: exposing exactly these
  -- factors makes `field_simp; ring` robust.
  have hxinner : inner ℝ b.1 ((1 - u) • b.1 + u • e) =
        (1-u)*inner ℝ b.1 b.1 + u*inner ℝ b.1 e := by
    simp [inner_add_right, inner_smul_right]
  have hxx : 1 - inner ℝ ((1 - u) • b.1 + u • e)
                    ((1 - u) • b.1 + u • e) =
        (1-u) * ((1-u)*(1-inner ℝ b.1 b.1)+2*u*(1-inner ℝ b.1 e)) := by
    -- expand with `he`
    simp only [inner_add_left,inner_add_right,inner_smul_left,inner_smul_right, conj_trivial]
    rw [real_inner_comm e b.1, he]
    ring
  rw [hxinner, hxx]
  have hne1 : 1 - inner ℝ b.1 b.1 ≠ 0 := ne_of_gt hb
  have hnA : (1 - u) * (1 - inner ℝ b.1 b.1) ≠ 0 := ne_of_gt Apos
  have hnD : (1-u)*(1-inner ℝ b.1 b.1)+2*u*(1-inner ℝ b.1 e) ≠ 0 :=
    ne_of_gt Dpos
  have hneU : 1-u ≠ 0 := ne_of_gt (sub_pos.mpr hu')
  field_simp
  ring

/-- Solve the one-variable Klein chord equation at any prescribed nonnegative
length.  The useful substitution is `z = u D/(1-u)`: the length becomes
`z²/(1+2z)`. -/
lemma klein_solve_chord (b : GenericKleinDisk V) (e : V)
    (he : inner ℝ e e = 1) (r : ℝ) (hr : 0 ≤ r) :
    ∃ (u : ℝ) (u0 : 0 ≤ u) (u1 : u < 1),
      let x : GenericKleinDisk V :=
        ⟨(1-u) • b.1 + u • e, klein_chord_mem b he u0 u1⟩
      GenericKleinLength b x = r := by
  classical
  have hb : 0 < 1-inner ℝ b.1 b.1 := klein_one_sub_pos b
  have hbe : 0 < 1-inner ℝ b.1 e := sub_pos.mpr (klein_inner_boundary_lt_one b e he)
  -- Every z≥0 has z²/(1+2z)=r.
  let z : ℝ := r + Real.sqrt (r^2+r)
  have zs0 : 0 ≤ Real.sqrt (r^2+r) := Real.sqrt_nonneg _
  have inside : 0 ≤ r^2+r := by nlinarith
  have z0 : 0 ≤ z := by dsimp [z]; linarith
  have zquad : z^2 = r*(1+2*z) := by
    dsimp [z]
    have es := Real.sq_sqrt inside
    nlinarith
  let d : ℝ := (1-inner ℝ b.1 e) / (1-inner ℝ b.1 b.1)
  have dpos : 0 < d := div_pos hbe hb
  let u : ℝ := z / (d+z)
  have dzpos : 0 < d+z := by linarith
  have u0 : 0 ≤ u := by dsimp [u]; positivity
  have u1 : u < 1 := by
    dsimp [u]
    exact (div_lt_one dzpos).2 (by linarith)
  refine ⟨u, u0, u1, ?_⟩
  dsimp
  -- Insert the closed length expression; dividing by the known factors
  -- leaves exactly `zquad`.
  rw [klein_length_on_chord b e he u0 u1]
  dsimp [u, d] at *
  let A : ℝ := 1 - inner ℝ b.1 b.1
  let B : ℝ := 1 - inner ℝ b.1 e
  have Apos : 0 < A := by simpa [A] using hb
  have Bpos : 0 < B := by simpa [B] using hbe
  have A0 : A ≠ 0 := ne_of_gt Apos
  have B0 : B ≠ 0 := ne_of_gt Bpos
  -- after unfolding the substitution the expression has no geometry left.
  change (z / (B/A + z) * B)^2 /
    ((1-z/(B/A+z))*A * ((1-z/(B/A+z))*A + 2*(z/(B/A+z))*B)) = r
  have BApos : 0 < B + z*A := by positivity
  have BA0 : B + z*A ≠ 0 := ne_of_gt BApos
  have frac : z / (B/A+z) = z*A/(B+z*A) := by
    field_simp
  rw [frac]
  have subfrac : 1 - z*A/(B+z*A) = B/(B+z*A) := by
    apply (eq_div_iff BA0).2
    field_simp
    ring
  rw [subfrac]
  have denBig : (B/(B+z*A))*A *
        ((B/(B+z*A))*A + 2*(z*A/(B+z*A))*B) ≠ 0 := by
    have f1 : 0 < B/(B+z*A)*A := by positivity
    have f2 : 0 < B/(B+z*A)*A + 2*(z*A/(B+z*A))*B := by
      have : 0 ≤ 2*(z*A/(B+z*A))*B := by positivity
      linarith
    exact mul_ne_zero (ne_of_gt f1) (ne_of_gt f2)
  apply (div_eq_iff denBig).2
  field_simp
  nlinarith


/-- Segment construction on a nontrivial ray, with an arbitrary chosen
length code. -/
lemma klein_extend_nontrivial (a b : GenericKleinDisk V) (hab : a ≠ b)
    (r : ℝ) (hr : 0 ≤ r) :
    ∃ x : GenericKleinDisk V, GenericKleinBetween a b x ∧ GenericKleinLength b x = r := by
  classical
  have vv : b.1 - a.1 ≠ 0 := sub_ne_zero.mpr (fun h => hab (Subtype.ext h.symm))
  obtain ⟨α, αpos, hα⟩ := klein_ray_endpoint b vv
  let e : V := b.1 + α • (b.1-a.1)
  have ee : inner ℝ e e = 1 := by simpa [e] using hα
  obtain ⟨u, u0, u1, hlen⟩ := klein_solve_chord b e ee r hr
  let x : GenericKleinDisk V :=
    ⟨(1-u) • b.1 + u • e, klein_chord_mem b ee u0 u1⟩
  refine ⟨x, ?_, ?_⟩
  · -- `x=b+t(b-a)`; solve for the affine coefficient witnessing `a--b--x`.
    have t0 : 0 ≤ u*α := mul_nonneg u0 (le_of_lt αpos)
    let k : ℝ := 1/(1+u*α)
    have denp : 0 < 1+u*α := by linarith
    have k0 : 0 ≤ k := by dsimp [k]; positivity
    have k1 : k ≤ 1 := by
      dsimp [k]
      exact (div_le_one denp).2 (by linarith)
    unfold GenericKleinBetween
    refine ⟨k, k0, k1, ?_⟩
    change b.1 = (1-k) • a.1 + k • x.1
    dsimp [x,e,k]
    have den_ne : 1 + u*α ≠ 0 := ne_of_gt denp
    -- clear scalar coefficient in a module by preparing the scalar identity;
    -- `module` afterwards only sees polynomial arithmetic.
    have kk : (1/(1+u*α))*(1+u*α)=1 := by
      field_simp
    -- module works directly after the single scalar cancellation
    calc
      b.1 = a.1 + (b.1-a.1) := by abel
      _ = a.1 + ((1/(1+u*α))*(1+u*α)) • (b.1-a.1) := by rw [kk]; simp
      _ = (1-1/(1+u*α)) • a.1 +
           (1/(1+u*α)) • ((1-u) • b.1 +
                 u • (b.1 + α • (b.1-a.1))) := by module
  · exact hlen

/-- A convenient direction at a degenerate initial segment.  The only
hypothesis is existence of one unit vector; in the plane the first basis
vector will do. -/
lemma klein_extend_equal (b : GenericKleinDisk V)
    {e₀ : V} (ee₀ : inner ℝ e₀ e₀ = 1)
    (r : ℝ) (hr : 0 ≤ r) :
    ∃ x : GenericKleinDisk V, GenericKleinBetween b b x ∧ GenericKleinLength b x = r := by
  classical
  have nz : e₀ ≠ 0 := by
    intro h; rw [h] at ee₀; simpa using ee₀
  obtain ⟨α, αpos, hα⟩ := klein_ray_endpoint b nz
  let e : V := b.1 + α • e₀
  have ee : inner ℝ e e = 1 := by simpa [e] using hα
  obtain ⟨u, u0, u1, hlen⟩ := klein_solve_chord b e ee r hr
  let x : GenericKleinDisk V := ⟨(1-u) • b.1 + u • e,
    klein_chord_mem b ee u0 u1⟩
  refine ⟨x, ?_, hlen⟩
  unfold GenericKleinBetween
  exact affineBetween_left _ _

/-- Generic A4 for the Klein segment code. Supplying a single unit vector is
slightly more general than assuming a coordinate presentation of the plane,
and enough for all finite-dimensional nonzero models. -/
theorem klein_segment_construction
    (e₀ : V) (ee₀ : inner ℝ e₀ e₀ = 1)
    (a b c d : GenericKleinDisk V) :
    ∃ x : GenericKleinDisk V, GenericKleinBetween a b x ∧ GenericKleinLength b x = GenericKleinLength c d := by
  classical
  have hr := GenericKleinLength.nonneg c d
  by_cases h : a = b
  · subst a
    exact klein_extend_equal b ee₀ (GenericKleinLength c d) hr
  · exact klein_extend_nontrivial a b h (GenericKleinLength c d) hr

end LeanEval.Geometry

end

end
-- END INLINED FILE: Mathlib/Support/parallel_postulate_independent_6d58d2ed72/KleinLengthBasic.lean

-- BEGIN INLINED FILE: Mathlib/Support/parallel_postulate_independent_6d58d2ed72/SquareFailure.lean
section
namespace LeanEval.Geometry
noncomputable section
/-- A particularly convenient bounded convex domain.  Its chords have the
same affine betweenness as the Klein disk; using a square makes the elementary
parallel-postulate counterexample rational. Congruence is deliberately not
chosen here. -/
def OpenSquare := {p : ℝ × ℝ //
  -1 < p.1 ∧ p.1 < 1 ∧ -1 < p.2 ∧ p.2 < 1}

def SquareBetween (a b c : OpenSquare) : Prop :=
  AffineBetween (ℝ × ℝ) a.1 b.1 c.1

lemma square_point (x y : ℝ)
    (x0 : -1 < x) (x1 : x < 1) (y0 : -1 < y) (y1 : y < 1) :
    ((x,y) : ℝ × ℝ) ∈ {p | -1 < p.1 ∧ p.1 < 1 ∧ -1 < p.2 ∧ p.2 < 1} :=
  ⟨x0,x1,y0,y1⟩

/-- No choice of congruence can make the chord betweenness of a bounded
square Euclidean. This clean rational witness is the affine obstruction in
the Klein model: the ray intersections required by A10 fall outside the
carrier. -/
lemma square_not_parallel :
  ¬ (∀ a b c d t : OpenSquare,
    SquareBetween a d t → SquareBetween b d c → a ≠ d →
    ∃ x y : OpenSquare, SquareBetween a b x ∧
      SquareBetween a c y ∧ SquareBetween x t y) := by
  let A : OpenSquare := ⟨(0,0), by norm_num⟩
  let B : OpenSquare := ⟨(-(9/10:ℝ), (1/2:ℝ)), by norm_num⟩
  let C : OpenSquare := ⟨((9/10:ℝ), (1/2:ℝ)), by norm_num⟩
  let D : OpenSquare := ⟨((0:ℝ), (1/2:ℝ)), by norm_num⟩
  let T : OpenSquare := ⟨((0:ℝ), (9/10:ℝ)), by norm_num⟩
  intro H
  have Hadt : SquareBetween A D T := by
    refine ⟨5/9, by norm_num, by norm_num, ?_⟩
    ext <;> norm_num [A, D, T] <;> ring
  have Hbdc : SquareBetween B D C := by
    refine ⟨1/2, by norm_num, by norm_num, ?_⟩
    ext <;> norm_num [B, C, D] <;> ring
  have Had : A ≠ D := by
    intro e
    have q := congrArg (fun z : OpenSquare => z.1.2) e
    norm_num [A,D] at q
  obtain ⟨x,y,hx,hy,hxy⟩ := H A B C D T Hadt Hbdc Had
  rcases hx with ⟨u, u0, u1, hx⟩
  rcases hy with ⟨w, w0, w1, hy⟩
  rcases hxy with ⟨v, v0, v1, hv⟩
  have hx1 := congrArg Prod.fst hx
  have hx2 := congrArg Prod.snd hx
  have hy1 := congrArg Prod.fst hy
  have hy2 := congrArg Prod.snd hy
  have ht2 := congrArg Prod.snd hv
  -- coordinates of `x` and `y`; the origin endpoint deletes the other
  -- affine coefficient
  change -(9/10:ℝ) = (1-u) * 0 + u * x.1.1 at hx1
  change (1/2:ℝ) = (1-u) * 0 + u * x.1.2 at hx2
  change (9/10:ℝ) = (1-w) * 0 + w * y.1.1 at hy1
  change (1/2:ℝ) = (1-w) * 0 + w * y.1.2 at hy2
  change (9/10:ℝ) = (1-v) * x.1.2 + v * y.1.2 at ht2
  rcases x.2 with ⟨xlo,xhi,xlo',xhi'⟩
  rcases y.2 with ⟨ylo,yhi,ylo',yhi'⟩
  have up : 0 < u := by
    by_contra n
    have : u = 0 := le_antisymm (le_of_not_gt n) u0
    rw [this] at hx1
    norm_num at hx1
  have wp : 0 < w := by
    by_contra n
    have : w = 0 := le_antisymm (le_of_not_gt n) w0
    rw [this] at hy1
    norm_num at hy1
  have ub : 9/10 < u := by nlinarith [mul_pos up (show 0 < x.1.1 + 1 by linarith)]
  have wb : 9/10 < w := by nlinarith [mul_pos wp (show 0 < 1 - y.1.1 by linarith)]
  have xpos : 0 < x.1.2 := by nlinarith
  have ypos : 0 < y.1.2 := by nlinarith
  have xl : x.1.2 < 5/9 := by nlinarith
  have yl : y.1.2 < 5/9 := by nlinarith
  have comb : (1-v)*x.1.2 + v*y.1.2 < 5/9 := by
    by_cases z : v = 0
    · simpa [z] using xl
    by_cases o : v = 1
    · simpa [o] using yl
    have vp : 0 < v := lt_of_le_of_ne v0 (Ne.symm z)
    have op : 0 < 1-v := sub_pos.mpr (lt_of_le_of_ne v1 o)
    have h1 := mul_lt_mul_of_pos_left xl op
    have h2 := mul_lt_mul_of_pos_left yl vp
    linarith
  linarith
end
end LeanEval.Geometry

namespace LeanEval.Geometry
noncomputable section
lemma squareBetween_id (a b : OpenSquare) (h : SquareBetween a b a) : a = b := by
  apply Subtype.ext
  exact AffineBetween.id_ax _ _ h

@[simp] lemma squareBetween_left (a b : OpenSquare) : SquareBetween a a b :=
  affineBetween_left _ _
@[simp] lemma squareBetween_right (a b : OpenSquare) : SquareBetween a b b :=
  affineBetween_right _ _

/-- Chord intersections stay in the open square by convexity. -/
lemma square_combo_mem (a b : OpenSquare) {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    ∃ x : OpenSquare, x.1 = (1-u) • a.1 + u • b.1 := by
  have om : 0 ≤ 1-u := sub_nonneg.mpr h1
  have lo0 : -1 < (1-u)*a.1.1 + u*b.1.1 := by
    rcases a.2 with ⟨a0,a1,a2,a3⟩
    rcases b.2 with ⟨b0,b1,b2,b3⟩
    by_cases z : u = 0
    · simpa [z] using a0
    by_cases o : u = 1
    · simpa [o] using b0
    have up : 0 < u := lt_of_le_of_ne h0 (Ne.symm z)
    have op : 0 < 1-u := sub_pos.mpr (lt_of_le_of_ne h1 o)
    nlinarith
  have hi0 : (1-u)*a.1.1 + u*b.1.1 < 1 := by
    rcases a.2 with ⟨a0,a1,a2,a3⟩
    rcases b.2 with ⟨b0,b1,b2,b3⟩
    by_cases z : u = 0
    · simpa [z] using a1
    by_cases o : u = 1
    · simpa [o] using b1
    have up : 0 < u := lt_of_le_of_ne h0 (Ne.symm z)
    have op : 0 < 1-u := sub_pos.mpr (lt_of_le_of_ne h1 o)
    nlinarith
  have lo1 : -1 < (1-u)*a.1.2 + u*b.1.2 := by
    rcases a.2 with ⟨a0,a1,a2,a3⟩
    rcases b.2 with ⟨b0,b1,b2,b3⟩
    by_cases z : u = 0
    · simpa [z] using a2
    by_cases o : u = 1
    · simpa [o] using b2
    have up : 0 < u := lt_of_le_of_ne h0 (Ne.symm z)
    have op : 0 < 1-u := sub_pos.mpr (lt_of_le_of_ne h1 o)
    nlinarith
  have hi1 : (1-u)*a.1.2 + u*b.1.2 < 1 := by
    rcases a.2 with ⟨a0,a1,a2,a3⟩
    rcases b.2 with ⟨b0,b1,b2,b3⟩
    by_cases z : u = 0
    · simpa [z] using a3
    by_cases o : u = 1
    · simpa [o] using b3
    have up : 0 < u := lt_of_le_of_ne h0 (Ne.symm z)
    have op : 0 < 1-u := sub_pos.mpr (lt_of_le_of_ne h1 o)
    nlinarith
  refine ⟨⟨((1-u)*a.1.1 + u*b.1.1, (1-u)*a.1.2 + u*b.1.2),
    ⟨lo0, hi0, lo1, hi1⟩⟩, ?_⟩
  rfl

lemma square_inner_pasch (a b c p q : OpenSquare)
    (ha : SquareBetween a p c) (hb : SquareBetween b q c) :
    ∃ x : OpenSquare, SquareBetween p x b ∧ SquareBetween q x a := by
  obtain ⟨z, hz, hz'⟩ := AffineBetween.inner_pasch a.1 b.1 c.1 p.1 q.1 ha hb
  rcases hz with ⟨u, u0, u1, hu⟩
  obtain ⟨x,hx⟩ := square_combo_mem p b u0 u1
  refine ⟨x, ⟨u,u0,u1, ?_⟩, ?_⟩
  · exact hx
  · -- replace the common ambient point `z` in the second chord
    rw [hu] at hz'
    simpa [SquareBetween, hx] using hz'

lemma square_lower :
    ∃ a b c : OpenSquare, ¬ SquareBetween a b c ∧
      ¬ SquareBetween b c a ∧ ¬ SquareBetween c a b := by
  -- the standard affine-coordinate witness, scaled into the square
  let a : OpenSquare := ⟨((1/2:ℝ),0), by norm_num⟩
  let b : OpenSquare := ⟨((0:ℝ),1/2), by norm_num⟩
  let c : OpenSquare := ⟨((0:ℝ),0), by norm_num⟩
  refine ⟨a,b,c, ?_, ?_, ?_⟩
  all_goals
    intro h
    rcases h with ⟨u,u0,u1,hu⟩
    have h0 := congrArg Prod.fst hu
    have h1 := congrArg Prod.snd hu
    dsimp [a,b,c] at h0 h1
    (try norm_num at h0) <;> (try norm_num at h1) <;> linarith
end
end LeanEval.Geometry

end
-- END INLINED FILE: Mathlib/Support/parallel_postulate_independent_6d58d2ed72/SquareFailure.lean

-- BEGIN INLINED FILE: Mathlib/Support/parallel_postulate_independent_6d58d2ed72/KleinAnalytic.lean
section

namespace LeanEval.Geometry
noncomputable section
open scoped RealInnerProductSpace

/-- Points of the open Euclidean disk, in ambient real coordinate plane. -/
abbrev KleinDisk2 := GenericKleinDisk Plane2

/-- The residual quadratic form. -/
def KQ (x : KleinDisk2) : ℝ := 1 - inner ℝ x.1 x.1

def KS (x : KleinDisk2) : ℝ := Real.sqrt (KQ x)

/-- Cosh of the Klein distance. -/
def KM (x y : KleinDisk2) : ℝ := (1 - inner ℝ x.1 y.1) / (KS x * KS y)

/-- squared-sinh length used for congruence. -/
def KL (x y : KleinDisk2) : ℝ :=
  (1 - inner ℝ x.1 y.1) ^ 2 /
    ((1 - inner ℝ x.1 x.1) * (1 - inner ℝ y.1 y.1)) - 1

@[simp] lemma KL_is_GenericKleinLength (a b : KleinDisk2) : KL a b = GenericKleinLength a b := rfl

/-- Chord betweenness, in the orientation used in this file and `AffineBetween`. -/
def KBetween (a b c : KleinDisk2) : Prop :=
  AffineBetween (Plane2) a.1 b.1 c.1

@[simp] lemma KBetween_is_GenericKleinBetween (a b c : KleinDisk2) :
    KBetween a b c ↔ GenericKleinBetween a b c := Iff.rfl

lemma KQ_pos (x : KleinDisk2) : 0 < KQ x := by
  exact sub_pos.mpr x.2
lemma KS_pos (x : KleinDisk2) : 0 < KS x := by
  exact Real.sqrt_pos.2 (KQ_pos x)
lemma KS_sq (x : KleinDisk2) : KS x ^ 2 = KQ x := by
  exact Real.sq_sqrt (le_of_lt (KQ_pos x))

-- Cauchy gives the small but useful strict numerator inequality.
lemma inner_lt_one_disk (x y : KleinDisk2) : inner ℝ x.1 y.1 < 1 := by
  have xx0 : 0 ≤ ‖x.1‖ := norm_nonneg _
  have yy0 : 0 ≤ ‖y.1‖ := norm_nonneg _
  have xx2 : ‖x.1‖ ^ 2 = inner ℝ x.1 x.1 := by
    exact (real_inner_self_eq_norm_sq _).symm
  have yy2 : ‖y.1‖ ^ 2 = inner ℝ y.1 y.1 := by
    exact (real_inner_self_eq_norm_sq _).symm
  have xxlt : ‖x.1‖ < 1 := by nlinarith [x.2]
  have yylt : ‖y.1‖ < 1 := by nlinarith [y.2]
  have prodlt : ‖x.1‖ * ‖y.1‖ < 1 := by nlinarith
  have hca : inner ℝ x.1 y.1 ≤ ‖x.1‖ * ‖y.1‖ := real_inner_le_norm _ _
  linarith
lemma Knum_pos (x y : KleinDisk2) : 0 < 1 - inner ℝ x.1 y.1 :=
  sub_pos.mpr (inner_lt_one_disk x y)
lemma KM_pos (x y : KleinDisk2) : 0 < KM x y := by
  dsimp [KM]
  exact div_pos (Knum_pos x y) (mul_pos (KS_pos x) (KS_pos y))

lemma KL_eq_sq (x y : KleinDisk2) : KL x y = KM x y ^ 2 - 1 := by
  dsimp [KL, KM]
  have hx : KS x ^ 2 = 1 - inner ℝ x.1 x.1 := KS_sq x
  have hy : KS y ^ 2 = 1 - inner ℝ y.1 y.1 := KS_sq y
  rw [div_pow]
  rw [mul_pow]
  rw [hx, hy]
  unfold GenericKleinLength
  rfl


-- expansion after translating by the first point; it avoids any coordinate determinant.
lemma knum_sq_gap (x y : KleinDisk2) :
    (1 - inner ℝ x.1 y.1)^2 -
      ((1-inner ℝ x.1 x.1)*(1-inner ℝ y.1 y.1))
      = (inner ℝ x.1 (y.1 - x.1))^2 +
          (1-inner ℝ x.1 x.1) * inner ℝ (y.1 - x.1) (y.1 - x.1) := by
  -- bilinearity in the ambient real plane
  -- let the mixed product expand and finish with commutativity.
  simp only [inner_sub_right, inner_sub_left,
    real_inner_comm y.1 x.1] -- might leave terms
  ring

lemma KM_gt_one_of_ne (x y : KleinDisk2) (h : x ≠ y) : 1 < KM x y := by
  have hv : y.1 - x.1 ≠ 0 := by
    intro z
    have e : y.1 = x.1 := sub_eq_zero.mp z
    apply h
    exact Subtype.ext e.symm
  have vv : 0 < inner ℝ (y.1-x.1) (y.1-x.1) := by
    exact real_inner_self_pos.mpr hv
  have qx : 0 < 1 - inner ℝ x.1 x.1 := KQ_pos x
  have den : 0 < (1-inner ℝ x.1 x.1)*(1-inner ℝ y.1 y.1) :=
    mul_pos qx (KQ_pos y)
  have gap : 0 < (1 - inner ℝ x.1 y.1)^2 -
      ((1-inner ℝ x.1 x.1)*(1-inner ℝ y.1 y.1)) := by
    rw [knum_sq_gap x y]
    nlinarith [sq_nonneg (inner ℝ x.1 (y.1-x.1))]
  have hsx : 0 < KS x * KS y := mul_pos (KS_pos x) (KS_pos y)
  have den_s : (KS x * KS y)^2 =
      (1-inner ℝ x.1 x.1)*(1-inner ℝ y.1 y.1) := by
    rw [mul_pow, KS_sq x, KS_sq y]; rfl
  have Mform : KM x y = (1-inner ℝ x.1 y.1)/(KS x * KS y) := rfl
  have ms : 1 < (KM x y)^2 := by
    rw [Mform]
    -- field_simp by positivity
    rw [div_pow]
    rw [den_s]
    apply (lt_div_iff₀ den).2
    nlinarith
  have mp : 0 < KM x y := KM_pos x y
  nlinarith

lemma KM_one_iff (x y : KleinDisk2) : KM x y = 1 ↔ x = y := by
  constructor
  · intro h
    by_contra n
    have := KM_gt_one_of_ne x y n
    linarith
  · intro h; subst y
    dsimp [KM]
    have hq : 1 - inner ℝ x.1 x.1 = KQ x := rfl
    have hs : KS x ^ 2 = KQ x := KS_sq x
    rw [← pow_two]
    rw [hs]
    apply div_self
    linarith [KQ_pos x]

lemma KM_ge_one (x y : KleinDisk2) : 1 ≤ KM x y := by
  by_cases h : x = y
  · exact le_of_eq (KM_one_iff x y |>.2 h).symm
  · exact le_of_lt (KM_gt_one_of_ne x y h)

lemma KL_eq_imp_KM_eq {a b c d : KleinDisk2}
    (h : KL a b = KL c d) : KM a b = KM c d := by
  rw [KL_eq_sq, KL_eq_sq] at h
  have p := KM_pos a b
  have q := KM_pos c d
  nlinarith

-- basic Minkowski pairing rules for a point expressed on a chord.
-- Coefficients scale by `KS` rather than by raw affine parameters.
lemma KM_affine_right
    (a b c d : KleinDisk2) (k : ℝ)
    (hc : c.1 = a.1 + k • (b.1 - a.1)) :
    KM c d = (((1-k) * KS a / KS c) * KM a d +
                (k * KS b / KS c) * KM b d) := by
  have sa : 0 < KS a := KS_pos a
  have sb : 0 < KS b := KS_pos b
  have sc : 0 < KS c := KS_pos c
  have sd : 0 < KS d := KS_pos d
  -- bilinear numerator plus scalar identity `1 = (1-k)+k`.
  dsimp [KM]
  rw [hc]
  -- simplify inner with add/sub/smul
  simp only [inner_add_left, inner_smul_left, inner_sub_left]
  -- all pairings are real
  -- `simp` introduces conj on real as trivial
  simp only [conj_trivial]
  field_simp
  ring

-- the identical formula when `d=a`, and the normalization equation.
-- obtaining the latter by expanding `q c` also avoids Lorentz vectors.
lemma affine_coeff_norm
    (a b c : KleinDisk2) (k : ℝ)
    (hc : c.1 = a.1 + k • (b.1 - a.1)) :
    let α := (1-k) * KS a / KS c
    let β := k * KS b / KS c
    α^2 + β^2 + 2*α*β*KM a b = 1 := by
  dsimp
  have sa : 0 < KS a := KS_pos a
  have sb : 0 < KS b := KS_pos b
  have sc : 0 < KS c := KS_pos c
  have qab : (KS a)^2 = 1 - inner ℝ a.1 a.1 := KS_sq a
  have qbb : (KS b)^2 = 1 - inner ℝ b.1 b.1 := KS_sq b
  have qcc : (KS c)^2 = 1 - inner ℝ c.1 c.1 := KS_sq c
  dsimp [KM]
  rw [hc] at qcc
  simp only [inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, inner_sub_left, inner_sub_right,
    conj_trivial] at qcc
  -- this identity is pure polynomial after clearing positive square roots
  field_simp
  nlinarith [qab, qbb, qcc, real_inner_comm a.1 b.1]

-- endpoint parameter extant helper in EuclideanInner applies to `KBetween` directly.
lemma chord_coeffs
    (a b c : KleinDisk2) (hab : a ≠ b)
    (h : KBetween a b c) :
    ∃ k : ℝ, 1 ≤ k ∧ c.1 = a.1 + k • (b.1-a.1) := by
  have hne : a.1 ≠ b.1 := by
    intro e; exact hab (Subtype.ext e)
  exact AffineBetween.endpoint_parameter a.1 b.1 c.1 hne h

lemma KM_symm (x y : KleinDisk2) : KM x y = KM y x := by
  dsimp [KM]
  rw [real_inner_comm x.1 y.1, mul_comm]
lemma KL_of_KM_eq {x y z w : KleinDisk2} (h : KM x y = KM z w) : KL x y = KL z w := by
  rw [KL_eq_sq, KL_eq_sq, h]

lemma klein_five_segment
    (a b c d a' b' c' d' : KleinDisk2) (hab : a ≠ b)
    (hc : KBetween a b c) (hc' : KBetween a' b' c')
    (eab : KL a b = KL a' b')
    (ebc : KL b c = KL b' c')
    (ead : KL a d = KL a' d')
    (ebd : KL b d = KL b' d') : KL c d = KL c' d' := by
  -- all the hypotheses can now be read as equality of hyperbolic cosines.
  have tab : KM a b = KM a' b' := KL_eq_imp_KM_eq eab
  have ubc : KM b c = KM b' c' := KL_eq_imp_KM_eq ebc
  have vad : KM a d = KM a' d' := KL_eq_imp_KM_eq ead
  have wbd : KM b d = KM b' d' := KL_eq_imp_KM_eq ebd
  have hne' : a' ≠ b' := by
    intro h
    have one : KM a' b' = 1 := KM_one_iff _ _ |>.2 h
    have gt := KM_gt_one_of_ne a b hab
    nlinarith
  rcases chord_coeffs a b c hab hc with ⟨k,hk,hcval⟩
  rcases chord_coeffs a' b' c' hne' hc' with ⟨l,hl,hcval'⟩
  let A : ℝ := (1-k)*KS a / KS c
  let B : ℝ := k*KS b / KS c
  let A' : ℝ := (1-l)*KS a' / KS c'
  let B' : ℝ := l*KS b' / KS c'
  have Aneg : A ≤ 0 := by
    dsimp [A];
    have := KS_pos a; have := KS_pos c
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos_of_le hk) (le_of_lt ‹0 < KS a›)) (le_of_lt ‹0 < KS c›)
  have Aneg' : A' ≤ 0 := by
    dsimp [A'];
    have := KS_pos a'; have := KS_pos c'
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos_of_le hl) (le_of_lt ‹0 < KS a'›)) (le_of_lt ‹0 < KS c'›)
  have eqU : KM b c = A * KM b a + B := by
    have e := KM_affine_right a b c b k hcval
    have one : KM b b = 1 := KM_one_iff _ _ |>.2 rfl
    rw [one, mul_one] at e
    rw [KM_symm b c, KM_symm b a]
    simpa [A, B] using e
  have eqU' : KM b' c' = A' * KM b' a' + B' := by
    have e := KM_affine_right a' b' c' b' l hcval'
    have one : KM b' b' = 1 := KM_one_iff _ _ |>.2 rfl
    rw [one, mul_one] at e
    rw [KM_symm b' c', KM_symm b' a']
    simpa [A', B'] using e
  have nrm : A^2 + B^2 + 2*A*B*KM a b = 1 := by
    simpa [A, B] using affine_coeff_norm a b c k hcval
  have nrm' : A'^2 + B'^2 + 2*A'*B'*KM a' b' = 1 := by
    simpa [A', B'] using affine_coeff_norm a' b' c' l hcval'
  have t_gt : 1 < KM a b := KM_gt_one_of_ne _ _ hab
  have B_expr : B = KM b' c' - A * KM a b := by
    rw [KM_symm b a, tab] at eqU
    nlinarith
  have B_expr' : B' = KM b' c' - A' * KM a b := by
    rw [KM_symm b' a', ← tab] at eqU'
    nlinarith
  rw [B_expr] at nrm
  rw [B_expr'] at nrm'
  rw [← tab] at nrm'
  ring_nf at nrm nrm'
  have fac : (A^2 - A'^2) * (1 - (KM a b)^2) = 0 := by
    nlinarith [nrm, nrm']
  have fac_ne : 1 - (KM a b)^2 ≠ 0 := by
    nlinarith only [t_gt]
  have Asq : A^2 = A'^2 := by
    rcases mul_eq_zero.mp fac with h | h
    · exact sub_eq_zero.mp h
    · exact False.elim (fac_ne h)
  have Aeq : A = A' := by
    have hfac : (A - A') * (A + A') = 0 := by
      nlinarith only [Asq]
    rcases mul_eq_zero.mp hfac with h | h
    · exact sub_eq_zero.mp h
    · nlinarith only [h, Aneg, Aneg']
  have Beq : B = B' := by
    rw [B_expr, B_expr', Aeq]
  have target : KM c d = KM c' d' := by
    have e := KM_affine_right a b c d k hcval
    have e' := KM_affine_right a' b' c' d' l hcval'
    change KM c d = A * KM a d + B * KM b d at e
    change KM c' d' = A' * KM a' d' + B' * KM b' d' at e'
    rw [Aeq, Beq, vad, wbd] at e
    rw [e, e']
  exact KL_of_KM_eq target

lemma KM_bisect_eq
    (p q z : KleinDisk2) (h : KM p z = KM q z) :
    KS q * (1 - inner ℝ p.1 z.1) = KS p * (1 - inner ℝ q.1 z.1) := by
  dsimp [KM] at h
  have sp : 0 < KS p := KS_pos p
  have sq : 0 < KS q := KS_pos q
  have sz : 0 < KS z := KS_pos z
  field_simp at h
  nlinarith

/-- Normal of the hyperbolic perpendicular-bisector chord. -/
def Knormal (p q : KleinDisk2) : Plane2 :=
  KS q • p.1 - KS p • q.1

lemma Knormal_ne (p q : KleinDisk2) (h : p ≠ q) : Knormal p q ≠ (0 : Plane2) := by
  intro hz
  have eqs : KS q • p.1 = KS p • q.1 := sub_eq_zero.mp hz
  have sp : 0 < KS p := KS_pos p
  have sq : 0 < KS q := KS_pos q
  have pexpr : p.1 = (KS p / KS q) • q.1 := by
    -- divide the vector identity by `KS q`
    calc
      p.1 = ((1/KS q) * KS q) • p.1 := by rw [div_mul_cancel₀ (1:ℝ) (ne_of_gt sq)]; simp
      _ = (1/KS q) • (KS q • p.1) := by rw [smul_smul]
      _ = (1/KS q) • (KS p • q.1) := by rw [eqs]
      _ = (KS p / KS q) • q.1 := by rw [smul_smul]; ring_nf
  have pp : inner ℝ p.1 p.1 = (KS p / KS q)^2 * inner ℝ q.1 q.1 := by
    rw [pexpr]
    rw [inner_smul_left, inner_smul_right]
    simp only [conj_trivial]
    ring
  have sp2 : KS p ^ 2 = 1 - inner ℝ p.1 p.1 := KS_sq p
  have sq2 : KS q ^ 2 = 1 - inner ℝ q.1 q.1 := KS_sq q
  have eqsq : KS p ^ 2 = KS q ^ 2 := by
    -- substitute the inner product via `pexpr`, clear denominator, simplify.
    field_simp at pp
    -- pp : ... maybe `sq` factors
    nlinarith
  have ks_eq : KS p = KS q := by nlinarith
  have pq : p.1 = q.1 := by
    rw [ks_eq] at pexpr
    have : KS q / KS q = (1:ℝ) := div_self (ne_of_gt sq)
    simpa [this] using pexpr
  exact h (Subtype.ext pq)

lemma Kbisector_orth
    (p q a b : KleinDisk2)
    (ha : KM p a = KM q a)
    (hb : KM p b = KM q b) :
    inner ℝ (Knormal p q) (b.1 - a.1) = 0 := by
  have ea := KM_bisect_eq p q a ha
  have eb := KM_bisect_eq p q b hb
  dsimp [Knormal]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, conj_trivial]
  -- collect the two affine equations at `a` and `b`
  nlinarith

lemma klein_upper_dim
    (a b c p q : KleinDisk2) (hpq : p ≠ q)
    (ha : KL p a = KL q a)
    (hb : KL p b = KL q b)
    (hc : KL p c = KL q c) :
    KBetween a b c ∨ KBetween b c a ∨ KBetween c a b := by
  have ha' : KM p a = KM q a := KL_eq_imp_KM_eq ha
  have hb' : KM p b = KM q b := KL_eq_imp_KM_eq hb
  have hc' : KM p c = KM q c := KL_eq_imp_KM_eq hc
  by_cases hba : b = a
  · subst b
    left
    exact affineBetween_left _ _
  have horth1 : inner ℝ (Knormal p q) (b.1-a.1) = 0 :=
    Kbisector_orth p q a b ha' hb'
  have horth2 : inner ℝ (Knormal p q) (c.1-a.1) = 0 :=
    Kbisector_orth p q a c ha' hc'
  have nn : (Knormal p q) ≠ (0:Plane2) := Knormal_ne p q hpq
  have ba : (b.1-a.1) ≠ (0:Plane2) := sub_ne_zero.mpr (by
    intro e; exact hba (Subtype.ext e))
  obtain ⟨r, hr⟩ := plane2_kernel_multiple (Knormal p q)
    (b.1-a.1) (c.1-a.1) nn ba horth1 horth2
  exact affinely_collinear_of_multiple a.1 b.1 c.1 r hr

/-- The five-segment lemma stated with the generic names from `GenericKleinLengthBasic`.
This is often the convenient way to feed the analytic field into Tarski's
structure. -/
lemma GenericKleinLength.five_segment_plane
    (a b c d a' b' c' d' : GenericKleinDisk Plane2) (hab : a ≠ b)
    (hc : GenericKleinBetween a b c) (hc' : GenericKleinBetween a' b' c')
    (eab : GenericKleinLength a b = GenericKleinLength a' b')
    (ebc : GenericKleinLength b c = GenericKleinLength b' c')
    (ead : GenericKleinLength a d = GenericKleinLength a' d')
    (ebd : GenericKleinLength b d = GenericKleinLength b' d') :
    GenericKleinLength c d = GenericKleinLength c' d' := by
  exact klein_five_segment a b c d a' b' c' d'
    hab hc hc' eab ebc ead ebd

lemma GenericKleinLength.upper_dim_plane
    (a b c p q : GenericKleinDisk Plane2) (hpq : p ≠ q)
    (ha : GenericKleinLength p a = GenericKleinLength q a)
    (hb : GenericKleinLength p b = GenericKleinLength q b)
    (hc : GenericKleinLength p c = GenericKleinLength q c) :
    GenericKleinBetween a b c ∨ GenericKleinBetween b c a ∨ GenericKleinBetween c a b := by
  exact klein_upper_dim a b c p q hpq ha hb hc

end
end LeanEval.Geometry

end
-- END INLINED FILE: Mathlib/Support/parallel_postulate_independent_6d58d2ed72/KleinAnalytic.lean

-- BEGIN INLINED FILE: Mathlib/Support/parallel_postulate_independent_6d58d2ed72/KleinLengthPlane.lean
section
namespace LeanEval.Geometry
noncomputable section
open scoped RealInnerProductSpace Matrix
open Finset

/-- The first coordinate basis vector of `Plane2`, used only when the
initial ray is degenerate in Klein segment construction. -/
def planeFirst : Plane2 := WithLp.toLp 2 ![(1:ℝ),(0:ℝ)]
@[simp] lemma planeFirst_apply0 : planeFirst 0 = (1:ℝ) := by rfl
@[simp] lemma planeFirst_apply1 : planeFirst 1 = (0:ℝ) := by rfl
@[simp] lemma planeFirst_inner : inner ℝ planeFirst planeFirst = (1:ℝ) := by
  rw [PiLp.inner_apply]
  simp [planeFirst, Fin.sum_univ_two]

/-- A4 for the two-dimensional Hilbert Klein plane. -/
lemma planeKlein_segment (a b c d : GenericKleinDisk Plane2) :
  ∃ x : GenericKleinDisk Plane2, GenericKleinBetween a b x ∧ GenericKleinLength b x = GenericKleinLength c d :=
  klein_segment_construction planeFirst planeFirst_inner a b c d

end
end LeanEval.Geometry

end
-- END INLINED FILE: Mathlib/Support/parallel_postulate_independent_6d58d2ed72/KleinLengthPlane.lean

-- BEGIN INLINED FILE: Mathlib/Support/parallel_postulate_independent_6d58d2ed72/SquareContinuity.lean
section

namespace LeanEval.Geometry
noncomputable section
open Set

/-- An affine parameter on a nondegenerate real line is unique. -/
private lemma __SquareContinuity_square_param_unique
    {a z : ℝ × ℝ} (hne : z ≠ a) {u v : ℝ}
    (h : (1-u) • a + u • z = (1-v) • a + v • z) : u = v := by
  have hz : (u-v) • (z-a) = (0 : ℝ × ℝ) := by
    calc
      (u-v) • (z-a) =
          ((1-u) • a + u • z) - ((1-v) • a + v • z) := by module
      _ = 0 := by rw [h]; simp
  have hor := (smul_eq_zero.mp hz)
  cases hor with
  | inl hs => linarith
  | inr hza =>
    have : z = a := sub_eq_zero.mp hza
    exact (hne this).elim

/-- If the same non-initial point is reached with parameters `u` and `v`,
solving the latter equation writes its far endpoint on the former line. -/
private lemma __SquareContinuity_square_solve_param
    {a z y : ℝ × ℝ} {u v : ℝ} (hv : v ≠ 0)
    (h : (1-u) • a + u • z = (1-v) • a + v • y) :
    y = (1-u/v) • a + (u/v) • z := by
  have hz : v • (y-a) = u • (z-a) := by
    calc
      v • (y-a) = ((1-v) • a + v • y) - a := by module
      _ = ((1-u) • a + u • z) - a := by rw [← h]
      _ = u • (z-a) := by module
  calc
    y = a + (y-a) := by module
    _ = a + (1/v) • (v • (y-a)) := by
      have vv : (1/v) * v = (1:ℝ) := by field_simp
      rw [smul_smul, vv, one_smul]
    _ = a + (1/v) • (u • (z-a)) := by rw [hz]
    _ = (1-u/v) • a + (u/v) • z := by
      rw [smul_smul]
      have hu : (1/v) * u = u / v := by field_simp
      rw [hu]
      module

/-- Composition of affine parameters along the same first endpoint. -/
private lemma __SquareContinuity_square_param_comp
    {a z y x : ℝ × ℝ} {u v : ℝ}
    (hy : y = (1-v) • a + v • z)
    (hx : x = (1-u) • a + u • y) :
    x = (1-u*v) • a + (u*v) • z := by
  rw [hy] at hx
  calc
    x = (1-u) • a + u • ((1-v) • a + v • z) := hx
    _ = (1-u*v) • a + (u*v) • z := by module

/-- The only non-vacuous square cut. On the line `a--y₀`, members of `X`
carry parameters in `[0,1]` and those parameters are at most the parameter
of every point of `Y`. Their supremum lies in the same bounded chord. -/
lemma square_line_cut (X Y : Set OpenSquare) (a x₀ y₀ : OpenSquare)
    (hx₀ : x₀ ∈ X) (hy₀ : y₀ ∈ Y) (hne : x₀ ≠ a)
    (h : ∀ x ∈ X, ∀ y ∈ Y, SquareBetween a x y) :
    ∃ b : OpenSquare, ∀ x ∈ X, ∀ y ∈ Y, SquareBetween x b y := by
  -- A nonzero parameter of the fixed member `x₀` on the baseline `a--y₀`.
  rcases h x₀ hx₀ y₀ hy₀ with ⟨u₀, hu₀0, hu₀1, hx₀base⟩
  have hu₀ne : u₀ ≠ 0 := by
    intro hu
    have heqval : x₀.1 = a.1 := by
      simpa [hu] using hx₀base
    have heq : x₀ = a := Subtype.ext heqval
    exact hne heq
  have hu₀p : 0 < u₀ := lt_of_le_of_ne hu₀0 (Ne.symm hu₀ne)
  have hbase_ne : y₀.1 ≠ a.1 := by
    intro hya
    have : x₀.1 = a.1 := by
      rw [hya] at hx₀base
      -- both endpoints coincide
      simpa [sub_smul] using hx₀base
    exact hne (Subtype.ext this)
  -- Parameters realised by `X` on the chord with endpoints `a,y₀`.
  let U : Set ℝ := {u | ∃ x : OpenSquare, x ∈ X ∧
      0 ≤ u ∧ u ≤ 1 ∧ x.1 = (1-u) • a.1 + u • y₀.1}
  have hU_ne : U.Nonempty := by
    refine ⟨u₀, ?_⟩
    exact ⟨x₀, hx₀, hu₀0, hu₀1, hx₀base⟩
  have hU_bdd : BddAbove U := by
    refine ⟨1, ?_⟩
    intro v hv
    rcases hv with ⟨x, hx, hv0, hv1, he⟩
    exact hv1
  let s : ℝ := sSup U
  have hs1 : s ≤ 1 := by
    dsimp [s]
    refine csSup_le hU_ne ?_
    intro v hv
    rcases hv with ⟨x, hx, hv0, hv1, he⟩
    exact hv1
  have hs0 : 0 ≤ s := by
    dsimp [s]
    -- compare with the chosen nonempty parameter
    have hu_mem : u₀ ∈ U := ⟨x₀, hx₀, hu₀0, hu₀1, hx₀base⟩
    exact le_trans hu₀0 (le_csSup hU_bdd hu_mem)
  obtain ⟨b, hb⟩ := square_combo_mem a y₀ hs0 hs1
  refine ⟨b, ?_⟩
  intro x hx y hy
  -- Baseline parameter of `x`.
  rcases h x hx y₀ hy₀ with ⟨u, hu0, hu1, hxbase⟩
  have hu_mem : u ∈ U := ⟨x, hx, hu0, hu1, hxbase⟩
  have hu_s : u ≤ s := by
    exact le_csSup hU_bdd hu_mem
  -- Write any `y` on the same baseline, with parameter `w = u₀/v`.
  rcases h x₀ hx₀ y hy with ⟨v, hv0, hv1, hx₀y⟩
  have hv_ne : v ≠ 0 := by
    intro hv
    have : x₀.1 = a.1 := by simpa [hv] using hx₀y
    exact hne (Subtype.ext this)
  have hv_pos : 0 < v := lt_of_le_of_ne hv0 (Ne.symm hv_ne)
  let w : ℝ := u₀ / v
  have hw0 : 0 ≤ w := by
    dsimp [w]; positivity
  have hybase : y.1 = (1-w) • a.1 + w • y₀.1 := by
    dsimp [w]
    apply __SquareContinuity_square_solve_param hv_ne
    -- equations for the same point `x₀`
    rw [← hx₀base, ← hx₀y]
  -- Every member parameter of `X` is at most this `w`: use the
  -- actual between witness for that pair.
  have hU_le_w : ∀ q ∈ U, q ≤ w := by
    intro q hq
    rcases hq with ⟨z, hzX, hq0, hq1, hzbase⟩
    rcases h z hzX y hy with ⟨t, ht0, ht1, hzay⟩
    have hzcomp : z.1 = (1 - t*w) • a.1 + (t*w) • y₀.1 :=
      __SquareContinuity_square_param_comp hybase hzay
    have hpar : q = t*w := by
      apply __SquareContinuity_square_param_unique hbase_ne
      rw [← hzbase, ← hzcomp]
    -- `t ≤ 1` and `w ≥ 0`.
    rw [hpar]
    exact mul_le_of_le_one_left hw0 ht1
  have hs_w : s ≤ w := by
    dsimp [s]
    exact csSup_le hU_ne hU_le_w
  -- Interpolate in the parameters `u ≤ s ≤ w`.
  by_cases heq : u = w
  · have hus : s = u := le_antisymm (by simpa [heq] using hs_w) hu_s
    -- In this degenerate endpoint case all ambient points coincide.
    refine ⟨0, by positivity, by norm_num, ?_⟩
    -- `SquareBetween x b y` asks that `b` is the affine point with
    -- coefficient zero on the endpoints, i.e. simply `x`.
    -- `1-0=1`.
    -- Show their underlying ambient coordinates agree.
    change b.1 = (1 - (0:ℝ)) • x.1 + (0:ℝ) • y.1
    -- both are the same baseline coordinate
    have hb' : b.1 = (1-s) • a.1 + s • y₀.1 := hb
    calc
      b.1 = (1-s) • a.1 + s • y₀.1 := hb'
      _ = (1-u) • a.1 + u • y₀.1 := by rw [hus]
      _ = x.1 := by symm; exact hxbase
      _ = (1 - (0:ℝ)) • x.1 + (0:ℝ) • y.1 := by simp
  · have huw_pos : 0 < w - u := sub_pos.mpr (lt_of_le_of_ne
        (hU_le_w u hu_mem) heq)
    let k : ℝ := (s-u) / (w-u)
    have hk0 : 0 ≤ k := by
      dsimp [k]
      exact div_nonneg (sub_nonneg.mpr hu_s) (le_of_lt huw_pos)
    have hk1 : k ≤ 1 := by
      dsimp [k]
      exact (div_le_one huw_pos).2 (sub_le_sub_right hs_w u)
    refine ⟨k, hk0, hk1, ?_⟩
    -- Substituting the three coordinates leaves a scalar identity
    -- `s = (1-k)*u + k*w`.
    have hcoeff : (1-k)*u + k*w = s := by
      dsimp [k]
      have hden : w-u ≠ 0 := ne_of_gt huw_pos
      field_simp
      ring
    -- homogeneous affine arithmetic on the common basis `(a,y₀)`
    calc
      b.1 = (1-s) • a.1 + s • y₀.1 := hb
      _ = (1-((1-k)*u + k*w)) • a.1 + ((1-k)*u + k*w) • y₀.1 := by rw [hcoeff]
      _ = (1-k) • ((1-u) • a.1 + u • y₀.1) +
            k • ((1-w) • a.1 + w • y₀.1) := by module
      _ = (1-k) • x.1 + k • y.1 := by rw [hxbase, hybase]

/-- A11 (second-order cut continuity) for the convex open square with chord
betweenness. No congruence has entered: this is entirely the one-dimensional
cut argument on a fixed chord. -/
lemma square_continuity :
    ∀ X Y : Set OpenSquare,
      (∃ a, ∀ x ∈ X, ∀ y ∈ Y, SquareBetween a x y) →
      (∃ b, ∀ x ∈ X, ∀ y ∈ Y, SquareBetween x b y) := by
  intro X Y H
  by_cases xe : X.Nonempty
  · obtain ⟨x,hx⟩ := xe
    by_cases ye : Y.Nonempty
    · obtain ⟨y,hy⟩ := ye
      obtain ⟨a,ha⟩ := H
      by_cases hn : ∃ z ∈ X, z ≠ a
      · obtain ⟨z,hz,hza⟩ := hn
        exact square_line_cut X Y a z y hz hy hza ha
      · have allx : ∀ z ∈ X, z = a := by
          intro z hz
          by_contra hza
          exact hn ⟨z,hz,hza⟩
        refine ⟨a, ?_⟩
        intro z hz w hw
        rw [allx z hz]
        exact squareBetween_left _ _
    · refine ⟨x, ?_⟩
      intro z hz w hw
      exact (ye ⟨w,hw⟩).elim
  · -- any point, say the centre of the square, works when `X` is empty
    let o : OpenSquare := ⟨(0,0), by norm_num⟩
    refine ⟨o, ?_⟩
    intro x hx y hy
    exact (xe ⟨x,hx⟩).elim
end
end LeanEval.Geometry

end
-- END INLINED FILE: Mathlib/Support/parallel_postulate_independent_6d58d2ed72/SquareContinuity.lean

-- BEGIN INLINED FILE: Mathlib/Support/parallel_postulate_independent_6d58d2ed72/DiskBetween.lean
section

namespace LeanEval.Geometry
noncomputable section
open scoped RealInnerProductSpace BigOperators
open Set

/-- The open Klein (unit) disk.  We use the coordinate Hilbert plane
`Plane2 = EuclideanSpace ℝ (Fin 2)` rather than the max-norm product; unlike
`ℝ × ℝ` in core this carrier has its standard inner product. -/
def KleinDisk := {v : Plane2 // inner ℝ v v < 1}

/-- Chord betweenness on the Klein disk is just affine betweenness of its
underlying vectors.  Congruence is a separate, hyperbolic piece of the model. -/
def DiskBetween (a b c : KleinDisk) : Prop :=
  AffineBetween Plane2 a.1 b.1 c.1

lemma diskBetween_left (a c : KleinDisk) : DiskBetween a a c := by
  exact affineBetween_left _ _
lemma diskBetween_right (a c : KleinDisk) : DiskBetween a c c := by
  exact affineBetween_right _ _

@[simp] lemma DiskBetween.swap (a b c : KleinDisk) :
    DiskBetween a b c ↔ DiskBetween c b a := by
  exact AffineBetween.swap _ _ _

/-- Convex combinations of two points of the open Hilbert ball stay in that
ball.  We keep the witness equation explicit, so the elementary affine cut
argument for continuity works literally as for any bounded convex chart. -/
lemma disk_combo_mem (p q : KleinDisk) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ∃ z : KleinDisk, z.1 = (1-u) • p.1 + u • q.1 := by
  let z : Plane2 := (1-u) • p.1 + u • q.1
  have hp2 : ‖(p.1 : Plane2)‖ ^ 2 < 1 := by
    simpa [real_inner_self_eq_norm_sq] using p.2
  have hq2 : ‖(q.1 : Plane2)‖ ^ 2 < 1 := by
    simpa [real_inner_self_eq_norm_sq] using q.2
  have hp : ‖(p.1 : Plane2)‖ < 1 := by
    nlinarith [norm_nonneg (p.1 : Plane2)]
  have hq : ‖(q.1 : Plane2)‖ < 1 := by
    nlinarith [norm_nonneg (q.1 : Plane2)]
  have havg : (1-u) * ‖(p.1 : Plane2)‖ + u * ‖(q.1 : Plane2)‖ < 1 := by
    by_cases h0 : u = 0
    · simp [h0, hp]
    by_cases h1 : u = 1
    · simp [h1, hq]
    have hup : 0 < u := lt_of_le_of_ne hu0 (Ne.symm h0)
    have hcp : 0 < 1-u := sub_pos.mpr (lt_of_le_of_ne hu1 h1)
    nlinarith [mul_lt_mul_of_pos_left hp hcp,
      mul_lt_mul_of_pos_left hq hup]
  have hzl : ‖z‖ ≤ (1-u) * ‖(p.1 : Plane2)‖ + u * ‖(q.1 : Plane2)‖ := by
    dsimp [z]
    calc
      ‖(1-u) • p.1 + u • q.1‖ ≤ ‖(1-u) • p.1‖ + ‖u • q.1‖ := norm_add_le _ _
      _ = (1-u) * ‖(p.1 : Plane2)‖ + u * ‖(q.1 : Plane2)‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        rw [abs_of_nonneg hu0, abs_of_nonneg (sub_nonneg.mpr hu1)]
  have hzn : ‖z‖ < 1 := lt_of_le_of_lt hzl havg
  have hzinner : inner ℝ z z < 1 := by
    rw [real_inner_self_eq_norm_sq]
    nlinarith [norm_nonneg z]
  exact ⟨⟨z, hzinner⟩, rfl⟩

/-- Betweenness identity on chords (Tarski A6). -/
lemma DiskBetween.id_ax (a b : KleinDisk) (h : DiskBetween a b a) : a = b := by
  apply Subtype.ext
  exact AffineBetween.id_ax a.1 b.1 h

/-- Inner Pasch is affine.  Its witness is a convex combination of two
already interior endpoints, hence belongs to the disk. -/
lemma DiskBetween.inner_pasch
    (a b c p q : KleinDisk)
    (hp : DiskBetween a p c) (hq : DiskBetween b q c) :
    ∃ x : KleinDisk, DiskBetween p x b ∧ DiskBetween q x a := by
  obtain ⟨x, hpx, hqx⟩ := AffineBetween.inner_pasch
    (V:=Plane2) a.1 b.1 c.1 p.1 q.1 hp hq
  rcases hpx with ⟨u, hu0, hu1, hx⟩
  -- interiority of the first affine expression (`p` -- `b`)
  obtain ⟨x', hxmem⟩ := disk_combo_mem p b u hu0 hu1
  have hxx : (x' : KleinDisk).1 = x := by simpa [hx] using hxmem
  refine ⟨x', ?_, ?_⟩
  · change AffineBetween Plane2 p.1 x'.1 b.1
    exact ⟨u, hu0, hu1, by simpa only [hxx] using hx⟩
  · change AffineBetween Plane2 q.1 x'.1 a.1
    -- cast the already found Pasch witness back into the subtype
    simpa only [hxx] using hqx

/-- Three small, pairwise non-collinear points fit in the open disk. -/
lemma disk_lower :
    ∃ a b c : KleinDisk,
      ¬ DiskBetween a b c ∧ ¬ DiskBetween b c a ∧
        ¬ DiskBetween c a b := by
  -- axis vectors of norm `1/2`, and the origin
  let A : Plane2 := EuclideanSpace.single (𝕜:=ℝ) (0 : Fin 2) (1/2 : ℝ)
  let B : Plane2 := EuclideanSpace.single (𝕜:=ℝ) (1 : Fin 2) (1/2 : ℝ)
  let Z : Plane2 := 0
  have hA : inner ℝ A A < 1 := by
    -- coordinates make the little radius immediate
    dsimp [A]
    rw [PiLp.inner_apply]
    simp [Fin.sum_univ_two]
    norm_num
  have hB : inner ℝ B B < 1 := by
    dsimp [B]
    rw [PiLp.inner_apply]
    simp [Fin.sum_univ_two]
    norm_num
  have hZ : inner ℝ Z Z < 1 := by simp [Z]
  let a : KleinDisk := ⟨A, hA⟩
  let b : KleinDisk := ⟨B, hB⟩
  let z : KleinDisk := ⟨Z, hZ⟩
  refine ⟨a, b, z, ?_, ?_, ?_⟩
  all_goals
    intro h
    rcases h with ⟨u, hu, hu', he⟩
    have h0 := congrArg (fun v : Plane2 => v 0) he
    have h1 := congrArg (fun v : Plane2 => v 1) he
    dsimp [a, b, z, A, B, Z] at h0 h1
    simp at h0 h1
  · linarith

-- The elementary cut lemmas below are written for the Hilbert disk but only
-- use affine combinations and `disk_combo_mem`.  In particular no topology
-- of the boundary is used: A11 is a one-dimensional real supremum.

private lemma __DiskBetween_disk_param_unique {a z : Plane2} (hne : z ≠ a) {u v : ℝ}
    (h : (1-u) • a + u • z = (1-v) • a + v • z) : u = v := by
  have hz : (u-v) • (z-a) = (0 : Plane2) := by
    calc
      (u-v) • (z-a) =
          ((1-u) • a + u • z) - ((1-v) • a + v • z) := by module
      _ = 0 := by rw [h]; simp
  have hor := smul_eq_zero.mp hz
  cases hor with
  | inl hs => linarith
  | inr hza =>
    have : z = a := sub_eq_zero.mp hza
    exact (hne this).elim

private lemma __DiskBetween_disk_solve_param {a z y : Plane2} {u v : ℝ}
    (hv : v ≠ 0)
    (h : (1-u) • a + u • z = (1-v) • a + v • y) :
    y = (1-u/v) • a + (u/v) • z := by
  have hz : v • (y-a) = u • (z-a) := by
    calc
      v • (y-a) = ((1-v) • a + v • y) - a := by module
      _ = ((1-u) • a + u • z) - a := by rw [← h]
      _ = u • (z-a) := by module
  calc
    y = a + (y-a) := by module
    _ = a + (1/v) • (v • (y-a)) := by
      have vv : (1/v) * v = (1:ℝ) := by field_simp
      rw [smul_smul, vv, one_smul]
    _ = a + (1/v) • (u • (z-a)) := by rw [hz]
    _ = (1-u/v) • a + (u/v) • z := by
      rw [smul_smul]
      have hu : (1/v) * u = u / v := by field_simp
      rw [hu]
      module

private lemma __DiskBetween_disk_param_comp {a z y x : Plane2} {u v : ℝ}
    (hy : y = (1-v) • a + v • z)
    (hx : x = (1-u) • a + u • y) :
    x = (1-u*v) • a + (u*v) • z := by
  rw [hy] at hx
  calc
    x = (1-u) • a + u • ((1-v) • a + v • z) := hx
    _ = (1-u*v) • a + (u*v) • z := by module

lemma disk_line_cut (X Y : Set KleinDisk) (a x₀ y₀ : KleinDisk)
    (hx₀ : x₀ ∈ X) (hy₀ : y₀ ∈ Y) (hne : x₀ ≠ a)
    (h : ∀ x ∈ X, ∀ y ∈ Y, DiskBetween a x y) :
    ∃ b : KleinDisk, ∀ x ∈ X, ∀ y ∈ Y, DiskBetween x b y := by
  rcases h x₀ hx₀ y₀ hy₀ with ⟨u₀, hu₀0, hu₀1, hx₀base⟩
  have hu₀ne : u₀ ≠ 0 := by
    intro hu
    have heqval : x₀.1 = a.1 := by simpa [hu] using hx₀base
    have heq : x₀ = a := Subtype.ext heqval
    exact hne heq
  have hu₀p : 0 < u₀ := lt_of_le_of_ne hu₀0 (Ne.symm hu₀ne)
  have hbase_ne : y₀.1 ≠ a.1 := by
    intro hya
    have : x₀.1 = a.1 := by
      rw [hya] at hx₀base
      simpa [sub_smul] using hx₀base
    exact hne (Subtype.ext this)
  let U : Set ℝ := {u | ∃ x : KleinDisk, x ∈ X ∧
      0 ≤ u ∧ u ≤ 1 ∧ x.1 = (1-u) • a.1 + u • y₀.1}
  have hU_ne : U.Nonempty := by
    refine ⟨u₀, ?_⟩
    exact ⟨x₀, hx₀, hu₀0, hu₀1, hx₀base⟩
  have hU_bdd : BddAbove U := by
    refine ⟨1, ?_⟩
    intro v hv
    rcases hv with ⟨x, hx, hv0, hv1, he⟩
    exact hv1
  let s : ℝ := sSup U
  have hs1 : s ≤ 1 := by
    dsimp [s]
    refine csSup_le hU_ne ?_
    intro v hv
    rcases hv with ⟨x, hx, hv0, hv1, he⟩
    exact hv1
  have hs0 : 0 ≤ s := by
    dsimp [s]
    have hu_mem : u₀ ∈ U := ⟨x₀, hx₀, hu₀0, hu₀1, hx₀base⟩
    exact le_trans hu₀0 (le_csSup hU_bdd hu_mem)
  obtain ⟨b, hb⟩ := disk_combo_mem a y₀ s hs0 hs1
  refine ⟨b, ?_⟩
  intro x hx y hy
  rcases h x hx y₀ hy₀ with ⟨u, hu0, hu1, hxbase⟩
  have hu_mem : u ∈ U := ⟨x, hx, hu0, hu1, hxbase⟩
  have hu_s : u ≤ s := le_csSup hU_bdd hu_mem
  rcases h x₀ hx₀ y hy with ⟨v, hv0, hv1, hx₀y⟩
  have hv_ne : v ≠ 0 := by
    intro hv
    have : x₀.1 = a.1 := by simpa [hv] using hx₀y
    exact hne (Subtype.ext this)
  have hv_pos : 0 < v := lt_of_le_of_ne hv0 (Ne.symm hv_ne)
  let w : ℝ := u₀ / v
  have hw0 : 0 ≤ w := by
    dsimp [w]
    positivity
  have hybase : y.1 = (1-w) • a.1 + w • y₀.1 := by
    dsimp [w]
    apply __DiskBetween_disk_solve_param hv_ne
    rw [← hx₀base, ← hx₀y]
  have hU_le_w : ∀ q ∈ U, q ≤ w := by
    intro q hq
    rcases hq with ⟨z, hzX, hq0, hq1, hzbase⟩
    rcases h z hzX y hy with ⟨t, ht0, ht1, hzay⟩
    have hzcomp : z.1 = (1 - t*w) • a.1 + (t*w) • y₀.1 :=
      __DiskBetween_disk_param_comp hybase hzay
    have hpar : q = t*w := by
      apply __DiskBetween_disk_param_unique hbase_ne
      rw [← hzbase, ← hzcomp]
    rw [hpar]
    exact mul_le_of_le_one_left hw0 ht1
  have hs_w : s ≤ w := by
    dsimp [s]
    exact csSup_le hU_ne hU_le_w
  by_cases heq : u = w
  · have hus : s = u := le_antisymm (by simpa [heq] using hs_w) hu_s
    refine ⟨0, by positivity, by norm_num, ?_⟩
    change b.1 = (1 - (0:ℝ)) • x.1 + (0:ℝ) • y.1
    have hb' : b.1 = (1-s) • a.1 + s • y₀.1 := hb
    calc
      b.1 = (1-s) • a.1 + s • y₀.1 := hb'
      _ = (1-u) • a.1 + u • y₀.1 := by rw [hus]
      _ = x.1 := by symm; exact hxbase
      _ = (1 - (0:ℝ)) • x.1 + (0:ℝ) • y.1 := by simp
  · have huw_pos : 0 < w-u := sub_pos.mpr (lt_of_le_of_ne
        (hU_le_w u hu_mem) heq)
    let k : ℝ := (s-u) / (w-u)
    have hk0 : 0 ≤ k := by
      dsimp [k]
      exact div_nonneg (sub_nonneg.mpr hu_s) (le_of_lt huw_pos)
    have hk1 : k ≤ 1 := by
      dsimp [k]
      exact (div_le_one huw_pos).2 (sub_le_sub_right hs_w u)
    refine ⟨k, hk0, hk1, ?_⟩
    have hcoeff : (1-k)*u + k*w = s := by
      dsimp [k]
      have hden : w-u ≠ 0 := ne_of_gt huw_pos
      field_simp
      ring
    calc
      b.1 = (1-s) • a.1 + s • y₀.1 := hb
      _ = (1-((1-k)*u + k*w)) • a.1 + ((1-k)*u + k*w) • y₀.1 := by rw [hcoeff]
      _ = (1-k) • ((1-u) • a.1 + u • y₀.1) +
            k • ((1-w) • a.1 + w • y₀.1) := by module
      _ = (1-k) • x.1 + k • y.1 := by rw [hxbase, hybase]

/-- Second-order continuity (A11) for chord betweenness in the disk. -/
lemma disk_continuity :
    ∀ X Y : Set KleinDisk,
      (∃ a, ∀ x ∈ X, ∀ y ∈ Y, DiskBetween a x y) →
      (∃ b, ∀ x ∈ X, ∀ y ∈ Y, DiskBetween x b y) := by
  intro X Y H
  by_cases xe : X.Nonempty
  · obtain ⟨x,hx⟩ := xe
    by_cases ye : Y.Nonempty
    · obtain ⟨y,hy⟩ := ye
      obtain ⟨a,ha⟩ := H
      by_cases hn : ∃ z ∈ X, z ≠ a
      · obtain ⟨z,hz,hza⟩ := hn
        exact disk_line_cut X Y a z y hz hy hza ha
      · have allx : ∀ z ∈ X, z = a := by
          intro z hz
          by_contra hza
          exact hn ⟨z,hz,hza⟩
        refine ⟨a, ?_⟩
        intro z hz w hw
        rw [allx z hz]
        exact diskBetween_left _ _
    · refine ⟨x, ?_⟩
      intro z hz w hw
      exact (ye ⟨w,hw⟩).elim
  · let o : KleinDisk := ⟨0, by simp⟩
    refine ⟨o, ?_⟩
    intro x hx y hy
    exact (xe ⟨x,hx⟩).elim

/-- No affine chord geometry on the open unit disk satisfies Tarski's
parallel axiom A10.  Explicit rational witnesses keep the obstruction clear:
the necessary extensions along the side rays leave the ball before their
height can reach the chosen transversal `T`. -/
private def __DiskBetween_diskVec (x y : ℝ) : Plane2 :=
  x • EuclideanSpace.single (𝕜:=ℝ) (0 : Fin 2) 1 +
    y • EuclideanSpace.single (𝕜:=ℝ) (1 : Fin 2) 1
@[simp] private lemma __DiskBetween_diskVec_zero (x y : ℝ) : __DiskBetween_diskVec x y 0 = x := by
  simp [__DiskBetween_diskVec]
@[simp] private lemma __DiskBetween_diskVec_one (x y : ℝ) : __DiskBetween_diskVec x y 1 = y := by
  simp [__DiskBetween_diskVec]
@[simp] private lemma __DiskBetween_diskVec_inner (x y : ℝ) :
    inner ℝ (__DiskBetween_diskVec x y) (__DiskBetween_diskVec x y) = x*x + y*y := by
  rw [PiLp.inner_apply]
  simp [__DiskBetween_diskVec, Fin.sum_univ_two]
  ring

set_option maxHeartbeats 2000000 in
lemma disk_not_parallel :
  ¬ (∀ a b c d t : KleinDisk,
    DiskBetween a d t → DiskBetween b d c → a ≠ d →
    ∃ x y : KleinDisk, DiskBetween a b x ∧
      DiskBetween a c y ∧ DiskBetween x t y) := by
  let A : KleinDisk := ⟨__DiskBetween_diskVec 0 0, by rw [__DiskBetween_diskVec_inner]; norm_num⟩
  let B : KleinDisk := ⟨__DiskBetween_diskVec (-(7/10:ℝ)) (1/2:ℝ), by
      rw [__DiskBetween_diskVec_inner]; norm_num⟩
  let C : KleinDisk := ⟨__DiskBetween_diskVec (7/10:ℝ) (1/2:ℝ), by
      rw [__DiskBetween_diskVec_inner]; norm_num⟩
  let D : KleinDisk := ⟨__DiskBetween_diskVec 0 (1/2:ℝ), by
      rw [__DiskBetween_diskVec_inner]; norm_num⟩
  let T : KleinDisk := ⟨__DiskBetween_diskVec 0 (9/10:ℝ), by
      rw [__DiskBetween_diskVec_inner]; norm_num⟩
  intro H
  have Hadt : DiskBetween A D T := by
    refine ⟨5/9, by norm_num, by norm_num, ?_⟩
    apply plane2_ext
    · norm_num [A, D, T, __DiskBetween_diskVec]
    · norm_num [A, D, T, __DiskBetween_diskVec] <;> ring
  have Hbdc : DiskBetween B D C := by
    refine ⟨1/2, by norm_num, by norm_num, ?_⟩
    apply plane2_ext
    · norm_num [B,C,D,__DiskBetween_diskVec] <;> ring
    · norm_num [B,C,D,__DiskBetween_diskVec] <;> ring
  have Had : A ≠ D := by
    intro e
    have q := congrArg (fun z : KleinDisk => (z.1 : Plane2) 1) e
    norm_num [A,D,__DiskBetween_diskVec] at q
  obtain ⟨x,y,hx,hy,hxy⟩ := H A B C D T Hadt Hbdc Had
  rcases hx with ⟨u,u0,u1,hx⟩
  rcases hy with ⟨w,w0,w1,hy⟩
  rcases hxy with ⟨v,v0,v1,hv⟩
  have hx0 := congrArg (fun z : Plane2 => z 0) hx
  have hx1 := congrArg (fun z : Plane2 => z 1) hx
  have hy0 := congrArg (fun z : Plane2 => z 0) hy
  have hy1 := congrArg (fun z : Plane2 => z 1) hy
  have ht1 := congrArg (fun z : Plane2 => z 1) hv
  simp [A,B,__DiskBetween_diskVec] at hx0 hx1
  simp [A,C,__DiskBetween_diskVec] at hy0 hy1
  simp [T,__DiskBetween_diskVec] at ht1
  have xball : x.1 0 * x.1 0 + x.1 1 * x.1 1 < (1:ℝ) := by
    simpa only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, starRingEnd_apply, star_trivial] using x.2
  have yball : y.1 0 * y.1 0 + y.1 1 * y.1 1 < (1:ℝ) := by
    simpa only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, starRingEnd_apply, star_trivial] using y.2
  have up : 0 < u := by
    by_contra n
    have h : u = 0 := le_antisymm (le_of_not_gt n) u0
    rw [h] at hx1
    norm_num at hx1
  have wp : 0 < w := by
    by_contra n
    have h : w = 0 := le_antisymm (le_of_not_gt n) w0
    rw [h] at hy1
    norm_num at hy1
  have idu : u^2 * (x.1 0*x.1 0 + x.1 1*x.1 1) = (74/100:ℝ) := by
    calc
      u^2 * (x.1 0*x.1 0 + x.1 1*x.1 1) =
          (u*x.1 0)^2 + (u*x.1 1)^2 := by ring
      _ = (-(7/10:ℝ))^2 + (1/2:ℝ)^2 := by rw [← hx0, ← hx1]; norm_num
      _ = (74/100:ℝ) := by norm_num
  have idw : w^2 * (y.1 0*y.1 0 + y.1 1*y.1 1) = (74/100:ℝ) := by
    calc
      w^2 * (y.1 0*y.1 0 + y.1 1*y.1 1) =
          (w*y.1 0)^2 + (w*y.1 1)^2 := by ring
      _ = (7/10:ℝ)^2 + (1/2:ℝ)^2 := by rw [← hy0, ← hy1]; norm_num
      _ = (74/100:ℝ) := by norm_num
  have ub2 : (74/100:ℝ) < u^2 := by
    nlinarith [mul_pos (sq_pos_of_pos up) (sub_pos.mpr xball)]
  have wb2 : (74/100:ℝ) < w^2 := by
    nlinarith [mul_pos (sq_pos_of_pos wp) (sub_pos.mpr yball)]
  have ub : (5/6:ℝ) < u := by nlinarith
  have wb : (5/6:ℝ) < w := by nlinarith
  have xpos : 0 < x.1 1 := by nlinarith
  have ypos : 0 < y.1 1 := by nlinarith
  have xl : x.1 1 < (3/5:ℝ) := by
    by_contra n
    have ge : (3/5:ℝ) ≤ x.1 1 := le_of_not_gt n
    nlinarith [mul_pos (by linarith : 0 < u-5/6) xpos]
  have yl : y.1 1 < (3/5:ℝ) := by
    by_contra n
    have ge : (3/5:ℝ) ≤ y.1 1 := le_of_not_gt n
    nlinarith [mul_pos (by linarith : 0 < w-5/6) ypos]
  have comb : (1-v)*x.1 1 + v*y.1 1 < (3/5:ℝ) := by
    by_cases z : v = 0
    · simpa [z] using xl
    by_cases o : v = 1
    · simpa [o] using yl
    have vp : 0 < v := lt_of_le_of_ne v0 (Ne.symm z)
    have op : 0 < 1-v := sub_pos.mpr (lt_of_le_of_ne v1 o)
    have h1 := mul_lt_mul_of_pos_left xl op
    have h2 := mul_lt_mul_of_pos_left yl vp
    linarith
  linarith

end
end LeanEval.Geometry

end
-- END INLINED FILE: Mathlib/Support/parallel_postulate_independent_6d58d2ed72/DiskBetween.lean


-- BEGIN INLINED MAIN PRELUDE

open LeanEval.Geometry
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
open scoped RealInnerProductSpace
namespace LeanEval.Geometry
noncomputable section
/-- The single non-vacuous cut case. On the line `a--y₀`, write
`x=a+u(y₀-a)`; the parameters of the members of `X` are bounded by every
parameter from `Y`. The desired `b` is at their real supremum. Isolating
this case avoids losing the endpoint and empty-set cases of A11. -/
lemma plane2_line_cut (X Y : Set Plane2) (a x₀ y₀ : Plane2)
    (hx₀ : x₀ ∈ X) (hy₀ : y₀ ∈ Y) (hne : x₀ ≠ a)
    (h : ∀ x ∈ X, ∀ y ∈ Y, AffineBetween Plane2 a x y) :
    ∃ b, ∀ x ∈ X, ∀ y ∈ Y, AffineBetween Plane2 x b y := by
  classical
  -- direction vector along the chosen endpoint of Y
  let v : Plane2 := y₀ - a
  have hyne : y₀ ≠ a := by
    intro hya
    have hxbetween : AffineBetween Plane2 a x₀ a := by
      simpa [hya] using h x₀ hx₀ y₀ hy₀
    have hax : a = x₀ := AffineBetween.id_ax a x₀ hxbetween
    exact hne hax.symm
  have hv : v ≠ 0 := by
    dsimp [v]
    exact sub_ne_zero.mpr hyne
  -- convenient affine expression based at the first endpoint.
  have normParam (z c : Plane2)
      (hz : AffineBetween Plane2 a z c) :
      ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ z = a + u • (c-a) := by
    rcases hz with ⟨u,hu0,hu1,hu⟩
    refine ⟨u,hu0,hu1,?_⟩
    rw [hu]
    module
  obtain ⟨t, ht0, ht1, hxt⟩ := normParam x₀ y₀ (h x₀ hx₀ y₀ hy₀)
  have hxt' : x₀ = a + t • v := by
    simpa [v] using hxt
  have htpos : 0 < t := by
    have htne : t ≠ 0 := by
      intro ht
      have : x₀ = a := by simpa [ht] using hxt'
      exact hne this
    exact lt_of_le_of_ne ht0 (Ne.symm htne)
  -- cut set of all parameters occupied by X on this line.
  let S : Set ℝ := {u | ∃ x ∈ X, 0 ≤ u ∧ u ≤ 1 ∧ x = a + u • v}
  have tmem : t ∈ S := by
    refine ⟨x₀,hx₀,ht0,ht1,hxt'⟩
  have Sne : S.Nonempty := ⟨t,tmem⟩
  have Sbound : BddAbove S := by
    refine ⟨1, ?_⟩
    intro z hz
    rcases hz with ⟨x,hx,h0,h1,hxv⟩
    exact h1
  let s : ℝ := sSup S
  have us_le_s {u : ℝ} (hu : u ∈ S) : u ≤ s := by
    dsimp [s]
    exact le_csSup Sbound hu
  have hparams : ∀ x ∈ X, ∃ u : ℝ,
      0 ≤ u ∧ u ≤ 1 ∧ x = a + u • v ∧ u ∈ S := by
    intro x hx
    obtain ⟨u,hu0,hu1,hux⟩ := normParam x y₀ (h x hx y₀ hy₀)
    have hux' : x = a + u • v := by simpa [v] using hux
    refine ⟨u,hu0,hu1,hux',?_⟩
    exact ⟨x,hx,hu0,hu1,hux'⟩
  refine ⟨a + s • v, ?_⟩
  intro x hx y hy
  obtain ⟨u,hu0,hu1,hxu,huS⟩ := hparams x hx
  have ule : u ≤ s := us_le_s huS
  -- parameter for Y via positivity of t
  obtain ⟨r,hr0,hr1,hxary⟩ := normParam x₀ y (h x₀ hx₀ y hy)
  have hrpos : 0 < r := by
    by_contra hr
    have hreq : r = 0 := le_antisymm (not_lt.mp hr) hr0
    have heq : x₀ = a := by simpa [hreq] using hxary
    exact hne heq
  -- solve y as a+(t/r) v from the equation for x₀
  let w : ℝ := t / r
  have hw0 : 0 ≤ w := by
    dsimp [w]
    positivity
  have hyw : y = a + w • v := by
    -- cancel scalar r using its inverse
    have equation : r • (y - a) = t • v := by
      -- derived from hxary and hxt'
      -- likely linear manipulate hxary : x₀ = a + r • (y-a)
      have hxary' : x₀ = a + r • (y-a) := hxary
      rw [hxt'] at hxary'
      -- hxary': a+t•v= a+r•(y-a)
      -- cancellation
      -- module to transform
      have := add_left_cancel hxary'
      -- wait hxary' after rewrite has a+t•v = a+r ...; add_left_cancel works
      exact this.symm
    have : y - a = (t / r) • v := by
      -- derive via `(r)^{-1}`
      have hrne : r ≠ 0 := ne_of_gt hrpos
      -- apply inverse scalar
      have scal : (r:ℝ)⁻¹ * r = 1 := inv_mul_cancel₀ hrne
      -- scalar action
      calc
        y - a = ((r:ℝ)⁻¹ * r) • (y-a) := by rw [scal]; simp
        _ = (r:ℝ)⁻¹ • (r • (y-a)) := by rw [mul_smul]
        _ = (r:ℝ)⁻¹ • (t • v) := by rw [equation]
        _ = (t / r) • v := by
          rw [smul_smul]
          congr 1
          -- commutativity
          ring
    dsimp [w]
    have := this
    -- rewrite y = a + ... from y-a
    exact (sub_eq_iff_eq_add'.mp this)
  -- all parameters from X are <= w
  have w_is_ub : ∀ z ∈ S, z ≤ w := by
    intro z hz
    rcases hz with ⟨x', hx', hz0, hz1, hxz⟩
    -- use betweenness of x' wrt y
    obtain ⟨k,hk0,hk1,hxky⟩ := normParam x' y (h x' hx' y hy)
    -- uniqueness along nonzero v: z = k*w
    have heq : z = k*w := by
      apply (smul_left_injective ℝ hv)
      -- need equality z • v = (k*w) • v
      have hzv : x' = a + z • v := hxz
      have hxky' : x' = a + k • (y-a) := hxky
      have hya : y-a = w • v := by rw [hyw]; abel_nf --? 
      rw [hya] at hxky'
      rw [smul_smul] at hxky'
      -- compare
      -- add_left_cancel
      exact add_left_cancel (hzv.symm.trans hxky')
    rw [heq]
    calc
      k * w ≤ 1 * w := mul_le_mul_of_nonneg_right hk1 hw0
      _ = w := by ring
  have sle : s ≤ w := by
    dsimp [s]
    exact csSup_le Sne w_is_ub
  -- obtain final affine coefficient between x and y
  by_cases hwu : w = u
  · have hsu : s = u := le_antisymm (by simpa [hwu] using sle) ule
    have hsx : a + s • v = x := by rw [hsu, hxu]
    -- choose coefficient zero
    rw [hsx]
    exact affineBetween_left _ _
  · have hlt : u < w := lt_of_le_of_ne
          (le_trans ule sle) (Ne.symm hwu)
    let q : ℝ := (s-u) / (w-u)
    have hq0 : 0 ≤ q := by
      dsimp [q]
      positivity
    have hq1 : q ≤ 1 := by
      dsimp [q]
      apply (div_le_one (by linarith)).mpr
      linarith
    refine ⟨q, hq0, hq1, ?_⟩
    -- direct calculation with the two line expressions
    rw [hxu, hyw]
    -- goal a+s•v = affine expression
    -- module after prove scalar identity
    have hqeq : s = (1-q)*u + q*w := by
      dsimp [q]
      have hden : w-u ≠ 0 := ne_of_gt (sub_pos.mpr hlt)
      field_simp
      ring
    -- use module + scalar equality
    -- transform RHS
    -- `module` incorporates hqeq?
    calc
      a + s • v = a + (((1-q)*u + q*w)) • v := by rw [hqeq]
      _ = (1-q) • (a + u • v) + q • (a + w • v) := by module

lemma plane2_continuity :
    ∀ X Y : Set Plane2,
      (∃ a, ∀ x ∈ X, ∀ y ∈ Y, AffineBetween Plane2 a x y) →
      (∃ b, ∀ x ∈ X, ∀ y ∈ Y, AffineBetween Plane2 x b y) := by
  intro X Y H
  by_cases xe : X.Nonempty
  · obtain ⟨x,hx⟩ := xe
    by_cases ye : Y.Nonempty
    · obtain ⟨y,hy⟩ := ye
      obtain ⟨a,ha⟩ := H
      by_cases hn : ∃ z ∈ X, z ≠ a
      · obtain ⟨z,hz,hza⟩ := hn
        exact plane2_line_cut X Y a z y hz hy hza ha
      · have allx : ∀ z ∈ X, z = a := by
          intro z hz
          by_contra hza
          exact hn ⟨z,hz,hza⟩
        refine ⟨a, ?_⟩
        intro z hz w hw
        rw [allx z hz]
        exact affineBetween_left _ _
    · refine ⟨x, ?_⟩
      intro z hz w hw
      exact (ye ⟨w,hw⟩).elim
  · refine ⟨0, ?_⟩
    intro x hx y hy
    exact (xe ⟨x,hx⟩).elim

/-- Coordinate Hilbert plane. The field-by-field assembly makes explicit
which pieces of the textbook coordinate model are routine and reusable:
Pasch, five-segment, and upper dimension are the analytic lemmas in the
support modules. -/
def coordinateAbsolute : TarskiAbsolute Plane2 where
  B := AffineBetween Plane2
  C := MetricCongruent
  congr_refl := MetricCongruent.refl_ax
  congr_trans := MetricCongruent.trans_ax
  congr_id := MetricCongruent.id_ax
  segment_construction := by
    intro a b c d
    obtain ⟨x,h,h'⟩ := AffineBetween.segment_metric a b c d
    exact ⟨x,h,h'⟩
  five_segment := by
    intro a b c d a' b' c' d' hn h h' h1 h2 h3 h4
    exact affine_inner_five_segment a b c d a' b' c' d' hn h h' h1 h2 h3 h4
  betw_id := AffineBetween.id_ax
  inner_pasch := AffineBetween.inner_pasch
  lower_dim := plane2_lower
  upper_dim := by
    intro a b c p q hn h1 h2 h3
    exact plane2_upper a b c p q hn h1 h2 h3
  continuity := plane2_continuity

lemma coordinateEuclidean : Euclidean Plane2 coordinateAbsolute := by
  intro a b c d t h h' hn
  exact AffineBetween.euclidean_ax a b c d t h h' hn

/-- Congruence data for the bounded Klein disk.  The earlier affine cut and
parallel obstruction work for any open convex chart; the circular chart is
particularly convenient for the rational Klein length. -/
structure SquareMetricData where
  C : KleinDisk → KleinDisk → KleinDisk → KleinDisk → Prop
  congr_refl : ∀ a b, C a b b a
  congr_trans : ∀ a b c d e f, C a b c d → C a b e f → C c d e f
  congr_id : ∀ a b c, C a b c c → a = b
  segment_construction : ∀ a b c d, ∃ x : KleinDisk,
    DiskBetween a b x ∧ C b x c d
  five_segment : ∀ a b c d a' b' c' d' : KleinDisk, a ≠ b →
    DiskBetween a b c → DiskBetween a' b' c' →
    C a b a' b' → C b c b' c' → C a d a' d' → C b d b' d' →
    C c d c' d'
  upper_dim : ∀ a b c p q : KleinDisk, p ≠ q →
    C p a q a → C p b q b → C p c q c →
    DiskBetween a b c ∨ DiskBetween b c a ∨ DiskBetween c a b
  continuity : ∀ X Y : Set KleinDisk,
    (∃ a, ∀ x ∈ X, ∀ y ∈ Y, DiskBetween a x y) →
      (∃ b, ∀ x ∈ X, ∀ y ∈ Y, DiskBetween x b y)

def SquareMetricData.ofCongruence
    (C : KleinDisk → KleinDisk → KleinDisk → KleinDisk → Prop)
    (h1 : ∀ a b, C a b b a)
    (h2 : ∀ a b c d e f, C a b c d → C a b e f → C c d e f)
    (h3 : ∀ a b c, C a b c c → a = b)
    (h4 : ∀ a b c d, ∃ x : KleinDisk,
      DiskBetween a b x ∧ C b x c d)
    (h5 : ∀ a b c d a' b' c' d' : KleinDisk, a ≠ b →
      DiskBetween a b c → DiskBetween a' b' c' →
      C a b a' b' → C b c b' c' → C a d a' d' → C b d b' d' →
      C c d c' d')
    (h9 : ∀ a b c p q : KleinDisk, p ≠ q →
      C p a q a → C p b q b → C p c q c →
      DiskBetween a b c ∨ DiskBetween b c a ∨ DiskBetween c a b) :
    SquareMetricData where
  C := C
  congr_refl := h1
  congr_trans := h2
  congr_id := h3
  segment_construction := h4
  five_segment := h5
  upper_dim := h9
  continuity := disk_continuity

def SquareMetricData.ofLength
    (L : KleinDisk → KleinDisk → ℝ)
    (symmL : ∀ a b, L a b = L b a)
    (diagL : ∀ a, L a a = 0)
    (sepL : ∀ {a b}, L a b = 0 → a = b)
    (h4 : ∀ a b c d, ∃ x : KleinDisk,
      DiskBetween a b x ∧ L b x = L c d)
    (h5 : ∀ a b c d a' b' c' d' : KleinDisk, a ≠ b →
      DiskBetween a b c → DiskBetween a' b' c' →
      L a b = L a' b' → L b c = L b' c' →
      L a d = L a' d' → L b d = L b' d' → L c d = L c' d')
    (h9 : ∀ a b c p q : KleinDisk, p ≠ q →
      L p a = L q a → L p b = L q b → L p c = L q c →
      DiskBetween a b c ∨ DiskBetween b c a ∨ DiskBetween c a b) :
    SquareMetricData := by
  refine SquareMetricData.ofCongruence
    (LengthCongruent L)
    (LengthCongruent.refl_of_symm L symmL)
    (LengthCongruent.trans_ax' L)
    (LengthCongruent.id_of_zero L diagL sepL)
    ?_ ?_ ?_
  · intro a b c d
    rcases h4 a b c d with ⟨x,hx,hL⟩
    exact ⟨x,hx,hL⟩
  · intro a b c d a' b' c' d' hn h h' h1 h2 h3 h4
    exact h5 a b c d a' b' c' d' hn h h' h1 h2 h3 h4
  · intro a b c p q hn h1 h2 h3
    exact h9 a b c p q hn h1 h2 h3

/-- The length is `sinh(d)^2` in projective Klein coordinates.  Its
numerator is rational.  On a chord it is strictly increasing to the circle;
this supplies segment construction.  Its normalized square root is the
hyperbolic cosine.  Affinity of the latter proves five-segment and makes a
perpendicular bisector an ordinary affine line. -/
lemma square_metric_data : Nonempty SquareMetricData := by
  -- `KleinDisk` for the cut and `GenericKleinDisk Plane2` for the analytic
  -- lemmas are the same subtype, definitionally.
  let L : KleinDisk → KleinDisk → ℝ :=
    fun a b =>
      (1 - inner ℝ a.1 b.1)^2 /
          ((1 - inner ℝ a.1 a.1) * (1 - inner ℝ b.1 b.1)) - 1
  refine ⟨SquareMetricData.ofLength L ?_ ?_ ?_ ?_ ?_ ?_⟩
  · intro a b
    change GenericKleinLength (V:=Plane2) a b =
      GenericKleinLength (V:=Plane2) b a
    exact GenericKleinLength.symm _ _
  · intro a
    change GenericKleinLength (V:=Plane2) a a = 0
    exact GenericKleinLength.diag _
  · intro a b h
    change GenericKleinLength (V:=Plane2) a b = 0 at h
    exact GenericKleinLength.eq_of_zero h
  · intro a b c d
    obtain ⟨x,hx,hh⟩ := planeKlein_segment
      (a : GenericKleinDisk Plane2) (b : GenericKleinDisk Plane2)
      (c : GenericKleinDisk Plane2) (d : GenericKleinDisk Plane2)
    exact ⟨x, hx, hh⟩
  · intro a b c d a' b' c' d' hab hc hc' h1 h2 h3 h4
    change GenericKleinLength (V:=Plane2) a b =
      GenericKleinLength (V:=Plane2) a' b' at h1
    change GenericKleinLength (V:=Plane2) b c =
      GenericKleinLength (V:=Plane2) b' c' at h2
    change GenericKleinLength (V:=Plane2) a d =
      GenericKleinLength (V:=Plane2) a' d' at h3
    change GenericKleinLength (V:=Plane2) b d =
      GenericKleinLength (V:=Plane2) b' d' at h4
    -- the plane analytic lemma reads the chord in exactly the same affine
    -- convention (the middle point is beyond the second argument).
    exact GenericKleinLength.five_segment_plane
      a b c d a' b' c' d' hab hc hc' h1 h2 h3 h4
  · intro a b c p q hpq ha hb hc
    change GenericKleinLength (V:=Plane2) p a =
      GenericKleinLength (V:=Plane2) q a at ha
    change GenericKleinLength (V:=Plane2) p b =
      GenericKleinLength (V:=Plane2) q b at hb
    change GenericKleinLength (V:=Plane2) p c =
      GenericKleinLength (V:=Plane2) q c at hc
    exact GenericKleinLength.upper_dim_plane a b c p q hpq ha hb hc

def squareAbsolute (D : SquareMetricData) : TarskiAbsolute KleinDisk where
  B := DiskBetween
  C := D.C
  congr_refl := D.congr_refl
  congr_trans := D.congr_trans
  congr_id := D.congr_id
  segment_construction := D.segment_construction
  five_segment := D.five_segment
  betw_id := DiskBetween.id_ax
  inner_pasch := DiskBetween.inner_pasch
  lower_dim := disk_lower
  upper_dim := D.upper_dim
  continuity := D.continuity

lemma squareAbsolute_not_euclidean (D : SquareMetricData) :
    ¬ Euclidean KleinDisk (squareAbsolute D) := by
  intro h
  exact disk_not_parallel h
end
end LeanEval.Geometry

/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/


-- END INLINED MAIN PRELUDE

namespace Submission

/-ResultBegin-/

theorem parallel_postulate_independent :
    (∃ (M : Type) (T : TarskiAbsolute M), Euclidean M T) ∧
    (∃ (M : Type) (T : TarskiAbsolute M), ¬ Euclidean M T) :=
/-ResultProofBegin-/by
  classical
  refine ⟨⟨LeanEval.Geometry.Plane2, LeanEval.Geometry.coordinateAbsolute,
      LeanEval.Geometry.coordinateEuclidean⟩, ?_⟩
  obtain ⟨D⟩ := LeanEval.Geometry.square_metric_data
  exact ⟨LeanEval.Geometry.KleinDisk, LeanEval.Geometry.squareAbsolute D,
    LeanEval.Geometry.squareAbsolute_not_euclidean D⟩
/-ResultProofEnd-/
/-ResultEnd-/

end Submission
