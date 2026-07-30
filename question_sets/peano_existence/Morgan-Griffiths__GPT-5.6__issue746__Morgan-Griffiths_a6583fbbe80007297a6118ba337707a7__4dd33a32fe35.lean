import Mathlib

-- BEGIN INLINED FILE: Mathlib/Support/peano_existence_807bb36d9a/FunCompact.lean

open Set Metric Topology Filter
open scoped NNReal
open ODE

noncomputable section

namespace PeanoSupport

/-- A family of functions with a common Lipschitz constant is equicontinuous. This tiny
wrapper is useful because the version of Ascoli for bounded maps asks for the family
indexed by a subtype. -/
lemma equicontinuous_of_lipschitz_family
    {X Y ι : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (C : ℝ≥0) (g : ι → X → Y) (hg : ∀ i, LipschitzWith C (g i)) :
    Equicontinuous g := by
  apply Metric.equicontinuous_of_continuity_modulus (fun t : ℝ => (C : ℝ) * t)
    (by simpa using (Filter.Tendsto.const_mul (C:ℝ)
      (show Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0) from tendsto_id))) g
  intro x y i
  simpa using (hg i).dist_le_mul x y

open BoundedContinuousFunction ContinuousMap

variable {E : Type*} [NormedAddCommGroup E]

/-- On a compact interval, the closed set of curves with a fixed Lipschitz bound and a
bounded value at one point is compact, if closed balls in the range are compact.
This is the precise compactness input (Arzela--Ascoli) needed by the polygonal proof;
the ODE file only proves completeness of this space. -/
lemma funSpace_isCompact_range [ProperSpace E]
    {lo hi : ℝ} {u : Set.Icc lo hi} {x : E} {r L : ℝ≥0} :
    IsCompact (range (fun α : ODE.FunSpace u x r L => α.toContinuousMap)) := by
  -- Write the range by its elementary closed conditions (`PicardLindelof` proves this lemma).
  rw [ODE.FunSpace.range_toContinuousMap]
  let S : Set C(Set.Icc lo hi, E) :=
    {v | LipschitzWith L v ∧ v u ∈ closedBall x r}
  -- A uniform ball containing all the values.
  let R : ℝ := (L : ℝ) * max (hi - (u:ℝ)) ((u:ℝ) - lo) + r
  let K : Set E := closedBall x R
  have hK : IsCompact K := isCompact_closedBall _ _
  have hSin : ∀ (v : C(Set.Icc lo hi, E)) (z : Set.Icc lo hi), v ∈ S → v z ∈ K := by
    intro v z hv
    change dist (v z) x ≤ R
    have hu0 : dist (v u) x ≤ (r:ℝ) := by simpa using hv.2
    calc
      dist (v z) x ≤ dist (v z) (v u) + dist (v u) x := dist_triangle _ _ _
      _ ≤ (L:ℝ) * dist z u + (r:ℝ) := add_le_add (hv.1.dist_le_mul z u) hu0
      _ ≤ (L:ℝ) * max (hi - (u:ℝ)) ((u:ℝ) - lo) + (r:ℝ) := by
        gcongr
        -- diameter from the distinguished point along the interval
        rw [Subtype.dist_eq, Real.dist_eq]
        exact (abs_sub_le_max_sub z.2.1 z.2.2 (u:ℝ))
  have hSclosed : IsClosed S := by
    dsimp [S]
    -- the same closedness calculation as for completeness of `FunSpace`
    apply (isClosed_setOf_lipschitzWith L |>.preimage continuous_coeFun).inter
    have hEval : Continuous (fun v : C(Set.Icc lo hi, E) => v u) := by fun_prop
    exact (isClosed_closedBall : IsClosed (closedBall x (r:ℝ))).preimage hEval
  -- Move to bounded continuous maps. On a compact source this is an isometry equivalence.
  let A : Set (Set.Icc lo hi →ᵇ E) := (ContinuousMap.equivBoundedOfCompact (Set.Icc lo hi) E) '' S
  have hAclosed : IsClosed A := by
    -- the equivalence is a homeomorphism (isometry equivalence);
    -- spelling it through the isometry equivalence gives a homeomorph.
    let e := ContinuousMap.isometryEquivBoundedOfCompact (Set.Icc lo hi) E
    exact (e.toHomeomorph.isClosedMap S hSclosed)
  have hAin : ∀ (v : Set.Icc lo hi →ᵇ E) (z : Set.Icc lo hi), v ∈ A → v z ∈ K := by
    intro v z hv
    rcases hv with ⟨w, hw, rfl⟩
    exact hSin w z hw
  have hAeq : Equicontinuous ((↑) : A → Set.Icc lo hi → E) := by
    apply equicontinuous_of_lipschitz_family L
      ((↑) : A → Set.Icc lo hi → E)
    intro v
    rcases v.property with ⟨w, hw, eq⟩
    -- `equivBoundedOfCompact` is the same function
    change LipschitzWith L (v : Set.Icc lo hi → E)
    -- turn the equality into pointwise equality
    have hvfun : (v : Set.Icc lo hi → E) = (w : Set.Icc lo hi → E) := by
      funext z
      simpa using congrArg (fun q : (Set.Icc lo hi →ᵇ E) => q z) eq.symm
    rw [hvfun]
    exact hw.1
  have hAcompact : IsCompact A :=
    BoundedContinuousFunction.arzela_ascoli₂ K hK A hAclosed hAin hAeq
  -- transfer it back under the homeomorphism
  -- preimage of `A` is exactly `S`
  have himg :
      (ContinuousMap.isometryEquivBoundedOfCompact (Set.Icc lo hi) E).symm '' A = S := by
    ext v
    constructor
    · rintro ⟨w, ⟨v', hv', rfl⟩, rfl⟩
      change (BoundedContinuousFunction.mkOfCompact v').toContinuousMap ∈ S
      have hsame : (BoundedContinuousFunction.mkOfCompact v').toContinuousMap = v' := by
        ext z
        rfl
      rw [hsame]
      exact hv'
    · intro hv
      refine ⟨(ContinuousMap.isometryEquivBoundedOfCompact (Set.Icc lo hi) E) v,
        ⟨v, hv, rfl⟩, by
          ext z
          rfl⟩
  have hSc : IsCompact S := by
    rw [← himg]
    exact hAcompact.image
      (ContinuousMap.isometryEquivBoundedOfCompact (Set.Icc lo hi) E).symm.continuous
  simpa [S] using hSc

/-- In particular `FunSpace` itself is compact. Finite dimensional normed spaces are proper,
so this is the form used for Peano. -/
theorem compactSpace_funSpace [ProperSpace E]
    {lo hi : ℝ} {u : Set.Icc lo hi} {x : E} {r L : ℝ≥0} :
    CompactSpace (ODE.FunSpace u x r L) := by
  let F := (ODE.FunSpace.toContinuousMap (t₀:=u) (x₀:=x) (r:=r) (L:=L))
  have hr : IsCompact (range F) :=
    funSpace_isCompact_range (u:=u) (x:=x) (r:=r) (L:=L)
  letI : CompactSpace (range F) := isCompact_iff_compactSpace.mp hr
  have he : IsEmbedding F := {
    eq_induced := (ODE.FunSpace.isUniformInducing_toContinuousMap
      (t₀:=u) (x₀:=x) (r:=r) (L:=L)).isInducing.eq_induced
    injective := F.injective }
  exact Homeomorph.compactSpace he.toHomeomorph.symm

end PeanoSupport

end

-- END INLINED FILE: Mathlib/Support/peano_existence_807bb36d9a/FunCompact.lean

-- BEGIN INLINED FILE: Mathlib/Support/peano_existence_807bb36d9a/Tonelli.lean

open Set Metric Topology Filter MeasureTheory
open scoped NNReal Interval
open ODE

noncomputable section
namespace PeanoSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The distinguished left end point of `[0,b]`. -/
def zpt (b : ℝ) (hb : 0 ≤ b) : Set.Icc (0:ℝ) b := ⟨0, by simp [hb]⟩

section
variable {f : E → E} {x : E} {a L : ℝ≥0} {b : ℝ} (hb : 0 ≤ b)
  (hf : Continuous f)
  (hLa : (L:ℝ) * b ≤ (a:ℝ))
  (hBd : ∀ y ∈ closedBall x (a:ℝ), ‖f y‖ ≤ (L:ℝ))

abbrev Curves := ODE.FunSpace (zpt b hb) x 0 L

include hLa in
lemma mul_condition : (L:ℝ) * max (b - (zpt b hb:ℝ)) ((zpt b hb:ℝ) - 0) ≤ (a:ℝ) - (0:ℝ≥0) := by
  simpa [zpt, max_eq_left hb] using hLa

include hf in
lemma int_cont (u : Curves hb (x:=x) (L:=L)) (δ : ℝ) :
    Continuous (fun s : ℝ => f (u.compProj (s-δ))) := by
  exact hf.comp (u.continuous_compProj.comp (continuous_id.sub continuous_const))

include hf in
lemma int_int (u : Curves hb (x:=x) (L:=L)) (δ p q : ℝ) :
    IntervalIntegrable (fun s : ℝ => f (u.compProj (s-δ))) volume p q := by
  exact (int_cont hb hf u δ).intervalIntegrable _ _

include hf hLa hBd
/-- Tonelli's delayed Picard operator.  Every use of the field is at an old time `s-δ`.
No spatial Lipschitz assumption enters in its definition or in its Lipschitz estimate. -/
def delayNext (δ : ℝ) : Curves hb (x:=x) (L:=L) → Curves hb (x:=x) (L:=L) := fun u =>
 { toFun := fun t => x + ∫ s in (0:ℝ)..(t:ℝ), f (u.compProj (s-δ))
   lipschitzWith := LipschitzWith.of_dist_le_mul (fun t₁ t₂ => by
     rw [dist_eq_norm, add_sub_add_left_eq_sub,
       intervalIntegral.integral_interval_sub_left (int_int hb hf u δ _ _)
         (int_int hb hf u δ _ _), Subtype.dist_eq, Real.dist_eq]
     apply intervalIntegral.norm_integral_le_of_norm_le_const
     intro s hs
     -- the projection always lands in the ball
     exact hBd _ (u.compProj_mem_closedBall (mul_condition hb hLa) ))
   mem_closedBall₀ := by simp [zpt] }


@[simp] lemma delayNext_apply (δ : ℝ) (u : Curves hb (x:=x) (L:=L))
    (t : Set.Icc (0:ℝ) b) :
    delayNext hb hf hLa hBd δ u t =
      x + ∫ s in (0:ℝ)..(t:ℝ), f (u.compProj (s-δ)) := rfl

lemma curves_zero (u v : Curves hb (x:=x) (L:=L)) :
    u (zpt b hb) = v (zpt b hb) := by
  rw [u.apply_of_zero, v.apply_of_zero]

/-- Comparison of two delayed Picard steps.  Agreement up to time `q` extends to
agreement up to `q+δ`. This is the triangular nature of Tonelli's construction. -/
lemma delayNext_eq_of_le {δ q : ℝ} (hδ : 0 ≤ δ)
    (u v : Curves hb (x:=x) (L:=L))
    (huv : ∀ t : Set.Icc (0:ℝ) b, (t:ℝ) ≤ q → u t = v t) :
    ∀ t : Set.Icc (0:ℝ) b, (t:ℝ) ≤ q + δ →
      delayNext hb hf hLa hBd δ u t = delayNext hb hf hLa hBd δ v t := by
  intro t ht
  rw [delayNext_apply, delayNext_apply]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  change f (u.compProj (s-δ)) = f (v.compProj (s-δ))
  congr 1
  -- split at the left endpoint of the projection
  by_cases hs0 : s - δ ≤ 0
  · have hu0 : u.compProj (s-δ) = u (zpt b hb) := by
      rw [ODE.FunSpace.compProj_apply]
      congr 1
      apply Subtype.ext
      simp [projIcc, hs0]
      change (0:ℝ) = 0
      rfl
    have hv0 : v.compProj (s-δ) = v (zpt b hb) := by
      rw [ODE.FunSpace.compProj_apply]
      congr 1
      apply Subtype.ext
      simp [projIcc, hs0]
      change (0:ℝ) = 0
      rfl
    rw [hu0, hv0, curves_zero (hf:=hf) (hLa:=hLa) (hBd:=hBd) hb u v]
  · have hsnon : 0 ≤ s - δ := le_of_lt (lt_of_not_ge hs0)
    have hst : s ≤ (t:ℝ) := by
      have hh := hs
      -- `integral_congr` presents points of `uIcc`; with `0 ≤ t` it is `Icc 0 t`
      have : s ∈ Set.Icc (0:ℝ) (t:ℝ) := by
        simpa [Set.uIcc_of_le t.2.1] using hs
      exact this.2
    have hsq : s - δ ≤ q := by linarith
    by_cases hsB : s - δ ≤ b
    · have hm : (s-δ) ∈ Set.Icc (0:ℝ) b := ⟨hsnon, hsB⟩
      rw [u.compProj_of_mem hm, v.compProj_of_mem hm]
      exact huv ⟨s-δ, hm⟩ hsq
    · -- this branch cannot happen, since `s ≤ t ≤ b` and `δ ≥ 0`
      have : s ≤ b := hst.trans t.2.2
      exfalso
      apply hsB
      linarith

/-- Successive iterates of the delayed operator agree on the growing initial segment
`[0,nδ]`, independently of the seed. -/
lemma iterate_delayNext_succ_eq (δ : ℝ) (hδ : 0 ≤ δ)
    (u : Curves hb (x:=x) (L:=L)) :
    ∀ n : ℕ, ∀ t : Set.Icc (0:ℝ) b, (t:ℝ) ≤ (n:ℝ) * δ →
      (delayNext hb hf hLa hBd δ)^[n+1] u t =
        (delayNext hb hf hLa hBd δ)^[n] u t := by
  intro n
  induction n with
  | zero =>
      intro t ht
      have ht0 : (t:ℝ) = 0 := by
        have : (t:ℝ) ≤ 0 := by simpa using ht
        exact le_antisymm this t.2.1
      have teq : t = zpt b hb := Subtype.ext ht0
      subst t
      exact curves_zero (E:=E) (x:=x) (L:=L) (f:=f) (a:=a)
        (hf:=hf) (hLa:=hLa) (hBd:=hBd) hb _ _
  | succ n ih =>
      -- applying the comparison lemma to the preceding pair of iterates
      intro t ht
      have H := delayNext_eq_of_le (hb:=hb) (hf:=hf) (hLa:=hLa) (hBd:=hBd)
        hδ
        ((delayNext hb hf hLa hBd δ)^[n+1] u)
        ((delayNext hb hf hLa hBd δ)^[n] u)
        (by
          intro w hw
          exact ih w (by simpa using hw)) t
        (by
          -- `(n+1)δ = nδ + δ`
          simpa [Nat.cast_add, Nat.cast_one, add_mul] using ht)
      simpa [Function.iterate_succ_apply'] using H

/-- At a mesh which covers the interval, the `n`th iterate is an exact fixed point
of the delayed equation on the whole interval. -/
lemma iterate_delayNext_fixed (δ : ℝ) (hδ : 0 ≤ δ) (n : ℕ)
    (hcover : b ≤ (n:ℝ) * δ)
    (u : Curves hb (x:=x) (L:=L)) (t : Set.Icc (0:ℝ) b) :
    (delayNext hb hf hLa hBd δ)^[n] u t =
      x + ∫ s in (0:ℝ)..(t:ℝ),
          f (((delayNext hb hf hLa hBd δ)^[n] u).compProj (s-δ)) := by
  have hseg := iterate_delayNext_succ_eq (hb:=hb) (hf:=hf) (hLa:=hLa)
    (hBd:=hBd) δ hδ u n t (le_trans t.2.2 hcover)
  -- it says `T^(n+1) = T^n`; unfold one step
  simpa [Function.iterate_succ_apply', delayNext_apply] using hseg.symm

end
end PeanoSupport

end

-- END INLINED FILE: Mathlib/Support/peano_existence_807bb36d9a/Tonelli.lean

-- BEGIN INLINED FILE: Mathlib/Support/peano_existence_807bb36d9a/Limit.lean

open Set Metric Topology Filter MeasureTheory
open scoped NNReal Interval Topology
open ODE

noncomputable section
namespace PeanoSupport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {x : E} {L a : ℝ≥0} {b : ℝ} (hb : 0 ≤ b)
-- a few elementary limit facts for delayed curves
abbrev CV := ODE.FunSpace (zpt b (by assumption)) x 0 L

/-- A limit in the fun space may be evaluated at a simultaneously moving point of the
compact interval.  We use the uniform (sup) topology on continuous maps. -/
lemma tendsto_eval_moving
    (u : ℕ → ODE.FunSpace (zpt b hb) x 0 L)
    (v : ODE.FunSpace (zpt b hb) x 0 L)
    (hu : Tendsto u atTop (𝓝 v))
    (q : ℕ → Set.Icc (0:ℝ) b) (q0 : Set.Icc (0:ℝ) b)
    (hq : Tendsto q atTop (𝓝 q0)) :
    Tendsto (fun n => u n (q n)) atTop (𝓝 (v q0)) := by
  -- map the first component to continuous maps (this embedding defines its topology)
  have hmcont : Continuous (fun w : ODE.FunSpace (zpt b hb) x 0 L => w.toContinuousMap) :=
    ODE.FunSpace.isUniformInducing_toContinuousMap.uniformContinuous.continuous
  have hm : Tendsto (fun n => (u n).toContinuousMap) atTop
      (𝓝 v.toContinuousMap) := (hmcont.tendsto v).comp hu
  have hp := hm.prodMk_nhds hq
  have he : Continuous (fun w : (C(Set.Icc (0:ℝ) b, E) × Set.Icc (0:ℝ) b) => w.1 w.2) :=
    ContinuousEval.continuous_eval
  exact (he.tendsto _ |>.comp hp)

lemma tendsto_compProj_delay
    (u : ℕ → ODE.FunSpace (zpt b hb) x 0 L)
    (v : ODE.FunSpace (zpt b hb) x 0 L)
    (hu : Tendsto u atTop (𝓝 v))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 (0:ℝ))) (s : ℝ) :
    Tendsto (fun n => (u n).compProj (s - δ n)) atTop (𝓝 (v.compProj s)) := by
  have hs : Tendsto (fun n => s - δ n) atTop (𝓝 (s - (0:ℝ))) :=
    tendsto_const_nhds.sub hδ
  have hs' : Tendsto (fun n => s - δ n) atTop (𝓝 s) := by simpa using hs
  let h0b : (0:ℝ) ≤ b := hb
  let q : ℕ → Set.Icc (0:ℝ) b := fun n => projIcc 0 b h0b (s - δ n)
  let q0 : Set.Icc (0:ℝ) b := projIcc 0 b h0b s
  have hq : Tendsto q atTop (𝓝 q0) := by
    exact ((continuous_projIcc.tendsto s).comp hs')
  simpa [q, q0, ODE.FunSpace.compProj_apply] using
    (tendsto_eval_moving (hb:=hb) u v hu q q0 hq)

lemma tendsto_field_compProj_delay
    {f : E → E} (hf : Continuous f)
    (u : ℕ → ODE.FunSpace (zpt b hb) x 0 L)
    (v : ODE.FunSpace (zpt b hb) x 0 L)
    (hu : Tendsto u atTop (𝓝 v))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 (0:ℝ))) (s : ℝ) :
    Tendsto (fun n => f ((u n).compProj (s - δ n))) atTop
      (𝓝 (f (v.compProj s))) := by
  exact (hf.tendsto (v.compProj s)).comp
    (tendsto_compProj_delay (hb:=hb) u v hu δ hδ s)

/-- Dominated convergence, on a fixed forward interval, for the fields sampled by delayed
curves.  Only the common closed-ball bound is used for domination. -/
lemma tendsto_intervalIntegral_delay
    {f : E → E} (hf : Continuous f)
    (hLa : (L:ℝ) * b ≤ (a:ℝ))
    (hBd : ∀ y ∈ closedBall x (a:ℝ), ‖f y‖ ≤ (L:ℝ))
    (u : ℕ → ODE.FunSpace (zpt b hb) x 0 L)
    (v : ODE.FunSpace (zpt b hb) x 0 L)
    (hu : Tendsto u atTop (𝓝 v))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 (0:ℝ)))
    (t : Set.Icc (0:ℝ) b) :
    Tendsto (fun n => ∫ s in (0:ℝ)..(t:ℝ), f ((u n).compProj (s - δ n)))
      atTop (𝓝 (∫ s in (0:ℝ)..(t:ℝ), f (v.compProj s))) := by
  let S : Set ℝ := Set.Ioc (0:ℝ) (t:ℝ)
  let μ : Measure ℝ := Measure.restrict volume S
  have hdom := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ:=μ)
    (F:=fun n s => f ((u n).compProj (s - δ n)))
    (f:=fun s => f (v.compProj s))
    (fun _ : ℝ => (L:ℝ))
  have hmeas (n : ℕ) : AEStronglyMeasurable
        (fun s : ℝ => f ((u n).compProj (s - δ n))) μ := by
    -- the integrands are continuous on the line
    have hc : Continuous (fun s : ℝ => f ((u n).compProj (s - δ n))) :=
      hf.comp ((u n).continuous_compProj.comp (continuous_id.sub continuous_const))
    exact hc.aestronglyMeasurable
  have hint : Integrable (fun _ : ℝ => (L:ℝ)) μ := by
    -- finite restriction, constant integrable
    haveI : IsFiniteMeasure μ := by
      dsimp [μ, S]
      infer_instance
    exact MeasureTheory.integrable_const _
  have hboundn (n : ℕ) : ∀ᵐ s ∂μ,
        ‖f ((u n).compProj (s - δ n))‖ ≤ (fun _ : ℝ => (L:ℝ)) s := by
    filter_upwards [] with s
    exact hBd _ ((u n).compProj_mem_closedBall (mul_condition hb hLa))
  have hlim : ∀ᵐ s ∂μ, Tendsto
        (fun n => f ((u n).compProj (s - δ n))) atTop
        (𝓝 (f (v.compProj s))) := by
    filter_upwards [] with s
    exact tendsto_field_compProj_delay (hb:=hb) hf u v hu δ hδ s
  have H := hdom hmeas hint hboundn hlim
  -- write interval integrals as restricted integrals; `0 ≤ t`
  simpa [μ, S, intervalIntegral.integral_of_le t.2.1] using H
end PeanoSupport

end

-- END INLINED FILE: Mathlib/Support/peano_existence_807bb36d9a/Limit.lean

namespace Submission

-- BEGIN INLINED FILE: Main.lean

open Filter Topology MeasureTheory
open scoped Interval

open Set Metric
open scoped NNReal
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem peano_existence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → E} (hf : Continuous f) (x₀ : E) :
    ∃ a : ℝ, 0 < a ∧ ∃ α : ℝ → E, α 0 = x₀ ∧
      ∀ t ∈ Ioo (-a) a, HasDerivAt α (f (α t)) t :=
/-ResultProofBegin-/by
  classical
  letI : ProperSpace E := FiniteDimensional.proper ℝ E
  have hc : IsCompact (f '' (closedBall x₀ (1:ℝ))) :=
    (isCompact_closedBall x₀ (1:ℝ)).image hf
  obtain ⟨C, hC⟩ := hc.isBounded.exists_norm_le
  let M : ℝ := max 1 C
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hbound : ∀ y ∈ closedBall x₀ (1:ℝ), ‖f y‖ ≤ M := by
    intro y hy
    exact (hC _ ⟨y, hy, rfl⟩).trans (le_max_right _ _)
  let L : ℝ≥0 := ⟨M, le_of_lt hM⟩
  let b : ℝ := 1 / M
  have hb : 0 < b := one_div_pos.mpr hM
  have hLa : (L:ℝ) * b ≤ (1:ℝ≥0) := by
    change M * (1 / M) ≤ (1:ℝ)
    simp [div_eq_mul_inv, hM.ne']
  -- compactness and exact delayed solutions on this interval are the two ingredients
  let z := PeanoSupport.zpt b hb.le
  let P := ODE.FunSpace z x₀ 0 L
  have hpc : CompactSpace P :=
    PeanoSupport.compactSpace_funSpace (u:=z) (x:=x₀) (r:=0) (L:=L)
  letI : CompactSpace P := hpc
  have hBd : ∀ y ∈ Metric.closedBall x₀ ((1:ℝ≥0):ℝ), ‖f y‖ ≤ (L:ℝ) := by
    intro y hy
    change ‖f y‖ ≤ M
    exact hbound y (by simpa using hy)
  let d : ℕ → ℝ := fun n => b / (n+1:ℕ)
  let seed : P := default
  let ps : ℕ → P := fun n =>
    (PeanoSupport.delayNext hb.le hf hLa hBd (d n))^[n+1] seed
  have hd (n : ℕ) : 0 ≤ d n := by
    dsimp [d]
    exact div_nonneg hb.le (by exact_mod_cast (Nat.zero_le (n+1)))
  have hcov (n : ℕ) : b ≤ ((n+1:ℕ):ℝ) * d n := by
    dsimp [d]
    have hn : (0:ℝ) < (n+1:ℕ) := by exact_mod_cast (Nat.zero_lt_succ n)
    calc b ≤ b := le_rfl
         _ = ((n+1:ℕ):ℝ) * (b / (n+1:ℕ)) := by field_simp
  have hps (n : ℕ) (t : Set.Icc (0:ℝ) b) :
      ps n t = x₀ + ∫ s in (0:ℝ)..(t:ℝ), f ((ps n).compProj (s-d n)) := by
    exact PeanoSupport.iterate_delayNext_fixed (hb:=hb.le) (hf:=hf)
      (hLa:=hLa) (hBd:=hBd) (d n) (hd n) (n+1) (hcov n) seed t
  obtain ⟨v, -, k, hk, hkv⟩ :
      ∃ v ∈ (Set.univ : Set P), ∃ k, StrictMono k ∧
        Filter.Tendsto (ps ∘ k) Filter.atTop (nhds v) :=

    (isCompact_univ : IsCompact (Set.univ : Set P)).isSeqCompact
      (x:=ps) (fun n => Set.mem_univ _)

  -- the mesh tends to zero, also along the extracted subsequence
  have hdlim0 : Filter.Tendsto d Filter.atTop (nhds (0:ℝ)) := by
    have hbase := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
    have hmul : Filter.Tendsto (fun n : ℕ => b * (1 / ((n:ℝ) + 1)))
        Filter.atTop (nhds (b * (0:ℝ))) :=
      tendsto_const_nhds.mul hbase
    simpa [d, Nat.cast_add, Nat.cast_one, div_eq_mul_inv] using hmul
  have hdk0 : Filter.Tendsto (fun n => d (k n)) Filter.atTop (nhds (0:ℝ)) :=
    hdlim0.comp hk.tendsto_atTop
  have hu : Filter.Tendsto (fun n => ps (k n)) Filter.atTop (nhds v) := by
    simpa [Function.comp_def] using hkv
  have hinteg (t : Set.Icc (0:ℝ) b) :
      Filter.Tendsto
        (fun n => ∫ s in (0:ℝ)..(t:ℝ), f ((ps (k n)).compProj (s-d (k n))))
        Filter.atTop (nhds (∫ s in (0:ℝ)..(t:ℝ), f (v.compProj s))) := by
    exact PeanoSupport.tendsto_intervalIntegral_delay (hb:=hb.le) hf hLa hBd
      (fun n => ps (k n)) v hu (fun n => d (k n)) hdk0 t
  have heval (t : Set.Icc (0:ℝ) b) :
      Filter.Tendsto (fun n => ps (k n) t) Filter.atTop (nhds (v t)) := by
    -- constant moving point is enough
    exact PeanoSupport.tendsto_eval_moving (hb:=hb.le) (fun n => ps (k n)) v hu
      (fun _ => t) t tendsto_const_nhds
  have hveq (t : Set.Icc (0:ℝ) b) :
      v t = x₀ + ∫ s in (0:ℝ)..(t:ℝ), f (v.compProj s) := by
    have hr : Filter.Tendsto
        (fun n => x₀ + ∫ s in (0:ℝ)..(t:ℝ), f ((ps (k n)).compProj (s-d (k n))))
        Filter.atTop (nhds (x₀ + ∫ s in (0:ℝ)..(t:ℝ), f (v.compProj s))) :=
      tendsto_const_nhds.add (hinteg t)
    have ee := heval t
    have eqn : (fun n => ps (k n) t) =
        (fun n => x₀ + ∫ s in (0:ℝ)..(t:ℝ), f ((ps (k n)).compProj (s-d (k n)))) := by
      funext n
      exact hps (k n) t
    rw [eqn] at ee
    exact tendsto_nhds_unique ee hr

  let gp : ℝ → E := fun t => f (v.compProj t)
  have hcgp : Continuous gp := hf.comp v.continuous_compProj
  let w : ℝ → E := fun t => x₀ + ∫ s in (0:ℝ)..t, gp s
  have hw_deriv (t : ℝ) : HasDerivAt w (gp t) t := by
    dsimp [w]
    exact (intervalIntegral.integral_hasDerivAt_right
      (hcgp.intervalIntegrable (0:ℝ) t)
      hcgp.aestronglyMeasurable.stronglyMeasurableAtFilter hcgp.continuousAt).const_add x₀
  have hw0 : w 0 = x₀ := by simp [w]
  have hw_eq (t : Set.Icc (0:ℝ) b) : w t = v t := by
    simpa [w, gp] using (hveq t).symm
  have hw_good (t : ℝ) (ht0 : 0 ≤ t) (htb : t ≤ b) :
      HasDerivAt w (f (w t)) t := by
    have hm : t ∈ Set.Icc (0:ℝ) b := ⟨ht0, htb⟩
    have val : w t = v.compProj t := by
      calc w t = v (⟨t, hm⟩ : Set.Icc (0:ℝ) b) := hw_eq ⟨t, hm⟩
           _ = v.compProj t := by symm; exact ODE.FunSpace.compProj_of_mem hm
    simpa [gp, val] using hw_deriv t

  -- run the same delayed construction for the reversed vector field
  let fm : E → E := fun y => - f y
  have hfm : Continuous fm := hf.neg
  have hBdm : ∀ y ∈ Metric.closedBall x₀ ((1:ℝ≥0):ℝ), ‖fm y‖ ≤ (L:ℝ) := by
    intro y hy
    simpa [fm] using hBd y hy
  let psm : ℕ → P := fun n =>
    (PeanoSupport.delayNext hb.le hfm hLa hBdm (d n))^[n+1] seed
  have hpsm (n : ℕ) (t : Set.Icc (0:ℝ) b) :
      psm n t = x₀ + ∫ s in (0:ℝ)..(t:ℝ), fm ((psm n).compProj (s-d n)) := by
    exact PeanoSupport.iterate_delayNext_fixed (hb:=hb.le) (hf:=hfm)
      (hLa:=hLa) (hBd:=hBdm) (d n) (hd n) (n+1) (hcov n) seed t
  obtain ⟨vm, -, km, hkm, hkmv⟩ :
      ∃ v ∈ (Set.univ : Set P), ∃ k, StrictMono k ∧
        Filter.Tendsto (psm ∘ k) Filter.atTop (nhds v) :=
    (isCompact_univ : IsCompact (Set.univ : Set P)).isSeqCompact
      (x:=psm) (fun n => Set.mem_univ _)
  have hum : Filter.Tendsto (fun n => psm (km n)) Filter.atTop (nhds vm) := by
    simpa [Function.comp_def] using hkmv
  have hdkm0 : Filter.Tendsto (fun n => d (km n)) Filter.atTop (nhds (0:ℝ)) :=
    hdlim0.comp hkm.tendsto_atTop
  have hmint (t : Set.Icc (0:ℝ) b) :
      Filter.Tendsto
        (fun n => ∫ s in (0:ℝ)..(t:ℝ), fm ((psm (km n)).compProj (s-d (km n))))
        Filter.atTop (nhds (∫ s in (0:ℝ)..(t:ℝ), fm (vm.compProj s))) :=
    PeanoSupport.tendsto_intervalIntegral_delay (hb:=hb.le) hfm hLa hBdm
      (fun n => psm (km n)) vm hum (fun n => d (km n)) hdkm0 t
  have hmev (t : Set.Icc (0:ℝ) b) :
      Filter.Tendsto (fun n => psm (km n) t) Filter.atTop (nhds (vm t)) :=
    PeanoSupport.tendsto_eval_moving (hb:=hb.le) (fun n => psm (km n)) vm hum
      (fun _ => t) t tendsto_const_nhds
  have hvmeq (t : Set.Icc (0:ℝ) b) :
      vm t = x₀ + ∫ s in (0:ℝ)..(t:ℝ), fm (vm.compProj s) := by
    have rr : Filter.Tendsto
        (fun n => x₀ + ∫ s in (0:ℝ)..(t:ℝ), fm ((psm (km n)).compProj (s-d (km n))))
        Filter.atTop (nhds (x₀ + ∫ s in (0:ℝ)..(t:ℝ), fm (vm.compProj s))) :=
      tendsto_const_nhds.add (hmint t)
    have ee := hmev t
    have eqn : (fun n => psm (km n) t) =
        (fun n => x₀ + ∫ s in (0:ℝ)..(t:ℝ), fm ((psm (km n)).compProj (s-d (km n)))) := by
      funext n
      exact hpsm (km n) t
    rw [eqn] at ee
    exact tendsto_nhds_unique ee rr
  let gm : ℝ → E := fun t => fm (vm.compProj t)
  have hcgm : Continuous gm := hfm.comp vm.continuous_compProj
  let wm : ℝ → E := fun t => x₀ + ∫ s in (0:ℝ)..t, gm s
  have hwmder (t : ℝ) : HasDerivAt wm (gm t) t := by
    dsimp [wm]
    exact (intervalIntegral.integral_hasDerivAt_right
      (hcgm.intervalIntegrable (0:ℝ) t)
      hcgm.aestronglyMeasurable.stronglyMeasurableAtFilter hcgm.continuousAt).const_add x₀
  have hwm0 : wm 0 = x₀ := by simp [wm]
  have hwmeq (t : Set.Icc (0:ℝ) b) : wm t = vm t := by
    simpa [wm, gm] using (hvmeq t).symm
  have hwmgood (t : ℝ) (ht0 : 0 ≤ t) (htb : t ≤ b) :
      HasDerivAt wm (fm (wm t)) t := by
    have hm' : t ∈ Set.Icc (0:ℝ) b := ⟨ht0, htb⟩
    have val : wm t = vm.compProj t := by
      calc wm t = vm (⟨t, hm'⟩ : Set.Icc (0:ℝ) b) := hwmeq ⟨t, hm'⟩
           _ = vm.compProj t := by symm; exact ODE.FunSpace.compProj_of_mem hm'
    simpa [gm, val] using hwmder t
  let wn : ℝ → E := fun t => wm (-t)
  have hwn0 : wn 0 = x₀ := by simp [wn, hwm0]
  have hwnder (t : ℝ) (ht0 : 0 ≤ -t) (htb : -t ≤ b) :
      HasDerivAt wn (f (wn t)) t := by
    have H := (hwmgood (-t) ht0 htb).scomp t (hasDerivAt_neg t)
    -- chain rule changes sign of the derivative of the reversed equation
    have HH : HasDerivAt (wm ∘ fun q : ℝ => -q)
          ((-1 : ℝ) • fm (wm (-t))) t := by simpa using H
    simpa [wn, fm, Function.comp_def] using HH
  let α : ℝ → E := fun t => if 0 ≤ t then w t else wn t
  have ha0 : α 0 = x₀ := by simp [α, hw0]
  refine ⟨b, hb, α, ha0, ?_⟩
  intro t ht
  rcases ht with ⟨htl, htu⟩
  by_cases hp0 : 0 < t
  · have ht0 : 0 ≤ t := hp0.le
    have H := hw_good t ht0 (le_of_lt htu)
    have ev : α =ᶠ[nhds t] w := by
      filter_upwards [Ioi_mem_nhds hp0] with q hq
      have hq0 : 0 ≤ q := le_of_lt hq
      simp [α, hq0]
    have eqv : α t = w t := by simp [α, ht0]
    -- replace both the function and its value
    simpa [eqv] using H.congr_of_eventuallyEq ev
  · by_cases hn0 : t < 0
    · have ht0 : 0 ≤ -t := (neg_nonneg.mpr hn0.le)
      have htb : -t ≤ b := by linarith
      have H := hwnder t ht0 htb
      have ev : α =ᶠ[nhds t] wn := by
        have hh : Iio (0:ℝ) ∈ nhds t := Iio_mem_nhds hn0
        filter_upwards [hh] with q hq
        simp [α, not_le_of_gt (show q < 0 from hq)]
      have eqv : α t = wn t := by simp [α, not_le_of_gt hn0]
      simpa [eqv] using H.congr_of_eventuallyEq ev
    · have tz : t = 0 := by linarith
      subst t
      -- glue the two one-sided derivatives at the origin
      have Hw : HasDerivAt w (f x₀) 0 := by
        have z : (0:ℝ) ≤ b := hb.le
        simpa [hw0] using hw_good 0 le_rfl z
      have Hn : HasDerivAt wn (f x₀) 0 := by
        simpa [hwn0] using hwnder 0 (by simp) (by simpa using hb.le)
      have hright : HasDerivWithinAt α (f x₀) (Ici (0:ℝ)) 0 := by
        refine Hw.hasDerivWithinAt.congr ?_ ?_
        · intro q hq
          have : 0 ≤ q := hq
          simp [α, this]
        · simp [ha0, hw0]
      have hleft : HasDerivWithinAt α (f x₀) (Iic (0:ℝ)) 0 := by
        refine Hn.hasDerivWithinAt.congr ?_ ?_
        · intro q hq
          by_cases hz : 0 ≤ q
          · have zq : q = 0 := le_antisymm hq hz
            subst q; simp [α, hw0, hwn0]
          · simp [α, hz]
        · simp [ha0, hwn0]
      have hall := hleft.union hright
      rw [Iic_union_Ici] at hall
      have final : HasDerivAt α (f x₀) 0 := hasDerivWithinAt_univ.mp hall
      simpa [ha0] using final
/-ResultProofEnd-/
/-ResultEnd-/
-- END INLINED FILE: Main.lean

end Submission
