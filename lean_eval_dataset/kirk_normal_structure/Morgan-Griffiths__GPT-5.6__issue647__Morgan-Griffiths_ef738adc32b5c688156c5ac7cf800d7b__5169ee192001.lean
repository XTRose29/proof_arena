import Mathlib

namespace Submission

namespace LeanEval.Topology.KirkNormalStructure

/-!
# Kirk's normal-structure fixed point theorem

`kirk_normal_structure`: a nonexpansive self-map of a nonempty bounded closed
convex subset of a reflexive Banach space with normal structure has a fixed
point. Reflexivity is genuine Banach-space reflexivity (surjectivity of the
canonical embedding into the bidual), avoiding the collapse to the
finite-dimensional case caused by algebraic reflexivity. Helpers
`metricDiameter`, `pointRadiusIn`, `IsDiametralPoint`, `HasNormalStructure`
and `IsNonexpansiveSelfMap` express the geometric hypotheses. Category-(b)
candidate from §228 of the Knill survey.
-/

open Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The diameter of a set, as a real supremum of all pairwise distances inside
the set.  This keeps the normal-structure statement in ordinary metric
language. -/
noncomputable def metricDiameter (s : Set E) : ℝ :=
  sSup {r : ℝ | ∃ x ∈ s, ∃ y ∈ s, dist x y = r}

/-- Radius of a point relative to a set, i.e. the supremum of its distances to
points of the set. -/
noncomputable def pointRadiusIn (x : E) (s : Set E) : ℝ :=
  sSup {r : ℝ | ∃ y ∈ s, dist x y = r}

/-- A point is diametral in `s` if its radius in `s` is the diameter of `s`. -/
def IsDiametralPoint (s : Set E) (x : E) : Prop :=
  x ∈ s ∧ pointRadiusIn x s = metricDiameter s

/-- A bounded convex set has normal structure if every nontrivial convex subset
contains a non-diametral point. -/
def HasNormalStructure (K : Set E) : Prop :=
  ∀ H : Set E,
    H ⊆ K →
      Convex ℝ H →
        H.Nontrivial →
          ∃ x ∈ H, ¬ IsDiametralPoint H x

/-- A self-map of a set is nonexpansive when it is `1`-Lipschitz for the
subtype metric. -/
def IsNonexpansiveSelfMap (K : Set E) (T : K → K) : Prop :=
  LipschitzWith 1 T



end LeanEval.Topology.KirkNormalStructure

open LeanEval.Topology.KirkNormalStructure
open Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/


/-- We keep weak closedness concrete: a subset of `E` is weakly closed when
its image in the weak space is closed.  Using an image rather than a preimage
is harmless here since `toWeakSpace` is a bijection; it is a convenient
interface for compactness. -/
def KirkWeakClosed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Set E) : Prop :=
  IsClosed ((toWeakSpace ℝ E : E → WeakSpace ℝ E) '' s)

/-- The part of the image of `A` under a self map of `K`. -/
def kirkImage {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (T : K → K) (A : Set E) : Set E :=
  { z : E | ∃ x : K, (x : E) ∈ A ∧ (T x : E) = z }

/-- The sets to which the minimal-set argument for Kirk's theorem is applied. -/
def KirkCandidate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (T : K → K) (A : Set E) : Prop :=
  A ⊆ K ∧ A.Nonempty ∧ Convex ℝ A ∧ KirkWeakClosed A ∧
    (∀ x : K, (x : E) ∈ A → (T x : E) ∈ A)

/-- A weakly closed set is closed for the norm topology.  The identity map
from the norm topology to the weak topology is continuous. -/
lemma kirk_normClosed_of_weakClosed {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Set E} (hs : KirkWeakClosed s) : IsClosed s := by
  -- take a preimage of the closed image by the continuous identity map
  have hc : Continuous (toWeakSpaceCLM ℝ E) :=
    (toWeakSpaceCLM ℝ E).cont
  have hp : ( (toWeakSpace ℝ E : E → WeakSpace ℝ E) ⁻¹'
          ((toWeakSpace ℝ E : E → WeakSpace ℝ E) '' s)) = s :=
    Set.preimage_image_eq s (toWeakSpace ℝ E).injective
  have hi : IsClosed
      ( (toWeakSpaceCLM ℝ E : E → WeakSpace ℝ E) ⁻¹'
          ((toWeakSpace ℝ E : E → WeakSpace ℝ E) '' s)) :=
    hs.preimage hc
  -- the two identity maps have the same underlying function
  change IsClosed
      ((toWeakSpace ℝ E : E → WeakSpace ℝ E) ⁻¹'
        ((toWeakSpace ℝ E : E → WeakSpace ℝ E) '' s)) at hi
  rw [hp] at hi
  exact hi

/-- For convex sets, norm closedness and weak closedness agree. -/
lemma kirk_isClosed_weak_image {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (s : Set E) (hs : IsClosed s) (hconv : Convex ℝ s) :
    KirkWeakClosed s := by
  unfold KirkWeakClosed
  have hEq : (toWeakSpace ℝ E : E → WeakSpace ℝ E) '' s =
        closure ((toWeakSpace ℝ E : E → WeakSpace ℝ E) '' s) := by
    simpa [hs.closure_eq] using (Convex.toWeakSpace_closure ℝ hconv)
  -- the right hand side is a closure in the weak topology
  rw [hEq]
  exact isClosed_closure

/-- Existence of an inclusion-minimal nonempty weakly closed convex invariant
subset of `K`.

This is the weak-compactness step of the Kirk argument.  Reflexivity is used
only here: the weak double-dual embedding is onto, and Alaoglu gives
compactness of a bounded weak set.  Intersections of a nested nonempty family
of candidates are then nonempty by compactness; Zorn is applied to their
(relative) complements so that ordinary `zorn_subset_nonempty` gives the
*minimal* candidate. -/
lemma kirk_exists_minimal_candidate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (hE_reflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E))
    (K : Set E) (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K)
    (hK_bounded : Bornology.IsBounded K) (hK_convex : Convex ℝ K)
    (T : K → K) :
    ∃ A : Set E, KirkCandidate K T A ∧
      (∀ {B : Set E}, KirkCandidate K T B → B ⊆ A → A ⊆ B) := by
  classical
  let e : E ≃ₗ[ℝ] WeakSpace ℝ E := toWeakSpace ℝ E
  -- The weak double-dual embedding is surjective as a map of underlying
  -- sets: the change from strong to weak dual is just an identity linear
  -- equivalence.
  have hsurjWeak : Function.Surjective
      (NormedSpace.inclusionInDoubleDualWeak ℝ E) := by
    intro y
    have hy : ∃ x : E,
        (NormedSpace.inclusionInDoubleDual ℝ E) x =
          (WeakDual.toStrongDual y) := hE_reflexive _
    rcases hy with ⟨x, hx⟩
    refine ⟨(toWeakSpace ℝ E) x, ?_⟩
    -- equality of weak functionals follows by evaluation
    apply DFunLike.ext _ _
    intro f
    -- the two representations of a weak dual have the same evaluation
    have hf := congrArg (fun (g : StrongDual ℝ (StrongDual ℝ E)) => g f) hx
    calc
      ((NormedSpace.inclusionInDoubleDualWeak ℝ E) ((toWeakSpace ℝ E) x)) f = f x := by rfl
      _ = y f := by simpa using hf
  have hKweak : KirkWeakClosed K :=
    kirk_isClosed_weak_image K hK_closed hK_convex
  let S : Set (WeakSpace ℝ E) :=
    (toWeakSpace ℝ E : E → WeakSpace ℝ E) '' K
  have hSclosed : IsClosed S := by
    simpa [S, KirkWeakClosed] using hKweak
  have hpre : ( (toWeakSpace ℝ E : E → WeakSpace ℝ E) ⁻¹' S) = K := by
    simpa [S] using
      (Set.preimage_image_eq K (toWeakSpace ℝ E).injective)
  have hbS : Bornology.IsBounded
      ((toWeakSpace ℝ E : E → WeakSpace ℝ E) ⁻¹' S) := by
    simpa [hpre] using hK_bounded
  have hcompS : IsCompact S := by
    have hrange : closure
          ((NormedSpace.inclusionInDoubleDualWeak ℝ E :
              WeakSpace ℝ E → WeakDual ℝ (StrongDual ℝ E)) '' S) ⊆
          Set.range (NormedSpace.inclusionInDoubleDualWeak ℝ E) := by
      intro y hy
      exact hsurjWeak y
    have hc := NormedSpace.isCompact_closure_of_isBounded
      (𝕜 := ℝ) (X := E) S hbS hrange
    simpa [hSclosed.closure_eq] using hc
  have hKcand : KirkCandidate K T K := by
    refine ⟨fun x hx => hx, hK_nonempty, hK_convex, hKweak, ?_⟩
    intro x hx
    exact (T x).property

  -- Work with complements inside `K`; an upper bound of a chain of
  -- complements corresponds to the intersection of the candidates.
  let Cs : Set (Set E) :=
    {C : Set E | C ⊆ K ∧ KirkCandidate K T (K \ C)}
  have hchain : ∀ c ⊆ Cs,
        IsChain (fun x1 x2 : Set E => x1 ⊆ x2) c → c.Nonempty →
          ∃ ub ∈ Cs, ∀ s ∈ c, s ⊆ ub := by
    intro c hcsub hc hn
    classical
    letI : Nonempty c := hn.to_subtype
    let Aint : Set E := ⋂ i : c, K \ (i : Set E)
    let U : c → Set (WeakSpace ℝ E) :=
      fun i => (toWeakSpace ℝ E : E → WeakSpace ℝ E) ''
          (K \ (i : Set E))
    have hiCand (i : c) : KirkCandidate K T (K \ (i : Set E)) :=
      (hcsub i.property).2
    have hUclosed (i : c) : IsClosed (U i) := by
      simpa [U, KirkWeakClosed] using (hiCand i).2.2.2.1
    have hUsub (i : c) : U i ⊆ S := by
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact ⟨x, (hiCand i).1 hx, rfl⟩
    have hUcompact (i : c) : IsCompact (U i) :=
      IsCompact.of_isClosed_subset hcompS (hUclosed i) (hUsub i)
    have hUnon (i : c) : (U i).Nonempty := by
      rcases (hiCand i).2.1 with ⟨x, hx⟩
      exact ⟨(toWeakSpace ℝ E) x, ⟨x, hx, rfl⟩⟩
    have hUdir : Directed (fun s t : Set (WeakSpace ℝ E) => s ⊇ t) U := by
      intro i j
      rcases hc.total i.property j.property with hij | hji
      · refine ⟨j, ?_, ?_⟩
        · -- a larger complement gives a smaller candidate
          intro y hy
          rcases hy with ⟨x, hx, rfl⟩
          refine ⟨x, ?_, rfl⟩
          exact ⟨hx.1, fun hxi => hx.2 (hij hxi)⟩
        · exact fun _ h => h
      · refine ⟨i, ?_, ?_⟩
        · exact fun _ h => h
        · intro y hy
          rcases hy with ⟨x, hx, rfl⟩
          refine ⟨x, ?_, rfl⟩
          exact ⟨hx.1, fun hxj => hx.2 (hji hxj)⟩
    have hnonweak : (⋂ i : c, U i).Nonempty :=
      IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
        U hUdir hUnon hUcompact hUclosed
    have himg :
        (toWeakSpace ℝ E : E → WeakSpace ℝ E) '' Aint =
          (⋂ i : c, U i) := by
      simpa [Aint, U] using
        (Set.image_iInter (f := (toWeakSpace ℝ E : E → WeakSpace ℝ E))
          (toWeakSpace ℝ E).bijective
          (fun i : c => K \ (i : Set E)))
    have hAn : Aint.Nonempty := by
      rw [← himg] at hnonweak
      rcases hnonweak with ⟨z, hz⟩
      rcases hz with ⟨x, hx, rfl⟩
      exact ⟨x, hx⟩
    have hAsub : Aint ⊆ K := by
      intro x hx
      -- any member of the chain witnesses a containing candidate
      rcases hn with ⟨i, hi⟩
      have hxi : x ∈ K \ i := (Set.mem_iInter.1 hx) ⟨i, hi⟩
      exact hxi.1
    have hAconv : Convex ℝ Aint := by
      unfold Aint
      exact convex_iInter (fun i : c => (hiCand i).2.2.1)
    have hAweak : KirkWeakClosed Aint := by
      unfold KirkWeakClosed
      rw [himg]
      exact isClosed_iInter (fun i : c => hUclosed i)
    have hAinv : ∀ x : K, (x : E) ∈ Aint → (T x : E) ∈ Aint := by
      intro x hx
      -- invariance holds in every member of the intersection
      refine Set.mem_iInter.2 ?_
      intro i
      exact (hiCand i).2.2.2.2 x (Set.mem_iInter.1 hx i)
    have hAcand : KirkCandidate K T Aint :=
      ⟨hAsub, hAn, hAconv, hAweak, hAinv⟩
    let ub : Set E := ⋃₀ c
    have hubsub : ub ⊆ K := by
      intro x hx
      rcases Set.mem_sUnion.1 hx with ⟨i, hi, hxi⟩
      exact (hcsub hi).1 hxi
    have hdiff : (K \ ub) = Aint := by
      ext x
      constructor
      · intro hx
        refine Set.mem_iInter.2 ?_
        intro i
        exact ⟨hx.1, fun hxi => hx.2
          (Set.mem_sUnion.2 ⟨(i : Set E), i.property, hxi⟩)⟩
      · intro hx
        have hxall := Set.mem_iInter.1 hx
        have hxK : x ∈ K := hAsub hx
        refine ⟨hxK, ?_⟩
        intro hxu
        rcases Set.mem_sUnion.1 hxu with ⟨i, hi, hxi⟩
        exact (hxall ⟨i, hi⟩).2 hxi
    have hubcand : KirkCandidate K T (K \ ub) := by
      -- just the same intersection
      simpa [hdiff] using hAcand
    refine ⟨ub, ?_, ?_⟩
    · exact ⟨hubsub, hubcand⟩
    · intro s hs
      exact fun x hx => Set.mem_sUnion.2 ⟨s, hs, hx⟩
  have hempty : (∅ : Set E) ∈ Cs := by
    change (∅ : Set E) ⊆ K ∧ KirkCandidate K T (K \ (∅ : Set E))
    refine ⟨Set.empty_subset _, ?_⟩
    simpa using hKcand
  obtain ⟨m, hm0, hmmax⟩ :=
    zorn_subset_nonempty Cs hchain (∅ : Set E) hempty
  have hmCs : m ∈ Cs := hmmax.1
  have hmcsub : m ⊆ K := hmCs.1
  let A : Set E := K \ m
  have hAcand : KirkCandidate K T A := hmCs.2
  refine ⟨A, hAcand, ?_⟩
  intro B hB hBA
  have hBsub : B ⊆ K := hB.1
  let d : Set E := K \ B
  have hdsub : d ⊆ K := fun x hx => hx.1
  have hdCand : KirkCandidate K T (K \ d) := by
    have hdd : K \ (K \ B) = B :=
      Set.sdiff_sdiff_cancel_left hBsub
    simpa [d, hdd] using hB
  have hdCs : d ∈ Cs := ⟨hdsub, hdCand⟩
  have hmd : m ⊆ d := by
    intro x hx
    have hxK : x ∈ K := hmcsub hx
    refine ⟨hxK, ?_⟩
    intro hxB
    have hxA : x ∈ A := hBA hxB
    exact hxA.2 hx
  have hdm : d ⊆ m := hmmax.2 hdCs hmd
  -- Taking complements again reverses the inclusion.
  intro x hxA
  have hxK : x ∈ K := hxA.1
  by_contra hxB
  have hxd : x ∈ d := ⟨hxK, hxB⟩
  exact hxA.2 (hdm hxd)



/-- Every distance from a point to a bounded set is below its (real)
supremum radius. -/
lemma kirk_dist_le_radius {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {K A : Set E}
    (hKb : Bornology.IsBounded K) (hAK : A ⊆ K) (_hAn : A.Nonempty)
    (x : E) {y : E} (hy : y ∈ A) :
    dist x y ≤ pointRadiusIn x A := by
  have hAb : Bornology.IsBounded A := hKb.subset hAK
  rcases (Metric.isBounded_iff_subset_closedBall x).1 hAb with ⟨C, hC⟩
  have hUpper : BddAbove {r : ℝ | ∃ z ∈ A, dist x z = r} := by
    refine (bddAbove_def).2 ⟨C, ?_⟩
    intro r hr
    rcases hr with ⟨z, hz, rfl⟩
    have hz' := hC hz
    -- membership in a ball is written with the centre on the right
    have hzle : dist z x ≤ C := Metric.mem_closedBall.1 hz'
    simpa [dist_comm] using hzle
  unfold pointRadiusIn
  exact le_csSup hUpper ⟨y, hy, rfl⟩

/-- A point which belongs to a bounded nonempty set has radius at most that
set's diameter. -/
lemma kirk_radius_le_diameter {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {K A : Set E}
    (hKb : Bornology.IsBounded K) (hAK : A ⊆ K) (hAn : A.Nonempty)
    {x : E} (hx : x ∈ A) :
    pointRadiusIn x A ≤ metricDiameter A := by
  have hAb : Bornology.IsBounded A := hKb.subset hAK
  rcases (Metric.isBounded_iff).1 hAb with ⟨C, hC⟩
  have hpairUpper : BddAbove
      {r : ℝ | ∃ u ∈ A, ∃ v ∈ A, dist u v = r} := by
    refine (bddAbove_def).2 ⟨C, ?_⟩
    intro r hr
    rcases hr with ⟨u, hu, v, hv, rfl⟩
    exact hC hu hv
  have hdiam (y : E) (hy : y ∈ A) :
      dist x y ≤ metricDiameter A := by
    unfold metricDiameter
    exact le_csSup hpairUpper ⟨x, hx, y, hy, rfl⟩
  unfold pointRadiusIn
  have hn : {r : ℝ | ∃ y ∈ A, dist x y = r}.Nonempty := by
    rcases hAn with ⟨y, hy⟩
    exact ⟨dist x y, ⟨y, hy, rfl⟩⟩
  exact csSup_le hn (by
    intro r hr
    rcases hr with ⟨y, hy, rfl⟩
    exact hdiam y hy)

/-- A common upper bound on all the distances is an upper bound on the
(real) diameter. -/
lemma kirk_diameter_le_of_forall {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {A : Set E} (hAn : A.Nonempty) (r : ℝ)
    (hall : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ r) :
    metricDiameter A ≤ r := by
  unfold metricDiameter
  have hn : {d : ℝ | ∃ x ∈ A, ∃ y ∈ A, dist x y = d}.Nonempty := by
    rcases hAn with ⟨x, hx⟩
    exact ⟨dist x x, ⟨x, hx, x, hx, rfl⟩⟩
  exact csSup_le hn (by
    intro d hd
    rcases hd with ⟨x, hx, y, hy, rfl⟩
    exact hall x hx y hy)

/-- Minimality makes a candidate equal to the closed convex hull of its
image.  Only the invariance and the elementary weak-closed = closed fact for
convex sets are involved in this step. -/
lemma kirk_minimal_eq_hull {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {K A : Set E} {T : K → K}
    (hA : KirkCandidate K T A)
    (hmin : ∀ {B : Set E}, KirkCandidate K T B → B ⊆ A → A ⊆ B) :
    A = closedConvexHull ℝ (kirkImage K T A) := by
  classical
  let H : Set E := closedConvexHull ℝ (kirkImage K T A)
  have himgsub : kirkImage K T A ⊆ A := by
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    exact hA.2.2.2.2 x hx
  have hHsubA : H ⊆ A := by
    unfold H
    exact closedConvexHull_min himgsub hA.2.2.1
      (kirk_normClosed_of_weakClosed hA.2.2.2.1)
  have hHn : H.Nonempty := by
    rcases hA.2.1 with ⟨a, ha⟩
    have haK : a ∈ K := hA.1 ha
    let x : K := ⟨a, haK⟩
    have hximg : (T x : E) ∈ kirkImage K T A :=
      ⟨x, ha, rfl⟩
    exact ⟨(T x : E), subset_closedConvexHull (𝕜 := ℝ) hximg⟩
  have hHconv : Convex ℝ H := by
    exact convex_closedConvexHull (𝕜 := ℝ) (s := kirkImage K T A)
  have hHclosed : IsClosed H := by
    exact isClosed_closedConvexHull (𝕜 := ℝ)
  have hHweak : KirkWeakClosed H :=
    kirk_isClosed_weak_image H hHclosed hHconv
  have hHinv : ∀ x : K, (x : E) ∈ H → (T x : E) ∈ H := by
    intro x hx
    have hxA : (x : E) ∈ A := hHsubA hx
    have hximg : (T x : E) ∈ kirkImage K T A :=
      ⟨x, hxA, rfl⟩
    exact subset_closedConvexHull (𝕜 := ℝ) hximg
  have hHcand : KirkCandidate K T H :=
    ⟨hHsubA.trans hA.1, hHn, hHconv, hHweak, hHinv⟩
  exact Set.Subset.antisymm (hmin hHcand hHsubA)
    (by -- this direction was the easy closed-hull inclusion
      exact hHsubA)

/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem kirk_normal_structure [CompleteSpace E]
    (hE_reflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E))
    (K : Set E) (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K)
    (hK_bounded : Bornology.IsBounded K) (hK_convex : Convex ℝ K)
    (hK_normal : HasNormalStructure K) (T : K → K)
    (hT : IsNonexpansiveSelfMap K T) :
    ∃ x : K, IsFixedPt T x :=
/-ResultProofBegin-/by
  classical
  obtain ⟨A, hA, hmin⟩ :=
    kirk_exists_minimal_candidate hE_reflexive K hK_nonempty hK_closed
      hK_bounded hK_convex T
  by_cases hnt : A.Nontrivial
  · obtain ⟨a, ha, hnd⟩ := hK_normal A hA.1 hA.2.2.1 hnt
    let r : ℝ := pointRadiusIn a A
    let A₀ : Set E := A ∩ ⋂ y : A, Metric.closedBall (y : E) r
    have hnormA : IsClosed A := kirk_normClosed_of_weakClosed hA.2.2.2.1
    have hrlt : r < metricDiameter A := by
      have hle : pointRadiusIn a A ≤ metricDiameter A :=
        kirk_radius_le_diameter hK_bounded hA.1 hA.2.1 ha
      have hne : pointRadiusIn a A ≠ metricDiameter A := by
        intro he
        exact hnd ⟨ha, he⟩
      exact lt_of_le_of_ne hle hne
    have ha0 : a ∈ A₀ := by
      refine ⟨ha, Set.mem_iInter.2 ?_⟩
      intro y
      exact Metric.mem_closedBall.2
        (kirk_dist_le_radius hK_bounded hA.1 hA.2.1 a y.property)
    have hA0sub : A₀ ⊆ A := fun x hx => hx.1
    have hA0n : A₀.Nonempty := ⟨a, ha0⟩
    have hA0closed : IsClosed A₀ := by
      exact hnormA.inter (isClosed_iInter (fun y : A => Metric.isClosed_closedBall))
    have hA0conv : Convex ℝ A₀ := by
      exact hA.2.2.1.inter
        (convex_iInter (fun y : A => convex_closedBall (y : E) r))
    have hA0weak : KirkWeakClosed A₀ :=
      kirk_isClosed_weak_image A₀ hA0closed hA0conv
    have hHull : A = closedConvexHull ℝ (kirkImage K T A) :=
      kirk_minimal_eq_hull hA hmin
    have hlip : LipschitzWith 1 T := hT
    have hA0inv : ∀ x : K, (x : E) ∈ A₀ → (T x : E) ∈ A₀ := by
      intro x hx
      have hxA : (x : E) ∈ A := hx.1
      have hball : A ⊆ Metric.closedBall (T x : E) r := by
        rw [hHull]
        apply closedConvexHull_min (𝕜 := ℝ)
          (t := Metric.closedBall (T x : E) r)
        · intro w hw
          rcases hw with ⟨z, hzA, rfl⟩
          have hxz : dist (x : E) (z : E) ≤ r := by
            have hm := Set.mem_iInter.1 hx.2 (⟨(z : E), hzA⟩ : A)
            exact Metric.mem_closedBall.1 hm
          have hle : dist (T x : E) (T z : E) ≤
                dist (x : E) (z : E) := by
            simpa [Subtype.dist_eq] using (hlip.dist_le_mul x z)
          exact Metric.mem_closedBall.2 (by
            calc
              dist (T z : E) (T x : E) = dist (T x : E) (T z : E) := dist_comm _ _
              _ ≤ dist (x : E) (z : E) := hle
              _ ≤ r := hxz)
        · exact convex_closedBall (T x : E) r
        · exact Metric.isClosed_closedBall
      refine ⟨hA.2.2.2.2 x hxA, Set.mem_iInter.2 ?_⟩
      intro y
      have hm : (y : E) ∈ Metric.closedBall (T x : E) r := hball y.property
      apply Metric.mem_closedBall.2
      have hm' : dist (y : E) (T x : E) ≤ r := Metric.mem_closedBall.1 hm
      simpa [dist_comm] using hm'
    have hA0cand : KirkCandidate K T A₀ :=
      ⟨hA0sub.trans hA.1, hA0n, hA0conv, hA0weak, hA0inv⟩
    have hinc : A ⊆ A₀ := hmin hA0cand hA0sub
    have hall : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ r := by
      intro x hx y hy
      have hx' : x ∈ A₀ := hinc hx
      have hm : x ∈ Metric.closedBall (y : E) r :=
        Set.mem_iInter.1 hx'.2 ⟨y, hy⟩
      exact Metric.mem_closedBall.1 hm
    have hdle : metricDiameter A ≤ r :=
      kirk_diameter_le_of_forall hA.2.1 r hall
    exact False.elim ((not_le_of_gt hrlt) hdle)
  · rcases hA.2.1 with ⟨a, ha⟩
    let x : K := ⟨a, hA.1 ha⟩
    refine ⟨x, ?_⟩
    -- in a non-nontrivial set all of its members coincide
    have hTx : (T x : E) ∈ A := hA.2.2.2.2 x ha
    have heq : (T x : E) = (x : E) := by
      by_contra hne
      exact hnt ⟨(T x : E), hTx, (x : E), ha, hne⟩
    exact Subtype.ext heq
/-ResultProofEnd-/
/-ResultEnd-/

end Submission
