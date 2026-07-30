import Mathlib

-- BEGIN INLINED FILE: Mathlib/Support/kakutani_fixed_point_7ac198bd0e/BrouwerReduction.lean

open Set Filter Topology
open scoped RealInnerProductSpace

namespace KakutaniSupport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def convexProj (K : Set E) (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hconv : Convex ℝ K) (x : E) : E :=
  Classical.choose (exists_norm_eq_iInf_of_complete_convex hne hcomplete hconv x)

lemma convexProj_mem (K : Set E) (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hconv : Convex ℝ K) (x : E) :
    convexProj K hne hcomplete hconv x ∈ K :=
  (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hne hcomplete hconv x)).1

lemma convexProj_spec (K : Set E) (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hconv : Convex ℝ K) (x : E) :
    ‖x - convexProj K hne hcomplete hconv x‖ = ⨅ w : K, ‖x - w‖ :=
  (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hne hcomplete hconv x)).2

lemma convexProj_variational (K : Set E) (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hconv : Convex ℝ K) (x : E) :
    ∀ z ∈ K, @inner ℝ E _ (x - convexProj K hne hcomplete hconv x) (z - convexProj K hne hcomplete hconv x) ≤ 0 := by
  apply (norm_eq_iInf_iff_real_inner_le_zero hconv
    (convexProj_mem K hne hcomplete hconv x)).1
  exact convexProj_spec K hne hcomplete hconv x

lemma convexProj_of_mem (K : Set E) (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hconv : Convex ℝ K)
    {x : E} (hx : x ∈ K) : convexProj K hne hcomplete hconv x = x := by
  -- use variational inequality with z=x
  have h := convexProj_variational K hne hcomplete hconv x x hx
  have hnorm : 0 ≤ @inner ℝ E _ (x - convexProj K hne hcomplete hconv x)
      (x - convexProj K hne hcomplete hconv x) := real_inner_self_nonneg
  have hz : @inner ℝ E _ (x - convexProj K hne hcomplete hconv x)
      (x - convexProj K hne hcomplete hconv x) = 0 := le_antisymm h hnorm
  have hv : x - convexProj K hne hcomplete hconv x = 0 := (inner_self_eq_zero.mp hz)
  exact (sub_eq_zero.mp hv).symm

-- nonexpansiveness
lemma convexProj_dist_le (K : Set E) (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hconv : Convex ℝ K) (x y : E) :
    dist (convexProj K hne hcomplete hconv x)
      (convexProj K hne hcomplete hconv y) ≤ dist x y := by
  let p := convexProj K hne hcomplete hconv x
  let q := convexProj K hne hcomplete hconv y
  have hp : p ∈ K := convexProj_mem K hne hcomplete hconv x
  have hq : q ∈ K := convexProj_mem K hne hcomplete hconv y
  have hx : @inner ℝ E _ (x-p) (q-p) ≤ 0 := convexProj_variational K hne hcomplete hconv x q hq
  have hy : @inner ℝ E _ (y-q) (p-q) ≤ 0 := convexProj_variational K hne hcomplete hconv y p hp
  -- Cauchy-Schwarz after combine
  have hineq : ‖p - q‖ ^ 2 ≤ @inner ℝ E _ (x-y) (p-q) := by
    have hdecomp : x-y = (x-p) - (y-q) + (p-q) := by abel
    have hneg : q-p = -(p-q) := by abel
    have hident : @inner ℝ E _ (x-y) (p-q) =
        @inner ℝ E _ (p-q) (p-q) -
          @inner ℝ E _ (x-p) (q-p) - @inner ℝ E _ (y-q) (p-q) := by
      rw [hdecomp, hneg]
      rw [inner_add_left, inner_sub_left, inner_neg_right]
      -- real bilinearity
      ring
    rw [real_inner_self_eq_norm_sq] at hident
    rw [hident]
    linarith
  have hcauchy : @inner ℝ E _ (x-y) (p-q) ≤ ‖x-y‖ * ‖p-q‖ := real_inner_le_norm _ _
  have hsq : ‖p-q‖ ^ 2 ≤ ‖x-y‖ * ‖p-q‖ := le_trans hineq hcauchy
  have hle : ‖p-q‖ ≤ ‖x-y‖ := by
    by_cases hz : ‖p-q‖ = 0
    · simpa [hz] using norm_nonneg (x-y)
    · have hpos : 0 < ‖p-q‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      nlinarith
  simpa [dist_eq_norm] using hle

end KakutaniSupport

namespace KakutaniSupport
open Set Metric
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma convexProj_lipschitz (K : Set E) (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hconv : Convex ℝ K) :
    LipschitzWith 1 (convexProj K hne hcomplete hconv) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simpa using (convexProj_dist_le K hne hcomplete hconv x y)

lemma convexProj_continuous (K : Set E) (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hconv : Convex ℝ K) :
    Continuous (convexProj K hne hcomplete hconv) :=
  (convexProj_lipschitz K hne hcomplete hconv).continuous

-- Reducing the continuous fixed point property for compact convex sets in a Hilbert
-- (finite dimensional) space to the same property for a closed ball.  Stating the ball
-- principle as an explicit argument keeps the only remaining topological input small.
theorem continuous_fixed_of_ball
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (ball_fixed : ∀ R : ℝ, 0 < R →
      ∀ g : (Metric.closedBall (0:E) R) → (Metric.closedBall (0:E) R),
        Continuous g → ∃ u : (Metric.closedBall (0:E) R), g u = u)
    (K : Set E) (hcompact : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty) :
    ∀ f : K → K, Continuous f → ∃ x : K, f x = x := by
  classical
  intro f hf
  have hcompl : IsComplete K := hcompact.isClosed.isComplete
  obtain ⟨r, hr⟩ := hcompact.isBounded.subset_closedBall (0:E)
  let R : ℝ := max r 1
  have hR : 0 < R := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _)
  have hKR : K ⊆ Metric.closedBall (0:E) R := by
    intro x hx
    have hh := hr hx
    have hle : r ≤ R := le_max_left _ _
    exact mem_closedBall'.2 ((mem_closedBall'.1 hh).trans hle)
  -- the nearest-point map onto K
  let p : E → E := convexProj K hne hcompl hconv
  let ps : E → K := fun x => ⟨p x, convexProj_mem K hne hcompl hconv x⟩
  have hp : Continuous p := convexProj_continuous K hne hcompl hconv
  have hps : Continuous ps := hp.subtype_mk _
  -- compose f with that retraction, and regard it as a self map of the ball
  let g : (Metric.closedBall (0:E) R) → (Metric.closedBall (0:E) R) := fun x =>
    ⟨(f (ps (x:E)) : E), hKR (f (ps (x:E))).property⟩
  have hg : Continuous g := by
    exact (hf.subtype_val.comp (hps.comp continuous_subtype_val)).subtype_mk _
  obtain ⟨u, hu⟩ := ball_fixed R hR g hg
  have huval : (f (ps (u:E)) : E) = (u:E) := congrArg Subtype.val hu
  have uK : (u:E) ∈ K := by
    rw [← huval]
    exact (f (ps (u:E))).property
  refine ⟨⟨u, uK⟩, ?_⟩
  apply Subtype.ext
  change (f (⟨(u:E), uK⟩ : K) : E) = (u:E)
  have hp_u : p (u:E) = (u:E) := convexProj_of_mem K hne hcompl hconv uK
  have heq : ps (u:E) = (⟨(u:E), uK⟩ : (K : Set E)) := by
    apply Subtype.ext
    exact hp_u
  simpa [heq] using huval

end KakutaniSupport

namespace KakutaniSupport
open Set
open scoped RealInnerProductSpace

-- useful more general retraction lemma: it is enough to prove fixed points on any
-- compact region which contains K (cube, simplex, ...).
theorem continuous_fixed_of_superset
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K S : Set E) (hKc : IsClosed K) (hKv : Convex ℝ K) (hKn : K.Nonempty)
    (hKS : K ⊆ S)
    (fixedS : ∀ g : S → S, Continuous g → ∃ u : S, g u = u) :
    ∀ f : K → K, Continuous f → ∃ x : K, f x = x := by
  classical
  intro f hf
  have hcompl : IsComplete K := hKc.isComplete
  let p : E → E := convexProj K hKn hcompl hKv
  let ps : E → K := fun x => ⟨p x, convexProj_mem K hKn hcompl hKv x⟩
  have hp : Continuous p := convexProj_continuous K hKn hcompl hKv
  have hps : Continuous ps := hp.subtype_mk _
  let g : S → S := fun x => ⟨(f (ps (x:E)) : E), hKS (f (ps (x:E))).property⟩
  have hg : Continuous g :=
    (hf.subtype_val.comp (hps.comp continuous_subtype_val)).subtype_mk _
  obtain ⟨u, hu⟩ := fixedS g hg
  have huval : (f (ps (u:E)) : E) = (u:E) := congrArg Subtype.val hu
  have uK : (u:E) ∈ K := by rw [← huval]; exact (f (ps (u:E))).property
  refine ⟨⟨u, uK⟩, ?_⟩
  apply Subtype.ext
  change (f (⟨(u:E), uK⟩ : K) : E) = (u:E)
  have hp_u : p (u:E) = (u:E) := convexProj_of_mem K hKn hcompl hKv uK
  have heq : ps (u:E) = (⟨(u:E), uK⟩ : K) := Subtype.ext hp_u
  simpa [heq] using huval

section Cube
variable {n : ℕ}

noncomputable def ecsEquiv : EuclideanSpace ℝ (Fin n) ≃L[ℝ] ((Fin n) → ℝ) :=
  EuclideanSpace.equiv (Fin n) ℝ

noncomputable def cube (n : ℕ) (R : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  (ecsEquiv (n:=n)) ⁻¹' (Set.univ.pi (fun _ : Fin n => Set.Icc (-R) R))

lemma cube_compact (R : ℝ) : IsCompact (cube n R) := by
  let e := ecsEquiv (n:=n)
  have h : IsCompact (Set.univ.pi (fun _ : Fin n => Set.Icc (-R) R)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  change IsCompact ((⇑e.toLinearEquiv) ⁻¹' (Set.univ.pi (fun _ : Fin n => Set.Icc (-R) R)))
  rw [← e.toLinearEquiv.image_symm_eq_preimage]
  exact h.image e.symm.continuous

lemma cube_convex (R : ℝ) : Convex ℝ (cube n R) := by
  let e := ecsEquiv (n:=n)
  have h : Convex ℝ (Set.univ.pi (fun _ : Fin n => Set.Icc (-R) R)) :=
    convex_pi (fun _ _ => convex_Icc _ _)
  exact h.linear_preimage e.toLinearMap

lemma compact_subset_cube {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) : ∃ R : ℝ, 0 < R ∧ K ⊆ cube n R := by
  let e := ecsEquiv (n:=n)
  have hb : Bornology.IsBounded (e '' K) := (hK.image e.continuous).isBounded
  obtain ⟨r, hr⟩ := hb.subset_closedBall (0 : (Fin n → ℝ))
  let R : ℝ := max r 1
  refine ⟨R, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro x hx
  have hxe : e x ∈ Metric.closedBall (0 : Fin n → ℝ) r := hr ⟨x, hx, rfl⟩
  have hnorm : ‖e x‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hxe
  intro i hi
  change -(R) ≤ e x i ∧ e x i ≤ R
  have habs0 : |e x i| ≤ ‖e x‖ := by
    simpa [Real.norm_eq_abs] using (norm_le_pi_norm (e x) i)
  have habs : |e x i| ≤ R := habs0.trans (hnorm.trans (le_max_left _ _))
  exact (abs_le.mp habs)

-- it therefore remains enough to establish the elementary cubical form of Brouwer.
theorem continuous_fixed_of_cube
    {n : ℕ}
    (cube_fixed : ∀ R : ℝ, 0 < R →
       ∀ f : cube n R → cube n R, Continuous f → ∃ x : cube n R, f x = x)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hKv : Convex ℝ K) (hKn : K.Nonempty) :
    ∀ f : K → K, Continuous f → ∃ x : K, f x = x := by
  obtain ⟨R, hR, hsub⟩ := compact_subset_cube hK
  exact continuous_fixed_of_superset K (cube n R) hK.isClosed hKv hKn hsub
    (cube_fixed R hR)

end Cube
end KakutaniSupport

namespace KakutaniSupport
open Set
/-- On a compact region, approximate fixed points at every scale give a fixed point.
This isolates the finite (cubical) combinatorics in the usual Brouwer proof. -/
theorem compact_fixed_of_approx
    {E : Type*} [MetricSpace E]
    {S : Set E} (hS : IsCompact S) (hne : S.Nonempty)
    {f : S → S} (hf : Continuous f)
    (ha : ∀ ε : ℝ, 0 < ε → ∃ x : S, dist (f x : E) (x:E) < ε) :
    ∃ x : S, f x = x := by
  classical
  letI : Nonempty S := hne.to_subtype
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let φ : S → ℝ := fun x => dist (f x : E) (x:E)
  have hφ : Continuous φ :=
    (continuous_subtype_val.comp hf).dist continuous_subtype_val
  obtain ⟨x, hx, hmin⟩ := (isCompact_univ : IsCompact (Set.univ : Set S)).exists_isMinOn
    (Set.univ_nonempty) hφ.continuousOn
  have hz : φ x = 0 := by
    have hn : 0 ≤ φ x := dist_nonneg
    apply le_antisymm ?_ hn
    by_contra hh
    have hp : 0 < φ x := lt_of_not_ge hh
    obtain ⟨y, hy⟩ := ha (φ x) hp
    have hle := hmin (by trivial : x ∈ (Set.univ : Set S))
    have hxy := hmin (show y ∈ (Set.univ : Set S) from trivial)
    exact (not_le_of_gt hy) hxy
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact dist_eq_zero.mp (show dist (f x : E) (x:E) = 0 from hz)

-- Combining this compact minimization with the cube reduction: the active finite-
-- dimensional input is only approximate cubical fixed points.
theorem continuous_fixed_of_cube_approx {n : ℕ}
    (cube_approx : ∀ R : ℝ, 0 < R →
       ∀ f : cube n R → cube n R, Continuous f →
         ∀ ε : ℝ, 0 < ε → ∃ x : cube n R, dist (f x : EuclideanSpace ℝ (Fin n)) (x:EuclideanSpace ℝ (Fin n)) < ε)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hKv : Convex ℝ K) (hKn : K.Nonempty) :
    ∀ f : K → K, Continuous f → ∃ x : K, f x = x := by
  apply continuous_fixed_of_cube (n:=n)
    (fun R hR f hf =>
      compact_fixed_of_approx (S:= cube n R) (cube_compact R)
        (by
          have : (0 : EuclideanSpace ℝ (Fin n)) ∈ cube n R := by
            intro i hi
            change -R ≤ (ecsEquiv (n:=n)) 0 i ∧ (ecsEquiv (n:=n)) 0 i ≤ R
            simp [map_zero, le_of_lt hR]
          exact ⟨0, this⟩)
        hf (cube_approx R hR f hf)) K hK hKv hKn

end KakutaniSupport

-- END INLINED FILE: Mathlib/Support/kakutani_fixed_point_7ac198bd0e/BrouwerReduction.lean

-- BEGIN INLINED FILE: Mathlib/Support/kakutani_fixed_point_7ac198bd0e/Limit.lean

open Set Topology Filter Metric
open scoped Topology

namespace KakutaniSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The graph of a closed-graph compact-valued correspondence, restricted to its
compact domain/range, is compact. The elementary compactness/projection argument is
a useful way of using the closed-graph version of upper hemicontinuity; no choice of
a selector is involved. -/
lemma compact_restricted_graph
    {K : Set E} (hK : IsCompact K)
    (F : E → Set E)
    (hgr : IsClosed {p : E × E | p.2 ∈ F p.1}) :
    IsCompact ({p : E × E | p.1 ∈ K ∧ p.2 ∈ K ∧ p.2 ∈ F p.1}) := by
  have hcprod : IsCompact (K ×ˢ K) := hK.prod hK
  have hsubset : {p : E × E | p.1 ∈ K ∧ p.2 ∈ K ∧ p.2 ∈ F p.1} ⊆ K ×ˢ K := by
    intro p hp
    exact ⟨hp.1, hp.2.1⟩
  have hclosed : IsClosed {p : E × E | p.1 ∈ K ∧ p.2 ∈ K ∧ p.2 ∈ F p.1} := by
    have hKc : IsClosed K := hK.isClosed
    have hp : IsClosed (K ×ˢ K) := hKc.prod hKc
    have hi : IsClosed ((K ×ˢ K) ∩ {p : E × E | p.2 ∈ F p.1}) := hp.inter hgr
    have heq : ((K ×ˢ K) ∩ {p : E × E | p.2 ∈ F p.1}) =
        {p : E × E | p.1 ∈ K ∧ p.2 ∈ K ∧ p.2 ∈ F p.1} := by
      ext p
      constructor
      · intro h
        exact ⟨h.1.1, h.1.2, h.2⟩
      · intro h
        exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
    simpa [heq] using hi -- maybe
  exact hcprod.of_isClosed_subset hclosed hsubset

/-- The compact-codomain form of the closed graph lemma.  We only claim it on
`K` (outside `K` no compactness of the values is available).  If an open set
contains `F x`, all the values `F a`, for `a∈K` near `x`, lie in it.  This is
where compactness of the *range* in the usual closed-graph formulation is
used.
-/
lemma closedGraph_upper_on_compact
    {K : Set E} (hK : IsCompact K)
    (F : E → Set E)
    (hgr : IsClosed {p : E × E | p.2 ∈ F p.1})
    (hmaps : ∀ a ∈ K, F a ⊆ K)
    {x : E} (hx : x ∈ K)
    {U : Set E} (hUopen : IsOpen U) (hxU : F x ⊆ U) :
    ∃ δ > (0:ℝ), ∀ a ∈ K, dist a x < δ → F a ⊆ U := by
  classical
  let G : Set (E × E) := {p : E × E | p.1 ∈ K ∧ p.2 ∈ K ∧ p.2 ∈ F p.1}
  have hGc : IsCompact G := by
    dsimp [G]
    exact compact_restricted_graph hK F hgr
  -- bad pairs whose second entry is outside the open tube
  let B : Set (E × E) := G ∩ (Prod.snd ⁻¹' (Uᶜ))
  have hBc : IsCompact B := by
    have hpre : IsClosed (Prod.snd ⁻¹' (Uᶜ : Set E)) :=
      hUopen.isClosed_compl.preimage
        (continuous_snd : Continuous (Prod.snd : E × E → E))
    exact hGc.inter_right hpre
  let A : Set E := Prod.fst '' B
  have hAc : IsCompact A := hBc.image
    (continuous_fst : Continuous (Prod.fst : E × E → E))
  have hAclosed : IsClosed A := hAc.isClosed
  have hxnot : x ∉ A := by
    intro hxa
    rcases hxa with ⟨p, hpB, hp1⟩
    have hpG : p ∈ G := hpB.1
    have hpnot : p.2 ∉ U := hpB.2
    have hpF : p.2 ∈ F p.1 := hpG.2.2
    have hpeqx : p.1 = x := hp1
    exact hpnot (hxU (by simpa [hpeqx] using hpF))
  have hxAc : x ∈ (Aᶜ : Set E) := hxnot
  rcases (Metric.isOpen_iff.1 hAclosed.isOpen_compl x hxAc) with
    ⟨δ, hδ, hball⟩
  refine ⟨δ, hδ, ?_⟩
  intro a haK hax y hyF
  have ha_not_bad : a ∉ A := by
    intro haA
    have haBall : a ∈ Metric.ball x δ := by
      -- the centre of the ball was `x`, whereas the hypothesis has `a` first
      exact hax
    exact (hball haBall) haA
  by_contra hyU
  have hyK : y ∈ K := hmaps a haK hyF
  have hpG : (a,y) ∈ G := by
    exact ⟨haK, hyK, hyF⟩
  have hpB : (a,y) ∈ B := ⟨hpG, hyU⟩
  exact ha_not_bad ⟨(a,y), hpB, rfl⟩

end KakutaniSupport

namespace KakutaniSupport
open Set Topology Filter Metric

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The limiting, genuinely topological part of the approximation proof of
Kakutani. Notice the shape of the approximation required here: `x` belongs to
the convex hull of *actual* graph values above base points less than `ε` from
`x`. There is no selector, closure, or upper-continuity fudge factor in this
statement. The little shrinking of the thickening in the proof is important:
being in an open neighbourhood for all sufficiently large indices is not in
itself inherited by a limit on its boundary.
-/
theorem fixed_of_approximate_convexHull
    {K : Set V} (hK : IsCompact K)
    (F : V → Set V)
    (hgr : IsClosed {p : V × V | p.2 ∈ F p.1})
    (hne : ∀ x ∈ K, (F x).Nonempty)
    (hconv : ∀ x ∈ K, Convex ℝ (F x))
    (hclosed : ∀ x ∈ K, IsClosed (F x))
    (hmaps : ∀ x ∈ K, F x ⊆ K)
    (happ : ∀ ε : ℝ, 0 < ε →
      ∃ x ∈ K, x ∈ convexHull ℝ {y : V | ∃ a ∈ K, dist a x < ε ∧ y ∈ F a}) :
    ∃ x ∈ K, x ∈ F x := by
  classical
  let e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hepos : ∀ n, 0 < e n := by
    intro n
    dsimp [e]
    positivity
  have hall : ∀ n : ℕ, ∃ x ∈ K,
      x ∈ convexHull ℝ {y : V | ∃ a ∈ K, dist a x < e n ∧ y ∈ F a} := by
    intro n
    exact happ (e n) (hepos n)
  choose z hzK hz using hall
  obtain ⟨x, hxK, φ, hφ, hzlim⟩ := hK.tendsto_subseq hzK
  refine ⟨x, hxK, ?_⟩
  by_contra hxF
  -- A ball around the alleged limiting point misses its (closed) value.
  have hopenC : IsOpen ((F x)ᶜ : Set V) := (hclosed x hxK).isOpen_compl
  have hxC : x ∈ ((F x)ᶜ : Set V) := hxF
  obtain ⟨R, hR, hballR⟩ := (Metric.isOpen_iff.1 hopenC) x hxC
  let r : ℝ := R / 2
  have hr : 0 < r := by dsimp [r]; linarith
  let U : Set V := Metric.thickening r (F x)
  have hUopen : IsOpen U := by
    dsimp [U]
    exact Metric.isOpen_thickening
  have hUconv : Convex ℝ U := by
    dsimp [U]
    exact (hconv x hxK).thickening r
  have hxsub : F x ⊆ U := by
    intro y hy
    dsimp [U]
    apply (Metric.mem_thickening_iff).2
    exact ⟨y, hy, by simpa using hr⟩
  obtain ⟨δ, hδ, hup⟩ :=
    closedGraph_upper_on_compact (E := V) hK F hgr hmaps hxK hUopen hxsub
  have hδ' : 0 < δ / 2 := by linarith
  -- Along the extracted subsequence both the base points and the prescribed
  -- radii tend to zero.
  have he_tend : Tendsto e atTop (𝓝 (0 : ℝ)) := by
    simpa [e] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have heφ_tend : Tendsto (fun n => e (φ n)) atTop (𝓝 (0 : ℝ)) :=
    he_tend.comp hφ.tendsto_atTop
  have hev_e : ∀ᶠ n : ℕ in atTop, e (φ n) < δ/2 :=
    (tendsto_order.1 heφ_tend).2 (δ/2) hδ'
  have hev_zδ : ∀ᶠ n : ℕ in atTop, dist (z (φ n)) x < δ/2 :=
    (Metric.tendsto_nhds.1 hzlim) (δ/2) hδ'
  have hev_zr : ∀ᶠ n : ℕ in atTop, dist (z (φ n)) x < r :=
    (Metric.tendsto_nhds.1 hzlim) r hr
  have hev : ∀ᶠ n : ℕ in atTop,
      e (φ n) < δ/2 ∧ dist (z (φ n)) x < δ/2 ∧ dist (z (φ n)) x < r :=
    hev_e.and (hev_zδ.and hev_zr)
  obtain ⟨n, hne_small, hnzδ, hnzr⟩ := hev.exists
  have hsmall : {y : V | ∃ a ∈ K, dist a (z (φ n)) < e (φ n) ∧ y ∈ F a}
        ⊆ U := by
    intro y hy
    rcases hy with ⟨a, haK, haNear, hay⟩
    have hax : dist a x < δ := by
      calc
        dist a x ≤ dist a (z (φ n)) + dist (z (φ n)) x := dist_triangle _ _ _
        _ < δ := by linarith
    exact hup a haK hax hay
  have hzU : z (φ n) ∈ U :=
    (convexHull_min hsmall hUconv) (hz (φ n))
  have hznotU : z (φ n) ∉ U := by
    intro hmem
    rcases (Metric.mem_thickening_iff.1 (show z (φ n) ∈ Metric.thickening r (F x) from hmem))
      with ⟨y, hyF, hzy⟩
    have hxyR : dist x y < R := by
      calc
        dist x y ≤ dist x (z (φ n)) + dist (z (φ n)) y := dist_triangle _ _ _
        _ < R := by
          have hxz : dist x (z (φ n)) < r := by simpa [dist_comm] using hnzr
          dsimp [r] at hxz hzy ⊢
          linarith
    have hyBall : y ∈ Metric.ball x R := by
      have : dist y x < R := by simpa [dist_comm] using hxyR
      exact this
    exact (hballR hyBall) hyF
  exact hznotU hzU

end KakutaniSupport

-- END INLINED FILE: Mathlib/Support/kakutani_fixed_point_7ac198bd0e/Limit.lean

-- BEGIN INLINED FILE: Mathlib/Support/kakutani_fixed_point_7ac198bd0e/Approx.lean

open Set Topology Filter Metric
open scoped BigOperators Topology
namespace KakutaniSupport

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The elementary partition-of-unity part of the usual proof. We separate the
fixed-point input on purpose. The input is a fixed-point principle for
continuous maps of the compactum *as a subtype*, so there is no extension or
projection assumption hidden here. -/
theorem approximate_convexHull_of_continuous_fixed
    {K : Set V} (hK : IsCompact K)
    (hconvK : Convex ℝ K)
    (F : V → Set V)
    (hne : ∀ x ∈ K, (F x).Nonempty)
    (hmaps : ∀ x ∈ K, F x ⊆ K)
    (hfp : ∀ f : K → K, Continuous f → ∃ x : K, f x = x) :
    ∀ ε : ℝ, 0 < ε →
      ∃ x ∈ K, x ∈ convexHull ℝ {y : V | ∃ a ∈ K, dist a x < ε ∧ y ∈ F a} := by
  classical
  intro ε hε
  -- Centres are indexed by the subtype; compactness gives a genuinely finite
  -- subcover. Keeping this index type avoids an otherwise useless choice of
  -- representatives in `K`.
  have hcover : K ⊆ ⋃ a : K, Metric.ball (a : V) ε := by
    intro x hx
    have : x ∈ Metric.ball x ε := by
      change dist x x < ε
      simpa using hε
    exact Set.mem_iUnion.2 ⟨⟨x,hx⟩, this⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun a : K => Metric.ball (a : V) ε)
    (fun a => Metric.isOpen_ball) hcover
  choose Y hY using (fun a : K => hne (a:V) a.property)
  have hYK (a : K) : Y a ∈ K := hmaps a a.property (hY a)
  let w (a : K) (x : V) : ℝ := max 0 (ε - dist x (a : V))
  have hwcont (a : K) : Continuous (w a) := by
    dsimp [w]
    fun_prop
  have hw_nonneg (a : K) (x : V) : 0 ≤ w a x := by
    dsimp [w]
    exact le_max_left _ _
  have hw_pos {a : K} {x : V} (h : dist x (a:V) < ε) : 0 < w a x := by
    dsimp [w]
    exact (lt_max_iff).2 (Or.inr (by linarith))
  have hw_zero {a : K} {x : V} (h : ¬ dist x (a:V) < ε) : w a x = 0 := by
    dsimp [w]
    have hh : ε - dist x (a:V) ≤ 0 := by linarith
    exact max_eq_left hh
  let S (x : V) : ℝ := ∑ a ∈ t, w a x
  have hScont : Continuous S := by
    dsimp [S]
    exact continuous_finset_sum t (fun i hi => hwcont i)
  have hSpos {x : V} (hx : x ∈ K) : 0 < S x := by
    have hmem : x ∈ ⋃ a ∈ t, Metric.ball (a : V) ε := ht hx
    rcases Set.mem_iUnion.1 hmem with ⟨a, hmem⟩
    rcases Set.mem_iUnion.1 hmem with ⟨hat, hball⟩
    have hat' : a ∈ t := by
      simpa using hat
    have hax : dist x (a : V) < ε := hball
    have hp : 0 < w a x := hw_pos hax
    have hle : w a x ≤ S x := by
      dsimp [S]
      exact Finset.single_le_sum (fun i hi => hw_nonneg i x) hat'
    exact lt_of_lt_of_le hp hle
  let L (a : K) (x : V) : ℝ := w a x / S x
  have hLcont : ∀ a : K, Continuous (fun q : K => L a (q:V)) := by
    intro a
    dsimp [L]
    have hw' : Continuous (fun q : K => w a (q:V)) :=
      (hwcont a).comp continuous_subtype_val
    have hS' : Continuous (fun q : K => S (q:V)) :=
      hScont.comp continuous_subtype_val
    exact hw'.div hS' (fun q => ne_of_gt (hSpos q.property))
  have hL_nonneg (a : K) {x : V} (hx : x ∈ K) : 0 ≤ L a x := by
    dsimp [L]
    exact div_nonneg (hw_nonneg _ _) (le_of_lt (hSpos hx))
  have hL_sum {x : V} (hx : x ∈ K) : (∑ a ∈ t, L a x) = 1 := by
    dsimp [L]
    rw [← Finset.sum_div]
    -- the denominator is nonzero on `K`
    exact div_self (ne_of_gt (hSpos hx))
  let gval (x : K) : V := ∑ a ∈ t, (L a (x:V)) • Y a
  have hgmem (x : K) : gval x ∈ K := by
    dsimp [gval]
    exact hconvK.sum_mem
      (fun i hi => hL_nonneg i x.property)
      (hL_sum x.property)
      (fun i hi => hYK i)
  let g : K → K := fun x => ⟨gval x, hgmem x⟩
  have hgcont : Continuous g := by
    dsimp [g]
    apply Continuous.subtype_mk
    dsimp [gval]
    exact continuous_finset_sum t (fun i hi => (hLcont i).smul continuous_const)
  obtain ⟨q, hq⟩ := hfp g hgcont
  have hqeq : (q : V) = gval q := by
    have := congrArg (fun z : K => (z : V)) hq
    -- `g q = q`; we shall use the other orientation
    simpa [g] using this.symm
  refine ⟨(q:V), q.property, ?_⟩
  -- throw away the zero coefficients. This small step prevents any use of a
  -- value `Y a` outside the appropriate local graph set.
  let u : Finset K := t.filter (fun a => dist (a:V) (q:V) < ε)
  have hzero (a : K) (ha : a ∈ t) (hau : a ∉ u) : L a (q:V) = 0 := by
    have hn : ¬ dist (a:V) (q:V) < ε := by
      intro h
      have : a ∈ u := by
        exact Finset.mem_filter.2 ⟨ha, h⟩
      exact hau this
    have hn' : ¬ dist (q:V) (a:V) < ε := by simpa [dist_comm] using hn
    dsimp [L]
    rw [hw_zero hn']
    simp
  have hsubset : u ⊆ t := Finset.filter_subset _ _
  have hLsumu : (∑ a ∈ u, L a (q:V)) = 1 := by
    calc
      (∑ a ∈ u, L a (q:V)) = ∑ a ∈ t, L a (q:V) :=
        Finset.sum_subset hsubset (by
          intro i hi hin
          exact hzero i hi hin)
      _ = 1 := hL_sum q.property
  have hgvalu : gval q = ∑ a ∈ u, (L a (q:V)) • Y a := by
    dsimp [gval]
    symm
    apply Finset.sum_subset hsubset
    intro i hi hin
    simp [hzero i hi hin]
  -- The convex hull is used only through its minimality; equivalently these
  -- are the finite barycentric coordinates themselves.
  -- Keep the base point in this set as `q`; rewriting it too would change the
  -- radius test. Rewrite only the left hand side of the final membership.
  have hsum : (∑ a ∈ u, (L a (q:V)) • Y a) ∈
      convexHull ℝ {y : V | ∃ a ∈ K, dist a (q:V) < ε ∧ y ∈ F a} := by
    apply (convex_convexHull ℝ _).sum_mem
      (fun i hi => hL_nonneg i q.property)
      hLsumu
    intro i hi
    apply subset_convexHull (𝕜 := ℝ)
    change ∃ a ∈ K, dist a (q:V) < ε ∧ Y i ∈ F a
    exact ⟨(i:V), i.property, (Finset.mem_filter.1 hi).2, hY i⟩
  have heqsum : (q:V) = ∑ a ∈ u, (L a (q:V)) • Y a :=
    hqeq.trans hgvalu
  -- `convert` compares the two elements, not the occurrence of `q` in the
  -- parameter of the set.
  convert hsum using 1

end KakutaniSupport

-- END INLINED FILE: Mathlib/Support/kakutani_fixed_point_7ac198bd0e/Approx.lean

-- BEGIN INLINED FILE: Mathlib/Support/kakutani_fixed_point_7ac198bd0e/Cubical.lean
open Set Filter Topology
open scoped RealInnerProductSpace BigOperators
namespace KakutaniSupport
/- A completely finite, unsigned form of the cubical Sperner lemma.  Notice
that no topology occurs here: `m` is the number of little boxes in each
direction and `v` and `b` are just finite tuples. Keeping this input separate
is convenient in proofs of the analytic reduction. -/
def bitVertex {n m : ℕ} (c : Fin n → Fin m) (u : Fin n → Bool) : Fin n → Fin (m+1) :=
 fun i => ⟨(c i).val + if u i then 1 else 0, by
   have h := (c i).isLt
   split <;> omega⟩

def CubicalCross (n : ℕ) : Prop :=
 ∀ m : ℕ, 0 < m →
 ∀ L : (Fin n → Fin (m+1)) → (Fin n → Bool),
   (∀ v i, (v i).val = 0 → L v i = true) →
   (∀ v i, (v i).val = m → L v i = false) →
   ∃ c : Fin n → Fin m, ∀ i : Fin n,
     ∃ u w : Fin n → Bool,
       L (bitVertex c u) i = false ∧ L (bitVertex c w) i = true

abbrev pcube (n:ℕ) (R:ℝ) : Set (Fin n → ℝ) :=
 Set.univ.pi (fun _ : Fin n => Set.Icc (-R) R)

section
variable {n : ℕ}
lemma pcube_compact (R:ℝ) : IsCompact (pcube n R) :=
 isCompact_univ_pi (fun _ => isCompact_Icc)

-- Equally spaced vertices of a grid in [-R,R].
noncomputable def gridPoint (R:ℝ) (m:ℕ) (v:Fin n → Fin (m+1)) : Fin n → ℝ :=
 fun i => -R + (2*R) * ((v i).val : ℝ) / (m:ℝ)

lemma gridPoint_mem (R:ℝ) {m:ℕ} (hm : 0 < m) (hR : 0 ≤ R)
 (v:Fin n → Fin (m+1)) : gridPoint R m v ∈ pcube n R := by
 intro i hi
 change -R ≤ -R + (2*R) * ((v i).val:ℝ) / (m:ℝ) ∧
       -R + (2*R) * ((v i).val:ℝ) / (m:ℝ) ≤ R
 have hvm : (v i).val ≤ m := by have:= (v i).isLt; omega
 have hm' : (0:ℝ) < m := by exact_mod_cast hm
 have hv0 : (0:ℝ) ≤ (v i).val := by exact_mod_cast (Nat.zero_le _)
 have hv : ((v i).val:ℝ) ≤ (m:ℝ) := by exact_mod_cast hvm
 constructor
 · have : 0 ≤ (2*R) * ((v i).val:ℝ) / (m:ℝ) :=
       div_nonneg (mul_nonneg (by linarith) hv0) (le_of_lt hm')
   linarith
 · have hfrac : ((v i).val:ℝ) / (m:ℝ) ≤ 1 := (div_le_one hm').2 hv
   have hnon : 0 ≤ ((v i).val:ℝ) / (m:ℝ) := div_nonneg hv0 (le_of_lt hm')
   rw [mul_div_assoc] -- a*(b/m)
   nlinarith

lemma gridPoint_dist_same (R:ℝ) (hR : 0 ≤ R) {m:ℕ} (hm : 0 < m)
 (c:Fin n → Fin m) (u w:Fin n → Bool) :
 dist (gridPoint R m (bitVertex c u)) (gridPoint R m (bitVertex c w)) ≤ (2*R)/(m:ℝ) := by
 have hm' : (0:ℝ) < m := by exact_mod_cast hm
 have hnon : 0 ≤ (2*R)/(m:ℝ) := div_nonneg (by linarith) (le_of_lt hm')
 rw [dist_pi_le_iff hnon]
 intro i
 have hnn : 0 ≤ R * (m:ℝ)⁻¹ * 2 := by
   convert hnon using 1 <;> ring
 -- only four cases for the two bits
 cases hu : u i <;> cases hw : w i
 <;> simp [gridPoint, bitVertex, hu, hw, Real.dist_eq]
 · -- both false
   exact hnon
 · -- 0 then 1
   have : (0:ℝ) ≤ 2*R/(m:ℝ) := hnon
   -- simp left an expression
   rw [mul_div_assoc]
   rw [abs_le]
   constructor <;> ring_nf <;> nlinarith
 · -- 1 then 0
   rw [mul_div_assoc]
   rw [abs_le]
   constructor <;> ring_nf <;> nlinarith
 · exact hnon

theorem pcube_approx_of_cross (hc : CubicalCross n)
 (R:ℝ) (hR : 0 ≤ R) (f : pcube n R → pcube n R) (hf : Continuous f)
 {ε:ℝ} (hε : 0 < ε) : ∃ x : pcube n R, dist (f x : Fin n → ℝ) (x:Fin n → ℝ) < ε := by
  classical
  by_cases hn : n = 0
  · subst n
    let z : pcube 0 R := ⟨fun i => Fin.elim0 i, by intro i; exact Fin.elim0 i⟩
    refine ⟨z, ?_⟩
    have : dist (f z : Fin 0 → ℝ) (z:Fin 0 → ℝ) = 0 := by
      have hfun (a : Fin 0 → ℝ) : a = fun i => Fin.elim0 i :=
        funext (fun i => Fin.elim0 i)
      rw [hfun (f z : Fin 0 → ℝ), hfun (z:Fin 0 → ℝ), dist_self]
    linarith
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn
    letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn'
    -- compactness supplies a single modulus for all the little edges
    let H : pcube n R → (Fin n → ℝ) := fun x i => (f x : Fin n → ℝ) i - (x:Fin n → ℝ) i
    have hH : Continuous H := by
      exact (continuous_subtype_val.comp hf).sub continuous_subtype_val
    letI : CompactSpace (pcube n R) := isCompact_iff_compactSpace.mp (pcube_compact R)
    have hU : UniformContinuous H :=
       CompactSpace.uniformContinuous_of_continuous hH
    obtain ⟨δ, hδ, hmod⟩ := (Metric.uniformContinuous_iff.mp hU) ε hε
    obtain ⟨k : ℕ, hk : 2*R/δ < k⟩ := exists_nat_gt (2*R/δ)
    let m : ℕ := k+1
    have hm : 0 < m := by dsimp [m]; omega
    have hm' : (0:ℝ) < m := by exact_mod_cast hm
    have hmesh : 2*R/(m:ℝ) < δ := by
      have hk' : 2*R/δ < (m:ℝ) := by
        have : 2*R/δ < (k:ℝ) := hk
        exact this.trans (by exact_mod_cast Nat.lt_succ_self k)
      have := hδ
      have hr0 : 0 ≤ 2*R := by linarith
      apply (div_lt_iff₀ hm').2
      -- clear denominators in hk'
      have hh := (div_lt_iff₀ hδ).1 hk'
      nlinarith
    let pt (v : Fin n → Fin (m+1)) : pcube n R :=
        ⟨gridPoint R m v, gridPoint_mem R hm hR v⟩
    -- on the two exterior faces ties are broken towards the inside.  Thus
    -- a zero component never spoils a boundary label.
    let L : (Fin n → Fin (m+1)) → (Fin n → Bool) := fun v i =>
        if (v i).val = 0 then true
        else if (v i).val = m then false
        else decide (0 < H (pt v) i)
    have Llow : ∀ v i, (v i).val = 0 → L v i = true := by
     intro v i hi
     dsimp [L]
     rw [if_pos hi]
    have Lhigh : ∀ v i, (v i).val = m → L v i = false := by
      intro v i hi
      have nz : (v i).val ≠ 0 := by omega
      dsimp [L]; rw [if_neg nz, if_pos hi]
    obtain ⟨c, hc⟩ := hc m hm L Llow Lhigh
    let b : Fin n → Bool := fun _ => false
    let x : pcube n R := pt (bitVertex c b)
    have hcoord : ∀ i, |H x i| < ε := by
      intro i
      obtain ⟨u,w,hu,hw⟩ := hc i
      have hsign (v : Fin n → Fin (m+1)) (i:Fin n) :
         (L v i = false → H (pt v) i ≤ 0) ∧
         (L v i = true → 0 ≤ H (pt v) i) := by
       constructor
       · intro he
         by_cases z0 : (v i).val = 0
         · have := Llow v i z0
           rw [this] at he
           contradiction
         · by_cases zm : (v i).val = m
           · have hmem := (f (pt v)).property i (by trivial)
             change -R ≤ (f (pt v) : Fin n → ℝ) i ∧
                        (f (pt v) : Fin n → ℝ) i ≤ R at hmem
             have xv : (gridPoint R m v) i = R := by
               simp [gridPoint, zm]
               have mm : (m:ℝ) ≠ 0 := ne_of_gt hm'
               field_simp
               ring
             change (f (pt v) : Fin n → ℝ) i - (gridPoint R m v) i ≤ 0
             linarith
           · have ee : (decide (0 < H (pt v) i)) = false := by
               dsimp [L] at he
               rw [if_neg z0, if_neg zm] at he
               exact he
             have hp : ¬ 0 < H (pt v) i := of_decide_eq_false ee
             exact le_of_not_gt hp
       · intro he
         by_cases z0 : (v i).val = 0
         · have hmem := (f (pt v)).property i (by trivial)
           change -R ≤ (f (pt v) : Fin n → ℝ) i ∧
                      (f (pt v) : Fin n → ℝ) i ≤ R at hmem
           have xv : (gridPoint R m v) i = -R := by simp [gridPoint,z0]
           change 0 ≤ (f (pt v) : Fin n → ℝ) i - (gridPoint R m v) i
           linarith
         · by_cases zm : (v i).val = m
           · have hh := Lhigh v i zm
             rw [hh] at he
             contradiction
           · have ee : (decide (0 < H (pt v) i)) = true := by
               dsimp [L] at he
               rw [if_neg z0, if_neg zm] at he
               exact he
             have hp : 0 < H (pt v) i := of_decide_eq_true ee
             exact hp.le
      have negu : H (pt (bitVertex c u)) i ≤ 0 :=
        (hsign (bitVertex c u) i).1 hu
      have posw : 0 ≤ H (pt (bitVertex c w)) i :=
        (hsign (bitVertex c w) i).2 hw
      have near (q : Fin n → Bool) :
        dist (H (pt (bitVertex c q))) (H x) < ε := by
        apply hmod
        -- distances in the subtype are inherited from the ambient pi space
        change dist (gridPoint R m (bitVertex c q))
           (gridPoint R m (bitVertex c b)) < δ
        exact (gridPoint_dist_same R hR hm c q b).trans_lt hmesh
      have nu := (dist_pi_lt_iff hε).1 (near u) i
      have nw := (dist_pi_lt_iff hε).1 (near w) i
      rw [Real.dist_eq] at nu nw
      rw [abs_lt] at nu nw
      rw [abs_lt]
      constructor <;> linarith
    refine ⟨x, ?_⟩
    rw [dist_pi_lt_iff hε]
    intro i
    rw [Real.dist_eq]
    -- the residual H is exactly this coordinate difference
    exact hcoord i
end
end KakutaniSupport

-- END INLINED FILE: Mathlib/Support/kakutani_fixed_point_7ac198bd0e/Cubical.lean

-- BEGIN INLINED FILE: Mathlib/Support/kakutani_fixed_point_7ac198bd0e/Bridge.lean
open Set Filter Topology
open scoped RealInnerProductSpace BigOperators
namespace KakutaniSupport

-- The two coordinate models used in the reduction are linearly equivalent.  We
-- only need uniform continuity of the inverse here (their norms are the l2 and
-- l-infinity norms respectively).
noncomputable def cubeToPCube {n : ℕ} (R : ℝ) : cube n R → pcube n R :=
  fun x => ⟨ecsEquiv (x: EuclideanSpace ℝ (Fin n)), x.property⟩

noncomputable def pcubeToCube {n : ℕ} (R : ℝ) : pcube n R → cube n R :=
  fun x => ⟨(ecsEquiv (n:=n)).symm (x : Fin n → ℝ), by
    change ecsEquiv ((ecsEquiv (n:=n)).symm (x : Fin n → ℝ)) ∈ pcube n R
    simpa using x.property⟩

lemma cubeToPCube_cont {n : ℕ} (R : ℝ) : Continuous (cubeToPCube (n:=n) R) := by
  exact ((ecsEquiv (n:=n)).continuous.comp continuous_subtype_val).subtype_mk _

lemma pcubeToCube_cont {n : ℕ} (R : ℝ) : Continuous (pcubeToCube (n:=n) R) := by
  exact ((ecsEquiv (n:=n)).symm.continuous.comp continuous_subtype_val).subtype_mk _

@[simp] lemma cubeToPCube_left {n : ℕ} (R : ℝ) (x : cube n R) :
    pcubeToCube R (cubeToPCube R x) = x := by
  apply Subtype.ext
  exact (ecsEquiv (n:=n)).symm_apply_apply (x:EuclideanSpace ℝ (Fin n))

@[simp] lemma cubeToPCube_right {n : ℕ} (R : ℝ) (x : pcube n R) :
    cubeToPCube R (pcubeToCube R x) = x := by
  apply Subtype.ext
  exact (ecsEquiv (n:=n)).apply_symm_apply (x:Fin n → ℝ)

/-- Transport the elementary cubical estimate from the sup-norm coordinate model
 to the `EuclideanSpace` cube.  Small coordinates imply small Euclidean norm by
 uniform continuity of the inverse linear equivalence. -/
theorem cube_approx_of_cross {n : ℕ} (hc : CubicalCross n) :
    ∀ R : ℝ, 0 < R →
     ∀ f : cube n R → cube n R, Continuous f →
       ∀ ε : ℝ, 0 < ε →
          ∃ x : cube n R, dist (f x : EuclideanSpace ℝ (Fin n))
                                (x : EuclideanSpace ℝ (Fin n)) < ε := by
  classical
  intro R hR f hf ε hε
  have huni : UniformContinuous ((ecsEquiv (n:=n)).symm :
       (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) :=
    (ecsEquiv (n:=n)).symm.toContinuousLinearMap.uniformContinuous
  obtain ⟨δ, hδ, hu⟩ := (Metric.uniformContinuous_iff.mp huni) ε hε
  let q : pcube n R → pcube n R :=
       fun v => cubeToPCube R (f (pcubeToCube R v))
  have hq : Continuous q := by
    exact (cubeToPCube_cont R).comp (hf.comp (pcubeToCube_cont R))
  obtain ⟨z, hz⟩ := pcube_approx_of_cross hc R (le_of_lt hR) q hq hδ
  refine ⟨pcubeToCube R z, ?_⟩
  have hz' : dist ((q z : pcube n R) : Fin n → ℝ) (z : Fin n → ℝ) < δ := hz
  have hsmall := hu hz'
  -- apply the modulus of the inverse equivalence to the chosen pair
  change dist ((f (pcubeToCube R z) : cube n R) : EuclideanSpace ℝ (Fin n))
        (pcubeToCube R z : EuclideanSpace ℝ (Fin n)) < ε
  simpa [q, cubeToPCube, pcubeToCube] using hsmall

end KakutaniSupport

-- END INLINED FILE: Mathlib/Support/kakutani_fixed_point_7ac198bd0e/Bridge.lean

-- BEGIN INLINED FILE: Mathlib/Support/kakutani_fixed_point_7ac198bd0e/Cross1.lean
namespace KakutaniSupport

lemma bool_has_switch (a : ℕ → Bool) {m : ℕ}
    (h0 : a 0 = true) (hm : a m = false) :
    ∃ k : ℕ, k < m ∧ a k = true ∧ a (k+1) = false := by
  induction m with
  | zero => simp [h0] at hm
  | succ m ih =>
    by_cases h : a m = true
    · refine ⟨m, Nat.lt_succ_self _, h, ?_⟩
      simpa using hm
    · have hh : a m = false := (Bool.eq_false_of_not_eq_true h)
      obtain ⟨k,hk,hk0,hk1⟩ := ih hh
      exact ⟨k, Nat.lt_trans hk (Nat.lt_succ_self _), hk0, hk1⟩

lemma cubicalCross_zero : CubicalCross 0 := by
  intro m hm L hlo hhi
  exact ⟨(fun i => Fin.elim0 i), fun i => Fin.elim0 i⟩

lemma cubicalCross_one : CubicalCross 1 := by
  classical
  intro m hm L hlo hhi
  let z : Fin 1 := 0
  have hmle : m < m+1 := Nat.lt_succ_self _
  let vnat : ∀ t : Fin (m+1), Fin 1 → Fin (m+1) := fun t _ => t
  let a : ℕ → Bool := fun k =>
      if hk : k ≤ m then L (vnat ⟨k, Nat.lt_succ_of_le hk⟩) z else false
  have a0 : a 0 = true := by
    dsimp [a]
    apply hlo
    rfl
  have am : a m = false := by
    dsimp [a]
    rw [dif_pos (le_rfl : m ≤ m)]
    apply hhi
    rfl
  obtain ⟨k,hk,ak,ak1⟩ := bool_has_switch a a0 am
  have hkm : k ≤ m := (Nat.le_of_lt hk)
  have hk1m : k+1 ≤ m := hk
  let cc : Fin 1 → Fin m := fun _ => ⟨k, hk⟩
  refine ⟨cc, ?_⟩
  intro i
  let uu : Fin 1 → Bool := fun _ => true
  let ww : Fin 1 → Bool := fun _ => false
  refine ⟨uu, ww, ?_, ?_⟩
  · have he : bitVertex cc uu = vnat ⟨k+1, Nat.lt_succ_of_le hk1m⟩ := by
      funext j
      apply Fin.ext
      simp [bitVertex, cc, uu, vnat]
    rw [he]
    -- reduce to the value of the one-dimensional sequence at k+1
    have hai : i = z := Subsingleton.elim _ _
    subst i
    dsimp [a] at ak1
    simp only [dif_pos hk1m] at ak1
    exact ak1
  · have he : bitVertex cc ww = vnat ⟨k, Nat.lt_succ_of_le hkm⟩ := by
      funext j
      apply Fin.ext
      simp [bitVertex, cc, ww, vnat]
    rw [he]
    have hai : i = z := Subsingleton.elim _ _
    subst i
    dsimp [a] at ak
    simp only [dif_pos hkm] at ak
    exact ak

end KakutaniSupport

-- END INLINED FILE: Mathlib/Support/kakutani_fixed_point_7ac198bd0e/Cross1.lean

-- BEGIN INLINED FILE: Mathlib/Support/kakutani_fixed_point_7ac198bd0e/Sperner.lean
namespace KakutaniSupport

/-- A purely finite colouring variant of the cubical step.  Colours are `none`
 and the `n` coordinate colours.  The usual cubical Sperner (or Kuhn) lemma
 has exactly these boundary rules.  Keeping the reduction to this finitely
 stated assertion separate is useful: no continuity enters it. -/
def CubeSperner (n : ℕ) : Prop :=
 ∀ m : ℕ, 0 < m →
 ∀ lab : (Fin n → Fin (m+1)) → Option (Fin n),
   (∀ v i, (v i).val = 0 → lab v ≠ some i) →
   (∀ v i, (v i).val = m → lab v ≠ none) →
   ∃ c : Fin n → Fin m,
     ∀ colour : Option (Fin n),
        ∃ u : Fin n → Bool, lab (bitVertex c u) = colour

/-- Cubical Sperner for option colours is the only combinatorial input in
 `CubicalCross`.  A vertex coloured `none` is one where every coordinate
 carries the lower sign; a vertex of colour `i` carries the upper sign in
 coordinate `i`. -/
lemma cubicalCross_of_cubeSperner {n : ℕ} (hs : CubeSperner n) :
    CubicalCross n := by
  classical
  intro m hm L hlo hhi
  let lab : (Fin n → Fin (m+1)) → Option (Fin n) := fun v =>
     if h : ∃ i : Fin n, L v i = false then some (Classical.choose h)
     else none
  have lab_some {v : Fin n → Fin (m+1)} {i : Fin n}
       (hi : lab v = some i) : L v i = false := by
    dsimp [lab] at hi
    split at hi
    next h =>
      have ei : Classical.choose h = i := Option.some.inj hi
      simpa [ei] using (Classical.choose_spec h)
    next h => simp at hi
  have lab_none {v : Fin n → Fin (m+1)} (hv : lab v = none) :
      ∀ i : Fin n, L v i = true := by
    intro i
    dsimp [lab] at hv
    split at hv
    next h => simp at hv
    next h =>
      have hn : L v i ≠ false := by
        intro hh
        apply h
        exact ⟨i, hh⟩
      cases hh : L v i
      · exact False.elim (hn hh)
      · rfl
  have hlow : ∀ v i, (v i).val = 0 → lab v ≠ some i := by
    intro v i hv hi
    have aa := lab_some hi
    have bb := hlo v i hv
    rw [bb] at aa
    contradiction
  have hhigh : ∀ v i, (v i).val = m → lab v ≠ none := by
    intro v i hv hi
    have aa := lab_none hi i
    have bb := hhi v i hv
    rw [bb] at aa
    contradiction
  obtain ⟨c,hc⟩ := hs m hm lab hlow hhigh
  refine ⟨c, ?_⟩
  intro i
  obtain ⟨u, hu⟩ := hc (some i)
  obtain ⟨w, hw⟩ := hc none
  refine ⟨u, w, ?_, ?_⟩
  · exact lab_some hu
  · exact lab_none hw i

end KakutaniSupport

namespace KakutaniSupport

/-- With just one little interval in each direction there is a single cube;
 the boundary rules already force all `n+1` colours to occur among its corners.
 This is a useful base case of the finite lemma. -/
lemma cubeSperner_oneBox {n : ℕ}
   (lab : (Fin n → Fin (1+1)) → Option (Fin n))
   (lo : ∀ v i, (v i).val = 0 → lab v ≠ some i)
   (hi : ∀ v i, (v i).val = 1 → lab v ≠ none) :
   ∃ c : Fin n → Fin 1,
     ∀ colour : Option (Fin n), ∃ u : Fin n → Bool,
        lab (bitVertex c u) = colour := by
  classical
  let c : Fin n → Fin 1 := fun _ => 0
  let z : Fin n → Bool := fun _ => false
  have vz (i : Fin n) : ((bitVertex c z i) : ℕ) = 0 := by
    simp [bitVertex, c, z]
  have hz : lab (bitVertex c z) = none := by
    cases ee : lab (bitVertex c z) with
    | none => rfl
    | some i => exact False.elim ((lo _ i (vz i)) ee)
  refine ⟨c, ?_⟩
  intro col
  cases col with
  | none => exact ⟨z, hz⟩
  | some i =>
    let w : Fin n → Bool := fun j => if j = i then true else false
    have vself : ((bitVertex c w i) : ℕ) = 1 := by
      simp [bitVertex, c, w]
    have vother {j : Fin n} (hne : j ≠ i) :
        ((bitVertex c w j) : ℕ) = 0 := by
      simp [bitVertex, c, w, hne]
    have hlab : lab (bitVertex c w) = some i := by
      cases ee : lab (bitVertex c w) with
      | none => exact False.elim ((hi _ i vself) ee)
      | some j =>
        have ji : j = i := by
          by_contra hne
          exact (lo _ j (vother hne)) ee
        simpa [ji] using ee
    exact ⟨w, hlab⟩

end KakutaniSupport

-- END INLINED FILE: Mathlib/Support/kakutani_fixed_point_7ac198bd0e/Sperner.lean

-- BEGIN INLINED FILE: Mathlib/Support/kakutani_fixed_point_7ac198bd0e/Kuhn.lean
open scoped BigOperators
namespace KakutaniSupport

/-- Vertices along one of the monotone (Kuhn) simplices of a little cube.
 `σ` is the order in which coordinates are raised. -/
def kuhnVertex {n m : ℕ} (c : Fin n → Fin m)
    (σ : Equiv.Perm (Fin n)) (k : Fin (n+1)) : Fin n → Fin (m+1) :=
  fun i => ⟨(c i).val + if (σ.symm i).val < k.val then 1 else 0, by
    have h := (c i).isLt
    split <;> omega⟩

def kuhnBits {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : Fin (n+1)) :
    Fin n → Bool := fun i => decide ((σ.symm i).val < k.val)

lemma bitVertex_kuhnBits {n m : ℕ} (c : Fin n → Fin m)
   (σ : Equiv.Perm (Fin n)) (k : Fin (n+1)) :
    bitVertex c (kuhnBits σ k) = kuhnVertex c σ k := by
  funext i
  apply Fin.ext
  by_cases h : (σ.symm i).val < k.val
  · simp [bitVertex, kuhnBits, kuhnVertex, h]
  · simp [bitVertex, kuhnBits, kuhnVertex, h]

/-- The sharpened finite Kuhn/Sperner assertion: a *monotone simplex* in
 the grid already carries all the colours.  Such a simplex of course sits in
 a little cube, which is all the analytic argument asks for.  This spelling
 gives a convenient, concrete finite target for the remaining parity lemma. -/
def KuhnSperner (n : ℕ) : Prop :=
 ∀ m : ℕ, 0 < m →
 ∀ lab : (Fin n → Fin (m+1)) → Option (Fin n),
   (∀ v i, (v i).val = 0 → lab v ≠ some i) →
   (∀ v i, (v i).val = m → lab v ≠ none) →
   ∃ (c : Fin n → Fin m) (σ : Equiv.Perm (Fin n)),
      ∀ colour : Option (Fin n),
        ∃ k : Fin (n+1), lab (kuhnVertex c σ k) = colour

lemma cubeSperner_of_kuhn {n : ℕ} (h : KuhnSperner n) : CubeSperner n := by
  classical
  intro m hm lab lo hi
  obtain ⟨c,σ,hc⟩ := h m hm lab lo hi
  refine ⟨c, ?_⟩
  intro colour
  obtain ⟨k,hk⟩ := hc colour
  exact ⟨kuhnBits σ k, by simpa [bitVertex_kuhnBits] using hk⟩

end KakutaniSupport

namespace KakutaniSupport

def lowCorner {n m : ℕ} (c : Fin n → Fin m) : Fin n → Fin (m+1) :=
  fun i => ⟨(c i).val, Nat.lt_succ_of_lt (c i).isLt⟩

def highCorner {n m : ℕ} (c : Fin n → Fin m) : Fin n → Fin (m+1) :=
  fun i => ⟨(c i).val + 1, by have h := (c i).isLt; omega⟩

@[simp] lemma kuhnVertex_first {n m : ℕ} (c : Fin n → Fin m)
   (σ : Equiv.Perm (Fin n)) :
    kuhnVertex c σ (⟨0, Nat.zero_lt_succ n⟩ : Fin (n+1)) = lowCorner c := by
  funext i
  apply Fin.ext
  simp [kuhnVertex, lowCorner]

@[simp] lemma kuhnVertex_last {n m : ℕ} (c : Fin n → Fin m)
   (σ : Equiv.Perm (Fin n)) :
    kuhnVertex c σ (Fin.last n) = highCorner c := by
  funext i
  apply Fin.ext
  have h := (σ.symm i).isLt
  simp [kuhnVertex, highCorner, Fin.last, h]

end KakutaniSupport

-- END INLINED FILE: Mathlib/Support/kakutani_fixed_point_7ac198bd0e/Kuhn.lean

-- BEGIN INLINED FILE: Mathlib/Support/kakutani_fixed_point_7ac198bd0e/KuhnFaces.lean
open KakutaniSupport
open scoped BigOperators
namespace KakutaniSupport
noncomputable section

def swp {n:ℕ} (σ:Equiv.Perm (Fin n)) (p q:Fin n) : Equiv.Perm (Fin n) :=
 (Equiv.swap p q).trans σ
@[simp] lemma swp_symm {n} (σ:Equiv.Perm (Fin n)) (p q i:Fin n) :
 (swp σ p q).symm i = Equiv.swap p q (σ.symm i) := by
 rfl
lemma swap_rank_lt {n:ℕ} (r p q : Fin n) (hpq : q.val = p.val + 1) {k:ℕ}
 (hk : k ≠ q.val) : (Equiv.swap p q r).val < k ↔ r.val < k := by
 by_cases hp : r=p
 · subst r
   simp [Equiv.swap_apply_left, hpq]
   omega
 by_cases hq : r=q
 · subst r
   simp [Equiv.swap_apply_right, hpq]
   omega
 have e : Equiv.swap p q r = r := Equiv.swap_apply_of_ne_of_ne hp hq
 simp [e]
lemma adjacent_face {n m:ℕ} (c:Fin n → Fin m) (σ:Equiv.Perm (Fin n))
  (t:Fin (n+1)) (h0: 0 < t.val) (hn: t.val < n) :
  let p : Fin n := ⟨t.val-1, by omega⟩
  let q : Fin n := ⟨t.val, by omega⟩
  ∀ k : Fin (n+1), k ≠ t →
    kuhnVertex c (swp σ p q) k = kuhnVertex c σ k := by
 dsimp
 intro k hk
 funext i
 apply Fin.ext
 simp only [kuhnVertex, swp_symm]
 have adj : (⟨t.val, hn⟩ : Fin n).val = (⟨t.val-1, by omega⟩ : Fin n).val +1 := by simp; omega
 have alt : k.val ≠ t.val := by
   intro bad
   apply hk; apply Fin.ext; exact bad
 have eqv := swap_rank_lt (σ.symm i) (⟨t.val-1, by omega⟩ : Fin n)
   (⟨t.val, hn⟩ : Fin n) adj alt
 by_cases hh : (σ.symm i).val < k.val
 · have h2 : (Equiv.swap (⟨t.val-1, by omega⟩ : Fin n) ⟨t.val, hn⟩ (σ.symm i)).val < k.val := eqv.mpr hh
   simp [hh,h2]
 · have h2 : ¬ (Equiv.swap (⟨t.val-1, by omega⟩ : Fin n) ⟨t.val, hn⟩ (σ.symm i)).val < k.val := by intro x; exact hh (eqv.mp x)
   simp [hh,h2]
end
end KakutaniSupport

-- END INLINED FILE: Mathlib/Support/kakutani_fixed_point_7ac198bd0e/KuhnFaces.lean

-- BEGIN INLINED FILE: Mathlib/Support/kakutani_fixed_point_7ac198bd0e/Parity.lean
namespace KakutaniSupport
open scoped BigOperators
open Finset
noncomputable section
variable {I C:Type*} [Fintype I] [DecidableEq I] [Fintype C] [DecidableEq C]
variable (r:C) (a:I→C)
def Fac (t:I) : Prop := ∀ c:C, c ≠ r → ∃ k:I, k ≠ t ∧ a k = c
set_option autoImplicit true
lemma helper (hcard: Fintype.card I = Fintype.card C) {t:I} (h:Fac r a t) :
  ((Finset.univ.erase t).image a) = (Finset.univ.erase r) := by
  classical
  let s : Finset C := (Finset.univ.erase t).image a
  have sub : Finset.univ.erase r ⊆ s := by
    intro c hc
    have nr : c ≠ r := (Finset.mem_erase.1 hc).1
    obtain ⟨k, nk, e⟩ := h c nr
    exact Finset.mem_image.2 ⟨k, Finset.mem_erase.2 ⟨nk, Finset.mem_univ _⟩, e⟩
  have card_t : (Finset.univ.erase t).card = Fintype.card I - 1 := by simp
  have card_r : (Finset.univ.erase r).card = Fintype.card C - 1 := by simp
  have le : s.card ≤ (Finset.univ.erase r).card := by
    calc s.card ≤ (Finset.univ.erase t).card := Finset.card_image_le
      _ = Fintype.card I -1 := card_t
      _ = Fintype.card C -1 := by rw [hcard]
      _ = _ := card_r.symm
  exact (Finset.eq_of_subset_of_card_le sub le).symm
lemma helper_nr (hcard: Fintype.card I = Fintype.card C) {t:I} (h:Fac r a t)
 {k:I} (nk:k≠t) : a k ≠ r := by
  classical
  have im := helper (r:=r) (a:=a) hcard h
  have mem : a k ∈ (Finset.univ.erase t).image a := Finset.mem_image.2 ⟨k, by simpa using nk, rfl⟩
  rw [im] at mem
  exact (Finset.mem_erase.1 mem).1
lemma helper_inj (hcard: Fintype.card I = Fintype.card C) {t:I} (h:Fac r a t)
 {k l:I} (nk:k≠t) (nl:l≠t) (eq:a k=a l) : k=l := by
  classical
  let s := Finset.univ.erase t
  have him := helper (r:=r) (a:=a) hcard h
  have cardim : (s.image a).card = s.card := by
    rw [him]
    simp [s, hcard]
  -- card_image_iff.mpr?
  have hinj : Set.InjOn a (↑s : Set I) := (Finset.card_image_iff.mp cardim) -- check
  exact hinj (by simp [s,nk]) (by simp [s,nl]) eq
open scoped BigOperators

noncomputable def Ind (p:Prop) : ZMod 2 := by classical exact if p then 1 else 0
lemma zself (x:ZMod 2) : x+x=0 := by
  calc x+x = (2:ZMod 2)*x := by ring
  _=0 := by
    have h : (2:ZMod 2)=0 := by decide
    rw [h]; simp
lemma ind_self (p:Prop) : Ind p + Ind p = 0 := by apply zself
lemma ind_false (p:Prop) (h:¬p) : Ind p = 0 := by classical simp [Ind,h]
lemma ind_true (p:Prop) (h:p) : Ind p = 1 := by classical simp [Ind,h]
set_option autoImplicit true
def Rain (a:I→C) : Prop := Function.Surjective a
lemma face_if_eq (t x:I) (eq : a x = r) :
  Fac r a t ↔ (∀ c:C, c≠r → ∃ k:I, k≠t ∧ a k = c) := Iff.rfl
-- relation lemmas
lemma rain_of_fac_label (h:Fac r a t) (e : a t = r) : Rain a := by
 intro c
 by_cases hc : c = r
 · exact ⟨t, by simpa [hc] using e⟩
 · obtain ⟨k,_,hk⟩ := h c hc
   exact ⟨k,hk⟩
lemma fac_remove_of_bij (hb : Function.Bijective a) {x:I} (ex : a x = r) : Fac r a x := by
 intro c hc
 obtain ⟨k,hk⟩ := hb.2 c
 refine ⟨k, ?_, hk⟩
 intro ke
 subst k
 exact hc (by simpa [hk] using ex) -- check
lemma sum_fac (hcard: Fintype.card I = Fintype.card C) :
 (∑ t:I, Ind (Fac r a t)) = Ind (Rain a) := by
 classical
 by_cases hr : Rain a
 · have hb : Function.Bijective a :=
     (Fintype.bijective_iff_surjective_and_card a).2 ⟨hr, hcard⟩
   obtain ⟨t0,e0⟩ := hb.2 r
   have only : ∀ t:I, Fac r a t ↔ t=t0 := by
     intro t
     constructor
     · intro ht
       by_contra ne
       have nr := helper_nr (r:=r) (a:=a) hcard ht (k:=t0) (Ne.symm ne)
       exact nr e0
     · intro e
       subst t
       exact fac_remove_of_bij (r:=r) (a:=a) hb e0
   simp only [ind_true (Rain a) hr]
   -- sum single
   calc
    (∑ t:I, Ind (Fac r a t)) = ∑ t:I, Ind (t=t0) := by
      apply Finset.sum_congr rfl; intro x hx
      rw [only]
    _ = 1 := by
      classical
      rw [Fintype.sum_eq_single t0]
      · simp [Ind]
      · intro x nx
        simp [Ind, nx]
 · have ir : Ind (Rain a) = 0 := ind_false _ hr
   rw [ir]
   by_cases ex : ∃ t:I, Fac r a t
   · obtain ⟨t,ht⟩ := ex
     have ne : a t ≠ r := by
       intro e
       exact hr (rain_of_fac_label (r:=r) (a:=a) ht e)
     obtain ⟨k,nk,ek⟩ := ht (a t) ne
     have only : ∀ x:I, Fac r a x ↔ x=t ∨ x=k := by
       intro x
       constructor
       · intro hx
         by_cases xt : x = t
         · exact Or.inl xt
         have nxr : a x ≠ r := helper_nr (r:=r) (a:=a) hcard ht xt
         obtain ⟨y, ny, ey⟩ := hx (a x) nxr
         by_cases yt : y = t
         · right
           -- uniqueness complement of t for x and k
           have exv : a x = a t := by simpa [yt] using ey.symm -- check
           exact (helper_inj (r:=r) (a:=a) hcard ht xt nk (exv.trans ek.symm))
         · have yx : y = x := helper_inj (r:=r) (a:=a) hcard ht yt xt ey
           exact False.elim (ny yx)
       · intro hx
         rcases hx with hx | hx
         · simpa [hx] using ht
         · subst x
           intro c nc
           obtain ⟨l,nl,el⟩ := ht c nc
           by_cases lk : l = k
           · subst l
             refine ⟨t, ?_, ?_⟩
             · exact Ne.symm nk
             -- a t = c via ek and el
             exact ek.symm.trans el
           · exact ⟨l, lk, el⟩
     let g : I → I := Equiv.swap t k
     have sum0 : (∑ x ∈ (Finset.univ : Finset I), Ind (Fac r a x)) = 0 := by
       apply Finset.sum_ninvolution (s:= (Finset.univ : Finset I)) (f:= fun x => Ind (Fac r a x)) g
       · intro x
         by_cases hx : Fac r a x
         · have ox := (only x).1 hx
           rcases ox with xt | xk
           · subst x
             -- g swaps to k
             have nk' : t ≠ k := Ne.symm nk
             simp [g, Ind, ht, (only k).2 (Or.inr rfl), nk, nk']; decide
           · subst x
             have nk' : t ≠ k := Ne.symm nk
             have hkface : Fac r a k := (only k).2 (Or.inr rfl)
             simp [g, Ind, ht, hkface, nk, nk']; decide
         · have z : Ind (Fac r a x) = 0 := ind_false _ hx
           have ng : ¬ Fac r a (g x) := by
             intro hgx
             have o := (only (g x)).1 hgx
             have gn : g x = t ∨ g x = k := o
             have xbad : x = k ∨ x = t := by
               rcases gn with gnt | gnk
               · left
                 -- swap inverse
                 have := congrArg g gnt
                 simpa [g, nk, Ne.symm nk] using this
               · right
                 have := congrArg g gnk
                 simpa [g, nk, Ne.symm nk] using this
             exact hx ((only x).2 (xbad.elim (fun e => Or.inr e) (fun e => Or.inl e)))
           simp [z, ind_false _ ng]
       · intro x hx
         -- nonzero terms are t or k, hence moved
         by_cases hfx : Fac r a x
         · rcases (only x).1 hfx with xt | xk
           · subst x; simp [g, nk, Ne.symm nk]
           · subst x; simp [g, nk, Ne.symm nk]
         · exact False.elim (hx (ind_false _ hfx))
       · intro x; simp
       · intro x; exact (Equiv.swap t k).apply_symm_apply x -- swap invol
     simpa using sum0
   · push_neg at ex
     simp_rw [ind_false _ (ex _)]
     simp

end
end KakutaniSupport

-- END INLINED FILE: Mathlib/Support/kakutani_fixed_point_7ac198bd0e/Parity.lean

-- BEGIN INLINED FILE: Mathlib/Support/kakutani_fixed_point_7ac198bd0e/Rainbow.lean
open scoped BigOperators
open KakutaniSupport
namespace KakutaniSupport
noncomputable section
lemma simplex_fac {n m:ℕ} (lab:(Fin n → Fin (m+1)) → Option (Fin n))
 (i:Fin n) (c:Fin n → Fin m) (σ:Equiv.Perm (Fin n)) :
 (∑ t:Fin (n+1), Ind (∀ col:Option (Fin n), col ≠ some i → ∃ k:Fin (n+1), k ≠ t ∧ lab (kuhnVertex c σ k)=col))
 = Ind (∀ col:Option (Fin n), ∃ k:Fin (n+1), lab (kuhnVertex c σ k)=col) := by
 let a : Fin (n+1) → Option (Fin n) := fun k => lab (kuhnVertex c σ k)
 have card : Fintype.card (Fin (n+1)) = Fintype.card (Option (Fin n)) := by simp
 exact (sum_fac (r:= some i) (a:=a) card)
end
end KakutaniSupport
namespace KakutaniSupport
lemma internal_fac_eq {n m:ℕ}
 (lab:(Fin n → Fin (m+1)) → Option (Fin n))
 (c:Fin n → Fin m) (σ:Equiv.Perm (Fin n)) (i:Fin n) (t:Fin (n+1))
 (h0:0<t.val) (hn:t.val<n) :
 let p:Fin n := ⟨t.val-1, by omega⟩
 let q:Fin n := ⟨t.val, by omega⟩
 (∀ col:Option (Fin n), col ≠ some i → ∃ k:Fin (n+1), k≠t ∧ lab (kuhnVertex c (swp σ p q) k)=col) ↔
 (∀ col:Option (Fin n), col ≠ some i → ∃ k:Fin (n+1), k≠t ∧ lab (kuhnVertex c σ k)=col) := by
 dsimp
 have vv := adjacent_face c σ t h0 hn
 constructor
 · intro h col nc
   obtain ⟨k,nk,hk⟩ := h col nc
   refine ⟨k,nk,?_⟩
   simpa [vv k nk] using hk
 · intro h col nc
   obtain ⟨k,nk,hk⟩ := h col nc
   refine ⟨k,nk,?_⟩
   simpa [vv k nk] using hk
end KakutaniSupport
namespace KakutaniSupport
open scoped BigOperators
lemma internal_sum_zero {n m:ℕ}
 (lab:(Fin n → Fin (m+1)) → Option (Fin n))
 (c:Fin n → Fin m) (i:Fin n) (t:Fin (n+1))
 (h0:0<t.val) (hn:t.val<n) :
 (∑ σ:Equiv.Perm (Fin n), Ind (∀ col:Option (Fin n), col ≠ some i → ∃ k:Fin (n+1), k≠t ∧ lab (kuhnVertex c σ k)=col)) = 0 := by
 classical
 let p : Fin n := ⟨t.val-1, by omega⟩
 let q : Fin n := ⟨t.val, by omega⟩
 let g : Equiv.Perm (Fin n) → Equiv.Perm (Fin n) := fun σ => swp σ p q
 apply Finset.sum_ninvolution (s:= (Finset.univ : Finset (Equiv.Perm (Fin n)))) g
 · intro σ
   have iff := internal_fac_eq lab c σ i t h0 hn
   -- equal term twice
   have eq : Ind (∀ col:Option (Fin n), col ≠ some i → ∃ k:Fin (n+1), k≠t ∧ lab (kuhnVertex c (g σ) k)=col)
      = Ind (∀ col:Option (Fin n), col ≠ some i → ∃ k:Fin (n+1), k≠t ∧ lab (kuhnVertex c σ k)=col) := by
        congr 1
        exact propext iff
   rw [eq]
   exact zself _
 · intro σ nonz hfix
   -- apply function equality at position p; swapped exchanges q
   have eq := congrArg (fun e : Equiv.Perm (Fin n) => e p) hfix
   have bad : σ q = σ p := by
     simpa [g, swp, p, q] using eq
   have pq : (p:Fin n) ≠ q := by
     intro h
     have := congrArg Fin.val h
     dsimp [p,q] at this
     omega
   exact pq ((σ.injective) bad.symm)
 · intro σ; simp
 · intro σ
   ext x
   by_cases hp : x = p
   · subst x; simp [g, swp]
   by_cases hq : x = q
   · subst x; simp [g, swp]
   have e : Equiv.swap p q x = x := Equiv.swap_apply_of_ne_of_ne hp hq
   simp [g, swp, e, hp, hq]
end KakutaniSupport
namespace KakutaniSupport
open scoped BigOperators
/-- Just summing the preceding elementary simplex identity. This is the
mod-two incidence equality before the geometrical cancellation of the two
outer faces. -/
lemma all_simplex_incidence {n m:ℕ} (i:Fin n)
 (lab:(Fin n → Fin (m+1)) → Option (Fin n)) :
 (∑ c:Fin n → Fin m, ∑ σ:Equiv.Perm (Fin n),
    Ind (∀ col:Option (Fin n), ∃ k:Fin (n+1), lab (kuhnVertex c σ k)=col)) =
 (∑ c:Fin n → Fin m, ∑ σ:Equiv.Perm (Fin n), ∑ t:Fin (n+1),
    Ind (∀ col:Option (Fin n), col ≠ some i → ∃ k:Fin (n+1), k≠t ∧ lab (kuhnVertex c σ k)=col)) := by
 classical
 apply Finset.sum_congr rfl
 intro c hc
 apply Finset.sum_congr rfl
 intro σ hs
 exact (simplex_fac lab i c σ).symm
end KakutaniSupport
namespace KakutaniSupport
private lemma zfin {n:ℕ} : (0:Fin (n+1)).val = 0 := rfl
/-- An outer first face at the very top has no `none` vertices. -/
lemma upper_face_no {n m:ℕ} (lab:(Fin n → Fin (m+1)) → Option (Fin n))
 (hi : ∀ v i, (v i).val = m → lab v ≠ none)
 (i:Fin n) (c:Fin n → Fin m) (σ:Equiv.Perm (Fin n))
 (hn: (c (σ ⟨0, by have := i.isLt; omega⟩)).val + 1 = m) :
 ¬ (∀ col:Option (Fin n), col ≠ some i →
      ∃ k:Fin (n+1), k≠(0:Fin (n+1)) ∧ lab (kuhnVertex c σ k)=col) := by
 classical
 intro h
 obtain ⟨k,nk,hk⟩ := h none (by simp)
 have kp : 0 < k.val := by
   have : k.val ≠ 0 := by
     intro e
     apply nk
     apply Fin.ext
     exact e
   omega
 let j : Fin n := ⟨0, by have := i.isLt; omega⟩
 have rank : (σ.symm (σ j)).val = 0 := by simp [j]
 have vv : ((kuhnVertex c σ k) (σ j)).val = m := by
   change (c (σ j)).val + (if (σ.symm (σ j)).val < k.val then 1 else 0) = m
   rw [rank]
   simp [kp, hn, j]
 exact (hi _ _ vv) hk
end KakutaniSupport

-- END INLINED FILE: Mathlib/Support/kakutani_fixed_point_7ac198bd0e/Rainbow.lean

-- BEGIN INLINED FILE: Mathlib/Support/kakutani_fixed_point_7ac198bd0e/Full.lean
open scoped BigOperators
open KakutaniSupport
namespace KakutaniSupport
noncomputable section

-- predicates for a full or a nearly full Kuhn simplex
def KFull {n m:ℕ} (lab:(Fin n → Fin (m+1)) → Option (Fin n))
 (c:Fin n → Fin m) (σ:Equiv.Perm (Fin n)) : Prop :=
 ∀ col:Option (Fin n), ∃ k:Fin (n+1), lab (kuhnVertex c σ k)=col

def KFac {n m:ℕ} (lab:(Fin n → Fin (m+1)) → Option (Fin n)) (i:Fin n)
 (c:Fin n → Fin m) (σ:Equiv.Perm (Fin n)) (t:Fin (n+1)) : Prop :=
 ∀ col:Option (Fin n), col ≠ some i →
   ∃ k:Fin (n+1), k ≠ t ∧ lab (kuhnVertex c σ k)=col

-- rotation moving the first direction to the last
private def rot {n:ℕ} (σ:Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
 (finRotate n).trans σ
private def unrot {n:ℕ} (σ:Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
 (finRotate n).symm.trans σ

@[simp] private lemma rot_unrot {n} (σ:Equiv.Perm (Fin n)) : rot (unrot σ) = σ := by
 apply Equiv.ext
 intro x
 change σ ((finRotate n).symm ((finRotate n) x)) = σ x
 rw [Equiv.symm_apply_apply]
@[simp] private lemma unrot_rot {n} (σ:Equiv.Perm (Fin n)) : unrot (rot σ) = σ := by
 apply Equiv.ext
 intro x
 change σ ((finRotate n) ((finRotate n).symm x)) = σ x
 rw [Equiv.apply_symm_apply]

private def up {n m:ℕ} (c:Fin n → Fin m) (j:Fin n)
 (h : (c j).val + 1 < m) : Fin n → Fin m := fun a =>
 if e : a=j then ⟨(c a).val+1, by simpa [e] using h⟩ else c a

private def dn {n m:ℕ} (c:Fin n → Fin m) (j:Fin n)
 (h : 0 < (c j).val) : Fin n → Fin m := fun a =>
 if e : a=j then ⟨(c a).val-1, by have z: (c a).val < m := (c a).isLt; omega⟩ else c a

private lemma up_dn {n m:ℕ} (c:Fin n → Fin m) (j:Fin n)
 (h : (c j).val+1 < m) :
 dn (up c j h) j (by simp [up]) = c := by
 funext a
 by_cases e:a=j
 · subst a
   simp [dn, up]
 · simp [dn, up, e]
private lemma dn_up {n m:ℕ} (c:Fin n → Fin m) (j:Fin n)
 (h : 0 < (c j).val) :
 up (dn c j h) j (by have z : (c j).val < m := (c j).isLt; simp [dn]; omega) = c := by
 funext a
 by_cases e:a=j
 · subst a
   apply Fin.ext
   simp [dn, up]; omega
 · simp [dn, up, e]

-- equality of the two enumerations of an interior cubical face
private lemma face_vertices_rot {q m:ℕ} (c:Fin (q+1) → Fin m)
 (σ:Equiv.Perm (Fin (q+1)))
 (h : (c (σ (0:Fin (q+1)))).val + 1 < m)
 (l:Fin (q+1)) :
 kuhnVertex (up c (σ 0) h) (rot σ) (l.castSucc) =
   kuhnVertex c σ l.succ := by
 funext a
 apply Fin.ext
 -- rank of a in σ
 have nz : NeZero (q+1) := ⟨by omega⟩
 classical
 by_cases e : σ.symm a = (0:Fin (q+1))
 · have ae : a = σ 0 := by
     have := congrArg σ e
     simpa using this
   subst a
   have rr : (σ.symm (σ (0:Fin (q+1)))).val = 0 := by simp
   have nr : ((rot σ).symm (σ (0:Fin (q+1)))).val = q := by
     simp [rot, finRotate_symm_apply]
   -- coordinate 0 has been raised before all listed vertices
   simp only [kuhnVertex, Fin.castSucc, Fin.succ]
   -- easier force simplification of ranks
   change
    ( (up c (σ 0) h (σ 0)).val +
       (if ((rot σ).symm (σ 0)).val < l.val then 1 else 0)) =
      ( (c (σ 0)).val +
       (if (σ.symm (σ 0)).val < l.val + 1 then 1 else 0))
   rw [nr, rr]
   have nl : ¬ q < l.val := by omega
   have pl : 0 < l.val + 1 := by omega
   simp [up, nl, pl]
 · have an : a ≠ σ 0 := by
     intro bad; subst a; simp at e
   have rv : ((rot σ).symm a) = (finRotate (q+1)).symm (σ.symm a) := rfl
   have valr : ((rot σ).symm a).val = (σ.symm a).val - 1 := by
     rw [rv]
     exact coe_finRotate_symm_of_ne_zero e
   change
    ( (up c (σ 0) h a).val +
       (if ((rot σ).symm a).val < l.val then 1 else 0)) =
      ( (c a).val +
       (if (σ.symm a).val < l.val + 1 then 1 else 0))
   have pos : 0 < (σ.symm a).val := (Fin.pos_iff_ne_zero).2 e
   have iff : ((rot σ).symm a).val < l.val ↔ (σ.symm a).val < l.val + 1 := by
     rw [valr]
     omega
   simp [up, an, iff]

lemma KFac_zero_up_last {q m:ℕ} (lab:(Fin (q+1) → Fin (m+1)) → Option (Fin (q+1)))
 (i:Fin (q+1)) (c:Fin (q+1) → Fin m) (σ:Equiv.Perm (Fin (q+1)))
 (h : (c (σ (0:Fin (q+1)))).val + 1 < m) :
 KFac lab i c σ 0 ↔
 KFac lab i (up c (σ 0) h) (rot σ) (Fin.last (q+1)) := by
 classical
 constructor
 · intro H col nc
   obtain ⟨k,nk,hk⟩ := H col nc
   have pk : 0 < k.val := by
     have : k.val ≠ 0 := by
       intro z; apply nk; apply Fin.ext; exact z
     omega
   let l : Fin (q+1) := ⟨k.val-1, by have z:=k.isLt; omega⟩
   have kl : k = l.succ := by apply Fin.ext; simp [l]; omega
   refine ⟨l.castSucc, ?_, ?_⟩
   · intro bad
     have := congrArg Fin.val bad
     simp [l] at this
     omega
   · rw [face_vertices_rot c σ h l]
     simpa [kl] using hk
 · intro H col nc
   obtain ⟨k,nk,hk⟩ := H col nc
   have pk : k.val < q+1 := by
     have ne : k.val ≠ q+1 := by
       intro z; apply nk; apply Fin.ext; simpa using z
     have := k.isLt
     omega
   let l : Fin (q+1) := ⟨k.val, pk⟩
   have kl : k = l.castSucc := by apply Fin.ext; rfl
   refine ⟨l.succ, ?_, ?_⟩
   · intro bad
     have := congrArg Fin.val bad
     simp at this
   · rw [← face_vertices_rot c σ h l]
     simpa [kl] using hk

private lemma fac0_top {q m:ℕ} (lab:(Fin (q+1) → Fin (m+1)) → Option (Fin (q+1)))
 (hi : ∀ v i, (v i).val = m → lab v ≠ none) (i:Fin (q+1))
 (c:Fin (q+1) → Fin m) (σ:Equiv.Perm (Fin (q+1)))
 (h : (c (σ (0:Fin (q+1)))).val + 1 = m) : ¬ KFac lab i c σ 0 := by
 exact upper_face_no lab hi i c σ h

private lemma faclast_wrong {q m:ℕ} (lab:(Fin (q+1) → Fin (m+1)) → Option (Fin (q+1)))
 (lo : ∀ v i, (v i).val = 0 → lab v ≠ some i) (i:Fin (q+1))
 (c:Fin (q+1) → Fin m) (σ:Equiv.Perm (Fin (q+1)))
 (h : (c (σ (Fin.last q))).val = 0) (ne : σ (Fin.last q) ≠ i) :
 ¬ KFac lab i c σ (Fin.last (q+1)) := by
 classical
 intro H
 obtain ⟨k,nk,hk⟩ := H (some (σ (Fin.last q))) (by simpa using ne)
 have pk : k.val < q+1 := by
   have t : k.val ≠ q+1 := by
     intro z; apply nk; apply Fin.ext; simpa using z
   have z := k.isLt
   omega
 have rank : (σ.symm (σ (Fin.last q))).val = q := by simp
 have vv : ((kuhnVertex c σ k) (σ (Fin.last q))).val = 0 := by
   change (c (σ (Fin.last q))).val +
      (if (σ.symm (σ (Fin.last q))).val < k.val then 1 else 0) = 0
   rw [rank, h]
   simp
   omega
 exact (lo _ _ vv) hk

@[simp] private lemma rot_last {q} (σ:Equiv.Perm (Fin (q+1))) :
 rot σ (Fin.last q) = σ 0 := by
 change σ ((finRotate (q+1)) (Fin.last q)) = σ 0
 simp
@[simp] private lemma unrot_zero {q} (σ:Equiv.Perm (Fin (q+1))) :
 unrot σ 0 = σ (Fin.last q) := by
 change σ ((finRotate (q+1)).symm 0) = σ (Fin.last q)
 have e : (finRotate (q+1)).symm (0:Fin (q+1)) = Fin.last q := by
   apply Fin.ext
   simp [finRotate_symm_apply]
 rw [e]

private abbrev OIdx (q m:ℕ) := ((Fin (q+1) → Fin m) × Equiv.Perm (Fin (q+1))) × Bool
private def frontIdx {q m:ℕ} (x:OIdx q m) : Bool := x.2

private def turn {q m:ℕ} (x:OIdx q m) : OIdx q m :=
 let c:=x.1.1; let σ:=x.1.2
 if b:x.2 = true then
   if h:(c (σ (0:Fin (q+1)))).val + 1 < m then
     ((up c (σ 0) h, rot σ), false)
   else x
 else
   if h:0 < (c (σ (Fin.last q))).val then
     ((dn c (σ (Fin.last q)) h, unrot σ), true)
   else x

private lemma turn_turn {q m:ℕ} (x:OIdx q m) : turn (turn x) = x := by
 classical
 rcases x with ⟨⟨c,σ⟩,b⟩
 cases b with
 | false =>
   by_cases h : 0 < (c (σ (Fin.last q))).val
   · have hh : ((dn c (σ (Fin.last q)) h) ((unrot σ) (0:Fin (q+1)))).val + 1 < m := by
       simp [unrot_zero, dn]
       have z := (c (σ (Fin.last q))).isLt
       omega
     have e1 : turn ((c,σ),false) = ((dn c (σ (Fin.last q)) h, unrot σ), true) := by
       simp [turn, h]
     rw [e1]
     have du : up (dn c (σ (Fin.last q)) h) (unrot σ 0) hh = c := by
       funext a
       by_cases ea : a = σ (Fin.last q)
       · subst a
         apply Fin.ext
         simp [up, dn, unrot_zero]
         omega
       · have ea' : a ≠ unrot σ (0:Fin (q+1)) := by simpa using ea
         simp [up, dn, ea, ea']
     have hl : (dn c (σ (Fin.last q)) h (σ (Fin.last q))).val + 1 < m := by
       simp [dn]
       have z := (c (σ (Fin.last q))).isLt
       omega
     simp [turn, hh, du, hl]
   · simp [turn, h]
 | true =>
   by_cases h : (c (σ (0:Fin (q+1)))).val + 1 < m
   · have hh : 0 < ((up c (σ 0) h) ((rot σ) (Fin.last q))).val := by
       simp [rot_last, up]
     have e1 : turn ((c,σ),true) = ((up c (σ 0) h, rot σ), false) := by
       simp [turn, h]
     rw [e1]
     have ud : dn (up c (σ 0) h) (rot σ (Fin.last q)) hh = c := by
       funext a
       by_cases ea : a = σ (0:Fin (q+1))
       · subst a
         apply Fin.ext
         simp [up, dn, rot_last]
       · have ea' : a ≠ rot σ (Fin.last q) := by simpa using ea
         simp [up, dn, ea, ea']
     have hl : 0 < (up c (σ 0) h (σ 0)).val := by simp [up]
     simp [turn, hh, ud, hl]
   · simp [turn, h]
private def bdry {q m:ℕ} (i:Fin (q+1)) (x:OIdx q m) : Prop :=
 x.2 = false ∧ x.1.2 (Fin.last q) = i ∧ (x.1.1 i).val = 0
private def oval {q m:ℕ} (lab:(Fin (q+1) → Fin (m+1)) → Option (Fin (q+1)))
 (i:Fin (q+1)) (x:OIdx q m) : ZMod 2 :=
 if x.2 = true then Ind (KFac lab i x.1.1 x.1.2 0)
 else Ind (KFac lab i x.1.1 x.1.2 (Fin.last (q+1)))
private def rest {q m:ℕ} (lab:(Fin (q+1) → Fin (m+1)) → Option (Fin (q+1)))
 (i:Fin (q+1)) (x:OIdx q m) : ZMod 2 := by
 classical
 exact if bdry i x then 0 else oval lab i x

private lemma rest_pair {q m:ℕ} (lab:(Fin (q+1) → Fin (m+1)) → Option (Fin (q+1)))
 (lo : ∀ v a, (v a).val = 0 → lab v ≠ some a)
 (hi : ∀ v a, (v a).val = m → lab v ≠ none)
 (i:Fin (q+1)) (x:OIdx q m) :
 rest lab i x + rest lab i (turn x) = 0 := by
 classical
 rcases x with ⟨⟨c,σ⟩,b⟩
 cases b with
 | true =>
   by_cases h : (c (σ (0:Fin (q+1)))).val + 1 < m
   · have hh : 0 < ((up c (σ 0) h) ((rot σ) (Fin.last q))).val := by simp [rot_last, up]
     have notb : ¬ bdry i (((c,σ),true) : OIdx q m) := by simp [bdry]
     have notb' : ¬ bdry i (((up c (σ 0) h,rot σ),false) : OIdx q m) := by
       intro z
       have ji := z.2.1
       have jj : i = σ 0 := by simpa using ji.symm
       have zz := z.2.2
       simp [jj, up] at zz
     have eqp := KFac_zero_up_last lab i c σ h
     have e1 : turn (((c,σ),true):OIdx q m) = ((up c (σ 0) h, rot σ),false) := by simp [turn,h]
     rw [e1]
     have eqv : oval lab i (((c,σ),true):OIdx q m) =
        oval lab i (((up c (σ 0) h,rot σ),false):OIdx q m) := by
       dsimp [oval]
       congr 1
       exact propext eqp
     simp only [rest, notb, notb', ↓reduceIte]
     rw [eqv]
     exact zself _
   · have top : (c (σ (0:Fin (q+1)))).val + 1 = m := by
       have z := (c (σ (0:Fin (q+1)))).isLt
       omega
     have nof := fac0_top lab hi i c σ top
     have zero : oval lab i (((c,σ),true):OIdx q m) = 0 := by
       simp [oval, ind_false _ nof]
     have e1 : turn (((c,σ),true):OIdx q m) = ((c,σ),true) := by simp [turn,h]
     rw [e1]
     have rr : rest lab i (((c,σ),true):OIdx q m) = 0 := by
       simp [rest, zero, oval, bdry, ind_false _ nof]
     simp [rr]
 | false =>
   by_cases h : 0 < (c (σ (Fin.last q))).val
   · have hh : ((dn c (σ (Fin.last q)) h) ((unrot σ) (0:Fin (q+1)))).val + 1 < m := by
       simp [unrot_zero, dn]
       have z := (c (σ (Fin.last q))).isLt
       omega
     have e1 : turn (((c,σ),false):OIdx q m) = ((dn c (σ (Fin.last q)) h, unrot σ),true) := by
       simp [turn,h]
     rw [e1]
     have notb : ¬ bdry i (((c,σ),false):OIdx q m) := by
       intro z
       have ji:=z.2.1
       have zz:=z.2.2
       have hp : 0 < (c i).val := by simpa [ji] using h
       exact (Nat.ne_of_gt hp) zz
     have notb' : ¬ bdry i (((dn c (σ (Fin.last q)) h, unrot σ),true):OIdx q m) := by simp [bdry]
     -- the same face read in the lower neighbour
     have eqp := KFac_zero_up_last lab i (dn c (σ (Fin.last q)) h) (unrot σ) hh
     have du : up (dn c (σ (Fin.last q)) h) (unrot σ 0) hh = c := by
       funext a
       by_cases ea : a = σ (Fin.last q)
       · subst a; apply Fin.ext; simp [up,dn,unrot_zero]; omega
       · have ea' : a ≠ unrot σ (0:Fin (q+1)) := by simpa using ea
         simp [up,dn,ea,ea']
     have eqp' : KFac lab i (dn c (σ (Fin.last q)) h) (unrot σ) 0 ↔
           KFac lab i c σ (Fin.last (q+1)) := by
       simpa [du] using eqp
     have eqv : oval lab i (((c,σ),false):OIdx q m) =
          oval lab i (((dn c (σ (Fin.last q)) h, unrot σ),true):OIdx q m) := by
       dsimp [oval]
       congr 1
       exact propext eqp'.symm
     simp only [rest, notb, notb', ↓reduceIte]
     rw [eqv]
     exact zself _
   · have zc : (c (σ (Fin.last q))).val = 0 := by omega
     have e1 : turn (((c,σ),false):OIdx q m) = ((c,σ),false) := by simp [turn,h]
     rw [e1]
     by_cases ji : σ (Fin.last q) = i
     · have bnd : bdry i (((c,σ),false):OIdx q m) := by
         refine ⟨rfl, ji, ?_⟩
         simpa [← ji] using zc
       simp [rest, bnd]
     · have nof := faclast_wrong lab lo i c σ zc ji
       have nov : oval lab i (((c,σ),false):OIdx q m) = 0 := by simp [oval, ind_false _ nof]
       have rr : rest lab i (((c,σ),false):OIdx q m) = 0 := by
         simp [rest, nov, oval, ind_false _ nof]
       simp [rr]

private lemma rest_move {q m:ℕ} (lab:(Fin (q+1) → Fin (m+1)) → Option (Fin (q+1)))
 (lo : ∀ v a, (v a).val = 0 → lab v ≠ some a)
 (hi : ∀ v a, (v a).val = m → lab v ≠ none)
 (i:Fin (q+1)) (x:OIdx q m) (ne : rest lab i x ≠ 0) : turn x ≠ x := by
 classical
 rcases x with ⟨⟨c,σ⟩,b⟩
 cases b with
 | true =>
   by_cases h : (c (σ (0:Fin (q+1)))).val + 1 < m
   · intro bad
     have eq := congrArg Prod.snd bad
     simp [turn,h] at eq
   · have top : (c (σ (0:Fin (q+1)))).val + 1 = m := by
       have z := (c (σ (0:Fin (q+1)))).isLt; omega
     have nof := fac0_top lab hi i c σ top
     exfalso
     apply ne
     simp [rest, oval, ind_false _ nof]
 | false =>
   by_cases h : 0 < (c (σ (Fin.last q))).val
   · intro bad
     have eq := congrArg Prod.snd bad
     simp [turn,h] at eq
   · have zc : (c (σ (Fin.last q))).val = 0 := by omega
     by_cases ji : σ (Fin.last q) = i
     · have bnd : bdry i (((c,σ),false):OIdx q m) := by
         refine ⟨rfl,ji,?_⟩
         simpa [← ji] using zc
       exfalso
       exact ne (by simp [rest, bnd])
     · have nof := faclast_wrong lab lo i c σ zc ji
       exfalso
       apply ne
       simp [rest, oval, ind_false _ nof]
private def bval {q m:ℕ} (lab:(Fin (q+1) → Fin (m+1)) → Option (Fin (q+1)))
 (i:Fin (q+1)) (x:OIdx q m) : ZMod 2 := by
 classical
 exact if bdry i x then oval lab i x else 0

private lemma rest_zero {q m:ℕ} (lab:(Fin (q+1) → Fin (m+1)) → Option (Fin (q+1)))
 (lo : ∀ v a, (v a).val = 0 → lab v ≠ some a)
 (hi : ∀ v a, (v a).val = m → lab v ≠ none) (i:Fin (q+1)) :
 (∑ x:OIdx q m, rest lab i x) = 0 := by
 classical
 have z : (∑ x ∈ (Finset.univ : Finset (OIdx q m)), rest lab i x) = 0 := by
   apply Finset.sum_ninvolution (s:=(Finset.univ : Finset (OIdx q m))) (g:=turn)
   · exact rest_pair lab lo hi i
   · exact fun x h => rest_move lab lo hi i x h
   · intro x; simp
   · intro x; exact turn_turn x
 simpa using z

private lemma oval_split {q m:ℕ} (lab:(Fin (q+1) → Fin (m+1)) → Option (Fin (q+1)))
 (i:Fin (q+1)) (x:OIdx q m) :
 oval lab i x = rest lab i x + bval lab i x := by
 classical
 by_cases h:bdry i x <;> simp [rest, bval, h]

private lemma outer_boundary {q m:ℕ} (lab:(Fin (q+1) → Fin (m+1)) → Option (Fin (q+1)))
 (lo : ∀ v a, (v a).val = 0 → lab v ≠ some a)
 (hi : ∀ v a, (v a).val = m → lab v ≠ none) (i:Fin (q+1)) :
 (∑ c:Fin (q+1) → Fin m, ∑ σ:Equiv.Perm (Fin (q+1)),
     (Ind (KFac lab i c σ 0) + Ind (KFac lab i c σ (Fin.last (q+1))))) =
 (∑ c:Fin (q+1) → Fin m, ∑ σ:Equiv.Perm (Fin (q+1)),
     if σ (Fin.last q) = i ∧ (c i).val = 0 then
       Ind (KFac lab i c σ (Fin.last (q+1))) else 0) := by
 classical
 have A : (∑ x:OIdx q m, oval lab i x) = ∑ x:OIdx q m, bval lab i x := by
   calc
    (∑ x:OIdx q m, oval lab i x) =
       (∑ x:OIdx q m, (rest lab i x + bval lab i x)) := by
         apply Finset.sum_congr rfl; intro x hx; rw [oval_split]
    _ = (∑ x:OIdx q m, rest lab i x) + (∑ x:OIdx q m, bval lab i x) := by
         exact Finset.sum_add_distrib
    _ = _ := by rw [rest_zero lab lo hi i]; simp
 -- split the product and the two booleans
 simpa [Fintype.sum_prod_type, oval, bval, bdry, Bool.false_eq_true]
   using A
lemma faces_outer {q m:ℕ}
 (lab:(Fin (q+1) → Fin (m+1)) → Option (Fin (q+1))) (i:Fin (q+1)) :
 (∑ c:Fin (q+1) → Fin m, ∑ σ:Equiv.Perm (Fin (q+1)),
      ∑ t:Fin ((q+1)+1), Ind (KFac lab i c σ t)) =
 (∑ c:Fin (q+1) → Fin m, ∑ σ:Equiv.Perm (Fin (q+1)),
      (Ind (KFac lab i c σ 0) + Ind (KFac lab i c σ (Fin.last (q+1))))) := by
 classical
 -- do each cube separately
 apply Finset.sum_congr rfl
 intro c hc
 let a (σ:Equiv.Perm (Fin (q+1))) (t:Fin ((q+1)+1)) : ZMod 2 :=
    Ind (KFac lab i c σ t)
 have mid (u:Fin q) :
       (∑ σ:Equiv.Perm (Fin (q+1)), a σ (Fin.castSucc u).succ) = 0 := by
   apply internal_sum_zero lab c i
   · simp
   · simp
 have split (σ:Equiv.Perm (Fin (q+1))) :
       (∑ t, a σ t) = a σ 0 + (∑ u:Fin q, a σ (Fin.castSucc u).succ)
                           + a σ (Fin.last (q+1)) := by
   rw [Fin.sum_univ_succ]
   rw [Fin.sum_univ_castSucc]
   simp [add_assoc]
 change (∑ σ, ∑ t, a σ t) = ∑ σ, (a σ 0 + a σ (Fin.last (q+1)))
 simp_rw [split]
 simp_rw [Finset.sum_add_distrib]
 have middle0 : (∑ σ:Equiv.Perm (Fin (q+1)),
       ∑ u:Fin q, a σ (Fin.castSucc u).succ) = 0 := by
   rw [Finset.sum_comm]
   simp [mid]
 rw [middle0]
 simp


-- recurrence from all full simplices to the surviving lower exterior faces
lemma full_to_boundary {q m:ℕ}
 (lab:(Fin (q+1) → Fin (m+1)) → Option (Fin (q+1)))
 (lo : ∀ v a, (v a).val = 0 → lab v ≠ some a)
 (hi : ∀ v a, (v a).val = m → lab v ≠ none)
 (i:Fin (q+1)) :
 (∑ c:Fin (q+1) → Fin m, ∑ σ:Equiv.Perm (Fin (q+1)), Ind (KFull lab c σ)) =
 (∑ c:Fin (q+1) → Fin m, ∑ σ:Equiv.Perm (Fin (q+1)),
     if σ (Fin.last q) = i ∧ (c i).val = 0 then
       Ind (KFac lab i c σ (Fin.last (q+1))) else 0) := by
 classical
 change (∑ c:Fin (q+1) → Fin m, ∑ σ:Equiv.Perm (Fin (q+1)),
    Ind (∀ col:Option (Fin (q+1)), ∃ k:Fin ((q+1)+1), lab (kuhnVertex c σ k)=col)) = _
 rw [all_simplex_incidence i lab]
 change (∑ c:Fin (q+1) → Fin m, ∑ σ:Equiv.Perm (Fin (q+1)), ∑ t, Ind (KFac lab i c σ t)) = _
 rw [faces_outer lab i]
 exact outer_boundary lab lo hi i
-- Operations on the lower face of the last coordinate.
def embV {q m:ℕ} (v:Fin q → Fin (m+1)) : Fin (q+1) → Fin (m+1) := fun j =>
 if h:j.val < q then v ⟨j.val,h⟩ else 0
def embC {q m:ℕ} [NeZero m] (c:Fin q → Fin m) : Fin (q+1) → Fin m := fun j =>
 if h:j.val < q then c ⟨j.val,h⟩ else 0
def embP {q:ℕ} (τ:Equiv.Perm (Fin q)) : Equiv.Perm (Fin (q+1)) where
 toFun j := if h:j.val < q then Fin.castSucc (τ ⟨j.val,h⟩) else Fin.last q
 invFun j := if h:j.val < q then Fin.castSucc (τ.symm ⟨j.val,h⟩) else Fin.last q
 left_inv j := by
  dsimp
  by_cases h : j.val < q
  · simp [h]
  · have hj : j = Fin.last q := by apply Fin.ext; simp; omega
    subst j; simp
 right_inv j := by
  dsimp
  by_cases h : j.val < q
  · simp [h]
  · have hj : j = Fin.last q := by apply Fin.ext; simp; omega
    subst j; simp
@[simp] lemma embP_last {q} (τ:Equiv.Perm (Fin q)) : embP τ (Fin.last q)=Fin.last q := by simp [embP]

def lowLab {q m:ℕ} (lab:(Fin (q+1) → Fin (m+1)) → Option (Fin (q+1)))
 (v:Fin q → Fin (m+1)) : Option (Fin q) :=
 match lab (embV v) with
 | none => none
 | some j => if h:j.val < q then some ⟨j.val,h⟩ else none

lemma lowLab_eq {q m:ℕ} (lab:(Fin (q+1) → Fin (m+1)) → Option (Fin (q+1)))
 (lo : ∀ v a, (v a).val = 0 → lab v ≠ some a) (v:Fin q → Fin (m+1)) :
 (lowLab lab v).map Fin.castSucc = lab (embV v) := by
 classical
 cases e:lab (embV v) with
 | none => simp [lowLab, e]
 | some j =>
   have jl : j.val < q := by
     by_contra z
     have je : j = Fin.last q := by apply Fin.ext; simp; omega
     subst j
     have zz : ((embV v) (Fin.last q)).val = 0 := by simp [embV]
     exact (lo _ _ zz) e
   simp [lowLab, e, jl]

lemma lower_rules {q m:ℕ} (lab:(Fin (q+1) → Fin (m+1)) → Option (Fin (q+1)))
 (lo : ∀ v a, (v a).val = 0 → lab v ≠ some a)
 (hi : ∀ v a, (v a).val = m → lab v ≠ none) :
 (∀ v a, (v a).val = 0 → lowLab lab v ≠ some a) ∧
 (∀ v a, (v a).val = m → lowLab lab v ≠ none) := by
 classical
 constructor
 · intro v a z bad
   have eq := congrArg (Option.map Fin.castSucc) bad
   rw [lowLab_eq lab lo v] at eq
   simp at eq
   have zz : ((embV v) a.castSucc).val = 0 := by simpa [embV] using z
   exact (lo _ _ zz) eq
 · intro v a z bad
   have eq := congrArg (Option.map Fin.castSucc) bad
   rw [lowLab_eq lab lo v] at eq
   simp at eq
   have zz : ((embV v) a.castSucc).val = m := by simpa [embV] using z
   exact (hi _ _ zz) eq

private lemma lower_vertices {q m:ℕ} [NeZero m]
 (c:Fin q → Fin m) (τ:Equiv.Perm (Fin q)) (k:Fin (q+1)) :
 kuhnVertex (embC c) (embP τ) k.castSucc =
      embV (kuhnVertex c τ k) := by
 funext a
 apply Fin.ext
 classical
 by_cases h:a.val < q
 · let b : Fin q := ⟨a.val,h⟩
   change (embC c a).val +
       (if ((embP τ).symm a).val < k.val then 1 else 0) =
     (embV (kuhnVertex c τ k) a).val
   have sy : (embP τ).symm a = (τ.symm ⟨a.val,h⟩).castSucc := by
     change (if hh:a.val < q then Fin.castSucc (τ.symm ⟨a.val,hh⟩) else Fin.last q) = _
     simp [h]
   rw [sy]
   simp [embC, embV, h, kuhnVertex]
 · have ae : a = Fin.last q := by apply Fin.ext; simp; omega
   subst a
   change (embC c (Fin.last q)).val +
       (if ((embP τ).symm (Fin.last q)).val < k.val then 1 else 0) =
     (embV (kuhnVertex c τ k) (Fin.last q)).val
   have sy : (embP τ).symm (Fin.last q) = Fin.last q := by
     change (if hh:q<q then _ else _) = _
     simp
   rw [sy]
   have kk : ¬ q < k.val := by omega
   simp [embC, embV, kk]

lemma lower_face_equiv {q m:ℕ} [NeZero m]
 (lab:(Fin (q+1) → Fin (m+1)) → Option (Fin (q+1)))
 (lo : ∀ v a, (v a).val = 0 → lab v ≠ some a)
 (c:Fin q → Fin m) (τ:Equiv.Perm (Fin q)) :
 KFac lab (Fin.last q) (embC c) (embP τ) (Fin.last (q+1)) ↔
 KFull (lowLab lab) c τ := by
 classical
 constructor
 · intro H col
   have ne : (col.map Fin.castSucc) ≠ some (Fin.last q) := by
     cases col <;> simp
   obtain ⟨k,nk,hk⟩ := H (col.map Fin.castSucc) ne
   have kl : k.val < q+1 := by
     have z : k.val ≠ q+1 := by intro e; apply nk; apply Fin.ext; simpa using e
     omega
   let l : Fin (q+1) := ⟨k.val, kl⟩
   have ke : k = l.castSucc := by apply Fin.ext; rfl
   refine ⟨l, ?_⟩
   apply (Option.map_injective (f:=Fin.castSucc) (by intro a b h; exact Fin.castSucc_injective _ h))
   rw [lowLab_eq lab lo]
   rw [← lower_vertices c τ l, ← ke]
   exact hk
 · intro H col nc
   -- every colour different from last is a mapped lower colour
   have ex : ∃ cc:Option (Fin q), cc.map Fin.castSucc = col := by
     cases col with
     | none => exact ⟨none,rfl⟩
     | some j =>
       have jl : j.val < q := by
         by_contra z
         have je : j = Fin.last q := by apply Fin.ext; simp; omega
         exact nc (by simpa [je])
       exact ⟨some ⟨j.val,jl⟩, by simp⟩
   obtain ⟨cc,rfl⟩ := ex
   obtain ⟨k,hk⟩ := H cc
   refine ⟨k.castSucc, ?_, ?_⟩
   · intro e; have ee:=congrArg Fin.val e; simp at ee; have zz:=k.isLt; omega
   · rw [lower_vertices c τ k]
     rw [← lowLab_eq lab lo]
     simpa [hk]
end
end KakutaniSupport
namespace KakutaniSupport
open scoped BigOperators
noncomputable section
lemma cube_of_full_nonzero {n m:ℕ} (lab:(Fin n → Fin (m+1)) → Option (Fin n))
 (h : (∑ c:Fin n → Fin m, ∑ σ:Equiv.Perm (Fin n), Ind (KFull lab c σ)) ≠ 0) :
 ∃ c:Fin n → Fin m, ∀ col:Option (Fin n), ∃ u:Fin n → Bool,
    lab (bitVertex c u)=col := by
 classical
 by_contra z
 push_neg at z
 have zz : ∀ c:Fin n → Fin m, ∀ σ:Equiv.Perm (Fin n), ¬ KFull lab c σ := by
   intro c σ H
   obtain ⟨col,hc⟩ := z c
   obtain ⟨k,hk⟩ := H col
   exact hc (kuhnBits σ k) (by simpa [bitVertex_kuhnBits] using hk)
 apply h
 simp [ind_false _ (zz _ _)]
end
end KakutaniSupport

-- END INLINED FILE: Mathlib/Support/kakutani_fixed_point_7ac198bd0e/Full.lean

-- BEGIN INLINED FILE: Mathlib/Support/kakutani_fixed_point_7ac198bd0e/Exterior.lean
open scoped BigOperators
namespace KakutaniSupport
noncomputable section

/-- Restrict a permutation of `q+1` coordinates that fixes the last coordinate to
 the first `q` coordinates. -/
def dropP {q : ℕ} (σ : Equiv.Perm (Fin (q+1)))
    (hσ : σ (Fin.last q) = Fin.last q) : Equiv.Perm (Fin q) where
  toFun j :=
    ⟨(σ j.castSucc).val, by
      have lt := (σ j.castSucc).isLt
      have ne : σ j.castSucc ≠ Fin.last q := by
        intro e
        have e' : σ j.castSucc = σ (Fin.last q) := by simpa [hσ] using e
        have z : j.castSucc = (Fin.last q) := σ.injective e'
        have zv := congrArg Fin.val z
        simp at zv
        have jj := j.isLt
        omega
      have neq : (σ j.castSucc).val ≠ q := by
        intro e
        apply ne
        apply Fin.ext
        simpa using e
      omega⟩
  invFun j :=
    ⟨(σ.symm j.castSucc).val, by
      have lt := (σ.symm j.castSucc).isLt
      have fix' : σ.symm (Fin.last q) = Fin.last q := by
        apply σ.injective
        simp [hσ]
      have ne : σ.symm j.castSucc ≠ Fin.last q := by
        intro e
        have e' : σ.symm j.castSucc = σ.symm (Fin.last q) := by simpa [fix'] using e
        have z : j.castSucc = (Fin.last q) := σ.symm.injective e'
        have zv := congrArg Fin.val z
        simp at zv
        have jj := j.isLt
        omega
      have neq : (σ.symm j.castSucc).val ≠ q := by
        intro e
        apply ne
        apply Fin.ext
        simpa using e
      omega⟩
  left_inv j := by
    apply Fin.ext
    -- casting the restricted image back is the same original image
    have hcast : (⟨(σ j.castSucc).val, by
      have lt := (σ j.castSucc).isLt
      have ne : σ j.castSucc ≠ Fin.last q := by
        intro e
        have e' : σ j.castSucc = σ (Fin.last q) := by simpa [hσ] using e
        have z : j.castSucc = (Fin.last q) := σ.injective e'
        have zv := congrArg Fin.val z
        simp at zv
        have jj := j.isLt; omega
      have neq : (σ j.castSucc).val ≠ q := by
        intro e; apply ne; apply Fin.ext; simpa using e
      omega⟩ : Fin q).castSucc = σ j.castSucc := by
        apply Fin.ext; rfl
    -- now the inverse value
    change (σ.symm
      ( (⟨(σ j.castSucc).val, by
          have lt := (σ j.castSucc).isLt
          have ne : σ j.castSucc ≠ Fin.last q := by
            intro e
            have e' : σ j.castSucc = σ (Fin.last q) := by simpa [hσ] using e
            have z : j.castSucc = (Fin.last q) := σ.injective e'
            have zv := congrArg Fin.val z
            simp at zv
            have jj := j.isLt; omega
          have neq : (σ j.castSucc).val ≠ q := by
            intro e; apply ne; apply Fin.ext; simpa using e
          omega⟩ : Fin q).castSucc)).val = j.val
    rw [hcast]
    simp
  right_inv j := by
    apply Fin.ext
    have fix' : σ.symm (Fin.last q) = Fin.last q := by
      apply σ.injective
      simp [hσ]
    have hcast : (⟨(σ.symm j.castSucc).val, by
      have lt := (σ.symm j.castSucc).isLt
      have ne : σ.symm j.castSucc ≠ Fin.last q := by
        intro e
        have e' : σ.symm j.castSucc = σ.symm (Fin.last q) := by simpa [fix'] using e
        have z : j.castSucc = (Fin.last q) := σ.symm.injective e'
        have zv := congrArg Fin.val z
        simp at zv
        have jj:=j.isLt; omega
      have neq : (σ.symm j.castSucc).val ≠ q := by
        intro e; apply ne; apply Fin.ext; simpa using e
      omega⟩ : Fin q).castSucc = σ.symm j.castSucc := by
        apply Fin.ext; rfl
    change (σ
      ((⟨(σ.symm j.castSucc).val, by
          have lt := (σ.symm j.castSucc).isLt
          have ne : σ.symm j.castSucc ≠ Fin.last q := by
            intro e
            have e' : σ.symm j.castSucc = σ.symm (Fin.last q) := by simpa [fix'] using e
            have z : j.castSucc = (Fin.last q) := σ.symm.injective e'
            have zv := congrArg Fin.val z
            simp at zv
            have jj:=j.isLt; omega
          have neq : (σ.symm j.castSucc).val ≠ q := by
            intro e; apply ne; apply Fin.ext; simpa using e
          omega⟩ : Fin q).castSucc)).val = j.val
    rw [hcast]
    simp

lemma embP_cast {q : ℕ} (τ : Equiv.Perm (Fin q)) (j : Fin q) :
    embP τ j.castSucc = (τ j).castSucc := by
  -- both are the first branch of `embP`
  change (if h : (j.castSucc : Fin (q+1)).val < q
            then Fin.castSucc (τ ⟨(j.castSucc : Fin (q+1)).val, h⟩)
            else Fin.last q) = _
  have h : (j.castSucc : Fin (q+1)).val < q := by simpa using j.isLt
  simp [h]

lemma dropP_embP {q : ℕ} (τ : Equiv.Perm (Fin q)) :
    dropP (embP τ) (embP_last τ) = τ := by
  apply Equiv.ext
  intro j
  apply Fin.ext
  change ((embP τ) j.castSucc).val = (τ j).val
  rw [embP_cast]
  rfl

lemma embP_dropP {q : ℕ} (σ : Equiv.Perm (Fin (q+1)))
    (hσ : σ (Fin.last q) = Fin.last q) :
    embP (dropP σ hσ) = σ := by
  apply Equiv.ext
  intro j
  by_cases h : j.val < q
  · let a : Fin q := ⟨j.val,h⟩
    have ja : j = a.castSucc := by apply Fin.ext; rfl
    -- use first branch
    calc
      embP (dropP σ hσ) j = (dropP σ hσ a).castSucc := by
        rw [ja]
        exact embP_cast (dropP σ hσ) a
      _ = σ j := by
        apply Fin.ext
        change (σ a.castSucc).val = (σ j).val
        rw [ja]
  · have jlast : j = Fin.last q := by
      apply Fin.ext
      simp
      have lt := j.isLt
      omega
    rw [jlast, embP_last, hσ]

/-- Functions on the lower face correspond to functions in one lower dimension. -/
def cLowerEquiv {q m : ℕ} [NeZero m] :
    (Fin q → Fin m) ≃ {c : Fin (q+1) → Fin m // (c (Fin.last q)).val = 0} where
  toFun c := ⟨embC c, by simp [embC]⟩
  invFun C := fun j => C.1 j.castSucc
  left_inv c := by
    funext j
    change (if h : (j.castSucc : Fin (q+1)).val < q
             then c ⟨(j.castSucc : Fin (q+1)).val,h⟩ else 0) = c j
    have h : (j.castSucc : Fin (q+1)).val < q := by simpa using j.isLt
    simp [h]
  right_inv C := by
    apply Subtype.ext
    funext j
    by_cases h : j.val < q
    · change (if hh : j.val < q
           then C.1 (⟨j.val, hh⟩ : Fin q).castSucc else 0) = C.1 j
      simp [h]
    · have jl : j = Fin.last q := by
        apply Fin.ext
        simp
        have lt := j.isLt
        omega
      subst j
      have hz := C.2
      -- Fin numbers are determined by value
      apply Fin.ext
      -- value of the zero branch
      simpa [embC] using hz.symm

/-- The product of a lower cube and a lower permutation enumerates, without
 repetition, the surviving boundary indices. -/
def lowerPairEquiv {q m : ℕ} [NeZero m] :
   ((Fin q → Fin m) × Equiv.Perm (Fin q)) ≃
    {x : (Fin (q+1) → Fin m) × Equiv.Perm (Fin (q+1)) //
       x.2 (Fin.last q) = Fin.last q ∧ (x.1 (Fin.last q)).val = 0} where
  toFun x := ⟨(embC x.1, embP x.2), by simp [embC]⟩
  invFun x :=
    ((cLowerEquiv.symm ⟨x.1.1, x.2.2⟩),
      dropP x.1.2 x.2.1)
  left_inv x := by
    rcases x with ⟨c,τ⟩
    dsimp
    -- equality of two components
    apply Prod.ext
    · change cLowerEquiv.symm (cLowerEquiv c) = c
      exact Equiv.symm_apply_apply _ c
    · exact dropP_embP τ
  right_inv x := by
    rcases x with ⟨⟨C,S⟩,h⟩
    dsimp
    apply Subtype.ext
    apply Prod.ext
    · 
      have ee := Equiv.apply_symm_apply (cLowerEquiv (q:=q) (m:=m)) ⟨C, h.2⟩
      exact congrArg Subtype.val ee
    · exact embP_dropP S h.1

end
end KakutaniSupport

namespace KakutaniSupport
open scoped BigOperators
noncomputable section

lemma sum_ite_subtype {α M : Type*} [Fintype α] [AddCommMonoid M]
    (p : α → Prop) [DecidablePred p] (f : α → M) :
    (∑ x : α, if p x then f x else 0) =
      ∑ x : {x // p x}, f x.1 := by
  classical
  -- filters and subtype have the same enumeration
  have h := Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset α)) f (p:=p)
  -- h : ∑ (x ∈ Finset.subtype p univ), ... = ...
  -- the subtype `univ` is its full fintype
  -- turn the left hand side into a filtered sum
  rw [← Finset.sum_filter]
  -- should be reverse of h with simp
  simpa using h.symm

/-- The remaining boundary sum after cancellation is exactly the full-simplex
 sum in one smaller dimension. -/
lemma boundary_as_lower {q m : ℕ} [NeZero m]
    (lab : (Fin (q+1) → Fin (m+1)) → Option (Fin (q+1)))
    (lo : ∀ v a, (v a).val = 0 → lab v ≠ some a) :
 (∑ c : Fin (q+1) → Fin m, ∑ σ : Equiv.Perm (Fin (q+1)),
       if σ (Fin.last q) = Fin.last q ∧ (c (Fin.last q)).val = 0 then
         Ind (KFac lab (Fin.last q) c σ (Fin.last (q+1))) else 0) =
 (∑ c : Fin q → Fin m, ∑ τ : Equiv.Perm (Fin q),
       Ind (KFull (lowLab lab) c τ)) := by
  classical
  let B := (Fin (q+1) → Fin m) × Equiv.Perm (Fin (q+1))
  let S := (Fin q → Fin m) × Equiv.Perm (Fin q)
  let p : ((Fin (q+1) → Fin m) × Equiv.Perm (Fin (q+1))) → Prop :=
     fun x => x.2 (Fin.last q) = Fin.last q ∧ (x.1 (Fin.last q)).val = 0
  let f : ((Fin (q+1) → Fin m) × Equiv.Perm (Fin (q+1))) → ZMod 2 :=
     fun x => Ind (KFac lab (Fin.last q) x.1 x.2 (Fin.last (q+1)))
  have hsub :
     (∑ x : ((Fin (q+1) → Fin m) × Equiv.Perm (Fin (q+1))),
          if p x then f x else 0)
       = ∑ x : {x : ((Fin (q+1) → Fin m) × Equiv.Perm (Fin (q+1))) // p x}, f x.1 := by
        exact sum_ite_subtype p f
  calc
    (∑ c : Fin (q+1) → Fin m, ∑ σ : Equiv.Perm (Fin (q+1)),
       if σ (Fin.last q) = Fin.last q ∧ (c (Fin.last q)).val = 0 then
         Ind (KFac lab (Fin.last q) c σ (Fin.last (q+1))) else 0) =
      (∑ x : ((Fin (q+1) → Fin m) × Equiv.Perm (Fin (q+1))),
          if p x then f x else 0) := by
        rw [Fintype.sum_prod_type]
    _ = (∑ x : {x : ((Fin (q+1) → Fin m) × Equiv.Perm (Fin (q+1))) // p x}, f x.1) := hsub
    _ = (∑ y : ((Fin q → Fin m) × Equiv.Perm (Fin q)),
             f ( (lowerPairEquiv (q:=q) (m:=m)) y).1) := by
        -- change the indexing set using the explicit boundary equivalence
        symm
        apply Fintype.sum_equiv (lowerPairEquiv (q:=q) (m:=m))
        intro y
        rfl
    _ = (∑ c : Fin q → Fin m, ∑ τ : Equiv.Perm (Fin q),
            Ind (KFull (lowLab lab) c τ)) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro c hc
        apply Finset.sum_congr rfl
        intro τ hτ
        change Ind (KFac lab (Fin.last q) (embC c) (embP τ)
                       (Fin.last (q+1))) = Ind (KFull (lowLab lab) c τ)
        exact congrArg Ind (propext (lower_face_equiv lab lo c τ))

end
end KakutaniSupport

namespace KakutaniSupport
open scoped BigOperators
noncomputable section

lemma fullsum_zero (m : ℕ)
    (lab : (Fin 0 → Fin (m+1)) → Option (Fin 0)) :
    (∑ c : Fin 0 → Fin m, ∑ σ : Equiv.Perm (Fin 0),
        Ind (KFull lab c σ)) = 1 := by
  classical
  have hfull : ∀ (c : Fin 0 → Fin m) (σ : Equiv.Perm (Fin 0)),
       KFull lab c σ := by
    intro c σ col
    have cn : col = none := by
      cases col with
      | none => rfl
      | some i => exact Fin.elim0 i
    subst col
    let k : Fin (0+1) := 0
    refine ⟨k, ?_⟩
    cases h : lab (kuhnVertex c σ k) with
    | none => rfl
    | some i => exact Fin.elim0 i
  simp_rw [ind_true _ (hfull _ _)]
  -- all three fintypes here are singletons
  simp

end
end KakutaniSupport

namespace KakutaniSupport
open scoped BigOperators
noncomputable section

/-- The parity count of full Kuhn simplices is always odd (in fact it is one).
This is the exterior-face induction. -/
lemma fullsum_one : ∀ (n m : ℕ), 0 < m →
    ∀ lab : (Fin n → Fin (m+1)) → Option (Fin n),
      (∀ v a, (v a).val = 0 → lab v ≠ some a) →
      (∀ v a, (v a).val = m → lab v ≠ none) →
      (∑ c : Fin n → Fin m, ∑ σ : Equiv.Perm (Fin n),
         Ind (KFull lab c σ)) = 1 := by
  intro n
  induction n with
  | zero =>
      intro m hm lab lo hi
      exact fullsum_zero m lab
  | succ q ih =>
      intro m hm lab lo hi
      letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
      have rules := lower_rules lab lo hi
      -- cancel all interior and upper faces, then identify the remaining face
      calc
        (∑ c : Fin (q+1) → Fin m, ∑ σ : Equiv.Perm (Fin (q+1)),
            Ind (KFull lab c σ)) =
          (∑ c : Fin (q+1) → Fin m, ∑ σ : Equiv.Perm (Fin (q+1)),
            if σ (Fin.last q) = (Fin.last q) ∧ (c (Fin.last q)).val = 0 then
              Ind (KFac lab (Fin.last q) c σ (Fin.last (q+1))) else 0) :=
                full_to_boundary lab lo hi (Fin.last q)
        _ = (∑ c : Fin q → Fin m, ∑ τ : Equiv.Perm (Fin q),
                Ind (KFull (lowLab lab) c τ)) :=
                boundary_as_lower lab lo
        _ = 1 := ih m hm (lowLab lab) rules.1 rules.2

end
end KakutaniSupport

-- END INLINED FILE: Mathlib/Support/kakutani_fixed_point_7ac198bd0e/Exterior.lean

namespace Submission

-- BEGIN INLINED FILE: Main.lean

namespace LeanEval
namespace Topology

/-!
# Kakutani fixed-point theorem

§33 of Oliver Knill's *Some Fundamental Theorems in Mathematics* (an
additional statement in the section on game theory; Nash's 1951 proof of
equilibrium existence uses Kakutani directly). The set-valued
generalization of Brouwer: every upper-hemicontinuous correspondence from
a nonempty compact convex `K ⊆ ℝᵈ` to itself with nonempty convex closed
values has a fixed point `x ∈ F x`.

mathlib has Brouwer-related lattices/logics under `grep -ri kakutani` only
the Riesz–Markov–Kakutani representation theorem for positive functionals
— a different theorem entirely. The fixed-point theorem itself is not in
mathlib.
-/

/-- A correspondence `F : α → Set β` is **upper hemicontinuous** in the
closed-graph sense if its graph `{(x, y) | y ∈ F x}` is closed in `α × β`.
For closed-valued maps into a compact space this coincides with the
sequential/topological definition. -/
def IsUpperHemicontinuous {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β] (F : α → Set β) : Prop :=
  IsClosed {p : α × β | p.2 ∈ F p.1}



end Topology
end LeanEval

open LeanEval.Topology
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem kakutani_fixed_point {d : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin d))}
    (_hK_compact : IsCompact K) (_hK_convex : Convex ℝ K)
    (_hK_nonempty : K.Nonempty)
    (F : EuclideanSpace ℝ (Fin d) → Set (EuclideanSpace ℝ (Fin d)))
    (_hF_uhc : IsUpperHemicontinuous F)
    (_hF_nonempty : ∀ x ∈ K, (F x).Nonempty)
    (_hF_convex : ∀ x ∈ K, Convex ℝ (F x))
    (_hF_closed : ∀ x ∈ K, IsClosed (F x))
    (_hF_maps : ∀ x ∈ K, F x ⊆ K) :
    ∃ x ∈ K, x ∈ F x :=
/-ResultProofBegin-/by
  classical
  -- First isolate the closed graph / limiting part.  It is useful to keep
  -- track of exactly which approximation is needed: no asymptotic membership
  -- in a thickened graph is being silently passed to the limit.
  apply KakutaniSupport.fixed_of_approximate_convexHull
    (V := EuclideanSpace ℝ (Fin d)) _hK_compact F
    (by
      change IsClosed {p : (EuclideanSpace ℝ (Fin d)) ×
        (EuclideanSpace ℝ (Fin d)) | p.2 ∈ F p.1}
      exact _hF_uhc)
    _hF_nonempty _hF_convex _hF_closed _hF_maps
  -- The finite partition of unity giving the approximation only uses a
  -- single-valued continuous fixed point principle on the compact convex
  -- set.  All compactness/closed-graph limiting arguments now live above,
  -- rather than as a mistaken selection argument.
  apply KakutaniSupport.approximate_convexHull_of_continuous_fixed
    (V := EuclideanSpace ℝ (Fin d)) _hK_compact _hK_convex F
    _hF_nonempty _hF_maps
  -- This is the remaining (ordinary Brouwer) input: fixed points for
  -- continuous self maps of a compact convex subtype.
  intro f hf
  -- projection onto a complete convex set is a nonexpanding retraction; bounding coordinate
  -- extrema reduces the single-valued theorem in turn to the cubical Brouwer assertion.
  apply KakutaniSupport.continuous_fixed_of_cube_approx
    (n := d) ?_ K _hK_compact _hK_convex _hK_nonempty f hf
  intro R hR g hg ε hε
  have hc : KakutaniSupport.CubicalCross d := by
    by_cases h0 : d = 0
    · subst d
      exact KakutaniSupport.cubicalCross_zero
    · by_cases h1 : d = 1
      · subst d
        exact KakutaniSupport.cubicalCross_one
      · have hd2 : 2 ≤ d := by omega
        exact KakutaniSupport.cubicalCross_of_cubeSperner (by
          intro m hm lab hlo hhi
          by_cases hm1 : m = 1
          · subst m
            exact KakutaniSupport.cubeSperner_oneBox lab hlo hhi
          · -- the only still finite step: the (multi-dimensional) cubical
            -- Sperner/Kuhn colouring lemma for at least two axes/slices.
            have hm2 : 2 ≤ m := by omega
            -- For the remaining parity step we will count flags of a small
            -- Kuhn simplex, rather than assume a continuous selection.  In
            -- `Rainbow` the deletion identity is proved over `ZMod 2` for an
            -- *arbitrary* sequence of `d+1` colours.  Summing it over the
            -- grid is the usual first half of cubical Sperner; interior
            -- middle faces are paired by the adjacent transposition lemma.
            -- Incidence in each Kuhn simplex and cancellation of all interior
            -- and adjoining cubical faces are now kernel lemmas `full_to_boundary`.
            -- Thus all that remains is the genuinely lower, one-dimension
            -- smaller exterior face.
            obtain ⟨q, rq⟩ : ∃ q, d = q+1 := by
              refine ⟨d-1, by omega⟩
            subst d
            apply KakutaniSupport.cube_of_full_nonzero lab
            rw [KakutaniSupport.full_to_boundary lab hlo hhi (Fin.last q)]
            -- The surviving lower face is a copy of the grid of one smaller
            -- dimension.  Its parity is the induction count `fullsum_one`.
            letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
            rw [KakutaniSupport.boundary_as_lower lab hlo]
            have rr := KakutaniSupport.lower_rules lab hlo hhi
            have one := KakutaniSupport.fullsum_one q m hm
                (KakutaniSupport.lowLab lab) rr.1 rr.2
            rw [one]
            decide)
  exact KakutaniSupport.cube_approx_of_cross (n:=d) hc R hR g hg ε hε/-ResultProofEnd-/
/-ResultEnd-/
-- END INLINED FILE: Main.lean

end Submission
