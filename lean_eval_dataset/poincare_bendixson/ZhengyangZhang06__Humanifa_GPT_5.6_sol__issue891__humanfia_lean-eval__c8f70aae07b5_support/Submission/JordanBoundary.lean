import Submission.ArcSeparation
import Submission.Transport
import ChallengeDeps

open Function Set Topology

namespace Submission.JordanBoundary

noncomputable section

/-- Every complementary component of a Jordan curve has the whole curve as
its frontier. -/
theorem frontier_component_eq_range
    (r : C(Circle, ℂ)) (hinj : Injective r) {x : ℂ}
    (hx : x ∈ (range r)ᶜ) :
    frontier (connectedComponentIn (range r)ᶜ x) = range r := by
  let B : Set ℂ := connectedComponentIn (range r)ᶜ x
  have hfrontsub : frontier B ⊆ range r := by
    exact Components.frontier_component_subset_range r hx
  apply Subset.antisymm hfrontsub
  rintro z ⟨w, rfl⟩
  by_contra hwfront
  let K : Set Circle := r ⁻¹' frontier B
  have hKcompact : IsCompact K := by
    exact isCompact_univ.of_isClosed_subset
      (isClosed_frontier.preimage r.continuous) (subset_univ _)
  have hfrontne : (frontier B).Nonempty := by
    exact
      JordanHelpers.frontier_connectedComponentIn_compl_range_nonempty
        (E := ℂ) (by rw [Complex.rank_real_complex]; norm_num)
        r hx
  have hKne : K.Nonempty := by
    obtain ⟨y, hy⟩ := hfrontne
    obtain ⟨t, ht⟩ := hfrontsub hy
    refine ⟨t, ?_⟩
    change r t ∈ frontier B
    rw [ht]
    exact hy
  have hwK : w ∉ K := hwfront
  let e : Circle ≃ₜ Circle := Homeomorph.mulLeft (-w⁻¹)
  have hew : e w = -1 := by
    simp [e]
  let f : Circle → ℝ := fun t ↦ Complex.arg (e t : ℂ)
  have heslit (t : Circle) (ht : t ∈ K) :
      (e t : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff_arg]
    constructor
    · intro harg
      have het : e t = -1 := by
        apply Circle.injective_arg
        simpa only [Circle.coe_neg, Circle.coe_one,
          Complex.arg_neg_one] using harg
      have htw : t = w := e.injective (het.trans hew.symm)
      exact hwK (htw ▸ ht)
    · exact Circle.coe_ne_zero _
  have hfcont : ContinuousOn f K := by
    exact Complex.continuousOn_arg.comp
      ((continuous_subtype_val.comp e.continuous).continuousOn)
      heslit
  obtain ⟨tmin, htmin, hmin⟩ :=
    hKcompact.exists_isMinOn hKne hfcont
  obtain ⟨tmax, htmax, hmax⟩ :=
    hKcompact.exists_isMaxOn hKne hfcont
  let A : ℝ := f tmin
  let M : ℝ := f tmax
  have hAneg : -Real.pi < A :=
    Complex.neg_pi_lt_arg _
  have hMpi : M < Real.pi := by
    exact lt_of_le_of_ne (Complex.arg_le_pi _)
      (Complex.slitPlane_arg_ne_pi (heslit tmax htmax))
  have hAM : A ≤ M :=
    hmin htmax
  let a : ℝ := (-Real.pi + A) / 2
  let b : ℝ := (M + Real.pi) / 2
  have hnega : -Real.pi < a := by
    dsimp [a]
    linarith
  have hAb : A < b := by
    dsimp [b]
    linarith [hAM]
  have hMb : M < b := by
    dsimp [b]
    linarith [hMpi]
  have haA : a < A := by
    dsimp [a]
    linarith
  have hbpi : b < Real.pi := by
    dsimp [b]
    linarith
  have hab : a < b := haA.trans (hAM.trans_lt hMb)
  have hwidth : b - a < 2 * Real.pi := by
    linarith
  let θ : Path a b := Path.segment a b
  let η : Path (Circle.exp a) (Circle.exp b) :=
    θ.map Circle.exp.continuous
  have hθinj : Injective θ :=
    Path.segment_injective_of_ne hab.ne
  have hηinj : Injective η := by
    intro s t hst
    have hsIcc : θ s ∈ Icc a b := by
      dsimp only [θ]
      rw [Path.segment_apply, AffineMap.lineMap_apply_ring]
      constructor <;> nlinarith [s.2.1, s.2.2]
    have htIcc : θ t ∈ Icc a b := by
      dsimp only [θ]
      rw [Path.segment_apply, AffineMap.lineMap_apply_ring]
      constructor <;> nlinarith [t.2.1, t.2.2]
    have hangle : θ s = θ t :=
      Circle.exp_injOn_Icc hwidth hsIcc htIcc
        (by simpa only [η, Path.map_coe, Function.comp_apply] using hst)
    exact hθinj hangle
  let α : Path (r (e.symm (Circle.exp a)))
      (r (e.symm (Circle.exp b))) :=
    (η.map e.symm.continuous).map r.continuous
  have hαinj : Injective α :=
    hinj.comp (e.symm.injective.comp hηinj)
  have hαsub : range α ⊆ range r := by
    rintro _ ⟨t, rfl⟩
    exact ⟨e.symm (η t), rfl⟩
  have hfrontα : frontier B ⊆ range α := by
    intro y hy
    obtain ⟨t, rfl⟩ := hfrontsub hy
    have htK : t ∈ K := hy
    have hft : f t ∈ Icc a b := by
      constructor
      · exact haA.le.trans (hmin htK)
      · exact (hmax htK).trans hMb.le
    have hftRange : f t ∈ range θ := by
      change f t ∈ range (Path.segment a b)
      rw [Path.range_segment, segment_eq_Icc hab.le]
      exact hft
    obtain ⟨s, hs⟩ := hftRange
    refine ⟨s, ?_⟩
    change r (e.symm (Circle.exp (θ s))) = r t
    rw [hs]
    change r (e.symm (Circle.exp (Complex.arg (e t : ℂ)))) = r t
    rw [Circle.exp_arg, e.symm_apply_apply]
  have hrwNot : r w ∉ range α := by
    rintro ⟨s, hs⟩
    have heq :
        e.symm (Circle.exp (θ s)) = w := by
      apply hinj
      simpa only [α, η, Path.map_coe, Function.comp_apply] using hs
    have hexp : Circle.exp (θ s) = e w := by
      exact e.symm.injective (by simpa only [e.symm_apply_apply] using heq)
    have hsIcc : θ s ∈ Icc a b := by
      dsimp only [θ]
      rw [Path.segment_apply, AffineMap.lineMap_apply_ring]
      constructor <;> nlinarith [s.2.1, s.2.2]
    have hsAngle : θ s ∈ Ioc (-Real.pi) Real.pi :=
      ⟨hnega.trans_le hsIcc.1, hsIcc.2.trans hbpi.le⟩
    have harg :
        Complex.arg ((Circle.exp (θ s) : Circle) : ℂ) = θ s :=
      Circle.invOn_arg_exp.1 hsAngle
    have hewC : ((e w : Circle) : ℂ) = (-1 : ℂ) := by
      rw [hew]
      simp only [Circle.coe_neg, Circle.coe_one]
    have hθpi : θ s = Real.pi := by
      calc
        θ s = Complex.arg ((Circle.exp (θ s) : Circle) : ℂ) :=
          harg.symm
        _ = Complex.arg ((e w : Circle) : ℂ) := by rw [hexp]
        _ = Complex.arg (-1 : ℂ) := congrArg Complex.arg hewC
        _ = Real.pi := Complex.arg_neg_one
    linarith [hsIcc.2, hbpi]
  have hBopen : IsOpen B :=
    (isCompact_range r.continuous).isClosed.isOpen_compl
      |>.connectedComponentIn
  have hBsub : B ⊆ (range α)ᶜ := by
    intro y hyB hyα
    exact
      (connectedComponentIn_subset (range r)ᶜ x hyB)
        (hαsub hyα)
  have hcover : (range α)ᶜ ⊆ B ∪ (closure B)ᶜ := by
    intro y hy
    by_cases hyB : y ∈ B
    · exact Or.inl hyB
    · refine Or.inr ?_
      intro hyClosure
      have hyFront : y ∈ frontier B := by
        exact ⟨hyClosure, fun hyInterior ↦ hyB (interior_subset hyInterior)⟩
      exact hy (hfrontα hyFront)
  have hdisj : Disjoint B (closure B)ᶜ := by
    exact Set.disjoint_left.2 fun _ hyB hyCompl ↦
      hyCompl (subset_closure hyB)
  rcases
      (ArcSeparation.isPreconnected_compl_range α hαinj).subset_or_subset
        hBopen isClosed_closure.isOpen_compl hdisj hcover with
    hsub | hsub
  · have hrwB : r w ∈ B :=
      hsub hrwNot
    exact
      (connectedComponentIn_subset (range r)ᶜ x hrwB)
        ⟨w, rfl⟩
  · have hxArcCompl : x ∈ (range α)ᶜ :=
      fun hxα ↦ hx (hαsub hxα)
    exact (hsub hxArcCompl) (subset_closure (mem_connectedComponentIn hx))

/-- The bounded-component specialization of
`frontier_component_eq_range`. -/
theorem frontier_bounded_component_eq_range
    (r : C(Circle, ℂ)) (hinj : Injective r) {x : ℂ}
    (hx : x ∈ (range r)ᶜ)
    (_hbounded :
      Bornology.IsBounded (connectedComponentIn (range r)ᶜ x)) :
    frontier (connectedComponentIn (range r)ᶜ x) = range r :=
  frontier_component_eq_range r hinj hx

/-- The unbounded-component specialization of
`frontier_component_eq_range`. -/
theorem frontier_unbounded_component_eq_range
    (r : C(Circle, ℂ)) (hinj : Injective r) {x : ℂ}
    (hx : x ∈ (range r)ᶜ)
    (_hunbounded :
      ¬ Bornology.IsBounded (connectedComponentIn (range r)ᶜ x)) :
    frontier (connectedComponentIn (range r)ᶜ x) = range r :=
  frontier_component_eq_range r hinj hx

/-- Euclidean-plane form of `frontier_component_eq_range`. -/
theorem frontier_component_eq_range_plane
    (r : C(Circle, LeanEval.Dynamics.Plane)) (hinj : Injective r)
    {x : LeanEval.Dynamics.Plane} (hx : x ∈ (range r)ᶜ) :
    frontier (connectedComponentIn (range r)ᶜ x) = range r := by
  let e : LeanEval.Dynamics.Plane ≃ₜ ℂ :=
    Transport.planeEquiv.toHomeomorph
  let rc : C(Circle, ℂ) :=
    ⟨fun z ↦ e (r z), e.continuous.comp r.continuous⟩
  have hrcinj : Injective rc :=
    e.injective.comp hinj
  have hrange : e '' range r = range rc := by
    apply Subset.antisymm
    · rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, rfl⟩
    · rintro _ ⟨z, rfl⟩
      exact ⟨r z, ⟨z, rfl⟩, rfl⟩
  have hxC : e x ∈ (range rc)ᶜ := by
    intro hxRange
    obtain ⟨z, hz⟩ := hxRange
    apply hx
    refine ⟨z, ?_⟩
    apply e.injective
    simpa only [rc, ContinuousMap.coe_mk] using hz
  apply Set.image_injective.mpr e.injective
  calc
    e '' frontier (connectedComponentIn (range r)ᶜ x) =
        frontier (e '' connectedComponentIn (range r)ᶜ x) :=
      e.image_frontier _
    _ =
        frontier
          (connectedComponentIn (e '' (range r)ᶜ) (e x)) := by
      rw [e.image_connectedComponentIn hx]
    _ =
        frontier
          (connectedComponentIn (range rc)ᶜ (e x)) := by
      rw [e.image_compl, hrange]
    _ = range rc :=
      frontier_component_eq_range rc hrcinj hxC
    _ = e '' range r := hrange.symm

end

end Submission.JordanBoundary
