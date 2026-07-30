import Submission.Separation
import Submission.SphereCommutationReduction
import Submission.StableGauss

namespace Submission.Helpers

open Set

noncomputable section

private abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Stabilizing the embedding turns stable commutativity of sphere maps into
uniqueness of the bounded component of the original complement. -/
theorem bounded_components_eq_of_stable_commutation
    (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : E d) 1 → E d)
    (hcont : Continuous r) (hinj : Function.Injective r)
    (x y : ((Set.range r)ᶜ : Set (E d)))
    (hxb : Bornology.IsBounded
      (connectedComponentIn (Set.range r)ᶜ (x : E d)))
    (hyb : Bornology.IsBounded
      (connectedComponentIn (Set.range r)ᶜ (y : E d))) :
    connectedComponentIn (Set.range r)ᶜ (x : E d) =
      connectedComponentIn (Set.range r)ᶜ (y : E d) := by
  let Ux : Set (E d) := connectedComponentIn (Set.range r)ᶜ (x : E d)
  have hxUx : (x : E d) ∈ Ux := mem_connectedComponentIn x.2
  have hUxOpen : IsOpen Ux :=
    (isOpen_compl_range_sphere_embedding d r hcont hinj).connectedComponentIn
  have hfrontx : frontier Ux = Set.range r :=
    frontier_bounded_sphere_complement_component_eq_range
      d hd r hcont hinj x.2 hxb
  have hsxb : Bornology.IsBounded
      (connectedComponentIn (Set.range (suspendedEmbedding d r))ᶜ
        (suspendedComplementPoint d r x : E (d + d))) :=
    isBounded_suspendedComponent d r Ux hUxOpen hxb hfrontx x hxUx

  let Uy : Set (E d) := connectedComponentIn (Set.range r)ᶜ (y : E d)
  have hyUy : (y : E d) ∈ Uy := mem_connectedComponentIn y.2
  have hUyOpen : IsOpen Uy :=
    (isOpen_compl_range_sphere_embedding d r hcont hinj).connectedComponentIn
  have hfronty : frontier Uy = Set.range r :=
    frontier_bounded_sphere_complement_component_eq_range
      d hd r hcont hinj y.2 hyb
  have hsyb : Bornology.IsBounded
      (connectedComponentIn (Set.range (suspendedEmbedding d r))ᶜ
        (suspendedComplementPoint d r y : E (d + d))) :=
    isBounded_suspendedComponent d r Uy hUyOpen hyb hfronty y hyUy

  let hscont : Continuous (suspendedEmbedding d r) :=
    continuous_suspendedEmbedding d hd r hcont
  have hxhom :=
    gaussMap_suspendedEmbedding_homotopic_stableSphereMap d hd r hcont x
  have hyhom :=
    gaussMap_suspendedEmbedding_homotopic_stableSphereMap d hd r hcont y
  have hstable : ContinuousMap.Homotopic
      ((stableSphereMap d (gaussMap d r hcont y)).comp
        (stableSphereMap d (gaussMap d r hcont x)))
      ((stableSphereMap d (gaussMap d r hcont x)).comp
        (stableSphereMap d (gaussMap d r hcont y))) := by
    simpa only [stableSphereMap_comp] using
      stableSphereMap_comp_comm d (gaussMap d r hcont y)
        (gaussMap d r hcont x)
  have hcomm : ContinuousMap.Homotopic
      ((gaussMap (d + d) (suspendedEmbedding d r) hscont
          (suspendedComplementPoint d r y)).comp
        (gaussMap (d + d) (suspendedEmbedding d r) hscont
          (suspendedComplementPoint d r x)))
      ((gaussMap (d + d) (suspendedEmbedding d r) hscont
          (suspendedComplementPoint d r x)).comp
        (gaussMap (d + d) (suspendedEmbedding d r) hscont
          (suspendedComplementPoint d r y))) :=
    (hyhom.comp hxhom).trans
      (hstable.trans (hxhom.comp hyhom).symm)
  have hdd : 2 ≤ d + d := by omega
  have hscomponents := bounded_components_eq_of_gaussMap_comp_comm
    (d + d) hdd (suspendedEmbedding d r) hscont
      (injective_suspendedEmbedding d r hinj)
      (suspendedComplementPoint d r x) (suspendedComplementPoint d r y)
      hsxb hsyb hcomm
  have hsyMem : (suspendedComplementPoint d r y : E (d + d)) ∈
      connectedComponentIn (Set.range (suspendedEmbedding d r))ᶜ
        (suspendedComplementPoint d r x : E (d + d)) := by
    rw [hscomponents]
    exact mem_connectedComponentIn (suspendedComplementPoint d r y).2
  have hyUx : (y : E d) ∈ Ux :=
    original_mem_region_of_suspendedComponent_mem
      d r Ux hUxOpen hxb hfrontx x y hxUx hsyMem
  exact connectedComponentIn_eq hyUx

/-- Stable commutativity supplies the uniqueness input in the component-count
reduction, while separation supplies existence. -/
theorem jordan_brouwer_of_stable_commutation
    (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : E d) 1 → E d)
    (hcont : Continuous r) (hinj : Function.Injective r) :
    Nat.card (ConnectedComponents ((Set.range r)ᶜ : Set (E d))) = 2 := by
  apply jordan_brouwer_of_bounded_component d hd r hcont
  · exact exists_bounded_sphere_complement_component d hd r hcont hinj
  · intro x hx y hy hxb hyb
    exact bounded_components_eq_of_stable_commutation
      d hd r hcont hinj ⟨x, hx⟩ ⟨y, hy⟩ hxb hyb

end

end Submission.Helpers
