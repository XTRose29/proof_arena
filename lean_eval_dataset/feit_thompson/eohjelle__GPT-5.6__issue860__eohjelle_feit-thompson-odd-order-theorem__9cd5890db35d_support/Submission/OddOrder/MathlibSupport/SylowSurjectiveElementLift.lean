import Submission.OddOrder.MathlibSupport.PElementCyclic
import Mathlib.GroupTheory.Sylow

/-!
Lifting p-elements through surjective homomorphisms inside Sylow subgroups.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G K : Type*} [Group G] [Group K] [Finite G]

/-- Every p-element in a surjective image has a preimage lying in a Sylow
p-subgroup of the source. -/
theorem exists_sylow_preimage_of_isPElement
    {p : ℕ} [Fact p.Prime] (f : G →* K)
    (hf : Function.Surjective f) {a : K} (ha : IsPElement p a) :
    ∃ (P : Sylow p G) (g : G), g ∈ P ∧ f g = a := by
  letI : Finite K := Finite.of_surjective f hf
  obtain ⟨Q, hQ⟩ := ha.zpowers_isPGroup.exists_le_sylow
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective hf p Q
  have haQ : a ∈ Q := hQ (Subgroup.mem_zpowers a)
  rw [← hP] at haQ
  rcases haQ with ⟨g, hgP, hga⟩
  exact ⟨P, g, hgP, hga⟩

end Submission.OddOrder.MathlibSupport
