import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
Characteristic subgroups are invariant under subgroups of the ambient
normalizer.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- If `R` is characteristic in `E`, then its image in the ambient group is
invariant under every subgroup of `N_G(E)`. -/
theorem characteristic_map_subtype_invariant_under_normalizer
    (E H : Subgroup G) (R : Subgroup E) [R.Characteristic]
    (hH : H ≤ Subgroup.normalizer (E : Set G)) :
    ∀ g : G, g ∈ H → ∀ d : G, d ∈ R.map E.subtype →
      g * d * g⁻¹ ∈ R.map E.subtype := by
  intro g hg d hd
  rcases hd with ⟨r, hr, rfl⟩
  let gn : Subgroup.normalizer (E : Set G) := ⟨g, hH hg⟩
  refine ⟨E.normalizerMonoidHom gn r, ?_, rfl⟩
  exact (SetLike.ext_iff.mp
    ((show R.Characteristic from inferInstance).fixed
      (E.normalizerMonoidHom gn)) r).mpr hr

end Submission.OddOrder.MathlibSupport
