import Mathlib.GroupTheory.PGroup

/-!
Lifting p-group structure from a subgroup image and the kernel of the
restricted homomorphism.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G K : Type*} [Group G] [Group K]

/-- A subgroup is a p-group when its image is a p-group and the kernel of the
homomorphism restricted to that subgroup is a p-group. -/
theorem isPGroup_of_map_and_restrict_ker {p : ℕ}
    (D : Subgroup G) (f : G →* K)
    (hmap : IsPGroup p (D.map f))
    (hker : IsPGroup p (f.restrict D).ker) :
    IsPGroup p D := by
  intro d
  have hfd : f (d : G) ∈ D.map f := ⟨d, d.property, rfl⟩
  obtain ⟨j, hj⟩ := hmap ⟨f (d : G), hfd⟩
  have hfj : f ((d : G) ^ p ^ j) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val hj
  let dk : (f.restrict D).ker := ⟨d ^ p ^ j, hfj⟩
  obtain ⟨k, hk⟩ := hker dk
  refine ⟨j + k, ?_⟩
  apply Subtype.ext
  have hkD : (dk : D) ^ p ^ k = 1 := congrArg Subtype.val hk
  have hkG : ((dk : D) : G) ^ p ^ k = 1 := congrArg Subtype.val hkD
  simpa [dk, ← pow_mul, ← pow_add] using hkG

end Submission.OddOrder.MathlibSupport
