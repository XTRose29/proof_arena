import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
Endomorphisms of one-dimensional vector spaces.
-/

namespace Submission.OddOrder.MathlibSupport

variable {D V : Type*} [Field D] [AddCommGroup V] [Module D V]

/-- Any two endomorphisms of a one-dimensional vector space commute. -/
theorem endomorphisms_commute_of_finrank_eq_one
    (hV : Module.finrank D V = 1) (f g : Module.End D V) :
    Commute f g := by
  obtain ⟨a, ha, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hV f
  obtain ⟨b, hb, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hV g
  rw [commute_iff_eq]
  ext v
  rw [ha, hb]
  simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq]
  rw [smul_smul, smul_smul, mul_comm]

end Submission.OddOrder.MathlibSupport
