import Mathlib.RepresentationTheory.Irreducible

/-!
Conjugation of subrepresentations in the restriction to a normal subgroup.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- Translate a subrepresentation of the restriction to a normal subgroup by
an ambient represented element. -/
def conjugateNormalSubrepresentation
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (g : G) (U : Subrepresentation (rho.comp N.subtype)) :
    Subrepresentation (rho.comp N.subtype) where
  toSubmodule := U.toSubmodule.map (rho g)
  apply_mem_toSubmodule n v hv := by
    obtain ⟨u, hu, rfl⟩ := hv
    let n' : N := ⟨g⁻¹ * (n : G) * g,
      Subgroup.Normal.conj_mem' inferInstance (n : G) n.property g⟩
    refine ⟨(rho n') u, U.apply_mem_toSubmodule n' hu, ?_⟩
    change rho g (rho n' u) = rho n (rho g u)
    simp only [← Module.End.mul_apply, ← rho.map_mul]
    congr 2
    dsimp [n']
    group

/-- Membership in a translated subrepresentation can be tested after applying
the inverse represented element. -/
theorem mem_conjugateNormalSubrepresentation_iff
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (g : G) (U : Subrepresentation (rho.comp N.subtype)) (v : V) :
    v ∈ conjugateNormalSubrepresentation rho N g U ↔ rho g⁻¹ v ∈ U := by
  constructor
  · rintro ⟨u, hu, huv⟩
    simpa [← huv]
  · intro hv
    refine ⟨rho g⁻¹ v, hv, ?_⟩
    simp

/-- Translating by the identity fixes every subrepresentation. -/
@[simp]
theorem conjugateNormalSubrepresentation_one
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (U : Subrepresentation (rho.comp N.subtype)) :
    conjugateNormalSubrepresentation rho N 1 U = U := by
  apply SetLike.ext
  intro v
  rw [mem_conjugateNormalSubrepresentation_iff]
  simp

/-- Translation by a product is successive translation. -/
theorem conjugateNormalSubrepresentation_mul
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (g h : G) (U : Subrepresentation (rho.comp N.subtype)) :
    conjugateNormalSubrepresentation rho N (g * h) U =
      conjugateNormalSubrepresentation rho N g
        (conjugateNormalSubrepresentation rho N h U) := by
  apply SetLike.ext
  intro v
  rw [mem_conjugateNormalSubrepresentation_iff,
    mem_conjugateNormalSubrepresentation_iff,
    mem_conjugateNormalSubrepresentation_iff]
  rw [mul_inv_rev, rho.map_mul]
  rfl

/-- Translation is monotone on the lattice of subrepresentations. -/
theorem conjugateNormalSubrepresentation_mono
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (g : G) {U W : Subrepresentation (rho.comp N.subtype)} (hUW : U ≤ W) :
    conjugateNormalSubrepresentation rho N g U ≤
      conjugateNormalSubrepresentation rho N g W := by
  intro v hv
  rw [mem_conjugateNormalSubrepresentation_iff] at hv ⊢
  exact hUW hv

/-- Ambient translation is an order automorphism of the normal restriction's
subrepresentation lattice. -/
def conjugateNormalSubrepresentationOrderIso
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (g : G) :
    Subrepresentation (rho.comp N.subtype) ≃o
      Subrepresentation (rho.comp N.subtype) where
  toFun := conjugateNormalSubrepresentation rho N g
  invFun := conjugateNormalSubrepresentation rho N g⁻¹
  left_inv U := by
    rw [← conjugateNormalSubrepresentation_mul]
    simp
  right_inv U := by
    rw [← conjugateNormalSubrepresentation_mul]
    simp
  map_rel_iff' := by
    intro U W
    constructor
    · intro h
      have h' := conjugateNormalSubrepresentation_mono rho N g⁻¹ h
      simpa [← conjugateNormalSubrepresentation_mul] using h'
    · exact conjugateNormalSubrepresentation_mono rho N g

end Submission.OddOrder.MathlibSupport
