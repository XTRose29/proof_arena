import Submission.OddOrder.MathlibSupport.SubrepresentationBurnsideExtension

/-!
Conjugation of subgroup-algebra elements and their ambient representation
endomorphisms.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- Conjugation by an ambient element, acting on the algebra of a normal
subgroup. -/
noncomputable def conjugateSubgroupAlgebra
    (H : Subgroup G) [H.Normal] (g : G) : k[H] ≃ₐ[k] k[H] :=
  MonoidAlgebra.domCongr k k (MulAut.conjNormal g)

/-- Conjugating an element of a normal subgroup algebra corresponds to
conjugating its represented ambient endomorphism. -/
theorem subgroupAlgebraEnd_conjugate_apply
    (rho : Representation k G V) (H : Subgroup G) [H.Normal]
    (g : G) (a : k[H]) (v : V) :
    subgroupAlgebraEnd rho H (conjugateSubgroupAlgebra H g a) v =
      rho g (subgroupAlgebraEnd rho H a (rho g⁻¹ v)) := by
  induction a using MonoidAlgebra.induction_on with
  | hM h =>
      simp [subgroupAlgebraEnd, subgroupAlgebraMap, conjugateSubgroupAlgebra]
  | hadd a b ha hb =>
      simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) ha hb
  | hsmul c a ha =>
      simpa only [map_smul, LinearMap.smul_apply, RingHom.id_apply, map_smul]
        using congrArg (c • ·) ha

/-- Endomorphism form of `subgroupAlgebraEnd_conjugate_apply`. -/
theorem subgroupAlgebraEnd_conjugate
    (rho : Representation k G V) (H : Subgroup G) [H.Normal]
    (g : G) (a : k[H]) :
    subgroupAlgebraEnd rho H (conjugateSubgroupAlgebra H g a) =
      rho g * subgroupAlgebraEnd rho H a * rho g⁻¹ := by
  ext v
  simp only [Module.End.mul_apply]
  exact subgroupAlgebraEnd_conjugate_apply rho H g a v

end Submission.OddOrder.MathlibSupport
