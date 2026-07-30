import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
Transport eigenspaces across an intertwining linear equivalence.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {k : Type u} {V : Type v} {W : Type w}
variable [Field k]
variable [AddCommGroup V] [Module k V]
variable [AddCommGroup W] [Module k W]

/-- An equivalence intertwining two endomorphisms restricts to an
equivalence of their eigenspaces. -/
def eigenspaceEquivOfIntertwining
    (e : V ≃ₗ[k] W) (f : Module.End k V) (g : Module.End k W)
    (hintertwine : ∀ x : V, e (f x) = g (e x)) (mu : k) :
    Module.End.eigenspace f mu ≃ₗ[k] Module.End.eigenspace g mu where
  toFun x :=
    ⟨e x.1, Module.End.mem_eigenspace_iff.mpr (by
      rw [← hintertwine]
      calc
        e (f x.1) = e (mu • x.1) :=
          congrArg e (Module.End.mem_eigenspace_iff.mp x.2)
        _ = mu • e x.1 := e.map_smul mu x.1)⟩
  invFun y :=
    ⟨e.symm y.1, Module.End.mem_eigenspace_iff.mpr (by
      apply e.injective
      rw [hintertwine, e.map_smul, e.apply_symm_apply]
      exact Module.End.mem_eigenspace_iff.mp y.2)⟩
  left_inv x := by
    apply Subtype.ext
    exact e.symm_apply_apply x.1
  right_inv y := by
    apply Subtype.ext
    exact e.apply_symm_apply y.1
  map_add' x y := by
    apply Subtype.ext
    exact e.map_add x.1 y.1
  map_smul' c x := by
    apply Subtype.ext
    exact e.map_smul c x.1

/-- Intertwined endomorphisms have eigenspaces of equal finrank. -/
theorem finrank_eigenspace_eq_of_intertwining
    (e : V ≃ₗ[k] W) (f : Module.End k V) (g : Module.End k W)
    (hintertwine : ∀ x : V, e (f x) = g (e x)) (mu : k) :
    Module.finrank k (Module.End.eigenspace f mu) =
      Module.finrank k (Module.End.eigenspace g mu) :=
  LinearEquiv.finrank_eq (eigenspaceEquivOfIntertwining e f g hintertwine mu)

end Submission.OddOrder.MathlibSupport
