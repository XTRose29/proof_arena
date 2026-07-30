import Mathlib.RepresentationTheory.Irreducible
import Submission.OddOrder.MathlibSupport.EndomorphismConjugationRepresentation

/-!
Invariant endomorphisms under the conjugation representation.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- Invariant vectors in the conjugation representation on `End_k(V)` are
the same linear space as self-intertwining maps of the original
representation. -/
noncomputable def endomorphismConjugationInvariantsEquivIntertwiningMap
    (rho : Representation k G V) :
    (endomorphismConjugationRepresentation rho).invariants ≃ₗ[k]
      Representation.IntertwiningMap rho rho where
  toFun T :=
    { toLinearMap := T
      isIntertwining' := fun g ↦ by
        ext v
        have hg :=
          (mem_endomorphismConjugation_invariants_iff rho T).mp T.property g
        exact DFunLike.congr_fun hg.eq v }
  invFun f :=
    ⟨f.toLinearMap,
      (mem_endomorphismConjugation_invariants_iff rho f.toLinearMap).mpr
        (fun g ↦ by
          rw [Commute]
          ext v
          exact Representation.IntertwiningMap.isIntertwining
            rho rho f g v)⟩
  left_inv T := by
    apply Subtype.ext
    rfl
  right_inv f := by
    ext v
    rfl
  map_add' A B := by
    ext v
    rfl
  map_smul' c A := by
    ext v
    rfl

/-- For an irreducible finite-dimensional representation over an
algebraically closed field, the invariant subspace of the endomorphism
conjugation representation is one-dimensional. -/
theorem finrank_endomorphismConjugation_invariants
    [IsAlgClosed k] [FiniteDimensional k V]
    (rho : Representation k G V) [Representation.IsIrreducible rho] :
    Module.finrank k
      (endomorphismConjugationRepresentation rho).invariants = 1 := by
  rw [LinearEquiv.finrank_eq
    (endomorphismConjugationInvariantsEquivIntertwiningMap rho)]
  exact Representation.IsIrreducible.finrank_intertwiningMap_self rho

end Submission.OddOrder.MathlibSupport
