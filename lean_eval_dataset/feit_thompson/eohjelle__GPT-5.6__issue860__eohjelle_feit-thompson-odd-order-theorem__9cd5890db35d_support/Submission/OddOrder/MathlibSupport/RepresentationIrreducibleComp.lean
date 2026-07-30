import Mathlib.RepresentationTheory.Irreducible

/-!
Irreducibility transfer from a representation restricted along a monoid homomorphism.
-/

namespace Submission.OddOrder.MathlibSupport

variable {k V H K : Type*} [Semiring k] [AddCommMonoid V] [Module k V]
variable [Monoid H] [Monoid K]

/-- If a representation is irreducible after composition with a monoid
homomorphism, then the original representation is irreducible. -/
theorem representation_isIrreducible_of_comp
    (rho : Representation k K V) (f : H →* K)
    [IsSimpleOrder (Subrepresentation (rho.comp f))] :
    IsSimpleOrder (Subrepresentation rho) := by
  refine { toNontrivial := ?_, eq_bot_or_eq_top := ?_ }
  · refine ⟨⊥, ⊤, fun h ↦ ?_⟩
    have h' := congrArg Subrepresentation.toSubmodule h
    change (⊥ : Submodule k V) = ⊤ at h'
    apply (show (⊥ : Subrepresentation (rho.comp f)) ≠ ⊤ from bot_ne_top)
    apply Subrepresentation.toSubmodule_injective
    exact h'
  · intro sigma
    let tau : Subrepresentation (rho.comp f) :=
      { toSubmodule := sigma.toSubmodule
        apply_mem_toSubmodule h {v} hv := sigma.apply_mem_toSubmodule (f h) hv }
    rcases eq_bot_or_eq_top tau with htau | htau
    · left
      have htau' := congrArg Subrepresentation.toSubmodule htau
      change sigma.toSubmodule = (⊥ : Submodule k V) at htau'
      apply Subrepresentation.toSubmodule_injective
      exact htau'
    · right
      have htau' := congrArg Subrepresentation.toSubmodule htau
      change sigma.toSubmodule = (⊤ : Submodule k V) at htau'
      apply Subrepresentation.toSubmodule_injective
      exact htau'

end Submission.OddOrder.MathlibSupport
