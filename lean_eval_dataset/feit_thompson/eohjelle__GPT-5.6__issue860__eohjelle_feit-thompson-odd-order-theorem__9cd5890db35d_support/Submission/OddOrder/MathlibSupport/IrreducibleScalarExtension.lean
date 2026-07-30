import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.RepresentationTheory.Irreducible

/-!
Irreducibility after extending the scalar-linear structure on a fixed action.
-/

namespace Submission.OddOrder.MathlibSupport

variable {k D V G : Type*} [Semiring k] [Semiring D] [AddCommMonoid V]
variable [Module k V] [Module D V] [SMul k D] [IsScalarTower k D V]
variable [Monoid G]

/-- If the same group action is irreducible over `k`, then it remains
irreducible when its operators are linear over a larger scalar field `D`.

This direction needs no finite-dimensional hypothesis: a `D`-linear
subrepresentation can simply be restricted to a `k`-linear one. -/
theorem representation_isIrreducible_of_scalar_extension
    (rhoK : Representation k G V) (rhoD : Representation D G V)
    (hact : ∀ g v, rhoD g v = rhoK g v)
    [IsSimpleOrder (Subrepresentation rhoK)] :
    IsSimpleOrder (Subrepresentation rhoD) := by
  refine { toNontrivial := ?_, eq_bot_or_eq_top := ?_ }
  · refine ⟨⊥, ⊤, fun h ↦ ?_⟩
    have hD : (⊥ : Submodule D V) = ⊤ :=
      congrArg Subrepresentation.toSubmodule h
    have hk : (⊥ : Submodule k V) = ⊤ := by
      ext v
      have hv := SetLike.ext_iff.mp hD v
      simpa using hv
    apply (show (⊥ : Subrepresentation rhoK) ≠ ⊤ from bot_ne_top)
    apply Subrepresentation.toSubmodule_injective
    exact hk
  · intro sigma
    let tau : Subrepresentation rhoK :=
      { toSubmodule := sigma.toSubmodule.restrictScalars k
        apply_mem_toSubmodule g {v} hv := by
          change rhoK g v ∈ sigma.toSubmodule
          rw [← hact g v]
          exact sigma.apply_mem_toSubmodule g hv }
    rcases eq_bot_or_eq_top tau with htau | htau
    · left
      have htau' := congrArg Subrepresentation.toSubmodule htau
      change sigma.toSubmodule.restrictScalars k = ⊥ at htau'
      apply Subrepresentation.toSubmodule_injective
      change sigma.toSubmodule = (⊥ : Submodule D V)
      apply Submodule.restrictScalars_injective k D V
      simpa only [Submodule.restrictScalars_bot] using htau'
    · right
      have htau' := congrArg Subrepresentation.toSubmodule htau
      change sigma.toSubmodule.restrictScalars k = ⊤ at htau'
      apply Subrepresentation.toSubmodule_injective
      change sigma.toSubmodule = (⊤ : Submodule D V)
      apply Submodule.restrictScalars_injective k D V
      simpa only [Submodule.restrictScalars_top] using htau'

end Submission.OddOrder.MathlibSupport
