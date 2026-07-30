import Submission.OddOrder.MathlibSupport.ElementaryAbelianSubmodule
import Mathlib.RepresentationTheory.Irreducible

/-!
Irreducibility of conjugation on a minimal invariant elementary abelian
subgroup.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- Every subgroup of `E` invariant under `H ≤ N(E)` is trivial or all of
`E`. -/
def IsMinimalInvariantUnderNormalizer
    (E : Subgroup G)
    (H : Subgroup (Subgroup.normalizer (E : Set G))) : Prop :=
  ∀ K : Subgroup E,
    (∀ h : H, ∀ x : E, x ∈ K → (H.subtype h) • x ∈ K) →
    K = ⊥ ∨ K = ⊤

/-- Minimality of invariant subgroups is exactly irreducibility of the
restricted conjugation representation. -/
theorem normalizerConjugation_isIrreducible
    (E : Subgroup G) (p : ℕ) [Fact p.Prime]
    [IsMulCommutative E] [Module (ZMod p) (Additive E)]
    (H : Subgroup (Subgroup.normalizer (E : Set G)))
    (hE : E ≠ ⊥) (hmin : IsMinimalInvariantUnderNormalizer E H) :
    Representation.IsIrreducible
      ((normalizerConjugationRepresentation E p).comp H.subtype) := by
  letI : Nontrivial E := E.nontrivial_iff_ne_bot.mpr hE
  let rho := (normalizerConjugationRepresentation E p).comp H.subtype
  let e := elementaryAbelianSubmoduleSubgroupOrderIso E p
  refine { toNontrivial := ?_, eq_bot_or_eq_top := ?_ }
  · obtain ⟨x, hx⟩ := exists_ne (1 : E)
    exact ⟨⊥, ⊤, fun h ↦ by
      have hxbot : Additive.ofMul x ∈ (⊥ : Subrepresentation rho) := by
        rw [h]
        trivial
      have hxzero : Additive.ofMul x = 0 := by
        change Additive.ofMul x ∈ (⊥ : Submodule (ZMod p) (Additive E)) at hxbot
        exact hxbot
      apply hx
      exact congrArg Additive.toMul hxzero⟩
  · intro sigma
    let W := sigma.toSubmodule
    let K : Subgroup E := e W
    have hKinv : ∀ h : H, ∀ x : E, x ∈ K → (H.subtype h) • x ∈ K := by
      intro h x hx
      change Additive.ofMul ((H.subtype h) • x) ∈ W
      have hxW : Additive.ofMul x ∈ W := hx
      have hsigma := sigma.apply_mem_toSubmodule h hxW
      exact hsigma
    rcases hmin K hKinv with hK | hK
    · left
      apply Subrepresentation.toSubmodule_injective
      change W = ⊥
      apply e.injective
      simpa [K] using hK
    · right
      apply Subrepresentation.toSubmodule_injective
      change W = ⊤
      apply e.injective
      simpa [K] using hK

end Submission.OddOrder.MathlibSupport
