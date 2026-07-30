import Submission.OddOrder.MathlibSupport.ElementaryAbelianIrreducible

/-!
Minimal normal subgroups relative to an acting subgroup.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- `E` is a nontrivial minimal subgroup normalized by `H`. -/
def IsMinimalNormalUnder (E H : Subgroup G) : Prop :=
  E ≠ ⊥ ∧
  H ≤ Subgroup.normalizer (E : Set G) ∧
  ∀ D : Subgroup G,
    D ≤ E → D ≠ ⊥ →
    (∀ g : G, g ∈ H → ∀ d : G, d ∈ D → g * d * g⁻¹ ∈ D) →
    E ≤ D

namespace IsMinimalNormalUnder

variable {E H : Subgroup G}

theorem ne_bot (h : IsMinimalNormalUnder E H) : E ≠ ⊥ := h.1

theorem le_normalizer (h : IsMinimalNormalUnder E H) :
    H ≤ Subgroup.normalizer (E : Set G) := h.2.1

theorem isMinimalInvariantUnderNormalizer (h : IsMinimalNormalUnder E H) :
    IsMinimalInvariantUnderNormalizer E
      (H.subgroupOf (Subgroup.normalizer (E : Set G))) := by
  intro K hKinv
  by_cases hK : K = ⊥
  · exact Or.inl hK
  · let D : Subgroup G := K.map E.subtype
    have hDE : D ≤ E := by
      dsimp [D]
      exact Subgroup.map_subtype_le K
    have hD : D ≠ ⊥ := by
      dsimp [D]
      intro hDbot
      apply hK
      exact (Subgroup.map_eq_bot_iff_of_injective
        K E.subtype_injective).mp hDbot
    have hDinv : ∀ g : G, g ∈ H → ∀ d : G, d ∈ D →
        g * d * g⁻¹ ∈ D := by
      intro g hg d hd
      rcases hd with ⟨k, hk, rfl⟩
      let gn : Subgroup.normalizer (E : Set G) := ⟨g, h.le_normalizer hg⟩
      let gh : H.subgroupOf (Subgroup.normalizer (E : Set G)) := ⟨gn, hg⟩
      have hconj : gn • k ∈ K := hKinv gh k hk
      exact ⟨gn • k, hconj, rfl⟩
    have hED : E ≤ D := h.2.2 D hDE hD hDinv
    right
    apply top_unique
    intro x _
    have hxD : (x : G) ∈ D := hED x.2
    rcases hxD with ⟨y, hy, hyx⟩
    have hxy : y = x := Subtype.ext hyx
    simpa [hxy] using hy

end IsMinimalNormalUnder

theorem normalizerConjugation_isIrreducible_of_isMinimalNormalUnder
    (E H : Subgroup G) (p : ℕ) [Fact p.Prime]
    [IsMulCommutative E] [Module (ZMod p) (Additive E)]
    (h : IsMinimalNormalUnder E H) :
    Representation.IsIrreducible
      ((normalizerConjugationRepresentation E p).comp
        (H.subgroupOf (Subgroup.normalizer (E : Set G))).subtype) :=
  normalizerConjugation_isIrreducible E p _ h.ne_bot
    h.isMinimalInvariantUnderNormalizer

end Submission.OddOrder.MathlibSupport
