import Submission.OddOrder.BG.AppendixAB.QuadraticAnticommutator
import Submission.OddOrder.MathlibSupport.RepresentationCentralizer

/-!
Centrality of the quadratic anticommutator on the generated local group.

This is the basis-free form of `cAG` in `BGappendixAB.odd_p_stable`.
-/

namespace Submission.OddOrder.BG.AppendixAB

open scoped IsMulCommutative
open Submission.OddOrder.BG.Section01
open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

theorem pairGenerated_le_representationCentralizer
    {k V H : Type*} [Semiring k] [Group H]
    [AddCommMonoid V] [Module k V]
    (rho : Representation k H V) (A : Module.End k V) {x y : H}
    (hx : Commute (rho x) A) (hy : Commute (rho y) A) :
    pairGenerated x y ≤ representationCentralizerSubgroup rho A :=
  pairGenerated_le_iff.mpr ⟨hx, hy⟩

theorem quadraticAnticommutator_commutes_quotient_pairGenerated
    (E : Subgroup G) (p : ℕ) [IsMulCommutative E]
    [Module (ZMod p) (Additive E)]
    {x y : G}
    (hxN : x ∈ Subgroup.normalizer (E : Set G))
    (hyN : y ∈ Subgroup.normalizer (E : Set G))
    (hx : IsQuadraticPElement p E x)
    (hy : IsQuadraticPElement p E y) :
    let q := QuotientGroup.mk' (normalizerCentralizer E)
    let xq := q ⟨x, hxN⟩
    let yq := q ⟨y, hyN⟩
    let A := quadraticAnticommutator E p ⟨x, hxN⟩ ⟨y, hyN⟩
    ∀ z : pairGenerated xq yq,
      Commute (centralizerQuotientConjugationRepresentation E p z.1) A := by
  dsimp only
  let q := QuotientGroup.mk' (normalizerCentralizer E)
  let xq := q ⟨x, hxN⟩
  let yq := q ⟨y, hyN⟩
  let A := quadraticAnticommutator E p ⟨x, hxN⟩ ⟨y, hyN⟩
  let rho := centralizerQuotientConjugationRepresentation E p
  have hxcomm : Commute (rho xq) A := by
    dsimp [rho, xq, q, A]
    have heq : centralizerQuotientConjugationRepresentation E p
        (⟨x, hxN⟩ : Subgroup.normalizer (E : Set G)) =
        normalizerConjugationRepresentation E p ⟨x, hxN⟩ := by
      apply LinearMap.ext
      intro v
      exact centralizerQuotientConjugationRepresentation_mk_apply E p ⟨x, hxN⟩ v
    rw [heq]
    exact quadraticAnticommutator_commutes_left E p hxN hyN hx
  have hycomm : Commute (rho yq) A := by
    dsimp [rho, yq, q, A]
    have heq : centralizerQuotientConjugationRepresentation E p
        (⟨y, hyN⟩ : Subgroup.normalizer (E : Set G)) =
        normalizerConjugationRepresentation E p ⟨y, hyN⟩ := by
      apply LinearMap.ext
      intro v
      exact centralizerQuotientConjugationRepresentation_mk_apply E p ⟨y, hyN⟩ v
    rw [heq]
    exact quadraticAnticommutator_commutes_right E p hxN hyN hy
  have hle : pairGenerated xq yq ≤
      representationCentralizerSubgroup rho A :=
    pairGenerated_le_representationCentralizer rho A hxcomm hycomm
  intro z
  exact hle z.2

end Submission.OddOrder.BG.AppendixAB
