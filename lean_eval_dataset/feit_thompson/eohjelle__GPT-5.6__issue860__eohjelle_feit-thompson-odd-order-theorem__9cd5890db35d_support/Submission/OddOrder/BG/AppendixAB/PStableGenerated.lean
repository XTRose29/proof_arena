import Submission.OddOrder.BG.Section01.PStability
import Submission.OddOrder.BG.Section01.Puig

/-!
The generated-subgroup consequence of `p`-stability.

This is the mathlib-shaped, conditional form of Bender-Glauberman A.5.1.  It
also supplies the quotient comparison needed to pass from the normalizer
quotient in `IsPStable` to the ambient quotient when `P` is normal.
-/

namespace Submission.OddOrder.BG.AppendixAB

open Submission.OddOrder.BG.Section01
open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- For normal `P`, the inclusion `N_G(P) → G` induces the expected map from
`N_G(P) / C_G(P)` to `G / C_G(P)`. -/
def normalizerQuotientToAmbient (P : Subgroup G) [P.Normal] :
    (Subgroup.normalizer (P : Set G) ⧸ normalizerCentralizer P) →*
      G ⧸ Subgroup.centralizer (P : Set G) :=
  QuotientGroup.map (normalizerCentralizer P)
    (Subgroup.centralizer (P : Set G))
    (Subgroup.normalizer (P : Set G)).subtype (by
      intro x hx
      exact hx)

theorem normalizerQuotientToAmbient_surjective (P : Subgroup G) [P.Normal] :
    Function.Surjective (normalizerQuotientToAmbient P) := by
  apply QuotientGroup.map_surjective_of_surjective
  intro x
  refine Quotient.inductionOn' x fun g ↦ ?_
  refine ⟨⟨g, ?_⟩, rfl⟩
  rw [P.normalizer_eq_top]
  exact Subgroup.mem_top g

theorem imageInNormalizerCentralizerQuotient_map_eq
    (P A : Subgroup G) [P.Normal]
    (hA : A ≤ Subgroup.normalizer (P : Set G)) :
    (imageInNormalizerCentralizerQuotient P A).map
        (normalizerQuotientToAmbient P) =
      A.map (QuotientGroup.mk' (Subgroup.centralizer (P : Set G))) := by
  let N := Subgroup.normalizer (P : Set G)
  let C := Subgroup.centralizer (P : Set G)
  let qN := QuotientGroup.mk' (normalizerCentralizer P)
  let q := QuotientGroup.mk' C
  let f := normalizerQuotientToAmbient P
  have hf : f.comp qN = q.comp N.subtype := by
    ext x
    rfl
  calc
    (imageInNormalizerCentralizerQuotient P A).map f =
        (A.subgroupOf N).map (f.comp qN) := by
      rw [imageInNormalizerCentralizerQuotient, Subgroup.map_map]
    _ = (A.subgroupOf N).map (q.comp N.subtype) := by rw [hf]
    _ = ((A.subgroupOf N).map N.subtype).map q := by
      rw [Subgroup.map_map]
    _ = A.map q := by rw [Subgroup.map_subgroupOf_eq_of_le hA]

theorem pCore_normalizerQuotient_map_le (p : ℕ) (P : Subgroup G) [P.Normal] :
    (pCore p
        (Subgroup.normalizer (P : Set G) ⧸ normalizerCentralizer P)).map
        (normalizerQuotientToAmbient P) ≤
      pCore p (G ⧸ Subgroup.centralizer (P : Set G)) := by
  apply le_pCore (pCore_isPGroup.map (normalizerQuotientToAmbient P))
  exact Subgroup.Normal.map (by infer_instance) _
    (normalizerQuotientToAmbient_surjective P)

theorem pNormalizedAbelian_quotient_le_pCore_of_isPStable [Finite G]
    {p : ℕ} {P A : Subgroup G} [P.Normal]
    (hstable : IsPStable p G) (hP : IsPGroup p P)
    (hA : PNormalizedAbelian p P A) :
    A.map (QuotientGroup.mk' (Subgroup.centralizer (P : Set G))) ≤
      pCore p (G ⧸ Subgroup.centralizer (P : Set G)) := by
  have hAnormalizesP : A ≤ Subgroup.normalizer (P : Set G) := by
    rw [P.normalizer_eq_top]
    exact le_top
  have hcommPA : ⁅P, A⁆ ≤ A :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hA.2.1
  have hcommAA : ⁅A, A⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha b hb
    exact congrArg Subtype.val (hA.2.2 ⟨b, hb⟩ ⟨a, ha⟩)
  have hquadratic : ⁅⁅P, A⁆, A⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (Subgroup.commutator_mono hcommPA le_rfl).trans hcommAA.le
  have hstableA : imageInNormalizerCentralizerQuotient P A ≤
      pCore p
        (Subgroup.normalizer (P : Set G) ⧸ normalizerCentralizer P) := by
    exact hstable P A hP (by infer_instance) hA.1 hAnormalizesP hquadratic
  calc
    A.map (QuotientGroup.mk' (Subgroup.centralizer (P : Set G))) =
        (imageInNormalizerCentralizerQuotient P A).map
          (normalizerQuotientToAmbient P) :=
      (imageInNormalizerCentralizerQuotient_map_eq P A hAnormalizesP).symm
    _ ≤ (pCore p
          (Subgroup.normalizer (P : Set G) ⧸ normalizerCentralizer P)).map
          (normalizerQuotientToAmbient P) := Subgroup.map_mono hstableA
    _ ≤ pCore p (G ⧸ Subgroup.centralizer (P : Set G)) :=
      pCore_normalizerQuotient_map_le p P

/-- Conditional form of Bender-Glauberman A.5.1. -/
theorem abelianGenerated_quotient_le_pCore_of_isPStable [Finite G]
    {p : ℕ} {P X : Subgroup G} [P.Normal]
    (hstable : IsPStable p G) (hP : IsPGroup p P)
    (hgen : GeneratedBy (PNormalizedAbelian p P) X) :
    X.map (QuotientGroup.mk' (Subgroup.centralizer (P : Set G))) ≤
      pCore p (G ⧸ Subgroup.centralizer (P : Set G)) := by
  rw [Subgroup.map_le_iff_le_comap]
  apply hgen.le_of_forall_le
  intro A hA
  rw [← Subgroup.map_le_iff_le_comap]
  exact pNormalizedAbelian_quotient_le_pCore_of_isPStable hstable hP hA

end Submission.OddOrder.BG.AppendixAB
