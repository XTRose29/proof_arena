import Submission.OddOrder.BG.Section01.PStability

/-!
The faithful conjugation action of a normalizer-centralizer quotient.
-/

namespace Submission.OddOrder.MathlibSupport

open Submission.OddOrder.BG.Section01

variable {G : Type*} [Group G]

/-- Conjugation embeds `N_G(E) / C_G(E)` into the automorphism group of
`E`. -/
def normalizerQuotientConjugationHom (E : Subgroup G) :
    (Subgroup.normalizer (E : Set G) ⧸ normalizerCentralizer E) →* MulAut E :=
  QuotientGroup.lift (normalizerCentralizer E) E.normalizerMonoidHom <| by
    change (Subgroup.centralizer (E : Set G)).subgroupOf
      (Subgroup.normalizer (E : Set G)) ≤ E.normalizerMonoidHom.ker
    rw [Subgroup.normalizerMonoidHom_ker]

@[simp]
theorem normalizerQuotientConjugationHom_mk_apply
    (E : Subgroup G) (g : Subgroup.normalizer (E : Set G)) (e : E) :
    normalizerQuotientConjugationHom E
        (QuotientGroup.mk' (normalizerCentralizer E) g) e =
      E.normalizerMonoidHom g e :=
  rfl

/-- The normalizer-centralizer quotient action is faithful. -/
theorem normalizerQuotientConjugationHom_injective (E : Subgroup G) :
    Function.Injective (normalizerQuotientConjugationHom E) := by
  apply (QuotientGroup.injective_lift_iff
    (normalizerCentralizer E) E.normalizerMonoidHom _).mpr
  rw [normalizerCentralizer, Subgroup.normalizerMonoidHom_ker]

theorem normalizerQuotientConjugationHom_ker_eq_bot (E : Subgroup G) :
    (normalizerQuotientConjugationHom E).ker = ⊥ :=
  MonoidHom.ker_eq_bot _ (normalizerQuotientConjugationHom_injective E)

end Submission.OddOrder.MathlibSupport
