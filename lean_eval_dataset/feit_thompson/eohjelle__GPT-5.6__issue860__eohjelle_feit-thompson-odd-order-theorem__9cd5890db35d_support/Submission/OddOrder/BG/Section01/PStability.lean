import Submission.OddOrder.MathlibSupport.PCore
import Submission.OddOrder.MathlibSupport.PPrimeCore

/-!
The `p`-stability predicate from `BGsection1`.

MathComp writes the target of the stability condition as
`'O_p('N_G(P) / 'C_G(P))`.  Here the centralizer is first regarded as a
normal subgroup of the normalizer, so the same expression is represented by
the mathlib quotient and `pCore`.
-/

namespace Submission.OddOrder.BG.Section01

open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- The centralizer of `P`, regarded as a normal subgroup of its normalizer. -/
def normalizerCentralizer (P : Subgroup G) :
    Subgroup (Subgroup.normalizer (P : Set G)) :=
  (Subgroup.centralizer (P : Set G)).subgroupOf
    (Subgroup.normalizer (P : Set G))

instance normalizerCentralizer_normal (P : Subgroup G) :
    (normalizerCentralizer P).Normal := by
  dsimp [normalizerCentralizer]
  infer_instance

/-- The image of `A` in `N_G(P) / C_G(P)`.  In applications `A` is contained
in `N_G(P)`; using `subgroupOf` makes the construction total. -/
def imageInNormalizerCentralizerQuotient (P A : Subgroup G) :
    Subgroup ((Subgroup.normalizer (P : Set G)) ⧸ normalizerCentralizer P) :=
  (A.subgroupOf (Subgroup.normalizer (P : Set G))).map
    (QuotientGroup.mk' (normalizerCentralizer P))

theorem imageInNormalizerCentralizerQuotient_isPGroup {p : ℕ}
    {P A : Subgroup G} (hA : IsPGroup p A) :
    IsPGroup p (imageInNormalizerCentralizerQuotient P A) := by
  exact (hA.comap_subtype.map
    (QuotientGroup.mk' (normalizerCentralizer P)))

/-- Bender-Glauberman `p`-stability.  The normality premise is the
mathlib-shaped form of `'O_p^'(G) * P <| G`; the final inclusion says that the
quadratic action of `A` on `P` is trivial modulo the `p`-core of
`N_G(P) / C_G(P)`. -/
def IsPStable (p : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ (P A : Subgroup G),
    IsPGroup p P →
    (pPrimeCore p G ⊔ P).Normal →
    IsPGroup p A →
    A ≤ Subgroup.normalizer (P : Set G) →
    ⁅⁅P, A⁆, A⁆ = ⊥ →
    imageInNormalizerCentralizerQuotient P A ≤
      pCore p ((Subgroup.normalizer (P : Set G)) ⧸ normalizerCentralizer P)

end Submission.OddOrder.BG.Section01
