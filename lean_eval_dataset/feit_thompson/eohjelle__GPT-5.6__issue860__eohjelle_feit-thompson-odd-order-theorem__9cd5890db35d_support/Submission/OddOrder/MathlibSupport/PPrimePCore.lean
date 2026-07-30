import Submission.OddOrder.MathlibSupport.PCoreFunctorial
import Submission.OddOrder.MathlibSupport.PPrimeCoreQuotient

/-!
The first two terms of the alternating `p'`, `p` core series.

MathComp writes `O_{p',p}(G)` for the inverse image of the `p`-core of
`G / O_{p'}(G)`.  This module supplies that construction and its basic
quotient properties.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

/-- The `p'`, `p` core `O_{p',p}(G)`. -/
noncomputable def pPrimePCore (p : ℕ) (G : Type*) [Group G] [Finite G] : Subgroup G :=
  (pCore p (G ⧸ pPrimeCore p G)).comap
    (QuotientGroup.mk' (pPrimeCore p G))

instance pPrimePCore_normal : (pPrimePCore p G).Normal := by
  dsimp [pPrimePCore]
  infer_instance

theorem pPrimeCore_le_pPrimePCore : pPrimeCore p G ≤ pPrimePCore p G := by
  intro x hx
  change QuotientGroup.mk' (pPrimeCore p G) x ∈
    pCore p (G ⧸ pPrimeCore p G)
  have hqx : QuotientGroup.mk' (pPrimeCore p G) x = 1 :=
    (QuotientGroup.eq_one_iff x).mpr hx
  rw [hqx]
  exact Subgroup.one_mem _

theorem pPrimePCore_map_quotient_eq :
    (pPrimePCore p G).map (QuotientGroup.mk' (pPrimeCore p G)) =
      pCore p (G ⧸ pPrimeCore p G) := by
  exact Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective (pPrimeCore p G)) _

theorem pCore_le_pPrimePCore : pCore p G ≤ pPrimePCore p G := by
  change pCore p G ≤ (pCore p (G ⧸ pPrimeCore p G)).comap
    (QuotientGroup.mk' (pPrimeCore p G))
  exact Subgroup.map_le_iff_le_comap.mp <|
    map_pCore_le_of_surjective
      (QuotientGroup.mk' (pPrimeCore p G))
      (QuotientGroup.mk'_surjective (pPrimeCore p G))

theorem pPrimePCore_eq_pCore_of_pPrimeCore_eq_bot
    (hprimeCore : pPrimeCore p G = ⊥) :
    pPrimePCore p G = pCore p G := by
  apply le_antisymm
  · apply le_pCore
    · unfold pPrimePCore
      apply pCore_isPGroup.comap_of_ker_isPGroup
      rw [QuotientGroup.ker_mk', hprimeCore]
      exact IsPGroup.of_bot
    · infer_instance
  · exact pCore_le_pPrimePCore

end Submission.OddOrder.MathlibSupport
