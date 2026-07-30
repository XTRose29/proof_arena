import Submission.OddOrder.MathlibSupport.PPrimeCore

/-!
Functoriality of the prime-complement core under group isomorphisms.
-/

namespace Submission.OddOrder.MathlibSupport

/-- A group isomorphism carries the `p'`-core onto the `p'`-core. -/
theorem map_pPrimeCore_eq_mulEquiv
    {G K : Type*} [Group G] [Finite G]
    [Group K] [Finite K]
    {p : ℕ}
    (e : G ≃* K) :
    (pPrimeCore p G).map e.toMonoidHom = pPrimeCore p K := by
  have hforward :
      (pPrimeCore p G).map e.toMonoidHom ≤ pPrimeCore p K := by
    apply le_pPrimeCore
    · rw [IsPPrimeSubgroup]
      rw [Subgroup.card_map_of_injective e.injective]
      exact pPrimeCore_coprime_card
    · exact Subgroup.Normal.map (by infer_instance)
        e.toMonoidHom e.surjective
  have hbackward :
      (pPrimeCore p K).map e.symm.toMonoidHom ≤ pPrimeCore p G := by
    apply le_pPrimeCore
    · rw [IsPPrimeSubgroup]
      rw [Subgroup.card_map_of_injective e.symm.injective]
      exact pPrimeCore_coprime_card
    · exact Subgroup.Normal.map (by infer_instance)
        e.symm.toMonoidHom e.symm.surjective
  apply le_antisymm hforward
  rw [← Subgroup.map_le_map_iff_of_injective
    (f := e.symm.toMonoidHom) e.symm.injective]
  simpa [Subgroup.map_map] using hbackward

end Submission.OddOrder.MathlibSupport
