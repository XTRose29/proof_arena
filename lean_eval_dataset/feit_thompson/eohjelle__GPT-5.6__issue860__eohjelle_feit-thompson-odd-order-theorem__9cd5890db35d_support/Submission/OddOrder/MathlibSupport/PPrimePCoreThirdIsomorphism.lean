import Submission.OddOrder.MathlibSupport.PPrimePCore

/-!
The third-isomorphism identification for the two-step `p'`, `p` core.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

/-- Quotienting first by `O_{p'}(G)` and then by the resulting `p`-core is
canonically equivalent to quotienting by `O_{p',p}(G)`. -/
noncomputable def pPrimePCoreQuotientEquiv
    (p : ℕ) (G : Type u) [Group G] [Finite G] :
    ((G ⧸ pPrimeCore p G) ⧸
      pCore p (G ⧸ pPrimeCore p G)) ≃*
      (G ⧸ pPrimePCore p G) :=
  (QuotientGroup.quotientMulEquivOfEq
      (pPrimePCore_map_quotient_eq (p := p) (G := G)).symm).trans
    (QuotientGroup.quotientQuotientEquivQuotient
      (pPrimeCore p G) (pPrimePCore p G) pPrimeCore_le_pPrimePCore)

end Submission.OddOrder.MathlibSupport
