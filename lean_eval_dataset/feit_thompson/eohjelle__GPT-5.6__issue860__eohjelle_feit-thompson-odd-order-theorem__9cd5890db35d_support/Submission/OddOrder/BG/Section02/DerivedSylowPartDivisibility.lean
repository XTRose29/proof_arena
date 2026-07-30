import Submission.OddOrder.BG.Section02.DerivedSylowPart
import Submission.OddOrder.MathlibSupport.PElementCyclic

/-!
The divisibility statement `pQ` in `BGsection2.der1_odd_GL2_charf`.
-/

namespace Submission.OddOrder.BG.Section02

open Submission.OddOrder.MathlibSupport
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

/-- If `q` divides the ambient commutator, then it divides the part of that
commutator lying in any selected Sylow `q`-subgroup. -/
theorem prime_dvd_card_derivedSylowPart
    {q : ℕ} [Fact q.Prime] (Q : Sylow q G)
    (hq : q ∣ Nat.card (_root_.commutator G)) :
    q ∣ Nat.card (derivedSylowPart Q) := by
  let D : Subgroup G := _root_.commutator G
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := D) q hq
  let xG : G := x
  have hxorder : orderOf xG = q := by
    exact (Subgroup.orderOf_coe x).trans hx
  have hxP : IsPElement q xG := by
    refine ⟨1, ?_⟩
    rw [pow_one, ← hxorder]
    exact pow_orderOf_eq_one xG
  obtain ⟨S, hcycS⟩ := hxP.zpowers_isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S Q
  let y : G := MulAut.conj g xG
  have hxS : xG ∈ S := hcycS (Subgroup.mem_zpowers xG)
  have hyQ : y ∈ Q := by
    rw [← hg]
    change y ∈ MulAut.conj g • (S : Subgroup G)
    exact Subgroup.smul_mem_pointwise_smul xG (MulAut.conj g)
      (S : Subgroup G) hxS
  have hyD : y ∈ D := by
    change MulAut.conj g xG ∈ D
    simpa [xG, MulAut.conj_apply] using
      (show g * (x : G) * g⁻¹ ∈ D from
        (inferInstance : D.Normal).conj_mem x x.2 g)
  have hyorder : orderOf y = q := by
    calc
      orderOf y = orderOf xG :=
        orderOf_injective (MulAut.conj g).toMonoidHom
          (MulAut.conj g).injective xG
      _ = q := hxorder
  have hdvd : orderOf y ∣ Nat.card (derivedSylowPart Q) :=
    (derivedSylowPart Q).orderOf_dvd_natCard ⟨hyD, hyQ⟩
  simpa only [hyorder] using hdvd

end Submission.OddOrder.BG.Section02
