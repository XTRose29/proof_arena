import Submission.OddOrder.BG.Section03.FrobeniusQuotientComplement
import Submission.OddOrder.MathlibSupport.CoprimeCentralFixedPoint

/-!
Frobenius quotients by complement-centralized kernel subgroups.
-/

namespace Submission.OddOrder.BG.Section03

open Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]
variable {K R N : Subgroup G}

namespace IsFrobeniusDecomposition

/-- If the complement centralizes a proper normal subgroup of the kernel,
the induced quotient decomposition is again Frobenius. This is the central
fixed-subgroup case of Bender-Glauberman Lemma 3.2. -/
theorem quotient_of_complement_le_centralizer
    (h : IsFrobeniusDecomposition K R) [N.Normal] (hNK : N < K)
    (hRN : R ≤ Subgroup.centralizer (N : Set G)) :
    IsFrobeniusDecomposition
      (K.map (QuotientGroup.mk' N))
      (R.map (QuotientGroup.mk' N)) := by
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  apply h.quotient_decomposition_of_fixedPointFree hNK
  intro rq hrq kq hkq
  rcases rq.property with ⟨r, hr, hrEq⟩
  rcases kq.property with ⟨k, hk, hkEq⟩
  let rR : R := ⟨r, hr⟩
  let kK : K := ⟨k, hk⟩
  have hrR : rR ≠ 1 := by
    intro hrOne
    apply hrq
    apply Subtype.ext
    rw [← hrEq]
    have hrOneG : r = 1 := congrArg Subtype.val hrOne
    rw [hrOneG, map_one]
    rfl
  letI := h.conjugationAction
  let NK : Subgroup K := N.subgroupOf K
  have hcop : Nat.Coprime (Nat.card NK) (orderOf rR) := by
    have hNdivK : Nat.card NK ∣ Nat.card K :=
      NK.card_subgroup_dvd_card
    have hordR : orderOf rR ∣ Nat.card R := orderOf_dvd_natCard rR
    exact (h.natCard_coprime.coprime_dvd_left hNdivK).coprime_dvd_right
      hordR
  have hfixN : ∀ n : NK, rR • (n : K) = n := by
    intro n
    apply Subtype.ext
    change r * (n : G) * r⁻¹ = (n : G)
    have hcomm :=
      Subgroup.mem_centralizer_iff.mp (hRN hr) (n : G) n.property
    calc
      r * (n : G) * r⁻¹ = (n : G) * r * r⁻¹ := by rw [hcomm.symm]
      _ = n := by simp
  have hfixed : ∀ x : K, rR • x = x → x ∈ NK := by
    intro x hx
    have hxOne : x = 1 := by
      apply h.fixedPointFree rR hrR x
      exact congrArg Subtype.val hx
    rw [hxOne]
    exact NK.one_mem
  have hqfix := hkq
  rw [← hrEq, ← hkEq] at hqfix
  have hqfix' : q (r * k * r⁻¹) = q k := by
    simpa only [map_mul, map_inv] using hqfix
  have herrG : (r * k * r⁻¹)⁻¹ * k ∈ N :=
    QuotientGroup.eq.mp hqfix'
  have herr : (rR • kK)⁻¹ * kK ∈ NK := by
    change ((((rR • kK : K) : G))⁻¹ * k) ∈ N
    rw [h.coe_smul]
    exact herrG
  have hkN : kK ∈ NK :=
    fixed_rep_mem_of_coprime_order_of_fixed_subgroup
      NK rR hcop hfixN hfixed kK herr
  apply Subtype.ext
  rw [← hkEq]
  exact (QuotientGroup.eq_one_iff (N := N) k).mpr hkN

end IsFrobeniusDecomposition

end Submission.OddOrder.BG.Section03
