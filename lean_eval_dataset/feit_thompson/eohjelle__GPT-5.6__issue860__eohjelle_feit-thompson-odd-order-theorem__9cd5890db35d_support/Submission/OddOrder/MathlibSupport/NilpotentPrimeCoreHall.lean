import Submission.OddOrder.MathlibSupport.NilpotentPrimeCores
import Submission.OddOrder.MathlibSupport.PrimeComplement

/-!
Hall structure of the prime-complement core in a finite nilpotent group,
and its transport across a normal `p`-group quotient.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- In a finite nilpotent group, the `p'`-core is a Hall `p'`-subgroup. -/
theorem pPrimeCore_isPrimeComplement_of_isNilpotent
    [Group.IsNilpotent G] :
    IsPrimeComplement p (pPrimeCore p G) := by
  have hcomp : (pCore p G).IsComplement' (pPrimeCore p G) := by
    letI : (pCore p G).Normal := by infer_instance
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
      (disjoint_pCore_pPrimeCore (G := G) (p := p))
    rw [← Subgroup.normal_mul (pCore p G) (pPrimeCore p G),
      sup_pCore_pPrimeCore_eq_top_of_isNilpotent (G := G) p]
    rfl
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := p) (G := G)).exists_card_eq
  exact ⟨(pPrimeCore_coprime_card (G := G) (p := p)).symm,
    ⟨n, hcomp.index_eq_card.trans hn⟩⟩

/-- If `H` is normal and `G / H` is a `p`-group, then the `p'`-core of
`H`, mapped into `G`, is the `p'`-core of `G`. -/
theorem map_pPrimeCore_eq_of_quotient_isPGroup
    {H : Subgroup G} [H.Normal]
    (hquot : IsPGroup p (G ⧸ H)) :
    (pPrimeCore p H).map H.subtype = pPrimeCore p G := by
  let R : Subgroup G := (pPrimeCore p H).map H.subtype
  have hRle : R ≤ pPrimeCore p G := by
    apply le_pPrimeCore
    · change IsPPrimeSubgroup p ((pPrimeCore p H).map H.subtype)
      rw [IsPPrimeSubgroup,
        Subgroup.card_map_of_injective H.subtype_injective]
      exact pPrimeCore_coprime_card
    · dsimp [R]
      infer_instance
  have hcoreH : pPrimeCore p G ≤ H := by
    let q : G →* G ⧸ H := QuotientGroup.mk' H
    let Obar : Subgroup (G ⧸ H) := (pPrimeCore p G).map q
    have hObarP : IsPGroup p Obar := hquot.to_subgroup Obar
    have hObarPrime : IsPPrimeSubgroup p Obar := by
      rw [IsPPrimeSubgroup]
      exact (pPrimeCore_coprime_card (G := G) (p := p)).coprime_dvd_right
        (Subgroup.card_map_dvd (pPrimeCore p G) q)
    have hObarCore : Obar ≤ pPrimeCore p (G ⧸ H) := by
      apply le_pPrimeCore hObarPrime
      dsimp [Obar]
      infer_instance
    have hObarBot : Obar = ⊥ := by
      apply le_bot_iff.mp
      rw [← disjoint_iff.mp
        (disjoint_pPrimeCore_of_isPGroup (G := G ⧸ H) hObarP)]
      exact le_inf le_rfl hObarCore
    have hker : pPrimeCore p G ≤ q.ker :=
      (Subgroup.map_eq_bot_iff (pPrimeCore p G)).mp hObarBot
    simpa [q, QuotientGroup.ker_mk'] using hker
  have hcoreLeR : pPrimeCore p G ≤ R := by
    change pPrimeCore p G ≤ (pPrimeCore p H).map H.subtype
    rw [← Subgroup.map_subgroupOf_eq_of_le hcoreH]
    apply Subgroup.map_mono
    apply le_pPrimeCore
    · rw [IsPPrimeSubgroup,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcoreH).toEquiv]
      exact pPrimeCore_coprime_card
    · infer_instance
  exact le_antisymm hRle hcoreLeR

/-- A Hall `p'`-core in a normal subgroup remains Hall after extending by
a `p`-group quotient. -/
theorem pPrimeCore_isPrimeComplement_of_quotient_isPGroup
    {H : Subgroup G} [H.Normal]
    (hHall : IsPrimeComplement p (pPrimeCore p H))
    (hquot : IsPGroup p (G ⧸ H)) :
    IsPrimeComplement p (pPrimeCore p G) := by
  obtain ⟨a, ha⟩ := hHall.exists_index_eq_pow
  obtain ⟨b, hb⟩ := hquot.exists_card_eq
  refine ⟨(pPrimeCore_coprime_card (G := G) (p := p)).symm,
    ⟨a + b, ?_⟩⟩
  rw [← map_pPrimeCore_eq_of_quotient_isPGroup hquot,
    Subgroup.index_map_subtype, ha, H.index_eq_card, hb, pow_add]

end Submission.OddOrder.MathlibSupport
