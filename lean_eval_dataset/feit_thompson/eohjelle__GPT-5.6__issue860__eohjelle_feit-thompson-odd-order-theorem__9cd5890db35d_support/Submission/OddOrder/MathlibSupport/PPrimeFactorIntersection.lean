import Submission.OddOrder.MathlibSupport.PPrimeCore

/-!
Coprime intersection control from a prime-power quotient factor.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

/-- If the image of `U` modulo `V` is a `p`-group, then a `p'`-subgroup
meets `U` inside `V`. -/
theorem inf_le_of_isPPrimeSubgroup_of_factor_isPGroup
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    {K V U : Subgroup G} [V.Normal]
    (hK : IsPPrimeSubgroup p K)
    (hfactor : IsPGroup p
      (U.map (QuotientGroup.mk' V))) :
    K ⊓ U ≤ V := by
  let q : G →* G ⧸ V := QuotientGroup.mk' V
  have hKmap : IsPPrimeSubgroup p (K.map q) := by
    rw [IsPPrimeSubgroup]
    exact hK.coprime_dvd_right (Subgroup.card_map_dvd K q)
  obtain ⟨n, hcard⟩ := IsPGroup.iff_card.mp hfactor
  have hcoprime : Nat.Coprime (Nat.card (K.map q))
      (Nat.card (U.map q)) := by
    rw [hcard]
    exact (hKmap.pow_left n).symm
  have hdisjoint : Disjoint (K.map q) (U.map q) :=
    Subgroup.disjoint_of_coprime_natCard hcoprime
  intro x hx
  have hxbot : q x ∈ (⊥ : Subgroup (G ⧸ V)) := by
    rw [← disjoint_iff.mp hdisjoint]
    exact ⟨Subgroup.mem_map_of_mem q hx.1,
      Subgroup.mem_map_of_mem q hx.2⟩
  exact QuotientGroup.eq_one_iff x |>.mp (Subgroup.mem_bot.mp hxbot)

end Submission.OddOrder.MathlibSupport
