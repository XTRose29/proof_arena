import Submission.OddOrder.MathlibSupport.PPrimeCore
import Submission.OddOrder.MathlibSupport.PrimeComplement

/-!
Containment of `p'`-subgroups in a normal Hall `p'`-subgroup.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

/-- Every `p'`-subgroup lies in a normal Hall `p'`-subgroup. -/
theorem isPPrimeSubgroup_le_normal_primeComplement
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    {H A : Subgroup G}
    (hHnormal : H.Normal)
    (hH : IsPrimeComplement p H)
    (hA : IsPPrimeSubgroup p A) :
    A ≤ H := by
  letI : H.Normal := hHnormal
  let q : G →* G ⧸ H := QuotientGroup.mk' H
  have hQp : IsPGroup p (G ⧸ H) := by
    obtain ⟨n, hn⟩ := hH.exists_index_eq_pow
    apply IsPGroup.of_card (n := n)
    rw [← H.index_eq_card, hn]
  have hAmapP : IsPGroup p (A.map q) := hQp.to_subgroup (A.map q)
  have hAmapPrime : IsPPrimeSubgroup p (A.map q) := by
    rw [IsPPrimeSubgroup]
    exact hA.coprime_dvd_right (Subgroup.card_map_dvd A q)
  have hnotDvd : ¬ p ∣ Nat.card (A.map q) :=
    (Fact.out : p.Prime).coprime_iff_not_dvd.mp hAmapPrime
  have hAmapCard : Nat.card (A.map q) = 1 :=
    hAmapP.card_eq_or_dvd.resolve_right hnotDvd
  have hAmapBot : A.map q = ⊥ := Subgroup.card_eq_one.mp hAmapCard
  have hAleKer : A ≤ q.ker := (Subgroup.map_eq_bot_iff A).mp hAmapBot
  simpa [q, QuotientGroup.ker_mk'] using hAleKer

end Submission.OddOrder.MathlibSupport
