import Submission.OddOrder.MathlibSupport.PPrimeCore
import Submission.OddOrder.MathlibSupport.PrimeComplement

/-!
Hall structure in a derived subgroup detected after a `p'` quotient.

If the derived subgroup of `G / N` is a `p`-group and `N` is a normal
`p'`-subgroup, then the `p'`-core of the derived subgroup of `G` is a Hall
`p'`-subgroup.  Restricting the quotient map to the derived subgroup shows
that the index of its `p'`-core divides a power of `p`.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

/-- A normal `p'` quotient with `p`-group derived subgroup makes the
`p'`-core of the original derived subgroup a Hall `p'`-subgroup. -/
theorem pPrimeCore_commutator_isPrimeComplement_of_quotient
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    {N : Subgroup G} [N.Normal]
    (hN : IsPPrimeSubgroup p N)
    (hcomm : IsPGroup p (_root_.commutator (G ⧸ N))) :
    IsPrimeComplement p
      (pPrimeCore p (_root_.commutator G)) := by
  let D : Subgroup G := _root_.commutator G
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let f : D →* G ⧸ N := q.comp D.subtype
  have hfrange : f.range = _root_.commutator (G ⧸ N) := by
    calc
      f.range = D.map q := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      _ = _root_.commutator (G ⧸ N) := by
        dsimp only [D]
        rw [map_commutator_eq,
          MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)]
        rfl
  have hfrangeP : IsPGroup p f.range := by
    rw [hfrange]
    exact hcomm
  have hkerMapN : f.ker.map D.subtype ≤ N := by
    rintro x ⟨y, hy, rfl⟩
    have hyker : f y = 1 := MonoidHom.mem_ker.mp hy
    change q (y : G) = 1 at hyker
    exact (QuotientGroup.eq_one_iff (y : G)).mp hyker
  have hkerPrime : IsPPrimeSubgroup p f.ker := by
    rw [IsPPrimeSubgroup,
      ← Subgroup.card_map_of_injective D.subtype_injective]
    exact hN.coprime_dvd_right (Subgroup.card_dvd_of_le hkerMapN)
  have hkerCore : f.ker ≤ pPrimeCore p D :=
    le_pPrimeCore hkerPrime (by infer_instance)
  obtain ⟨n, hn⟩ := hfrangeP.exists_card_eq
  have hindexDvd : (pPrimeCore p D).index ∣ p ^ n := by
    rw [← hn, ← Subgroup.index_ker f]
    exact Subgroup.index_dvd_of_le hkerCore
  obtain ⟨m, _hmn, hm⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hindexDvd
  constructor
  · exact (pPrimeCore_coprime_card (G := D) (p := p)).symm
  · exact ⟨m, hm⟩

end Submission.OddOrder.MathlibSupport
