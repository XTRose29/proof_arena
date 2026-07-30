import Submission.OddOrder.BG.Section04.RankTwoFittingDerived
import Submission.OddOrder.BG.Section04.RankTwoMinimalPrimeComplement
import Submission.OddOrder.MathlibSupport.ElementaryAbelianRankSylowTransport
import Submission.OddOrder.MathlibSupport.NilpotentPrimeCoreHall

/-!
Bender--Glauberman Theorem 4.20(c), for the least-prime factor.

The quotient by the Fitting subgroup is abelian by Theorem 4.20(a), hence
nilpotent.  Pull back its `p'`-core to a normal subgroup `H`.  A Sylow
`p`-subgroup of `H` lies in the Fitting subgroup, so the rank hypothesis
passes to `H`; Theorem 4.18(b) then identifies the `p'`-core of `H` as a
Hall subgroup.  The remaining quotient is a `p`-group.
-/

namespace Submission.OddOrder.BG.Section04

open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative

noncomputable section

universe u

/-- `BGsection4.v: rank2_min_p'core_Hall` (Bender--Glauberman
Theorem 4.20(c), least-prime factor). -/
theorem rank2_min_pPrimeCore_Hall
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (hpmin : ∀ {q : ℕ}, q.Prime → q ∣ Nat.card G → p ≤ q)
    (hodd : Odd (Nat.card G))
    (hsol : IsSolvable G)
    (hRank : ∀ q : ℕ, q.Prime →
      ¬ ∃ E : Subgroup (fittingCore G),
        IsElementaryAbelianOfRank q 3 E) :
    IsPrimeComplement p (pPrimeCore p G) := by
  classical
  letI : IsSolvable G := hsol
  let F : Subgroup G := fittingCore G
  letI : F.Normal := by
    dsimp [F]
    infer_instance
  have hderived : _root_.commutator G ≤ F := by
    exact rank2_der1_sub_Fitting hodd hsol hRank
  letI : IsMulCommutative (G ⧸ F) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hderived
  letI : Group.IsNilpotent (G ⧸ F) := by infer_instance

  let q : G →* G ⧸ F := QuotientGroup.mk' F
  let Q0 : Subgroup (G ⧸ F) := pPrimeCore p (G ⧸ F)
  let H : Subgroup G := Q0.comap q
  have hHnormal : H.Normal := by
    dsimp [H, Q0, q]
    infer_instance
  letI : H.Normal := hHnormal

  have hHallQ0 : IsPrimeComplement p Q0 := by
    dsimp [Q0]
    exact pPrimeCore_isPrimeComplement_of_isNilpotent
  obtain ⟨b, hQ0index⟩ := hHallQ0.exists_index_eq_pow
  have hHindex : H.index = Q0.index := by
    simpa [H, q] using
      Q0.index_comap_of_surjective (QuotientGroup.mk'_surjective F)
  have hquotGH : IsPGroup p (G ⧸ H) := by
    apply IsPGroup.of_card (n := b)
    rw [← H.index_eq_card, hHindex, hQ0index]

  let f : H →* G ⧸ F := q.comp H.subtype
  have hfrange : f.range = Q0 := by
    calc
      f.range = H.map q := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      _ = Q0 := by
        dsimp [H]
        exact Subgroup.map_comap_eq_self_of_surjective
          (QuotientGroup.mk'_surjective F) Q0
  let P : Sylow p H := Classical.choice Sylow.nonempty
  have hPmapQ0 : (P : Subgroup H).map f ≤ Q0 := by
    rw [← hfrange]
    exact Subgroup.map_le_range (f := f) (P : Subgroup H)
  have hPmapP : IsPGroup p ((P : Subgroup H).map f) :=
    P.isPGroup'.map f
  have hPmapPrime : Nat.Coprime p
      (Nat.card ((P : Subgroup H).map f)) :=
    (pPrimeCore_coprime_card (G := G ⧸ F) (p := p)).coprime_dvd_right
      (Subgroup.card_dvd_of_le hPmapQ0)
  have hPmapCard : Nat.card ((P : Subgroup H).map f) = 1 :=
    hPmapP.card_eq_or_dvd.resolve_right
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hPmapPrime)
  have hPmapBot : (P : Subgroup H).map f = ⊥ :=
    Subgroup.card_eq_one.mp hPmapCard
  have hPker : (P : Subgroup H) ≤ f.ker :=
    (Subgroup.map_eq_bot_iff (P : Subgroup H)).mp hPmapBot
  have hPF : (P : Subgroup H).map H.subtype ≤ F := by
    rintro x ⟨y, hyP, rfl⟩
    have hyker : f y = 1 := hPker hyP
    change q (y : G) = 1 at hyker
    exact (QuotientGroup.eq_one_iff (y : G)).mp hyker

  have hRankF : ¬ ∃ E : Subgroup F,
      IsElementaryAbelianOfRank p 3 E := by
    simpa [F] using hRank p (Fact.out : p.Prime)
  have hRankH : ¬ ∃ E : Subgroup H,
      IsElementaryAbelianOfRank p 3 E :=
    no_elementaryAbelian_rank_three_of_sylow_map_le P hPF hRankF
  have hpminH : ∀ {r : ℕ}, r.Prime → r ∣ Nat.card H → p ≤ r := by
    intro r hr hrH
    apply hpmin hr
    exact hrH.trans H.card_subgroup_dvd_card
  have hHallH : IsPrimeComplement p (pPrimeCore p H) :=
    rank2_min_p_complement hpminH (by infer_instance)
      (odd_natCard_subgroup H hodd) hRankH
  exact pPrimeCore_isPrimeComplement_of_quotient_isPGroup hHallH hquotGH

end

end Submission.OddOrder.BG.Section04
