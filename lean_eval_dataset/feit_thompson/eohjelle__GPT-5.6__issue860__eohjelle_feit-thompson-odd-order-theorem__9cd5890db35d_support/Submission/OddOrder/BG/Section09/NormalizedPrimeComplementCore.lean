import Submission.OddOrder.MathlibSupport.FittingPCore
import Submission.OddOrder.MathlibSupport.PPrimeCoreQuotient

/-!
# Bender--Glauberman Section 9: normalized prime-complement cores

This file isolates the prime-complement-core argument at the start of the
proof of Theorem 9.1(b).  A `p'`-subgroup normalized by a Sylow `p`-subgroup
of a finite solvable group lies in the `p'`-core.  The ambient version then
shows that the normalizer of the mapped Sylow subgroup also normalizes the
mapped `p'`-core.
-/

namespace Submission.OddOrder.BG.Section09

open Submission.OddOrder.MathlibSupport

universe u

private theorem normalized_pPrimeSubgroup_le_pPrimeCore_local
    {H : Type u} [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p H)
    (hsol : IsSolvable H)
    {K : Subgroup H}
    (hKp' : IsPPrimeSubgroup p K)
    (hPK : (P : Subgroup H) ≤ Subgroup.normalizer (K : Set H)) :
    K ≤ pPrimeCore p H := by
  let O : Subgroup H := pPrimeCore p H
  letI : O.Normal := by
    dsimp only [O]
    infer_instance
  let q : H →* H ⧸ O := QuotientGroup.mk' O
  let Q : Subgroup (H ⧸ O) := pCore p (H ⧸ O)
  let Kq : Subgroup (H ⧸ O) := K.map q
  let Pq : Sylow p (H ⧸ O) :=
    P.mapSurjective (QuotientGroup.mk'_surjective O)
  letI : IsSolvable H := hsol
  letI : IsSolvable (H ⧸ O) := by
    infer_instance

  have hKqPrime : IsPPrimeSubgroup p Kq := by
    rw [IsPPrimeSubgroup]
    exact hKp'.coprime_dvd_right (Subgroup.card_map_dvd K q)
  have hQp : IsPGroup p Q := by
    dsimp only [Q]
    exact pCore_isPGroup
  obtain ⟨n, hQcard⟩ := IsPGroup.iff_card.mp hQp
  have hQKcoprime : Nat.Coprime (Nat.card Q) (Nat.card Kq) := by
    rw [hQcard]
    exact hKqPrime.pow_left n
  have hQKdisjoint : Disjoint Q Kq :=
    Subgroup.disjoint_of_coprime_natCard hQKcoprime

  have hPq_normalizes_Kq :
      (Pq : Subgroup (H ⧸ O)) ≤
        Subgroup.normalizer (Kq : Set (H ⧸ O)) := by
    simpa only [Pq, Kq, Sylow.coe_mapSurjective] using
      (Subgroup.map_mono hPK).trans (K.le_normalizer_map q)
  have hQPq : Q ≤ (Pq : Subgroup (H ⧸ O)) := pCore_le_sylow Pq
  have hQ_normalizes_Kq :
      Q ≤ Subgroup.normalizer (Kq : Set (H ⧸ O)) :=
    hQPq.trans hPq_normalizes_Kq
  have hKq_normalizes_Q :
      Kq ≤ Subgroup.normalizer (Q : Set (H ⧸ O)) := by
    rw [Q.normalizer_eq_top]
    exact le_top

  have hcommKq : ⁅Kq, Q⁆ ≤ Kq :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hQ_normalizes_Kq
  have hcommQ : ⁅Kq, Q⁆ ≤ Q :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hKq_normalizes_Q
  have hcommBot : ⁅Kq, Q⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (le_inf hcommQ hcommKq).trans
      (disjoint_iff.mp hQKdisjoint).le
  have hKq_centralizes_Q :
      Kq ≤ Subgroup.centralizer (Q : Set (H ⧸ O)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommBot

  have hcoreQuotient : pPrimeCore p (H ⧸ O) = ⊥ := by
    simpa only [O] using
      (pPrimeCore_quotient_self_eq_bot (G := H) (p := p))
  have hKqQ : Kq ≤ Q := by
    exact hKq_centralizes_Q.trans
      (centralizer_pCore_le_pCore_of_pPrimeCore_eq_bot hcoreQuotient)
  have hKqBot : Kq = ⊥ := by
    apply le_bot_iff.mp
    exact (le_inf hKqQ le_rfl).trans
      (disjoint_iff.mp hQKdisjoint).le

  change K ≤ O
  intro k hk
  have hkq : q k ∈ Kq := ⟨k, hk, rfl⟩
  rw [hKqBot] at hkq
  exact (QuotientGroup.eq_one_iff k).mp (Subgroup.mem_bot.mp hkq)

/-- A `p'`-subgroup of an ambient group that lies in a finite solvable
subgroup and is normalized by the image of one of its Sylow `p`-subgroups
lies in the mapped `p'`-core. -/
theorem normalized_pPrimeSubgroup_le_map_pPrimeCore
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (M : Subgroup G) (P : Sylow p M)
    (hsol : IsSolvable M)
    {K : Subgroup G}
    (hKM : K ≤ M)
    (hKp' : IsPPrimeSubgroup p K)
    (hPK : (P : Subgroup M).map M.subtype ≤
      Subgroup.normalizer (K : Set G)) :
    K ≤ (pPrimeCore p M).map M.subtype := by
  let KM : Subgroup M := K.subgroupOf M
  have hKMPrime : IsPPrimeSubgroup p KM := by
    rw [IsPPrimeSubgroup]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]
    exact hKp'
  have hP_normalizes_KM :
      (P : Subgroup M) ≤ Subgroup.normalizer (KM : Set M) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hKM]
    intro x hx
    change (x : G) ∈ Subgroup.normalizer (K : Set G)
    apply hPK
    exact ⟨x, hx, rfl⟩
  have hKMCore : KM ≤ pPrimeCore p M :=
    normalized_pPrimeSubgroup_le_pPrimeCore_local
      P hsol hKMPrime hP_normalizes_KM
  rw [← Subgroup.map_subgroupOf_eq_of_le hKM]
  exact Subgroup.map_mono hKMCore

/-- If every ambient `p'`-subgroup normalized by the mapped Sylow subgroup
is forced back into `M`, then the ambient normalizer of that Sylow subgroup
normalizes the mapped `p'`-core of `M`. -/
theorem normalizer_map_sylow_le_normalizer_map_pPrimeCore
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (M : Subgroup G) (P : Sylow p M)
    (hsol : IsSolvable M)
    (hclosed : ∀ K : Subgroup G,
      IsPPrimeSubgroup p K →
      (P : Subgroup M).map M.subtype ≤
        Subgroup.normalizer (K : Set G) →
      K ≤ M) :
    Subgroup.normalizer
        ((P : Subgroup M).map M.subtype : Set G) ≤
      Subgroup.normalizer
        ((pPrimeCore p M).map M.subtype : Set G) := by
  let PM : Subgroup G := (P : Subgroup M).map M.subtype
  let O : Subgroup G := (pPrimeCore p M).map M.subtype
  have hPM_normalizes_O : PM ≤ Subgroup.normalizer (O : Set G) := by
    have hP_normalizes_core :
        (P : Subgroup M) ≤
          Subgroup.normalizer (pPrimeCore p M : Set M) := by
      rw [(pPrimeCore p M).normalizer_eq_top]
      exact le_top
    exact (Subgroup.map_mono hP_normalizes_core).trans
      ((pPrimeCore p M).le_normalizer_map M.subtype)

  intro x hx
  let e : G ≃* G := MulAut.conj x
  let Kx : Subgroup G := O.map e.toMonoidHom
  have hPMmap : PM.map e.toMonoidHom = PM := by
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hx
  have hPM_normalizes_Kx :
      PM ≤ Subgroup.normalizer (Kx : Set G) := by
    have hmapped := Subgroup.map_mono hPM_normalizes_O
      (f := e.toMonoidHom)
    rw [hPMmap, Subgroup.map_equiv_normalizer_eq O e] at hmapped
    exact hmapped
  have hKxPrime : IsPPrimeSubgroup p Kx := by
    rw [IsPPrimeSubgroup]
    rw [Subgroup.card_map_of_injective e.injective]
    dsimp only [O]
    rw [Subgroup.card_map_of_injective M.subtype_injective]
    exact pPrimeCore_coprime_card
  have hKxM : Kx ≤ M := hclosed Kx hKxPrime hPM_normalizes_Kx
  have hKxO : Kx ≤ O := by
    exact normalized_pPrimeSubgroup_le_map_pPrimeCore
      M P hsol hKxM hKxPrime hPM_normalizes_Kx
  have hKxEq : Kx = O := by
    apply Subgroup.eq_of_le_of_card_ge hKxO
    have hcard : Nat.card Kx = Nat.card O := by
      dsimp only [Kx]
      exact Subgroup.card_map_of_injective e.injective
    exact hcard.ge

  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hKxEq

end Submission.OddOrder.BG.Section09
