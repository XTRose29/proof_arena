import Submission.OddOrder.MathlibSupport.PElement
import Submission.OddOrder.MathlibSupport.PLengthOne
import Submission.OddOrder.MathlibSupport.PPrimePCoreThirdIsomorphism
import Submission.OddOrder.MathlibSupport.PrimeComplement
import Submission.OddOrder.MathlibSupport.SylowSurjectiveElementLift

/-!
# Functoriality of groups of p-length one

This file ports Bender--Glauberman Lemma 1.21(a,d), in the form used later
in Sections 3, 10, and 11.  MathComp's `p.-length_1` predicate is represented
by `IsPLengthOne`; its two-step core is `pPrimePCore`.
-/

namespace Submission.OddOrder.BG.Section01

open Submission.OddOrder.MathlibSupport

universe u v

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- The defining Sylow condition for p-length one can equivalently be read
off from the index of `O_{p',p}(G)`. -/
private theorem isPLengthOne_iff_not_dvd_pPrimePCore_index :
    IsPLengthOne p G ↔ ¬ p ∣ (pPrimePCore p G).index := by
  have hindex :
      (pPrimePCore p G).index =
        (pCore p (G ⧸ pPrimeCore p G)).index := by
    rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
    exact (Nat.card_congr (pPrimePCoreQuotientEquiv p G).toEquiv).symm
  constructor
  · rintro ⟨P, hP⟩
    rw [hindex, ← hP]
    exact P.not_dvd_index
  · intro hindex'
    have hcoreIndex :
        ¬ p ∣ (pCore p (G ⧸ pPrimeCore p G)).index := by
      rwa [← hindex]
    let P : Sylow p (G ⧸ pPrimeCore p G) :=
      pCore_isPGroup.toSylow hcoreIndex
    exact ⟨P, rfl⟩

/-- The intersection of `O_{p',p}(G)` with a subgroup `H` lies in
`O_{p',p}(H)`.  This is the two-step-core form of functoriality needed for
Lemma 1.21(a). -/
private theorem pPrimePCore_subgroupOf_le (H : Subgroup G) :
    (pPrimePCore p G).subgroupOf H ≤ pPrimePCore p H := by
  classical
  let O : Subgroup G := pPrimeCore p G
  let OH : Subgroup H := pPrimeCore p H
  let N : Subgroup G := pPrimePCore p G
  let I : Subgroup H := O.subgroupOf H
  let L : Subgroup H := N.subgroupOf H

  have hIcard : Nat.card I ∣ Nat.card O := by
    exact Subgroup.card_comap_dvd_of_injective O H.subtype
      H.subtype_injective
  have hIprime : IsPPrimeSubgroup p I := by
    rw [IsPPrimeSubgroup]
    exact (pPrimeCore_coprime_card (G := G) (p := p)).coprime_dvd_right
      hIcard
  have hIleOH : I ≤ OH := by
    apply le_pPrimeCore hIprime
    infer_instance

  let qI : H →* H ⧸ I := QuotientGroup.mk' I
  let qO : G →* G ⧸ O := QuotientGroup.mk' O
  let f : H →* G ⧸ O := qO.comp H.subtype
  have hIker : I = f.ker := by
    ext x
    change ((x : H) : G) ∈ O ↔ qO ((x : H) : G) = 1
    exact (QuotientGroup.eq_one_iff ((x : H) : G)).symm
  let e : (H ⧸ I) →* (G ⧸ O) :=
    QuotientGroup.lift I f hIker.le
  have he : Function.Injective e := by
    exact
      (QuotientGroup.injective_lift_iff I f hIker.le).mpr hIker

  have hLmap : L.map f ≤ pCore p (G ⧸ O) := by
    rintro y ⟨x, hx, rfl⟩
    change qO ((x : H) : G) ∈ pCore p (G ⧸ O)
    exact hx
  have hLmapE : (L.map qI).map e ≤ pCore p (G ⧸ O) := by
    rintro y ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    change e (qI x) ∈ pCore p (G ⧸ O)
    simpa [e, qI] using hLmap (Subgroup.mem_map_of_mem f hx)
  have hLqIp : IsPGroup p (L.map qI) := by
    have hpre : IsPGroup p ((pCore p (G ⧸ O)).comap e) :=
      pCore_isPGroup.comap_of_injective e he
    apply hpre.to_le
    exact Subgroup.map_le_iff_le_comap.mp hLmapE

  let qH : H →* H ⧸ OH := QuotientGroup.mk' OH
  have hIcomap : I ≤ OH.comap (MonoidHom.id H) := by
    simpa using hIleOH
  let d : (H ⧸ I) →* (H ⧸ OH) :=
    QuotientGroup.map I OH (MonoidHom.id H) hIcomap
  have hdcomp : d.comp qI = qH := by
    ext x
    rfl
  have hLqH : L.map qH = (L.map qI).map d := by
    rw [Subgroup.map_map, hdcomp]
  have hLqHp : IsPGroup p (L.map qH) := by
    rw [hLqH]
    exact hLqIp.map d
  have hLqHnormal : (L.map qH).Normal := by
    exact Subgroup.Normal.map (by infer_instance) qH
      (QuotientGroup.mk'_surjective OH)
  have hLqHcore : L.map qH ≤ pCore p (H ⧸ OH) :=
    le_pCore hLqHp hLqHnormal
  change L ≤ (pCore p (H ⧸ OH)).comap qH
  exact Subgroup.map_le_iff_le_comap.mp hLqHcore

/-- The index of the two-step core of a subgroup divides the index of the
ambient two-step core. -/
private theorem pPrimePCore_index_dvd (H : Subgroup G) :
    (pPrimePCore p H).index ∣ (pPrimePCore p G).index := by
  classical
  let N : Subgroup G := pPrimePCore p G
  let NH : Subgroup H := pPrimePCore p H
  let L : Subgroup H := N.subgroupOf H
  have hLNH : L ≤ NH := pPrimePCore_subgroupOf_le H
  have hNHdvdL : NH.index ∣ L.index :=
    Subgroup.index_dvd_of_le hLNH

  let qL : H →* H ⧸ L := QuotientGroup.mk' L
  let qN : G →* G ⧸ N := QuotientGroup.mk' N
  let f : H →* G ⧸ N := qN.comp H.subtype
  have hLker : L = f.ker := by
    ext x
    change ((x : H) : G) ∈ N ↔ qN ((x : H) : G) = 1
    exact (QuotientGroup.eq_one_iff ((x : H) : G)).symm
  let e : (H ⧸ L) →* (G ⧸ N) :=
    QuotientGroup.lift L f hLker.le
  have he : Function.Injective e := by
    exact
      (QuotientGroup.injective_lift_iff L f hLker.le).mpr hLker
  have hLdN : L.index ∣ N.index := by
    rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
    exact Subgroup.card_dvd_of_injective e he
  exact hNHdvdL.trans hLdN

/-- `BGsection1.v: plength1S`, Bender--Glauberman Lemma 1.21(a).

Subgroups of a group of p-length one again have p-length one. -/
theorem plength1S (H : Subgroup G) (hG : IsPLengthOne p G) :
    IsPLengthOne p H := by
  apply isPLengthOne_iff_not_dvd_pPrimePCore_index.mpr
  intro hpH
  exact isPLengthOne_iff_not_dvd_pPrimePCore_index.mp hG
    (hpH.trans (pPrimePCore_index_dvd H))

/-- A p-element in a finite group of order prime to `p` is trivial. -/
private theorem isPElement_eq_one_of_not_dvd_natCard
    {K : Type v} [Group K] [Finite K] {x : K}
    (hnot : ¬ p ∣ Nat.card K) (hx : IsPElement p x) : x = 1 := by
  obtain ⟨n, hn⟩ := hx
  have hcop : Nat.Coprime (p ^ n) (Nat.card K) :=
    ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hnot).pow_left n
  have hordPow : orderOf x ∣ p ^ n :=
    orderOf_dvd_iff_pow_eq_one.mpr hn
  have hordCard : orderOf x ∣ Nat.card K := orderOf_dvd_natCard x
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcop hordPow hordCard)

/-- If the two-step core is the whole group, the p'-core is a Hall
p'-subgroup. -/
private theorem pPrimeCore_isPrimeComplement_of_pPrimePCore_eq_top
    {K : Type v} [Group K] [Finite K]
    (htop : pPrimePCore p K = ⊤) :
    IsPrimeComplement p (pPrimeCore p K) := by
  let O : Subgroup K := pPrimeCore p K
  let q : K →* K ⧸ O := QuotientGroup.mk' O
  have hcoreTop : pCore p (K ⧸ O) = ⊤ := by
    calc
      pCore p (K ⧸ O) = (pPrimePCore p K).map q := by
        simpa [O, q] using
          (pPrimePCore_map_quotient_eq (p := p) (G := K)).symm
      _ = (⊤ : Subgroup K).map q := by rw [htop]
      _ = q.range := (MonoidHom.range_eq_map q).symm
      _ = ⊤ := q.range_eq_top.mpr (QuotientGroup.mk'_surjective O)
  have htopP : IsPGroup p (⊤ : Subgroup (K ⧸ O)) := by
    rw [← hcoreTop]
    exact pCore_isPGroup
  have hquotP : IsPGroup p (K ⧸ O) :=
    htopP.of_equiv Subgroup.topEquiv
  obtain ⟨n, hn⟩ := hquotP.exists_card_eq
  refine ⟨(pPrimeCore_coprime_card (G := K) (p := p)).symm,
    ⟨n, ?_⟩⟩
  rw [O.index_eq_card]
  exact hn

/-- `BGsection1.v: p_elt_gen_length1`, Bender--Glauberman Lemma 1.21(d).

A group has p-length one exactly when the p'-core of the subgroup generated
by its p-elements is a Hall p'-subgroup. -/
theorem p_elt_gen_length1 :
    IsPLengthOne p G ↔
      IsPrimeComplement p
        (pPrimeCore p (pElementGenerated p G)) := by
  classical
  let U : Subgroup G := pElementGenerated p G
  let N : Subgroup G := pPrimePCore p G
  constructor
  · intro hpl
    have hnotN : ¬ p ∣ Nat.card (G ⧸ N) := by
      have hindex := isPLengthOne_iff_not_dvd_pPrimePCore_index.mp hpl
      rwa [N.index_eq_card] at hindex
    let qN : G →* G ⧸ N := QuotientGroup.mk' N
    have hUN : U ≤ N := by
      change pElementGenerated p G ≤ N
      rw [pElementGenerated_le_iff]
      intro x hx
      apply (QuotientGroup.eq_one_iff x).mp
      exact isPElement_eq_one_of_not_dvd_natCard hnotN (hx.map qN)
    have hNsubTop : N.subgroupOf U = ⊤ :=
      Subgroup.subgroupOf_eq_top.mpr hUN
    have hNUTop : pPrimePCore p U = ⊤ := by
      apply top_unique
      rw [← hNsubTop]
      exact pPrimePCore_subgroupOf_le U
    exact pPrimeCore_isPrimeComplement_of_pPrimePCore_eq_top hNUTop
  · intro hHall
    let OU : Subgroup U := pPrimeCore p U
    obtain ⟨n, hn⟩ := hHall.exists_index_eq_pow
    have hUquotP : IsPGroup p (U ⧸ OU) := by
      apply IsPGroup.of_card (n := n)
      rw [← OU.index_eq_card, hn]

    let OUG : Subgroup G := OU.map U.subtype
    have hOUGprime : IsPPrimeSubgroup p OUG := by
      change Nat.Coprime p (Nat.card (OU.map U.subtype))
      rw [Subgroup.card_map_of_injective U.subtype_injective]
      exact pPrimeCore_coprime_card
    have hOUGnormal : OUG.Normal := by
      dsimp [OUG, OU, U]
      infer_instance
    have hOUGle : OUG ≤ pPrimeCore p G :=
      le_pPrimeCore hOUGprime hOUGnormal

    let O : Subgroup G := pPrimeCore p G
    let qO : G →* G ⧸ O := QuotientGroup.mk' O
    let f : U →* G ⧸ O := qO.comp U.subtype
    have hOUker : OU ≤ f.ker := by
      intro x hx
      apply (QuotientGroup.eq_one_iff ((x : U) : G)).mpr
      exact hOUGle (Subgroup.mem_map_of_mem U.subtype hx)
    let fbar : (U ⧸ OU) →* (G ⧸ O) :=
      QuotientGroup.lift OU f hOUker
    have hRangeP : IsPGroup p fbar.range := by
      rw [MonoidHom.range_eq_map]
      exact (hUquotP.to_subgroup ⊤).map fbar
    have hRange : fbar.range = U.map qO := by
      apply le_antisymm
      · rintro y ⟨z, rfl⟩
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective OU z
        exact ⟨(x : G), x.property, rfl⟩
      · rintro y ⟨x, hx, rfl⟩
        refine ⟨QuotientGroup.mk' OU ⟨x, hx⟩, ?_⟩
        rfl
    have hUmapP : IsPGroup p (U.map qO) := by
      rwa [← hRange]
    have hUmapNormal : (U.map qO).Normal := by
      exact Subgroup.Normal.map (by infer_instance) qO
        (QuotientGroup.mk'_surjective O)
    have hUmapCore : U.map qO ≤ pCore p (G ⧸ O) :=
      le_pCore hUmapP hUmapNormal
    have hUN : U ≤ N := by
      change U ≤ (pCore p (G ⧸ O)).comap qO
      exact Subgroup.map_le_iff_le_comap.mp hUmapCore

    let qN : G →* G ⧸ N := QuotientGroup.mk' N
    have hnotN : ¬ p ∣ Nat.card (G ⧸ N) := by
      intro hpCard
      obtain ⟨y, hyorder⟩ := exists_prime_orderOf_dvd_card' p hpCard
      have hyPElement : IsPElement p y := by
        refine ⟨1, ?_⟩
        simpa [hyorder] using pow_orderOf_eq_one y
      obtain ⟨P, g, hgP, hgy⟩ :=
        exists_sylow_preimage_of_isPElement qN
          (QuotientGroup.mk'_surjective N) hyPElement
      have hgPElement : IsPElement p g := by
        obtain ⟨k, hk⟩ := P.isPGroup' ⟨g, hgP⟩
        exact ⟨k, by simpa using congrArg Subtype.val hk⟩
      have hgU : g ∈ U := isPElement_subset_pElementGenerated hgPElement
      have hgN : g ∈ N := hUN hgU
      have hyOne : y = 1 := by
        exact hgy.symm.trans ((QuotientGroup.eq_one_iff g).mpr hgN)
      rw [hyOne, orderOf_one] at hyorder
      exact (Fact.out : p.Prime).ne_one hyorder.symm
    apply isPLengthOne_iff_not_dvd_pPrimePCore_index.mpr
    rwa [N.index_eq_card]

end Submission.OddOrder.BG.Section01
