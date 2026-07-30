import Submission.OddOrder.BG.Section04.RankTwoChiefFactorCoreFree
import Submission.OddOrder.MathlibSupport.ChiefFactorQuotient
import Submission.OddOrder.MathlibSupport.PPrimeCoreFunctorial
import Submission.OddOrder.MathlibSupport.PPrimeFactorIntersection
import Submission.OddOrder.MathlibSupport.PPrimeQuotientElementaryAbelian

/-!
Bender--Glauberman Corollary 4.19.

The proof first removes the `p'`-core of the normal rank-two subgroup.
The preceding core-free theorem applies in the quotient, and the resulting
mixed-commutator containment lifts through the quotient because the kernel
meets the upper group of the chief factor inside its lower group.
-/

namespace Submission.OddOrder.BG.Section04

open Submission.OddOrder.MathlibSupport

noncomputable section

universe u

private theorem quotient_chief_factor_lift_commutator
    {G : Type u} [Group G] [Finite G]
    {K V U : Subgroup G} [K.Normal] [V.Normal]
    (hchief : IsChiefFactor V U)
    (hKU : K ⊓ U ≤ V)
    (hqcomm :
      ⁅(_root_.commutator (G ⧸ K)), U.map (QuotientGroup.mk' K)⁆ ≤
        V.map (QuotientGroup.mk' K)) :
    ⁅(_root_.commutator G), U⁆ ≤ V := by
  letI : U.Normal := hchief.upper_normal
  let q : G →* G ⧸ K := QuotientGroup.mk' K
  have hmapD :
      (_root_.commutator G).map q =
        _root_.commutator (G ⧸ K) := by
    rw [map_commutator_eq,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective K)]
    rfl
  have hmapMixed :
      ⁅(_root_.commutator G), U⁆.map q =
        ⁅(_root_.commutator (G ⧸ K)), U.map q⁆ := by
    rw [Subgroup.map_commutator, hmapD]
  have hpre :
      ⁅(_root_.commutator G), U⁆ ≤ (V.map q).comap q := by
    rw [← Subgroup.map_le_iff_le_comap, hmapMixed]
    exact hqcomm
  have hmixedU : ⁅(_root_.commutator G), U⁆ ≤ U :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp
      (show _root_.commutator G ≤ Subgroup.normalizer (U : Set G) by
        rw [U.normalizer_eq_top]
        exact le_top)
  intro x hx
  have hxU : x ∈ U := hmixedU hx
  have hxSup : x ∈ V ⊔ K := by
    have := hpre hx
    simpa [q, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] using this
  obtain ⟨v, hvV, k, hkK, hvkx⟩ :=
    Subgroup.mem_sup_of_normal_right.mp hxSup
  have hvU : v ∈ U := hchief.le hvV
  have hkU : k ∈ U := by
    have hvinvU : v⁻¹ ∈ U := U.inv_mem hvU
    have hvxU : v⁻¹ * x ∈ U := U.mul_mem hvinvU hxU
    have hvx : v⁻¹ * x = k := by
      rw [← hvkx]
      exact inv_mul_cancel_left v k
    rw [← hvx]
    exact hvxU
  have hkV : k ∈ V := hKU ⟨hkK, hkU⟩
  rw [← hvkx]
  exact V.mul_mem hvV hkV

private theorem quotient_pPrimeCore_map_rank
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (Gs : Subgroup G) [Gs.Normal]
    (hsol : IsSolvable Gs)
    (hRank : ¬ ∃ E : Subgroup Gs,
      IsElementaryAbelianOfRank p 3 E) :
    let K : Subgroup G := (pPrimeCore p Gs).map Gs.subtype
    let q : G →* G ⧸ K := QuotientGroup.mk' K
    let GsQ : Subgroup (G ⧸ K) := Gs.map q
    ¬ ∃ E : Subgroup GsQ,
      IsElementaryAbelianOfRank p 3 E := by
  classical
  dsimp only
  let K : Subgroup G := (pPrimeCore p Gs).map Gs.subtype
  letI : K.Normal := by
    dsimp [K]
    infer_instance
  let q : G →* G ⧸ K := QuotientGroup.mk' K
  let GsQ : Subgroup (G ⧸ K) := Gs.map q
  have hKsub : K.subgroupOf Gs = pPrimeCore p Gs := by
    change K.comap Gs.subtype = pPrimeCore p Gs
    dsimp [K]
    exact Subgroup.comap_map_eq_self_of_injective
      Gs.subtype_injective (pPrimeCore p Gs)
  let e₀ : (Gs ⧸ K.subgroupOf Gs) ≃* GsQ :=
    QuotientGroup.liftEquiv (K.subgroupOf Gs)
      (q.subgroupMap_surjective Gs) (by
        rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk'])
  let e : (Gs ⧸ pPrimeCore p Gs) ≃* GsQ :=
    (QuotientGroup.quotientMulEquivOfEq hKsub.symm).trans e₀
  have hquotRank :=
    no_elementaryAbelian_rank_three_quotient_pPrimeCore
      (G := Gs) (p := p) hsol hRank
  rintro ⟨E, hE⟩
  apply hquotRank
  exact ⟨E.map e.symm.toMonoidHom,
    hE.map_of_injective e.symm.toMonoidHom e.symm.injective⟩

private theorem quotient_pPrimeCore_map_core
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (Gs : Subgroup G) [Gs.Normal] :
    let K : Subgroup G := (pPrimeCore p Gs).map Gs.subtype
    let q : G →* G ⧸ K := QuotientGroup.mk' K
    let GsQ : Subgroup (G ⧸ K) := Gs.map q
    pPrimeCore p GsQ = ⊥ := by
  classical
  dsimp only
  let K : Subgroup G := (pPrimeCore p Gs).map Gs.subtype
  letI : K.Normal := by
    dsimp [K]
    infer_instance
  let q : G →* G ⧸ K := QuotientGroup.mk' K
  let GsQ : Subgroup (G ⧸ K) := Gs.map q
  have hKsub : K.subgroupOf Gs = pPrimeCore p Gs := by
    change K.comap Gs.subtype = pPrimeCore p Gs
    dsimp [K]
    exact Subgroup.comap_map_eq_self_of_injective
      Gs.subtype_injective (pPrimeCore p Gs)
  let e₀ : (Gs ⧸ K.subgroupOf Gs) ≃* GsQ :=
    QuotientGroup.liftEquiv (K.subgroupOf Gs)
      (q.subgroupMap_surjective Gs) (by
        rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk'])
  let e : (Gs ⧸ pPrimeCore p Gs) ≃* GsQ :=
    (QuotientGroup.quotientMulEquivOfEq hKsub.symm).trans e₀
  have hmap := map_pPrimeCore_eq_mulEquiv (p := p) e
  rw [pPrimeCore_quotient_self_eq_bot, Subgroup.map_bot] at hmap
  exact hmap.symm

/-- `BGsection4.v: rank2_der1_cent_chief` (Corollary 4.19).

If a normal subgroup has no elementary-abelian subgroup of rank three at
`p`, then the derived group centralizes every chief `p`-factor contained
in that subgroup. -/
theorem rank2_der1_cent_chief
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    {Gs U V : Subgroup G} [V.Normal]
    (hodd : Odd (Nat.card G))
    (hsol : IsSolvable G)
    (hGs : Gs.Normal)
    (hRank : ¬ ∃ E : Subgroup Gs,
      IsElementaryAbelianOfRank p 3 E)
    (hchief : IsChiefFactor V U)
    (hfactor : IsPGroup p
      (U.map (QuotientGroup.mk' V)))
    (hUGs : U ≤ Gs) :
    ⁅(_root_.commutator G), U⁆ ≤ V := by
  classical
  letI : IsSolvable G := hsol
  letI : Gs.Normal := hGs
  letI : IsSolvable Gs := by infer_instance
  let K : Subgroup G := (pPrimeCore p Gs).map Gs.subtype
  letI : K.Normal := by
    dsimp [K]
    infer_instance
  let q : G →* G ⧸ K := QuotientGroup.mk' K
  let Q := G ⧸ K
  let GsQ : Subgroup Q := Gs.map q
  let UQ : Subgroup Q := U.map q
  let VQ : Subgroup Q := V.map q
  letI : IsSolvable Q := isSolvable_quotient_of_isSolvable K
  have hQodd : Odd (Nat.card Q) :=
    odd_natCard_quotient K hodd
  have hGsQnormal : GsQ.Normal := by
    dsimp only [GsQ]
    exact Subgroup.Normal.map hGs q
      (QuotientGroup.mk'_surjective K)
  letI : GsQ.Normal := hGsQnormal
  have hVQnormal : VQ.Normal := by
    dsimp only [VQ]
    exact Subgroup.Normal.map (by infer_instance) q
      (QuotientGroup.mk'_surjective K)
  letI : VQ.Normal := hVQnormal
  have hKprime : IsPPrimeSubgroup p K := by
    rw [IsPPrimeSubgroup]
    exact (pPrimeCore_coprime_card (G := Gs) (p := p)).coprime_dvd_right
      (Subgroup.card_map_dvd (pPrimeCore p Gs) Gs.subtype)
  have hKU : K ⊓ U ≤ V :=
    inf_le_of_isPPrimeSubgroup_of_factor_isPGroup hKprime hfactor
  have hQrank : ¬ ∃ E : Subgroup GsQ,
      IsElementaryAbelianOfRank p 3 E := by
    simpa [K, q, Q, GsQ] using
      (quotient_pPrimeCore_map_rank Gs
        (hsol := (by infer_instance)) hRank)
  have hQchief : IsChiefFactor VQ UQ := by
    simpa [VQ, UQ] using hchief.map_quotient_of_inf_le hKU
  have hQfactor : IsPGroup p
      (UQ.map (QuotientGroup.mk' VQ)) := by
    simpa [UQ, VQ] using
      (isPGroup_map_quotient_factor_iff hchief.le hKU).mpr hfactor
  have hUQGsQ : UQ ≤ GsQ := by
    dsimp only [UQ, GsQ]
    exact Subgroup.map_mono hUGs
  have hQcore : pPrimeCore p GsQ = ⊥ := by
    simpa [K, q, Q, GsQ] using
      (quotient_pPrimeCore_map_core (p := p) Gs)
  have hQmixed :
      ⁅(_root_.commutator Q), UQ⁆ ≤ VQ :=
    rank2_der1_cent_chief_of_pPrimeCore_eq_bot
      (G := Q) (p := p) (Gs := GsQ) (U := UQ) (V := VQ)
      hQodd (by infer_instance) hGsQnormal hQrank
      hQchief hQfactor hUQGsQ hQcore
  exact quotient_chief_factor_lift_commutator
    hchief hKU (by simpa [Q, UQ, VQ] using hQmixed)

end

end Submission.OddOrder.BG.Section04
