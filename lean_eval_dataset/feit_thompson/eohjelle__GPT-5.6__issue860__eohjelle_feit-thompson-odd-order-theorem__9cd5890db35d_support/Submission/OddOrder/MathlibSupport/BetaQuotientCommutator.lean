import Submission.OddOrder.BG.Section10.BetaHallStructure
import Submission.OddOrder.MathlibSupport.CoprimeSolvableCentralProduct
import Submission.OddOrder.MathlibSupport.PPrimeFactorIntersection

/-!
# A beta-quotient commutator adapter

This packages the quotient argument in `BGsection13.v`, lines 674--689.
If a `q`-subgroup `Q` of two maximal subgroups acts as the normalized
fixed-point-free part of a coprime action, then commutators of `Q` with a
subgroup of the beta core of the first maximal subgroup lie in the beta
core of the second.

The proof pulls the `q`-core of `L' / beta(L)` back to `L`.  Nilpotence of
that quotient comes from `Mbeta_quo_nil`.  The pulled-back subgroup is
normal, so it contains the relevant commutator; its intersection with
`beta(M)` is forced into `beta(L)` because `q` does not belong to
`betaPrimes M`.
-/

namespace Submission.OddOrder.MathlibSupport

open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section10
open scoped commutatorElement

noncomputable section

universe u

/-- The quotient of a subgroup by the restriction of an ambient normal
subgroup is canonically the subgroup's image in the ambient quotient. -/
private def subgroupQuotientEquivImage
    {K : Type u} [Group K] (B D : Subgroup K) [B.Normal] :
    (D ⧸ B.subgroupOf D) ≃* D.map (QuotientGroup.mk' B) := by
  letI : (B.subgroupOf D).Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : B.Normal) D
  exact QuotientGroup.liftEquiv (B.subgroupOf D)
    ((QuotientGroup.mk' B).subgroupMap_surjective D) (by
      rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk'])

/-- The beta-quotient commutator step of `BGsection13.v`, lines 674--689.

The rank-one and Sylow hypotheses used at the call site are deliberately
reduced here to the two prime-power hypotheses actually needed by the
argument. -/
theorem commutator_le_betaCore_of_coprime_regular_action
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M L X P Q : Subgroup G} {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime]
    (hM : M ∈ minSimple_max_groups (G := G))
    (hL : L ∈ minSimple_max_groups (G := G))
    (hpq : p ≠ q)
    (hPp : IsPGroup p P)
    (hQq : IsPGroup q Q)
    (hXbeta : X ≤ betaCore M)
    (hXL : X ≤ L)
    (hQML : Q ≤ M ⊓ L)
    (hPL : P ≤ L)
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hcent : centralizerWithin Q P = ⊥)
    (hqNotBeta : q ∉ betaPrimes M) :
    ⁅X, Q⁆ ≤ betaCore L := by
  classical
  have hQM : Q ≤ M := hQML.trans inf_le_left
  have hQL : Q ≤ L := hQML.trans inf_le_right

  /- Fixed-point-free coprime action gives `Q ≤ [P,Q]`, hence
  `Q ≤ L'`. -/
  have hcopQP : (Nat.card Q).Coprime (Nat.card P) :=
    IsPGroup.coprime_card_of_ne q p hpq.symm Q P hQq hPp
  letI : Group.IsNilpotent Q := hQq.isNilpotent
  have hQcomm : Q ≤ ⁅P, Q⁆ := by
    have hdecomp : Q ≤ ⁅P, Q⁆ ⊔ centralizerWithin Q P :=
      le_commutator_sup_centralizerWithin_of_coprime hPQ hcopQP
    simpa [hcent] using hdecomp
  let D : Subgroup L := _root_.commutator L
  have hQderG : Q ≤ D.map L.subtype := by
    rw [show D.map L.subtype = ⁅L, L⁆ by
      exact L.map_subtype_commutator]
    exact hQcomm.trans (Subgroup.commutator_mono hPL hQL)

  /- Work in `L / beta(L)`.  Its derived subgroup is the image of `D`,
  and `Mbeta_quo_nil` makes that image nilpotent. -/
  let B : Subgroup L := (betaCore L).subgroupOf L
  let pi : L →* L ⧸ B := QuotientGroup.mk' B
  have hBnormal : B.Normal := by
    simpa [B] using betaCore_normal L
  letI : B.Normal := hBnormal
  let Dbar : Subgroup (L ⧸ B) := D.map pi
  letI : Dbar.Normal := by
    dsimp [Dbar, pi, D]
    exact Subgroup.Normal.map
      (inferInstance : (_root_.commutator L).Normal)
      (QuotientGroup.mk' B) (QuotientGroup.mk'_surjective B)
  letI : Group.IsNilpotent Dbar := by
    letI : Group.IsNilpotent (D ⧸ B.subgroupOf D) := by
      simpa [D, B] using Mbeta_quo_nil hL
    simpa [Dbar, pi] using
      Group.nilpotent_of_mulEquiv (subgroupQuotientEquivImage B D)

  /- Pull the `q`-core of the nilpotent derived image back to `L`. -/
  let R : Subgroup (L ⧸ B) := (pCore q Dbar).map Dbar.subtype
  have hRnormal : R.Normal := by
    dsimp [R]
    infer_instance
  have hRq : IsPGroup q R := by
    dsimp [R]
    exact pCore_isPGroup.map Dbar.subtype
  let U : Subgroup L := R.comap pi
  have hUnormal : U.Normal := hRnormal.comap pi
  letI : U.Normal := hUnormal

  let QL : Subgroup L := Q.subgroupOf L
  have hQLq : IsPGroup q QL :=
    hQq.of_equiv (Subgroup.subgroupOfEquivOfLe hQL).symm
  have hQLD : QL ≤ D := by
    intro x hx
    have hxD : (x : G) ∈ D.map L.subtype := hQderG hx
    obtain ⟨d, hd, hdx⟩ := hxD
    have hdx' : d = x := L.subtype_injective hdx
    simpa [hdx'] using hd
  have hQLmapDbar : QL.map pi ≤ Dbar := by
    change QL.map pi ≤ D.map pi
    exact Subgroup.map_mono hQLD
  let QD : Subgroup Dbar := (QL.map pi).subgroupOf Dbar
  have hQDq : IsPGroup q QD :=
    (hQLq.map pi).of_equiv
      (Subgroup.subgroupOfEquivOfLe hQLmapDbar).symm
  have hQDcore : QD ≤ pCore q Dbar :=
    IsPGroup.le_pCore_of_isNilpotent hQDq
  have hQLmapR : QL.map pi ≤ R := by
    calc
      QL.map pi = QD.map Dbar.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hQLmapDbar).symm
      _ ≤ (pCore q Dbar).map Dbar.subtype :=
        Subgroup.map_mono hQDcore
      _ = R := rfl
  have hQLU : QL ≤ U := by
    change QL ≤ R.comap pi
    exact Subgroup.map_le_iff_le_comap.mp hQLmapR

  /- Represent the desired commutator intrinsically in `L`. -/
  let XL : Subgroup L := X.subgroupOf L
  have hcommMapL : ⁅XL, QL⁆.map L.subtype = ⁅X, Q⁆ := by
    rw [Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le hXL,
      Subgroup.map_subgroupOf_eq_of_le hQL]
  have hcommU : ⁅XL, QL⁆ ≤ U :=
    (Subgroup.commutator_mono le_top hQLU).trans
      (Subgroup.commutator_le_right (⊤ : Subgroup L) U)

  /- Normality of `beta(M)` inside `M` gives the other containment. -/
  let BM : Subgroup M := (betaCore M).subgroupOf M
  let XM : Subgroup M := X.subgroupOf M
  let QM : Subgroup M := Q.subgroupOf M
  have hXMbeta : XM ≤ BM :=
    Subgroup.subgroupOf_mono M hXbeta
  have hcommMapM : ⁅XM, QM⁆.map M.subtype = ⁅X, Q⁆ := by
    rw [Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le
        (hXbeta.trans (betaCore_le M)),
      Subgroup.map_subgroupOf_eq_of_le hQM]
  have hBMnormal : BM.Normal := by
    simpa [BM] using betaCore_normal M
  letI : BM.Normal := hBMnormal
  have hcommBM : ⁅XM, QM⁆ ≤ BM :=
    (Subgroup.commutator_mono hXMbeta le_top).trans
      (Subgroup.commutator_le_left BM (⊤ : Subgroup M))
  have hcommBetaM : ⁅X, Q⁆ ≤ betaCore M := by
    rw [← hcommMapM,
      ← Subgroup.map_subgroupOf_eq_of_le (betaCore_le M)]
    exact Subgroup.map_mono hcommBM

  /- The intrinsic intersection `beta(M) ∩ U` inside `L` is contained
  in `beta(L)`: its first factor is a `q'`-group and the quotient image of
  its second factor is a `q`-group. -/
  let KM : Subgroup L := (betaCore M).subgroupOf L
  have hKMmap : KM.map L.subtype ≤ betaCore M := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  have hKMpi : IsPiNumber (betaPrimes M) (Nat.card KM) := by
    rw [← Subgroup.card_map_of_injective L.subtype_injective]
    exact (Mbeta_Hall_G hM).isPiNumber_card.of_dvd
      (Subgroup.card_dvd_of_le hKMmap)
  have hKMprime : IsPPrimeSubgroup q KM := by
    rw [IsPPrimeSubgroup]
    exact (Fact.out : q.Prime).coprime_iff_not_dvd.mpr fun hqKM ↦
      hqNotBeta (hKMpi Fact.out hqKM)
  have hfactorU : IsPGroup q (U.map (QuotientGroup.mk' B)) := by
    change IsPGroup q ((R.comap pi).map pi)
    rw [Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective B) R]
    exact hRq
  have hKMinfU : KM ⊓ U ≤ B :=
    inf_le_of_isPPrimeSubgroup_of_factor_isPGroup
      hKMprime hfactorU

  have hcommKM : ⁅XL, QL⁆ ≤ KM := by
    intro z hz
    change (z : G) ∈ betaCore M
    apply hcommBetaM
    rw [← hcommMapL]
    exact Subgroup.mem_map_of_mem L.subtype hz
  have hcommB : ⁅XL, QL⁆ ≤ B :=
    (le_inf hcommKM hcommU).trans hKMinfU
  rw [← hcommMapL,
    ← Subgroup.map_subgroupOf_eq_of_le (betaCore_le L)]
  exact Subgroup.map_mono hcommB

end

end Submission.OddOrder.MathlibSupport
