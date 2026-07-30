import Submission.OddOrder.BG.Section04.RankTwoDerivedComplement
import Submission.OddOrder.MathlibSupport.ChiefFactorFaithfulPCore
import Submission.OddOrder.MathlibSupport.PPrimePCore
import Submission.OddOrder.MathlibSupport.SylowFunctorial

/-!
Bender--Glauberman Corollary 4.19 in the case where the `p'`-core of the
normal rank-two subgroup is trivial.
-/

namespace Submission.OddOrder.BG.Section04

open Submission.OddOrder.MathlibSupport

noncomputable section

universe u

/-- The core-free branch of `BGsection4.v: rank2_der1_cent_chief`.

The ambient `p`-core of `Gs` is Sylow by Theorem 4.18(e).  Theorem 4.17
makes the derived group of its conjugation image a `p`-group.  Passing to
the action on the chief factor preserves that conclusion, while the
faithful chief-factor quotient has trivial `p`-core. -/
theorem rank2_der1_cent_chief_of_pPrimeCore_eq_bot
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
    (hUGs : U ≤ Gs)
    (hcore : pPrimeCore p Gs = ⊥) :
    ⁅(_root_.commutator G), U⁆ ≤ V := by
  classical
  letI : IsSolvable G := hsol
  letI : Gs.Normal := hGs
  letI : IsSolvable Gs := by infer_instance
  have hoddGs : Odd (Nat.card Gs) := odd_natCard_subgroup Gs hodd

  have hquotPrime : IsPPrimeSubgroup p
      (⊤ : Subgroup (Gs ⧸ pPrimePCore p Gs)) :=
    (rank2_der1_complement
      (G := Gs) (p := p) (by infer_instance) hoddGs hRank).2.2
  have hnotDvdIndex : ¬ p ∣ (pCore p Gs).index := by
    rw [← pPrimePCore_eq_pCore_of_pPrimeCore_eq_bot hcore]
    rw [Subgroup.index_eq_card]
    rw [IsPPrimeSubgroup, Subgroup.card_top] at hquotPrime
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp hquotPrime
  let S : Sylow p Gs :=
    pCore_isPGroup.toSylow hnotDvdIndex

  let R : Subgroup G := (pCore p Gs).map Gs.subtype
  have hRnormal : R.Normal := by
    dsimp only [R]
    infer_instance
  letI : R.Normal := hRnormal
  have hRp : IsPGroup p R := pCore_isPGroup.map Gs.subtype
  have hRodd : Odd (Nat.card R) := odd_natCard_subgroup R hodd
  let eR : pCore p Gs ≃* R :=
    (pCore p Gs).equivMapOfInjective
      Gs.subtype Gs.subtype_injective
  let fR : R →* Gs :=
    (pCore p Gs).subtype.comp eR.symm.toMonoidHom
  have hfR : Function.Injective fR :=
    (pCore p Gs).subtype_injective.comp eR.symm.injective
  have hRrank : ¬ ∃ E : Subgroup R,
      IsElementaryAbelianOfRank p 3 E := by
    rintro ⟨E, hE⟩
    apply hRank
    exact ⟨E.map fR, hE.map_of_injective fR hfR⟩

  let normalizerHom : G →* Subgroup.normalizer (R : Set G) :=
    (MonoidHom.id G).codRestrict
      (Subgroup.normalizer (R : Set G)) fun g ↦ by
        rw [R.normalizer_eq_top]
        trivial
  let rhoR : G →* MulAut R :=
    R.normalizerMonoidHom.comp normalizerHom
  let A : Subgroup (MulAut R) := rhoR.range
  have hAsol : IsSolvable A :=
    solvable_of_surjective rhoR.rangeRestrict_surjective
  have hAodd : Odd (Nat.card A) :=
    hodd.of_dvd_nat (Subgroup.card_range_dvd rhoR)
  have hAderived : IsPGroup p (_root_.commutator A) :=
    der1_Aut_rank2_pgroup hRp hRodd hRrank A hAsol hAodd

  let QR := G ⧸ rhoR.ker
  let eQA : QR ≃* A :=
    QuotientGroup.quotientKerEquivRange rhoR
  let DR : Subgroup QR := _root_.commutator QR
  have hmapDR : DR.map eQA.toMonoidHom =
      _root_.commutator A := by
    calc
      DR.map eQA.toMonoidHom =
          ⁅eQA.toMonoidHom.range, eQA.toMonoidHom.range⁆ :=
        map_commutator_eq QR eQA.toMonoidHom
      _ = _root_.commutator A := by
        have hrange : eQA.toMonoidHom.range = ⊤ :=
          MonoidHom.range_eq_top.mpr eQA.surjective
        rw [hrange]
        exact (_root_.commutator_def A).symm
  let eDR : DR ≃* _root_.commutator A :=
    (DR.equivMapOfInjective
      eQA.toMonoidHom eQA.injective).trans
        (MulEquiv.subgroupCongr hmapDR)
  have hDRp : IsPGroup p DR := hAderived.of_equiv eDR.symm

  let qV : G →* G ⧸ V := QuotientGroup.mk' V
  let GsQ : Subgroup (G ⧸ V) := Gs.map qV
  let fGs : Gs →* GsQ := qV.subgroupMap Gs
  have hfGs : Function.Surjective fGs :=
    qV.subgroupMap_surjective Gs
  let SQ : Sylow p GsQ := S.mapSurjective hfGs
  have hUQGsQ : U.map qV ≤ GsQ := Subgroup.map_mono hUGs
  let UQ : Subgroup GsQ := (U.map qV).subgroupOf GsQ
  have hUQp : IsPGroup p UQ :=
    hfactor.of_equiv
      (Subgroup.subgroupOfEquivOfLe hUQGsQ).symm
  have hUQnormal : UQ.Normal := by
    dsimp only [UQ, GsQ]
    letI : (U.map qV).Normal :=
      hchief.upper_normal.map qV
        (QuotientGroup.mk'_surjective V)
    infer_instance
  letI : UQ.Normal := hUQnormal
  have hUQSQ : UQ ≤ (SQ : Subgroup GsQ) :=
    hUQp.le_sylow_of_normal SQ
  have hUQR : U.map qV ≤ R.map qV := by
    intro x hx
    let xQ : GsQ := ⟨x, hUQGsQ hx⟩
    have hxUQ : xQ ∈ UQ := hx
    have hxSQ := hUQSQ hxUQ
    change xQ ∈ (S : Subgroup Gs).map fGs at hxSQ
    rcases hxSQ with ⟨r, hr, hrx⟩
    refine ⟨(r : G), ⟨r, hr, rfl⟩, ?_⟩
    exact congrArg Subtype.val hrx

  let rhoU : G →* MulAut (U ⧸ V.subgroupOf U) :=
    chiefFactorConjugationHom hchief
  let eU : (U ⧸ V.subgroupOf U) ≃* U.map qV :=
    QuotientGroup.liftEquiv (V.subgroupOf U)
      (qV.subgroupMap_surjective U) (by
        rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk'])
  have hkerRU : rhoR.ker ≤ rhoU.ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    apply MulEquiv.ext
    intro x
    obtain ⟨u, rfl⟩ :=
      QuotientGroup.mk'_surjective (V.subgroupOf U) x
    apply eU.injective
    apply Subtype.ext
    change qV (g * (u : G) * g⁻¹) = qV (u : G)
    have huQ : qV (u : G) ∈ U.map qV :=
      Subgroup.mem_map_of_mem qV u.property
    obtain ⟨r, hrR, hru⟩ := hUQR huQ
    let rR : R := ⟨r, hrR⟩
    have hfix := DFunLike.congr_fun
      (MonoidHom.mem_ker.mp hg) rR
    have hgr : g * r * g⁻¹ = r := by
      exact congrArg Subtype.val hfix
    calc
      qV (g * (u : G) * g⁻¹) =
          qV g * qV (u : G) * (qV g)⁻¹ := by simp
      _ = qV g * qV r * (qV g)⁻¹ := by rw [← hru]
      _ = qV (g * r * g⁻¹) := by simp
      _ = qV r := by rw [hgr]
      _ = qV (u : G) := hru

  let QU := G ⧸ rhoU.ker
  have hkerMk : rhoR.ker ≤
      (QuotientGroup.mk' rhoU.ker).ker := by
    rw [QuotientGroup.ker_mk']
    exact hkerRU
  let qRU : QR →* QU :=
    QuotientGroup.lift rhoR.ker
      (QuotientGroup.mk' rhoU.ker) hkerMk
  have hqRU : Function.Surjective qRU :=
    QuotientGroup.lift_surjective_of_surjective
      rhoR.ker (QuotientGroup.mk' rhoU.ker)
      (QuotientGroup.mk'_surjective rhoU.ker) hkerMk
  have hmapDerived : DR.map qRU =
      _root_.commutator QU := by
    calc
      DR.map qRU = ⁅qRU.range, qRU.range⁆ :=
        map_commutator_eq QR qRU
      _ = _root_.commutator QU := by
        rw [MonoidHom.range_eq_top.mpr hqRU]
        exact (_root_.commutator_def QU).symm
  have hDUp : IsPGroup p (_root_.commutator QU) := by
    rw [← hmapDerived]
    exact hDRp.map qRU
  have hQUcore : pCore p QU = ⊥ := by
    exact pCore_quotient_ker_chiefFactorConjugationHom_eq_bot
      hchief hfactor
  have hDUbot : _root_.commutator QU = ⊥ := by
    apply le_bot_iff.mp
    rw [← hQUcore]
    exact le_pCore hDUp (by infer_instance)
  have hmapGderived :
      (_root_.commutator G).map
          (QuotientGroup.mk' rhoU.ker) = ⊥ := by
    rw [map_commutator_eq,
      MonoidHom.range_eq_top.mpr
        (QuotientGroup.mk'_surjective rhoU.ker)]
    exact hDUbot
  have hderivedKer : _root_.commutator G ≤ rhoU.ker := by
    have := (Subgroup.map_eq_bot_iff
      (_root_.commutator G)).mp hmapGderived
    simpa [QuotientGroup.ker_mk'] using this
  exact
    (commutator_le_ker_chiefFactorConjugationHom_iff hchief).mp
      hderivedKer

end

end Submission.OddOrder.BG.Section04
