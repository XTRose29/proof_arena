import Submission.OddOrder.BG.Section04.RankTwoAutomorphismDerived
import Submission.OddOrder.MathlibSupport.FittingPCore
import Submission.OddOrder.MathlibSupport.PCoreSelfQuotient
import Submission.OddOrder.MathlibSupport.PGroupMapKernel
import Submission.OddOrder.MathlibSupport.PPrimeCoreDerivedHall
import Submission.OddOrder.MathlibSupport.PPrimeCoreQuotient
import Submission.OddOrder.MathlibSupport.PPrimePCoreQuotient
import Submission.OddOrder.MathlibSupport.PPrimePCoreThirdIsomorphism
import Submission.OddOrder.MathlibSupport.PPrimeQuotientElementaryAbelian

/-!
Bender--Glauberman Theorem 4.18(c,e).

After removing the `p'`-core, conjugation on the `p`-core detects the
derived subgroup.  Theorem 4.17 makes the derived image a `p`-group, while
the self-centralizing property of the Fitting subgroup makes the kernel a
`p`-group.  This gives the derived Hall complement and the two conclusions
after quotienting by `O_{p',p}`.
-/

namespace Submission.OddOrder.BG.Section04

open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative

noncomputable section

universe u

/-- `BGsection4.v: rank2_der1_complement` and its `O_{p',p}` quotient
consequences (Bender--Glauberman Theorem 4.18(c,e)). -/
theorem rank2_der1_complement
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (hsol : IsSolvable G)
    (hodd : Odd (Nat.card G))
    (hRank : ¬ ∃ E : Subgroup G,
      IsElementaryAbelianOfRank p 3 E) :
    IsPrimeComplement p
        (pPrimeCore p (_root_.commutator G)) ∧
      IsMulCommutative (G ⧸ pPrimePCore p G) ∧
      IsPPrimeSubgroup p
        (⊤ : Subgroup (G ⧸ pPrimePCore p G)) := by
  classical
  let O : Subgroup G := pPrimeCore p G
  let Q := G ⧸ O
  letI : IsSolvable G := hsol
  letI : IsSolvable Q := isSolvable_quotient_of_isSolvable O
  have hQodd : Odd (Nat.card Q) := odd_natCard_quotient O hodd
  have hQrank :
      ¬ ∃ E : Subgroup Q, IsElementaryAbelianOfRank p 3 E := by
    simpa [Q, O] using
      (no_elementaryAbelian_rank_three_quotient_pPrimeCore
        (G := G) (p := p) hsol hRank)
  let R : Subgroup Q := pCore p Q
  have hRp : IsPGroup p R := pCore_isPGroup
  have hRodd : Odd (Nat.card R) := odd_natCard_subgroup R hQodd
  have hRrank :
      ¬ ∃ E : Subgroup R, IsElementaryAbelianOfRank p 3 E := by
    rintro ⟨E, hE⟩
    apply hQrank
    exact ⟨E.map R.subtype,
      hE.map_of_injective R.subtype R.subtype_injective⟩
  let i : Q →* Subgroup.normalizer (R : Set Q) :=
    { toFun := fun x ↦ ⟨x, by
        rw [R.normalizer_eq_top]
        trivial⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  let rho : Q →* MulAut R := R.normalizerMonoidHom.comp i
  let A : Subgroup (MulAut R) := rho.range
  have hAsol : IsSolvable A :=
    solvable_of_surjective rho.rangeRestrict_surjective
  have hAodd : Odd (Nat.card A) :=
    hQodd.of_dvd_nat (Subgroup.card_range_dvd rho)
  have hAderived : IsPGroup p (_root_.commutator A) :=
    der1_Aut_rank2_pgroup hRp hRodd hRrank A hAsol hAodd
  let C : Subgroup Q := Subgroup.centralizer (R : Set Q)
  have hrhoKer : rho.ker = C := by
    ext x
    change i x ∈ R.normalizerMonoidHom.ker ↔
      x ∈ Subgroup.centralizer (R : Set Q)
    rw [Subgroup.normalizerMonoidHom_ker]
    rfl
  have hQcore : pPrimeCore p Q = ⊥ := by
    simpa [Q, O] using
      (pPrimeCore_quotient_self_eq_bot (G := G) (p := p))
  have hCgroup : IsPGroup p C := by
    dsimp only [C, R]
    exact centralizer_pCore_isPGroup_of_pPrimeCore_eq_bot hQcore
  have hrhoKerP : IsPGroup p rho.ker := by
    rw [hrhoKer]
    exact hCgroup
  let DQ : Subgroup Q := _root_.commutator Q
  have hmapDQ : DQ.map rho =
      (_root_.commutator A).map A.subtype := by
    calc
      DQ.map rho = ⁅rho.range, rho.range⁆ := map_commutator_eq Q rho
      _ = (_root_.commutator A).map A.subtype := by
        simpa [A] using (Subgroup.map_subtype_commutator A).symm
  have hmapDQP : IsPGroup p (DQ.map rho) := by
    rw [hmapDQ]
    exact hAderived.of_equiv
      ((_root_.commutator A).equivMapOfInjective
        A.subtype A.subtype_injective)
  have hrestrictKerP : IsPGroup p (rho.restrict DQ).ker := by
    let j : (rho.restrict DQ).ker →* rho.ker :=
      { toFun := fun x ↦ ⟨((x : DQ) : Q), x.property⟩
        map_one' := rfl
        map_mul' := fun _ _ ↦ rfl }
    exact hrhoKerP.of_injective j (by
      intro x y hxy
      have hxyQ : ((x : DQ) : Q) = ((y : DQ) : Q) :=
        congrArg (fun z : rho.ker ↦ (z : Q)) hxy
      apply Subtype.ext
      apply Subtype.ext
      exact hxyQ)
  have hDQp : IsPGroup p (_root_.commutator Q) := by
    change IsPGroup p DQ
    exact isPGroup_of_map_and_restrict_ker DQ rho hmapDQP hrestrictKerP
  have hHall : IsPrimeComplement p
      (pPrimeCore p (_root_.commutator G)) := by
    apply pPrimeCore_commutator_isPrimeComplement_of_quotient
      (N := O)
    · exact pPrimeCore_isNormalPPrime.1
    · simpa [Q, O] using hDQp
  have hmapDerived :
      (_root_.commutator G).map (QuotientGroup.mk' O) =
        _root_.commutator Q := by
    dsimp only [Q]
    rw [map_commutator_eq,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective O)]
    rfl
  have hDerivedLe :
      _root_.commutator G ≤ pPrimePCore p G := by
    change _root_.commutator G ≤
      (pCore p Q).comap (QuotientGroup.mk' O)
    rw [← Subgroup.map_le_iff_le_comap, hmapDerived]
    exact le_pCore hDQp (by infer_instance)
  have hquotComm : IsMulCommutative (G ⧸ pPrimePCore p G) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hDerivedLe
  have hDQleR : _root_.commutator Q ≤ R := by
    dsimp only [R]
    exact le_pCore hDQp (by infer_instance)
  letI : IsMulCommutative (Q ⧸ R) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hDQleR
  have hnotDvdQR : ¬ p ∣ Nat.card (Q ⧸ R) := by
    dsimp only [R]
    exact not_dvd_natCard_quotient_pCore_of_isNilpotent
  let e : (Q ⧸ R) ≃* (G ⧸ pPrimePCore p G) := by
    simpa [Q, O, R] using pPrimePCoreQuotientEquiv p G
  have hnotDvdFinal : ¬ p ∣ Nat.card (G ⧸ pPrimePCore p G) := by
    rw [← Nat.card_congr e.toEquiv]
    exact hnotDvdQR
  refine ⟨hHall, hquotComm, ?_⟩
  rw [IsPPrimeSubgroup, Subgroup.card_top]
  exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hnotDvdFinal

end

end Submission.OddOrder.BG.Section04
