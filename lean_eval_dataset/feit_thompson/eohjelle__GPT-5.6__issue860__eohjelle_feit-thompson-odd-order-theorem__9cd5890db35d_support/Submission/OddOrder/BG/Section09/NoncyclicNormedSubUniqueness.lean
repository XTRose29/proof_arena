import Submission.OddOrder.BG.Section04.RankTwoFittingDerived
import Submission.OddOrder.BG.Section08.FittingUniqueness
import Submission.OddOrder.BG.Section09.ExtremalPOverlap
import Submission.OddOrder.BG.Section09.SylowNormalizerContainment
import Submission.OddOrder.MathlibSupport.FittingSylowFrattini
import Submission.OddOrder.MathlibSupport.FittingSylowPrimeComplement
import Submission.OddOrder.MathlibSupport.SylowIntersectionNormalizer

/-!
# Bender--Glauberman Theorem 9.1(b)

A noncyclic elementary-abelian subgroup `B` of a maximal subgroup `M` has
`M` as its unique maximal overgroup when every ambient `p'`-subgroup
normalized by `B` is forced into `M`.
-/

namespace Submission.OddOrder.BG.Section09

open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section08
open Submission.OddOrder.MathlibSupport

universe u

/-- `BGsection9.v: noncyclic_normed_sub_Uniqueness`
(Bender--Glauberman Theorem 9.1(b)). -/
theorem noncyclic_normed_sub_Uniqueness
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} [Fact p.Prime] {M B : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hB : IsPElementaryIn p M B)
    (hncyc : ¬ IsCyclic B)
    (hclosed : ∀ K : Subgroup G, IsPPrimeSubgroup p K →
      B ≤ Subgroup.normalizer (K : Set G) → K ≤ M) :
    B ∈ minSimple_uniq_max_groups (G := G) := by
  classical
  have hBM : B ≤ M := hB.1
  have hBp : IsPGroup p B := hB.2.isPGroup
  have hBne : B ≠ ⊥ := by
    intro hBbot
    apply hncyc
    rw [hBbot]
    exact isCyclic_of_subsingleton

  apply (uniq_mmax_subset1 hM hBM).mpr
  intro H₀ hH₀
  rw [Set.mem_singleton_iff]
  by_contra hH₀M

  have hPnormalizer : ∀ P : Sylow p M,
      B ≤ (P : Subgroup M).map M.subtype →
      Subgroup.normalizer
        ((P : Subgroup M).map M.subtype : Set G) ≤ M := by
    intro P hBP
    exact normalizer_map_sylow_le_maximal_of_closed_pPrime
      P hM hBP hBne hclosed
  obtain ⟨H, R, hH, hHM, hBR, hNRM⟩ :=
    exists_extremal_sylow hBM hBp hBne hH₀.1 hH₀.2 hH₀M
      hPnormalizer

  let RG : Subgroup G := (R : Subgroup H).map H.subtype
  let O : Subgroup G := (pPrimeCore p H).map H.subtype
  have hRGM : RG ≤ M := by
    exact Subgroup.le_normalizer.trans hNRM
  have hOprime : IsPPrimeSubgroup p O := by
    change IsPPrimeSubgroup p ((pPrimeCore p H).map H.subtype)
    rw [IsPPrimeSubgroup,
      Subgroup.card_map_of_injective H.subtype_injective]
    exact pPrimeCore_coprime_card
  have hRGnormalizesO : RG ≤ Subgroup.normalizer (O : Set G) := by
    have hRnormalizesCore :
        (R : Subgroup H) ≤
          Subgroup.normalizer (pPrimeCore p H : Set H) := by
      rw [(pPrimeCore p H).normalizer_eq_top]
      exact le_top
    exact (Subgroup.map_mono hRnormalizesCore).trans
      ((pPrimeCore p H).le_normalizer_map H.subtype)
  have hOM : O ≤ M :=
    hclosed O hOprime (hBR.trans hRGnormalizesO)

  have hFittingJoin : fittingWithin H ≤ RG ⊔ O := by
    calc
      fittingWithin H = (fittingCore H).map H.subtype := rfl
      _ ≤ (((R : Subgroup H) ⊔ pPrimeCore p H).map H.subtype) :=
        Subgroup.map_mono (fittingCore_le_sylow_sup_pPrimeCore R)
      _ = RG ⊔ O := by simp only [RG, O, Subgroup.map_sup]
  have hFittingM : fittingWithin H ≤ M :=
    hFittingJoin.trans (sup_le hRGM hOM)

  by_cases hRank3 : ∃ q : ℕ, q.Prime ∧
      HasElementaryAbelianRankAtLeast q 3 (fittingWithin H)
  · have hFunique :
        fittingWithin H ∈ minSimple_uniq_max_groups (G := G) :=
      Fitting_Uniqueness H hH hRank3
    have hFfamily :
        minSimple_max_groups_of (G := G) (fittingWithin H : Set G) =
          {M} :=
      def_uniq_mmax hFunique hM hFittingM
    have hEq : H = M :=
      eq_uniq_mmax hFfamily hH (fittingWithin_le H)
    exact hHM hEq
  · have hRank : ∀ q : ℕ, q.Prime →
        ¬ ∃ E : Subgroup (fittingCore H),
          IsElementaryAbelianOfRank q 3 E := by
      intro q hq
      rintro ⟨E, hE⟩
      let EH : Subgroup H := E.map (fittingCore H).subtype
      let EG : Subgroup G := EH.map H.subtype
      have hEGle : EG ≤ fittingWithin H := by
        dsimp only [EG, EH, fittingWithin]
        exact Subgroup.map_mono (Subgroup.map_subtype_le E)
      have hEH : IsElementaryAbelianOfRank q 3 EH := by
        dsimp only [EH]
        exact hE.map_of_injective (fittingCore H).subtype
          (fittingCore H).subtype_injective
      have hEG : IsElementaryAbelianOfRank q 3 EG := by
        dsimp only [EG]
        exact hEH.map_of_injective H.subtype H.subtype_injective
      apply hRank3
      exact ⟨q, hq, EG, hEGle, hEG⟩

    have hderived : _root_.commutator H ≤ fittingCore H :=
      rank2_der1_sub_Fitting (G := H) (mFT_odd H) (mmax_sol hH) hRank
    have hFrattini :
        fittingCore H ⊔
          Subgroup.normalizer ((R : Subgroup H) : Set H) = ⊤ :=
      fittingCore_sup_normalizer_sylow_eq_top R hderived
    have hnormalizerMapM :
        (Subgroup.normalizer ((R : Subgroup H) : Set H)).map H.subtype ≤ M :=
      ((R : Subgroup H).le_normalizer_map H.subtype).trans hNRM
    have htopMapM : (⊤ : Subgroup H).map H.subtype ≤ M := by
      rw [← hFrattini, Subgroup.map_sup]
      exact sup_le hFittingM hnormalizerMapM
    have hHMle : H ≤ M := by
      rw [← H.range_subtype, MonoidHom.range_eq_map]
      exact htopMapM
    exact hHM (eq_mmax hH hM hHMle)

end Submission.OddOrder.BG.Section09
