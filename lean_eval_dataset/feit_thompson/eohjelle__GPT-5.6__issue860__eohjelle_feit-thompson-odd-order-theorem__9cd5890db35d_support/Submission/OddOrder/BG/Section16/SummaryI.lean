import Submission.OddOrder.BG.Section16.SummaryABC

/-!
# Bender--Glauberman Section 16: summary I

This phase packages Bender--Glauberman Theorem I.  Its exceptional alternative
contains subgroup witnesses, so the conclusion is data in `Type`, with the
classification expressed by `Sum` and dependent `Sigma` types.
-/

namespace Submission.OddOrder.BG.Section16

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section09
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.BG.Section12
open Submission.OddOrder.BG.Section13
open Submission.OddOrder.BG.Section14
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.PF
open scoped Pointwise IsMulCommutative commutatorElement

noncomputable section

universe u

variable {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]

/-- Conjugation of an element, using the same convention as subgroup
conjugation by `MulAut.conj`. -/
abbrev conjugateElement16 (x g : G) : G := MulAut.conj g x

/-- Transport an ambient Hall subgroup into an intermediate subgroup that
contains it. -/
private theorem isHall_subgroupOf_intermediate16
    {A B : Subgroup G} (hAB : A ≤ B) {pi : Set ℕ}
    (hA : IsHall pi A) :
    IsHall pi (A.subgroupOf B) := by
  constructor
  · simpa [MathlibSupport.natCard_subgroupOf_eq hAB] using
      hA.isPiNumber_card
  · exact hA.isPiNumber_index.of_dvd
      (Subgroup.relIndex_dvd_index_of_le hAB)

/-- The exceptional pair in clauses (a)--(e) of Bender--Glauberman
Theorem I. -/
structure BGSummaryIExceptionalPair (S T : Subgroup G) : Type u where
  S_maximal : S ∈ minSimple_max_groups (G := G)
  T_maximal : T ∈ minSimple_max_groups (G := G)
  W₁ : Subgroup G
  W₂ : Subgroup G
  W : Subgroup G
  direct_W : IsInternalDirectProductIn W₁ W₂ W
  /- (a) -/
  W_cyclic : IsCyclic W
  outside_normalizedTI :
    IsNormalizedTI
      ((W : Set G) \ ((W₁ : Set G) ∪ (W₂ : Set G))) ⊤ W
  W₁_ne_bot : W₁ ≠ ⊥
  W₂_ne_bot : W₂ ≠ ⊥
  /- (b) -/
  S_decomposition : IsInternalSemidirectProductIn (derivedWithin S) W₁ S
  T_decomposition : IsInternalSemidirectProductIn (derivedWithin T) W₂ T
  intersection_eq : S ⊓ T = W
  /- (c) -/
  controls_non_type_one : ∀ {M : Subgroup G},
    M ∈ minSimple_max_groups (G := G) → FTtype M ≠ 1 →
      ∃ g : G,
        conjugateSubgroup16 S g = M ∨ conjugateSubgroup16 T g = M
  /- (d) -/
  one_type_two : FTtype S = 2 ∨ FTtype T = 2
  /- (e) -/
  S_type_range : 1 < FTtype S ∧ FTtype S ≤ 5
  T_type_range : 1 < FTtype T ∧ FTtype T ≤ 5

/-- The complete conclusion of Bender--Glauberman Theorem I. -/
structure BGSummaryIConclusion : Type u where
  /-- Nilpotent Hall subgroups control fusion in their normalizers. -/
  nilpotent_Hall_fusion : ∀ (H : Subgroup G),
    Nat.Coprime (Nat.card H) H.index →
    Group.IsNilpotent H →
    ∀ x a : G, x ∈ H → conjugateElement16 x a ∈ H →
      ∃ y : G, y ∈ Subgroup.normalizer (H : Set G) ∧
        conjugateElement16 x a = conjugateElement16 x y
  /-- Either every maximal subgroup has type I, or the exceptional pair
  controls every non-type-I maximal subgroup. -/
  type_classification :
    PSum
      (∀ M : Subgroup G,
        M ∈ minSimple_max_groups (G := G) → FTtype M = 1)
      (Σ S : Subgroup G, Σ T : Subgroup G,
        BGSummaryIExceptionalPair S T)

/-- `BGsection16.v: BGsummaryI`, Bender--Glauberman Theorem I. -/
noncomputable def BGsummaryI : BGSummaryIConclusion (G := G) := by
  classical
  refine
    { nilpotent_Hall_fusion := ?_
      type_classification := ?_ }
  · intro H hHall hnil x a hx hxa
    have hHallG : IsHall (primeSupport (Nat.card H)) H :=
      (isHall_primeSupport_iff H).2 hHall
    obtain ⟨M, hM, hHsigma⟩ := nilpotent_Hall_sigma hnil hHallG
    have hHallSigma :
        IsHall (primeSupport (Nat.card H))
          (H.subgroupOf (sigmaCore M)) :=
      isHall_subgroupOf_intermediate16 hHsigma hHallG
    obtain ⟨y, hy, hconj⟩ :=
      sigma_Hall_tame hM hHsigma hHallSigma hx hxa
    exact ⟨y, hy.2, hconj⟩
  · by_cases hAll : ∀ M : Subgroup G,
        M ∈ minSimple_max_groups (G := G) → FTtype M = 1
    · exact PSum.inl hAll
    · have hExists : ∃ S : Subgroup G,
          S ∈ minSimple_max_groups (G := G) ∧ FTtype S ≠ 1 := by
        push_neg at hAll
        exact hAll
      let S : Subgroup G := Classical.choose hExists
      have hSData :
          S ∈ minSimple_max_groups (G := G) ∧ FTtype S ≠ 1 :=
        Classical.choose_spec hExists
      have hS : S ∈ minSimple_max_groups (G := G) := hSData.1
      have hSnotOne : FTtype S ≠ 1 := hSData.2
      have hSP : S ∈ typePMaximalSubgroups (G := G) :=
        (FTtype_Pmax hS).2 hSnotOne
      have hKappaExists :
          ∃ U K : Subgroup G, KappaComplement S U K := kappa_witness hS
      let U : Subgroup G := Classical.choose hKappaExists
      have hKExists : ∃ K : Subgroup G, KappaComplement S U K :=
        Classical.choose_spec hKappaExists
      let K : Subgroup G := Classical.choose hKExists
      have hCompl : KappaComplement S U K := Classical.choose_spec hKExists
      have hKne : K ≠ ⊥ := (trivgPmax hS hCompl).1 hSP
      have hC : BGSummaryC S U K := BGsummaryC hS hCompl hKne
      have hTExists : ∃ T : Subgroup G, PTypeEmbedding S K T :=
        Ptype_embedding hSP hCompl.K_le_M hCompl.hall_K
      let T : Subgroup G := Classical.choose hTExists
      have hEmbed : PTypeEmbedding S K T := Classical.choose_spec hTExists
      have hPartnerExists : ∃ N : Subgroup G,
          PTypeEmbedding T (pTypePartner S K) N :=
        Ptype_embedding hEmbed.Mstar_typeP hEmbed.Kstar_le_Mstar
          hEmbed.Kstar_hall_kappa
      let N : Subgroup G := Classical.choose hPartnerExists
      have hPartnerEmbed : PTypeEmbedding T (pTypePartner S K) N :=
        Classical.choose_spec hPartnerExists
      let Kstar : Subgroup G := pTypePartner S K
      let Z : Subgroup G := pTypeJoin S K
      have hSrange : 1 < FTtype S ∧ FTtype S ≤ 5 := by
        have hrange := FTtype_range S
        omega
      have hTnotOne : FTtype T ≠ 1 :=
        (FTtype_Pmax hEmbed.Mstar_typeP.1).1 hEmbed.Mstar_typeP
      have hTrange : 1 < FTtype T ∧ FTtype T ≤ 5 := by
        have hrange := FTtype_range T
        omega
      refine PSum.inr ⟨S, T, ?_⟩
      exact
        { S_maximal := hS
          T_maximal := hEmbed.Mstar_typeP.1
          W₁ := K
          W₂ := Kstar
          W := Z
          direct_W := by simpa [Kstar, Z] using hC.join_direct
          W_cyclic := by simpa [Z] using hEmbed.cyclicStructure.cyclic_join
          outside_normalizedTI := by
            simpa [Kstar, Z, pTypeTISet] using
              hC.join_difference_normalizedTI
          W₁_ne_bot := hKne
          W₂_ne_bot := by simpa [Kstar] using hC.partner_ne_bot
          S_decomposition := hEmbed.derived_sdprod
          T_decomposition := by
            simpa only [Kstar, derivedWithin] using
              hPartnerEmbed.derived_sdprod
          intersection_eq := by
            simpa [Z] using hEmbed.cyclicStructure.inf_eq_join
          controls_non_type_one := by
            intro M hM hMnotOne
            have hMP : M ∈ typePMaximalSubgroups (G := G) :=
              (FTtype_Pmax hM).2 hMnotOne
            rcases hEmbed.typeP_transitive hMP with hSM | hTM
            · obtain ⟨g, hg⟩ := hSM
              exact ⟨g, Or.inl hg.symm⟩
            · obtain ⟨g, hg⟩ := hTM
              exact ⟨g, Or.inr hg.symm⟩
          one_type_two := by
            rcases hEmbed.typeP2_prime with hS2 | hT2
            · exact Or.inl ((FTtype_P2max hS).1 hS2.1)
            · exact Or.inr
                ((FTtype_P2max hEmbed.Mstar_typeP.1).1 hT2.1)
          S_type_range := hSrange
          T_type_range := hTrange }

end

end Submission.OddOrder.BG.Section16
