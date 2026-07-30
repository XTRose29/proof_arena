import Submission.OddOrder.BG.Section07.MaximalSubgroups
import Submission.OddOrder.MathlibSupport.SubgroupCardinality
import Submission.OddOrder.MathlibSupport.SylowIntersectionNormalizer

/-!
# Bender--Glauberman Section 9: an extremal Sylow overlap

Among the maximal subgroups different from `M` and containing a fixed
nontrivial `p`-subgroup `B`, choose one for which the Sylow `p`-part of its
intersection with `M` has largest cardinality.  The normalizer-growth
argument forces the ambient normalizer of that Sylow subgroup back into
`M`.
-/

namespace Submission.OddOrder.BG.Section09

open Submission.OddOrder
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.MathlibSupport

universe u

/-- The extremal Sylow-overlap package used in the proof of
Bender--Glauberman Theorem 9.1(b).

The extremal score is the cardinality of a Sylow `p`-subgroup of `H ⊓ M`,
not the cardinality of the full intersection. -/
theorem exists_extremal_sylow
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} [Fact p.Prime]
    {M B H₀ : Subgroup G}
    (hBM : B ≤ M) (hBp : IsPGroup p B) (hBne : B ≠ ⊥)
    (hH₀ : H₀ ∈ minSimple_max_groups (G := G))
    (hBH₀ : B ≤ H₀) (hH₀M : H₀ ≠ M)
    (hPnorm : ∀ P : Sylow p M,
      B ≤ (P : Subgroup M).map M.subtype →
      Subgroup.normalizer
        ((P : Subgroup M).map M.subtype : Set G) ≤ M) :
    ∃ H : Subgroup G, ∃ R : Sylow p H,
      H ∈ minSimple_max_groups (G := G) ∧ H ≠ M ∧
      B ≤ (R : Subgroup H).map H.subtype ∧
      Subgroup.normalizer
        ((R : Subgroup H).map H.subtype : Set G) ≤ M := by
  classical
  let candidates : Set (Subgroup G) :=
    {H | H ∈ minSimple_max_groups (G := G) ∧ B ≤ H ∧ H ≠ M}
  let score : Subgroup G → ℕ := fun H =>
    Nat.card (default : Sylow p ↑(H ⊓ M))
  have hH₀cand : H₀ ∈ candidates := ⟨hH₀, hBH₀, hH₀M⟩
  obtain ⟨H, hHcand, hHmax⟩ :=
    Set.exists_max_image candidates score candidates.toFinite
      ⟨H₀, hH₀cand⟩
  have hH : H ∈ minSimple_max_groups (G := G) := hHcand.1
  have hBH : B ≤ H := hHcand.2.1
  have hHM : H ≠ M := hHcand.2.2

  let I : Subgroup G := H ⊓ M
  have hBI : B ≤ I := le_inf hBH hBM
  let BI : Subgroup I := B.subgroupOf I
  have hBIp : IsPGroup p BI :=
    hBp.of_equiv (Subgroup.subgroupOfEquivOfLe hBI).symm
  obtain ⟨R, hBIR⟩ := hBIp.exists_le_sylow
  let RG : Subgroup G := (R : Subgroup I).map I.subtype
  have hBRG : B ≤ RG := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hBI]
    exact Subgroup.map_mono hBIR
  have hRGI : RG ≤ I := Subgroup.map_subtype_le _
  have hRGH : RG ≤ H := hRGI.trans inf_le_left
  have hRGM : RG ≤ M := hRGI.trans inf_le_right
  have hRGp : IsPGroup p RG := R.isPGroup'.map I.subtype
  have hRGne : RG ≠ ⊥ := fun hRGbot =>
    hBne (le_bot_iff.mp (hBRG.trans_eq hRGbot))

  have hscoreH : score H = Nat.card RG := by
    dsimp only [score, RG, I]
    rw [Subgroup.card_map_of_injective I.subtype_injective]
    exact (default : Sylow p ↑(H ⊓ M)).card_eq_multiplicity.trans
      R.card_eq_multiplicity.symm

  have hNRGM : Subgroup.normalizer (RG : Set G) ≤ M := by
    let RM : Subgroup M := RG.subgroupOf M
    have hRMp : IsPGroup p RM :=
      hRGp.of_equiv (Subgroup.subgroupOfEquivOfLe hRGM).symm
    obtain ⟨P, hRMP⟩ := hRMp.exists_le_sylow
    let PG : Subgroup G := (P : Subgroup M).map M.subtype
    have hRGPG : RG ≤ PG := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hRGM]
      exact Subgroup.map_mono hRMP
    have hBPG : B ≤ PG := hBRG.trans hRGPG
    by_cases hRGPG_eq : RG = PG
    · rw [hRGPG_eq]
      exact hPnorm P hBPG
    · have hRGltPG : RG < PG :=
        lt_of_le_of_ne hRGPG hRGPG_eq
      let T : Subgroup G :=
        PG ⊓ Subgroup.normalizer (RG : Set G)
      have hRGltT : RG < T :=
        lt_inf_normalizer_of_isPGroup
          (P.isPGroup'.map M.subtype) hRGltPG
      have hNproper : Subgroup.normalizer (RG : Set G) < ⊤ :=
        mFT_norm_proper RG hRGne
          (lt_of_le_of_lt hRGH (mmax_proper hH))
      by_contra hNRGM
      obtain ⟨E, hE, hNE⟩ :=
        mmax_exists (Subgroup.normalizer (RG : Set G)) hNproper
      have hBE : B ≤ E :=
        hBRG.trans (Subgroup.le_normalizer.trans hNE)
      have hEM : E ≠ M := by
        intro hEq
        exact hNRGM (hNE.trans_eq hEq)
      have hEcand : E ∈ candidates := ⟨hE, hBE, hEM⟩
      have hTM : T ≤ M := by
        apply inf_le_left.trans
        dsimp only [PG]
        exact Subgroup.map_subtype_le (P : Subgroup M)
      have hTE : T ≤ E := inf_le_right.trans hNE
      let J : Subgroup G := E ⊓ M
      have hTJ : T ≤ J := le_inf hTE hTM
      let TJ : Subgroup J := T.subgroupOf J
      have hTJp : IsPGroup p TJ :=
        ((P.isPGroup'.map M.subtype).to_le inf_le_left).of_equiv
          (Subgroup.subgroupOfEquivOfLe hTJ).symm
      obtain ⟨S, hTJS⟩ := hTJp.exists_le_sylow
      have hcardRGltT : Nat.card RG < Nat.card T :=
        natCard_subgroup_lt_of_lt hRGltT
      have hcardTleS : Nat.card T ≤ Nat.card (S : Subgroup J) := by
        rw [← natCard_subgroupOf_eq hTJ]
        exact Subgroup.card_le_of_le hTJS
      have hcardSscore : Nat.card (S : Subgroup J) = score E := by
        dsimp only [score, J]
        exact S.card_eq_multiplicity.trans
          (default : Sylow p ↑(E ⊓ M)).card_eq_multiplicity.symm
      have hscoreEleH : score E ≤ score H := hHmax E hEcand
      have : Nat.card RG < Nat.card RG := calc
        Nat.card RG < Nat.card T := hcardRGltT
        _ ≤ Nat.card (S : Subgroup J) := hcardTleS
        _ = score E := hcardSscore
        _ ≤ score H := hscoreEleH
        _ = Nat.card RG := hscoreH
      exact (lt_irrefl _ this).elim

  obtain ⟨RH, hRHmap⟩ :=
    exists_sylow_map_eq_of_sylow_inf_of_normalizer_le H M R hNRGM
  refine ⟨H, RH, hH, hHM, ?_, ?_⟩
  · rwa [hRHmap]
  · rwa [hRHmap]

end Submission.OddOrder.BG.Section09
