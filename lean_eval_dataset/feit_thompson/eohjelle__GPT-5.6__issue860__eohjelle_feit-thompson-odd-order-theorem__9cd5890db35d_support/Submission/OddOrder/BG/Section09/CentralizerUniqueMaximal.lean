import Submission.OddOrder.BG.Section09.NoncyclicCentralizerUniqueness

/-!
# Bender--Glauberman Corollary 9.2

A subgroup of rank at least two which centralizes a subgroup with a unique
maximal overgroup itself has a unique maximal overgroup.
-/

namespace Submission.OddOrder.BG.Section09

open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.MathlibSupport

universe u

/-- `BGsection9.v: cent_uniq_Uniqueness`
(Bender--Glauberman Corollary 9.2). -/
theorem cent_uniq_Uniqueness
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {K L : Subgroup G}
    (hL : L ∈ minSimple_uniq_max_groups (G := G))
    (hKL : K ≤ Subgroup.centralizer (L : Set G))
    (hRank2 : ∃ p : ℕ, p.Prime ∧
      HasElementaryAbelianRankAtLeast p 2 K) :
    K ∈ minSimple_uniq_max_groups (G := G) := by
  rcases (uniq_mmaxP L).mp hL with ⟨H, hLHunique⟩
  obtain ⟨hH, hLH⟩ := mem_uniq_mmax hLHunique
  rcases hRank2 with ⟨p, hp, B, hBK, hB⟩
  letI : Fact p.Prime := ⟨hp⟩

  have hcentH : ∀ b : G, b ∈ B → b ≠ 1 →
      Subgroup.centralizer ({b} : Set G) ≤ H := by
    intro b hb hb1
    have hLcentb : L ≤ Subgroup.centralizer ({b} : Set G) := by
      intro l hl
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact
        Subgroup.mem_centralizer_iff.mp (hKL (hBK hb)) l hl
    exact sub_uniq_mmax hLHunique hLcentb (mFT_cent1_proper hb1)

  have hBH : B ≤ H := by
    intro b hb
    by_cases hb1 : b = 1
    · subst b
      exact H.one_mem
    · apply hcentH b hb hb1
      rw [Subgroup.mem_centralizer_singleton_iff]

  have hBU : B ∈ minSimple_uniq_max_groups (G := G) :=
    noncyclic_cent1_sub_Uniqueness hH
      ⟨hBH, hB.toIsElementaryAbelianGroup⟩
      (hB.not_isCyclic hp) hcentH
  have hKproper : K < ⊤ :=
    lt_of_le_of_lt hKL (mFT_cent_proper L (uniq_mmax_neq1 hL))
  exact uniq_mmaxS hBK hKproper hBU

end Submission.OddOrder.BG.Section09
