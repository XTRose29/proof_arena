import Submission.OddOrder.BG.Section07.MaximalSubgroups
import Submission.OddOrder.BG.Section07.NormedConstrainedRankThreeTrans
import Submission.OddOrder.BG.Section07.SCNNormedConstrained
import Submission.OddOrder.MathlibSupport.AbelianPGroupRankThree
import Submission.OddOrder.BG.Section07.PrimeSetCorePPrime

/-!
# Bender--Glauberman Theorem 7.6: Thompson transitivity

An SCN subgroup of rank at least three satisfies Hypothesis 7.1, and its
rank supplies the elementary-abelian subgroup needed by Theorem 7.2.  Thus
the `p`-prime core of its centralizer acts transitively on the maximal
normalized `q`-subgroups for every `q ≠ p`.
-/

namespace Submission.OddOrder.BG.Section07

open Submission.OddOrder.MathlibSupport

universe u

/-- `BGsection7.Thompson_transitivity`, Bender--Glauberman Theorem 7.6. -/
theorem Thompson_transitivity
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    (p q : ℕ) [Fact p.Prime] (A : Subgroup G)
    (hA : A ∈ minSimple_SCN_at (G := G) 3 p)
    (hqp : q ≠ p) :
    ∀ Q₁ Q₂ : Subgroup G,
      Q₁ ∈ max_normed_pgroups (A : Set G) ({q} : Set ℕ) →
      Q₂ ∈ max_normed_pgroups (A : Set G) ({q} : Set ℕ) →
      ∃ k : G,
        k ∈
          (pPrimeCore p (Subgroup.centralizer (A : Set G))).map
            (Subgroup.centralizer (A : Set G)).subtype ∧
        Q₂ = Q₁.map (MulAut.conj k⁻¹).toMonoidHom := by
  classical
  rcases hA with ⟨P, hSCN, hRank⟩
  have hAne : A ≠ ⊥ := by
    intro hAbot
    have hzero : Group.rank A = 0 := by
      rw [hAbot]
      exact Group.rank_eq_zero _
    omega
  letI : Nontrivial A := A.nontrivial_iff_ne_bot.mpr hAne
  have hAp : IsPGroup p A :=
    IsPGroup.to_le P.isPGroup' hSCN.le_sylow
  have hsupport : primeSupport (Nat.card A) = {p} :=
    hAp.primeSupport_natCard_eq_singleton
  have hqA : q ∉ primeSupport (Nat.card A) := by
    rw [hsupport]
    simpa only [Set.mem_singleton_iff] using hqp
  obtain ⟨E, hEA, hE⟩ :=
    exists_elementaryAbelian_rank_three_le_of_group_rank
      A hAp hSCN.commutative hRank
  have hAEcentral : A ≤ Subgroup.centralizer (E : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr
      hSCN.commutative).trans (Subgroup.centralizer_le hEA)
  have hcstr : NormedConstrained A :=
    SCN_normed_constrained p P A hSCN (by omega)
  intro Q₁ Q₂ hQ₁ hQ₂
  obtain ⟨k, hk, hconj⟩ :=
    normed_constrained_rank3_trans A hcstr hqA
      ⟨p, E, Fact.out, hEA, hAEcentral, hE⟩ Q₁ Q₂ hQ₁ hQ₂
  refine ⟨k, ?_, hconj⟩
  rw [centralPrimeComplementCore_eq_map_pPrimeCore
    (p := p) A hsupport] at hk
  exact hk

end Submission.OddOrder.BG.Section07
