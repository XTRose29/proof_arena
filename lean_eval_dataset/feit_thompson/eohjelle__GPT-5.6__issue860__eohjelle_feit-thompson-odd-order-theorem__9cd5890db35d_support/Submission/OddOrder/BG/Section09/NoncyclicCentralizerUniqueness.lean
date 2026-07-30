import Submission.OddOrder.BG.Section09.NoncyclicNormedSubUniqueness
import Submission.OddOrder.MathlibSupport.CoprimeAbelianCentralizerGenerationSolvable

/-!
# Bender--Glauberman Theorem 9.1(a)

If the centralizer of every nonidentity element of a noncyclic
elementary-abelian subgroup `B` lies in a maximal subgroup `M`, then `M` is
the unique maximal overgroup of `B`.
-/

namespace Submission.OddOrder.BG.Section09

open Submission.OddOrder.BG.Section07
open Submission.OddOrder.MathlibSupport

universe u

/-- `BGsection9.v: noncyclic_cent1_sub_Uniqueness`
(Bender--Glauberman Theorem 9.1(a)). -/
theorem noncyclic_cent1_sub_Uniqueness
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} [Fact p.Prime] {M B : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hB : IsPElementaryIn p M B)
    (hncyc : ¬ IsCyclic B)
    (hcent : ∀ b : G, b ∈ B → b ≠ 1 →
      Subgroup.centralizer ({b} : Set G) ≤ M) :
    B ∈ minSimple_uniq_max_groups (G := G) := by
  apply noncyclic_normed_sub_Uniqueness hM hB hncyc
  intro K hKprime hBnormK
  have hKcop : Nat.Coprime p (Nat.card K) := hKprime
  have hpB : p ∣ Nat.card B := by
    rcases hB.2.isPGroup.card_eq_or_dvd with hBcard | hpB
    · haveI : Subsingleton B :=
        (Nat.card_eq_one_iff_unique.mp hBcard).1
      exact (hncyc isCyclic_of_subsingleton).elim
    · exact hpB
  have hKproper : K < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro hKtop
    have hBK : B ≤ K := by
      rw [hKtop]
      exact le_top
    have hpK : p ∣ Nat.card K :=
      hpB.trans (Subgroup.card_dvd_of_le hBK)
    exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hKcop) hpK
  obtain ⟨n, hBcard⟩ := IsPGroup.iff_card.mp hB.2.isPGroup
  have hcop : (Nat.card K).Coprime (Nat.card B) := by
    rw [hBcard]
    exact hKcop.symm.pow_right n
  apply le_of_centralizerWithin_zpowers_le_of_coprime_abelian_solvable
    hB.2.commutative hncyc hBnormK hcop (mFT_sol hKproper)
  intro b hb hb1
  calc
    centralizerWithin K (Subgroup.zpowers b) ≤
        Subgroup.centralizer (Subgroup.zpowers b : Set G) := inf_le_right
    _ ≤ Subgroup.centralizer ({b} : Set G) := by
      apply Subgroup.centralizer_le
      exact Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers b)
    _ ≤ M := hcent b hb hb1

end Submission.OddOrder.BG.Section09
