import Submission.OddOrder.MathlibSupport.BaerSuzukiSetNormalizer
import Submission.OddOrder.MathlibSupport.PGroupNormalizer

/-!
The first normalizing conjugate in the hard Baer-Suzuki branch.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G]

/-- Inside the witness p-group, normalizer growth produces a conjugate of
`x` that normalizes `D` but lies outside the selected Sylow subgroup. -/
theorem exists_conjugate_mem_normalizer_not_sylow
    {p : ℕ} [Fact p.Prime] {x y₀ : G} {P B : Subgroup G} {D : Set G}
    (hy₀class : y₀ ∈ conjugatesOf x) (hy₀P : y₀ ∉ P)
    (hy₀B : y₀ ∈ B) (hDB : D ⊆ B) (hB : IsPGroup p B)
    (hdef : D = ((P : Set G) ∩ (B : Set G)) ∩ conjugatesOf x)
    (hself : D ⊆ Subgroup.normalizer D) :
    ∃ y₁ : G, y₁ ∈ conjugatesOf x ∧
      y₁ ∈ Subgroup.normalizer D ∧ y₁ ∉ P := by
  let NB : Subgroup G := B ⊓ Subgroup.normalizer D
  have hDNB : D ⊆ NB := by
    intro d hd
    exact ⟨hDB hd, hself hd⟩
  by_cases hNBB : NB = B
  · have hy₀NB : y₀ ∈ NB := by
      rw [hNBB]
      exact hy₀B
    exact ⟨y₀, hy₀class, hy₀NB.2, hy₀P⟩
  · have hNBlt : NB < B := lt_of_le_of_ne inf_le_left hNBB
    have hgrowth : NB < B ⊓ Subgroup.normalizer (NB : Set G) :=
      lt_inf_normalizer_of_isPGroup hB hNBlt
    obtain ⟨z, hz, hzNB⟩ := SetLike.exists_of_lt hgrowth
    have hzB : z ∈ B := hz.1
    have hzNNB : z ∈ Subgroup.normalizer (NB : Set G) := hz.2
    have hzN : z ∉ Subgroup.normalizer D := by
      intro hzD
      exact hzNB ⟨hzB, hzD⟩
    have hnotall : ¬∀ d : G, d ∈ D → z * d * z⁻¹ ∈ D := by
      intro hall
      exact hzN (Subgroup.mem_normalizer_fintype hall)
    push Not at hnotall
    obtain ⟨d, hdD, hydD⟩ := hnotall
    let y₁ : G := z * d * z⁻¹
    have hdNB : d ∈ NB := hDNB hdD
    have hy₁NB : y₁ ∈ NB :=
      (Subgroup.mem_normalizer_iff.mp hzNNB d).mp hdNB
    have hy₁class : y₁ ∈ conjugatesOf x := by
      have hdclass : d ∈ conjugatesOf x := by
        rw [hdef] at hdD
        exact hdD.2
      exact hdclass.trans (isConj_iff.mpr ⟨z, rfl⟩)
    have hy₁P : y₁ ∉ P := by
      intro hyP
      apply hydD
      rw [hdef]
      exact ⟨⟨hyP, hy₁NB.1⟩, hy₁class⟩
    exact ⟨y₁, hy₁class, hy₁NB.2, hy₁P⟩

end Submission.OddOrder.MathlibSupport
