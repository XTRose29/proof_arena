import Submission.OddOrder.MathlibSupport.BaerSuzukiFirstNormalizerWitness
import Submission.OddOrder.MathlibSupport.SylowConjugateEmbedding

/-!
The second normalizing conjugate in the hard Baer-Suzuki branch.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G]

/-- Normalizer growth in the selected Sylow subgroup, together with Sylow
conjugacy in the exceptional branch, produces a normalizing conjugate in `P`
that lies outside `D`. -/
theorem exists_sylow_conjugate_mem_normalizer_not_candidate
    {p : ℕ} [Fact p.Prime] {x y₀ : G}
    (P₀ : Sylow p (conjugacyClassGenerated x))
    {B : Subgroup G} {D : Set G}
    (hy₀class : y₀ ∈ conjugatesOf x)
    (hy₀P : y₀ ∉ (P₀ : Subgroup (conjugacyClassGenerated x)).map
      (conjugacyClassGenerated x).subtype)
    (hy₀B : y₀ ∈ B) (hDB : D ⊆ B)
    (hBE : B ≤ conjugacyClassGenerated x) (hB : IsPGroup p B)
    (hDPE : D ⊆
      ((P₀ : Subgroup (conjugacyClassGenerated x)).map
        (conjugacyClassGenerated x).subtype : Set G) ∩ conjugatesOf x)
    (hself : D ⊆ Subgroup.normalizer D) :
    ∃ y₂ : G,
      y₂ ∈ (P₀ : Subgroup (conjugacyClassGenerated x)).map
          (conjugacyClassGenerated x).subtype ∧
      y₂ ∈ conjugatesOf x ∧ y₂ ∈ Subgroup.normalizer D ∧ y₂ ∉ D := by
  let E : Subgroup G := conjugacyClassGenerated x
  let P : Subgroup G := (P₀ : Subgroup E).map E.subtype
  change y₀ ∉ P at hy₀P
  change D ⊆ (P : Set G) ∩ conjugatesOf x at hDPE
  change ∃ y₂ : G, y₂ ∈ P ∧ y₂ ∈ conjugatesOf x ∧
    y₂ ∈ Subgroup.normalizer D ∧ y₂ ∉ D
  let NP : Subgroup G := P ⊓ Subgroup.normalizer D
  have hDNP : D ⊆ NP := by
    intro d hd
    exact ⟨(hDPE hd).1, hself hd⟩
  by_cases hNPP : NP = P
  · obtain ⟨e, he⟩ := exists_conjugate_le_sylow_map P₀ hBE hB
    let f : G → G := fun g => (e : G) * g * (e : G)⁻¹
    have hf : Function.Injective f := (MulAut.conj (e : G)).injective
    have hy₀D : y₀ ∉ D := fun hyD => hy₀P (hDPE hyD).1
    have hnotSubset : ¬f '' Set.insert y₀ D ⊆ D := by
      intro hsub
      have hcard := Set.ncard_le_ncard hsub
      rw [Set.ncard_image_of_injective _ hf] at hcard
      have hcardInsert : (Set.insert y₀ D).ncard = D.ncard + 1 :=
        Set.ncard_insert_of_notMem hy₀D
      rw [hcardInsert] at hcard
      omega
    obtain ⟨y₂, hy₂image, hy₂D⟩ := Set.not_subset.mp hnotSubset
    obtain ⟨s, hs, rfl⟩ := hy₂image
    have hsB : s ∈ B := by
      rcases hs with rfl | hs
      · exact hy₀B
      · exact hDB hs
    have hsclass : s ∈ conjugatesOf x := by
      rcases hs with rfl | hs
      · exact hy₀class
      · exact (hDPE hs).2
    have hyP : f s ∈ P := he s hsB
    have hyNP : f s ∈ NP := by
      rw [hNPP]
      exact hyP
    have hyclass : f s ∈ conjugatesOf x :=
      hsclass.trans (isConj_iff.mpr ⟨(e : G), rfl⟩)
    exact ⟨f s, hyP, hyclass, hyNP.2, hy₂D⟩
  · have hNPlt : NP < P := lt_of_le_of_ne inf_le_left hNPP
    have hgrowth : NP < P ⊓ Subgroup.normalizer (NP : Set G) :=
      lt_inf_normalizer_of_isPGroup
        (P₀.isPGroup'.map E.subtype) hNPlt
    obtain ⟨z, hz, hzNP⟩ := SetLike.exists_of_lt hgrowth
    have hzP : z ∈ P := hz.1
    have hzNNP : z ∈ Subgroup.normalizer (NP : Set G) := hz.2
    have hzN : z ∉ Subgroup.normalizer D := by
      intro hzD
      exact hzNP ⟨hzP, hzD⟩
    have hnotall : ¬∀ d : G, d ∈ D → z * d * z⁻¹ ∈ D := by
      intro hall
      exact hzN (Subgroup.mem_normalizer_fintype hall)
    push Not at hnotall
    obtain ⟨d, hdD, hydD⟩ := hnotall
    let y₂ : G := z * d * z⁻¹
    have hy₂NP : y₂ ∈ NP :=
      (Subgroup.mem_normalizer_iff.mp hzNNP d).mp (hDNP hdD)
    have hdclass : d ∈ conjugatesOf x := (hDPE hdD).2
    have hy₂class : y₂ ∈ conjugatesOf x :=
      hdclass.trans (isConj_iff.mpr ⟨z, rfl⟩)
    exact ⟨y₂, hy₂NP.1, hy₂class, hy₂NP.2, hydD⟩

end Submission.OddOrder.MathlibSupport
