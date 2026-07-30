import Submission.OddOrder.BG.Section03.FrobeniusPartition

/-!
Normalizer control for nontrivial subgroups of Frobenius complements.
-/

namespace Submission.OddOrder.BG.Section03

universe u

variable {G : Type u} [Group G]
variable {K R S : Subgroup G}

namespace IsFrobeniusDecomposition

/-- The normalizer of a nontrivial subgroup of the Frobenius complement is
contained in the complement. -/
theorem normalizer_le_complement_of_ne_bot_of_le
    (h : IsFrobeniusDecomposition K R)
    (hSne : S ≠ ⊥) (hSR : S ≤ R) :
    Subgroup.normalizer (S : Set G) ≤ R := by
  intro g hg
  by_contra hgR
  have hmapS : S.map (MulAut.conj g).toMonoidHom = S :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have hSmap : S ≤ R.map (MulAut.conj g).toMonoidHom := by
    rw [← hmapS]
    exact Subgroup.map_mono hSR
  apply hSne
  apply le_antisymm _ bot_le
  intro s hs
  have hsbot : s ∈ (R ⊓ R.map (MulAut.conj g).toMonoidHom) :=
    ⟨hSR hs, hSmap hs⟩
  rw [disjoint_iff.mp
    (h.disjoint_complement_conjugate_of_not_mem hgR)] at hsbot
  exact hsbot

/-- The same normalizer control inside an arbitrary kernel-conjugate of the
Frobenius complement. -/
theorem normalizer_le_kernel_conjugate_complement
    (h : IsFrobeniusDecomposition K R) (x : K)
    (hSne : S ≠ ⊥)
    (hSRx : S ≤ R.map (MulAut.conj (x : G)).toMonoidHom) :
    Subgroup.normalizer (S : Set G) ≤
      R.map (MulAut.conj (x : G)).toMonoidHom := by
  let xi : G := (x : G)⁻¹
  let S0 : Subgroup G := S.map (MulAut.conj xi).toMonoidHom
  have hS0ne : S0 ≠ ⊥ := by
    intro hbot
    apply hSne
    exact (Subgroup.map_eq_bot_iff_of_injective S
      (MulAut.conj xi).injective).mp hbot
  have hS0R : S0 ≤ R := by
    rintro z ⟨s, hs, rfl⟩
    rcases hSRx hs with ⟨r, hr, hrs⟩
    have hz : xi * s * xi⁻¹ = r := by
      rw [← hrs]
      dsimp [xi]
      group
    change xi * s * xi⁻¹ ∈ R
    rw [hz]
    exact hr
  intro g hg
  let a : G := xi * g * xi⁻¹
  have hgmap : S.map (MulAut.conj g).toMonoidHom = S :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have hamap : S0.map (MulAut.conj a).toMonoidHom = S0 := by
    calc
      S0.map (MulAut.conj a).toMonoidHom =
          (S.map (MulAut.conj g).toMonoidHom).map
            (MulAut.conj xi).toMonoidHom := by
        ext z
        constructor
        · rintro ⟨w, ⟨s, hs, rfl⟩, rfl⟩
          refine ⟨g * s * g⁻¹, ⟨s, hs, rfl⟩, ?_⟩
          dsimp [a]
          group
        · rintro ⟨w, ⟨s, hs, rfl⟩, rfl⟩
          refine ⟨xi * s * xi⁻¹, ⟨s, hs, rfl⟩, ?_⟩
          dsimp [a]
          group
      _ = S0 := by rw [hgmap]
  have haNorm : a ∈ Subgroup.normalizer (S0 : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hamap
  have haR : a ∈ R :=
    h.normalizer_le_complement_of_ne_bot_of_le hS0ne hS0R haNorm
  refine ⟨a, haR, ?_⟩
  dsimp [a, xi]
  group

end IsFrobeniusDecomposition

end Submission.OddOrder.BG.Section03
