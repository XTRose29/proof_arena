import Submission.Zipper

open LeanEval.GroupTheory
open LeanEval.GroupTheory.Defs

namespace Submission.Helpers

universe u

/-- If an element lies in the `p`-core of a maximal overgroup but not in the
ambient `p`-core, then that maximal overgroup is exactly the normalizer of
the mapped local `p`-core. -/
theorem normalizer_map_pCore_eq_coatom
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (x : G) (M : Subgroup G) (hM : IsCoatom M)
    (hxM : x ∈ M)
    (hxcore : (⟨x, hxM⟩ : M) ∈ pCore p M)
    (hxnot : x ∉ pCore p G) :
    Subgroup.normalizer
        ((pCore p M).map M.subtype : Set G) = M := by
  let P : Subgroup G := (pCore p M).map M.subtype
  have hPM : P ≤ M :=
    Subgroup.map_subtype_le (pCore p M)
  letI : (pCore p M).Normal := pCore_normal p
  have hMN : M ≤ Subgroup.normalizer (P : Set G) := by
    have hmap :=
      Subgroup.le_normalizer_map
        (H := pCore p M) M.subtype
    rw [Subgroup.normalizer_eq_top,
      ← MonoidHom.range_eq_map,
      M.range_subtype] at hmap
    exact hmap
  have hNne : Subgroup.normalizer (P : Set G) ≠ ⊤ := by
    intro htop
    have hPnormal : P.Normal :=
      Subgroup.normalizer_eq_top_iff.mp htop
    have hPp : IsPGroup p P :=
      pCore_isPGroup.map M.subtype
    have hPle : P ≤ pCore p G :=
      le_pCore hPnormal hPp
    apply hxnot
    apply hPle
    exact ⟨⟨x, hxM⟩, hxcore, rfl⟩
  exact (hM.ne_top_iff_eq hMN).mp hNne

/-- The normalizer of the intersection of two mapped local `p`-cores is
contained in a maximal overgroup of `x`, unless `x` already lies in the
ambient `p`-core. -/
theorem exists_coatom_ge_normalizer_inf_map_pCore
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (x : G) (M N : Subgroup G)
    (hxM : x ∈ M) (hxN : x ∈ N)
    (hxMcore : (⟨x, hxM⟩ : M) ∈ pCore p M)
    (hxNcore : (⟨x, hxN⟩ : N) ∈ pCore p N)
    (hxnot : x ∉ pCore p G) :
    ∃ L : Subgroup G, IsCoatom L ∧
      Subgroup.normalizer
          (((pCore p M).map M.subtype ⊓
            (pCore p N).map N.subtype : Subgroup G) : Set G) ≤ L ∧
      x ∈ L := by
  let PM : Subgroup G := (pCore p M).map M.subtype
  let PN : Subgroup G := (pCore p N).map N.subtype
  let D : Subgroup G := PM ⊓ PN
  have hxPM : x ∈ PM :=
    ⟨⟨x, hxM⟩, hxMcore, rfl⟩
  have hxPN : x ∈ PN :=
    ⟨⟨x, hxN⟩, hxNcore, rfl⟩
  have hxD : x ∈ D :=
    ⟨hxPM, hxPN⟩
  have hDp : IsPGroup p D :=
    (pCore_isPGroup.map M.subtype).to_le inf_le_left
  have hNne : Subgroup.normalizer (D : Set G) ≠ ⊤ := by
    intro htop
    have hDnormal : D.Normal :=
      Subgroup.normalizer_eq_top_iff.mp htop
    apply hxnot
    exact le_pCore hDnormal hDp hxD
  rcases eq_top_or_exists_le_coatom (Subgroup.normalizer (D : Set G)) with
    htop | ⟨L, hL, hNL⟩
  · exact (hNne htop).elim
  · refine ⟨L, hL, hNL, ?_⟩
    exact hNL (D.le_normalizer hxD)

/-- Inductive form of `normalizer_map_pCore_eq_coatom`: the pairwise
Baer–Suzuki hypothesis supplies membership in the local `p`-core. -/
theorem normalizer_map_pCore_eq_coatom_of_induction
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hind : ∀ {K : Type u} [Group K] [Finite K],
      Nat.card K < Nat.card G → ∀ y : K,
        y ∈ pCore p K ↔
          ∀ k : K, IsPGroup p
            (Subgroup.closure ({y, k * y * k⁻¹} : Set K)))
    (x : G)
    (h : ∀ g : G, IsPGroup p
      (Subgroup.closure ({x, g * x * g⁻¹} : Set G)))
    (M : Subgroup G) (hM : IsCoatom M)
    (hxM : x ∈ M) (hxnot : x ∉ pCore p G) :
    Subgroup.normalizer
        ((pCore p M).map M.subtype : Set G) = M := by
  have hxcore : (⟨x, hxM⟩ : M) ∈ pCore p M :=
    mem_pCore_proper_subgroup_of_induction
      hind x M hxM hM.lt_top h
  exact normalizer_map_pCore_eq_coatom
    x M hM hxM hxcore hxnot

end Submission.Helpers
