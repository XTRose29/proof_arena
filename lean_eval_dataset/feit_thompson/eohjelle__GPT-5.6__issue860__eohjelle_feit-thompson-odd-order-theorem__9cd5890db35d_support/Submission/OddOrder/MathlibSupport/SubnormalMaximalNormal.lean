import Mathlib.GroupTheory.IsSubnormal
import Mathlib.GroupTheory.QuotientGroup.Finite

/-!
Maximal proper normal subgroups above a proper subnormal subgroup.

This is the small subgroup-chain bridge used in the proof of
Bender--Glauberman Lemma 7.4.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

/-- A normal subgroup which is proper and maximal among proper normal
subgroups. -/
structure IsMaximalProperNormal {G : Type u} [Group G]
    (M : Subgroup G) : Prop where
  normal : M.Normal
  proper : M < ⊤
  eq_self_or_top_of_normal_of_le :
    ∀ N : Subgroup G, N.Normal → M ≤ N → N = M ∨ N = ⊤

/-- A proper subnormal subgroup of a finite group is contained in an
intermediate subgroup which is maximal proper normal in the ambient subgroup.
-/
theorem exists_maximalProperNormal_intermediate_of_isSubnormal
    {G : Type u} [Group G] [Finite G] {A P : Subgroup G}
    (hAP : A ≤ P) (hsub : (A.subgroupOf P).IsSubnormal)
    (hne : A ≠ P) :
    ∃ B : Subgroup G, A ≤ B ∧ B < P ∧
      (A.subgroupOf B).IsSubnormal ∧
      IsMaximalProperNormal (B.subgroupOf P) := by
  have hAneTop : A.subgroupOf P ≠ ⊤ := by
    intro htop
    have hPA : P ≤ A := Subgroup.subgroupOf_eq_top.mp htop
    exact hne (le_antisymm hAP hPA)
  obtain ⟨C, hCnormal, hAC, hCproper⟩ :=
    hsub.exists_normal_and_le_and_lt_top_of_ne hAneTop
  let Good : Subgroup P → Prop := fun N ↦
    N.Normal ∧ C ≤ N ∧ N < ⊤
  have hCgood : Good C := ⟨hCnormal, le_rfl, hCproper⟩
  letI : Finite (Subgroup P) :=
    Finite.of_injective (fun N : Subgroup P ↦ (N : Set P))
      SetLike.coe_injective
  obtain ⟨M, _hCM, hMgood, hMmax⟩ :=
    Finite.exists_le_maximal (p := Good) hCgood
  have hMmaximal : IsMaximalProperNormal M := by
    refine
      { normal := hMgood.1
        proper := hMgood.2.2
        eq_self_or_top_of_normal_of_le := ?_ }
    intro N hNnormal hMN
    by_cases hNtop : N = ⊤
    · exact Or.inr hNtop
    · left
      apply le_antisymm
      · exact hMmax
          ⟨hNnormal, hMgood.2.1.trans hMN,
            lt_top_iff_ne_top.mpr hNtop⟩ hMN
      · exact hMN
  let B : Subgroup G := M.map P.subtype
  have hBsubgroupOf : B.subgroupOf P = M := by
    change (M.map P.subtype).comap P.subtype = M
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective M
  have hBP : B ≤ P := by
    change M.map P.subtype ≤ P
    exact (Subgroup.map_le_range P.subtype M).trans_eq P.range_subtype
  have hAM : A.subgroupOf P ≤ M := hAC.trans hMgood.2.1
  have hAB : A ≤ B := by
    change A ≤ M.map P.subtype
    rw [← Subgroup.map_subgroupOf_eq_of_le hAP]
    exact Subgroup.map_mono hAM
  have hBneP : B ≠ P := by
    intro hBP'
    apply hMgood.2.2.ne
    rw [← hBsubgroupOf, hBP']
    exact Subgroup.subgroupOf_self P
  have hBltP : B < P := lt_of_le_of_ne hBP hBneP
  have hsubB : (A.subgroupOf B).IsSubnormal := by
    simpa only [Subgroup.comap_inclusion_subgroupOf] using
      hsub.comap (Subgroup.inclusion hBP)
  have hBmaximal : IsMaximalProperNormal (B.subgroupOf P) := by
    rw [hBsubgroupOf]
    exact hMmaximal
  exact ⟨B, hAB, hBltP, hsubB, hBmaximal⟩

/-- The quotient by a maximal proper normal subgroup is simple. -/
theorem IsMaximalProperNormal.isSimpleGroup_quotient
    {G : Type u} [Group G] {M : Subgroup G} [M.Normal]
    (hM : IsMaximalProperNormal M) : IsSimpleGroup (G ⧸ M) := by
  letI : Nontrivial (G ⧸ M) := QuotientGroup.nontrivial_iff.mpr hM.proper.ne
  refine ⟨fun K _ ↦ ?_⟩
  let N : Subgroup G := K.comap (QuotientGroup.mk' M)
  have hNnormal : N.Normal := by
    dsimp only [N]
    infer_instance
  have hMN : M ≤ N := QuotientGroup.le_comap_mk' M K
  rcases hM.eq_self_or_top_of_normal_of_le N hNnormal hMN with hNM | hNtop
  · left
    apply Subgroup.comap_injective (QuotientGroup.mk'_surjective M)
    simpa only [N, MonoidHom.comap_bot, QuotientGroup.ker_mk'] using hNM
  · right
    apply Subgroup.comap_injective (QuotientGroup.mk'_surjective M)
    simpa only [N, Subgroup.comap_top] using hNtop

end Submission.OddOrder.MathlibSupport
