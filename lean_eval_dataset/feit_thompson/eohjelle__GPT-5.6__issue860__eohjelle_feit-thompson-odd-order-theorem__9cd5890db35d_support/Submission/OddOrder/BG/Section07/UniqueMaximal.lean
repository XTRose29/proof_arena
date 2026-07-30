import Submission.OddOrder.BG.Section07.MaximalSubgroups

/-!
# Bender--Glauberman, Section 7: unique maximal overgroups

This ports the consecutive `BGsection7.v` block from conjugation invariance
of maximal subgroups through upward closure of the family `'U`.
-/

namespace Submission.OddOrder.BG.Section07

universe u

variable {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]

/-- Maximality is invariant under every group automorphism (in particular,
under conjugation). -/
theorem mmaxJ (M : Subgroup G) (e : G ≃* G) :
    M.map e.toMonoidHom ∈ minSimple_max_groups (G := G) ↔
      M ∈ minSimple_max_groups (G := G) := by
  change IsCoatom (M.map e.toMonoidHom) ↔ IsCoatom M
  exact OrderIso.isCoatom_iff e.mapSubgroup M

/-- Enlarging the prescribed subgroup shrinks its family of maximal
overgroups. -/
theorem mmax_ofS {H K : Subgroup G} (hHK : H ≤ K) :
    minSimple_max_groups_of (G := G) (K : Set G) ⊆
      minSimple_max_groups_of (G := G) (H : Set G) := by
  intro M hM
  exact ⟨hM.1, hHK.trans hM.2⟩

/-- The family of maximal overgroups is equivariant under automorphisms. -/
theorem mmax_ofJ (K M : Subgroup G) (e : G ≃* G) :
    M.map e.toMonoidHom ∈
        minSimple_max_groups_of (G := G)
          (K.map e.toMonoidHom : Set G) ↔
      M ∈ minSimple_max_groups_of (G := G) (K : Set G) := by
  change (IsCoatom (M.map e.toMonoidHom) ∧
      K.map e.toMonoidHom ≤ M.map e.toMonoidHom) ↔
    IsCoatom M ∧ K ≤ M
  constructor
  · rintro ⟨hM, hKM⟩
    exact ⟨(mmaxJ M e).mp hM,
      (Subgroup.map_le_map_iff_of_injective e.injective).mp hKM⟩
  · rintro ⟨hM, hKM⟩
    exact ⟨(mmaxJ M e).mpr hM,
      (Subgroup.map_le_map_iff_of_injective e.injective).mpr hKM⟩

/-- Membership in `'U` is equivalent to having a singleton family of
maximal overgroups. -/
theorem uniq_mmaxP (U : Subgroup G) :
    U ∈ minSimple_uniq_max_groups (G := G) ↔
      ∃ M : Subgroup G,
        minSimple_max_groups_of (G := G) (U : Set G) = {M} := by
  change (minSimple_max_groups_of (G := G) (U : Set G)).ncard = 1 ↔ _
  exact Set.ncard_eq_one

/-- The unique maximal overgroup is maximal and contains the subgroup. -/
theorem mem_uniq_mmax {U M : Subgroup G}
    (hU : minSimple_max_groups_of (G := G) (U : Set G) = {M}) :
    M ∈ minSimple_max_groups (G := G) ∧ U ≤ M := by
  have hmem : M ∈ minSimple_max_groups_of (G := G) (U : Set G) := by
    rw [hU]
    exact Set.mem_singleton M
  exact hmem

/-- Any maximal overgroup of `U` is its prescribed unique one. -/
theorem eq_uniq_mmax {U M H : Subgroup G}
    (hU : minSimple_max_groups_of (G := G) (U : Set G) = {M})
    (hH : H ∈ minSimple_max_groups (G := G)) (hUH : U ≤ H) :
    H = M := by
  have hmem : H ∈ minSimple_max_groups_of (G := G) (U : Set G) := ⟨hH, hUH⟩
  rw [hU] at hmem
  exact Set.mem_singleton_iff.mp hmem

/-- A member of `'U` and one of its maximal overgroups determine its
singleton family. -/
theorem def_uniq_mmax {U M : Subgroup G}
    (hU : U ∈ minSimple_uniq_max_groups (G := G))
    (hM : M ∈ minSimple_max_groups (G := G)) (hUM : U ≤ M) :
    minSimple_max_groups_of (G := G) (U : Set G) = {M} := by
  rcases (uniq_mmaxP U).mp hU with ⟨D, hD⟩
  have hMmem : M ∈ minSimple_max_groups_of (G := G) (U : Set G) := ⟨hM, hUM⟩
  have hMD : M = D := by
    rw [hD] at hMmem
    exact Set.mem_singleton_iff.mp hMmem
  simpa [hMD] using hD

/-- With a known maximal overgroup, uniqueness is equivalent to every
maximal overgroup being that one. -/
theorem uniq_mmax_subset1 {U M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) (hUM : U ≤ M) :
    U ∈ minSimple_uniq_max_groups (G := G) ↔
      minSimple_max_groups_of (G := G) (U : Set G) ⊆ {M} := by
  constructor
  · intro hU
    rw [def_uniq_mmax hU hM hUM]
  · intro hsub
    apply (uniq_mmaxP U).mpr
    refine ⟨M, Set.Subset.antisymm hsub ?_⟩
    rw [Set.singleton_subset_iff]
    exact ⟨hM, hUM⟩

/-- Every proper overgroup of a uniquely-maximal subgroup lies in its unique
maximal overgroup. -/
theorem sub_uniq_mmax {U M H : Subgroup G}
    (hU : minSimple_max_groups_of (G := G) (U : Set G) = {M})
    (hUH : U ≤ H) (hH : H < ⊤) : H ≤ M := by
  rcases mmax_exists H hH with ⟨D, hD, hHD⟩
  have hDmem : D ∈ minSimple_max_groups_of (G := G) (U : Set G) :=
    ⟨hD, hUH.trans hHD⟩
  have hDM : D = M := by
    rw [hU] at hDmem
    exact Set.mem_singleton_iff.mp hDmem
  simpa [hDM] using hHD

/-- A maximal subgroup has itself as its only maximal overgroup. -/
theorem mmax_sup_id {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    minSimple_max_groups_of (G := G) (M : Set G) = {M} := by
  ext H
  constructor
  · intro hH
    have hEq : H = M := mmax_max hM (mmax_proper hH.1) hH.2
    simpa [hEq]
  · intro hH
    have hEq : H = M := Set.mem_singleton_iff.mp hH
    subst H
    exact ⟨hM, le_rfl⟩

/-- Every maximal subgroup belongs to `'U`. -/
theorem mmax_uniq_id {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    M ∈ minSimple_uniq_max_groups (G := G) :=
  (uniq_mmaxP M).mpr ⟨M, mmax_sup_id hM⟩

/-- A singleton family of maximal overgroups transports under an
automorphism. -/
theorem def_uniq_mmaxJ {K M : Subgroup G} (e : G ≃* G)
    (hK : minSimple_max_groups_of (G := G) (K : Set G) = {M}) :
    minSimple_max_groups_of (G := G)
        (K.map e.toMonoidHom : Set G) = {M.map e.toMonoidHom} := by
  ext L
  let L₀ : Subgroup G := L.comap e.toMonoidHom
  have hL₀ : L₀.map e.toMonoidHom = L :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective L
  constructor
  · intro hL
    have hback : L₀ ∈ minSimple_max_groups_of (G := G) (K : Set G) := by
      apply (mmax_ofJ K L₀ e).mp
      rw [hL₀]
      exact hL
    have hL₀M : L₀ = M := by
      rw [hK] at hback
      exact Set.mem_singleton_iff.mp hback
    rw [Set.mem_singleton_iff, ← hL₀, hL₀M]
  · intro hL
    have hLM : L = M.map e.toMonoidHom := Set.mem_singleton_iff.mp hL
    rw [hLM]
    apply (mmax_ofJ K M e).mpr
    rw [hK]
    exact Set.mem_singleton M

/-- The property of having a unique maximal overgroup is invariant under
automorphisms. -/
theorem uniq_mmaxJ (K : Subgroup G) (e : G ≃* G) :
    K.map e.toMonoidHom ∈ minSimple_uniq_max_groups (G := G) ↔
      K ∈ minSimple_uniq_max_groups (G := G) := by
  constructor
  · intro hKe
    rcases (uniq_mmaxP (K.map e.toMonoidHom)).mp hKe with ⟨M, hM⟩
    have hback := def_uniq_mmaxJ e.symm hM
    have hKK : (K.map e.toMonoidHom).map e.symm.toMonoidHom = K := by
      ext x
      simp
    rw [hKK] at hback
    exact (uniq_mmaxP K).mpr ⟨M.map e.symm.toMonoidHom, hback⟩
  · intro hK
    rcases (uniq_mmaxP K).mp hK with ⟨M, hM⟩
    exact (uniq_mmaxP (K.map e.toMonoidHom)).mpr
      ⟨M.map e.toMonoidHom, def_uniq_mmaxJ e hM⟩

/-- The normalizer of a uniquely-maximal subgroup lies in its unique maximal
overgroup. -/
theorem uniq_mmax_norm_sub {U M : Subgroup G}
    (hU : minSimple_max_groups_of (G := G) (U : Set G) = {M}) :
    Subgroup.normalizer (U : Set G) ≤ M := by
  have hM : M ∈ minSimple_max_groups (G := G) := (mem_uniq_mmax hU).1
  intro x hx
  rw [← norm_mmax hM, Subgroup.mem_normalizer_iff_map_conj_eq]
  let e : G ≃* G := MulAut.conj x
  have hUmap : U.map e.toMonoidHom = U :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hx
  have htransport := def_uniq_mmaxJ e hU
  rw [hUmap, hU] at htransport
  exact (Set.singleton_injective htransport).symm

/-- A subgroup with a unique maximal overgroup is nontrivial. -/
theorem uniq_mmax_neq1 {U : Subgroup G}
    (hU : U ∈ minSimple_uniq_max_groups (G := G)) : U ≠ ⊥ := by
  rcases (uniq_mmaxP U).mp hU with ⟨M, hUM⟩
  have hM : M ∈ minSimple_max_groups (G := G) := (mem_uniq_mmax hUM).1
  intro hUbot
  have htopM := uniq_mmax_norm_sub hUM
  have hnormBot :
      Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
    Subgroup.normalizer_eq_top (⊥ : Subgroup G)
  rw [hUbot, hnormBot] at htopM
  exact (mmax_proper hM).ne (top_unique htopM)

/-- The same unique maximal subgroup remains unique after passing to a
proper overgroup. -/
theorem def_uniq_mmaxS {M U V : Subgroup G}
    (hUV : U ≤ V) (hV : V < ⊤)
    (hU : minSimple_max_groups_of (G := G) (U : Set G) = {M}) :
    minSimple_max_groups_of (G := G) (V : Set G) = {M} := by
  apply Set.Subset.antisymm
  · intro D hD
    have hDU : D ∈ minSimple_max_groups_of (G := G) (U : Set G) :=
      mmax_ofS hUV hD
    simpa [hU] using hDU
  · rw [Set.singleton_subset_iff]
    have hM := mem_uniq_mmax hU
    exact ⟨hM.1, sub_uniq_mmax hU hUV hV⟩

/-- The family `'U` is upward closed among proper subgroups. -/
theorem uniq_mmaxS {U V : Subgroup G}
    (hUV : U ≤ V) (hV : V < ⊤)
    (hU : U ∈ minSimple_uniq_max_groups (G := G)) :
    V ∈ minSimple_uniq_max_groups (G := G) := by
  rcases (uniq_mmaxP U).mp hU with ⟨M, hM⟩
  exact (uniq_mmaxP V).mpr ⟨M, def_uniq_mmaxS hUV hV hM⟩

end Submission.OddOrder.BG.Section07
