import Mathlib.GroupTheory.Sylow

/-!
Sylow subgroups and intersections with normal subgroups.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem exists_sylow_eq_comap_normal {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (K : Subgroup G) [K.Normal] :
    ∃ Q : Sylow p K, (Q : Subgroup K) = (S : Subgroup G).comap K.subtype := by
  let Q₀ : Sylow p K := Classical.choice Sylow.nonempty
  obtain ⟨T, hT⟩ := Q₀.exists_comap_subtype_eq
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
  let e : MulAut K := MulAut.conjNormal g
  refine ⟨e • Q₀, ?_⟩
  change e • (Q₀ : Subgroup K) = (S : Subgroup G).comap K.subtype
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  rw [← hT]
  change ((e⁻¹) x : G) ∈ T ↔ (x : G) ∈ S
  rw [← hg]
  change ((e⁻¹) x : G) ∈ T ↔
    (x : G) ∈ MulAut.conj g • (T : Subgroup G)
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [e, MulAut.smul_def]
  rfl

/-- A Sylow subgroup of a normal subgroup obtained by intersecting an ambient Sylow
subgroup with it. -/
noncomputable def normalIntersectionSylow {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (K : Subgroup G) [K.Normal] : Sylow p K :=
  Classical.choose (exists_sylow_eq_comap_normal S K)

@[simp]
theorem coe_normalIntersectionSylow {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (K : Subgroup G) [K.Normal] :
    (normalIntersectionSylow S K : Subgroup K) =
      (S : Subgroup G).comap K.subtype :=
  Classical.choose_spec (exists_sylow_eq_comap_normal S K)

@[simp]
theorem map_normalIntersectionSylow_eq_inf {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (K : Subgroup G) [K.Normal] :
    (normalIntersectionSylow S K : Subgroup K).map K.subtype =
      (S : Subgroup G) ⊓ K := by
  rw [coe_normalIntersectionSylow]
  exact Subgroup.subgroupOf_map_subtype (S : Subgroup G) K

end Submission.OddOrder.MathlibSupport
