import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
Lifting a generator of a cyclic quotient.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G]

/-- A generator of `G / H` can be lifted so that every element of `G` is a
power of the lift modulo `H`. -/
theorem exists_generator_mod_normal (H : Subgroup G) [H.Normal]
    [IsCyclic (G ⧸ H)] :
    ∃ x : G, ∀ g : G, ∃ n : ℤ, g * (x ^ n)⁻¹ ∈ H := by
  obtain ⟨q, hq⟩ := IsCyclic.exists_generator (α := G ⧸ H)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H q
  refine ⟨x, fun g ↦ ?_⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hq (g : G ⧸ H))
  refine ⟨n, (QuotientGroup.eq_one_iff _).mp ?_⟩
  change (g : G ⧸ H) * ((x : G ⧸ H) ^ n)⁻¹ = 1
  rw [← hn]
  simp

/-- A lift of a cyclic quotient generator, together with the normal subgroup,
generates the ambient group. -/
theorem exists_zpowers_sup_eq_top_of_quotient_isCyclic
    (H : Subgroup G) [H.Normal] [IsCyclic (G ⧸ H)] :
    ∃ x : G, Subgroup.zpowers x ⊔ H = ⊤ := by
  obtain ⟨x, hx⟩ := exists_generator_mod_normal H
  refine ⟨x, top_unique fun g _ ↦ ?_⟩
  obtain ⟨n, hn⟩ := hx g
  have hmod : g * (x ^ n)⁻¹ ∈ Subgroup.zpowers x ⊔ H :=
    (le_sup_right : H ≤ Subgroup.zpowers x ⊔ H) hn
  have hpow : x ^ n ∈ Subgroup.zpowers x ⊔ H :=
    (le_sup_left : Subgroup.zpowers x ≤ Subgroup.zpowers x ⊔ H)
      (Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩)
  simpa [mul_assoc] using (Subgroup.mul_mem _ hmod hpow)

end Submission.OddOrder.MathlibSupport
