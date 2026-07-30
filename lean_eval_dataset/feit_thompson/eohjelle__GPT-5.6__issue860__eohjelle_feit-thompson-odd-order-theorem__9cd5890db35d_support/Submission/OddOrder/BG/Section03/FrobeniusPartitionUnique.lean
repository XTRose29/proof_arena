import Submission.OddOrder.BG.Section03.FrobeniusNormalSubgroup

/-!
Uniqueness in the finite Frobenius partition.
-/

namespace Submission.OddOrder.BG.Section03

universe u

variable {G : Type u} [Group G] [Finite G]
variable {K R : Subgroup G}

namespace IsFrobeniusDecomposition

/-- Every element outside the Frobenius kernel belongs to a unique conjugate
of the complement by a kernel element. -/
theorem existsUnique_kernel_conjugate_complement_of_not_mem
    (h : IsFrobeniusDecomposition K R) {g : G} (hg : g ∉ K) :
    ∃! x : K, g ∈ R.map (MulAut.conj (x : G)).toMonoidHom := by
  obtain ⟨x, hx⟩ := h.exists_kernel_conjugate_complement_of_not_mem hg
  refine ⟨x, hx, ?_⟩
  intro y hy
  by_contra hxy
  let a : G := (x : G)⁻¹ * (y : G)
  have haK : a ∈ K := K.mul_mem (K.inv_mem x.property) y.property
  have haNotR : a ∉ R := by
    intro haR
    have haOne : a = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← disjoint_iff.mp h.disjoint]
      exact ⟨haK, haR⟩
    apply hxy
    apply Subtype.ext
    exact (inv_mul_eq_one.mp haOne).symm
  rcases hx with ⟨rx, hrx, hrxEq⟩
  rcases hy with ⟨ry, hry, hryEq⟩
  have hryEq' : (y : G) * ry * (y : G)⁻¹ = g := by
    exact hryEq
  let t : G := (x : G)⁻¹ * g * (x : G)
  have htR : t ∈ R := by
    have htEq : t = rx := by
      dsimp [t]
      rw [← hrxEq]
      change (x : G)⁻¹ * ((x : G) * rx * (x : G)⁻¹) * (x : G) = rx
      group
    rwa [htEq]
  have htConj : t ∈ R.map (MulAut.conj a).toMonoidHom := by
    refine ⟨ry, hry, ?_⟩
    change a * ry * a⁻¹ = t
    dsimp [a, t]
    rw [← hryEq']
    group
  have htNe : t ≠ 1 := by
    intro htOne
    apply hg
    have hgOne : g = 1 := by
      have : (x : G) * t * (x : G)⁻¹ = g := by
        dsimp [t]
        group
      rw [← this, htOne]
      simp
    rw [hgOne]
    exact K.one_mem
  have htBot : t ∈ (⊥ : Subgroup G) := by
    rw [← disjoint_iff.mp
      (h.disjoint_complement_conjugate_of_not_mem haNotR)]
    exact ⟨htR, htConj⟩
  exact htNe (Subgroup.mem_bot.mp htBot)

end IsFrobeniusDecomposition

end Submission.OddOrder.BG.Section03
