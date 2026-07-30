import Submission.OddOrder.BG.Section03.FrobeniusQuotient

/-!
Normal-subgroup dichotomy for finite Frobenius decompositions.
-/

namespace Submission.OddOrder.BG.Section03

universe u

variable {G : Type u} [Group G] [Finite G]
variable {K R N : Subgroup G}

namespace IsFrobeniusDecomposition

/-- Every ambient normal subgroup is either contained in the Frobenius kernel
or contains it. -/
theorem normal_le_kernel_or_kernel_le
    (h : IsFrobeniusDecomposition K R) [N.Normal] :
    N ≤ K ∨ K ≤ N := by
  by_cases hNK : N ≤ K
  · exact Or.inl hNK
  · right
    obtain ⟨n, hnN, hnK⟩ := SetLike.not_le_iff_exists.mp hNK
    obtain ⟨x, hxn⟩ := h.exists_kernel_conjugate_complement_of_not_mem hnK
    rcases hxn with ⟨r, hr, hrEq⟩
    let rR : R := ⟨r, hr⟩
    have hrR : rR ≠ 1 := by
      intro hrOne
      apply hnK
      have hrOneG : r = 1 := congrArg Subtype.val hrOne
      have hnOne : n = 1 := by
        rw [← hrEq, hrOneG]
        simp
      rw [hnOne]
      exact K.one_mem
    have hrN : r ∈ N := by
      have hnConj : (x : G)⁻¹ * n * (x : G) ∈ N :=
        (inferInstance : N.Normal).conj_mem' n hnN (x : G)
      have hrConj : (x : G)⁻¹ * n * (x : G) = r := by
        rw [← hrEq]
        change (x : G)⁻¹ * ((x : G) * r * (x : G)⁻¹) * (x : G) = r
        group
      rwa [hrConj] at hnConj
    intro k hk
    let kK : K := ⟨k, hk⟩
    letI := h.conjugationAction
    let φK : K →* K := MulDistribMulAction.toMonoidHom K rR
    obtain ⟨y, hy⟩ := h.kernelCommutatorMap_surjective rR hrR kK
    have hyG := congrArg Subtype.val hy
    rw [MonoidHom.commutatorMap_apply, div_eq_mul_inv] at hyG
    change (y : G) * (((rR • y : K) : G))⁻¹ = k at hyG
    rw [h.coe_smul] at hyG
    rw [← hyG]
    change (y : G) * (r * (y : G) * r⁻¹)⁻¹ ∈ N
    have hyrN : (y : G) * r * (y : G)⁻¹ ∈ N :=
      (inferInstance : N.Normal).conj_mem r hrN (y : G)
    convert N.mul_mem hyrN (N.inv_mem hrN) using 1; group

/-- Bender-Glauberman Lemma 3.2(a): a normal subgroup not containing the
Frobenius kernel is a proper subgroup of it. -/
theorem normal_proper_kernel
    (h : IsFrobeniusDecomposition K R) [N.Normal]
    (hnot : ¬ K ≤ N) :
    N < K := by
  exact ⟨h.normal_le_kernel_or_kernel_le.resolve_right hnot, hnot⟩

/-- Bender-Glauberman Lemma 3.2(b), in the source theorem's hypothesis form:
a normal quotient whose kernel does not contain the Frobenius kernel is again
Frobenius. -/
theorem quotient_of_not_kernel_le
    (h : IsFrobeniusDecomposition K R) [N.Normal]
    (hnot : ¬ K ≤ N) :
    IsFrobeniusDecomposition
      (K.map (QuotientGroup.mk' N))
      (R.map (QuotientGroup.mk' N)) :=
  h.quotient (h.normal_proper_kernel hnot)

end IsFrobeniusDecomposition

end Submission.OddOrder.BG.Section03
