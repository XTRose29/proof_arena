import Mathlib.GroupTheory.FixedPointFree
import Submission.OddOrder.BG.Section03.FrobeniusNormalizer

/-!
The commutator-map and partition consequences of a finite Frobenius
decomposition.
-/

namespace Submission.OddOrder.BG.Section03

universe u

variable {G : Type u} [Group G]
variable {K R : Subgroup G}

namespace IsFrobeniusDecomposition

/-- Conjugation by a nonidentity complement element is a fixed-point-free
endomorphism of the kernel. -/
theorem kernelConjugation_fixedPointFree
    (h : IsFrobeniusDecomposition K R) (r : R) (hr : r ≠ 1) :
    letI := h.conjugationAction
    MonoidHom.FixedPointFree
      (MulDistribMulAction.toMonoidHom K r) := by
  letI := h.conjugationAction
  intro k hk
  exact h.smul_eq_imp_eq_one r hr k hk

variable [Finite G]

/-- The kernel commutator map attached to a nonidentity complement element
is surjective. -/
theorem kernelCommutatorMap_surjective
    (h : IsFrobeniusDecomposition K R) (r : R) (hr : r ≠ 1) :
    letI := h.conjugationAction
    Function.Surjective
      (MonoidHom.commutatorMap
        (MulDistribMulAction.toMonoidHom K r)) := by
  letI := h.conjugationAction
  exact (h.kernelConjugation_fixedPointFree r hr).commutatorMap_surjective

/-- Every element outside the kernel lies in a conjugate of the Frobenius
complement by a kernel element. This is the covering half of the Frobenius
partition. -/
theorem mem_kernel_or_conjugate_complement
    (h : IsFrobeniusDecomposition K R) (g : G) :
    g ∈ K ∨ ∃ x : K,
      g ∈ R.map (MulAut.conj (x : G)).toMonoidHom := by
  rcases h.existsUnique_kernel_mul_complement g with
    ⟨⟨k, r⟩, hkr, _⟩
  by_cases hr : r = 1
  · left
    rw [← hkr, hr]
    simpa only [Prod.fst, Prod.snd, Subgroup.coe_one, mul_one] using k.property
  · right
    letI := h.conjugationAction
    obtain ⟨x, hx⟩ := h.kernelCommutatorMap_surjective r hr k
    refine ⟨x, ⟨(r : G), r.property, ?_⟩⟩
    have hxG := congrArg Subtype.val hx
    rw [MonoidHom.commutatorMap_apply] at hxG
    change (x : G) / ((r • x : K) : G) = (k : G) at hxG
    rw [h.coe_smul] at hxG
    rw [div_eq_mul_inv] at hxG
    change (x : G) * (r : G) * (x : G)⁻¹ = g
    calc
      (x : G) * (r : G) * (x : G)⁻¹ =
          ((x : G) * ((r : G) * (x : G) * (r : G)⁻¹)⁻¹) *
            (r : G) := by group
      _ = (k : G) * (r : G) := by rw [hxG]
      _ = g := hkr

/-- Elements outside the kernel lie in conjugates of the complement by
kernel elements. -/
theorem exists_kernel_conjugate_complement_of_not_mem
    (h : IsFrobeniusDecomposition K R) {g : G} (hg : g ∉ K) :
    ∃ x : K, g ∈ R.map (MulAut.conj (x : G)).toMonoidHom :=
  (h.mem_kernel_or_conjugate_complement g).resolve_left hg

end IsFrobeniusDecomposition

end Submission.OddOrder.BG.Section03
