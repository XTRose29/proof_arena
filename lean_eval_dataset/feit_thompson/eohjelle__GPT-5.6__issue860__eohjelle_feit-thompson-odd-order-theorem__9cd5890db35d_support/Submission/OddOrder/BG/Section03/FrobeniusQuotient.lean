import Submission.OddOrder.BG.Section03.FrobeniusPartition
import Submission.OddOrder.BG.Section03.FrobeniusQuotientComplement

/-!
Proper kernel quotients of finite Frobenius decompositions.
-/

namespace Submission.OddOrder.BG.Section03

universe u

variable {G : Type u} [Group G] [Finite G]
variable {K R N : Subgroup G}

namespace IsFrobeniusDecomposition

/-- The commutator map of a nonidentity complement element restricts to a
bijection on every ambient-normal subgroup of the kernel. -/
theorem restrictedKernelCommutatorMap_surjective
    (h : IsFrobeniusDecomposition K R) [N.Normal] (_hNK : N ≤ K)
    (r : R) (hr : r ≠ 1) :
    letI := h.conjugationAction
    let NK : Subgroup K := N.subgroupOf K
    let φK : K →* K := MulDistribMulAction.toMonoidHom K r
    let φN : NK →* NK :=
      { toFun := fun n ↦
          ⟨φK (n : K), by
            change (r : G) * (n : G) * (r : G)⁻¹ ∈ N
            exact (inferInstance : N.Normal).conj_mem (n : G) n.property (r : G)⟩
        map_one' := by
          apply Subtype.ext
          exact φK.map_one
        map_mul' := fun a b ↦ by
          apply Subtype.ext
          exact φK.map_mul a b }
    Function.Surjective (MonoidHom.commutatorMap φN) := by
  letI := h.conjugationAction
  let NK : Subgroup K := N.subgroupOf K
  let φK : K →* K := MulDistribMulAction.toMonoidHom K r
  let φN : NK →* NK :=
    { toFun := fun n ↦
        ⟨φK (n : K), by
          change (r : G) * (n : G) * (r : G)⁻¹ ∈ N
          exact (inferInstance : N.Normal).conj_mem (n : G) n.property (r : G)⟩
      map_one' := by
        apply Subtype.ext
        exact φK.map_one
      map_mul' := fun a b ↦ by
        apply Subtype.ext
        exact φK.map_mul a b }
  have hfixedN : MonoidHom.FixedPointFree φN := by
    intro n hn
    apply Subtype.ext
    apply h.fixedPointFree r hr (n : K)
    exact congrArg (fun x : NK ↦ ((x : K) : G)) hn
  exact hfixedN.commutatorMap_surjective

/-- Bender-Glauberman Lemma 3.2(b): quotienting a finite Frobenius
decomposition by a proper ambient-normal subgroup of its kernel preserves the
Frobenius decomposition. -/
theorem quotient
    (h : IsFrobeniusDecomposition K R) [N.Normal] (hNK : N < K) :
    IsFrobeniusDecomposition
      (K.map (QuotientGroup.mk' N))
      (R.map (QuotientGroup.mk' N)) := by
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  apply h.quotient_decomposition_of_fixedPointFree hNK
  intro rq hrq kq hkq
  rcases rq.property with ⟨r, hr, hrEq⟩
  rcases kq.property with ⟨k, hk, hkEq⟩
  let rR : R := ⟨r, hr⟩
  let kK : K := ⟨k, hk⟩
  have hrR : rR ≠ 1 := by
    intro hrOne
    apply hrq
    apply Subtype.ext
    rw [← hrEq]
    have hrOneG : r = 1 := congrArg Subtype.val hrOne
    rw [hrOneG, map_one]
    rfl
  letI := h.conjugationAction
  let NK : Subgroup K := N.subgroupOf K
  let φK : K →* K := MulDistribMulAction.toMonoidHom K rR
  let φN : NK →* NK :=
    { toFun := fun n ↦
        ⟨φK (n : K), by
          change r * (n : G) * r⁻¹ ∈ N
          exact (inferInstance : N.Normal).conj_mem (n : G) n.property r⟩
      map_one' := by
        apply Subtype.ext
        exact φK.map_one
      map_mul' := fun a b ↦ by
        apply Subtype.ext
        exact φK.map_mul a b }
  have hqfix := hkq
  rw [← hrEq, ← hkEq] at hqfix
  have hqfix' : q (r * k * r⁻¹) = q k := by
    simpa only [map_mul, map_inv] using hqfix
  have herr : (r * k * r⁻¹)⁻¹ * k ∈ N :=
    QuotientGroup.eq.mp hqfix'
  have hcommN : ((kK : K) / φK kK : K) ∈ NK := by
    change (((kK / φK kK : K) : K) : G) ∈ N
    rw [div_eq_mul_inv]
    change k * (((rR • kK : K) : G))⁻¹ ∈ N
    rw [h.coe_smul]
    change k * (r * k * r⁻¹)⁻¹ ∈ N
    have hconj :
        (r * k * r⁻¹) * ((r * k * r⁻¹)⁻¹ * k) *
            (r * k * r⁻¹)⁻¹ ∈ N :=
      (inferInstance : N.Normal).conj_mem
        ((r * k * r⁻¹)⁻¹ * k) herr (r * k * r⁻¹)
    convert hconj using 1; group
  obtain ⟨n, hn⟩ := h.restrictedKernelCommutatorMap_surjective hNK.1 rR hrR
    ⟨(kK / φK kK : K), hcommN⟩
  have hnK : MonoidHom.commutatorMap φK (n : K) =
      MonoidHom.commutatorMap φK kK := by
    apply Subtype.ext
    have hnVal := congrArg (fun x : NK ↦ ((x : K) : G)) hn
    exact hnVal
  have hkEqN : (n : K) = kK :=
    (h.kernelConjugation_fixedPointFree rR hrR).commutatorMap_injective hnK
  have hkN : k ∈ N := by
    have := n.property
    rwa [hkEqN] at this
  apply Subtype.ext
  rw [← hkEq]
  exact (QuotientGroup.eq_one_iff (N := N) k).mpr hkN

end IsFrobeniusDecomposition

end Submission.OddOrder.BG.Section03
