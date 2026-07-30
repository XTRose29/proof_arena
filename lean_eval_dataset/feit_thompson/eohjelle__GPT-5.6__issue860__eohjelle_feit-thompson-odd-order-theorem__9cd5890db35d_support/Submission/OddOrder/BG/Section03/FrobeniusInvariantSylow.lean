import Mathlib.GroupTheory.SchurZassenhaus
import Submission.OddOrder.BG.Section03.PrimeProductComplementConjugacy

/-!
Invariant Sylow subgroups of a Frobenius kernel with prime-product
complement.
-/

namespace Submission.OddOrder.BG.Section03

universe u

variable {G : Type u} [Group G] [Finite G]
variable {K R : Subgroup G}
variable {p q ell : ℕ}

namespace IsFrobeniusDecomposition

/-- Every prime divisor of the Frobenius kernel has a nontrivial Sylow
subgroup normalized by a prime-product complement. -/
theorem exists_invariant_pSubgroup_of_natCard_eq_mul_primes
    (h : IsFrobeniusDecomposition K R)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hcard : Nat.card R = p * q)
    (hell : ell.Prime) (hellK : ell ∣ Nat.card K) :
    ∃ S : Subgroup G,
      S ≤ K ∧ S ≠ ⊥ ∧ IsPGroup ell S ∧
        R ≤ Subgroup.normalizer (S : Set G) := by
  letI : Fact ell.Prime := ⟨hell⟩
  let Pk : Sylow ell K := default
  let P : Subgroup G := (Pk : Subgroup K).map K.subtype
  have hPkne : (Pk : Subgroup K) ≠ ⊥ := Pk.ne_bot_of_dvd_card hellK
  have hPne : P ≠ ⊥ := by
    intro hbot
    apply hPkne
    exact (Subgroup.map_eq_bot_iff_of_injective (Pk : Subgroup K)
      K.subtype_injective).mp hbot
  letI : K.Normal := h.kernel_normal
  have hfrattini : Subgroup.normalizer (P : Set G) ⊔ K = ⊤ := by
    simpa [P] using Pk.normalizer_sup_eq_top
  let N : Subgroup G := Subgroup.normalizer (P : Set G)
  let KN : Subgroup N := K.comap N.subtype
  letI : KN.Normal := by
    dsimp [KN]
    infer_instance
  have hindex : KN.index = K.index := by
    dsimp [KN]
    rw [← K.relIndex_top_right, ← hfrattini]
    exact (Subgroup.relIndex_sup_right N K).symm
  have hcardKNdiv : Nat.card KN ∣ Nat.card K :=
    Subgroup.card_comap_dvd_of_injective K N.subtype N.subtype_injective
  have hcopKN : Nat.Coprime (Nat.card KN) KN.index := by
    rw [hindex, h.isComplement.symm.index_eq_card]
    exact h.natCard_coprime.coprime_dvd_left hcardKNdiv
  obtain ⟨C, hC⟩ := KN.exists_right_complement'_of_coprime hcopKN
  let B : Subgroup G := C.map N.subtype
  have hcardC : Nat.card C = Nat.card R := by
    rw [← hC.symm.index_eq_card, hindex,
      h.isComplement.symm.index_eq_card]
  have hcardB : Nat.card B = Nat.card R := by
    rw [Subgroup.card_map_of_injective (K := C) N.subtype_injective]
    exact hcardC
  have hBcomp : K.IsComplement' B := by
    apply Subgroup.isComplement'_of_coprime
    · rw [hcardB]
      exact h.card_mul_card
    · rw [hcardB]
      exact h.natCard_coprime
  obtain ⟨x, hBx⟩ :=
    h.complement_eq_kernel_conjugate_of_natCard_eq_mul_primes
      hp hq hpq hcard hBcomp
  have hBnormP : B ≤ Subgroup.normalizer (P : Set G) := by
    dsimp [B, N]
    exact Subgroup.map_subtype_le C
  let xi : G := (x : G)⁻¹
  let S : Subgroup G := P.map (MulAut.conj xi).toMonoidHom
  have hSleK : S ≤ K := by
    rintro s ⟨y, hy, rfl⟩
    rcases hy with ⟨z, hz, rfl⟩
    change xi * (z : K) * xi⁻¹ ∈ K
    exact K.mul_mem (K.mul_mem (K.inv_mem x.property) z.property)
      (K.inv_mem (K.inv_mem x.property))
  have hSne : S ≠ ⊥ := by
    intro hbot
    apply hPne
    exact (Subgroup.map_eq_bot_iff_of_injective P
      (MulAut.conj xi).injective).mp hbot
  have hSp : IsPGroup ell S := by
    dsimp [S, P]
    exact (Pk.2.map K.subtype).map (MulAut.conj xi).toMonoidHom
  have hRnormS : R ≤ Subgroup.normalizer (S : Set G) := by
    intro r hr
    let b : G := (x : G) * r * (x : G)⁻¹
    have hbB : b ∈ B := by
      rw [hBx]
      exact ⟨r, hr, rfl⟩
    have hbNorm : b ∈ Subgroup.normalizer (P : Set G) := hBnormP hbB
    have hbMap : (MulAut.conj xi) b ∈
        (Subgroup.normalizer (P : Set G)).map
          (MulAut.conj xi).toMonoidHom :=
      ⟨b, hbNorm, rfl⟩
    rw [Subgroup.map_equiv_normalizer_eq P (MulAut.conj xi)] at hbMap
    have hbr : (MulAut.conj xi) b = r := by
      dsimp [b, xi]
      group
    rwa [hbr] at hbMap
  exact ⟨S, hSleK, hSne, hSp, hRnormS⟩

end IsFrobeniusDecomposition

end Submission.OddOrder.BG.Section03
