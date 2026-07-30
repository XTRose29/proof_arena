import Submission.OddOrder.BG.Section06.PProdCoprime
import Submission.OddOrder.BG.Section07.NormedSubgroups

/-!
# Bender--Glauberman, Section 7: consequences of normalized transitivity

Transitivity on the maximal normalized `q`-subgroups gives a normalizer
factorization.  The coprime focal theorem then compares the corresponding
derived-subgroup intersections.
-/

namespace Submission.OddOrder.BG.Section07

open Submission.OddOrder.MathlibSupport
open scoped Pointwise commutatorElement

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem subgroup_map_symm_map (H : Subgroup G) (e : G ≃* G) :
    (H.map e.toMonoidHom).map e.symm.toMonoidHom = H := by
  ext x
  simp

omit [Finite G] in
private theorem subgroup_symm_map_map (H : Subgroup G) (e : G ≃* G) :
    (H.map e.symm.toMonoidHom).map e.toMonoidHom = H := by
  simpa using subgroup_map_symm_map H e.symm

/-- Orbit--stabilizer, in the form needed below: transitivity by `K` on the
maximal normalized subgroups factors the normalizer through the stabilizer
of a chosen maximal subgroup. -/
private theorem normalizer_eq_mul_stabilizer_of_transitive
    {q : ℕ} (K P : Subgroup G)
    (hKNP : K ≤ Subgroup.normalizer (P : Set G))
    (htrans : ∀ Q₁ Q₂ : Subgroup G,
      Q₁ ∈ max_normed_pgroups (P : Set G) ({q} : Set ℕ) →
      Q₂ ∈ max_normed_pgroups (P : Set G) ({q} : Set ℕ) →
      ∃ k : G, k ∈ K ∧ Q₂ = Q₁.map (MulAut.conj k⁻¹).toMonoidHom)
    {Q : Subgroup G}
    (hQmax : Q ∈ max_normed_pgroups (P : Set G) ({q} : Set ℕ)) :
    (Subgroup.normalizer (P : Set G) : Set G) =
      (K : Set G) * ((Subgroup.normalizer (P : Set G) ⊓
        Subgroup.normalizer (Q : Set G) : Subgroup G) : Set G) := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    let Qx : Subgroup G := Q.map (MulAut.conj x).toMonoidHom
    have hQxmax : Qx ∈
        max_normed_pgroups (P : Set G) ({q} : Set ℕ) := by
      exact (norm_acts_max_norm P Q ({q} : Set ℕ) x hx).mpr hQmax
    obtain ⟨k, hkK, hQx⟩ := htrans Q Qx hQmax hQxmax
    have hkNP : k ∈ Subgroup.normalizer (P : Set G) := hKNP hkK
    have hkxNP : k * x ∈ Subgroup.normalizer (P : Set G) :=
      (Subgroup.normalizer (P : Set G)).mul_mem hkNP hx
    have hkxNQ : k * x ∈ Subgroup.normalizer (Q : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      calc
        Q.map (MulAut.conj (k * x)).toMonoidHom =
            Qx.map (MulAut.conj k).toMonoidHom := by
          dsimp [Qx]
          rw [Subgroup.map_map]
          congr 1
          ext z
          simp [MulAut.conj_apply, mul_assoc]
        _ = (Q.map (MulAut.conj k⁻¹).toMonoidHom).map
              (MulAut.conj k).toMonoidHom := by rw [hQx]
        _ = Q := by
          have he : MulAut.conj k⁻¹ = (MulAut.conj k).symm := by
            ext z
            simp [MulAut.conj_symm_apply]
          rw [he]
          exact subgroup_symm_map_map Q (MulAut.conj k)
    refine ⟨k⁻¹, K.inv_mem hkK, k * x, ⟨hkxNP, hkxNQ⟩, ?_⟩
    simp
  · rintro x ⟨k, hkK, s, hs, rfl⟩
    exact (Subgroup.normalizer (P : Set G)).mul_mem (hKNP hkK) hs.1

/-- Transitivity on the maximal normalized `q`-subgroups gives both the
normalizer factorization and the focal-subgroup containment used in the
Section 7 argument. -/
theorem normed_transitive_normalizer_consequences
    {G : Type u} [Group G] [Finite G]
    {pi : Set ℕ} {q : ℕ} (K P : Subgroup G)
    (hKNP : K ≤ Subgroup.normalizer (P : Set G))
    (hKnormal : (K.subgroupOf (Subgroup.normalizer (P : Set G))).Normal)
    (hKpi' : IsPiNumber piᶜ (Nat.card K))
    (hPpi : IsPiNumber pi (Nat.card P))
    (htrans : ∀ Q₁ Q₂ : Subgroup G,
      Q₁ ∈ max_normed_pgroups (P : Set G) ({q} : Set ℕ) →
      Q₂ ∈ max_normed_pgroups (P : Set G) ({q} : Set ℕ) →
      ∃ k : G, k ∈ K ∧ Q₂ = Q₁.map (MulAut.conj k⁻¹).toMonoidHom)
    {Q : Subgroup G}
    (hQmax : Q ∈ max_normed_pgroups (P : Set G) ({q} : Set ℕ)) :
    P ⊓ ⁅Subgroup.normalizer (P : Set G), Subgroup.normalizer (P : Set G)⁆ ≤
      ⁅Subgroup.normalizer (Q : Set G), Subgroup.normalizer (Q : Set G)⁆ ∧
    (Subgroup.normalizer (P : Set G) : Set G) =
      (K : Set G) * ((Subgroup.normalizer (P : Set G) ⊓
        Subgroup.normalizer (Q : Set G) : Subgroup G) : Set G) := by
  classical
  let N : Subgroup G := Subgroup.normalizer (P : Set G)
  let S : Subgroup G := N ⊓ Subgroup.normalizer (Q : Set G)
  have hPleN : P ≤ N := by
    simpa [N] using (Subgroup.le_normalizer :
      P ≤ Subgroup.normalizer (P : Set G))
  have hKleN : K ≤ N := by simpa [N] using hKNP
  have hSleN : S ≤ N := by exact inf_le_left
  have hPleNQ : P ≤ Subgroup.normalizer (Q : Set G) :=
    (mem_max_normed hQmax).2
  have hPleS : P ≤ S := by
    exact le_inf hPleN hPleNQ
  have hSleNQ : S ≤ Subgroup.normalizer (Q : Set G) :=
    inf_le_right
  have hprod : (N : Set G) = (K : Set G) * (S : Set G) := by
    simpa [N, S] using
      normalizer_eq_mul_stabilizer_of_transitive K P hKNP htrans hQmax

  let KN : Subgroup N := K.subgroupOf N
  let SN : Subgroup N := S.subgroupOf N
  let PN : Subgroup N := P.subgroupOf N
  letI : KN.Normal := by
    simpa [KN, N] using hKnormal
  have hPNSN : PN ≤ SN := by
    exact Subgroup.subgroupOf_mono N hPleS
  have hKNSNtop : KN ⊔ SN = ⊤ := by
    apply top_unique
    intro n _
    have hnprod : ((n : N) : G) ∈ (K : Set G) * (S : Set G) := by
      rw [← hprod]
      exact n.property
    rcases hnprod with ⟨k, hkK, s, hsS, hks⟩
    let kn : KN := ⟨⟨k, hKleN hkK⟩, hkK⟩
    let sn : SN := ⟨⟨s, hSleN hsS⟩, hsS⟩
    have hmul : (kn : N) * (sn : N) ∈ KN ⊔ SN :=
      Subgroup.mul_mem_sup kn.property sn.property
    have heq : (kn : N) * (sn : N) = n := by
      apply Subtype.ext
      exact hks
    rw [← heq]
    exact hmul
  have hcopKP : (Nat.card K).Coprime (Nat.card P) := by
    apply Nat.coprime_of_dvd
    intro p hp hpK hpP
    exact (hKpi' hp hpK) (hPpi hp hpP)
  have hcopKNPN : (Nat.card KN).Coprime (Nat.card PN) := by
    rw [natCard_subgroupOf_eq hKleN, natCard_subgroupOf_eq hPleN]
    exact hcopKP
  have hfocal :
      PN ⊓ _root_.commutator N = PN ⊓ ⁅SN, SN⁆ :=
    Section06.pprod_focal_coprime hKNSNtop hPNSN hcopKNPN

  constructor
  · intro x hx
    let xn : N := ⟨x, hPleN hx.1⟩
    have hxMap : x ∈ (_root_.commutator N).map N.subtype := by
      rw [N.map_subtype_commutator]
      simpa [N] using hx.2
    rcases hxMap with ⟨y, hyDer, hyx⟩
    have hyxn : y = xn := by
      apply Subtype.ext
      exact hyx
    have hxnDer : xn ∈ _root_.commutator N := by
      simpa [hyxn] using hyDer
    have hxnPN : xn ∈ PN := hx.1
    have hxnSNSN : xn ∈ ⁅SN, SN⁆ := by
      have hleft : xn ∈ PN ⊓ _root_.commutator N := ⟨hxnPN, hxnDer⟩
      rw [hfocal] at hleft
      exact hleft.2
    have hmapped : x ∈ ⁅SN, SN⁆.map N.subtype := by
      exact ⟨xn, hxnSNSN, rfl⟩
    rw [Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le hSleN] at hmapped
    exact (Subgroup.commutator_mono hSleNQ hSleNQ) hmapped
  · simpa [N, S] using hprod

end Submission.OddOrder.BG.Section07
