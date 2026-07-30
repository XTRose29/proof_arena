import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Complement

/-!
Normal-subgroup containment for a coprime factorization with prime-order
right factor.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]
variable {K R N : Subgroup G}

/-- A normal subgroup disjoint from the prime-order factor of a coprime
factorization lies in the normal left factor.  This is the specialized Hall
containment used for kernels of simple constituents in BGsection3. -/
theorem normal_le_left_of_disjoint_prime_right
    [K.Normal] [N.Normal]
    (hKR : K.IsComplement' R)
    (hcop : Nat.Coprime (Nat.card K) (Nat.card R))
    (hRprime : (Nat.card R).Prime)
    (hdis : Disjoint N R) :
    N ≤ K := by
  classical
  let p := Nat.card R
  letI : Fact p.Prime := ⟨hRprime⟩
  have hpK : Nat.Coprime p (Nat.card K) := by
    simpa [p] using hcop.symm
  have hRp : IsPGroup p R := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by simp [p]⟩
  have hpRindex : ¬ p ∣ R.index := by
    rw [hKR.index_eq_card]
    exact hRprime.coprime_iff_not_dvd.mp hpK
  let PR : Sylow p G := hRp.toSylow hpRindex
  by_contra hNK
  let q : G →* G ⧸ K := QuotientGroup.mk' K
  have hNqne : N.map q ≠ ⊥ := by
    intro hbot
    apply hNK
    have hle := (Subgroup.map_eq_bot_iff N).mp hbot
    simpa [q, QuotientGroup.ker_mk'] using hle
  have hqcard : Nat.card (G ⧸ K) = p := by
    rw [← Subgroup.index_eq_card, hKR.symm.index_eq_card]
  have hqprime : (Nat.card (G ⧸ K)).Prime := by
    rw [hqcard]
    exact hRprime
  letI : Fact (Nat.card (G ⧸ K)).Prime := ⟨hqprime⟩
  have hNqtop : N.map q = ⊤ :=
    (N.map q).eq_bot_or_eq_top_of_prime_card.resolve_left hNqne
  have hsup : N ⊔ K = ⊤ := by
    have hc := Subgroup.comap_map_eq q N
    rw [hNqtop, Subgroup.comap_top, QuotientGroup.ker_mk'] at hc
    exact hc.symm
  have hNindex_eq : N.index = N.relIndex K := by
    calc
      N.index = N.relIndex ⊤ := N.relIndex_top_right.symm
      _ = N.relIndex (N ⊔ K) := congrArg (N.relIndex ·) hsup.symm
      _ = N.relIndex K := Subgroup.relIndex_sup_left K N
  have hNindex_dvd : N.index ∣ Nat.card K := by
    rw [hNindex_eq]
    exact N.relIndex_dvd_card K
  have hpNindex : ¬ p ∣ N.index :=
    hRprime.coprime_iff_not_dvd.mp
      (hpK.coprime_dvd_right hNindex_dvd)
  let P : Sylow p N := Sylow.nonempty.some
  have hPmap : IsPGroup p ((P : Subgroup N).map N.subtype) :=
    P.isPGroup'.map N.subtype
  have hpPmapIndex : ¬ p ∣ ((P : Subgroup N).map N.subtype).index := by
    rw [Subgroup.index_map_subtype]
    exact hRprime.not_dvd_mul P.not_dvd_index hpNindex
  let PN : Sylow p G := hPmap.toSylow hpPmapIndex
  have hPNle : (PN : Subgroup G) ≤ N := by
    exact Subgroup.map_subtype_le (P : Subgroup N)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G PN PR
  have hconj : MulAut.conj g • (PN : Subgroup G) = R := by
    rw [← Sylow.coe_subgroup_smul, hg]
    rfl
  have hRleN : R ≤ N := by
    calc
      R = MulAut.conj g • (PN : Subgroup G) := hconj.symm
      _ ≤ MulAut.conj g • N :=
        Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hPNle
      _ = N := Subgroup.Normal.conj_smul_eq_self g N
  have hRbot : R = ⊥ := by
    apply le_bot_iff.mp
    rw [← disjoint_iff.mp hdis]
    exact le_inf hRleN le_rfl
  apply hRprime.ne_one
  simp [hRbot]

end Submission.OddOrder.MathlibSupport
