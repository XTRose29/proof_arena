import Submission.OddOrder.MathlibSupport.CommutatorSup
import Submission.OddOrder.MathlibSupport.CoprimePrimeOrderCentralProduct

/-!
Idempotence of a coprime prime-order commutator action.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]
variable {K R : Subgroup G}

/-- In a coprime factorization with prime-order complement, applying the mixed
commutator operation twice does not shrink its image. This is the specialized
Theorem 3.4 form of Bender-Glauberman Proposition 1.6(b). -/
theorem commutator_commutator_eq_of_prime_complement
    (hKR : K.IsComplement' R)
    (hnormK : R ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card K) (Nat.card R))
    (hRprime : (Nat.card R).Prime) :
    ⁅R, ⁅R, K⁆⁆ = ⁅R, K⁆ := by
  let H : Subgroup G := ⁅R, K⁆
  let C : Subgroup G := centralizerWithin K R
  let N : Subgroup G := ⁅R, H⁆
  have hHK : H ≤ K :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hnormK
  have hnormH : R ≤ Subgroup.normalizer (H : Set G) :=
    Subgroup.normalizer_commutator_ge_left R K
  have hNH : N ≤ H :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hnormH
  have hKsup : K = H ⊔ C := by
    apply le_antisymm
    · exact le_commutator_sup_centralizerWithin_of_prime_complement
        hKR hnormK hcop hRprime
    · exact sup_le hHK (centralizerWithin_le_left K R)
  have hnormNR : R ≤ Subgroup.normalizer (N : Set G) := by
    exact Subgroup.normalizer_commutator_ge_left R H
  have hnormNH : H ≤ Subgroup.normalizer (N : Set G) := by
    exact Subgroup.normalizer_commutator_ge_right R H
  have hnormHC : C ≤ Subgroup.normalizer (H : Set G) :=
    centralizerWithin_le_left K R |>.trans
      (Subgroup.normalizer_commutator_ge_right R K)
  have hnormRC : C ≤ Subgroup.normalizer (R : Set G) :=
    (show C ≤ Subgroup.centralizer (R : Set G) from inf_le_right) |>.trans
      (Subgroup.centralizer_le_normalizer (R : Set G))
  have hnormNC : C ≤ Subgroup.normalizer (N : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    dsimp [N]
    rw [Subgroup.map_commutator,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnormRC hc),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnormHC hc)]
  have hnormNK : K ≤ Subgroup.normalizer (N : Set G) := by
    rw [hKsup]
    exact sup_le hnormNH hnormNC
  letI : N.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hKR.sup_eq_top]
    exact sup_le hnormNK hnormNR
  have hRCbot : ⁅R, C⁆ = ⊥ := by
    rw [Subgroup.commutator_comm,
      Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact inf_le_right
  have hRK : ⁅R, K⁆ ≤ N := by
    rw [hKsup]
    exact commutator_sup_le_of_normal le_rfl (hRCbot.le.trans bot_le)
  apply le_antisymm hNH
  simpa [H, N] using hRK

end Submission.OddOrder.MathlibSupport
