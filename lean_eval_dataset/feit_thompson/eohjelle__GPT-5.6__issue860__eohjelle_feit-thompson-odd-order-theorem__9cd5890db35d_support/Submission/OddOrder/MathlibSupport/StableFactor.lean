import Mathlib

/-!
The stable-factor coprime-action lemma.

If `A` acts trivially on `N` and on the factor represented by
`[A,H] <= N`, then a coprime-order argument shows that `A` centralizes `H`.
The pointwise proof is stronger than the solvable formulation used in
`BGsection1.stable_factor_cent`.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem stableFactor_centralizes {A H N : Subgroup G}
    (hcentral : A ≤ Subgroup.centralizer (N : Set G))
    (hNH : N ≤ H) (hcomm : ⁅A, H⁆ ≤ N)
    (hcoprime : Nat.Coprime (Nat.card H) (Nat.card A)) :
    A ≤ Subgroup.centralizer (H : Set G) := by
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  let c : G := ⁅a, h⁆
  have hcN : c ∈ N := by
    exact Subgroup.commutator_le.mp hcomm a ha h hh
  have hac : Commute a c := by
    exact (Subgroup.mem_centralizer_iff.mp (hcentral ha) c hcN).symm
  have hconj : a * h * a⁻¹ = c * h := by
    simpa [c] using (conj_eq_commutatorElement_mul (g₁ := a) (g₂ := h))
  have hiter : ∀ k : ℕ, a ^ k * h * (a ^ k)⁻¹ = c ^ k * h := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hakc : a ^ k * c * (a ^ k)⁻¹ = c := by
          rw [(hac.pow_left k).eq]
          simp
        calc
          a ^ (k + 1) * h * (a ^ (k + 1))⁻¹ =
              a ^ k * (a * h * a⁻¹) * (a ^ k)⁻¹ := by
            rw [pow_succ]
            group
          _ = a ^ k * (c * h) * (a ^ k)⁻¹ := by rw [hconj]
          _ = (a ^ k * c * (a ^ k)⁻¹) *
              (a ^ k * h * (a ^ k)⁻¹) := by group
          _ = c * (c ^ k * h) := by rw [hakc, ih]
          _ = c ^ (k + 1) * h := by rw [pow_succ']; group
  have haPow : a ^ Nat.card A = 1 := by
    have haPowSubtype : (⟨a, ha⟩ : A) ^ Nat.card A = 1 :=
      pow_card_eq_one'
    exact congrArg Subtype.val haPowSubtype
  have hcPowMul : c ^ Nat.card A * h = h := by
    rw [← hiter (Nat.card A), haPow]
    simp
  have hcPow : c ^ Nat.card A = 1 := by
    have := congrArg (fun x : G ↦ x * h⁻¹) hcPowMul
    simpa [mul_assoc] using this
  have horderA : orderOf c ∣ Nat.card A := orderOf_dvd_of_pow_eq_one hcPow
  have horderH : orderOf c ∣ Nat.card H :=
    H.orderOf_dvd_natCard (hNH hcN)
  have horder : orderOf c = 1 :=
    Nat.eq_one_of_dvd_coprimes hcoprime horderH horderA
  have hcOne : c = 1 := orderOf_eq_one_iff.mp horder
  exact (commutatorElement_eq_one_iff_mul_comm.mp (by simpa [c] using hcOne)).symm

end Submission.OddOrder.MathlibSupport
