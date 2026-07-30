import Submission.OddOrder.BG.Section03.SemiregularConjugation
import Submission.OddOrder.MathlibSupport.PrimeProductGroup

/-!
The Frobenius alternative for groups of squarefree prime-product order.
-/

namespace Submission.OddOrder.BG.Section03

open Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p q : ℕ}

/-- For `p < q`, a noncentral Sylow `p`-action on the normal Sylow
`q`-subgroup of a group of order `p * q` is Frobenius. -/
theorem sylow_isFrobeniusDecomposition_of_not_le_centralizer
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hcard : Nat.card G = p * q) (P : Sylow p G) (Q : Sylow q G)
    (hnoncentral : ¬ (P : Subgroup G) ≤
      Subgroup.centralizer (Q : Set G)) :
    IsFrobeniusDecomposition (Q : Subgroup G) (P : Subgroup G) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  have hPcard : Nat.card P = p :=
    sylow_card_eq_left_prime_of_natCard_eq_mul hp hq hpq.ne hcard P
  have hQcard : Nat.card Q = q :=
    sylow_card_eq_left_prime_of_natCard_eq_mul hq hp hpq.ne'
      (hcard.trans (Nat.mul_comm p q)) Q
  have hnormal : (Q : Subgroup G).Normal :=
    sylow_right_normal_of_lt_of_natCard_eq_mul hp hq hpq hcard Q
  have hcomplement : (Q : Subgroup G).IsComplement' (P : Subgroup G) :=
    (sylow_isComplement_of_natCard_eq_mul hp hq hpq.ne hcard P Q).symm
  have hQne : (Q : Subgroup G) ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot, hQcard]
    exact hq.one_lt
  have hPne : (P : Subgroup G) ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot, hPcard]
    exact hp.one_lt
  have hfixed : ∀ r : P, r ≠ 1 → ∀ x : Q,
      (r : G) * (x : G) * (r : G)⁻¹ = (x : G) → x = 1 := by
    intro r hr x hx
    by_contra hxOne
    have hcomm : Commute (r : G) (x : G) := by
      rw [Commute]
      calc
        (r : G) * (x : G) =
            ((r : G) * (x : G) * (r : G)⁻¹) * (r : G) := by simp
        _ = (x : G) * (r : G) := by rw [hx]
    apply hnoncentral
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    let yP : P := ⟨y, hy⟩
    let zQ : Q := ⟨z, hz⟩
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp
      (mem_zpowers_of_prime_card hPcard hr (g' := yP))
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp
      (mem_zpowers_of_prime_card hQcard hxOne (g' := zQ))
    have hmn := hcomm.zpow_zpow m n
    have hmG : (r : G) ^ m = y := by
      exact congrArg Subtype.val hm
    have hnG : (x : G) ^ n = z := by
      exact congrArg Subtype.val hn
    rw [hmG, hnG] at hmn
    exact hmn.eq.symm
  exact
    { isComplement := hcomplement
      kernel_normal := hnormal
      kernel_ne_bot := hQne
      complement_ne_bot := hPne
      fixedPointFree := hfixed }

end Submission.OddOrder.BG.Section03
