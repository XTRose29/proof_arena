/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
user: LorenzoLuccioli
model: Aristotle (Harmonic)
submission_repo: LorenzoLuccioli/lean-eval
submission_ref: 6ae2287b66eb687095e58fd0dbaeb7635ab26aba
issue_number: 270
-/
import Mathlib
import Submission.Helpers

namespace Submission

open Submission.Helpers Fintype

private theorem card_subgroup_lt {G : Type} [Group G] [Fintype G]
    {N : Subgroup G} [Fintype N] (h : N ≠ ⊤) :
    Fintype.card N < Fintype.card G := by
  have hN : Nat.card N < Nat.card G := by
    have h_card : Nat.card N ∣ Nat.card G := by
      simpa using Subgroup.card_subgroup_dvd_card N
    refine' lt_of_le_of_ne ( Nat.le_of_dvd ( Nat.card_pos ) h_card ) fun con => h ( Subgroup.eq_top_of_card_eq _ _ );
    exact con;
  aesop

private theorem card_quotient_lt {G : Type} [Group G] [Fintype G]
    {N : Subgroup G} [N.Normal] [Fintype N] [Fintype (G ⧸ N)] (h : N ≠ ⊥) :
    Fintype.card (G ⧸ N) < Fintype.card G := by
  have h_card_quotient_lt_card_G : Fintype.card (G ⧸ N) * Fintype.card N = Fintype.card G := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup N; aesop;
  simp_all +decide [ Subgroup.eq_bot_iff_forall ];
  exact h_card_quotient_lt_card_G ▸ lt_mul_of_one_lt_right ( Fintype.card_pos ) ( Fintype.one_lt_card_iff_nontrivial.mpr ⟨ ⟨ h.choose, h.choose_spec.1 ⟩, ⟨ 1, N.one_mem ⟩, by simpa using h.choose_spec.2 ⟩ )

/-- Burnside's p^a q^b theorem (universe-zero version used internally). -/
private theorem burnside_type0 {G : Type} [Group G] [Fintype G]
    {p q a b : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hpq : p ≠ q)
    (hcard : Fintype.card G = p ^ a * q ^ b) :
    IsSolvable G := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; simp at hcard; exact isSolvable_of_card_eq_prime_pow hq hcard
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; simp at hcard; exact isSolvable_of_card_eq_prime_pow hp hcard
  have h_not_simple := not_isSimpleGroup_of_card_eq_prime_pow_mul_prime_pow hp hq hpq ha hb hcard
  have hG_card_gt_one : 1 < Fintype.card G := by
    rw [hcard]
    have h1 : 1 < p ^ a := Nat.one_lt_pow (by omega) hp.one_lt
    have h2 : 0 < q ^ b := pos_of_gt (Nat.one_lt_pow (by omega) hq.one_lt)
    nlinarith [Fintype.card_pos (α := G)]
  haveI : Nontrivial G := Fintype.one_lt_card_iff_nontrivial.mp hG_card_gt_one
  obtain ⟨N, hN_normal, hN_ne_bot, hN_ne_top⟩ :
      ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
    by_contra h'
    simp only [not_exists, not_and, not_not] at h'
    exact h_not_simple {
      eq_bot_or_eq_top_of_normal := fun N hN => by
        by_cases hbot : N = ⊥
        · exact Or.inl hbot
        · exact Or.inr (h' N hN hbot)
    }
  haveI := hN_normal
  haveI : Fintype N := Fintype.ofFinite N
  haveI : Fintype (G ⧸ N) := Fintype.ofFinite (G ⧸ N)
  obtain ⟨a₁, b₁, _, _, hcardN⟩ :=
    card_subgroup_eq_prime_pow_mul_prime_pow hp hq hpq hcard N
  obtain ⟨a₂, b₂, _, _, hcardQ⟩ :=
    card_quotient_eq_prime_pow_mul_prime_pow hp hq hpq hcard N
  have hN_solv : IsSolvable N :=
    burnside_type0 hp hq hpq hcardN
  have hQ_solv : IsSolvable (G ⧸ N) :=
    burnside_type0 hp hq hpq hcardQ
  exact solvable_of_ker_le_range (Subgroup.subtype N) (QuotientGroup.mk' N)
    (by rw [QuotientGroup.ker_mk', Subgroup.subtype_range])
termination_by Fintype.card G
decreasing_by
  all_goals (first | exact @card_subgroup_lt _ _ _ _ (Fintype.ofFinite N) hN_ne_top
                    | exact @card_quotient_lt _ _ _ _ _ (Fintype.ofFinite N) (Fintype.ofFinite (G ⧸ N)) hN_ne_bot)

/-- Burnside's p^a q^b theorem: every group of order p^a * q^b is solvable.
    Universe-polymorphic version, proved by reducing to the universe-zero case
    via `Shrink`. -/
theorem finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
    {G : Type*} [Group G] [Fintype G]
    {p q a b : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hpq : p ≠ q)
    (hcard : Fintype.card G = p ^ a * q ^ b) :
    IsSolvable G := by
  -- Transfer to Shrink.{0} G which lives in Type (universe 0)
  letI : Group (Shrink.{0} G) := (equivShrink.{0} G).symm.group
  letI : Fintype (Shrink.{0} G) := Fintype.ofEquiv G (equivShrink.{0} G)
  have hcard' : Fintype.card (Shrink.{0} G) = p ^ a * q ^ b := by
    rw [Fintype.card_congr (equivShrink.{0} G).symm]; exact hcard
  have : IsSolvable (Shrink.{0} G) := burnside_type0 hp hq hpq hcard'
  -- Transfer IsSolvable back to G via the MulEquiv
  let e : Shrink.{0} G ≃* G := {
    toFun := (equivShrink.{0} G).symm
    invFun := equivShrink.{0} G
    left_inv := (equivShrink.{0} G).symm.left_inv
    right_inv := (equivShrink.{0} G).symm.right_inv
    map_mul' := by intro a b; simp
  }
  exact solvable_of_surjective (f := e.toMonoidHom) e.surjective

end Submission
