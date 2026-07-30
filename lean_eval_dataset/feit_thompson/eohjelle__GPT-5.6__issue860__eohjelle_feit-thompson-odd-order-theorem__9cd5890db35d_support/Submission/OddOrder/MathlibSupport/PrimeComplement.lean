import Mathlib.GroupTheory.SchurZassenhaus
import Submission.OddOrder.MathlibSupport.SubgroupCardinality

/-!
Hall `q'`-subgroups in a form tailored to the odd-order port.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]
variable {q : ℕ} {H : Subgroup G}

/-- A Hall `q'`-subgroup: its cardinality is coprime to `q`, while its index
is a power of `q`. -/
def IsPrimeComplement (q : ℕ) (H : Subgroup G) : Prop :=
  Nat.Coprime (Nat.card H) q ∧ ∃ n : ℕ, H.index = q ^ n

namespace IsPrimeComplement

open scoped Pointwise

omit [Finite G] in
theorem card_coprime (hH : IsPrimeComplement q H) :
    Nat.Coprime (Nat.card H) q :=
  hH.1

omit [Finite G] in
theorem exists_index_eq_pow (hH : IsPrimeComplement q H) :
    ∃ n : ℕ, H.index = q ^ n :=
  hH.2

omit [Finite G] in
theorem not_dvd_card (hq : q.Prime) (hH : IsPrimeComplement q H) :
    ¬q ∣ Nat.card H :=
  hq.coprime_iff_not_dvd.mp hH.card_coprime.symm

theorem index_eq_sylow_card (hq : q.Prime)
    (hH : IsPrimeComplement q H) (P : Sylow q G) :
    H.index = Nat.card P := by
  letI : Fact q.Prime := ⟨hq⟩
  obtain ⟨n, hn⟩ := hH.exists_index_eq_pow
  have hcardH : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hpow : q ^ n ≠ 0 := pow_ne_zero _ hq.ne_zero
  have hfac : Nat.factorization (Nat.card G) q = n := by
    rw [← H.index_mul_card, hn,
      Nat.factorization_mul hpow hcardH, Finsupp.add_apply,
      Nat.factorization_pow_self hq,
      Nat.factorization_eq_zero_of_not_dvd (hH.not_dvd_card hq), add_zero]
  rw [hn, P.card_eq_multiplicity, hfac]

/-- Every Sylow `q`-subgroup and Hall `q'`-subgroup are complementary. -/
theorem sylow_isComplement (hq : q.Prime)
    (hH : IsPrimeComplement q H) (P : Sylow q G) :
    (P : Subgroup G).IsComplement' H := by
  letI : Fact q.Prime := ⟨hq⟩
  have hindex : H.index = Nat.card P := hH.index_eq_sylow_card hq P
  apply Subgroup.isComplement'_of_coprime
  · rw [← hindex, H.index_mul_card]
  · obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    rw [hn]
    exact hH.card_coprime.symm.pow_left n

theorem sylow_sup_eq_top (hq : q.Prime)
    (hH : IsPrimeComplement q H) (P : Sylow q G) :
    (P : Subgroup G) ⊔ H = ⊤ :=
  (hH.sylow_isComplement hq P).sup_eq_top

omit [Finite G] in
theorem ne_top_of_dvd_card (hq : q.Prime)
    (hH : IsPrimeComplement q H) (hqdvd : q ∣ Nat.card G) :
    H ≠ ⊤ := by
  intro htop
  apply hH.not_dvd_card hq
  simpa [htop] using hqdvd

omit [Finite G] in
/-- Hall `q'`-subgroups are preserved by automorphisms. -/
theorem smul_mulAut (hH : IsPrimeComplement q H) (a : MulAut G) :
    IsPrimeComplement q (a • H) := by
  have hcard : Nat.card (a • H : Subgroup G) = Nat.card H :=
    Nat.card_congr (Subgroup.equivSMul a H).symm.toEquiv
  constructor
  · rw [hcard]
    exact hH.card_coprime
  · obtain ⟨n, hn⟩ := hH.exists_index_eq_pow
    refine ⟨n, ?_⟩
    change (H.map (a : G →* G)).index = q ^ n
    rw [Subgroup.index_map_equiv, hn]

end IsPrimeComplement

end Submission.OddOrder.MathlibSupport
