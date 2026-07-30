import Submission.OddOrder.MathlibSupport.Cardinality

/-!
Prime-set Hall subgroup support for the odd-order port.

MathComp packages the choice of allowed prime divisors into its `pi.-Hall`
predicate.  Mathlib's current finite-group API generally states the same
condition as coprimality between a subgroup's cardinality and index.  The
definitions and lemmas below retain the prime-set information used throughout
the Bender-Glauberman and Peterfalvi developments while exposing the coprime
form expected by mathlib's Sylow and Schur-Zassenhaus theorems.
-/

namespace Submission.OddOrder.MathlibSupport

/-- The natural numbers all of whose prime divisors belong to `pi`. -/
def IsPiNumber (pi : Set ℕ) (n : ℕ) : Prop :=
  ∀ ⦃p : ℕ⦄, p.Prime → p ∣ n → p ∈ pi

/-- The set of prime divisors of a natural number. -/
def primeSupport (n : ℕ) : Set ℕ :=
  {p | p.Prime ∧ p ∣ n}

namespace IsPiNumber

variable {pi rho : Set ℕ} {m n : ℕ}

theorem one : IsPiNumber pi 1 := by
  intro p hp hpdvd
  exact (hp.not_dvd_one hpdvd).elim

theorem mono (hpi : pi ⊆ rho) (hn : IsPiNumber pi n) : IsPiNumber rho n :=
  fun _ hp hdvd => hpi (hn hp hdvd)

theorem of_dvd (hmn : m ∣ n) (hn : IsPiNumber pi n) : IsPiNumber pi m :=
  fun _ hp hdvd => hn hp (hdvd.trans hmn)

theorem mul (hm : IsPiNumber pi m) (hn : IsPiNumber pi n) :
    IsPiNumber pi (m * n) := by
  intro p hp hpdvd
  rcases hp.dvd_mul.mp hpdvd with hpm | hpn
  · exact hm hp hpm
  · exact hn hp hpn

theorem left_of_mul (h : IsPiNumber pi (m * n)) : IsPiNumber pi m :=
  h.of_dvd (dvd_mul_right m n)

theorem right_of_mul (h : IsPiNumber pi (m * n)) : IsPiNumber pi n :=
  h.of_dvd (dvd_mul_left n m)

theorem primeSupport_self : IsPiNumber (primeSupport n) n :=
  fun _ hp hdvd => ⟨hp, hdvd⟩

end IsPiNumber

/-- A subgroup has `pi`-number cardinality when each of its nonidentity
elements has `pi`-number order. -/
theorem isPiNumber_natCard_of_orderOf {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} {pi : Set ℕ}
    (h : ∀ x : G, x ∈ H → x ≠ 1 → IsPiNumber pi (orderOf x)) :
    IsPiNumber pi (Nat.card H) := by
  intro p hp hpH
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := H) p hpH
  have hxorder : orderOf (x : G) = p :=
    (Subgroup.orderOf_coe x).trans hx
  have hxne : (x : G) ≠ 1 := by
    intro hxone
    rw [hxone, orderOf_one] at hxorder
    exact hp.ne_one hxorder.symm
  exact h (x : G) x.property hxne hp (by rw [hxorder])

variable {G : Type*} [Group G]

/-- A `pi`-Hall subgroup has `pi`-number cardinality and `pi`-prime index. -/
def IsHall (pi : Set ℕ) (H : Subgroup G) : Prop :=
  IsPiNumber pi (Nat.card H) ∧ IsPiNumber piᶜ H.index

namespace IsHall

variable {pi : Set ℕ} {H : Subgroup G}

theorem isPiNumber_card (hH : IsHall pi H) : IsPiNumber pi (Nat.card H) :=
  hH.1

theorem isPiNumber_index (hH : IsHall pi H) : IsPiNumber piᶜ H.index :=
  hH.2

theorem coprime_card_index (hH : IsHall pi H) :
    (Nat.card H).Coprime H.index := by
  apply Nat.coprime_of_dvd
  intro p hp hpcard hpindex
  exact hH.2 hp hpindex (hH.1 hp hpcard)

theorem odd_card [Finite G] (_hH : IsHall pi H) (hodd : Odd (Nat.card G)) :
    Odd (Nat.card H) :=
  hodd.of_dvd_nat H.card_subgroup_dvd_card

theorem odd_index [Finite G] (_hH : IsHall pi H) (hodd : Odd (Nat.card G)) :
    Odd H.index :=
  hodd.of_dvd_nat H.index_dvd_card

theorem exists_left_complement [Finite G] [H.Normal] (hH : IsHall pi H) :
    ∃ K : Subgroup G, Subgroup.IsComplement' K H :=
  H.exists_left_complement'_of_coprime hH.coprime_card_index

theorem exists_right_complement [Finite G] [H.Normal] (hH : IsHall pi H) :
    ∃ K : Subgroup G, Subgroup.IsComplement' H K :=
  H.exists_right_complement'_of_coprime hH.coprime_card_index

end IsHall

theorem isHall_primeSupport_iff [Finite G] (H : Subgroup G) :
    IsHall (primeSupport (Nat.card H)) H ↔ (Nat.card H).Coprime H.index := by
  constructor
  · exact IsHall.coprime_card_index
  · intro hcop
    refine ⟨IsPiNumber.primeSupport_self, ?_⟩
    intro p hp hpindex hpsupport
    exact (Nat.Prime.not_coprime_iff_dvd.mpr
      ⟨p, hp, hpsupport.2, hpindex⟩) hcop

theorem isHall_primeSupport [Finite G] (H : Subgroup G)
    (hcop : (Nat.card H).Coprime H.index) :
    IsHall (primeSupport (Nat.card H)) H :=
  (isHall_primeSupport_iff H).2 hcop

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Every Sylow subgroup is a Hall subgroup for its own prime support. -/
theorem sylow_isHall_primeSupport (P : Sylow p G) :
    IsHall (primeSupport (Nat.card P)) (P : Subgroup G) :=
  isHall_primeSupport (P : Subgroup G) P.card_coprime_index

end Submission.OddOrder.MathlibSupport
