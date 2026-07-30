import Submission.OddOrder.MathlibSupport.PiPrimeCore
import Submission.OddOrder.MathlibSupport.PPrimeCore
import Submission.OddOrder.MathlibSupport.PrimeComplement

/-!
# Group-level prime-set cores

MathComp writes `'O_pi(G)` for the largest normal `pi`-subgroup of `G`.
The local `piPrimeCore` construction uses the complementary convention, so
`piCore pi G` is `piPrimeCore piᶜ ⊤`.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G]

/-- The largest normal subgroup of `G` whose cardinality is a `pi`-number. -/
def piCore (pi : Set ℕ) (G : Type*) [Group G] : Subgroup G :=
  piPrimeCore piᶜ (⊤ : Subgroup G)

/-- Every normal `pi`-subgroup is contained in the `pi`-core. -/
theorem le_piCore {pi : Set ℕ} {K : Subgroup G}
    (hKnormal : K.Normal) (hKpi : IsPiNumber pi (Nat.card K)) :
    K ≤ piCore pi G := by
  rw [piCore, piPrimeCore]
  exact le_sSup ⟨le_top, hKnormal.subgroupOf ⊤,
    by simpa only [compl_compl] using hKpi⟩

/-- The `pi`-core has `pi`-number cardinality. -/
theorem piCore_isPiNumber [Finite G] (pi : Set ℕ) :
    IsPiNumber pi (Nat.card (piCore pi G)) := by
  simpa only [piCore, compl_compl] using
    (piPrimeCore_isPiNumber piᶜ (⊤ : Subgroup G))

/-- A finite `pi`-group is equal to its `pi`-core. -/
theorem piCore_eq_top_of_isPiNumber [Finite G] {pi : Set ℕ}
    (hG : IsPiNumber pi (Nat.card G)) :
    piCore pi G = ⊤ := by
  apply top_unique
  apply le_piCore (K := (⊤ : Subgroup G)) (by infer_instance)
  simpa using hG

/-- The `pi`-core is characteristic. -/
instance piCore_characteristic (pi : Set ℕ) :
    (piCore pi G).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro e
  change (piPrimeCore piᶜ (⊤ : Subgroup G)).map e.toMonoidHom =
    piPrimeCore piᶜ (⊤ : Subgroup G)
  rw [piPrimeCore_map_equiv]
  simp

/-- The `pi`-core is normal. -/
instance piCore_normal (pi : Set ℕ) : (piCore pi G).Normal := by
  infer_instance

namespace IsPiNumber

variable {pi : Set ℕ} {m n : ℕ}

/-- A `pi`-number and a `piᶜ`-number are coprime. -/
theorem coprime_compl (hm : IsPiNumber pi m)
    (hn : IsPiNumber piᶜ n) : m.Coprime n := by
  apply Nat.coprime_of_dvd
  intro p hp hpm hpn
  exact hn hp hpn (hm hp hpm)

/-- Powers of a `pi`-number are `pi`-numbers. -/
theorem pow (hm : IsPiNumber pi m) (k : ℕ) :
    IsPiNumber pi (m ^ k) := by
  intro p hp hpdvd
  exact hm hp (hp.dvd_of_dvd_pow hpdvd)

end IsPiNumber

namespace IsPGroup

variable {p : ℕ} [Fact p.Prime]

/-- The cardinality of a finite `p`-group is a `pi`-number whenever
`p ∈ pi`. -/
theorem isPiNumber_natCard [Finite G] {pi : Set ℕ}
    (hG : IsPGroup p G) (hp : p ∈ pi) :
    IsPiNumber pi (Nat.card G) := by
  obtain ⟨n, hn⟩ := hG.exists_card_eq
  rw [hn]
  intro q hq hqpow
  have hqp : q = p := Nat.prime_eq_prime_of_dvd_pow hq Fact.out hqpow
  simpa [hqp] using hp

end IsPGroup

/-- If `N` is normal and `G/N` has `piᶜ`-number cardinality, then the
`pi`-core of `N`, mapped into `G`, is the `pi`-core of `G`. -/
theorem map_piCore_eq_of_quotient_isPiNumber
    [Finite G] {pi : Set ℕ} {N : Subgroup G} [N.Normal]
    (hquot : IsPiNumber piᶜ (Nat.card (G ⧸ N))) :
    (piCore pi N).map N.subtype = piCore pi G := by
  let O : Subgroup G := piCore pi G
  let L : Subgroup G := (piCore pi N).map N.subtype
  let q : G →* G ⧸ N := QuotientGroup.mk' N

  have hON : O ≤ N := by
    have hcop : (Nat.card O).Coprime (Nat.card (G ⧸ N)) :=
      IsPiNumber.coprime_compl (by
        simpa [O] using piCore_isPiNumber (G := G) pi) hquot
    intro x hx
    have horderO : orderOf (q x) ∣ Nat.card O :=
      (orderOf_map_dvd q x).trans (O.orderOf_dvd_natCard hx)
    have horderQ : orderOf (q x) ∣ Nat.card (G ⧸ N) :=
      orderOf_dvd_natCard (q x)
    have horderOne : orderOf (q x) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop horderO horderQ
    have hqx : q x = 1 := orderOf_eq_one_iff.mp horderOne
    exact (QuotientGroup.eq_one_iff x).mp (by simpa [q] using hqx)

  have hLO : L ≤ O := by
    apply le_piCore
    · dsimp [L]
      infer_instance
    · dsimp [L]
      rw [Subgroup.card_map_of_injective N.subtype_injective]
      exact piCore_isPiNumber pi

  have hOL : O ≤ L := by
    have hcard : Nat.card (O.subgroupOf N) = Nat.card O :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hON).toEquiv
    have hsubPi : IsPiNumber pi (Nat.card (O.subgroupOf N)) := by
      rw [hcard]
      exact piCore_isPiNumber pi
    have hsubLe : O.subgroupOf N ≤ piCore pi N :=
      le_piCore ((inferInstance : O.Normal).subgroupOf N) hsubPi
    calc
      O = (O.subgroupOf N).map N.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hON).symm
      _ ≤ (piCore pi N).map N.subtype := Subgroup.map_mono hsubLe
      _ = L := rfl

  exact le_antisymm hLO hOL

/-- Restricting a prime-set core to a normal Hall `pᶜ`-core does not
change it when `p ∉ pi`. -/
theorem map_piCore_pPrimeCore_eq_of_isPrimeComplement
    [Finite G] {pi : Set ℕ} {p : ℕ} [Fact p.Prime]
    (hp : p ∉ pi)
    (hHall : IsPrimeComplement p (pPrimeCore p G)) :
    (piCore pi (pPrimeCore p G)).map (pPrimeCore p G).subtype =
      piCore pi G := by
  let N : Subgroup G := pPrimeCore p G
  letI : N.Normal := by
    dsimp [N]
    infer_instance
  obtain ⟨n, hn⟩ := hHall.exists_index_eq_pow
  have hcard : Nat.card (G ⧸ N) = p ^ n := by
    rw [← N.index_eq_card]
    simpa [N] using hn
  have hquotP : IsPGroup p (G ⧸ N) := IsPGroup.of_card hcard
  have hquotPi : IsPiNumber piᶜ (Nat.card (G ⧸ N)) :=
    IsPGroup.isPiNumber_natCard hquotP hp
  simpa [N] using
    (map_piCore_eq_of_quotient_isPiNumber (G := G) hquotPi)

end Submission.OddOrder.MathlibSupport
