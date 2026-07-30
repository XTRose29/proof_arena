import Submission.OddOrder.MathlibSupport.CoprimeNilpotentCentralizer
import Submission.OddOrder.MathlibSupport.FittingPCore

/-!
The p-group centralizer input for Bender-Glauberman A.5.2.

In a finite solvable group with trivial `p'`-core, a normal `p`-subgroup `P`
whose centralizer inside `O_p(G)` is contained in `P` has p-group ambient
centralizer.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

theorem centralizer_isPGroup_of_pPrimeCore_eq_bot
    {p : ℕ} [Fact p.Prime] [IsSolvable G] {P : Subgroup G}
    (hP : IsPGroup p P) (hPnormal : P.Normal)
    (hprimeCore : pPrimeCore p G = ⊥)
    (hcent : centralizerWithin (pCore p G) P ≤ P) :
    IsPGroup p (Subgroup.centralizer (P : Set G)) := by
  letI : P.Normal := hPnormal
  let Q : Subgroup G := pCore p G
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  have hPQ : P ≤ Q := le_pCore hP hPnormal
  have hCQ : Subgroup.centralizer (Q : Set G) ≤ Q := by
    exact centralizer_pCore_le_pCore_of_pPrimeCore_eq_bot hprimeCore
  rw [IsPGroup.iff_orderOf]
  intro x
  refine ⟨(orderOf x).primeFactorsList.length,
    Nat.eq_prime_pow_of_unique_prime_dvd (orderOf_pos x).ne' ?_⟩
  intro q hq hqdiv
  haveI : Fact q.Prime := ⟨hq⟩
  by_contra hqp
  have hqdivG : q ∣ orderOf (x : G) := by
    simpa using hqdiv
  let u : G := (x : G) ^ (orderOf (x : G) / q)
  have huOrder : orderOf u = q := by
    exact orderOf_pow_orderOf_div (orderOf_pos (x : G)).ne' hqdivG
  have huC : u ∈ C := by
    exact C.pow_mem x.property _
  let U : Subgroup G := Subgroup.zpowers u
  have hUq : IsPGroup q U := by
    apply IsPGroup.of_card (n := 1)
    dsimp [U]
    rw [Nat.card_zpowers, huOrder, pow_one]
  have hUQcoprime : Nat.Coprime (Nat.card Q) (Nat.card U) := by
    exact IsPGroup.coprime_card_of_ne p q (Ne.symm hqp) Q U pCore_isPGroup hUq
  have hUnormalizesQ : U ≤ Subgroup.normalizer (Q : Set G) := by
    rw [Q.normalizer_eq_top]
    exact le_top
  have hUC : U ≤ C := by
    change Subgroup.zpowers u ≤ C
    rw [Subgroup.zpowers_le]
    exact huC
  have hPfixed : P ≤ centralizerWithin Q U := by
    intro y hy
    refine ⟨hPQ hy, ?_⟩
    change y ∈ Subgroup.centralizer (U : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzC : z ∈ C := hUC hz
    exact (Subgroup.mem_centralizer_iff.mp hzC y hy).symm
  have hfixedSelf :
      centralizerWithin Q (centralizerWithin Q U) ≤ centralizerWithin Q U := by
    exact (centralizerWithin_antitone_right hPfixed).trans
      (hcent.trans hPfixed)
  letI : Group.IsNilpotent Q := pCore_isPGroup.isNilpotent
  have hUcentralizesQ : U ≤ Subgroup.centralizer (Q : Set G) :=
    coprime_nilpotent_centralizes_of_selfCentralizing_fixedPoints
      hUnormalizesQ hUQcoprime hfixedSelf
  have huQ : u ∈ Q := hCQ (hUcentralizesQ (Subgroup.mem_zpowers u))
  obtain ⟨k, huk⟩ := IsPGroup.iff_orderOf.mp
    (pCore_isPGroup (p := p) (G := G)) ⟨u, huQ⟩
  have hqpow : q = p ^ k := by
    rw [← huOrder, ← Subgroup.orderOf_mk]
    exact huk
  have hqdivpow : q ∣ p ^ k := by
    rw [← hqpow]
  have hqeqp : q = p :=
    Nat.prime_eq_prime_of_dvd_pow hq Fact.out hqdivpow
  exact hqp hqeqp

end Submission.OddOrder.MathlibSupport
