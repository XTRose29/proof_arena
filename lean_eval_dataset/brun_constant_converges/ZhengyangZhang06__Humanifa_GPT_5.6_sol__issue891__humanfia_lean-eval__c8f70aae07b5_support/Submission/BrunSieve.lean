import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Primorial
import Submission.Selberg

open scoped ArithmeticFunction.omega BigOperators

open ArithmeticFunction Finset Nat Real

noncomputable section

namespace Submission.BrunSieve

/-- The polynomial whose prime values encode twin-prime starts. -/
def twinPolynomial (n : ℕ) : ℕ := n * (n + 2)

/-- The corresponding root predicate in a residue ring. -/
def IsTwinRoot (d : ℕ) (x : ZMod d) : Prop :=
  x * (x + 2) = 0

private def rootEquivProd {m n : ℕ} (h : m.Coprime n) :
    {x : ZMod (m * n) // IsTwinRoot (m * n) x} ≃
      {x : ZMod m // IsTwinRoot m x} × {x : ZMod n // IsTwinRoot n x} :=
  (((ZMod.chineseRemainder h).toEquiv.subtypeEquiv fun x => by
      change x * (x + 2) = 0 ↔
        ((ZMod.chineseRemainder h) x).1 * (((ZMod.chineseRemainder h) x).1 + 2) = 0 ∧
          ((ZMod.chineseRemainder h) x).2 * (((ZMod.chineseRemainder h) x).2 + 2) = 0
      calc
        _ ↔ (ZMod.chineseRemainder h) (x * (x + 2)) =
            (ZMod.chineseRemainder h) 0 :=
          (ZMod.chineseRemainder h).injective.eq_iff.symm
        _ ↔ _ := by
          simp only [map_mul, map_add, map_ofNat, _root_.map_zero, Prod.ext_iff,
            Prod.fst_mul, Prod.snd_mul, Prod.fst_add, Prod.snd_add,
            Prod.fst_ofNat, Prod.snd_ofNat, Prod.fst_zero, Prod.snd_zero])).trans
    Equiv.subtypeProdEquivProd

theorem card_twinRoots_mul {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n) :
    Nat.card {x : ZMod (m * n) // IsTwinRoot (m * n) x} =
      Nat.card {x : ZMod m // IsTwinRoot m x} *
        Nat.card {x : ZMod n // IsTwinRoot n x} := by
  letI : NeZero (m * n) := ⟨mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  simpa only [Nat.card_prod] using Nat.card_congr (rootEquivProd h)

theorem card_twinRoots_prime {p : ℕ} (hp : p.Prime) :
    Nat.card {x : ZMod p // IsTwinRoot p x} = if p = 2 then 1 else 2 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  by_cases hp2 : p = 2
  · subst p
    rw [if_pos rfl]
    calc
      Nat.card {x : ZMod 2 // IsTwinRoot 2 x} =
          Nat.card {x : ZMod 2 // x = 0} := by
        apply Nat.card_congr
        exact (Equiv.refl (ZMod 2)).subtypeEquiv fun x => by
          rw [IsTwinRoot, _root_.mul_eq_zero]
          have htwo : (2 : ZMod 2) = 0 := by
            change ((2 : ℕ) : ZMod 2) = 0
            rw [ZMod.natCast_eq_zero_iff]
          rw [htwo, add_zero, or_self]
          rfl
      _ = 1 := by simp
  · rw [if_neg hp2]
    calc
      Nat.card {x : ZMod p // IsTwinRoot p x} =
          Nat.card {x : ZMod p // x = 0 ∨ x = -2} := by
        apply Nat.card_congr
        exact (Equiv.refl (ZMod p)).subtypeEquiv fun x => by
          rw [IsTwinRoot, _root_.mul_eq_zero]
          simpa only [Equiv.refl_apply] using
            (or_congr Iff.rfl eq_neg_iff_add_eq_zero.symm)
      _ = 2 := by
        letI : Fintype (ZMod p) := Fintype.ofFinite _
        rw [Nat.card_eq_fintype_card]
        apply Fintype.card_subtype_eq_or_eq_of_ne
        intro h
        have htwo : (2 : ZMod p) = 0 := by simpa using h.symm
        change ((2 : ℕ) : ZMod p) = 0 at htwo
        rw [ZMod.natCast_eq_zero_iff] at htwo
        have hp_le : p ≤ 2 := Nat.le_of_dvd (by norm_num) htwo
        exact hp2 (Nat.le_antisymm hp_le hp.two_le)

private noncomputable def rootEquivPi (d : ℕ) (hd : d ≠ 0) :
    {x : ZMod d // IsTwinRoot d x} ≃
      ∀ p : d.primeFactors,
        {x : ZMod (p.1 ^ d.factorization p.1) //
          IsTwinRoot (p.1 ^ d.factorization p.1) x} :=
  (((ZMod.equivPi d hd).toEquiv.subtypeEquiv fun x => by
      change x * (x + 2) = 0 ↔ ∀ p,
        ((ZMod.equivPi d hd) x p) * (((ZMod.equivPi d hd) x p) + 2) = 0
      calc
        _ ↔ (ZMod.equivPi d hd) (x * (x + 2)) =
            (ZMod.equivPi d hd) 0 :=
          (ZMod.equivPi d hd).injective.eq_iff.symm
        _ ↔ _ := by
          simp only [map_mul, map_add, map_ofNat, _root_.map_zero, funext_iff,
            Pi.mul_apply, Pi.add_apply, Pi.ofNat_apply])).trans
    Equiv.subtypePiEquivPi

theorem card_twinRoots_squarefree {d : ℕ} (hd : Squarefree d) :
    Nat.card {x : ZMod d // IsTwinRoot d x} =
      ∏ p ∈ d.primeFactors, if p = 2 then 1 else 2 := by
  classical
  letI : NeZero d := ⟨hd.ne_zero⟩
  calc
    Nat.card {x : ZMod d // IsTwinRoot d x} =
        Nat.card (∀ p : d.primeFactors,
          {x : ZMod (p.1 ^ d.factorization p.1) //
            IsTwinRoot (p.1 ^ d.factorization p.1) x}) :=
      Nat.card_congr (rootEquivPi d hd.ne_zero)
    _ = ∏ p : d.primeFactors,
        Nat.card {x : ZMod (p.1 ^ d.factorization p.1) //
          IsTwinRoot (p.1 ^ d.factorization p.1) x} := Nat.card_pi
    _ = ∏ p : d.primeFactors, if p.1 = 2 then 1 else 2 := by
      apply prod_congr rfl
      intro p _
      have hp : p.1.Prime := prime_of_mem_primeFactors p.2
      have hfac : d.factorization p.1 = 1 :=
        Nat.factorization_eq_one_of_squarefree hd hp (dvd_of_mem_primeFactors p.2)
      rw [hfac, pow_one]
      exact card_twinRoots_prime hp
    _ = ∏ p ∈ d.primeFactors, if p = 2 then 1 else 2 :=
      prod_coe_sort d.primeFactors fun p => if p = 2 then 1 else 2

end Submission.BrunSieve
