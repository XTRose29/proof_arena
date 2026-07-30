import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Submission.OddOrder.BG.AppendixC.Arithmetic
import Submission.OddOrder.BG.AppendixC.FiniteFieldImage

/-!
# The norm-one image in Bender--Glauberman Appendix C

This file ports `BGappendixC.v`, lines 157--179 (Remark VII).  If the
finite-field image of `U` has order

`nU p q = (p ^ q - 1) / (p - 1)`,

then its underlying field values are exactly the elements of norm one over
the prime field `ZMod p`.

The Coq proof chooses generators and invokes Hilbert 90.  In Lean the same
conclusion follows directly from the standard finite-field norm formula:
both sides describe the subgroup of `nU p q`-th roots of unity in the
cyclic group of nonzero field elements.
-/

namespace Submission.OddOrder.BG.AppendixC

noncomputable section

universe u v

variable {G : Type u} [Group G]

namespace FiniteFieldImage

variable {P P0 U : Subgroup G} (h : FiniteFieldImage P P0 U)

/-- The unit-valued image of `U` is the subgroup of `nU p q`-th roots of
unity.  This is the group-theoretic core of `BGappendixC.v: im_psi`. -/
theorem psi_range_eq_powMonoidHom_ker
    {p q : ℕ} [Fact p.Prime]
    (hcardF : Nat.card h.F = p ^ q)
    (hcardU : Nat.card U = nU p q) :
    h.psi.range =
      (powMonoidHom (nU p q) : h.Fˣ →* h.Fˣ).ker := by
  let R : Subgroup h.Fˣ :=
    (powMonoidHom (nU p q) : h.Fˣ →* h.Fˣ).ker
  have hp : p.Prime := Fact.out
  have hnU_dvd : nU p q ∣ Nat.card h.Fˣ := by
    rw [Nat.card_units, hcardF]
    exact ⟨p - 1, (nU_mul_sub_one p q hp.one_lt.le).symm⟩
  have hRcard : Nat.card R = nU p q := by
    change Nat.card
      (powMonoidHom (nU p q) : h.Fˣ →* h.Fˣ).ker = nU p q
    rw [IsCyclic.card_powMonoidHom_ker,
      Nat.gcd_eq_right_iff_dvd]
    exact hnU_dvd
  have himageCard : Nat.card h.psi.range = nU p q := by
    calc
      Nat.card h.psi.range = Nat.card U :=
        (Nat.card_congr (h.psi.ofInjective h.psi_injective).toEquiv).symm
      _ = nU p q := hcardU
  have himage_le : h.psi.range ≤ R := by
    rintro y ⟨u, rfl⟩
    rw [MonoidHom.mem_ker]
    change h.psi u ^ nU p q = 1
    calc
      h.psi u ^ nU p q = h.psi (u ^ nU p q) :=
        (map_pow h.psi u (nU p q)).symm
      _ = h.psi (u ^ Nat.card U) := by rw [hcardU]
      _ = h.psi 1 :=
        congrArg h.psi (pow_card_eq_one' (x := u))
      _ = 1 := h.psi.map_one
  change h.psi.range = R
  exact Subgroup.eq_of_le_of_card_ge himage_le
    (by rw [hRcard, himageCard])

/-- Bender--Glauberman Appendix C, Remark VII (`BGappendixC.v: im_psi`):
the field-valued image of `U` consists exactly of the elements whose norm
to the prime field is one. -/
theorem mem_range_psiValue_iff_norm_eq_one
    {p q : ℕ} [Fact p.Prime]
    [Algebra (ZMod p) h.F]
    (hcardF : Nat.card h.F = p ^ q)
    (hcardU : Nat.card U = nU p q)
    (x : h.F) :
    x ∈ Set.range h.psiValue ↔
      Algebra.norm (ZMod p) x = 1 := by
  have hp : p.Prime := Fact.out
  have himage := h.psi_range_eq_powMonoidHom_ker hcardF hcardU
  have hnormExponent :
      (Nat.card h.F - 1) / (Nat.card (ZMod p) - 1) = nU p q := by
    rw [Nat.card_zmod, hcardF]
    exact (nU_eq_div_of_prime hp).symm
  constructor
  · rintro ⟨u, rfl⟩
    apply (algebraMap (ZMod p) h.F).injective
    rw [map_one, FiniteField.algebraMap_norm_eq_pow,
      hnormExponent]
    have hu : (h.psi u) ^ nU p q = 1 := by
      calc
        (h.psi u) ^ nU p q = h.psi (u ^ nU p q) :=
          (map_pow h.psi u (nU p q)).symm
        _ = h.psi (u ^ Nat.card U) := by rw [hcardU]
        _ = h.psi 1 :=
          congrArg h.psi (pow_card_eq_one' (x := u))
        _ = 1 := h.psi.map_one
    simpa [psiValue] using congrArg Units.val hu
  · intro hxnorm
    have hx0 : x ≠ 0 := by
      intro hx
      rw [hx, Algebra.norm_zero] at hxnorm
      exact zero_ne_one hxnorm
    let xu : h.Fˣ := Units.mk0 x hx0
    have hxpow : x ^ nU p q = 1 := by
      calc
        x ^ nU p q =
            algebraMap (ZMod p) h.F (Algebra.norm (ZMod p) x) := by
          rw [FiniteField.algebraMap_norm_eq_pow, hnormExponent]
        _ = 1 := by rw [hxnorm, map_one]
    have hxu_mem : xu ∈
        (powMonoidHom (nU p q) : h.Fˣ →* h.Fˣ).ker := by
      rw [MonoidHom.mem_ker]
      apply Units.ext
      simpa [xu] using hxpow
    have hxu_range : xu ∈ h.psi.range := by
      rw [himage]
      exact hxu_mem
    rcases hxu_range with ⟨u, hu⟩
    refine ⟨u, ?_⟩
    simpa [psiValue, xu] using congrArg Units.val hu

/-- Source-facing form of `BGappendixC.v: im_psi`.  The Coq context states
the cardinality hypothesis for `P`; the finite-field realization transports
it to `h.F`. -/
theorem im_psi
    {p q : ℕ} [Fact p.Prime]
    [Algebra (ZMod p) h.F]
    (hcardP : Nat.card P = p ^ q)
    (hcardU : Nat.card U = nU p q)
    (x : h.F) :
    x ∈ Set.range h.psiValue ↔
      Algebra.norm (ZMod p) x = 1 :=
  h.mem_range_psiValue_iff_norm_eq_one
    (h.natCard_P_eq_field.symm.trans hcardP) hcardU x

end FiniteFieldImage

end

end Submission.OddOrder.BG.AppendixC
