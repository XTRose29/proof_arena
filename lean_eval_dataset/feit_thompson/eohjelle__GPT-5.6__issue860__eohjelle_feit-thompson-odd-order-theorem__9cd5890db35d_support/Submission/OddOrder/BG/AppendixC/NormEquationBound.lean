import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.Tactic

/-!
# Bender--Glauberman Appendix C: the norm-equation bound

This file isolates the finite-field argument in Lemma C.1 of Coq
`BGappendixC.v`.  It is independent of the group-theoretic hypotheses used
later in Appendix C.

For a finite extension `F / ZMod p`, let `E` be the set of `x : F` such that
both `x` and `2 - x` have norm one.  If `E` is stable under inversion and has
more than one element, then the cardinality `p` of the prime field is at most
the degree of the extension.
-/

namespace Submission.OddOrder.BG.AppendixC

noncomputable section

open scoped BigOperators Polynomial

universe u v

/-- The set called `E` in Bender--Glauberman Appendix C, Lemma C.1. -/
def normEquationSet
    (K : Type u) (F : Type v)
    [CommRing K] [CommRing F] [Algebra K F] : Set F :=
  {x | Algebra.norm K x = 1 ∧ Algebra.norm K (2 - x) = 1}

@[simp]
theorem mem_normEquationSet_iff
    (K : Type u) (F : Type v)
    [CommRing K] [CommRing F] [Algebra K F] (x : F) :
    x ∈ normEquationSet K F ↔
      Algebra.norm K x = 1 ∧ Algebra.norm K (2 - x) = 1 :=
  Iff.rfl

@[simp]
theorem one_mem_normEquationSet
    (K : Type u) (F : Type v)
    [CommRing K] [CommRing F] [Algebra K F] :
    (1 : F) ∈ normEquationSet K F := by
  change Algebra.norm K (1 : F) = 1 ∧
    Algebra.norm K ((2 : F) - 1) = 1
  constructor
  · exact map_one (Algebra.norm K)
  · rw [show (2 : F) - 1 = 1 by ring]
    exact map_one (Algebra.norm K)

/-- The two norm equations are exchanged by the reflection `x ↦ 2 - x`. -/
theorem two_sub_mem_normEquationSet_iff
    (K : Type u) (F : Type v)
    [CommRing K] [CommRing F] [Algebra K F] (x : F) :
    2 - x ∈ normEquationSet K F ↔ x ∈ normEquationSet K F := by
  simp only [mem_normEquationSet_iff]
  rw [show (2 : F) - (2 - x) = x by ring]
  exact and_comm

/-- The fractional transformation used in the proof of Lemma C.1. -/
def normEquationTau {F : Type v} [Field F] (x : F) : F :=
  (2 - x)⁻¹

/-- Inversion stability of `E` makes the transformation
`x ↦ (2 - x)⁻¹` preserve `E`. -/
theorem normEquationTau_mem
    (K : Type u) (F : Type v)
    [CommRing K] [Field F] [Algebra K F]
    (hinv : Set.MapsTo (·⁻¹) (normEquationSet K F)
      (normEquationSet K F))
    {x : F} (hx : x ∈ normEquationSet K F) :
    normEquationTau x ∈ normEquationSet K F := by
  exact hinv ((two_sub_mem_normEquationSet_iff K F x).2 hx)

/-- The image equality used literally in the Coq statement implies the
one-sided inversion stability needed by the proof. -/
theorem normEquationSet_inv_mapsTo_of_eq_image
    (K : Type u) (F : Type v)
    [CommRing K] [Field F] [Algebra K F]
    (hinv : normEquationSet K F =
      (fun x : F ↦ x⁻¹) '' normEquationSet K F) :
    Set.MapsTo (·⁻¹) (normEquationSet K F) (normEquationSet K F) := by
  intro x hx
  rw [hinv]
  exact ⟨x, hx, rfl⟩

/-- Bender--Glauberman Appendix C, Lemma C.1, in a form independent of the
later group-theoretic argument.

The base field is written as `ZMod p` because the proof enumerates it by the
successive natural-number multiples of `1`.  The conclusion is the stronger,
intrinsic inequality against the extension degree; the source conclusion
`p ≤ q` follows by rewriting `Module.finrank (ZMod p) F = q`. -/
theorem primeField_card_le_finrank_of_normEquationSet_inv
    {p : ℕ} [Fact p.Prime]
    (F : Type v) [Field F] [Finite F]
    [Algebra (ZMod p) F] [FiniteDimensional (ZMod p) F]
    (hinv : Set.MapsTo (·⁻¹) (normEquationSet (ZMod p) F)
      (normEquationSet (ZMod p) F))
    (hcard : 1 < (normEquationSet (ZMod p) F).ncard) :
    p ≤ Module.finrank (ZMod p) F := by
  classical
  let E := normEquationSet (ZMod p) F
  obtain ⟨a, haE, ha1⟩ :=
    Set.exists_ne_of_one_lt_ncard hcard (1 : F)
  let h : ℕ → F := fun n ↦ (1 - a) * (n : F) + 1

  have hratio : ∀ n : ℕ, h n / h (n + 1) ∈ E := by
    intro n
    induction n with
    | zero =>
        have htau := normEquationTau_mem (ZMod p) F hinv haE
        have heq : h 0 / h (0 + 1) = normEquationTau a := by
          simp only [h, normEquationTau, Nat.cast_zero, mul_zero,
            zero_add, Nat.cast_one, mul_one, one_div]
          congr 1
          ring
        rwa [heq]
    | succ n ih =>
        have hden : h (n + 1) ≠ 0 := by
          intro hzero
          have hnormZero : (0 : ZMod p) = 1 := by
            simpa [hzero] using
              (show Algebra.norm (ZMod p) (h n / h (n + 1)) = 1 from ih.1)
          exact zero_ne_one hnormZero
        have htau := normEquationTau_mem (ZMod p) F hinv ih
        have heq :
            normEquationTau (h n / h (n + 1)) =
              h (n + 1) / h (n + 2) := by
          unfold normEquationTau
          have hsub :
              (2 : F) - h n / h (n + 1) = h (n + 2) / h (n + 1) := by
            field_simp [hden]
            simp only [h, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
            ring
          rw [hsub, inv_div]
        rw [heq] at htau
        convert htau using 1 <;> omega

  have hnorm : ∀ n : ℕ, Algebra.norm (ZMod p) (h n) = 1 := by
    intro n
    induction n with
    | zero => simp [h]
    | succ n ih =>
        have hr := (hratio n).1
        rw [div_eq_mul_inv, map_mul, Algebra.norm_inv, ih, one_mul] at hr
        have := congrArg Inv.inv hr
        simpa using this

  let P : Polynomial F :=
    ∏ σ : F ≃ₐ[ZMod p] F,
      (Polynomial.C (σ (1 - a)) * Polynomial.X + Polynomial.C 1)

  have hcoeff (σ : F ≃ₐ[ZMod p] F) : σ (1 - a) ≠ 0 := by
    intro hzero
    have hzero' : σ (1 - a) = σ 0 := by simpa using hzero
    exact (sub_ne_zero.mpr ha1.symm) (σ.injective hzero')

  have hfactorDegree (σ : F ≃ₐ[ZMod p] F) :
      (Polynomial.C (σ (1 - a)) * Polynomial.X +
        Polynomial.C 1).natDegree = 1 :=
    Polynomial.natDegree_linear (hcoeff σ)

  have hfactorNe (σ : F ≃ₐ[ZMod p] F) :
      Polynomial.C (σ (1 - a)) * Polynomial.X +
          Polynomial.C 1 ≠ 0 := by
    intro hz
    have := hfactorDegree σ
    rw [hz] at this
    simp at this

  have hPdegree : P.natDegree = Module.finrank (ZMod p) F := by
    calc
      P.natDegree =
          ∑ σ : F ≃ₐ[ZMod p] F,
            (Polynomial.C (σ (1 - a)) * Polynomial.X +
              Polynomial.C 1).natDegree := by
        simpa [P] using
          Polynomial.natDegree_prod
            (s := Finset.univ)
            (f := fun σ : F ≃ₐ[ZMod p] F ↦
              Polynomial.C (σ (1 - a)) * Polynomial.X +
                Polynomial.C 1)
            (fun σ _ ↦ hfactorNe σ)
      _ = Fintype.card (F ≃ₐ[ZMod p] F) := by
        calc
          ∑ σ : F ≃ₐ[ZMod p] F,
              (Polynomial.C (σ (1 - a)) * Polynomial.X +
                Polynomial.C 1).natDegree =
              ∑ _σ : F ≃ₐ[ZMod p] F, 1 := by
            apply Finset.sum_congr rfl
            intro σ _
            exact hfactorDegree σ
          _ = Fintype.card (F ≃ₐ[ZMod p] F) := by simp
      _ = Module.finrank (ZMod p) F := by
        rw [Fintype.card_eq_nat_card,
          IsGalois.card_aut_eq_finrank]

  have hPsubDegree :
      (P - 1).natDegree = Module.finrank (ZMod p) F := by
    calc
      (P - 1).natDegree = P.natDegree :=
        Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by
          simpa [hPdegree] using (Module.finrank_pos :
            0 < Module.finrank (ZMod p) F))
      _ = Module.finrank (ZMod p) F := hPdegree

  have hPsubNe : P - 1 ≠ 0 := by
    intro hz
    have hzero := hPsubDegree
    rw [hz] at hzero
    have hpos : 0 < Module.finrank (ZMod p) F := Module.finrank_pos
    simp only [Polynomial.natDegree_zero] at hzero
    omega

  have hPeval (b : ZMod p) :
      P.eval (algebraMap (ZMod p) F b) = 1 := by
    have hb : algebraMap (ZMod p) F b = (b.val : F) := by
      calc
        algebraMap (ZMod p) F b =
            algebraMap (ZMod p) F (b.val : ZMod p) :=
          congrArg (algebraMap (ZMod p) F)
            (ZMod.natCast_zmod_val b).symm
        _ = (b.val : F) :=
          map_natCast (algebraMap (ZMod p) F) b.val
    calc
      P.eval (algebraMap (ZMod p) F b) =
          ∏ σ : F ≃ₐ[ZMod p] F,
            σ ((1 - a) * algebraMap (ZMod p) F b + 1) := by
        simp only [P, Polynomial.eval_prod]
        apply Finset.prod_congr rfl
        intro σ _
        simp
      _ = algebraMap (ZMod p) F
          (Algebra.norm (ZMod p)
            ((1 - a) * algebraMap (ZMod p) F b + 1)) :=
        (Algebra.norm_eq_prod_automorphisms
          (K := ZMod p) (L := F)
          ((1 - a) * algebraMap (ZMod p) F b + 1)).symm
      _ = 1 := by
        rw [hb]
        change algebraMap (ZMod p) F
          (Algebra.norm (ZMod p) (h b.val)) = 1
        rw [hnorm, map_one]

  by_contra hpq
  have hqp : Module.finrank (ZMod p) F < p := Nat.lt_of_not_ge hpq
  have hzero : P - 1 = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      (P - 1) (algebraMap (ZMod p) F).injective
    · intro b
      simp [hPeval b]
    · simpa [hPsubDegree, ZMod.card] using hqp
  exact hPsubNe hzero

/-- The `p ≤ q` formulation used literally in the Coq source. -/
theorem prime_le_of_normEquationSet_inv
    {p q : ℕ} [Fact p.Prime]
    (F : Type v) [Field F] [Finite F]
    [Algebra (ZMod p) F] [FiniteDimensional (ZMod p) F]
    (hfinrank : Module.finrank (ZMod p) F = q)
    (hinv : Set.MapsTo (·⁻¹) (normEquationSet (ZMod p) F)
      (normEquationSet (ZMod p) F))
    (hcard : 1 < (normEquationSet (ZMod p) F).ncard) :
    p ≤ q := by
  rw [← hfinrank]
  exact primeField_card_le_finrank_of_normEquationSet_inv F hinv hcard

/-- The source-faithful image-equality formulation of Lemma C.1. -/
theorem prime_le_of_normEquationSet_eq_image_inv
    {p q : ℕ} [Fact p.Prime]
    (F : Type v) [Field F] [Finite F]
    [Algebra (ZMod p) F] [FiniteDimensional (ZMod p) F]
    (hfinrank : Module.finrank (ZMod p) F = q)
    (hinv : normEquationSet (ZMod p) F =
      (fun x : F ↦ x⁻¹) '' normEquationSet (ZMod p) F)
    (hcard : 1 < (normEquationSet (ZMod p) F).ncard) :
    p ≤ q :=
  prime_le_of_normEquationSet_inv F hfinrank
    (normEquationSet_inv_mapsTo_of_eq_image (ZMod p) F hinv) hcard

end

end Submission.OddOrder.BG.AppendixC
