import Mathlib.Data.Nat.ModEq
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Submission.OddOrder.MathlibSupport.CyclotomicPowerAutomorphism

/-!
# Peterfalvi 1.9(a): compatible cyclotomic automorphisms

Automorphisms prescribed on cyclotomic extensions of coprime orders can be
made compatible in a common algebraic closure.  The proof follows the source:
read the first action as a coprime power, combine that exponent with `1` by
the Chinese remainder theorem, and use the resulting global power
automorphism.
-/

namespace Submission.OddOrder.PF

noncomputable section

universe u v w

private theorem algHom_eq_of_eq_on_primitive_generator
    {F : Type u} {E : Type v} {L : Type w}
    [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra F L] [Algebra.IsAlgebraic F E]
    {z : E} (hgen : IntermediateField.adjoin F {z} = ⊤)
    (f g : E →ₐ[F] L) (hz : f z = g z) : f = g := by
  apply AlgHom.ext_of_adjoin_eq_top
    (IntermediateField.adjoin_eq_top_iff.mp hgen)
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst x
  exact hz

/-- Peterfalvi 1.9(a), source `extend_coprime_Qn_aut`. -/
theorem extend_coprime_Qn_aut
    {Qa Qb K : Type u}
    [Field Qa] [Field Qb] [Field K]
    [Algebra ℚ Qa] [Algebra ℚ Qb] [Algebra ℚ K]
    [Algebra.IsAlgebraic ℚ Qa] [Algebra.IsAlgebraic ℚ Qb]
    [IsAlgClosure ℚ K]
    (a b : ℕ) (wa : Qa) (wb : Qb)
    (QaC : Qa →ₐ[ℚ] K) (QbC : Qb →ₐ[ℚ] K)
    (mu : K ≃ₐ[ℚ] K)
    (hab : a.Coprime b)
    (hwa : IsPrimitiveRoot wa a)
    (hgenQa : IntermediateField.adjoin ℚ {wa} = ⊤)
    (hwb : IsPrimitiveRoot wb b)
    (hgenQb : IntermediateField.adjoin ℚ {wb} = ⊤) :
    ∃ nu : K ≃ₐ[ℚ] K,
      (∀ x : Qa, nu (QaC x) = mu (QaC x)) ∧
      ∀ y : Qb, nu (QbC y) = QbC y := by
  by_cases ha0 : a = 0
  · subst a
    have hb1 : b = 1 := by
      simpa only [Nat.coprime_zero_left] using hab
    have hwb1 : wb = 1 := by
      apply IsPrimitiveRoot.one_right_iff.mp
      simpa only [hb1] using hwb
    refine ⟨mu, fun _ ↦ rfl, ?_⟩
    have heq : mu.toAlgHom.comp QbC = QbC := by
      apply algHom_eq_of_eq_on_primitive_generator
        (F := ℚ) (E := Qb) (L := K) (z := wb) hgenQb
      simp only [hwb1, map_one]
    intro y
    exact DFunLike.congr_fun heq y
  · by_cases hb0 : b = 0
    · subst b
      have ha1 : a = 1 := by
        simpa only [Nat.coprime_zero_right] using hab
      have hwa1 : wa = 1 := by
        apply IsPrimitiveRoot.one_right_iff.mp
        simpa only [ha1] using hwa
      refine ⟨(AlgEquiv.refl : K ≃ₐ[ℚ] K), ?_, fun _ ↦ rfl⟩
      have heq : QaC = mu.toAlgHom.comp QaC := by
        apply algHom_eq_of_eq_on_primitive_generator
          (F := ℚ) (E := Qa) (L := K) (z := wa) hgenQa
        simp only [hwa1, map_one]
      intro x
      exact DFunLike.congr_fun heq x
    · letI : NeZero a := ⟨ha0⟩
      letI : NeZero b := ⟨hb0⟩
      have hwaK : IsPrimitiveRoot (QaC wa) a :=
        hwa.map_of_injective QaC.injective
      have hmuWa : IsPrimitiveRoot (mu (QaC wa)) a :=
        hwaK.map_of_injective mu.injective
      obtain ⟨k, _, hka, hk⟩ := hwaK.isPrimitiveRoot_iff.mp hmuWa
      let c := Nat.chineseRemainder hab k 1
      have hca : (c : ℕ).Coprime a := by
        rw [Nat.coprime_iff_gcd_eq_one, c.property.1.gcd_eq]
        exact Nat.coprime_iff_gcd_eq_one.mp hka
      have hcb : (c : ℕ).Coprime b := by
        rw [Nat.coprime_iff_gcd_eq_one, c.property.2.gcd_eq]
        simp
      have hcab : (c : ℕ).Coprime (a * b) :=
        Nat.Coprime.mul_right hca hcb
      obtain ⟨nu, hnu⟩ :=
        _root_.Submission.OddOrder.MathlibSupport.exists_algEquiv_apply_eq_pow_of_coprime
          (K := K) (a * b) (c : ℕ) hcab
      have hnuWa : nu (QaC wa) = mu (QaC wa) := by
        calc
          nu (QaC wa) = QaC wa ^ (c : ℕ) := hnu _ (by
            rw [pow_mul, hwaK.pow_eq_one, one_pow])
          _ = QaC wa ^ k :=
            pow_eq_pow_of_modEq c.property.1 hwaK.pow_eq_one
          _ = mu (QaC wa) := hk
      have hwbK : IsPrimitiveRoot (QbC wb) b :=
        hwb.map_of_injective QbC.injective
      have hnuWb : nu (QbC wb) = QbC wb := by
        calc
          nu (QbC wb) = QbC wb ^ (c : ℕ) := hnu _ (by
            rw [mul_comm, pow_mul, hwbK.pow_eq_one, one_pow])
          _ = QbC wb ^ 1 :=
            pow_eq_pow_of_modEq c.property.2 hwbK.pow_eq_one
          _ = QbC wb := pow_one _
      refine ⟨nu, ?_, ?_⟩
      · have heq : nu.toAlgHom.comp QaC = mu.toAlgHom.comp QaC := by
          apply algHom_eq_of_eq_on_primitive_generator
            (F := ℚ) (E := Qa) (L := K) (z := wa) hgenQa
          exact hnuWa
        intro x
        exact DFunLike.congr_fun heq x
      · have heq : nu.toAlgHom.comp QbC = QbC := by
          apply algHom_eq_of_eq_on_primitive_generator
            (F := ℚ) (E := Qb) (L := K) (z := wb) hgenQb
          exact hnuWb
        intro y
        exact DFunLike.congr_fun heq y

end

end Submission.OddOrder.PF
