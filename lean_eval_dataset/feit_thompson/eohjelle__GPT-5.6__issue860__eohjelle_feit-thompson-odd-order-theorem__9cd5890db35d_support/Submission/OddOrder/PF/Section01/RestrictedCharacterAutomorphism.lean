import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Submission.OddOrder.MathlibSupport.CharacterValueCyclotomic
import Submission.OddOrder.PF.Section01.CoprimeCyclotomicAutomorphism

/-!
# Peterfalvi 1.9(b): restricting a cyclotomic automorphism

An automorphism of the algebraic closure can be preserved on character
values at elements whose orders divide `a`, while making it fix character
values at elements of a fixed finite group whose orders are coprime to `a`.

The proof follows the source `dvd_restrict_cfAut`: collect the complementary
orders in a product `b`, combine the actions on the coprime cyclotomic fields
of orders `a` and `b` using Peterfalvi 1.9(a), and use cyclotomicity of
virtual-character values.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators

universe u v w

/-- Peterfalvi 1.9(b), source `dvd_restrict_cfAut`. -/
theorem dvd_restrict_cfAut
    {K : Type u} [Field K] [Algebra ℚ K] [IsAlgClosure ℚ K]
    (G : Type v) [Group G] [Fintype G]
    (a : ℕ) (mu : K ≃ₐ[ℚ] K) :
    ∃ nu : K ≃ₐ[ℚ] K,
      (∀ {G₀ : Type w} [Group G₀] [Fintype G₀]
          (chi : VirtualCharacter G₀ K) (x : G₀),
          orderOf x ∣ a →
          nu (VirtualCharacter.realize chi x) =
            mu (VirtualCharacter.realize chi x)) ∧
      ∀ (chi : VirtualCharacter G K) (x : G),
        (orderOf x).Coprime a →
        nu (VirtualCharacter.realize chi x) =
          VirtualCharacter.realize chi x := by
  letI : IsAlgClosed K := IsAlgClosure.isAlgClosed ℚ
  by_cases ha0 : a = 0
  · subst a
    refine ⟨mu, fun _ _ _ ↦ rfl, ?_⟩
    intro chi x hx
    have hx1 : orderOf x = 1 := by
      simpa only [Nat.coprime_zero_right] using hx
    have hxo : orderOf x ∣ 1 := by simp [hx1]
    let omega : Kˣ := 1
    have homega : IsPrimitiveRoot omega 1 := by simp [omega]
    simpa only [pow_one] using
      Submission.OddOrder.MathlibSupport.algEquiv_virtualCharacter_apply_eq_pow
        homega mu 1 (by simp [omega]) chi x hxo
  · letI : NeZero a := ⟨ha0⟩
    let b : ℕ := ∏ x : G,
      if (orderOf x).Coprime a then orderOf x else 1
    have hab : a.Coprime b := by
      change a.Coprime
        (∏ x : G, if (orderOf x).Coprime a then orderOf x else 1)
      rw [Nat.coprime_fintype_prod_right_iff]
      intro x
      by_cases hx : (orderOf x).Coprime a
      · rw [if_pos hx]
        exact hx.symm
      · rw [if_neg hx]
        exact Nat.coprime_one_right a
    have hbpos : 0 < b := by
      dsimp only [b]
      apply Finset.prod_pos
      intro x _
      by_cases hx : (orderOf x).Coprime a
      · rw [if_pos hx]
        exact orderOf_pos x
      · rw [if_neg hx]
        exact Nat.zero_lt_one
    letI : NeZero b := ⟨Nat.ne_of_gt hbpos⟩
    letI : CharZero K :=
      charZero_of_injective_algebraMap (algebraMap ℚ K).injective
    let rootsA : Set K :=
      {x | ∃ n ∈ ({a} : Set ℕ), n ≠ 0 ∧ x ^ n = 1}
    let rootsB : Set K :=
      {x | ∃ n ∈ ({b} : Set ℕ), n ≠ 0 ∧ x ^ n = 1}
    let Qa : IntermediateField ℚ K := IntermediateField.adjoin ℚ rootsA
    let Qb : IntermediateField ℚ K := IntermediateField.adjoin ℚ rootsB
    letI : Algebra ℚ Qa := Qa.algebra'
    letI : Algebra ℚ Qb := Qb.algebra'
    letI : IsCyclotomicExtension {a} ℚ Qa := by
      dsimp only [Qa, rootsA]
      apply
        IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot
      intro n hn _
      rw [Set.mem_singleton_iff] at hn
      subst n
      exact HasEnoughRootsOfUnity.exists_primitiveRoot K a
    letI : IsCyclotomicExtension {b} ℚ Qb := by
      dsimp only [Qb, rootsB]
      apply
        IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot
      intro n hn _
      rw [Set.mem_singleton_iff] at hn
      subst n
      exact HasEnoughRootsOfUnity.exists_primitiveRoot K b
    let wa : Qa := IsCyclotomicExtension.zeta a ℚ Qa
    let wb : Qb := IsCyclotomicExtension.zeta b ℚ Qb
    have hwa : IsPrimitiveRoot wa a :=
      IsCyclotomicExtension.zeta_spec a ℚ Qa
    have hwb : IsPrimitiveRoot wb b :=
      IsCyclotomicExtension.zeta_spec b ℚ Qb
    let QaC : Qa →ₐ[ℚ] K := Qa.val
    let QbC : Qb →ₐ[ℚ] K := Qb.val
    have hgenQa : IntermediateField.adjoin ℚ {wa} = ⊤ := by
      apply IntermediateField.toSubalgebra_injective
      rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (Algebra.IsAlgebraic.isAlgebraic wa),
        IntermediateField.top_toSubalgebra]
      exact IsCyclotomicExtension.adjoin_primitive_root_eq_top hwa
    have hgenQb : IntermediateField.adjoin ℚ {wb} = ⊤ := by
      apply IntermediateField.toSubalgebra_injective
      rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (Algebra.IsAlgebraic.isAlgebraic wb),
        IntermediateField.top_toSubalgebra]
      exact IsCyclotomicExtension.adjoin_primitive_root_eq_top hwb
    obtain ⟨nu, hnuQa, hnuQb⟩ :=
      extend_coprime_Qn_aut a b wa wb QaC QbC mu hab
        hwa hgenQa hwb hgenQb
    refine ⟨nu, ?_, ?_⟩
    · intro G₀ _ _ chi x hx
      obtain ⟨q, hq⟩ :=
        Submission.OddOrder.MathlibSupport.virtualCharacter_value_exists_preimage
          QaC hwa chi x hx
      calc
        nu (VirtualCharacter.realize chi x) = nu (QaC q) := by rw [hq]
        _ = mu (QaC q) := hnuQa q
        _ = mu (VirtualCharacter.realize chi x) := by rw [hq]
    · intro chi x hx
      have hxb : orderOf x ∣ b := by
        have hd := Finset.dvd_prod_of_mem
          (fun y : G ↦ if (orderOf y).Coprime a then orderOf y else 1)
          (Finset.mem_univ x)
        change orderOf x ∣
          ∏ y : G, if (orderOf y).Coprime a then orderOf y else 1
        simpa only [if_pos hx] using hd
      obtain ⟨q, hq⟩ :=
        Submission.OddOrder.MathlibSupport.virtualCharacter_value_exists_preimage
          QbC hwb chi x hxb
      calc
        nu (VirtualCharacter.realize chi x) = nu (QbC q) := by rw [hq]
        _ = QbC q := hnuQb q
        _ = VirtualCharacter.realize chi x := hq

end

end Submission.OddOrder.PF
