import Mathlib.FieldTheory.Normal.Basic
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Power automorphisms of an algebraic closure

An exponent coprime to `n` determines an automorphism of an algebraic
closure of `ℚ` that raises every `n`-th root of unity to that exponent.
This is the Mathlib analogue of the source lemma `Qn_aut_exists`.
-/

namespace Submission.OddOrder.MathlibSupport

noncomputable section

open Polynomial

universe u

/-- A coprime exponent acts on all `n`-th roots of unity through an
automorphism of an algebraic closure of `ℚ`. -/
theorem exists_algEquiv_apply_eq_pow_of_coprime
    {K : Type u} [Field K] [Algebra ℚ K] [IsAlgClosure ℚ K]
    (n k : ℕ) (hkn : k.Coprime n) :
    ∃ σ : K ≃ₐ[ℚ] K, ∀ x : K, x ^ n = 1 → σ x = x ^ k := by
  letI : IsAlgClosed K := IsAlgClosure.isAlgClosed ℚ
  letI : CharZero K :=
    charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  by_cases hn : n = 0
  · subst n
    have hk : k = 1 := k.coprime_zero_right.mp hkn
    refine ⟨AlgEquiv.refl, ?_⟩
    intro x _
    simp [hk]
  · letI : NeZero n := ⟨hn⟩
    let roots : Set K :=
      {x | ∃ m ∈ ({n} : Set ℕ), m ≠ 0 ∧ x ^ m = 1}
    let E : IntermediateField ℚ K := IntermediateField.adjoin ℚ roots
    letI : Algebra ℚ E := E.algebra'
    letI : IsCyclotomicExtension {n} ℚ E := by
      dsimp only [E, roots]
      apply IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot
      intro m hm _
      rw [Set.mem_singleton_iff] at hm
      subst m
      exact HasEnoughRootsOfUnity.exists_primitiveRoot K n
    let zeta : E := IsCyclotomicExtension.zeta n ℚ E
    have hzeta : IsPrimitiveRoot zeta n :=
      IsCyclotomicExtension.zeta_spec n ℚ E
    have hirr : Irreducible (cyclotomic n ℚ) :=
      cyclotomic.irreducible_rat (Nat.pos_of_ne_zero hn)
    let tau : E ≃ₐ[ℚ] E :=
      IsCyclotomicExtension.fromZetaAut
        (hzeta.pow_of_coprime k hkn) hirr
    have htauZeta : tau zeta = zeta ^ k := by
      dsimp only [tau, zeta]
      exact IsCyclotomicExtension.fromZetaAut_spec
        (hzeta.pow_of_coprime k hkn) hirr
    refine ⟨tau.liftNormal K, ?_⟩
    intro x hx
    have hxE : x ∈ E := by
      apply IntermediateField.subset_adjoin
      exact ⟨n, Set.mem_singleton n, hn, hx⟩
    let xE : E := ⟨x, hxE⟩
    have hxEpow : xE ^ n = 1 := by
      apply Subtype.ext
      exact hx
    have htauX : tau xE = xE ^ k := by
      obtain ⟨i, _, hi⟩ := hzeta.eq_pow_of_pow_eq_one hxEpow
      calc
        tau xE = tau (zeta ^ i) := congrArg tau hi.symm
        _ = (tau zeta) ^ i := map_pow tau zeta i
        _ = (zeta ^ k) ^ i := by rw [htauZeta]
        _ = (zeta ^ i) ^ k := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ = xE ^ k := congrArg (fun y : E ↦ y ^ k) hi
    have hlift := tau.liftNormal_commutes K xE
    calc
      tau.liftNormal K x = algebraMap E K (tau xE) := by
        simpa only [xE, IntermediateField.algebraMap_apply] using hlift
      _ = algebraMap E K (xE ^ k) := congrArg (algebraMap E K) htauX
      _ = x ^ k := by simp only [map_pow, xE, IntermediateField.algebraMap_apply]

end

end Submission.OddOrder.MathlibSupport
