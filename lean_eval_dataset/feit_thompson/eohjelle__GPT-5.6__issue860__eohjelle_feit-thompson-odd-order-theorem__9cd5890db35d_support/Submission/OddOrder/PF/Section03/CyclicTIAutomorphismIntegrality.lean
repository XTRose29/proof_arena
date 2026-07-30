import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.NumberTheory.Niven
import Submission.OddOrder.MathlibSupport.IrreducibleCharacterDegreeDivides
import Submission.OddOrder.PF.Section01.PiCharacterAutomorphism
import Submission.OddOrder.PF.Section03.CyclicTIUniqueness

/-!
# Automorphisms and integral values of the cyclic-TI isometry

This file ports Peterfalvi (3.9)(b)--(c), corresponding to
`cycTIiso_aut_exists` and `Cint_cycTIiso_coprime` in `PFsection3.v`.

The Coq development uses the order of a linear character.  The present
character API does not yet package a linear character as a homomorphism into
the roots of unity, so the results below use a conductor `a` together with
the concrete hypothesis that every element order in the source divides
`a`.  Taking `a = |W|` always supplies this hypothesis; the corresponding
specializations are provided at the end of the file.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped Classical

universe u

namespace ClassFunction

variable {H R : Type u} [Group H] [Ring R]

/-- Precompose a class function with the `n`-th power map.  The power map
need not be a group homomorphism, but it preserves conjugacy classes. -/
def powerArgument (n : ℕ) : ClassFunction H R →ₗ[R] ClassFunction H R where
  toFun f :=
    ⟨fun x ↦ f (x ^ n), fun x y ↦ by
      simpa only [conj_pow] using
        ClassFunction.conj_apply f x (y ^ n)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem powerArgument_apply (n : ℕ) (f : ClassFunction H R) (x : H) :
    powerArgument n f x = f (x ^ n) :=
  rfl

end ClassFunction

variable {Gamma K : Type u} [Group Gamma] [Fintype Gamma]
  [Field K] [Algebra ℚ K] [IsAlgClosure ℚ K]
  {G W W₁ W₂ : Subgroup Gamma}
  {defW : IsInternalDirectProductIn W₁ W₂ W}

local instance : IsAlgClosed K := IsAlgClosure.isAlgClosed ℚ
local instance : CharZero K :=
  charZero_of_injective_algebraMap (algebraMap ℚ K).injective

namespace CyclicTIHypothesis

/-- Peterfalvi (3.9)(b), in conductor form.

If all element orders of `W` divide `a`, an exponent coprime to `a` is
realized on source character values by a coefficient-field automorphism.
Naturality of the cyclic-TI isometry transports that power action to `G`,
while the same automorphism fixes its values on elements whose orders are
coprime to `a`. -/
theorem cycTIiso_aut_exists
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (w : IrreducibleCharacter W K) (a k : ℕ)
    (hWa : ∀ y : W, orderOf y ∣ a) (hka : k.Coprime a) :
    ∃ nu : K ≃ₐ[ℚ] K,
      h.cyclicTIIsometry
          (ClassFunction.powerArgument k (w : ClassFunction W K)) =
        ClassFunction.mapRingHom nu.toRingEquiv.toRingHom
          (h.cyclicTIIsometry (w : ClassFunction W K)) ∧
      ∀ x : G, (orderOf x).Coprime a →
        h.cyclicTIIsometry
            (ClassFunction.powerArgument k (w : ClassFunction W K)) x =
          h.cyclicTIIsometry (w : ClassFunction W K) x := by
  obtain ⟨nu, hpow, hfix⟩ := make_pi_cfAut (K := K) G a k hka
  have hsource :
      ClassFunction.mapRingHom nu.toRingEquiv.toRingHom
          (w : ClassFunction W K) =
        ClassFunction.powerArgument k (w : ClassFunction W K) := by
    ext y
    change nu (w y) = w (y ^ k)
    have hy := hpow (Finsupp.single w 1 : VirtualCharacter W K) y (hWa y)
    simpa only [ClassFunction.mapRingHom_apply,
      ClassFunction.powerArgument_apply,
      VirtualCharacter.realize_single, ClassFunction.smul_apply,
      Int.cast_one, one_smul] using hy
  have himage :
      h.cyclicTIIsometry
          (ClassFunction.powerArgument k (w : ClassFunction W K)) =
        ClassFunction.mapRingHom nu.toRingEquiv.toRingHom
          (h.cyclicTIIsometry (w : ClassFunction W K)) := by
    rw [← hsource]
    exact (h.cfAut_cycTIiso nu.toRingEquiv
      (w : ClassFunction W K)).symm
  refine ⟨nu, himage, ?_⟩
  intro x hx
  let z : VirtualCharacter G K :=
    h.cyclicTIIsometryVirtual (Finsupp.single w 1)
  have hz : VirtualCharacter.realize z =
      h.cyclicTIIsometry (w : ClassFunction W K) := by
    rw [h.realize_cyclicTIIsometryVirtual]
    simp only [VirtualCharacter.realize_single, Int.cast_one, one_smul]
  calc
    h.cyclicTIIsometry
          (ClassFunction.powerArgument k (w : ClassFunction W K)) x =
        nu (h.cyclicTIIsometry (w : ClassFunction W K) x) := by
      exact congrArg (fun f : ClassFunction G K ↦ f x) himage
    _ = h.cyclicTIIsometry (w : ClassFunction W K) x := by
      simpa only [hz] using hfix z x hx

/-- Peterfalvi (3.9)(c), in conductor form.

At an element whose order is coprime to the source conductor, the image of
an irreducible source character under the cyclic-TI isometry is a rational
algebraic integer, hence an integer.  The existential equality is the Lean
counterpart of membership in Coq's `Num.int`. -/
theorem Cint_cycTIiso_coprime
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (w : IrreducibleCharacter W K) (a : ℕ)
    (hWa : ∀ y : W, orderOf y ∣ a) (x : G)
    (hxa : (orderOf x).Coprime a) :
    ∃ z : ℤ,
      h.cyclicTIIsometry (w : ClassFunction W K) x = (z : K) := by
  let phi : ClassFunction G K :=
    h.cyclicTIIsometry (w : ClassFunction W K)
  have hphiIntegral : IsIntegral ℤ (phi x) := by
    obtain ⟨psi, epsilon, hepsilon, hphi⟩ :=
      (h.cyclicTIIsometryData (k := K)).exists_signed_irreducible_image w
    have hpsi : IsIntegral ℤ (psi x) := by
      rw [← psi.representation_character]
      exact
        Submission.OddOrder.MathlibSupport.representation_character_isIntegral
          psi.representation.ρ x
    have hepsilonIntegral : IsIntegral ℤ (epsilon : K) := by
      exact isIntegral_intCast epsilon
    have hvalue : phi x = (epsilon : K) * psi x := by
      exact congrArg (fun f : ClassFunction G K ↦ f x) hphi
    rw [hvalue]
    exact hepsilonIntegral.mul hpsi
  have hphiFixed : ∀ sigma : K ≃ₐ[ℚ] K, sigma (phi x) = phi x := by
    intro sigma
    obtain ⟨nu, hagree, hfix⟩ :=
      dvd_restrict_cfAut (K := K) G a sigma
    have hsource :
        ClassFunction.mapRingHom nu.toRingEquiv.toRingHom
            (w : ClassFunction W K) =
          ClassFunction.mapRingHom sigma.toRingEquiv.toRingHom
            (w : ClassFunction W K) := by
      ext y
      change nu (w y) = sigma (w y)
      have hy := hagree
        (Finsupp.single w 1 : VirtualCharacter W K) y (hWa y)
      simpa only [ClassFunction.mapRingHom_apply,
        VirtualCharacter.realize_single, ClassFunction.smul_apply,
        Int.cast_one, one_smul] using hy
    let z : VirtualCharacter G K :=
      h.cyclicTIIsometryVirtual (Finsupp.single w 1)
    have hz : VirtualCharacter.realize z = phi := by
      rw [h.realize_cyclicTIIsometryVirtual]
      simp only [VirtualCharacter.realize_single, Int.cast_one, one_smul,
        phi]
    calc
      sigma (phi x) =
          h.cyclicTIIsometry
            (ClassFunction.mapRingHom sigma.toRingEquiv.toRingHom
              (w : ClassFunction W K)) x := by
        exact congrArg (fun f : ClassFunction G K ↦ f x)
          (h.cfAut_cycTIiso sigma.toRingEquiv
            (w : ClassFunction W K))
      _ = h.cyclicTIIsometry
            (ClassFunction.mapRingHom nu.toRingEquiv.toRingHom
              (w : ClassFunction W K)) x := by
        rw [hsource]
      _ = nu (phi x) := by
        exact congrArg (fun f : ClassFunction G K ↦ f x)
          (h.cfAut_cycTIiso nu.toRingEquiv
            (w : ClassFunction W K)).symm
      _ = phi x := by
        simpa only [hz] using hfix z x hxa
  have hphiRat : ∃ q : ℚ, phi x = (q : K) := by
    have hmem : phi x ∈ Set.range (algebraMap ℚ K) :=
      (InfiniteGalois.mem_range_algebraMap_iff_fixed (phi x)).2 hphiFixed
    obtain ⟨q, hq⟩ := hmem
    refine ⟨q, hq.symm.trans ?_⟩
    exact map_ratCast (algebraMap ℚ K) q
  obtain ⟨z, hz⟩ :=
    (IsIntegral.exists_int_iff_exists_rat hphiIntegral).mp hphiRat
  exact ⟨z, hz⟩

/-- The always-available `a = |W|` specialization of
`cycTIiso_aut_exists`. -/
theorem cycTIiso_aut_exists_card
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (w : IrreducibleCharacter W K) (k : ℕ)
    (hk : k.Coprime (Fintype.card W)) :
    ∃ nu : K ≃ₐ[ℚ] K,
      h.cyclicTIIsometry
          (ClassFunction.powerArgument k (w : ClassFunction W K)) =
        ClassFunction.mapRingHom nu.toRingEquiv.toRingHom
          (h.cyclicTIIsometry (w : ClassFunction W K)) ∧
      ∀ x : G, (orderOf x).Coprime (Fintype.card W) →
        h.cyclicTIIsometry
            (ClassFunction.powerArgument k (w : ClassFunction W K)) x =
          h.cyclicTIIsometry (w : ClassFunction W K) x :=
  h.cycTIiso_aut_exists w (Fintype.card W) k
    (fun _ ↦ orderOf_dvd_card) hk

/-- The always-available `a = |W|` specialization of
`Cint_cycTIiso_coprime`. -/
theorem Cint_cycTIiso_coprime_card
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (w : IrreducibleCharacter W K) (x : G)
    (hx : (orderOf x).Coprime (Fintype.card W)) :
    ∃ z : ℤ,
      h.cyclicTIIsometry (w : ClassFunction W K) x = (z : K) :=
  h.Cint_cycTIiso_coprime w (Fintype.card W)
    (fun _ ↦ orderOf_dvd_card) x hx

end CyclicTIHypothesis

end

end Submission.OddOrder.PF
