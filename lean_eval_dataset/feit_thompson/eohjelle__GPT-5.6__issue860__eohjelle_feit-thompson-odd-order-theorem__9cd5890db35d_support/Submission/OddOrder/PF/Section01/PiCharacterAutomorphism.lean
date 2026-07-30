import Submission.OddOrder.MathlibSupport.CyclotomicPowerAutomorphism
import Submission.OddOrder.PF.Section01.RestrictedCharacterAutomorphism

/-!
# Peterfalvi 1.9(b): a power automorphism on selected character values

For an exponent `k` coprime to `a`, there is an automorphism which acts on
all virtual-character values at elements of order dividing `a` by sending
`x` to `x ^ k`, and which fixes the virtual-character values at elements of
a prescribed finite group whose orders are coprime to `a`.

This is the source lemma `make_pi_cfAut`.  It combines the global cyclotomic
power automorphism with `dvd_restrict_cfAut`.
-/

namespace Submission.OddOrder.PF

noncomputable section

universe u v w

/-- Peterfalvi 1.9(b), source `make_pi_cfAut`. -/
theorem make_pi_cfAut
    {K : Type u} [Field K] [Algebra ℚ K] [IsAlgClosure ℚ K]
    (G : Type v) [Group G] [Fintype G]
    (a k : ℕ) (hka : k.Coprime a) :
    ∃ nu : K ≃ₐ[ℚ] K,
      (∀ {G₀ : Type w} [Group G₀] [Fintype G₀]
          (chi : VirtualCharacter G₀ K) (x : G₀),
          orderOf x ∣ a →
          nu (VirtualCharacter.realize chi x) =
            VirtualCharacter.realize chi (x ^ k)) ∧
      ∀ (chi : VirtualCharacter G K) (x : G),
        (orderOf x).Coprime a →
        nu (VirtualCharacter.realize chi x) =
          VirtualCharacter.realize chi x := by
  by_cases ha0 : a = 0
  · subst a
    have hk : k = 1 := by
      simpa only [Nat.coprime_zero_right] using hka
    refine ⟨AlgEquiv.refl, ?_, fun _ _ _ ↦ rfl⟩
    intro G₀ _ _ chi x _
    change VirtualCharacter.realize chi x =
      VirtualCharacter.realize chi (x ^ k)
    simp only [hk, pow_one]
  · letI : NeZero a := ⟨ha0⟩
    letI : IsAlgClosed K := IsAlgClosure.isAlgClosed ℚ
    letI : CharZero K :=
      charZero_of_injective_algebraMap (algebraMap ℚ K).injective
    obtain ⟨mu, hmu⟩ :=
      Submission.OddOrder.MathlibSupport.exists_algEquiv_apply_eq_pow_of_coprime
        (K := K) a k hka
    obtain ⟨nu, hnu, hfix⟩ := dvd_restrict_cfAut G a mu
    obtain ⟨omegaK, homegaK⟩ :=
      HasEnoughRootsOfUnity.exists_primitiveRoot K a
    let omega : Kˣ :=
      Units.mk0 omegaK (homegaK.ne_zero (NeZero.ne a))
    have homega : IsPrimitiveRoot omega a := by
      apply IsPrimitiveRoot.coe_units_iff.mp
      simpa only [omega, Units.val_mk0] using homegaK
    have hmuOmega : mu (omega : K) = (omega : K) ^ k := by
      apply hmu
      simpa only [omega, Units.val_mk0] using homegaK.pow_eq_one
    refine ⟨nu, ?_, hfix⟩
    intro G₀ _ _ chi x hx
    calc
      nu (VirtualCharacter.realize chi x) =
          mu (VirtualCharacter.realize chi x) := hnu chi x hx
      _ = VirtualCharacter.realize chi (x ^ k) :=
        Submission.OddOrder.MathlibSupport.algEquiv_virtualCharacter_apply_eq_pow
          homega mu k hmuOmega chi x hx

end

end Submission.OddOrder.PF
