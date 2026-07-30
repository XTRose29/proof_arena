import Submission.OddOrder.MathlibSupport.CharacterValueCyclotomic

namespace Submission

noncomputable section

/-- Every complex character value of a finite group lies in the image of the
cyclotomic field whose conductor is the exponent of the group. -/
theorem brauer_character_in_cyclotomic (G : Type) [Group G] [Fintype G] :
    ∃ φ : CyclotomicField (Monoid.exponent G) ℚ →+* ℂ,
      ∀ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
        (ρ : Representation ℂ G V) (g : G),
        LinearMap.trace ℂ V (ρ g) ∈ φ.range := by
  classical
  let n := Monoid.exponent G
  letI : NeZero n := ⟨Monoid.exponent_ne_zero_of_finite⟩
  letI : IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) :=
    CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero n ℚ
  let ι : CyclotomicField n ℚ →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let φ : CyclotomicField n ℚ →+* ℂ := ι.toRingHom
  let ζ : CyclotomicField n ℚ :=
    IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ)
  have hζ : IsPrimitiveRoot ζ n :=
    IsCyclotomicExtension.zeta_spec n ℚ (CyclotomicField n ℚ)
  refine ⟨φ, ?_⟩
  intro V _ _ _ ρ g
  obtain ⟨q, hq⟩ :=
    OddOrder.MathlibSupport.representation_character_exists_preimage
      ι hζ ρ g (Monoid.order_dvd_exponent g)
  refine ⟨q, ?_⟩
  change ι q = LinearMap.trace ℂ V (ρ g)
  simpa only [Representation.character] using hq

end

end Submission
