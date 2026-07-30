import Submission.GlobalSlice

namespace Submission.Helpers

variable {K : Type*} [Field K]

lemma length_eq_sum_primeSpectrum_localizations
    (A : Type*) [CommRing A] [Algebra K A] [Module.Finite K A] :
    Module.length K A =
      ∑ᶠ p : PrimeSpectrum A,
        Module.length K (Localization.AtPrime p.asIdeal) := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite K A
  letI : Fintype (PrimeSpectrum A) := Fintype.ofFinite (PrimeSpectrum A)
  letI (p : PrimeSpectrum A) :
      Module.Finite K (Localization.AtPrime p.asIdeal) :=
    Module.Finite.of_surjective
      (Algebra.algHom K A (Localization.AtPrime p.asIdeal)).toLinearMap
      (IsArtinianRing.localization_surjective
        p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal))
  rw [Module.length_eq_finrank K A]
  rw [finsum_eq_sum_of_fintype]
  simp_rw [Module.length_eq_finrank K]
  exact_mod_cast IsArtinianRing.finrank_eq_sum_primeSpectrum A K

end Submission.Helpers
