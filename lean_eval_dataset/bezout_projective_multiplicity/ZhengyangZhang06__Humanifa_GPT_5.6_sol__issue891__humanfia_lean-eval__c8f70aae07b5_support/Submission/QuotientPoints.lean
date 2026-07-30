import Submission.ArtinianDecomposition

open MvPolynomial

namespace Submission.Helpers

variable {K : Type*} [Field K]

lemma exists_quotientPrimePoint [IsAlgClosed K] {σ : Type*} [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    [Module.Finite K (MvPolynomial σ K ⧸ I)]
    (p : PrimeSpectrum (MvPolynomial σ K ⧸ I)) :
    ∃ q : σ → K,
      p.asIdeal.comap (Ideal.Quotient.mk I) =
        MvPolynomial.vanishingIdeal K {q} := by
  letI : IsArtinianRing (MvPolynomial σ K ⧸ I) :=
    IsArtinianRing.of_finite K (MvPolynomial σ K ⧸ I)
  letI : p.asIdeal.IsMaximal :=
    (IsArtinianRing.isPrime_iff_isMaximal p.asIdeal).mp p.isPrime
  letI :
      (p.asIdeal.comap (Ideal.Quotient.mk I)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  exact MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K inferInstance

noncomputable def quotientPrimePoint [IsAlgClosed K] {σ : Type*} [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    [Module.Finite K (MvPolynomial σ K ⧸ I)]
    (p : PrimeSpectrum (MvPolynomial σ K ⧸ I)) : σ → K :=
  Classical.choose (exists_quotientPrimePoint I p)

lemma quotientPrimePoint_spec [IsAlgClosed K] {σ : Type*} [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    [Module.Finite K (MvPolynomial σ K ⧸ I)]
    (p : PrimeSpectrum (MvPolynomial σ K ⧸ I)) :
    p.asIdeal.comap (Ideal.Quotient.mk I) =
      MvPolynomial.vanishingIdeal K {quotientPrimePoint I p} :=
  Classical.choose_spec (exists_quotientPrimePoint I p)

lemma quotientPrimePoint_mem_zeroLocus [IsAlgClosed K]
    {σ : Type*} [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    [Module.Finite K (MvPolynomial σ K ⧸ I)]
    (p : PrimeSpectrum (MvPolynomial σ K ⧸ I)) :
    quotientPrimePoint I p ∈ MvPolynomial.zeroLocus K I := by
  intro g hg
  rw [← MvPolynomial.mem_vanishingIdeal_singleton_iff]
  rw [← quotientPrimePoint_spec I p]
  exact Ideal.mem_comap.mpr
    (show Ideal.Quotient.mk I g ∈ p.asIdeal by
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hg]
      exact p.asIdeal.zero_mem)

noncomputable def zeroLocusQuotientPrime [IsAlgClosed K]
    {σ : Type*} [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    (q : MvPolynomial.zeroLocus K I) :
    PrimeSpectrum (MvPolynomial σ K ⧸ I) := by
  let J : Ideal (MvPolynomial σ K) :=
    MvPolynomial.vanishingIdeal K {(q : σ → K)}
  have hIJ : I ≤ J := by
    intro g hg
    exact MvPolynomial.mem_vanishingIdeal_singleton_iff
      (q : σ → K) g |>.mpr (q.property g hg)
  exact ⟨J.map (Ideal.Quotient.mk I),
    Ideal.isPrime_map_quotientMk_of_isPrime hIJ⟩

@[simp]
lemma zeroLocusQuotientPrime_asIdeal [IsAlgClosed K]
    {σ : Type*} [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    (q : MvPolynomial.zeroLocus K I) :
    (zeroLocusQuotientPrime I q).asIdeal =
      (MvPolynomial.vanishingIdeal K {(q : σ → K)}).map
        (Ideal.Quotient.mk I) :=
  rfl

lemma quotientPrimePoint_injective [IsAlgClosed K]
    {σ : Type*} [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    [Module.Finite K (MvPolynomial σ K ⧸ I)] :
    Function.Injective (quotientPrimePoint I) := by
  intro p p' hpp'
  apply PrimeSpectrum.ext
  rw [← Ideal.map_comap_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective p.asIdeal,
    ← Ideal.map_comap_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective p'.asIdeal,
    quotientPrimePoint_spec I p, quotientPrimePoint_spec I p', hpp']

lemma quotientPrimePoint_zeroLocusQuotientPrime [IsAlgClosed K]
    {σ : Type*} [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    [Module.Finite K (MvPolynomial σ K ⧸ I)]
    (q : MvPolynomial.zeroLocus K I) :
    quotientPrimePoint I (zeroLocusQuotientPrime I q) = q := by
  have hcomap :
      (zeroLocusQuotientPrime I q).asIdeal.comap
          (Ideal.Quotient.mk I) =
        MvPolynomial.vanishingIdeal K {(q : σ → K)} := by
    rw [zeroLocusQuotientPrime_asIdeal,
      Ideal.comap_map_quotientMk, sup_eq_right]
    intro g hg
    exact MvPolynomial.mem_vanishingIdeal_singleton_iff
      (q : σ → K) g |>.mpr (q.property g hg)
  have hideals :
      MvPolynomial.vanishingIdeal K {quotientPrimePoint I
          (zeroLocusQuotientPrime I q)} =
        MvPolynomial.vanishingIdeal K {(q : σ → K)} := by
    rw [← quotientPrimePoint_spec I (zeroLocusQuotientPrime I q), hcomap]
  funext i
  have hmem :
      X i - C ((q : σ → K) i) ∈
        MvPolynomial.vanishingIdeal K {(q : σ → K)} :=
    MvPolynomial.mem_vanishingIdeal_singleton_iff
      (q : σ → K) (X i - C ((q : σ → K) i)) |>.mpr (by simp)
  rw [← hideals, MvPolynomial.mem_vanishingIdeal_singleton_iff] at hmem
  exact sub_eq_zero.mp (by simpa using hmem)

noncomputable def quotientPrimeSpectrumEquivZeroLocus [IsAlgClosed K]
    {σ : Type*} [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    [Module.Finite K (MvPolynomial σ K ⧸ I)] :
    PrimeSpectrum (MvPolynomial σ K ⧸ I) ≃
      MvPolynomial.zeroLocus K I where
  toFun p := ⟨quotientPrimePoint I p, quotientPrimePoint_mem_zeroLocus I p⟩
  invFun := zeroLocusQuotientPrime I
  left_inv p := quotientPrimePoint_injective I <|
    quotientPrimePoint_zeroLocusQuotientPrime I
      ⟨quotientPrimePoint I p, quotientPrimePoint_mem_zeroLocus I p⟩
  right_inv q := Subtype.ext (quotientPrimePoint_zeroLocusQuotientPrime I q)

@[simp]
lemma quotientPrimeSpectrumEquivZeroLocus_apply [IsAlgClosed K]
    {σ : Type*} [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    [Module.Finite K (MvPolynomial σ K ⧸ I)]
    (p : PrimeSpectrum (MvPolynomial σ K ⧸ I)) :
    (quotientPrimeSpectrumEquivZeroLocus I p : σ → K) =
      quotientPrimePoint I p :=
  rfl

lemma maxIdealAt_eq_vanishingIdeal {n : ℕ}
    (q : Fin (n + 1) → K) :
    LeanEval.AlgebraicGeometry.maxIdealAt q =
      MvPolynomial.vanishingIdeal K {q} := by
  ext g
  rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
  rfl

lemma quotientPrimePoint_comap_eq_maxIdealAt [IsAlgClosed K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    [Module.Finite K (MvPolynomial (Fin (n + 1)) K ⧸ I)]
    (p : PrimeSpectrum (MvPolynomial (Fin (n + 1)) K ⧸ I)) :
    p.asIdeal.comap (Ideal.Quotient.mk I) =
      LeanEval.AlgebraicGeometry.maxIdealAt (quotientPrimePoint I p) := by
  rw [maxIdealAt_eq_vanishingIdeal]
  exact quotientPrimePoint_spec I p

lemma quotientPrimePoint_submonoid_eq [IsAlgClosed K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    [Module.Finite K (MvPolynomial (Fin (n + 1)) K ⧸ I)]
    (p : PrimeSpectrum (MvPolynomial (Fin (n + 1)) K ⧸ I)) :
    Algebra.algebraMapSubmonoid (MvPolynomial (Fin (n + 1)) K ⧸ I)
        (LeanEval.AlgebraicGeometry.maxIdealAt
          (quotientPrimePoint I p)).primeCompl =
      p.asIdeal.primeCompl := by
  have hpc :
      (LeanEval.AlgebraicGeometry.maxIdealAt
          (quotientPrimePoint I p)).primeCompl =
        (p.asIdeal.comap (Ideal.Quotient.mk I)).primeCompl := by
    ext x
    simp only [Ideal.mem_primeCompl_iff]
    rw [quotientPrimePoint_comap_eq_maxIdealAt I p]
  rw [hpc]
  simpa only [Algebra.algebraMapSubmonoid,
    Ideal.Quotient.algebraMap_eq] using
      p.asIdeal.map_primeCompl_comap_of_surjective
        (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

set_option synthInstance.maxHeartbeats 100000 in
noncomputable def quotientPrimeLocalizationEquiv [IsAlgClosed K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    [Module.Finite K (MvPolynomial (Fin (n + 1)) K ⧸ I)]
    (p : PrimeSpectrum (MvPolynomial (Fin (n + 1)) K ⧸ I)) :
    Localization.AtPrime p.asIdeal ≃ₐ[K]
      (LeanEval.AlgebraicGeometry.localRingAt (quotientPrimePoint I p) ⧸
        I.map (algebraMap (MvPolynomial (Fin (n + 1)) K)
          (LeanEval.AlgebraicGeometry.localRingAt
            (quotientPrimePoint I p)))) := by
  let A := MvPolynomial (Fin (n + 1)) K ⧸ I
  let q := quotientPrimePoint I p
  let J : Ideal (LeanEval.AlgebraicGeometry.localRingAt q) :=
    I.map (algebraMap (MvPolynomial (Fin (n + 1)) K)
      (LeanEval.AlgebraicGeometry.localRingAt q))
  let B :=
    LeanEval.AlgebraicGeometry.localRingAt q ⧸ J
  have hsub :
      Algebra.algebraMapSubmonoid A
          (LeanEval.AlgebraicGeometry.maxIdealAt q).primeCompl =
        p.asIdeal.primeCompl :=
    quotientPrimePoint_submonoid_eq I p
  letI : Algebra A B := inferInstance
  letI : IsLocalization p.asIdeal.primeCompl B :=
    hsub ▸
      (inferInstance : IsLocalization
        (Algebra.algebraMapSubmonoid A
          (LeanEval.AlgebraicGeometry.maxIdealAt q).primeCompl) B)
  letI : IsScalarTower K A B := by
    constructor
    intro k x y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    change (k • (Ideal.Quotient.mkₐ K I) r) •
        Ideal.Quotient.mk J s =
      k • ((Ideal.Quotient.mkₐ K I) r • Ideal.Quotient.mk J s)
    rw [← map_smul (Ideal.Quotient.mkₐ K I) k r]
    change Ideal.Quotient.mk I (k • r) • Ideal.Quotient.mk J s =
      k • (Ideal.Quotient.mk I r • Ideal.Quotient.mk J s)
    rw [Ideal.Quotient.mk_smul_mk_quotient_map_quotient]
    rw [Ideal.Quotient.mk_smul_mk_quotient_map_quotient]
    change Ideal.Quotient.mk J
        (algebraMap _ _ (k • r) * s) =
      k • (Ideal.Quotient.mkₐ K J) (algebraMap _ _ r * s)
    rw [← map_smul (Ideal.Quotient.mkₐ K J)]
    apply congrArg
    simp only [Algebra.smul_def, map_mul, mul_assoc]
    rw [IsScalarTower.algebraMap_apply K
      (MvPolynomial (Fin (n + 1)) K)
      (LeanEval.AlgebraicGeometry.localRingAt q)]
  exact (IsLocalization.algEquiv p.asIdeal.primeCompl
    (Localization.AtPrime p.asIdeal) B).restrictScalars K

lemma length_quotientPrimeLocalization [IsAlgClosed K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    [Module.Finite K (MvPolynomial (Fin (n + 1)) K ⧸ I)]
    (p : PrimeSpectrum (MvPolynomial (Fin (n + 1)) K ⧸ I)) :
    Module.length K (Localization.AtPrime p.asIdeal) =
      Module.length K
        (LeanEval.AlgebraicGeometry.localRingAt (quotientPrimePoint I p) ⧸
          I.map (algebraMap (MvPolynomial (Fin (n + 1)) K)
            (LeanEval.AlgebraicGeometry.localRingAt
              (quotientPrimePoint I p)))) :=
  (quotientPrimeLocalizationEquiv I p).toLinearEquiv.length_eq

lemma length_polynomialQuotient_eq_finsum_zeroLocus_localizations
    [IsAlgClosed K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    [Module.Finite K (MvPolynomial (Fin (n + 1)) K ⧸ I)] :
    Module.length K (MvPolynomial (Fin (n + 1)) K ⧸ I) =
      ∑ᶠ q : MvPolynomial.zeroLocus K I,
        Module.length K
          (LeanEval.AlgebraicGeometry.localRingAt (q : Fin (n + 1) → K) ⧸
            I.map (algebraMap (MvPolynomial (Fin (n + 1)) K)
              (LeanEval.AlgebraicGeometry.localRingAt
                (q : Fin (n + 1) → K)))) := by
  rw [length_eq_sum_primeSpectrum_localizations]
  apply finsum_eq_of_bijective (quotientPrimeSpectrumEquivZeroLocus I)
    (quotientPrimeSpectrumEquivZeroLocus I).bijective
  intro p
  exact length_quotientPrimeLocalization I p

end Submission.Helpers
