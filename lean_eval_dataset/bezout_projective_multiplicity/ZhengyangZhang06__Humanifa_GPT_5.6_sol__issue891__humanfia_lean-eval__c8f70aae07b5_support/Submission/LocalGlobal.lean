import Submission.QuotientPoints

open LeanEval.AlgebraicGeometry
open scoped LinearAlgebra.Projectivization
open MvPolynomial

namespace Submission.Helpers

variable {K : Type*} [Field K]

lemma linearSliceCoord_ne_zero {n : ℕ}
    (a : Fin (n + 1) → K) (p : ProjSpace K n)
    (hne : eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    linearSliceCoord a p ≠ 0 :=
  ne_zero_of_eval_linearForm_eq_one a (linearSliceCoord a p)
    (eval_linearForm_linearSliceCoord a p hne)

lemma projectivization_mk_linearSliceCoord {n : ℕ}
    (a : Fin (n + 1) → K) (p : ProjSpace K n)
    (hne : eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    Projectivization.mk K (linearSliceCoord a p)
        (linearSliceCoord_ne_zero a p hne) = p := by
  calc
    Projectivization.mk K (linearSliceCoord a p)
        (linearSliceCoord_ne_zero a p hne) =
        Projectivization.mk K (Projectivization.rep p)
          (Projectivization.rep_nonzero p) := by
      apply (Projectivization.mk_eq_mk_iff' K _ _
        (linearSliceCoord_ne_zero a p hne)
        (Projectivization.rep_nonzero p)).mpr
      refine ⟨(eval (Projectivization.rep p) (linearForm a))⁻¹, ?_⟩
      funext i
      simp only [linearSliceCoord, Pi.smul_apply, smul_eq_mul,
        div_eq_mul_inv]
      rw [mul_comm]
    _ = p := Projectivization.mk_rep p

lemma linearSliceCoord_injective_on {n : ℕ}
    (a : Fin (n + 1) → K) (S : Set (ProjSpace K n))
    (hne : ∀ p ∈ S,
      eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    Set.InjOn (linearSliceCoord a) S := by
  intro p hp p' hp' h
  rw [← projectivization_mk_linearSliceCoord a p (hne p hp),
    ← projectivization_mk_linearSliceCoord a p' (hne p' hp')]
  apply (Projectivization.mk_eq_mk_iff' K _ _
    (linearSliceCoord_ne_zero a p (hne p hp))
    (linearSliceCoord_ne_zero a p' (hne p' hp'))).mpr
  exact ⟨1, by simpa using h.symm⟩

noncomputable def projectiveZeroEquivLinearSliceZero [IsAlgClosed K] {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (a : Fin (n + 1) → K)
    (hne : ∀ p ∈ ⋂ k, vanishingSet (f k),
      eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    (⋂ k, vanishingSet (f k)) ≃
      MvPolynomial.zeroLocus K (linearSlicePolynomialIdeal f a) :=
  Equiv.ofBijective
    (fun p => ⟨linearSliceCoord a p,
      linearSliceCoord_mem_zeroLocus f d hd a p p.property
        (hne p p.property)⟩)
    ⟨fun p p' h => Subtype.ext <|
        linearSliceCoord_injective_on a (⋂ k, vanishingSet (f k))
          hne p.property p'.property (congrArg Subtype.val h),
      fun q => by
        have hq :
            (q : Fin (n + 1) → K) ∈
              linearSliceCoord a '' (⋂ k, vanishingSet (f k)) := by
          rw [← zeroLocus_linearSlicePolynomialIdeal_eq_image f d hd a hne]
          exact q.property
        obtain ⟨p, hp, heq⟩ := hq
        exact ⟨⟨p, hp⟩, Subtype.ext heq⟩⟩

@[simp]
lemma projectiveZeroEquivLinearSliceZero_apply [IsAlgClosed K] {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (a : Fin (n + 1) → K)
    (hne : ∀ p ∈ ⋂ k, vanishingSet (f k),
      eval (Projectivization.rep p) (linearForm a) ≠ 0)
    (p : ⋂ k, vanishingSet (f k)) :
    (projectiveZeroEquivLinearSliceZero f d hd a hne p :
        Fin (n + 1) → K) =
      linearSliceCoord a p :=
  rfl

lemma linearSlice_local_length_eq_intersectionMultiplicity {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (a : Fin (n + 1) → K)
    (p : ⋂ k, vanishingSet (f k))
    (hne : ∀ p ∈ ⋂ k, vanishingSet (f k),
      eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    Module.length K
        (localRingAt (linearSliceCoord a p) ⧸
          (linearSlicePolynomialIdeal f a).map
            (algebraMap (MvPolynomial (Fin (n + 1)) K)
              (localRingAt (linearSliceCoord a p)))) =
      intersectionMultiplicity f p := by
  rw [← linearSliceIdeal_eq_map f a p]
  exact (intersectionMultiplicity_eq_linearSlice_length
    f d hd a p p.property (hne p p.property)).symm

lemma length_linearSlicePolynomialQuotient_eq_intersectionMultiplicity_sum
    [IsAlgClosed K] {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (a : Fin (n + 1) → K)
    (hfin : (⋂ k, vanishingSet (f k)).Finite)
    (hne : ∀ p ∈ ⋂ k, vanishingSet (f k),
      eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    Module.length K
        (MvPolynomial (Fin (n + 1)) K ⧸ linearSlicePolynomialIdeal f a) =
      ∑ᶠ p ∈ (⋂ k, vanishingSet (f k)),
        intersectionMultiplicity f p := by
  letI : Module.Finite K
      (MvPolynomial (Fin (n + 1)) K ⧸ linearSlicePolynomialIdeal f a) :=
    linearSlicePolynomialQuotient_module_finite f d hd a hfin hne
  rw [length_polynomialQuotient_eq_finsum_zeroLocus_localizations]
  rw [← finsum_set_coe_eq_finsum_mem]
  symm
  apply finsum_eq_of_bijective
    (projectiveZeroEquivLinearSliceZero f d hd a hne)
    (projectiveZeroEquivLinearSliceZero f d hd a hne).bijective
  intro p
  exact (linearSlice_local_length_eq_intersectionMultiplicity
    f d hd a p hne).symm

end Submission.Helpers
