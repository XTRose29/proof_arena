import Submission.LocalSlice

open LeanEval.AlgebraicGeometry
open scoped LinearAlgebra.Projectivization
open MvPolynomial

namespace Submission.Helpers

variable {K : Type*} [Field K]

noncomputable def linearSlicePolynomialIdeal {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K)
    (a : Fin (n + 1) → K) :
    Ideal (MvPolynomial (Fin (n + 1)) K) :=
  Ideal.span (Set.range f ∪ {linearForm a - C 1})

lemma linearSliceIdeal_eq_map {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K)
    (a : Fin (n + 1) → K) (p : ProjSpace K n) :
    linearSliceIdeal f a p =
      (linearSlicePolynomialIdeal f a).map
        (algebraMap (MvPolynomial (Fin (n + 1)) K)
          (localRingAt (linearSliceCoord a p))) := by
  rw [linearSliceIdeal, linearSlicePolynomialIdeal, Ideal.map_span]
  congr 1
  ext x
  simp [eq_comm]

lemma mem_zeroLocus_linearSlicePolynomialIdeal {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K)
    (a q : Fin (n + 1) → K) :
    q ∈ MvPolynomial.zeroLocus K (linearSlicePolynomialIdeal f a) ↔
      (∀ k, eval q (f k) = 0) ∧ eval q (linearForm a) = 1 := by
  rw [linearSlicePolynomialIdeal, MvPolynomial.zeroLocus_span]
  simp [sub_eq_zero, and_comm]

lemma linearSliceCoord_mem_zeroLocus {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (a : Fin (n + 1) → K) (p : ProjSpace K n)
    (hp : p ∈ ⋂ k, vanishingSet (f k))
    (hne : eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    linearSliceCoord a p ∈
      MvPolynomial.zeroLocus K (linearSlicePolynomialIdeal f a) := by
  rw [mem_zeroLocus_linearSlicePolynomialIdeal]
  refine ⟨fun k => ?_, eval_linearForm_linearSliceCoord a p hne⟩
  exact eval_linearSliceCoord_eq_zero a p (hd k) (Set.mem_iInter.mp hp k)

lemma ne_zero_of_eval_linearForm_eq_one {n : ℕ}
    (a q : Fin (n + 1) → K) (h : eval q (linearForm a) = 1) :
    q ≠ 0 := by
  intro hq
  subst q
  simp [linearForm] at h

lemma projectivization_mk_mem_vanishingSet_iInter {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (q : Fin (n + 1) → K) (hq : q ≠ 0)
    (hzero : ∀ k, eval q (f k) = 0) :
    Projectivization.mk K q hq ∈ ⋂ k, vanishingSet (f k) := by
  rw [Set.mem_iInter]
  intro k
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep K q hq
  change eval (Projectivization.rep (Projectivization.mk K q hq)) (f k) = 0
  rw [← hu]
  change eval ((u : K) • q) (f k) = 0
  rw [eval_smul_of_isHomogeneous (hd k), hzero k, mul_zero]

lemma linearSliceCoord_projectivization_mk {n : ℕ}
    (a q : Fin (n + 1) → K) (hq : q ≠ 0)
    (hlinear : eval q (linearForm a) = 1) :
    linearSliceCoord a (Projectivization.mk K q hq) = q := by
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep K q hq
  funext i
  change Projectivization.rep (Projectivization.mk K q hq) i /
      eval (Projectivization.rep (Projectivization.mk K q hq))
        (linearForm a) = q i
  rw [← hu]
  change ((u : K) * q i) / eval ((u : K) • q) (linearForm a) = q i
  rw [eval_smul_of_isHomogeneous (linearForm_isHomogeneous a), hlinear]
  field_simp [Units.ne_zero u]

lemma zeroLocus_linearSlicePolynomialIdeal_eq_image {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (a : Fin (n + 1) → K)
    (hne : ∀ p ∈ ⋂ k, vanishingSet (f k),
      eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    MvPolynomial.zeroLocus K (linearSlicePolynomialIdeal f a) =
      linearSliceCoord a '' (⋂ k, vanishingSet (f k)) := by
  ext q
  constructor
  · intro hq
    obtain ⟨hzero, hlinear⟩ :=
      (mem_zeroLocus_linearSlicePolynomialIdeal f a q).mp hq
    have hq0 := ne_zero_of_eval_linearForm_eq_one a q hlinear
    let p := Projectivization.mk K q hq0
    have hp : p ∈ ⋂ k, vanishingSet (f k) :=
      projectivization_mk_mem_vanishingSet_iInter f d hd q hq0 hzero
    exact ⟨p, hp, linearSliceCoord_projectivization_mk a q hq0 hlinear⟩
  · rintro ⟨p, hp, rfl⟩
    exact linearSliceCoord_mem_zeroLocus f d hd a p hp (hne p hp)

lemma zeroLocus_linearSlicePolynomialIdeal_finite {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (a : Fin (n + 1) → K)
    (hfin : (⋂ k, vanishingSet (f k)).Finite)
    (hne : ∀ p ∈ ⋂ k, vanishingSet (f k),
      eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    (MvPolynomial.zeroLocus K (linearSlicePolynomialIdeal f a)).Finite := by
  rw [zeroLocus_linearSlicePolynomialIdeal_eq_image f d hd a hne]
  exact hfin.image _

noncomputable def finiteZeroCoordinatePolynomial {n : ℕ}
    (V : Set (Fin (n + 1) → K)) (hV : V.Finite) (i : Fin (n + 1)) :
    Polynomial K :=
  ∏ q ∈ hV.toFinset, (Polynomial.X - Polynomial.C (q i))

noncomputable def finiteZeroCoordinateMvPolynomial {n : ℕ}
    (V : Set (Fin (n + 1) → K)) (hV : V.Finite) (i : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) K :=
  ∏ q ∈ hV.toFinset, (X i - C (q i))

lemma finiteZeroCoordinatePolynomial_monic {n : ℕ}
    (V : Set (Fin (n + 1) → K)) (hV : V.Finite) (i : Fin (n + 1)) :
    (finiteZeroCoordinatePolynomial V hV i).Monic := by
  unfold finiteZeroCoordinatePolynomial
  apply Polynomial.monic_prod_of_monic
  intro q _hq
  exact Polynomial.monic_X_sub_C (q i)

lemma eval_finiteZeroCoordinateMvPolynomial {n : ℕ}
    (V : Set (Fin (n + 1) → K)) (hV : V.Finite) (i : Fin (n + 1))
    (q : Fin (n + 1) → K) (hq : q ∈ V) :
    eval q (finiteZeroCoordinateMvPolynomial V hV i) = 0 := by
  rw [finiteZeroCoordinateMvPolynomial, map_prod]
  simp only [map_sub, eval_X, eval_C]
  refine Finset.prod_eq_zero (hV.mem_toFinset.mpr hq) ?_
  exact sub_self (q i)

lemma quotient_X_isIntegral_of_zeroLocus_finite [IsAlgClosed K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hV : (MvPolynomial.zeroLocus K I).Finite) (i : Fin (n + 1)) :
    IsIntegral K
      (Ideal.Quotient.mk I (X i) :
        MvPolynomial (Fin (n + 1)) K ⧸ I) := by
  let V := MvPolynomial.zeroLocus K I
  let P := finiteZeroCoordinatePolynomial V hV i
  let G := finiteZeroCoordinateMvPolynomial V hV i
  have hGvan : G ∈ MvPolynomial.vanishingIdeal K V := by
    intro q hq
    exact eval_finiteZeroCoordinateMvPolynomial V hV i q hq
  have hGrad : G ∈ I.radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K) I]
    exact hGvan
  obtain ⟨N, hGN⟩ := hGrad
  refine ⟨P ^ N, (finiteZeroCoordinatePolynomial_monic V hV i).pow N, ?_⟩
  have hC (r : K) :
      algebraMap K (MvPolynomial (Fin (n + 1)) K ⧸ I) r =
        Ideal.Quotient.mk I (C r) := by
    change algebraMap K (MvPolynomial (Fin (n + 1)) K ⧸ I) r =
      algebraMap (MvPolynomial (Fin (n + 1)) K)
        (MvPolynomial (Fin (n + 1)) K ⧸ I) (C r)
    simpa only [← algebraMap_eq] using
      IsScalarTower.algebraMap_apply K
        (MvPolynomial (Fin (n + 1)) K)
        (MvPolynomial (Fin (n + 1)) K ⧸ I) r
  have heval :
      Polynomial.eval₂
          (algebraMap K (MvPolynomial (Fin (n + 1)) K ⧸ I))
          (Ideal.Quotient.mk I (X i)) P =
        Ideal.Quotient.mk I G := by
    change Polynomial.eval₂
        (algebraMap K (MvPolynomial (Fin (n + 1)) K ⧸ I))
        (Ideal.Quotient.mk I (X i))
        (∏ q ∈ hV.toFinset, (Polynomial.X - Polynomial.C (q i))) =
      Ideal.Quotient.mk I
        (∏ q ∈ hV.toFinset, (X i - C (q i)))
    rw [Polynomial.eval₂_finsetProd, map_prod]
    apply Finset.prod_congr rfl
    intro q _hq
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C,
      map_sub, hC]
  rw [Polynomial.eval₂_pow, heval, ← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hGN

lemma quotient_mk_C_eq_algebraMap {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) (r : K) :
    Ideal.Quotient.mk I (C r) =
      algebraMap K (MvPolynomial (Fin (n + 1)) K ⧸ I) r := by
  change algebraMap (MvPolynomial (Fin (n + 1)) K)
      (MvPolynomial (Fin (n + 1)) K ⧸ I) (C r) =
    algebraMap K (MvPolynomial (Fin (n + 1)) K ⧸ I) r
  simpa only [← algebraMap_eq] using
    (IsScalarTower.algebraMap_apply K
      (MvPolynomial (Fin (n + 1)) K)
      (MvPolynomial (Fin (n + 1)) K ⧸ I) r).symm

lemma quotient_isIntegral_of_zeroLocus_finite [IsAlgClosed K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hV : (MvPolynomial.zeroLocus K I).Finite) :
    Algebra.IsIntegral K (MvPolynomial (Fin (n + 1)) K ⧸ I) := by
  constructor
  intro z
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective z
  induction g using MvPolynomial.induction_on with
  | C r =>
      rw [quotient_mk_C_eq_algebraMap]
      exact isIntegral_algebraMap
  | add p q hp hq =>
      simpa only [map_add] using hp.add hq
  | mul_X p i hp =>
      simpa only [map_mul] using
        hp.mul (quotient_X_isIntegral_of_zeroLocus_finite I hV i)

lemma quotient_module_finite_of_zeroLocus_finite [IsAlgClosed K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hV : (MvPolynomial.zeroLocus K I).Finite) :
    Module.Finite K (MvPolynomial (Fin (n + 1)) K ⧸ I) := by
  letI : Algebra.IsIntegral K (MvPolynomial (Fin (n + 1)) K ⧸ I) :=
    quotient_isIntegral_of_zeroLocus_finite I hV
  exact Algebra.IsIntegral.finite

lemma linearSlicePolynomialQuotient_module_finite [IsAlgClosed K] {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (a : Fin (n + 1) → K)
    (hfin : (⋂ k, vanishingSet (f k)).Finite)
    (hne : ∀ p ∈ ⋂ k, vanishingSet (f k),
      eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    Module.Finite K
      (MvPolynomial (Fin (n + 1)) K ⧸ linearSlicePolynomialIdeal f a) :=
  quotient_module_finite_of_zeroLocus_finite
    (linearSlicePolynomialIdeal f a)
    (zeroLocus_linearSlicePolynomialIdeal_finite f d hd a hfin hne)

end Submission.Helpers
