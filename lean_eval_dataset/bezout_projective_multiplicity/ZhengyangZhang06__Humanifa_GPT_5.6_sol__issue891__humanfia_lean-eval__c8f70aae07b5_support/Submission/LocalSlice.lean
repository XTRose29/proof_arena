import Submission.Slice

open LeanEval.AlgebraicGeometry
open scoped LinearAlgebra.Projectivization
open MvPolynomial

namespace Submission.Helpers

variable {K : Type*} [Field K]

@[simp]
lemma localNormalizeHom_algebraMap {n : ℕ}
    (q q' : Fin (n + 1) → K) (I : Ideal (localRingAt q))
    (hI : I ≤ RingHom.ker (localEvalAt q))
    (g : MvPolynomial (Fin (n + 1)) K) (hg : eval q g ≠ 0)
    (hcenter : q' = fun i => q i / eval q g)
    (x : MvPolynomial (Fin (n + 1)) K) :
    localNormalizeHom q q' I hI g hg hcenter
        (algebraMap _ (localRingAt q') x) =
      normalizeHom q I g hg x := by
  unfold localNormalizeHom
  rw [IsLocalization.lift_eq]

noncomputable def chartToLinearSliceHom {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (a : Fin (n + 1) → K) (p : ProjSpace K n)
    (hp : p ∈ ⋂ k, vanishingSet (f k))
    (hne : eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    localRingAt (linearSliceCoord a p) →+*
      localRingAt (affineConeCoord p) ⧸ localIntersectionIdeal f p :=
  localNormalizeHom (affineConeCoord p) (linearSliceCoord a p)
    (localIntersectionIdeal f p)
    (localIntersectionIdeal_le_ker f d hd p hp)
    (linearForm a)
    (eval_affineConeCoord_linearForm_ne_zero a p hne)
    (linearSliceCoord_eq_normalize_affineConeCoord a p hne)

@[simp]
lemma chartToLinearSliceHom_algebraMap {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (a : Fin (n + 1) → K) (p : ProjSpace K n)
    (hp : p ∈ ⋂ k, vanishingSet (f k))
    (hne : eval (Projectivization.rep p) (linearForm a) ≠ 0)
    (x : MvPolynomial (Fin (n + 1)) K) :
    chartToLinearSliceHom f d hd a p hp hne
        (algebraMap _ (localRingAt (linearSliceCoord a p)) x) =
      normalizeHom (affineConeCoord p) (localIntersectionIdeal f p)
        (linearForm a)
        (eval_affineConeCoord_linearForm_ne_zero a p hne) x :=
  localNormalizeHom_algebraMap _ _ _ _ _ _ _ x

lemma linearSliceIdeal_le_ker_chartToLinearSliceHom {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (a : Fin (n + 1) → K) (p : ProjSpace K n)
    (hp : p ∈ ⋂ k, vanishingSet (f k))
    (hne : eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    linearSliceIdeal f a p ≤
      RingHom.ker (chartToLinearSliceHom f d hd a p hp hne) := by
  rw [linearSliceIdeal, Ideal.span_le]
  rintro x (⟨k, rfl⟩ | rfl)
  · change chartToLinearSliceHom f d hd a p hp hne
        (algebraMap _ (localRingAt (linearSliceCoord a p)) (f k)) = 0
    rw [chartToLinearSliceHom_algebraMap,
      normalizeHom_of_isHomogeneous _ _ _ _ _ (hd k)]
    have hmem :
        algebraMap (MvPolynomial (Fin (n + 1)) K)
            (localRingAt (affineConeCoord p)) (f k) ∈
          localIntersectionIdeal f p :=
      Ideal.subset_span (Or.inl ⟨k, rfl⟩)
    have hzero :
        quotientPolynomialMap (affineConeCoord p)
            (localIntersectionIdeal f p) (f k) = 0 := by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [hzero, mul_zero]
  · change chartToLinearSliceHom f d hd a p hp hne
        (algebraMap _ (localRingAt (linearSliceCoord a p))
          (linearForm a - C 1)) = 0
    rw [chartToLinearSliceHom_algebraMap, map_sub,
      normalizeHom_degree_one _ _ _
        (eval_affineConeCoord_linearForm_ne_zero a p hne)
        (linearForm_isHomogeneous a)]
    simp

noncomputable def linearSliceQuotientToChartQuotient {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (a : Fin (n + 1) → K) (p : ProjSpace K n)
    (hp : p ∈ ⋂ k, vanishingSet (f k))
    (hne : eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    (localRingAt (linearSliceCoord a p) ⧸ linearSliceIdeal f a p) →+*
      localRingAt (affineConeCoord p) ⧸ localIntersectionIdeal f p :=
  Ideal.Quotient.lift (linearSliceIdeal f a p)
    (chartToLinearSliceHom f d hd a p hp hne)
    fun _x hx =>
      RingHom.mem_ker.mp
        (linearSliceIdeal_le_ker_chartToLinearSliceHom f d hd a p hp hne hx)

lemma eval_linearSliceCoord_X_chartIndex_ne_zero {n : ℕ}
    (a : Fin (n + 1) → K) (p : ProjSpace K n)
    (hne : eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    eval (linearSliceCoord a p) (X (chartIndex p)) ≠ 0 := by
  rw [eval_X]
  exact div_ne_zero (chartIndex_rep_ne_zero p) hne

lemma affineConeCoord_eq_normalize_linearSliceCoord {n : ℕ}
    (a : Fin (n + 1) → K) (p : ProjSpace K n)
    (hne : eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    affineConeCoord p = fun i =>
      linearSliceCoord a p i /
        eval (linearSliceCoord a p) (X (chartIndex p)) := by
  funext i
  simp only [affineConeCoord, linearSliceCoord, eval_X]
  field_simp [chartIndex_rep_ne_zero p, hne]

noncomputable def linearSliceToChartHom {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (a : Fin (n + 1) → K) (p : ProjSpace K n)
    (hp : p ∈ ⋂ k, vanishingSet (f k))
    (hne : eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    localRingAt (affineConeCoord p) →+*
      localRingAt (linearSliceCoord a p) ⧸ linearSliceIdeal f a p :=
  localNormalizeHom (linearSliceCoord a p) (affineConeCoord p)
    (linearSliceIdeal f a p)
    (linearSliceIdeal_le_ker f d hd a p hp hne)
    (X (chartIndex p))
    (eval_linearSliceCoord_X_chartIndex_ne_zero a p hne)
    (affineConeCoord_eq_normalize_linearSliceCoord a p hne)

@[simp]
lemma linearSliceToChartHom_algebraMap {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (a : Fin (n + 1) → K) (p : ProjSpace K n)
    (hp : p ∈ ⋂ k, vanishingSet (f k))
    (hne : eval (Projectivization.rep p) (linearForm a) ≠ 0)
    (x : MvPolynomial (Fin (n + 1)) K) :
    linearSliceToChartHom f d hd a p hp hne
        (algebraMap _ (localRingAt (affineConeCoord p)) x) =
      normalizeHom (linearSliceCoord a p) (linearSliceIdeal f a p)
        (X (chartIndex p))
        (eval_linearSliceCoord_X_chartIndex_ne_zero a p hne) x :=
  localNormalizeHom_algebraMap _ _ _ _ _ _ _ x

lemma localIntersectionIdeal_le_ker_linearSliceToChartHom {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (a : Fin (n + 1) → K) (p : ProjSpace K n)
    (hp : p ∈ ⋂ k, vanishingSet (f k))
    (hne : eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    localIntersectionIdeal f p ≤
      RingHom.ker (linearSliceToChartHom f d hd a p hp hne) := by
  rw [localIntersectionIdeal, Ideal.span_le]
  rintro x (⟨k, rfl⟩ | rfl)
  · change linearSliceToChartHom f d hd a p hp hne
        (algebraMap _ (localRingAt (affineConeCoord p)) (f k)) = 0
    rw [linearSliceToChartHom_algebraMap,
      normalizeHom_of_isHomogeneous _ _ _ _ _ (hd k)]
    have hmem :
        algebraMap (MvPolynomial (Fin (n + 1)) K)
            (localRingAt (linearSliceCoord a p)) (f k) ∈
          linearSliceIdeal f a p :=
      Ideal.subset_span (Or.inl ⟨k, rfl⟩)
    have hzero :
        quotientPolynomialMap (linearSliceCoord a p)
            (linearSliceIdeal f a p) (f k) = 0 := by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [hzero, mul_zero]
  · change linearSliceToChartHom f d hd a p hp hne
        (algebraMap _ (localRingAt (affineConeCoord p))
          (X (chartIndex p) - C 1)) = 0
    rw [linearSliceToChartHom_algebraMap, map_sub,
      normalizeHom_degree_one _ _ _
        (eval_linearSliceCoord_X_chartIndex_ne_zero a p hne)
        (isHomogeneous_X K (chartIndex p))]
    simp

noncomputable def chartQuotientToLinearSliceQuotient {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (a : Fin (n + 1) → K) (p : ProjSpace K n)
    (hp : p ∈ ⋂ k, vanishingSet (f k))
    (hne : eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    (localRingAt (affineConeCoord p) ⧸ localIntersectionIdeal f p) →+*
      localRingAt (linearSliceCoord a p) ⧸ linearSliceIdeal f a p :=
  Ideal.Quotient.lift (localIntersectionIdeal f p)
    (linearSliceToChartHom f d hd a p hp hne)
    fun _x hx =>
      RingHom.mem_ker.mp
        (localIntersectionIdeal_le_ker_linearSliceToChartHom
          f d hd a p hp hne hx)

@[simp]
lemma linearSliceQuotientToChartQuotient_quotientPolynomialMap {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (a : Fin (n + 1) → K) (p : ProjSpace K n)
    (hp : p ∈ ⋂ k, vanishingSet (f k))
    (hne : eval (Projectivization.rep p) (linearForm a) ≠ 0)
    (x : MvPolynomial (Fin (n + 1)) K) :
    linearSliceQuotientToChartQuotient f d hd a p hp hne
        (quotientPolynomialMap (linearSliceCoord a p)
          (linearSliceIdeal f a p) x) =
      normalizeHom (affineConeCoord p) (localIntersectionIdeal f p)
        (linearForm a)
        (eval_affineConeCoord_linearForm_ne_zero a p hne) x := by
  rw [quotientPolynomialMap, RingHom.comp_apply,
    linearSliceQuotientToChartQuotient, Ideal.Quotient.lift_mk,
    chartToLinearSliceHom_algebraMap]

@[simp]
lemma chartQuotientToLinearSliceQuotient_quotientPolynomialMap {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (a : Fin (n + 1) → K) (p : ProjSpace K n)
    (hp : p ∈ ⋂ k, vanishingSet (f k))
    (hne : eval (Projectivization.rep p) (linearForm a) ≠ 0)
    (x : MvPolynomial (Fin (n + 1)) K) :
    chartQuotientToLinearSliceQuotient f d hd a p hp hne
        (quotientPolynomialMap (affineConeCoord p)
          (localIntersectionIdeal f p) x) =
      normalizeHom (linearSliceCoord a p) (linearSliceIdeal f a p)
        (X (chartIndex p))
        (eval_linearSliceCoord_X_chartIndex_ne_zero a p hne) x := by
  rw [quotientPolynomialMap, RingHom.comp_apply,
    chartQuotientToLinearSliceQuotient, Ideal.Quotient.lift_mk,
    linearSliceToChartHom_algebraMap]

lemma quotientPolynomialMap_linearForm_eq_one {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K)
    (a : Fin (n + 1) → K) (p : ProjSpace K n) :
    quotientPolynomialMap (linearSliceCoord a p) (linearSliceIdeal f a p)
        (linearForm a) = 1 := by
  have hmem :
      algebraMap (MvPolynomial (Fin (n + 1)) K)
          (localRingAt (linearSliceCoord a p)) (linearForm a - C 1) ∈
        linearSliceIdeal f a p :=
    Ideal.subset_span (Or.inr rfl)
  have hzero :
      quotientPolynomialMap (linearSliceCoord a p) (linearSliceIdeal f a p)
          (linearForm a - C 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  exact sub_eq_zero.mp (by simpa using hzero)

lemma quotientPolynomialMap_X_chartIndex_eq_one {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K)
    (p : ProjSpace K n) :
    quotientPolynomialMap (affineConeCoord p) (localIntersectionIdeal f p)
        (X (chartIndex p)) = 1 := by
  have hmem :
      algebraMap (MvPolynomial (Fin (n + 1)) K)
          (localRingAt (affineConeCoord p)) (X (chartIndex p) - C 1) ∈
        localIntersectionIdeal f p :=
    Ideal.subset_span (Or.inr rfl)
  have hzero :
      quotientPolynomialMap (affineConeCoord p) (localIntersectionIdeal f p)
          (X (chartIndex p) - C 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  exact sub_eq_zero.mp (by simpa using hzero)

lemma chartQuotientToLinearSliceQuotient_normalizationUnit {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (a : Fin (n + 1) → K) (p : ProjSpace K n)
    (hp : p ∈ ⋂ k, vanishingSet (f k))
    (hne : eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    chartQuotientToLinearSliceQuotient f d hd a p hp hne
        (normalizationUnit (affineConeCoord p) (localIntersectionIdeal f p)
          (linearForm a)
          (eval_affineConeCoord_linearForm_ne_zero a p hne)) =
      (↑(normalizationUnit (linearSliceCoord a p) (linearSliceIdeal f a p)
        (X (chartIndex p))
        (eval_linearSliceCoord_X_chartIndex_ne_zero a p hne))⁻¹ :
          localRingAt (linearSliceCoord a p) ⧸ linearSliceIdeal f a p) := by
  rw [normalizationUnit_spec,
    chartQuotientToLinearSliceQuotient_quotientPolynomialMap,
    normalizeHom_of_isHomogeneous _ _ _ _ _
      (linearForm_isHomogeneous a),
    quotientPolynomialMap_linearForm_eq_one, pow_one, mul_one]

lemma linearSliceQuotientToChartQuotient_normalizationUnit {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (a : Fin (n + 1) → K) (p : ProjSpace K n)
    (hp : p ∈ ⋂ k, vanishingSet (f k))
    (hne : eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    linearSliceQuotientToChartQuotient f d hd a p hp hne
        (normalizationUnit (linearSliceCoord a p) (linearSliceIdeal f a p)
          (X (chartIndex p))
          (eval_linearSliceCoord_X_chartIndex_ne_zero a p hne)) =
      (↑(normalizationUnit (affineConeCoord p) (localIntersectionIdeal f p)
        (linearForm a)
        (eval_affineConeCoord_linearForm_ne_zero a p hne))⁻¹ :
          localRingAt (affineConeCoord p) ⧸ localIntersectionIdeal f p) := by
  rw [normalizationUnit_spec,
    linearSliceQuotientToChartQuotient_quotientPolynomialMap,
    normalizeHom_of_isHomogeneous _ _ _ _ _
      (isHomogeneous_X K (chartIndex p)),
    quotientPolynomialMap_X_chartIndex_eq_one, pow_one, mul_one]

lemma chartQuotientToLinearSliceQuotient_normalizationUnit_inv {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (a : Fin (n + 1) → K) (p : ProjSpace K n)
    (hp : p ∈ ⋂ k, vanishingSet (f k))
    (hne : eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    chartQuotientToLinearSliceQuotient f d hd a p hp hne
        (↑(normalizationUnit (affineConeCoord p) (localIntersectionIdeal f p)
          (linearForm a)
          (eval_affineConeCoord_linearForm_ne_zero a p hne))⁻¹ :
            localRingAt (affineConeCoord p) ⧸ localIntersectionIdeal f p) =
      normalizationUnit (linearSliceCoord a p) (linearSliceIdeal f a p)
        (X (chartIndex p))
        (eval_linearSliceCoord_X_chartIndex_ne_zero a p hne) := by
  let G :
      (localRingAt (affineConeCoord p) ⧸ localIntersectionIdeal f p) →+*
        (localRingAt (linearSliceCoord a p) ⧸ linearSliceIdeal f a p) :=
    chartQuotientToLinearSliceQuotient f d hd a p hp hne
  let u :
      (localRingAt (affineConeCoord p) ⧸ localIntersectionIdeal f p)ˣ :=
    normalizationUnit (affineConeCoord p) (localIntersectionIdeal f p)
    (linearForm a) (eval_affineConeCoord_linearForm_ne_zero a p hne)
  let v :
      (localRingAt (linearSliceCoord a p) ⧸ linearSliceIdeal f a p)ˣ :=
    normalizationUnit (linearSliceCoord a p) (linearSliceIdeal f a p)
      (X (chartIndex p)) (eval_linearSliceCoord_X_chartIndex_ne_zero a p hne)
  have huv : G u = (↑v⁻¹ :
      localRingAt (linearSliceCoord a p) ⧸ linearSliceIdeal f a p) := by
    simpa [G, u, v] using
      chartQuotientToLinearSliceQuotient_normalizationUnit
        f d hd a p hp hne
  have huv' : Units.map G.toMonoidHom u = v⁻¹ := by
    ext
    exact huv
  change G (↑u⁻¹ :
      localRingAt (affineConeCoord p) ⧸ localIntersectionIdeal f p) =
    (↑v : localRingAt (linearSliceCoord a p) ⧸ linearSliceIdeal f a p)
  calc
    _ = (↑(Units.map G.toMonoidHom (u⁻¹)) :
        localRingAt (linearSliceCoord a p) ⧸ linearSliceIdeal f a p) := rfl
    _ = (↑((Units.map G.toMonoidHom u)⁻¹) :
        localRingAt (linearSliceCoord a p) ⧸ linearSliceIdeal f a p) := by
      rw [map_inv]
    _ = _ := by rw [huv', inv_inv]

lemma linearSliceQuotientToChartQuotient_normalizationUnit_inv {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (a : Fin (n + 1) → K) (p : ProjSpace K n)
    (hp : p ∈ ⋂ k, vanishingSet (f k))
    (hne : eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    linearSliceQuotientToChartQuotient f d hd a p hp hne
        (↑(normalizationUnit (linearSliceCoord a p) (linearSliceIdeal f a p)
          (X (chartIndex p))
          (eval_linearSliceCoord_X_chartIndex_ne_zero a p hne))⁻¹ :
            localRingAt (linearSliceCoord a p) ⧸ linearSliceIdeal f a p) =
      normalizationUnit (affineConeCoord p) (localIntersectionIdeal f p)
        (linearForm a)
        (eval_affineConeCoord_linearForm_ne_zero a p hne) := by
  let F :
      (localRingAt (linearSliceCoord a p) ⧸ linearSliceIdeal f a p) →+*
        (localRingAt (affineConeCoord p) ⧸ localIntersectionIdeal f p) :=
    linearSliceQuotientToChartQuotient f d hd a p hp hne
  let u :
      (localRingAt (linearSliceCoord a p) ⧸ linearSliceIdeal f a p)ˣ :=
    normalizationUnit (linearSliceCoord a p) (linearSliceIdeal f a p)
      (X (chartIndex p)) (eval_linearSliceCoord_X_chartIndex_ne_zero a p hne)
  let v :
      (localRingAt (affineConeCoord p) ⧸ localIntersectionIdeal f p)ˣ :=
    normalizationUnit (affineConeCoord p) (localIntersectionIdeal f p)
    (linearForm a) (eval_affineConeCoord_linearForm_ne_zero a p hne)
  have huv : F u = (↑v⁻¹ :
      localRingAt (affineConeCoord p) ⧸ localIntersectionIdeal f p) := by
    simpa [F, u, v] using
      linearSliceQuotientToChartQuotient_normalizationUnit
        f d hd a p hp hne
  have huv' : Units.map F.toMonoidHom u = v⁻¹ := by
    ext
    exact huv
  change F (↑u⁻¹ :
      localRingAt (linearSliceCoord a p) ⧸ linearSliceIdeal f a p) =
    (↑v : localRingAt (affineConeCoord p) ⧸ localIntersectionIdeal f p)
  calc
    _ = (↑(Units.map F.toMonoidHom (u⁻¹)) :
        localRingAt (affineConeCoord p) ⧸ localIntersectionIdeal f p) := rfl
    _ = (↑((Units.map F.toMonoidHom u)⁻¹) :
        localRingAt (affineConeCoord p) ⧸ localIntersectionIdeal f p) := by
      rw [map_inv]
    _ = _ := by rw [huv', inv_inv]

lemma chartQuotientToLinearSliceQuotient_comp
    {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (a : Fin (n + 1) → K) (p : ProjSpace K n)
    (hp : p ∈ ⋂ k, vanishingSet (f k))
    (hne : eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    (chartQuotientToLinearSliceQuotient f d hd a p hp hne).comp
        (linearSliceQuotientToChartQuotient f d hd a p hp hne) =
      RingHom.id
        (localRingAt (linearSliceCoord a p) ⧸ linearSliceIdeal f a p) := by
  apply Ideal.Quotient.ringHom_ext
  apply IsLocalization.ringHom_ext (maxIdealAt (linearSliceCoord a p)).primeCompl
  apply MvPolynomial.ringHom_ext
  · intro r
    change chartQuotientToLinearSliceQuotient f d hd a p hp hne
        (linearSliceQuotientToChartQuotient f d hd a p hp hne
          (quotientPolynomialMap (linearSliceCoord a p)
            (linearSliceIdeal f a p) (C r))) =
      quotientPolynomialMap (linearSliceCoord a p)
        (linearSliceIdeal f a p) (C r)
    rw [linearSliceQuotientToChartQuotient_quotientPolynomialMap,
      normalizeHom_of_isHomogeneous _ _ _ _ _ (isHomogeneous_C _ _),
      pow_zero, one_mul,
      chartQuotientToLinearSliceQuotient_quotientPolynomialMap,
      normalizeHom_of_isHomogeneous _ _ _ _ _ (isHomogeneous_C _ _),
      pow_zero, one_mul]
  · intro i
    change chartQuotientToLinearSliceQuotient f d hd a p hp hne
        (linearSliceQuotientToChartQuotient f d hd a p hp hne
          (quotientPolynomialMap (linearSliceCoord a p)
            (linearSliceIdeal f a p) (X i))) =
      quotientPolynomialMap (linearSliceCoord a p)
        (linearSliceIdeal f a p) (X i)
    rw [linearSliceQuotientToChartQuotient_quotientPolynomialMap,
      normalizeHom_of_isHomogeneous _ _ _ _ _
        (isHomogeneous_X K i),
      pow_one, map_mul,
      chartQuotientToLinearSliceQuotient_normalizationUnit_inv,
      chartQuotientToLinearSliceQuotient_quotientPolynomialMap,
      normalizeHom_of_isHomogeneous _ _ _ _ _
        (isHomogeneous_X K i),
      pow_one]
    exact Units.mul_inv_cancel_left
      (normalizationUnit (linearSliceCoord a p) (linearSliceIdeal f a p)
        (X (chartIndex p))
        (eval_linearSliceCoord_X_chartIndex_ne_zero a p hne))
      (quotientPolynomialMap (linearSliceCoord a p)
        (linearSliceIdeal f a p) (X i))

lemma linearSliceQuotientToChartQuotient_comp
    {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (a : Fin (n + 1) → K) (p : ProjSpace K n)
    (hp : p ∈ ⋂ k, vanishingSet (f k))
    (hne : eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    (linearSliceQuotientToChartQuotient f d hd a p hp hne).comp
        (chartQuotientToLinearSliceQuotient f d hd a p hp hne) =
      RingHom.id
        (localRingAt (affineConeCoord p) ⧸ localIntersectionIdeal f p) := by
  apply Ideal.Quotient.ringHom_ext
  apply IsLocalization.ringHom_ext (maxIdealAt (affineConeCoord p)).primeCompl
  apply MvPolynomial.ringHom_ext
  · intro r
    change linearSliceQuotientToChartQuotient f d hd a p hp hne
        (chartQuotientToLinearSliceQuotient f d hd a p hp hne
          (quotientPolynomialMap (affineConeCoord p)
            (localIntersectionIdeal f p) (C r))) =
      quotientPolynomialMap (affineConeCoord p)
        (localIntersectionIdeal f p) (C r)
    rw [chartQuotientToLinearSliceQuotient_quotientPolynomialMap,
      normalizeHom_of_isHomogeneous _ _ _ _ _ (isHomogeneous_C _ _),
      pow_zero, one_mul,
      linearSliceQuotientToChartQuotient_quotientPolynomialMap,
      normalizeHom_of_isHomogeneous _ _ _ _ _ (isHomogeneous_C _ _),
      pow_zero, one_mul]
  · intro i
    change linearSliceQuotientToChartQuotient f d hd a p hp hne
        (chartQuotientToLinearSliceQuotient f d hd a p hp hne
          (quotientPolynomialMap (affineConeCoord p)
            (localIntersectionIdeal f p) (X i))) =
      quotientPolynomialMap (affineConeCoord p)
        (localIntersectionIdeal f p) (X i)
    rw [chartQuotientToLinearSliceQuotient_quotientPolynomialMap,
      normalizeHom_of_isHomogeneous _ _ _ _ _
        (isHomogeneous_X K i),
      pow_one, map_mul,
      linearSliceQuotientToChartQuotient_normalizationUnit_inv,
      linearSliceQuotientToChartQuotient_quotientPolynomialMap,
      normalizeHom_of_isHomogeneous _ _ _ _ _
        (isHomogeneous_X K i),
      pow_one]
    exact Units.mul_inv_cancel_left
      (normalizationUnit (affineConeCoord p) (localIntersectionIdeal f p)
        (linearForm a)
        (eval_affineConeCoord_linearForm_ne_zero a p hne))
      (quotientPolynomialMap (affineConeCoord p)
        (localIntersectionIdeal f p) (X i))

noncomputable def localSliceRingEquiv
    {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (a : Fin (n + 1) → K) (p : ProjSpace K n)
    (hp : p ∈ ⋂ k, vanishingSet (f k))
    (hne : eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    (localRingAt (affineConeCoord p) ⧸ localIntersectionIdeal f p) ≃+*
      (localRingAt (linearSliceCoord a p) ⧸ linearSliceIdeal f a p) :=
  RingEquiv.ofRingHom
    (chartQuotientToLinearSliceQuotient f d hd a p hp hne)
    (linearSliceQuotientToChartQuotient f d hd a p hp hne)
    (chartQuotientToLinearSliceQuotient_comp f d hd a p hp hne)
    (linearSliceQuotientToChartQuotient_comp f d hd a p hp hne)

lemma localSliceRingEquiv_algebraMap
    {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (a : Fin (n + 1) → K) (p : ProjSpace K n)
    (hp : p ∈ ⋂ k, vanishingSet (f k))
    (hne : eval (Projectivization.rep p) (linearForm a) ≠ 0)
    (r : K) :
    localSliceRingEquiv f d hd a p hp hne
        (algebraMap K
          (localRingAt (affineConeCoord p) ⧸ localIntersectionIdeal f p) r) =
      algebraMap K
        (localRingAt (linearSliceCoord a p) ⧸ linearSliceIdeal f a p) r := by
  change chartQuotientToLinearSliceQuotient f d hd a p hp hne
      (algebraMap K
        (localRingAt (affineConeCoord p) ⧸ localIntersectionIdeal f p) r) =
    algebraMap K
      (localRingAt (linearSliceCoord a p) ⧸ linearSliceIdeal f a p) r
  calc
    _ = chartQuotientToLinearSliceQuotient f d hd a p hp hne
        (quotientPolynomialMap (affineConeCoord p)
          (localIntersectionIdeal f p) (C r)) := by
      congr 1
    _ = normalizeHom (linearSliceCoord a p) (linearSliceIdeal f a p)
        (X (chartIndex p))
        (eval_linearSliceCoord_X_chartIndex_ne_zero a p hne) (C r) :=
      chartQuotientToLinearSliceQuotient_quotientPolynomialMap
        f d hd a p hp hne (C r)
    _ = quotientPolynomialMap (linearSliceCoord a p)
        (linearSliceIdeal f a p) (C r) := by
      rw [normalizeHom_of_isHomogeneous _ _ _ _ _
        (isHomogeneous_C _ _), pow_zero, one_mul]
    _ = _ := by
      change (algebraMap (MvPolynomial (Fin (n + 1)) K)
          (localRingAt (linearSliceCoord a p) ⧸ linearSliceIdeal f a p))
          (C r) =
        algebraMap K
          (localRingAt (linearSliceCoord a p) ⧸ linearSliceIdeal f a p) r
      simpa only [← algebraMap_eq] using
        (IsScalarTower.algebraMap_apply K
          (MvPolynomial (Fin (n + 1)) K)
          (localRingAt (linearSliceCoord a p) ⧸ linearSliceIdeal f a p)
          r).symm

noncomputable def localSliceAlgEquiv
    {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (a : Fin (n + 1) → K) (p : ProjSpace K n)
    (hp : p ∈ ⋂ k, vanishingSet (f k))
    (hne : eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    (localRingAt (affineConeCoord p) ⧸ localIntersectionIdeal f p) ≃ₐ[K]
      (localRingAt (linearSliceCoord a p) ⧸ linearSliceIdeal f a p) :=
  AlgEquiv.ofRingEquiv (localSliceRingEquiv_algebraMap f d hd a p hp hne)

lemma intersectionMultiplicity_eq_linearSlice_length
    {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (a : Fin (n + 1) → K) (p : ProjSpace K n)
    (hp : p ∈ ⋂ k, vanishingSet (f k))
    (hne : eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    intersectionMultiplicity f p =
      Module.length K
        (localRingAt (linearSliceCoord a p) ⧸ linearSliceIdeal f a p) := by
  change Module.length K
      (localRingAt (affineConeCoord p) ⧸ localIntersectionIdeal f p) =
    Module.length K
      (localRingAt (linearSliceCoord a p) ⧸ linearSliceIdeal f a p)
  exact (localSliceAlgEquiv f d hd a p hp hne).toLinearEquiv.length_eq

end Submission.Helpers
