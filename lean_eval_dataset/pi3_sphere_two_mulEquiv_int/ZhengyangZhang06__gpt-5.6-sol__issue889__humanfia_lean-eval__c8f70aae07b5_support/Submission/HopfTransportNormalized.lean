import Submission.HopfTransport

noncomputable section

namespace Submission.HopfTransport

open Submission.Helpers

/-- The locus on which short Hopf transport can be normalized. -/
abbrev Domain :=
  {p : SphereThree × SphereTwo // raw p.1 p.2 ≠ 0}

/-- Normalize the short transported spinor to a point of the unit 3-sphere. -/
def transport (p : Domain) : SphereThree :=
  ⟨NormedSpace.normalize (raw p.1.1 p.1.2), by
    rw [Metric.mem_sphere, dist_zero_right]
    exact NormedSpace.norm_normalize p.2⟩

lemma continuous_transport : Continuous transport := by
  apply Continuous.subtype_mk
  let f : Domain → EuclideanSpace ℂ (Fin 2) :=
    fun p => raw p.1.1 p.1.2
  have hf : Continuous f :=
    continuous_raw.comp continuous_subtype_val
  change Continuous fun p => ‖f p‖⁻¹ • f p
  exact (hf.norm.inv₀ fun p => norm_ne_zero_iff.mpr p.2).smul hf

/-- The polynomial Hopf map is quadratic under real scaling. -/
lemma hopfMapRaw_real_smul (r : ℝ)
    (w : EuclideanSpace ℂ (Fin 2)) :
    hopfMapRaw (r • w) = r ^ 2 • hopfMapRaw w := by
  ext i
  fin_cases i
  · simp [hopfMapRaw, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im]
    ring
  · simp [hopfMapRaw, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im]
    ring
  · simp [hopfMapRaw, Matrix.cons_val_two, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im]
    ring

lemma raw_normSq_eq_norm_sq (z : SphereThree) (y : SphereTwo) :
    Complex.normSq (raw z y 0) + Complex.normSq (raw z y 1) =
      ‖raw z y‖ ^ 2 := by
  have h := EuclideanSpace.norm_sq_eq (raw z y)
  rw [Fin.sum_univ_two, Complex.sq_norm, Complex.sq_norm] at h
  exact h.symm

/-- Short transport lies over its target point. -/
@[simp]
lemma hopfMap_transport (p : Domain) :
    hopfMap (transport p) = p.1.2 := by
  apply Subtype.ext
  change
    hopfMapRaw (NormedSpace.normalize (raw p.1.1 p.1.2)) =
      (p.1.2 : EuclideanSpace ℝ (Fin 3))
  rw [NormedSpace.normalize, hopfMapRaw_real_smul, hopfMapRaw_raw,
    smul_smul]
  have hnorm : ‖raw p.1.1 p.1.2‖ ≠ 0 :=
    norm_ne_zero_iff.mpr p.2
  have hsq := raw_normSq_eq_norm_sq p.1.1 p.1.2
  have hscalar :
      ‖raw p.1.1 p.1.2‖⁻¹ ^ 2 *
          (Complex.normSq (raw p.1.1 p.1.2 0) +
            Complex.normSq (raw p.1.1 p.1.2 1)) = 1 := by
    rw [hsq]
    field_simp
  rw [hscalar, one_smul]

lemma sphereThree_val_ne_zero (z : SphereThree) :
    (z : EuclideanSpace ℂ (Fin 2)) ≠ 0 := by
  intro hz
  have hnorm : ‖(z : EuclideanSpace ℂ (Fin 2))‖ = 1 := by
    rw [← dist_zero_right]
    exact z.property
  rw [hz, norm_zero] at hnorm
  norm_num at hnorm

/-- A lift and its own Hopf image always form an admissible pair. -/
def selfDomain (z : SphereThree) : Domain :=
  ⟨(z, hopfMap z), by
    rw [raw_self]
    rw [← two_smul ℝ]
    exact smul_ne_zero (by norm_num) (sphereThree_val_ne_zero z)⟩

/-- Transport to the current base point fixes the lift. -/
@[simp]
lemma transport_selfDomain (z : SphereThree) :
    transport (selfDomain z) = z := by
  apply Subtype.ext
  change
    NormedSpace.normalize (raw z (hopfMap z)) =
      (z : EuclideanSpace ℂ (Fin 2))
  rw [raw_self, ← two_smul ℝ,
    NormedSpace.normalize_smul_of_pos (by norm_num)]
  apply NormedSpace.normalize_eq_self_of_norm_eq_one
  rw [← dist_zero_right]
  exact z.property

/-- Base points at distance less than two are never antipodal, hence the raw
short transport is nonzero. -/
lemma raw_ne_zero_of_dist_lt_two {z : SphereThree} {y : SphereTwo}
    (h : dist (hopfMap z) y < 2) :
    raw z y ≠ 0 := by
  have hx := sphereTwo_sq_add (hopfMap z)
  have hy := sphereTwo_sq_add y
  have hdist :
      ‖(hopfMap z : EuclideanSpace ℝ (Fin 3)) -
          (y : EuclideanSpace ℝ (Fin 3))‖ < 2 := by
    change
      dist (hopfMap z : EuclideanSpace ℝ (Fin 3))
        (y : EuclideanSpace ℝ (Fin 3)) < 2 at h
    simpa [dist_eq_norm] using h
  have hnorm :=
    EuclideanSpace.real_norm_sq_eq
      ((hopfMap z : EuclideanSpace ℝ (Fin 3)) -
        (y : EuclideanSpace ℝ (Fin 3)))
  rw [Fin.sum_univ_three] at hnorm
  have hdot :
      -1 <
        (hopfMap z).1 0 * y.1 0 +
          (hopfMap z).1 1 * y.1 1 +
          (hopfMap z).1 2 * y.1 2 := by
    simp only [PiLp.sub_apply] at hnorm
    nlinarith [norm_nonneg
      ((hopfMap z : EuclideanSpace ℝ (Fin 3)) -
        (y : EuclideanSpace ℝ (Fin 3)))]
  intro hzero
  have hcoords :
      Complex.normSq (raw z y 0) + Complex.normSq (raw z y 1) = 0 := by
    rw [hzero]
    simp
  rw [raw_normSq] at hcoords
  nlinarith

/-- Package a non-antipodal pair for short transport. -/
def domainOfDistLtTwo (z : SphereThree) (y : SphereTwo)
    (h : dist (hopfMap z) y < 2) : Domain :=
  ⟨(z, y), raw_ne_zero_of_dist_lt_two h⟩

/-- Pointwise short transport for a family of lifts and nearby target
points. -/
def transportOf {A : Type*} (z : A → SphereThree) (y : A → SphereTwo)
    (h : ∀ a, dist (hopfMap (z a)) (y a) < 2) (a : A) :
    SphereThree :=
  transport (domainOfDistLtTwo (z a) (y a) (h a))

@[simp]
lemma hopfMap_transportOf {A : Type*} (z : A → SphereThree)
    (y : A → SphereTwo)
    (h : ∀ a, dist (hopfMap (z a)) (y a) < 2) (a : A) :
    hopfMap (transportOf z y h a) = y a :=
  hopfMap_transport _

/-- Short transport preserves continuity uniformly in any parameter
space. -/
lemma continuous_transportOf {A : Type*} [TopologicalSpace A]
    {z : A → SphereThree} {y : A → SphereTwo}
    (h : ∀ a, dist (hopfMap (z a)) (y a) < 2)
    (hz : Continuous z) (hy : Continuous y) :
    Continuous (transportOf z y h) := by
  apply continuous_transport.comp
  exact (hz.prodMk hy).subtype_mk _

lemma transportOf_eq_self {A : Type*} (z : A → SphereThree)
    (y : A → SphereTwo)
    (h : ∀ a, dist (hopfMap (z a)) (y a) < 2) (a : A)
    (hy : y a = hopfMap (z a)) :
    transportOf z y h a = z a := by
  unfold transportOf
  have hdomain :
      domainOfDistLtTwo (z a) (y a) (h a) =
        selfDomain (z a) := by
    apply Subtype.ext
    exact Prod.ext rfl hy
  rw [hdomain]
  exact transport_selfDomain (z a)

end Submission.HopfTransport
