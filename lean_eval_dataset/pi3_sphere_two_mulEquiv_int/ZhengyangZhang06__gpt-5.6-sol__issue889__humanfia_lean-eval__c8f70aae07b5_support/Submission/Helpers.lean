import Mathlib
import Submission.CircleHomotopy
import Submission.HomotopyMap

noncomputable section

namespace Submission.Helpers

open Topology.Homotopy
open scoped ComplexConjugate

theorem nonemptyMulEquivIntOfInfiniteCyclic
    (G : Type*) [Group G] [Infinite G] [IsCyclic G] :
    Nonempty (G ≃* Multiplicative ℤ) :=
  ⟨intCyclicMulEquiv.symm⟩

theorem nonemptyMulEquivIntOfZPowersHomBijective
    (G : Type*) [Group G] (g : G)
    (hg : Function.Bijective (zpowersHom G g)) :
    Nonempty (G ≃* Multiplicative ℤ) :=
  ⟨(MulEquiv.ofBijective (zpowersHom G g) hg).symm⟩

theorem nonempty_mulEquiv_int_iff_infinite_and_isCyclic
    (G : Type*) [Group G] :
    Nonempty (G ≃* Multiplicative ℤ) ↔ Infinite G ∧ IsCyclic G := by
  constructor
  · rintro ⟨e⟩
    exact ⟨Infinite.of_injective e.symm e.symm.injective,
      e.isCyclic.mpr inferInstance⟩
  · rintro ⟨hInfinite, hCyclic⟩
    letI := hInfinite
    letI := hCyclic
    exact nonemptyMulEquivIntOfInfiniteCyclic G

variable {N X : Type*} [TopologicalSpace X] (x : X)

/-- The equivalence with the fundamental group of an iterated loop space respects
the canonical group structure on a positive-dimensional homotopy group. -/
def homotopyGroupMulEquivFundamentalGroup [DecidableEq N] [Nonempty N] (i : N) :
    HomotopyGroup N X x ≃*
      FundamentalGroup (GenLoop {j // j ≠ i} X x) GenLoop.const := by
  refine
    { toEquiv := homotopyGroupEquivFundamentalGroup (X := X) (x := x) i
      map_mul' := ?_ }
  intro a b
  induction a using Quotient.inductionOn with
  | _ p =>
    induction b using Quotient.inductionOn with
    | _ q =>
      simp only [HomotopyGroup.mul_spec (i := i)]
      apply Quotient.sound
      rw [← GenLoop.fromLoop_trans_toLoop]
      change
        (GenLoop.toLoop i
            (GenLoop.fromLoop i
              ((GenLoop.toLoop i q).trans (GenLoop.toLoop i p)))).Homotopic
          ((GenLoop.toLoop i q).trans (GenLoop.toLoop i p))
      rw [GenLoop.to_from]

abbrev SphereTwo :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

abbrev SphereThree :=
  Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1

abbrev SphereThreeReal :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/-- The real-coordinate identification `ℂ² ≃ ℝ⁴`. -/
def complexPairRealLinearEquiv :
    EuclideanSpace ℂ (Fin 2) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 4) where
  toFun z := !₂[(z 0).re, (z 0).im, (z 1).re, (z 1).im]
  invFun v := !₂[⟨v 0, v 1⟩, ⟨v 2, v 3⟩]
  left_inv z := by
    ext i
    fin_cases i <;> apply Complex.ext <;> simp
  right_inv v := by
    ext i
    fin_cases i <;> simp
  map_add' z w := by
    ext i
    fin_cases i <;> simp
  map_smul' r z := by
    ext i
    fin_cases i <;> simp

/-- The real-coordinate identification preserves the Euclidean norm. -/
def complexPairRealLinearIsometry :
    EuclideanSpace ℂ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4) :=
  { complexPairRealLinearEquiv with
    norm_map' := fun z => by
      have hz := EuclideanSpace.norm_sq_eq z
      have hv := EuclideanSpace.real_norm_sq_eq
        (complexPairRealLinearEquiv z)
      rw [Fin.sum_univ_two, Complex.sq_norm, Complex.sq_norm,
        Complex.normSq_apply, Complex.normSq_apply] at hz
      rw [Fin.sum_univ_four] at hv
      simp [complexPairRealLinearEquiv] at hv
      ring_nf at hz hv
      rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
      exact hv.trans hz.symm }

/-- A linear isometry restricts to a homeomorphism of unit spheres. -/
def unitSphereHomeomorphOfLinearIsometry
    {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [Module ℝ E] [Module ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) :
    Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : F) 1 where
  toFun z := ⟨e z, by
    rw [mem_sphere_zero_iff_norm, e.norm_map]
    rw [← mem_sphere_zero_iff_norm]
    exact z.property⟩
  invFun v := ⟨e.symm v, by
    rw [mem_sphere_zero_iff_norm, e.symm.norm_map]
    rw [← mem_sphere_zero_iff_norm]
    exact v.property⟩
  left_inv z := by
    apply Subtype.ext
    exact e.symm_apply_apply z
  right_inv v := by
    apply Subtype.ext
    exact e.apply_symm_apply v
  continuous_toFun :=
    (e.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (e.symm.continuous.comp continuous_subtype_val).subtype_mk _

/-- The complex and real concrete models of the unit 3-sphere are
homeomorphic. -/
def sphereThreeHomeomorphReal : SphereThree ≃ₜ SphereThreeReal :=
  unitSphereHomeomorphOfLinearIsometry complexPairRealLinearIsometry

/-- A canonical basepoint of the standard real 3-sphere. -/
def sphereThreeRealNorth : SphereThreeReal := by
  let v : EuclideanSpace ℝ (Fin 4) :=
    PiLp.single 2 (0 : Fin 4) (1 : ℝ)
  refine ⟨v, ?_⟩
  rw [mem_sphere_zero_iff_norm]
  simp [v]

lemma sphereThreeReal_norm (z : SphereThreeReal) :
    ‖(z : EuclideanSpace ℝ (Fin 4))‖ = 1 := by
  rw [← mem_sphere_zero_iff_norm]
  exact z.property

/-- Reflection in the hyperplane perpendicular to `z - north` sends a
unit vector `z` to the canonical north pole. -/
def sphereThreeRealReflection (z : SphereThreeReal) :
    EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4) :=
  Submodule.reflection
    (ℝ ∙ ((z : EuclideanSpace ℝ (Fin 4)) -
      (sphereThreeRealNorth : EuclideanSpace ℝ (Fin 4))))ᗮ

lemma sphereThreeRealReflection_apply (z : SphereThreeReal) :
    sphereThreeRealReflection z z = sphereThreeRealNorth := by
  change
    Submodule.reflection
        (ℝ ∙ ((z : EuclideanSpace ℝ (Fin 4)) -
          (sphereThreeRealNorth : EuclideanSpace ℝ (Fin 4))))ᗮ z =
      (sphereThreeRealNorth : EuclideanSpace ℝ (Fin 4))
  apply Submodule.reflection_sub
  rw [sphereThreeReal_norm, sphereThreeReal_norm]

/-- A self-homeomorphism of the real 3-sphere sending `z` to the
canonical north pole. -/
def sphereThreeRealHomeomorphNorth
    (z : SphereThreeReal) : SphereThreeReal ≃ₜ SphereThreeReal :=
  unitSphereHomeomorphOfLinearIsometry (sphereThreeRealReflection z)

@[simp]
lemma sphereThreeRealHomeomorphNorth_apply_self (z : SphereThreeReal) :
    sphereThreeRealHomeomorphNorth z z = sphereThreeRealNorth := by
  apply Subtype.ext
  exact sphereThreeRealReflection_apply z

abbrev CompactifiedThreeSpace :=
  OnePoint (EuclideanSpace ℝ (Fin 3))

/-- Stereographic compactification identifies real 3-space with the real
unit 3-sphere. -/
def compactifiedThreeSpaceHomeomorphSphereThreeReal :
    CompactifiedThreeSpace ≃ₜ SphereThreeReal :=
  onePointEquivSphereOfFinrankEq (by simp)

/-- A pointed version of stereographic compactification, normalized so that
the point at infinity is sent to the chosen north pole. -/
def compactifiedThreeSpaceHomeomorphNorth :
    CompactifiedThreeSpace ≃ₜ SphereThreeReal :=
  compactifiedThreeSpaceHomeomorphSphereThreeReal.trans
    (sphereThreeRealHomeomorphNorth
      (compactifiedThreeSpaceHomeomorphSphereThreeReal
        (OnePoint.infty : CompactifiedThreeSpace)))

@[simp]
lemma compactifiedThreeSpaceHomeomorphNorth_apply_infty :
    compactifiedThreeSpaceHomeomorphNorth
        (OnePoint.infty : CompactifiedThreeSpace) =
      sphereThreeRealNorth := by
  exact sphereThreeRealHomeomorphNorth_apply_self _

abbrev DoubleLoop (x : SphereTwo) :=
  GenLoop {j : Fin 3 // j ≠ 0} SphereTwo x

/-- The polynomial formula underlying the Hopf map
`S³ ⊆ ℂ² → S² ⊆ ℝ³`. -/
def hopfMapRaw (z : EuclideanSpace ℂ (Fin 2)) :
    EuclideanSpace ℝ (Fin 3) :=
  !₂[2 * (z 0 * conj (z 1)).re,
    2 * (z 0 * conj (z 1)).im,
    Complex.normSq (z 0) - Complex.normSq (z 1)]

lemma continuous_hopfMapRaw : Continuous hopfMapRaw := by
  unfold hopfMapRaw
  fun_prop

lemma hopfMapRaw_eq_iff {z w : EuclideanSpace ℂ (Fin 2)} :
    hopfMapRaw z = hopfMapRaw w ↔
      z 0 * conj (z 1) = w 0 * conj (w 1) ∧
        Complex.normSq (z 0) - Complex.normSq (z 1) =
          Complex.normSq (w 0) - Complex.normSq (w 1) := by
  constructor
  · intro h
    have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) h
    have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) h
    have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) h
    simp [hopfMapRaw] at h0 h1 h2
    refine ⟨?_, h2⟩
    apply Complex.ext
    · simpa using h0
    · simpa using h1
  · rintro ⟨hprod, hnorm⟩
    ext i
    fin_cases i <;> simp [hopfMapRaw, hprod, hnorm]

lemma norm_hopfMapRaw_sq (z : EuclideanSpace ℂ (Fin 2)) :
    ‖hopfMapRaw z‖ ^ 2 = ‖z‖ ^ 4 := by
  calc
    ‖hopfMapRaw z‖ ^ 2 =
        ∑ i, (hopfMapRaw z i) ^ 2 :=
      EuclideanSpace.real_norm_sq_eq _
    _ = (∑ i, ‖z i‖ ^ 2) ^ 2 := by
      rw [Fin.sum_univ_three, Fin.sum_univ_two]
      simp [hopfMapRaw, Complex.normSq_apply, Complex.sq_norm]
      ring
    _ = ‖z‖ ^ 4 := by
      rw [← EuclideanSpace.norm_sq_eq]
      ring

/-- The Hopf map between the concrete unit spheres used by the benchmark. -/
def hopfMap (z : SphereThree) : SphereTwo := by
  refine ⟨hopfMapRaw z, ?_⟩
  have hz : ‖(z : EuclideanSpace ℂ (Fin 2))‖ = 1 := by
    rw [← dist_zero_right]
    exact z.property
  have hsq := norm_hopfMapRaw_sq (z : EuclideanSpace ℂ (Fin 2))
  rw [hz] at hsq
  change dist (hopfMapRaw z) 0 = 1
  rw [dist_zero_right]
  nlinarith [norm_nonneg (hopfMapRaw z)]

lemma sphereThree_normSq_add (z : SphereThree) :
    Complex.normSq (z.1 0) + Complex.normSq (z.1 1) = 1 := by
  have hnorm := EuclideanSpace.norm_sq_eq
    (z : EuclideanSpace ℂ (Fin 2))
  rw [Fin.sum_univ_two, Complex.sq_norm, Complex.sq_norm] at hnorm
  have hz : ‖(z : EuclideanSpace ℂ (Fin 2))‖ = 1 := by
    rw [← dist_zero_right]
    exact z.property
  rw [hz] at hnorm
  norm_num at hnorm ⊢
  exact hnorm.symm

lemma sphereTwo_sq_add (x : SphereTwo) :
    x.1 0 ^ 2 + x.1 1 ^ 2 + x.1 2 ^ 2 = 1 := by
  have hnorm := EuclideanSpace.real_norm_sq_eq
    (x : EuclideanSpace ℝ (Fin 3))
  rw [Fin.sum_univ_three] at hnorm
  have hx : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    rw [← dist_zero_right]
    exact x.property
  rw [hx] at hnorm
  norm_num at hnorm ⊢
  exact hnorm.symm

/-- The concrete polynomial Hopf map reaches every point of the unit
2-sphere. -/
lemma hopfMap_surjective : Function.Surjective hopfMap := by
  intro x
  have hsphere := sphereTwo_sq_add x
  by_cases hsouth : x.1 2 = -1
  · have hx0 : x.1 0 = 0 := by
      nlinarith [sq_nonneg (x.1 0), sq_nonneg (x.1 1)]
    have hx1 : x.1 1 = 0 := by
      nlinarith [sq_nonneg (x.1 0), sq_nonneg (x.1 1)]
    let zraw : EuclideanSpace ℂ (Fin 2) := !₂[0, 1]
    have hznorm : ‖zraw‖ = 1 := by
      have hsq := EuclideanSpace.norm_sq_eq zraw
      rw [Fin.sum_univ_two] at hsq
      norm_num [zraw] at hsq
      rcases hsq with hsq | hsq
      · exact hsq
      · nlinarith [norm_nonneg zraw]
    let z : SphereThree := ⟨zraw, by
      change zraw ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1
      rw [mem_sphere_zero_iff_norm]
      exact hznorm⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [hopfMap, hopfMapRaw, z, zraw, hx0, hx1, hsouth]
  · have hc_lower : -1 < x.1 2 := by
      have hc : -1 ≤ x.1 2 := by
        nlinarith [sq_nonneg (x.1 0), sq_nonneg (x.1 1),
          sq_nonneg (x.1 2 + 1)]
      exact lt_of_le_of_ne hc (Ne.symm hsouth)
    let r : ℝ := Real.sqrt ((1 + x.1 2) / 2)
    have hrpos : 0 < r := by
      apply Real.sqrt_pos.2
      linarith
    have hrsq : r ^ 2 = (1 + x.1 2) / 2 := by
      apply Real.sq_sqrt
      linarith
    let zraw : EuclideanSpace ℂ (Fin 2) :=
      !₂[⟨r, 0⟩, ⟨x.1 0 / (2 * r), -x.1 1 / (2 * r)⟩]
    have hz0 :
        Complex.normSq (zraw 0) = (1 + x.1 2) / 2 := by
      simp [zraw, Complex.normSq_apply]
      nlinarith
    have hz1 :
        Complex.normSq (zraw 1) = (1 - x.1 2) / 2 := by
      simp [zraw, Complex.normSq_apply]
      field_simp [ne_of_gt hrpos]
      nlinarith [hrsq, hsphere]
    have hznorm : ‖zraw‖ = 1 := by
      have hsq := EuclideanSpace.norm_sq_eq zraw
      rw [Fin.sum_univ_two, Complex.sq_norm, Complex.sq_norm,
        hz0, hz1] at hsq
      nlinarith [norm_nonneg zraw]
    let z : SphereThree := ⟨zraw, by
      change zraw ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1
      rw [mem_sphere_zero_iff_norm]
      exact hznorm⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    ext i
    fin_cases i
    · change 2 * ((zraw 0 * conj (zraw 1)).re) = x.1 0
      simp [zraw, Complex.mul_re]
      field_simp [ne_of_gt hrpos]
    · change 2 * ((zraw 0 * conj (zraw 1)).im) = x.1 1
      simp [zraw, Complex.mul_im]
      field_simp [ne_of_gt hrpos]
    · change
        Complex.normSq (zraw 0) - Complex.normSq (zraw 1) = x.1 2
      rw [hz0, hz1]
      ring

/-- The standard northern chart of the 2-sphere, obtained by deleting the
south pole. -/
abbrev SphereTwoAwaySouth :=
  {x : SphereTwo // x.1 2 ≠ -1}

/-- The positive first-coordinate radius used by the northern Hopf section. -/
def hopfNorthRadius (x : SphereTwoAwaySouth) : ℝ :=
  Real.sqrt ((1 + x.1.1 2) / 2)

lemma hopfNorthRadius_pos (x : SphereTwoAwaySouth) :
    0 < hopfNorthRadius x := by
  apply Real.sqrt_pos.2
  have hsphere := sphereTwo_sq_add x.1
  have hc : -1 ≤ x.1.1 2 := by
    nlinarith [sq_nonneg (x.1.1 0), sq_nonneg (x.1.1 1),
      sq_nonneg (x.1.1 2 + 1)]
  have hc_lower : -1 < x.1.1 2 :=
    lt_of_le_of_ne hc (Ne.symm x.property)
  linarith

lemma hopfNorthRadius_sq (x : SphereTwoAwaySouth) :
    hopfNorthRadius x ^ 2 = (1 + x.1.1 2) / 2 := by
  apply Real.sq_sqrt
  exact (Real.sqrt_pos.1 (hopfNorthRadius_pos x)).le

/-- The explicit lift of the northern Hopf chart before imposing the unit
sphere condition. -/
def hopfSectionAwaySouthRaw (x : SphereTwoAwaySouth) :
    EuclideanSpace ℂ (Fin 2) :=
  !₂[(hopfNorthRadius x : ℂ),
    ((x.1.1 0 / (2 * hopfNorthRadius x) : ℝ) : ℂ) -
      ((x.1.1 1 / (2 * hopfNorthRadius x) : ℝ) : ℂ) * Complex.I]

@[simp]
lemma hopfSectionAwaySouthRaw_zero (x : SphereTwoAwaySouth) :
    hopfSectionAwaySouthRaw x 0 = (hopfNorthRadius x : ℂ) :=
  rfl

@[simp]
lemma hopfSectionAwaySouthRaw_one_re (x : SphereTwoAwaySouth) :
    (hopfSectionAwaySouthRaw x 1).re =
      x.1.1 0 / (2 * hopfNorthRadius x) := by
  change
    (((x.1.1 0 / (2 * hopfNorthRadius x) : ℝ) : ℂ) -
      ((x.1.1 1 / (2 * hopfNorthRadius x) : ℝ) : ℂ) *
        Complex.I).re =
      x.1.1 0 / (2 * hopfNorthRadius x)
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_zero]

@[simp]
lemma hopfSectionAwaySouthRaw_one_im (x : SphereTwoAwaySouth) :
    (hopfSectionAwaySouthRaw x 1).im =
      -(x.1.1 1 / (2 * hopfNorthRadius x)) := by
  change
    (((x.1.1 0 / (2 * hopfNorthRadius x) : ℝ) : ℂ) -
      ((x.1.1 1 / (2 * hopfNorthRadius x) : ℝ) : ℂ) *
        Complex.I).im =
      -(x.1.1 1 / (2 * hopfNorthRadius x))
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, zero_mul,
    add_zero, zero_sub]

lemma hopfSectionAwaySouthRaw_normSq_zero (x : SphereTwoAwaySouth) :
    Complex.normSq (hopfSectionAwaySouthRaw x 0) =
      (1 + x.1.1 2) / 2 := by
  rw [Complex.normSq_apply, hopfSectionAwaySouthRaw_zero]
  norm_num
  simpa [pow_two] using hopfNorthRadius_sq x

lemma hopfSectionAwaySouthRaw_normSq_one (x : SphereTwoAwaySouth) :
    Complex.normSq (hopfSectionAwaySouthRaw x 1) =
      (1 - x.1.1 2) / 2 := by
  rw [Complex.normSq_apply, hopfSectionAwaySouthRaw_one_re,
    hopfSectionAwaySouthRaw_one_im]
  have hsphere := sphereTwo_sq_add x.1
  have hrpos := hopfNorthRadius_pos x
  have hrsq := hopfNorthRadius_sq x
  field_simp [ne_of_gt hrpos]
  nlinarith

lemma hopfSectionAwaySouthRaw_norm (x : SphereTwoAwaySouth) :
    ‖hopfSectionAwaySouthRaw x‖ = 1 := by
  have hsq := EuclideanSpace.norm_sq_eq (hopfSectionAwaySouthRaw x)
  rw [Fin.sum_univ_two, Complex.sq_norm, Complex.sq_norm,
    hopfSectionAwaySouthRaw_normSq_zero,
    hopfSectionAwaySouthRaw_normSq_one] at hsq
  nlinarith [norm_nonneg (hopfSectionAwaySouthRaw x)]

/-- A continuous local section of the Hopf map away from the south pole. -/
def hopfSectionAwaySouth (x : SphereTwoAwaySouth) : SphereThree :=
  ⟨hopfSectionAwaySouthRaw x, by
    rw [mem_sphere_zero_iff_norm]
    exact hopfSectionAwaySouthRaw_norm x⟩

@[simp]
lemma hopfMap_hopfSectionAwaySouth (x : SphereTwoAwaySouth) :
    hopfMap (hopfSectionAwaySouth x) = x.1 := by
  have hrpos := hopfNorthRadius_pos x
  have hrsq := hopfNorthRadius_sq x
  have hsphere := sphereTwo_sq_add x.1
  apply Subtype.ext
  ext i
  fin_cases i
  · change
      2 * ((hopfSectionAwaySouthRaw x 0 *
        conj (hopfSectionAwaySouthRaw x 1)).re) = x.1.1 0
    rw [Complex.mul_re]
    simp only [hopfSectionAwaySouthRaw_zero, Complex.ofReal_re,
      Complex.conj_re, hopfSectionAwaySouthRaw_one_re,
      Complex.ofReal_im, Complex.conj_im,
      hopfSectionAwaySouthRaw_one_im, zero_mul, sub_zero]
    field_simp [ne_of_gt hrpos]
  · change
      2 * ((hopfSectionAwaySouthRaw x 0 *
        conj (hopfSectionAwaySouthRaw x 1)).im) = x.1.1 1
    rw [Complex.mul_im]
    simp only [hopfSectionAwaySouthRaw_zero, Complex.ofReal_re,
      Complex.conj_im, hopfSectionAwaySouthRaw_one_im,
      Complex.ofReal_im, Complex.conj_re,
      hopfSectionAwaySouthRaw_one_re, zero_mul, add_zero]
    field_simp [ne_of_gt hrpos]
  · change
      Complex.normSq (hopfSectionAwaySouthRaw x 0) -
          Complex.normSq (hopfSectionAwaySouthRaw x 1) =
        x.1.1 2
    rw [hopfSectionAwaySouthRaw_normSq_zero,
      hopfSectionAwaySouthRaw_normSq_one]
    ring

@[fun_prop]
lemma continuous_hopfNorthRadius :
    Continuous hopfNorthRadius := by
  unfold hopfNorthRadius
  fun_prop

lemma continuous_hopfSectionAwaySouthRaw :
    Continuous hopfSectionAwaySouthRaw := by
  unfold hopfSectionAwaySouthRaw
  have hdenom :
      ∀ x : SphereTwoAwaySouth, 2 * hopfNorthRadius x ≠ 0 :=
    fun x => mul_ne_zero (by norm_num) (ne_of_gt (hopfNorthRadius_pos x))
  fun_prop (disch := assumption)

lemma continuous_hopfSectionAwaySouth :
    Continuous hopfSectionAwaySouth :=
  continuous_hopfSectionAwaySouthRaw.subtype_mk _

/-- The standard southern chart of the 2-sphere, obtained by deleting the
north pole. -/
abbrev SphereTwoAwayNorth :=
  {x : SphereTwo // x.1 2 ≠ 1}

/-- The positive second-coordinate radius used by the southern Hopf
section. -/
def hopfSouthRadius (x : SphereTwoAwayNorth) : ℝ :=
  Real.sqrt ((1 - x.1.1 2) / 2)

lemma hopfSouthRadius_pos (x : SphereTwoAwayNorth) :
    0 < hopfSouthRadius x := by
  apply Real.sqrt_pos.2
  have hsphere := sphereTwo_sq_add x.1
  have hc : x.1.1 2 ≤ 1 := by
    nlinarith [sq_nonneg (x.1.1 0), sq_nonneg (x.1.1 1),
      sq_nonneg (x.1.1 2 - 1)]
  have hc_upper : x.1.1 2 < 1 :=
    lt_of_le_of_ne hc x.property
  linarith

lemma hopfSouthRadius_sq (x : SphereTwoAwayNorth) :
    hopfSouthRadius x ^ 2 = (1 - x.1.1 2) / 2 := by
  apply Real.sq_sqrt
  exact (Real.sqrt_pos.1 (hopfSouthRadius_pos x)).le

/-- The explicit lift of the southern Hopf chart before imposing the unit
sphere condition. -/
def hopfSectionAwayNorthRaw (x : SphereTwoAwayNorth) :
    EuclideanSpace ℂ (Fin 2) :=
  !₂[
    ((x.1.1 0 / (2 * hopfSouthRadius x) : ℝ) : ℂ) +
      ((x.1.1 1 / (2 * hopfSouthRadius x) : ℝ) : ℂ) * Complex.I,
    (hopfSouthRadius x : ℂ)]

@[simp]
lemma hopfSectionAwayNorthRaw_zero_re (x : SphereTwoAwayNorth) :
    (hopfSectionAwayNorthRaw x 0).re =
      x.1.1 0 / (2 * hopfSouthRadius x) := by
  change
    ((((x.1.1 0 / (2 * hopfSouthRadius x) : ℝ) : ℂ) +
      ((x.1.1 1 / (2 * hopfSouthRadius x) : ℝ) : ℂ) *
        Complex.I)).re =
      x.1.1 0 / (2 * hopfSouthRadius x)
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_self, add_zero]

@[simp]
lemma hopfSectionAwayNorthRaw_zero_im (x : SphereTwoAwayNorth) :
    (hopfSectionAwayNorthRaw x 0).im =
      x.1.1 1 / (2 * hopfSouthRadius x) := by
  change
    ((((x.1.1 0 / (2 * hopfSouthRadius x) : ℝ) : ℂ) +
      ((x.1.1 1 / (2 * hopfSouthRadius x) : ℝ) : ℂ) *
        Complex.I)).im =
      x.1.1 1 / (2 * hopfSouthRadius x)
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, zero_mul,
    zero_add, add_zero]

@[simp]
lemma hopfSectionAwayNorthRaw_one (x : SphereTwoAwayNorth) :
    hopfSectionAwayNorthRaw x 1 = (hopfSouthRadius x : ℂ) :=
  rfl

lemma hopfSectionAwayNorthRaw_normSq_zero (x : SphereTwoAwayNorth) :
    Complex.normSq (hopfSectionAwayNorthRaw x 0) =
      (1 + x.1.1 2) / 2 := by
  rw [Complex.normSq_apply, hopfSectionAwayNorthRaw_zero_re,
    hopfSectionAwayNorthRaw_zero_im]
  have hsphere := sphereTwo_sq_add x.1
  have hrpos := hopfSouthRadius_pos x
  have hrsq := hopfSouthRadius_sq x
  field_simp [ne_of_gt hrpos]
  nlinarith

lemma hopfSectionAwayNorthRaw_normSq_one (x : SphereTwoAwayNorth) :
    Complex.normSq (hopfSectionAwayNorthRaw x 1) =
      (1 - x.1.1 2) / 2 := by
  rw [Complex.normSq_apply, hopfSectionAwayNorthRaw_one]
  norm_num
  simpa [pow_two] using hopfSouthRadius_sq x

lemma hopfSectionAwayNorthRaw_norm (x : SphereTwoAwayNorth) :
    ‖hopfSectionAwayNorthRaw x‖ = 1 := by
  have hsq := EuclideanSpace.norm_sq_eq (hopfSectionAwayNorthRaw x)
  rw [Fin.sum_univ_two, Complex.sq_norm, Complex.sq_norm,
    hopfSectionAwayNorthRaw_normSq_zero,
    hopfSectionAwayNorthRaw_normSq_one] at hsq
  nlinarith [norm_nonneg (hopfSectionAwayNorthRaw x)]

/-- A continuous local section of the Hopf map away from the north pole. -/
def hopfSectionAwayNorth (x : SphereTwoAwayNorth) : SphereThree :=
  ⟨hopfSectionAwayNorthRaw x, by
    rw [mem_sphere_zero_iff_norm]
    exact hopfSectionAwayNorthRaw_norm x⟩

@[simp]
lemma hopfMap_hopfSectionAwayNorth (x : SphereTwoAwayNorth) :
    hopfMap (hopfSectionAwayNorth x) = x.1 := by
  have hrpos := hopfSouthRadius_pos x
  have hrsq := hopfSouthRadius_sq x
  have hsphere := sphereTwo_sq_add x.1
  apply Subtype.ext
  ext i
  fin_cases i
  · change
      2 * ((hopfSectionAwayNorthRaw x 0 *
        conj (hopfSectionAwayNorthRaw x 1)).re) = x.1.1 0
    rw [Complex.mul_re]
    simp only [hopfSectionAwayNorthRaw_zero_re,
      hopfSectionAwayNorthRaw_one, Complex.conj_re, Complex.ofReal_re,
      hopfSectionAwayNorthRaw_zero_im, Complex.conj_im,
      Complex.ofReal_im, neg_zero, mul_zero, sub_zero]
    field_simp [ne_of_gt hrpos]
  · change
      2 * ((hopfSectionAwayNorthRaw x 0 *
        conj (hopfSectionAwayNorthRaw x 1)).im) = x.1.1 1
    rw [Complex.mul_im]
    simp only [hopfSectionAwayNorthRaw_zero_re,
      hopfSectionAwayNorthRaw_one, Complex.conj_im, Complex.ofReal_im,
      hopfSectionAwayNorthRaw_zero_im, Complex.conj_re,
      Complex.ofReal_re, neg_zero, mul_zero, zero_add]
    field_simp [ne_of_gt hrpos]
  · change
      Complex.normSq (hopfSectionAwayNorthRaw x 0) -
          Complex.normSq (hopfSectionAwayNorthRaw x 1) =
        x.1.1 2
    rw [hopfSectionAwayNorthRaw_normSq_zero,
      hopfSectionAwayNorthRaw_normSq_one]
    ring

@[fun_prop]
lemma continuous_hopfSouthRadius :
    Continuous hopfSouthRadius := by
  unfold hopfSouthRadius
  fun_prop

lemma continuous_hopfSectionAwayNorthRaw :
    Continuous hopfSectionAwayNorthRaw := by
  unfold hopfSectionAwayNorthRaw
  have hdenom :
      ∀ x : SphereTwoAwayNorth, 2 * hopfSouthRadius x ≠ 0 :=
    fun x => mul_ne_zero (by norm_num) (ne_of_gt (hopfSouthRadius_pos x))
  fun_prop (disch := assumption)

lemma continuous_hopfSectionAwayNorth :
    Continuous hopfSectionAwayNorth :=
  continuous_hopfSectionAwayNorthRaw.subtype_mk _

lemma continuous_hopfMap : Continuous hopfMap :=
  (continuous_hopfMapRaw.comp continuous_subtype_val).subtype_mk _

def hopfContinuousMap : C(SphereThree, SphereTwo) :=
  ⟨hopfMap, continuous_hopfMap⟩

/-- A chosen point in the Hopf fiber over `x`. -/
def hopfBase (x : SphereTwo) : SphereThree :=
  Classical.choose (hopfMap_surjective x)

@[simp]
lemma hopfMap_hopfBase (x : SphereTwo) :
    hopfMap (hopfBase x) = x :=
  Classical.choose_spec (hopfMap_surjective x)

/-- The homomorphism on third homotopy groups induced by the concrete Hopf
map, based at a chosen point of the requested fiber. -/
def hopfHomotopyGroupMap (x : SphereTwo) :
    HomotopyGroup.Pi 3 SphereThree (hopfBase x) →*
      HomotopyGroup.Pi 3 SphereTwo x :=
  homotopyGroupMapMulHom hopfContinuousMap (hopfMap_hopfBase x)

/-- Combine the degree classification of the concrete 3-sphere with the
bijectivity furnished by the Hopf fibration. -/
def pi3SphereTwoMulEquivIntOfHopf
    (x : SphereTwo)
    (sphereDegree :
      HomotopyGroup.Pi 3 SphereThree (hopfBase x) ≃* Multiplicative ℤ)
    (hopfIsomorphism : Function.Bijective (hopfHomotopyGroupMap x)) :
    HomotopyGroup.Pi 3 SphereTwo x ≃* Multiplicative ℤ :=
  (MulEquiv.ofBijective (hopfHomotopyGroupMap x)
    hopfIsomorphism).symm.trans sphereDegree

/-- Transfer the standard real-sphere degree classification to the complex
3-sphere model used by the Hopf map. -/
def pi3ComplexSphereMulEquivIntOfRealDegree
    (z : SphereThree)
    (realSphereDegree :
      HomotopyGroup.Pi 3 SphereThreeReal
          (sphereThreeHomeomorphReal z) ≃* Multiplicative ℤ) :
    HomotopyGroup.Pi 3 SphereThree z ≃* Multiplicative ℤ :=
  (homotopyGroupMulEquivOfHomeomorph
    (N := Fin 3) sphereThreeHomeomorphReal z).trans realSphereDegree

/-- A degree classification at the north pole classifies the third homotopy
group at every basepoint of the standard real 3-sphere. -/
def pi3RealSphereMulEquivIntOfNorthDegree
    (z : SphereThreeReal)
    (northDegree :
      HomotopyGroup.Pi 3 SphereThreeReal sphereThreeRealNorth ≃*
        Multiplicative ℤ) :
    HomotopyGroup.Pi 3 SphereThreeReal z ≃* Multiplicative ℤ := by
  rw [← sphereThreeRealHomeomorphNorth_apply_self z] at northDegree
  exact
    (homotopyGroupMulEquivOfHomeomorph
      (N := Fin 3) (sphereThreeRealHomeomorphNorth z) z).trans
        northDegree

/-- Transfer a degree classification on compactified real 3-space to the
standard real 3-sphere. -/
def pi3RealSphereMulEquivIntOfCompactifiedDegree
    (compactifiedDegree :
      HomotopyGroup.Pi 3 CompactifiedThreeSpace
          (OnePoint.infty : CompactifiedThreeSpace) ≃*
        Multiplicative ℤ) :
    HomotopyGroup.Pi 3 SphereThreeReal sphereThreeRealNorth ≃*
      Multiplicative ℤ := by
  rw [← compactifiedThreeSpaceHomeomorphNorth_apply_infty]
  exact
    (homotopyGroupMulEquivOfHomeomorph
      (N := Fin 3) compactifiedThreeSpaceHomeomorphNorth
      (OnePoint.infty : CompactifiedThreeSpace)).symm.trans
        compactifiedDegree

/-- The final benchmark equivalence follows from the real 3-sphere degree
classification and the Hopf-induced isomorphism. -/
def pi3SphereTwoMulEquivIntOfRealDegreeAndHopf
    (x : SphereTwo)
    (realSphereDegree :
      HomotopyGroup.Pi 3 SphereThreeReal
          (sphereThreeHomeomorphReal (hopfBase x)) ≃*
        Multiplicative ℤ)
    (hopfIsomorphism : Function.Bijective (hopfHomotopyGroupMap x)) :
    HomotopyGroup.Pi 3 SphereTwo x ≃* Multiplicative ℤ :=
  pi3SphereTwoMulEquivIntOfHopf x
    (pi3ComplexSphereMulEquivIntOfRealDegree
      (hopfBase x) realSphereDegree)
    hopfIsomorphism

/-- It is enough to prove the degree classification once, at the canonical
north pole, together with bijectivity of the Hopf-induced map. -/
def pi3SphereTwoMulEquivIntOfNorthDegreeAndHopf
    (x : SphereTwo)
    (northDegree :
      HomotopyGroup.Pi 3 SphereThreeReal sphereThreeRealNorth ≃*
        Multiplicative ℤ)
    (hopfIsomorphism : Function.Bijective (hopfHomotopyGroupMap x)) :
    HomotopyGroup.Pi 3 SphereTwo x ≃* Multiplicative ℤ :=
  pi3SphereTwoMulEquivIntOfRealDegreeAndHopf x
    (pi3RealSphereMulEquivIntOfNorthDegree
      (sphereThreeHomeomorphReal (hopfBase x)) northDegree)
    hopfIsomorphism

/-- It is enough to classify based maps of the compactification of `ℝ³`
and prove that the Hopf map induces a bijection on third homotopy groups. -/
def pi3SphereTwoMulEquivIntOfCompactifiedDegreeAndHopf
    (x : SphereTwo)
    (compactifiedDegree :
      HomotopyGroup.Pi 3 CompactifiedThreeSpace
          (OnePoint.infty : CompactifiedThreeSpace) ≃*
        Multiplicative ℤ)
    (hopfIsomorphism : Function.Bijective (hopfHomotopyGroupMap x)) :
    HomotopyGroup.Pi 3 SphereTwo x ≃* Multiplicative ℤ :=
  pi3SphereTwoMulEquivIntOfNorthDegreeAndHopf x
    (pi3RealSphereMulEquivIntOfCompactifiedDegree compactifiedDegree)
    hopfIsomorphism

/-- The diagonal circle action on the concrete 3-sphere. -/
def circleAct (u : Circle) (z : SphereThree) : SphereThree := by
  refine ⟨u • (z : EuclideanSpace ℂ (Fin 2)), ?_⟩
  change dist (u • (z : EuclideanSpace ℂ (Fin 2))) 0 = 1
  rw [dist_zero_right, Circle.norm_smul]
  rw [← dist_zero_right]
  exact z.property

@[simp]
lemma circleAct_one (z : SphereThree) : circleAct 1 z = z := by
  apply Subtype.ext
  simp [circleAct]

@[simp]
lemma circleAct_mul (u v : Circle) (z : SphereThree) :
    circleAct (u * v) z = circleAct u (circleAct v z) := by
  apply Subtype.ext
  simp [circleAct, mul_smul]

lemma continuous_circleAct :
    Continuous fun p : Circle × SphereThree => circleAct p.1 p.2 :=
  (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _

lemma hopfMapRaw_circle_smul (u : Circle)
    (z : EuclideanSpace ℂ (Fin 2)) :
    hopfMapRaw (u • z) = hopfMapRaw z := by
  have hu : (u : ℂ) * conj (u : ℂ) = 1 := by
    rw [Complex.mul_conj]
    exact_mod_cast Circle.normSq_coe u
  have hprod :
      (u • z) 0 * conj ((u • z) 1) =
        z 0 * conj (z 1) := by
    change ((u : ℂ) * z 0) * conj ((u : ℂ) * z 1) =
      z 0 * conj (z 1)
    rw [map_mul]
    calc
      ((u : ℂ) * z 0) * (conj (u : ℂ) * conj (z 1)) =
          ((u : ℂ) * conj (u : ℂ)) * (z 0 * conj (z 1)) := by
            ring
      _ = z 0 * conj (z 1) := by rw [hu, one_mul]
  ext i
  fin_cases i
  · change
      2 * (((u • z) 0 * conj ((u • z) 1)).re) =
        2 * ((z 0 * conj (z 1)).re)
    exact congrArg (fun c : ℂ => 2 * c.re) hprod
  · change
      2 * (((u • z) 0 * conj ((u • z) 1)).im) =
        2 * ((z 0 * conj (z 1)).im)
    exact congrArg (fun c : ℂ => 2 * c.im) hprod
  · change
      Complex.normSq ((u • z) 0) - Complex.normSq ((u • z) 1) =
        Complex.normSq (z 0) - Complex.normSq (z 1)
    simp [Circle.smul_def, smul_eq_mul, Complex.normSq_mul]

lemma hopfMap_circleAct (u : Circle) (z : SphereThree) :
    hopfMap (circleAct u z) = hopfMap z := by
  apply Subtype.ext
  exact hopfMapRaw_circle_smul u z

lemma normSq_eq_of_hopfMap_eq {z w : SphereThree}
    (h : hopfMap z = hopfMap w) :
    Complex.normSq (z.1 0) = Complex.normSq (w.1 0) ∧
      Complex.normSq (z.1 1) = Complex.normSq (w.1 1) := by
  have hraw : hopfMapRaw z = hopfMapRaw w :=
    congrArg Subtype.val h
  have hdiff := (hopfMapRaw_eq_iff.mp hraw).2
  have hz := sphereThree_normSq_add z
  have hw := sphereThree_normSq_add w
  constructor <;> linarith

lemma norm_eq_of_normSq_eq {z w : ℂ}
    (h : Complex.normSq z = Complex.normSq w) :
    ‖z‖ = ‖w‖ := by
  have hsquare : ‖z‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    exact h
  nlinarith [norm_nonneg z, norm_nonneg w]

/-- The unique phase taking a nonzero complex number `z` to another number
`w` of the same norm. -/
def phaseQuotient (w z : ℂ) (hz : z ≠ 0) (hnorm : ‖w‖ = ‖z‖) :
    Circle := by
  refine ⟨w / z, ?_⟩
  change w / z ∈ Metric.sphere (0 : ℂ) 1
  rw [mem_sphere_zero_iff_norm, norm_div, hnorm,
    div_self (norm_ne_zero_iff.mpr hz)]

lemma phaseQuotient_mul (w z : ℂ) (hz : z ≠ 0)
    (hnorm : ‖w‖ = ‖z‖) :
    (phaseQuotient w z hz hnorm : ℂ) * z = w :=
  div_mul_cancel₀ w hz

/-- The fibers of the polynomial Hopf map are precisely orbits of the
diagonal circle action. -/
lemma exists_circleAct_eq_of_hopfMap_eq {z w : SphereThree}
    (h : hopfMap z = hopfMap w) :
    ∃ u : Circle, circleAct u z = w := by
  have hraw : hopfMapRaw z = hopfMapRaw w :=
    congrArg Subtype.val h
  have hprod := (hopfMapRaw_eq_iff.mp hraw).1
  have hnorm := normSq_eq_of_hopfMap_eq h
  by_cases hz0 : z.1 0 = 0
  · have hw0 : w.1 0 = 0 := by
      apply Complex.normSq_eq_zero.mp
      rw [← hnorm.1, hz0, map_zero]
    have hz1 : z.1 1 ≠ 0 := by
      intro hz1
      have hzsum := sphereThree_normSq_add z
      simp only [hz0, hz1, map_zero, zero_add] at hzsum
      norm_num at hzsum
    have hnorm1 : ‖w.1 1‖ = ‖z.1 1‖ :=
      (norm_eq_of_normSq_eq hnorm.2).symm
    let u := phaseQuotient (w.1 1) (z.1 1) hz1 hnorm1
    have hu0 : (u : ℂ) * z.1 0 = w.1 0 := by rw [hz0, hw0, mul_zero]
    have hu1 : (u : ℂ) * z.1 1 = w.1 1 :=
      phaseQuotient_mul (w.1 1) (z.1 1) hz1 hnorm1
    refine ⟨u, ?_⟩
    apply Subtype.ext
    ext i
    fin_cases i
    · change (u : ℂ) * z.1 0 = w.1 0
      exact hu0
    · change (u : ℂ) * z.1 1 = w.1 1
      exact hu1
  · have hnorm0 : ‖w.1 0‖ = ‖z.1 0‖ :=
      (norm_eq_of_normSq_eq hnorm.1).symm
    let u := phaseQuotient (w.1 0) (z.1 0) hz0 hnorm0
    have hu0 : (u : ℂ) * z.1 0 = w.1 0 :=
      phaseQuotient_mul (w.1 0) (z.1 0) hz0 hnorm0
    have hu1 : (u : ℂ) * z.1 1 = w.1 1 := by
      by_cases hz1 : z.1 1 = 0
      · have hw1 : w.1 1 = 0 := by
          apply Complex.normSq_eq_zero.mp
          rw [← hnorm.2, hz1, map_zero]
        rw [hz1, hw1, mul_zero]
      · have hconj : conj (z.1 1) ≠ 0 := by simp [hz1]
        have hcross : w.1 0 * z.1 1 = w.1 1 * z.1 0 := by
          apply mul_right_cancel₀ hconj
          calc
            (w.1 0 * z.1 1) * conj (z.1 1) =
                w.1 0 * (z.1 1 * conj (z.1 1)) := by ring
            _ = w.1 0 * Complex.normSq (z.1 1) := by
              rw [Complex.mul_conj]
            _ = w.1 0 * Complex.normSq (w.1 1) := by rw [hnorm.2]
            _ = w.1 0 * (w.1 1 * conj (w.1 1)) := by
              rw [Complex.mul_conj]
            _ = w.1 1 * (w.1 0 * conj (w.1 1)) := by ring
            _ = w.1 1 * (z.1 0 * conj (z.1 1)) := by rw [hprod]
            _ = (w.1 1 * z.1 0) * conj (z.1 1) := by ring
        change (w.1 0 / z.1 0) * z.1 1 = w.1 1
        rw [div_mul_eq_mul_div₀]
        exact (div_eq_iff hz0).2 hcross
    refine ⟨u, ?_⟩
    apply Subtype.ext
    ext i
    fin_cases i
    · change (u : ℂ) * z.1 0 = w.1 0
      exact hu0
    · change (u : ℂ) * z.1 1 = w.1 1
      exact hu1

/-- No nontrivial phase fixes a point of the unit 3-sphere. -/
lemma circleAct_injective (z : SphereThree) :
    Function.Injective fun u : Circle => circleAct u z := by
  intro u v huv
  have hcoord : z.1 0 ≠ 0 ∨ z.1 1 ≠ 0 := by
    by_contra h
    push Not at h
    have hzsum := sphereThree_normSq_add z
    simp only [h.1, h.2, map_zero, zero_add] at hzsum
    norm_num at hzsum
  rcases hcoord with hz0 | hz1
  · apply Circle.ext
    apply mul_right_cancel₀ hz0
    have hval := congrArg Subtype.val huv
    have hzero :=
      congrArg (fun q : EuclideanSpace ℂ (Fin 2) => q 0) hval
    simpa [circleAct, Circle.smul_def, smul_eq_mul] using hzero
  · apply Circle.ext
    apply mul_right_cancel₀ hz1
    have hval := congrArg Subtype.val huv
    have hone :=
      congrArg (fun q : EuclideanSpace ℂ (Fin 2) => q 1) hval
    simpa [circleAct, Circle.smul_def, smul_eq_mul] using hone

abbrev HopfFiber (z : SphereThree) :=
  {w : SphereThree // hopfMap w = hopfMap z}

/-- An explicit phase coordinate on a Hopf fiber.  The coordinate used is
chosen once from the fixed basepoint `z`, so this phase varies continuously
with the point of the fiber. -/
def hopfFiberPhaseContinuous (z : SphereThree) (w : HopfFiber z) :
    Circle := by
  by_cases hz0 : z.1 0 = 0
  · have hz1 : z.1 1 ≠ 0 := by
      intro hz1
      have hzsum := sphereThree_normSq_add z
      simp only [hz0, hz1, map_zero, zero_add] at hzsum
      norm_num at hzsum
    exact phaseQuotient (w.1.1 1) (z.1 1) hz1
      (norm_eq_of_normSq_eq (normSq_eq_of_hopfMap_eq w.property).2)
  · exact phaseQuotient (w.1.1 0) (z.1 0) hz0
      (norm_eq_of_normSq_eq (normSq_eq_of_hopfMap_eq w.property).1)

/-- The explicit continuous phase carries the fixed fiber basepoint to the
given point. -/
lemma circleAct_hopfFiberPhaseContinuous
    (z : SphereThree) (w : HopfFiber z) :
    circleAct (hopfFiberPhaseContinuous z w) z = w := by
  obtain ⟨u, hu⟩ :=
    exists_circleAct_eq_of_hopfMap_eq w.property.symm
  suffices hopfFiberPhaseContinuous z w = u by simpa [this] using hu
  apply Circle.ext
  by_cases hz0 : z.1 0 = 0
  · have hz1 : z.1 1 ≠ 0 := by
      intro hz1
      have hzsum := sphereThree_normSq_add z
      simp only [hz0, hz1, map_zero, zero_add] at hzsum
      norm_num at hzsum
    apply mul_right_cancel₀ hz1
    have hphase :
        (hopfFiberPhaseContinuous z w : ℂ) * z.1 1 = w.1.1 1 := by
      simpa [hopfFiberPhaseContinuous, hz0] using
        phaseQuotient_mul (w.1.1 1) (z.1 1) hz1
          (norm_eq_of_normSq_eq
            (normSq_eq_of_hopfMap_eq w.property).2)
    have hu' := congrArg
      (fun q : EuclideanSpace ℂ (Fin 2) => q 1)
      (congrArg Subtype.val hu)
    rw [hphase]
    simpa [circleAct, Circle.smul_def, smul_eq_mul] using hu'.symm
  · apply mul_right_cancel₀ hz0
    have hphase :
        (hopfFiberPhaseContinuous z w : ℂ) * z.1 0 = w.1.1 0 := by
      simpa [hopfFiberPhaseContinuous, hz0] using
        phaseQuotient_mul (w.1.1 0) (z.1 0) hz0
          (norm_eq_of_normSq_eq
            (normSq_eq_of_hopfMap_eq w.property).1)
    have hu' := congrArg
      (fun q : EuclideanSpace ℂ (Fin 2) => q 0)
      (congrArg Subtype.val hu)
    rw [hphase]
    simpa [circleAct, Circle.smul_def, smul_eq_mul] using hu'.symm

lemma continuous_hopfFiberPhaseContinuous (z : SphereThree) :
    Continuous (hopfFiberPhaseContinuous z) := by
  unfold hopfFiberPhaseContinuous
  split
  · apply Continuous.subtype_mk
    change Continuous (fun w : HopfFiber z => w.1.1 1 / z.1 1)
    fun_prop
  · apply Continuous.subtype_mk
    change Continuous (fun w : HopfFiber z => w.1.1 0 / z.1 0)
    fun_prop

/-- Every concrete Hopf fiber is homeomorphic to the unit circle. -/
def hopfFiberHomeomorphCircle (z : SphereThree) :
    HopfFiber z ≃ₜ Circle where
  toFun := hopfFiberPhaseContinuous z
  invFun u := ⟨circleAct u z, hopfMap_circleAct u z⟩
  left_inv w := by
    apply Subtype.ext
    exact circleAct_hopfFiberPhaseContinuous z w
  right_inv u := by
    apply circleAct_injective z
    exact circleAct_hopfFiberPhaseContinuous z
      ⟨circleAct u z, hopfMap_circleAct u z⟩
  continuous_toFun := continuous_hopfFiberPhaseContinuous z
  continuous_invFun :=
    (continuous_circleAct.comp
      (continuous_id.prodMk continuous_const)).subtype_mk _

/-- The phase relating a point in a Hopf fiber to its chosen basepoint. -/
def hopfFiberPhase (z : SphereThree) (w : HopfFiber z) : Circle :=
  Classical.choose (exists_circleAct_eq_of_hopfMap_eq w.property.symm)

lemma circleAct_hopfFiberPhase (z : SphereThree) (w : HopfFiber z) :
    circleAct (hopfFiberPhase z w) z = w :=
  Classical.choose_spec (exists_circleAct_eq_of_hopfMap_eq w.property.symm)

/-- Every concrete Hopf fiber is a torsor for the unit circle. -/
def hopfFiberEquivCircle (z : SphereThree) : HopfFiber z ≃ Circle where
  toFun := hopfFiberPhase z
  invFun u := ⟨circleAct u z, hopfMap_circleAct u z⟩
  left_inv w := by
    apply Subtype.ext
    exact circleAct_hopfFiberPhase z w
  right_inv u := by
    apply circleAct_injective z
    exact circleAct_hopfFiberPhase z
      ⟨circleAct u z, hopfMap_circleAct u z⟩

/-- Recast `π₃(S²)` as the fundamental group of the double loop space.
This is the formal reduction used before constructing the Hopf invariant. -/
def pi3SphereTwoMulEquivDoubleLoopFundamentalGroup (x : SphereTwo) :
    HomotopyGroup.Pi 3 SphereTwo x ≃*
      FundamentalGroup (DoubleLoop x) GenLoop.const :=
  homotopyGroupMulEquivFundamentalGroup x (0 : Fin 3)

/-- It remains enough to classify the fundamental group of the double loop
space by the Hopf invariant. -/
def pi3SphereTwoMulEquivIntOfDoubleLoopEquiv (x : SphereTwo)
    (e : FundamentalGroup (DoubleLoop x) GenLoop.const ≃* Multiplicative ℤ) :
    HomotopyGroup.Pi 3 SphereTwo x ≃* Multiplicative ℤ :=
  (pi3SphereTwoMulEquivDoubleLoopFundamentalGroup x).trans e

end Submission.Helpers
