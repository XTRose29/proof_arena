import Submission.RadialCore

open Complex
open scoped unitInterval

namespace Submission.CoreEdges

noncomputable section

def zRoot : Fin 2 → ℂ := ![1, -1]

def wGenerator : ℂ :=
  Complex.exp (((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I)

def wRoot (j : Fin 3) : ℂ := wGenerator ^ (j : ℕ)

@[simp] theorem wRoot_zero : wRoot 0 = 1 := by norm_num [wRoot]

@[simp] theorem wRoot_one : wRoot 1 = wGenerator := by norm_num [wRoot]

@[simp] theorem wRoot_two : wRoot 2 = wGenerator ^ 2 := by norm_num [wRoot]

@[simp] theorem zRoot_sq (i : Fin 2) : zRoot i ^ 2 = 1 := by
  fin_cases i <;> norm_num [zRoot]

@[simp] theorem norm_zRoot (i : Fin 2) : ‖zRoot i‖ = 1 := by
  fin_cases i <;> norm_num [zRoot]

@[simp] theorem norm_wGenerator : ‖wGenerator‖ = 1 := by
  unfold wGenerator
  exact Complex.norm_exp_ofReal_mul_I _

@[simp] theorem wGenerator_cube : wGenerator ^ 3 = 1 := by
  unfold wGenerator
  rw [← Complex.exp_nat_mul]
  have harg :
      ((3 : ℕ) : ℂ) *
          (((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I) =
        2 * (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_two_pi_mul_I]

theorem wGenerator_isPrimitiveRoot : IsPrimitiveRoot wGenerator 3 := by
  have h := Complex.isPrimitiveRoot_exp 3 (by norm_num)
  convert h using 1
  unfold wGenerator
  congr 1
  push_cast
  ring

@[simp] theorem norm_wRoot (j : Fin 3) : ‖wRoot j‖ = 1 := by
  rw [wRoot, norm_pow, norm_wGenerator, one_pow]

@[simp] theorem wRoot_cube (j : Fin 3) : wRoot j ^ 3 = 1 := by
  rw [wRoot, ← pow_mul, Nat.mul_comm, pow_mul, wGenerator_cube, one_pow]

theorem exists_wRoot_of_cube_eq_one {w : ℂ} (hw : w ^ 3 = 1) :
    ∃ j : Fin 3, wRoot j = w := by
  obtain ⟨j, hj, hpow⟩ := wGenerator_isPrimitiveRoot.eq_pow_of_pow_eq_one hw
  exact ⟨⟨j, hj⟩, hpow⟩

@[simp] theorem radialCube_wRoot (j : Fin 3) :
    RadialMilnor.radialCube (wRoot j) = 1 := by
  have hj : wRoot j ≠ 0 := norm_ne_zero_iff.mp (by rw [norm_wRoot]; norm_num)
  rw [RadialMilnor.radialCube_of_ne hj, norm_wRoot, wRoot_cube]
  norm_num

def fromZCoordinate (z : ℂ) : ℂ :=
  Complex.exp (-(((Real.pi / 4 : ℝ) : ℂ) * Complex.I)) * z

def fromWCoordinate (w : ℂ) : ℂ :=
  Complex.exp (-(((Real.pi / 6 : ℝ) : ℂ) * Complex.I)) * w

@[simp] theorem zCoordinate_fromZCoordinate (z : ℂ) :
    RadialCore.zCoordinate (fromZCoordinate z) = z := by
  unfold RadialCore.zCoordinate fromZCoordinate
  rw [← mul_assoc, ← Complex.exp_add]
  have harg :
      (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) +
          -(((Real.pi / 4 : ℝ) : ℂ) * Complex.I) = 0 := by ring
  rw [harg]
  simp

@[simp] theorem wCoordinate_fromWCoordinate (w : ℂ) :
    RadialCore.wCoordinate (fromWCoordinate w) = w := by
  unfold RadialCore.wCoordinate fromWCoordinate
  rw [← mul_assoc, ← Complex.exp_add]
  have harg :
      (((Real.pi / 6 : ℝ) : ℂ) * Complex.I) +
          -(((Real.pi / 6 : ℝ) : ℂ) * Complex.I) = 0 := by ring
  rw [harg]
  simp

@[simp] theorem fromZCoordinate_zCoordinate (z : ℂ) :
    fromZCoordinate (RadialCore.zCoordinate z) = z := by
  unfold RadialCore.zCoordinate fromZCoordinate
  rw [← mul_assoc, ← Complex.exp_add]
  have harg :
      -(((Real.pi / 4 : ℝ) : ℂ) * Complex.I) +
          (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) = 0 := by ring
  rw [harg]
  simp

@[simp] theorem fromWCoordinate_wCoordinate (w : ℂ) :
    fromWCoordinate (RadialCore.wCoordinate w) = w := by
  unfold RadialCore.wCoordinate fromWCoordinate
  rw [← mul_assoc, ← Complex.exp_add]
  have harg :
      -(((Real.pi / 6 : ℝ) : ℂ) * Complex.I) +
          (((Real.pi / 6 : ℝ) : ℂ) * Complex.I) = 0 := by ring
  rw [harg]
  simp

theorem norm_fromZCoordinate (z : ℂ) : ‖fromZCoordinate z‖ = ‖z‖ := by
  unfold fromZCoordinate
  rw [norm_mul]
  have hnorm :
      ‖Complex.exp (-(((Real.pi / 4 : ℝ) : ℂ) * Complex.I))‖ = 1 := by
    have hrewrite :
        -(((Real.pi / 4 : ℝ) : ℂ) * Complex.I) =
          (((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [hrewrite, Complex.norm_exp_ofReal_mul_I]
  rw [hnorm, one_mul]

theorem norm_fromWCoordinate (w : ℂ) : ‖fromWCoordinate w‖ = ‖w‖ := by
  unfold fromWCoordinate
  rw [norm_mul]
  have hnorm :
      ‖Complex.exp (-(((Real.pi / 6 : ℝ) : ℂ) * Complex.I))‖ = 1 := by
    have hrewrite :
        -(((Real.pi / 6 : ℝ) : ℂ) * Complex.I) =
          (((-(Real.pi / 6) : ℝ) : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [hrewrite, Complex.norm_exp_ofReal_mul_I]
  rw [hnorm, one_mul]

def edgeZCoordinate (i : Fin 2) (u : unitInterval) : ℂ :=
  (Real.sqrt (1 - (u : ℝ)) : ℂ) * zRoot i

def edgeWCoordinate (j : Fin 3) (u : unitInterval) : ℂ :=
  (Real.sqrt (u : ℝ) : ℂ) * wRoot j

def edgeZ (i : Fin 2) (u : unitInterval) : ℂ :=
  fromZCoordinate (edgeZCoordinate i u)

def edgeW (j : Fin 3) (u : unitInterval) : ℂ :=
  fromWCoordinate (edgeWCoordinate j u)

theorem normSq_edgeZ (i : Fin 2) (u : unitInterval) :
    normSq (edgeZ i u) = 1 - (u : ℝ) := by
  rw [normSq_eq_norm_sq, edgeZ, norm_fromZCoordinate, edgeZCoordinate,
    norm_mul, norm_zRoot, mul_one, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt]
  exact sub_nonneg.mpr u.2.2

theorem normSq_edgeW (j : Fin 3) (u : unitInterval) :
    normSq (edgeW j u) = (u : ℝ) := by
  rw [normSq_eq_norm_sq, edgeW, norm_fromWCoordinate, edgeWCoordinate,
    norm_mul, norm_wRoot, mul_one, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt]
  exact u.2.1

theorem zTerm_edgeZ (i : Fin 2) (u : unitInterval) :
    RadialSpine.zTerm (edgeZ i u) = (16 * (1 - (u : ℝ)) : ℝ) := by
  rw [RadialCore.zTerm_eq_coordinate, edgeZ,
    zCoordinate_fromZCoordinate, edgeZCoordinate, mul_pow, zRoot_sq]
  rw [show ((Real.sqrt (1 - (u : ℝ)) : ℂ) ^ 2) =
      ((1 - (u : ℝ) : ℝ) : ℂ) by
    exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr u.2.2)]
  push_cast
  ring

theorem wTerm_edgeW (j : Fin 3) (u : unitInterval) :
    RadialSpine.wTerm (edgeW j u) = (9 * (u : ℝ) : ℝ) := by
  rw [RadialCore.wTerm_eq_coordinate, edgeW,
    wCoordinate_fromWCoordinate, edgeWCoordinate]
  rw [RadialMilnor.radialCube_smul_of_nonneg _ (Real.sqrt_nonneg _),
    radialCube_wRoot]
  rw [show ((Real.sqrt (u : ℝ) : ℂ) ^ 2) = (((u : ℝ) : ℂ)) by
    exact_mod_cast Real.sq_sqrt u.2.1]
  push_cast
  ring

def edgeSphere (i : Fin 2) (j : Fin 3) (u : unitInterval) :
    RadialMilnor.CSphere :=
  ⟨(edgeZ i u, edgeW j u), by
    rw [normSq_edgeZ, normSq_edgeW]
    ring⟩

def edgeFiber (i : Fin 2) (j : Fin 3) (u : unitInterval) :
    RadialMilnor.Fiber :=
  ⟨edgeSphere i j u, by
    rw [RadialSpine.polynomial_eq_terms]
    change 0 < (RadialSpine.zTerm (edgeZ i u) +
        RadialSpine.wTerm (edgeW j u)).re ∧
      (RadialSpine.zTerm (edgeZ i u) +
        RadialSpine.wTerm (edgeW j u)).im = 0
    rw [zTerm_edgeZ, wTerm_edgeW]
    constructor
    · norm_num
      linarith [u.2.2]
    · simp⟩

def edgeSpine (i : Fin 2) (j : Fin 3) (u : unitInterval) :
    RadialSpine.Spine :=
  ⟨edgeFiber i j u, by
    change (RadialSpine.zTerm (edgeZ i u)).im = 0 ∧
      (RadialSpine.wTerm (edgeW j u)).im = 0
    rw [zTerm_edgeZ, wTerm_edgeW]
    simp⟩

def edge (i : Fin 2) (j : Fin 3) (u : unitInterval) : RadialCore.Core :=
  ⟨edgeSpine i j u, by
    change 0 ≤ (RadialSpine.zTerm (edgeZ i u)).re ∧
      0 ≤ (RadialSpine.wTerm (edgeW j u)).re
    rw [zTerm_edgeZ, wTerm_edgeW]
    constructor
    · exact mul_nonneg (by norm_num) (sub_nonneg.mpr u.2.2)
    · exact mul_nonneg (by norm_num) u.2.1⟩

theorem edge_continuous (i : Fin 2) (j : Fin 3) :
    Continuous (edge i j) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact (by
    unfold edgeZ edgeW edgeZCoordinate edgeWCoordinate
      fromZCoordinate fromWCoordinate
    fun_prop)

theorem edge_parameter (i : Fin 2) (j : Fin 3) (u : unitInterval) :
    normSq (edge i j u).1.1.1.1.2 = (u : ℝ) :=
  normSq_edgeW j u

end

end Submission.CoreEdges
