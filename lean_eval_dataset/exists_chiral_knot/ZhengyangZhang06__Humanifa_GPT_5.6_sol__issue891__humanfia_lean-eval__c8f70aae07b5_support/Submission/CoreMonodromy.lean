import Submission.CoreEdges

open Complex
open scoped unitInterval

namespace Submission.CoreMonodromy

noncomputable section

def flip (i : Fin 2) : Fin 2 := ![1, 0] i

def next (j : Fin 3) : Fin 3 :=
  if j = 0 then 1 else if j = 1 then 2 else 0

@[simp] theorem next_zero : next 0 = 1 := by simp [next]

@[simp] theorem next_one : next 1 = 2 := by simp [next]

@[simp] theorem next_two : next 2 = 0 := by simp [next]

@[simp] theorem flip_flip (i : Fin 2) : flip (flip i) = i := by
  fin_cases i <;> rfl

@[simp] theorem next_next_next (j : Fin 3) : next (next (next j)) = j := by
  fin_cases j <;> rfl

theorem rotate_z (z : ℂ) :
    Milnor.rotate 3 (Real.pi / 3) z = -z := by
  unfold Milnor.rotate
  have harg :
      (((3 : ℕ) : ℝ) * (Real.pi / 3) : ℝ) = Real.pi := by ring
  rw [harg]
  rw [Complex.exp_pi_mul_I]
  ring

theorem rotate_w (w : ℂ) :
    Milnor.rotate 2 (Real.pi / 3) w = CoreEdges.wRoot 1 * w := by
  rw [CoreEdges.wRoot_one]
  unfold Milnor.rotate CoreEdges.wGenerator
  have harg : ((2 : ℕ) : ℝ) * (Real.pi / 3) = 2 * Real.pi / 3 := by ring
  rw [harg]

theorem zTerm_monodromy (z : ℂ) :
    RadialSpine.zTerm (Milnor.rotate 3 (Real.pi / 3) z) =
      RadialSpine.zTerm z := by
  rw [rotate_z]
  simp [RadialSpine.zTerm]

theorem radialCube_root_mul (j : Fin 3) (w : ℂ) :
    RadialMilnor.radialCube (CoreEdges.wRoot j * w) =
      RadialMilnor.radialCube w := by
  by_cases hw : w = 0
  · simp [hw]
  · have hroot : CoreEdges.wRoot j ≠ 0 :=
      norm_ne_zero_iff.mp (by rw [CoreEdges.norm_wRoot]; norm_num)
    rw [RadialMilnor.radialCube_of_ne (mul_ne_zero hroot hw),
      RadialMilnor.radialCube_of_ne hw, mul_pow, norm_mul,
      CoreEdges.norm_wRoot, one_mul, CoreEdges.wRoot_cube, one_mul]

theorem wTerm_monodromy (w : ℂ) :
    RadialSpine.wTerm (Milnor.rotate 2 (Real.pi / 3) w) =
      RadialSpine.wTerm w := by
  rw [rotate_w]
  unfold RadialSpine.wTerm
  rw [radialCube_root_mul]

def coreMonodromy (q : RadialCore.Core) : RadialCore.Core :=
  ⟨⟨RadialMilnor.fiberMonodromy q.1.1, by
      change
        (RadialSpine.zTerm (Milnor.rotate 3 (Real.pi / 3) q.1.1.1.1.1)).im = 0 ∧
        (RadialSpine.wTerm (Milnor.rotate 2 (Real.pi / 3) q.1.1.1.1.2)).im = 0
      rw [zTerm_monodromy, wTerm_monodromy]
      exact q.1.2⟩, by
    change
      0 ≤ (RadialSpine.zTerm (Milnor.rotate 3 (Real.pi / 3) q.1.1.1.1.1)).re ∧
      0 ≤ (RadialSpine.wTerm (Milnor.rotate 2 (Real.pi / 3) q.1.1.1.1.2)).re
    rw [zTerm_monodromy, wTerm_monodromy]
    exact q.2⟩

theorem coreMonodromy_continuous : Continuous coreMonodromy := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact RadialMilnor.fiberMonodromyHomeomorph.continuous.comp
    (continuous_subtype_val.comp continuous_subtype_val)

theorem zRoot_flip (i : Fin 2) : CoreEdges.zRoot (flip i) = -CoreEdges.zRoot i := by
  fin_cases i <;> norm_num [flip, CoreEdges.zRoot]

theorem wRoot_next (j : Fin 3) :
    CoreEdges.wRoot (next j) = CoreEdges.wRoot 1 * CoreEdges.wRoot j := by
  rcases j with ⟨j, hj⟩
  interval_cases j
  · simp [next]
  · simp [next, pow_two]
  · rw [show next ⟨2, hj⟩ = 0 by
        apply Fin.ext
        simp [next],
      CoreEdges.wRoot_zero, CoreEdges.wRoot_one]
    have hroot : CoreEdges.wRoot ⟨2, hj⟩ = CoreEdges.wGenerator ^ 2 := rfl
    rw [hroot]
    calc
      1 = CoreEdges.wGenerator ^ 3 := CoreEdges.wGenerator_cube.symm
      _ = CoreEdges.wGenerator * CoreEdges.wGenerator ^ 2 := by ring

theorem edgeZ_flip (i : Fin 2) (u : unitInterval) :
    -CoreEdges.edgeZ i u = CoreEdges.edgeZ (flip i) u := by
  unfold CoreEdges.edgeZ CoreEdges.fromZCoordinate CoreEdges.edgeZCoordinate
  rw [zRoot_flip]
  ring

theorem edgeW_next (j : Fin 3) (u : unitInterval) :
    CoreEdges.wRoot 1 * CoreEdges.edgeW j u =
      CoreEdges.edgeW (next j) u := by
  unfold CoreEdges.edgeW CoreEdges.fromWCoordinate CoreEdges.edgeWCoordinate
  rw [wRoot_next]
  ring

theorem coreMonodromy_edge (i : Fin 2) (j : Fin 3) (u : unitInterval) :
    coreMonodromy (CoreEdges.edge i j u) =
      CoreEdges.edge (flip i) (next j) u := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · change Milnor.rotate 3 (Real.pi / 3) (CoreEdges.edgeZ i u) =
      CoreEdges.edgeZ (flip i) u
    rw [rotate_z, edgeZ_flip]
  · change Milnor.rotate 2 (Real.pi / 3) (CoreEdges.edgeW j u) =
      CoreEdges.edgeW (next j) u
    rw [rotate_w, edgeW_next]

end

end Submission.CoreMonodromy
