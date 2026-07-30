import Submission.CoreCycles
import Mathlib.Topology.Homotopy.Lifting

open scoped unitInterval

namespace Submission.CircleWinding

noncomputable section

def normalizeLoop {x : Circle} (gamma : Path x x) : Path (1 : Circle) 1 where
  toFun t := gamma t * x⁻¹
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

def liftedLoop {x : Circle} (gamma : Path x x) : C(unitInterval, ℝ) :=
  Circle.isCoveringMap_exp.liftPath
    (normalizeLoop gamma : C(unitInterval, Circle)) 0 (by simp)

def windingReal {x : Circle} (gamma : Path x x) : ℝ := liftedLoop gamma 1

def normalizePath {x y : Circle} (gamma : Path x y) : Path (1 : Circle) (y * x⁻¹) where
  toFun t := gamma t * x⁻¹
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by rw [gamma.target]

def liftedPath {x y : Circle} (gamma : Path x y) : C(unitInterval, ℝ) :=
  Circle.isCoveringMap_exp.liftPath
    (normalizePath gamma : C(unitInterval, Circle)) 0 (by simp)

def pathIncrement {x y : Circle} (gamma : Path x y) : ℝ := liftedPath gamma 1

@[simp] theorem pathIncrement_cast {x y x' y' : Circle} (gamma : Path x y)
    (hx : x' = x) (hy : y' = y) :
    pathIncrement (gamma.cast hx hy) = pathIncrement gamma := by
  subst x'
  subst y'
  simp

@[simp] theorem pathIncrement_map_cast {X : Type*} [TopologicalSpace X]
    {x y x' y' : X} (gamma : Path x y) (hx : x' = x) (hy : y' = y)
    (f : X → Circle) (hf : Continuous f) :
    pathIncrement ((gamma.cast hx hy).map hf) = pathIncrement (gamma.map hf) := by
  subst x'
  subst y'
  simp

@[simp] theorem liftedPath_zero {x y : Circle} (gamma : Path x y) :
    liftedPath gamma 0 = 0 := by
  exact Circle.isCoveringMap_exp.liftPath_zero
    (normalizePath gamma : C(unitInterval, Circle)) 0 (by simp)

theorem exp_liftedPath {x y : Circle} (gamma : Path x y) (t : unitInterval) :
    Circle.exp (liftedPath gamma t) = normalizePath gamma t := by
  exact congrFun
    (Circle.isCoveringMap_exp.liftPath_lifts
      (normalizePath gamma : C(unitInterval, Circle)) 0 (by simp)) t

@[simp] theorem pathIncrement_loop {x : Circle} (gamma : Path x x) :
    pathIncrement gamma = windingReal gamma := by
  have hlift : liftedPath gamma = liftedLoop gamma := by
    apply (Circle.isCoveringMap_exp.eq_liftPath_iff' (γ_0 := by simp)).mpr
    constructor
    · funext t
      change Circle.exp (liftedPath gamma t) = normalizeLoop gamma t
      rw [exp_liftedPath]
      rfl
    · exact liftedPath_zero gamma
  exact congrArg (fun f : C(unitInterval, ℝ) => f 1) hlift

theorem pathIncrement_trans {x y z : Circle} (gamma : Path x y) (delta : Path y z) :
    pathIncrement (gamma.trans delta) = pathIncrement gamma + pathIncrement delta := by
  let firstLift : Path (0 : ℝ) (pathIncrement gamma) :=
    ⟨liftedPath gamma, liftedPath_zero gamma, rfl⟩
  let secondLift : Path (pathIncrement gamma)
      (pathIncrement gamma + pathIncrement delta) :=
    { toFun := fun t => pathIncrement gamma + liftedPath delta t
      continuous_toFun := continuous_const.add (liftedPath delta).continuous
      source' := by rw [liftedPath_zero]; ring
      target' := rfl }
  let combined : Path (0 : ℝ) (pathIncrement gamma + pathIncrement delta) :=
    firstLift.trans secondLift
  have hprojection :
      Circle.exp ∘ (combined : C(unitInterval, ℝ)) =
        (normalizePath (gamma.trans delta) : C(unitInterval, Circle)) := by
    funext t
    change Circle.exp (combined t) = normalizePath (gamma.trans delta) t
    change Circle.exp ((firstLift.trans secondLift) t) =
      (gamma.trans delta) t * x⁻¹
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs with ht
    · exact exp_liftedPath gamma _
    · change Circle.exp (pathIncrement gamma + liftedPath delta _) = _
      rw [Circle.exp_add, exp_liftedPath]
      have hend : Circle.exp (pathIncrement gamma) = y * x⁻¹ := by
        change Circle.exp (liftedPath gamma 1) = y * x⁻¹
        exact (exp_liftedPath gamma 1).trans (normalizePath gamma).target
      rw [hend]
      change (y * x⁻¹) * (delta _ * y⁻¹) = delta _ * x⁻¹
      calc
        (y * x⁻¹) * (delta _ * y⁻¹) =
            (y * y⁻¹) * (delta _ * x⁻¹) := by ac_rfl
        _ = delta _ * x⁻¹ := by simp
  have hlift :
      (combined : C(unitInterval, ℝ)) = liftedPath (gamma.trans delta) := by
    apply (Circle.isCoveringMap_exp.eq_liftPath_iff' (γ_0 := by simp)).mpr
    exact ⟨hprojection, combined.source⟩
  have hend := DFunLike.congr_fun hlift 1
  simpa [pathIncrement, combined, secondLift, Path.trans_apply] using hend.symm

@[simp] theorem pathIncrement_symm {x y : Circle} (gamma : Path x y) :
    pathIncrement gamma.symm = -pathIncrement gamma := by
  let reverseLift : Path (0 : ℝ) (-pathIncrement gamma) :=
    { toFun := fun t => liftedPath gamma (unitInterval.symm t) - pathIncrement gamma
      continuous_toFun :=
        ((liftedPath gamma).continuous.comp unitInterval.continuous_symm).sub
          continuous_const
      source' := by rw [unitInterval.symm_zero]; simp [pathIncrement]
      target' := by rw [unitInterval.symm_one, liftedPath_zero]; ring }
  have hprojection :
      Circle.exp ∘ (reverseLift : C(unitInterval, ℝ)) =
        (normalizePath gamma.symm : C(unitInterval, Circle)) := by
    funext t
    change Circle.exp (reverseLift t) = normalizePath gamma.symm t
    change Circle.exp
        (liftedPath gamma (unitInterval.symm t) - pathIncrement gamma) =
      gamma (unitInterval.symm t) * y⁻¹
    rw [Circle.exp_sub, exp_liftedPath]
    have hend : Circle.exp (pathIncrement gamma) = y * x⁻¹ := by
      change Circle.exp (liftedPath gamma 1) = y * x⁻¹
      exact (exp_liftedPath gamma 1).trans (normalizePath gamma).target
    rw [hend]
    change (gamma (unitInterval.symm t) * x⁻¹) / (y * x⁻¹) =
      gamma (unitInterval.symm t) * y⁻¹
    rw [div_eq_mul_inv, mul_inv_rev, inv_inv]
    calc
      gamma (unitInterval.symm t) * x⁻¹ * (x * y⁻¹) =
          (x⁻¹ * x) * (gamma (unitInterval.symm t) * y⁻¹) := by ac_rfl
      _ = gamma (unitInterval.symm t) * y⁻¹ := by simp
  have hlift :
      (reverseLift : C(unitInterval, ℝ)) = liftedPath gamma.symm := by
    apply (Circle.isCoveringMap_exp.eq_liftPath_iff' (γ_0 := by simp)).mpr
    exact ⟨hprojection, reverseLift.source⟩
  have hend := DFunLike.congr_fun hlift 1
  simpa [pathIncrement, reverseLift] using hend.symm

theorem windingReal_conjugate {x y : Circle} (gamma : Path x y) (delta : Path y y) :
    windingReal (gamma.trans (delta.trans gamma.symm)) = windingReal delta := by
  rw [← pathIncrement_loop, pathIncrement_trans, pathIncrement_trans,
    pathIncrement_symm, pathIncrement_loop]
  ring

@[simp] theorem liftedLoop_zero {x : Circle} (gamma : Path x x) :
    liftedLoop gamma 0 = 0 := by
  exact Circle.isCoveringMap_exp.liftPath_zero
    (normalizeLoop gamma : C(unitInterval, Circle)) 0 (by simp)

theorem exp_liftedLoop {x : Circle} (gamma : Path x x) (t : unitInterval) :
    Circle.exp (liftedLoop gamma t) = normalizeLoop gamma t := by
  exact congrFun
    (Circle.isCoveringMap_exp.liftPath_lifts
      (normalizeLoop gamma : C(unitInterval, Circle)) 0 (by simp)) t

theorem exp_windingReal {x : Circle} (gamma : Path x x) :
    Circle.exp (windingReal gamma) = 1 := by
  have h := congrFun
    (Circle.isCoveringMap_exp.liftPath_lifts
      (normalizeLoop gamma : C(unitInterval, Circle)) 0 (by simp)) 1
  simpa [windingReal, liftedLoop] using h

theorem windingReal_eq_int_mul_two_pi {x : Circle} (gamma : Path x x) :
    ∃ n : ℤ, windingReal gamma = n * (2 * Real.pi) :=
  Circle.exp_eq_one.mp (exp_windingReal gamma)

theorem normalizeLoop_refl (x : Circle) :
    normalizeLoop (Path.refl x) = Path.refl (1 : Circle) := by
  ext t
  simp [normalizeLoop]

@[simp] theorem windingReal_refl (x : Circle) :
    windingReal (Path.refl x) = 0 := by
  unfold windingReal liftedLoop
  have hlift :
      Circle.isCoveringMap_exp.liftPath
          (normalizeLoop (Path.refl x) : C(unitInterval, Circle)) 0 (by simp) =
        ContinuousMap.const unitInterval (0 : ℝ) := by
    symm
    apply (Circle.isCoveringMap_exp.eq_liftPath_iff' (γ_0 := by simp)).mpr
    constructor
    · funext t
      simp [normalizeLoop]
    · rfl
  rw [hlift]
  rfl

theorem normalizeLoop_trans {x : Circle} (gamma delta : Path x x) :
    normalizeLoop (gamma.trans delta) =
      (normalizeLoop gamma).trans (normalizeLoop delta) := by
  ext t
  simp [normalizeLoop, Path.trans_apply]

theorem normalizeLoop_symm {x : Circle} (gamma : Path x x) :
    normalizeLoop gamma.symm = (normalizeLoop gamma).symm := by
  ext t
  rfl

theorem windingReal_eq_of_homotopic {x : Circle} {gamma delta : Path x x}
    (h : gamma.Homotopic delta) : windingReal gamma = windingReal delta := by
  rcases h with ⟨H⟩
  let mulInv : C(Circle, Circle) :=
    ⟨fun z => z * x⁻¹, by fun_prop⟩
  have Hcomp := H.compContinuousMap mulInv
  have hgamma : mulInv.comp gamma.toContinuousMap =
      (normalizeLoop gamma).toContinuousMap := by
    ext t
    rfl
  have hdelta : mulInv.comp delta.toContinuousMap =
      (normalizeLoop delta).toContinuousMap := by
    ext t
    rfl
  let Hnorm : (normalizeLoop gamma).Homotopy (normalizeLoop delta) :=
    Hcomp.cast hgamma hdelta
  exact Circle.isCoveringMap_exp.liftPath_apply_one_eq_of_homotopicRel
    ⟨Hnorm⟩ 0 (by simp) (by simp)

theorem windingReal_eq_of_freeHomotopy {x y : Circle}
    {gamma : Path x x} {delta : Path y y}
    (H : (gamma : C(unitInterval, Circle)).Homotopy delta)
    (hloop : ∀ s : unitInterval, H (s, 1) = H (s, 0)) :
    windingReal gamma = windingReal delta := by
  let Hnorm : (normalizeLoop gamma : C(unitInterval, Circle)).Homotopy
      (normalizeLoop delta) :=
    ContinuousMap.Homotopy.mk
      ⟨fun p : unitInterval × unitInterval => H p * (H (p.1, 0))⁻¹, by
        fun_prop⟩
      (by
        intro t
        change H (0, t) * (H (0, 0))⁻¹ = gamma t * x⁻¹
        rw [H.apply_zero t, H.apply_zero 0]
        change gamma t * (gamma 0)⁻¹ = gamma t * x⁻¹
        rw [gamma.source])
      (by
        intro t
        change H (1, t) * (H (1, 0))⁻¹ = delta t * y⁻¹
        rw [H.apply_one t, H.apply_one 0]
        change delta t * (delta 0)⁻¹ = delta t * y⁻¹
        rw [delta.source])
  let Hrel : (normalizeLoop gamma : C(unitInterval, Circle)).HomotopyRel
      (normalizeLoop delta) {0, 1} :=
    { toHomotopy := Hnorm
      prop' := by
        intro s t ht
        rcases ht with (rfl | rfl)
        · change H (s, 0) * (H (s, 0))⁻¹ = normalizeLoop gamma 0
          simp [normalizeLoop]
        · change H (s, 1) * (H (s, 0))⁻¹ = normalizeLoop gamma 1
          rw [hloop]
          simp [normalizeLoop] }
  exact Circle.isCoveringMap_exp.liftPath_apply_one_eq_of_homotopicRel
    ⟨Hrel⟩ 0 (by simp) (by simp)

theorem windingReal_trans {x : Circle} (gamma delta : Path x x) :
    windingReal (gamma.trans delta) = windingReal gamma + windingReal delta := by
  let firstLift : Path (0 : ℝ) (windingReal gamma) :=
    ⟨liftedLoop gamma, liftedLoop_zero gamma, rfl⟩
  let secondLift : Path (windingReal gamma)
      (windingReal gamma + windingReal delta) :=
    { toFun := fun t => windingReal gamma + liftedLoop delta t
      continuous_toFun := continuous_const.add (liftedLoop delta).continuous
      source' := by rw [liftedLoop_zero]; ring
      target' := rfl }
  let combined : Path (0 : ℝ) (windingReal gamma + windingReal delta) :=
    firstLift.trans secondLift
  have hprojection :
      Circle.exp ∘ (combined : C(unitInterval, ℝ)) =
        (normalizeLoop (gamma.trans delta) : C(unitInterval, Circle)) := by
    funext t
    rw [normalizeLoop_trans]
    change Circle.exp ((firstLift.trans secondLift) t) =
      ((normalizeLoop gamma).trans (normalizeLoop delta)) t
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs with ht
    · exact exp_liftedLoop gamma _
    · change Circle.exp (windingReal gamma + liftedLoop delta _) = _
      rw [Circle.exp_add, exp_windingReal, one_mul]
      exact exp_liftedLoop delta _
  have hlift :
      (combined : C(unitInterval, ℝ)) = liftedLoop (gamma.trans delta) := by
    apply (Circle.isCoveringMap_exp.eq_liftPath_iff' (γ_0 := by simp)).mpr
    exact ⟨hprojection, combined.source⟩
  have hend := DFunLike.congr_fun hlift 1
  simpa [windingReal, combined, secondLift, Path.trans_apply] using hend.symm

@[simp] theorem windingReal_symm {x : Circle} (gamma : Path x x) :
    windingReal gamma.symm = -windingReal gamma := by
  let reverseLift : Path (0 : ℝ) (-windingReal gamma) :=
    { toFun := fun t => liftedLoop gamma (unitInterval.symm t) - windingReal gamma
      continuous_toFun :=
        ((liftedLoop gamma).continuous.comp unitInterval.continuous_symm).sub
          continuous_const
      source' := by rw [unitInterval.symm_zero]; simp [windingReal]
      target' := by rw [unitInterval.symm_one, liftedLoop_zero]; ring }
  have hprojection :
      Circle.exp ∘ (reverseLift : C(unitInterval, ℝ)) =
        (normalizeLoop gamma.symm : C(unitInterval, Circle)) := by
    funext t
    rw [normalizeLoop_symm]
    change Circle.exp
        (liftedLoop gamma (unitInterval.symm t) - windingReal gamma) =
      normalizeLoop gamma (unitInterval.symm t)
    rw [Circle.exp_sub, exp_windingReal, div_one]
    exact exp_liftedLoop gamma _
  have hlift :
      (reverseLift : C(unitInterval, ℝ)) = liftedLoop gamma.symm := by
    apply (Circle.isCoveringMap_exp.eq_liftPath_iff' (γ_0 := by simp)).mpr
    exact ⟨hprojection, reverseLift.source⟩
  have hend := DFunLike.congr_fun hlift 1
  simpa [windingReal, reverseLift] using hend.symm

end

end Submission.CircleWinding
