import Submission.CoreCoordinates

open scoped unitInterval

namespace Submission.CircleMapAlgebra

noncomputable section

def mapMul {X : Type*} [TopologicalSpace X]
    (f g : C(X, Circle)) : C(X, Circle) :=
  ⟨fun x => f x * g x, f.continuous.mul g.continuous⟩

def mapInv {X : Type*} [TopologicalSpace X]
    (f : C(X, Circle)) : C(X, Circle) :=
  ⟨fun x => (f x)⁻¹, f.continuous.inv⟩

def mapZPow {X : Type*} [TopologicalSpace X]
    (f : C(X, Circle)) (n : ℤ) : C(X, Circle) :=
  ⟨fun x => f x ^ n, f.continuous.zpow n⟩

def loopMul {x y : Circle} (gamma : Path x x) (delta : Path y y) :
    Path (x * y) (x * y) where
  toFun t := gamma t * delta t
  continuous_toFun := gamma.continuous.mul delta.continuous
  source' := by rw [gamma.source, delta.source]
  target' := by rw [gamma.target, delta.target]

def loopInv {x : Circle} (gamma : Path x x) : Path x⁻¹ x⁻¹ where
  toFun t := (gamma t)⁻¹
  continuous_toFun := gamma.continuous.inv
  source' := by rw [gamma.source]
  target' := by rw [gamma.target]

def loopZPow {x : Circle} (gamma : Path x x) (n : ℤ) : Path (x ^ n) (x ^ n) where
  toFun t := gamma t ^ n
  continuous_toFun := gamma.continuous.zpow n
  source' := by rw [gamma.source]
  target' := by rw [gamma.target]

theorem windingReal_loopMul {x y : Circle} (gamma : Path x x) (delta : Path y y) :
    CircleWinding.windingReal (loopMul gamma delta) =
      CircleWinding.windingReal gamma + CircleWinding.windingReal delta := by
  let candidate : C(unitInterval, ℝ) :=
    ⟨fun t => CircleWinding.liftedLoop gamma t + CircleWinding.liftedLoop delta t,
      (CircleWinding.liftedLoop gamma).continuous.add
        (CircleWinding.liftedLoop delta).continuous⟩
  have hlift : candidate = CircleWinding.liftedLoop (loopMul gamma delta) := by
    apply (Circle.isCoveringMap_exp.eq_liftPath_iff' (γ_0 := by simp)).mpr
    constructor
    · funext t
      change Circle.exp
          (CircleWinding.liftedLoop gamma t + CircleWinding.liftedLoop delta t) =
        CircleWinding.normalizeLoop (loopMul gamma delta) t
      rw [Circle.exp_add, CircleWinding.exp_liftedLoop,
        CircleWinding.exp_liftedLoop]
      change (gamma t * x⁻¹) * (delta t * y⁻¹) =
        (gamma t * delta t) * (x * y)⁻¹
      simp only [mul_inv_rev]
      ac_rfl
    · simp [candidate]
  have hend := DFunLike.congr_fun hlift 1
  simpa [candidate, CircleWinding.windingReal] using hend.symm

theorem windingReal_loopInv {x : Circle} (gamma : Path x x) :
    CircleWinding.windingReal (loopInv gamma) =
      -CircleWinding.windingReal gamma := by
  let candidate : C(unitInterval, ℝ) :=
    ⟨fun t => -CircleWinding.liftedLoop gamma t,
      (CircleWinding.liftedLoop gamma).continuous.neg⟩
  have hlift : candidate = CircleWinding.liftedLoop (loopInv gamma) := by
    apply (Circle.isCoveringMap_exp.eq_liftPath_iff' (γ_0 := by simp)).mpr
    constructor
    · funext t
      change Circle.exp (-CircleWinding.liftedLoop gamma t) =
        CircleWinding.normalizeLoop (loopInv gamma) t
      rw [Circle.exp_neg, CircleWinding.exp_liftedLoop]
      change (gamma t * x⁻¹)⁻¹ = (gamma t)⁻¹ * (x⁻¹)⁻¹
      simp only [mul_inv_rev]
      ac_rfl
    · simp [candidate]
  have hend := DFunLike.congr_fun hlift 1
  simpa [candidate, CircleWinding.windingReal] using hend.symm

@[simp] theorem windingReal_cast {x x' : Circle} (gamma : Path x x)
    (hx : x' = x) :
    CircleWinding.windingReal (gamma.cast hx hx) =
      CircleWinding.windingReal gamma := by
  rw [← CircleWinding.pathIncrement_loop,
    CircleWinding.pathIncrement_cast, CircleWinding.pathIncrement_loop]

theorem loopZPow_add_one {x : Circle} (gamma : Path x x) (n : ℤ) :
    loopZPow gamma (n + 1) =
      (loopMul (loopZPow gamma n) gamma).cast
        (zpow_add_one x n) (zpow_add_one x n) := by
  apply Path.ext
  funext t
  exact zpow_add_one (gamma t) n

theorem loopZPow_sub_one {x : Circle} (gamma : Path x x) (n : ℤ) :
    loopZPow gamma (n - 1) =
      (loopMul (loopZPow gamma n) (loopInv gamma)).cast
        (zpow_sub_one x n) (zpow_sub_one x n) := by
  apply Path.ext
  funext t
  exact zpow_sub_one (gamma t) n

theorem windingReal_loopZPow {x : Circle} (gamma : Path x x) (n : ℤ) :
    CircleWinding.windingReal (loopZPow gamma n) =
      (n : ℝ) * CircleWinding.windingReal gamma := by
  induction n using Int.induction_on with
  | zero =>
      have hpath : loopZPow gamma 0 = Path.refl (x ^ (0 : ℤ)) := by
        apply Path.ext
        funext t
        rfl
      calc
        CircleWinding.windingReal (loopZPow gamma 0) =
            CircleWinding.windingReal (Path.refl (x ^ (0 : ℤ))) :=
          congrArg CircleWinding.windingReal hpath
        _ = 0 := CircleWinding.windingReal_refl _
        _ = ((0 : ℤ) : ℝ) * CircleWinding.windingReal gamma := by simp
  | succ n ih =>
      rw [loopZPow_add_one]
      rw [windingReal_cast]
      rw [windingReal_loopMul, ih]
      push_cast
      ring
  | pred n ih =>
      rw [loopZPow_sub_one]
      rw [windingReal_cast]
      rw [windingReal_loopMul, ih, windingReal_loopInv]
      push_cast
      ring

theorem mappedLoop_mapMul {X : Type*} [TopologicalSpace X] {x : X}
    (gamma : Path x x) (f g : C(X, Circle)) :
    gamma.map (mapMul f g).continuous =
      loopMul (gamma.map f.continuous) (gamma.map g.continuous) := by
  apply Path.ext
  rfl

theorem mappedLoop_mapInv {X : Type*} [TopologicalSpace X] {x : X}
    (gamma : Path x x) (f : C(X, Circle)) :
    gamma.map (mapInv f).continuous = loopInv (gamma.map f.continuous) := by
  apply Path.ext
  rfl

theorem mappedLoop_mapZPow {X : Type*} [TopologicalSpace X] {x : X}
    (gamma : Path x x) (f : C(X, Circle)) (n : ℤ) :
    gamma.map (mapZPow f n).continuous = loopZPow (gamma.map f.continuous) n := by
  apply Path.ext
  rfl

theorem windingReal_mapMul {X : Type*} [TopologicalSpace X] {x : X}
    (gamma : Path x x) (f g : C(X, Circle)) :
    CircleWinding.windingReal (gamma.map (mapMul f g).continuous) =
      CircleWinding.windingReal (gamma.map f.continuous) +
        CircleWinding.windingReal (gamma.map g.continuous) := by
  rw [mappedLoop_mapMul]
  exact windingReal_loopMul (gamma.map f.continuous) (gamma.map g.continuous)

theorem windingReal_mapInv {X : Type*} [TopologicalSpace X] {x : X}
    (gamma : Path x x) (f : C(X, Circle)) :
    CircleWinding.windingReal (gamma.map (mapInv f).continuous) =
      -CircleWinding.windingReal (gamma.map f.continuous) := by
  rw [mappedLoop_mapInv]
  exact windingReal_loopInv (gamma.map f.continuous)

theorem windingReal_mapZPow {X : Type*} [TopologicalSpace X] {x : X}
    (gamma : Path x x) (f : C(X, Circle)) (n : ℤ) :
    CircleWinding.windingReal (gamma.map (mapZPow f n).continuous) =
      (n : ℝ) * CircleWinding.windingReal (gamma.map f.continuous) := by
  rw [mappedLoop_mapZPow]
  exact windingReal_loopZPow (gamma.map f.continuous) n

end

end Submission.CircleMapAlgebra
