import Submission.CircleMapAlgebra

open scoped unitInterval

namespace Submission.CoreMapAlgebra

noncomputable section

def windingInt {x : Circle} (gamma : Path x x) : ℤ :=
  Classical.choose (CircleWinding.windingReal_eq_int_mul_two_pi gamma)

theorem windingReal_eq_windingInt_mul_two_pi {x : Circle} (gamma : Path x x) :
    CircleWinding.windingReal gamma = windingInt gamma * (2 * Real.pi) :=
  Classical.choose_spec (CircleWinding.windingReal_eq_int_mul_two_pi gamma)

theorem windingInt_eq_of_windingReal_eq {x : Circle} (gamma : Path x x)
    (n : ℤ) (h : CircleWinding.windingReal gamma = n * (2 * Real.pi)) :
    windingInt gamma = n := by
  have hspec := windingReal_eq_windingInt_mul_two_pi gamma
  have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hcast : (windingInt gamma : ℝ) = (n : ℝ) := by
    apply mul_right_cancel₀ htwoPi
    linarith
  exact_mod_cast hcast

theorem windingReal_eq_zero_of_lift {X : Type*} [TopologicalSpace X]
    {x : X} (g : C(X, Circle)) (G : C(X, ℝ))
    (hexp : ∀ y, Circle.exp (G y) = g y) (gamma : Path x x) :
    CircleWinding.windingReal (gamma.map g.continuous) = 0 := by
  let candidate : C(unitInterval, ℝ) :=
    ⟨fun t => G (gamma t) - G x,
      (G.continuous.comp gamma.continuous).sub continuous_const⟩
  have hlift : candidate =
      CircleWinding.liftedLoop (gamma.map g.continuous) := by
    apply (Circle.isCoveringMap_exp.eq_liftPath_iff' (γ_0 := by simp)).mpr
    constructor
    · funext t
      change Circle.exp (G (gamma t) - G x) =
        CircleWinding.normalizeLoop (gamma.map g.continuous) t
      rw [Circle.exp_sub, hexp, hexp]
      rfl
    · simp [candidate]
  have hend := DFunLike.congr_fun hlift 1
  change G (gamma 1) - G x =
    CircleWinding.windingReal (gamma.map g.continuous) at hend
  rw [gamma.target] at hend
  linarith

def firstClass (g : C(RadialCore.Core, Circle)) : ℤ :=
  windingInt (CoreCycles.firstCycle.map g.continuous)

def secondClass (g : C(RadialCore.Core, Circle)) : ℤ :=
  windingInt (CoreCycles.secondCycle.map g.continuous)

theorem windingReal_firstClass (g : C(RadialCore.Core, Circle)) :
    CircleWinding.windingReal (CoreCycles.firstCycle.map g.continuous) =
      firstClass g * (2 * Real.pi) :=
  windingReal_eq_windingInt_mul_two_pi _

theorem windingReal_secondClass (g : C(RadialCore.Core, Circle)) :
    CircleWinding.windingReal (CoreCycles.secondCycle.map g.continuous) =
      secondClass g * (2 * Real.pi) :=
  windingReal_eq_windingInt_mul_two_pi _

def residual (g : C(RadialCore.Core, Circle)) : C(RadialCore.Core, Circle) :=
  CircleMapAlgebra.mapMul
    (CircleMapAlgebra.mapMul g
      (CircleMapAlgebra.mapZPow CoreCoordinates.firstCoordinate (-firstClass g)))
    (CircleMapAlgebra.mapZPow CoreCoordinates.secondCoordinate (-secondClass g))

theorem residual_firstCycle (g : C(RadialCore.Core, Circle)) :
    CircleWinding.windingReal
      (CoreCycles.firstCycle.map (residual g).continuous) = 0 := by
  rw [residual, CircleMapAlgebra.windingReal_mapMul,
    CircleMapAlgebra.windingReal_mapMul,
    CircleMapAlgebra.windingReal_mapZPow,
    CircleMapAlgebra.windingReal_mapZPow,
    windingReal_firstClass,
    CoreCoordinates.firstCoordinate_firstCycle,
    CoreCoordinates.secondCoordinate_firstCycle]
  push_cast
  ring

theorem residual_secondCycle (g : C(RadialCore.Core, Circle)) :
    CircleWinding.windingReal
      (CoreCycles.secondCycle.map (residual g).continuous) = 0 := by
  rw [residual, CircleMapAlgebra.windingReal_mapMul,
    CircleMapAlgebra.windingReal_mapMul,
    CircleMapAlgebra.windingReal_mapZPow,
    CircleMapAlgebra.windingReal_mapZPow,
    windingReal_secondClass,
    CoreCoordinates.firstCoordinate_secondCycle,
    CoreCoordinates.secondCoordinate_secondCycle]
  push_cast
  ring

def residualLift (g : C(RadialCore.Core, Circle)) : C(RadialCore.Core, ℝ) :=
  Classical.choose
    (CoreLift.exists_continuous_lift (residual g)
      (residual_firstCycle g) (residual_secondCycle g))

theorem exp_residualLift (g : C(RadialCore.Core, Circle))
    (q : RadialCore.Core) :
    Circle.exp (residualLift g q) = residual g q :=
  Classical.choose_spec
    (CoreLift.exists_continuous_lift (residual g)
      (residual_firstCycle g) (residual_secondCycle g)) q

theorem windingReal_residual (g : C(RadialCore.Core, Circle))
    {q : RadialCore.Core} (gamma : Path q q) :
    CircleWinding.windingReal (gamma.map (residual g).continuous) = 0 :=
  windingReal_eq_zero_of_lift (residual g) (residualLift g)
    (exp_residualLift g) gamma

theorem windingReal_eq_classes (g : C(RadialCore.Core, Circle))
    {q : RadialCore.Core} (gamma : Path q q) :
    CircleWinding.windingReal (gamma.map g.continuous) =
      (firstClass g : ℝ) *
          CircleWinding.windingReal
            (gamma.map CoreCoordinates.firstCoordinate.continuous) +
        (secondClass g : ℝ) *
          CircleWinding.windingReal
            (gamma.map CoreCoordinates.secondCoordinate.continuous) := by
  have hzero := windingReal_residual g gamma
  rw [residual, CircleMapAlgebra.windingReal_mapMul,
    CircleMapAlgebra.windingReal_mapMul,
    CircleMapAlgebra.windingReal_mapZPow,
    CircleMapAlgebra.windingReal_mapZPow] at hzero
  push_cast at hzero
  linarith

end

end Submission.CoreMapAlgebra
