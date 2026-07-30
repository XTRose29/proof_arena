import ChallengeDeps

open LeanEval.Analysis.SobolevMorreyProblem

#check NormedField.toNormedSpace
#check RCLike.toInnerProductSpaceReal
#check RCLike.toInnerProductSpaceReal.toNormedSpace
#check Real.smoothTransition.contDiff
#check NormedSpace.ext
#check NormedAddCommGroup.mk
#check MetricSpace.ext

example :
    Real.normedAddCommGroup =
      NonUnitalNormedRing.toNormedAddCommGroup := by
  rfl

example :
    RCLike.toInnerProductSpaceReal.toNormedSpace =
      (NormedField.toNormedSpace : NormedSpace ℝ ℝ) := by
  rfl

attribute [local instance 10000] NormedField.toNormedSpace

set_option pp.all true in
#check (inferInstance : NormedSpace ℝ ℝ)

example : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition :=
  Real.smoothTransition.contDiff

example {n : ℕ} (x : E n) (i : Fin n) (s : ℝ) :
    (x + s • EuclideanSpace.single i (1 : ℝ)) i = x i + s := by
  simp

example {n : ℕ} (x : E n) (i j : Fin n) (s : ℝ) (hji : j < i) :
    (x + s • EuclideanSpace.single i (1 : ℝ)) j = x j := by
  simp [ne_of_lt hji]

example {n : ℕ} (x : E n) (i j : Fin n) (s : ℝ) (hij : i < j) :
    (x + s • EuclideanSpace.single i (1 : ℝ)) j = x j := by
  simp [ne_of_gt hij]
