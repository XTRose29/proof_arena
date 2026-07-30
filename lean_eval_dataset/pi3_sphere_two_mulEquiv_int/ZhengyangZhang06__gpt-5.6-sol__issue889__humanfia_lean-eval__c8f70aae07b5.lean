import Mathlib
import Submission.HopfHomotopyLift
import Submission.SphereInfinite

namespace Submission

theorem pi3_sphere_two_mulEquiv_int (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    Nonempty
      (HomotopyGroup.Pi 3 (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) x ≃*
        Multiplicative ℤ) := by
  refine ⟨Helpers.pi3SphereTwoMulEquivIntOfNorthDegreeAndHopf
    x ?_ (HopfHomotopyLift.hopfHomotopyGroupMap_bijective x)⟩
  rw [← SphereGenerator.rotateToBasepoint_canonicalBasepoint
    2 Helpers.sphereThreeRealNorth]
  exact
    (Helpers.homotopyGroupMulEquivOfHomeomorph
      (N := Fin 3)
      (SphereGenerator.rotateToBasepointHomeomorph
        2 Helpers.sphereThreeRealNorth)
      (SphereGenerator.canonicalBasepoint 2)).symm.trans
        SphereInfinite.northMulEquivInt

end Submission
