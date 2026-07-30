/-
Lean Eval submission for `morley_theorem`.
Produced by the UNICO/NOUS autonomous pipeline (Claude by Anthropic, directed
by Solarys431); independent of all previous solutions. The full development is
in `Submission/Helpers.lean`; this file only transports the benchmark
configuration across the canonical isometry `Plane ≃ ℂ` and applies our
oriented-ray Morley theorem.
-/
import ChallengeDeps
import Submission.Helpers

open LeanEval.Geometry.Morley
open scoped EuclideanGeometry

namespace Submission

theorem morley_theorem (A B C P Q R : Plane)
    (h : IsMorleyConfiguration A B C P Q R) :
    IsEquilateralTriple P Q R := by
  obtain ⟨hnc, hP, hQ, hR, hA1, hA2, hA3, hA4, hB1, hB2, hB3, hB4,
    hC1, hC2, hC3, hC4⟩ := h
  have h' := morley_config_complessa
    (planeToComplex A) (planeToComplex B) (planeToComplex C)
    (planeToComplex P) (planeToComplex Q) (planeToComplex R)
    (planeToComplex_not_collinear hnc)
    (planeToComplex_mem_convexHull hP)
    (planeToComplex_mem_convexHull hQ)
    (planeToComplex_mem_convexHull hR)
    (by rw [planeToComplex_angle]; exact hA1)
    (by rw [planeToComplex_angle, planeToComplex_angle]; exact hA2)
    (by rw [planeToComplex_angle, planeToComplex_angle]; exact hA3)
    (by rw [planeToComplex_angle, planeToComplex_angle]; exact hA4)
    (by rw [planeToComplex_angle]; exact hB1)
    (by rw [planeToComplex_angle, planeToComplex_angle]; exact hB2)
    (by rw [planeToComplex_angle, planeToComplex_angle]; exact hB3)
    (by rw [planeToComplex_angle, planeToComplex_angle]; exact hB4)
    (by rw [planeToComplex_angle]; exact hC1)
    (by rw [planeToComplex_angle, planeToComplex_angle]; exact hC2)
    (by rw [planeToComplex_angle, planeToComplex_angle]; exact hC3)
    (by rw [planeToComplex_angle, planeToComplex_angle]; exact hC4)
  constructor
  · have h1 := h'.1
    rwa [planeToComplex_dist, planeToComplex_dist] at h1
  · have h2 := h'.2
    rwa [planeToComplex_dist, planeToComplex_dist] at h2

end Submission
