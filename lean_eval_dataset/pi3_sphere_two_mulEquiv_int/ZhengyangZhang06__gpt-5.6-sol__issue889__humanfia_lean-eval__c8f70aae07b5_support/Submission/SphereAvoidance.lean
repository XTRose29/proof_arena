import Mathlib
import Submission.SphereHomotopy

noncomputable section

namespace Submission.SphereAvoidance

open Submission.SphereHomotopy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Two unit vectors that are not antipodal are strictly less than distance
two apart. -/
theorem dist_lt_two_of_ne_neg (u v : UnitSphere (E := E))
    (huv : u ≠ -v) :
    dist u v < 2 := by
  have hu : ‖(u : E)‖ = 1 := norm_coe_unitSphere u
  have hv : ‖(v : E)‖ = 1 := norm_coe_unitSphere v
  have hle : dist (u : E) (v : E) ≤ 2 := by
    calc
      dist (u : E) (v : E) ≤
          dist (u : E) 0 + dist 0 (v : E) :=
        dist_triangle _ _ _
      _ = 2 := by rw [dist_zero_right, dist_zero_left, hu, hv]; norm_num
  by_contra hlt
  have hdist : dist (u : E) (v : E) = 2 :=
    le_antisymm hle (le_of_not_gt hlt)
  have hinner : inner ℝ (u : E) (v : E) = -1 := by
    have hs := norm_sub_sq_real (u : E) (v : E)
    rw [← dist_eq_norm, hdist, hu, hv] at hs
    linarith
  have hneg : (u : E) = -(v : E) :=
    (inner_eq_neg_one_iff_of_norm_eq_one hu hv).mp hinner
  apply huv
  apply Subtype.ext
  simpa using hneg

variable {N : Type*} {x : UnitSphere (E := E)}

/-- A based cubical loop in a unit sphere is null-homotopic whenever it misses
the antipode of its basepoint. -/
theorem homotopic_const_of_avoids_antipode
    (p : GenLoop N (UnitSphere (E := E)) x)
    (hp : ∀ t, p t ≠ -x) :
    GenLoop.Homotopic p GenLoop.const := by
  refine ⟨normalizedLineHomotopyRel p.1
    (@GenLoop.const N (UnitSphere (E := E)) _ x).1
    (fun t => dist_lt_two_of_ne_neg (p t) x (hp t))
    (Cube.boundary N) ?_⟩
  intro t ht
  exact p.property t ht

theorem homotopy_class_eq_const_of_avoids_antipode
    (p : GenLoop N (UnitSphere (E := E)) x)
    (hp : ∀ t, p t ≠ -x) :
    (Quotient.mk' p :
      HomotopyGroup N (UnitSphere (E := E)) x) =
        Quotient.mk' (@GenLoop.const N (UnitSphere (E := E)) _ x) :=
  Quotient.sound (homotopic_const_of_avoids_antipode p hp)

end Submission.SphereAvoidance
