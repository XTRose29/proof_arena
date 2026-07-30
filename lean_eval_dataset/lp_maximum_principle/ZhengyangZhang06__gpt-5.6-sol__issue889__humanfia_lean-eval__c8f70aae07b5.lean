import Mathlib
import ChallengeDeps

namespace Submission

open _root_.LeanEval.ConvexGeometry.LinearProgram
open _root_.LeanEval.ConvexGeometry
open LeanEval
namespace LeanEval
namespace ConvexGeometry

/-!
# Linear programming: maximum principle and vertex optimality

§101 of Oliver Knill's *Some Fundamental Theorems in Mathematics*.

* **Maximum principle** (main): a local maximiser of a linear program's
  objective on the feasible region is automatically a global maximiser, and
  whenever the objective is non-constant (`c ≠ 0`) the maximiser lies on the
  topological frontier of the feasible region.
* **Vertex optimality** (additional, the existence content of Dantzig's simplex
  algorithm): every linear program with a nonempty bounded feasible region
  attains its optimum at an extreme point (vertex) of that region.

The program is the standard inequality form `maximise c · x` subject to
`A x ≤ b` and `0 ≤ x`. mathlib has the convex-geometry primitives used here
(`IsLocalMaxOn`, `IsMaxOn`, `frontier`, `Set.extremePoints`, Krein–Milman) but
neither the LP maximum principle nor the existence of an optimal vertex as named
results.
-/

open Matrix
open Filter
open scoped Topology



namespace LinearProgram

variable {m n : ℕ}

noncomputable def objectiveContinuousLinear (lp : LinearProgram m n) :
    (Fin m → ℝ) →L[ℝ] ℝ :=
  letI : AddCommGroup (Fin m → ℝ) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (Fin m → ℝ) := Pi.normedSpace.toModule
  LinearMap.toContinuousLinearMap (dotProductBilin ℝ ℝ lp.c)

@[simp]
theorem objectiveContinuousLinear_apply (lp : LinearProgram m n) (x : Fin m → ℝ) :
    objectiveContinuousLinear lp x = lp.objective x :=
  rfl

theorem convex_feasible (lp : LinearProgram m n) : Convex ℝ lp.feasible := by
  change Convex ℝ ((lp.A.mulVecLin) ⁻¹' Set.Iic lp.b ∩ Set.Ici 0)
  exact ((convex_Iic lp.b).linear_preimage lp.A.mulVecLin).inter (convex_Ici 0)

theorem isClosed_feasible (lp : LinearProgram m n) : IsClosed lp.feasible := by
  change IsClosed ((lp.A.mulVecLin) ⁻¹' Set.Iic lp.b ∩ Set.Ici 0)
  exact (isClosed_Iic.preimage lp.A.mulVecLin.continuous_of_finiteDimensional).inter isClosed_Ici
end LinearProgram

/-- **Maximum principle for linear programming** (§101). A local maximiser of
the LP objective on the feasible region is automatically a global maximiser; and
whenever the objective is non-constant (`c ≠ 0`), the maximiser lies on the
topological frontier of the feasible region. -/
theorem lp_maximum_principle {m n : ℕ} (lp : LinearProgram m n)
    (x : Fin m → ℝ) (_hx : x ∈ lp.feasible)
    (_hlocal : IsLocalMaxOn lp.objective lp.feasible x) :
    IsMaxOn lp.objective lp.feasible x ∧
      (lp.c ≠ 0 → x ∈ frontier lp.feasible) := by
  classical
  have hmax : IsMaxOn lp.objective lp.feasible x :=
    by
      simpa only [LinearProgram.objectiveContinuousLinear_apply] using
        IsMaxOn.of_isLocalMaxOn_of_concaveOn _hx _hlocal
          ((LinearProgram.objectiveContinuousLinear lp).toLinearMap.concaveOn
            (LinearProgram.convex_feasible lp))
  refine ⟨hmax, fun hc ↦ (mem_frontier_iff_notMem_interior _hx).2 ?_⟩
  intro hxint
  have hline :
      HasLineDerivAt ℝ lp.objective (lp.c ⬝ᵥ lp.c) x lp.c := by
    rw [HasLineDerivAt]
    simp only [LinearProgram.objective, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine HasDerivAt.fun_sum fun i _ ↦ ?_
    simpa [mul_assoc] using
      (((hasDerivAt_const (0 : ℝ) (x i)).add
        ((hasDerivAt_id (0 : ℝ)).mul_const (lp.c i))).const_mul (lp.c i))
  have hstay : ∀ᶠ t : ℝ in 𝓝 0, x + t • lp.c ∈ lp.feasible := by
    apply (show Tendsto (fun t : ℝ ↦ x + t • lp.c) (𝓝 0) (𝓝 x) by
      have hcont : Tendsto (fun t : ℝ ↦ x + t • lp.c) (𝓝 0)
          (𝓝 (x + (0 : ℝ) • lp.c)) :=
        (show Continuous (fun t : ℝ ↦ x + t • lp.c) by fun_prop).continuousAt
      simpa only [zero_smul, add_zero] using hcont)
    exact mem_interior_iff_mem_nhds.mp hxint
  exact hc (dotProduct_self_eq_zero.mp (hmax.hasLineDerivAt_eq_zero hline hstay))

/-- **Vertex optimality** (§101; the existence content of Dantzig's 1947 simplex
algorithm). Every linear program with a nonempty bounded feasible region admits a
global maximiser that is an extreme point (vertex) of the feasible region. -/
theorem simplex_algorithm {m n : ℕ} (lp : LinearProgram m n)
    (_hfeas : lp.feasible.Nonempty) (_hbdd : Bornology.IsBounded lp.feasible) :
    ∃ x ∈ lp.feasible, IsMaxOn lp.objective lp.feasible x ∧
      x ∈ Set.extremePoints ℝ lp.feasible := by
  classical
  let f := LinearProgram.objectiveContinuousLinear lp
  have hcompact : IsCompact lp.feasible :=
    Metric.isCompact_of_isClosed_isBounded (LinearProgram.isClosed_feasible lp) _hbdd
  obtain ⟨z, hz, hzmax⟩ :=
    hcompact.exists_isMaxOn _hfeas f.continuous.continuousOn
  have hzexposed : z ∈ f.toExposed lp.feasible := ⟨hz, hzmax⟩
  have hface : IsExposed ℝ lp.feasible (f.toExposed lp.feasible) :=
    ContinuousLinearMap.toExposed.isExposed
  obtain ⟨x, hx⟩ :=
    (hface.isCompact hcompact).extremePoints_nonempty ⟨z, hzexposed⟩
  have hxmax := extremePoints_subset hx
  refine ⟨x, hxmax.1, ?_, hface.isExtreme.extremePoints_subset_extremePoints hx⟩
  intro y hy
  change lp.objective y ≤ lp.objective x
  simpa only [f, LinearProgram.objectiveContinuousLinear_apply] using hxmax.2 y hy

end ConvexGeometry
end LeanEval

end Submission
