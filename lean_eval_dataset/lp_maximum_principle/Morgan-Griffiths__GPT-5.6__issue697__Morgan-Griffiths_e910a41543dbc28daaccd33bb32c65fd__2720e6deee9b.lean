import Mathlib
import Submission.Helpers
import ChallengeDeps

namespace Submission

namespace SourceDefinitions
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

/-- A **linear program** in standard inequality form on `ℝ^m` with `n`
constraints: maximise `c · x` subject to `A x ≤ b` and `0 ≤ x`. -/
structure LinearProgram (m n : ℕ) where
  /-- Coefficient vector of the objective `c · x`. -/
  c : Fin m → ℝ
  /-- Right-hand side of the inequality constraints `A x ≤ b`. -/
  b : Fin n → ℝ
  /-- Constraint matrix. -/
  A : Matrix (Fin n) (Fin m) ℝ

namespace LinearProgram

variable {m n : ℕ}

/-- The **feasible region** of `lp`: the vectors `x ∈ ℝ^m` with `A x ≤ b` and
`0 ≤ x`, a convex polyhedron in `ℝ^m`. -/
def feasible (lp : LinearProgram m n) : Set (Fin m → ℝ) :=
  {x | lp.A *ᵥ x ≤ lp.b ∧ 0 ≤ x}

/-- The **objective** `f(x) = c · x`. -/
def objective (lp : LinearProgram m n) (x : Fin m → ℝ) : ℝ :=
  lp.c ⬝ᵥ x

end LinearProgram





end ConvexGeometry
end LeanEval
end SourceDefinitions

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



namespace LinearProgram

variable {m n : ℕ}





end LinearProgram

/-- **Maximum principle for linear programming** (§101). A local maximiser of
the LP objective on the feasible region is automatically a global maximiser; and
whenever the objective is non-constant (`c ≠ 0`), the maximiser lies on the
topological frontier of the feasible region. -/
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/
theorem lp_maximum_principle {m n : ℕ} (lp : LinearProgram m n)
    (x : Fin m → ℝ) (_hx : x ∈ lp.feasible)
    (_hlocal : IsLocalMaxOn lp.objective lp.feasible x) :
    IsMaxOn lp.objective lp.feasible x ∧
      (lp.c ≠ 0 → x ∈ frontier lp.feasible) :=
/-ResultProofBegin-/by
  classical
  -- First note that the feasible set is convex.  We verify this componentwise;
  -- this also avoids any choices of presentations of a polyhedron.
  have hconv : Convex ℝ lp.feasible := by
    intro u hu v hv a b ha hb hab
    change (lp.A *ᵥ u ≤ lp.b ∧ 0 ≤ u) at hu
    change (lp.A *ᵥ v ≤ lp.b ∧ 0 ≤ v) at hv
    change lp.A *ᵥ (a • u + b • v) ≤ lp.b ∧ 0 ≤ (a • u + b • v)
    constructor
    · intro i
      calc
        (lp.A *ᵥ (a • u + b • v)) i =
            a * (lp.A *ᵥ u) i + b * (lp.A *ᵥ v) i := by
              simp [Matrix.mulVec_add, Matrix.mulVec_smul]
        _ ≤ a * lp.b i + b * lp.b i := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left (hu.1 i) ha)
                (mul_le_mul_of_nonneg_left (hv.1 i) hb)
        _ = lp.b i := by rw [← add_mul, hab, one_mul]
    · intro i
      have hui : 0 ≤ u i := hu.2 i
      have hvi : 0 ≤ v i := hv.2 i
      change 0 ≤ (a • u + b • v) i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha hui) (mul_nonneg hb hvi)
  -- The objective is a linear map, namely a dot product with the fixed vector.
  let L : (Fin m → ℝ) →ₗ[ℝ] ℝ := (dotProductBilin ℝ ℝ) lp.c
  have hL (z : Fin m → ℝ) : L z = lp.objective z := by
    simp [L, LinearProgram.objective, dotProductBilin_apply_apply]
  have hfun : (fun z : Fin m → ℝ => L z) = lp.objective := by
    funext z
    exact hL z
  have hconc : ConcaveOn ℝ lp.feasible lp.objective := by
    -- replace the function, without unfolding the scalar-action instances
    rw [← hfun]
    exact L.concaveOn hconv
  refine ⟨IsMaxOn.of_isLocalMaxOn_of_concaveOn _hx _hlocal hconc, ?_⟩
  intro hc
  -- A non-zero linear functional cannot have a (usual) local maximum.  At an
  -- interior point the relative local maximum is an ordinary one, and
  -- Fermat's linear version makes the contradiction especially transparent.
  have hxnot : x ∉ interior lp.feasible := by
    intro hxint
    have hsnh : lp.feasible ∈ nhds x :=
      (mem_interior_iff_mem_nhds.mp hxint)
    have hloc : IsLocalMax lp.objective x := _hlocal.isLocalMax hsnh
    let LC : (Fin m → ℝ) →L[ℝ] ℝ :=
      LinearMap.toContinuousLinearMap L
    have hfunC : (fun z : Fin m → ℝ => LC z) = lp.objective := by
      funext z
      -- the continuous version has the same underlying linear map
      exact hL z
    have hd : HasFDerivAt lp.objective LC x := by
      -- a continuous linear map is its own derivative
      rw [← hfunC]
      exact LC.hasFDerivAt
    have hz : LC = 0 := hloc.hasFDerivAt_eq_zero hd
    have hzero : ∀ z : Fin m → ℝ, lp.c ⬝ᵥ z = 0 := by
      intro z
      have hz' : LC z = (0 : (Fin m → ℝ) →L[ℝ] ℝ) z :=
        congrArg (fun q : (Fin m → ℝ) →L[ℝ] ℝ => q z) hz
      simpa [LC, L, dotProductBilin_apply_apply] using hz'
    exact hc (dotProduct_eq_zero lp.c hzero)
  -- Membership in a set always implies membership in its closure.
  exact ⟨subset_closure _hx, hxnot⟩
/-ResultProofEnd-/
/-ResultEnd-/
/-- **Vertex optimality** (§101; the existence content of Dantzig's 1947 simplex
algorithm). Every linear program with a nonempty bounded feasible region admits a
global maximiser that is an extreme point (vertex) of the feasible region. -/
/-ResultBegin-/
theorem simplex_algorithm {m n : ℕ} (lp : LinearProgram m n)
    (_hfeas : lp.feasible.Nonempty) (_hbdd : Bornology.IsBounded lp.feasible) :
    ∃ x ∈ lp.feasible, IsMaxOn lp.objective lp.feasible x ∧
      x ∈ Set.extremePoints ℝ lp.feasible :=
/-ResultProofBegin-/by
  classical
  -- The defining half-spaces are closed, hence so is the feasible set.
  have hmul : Continuous (fun u : Fin m → ℝ => lp.A *ᵥ u) := by
    change Continuous ⇑(lp.A.mulVecLin)
    exact lp.A.mulVecLin.continuous_of_finiteDimensional
  have hAclosed : IsClosed {u : Fin m → ℝ | lp.A *ᵥ u ≤ lp.b} := by
    have hi (i : Fin n) :
        IsClosed {u : Fin m → ℝ | (lp.A *ᵥ u) i ≤ lp.b i} := by
      have hf : Continuous (fun u : Fin m → ℝ => (lp.A *ᵥ u) i) :=
        (continuous_apply i).comp hmul
      change IsClosed
        ((fun u : Fin m → ℝ => (lp.A *ᵥ u) i) ⁻¹' Set.Iic (lp.b i))
      exact IsClosed.preimage hf isClosed_Iic
    have heq : {u : Fin m → ℝ | lp.A *ᵥ u ≤ lp.b} =
        ⋂ i : Fin n, {u : Fin m → ℝ | (lp.A *ᵥ u) i ≤ lp.b i} := by
      ext u
      simp [Pi.le_def]
    rw [heq]
    exact isClosed_iInter hi
  have hnonneg : IsClosed {u : Fin m → ℝ | (0 : Fin m → ℝ) ≤ u} := by
    have hi (i : Fin m) : IsClosed {u : Fin m → ℝ | (0 : ℝ) ≤ u i} := by
      change IsClosed ((fun u : Fin m → ℝ => u i) ⁻¹' Set.Ici (0 : ℝ))
      exact IsClosed.preimage (continuous_apply i) isClosed_Ici
    have heq : {u : Fin m → ℝ | (0 : Fin m → ℝ) ≤ u} =
        ⋂ i : Fin m, {u : Fin m → ℝ | (0 : ℝ) ≤ u i} := by
      ext u
      simp [Pi.le_def]
    rw [heq]
    exact isClosed_iInter hi
  have hclosed : IsClosed lp.feasible := by
    change IsClosed
      ({u : Fin m → ℝ | lp.A *ᵥ u ≤ lp.b} ∩
        {u : Fin m → ℝ | (0 : Fin m → ℝ) ≤ u})
    exact hAclosed.inter hnonneg
  have hcompact : IsCompact lp.feasible :=
    (Metric.isCompact_iff_isClosed_bounded).2 ⟨hclosed, _hbdd⟩

  -- Regard the objective as a continuous linear functional.
  let L : (Fin m → ℝ) →ₗ[ℝ] ℝ := (dotProductBilin ℝ ℝ) lp.c
  let LC : (Fin m → ℝ) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap L
  have hval (u : Fin m → ℝ) : LC u = lp.objective u := by
    simp [LC, L, LinearProgram.objective, dotProductBilin_apply_apply]
  have hfun : (fun u : Fin m → ℝ => LC u) = lp.objective := by
    funext u
    exact hval u

  -- The continuous functional has a largest value on the compact set.
  obtain ⟨z, hzs, hzmax⟩ :=
    hcompact.exists_isMaxOn _hfeas (LC.continuous.continuousOn)
  have hzle : ∀ w ∈ lp.feasible, LC w ≤ LC z := by
    simpa [IsMaxOn, IsMaxFilter] using hzmax

  -- Its fibre of maximizers is an exposed (therefore extreme) compact subset.
  let B : Set (Fin m → ℝ) :=
    {u | u ∈ lp.feasible ∧ ∀ w ∈ lp.feasible, LC w ≤ LC u}
  have hzB : z ∈ B := by
    exact ⟨hzs, hzle⟩
  have hBnonempty : B.Nonempty := ⟨z, hzB⟩
  have hBexp : IsExposed ℝ lp.feasible B := by
    intro _
    exact ⟨LC, rfl⟩
  have hBcomp : IsCompact B := hBexp.isCompact hcompact
  obtain ⟨y, hy⟩ := hBcomp.extremePoints_nonempty hBnonempty
  have hyB : y ∈ B := extremePoints_subset hy
  have hyext : y ∈ Set.extremePoints ℝ lp.feasible :=
    hBexp.isExtreme.extremePoints_subset_extremePoints hy
  refine ⟨y, hyB.1, ?_, hyext⟩
  have hym : IsMaxOn (fun u : Fin m → ℝ => LC u) lp.feasible y := by
    simpa [IsMaxOn, IsMaxFilter] using hyB.2
  -- and translating back changes only the notation for the functional
  rw [← hfun]
  exact hym
/-ResultProofEnd-/
/-ResultEnd-/
end ConvexGeometry
end LeanEval

end Submission
