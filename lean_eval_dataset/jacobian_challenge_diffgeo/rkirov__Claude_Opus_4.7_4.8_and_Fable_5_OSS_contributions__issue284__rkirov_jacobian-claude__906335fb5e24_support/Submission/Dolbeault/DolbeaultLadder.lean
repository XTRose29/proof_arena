/-
  Dolbeault ladder — the Čech finiteness headline (light scaffold).

  HISTORICAL NOTE: this file used to carry the whole Čech ladder to `exists_riemannRoch_divisor`
  (`arithmeticGenus_eq_genus`, `serre_h1_eq`, `riemannRoch_equality_of_ladder`), gated on the
  never-discharged §17 instantiation `exists_serreDualityData`.  That route is SUPERSEDED:
  Riemann–Roch is now proven unconditionally by the Miranda Laurent-tail route
  (`LaurentTail.exists_riemannRoch_divisor_unconditional`, re-pointed in `RiemannRoch.lean`),
  and the gated leaves were pruned along with their `sorry`.

  What remains here is the PROVEN, load-bearing finiteness headline:
    * `finiteDimensional_cechH1` — G3b finiteness (Forster 14.9): disk-Montel +
      Schwartz/Riesz–Schauder (`finiteDimensional_cechH1_wired`).
  The Čech tower below (cohomological RR / skyscraper LES / `h0Dim_eq_lDim`, imported here) stays:
  it feeds the Riemann inequality and `exists_nonconstant_meromorphic`, which the tail route's
  pole-budget bound consumes.
-/
import Submission.Dolbeault.CechH0
import Submission.Dolbeault.CohomologicalRR
import Submission.Dolbeault.SerreDualityPairing
import Submission.Dolbeault.CechFinitenessWiring

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **G3b — finiteness (Forster Thm 14.9).** `H¹(𝔘, 𝒪_D)` is finite-dimensional. Engine: the cochain
restriction between a cover and a relatively-compact shrinking is *compact* (disk-Montel: Mathlib
`Analysis.Complex.LocallyUniformLimit` + Arzelà–Ascoli), and a compact perturbation has finite-codim
image (Schwartz / Riesz–Schauder, via Mathlib `IsCompactOperator` + `RieszLemma`). **Deep analytic
leaf.** -/
theorem finiteDimensional_cechH1 (𝔘 : FiniteCover X) (D : Divisor X) :
    FiniteDimensional ℂ (𝔘.cechH1 D) :=
  finiteDimensional_cechH1_wired 𝔘 D

/- **Cohomological Riemann–Roch (χ-additivity, Forster §16)** is now PROVEN in `CohomologicalRR.lean`
(imported above) modulo the single isolated kernel `exists_skyscraperLES` (the skyscraper-SES connecting
map + `skyDim=1`); base `h⁰(0)=1` + divisor induction + the 6-term alternating-sum crank are axiom-clean.
So `cohomological_riemannRoch` is in scope here via the import — no longer an unproved leaf of this file. -/

/- The former gated leaves `arithmeticGenus_eq_genus`, `serre_h1_eq` and the composition
`riemannRoch_equality_of_ladder` (all transitively dependent on the pruned `sorry`
`exists_serreDualityData`) were removed — see the header note.  Their content is delivered,
genus-uniformly and sorry-free, by `LaurentTail.h1TailDim_zero_eq_genus_unconditional`,
`LaurentTail.h1TailDim_eq_lDim_pairCanonical_sub`, and
`LaurentTail.exists_riemannRoch_divisor_unconditional` (on the Mittag-Leffler tail `H¹`). -/

end Jacobians.Dolbeault
