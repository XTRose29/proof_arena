/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# Forster 21.4 assembled: the period real basis (`exists_periodLattice_realBasis`)

The dissection-free proof of the period-lattice real basis, with the statement EXACTLY as
frozen in the original `Jacobians/PeriodLattice.lean`:

* discreteness (B-4, `truePeriodLattice_isolated_zero`) ⟹ `DiscreteTopology`;
* non-degeneracy (B-3, `span_real_truePeriodLattice_eq_top`) ⟹ `IsZLattice ℝ`;
* Mathlib's ZLattice theory then yields a free `ℤ`-module of rank
  `finrank ℝ ℂ^g = 2g`, whose `ℤ`-basis is an `ℝ`-basis of the ambient space spanning the
  lattice over `ℤ` (`Basis.ofZLatticeBasis` + `ofZLatticeBasis_span`).

This retires the cut-surface/dissection route entirely (Wall B closed).

Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), 21.1 + 21.4 (pp. 166–170);
plan `docs/walls_bc_plan_2026-06-10.md`, phase B-5.
-/
import Submission.PeriodLatticeDiscrete

noncomputable section

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Module

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Discrete topology on the period lattice** (Forster 21.4(b), via the isolated-zero
window of `truePeriodLattice_isolated_zero`). -/
instance : DiscreteTopology (truePeriodLattice X) := by
  obtain ⟨U, hU, hU0⟩ := truePeriodLattice_isolated_zero (X := X)
  obtain ⟨V, hVsub, hVopen, hV0⟩ := mem_nhds_iff.mp hU
  rw [discreteTopology_iff_isOpen_singleton_zero]
  have hset : ({0} : Set (truePeriodLattice X))
      = (Subtype.val : truePeriodLattice X → (Fin (genus X) → ℂ)) ⁻¹' V := by
    ext ⟨v, hv⟩
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · intro h0
      rw [show v = 0 from congrArg Subtype.val h0]
      exact hV0
    · intro hvV
      exact Subtype.ext (hU0 v hv (hVsub hvV))
  rw [hset]
  exact hVopen.preimage continuous_subtype_val

/-- **The period lattice is a full `ℤ`-lattice** (Forster 21.4(c), via the maximum-principle
non-degeneracy `span_real_truePeriodLattice_eq_top`). -/
instance : IsZLattice ℝ (truePeriodLattice X) :=
  ⟨span_real_truePeriodLattice_eq_top⟩

/-- **Existence of a period ℝ-basis** — the *single* classical input behind the
Jacobian-as-complex-torus structure.  The period lattice is generated, as a `ℤ`-module, by
a **real basis** of `ℂ^(genus X) ≅ ℝ^(2·genus X)`.

PROVEN dissection-free (Forster 21.4): discreteness (B-4) + non-degeneracy (B-3) make the
lattice a `ZLattice`, and Mathlib's ZLattice theory produces the basis. -/
theorem exists_periodLattice_realBasis :
    ∃ b : Module.Basis (Fin (2 * genus X)) ℝ (Fin (genus X) → ℂ),
      truePeriodLattice X = Submodule.span ℤ (Set.range ⇑b) := by
  classical
  haveI hfree : Module.Free ℤ (truePeriodLattice X) :=
    ZLattice.module_free ℝ (truePeriodLattice X)
  haveI hfin : Module.Finite ℤ (truePeriodLattice X) :=
    ZLattice.module_finite ℝ (truePeriodLattice X)
  have hrank : Module.finrank ℤ (truePeriodLattice X) = 2 * genus X := by
    rw [ZLattice.rank ℝ, finrank_real_of_complex, Module.finrank_pi, Fintype.card_fin]
  have hcard : Fintype.card
      (Module.Free.ChooseBasisIndex ℤ (truePeriodLattice X)) = 2 * genus X := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, hrank]
  set e := Fintype.equivFinOfCardEq hcard with he
  set b₀ := (Module.Free.chooseBasis ℤ (truePeriodLattice X)).reindex e with hb₀
  refine ⟨b₀.ofZLatticeBasis ℝ, ?_⟩
  exact (b₀.ofZLatticeBasis_span ℝ).symm

end Jacobians
