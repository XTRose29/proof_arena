/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# Riemann–Roch for positive genus (Miranda Ch. VI Thm 3.11 / Forster 16.9)

The Miranda-route assembly, M5: combining

* **RR-I** `riemannRoch_tailForm` (`l(D) − h¹(D) = deg D + 1 − h¹(0)`),
* **Serre duality for the tail `H¹`** `h1TailDim_eq_lDim_canonical_sub` (`h¹(D) = l(K − D)`,
  `K = div ω₀`), and
* **`l(K) = genus`** — the proven §17.4 canonical-form iso (`hKgenus_unconditional`), applied to
  the datum built from a nonzero *holomorphic* `ω₀` (which positive genus supplies),

into the headline equality `l(D) − l(K − D) = deg D + 1 − g` for every divisor `D`.

The only genus-restricted input is the existence of `0 ≠ ω₀ ∈ Ω(X)` — everything else is
genus-uniform.  The genus-0 case runs the same duality in the meromorphic frame `ω₀ = df`
(needs the genus-free residue theorem) and is assembled separately.
-/
import Submission.LaurentTail.TailDualitySurjectiveAssembly
import Submission.Dolbeault.FormRemovableSingularity
import Submission.Dolbeault.OmegaFactorization

open scoped Manifold ContDiff Topology
open Module

set_option linter.unusedSectionVars false

namespace Jacobians.LaurentTail

open Jacobians Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### §1 A holomorphic `ω₀` as a §17.4 canonical-form datum -/

/-- The meromorphic order of (the meromorphic-form image of) a holomorphic 1-form is its
`omegaOrderAt`: both read `meromorphicOrderAt` of the same chart coefficient at the chart
centre. -/
theorem formOrderW_holToMero (ω₀ : HolomorphicOneForms X) (p : X) :
    (holToMero ω₀).formOrderW p = omegaOrderAt ω₀ p := rfl

/-- **A nonzero holomorphic 1-form is a §17.4 canonical-form datum**: `ω₀` qua meromorphic
1-form, together with its zero divisor `canonicalDivisorOf ω₀` (the tail-duality canonical
divisor `K`). -/
noncomputable def canonicalForm17DataOfHolomorphic (ω₀ : HolomorphicOneForms X)
    (hω₀ : ω₀ ≠ 0) : CanonicalForm17Data X where
  ω₀ := holToMero ω₀
  nontrivial := by
    obtain ⟨p⟩ := (inferInstance : Nonempty X)
    exact ⟨p, by rw [formOrderW_holToMero]; exact omegaOrderAt_ne_top ω₀ hω₀ p⟩
  K := canonicalDivisorOf ω₀ hω₀
  order_eq := fun x => by
    rw [formOrderW_holToMero]
    exact (coe_canonicalDivisorOf ω₀ hω₀ x).symm

/-- **`l(K) = genus`** for the tail-duality canonical divisor `K = div ω₀` of a nonzero
holomorphic 1-form (Forster §17.4 at `D = 0`, via the proven unconditional `hKgenus`). -/
theorem lDim_canonicalDivisorOf_eq_genus (ω₀ : HolomorphicOneForms X) (hω₀ : ω₀ ≠ 0) :
    lDim (X := X) (canonicalDivisorOf ω₀ hω₀) = genus X :=
  (canonicalForm17DataOfHolomorphic ω₀ hω₀).hKgenus_unconditional

/-! ### §2 The three-genera identity and Riemann–Roch -/

/-- **`h¹(0) = genus`** (Miranda's "three genera", arithmetic = analytic): Serre duality at
`D = 0` reads `h¹(0) = l(K)`, and `l(K) = genus` by §17.4. -/
theorem h1TailDim_zero_eq_genus (hg : 0 < genus X) : h1TailDim (X := X) 0 = genus X := by
  obtain ⟨ω₀, hω₀⟩ := exists_holomorphicOneForm_ne_zero hg
  rw [h1TailDim_eq_lDim_canonical_sub ω₀ hω₀ 0, sub_zero,
    lDim_canonicalDivisorOf_eq_genus ω₀ hω₀]

/-- **Riemann–Roch, positive genus** (Forster Thm 16.9 / Miranda Ch. VI Thm 3.11): a canonical
divisor `K` with `l(D) − l(K−D) = deg D + 1 − g` for every divisor `D`.  This is the exact
statement shape of `Jacobians.exists_riemannRoch_divisor`, with the `0 < genus` hypothesis. -/
theorem exists_riemannRoch_divisor_of_genus_pos (hg : 0 < genus X) :
    ∃ K : Divisor X, ∀ D : Divisor X,
      (lDim (X := X) D : ℤ) - (lDim (X := X) (K - D) : ℤ)
        = Divisor.deg X D + 1 - (genus X : ℤ) := by
  obtain ⟨ω₀, hω₀⟩ := exists_holomorphicOneForm_ne_zero hg
  refine ⟨canonicalDivisorOf ω₀ hω₀, fun D => ?_⟩
  have hRR := riemannRoch_tailForm (X := X) D
  rw [h1TailDim_eq_lDim_canonical_sub ω₀ hω₀ D, h1TailDim_zero_eq_genus hg] at hRR
  omega

end Jacobians.LaurentTail
