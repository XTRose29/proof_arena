/-
  THE PAIR-FORM RESIDUE THEOREM, genus ≥ 1 (Miranda Ch. VI pp. 186–188; Route M input 2).

  A meromorphic 1-form on the compact Riemann surface `X` is represented as a PAIR `(g₀, h)` of
  meromorphic functions meaning `h·dg₀` (no new form type).  Its residue at `a` is computed in the
  canonical chart: `pairFormResidue g₀ h a = Res_{chart a}((h∘chart⁻¹)·(g₀∘chart⁻¹)′)`.

  **Main theorem** (`residueSum_pairForm_eq_zero`): for `0 < genus X`,

    `∑ a ∈ poles, pairFormResidue g₀ h a = 0`

  whenever the pair integrand is honestly analytic at every chart centre off the finite `poles`.

  Proof = the ω₀-factorization reduction to the PROVEN Gate-A engine
  `SerreResidueTheorem.residueTheorem_unconditional` (`∑Res(ω₀·g) = 0`, ω₀ holomorphic):
  1. `0 < genus` picks `ω₀ ≠ 0` (`exists_holomorphicOneForm_ne_zero`).
  2. `q := dg₀/ω₀` is a global meromorphic function (`derivQuotientFn`,
     `Jacobians/Dolbeault/OmegaFactorization.lean`), so `h·dg₀ = (h·q)·ω₀`.
  3. LOCAL IDENTITY (`pairFormResidue_eq_formFnResidue`): at EVERY point,
     `pairFormResidue g₀ h a = formFnResidue ω₀ ((h·q).toFun) a` — germ equality off the centre
     (chart-coherence of `q` + isolated zeros of `coeffAt ω₀ a`) + `resAt_congr`.
  4. SUM with pole-set enlargement: apply the engine at
     `poles' := poles ∪ (the finite analytic-bad set of h·q)`
     (`MeromorphicFunction.finite_nonAnalyticAt` — the removable-singularity `toFun`-junk points
     must be enlarged into the pole set, NOT just the genuine poles); the extra terms vanish
     because off `poles` the PAIR integrand is analytic (`pairFormResidue_eq_zero_of_analyticAt`).

  The Gate-A chain is consumed read-only.  Everything here is complete and depends on no
  unproved lemma.
-/
import Submission.Dolbeault.OmegaFactorization
import Submission.Dolbeault.SerreResidueRamifiedRealSlitGeometry

open scoped Manifold ContDiff Topology
open Filter

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **The residue of the meromorphic pair-form `h·dg₀` at `a`**, computed in the canonical chart:
the `resAt` of `(h ∘ chart⁻¹)·(g₀ ∘ chart⁻¹)′` at the chart image of `a` (Miranda Ch. VI p. 186:
residues of `f·dg` are chart-independent, so the canonical chart pins the value). -/
noncomputable def pairFormResidue (g₀ h : MeromorphicFunction X) (a : X) : ℂ :=
  resAt (fun z => h.toFun ((chartAt (H := ℂ) a).symm z)
    * deriv (fun w => g₀.toFun ((chartAt (H := ℂ) a).symm w)) z) ((chartAt (H := ℂ) a) a)

/-- **`Res(holo) = 0` for pair-forms**: if the pair integrand is analytic at the chart centre
(no pole of `h·dg₀` at `a`), the residue vanishes. -/
theorem pairFormResidue_eq_zero_of_analyticAt (g₀ h : MeromorphicFunction X) (a : X)
    (ha : AnalyticAt ℂ (fun z => h.toFun ((chartAt (H := ℂ) a).symm z)
      * deriv (fun w => g₀.toFun ((chartAt (H := ℂ) a).symm w)) z) ((chartAt (H := ℂ) a) a)) :
    pairFormResidue g₀ h a = 0 :=
  resAt_eq_zero_of_analyticAt ha

/-- **The local identity `Res_a(h·dg₀) = Res_a((h·q)·ω₀)`** for `q = dg₀/ω₀` — at EVERY point `a`
(no exceptional set!): near the chart centre (off it), `q`'s pullback is the single-chart quotient
(`derivQuotient_eventuallyEq_chart`) and `coeffAt ω₀ a ≠ 0` (isolated zeros, `ω₀ ≠ 0`), so the
`coeffAt` factor cancels and the two `resAt` integrands agree as germs (`resAt_congr`). -/
theorem pairFormResidue_eq_formFnResidue (ω₀ : HolomorphicOneForms X) (hω₀ : ω₀ ≠ 0)
    (g₀ h : MeromorphicFunction X) (a : X) :
    pairFormResidue g₀ h a = formFnResidue ω₀ ((h * derivQuotientFn ω₀ g₀).toFun) a := by
  refine resAt_congr ?_
  have hcoh := derivQuotient_eventuallyEq_chart ω₀ g₀ a
  have hne := coeffAt_eventually_ne_zero ω₀ hω₀ a
  filter_upwards [hcoh, hne] with z hq hC
  simp only [MeromorphicFunction.mul_toFun, Pi.mul_apply, derivQuotientFn_toFun]
  rw [hq]
  set H := h.toFun ((chartAt (H := ℂ) a).symm z) with hH
  set D := deriv (fun w => g₀.toFun ((chartAt (H := ℂ) a).symm w)) z with hD
  set C := coeffAt ω₀ a z with hCdef
  -- `H·D = C·(H·(D/C))` with `C ≠ 0`
  rw [mul_left_comm C H (D / C), mul_div_cancel₀ D hC]

/-- **THE PAIR-FORM RESIDUE THEOREM, genus ≥ 1** (Miranda Ch. VI pp. 186–188): the total residue
of a meromorphic pair-form `h·dg₀` over any finite set containing its poles vanishes,

  `∑ a ∈ poles, pairFormResidue g₀ h a = 0`,

provided the pair integrand is honestly `AnalyticAt` at every chart centre off `poles`.
Reduction to the PROVEN `residueTheorem_unconditional` via the ω₀-factorization
`h·dg₀ = (h·q)·ω₀`, `q = dg₀/ω₀` (`0 < genus X` supplies `ω₀ ≠ 0`); the pole set is enlarged by
the finite analytic-bad set of `h·q`, whose extra terms vanish by the off-`poles` analyticity. -/
theorem residueSum_pairForm_eq_zero (hgenus : 0 < genus X)
    (g₀ h : MeromorphicFunction X) (poles : Finset X)
    (hpoles : ∀ x, x ∉ poles → AnalyticAt ℂ
      (fun z => h.toFun ((chartAt (H := ℂ) x).symm z)
         * deriv (fun w => g₀.toFun ((chartAt (H := ℂ) x).symm w)) z)
      ((chartAt (H := ℂ) x) x)) :
    ∑ a ∈ poles, pairFormResidue g₀ h a = 0 := by
  classical
  obtain ⟨ω₀, hω₀⟩ := exists_holomorphicOneForm_ne_zero hgenus
  set hq : MeromorphicFunction X := h * derivQuotientFn ω₀ g₀ with hhq
  -- enlarge the pole set by `h·q`'s finite analytic-bad set
  set poles' : Finset X := poles ∪ hq.finite_nonAnalyticAt.toFinset with hpolesdef
  have hsub : poles ⊆ poles' := Finset.subset_union_left
  -- the Gate-A engine at `(ω₀, h·q, poles')`
  have hzero : ∑ a ∈ poles', formFnResidue ω₀ hq.toFun a = 0 := by
    refine SerreResidueTheorem.residueTheorem_unconditional ω₀ hq poles' (fun x hx => ?_)
    have hxbad : x ∉ hq.finite_nonAnalyticAt.toFinset := fun hmem =>
      hx (Finset.mem_union_right _ hmem)
    rw [Set.Finite.mem_toFinset] at hxbad
    exact not_not.mp hxbad
  -- every `formFnResidue` term is the corresponding pair residue (local identity)
  have hloc : ∀ a ∈ poles', formFnResidue ω₀ hq.toFun a = pairFormResidue g₀ h a := fun a _ =>
    (pairFormResidue_eq_formFnResidue ω₀ hω₀ g₀ h a).symm
  rw [Finset.sum_congr rfl hloc, ← Finset.sum_sdiff hsub] at hzero
  -- the enlargement terms sit off `poles`, where the pair integrand is analytic: they vanish
  have hextra : ∑ a ∈ poles' \ poles, pairFormResidue g₀ h a = 0 :=
    Finset.sum_eq_zero fun a ha =>
      pairFormResidue_eq_zero_of_analyticAt g₀ h a (hpoles a (Finset.mem_sdiff.mp ha).2)
  rw [hextra, zero_add] at hzero
  exact hzero

/-- **Convenience wrapper for product numerators** (the downstream Mittag–Leffler/Serre-pairing
shape `∑Res(f·h·dg₀) = 0`): the main theorem at the pair `(g₀, f·h)`, with the analyticity
hypothesis stated on the unfolded product integrand. -/
theorem residueSum_pairForm_mul_eq_zero (hgenus : 0 < genus X)
    (g₀ f h : MeromorphicFunction X) (poles : Finset X)
    (hpoles : ∀ x, x ∉ poles → AnalyticAt ℂ
      (fun z => f.toFun ((chartAt (H := ℂ) x).symm z) * h.toFun ((chartAt (H := ℂ) x).symm z)
         * deriv (fun w => g₀.toFun ((chartAt (H := ℂ) x).symm w)) z)
      ((chartAt (H := ℂ) x) x)) :
    ∑ a ∈ poles, pairFormResidue g₀ (f * h) a = 0 := by
  refine residueSum_pairForm_eq_zero hgenus g₀ (f * h) poles (fun x hx => ?_)
  have hfh := hpoles x hx
  simpa only [MeromorphicFunction.mul_toFun, Pi.mul_apply] using hfh

end Jacobians.Dolbeault
