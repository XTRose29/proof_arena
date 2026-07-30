/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# Abel engine C-1: weak solutions of divisors (Forster §20.1–20.2)

A **weak solution** of a divisor `D` is a function that locally looks like `ψ · z^{D a}` with
`ψ` smooth and nonvanishing — the smooth precursor of a meromorphic function with divisor `D`
(`f` is a meromorphic solution exactly when it is holomorphic on `X_D`, Forster 20.1).

Design (normalized, junk-friendly): the local coordinate is FIXED to the centred chart
coordinate `chartCoord a = chartAt a · − chartAt a a`, and the normal form is imposed on the
whole neighbourhood with `zpow`-junk conventions (`(0:ℂ)^k = 0` for `k ≠ 0`), which
normalizes `toFun` to vanish at both zeros and poles of `D`. With this convention products,
inverses and integer powers of weak solutions are weak solutions with **no**
continuity-extension repair (the structure carries its local units, and the product unit is
the product of units).

Main contents:
* `WeakSolution D` — the data-carrying structure (function + local units);
* `one`, `mul`, `inv`, `pow`, `zpow` — the algebra of weak solutions
  (divisors add/negate/scale);
* `contMDiffAt_toFun` — `toFun` is real-smooth on `X_D = {x | 0 ≤ D x}` (Forster's
  `f ∈ 𝓔(X_D)`);
* `logDbar` — the **global smooth `(0,1)`-datum** `σ_f = d″f/f` (Forster 20.2): smooth
  ACROSS the divisor because locally `d″f/f = d″ψ/ψ`; with `logDbar_mem_zeroOne`,
  `logDbar_mul`, `logDbar_zpow`.

Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), §20.1, §20.2;
plan `docs/walls_bc_plan_2026-06-10.md`, phase C-1 (E1).
-/
import Submission.Abel
import Submission.Dolbeault.DolbeaultComparisonInverse

noncomputable section

-- ℝ/ℂ-module diamond discipline (as in `RealForms`, `DolbeaultH01`, `AbelChains`).
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology
open Set Filter

namespace Jacobians

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The centred chart coordinate -/

/-- The **centred chart coordinate at `a`**: `z_a(x) = chartAt a x − chartAt a a`, a
holomorphic coordinate on the chart source vanishing exactly at `a`. -/
def chartCoord (a : X) : X → ℂ := fun x => (chartAt (H := ℂ) a) x - (chartAt (H := ℂ) a) a

@[simp] theorem chartCoord_self (a : X) : chartCoord a a = 0 := sub_self _

theorem chartCoord_ne_zero {a x : X} (hx : x ∈ (chartAt (H := ℂ) a).source) (hne : x ≠ a) :
    chartCoord a x ≠ 0 := by
  refine sub_ne_zero_of_ne fun heq => hne ?_
  exact (chartAt (H := ℂ) a).injOn hx (mem_chart_source ℂ a) heq

/-- The chart-read of `chartCoord a` in the chart at `a` is the affine map `w − chart a a`,
near any point of the chart target. -/
theorem chartCoord_comp_symm_eventuallyEq {a : X} {w : ℂ}
    (hw : w ∈ (chartAt (H := ℂ) a).target) :
    (chartCoord a ∘ (chartAt (H := ℂ) a).symm) =ᶠ[𝓝 w]
      fun z => z - (chartAt (H := ℂ) a) a := by
  filter_upwards [(chartAt (H := ℂ) a).open_target.mem_nhds hw] with z hz
  show (chartAt (H := ℂ) a) ((chartAt (H := ℂ) a).symm z) - _ = z - _
  rw [(chartAt (H := ℂ) a).right_inv hz]

/-- `chartCoord a` read in the chart at `a` is analytic at any chart point of the source. -/
theorem chartCoord_chart_analyticAt_center {a x : X}
    (hx : x ∈ (chartAt (H := ℂ) a).source) :
    AnalyticAt ℂ (chartCoord a ∘ (chartAt (H := ℂ) a).symm) ((chartAt (H := ℂ) a) x) := by
  have hw : (chartAt (H := ℂ) a) x ∈ (chartAt (H := ℂ) a).target :=
    (chartAt (H := ℂ) a).map_source hx
  rw [analyticAt_congr (chartCoord_comp_symm_eventuallyEq hw)]
  exact analyticAt_id.sub analyticAt_const

/-- **Integer powers of the centred coordinate are chart-analytic** at every `x` in the chart
source with `x ≠ a` (any exponent) or `0 ≤ k` (any point): in the chart at `a`,
`z_a^k` is `(w − chart a a)^k`. -/
theorem chartCoord_zpow_chart_analyticAt {a x : X} (k : ℤ)
    (hx : x ∈ (chartAt (H := ℂ) a).source) (h : x ≠ a ∨ 0 ≤ k) :
    AnalyticAt ℂ ((fun y => chartCoord a y ^ k) ∘ (chartAt (H := ℂ) x).symm)
      ((chartAt (H := ℂ) x) x) := by
  refine Dolbeault.analyticAt_chart_change hx ?_
  have hbase : AnalyticAt ℂ (chartCoord a ∘ (chartAt (H := ℂ) a).symm)
      ((chartAt (H := ℂ) a) x) := chartCoord_chart_analyticAt_center hx
  have hcomp : ((fun y => chartCoord a y ^ k) ∘ (chartAt (H := ℂ) a).symm)
      = fun w => (chartCoord a ∘ (chartAt (H := ℂ) a).symm) w ^ k := rfl
  rw [hcomp]
  rcases h with hne | hk
  · -- nonzero base: `AnalyticAt.zpow`
    refine hbase.zpow ?_
    show chartCoord a ((chartAt (H := ℂ) a).symm ((chartAt (H := ℂ) a) x)) ≠ 0
    rw [(chartAt (H := ℂ) a).left_inv hx]
    exact chartCoord_ne_zero hx hne
  · -- nonnegative exponent: rewrite as a natural power
    have hfun : (fun w => (chartCoord a ∘ (chartAt (H := ℂ) a).symm) w ^ k)
        = fun w => (chartCoord a ∘ (chartAt (H := ℂ) a).symm) w ^ k.toNat := by
      funext w
      rw [← zpow_natCast, Int.toNat_of_nonneg hk]
    rw [hfun]
    exact hbase.pow k.toNat

/-- Real-smoothness of `z_a^k` (under the same hypotheses), via the chart-analytic →
real-`C^∞` bridge. -/
theorem chartCoord_zpow_contMDiffAt {a x : X} (k : ℤ)
    (hx : x ∈ (chartAt (H := ℂ) a).source) (h : x ≠ a ∨ 0 ≤ k) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (fun y => chartCoord a y ^ k) x :=
  Dolbeault.contMDiffAt_real_of_chart_analyticAt (chartCoord_zpow_chart_analyticAt k hx h)

/-! ### `∂̄` kills chart-holomorphic functions -/

/-- **`∂̄` kills chart-analytic functions** (the general form of `holoFn_dbar_eq_zero`): if `h`
read in the chart at `x` is complex-analytic at the chart image, then
`proj01 (mfderiv 𝓘(ℝ,ℂ) h x) = 0`. -/
theorem proj01_mfderiv_eq_zero_of_chart_analyticAt {h : X → ℂ} {x : X}
    (ha : AnalyticAt ℂ (h ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x)) :
    Dolbeault.proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) h x) = 0 := by
  have hmdiff : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) h x :=
    (Dolbeault.contMDiffAt_real_of_chart_analyticAt ha).mdifferentiableAt (by simp)
  have hpull : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) h x
      = fderiv ℝ (fun z => h ((extChartAt 𝓘(ℝ, ℂ) x).symm z)) (extChartAt 𝓘(ℝ, ℂ) x x) := by
    rw [hmdiff.mfderiv, ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ]
    congr 1
  have hCdiff : DifferentiableAt ℂ (fun z => h ((extChartAt 𝓘(ℝ, ℂ) x).symm z))
      (extChartAt 𝓘(ℝ, ℂ) x x) := ha.differentiableAt
  rw [hpull, hCdiff.fderiv_restrictScalars ℝ]
  exact Dolbeault.proj01_restrictScalars_eq_zero _

/-- `∂̄(z_a^k) = 0` at points where `z_a^k` is chart-analytic. -/
theorem proj01_mfderiv_chartCoord_zpow_eq_zero {a x : X} (k : ℤ)
    (hx : x ∈ (chartAt (H := ℂ) a).source) (h : x ≠ a ∨ 0 ≤ k) :
    Dolbeault.proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun y => chartCoord a y ^ k) x) = 0 :=
  proj01_mfderiv_eq_zero_of_chart_analyticAt (chartCoord_zpow_chart_analyticAt k hx h)

/-! ### Weak solutions (Forster 20.1, normalized) -/

/-- **Weak solution of a divisor `D`** (Forster 20.1, normalized): a function `toFun`
together with, at every point `a`, a **local unit** `unit a` on an open chart-source
neighbourhood `nbhd a`, smooth and nonvanishing there, with the normal form

  `toFun = unit a · (z_a)^{D a}`  on `nbhd a`

(`z_a` the centred chart coordinate). The normal form holds on ALL of `nbhd a` with
`zpow`-junk conventions, so `toFun` vanishes at both zeros and poles of `D` and equals
`unit x x` off `supp D`. Forster's `f ∈ 𝓔(X_D)` is the derived `contMDiffAt_toFun`. -/
structure WeakSolution (D : Divisor X) where
  /-- the underlying function -/
  toFun : X → ℂ
  /-- the local-unit neighbourhood at each centre -/
  nbhd : X → Set X
  /-- the local unit at each centre -/
  unit : X → X → ℂ
  isOpen_nbhd : ∀ a, IsOpen (nbhd a)
  mem_nbhd : ∀ a, a ∈ nbhd a
  nbhd_subset : ∀ a, nbhd a ⊆ (chartAt (H := ℂ) a).source
  unit_contMDiffOn : ∀ a, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (unit a) (nbhd a)
  unit_ne_zero : ∀ a, ∀ x ∈ nbhd a, unit a x ≠ 0
  normalForm : ∀ a, ∀ x ∈ nbhd a, toFun x = unit a x * chartCoord a x ^ (D a)

namespace WeakSolution

variable {D D₁ D₂ : Divisor X}

/-- The normal form at the centre: `f x = ψ_x(x) · 0^{D x}`. -/
theorem toFun_eq_unit_center (F : WeakSolution D) (x : X) :
    F.toFun x = F.unit x x * (0 : ℂ) ^ (D x) := by
  have h := F.normalForm x x (F.mem_nbhd x)
  rwa [chartCoord_self] at h

/-- The local unit is smooth at the centre. -/
theorem unit_contMDiffAt (F : WeakSolution D) (a : X) {x : X} (hx : x ∈ F.nbhd a) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (F.unit a) x :=
  (F.unit_contMDiffOn a x hx).contMDiffAt ((F.isOpen_nbhd a).mem_nhds hx)

/-- **The local-unit neighbourhood meets the divisor support only at its centre**: a
forced consistency of the structure (at `x ≠ a` in `nbhd a` the normal form at `a` gives
`f x ≠ 0`, while `D x ≠ 0` would force `f x = 0` by the centre form at `x`). -/
theorem coeff_eq_zero_of_mem_nbhd (F : WeakSolution D) {a x : X} (hx : x ∈ F.nbhd a)
    (hne : x ≠ a) : D x = 0 := by
  by_contra hDx
  have h0 : F.toFun x = 0 := by
    rw [F.toFun_eq_unit_center x, zero_zpow _ hDx, mul_zero]
  have hz : chartCoord a x ≠ 0 := chartCoord_ne_zero (F.nbhd_subset a hx) hne
  exact mul_ne_zero (F.unit_ne_zero a x hx) (zpow_ne_zero _ hz)
    ((F.normalForm a x hx) ▸ h0)

/-- Off the divisor support, `f` equals its local unit: `f x = ψ_x(x) ≠ 0`. -/
theorem toFun_eq_unit_of_coeff_zero (F : WeakSolution D) {x : X} (hD : D x = 0) :
    F.toFun x = F.unit x x := by
  rw [F.toFun_eq_unit_center x, hD, zpow_zero, mul_one]

/-- Off the divisor support, `f` is nonvanishing. -/
theorem toFun_ne_zero_of_coeff_zero (F : WeakSolution D) {x : X} (hD : D x = 0) :
    F.toFun x ≠ 0 := by
  rw [F.toFun_eq_unit_of_coeff_zero hD]
  exact F.unit_ne_zero x x (F.mem_nbhd x)

/-- On the divisor support, `f` vanishes (the `zpow`-junk normalization). -/
theorem toFun_eq_zero_of_coeff_ne_zero (F : WeakSolution D) {x : X} (hD : D x ≠ 0) :
    F.toFun x = 0 := by
  rw [F.toFun_eq_unit_center x, zero_zpow _ hD, mul_zero]

/-- Off the divisor support, `f` agrees with its local unit on a whole neighbourhood. -/
theorem toFun_eventuallyEq_unit (F : WeakSolution D) {x : X} (hD : D x = 0) :
    F.toFun =ᶠ[𝓝 x] F.unit x := by
  filter_upwards [(F.isOpen_nbhd x).mem_nhds (F.mem_nbhd x)] with y hy
  rw [F.normalForm x y hy, hD, zpow_zero, mul_one]

/-- **`f ∈ 𝓔(X_D)`** (Forster 20.1): the weak solution is real-smooth at every point of
`X_D = {x | 0 ≤ D x}`. -/
theorem contMDiffAt_toFun (F : WeakSolution D) {a : X} (ha : 0 ≤ D a) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) F.toFun a := by
  have hzk : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (fun y => chartCoord a y ^ (D a)) a :=
    chartCoord_zpow_contMDiffAt (D a) (F.nbhd_subset a (F.mem_nbhd a)) (Or.inr ha)
  refine ContMDiffAt.congr_of_eventuallyEq ((F.unit_contMDiffAt a (F.mem_nbhd a)).mul hzk) ?_
  filter_upwards [(F.isOpen_nbhd a).mem_nhds (F.mem_nbhd a)] with y hy
  exact F.normalForm a y hy

/-! ### The constant weak solution of `D = 0` -/

/-- The constant function `1` is a weak solution of the zero divisor. -/
def one (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    WeakSolution (0 : Divisor X) where
  toFun := fun _ => 1
  nbhd a := (chartAt (H := ℂ) a).source
  unit _ := fun _ => 1
  isOpen_nbhd a := (chartAt (H := ℂ) a).open_source
  mem_nbhd a := mem_chart_source ℂ a
  nbhd_subset _ := le_refl _
  unit_contMDiffOn _ := contMDiffOn_const
  unit_ne_zero _ _ _ := one_ne_zero
  normalForm a x _ := by
    rw [show ((0 : Divisor X) a) = 0 from rfl, zpow_zero, mul_one]

@[simp] theorem one_toFun (x : X) : (one X).toFun x = 1 := rfl

/-! ### Inversion of ℂ over `𝓘(ℝ,ℂ)` (no `ContMDiffInv₀` instance for the real model) -/

/-- `z ↦ z⁻¹` is real-`C^∞` at any nonzero complex number, over the real model `𝓘(ℝ,ℂ)`. -/
theorem contMDiffAt_inv_complex {c : ℂ} (hc : c ≠ 0) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (fun z : ℂ => z⁻¹) c := by
  rw [contMDiffAt_iff_contDiffAt]
  exact contDiffAt_inv ℝ hc

/-! ### Products (Forster 20.1: `f₁f₂` solves `D₁ + D₂`)

With the `zpow`-normalization no continuity-extension repair is needed: the product weak
solution is DEFINED through its local units (`ψ = ψ₁ψ₂`), and it agrees with the pointwise
product `f₁·f₂` away from the cancellation points (everywhere except where
`D₁ x + D₂ x = 0 ≠ D₁ x`). -/

/-- **Product of weak solutions** (Forster 20.1): solves `D₁ + D₂`. The local-unit
neighbourhood is shrunk to meet the supports only at the centre. -/
def mul (F₁ : WeakSolution D₁) (F₂ : WeakSolution D₂) : WeakSolution (D₁ + D₂) where
  toFun := fun x => F₁.unit x x * F₂.unit x x * (0 : ℂ) ^ (D₁ x + D₂ x)
  nbhd a := (F₁.nbhd a ∩ F₂.nbhd a) ∩
    ((((D₁.support : Set X) ∪ (D₂.support : Set X))) \ {a})ᶜ
  unit a := fun x => F₁.unit a x * F₂.unit a x
  isOpen_nbhd a := by
    refine ((F₁.isOpen_nbhd a).inter (F₂.isOpen_nbhd a)).inter ?_
    have hfin : ((((D₁.support : Set X) ∪ (D₂.support : Set X))) \ {a}).Finite :=
      ((D₁.support.finite_toSet.union D₂.support.finite_toSet)).diff
    exact hfin.isClosed.isOpen_compl
  mem_nbhd a := ⟨⟨F₁.mem_nbhd a, F₂.mem_nbhd a⟩, fun h => h.2 rfl⟩
  nbhd_subset a := fun x hx => F₁.nbhd_subset a hx.1.1
  unit_contMDiffOn a := by
    refine ContMDiffOn.mul ((F₁.unit_contMDiffOn a).mono ?_) ((F₂.unit_contMDiffOn a).mono ?_)
    · exact fun x hx => hx.1.1
    · exact fun x hx => hx.1.2
  unit_ne_zero a x hx := mul_ne_zero (F₁.unit_ne_zero a x hx.1.1) (F₂.unit_ne_zero a x hx.1.2)
  normalForm a x hx := by
    rcases eq_or_ne x a with rfl | hne
    · rw [chartCoord_self, Finsupp.add_apply]
    · have hsupp : x ∉ ((D₁.support : Set X) ∪ (D₂.support : Set X)) := by
        intro hmem
        exact hx.2 ⟨hmem, hne⟩
      have hD₁ : D₁ x = 0 := by
        by_contra h
        exact hsupp (by simp [Finsupp.mem_support_iff, h])
      have hD₂ : D₂ x = 0 := by
        by_contra h
        exact hsupp (by simp [Finsupp.mem_support_iff, h])
      have hz : chartCoord a x ≠ 0 :=
        chartCoord_ne_zero (F₁.nbhd_subset a hx.1.1) hne
      have h₁ := F₁.normalForm a x hx.1.1
      have h₂ := F₂.normalForm a x hx.1.2
      rw [F₁.toFun_eq_unit_of_coeff_zero hD₁] at h₁
      rw [F₂.toFun_eq_unit_of_coeff_zero hD₂] at h₂
      rw [hD₁, hD₂, add_zero, zpow_zero, mul_one, h₁, h₂, Finsupp.add_apply,
        zpow_add₀ hz]
      ring

@[simp] theorem mul_unit (F₁ : WeakSolution D₁) (F₂ : WeakSolution D₂) (a x : X) :
    (F₁.mul F₂).unit a x = F₁.unit a x * F₂.unit a x := rfl

/-- Off both supports, the product weak solution is the pointwise product. -/
theorem mul_toFun_of_coeff_zero (F₁ : WeakSolution D₁) (F₂ : WeakSolution D₂) {x : X}
    (h₁ : D₁ x = 0) (h₂ : D₂ x = 0) :
    (F₁.mul F₂).toFun x = F₁.toFun x * F₂.toFun x := by
  show F₁.unit x x * F₂.unit x x * (0 : ℂ) ^ (D₁ x + D₂ x) = _
  rw [h₁, h₂, add_zero, zpow_zero, mul_one,
    F₁.toFun_eq_unit_of_coeff_zero h₁, F₂.toFun_eq_unit_of_coeff_zero h₂]

/-! ### Inverses (Forster 20.1: `1/f` solves `−D`)

With the `zpow`-junk normalization (`0⁻¹ = 0`, `(0:ℂ)^{-k} = 0`), the pointwise inverse is
literally a weak solution of `−D` — no repair. -/

/-- **Inverse of a weak solution**: solves `−D`. -/
def inv (F : WeakSolution D) : WeakSolution (-D) where
  toFun := fun x => (F.toFun x)⁻¹
  nbhd := F.nbhd
  unit a := fun x => (F.unit a x)⁻¹
  isOpen_nbhd := F.isOpen_nbhd
  mem_nbhd := F.mem_nbhd
  nbhd_subset := F.nbhd_subset
  unit_contMDiffOn a := by
    intro x hx
    refine (ContMDiffAt.contMDiffWithinAt ?_)
    exact (contMDiffAt_inv_complex (F.unit_ne_zero a x hx)).comp x (F.unit_contMDiffAt a hx)
  unit_ne_zero a x hx := inv_ne_zero (F.unit_ne_zero a x hx)
  normalForm a x hx := by
    rw [F.normalForm a x hx, mul_inv, Finsupp.neg_apply, zpow_neg]

@[simp] theorem inv_toFun (F : WeakSolution D) (x : X) :
    F.inv.toFun x = (F.toFun x)⁻¹ := rfl

@[simp] theorem inv_unit (F : WeakSolution D) (a x : X) :
    F.inv.unit a x = (F.unit a x)⁻¹ := rfl

/-! ### Integer powers -/

/-- Transport a weak solution along an equality of divisors. -/
def recast (h : D₁ = D₂) (F : WeakSolution D₁) : WeakSolution D₂ := h ▸ F

@[simp] theorem recast_toFun (h : D₁ = D₂) (F : WeakSolution D₁) :
    (F.recast h).toFun = F.toFun := by cases h; rfl

@[simp] theorem recast_unit (h : D₁ = D₂) (F : WeakSolution D₁) :
    (F.recast h).unit = F.unit := by cases h; rfl

/-- **Natural powers of a weak solution**: `f^n` solves `n • D`. -/
def pow (F : WeakSolution D) : (n : ℕ) → WeakSolution ((n : ℤ) • D)
  | 0 => (one X).recast (by rw [Nat.cast_zero, zero_smul])
  | n + 1 => ((F.pow n).mul F).recast
      (by rw [Nat.cast_add, Nat.cast_one, add_smul, one_smul])

/-- **Integer powers of a weak solution**: `f^n` solves `n • D` (negative powers via the
inverse). -/
def zpow (F : WeakSolution D) : (n : ℤ) → WeakSolution (n • D)
  | (n : ℕ) => F.pow n
  | Int.negSucc n => ((F.pow (n + 1)).inv).recast
      (by rw [Int.negSucc_eq, neg_smul, Nat.cast_add, Nat.cast_one])

end WeakSolution

end Jacobians
