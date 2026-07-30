/-
Submission for the lean-eval problem `jacobian_challenge_diffgeo`
(Kevin Buzzard's Jacobian challenge). The full development lives under
`Submission/` (root module `Submission.Root`); this file provides the
challenge declarations in the problem file's `JacobianChallenge` namespace,
each delegating to the proven development. Sorry-free; axioms:
[propext, Classical.choice, Quot.sound].
-/
import Submission.Root

open scoped ContDiff

namespace Submission

namespace JacobianChallenge

universe u v w

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) ω X]

/-- Runtime stub (the honest `genus` is noncomputable; the problem file's `Solution.lean`
delegates via a plain `def`, so executable code must exist). Never affects the kernel. -/
unsafe def genusImpl (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) ω X] : ℕ :=
  unsafeCast ()

@[implemented_by genusImpl]
def genus (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) ω X] : ℕ :=
  _root_.genus X

theorem genus_eq_zero_iff_homeo :
    genus X = 0 ↔ Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
  _root_.genus_eq_zero_iff_homeo

def Jacobian (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) ω X] : Type u :=
  _root_.Jacobian X

namespace Jacobian

unsafe def instAddCommGroupImpl : AddCommGroup (_root_.Jacobian X) := unsafeCast ()

@[implemented_by instAddCommGroupImpl]
def instAddCommGroup : AddCommGroup (_root_.Jacobian X) := inferInstance

unsafe def instTopologicalSpaceImpl : TopologicalSpace (_root_.Jacobian X) := unsafeCast ()

@[implemented_by instTopologicalSpaceImpl]
def instTopologicalSpace : TopologicalSpace (_root_.Jacobian X) := inferInstance

def instT2Space : T2Space (_root_.Jacobian X) := inferInstance

def instCompactSpace : CompactSpace (_root_.Jacobian X) := inferInstance

unsafe def instChartedSpaceImpl : ChartedSpace (Fin (_root_.genus X) → ℂ) (_root_.Jacobian X) :=
  unsafeCast ()

@[implemented_by instChartedSpaceImpl]
def instChartedSpace : ChartedSpace (Fin (_root_.genus X) → ℂ) (_root_.Jacobian X) :=
  inferInstance

def instIsManifold :
    IsManifold (modelWithCornersSelf ℂ (Fin (_root_.genus X) → ℂ)) ω (_root_.Jacobian X) :=
  inferInstance

def instLieAddGroup :
    LieAddGroup (modelWithCornersSelf ℂ (Fin (_root_.genus X) → ℂ)) ω (_root_.Jacobian X) :=
  inferInstance

unsafe def ofCurveImpl (P : X) : X → _root_.Jacobian X := unsafeCast ()

@[implemented_by ofCurveImpl]
def ofCurve (P : X) : X → _root_.Jacobian X := _root_.Jacobian.ofCurve P

theorem ofCurve_contMDiff (P : X) :
    ContMDiff (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ (Fin (_root_.genus X) → ℂ)) ω (ofCurve P) :=
  _root_.Jacobian.ofCurve_contMDiff P

theorem ofCurve_self (P : X) : ofCurve P P = 0 := _root_.Jacobian.ofCurve_self P

theorem ofCurve_inj (P : X) (h : 0 < genus X) : Function.Injective (ofCurve P) :=
  _root_.Jacobian.ofCurve_inj P h

variable {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold (modelWithCornersSelf ℂ ℂ) ω Y]

variable (f : X → Y) (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f)

unsafe def pushforwardImpl (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) :
    _root_.Jacobian X →ₜ+ _root_.Jacobian Y :=
  unsafeCast ()

@[implemented_by pushforwardImpl]
def pushforward (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) :
    _root_.Jacobian X →ₜ+ _root_.Jacobian Y :=
  _root_.Jacobian.pushforward f hf

theorem pushforward_contMDiff (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (_root_.genus X) → ℂ))
      (modelWithCornersSelf ℂ (Fin (_root_.genus Y) → ℂ)) ω (pushforward f hf) :=
  _root_.Jacobian.pushforward_contMDiff f hf

theorem pushforward_id_apply (P : _root_.Jacobian X) :
    pushforward id contMDiff_id P = P :=
  _root_.Jacobian.pushforward_id_apply P

variable {Z : Type w} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [Nonempty Z] [ChartedSpace ℂ Z] [IsManifold (modelWithCornersSelf ℂ ℂ) ω Z]

variable (g : Y → Z) (hg : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω g)

theorem pushforward_comp_apply (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω g)
    (P : _root_.Jacobian X) :
    pushforward (g ∘ f) (hg.comp hf) P = pushforward g hg (pushforward f hf P) := by
  apply _root_.Jacobian.pushforward_comp_apply

unsafe def pullbackImpl (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) :
    _root_.Jacobian Y →ₜ+ _root_.Jacobian X :=
  unsafeCast ()

@[implemented_by pullbackImpl]
def pullback (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) :
    _root_.Jacobian Y →ₜ+ _root_.Jacobian X :=
  _root_.Jacobian.pullback f hf

theorem pullback_contMDiff (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (_root_.genus Y) → ℂ))
      (modelWithCornersSelf ℂ (Fin (_root_.genus X) → ℂ)) ω (pullback f hf) :=
  _root_.Jacobian.pullback_contMDiff f hf

theorem pullback_id_apply (P : _root_.Jacobian X) :
    pullback id contMDiff_id P = P :=
  _root_.Jacobian.pullback_id_apply P

theorem pullback_comp_apply (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω g)
    (P : _root_.Jacobian Z) :
    pullback (g.comp f) (hg.comp hf) P = pullback f hf (pullback g hg P) := by
  apply _root_.Jacobian.pullback_comp_apply

unsafe def degreeImpl {X' : Type u} [TopologicalSpace X'] [ChartedSpace ℂ X']
    {Y' : Type v} [TopologicalSpace Y'] [ChartedSpace ℂ Y'] (f : X' → Y')
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) : ℕ :=
  unsafeCast ()

open Classical in
/-- The mapping degree, in the challenge's (weak) signature: the benchmark's `degree` hole was
elaborated from a `sorry` body, so only the instances mentioned by its signature were included.
On compact connected Riemann surfaces this agrees with the honest `ContMDiff.degree`
(propositional type classes are proof-irrelevant); off that case it returns `0`. -/
@[implemented_by degreeImpl]
def degree {X' : Type u} [TopologicalSpace X'] [ChartedSpace ℂ X']
    {Y' : Type v} [TopologicalSpace Y'] [ChartedSpace ℂ Y'] (f : X' → Y')
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) : ℕ :=
  if h : T2Space X' ∧ CompactSpace X' ∧ ConnectedSpace X'
      ∧ IsManifold (modelWithCornersSelf ℂ ℂ) ω X'
      ∧ T2Space Y' ∧ CompactSpace Y' ∧ ConnectedSpace Y'
      ∧ IsManifold (modelWithCornersSelf ℂ ℂ) ω Y' then
    @ContMDiff.degree X' _ h.1 h.2.1 h.2.2.1 _ h.2.2.2.1
      Y' _ h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 _ h.2.2.2.2.2.2.2 f hf
  else 0

theorem pushforward_pullback (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f)
    (P : _root_.Jacobian Y) :
    pushforward f hf (pullback f hf P) = (degree f hf) • P := by
  have hdeg : degree f hf = ContMDiff.degree f hf := by
    rw [degree, dif_pos ⟨inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance⟩]
  rw [hdeg]
  apply _root_.Jacobian.pushforward_pullback

end Jacobian

end JacobianChallenge

end Submission
