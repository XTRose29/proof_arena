import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Algebra.Metric
import DifferentialGeometry.Geometry.Connection
import DifferentialGeometry.Geometry.Curvature
import DifferentialGeometry.Operators.Gradient
import DifferentialGeometry.Operators.Laplacian
import DifferentialGeometry.Operators.Hessian
import DifferentialGeometry.Operators.Time
import DifferentialGeometry.Operators.Variation
import DifferentialGeometry.Operators.Bochner
import DifferentialGeometry.Flows.RicciFlow.Basic
import DifferentialGeometry.Analysis.TraceRankOne
import DifferentialGeometry.Analysis.TensorInnerProduct
import DifferentialGeometry.Operators.CovariantDerivative
import DifferentialGeometry.Operators.SpatialConstant
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Linarith

-- Download DifferentialGeometry at https://github.com/qinz1yang/differential-geometry

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

namespace CaoCerenziaKazaras2014

variable {Time R V : Type}
variable [CommRing R] [PartialOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V]
variable [DerivationAction R V] [LieBracket V] [DerivationRules R V] [TraceOperator R V]
variable [TimeDerivative Time R] [TimeDerivative Time V] [TimeDerivativeRules Time R V]
variable [ActionTimeDerivativeRules Time R V] [Invertible (2:R)]

/-! NODE
  \name: RicciFlat
  \inputs: []
  \type: class
  \natural: Defines a Ricci-flat affine connection, where the Ricci curvature tensor vanishes identically, $Rc = 0$.
  \NL_proof:
-/
class RicciFlat (conn : AffineConnection R V) : Prop where
  rc_zero : ∀ X Y, Rc conn X Y = 0

/-! NODE
  \name: flat_bochner_identity
  \inputs: ["RicciFlat"]
  \type: theorem
  \natural: The Bochner identity on a Ricci-flat manifold for a scalar function $f$: $\Delta(|\nabla f|^2) = 2\langle \nabla f, \nabla(\Delta f) \rangle + 2|\nabla^2 f|^2$.
  \NL_proof: Start with the standard Bochner identity for the Laplacian of the squared gradient of a scalar function. Apply the Ricci-flat condition, which sets the Ricci curvature term to zero. Rearrange the remaining terms to obtain the result.
-/
theorem flat_bochner_identity
  [Invertible (2 : R)] [TraceOperator R V]
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor] [MetricTraceRules R V metric.toNonDegenerateMetric.toMetricTensor]
  (conn : AffineConnection R V) [MetricCompatible conn metric.toNonDegenerateMetric.toMetricTensor] [TorsionFree conn]
  [bochner_rules : BochnerTraceRules metric conn]
  [ricci_flat : RicciFlat conn]
  (f : R) :
  laplacian metric.toNonDegenerateMetric.toMetricTensor conn (metric.g (grad metric f) (grad metric f)) =
  (2:R) * metric.g (grad metric f) (grad metric (laplacian metric.toNonDegenerateMetric.toMetricTensor conn f)) +
  (2:R) * tensorNormSq metric (hessianForm conn f) := by sorry

/-! NODE
  \name: ESEExponentialSmooth
  \inputs: []
  \type: class
  \natural: Specifies the evolution equations for the abstract exponential term $E(t)$ representing $e^{u(p-1)}$, including its time derivative, gradient, and Laplacian.
  \NL_proof:
-/
class ESEExponentialSmooth
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  (conn : AffineConnection R V)
  (u E : Time → R) (p : R) where
  dt_eq : ∀ t, TimeDerivative.partial_t E t = (p - 1) * E t * TimeDerivative.partial_t u t
  grad_eq : ∀ t, grad metric (E t) = ((p - 1) * E t) • grad metric (u t)
  laplacian_eq : ∀ t,
    laplacian metric.toNonDegenerateMetric.toMetricTensor conn (E t) =
      (p - 1) * E t * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) +
      (p - 1)^2 * E t * metric.g (grad metric (u t)) (grad metric (u t))

/-! NODE
  \name: EndangeredSpeciesEquation
  \inputs: []
  \type: class
  \natural: Endangered Species Equation (ESE) under logarithmic transformation $u = \log f$: $u_t = \Delta u + |\nabla u|^2 + E(t)$, where $E(t)$ represents $e^{u(p-1)}$.
  \NL_proof:
-/
class EndangeredSpeciesEquation
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  (conn : AffineConnection R V)
  (u E : Time → R) where
  eq : ∀ t, TimeDerivative.partial_t u t =
    laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) +
    metric.g (grad metric (u t)) (grad metric (u t)) +
    E t

/-! NODE
  \name: H_def
  \inputs: []
  \type: definition
  \natural: Harnack Quantity $H$ from Cao-Cerenzia-Kazaras (2014) Lemma 2.1: $H := \alpha\Delta u + \beta|\nabla u|^2 + c e^{u(p-1)} + \varphi$. We represent $e^{u(p-1)}$ as $E$.
  \NL_proof:
-/
def H_def
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  (conn : AffineConnection R V)
  (α β c : R)
  (u E φ : Time → R)
  (t : Time) : R :=
  α * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) +
  β * metric.g (grad metric (u t)) (grad metric (u t)) +
  c * E t +
  φ t

/-! NODE
  \name: dt_laplacian_evolution
  \inputs: ["EndangeredSpeciesEquation", "ESEExponentialSmooth"]
  \type: theorem
  \natural: The evolution of the Laplacian of $u$: $\partial_t(\Delta u) = \Delta(\Delta u) + \Delta(|\nabla u|^2) + (p-1)E \Delta u + (p-1)^2 E |\nabla u|^2$.
  \NL_proof: Commute the time derivative with the Laplacian using the static metric assumption. Substitute the evolution equation for $u_t$. Expand the Laplacian of the resulting sum, and substitute the assumed Laplacian identity for the exponential term $E$.
-/
theorem dt_laplacian_evolution
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  (conn : AffineConnection R V)
  (u E : Time → R)
  (p : R)
  [ese : EndangeredSpeciesEquation metric conn u E]
  [ese_exp : ESEExponentialSmooth metric conn u E p]
  [static_time : StaticMetricTimeRules Time metric conn]
  [TraceLinearityRules R V]
  [MetricTraceRules R V metric.toNonDegenerateMetric.toMetricTensor]
  (t : Time) :
  TimeDerivative.partial_t (fun s => laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u s)) t =
  laplacian metric.toNonDegenerateMetric.toMetricTensor conn (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t)) +
  laplacian metric.toNonDegenerateMetric.toMetricTensor conn (metric.g (grad metric (u t)) (grad metric (u t))) +
  (p - 1) * E t * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) +
  (p - 1)^2 * E t * metric.g (grad metric (u t)) (grad metric (u t)) := by sorry

/-! NODE
  \name: dt_grad_sq_evolution
  \inputs: ["EndangeredSpeciesEquation", "ESEExponentialSmooth", "flat_bochner_identity"]
  \type: theorem
  \natural: The evolution of the squared gradient of $u$: $\partial_t(|\nabla u|^2) = \Delta(|\nabla u|^2) - 2|\nabla^2 u|^2 + 2\langle \nabla(|\nabla u|^2), \nabla u \rangle + 2(p-1)E|\nabla u|^2$.
  \NL_proof: Commute the time derivative with the metric gradient norm squared. Substitute the evolution equation for $u_t$ and expand the gradient of the sum. Apply the Bochner identity on a Ricci-flat manifold to substitute the $\langle \nabla(\Delta u), \nabla u \rangle$ term. Substitute the gradient identity for the exponential term $E$ and simplify using algebraic properties of the metric tensor.
-/
theorem dt_grad_sq_evolution
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  [TraceLinearityRules R V]
  [MetricTraceRules R V metric.toNonDegenerateMetric.toMetricTensor]
  (conn : AffineConnection R V)
  (u E : Time → R)
  (p : R)
  [ese : EndangeredSpeciesEquation metric conn u E]
  [ese_exp : ESEExponentialSmooth metric conn u E p]
  [MetricTraceRules R V metric.toNonDegenerateMetric.toMetricTensor]
  [MetricCompatible conn metric.toNonDegenerateMetric.toMetricTensor]
  [TorsionFree conn]
  [bochner_rules : BochnerTraceRules metric conn]
  [ricci_flat : RicciFlat conn]
  [static_time : StaticMetricTimeRules Time metric conn]
  (t : Time) :
  TimeDerivative.partial_t (fun s => metric.g (grad metric (u s)) (grad metric (u s))) t =
  laplacian metric.toNonDegenerateMetric.toMetricTensor conn (metric.g (grad metric (u t)) (grad metric (u t))) -
  (2:R) * tensorNormSq metric (hessianForm conn (u t)) +
  (2:R) * metric.g (grad metric (metric.g (grad metric (u t)) (grad metric (u t)))) (grad metric (u t)) +
  (2:R) * (p - 1) * E t * metric.g (grad metric (u t)) (grad metric (u t)) := by sorry

/-! NODE
  \name: lemma_2_1_algebraic_identity
  \inputs: []
  \type: lemma
  \natural: An algebraic identity ensuring the components of the $H$ evolution equation cancel correctly, relying on the Bochner identity and the $u_t$ equation.
  \NL_proof: Group terms by their coefficients $\alpha$, $\beta$, and $c$. Substitute the Bochner identity relation and the Endangered Species Equation relation into the separated groups. Algebraic expansion and cancellation show that the difference between the two large expressions evaluates to exactly zero.
-/
lemma lemma_2_1_algebraic_identity
  (α β c p : R)
  (LapLapU LapGradSq LapU GradSq HessSq GradGradSq GradLapU E Phi Phi_t LapPhi GradPhi_GradU u_t : R)
  (h_bochner : LapGradSq = (2:R) * GradLapU + (2:R) * HessSq)
  (h_ut : u_t = LapU + GradSq + E) :
  -- LHS (H_t expanded)
  α * (LapLapU + LapGradSq + (p - 1) * E * LapU + (p - 1)^2 * E * GradSq) +
  β * (LapGradSq - (2:R) * HessSq + (2:R) * GradGradSq + (2:R) * (p - 1) * E * GradSq) +
  c * ((p - 1) * E * u_t) +
  Phi_t
  -
  -- RHS (Target)
  (
  (α * LapLapU + β * LapGradSq + c * ((p - 1) * E * LapU + (p - 1)^2 * E * GradSq) + LapPhi) +
    (2:R) * (α * GradLapU + β * GradGradSq + c * (p - 1) * E * GradSq + GradPhi_GradU) +
    (p - 1) * E * (α * LapU + β * GradSq + c * E + Phi) +
    (2:R) * (α - β) * HessSq +
    (α * (p - 1) + β - c * p) * (p - 1) * E * GradSq -
    (p - 1) * E * Phi +
    Phi_t -
    LapPhi -
    (2:R) * GradPhi_GradU
  )
  = 0 := by sorry

/-! NODE
  \name: lemma_2_1_evolution
  \inputs: ["EndangeredSpeciesEquation", "ESEExponentialSmooth", "dt_laplacian_evolution", "dt_grad_sq_evolution", "lemma_2_1_algebraic_identity", "H_def"]
  \type: theorem
  \natural: The complete evolution equation for the Harnack quantity $H$, matching Lemma 2.1 in Cao-Cerenzia-Kazaras (2014): $H_t = \Delta H + 2\langle \nabla H, \nabla u \rangle + (p-1)e^{u(p-1)}H + 2(\alpha-\beta)|\nabla\nabla u|^2 + (\alpha(p-1)+\beta-cp)(p-1)e^{u(p-1)}|\nabla u|^2 - (p-1)e^{u(p-1)}\varphi + \varphi_t - \Delta\varphi - 2\langle \nabla\varphi, \nabla u \rangle$.
  \NL_proof: Take the time derivative of the definition of $H$. Expand the derivatives linearly. Substitute the previously derived evolution equations for the Laplacian of $u$, the squared gradient of $u$, and the exponential term $E$. Expand the spatial Laplacian and gradient of $H$. Finally, apply the algebraic identity lemma to match the resulting terms to the target RHS of the evolution equation, concluding the proof.
-/
theorem lemma_2_1_evolution
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  (conn : AffineConnection R V)
  (α β c p : R)
  [h_const_alpha : IsSpatialConstant R V α]
  [h_const_beta : IsSpatialConstant R V β]
  [h_const_c : IsSpatialConstant R V c]
  (u E φ : Time → R)
  [ese : EndangeredSpeciesEquation metric conn u E]
  [static_time : StaticMetricTimeRules Time metric conn]
  [TraceLinearityRules R V]
  [MetricTraceRules R V metric.toNonDegenerateMetric.toMetricTensor]
  [MetricCompatible conn metric.toNonDegenerateMetric.toMetricTensor]
  [TorsionFree conn]
  [bochner_rules : BochnerTraceRules metric conn]
  [ricci_flat : RicciFlat conn]
  [ese_exp : ESEExponentialSmooth metric conn u E p]
  [scalar_deriv_rules : TimeDerivativeRules Time R V]
  (t : Time) :
  TimeDerivative.partial_t (fun s => H_def metric conn α β c u E φ s) t =
  laplacian metric.toNonDegenerateMetric.toMetricTensor conn (H_def metric conn α β c u E φ t) +
  (2:R) * metric.g (grad metric (H_def metric conn α β c u E φ t)) (grad metric (u t)) +
  (p - 1) * E t * H_def metric conn α β c u E φ t +
  (2:R) * (α - β) * tensorNormSq metric (hessianForm conn (u t)) +
  (α * (p - 1) + β - c * p) * (p - 1) * E t * metric.g (grad metric (u t)) (grad metric (u t)) -
  (p - 1) * E t * φ t +
  TimeDerivative.partial_t φ t -
  laplacian metric.toNonDegenerateMetric.toMetricTensor conn (φ t) -
  (2:R) * metric.g (grad metric (φ t)) (grad metric (u t)) := by sorry

end CaoCerenziaKazaras2014
