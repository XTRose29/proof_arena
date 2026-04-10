import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Algebra.Metric
import DifferentialGeometry.Geometry.Connection
import DifferentialGeometry.Geometry.Curvature
import DifferentialGeometry.Operators.Gradient
import DifferentialGeometry.Operators.Laplacian
import DifferentialGeometry.Operators.Hessian
import DifferentialGeometry.Operators.Variation
import DifferentialGeometry.Operators.Bochner
import DifferentialGeometry.Analysis.TensorInnerProduct
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

variable {Time R V : Type}
variable [CommRing R] [PartialOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V]
variable [DerivationAction R V] [LieBracket V] [DerivationRules R V] [TraceOperator R V]

/-- The drift operator L(h) = ∂_t h - Δh - 2⟨∇f, ∇h⟩ -/
def L
  [TimeDerivative Time R]
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  (conn : AffineConnection R V)
  (f h : Time → R) (t : Time) : R :=
  TimeDerivative.partial_t h t - laplacian metric.toNonDegenerateMetric.toMetricTensor conn (h t) - 2 * metric.g (grad metric (f t)) (grad metric (h t))

/-- Hypotheses for the 1D Li-Yau Harnack Inequality on a static, flat metric evolution where u solves the heat equation and f = log u. -/
class HeatEquation1D
  [TimeDerivative Time R]
  (metric : MetricDuality R V)
  [TraceOperator R V]
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  (conn : AffineConnection R V)
  (u f inv_u : Time → R) where
  metric_flat : ∀ X Y Z, Rm conn X Y Z = 0
  flat_Rc : ∀ X Y, Rc conn X Y = 0
  heat_eq : ∀ t, TimeDerivative.partial_t u t = laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t)
  dt_laplacian_commute : ∀ (h : Time → R) t, TimeDerivative.partial_t (fun s => laplacian metric.toNonDegenerateMetric.toMetricTensor conn (h s)) t = laplacian metric.toNonDegenerateMetric.toMetricTensor conn (TimeDerivative.partial_t h t)
  laplacian_add : ∀ (h1 h2 : R), laplacian metric.toNonDegenerateMetric.toMetricTensor conn (h1 + h2) = laplacian metric.toNonDegenerateMetric.toMetricTensor conn h1 + laplacian metric.toNonDegenerateMetric.toMetricTensor conn h2
  inv_u_mul_u : ∀ t, inv_u t * u t = 1
  dt_log : ∀ t, TimeDerivative.partial_t f t = inv_u t * TimeDerivative.partial_t u t
  grad_log : ∀ t, grad metric (f t) = inv_u t • grad metric (u t)
  laplacian_log : ∀ t, laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) = inv_u t * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) - (inv_u t)^2 * metric.g (grad metric (u t)) (grad metric (u t))
  hessian_norm_eq_laplacian_sq : ∀ t, tensorNormSq metric (hessianForm conn (f t)) = laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t)
  t_val : Time → R
  L_t_mul : ∀ (h : Time → R) t, L metric conn f (fun s => t_val s * h s) t = t_val t * L metric conn f h t + h t
  L_const : ∀ (c : R) t, L metric conn f (fun _ => c) t = 0
  L_add : ∀ (h1 h2 : Time → R) t, L metric conn f (fun s => h1 s + h2 s) t = L metric conn f h1 t + L metric conn f h2 t
  L_sub : ∀ (h1 h2 : Time → R) t, L metric conn f (fun s => h1 s - h2 s) t = L metric conn f h1 t - L metric conn f h2 t
  L_smul : ∀ (c : R) (h : Time → R) t, L metric conn f (fun s => c * h s) t = c * L metric conn f h t

/-- Derives the evolution equation for f = log u under the heat flow: ∂_t f = Δf + |∇f|^2. -/
theorem f_evolution
  [TimeDerivative Time R]
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  (conn : AffineConnection R V)
  (u f inv_u : Time → R)
  [heat : HeatEquation1D metric conn u f inv_u]
  (t : Time) :
  TimeDerivative.partial_t f t = laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) + metric.g (grad metric (f t)) (grad metric (f t)) := by
  have hdt : TimeDerivative.partial_t f t = inv_u t * TimeDerivative.partial_t u t := heat.dt_log t
  have heq : TimeDerivative.partial_t u t = laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) := heat.heat_eq t
  have hlap : laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) = inv_u t * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (u t) - (inv_u t)^2 * metric.g (grad metric (u t)) (grad metric (u t)) := heat.laplacian_log t
  have hgrad : grad metric (f t) = inv_u t • grad metric (u t) := heat.grad_log t
  rw [hdt, heq, hlap, hgrad]
  have h_smul1 : metric.g (inv_u t • grad metric (u t)) (inv_u t • grad metric (u t)) = inv_u t * metric.g (grad metric (u t)) (inv_u t • grad metric (u t)) := metric.toNonDegenerateMetric.toMetricTensor.bilinear_smul_left (inv_u t) _ _
  have h_symm : metric.g (grad metric (u t)) (inv_u t • grad metric (u t)) = metric.g (inv_u t • grad metric (u t)) (grad metric (u t)) := metric.toNonDegenerateMetric.toMetricTensor.symm _ _
  have h_smul2 : metric.g (inv_u t • grad metric (u t)) (grad metric (u t)) = inv_u t * metric.g (grad metric (u t)) (grad metric (u t)) := metric.toNonDegenerateMetric.toMetricTensor.bilinear_smul_left (inv_u t) _ _
  rw [h_smul1, h_symm, h_smul2]
  ring

/-- Derives the evolution of the Laplacian of f using the Bochner identity on a flat manifold: L(Δf) = 2|∇²f|^2. -/
theorem laplacian_f_evolution
  [TimeDerivative Time R] [Invertible (2 : R)] [TraceOperator R V]
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  [MetricTraceRules R V metric.toNonDegenerateMetric.toMetricTensor]
  (conn : AffineConnection R V) [MetricCompatible conn metric.toNonDegenerateMetric.toMetricTensor]
  [TorsionFree conn] [bochner_rules : BochnerTraceRules metric conn]
  (u f inv_u : Time → R)
  [heat : HeatEquation1D metric conn u f inv_u]
  (t : Time) :
  L metric conn f (fun s => laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f s)) t =
  2 * tensorNormSq metric (hessianForm conn (f t)) := by
  dsimp [L]
  have h_comm : TimeDerivative.partial_t (fun s => laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f s)) t = laplacian metric.toNonDegenerateMetric.toMetricTensor conn (TimeDerivative.partial_t f t) := heat.dt_laplacian_commute f t
  rw [h_comm]
  have h_f_evol : TimeDerivative.partial_t f t = laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) + metric.g (grad metric (f t)) (grad metric (f t)) := f_evolution metric conn u f inv_u t
  rw [h_f_evol]
  have h_lap_add : laplacian metric.toNonDegenerateMetric.toMetricTensor conn (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) + metric.g (grad metric (f t)) (grad metric (f t))) = laplacian metric.toNonDegenerateMetric.toMetricTensor conn (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t)) + laplacian metric.toNonDegenerateMetric.toMetricTensor conn (metric.g (grad metric (f t)) (grad metric (f t))) := heat.laplacian_add _ _
  rw [h_lap_add]
  have h_bochner : laplacian metric.toNonDegenerateMetric.toMetricTensor conn (metric.g (grad metric (f t)) (grad metric (f t))) = 2 * tensorNormSq metric (hessianForm conn (f t)) + 2 * Rc conn (grad metric (f t)) (grad metric (f t)) + 2 * metric.g (grad metric (f t)) (grad metric (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t))) := bochner_identity metric conn (f t)
  rw [h_bochner]
  have h_rc : Rc conn (grad metric (f t)) (grad metric (f t)) = 0 := heat.flat_Rc _ _
  rw [h_rc]
  change laplacian metric.toNonDegenerateMetric.toMetricTensor conn (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t)) + (2 * tensorNormSq metric (hessianForm conn (f t)) + 2 * 0 + 2 * metric.g (grad metric (f t)) (grad metric (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t)))) - laplacian metric.toNonDegenerateMetric.toMetricTensor conn (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t)) - 2 * metric.g (grad metric (f t)) (grad metric (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t))) = 2 * tensorNormSq metric (hessianForm conn (f t))
  ring

/-- The Li-Yau Harnack quantity Q = t(|∇f|^2 - ∂_t f) - 1/2, algebraically simplified using the f evolution equation. -/
def Q
  [TimeDerivative Time R] [Invertible (2 : R)] [TraceOperator R V]
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  (conn : AffineConnection R V)
  (u f inv_u : Time → R)
  (t : Time)
  [heat : HeatEquation1D metric conn u f inv_u] : R :=
  - heat.t_val t * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) - (⅟2 : R)

/-- Derives the evolution inequality for the Li-Yau quantity Q under the drift operator: t L(Q) = -2 Q (Q + 1/2). -/
theorem Q_evolution
  [TimeDerivative Time R] [Invertible (2 : R)] [TraceOperator R V]
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  [MetricTraceRules R V metric.toNonDegenerateMetric.toMetricTensor]
  (conn : AffineConnection R V) [MetricCompatible conn metric.toNonDegenerateMetric.toMetricTensor]
  [TorsionFree conn] [bochner_rules : BochnerTraceRules metric conn]
  (u f inv_u : Time → R)
  [heat : HeatEquation1D metric conn u f inv_u]
  (t : Time) :
  heat.t_val t * L metric conn f (fun s => Q metric conn u f inv_u s) t =
  - 2 * (Q metric conn u f inv_u t) * (Q metric conn u f inv_u t + (⅟2 : R)) := by
  have h_q_l : L metric conn f (fun s => Q metric conn u f inv_u s) t = L metric conn f (fun s => - heat.t_val s * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f s) - (⅟2 : R)) t := rfl
  rw [h_q_l]
  have h_sub : L metric conn f (fun s => - heat.t_val s * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f s) - (⅟2 : R)) t = L metric conn f (fun s => - heat.t_val s * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f s)) t - L metric conn f (fun s => (⅟2 : R)) t := heat.L_sub _ _ t
  rw [h_sub]
  rw [heat.L_const (⅟2 : R) t]
  have h_neg : (fun s => - heat.t_val s * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f s)) = fun s => (-1 : R) * (heat.t_val s * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f s)) := by
    funext s
    ring
  rw [h_neg]
  rw [heat.L_smul (-1 : R) _ t]
  have h_tmul : L metric conn f (fun s => heat.t_val s * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f s)) t = heat.t_val t * L metric conn f (fun s => laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f s)) t + laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) := heat.L_t_mul _ t
  rw [h_tmul]
  have h_lap_evol : L metric conn f (fun s => laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f s)) t = 2 * tensorNormSq metric (hessianForm conn (f t)) := laplacian_f_evolution metric conn u f inv_u t
  rw [h_lap_evol]
  have h_1d : tensorNormSq metric (hessianForm conn (f t)) = laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) := heat.hessian_norm_eq_laplacian_sq t
  rw [h_1d]
  have h_rhs : - 2 * (Q metric conn u f inv_u t) * (Q metric conn u f inv_u t + (⅟2 : R)) = - 2 * (- heat.t_val t * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) - (⅟2 : R)) * (- heat.t_val t * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) - (⅟2 : R) + (⅟2 : R)) := rfl
  rw [h_rhs]
  have h_half : (2 : R) * (⅟2 : R) = 1 := mul_invOf_self 2
  have h_alg : - 2 * (- heat.t_val t * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) - (⅟2 : R)) * (- heat.t_val t * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) - (⅟2 : R) + (⅟2 : R)) =
               - 2 * (heat.t_val t * heat.t_val t) * (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t)) - heat.t_val t * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) := by
    have step1 : (- heat.t_val t * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) - (⅟2 : R) + (⅟2 : R)) = - heat.t_val t * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) := by abel
    rw [step1]
    calc -2 * (- heat.t_val t * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) - (⅟2 : R)) * (- heat.t_val t * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t))
      _ = - 2 * (heat.t_val t * heat.t_val t) * (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t)) - (2 * (⅟2 : R)) * (heat.t_val t * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t)) := by ring
      _ = - 2 * (heat.t_val t * heat.t_val t) * (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t)) - 1 * (heat.t_val t * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t)) := by rw [h_half]
      _ = - 2 * (heat.t_val t * heat.t_val t) * (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t)) - heat.t_val t * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) := by ring

  calc heat.t_val t * ((-1 : R) * (heat.t_val t * (2 * (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t))) + laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t)) - 0)
    _ = - 2 * (heat.t_val t * heat.t_val t) * (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t)) - heat.t_val t * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) := by ring
    _ = - 2 * (- heat.t_val t * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) - (⅟2 : R)) * (- heat.t_val t * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) - (⅟2 : R) + (⅟2 : R)) := h_alg.symm

/-- The Maximum Principle is injected as axiom -/
axiom max_principle
  [TimeDerivative Time R] [Invertible (2 : R)] [TraceOperator R V]
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  [MetricTraceRules R V metric.toNonDegenerateMetric.toMetricTensor]
  (conn : AffineConnection R V) [MetricCompatible conn metric.toNonDegenerateMetric.toMetricTensor]
  [TorsionFree conn] [bochner_rules : BochnerTraceRules metric conn]
  (u f inv_u : Time → R)
  [heat : HeatEquation1D metric conn u f inv_u] :
  (∀ t, heat.t_val t * L metric conn f (fun s => Q metric conn u f inv_u s) t = - 2 * (Q metric conn u f inv_u t) * (Q metric conn u f inv_u t + (⅟2 : R))) →
  (∀ t, Q metric conn u f inv_u t ≤ 0)


theorem harnack_inequality
  [TimeDerivative Time R] [Invertible (2 : R)] [TraceOperator R V]
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  [MetricTraceRules R V metric.toNonDegenerateMetric.toMetricTensor]
  (conn : AffineConnection R V) [MetricCompatible conn metric.toNonDegenerateMetric.toMetricTensor]
  [TorsionFree conn] [bochner_rules : BochnerTraceRules metric conn]
  (u f inv_u : Time → R)
  [heat : HeatEquation1D metric conn u f inv_u] :
  ∀ t, heat.t_val t * (metric.g (grad metric (f t)) (grad metric (f t)) - TimeDerivative.partial_t f t) ≤ (⅟2 : R) := by
  intro t
  have hQ_le_0_all : (∀ s, Q metric conn u f inv_u s ≤ 0) := max_principle metric conn u f inv_u (fun s => Q_evolution metric conn u f inv_u s)
  have hQ_le_0 : Q metric conn u f inv_u t ≤ 0 := hQ_le_0_all t

  dsimp [Q] at hQ_le_0
  have h_f_evol : TimeDerivative.partial_t f t = laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) + metric.g (grad metric (f t)) (grad metric (f t)) := f_evolution metric conn u f inv_u t

  have h_lap : metric.g (grad metric (f t)) (grad metric (f t)) - TimeDerivative.partial_t f t = - laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) := by
    calc metric.g (grad metric (f t)) (grad metric (f t)) - TimeDerivative.partial_t f t
      _ = metric.g (grad metric (f t)) (grad metric (f t)) - (laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) + metric.g (grad metric (f t)) (grad metric (f t))) := by rw [h_f_evol]
      _ = - laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) := by ring

  rw [h_lap]

  have h_goal_rw : heat.t_val t * -laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) = - heat.t_val t * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) := by ring
  rw [h_goal_rw]

  have h1 : (- heat.t_val t * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) - (⅟2 : R)) + (⅟2 : R) ≤ 0 + (⅟2 : R) := add_le_add hQ_le_0 (le_refl (⅟2 : R))
  have h2 : - heat.t_val t * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) ≤ (⅟2 : R) := by
    calc - heat.t_val t * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t)
      _ = (- heat.t_val t * laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f t) - (⅟2 : R)) + (⅟2 : R) := by abel
      _ ≤ 0 + (⅟2 : R) := h1
      _ = (⅟2 : R) := by ring

  exact h2
