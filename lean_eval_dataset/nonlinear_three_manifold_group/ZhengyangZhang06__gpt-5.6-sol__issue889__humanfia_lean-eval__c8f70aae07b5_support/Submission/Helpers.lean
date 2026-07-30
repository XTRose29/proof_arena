import ChallengeDeps
import Submission.QuaternionObstruction

open LeanEval.Topology
open Matrix

namespace Submission.Helpers

/--
A closed three-manifold whose fundamental group contains two quaternion groups
with distinct central involutions.  This is the exact interface supplied by the
connected sum of two quaternionic spherical space forms.
-/
structure DoubleQuaternionManifoldCertificate where
  manifold : Closed3Manifold
  basepoint : manifold.carrier
  inclusion :
    (i : Bool) →
      QuaternionObstruction.Q8 →*
        FundamentalGroup manifold.carrier basepoint
  inclusion_injective :
    ∀ i, Function.Injective (inclusion i)
  centralInvolutions_ne :
    inclusion false QuaternionObstruction.centralInvolution ≠
      inclusion true QuaternionObstruction.centralInvolution

/--
Two embedded quaternion factors with distinct central involutions rule out a
faithful four-dimensional real representation.
-/
theorem DoubleQuaternionManifoldCertificate.exists_nonlinear
    (C : DoubleQuaternionManifoldCertificate) :
    ∃ (M : Closed3Manifold) (x : M.carrier),
      ∀ f : FundamentalGroup M.carrier x →* GL (Fin 4) ℝ,
        ¬ Function.Injective f := by
  refine ⟨C.manifold, C.basepoint, fun f hf ↦ ?_⟩
  let f₀ : QuaternionObstruction.Q8 →* GL (Fin 4) ℝ :=
    f.comp (C.inclusion false)
  let f₁ : QuaternionObstruction.Q8 →* GL (Fin 4) ℝ :=
    f.comp (C.inclusion true)
  have hf₀ : Function.Injective f₀ :=
    hf.comp (C.inclusion_injective false)
  have hf₁ : Function.Injective f₁ :=
    hf.comp (C.inclusion_injective true)
  have h₀ :=
    QuaternionObstruction.map_centralInvolution_eq_negOne f₀ hf₀
  have h₁ :=
    QuaternionObstruction.map_centralInvolution_eq_negOne f₁ hf₁
  apply C.centralInvolutions_ne
  apply hf
  simpa [f₀, f₁] using h₀.trans h₁.symm

end Submission.Helpers
