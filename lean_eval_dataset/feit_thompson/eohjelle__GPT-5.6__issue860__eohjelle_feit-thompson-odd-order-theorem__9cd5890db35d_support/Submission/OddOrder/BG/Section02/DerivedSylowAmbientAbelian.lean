import Submission.OddOrder.BG.Section02.DerivedSylowAmbientLineFixing
import Submission.OddOrder.MathlibSupport.ComplementaryLineCommuting

/-!
The abelian-image conclusion after `redG` in
`BGsection2.der1_odd_GL2_charf`.
-/

namespace Submission.OddOrder.BG.Section02

open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative MonoidAlgebra

universe u v w

variable {F : Type v} {G : Type u} {V : Type w}
  [Field F] [Group G] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

/-- Once the odd ambient action fixes both complementary derived-Sylow
eigenlines, its faithful two-dimensional representation has abelian image and
the ambient group itself is commutative. -/
theorem ambient_isMulCommutative_of_derivedSylow_lines
    {q : ℕ} (hodd : Odd (Nat.card G))
    (rho : Representation F G V) (hrho : Function.Injective rho)
    (Q : Sylow q G) (hN : (derivedSylowPart Q).Normal)
    (m n : Submodule F[derivedSylowPart Q]
      (derivedSylowRepresentation rho Q).asModule)
    (hmn : IsCompl m n) (x : derivedSylowPart Q) (a b : F)
    (hma : invariantLineAction (derivedSylowRepresentation rho Q) m x =
      a • LinearMap.id)
    (hna : invariantLineAction (derivedSylowRepresentation rho Q) n x =
      b • LinearMap.id)
    (hab : a ≠ b)
    (hmdim : Module.finrank F (m.restrictScalars F) = 1)
    (hndim : Module.finrank F (n.restrictScalars F) = 1) :
    IsMulCommutative G := by
  let N := derivedSylowPart Q
  let sigma := subgroupRepresentation rho N
  let U : Submodule F sigma.asModule := m.restrictScalars F
  let W : Submodule F sigma.asModule := n.restrictScalars F
  let phi := subgroupModuleAmbientLinearEquivHom rho N
  have hmnF : IsCompl U W :=
    (Submodule.isCompl_restrictScalars_iff F).mpr hmn
  have hfix := derivedSylow_lines_fixed_by_ambient
    hodd rho Q hN m n hmn x a b hma hna hab hmdim hndim
  have hpreserve (y : G) :
      U ≤ U.comap (phi y).toLinearMap ∧
        W ≤ W.comap (phi y).toLinearMap := by
    have hy := hfix y
    change U.map (phi y).toLinearMap = U ∧
      W.map (phi y).toLinearMap = W at hy
    exact ⟨Submodule.map_le_iff_le_comap.mp hy.1.le,
      Submodule.map_le_iff_le_comap.mp hy.2.le⟩
  have hcomm (y z : G) :
      Commute (phi y).toLinearMap (phi z).toLinearMap :=
    commute_of_preserves_complementary_lines U W hmnF hmdim hndim
      (phi y).toLinearMap (phi z).toLinearMap
      (hpreserve y).1 (hpreserve y).2 (hpreserve z).1 (hpreserve z).2
  have hrhoComm (y z : G) : Commute (rho y) (rho z) := by
    apply LinearMap.ext
    intro v
    let u : sigma.asModule := sigma.asModuleEquiv.symm v
    have hu := LinearMap.congr_fun (hcomm y z).eq u
    have hu' := congrArg sigma.asModuleEquiv hu
    simpa [u, phi, N, sigma, Module.End.mul_apply] using hu'
  refine ⟨⟨fun y z ↦ ?_⟩⟩
  apply hrho
  rw [map_mul, map_mul]
  exact (hrhoComm y z).eq

/-- The ambient commutator is trivial in the diagonal-image branch. -/
theorem ambient_commutator_eq_bot_of_derivedSylow_lines
    {q : ℕ} (hodd : Odd (Nat.card G))
    (rho : Representation F G V) (hrho : Function.Injective rho)
    (Q : Sylow q G) (hN : (derivedSylowPart Q).Normal)
    (m n : Submodule F[derivedSylowPart Q]
      (derivedSylowRepresentation rho Q).asModule)
    (hmn : IsCompl m n) (x : derivedSylowPart Q) (a b : F)
    (hma : invariantLineAction (derivedSylowRepresentation rho Q) m x =
      a • LinearMap.id)
    (hna : invariantLineAction (derivedSylowRepresentation rho Q) n x =
      b • LinearMap.id)
    (hab : a ≠ b)
    (hmdim : Module.finrank F (m.restrictScalars F) = 1)
    (hndim : Module.finrank F (n.restrictScalars F) = 1) :
    _root_.commutator G = ⊥ := by
  letI : IsMulCommutative G :=
    ambient_isMulCommutative_of_derivedSylow_lines
      hodd rho hrho Q hN m n hmn x a b hma hna hab hmdim hndim
  exact _root_.commutator_eq_bot G

end Submission.OddOrder.BG.Section02
