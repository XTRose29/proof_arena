import Submission.OddOrder.MathlibSupport.IrreducibleHallExtensionFDRep
import Submission.OddOrder.MathlibSupport.RepresentationBurnsideDensity
import Submission.OddOrder.PF.Section01.QuotientDescent

/-!
# Translation kernels of irreducible characters

For an irreducible character, the source development's `cfker` agrees with
the kernel of any representation realizing that character.  The nontrivial
direction uses Burnside density and the nondegeneracy of the trace pairing on
the full endomorphism algebra.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped MonoidAlgebra
open CategoryTheory

universe u

namespace ClassFunction

variable {G k : Type u} [Group G]
  [Field k] [IsAlgClosed k]

/-- For an irreducible character, left-translation invariance is equivalent
to acting trivially in its chosen realizing representation. -/
theorem translationKernel_irreducibleCharacter
    (chi : IrreducibleCharacter G k) :
    translationKernel (chi : ClassFunction G k) =
      chi.representation.ρ.ker := by
  apply le_antisymm
  · intro a ha
    rw [MonoidHom.mem_ker]
    let rho : Representation k G chi.representation :=
      chi.representation.ρ
    letI : Simple chi.representation := chi.representation_simple
    letI : Representation.IsIrreducible rho :=
      _root_.Submission.OddOrder.MathlibSupport.representation_isIrreducible_of_simple_fdRep
        chi.representation
    have htraceGroup (g : G) :
        LinearMap.trace k chi.representation
            ((rho a - 1) * rho g) = 0 := by
      rw [sub_mul, one_mul, map_sub, ← rho.map_mul]
      change rho.character (a * g) - rho.character g = 0
      dsimp only [rho]
      change chi.representation.character (a * g) -
        chi.representation.character g = 0
      rw [chi.representation_character, chi.representation_character]
      exact sub_eq_zero.mpr (ha g)
    have htraceAlgebra (z : k[G]) :
        LinearMap.trace k chi.representation
            ((rho a - 1) * rho.asAlgebraHom z) = 0 := by
      induction z using MonoidAlgebra.induction_on with
      | hM g =>
          simpa only [Representation.asAlgebraHom_of] using htraceGroup g
      | hadd x y hx hy =>
          simp only [map_add, mul_add, hx, hy, add_zero]
      | hsmul c x hx =>
          simp only [map_smul, mul_smul_comm, hx, smul_zero]
    have htraceEnd (X : Module.End k chi.representation) :
        LinearMap.trace k chi.representation ((rho a - 1) * X) = 0 := by
      obtain ⟨z, rfl⟩ :=
        _root_.Submission.OddOrder.MathlibSupport.Representation.IsIrreducible.asAlgebraHom_surjective
          rho X
      exact htraceAlgebra z
    have hzero : rho a - 1 = 0 := by
      let b := Module.finBasis k chi.representation
      apply (LinearMap.toMatrixAlgEquiv b).injective
      rw [map_zero]
      apply (Matrix.ext_iff_trace_mul_right).2
      intro X
      have hX := htraceEnd ((LinearMap.toMatrixAlgEquiv b).symm X)
      rw [LinearMap.trace_eq_matrix_trace k b] at hX
      change
        ((LinearMap.toMatrixAlgEquiv b)
            ((rho a - 1) * (LinearMap.toMatrixAlgEquiv b).symm X)).trace = 0
        at hX
      simpa only [map_mul, AlgEquiv.apply_symm_apply, Matrix.zero_mul,
        Matrix.trace_zero] using hX
    exact sub_eq_zero.mp hzero
  · intro a ha g
    rw [← chi.representation_character,
      ← chi.representation_character]
    change LinearMap.trace k chi.representation
        (chi.representation.ρ (a * g)) =
      LinearMap.trace k chi.representation (chi.representation.ρ g)
    rw [chi.representation.ρ.map_mul, MonoidHom.mem_ker.mp ha, one_mul]

end ClassFunction

end

end Submission.OddOrder.PF
