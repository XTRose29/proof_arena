import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Submission.OddOrder.MathlibSupport.PrimitiveRootMatrixConjugation

/-!
Primitive-root eigenspace decompositions for finite-order operators.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v

variable {k : Type u} {V : Type v}
variable [Field k] [AddCommGroup V] [Module k V]

@[simp]
theorem primitiveRootUnitWeight_natCast
    {h : Nat} {omega : kˣ} (homega : IsPrimitiveRoot omega h)
    (i : Nat) :
    primitiveRootUnitWeight homega (i : ZMod h) = omega ^ i := by
  apply Units.ext
  simp [primitiveRootUnitWeight,
    homega.zmodEquivZPowers_apply_coe_nat]

/-- If an endomorphism has order dividing `h`, its eigenspaces indexed by
the powers of a primitive `h`-th root span the whole space. -/
theorem iSup_primitiveRootUnitWeight_eigenspace_eq_top
    {h : Nat} [NeZero h] {omega : kˣ}
    (homega : IsPrimitiveRoot omega h) [IsAlgClosed k]
    [FiniteDimensional k V] (f : Module.End k V)
    (hpow : f ^ h = 1) :
    ⨆ i : ZMod h,
      Module.End.eigenspace f
        (primitiveRootUnitWeight homega i : k) = ⊤ := by
  have homegaVal : IsPrimitiveRoot (omega : k) h :=
    IsPrimitiveRoot.coe_units_iff.mpr homega
  letI : NeZero (h : k) := homegaVal.neZero'
  have hsemisimple : f.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero
      (Polynomial.X_pow_sub_one_separable_iff.mpr
        (NeZero.ne (h : k))).squarefree
      (by simp [hpow])
  rw [eq_top_iff, ← hsemisimple.iSup_eigenspace_eq_top]
  refine iSup_le fun mu => ?_
  by_cases hmu : f.HasEigenvalue mu
  · obtain ⟨v, hv⟩ := hmu.exists_hasEigenvector
    have hvpow : v = mu ^ h • v := by
      simpa [hpow] using hv.pow_apply h
    have hmuPow : mu ^ h = 1 := by
      have hzero : (1 - mu ^ h) • v = 0 := by
        rw [sub_smul, one_smul, sub_eq_zero]
        exact hvpow
      exact (sub_eq_zero.mp
        ((smul_eq_zero.mp hzero).resolve_right hv.2)).symm
    obtain ⟨i, -, hi⟩ := homegaVal.eq_pow_of_pow_eq_one hmuPow
    rw [← hi, ← Units.val_pow_eq_pow_val,
      ← primitiveRootUnitWeight_natCast homega i]
    exact le_iSup
      (fun j : ZMod h =>
        Module.End.eigenspace f
          (primitiveRootUnitWeight homega j : k)) (i : ZMod h)
  · have hbot : Module.End.eigenspace f mu = ⊥ := not_ne_iff.mp hmu
    rw [hbot]
    exact bot_le

end Submission.OddOrder.MathlibSupport
