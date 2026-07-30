import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Submission.OddOrder.MathlibSupport.EndomorphismScalarLine

/-!
Fourier eigenbases for a freely shifted finite cyclic basis.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped BigOperators
open Module

universe u v

variable {k : Type u} {U : Type v}
variable [Field k] [AddCommGroup U] [Module k U]

/-- The Fourier vector of weight `j` associated to a basis cyclically shifted
by an operator. -/
noncomputable def cyclicOrbitFourierVector
    {h : Nat} [NeZero h] {omega : kˣ}
    (homega : IsPrimitiveRoot omega h) (b : Basis (ZMod h) k U)
    (j : ZMod h) : U :=
  ∑ i : ZMod h,
    (primitiveRootUnitWeight homega (-(j * i)) : k) • b i

/-- Every cyclic-orbit Fourier vector is nonzero. -/
theorem cyclicOrbitFourierVector_ne_zero
    {h : Nat} [NeZero h] {omega : kˣ}
    (homega : IsPrimitiveRoot omega h) (b : Basis (ZMod h) k U)
    (j : ZMod h) :
    cyclicOrbitFourierVector homega b j ≠ 0 := by
  intro hzero
  have hcoord := congrArg (fun u : U => b.repr u (0 : ZMod h)) hzero
  rw [cyclicOrbitFourierVector, b.repr_sum_self] at hcoord
  simp at hcoord

/-- If an equivalence shifts a cyclic basis by one, its Fourier vector of
weight `j` is an eigenvector with eigenvalue `omega ^ j`. -/
theorem linearEquiv_apply_cyclicOrbitFourierVector
    {h : Nat} [NeZero h] {omega : kˣ}
    (homega : IsPrimitiveRoot omega h) (b : Basis (ZMod h) k U)
    (f : U ≃ₗ[k] U) (hshift : ∀ i : ZMod h, f (b i) = b (i + 1))
    (j : ZMod h) :
    f (cyclicOrbitFourierVector homega b j) =
      (primitiveRootUnitWeight homega j : k) •
        cyclicOrbitFourierVector homega b j := by
  rw [cyclicOrbitFourierVector, map_sum]
  simp_rw [map_smul, hshift]
  rw [Finset.smul_sum]
  apply Fintype.sum_equiv (Equiv.addRight (1 : ZMod h))
  intro i
  rw [smul_smul]
  have hweight :
      primitiveRootUnitWeight homega (-(j * i)) =
        primitiveRootUnitWeight homega j *
          primitiveRootUnitWeight homega (-(j * (i + 1))) := by
    rw [← primitiveRootUnitWeight_add]
    congr 1
    ring
  rw [hweight]
  simp

/-- Fourier vectors of a cyclically shifted basis are linearly independent. -/
theorem cyclicOrbitFourierVector_linearIndependent
    {h : Nat} [NeZero h] {omega : kˣ}
    (homega : IsPrimitiveRoot omega h) (b : Basis (ZMod h) k U)
    (f : U ≃ₗ[k] U) (hshift : ∀ i : ZMod h, f (b i) = b (i + 1)) :
    LinearIndependent k (cyclicOrbitFourierVector homega b) := by
  exact Module.End.eigenvectors_linearIndependent' f.toLinearMap
    (fun j : ZMod h => (primitiveRootUnitWeight homega j : k))
    (primitiveRootUnitWeight_val_injective homega)
    (cyclicOrbitFourierVector homega b) (fun j =>
      ⟨Module.End.mem_eigenspace_iff.mpr
        (linearEquiv_apply_cyclicOrbitFourierVector homega b f hshift j),
      cyclicOrbitFourierVector_ne_zero homega b j⟩)

/-- The Fourier vectors form a basis of a freely shifted cyclic orbit. -/
noncomputable def cyclicOrbitFourierBasis
    {h : Nat} [NeZero h] {omega : kˣ}
    (homega : IsPrimitiveRoot omega h) (b : Basis (ZMod h) k U)
    (f : U ≃ₗ[k] U) (hshift : ∀ i : ZMod h, f (b i) = b (i + 1)) :
    Basis (ZMod h) k U := by
  letI : FiniteDimensional k U := b.finiteDimensional_of_finite
  exact basisOfLinearIndependentOfCardEqFinrank'
    (cyclicOrbitFourierVector homega b)
    (cyclicOrbitFourierVector_linearIndependent homega b f hshift)
    (Module.finrank_eq_card_basis b).symm

@[simp]
theorem cyclicOrbitFourierBasis_apply
    {h : Nat} [NeZero h] {omega : kˣ}
    (homega : IsPrimitiveRoot omega h) (b : Basis (ZMod h) k U)
    (f : U ≃ₗ[k] U) (hshift : ∀ i : ZMod h, f (b i) = b (i + 1))
    (j : ZMod h) :
    cyclicOrbitFourierBasis homega b f hshift j =
      cyclicOrbitFourierVector homega b j := by
  simp [cyclicOrbitFourierBasis]

/-- The one-dimensional Fourier lines span a freely shifted cyclic orbit. -/
theorem iSup_cyclicOrbitFourierLine_eq_top
    {h : Nat} [NeZero h] {omega : kˣ}
    (homega : IsPrimitiveRoot omega h) (b : Basis (ZMod h) k U)
    (f : U ≃ₗ[k] U) (hshift : ∀ i : ZMod h, f (b i) = b (i + 1)) :
    ⨆ j : ZMod h, k ∙ cyclicOrbitFourierVector homega b j = ⊤ := by
  letI : FiniteDimensional k U := b.finiteDimensional_of_finite
  rw [← Submodule.span_range_eq_iSup]
  exact (cyclicOrbitFourierVector_linearIndependent homega b f hshift).span_eq_top_of_card_eq_finrank'
    (Module.finrank_eq_card_basis b).symm

/-- Each Fourier line lies in its primitive-root eigenspace. -/
theorem cyclicOrbitFourierLine_le_eigenspace
    {h : Nat} [NeZero h] {omega : kˣ}
    (homega : IsPrimitiveRoot omega h) (b : Basis (ZMod h) k U)
    (f : U ≃ₗ[k] U) (hshift : ∀ i : ZMod h, f (b i) = b (i + 1))
    (j : ZMod h) :
    k ∙ cyclicOrbitFourierVector homega b j ≤
      Module.End.eigenspace f.toLinearMap
        (primitiveRootUnitWeight homega j : k) := by
  rw [Submodule.span_singleton_le_iff_mem, Module.End.mem_eigenspace_iff]
  exact linearEquiv_apply_cyclicOrbitFourierVector homega b f hshift j

/-- Every Fourier line in a freely shifted cyclic orbit has dimension one. -/
theorem finrank_cyclicOrbitFourierLine
    {h : Nat} [NeZero h] {omega : kˣ}
    (homega : IsPrimitiveRoot omega h) (b : Basis (ZMod h) k U)
    (j : ZMod h) :
    Module.finrank k (k ∙ cyclicOrbitFourierVector homega b j) = 1 :=
  finrank_span_singleton (cyclicOrbitFourierVector_ne_zero homega b j)

end Submission.OddOrder.MathlibSupport
