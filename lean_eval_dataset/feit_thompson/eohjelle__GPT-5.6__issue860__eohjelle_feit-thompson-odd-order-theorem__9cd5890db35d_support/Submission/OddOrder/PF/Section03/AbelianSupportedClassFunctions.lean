import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.StdBasis
import Submission.OddOrder.PF.Section01.ClassFunctionSupport

/-!
Class functions supported on a subset of a finite abelian group.

Conjugation is trivial in an abelian group, so an arbitrary function on a
subset extends by zero to a class function.  This identifies the supported
class functions with the full function space on the subset and gives the
delta-function basis used in Peterfalvi, Section 3.
-/

namespace Submission.OddOrder.PF

noncomputable section

universe u v

namespace ClassFunction

variable {H : Type u} [Group H] [Fintype H] [IsMulCommutative H]
variable {k : Type v} [Field k]

local instance : DecidableEq H := Classical.decEq H
local instance (A : Set H) : DecidablePred (fun h : H ↦ h ∈ A) :=
  Classical.decPred _

/-- Restriction to `A`, viewed as a linear equivalence from class functions
supported on `A` to arbitrary functions on `A`.  The inverse extends a
function by zero. -/
def abelianSupportedEquivFun (A : Set H) :
    supportedOn (R := k) A ≃ₗ[k] (A → k) where
  toFun f a := f.1 a.1
  invFun phi :=
    ⟨⟨fun h ↦ if hh : h ∈ A then phi ⟨h, hh⟩ else 0,
        fun x h ↦ by
          have hconj : x * h * x⁻¹ = h := by
            calc
              x * h * x⁻¹ = h * (x * x⁻¹) := by ac_rfl
              _ = h := by simp
          rw [hconj]⟩,
      by
        intro h hh
        simp [hh]⟩
  left_inv f := by
    apply Subtype.ext
    apply ClassFunction.ext
    intro h
    by_cases hh : h ∈ A
    · simp [hh]
    · simpa [hh] using
        (ClassFunction.eq_zero_of_mem_supportedOn f.2 hh).symm
  right_inv phi := by
    funext a
    simp [a.2]
  map_add' f g := by
    funext a
    rfl
  map_smul' c f := by
    funext a
    rfl

omit [Fintype H] in
@[simp]
theorem abelianSupportedEquivFun_apply (A : Set H)
    (f : supportedOn (R := k) A) (a : A) :
    abelianSupportedEquivFun (k := k) A f a = f.1 a.1 :=
  rfl

omit [Fintype H] in
@[simp]
theorem abelianSupportedEquivFun_symm_apply (A : Set H) (phi : A → k) (h : H) :
    ((abelianSupportedEquivFun (k := k) A).symm phi :
        supportedOn (R := k) A).1 h =
      if hh : h ∈ A then phi ⟨h, hh⟩ else 0 :=
  rfl

/-- The canonical delta-function basis of class functions supported on `A`. -/
def abelianSupportedBasis (A : Set H) :
    Module.Basis A k (supportedOn (R := k) A) :=
  Module.Basis.ofEquivFun (abelianSupportedEquivFun (k := k) A)

@[simp]
theorem abelianSupportedBasis_apply_subtype (A : Set H) (a b : A) :
    ((abelianSupportedBasis (k := k) A a :
        supportedOn (R := k) A).1 : ClassFunction H k) b.1 =
      if a = b then 1 else 0 := by
  classical
  simp [abelianSupportedBasis, Pi.single_apply, eq_comm]

/-- Pointwise delta formula for the canonical supported basis, including
points outside the support set. -/
@[simp]
theorem abelianSupportedBasis_apply (A : Set H) (a : A) (h : H) :
    ((abelianSupportedBasis (k := k) A a :
        supportedOn (R := k) A).1 : ClassFunction H k) h =
      if h = a.1 then 1 else 0 := by
  classical
  by_cases hh : h ∈ A
  · simp [abelianSupportedBasis, Pi.single_apply, Subtype.ext_iff, eq_comm, hh]
  · have hne : h ≠ a.1 := by
      intro heq
      apply hh
      subst h
      exact a.2
    simp [abelianSupportedBasis, hh, hne]

/-- The dimension of class functions supported on `A` is the cardinality of
`A`. -/
@[simp]
theorem finrank_abelian_supportedOn (A : Set H) :
    Module.finrank k (supportedOn (R := k) A) = A.ncard := by
  letI : Fintype A := Fintype.ofFinite A
  rw [LinearEquiv.finrank_eq (abelianSupportedEquivFun (k := k) A),
    Module.finrank_fintype_fun_eq_card, Set.fintypeCard_eq_ncard]

end ClassFunction

end

end Submission.OddOrder.PF
