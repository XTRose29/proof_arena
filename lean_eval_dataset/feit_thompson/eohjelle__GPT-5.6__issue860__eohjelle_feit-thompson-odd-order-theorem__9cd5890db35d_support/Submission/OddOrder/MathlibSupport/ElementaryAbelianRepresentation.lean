import Submission.OddOrder.MathlibSupport.MinimalNormalElementaryAbelian
import Mathlib.Algebra.Module.ZMod
import Mathlib.RepresentationTheory.Basic

/-!
The conjugation representation on an elementary abelian normal subgroup.

This is the mathlib-facing replacement for the `abelem_repr` construction
used in the representation-theoretic part of `BGappendixAB.odd_p_stable`.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative

variable {G : Type*} [Group G]
variable (E : Subgroup G)

/-- The canonical `ZMod p`-module structure on the additive form of an
abelian group of exponent `p`. -/
abbrev elementaryAbelianZModModule (p : ℕ) [IsMulCommutative E]
    (hpow : ∀ x : E, x ^ p = 1) : Module (ZMod p) (Additive E) :=
  AddCommGroup.zmodModule fun x ↦ by
    change x.toMul ^ p = 1
    exact hpow x.toMul

/-- Conjugation by the normalizer, regarded as a linear representation on
the elementary abelian subgroup. -/
def normalizerConjugationRepresentation (p : ℕ) [IsMulCommutative E]
    [Module (ZMod p) (Additive E)] :
    Representation (ZMod p) (Subgroup.normalizer (E : Set G)) (Additive E) where
  toFun g :=
    (MonoidHom.toAdditive (E.normalizerMonoidHom g).toMonoidHom).toZModLinearMap p
  map_one' := by
    apply LinearMap.ext
    intro x
    change Additive.ofMul ((E.normalizerMonoidHom 1) x.toMul) = x
    simp
  map_mul' := by
    intro x y
    apply LinearMap.ext
    intro z
    change Additive.ofMul ((E.normalizerMonoidHom (x * y)) z.toMul) =
      Additive.ofMul ((E.normalizerMonoidHom x) ((E.normalizerMonoidHom y) z.toMul))
    simp

@[simp]
theorem normalizerConjugationRepresentation_apply
    (p : ℕ) [IsMulCommutative E] [Module (ZMod p) (Additive E)]
    (g : Subgroup.normalizer (E : Set G)) (x : Additive E) :
    normalizerConjugationRepresentation E p g x =
      Additive.ofMul (g • x.toMul) :=
  rfl

/-- The kernel of the conjugation representation is the centralizer of `E`
inside its normalizer. -/
theorem normalizerConjugationRepresentation_ker
    (p : ℕ) [IsMulCommutative E] [Module (ZMod p) (Additive E)] :
    (normalizerConjugationRepresentation E p).ker =
      (Subgroup.centralizer E).subgroupOf (Subgroup.normalizer (E : Set G)) := by
  rw [← E.normalizerMonoidHom_ker]
  ext g
  simp only [MonoidHom.mem_ker]
  constructor
  · intro hg
    apply MulEquiv.ext
    intro x
    have h := LinearMap.congr_fun hg (Additive.ofMul x)
    exact congrArg Additive.toMul h
  · intro hg
    apply LinearMap.ext
    intro x
    have h := DFunLike.congr_fun hg x.toMul
    exact congrArg Additive.ofMul h

/-- Every multiplicative automorphism of an elementary abelian group is
`ZMod p`-linear on its additive form. -/
def mulAutRepresentation (p : ℕ) [IsMulCommutative E]
    [Module (ZMod p) (Additive E)] :
    Representation (ZMod p) (MulAut E) (Additive E) where
  toFun f := (MonoidHom.toAdditive f.toMonoidHom).toZModLinearMap p
  map_one' := by
    apply LinearMap.ext
    intro x
    change Additive.ofMul ((1 : MulAut E) x.toMul) = x
    simp
  map_mul' := by
    intro f g
    apply LinearMap.ext
    intro x
    change Additive.ofMul ((f * g) x.toMul) =
      Additive.ofMul (f (g x.toMul))
    rfl

@[simp]
theorem mulAutRepresentation_apply
    (p : ℕ) [IsMulCommutative E] [Module (ZMod p) (Additive E)]
    (f : MulAut E) (x : Additive E) :
    mulAutRepresentation E p f x = Additive.ofMul (f x.toMul) :=
  rfl

/-- The linearization of multiplicative automorphisms is faithful. -/
theorem mulAutRepresentation_injective
    (p : ℕ) [IsMulCommutative E] [Module (ZMod p) (Additive E)] :
    Function.Injective (mulAutRepresentation E p) := by
  intro f g hfg
  apply MulEquiv.ext
  intro x
  have hx := LinearMap.congr_fun hfg (Additive.ofMul x)
  exact congrArg Additive.toMul hx

/-- The associated homomorphism into the general linear group is faithful. -/
theorem mulAutRepresentation_asGroupHom_injective
    (p : ℕ) [IsMulCommutative E] [Module (ZMod p) (Additive E)] :
    Function.Injective (mulAutRepresentation E p).asGroupHom := by
  intro f g hfg
  apply mulAutRepresentation_injective E p
  exact Units.ext_iff.mp hfg

end Submission.OddOrder.MathlibSupport
