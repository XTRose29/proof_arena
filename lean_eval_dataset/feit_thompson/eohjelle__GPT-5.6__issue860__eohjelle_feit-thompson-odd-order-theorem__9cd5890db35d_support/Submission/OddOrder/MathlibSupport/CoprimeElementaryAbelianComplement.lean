import Mathlib.RepresentationTheory.Maschke
import Submission.OddOrder.MathlibSupport.ElementaryAbelianRepresentation
import Submission.OddOrder.MathlibSupport.ElementaryAbelianSubmodule

/-!
Maschke complements for coprime automorphisms of elementary abelian groups.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative

universe u v

variable {E : Type u} {A : Type v}
variable [Group E] [Finite E] [Group A] [Finite A]
variable {p : ℕ} [Fact p.Prime] [IsMulCommutative E]

/-- Multiplicative automorphisms of an elementary abelian group, linearized
over its prime field. -/
def elementaryAbelianMulAutRepresentation
    (E : Type u) [Group E] (p : ℕ) [IsMulCommutative E]
    [Module (ZMod p) (Additive E)] :
    Representation (ZMod p) (MulAut E) (Additive E) where
  toFun f :=
    (MonoidHom.toAdditive f.toMonoidHom).toZModLinearMap p
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

/-- An action through multiplicative automorphisms, linearized over the
prime field of the acted-on elementary abelian group. -/
def elementaryAbelianActionRepresentation
    (E : Type u) (A : Type v) [Group E] [Group A]
    (p : ℕ) [IsMulCommutative E]
    [Module (ZMod p) (Additive E)] (f : A →* MulAut E) :
    Representation (ZMod p) A (Additive E) where
  toFun a :=
    (MonoidHom.toAdditive (f a).toMonoidHom).toZModLinearMap p
  map_one' := by
    apply LinearMap.ext
    intro x
    change Additive.ofMul ((f 1) x.toMul) = x
    simp
  map_mul' := by
    intro a b
    apply LinearMap.ext
    intro x
    change Additive.ofMul ((f (a * b)) x.toMul) =
      Additive.ofMul ((f a) ((f b) x.toMul))
    simp

private theorem exists_invariant_complement_of_coprime_mulAut_action_of_module
    [Module (ZMod p) (Additive E)]
    (f : A →* MulAut E) (hpA : ¬p ∣ Nat.card A)
    (U : Subgroup E)
    (hU : ∀ a : A, U.map (f a).toMonoidHom = U) :
    ∃ X : Subgroup E, IsCompl U X ∧
      ∀ a : A, X.map (f a).toMonoidHom = X := by
  classical
  let W : Submodule (ZMod p) (Additive E) :=
    AddSubgroup.toZModSubmodule p U.toAddSubgroup
  let rho : Representation (ZMod p) A (Additive E) :=
    elementaryAbelianActionRepresentation E A p f
  let sigma : Subrepresentation rho :=
    { toSubmodule := W
      apply_mem_toSubmodule := by
        intro a x hx
        change Additive.ofMul (f a x.toMul) ∈ W
        have hxU : x.toMul ∈ U := by
          change Additive.ofMul x.toMul ∈ W at hx
          exact hx
        have hmemMap : f a x.toMul ∈ U.map (f a).toMonoidHom :=
          ⟨x.toMul, hxU, rfl⟩
        rw [hU a] at hmemMap
        exact hmemMap }
  letI : NeZero (Nat.card A : ZMod p) :=
    NeZero.of_not_dvd (ZMod p) hpA
  letI : Representation.IsSemisimpleRepresentation rho := by infer_instance
  obtain ⟨tau, htau⟩ := exists_isCompl sigma
  let X : Subgroup E :=
    AddSubgroup.toSubgroup' tau.toSubmodule.toAddSubgroup
  have hcomplSub : IsCompl W tau.toSubmodule := by
    rw [isCompl_iff] at htau ⊢
    constructor
    · rw [disjoint_iff] at htau ⊢
      have h := congrArg Subrepresentation.toSubmodule htau.1
      exact h
    · rw [codisjoint_iff] at htau ⊢
      have h := congrArg Subrepresentation.toSubmodule htau.2
      exact h
  have hcompl : IsCompl U X := by
    have hcomplAdd :
        IsCompl W.toAddSubgroup tau.toSubmodule.toAddSubgroup :=
      (AddSubgroup.toZModSubmodule p).symm.isCompl hcomplSub
    have hmapped : IsCompl
        (AddSubgroup.toSubgroup' W.toAddSubgroup)
        (AddSubgroup.toSubgroup' tau.toSubmodule.toAddSubgroup) :=
      AddSubgroup.toSubgroup'.isCompl hcomplAdd
    simpa [W, X] using hmapped
  refine ⟨X, hcompl, ?_⟩
  intro a
  apply Subgroup.eq_of_le_of_card_ge
  · rintro y ⟨x, hx, rfl⟩
    change Additive.ofMul (f a x) ∈ tau.toSubmodule
    have hx' : Additive.ofMul x ∈ tau.toSubmodule := hx
    exact tau.apply_mem_toSubmodule a hx'
  · rw [Subgroup.card_map_of_injective (f a).injective]

/-- An invariant subgroup of an elementary abelian `p`-group has an
invariant complement under an action whose order is prime to `p`. -/
theorem exists_invariant_complement_of_coprime_mulAut_action
    (hpow : ∀ x : E, x ^ p = 1)
    (f : A →* MulAut E) (hpA : ¬p ∣ Nat.card A)
    (U : Subgroup E)
    (hU : ∀ a : A, U.map (f a).toMonoidHom = U) :
    ∃ X : Subgroup E, IsCompl U X ∧
      ∀ a : A, X.map (f a).toMonoidHom = X := by
  letI : Module (ZMod p) (Additive E) :=
    AddCommGroup.zmodModule fun x ↦ by
      change x.toMul ^ p = 1
      exact hpow x.toMul
  exact exists_invariant_complement_of_coprime_mulAut_action_of_module
    (p := p) f hpA U hU

end Submission.OddOrder.MathlibSupport
