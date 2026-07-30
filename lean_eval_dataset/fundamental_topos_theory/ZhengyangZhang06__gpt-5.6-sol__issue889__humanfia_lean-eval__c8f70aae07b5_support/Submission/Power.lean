import Submission.Helpers

open CategoryTheory CategoryTheory.Limits

namespace Submission.Power

noncomputable section

universe u v

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
  [HasSubobjectClassifier C]

/-- A representing object for predicates on `B`. -/
class IsPower {B PB : C} (membership : B ⨯ PB ⟶ HasSubobjectClassifier.Ω C) where
  transpose {A : C} (f : B ⨯ A ⟶ HasSubobjectClassifier.Ω C) : A ⟶ PB
  comm {A : C} (f : B ⨯ A ⟶ HasSubobjectClassifier.Ω C) :
    prod.map (𝟙 B) (transpose f) ≫ membership = f
  uniq {A : C} {f : B ⨯ A ⟶ HasSubobjectClassifier.Ω C} {g : A ⟶ PB}
    (hg : prod.map (𝟙 B) g ≫ membership = f) : transpose f = g

/-- A chosen power object for `B`. -/
class HasPower (B : C) where
  pow : C
  membership : B ⨯ pow ⟶ HasSubobjectClassifier.Ω C
  isPower : IsPower membership

/-- Chosen power objects for every object of a category. -/
class HasPowers (C : Type u) [Category.{v} C] [HasFiniteLimits C]
    [HasSubobjectClassifier C] where
  hasPower (B : C) : HasPower B

attribute [instance_reducible, instance] HasPowers.hasPower

abbrev pow (B : C) [HasPower B] : C := HasPower.pow B

abbrev membership (B : C) [HasPower B] :
    B ⨯ pow B ⟶ HasSubobjectClassifier.Ω C :=
  (inferInstance : HasPower B).membership

def transpose {A B : C} [HasPower B]
    (f : B ⨯ A ⟶ HasSubobjectClassifier.Ω C) : A ⟶ pow B :=
  (inferInstance : HasPower B).isPower.transpose f

@[reassoc]
lemma transpose_comm {A B : C} [HasPower B]
    (f : B ⨯ A ⟶ HasSubobjectClassifier.Ω C) :
    prod.map (𝟙 B) (transpose f) ≫ membership B = f :=
  (inferInstance : HasPower B).isPower.comm f

lemma transpose_unique {A B : C} [HasPower B]
    {f : B ⨯ A ⟶ HasSubobjectClassifier.Ω C} {g : A ⟶ pow B}
    (hg : prod.map (𝟙 B) g ≫ membership B = f) : transpose f = g :=
  (inferInstance : HasPower B).isPower.uniq hg

def transposeEquiv (A B : C) [HasPower B] :
    (B ⨯ A ⟶ HasSubobjectClassifier.Ω C) ≃ (A ⟶ pow B) where
  toFun := transpose
  invFun := fun g ↦ prod.map (𝟙 B) g ≫ membership B
  left_inv := transpose_comm
  right_inv := fun g ↦ by
    apply transpose_unique (g := g)
    rfl

section Closed

variable [CartesianMonoidalCategory C] [MonoidalClosed C]

/-- The adjunction between product by `B` and the internal hom out of `B`. -/
def prodIhomAdjunction (B : C) : prod.functor.obj B ⊣ CategoryTheory.ihom B :=
  (CategoryTheory.ihom.adjunction B).ofNatIsoLeft
    (CartesianMonoidalCategory.tensorLeftIsoProd B)

/-- In a cartesian closed category, `Ω^B` is a power object for `B`. -/
@[implicit_reducible]
def closedHasPower (B : C) : HasPower B where
  pow := (CategoryTheory.ihom B).obj (HasSubobjectClassifier.Ω C)
  membership := (prodIhomAdjunction B).counit.app (HasSubobjectClassifier.Ω C)
  isPower := {
    transpose := fun f ↦ (prodIhomAdjunction B).homEquiv _ _ f
    comm := fun f ↦ by
      change ((prodIhomAdjunction B).homEquiv _ _).symm
        ((prodIhomAdjunction B).homEquiv _ _ f) = f
      exact Equiv.symm_apply_apply _ f
    uniq := fun {A} {f} {g} hg ↦ by
      apply ((prodIhomAdjunction B).homEquiv A _).apply_eq_iff_eq_symm_apply.2
      change f = prod.map (𝟙 B) g ≫
        (prodIhomAdjunction B).counit.app (HasSubobjectClassifier.Ω C)
      exact hg.symm }

/-- Cartesian closed categories with a classifier have power objects. -/
@[implicit_reducible]
def closedHasPowers : HasPowers C where
  hasPower := closedHasPower

end Closed

end

end Submission.Power
