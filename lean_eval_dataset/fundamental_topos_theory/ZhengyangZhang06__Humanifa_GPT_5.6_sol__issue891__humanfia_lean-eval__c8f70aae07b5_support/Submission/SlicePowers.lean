import Submission.Exponentials
import Mathlib.CategoryTheory.Subobject.Lattice

open CategoryTheory CategoryTheory.Limits

namespace Submission.SlicePowers

noncomputable section

universe u v

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
  [HasSubobjectClassifier C]

abbrev c : Subobject.Classifier C := Exponentials.classifier

/-- The subobject classified by a predicate. -/
def classified {D : C} (φ : D ⟶ HasSubobjectClassifier.Ω C) : Subobject D :=
  (c (C := C)).representableBy.homEquiv φ

lemma classified_comp {D D' : C} (f : D' ⟶ D)
    (φ : D ⟶ HasSubobjectClassifier.Ω C) :
    classified (f ≫ φ) = (Subobject.pullback f).obj (classified φ) := by
  exact (c (C := C)).representableBy.homEquiv_comp f φ

lemma classified_characteristic {U D : C} (m : U ⟶ D) [Mono m] :
    classified ((c (C := C)).χ m) = Subobject.mk m := by
  change (Subobject.pullback ((c (C := C)).χ m)).obj
    (c (C := C)).truth_as_subobject = Subobject.mk m
  exact (c (C := C)).pullback_χ_obj_mk_truth m

variable [Power.HasPowers C]

/-- The relation on `B` represented by a generalized subset `s`. -/
def relation {A B : C} (s : A ⟶ Power.pow B) : Subobject (B ⨯ A) :=
  classified (prod.map (𝟙 B) s ≫ Power.membership B)

/-- The predicate saying that an element belongs to both of two generalized subsets. -/
def intersectionPredicate (B : C) :
    B ⨯ (Power.pow B ⨯ Power.pow B) ⟶ HasSubobjectClassifier.Ω C :=
  (c (C := C)).representableBy.homEquiv.symm
    ((Subobject.inf.obj
      ((Subobject.pullback (prod.map (𝟙 B) prod.fst)).obj
        (classified (Power.membership B)))).obj
      ((Subobject.pullback (prod.map (𝟙 B) prod.snd)).obj
        (classified (Power.membership B))))

/-- Intersection of generalized subsets. -/
def intersection (B : C) : Power.pow B ⨯ Power.pow B ⟶ Power.pow B :=
  Power.transpose (intersectionPredicate B)

lemma relation_intersection {A B : C} (s t : A ⟶ Power.pow B) :
    relation (prod.lift s t ≫ intersection B) = relation s ⊓ relation t := by
  rw [relation, relation, relation]
  rw [prod.map_id_comp, Category.assoc, intersection, Power.transpose_comm, classified_comp]
  rw [intersectionPredicate, classified, Equiv.apply_symm_apply]
  rw [← Subobject.inf_def, Subobject.inf_pullback, classified_comp, classified_comp]
  apply congrArg₂ (fun p q : Subobject (B ⨯ A) ↦ p ⊓ q)
  · rw [← Subobject.pullback_comp]
    have h :
        prod.map (𝟙 B) (prod.lift s t) ≫ prod.map (𝟙 B) prod.fst = prod.map (𝟙 B) s := by
      apply prod.hom_ext
      · simp
      · calc
          (prod.map (𝟙 B) (prod.lift s t) ≫ prod.map (𝟙 B) prod.fst) ≫ prod.snd =
              prod.map (𝟙 B) (prod.lift s t) ≫ (prod.map (𝟙 B) prod.fst ≫ prod.snd) :=
            Category.assoc _ _ _
          _ = prod.map (𝟙 B) (prod.lift s t) ≫ (prod.snd ≫ prod.fst) := by
            rw [prod.map_snd]
          _ = (prod.map (𝟙 B) (prod.lift s t) ≫ prod.snd) ≫ prod.fst := by
            rw [Category.assoc]
          _ = (prod.snd ≫ prod.lift s t) ≫ prod.fst := by rw [prod.map_snd]
          _ = prod.snd ≫ (prod.lift s t ≫ prod.fst) := Category.assoc _ _ _
          _ = prod.snd ≫ s := by rw [prod.lift_fst]
          _ = prod.map (𝟙 B) s ≫ prod.snd := (prod.map_snd _ _).symm
    rw [h]
  · rw [← Subobject.pullback_comp]
    have h :
        prod.map (𝟙 B) (prod.lift s t) ≫ prod.map (𝟙 B) prod.snd = prod.map (𝟙 B) t := by
      apply prod.hom_ext
      · simp
      · calc
          (prod.map (𝟙 B) (prod.lift s t) ≫ prod.map (𝟙 B) prod.snd) ≫ prod.snd =
              prod.map (𝟙 B) (prod.lift s t) ≫ (prod.map (𝟙 B) prod.snd ≫ prod.snd) :=
            Category.assoc _ _ _
          _ = prod.map (𝟙 B) (prod.lift s t) ≫ (prod.snd ≫ prod.snd) := by
            rw [prod.map_snd]
          _ = (prod.map (𝟙 B) (prod.lift s t) ≫ prod.snd) ≫ prod.snd := by
            rw [Category.assoc]
          _ = (prod.snd ≫ prod.lift s t) ≫ prod.snd := by rw [prod.map_snd]
          _ = prod.snd ≫ (prod.lift s t ≫ prod.snd) := Category.assoc _ _ _
          _ = prod.snd ≫ t := by rw [prod.lift_snd]
          _ = prod.map (𝟙 B) t ≫ prod.snd := (prod.map_snd _ _).symm
    rw [h]

/-- The locally constructed classifier instance on a slice. -/
instance overHasSubobjectClassifier (X : C) : HasSubobjectClassifier (Over X) :=
  ⟨⟨Helpers.classifierOver X⟩⟩

variable {X : C}

abbrev chosenOverClassifier (X : C) : Subobject.Classifier (Over X) :=
  HasSubobjectClassifier.exists_classifier.some

def overClassifierIso (X : C) :
    (chosenOverClassifier X).Ω ≅ (Helpers.classifierOver X).Ω :=
  (chosenOverClassifier X).uniqueUpToIso (Helpers.classifierOver X)

/-- The relation `b` lies over `x`. -/
def fiberRelation (B : Over X) : Subobject (B.left ⨯ X) :=
  equalizerSubobject (prod.fst ≫ B.hom) prod.snd

/-- The family of fibers of `B`, regarded as generalized subsets of `B.left`. -/
def fiberName (B : Over X) : X ⟶ Power.pow B.left :=
  Power.transpose ((c (C := C)).χ (equalizer.ι (prod.fst ≫ B.hom) prod.snd))

lemma relation_fiberName (B : Over X) :
    relation (fiberName B) = fiberRelation B := by
  rw [relation, fiberName, Power.transpose_comm]
  exact classified_characteristic _

lemma relation_comp {A A' B : C} (f : A' ⟶ A) (s : A ⟶ Power.pow B) :
    relation (f ≫ s) = (Subobject.pullback (prod.map (𝟙 B) f)).obj (relation s) := by
  rw [relation, relation, prod.map_id_comp, Category.assoc, classified_comp]

lemma relation_injective {A B : C} : Function.Injective (relation : (A ⟶ Power.pow B) → _) := by
  intro s t h
  exact (Power.transposeEquiv A B).symm.injective
    ((c (C := C)).representableBy.homEquiv.injective h)

/-- The underlying morphism from a product in the slice to the ordinary product. -/
def overProdComparison (B A : Over X) : (B ⨯ A).left ⟶ B.left ⨯ A.left :=
  prod.lift (prod.fst : B ⨯ A ⟶ B).left (prod.snd : B ⨯ A ⟶ A).left

omit [HasSubobjectClassifier C] [Power.HasPowers C] in
@[reassoc (attr := simp)]
lemma overProdComparison_fst (B A : Over X) :
    overProdComparison B A ≫ prod.fst = (prod.fst : B ⨯ A ⟶ B).left :=
  prod.lift_fst _ _

omit [HasSubobjectClassifier C] [Power.HasPowers C] in
@[reassoc (attr := simp)]
lemma overProdComparison_snd (B A : Over X) :
    overProdComparison B A ≫ prod.snd = (prod.snd : B ⨯ A ⟶ A).left :=
  prod.lift_snd _ _

instance overProdComparison_mono (B A : Over X) : Mono (overProdComparison B A) where
  right_cancellation := by
    intro Z f g h
    have hfst := congrArg (fun k ↦ k ≫ prod.fst) h
    have hsnd := congrArg (fun k ↦ k ≫ prod.snd) h
    apply (cancel_mono (Over.prodLeftIsoPullback B A).hom).1
    apply pullback.hom_ext
    · simpa only [Category.assoc, Over.prodLeftIsoPullback_hom_fst,
        overProdComparison_fst] using hfst
    · simpa only [Category.assoc, Over.prodLeftIsoPullback_hom_snd,
        overProdComparison_snd] using hsnd

/-- The equalizer relation expressing that the two components lie over the same point. -/
def sameFiberRelation (B A : Over X) : Subobject (B.left ⨯ A.left) :=
  equalizerSubobject (prod.fst ≫ B.hom) (prod.snd ≫ A.hom)

lemma relation_fiberAt (B A : Over X) :
    relation (A.hom ≫ fiberName B) = sameFiberRelation B A := by
  rw [relation_comp, relation_fiberName, fiberRelation, sameFiberRelation,
    pullback_equalizer]
  congr 1 <;> simp

/-- Ambient pairs consisting of a generalized subset of `B.left` and a point of `X`. -/
abbrev ambient (B : Over X) : C := Power.pow B.left ⨯ X

/-- Restrict an ambient generalized subset to the indicated fiber. -/
def restrictToFiber (B : Over X) : ambient B ⟶ Power.pow B.left :=
  prod.lift prod.fst (prod.snd ≫ fiberName B) ≫ intersection B.left

/-- The object of generalized subsets which are entirely contained in the indicated fiber. -/
def boundedPower (B : Over X) : Over X :=
  Over.mk
    (equalizer.ι (prod.fst : ambient B ⟶ Power.pow B.left) (restrictToFiber B) ≫ prod.snd)

@[simp] lemma boundedPower_left (B : Over X) :
    (boundedPower B).left =
      equalizer (prod.fst : ambient B ⟶ Power.pow B.left) (restrictToFiber B) := rfl

@[simp] lemma boundedPower_hom (B : Over X) :
    (boundedPower B).hom =
      equalizer.ι (prod.fst : ambient B ⟶ Power.pow B.left) (restrictToFiber B) ≫
        prod.snd := rfl

/-- The generalized subset carried by a point of `boundedPower B`. -/
def boundedSubset (B : Over X) : (boundedPower B).left ⟶ Power.pow B.left :=
  equalizer.ι (prod.fst : ambient B ⟶ Power.pow B.left) (restrictToFiber B) ≫ prod.fst

/-- The membership predicate valued in the explicit slice classifier. -/
def explicitBoundedMembership (B : Over X) :
    B ⨯ boundedPower B ⟶ (Helpers.classifierOver X).Ω := by
  let φ : (B ⨯ boundedPower B).left ⟶ HasSubobjectClassifier.Ω C :=
    prod.lift (prod.fst : B ⨯ boundedPower B ⟶ B).left
        ((prod.snd : B ⨯ boundedPower B ⟶ boundedPower B).left ≫ boundedSubset B) ≫
      Power.membership B.left
  exact Over.homMk (prod.lift φ (B ⨯ boundedPower B).hom) (prod.lift_snd _ _)

/-- The membership predicate of the power object in the chosen slice classifier. -/
def boundedMembership (B : Over X) :
    B ⨯ boundedPower B ⟶ HasSubobjectClassifier.Ω (Over X) :=
  explicitBoundedMembership B ≫ (overClassifierIso X).inv

@[simp] lemma explicitBoundedMembership_left (B : Over X) :
    (explicitBoundedMembership B).left =
      prod.lift
          (prod.lift (prod.fst : B ⨯ boundedPower B ⟶ B).left
            ((prod.snd : B ⨯ boundedPower B ⟶ boundedPower B).left ≫ boundedSubset B) ≫
            Power.membership B.left)
          (B ⨯ boundedPower B).hom := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma explicitBoundedMembership_fst (B : Over X) :
    (explicitBoundedMembership B).left ≫ prod.fst =
      prod.lift (prod.fst : B ⨯ boundedPower B ⟶ B).left
          ((prod.snd : B ⨯ boundedPower B ⟶ boundedPower B).left ≫ boundedSubset B) ≫
        Power.membership B.left := by
  change
    prod.lift
          (prod.lift (prod.fst : B ⨯ boundedPower B ⟶ B).left
            ((prod.snd : B ⨯ boundedPower B ⟶ boundedPower B).left ≫ boundedSubset B) ≫
            Power.membership B.left)
          (B ⨯ boundedPower B).hom ≫ prod.fst = _
  exact prod.lift_fst _ _

/-- The ordinary predicate underlying a predicate in the slice. -/
def explicitPredicate {A B : Over X}
    (f : B ⨯ A ⟶ HasSubobjectClassifier.Ω (Over X)) :
    (B ⨯ A).left ⟶ HasSubobjectClassifier.Ω C :=
  (f ≫ (overClassifierIso X).hom).left ≫ prod.fst

/-- The subobject of the slice product classified by a predicate. -/
def sourceRelation {A B : Over X}
    (f : B ⨯ A ⟶ HasSubobjectClassifier.Ω (Over X)) :
    Subobject (B ⨯ A).left :=
  classified (explicitPredicate f)

/-- Extend a relation on the fiber product to the ambient ordinary product. -/
def ambientRelation {A B : Over X}
    (f : B ⨯ A ⟶ HasSubobjectClassifier.Ω (Over X)) :
    Subobject (B.left ⨯ A.left) :=
  (Subobject.map (overProdComparison B A)).obj (sourceRelation f)

/-- The generalized subset corresponding to the ambient extension of a slice predicate. -/
def ambientName {A B : Over X}
    (f : B ⨯ A ⟶ HasSubobjectClassifier.Ω (Over X)) :
    A.left ⟶ Power.pow B.left :=
  Power.transpose ((c (C := C)).representableBy.homEquiv.symm (ambientRelation f))

lemma relation_ambientName {A B : Over X}
    (f : B ⨯ A ⟶ HasSubobjectClassifier.Ω (Over X)) :
    relation (ambientName f) = ambientRelation f := by
  rw [relation, ambientName, Power.transpose_comm, classified, Equiv.apply_symm_apply]

omit [HasSubobjectClassifier C] [Power.HasPowers C] in
lemma overProdComparison_factors_sameFiber (B A : Over X) :
    (sameFiberRelation B A).Factors (overProdComparison B A) := by
  apply equalizerSubobject_factors
  simp

omit [Power.HasPowers C] in
lemma ambientRelation_le_sameFiber {A B : Over X}
    (f : B ⨯ A ⟶ HasSubobjectClassifier.Ω (Over X)) :
    ambientRelation f ≤ sameFiberRelation B A := by
  calc
    ambientRelation f ≤
        (Subobject.map (overProdComparison B A)).obj (⊤ : Subobject (B ⨯ A).left) :=
      (Subobject.map (overProdComparison B A)).monotone le_top
    _ = Subobject.mk (overProdComparison B A) := Subobject.map_top _
    _ ≤ sameFiberRelation B A := by
      apply Subobject.le_of_factors
      rw [← Subobject.underlyingIso_hom_comp_eq_mk]
      exact Subobject.factors_of_factors_right _
        (overProdComparison_factors_sameFiber B A)

/-- The ambient pair consisting of the named relation and its base point. -/
def boundedPair {A B : Over X}
    (f : B ⨯ A ⟶ HasSubobjectClassifier.Ω (Over X)) : A.left ⟶ ambient B :=
  prod.lift (ambientName f) A.hom

@[reassoc (attr := simp)]
lemma boundedPair_fst {A B : Over X}
    (f : B ⨯ A ⟶ HasSubobjectClassifier.Ω (Over X)) :
    boundedPair f ≫ prod.fst = ambientName f :=
  prod.lift_fst _ _

@[reassoc (attr := simp)]
lemma boundedPair_snd {A B : Over X}
    (f : B ⨯ A ⟶ HasSubobjectClassifier.Ω (Over X)) :
    boundedPair f ≫ prod.snd = A.hom :=
  prod.lift_snd _ _

lemma boundedPair_condition {A B : Over X}
    (f : B ⨯ A ⟶ HasSubobjectClassifier.Ω (Over X)) :
    boundedPair f ≫ prod.fst = boundedPair f ≫ restrictToFiber B := by
  have hpair :
      boundedPair f ≫ prod.lift prod.fst (prod.snd ≫ fiberName B) =
        prod.lift (ambientName f) (A.hom ≫ fiberName B) := by
    rw [prod.comp_lift]
    simp
  apply relation_injective
  rw [boundedPair_fst, restrictToFiber, ← Category.assoc, hpair]
  rw [relation_intersection, relation_ambientName, relation_fiberAt,
    inf_eq_left.mpr (ambientRelation_le_sameFiber f)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The underlying factorization through the equalizer defining `boundedPower`. -/
def boundedLift {A B : Over X}
    (f : B ⨯ A ⟶ HasSubobjectClassifier.Ω (Over X)) :
    A.left ⟶ (boundedPower B).left :=
  equalizer.lift (boundedPair f) (boundedPair_condition f)

@[reassoc (attr := simp)]
lemma boundedLift_ι {A B : Over X}
    (f : B ⨯ A ⟶ HasSubobjectClassifier.Ω (Over X)) :
    boundedLift f ≫
        equalizer.ι (prod.fst : ambient B ⟶ Power.pow B.left) (restrictToFiber B) =
      boundedPair f := by
  change equalizer.lift (boundedPair f) (boundedPair_condition f) ≫
      equalizer.ι (prod.fst : ambient B ⟶ Power.pow B.left) (restrictToFiber B) = _
  exact equalizer.lift_ι _ _

/-- The transpose of a slice predicate into the bounded power object. -/
def boundedTranspose {A B : Over X}
    (f : B ⨯ A ⟶ HasSubobjectClassifier.Ω (Over X)) : A ⟶ boundedPower B :=
  Over.homMk (boundedLift f) (by
    change boundedLift f ≫
        (equalizer.ι (prod.fst : ambient B ⟶ Power.pow B.left) (restrictToFiber B) ≫
          prod.snd) = A.hom
    rw [← Category.assoc, boundedLift_ι, boundedPair_snd])

@[reassoc (attr := simp)]
lemma boundedTranspose_ι {A B : Over X}
    (f : B ⨯ A ⟶ HasSubobjectClassifier.Ω (Over X)) :
    (boundedTranspose f).left ≫
        equalizer.ι (prod.fst : ambient B ⟶ Power.pow B.left) (restrictToFiber B) =
      boundedPair f :=
  boundedLift_ι f

@[reassoc (attr := simp)]
lemma boundedTranspose_boundedSubset {A B : Over X}
    (f : B ⨯ A ⟶ HasSubobjectClassifier.Ω (Over X)) :
    (boundedTranspose f).left ≫ boundedSubset B = ambientName f := by
  change boundedLift f ≫
      (equalizer.ι (prod.fst : ambient B ⟶ Power.pow B.left) (restrictToFiber B) ≫
        prod.fst) = ambientName f
  rw [← Category.assoc, boundedLift_ι, boundedPair_fst]

lemma mappedExplicitBoundedMembership_fst {A B : Over X}
    (g : A ⟶ boundedPower B) :
    (prod.map (𝟙 B) g ≫ explicitBoundedMembership B).left ≫ prod.fst =
      overProdComparison B A ≫
        prod.map (𝟙 B.left) (g.left ≫ boundedSubset B) ≫ Power.membership B.left := by
  have hfst :
      (prod.map (𝟙 B) g).left ≫ (prod.fst : B ⨯ boundedPower B ⟶ B).left =
        (prod.fst : B ⨯ A ⟶ B).left := by
    simpa only [Over.comp_left, Over.id_left, Category.comp_id] using
      congrArg Over.Hom.left (prod.map_fst (𝟙 B) g)
  have hsnd :
      (prod.map (𝟙 B) g).left ≫ (prod.snd : B ⨯ boundedPower B ⟶ boundedPower B).left =
        (prod.snd : B ⨯ A ⟶ A).left ≫ g.left := by
    simpa only [Over.comp_left, Over.id_left, Category.id_comp] using
      congrArg Over.Hom.left (prod.map_snd (𝟙 B) g)
  rw [Over.comp_left, Category.assoc, explicitBoundedMembership_fst,
    ← Category.assoc, prod.comp_lift, hfst, ← Category.assoc, hsnd]
  simp only [overProdComparison, ← Category.assoc, prod.lift_map, Category.comp_id]

lemma boundedTranspose_explicitPredicate {A B : Over X}
    (f : B ⨯ A ⟶ HasSubobjectClassifier.Ω (Over X)) :
    (prod.map (𝟙 B) (boundedTranspose f) ≫ explicitBoundedMembership B).left ≫ prod.fst =
      explicitPredicate f := by
  rw [mappedExplicitBoundedMembership_fst, boundedTranspose_boundedSubset]
  apply (c (C := C)).representableBy.homEquiv.injective
  change classified
      (overProdComparison B A ≫
        (prod.map (𝟙 B.left) (ambientName f) ≫ Power.membership B.left)) =
    sourceRelation f
  rw [classified_comp]
  change (Subobject.pullback (overProdComparison B A)).obj (relation (ambientName f)) = _
  rw [relation_ambientName, ambientRelation, Subobject.pullback_map_self]

lemma boundedTranspose_comm {A B : Over X}
    (f : B ⨯ A ⟶ HasSubobjectClassifier.Ω (Over X)) :
    prod.map (𝟙 B) (boundedTranspose f) ≫ boundedMembership B = f := by
  apply (cancel_mono (overClassifierIso X).hom).1
  simp only [boundedMembership, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · exact boundedTranspose_explicitPredicate f
  · exact (prod.map (𝟙 B) (boundedTranspose f) ≫ explicitBoundedMembership B).w.trans
      (f ≫ (overClassifierIso X).hom).w.symm

omit [HasSubobjectClassifier C] [Power.HasPowers C] in
/-- Lift a compatible pair of maps to the product in the slice. -/
def overProdLift {A B : Over X} {T : C} (p : T ⟶ B.left) (q : T ⟶ A.left)
    (w : p ≫ B.hom = q ≫ A.hom) : T ⟶ (B ⨯ A).left :=
  pullback.lift p q w ≫ (Over.prodLeftIsoPullback B A).inv

omit [HasSubobjectClassifier C] [Power.HasPowers C] in
@[reassoc (attr := simp)]
lemma overProdLift_fst {A B : Over X} {T : C} (p : T ⟶ B.left) (q : T ⟶ A.left)
    (w : p ≫ B.hom = q ≫ A.hom) :
    overProdLift p q w ≫ (prod.fst : B ⨯ A ⟶ B).left = p := by
  rw [overProdLift, Category.assoc, Over.prodLeftIsoPullback_inv_fst, pullback.lift_fst]

omit [HasSubobjectClassifier C] [Power.HasPowers C] in
@[reassoc (attr := simp)]
lemma overProdLift_snd {A B : Over X} {T : C} (p : T ⟶ B.left) (q : T ⟶ A.left)
    (w : p ≫ B.hom = q ≫ A.hom) :
    overProdLift p q w ≫ (prod.snd : B ⨯ A ⟶ A).left = q := by
  rw [overProdLift, Category.assoc, Over.prodLeftIsoPullback_inv_snd, pullback.lift_snd]

omit [HasSubobjectClassifier C] [Power.HasPowers C] in
lemma overProdLift_comparison {A B : Over X} {T : C} (p : T ⟶ B.left) (q : T ⟶ A.left)
    (w : p ≫ B.hom = q ≫ A.hom) :
    overProdLift p q w ≫ overProdComparison B A = prod.lift p q := by
  apply prod.hom_ext
  · rw [Category.assoc, overProdComparison_fst, overProdLift_fst]
    exact (prod.lift_fst p q).symm
  · rw [Category.assoc, overProdComparison_snd, overProdLift_snd]
    exact (prod.lift_snd p q).symm

omit [HasSubobjectClassifier C] [Power.HasPowers C] in
lemma sameFiberRelation_eq_mk_overProdComparison (B A : Over X) :
    sameFiberRelation B A = Subobject.mk (overProdComparison B A) := by
  apply le_antisymm
  · let i := equalizer.ι (prod.fst ≫ B.hom) (prod.snd ≫ A.hom)
    have w : (i ≫ prod.fst) ≫ B.hom = (i ≫ prod.snd) ≫ A.hom := by
      rw [Category.assoc, Category.assoc]
      exact equalizer.condition _ _
    apply Subobject.mk_le_mk_of_comm (overProdLift (i ≫ prod.fst) (i ≫ prod.snd) w)
    rw [overProdLift_comparison, ← prod.comp_lift, prod.lift_fst_snd, Category.comp_id]
  · apply Subobject.le_of_factors
    rw [← Subobject.underlyingIso_hom_comp_eq_mk]
    exact Subobject.factors_of_factors_right _
      (overProdComparison_factors_sameFiber B A)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma boundedMap_ι_snd {A B : Over X} (g : A ⟶ boundedPower B) :
    (g.left ≫
      equalizer.ι (prod.fst : ambient B ⟶ Power.pow B.left) (restrictToFiber B)) ≫
      prod.snd = A.hom := by
  rw [Category.assoc, ← boundedPower_hom]
  exact g.w

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma boundedSubset_condition {A B : Over X} (g : A ⟶ boundedPower B) :
    g.left ≫ boundedSubset B =
      prod.lift (g.left ≫ boundedSubset B) (A.hom ≫ fiberName B) ≫ intersection B.left := by
  let i := equalizer.ι (prod.fst : ambient B ⟶ Power.pow B.left) (restrictToFiber B)
  have hi := congrArg (fun k ↦ g.left ≫ k)
    (equalizer.condition (prod.fst : ambient B ⟶ Power.pow B.left) (restrictToFiber B))
  calc
    g.left ≫ boundedSubset B = g.left ≫ (i ≫ prod.fst) := rfl
    _ = g.left ≫ (i ≫ restrictToFiber B) := hi
    _ = (g.left ≫ i) ≫ restrictToFiber B := by rw [Category.assoc]
    _ = prod.lift ((g.left ≫ i) ≫ prod.fst)
          (((g.left ≫ i) ≫ prod.snd) ≫ fiberName B) ≫ intersection B.left := by
      rw [restrictToFiber, ← Category.assoc, prod.comp_lift]
      simp only [Category.assoc]
    _ = prod.lift (g.left ≫ boundedSubset B) (A.hom ≫ fiberName B) ≫
          intersection B.left := by
      rw [boundedMap_ι_snd]
      rw [boundedSubset, Category.assoc]

lemma relation_boundedSubset_inf {A B : Over X} (g : A ⟶ boundedPower B) :
    relation (g.left ≫ boundedSubset B) =
      relation (g.left ≫ boundedSubset B) ⊓ sameFiberRelation B A := by
  calc
    relation (g.left ≫ boundedSubset B) =
        relation
          (prod.lift (g.left ≫ boundedSubset B) (A.hom ≫ fiberName B) ≫
            intersection B.left) := congrArg relation (boundedSubset_condition g)
    _ = relation (g.left ≫ boundedSubset B) ⊓ relation (A.hom ≫ fiberName B) :=
      relation_intersection _ _
    _ = relation (g.left ≫ boundedSubset B) ⊓ sameFiberRelation B A := by
      rw [relation_fiberAt]

lemma relation_boundedSubset_le_sameFiber {A B : Over X} (g : A ⟶ boundedPower B) :
    relation (g.left ≫ boundedSubset B) ≤ sameFiberRelation B A := by
  apply inf_eq_left.mp
  exact (relation_boundedSubset_inf g).symm

lemma relation_boundedSubset_eq_map_pullback {A B : Over X} (g : A ⟶ boundedPower B) :
    relation (g.left ≫ boundedSubset B) =
      (Subobject.map (overProdComparison B A)).obj
        ((Subobject.pullback (overProdComparison B A)).obj
          (relation (g.left ≫ boundedSubset B))) := by
  have hle : relation (g.left ≫ boundedSubset B) ≤
      Subobject.mk (overProdComparison B A) := by
    rw [← sameFiberRelation_eq_mk_overProdComparison]
    exact relation_boundedSubset_le_sameFiber g
  calc
    relation (g.left ≫ boundedSubset B) =
        Subobject.mk (overProdComparison B A) ⊓
          relation (g.left ≫ boundedSubset B) := (inf_eq_right.mpr hle).symm
    _ = (Subobject.map (overProdComparison B A)).obj
          ((Subobject.pullback (overProdComparison B A)).obj
            (relation (g.left ≫ boundedSubset B))) :=
      Subobject.inf_eq_map_pullback' (MonoOver.mk (overProdComparison B A)) _

lemma membershipEquation_explicitPredicate {A B : Over X}
    {f : B ⨯ A ⟶ HasSubobjectClassifier.Ω (Over X)} {g : A ⟶ boundedPower B}
    (hg : prod.map (𝟙 B) g ≫ boundedMembership B = f) :
    overProdComparison B A ≫
        prod.map (𝟙 B.left) (g.left ≫ boundedSubset B) ≫ Power.membership B.left =
      explicitPredicate f := by
  have hgExplicit :
      prod.map (𝟙 B) g ≫ explicitBoundedMembership B =
        f ≫ (overClassifierIso X).hom := by
    calc
      prod.map (𝟙 B) g ≫ explicitBoundedMembership B =
          (prod.map (𝟙 B) g ≫ boundedMembership B) ≫ (overClassifierIso X).hom := by
        simp only [boundedMembership, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      _ = f ≫ (overClassifierIso X).hom := by rw [hg]
  have h := congrArg (fun k ↦ k.left ≫ prod.fst) hgExplicit
  change overProdComparison B A ≫
      prod.map (𝟙 B.left) (g.left ≫ boundedSubset B) ≫ Power.membership B.left =
    (f ≫ (overClassifierIso X).hom).left ≫ prod.fst
  exact (mappedExplicitBoundedMembership_fst g).symm.trans h

lemma membershipEquation_pullback {A B : Over X}
    {f : B ⨯ A ⟶ HasSubobjectClassifier.Ω (Over X)} {g : A ⟶ boundedPower B}
    (hg : prod.map (𝟙 B) g ≫ boundedMembership B = f) :
    (Subobject.pullback (overProdComparison B A)).obj
        (relation (g.left ≫ boundedSubset B)) = sourceRelation f := by
  have h := congrArg classified (membershipEquation_explicitPredicate hg)
  rw [classified_comp] at h
  simpa only [relation, sourceRelation] using h

lemma boundedTranspose_unique {A B : Over X}
    {f : B ⨯ A ⟶ HasSubobjectClassifier.Ω (Over X)} {g : A ⟶ boundedPower B}
    (hg : prod.map (𝟙 B) g ≫ boundedMembership B = f) : boundedTranspose f = g := by
  have hsubset : g.left ≫ boundedSubset B = ambientName f := by
    apply relation_injective
    calc
      relation (g.left ≫ boundedSubset B) =
          (Subobject.map (overProdComparison B A)).obj
            ((Subobject.pullback (overProdComparison B A)).obj
              (relation (g.left ≫ boundedSubset B))) :=
        relation_boundedSubset_eq_map_pullback g
      _ = (Subobject.map (overProdComparison B A)).obj (sourceRelation f) := by
        rw [membershipEquation_pullback hg]
      _ = ambientRelation f := rfl
      _ = relation (ambientName f) := (relation_ambientName f).symm
  apply Over.OverMorphism.ext
  apply (cancel_mono
    (equalizer.ι (prod.fst : ambient B ⟶ Power.pow B.left) (restrictToFiber B))).1
  apply prod.hom_ext
  · rw [Category.assoc, Category.assoc]
    change (boundedTranspose f).left ≫ boundedSubset B = g.left ≫ boundedSubset B
    rw [boundedTranspose_boundedSubset, hsubset]
  · rw [Category.assoc, Category.assoc]
    change (boundedTranspose f).left ≫ (boundedPower B).hom =
      g.left ≫ (boundedPower B).hom
    exact (boundedTranspose f).w.trans g.w.symm

/-- The bounded power object represents predicates in the slice. -/
@[implicit_reducible]
def boundedIsPower (B : Over X) : Power.IsPower (boundedMembership B) where
  transpose := boundedTranspose
  comm := boundedTranspose_comm
  uniq := boundedTranspose_unique

/-- A chosen power object for an object of the slice. -/
@[implicit_reducible]
def overHasPower (B : Over X) : Power.HasPower B where
  pow := boundedPower B
  membership := boundedMembership B
  isPower := boundedIsPower B

/-- Chosen power objects for all objects of the slice. -/
@[implicit_reducible]
def overHasPowers (X : C) : Power.HasPowers (Over X) where
  hasPower := overHasPower

end

end Submission.SlicePowers
