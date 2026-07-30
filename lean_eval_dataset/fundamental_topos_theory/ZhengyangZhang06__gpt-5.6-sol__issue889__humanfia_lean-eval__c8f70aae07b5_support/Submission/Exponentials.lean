import Submission.Power

open CategoryTheory hiding prod
open CategoryTheory.Limits

namespace Submission.Exponentials

noncomputable section

universe u v

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
  [HasSubobjectClassifier C]

/-- A classifier equivalent to the chosen one, with the chosen terminal object as truth domain. -/
def rawClassifier : Subobject.Classifier C :=
  let c := HasSubobjectClassifier.exists_classifier.some
  c.ofIso (Iso.refl c.Ω) (c.isTerminalΩ₀.uniqueUpToIso terminalIsTerminal)
    (fun _ ↦ terminal.from _)
    (c.χ₀ (⊤_ C) ≫ c.truth)

@[simp] lemma rawClassifier_Ω :
    (rawClassifier (C := C)).Ω = HasSubobjectClassifier.Ω C := rfl

@[simp] lemma rawClassifier_Ω₀ : (rawClassifier (C := C)).Ω₀ = ⊤_ C := rfl

abbrev classifier : Subobject.Classifier C where
  Ω₀ := ⊤_ C
  Ω := HasSubobjectClassifier.Ω C
  truth := by simpa only [rawClassifier_Ω, rawClassifier_Ω₀] using
    (rawClassifier (C := C)).truth
  mono_truth := by infer_instance
  χ₀ U := by simpa only [rawClassifier_Ω₀] using
    (rawClassifier (C := C)).χ₀ U
  χ {U X} m _ := by simpa only [rawClassifier_Ω] using
    (rawClassifier (C := C)).χ m
  isPullback {U X} m _ := by
    simpa only [rawClassifier_Ω, rawClassifier_Ω₀] using
      (rawClassifier (C := C)).isPullback m
  uniq {U X} m _ χ₀ χ' h := by
    simpa only [rawClassifier_Ω, rawClassifier_Ω₀] using
      (rawClassifier (C := C)).uniq m h

@[simp] lemma classifier_Ω : (classifier (C := C)).Ω = HasSubobjectClassifier.Ω C := rfl

@[simp] lemma classifier_Ω₀ : (classifier (C := C)).Ω₀ = ⊤_ C := rfl

namespace Predicate

/-- The predicate which is true everywhere. -/
def true_ (B : C) : B ⟶ HasSubobjectClassifier.Ω C :=
  terminal.from B ≫ (classifier (C := C)).truth

/-- The equality predicate on `B`. -/
def eq (B : C) : B ⨯ B ⟶ HasSubobjectClassifier.Ω C :=
  (classifier (C := C)).χ (diag B)

lemma lift_eq {X B : C} (b : X ⟶ B) :
    prod.lift b b ≫ eq B = true_ X := by
  dsimp only [eq, true_]
  rw [← prod.comp_diag b, Category.assoc,
    (classifier (C := C)).isPullback (diag B) |>.w, ← Category.assoc]
  congr 1
  exact terminalIsTerminal.hom_ext _ _

lemma eq_of_lift_eq {X B : C} {b b' : X ⟶ B}
    (h : prod.lift b b' ≫ eq B = true_ X) : b = b' := by
  dsimp only [eq, true_] at h
  let l := (classifier (C := C)).isPullback (diag B) |>.lift
    (prod.lift b b') (terminal.from X) h
  have hl : l ≫ diag B = prod.lift b b' :=
    (classifier (C := C)).isPullback (diag B) |>.lift_fst _ _ h
  have hfst := congrArg (fun k ↦ k ≫ prod.fst) hl
  have hsnd := congrArg (fun k ↦ k ≫ prod.snd) hl
  have hfst' : l = b := by simpa only [Category.assoc, prod.comp_diag,
    prod.lift_fst] using hfst
  have hsnd' : l = b' := by simpa only [Category.assoc, prod.comp_diag,
    prod.lift_snd] using hsnd
  exact hfst'.symm.trans hsnd'

end Predicate

variable [Power.HasPowers C]

/-- The singleton map into a power object. -/
def singleton (B : C) : B ⟶ Power.pow B :=
  Power.transpose (Predicate.eq B)

instance singletonMono (B : C) : Mono (singleton B) where
  right_cancellation := by
    intro X b b' h
    rw [singleton] at h
    have h₁ :
        prod.map (𝟙 B) (b ≫ Power.transpose (Predicate.eq B)) ≫ Power.membership B =
          prod.map (𝟙 B) (b' ≫ Power.transpose (Predicate.eq B)) ≫ Power.membership B :=
      congrArg (fun k ↦ prod.map (𝟙 B) k ≫ Power.membership B) h
    rw [prod.map_id_comp, Category.assoc, Power.transpose_comm,
      prod.map_id_comp, Category.assoc, Power.transpose_comm] at h₁
    have htrue :
        (b ≫ terminal.from _) ≫ (classifier (C := C)).truth =
          prod.lift b (𝟙 X) ≫ prod.map (𝟙 B) b ≫ Predicate.eq B := by
      rw [terminal.comp_from, ← Category.assoc, prod.lift_map,
        Category.comp_id, Category.id_comp, Predicate.lift_eq, Predicate.true_]
    rw [terminal.comp_from, h₁, ← Category.assoc, prod.lift_map,
      Category.id_comp, Category.comp_id] at htrue
    apply Predicate.eq_of_lift_eq
    simpa [Predicate.true_] using htrue.symm

namespace Predicate

/-- The predicate selecting singleton subobjects. -/
def isSingleton (B : C) : Power.pow B ⟶ HasSubobjectClassifier.Ω C :=
  (classifier (C := C)).χ (singleton B)

end Predicate

/-- The global element of a power object corresponding to a predicate. -/
def name {B : C} (φ : B ⟶ HasSubobjectClassifier.Ω C) : ⊤_ C ⟶ Power.pow B :=
  Power.transpose (prod.fst ≫ φ)

@[reassoc]
lemma name_membership {B : C} (φ : B ⟶ HasSubobjectClassifier.Ω C) :
    prod.map (𝟙 B) (name φ) ≫ Power.membership B = prod.fst ≫ φ :=
  Power.transpose_comm _

/-- The object of functional relations from `A` to `B`. -/
def hom (A B : C) : C :=
  pullback
    (Power.transpose
      (Power.transpose ((Limits.prod.associator _ _ _).inv ≫ Power.membership (B ⨯ A)) ≫
        Predicate.isSingleton B))
    (name (Predicate.true_ A))

/-- The underlying graph of a functional relation. -/
def homToGraph (A B : C) : hom A B ⟶ Power.pow (B ⨯ A) :=
  pullback.fst _ _

instance homToGraph_mono {A B : C} : Mono (homToGraph A B) :=
  pullback.fst_of_mono

lemma hom_snd (A B : C) :
    pullback.snd
      (Power.transpose
        (Power.transpose ((Limits.prod.associator _ _ _).inv ≫ Power.membership (B ⨯ A)) ≫
          Predicate.isSingleton B))
      (name (Predicate.true_ A)) = terminal.from (hom A B) :=
  terminalIsTerminal.hom_ext _ _

lemma hom_condition (A B : C) :
    homToGraph A B ≫
      Power.transpose
        (Power.transpose ((Limits.prod.associator _ _ _).inv ≫ Power.membership (B ⨯ A)) ≫
          Predicate.isSingleton B) =
      terminal.from (hom A B) ≫ name (Predicate.true_ A) := by
  rw [← hom_snd A B]
  exact pullback.condition

lemma eval_condition_aux (A B : C) :
    (prod.map (𝟙 A) (homToGraph A B) ≫
      Power.transpose ((Limits.prod.associator _ _ _).inv ≫ Power.membership (B ⨯ A))) ≫
        Predicate.isSingleton B =
      Predicate.true_ (A ⨯ hom A B) := by
  let graphMap : A ⨯ hom A B ⟶ A ⨯ Power.pow (B ⨯ A) :=
    prod.map (𝟙 A) (homToGraph A B)
  let fibers : A ⨯ Power.pow (B ⨯ A) ⟶ Power.pow B :=
    Power.transpose ((Limits.prod.associator _ _ _).inv ≫ Power.membership (B ⨯ A))
  let singletonFibers : Power.pow (B ⨯ A) ⟶ Power.pow A :=
    Power.transpose (fibers ≫ Predicate.isSingleton B)
  let mapSingletonFibers : A ⨯ Power.pow (B ⨯ A) ⟶ A ⨯ Power.pow A :=
    prod.map (𝟙 A) singletonFibers
  have hmiddle :
      fibers ≫ Predicate.isSingleton B =
        prod.map (𝟙 A) singletonFibers ≫ Power.membership A :=
    (Power.transpose_comm _).symm
  have hleft :
      graphMap ≫ mapSingletonFibers =
        prod.map (𝟙 A) (terminal.from _) ≫
          prod.map (𝟙 A) (name (Predicate.true_ A)) := by
    rw [prod.map_map, prod.map_map]
    apply prod.hom_ext
    · simp
    · simpa only [singletonFibers, prod.map_snd, Category.assoc] using
        congrArg (fun k ↦ prod.snd ≫ k) (hom_condition A B)
  have hterminal :
      (prod.map (𝟙 A) (terminal.from (hom A B)) ≫ prod.fst) ≫ terminal.from A =
        terminal.from (A ⨯ hom A B) :=
    terminalIsTerminal.hom_ext _ _
  rw [Category.assoc, hmiddle, ← Category.assoc, hleft, Category.assoc,
    name_membership]
  dsimp only [Predicate.true_]
  rw [← Category.assoc, ← Category.assoc, hterminal]

/-- Evaluation of a functional relation. -/
def eval (A B : C) : A ⨯ hom A B ⟶ B :=
  (classifier (C := C)).isPullback (singleton B) |>.lift
    (prod.map (𝟙 A) (homToGraph A B) ≫
      Power.transpose ((Limits.prod.associator _ _ _).inv ≫ Power.membership (B ⨯ A)))
    (terminal.from _) (eval_condition_aux A B)

@[reassoc]
lemma eval_singleton (A B : C) :
    eval A B ≫ singleton B =
      prod.map (𝟙 A) (homToGraph A B) ≫
        Power.transpose ((Limits.prod.associator _ _ _).inv ≫ Power.membership (B ⨯ A)) :=
  (classifier (C := C)).isPullback (singleton B) |>.lift_fst _ _ _

abbrev Exponentiates {A B X H : C} (e : A ⨯ H ⟶ B) (f : A ⨯ X ⟶ B)
    (fexp : X ⟶ H) : Prop :=
  prod.map (𝟙 A) fexp ≫ e = f

variable {A B X : C} (f : A ⨯ X ⟶ B)

/-- The graph relation associated to a morphism `A ⨯ X ⟶ B`. -/
def graphName : X ⟶ Power.pow (B ⨯ A) :=
  Power.transpose
    ((Limits.prod.associator _ _ _).hom ≫ prod.map (𝟙 B) f ≫ Predicate.eq B)

lemma graphName_condition :
    graphName f ≫
      Power.transpose
        (Power.transpose ((Limits.prod.associator B A (Power.pow (B ⨯ A))).inv ≫
          Power.membership (B ⨯ A)) ≫ Predicate.isSingleton B) =
      terminal.from X ≫ name (Predicate.true_ A) := by
  let relation : B ⨯ (A ⨯ X) ⟶ HasSubobjectClassifier.Ω C :=
    prod.map (𝟙 B) f ≫ Predicate.eq B
  let graph : X ⟶ Power.pow (B ⨯ A) :=
    Power.transpose ((Limits.prod.associator _ _ _).hom ≫ relation)
  have hgraph :
      (Limits.prod.associator _ _ _).hom ≫ relation =
        prod.map (𝟙 (B ⨯ A)) graph ≫ Power.membership (B ⨯ A) := by
    exact (Power.transpose_comm _).symm
  have hgraph' :
      relation = (Limits.prod.associator _ _ _).inv ≫
        prod.map (𝟙 (B ⨯ A)) graph ≫ Power.membership (B ⨯ A) := by
    rw [← hgraph, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  let fibers : A ⨯ Power.pow (B ⨯ A) ⟶ Power.pow B :=
    Power.transpose ((Limits.prod.associator _ _ _).inv ≫ Power.membership (B ⨯ A))
  have hfibers :
      (Limits.prod.associator _ _ _).inv ≫ Power.membership (B ⨯ A) =
        prod.map (𝟙 B) fibers ≫ Power.membership B :=
    (Power.transpose_comm _).symm
  have htranspose :
      Power.transpose
          (prod.map (𝟙 A) graph ≫ fibers ≫ Predicate.isSingleton B) =
        graph ≫ Power.transpose (fibers ≫ Predicate.isSingleton B) := by
    apply Power.transpose_unique
    rw [prod.map_id_comp, Category.assoc, Power.transpose_comm, ← Category.assoc]
  change graph ≫ Power.transpose (fibers ≫ Predicate.isSingleton B) = _
  rw [← htranspose]
  have hgraphSingleton :
      Power.transpose relation = f ≫ singleton B := by
    apply Power.transpose_unique
    dsimp only [singleton]
    rw [prod.map_id_comp, Category.assoc, Power.transpose_comm]
  have hshuffle :
      (Limits.prod.associator B A X).inv ≫ prod.map (𝟙 (B ⨯ A)) graph =
        prod.map (𝟙 B) (prod.map (𝟙 A) graph) ≫
          (Limits.prod.associator _ _ _).inv := by
    simp
  have hgraphFibers :
      Power.transpose relation = prod.map (𝟙 A) graph ≫ fibers := by
    apply Power.transpose_unique
    rw [hgraph', ← Category.assoc, hshuffle, prod.map_id_comp,
      Category.assoc, ← hfibers, Category.assoc]
  have heq :
      f ≫ singleton B = prod.map (𝟙 A) graph ≫ fibers :=
    hgraphSingleton.symm.trans hgraphFibers
  have heq' :
      f ≫ singleton B ≫ Predicate.isSingleton B =
        prod.map (𝟙 A) graph ≫ fibers ≫ Predicate.isSingleton B := by
    rw [← Category.assoc, ← Category.assoc, heq]
  rw [← heq']
  apply Power.transpose_unique
  dsimp only [name, Predicate.true_, Predicate.isSingleton]
  have hfTerminal : f ≫ terminal.from B = terminal.from _ :=
    terminalIsTerminal.hom_ext _ _
  have hrightTerminal :
      (prod.rightUnitor A).hom ≫ terminal.from A = terminal.from _ :=
    terminalIsTerminal.hom_ext _ _
  have hmapTerminal :
      prod.map (𝟙 A) (terminal.from X) ≫ terminal.from (A ⨯ ⊤_ C) = terminal.from _ :=
    terminalIsTerminal.hom_ext _ _
  have htruth :
      terminal.from (A ⨯ ⊤_ C) ≫ (classifier (C := C)).truth =
        prod.map (𝟙 A)
          (Power.transpose
            (terminal.from (A ⨯ ⊤_ C) ≫ (classifier (C := C)).truth)) ≫
          Power.membership A :=
    (Power.transpose_comm _).symm
  have hright : (prod.rightUnitor A).hom = prod.fst := rfl
  have hχ₀ : (classifier (C := C)).χ₀ B = terminal.from B :=
    terminalIsTerminal.hom_ext _ _
  rw [(classifier (C := C)).isPullback (singleton B) |>.w,
    hχ₀, ← Category.assoc, ← hright, hrightTerminal, ← Category.assoc, hfTerminal,
    prod.map_id_comp, Category.assoc, ← htruth, ← Category.assoc, hmapTerminal]

/-- Currying a morphism as its functional graph. -/
def homMap : X ⟶ hom A B :=
  pullback.lift (graphName f) (terminal.from X) (graphName_condition f)

@[simp, reassoc]
lemma homMap_toGraph : homMap f ≫ homToGraph A B = graphName f :=
  pullback.lift_fst _ _ _

lemma graphName_fibers :
    prod.map (𝟙 A) (graphName f) ≫
        Power.transpose ((Limits.prod.associator B A (Power.pow (B ⨯ A))).inv ≫
          Power.membership (B ⨯ A)) =
      f ≫ singleton B := by
  apply (Power.transposeEquiv (A ⨯ X) B).symm.injective
  change
    prod.map (𝟙 B)
        (prod.map (𝟙 A) (graphName f) ≫
          Power.transpose ((Limits.prod.associator B A (Power.pow (B ⨯ A))).inv ≫
            Power.membership (B ⨯ A))) ≫ Power.membership B =
      prod.map (𝟙 B) (f ≫ singleton B) ≫ Power.membership B
  rw [prod.map_id_comp, Category.assoc, Power.transpose_comm,
    prod.map_id_comp, Category.assoc]
  dsimp only [singleton, graphName]
  rw [Power.transpose_comm, ← Category.assoc]
  have hshuffle :
      prod.map (𝟙 B) (prod.map (𝟙 A)
          (Power.transpose
            ((Limits.prod.associator B A X).hom ≫ prod.map (𝟙 B) f ≫ Predicate.eq B))) ≫
          (Limits.prod.associator B A (Power.pow (B ⨯ A))).inv =
        (Limits.prod.associator B A X).inv ≫
          prod.map (𝟙 (B ⨯ A))
            (Power.transpose
              ((Limits.prod.associator B A X).hom ≫ prod.map (𝟙 B) f ≫ Predicate.eq B)) := by
    simp
  rw [hshuffle, Category.assoc, Power.transpose_comm, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

theorem homMap_exponentiates : Exponentiates (eval A B) f (homMap f) := by
  dsimp only [Exponentiates]
  rw [← cancel_mono (singleton B), Category.assoc, eval_singleton,
    ← Category.assoc, ← prod.map_id_comp, homMap_toGraph, graphName_fibers]

theorem homMap_unique {g : X ⟶ hom A B} (hg : Exponentiates (eval A B) f g) :
    homMap f = g := by
  dsimp only [Exponentiates] at hg
  have hgSingleton := congrArg (fun k ↦ k ≫ singleton B) hg
  let fibers : A ⨯ Power.pow (B ⨯ A) ⟶ Power.pow B :=
    Power.transpose ((Limits.prod.associator _ _ _).inv ≫ Power.membership (B ⨯ A))
  have heval :
      eval A B ≫ singleton B = prod.map (𝟙 A) (homToGraph A B) ≫ fibers :=
    eval_singleton A B
  rw [Category.assoc, heval, ← Category.assoc, ← prod.map_id_comp] at hgSingleton
  let relation : B ⨯ (A ⨯ X) ⟶ HasSubobjectClassifier.Ω C :=
    prod.map (𝟙 B) f ≫ Predicate.eq B
  have hrelation : Power.transpose relation = f ≫ singleton B := by
    apply Power.transpose_unique
    dsimp only [singleton]
    rw [prod.map_id_comp, Category.assoc, Power.transpose_comm]
  have hgFibers :
      Power.transpose
          (prod.map (𝟙 B) (prod.map (𝟙 A) (g ≫ homToGraph A B)) ≫
            (Limits.prod.associator _ _ _).inv ≫ Power.membership (B ⨯ A)) =
        prod.map (𝟙 A) (g ≫ homToGraph A B) ≫ fibers := by
    apply Power.transpose_unique
    rw [prod.map_id_comp, Category.assoc, Power.transpose_comm]
  have hgUncurried := Power.transpose_comm
    (prod.map (𝟙 B) (prod.map (𝟙 A) (g ≫ homToGraph A B)) ≫
      (Limits.prod.associator B A (Power.pow (B ⨯ A))).inv ≫ Power.membership (B ⨯ A))
  rw [hgFibers, hgSingleton, ← hrelation, Power.transpose_comm, ← Category.assoc]
    at hgUncurried
  have hmapSingleton := congrArg (fun k ↦ k ≫ singleton B) (homMap_exponentiates f)
  rw [Category.assoc, heval, ← Category.assoc, ← prod.map_id_comp] at hmapSingleton
  have hmapFibers :
      Power.transpose
          (prod.map (𝟙 B)
              (prod.map (𝟙 A) (homMap f ≫ homToGraph A B)) ≫
            (Limits.prod.associator _ _ _).inv ≫ Power.membership (B ⨯ A)) =
        prod.map (𝟙 A) (homMap f ≫ homToGraph A B) ≫ fibers := by
    apply Power.transpose_unique
    rw [prod.map_id_comp, Category.assoc, Power.transpose_comm]
  have hmapUncurried := Power.transpose_comm
    (prod.map (𝟙 B) (prod.map (𝟙 A) (homMap f ≫ homToGraph A B)) ≫
      (Limits.prod.associator B A (Power.pow (B ⨯ A))).inv ≫ Power.membership (B ⨯ A))
  rw [hmapFibers, hmapSingleton, ← hrelation, Power.transpose_comm, ← Category.assoc]
    at hmapUncurried
  have hpredicates := hmapUncurried.symm.trans hgUncurried
  have hshuffleG :
      prod.map (𝟙 B) (prod.map (𝟙 A) (g ≫ homToGraph A B)) ≫
          (Limits.prod.associator B A (Power.pow (B ⨯ A))).inv =
        (Limits.prod.associator B A X).inv ≫
          prod.map (𝟙 (B ⨯ A)) (g ≫ homToGraph A B) := by
    simp
  have hshuffleMap :
      prod.map (𝟙 B) (prod.map (𝟙 A) (homMap f ≫ homToGraph A B)) ≫
          (Limits.prod.associator B A (Power.pow (B ⨯ A))).inv =
        (Limits.prod.associator B A X).inv ≫
          prod.map (𝟙 (B ⨯ A)) (homMap f ≫ homToGraph A B) := by
    simp
  rw [hshuffleG, hshuffleMap] at hpredicates
  have hpredicates' := congrArg (fun k ↦ (Limits.prod.associator B A X).hom ≫ k) hpredicates
  rw [← Category.assoc, ← Category.assoc, Iso.hom_inv_id, Category.id_comp,
    ← Category.assoc, ← Category.assoc, Iso.hom_inv_id, Category.id_comp] at hpredicates'
  have hgraphs := congrArg Power.transpose hpredicates'
  rw [Power.transpose_unique rfl, Power.transpose_unique rfl] at hgraphs
  exact (cancel_mono (homToGraph A B)).1 hgraphs

/-- The exponential functor associated to `A`. -/
def expFunctor (A : C) : C ⥤ C where
  obj B := hom A B
  map {B B'} g := homMap (eval A B ≫ g)
  map_id B := by
    rw [Category.comp_id]
    apply homMap_unique
    dsimp only [Exponentiates]
    rw [prod.map_id_id, Category.id_comp]
  map_comp {B B' B''} g h := by
    apply homMap_unique
    dsimp only [Exponentiates]
    rw [prod.map_id_comp, Category.assoc, homMap_exponentiates,
      ← Category.assoc, homMap_exponentiates, Category.assoc]

/-- The exponential universal property as a hom-set equivalence. -/
def homEquiv (A B X : C) : (A ⨯ X ⟶ B) ≃ (X ⟶ hom A B) where
  toFun := homMap
  invFun g := prod.map (𝟙 A) g ≫ eval A B
  left_inv := homMap_exponentiates
  right_inv g := by
    apply homMap_unique (g := g)
    rfl

/-- Product by `A` is left adjoint to the exponential functor. -/
def prodExpAdjunction (A : C) : prod.functor.obj A ⊣ expFunctor A := by
  apply Adjunction.mkOfHomEquiv
  fapply Adjunction.CoreHomEquiv.mk
  · intro X B
    exact homEquiv A B X
  · intro X X' B f g
    dsimp only [homEquiv]
    change prod.map (𝟙 A) (f ≫ g) ≫ eval A B =
      prod.map (𝟙 A) f ≫ prod.map (𝟙 A) g ≫ eval A B
    rw [← Category.assoc, prod.map_map, Category.id_comp]
  · intro X B B' f g
    dsimp only [homEquiv, expFunctor]
    change homMap (f ≫ g) = homMap f ≫ homMap (eval A B ≫ g)
    apply homMap_unique
    dsimp only [Exponentiates]
    rw [prod.map_id_comp, Category.assoc, homMap_exponentiates,
      ← Category.assoc, homMap_exponentiates]

section Cartesian

variable [CartesianMonoidalCategory C]

/-- Power objects and a classifier make a finitely complete category cartesian closed. -/
@[implicit_reducible]
def monoidalClosed : MonoidalClosed C where
  closed A := {
    rightAdj := expFunctor A
    adj := (prodExpAdjunction A).ofNatIsoLeft
      (CartesianMonoidalCategory.tensorLeftIsoProd A).symm }

end Cartesian

end

end Submission.Exponentials
