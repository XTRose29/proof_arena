import Mathlib

-- BEGIN INLINED FILE: Mathlib/Support/fundamental_topos_theory_cdf879d0c2/PiBase.lean
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {C : Type*} [Category C] [HasFiniteLimits C]
-- constructions relative to a chosen classifier
namespace Subobject.Classifier
variable (c : Subobject.Classifier C)
/-- The zero extension of a predicate across a monomorphism. -/
def extendAlong {S T : C} (m : S ⟶ T) [Mono m] (k : S ⟶ c.Ω) : T ⟶ c.Ω :=
  c.χ (pullback.fst k c.truth ≫ m)
instance {S T : C} (m : S ⟶ T) [Mono m] (k : S ⟶ c.Ω) :
    Mono (pullback.fst k c.truth ≫ m) := inferInstance
/-- zero extension really extends a predicate on a subobject. -/
lemma comp_extendAlong {S T : C} (m : S ⟶ T) [Mono m] (k : S ⟶ c.Ω) :
    m ≫ c.extendAlong m k = k := by
  -- use uniqueness of the characteristic morphism of the pullback of `k`
  let R : C := Limits.pullback k c.truth
  let r : R ⟶ S := pullback.fst k c.truth
  haveI : Mono r := inferInstance
  -- the literal pullback square
  have hpb0 : IsPullback r (c.χ₀ R) k c.truth := by
    -- snd to terminal object agrees with χ₀
    have hp : IsPullback (pullback.fst k c.truth) (pullback.snd k c.truth) k c.truth :=
      IsPullback.of_hasPullback _ _
    -- replace second leg by terminal equality
    have hs : pullback.snd k c.truth = c.χ₀ R :=
      c.isTerminalΩ₀.hom_ext _ _
    simpa [r, hs] using hp
  -- outer classifier square
  have hpbBig : IsPullback (r ≫ m) (c.χ₀ R)
      (c.χ (r ≫ m)) c.truth := c.isPullback (r ≫ m)
  have hpb : IsPullback r (c.χ₀ R)
      (m ≫ c.χ (r ≫ m)) c.truth := by
    refine IsPullback.mk' ?_ ?_ ?_
    · simpa [Category.assoc] using hpbBig.w
    · intro Z a b h1 h2
      -- both arrows into R; use big square, cancel mono m
      apply hpbBig.hom_ext
        (by
          -- maps to T equal
          simpa only [Category.assoc] using congrArg (fun z => z ≫ m) h1) h2
    · intro Z a b eq
      -- a:Z→S b:Z→Ω₀ with a ≫ m ≫ χ = b≫truth
      have eq' : (a ≫ m) ≫ c.χ (r ≫ m) = b ≫ c.truth := by
        simpa [Category.assoc] using eq
      obtain ⟨l, hl1, hl2⟩ := hpbBig.exists_lift (a ≫ m) b eq'
      refine ⟨l, ?_, hl2⟩
      apply (cancel_mono m).1
      simpa [Category.assoc] using hl1
  have e1 : m ≫ c.χ (r ≫ m) = c.χ r :=
    c.uniq r (χ' := m ≫ c.χ (r ≫ m)) (χ₀' := c.χ₀ R) hpb
  have e2 : k = c.χ r :=
    c.uniq r (χ' := k) (χ₀' := c.χ₀ R) hpb0
  change m ≫ c.χ (Limits.pullback.fst k c.truth ≫ m) = k
  simpa [r] using (e1.trans e2.symm)
end Subobject.Classifier
end
end CategoryTheory

namespace CategoryTheory
open Opposite
open CategoryTheory.Functor
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u₁ u₂
variable {C : Type u₁} {D : Type u₂} [Category.{v} C] [Category.{v} D]
/-- The presheaf of arrows into `Y` along a functor.  Representability of
these presheaves is a convenient objectwise form of having a right adjoint. -/
abbrev Functor.rightPresheaf (F : C ⥤ D) (Y : D) : Cᵒᵖ ⥤ Type v :=
  F.op ⋙ yoneda.obj Y
/-- Objectwise representability of Hom(`F -`, `Y`) suffices for a right
adjoint. This separates the construction of dependent products from all
functorial bookkeeping: only the representing objects remain. -/
lemma Functor.isLeftAdjoint_of_isRepresentable_rightPresheaf (F : C ⥤ D)
    (H : ∀ Y : D, (F.rightPresheaf Y).IsRepresentable) : F.IsLeftAdjoint := by
  classical
  letI (Y : D) : (F.rightPresheaf Y).IsRepresentable := H Y
  let Gobj : D → C := fun Y => (F.rightPresheaf Y).reprX
  let e : ∀ X : C, ∀ Y : D, (F.obj X ⟶ Y) ≃ (X ⟶ Gobj Y) :=
    fun X Y => (F.rightPresheaf Y).representableBy.homEquiv.symm
  have he : ∀ (X' X : C) (Y : D) (f : X' ⟶ X) (g : F.obj X ⟶ Y),
      e X' Y (F.map f ≫ g) = f ≫ e X Y g := by
    intro X' X Y f g
    -- apply the representing equivalence in the other direction
    change (F.rightPresheaf Y).representableBy.homEquiv.symm (F.map f ≫ g) =
      f ≫ (F.rightPresheaf Y).representableBy.homEquiv.symm g
    apply (F.rightPresheaf Y).representableBy.homEquiv.injective
    -- functor acts by precomposition
    rw [Equiv.apply_symm_apply,
      (F.rightPresheaf Y).representableBy.homEquiv_comp f
        ((F.rightPresheaf Y).representableBy.homEquiv.symm g),
      Equiv.apply_symm_apply]
    rfl

  exact
    (CategoryTheory.Adjunction.adjunctionOfEquivRight (F := F) e he).isLeftAdjoint
end
end CategoryTheory
namespace CategoryTheory
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
/-- Product with an object preserves monomorphisms; using the projections
makes this independent of a particular choice of products. -/
lemma mono_whiskerLeft_cartesian (A : C) {S T : C} (m : S ⟶ T) [Mono m] :
    Mono (A ◁ m) := by
  constructor
  intro Z g h eq
  apply CartesianMonoidalCategory.hom_ext
  · simpa [Category.assoc] using
      congrArg (fun t => t ≫ CartesianMonoidalCategory.fst A T) eq
  · apply (cancel_mono m).1
    simpa [Category.assoc] using
      congrArg (fun t => t ≫ CartesianMonoidalCategory.snd A T) eq

variable [MonoidalClosed C] [HasFiniteLimits C]
/-- Predicates with an extra parameter extend across subobjects, too.  This
is the small categorical heart of the partial-map construction: uncurrying
gives a predicate on a product, the classifier extends it by false, and
currying it back gives a total family. -/
lemma exists_extension_ihom_omega (c : Subobject.Classifier C)
    (A : C) {S T : C} (m : S ⟶ T) [Mono m]
    (q : S ⟶ (ihom A).obj c.Ω) :
    ∃ q' : T ⟶ (ihom A).obj c.Ω, m ≫ q' = q := by
  -- product with `A` is monic
  letI : Mono (A ◁ m) := mono_whiskerLeft_cartesian A m
  let k : A ⊗ S ⟶ c.Ω := uncurry q
  refine ⟨curry (c.extendAlong (A ◁ m) k), ?_⟩
  -- compare the uncurried maps; extension was chosen so that restriction is literal
  -- the naturality law for currying on the left parameter gives the equation.
  rw [← curry_natural_left m (c.extendAlong (A ◁ m) k)]
  dsimp [k]
  rw [c.comp_extendAlong (A ◁ m) (uncurry q)]
  exact curry_uncurry q
end
end CategoryTheory
namespace CategoryTheory
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
lemma isPullback_cartesian_graph {A X : C} (u : X ⟶ A) :
    IsPullback u (lift u (𝟙 X)) (lift (𝟙 A) (𝟙 A)) (A ◁ u) := by
  refine IsPullback.mk' ?_ ?_ ?_
  · apply CartesianMonoidalCategory.hom_ext <;> simp
  · intro T a b h1 h2
    -- first leg already determines maps through the graph
    apply (cancel_mono (lift u (𝟙 X))).1 h2
  · intro T a b h
    have h₁ := congrArg (fun t => t ≫ fst A A) h
    have h₂ := congrArg (fun t => t ≫ snd A A) h
    simp [Category.assoc] at h₁ h₂
    refine ⟨b ≫ snd A X, ?_, ?_⟩
    · simpa only [Category.assoc] using h₂.symm
    · apply CartesianMonoidalCategory.hom_ext
      · simpa [Category.assoc] using h₂.symm.trans h₁
      · simp [Category.assoc]
variable [MonoidalClosed C] [HasFiniteLimits C]
/-- Singleton predicate in a power object. -/
def classifierSingleton (c : Subobject.Classifier C) (A : C) :
    A ⟶ (ihom A).obj c.Ω :=
  curry (c.χ (lift (𝟙 A) (𝟙 A)))
/-- Singletons are separated.  Equivalently every object of a cartesian
closed category with a classifier embeds in the injective power object.
The graph argument avoids any logic on Ω. -/
lemma mono_classifierSingleton (c : Subobject.Classifier C) (A : C) :
    Mono (classifierSingleton c A) := by
  constructor
  intro X g h eq
  have eq' : A ◁ g ≫ c.χ (lift (𝟙 A) (𝟙 A)) =
      A ◁ h ≫ c.χ (lift (𝟙 A) (𝟙 A)) := by
    apply curry_injective
    simpa [classifierSingleton, curry_natural_left] using eq
  -- graph of h has this predicate as characteristic
  have pb_h0 := isPullback_cartesian_graph (A := A) h
  have pb_diag := c.isPullback (lift (𝟙 A) (𝟙 A))
  -- paste diagram
  have pb_h : IsPullback (lift h (𝟙 X)) (c.χ₀ X)
        (A ◁ h ≫ c.χ (lift (𝟙 A) (𝟙 A))) c.truth := by
    -- graph square flipped, then paste its classifier square
    -- pb_h0: top h, side graph
    have ph := pb_h0.flip
    -- IsPullback (graph) h (A◁h) diag
    have pp := ph.paste_vert pb_diag
    -- pp has second leg `h ≫ χ₀ A`, terminally equal χ₀ X
    have term : h ≫ c.χ₀ A = c.χ₀ X := c.isTerminalΩ₀.hom_ext _ _
    simpa [term] using pp
  -- the graph of g lands in that pullback, using equality of predicates
  have commg : lift g (𝟙 X) ≫ (A ◁ h ≫ c.χ (lift (𝟙 A) (𝟙 A))) =
      c.χ₀ X ≫ c.truth := by
    -- replace h predicate by g and use graph pullback pasted
    have pb_g0 := isPullback_cartesian_graph (A := A) g
    have phg := pb_g0.flip
    have ppg := phg.paste_vert pb_diag
    have termg : g ≫ c.χ₀ A = c.χ₀ X := c.isTerminalΩ₀.hom_ext _ _
    have wg : lift g (𝟙 X) ≫ (A ◁ g ≫ c.χ (lift (𝟙 A) (𝟙 A))) =
        c.χ₀ X ≫ c.truth := by simpa [termg] using ppg.w
    simpa [eq'] using wg
  obtain ⟨l, hl1, hl2⟩ := pb_h.exists_lift (lift g (𝟙 X)) (c.χ₀ X) commg
  -- second projection of equality of graphs yields l=id
  have l_id : l = 𝟙 X := by
    have e2 := congrArg (fun t => t ≫ snd A X) hl1
    simpa [Category.assoc] using e2
  have e1 := congrArg (fun t => t ≫ fst A X) hl1
  simpa [Category.assoc, l_id] using e1.symm
end
end CategoryTheory
namespace CategoryTheory
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
 [MonoidalClosed C] [HasFiniteLimits C]
/-- A map defined on a subobject extends after the singleton embedding.
Together with `mono_classifierSingleton`, this is the useful "injective
resolution" first step in the dependent product construction. -/
lemma exists_singleton_extension (c : Subobject.Classifier C)
    {S T A : C} (m : S ⟶ T) [Mono m] (a : S ⟶ A) :
    ∃ q : T ⟶ (ihom A).obj c.Ω,
      m ≫ q = a ≫ classifierSingleton c A := by
  exact exists_extension_ihom_omega c A m (a ≫ classifierSingleton c A)
end
end CategoryTheory

-- END INLINED FILE: Mathlib/Support/fundamental_topos_theory_cdf879d0c2/PiBase.lean

-- BEGIN INLINED FILE: Mathlib/Support/fundamental_topos_theory_cdf879d0c2/SliceClassifier.lean

open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory
namespace Over
noncomputable section
variable {C : Type*} [Category C]
variable [HasBinaryProducts C]

/-- Transpose of a map to the right-adjoint `star` of the slice forgetful functor. -/
def starHom (X : C) {Y : Over X} {A : C} (f : Y.left ⟶ A) :
    Y ⟶ (Over.star X).obj A :=
  (Over.forgetAdjStar X).homEquiv Y A f

@[simp] lemma starHom_left (X : C) {Y : Over X} {A : C} (f : Y.left ⟶ A) :
    (starHom X f).left = Limits.prod.lift Y.hom f := by
  change ((Over.forgetAdjStar X).unit.app Y ≫ (Over.star X).map f).left = _
  -- calculate the unit and the action of `star`
  change ((Over.forgetAdjStar X).unit.app Y).left ≫
    ((Over.star X).map f).left = _
  rw [Over.forgetAdjStar_unit_app_left]
  change Limits.prod.lift Y.hom (𝟙 Y.left) ≫ Limits.prod.map (𝟙 X) f = _
  ext <;> simp

@[simp] lemma starHom_comp (X : C) {Y Z : Over X} {A : C}
    (k : Y ⟶ Z) (f : Z.left ⟶ A) :
    k ≫ starHom X f = starHom X (k.left ≫ f) := by
  apply (Over.forget X).map_injective
  change k.left ≫ (starHom X f).left = (starHom X (k.left ≫ f)).left
  rw [starHom_left, starHom_left]
  change k.left ≫ Limits.prod.lift Z.hom f = Limits.prod.lift Y.hom (k.left ≫ f)
  ext
  · simpa [Category.assoc] using Over.w k
  · simp

@[simp] lemma star_map_comp_starHom (X : C) {Y : Over X} {A B : C}
    (f : Y.left ⟶ A) (k : A ⟶ B) :
    starHom X f ≫ (Over.star X).map k = starHom X (f ≫ k) := by
  -- adjunction naturality
  simpa [starHom] using
    ((Over.forgetAdjStar X).homEquiv_naturality_right f k).symm

/-- If `T` is terminal, its cofree object `X × T -> X` is terminal in the slice. -/
def starIsTerminal (X : C) {T : C} (t : IsTerminal T) :
    IsTerminal ((Over.star X).obj T) := by
  letI u (Y : Over X) : Unique (Y ⟶ (Over.star X).obj T) :=
    { default := starHom X (t.from Y.left)
      uniq := by
        intro f
        apply ((Over.forgetAdjStar X).homEquiv Y T).symm.injective
        exact t.hom_ext _ _ }
  exact IsTerminal.ofUnique _

@[simp] lemma starIsTerminal_from (X : C) {T : C} (t : IsTerminal T)
    (Y : Over X) :
    (starIsTerminal X t).from Y = starHom X (t.from Y.left) := rfl

-- PB square with graphs
lemma isPullback_graph {X U Y A B : C}
    (m : U ⟶ Y) (u : U ⟶ X) (y : Y ⟶ X)
    (a : U ⟶ A) (b : Y ⟶ B) (q : A ⟶ B)
    (hu : m ≫ y = u)
    (h : IsPullback m a b q) :
    IsPullback m (Limits.prod.lift u a)
      (Limits.prod.lift y b) (Limits.prod.map (𝟙 X) q) := by
  -- graph square; reduce to base pullback by elementary universal property
  refine IsPullback.mk' ?w ?ext ?lift
  · ext
    · simp [hu]
    · -- A/B component is base square
      simp [Category.assoc, h.w]
  · intro T φ ψ h₁ h₂
    -- first coordinates give equality through old square using second coordinates
    apply h.hom_ext h₁
      (by
        -- project second on equality of product maps
        simpa [Category.assoc] using congrArg (fun z => z ≫ Limits.prod.snd) h₂)
  · intro T α β hab
    -- α : T ⟶ Y? inspect: fst=m f=bla; square m : U -> Y; snd=graph U -> X×A
    -- targets Xobj=Y, Yobj= X×A. β accordingly
    have hbase : α ≫ b = (β ≫ Limits.prod.snd) ≫ q := by
      -- from equality into X×B, second projection
      simpa [Category.assoc] using
        congrArg (fun z => z ≫ Limits.prod.snd) hab
    obtain ⟨l, hl₁, hl₂⟩ := h.exists_lift α (β ≫ Limits.prod.snd) hbase
    refine ⟨l, hl₁, ?_⟩
    ext
    · -- first component follows β's first via hab first and hu
      -- easier β.first = α≫ y from equality into X×B first
      have hx : α ≫ y = β ≫ Limits.prod.fst := by
        simpa [Category.assoc] using
          congrArg (fun z => z ≫ Limits.prod.fst) hab
      have hx' : l ≫ u = β ≫ Limits.prod.fst := by rw [← hu, ← Category.assoc, hl₁]; exact hx
      simpa [Category.assoc] using hx'
    · simpa [Category.assoc] using hl₂


/-- conversely a pullback between graph maps over `X` yields the pullback on
second components. -/
lemma isPullback_ungraph {X U Y A B : C}
    (m : U ⟶ Y) (u : U ⟶ X) (y : Y ⟶ X)
    (a : U ⟶ A) (b : Y ⟶ X ⨯ B) (q : A ⟶ B)
    (hu : m ≫ y = u)
    (hb : b ≫ Limits.prod.fst = y)
    (h : IsPullback m (Limits.prod.lift u a) b
          (Limits.prod.map (𝟙 X) q)) :
    IsPullback m a (b ≫ Limits.prod.snd) q := by
  refine IsPullback.mk' ?_ ?_ ?_
  · -- commute, second component of graph square
    simpa [Category.assoc] using
      congrArg (fun z => z ≫ Limits.prod.snd) h.w
  · intro T f g h₁ h₂
    apply h.hom_ext h₁
    -- compare arrows to the product
    apply Limits.prod.hom_ext
    · simp [Category.assoc, ← hu, ← Category.assoc, h₁]
    · simpa [Category.assoc] using h₂
  · intro T α β hab
    have hab' : α ≫ b = Limits.prod.lift (α ≫ y) β ≫
        Limits.prod.map (𝟙 X) q := by
      ext
      · -- use that b is over y
        simpa [Category.assoc, hb]
      · -- given equation for second coordinate
        simpa [Category.assoc] using hab
    obtain ⟨l, h₁, h₂⟩ := h.exists_lift α (Limits.prod.lift (α ≫ y) β) hab'
    refine ⟨l, h₁, ?_⟩
    simpa [Category.assoc] using
      congrArg (fun z => z ≫ Limits.prod.snd) h₂

open Subobject
/-- A subobject classifier in `C` yields one in each slice. -/
def classifierOver (X : C) (c : Subobject.Classifier C) :
    Subobject.Classifier (Over X) := by
  let t := starIsTerminal X c.isTerminalΩ₀
  refine Subobject.Classifier.mkOfTerminalΩ₀
    ((Over.star X).obj c.Ω₀) t ((Over.star X).obj c.Ω)
    ((Over.star X).map c.truth)
    (fun {U Y} m _ => starHom X (c.χ m.left))
    ?_ ?_
  · intro U Y m hm
    -- reflect the graph pullback via forget
    apply IsPullback.of_map_of_faithful (Over.forget X)
    -- identify the underlying graph square
    change IsPullback m.left _ _ _
    -- rewrites
    change IsPullback m.left (starHom X (c.χ₀ U.left)).left
      (starHom X (c.χ m.left)).left (((Over.star X).map c.truth).left)
    rw [starHom_left, starHom_left]
    change IsPullback m.left (Limits.prod.lift U.hom _)
      (Limits.prod.lift Y.hom _) (Limits.prod.map (𝟙 X) c.truth)
    -- map is product map
    apply isPullback_graph m.left U.hom Y.hom
      (c.χ₀ U.left) (c.χ m.left) c.truth
        (by simpa using Over.w m)
    apply c.isPullback m.left
  · intro U Y m hm k hk
    -- Show equality of characteristic maps by transpose adjunction.
    -- hk graph PB. Underlying image is a PB, and project second coordinate.
    apply ((Over.forgetAdjStar X).homEquiv Y c.Ω).symm.injective
    change ((Over.forgetAdjStar X).homEquiv Y c.Ω).symm k = _
    change _ = ((Over.forgetAdjStar X).homEquiv Y c.Ω).symm
      (((Over.forgetAdjStar X).homEquiv Y c.Ω) (c.χ m.left))
    rw [Equiv.symm_apply_apply]
    -- compute inverse transpose: counit = snd
    -- express it as k.left ≫ snd
    have hk_left :
        IsPullback m.left
          (((t.from U)).left)
          k.left (((Over.star X).map c.truth).left) :=
      hk.map (Over.forget X)
    -- project product square down along snd, recovering classifier square.
    have hsquare : IsPullback m.left (c.χ₀ U.left)
          (k.left ≫ Limits.prod.snd) c.truth := by
      -- a morphism into `star` is a graph: its first component is
      -- the structure morphism to the base.
      have hbasek : k.left ≫ Limits.prod.fst = Y.hom := by
        -- this is just the condition for a morphism in the slice
        have hw := Over.w k
        -- the structural map of `star` is the first projection
        change k.left ≫ (Limits.prod.lift (Limits.prod.fst) (𝟙 _) ≫ Limits.prod.fst) = Y.hom at hw
        simpa using hw
      -- Put the mapped square in the graph form, then forget the first
      -- component using the elementary converse lemma.
      have hk' : IsPullback m.left
          (Limits.prod.lift U.hom (c.χ₀ U.left)) k.left
          (Limits.prod.map (𝟙 X) c.truth) := by
        -- rewrite the three computable arrows
        change IsPullback m.left
          ((starIsTerminal X c.isTerminalΩ₀).from U).left
          k.left (((Over.star X).map c.truth).left) at hk_left
        rw [starIsTerminal_from, starHom_left] at hk_left
        change IsPullback m.left (Limits.prod.lift U.hom (c.χ₀ U.left))
          k.left (Limits.prod.map (𝟙 X) c.truth) at hk_left
        exact hk_left
      exact isPullback_ungraph m.left U.hom Y.hom (c.χ₀ U.left)
        k.left c.truth (by simpa using Over.w m) hbasek hk' 
    have hu := c.uniq m.left (χ' := k.left ≫ Limits.prod.snd)
      (χ₀' := c.χ₀ U.left) hsquare
    -- inverse adjunction formula
    simpa [Adjunction.homEquiv, Over.forgetAdjStar_counit_app] using hu
end
end Over
end CategoryTheory

namespace CategoryTheory
noncomputable section
variable {C : Type*} [Category C] [HasBinaryProducts C]
/-- Existence version of `classifierOver`. -/
def hasSubobjectClassifierOver [h : HasSubobjectClassifier C] (X : C) :
    HasSubobjectClassifier (Over X) :=
  { exists_classifier := ⟨Over.classifierOver X h.exists_classifier.some⟩ }
end
end CategoryTheory

-- END INLINED FILE: Mathlib/Support/fundamental_topos_theory_cdf879d0c2/SliceClassifier.lean

-- BEGIN INLINED FILE: Mathlib/Support/fundamental_topos_theory_cdf879d0c2/SliceClosedReduction.lean

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
namespace CategoryTheory
open Functor
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {C : Type*} [Category C] [HasPullbacks C]

attribute [local instance] Over.cartesianMonoidalCategory

/-- Tensoring by an object in a slice is pulling back along it, then composing
back down.  This comparison is independent of any closed structure. -/
def tensorLeftIsoPullbackMap {X : C} (Y : Over X) :
    tensorLeft Y ≅ Over.pullback Y.hom ⋙ Over.map Y.hom := by
  refine NatIso.ofComponents (fun A => ?_) ?_
  · refine Over.isoMk (pullbackSymmetry Y.hom A.hom) ?_
    -- structural maps
    simp
  · intro A B k
    -- compare by the two projections
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · -- projection to A? after symmetry
      simp [Over.whiskerLeft_left]
    · simp [Over.whiskerLeft_left]

-- variant inspect
/-- If every pullback functor of `C` is a left adjoint, its slices are
cartesian closed (for the standard pullback cartesian structure).  The
separate hard part of the topos theorem is exactly the premise. -/
def monoidalClosedOver_of_pullback_left
    (H : ∀ {I J : C} (f : I ⟶ J), (Over.pullback f).IsLeftAdjoint)
    (X : C) :
    let cm : CartesianMonoidalCategory (Over X) := Over.cartesianMonoidalCategory X
    @MonoidalClosed (Over X) _ cm.toMonoidalCategory := by
  dsimp
  constructor
  intro Y
  haveI : (Over.pullback Y.hom).IsLeftAdjoint := H _
  -- map is always a left adjoint
  haveI : (Over.map Y.hom).IsLeftAdjoint :=
    ⟨_, ⟨Over.mapPullbackAdj Y.hom⟩⟩
  let L : Over X ⥤ Over X := Over.pullback Y.hom ⋙ Over.map Y.hom
  haveI : L.IsLeftAdjoint := inferInstance
  let R : Over X ⥤ Over X := L.rightAdjoint
  exact
    { rightAdj := R
      adj := Adjunction.ofNatIsoLeft (Adjunction.ofIsLeftAdjoint L)
        (tensorLeftIsoPullbackMap Y).symm }
end
end CategoryTheory

-- END INLINED FILE: Mathlib/Support/fundamental_topos_theory_cdf879d0c2/SliceClosedReduction.lean

-- BEGIN INLINED FILE: Mathlib/Support/fundamental_topos_theory_cdf879d0c2/PiConstruct.lean
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Subobject.Classifier
variable {C : Type*} [Category C] [HasFiniteLimits C]
-- helper: base change of the zero extension of a predicate
lemma comp_extendAlong_pullback (c : Subobject.Classifier C)
    {S T S' T' : C} (m : S ⟶ T) [Mono m]
    (m' : S' ⟶ T') [Mono m'] (h : S' ⟶ S) (g : T' ⟶ T)
    (sq : IsPullback m' h g m) (p : S ⟶ c.Ω) :
    g ≫ c.extendAlong m p = c.extendAlong m' (h ≫ p) := by
  -- first, the pullback of the ``truth'' part
  let R : C := Limits.pullback p c.truth
  let R' : C := Limits.pullback (h ≫ p) c.truth
  let s : R ⟶ S := pullback.fst p c.truth
  let z : R ⟶ c.Ω₀ := pullback.snd p c.truth
  let s' : R' ⟶ S' := pullback.fst (h ≫ p) c.truth
  let z' : R' ⟶ c.Ω₀ := pullback.snd (h ≫ p) c.truth
  let t : R' ⟶ R := pullback.lift (s' ≫ h) z'
    (by simpa [s', z', Category.assoc] using (pullback.condition : pullback.fst (h ≫ p) c.truth ≫ (h ≫ p) = _))
  have ht_s : t ≫ s = s' ≫ h := by
    simp [t, s]
  have ht_z : t ≫ z = z' := by
    simp [t, z]
  have st : IsPullback s' t h s := by
    refine IsPullback.mk' ?_ ?_ ?_
    · simpa [ht_s]
    · intro Z a b h1 h2
      -- use the literal pullback of h≫p and truth
      apply (IsPullback.of_hasPullback (h ≫ p) c.truth).hom_ext h1
      -- second projection through t
      -- b,b' : maps to R
      -- equality t components follows from h2
      have ez := congrArg (fun q => q ≫ z) h2
      -- reassociate and use the second projection of `t`
      simpa [Category.assoc, ht_z] using ez
    · intro Z a b hab
      -- solve using the literal small pullback
      have hz : a ≫ (h ≫ p) = (b ≫ z) ≫ c.truth := by
        -- s≫p = z≫truth
        calc
          a ≫ (h ≫ p) = (a ≫ h) ≫ p := by simp [Category.assoc]
          _ = (b ≫ s) ≫ p := by rw [hab]
          _ = b ≫ (s ≫ p) := by simp [Category.assoc]
          _ = b ≫ (z ≫ c.truth) := by rw [pullback.condition]
          _ = (b ≫ z) ≫ c.truth := by simp [Category.assoc]
      let l : Z ⟶ R' := pullback.lift a (b ≫ z) hz
      refine ⟨l, ?_, ?_⟩
      · simp [l, s']
      · -- check the two projections to the old pullback
        apply pullback.hom_ext
        ·
          change (l ≫ t) ≫ s = b ≫ s
          rw [Category.assoc, ht_s]
          rw [← Category.assoc]
          rw [show l ≫ s' = a by simp [l, s']]
          exact hab
        ·
          change (l ≫ t) ≫ z = b ≫ z
          rw [Category.assoc, ht_z]
          simp [l, z']
  -- paste the two pullbacks
  have sn : IsPullback (s' ≫ m') t g (s ≫ m) := by
    -- top row s' then m'
    have := st.paste_horiz sq
    -- the common vertical in sq is h; orientations match
    simpa using this
  have big : IsPullback (s' ≫ m') (c.χ₀ R')
      (g ≫ c.χ (s ≫ m)) c.truth := by
    have bot := c.isPullback (s ≫ m)
    have bp := sn.paste_vert bot
    have term : t ≫ c.χ₀ R = c.χ₀ R' := c.isTerminalΩ₀.hom_ext _ _
    simpa [term] using bp
  -- the characteristic arrow of the pulled-back composite is therefore it
  have hu : g ≫ c.χ (s ≫ m) = c.χ (s' ≫ m') := c.uniq _ big
  simpa [Subobject.Classifier.extendAlong, s, s', Category.assoc] using hu
end Subobject.Classifier
end
end CategoryTheory
namespace CategoryTheory
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {C : Type*} [Category C] [CartesianMonoidalCategory C]
  [HasFiniteLimits C]

lemma mono_pullback_graph_tensor {I J B : C} (f : I ⟶ J) (b : B ⟶ J) :
    Mono (lift (pullback.snd b f) (pullback.fst b f) :
      Limits.pullback b f ⟶ I ⊗ B) := by
  constructor
  intro Z x y e
  apply pullback.hom_ext
  · -- projection to B
    have h := congrArg (fun t => t ≫ snd I B) e
    simpa [Category.assoc] using h
  · have h := congrArg (fun t => t ≫ fst I B) e
    simpa [Category.assoc] using h

-- the graph inclusions of the inverse images form a pullback
lemma isPullback_pullback_graph_tensor {I J W B : C}
    (f : I ⟶ J) (w : W ⟶ J) (y : B ⟶ W) (b : B ⟶ J)
    (hy : y ≫ w = b) :
    let n : Limits.pullback b f ⟶ Limits.pullback w f :=
      pullback.lift (pullback.fst b f ≫ y) (pullback.snd b f)
        (by simpa [Category.assoc, hy] using (pullback.condition :
            pullback.fst b f ≫ b = pullback.snd b f ≫ f))
    IsPullback
      (lift (pullback.snd b f) (pullback.fst b f) :
        Limits.pullback b f ⟶ I ⊗ B)
      n (I ◁ y)
      (lift (pullback.snd w f) (pullback.fst w f) :
        Limits.pullback w f ⟶ I ⊗ W) := by
  dsimp
  let n : Limits.pullback b f ⟶ Limits.pullback w f :=
      pullback.lift (pullback.fst b f ≫ y) (pullback.snd b f)
        (by simpa [Category.assoc, hy] using (pullback.condition :
            pullback.fst b f ≫ b = pullback.snd b f ≫ f))
  -- retain name for simplification
  change IsPullback
      (lift (pullback.snd b f) (pullback.fst b f)) n (I ◁ y)
      (lift (pullback.snd w f) (pullback.fst w f))
  refine IsPullback.mk' ?_ ?_ ?_
  · apply CartesianMonoidalCategory.hom_ext
    · simp [Category.assoc, n]
    · simp [Category.assoc, n]
  · intro T a q h1 h2
    -- `m_B` is monic
    letI : Mono (lift (pullback.snd b f) (pullback.fst b f) :
        Limits.pullback b f ⟶ I ⊗ B) := mono_pullback_graph_tensor f b
    exact (cancel_mono
      (lift (pullback.snd b f) (pullback.fst b f) :
        Limits.pullback b f ⟶ I ⊗ B)).1 h1
  · intro T a q h -- a:T→I⊗B, q:T→PB_W and a≫(I◁y)=q≫mW
    -- the coordinates in `I` and `B` determine the lift
    -- use the map to the ordinary pullback b f
    have hab : (a ≫ snd I B) ≫ b = (a ≫ fst I B) ≫ f := by
      -- from q condition and hy
      have hx := congrArg (fun t => t ≫ snd I W) h
      have hi := congrArg (fun t => t ≫ fst I W) h
      -- hx : B coordinate after y equals q.fst
      -- hi : I coordinate equals q.snd
      simp [Category.assoc] at hx hi
      calc
        (a ≫ snd I B) ≫ b = (a ≫ snd I B) ≫ y ≫ w := by rw [← hy]
        _ = (q ≫ pullback.fst w f) ≫ w := by
              simpa [Category.assoc] using congrArg (fun z => z ≫ w) hx
        _ = (q ≫ pullback.snd w f) ≫ f := by
              simp [Category.assoc, pullback.condition]
        _ = (a ≫ fst I B) ≫ f := by rw [hi]
    let l : T ⟶ Limits.pullback b f :=
      pullback.lift (a ≫ snd I B) (a ≫ fst I B) hab
    refine ⟨l, ?_, ?_⟩
    · apply CartesianMonoidalCategory.hom_ext
      · simp [l, Category.assoc]
      · simp [l, Category.assoc]
    · apply pullback.hom_ext
      · -- B-to-W coordinate
        -- obtained from h's W-coordinate
        have hx := congrArg (fun t => t ≫ snd I W) h
        simpa [l, n, Category.assoc] using hx
      · have hi := congrArg (fun t => t ≫ fst I W) h
        simpa [l, n, Category.assoc] using hi
end
end CategoryTheory

namespace CategoryTheory
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
-- product with a fixed object preserves pullbacks (a coordinate proof avoids
-- any chosen finite-limit-preservation structure).
lemma isPullback_whiskerLeft_cartesian (A : C)
    {X Y Z W : C} {r : X ⟶ Y} {s : X ⟶ Z} {t : Y ⟶ W} {u : Z ⟶ W}
    (h : IsPullback r s t u) :
    IsPullback (A ◁ r) (A ◁ s) (A ◁ t) (A ◁ u) := by
  refine IsPullback.mk' ?_ ?_ ?_
  · -- functoriality
    simp [← MonoidalCategory.whiskerLeft_comp, h.w]
  · intro Q f g h1 h2
    apply CartesianMonoidalCategory.hom_ext
    · -- the fixed coordinate can be read from either side
      have q := congrArg (fun z => z ≫ fst A Y) h1
      simpa [Category.assoc] using q
    · -- the moving coordinate is the old pullback
      apply h.hom_ext
      · have q := congrArg (fun z => z ≫ snd A Y) h1
        simpa [Category.assoc] using q
      · have q := congrArg (fun z => z ≫ snd A Z) h2
        simpa [Category.assoc] using q
  · intro Q a b hab
    have ac : a ≫ fst A Y = b ≫ fst A Z := by
      have e := congrArg (fun q => q ≫ fst A W) hab
      simpa [Category.assoc] using e
    have mov : (a ≫ snd A Y) ≫ t = (b ≫ snd A Z) ≫ u := by
      have e := congrArg (fun q => q ≫ snd A W) hab
      simpa [Category.assoc] using e
    obtain ⟨q, q1, q2⟩ := h.exists_lift (a ≫ snd A Y) (b ≫ snd A Z) mov
    refine ⟨lift (a ≫ fst A Y) q, ?_, ?_⟩
    · apply CartesianMonoidalCategory.hom_ext
      · simp [Category.assoc]
      · simpa [Category.assoc] using q1
    · apply CartesianMonoidalCategory.hom_ext
      · simpa [Category.assoc] using ac
      · simpa [Category.assoc] using q2
end
end CategoryTheory
namespace CategoryTheory
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
 [MonoidalClosed C] [HasFiniteLimits C]
namespace Subobject.Classifier
/-- A useful, canonical total encoding of a partially defined map to a power
object. Notice that it requires no choice: its values outside the subobject
are false. -/
def partialExtend (c : Subobject.Classifier C) (K : C)
    {S T : C} (m : S ⟶ T) [Mono m]
    (q : S ⟶ (ihom K).obj c.Ω) : T ⟶ (ihom K).obj c.Ω :=
  letI : Mono (K ◁ m) := mono_whiskerLeft_cartesian K m
  curry (c.extendAlong (K ◁ m) (uncurry q))

lemma comp_partialExtend (c : Subobject.Classifier C) (K : C)
    {S T : C} (m : S ⟶ T) [Mono m]
    (q : S ⟶ (ihom K).obj c.Ω) :
    m ≫ c.partialExtend K m q = q := by
  dsimp [partialExtend]
  rw [← curry_natural_left]
  letI : Mono (K ◁ m) := mono_whiskerLeft_cartesian K m
  rw [c.comp_extendAlong]
  exact curry_uncurry _

lemma comp_uncurry_eq {A X X' Y : C}
    (g : X ⟶ X') (q : X' ⟶ (ihom A).obj Y) :
    (A ◁ g) ≫ uncurry q = uncurry (g ≫ q) := by
  apply curry_injective (A := A)
  simpa [curry_natural_left]

lemma partialExtend_pullback (c : Subobject.Classifier C) (K : C)
    {S T S' T' : C} (m : S ⟶ T) [Mono m]
    (m' : S' ⟶ T') [Mono m'] (h : S' ⟶ S) (g : T' ⟶ T)
    (sq : IsPullback m' h g m)
    (q : S ⟶ (ihom K).obj c.Ω) :
    g ≫ c.partialExtend K m q =
       c.partialExtend K m' (h ≫ q) := by
  dsimp [partialExtend]
  -- first move the parameter through curry
  rw [← curry_natural_left]
  letI im : Mono (K ◁ m) := mono_whiskerLeft_cartesian K m
  letI im' : Mono (K ◁ m') := mono_whiskerLeft_cartesian K m'
  rw [c.comp_extendAlong_pullback (K ◁ m) (K ◁ m') (K ◁ h)
    (K ◁ g) (isPullback_whiskerLeft_cartesian K sq) (uncurry q)]
  rw [comp_uncurry_eq h q]
end Subobject.Classifier
end
end CategoryTheory
namespace CategoryTheory
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
variable {C : Type u} [Category.{v} C]
 [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]
namespace Subobject.Classifier
/-- The zero-filled code of a partial functional relation is a fixed point of
zero-filling again on the universal graph. This is the `q₀ = ext` equalizer
in the construction of Π. Written with arbitrary square, this avoids all
strictness choices for pullbacks. -/
lemma curry_partialExtend_fixed (c : Subobject.Classifier C)
    {I K W B S S' : C}
    (m : S ⟶ I ⊗ W) [Mono m]
    (mb : S' ⟶ I ⊗ B) [Mono mb]
    (n : S' ⟶ S) (y : B ⟶ W)
    (sq : IsPullback mb n (I ◁ y) m)
    (t : W ⟶ (ihom I).obj ((ihom K).obj c.Ω))
    (q : S' ⟶ (ihom K).obj c.Ω)
    (hq : mb ≫ uncurry (y ≫ t) = q) :
    y ≫ curry (c.partialExtend K m (m ≫ uncurry t)) =
      curry (c.partialExtend K mb q) := by
  -- the restriction of the universal family to the small graph is q
  have hr : n ≫ (m ≫ uncurry t) = q := by
    rw [← hq]
    rw [← Category.assoc, ← sq.w]
    simp [Category.assoc, Subobject.Classifier.comp_uncurry_eq]
  rw [← curry_natural_left]
  rw [c.partialExtend_pullback K m mb n (I ◁ y) sq (m ≫ uncurry t)]
  rw [hr]
end Subobject.Classifier
end
end CategoryTheory

-- END INLINED FILE: Mathlib/Support/fundamental_topos_theory_cdf879d0c2/PiConstruct.lean

namespace Submission

-- BEGIN INLINED FILE: Main.lean

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace LeanEval.ToposTheory

/-!
# The fundamental theorem of topos theory

`fundamental_topos_theory`: the slice category `E/X` of an elementary topos `E`
is again an elementary topos. The trusted helper `IsTopos` (a non-hole) bundles
the four Mathlib classes that make up "elementary topos". Mathlib has finite
limits and cartesian-monoidal structure on `Over X` and a subobject-classifier
class, but neither `MonoidalClosed (Over X)` (the locally-cartesian-closed
upgrade) nor `HasSubobjectClassifier (Over X)` — so no fundamental theorem.

Category-(b) candidate from §54 of the Knill survey.
-/


open _root_.CategoryTheory _root_.CategoryTheory.Limits

/-- An **elementary topos**: finite limits, a cartesian closed structure
(cartesian-monoidal with internal homs), and a subobject classifier. -/
def IsTopos (E : Type*) [Category E] : Prop :=
  HasFiniteLimits E ∧
  ∃ cm : CartesianMonoidalCategory E,
    (letI : MonoidalCategory E := cm.toMonoidalCategory
     Nonempty (MonoidalClosed E)) ∧
    HasSubobjectClassifier E



end LeanEval.ToposTheory

open LeanEval.ToposTheory
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem fundamental_topos_theory {E : Type*} [Category E]
    (hE : IsTopos E) (X : E) : IsTopos (Over X) :=
/-ResultProofBegin-/by
  classical
  rcases hE with ⟨hfin, cm, hcl, hsub⟩
  letI : HasFiniteLimits E := hfin
  letI : CartesianMonoidalCategory E := cm
  letI : MonoidalCategory E := cm.toMonoidalCategory
  have hmc : Nonempty (MonoidalClosed E) := hcl
  letI : MonoidalClosed E := hmc.some
  letI : HasSubobjectClassifier E := hsub
  -- the underlying finite limits of a slice and its cartesian structure are
  -- already provided by the limit construction for over categories
  refine ⟨(inferInstance : HasFiniteLimits (Over X)), ?_⟩
  let cmX : CartesianMonoidalCategory (Over X) :=
    CategoryTheory.Over.cartesianMonoidalCategory X
  -- all that remains here, beyond the classifier construction below, is
  -- the locally-cartesian-closed part
  have hclosedX :
      letI : MonoidalCategory (Over X) := cmX.toMonoidalCategory
      Nonempty (MonoidalClosed (Over X)) := by
        -- after identifying tensor product with pullback-then-compose, the
        -- outstanding LCC step is precisely that every base change in a
        -- topos is a left adjoint
        have hpb : ∀ {I J : E} (f : I ⟶ J),
            (CategoryTheory.Over.pullback f).IsLeftAdjoint := by
          intro I J f
          -- it is enough to represent the functor of arrows into each
          -- object of the fibre; functoriality of the dependent product is
          -- then formal (`adjunctionOfEquivRight`).
          apply CategoryTheory.Functor.isLeftAdjoint_of_isRepresentable_rightPresheaf
            (CategoryTheory.Over.pullback f)
          intro A
          -- We fix the classifier.  The representing object is the usual
          -- object of total functional relations.  Writing it down explicitly
          -- avoids any appeal to a choice of dependent products.
          let c : CategoryTheory.Subobject.Classifier E :=
            CategoryTheory.HasSubobjectClassifier.exists_classifier.some
          let P : E := (CategoryTheory.ihom A.left).obj c.Ω
          let e : A.left ⟶ P :=
            CategoryTheory.classifierSingleton c A.left
          letI he : Mono e := CategoryTheory.mono_classifierSingleton c A.left
          let d : A.left ⟶ I ⊗ P :=
            CategoryTheory.CartesianMonoidalCategory.lift A.hom e
          letI hd : Mono d := by
            constructor
            intro Z x y h
            apply (cancel_mono e).1
            have hh := congrArg (fun t => t ≫
              CategoryTheory.CartesianMonoidalCategory.snd I P) h
            simpa [d, Category.assoc] using hh
          let Q : E := (CategoryTheory.ihom I).obj P
          let V : E := (CategoryTheory.ihom I).obj c.Ω
          -- a point of W is `j` together with a total, zero-filled predicate;
          -- the two equalizers below impose (i) the zero-fill fixed point
          -- and (ii) the condition that on `f i = j` it is the graph of a
          -- unique `A`-element.
          let W : E := J ⊗ Q
          let w : W ⟶ J := CategoryTheory.CartesianMonoidalCategory.fst J Q
          let q₀ : W ⟶ Q := CategoryTheory.CartesianMonoidalCategory.snd J Q
          let S : E := Limits.pullback w f
          let m : S ⟶ I ⊗ W :=
            CategoryTheory.CartesianMonoidalCategory.lift
              (pullback.snd w f) (pullback.fst w f)
          letI hm : Mono m :=
            CategoryTheory.mono_pullback_graph_tensor f w
          let val : I ⊗ W ⟶ P :=
            CategoryTheory.MonoidalClosed.uncurry q₀
          let r : S ⟶ P := m ≫ val
          let bad : S ⟶ c.Ω :=
            CategoryTheory.CartesianMonoidalCategory.lift
              (pullback.snd w f) r ≫ c.χ d
          let good : S ⟶ c.Ω := c.χ₀ S ≫ c.truth
          let u : W ⟶ V :=
            CategoryTheory.MonoidalClosed.curry (c.extendAlong m bad)
          let v : W ⟶ V :=
            CategoryTheory.MonoidalClosed.curry (c.extendAlong m good)
          let mA : A.left ⊗ S ⟶ A.left ⊗ (I ⊗ W) := A.left ◁ m
          letI hmA : Mono mA :=
            CategoryTheory.mono_whiskerLeft_cartesian A.left m
          let hval : I ⊗ W ⟶ P :=
            CategoryTheory.MonoidalClosed.curry
              (c.extendAlong mA (CategoryTheory.MonoidalClosed.uncurry r))
          let ext : W ⟶ Q := CategoryTheory.MonoidalClosed.curry hval
          let R : E := Limits.equalizer q₀ ext
          let z : R ⟶ W := Limits.equalizer.ι q₀ ext
          let T : E := Limits.equalizer (z ≫ u) (z ≫ v)
          let j : T ⟶ R := Limits.equalizer.ι (z ≫ u) (z ≫ v)
          let inc : T ⟶ W := j ≫ z
          let D : Over J := Over.mk (inc ≫ w)
          -- At this point the only remaining issue is the natural bijection.
          -- Restriction is monic: a graph is recovered by the fixed-point
          -- equation.  Both the zero-extension under base change and the
          -- product graph squares are proved in `PiConstruct`.
          have inc_fix : inc ≫ q₀ = inc ≫ ext := by
            change (j ≫ z) ≫ q₀ = (j ≫ z) ≫ ext
            simp only [Category.assoc]
            rw [equalizer.condition q₀ ext]
          have inc_good : inc ≫ u = inc ≫ v := by
            change (j ≫ z) ≫ u = (j ≫ z) ≫ v
            simpa [Category.assoc] using
              (equalizer.condition (z ≫ u) (z ≫ v))
          letI minc : Mono inc := by dsimp [inc, j, z]; infer_instance
          -- Encoding a section over `pullback B f`: outside that graph put
          -- the false predicate. `comp_partialExtend` says that this operation
          -- restricts exactly to the given graph, and
          -- `curry_partialExtend_fixed` proves the first equalizer condition.
          let tb {B : Over J}
              (k : (Over.pullback f).obj B ⟶ A) : B.left ⟶ Q :=
            let mb : Limits.pullback B.hom f ⟶ I ⊗ B.left :=
              CategoryTheory.CartesianMonoidalCategory.lift
                (pullback.snd B.hom f) (pullback.fst B.hom f)
            letI : Mono mb :=
              CategoryTheory.mono_pullback_graph_tensor f B.hom
            CategoryTheory.MonoidalClosed.curry
              (c.partialExtend A.left mb (k.left ≫ e))
          refine CategoryTheory.Functor.RepresentableBy.isRepresentable (Y := D) ?_
          -- construct maps in both directions; for a code in the two
          -- equalizers its restriction on the graph is a genuine section.
          -- Some handy notation for the graph of an object over J.
          let mb0 (B : Over J) : Limits.pullback B.hom f ⟶ I ⊗ B.left :=
            CategoryTheory.CartesianMonoidalCategory.lift
              (pullback.snd B.hom f) (pullback.fst B.hom f)
          let nOf (B : Over J) (y₁ : B.left ⟶ W)
              (hy : y₁ ≫ w = B.hom) :
              Limits.pullback B.hom f ⟶ S :=
            pullback.lift (pullback.fst B.hom f ≫ y₁)
              (pullback.snd B.hom f)
              (by
                simpa [S, Category.assoc, hy] using
                  (pullback.condition : pullback.fst B.hom f ≫ B.hom = _))
          have sqOf (B : Over J) (y₁ : B.left ⟶ W)
              (hy : y₁ ≫ w = B.hom) :
              IsPullback (mb0 B) (nOf B y₁ hy) (I ◁ y₁) m := by
            dsimp [mb0, nOf, S, m]
            exact CategoryTheory.isPullback_pullback_graph_tensor f w y₁ B.hom hy
          let yOf {B : Over J}
              (k : (Over.pullback f).obj B ⟶ A) : B.left ⟶ W :=
            CategoryTheory.CartesianMonoidalCategory.lift B.hom (tb k)
          have yOf_w {B : Over J}
              (k : (Over.pullback f).obj B ⟶ A) :
              yOf k ≫ w = B.hom := by
            dsimp [yOf, w, W]; simp
          have yOf_q {B : Over J}
              (k : (Over.pullback f).obj B ⟶ A) :
              yOf k ≫ q₀ = tb k := by
            dsimp [yOf, q₀, W]; simp
          -- The first, fixed-point equalizer.
          have yOf_fix {B : Over J}
              (k : (Over.pullback f).obj B ⟶ A) :
              yOf k ≫ q₀ = yOf k ≫ ext := by
            let mbi : Limits.pullback B.hom f ⟶ I ⊗ B.left := mb0 B
            letI imb : Mono mbi :=
              CategoryTheory.mono_pullback_graph_tensor f B.hom
            let nn : Limits.pullback B.hom f ⟶ S :=
              nOf B (yOf k) (yOf_w k)
            have sq : IsPullback mbi nn (I ◁ yOf k) m :=
              sqOf B (yOf k) (yOf_w k)
            have hq : mbi ≫ CategoryTheory.MonoidalClosed.uncurry
                    (yOf k ≫ q₀) = k.left ≫ e := by
              -- restriction of the zero extension is the given graph
              rw [yOf_q]
              dsimp [tb]
              rw [CategoryTheory.MonoidalClosed.uncurry_curry]
              exact c.comp_partialExtend A.left mbi (k.left ≫ e)
            have hx := c.curry_partialExtend_fixed
              (K := A.left) (I := I) (m := m) (mb := mbi)
              (n := nn) (y := yOf k) sq (t := q₀)
              (q := k.left ≫ e) hq
            -- unfold the three nested curries in `ext`
            calc
              yOf k ≫ q₀ = tb k := yOf_q k
              _ = CategoryTheory.MonoidalClosed.curry
                    (c.partialExtend A.left mbi (k.left ≫ e)) := by
                      rfl
              _ = yOf k ≫ ext := by
                simpa [ext, hval, CategoryTheory.Subobject.Classifier.partialExtend,
                  mA, r, val, mbi, nn] using hx.symm
          -- The graph of k is good on the fibre, hence the second
          -- equalizer as well.
          have yOf_good {B : Over J}
              (k : (Over.pullback f).obj B ⟶ A) :
              yOf k ≫ u = yOf k ≫ v := by
            let mbi : Limits.pullback B.hom f ⟶ I ⊗ B.left := mb0 B
            letI imb : Mono mbi :=
              CategoryTheory.mono_pullback_graph_tensor f B.hom
            let nn : Limits.pullback B.hom f ⟶ S :=
              nOf B (yOf k) (yOf_w k)
            have sq : IsPullback mbi nn (I ◁ yOf k) m :=
              sqOf B (yOf k) (yOf_w k)
            have hq : mbi ≫ CategoryTheory.MonoidalClosed.uncurry
                    (yOf k ≫ q₀) = k.left ≫ e := by
              rw [yOf_q]
              dsimp [tb]
              rw [CategoryTheory.MonoidalClosed.uncurry_curry]
              exact c.comp_partialExtend A.left mbi (k.left ≫ e)
            have nr : nn ≫ r = k.left ≫ e := by
              calc
                nn ≫ r = nn ≫ m ≫ val := by simp [r, Category.assoc]
                _ = (mbi ≫ (I ◁ yOf k)) ≫ val := by
                  rw [sq.w]; simp [Category.assoc]
                _ = mbi ≫ CategoryTheory.MonoidalClosed.uncurry
                      (yOf k ≫ q₀) := by
                  rw [Category.assoc]
                  simp [val, CategoryTheory.Subobject.Classifier.comp_uncurry_eq]
                _ = k.left ≫ e := hq
            have nsnd : nn ≫ pullback.snd w f =
                    pullback.snd B.hom f := by
              dsimp [nn, nOf]
              apply Limits.pullback.lift_snd
            have kw : k.left ≫ A.hom = pullback.snd B.hom f := by
              simpa using k.w
            have ld :
                CategoryTheory.CartesianMonoidalCategory.lift
                    (pullback.snd B.hom f) (k.left ≫ e) =
                  k.left ≫ d := by
              symm
              calc
                k.left ≫ d =
                    CategoryTheory.CartesianMonoidalCategory.lift
                      (k.left ≫ A.hom) (k.left ≫ e) := by
                        apply CategoryTheory.CartesianMonoidalCategory.comp_lift
                _ = _ := by rw [kw]
            have ll : nn ≫
                  CategoryTheory.CartesianMonoidalCategory.lift
                    (pullback.snd w f) r = k.left ≫ d := by
              rw [CategoryTheory.CartesianMonoidalCategory.comp_lift]
              rw [nsnd, nr]
              exact ld
            have nb : nn ≫ bad =
                (k.left ≫ d) ≫ c.χ d := by
              calc
                nn ≫ bad = (nn ≫
                    CategoryTheory.CartesianMonoidalCategory.lift
                      (pullback.snd w f) r) ≫ c.χ d := by
                        simp only [bad, Category.assoc]
                _ = _ := by rw [ll]
            have ng : nn ≫ good =
                  c.χ₀ (Limits.pullback B.hom f) ≫ c.truth := by
              dsimp [good]
              rw [← Category.assoc]
              have hterm : nn ≫ c.χ₀ S =
                    c.χ₀ (Limits.pullback B.hom f) :=
                c.isTerminalΩ₀.hom_ext _ _
              rw [hterm]
            have nbg : nn ≫ bad = nn ≫ good := by
              rw [nb, ng]
              calc
                (k.left ≫ d) ≫ c.χ d =
                    k.left ≫ (d ≫ c.χ d) := by simp [Category.assoc]
                _ = k.left ≫ (c.χ₀ A.left ≫ c.truth) := by
                    rw [(c.isPullback d).w]
                _ = (c.χ₀ (Limits.pullback B.hom f)) ≫ c.truth := by
                    rw [← Category.assoc]
                    have ht : k.left ≫ c.χ₀ A.left =
                        c.χ₀ (Limits.pullback B.hom f) :=
                      c.isTerminalΩ₀.hom_ext _ _
                    simpa only [Category.assoc] using
                      congrArg (fun t => t ≫ c.truth) ht
            have hext : (I ◁ yOf k) ≫ c.extendAlong m bad =
                    (I ◁ yOf k) ≫ c.extendAlong m good := by
              rw [c.comp_extendAlong_pullback m mbi nn (I ◁ yOf k) sq bad]
              rw [c.comp_extendAlong_pullback m mbi nn (I ◁ yOf k) sq good]
              rw [nbg]
            dsimp [u, v]
            rw [← CategoryTheory.MonoidalClosed.curry_natural_left,
                ← CategoryTheory.MonoidalClosed.curry_natural_left]
            rw [hext]
          let toR {B : Over J}
              (k : (Over.pullback f).obj B ⟶ A) : B.left ⟶ R :=
            Limits.equalizer.lift (yOf k) (yOf_fix k)
          have toR_z {B : Over J}
              (k : (Over.pullback f).obj B ⟶ A) :
              toR k ≫ z = yOf k := by
            dsimp [toR, z, R]
            apply Limits.equalizer.lift_ι
          let toT {B : Over J}
              (k : (Over.pullback f).obj B ⟶ A) : B.left ⟶ T :=
            Limits.equalizer.lift (toR k) (by
              simp only [← Category.assoc, toR_z]
              exact yOf_good k)
          have toT_inc {B : Over J}
              (k : (Over.pullback f).obj B ⟶ A) :
              toT k ≫ inc = yOf k := by
            have hj : toT k ≫ j = toR k := by
              dsimp [toT, j, T]
              apply Limits.equalizer.lift_ι
            calc
              toT k ≫ inc = (toT k ≫ j) ≫ z := by simp only [inc, Category.assoc]
              _ = toR k ≫ z := by rw [hj]
              _ = yOf k := toR_z k
          let toD {B : Over J}
              (k : (Over.pullback f).obj B ⟶ A) : B ⟶ D :=
            Over.homMk (toT k) (by
              change toT k ≫ (inc ≫ w) = B.hom
              rw [← Category.assoc, toT_inc]
              exact yOf_w k)
          -- Conversely a code in T has a graph lying over the mono d;
          -- use the classifier pullback to obtain its unique section.
          let codeY {B : Over J} (g : B ⟶ D) : B.left ⟶ W :=
            g.left ≫ inc
          have codeY_w {B : Over J} (g : B ⟶ D) :
              codeY g ≫ w = B.hom := by
            calc
              codeY g ≫ w = g.left ≫ (inc ≫ w) := by simp only [codeY, Category.assoc]
              _ = g.left ≫ D.hom := rfl
              _ = B.hom := g.w
          have codeY_fix {B : Over J} (g : B ⟶ D) :
              codeY g ≫ q₀ = codeY g ≫ ext := by
            calc
              codeY g ≫ q₀ = g.left ≫ (inc ≫ q₀) := by simp only [codeY, Category.assoc]
              _ = g.left ≫ (inc ≫ ext) := by rw [inc_fix]
              _ = codeY g ≫ ext := by simp only [codeY, Category.assoc]
          have codeY_good {B : Over J} (g : B ⟶ D) :
              codeY g ≫ u = codeY g ≫ v := by
            calc
              codeY g ≫ u = g.left ≫ (inc ≫ u) := by simp only [codeY, Category.assoc]
              _ = g.left ≫ (inc ≫ v) := by rw [inc_good]
              _ = codeY g ≫ v := by simp only [codeY, Category.assoc]
          let codeN {B : Over J} (g : B ⟶ D) :
              Limits.pullback B.hom f ⟶ S :=
            nOf B (codeY g) (codeY_w g)
          let codeα {B : Over J} (g : B ⟶ D) :
              Limits.pullback B.hom f ⟶ I ⊗ P :=
            CategoryTheory.CartesianMonoidalCategory.lift
              (pullback.snd B.hom f) (codeN g ≫ r)
          have code_true {B : Over J} (g : B ⟶ D) :
              codeα g ≫ c.χ d = c.χ₀ (Limits.pullback B.hom f) ≫ c.truth := by
            let yy : B.left ⟶ W := codeY g
            have hy : yy ≫ w = B.hom := codeY_w g
            let nn : Limits.pullback B.hom f ⟶ S := codeN g
            let mbi : Limits.pullback B.hom f ⟶ I ⊗ B.left := mb0 B
            letI imb : Mono mbi :=
              CategoryTheory.mono_pullback_graph_tensor f B.hom
            have sq : IsPullback mbi nn (I ◁ yy) m :=
              sqOf B yy hy
            have ce : (I ◁ yy) ≫ c.extendAlong m bad =
                    (I ◁ yy) ≫ c.extendAlong m good := by
              apply CategoryTheory.MonoidalClosed.curry_injective
              -- curry moves the parameter to the outside
              rw [CategoryTheory.MonoidalClosed.curry_natural_left,
                CategoryTheory.MonoidalClosed.curry_natural_left]
              exact codeY_good g
            have nbng : nn ≫ bad = nn ≫ good := by
              calc
                nn ≫ bad = (nn ≫ m) ≫ c.extendAlong m bad := by
                  rw [Category.assoc, c.comp_extendAlong m bad]
                _ = (mbi ≫ (I ◁ yy)) ≫ c.extendAlong m bad := by
                  rw [sq.w]
                _ = mbi ≫ ((I ◁ yy) ≫ c.extendAlong m bad) := by
                  simp [Category.assoc]
                _ = mbi ≫ ((I ◁ yy) ≫ c.extendAlong m good) := by
                  rw [ce]
                _ = (nn ≫ m) ≫ c.extendAlong m good := by
                  rw [← sq.w]
                  simp [Category.assoc]
                _ = nn ≫ good := by
                  rw [Category.assoc, c.comp_extendAlong m good]
            have nsnd : nn ≫ pullback.snd w f =
                    pullback.snd B.hom f := by
              dsimp [nn, codeN, nOf]
              apply Limits.pullback.lift_snd
            have nb : nn ≫ bad = codeα g ≫ c.χ d := by
              calc
                nn ≫ bad = (nn ≫
                    CategoryTheory.CartesianMonoidalCategory.lift
                      (pullback.snd w f) r) ≫ c.χ d := by
                        simp only [bad, Category.assoc]
                _ = codeα g ≫ c.χ d := by
                  congr 1
                  rw [CategoryTheory.CartesianMonoidalCategory.comp_lift, nsnd]
            have ng : nn ≫ good =
                    c.χ₀ (Limits.pullback B.hom f) ≫ c.truth := by
              dsimp [good]
              rw [← Category.assoc]
              have term : nn ≫ c.χ₀ S =
                    c.χ₀ (Limits.pullback B.hom f) :=
                c.isTerminalΩ₀.hom_ext _ _
              rw [term]
            rw [← nb, nbng, ng]
          -- make the lift given by the universal property of the classifier
          let codeL {B : Over J} (g : B ⟶ D) :
              Limits.pullback B.hom f ⟶ A.left :=
            (c.isPullback d).lift (codeα g)
              (c.χ₀ (Limits.pullback B.hom f)) (code_true g)
          have codeL_d {B : Over J} (g : B ⟶ D) :
              codeL g ≫ d = codeα g := by
            dsimp [codeL]; exact (c.isPullback d).lift_fst _ _ _
          let fromD {B : Over J} (g : B ⟶ D) :
              (Over.pullback f).obj B ⟶ A :=
            Over.homMk (codeL g) (by
              have hh := congrArg
                (fun t => t ≫ CategoryTheory.CartesianMonoidalCategory.fst I P)
                (codeL_d g)
              change codeL g ≫ A.hom = pullback.snd B.hom f
              simpa [d, codeα, Category.assoc] using hh)
          -- equality of two encodings is detected on W by the monic inc.
          have to_from {B : Over J}
              (k : (Over.pullback f).obj B ⟶ A) :
              fromD (toD k) = k := by
            apply Over.OverMorphism.ext
            change codeL (toD k) = k.left
            apply (cancel_mono d).1
            rw [codeL_d]
            -- identify the graph of the encoded point
            have cy : codeY (toD k) = yOf k := by
              calc
                codeY (toD k) = toT k ≫ inc := rfl
                _ = yOf k := toT_inc k
            let mbi : Limits.pullback B.hom f ⟶ I ⊗ B.left := mb0 B
            letI imb : Mono mbi :=
              CategoryTheory.mono_pullback_graph_tensor f B.hom
            let nn : Limits.pullback B.hom f ⟶ S := codeN (toD k)
            have ny : nn = nOf B (yOf k) (yOf_w k) := by
              dsimp [nn, codeN]
              simp only [cy]
            have sq : IsPullback mbi nn (I ◁ yOf k) m := by
              rw [ny]; exact sqOf B (yOf k) (yOf_w k)
            have hq : mbi ≫ CategoryTheory.MonoidalClosed.uncurry
                    (yOf k ≫ q₀) = k.left ≫ e := by
              rw [yOf_q]
              dsimp [tb]
              rw [CategoryTheory.MonoidalClosed.uncurry_curry]
              exact c.comp_partialExtend A.left mbi (k.left ≫ e)
            have nr : nn ≫ r = k.left ≫ e := by
              calc
                nn ≫ r = nn ≫ m ≫ val := by simp [r]
                _ = (mbi ≫ (I ◁ yOf k)) ≫ val := by rw [sq.w]; simp [Category.assoc]
                _ = mbi ≫ CategoryTheory.MonoidalClosed.uncurry (yOf k ≫ q₀) := by
                  rw [Category.assoc]
                  simp [val, CategoryTheory.Subobject.Classifier.comp_uncurry_eq]
                _ = _ := hq
            change CategoryTheory.CartesianMonoidalCategory.lift
              (pullback.snd B.hom f) (_ ≫ r) = k.left ≫ d
            rw [nr]
            symm
            calc
              k.left ≫ d = CategoryTheory.CartesianMonoidalCategory.lift
                (k.left ≫ A.hom) (k.left ≫ e) := by
                  apply CategoryTheory.CartesianMonoidalCategory.comp_lift
              _ = _ := by rw [show k.left ≫ A.hom = pullback.snd B.hom f by simpa using k.w]
          have from_to {B : Over J} (g : B ⟶ D) :
              toD (fromD g) = g := by
            apply Over.OverMorphism.ext
            -- the inclusion of the two equalizers is monic
            apply (cancel_mono inc).1
            have yyEq : yOf (fromD g) = codeY g := by
              apply CategoryTheory.CartesianMonoidalCategory.hom_ext
              · rw [yOf_w, codeY_w]
              · rw [yOf_q]
                let yy : B.left ⟶ W := codeY g
                have hy : yy ≫ w = B.hom := codeY_w g
                let mbi : Limits.pullback B.hom f ⟶ I ⊗ B.left := mb0 B
                letI imb : Mono mbi :=
                  CategoryTheory.mono_pullback_graph_tensor f B.hom
                let nn : Limits.pullback B.hom f ⟶ S := codeN g
                have sq : IsPullback mbi nn (I ◁ yy) m :=
                  sqOf B yy hy
                have ne : nn ≫ r = codeL g ≫ e := by
                  have zz := congrArg
                    (fun t => t ≫ CategoryTheory.CartesianMonoidalCategory.snd I P)
                    (codeL_d g)
                  simpa [codeα, d, nn, Category.assoc] using zz.symm
                have hcalc : mbi ≫ CategoryTheory.MonoidalClosed.uncurry
                        (yy ≫ q₀) = nn ≫ r := by
                  calc
                    mbi ≫ CategoryTheory.MonoidalClosed.uncurry (yy ≫ q₀) =
                        (mbi ≫ (I ◁ yy)) ≫ val := by
                          rw [Category.assoc]
                          -- unfold the parameter `yy` so that the usual
                          -- naturality of uncurrying reduces this to an
                          -- associativity identity
                          simp [val, CategoryTheory.Subobject.Classifier.comp_uncurry_eq, yy, codeY]
                    _ = nn ≫ m ≫ val := by
                      rw [sq.w]
                      simp only [Category.assoc]
                    _ = nn ≫ r := by simp [r, Category.assoc]
                have hh := c.curry_partialExtend_fixed
                  (K := A.left) (I := I) (m := m) (mb := mbi)
                  (n := nn) (y := yy) sq (t := q₀)
                  (q := codeL g ≫ e) (hcalc.trans ne)
                -- use its fixed point equation and the fixed equation of g
                calc
                  tb (fromD g) =
                      CategoryTheory.MonoidalClosed.curry
                        (c.partialExtend A.left mbi (codeL g ≫ e)) := by rfl
                  _ = yy ≫ ext := by
                    simpa [ext, hval, CategoryTheory.Subobject.Classifier.partialExtend,
                      mA, r, val] using hh.symm
                  _ = yy ≫ q₀ := (codeY_fix g).symm
            calc
              (toD (fromD g)).left ≫ inc = yOf (fromD g) := toT_inc (fromD g)
              _ = codeY g := yyEq
              _ = g.left ≫ inc := rfl
          -- precomposition compatibility (the mate hom-equivalence).
          have natural {B B' : Over J} (l : B ⟶ B')
              (g : B' ⟶ D) :
              fromD (l ≫ g) = (Over.pullback f).map l ≫ fromD g := by
            have y_pre {B₀ B₁ : Over J} (l₀ : B₀ ⟶ B₁)
                (k₁ : (Over.pullback f).obj B₁ ⟶ A) :
                yOf ((Over.pullback f).map l₀ ≫ k₁) = l₀.left ≫ yOf k₁ := by
              apply CategoryTheory.CartesianMonoidalCategory.hom_ext
              · rw [yOf_w]
                -- first coordinate says that `l₀` lies over `J`
                rw [Category.assoc, yOf_w]
                exact (l₀.w).symm
              · rw [yOf_q]
                rw [Category.assoc, yOf_q]
                -- naturality of zero-filled extension for the graph square
                let mb : Limits.pullback B₀.hom f ⟶ I ⊗ B₀.left := mb0 B₀
                letI imbb : Mono mb :=
                  CategoryTheory.mono_pullback_graph_tensor f B₀.hom
                let mb' : Limits.pullback B₁.hom f ⟶ I ⊗ B₁.left := mb0 B₁
                letI imbp : Mono mb' :=
                  CategoryTheory.mono_pullback_graph_tensor f B₁.hom
                let n : Limits.pullback B₀.hom f ⟶ Limits.pullback B₁.hom f :=
                  ((Over.pullback f).map l₀).left
                have hn : n = pullback.lift
                    (pullback.fst B₀.hom f ≫ l₀.left)
                    (pullback.snd B₀.hom f)
                    (by simpa [Category.assoc] using
                      (pullback.condition : pullback.fst B₀.hom f ≫ B₀.hom = _)) := by
                  dsimp [n, CategoryTheory.Over.pullback]
                have sqb : IsPullback mb n (I ◁ l₀.left) mb' := by
                  rw [hn]
                  dsimp [mb, mb', mb0]
                  exact CategoryTheory.isPullback_pullback_graph_tensor
                    f B₁.hom l₀.left B₀.hom l₀.w
                have hextb := c.partialExtend_pullback A.left mb' mb n
                  (I ◁ l₀.left) sqb (k₁.left ≫ e)
                dsimp [tb]
                rw [← CategoryTheory.MonoidalClosed.curry_natural_left]
                apply congrArg (fun t => CategoryTheory.MonoidalClosed.curry t)
                simpa [mb, mb', n, Category.assoc] using hextb.symm
            let k₂ : (Over.pullback f).obj B ⟶ A :=
              (Over.pullback f).map l ≫ fromD g
            have hd2 : toD k₂ = l ≫ g := by
              apply Over.OverMorphism.ext
              apply (cancel_mono inc).1
              calc
                (toD k₂).left ≫ inc = yOf k₂ := toT_inc k₂
                _ = l.left ≫ yOf (fromD g) := y_pre l (fromD g)
                _ = l.left ≫ (toT (fromD g) ≫ inc) := by
                  rw [toT_inc]
                _ = l.left ≫ (g.left ≫ inc) := by
                  have hleft := congrArg (fun t : (B' ⟶ D) => t.left)
                    (from_to g)
                  change toT (fromD g) = g.left at hleft
                  rw [hleft]
                _ = (l ≫ g).left ≫ inc := by
                  simp [Category.assoc]
            calc
              fromD (l ≫ g) = fromD (toD k₂) := by rw [hd2]
              _ = k₂ := to_from k₂
              _ = _ := rfl
          exact
            { homEquiv :=
                { toFun := fun g => fromD g
                  invFun := fun k => toD k
                  left_inv := fun g => from_to g
                  right_inv := fun k => to_from k }
              homEquiv_comp := by
                intro B B' l g
                -- the presheaf acts by precomposition with the pullback map
                exact natural l g }

        exact ⟨CategoryTheory.monoidalClosedOver_of_pullback_left hpb X⟩
  refine ⟨cmX, hclosedX, ?_⟩
  exact CategoryTheory.hasSubobjectClassifierOver X
/-ResultProofEnd-/
/-ResultEnd-/
-- END INLINED FILE: Main.lean

end Submission
