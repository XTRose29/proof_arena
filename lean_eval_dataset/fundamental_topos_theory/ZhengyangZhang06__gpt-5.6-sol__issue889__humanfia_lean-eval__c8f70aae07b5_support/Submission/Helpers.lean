import ChallengeDeps

open CategoryTheory CategoryTheory.Limits

namespace Submission.Helpers

noncomputable section

variable {C : Type*} [Category C] [HasFiniteLimits C]

def omegaOver (c : Subobject.Classifier C) (X : C) : Over X :=
  Over.mk (prod.snd : c.Ω ⨯ X ⟶ X)

@[simp] lemma omegaOver_left (c : Subobject.Classifier C) (X : C) :
    (omegaOver c X).left = (c.Ω ⨯ X) := rfl

@[simp] lemma omegaOver_hom (c : Subobject.Classifier C) (X : C) :
    (omegaOver c X).hom = (prod.snd : c.Ω ⨯ X ⟶ X) := rfl

def truthOver (c : Subobject.Classifier C) (X : C) :
    Over.mk (𝟙 X) ⟶ omegaOver c X :=
  Over.homMk (prod.lift (c.χ₀ X ≫ c.truth) (𝟙 X)) (prod.lift_snd _ _)

@[simp] lemma truthOver_left (c : Subobject.Classifier C) (X : C) :
    (truthOver c X).left = prod.lift (c.χ₀ X ≫ c.truth) (𝟙 X) := rfl

def chiOver (c : Subobject.Classifier C) {X : C} {U A : Over X}
    (m : U ⟶ A) [Mono m] : A ⟶ omegaOver c X := by
  letI : Mono m.left := Over.mono_left_of_mono m
  exact Over.homMk (prod.lift (c.χ m.left) A.hom) (prod.lift_snd _ _)

@[simp] lemma chiOver_left (c : Subobject.Classifier C) {X : C} {U A : Over X}
    (m : U ⟶ A) [Mono m] :
    (chiOver c m).left = prod.lift (c.χ m.left) A.hom := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
def classifierOver [HasSubobjectClassifier C] (X : C) : Subobject.Classifier (Over X) := by
  let c : Subobject.Classifier C := HasSubobjectClassifier.exists_classifier.some
  refine Subobject.Classifier.mkOfTerminalΩ₀
    (Over.mk (𝟙 X)) Over.mkIdTerminal
    (omegaOver c X) (truthOver c X) (chiOver c) ?_ ?_
  · intro U A m _
    letI : Mono m.left := Over.mono_left_of_mono m
    apply IsPullback.mk'
    · apply Over.OverMorphism.ext
      apply prod.hom_ext
      · calc
          ((m ≫ chiOver c m).left) ≫ prod.fst = m.left ≫ c.χ m.left := by
            rw [Over.comp_left, chiOver_left, Category.assoc, prod.lift_fst]
          _ = c.χ₀ U.left ≫ c.truth := (c.isPullback m.left).w
          _ = U.hom ≫ c.χ₀ X ≫ c.truth := by
            rw [← Category.assoc]
            congr 1
            exact c.isTerminalΩ₀.hom_ext _ _
          _ = ((Over.mkIdTerminal.from U ≫ truthOver c X).left) ≫ prod.fst := by
            rw [Over.comp_left, Over.mkIdTerminal_from_left, truthOver_left,
              Category.assoc, prod.lift_fst]
      · calc
          ((m ≫ chiOver c m).left) ≫ prod.snd = m.left ≫ A.hom := by
            rw [Over.comp_left, chiOver_left, Category.assoc, prod.lift_snd]
          _ = U.hom := m.w
          _ = U.hom ≫ 𝟙 X := by rw [Category.comp_id]
          _ = ((Over.mkIdTerminal.from U ≫ truthOver c X).left) ≫ prod.snd := by
            rw [Over.comp_left, Over.mkIdTerminal_from_left, truthOver_left,
              Category.assoc, prod.lift_snd]
    · intro T f g hfg _
      apply Over.OverMorphism.ext
      exact (cancel_mono m.left).1 (congrArg Over.Hom.left hfg)
    · intro T a b hab
      have habLeft := congrArg Over.Hom.left hab
      have hfst := congrArg (fun k => k ≫ prod.fst) habLeft
      have hb : b.left ≫ c.χ₀ X = c.χ₀ T.left := c.isTerminalΩ₀.hom_ext _ _
      have hchi : a.left ≫ c.χ m.left = c.χ₀ T.left ≫ c.truth := by
        have hchi' : a.left ≫ c.χ m.left = b.left ≫ c.χ₀ X ≫ c.truth := by
          simpa only [Over.comp_left, chiOver_left, truthOver_left,
            Category.assoc, prod.lift_fst] using hfst
        rw [← Category.assoc, hb] at hchi'
        exact hchi'
      let pb := c.isPullback m.left
      let lleft := pb.lift a.left (c.χ₀ T.left) hchi
      let l : T ⟶ U := Over.homMk lleft (by
        rw [← m.w, ← Category.assoc, pb.lift_fst, a.w])
      refine ⟨l, ?_, ?_⟩
      · apply Over.OverMorphism.ext
        exact pb.lift_fst a.left (c.χ₀ T.left) hchi
      · exact Over.mkIdTerminal.hom_ext _ _
  · intro U A m _ chi' hchi'
    apply Over.OverMorphism.ext
    apply prod.hom_ext
    · letI : Mono m.left := Over.mono_left_of_mono m
      have hfirst : IsPullback m.left (c.χ₀ U.left) (chi'.left ≫ prod.fst) c.truth := by
        apply IsPullback.mk'
        · have hw := congrArg Over.Hom.left hchi'.w
          have hwfst := congrArg (fun k => k ≫ prod.fst) hw
          have hu : U.hom ≫ c.χ₀ X = c.χ₀ U.left := c.isTerminalΩ₀.hom_ext _ _
          calc
            m.left ≫ (chi'.left ≫ prod.fst) = (m.left ≫ chi'.left) ≫ prod.fst := by
              rw [Category.assoc]
            _ = ((Over.mkIdTerminal.from U).left ≫ (truthOver c X).left) ≫ prod.fst := by
              exact hwfst
            _ = U.hom ≫ c.χ₀ X ≫ c.truth := by
              rw [Over.mkIdTerminal_from_left, truthOver_left, Category.assoc, prod.lift_fst]
            _ = c.χ₀ U.left ≫ c.truth := by rw [← Category.assoc, hu]
        · intro T f g hfg _
          exact (cancel_mono m.left).1 hfg
        · intro T a b hab
          let T' : Over X := Over.mk (a ≫ A.hom)
          let aa : T' ⟶ A := Over.homMk a
          let bb : T' ⟶ Over.mk (𝟙 X) := Over.mkIdTerminal.from T'
          have hb : b = a ≫ A.hom ≫ c.χ₀ X := c.isTerminalΩ₀.hom_ext _ _
          have hsquare : aa ≫ chi' = bb ≫ truthOver c X := by
            apply Over.OverMorphism.ext
            simp only [Over.comp_left, aa, bb, Over.homMk_left, Over.mkIdTerminal_from_left]
            change a ≫ chi'.left = (a ≫ A.hom) ≫ (truthOver c X).left
            apply prod.hom_ext
            · rw [Category.assoc]
              calc
                a ≫ chi'.left ≫ prod.fst = b ≫ c.truth := hab
                _ = (a ≫ A.hom ≫ c.χ₀ X) ≫ c.truth := by rw [hb]
                _ = ((a ≫ A.hom) ≫ (truthOver c X).left) ≫ prod.fst := by
                  simp only [truthOver_left, Category.assoc, prod.lift_fst]
            · have hchiw : chi'.left ≫ prod.snd = A.hom := chi'.w
              rw [Category.assoc, hchiw, truthOver_left, Category.assoc,
                prod.lift_snd, Category.comp_id]
          let l := hchi'.lift aa bb hsquare
          refine ⟨l.left, ?_, ?_⟩
          · exact congrArg Over.Hom.left (hchi'.lift_fst aa bb hsquare)
          · exact c.isTerminalΩ₀.hom_ext _ _
      have huniq := c.uniq m.left hfirst
      simpa only [chiOver_left, prod.lift_fst] using huniq
    · have hchiw : chi'.left ≫ prod.snd = A.hom := chi'.w
      simpa only [chiOver_left, prod.lift_snd] using hchiw

end

end Submission.Helpers
