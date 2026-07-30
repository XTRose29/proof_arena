import Mathlib

noncomputable section

open scoped unitInterval Topology
open Topology.Homotopy

namespace Submission.Helpers

variable {N X Y Z : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {x : X} {y : Y} {z : Z}

/-- Postcomposition of a generalized loop by a pointed continuous map. -/
def genLoopMap (f : C(X, Y)) (hf : f x = y) (p : GenLoop N X x) :
    GenLoop N Y y :=
  ⟨f.comp p.1, fun t ht => by rw [ContinuousMap.comp_apply, p.property t ht, hf]⟩

@[simp]
lemma genLoopMap_apply (f : C(X, Y)) (hf : f x = y)
    (p : GenLoop N X x) (t : N → I) :
    genLoopMap f hf p t = f (p t) :=
  rfl

@[simp]
lemma genLoopMap_const (f : C(X, Y)) (hf : f x = y) :
    genLoopMap (N := N) f hf GenLoop.const = GenLoop.const := by
  ext t
  exact hf

lemma genLoopMap_homotopic (f : C(X, Y)) (hf : f x = y)
    {p q : GenLoop N X x} (hpq : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (genLoopMap f hf p) (genLoopMap f hf q) := by
  exact hpq.comp_continuousMap f

/-- The map on generalized-loop homotopy classes induced by a pointed
continuous map. -/
def homotopyGroupMap (f : C(X, Y)) (hf : f x = y) :
    HomotopyGroup N X x → HomotopyGroup N Y y :=
  Quotient.map (genLoopMap f hf) (by
    intro p q hpq
    change GenLoop.Homotopic p q at hpq
    change GenLoop.Homotopic (genLoopMap f hf p) (genLoopMap f hf q)
    exact genLoopMap_homotopic f hf hpq)

@[simp]
lemma homotopyGroupMap_mk (f : C(X, Y)) (hf : f x = y)
    (p : GenLoop N X x) :
    homotopyGroupMap f hf (Quotient.mk' p) =
      Quotient.mk' (genLoopMap f hf p) :=
  rfl

@[simp]
lemma genLoopMap_id (p : GenLoop N X x) :
    genLoopMap (ContinuousMap.id X) rfl p = p := by
  ext t
  rfl

@[simp]
lemma genLoopMap_id_of_eq
    (h : (ContinuousMap.id X) x = x) (p : GenLoop N X x) :
    genLoopMap (ContinuousMap.id X) h p = p := by
  ext t
  rfl

@[simp]
lemma homotopyGroupMap_id :
    homotopyGroupMap (N := N) (x := x) (ContinuousMap.id X) rfl = id := by
  funext a
  induction a using Quotient.inductionOn with
  | _ p =>
    exact congrArg Quotient.mk' (genLoopMap_id p)

lemma genLoopMap_comp (g : C(Y, Z)) (hg : g y = z)
    (f : C(X, Y)) (hf : f x = y) (p : GenLoop N X x) :
    genLoopMap g hg (genLoopMap f hf p) =
      genLoopMap (g.comp f) (by rw [ContinuousMap.comp_apply, hf, hg]) p := by
  ext t
  rfl

lemma homotopyGroupMap_comp (g : C(Y, Z)) (hg : g y = z)
    (f : C(X, Y)) (hf : f x = y) :
    homotopyGroupMap (N := N) g hg ∘ homotopyGroupMap f hf =
      homotopyGroupMap (g.comp f)
        (by rw [ContinuousMap.comp_apply, hf, hg]) := by
  funext a
  induction a using Quotient.inductionOn with
  | _ p =>
    exact congrArg Quotient.mk' (genLoopMap_comp g hg f hf p)

/-- Pointed-homotopic maps induce homotopic postcompositions of generalized
loops. -/
lemma genLoopMap_homotopic_of_homotopicRel
    (f g : C(X, Y)) (hf : f x = y) (hg : g x = y)
    (H : f.HomotopicRel g {x}) (p : GenLoop N X x) :
    GenLoop.Homotopic (genLoopMap f hf p) (genLoopMap g hg p) := by
  rcases H with ⟨H⟩
  refine ⟨{ toHomotopy := H.toHomotopy.compContinuousMap p.1,
             prop' := ?_ }⟩
  intro t s hs
  change H (t, p s) = f (p s)
  exact H.eq_fst t (by simpa using p.property s hs)

/-- Pointed-homotopic maps induce the same function on higher homotopy
classes. -/
lemma homotopyGroupMap_eq_of_homotopicRel
    (f g : C(X, Y)) (hf : f x = y) (hg : g x = y)
    (H : f.HomotopicRel g {x}) :
    homotopyGroupMap (N := N) f hf =
      homotopyGroupMap g hg := by
  funext a
  induction a using Quotient.inductionOn with
  | _ p =>
    apply Quotient.sound
    exact genLoopMap_homotopic_of_homotopicRel f g hf hg H p

variable [DecidableEq N]

lemma genLoopMap_transAt (f : C(X, Y)) (hf : f x = y)
    (i : N) (p q : GenLoop N X x) :
    genLoopMap f hf (GenLoop.transAt i p q) =
      GenLoop.transAt i (genLoopMap f hf p) (genLoopMap f hf q) := by
  ext t
  change f (GenLoop.transAt i p q t) =
    GenLoop.transAt i (genLoopMap f hf p) (genLoopMap f hf q) t
  simp only [GenLoop.transAt, GenLoop.coe_copy]
  split_ifs <;> rfl

lemma homotopyGroupMap_mul_mk [Nonempty N]
    (f : C(X, Y)) (hf : f x = y) (p q : GenLoop N X x) :
    homotopyGroupMap f hf
        (((· * ·) : HomotopyGroup N X x → HomotopyGroup N X x →
            HomotopyGroup N X x) (Quotient.mk' p) (Quotient.mk' q)) =
      ((· * ·) : HomotopyGroup N Y y → HomotopyGroup N Y y →
          HomotopyGroup N Y y)
        (homotopyGroupMap f hf (Quotient.mk' p))
        (homotopyGroupMap f hf (Quotient.mk' q)) := by
  refine (congrArg (homotopyGroupMap f hf)
    (HomotopyGroup.mul_spec
      (X := X) (i := Classical.arbitrary N)
      (p := p) (q := q))).trans ?_
  change
    (Quotient.mk'
        (genLoopMap f hf
          (GenLoop.transAt (Classical.arbitrary N) q p)) :
      HomotopyGroup N Y y) =
      ((· * ·) : HomotopyGroup N Y y → HomotopyGroup N Y y →
        HomotopyGroup N Y y)
        (Quotient.mk' (genLoopMap f hf p))
        (Quotient.mk' (genLoopMap f hf q))
  rw [genLoopMap_transAt]
  exact (HomotopyGroup.mul_spec
    (X := Y) (i := Classical.arbitrary N)
    (p := genLoopMap f hf p) (q := genLoopMap f hf q)).symm

/-- The homomorphism on positive-dimensional homotopy groups induced by a
pointed continuous map. -/
def homotopyGroupMapMulHom [Nonempty N]
    (f : C(X, Y)) (hf : f x = y) :
    HomotopyGroup N X x →* HomotopyGroup N Y y where
  toFun := homotopyGroupMap f hf
  map_one' := by
    change
      homotopyGroupMap f hf (Quotient.mk' (@GenLoop.const N X _ x)) =
        Quotient.mk' (@GenLoop.const N Y _ y)
    exact congrArg Quotient.mk' (genLoopMap_const f hf)
  map_mul' a b := by
    exact Quotient.inductionOn₂ a b
      (fun p q => homotopyGroupMap_mul_mk f hf p q)

/-- A homeomorphism induces an isomorphism on every positive-dimensional
homotopy group. -/
def homotopyGroupMulEquivOfHomeomorph [Nonempty N]
    (e : X ≃ₜ Y) (x : X) :
    HomotopyGroup N X x ≃* HomotopyGroup N Y (e x) where
  toFun :=
    homotopyGroupMap
      ⟨e, e.continuous⟩ rfl
  invFun :=
    homotopyGroupMap
      ⟨e.symm, e.symm.continuous⟩ (e.symm_apply_apply x)
  left_inv a := by
    induction a using Quotient.inductionOn with
    | _ p =>
      apply congrArg Quotient.mk'
      ext t
      exact e.symm_apply_apply (p t)
  right_inv a := by
    induction a using Quotient.inductionOn with
    | _ p =>
      apply congrArg Quotient.mk'
      ext t
      exact e.apply_symm_apply (p t)
  map_mul' a b :=
    (homotopyGroupMapMulHom
      (N := N) ⟨e, e.continuous⟩ rfl).map_mul a b

/-- A homotopy equivalence that preserves chosen basepoints and whose inverse
laws are relative to those basepoints. -/
structure PointedHomotopyEquiv
    (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) where
  toFun : C(X, Y)
  invFun : C(Y, X)
  map_base : toFun x = y
  inv_base : invFun y = x
  left_inv :
    (invFun.comp toFun).HomotopicRel (ContinuousMap.id X) {x}
  right_inv :
    (toFun.comp invFun).HomotopicRel (ContinuousMap.id Y) {y}

/-- A pointed homotopy equivalence induces an isomorphism on every
positive-dimensional homotopy group. -/
def PointedHomotopyEquiv.homotopyGroupMulEquiv [Nonempty N]
    (e : PointedHomotopyEquiv X Y x y) :
    HomotopyGroup N X x ≃* HomotopyGroup N Y y where
  toFun := homotopyGroupMap e.toFun e.map_base
  invFun := homotopyGroupMap e.invFun e.inv_base
  left_inv a := by
    induction a using Quotient.inductionOn with
    | _ p =>
      apply Quotient.sound
      rw [genLoopMap_comp]
      have H := genLoopMap_homotopic_of_homotopicRel
        (N := N) (x := x) (y := x)
        (e.invFun.comp e.toFun) (ContinuousMap.id X)
        (by rw [ContinuousMap.comp_apply, e.map_base, e.inv_base])
        rfl e.left_inv p
      change GenLoop.Homotopic _ p
      simpa only [genLoopMap_id_of_eq] using H
  right_inv a := by
    induction a using Quotient.inductionOn with
    | _ p =>
      apply Quotient.sound
      rw [genLoopMap_comp]
      have H := genLoopMap_homotopic_of_homotopicRel
        (N := N) (x := y) (y := y)
        (e.toFun.comp e.invFun) (ContinuousMap.id Y)
        (by rw [ContinuousMap.comp_apply, e.inv_base, e.map_base])
        rfl e.right_inv p
      change GenLoop.Homotopic _ p
      simpa only [genLoopMap_id_of_eq] using H
  map_mul' a b :=
    (homotopyGroupMapMulHom
      (N := N) e.toFun e.map_base).map_mul a b

end Submission.Helpers
