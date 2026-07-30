import Submission.OddOrder.MathlibSupport.CentralCommutatorPowers
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
A commutator pairing for a quotient in which the image of the derived subgroup
is central.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped commutatorElement IsMulCommutative

universe u

private theorem classTwoQuotient_commutator_le_center
    {P : Type u} [Group P] (Q : Subgroup P) [Q.Normal]
    (hcentral : (_root_.commutator P).map (QuotientGroup.mk' Q) ≤
      Subgroup.center (P ⧸ Q)) :
    _root_.commutator (P ⧸ Q) ≤ Subgroup.center (P ⧸ Q) := by
  let q : P →* P ⧸ Q := QuotientGroup.mk' Q
  have hmap : (_root_.commutator P).map q = _root_.commutator (P ⧸ Q) := by
    calc
      (_root_.commutator P).map q = ⁅q.range, q.range⁆ :=
        map_commutator_eq P q
      _ = ⁅(⊤ : Subgroup (P ⧸ Q)), ⊤⁆ := by
        rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective Q)]
      _ = _root_.commutator (P ⧸ Q) := rfl
  rw [← hmap]
  exact hcentral

private def classTwoQuotientCommutatorValue
    {P : Type u} [Group P] (Q : Subgroup P) [Q.Normal] (x y : P) :
    (_root_.commutator P).map (QuotientGroup.mk' Q) :=
  ⟨QuotientGroup.mk' Q ⁅x, y⁆,
    ⟨⁅x, y⁆, Subgroup.commutator_mem_commutator trivial trivial, rfl⟩⟩

private theorem classTwoQuotientCommutatorValue_mul_left
    {P : Type u} [Group P] (Q : Subgroup P) [Q.Normal]
    (hcentral : (_root_.commutator P).map (QuotientGroup.mk' Q) ≤
      Subgroup.center (P ⧸ Q)) (a b c : P) :
    classTwoQuotientCommutatorValue Q (a * b) c =
      classTwoQuotientCommutatorValue Q a c *
        classTwoQuotientCommutatorValue Q b c := by
  apply Subtype.ext
  change QuotientGroup.mk' Q ⁅a * b, c⁆ =
    QuotientGroup.mk' Q ⁅a, c⁆ * QuotientGroup.mk' Q ⁅b, c⁆
  simpa only [map_mul, map_commutatorElement] using
    commutatorElement_mul_left_of_commutator_le
      (classTwoQuotient_commutator_le_center Q hcentral)
      (QuotientGroup.mk' Q a) (QuotientGroup.mk' Q b)
      (QuotientGroup.mk' Q c)

private theorem classTwoQuotientCommutatorValue_mul_right
    {P : Type u} [Group P] (Q : Subgroup P) [Q.Normal]
    (hcentral : (_root_.commutator P).map (QuotientGroup.mk' Q) ≤
      Subgroup.center (P ⧸ Q)) (a b c : P) :
    classTwoQuotientCommutatorValue Q a (b * c) =
      classTwoQuotientCommutatorValue Q a b *
        classTwoQuotientCommutatorValue Q a c := by
  apply Subtype.ext
  change QuotientGroup.mk' Q ⁅a, b * c⁆ =
    QuotientGroup.mk' Q ⁅a, b⁆ * QuotientGroup.mk' Q ⁅a, c⁆
  simpa only [map_mul, map_commutatorElement] using
    commutatorElement_mul_right_of_commutator_le
      (classTwoQuotient_commutator_le_center Q hcentral)
      (QuotientGroup.mk' Q a) (QuotientGroup.mk' Q b)
      (QuotientGroup.mk' Q c)

private def classTwoQuotientCommutatorRightHom
    {P : Type u} [Group P] (Q : Subgroup P) [Q.Normal]
    (hcentral : (_root_.commutator P).map (QuotientGroup.mk' Q) ≤
      Subgroup.center (P ⧸ Q)) (x : P) :
    P →* ((_root_.commutator P).map (QuotientGroup.mk' Q)) where
  toFun := classTwoQuotientCommutatorValue Q x
  map_one' := by
    apply Subtype.ext
    simp [classTwoQuotientCommutatorValue]
  map_mul' := classTwoQuotientCommutatorValue_mul_right Q hcentral x

private theorem classTwoQuotient_commutator_le_rightKernel
    {P : Type u} [Group P] (Q : Subgroup P) [Q.Normal]
    (hcentral : (_root_.commutator P).map (QuotientGroup.mk' Q) ≤
      Subgroup.center (P ⧸ Q)) (x : P) :
    _root_.commutator P ≤
      (classTwoQuotientCommutatorRightHom Q hcentral x).ker := by
  intro d hd
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  change QuotientGroup.mk' Q ⁅x, d⁆ = 1
  rw [map_commutatorElement]
  apply commutatorElement_eq_one_iff_commute.mpr
  exact Subgroup.mem_center_iff.mp
    (hcentral ⟨d, hd, rfl⟩) (QuotientGroup.mk' Q x)

private def classTwoQuotientCommutatorRightQuotientHom
    {P : Type u} [Group P] (Q : Subgroup P) [Q.Normal]
    (hcentral : (_root_.commutator P).map (QuotientGroup.mk' Q) ≤
      Subgroup.center (P ⧸ Q)) (x : P) :
    (P ⧸ _root_.commutator P) →*
      ((_root_.commutator P).map (QuotientGroup.mk' Q)) :=
  QuotientGroup.lift (_root_.commutator P)
    (classTwoQuotientCommutatorRightHom Q hcentral x)
    (classTwoQuotient_commutator_le_rightKernel Q hcentral x)

private theorem classTwoQuotientRange_isMulCommutative
    {P : Type u} [Group P] (Q : Subgroup P) [Q.Normal]
    (hcentral : (_root_.commutator P).map (QuotientGroup.mk' Q) ≤
      Subgroup.center (P ⧸ Q)) :
    IsMulCommutative
      ((_root_.commutator P).map (QuotientGroup.mk' Q)) :=
  ⟨⟨fun a b ↦ Subtype.ext
    ((Subgroup.mem_center_iff.mp (hcentral a.property) b).symm)⟩⟩

private def classTwoQuotientCommutatorLeftHom
    {P : Type u} [Group P] (Q : Subgroup P) [Q.Normal]
    (hcentral : (_root_.commutator P).map (QuotientGroup.mk' Q) ≤
      Subgroup.center (P ⧸ Q)) :
    letI : IsMulCommutative
        ((_root_.commutator P).map (QuotientGroup.mk' Q)) :=
      classTwoQuotientRange_isMulCommutative Q hcentral
    P →* ((P ⧸ _root_.commutator P) →*
      ((_root_.commutator P).map (QuotientGroup.mk' Q))) := by
  letI : IsMulCommutative
      ((_root_.commutator P).map (QuotientGroup.mk' Q)) :=
    classTwoQuotientRange_isMulCommutative Q hcentral
  exact
    { toFun := classTwoQuotientCommutatorRightQuotientHom Q hcentral
      map_one' := by
        apply QuotientGroup.monoidHom_ext
        ext y
        change QuotientGroup.mk' Q ⁅1, y⁆ = 1
        simp
      map_mul' := by
        intro a b
        apply QuotientGroup.monoidHom_ext
        ext y
        change QuotientGroup.mk' Q ⁅a * b, y⁆ =
          QuotientGroup.mk' Q ⁅a, y⁆ * QuotientGroup.mk' Q ⁅b, y⁆
        exact congrArg Subtype.val
          (classTwoQuotientCommutatorValue_mul_left Q hcentral a b y) }

private theorem classTwoQuotient_commutator_le_leftKernel
    {P : Type u} [Group P] (Q : Subgroup P) [Q.Normal]
    (hcentral : (_root_.commutator P).map (QuotientGroup.mk' Q) ≤
      Subgroup.center (P ⧸ Q)) :
    letI : IsMulCommutative
        ((_root_.commutator P).map (QuotientGroup.mk' Q)) :=
      classTwoQuotientRange_isMulCommutative Q hcentral
    _root_.commutator P ≤
      (classTwoQuotientCommutatorLeftHom Q hcentral).ker := by
  letI : IsMulCommutative
      ((_root_.commutator P).map (QuotientGroup.mk' Q)) :=
    classTwoQuotientRange_isMulCommutative Q hcentral
  intro d hd
  rw [MonoidHom.mem_ker]
  apply QuotientGroup.monoidHom_ext
  ext y
  change QuotientGroup.mk' Q ⁅d, y⁆ = 1
  rw [map_commutatorElement]
  apply commutatorElement_eq_one_iff_commute.mpr
  exact (Subgroup.mem_center_iff.mp
    (hcentral ⟨d, hd, rfl⟩) (QuotientGroup.mk' Q y)).symm

/-- The derived-subgroup-valued commutator pairing on the abelianization of a
group modulo a subgroup for which the image of the derived subgroup is
central. -/
def classTwoQuotientCommutatorPairing
    {P : Type u} [Group P] (Q : Subgroup P) [Q.Normal]
    (hQder : Q ≤ _root_.commutator P)
    (hcentral : (_root_.commutator P).map (QuotientGroup.mk' Q) ≤
      Subgroup.center (P ⧸ Q)) :
    letI : IsMulCommutative
        ((_root_.commutator P).map (QuotientGroup.mk' Q)) :=
      classTwoQuotientRange_isMulCommutative Q hcentral
    (P ⧸ _root_.commutator P) →*
      ((P ⧸ _root_.commutator P) →*
        ((_root_.commutator P).map (QuotientGroup.mk' Q))) := by
  letI : IsMulCommutative
      ((_root_.commutator P).map (QuotientGroup.mk' Q)) :=
    classTwoQuotientRange_isMulCommutative Q hcentral
  let _hker : (QuotientGroup.mk' Q).ker ≤ _root_.commutator P := by
    simpa only [QuotientGroup.ker_mk'] using hQder
  exact QuotientGroup.lift (_root_.commutator P)
    (classTwoQuotientCommutatorLeftHom Q hcentral)
    (classTwoQuotient_commutator_le_leftKernel Q hcentral)

@[simp] theorem classTwoQuotientCommutatorPairing_mk_mk
    {P : Type u} [Group P] (Q : Subgroup P) [Q.Normal]
    (hQder : Q ≤ _root_.commutator P)
    (hcentral : (_root_.commutator P).map (QuotientGroup.mk' Q) ≤
      Subgroup.center (P ⧸ Q)) (x y : P) :
    (((classTwoQuotientCommutatorPairing Q hQder hcentral
      (QuotientGroup.mk' (_root_.commutator P) x)
      (QuotientGroup.mk' (_root_.commutator P) y) :
        (_root_.commutator P).map (QuotientGroup.mk' Q)) : P ⧸ Q)) =
      QuotientGroup.mk' Q ⁅x, y⁆ := by
  rfl

end Submission.OddOrder.MathlibSupport
