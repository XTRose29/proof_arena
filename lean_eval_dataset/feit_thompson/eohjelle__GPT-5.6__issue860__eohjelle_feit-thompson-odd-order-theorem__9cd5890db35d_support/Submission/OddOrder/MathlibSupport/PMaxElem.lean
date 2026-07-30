import Submission.OddOrder.MathlibSupport.ElementaryAbelian
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
Maximal elementary-abelian `p`-subgroups.

This is the mathlib-shaped support for MathComp's sets `'E_p(A)` and
`'E*_p(A)`, together with `pmaxElemP` and `pmaxElem_LdivP` from
`solvable/abelian.v`.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

/-- `E` is an elementary-abelian `p`-subgroup contained in `A`. -/
def IsPElementaryIn (p : ℕ) (A E : Subgroup G) : Prop :=
  E ≤ A ∧ IsElementaryAbelianGroup p E

/-- `E` is inclusion-maximal among the elementary-abelian `p`-subgroups of
`A`.  This is MathComp's membership predicate `E \in 'E*_p(A)`. -/
def IsPMaxElem (p : ℕ) (A E : Subgroup G) : Prop :=
  IsPElementaryIn p A E ∧
    ∀ F : Subgroup G, IsPElementaryIn p A F → E ≤ F → F = E

/-- The elements of `A` that centralize `E` and whose `p`th power is one.
This is the set denoted `'Ldiv_p('C_A(E))` in MathComp. -/
def pTorsionCentralizerWithin (p : ℕ) (A E : Subgroup G) : Set G :=
  {x : G | x ∈ A ∧ x ∈ Subgroup.centralizer (E : Set G) ∧ x ^ p = 1}

namespace IsPMaxElem

variable {p : ℕ} {A B E : Subgroup G}

theorem isPElementaryIn (hE : IsPMaxElem p A E) :
    IsPElementaryIn p A E :=
  hE.1

theorem le (hE : IsPMaxElem p A E) : E ≤ A :=
  hE.1.1

theorem elementary (hE : IsPMaxElem p A E) :
    IsElementaryAbelianGroup p E :=
  hE.1.2

/-- A maximal elementary-abelian subgroup of `B` that lies in `A ≤ B` is
already maximal in `A`.  This is the predicate form of `pmaxElemS`. -/
theorem of_le (hE : IsPMaxElem p B E) (hAB : A ≤ B) (hEA : E ≤ A) :
    IsPMaxElem p A E := by
  refine ⟨⟨hEA, hE.elementary⟩, ?_⟩
  intro F hF hEF
  exact hE.2 F ⟨hF.1.trans hAB, hF.2⟩ hEF

end IsPMaxElem

/-- `pmaxElem_LdivP`: a subgroup is maximal elementary abelian exactly when
it consists of all `p`-torsion elements in its centralizer inside the
ambient subgroup.  The MathComp theorem assumes `p` prime; with the
pointwise `IsPGroup` definition used here, the same proof works for every
`p`. -/
theorem isPMaxElem_iff_pTorsionCentralizerWithin
    {p : ℕ} {A E : Subgroup G} :
    IsPMaxElem p A E ↔
      pTorsionCentralizerWithin p A E = (E : Set G) := by
  constructor
  · intro hE
    letI : IsMulCommutative E := hE.elementary.commutative
    apply Set.Subset.antisymm
    · intro x hx
      let H : Subgroup G := Subgroup.zpowers x ⊔ E
      have hxCent : x ∈ Subgroup.centralizer (E : Set G) := hx.2.1
      have hzpCent : Subgroup.zpowers x ≤
          Subgroup.centralizer (E : Set G) :=
        Subgroup.zpowers_le.mpr hxCent
      have hzpNorm : Subgroup.zpowers x ≤
          Subgroup.normalizer (E : Set G) :=
        hzpCent.trans (Subgroup.centralizer_le_normalizer (E : Set G))
      have hHclosure :
          H = Subgroup.closure (({x} : Set G) ∪ (E : Set G)) := by
        dsimp [H]
        apply le_antisymm
        · apply sup_le
          · apply Subgroup.zpowers_le.mpr
            exact Subgroup.subset_closure (Or.inl rfl)
          · intro e he
            exact Subgroup.subset_closure (Or.inr he)
        · rw [Subgroup.closure_le]
          intro z hz
          rcases hz with hz | hz
          · subst z
            exact (show Subgroup.zpowers x ≤ Subgroup.zpowers x ⊔ E from
              le_sup_left) (Subgroup.mem_zpowers x)
          · exact (show E ≤ Subgroup.zpowers x ⊔ E from le_sup_right) hz
      letI : IsMulCommutative H := by
        rw [hHclosure]
        apply Subgroup.isMulCommutative_closure
        intro a ha b hb
        simp only [Set.mem_union, Set.mem_singleton_iff] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · rfl
        · exact (Subgroup.mem_centralizer_iff.mp hxCent b hb).symm
        · exact Subgroup.mem_centralizer_iff.mp hxCent a ha
        · exact congrArg Subtype.val
            (mul_comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
      have hHpow : ∀ y : H, y ^ p = 1 := by
        intro y
        apply Subtype.ext
        change (y : G) ^ p = 1
        have hy : (y : G) ∈
            (Subgroup.zpowers x : Set G) * (E : Set G) := by
          rw [← Subgroup.coe_mul_of_left_le_normalizer_right
            (Subgroup.zpowers x) E hzpNorm]
          exact y.property
        rcases hy with ⟨a, ha, e, he, hy⟩
        rw [← hy]
        have hae : Commute a e :=
          (Subgroup.mem_centralizer_iff.mp (hzpCent ha) e he).symm
        have hap : a ^ p = 1 := by
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
            zpow_natCast, hx.2.2, one_zpow]
        have hep : e ^ p = 1 := by
          have := hE.elementary.pow_eq_one (⟨e, he⟩ : E)
          exact congrArg Subtype.val this
        rw [hae.mul_pow, hap, hep, one_mul]
      have hHel : IsElementaryAbelianGroup p H :=
        { isPGroup := by
            intro y
            refine ⟨1, ?_⟩
            simpa using hHpow y
          commutative := inferInstance
          pow_eq_one := hHpow }
      have hHA : H ≤ A := by
        dsimp [H]
        apply sup_le
        · exact Subgroup.zpowers_le.mpr hx.1
        · exact hE.le
      have hHE : H = E := hE.2 H ⟨hHA, hHel⟩ le_sup_right
      rw [← hHE]
      exact (show Subgroup.zpowers x ≤ H from le_sup_left)
        (Subgroup.mem_zpowers x)
    · intro x hx
      have hxCent : x ∈ Subgroup.centralizer (E : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact congrArg Subtype.val
          (mul_comm (⟨y, hy⟩ : E) ⟨x, hx⟩)
      have hxPow : x ^ p = 1 := by
        exact congrArg Subtype.val
          (hE.elementary.pow_eq_one (⟨x, hx⟩ : E))
      exact ⟨hE.le hx, hxCent, hxPow⟩
  · intro hEq
    have hEdata : ∀ x : G, x ∈ E →
        x ∈ A ∧ x ∈ Subgroup.centralizer (E : Set G) ∧ x ^ p = 1 := by
      intro x hx
      have hx' : x ∈ pTorsionCentralizerWithin p A E := by
        rw [hEq]
        exact hx
      exact hx'
    have hEA : E ≤ A := fun x hx ↦ (hEdata x hx).1
    have hEpow : ∀ x : E, x ^ p = 1 := by
      intro x
      apply Subtype.ext
      exact (hEdata x x.property).2.2
    letI : IsMulCommutative E := by
      refine ⟨⟨fun x y ↦ ?_⟩⟩
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp
        (hEdata x x.property).2.1 y y.property).symm
    have hEel : IsElementaryAbelianGroup p E :=
      { isPGroup := by
          intro x
          refine ⟨1, ?_⟩
          simpa using hEpow x
        commutative := inferInstance
        pow_eq_one := hEpow }
    refine ⟨⟨hEA, hEel⟩, ?_⟩
    intro F hF hEF
    letI : IsMulCommutative F := hF.2.commutative
    apply le_antisymm ?_ hEF
    intro x hx
    have hxCent : x ∈ Subgroup.centralizer (E : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact congrArg Subtype.val
        (mul_comm (⟨e, hEF he⟩ : F) ⟨x, hx⟩)
    have hxPow : x ^ p = 1 := by
      exact congrArg Subtype.val (hF.2.pow_eq_one (⟨x, hx⟩ : F))
    have hxTorsion : x ∈ pTorsionCentralizerWithin p A E :=
      ⟨hF.1 hx, hxCent, hxPow⟩
    rw [hEq] at hxTorsion
    exact hxTorsion

end Submission.OddOrder.MathlibSupport
