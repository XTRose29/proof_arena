import Submission.OddOrder.MathlibSupport.ElementaryAbelianFunctorial
import Mathlib.GroupTheory.Sylow

/-!
Transport of an elementary-abelian rank obstruction from a containing
subgroup to a Sylow subgroup.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped Pointwise IsMulCommutative

universe u

variable {G : Type u} [Group G]
variable {p n : ℕ}

namespace IsElementaryAbelianOfRank

/-- Regard an elementary-abelian subgroup as a subgroup of any containing
subgroup without changing its cardinal rank. -/
theorem subgroupOf {E N : Subgroup G}
    (hE : IsElementaryAbelianOfRank p n E) (hEN : E ≤ N) :
    IsElementaryAbelianOfRank p n (E.subgroupOf N) := by
  let e : E.subgroupOf N ≃* E := Subgroup.subgroupOfEquivOfLe hEN
  letI : IsMulCommutative E := hE.commutative
  refine
    { isPGroup := hE.isPGroup.of_equiv e.symm
      commutative := isMulCommutative_iff.mpr ?_
      pow_eq_one := ?_
      card_eq := ?_ }
  · intro x y
    apply e.injective
    exact mul_comm' (e x) (e y)
  · intro x
    apply e.injective
    simpa using hE.pow_eq_one (e x)
  · exact (Nat.card_congr e.toEquiv).trans hE.card_eq

end IsElementaryAbelianOfRank

variable [Finite G] [Fact p.Prime]

/-- If a Sylow `p`-subgroup of `H`, viewed in the ambient group, lies in
`N`, then absence of elementary-abelian rank three in `N` implies the same
absence in `H`. -/
theorem no_elementaryAbelian_rank_three_of_sylow_map_le
    {H N : Subgroup G} (P : Sylow p H)
    (hPN : (P : Subgroup H).map H.subtype ≤ N)
    (hRank : ¬ ∃ E : Subgroup N,
      IsElementaryAbelianOfRank p 3 E) :
    ¬ ∃ E : Subgroup H, IsElementaryAbelianOfRank p 3 E := by
  rintro ⟨E, hE⟩
  obtain ⟨Q, hEQ⟩ := hE.isPGroup.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq H Q P
  let c : H →* H := (MulAut.conj x).toMonoidHom
  let C : Subgroup H := E.map c
  have hQC : (Q : Subgroup H).map c = (P : Subgroup H) := by
    change MulAut.conj x • (Q : Subgroup H) = (P : Subgroup H)
    rw [← Sylow.coe_subgroup_smul, hx]
  have hCP : C ≤ (P : Subgroup H) := by
    dsimp only [C]
    exact (Subgroup.map_mono hEQ).trans_eq hQC
  have hC : IsElementaryAbelianOfRank p 3 C := by
    dsimp only [C, c]
    exact hE.map_of_injective (MulAut.conj x).toMonoidHom
      (MulAut.conj x).injective
  let B : Subgroup G := C.map H.subtype
  have hBN : B ≤ N := by
    dsimp only [B]
    exact (Subgroup.map_mono hCP).trans hPN
  have hB : IsElementaryAbelianOfRank p 3 B := by
    dsimp only [B]
    exact hC.map_of_injective H.subtype H.subtype_injective
  apply hRank
  exact ⟨B.subgroupOf N, hB.subgroupOf hBN⟩

end Submission.OddOrder.MathlibSupport
