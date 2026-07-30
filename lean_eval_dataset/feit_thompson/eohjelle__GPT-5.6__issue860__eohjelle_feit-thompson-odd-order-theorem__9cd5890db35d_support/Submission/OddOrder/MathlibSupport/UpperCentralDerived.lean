import Mathlib.GroupTheory.Nilpotent

/-!
The second center centralizes the derived subgroup.  This is the
three-subgroups input in the special-group reduction.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G]

/-- The second term of the upper central series centralizes the commutator
subgroup. -/
theorem commutator_upperCentralSeries_two_eq_bot :
    ⁅_root_.commutator G, Subgroup.upperCentralSeries G 2⁆ = ⊥ := by
  change ⁅⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆,
    Subgroup.upperCentralSeries G 2⁆ = ⊥
  let Z2 := Subgroup.upperCentralSeries G 2
  have hstep : ⁅Z2, (⊤ : Subgroup G)⁆ ≤ Subgroup.center G := by
    rw [Subgroup.commutator_le]
    intro x hx y _hy
    have hx' := (Subgroup.mem_upperCentralSeries_succ_iff
      (G := G) (n := 1) (x := x)).mp (by simpa [Z2] using hx) y
    simpa using hx'
  have h1 : ⁅⁅(⊤ : Subgroup G), Z2⁆, (⊤ : Subgroup G)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    rw [Subgroup.commutator_comm]
    exact hstep.trans (Subgroup.center_le_centralizer (⊤ : Set G))
  have h2 : ⁅⁅Z2, (⊤ : Subgroup G)⁆, (⊤ : Subgroup G)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hstep.trans (Subgroup.center_le_centralizer (⊤ : Set G))
  simpa [Z2] using
    (Subgroup.commutator_commutator_eq_bot_of_rotate
      (H₁ := (⊤ : Subgroup G)) (H₂ := (⊤ : Subgroup G)) (H₃ := Z2)
      h1 h2)

/-- The intersection of the second center and the derived subgroup is
abelian. -/
theorem inf_upperCentralSeries_two_commutator_isMulCommutative :
    IsMulCommutative
      ((Subgroup.upperCentralSeries G 2 ⊓ _root_.commutator G) : Subgroup G) := by
  apply IsMulCommutative.of_setLike_mul_comm
  intro x hx y hy
  have hcent : _root_.commutator G ≤
      Subgroup.centralizer (Subgroup.upperCentralSeries G 2 : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      commutator_upperCentralSeries_two_eq_bot
  exact Subgroup.mem_centralizer_iff.mp (hcent hy.2) x hx.1

/-- The second upper-central subgroup has lower central series zero at
weight two. -/
theorem lowerCentralSeries_two_upperCentralSeries_two_eq_bot :
    (Subgroup.upperCentralSeries G 2).lowerCentralSeries 2 = ⊥ := by
  change ⁅⁅Subgroup.upperCentralSeries G 2,
    Subgroup.upperCentralSeries G 2⁆,
      Subgroup.upperCentralSeries G 2⁆ = ⊥
  apply le_bot_iff.mp
  calc
    ⁅⁅Subgroup.upperCentralSeries G 2,
        Subgroup.upperCentralSeries G 2⁆,
        Subgroup.upperCentralSeries G 2⁆ ≤
        ⁅_root_.commutator G, Subgroup.upperCentralSeries G 2⁆ :=
      Subgroup.commutator_mono
        (Subgroup.commutator_mono le_top le_top) le_rfl
    _ = ⊥ := commutator_upperCentralSeries_two_eq_bot

theorem lowerCentralSeries_two_upperCentralSeries_two_subtype_eq_bot :
    Subgroup.lowerCentralSeries
      (⊤ : Subgroup (Subgroup.upperCentralSeries G 2)) 2 = ⊥ := by
  let Z2 := Subgroup.upperCentralSeries G 2
  have hambient : Z2.lowerCentralSeries 2 = ⊥ := by
    simpa [Z2] using
      (lowerCentralSeries_two_upperCentralSeries_two_eq_bot (G := G))
  have hmap :
      (Subgroup.lowerCentralSeries (⊤ : Subgroup Z2) 2).map Z2.subtype = ⊥ := by
    rw [Subgroup.top_subtype_lowerCentralSeries, hambient]
  exact ((Subgroup.lowerCentralSeries (⊤ : Subgroup Z2) 2).map_eq_bot_iff_of_injective
    Z2.subtype_injective).mp hmap

instance upperCentralSeries_two_isNilpotent :
    Group.IsNilpotent (Subgroup.upperCentralSeries G 2) :=
  (Subgroup.nilpotent_iff_lowerCentralSeries
    (G := Subgroup.upperCentralSeries G 2)).mpr
      ⟨2, lowerCentralSeries_two_upperCentralSeries_two_subtype_eq_bot (G := G)⟩

/-- The subgroup `Z₂(G)` has nilpotency class at most two. -/
theorem nilpotencyClass_upperCentralSeries_two_le :
    Group.nilpotencyClass (Subgroup.upperCentralSeries G 2) ≤ 2 := by
  exact (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le
    (G := Subgroup.upperCentralSeries G 2) (n := 2)).mp
      (lowerCentralSeries_two_upperCentralSeries_two_subtype_eq_bot (G := G))

end Submission.OddOrder.MathlibSupport
