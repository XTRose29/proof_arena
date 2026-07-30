import Submission.OddOrder.BG.Section04.OmegaOneUpperCentral
import Submission.OddOrder.MathlibSupport.OmegaOneFunctorial

/-!
The three characteristic subgroups used in Bender--Glauberman Lemma 5.2.
-/

namespace Submission.OddOrder.BG.Section05

open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G]

/-- MathComp's `Z := 'Ohm_1('Z(G))`, transported to the ambient group. -/
def omegaOneCenter (p : ℕ) (G : Type u) [Group G] : Subgroup G :=
  (omegaOne p (Subgroup.center G)).map (Subgroup.center G).subtype

/-- MathComp's `W := 'Ohm_1('Z_2(G))`, transported to the ambient group. -/
def omegaOneUpperCentralTwo (p : ℕ) (G : Type u) [Group G] : Subgroup G :=
  (omegaOne p (Subgroup.upperCentralSeries G 2)).map
    (Subgroup.upperCentralSeries G 2).subtype

/-- MathComp's `T := 'C_G(W)`. -/
def omegaUpperCentralTwoCentralizer
    (p : ℕ) (G : Type u) [Group G] : Subgroup G :=
  Subgroup.centralizer (omegaOneUpperCentralTwo p G : Set G)

private theorem map_omegaOne_subtype_characteristic
    (p : ℕ) (H : Subgroup G) [H.Characteristic] :
    ((omegaOne p H).map H.subtype).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro e
  have hmapH : H.map e.toMonoidHom = H :=
    Subgroup.characteristic_iff_map_eq.mp
      (show H.Characteristic from inferInstance) e
  let eH : H →* H :=
    (e.toMonoidHom.comp H.subtype).codRestrict H fun h ↦ by
    change e (h : G) ∈ H
    have heh : e (h : G) ∈ H.map e.toMonoidHom := ⟨h, h.2, rfl⟩
    rw [hmapH] at heh
    exact heh
  rintro _ ⟨x, hx, rfl⟩
  rcases hx with ⟨h, hhOmega, rfl⟩
  have hehOmega : eH h ∈ omegaOne p H :=
    map_omegaOne_le p eH
      (Subgroup.mem_map_of_mem eH hhOmega)
  exact ⟨eH h, hehOmega, rfl⟩

instance omegaOneCenter_characteristic (p : ℕ) :
    (omegaOneCenter p G).Characteristic := by
  dsimp [omegaOneCenter]
  exact map_omegaOne_subtype_characteristic p (Subgroup.center G)

instance omegaOneUpperCentralTwo_characteristic (p : ℕ) :
    (omegaOneUpperCentralTwo p G).Characteristic := by
  dsimp [omegaOneUpperCentralTwo]
  exact map_omegaOne_subtype_characteristic p
    (Subgroup.upperCentralSeries G 2)

instance omegaUpperCentralTwoCentralizer_characteristic (p : ℕ) :
    (omegaUpperCentralTwoCentralizer p G).Characteristic := by
  dsimp [omegaUpperCentralTwoCentralizer]
  infer_instance

theorem omegaOneCenter_le_center (p : ℕ) :
    omegaOneCenter p G ≤ Subgroup.center G :=
  Subgroup.map_subtype_le _

/-- Every element of the mapped omega-one subgroup of the center has
`p`th power one. -/
theorem omegaOneCenter_pow_eq_one (p : ℕ) :
    ∀ z : omegaOneCenter p G, z ^ p = 1 := by
  rintro ⟨_, z, hzOmega, rfl⟩
  apply Subtype.ext
  change (z : G) ^ p = 1
  simpa using congrArg Subtype.val
    (omegaOne_pow_eq_one_of_mul_closed p
      (fun a b ha hb ↦ by
        have hab : Commute a b := Std.Commutative.comm a b
        simpa [ha, hb] using hab.mul_pow p) hzOmega)

theorem omegaOneUpperCentralTwo_le_upperCentralSeries (p : ℕ) :
    omegaOneUpperCentralTwo p G ≤ Subgroup.upperCentralSeries G 2 :=
  Subgroup.map_subtype_le _

theorem omegaOneCenter_le_omegaOneUpperCentralTwo (p : ℕ) :
    omegaOneCenter p G ≤ omegaOneUpperCentralTwo p G := by
  rintro x ⟨z, hzOmega, rfl⟩
  have hzZ2 : (z : G) ∈ Subgroup.upperCentralSeries G 2 := by
    have hzCenter : (z : G) ∈ Subgroup.upperCentralSeries G 1 := by
      rw [Subgroup.upperCentralSeries_one]
      exact z.2
    exact Subgroup.upperCentralSeries_mono (G := G) (by omega) hzCenter
  let z₂ : Subgroup.upperCentralSeries G 2 := ⟨z, hzZ2⟩
  have hzPow : z₂ ^ p = 1 := by
    apply Subtype.ext
    change (z : G) ^ p = 1
    simpa using congrArg Subtype.val
      (omegaOne_pow_eq_one_of_mul_closed p
        (fun a b ha hb ↦ by
          have hab : Commute a b := Std.Commutative.comm a b
          simpa [ha, hb] using hab.mul_pow p) hzOmega)
  exact ⟨z₂, mem_omegaOne_of_pow_eq_one p hzPow, rfl⟩

end Submission.OddOrder.BG.Section05
