import Submission.BFC
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

namespace Submission.Helpers

open scoped BigOperators commutatorElement

noncomputable section

def derivedCommutator (G : Type) [Group G] (x y : G) : commutator G :=
  ⟨⁅x, y⁆, by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)⟩

lemma derivedCommutator_mul_right (G : Type) [Group G]
    (hcentral : commutator G ≤ Subgroup.center G) (x y z : G) :
    derivedCommutator G x (y * z) =
      derivedCommutator G x y * derivedCommutator G x z := by
  apply Subtype.ext
  change ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆
  rw [commutatorElement_mul_right_eq_mul_conj]
  have hz : y * ⁅x, z⁆ = ⁅x, z⁆ * y :=
    Subgroup.mem_center_iff.mp (hcentral (derivedCommutator G x z).property) y
  calc
    ⁅x, y⁆ * y * ⁅x, z⁆ * y⁻¹ = ⁅x, y⁆ * (y * ⁅x, z⁆) * y⁻¹ := by
      simp [mul_assoc]
    _ = ⁅x, y⁆ * (⁅x, z⁆ * y) * y⁻¹ := by rw [hz]
    _ = ⁅x, y⁆ * ⁅x, z⁆ := by simp [mul_assoc]

lemma derivedCommutator_mul_left (G : Type) [Group G]
    (hcentral : commutator G ≤ Subgroup.center G) (x y z : G) :
    derivedCommutator G (x * y) z =
      derivedCommutator G x z * derivedCommutator G y z := by
  apply Subtype.ext
  change ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hy : x * ⁅y, z⁆ = ⁅y, z⁆ * x :=
    Subgroup.mem_center_iff.mp (hcentral (derivedCommutator G y z).property) x
  have hcomm : ⁅y, z⁆ * ⁅x, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ :=
    (Subgroup.mem_center_iff.mp
      (hcentral (derivedCommutator G y z).property) ⁅x, z⁆).symm
  calc
    x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ = (x * ⁅y, z⁆) * x⁻¹ * ⁅x, z⁆ := rfl
    _ = (⁅y, z⁆ * x) * x⁻¹ * ⁅x, z⁆ := by rw [hy]
    _ = ⁅y, z⁆ * ⁅x, z⁆ := by simp [mul_assoc]
    _ = ⁅x, z⁆ * ⁅y, z⁆ := hcomm

def commutatorAddChar (G : Type) [Group G]
    (hcentral : commutator G ≤ Subgroup.center G)
    (psi : AddChar (Additive (commutator G)) ℂ) (x : G) : AddChar (Additive G) ℂ where
  toFun y := psi (Additive.ofMul (derivedCommutator G x y.toMul))
  map_zero_eq_one' := by
    change psi (Additive.ofMul (derivedCommutator G x 1)) = 1
    rw [show derivedCommutator G x 1 = 1 by ext; simp [derivedCommutator]]
    exact psi.map_zero_eq_one
  map_add_eq_mul' := by
    intro a b
    change psi (Additive.ofMul (derivedCommutator G x (a.toMul * b.toMul))) = _
    rw [derivedCommutator_mul_right G hcentral]
    exact psi.map_add_eq_mul _ _

def commutatorCharMap (G : Type) [Group G]
    (hcentral : commutator G ≤ Subgroup.center G)
    (psi : AddChar (Additive (commutator G)) ℂ) :
    Additive G →+ AddChar (Additive G) ℂ where
  toFun x := commutatorAddChar G hcentral psi x.toMul
  map_zero' := by
    apply AddChar.ext
    intro y
    change psi (Additive.ofMul (derivedCommutator G 1 y.toMul)) = 1
    rw [show derivedCommutator G 1 y.toMul = 1 by ext; simp [derivedCommutator]]
    exact psi.map_zero_eq_one
  map_add' := by
    intro a b
    apply AddChar.ext
    intro y
    change psi (Additive.ofMul (derivedCommutator G (a.toMul * b.toMul) y.toMul)) = _
    rw [derivedCommutator_mul_left G hcentral]
    exact psi.map_add_eq_mul _ _

@[reducible]
def commutatorCommGroupOfLeCenter (G : Type) [Group G]
    (hcentral : commutator G ≤ Subgroup.center G) : CommGroup (commutator G) :=
  CommGroup.mk fun a b => by
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (hcentral a.property) b.1).symm

lemma expect_zero_fiber_eq_inv_index
    {A B : Type} [AddGroup A] [Fintype A] [AddZeroClass B] [DecidableEq B]
    (f : A →+ B) :
    (𝔼 x : A, if f x = 0 then (1 : ℂ) else 0) = 1 / (f.ker.index : ℂ) := by
  classical
  rw [Fintype.expect_eq_sum_div_card, Finset.sum_boole]
  have hcard : (Finset.univ.filter fun x : A => f x = 0).card = Nat.card f.ker := by
    calc
      _ = Fintype.card {x : A // f x = 0} :=
        (Fintype.subtype_card _ (by simp)).symm
      _ = Fintype.card f.ker := by
        apply Fintype.card_congr
        exact {
          toFun := fun x => ⟨x, x.property⟩
          invFun := fun x => ⟨x, x.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      _ = Nat.card f.ker := Nat.card_eq_fintype_card.symm
  rw [hcard, ← Nat.card_eq_fintype_card]
  rw [← f.ker.card_mul_index, Nat.cast_mul]
  have hkNat : Nat.card f.ker ≠ 0 := Nat.ne_of_gt Nat.card_pos
  have hk : (Nat.card f.ker : ℂ) ≠ 0 := by exact_mod_cast hkNat
  field_simp

lemma expect_commute_indicator_eq_commProb
    (G : Type) [Group G] [Fintype G] [DecidableEq G] :
    (𝔼 x : G, 𝔼 y : G, if x * y = y * x then (1 : ℂ) else 0) =
      ((commProb G : ℚ) : ℂ) := by
  classical
  rw [← Finset.expect_product']
  simp only [Finset.univ_product_univ]
  rw [Fintype.expect_eq_sum_div_card, Finset.sum_boole]
  rw [commProb_def]
  push_cast
  congr 2
  · rw [Nat.card_eq_fintype_card]
    calc
      (Finset.univ.filter fun p : G × G => p.1 * p.2 = p.2 * p.1).card =
          Fintype.card {p : G × G // p.1 * p.2 = p.2 * p.1} :=
        (Fintype.subtype_card _ (by simp)).symm
      _ = Fintype.card {p : G × G // Commute p.1 p.2} := by
        apply Fintype.card_congr
        exact {
          toFun := fun p => ⟨p, p.property⟩
          invFun := fun p => ⟨p, p.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
  · rw [Fintype.card_prod, Nat.card_eq_fintype_card]
    simp [pow_two, Nat.cast_mul]

lemma expect_rotate_three
    {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (f : A → B → C → ℂ) :
    (𝔼 a : A, 𝔼 b : B, 𝔼 c : C, f a b c) =
      𝔼 c : C, 𝔼 a : A, 𝔼 b : B, f a b c := by
  calc
    _ = 𝔼 a : A, 𝔼 c : C, 𝔼 b : B, f a b c := by
      apply Finset.expect_congr rfl
      intro a _
      exact Finset.expect_comm Finset.univ Finset.univ (fun b c => f a b c)
    _ = _ :=
      Finset.expect_comm Finset.univ Finset.univ (fun a c => 𝔼 b : B, f a b c)

end

end Submission.Helpers
