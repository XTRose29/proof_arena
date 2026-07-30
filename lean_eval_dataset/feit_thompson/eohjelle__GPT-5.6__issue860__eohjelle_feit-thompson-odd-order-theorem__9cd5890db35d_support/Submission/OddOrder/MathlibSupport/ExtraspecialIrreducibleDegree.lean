import Submission.OddOrder.MathlibSupport.Extraspecial
import Submission.OddOrder.MathlibSupport.ExtraspecialCharacterVanishing

/-!
The degree of a faithful irreducible representation of an extraspecial group.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra BigOperators

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [IsAlgClosed k] [CharZero k]
variable [Group G] [Finite G]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {p n : ℕ} [Fact p.Prime]

namespace IsExtraspecial

/-- Character orthogonality for a faithful irreducible representation reduces
to a sum over the prime-order center. -/
theorem faithful_irreducible_character_norm_center
    (hG : IsExtraspecial G) (hpG : IsPGroup p G)
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    (hrho : Function.Injective rho) :
    letI := Fintype.ofFinite G
    ∑ g : G, rho.character g * rho.character g⁻¹ =
      (p : k) * (Module.finrank k V : k) ^ 2 := by
  letI := Fintype.ofFinite G
  classical
  let d : k := Module.finrank k V
  have hcenter (z : Subgroup.center G) :
      rho.character z * rho.character (z : G)⁻¹ = d ^ 2 := by
    rw [character_center_eq_finrank_mul_schurCenterScalarCharacter rho z]
    have hinv :=
      character_center_eq_finrank_mul_schurCenterScalarCharacter rho z⁻¹
    change rho.character (z : G)⁻¹ =
      (Module.finrank k V : k) *
        (schurCenterScalarCharacter rho z⁻¹ : k) at hinv
    rw [hinv, map_inv, Units.val_inv_eq_inv_val]
    dsimp [d]
    have hc : (schurCenterScalarCharacter rho z : k) ≠ 0 := Units.ne_zero _
    calc
      (Module.finrank k V : k) * (schurCenterScalarCharacter rho z : k) *
          ((Module.finrank k V : k) *
            (schurCenterScalarCharacter rho z : k)⁻¹) =
          (Module.finrank k V : k) ^ 2 *
            ((schurCenterScalarCharacter rho z : k) *
              (schurCenterScalarCharacter rho z : k)⁻¹) := by ring
      _ = (Module.finrank k V : k) ^ 2 := by rw [mul_inv_cancel₀ hc, mul_one]
  have hterm (g : G) :
      rho.character g * rho.character g⁻¹ =
        if g ∈ Subgroup.center G then d ^ 2 else 0 := by
    by_cases hg : g ∈ Subgroup.center G
    · rw [if_pos hg]
      exact hcenter ⟨g, hg⟩
    · rw [if_neg hg,
        hG.toIsSpecial.character_eq_zero_of_not_mem_center rho hrho hg,
        zero_mul]
  calc
    ∑ g : G, rho.character g * rho.character g⁻¹ =
        ∑ g : G, if g ∈ Subgroup.center G then d ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro g _
      exact hterm g
    _ = (∑ g : G, if g ∈ Subgroup.center G then (1 : k) else 0) * d ^ 2 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro g _
      split <;> simp_all
    _ = (Nat.card (Subgroup.center G) : k) * d ^ 2 := by
      rw [Finset.sum_boole]
      congr 2
      rw [Nat.card_eq_fintype_card]
      exact (Fintype.card_subtype
        (fun g : G ↦ g ∈ Subgroup.center G)).symm
    _ = (p : k) * (Module.finrank k V : k) ^ 2 := by
      rw [hG.center_card_eq hpG]

/-- The degree-square formula for a faithful irreducible representation of an
extraspecial group of order `p ^ (2 * n + 1)`. -/
theorem faithful_irreducible_finrank_sq_eq
    (hG : IsExtraspecial G) (hpG : IsPGroup p G)
    (hcard : Nat.card G = p ^ (2 * n + 1))
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    (hrho : Function.Injective rho) :
    Module.finrank k V ^ 2 = p ^ (2 * n) := by
  letI := Fintype.ofFinite G
  classical
  have hnatCardNe : Nat.card G ≠ 0 := by
    rw [hcard]
    exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hcardne : (Nat.card G : k) ≠ 0 := Nat.cast_ne_zero.mpr hnatCardNe
  letI : Invertible (Nat.card G : k) := invertibleOfNonzero hcardne
  letI : Nonempty (rho.Equiv rho) := ⟨Representation.Equiv.refl rho⟩
  have horth :
      (Nat.card G : k)⁻¹ *
          ∑ g : G, rho.character g * rho.character g⁻¹ = 1 := by
    simpa only [if_pos (show Nonempty (rho.Equiv rho) from inferInstance)] using
      rho.char_orthonormal rho
  have hsum :
      ∑ g : G, rho.character g * rho.character g⁻¹ =
        (Nat.card G : k) := by
    calc
      ∑ g : G, rho.character g * rho.character g⁻¹ =
          (Nat.card G : k) *
            ((Nat.card G : k)⁻¹ *
              ∑ g : G, rho.character g * rho.character g⁻¹) := by
        field_simp
      _ = (Nat.card G : k) := by rw [horth, mul_one]
  rw [hG.faithful_irreducible_character_norm_center hpG rho hrho,
    hcard, Nat.cast_pow] at hsum
  apply Nat.cast_injective (R := k)
  simp only [Nat.cast_pow]
  have hpne : (p : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  apply mul_left_cancel₀ hpne
  calc
    (p : k) * (Module.finrank k V : k) ^ 2 =
        (p : k) ^ (2 * n + 1) := hsum
    _ = (p : k) * (p : k) ^ (2 * n) := by rw [pow_succ']

/-- A faithful irreducible representation of an extraspecial group of order
`p ^ (2 * n + 1)` has degree `p ^ n`. -/
theorem faithful_irreducible_finrank_eq
    (hG : IsExtraspecial G) (hpG : IsPGroup p G)
    (hcard : Nat.card G = p ^ (2 * n + 1))
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    (hrho : Function.Injective rho) :
    Module.finrank k V = p ^ n := by
  apply Nat.pow_left_injective (by omega : 2 ≠ 0)
  simpa [pow_mul, Nat.mul_comm] using
    hG.faithful_irreducible_finrank_sq_eq hpG hcard rho hrho

end IsExtraspecial

end Submission.OddOrder.MathlibSupport
