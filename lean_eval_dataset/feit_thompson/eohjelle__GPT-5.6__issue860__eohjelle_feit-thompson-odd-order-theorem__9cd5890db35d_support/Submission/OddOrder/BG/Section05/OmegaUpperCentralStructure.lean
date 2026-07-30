import Submission.OddOrder.BG.Section05.OmegaUpperCentralCommutator
import Mathlib.GroupTheory.Exponent

/-!
The Section 4 structural input for the omega-one subgroup of the second
upper center, transported to the ambient subgroup used in Section 5.
-/

namespace Submission.OddOrder.BG.Section05

open Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

private theorem not_isCyclic_of_elementaryAbelian_rank_three
    {E : Subgroup G} (hE : IsElementaryAbelianOfRank p 3 E) :
    ¬ IsCyclic E := by
  intro hcyclic
  letI : IsCyclic E := hcyclic
  letI := Fintype.ofFinite E
  classical
  have hle : Nat.card E ≤ p := by
    rw [Nat.card_eq_fintype_card]
    simpa only [hE.pow_eq_one, Finset.filter_true, Finset.card_univ] using
      (IsCyclic.card_pow_eq_one_le (α := E) (Fact.out : p.Prime).pos)
  have hlt : p < p ^ 3 := by
    simpa using
      (Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by omega : 1 < 3))
  exact (not_lt_of_ge (hE.card_eq ▸ hle)) hlt

private theorem not_isCyclic_of_rank_three
    (hRank3 : ∃ A : Subgroup G, IsElementaryAbelianOfRank p 3 A) :
    ¬ IsCyclic G := by
  rintro hcyclic
  obtain ⟨A, hA⟩ := hRank3
  have htop : IsCyclic (⊤ : Subgroup G) :=
    Subgroup.topEquiv.isCyclic.mpr hcyclic
  letI : IsCyclic (⊤ : Subgroup G) := htop
  exact not_isCyclic_of_elementaryAbelian_rank_three hA
    (Subgroup.isCyclic_of_le le_top)

/-- The mapped subgroup `W = Ω₁(Z₂(G))` is noncyclic and has exponent
dividing `p` under the rank-three hypotheses of Bender--Glauberman Lemma 5.2.
-/
theorem omegaOneUpperCentralTwo_structure
    (hG : IsPGroup p G) (hodd : Odd (Nat.card G))
    (hRank3 : ∃ A : Subgroup G, IsElementaryAbelianOfRank p 3 A) :
    ¬ IsCyclic (omegaOneUpperCentralTwo p G) ∧
      ∀ w : omegaOneUpperCentralTwo p G, w ^ p = 1 := by
  let O : Subgroup (Subgroup.upperCentralSeries G 2) :=
    omegaOne p (Subgroup.upperCentralSeries G 2)
  obtain ⟨hOncyclic, hOexponent⟩ :=
    Submission.OddOrder.BG.Section04.Ohm1_odd_ucn2 hG hodd
      (not_isCyclic_of_rank_three hRank3)
  let e : O ≃* omegaOneUpperCentralTwo p G :=
    O.equivMapOfInjective (Subgroup.upperCentralSeries G 2).subtype
      (Subgroup.upperCentralSeries G 2).subtype_injective
  have hWcyclic : IsCyclic (omegaOneUpperCentralTwo p G) → IsCyclic O :=
    fun hW ↦ e.isCyclic.mpr hW
  refine ⟨fun hW ↦ hOncyclic (hWcyclic hW), ?_⟩
  have hOpow : ∀ x : O, x ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hOexponent
  intro w
  obtain ⟨x, rfl⟩ := e.surjective w
  calc
    e x ^ p = e (x ^ p) := (map_pow e x p).symm
    _ = e 1 := by rw [hOpow]
    _ = 1 := map_one e

/-- The ambient commutator consequence used throughout the proof of
`Ohm1_ucn_p2maxElem`. -/
theorem commutator_omegaOneUpperCentralTwo_le_omegaOneCenter_of_rank_three
    (hG : IsPGroup p G) (hodd : Odd (Nat.card G))
    (hRank3 : ∃ A : Subgroup G, IsElementaryAbelianOfRank p 3 A) :
    ⁅omegaOneUpperCentralTwo p G, (⊤ : Subgroup G)⁆ ≤
      omegaOneCenter p G :=
  commutator_omegaOneUpperCentralTwo_le_omegaOneCenter p
    (omegaOneUpperCentralTwo_structure hG hodd hRank3).2

end Submission.OddOrder.BG.Section05
