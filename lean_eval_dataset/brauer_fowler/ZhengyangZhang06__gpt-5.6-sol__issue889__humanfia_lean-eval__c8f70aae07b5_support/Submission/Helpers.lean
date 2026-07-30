import Mathlib

namespace Submission.Helpers

theorem card_le_factorial_index_of_ne_top
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (H : Subgroup G) (hH : H ≠ ⊤) :
    Nat.card G ≤ H.index.factorial := by
  let rho := MulAction.toPermHom G (G ⧸ H)
  have hrho : Function.Injective rho := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [← H.normalCore_eq_ker]
    rcases H.normalCore_normal.eq_bot_or_eq_top with hcore | hcore
    · exact hcore
    · exact (hH (top_unique (hcore ▸ H.normalCore_le))).elim
  calc
    Nat.card G ≤ Nat.card (Equiv.Perm (G ⧸ H)) :=
      Nat.card_le_card_of_injective rho hrho
    _ = (Nat.card (G ⧸ H)).factorial := Nat.card_perm
    _ = H.index.factorial := by rw [H.index_eq_card]

theorem card_prod_ne {α : Type*} [Fintype α] [DecidableEq α] :
    Fintype.card {p : α × α // p.2 ≠ p.1} =
      Fintype.card α * (Fintype.card α - 1) := by
  let e : {p : α × α // p.2 ≠ p.1} ≃ Σ a : α, {b : α // b ≠ a} :=
    { toFun := fun p => ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
      invFun := fun p => ⟨(p.1, p.2.1), p.2.2⟩
      left_inv := by rintro ⟨⟨a, b⟩, h⟩; rfl
      right_inv := by rintro ⟨a, b, h⟩; rfl }
  rw [Fintype.card_congr e]
  simp [Fintype.card_sigma]

theorem nat_card_conj_orbit_mul_centralizer
    {G : Type*} [Group G] [Finite G] (t : G) :
    Nat.card (MulAction.orbit (ConjAct G) t) *
        Nat.card (Subgroup.centralizer ({t} : Set G)) = Nat.card G := by
  classical
  letI := Fintype.ofFinite G
  rw [Subgroup.nat_card_centralizer_nat_card_stabilizer]
  calc
    Nat.card (MulAction.orbit (ConjAct G) t) *
          Nat.card (MulAction.stabilizer (ConjAct G) t) = Nat.card (ConjAct G) := by
      simpa only [Nat.card_eq_fintype_card] using
        MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) t
    _ = Nat.card G :=
      (Nat.card_congr (ConjAct.toConjAct (G := G)).toEquiv).symm

end Submission.Helpers
