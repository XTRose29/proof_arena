import Mathlib

namespace Submission.Helpers

open Polynomial IntermediateField

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

def RadicallyClosed : Prop :=
  ∀ (x : E) (n : ℕ), n ≠ 0 → x ^ n ∈ (⊥ : IntermediateField K E) →
    x ∈ (⊥ : IntermediateField K E)

private theorem radicallyClosed_tower (hrad : RadicallyClosed (K := K) (E := E))
    (L : IntermediateField K E) : RadicallyClosed (K := K) (E := L) := by
  intro x n hn hx
  rw [IntermediateField.mem_bot] at hx ⊢
  obtain ⟨a, ha⟩ := hx
  have hxE : (x : E) ^ n ∈ (⊥ : IntermediateField K E) := by
    rw [IntermediateField.mem_bot]
    exact ⟨a, congrArg Subtype.val ha⟩
  obtain ⟨b, hb⟩ := IntermediateField.mem_bot.mp (hrad x n hn hxE)
  exact ⟨b, Subtype.ext hb⟩

private theorem bot_eq_top_of_isCyclic [FiniteDimensional K E] [IsGalois K E]
    [IsCyclic Gal(E/K)] (hrad : RadicallyClosed (K := K) (E := E))
    (hroots : ∀ n : ℕ, n ≠ 0 → (primitiveRoots n K).Nonempty) :
    (⊥ : IntermediateField K E) = ⊤ := by
  have hn : Module.finrank K E ≠ 0 := Module.finrank_pos.ne'
  obtain ⟨α, hα, hα_top⟩ :=
    exists_root_adjoin_eq_top_of_isCyclic K E (hroots (Module.finrank K E) hn)
  apply le_antisymm bot_le
  rw [← hα_top]
  exact adjoin_le_iff.mpr <| Set.singleton_subset_iff.mpr <|
    hrad α (Module.finrank K E) hn (IntermediateField.mem_bot.mpr hα)

private theorem bot_eq_top_of_isMulCommutative [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)] (hrad : RadicallyClosed (K := K) (E := E))
    (hroots : ∀ n : ℕ, n ≠ 0 → (primitiveRoots n K).Nonempty) :
    (⊥ : IntermediateField K E) = ⊤ := by
  induction hdegree : Module.finrank K E using Nat.strong_induction_on generalizing K E with
  | h n ih =>
      let G := Gal(E/K)
      cases subsingleton_or_nontrivial G with
      | inl hG =>
          letI : Subsingleton G := hG
          letI : IsCyclic G := isCyclic_of_subsingleton
          exact bot_eq_top_of_isCyclic hrad hroots
      | inr hG =>
          letI : Nontrivial G := hG
          obtain ⟨σ : G, hσ⟩ := exists_ne (1 : G)
          let H : Subgroup G := Subgroup.zpowers σ
          have hH_ne : H ≠ ⊥ := by
            intro hH
            apply hσ
            apply Subgroup.mem_bot.mp
            rw [← hH]
            exact Subgroup.mem_zpowers σ
          let L : IntermediateField K E := IntermediateField.fixedField H
          have hL_ne : L ≠ ⊤ := by
            intro hL
            change IntermediateField.fixedField H = ⊤ at hL
            have hfix := IntermediateField.fixingSubgroup_fixedField H
            rw [hL, IntermediateField.fixingSubgroup_top] at hfix
            exact hH_ne hfix.symm
          have hLE : 1 < Module.finrank L E := by
            have hpos : 0 < Module.finrank L E := Module.finrank_pos
            have hone : Module.finrank L E ≠ 1 := by
              intro hone
              exact hL_ne (IntermediateField.finrank_eq_one_iff_eq_top.mp hone)
            omega
          have hdegreeL : Module.finrank K L < Module.finrank K E := by
            rw [← Module.finrank_mul_finrank K L E]
            nlinarith [Module.finrank_pos (R := K) (M := L)]
          letI : IsMulCommutative (G ⧸ H) :=
            Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr <|
              (commutator_eq_bot G).le.trans bot_le
          letI : IsMulCommutative Gal(L/K) :=
            let e : (G ⧸ H) ≃* Gal(L/K) := IsGalois.normalAutEquivQuotient H
            ⟨⟨fun a b ↦ by
              apply e.symm.injective
              simp only [map_mul]
              exact mul_comm' _ _⟩⟩
          have hL_bot : (⊥ : IntermediateField K L) = ⊤ :=
            ih (Module.finrank K L) (by simpa [hdegree] using hdegreeL)
              (radicallyClosed_tower hrad L) hroots rfl
          have hL_eq_bot : L = (⊥ : IntermediateField K E) := by
            have hlift := congrArg (IntermediateField.lift (F := L)) hL_bot
            simpa using hlift.symm
          have hH_top : H = ⊤ := by
            change IntermediateField.fixedField H = (⊥ : IntermediateField K E) at hL_eq_bot
            have hfix := IntermediateField.fixingSubgroup_fixedField H
            rw [hL_eq_bot, IntermediateField.fixingSubgroup_bot] at hfix
            exact hfix.symm
          letI : IsCyclic G :=
            isCyclic_iff_exists_zpowers_eq_top.mpr ⟨σ, hH_top⟩
          exact bot_eq_top_of_isCyclic hrad hroots

theorem bot_eq_top_of_isSolvable [FiniteDimensional K E] [IsGalois K E]
    [IsSolvable Gal(E/K)] (hrad : RadicallyClosed (K := K) (E := E))
    (hroots : ∀ n : ℕ, n ≠ 0 → (primitiveRoots n K).Nonempty) :
    (⊥ : IntermediateField K E) = ⊤ := by
  let G := Gal(E/K)
  cases subsingleton_or_nontrivial G with
  | inl hG =>
      letI : Subsingleton G := hG
      letI : IsCyclic G := isCyclic_of_subsingleton
      exact bot_eq_top_of_isCyclic hrad hroots
  | inr hG =>
      letI : Nontrivial G := hG
      let H : Subgroup G := commutator G
      have hH_lt : H < ⊤ := IsSolvable.commutator_lt_top_of_nontrivial G
      let L : IntermediateField K E := IntermediateField.fixedField H
      letI : IsMulCommutative (G ⧸ H) :=
        Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
      letI : IsMulCommutative Gal(L/K) :=
        let e : (G ⧸ H) ≃* Gal(L/K) := IsGalois.normalAutEquivQuotient H
        ⟨⟨fun a b ↦ by
          apply e.symm.injective
          simp only [map_mul]
          exact mul_comm' _ _⟩⟩
      have hL_bot : (⊥ : IntermediateField K L) = ⊤ :=
        bot_eq_top_of_isMulCommutative (radicallyClosed_tower hrad L) hroots
      have hL_eq_bot : L = (⊥ : IntermediateField K E) := by
        have hlift := congrArg (IntermediateField.lift (F := L)) hL_bot
        simpa using hlift.symm
      have hH_top : H = ⊤ := by
        change IntermediateField.fixedField H = (⊥ : IntermediateField K E) at hL_eq_bot
        have hfix := IntermediateField.fixingSubgroup_fixedField H
        rw [hL_eq_bot, IntermediateField.fixingSubgroup_bot] at hfix
        exact hfix.symm
      exact (hH_lt.ne hH_top).elim

end Submission.Helpers
