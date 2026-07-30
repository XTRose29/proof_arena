import Submission.OddOrder.BG.Section07.NormedSubgroups
import Mathlib.GroupTheory.GroupAction.OfQuotient
import Mathlib.GroupTheory.PGroup

/-!
# Bender--Glauberman, Section 7: quotient fixed points

The maximal subgroups normalized by `B` carry the conjugation action of every
subgroup of the normalizer of `B`.  We use orbit--stabilizer for a transitive
action and the fixed-point congruence for a quotient p-group.
-/

namespace Submission.OddOrder.BG.Section07

open Submission.OddOrder.MathlibSupport

universe u

private abbrev MaxNormedSubgroups {G : Type u} [Group G] [Finite G]
    (B : Subgroup G) (q : ℕ) :=
  {Q : Subgroup G // Q ∈ max_normed_pgroups (B : Set G) ({q} : Set ℕ)}

/-- Conjugation by a subgroup of the normalizer preserves the maximal
normalized subgroups. -/
@[reducible] private def maxNormedConjAction {G : Type u} [Group G] [Finite G]
    {q : ℕ} (B L : Subgroup G)
    (hLB : L ≤ Subgroup.normalizer (B : Set G)) :
    MulAction L (MaxNormedSubgroups B q) where
  smul x Q :=
    ⟨Q.1.map (MulAut.conj (x : G)).toMonoidHom,
      (norm_acts_max_norm B Q.1 ({q} : Set ℕ) (x : G) (hLB x.2)).2 Q.2⟩
  one_smul Q := by
    apply Subtype.ext
    change Q.1.map (MulAut.conj (1 : G)).toMonoidHom = Q.1
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.one_mem _)
  mul_smul x y Q := by
    apply Subtype.ext
    change Q.1.map (MulAut.conj ((x : G) * (y : G))).toMonoidHom =
      (Q.1.map (MulAut.conj (y : G)).toMonoidHom).map
        (MulAut.conj (x : G)).toMonoidHom
    rw [Subgroup.map_map]
    ext z
    simp [MulAut.conj_apply, mul_assoc]

private theorem maxNormedSubgroups_nonempty {G : Type u} [Group G] [Finite G]
    (B : Subgroup G) (q : ℕ) : Nonempty (MaxNormedSubgroups B q) := by
  rcases max_normed_exists (B : Set G) ({q} : Set ℕ) (⊥ : Subgroup G)
      (by simpa using (IsPiNumber.one : IsPiNumber ({q} : Set ℕ) 1)) (by
        intro b _
        exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
          (Subgroup.map_bot (MulAut.conj b).toMonoidHom)) with
    ⟨Q, hQ, _⟩
  exact ⟨⟨Q, hQ⟩⟩

/-- A transitive conjugation action on the maximal normalized `q`-subgroups
has cardinality dividing the order of the acting subgroup. -/
theorem natCard_max_normed_pgroups_dvd_of_transitive
    {G : Type u} [Group G] [Finite G] {q : ℕ}
    (B L : Subgroup G)
    (hLB : L ≤ Subgroup.normalizer (B : Set G))
    (htrans : ∀ Q₁ Q₂ : Subgroup G,
      Q₁ ∈ max_normed_pgroups (B : Set G) ({q} : Set ℕ) →
      Q₂ ∈ max_normed_pgroups (B : Set G) ({q} : Set ℕ) →
      ∃ k : G, k ∈ L ∧ Q₂ = Q₁.map (MulAut.conj k⁻¹).toMonoidHom) :
    Nat.card {Q : Subgroup G // Q ∈ max_normed_pgroups (B : Set G) ({q} : Set ℕ)} ∣
      Nat.card L := by
  letI : MulAction L (MaxNormedSubgroups B q) := maxNormedConjAction B L hLB
  letI : MulAction.IsPretransitive L (MaxNormedSubgroups B q) :=
    ⟨fun Q₁ Q₂ => by
      rcases htrans Q₁.1 Q₂.1 Q₁.2 Q₂.2 with ⟨k, hkL, hk⟩
      refine ⟨⟨k⁻¹, L.inv_mem hkL⟩, ?_⟩
      apply Subtype.ext
      change Q₁.1.map (MulAut.conj (k⁻¹ : G)).toMonoidHom = Q₂.1
      exact hk.symm⟩
  let Q₀ : MaxNormedSubgroups B q := Classical.choice (maxNormedSubgroups_nonempty B q)
  rw [← MulAction.index_stabilizer_of_transitive L Q₀]
  exact (MulAction.stabilizer L Q₀).index_dvd_card

/-- If the quotient `P / B` is a p-group and `p` does not divide the number
of maximal normalized `q`-subgroups, one of them is normalized by `P`. -/
theorem exists_max_normed_normalized_of_quotient_isPGroup
    {G : Type u} [Group G] [Finite G] {p q : ℕ} [Fact p.Prime]
    (B P : Subgroup G) (hBP : B ≤ P)
    [hBnormal : (B.subgroupOf P).Normal]
    (hquot : IsPGroup p (P ⧸ B.subgroupOf P))
    (hcard : ¬ p ∣ Nat.card {Q : Subgroup G //
      Q ∈ max_normed_pgroups (B : Set G) ({q} : Set ℕ)}) :
    ∃ Q : Subgroup G, Q ∈ max_normed_pgroups (B : Set G) ({q} : Set ℕ) ∧
      P ≤ Subgroup.normalizer (Q : Set G) := by
  let Ω := MaxNormedSubgroups B q
  let H := B.subgroupOf P
  have hPB : P ≤ Subgroup.normalizer (B : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBP).mp hBnormal
  letI : MulAction P Ω := maxNormedConjAction B P hPB
  have hfixed (Q : Ω) : Q ∈ MulAction.fixedPoints H Ω := by
    rw [MulAction.mem_fixedPoints]
    intro b
    apply Subtype.ext
    change Q.1.map (MulAut.conj ((b : P) : G)).toMonoidHom = Q.1
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mp
    exact Q.2.prop.2 b.2
  let fixedEquiv : Ω ≃ MulAction.fixedPoints H Ω :=
    { toFun := fun Q => ⟨Q, hfixed Q⟩
      invFun := fun Q => Q.1
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcardFixed : ¬ p ∣ Nat.card (MulAction.fixedPoints H Ω) := by
    rw [Nat.card_congr fixedEquiv.symm]
    exact hcard
  rcases hquot.nonempty_fixed_point_of_prime_not_dvd_card
      (MulAction.fixedPoints H Ω) hcardFixed with ⟨R, hR⟩
  refine ⟨R.1.1, R.1.2, ?_⟩
  intro x hx
  let xP : P := ⟨x, hx⟩
  have hxR := (MulAction.mem_fixedPoints.mp hR) (xP : P ⧸ H)
  have hxΩ : xP • (R.1 : Ω) = R.1 := by
    have := congrArg (fun S : MulAction.fixedPoints H Ω => (S : Ω)) hxR
    simpa using this
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  exact congrArg Subtype.val hxΩ

end Submission.OddOrder.BG.Section07
