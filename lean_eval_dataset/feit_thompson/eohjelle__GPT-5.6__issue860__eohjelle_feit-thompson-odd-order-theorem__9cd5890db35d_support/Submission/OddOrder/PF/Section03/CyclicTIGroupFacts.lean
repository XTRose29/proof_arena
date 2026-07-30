import Submission.OddOrder.PF.Section01.ClassFunctionSupport
import Submission.OddOrder.PF.Section03.InternalDirectProduct

/-!
# Group-theoretic consequences of the cyclic-TI hypothesis

This file ports the elementary group and cardinality facts at the start of
the cyclic part of Peterfalvi Section 3.  The character-theoretic construction
only needs the fixed internal direct-product proof from
`InternalDirectProduct`; all declarations here remain proposition-valued.
-/

namespace Submission.OddOrder.PF

noncomputable section

universe u

variable {Γ : Type u} [Group Γ]

namespace IsInternalDirectProductIn

variable {W W₁ W₂ : Subgroup Γ}

/-- Under the canonical product equivalence, an element belongs to the left
factor exactly when its right coordinate is trivial. -/
@[simp]
theorem mulEquiv_mem_left_iff
    (h : IsInternalDirectProductIn W₁ W₂ W) (x : W₁ × W₂) :
    ((h.mulEquiv x : W) : Γ) ∈ W₁ ↔ x.2 = 1 := by
  constructor
  · intro hx
    let z : W₁ := ⟨((h.mulEquiv x : W) : Γ), hx⟩
    have heq : h.mulEquiv x = h.leftEmbedding z := by
      apply Subtype.ext
      rfl
    have hproj := congrArg (fun w : W ↦ h.rightProjection w) heq
    simpa using hproj
  · intro hx
    have hpair : x = (x.1, 1) := Prod.ext rfl hx
    rw [hpair, h.mulEquiv_apply_left]
    exact x.1.property

/-- Under the canonical product equivalence, an element belongs to the right
factor exactly when its left coordinate is trivial. -/
@[simp]
theorem mulEquiv_mem_right_iff
    (h : IsInternalDirectProductIn W₁ W₂ W) (x : W₁ × W₂) :
    ((h.mulEquiv x : W) : Γ) ∈ W₂ ↔ x.1 = 1 := by
  constructor
  · intro hx
    let z : W₂ := ⟨((h.mulEquiv x : W) : Γ), hx⟩
    have heq : h.mulEquiv x = h.rightEmbedding z := by
      apply Subtype.ext
      rfl
    have hproj := congrArg (fun w : W ↦ h.leftProjection w) heq
    simpa using hproj
  · intro hx
    have hpair : x = (1, x.2) := Prod.ext hx rfl
    rw [hpair, h.mulEquiv_apply_right]
    exact x.2.property

/-- Cardinality of an internal direct product.  This is valid with
`Nat.card` even before finiteness is deduced from odd order. -/
theorem card_eq_mul_card (h : IsInternalDirectProductIn W₁ W₂ W) :
    Nat.card W = Nat.card W₁ * Nat.card W₂ := by
  simpa only [Nat.card_prod] using
    (Nat.card_congr h.mulEquiv.toEquiv).symm

/-- The canonical product equivalence identifies the cyclic-TI set inside
`W` with the product of the nonidentity elements in the two factors. -/
theorem image_nonidentity_prod
    (h : IsInternalDirectProductIn W₁ W₂ W) :
    h.mulEquiv ''
        (((Set.univ : Set W₁) \ {1}) ×ˢ ((Set.univ : Set W₂) \ {1})) =
      cyclicTISetInW W W₁ W₂ := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_cyclicTISetInW]
    rw [h.mulEquiv_mem_left_iff, h.mulEquiv_mem_right_iff]
    simpa [and_comm] using hx
  · intro hw
    refine ⟨h.mulEquiv.symm w, ?_, h.mulEquiv.apply_symm_apply w⟩
    have hw' :
        h.mulEquiv (h.mulEquiv.symm w) ∈ cyclicTISetInW W W₁ W₂ := by
      simpa using hw
    rw [mem_cyclicTISetInW] at hw'
    rw [h.mulEquiv_mem_left_iff, h.mulEquiv_mem_right_iff] at hw'
    simpa [and_comm] using hw'

/-- Peterfalvi's cardinality formula for the cyclic-TI set, regarded as a
subset of `W`. -/
theorem ncard_cyclicTISetInW
    (h : IsInternalDirectProductIn W₁ W₂ W) :
    (cyclicTISetInW W W₁ W₂).ncard =
      (Nat.card W₁ - 1) * (Nat.card W₂ - 1) := by
  rw [← h.image_nonidentity_prod]
  rw [Set.ncard_image_of_injective _ h.mulEquiv.injective, Set.ncard_prod]
  simp

/-- Peterfalvi's cardinality formula for the cyclic-TI set in the common
ambient group. -/
theorem ncard_cyclicTISet
    (h : IsInternalDirectProductIn W₁ W₂ W) :
    (cyclicTISet W W₁ W₂).ncard =
      (Nat.card W₁ - 1) * (Nat.card W₂ - 1) := by
  have hsubset :
      cyclicTISet W W₁ W₂ ⊆ Set.range (Subtype.val : W → Γ) := by
    intro x hx
    exact ⟨⟨x, (mem_cyclicTISet.mp hx).1⟩, rfl⟩
  calc
    (cyclicTISet W W₁ W₂).ncard =
        (cyclicTISetInW W W₁ W₂).ncard := by
      change (cyclicTISet W W₁ W₂).ncard =
        ((Subtype.val : W → Γ) ⁻¹' cyclicTISet W W₁ W₂).ncard
      exact
        (Set.ncard_preimage_of_injective_subset_range
          Subtype.val_injective hsubset).symm
    _ = (Nat.card W₁ - 1) * (Nat.card W₂ - 1) :=
      h.ncard_cyclicTISetInW

end IsInternalDirectProductIn

/-- The cyclic-TI set inside `W` is stable under inversion.  This uses only
that its excluded pieces are subgroups. -/
theorem cyclicTISetInW_invStable (W W₁ W₂ : Subgroup Γ) :
    IsInvStable (cyclicTISetInW W W₁ W₂) := by
  intro x
  rw [mem_cyclicTISetInW, mem_cyclicTISetInW]
  simp only [Subgroup.coe_inv, Subgroup.inv_mem_iff]

private theorem two_lt_of_odd_of_one_lt {n : ℕ}
    (hnodd : Odd n) (hone : 1 < n) : 2 < n := by
  obtain ⟨k, rfl⟩ := hnodd
  by_cases hk : k = 0
  · subst k
    simp at hone
  · have hkone : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    have htwo : 2 ≤ 2 * k := by
      simpa using Nat.mul_le_mul_left 2 hkone
    exact htwo.trans_lt (by simp)

namespace CyclicTIHypothesis

variable {G W W₁ W₂ : Subgroup Γ}
  {defW : IsInternalDirectProductIn W₁ W₂ W}

/-- The direct factors are cyclic and their orders are coprime.  This is the
finite-product criterion for cyclicity, transported across the canonical
internal direct-product equivalence. -/
theorem cyclic_factors_coprime
    (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    IsCyclic W₁ ∧ IsCyclic W₂ ∧
      Nat.Coprime (Nat.card W₁) (Nat.card W₂) :=
  Group.isCyclic_prod_iff.mp (defW.mulEquiv.isCyclic.mpr h.cyclic)

/-- The left direct factor is cyclic. -/
theorem left_cyclic (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    IsCyclic W₁ :=
  h.cyclic_factors_coprime.1

/-- The right direct factor is cyclic. -/
theorem right_cyclic (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    IsCyclic W₂ :=
  h.cyclic_factors_coprime.2.1

/-- The orders of the two direct factors are coprime. -/
theorem factor_card_coprime
    (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    Nat.Coprime (Nat.card W₁) (Nat.card W₂) :=
  h.cyclic_factors_coprime.2.2

/-- Nonemptiness of the normalized-TI set forces both direct factors to be
nontrivial. -/
theorem factors_nontrivial
    (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    Nontrivial W₁ ∧ Nontrivial W₂ := by
  obtain ⟨g, hg⟩ := h.set_nonempty
  let w : W := ⟨g, (mem_cyclicTISet.mp hg).1⟩
  have hw : w ∈ cyclicTISetInW W W₁ W₂ := by
    rw [mem_cyclicTISetInW]
    exact (mem_cyclicTISet.mp hg).2
  let x : W₁ × W₂ := defW.mulEquiv.symm w
  have hx : defW.mulEquiv x ∈ cyclicTISetInW W W₁ W₂ := by
    simpa [x] using hw
  rw [mem_cyclicTISetInW, defW.mulEquiv_mem_left_iff,
    defW.mulEquiv_mem_right_iff] at hx
  exact ⟨nontrivial_of_ne x.1 1 hx.2, nontrivial_of_ne x.2 1 hx.1⟩

/-- The left direct factor has odd order. -/
theorem left_odd_card (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    Odd (Nat.card W₁) :=
  Odd.of_dvd_nat h.odd_card (Subgroup.card_dvd_of_le defW.left_le)

/-- The right direct factor has odd order. -/
theorem right_odd_card (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    Odd (Nat.card W₂) :=
  Odd.of_dvd_nat h.odd_card (Subgroup.card_dvd_of_le defW.right_le)

/-- Odd order makes the internal direct product finite. -/
theorem group_finite (h : CyclicTIHypothesis G W W₁ W₂ defW) : Finite W :=
  Nat.finite_of_card_ne_zero h.odd_card.pos.ne'

/-- The left direct factor is finite. -/
theorem left_finite (h : CyclicTIHypothesis G W W₁ W₂ defW) : Finite W₁ :=
  Nat.finite_of_card_ne_zero h.left_odd_card.pos.ne'

/-- The right direct factor is finite. -/
theorem right_finite (h : CyclicTIHypothesis G W W₁ W₂ defW) : Finite W₂ :=
  Nat.finite_of_card_ne_zero h.right_odd_card.pos.ne'

/-- The left factor has order greater than one. -/
theorem one_lt_card_left (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    1 < Nat.card W₁ := by
  letI : Finite W₁ := h.left_finite
  exact Finite.one_lt_card_iff_nontrivial.mpr h.factors_nontrivial.1

/-- The right factor has order greater than one. -/
theorem one_lt_card_right (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    1 < Nat.card W₂ := by
  letI : Finite W₂ := h.right_finite
  exact Finite.one_lt_card_iff_nontrivial.mpr h.factors_nontrivial.2

/-- A nontrivial odd-order left factor has order greater than two. -/
theorem two_lt_card_left (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    2 < Nat.card W₁ :=
  two_lt_of_odd_of_one_lt h.left_odd_card h.one_lt_card_left

/-- A nontrivial odd-order right factor has order greater than two. -/
theorem two_lt_card_right (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    2 < Nat.card W₂ :=
  two_lt_of_odd_of_one_lt h.right_odd_card h.one_lt_card_right

/-- The coprime nontrivial direct factors have unequal orders. -/
theorem factor_card_ne (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    Nat.card W₁ ≠ Nat.card W₂ := by
  intro heq
  have hone : Nat.card W₂ = 1 := by
    have hcop := h.factor_card_coprime
    rw [heq] at hcop
    exact (Nat.coprime_self (Nat.card W₂)).mp hcop
  exact (Nat.ne_of_gt h.one_lt_card_right) hone

/-- Under the cyclic-TI hypothesis, the set inside `W` is stable under
conjugation.  Indeed, cyclicity makes conjugation in `W` trivial. -/
theorem set_conjStable (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    IsConjStable (cyclicTISetInW W W₁ W₂) := by
  letI : IsCyclic W := h.cyclic
  intro x g
  have hconj : x * g * x⁻¹ = g := by
    calc
      x * g * x⁻¹ = g * x * x⁻¹ := by rw [mul_comm' x g]
      _ = g := mul_inv_cancel_right g x
  rw [hconj]

/-- The inverse-stability fact packaged with a cyclic-TI hypothesis. -/
theorem set_invStable (_h : CyclicTIHypothesis G W W₁ W₂ defW) :
    IsInvStable (cyclicTISetInW W W₁ W₂) :=
  cyclicTISetInW_invStable W W₁ W₂

/-- The cyclic-TI set inside `W` is finite. -/
theorem set_inW_finite (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    (cyclicTISetInW W W₁ W₂).Finite := by
  letI : Finite W := h.group_finite
  exact Set.finite_univ.subset (Set.subset_univ _)

/-- The cyclic-TI set in the common ambient group is finite. -/
theorem set_finite (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    (cyclicTISet W W₁ W₂).Finite :=
  (Set.finite_coe_iff.mp h.group_finite).subset
    (cyclicTISet_subset W W₁ W₂)

end CyclicTIHypothesis

end

end Submission.OddOrder.PF
