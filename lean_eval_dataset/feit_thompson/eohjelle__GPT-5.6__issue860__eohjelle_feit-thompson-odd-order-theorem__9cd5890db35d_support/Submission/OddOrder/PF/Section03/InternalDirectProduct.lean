import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Submission.OddOrder.MathlibSupport.NormalizedTI

/-!
# Internal direct products for Peterfalvi Section 3

This file records the group-side data used in the cyclic-TI construction.
The two factors are fixed subgroups of a common ambient group, and the
decomposition hypothesis is proposition-valued.  In particular, later
constructions may depend on a proof of the decomposition without turning the
decomposition itself into additional data.
-/

namespace Submission.OddOrder.PF

noncomputable section

universe u

variable {Γ : Type u} [Group Γ]

/-- The fixed subgroups `W₁` and `W₂` form an internal direct product `W`.

Complementarity gives unique factorization inside `W`, while `commute` makes
the multiplication map from `W₁ × W₂` a group homomorphism.  Keeping this
structure in `Prop` is important: different proofs of the same fixed-subgroup
decomposition are proof-irrelevant. -/
structure IsInternalDirectProductIn
    (W₁ W₂ W : Subgroup Γ) : Prop where
  left_le : W₁ ≤ W
  right_le : W₂ ≤ W
  complement : (W₁.subgroupOf W).IsComplement' (W₂.subgroupOf W)
  commute : ∀ x : W₁, ∀ y : W₂, Commute (x : Γ) (y : Γ)

namespace IsInternalDirectProductIn

variable {W₁ W₂ W : Subgroup Γ}

/-- Multiplication of the two fixed factors, regarded as a homomorphism into
their internal direct product. -/
def mulHom (h : IsInternalDirectProductIn W₁ W₂ W) : W₁ × W₂ →* W where
  toFun x :=
    ⟨(x.1 : Γ) * (x.2 : Γ),
      W.mul_mem (h.left_le x.1.property) (h.right_le x.2.property)⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    change ((x.1 : Γ) * (y.1 : Γ)) * ((x.2 : Γ) * (y.2 : Γ)) =
      ((x.1 : Γ) * (x.2 : Γ)) * ((y.1 : Γ) * (y.2 : Γ))
    symm
    calc
      ((x.1 : Γ) * (x.2 : Γ)) * ((y.1 : Γ) * (y.2 : Γ)) =
          (x.1 : Γ) * ((x.2 : Γ) * (y.1 : Γ)) * (y.2 : Γ) := by
            simp only [mul_assoc]
      _ = (x.1 : Γ) * ((y.1 : Γ) * (x.2 : Γ)) * (y.2 : Γ) := by
            rw [(h.commute y.1 x.2).eq.symm]
      _ = ((x.1 : Γ) * (y.1 : Γ)) * ((x.2 : Γ) * (y.2 : Γ)) := by
            simp only [mul_assoc]

@[simp]
theorem coe_mulHom_apply (h : IsInternalDirectProductIn W₁ W₂ W)
    (x : W₁ × W₂) :
    ((h.mulHom x : W) : Γ) = (x.1 : Γ) * (x.2 : Γ) :=
  rfl

/-- The canonical multiplicative equivalence supplied by unique
factorization in the two commuting factors. -/
noncomputable def mulEquiv (h : IsInternalDirectProductIn W₁ W₂ W) :
    W₁ × W₂ ≃* W := by
  let A : Subgroup W := W₁.subgroupOf W
  let B : Subgroup W := W₂.subgroupOf W
  let e : W₁ × W₂ ≃* A × B :=
    (Subgroup.subgroupOfEquivOfLe h.left_le).symm.prodCongr
      (Subgroup.subgroupOfEquivOfLe h.right_le).symm
  refine MulEquiv.ofBijective h.mulHom ?_
  have hcomplement :
      Function.Bijective (fun x : A × B => (x.1 : W) * (x.2 : W)) :=
    (Subgroup.isComplement_iff_bijective A B).mp h.complement
  have hfun :
      (h.mulHom : W₁ × W₂ → W) =
        (fun x : A × B => (x.1 : W) * (x.2 : W)) ∘ e := by
    funext x
    apply Subtype.ext
    rfl
  rw [hfun]
  exact hcomplement.comp e.bijective

@[simp]
theorem coe_mulEquiv_apply (h : IsInternalDirectProductIn W₁ W₂ W)
    (x : W₁ × W₂) :
    ((h.mulEquiv x : W) : Γ) = (x.1 : Γ) * (x.2 : Γ) :=
  rfl

/-- The canonical inclusion of the left factor into `W`. -/
def leftEmbedding (h : IsInternalDirectProductIn W₁ W₂ W) : W₁ →* W where
  toFun x := ⟨x, h.left_le x.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The canonical inclusion of the right factor into `W`. -/
def rightEmbedding (h : IsInternalDirectProductIn W₁ W₂ W) : W₂ →* W where
  toFun x := ⟨x, h.right_le x.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem coe_leftEmbedding_apply (h : IsInternalDirectProductIn W₁ W₂ W)
    (x : W₁) : ((h.leftEmbedding x : W) : Γ) = x :=
  rfl

@[simp]
theorem coe_rightEmbedding_apply (h : IsInternalDirectProductIn W₁ W₂ W)
    (y : W₂) : ((h.rightEmbedding y : W) : Γ) = y :=
  rfl

@[simp]
theorem mulEquiv_apply_left (h : IsInternalDirectProductIn W₁ W₂ W)
    (x : W₁) : h.mulEquiv (x, 1) = h.leftEmbedding x := by
  apply Subtype.ext
  simp

@[simp]
theorem mulEquiv_apply_right (h : IsInternalDirectProductIn W₁ W₂ W)
    (y : W₂) : h.mulEquiv (1, y) = h.rightEmbedding y := by
  apply Subtype.ext
  simp

/-- Projection onto the left direct factor. -/
noncomputable def leftProjection
    (h : IsInternalDirectProductIn W₁ W₂ W) : W →* W₁ :=
  (MonoidHom.fst W₁ W₂).comp h.mulEquiv.symm.toMonoidHom

/-- Projection onto the right direct factor. -/
noncomputable def rightProjection
    (h : IsInternalDirectProductIn W₁ W₂ W) : W →* W₂ :=
  (MonoidHom.snd W₁ W₂).comp h.mulEquiv.symm.toMonoidHom

@[simp]
theorem leftProjection_mulEquiv
    (h : IsInternalDirectProductIn W₁ W₂ W) (x : W₁ × W₂) :
    h.leftProjection (h.mulEquiv x) = x.1 := by
  simp [leftProjection]

@[simp]
theorem rightProjection_mulEquiv
    (h : IsInternalDirectProductIn W₁ W₂ W) (x : W₁ × W₂) :
    h.rightProjection (h.mulEquiv x) = x.2 := by
  simp [rightProjection]

@[simp]
theorem leftProjection_leftEmbedding
    (h : IsInternalDirectProductIn W₁ W₂ W) (x : W₁) :
    h.leftProjection (h.leftEmbedding x) = x := by
  calc
    h.leftProjection (h.leftEmbedding x) =
        h.leftProjection (h.mulEquiv (x, 1)) := by
          rw [h.mulEquiv_apply_left]
    _ = x := h.leftProjection_mulEquiv (x, 1)

@[simp]
theorem rightProjection_rightEmbedding
    (h : IsInternalDirectProductIn W₁ W₂ W) (y : W₂) :
    h.rightProjection (h.rightEmbedding y) = y := by
  calc
    h.rightProjection (h.rightEmbedding y) =
        h.rightProjection (h.mulEquiv (1, y)) := by
          rw [h.mulEquiv_apply_right]
    _ = y := h.rightProjection_mulEquiv (1, y)

@[simp]
theorem leftProjection_rightEmbedding
    (h : IsInternalDirectProductIn W₁ W₂ W) (y : W₂) :
    h.leftProjection (h.rightEmbedding y) = 1 := by
  calc
    h.leftProjection (h.rightEmbedding y) =
        h.leftProjection (h.mulEquiv (1, y)) := by
          rw [h.mulEquiv_apply_right]
    _ = 1 := h.leftProjection_mulEquiv (1, y)

@[simp]
theorem rightProjection_leftEmbedding
    (h : IsInternalDirectProductIn W₁ W₂ W) (x : W₁) :
    h.rightProjection (h.leftEmbedding x) = 1 := by
  calc
    h.rightProjection (h.leftEmbedding x) =
        h.rightProjection (h.mulEquiv (x, 1)) := by
          rw [h.mulEquiv_apply_left]
    _ = 1 := h.rightProjection_mulEquiv (x, 1)

@[simp]
theorem mulEquiv_projections
    (h : IsInternalDirectProductIn W₁ W₂ W) (w : W) :
    h.mulEquiv (h.leftProjection w, h.rightProjection w) = w := by
  change h.mulEquiv ((h.mulEquiv.symm w).1, (h.mulEquiv.symm w).2) = w
  exact h.mulEquiv.apply_symm_apply w

/-- Interchanging the two factors preserves the internal direct-product
hypothesis. -/
theorem swap (h : IsInternalDirectProductIn W₁ W₂ W) :
    IsInternalDirectProductIn W₂ W₁ W where
  left_le := h.right_le
  right_le := h.left_le
  complement := h.complement.symm
  commute y x := (h.commute x y).symm

@[simp]
theorem swap_swap (h : IsInternalDirectProductIn W₁ W₂ W) :
    h.swap.swap = h :=
  Subsingleton.elim _ _

@[simp]
theorem swap_mulEquiv_apply (h : IsInternalDirectProductIn W₁ W₂ W)
    (x : W₂ × W₁) :
    h.swap.mulEquiv x = h.mulEquiv (x.2, x.1) := by
  apply Subtype.ext
  exact (h.commute x.2 x.1).eq.symm

end IsInternalDirectProductIn

/-- The cyclic-TI set `W \ (W₁ ∪ W₂)` in the common ambient group. -/
def cyclicTISet (W W₁ W₂ : Subgroup Γ) : Set Γ :=
  (W : Set Γ) \ ((W₁ : Set Γ) ∪ (W₂ : Set Γ))

@[simp]
theorem mem_cyclicTISet {W W₁ W₂ : Subgroup Γ} {x : Γ} :
    x ∈ cyclicTISet W W₁ W₂ ↔ x ∈ W ∧ x ∉ W₁ ∧ x ∉ W₂ := by
  simp [cyclicTISet]

theorem cyclicTISet_subset (W W₁ W₂ : Subgroup Γ) :
    cyclicTISet W W₁ W₂ ⊆ (W : Set Γ) := by
  intro x hx
  exact (mem_cyclicTISet.mp hx).1

@[simp]
theorem one_not_mem_cyclicTISet (W W₁ W₂ : Subgroup Γ) :
    (1 : Γ) ∉ cyclicTISet W W₁ W₂ := by
  simp

theorem cyclicTISet_subset_diff_one (W W₁ W₂ : Subgroup Γ) :
    cyclicTISet W W₁ W₂ ⊆ (W : Set Γ) \ {(1 : Γ)} := by
  intro x hx
  exact ⟨(mem_cyclicTISet.mp hx).1, fun hx1 => by
    subst x
    exact one_not_mem_cyclicTISet W W₁ W₂ hx⟩

@[simp]
theorem cyclicTISet_swap (W W₁ W₂ : Subgroup Γ) :
    cyclicTISet W W₂ W₁ = cyclicTISet W W₁ W₂ := by
  ext x
  rw [mem_cyclicTISet, mem_cyclicTISet]
  constructor
  · rintro ⟨hxW, hxW₂, hxW₁⟩
    exact ⟨hxW, hxW₁, hxW₂⟩
  · rintro ⟨hxW, hxW₁, hxW₂⟩
    exact ⟨hxW, hxW₂, hxW₁⟩

/-- The cyclic-TI set regarded as a subset of the subgroup `W`, which is the
form used for supports of class functions on `W`. -/
def cyclicTISetInW (W W₁ W₂ : Subgroup Γ) : Set W :=
  Subtype.val ⁻¹' cyclicTISet W W₁ W₂

@[simp]
theorem mem_cyclicTISetInW {W W₁ W₂ : Subgroup Γ} {x : W} :
    x ∈ cyclicTISetInW W W₁ W₂ ↔
      (x : Γ) ∉ W₁ ∧ (x : Γ) ∉ W₂ := by
  simp [cyclicTISetInW]

@[simp]
theorem cyclicTISetInW_swap (W W₁ W₂ : Subgroup Γ) :
    cyclicTISetInW W W₂ W₁ = cyclicTISetInW W W₁ W₂ := by
  simp [cyclicTISetInW]

/-- The group-theoretic cyclic-TI hypothesis from Peterfalvi Section 3. -/
structure CyclicTIHypothesis (G W W₁ W₂ : Subgroup Γ)
    (defW : IsInternalDirectProductIn W₁ W₂ W) : Prop where
  cyclic : IsCyclic W
  odd_card : Odd (Nat.card W)
  normedTI :
    Submission.OddOrder.MathlibSupport.IsNormalizedTI
      (cyclicTISet W W₁ W₂) G W

namespace CyclicTIHypothesis

variable {G W W₁ W₂ : Subgroup Γ}
  {defW : IsInternalDirectProductIn W₁ W₂ W}

/-- The relative normalizer `W` lies in `G`. -/
theorem le_group (h : CyclicTIHypothesis G W W₁ W₂ defW) : W ≤ G :=
  fun _ hx => (h.normedTI.2.1 hx).1

/-- The cyclic-TI set is nonempty. -/
theorem set_nonempty (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    (cyclicTISet W W₁ W₂).Nonempty :=
  h.normedTI.1

/-- Swap the two fixed direct factors in a cyclic-TI hypothesis. -/
theorem swap (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    CyclicTIHypothesis G W W₂ W₁ defW.swap where
  cyclic := h.cyclic
  odd_card := h.odd_card
  normedTI := by
    simpa using h.normedTI

end CyclicTIHypothesis

end

end Submission.OddOrder.PF
