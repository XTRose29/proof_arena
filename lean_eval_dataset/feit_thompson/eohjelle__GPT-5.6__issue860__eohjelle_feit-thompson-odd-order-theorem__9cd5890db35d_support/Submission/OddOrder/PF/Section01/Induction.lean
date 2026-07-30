import Submission.OddOrder.PF.Section01.ClassFunction

/-!
Induction of class functions from a subgroup.

The definition is the usual finite-group formula.  It is developed directly
at the level of bundled class functions so that the Peterfalvi port can use
induction independently of a particular realization by representations.
-/

namespace Submission.OddOrder.PF

noncomputable section

universe u v

namespace ClassFunction

variable {G : Type u} {k : Type v} [Group G] [Field k] [Fintype G]

/-- The summand in the induction formula, extended by zero when the conjugate
does not lie in the subgroup. -/
def inductionKernel (H : Subgroup G) (f : ClassFunction H k) (x g : G) : k := by
  classical
  exact if hx : x⁻¹ * g * x ∈ H then f ⟨x⁻¹ * g * x, hx⟩ else 0

omit [Fintype G] in
theorem inductionKernel_of_mem (H : Subgroup G) (f : ClassFunction H k)
    (x g : G) (hx : x⁻¹ * g * x ∈ H) :
    inductionKernel H f x g = f ⟨x⁻¹ * g * x, hx⟩ := by
  simp [inductionKernel, hx]

omit [Fintype G] in
theorem inductionKernel_of_notMem (H : Subgroup G) (f : ClassFunction H k)
    (x g : G) (hx : x⁻¹ * g * x ∉ H) :
    inductionKernel H f x g = 0 := by
  simp [inductionKernel, hx]

/-- The value at `g` of the class function induced from `H`. -/
def inductionValue (H : Subgroup G) (f : ClassFunction H k) (g : G) : k := by
  exact (Nat.card H : k)⁻¹ * ∑ x : G, inductionKernel H f x g

/-- Reindexing the defining sum by left multiplication proves that an induced
function is constant on conjugacy classes. -/
theorem inductionValue_conj (H : Subgroup G) (f : ClassFunction H k) (y g : G) :
    inductionValue H f (y * g * y⁻¹) = inductionValue H f g := by
  classical
  unfold inductionValue
  congr 1
  symm
  refine Fintype.sum_equiv (Equiv.mulLeft y) _ _ fun x ↦ ?_
  simp [inductionKernel, mul_assoc]

/-- Induction of class functions along a subgroup inclusion. -/
def induce (H : Subgroup G) : ClassFunction H k →ₗ[k] ClassFunction G k where
  toFun f := ⟨inductionValue H f, inductionValue_conj H f⟩
  map_add' f₁ f₂ := by
    ext g
    classical
    simp only [inductionValue, add_apply]
    rw [← mul_add, ← Finset.sum_add_distrib]
    apply congrArg ((Nat.card H : k)⁻¹ * ·)
    apply Finset.sum_congr rfl
    intro x _
    unfold inductionKernel
    split_ifs <;> simp
  map_smul' a f := by
    ext g
    classical
    simp [inductionValue, inductionKernel, Finset.mul_sum, mul_left_comm, mul_assoc]

@[simp]
theorem induce_apply (H : Subgroup G) (f : ClassFunction H k) (g : G) :
    induce H f g = inductionValue H f g :=
  rfl

open scoped Classical in
/-- The standard pointwise finite-sum formula for induction. -/
theorem induce_apply_formula (H : Subgroup G) (f : ClassFunction H k) (g : G) :
    induce H f g =
      (Nat.card H : k)⁻¹ *
        ∑ x : G, if hx : x⁻¹ * g * x ∈ H then f ⟨x⁻¹ * g * x, hx⟩ else 0 := by
  rfl

@[simp]
theorem induce_zero_apply (H : Subgroup G) (g : G) :
    induce H (0 : ClassFunction H k) g = 0 := by
  simp

@[simp]
theorem induce_add_apply (H : Subgroup G) (f₁ f₂ : ClassFunction H k) (g : G) :
    induce H (f₁ + f₂) g = induce H f₁ g + induce H f₂ g := by
  simp

@[simp]
theorem induce_smul_apply (H : Subgroup G) (a : k)
    (f : ClassFunction H k) (g : G) :
    induce H (a • f) g = a • induce H f g := by
  simp

/-- Reindex a sum over the ambient group by conjugation and then discard the
terms outside `H`.  Class-invariance makes the resulting sum independent of
the conjugating element. -/
theorem sum_inductionKernel_mul (H : Subgroup G) [Fintype H]
    (f : ClassFunction H k)
    (g : ClassFunction G k) (x : G) :
    (∑ y : G, inductionKernel H f x y * g y⁻¹) =
      ∑ h : H, f h * g (h : G)⁻¹ := by
  classical
  let ambientSummand : G → k := fun y ↦ inductionKernel H f x y * g y⁻¹
  let subgroupIndicator : G → k := fun y ↦
    if hy : y ∈ H then f ⟨y, hy⟩ * g y⁻¹ else 0
  have h_reindex :
      (∑ y : G, ambientSummand y) = ∑ y : G, subgroupIndicator y := by
    symm
    refine Fintype.sum_equiv (MulAut.conj x).toEquiv subgroupIndicator
      ambientSummand fun y ↦ ?_
    have hg : g (x * (y⁻¹ * x⁻¹)) = g y⁻¹ := by
      simpa only [mul_assoc] using conj_apply g x y⁻¹
    simp [subgroupIndicator, ambientSummand, inductionKernel, mul_assoc, hg]
  rw [h_reindex]
  have h_indicator :=
    Finset.sum_congr_set (H : Set G) subgroupIndicator
      (fun h : (H : Set G) ↦ f ⟨h, h.property⟩ * g (h : G)⁻¹)
      (by
        intro y hy
        change y ∈ H at hy
        unfold subgroupIndicator
        rw [dif_pos hy])
      (by
        intro y hy
        change y ∉ H at hy
        unfold subgroupIndicator
        rw [dif_neg hy])
  rw [h_indicator]
  apply Finset.sum_congr
  · ext h
    simp
  · intro h _
    rfl

/-- Frobenius reciprocity for the normalized character pairing. -/
theorem frobeniusReciprocity (H : Subgroup G) [Fintype H] [CharZero k]
    (f : ClassFunction H k) (g : ClassFunction G k) :
    characterPairing (induce H f) g =
      characterPairing f (restrict H g) := by
  classical
  have hcardG : (Nat.card G : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have h_expand :
      (∑ y : G,
          ((Nat.card H : k)⁻¹ * ∑ x : G, inductionKernel H f x y) * g y⁻¹) =
        (Nat.card H : k)⁻¹ *
          ∑ x : G, ∑ y : G, inductionKernel H f x y * g y⁻¹ := by
    calc
      (∑ y : G,
          ((Nat.card H : k)⁻¹ * ∑ x : G, inductionKernel H f x y) * g y⁻¹) =
          ∑ y : G, (Nat.card H : k)⁻¹ *
            ∑ x : G, inductionKernel H f x y * g y⁻¹ := by
              apply Fintype.sum_congr
              intro y
              rw [mul_assoc, Finset.sum_mul]
      _ = (Nat.card H : k)⁻¹ *
          ∑ y : G, ∑ x : G, inductionKernel H f x y * g y⁻¹ := by
            rw [Finset.mul_sum]
      _ = (Nat.card H : k)⁻¹ *
          ∑ x : G, ∑ y : G, inductionKernel H f x y * g y⁻¹ := by
            rw [Finset.sum_comm]
  simp only [characterPairing, induce_apply, inductionValue, restrict_apply,
    Subgroup.coe_inv]
  rw [h_expand]
  calc
    (Nat.card G : k)⁻¹ *
        ((Nat.card H : k)⁻¹ *
          ∑ x : G, ∑ y : G, inductionKernel H f x y * g y⁻¹) =
        (Nat.card G : k)⁻¹ * (Nat.card H : k)⁻¹ *
          ∑ x : G, ∑ y : G, inductionKernel H f x y * g y⁻¹ := by
            ring
    _ = (Nat.card G : k)⁻¹ * (Nat.card H : k)⁻¹ *
        ∑ x : G, ∑ h : H, f h * g (h : G)⁻¹ := by
          congr 1
          apply Fintype.sum_congr
          intro x
          exact sum_inductionKernel_mul H f g x
    _ = (Nat.card G : k)⁻¹ * (Nat.card H : k)⁻¹ *
        ((Nat.card G : k) * ∑ h : H, f h * g (h : G)⁻¹) := by
          congr 1
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
            ← Nat.card_eq_fintype_card]
    _ = (Nat.card H : k)⁻¹ *
        ((Nat.card G : k)⁻¹ * (Nat.card G : k)) *
          ∑ h : H, f h * g (h : G)⁻¹ := by
            ring
    _ = (Nat.card H : k)⁻¹ * ∑ h : H, f h * g (h : G)⁻¹ := by
          rw [inv_mul_cancel₀ hcardG, mul_one]

end ClassFunction

end

end Submission.OddOrder.PF
