import Submission.OddOrder.PF.Section03.CyclicTIIsometry

/-!
# Coefficient support of the cyclic-TI isometry

This file ports the elementary `cyclicTI_NC` API from Peterfalvi Section 3
(Coq `PFsection3.v`, lines 1524--1596).  The definition counts the nonzero
pairing coefficients of an ambient class function against the rectangular
orthonormal image of the irreducible characters of `W`.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped Classical

universe u

variable {Gamma k : Type u} [Group Gamma] [Fintype Gamma]
  [Field k] [IsAlgClosed k] [CharZero k]
  {G W W₁ W₂ : Subgroup Gamma}
  {defW : IsInternalDirectProductIn W₁ W₂ W}
  {h : CyclicTIHypothesis G W W₁ W₂ defW}

local instance cyclicTICoefficientSupportInvertibleCard
    {H : Type u} [Group H] [Fintype H] :
    Invertible (Nat.card H : k) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

namespace CyclicTIIsometryData

/-- A rectangular irreducible source character. -/
def cyclicTISourceIrreducible
    (p : IrreducibleCharacter W₁ k × IrreducibleCharacter W₂ k) :
    ClassFunction W k :=
  IrreducibleCharacter.cyclicTICharacter defW p.1 p.2

/-- Its image under a cyclic-TI isometry. -/
def cyclicTIImage
    (iso : CyclicTIIsometryData (k := k) h)
    (p : IrreducibleCharacter W₁ k × IrreducibleCharacter W₂ k) :
    ClassFunction G k :=
  iso.linearMap (cyclicTISourceIrreducible (defW := defW) p)

/-- The finite set of nonzero cyclic-TI coefficients of `phi`. -/
def cyclicTICoefficientSupport
    (iso : CyclicTIIsometryData (k := k) h)
    (phi : ClassFunction G k) :
    Finset (IrreducibleCharacter W₁ k × IrreducibleCharacter W₂ k) :=
  Finset.univ.filter fun p ↦
    characterPairing phi (iso.cyclicTIImage p) ≠ 0

/-- Peterfalvi's `NC`. -/
def cyclicTINC
    (iso : CyclicTIIsometryData (k := k) h)
    (phi : ClassFunction G k) : ℕ :=
  (iso.cyclicTICoefficientSupport phi).card

@[simp]
theorem mem_cyclicTICoefficientSupport
    (iso : CyclicTIIsometryData (k := k) h)
    (phi : ClassFunction G k)
    (p : IrreducibleCharacter W₁ k × IrreducibleCharacter W₂ k) :
    p ∈ iso.cyclicTICoefficientSupport phi ↔
      characterPairing phi (iso.cyclicTIImage p) ≠ 0 := by
  simp [cyclicTICoefficientSupport]

theorem characterPairing_cyclicTIImage
    (iso : CyclicTIIsometryData (k := k) h)
    (p q : IrreducibleCharacter W₁ k ×
      IrreducibleCharacter W₂ k) :
    characterPairing (iso.cyclicTIImage p) (iso.cyclicTIImage q) =
      if p = q then 1 else 0 := by
  rw [cyclicTIImage, cyclicTIImage, iso.pairing]
  by_cases hpq : p = q
  · subst q
    simp [cyclicTISourceIrreducible]
  · rw [if_neg hpq]
    apply IrreducibleCharacter.characterPairing_eq_zero
    exact (IrreducibleCharacter.cyclicTICharacter_injective defW).ne hpq

/-- Every member of the image rectangle is a signed irreducible character. -/
theorem cyclicTIImage_eq_signed_irreducible
    (iso : CyclicTIIsometryData (k := k) h)
    (p : IrreducibleCharacter W₁ k ×
      IrreducibleCharacter W₂ k) :
    ∃ (chi : IrreducibleCharacter G k) (epsilon : ℤ),
      IsSign epsilon ∧
      iso.cyclicTIImage p =
        (epsilon : k) • (chi : ClassFunction G k) := by
  simpa [cyclicTIImage, cyclicTISourceIrreducible] using
    iso.exists_signed_irreducible_image
      (IrreducibleCharacter.cyclicTICharacter defW p.1 p.2)

@[simp]
theorem cyclicTINC_zero
    (iso : CyclicTIIsometryData (k := k) h) :
    iso.cyclicTINC (0 : ClassFunction G k) = 0 := by
  simp [cyclicTINC, cyclicTICoefficientSupport]

@[simp]
theorem cyclicTINC_neg
    (iso : CyclicTIIsometryData (k := k) h)
    (phi : ClassFunction G k) :
    iso.cyclicTINC (-phi) = iso.cyclicTINC phi := by
  change (iso.cyclicTICoefficientSupport (-phi)).card =
    (iso.cyclicTICoefficientSupport phi).card
  congr 1
  apply Finset.ext
  intro p
  simp only [mem_cyclicTICoefficientSupport]
  rw [← neg_one_smul k phi, characterPairing_smul_left]
  simp

theorem cyclicTINC_smul_eq
    (iso : CyclicTIIsometryData (k := k) h)
    (a : k) (phi : ClassFunction G k) (ha : a ≠ 0) :
    iso.cyclicTINC (a • phi) = iso.cyclicTINC phi := by
  change (iso.cyclicTICoefficientSupport (a • phi)).card =
    (iso.cyclicTICoefficientSupport phi).card
  congr 1
  apply Finset.ext
  intro p
  simp only [mem_cyclicTICoefficientSupport]
  rw [characterPairing_smul_left]
  simp [ha]

theorem cyclicTINC_smul_le
    (iso : CyclicTIIsometryData (k := k) h)
    (a : k) (phi : ClassFunction G k) :
    iso.cyclicTINC (a • phi) ≤ iso.cyclicTINC phi := by
  by_cases ha : a = 0
  · subst a
    simp
  · exact (iso.cyclicTINC_smul_eq a phi ha).le

theorem cyclicTINC_add_le
    (iso : CyclicTIIsometryData (k := k) h)
    (phi psi : ClassFunction G k) :
    iso.cyclicTINC (phi + psi) ≤
      iso.cyclicTINC phi + iso.cyclicTINC psi := by
  have hsub : iso.cyclicTICoefficientSupport (phi + psi) ⊆
      iso.cyclicTICoefficientSupport phi ∪
        iso.cyclicTICoefficientSupport psi := by
    intro p hp
    simp only [mem_cyclicTICoefficientSupport] at hp
    rw [Finset.mem_union]
    by_contra hpnot
    simp only [not_or, mem_cyclicTICoefficientSupport,
      not_ne_iff] at hpnot
    apply hp
    rw [characterPairing_add_left, hpnot.1, hpnot.2, add_zero]
  calc
    iso.cyclicTINC (phi + psi) ≤
        (iso.cyclicTICoefficientSupport phi ∪
          iso.cyclicTICoefficientSupport psi).card :=
      Finset.card_le_card hsub
    _ ≤ iso.cyclicTINC phi + iso.cyclicTINC psi := by
      exact Finset.card_union_le
        (iso.cyclicTICoefficientSupport phi)
        (iso.cyclicTICoefficientSupport psi)

theorem cyclicTINC_sub_le
    (iso : CyclicTIIsometryData (k := k) h)
    (phi psi : ClassFunction G k) :
    iso.cyclicTINC (phi - psi) ≤
      iso.cyclicTINC phi + iso.cyclicTINC psi := by
  rw [sub_eq_add_neg]
  simpa using iso.cyclicTINC_add_le phi (-psi)

/-- A member of the orthonormal image rectangle has exactly one nonzero
coefficient. -/
@[simp]
theorem cyclicTINC_image
    (iso : CyclicTIIsometryData (k := k) h)
    (p : IrreducibleCharacter W₁ k ×
      IrreducibleCharacter W₂ k) :
    iso.cyclicTINC (iso.cyclicTIImage p) = 1 := by
  have hsupport :
      iso.cyclicTICoefficientSupport (iso.cyclicTIImage p) = {p} := by
    ext q
    simp [cyclicTICoefficientSupport,
      iso.characterPairing_cyclicTIImage, eq_comm]
  rw [cyclicTINC, hsupport]
  simp

/-- The support-count bound by the squared norm for an arbitrary virtual
character.  This is the integral-lattice form of Coq's `cycTI_NC_norm`. -/
theorem cyclicTINC_realize_le_normSq
    (iso : CyclicTIIsometryData (k := k) h)
    (z : VirtualCharacter G k) :
    (iso.cyclicTINC (VirtualCharacter.realize z) : ℤ) ≤ normSq z := by
  choose imageIndex imageSign himageSign himage using
    fun p : IrreducibleCharacter W₁ k ×
        IrreducibleCharacter W₂ k ↦
      iso.cyclicTIImage_eq_signed_irreducible p
  have hindexInjective : Function.Injective imageIndex := by
    intro p q hpq
    by_contra hpq'
    have hpair := iso.characterPairing_cyclicTIImage p q
    rw [himage p, himage q, hpq] at hpair
    rw [if_neg hpq'] at hpair
    have hpair' :
        (imageSign q : k) * (imageSign p : k) = 0 := by
      simpa only [characterPairing_smul_left,
        characterPairing_smul_right,
        IrreducibleCharacter.characterPairing_self,
        mul_one] using hpair
    have hpSign : (imageSign p : k) ≠ 0 :=
      Int.cast_ne_zero.mpr (isSign_ne_zero (himageSign p))
    have hqSign : (imageSign q : k) ≠ 0 :=
      Int.cast_ne_zero.mpr (isSign_ne_zero (himageSign q))
    exact (mul_ne_zero hqSign hpSign) hpair'
  have hsupportMap :
      (iso.cyclicTICoefficientSupport
          (VirtualCharacter.realize z)).image imageIndex ⊆ z.support := by
    intro chi hchi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hchi
    rw [mem_cyclicTICoefficientSupport, himage p,
      characterPairing_smul_right,
      characterPairing_comm,
      VirtualCharacter.characterPairing_irreducible_realize] at hp
    rw [Finsupp.mem_support_iff]
    intro hz
    apply hp
    simp [hz]
  have hcard :
      iso.cyclicTINC (VirtualCharacter.realize z) ≤ z.support.card := by
    rw [cyclicTINC,
      ← Finset.card_image_iff.mpr hindexInjective.injOn]
    exact Finset.card_le_card hsupportMap
  have hsupportNorm : (z.support.card : ℤ) ≤ normSq z := by
    rw [normSq_eq_sum]
    calc
      (z.support.card : ℤ) = ∑ _i ∈ z.support, (1 : ℤ) := by simp
      _ ≤ ∑ i ∈ z.support, z i ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hzi : z i ≠ 0 := Finsupp.mem_support_iff.mp hi
        nlinarith [sq_pos_of_ne_zero hzi]
  exact (Int.ofNat_le.mpr hcard).trans hsupportNorm

/-- An ambient irreducible character has at most one nonzero cyclic-TI
coefficient. -/
theorem cyclicTINC_irreducible_le_one
    (iso : CyclicTIIsometryData (k := k) h)
    (chi : IrreducibleCharacter G k) :
    iso.cyclicTINC (chi : ClassFunction G k) ≤ 1 := by
  have hbound := iso.cyclicTINC_realize_le_normSq
    (Finsupp.single chi 1 : VirtualCharacter G k)
  have hbound' :
      (iso.cyclicTINC (chi : ClassFunction G k) : ℤ) ≤ (1 : ℤ) := by
    simpa [normSq] using hbound
  exact Int.ofNat_le.mp hbound'

/-- The same bound for a signed irreducible character. -/
theorem cyclicTINC_signedIrreducible_smul_le_one
    (iso : CyclicTIIsometryData (k := k) h)
    (chi : IrreducibleCharacter G k) (epsilon : ℤ)
    (hepsilon : IsSign epsilon) :
    iso.cyclicTINC
        ((epsilon : k) • (chi : ClassFunction G k)) ≤ 1 := by
  rw [iso.cyclicTINC_smul_eq]
  · exact iso.cyclicTINC_irreducible_le_one chi
  · exact Int.cast_ne_zero.mpr (isSign_ne_zero hepsilon)

/-- Predicate-style form matching Coq's `cycTI_NC_dirr`. -/
theorem cyclicTINC_signedIrreducible_le_one
    (iso : CyclicTIIsometryData (k := k) h)
    (phi : ClassFunction G k)
    (hphi : ∃ (chi : IrreducibleCharacter G k) (epsilon : ℤ),
      IsSign epsilon ∧
      phi = (epsilon : k) • (chi : ClassFunction G k)) :
    iso.cyclicTINC phi ≤ 1 := by
  obtain ⟨chi, epsilon, hepsilon, rfl⟩ := hphi
  exact iso.cyclicTINC_signedIrreducible_smul_le_one
    chi epsilon hepsilon

end CyclicTIIsometryData

end

end Submission.OddOrder.PF
