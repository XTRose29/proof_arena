import Submission.OddOrder.PF.Section01.ClassFunctionSupport

/-!
# Twisted class-function pairings

This file supplies the value-conjugating pairing convention used by the Coq
odd-order development.  A generic coefficient endomorphism gives the twisted
pairing; specializing it to the star involution recovers Coq's `cfdot`.
-/

namespace Submission.OddOrder.PF

noncomputable section

universe u v

variable {G : Type u} {k : Type v} [Group G] [Field k] [Fintype G]

/-- Pair class functions after applying a coefficient endomorphism to the
right-hand values. -/
def twistedCharacterPairing (σ : k →+* k)
    (f g : ClassFunction G k) : k :=
  (Nat.card G : k)⁻¹ * ∑ x : G, f x * σ (g x)

@[simp]
theorem twistedCharacterPairing_zero_left (σ : k →+* k)
    (g : ClassFunction G k) :
    twistedCharacterPairing σ 0 g = 0 := by
  simp [twistedCharacterPairing]

@[simp]
theorem twistedCharacterPairing_zero_right (σ : k →+* k)
    (f : ClassFunction G k) :
    twistedCharacterPairing σ f 0 = 0 := by
  simp [twistedCharacterPairing]

@[simp]
theorem twistedCharacterPairing_add_left (σ : k →+* k)
    (f₁ f₂ g : ClassFunction G k) :
    twistedCharacterPairing σ (f₁ + f₂) g =
      twistedCharacterPairing σ f₁ g + twistedCharacterPairing σ f₂ g := by
  simp [twistedCharacterPairing, add_mul, Finset.sum_add_distrib, mul_add]

@[simp]
theorem twistedCharacterPairing_add_right (σ : k →+* k)
    (f g₁ g₂ : ClassFunction G k) :
    twistedCharacterPairing σ f (g₁ + g₂) =
      twistedCharacterPairing σ f g₁ + twistedCharacterPairing σ f g₂ := by
  simp [twistedCharacterPairing, mul_add, Finset.sum_add_distrib]

@[simp]
theorem twistedCharacterPairing_smul_left (σ : k →+* k)
    (a : k) (f g : ClassFunction G k) :
    twistedCharacterPairing σ (a • f) g =
      a * twistedCharacterPairing σ f g := by
  simp [twistedCharacterPairing, Finset.mul_sum, mul_assoc, mul_left_comm]

@[simp]
theorem twistedCharacterPairing_smul_right (σ : k →+* k)
    (a : k) (f g : ClassFunction G k) :
    twistedCharacterPairing σ f (a • g) =
      σ a * twistedCharacterPairing σ f g := by
  simp [twistedCharacterPairing, Finset.mul_sum, mul_left_comm]

/-- The Coq `cfdot` convention, using coefficient star on the right. -/
def starCharacterPairing [StarRing k]
    (f g : ClassFunction G k) : k :=
  twistedCharacterPairing (starRingEnd k) f g

@[simp]
theorem starCharacterPairing_zero_left [StarRing k]
    (g : ClassFunction G k) :
    starCharacterPairing 0 g = 0 :=
  twistedCharacterPairing_zero_left (starRingEnd k) g

@[simp]
theorem starCharacterPairing_zero_right [StarRing k]
    (f : ClassFunction G k) :
    starCharacterPairing f 0 = 0 :=
  twistedCharacterPairing_zero_right (starRingEnd k) f

@[simp]
theorem starCharacterPairing_add_left [StarRing k]
    (f₁ f₂ g : ClassFunction G k) :
    starCharacterPairing (f₁ + f₂) g =
      starCharacterPairing f₁ g + starCharacterPairing f₂ g :=
  twistedCharacterPairing_add_left (starRingEnd k) f₁ f₂ g

@[simp]
theorem starCharacterPairing_add_right [StarRing k]
    (f g₁ g₂ : ClassFunction G k) :
    starCharacterPairing f (g₁ + g₂) =
      starCharacterPairing f g₁ + starCharacterPairing f g₂ :=
  twistedCharacterPairing_add_right (starRingEnd k) f g₁ g₂

@[simp]
theorem starCharacterPairing_smul_left [StarRing k]
    (a : k) (f g : ClassFunction G k) :
    starCharacterPairing (a • f) g =
      a * starCharacterPairing f g :=
  twistedCharacterPairing_smul_left (starRingEnd k) a f g

@[simp]
theorem starCharacterPairing_smul_right [StarRing k]
    (a : k) (f g : ClassFunction G k) :
    starCharacterPairing f (a • g) =
      star a * starCharacterPairing f g :=
  twistedCharacterPairing_smul_right (starRingEnd k) a f g

/-- Conjugate symmetry of the star pairing. -/
theorem starCharacterPairing_conj_symm [StarRing k]
    (f g : ClassFunction G k) :
    starCharacterPairing f g = star (starCharacterPairing g f) := by
  simp only [starCharacterPairing, twistedCharacterPairing]
  rw [star_mul, star_inv₀, star_natCast, star_sum, mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [star_mul, starRingEnd_apply, starRingEnd_apply, star_star, mul_comm]

open scoped Classical in
/-- Restrict the defining sum to a support of the left function. -/
theorem twistedCharacterPairing_eq_sum_of_mem_supportedOn
    (σ : k →+* k) {A : Set G} {f g : ClassFunction G k}
    (hf : f ∈ ClassFunction.supportedOn A) :
    twistedCharacterPairing σ f g = (Nat.card G : k)⁻¹ *
      ∑ x ∈ Finset.univ.filter (fun x : G ↦ x ∈ A), f x * σ (g x) := by
  unfold twistedCharacterPairing
  congr 1
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro x _ hx
  have hxA : x ∉ A := by
    simpa using hx
  rw [ClassFunction.eq_zero_of_mem_supportedOn hf hxA, zero_mul]

open scoped Classical in
/-- Star specialization of the support-restricted sum. -/
theorem starCharacterPairing_eq_sum_of_mem_supportedOn [StarRing k]
    {A : Set G} {f g : ClassFunction G k}
    (hf : f ∈ ClassFunction.supportedOn A) :
    starCharacterPairing f g = (Nat.card G : k)⁻¹ *
      ∑ x ∈ Finset.univ.filter (fun x : G ↦ x ∈ A), f x * star (g x) := by
  exact twistedCharacterPairing_eq_sum_of_mem_supportedOn (starRingEnd k) hf

/-- The twisted pairing agrees with the inverse-argument pairing when the
coefficient endomorphism realizes inversion on the right-hand function. -/
theorem twistedCharacterPairing_eq_characterPairing_of_map_apply_eq_inv
    (σ : k →+* k) (f g : ClassFunction G k)
    (hg : ∀ x : G, σ (g x) = g x⁻¹) :
    twistedCharacterPairing σ f g = characterPairing f g := by
  unfold twistedCharacterPairing characterPairing
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [hg]

/-- The star pairing agrees with the inverse-argument pairing when coefficient
star realizes inversion on the right-hand function. -/
theorem starCharacterPairing_eq_characterPairing_of_star_apply_eq_inv
    [StarRing k] (f g : ClassFunction G k)
    (hg : ∀ x : G, star (g x) = g x⁻¹) :
    starCharacterPairing f g = characterPairing f g := by
  exact twistedCharacterPairing_eq_characterPairing_of_map_apply_eq_inv
    (starRingEnd k) f g hg

end

end Submission.OddOrder.PF
