import Submission.OddOrder.PF.Section03.CyclicTISmallSupport

/-!
# Cyclic-TI signed-difference rigidity

This file ports `eq_signed_sub_cTIiso` from `PFsection3.v`, lines
1680--1747.  The theorem is the consequence of Peterfalvi (3.8) used later
in (4.8), (10.5), (10.10), and (11.8): a norm-two virtual character which
agrees on the cyclic-TI set with a signed difference of two entries in one
row of the cyclic-TI isometry is that difference everywhere.

The private lemmas below keep the integral coefficient calculation separate
from the small-support argument supplied by `CyclicTISmallSupport`.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped Classical

universe u

variable {Gamma k : Type u} [Group Gamma] [Fintype Gamma]
  [Field k] [IsAlgClosed k] [CharZero k]
  {G W W₁ W₂ : Subgroup Gamma}
  {defW : IsInternalDirectProductIn W₁ W₂ W}

local instance cyclicTISignedDifferenceInvertibleCard
    {H : Type u} [Group H] [Fintype H] :
    Invertible (Nat.card H : k) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

namespace CyclicTIIsometryData

variable {h : CyclicTIHypothesis G W W₁ W₂ defW}
  (iso : CyclicTIIsometryData (k := k) h)

private theorem normSq_add
    {iota : Type*} (x y : IntegralLattice iota) :
    normSq (x + y) =
      normSq x + normSq y + 2 * coeffDot x y := by
  simp only [normSq, coeffDot_add_left, coeffDot_add_right]
  rw [coeffDot_comm y x]
  ring

/-- The integral image underlying `cyclicTIImage`. -/
private def cyclicTIImageVirtual
    (p : IrreducibleCharacter W₁ k × IrreducibleCharacter W₂ k) :
    VirtualCharacter G k :=
  iso.virtualMap
    (Finsupp.single
      (IrreducibleCharacter.cyclicTICharacter defW p.1 p.2) 1)

@[simp]
private theorem realize_cyclicTIImageVirtual
    (p : IrreducibleCharacter W₁ k × IrreducibleCharacter W₂ k) :
    VirtualCharacter.realize (iso.cyclicTIImageVirtual p) =
      iso.cyclicTIImage p := by
  simp [cyclicTIImageVirtual, iso.realize_virtualMap,
    VirtualCharacter.realize_single, cyclicTIImage,
    cyclicTISourceIrreducible]

/-- The integral cyclic-TI images are an orthonormal family. -/
private theorem coeffDot_cyclicTIImageVirtual
    (p q : IrreducibleCharacter W₁ k ×
      IrreducibleCharacter W₂ k) :
    coeffDot (iso.cyclicTIImageVirtual p)
        (iso.cyclicTIImageVirtual q) =
      if p = q then 1 else 0 := by
  apply Int.cast_injective (α := k)
  rw [← VirtualCharacter.characterPairing_realize,
    iso.realize_cyclicTIImageVirtual,
    iso.realize_cyclicTIImageVirtual,
    iso.characterPairing_cyclicTIImage]
  split <;> simp

/-- A signed difference of two distinct entries in one cyclic-TI row has
squared norm two. -/
private theorem normSq_signed_cyclicTIImageVirtual_sub
    (epsilon : ℤ) (hepsilon : IsSign epsilon)
    (i : IrreducibleCharacter W₁ k)
    (j₁ j₂ : IrreducibleCharacter W₂ k) (hj : j₁ ≠ j₂) :
    normSq
        (epsilon •
          (iso.cyclicTIImageVirtual (i, j₁) -
            iso.cyclicTIImageVirtual (i, j₂))) = 2 := by
  rcases hepsilon with rfl | rfl <;>
    simp [normSq, sub_eq_add_neg, coeffDot_add_left,
      coeffDot_add_right, coeffDot_neg_left, coeffDot_neg_right,
      iso.coeffDot_cyclicTIImageVirtual, hj, hj.symm]

/-- Pairing a norm-two lattice vector with a norm-one lattice vector has
absolute value at most one. -/
private theorem abs_coeffDot_le_one_of_normSq_eq_two_one
    {iota : Type*} (x y : IntegralLattice iota)
    (hx : normSq x = 2) (hy : normSq y = 1) :
    |coeffDot x y| ≤ 1 := by
  classical
  obtain ⟨a, b, alpha, beta, hab, halpha, hbeta, rfl⟩ :=
    eq_sum_signed_singles_of_normSq_eq_two x hx
  obtain ⟨c, gamma, hgamma, rfl⟩ :=
    eq_signed_single_of_normSq_eq_one y hy
  rcases halpha with rfl | rfl <;>
    rcases hbeta with rfl | rfl <;>
    rcases hgamma with rfl | rfl <;>
    by_cases hac : a = c <;> by_cases hbc : b = c <;>
      simp_all [coeffDot_add_left, coeffDot_neg_left,
        coeffDot_neg_right]

/-- In a finite type of cardinality greater than two there are two distinct
points different from any prescribed point. -/
private theorem exists_two_ne
    {iota : Type*} [Fintype iota] (hcard : 2 < Fintype.card iota)
    (a : iota) :
    ∃ b c : iota, b ≠ a ∧ c ≠ a ∧ b ≠ c := by
  classical
  let I := {b : iota // b ≠ a}
  have hIcard : Fintype.card I = Fintype.card iota - 1 :=
    Set.card_ne_eq a
  have hIone : 1 < Fintype.card I := by omega
  obtain ⟨b, c, hbc⟩ := Fintype.exists_pair_of_one_lt_card hIone
  exact ⟨b, c, b.property, c.property, fun h ↦ hbc (Subtype.ext h)⟩

/-- Three distinct nonzero cyclic-TI coefficients force coefficient-support
cardinality at least three. -/
private theorem three_le_cyclicTINC
    (phi : ClassFunction G k)
    (p q r : IrreducibleCharacter W₁ k ×
      IrreducibleCharacter W₂ k)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hp : characterPairing phi (iso.cyclicTIImage p) ≠ 0)
    (hq : characterPairing phi (iso.cyclicTIImage q) ≠ 0)
    (hr : characterPairing phi (iso.cyclicTIImage r) ≠ 0) :
    3 ≤ iso.cyclicTINC phi := by
  have hsub : {p, q, r} ⊆ iso.cyclicTICoefficientSupport phi := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;>
      simpa only [iso.mem_cyclicTICoefficientSupport]
  calc
    3 = ({p, q, r} : Finset _).card := by simp [hpq, hpr, hqr]
    _ ≤ (iso.cyclicTICoefficientSupport phi).card :=
      Finset.card_le_card hsub
    _ = iso.cyclicTINC phi := rfl

/-- The positive-sign core of `eq_signed_sub_cTIiso`. -/
private theorem eq_sub_cTIiso
    (phi : VirtualCharacter G k)
    (i : IrreducibleCharacter W₁ k)
    (j₁ j₂ : IrreducibleCharacter W₂ k)
    (hnorm : normSq phi = 2) (hj : j₁ ≠ j₂)
    (heq : Set.EqOn
      (fun w : W ↦ VirtualCharacter.realize phi
        ⟨w, h.le_group w.property⟩)
      (fun w : W ↦
        (iso.cyclicTIImage (i, j₁) - iso.cyclicTIImage (i, j₂))
          ⟨w, h.le_group w.property⟩)
      (cyclicTISetInW W W₁ W₂)) :
    VirtualCharacter.realize phi =
      iso.cyclicTIImage (i, j₁) - iso.cyclicTIImage (i, j₂) := by
  let u₁ : VirtualCharacter G k := iso.cyclicTIImageVirtual (i, j₁)
  let u₂ : VirtualCharacter G k := iso.cyclicTIImageVirtual (i, j₂)
  let rho : VirtualCharacter G k := u₁ - u₂
  let z : VirtualCharacter G k := phi - rho
  have hp₁₂ : (i, j₁) ≠ (i, j₂) := by
    intro hp
    exact hj (congrArg Prod.snd hp)
  have hu₁norm : normSq u₁ = 1 := by
    simp [normSq, u₁, iso.coeffDot_cyclicTIImageVirtual]
  have hu₂norm : normSq u₂ = 1 := by
    simp [normSq, u₂, iso.coeffDot_cyclicTIImageVirtual]
  have hrhonorm : normSq rho = 2 := by
    simpa [rho, u₁, u₂] using
      (iso.normSq_signed_cyclicTIImageVirtual_sub
        (1 : ℤ) (by simp [IsSign]) i j₁ j₂ hj)
  have hrhorealize : VirtualCharacter.realize rho =
      iso.cyclicTIImage (i, j₁) - iso.cyclicTIImage (i, j₂) := by
    simp [rho, u₁, u₂]
  have hzero : Set.EqOn
      (fun w : W ↦ VirtualCharacter.realize z
        ⟨w, h.le_group w.property⟩)
      0 (cyclicTISetInW W W₁ W₂) := by
    intro w hw
    simp only [z, VirtualCharacter.realize_sub, ClassFunction.sub_apply,
      Pi.zero_apply]
    rw [hrhorealize]
    exact sub_eq_zero.mpr (heq hw)
  letI : IsCyclic W₁ := h.left_cyclic
  letI : IsCyclic W₂ := h.right_cyclic
  have hcard₁ :
      2 < Fintype.card (IrreducibleCharacter W₁ k) := by
    rw [IrreducibleCharacter.card_eq_natCard_of_isCyclic]
    exact h.two_lt_card_left
  have hcard₂ :
      2 < Fintype.card (IrreducibleCharacter W₂ k) := by
    rw [IrreducibleCharacter.card_eq_natCard_of_isCyclic]
    exact h.two_lt_card_right
  have hphiNC : iso.cyclicTINC (VirtualCharacter.realize phi) ≤ 2 := by
    have hbound := iso.cyclicTINC_realize_le_normSq phi
    have hbound' :
        (iso.cyclicTINC (VirtualCharacter.realize phi) : ℤ) ≤ 2 := by
      simpa [hnorm] using hbound
    exact Int.ofNat_le.mp hbound'
  have hrhoNC : iso.cyclicTINC (VirtualCharacter.realize rho) ≤ 2 := by
    have hbound := iso.cyclicTINC_realize_le_normSq rho
    have hbound' :
        (iso.cyclicTINC (VirtualCharacter.realize rho) : ℤ) ≤ 2 := by
      simpa [hrhonorm] using hbound
    exact Int.ofNat_le.mp hbound'
  have hzNC : iso.cyclicTINC (VirtualCharacter.realize z) ≤ 4 := by
    calc
      iso.cyclicTINC (VirtualCharacter.realize z) =
          iso.cyclicTINC
            (VirtualCharacter.realize phi - VirtualCharacter.realize rho) := by
        simp [z]
      _ ≤ iso.cyclicTINC (VirtualCharacter.realize phi) +
          iso.cyclicTINC (VirtualCharacter.realize rho) :=
        iso.cyclicTINC_sub_le _ _
      _ ≤ 4 := by omega
  have hzsmall : iso.cyclicTINC (VirtualCharacter.realize z) <
      2 * min
        (Fintype.card (IrreducibleCharacter W₁ k))
        (Fintype.card (IrreducibleCharacter W₂ k)) := by
    omega
  have hpair (v : VirtualCharacter G k)
      (a : IrreducibleCharacter W₁ k)
      (b : IrreducibleCharacter W₂ k) :
      characterPairing (VirtualCharacter.realize v)
          (iso.cyclicTIImage (a, b)) =
        (coeffDot v (iso.cyclicTIImageVirtual (a, b)) : k) := by
    rw [← iso.realize_cyclicTIImageVirtual (a, b)]
    exact VirtualCharacter.characterPairing_realize _ _
  have hpair_ne (v : VirtualCharacter G k)
      (a : IrreducibleCharacter W₁ k)
      (b : IrreducibleCharacter W₂ k)
      (hv : coeffDot v (iso.cyclicTIImageVirtual (a, b)) ≠ 0) :
      characterPairing (VirtualCharacter.realize v)
          (iso.cyclicTIImage (a, b)) ≠ 0 := by
    rw [hpair v a b]
    exact Int.cast_ne_zero.mpr hv
  have hz₁eq : coeffDot z u₁ = coeffDot phi u₁ - 1 := by
    simp [z, rho, u₁, u₂, sub_eq_add_neg, coeffDot_add_left,
      coeffDot_neg_left, iso.coeffDot_cyclicTIImageVirtual,
      hp₁₂, hp₁₂.symm]
  have hz₂eq : coeffDot z u₂ = coeffDot phi u₂ + 1 := by
    simp [z, rho, u₁, u₂, sub_eq_add_neg, coeffDot_add_left,
      coeffDot_neg_left, iso.coeffDot_cyclicTIImageVirtual,
      hp₁₂, hp₁₂.symm]
  have hbound₁ : -1 ≤ coeffDot phi u₁ ∧ coeffDot phi u₁ ≤ 1 :=
    abs_le.mp
      (abs_coeffDot_le_one_of_normSq_eq_two_one phi u₁ hnorm hu₁norm)
  have hbound₂ : -1 ≤ coeffDot phi u₂ ∧ coeffDot phi u₂ ≤ 1 :=
    abs_le.mp
      (abs_coeffDot_le_one_of_normSq_eq_two_one phi u₂ hnorm hu₂norm)
  have hz₁nonpos : coeffDot z u₁ ≤ 0 := by omega
  have hz₂nonneg : 0 ≤ coeffDot z u₂ := by omega
  have hz_eq_phi_of_fst_ne
      (a : IrreducibleCharacter W₁ k)
      (b : IrreducibleCharacter W₂ k) (ha : a ≠ i) :
      coeffDot z (iso.cyclicTIImageVirtual (a, b)) =
        coeffDot phi (iso.cyclicTIImageVirtual (a, b)) := by
    have hp₁ : (i, j₁) ≠ (a, b) := by
      intro hp
      exact ha (congrArg Prod.fst hp).symm
    have hp₂ : (i, j₂) ≠ (a, b) := by
      intro hp
      exact ha (congrArg Prod.fst hp).symm
    simp [z, rho, u₁, u₂, sub_eq_add_neg, coeffDot_add_left,
      coeffDot_neg_left, iso.coeffDot_cyclicTIImageVirtual, hp₁, hp₂]
  have hphi_rho : phi = rho := by
    by_contra hne
    have hpivot : coeffDot z u₁ ≠ 0 ∨ coeffDot z u₂ ≠ 0 := by
      by_contra hpivot
      simp only [not_or, not_ne_iff] at hpivot
      have hzr : coeffDot z rho = 0 := by
        simp [rho, sub_eq_add_neg, coeffDot_add_right,
          coeffDot_neg_right, hpivot.1, hpivot.2]
      have hdecomp : phi = z + rho := by simp [z]
      have hn := congrArg normSq hdecomp
      rw [hnorm, normSq_add, hzr, hrhonorm] at hn
      have hz0 : z = 0 :=
        (normSq_eq_zero_iff z).mp (by omega)
      apply hne
      have : phi - rho = 0 := by simpa [z] using hz0
      exact sub_eq_zero.mp this
    rcases hpivot with hz₁ | hz₂
    · have hpivotPair : characterPairing (VirtualCharacter.realize z)
          (iso.cyclicTIImage (i, j₁)) ≠ 0 :=
        hpair_ne z i j₁ (by simpa [u₁] using hz₁)
      rcases iso.small_cyclicTINC (VirtualCharacter.realize z) hzero
          i j₁ hzsmall
          (by simpa [cyclicTIImage, cyclicTISourceIrreducible] using
            hpivotPair) with hcol | hrow
      · have hcol₂ : characterPairing (VirtualCharacter.realize z)
            (iso.cyclicTIImage (i, j₂)) = 0 := by
          simpa [cyclicTIImage, cyclicTISourceIrreducible, hj.symm] using
            hcol i j₂
        have hz₂zero : coeffDot z u₂ = 0 := by
          apply Int.cast_injective (α := k)
          have hcast := (hpair z i j₂).symm.trans hcol₂
          simpa [u₂] using hcast
        have hphi₂ : coeffDot phi u₂ ≠ 0 := by omega
        obtain ⟨a, b, ha, hb, hab⟩ := exists_two_ne hcard₁ i
        have hline (c : IrreducibleCharacter W₁ k) :
            coeffDot z (iso.cyclicTIImageVirtual (c, j₁)) =
              coeffDot z u₁ := by
          have hc : characterPairing (VirtualCharacter.realize z)
                (iso.cyclicTIImage (c, j₁)) =
              characterPairing (VirtualCharacter.realize z)
                (iso.cyclicTIImage (i, j₁)) := by
            simpa [cyclicTIImage, cyclicTISourceIrreducible] using
              hcol c j₁
          apply Int.cast_injective (α := k)
          have hcast :
              (coeffDot z (iso.cyclicTIImageVirtual (c, j₁)) : k) =
                (coeffDot z (iso.cyclicTIImageVirtual (i, j₁)) : k) := by
            rw [← hpair z c j₁, ← hpair z i j₁]
            exact hc
          simpa [u₁] using hcast
        have hphia :
            coeffDot phi (iso.cyclicTIImageVirtual (a, j₁)) ≠ 0 := by
          rw [← hz_eq_phi_of_fst_ne a j₁ ha, hline a]
          exact hz₁
        have hphib :
            coeffDot phi (iso.cyclicTIImageVirtual (b, j₁)) ≠ 0 := by
          rw [← hz_eq_phi_of_fst_ne b j₁ hb, hline b]
          exact hz₁
        have hp₂a : (i, j₂) ≠ (a, j₁) := by
          intro hp
          exact ha (congrArg Prod.fst hp).symm
        have hp₂b : (i, j₂) ≠ (b, j₁) := by
          intro hp
          exact hb (congrArg Prod.fst hp).symm
        have hab' : (a, j₁) ≠ (b, j₁) := by
          intro hp
          exact hab (congrArg Prod.fst hp)
        have hthree := iso.three_le_cyclicTINC
          (VirtualCharacter.realize phi)
          (i, j₂) (a, j₁) (b, j₁)
          hp₂a hp₂b hab'
          (hpair_ne phi i j₂ (by simpa [u₂] using hphi₂))
          (hpair_ne phi a j₁ hphia)
          (hpair_ne phi b j₁ hphib)
        omega
      · have hroweq : coeffDot z u₂ = coeffDot z u₁ := by
          have hr : characterPairing (VirtualCharacter.realize z)
                (iso.cyclicTIImage (i, j₂)) =
              characterPairing (VirtualCharacter.realize z)
                (iso.cyclicTIImage (i, j₁)) := by
            simpa [cyclicTIImage, cyclicTISourceIrreducible] using
              hrow i j₂
          apply Int.cast_injective (α := k)
          have hcast :
              (coeffDot z (iso.cyclicTIImageVirtual (i, j₂)) : k) =
                (coeffDot z (iso.cyclicTIImageVirtual (i, j₁)) : k) := by
            rw [← hpair z i j₂, ← hpair z i j₁]
            exact hr
          simpa [u₁, u₂] using hcast
        omega
    · have hpivotPair : characterPairing (VirtualCharacter.realize z)
          (iso.cyclicTIImage (i, j₂)) ≠ 0 :=
        hpair_ne z i j₂ (by simpa [u₂] using hz₂)
      rcases iso.small_cyclicTINC (VirtualCharacter.realize z) hzero
          i j₂ hzsmall
          (by simpa [cyclicTIImage, cyclicTISourceIrreducible] using
            hpivotPair) with hcol | hrow
      · have hcol₁ : characterPairing (VirtualCharacter.realize z)
            (iso.cyclicTIImage (i, j₁)) = 0 := by
          simpa [cyclicTIImage, cyclicTISourceIrreducible, hj] using
            hcol i j₁
        have hz₁zero : coeffDot z u₁ = 0 := by
          apply Int.cast_injective (α := k)
          have hcast := (hpair z i j₁).symm.trans hcol₁
          simpa [u₁] using hcast
        have hphi₁ : coeffDot phi u₁ ≠ 0 := by omega
        obtain ⟨a, b, ha, hb, hab⟩ := exists_two_ne hcard₁ i
        have hline (c : IrreducibleCharacter W₁ k) :
            coeffDot z (iso.cyclicTIImageVirtual (c, j₂)) =
              coeffDot z u₂ := by
          have hc : characterPairing (VirtualCharacter.realize z)
                (iso.cyclicTIImage (c, j₂)) =
              characterPairing (VirtualCharacter.realize z)
                (iso.cyclicTIImage (i, j₂)) := by
            simpa [cyclicTIImage, cyclicTISourceIrreducible] using
              hcol c j₂
          apply Int.cast_injective (α := k)
          have hcast :
              (coeffDot z (iso.cyclicTIImageVirtual (c, j₂)) : k) =
                (coeffDot z (iso.cyclicTIImageVirtual (i, j₂)) : k) := by
            rw [← hpair z c j₂, ← hpair z i j₂]
            exact hc
          simpa [u₂] using hcast
        have hphia :
            coeffDot phi (iso.cyclicTIImageVirtual (a, j₂)) ≠ 0 := by
          rw [← hz_eq_phi_of_fst_ne a j₂ ha, hline a]
          exact hz₂
        have hphib :
            coeffDot phi (iso.cyclicTIImageVirtual (b, j₂)) ≠ 0 := by
          rw [← hz_eq_phi_of_fst_ne b j₂ hb, hline b]
          exact hz₂
        have hp₁a : (i, j₁) ≠ (a, j₂) := by
          intro hp
          exact ha (congrArg Prod.fst hp).symm
        have hp₁b : (i, j₁) ≠ (b, j₂) := by
          intro hp
          exact hb (congrArg Prod.fst hp).symm
        have hab' : (a, j₂) ≠ (b, j₂) := by
          intro hp
          exact hab (congrArg Prod.fst hp)
        have hthree := iso.three_le_cyclicTINC
          (VirtualCharacter.realize phi)
          (i, j₁) (a, j₂) (b, j₂)
          hp₁a hp₁b hab'
          (hpair_ne phi i j₁ (by simpa [u₁] using hphi₁))
          (hpair_ne phi a j₂ hphia)
          (hpair_ne phi b j₂ hphib)
        omega
      · have hroweq : coeffDot z u₁ = coeffDot z u₂ := by
          have hr : characterPairing (VirtualCharacter.realize z)
                (iso.cyclicTIImage (i, j₁)) =
              characterPairing (VirtualCharacter.realize z)
                (iso.cyclicTIImage (i, j₂)) := by
            simpa [cyclicTIImage, cyclicTISourceIrreducible] using
              hrow i j₁
          apply Int.cast_injective (α := k)
          have hcast :
              (coeffDot z (iso.cyclicTIImageVirtual (i, j₁)) : k) =
                (coeffDot z (iso.cyclicTIImageVirtual (i, j₂)) : k) := by
            rw [← hpair z i j₁, ← hpair z i j₂]
            exact hr
          simpa [u₁, u₂] using hcast
        omega
  have hrealize := congrArg VirtualCharacter.realize hphi_rho
  simpa [rho, u₁, u₂] using hrealize

/-- `eq_signed_sub_cTIiso` from `PFsection3.v`: a norm-two virtual
character agreeing on the cyclic-TI set with a signed difference of two
entries in one row agrees with it everywhere. -/
theorem eq_signed_sub_cTIiso
    (phi : VirtualCharacter G k) (epsilon : ℤ) (hepsilon : IsSign epsilon)
    (i : IrreducibleCharacter W₁ k)
    (j₁ j₂ : IrreducibleCharacter W₂ k)
    (hnorm : normSq phi = 2) (hj : j₁ ≠ j₂)
    (heq : Set.EqOn
      (fun w : W ↦ VirtualCharacter.realize phi
        ⟨w, h.le_group w.property⟩)
      (fun w : W ↦
        ((epsilon : k) •
          (iso.cyclicTIImage (i, j₁) - iso.cyclicTIImage (i, j₂)))
          ⟨w, h.le_group w.property⟩)
      (cyclicTISetInW W W₁ W₂)) :
    VirtualCharacter.realize phi =
      (epsilon : k) •
        (iso.cyclicTIImage (i, j₁) - iso.cyclicTIImage (i, j₂)) := by
  rcases hepsilon with rfl | rfl
  · have heqPos : Set.EqOn
        (fun w : W ↦ VirtualCharacter.realize phi
          ⟨w, h.le_group w.property⟩)
        (fun w : W ↦
          (iso.cyclicTIImage (i, j₁) - iso.cyclicTIImage (i, j₂))
            ⟨w, h.le_group w.property⟩)
        (cyclicTISetInW W W₁ W₂) := by
      simpa only [Int.cast_one, one_smul] using heq
    have hpos := iso.eq_sub_cTIiso phi i j₁ j₂ hnorm hj heqPos
    calc
      VirtualCharacter.realize phi =
          iso.cyclicTIImage (i, j₁) - iso.cyclicTIImage (i, j₂) := hpos
      _ = ((1 : ℤ) : k) •
          (iso.cyclicTIImage (i, j₁) - iso.cyclicTIImage (i, j₂)) := by
        norm_num
  · have hnormNeg : normSq (-phi) = 2 := by
      simpa [normSq, coeffDot_neg_left, coeffDot_neg_right] using hnorm
    have heqNeg : Set.EqOn
        (fun w : W ↦ VirtualCharacter.realize (-phi)
          ⟨w, h.le_group w.property⟩)
        (fun w : W ↦
          (iso.cyclicTIImage (i, j₁) - iso.cyclicTIImage (i, j₂))
            ⟨w, h.le_group w.property⟩)
        (cyclicTISetInW W W₁ W₂) := by
      intro w hw
      have hvalue := heq hw
      simp only [VirtualCharacter.realize_neg, ClassFunction.neg_apply]
      simp only [ClassFunction.smul_apply, Int.cast_neg, Int.cast_one,
        neg_one_mul] at hvalue
      rw [hvalue]
      simp
    have hneg := iso.eq_sub_cTIiso (-phi) i j₁ j₂ hnormNeg hj heqNeg
    calc
      VirtualCharacter.realize phi =
          -VirtualCharacter.realize (-phi) := by simp
      _ = -(iso.cyclicTIImage (i, j₁) - iso.cyclicTIImage (i, j₂)) :=
        congrArg Neg.neg hneg
      _ = (((-1 : ℤ) : k) •
          (iso.cyclicTIImage (i, j₁) - iso.cyclicTIImage (i, j₂))) := by
        ext g
        simp only [ClassFunction.neg_apply, ClassFunction.sub_apply,
          ClassFunction.smul_apply, Int.cast_neg, Int.cast_one]
        ring

end CyclicTIIsometryData

end

end Submission.OddOrder.PF
