import Submission.OddOrder.PF.Section03.CyclicTISmallSupport

/-!
# Uniqueness and naturality of the cyclic-TI isometry

This file ports `eq_in_cycTIiso` and `cfAut_cycTIiso`, the two parts of
Peterfalvi (3.9)(a).  The construction is phrased first for arbitrary
`CyclicTIIsometryData`; the canonical statements are obtained by specializing
to `CyclicTIHypothesis.cyclicTIIsometryData`.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical

universe u

variable {Gamma k : Type u} [Group Gamma] [Fintype Gamma]
  [Field k] [IsAlgClosed k] [CharZero k]
  {G W W₁ W₂ : Subgroup Gamma}
  {defW : IsInternalDirectProductIn W₁ W₂ W}

local instance cyclicTIUniquenessInvertibleCard
    {H : Type u} [Group H] [Fintype H] :
    Invertible (Nat.card H : k) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

private theorem characterPairing_sub_left
    {H : Type u} [Group H] [Fintype H]
    (f g z : ClassFunction H k) :
    characterPairing (f - g) z =
      characterPairing f z - characterPairing g z := by
  change characterPairingRight z (f - g) = _
  exact map_sub (characterPairingRight z) f g

private theorem signedIrreducible_eq_of_pairing_eq_one
    {H : Type u} [Group H] [Fintype H]
    {f g : ClassFunction H k}
    {chi psi : IrreducibleCharacter H k} {epsilon delta : ℤ}
    (hepsilon : IsSign epsilon) (hdelta : IsSign delta)
    (hf : f = (epsilon : k) • (chi : ClassFunction H k))
    (hg : g = (delta : k) • (psi : ClassFunction H k))
    (hpair : characterPairing f g = 1) :
    f = g := by
  subst f
  subst g
  rcases hepsilon with rfl | rfl <;>
    rcases hdelta with rfl | rfl <;>
    by_cases hchi : chi = psi <;>
    simp [characterPairing_smul_left, characterPairing_smul_right,
      IrreducibleCharacter.characterPairing_eq_ite, hchi] at hpair ⊢ <;>
    norm_num at hpair

private theorem mapRingHom_smul
    {H : Type u} [Group H]
    (sigma : k ≃+* k) (a : k) (f : ClassFunction H k) :
    ClassFunction.mapRingHom sigma.toRingHom (a • f) =
      sigma a • ClassFunction.mapRingHom sigma.toRingHom f := by
  ext x
  simp [map_mul]

private theorem mapRingHom_irreducible
    {H : Type u} [Group H] [Fintype H]
    (sigma : k ≃+* k) (chi : IrreducibleCharacter H k) :
    ClassFunction.mapRingHom sigma.toRingHom (chi : ClassFunction H k) =
      (IrreducibleCharacter.mapRingEquiv sigma chi :
        ClassFunction H k) := by
  ext x
  simp

private theorem inverseLinear_irreducible
    {H : Type u} [Group H] [Fintype H]
    (chi : IrreducibleCharacter H k) :
    ClassFunction.inverseLinear (chi : ClassFunction H k) =
      (IrreducibleCharacter.dual chi : ClassFunction H k) := by
  ext x
  simp

namespace CyclicTIIsometryData

variable {h : CyclicTIHypothesis G W W₁ W₂ defW}

/-- Peterfalvi (3.9)(a), in the data-generic form used by Section 4.

A signed irreducible character of `G` which restricts to an irreducible
character `chi` on the cyclic-TI set is the image of `chi` under the
cyclic-TI isometry. -/
theorem eq_in_cyclicTIIsometry
    (iso : CyclicTIIsometryData (k := k) h)
    (chi : IrreducibleCharacter W k) (phi : ClassFunction G k)
    (hdirr : ∃ (psi : IrreducibleCharacter G k) (epsilon : ℤ),
      IsSign epsilon ∧
        phi = (epsilon : k) • (psi : ClassFunction G k))
    (heq : Set.EqOn
      (fun w : W ↦ phi ⟨w, h.le_group w.property⟩)
      (↑chi : W → k) (cyclicTISetInW W W₁ W₂)) :
    phi = iso.linearMap (chi : ClassFunction W k) := by
  let p := IrreducibleCharacter.cyclicTICharacterIndex defW chi
  have hp :
      IrreducibleCharacter.cyclicTICharacter defW p.1 p.2 = chi := by
    exact (IrreducibleCharacter.cyclicTICharacterEquiv defW).apply_symm_apply chi
  have himage :
      iso.cyclicTIImage p = iso.linearMap (chi : ClassFunction W k) := by
    simp [cyclicTIImage, cyclicTISourceIrreducible, hp]
  let delta : ClassFunction G k := iso.cyclicTIImage p - phi
  have hzero : Set.EqOn
      (fun w : W ↦ delta ⟨w, h.le_group w.property⟩)
      0 (cyclicTISetInW W W₁ W₂) := by
    intro w hw
    simp only [delta, ClassFunction.sub_apply, Pi.zero_apply]
    rw [himage]
    apply sub_eq_zero.mpr
    exact (iso.restrict (chi : ClassFunction W k) hw).trans (heq hw).symm
  have hdelta : delta = 0 := by
    by_contra hdelta_ne
    have hself :
        characterPairing (iso.cyclicTIImage p) (iso.cyclicTIImage p) = 1 := by
      rw [himage, iso.pairing]
      exact IrreducibleCharacter.characterPairing_self chi
    obtain ⟨theta, eta, heta, himageSigned⟩ :=
      iso.exists_signed_irreducible_image chi
    have himageSigned' :
        iso.cyclicTIImage p =
          (eta : k) • (theta : ClassFunction G k) := by
      rw [himage]
      exact himageSigned
    have hcoefficient :
        characterPairing delta (iso.cyclicTIImage p) ≠ 0 := by
      intro hcoefficient_zero
      have hpair :
          characterPairing phi (iso.cyclicTIImage p) = 1 := by
        change characterPairing (iso.cyclicTIImage p - phi)
          (iso.cyclicTIImage p) = 0 at hcoefficient_zero
        rw [characterPairing_sub_left, hself] at hcoefficient_zero
        exact (sub_eq_zero.mp hcoefficient_zero).symm
      obtain ⟨psi, epsilon, hepsilon, hphi⟩ := hdirr
      have hphiImage : phi = iso.cyclicTIImage p :=
        signedIrreducible_eq_of_pairing_eq_one hepsilon heta hphi
          himageSigned' hpair
      apply hdelta_ne
      simp [delta, hphiImage]
    have hpos : 0 < iso.cyclicTINC delta := by
      rw [cyclicTINC, Finset.card_pos]
      exact ⟨p, by simp [hcoefficient]⟩
    have hle : iso.cyclicTINC delta ≤ 2 := by
      calc
        iso.cyclicTINC delta ≤
            iso.cyclicTINC (iso.cyclicTIImage p) + iso.cyclicTINC phi := by
          exact iso.cyclicTINC_sub_le (iso.cyclicTIImage p) phi
        _ ≤ 1 + 1 := Nat.add_le_add
          (le_of_eq (iso.cyclicTINC_image p))
          (iso.cyclicTINC_signedIrreducible_le_one phi hdirr)
        _ = 2 := by omega
    letI : IsCyclic W₁ := h.left_cyclic
    letI : IsCyclic W₂ := h.right_cyclic
    have hleft :
        2 < Fintype.card (IrreducibleCharacter W₁ k) := by
      rw [IrreducibleCharacter.card_eq_natCard_of_isCyclic]
      exact h.two_lt_card_left
    have hright :
        2 < Fintype.card (IrreducibleCharacter W₂ k) := by
      rw [IrreducibleCharacter.card_eq_natCard_of_isCyclic]
      exact h.two_lt_card_right
    have hlt : iso.cyclicTINC delta <
        2 * min (Fintype.card (IrreducibleCharacter W₁ k))
          (Fintype.card (IrreducibleCharacter W₂ k)) := by
      omega
    have hmin := iso.cyclicTINC_min_le delta hzero hpos hlt
    omega
  change iso.cyclicTIImage p - phi = 0 at hdelta
  rw [sub_eq_zero] at hdelta
  rw [← himage, hdelta]

/-- Norm-one virtual-character form of `eq_in_cyclicTIIsometry`.
This is often the most convenient direct analogue of Coq's `dirr` hypothesis. -/
theorem eq_in_cyclicTIIsometry_realize
    (iso : CyclicTIIsometryData (k := k) h)
    (chi : IrreducibleCharacter W k) (nu : VirtualCharacter G k)
    (hnorm : normSq nu = 1)
    (heq : Set.EqOn
      (fun w : W ↦ VirtualCharacter.realize nu
        ⟨w, h.le_group w.property⟩)
      (↑chi : W → k) (cyclicTISetInW W W₁ W₂)) :
    VirtualCharacter.realize nu =
      iso.linearMap (chi : ClassFunction W k) := by
  obtain ⟨psi, epsilon, hepsilon, hnu⟩ :=
    eq_signed_single_of_normSq_eq_one nu hnorm
  apply iso.eq_in_cyclicTIIsometry chi (VirtualCharacter.realize nu)
  · refine ⟨psi, epsilon, hepsilon, ?_⟩
    rw [hnu, VirtualCharacter.realize_single]
  · exact heq

/-- The coefficient-field automorphism compatibility in Peterfalvi (3.9)(a),
for arbitrary cyclic-TI isometry data. -/
theorem mapRingEquiv_cyclicTIIsometry
    (iso : CyclicTIIsometryData (k := k) h)
    (sigma : k ≃+* k) (phi : ClassFunction W k) :
    ClassFunction.mapRingHom sigma.toRingHom (iso.linearMap phi) =
      iso.linearMap (ClassFunction.mapRingHom sigma.toRingHom phi) := by
  have hirr (chi : IrreducibleCharacter W k) :
      ClassFunction.mapRingHom sigma.toRingHom
          (iso.linearMap (chi : ClassFunction W k)) =
        iso.linearMap
          (IrreducibleCharacter.mapRingEquiv sigma chi :
            ClassFunction W k) := by
    apply iso.eq_in_cyclicTIIsometry
        (IrreducibleCharacter.mapRingEquiv sigma chi)
    · obtain ⟨psi, epsilon, hepsilon, himage⟩ :=
        iso.exists_signed_irreducible_image chi
      refine ⟨IrreducibleCharacter.mapRingEquiv sigma psi,
        epsilon, hepsilon, ?_⟩
      rw [himage]
      ext g
      simp [map_mul]
    · intro w hw
      simp only [ClassFunction.mapRingHom_apply,
        IrreducibleCharacter.mapRingEquiv_apply]
      rw [← RingEquiv.coe_toRingHom sigma]
      exact congrArg sigma.toRingHom
        (iso.restrict (chi : ClassFunction W k) hw)
  rw [← ClassFunction.sum_irreducibleCharacterBasis_eq phi]
  simp only [map_sum, map_smul, mapRingHom_smul]
  apply Finset.sum_congr rfl
  intro chi hchi
  rw [hirr, mapRingHom_irreducible]

/-- Pullback along inversion commutes with arbitrary cyclic-TI isometry data. -/
theorem inverse_cyclicTIIsometry
    (iso : CyclicTIIsometryData (k := k) h)
    (phi : ClassFunction W k) :
    ClassFunction.inverseLinear (iso.linearMap phi) =
      iso.linearMap (ClassFunction.inverseLinear phi) := by
  have hirr (chi : IrreducibleCharacter W k) :
      ClassFunction.inverseLinear
          (iso.linearMap (chi : ClassFunction W k)) =
        iso.linearMap
          (IrreducibleCharacter.dual chi : ClassFunction W k) := by
    apply iso.eq_in_cyclicTIIsometry (IrreducibleCharacter.dual chi)
    · obtain ⟨psi, epsilon, hepsilon, himage⟩ :=
        iso.exists_signed_irreducible_image chi
      refine ⟨IrreducibleCharacter.dual psi, epsilon, hepsilon, ?_⟩
      rw [himage]
      ext g
      simp
    · intro w hw
      have hwinv : w⁻¹ ∈ cyclicTISetInW W W₁ W₂ :=
        (h.set_invStable w).2 hw
      simp only [ClassFunction.inverseLinear_apply,
        IrreducibleCharacter.dual_apply]
      rw [show (⟨w, h.le_group w.property⟩ : G)⁻¹ =
        ⟨w⁻¹, h.le_group (w⁻¹).property⟩ by rfl]
      exact iso.restrict (chi : ClassFunction W k) hwinv
  rw [← ClassFunction.sum_irreducibleCharacterBasis_eq phi]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro chi hchi
  rw [hirr, inverseLinear_irreducible]

end CyclicTIIsometryData

namespace CyclicTIHypothesis

/-- Canonical specialization of Peterfalvi (3.9)(a). -/
theorem eq_in_cyclicTIIsometry
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (chi : IrreducibleCharacter W k) (phi : ClassFunction G k)
    (hdirr : ∃ (psi : IrreducibleCharacter G k) (epsilon : ℤ),
      IsSign epsilon ∧
        phi = (epsilon : k) • (psi : ClassFunction G k))
    (heq : Set.EqOn
      (fun w : W ↦ phi ⟨w, h.le_group w.property⟩)
      (↑chi : W → k) (cyclicTISetInW W W₁ W₂)) :
    phi = h.cyclicTIIsometry (chi : ClassFunction W k) :=
  (h.cyclicTIIsometryData (k := k)).eq_in_cyclicTIIsometry
    chi phi hdirr heq

/-- Source-name alias for `eq_in_cyclicTIIsometry`. -/
theorem eq_in_cycTIiso
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (chi : IrreducibleCharacter W k) (phi : ClassFunction G k)
    (hdirr : ∃ (psi : IrreducibleCharacter G k) (epsilon : ℤ),
      IsSign epsilon ∧
        phi = (epsilon : k) • (psi : ClassFunction G k))
    (heq : Set.EqOn
      (fun w : W ↦ phi ⟨w, h.le_group w.property⟩)
      (↑chi : W → k) (cyclicTISetInW W W₁ W₂)) :
    phi = h.cyclicTIIsometry (chi : ClassFunction W k) :=
  h.eq_in_cyclicTIIsometry chi phi hdirr heq

/-- Canonical coefficient-field automorphism compatibility. -/
theorem mapRingEquiv_cyclicTIIsometry
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (sigma : k ≃+* k) (phi : ClassFunction W k) :
    ClassFunction.mapRingHom sigma.toRingHom (h.cyclicTIIsometry phi) =
      h.cyclicTIIsometry (ClassFunction.mapRingHom sigma.toRingHom phi) :=
  (h.cyclicTIIsometryData (k := k)).mapRingEquiv_cyclicTIIsometry sigma phi

/-- Source-name alias for the coefficient-field automorphism part of
Peterfalvi (3.9)(a). -/
theorem cfAut_cycTIiso
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (sigma : k ≃+* k) (phi : ClassFunction W k) :
    ClassFunction.mapRingHom sigma.toRingHom (h.cyclicTIIsometry phi) =
      h.cyclicTIIsometry (ClassFunction.mapRingHom sigma.toRingHom phi) :=
  h.mapRingEquiv_cyclicTIIsometry sigma phi

/-- Canonical inversion compatibility. -/
theorem inverse_cyclicTIIsometry
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (phi : ClassFunction W k) :
    ClassFunction.inverseLinear (h.cyclicTIIsometry phi) =
      h.cyclicTIIsometry (ClassFunction.inverseLinear phi) :=
  (h.cyclicTIIsometryData (k := k)).inverse_cyclicTIIsometry phi

end CyclicTIHypothesis

end

end Submission.OddOrder.PF
