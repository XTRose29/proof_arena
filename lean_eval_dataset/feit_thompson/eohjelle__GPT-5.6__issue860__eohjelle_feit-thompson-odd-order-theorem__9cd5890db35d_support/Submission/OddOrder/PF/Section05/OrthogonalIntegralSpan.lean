import Submission.OddOrder.PF.Section05.CoherenceBasics

/-!
# Orthogonal splitting in an integral character span

This file isolates the finite integral orthogonal projection used in
Peterfalvi (9.11.7)--(9.11.8).  For an orthonormal finite family of virtual
characters, pairing a virtual character with the family gives integral
coefficients.  Their linear combination is therefore in the integral span,
and the complementary virtual character is orthogonal to that span.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical

universe u

local instance orthogonalIntegralSpanInvertibleCard
    {Q : Type u} [Group Q] [Fintype Q] :
    Invertible (Nat.card Q : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

private theorem orthogonalIntegralSpan_pairing_sub_left
    {Q : Type u} [Group Q] [Fintype Q]
    (phi psi theta : ClassFunction Q ℂ) :
    characterPairing (phi - psi) theta =
      characterPairing phi theta - characterPairing psi theta := by
  rw [sub_eq_add_neg, characterPairing_add_left,
    ← neg_one_smul ℂ psi, characterPairing_smul_left]
  ring

private theorem orthogonalIntegralSpan_pairing_zsmul_left
    {Q : Type u} [Group Q] [Fintype Q]
    (a : ℤ) (phi psi : ClassFunction Q ℂ) :
    characterPairing (a • phi) psi =
      (a : ℂ) * characterPairing phi psi := by
  rw [← Int.cast_smul_eq_zsmul ℂ]
  exact characterPairing_smul_left (a : ℂ) phi psi

private theorem orthogonalIntegralSpan_pairing_finset_sum_left
    {Q : Type u} [Group Q] [Fintype Q]
    {I : Type*} (s : Finset I) (f : I → ClassFunction Q ℂ)
    (psi : ClassFunction Q ℂ) :
    characterPairing (∑ i ∈ s, f i) psi =
      ∑ i ∈ s, characterPairing (f i) psi := by
  exact map_sum (characterPairingRight psi) (fun i ↦ f i) s

/-- Integral orthogonal splitting along a finite orthonormal family of
virtual characters.  The first summand belongs to the integral span of the
family; the second is virtual and orthogonal both to every family member and
to the first summand. -/
theorem orthogonal_split_virtual
    {Q : Type u} [Group Q] [Fintype Q]
    (T : Finset (ClassFunction Q ℂ))
    (hTvirtual : ∀ alpha ∈ T, ClassFunction.IsVirtual alpha)
    (hTorthonormal : ∀ alpha ∈ T, ∀ gamma ∈ T,
      characterPairing alpha gamma =
        if alpha = gamma then 1 else 0)
    {beta : ClassFunction Q ℂ}
    (hbeta : ClassFunction.IsVirtual beta) :
    ∃ X Y : ClassFunction Q ℂ,
      X ∈ AddSubgroup.closure
        (↑T : Set (ClassFunction Q ℂ)) ∧
      ClassFunction.IsVirtual X ∧
      ClassFunction.IsVirtual Y ∧
      beta = X + Y ∧
      (∀ alpha ∈ T, characterPairing Y alpha = 0) ∧
      characterPairing X Y = 0 := by
  classical
  obtain ⟨b, hb⟩ := hbeta
  let z : ClassFunction Q ℂ → VirtualCharacter Q ℂ := fun alpha ↦
    if halpha : alpha ∈ T then
      Classical.choose (hTvirtual alpha halpha)
    else 0
  have hz (alpha : ClassFunction Q ℂ) (halpha : alpha ∈ T) :
      VirtualCharacter.realize (z alpha) = alpha := by
    simp only [z, dif_pos halpha]
    exact Classical.choose_spec (hTvirtual alpha halpha)
  let a : ClassFunction Q ℂ → ℤ := fun alpha ↦ coeffDot b (z alpha)
  let X : ClassFunction Q ℂ := ∑ alpha ∈ T, a alpha • alpha
  let Y : ClassFunction Q ℂ := beta - X
  have hXspan :
      X ∈ AddSubgroup.closure
        (↑T : Set (ClassFunction Q ℂ)) := by
    apply AddSubgroup.sum_mem
    intro alpha halpha
    exact (AddSubgroup.closure
      (↑T : Set (ClassFunction Q ℂ))).zsmul_mem
        (AddSubgroup.subset_closure halpha) (a alpha)
  have hXvirtual : ClassFunction.IsVirtual X := by
    refine ⟨∑ alpha ∈ T, a alpha • z alpha, ?_⟩
    simp only [X, map_sum]
    apply Finset.sum_congr rfl
    intro alpha halpha
    rw [map_zsmul, hz alpha halpha]
  have hYvirtual : ClassFunction.IsVirtual Y := by
    exact (show ClassFunction.IsVirtual beta from ⟨b, hb⟩).sub hXvirtual
  have hbetaPair (alpha : ClassFunction Q ℂ) (halpha : alpha ∈ T) :
      characterPairing beta alpha = (a alpha : ℂ) := by
    change characterPairing beta alpha =
      ((coeffDot b (z alpha) : ℤ) : ℂ)
    calc
      characterPairing beta alpha =
          characterPairing (VirtualCharacter.realize b)
            (VirtualCharacter.realize (z alpha)) := by
        rw [hb, hz alpha halpha]
      _ = ((coeffDot b (z alpha) : ℤ) : ℂ) :=
        VirtualCharacter.characterPairing_realize b (z alpha)
  have hXPair (alpha : ClassFunction Q ℂ) (halpha : alpha ∈ T) :
      characterPairing X alpha = (a alpha : ℂ) := by
    simp only [X]
    rw [orthogonalIntegralSpan_pairing_finset_sum_left]
    rw [Finset.sum_eq_single alpha]
    · rw [orthogonalIntegralSpan_pairing_zsmul_left,
        hTorthonormal alpha halpha alpha halpha,
        if_pos rfl, mul_one]
    · intro gamma hgamma hne
      rw [orthogonalIntegralSpan_pairing_zsmul_left,
        hTorthonormal gamma hgamma alpha halpha,
        if_neg hne, mul_zero]
    · exact fun h ↦ (h halpha).elim
  have hYorth (alpha : ClassFunction Q ℂ) (halpha : alpha ∈ T) :
      characterPairing Y alpha = 0 := by
    simp only [Y]
    rw [orthogonalIntegralSpan_pairing_sub_left,
      hbetaPair alpha halpha, hXPair alpha halpha, sub_self]
  have hXY : characterPairing X Y = 0 := by
    simp only [X]
    rw [orthogonalIntegralSpan_pairing_finset_sum_left]
    apply Finset.sum_eq_zero
    intro alpha halpha
    rw [orthogonalIntegralSpan_pairing_zsmul_left,
      characterPairing_comm, hYorth alpha halpha, mul_zero]
  refine ⟨X, Y, hXspan, hXvirtual, hYvirtual, ?_, hYorth, hXY⟩
  simp only [Y]
  abel

end

end Submission.OddOrder.PF
