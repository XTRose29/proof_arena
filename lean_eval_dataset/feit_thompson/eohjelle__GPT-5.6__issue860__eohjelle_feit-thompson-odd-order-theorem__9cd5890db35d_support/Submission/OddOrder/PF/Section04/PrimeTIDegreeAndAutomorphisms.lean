import Submission.OddOrder.MathlibSupport.AlgebraicIntegerCongruence
import Submission.OddOrder.PF.Section01.RestrictionMultiplicity
import Submission.OddOrder.PF.Section03.CyclicTIUniqueness
import Submission.OddOrder.PF.Section04.PrimeTIReducedCharacters

/-!
# Prime-TI degrees and coefficient-field automorphisms

This file ports the block immediately following Peterfalvi 4.3(b,c):
`prTIirr1_mod`, `prTIsign_aut`, and `prTIirr_aut`.

The first theorem says that the degree of the prime-TI irreducible indexed
by `(i,j)` is congruent, modulo `|W₁|`, to the sign of its column.  The next
two theorems show that coefficient-field automorphisms preserve the column
sign and act naturally on the prime-TI rectangle.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical

universe u

variable {Gamma k : Type u} [Group Gamma] [Fintype Gamma]
  [Field k] [IsAlgClosed k] [CharZero k]
  {L K W W₁ W₂ : Subgroup Gamma}
  {defW : IsInternalDirectProductIn W₁ W₂ W}

local instance primeTIDegreeInvertibleCard
    {H : Type u} [Group H] [Fintype H] :
    Invertible (Nat.card H : k) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-- A class function supported at the identity has identity value equal to
the group order times its pairing with the trivial character. -/
private theorem value_one_eq_card_mul_of_vanish_off_one
    {G : Type u} [Group G] [Fintype G]
    (phi one : ClassFunction G k) (z : ℤ)
    (hvanish : ∀ x : G, x ≠ 1 → phi x = 0)
    (hone : ∀ x : G, one x = 1)
    (hpair : characterPairing phi one = (z : k)) :
    phi 1 = (Nat.card G : k) * (z : k) := by
  have hsum : (∑ x : G, phi x) = phi 1 := by
    rw [Finset.sum_eq_single 1]
    · intro x _ hx
      exact hvanish x hx
    · simp
  simp only [characterPairing, hone, mul_one] at hpair
  rw [hsum] at hpair
  have hcard : (Nat.card G : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  calc
    phi 1 = 1 * phi 1 := (one_mul _).symm
    _ = ((Nat.card G : k) * (Nat.card G : k)⁻¹) * phi 1 := by
      rw [mul_inv_cancel₀ hcard]
    _ = (Nat.card G : k) * ((Nat.card G : k)⁻¹ * phi 1) := by
      rw [mul_assoc]
    _ = (Nat.card G : k) * (z : k) := by rw [hpair]

/-- Two signed irreducible characters are equal only when both their signs
and their irreducible constituents agree. -/
private theorem sign_and_irreducible_eq_of_smul_eq
    {G : Type u} [Group G] [Fintype G]
    {epsilon delta : ℤ} {chi psi : IrreducibleCharacter G k}
    (hepsilon : IsSign epsilon) (_hdelta : IsSign delta)
    (heq : (epsilon : k) • (chi : ClassFunction G k) =
      (delta : k) • (psi : ClassFunction G k)) :
    epsilon = delta ∧ chi = psi := by
  have hpair := congrArg
    (fun f : ClassFunction G k ↦
      characterPairing (chi : ClassFunction G k) f) heq
  rw [characterPairing_smul_right, characterPairing_smul_right,
    IrreducibleCharacter.characterPairing_self,
    IrreducibleCharacter.characterPairing_eq_ite, mul_one] at hpair
  have hchi : chi = psi := by
    by_contra hne
    rw [if_neg hne, mul_zero] at hpair
    exact (Int.cast_ne_zero.mpr (isSign_ne_zero hepsilon)) hpair
  subst psi
  rw [if_pos rfl, mul_one] at hpair
  exact ⟨Int.cast_injective hpair, rfl⟩

namespace PrimeTIHypothesis

variable (h : PrimeTIHypothesis L K W W₁ W₂ defW)
  (iso : CyclicTIIsometryData (k := k) h.prime_cycTIhyp)

/-- Peterfalvi 4.3(d), source `prTIirr1_mod`: the degree of a prime-TI
irreducible is congruent to its column sign modulo `|W₁|` in the ring of
algebraic integers of the coefficient field. -/
theorem primeTICharacter_one_mod_card_left
    (i : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k) :
    Submission.OddOrder.MathlibSupport.IsIntegralModEq
      (Nat.card W₁ : k)
      (h.primeTICharacter iso i j 1)
      (h.primeTISign iso j : k) := by
  letI : IsCyclic W₂ := h.fixed_cyclic
  let H : Subgroup L := W₁.subgroupOf L
  let e : H ≃* W₁ :=
    Subgroup.subgroupOfEquivOfLe h.complement_le_group
  letI : IsCyclic H := e.isCyclic.mpr h.complement_cyclic
  let iH : IrreducibleCharacter H k :=
    IrreducibleCharacter.comapMulEquiv e i
  let oneH : IrreducibleCharacter H k := IrreducibleCharacter.trivial
  have honeH : ∀ x : H, oneH x = 1 := by
    intro x
    simp [oneH]
  let mu : IrreducibleCharacter L k := h.primeTIIndex iso (i, j)
  let epsilon : ℤ := h.primeTISign iso j
  let phi : ClassFunction H k :=
    ClassFunction.restrict H (mu : ClassFunction L k) -
      (epsilon : k) • (iH : ClassFunction H k)
  let m : ℕ := IrreducibleCharacter.restrictionMultiplicity H mu
    oneH
  let b : ℤ := if iH = oneH then 1 else 0
  let z : ℤ := (m : ℤ) - epsilon * b
  have hres :
      characterPairingRight (oneH : ClassFunction H k)
          (ClassFunction.restrict H (mu : ClassFunction L k)) = (m : k) :=
    IrreducibleCharacter.characterPairing_restrict_eq_restrictionMultiplicity
      H mu oneH
  have hirr :
      characterPairingRight (oneH : ClassFunction H k)
          (iH : ClassFunction H k) = if iH = oneH then 1 else 0 :=
    IrreducibleCharacter.characterPairing_eq_ite iH oneH
  have hpair : characterPairing phi (oneH : ClassFunction H k) = (z : k) := by
    change characterPairingRight (oneH : ClassFunction H k)
      phi = (z : k)
    rw [show phi = ClassFunction.restrict H (mu : ClassFunction L k) -
      (epsilon : k) • (iH : ClassFunction H k) by rfl, map_sub]
    rw [map_smul, hres, hirr]
    simp only [m, b, z, Int.cast_sub, Int.cast_natCast, Int.cast_mul]
    split <;> simp_all
  have hvanish : ∀ x : H, x ≠ 1 → phi x = 0 := by
    intro x hx
    let x₁ : W₁ := e x
    have hx₁ : x₁ ≠ 1 := by
      intro hx₁
      apply hx
      apply e.injective
      simpa [x₁] using hx₁
    have hxW₂ : (x₁ : Gamma) ∉ W₂ := by
      intro hxW₂
      have hxW₂' :
          (((defW.mulEquiv (x₁, 1) : W) : Gamma)) ∈ W₂ := by
        simpa using hxW₂
      exact hx₁ ((defW.mulEquiv_mem_right_iff (x₁, 1)).mp hxW₂')
    have hw : defW.leftEmbedding x₁ ∈ primeTISetInW W W₂ :=
      mem_primeTISetInW.mpr hxW₂
    have hrestrict :=
      (h.primeTICharacterData iso).restrict_character i j
        hw
    change
      mu x - (epsilon : k) * iH x = 0
    change
      mu ⟨defW.leftEmbedding x₁,
        h.directProduct_le_group (defW.leftEmbedding x₁).property⟩ =
        (epsilon : k) *
          IrreducibleCharacter.cyclicTICharacter defW i j
            (defW.leftEmbedding x₁) at hrestrict
    rw [IrreducibleCharacter.cyclicTICharacter_leftEmbedding,
      IrreducibleCharacter.apply_one_eq_one_of_isCyclic j,
      mul_one] at hrestrict
    have hiH : iH x = i x₁ := by
      exact IrreducibleCharacter.comapMulEquiv_apply e i x
    rw [hiH]
    have hxL :
        (x : L) =
          (⟨defW.leftEmbedding x₁,
            h.directProduct_le_group (defW.leftEmbedding x₁).property⟩ : L) := by
      apply Subtype.ext
      rfl
    rw [hxL, hrestrict, sub_self]
  have hphiOne := value_one_eq_card_mul_of_vanish_off_one
    phi (oneH : ClassFunction H k) z hvanish honeH hpair
  have hcardH : Nat.card H = Nat.card W₁ :=
    Nat.card_congr e.toEquiv
  have hiHOne : iH 1 = 1 :=
    IrreducibleCharacter.apply_one_eq_one_of_isCyclic iH
  change mu 1 - (epsilon : k) * iH 1 =
    (Nat.card H : k) * (z : k) at hphiOne
  rw [hiHOne, mul_one, hcardH] at hphiOne
  exact ⟨z, isIntegral_intCast z, hphiOne⟩

/-- Source `prTIsign_aut`: coefficient-field automorphisms preserve each
prime-TI column sign. -/
theorem primeTISign_mapRingEquiv
    (sigma : k ≃+* k) (j : IrreducibleCharacter W₂ k) :
    h.primeTISign iso (IrreducibleCharacter.mapRingEquiv sigma j) =
      h.primeTISign iso j := by
  let j' := IrreducibleCharacter.mapRingEquiv sigma j
  let mu := h.primeTIIndex iso
    (IrreducibleCharacter.trivial, j)
  let mu' := h.primeTIIndex iso
    (IrreducibleCharacter.trivial, j')
  have hbase := (h.primeTICharacterData iso).isometry_character
    IrreducibleCharacter.trivial j
  have htarget := (h.primeTICharacterData iso).isometry_character
    IrreducibleCharacter.trivial j'
  have heq :
      (h.primeTISign iso j' : k) • (mu' : ClassFunction L k) =
      (h.primeTISign iso j : k) •
          (IrreducibleCharacter.mapRingEquiv sigma mu :
            ClassFunction L k) := by
    change
      ((h.primeTICharacterData iso).sign j' : k) •
          ((h.primeTICharacterData iso).index
            (IrreducibleCharacter.trivial, j') : ClassFunction L k) =
        ((h.primeTICharacterData iso).sign j : k) •
          (IrreducibleCharacter.mapRingEquiv sigma
            ((h.primeTICharacterData iso).index
              (IrreducibleCharacter.trivial, j)) : ClassFunction L k)
    rw [← htarget]
    have hcyclic :
        (IrreducibleCharacter.cyclicTICharacter defW
            IrreducibleCharacter.trivial j' : ClassFunction W k) =
          ClassFunction.mapRingHom sigma.toRingHom
            (IrreducibleCharacter.cyclicTICharacter defW
              IrreducibleCharacter.trivial j : ClassFunction W k) := by
      ext w
      simp [j', IrreducibleCharacter.cyclicTICharacter_apply]
    rw [hcyclic]
    rw [← iso.mapRingEquiv_cyclicTIIsometry]
    rw [hbase]
    ext x
    simp [map_mul]
  exact (sign_and_irreducible_eq_of_smul_eq
    (h.primeTISign_isSign iso j')
    (h.primeTISign_isSign iso j) heq).1

/-- Source `prTIirr_aut`: coefficient-field automorphisms act naturally on
the prime-TI irreducible rectangle. -/
theorem primeTIIndex_mapRingEquiv
    (sigma : k ≃+* k)
    (i : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k) :
    h.primeTIIndex iso
        (IrreducibleCharacter.mapRingEquiv sigma i,
          IrreducibleCharacter.mapRingEquiv sigma j) =
      IrreducibleCharacter.mapRingEquiv sigma
        (h.primeTIIndex iso (i, j)) := by
  let i' := IrreducibleCharacter.mapRingEquiv sigma i
  let j' := IrreducibleCharacter.mapRingEquiv sigma j
  let mu := h.primeTIIndex iso (i, j)
  let mu' := h.primeTIIndex iso (i', j')
  have hbase := (h.primeTICharacterData iso).isometry_character i j
  have htarget := (h.primeTICharacterData iso).isometry_character i' j'
  have heq :
      (h.primeTISign iso j' : k) • (mu' : ClassFunction L k) =
      (h.primeTISign iso j : k) •
          (IrreducibleCharacter.mapRingEquiv sigma mu :
            ClassFunction L k) := by
    change
      ((h.primeTICharacterData iso).sign j' : k) •
          ((h.primeTICharacterData iso).index (i', j') :
            ClassFunction L k) =
        ((h.primeTICharacterData iso).sign j : k) •
          (IrreducibleCharacter.mapRingEquiv sigma
            ((h.primeTICharacterData iso).index (i, j)) :
              ClassFunction L k)
    rw [← htarget]
    have hcyclic :
        (IrreducibleCharacter.cyclicTICharacter defW i' j' :
            ClassFunction W k) =
          ClassFunction.mapRingHom sigma.toRingHom
            (IrreducibleCharacter.cyclicTICharacter defW i j :
              ClassFunction W k) := by
      ext w
      simp [i', j', IrreducibleCharacter.cyclicTICharacter_apply, map_mul]
    rw [hcyclic]
    rw [← iso.mapRingEquiv_cyclicTIIsometry]
    rw [hbase]
    ext x
    simp [map_mul]
  exact (sign_and_irreducible_eq_of_smul_eq
    (h.primeTISign_isSign iso j')
    (h.primeTISign_isSign iso j) heq).2

end PrimeTIHypothesis

end

end Submission.OddOrder.PF
