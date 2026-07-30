import Submission.OddOrder.PF.Section01.IrreducibleCharacterTranslationKernel
import Submission.OddOrder.PF.Section01.NonzeroCharacterConstituent
import Submission.OddOrder.PF.Section04.PrimeTIDegreeAndAutomorphisms

/-!
# Structure of the reduced prime-TI columns

This file ports the remainder of Peterfalvi 4.4 and 4.5(a), from the
pairing formulas for the reduced columns through injectivity of their
irreducible restrictions to the Frobenius kernel.

The source uses inequalities in the ordered field of complex character
values.  Our coefficient field is an arbitrary algebraically closed field
of characteristic zero, so the degree comparison in `prTIres_spec` is
performed in `Nat`: ordinary virtual characters have nonnegative integral
coefficients, and evaluation at one is their dimension.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical
open CategoryTheory

universe u

variable {Gamma k : Type u} [Group Gamma] [Fintype Gamma]
  [Field k] [IsAlgClosed k] [CharZero k]
  {L K W W₁ W₂ : Subgroup Gamma}
  {defW : IsInternalDirectProductIn W₁ W₂ W}

local instance primeTIReducedStructureInvertibleCard
    {H : Type u} [Group H] [Fintype H] :
    Invertible (Nat.card H : k) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

private theorem irreducibleCharacter_finrank_pos
    {G : Type u} [Group G]
    (chi : IrreducibleCharacter G k) :
    0 < Module.finrank k chi.representation := by
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Nontrivial chi.representation := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    apply CategoryTheory.id_nonzero chi.representation
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro x
    exact Subsingleton.elim _ _
  exact Module.finrank_pos

/-- The integral degree of a virtual character. -/
private noncomputable def virtualDegree
    {G : Type u} [Group G] : VirtualCharacter G k →+ ℤ where
  toFun v := v.sum fun chi z ↦
    z * (Module.finrank k chi.representation : ℤ)
  map_zero' := by simp
  map_add' f g := by
    apply Finsupp.sum_add_index'
    · intro chi
      simp
    · intro chi a b
      simp [add_mul]

private theorem realize_one_eq_cast_virtualDegree
    {G : Type u} [Group G] [Fintype G]
    (v : VirtualCharacter G k) :
    VirtualCharacter.realize v 1 = (virtualDegree v : k) := by
  classical
  induction v using Finsupp.induction with
  | zero => simp [virtualDegree]
  | single_add chi z v hchi hz ih =>
      rw [VirtualCharacter.realize_add, map_add,
        ClassFunction.add_apply,
        VirtualCharacter.realize_single, ClassFunction.smul_apply,
        smul_eq_mul, ih]
      simp [virtualDegree, hchi,
        IrreducibleCharacter.apply_one_eq_finrank]

@[simp]
private theorem virtualCharacter_ofFDRep_apply
    {G : Type u} [Group G] [Fintype G]
    (V : FDRep k G) (chi : IrreducibleCharacter G k) :
    VirtualCharacter.ofFDRep V chi = (chi.multiplicity V : ℤ) := by
  simp [VirtualCharacter.ofFDRep]

private theorem virtualDegree_ofFDRep
    {G : Type u} [Group G] [Fintype G]
    (V : FDRep k G) :
    virtualDegree (VirtualCharacter.ofFDRep V) =
      (Module.finrank k V : ℤ) := by
  have hvalue := congrArg (fun f : ClassFunction G k ↦ f 1)
    (VirtualCharacter.realize_ofFDRep V)
  rw [realize_one_eq_cast_virtualDegree] at hvalue
  change (virtualDegree (VirtualCharacter.ofFDRep V) : k) =
    V.character 1 at hvalue
  rw [FDRep.char_one] at hvalue
  exact Int.cast_injective (by
    simpa only [Int.cast_natCast] using hvalue)

private theorem virtualDegree_nonneg_of_ordinary
    {G : Type u} [Group G] [Fintype G]
    {v : VirtualCharacter G k} (hv : v.IsOrdinary) :
    0 ≤ virtualDegree v := by
  change 0 ≤ v.sum fun chi z ↦
    z * (Module.finrank k chi.representation : ℤ)
  exact Finsupp.sum_nonneg fun chi _ ↦
    mul_nonneg (hv chi) (Int.natCast_nonneg _)

/-- A coefficientwise nonnegative virtual character of degree zero is zero. -/
private theorem ordinary_eq_zero_of_virtualDegree_eq_zero
    {G : Type u} [Group G] [Fintype G]
    (v : VirtualCharacter G k) (hv : v.IsOrdinary)
    (hdegree : virtualDegree v = 0) : v = 0 := by
  classical
  apply Finsupp.ext
  intro chi
  by_contra hchi
  have hcoeff : 0 < v chi := lt_of_le_of_ne (hv chi) (Ne.symm hchi)
  have hfinrank :
      0 < (Module.finrank k chi.representation : ℤ) := by
    exact_mod_cast irreducibleCharacter_finrank_pos chi
  have hterm :
      0 < v chi * (Module.finrank k chi.representation : ℤ) :=
    mul_pos hcoeff hfinrank
  have hle :
      v chi * (Module.finrank k chi.representation : ℤ) ≤
        virtualDegree v := by
    change v chi * (Module.finrank k chi.representation : ℤ) ≤
      v.support.sum (fun psi ↦
        v psi * (Module.finrank k psi.representation : ℤ))
    exact Finset.single_le_sum
      (s := v.support)
      (f := fun psi : IrreducibleCharacter G k ↦
        v psi * (Module.finrank k psi.representation : ℤ))
      (fun psi _ ↦ mul_nonneg (hv psi) (Int.natCast_nonneg _))
      (Finsupp.mem_support_iff.mpr hchi)
  rw [hdegree] at hle
  exact (not_lt_of_ge hle) hterm

private theorem sign_and_irreducible_eq_of_smul_eq
    {G : Type u} [Group G] [Fintype G]
    {epsilon delta : ℤ} {chi psi : IrreducibleCharacter G k}
    (hepsilon : IsSign epsilon) (hdelta : IsSign delta)
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

private theorem cyclicTICharacter_dual
    (i : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k) :
    IrreducibleCharacter.cyclicTICharacter defW
        (IrreducibleCharacter.dual i) (IrreducibleCharacter.dual j) =
      IrreducibleCharacter.dual
        (IrreducibleCharacter.cyclicTICharacter defW i j) := by
  ext w
  simp [IrreducibleCharacter.cyclicTICharacter_apply]

private theorem coe_dual_eq_inverseLinear
    {G : Type u} [Group G] [Fintype G]
    (chi : IrreducibleCharacter G k) :
    (IrreducibleCharacter.dual chi : ClassFunction G k) =
      ClassFunction.inverseLinear (chi : ClassFunction G k) := by
  ext x
  simp

namespace PrimeTIHypothesis

variable (h : PrimeTIHypothesis L K W W₁ W₂ defW)
  (iso : CyclicTIIsometryData (k := k) h.prime_cycTIhyp)

/-! ## Pairings, degree, and injectivity of reduced columns -/

/-- Pairing one rectangle entry with a reduced column. -/
theorem cfdot_prTIirr_red
    (i : IrreducibleCharacter W₁ k)
    (j r : IrreducibleCharacter W₂ k) :
    characterPairing (h.primeTICharacter iso i j)
        (h.primeTIRed iso r) = if j = r then 1 else 0 := by
  rw [h.primeTIRed_eq_sum]
  change characterPairingLeft
      (h.primeTICharacter iso i j)
      (∑ a : IrreducibleCharacter W₁ k,
        h.primeTICharacter iso a r) = _
  rw [map_sum]
  change (∑ a : IrreducibleCharacter W₁ k,
    characterPairing
      (h.primeTIIndex iso (i, j) : ClassFunction L k)
      (h.primeTIIndex iso (a, r) : ClassFunction L k)) = _
  by_cases hjr : j = r
  · subst r
    have heq (a : IrreducibleCharacter W₁ k) :
        h.primeTIIndex iso (i, j) = h.primeTIIndex iso (a, j) ↔
          i = a := by
      constructor
      · intro hidx
        exact congrArg Prod.fst ((h.primeTIirr_spec iso).1 hidx)
      · rintro rfl
        rfl
    simp [IrreducibleCharacter.characterPairing_eq_ite, heq]
  · have hne (a : IrreducibleCharacter W₁ k) :
        h.primeTIIndex iso (i, j) ≠ h.primeTIIndex iso (a, r) := by
      intro hidx
      exact hjr (congrArg Prod.snd ((h.primeTIirr_spec iso).1 hidx))
    simp [IrreducibleCharacter.characterPairing_eq_ite, hne, hjr]

/-- Pairing two reduced columns. -/
theorem cfdot_prTIred
    (j r : IrreducibleCharacter W₂ k) :
    characterPairing (h.primeTIRed iso j) (h.primeTIRed iso r) =
      if j = r then (Nat.card W₁ : k) else 0 := by
  letI : IsCyclic W₁ := h.complement_cyclic
  rw [h.primeTIRed_eq_sum]
  change characterPairingRight (h.primeTIRed iso r)
      (∑ i : IrreducibleCharacter W₁ k,
        h.primeTICharacter iso i j) = _
  rw [map_sum]
  change (∑ i : IrreducibleCharacter W₁ k,
    characterPairing (h.primeTICharacter iso i j)
      (h.primeTIRed iso r)) = _
  simp_rw [h.cfdot_prTIirr_red iso]
  by_cases hjr : j = r
  · subst r
    simp [IrreducibleCharacter.card_eq_natCard_of_isCyclic]
  · simp [hjr]

/-- The norm of a reduced column is the order of the left factor. -/
theorem cfnorm_prTIred (j : IrreducibleCharacter W₂ k) :
    characterPairing (h.primeTIRed iso j) (h.primeTIRed iso j) =
      (Nat.card W₁ : k) := by
  simpa using h.cfdot_prTIred iso j j

/-- No reduced column is zero. -/
theorem prTIred_neq0 (j : IrreducibleCharacter W₂ k) :
    h.primeTIRed iso j ≠ 0 := by
  intro hzero
  have hnorm := h.cfnorm_prTIred iso j
  rw [hzero, characterPairing_zero_left] at hnorm
  exact (Nat.cast_ne_zero.mpr Nat.card_pos.ne') hnorm.symm

/-- The reduced degree is a cast of a strictly positive natural number.
This is the ordered-field-free form of source `prTIred_1_gt0`. -/
theorem prTIred_1_gt0 (j : IrreducibleCharacter W₂ k) :
    ∃ n : ℕ, 0 < n ∧ h.primeTIRed iso j 1 = (n : k) := by
  let n := ∑ i : IrreducibleCharacter W₁ k,
    Module.finrank k (h.primeTIIndex iso (i, j)).representation
  letI : Nonempty (IrreducibleCharacter W₁ k) :=
    ⟨IrreducibleCharacter.trivial⟩
  have hn : 0 < n := by
    exact Finset.sum_pos
      (fun i _ ↦ irreducibleCharacter_finrank_pos
        (h.primeTIIndex iso (i, j)))
      Finset.univ_nonempty
  refine ⟨n, hn, ?_⟩
  rw [h.primeTIRed_eq_sum]
  simp [n, primeTICharacter,
    IrreducibleCharacter.apply_one_eq_finrank]

/-- The degree of a reduced column is nonzero. -/
theorem prTIred_1_neq0 (j : IrreducibleCharacter W₂ k) :
    h.primeTIRed iso j 1 ≠ 0 := by
  obtain ⟨n, hn, hdegree⟩ := h.prTIred_1_gt0 iso j
  rw [hdegree]
  exact Nat.cast_ne_zero.mpr hn.ne'

/-- Distinct right indices give distinct reduced columns. -/
theorem prTIred_inj : Function.Injective (h.primeTIRed iso) := by
  intro j r hjr
  by_contra hne
  have hpair := congrArg
    (fun f : ClassFunction L k ↦
      characterPairing (h.primeTIRed iso j) f) hjr
  rw [h.cfdot_prTIred iso, h.cfdot_prTIred iso,
    if_pos rfl, if_neg hne] at hpair
  exact (Nat.cast_ne_zero.mpr Nat.card_pos.ne') hpair

/-! ## Duality and the trivial rectangle entry -/

/-- Inversion preserves the prime-TI sign after dualizing the column. -/
theorem primeTISign_dual (j : IrreducibleCharacter W₂ k) :
    h.primeTISign iso (IrreducibleCharacter.dual j) =
      h.primeTISign iso j := by
  let i : IrreducibleCharacter W₁ k := IrreducibleCharacter.trivial
  let mu := h.primeTIIndex iso (i, j)
  let mu' := h.primeTIIndex iso
    (IrreducibleCharacter.dual i, IrreducibleCharacter.dual j)
  have hbase := (h.primeTICharacterData iso).isometry_character i j
  have htarget := (h.primeTICharacterData iso).isometry_character
    (IrreducibleCharacter.dual i) (IrreducibleCharacter.dual j)
  have heq :
      (h.primeTISign iso (IrreducibleCharacter.dual j) : k) •
          (mu' : ClassFunction L k) =
        (h.primeTISign iso j : k) •
          (IrreducibleCharacter.dual mu : ClassFunction L k) := by
    change
      ((h.primeTICharacterData iso).sign
          (IrreducibleCharacter.dual j) : k) •
          ((h.primeTICharacterData iso).index
            (IrreducibleCharacter.dual i,
              IrreducibleCharacter.dual j) : ClassFunction L k) =
        ((h.primeTICharacterData iso).sign j : k) •
          (IrreducibleCharacter.dual
            ((h.primeTICharacterData iso).index (i, j)) :
              ClassFunction L k)
    rw [← htarget, cyclicTICharacter_dual,
      coe_dual_eq_inverseLinear, coe_dual_eq_inverseLinear]
    rw [← iso.inverse_cyclicTIIsometry]
    rw [hbase]
    ext x
    simp
  exact (sign_and_irreducible_eq_of_smul_eq
    (h.primeTISign_isSign iso (IrreducibleCharacter.dual j))
    (h.primeTISign_isSign iso j) heq).1

/-- Duality acts componentwise on the prime-TI rectangle. -/
theorem primeTIIndex_dual
    (i : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k) :
    h.primeTIIndex iso
        (IrreducibleCharacter.dual i, IrreducibleCharacter.dual j) =
      IrreducibleCharacter.dual (h.primeTIIndex iso (i, j)) := by
  let mu := h.primeTIIndex iso (i, j)
  let mu' := h.primeTIIndex iso
    (IrreducibleCharacter.dual i, IrreducibleCharacter.dual j)
  have hbase := (h.primeTICharacterData iso).isometry_character i j
  have htarget := (h.primeTICharacterData iso).isometry_character
    (IrreducibleCharacter.dual i) (IrreducibleCharacter.dual j)
  have heq :
      (h.primeTISign iso (IrreducibleCharacter.dual j) : k) •
          (mu' : ClassFunction L k) =
        (h.primeTISign iso j : k) •
          (IrreducibleCharacter.dual mu : ClassFunction L k) := by
    change
      ((h.primeTICharacterData iso).sign
          (IrreducibleCharacter.dual j) : k) •
          ((h.primeTICharacterData iso).index
            (IrreducibleCharacter.dual i,
              IrreducibleCharacter.dual j) : ClassFunction L k) =
        ((h.primeTICharacterData iso).sign j : k) •
          (IrreducibleCharacter.dual
            ((h.primeTICharacterData iso).index (i, j)) :
              ClassFunction L k)
    rw [← htarget, cyclicTICharacter_dual,
      coe_dual_eq_inverseLinear, coe_dual_eq_inverseLinear]
    rw [← iso.inverse_cyclicTIIsometry]
    rw [hbase]
    ext x
    simp
  exact (sign_and_irreducible_eq_of_smul_eq
    (h.primeTISign_isSign iso (IrreducibleCharacter.dual j))
    (h.primeTISign_isSign iso j) heq).2

/-- Inversion of a reduced column dualizes its right index. -/
theorem primeTIRed_inverseLinear (j : IrreducibleCharacter W₂ k) :
    ClassFunction.inverseLinear (h.primeTIRed iso j) =
      h.primeTIRed iso (IrreducibleCharacter.dual j) := by
  rw [h.primeTIRed_eq_sum, h.primeTIRed_eq_sum, map_sum]
  apply Fintype.sum_equiv IrreducibleCharacter.dualEquiv
  intro i
  change ClassFunction.inverseLinear
      (h.primeTIIndex iso (i, j) : ClassFunction L k) =
    (h.primeTIIndex iso
      (IrreducibleCharacter.dual i, IrreducibleCharacter.dual j) :
        ClassFunction L k)
  rw [h.primeTIIndex_dual iso]
  ext x
  simp

/-- Source-name form of inversion compatibility for a reduced column. -/
theorem prTIred_aut (j : IrreducibleCharacter W₂ k) :
    ClassFunction.inverseLinear (h.primeTIRed iso j) =
      h.primeTIRed iso (IrreducibleCharacter.dual j) :=
  h.primeTIRed_inverseLinear iso j

/-- A nontrivial reduced column is not fixed by inversion. -/
theorem prTIred_not_real
    {j : IrreducibleCharacter W₂ k}
    (hj : j ≠ IrreducibleCharacter.trivial) :
    ClassFunction.inverseLinear (h.primeTIRed iso j) ≠
      h.primeTIRed iso j := by
  intro hreal
  rw [h.prTIred_aut iso] at hreal
  have hdual : IrreducibleCharacter.dual j = j :=
    h.prTIred_inj iso hreal
  exact (dual_ne_self_of_odd_of_ne_trivial h.fixed_odd_card hj) hdual

/-- Source `prTIsign0`: the trivial column has positive sign. -/
@[simp]
theorem prTIsign0 :
    h.primeTISign iso
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ k) = 1 := by
  let i : IrreducibleCharacter W₁ k := IrreducibleCharacter.trivial
  let j : IrreducibleCharacter W₂ k := IrreducibleCharacter.trivial
  have heq := (h.primeTICharacterData iso).isometry_character i j
  change iso.linearMap
      (IrreducibleCharacter.cyclicTICharacter defW i j :
        ClassFunction W k) =
    (h.primeTISign iso j : k) •
      (h.primeTIIndex iso (i, j) : ClassFunction L k) at heq
  rw [IrreducibleCharacter.cyclicTICharacter_trivial,
    iso.map_trivial] at heq
  have hsplit := sign_and_irreducible_eq_of_smul_eq
    (epsilon := (1 : ℤ)) (delta := h.primeTISign iso j)
    (chi := (IrreducibleCharacter.trivial : IrreducibleCharacter L k))
    (psi := h.primeTIIndex iso (i, j))
    (show IsSign (1 : ℤ) by simp [IsSign])
    (h.primeTISign_isSign iso j)
    (show ((1 : ℤ) : k) •
        ((IrreducibleCharacter.trivial : IrreducibleCharacter L k) :
          ClassFunction L k) =
      (h.primeTISign iso j : k) •
        (h.primeTIIndex iso (i, j) : ClassFunction L k) by
      simpa using heq)
  exact hsplit.1.symm

/-- Source `prTIirr00`: the trivial rectangle entry is trivial. -/
@[simp]
theorem prTIirr00 :
    h.primeTIIndex iso
        ((IrreducibleCharacter.trivial : IrreducibleCharacter W₁ k),
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ k)) =
      (IrreducibleCharacter.trivial : IrreducibleCharacter L k) := by
  let i : IrreducibleCharacter W₁ k := IrreducibleCharacter.trivial
  let j : IrreducibleCharacter W₂ k := IrreducibleCharacter.trivial
  have heq := (h.primeTICharacterData iso).isometry_character i j
  change iso.linearMap
      (IrreducibleCharacter.cyclicTICharacter defW i j :
        ClassFunction W k) =
    (h.primeTISign iso j : k) •
      (h.primeTIIndex iso (i, j) : ClassFunction L k) at heq
  rw [IrreducibleCharacter.cyclicTICharacter_trivial,
    iso.map_trivial] at heq
  have hsplit := sign_and_irreducible_eq_of_smul_eq
    (epsilon := (1 : ℤ)) (delta := h.primeTISign iso j)
    (chi := (IrreducibleCharacter.trivial : IrreducibleCharacter L k))
    (psi := h.primeTIIndex iso (i, j))
    (show IsSign (1 : ℤ) by simp [IsSign])
    (h.primeTISign_isSign iso j)
    (show ((1 : ℤ) : k) •
        ((IrreducibleCharacter.trivial : IrreducibleCharacter L k) :
          ClassFunction L k) =
      (h.primeTISign iso j : k) •
        (h.primeTIIndex iso (i, j) : ClassFunction L k) by
      simpa using heq)
  exact hsplit.2.symm

/-! ## Equality of the restrictions in a column -/

private theorem mem_fixed_of_mem_kernel_of_mem_directProduct
    (h : PrimeTIHypothesis L K W W₁ W₂ defW)
    {x : Gamma} (hxK : x ∈ K) (hxW : x ∈ W) : x ∈ W₂ := by
  let w : W := ⟨x, hxW⟩
  let p : W₁ × W₂ := defW.mulEquiv.symm w
  have hxdecomp : x = (p.1 : Gamma) * (p.2 : Gamma) := by
    have hp := defW.coe_mulEquiv_apply p
    rw [defW.mulEquiv.apply_symm_apply] at hp
    simpa [w] using hp
  have hp₁K : (p.1 : Gamma) ∈ K := by
    have hp₁eq : (p.1 : Gamma) = x * (p.2 : Gamma)⁻¹ := by
      rw [hxdecomp]
      group
    rw [hp₁eq]
    exact K.mul_mem hxK
      (K.inv_mem (h.fixed_le_kernel p.2.property))
  have hp₁one : p.1 = 1 := by
    have hdisjoint : Disjoint K W₁ :=
      Subgroup.disjoint_of_coprime_natCard
        h.kernel_complement_card_coprime
    apply Subtype.ext
    apply Subgroup.mem_bot.mp
    rw [← disjoint_iff.mp hdisjoint]
    exact ⟨hp₁K, p.1.property⟩
  have hwW₂ : (w : Gamma) ∈ W₂ := by
    have hp := (defW.mulEquiv_mem_right_iff p).mpr hp₁one
    simpa [w, p] using hp
  exact hwW₂

/-- First part of Peterfalvi 4.5(a): all entries in one column have the
same restriction to the Frobenius kernel. -/
theorem cfRes_prTIirr_eq0
    (i : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k) :
    ClassFunction.restrict (K.subgroupOf L)
        (h.primeTICharacter iso i j) =
      ClassFunction.restrict (K.subgroupOf L)
        (h.primeTICharacter iso IrreducibleCharacter.trivial j) := by
  apply ClassFunction.ext
  intro x
  have hinduced :
      (h.prime_cycTIhyp).induceClassFunction
          (VirtualCharacter.realize (primeTIDifference defW i j)) (x : L) =
        0 := by
    rw [CyclicTIHypothesis.induceClassFunction_apply,
      ClassFunction.induce_apply_formula]
    have hsum :
        (∑ y : L,
          if hy : y⁻¹ * (x : L) * y ∈ W.subgroupOf L then
            ClassFunction.toSubgroupOf W L h.directProduct_le_group
              (VirtualCharacter.realize (primeTIDifference defW i j))
              ⟨y⁻¹ * (x : L) * y, hy⟩
          else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro y _
      split_ifs with hy
      · let z : L := y⁻¹ * (x : L) * y
        let zW : W.subgroupOf L := ⟨z, hy⟩
        let w : W :=
          Subgroup.subgroupOfEquivOfLe h.directProduct_le_group zW
        have hzKsub : z ∈ K.subgroupOf L := by
          simpa [z] using h.kernel_normal.conj_mem x x.property y⁻¹
        have hwW₂ : (w : Gamma) ∈ W₂ := by
          apply mem_fixed_of_mem_kernel_of_mem_directProduct h
          · exact hzKsub
          · exact w.property
        have hnot : w ∉ primeTISetInW W W₂ := by
          intro hw
          exact (mem_primeTISetInW.mp hw) hwW₂
        have hsupp := h.primeTIDifference_mem_supportedOn i j
        rw [ClassFunction.mem_supportedOn_iff] at hsupp
        rw [ClassFunction.toSubgroupOf_apply]
        exact hsupp w hnot
      · rfl
    rw [hsum, mul_zero]
  have hdiff := congrArg (fun f : ClassFunction L k ↦ f (x : L))
    ((h.primeTICharacterData iso).induce_difference i j)
  rw [hinduced, ClassFunction.smul_apply, ClassFunction.sub_apply,
    smul_eq_mul] at hdiff
  have hsign : (h.primeTISign iso j : k) ≠ 0 :=
    Int.cast_ne_zero.mpr
      (isSign_ne_zero (h.primeTISign_isSign iso j))
  exact sub_eq_zero.mp
    ((mul_eq_zero.mp hdiff.symm).resolve_left hsign)

/-- All entries in a column have the same degree. -/
theorem prTIirr_1
    (i : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k) :
    h.primeTICharacter iso i j 1 =
      h.primeTICharacter iso IrreducibleCharacter.trivial j 1 := by
  have hres := congrArg (fun f : ClassFunction (K.subgroupOf L) k ↦ f 1)
    (h.cfRes_prTIirr_eq0 iso i j)
  simpa using hres

/-- Every entry of the trivial right column has degree one. -/
@[simp]
theorem prTIirr0_1 (i : IrreducibleCharacter W₁ k) :
    h.primeTICharacter iso i
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ k) 1 = 1 := by
  rw [h.prTIirr_1 iso]
  change h.primeTIIndex iso
      ((IrreducibleCharacter.trivial : IrreducibleCharacter W₁ k),
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ k)) 1 = 1
  rw [h.prTIirr00 iso]
  simp

/-- Lean's intrinsic form of `linear_char`: the realizing representation
has dimension one. -/
theorem prTIirr0_linear (i : IrreducibleCharacter W₁ k) :
    Module.finrank k
        (h.primeTIIndex iso
          (i, (IrreducibleCharacter.trivial :
            IrreducibleCharacter W₂ k))).representation = 1 := by
  have hone := h.prTIirr0_1 iso i
  rw [primeTICharacter,
    IrreducibleCharacter.apply_one_eq_finrank] at hone
  apply Nat.cast_injective (R := k)
  simpa using hone

/-- Degree of a reduced column. -/
theorem prTIred_1 (j : IrreducibleCharacter W₂ k) :
    h.primeTIRed iso j 1 =
      (Nat.card W₁ : k) *
        h.primeTICharacter iso IrreducibleCharacter.trivial j 1 := by
  letI : IsCyclic W₁ := h.complement_cyclic
  rw [h.primeTIRed_eq_sum]
  simp_rw [ClassFunction.finset_sum_apply, h.prTIirr_1 iso]
  rw [Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ, IrreducibleCharacter.card_eq_natCard_of_isCyclic]

/-! ## The irreducible restriction and its induction -/

private theorem exists_prTIres_constituent
    (j : IrreducibleCharacter W₂ k) :
    ∃ theta : IrreducibleCharacter (K.subgroupOf L) k,
      theta.IsConstituent
        (ClassFunction.restrict (K.subgroupOf L)
          (h.primeTICharacter iso IrreducibleCharacter.trivial j)) := by
  let mu := h.primeTIIndex iso
    ((IrreducibleCharacter.trivial : IrreducibleCharacter W₁ k), j)
  let R : FDRep k (K.subgroupOf L) :=
    FDRep.restrictToSubgroup (K.subgroupOf L) mu.representation
  letI : CategoryTheory.Simple mu.representation :=
    mu.representation_simple
  letI : Nontrivial mu.representation := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    apply CategoryTheory.id_nonzero mu.representation
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro x
    exact Subsingleton.elim _ _
  letI : Nontrivial R :=
    inferInstanceAs (Nontrivial mu.representation)
  obtain ⟨theta, htheta⟩ :=
    ClassFunction.exists_irreducible_constituent_of_nontrivial R
  refine ⟨theta, ?_⟩
  change theta.IsConstituent
    (ClassFunction.restrict (K.subgroupOf L)
      (mu : ClassFunction L k))
  rw [← mu.ofRepresentation_representation,
    ← FDRep.ofRepresentation_restrictToSubgroup]
  exact htheta

/-- The selected irreducible constituent of the trivial-left restriction.
The theorem `prTIres_spec` below shows that the whole restriction is this
single constituent. -/
def primeTI_Ires
    (j : IrreducibleCharacter W₂ k) :
    IrreducibleCharacter (K.subgroupOf L) k :=
  Classical.choose (h.exists_prTIres_constituent iso j)

private theorem primeTI_Ires_isConstituent
    (j : IrreducibleCharacter W₂ k) :
    (h.primeTI_Ires iso j).IsConstituent
      (ClassFunction.restrict (K.subgroupOf L)
        (h.primeTICharacter iso IrreducibleCharacter.trivial j)) :=
  Classical.choose_spec (h.exists_prTIres_constituent iso j)

private theorem primeTIRedVirtualCharacter_apply_index
    (i : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k) :
    h.primeTIRedVirtualCharacter iso j
        (h.primeTIIndex iso (i, j)) = 1 := by
  classical
  rw [primeTIRedVirtualCharacter, Finsupp.finsetSum_apply]
  have hsum :
      (∑ a : IrreducibleCharacter W₁ k,
        (Finsupp.single (h.primeTIIndex iso (a, j)) 1 :
          VirtualCharacter L k) (h.primeTIIndex iso (i, j))) =
        (Finsupp.single (h.primeTIIndex iso (i, j)) 1 :
          VirtualCharacter L k) (h.primeTIIndex iso (i, j)) := by
    apply Finset.sum_eq_single i
    · intro a _ hai
      rw [Finsupp.single_apply, if_neg]
      intro heq
      have hpairs := (h.primeTIirr_spec iso).1 heq
      exact hai (congrArg Prod.fst hpairs)
    · simp
  rw [hsum]
  simp

private theorem primeTIRedVirtualCharacter_apply_eq_zero
    (j : IrreducibleCharacter W₂ k)
    (chi : IrreducibleCharacter L k)
    (hchi : ∀ i : IrreducibleCharacter W₁ k,
      h.primeTIIndex iso (i, j) ≠ chi) :
    h.primeTIRedVirtualCharacter iso j chi = 0 := by
  simp [primeTIRedVirtualCharacter, Finsupp.single_apply, hchi]

/-- The rest of Peterfalvi 4.5(a): the selected constituent is the entire
restriction, and its induction is the reduced column. -/
theorem prTIres_spec (j : IrreducibleCharacter W₂ k) :
    ((h.primeTI_Ires iso j :
        IrreducibleCharacter (K.subgroupOf L) k) :
          ClassFunction (K.subgroupOf L) k) =
        ClassFunction.restrict (K.subgroupOf L)
          (h.primeTICharacter iso IrreducibleCharacter.trivial j) ∧
      h.primeTIRed iso j =
        ClassFunction.induce (K.subgroupOf L)
          (h.primeTI_Ires iso j :
            ClassFunction (K.subgroupOf L) k) := by
  let H : Subgroup L := K.subgroupOf L
  let mu := h.primeTIIndex iso
    ((IrreducibleCharacter.trivial : IrreducibleCharacter W₁ k), j)
  let theta := h.primeTI_Ires iso j
  let R : FDRep k H := FDRep.restrictToSubgroup H mu.representation
  let I : FDRep k L := FDRep.induceFromSubgroup H theta.representation
  let vI : VirtualCharacter L k := VirtualCharacter.ofFDRep I
  let vRed : VirtualCharacter L k := h.primeTIRedVirtualCharacter iso j
  have hRchar :
      ClassFunction.ofRepresentation R.ρ =
        ClassFunction.restrict H (mu : ClassFunction L k) := by
    simpa only [R, mu.ofRepresentation_representation] using
      FDRep.ofRepresentation_restrictToSubgroup H mu.representation
  have htheta : theta.IsConstituent
      (ClassFunction.ofRepresentation R.ρ) := by
    rw [hRchar]
    exact h.primeTI_Ires_isConstituent iso j
  have hIchar :
      ClassFunction.ofRepresentation I.ρ =
        ClassFunction.induce H (theta : ClassFunction H k) := by
    exact (ClassFunction.ofRepresentation_induceFromSubgroup_general
      H theta.representation).trans
        (congrArg (ClassFunction.induce H)
          theta.ofRepresentation_representation)
  have hmu_constituent (i : IrreducibleCharacter W₁ k) :
      (h.primeTIIndex iso (i, j)).IsConstituent
        (ClassFunction.ofRepresentation I.ρ) := by
    rw [hIchar]
    apply ((theta.isConstituent_restrict_iff_induce H
      (h.primeTIIndex iso (i, j))).mp)
    have hres := h.cfRes_prTIirr_eq0 iso i j
    change ClassFunction.restrict H
      (h.primeTIIndex iso (i, j) : ClassFunction L k) =
        ClassFunction.restrict H (mu : ClassFunction L k) at hres
    rw [hres]
    rw [← hRchar]
    exact htheta
  have hmu_multiplicity (i : IrreducibleCharacter W₁ k) :
      0 < (h.primeTIIndex iso (i, j)).multiplicity I := by
    exact ((h.primeTIIndex iso (i, j)).isConstituent_ofRepresentation_iff_multiplicity_pos I).mp
      (hmu_constituent i)
  have hvDiff_ordinary : (vI - vRed).IsOrdinary := by
    intro chi
    by_cases hchi : ∃ i : IrreducibleCharacter W₁ k,
        h.primeTIIndex iso (i, j) = chi
    · obtain ⟨i, rfl⟩ := hchi
      rw [Finsupp.sub_apply, virtualCharacter_ofFDRep_apply,
        h.primeTIRedVirtualCharacter_apply_index iso]
      have hm : (1 : ℤ) ≤
          ((h.primeTIIndex iso (i, j)).multiplicity I : ℤ) := by
        exact_mod_cast hmu_multiplicity i
      omega
    · have hchi' : ∀ i : IrreducibleCharacter W₁ k,
          h.primeTIIndex iso (i, j) ≠ chi := by
        intro i hi
        exact hchi ⟨i, hi⟩
      rw [Finsupp.sub_apply, virtualCharacter_ofFDRep_apply,
        h.primeTIRedVirtualCharacter_apply_eq_zero iso j chi hchi',
        sub_zero]
      exact Int.natCast_nonneg _
  have hdim_column (i : IrreducibleCharacter W₁ k) :
      Module.finrank k
          (h.primeTIIndex iso (i, j)).representation =
        Module.finrank k mu.representation := by
    have hdegree := h.prTIirr_1 iso i j
    change (h.primeTIIndex iso (i, j) : IrreducibleCharacter L k) 1 =
      mu 1 at hdegree
    rw [IrreducibleCharacter.apply_one_eq_finrank,
      IrreducibleCharacter.apply_one_eq_finrank] at hdegree
    apply Nat.cast_injective (R := k)
    simpa using hdegree
  have hdegreeRed : virtualDegree vRed =
      (Nat.card W₁ : ℤ) *
        (Module.finrank k mu.representation : ℤ) := by
    letI : IsCyclic W₁ := h.complement_cyclic
    simp [vRed, primeTIRedVirtualCharacter, virtualDegree,
      hdim_column,
      IrreducibleCharacter.card_eq_natCard_of_isCyclic]
  have hdegreeI : virtualDegree vI =
      (Module.finrank k I : ℤ) := by
    exact virtualDegree_ofFDRep I
  have hindex : H.index = Nat.card W₁ := by
    simpa only [H,
      _root_.Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
        h.complement_le_group] using
      h.semidirect_complement.symm.index_eq_card
  have hdimI : Module.finrank k I =
      H.index * Module.finrank k theta.representation := by
    apply Nat.cast_injective (R := k)
    calc
      (Module.finrank k I : k) = I.character 1 :=
        (FDRep.char_one I).symm
      _ = ClassFunction.ofRepresentation I.ρ 1 := rfl
      _ = ClassFunction.induce H (theta : ClassFunction H k) 1 := by
        rw [hIchar]
      _ = (H.index : k) * theta 1 := ClassFunction.induce_one H _
      _ = (H.index : k) *
          (Module.finrank k theta.representation : k) := by
        rw [IrreducibleCharacter.apply_one_eq_finrank]
      _ = (H.index * Module.finrank k theta.representation : ℕ) := by
        rw [Nat.cast_mul]
  have htheta_le :
      Module.finrank k theta.representation ≤
        Module.finrank k mu.representation := by
    have hle := FDRep.finrank_irreducible_le_of_isConstituent R theta htheta
    change Module.finrank k theta.representation ≤
      Module.finrank k mu.representation at hle
    exact hle
  have hdegreeDiff_nonneg : 0 ≤ virtualDegree (vI - vRed) :=
    virtualDegree_nonneg_of_ordinary hvDiff_ordinary
  have hlower :
      Nat.card W₁ * Module.finrank k mu.representation ≤
        Module.finrank k I := by
    rw [map_sub, hdegreeI, hdegreeRed] at hdegreeDiff_nonneg
    have hcast :
        (Nat.card W₁ : ℤ) *
            (Module.finrank k mu.representation : ℤ) ≤
          (Module.finrank k I : ℤ) :=
      Int.sub_nonneg.mp hdegreeDiff_nonneg
    exact_mod_cast hcast
  have htheta_dim :
      Module.finrank k theta.representation =
        Module.finrank k mu.representation := by
    rw [hdimI, hindex] at hlower
    apply le_antisymm htheta_le
    exact Nat.le_of_mul_le_mul_left hlower Nat.card_pos
  have htheta_eq_restriction :
      (theta : ClassFunction H k) =
        ClassFunction.restrict H (mu : ClassFunction L k) := by
    obtain ⟨f, hf⟩ :=
      FDRep.exists_hom_ne_zero_of_isConstituent R theta htheta
    letI : CategoryTheory.Simple theta.representation :=
      theta.representation_simple
    letI : Mono f := mono_of_nonzero_from_simple hf
    let fR := (forget₂ (FDRep k H) (Rep k H)).map f
    have hinj : Function.Injective fR.hom :=
      (Rep.mono_iff_injective fR).mp (by infer_instance)
    have hdim : Module.finrank k theta.representation =
        Module.finrank k R := by
      change Module.finrank k theta.representation =
        Module.finrank k mu.representation
      exact htheta_dim
    have hsurj : Function.Surjective fR.hom :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
    let e : Representation.Equiv theta.representation.ρ R.ρ :=
      fR.hom.ofBijective ⟨hinj, hsurj⟩
    have hchars := Representation.char_iso e
    rw [← hRchar]
    apply ClassFunction.ext
    intro x
    rw [← theta.representation_character]
    exact congrFun hchars x
  have hdegreeDiff : virtualDegree (vI - vRed) = 0 := by
    rw [map_sub, hdegreeI, hdegreeRed, hdimI, hindex, htheta_dim]
    push_cast
    ring
  have hvDiff : vI - vRed = 0 :=
    ordinary_eq_zero_of_virtualDegree_eq_zero
      (vI - vRed) hvDiff_ordinary hdegreeDiff
  have hvEq : vI = vRed := sub_eq_zero.mp hvDiff
  have hinduced :
      ClassFunction.induce H (theta : ClassFunction H k) =
        h.primeTIRed iso j := by
    have hreal := congrArg VirtualCharacter.realize hvEq
    change VirtualCharacter.realize (VirtualCharacter.ofFDRep I) =
      VirtualCharacter.realize
        (h.primeTIRedVirtualCharacter iso j) at hreal
    rw [VirtualCharacter.realize_ofFDRep, hIchar] at hreal
    simpa only [primeTIRed] using hreal
  exact ⟨htheta_eq_restriction, hinduced.symm⟩

/-- Restriction of every rectangle entry is the selected kernel
irreducible. -/
theorem cfRes_prTIirr
    (i : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k) :
    ClassFunction.restrict (K.subgroupOf L)
        (h.primeTICharacter iso i j) =
      (h.primeTI_Ires iso j :
        ClassFunction (K.subgroupOf L) k) := by
  rw [h.cfRes_prTIirr_eq0 iso]
  exact (h.prTIres_spec iso j).1.symm

/-- Induction of the selected kernel irreducible is its reduced column. -/
theorem cfInd_prTIres (j : IrreducibleCharacter W₂ k) :
    ClassFunction.induce (K.subgroupOf L)
        (h.primeTI_Ires iso j : ClassFunction (K.subgroupOf L) k) =
      h.primeTIRed iso j :=
  (h.prTIres_spec iso j).2.symm

/-- Restriction of a reduced column is the left-factor order times its
selected irreducible. -/
theorem cfRes_prTIred (j : IrreducibleCharacter W₂ k) :
    ClassFunction.restrict (K.subgroupOf L) (h.primeTIRed iso j) =
      (Nat.card W₁ : k) •
        (h.primeTI_Ires iso j : ClassFunction (K.subgroupOf L) k) := by
  letI : IsCyclic W₁ := h.complement_cyclic
  rw [h.primeTIRed_eq_sum, map_sum]
  simp_rw [h.cfRes_prTIirr iso]
  rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul k,
    Finset.card_univ, IrreducibleCharacter.card_eq_natCard_of_isCyclic]

/-! ## Naturality, the trivial restriction, and injectivity -/

/-- Coefficient-field automorphisms act naturally on the selected
restrictions. -/
theorem prTIres_aut
    (sigma : k ≃+* k) (j : IrreducibleCharacter W₂ k) :
    h.primeTI_Ires iso (IrreducibleCharacter.mapRingEquiv sigma j) =
      IrreducibleCharacter.mapRingEquiv sigma (h.primeTI_Ires iso j) := by
  apply IrreducibleCharacter.ext
  intro x
  have hleft := congrArg
    (fun f : ClassFunction (K.subgroupOf L) k ↦ f x)
    (h.cfRes_prTIirr iso
      (IrreducibleCharacter.mapRingEquiv sigma
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ k))
      (IrreducibleCharacter.mapRingEquiv sigma j))
  have hright := congrArg
    (fun f : ClassFunction (K.subgroupOf L) k ↦ f x)
    (h.cfRes_prTIirr iso
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ k) j)
  change
    (ClassFunction.restrict (K.subgroupOf L)
      ((h.primeTIIndex iso
        (IrreducibleCharacter.mapRingEquiv sigma
            (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ k),
          IrreducibleCharacter.mapRingEquiv sigma j)) :
            ClassFunction L k)) x =
      (h.primeTI_Ires iso
        (IrreducibleCharacter.mapRingEquiv sigma j) :
          ClassFunction (K.subgroupOf L) k) x at hleft
  rw [h.primeTIIndex_mapRingEquiv iso] at hleft
  simp only [ClassFunction.restrict_apply,
    IrreducibleCharacter.mapRingEquiv_apply] at hleft
  simp only [ClassFunction.restrict_apply, primeTICharacter] at hright
  simpa only [IrreducibleCharacter.mapRingEquiv_apply] using
    hleft.symm.trans (congrArg sigma hright)

/-- The selected restriction in the trivial column is trivial. -/
@[simp]
theorem prTIres0 :
    h.primeTI_Ires iso
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ k) =
      (IrreducibleCharacter.trivial :
        IrreducibleCharacter (K.subgroupOf L) k) := by
  apply IrreducibleCharacter.ext
  intro x
  have hres := congrArg
    (fun f : ClassFunction (K.subgroupOf L) k ↦ f x)
    (h.cfRes_prTIirr iso
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ k)
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ k))
  rw [primeTICharacter, h.prTIirr00 iso] at hres
  simpa using hres.symm

/-- The trivial reduced column is induced from the trivial kernel
character.  This is equivalent to the source's subgroup-indicator formula. -/
theorem prTIred0 :
    h.primeTIRed iso
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ k) =
      ClassFunction.induce (K.subgroupOf L)
        ((IrreducibleCharacter.trivial :
          IrreducibleCharacter (K.subgroupOf L) k) :
            ClassFunction (K.subgroupOf L) k) := by
  rw [← h.cfInd_prTIres iso, h.prTIres0 iso]

/-- The selected restrictions have distinct indices. -/
theorem prTIres_inj : Function.Injective (h.primeTI_Ires iso) := by
  intro j r hjr
  apply h.prTIred_inj iso
  rw [← h.cfInd_prTIres iso, ← h.cfInd_prTIres iso, hjr]

/-! ## Peterfalvi 4.4: the trivial-on-kernel irreducibles -/

private theorem le_translationKernel_of_restrict_eq_trivial
    (chi : IrreducibleCharacter L k)
    (hres : ClassFunction.restrict (K.subgroupOf L)
        (chi : ClassFunction L k) =
      ((IrreducibleCharacter.trivial :
        IrreducibleCharacter (K.subgroupOf L) k) :
          ClassFunction (K.subgroupOf L) k)) :
    K.subgroupOf L ≤
      ClassFunction.translationKernel (chi : ClassFunction L k) := by
  rw [ClassFunction.translationKernel_irreducibleCharacter]
  have hdimCast :
      (Module.finrank k chi.representation : k) = 1 := by
    have hvalue := congrArg
      (fun f : ClassFunction (K.subgroupOf L) k ↦ f 1) hres
    simpa [IrreducibleCharacter.apply_one_eq_finrank] using hvalue
  have hdim : Module.finrank k chi.representation = 1 :=
    by
      apply Nat.cast_injective (R := k)
      simpa using hdimCast
  intro x hx
  rw [MonoidHom.mem_ker]
  have hvalue := congrArg
    (fun f : ClassFunction (K.subgroupOf L) k ↦ f ⟨x, hx⟩) hres
  have hchar : Representation.character chi.representation.ρ x = 1 := by
    change chi.representation.character x = 1
    rw [chi.representation_character]
    simpa using hvalue
  obtain ⟨a, ha, _⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim
      (chi.representation.ρ x)
  change LinearMap.trace k chi.representation
      (chi.representation.ρ x) = 1 at hchar
  rw [ha, map_smul, LinearMap.trace_id, hdim] at hchar
  simp only [Nat.cast_one, smul_eq_mul, mul_one] at hchar
  rw [ha, hchar, one_smul]
  rfl

private theorem complement_restriction_isIrreducible
    (chi : IrreducibleCharacter L k)
    (hker : K.subgroupOf L ≤
      ClassFunction.translationKernel (chi : ClassFunction L k)) :
    Representation.IsIrreducible
      (chi.representation.ρ.comp
        (Subgroup.inclusion h.complement_le_group)) := by
  let rho := chi.representation.ρ
  let inc : W₁ →* L := Subgroup.inclusion h.complement_le_group
  let tau : Representation k W₁ chi.representation := rho.comp inc
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Representation.IsIrreducible rho := by
    exact Submission.OddOrder.MathlibSupport.representation_isIrreducible_of_simple_fdRep
      chi.representation
  have hkerRho : K.subgroupOf L ≤ rho.ker := by
    rw [← ClassFunction.translationKernel_irreducibleCharacter chi]
    exact hker
  let liftSub (U : Subrepresentation tau) : Subrepresentation rho :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule := by
        intro l v hv
        rcases h.semidirect_complement.2 l with
          ⟨⟨kL, xL⟩, hkxL⟩
        let x : W₁ := ⟨((xL : L) : Gamma), xL.property⟩
        have hk : rho (kL : L) = 1 :=
          MonoidHom.mem_ker.mp (hkerRho kL.property)
        have hx : inc x = (xL : L) := rfl
        rw [← hkxL, map_mul, hk, one_mul, ← hx]
        exact U.apply_mem_toSubmodule x hv }
  change Representation.IsIrreducible tau
  refine { toNontrivial := ?_, eq_bot_or_eq_top := ?_ }
  · refine ⟨⊥, ⊤, fun hEq ↦ ?_⟩
    have hEq' := congrArg Subrepresentation.toSubmodule hEq
    apply (show (⊥ : Subrepresentation rho) ≠ ⊤ from bot_ne_top)
    apply Subrepresentation.toSubmodule_injective
    exact hEq'
  · intro U
    rcases eq_bot_or_eq_top (liftSub U) with hU | hU
    · left
      have hU' := congrArg Subrepresentation.toSubmodule hU
      change U.toSubmodule = (⊥ : Submodule k chi.representation) at hU'
      apply Subrepresentation.toSubmodule_injective
      exact hU'
    · right
      have hU' := congrArg Subrepresentation.toSubmodule hU
      change U.toSubmodule = (⊤ : Submodule k chi.representation) at hU'
      apply Subrepresentation.toSubmodule_injective
      exact hU'

/-- Peterfalvi 4.4: an irreducible character of `L` is trivial on `K`
exactly when it belongs to the trivial right column of the prime-TI
rectangle. -/
theorem prTIirr0P (chi : IrreducibleCharacter L k) :
    (∃ i : IrreducibleCharacter W₁ k,
        chi = h.primeTIIndex iso
          (i, (IrreducibleCharacter.trivial :
            IrreducibleCharacter W₂ k))) ↔
      K.subgroupOf L ≤
        ClassFunction.translationKernel (chi : ClassFunction L k) := by
  constructor
  · rintro ⟨i, rfl⟩
    apply le_translationKernel_of_restrict_eq_trivial
    change ClassFunction.restrict (K.subgroupOf L)
      (h.primeTICharacter iso i
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ k)) =
      ((IrreducibleCharacter.trivial :
        IrreducibleCharacter (K.subgroupOf L) k) :
          ClassFunction (K.subgroupOf L) k)
    rw [h.cfRes_prTIirr iso, h.prTIres0 iso]
  · intro hker
    let rho : Representation k L chi.representation :=
      chi.representation.ρ
    let inc : W₁ →* L := Subgroup.inclusion h.complement_le_group
    let tau : Representation k W₁ chi.representation := rho.comp inc
    letI : Representation.IsIrreducible tau := by
      exact h.complement_restriction_isIrreducible chi hker
    let V : FDRep k W₁ := FDRep.of tau
    letI : CategoryTheory.Simple V :=
      simple_fdRep_of_isIrreducible tau
    let i : IrreducibleCharacter W₁ k :=
      IrreducibleCharacter.ofFDRep V
    have hkerRho : K.subgroupOf L ≤ rho.ker := by
      rw [← ClassFunction.translationKernel_irreducibleCharacter chi]
      exact hker
    have heq : Set.EqOn
        (fun w : W ↦ (chi : ClassFunction L k)
          ⟨w, h.directProduct_le_group w.property⟩)
        (IrreducibleCharacter.cyclicTICharacter defW i
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ k) :
            W → k)
        (cyclicTISetInW W W₁ W₂) := by
      intro w hw
      let x : W₁ := defW.leftProjection w
      let y : W₂ := defW.rightProjection w
      let wL : L := ⟨w, h.directProduct_le_group w.property⟩
      let yL : L := ⟨(y : Gamma),
        h.kernel_le_group (h.fixed_le_kernel y.property)⟩
      have hwL : wL = inc x * yL := by
        apply Subtype.ext
        change (w : Gamma) = (x : Gamma) * (y : Gamma)
        calc
          (w : Gamma) =
              ((defW.mulEquiv (x, y) : W) : Gamma) := by
                rw [defW.mulEquiv_projections]
          _ = (x : Gamma) * (y : Gamma) :=
            defW.coe_mulEquiv_apply (x, y)
      have hy : rho yL = 1 :=
        MonoidHom.mem_ker.mp
          (hkerRho (h.fixed_le_kernel y.property))
      calc
        chi wL = Representation.character rho wL :=
          (chi.representation_character wL).symm
        _ = LinearMap.trace k chi.representation (rho (inc x)) := by
          rw [hwL]
          change LinearMap.trace k chi.representation
            (rho (inc x * yL)) = _
          rw [map_mul, hy, mul_one]
        _ = tau.character x := rfl
        _ = i x := by
          exact (IrreducibleCharacter.ofFDRep_apply V x).symm
        _ = i x *
            (IrreducibleCharacter.trivial :
              IrreducibleCharacter W₂ k) y := by simp
        _ = IrreducibleCharacter.cyclicTICharacter defW i
            (IrreducibleCharacter.trivial :
              IrreducibleCharacter W₂ k) w := by
          rw [IrreducibleCharacter.cyclicTICharacter_apply]
    have hiso := iso.eq_in_cyclicTIIsometry
      (IrreducibleCharacter.cyclicTICharacter defW i
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ k))
      (chi : ClassFunction L k)
      ⟨chi, (1 : ℤ), (by simp [IsSign]), by simp⟩ heq
    refine ⟨i, ?_⟩
    apply IrreducibleCharacter.ext
    intro g
    have hg := congrArg (fun f : ClassFunction L k ↦ f g) hiso
    rw [(h.primeTICharacterData iso).isometry_character] at hg
    change chi g =
      (h.primeTISign iso
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ k) : k) *
        (h.primeTIIndex iso
          (i, (IrreducibleCharacter.trivial :
            IrreducibleCharacter W₂ k)) : ClassFunction L k) g at hg
    rw [h.prTIsign0 iso] at hg
    simpa using hg

end PrimeTIHypothesis

end

end Submission.OddOrder.PF
