import Submission.OddOrder.PF.Section01.NormalSubgroupInductionConsequences
import Submission.OddOrder.PF.Section01.RestrictionComplementEquivalenceSet
import Submission.OddOrder.PF.Section01.VirtualCharacterIsometryBase
import Submission.OddOrder.PF.Section03.AbelianSupportedClassFunctions
import Submission.OddOrder.PF.Section03.CyclicTIIsometry
import Submission.OddOrder.PF.Section03.CyclicTIUniqueness
import Submission.OddOrder.PF.Section04.PrimeTIHypothesis
import Submission.OddOrder.PF.Section04.VirtualCharacterPairs

/-!
# The irreducible characters attached to a prime-TI subgroup

This file ports Peterfalvi 4.3(b,c), from `sigma` and `w_` through
`primeTIirr_spec` and its five immediate restatements.  For a fixed character
of `W₂`, normalized-TI induction on `W \ W₂` and Peterfalvi 1.4 give a
signed, injectively indexed column of irreducible characters of `L`.  The
four-character comparison of 4.1 makes the indices in distinct columns
disjoint.  Restriction/complement equivalence then identifies the restrictions
of the resulting full rectangle and proves that every irreducible outside it
vanishes on `W \ W₂`.

The construction is parameterized by the explicit cyclic-TI isometry data.
This keeps the only dependency on the still-growing Section 3 construction at
the boundary of the file; no conclusion of 4.3 is assumed as part of that
data.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical

universe u

variable {Gamma k : Type u} [Group Gamma] [Fintype Gamma]
  [Field k] [IsAlgClosed k] [CharZero k]
  {L K W W₁ W₂ : Subgroup Gamma}
  {defW : IsInternalDirectProductIn W₁ W₂ W}

local instance primeTICharactersInvertibleCard
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

private theorem coeffDot_sub_left
    {ι : Type*} (f g z : IntegralLattice ι) :
    coeffDot (f - g) z = coeffDot f z - coeffDot g z := by
  rw [sub_eq_add_neg, coeffDot_add_left, coeffDot_neg_left]
  rfl

private theorem coeffDot_sub_right
    {ι : Type*} (z f g : IntegralLattice ι) :
    coeffDot z (f - g) = coeffDot z f - coeffDot z g := by
  rw [sub_eq_add_neg, coeffDot_add_right, coeffDot_neg_right]
  rfl

/-- The larger prime-TI set, regarded as a subset of the subgroup type `W`. -/
def primeTISetInW (W W₂ : Subgroup Gamma) : Set W :=
  {w | (w : Gamma) ∈ primeTISet W W₂}

@[simp]
theorem mem_primeTISetInW {w : W} :
    w ∈ primeTISetInW W W₂ ↔ (w : Gamma) ∉ W₂ := by
  simp [primeTISetInW, primeTISet]

namespace PrimeTIHypothesis

variable (h : PrimeTIHypothesis L K W W₁ W₂ defW)

include h

/-- `W \ W₂` is inverse-stable inside `W`. -/
theorem primeTISetInW_invStable : IsInvStable (primeTISetInW W W₂) := by
  intro w
  simp only [mem_primeTISetInW, Subgroup.coe_inv,
    Subgroup.inv_mem_iff]

/-- Since `W` is cyclic, `W \ W₂` is conjugation-stable inside `W`. -/
theorem primeTISetInW_conjStable : IsConjStable (primeTISetInW W W₂) := by
  letI : IsCyclic W := h.cyclic
  intro x w
  have hconj : x * w * x⁻¹ = w := by
    calc
      x * w * x⁻¹ = w * x * x⁻¹ := by rw [mul_comm' x w]
      _ = w := by simp
  rw [hconj]

/-- The cyclic-TI set is contained in the larger set used in 4.3. -/
theorem cyclicTISetInW_subset_primeTISetInW :
    cyclicTISetInW W W₁ W₂ ⊆ primeTISetInW W W₂ := by
  intro w hw
  exact mem_primeTISetInW.mpr (mem_cyclicTISetInW.mp hw).2

/-- The ambient prime-TI set lies in `L` and excludes the identity. -/
theorem primeTISet_subset_group_diff_one :
    primeTISet W W₂ ⊆ (L : Set Gamma) \ {(1 : Gamma)} := by
  intro x hx
  obtain ⟨hxW, hxW₂⟩ := mem_primeTISet.mp hx
  refine ⟨h.directProduct_le_group hxW, ?_⟩
  intro hx1
  apply hxW₂
  have hx1' : x = 1 := by simpa using hx1
  simpa [hx1'] using W₂.one_mem

/-- The ambient prime-TI set is inverse-stable. -/
theorem primeTISet_invStable : IsInvStable (primeTISet W W₂) := by
  intro x
  simp [primeTISet, Subgroup.inv_mem_iff]

/-- The product equivalence identifies `W \ W₂` with
`(W₁ \ {1}) × W₂`. -/
theorem image_nonidentity_left_prod :
    defW.mulEquiv ''
        (((Set.univ : Set W₁) \ {1}) ×ˢ (Set.univ : Set W₂)) =
      primeTISetInW W W₂ := by
  ext w
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [mem_primeTISetInW, defW.mulEquiv_mem_right_iff]
    simpa using hp.1
  · intro hw
    refine ⟨defW.mulEquiv.symm w, ?_, defW.mulEquiv.apply_symm_apply w⟩
    have hw' :
        ((defW.mulEquiv (defW.mulEquiv.symm w) : W) : Gamma) ∉ W₂ := by
      simpa using (mem_primeTISetInW.mp hw)
    rw [defW.mulEquiv_mem_right_iff] at hw'
    simpa using hw'

/-- Cardinality of `W \ W₂`. -/
theorem ncard_primeTISetInW :
    (primeTISetInW W W₂).ncard =
      (Nat.card W₁ - 1) * Nat.card W₂ := by
  rw [← h.image_nonidentity_left_prod]
  rw [Set.ncard_image_of_injective _ defW.mulEquiv.injective,
    Set.ncard_prod]
  simp

end PrimeTIHypothesis

/-- The row/column indices for the difference basis of the functions
supported on `W \ W₂`. -/
abbrev PrimeTIDifferenceIndex
    (W₁ W₂ : Subgroup Gamma) (k : Type u) [Field k]
    [IsAlgClosed k] [CharZero k] :=
  {i : IrreducibleCharacter W₁ k //
      i ≠ IrreducibleCharacter.trivial} ×
    IrreducibleCharacter W₂ k

/-- Peterfalvi's `ew_ i j = w_ i j - w_ 0 j`, at the integral level. -/
def primeTIDifference
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (i : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k) : VirtualCharacter W k :=
  Finsupp.single (IrreducibleCharacter.cyclicTICharacter defW i j) 1 -
    Finsupp.single
      (IrreducibleCharacter.cyclicTICharacter defW
        IrreducibleCharacter.trivial j) 1

@[simp]
theorem primeTIDifference_trivial
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (j : IrreducibleCharacter W₂ k) :
    primeTIDifference defW IrreducibleCharacter.trivial j = 0 := by
  simp [primeTIDifference]

@[simp]
theorem realize_primeTIDifference
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (i : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k) :
    VirtualCharacter.realize (primeTIDifference defW i j) =
      (IrreducibleCharacter.cyclicTICharacter defW i j :
        ClassFunction W k) -
      (IrreducibleCharacter.cyclicTICharacter defW
        IrreducibleCharacter.trivial j : ClassFunction W k) := by
  simp [primeTIDifference]

namespace PrimeTIHypothesis

variable (h : PrimeTIHypothesis L K W W₁ W₂ defW)

include h

/-- The difference `w_(i,j) - w_(0,j)` is supported on `W \ W₂`. -/
theorem primeTIDifference_mem_supportedOn
    (i : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k) :
    VirtualCharacter.realize (primeTIDifference defW i j) ∈
      ClassFunction.supportedOn (primeTISetInW W W₂) := by
  letI : IsCyclic W₁ := h.complement_cyclic
  letI : IsCyclic W₂ := h.fixed_cyclic
  rw [ClassFunction.mem_supportedOn_iff]
  intro w hw
  have hwW₂ : (w : Gamma) ∈ W₂ := by
    by_contra hwW₂
    exact hw (mem_primeTISetInW.mpr hwW₂)
  let p : W₁ × W₂ := defW.mulEquiv.symm w
  have hp₁ : p.1 = 1 := by
    apply (defW.mulEquiv_mem_right_iff p).mp
    simpa [p] using hwW₂
  have hwDecomp : defW.mulEquiv p = w := defW.mulEquiv.apply_symm_apply w
  rw [← hwDecomp, realize_primeTIDifference]
  simp [hp₁, IrreducibleCharacter.apply_one_eq_one_of_isCyclic]

/-- Exact pairing of one difference with an irreducible character of `W`. -/
theorem characterPairing_primeTIDifference_character
    (i a : IrreducibleCharacter W₁ k)
    (j b : IrreducibleCharacter W₂ k)
    (hi : i ≠ IrreducibleCharacter.trivial) :
    characterPairing
        (VirtualCharacter.realize (primeTIDifference defW i j))
        (IrreducibleCharacter.cyclicTICharacter defW a b :
          ClassFunction W k) =
      if (a, b) = (i, j) then 1
      else if (a, b) = (IrreducibleCharacter.trivial, j) then -1
      else 0 := by
  rw [realize_primeTIDifference, characterPairing_sub_left]
  simp only [IrreducibleCharacter.characterPairing_eq_ite,
    IrreducibleCharacter.cyclicTICharacter_eq_iff, Prod.ext_iff]
  by_cases hfirst : i = a ∧ j = b
  · have ha0 : a ≠ IrreducibleCharacter.trivial := by
      intro ha
      exact hi (hfirst.1.trans ha)
    simp [hfirst, ha0, hi, eq_comm]
  · by_cases hsecond : a = IrreducibleCharacter.trivial ∧ j = b
    · simp [hfirst, hsecond, hi, eq_comm]
    · simp [hfirst, hsecond, hi, eq_comm]

/-- Pairing two members of a fixed column. -/
theorem coeffDot_primeTIDifference_same_column
    (i a : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k)
    (hi : i ≠ IrreducibleCharacter.trivial)
    (ha : a ≠ IrreducibleCharacter.trivial) :
    coeffDot (primeTIDifference defW i j)
        (primeTIDifference defW a j) =
      if i = a then 2 else 1 := by
  by_cases hia : i = a <;>
    simp [primeTIDifference, coeffDot_sub_left, coeffDot_sub_right,
      IrreducibleCharacter.cyclicTICharacter_eq_iff,
      hi, ha, hia]

/-- Differences belonging to distinct `W₂` columns are orthogonal. -/
theorem coeffDot_primeTIDifference_right_ne
    (i a : IrreducibleCharacter W₁ k)
    (j b : IrreducibleCharacter W₂ k)
    (hjb : j ≠ b) :
    coeffDot (primeTIDifference defW i j)
        (primeTIDifference defW a b) = 0 := by
  simp [primeTIDifference, coeffDot_sub_left, coeffDot_sub_right,
    IrreducibleCharacter.cyclicTICharacter_eq_iff, hjb]

/-- The supported difference, bundled in the support subspace. -/
def primeTISupportedDifference
    (p : PrimeTIDifferenceIndex W₁ W₂ k) :
    ClassFunction.supportedOn (R := k) (primeTISetInW W W₂) :=
  ⟨VirtualCharacter.realize (primeTIDifference defW p.1.1 p.2),
    h.primeTIDifference_mem_supportedOn p.1.1 p.2⟩

@[simp]
theorem primeTISupportedDifference_val
    (p : PrimeTIDifferenceIndex W₁ W₂ k) :
    (h.primeTISupportedDifference p : ClassFunction W k) =
      VirtualCharacter.realize (primeTIDifference defW p.1.1 p.2) :=
  rfl

/-- The `ew_ i j` family is linearly independent. -/
theorem primeTISupportedDifference_linearIndependent :
    LinearIndependent k (h.primeTISupportedDifference (k := k)) := by
  refine (Fintype.linearIndependent_iff
    (R := k) (v := h.primeTISupportedDifference (k := k))).2 ?_
  intro c hc p
  let test : ClassFunction W k :=
    IrreducibleCharacter.cyclicTICharacter defW p.1.1 p.2
  let extract :
      ClassFunction.supportedOn (R := k) (primeTISetInW W W₂) →ₗ[k] k :=
    (characterPairingRight test).comp
      (ClassFunction.supportedOn (R := k)
        (primeTISetInW W W₂)).subtype
  have hextract (q : PrimeTIDifferenceIndex W₁ W₂ k) :
      extract (h.primeTISupportedDifference q) = if q = p then 1 else 0 := by
    change characterPairing
        (VirtualCharacter.realize
          (primeTIDifference defW q.1.1 q.2)) test = _
    rw [h.characterPairing_primeTIDifference_character _ _ _ _ q.1.2]
    by_cases hqp : q = p
    · subst q
      simp [test, p.1.2]
    · have hpqComponents :
          (p.1.1, p.2) ≠ (q.1.1, q.2) := by
        intro heq
        apply hqp
        apply Prod.ext
        · exact Subtype.ext (congrArg Prod.fst heq).symm
        · exact (congrArg Prod.snd heq).symm
      have hp0 :
          (p.1.1, p.2) ≠
            (IrreducibleCharacter.trivial, q.2) := by
        intro heq
        exact p.1.2 (congrArg Prod.fst heq)
      simp [test, hpqComponents, hp0, hqp]
  have hc' := congrArg extract hc
  simpa [map_sum, hextract] using hc'

/-- The difference index has the cardinality of `W \ W₂`. -/
theorem card_primeTIDifferenceIndex :
    Fintype.card (PrimeTIDifferenceIndex W₁ W₂ k) =
      (primeTISetInW W W₂).ncard := by
  letI : IsCyclic W₁ := h.complement_cyclic
  letI : IsCyclic W₂ := h.fixed_cyclic
  calc
    Fintype.card (PrimeTIDifferenceIndex W₁ W₂ k) =
        (Fintype.card (IrreducibleCharacter W₁ k) - 1) *
          Fintype.card (IrreducibleCharacter W₂ k) := by
      simp [PrimeTIDifferenceIndex, Fintype.card_prod, Set.card_ne_eq]
    _ = (Nat.card W₁ - 1) * Nat.card W₂ := by
      rw [IrreducibleCharacter.card_eq_natCard_of_isCyclic,
        IrreducibleCharacter.card_eq_natCard_of_isCyclic]
    _ = (primeTISetInW W W₂).ncard := h.ncard_primeTISetInW.symm

/-- Peterfalvi's `V2base`: a basis of all class functions supported on
`W \ W₂`. -/
def primeTIDifferenceBasis :
    Module.Basis (PrimeTIDifferenceIndex W₁ W₂ k) k
      (ClassFunction.supportedOn (R := k) (primeTISetInW W W₂)) :=
  basisOfLinearIndependentOfCardEqFinrank'
    (h.primeTISupportedDifference (k := k))
    h.primeTISupportedDifference_linearIndependent
    (by
      letI : IsCyclic W := h.cyclic
      rw [h.card_primeTIDifferenceIndex,
        ClassFunction.finrank_abelian_supportedOn])

@[simp]
theorem primeTIDifferenceBasis_val
    (p : PrimeTIDifferenceIndex W₁ W₂ k) :
    (h.primeTIDifferenceBasis p : ClassFunction W k) =
      VirtualCharacter.realize (primeTIDifference defW p.1.1 p.2) := by
  simp [primeTIDifferenceBasis, primeTISupportedDifference]

/-! ## The literal subgroup copy used by induction and restriction -/

/-- `W \ W₂`, transported to the literal subgroup copy `W.subgroupOf L`. -/
def primeTISetInSubgroupOf : Set (W.subgroupOf L) :=
  (Subgroup.subgroupOfEquivOfLe h.directProduct_le_group) ⁻¹'
    primeTISetInW W W₂

theorem primeTISetInSubgroupOf_conjStable :
    IsConjStable h.primeTISetInSubgroupOf := by
  intro x w
  change
    Subgroup.subgroupOfEquivOfLe h.directProduct_le_group
          (x * w * x⁻¹) ∈ primeTISetInW W W₂ ↔
      Subgroup.subgroupOfEquivOfLe h.directProduct_le_group w ∈
        primeTISetInW W W₂
  simp only [map_mul, map_inv]
  exact h.primeTISetInW_conjStable
    (Subgroup.subgroupOfEquivOfLe h.directProduct_le_group x)
    (Subgroup.subgroupOfEquivOfLe h.directProduct_le_group w)

theorem primeTISetInSubgroupOf_invStable :
    IsInvStable h.primeTISetInSubgroupOf := by
  intro w
  change
    Subgroup.subgroupOfEquivOfLe h.directProduct_le_group w⁻¹ ∈
        primeTISetInW W W₂ ↔
      Subgroup.subgroupOfEquivOfLe h.directProduct_le_group w ∈
        primeTISetInW W W₂
  rw [map_inv]
  exact h.primeTISetInW_invStable
    (Subgroup.subgroupOfEquivOfLe h.directProduct_le_group w)

/-- Transport supported functions from the friendly type `W` to its literal
copy inside `L`. -/
def primeTISupportedSubgroupOfEquiv :
    ClassFunction.supportedOn (R := k) (primeTISetInW W W₂) ≃ₗ[k]
      ClassFunction.supportedOn (R := k) h.primeTISetInSubgroupOf where
  toFun f :=
    ⟨(h.prime_cycTIhyp).classFunctionSubgroupOfEquiv f, by
      rw [ClassFunction.mem_supportedOn_iff]
      intro x hx
      exact f.property
        (Subgroup.subgroupOfEquivOfLe h.directProduct_le_group x) hx⟩
  invFun f :=
    ⟨(h.prime_cycTIhyp).classFunctionSubgroupOfEquiv.symm f, by
      rw [ClassFunction.mem_supportedOn_iff]
      intro x hx
      apply f.property
      simpa [primeTISetInSubgroupOf] using hx⟩
  left_inv f := by
    apply Subtype.ext
    exact (h.prime_cycTIhyp).classFunctionSubgroupOfEquiv.left_inv f.val
  right_inv f := by
    apply Subtype.ext
    exact (h.prime_cycTIhyp).classFunctionSubgroupOfEquiv.right_inv f.val
  map_add' f g := by
    apply Subtype.ext
    simp
  map_smul' a f := by
    apply Subtype.ext
    simp

/-- The `ew_ i j` basis on the literal subgroup copy. -/
def primeTIDifferenceBasisSubgroupOf :
    Module.Basis (PrimeTIDifferenceIndex W₁ W₂ k) k
      (ClassFunction.supportedOn (R := k) h.primeTISetInSubgroupOf) :=
  h.primeTIDifferenceBasis.map h.primeTISupportedSubgroupOfEquiv

@[simp]
theorem primeTIDifferenceBasisSubgroupOf_val
    (p : PrimeTIDifferenceIndex W₁ W₂ k) :
    (h.primeTIDifferenceBasisSubgroupOf p :
        ClassFunction (W.subgroupOf L) k) =
      (h.prime_cycTIhyp).classFunctionSubgroupOfEquiv
        (VirtualCharacter.realize
          (primeTIDifference defW p.1.1 p.2)) := by
  simp [primeTIDifferenceBasisSubgroupOf,
    primeTISupportedSubgroupOfEquiv]

/-- Normalized-TI induction on `W \ W₂` preserves the character pairing. -/
theorem characterPairing_induce_primeTISet
    (alpha beta : ClassFunction W k)
    (halpha : alpha ∈
      ClassFunction.supportedOn (primeTISetInW W W₂))
    (hbeta : beta ∈
      ClassFunction.supportedOn (primeTISetInW W W₂)) :
    characterPairing
        ((h.prime_cycTIhyp).induceClassFunction alpha)
        ((h.prime_cycTIhyp).induceClassFunction beta) =
      characterPairing alpha beta := by
  simpa [CyclicTIHypothesis.induceClassFunction] using
    (normedTI_induce_characterPairing h.normedTI_prTIset
      h.primeTISet_subset_group_diff_one h.primeTISet_invStable
      alpha beta halpha hbeta)

/-- The integral virtual character obtained by inducing `ew_ i j`. -/
def primeTIInducedDifference
    (i : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k) : VirtualCharacter L k :=
  (h.prime_cycTIhyp).induceVirtualCharacter
    (primeTIDifference defW i j)

@[simp]
theorem realize_primeTIInducedDifference
    (i : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k) :
    VirtualCharacter.realize (h.primeTIInducedDifference i j) =
      (h.prime_cycTIhyp).induceClassFunction
        (VirtualCharacter.realize (primeTIDifference defW i j)) :=
  (h.prime_cycTIhyp).realize_induceVirtualCharacter _

@[simp]
theorem primeTIInducedDifference_trivial
    (j : IrreducibleCharacter W₂ k) :
    h.primeTIInducedDifference IrreducibleCharacter.trivial j = 0 := by
  simp [primeTIInducedDifference]

end PrimeTIHypothesis

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

/-- In a character lattice, norm two and value zero at the identity force
the two signed coefficients to have opposite signs. -/
private theorem coeffSum_eq_zero_of_normSq_eq_two_of_realize_one_eq_zero
    {G : Type u} [Group G]
    (f : VirtualCharacter G k) (hnorm : normSq f = 2)
    (hone : VirtualCharacter.realize f 1 = 0) :
    coeffSum f = 0 := by
  obtain ⟨chi, psi, epsilon, delta, hne, hepsilon, hdelta, rfl⟩ :=
    eq_sum_signed_singles_of_normSq_eq_two f hnorm
  have hchi :
      chi 1 = (Module.finrank k chi.representation : k) := by
    rw [← chi.representation_character, FDRep.char_one]
  have hpsi :
      psi 1 = (Module.finrank k psi.representation : k) := by
    rw [← psi.representation_character, FDRep.char_one]
  have hpos :
      0 < Module.finrank k chi.representation +
        Module.finrank k psi.representation :=
    Nat.add_pos_left (irreducibleCharacter_finrank_pos chi) _
  rcases hepsilon with rfl | rfl <;>
    rcases hdelta with rfl | rfl
  · exfalso
    simp only [VirtualCharacter.realize_add,
      VirtualCharacter.realize_single, ClassFunction.add_apply,
      ClassFunction.smul_apply, Int.cast_one, one_smul,
      hchi, hpsi] at hone
    have hcast :
        ((Module.finrank k chi.representation +
          Module.finrank k psi.representation : Nat) : k) = 0 := by
      simpa only [Nat.cast_add] using hone
    exact (Nat.cast_ne_zero.mpr hpos.ne') hcast
  · simp [coeffSum_add, coeffSum_neg, coeffSum_single]
  · simp [coeffSum_add, coeffSum_neg, coeffSum_single]
  · exfalso
    simp only [VirtualCharacter.realize_add,
      VirtualCharacter.realize_single, ClassFunction.add_apply,
      ClassFunction.smul_apply, Int.cast_neg, Int.cast_one,
      neg_smul, one_smul, Pi.neg_apply, hchi, hpsi] at hone
    have hcast :
        -((Module.finrank k chi.representation +
          Module.finrank k psi.representation : Nat) : k) = 0 := by
      simpa only [Nat.cast_add, neg_add] using hone
    exact (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hpos.ne')) hcast

/-- Reindex Peterfalvi 1.4 from `Fin` to an arbitrary finite type with a
distinguished base point. -/
private theorem vchar_isometry_base_fintype
    {ι kappa : Type*} [Fintype ι] [DecidableEq ι]
    (base : ι) (hcard : 2 ≤ Fintype.card ι)
    (F : ι → IntegralLattice kappa)
    (hzero : F base = 0)
    (hnorm : ∀ i, i ≠ base → normSq (F i) = 2)
    (hsum : ∀ i, coeffSum (F i) = 0)
    (hpair : ∀ i j, i ≠ base → j ≠ base → i ≠ j →
      coeffDot (F i) (F j) = 1) :
    ∃ mu : ι → kappa, Function.Injective mu ∧
      ∃ epsilon : ℤ, IsSign epsilon ∧ ∀ i,
        F i = epsilon •
          (Finsupp.single (mu i) 1 - Finsupp.single (mu base) 1) := by
  let n := Fintype.card ι
  have hnpos : 0 < n := by
    dsimp only [n]
    omega
  letI : NeZero n := ⟨hnpos.ne'⟩
  let eFin : ι ≃ Fin n := Fintype.equivFin ι
  let eZero : Fin n ≃ ι :=
    (Equiv.swap 0 (eFin base)).trans eFin.symm
  have heZero : eZero 0 = base := by
    simp [eZero]
  have hn : n - 2 + 2 = n := Nat.sub_add_cancel hcard
  have hnDomain : n - 2 + 2 ≠ 0 := by omega
  letI : NeZero (n - 2 + 2) := ⟨hnDomain⟩
  let e : Fin (n - 2 + 2) ≃ ι := (finCongr hn).trans eZero
  have he : e 0 = base := by
    simp [e, heZero]
  let F' : Fin (n - 2 + 2) → IntegralLattice kappa := fun q ↦ F (e q)
  have hzero' : F' 0 = 0 := by simpa [F', he] using hzero
  have hnorm' : ∀ q, q ≠ 0 → normSq (F' q) = 2 := by
    intro q hq
    apply hnorm
    intro heq
    apply hq
    apply e.injective
    simpa [he] using heq
  have hsum' : ∀ q, coeffSum (F' q) = 0 := fun q ↦ hsum (e q)
  have hpair' : ∀ q r, q ≠ 0 → r ≠ 0 → q ≠ r →
      coeffDot (F' q) (F' r) = 1 := by
    intro q r hq hr hqr
    apply hpair
    · intro heq
      apply hq
      apply e.injective
      simpa [he] using heq
    · intro heq
      apply hr
      apply e.injective
      simpa [he] using heq
    · exact fun heq ↦ hqr (e.injective heq)
  obtain ⟨mu', hmu', epsilon, hepsilon, hrep⟩ :=
    vchar_isometry_base F' hzero' hnorm' hsum' hpair'
  let mu : ι → kappa := fun i ↦ mu' (e.symm i)
  refine ⟨mu, ?_, epsilon, hepsilon, ?_⟩
  · intro i j hij
    apply e.symm.injective
    exact hmu' hij
  · intro i
    have hbase : e.symm base = 0 := by
      apply e.injective
      simp [he]
    simpa [F', mu, hbase] using hrep (e.symm i)

namespace PrimeTIHypothesis

variable (h : PrimeTIHypothesis L K W W₁ W₂ defW)

include h

/-- Self-pairing of an induced nonbase difference. -/
theorem normSq_primeTIInducedDifference
    (i : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k)
    (hi : i ≠ IrreducibleCharacter.trivial) :
    normSq (h.primeTIInducedDifference i j) = 2 := by
  have hp := h.characterPairing_induce_primeTISet
    (VirtualCharacter.realize (primeTIDifference defW i j))
    (VirtualCharacter.realize (primeTIDifference defW i j))
    (h.primeTIDifference_mem_supportedOn i j)
    (h.primeTIDifference_mem_supportedOn i j)
  rw [← h.realize_primeTIInducedDifference,
    VirtualCharacter.characterPairing_realize,
    VirtualCharacter.characterPairing_realize,
    h.coeffDot_primeTIDifference_same_column i i j hi hi] at hp
  simpa [normSq] using Int.cast_injective hp

/-- Every induced difference has value zero at the identity. -/
theorem primeTIInducedDifference_one
    (i : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k) :
    VirtualCharacter.realize (h.primeTIInducedDifference i j) 1 = 0 := by
  letI : IsCyclic W₁ := h.complement_cyclic
  letI : IsCyclic W₂ := h.fixed_cyclic
  rw [h.realize_primeTIInducedDifference]
  change ClassFunction.induce (W.subgroupOf L)
      ((h.prime_cycTIhyp).classFunctionSubgroupOfEquiv
        (VirtualCharacter.realize (primeTIDifference defW i j))) 1 = 0
  rw [ClassFunction.induce_one]
  simp [realize_primeTIDifference,
    IrreducibleCharacter.apply_one_eq_one_of_isCyclic]

/-- The coefficient augmentation vanishes; this is the lattice formulation
used by the current Peterfalvi 1.4 API. -/
theorem coeffSum_primeTIInducedDifference
    (i : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k) :
    coeffSum (h.primeTIInducedDifference i j) = 0 := by
  by_cases hi : i = IrreducibleCharacter.trivial
  · subst i
    simp
  · exact coeffSum_eq_zero_of_normSq_eq_two_of_realize_one_eq_zero
      (h.primeTIInducedDifference i j)
      (h.normSq_primeTIInducedDifference i j hi)
      (h.primeTIInducedDifference_one i j)

/-- Off-diagonal pairing inside one induced column. -/
theorem coeffDot_primeTIInducedDifference_same_column
    (i a : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k)
    (hi : i ≠ IrreducibleCharacter.trivial)
    (ha : a ≠ IrreducibleCharacter.trivial)
    (hia : i ≠ a) :
    coeffDot (h.primeTIInducedDifference i j)
        (h.primeTIInducedDifference a j) = 1 := by
  have hp := h.characterPairing_induce_primeTISet
    (VirtualCharacter.realize (primeTIDifference defW i j))
    (VirtualCharacter.realize (primeTIDifference defW a j))
    (h.primeTIDifference_mem_supportedOn i j)
    (h.primeTIDifference_mem_supportedOn a j)
  rw [← h.realize_primeTIInducedDifference,
    ← h.realize_primeTIInducedDifference,
    VirtualCharacter.characterPairing_realize,
    VirtualCharacter.characterPairing_realize,
    h.coeffDot_primeTIDifference_same_column i a j hi ha,
    if_neg hia] at hp
  exact Int.cast_injective hp

end PrimeTIHypothesis

/-! ## Peterfalvi 1.4, column by column -/

private structure PrimeTIColumnData
    (h : PrimeTIHypothesis L K W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ k) where
  index : IrreducibleCharacter W₁ k → IrreducibleCharacter L k
  index_injective : Function.Injective index
  sign : ℤ
  isSign_sign : IsSign sign
  induce_eq : ∀ i : IrreducibleCharacter W₁ k,
    h.primeTIInducedDifference i j =
      sign •
        (Finsupp.single (index i) 1 -
          Finsupp.single (index IrreducibleCharacter.trivial) 1)

namespace PrimeTIHypothesis

variable (h : PrimeTIHypothesis L K W W₁ W₂ defW)

include h

/-- The signed irreducible column supplied by Peterfalvi 1.4. -/
private def primeTIColumnData
    (j : IrreducibleCharacter W₂ k) : PrimeTIColumnData (k := k) h j := by
  letI : IsCyclic W₁ := h.complement_cyclic
  have hcard : 2 ≤ Fintype.card (IrreducibleCharacter W₁ k) := by
    rw [IrreducibleCharacter.card_eq_natCard_of_isCyclic]
    exact h.prime_cycTIhyp.one_lt_card_left
  let hex := vchar_isometry_base_fintype
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ k)
      hcard (fun i ↦ h.primeTIInducedDifference i j)
      (h.primeTIInducedDifference_trivial j)
      (fun i hi ↦ h.normSq_primeTIInducedDifference i j hi)
      (fun i ↦ h.coeffSum_primeTIInducedDifference i j)
      (fun i a hi ha hia ↦
        h.coeffDot_primeTIInducedDifference_same_column i a j hi ha hia)
  let mu := hex.choose
  have hmu := hex.choose_spec.1
  let epsilon := hex.choose_spec.2.choose
  have hepsilon := hex.choose_spec.2.choose_spec.1
  have hrep := hex.choose_spec.2.choose_spec.2
  exact
    { index := mu
      index_injective := hmu
      sign := epsilon
      isSign_sign := hepsilon
      induce_eq := hrep }

private theorem primeTIColumnData_difference
    (j : IrreducibleCharacter W₂ k)
    (i a : IrreducibleCharacter W₁ k) :
    h.primeTIInducedDifference i j - h.primeTIInducedDifference a j =
      (h.primeTIColumnData j).sign •
        (Finsupp.single ((h.primeTIColumnData j).index i) 1 -
          Finsupp.single ((h.primeTIColumnData j).index a) 1) := by
  rw [(h.primeTIColumnData j).induce_eq,
    (h.primeTIColumnData j).induce_eq]
  rw [← smul_sub]
  congr 1
  abel

private theorem primeTIColumnIndex_difference_one
    (j : IrreducibleCharacter W₂ k)
    (i a : IrreducibleCharacter W₁ k) :
    VirtualCharacter.realize
        (Finsupp.single ((h.primeTIColumnData j).index i) 1 -
          Finsupp.single ((h.primeTIColumnData j).index a) 1) 1 = 0 := by
  have hrep := congrArg
    (fun z : VirtualCharacter L k ↦ VirtualCharacter.realize z 1)
    (h.primeTIColumnData_difference j i a)
  have hsign : ((h.primeTIColumnData j).sign : k) ≠ 0 :=
    Int.cast_ne_zero.mpr
      (isSign_ne_zero (h.primeTIColumnData j).isSign_sign)
  have hleft :
      VirtualCharacter.realize
          (h.primeTIInducedDifference i j -
            h.primeTIInducedDifference a j) 1 = 0 := by
    rw [VirtualCharacter.realize_sub, ClassFunction.sub_apply,
      h.primeTIInducedDifference_one,
      h.primeTIInducedDifference_one, sub_self]
  rw [hleft] at hrep
  simp only [map_zsmul, ← Int.cast_smul_eq_zsmul k,
    ClassFunction.smul_apply, smul_eq_mul] at hrep
  exact (mul_eq_zero.mp hrep.symm).resolve_left hsign

/-- Pairing preservation for differences of two members of each of two
distinct columns. -/
private theorem coeffDot_primeTIInducedDifference_sub_right_ne
    (i a q r : IrreducibleCharacter W₁ k)
    (j b : IrreducibleCharacter W₂ k) (hjb : j ≠ b) :
    coeffDot
        (h.primeTIInducedDifference i j -
          h.primeTIInducedDifference a j)
        (h.primeTIInducedDifference q b -
          h.primeTIInducedDifference r b) = 0 := by
  let alpha : VirtualCharacter W k :=
    primeTIDifference defW i j - primeTIDifference defW a j
  let beta : VirtualCharacter W k :=
    primeTIDifference defW q b - primeTIDifference defW r b
  have halpha : VirtualCharacter.realize alpha ∈
      ClassFunction.supportedOn (primeTISetInW W W₂) := by
    simpa only [alpha, VirtualCharacter.realize_sub] using
      (ClassFunction.supportedOn (R := k)
        (primeTISetInW W W₂)).sub_mem
          (h.primeTIDifference_mem_supportedOn i j)
          (h.primeTIDifference_mem_supportedOn a j)
  have hbeta : VirtualCharacter.realize beta ∈
      ClassFunction.supportedOn (primeTISetInW W W₂) := by
    simpa only [beta, VirtualCharacter.realize_sub] using
      (ClassFunction.supportedOn (R := k)
        (primeTISetInW W W₂)).sub_mem
          (h.primeTIDifference_mem_supportedOn q b)
          (h.primeTIDifference_mem_supportedOn r b)
  have hp := h.characterPairing_induce_primeTISet
    (VirtualCharacter.realize alpha) (VirtualCharacter.realize beta)
    halpha hbeta
  have hrealizeAlpha :
      (h.prime_cycTIhyp).induceClassFunction
          (VirtualCharacter.realize alpha) =
        VirtualCharacter.realize
          (h.primeTIInducedDifference i j -
            h.primeTIInducedDifference a j) := by
    dsimp only [alpha]
    rw [VirtualCharacter.realize_sub, map_sub,
      VirtualCharacter.realize_sub,
      h.realize_primeTIInducedDifference,
      h.realize_primeTIInducedDifference]
  have hrealizeBeta :
      (h.prime_cycTIhyp).induceClassFunction
          (VirtualCharacter.realize beta) =
        VirtualCharacter.realize
          (h.primeTIInducedDifference q b -
            h.primeTIInducedDifference r b) := by
    dsimp only [beta]
    rw [VirtualCharacter.realize_sub, map_sub,
      VirtualCharacter.realize_sub,
      h.realize_primeTIInducedDifference,
      h.realize_primeTIInducedDifference]
  rw [hrealizeAlpha, hrealizeBeta,
    VirtualCharacter.characterPairing_realize,
    VirtualCharacter.characterPairing_realize] at hp
  have hsource : coeffDot alpha beta = 0 := by
    simp [alpha, beta, coeffDot_sub_left, coeffDot_sub_right,
      h.coeffDot_primeTIDifference_right_ne, hjb]
  rw [hsource, Int.cast_zero] at hp
  exact Int.cast_injective (by simpa only [Int.cast_zero] using hp)

/-- The unscaled signed-coordinate differences from distinct columns are
orthogonal. -/
private theorem primeTIColumnIndex_difference_pairing_right_ne
    (i a q r : IrreducibleCharacter W₁ k)
    (j b : IrreducibleCharacter W₂ k) (hjb : j ≠ b) :
    characterPairing
        (VirtualCharacter.realize
          (Finsupp.single ((h.primeTIColumnData j).index i) 1 -
            Finsupp.single ((h.primeTIColumnData j).index a) 1))
        (VirtualCharacter.realize
          (Finsupp.single ((h.primeTIColumnData b).index q) 1 -
            Finsupp.single ((h.primeTIColumnData b).index r) 1)) = 0 := by
  have hzero := h.coeffDot_primeTIInducedDifference_sub_right_ne
    i a q r j b hjb
  rw [h.primeTIColumnData_difference j i a,
    h.primeTIColumnData_difference b q r,
    coeffDot_smul_left, coeffDot_smul_right] at hzero
  have hj0 : (h.primeTIColumnData j).sign ≠ 0 :=
    isSign_ne_zero (h.primeTIColumnData j).isSign_sign
  have hb0 : (h.primeTIColumnData b).sign ≠ 0 :=
    isSign_ne_zero (h.primeTIColumnData b).isSign_sign
  have hcoeff :
      coeffDot
          (Finsupp.single ((h.primeTIColumnData j).index i) 1 -
            Finsupp.single ((h.primeTIColumnData j).index a) 1)
          (Finsupp.single ((h.primeTIColumnData b).index q) 1 -
            Finsupp.single ((h.primeTIColumnData b).index r) 1) = 0 := by
    exact (mul_eq_zero.mp
      ((mul_eq_zero.mp hzero).resolve_left hj0)).resolve_left hb0
  rw [VirtualCharacter.characterPairing_realize, hcoeff]
  exact Int.cast_zero

private theorem exists_irreducible_ne
    (i : IrreducibleCharacter W₁ k) :
    ∃ a : IrreducibleCharacter W₁ k, a ≠ i := by
  letI : IsCyclic W₁ := h.complement_cyclic
  by_cases hi : i = IrreducibleCharacter.trivial
  · subst i
    exact IrreducibleCharacter.exists_ne_trivial_of_one_lt_card
      (k := k) h.prime_cycTIhyp.one_lt_card_left
  · exact ⟨IrreducibleCharacter.trivial, ne_comm.mp hi⟩

/-- The indices supplied column-by-column are globally injective.  This is
the four-character argument in the middle of the Coq proof of 4.3(b). -/
private theorem primeTIColumnIndex_injective :
    Function.Injective
      (fun p : IrreducibleCharacter W₁ k × IrreducibleCharacter W₂ k ↦
        (h.primeTIColumnData p.2).index p.1) := by
  rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ hindex
  by_cases hj : j₁ = j₂
  · subst j₂
    have hi := (h.primeTIColumnData j₁).index_injective hindex
    exact Prod.ext hi rfl
  obtain ⟨a₁, ha₁⟩ := h.exists_irreducible_ne i₁
  obtain ⟨a₂, ha₂⟩ := h.exists_irreducible_ne i₂
  let A : VirtualCharacter L k :=
    Finsupp.single ((h.primeTIColumnData j₁).index i₁) 1
  let B : VirtualCharacter L k :=
    Finsupp.single ((h.primeTIColumnData j₁).index a₁) 1
  let C : VirtualCharacter L k :=
    Finsupp.single ((h.primeTIColumnData j₂).index i₂) 1
  let D : VirtualCharacter L k :=
    Finsupp.single ((h.primeTIColumnData j₂).index a₂) 1
  have hAB : IntegralLattice.IsOrthonormalPair A B := by
    refine ⟨by simp [A, normSq], by simp [B, normSq], ?_⟩
    simp [A, B,
      (h.primeTIColumnData j₁).index_injective.ne ha₁.symm]
  have hCD : IntegralLattice.IsOrthonormalPair C D := by
    refine ⟨by simp [C, normSq], by simp [D, normSq], ?_⟩
    simp [C, D,
      (h.primeTIColumnData j₂).index_injective.ne ha₂.symm]
  have hpair :
      characterPairing (VirtualCharacter.realize (A - B))
        (VirtualCharacter.realize (C - D)) = 0 := by
    exact h.primeTIColumnIndex_difference_pairing_right_ne
      i₁ a₁ i₂ a₂ j₁ j₂ hj
  have hABOne : VirtualCharacter.realize (A - B) 1 = 0 := by
    exact h.primeTIColumnIndex_difference_one j₁ i₁ a₁
  have hCDOne : VirtualCharacter.realize (C - D) 1 = 0 := by
    exact h.primeTIColumnIndex_difference_one j₂ i₂ a₂
  have horth := orthonormal_vchar_diff_ortho_coeff
    A B C D hAB hCD hpair hABOne hCDOne
  have hAC : coeffDot A C = 1 := by
    simp [A, C, hindex]
  rw [hAC] at horth
  norm_num at horth

end PrimeTIHypothesis

/-! ## Assembly of the rectangle and restriction to `W \ W₂` -/

namespace PrimeTIHypothesis

variable (h : PrimeTIHypothesis L K W W₁ W₂ defW)

include h

private def primeTIRawIndex
    (p : IrreducibleCharacter W₁ k × IrreducibleCharacter W₂ k) :
    IrreducibleCharacter L k :=
  (h.primeTIColumnData p.2).index p.1

private def primeTIRawSign (j : IrreducibleCharacter W₂ k) : ℤ :=
  (h.primeTIColumnData j).sign

private theorem primeTIRawSign_isSign (j : IrreducibleCharacter W₂ k) :
    IsSign (h.primeTIRawSign j) :=
  (h.primeTIColumnData j).isSign_sign

private theorem primeTIRawIndex_injective :
    Function.Injective (h.primeTIRawIndex (k := k)) :=
  h.primeTIColumnIndex_injective (k := k)

/-- The signed target irreducible used by the restriction-complement
argument. -/
private def primeTISignedCharacter
    (p : IrreducibleCharacter W₁ k × IrreducibleCharacter W₂ k) :
    ClassFunction L k :=
  (h.primeTIRawSign p.2 : k) •
    (h.primeTIRawIndex p : ClassFunction L k)

private theorem primeTISignedCharacter_orthonormal
    (p q : IrreducibleCharacter W₁ k × IrreducibleCharacter W₂ k) :
    characterPairing (h.primeTISignedCharacter p)
        (h.primeTISignedCharacter q) =
      if p = q then 1 else 0 := by
  rw [primeTISignedCharacter, primeTISignedCharacter,
    characterPairing_smul_left, characterPairing_smul_right,
    IrreducibleCharacter.characterPairing_eq_ite]
  by_cases hpq : p = q
  · subst q
    rw [if_pos rfl, if_pos rfl]
    rcases h.primeTIRawSign_isSign p.2 with hs | hs <;>
      simp [hs]
  · rw [if_neg hpq]
    have hindex : h.primeTIRawIndex p ≠ h.primeTIRawIndex q :=
      h.primeTIRawIndex_injective.ne hpq
    rw [if_neg hindex, mul_zero, mul_zero]

/-- Realized form of the column decomposition. -/
private theorem induce_primeTIDifference_eq_signedCharacter
    (i : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k) :
    (h.prime_cycTIhyp).induceClassFunction
        (VirtualCharacter.realize (primeTIDifference defW i j)) =
      h.primeTISignedCharacter (i, j) -
        h.primeTISignedCharacter (IrreducibleCharacter.trivial, j) := by
  have hrep := congrArg VirtualCharacter.realize
    ((h.primeTIColumnData j).induce_eq i)
  rw [h.realize_primeTIInducedDifference] at hrep
  simpa [primeTISignedCharacter, primeTIRawIndex,
    primeTIRawSign, smul_sub] using hrep

private def primeTICharacterInSubgroupOf
    (p : IrreducibleCharacter W₁ k × IrreducibleCharacter W₂ k) :
    ClassFunction (W.subgroupOf L) k :=
  (h.prime_cycTIhyp).classFunctionSubgroupOfEquiv
    (IrreducibleCharacter.cyclicTICharacter defW p.1 p.2 :
      ClassFunction W k)

private theorem characterPairing_primeTIDifferenceBasisSubgroupOf
    (q : PrimeTIDifferenceIndex W₁ W₂ k)
    (p : IrreducibleCharacter W₁ k × IrreducibleCharacter W₂ k) :
    characterPairing
        (h.primeTIDifferenceBasisSubgroupOf q).val
        (h.primeTICharacterInSubgroupOf p) =
      if p = (q.1.1, q.2) then 1
      else if p = (IrreducibleCharacter.trivial, q.2) then -1
      else 0 := by
  rw [h.primeTIDifferenceBasisSubgroupOf_val]
  change characterPairing
      ((h.prime_cycTIhyp).classFunctionSubgroupOfEquiv
        (VirtualCharacter.realize
          (primeTIDifference defW q.1.1 q.2)))
      ((h.prime_cycTIhyp).classFunctionSubgroupOfEquiv
        (IrreducibleCharacter.cyclicTICharacter defW p.1 p.2 :
          ClassFunction W k)) = _
  rw [(h.prime_cycTIhyp).characterPairing_classFunctionSubgroupOfEquiv]
  exact h.characterPairing_primeTIDifference_character
    q.1.1 p.1 q.2 p.2 q.1.2

/-- Induction of every member of `V2base` is its Fourier expansion in the
signed target rectangle. -/
private theorem induce_primeTIDifferenceBasis_expansion
    (q : PrimeTIDifferenceIndex W₁ W₂ k) :
    ClassFunction.induce (W.subgroupOf L)
        (h.primeTIDifferenceBasisSubgroupOf q).val =
      ∑ p : IrreducibleCharacter W₁ k × IrreducibleCharacter W₂ k,
        characterPairing
            (h.primeTIDifferenceBasisSubgroupOf q).val
            (h.primeTICharacterInSubgroupOf p) •
          h.primeTISignedCharacter p := by
  calc
    ClassFunction.induce (W.subgroupOf L)
          (h.primeTIDifferenceBasisSubgroupOf q).val =
        (h.prime_cycTIhyp).induceClassFunction
          (VirtualCharacter.realize
            (primeTIDifference defW q.1.1 q.2)) := by
      rw [h.primeTIDifferenceBasisSubgroupOf_val]
      rfl
    _ = h.primeTISignedCharacter (q.1.1, q.2) -
          h.primeTISignedCharacter (IrreducibleCharacter.trivial, q.2) :=
      h.induce_primeTIDifference_eq_signedCharacter q.1.1 q.2
    _ = ∑ p : IrreducibleCharacter W₁ k × IrreducibleCharacter W₂ k,
          characterPairing
              (h.primeTIDifferenceBasisSubgroupOf q).val
              (h.primeTICharacterInSubgroupOf p) •
            h.primeTISignedCharacter p := by
      classical
      simp only [h.characterPairing_primeTIDifferenceBasisSubgroupOf]
      simp only [ite_smul, one_smul, zero_smul]
      have hab :
          ((q.1.1, q.2) :
              IrreducibleCharacter W₁ k × IrreducibleCharacter W₂ k) ≠
            (IrreducibleCharacter.trivial, q.2) := by
        intro hpairs
        exact q.1.2 (congrArg Prod.fst hpairs)
      have hterm
          (p : IrreducibleCharacter W₁ k × IrreducibleCharacter W₂ k) :
          (if p = (q.1.1, q.2) then h.primeTISignedCharacter p
            else if p = (IrreducibleCharacter.trivial, q.2) then
              (-1 : k) • h.primeTISignedCharacter p
            else 0) =
          (if p = (q.1.1, q.2) then
              h.primeTISignedCharacter (q.1.1, q.2) else 0) +
            (if p = (IrreducibleCharacter.trivial, q.2) then
              -h.primeTISignedCharacter
                (IrreducibleCharacter.trivial, q.2) else 0) := by
        by_cases hpa : p = (q.1.1, q.2)
        · subst p
          simp [hab]
        · by_cases hpb : p = (IrreducibleCharacter.trivial, q.2)
          · subst p
            simp only [hpa, if_false, if_pos, zero_add]
            ext x
            simp
          · simp [hpa, hpb]
      calc
        h.primeTISignedCharacter (q.1.1, q.2) -
              h.primeTISignedCharacter
                (IrreducibleCharacter.trivial, q.2) =
            ∑ p : IrreducibleCharacter W₁ k ×
                IrreducibleCharacter W₂ k,
              ((if p = (q.1.1, q.2) then
                  h.primeTISignedCharacter (q.1.1, q.2) else 0) +
                (if p = (IrreducibleCharacter.trivial, q.2) then
                  -h.primeTISignedCharacter
                    (IrreducibleCharacter.trivial, q.2) else 0)) := by
          rw [Finset.sum_add_distrib]
          simp [sub_eq_add_neg]
        _ = ∑ p : IrreducibleCharacter W₁ k ×
              IrreducibleCharacter W₂ k,
            if p = (q.1.1, q.2) then h.primeTISignedCharacter p
            else if p = (IrreducibleCharacter.trivial, q.2) then
              (-1 : k) • h.primeTISignedCharacter p
            else 0 := by
          apply Finset.sum_congr rfl
          intro p _
          exact (hterm p).symm

/-- The restriction/complement conclusion before removing the displayed
signs. -/
private theorem primeTISignedRestrictionAndVanish :
    (∀ p : IrreducibleCharacter W₁ k × IrreducibleCharacter W₂ k,
      Set.EqOn
        (fun w : W ↦ h.primeTISignedCharacter p
          ⟨w, h.directProduct_le_group w.property⟩)
        (fun w : W ↦
          IrreducibleCharacter.cyclicTICharacter defW p.1 p.2 w)
        (primeTISetInW W W₂)) ∧
      ∀ nu : ClassFunction L k,
        (∀ p : IrreducibleCharacter W₁ k × IrreducibleCharacter W₂ k,
          characterPairing nu (h.primeTISignedCharacter p) = 0) →
        Set.EqOn
          (fun w : W ↦ nu ⟨w, h.directProduct_le_group w.property⟩)
          0 (primeTISetInW W W₂) := by
  have hres := equiv_restrict_compl_ortho_set
    (W.subgroupOf L) h.primeTISetInSubgroupOf
    h.primeTISetInSubgroupOf_conjStable
    h.primeTISetInSubgroupOf_invStable
    (h.primeTIDifferenceBasisSubgroupOf (k := k))
    (h.primeTICharacterInSubgroupOf (k := k))
    (h.primeTISignedCharacter (k := k))
    h.primeTISignedCharacter_orthonormal
    h.induce_primeTIDifferenceBasis_expansion
  constructor
  · intro p w hw
    let w' : W.subgroupOf L :=
      ⟨⟨w, h.directProduct_le_group w.property⟩, w.property⟩
    have hw' : w' ∈ h.primeTISetInSubgroupOf := by
      simpa [w', primeTISetInSubgroupOf] using hw
    have hvalue := hres.1 p hw'
    change h.primeTISignedCharacter p
        ⟨w, h.directProduct_le_group w.property⟩ =
      IrreducibleCharacter.cyclicTICharacter defW p.1 p.2
        (Subgroup.subgroupOfEquivOfLe h.directProduct_le_group w') at hvalue
    have hmap :
        Subgroup.subgroupOfEquivOfLe h.directProduct_le_group w' = w := by
      apply Subtype.ext
      rfl
    simpa [hmap] using hvalue
  · intro nu hnu w hw
    let w' : W.subgroupOf L :=
      ⟨⟨w, h.directProduct_le_group w.property⟩, w.property⟩
    have hw' : w' ∈ h.primeTISetInSubgroupOf := by
      simpa [w', primeTISetInSubgroupOf] using hw
    exact ClassFunction.eq_zero_of_mem_vanishingOn
      (hres.2 nu hnu) hw'

/-- Removing the sign from the first restriction-complement conclusion. -/
private theorem primeTIRawIndex_eqOn
    (i : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k) :
    Set.EqOn
      (fun w : W ↦ (h.primeTIRawIndex (i, j) : ClassFunction L k)
        ⟨w, h.directProduct_le_group w.property⟩)
      (fun w : W ↦
        (h.primeTIRawSign j : k) *
          IrreducibleCharacter.cyclicTICharacter defW i j w)
      (primeTISetInW W W₂) := by
  intro w hw
  have hsigned := h.primeTISignedRestrictionAndVanish.1 (i, j) hw
  change
    (h.primeTIRawIndex (i, j) : ClassFunction L k)
        ⟨w, h.directProduct_le_group w.property⟩ = _
  change
    (h.primeTIRawSign j : k) *
        (h.primeTIRawIndex (i, j) : ClassFunction L k)
          ⟨w, h.directProduct_le_group w.property⟩ = _ at hsigned
  rcases h.primeTIRawSign_isSign j with hs | hs
  · simpa [hs] using hsigned
  · have hneg := congrArg Neg.neg hsigned
    simpa [hs] using hneg

/-- An irreducible character outside the rectangle vanishes on `W \ W₂`. -/
private theorem not_primeTIRawIndex_vanish
    (chi : IrreducibleCharacter L k)
    (hchi : chi ∉ Set.range h.primeTIRawIndex) :
    Set.EqOn
      (fun w : W ↦ (chi : ClassFunction L k)
        ⟨w, h.directProduct_le_group w.property⟩)
      0 (primeTISetInW W W₂) := by
  apply h.primeTISignedRestrictionAndVanish.2
  intro p
  rw [primeTISignedCharacter, characterPairing_smul_right,
    IrreducibleCharacter.characterPairing_eq_ite]
  have hne : chi ≠ h.primeTIRawIndex p := by
    intro heq
    exact hchi ⟨p, heq.symm⟩
  simp [hne]

end PrimeTIHypothesis

/-! ## The public prime-TI character data -/

/-- The complete output of Peterfalvi 4.3(b,c), kept as one record so the
choice of every column is coherent. -/
structure PrimeTICharacterData
    (h : PrimeTIHypothesis L K W W₁ W₂ defW)
    (iso : CyclicTIIsometryData (k := k) h.prime_cycTIhyp) where
  index : IrreducibleCharacter W₁ k × IrreducibleCharacter W₂ k →
    IrreducibleCharacter L k
  sign : IrreducibleCharacter W₂ k → ℤ
  isSign_sign : ∀ j, IsSign (sign j)
  index_injective : Function.Injective index
  induce_difference : ∀ i j,
    (h.prime_cycTIhyp).induceClassFunction
        (VirtualCharacter.realize (primeTIDifference defW i j)) =
      (sign j : k) •
        ((index (i, j) : ClassFunction L k) -
          (index (IrreducibleCharacter.trivial, j) : ClassFunction L k))
  isometry_character : ∀ i j,
    iso.linearMap
        (IrreducibleCharacter.cyclicTICharacter defW i j :
          ClassFunction W k) =
      (sign j : k) • (index (i, j) : ClassFunction L k)
  restrict_character : ∀ i j,
    Set.EqOn
      (fun w : W ↦ (index (i, j) : ClassFunction L k)
        ⟨w, h.directProduct_le_group w.property⟩)
      (fun w : W ↦ (sign j : k) *
        IrreducibleCharacter.cyclicTICharacter defW i j w)
      (primeTISetInW W W₂)
  outside_vanish : ∀ chi : IrreducibleCharacter L k,
    chi ∉ Set.range index →
      Set.EqOn
        (fun w : W ↦ (chi : ClassFunction L k)
          ⟨w, h.directProduct_le_group w.property⟩)
        0 (primeTISetInW W W₂)

namespace PrimeTIHypothesis

variable (h : PrimeTIHypothesis L K W W₁ W₂ defW)

include h

/-- Construct the prime-TI rectangle from explicit cyclic-TI isometry data. -/
def primeTICharacterData
    (iso : CyclicTIIsometryData (k := k) h.prime_cycTIhyp) :
    PrimeTICharacterData (k := k) h iso where
  index := h.primeTIRawIndex
  sign := h.primeTIRawSign
  isSign_sign := h.primeTIRawSign_isSign
  index_injective := h.primeTIRawIndex_injective
  induce_difference := by
    intro i j
    simpa [primeTISignedCharacter, primeTIRawIndex, primeTIRawSign,
      smul_sub] using h.induce_primeTIDifference_eq_signedCharacter i j
  isometry_character := by
    intro i j
    let nu : VirtualCharacter L k :=
      Finsupp.single (h.primeTIRawIndex (i, j)) (h.primeTIRawSign j)
    have hnorm : normSq nu = 1 := by
      rw [normSq]
      dsimp only [nu]
      rw [coeffDot_single_left]
      simpa [pow_two] using
        isSign_iff_sq_eq_one.mp (h.primeTIRawSign_isSign j)
    have heq :
        Set.EqOn
          (fun w : W ↦ VirtualCharacter.realize nu
            ⟨w, h.directProduct_le_group w.property⟩)
          (IrreducibleCharacter.cyclicTICharacter defW i j : W → k)
          (cyclicTISetInW W W₁ W₂) := by
      intro w hw
      have hraw := h.primeTIRawIndex_eqOn i j
        (h.cyclicTISetInW_subset_primeTISetInW hw)
      change
        (h.primeTIRawIndex (i, j) : ClassFunction L k)
            ⟨w, h.directProduct_le_group w.property⟩ =
          (h.primeTIRawSign j : k) *
            IrreducibleCharacter.cyclicTICharacter defW i j w at hraw
      dsimp only [nu]
      simp only [VirtualCharacter.realize_single,
        ClassFunction.smul_apply, smul_eq_mul]
      rw [hraw]
      rcases h.primeTIRawSign_isSign j with hs | hs <;>
        simp [hs]
    have hid := iso.eq_in_cyclicTIIsometry_realize
      (IrreducibleCharacter.cyclicTICharacter defW i j) nu hnorm heq
    simpa [nu, primeTIRawIndex, primeTIRawSign] using hid.symm
  restrict_character := h.primeTIRawIndex_eqOn
  outside_vanish := h.not_primeTIRawIndex_vanish

/-- The irreducible-character index `primeTI_Iirr`. -/
def primeTIIndex
    (iso : CyclicTIIsometryData (k := k) h.prime_cycTIhyp)
    (p : IrreducibleCharacter W₁ k × IrreducibleCharacter W₂ k) :
    IrreducibleCharacter L k :=
  (h.primeTICharacterData iso).index p

/-- The sign `primeTI_Isign`, represented as the integer `+1` or `-1`. -/
def primeTISign
    (iso : CyclicTIIsometryData (k := k) h.prime_cycTIhyp)
    (j : IrreducibleCharacter W₂ k) : ℤ :=
  (h.primeTICharacterData iso).sign j

/-- Coq's signed irreducible index `primeTIdIirr`. -/
def primeTIdIirr
    (iso : CyclicTIIsometryData (k := k) h.prime_cycTIhyp)
    (p : IrreducibleCharacter W₁ k × IrreducibleCharacter W₂ k) :
    ℤ × IrreducibleCharacter L k :=
  (h.primeTISign iso p.2, h.primeTIIndex iso p)

/-- The irreducible character `mu2_ i j`. -/
def primeTICharacter
    (iso : CyclicTIIsometryData (k := k) h.prime_cycTIhyp)
    (i : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k) : ClassFunction L k :=
  (h.primeTIIndex iso (i, j) : ClassFunction L k)

@[simp]
theorem primeTICharacter_apply
    (iso : CyclicTIIsometryData (k := k) h.prime_cycTIhyp)
    (i : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k) (x : L) :
    h.primeTICharacter iso i j x = h.primeTIIndex iso (i, j) x :=
  rfl

/-- The sign is always `+1` or `-1`. -/
theorem primeTISign_isSign
    (iso : CyclicTIIsometryData (k := k) h.prime_cycTIhyp)
    (j : IrreducibleCharacter W₂ k) :
    IsSign (h.primeTISign iso j) :=
  (h.primeTICharacterData iso).isSign_sign j

/-- Peterfalvi 4.3(b,c), in one source-shaped conjunction. -/
theorem primeTIirr_spec
    (iso : CyclicTIIsometryData (k := k) h.prime_cycTIhyp) :
    Function.Injective (h.primeTIIndex iso) ∧
      (∀ i j,
        (h.prime_cycTIhyp).induceClassFunction
            (VirtualCharacter.realize (primeTIDifference defW i j)) =
          (h.primeTISign iso j : k) •
            (h.primeTICharacter iso i j -
              h.primeTICharacter iso IrreducibleCharacter.trivial j)) ∧
      (∀ i j,
        iso.linearMap
            (IrreducibleCharacter.cyclicTICharacter defW i j :
              ClassFunction W k) =
          (h.primeTISign iso j : k) • h.primeTICharacter iso i j) ∧
      (∀ i j,
        Set.EqOn
          (fun w : W ↦ h.primeTICharacter iso i j
            ⟨w, h.directProduct_le_group w.property⟩)
          (fun w : W ↦ (h.primeTISign iso j : k) *
            IrreducibleCharacter.cyclicTICharacter defW i j w)
          (primeTISetInW W W₂)) ∧
      ∀ chi : IrreducibleCharacter L k,
        chi ∉ Set.range (h.primeTIIndex iso) →
          Set.EqOn
            (fun w : W ↦ (chi : ClassFunction L k)
              ⟨w, h.directProduct_le_group w.property⟩)
            0 (primeTISetInW W W₂) := by
  let data := h.primeTICharacterData iso
  exact ⟨data.index_injective, data.induce_difference,
    data.isometry_character, data.restrict_character,
    data.outside_vanish⟩

end PrimeTIHypothesis

end

end Submission.OddOrder.PF
