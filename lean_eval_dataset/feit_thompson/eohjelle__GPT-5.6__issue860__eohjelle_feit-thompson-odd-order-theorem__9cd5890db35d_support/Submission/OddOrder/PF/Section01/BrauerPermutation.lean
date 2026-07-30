import Mathlib.LinearAlgebra.Matrix.Permutation
import Submission.OddOrder.PF.Section01.CharacterCompleteness
import Submission.OddOrder.PF.Section01.OddConjugateIrreducible

/-!
The character-table reduction of Brauer's permutation lemma.

Duality permutes the irreducible-character rows of the character table, while
inversion permutes its conjugacy-class columns.  The character table
intertwines the corresponding permutation representations.  Consequently,
as soon as the irreducible characters span the class functions (equivalently,
as soon as the character table is square), the two permutations have equal
trace and hence the same number of fixed points.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators

universe u v

namespace ClassFunction

variable {G : Type u} {k : Type v} [Group G] [Field k]

/-- Pull a class function back along inversion. -/
def inverseLinear : ClassFunction G k →ₗ[k] ClassFunction G k where
  toFun f :=
    ⟨fun g ↦ f g⁻¹, fun x g ↦ by
      simpa only [conj_inv] using ClassFunction.conj_apply f x g⁻¹⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem inverseLinear_apply (f : ClassFunction G k) (g : G) :
    inverseLinear f g = f g⁻¹ :=
  rfl

end ClassFunction

variable {G : Type u} {k : Type v} [Group G] [Field k]

namespace ClassFunction

/-- Regard a class function as a function on conjugacy classes. -/
def onConjClasses (f : ClassFunction G k) : ConjClasses G → k :=
  Quotient.lift f (fun a b hab ↦ by
    obtain ⟨x, hx⟩ := isConj_iff.mp hab
    have h := ClassFunction.conj_apply f x a
    rw [hx] at h
    exact h.symm)

@[simp]
theorem onConjClasses_mk (f : ClassFunction G k) (g : G) :
    onConjClasses f (ConjClasses.mk g) = f g :=
  rfl

/-- Class functions are linearly equivalent to arbitrary functions on the
finite type of conjugacy classes. -/
def conjClassesLinearEquiv :
    ClassFunction G k ≃ₗ[k] (ConjClasses G → k) where
  toFun := onConjClasses
  invFun F :=
    ⟨fun g ↦ F (ConjClasses.mk g), fun x g ↦ by
      apply congrArg F
      apply ConjClasses.mk_eq_mk_iff_isConj.mpr
      exact (isConj_iff.mpr ⟨x, rfl⟩).symm⟩
  left_inv f := by
    ext g
    rfl
  right_inv F := by
    funext C
    induction C using Quotient.inductionOn
    rfl
  map_add' f g := by
    funext C
    induction C using Quotient.inductionOn
    rfl
  map_smul' a f := by
    funext C
    induction C using Quotient.inductionOn
    rfl

@[simp]
theorem finset_sum_apply {I : Type*} (s : Finset I)
    (f : I → ClassFunction G k) (g : G) :
    (∑ i ∈ s, f i) g = ∑ i ∈ s, f i g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha, ih]

end ClassFunction

section PermutationOperators

variable [Fintype G] [IsAlgClosed k] [CharZero k]

local instance : Invertible (Nat.card G : k) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

local instance : DecidableEq (IrreducibleCharacter G k) := Classical.decEq _
local instance : Fintype (ConjClasses G) := Fintype.ofFinite _
local instance : DecidableEq (ConjClasses G) := Classical.decEq _

/-- The permutation operator on row coefficients induced by duality. -/
def dualPermutationLinear :
    (IrreducibleCharacter G k → k) →ₗ[k] (IrreducibleCharacter G k → k) := by
  classical
  exact Matrix.toLin'
    (Equiv.Perm.permMatrix k
      (IrreducibleCharacter.dualEquiv :
        Equiv.Perm (IrreducibleCharacter G k)))

@[simp]
theorem dualPermutationLinear_apply (a : IrreducibleCharacter G k → k)
    (chi : IrreducibleCharacter G k) :
    dualPermutationLinear a chi = a (IrreducibleCharacter.dual chi) := by
  rw [dualPermutationLinear, Matrix.toLin'_apply,
    Matrix.permMatrix_mulVec]
  rfl

/-- The permutation operator on conjugacy-class coordinates induced by
inversion. -/
def inverseClassPermutationLinear :
    (ConjClasses G → k) →ₗ[k] (ConjClasses G → k) := by
  classical
  exact Matrix.toLin'
    (Equiv.Perm.permMatrix k
      (ConjClasses.inverseEquiv : Equiv.Perm (ConjClasses G)))

omit [IsAlgClosed k] [CharZero k] in
  @[simp]
  theorem inverseClassPermutationLinear_apply (a : ConjClasses G → k)
      (C : ConjClasses G) :
      inverseClassPermutationLinear a C = a (ConjClasses.inverse C) := by
    rw [inverseClassPermutationLinear, Matrix.toLin'_apply,
      Matrix.permMatrix_mulVec]
    rfl

omit [IsAlgClosed k] [CharZero k] in
  /-- In conjugacy-class coordinates, pullback along element inversion is the
  permutation matrix of inversion on conjugacy classes. -/
  theorem conjClassesLinearEquiv_conj_inverseLinear :
      ClassFunction.conjClassesLinearEquiv.conj ClassFunction.inverseLinear =
        inverseClassPermutationLinear (G := G) (k := k) := by
    apply LinearMap.ext
    intro f
    funext C
    induction C using Quotient.inductionOn with
    | _ g =>
        change ClassFunction.conjClassesLinearEquiv
            (ClassFunction.inverseLinear
              (ClassFunction.conjClassesLinearEquiv.symm f)) (ConjClasses.mk g) =
          inverseClassPermutationLinear f (ConjClasses.mk g)
        rw [inverseClassPermutationLinear_apply]
        rfl

/-- Synthesis of a class function from its irreducible-character row
coefficients. -/
def irreducibleCharacterSynthesis :
    (IrreducibleCharacter G k → k) →ₗ[k] ClassFunction G k :=
  Fintype.linearCombination k
    (fun chi : IrreducibleCharacter G k ↦ (chi : ClassFunction G k))

/-- The character table intertwines row duality with inversion of class
functions. -/
theorem irreducibleCharacterSynthesis_dualPermutation (a : IrreducibleCharacter G k → k) :
    irreducibleCharacterSynthesis (dualPermutationLinear a) =
      ClassFunction.inverseLinear (irreducibleCharacterSynthesis a) := by
  ext g
  simp only [irreducibleCharacterSynthesis, Fintype.linearCombination_apply,
    dualPermutationLinear_apply, ClassFunction.inverseLinear_apply,
    ClassFunction.finset_sum_apply, ClassFunction.smul_apply, smul_eq_mul]
  apply Fintype.sum_equiv IrreducibleCharacter.dualEquiv
  intro chi
  change a (IrreducibleCharacter.dual chi) * chi g =
    a (IrreducibleCharacter.dual chi) *
      IrreducibleCharacter.dual chi g⁻¹
  rw [IrreducibleCharacter.dual_apply, inv_inv]

/-- Completeness of ordinary irreducible characters: their class functions
span the full space of class functions. -/
def IrreducibleCharacterComplete : Prop :=
  Submodule.span k
      (Set.range (fun chi : IrreducibleCharacter G k ↦
        (chi : ClassFunction G k))) = ⊤

/-- Ordinary irreducible characters form a basis of the class functions. -/
theorem irreducibleCharacterComplete :
    IrreducibleCharacterComplete (G := G) (k := k) :=
  irreducibleCharacter_span_eq_top

/-- The character table is square: it has as many irreducible-character rows
as conjugacy-class columns.  This is the remaining standard character-theory
input after the matrix argument below. -/
def IrreducibleCharacterTableSquare : Prop :=
  Fintype.card (IrreducibleCharacter G k) = Fintype.card (ConjClasses G)

/-- A square character table is complete, because its rows are already known
to be linearly independent by the first orthogonality relation. -/
theorem irreducibleCharacterComplete_of_tableSquare
    (hsquare : IrreducibleCharacterTableSquare (G := G) (k := k)) :
    IrreducibleCharacterComplete (G := G) (k := k) := by
  apply IrreducibleCharacter.linearIndependent.span_eq_top_of_card_eq_finrank'
  calc
    Fintype.card (IrreducibleCharacter G k) = Fintype.card (ConjClasses G) :=
      hsquare
    _ = Module.finrank k (ConjClasses G → k) :=
      (Module.finrank_fintype_fun_eq_card k).symm
    _ = Module.finrank k (ClassFunction G k) :=
      (ClassFunction.conjClassesLinearEquiv (G := G) (k := k)).finrank_eq.symm

/-- Under character completeness, synthesis is the character-table linear
equivalence. -/
def irreducibleCharacterSynthesisEquiv (hcomplete :
    IrreducibleCharacterComplete (G := G) (k := k)) :
    (IrreducibleCharacter G k → k) ≃ₗ[k] ClassFunction G k :=
  LinearEquiv.ofBijective irreducibleCharacterSynthesis
    ⟨IrreducibleCharacter.linearIndependent.fintypeLinearCombination_injective,
      (span_range_eq_top_iff_surjective_fintypeLinearCombination k _).mp hcomplete⟩

/-- In a complete character table, row duality and class-function inversion
are conjugate linear operators. -/
theorem irreducibleCharacterSynthesisEquiv_conj_dualPermutation
    (hcomplete : IrreducibleCharacterComplete (G := G) (k := k)) :
    (irreducibleCharacterSynthesisEquiv hcomplete).conj dualPermutationLinear =
      ClassFunction.inverseLinear := by
  ext f g
  let a := (irreducibleCharacterSynthesisEquiv hcomplete).symm f
  have h := irreducibleCharacterSynthesis_dualPermutation (G := G) (k := k) a
  simpa [irreducibleCharacterSynthesisEquiv, a,
    LinearEquiv.conj_apply_apply] using congrArg (fun q : ClassFunction G k ↦ q g) h

/-- Brauer's fixed-point cardinality follows from completeness of the
irreducible character table. -/
theorem brauerPermutationCardinality_of_complete
    (hcomplete : IrreducibleCharacterComplete (G := G) (k := k)) :
    BrauerPermutationCardinality (G := G) (k := k) := by
  have hrow :
      LinearMap.trace k (IrreducibleCharacter G k → k) dualPermutationLinear =
        ((Function.fixedPoints
          (IrreducibleCharacter.dualEquiv (G := G) (k := k))).ncard : k) := by
    rw [dualPermutationLinear, Matrix.trace_toLin'_eq,
      Matrix.trace_permutation]
  have hclass :
      LinearMap.trace k (ConjClasses G → k) inverseClassPermutationLinear =
        ((Function.fixedPoints
          (ConjClasses.inverseEquiv (G := G))).ncard : k) := by
    rw [inverseClassPermutationLinear, Matrix.trace_toLin'_eq,
      Matrix.trace_permutation]
  have htrace₁ := LinearMap.trace_conj'
    (R := k) (ClassFunction.inverseLinear (G := G) (k := k))
      (ClassFunction.conjClassesLinearEquiv (G := G) (k := k))
  rw [conjClassesLinearEquiv_conj_inverseLinear (G := G) (k := k)] at htrace₁
  have htrace₂ := LinearMap.trace_conj'
    (R := k) (dualPermutationLinear (G := G) (k := k))
      (irreducibleCharacterSynthesisEquiv (G := G) (k := k) hcomplete)
  rw [irreducibleCharacterSynthesisEquiv_conj_dualPermutation
    (G := G) (k := k) hcomplete] at htrace₂
  have hcast :
      ((Function.fixedPoints
        (IrreducibleCharacter.dualEquiv (G := G) (k := k))).ncard : k) =
        ((Function.fixedPoints
          (ConjClasses.inverseEquiv (G := G))).ncard : k) := by
    rw [← hrow, ← hclass, htrace₁, htrace₂]
  have hnat :
      (Function.fixedPoints
        (IrreducibleCharacter.dualEquiv (G := G) (k := k))).ncard =
        (Function.fixedPoints
          (ConjClasses.inverseEquiv (G := G))).ncard :=
    Nat.cast_injective hcast
  exact hnat

/-- Brauer's permutation lemma: duality on irreducible characters and
inversion on conjugacy classes have the same number of fixed points. -/
theorem brauerPermutationCardinality :
    BrauerPermutationCardinality (G := G) (k := k) :=
  brauerPermutationCardinality_of_complete irreducibleCharacterComplete

/-- Brauer's permutation-cardinality lemma reduced to the assertion that the
ordinary character table is square. -/
theorem brauerPermutationCardinality_of_tableSquare
    (hsquare : IrreducibleCharacterTableSquare (G := G) (k := k)) :
    BrauerPermutationCardinality (G := G) (k := k) :=
  brauerPermutationCardinality_of_complete
    (irreducibleCharacterComplete_of_tableSquare hsquare)

/-- Peterfalvi 1.1 from the standard square-character-table theorem. -/
theorem odd_eq_conj_irr1_of_tableSquare
    (hsquare : IrreducibleCharacterTableSquare (G := G) (k := k))
    (hodd : Odd (Nat.card G)) (chi : IrreducibleCharacter G k) :
    IrreducibleCharacter.dual chi = chi ↔
      chi = IrreducibleCharacter.trivial :=
  odd_eq_conj_irr1_of_brauer
    (brauerPermutationCardinality_of_tableSquare hsquare) hodd chi

/-- Peterfalvi 1.1: in a finite group of odd order, the only irreducible
character fixed by contragredient duality is the trivial character. -/
theorem odd_eq_conj_irr1
    (hodd : Odd (Nat.card G)) (chi : IrreducibleCharacter G k) :
    IrreducibleCharacter.dual chi = chi ↔
      chi = IrreducibleCharacter.trivial :=
  odd_eq_conj_irr1_of_brauer brauerPermutationCardinality hodd chi

end PermutationOperators

end

end Submission.OddOrder.PF
