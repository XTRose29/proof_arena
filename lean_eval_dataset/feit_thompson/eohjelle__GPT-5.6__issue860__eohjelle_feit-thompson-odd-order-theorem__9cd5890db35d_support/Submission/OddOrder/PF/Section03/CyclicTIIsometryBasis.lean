import Submission.OddOrder.PF.Section03.ColumnPivot
import Submission.OddOrder.PF.Section03.CyclicTIBeta

/-!
# The cyclic-TI isometry basis

This file ports `cyclicTIiso_basis_exists` from Peterfalvi Section 3.  The
norm-three beta characters form a rectangular Gram configuration.  Row and
column pivots select signed irreducible characters detecting its rows and
columns.  Correcting beta by those pivots gives an orthonormal rectangular
family of virtual characters.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Finsupp
open scoped Classical

universe u

variable {Gamma k : Type u} [Group Gamma] [Fintype Gamma]
  [Field k] [IsAlgClosed k] [CharZero k]
  {G W W₁ W₂ : Subgroup Gamma}
  {defW : IsInternalDirectProductIn W₁ W₂ W}

local instance cyclicTIIsometryBasisInvertibleCard
    {H : Type u} [Group H] [Fintype H] :
    Invertible (Nat.card H : k) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

private abbrev NontrivialCharacterIndex
    (H : Subgroup Gamma) (k : Type u) [Field k]
    [IsAlgClosed k] [CharZero k] :=
  {chi : IrreducibleCharacter H k //
    chi ≠ IrreducibleCharacter.trivial}

private theorem card_nontrivialCharacterIndex
    {H : Subgroup Gamma} [IsCyclic H] :
    Fintype.card (NontrivialCharacterIndex H k) = Nat.card H - 1 := by
  calc
    Fintype.card (NontrivialCharacterIndex H k) =
        Fintype.card (IrreducibleCharacter H k) - 1 :=
      Set.card_ne_eq _
    _ = Nat.card H - 1 := by
      rw [IrreducibleCharacter.card_eq_natCard_of_isCyclic]

private structure SignedCoordinate (kappa : Type*) where
  coordinate : kappa
  sign : ℤ
  isSign_sign : IsSign sign

namespace SignedCoordinate

variable {kappa : Type*}

def vector (d : SignedCoordinate kappa) : IntegralLattice kappa :=
  single d.coordinate d.sign

@[simp]
theorem coeffDot_self (d : SignedCoordinate kappa) :
    coeffDot d.vector d.vector = 1 := by
  rw [vector, coeffDot_single_left]
  simpa [pow_two] using isSign_iff_sq_eq_one.mp d.isSign_sign

/-- If one lattice vector detects one signed coordinate but annihilates
another, the two signed coordinates are distinct and hence orthogonal. -/
theorem coeffDot_eq_zero_of_probe
    (d e : SignedCoordinate kappa) (phi : IntegralLattice kappa)
    (hd : coeffDot phi d.vector = 1)
    (he : coeffDot phi e.vector = 0) :
    coeffDot d.vector e.vector = 0 := by
  classical
  rw [vector, coeffDot_single_right] at hd he
  by_cases hq : d.coordinate = e.coordinate
  · have hphi_e : phi e.coordinate = 0 :=
      (mul_eq_zero.mp he).resolve_right (isSign_ne_zero e.isSign_sign)
    have hphi_d : phi d.coordinate = 0 := by simpa [hq] using hphi_e
    rw [hphi_d] at hd
    norm_num at hd
  · simp [vector, hq]

end SignedCoordinate

private def ambientSignedCoordinate :
    SignedCoordinate (IrreducibleCharacter G k) where
  coordinate := IrreducibleCharacter.trivial
  sign := 1
  isSign_sign := Or.inl rfl

@[simp]
private theorem ambientSignedCoordinate_vector :
    (ambientSignedCoordinate (G := G) (k := k)).vector =
      ambientTrivialVirtualCharacter (G := G) (k := k) :=
  rfl

private structure CyclicTIPivots
    (h : CyclicTIHypothesis G W W₁ W₂ defW) where
  Xi0 : NontrivialCharacterIndex W₁ k →
    SignedCoordinate (IrreducibleCharacter G k)
  X0j : NontrivialCharacterIndex W₂ k →
    SignedCoordinate (IrreducibleCharacter G k)
  Xi0_detects : ∀ (i : NontrivialCharacterIndex W₁ k)
      (p : CyclicTINontrivialIndex W₁ W₂ k),
    coeffDot (h.cyclicTIBeta p) (Xi0 i).vector =
      if p.1 = i then 1 else 0
  X0j_detects : ∀ (j : NontrivialCharacterIndex W₂ k)
      (p : CyclicTINontrivialIndex W₁ W₂ k),
    coeffDot (h.cyclicTIBeta p) (X0j j).vector =
      if p.2 = j then 1 else 0

private noncomputable def cyclicTIPivots
    (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    CyclicTIPivots (k := k) h := by
  letI : IsCyclic W₁ := h.left_cyclic
  letI : IsCyclic W₂ := h.right_cyclic
  let r := Fintype.card (NontrivialCharacterIndex W₁ k)
  let c := Fintype.card (NontrivialCharacterIndex W₂ k)
  let eI : Fin r ≃ NontrivialCharacterIndex W₁ k :=
    (Fintype.equivFin _).symm
  let eJ : Fin c ≃ NontrivialCharacterIndex W₂ k :=
    (Fintype.equivFin _).symm
  let beta : Fin r → Fin c → VirtualCharacter G k :=
    fun i j ↦ h.cyclicTIBeta (eI i, eJ j)
  have hrCard : r = Nat.card W₁ - 1 := by
    simpa [r] using
      (card_nontrivialCharacterIndex (Gamma := Gamma) (k := k)
        (H := W₁))
  have hcCard : c = Nat.card W₂ - 1 := by
    simpa [c] using
      (card_nontrivialCharacterIndex (Gamma := Gamma) (k := k)
        (H := W₂))
  have hleftTwo : 2 < Nat.card W₁ := h.two_lt_card_left
  have hrightTwo : 2 < Nat.card W₂ := h.two_lt_card_right
  have hrOne : 1 ≤ Nat.card W₁ := by omega
  have hcOne : 1 ≤ Nat.card W₂ := by omega
  have hrOdd : Odd (r + 1) := by
    rw [hrCard, Nat.sub_add_cancel hrOne]
    exact h.left_odd_card
  have hcOdd : Odd (c + 1) := by
    rw [hcCard, Nat.sub_add_cancel hcOne]
    exact h.right_odd_card
  have hr : 1 < r := by omega
  have hc : 1 < c := by omega
  have hrc : r ≠ c := by
    intro hrc'
    apply h.factor_card_ne
    omega
  have hgram : ∀ i j i' j',
      coeffDot (beta i j) (beta i' j') =
        ((if i = i' then 2 else 1) *
          (if j = j' then 2 else 1) - 1) := by
    intro i j i' j'
    simpa [beta] using
      h.coeffDot_cyclicTIBeta (eI i, eJ j) (eI i', eJ j')
  have hXi (i : NontrivialCharacterIndex W₁ k) :
      ∃ q epsilon, IsSign epsilon ∧ ∀ a b,
        coeffDot (beta a b) (single q epsilon) =
          if a = eI.symm i then 1 else 0 :=
    row_pivot beta hrOdd hcOdd hr hc hrc hgram (eI.symm i)
  choose qI epsilonI hI using hXi
  have hepsilonI (i : NontrivialCharacterIndex W₁ k) :
      IsSign (epsilonI i) := (hI i).1
  have hdetectI (i : NontrivialCharacterIndex W₁ k) : ∀ a b,
      coeffDot (beta a b) (single (qI i) (epsilonI i)) =
        if a = eI.symm i then 1 else 0 :=
    (hI i).2
  have hXj (j : NontrivialCharacterIndex W₂ k) :
      ∃ q epsilon, IsSign epsilon ∧ ∀ a b,
        coeffDot (beta a b) (single q epsilon) =
          if b = eJ.symm j then 1 else 0 :=
    column_pivot beta hrOdd hcOdd hr hc hrc hgram (eJ.symm j)
  choose qJ epsilonJ hJ using hXj
  have hepsilonJ (j : NontrivialCharacterIndex W₂ k) :
      IsSign (epsilonJ j) := (hJ j).1
  have hdetectJ (j : NontrivialCharacterIndex W₂ k) : ∀ a b,
      coeffDot (beta a b) (single (qJ j) (epsilonJ j)) =
        if b = eJ.symm j then 1 else 0 :=
    (hJ j).2
  refine
    { Xi0 := fun i ↦ ⟨qI i, epsilonI i, hepsilonI i⟩
      X0j := fun j ↦ ⟨qJ j, epsilonJ j, hepsilonJ j⟩
      Xi0_detects := ?_
      X0j_detects := ?_ }
  · intro i p
    simpa [SignedCoordinate.vector, beta] using
      hdetectI i (eI.symm p.1) (eJ.symm p.2)
  · intro j p
    simpa [SignedCoordinate.vector, beta] using
      hdetectJ j (eI.symm p.1) (eJ.symm p.2)

private noncomputable def leftNontrivialWitness
    (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    NontrivialCharacterIndex W₁ k := by
  letI : IsCyclic W₁ := h.left_cyclic
  let hex := IrreducibleCharacter.exists_ne_trivial_of_one_lt_card
    (k := k) h.one_lt_card_left
  exact ⟨hex.choose, hex.choose_spec⟩

private noncomputable def rightNontrivialWitness
    (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    NontrivialCharacterIndex W₂ k := by
  letI : IsCyclic W₂ := h.right_cyclic
  let hex := IrreducibleCharacter.exists_ne_trivial_of_one_lt_card
    (k := k) h.one_lt_card_right
  exact ⟨hex.choose, hex.choose_spec⟩

private def dualNontrivialIndex
    (j : NontrivialCharacterIndex W₂ k) :
    NontrivialCharacterIndex W₂ k := by
  refine ⟨IrreducibleCharacter.dual j.1, ?_⟩
  intro hdual
  apply j.2
  rw [← IrreducibleCharacter.dual_dual j.1, hdual,
    IrreducibleCharacter.dual_trivial]

private theorem dualNontrivialIndex_ne_self
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (j : NontrivialCharacterIndex W₂ k) :
    dualNontrivialIndex j ≠ j := by
  intro heq
  exact dual_ne_self_of_odd_of_ne_trivial h.right_odd_card j.2
    (congrArg Subtype.val heq)

private noncomputable def cyclicTIXi0
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (i : NontrivialCharacterIndex W₁ k) : VirtualCharacter G k :=
  ((cyclicTIPivots (k := k) h).Xi0 i).vector

private noncomputable def cyclicTIX0j
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (j : NontrivialCharacterIndex W₂ k) : VirtualCharacter G k :=
  ((cyclicTIPivots (k := k) h).X0j j).vector

@[simp]
private theorem coeffDot_cyclicTIBeta_cyclicTIXi0
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (p : CyclicTINontrivialIndex W₁ W₂ k)
    (i : NontrivialCharacterIndex W₁ k) :
    coeffDot (h.cyclicTIBeta p) (cyclicTIXi0 h i) =
      if p.1 = i then 1 else 0 := by
  simpa [cyclicTIXi0] using
    (cyclicTIPivots (k := k) h).Xi0_detects i p

@[simp]
private theorem coeffDot_cyclicTIBeta_cyclicTIX0j
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (p : CyclicTINontrivialIndex W₁ W₂ k)
    (j : NontrivialCharacterIndex W₂ k) :
    coeffDot (h.cyclicTIBeta p) (cyclicTIX0j h j) =
      if p.2 = j then 1 else 0 := by
  simpa [cyclicTIX0j] using
    (cyclicTIPivots (k := k) h).X0j_detects j p

@[simp]
private theorem coeffDot_cyclicTIXi0_cyclicTIBeta
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (i : NontrivialCharacterIndex W₁ k)
    (p : CyclicTINontrivialIndex W₁ W₂ k) :
    coeffDot (cyclicTIXi0 h i) (h.cyclicTIBeta p) =
      if p.1 = i then 1 else 0 := by
  rw [coeffDot_comm]
  exact coeffDot_cyclicTIBeta_cyclicTIXi0 h p i

@[simp]
private theorem coeffDot_cyclicTIX0j_cyclicTIBeta
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (j : NontrivialCharacterIndex W₂ k)
    (p : CyclicTINontrivialIndex W₁ W₂ k) :
    coeffDot (cyclicTIX0j h j) (h.cyclicTIBeta p) =
      if p.2 = j then 1 else 0 := by
  rw [coeffDot_comm]
  exact coeffDot_cyclicTIBeta_cyclicTIX0j h p j

@[simp]
private theorem coeffDot_cyclicTIBeta_ambient
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (p : CyclicTINontrivialIndex W₁ W₂ k) :
    coeffDot (h.cyclicTIBeta p)
      (ambientTrivialVirtualCharacter (G := G) (k := k)) = 0 :=
  h.coeffDot_cyclicTIBeta_ambientTrivial p

@[simp]
private theorem coeffDot_ambient_cyclicTIBeta
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (p : CyclicTINontrivialIndex W₁ W₂ k) :
    coeffDot (ambientTrivialVirtualCharacter (G := G) (k := k))
      (h.cyclicTIBeta p) = 0 := by
  rw [coeffDot_comm]
  exact coeffDot_cyclicTIBeta_ambient h p

@[simp]
private theorem coeffDot_cyclicTIXi0_self
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (i : NontrivialCharacterIndex W₁ k) :
    coeffDot (cyclicTIXi0 h i) (cyclicTIXi0 h i) = 1 := by
  simpa [cyclicTIXi0] using
    SignedCoordinate.coeffDot_self ((cyclicTIPivots (k := k) h).Xi0 i)

@[simp]
private theorem coeffDot_cyclicTIX0j_self
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (j : NontrivialCharacterIndex W₂ k) :
    coeffDot (cyclicTIX0j h j) (cyclicTIX0j h j) = 1 := by
  simpa [cyclicTIX0j] using
    SignedCoordinate.coeffDot_self ((cyclicTIPivots (k := k) h).X0j j)

@[simp]
private theorem coeffDot_cyclicTIXi0
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (i i' : NontrivialCharacterIndex W₁ k) :
    coeffDot (cyclicTIXi0 h i) (cyclicTIXi0 h i') =
      if i = i' then 1 else 0 := by
  by_cases hii : i = i'
  · subst i'
    simp
  · let p : CyclicTINontrivialIndex W₁ W₂ k :=
      (i, rightNontrivialWitness h)
    have hone : coeffDot (h.cyclicTIBeta p) (cyclicTIXi0 h i) = 1 := by
      simp [p]
    have hzero : coeffDot (h.cyclicTIBeta p) (cyclicTIXi0 h i') = 0 := by
      simp [p, hii]
    rw [if_neg hii]
    simpa [cyclicTIXi0] using
      SignedCoordinate.coeffDot_eq_zero_of_probe
        ((cyclicTIPivots (k := k) h).Xi0 i)
        ((cyclicTIPivots (k := k) h).Xi0 i')
        (h.cyclicTIBeta p) hone hzero

@[simp]
private theorem coeffDot_cyclicTIX0j
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (j j' : NontrivialCharacterIndex W₂ k) :
    coeffDot (cyclicTIX0j h j) (cyclicTIX0j h j') =
      if j = j' then 1 else 0 := by
  by_cases hjj : j = j'
  · subst j'
    simp
  · let p : CyclicTINontrivialIndex W₁ W₂ k :=
      (leftNontrivialWitness h, j)
    have hone : coeffDot (h.cyclicTIBeta p) (cyclicTIX0j h j) = 1 := by
      simp [p]
    have hzero : coeffDot (h.cyclicTIBeta p) (cyclicTIX0j h j') = 0 := by
      simp [p, hjj]
    rw [if_neg hjj]
    simpa [cyclicTIX0j] using
      SignedCoordinate.coeffDot_eq_zero_of_probe
        ((cyclicTIPivots (k := k) h).X0j j)
        ((cyclicTIPivots (k := k) h).X0j j')
        (h.cyclicTIBeta p) hone hzero

@[simp]
private theorem coeffDot_cyclicTIXi0_ambient
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (i : NontrivialCharacterIndex W₁ k) :
    coeffDot (cyclicTIXi0 h i)
      (ambientTrivialVirtualCharacter (G := G) (k := k)) = 0 := by
  let p : CyclicTINontrivialIndex W₁ W₂ k :=
    (i, rightNontrivialWitness h)
  have hone : coeffDot (h.cyclicTIBeta p) (cyclicTIXi0 h i) = 1 := by
    simp [p]
  have hzero : coeffDot (h.cyclicTIBeta p)
      (ambientTrivialVirtualCharacter (G := G) (k := k)) = 0 :=
    h.coeffDot_cyclicTIBeta_ambientTrivial p
  simpa [cyclicTIXi0] using
    SignedCoordinate.coeffDot_eq_zero_of_probe
      ((cyclicTIPivots (k := k) h).Xi0 i)
      (ambientSignedCoordinate (G := G) (k := k))
      (h.cyclicTIBeta p) hone hzero

@[simp]
private theorem coeffDot_cyclicTIX0j_ambient
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (j : NontrivialCharacterIndex W₂ k) :
    coeffDot (cyclicTIX0j h j)
      (ambientTrivialVirtualCharacter (G := G) (k := k)) = 0 := by
  let p : CyclicTINontrivialIndex W₁ W₂ k :=
    (leftNontrivialWitness h, j)
  have hone : coeffDot (h.cyclicTIBeta p) (cyclicTIX0j h j) = 1 := by
    simp [p]
  have hzero : coeffDot (h.cyclicTIBeta p)
      (ambientTrivialVirtualCharacter (G := G) (k := k)) = 0 :=
    h.coeffDot_cyclicTIBeta_ambientTrivial p
  simpa [cyclicTIX0j] using
    SignedCoordinate.coeffDot_eq_zero_of_probe
      ((cyclicTIPivots (k := k) h).X0j j)
      (ambientSignedCoordinate (G := G) (k := k))
      (h.cyclicTIBeta p) hone hzero

@[simp]
private theorem coeffDot_ambient_cyclicTIXi0
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (i : NontrivialCharacterIndex W₁ k) :
    coeffDot (ambientTrivialVirtualCharacter (G := G) (k := k))
      (cyclicTIXi0 h i) = 0 := by
  rw [coeffDot_comm]
  exact coeffDot_cyclicTIXi0_ambient h i

@[simp]
private theorem coeffDot_ambient_cyclicTIX0j
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (j : NontrivialCharacterIndex W₂ k) :
    coeffDot (ambientTrivialVirtualCharacter (G := G) (k := k))
      (cyclicTIX0j h j) = 0 := by
  rw [coeffDot_comm]
  exact coeffDot_cyclicTIX0j_ambient h j

@[simp]
private theorem coeffDot_cyclicTIXi0_cyclicTIX0j
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (i : NontrivialCharacterIndex W₁ k)
    (j : NontrivialCharacterIndex W₂ k) :
    coeffDot (cyclicTIXi0 h i) (cyclicTIX0j h j) = 0 := by
  let p : CyclicTINontrivialIndex W₁ W₂ k :=
    (i, dualNontrivialIndex j)
  have hone : coeffDot (h.cyclicTIBeta p) (cyclicTIXi0 h i) = 1 := by
    simp [p]
  have hzero : coeffDot (h.cyclicTIBeta p) (cyclicTIX0j h j) = 0 := by
    simp [p, dualNontrivialIndex_ne_self h j]
  simpa [cyclicTIXi0, cyclicTIX0j] using
    SignedCoordinate.coeffDot_eq_zero_of_probe
      ((cyclicTIPivots (k := k) h).Xi0 i)
      ((cyclicTIPivots (k := k) h).X0j j)
      (h.cyclicTIBeta p) hone hzero

@[simp]
private theorem coeffDot_cyclicTIX0j_cyclicTIXi0
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (j : NontrivialCharacterIndex W₂ k)
    (i : NontrivialCharacterIndex W₁ k) :
    coeffDot (cyclicTIX0j h j) (cyclicTIXi0 h i) = 0 := by
  rw [coeffDot_comm]
  exact coeffDot_cyclicTIXi0_cyclicTIX0j h i j

@[simp]
private theorem coeffDot_ambient_self :
    coeffDot (ambientTrivialVirtualCharacter (G := G) (k := k))
      (ambientTrivialVirtualCharacter (G := G) (k := k)) = 1 := by
  simp [ambientTrivialVirtualCharacter]

private theorem coeffDot_sub_left
    (f g z : VirtualCharacter G k) :
    coeffDot (f - g) z = coeffDot f z - coeffDot g z := by
  simp only [sub_eq_add_neg, coeffDot_add_left, coeffDot_neg_left]

private theorem coeffDot_sub_right
    (z f g : VirtualCharacter G k) :
    coeffDot z (f - g) = coeffDot z f - coeffDot z g := by
  simp only [sub_eq_add_neg, coeffDot_add_right, coeffDot_neg_right]

/-- The corrected beta family, including its trivial row and column. -/
private noncomputable def cyclicTIXi
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (i : IrreducibleCharacter W₁ k)
    (j : IrreducibleCharacter W₂ k) : VirtualCharacter G k :=
  if hi : i = IrreducibleCharacter.trivial then
    if hj : j = IrreducibleCharacter.trivial then
      ambientTrivialVirtualCharacter
    else
      -cyclicTIX0j h ⟨j, hj⟩
  else if hj : j = IrreducibleCharacter.trivial then
    -cyclicTIXi0 h ⟨i, hi⟩
  else
    h.cyclicTIBeta (⟨i, hi⟩, ⟨j, hj⟩) -
      cyclicTIXi0 h ⟨i, hi⟩ - cyclicTIX0j h ⟨j, hj⟩

@[simp]
private theorem cyclicTIXi_trivial_trivial
    (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    cyclicTIXi (k := k) h IrreducibleCharacter.trivial
        IrreducibleCharacter.trivial =
      ambientTrivialVirtualCharacter := by
  simp [cyclicTIXi]

@[simp]
private theorem cyclicTIXi_trivial_right
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    {j : IrreducibleCharacter W₂ k}
    (hj : j ≠ IrreducibleCharacter.trivial) :
    cyclicTIXi h IrreducibleCharacter.trivial j =
      -cyclicTIX0j h ⟨j, hj⟩ := by
  simp [cyclicTIXi, hj]

@[simp]
private theorem cyclicTIXi_left_trivial
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    {i : IrreducibleCharacter W₁ k}
    (hi : i ≠ IrreducibleCharacter.trivial) :
    cyclicTIXi h i IrreducibleCharacter.trivial =
      -cyclicTIXi0 h ⟨i, hi⟩ := by
  simp [cyclicTIXi, hi]

@[simp]
private theorem cyclicTIXi_nontrivial
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    {i : IrreducibleCharacter W₁ k}
    {j : IrreducibleCharacter W₂ k}
    (hi : i ≠ IrreducibleCharacter.trivial)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    cyclicTIXi h i j =
      h.cyclicTIBeta (⟨i, hi⟩, ⟨j, hj⟩) -
        cyclicTIXi0 h ⟨i, hi⟩ - cyclicTIX0j h ⟨j, hj⟩ := by
  simp [cyclicTIXi, hi, hj]

private theorem induceVirtualCharacter_eq_cyclicTIXi
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    {i : IrreducibleCharacter W₁ k}
    {j : IrreducibleCharacter W₂ k}
    (hi : i ≠ IrreducibleCharacter.trivial)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    h.induceVirtualCharacter (cyclicTIVirtualCharacter defW i j) =
      ambientTrivialVirtualCharacter -
        cyclicTIXi h i IrreducibleCharacter.trivial -
        cyclicTIXi h IrreducibleCharacter.trivial j +
        cyclicTIXi h i j := by
  rw [cyclicTIXi_left_trivial h hi, cyclicTIXi_trivial_right h hj,
    cyclicTIXi_nontrivial h hi hj]
  rw [CyclicTIHypothesis.cyclicTIBeta]
  abel

private theorem coeffDot_cyclicTIXi
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (i₁ i₂ : IrreducibleCharacter W₁ k)
    (j₁ j₂ : IrreducibleCharacter W₂ k) :
    coeffDot (cyclicTIXi h i₁ j₁) (cyclicTIXi h i₂ j₂) =
      if (i₁, j₁) = (i₂, j₂) then 1 else 0 := by
  by_cases hi₁ : i₁ = IrreducibleCharacter.trivial <;>
    by_cases hj₁ : j₁ = IrreducibleCharacter.trivial <;>
    by_cases hi₂ : i₂ = IrreducibleCharacter.trivial <;>
    by_cases hj₂ : j₂ = IrreducibleCharacter.trivial <;>
    by_cases hii : i₁ = i₂ <;>
    by_cases hjj : j₁ = j₂ <;>
    simp_all [cyclicTIXi, eq_comm,
      coeffDot_sub_left, coeffDot_sub_right, coeffDot_add_left,
      coeffDot_add_right, coeffDot_neg_left, coeffDot_neg_right,
      h.coeffDot_cyclicTIBeta] <;>
    ring

/-- The data supplied by the cyclic-TI isometry-basis construction.  Its
virtual-character type makes the source's separate integrality clause
automatic. -/
structure CyclicTIIsometryBasisData
    (h : CyclicTIHypothesis G W W₁ W₂ defW) where
  xi : IrreducibleCharacter W₁ k → IrreducibleCharacter W₂ k →
    VirtualCharacter G k
  xi_trivial_trivial :
    xi IrreducibleCharacter.trivial IrreducibleCharacter.trivial =
      ambientTrivialVirtualCharacter
  induce_eq : ∀ (i : IrreducibleCharacter W₁ k)
      (j : IrreducibleCharacter W₂ k),
    i ≠ IrreducibleCharacter.trivial →
    j ≠ IrreducibleCharacter.trivial →
    h.induceVirtualCharacter (cyclicTIVirtualCharacter defW i j) =
      ambientTrivialVirtualCharacter -
        xi i IrreducibleCharacter.trivial -
        xi IrreducibleCharacter.trivial j + xi i j
  coeffDot_xi : ∀ (i₁ i₂ : IrreducibleCharacter W₁ k)
      (j₁ j₂ : IrreducibleCharacter W₂ k),
    coeffDot (xi i₁ j₁) (xi i₂ j₂) =
      if (i₁, j₁) = (i₂, j₂) then 1 else 0

namespace CyclicTIHypothesis

/-- Construct the orthonormal virtual-character rectangle attached to a
cyclic-TI direct product. -/
def cyclicTIIsometryBasisData
    (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    CyclicTIIsometryBasisData (k := k) h where
  xi := cyclicTIXi h
  xi_trivial_trivial := cyclicTIXi_trivial_trivial h
  induce_eq := fun _ _ hi hj ↦
    induceVirtualCharacter_eq_cyclicTIXi h hi hj
  coeffDot_xi := coeffDot_cyclicTIXi h

/-- Existential form matching Coq's `cyclicTIiso_basis_exists`. -/
theorem cyclicTIiso_basis_exists
    (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    ∃ xi : IrreducibleCharacter W₁ k → IrreducibleCharacter W₂ k →
        VirtualCharacter G k,
      xi IrreducibleCharacter.trivial IrreducibleCharacter.trivial =
          ambientTrivialVirtualCharacter ∧
      (∀ (i : IrreducibleCharacter W₁ k)
          (j : IrreducibleCharacter W₂ k),
        i ≠ IrreducibleCharacter.trivial →
        j ≠ IrreducibleCharacter.trivial →
        h.induceVirtualCharacter (cyclicTIVirtualCharacter defW i j) =
          ambientTrivialVirtualCharacter -
            xi i IrreducibleCharacter.trivial -
            xi IrreducibleCharacter.trivial j + xi i j) ∧
      ∀ (i₁ i₂ : IrreducibleCharacter W₁ k)
          (j₁ j₂ : IrreducibleCharacter W₂ k),
        coeffDot (xi i₁ j₁) (xi i₂ j₂) =
          if (i₁, j₁) = (i₂, j₂) then 1 else 0 := by
  let data := h.cyclicTIIsometryBasisData (k := k)
  exact ⟨data.xi, data.xi_trivial_trivial, data.induce_eq,
    data.coeffDot_xi⟩

end CyclicTIHypothesis

namespace CyclicTIIsometryBasisData

/-- Class-function form of orthonormality. -/
theorem characterPairing_xi
    {h : CyclicTIHypothesis G W W₁ W₂ defW}
    (data : CyclicTIIsometryBasisData (k := k) h)
    (i₁ i₂ : IrreducibleCharacter W₁ k)
    (j₁ j₂ : IrreducibleCharacter W₂ k) :
    characterPairing
        (VirtualCharacter.realize (data.xi i₁ j₁))
        (VirtualCharacter.realize (data.xi i₂ j₂)) =
      if (i₁, j₁) = (i₂, j₂) then 1 else 0 := by
  rw [VirtualCharacter.characterPairing_realize, data.coeffDot_xi]
  split <;> norm_num

end CyclicTIIsometryBasisData

end

end Submission.OddOrder.PF
