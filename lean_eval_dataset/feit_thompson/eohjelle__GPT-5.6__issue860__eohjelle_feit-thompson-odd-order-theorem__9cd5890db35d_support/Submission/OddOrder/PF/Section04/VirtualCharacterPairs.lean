import Submission.OddOrder.PF.Section01.RestrictionComplementEquivalence
import Submission.OddOrder.PF.Section01.VirtualCharacterIsometry

/-!
# Two orthonormal pairs of virtual characters

This file ports Peterfalvi 4.1.  The source states the result for class
functions known to be virtual characters.  Here virtual characters are the
free integral lattice on the irreducible characters, so the main argument is
first isolated for an arbitrary integral lattice equipped with a nonvanishing
additive "degree" functional.  Evaluation of a virtual character at the
identity supplies that functional in the character-theoretic specialization.

The source assumes that its two coefficient scalars are fixed by complex
conjugation.  The pairing used in this development is the symmetric
inverse-argument pairing and is bilinear over the coefficient field, so no
corresponding reality hypotheses are needed.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped Classical

universe u v

namespace IntegralLattice

/-- Two lattice vectors are orthonormal when each has norm one and their
mutual coefficient pairing vanishes. -/
def IsOrthonormalPair {kappa : Type*}
    (a b : IntegralLattice kappa) : Prop :=
  normSq a = 1 ∧ normSq b = 1 ∧ coeffDot a b = 0

/-- Four lattice vectors are orthonormal, displayed as two already-grouped
pairs. -/
def IsOrthonormalFour {kappa : Type*}
    (a b c d : IntegralLattice kappa) : Prop :=
  IsOrthonormalPair a b ∧ IsOrthonormalPair c d ∧
    coeffDot a c = 0 ∧ coeffDot a d = 0 ∧
      coeffDot b c = 0 ∧ coeffDot b d = 0

theorem IsOrthonormalPair.swap {kappa : Type*}
    {a b : IntegralLattice kappa} (h : IsOrthonormalPair a b) :
    IsOrthonormalPair b a := by
  exact ⟨h.2.1, h.1, by rw [coeffDot_comm, h.2.2]⟩

end IntegralLattice

private theorem coeffDot_sub_left'
    {kappa : Type*} (a b c : IntegralLattice kappa) :
    coeffDot (a - b) c = coeffDot a c - coeffDot b c := by
  rw [sub_eq_add_neg, coeffDot_add_left, coeffDot_neg_left]
  rfl

private theorem coeffDot_sub_swap
    {kappa : Type*} (a b c : IntegralLattice kappa) :
    coeffDot (b - a) c = -coeffDot (a - b) c := by
  rw [coeffDot_sub_left', coeffDot_sub_left']
  ring

private theorem addHom_sub_swap
    {kappa A : Type*} [AddCommGroup A]
    (degree : IntegralLattice kappa →+ A)
    (a b : IntegralLattice kappa) :
    degree (b - a) = -degree (a - b) := by
  rw [map_sub, map_sub]
  abel

private theorem eq_sign_smul_of_normSq_eq_one_of_coeffDot_ne_zero
    {kappa : Type*} (a c : IntegralLattice kappa)
    (ha : normSq a = 1) (hc : normSq c = 1)
    (hac : coeffDot a c ≠ 0) :
    ∃ epsilon : ℤ, IsSign epsilon ∧ c = epsilon • a := by
  classical
  obtain ⟨i, epsilon, hepsilon, rfl⟩ :=
    eq_signed_single_of_normSq_eq_one a ha
  obtain ⟨j, delta, hdelta, rfl⟩ :=
    eq_signed_single_of_normSq_eq_one c hc
  have hij : i = j := by
    by_contra hij
    apply hac
    simp [hij]
  subst j
  rcases hepsilon with rfl | rfl <;>
    rcases hdelta with rfl | rfl
  · exact ⟨1, Or.inl rfl, by simp⟩
  · exact ⟨-1, Or.inr rfl, by simp⟩
  · exact ⟨-1, Or.inr rfl, by simp⟩
  · exact ⟨1, Or.inl rfl, by simp⟩

private theorem first_cross_eq_zero
    {kappa K : Type*} [Field K] [CharZero K]
    (degree : IntegralLattice kappa →+ K)
    (degree_ne_zero : ∀ f : IntegralLattice kappa,
      normSq f = 1 → degree f ≠ 0)
    (a b c d : IntegralLattice kappa) (u v : K)
    (hab : IntegralLattice.IsOrthonormalPair a b)
    (hcd : IntegralLattice.IsOrthonormalPair c d)
    (hu : u ≠ 0)
    (hpair :
      u * (coeffDot (a - b) c : K) -
        v * (coeffDot (a - b) d : K) = 0)
    (habDegree : degree (a - b) = 0)
    (hcdDegree : u * degree c - v * degree d = 0) :
    coeffDot a c = 0 := by
  rcases hab with ⟨ha, hb, hab⟩
  rcases hcd with ⟨hc, hd, hcd⟩
  by_contra hac0
  obtain ⟨s, hs, hca⟩ :=
    eq_sign_smul_of_normSq_eq_one_of_coeffDot_ne_zero a c ha hc hac0
  have hs0 : s ≠ 0 := isSign_ne_zero hs
  have hsK0 : (s : K) ≠ 0 := Int.cast_ne_zero.mpr hs0
  have hac : coeffDot a c = s := by
    rw [hca, coeffDot_smul_right, ← normSq, ha, mul_one]
  have hbc : coeffDot b c = 0 := by
    rw [hca, coeffDot_smul_right, coeffDot_comm b a, hab, mul_zero]
  have had : coeffDot a d = 0 := by
    rw [hca, coeffDot_smul_left] at hcd
    exact (mul_eq_zero.mp hcd).resolve_left hs0
  have hpair' :
      u * (s : K) + v * (coeffDot b d : K) = 0 := by
    rw [coeffDot_sub_left', coeffDot_sub_left', hac, hbc, had] at hpair
    simpa using hpair
  have hbd0 : coeffDot b d ≠ 0 := by
    intro hbd
    apply mul_ne_zero hu hsK0
    simpa [hbd] using hpair'
  obtain ⟨t, ht, hdb⟩ :=
    eq_sign_smul_of_normSq_eq_one_of_coeffDot_ne_zero b d hb hd hbd0
  have hbd : coeffDot b d = t := by
    rw [hdb, coeffDot_smul_right, ← normSq, hb, mul_one]
  have hsum : u * (s : K) + v * (t : K) = 0 := by
    simpa [hbd] using hpair'
  have habDegree' : degree a = degree b := by
    rw [map_sub] at habDegree
    exact sub_eq_zero.mp habDegree
  have hcdDegree' :
      u * (s : K) * degree a - v * (t : K) * degree b = 0 := by
    rw [hca, hdb, map_zsmul, map_zsmul] at hcdDegree
    simpa only [← Int.cast_smul_eq_zsmul K, smul_eq_mul, mul_assoc] using hcdDegree
  rw [← habDegree'] at hcdDegree'
  have hscalar : u * (s : K) - v * (t : K) = 0 := by
    have hfactor :
        (u * (s : K) - v * (t : K)) * degree a = 0 := by
      calc
        (u * (s : K) - v * (t : K)) * degree a =
            u * (s : K) * degree a - v * (t : K) * degree a := by ring
        _ = 0 := hcdDegree'
    exact (mul_eq_zero.mp hfactor).resolve_right (degree_ne_zero a ha)
  have htwo : (2 : K) * (u * (s : K)) = 0 := by
    calc
      (2 : K) * (u * (s : K)) =
          (u * (s : K) - v * (t : K)) +
            (u * (s : K) + v * (t : K)) := by ring
      _ = 0 := by rw [hscalar, hsum, zero_add]
  exact (mul_ne_zero (by norm_num) (mul_ne_zero hu hsK0)) htwo

namespace IntegralLattice

/-- Integral-lattice form of Peterfalvi's `vchar_pairs_orthonormal`.

The additive functional abstracts evaluation at the identity.  Its only
essential property is that it does not vanish on norm-one lattice vectors. -/
theorem pairs_orthonormal
    {kappa K : Type*} [Field K] [CharZero K]
    (degree : IntegralLattice kappa →+ K)
    (degree_ne_zero : ∀ f : IntegralLattice kappa,
      normSq f = 1 → degree f ≠ 0)
    (a b c d : IntegralLattice kappa) (u v : K)
    (hab : IsOrthonormalPair a b)
    (hcd : IsOrthonormalPair c d)
    (hu : u ≠ 0) (hv : v ≠ 0)
    (hpair :
      u * (coeffDot (a - b) c : K) -
        v * (coeffDot (a - b) d : K) = 0)
    (habDegree : degree (a - b) = 0)
    (hcdDegree : u * degree c - v * degree d = 0) :
    IsOrthonormalFour a b c d := by
  have hab' := hab.swap
  have hcd' := hcd.swap
  have hpairAB :
      u * (coeffDot (b - a) c : K) -
        v * (coeffDot (b - a) d : K) = 0 := by
    rw [coeffDot_sub_swap a b c, coeffDot_sub_swap a b d,
      Int.cast_neg, Int.cast_neg]
    calc
      u * -(coeffDot (a - b) c : K) -
          v * -(coeffDot (a - b) d : K) =
          -(u * (coeffDot (a - b) c : K) -
            v * (coeffDot (a - b) d : K)) := by ring
      _ = 0 := by rw [hpair, neg_zero]
  have habDegreeAB : degree (b - a) = 0 := by
    rw [addHom_sub_swap degree a b, habDegree, neg_zero]
  have hpairCD :
      v * (coeffDot (a - b) d : K) -
        u * (coeffDot (a - b) c : K) = 0 := by
    calc
      v * (coeffDot (a - b) d : K) -
          u * (coeffDot (a - b) c : K) =
          -(u * (coeffDot (a - b) c : K) -
            v * (coeffDot (a - b) d : K)) := by ring
      _ = 0 := by rw [hpair, neg_zero]
  have hcdDegreeCD : v * degree d - u * degree c = 0 := by
    calc
      v * degree d - u * degree c =
          -(u * degree c - v * degree d) := by ring
      _ = 0 := by rw [hcdDegree, neg_zero]
  have hpairABCD :
      v * (coeffDot (b - a) d : K) -
        u * (coeffDot (b - a) c : K) = 0 := by
    rw [coeffDot_sub_swap a b d, coeffDot_sub_swap a b c,
      Int.cast_neg, Int.cast_neg]
    calc
      v * -(coeffDot (a - b) d : K) -
          u * -(coeffDot (a - b) c : K) =
          u * (coeffDot (a - b) c : K) -
            v * (coeffDot (a - b) d : K) := by ring
      _ = 0 := hpair
  have hac := first_cross_eq_zero degree degree_ne_zero
    a b c d u v hab hcd hu hpair habDegree hcdDegree
  have hbc := first_cross_eq_zero degree degree_ne_zero
    b a c d u v hab' hcd hu hpairAB habDegreeAB hcdDegree
  have had := first_cross_eq_zero degree degree_ne_zero
    a b d c v u hab hcd' hv hpairCD habDegree hcdDegreeCD
  have hbd := first_cross_eq_zero degree degree_ne_zero
    b a d c v u hab' hcd' hv hpairABCD habDegreeAB hcdDegreeCD
  exact ⟨hab, hcd, hac, had, hbc, hbd⟩

end IntegralLattice

namespace VirtualCharacter

variable {G : Type u} {K : Type v} [Group G] [Field K]

/-- Evaluation at the identity, as an additive functional on virtual
characters. -/
def evalOne : VirtualCharacter G K →+ K where
  toFun f := realize f 1
  map_zero' := by simp
  map_add' f g := by simp

@[simp]
theorem evalOne_apply (f : VirtualCharacter G K) :
    evalOne f = realize f 1 :=
  rfl

end VirtualCharacter

private theorem irreducibleCharacter_apply_one_ne_zero
    {G : Type u} {K : Type v} [Group G] [Field K] [CharZero K]
    (chi : IrreducibleCharacter G K) : chi 1 ≠ 0 := by
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Nontrivial chi.representation := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    apply CategoryTheory.id_nonzero chi.representation
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro x
    exact Subsingleton.elim _ _
  rw [← chi.representation_character, FDRep.char_one]
  exact Nat.cast_ne_zero.mpr Module.finrank_pos.ne'

namespace VirtualCharacter

variable {G : Type u} {K : Type v} [Group G] [Field K] [CharZero K]

/-- Evaluation at the identity is nonzero on every norm-one virtual
character. -/
theorem evalOne_ne_zero_of_normSq_eq_one
    (f : VirtualCharacter G K) (hf : normSq f = 1) :
    evalOne f ≠ 0 := by
  obtain ⟨chi, epsilon, hepsilon, rfl⟩ :=
    eq_signed_single_of_normSq_eq_one f hf
  simp only [evalOne_apply, realize_single, ClassFunction.smul_apply,
    smul_eq_mul]
  exact mul_ne_zero (Int.cast_ne_zero.mpr (isSign_ne_zero hepsilon))
    (irreducibleCharacter_apply_one_ne_zero chi)

end VirtualCharacter

private theorem characterPairing_sub_right'
    {G : Type u} {K : Type v} [Group G] [Fintype G] [Field K]
    (f g h : ClassFunction G K) :
    characterPairing f (g - h) =
      characterPairing f g - characterPairing f h := by
  change characterPairingLeft f (g - h) = _
  exact map_sub (characterPairingLeft f) g h

/-- Peterfalvi 4.1, `vchar_pairs_orthonormal`, in the virtual-character
model. -/
theorem vchar_pairs_orthonormal
    {G : Type u} {K : Type v} [Group G] [Fintype G]
    [Field K] [IsAlgClosed K] [CharZero K]
    (a b c d : VirtualCharacter G K) (u v : K)
    (hab : IntegralLattice.IsOrthonormalPair a b)
    (hcd : IntegralLattice.IsOrthonormalPair c d)
    (hu : u ≠ 0) (hv : v ≠ 0)
    (hpair :
      characterPairing (VirtualCharacter.realize (a - b))
        (u • VirtualCharacter.realize c -
          v • VirtualCharacter.realize d) = 0)
    (habOne : VirtualCharacter.realize (a - b) 1 = 0)
    (hcdOne :
      (u • VirtualCharacter.realize c -
        v • VirtualCharacter.realize d) 1 = 0) :
    IntegralLattice.IsOrthonormalFour a b c d := by
  have hpair' :
      u * (coeffDot (a - b) c : K) -
        v * (coeffDot (a - b) d : K) = 0 := by
    rw [characterPairing_sub_right',
      characterPairing_smul_right, characterPairing_smul_right,
      VirtualCharacter.characterPairing_realize,
      VirtualCharacter.characterPairing_realize] at hpair
    exact hpair
  have habDegree : VirtualCharacter.evalOne (a - b) = 0 := habOne
  have hcdDegree :
      u * VirtualCharacter.evalOne c -
        v * VirtualCharacter.evalOne d = 0 := by
    simpa only [VirtualCharacter.evalOne_apply,
      ClassFunction.sub_apply, ClassFunction.smul_apply, smul_eq_mul] using hcdOne
  exact IntegralLattice.pairs_orthonormal VirtualCharacter.evalOne
    VirtualCharacter.evalOne_ne_zero_of_normSq_eq_one
    a b c d u v hab hcd hu hv hpair' habDegree hcdDegree

/-- Coefficient-lattice form of the source corollary
`orthonormal_vchar_diff_ortho`. -/
theorem orthonormal_vchar_diff_ortho_coeff
    {G : Type u} {K : Type v} [Group G] [Fintype G]
    [Field K] [IsAlgClosed K] [CharZero K]
    (a b c d : VirtualCharacter G K)
    (hab : IntegralLattice.IsOrthonormalPair a b)
    (hcd : IntegralLattice.IsOrthonormalPair c d)
    (hpair :
      characterPairing (VirtualCharacter.realize (a - b))
        (VirtualCharacter.realize (c - d)) = 0)
    (habOne : VirtualCharacter.realize (a - b) 1 = 0)
    (hcdOne : VirtualCharacter.realize (c - d) 1 = 0) :
    coeffDot a c = 0 := by
  have hfour := vchar_pairs_orthonormal a b c d (1 : K) (1 : K)
    hab hcd one_ne_zero one_ne_zero
    (by simpa using hpair) habOne (by simpa using hcdOne)
  exact hfour.2.2.1

/-- Realized-character form of Peterfalvi's
`orthonormal_vchar_diff_ortho`: the first members of the two pairs are
orthogonal. -/
theorem orthonormal_vchar_diff_ortho
    {G : Type u} {K : Type v} [Group G] [Fintype G]
    [Field K] [IsAlgClosed K] [CharZero K]
    (a b c d : VirtualCharacter G K)
    (hab : IntegralLattice.IsOrthonormalPair a b)
    (hcd : IntegralLattice.IsOrthonormalPair c d)
    (hpair :
      characterPairing (VirtualCharacter.realize (a - b))
        (VirtualCharacter.realize (c - d)) = 0)
    (habOne : VirtualCharacter.realize (a - b) 1 = 0)
    (hcdOne : VirtualCharacter.realize (c - d) 1 = 0) :
    characterPairing (VirtualCharacter.realize a)
      (VirtualCharacter.realize c) = 0 := by
  rw [VirtualCharacter.characterPairing_realize,
    orthonormal_vchar_diff_ortho_coeff a b c d hab hcd
      hpair habOne hcdOne]
  exact Int.cast_zero

end


end Submission.OddOrder.PF
