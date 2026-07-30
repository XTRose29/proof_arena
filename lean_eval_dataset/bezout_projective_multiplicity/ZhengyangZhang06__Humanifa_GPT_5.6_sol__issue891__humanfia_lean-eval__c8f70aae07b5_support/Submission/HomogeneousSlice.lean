import Submission.GlobalSlice

open LeanEval.AlgebraicGeometry
open scoped LinearAlgebra.Projectivization
open MvPolynomial

namespace Submission.Helpers

variable {K : Type*} [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The homogeneous ideal obtained by adjoining the slicing linear form itself.
Its affine zero locus is the vertex of the cone when the slice avoids every
projective intersection point. -/
noncomputable def homogeneousSlicePolynomialIdeal {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K)
    (a : Fin (n + 1) → K) :
    Ideal (MvPolynomial (Fin (n + 1)) K) :=
  Ideal.span (Set.range f ∪ {linearForm a})

/-- The ordered list of homogeneous equations defining the vertex slice. -/
noncomputable def homogeneousSliceSequence {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K)
    (a : Fin (n + 1) → K) :
    List (MvPolynomial (Fin (n + 1)) K) :=
  List.ofFn f ++ [linearForm a]

lemma ideal_ofList_homogeneousSliceSequence {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K)
    (a : Fin (n + 1) → K) :
    Ideal.ofList (homogeneousSliceSequence f a) =
      homogeneousSlicePolynomialIdeal f a := by
  rw [homogeneousSliceSequence, homogeneousSlicePolynomialIdeal,
    Ideal.ofList_append, Ideal.ofList_singleton, ← Ideal.span_union]
  congr 1
  ext g
  simp

@[simp]
lemma length_homogeneousSliceSequence {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K)
    (a : Fin (n + 1) → K) :
    (homogeneousSliceSequence f a).length = n + 1 := by
  simp [homogeneousSliceSequence]

lemma mem_zeroLocus_homogeneousSlicePolynomialIdeal {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K)
    (a q : Fin (n + 1) → K) :
    q ∈ MvPolynomial.zeroLocus K (homogeneousSlicePolynomialIdeal f a) ↔
      (∀ k, eval q (f k) = 0) ∧ eval q (linearForm a) = 0 := by
  rw [homogeneousSlicePolynomialIdeal, MvPolynomial.zeroLocus_span]
  simp [and_comm]

lemma homogeneousSlicePolynomialIdeal_isHomogeneous {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K)
    (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (a : Fin (n + 1) → K) :
    (homogeneousSlicePolynomialIdeal f a).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) := by
  apply Ideal.homogeneous_span
  rintro g (⟨k, rfl⟩ | rfl)
  · exact ⟨d k, hd k⟩
  · exact ⟨1, linearForm_isHomogeneous a⟩

lemma eval_zero_of_isHomogeneous_pos {n N : ℕ}
    {g : MvPolynomial (Fin (n + 1)) K}
    (hg : g.IsHomogeneous N) (hN : 0 < N) :
    eval (0 : Fin (n + 1) → K) g = 0 := by
  have h := eval_smul_of_isHomogeneous hg (0 : K)
    (0 : Fin (n + 1) → K)
  simpa [zero_pow hN.ne'] using h

lemma zeroLocus_homogeneousSlicePolynomialIdeal_eq_singleton
    [IsAlgClosed K] {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K)
    (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (hd_pos : ∀ k, 1 ≤ d k)
    (a : Fin (n + 1) → K)
    (hne : ∀ p ∈ ⋂ k, vanishingSet (f k),
      eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    MvPolynomial.zeroLocus K (homogeneousSlicePolynomialIdeal f a) = {0} := by
  ext q
  constructor
  · intro hq
    obtain ⟨hf, ha⟩ :=
      (mem_zeroLocus_homogeneousSlicePolynomialIdeal f a q).mp hq
    by_contra hq0
    let p := Projectivization.mk K q hq0
    have hp : p ∈ ⋂ k, vanishingSet (f k) :=
      projectivization_mk_mem_vanishingSet_iInter f d hd q hq0 hf
    apply hne p hp
    obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep K q hq0
    rw [← hu]
    change eval ((u : K) • q) (linearForm a) = 0
    rw [eval_smul_of_isHomogeneous (linearForm_isHomogeneous a), ha,
      mul_zero]
  · intro hq
    rw [Set.mem_singleton_iff] at hq
    subst q
    rw [mem_zeroLocus_homogeneousSlicePolynomialIdeal]
    refine ⟨fun k => eval_zero_of_isHomogeneous_pos (hd k)
      (lt_of_lt_of_le Nat.zero_lt_one (hd_pos k)), ?_⟩
    simp [linearForm]

lemma homogeneousSlicePolynomialQuotient_module_finite
    [IsAlgClosed K] {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K)
    (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (hd_pos : ∀ k, 1 ≤ d k)
    (a : Fin (n + 1) → K)
    (hne : ∀ p ∈ ⋂ k, vanishingSet (f k),
      eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    Module.Finite K
      (MvPolynomial (Fin (n + 1)) K ⧸
        homogeneousSlicePolynomialIdeal f a) := by
  apply quotient_module_finite_of_zeroLocus_finite
  rw [zeroLocus_homogeneousSlicePolynomialIdeal_eq_singleton
    f d hd hd_pos a hne]
  exact Set.finite_singleton 0

lemma homogeneousSlicePolynomialIdeal_radical_eq_maxIdealAt_zero
    [IsAlgClosed K] {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K)
    (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (hd_pos : ∀ k, 1 ≤ d k)
    (a : Fin (n + 1) → K)
    (hne : ∀ p ∈ ⋂ k, vanishingSet (f k),
      eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    (homogeneousSlicePolynomialIdeal f a).radical = maxIdealAt 0 := by
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K),
    zeroLocus_homogeneousSlicePolynomialIdeal_eq_singleton
      f d hd hd_pos a hne]
  ext g
  rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
  rfl

end Submission.Helpers
