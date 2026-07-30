import Submission.HilbertCount
import Submission.StableBridge
import Submission.LocalGlobal

open LeanEval.AlgebraicGeometry MvPolynomial RingTheory.Sequence
open scoped LinearAlgebra.Projectivization Pointwise

variable {K : Type*} [Field K]

namespace Submission.Helpers

attribute [local instance] MvPolynomial.gradedAlgebra

lemma forall₂_homogeneous_map_degrees
    {ι σ : Type*} (d : ι → ℕ)
    {order : List ι} {gs : List (MvPolynomial σ K)}
    (hhom : List.Forall₂ (fun i g ↦ g.IsHomogeneous (d i)) order gs) :
    List.Forall₂ (fun g e ↦ g.IsHomogeneous e) gs (order.map d) := by
  induction hhom with
  | nil => exact .nil
  | cons h _ ih => exact .cons h ih

lemma linearSlicePolynomialIdeal_eq_dehomogenizedSliceIdeal {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K)
    (a : Fin (n + 1) → K) :
    linearSlicePolynomialIdeal f a =
      dehomogenizedSliceIdeal (homogeneousEquationIdeal f) (linearForm a) := by
  rw [linearSlicePolynomialIdeal, dehomogenizedSliceIdeal,
    homogeneousEquationIdeal, Ideal.span_union]

lemma exists_avoiding_nonzero_linearForm [IsAlgClosed K] {n : ℕ}
    (S : Set (ProjSpace K n)) (hS : S.Finite) :
    ∃ a : Fin (n + 1) → K,
      (∀ p ∈ S, eval (Projectivization.rep p) (linearForm a) ≠ 0) ∧
        linearForm a ≠ 0 := by
  let v : Fin (n + 1) → K := fun _ ↦ 1
  have hv : v ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp [v] at h0
  let p0 : ProjSpace K n := Projectivization.mk K v hv
  obtain ⟨a, ha⟩ :=
    exists_linearForm_nonzero_on_finite (S ∪ {p0})
      (hS.union (Set.finite_singleton p0))
  refine ⟨a, fun p hp ↦ ha p (Set.mem_union_left _ hp), ?_⟩
  intro hzero
  have hp0 := ha p0 (Set.mem_union_right S (Set.mem_singleton p0))
  rw [hzero] at hp0
  simp at hp0

set_option maxHeartbeats 1600000 in
lemma finrank_linearSlicePolynomialQuotient_eq_degree_prod
    [IsAlgClosed K] {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K)
    (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (hdpos : ∀ k, 0 < d k)
    (a : Fin (n + 1) → K)
    (hne : ∀ p ∈ ⋂ k, vanishingSet (f k),
      eval (Projectivization.rep p) (linearForm a) ≠ 0)
    (hLne : linearForm a ≠ 0) :
    Module.finrank K
        (MvPolynomial (Fin (n + 1)) K ⧸ linearSlicePolynomialIdeal f a) =
      ∏ k, d k := by
  let R := MvPolynomial (Fin (n + 1)) K
  let I := homogeneousEquationIdeal f
  let L := linearForm a
  obtain ⟨order, gs, hord, huniv, hhom, hideal, hgsreg⟩ :=
    exists_homogeneous_regular_equation_generators_mod_linear
      f d hd hdpos a hne hLne
  have horderlen : order.length = n := by
    calc
      order.length = order.toFinset.card :=
        (List.toFinset_card_of_nodup hord).symm
      _ = (Finset.univ : Finset (Fin n)).card := by rw [huniv]
      _ = n := by simp
  have hglen : gs.length = n := hhom.length_eq.symm.trans horderlen
  have hfullLen : (L :: gs).length = n + 1 := by simp [hglen]
  let es : List ℕ := 1 :: order.map d
  have hhomTail :
      List.Forall₂ (fun g e ↦ g.IsHomogeneous e) gs (order.map d) :=
    forall₂_homogeneous_map_degrees d hhom
  have hhomFull :
      List.Forall₂ (fun g e ↦ g.IsHomogeneous e) (L :: gs) es := by
    exact .cons (linearForm_isHomogeneous a) hhomTail
  have hLreg : IsSMulRegular R L := by
    apply IsSMulRegular.of_right_eq_zero_of_smul
    intro p hp
    change L * p = 0 at hp
    exact (mul_eq_zero.mp hp).resolve_left hLne
  have hfull : IsRegular R (L :: gs) :=
    IsRegular.cons hLreg hgsreg
  have hIhom : I.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) K) := by
    apply Ideal.homogeneous_span
    rintro g ⟨k, rfl⟩
    exact ⟨d k, hd k⟩
  have hLmod : RegularModIdeal I L := by
    change RegularModIdeal (homogeneousEquationIdeal f) (linearForm a)
    rw [← hideal]
    exact regularModIdeal_head_of_regular_cons L gs hfull
  have hfullIdeal :
      Ideal.ofList (L :: gs) = I ⊔ Ideal.span {L} := by
    rw [Ideal.ofList_cons, hideal, sup_comm]
  have hespos : ∀ e ∈ es, 0 < e := by
    intro e he
    simp only [es, List.mem_cons, List.mem_map] at he
    rcases he with rfl | ⟨k, hk, rfl⟩
    · exact Nat.zero_lt_one
    · exact hdpos k
  let N := (es.map fun e ↦ e - 1).sum
  have hzero : ∀ m, N < m →
      Subsingleton
        (HomogeneousQuotientPiece (I ⊔ Ideal.span {L}) m) := by
    intro m hm
    rw [← hfullIdeal]
    exact homogeneousQuotientPiece_subsingleton_of_lt
      (n + 1) (L :: gs) es hhomFull hfull hfullLen hespos hm
  let e :=
    stablePieceDehomogenizedEquiv I L (linearForm_isHomogeneous a)
      hIhom hLmod N hzero
  have hstable :
      Module.finrank K
          (MvPolynomial (Fin (n + 1)) K ⧸ dehomogenizedSliceIdeal I L) =
        Module.finrank K (HomogeneousQuotientPiece I N) :=
    e.finrank_eq.symm
  have hsum :
      Module.finrank K (HomogeneousQuotientPiece I N) =
        ∑ j ∈ Finset.range (N + 1),
          Module.finrank K
            (HomogeneousQuotientPiece (I ⊔ Ideal.span {L}) j) :=
    finrank_homogeneousQuotientPiece_eq_sum_sup_span
      I L (linearForm_isHomogeneous a) hIhom hLmod N
  have hcount :
      (∑ j ∈ Finset.range (N + 1),
          Module.finrank K
            (HomogeneousQuotientPiece (I ⊔ Ideal.span {L}) j)) =
        es.prod := by
    rw [← hfullIdeal]
    exact sum_finrank_homogeneousQuotientPiece_eq_prod
      (n + 1) (L :: gs) es hhomFull hfull hfullLen hespos
  have hprodOrder : (order.map d).prod = ∏ k, d k := by
    calc
      (order.map d).prod = order.toFinset.prod d :=
        (List.prod_toFinset d hord).symm
      _ = (Finset.univ : Finset (Fin n)).prod d := by rw [huniv]
      _ = ∏ k, d k := rfl
  rw [linearSlicePolynomialIdeal_eq_dehomogenizedSliceIdeal]
  change Module.finrank K
      (R ⧸ dehomogenizedSliceIdeal I L) = ∏ k, d k
  calc
    _ = Module.finrank K (HomogeneousQuotientPiece I N) := hstable
    _ = ∑ j ∈ Finset.range (N + 1),
        Module.finrank K
          (HomogeneousQuotientPiece (I ⊔ Ideal.span {L}) j) := hsum
    _ = es.prod := hcount
    _ = (order.map d).prod := by simp [es]
    _ = ∏ k, d k := hprodOrder

set_option maxHeartbeats 1600000 in
lemma length_linearSlicePolynomialQuotient_eq_degree_prod
    [IsAlgClosed K] {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K)
    (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (hdpos : ∀ k, 0 < d k)
    (a : Fin (n + 1) → K)
    (hfin : (⋂ k, vanishingSet (f k)).Finite)
    (hne : ∀ p ∈ ⋂ k, vanishingSet (f k),
      eval (Projectivization.rep p) (linearForm a) ≠ 0)
    (hLne : linearForm a ≠ 0) :
    Module.length K
        (MvPolynomial (Fin (n + 1)) K ⧸ linearSlicePolynomialIdeal f a) =
      (∏ k, d k : ℕ∞) := by
  letI : Module.Finite K
      (MvPolynomial (Fin (n + 1)) K ⧸ linearSlicePolynomialIdeal f a) :=
    linearSlicePolynomialQuotient_module_finite f d hd a hfin hne
  rw [Module.length_eq_finrank]
  exact_mod_cast
    finrank_linearSlicePolynomialQuotient_eq_degree_prod
      f d hd hdpos a hne hLne

end Submission.Helpers
