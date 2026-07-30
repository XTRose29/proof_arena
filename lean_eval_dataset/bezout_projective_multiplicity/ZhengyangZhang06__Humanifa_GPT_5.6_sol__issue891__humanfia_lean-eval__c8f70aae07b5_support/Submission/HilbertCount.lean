import Submission.AffineBridge
import Mathlib.Algebra.Polynomial.Eval.Degree

open MvPolynomial RingTheory.Sequence
open scoped Pointwise

variable {K : Type*} [Field K]

namespace Submission.Helpers

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def hilbertGeom (d : ℕ) : PowerSeries ℤ :=
  ∑ i ∈ Finset.range d, PowerSeries.X ^ i

noncomputable def hilbertGeomPolynomial (d : ℕ) : Polynomial ℤ :=
  ∑ i ∈ Finset.range d, Polynomial.X ^ i

noncomputable def hilbertNumeratorPolynomial (es : List ℕ) : Polynomial ℤ :=
  (es.map hilbertGeomPolynomial).prod

lemma hilbertFactor_eq_mul_hilbertGeom (d : ℕ) :
    hilbertFactor d = (1 - PowerSeries.X) * hilbertGeom d := by
  simpa [hilbertFactor, hilbertGeom] using
    (mul_neg_geom_sum (PowerSeries.X : PowerSeries ℤ) d).symm

lemma prod_hilbertFactor_eq (es : List ℕ) :
    (es.map hilbertFactor).prod =
      (1 - PowerSeries.X) ^ es.length * (es.map hilbertGeom).prod := by
  induction es with
  | nil => simp
  | cons e es ih =>
      rw [List.map_cons, List.prod_cons, hilbertFactor_eq_mul_hilbertGeom, ih]
      simp only [List.length_cons, pow_succ]
      simp only [List.map_cons, List.prod_cons]
      ring_nf

lemma homogeneousQuotientHilbertSeries_of_regular_fin
    (m : ℕ) (rs : List (MvPolynomial (Fin m) K)) (es : List ℕ)
    (hhom : List.Forall₂ (fun g e ↦ g.IsHomogeneous e) rs es)
    (hreg : IsRegular (MvPolynomial (Fin m) K) rs)
    (hlen : rs.length = m) :
    homogeneousQuotientHilbertSeries (Ideal.ofList rs) =
      (es.map hilbertGeom).prod := by
  have heslen : es.length = m := hhom.length_eq.symm.trans hlen
  rw [homogeneousQuotientHilbertSeries_of_regular rs es hhom hreg,
    prod_hilbertFactor_eq]
  calc
    (1 - PowerSeries.X) ^ es.length * (es.map hilbertGeom).prod *
          homogeneousQuotientHilbertSeries
            (⊥ : Ideal (MvPolynomial (Fin m) K)) =
        (es.map hilbertGeom).prod *
          ((1 - PowerSeries.X) ^ m *
            homogeneousQuotientHilbertSeries
              (⊥ : Ideal (MvPolynomial (Fin m) K))) := by
          rw [heslen]
          ring
    _ = (es.map hilbertGeom).prod := by
      rw [one_sub_X_pow_card_mul_hilbertSeries_bot]
      simp

lemma coe_hilbertGeomPolynomial (d : ℕ) :
    (hilbertGeomPolynomial d : PowerSeries ℤ) = hilbertGeom d := by
  change Polynomial.coeToPowerSeries.ringHom
      (∑ i ∈ Finset.range d, Polynomial.X ^ i) =
    ∑ i ∈ Finset.range d, PowerSeries.X ^ i
  rw [map_sum]
  simp

lemma coe_hilbertNumeratorPolynomial (es : List ℕ) :
    (hilbertNumeratorPolynomial es : PowerSeries ℤ) =
      (es.map hilbertGeom).prod := by
  induction es with
  | nil => simp [hilbertNumeratorPolynomial]
  | cons e es ih =>
      simp only [hilbertNumeratorPolynomial, List.map_cons, List.prod_cons,
        Polynomial.coe_mul, coe_hilbertGeomPolynomial]
      change hilbertGeom e * (hilbertNumeratorPolynomial es : PowerSeries ℤ) =
        hilbertGeom e * (es.map hilbertGeom).prod
      rw [ih]

lemma natDegree_hilbertGeomPolynomial_le {d : ℕ} (hd : 0 < d) :
    (hilbertGeomPolynomial d).natDegree ≤ d - 1 := by
  rw [hilbertGeomPolynomial]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  simp only [Finset.mem_range] at hi
  simp
  omega

lemma natDegree_hilbertNumeratorPolynomial_le
    (es : List ℕ) (hpos : ∀ e ∈ es, 0 < e) :
    (hilbertNumeratorPolynomial es).natDegree ≤
      (es.map fun e ↦ e - 1).sum := by
  induction es with
  | nil => simp [hilbertNumeratorPolynomial]
  | cons e es ih =>
      have he : 0 < e := hpos e (by simp)
      have hes : ∀ x ∈ es, 0 < x := by
        intro x hx
        exact hpos x (by simp [hx])
      rw [hilbertNumeratorPolynomial]
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      exact Polynomial.natDegree_mul_le.trans
        (Nat.add_le_add (natDegree_hilbertGeomPolynomial_le he) (ih hes))

lemma eval_one_hilbertGeomPolynomial (d : ℕ) :
    (hilbertGeomPolynomial d).eval 1 = d := by
  simp [hilbertGeomPolynomial]

lemma eval_one_hilbertNumeratorPolynomial (es : List ℕ) :
    (hilbertNumeratorPolynomial es).eval 1 = (es.prod : ℤ) := by
  induction es with
  | nil => simp [hilbertNumeratorPolynomial]
  | cons e es ih =>
      change (hilbertGeomPolynomial e * hilbertNumeratorPolynomial es).eval 1 =
        ((e * es.prod : ℕ) : ℤ)
      rw [Polynomial.eval_mul, eval_one_hilbertGeomPolynomial, ih]
      norm_num

lemma coeff_hilbertNumeratorPolynomial_eq_finrank_of_regular
    (m : ℕ) (rs : List (MvPolynomial (Fin m) K)) (es : List ℕ)
    (hhom : List.Forall₂ (fun g e ↦ g.IsHomogeneous e) rs es)
    (hreg : IsRegular (MvPolynomial (Fin m) K) rs)
    (hlen : rs.length = m) (j : ℕ) :
    (hilbertNumeratorPolynomial es).coeff j =
      Module.finrank K (HomogeneousQuotientPiece (Ideal.ofList rs) j) := by
  have hseries :=
    homogeneousQuotientHilbertSeries_of_regular_fin m rs es hhom hreg hlen
  have hcoeff := congrArg (PowerSeries.coeff (R := ℤ) j) hseries
  rw [← coe_hilbertNumeratorPolynomial] at hcoeff
  simpa [homogeneousQuotientHilbertSeries] using hcoeff.symm

lemma finrank_homogeneousQuotientPiece_eq_zero_of_lt
    (m : ℕ) (rs : List (MvPolynomial (Fin m) K)) (es : List ℕ)
    (hhom : List.Forall₂ (fun g e ↦ g.IsHomogeneous e) rs es)
    (hreg : IsRegular (MvPolynomial (Fin m) K) rs)
    (hlen : rs.length = m)
    (hpos : ∀ e ∈ es, 0 < e)
    {j : ℕ} (hj : (es.map fun e ↦ e - 1).sum < j) :
    Module.finrank K (HomogeneousQuotientPiece (Ideal.ofList rs) j) = 0 := by
  rw [← Int.ofNat_inj, ← coeff_hilbertNumeratorPolynomial_eq_finrank_of_regular
    m rs es hhom hreg hlen j]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt
    ((natDegree_hilbertNumeratorPolynomial_le es hpos).trans_lt hj)

lemma homogeneousQuotientPiece_subsingleton_of_lt
    (m : ℕ) (rs : List (MvPolynomial (Fin m) K)) (es : List ℕ)
    (hhom : List.Forall₂ (fun g e ↦ g.IsHomogeneous e) rs es)
    (hreg : IsRegular (MvPolynomial (Fin m) K) rs)
    (hlen : rs.length = m)
    (hpos : ∀ e ∈ es, 0 < e)
    {j : ℕ} (hj : (es.map fun e ↦ e - 1).sum < j) :
    Subsingleton (HomogeneousQuotientPiece (Ideal.ofList rs) j) :=
  Module.finrank_zero_iff.mp
    (finrank_homogeneousQuotientPiece_eq_zero_of_lt
      m rs es hhom hreg hlen hpos hj)

set_option maxHeartbeats 800000 in
lemma sum_finrank_homogeneousQuotientPiece_eq_prod
    (m : ℕ) (rs : List (MvPolynomial (Fin m) K)) (es : List ℕ)
    (hhom : List.Forall₂ (fun g e ↦ g.IsHomogeneous e) rs es)
    (hreg : IsRegular (MvPolynomial (Fin m) K) rs)
    (hlen : rs.length = m)
    (hpos : ∀ e ∈ es, 0 < e) :
    (∑ j ∈ Finset.range ((es.map fun e ↦ e - 1).sum + 1),
        Module.finrank K (HomogeneousQuotientPiece (Ideal.ofList rs) j)) =
      es.prod := by
  let N := (es.map fun e ↦ e - 1).sum
  have hdeg : (hilbertNumeratorPolynomial es).natDegree < N + 1 :=
    (natDegree_hilbertNumeratorPolynomial_le es hpos).trans_lt
      (Nat.lt_succ_self N)
  have heval :=
    Polynomial.eval_eq_sum_range' hdeg (1 : ℤ)
  rw [eval_one_hilbertNumeratorPolynomial] at heval
  have hsumInt :
      (∑ x ∈ Finset.range (N + 1),
          (Module.finrank K
            (HomogeneousQuotientPiece (Ideal.ofList rs) x) : ℤ)) =
        (es.prod : ℤ) := by
    calc
      _ = ∑ x ∈ Finset.range (N + 1),
            (hilbertNumeratorPolynomial es).coeff x := by
              apply Finset.sum_congr rfl
              intro x hx
              exact (coeff_hilbertNumeratorPolynomial_eq_finrank_of_regular
                m rs es hhom hreg hlen x).symm
      _ = (es.prod : ℤ) := by
        simpa [one_pow] using heval.symm
  exact_mod_cast hsumInt

set_option maxHeartbeats 800000 in
lemma finrank_homogeneousQuotientPiece_eq_sum_sup_span
    {σ : Type*} [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    (L : MvPolynomial σ K) (hL : L.IsHomogeneous 1)
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    (hreg : RegularModIdeal I L) (N : ℕ) :
    Module.finrank K (HomogeneousQuotientPiece I N) =
      ∑ j ∈ Finset.range (N + 1),
        Module.finrank K
          (HomogeneousQuotientPiece (I ⊔ Ideal.span {L}) j) := by
  induction N with
  | zero =>
      have h :=
        finrank_sup_span_eq_of_not_le I L 1 0 hI hL (by omega)
      simpa using h.symm
  | succ N ih =>
      have h :=
        finrank_shift_add_finrank_sup_span I L 1 (N + 1)
          hI hL (by omega) hreg
      rw [Finset.sum_range_succ, ← ih]
      exact h.symm

end Submission.Helpers
