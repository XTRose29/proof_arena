import ChallengeDeps
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Basic

open LeanEval.RepresentationTheory
open scoped TensorProduct fwdDiff

namespace Submission.DiagonalAction

open Function

variable {R E V : Type*} [CommRing R] [AddCommGroup E] [Module R E]
  [AddCommGroup V] [Module R V]

private theorem fwdDiff_iter_smul_const (g : R → R) (v : E) (n : ℕ) :
    Nat.iterate (fwdDiff (1 : R)) n (fun t ↦ g t • v) =
      fun t ↦ Nat.iterate (fwdDiff (1 : R)) n g t • v := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      exact fwdDiff_smul_const 1 _ _

/-- The top forward difference of a homogeneous diagonal of a multilinear map. -/
theorem fwdDiff_iter_diagonal
    (k : ℕ) (L : MultilinearMap R (fun _ : Fin k ↦ V) E) (x y : V) :
    Nat.iterate (fwdDiff (1 : R)) k (fun t ↦ L (fun _ ↦ x + t • y)) 0 =
      (k.factorial : R) • L (fun _ ↦ y) := by
  classical
  have hexpand :
      (fun t : R ↦ L (fun _ : Fin k ↦ x + t • y)) =
        ∑ s : Finset (Fin k), fun t ↦
          t ^ s.card • L (s.piecewise (fun _ ↦ y) (fun _ ↦ x)) := by
    funext t
    rw [show (fun _ : Fin k ↦ x + t • y) =
        (fun _ ↦ t • y) + (fun _ ↦ x) by ext; simp [add_comm],
      L.map_add_univ]
    rw [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro s hs
    rw [← Finset.prod_const]
    rw [← L.map_piecewise_smul (fun _ ↦ t)
      (s.piecewise (fun _ ↦ y) (fun _ ↦ x)) s]
    apply congrArg L
    ext i
    by_cases hi : i ∈ s <;> simp [hi]
  rw [hexpand, fwdDiff_iter_finsetSum]
  simp_rw [fwdDiff_iter_smul_const]
  rw [Finset.sum_apply, Finset.sum_eq_single Finset.univ]
  · simp only [Finset.card_univ, Fintype.card_fin, fwdDiff_iter_eq_factorial,
      Pi.natCast_apply, Finset.piecewise_univ]
  · intro s hs hsu
    have hcard' : s.card < Fintype.card (Fin k) :=
      (Finset.card_lt_iff_ne_univ s).mpr hsu
    have hcard : s.card < k := by
      simpa only [Fintype.card_fin] using hcard'
    rw [fwdDiff_iter_pow_eq_zero_of_lt hcard]
    simp
  · simp

/-- Apply the same endomorphism in every tensor factor. -/
noncomputable def diagonalAction (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (k : ℕ) (f : Module.End R M) : Module.End R (⨂[R]^k M) :=
  PiTensorProduct.map (fun _ : Fin k ↦ f)

theorem diagonalAction_eq_piTensorHomMap_tprod
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (k : ℕ) (f : Module.End R M) :
    diagonalAction R M k f =
      PiTensorProduct.piTensorHomMap
        (PiTensorProduct.tprod R (fun _ : Fin k ↦ f)) := by
  exact (PiTensorProduct.piTensorHomMap_tprod_eq_map _).symm

theorem diagonalAction_mul
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (k : ℕ) (f g : Module.End R M) :
    diagonalAction R M k (f * g) =
      diagonalAction R M k f * diagonalAction R M k g := by
  ext x
  simp [diagonalAction]

theorem diagonalAction_mem_adjoin_of_isUnit
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (k : ℕ) (f : Module.End R M) (hf : IsUnit f) :
    diagonalAction R M k f ∈
      Algebra.adjoin R (Set.range (glAction R M k)) := by
  obtain ⟨g, rfl⟩ := hf
  apply Algebra.subset_adjoin
  exact ⟨g, rfl⟩

theorem diagonalAction_mem_adjoin_of_isNilpotent
    (R M : Type*) [Field R] [AddCommGroup M] [Module R M]
    (k : ℕ) [Invertible (k.factorial : R)]
    (f : Module.End R M) (hf : IsNilpotent f) :
    diagonalAction R M k f ∈
      Algebra.adjoin R (Set.range (glAction R M k)) := by
  let C := Algebra.adjoin R (Set.range (glAction R M k))
  let P : R → Module.End R (⨂[R]^k M) :=
    fun t ↦ diagonalAction R M k (1 + t • f)
  have hP (n : ℕ) : P (n : R) ∈ C := by
    apply diagonalAction_mem_adjoin_of_isUnit
    exact (hf.smul (n : R)).isUnit_one_add
  have hmap (u : Fin k → Module.End R M) :
      PiTensorProduct.mapMultilinear R
          (fun _ : Fin k ↦ M) (fun _ : Fin k ↦ M) u =
        PiTensorProduct.map u := by
    rfl
  have hdiff :
      Nat.iterate (fwdDiff (1 : R)) k P 0 =
        (k.factorial : R) • diagonalAction R M k f := by
    simpa only [P, diagonalAction, hmap] using
      fwdDiff_iter_diagonal k
        (PiTensorProduct.mapMultilinear R
          (fun _ : Fin k ↦ M) (fun _ : Fin k ↦ M))
        (1 : Module.End R M) f
  have hsum :
      Nat.iterate (fwdDiff (1 : R)) k P 0 ∈ C := by
    rw [fwdDiff_iter_eq_sum_shift]
    apply C.toSubmodule.sum_mem
    intro n hn
    rw [← Int.cast_smul_eq_zsmul R]
    exact C.toSubmodule.smul_mem _ (by simpa using hP n)
  rw [hdiff] at hsum
  exact C.toSubmodule.smul_mem_iff_of_isUnit
    (isUnit_of_invertible (k.factorial : R)) |>.mp hsum

end Submission.DiagonalAction
