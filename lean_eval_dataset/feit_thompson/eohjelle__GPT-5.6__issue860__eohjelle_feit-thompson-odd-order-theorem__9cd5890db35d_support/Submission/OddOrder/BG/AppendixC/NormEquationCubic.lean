import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Tactic
import Submission.OddOrder.BG.AppendixC.NormEquationBound

/-!
# Bender--Glauberman Appendix C: the cubic branch of Lemma C.2

This file ports the `q = 3` branch of Coq `BGappendixC.v`, Lemma C.2.
The source considers the family

`X * (X - 2) * (X - c) + (X - 1)`.

Over a finite field, one member of this family has no root: otherwise a
choice of one root for every `c` would define an injective self-map of the
field, hence a surjective one, although zero cannot occur among the chosen
roots.  Such a cubic is irreducible.  It acquires a root in every finite
extension of degree three, and evaluation at zero and two gives the two
norm-one equations used in Appendix C.

The group-character argument used for the complementary branch `4 < q` is
deliberately not included here.
-/

namespace Submission.OddOrder.BG.AppendixC

noncomputable section

open scoped Algebra IntermediateField Polynomial

universe u v

open Polynomial

/-! ### The cubic family from the source proof -/

/-- The polynomial called `f c` in the `q = 3` branch of Coq Lemma C.2. -/
def normEquationCubic
    {K : Type u} [Field K] (c : K) : K[X] :=
  X * (X - C 2) * (X - C c) + (X - C 1)

@[simp]
theorem normEquationCubic_eval
    {K : Type u} [Field K] (c x : K) :
    (normEquationCubic c).eval x =
      x * (x - 2) * (x - c) + (x - 1) := by
  simp [normEquationCubic]

@[simp]
theorem normEquationCubic_eval_zero
    {K : Type u} [Field K] (c : K) :
    (normEquationCubic c).eval 0 = -1 := by
  simp [normEquationCubic]

@[simp]
theorem normEquationCubic_eval_two
    {K : Type u} [Field K] (c : K) :
    (normEquationCubic c).eval 2 = 1 := by
  rw [normEquationCubic_eval]
  ring

theorem normEquationCubic_monic
    {K : Type u} [Field K] (c : K) :
    (normEquationCubic c).Monic := by
  let L : K[X] := X * (X - C 2) * (X - C c)
  have hX : (X : K[X]).Monic := monic_X
  have h2 : (X - C (2 : K)).Monic := monic_X_sub_C 2
  have hc : (X - C c).Monic := monic_X_sub_C c
  have hL : L.Monic := (hX.mul h2).mul hc
  have hLdegree : L.natDegree = 3 := by
    rw [(hX.mul h2).natDegree_mul hc, hX.natDegree_mul h2]
    simp
  change (L + (X - C (1 : K))).Monic
  apply hL.add_of_left
  apply degree_lt_degree
  rw [natDegree_X_sub_C, hLdegree]
  norm_num

@[simp]
theorem normEquationCubic_natDegree
    {K : Type u} [Field K] (c : K) :
    (normEquationCubic c).natDegree = 3 := by
  let L : K[X] := X * (X - C 2) * (X - C c)
  have hX : (X : K[X]).Monic := monic_X
  have h2 : (X - C (2 : K)).Monic := monic_X_sub_C 2
  have hc : (X - C c).Monic := monic_X_sub_C c
  have hLdegree : L.natDegree = 3 := by
    rw [(hX.mul h2).natDegree_mul hc, hX.natDegree_mul h2]
    simp
  change (L + (X - C (1 : K))).natDegree = 3
  rw [natDegree_add_eq_left_of_natDegree_lt]
  · exact hLdegree
  · rw [natDegree_X_sub_C, hLdegree]
    norm_num

/-- The finite pigeonhole argument in the `q = 3` part of Coq Lemma C.2:
some member of the cubic family has no root in the base field. -/
theorem exists_normEquationCubic_without_root
    (K : Type u) [Field K] [Finite K] :
    ∃ c : K, ∀ x : K, ¬(normEquationCubic c).IsRoot x := by
  classical
  by_contra h
  push Not at h
  choose r hr using h

  have hr_zero (c : K) : r c ≠ 0 := by
    intro hrc
    have hbad : (-1 : K) = 0 := by
      simpa [Polynomial.IsRoot, hrc] using hr c
    exact (neg_ne_zero.mpr one_ne_zero) hbad

  have hr_two (c : K) : r c ≠ 2 := by
    intro hrc
    have hbad := hr c
    rw [Polynomial.IsRoot, hrc, normEquationCubic_eval_two] at hbad
    exact one_ne_zero hbad

  have hr_injective : Function.Injective r := by
    intro a b hab
    have ha := hr a
    have hb := hr b
    rw [Polynomial.IsRoot, normEquationCubic_eval] at ha hb
    rw [hab] at ha
    have hprod :
        (r b * (r b - 2)) * (a - b) = 0 := by
      linear_combination hb - ha
    have hcoefficient : r b * (r b - 2) ≠ 0 :=
      mul_ne_zero (hr_zero b) (sub_ne_zero.mpr (hr_two b))
    exact sub_eq_zero.mp
      ((mul_eq_zero.mp hprod).resolve_left hcoefficient)

  obtain ⟨c, hc⟩ := Finite.surjective_of_injective hr_injective 0
  exact hr_zero c hc

/-- A source-facing bundle: one cubic in the family is monic, irreducible,
of degree three, and has no root in the base field. -/
theorem exists_irreducible_normEquationCubic
    (K : Type u) [Field K] [Finite K] :
    ∃ c : K,
      Irreducible (normEquationCubic c) ∧
      (normEquationCubic c).Monic ∧
      (normEquationCubic c).natDegree = 3 ∧
      ∀ x : K, ¬(normEquationCubic c).IsRoot x := by
  obtain ⟨c, hroot⟩ := exists_normEquationCubic_without_root K
  refine ⟨c, ?_, normEquationCubic_monic c,
    normEquationCubic_natDegree c, hroot⟩
  apply irreducible_of_degree_le_three_of_not_isRoot
  · simp
  · exact hroot

/-! ### Roots in degree-three finite extensions -/

/-- An irreducible polynomial whose degree is the degree of a finite-field
extension has a root in that extension.  This is the finite-field embedding
step that the Coq proof obtains by constructing an abstract root field and
comparing its cardinality with the given field. -/
theorem exists_root_of_irreducible_of_natDegree_eq_finrank
    {K : Type u} {F : Type v}
    [Field K] [Field F] [Algebra K F] [Finite F]
    {f : K[X]} (hirr : Irreducible f)
    (hdegree : f.natDegree = Module.finrank K F) :
    ∃ a : F, (f.map (algebraMap K F)).IsRoot a := by
  letI : Fact (Irreducible f) := ⟨hirr⟩
  have hrootFieldDegree :
      Module.finrank K (AdjoinRoot f) = f.natDegree :=
    (AdjoinRoot.powerBasis hirr.ne_zero).finrank
  have hdiv :
      Module.finrank K (AdjoinRoot f) ∣ Module.finrank K F := by
    rw [hrootFieldDegree, hdegree]
  obtain ⟨phi⟩ :=
    FiniteField.nonempty_algHom_of_finrank_dvd
      (F := K) (K := AdjoinRoot f) (L := F) hdiv
  refine ⟨phi (AdjoinRoot.root f), ?_⟩
  have hroot :
      ((f.map (AdjoinRoot.of f)).map phi.toRingHom).IsRoot
        (phi (AdjoinRoot.root f)) :=
    (AdjoinRoot.isRoot_root f).map
  have hcomp :
      phi.toRingHom.comp (AdjoinRoot.of f) = algebraMap K F := by
    ext x
    exact phi.commutes x
  rwa [Polynomial.map_map, hcomp] at hroot

/-! ### Norms of a full-degree root -/

/-- If `a` is a root of a monic irreducible polynomial whose degree is the
full extension degree, then the norm of `r - a` is the evaluation of the
polynomial at `r`.

This packages the factorization-over-the-Galois-group calculation used
twice at the end of the Coq cubic proof. -/
theorem norm_algebraMap_sub_root_eq_eval
    {K : Type u} {F : Type v}
    [Field K] [Field F] [Algebra K F] [FiniteDimensional K F]
    {f : K[X]} (hmonic : f.Monic) (hirr : Irreducible f)
    {a : F} (hroot : (f.map (algebraMap K F)).IsRoot a)
    (hdegree : f.natDegree = Module.finrank K F)
    (r : K) :
    Algebra.norm K (algebraMap K F r - a) = f.eval r := by
  have haeval : Polynomial.aeval a f = 0 := by
    simpa [Polynomial.IsRoot] using hroot
  have hfmin : f = minpoly K a :=
    minpoly.eq_of_irreducible_of_monic hirr haeval hmonic
  have haintegral : IsIntegral K a := ⟨f, hmonic, haeval⟩
  have hadjoinDegree :
      Module.finrank K (K⟮a⟯) = f.natDegree := by
    rw [IntermediateField.adjoin.finrank haintegral, ← hfmin]
  have hfactorDegree : Module.finrank K⟮a⟯ F = 1 := by
    have htower := Module.finrank_mul_finrank K K⟮a⟯ F
    rw [hadjoinDegree, ← hdegree] at htower
    have hpositive : 0 < f.natDegree :=
      natDegree_pos_iff_degree_pos.mpr
        (degree_pos_of_irreducible hirr)
    apply mul_left_cancel₀ hpositive.ne'
    simpa using htower
  have hadjoinTop : K⟮a⟯ = ⊤ :=
    IntermediateField.finrank_eq_one_iff_eq_top.mp hfactorDegree
  have halgebraAdjoinTop : K[a] = ⊤ :=
    Algebra.adjoin_eq_top_of_primitive_element
      haintegral.isAlgebraic hadjoinTop
  let pb : PowerBasis K F :=
    PowerBasis.ofAdjoinEqTop haintegral halgebraAdjoinTop
  have hpbgen : pb.gen = a := by
    simp [pb]
  have hmatrix :
      Algebra.leftMulMatrix pb.basis
          (algebraMap K F r - pb.gen) =
        Matrix.scalar (Fin pb.dim) r -
          Algebra.leftMulMatrix pb.basis pb.gen := by
    rw [map_sub, (Algebra.leftMulMatrix pb.basis).commutes]
    rfl
  rw [← hpbgen]
  calc
    Algebra.norm K (algebraMap K F r - pb.gen) =
        (Algebra.leftMulMatrix pb.basis
          (algebraMap K F r - pb.gen)).det :=
      Algebra.norm_eq_matrix_det pb.basis _
    _ = (Matrix.scalar (Fin pb.dim) r -
          Algebra.leftMulMatrix pb.basis pb.gen).det := by
      rw [hmatrix]
    _ = (Algebra.leftMulMatrix pb.basis pb.gen).charpoly.eval r :=
      (Matrix.eval_charpoly _ _).symm
    _ = (minpoly K pb.gen).eval r := by
      rw [charpoly_leftMulMatrix pb]
    _ = f.eval r := by
      rw [hpbgen, ← hfmin]

/-! ### The norm-equation element -/

/-- The generic mathematical content of the `q = 3` branch of Coq Lemma
C.2: a finite extension of finite fields of degree three contains a
nontrivial solution of the two norm-one equations. -/
theorem exists_nontrivial_mem_normEquationSet_of_finrank_three
    (K : Type u) (F : Type v)
    [Field K] [Finite K] [Field F] [Finite F]
    [Algebra K F] [FiniteDimensional K F]
    (hfinrank : Module.finrank K F = 3) :
    ∃ a : F, a ≠ 1 ∧ a ∈ normEquationSet K F := by
  obtain ⟨c, hirr, hmonic, hdegree, hnotRoot⟩ :=
    exists_irreducible_normEquationCubic K
  obtain ⟨a, haRoot⟩ :=
    exists_root_of_irreducible_of_natDegree_eq_finrank
      hirr (by simpa [hdegree] using hfinrank.symm)

  have ha_not_base (d : K) : a ≠ algebraMap K F d := by
    intro had
    apply hnotRoot d
    apply (Polynomial.isRoot_map_iff
      (algebraMap K F).injective).mp
    simpa [had] using haRoot

  have ha_one : a ≠ 1 := by
    intro ha
    exact ha_not_base 1 (by simpa using ha)

  have hnormNeg : Algebra.norm K (-a) = -1 := by
    have h := norm_algebraMap_sub_root_eq_eval
      hmonic hirr haRoot
      (by simpa [hdegree] using hfinrank.symm) (0 : K)
    simpa using h

  have hnorm_neg_eq :
      Algebra.norm K (-a) = -Algebra.norm K a := by
    calc
      Algebra.norm K (-a) =
          Algebra.norm K (algebraMap K F (-1) * a) := by
        congr 1
        simp
      _ = (-1 : K) ^ Module.finrank K F * Algebra.norm K a := by
        rw [map_mul, Algebra.norm_algebraMap]
      _ = -Algebra.norm K a := by
        rw [hfinrank]
        ring

  have hnormA : Algebra.norm K a = 1 := by
    rw [hnorm_neg_eq] at hnormNeg
    exact neg_injective hnormNeg

  have hnormTwoSub : Algebra.norm K (2 - a) = 1 := by
    have h := norm_algebraMap_sub_root_eq_eval
      hmonic hirr haRoot
      (by simpa [hdegree] using hfinrank.symm) (2 : K)
    have hmapTwo : algebraMap K F (2 : K) = (2 : F) :=
      map_ofNat (algebraMap K F) 2
    rw [hmapTwo] at h
    exact h.trans (normEquationCubic_eval_two c)

  exact ⟨a, ha_one, hnormA, hnormTwoSub⟩

/-- The source-facing `q = 3` formulation over the prime field.  The oddness
assumption is retained because it is one of the arithmetic facts available
at this branch in `BGappendixC.v`; the cubic argument itself is valid in
every characteristic. -/
theorem exists_nontrivial_mem_normEquationSet_of_q_eq_three
    {p q : ℕ} [Fact p.Prime]
    (F : Type v) [Field F] [Finite F]
    [Algebra (ZMod p) F] [FiniteDimensional (ZMod p) F]
    (_hpodd : Odd p) (hqthree : q = 3)
    (hfinrank : Module.finrank (ZMod p) F = q) :
    ∃ a : F, a ≠ 1 ∧ a ∈ normEquationSet (ZMod p) F := by
  apply exists_nontrivial_mem_normEquationSet_of_finrank_three (ZMod p) F
  simpa [hqthree] using hfinrank

/-- The literal small-odd-degree branch selection in the source proof:
`2 < q`, odd `q`, and `q ≤ 4` force `q = 3`. -/
theorem exists_nontrivial_mem_normEquationSet_of_small_odd_degree
    {p q : ℕ} [Fact p.Prime]
    (F : Type v) [Field F] [Finite F]
    [Algebra (ZMod p) F] [FiniteDimensional (ZMod p) F]
    (hpodd : Odd p) (hqodd : Odd q)
    (htwo : 2 < q) (hfour : q ≤ 4)
    (hfinrank : Module.finrank (ZMod p) F = q) :
    ∃ a : F, a ≠ 1 ∧ a ∈ normEquationSet (ZMod p) F := by
  have hqthree : q = 3 := by
    rcases hqodd with ⟨k, hk⟩
    omega
  exact exists_nontrivial_mem_normEquationSet_of_q_eq_three
    F hpodd hqthree hfinrank

end

end Submission.OddOrder.BG.AppendixC
