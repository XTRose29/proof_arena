import Mathlib.GroupTheory.ClassEquation
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Solvable
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.NumberTheory.Niven
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.Tactic

open Polynomial

namespace BurnsideCharacter

noncomputable section

theorem character_lift (G : Type*) [Group G] [Fintype G] :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra ℚ K)
      (i : K →ₐ[ℚ] ℂ),
      ∀ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
        (ρ : Representation ℂ G V) (g : G),
        ∃ x : K, i x = LinearMap.trace ℂ V (ρ g) ∧ IsIntegral ℤ x ∧
          ∀ σ : K →+* ℂ, ‖σ x‖ ≤ Module.finrank ℂ V := by
  let n := Monoid.exponent G
  let K := CyclotomicField n ℚ
  let p : ℚ[X] := X ^ n - 1
  letI : NeZero n := by
    dsimp [n]
    infer_instance
  letI : NeZero (n : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne n)⟩
  letI : IsCyclotomicExtension {n} ℚ K :=
    CyclotomicField.isCyclotomicExtension n ℚ
  letI : Polynomial.IsSplittingField ℚ K p := by
    dsimp [p]
    exact IsCyclotomicExtension.isSplittingField_X_pow_sub_one n ℚ _
  let i : K →ₐ[ℚ] ℂ :=
    Polynomial.IsSplittingField.lift K p (IsAlgClosed.splits _)
  refine ⟨K, inferInstance, inferInstance, inferInstance, i, ?_⟩
  intro V _ _ _ ρ g
  let roots := (ρ g).charpoly.roots
  have htrace : LinearMap.trace ℂ V (ρ g) = roots.sum :=
    Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)
  have hp_range : Algebra.adjoin ℚ (p.rootSet ℂ) = i.range :=
    Polynomial.IsSplittingField.adjoin_rootSet_eq_range K p i
  have root_mem (μ : ℂ) (hμ : μ ∈ roots) : μ ∈ i.range := by
    rw [← hp_range]
    apply Algebra.subset_adjoin
    rw [Polynomial.mem_rootSet_of_ne]
    · have hρ : (ρ g) ^ n = 1 := by
        simpa [n] using congrArg ρ (Monoid.pow_exponent_eq_one g)
      have hEigen : Module.End.HasEigenvalue (ρ g) μ :=
        (Module.End.hasEigenvalue_iff_isRoot_charpoly (ρ g) μ).2
          (Polynomial.isRoot_of_mem_roots hμ)
      obtain ⟨v, hv⟩ := hEigen.exists_hasEigenvector
      have hvpow : v = μ ^ n • v := by
        simpa [hρ] using hv.pow_apply n
      have hμpow : μ ^ n = 1 :=
        ((smul_left_injective ℂ hv.2) (by simpa using hvpow)).symm
      simp [p, hμpow]
    · dsimp [p]
      simpa using Polynomial.X_pow_sub_C_ne_zero (NeZero.pos n) (1 : ℚ)
  choose pre hpre using fun μ : {x // x ∈ roots} ↦ root_mem μ μ.2
  have root_pow (μ : {x // x ∈ roots}) : (μ : ℂ) ^ n = 1 := by
    have hρ : (ρ g) ^ n = 1 := by
      simpa [n] using congrArg ρ (Monoid.pow_exponent_eq_one g)
    have hEigen : Module.End.HasEigenvalue (ρ g) μ :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly (ρ g) μ).2
        (Polynomial.isRoot_of_mem_roots μ.2)
    obtain ⟨v, hv⟩ := hEigen.exists_hasEigenvector
    have hvpow : v = (μ : ℂ) ^ n • v := by
      simpa [hρ] using hv.pow_apply n
    exact ((smul_left_injective ℂ hv.2) (by simpa using hvpow)).symm
  have pre_pow (μ : {x // x ∈ roots}) : pre μ ^ n = 1 := by
    apply i.injective
    rw [map_pow, map_one, hpre]
    exact root_pow μ
  let lifted : Multiset K := roots.attach.map pre
  have lifted_map : lifted.map i = roots := by
    calc
      lifted.map i = roots.attach.map (i ∘ pre) := by
        simp only [lifted, Multiset.map_map]
      _ = roots.attach.map Subtype.val := by
        apply Multiset.map_congr rfl
        intro μ _
        exact hpre μ
      _ = roots := Multiset.attach_map_val roots
  refine ⟨lifted.sum, ?_, ?_, ?_⟩
  · rw [map_multiset_sum, lifted_map, htrace]
  · apply IsIntegral.multiset_sum
    intro y hy
    simp only [lifted, Multiset.mem_map, Multiset.mem_attach] at hy
    obtain ⟨μ, _, rfl⟩ := hy
    exact IsIntegral.of_pow (NeZero.pos n) (pre_pow μ ▸ isIntegral_one)
  · intro σ
    calc
      ‖σ lifted.sum‖ = ‖(lifted.map σ).sum‖ := by rw [map_multiset_sum]
      _ ≤ ((lifted.map σ).map fun z => ‖z‖).sum := norm_multiset_sum_le _
      _ = lifted.card := by
        rw [Multiset.map_map]
        have hmap : lifted.map (fun y => ‖σ y‖) = lifted.map (fun _ => (1 : ℝ)) := by
          apply Multiset.map_congr rfl
          intro y hy
          simp only [lifted, Multiset.mem_map, Multiset.mem_attach] at hy
          obtain ⟨μ, _, rfl⟩ := hy
          apply Complex.norm_eq_one_of_pow_eq_one
          · rw [← map_pow, pre_pow, map_one]
          · exact NeZero.ne n
        change (lifted.map (fun y => ‖σ y‖)).sum = _
        rw [hmap]
        simp
      _ = Module.finrank ℂ V := by
        rw [show lifted.card = roots.card by simp [lifted]]
        have hcard : roots.card = Module.finrank ℂ V := by
          change (ρ g).charpoly.roots.card = Module.finrank ℂ V
          rw [← (ρ g).charpoly_natDegree]
          exact (IsAlgClosed.splits (ρ g).charpoly).natDegree_eq_card_roots.symm
        exact_mod_cast hcard

open scoped MonoidAlgebra

def blockMatrixRepresentation {G : Type*} [Group G] {r : ℕ} (d : Fin r → ℕ)
    (E : ℂ[G] ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) (i : Fin r) :
    G →* Matrix (Fin (d i)) (Fin (d i)) ℂ :=
  (((Pi.evalAlgHom ℂ (fun i => Matrix (Fin (d i)) (Fin (d i)) ℂ) i).comp E.toAlgHom).toMonoidHom.comp
    (MonoidAlgebra.of ℂ G))

def blockRepresentation {G : Type*} [Group G] {r : ℕ} (d : Fin r → ℕ)
    (E : ℂ[G] ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) (i : Fin r) :
    Representation ℂ G (Fin (d i) → ℂ) :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp (blockMatrixRepresentation d E i)

noncomputable def conjugacyClassFinset {G : Type*} [Group G] [Fintype G] (g : G) : Finset G :=
  by
    classical
    exact Finset.univ.image fun h => h * g * h⁻¹

theorem mem_conjugacyClassFinset {G : Type*} [Group G] [Fintype G] {g y : G} :
    y ∈ conjugacyClassFinset g ↔ ∃ h : G, h * g * h⁻¹ = y := by
  classical
  simp [conjugacyClassFinset]

def classSum {G : Type*} [Group G] [Fintype G] (g : G) : ℂ[G] :=
  ∑ y ∈ conjugacyClassFinset g, MonoidAlgebra.single y 1

def classSumInt {G : Type*} [Group G] [Fintype G] (g : G) : ℤ[G] :=
  ∑ y ∈ conjugacyClassFinset g, MonoidAlgebra.single y 1

theorem classSum_conj {G : Type*} [Group G] [Fintype G] (g x : G) :
    MonoidAlgebra.single x (1 : ℂ) * classSum g * MonoidAlgebra.single x⁻¹ 1 = classSum g := by
  classical
  simp only [classSum, Finset.mul_sum, Finset.sum_mul, MonoidAlgebra.single_mul_single,
    mul_one]
  change (∑ y ∈ conjugacyClassFinset g, MonoidAlgebra.single (x * y * x⁻¹) 1) = _
  apply Finset.sum_bij (fun y _ => x * y * x⁻¹)
  · intro y hy
    rw [mem_conjugacyClassFinset] at hy ⊢
    obtain ⟨h, rfl⟩ := hy
    refine ⟨x * h, ?_⟩
    group
  · intro a _ b _ hab
    simpa using congrArg (fun z => x⁻¹ * z * x) hab
  · intro y hy
    refine ⟨x⁻¹ * y * x, ?_, ?_⟩
    · rw [mem_conjugacyClassFinset] at hy ⊢
      obtain ⟨h, rfl⟩ := hy
      refine ⟨x⁻¹ * h, ?_⟩
      group
    · group
  · intro y _
    rfl

theorem classSum_commute {G : Type*} [Group G] [Fintype G] (g x : G) :
    MonoidAlgebra.single x (1 : ℂ) * classSum g = classSum g * MonoidAlgebra.single x 1 := by
  have h := congrArg (fun z : ℂ[G] => z * MonoidAlgebra.single x (1 : ℂ))
    (classSum_conj g x)
  simpa [mul_assoc, ← MonoidAlgebra.one_def] using h

theorem classSum_commute_all {G : Type*} [Group G] [Fintype G] (g : G) (a : ℂ[G]) :
    a * classSum g = classSum g * a := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [add_mul, mul_add, ha, hb]
  | single x r =>
      calc
        MonoidAlgebra.single x r * classSum g =
            (r • MonoidAlgebra.single x (1 : ℂ)) * classSum g := by simp
        _ = r • (MonoidAlgebra.single x (1 : ℂ) * classSum g) := by
          rw [smul_mul_assoc]
        _ = r • (classSum g * MonoidAlgebra.single x (1 : ℂ)) := by
          rw [classSum_commute]
        _ = classSum g * (r • MonoidAlgebra.single x (1 : ℂ)) := by
          rw [mul_smul_comm]
        _ = classSum g * MonoidAlgebra.single x r := by simp

theorem matrix_eq_scalar_of_commute {n R : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] [CommRing R] (M : Matrix n n R) (k : n)
    (hM : ∀ N : Matrix n n R, M * N = N * M) :
    M = Matrix.scalar n (M k k) := by
  classical
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_iff_commute_single'.2 fun i j => (hM _).symm
  rw [← hc]
  simp

theorem block_classSum_scalar {G : Type*} [Group G] [Fintype G] {r : ℕ}
    (d : Fin r → ℕ) (hd : ∀ i, NeZero (d i))
    (E : ℂ[G] ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (g : G) (i : Fin r) :
    E (classSum g) i = Matrix.scalar (Fin (d i)) (E (classSum g) i 0 0) := by
  letI : NeZero (d i) := hd i
  apply matrix_eq_scalar_of_commute _ 0
  intro N
  let target : ∀ j, Matrix (Fin (d j)) (Fin (d j)) ℂ := Function.update 0 i N
  obtain ⟨a, ha⟩ := E.surjective target
  have hcomm := congrArg E (classSum_commute_all g a)
  have hi := congrFun hcomm i
  simpa [ha, target] using hi.symm

theorem block_classSum_trace_relation {G : Type*} [Group G] [Fintype G] {r : ℕ}
    (d : Fin r → ℕ) (hd : ∀ i, NeZero (d i))
    (E : ℂ[G] ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (g : G) (i : Fin r) :
    (d i : ℂ) * E (classSum g) i 0 0 =
      ((conjugacyClassFinset g).card : ℂ) * Matrix.trace (E (MonoidAlgebra.single g 1) i) := by
  letI : NeZero (d i) := hd i
  have hclass (y : G) (hy : y ∈ conjugacyClassFinset g) :
      Matrix.trace (E (MonoidAlgebra.single y 1) i) =
        Matrix.trace (E (MonoidAlgebra.single g 1) i) := by
    rw [mem_conjugacyClassFinset] at hy
    obtain ⟨h, rfl⟩ := hy
    have htraceToLin (A : Matrix (Fin (d i)) (Fin (d i)) ℂ) :
        LinearMap.trace ℂ (Fin (d i) → ℂ) (Matrix.toLinAlgEquiv' A) = A.trace := by
      change LinearMap.trace ℂ (Fin (d i) → ℂ) A.toLin' = A.trace
      exact Matrix.trace_toLin'_eq A
    rw [← htraceToLin, ← htraceToLin]
    simpa [Representation.character, blockRepresentation, blockMatrixRepresentation] using
      Representation.char_conj (blockRepresentation d E i) g h
  have htrace := congrArg Matrix.trace (block_classSum_scalar d hd E g i)
  rw [Matrix.scalar_apply, Matrix.trace_diagonal] at htrace
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at htrace
  calc
    (d i : ℂ) * E (classSum g) i 0 0 = Matrix.trace (E (classSum g) i) := htrace.symm
    _ = ∑ y ∈ conjugacyClassFinset g,
        Matrix.trace (E (MonoidAlgebra.single y 1) i) := by
      simp only [classSum, map_sum, Finset.sum_apply, Matrix.trace_sum]
    _ = ∑ _y ∈ conjugacyClassFinset g,
        Matrix.trace (E (MonoidAlgebra.single g 1) i) := by
      apply Finset.sum_congr rfl
      intro y hy
      exact hclass y hy
    _ = ((conjugacyClassFinset g).card : ℂ) *
        Matrix.trace (E (MonoidAlgebra.single g 1) i) := by simp

theorem block_classSum_isIntegral {G : Type*} [Group G] [Fintype G] {r : ℕ}
    (d : Fin r → ℕ) (hd : ∀ i, NeZero (d i))
    (E : ℂ[G] ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (g : G) (i : Fin r) : IsIntegral ℤ (E (classSum g) i 0 0) := by
  letI : NeZero (d i) := hd i
  let coeffMap : ℤ[G] →+* ℂ[G] := MonoidAlgebra.mapRingHom G (Int.castRingHom ℂ)
  let blockMap : ℂ[G] →+* Matrix (Fin (d i)) (Fin (d i)) ℂ :=
    (Pi.evalRingHom (fun j => Matrix (Fin (d j)) (Fin (d j)) ℂ) i).comp E.toRingEquiv.toRingHom
  have hzInt : IsIntegral ℤ (classSumInt g) := IsIntegral.of_finite ℤ _
  have hzMatrix : IsIntegral ℤ (blockMap (coeffMap (classSumInt g))) :=
    map_isIntegral_int blockMap (map_isIntegral_int coeffMap hzInt)
  have hcoeff : coeffMap (classSumInt g) = classSum g := by
    simp [coeffMap, classSumInt, classSum]
  have hscalar := block_classSum_scalar d hd E g i
  have hscalarInt :
      IsIntegral ℤ (Matrix.scalar (Fin (d i)) (E (classSum g) i 0 0)) := by
    rw [← hscalar]
    simpa [blockMap, hcoeff] using hzMatrix
  apply (isIntegral_algHom_iff (Matrix.scalarAlgHom (Fin (d i)) ℤ)
    (fun _ _ h => Matrix.scalar_inj.mp h)).mp
  simpa using hscalarInt

theorem eq_zero_of_mem_multiset_of_sum_eq_zero {s : Multiset ℝ}
    (hnonneg : ∀ x ∈ s, 0 ≤ x) (hsum : s.sum = 0) {x : ℝ} (hx : x ∈ s) : x = 0 := by
  induction s using Multiset.induction_on with
  | empty => simp at hx
  | @cons a s ih =>
      rw [Multiset.sum_cons] at hsum
      have ha : 0 ≤ a := hnonneg a (by simp)
      have hs : 0 ≤ s.sum := Multiset.sum_nonneg fun y hy => hnonneg y (by simp [hy])
      rcases Multiset.mem_cons.mp hx with rfl | hx
      · linarith
      · apply ih (fun y hy => hnonneg y (by simp [hy]))
        · linarith
        · exact hx

theorem sum_normSq_sub (s : Multiset ℂ) (a : ℂ) :
    (s.map fun z => Complex.normSq (z - a)).sum =
      (s.map Complex.normSq).sum + (s.card : ℝ) * Complex.normSq a -
        2 * (s.sum * star a).re := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons z s ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, Complex.normSq_sub, ih]
      simp only [Multiset.card_cons, Nat.cast_add, Nat.cast_one, Multiset.sum_cons,
        Multiset.map_cons, add_mul, one_mul]
      simp
      ring

theorem eq_average_of_mem_of_norm_eq_one {s : Multiset ℂ}
    (hs : ∀ z ∈ s, ‖z‖ = 1) (hcard : s.card ≠ 0)
    (havg : ‖s.sum / (s.card : ℂ)‖ = 1) {z : ℂ} (hz : z ∈ s) :
    z = s.sum / (s.card : ℂ) := by
  let a : ℂ := s.sum / (s.card : ℂ)
  have hcardC : (s.card : ℂ) ≠ 0 := by exact_mod_cast hcard
  have hsum : s.sum = (s.card : ℂ) * a := by
    dsimp [a]
    field_simp
  have haNorm : ‖a‖ = 1 := havg
  have haSq : Complex.normSq a = 1 := by
    rw [Complex.normSq_eq_norm_sq, haNorm]
    norm_num
  have hrootsSq : (s.map Complex.normSq).sum = (s.card : ℝ) := by
    calc
      (s.map Complex.normSq).sum = (s.map fun _ => (1 : ℝ)).sum := by
        apply congrArg Multiset.sum
        apply Multiset.map_congr rfl
        intro y hy
        rw [Complex.normSq_eq_norm_sq, hs y hy]
        norm_num
      _ = (s.card : ℝ) := by simp
  have hcross : (s.sum * star a).re = (s.card : ℝ) := by
    rw [hsum]
    simp [mul_assoc, Complex.mul_conj, haSq]
  have hdistSum : (s.map fun y => Complex.normSq (y - a)).sum = 0 := by
    rw [sum_normSq_sub, hrootsSq, haSq, hcross]
    ring
  have hzSq : Complex.normSq (z - a) = 0 :=
    eq_zero_of_mem_multiset_of_sum_eq_zero
      (fun y hy => by
        obtain ⟨w, _, rfl⟩ := Multiset.mem_map.mp hy
        exact Complex.normSq_nonneg (w - a))
      hdistSum (Multiset.mem_map_of_mem _ hz)
  exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp hzSq)

theorem end_eq_algebraMap_of_pow_eq_one_of_norm_trace_div_finrank_eq_one
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) {n : ℕ} (hn : n ≠ 0) (hpow : f ^ n = 1)
    (hfinrank : Module.finrank ℂ V ≠ 0)
    (hnorm : ‖LinearMap.trace ℂ V f / (Module.finrank ℂ V : ℂ)‖ = 1) :
    f = algebraMap ℂ (Module.End ℂ V)
      (LinearMap.trace ℂ V f / (Module.finrank ℂ V : ℂ)) := by
  let a : ℂ := LinearMap.trace ℂ V f / (Module.finrank ℂ V : ℂ)
  let roots := f.charpoly.roots
  have htrace : LinearMap.trace ℂ V f = roots.sum :=
    Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)
  have hcard : roots.card = Module.finrank ℂ V := by
    change f.charpoly.roots.card = Module.finrank ℂ V
    rw [← f.charpoly_natDegree]
    exact (IsAlgClosed.splits f.charpoly).natDegree_eq_card_roots.symm
  have hrootNorm (μ : ℂ) (hμ : μ ∈ roots) : ‖μ‖ = 1 := by
    have hEigen : f.HasEigenvalue μ :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).2
        (Polynomial.isRoot_of_mem_roots hμ)
    obtain ⟨v, hv⟩ := hEigen.exists_hasEigenvector
    have hvpow : v = μ ^ n • v := by
      simpa [hpow] using hv.pow_apply n
    have hμpow : μ ^ n = 1 :=
      ((smul_left_injective ℂ hv.2) (by simpa using hvpow)).symm
    exact Complex.norm_eq_one_of_pow_eq_one hμpow hn
  have havg : ‖roots.sum / (roots.card : ℂ)‖ = 1 := by
    rw [← htrace, hcard]
    exact hnorm
  have hall (μ : ℂ) (hμ : μ ∈ roots) : μ = a := by
    dsimp [a]
    rw [htrace, ← hcard]
    exact eq_average_of_mem_of_norm_eq_one hrootNorm (hcard ▸ hfinrank) havg hμ
  have hsqfree : Squarefree (X ^ n - 1 : ℂ[X]) :=
    (Polynomial.separable_X_pow_sub_C 1 (by exact_mod_cast hn) one_ne_zero).squarefree
  have haeval : aeval f (X ^ n - 1 : ℂ[X]) = 0 := by
    simp [hpow]
  have hfss : f.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsqfree haeval
  have hdiffss : (f - algebraMap ℂ (Module.End ℂ V) a).IsSemisimple :=
    Module.End.isSemisimple_sub_algebraMap_iff.mpr hfss
  apply sub_eq_zero.mp
  apply hdiffss.eq_zero_iff_forall_eigenvalue.mpr
  intro μ hμ
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hvEq := hv.apply_eq_smul
  have hfEq : f v = (μ + a) • v := by
    calc
      f v = (f v - a • v) + a • v := by abel
      _ = μ • v + a • v := by simpa using congrArg (fun w => w + a • v) hvEq
      _ = (μ + a) • v := by rw [add_smul]
  have hfvec : f.HasEigenvector (μ + a) v :=
    Module.End.hasEigenvector_iff.mpr
      ⟨Module.End.mem_eigenspace_iff.mpr hfEq, hv.2⟩
  have hfval : f.HasEigenvalue (μ + a) :=
    Module.End.hasEigenvalue_of_hasEigenvector hfvec
  have hroot : f.charpoly.IsRoot (μ + a) :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly f (μ + a)).mp hfval
  have hmem : μ + a ∈ roots := by
    rw [show roots = f.charpoly.roots by rfl, Polynomial.mem_roots f.charpoly_monic.ne_zero]
    exact hroot
  have := hall (μ + a) hmem
  linear_combination this

def matrixScalarKernel {G n : Type*} [Group G] [Fintype n] [DecidableEq n]
    [Nonempty n] (ρ : G →* Matrix n n ℂ) : Subgroup G where
  carrier := {g | ∃ c : ℂ, ρ g = Matrix.scalar n c}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro g h ⟨c, hc⟩ ⟨e, he⟩
    refine ⟨c * e, ?_⟩
    rw [map_mul, hc, he, map_mul]
  inv_mem' := by
    rintro g ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      intro hc0
      have hone : (1 : Matrix n n ℂ) = 0 := calc
        1 = ρ (g * g⁻¹) := by simp
        _ = ρ g * ρ g⁻¹ := by rw [map_mul]
        _ = 0 := by rw [hc, hc0]; simp
      exact one_ne_zero hone
    refine ⟨c⁻¹, ?_⟩
    calc
      ρ g⁻¹ = ρ g⁻¹ * 1 := by simp
      _ = ρ g⁻¹ * (Matrix.scalar n c * Matrix.scalar n c⁻¹) := by simp [hc0]
      _ = (ρ g⁻¹ * Matrix.scalar n c) * Matrix.scalar n c⁻¹ := by rw [mul_assoc]
      _ = 1 * Matrix.scalar n c⁻¹ := by rw [← hc, ← map_mul]; simp
      _ = Matrix.scalar n c⁻¹ := by simp

instance matrixScalarKernel_normal {G n : Type*} [Group G] [Fintype n] [DecidableEq n]
    [Nonempty n] (ρ : G →* Matrix n n ℂ) : (matrixScalarKernel ρ).Normal where
  conj_mem g := by
    rintro ⟨c, hc⟩ h
    refine ⟨c, ?_⟩
    rw [map_mul, map_mul, hc]
    calc
      ρ h * Matrix.scalar n c * ρ h⁻¹ =
          Matrix.scalar n c * (ρ h * ρ h⁻¹) := by
        rw [← mul_assoc, (Matrix.scalar_commute c (fun _ => mul_comm _ _) (ρ h)).eq.symm,
          mul_assoc]
      _ = Matrix.scalar n c := by rw [← map_mul]; simp

theorem block_is_one_dimensional_and_trivial_of_scalar_at_nonidentity
    {G : Type*} [Group G] [Fintype G] [IsSimpleGroup G]
    {r : ℕ} (d : Fin r → ℕ) (hd : ∀ i, NeZero (d i))
    (E : ℂ[G] ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (i : Fin r) (g : G) (hg : g ≠ 1) (hns : ¬IsSolvable G)
    (hscalar : ∃ c : ℂ,
      E (MonoidAlgebra.single g 1) i = Matrix.scalar (Fin (d i)) c) :
    d i = 1 ∧ E (MonoidAlgebra.single g 1) i = 1 := by
  letI : NeZero (d i) := hd i
  let ρ := blockMatrixRepresentation d E i
  have hgmem : g ∈ matrixScalarKernel ρ := by
    change ∃ c : ℂ, E (MonoidAlgebra.single g 1) i = Matrix.scalar (Fin (d i)) c
    exact hscalar
  have hscalarTop : matrixScalarKernel ρ = ⊤ :=
    (Subgroup.Normal.eq_bot_or_eq_top (matrixScalarKernel_normal ρ)).resolve_left fun hbot => by
      have : g = 1 := by
        rw [← Subgroup.mem_bot, ← hbot]
        exact hgmem
      exact hg this
  have hallScalar (h : G) : ∃ c : ℂ, ρ h = Matrix.scalar (Fin (d i)) c := by
    have hm : h ∈ matrixScalarKernel ρ := by
      rw [hscalarTop]
      exact Subgroup.mem_top h
    exact hm
  have hkerTop : ρ.ker = ⊤ :=
    (Subgroup.Normal.eq_bot_or_eq_top ρ.normal_ker).resolve_left fun hkerBot => by
      have hρinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).mp hkerBot
      have hcomm (a b : G) : a * b = b * a := by
        apply hρinj
        obtain ⟨ca, ha⟩ := hallScalar a
        obtain ⟨cb, hb⟩ := hallScalar b
        rw [map_mul, map_mul, ha, hb]
        exact (Matrix.scalar_commute ca (fun _ => mul_comm _ _)
          (Matrix.scalar (Fin (d i)) cb)).eq
      exact hns (IsSimpleGroup.comm_iff_isSolvable.mp hcomm)
  have hallOne (h : G) : ρ h = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [hkerTop]
    exact Subgroup.mem_top h
  have hallBlockScalar (a : ℂ[G]) :
      ∃ c : ℂ, E a i = Matrix.scalar (Fin (d i)) c := by
    induction a using MonoidAlgebra.induction_linear with
    | zero => exact ⟨0, by simp⟩
    | add a b ha hb =>
        obtain ⟨ca, ha⟩ := ha
        obtain ⟨cb, hb⟩ := hb
        refine ⟨ca + cb, ?_⟩
        rw [map_add, Pi.add_apply, ha, hb]
        exact (map_add (Matrix.scalar (Fin (d i))) ca cb).symm
    | single h c =>
        refine ⟨c, ?_⟩
        rw [show MonoidAlgebra.single h c = c • MonoidAlgebra.single h (1 : ℂ) by simp,
          map_smul, Pi.smul_apply]
        change c • ρ h = _
        rw [hallOne]
        ext u v
        simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]
  have everyMatrixScalar (M : Matrix (Fin (d i)) (Fin (d i)) ℂ) :
      ∃ c : ℂ, M = Matrix.scalar (Fin (d i)) c := by
    let target : ∀ j, Matrix (Fin (d j)) (Fin (d j)) ℂ := Function.update 0 i M
    obtain ⟨a, ha⟩ := E.surjective target
    obtain ⟨c, hc⟩ := hallBlockScalar a
    refine ⟨c, ?_⟩
    rw [ha] at hc
    simpa [target] using hc
  have hsub : ∀ u v : Fin (d i), u = v := by
    intro u v
    by_contra huv
    obtain ⟨c, hc⟩ := everyMatrixScalar (Matrix.single u v 1)
    have huvEntry := congrFun₂ hc u v
    simp [Matrix.scalar_apply, huv] at huvEntry
  have hdimLeFin : Fintype.card (Fin (d i)) ≤ 1 := Fintype.card_le_one_iff.mpr hsub
  have hdimLe : d i ≤ 1 := by simpa using hdimLeFin
  have hdim : d i = 1 := Nat.le_antisymm hdimLe (Nat.one_le_iff_ne_zero.mpr (NeZero.ne _))
  refine ⟨hdim, ?_⟩
  change ρ g = 1
  exact hallOne g

theorem block_trace_eq_zero_or_eq_scalar_of_coprime
    {G : Type*} [Group G] [Fintype G]
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K] (iK : K →ₐ[ℚ] ℂ)
    {r : ℕ} (d : Fin r → ℕ) (hd : ∀ i, NeZero (d i))
    (E : ℂ[G] ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (g : G) (i : Fin r) (x : K)
    (hx : iK x = Matrix.trace (E (MonoidAlgebra.single g 1) i))
    (hxInt : IsIntegral ℤ x)
    (hxNorm : ∀ σ : K →+* ℂ, ‖σ x‖ ≤ d i)
    (hcop : Nat.Coprime (conjugacyClassFinset g).card (d i)) :
    Matrix.trace (E (MonoidAlgebra.single g 1) i) = 0 ∨
      E (MonoidAlgebra.single g 1) i =
        Matrix.scalar (Fin (d i))
          (Matrix.trace (E (MonoidAlgebra.single g 1) i) / (d i : ℂ)) := by
  letI : NeZero (d i) := hd i
  let m := (conjugacyClassFinset g).card
  let z : K := x / (d i : K)
  let lambda : ℂ := E (classSum g) i 0 0
  have hd0 : d i ≠ 0 := NeZero.ne (d i)
  have hdC : (d i : ℂ) ≠ 0 := by exact_mod_cast hd0
  have hdK : (d i : K) ≠ 0 := by exact_mod_cast hd0
  have hrel : (d i : ℂ) * lambda = (m : ℂ) * iK x := by
    dsimp [lambda, m]
    rw [hx]
    exact block_classSum_trace_relation d hd E g i
  have hiz : iK z = Matrix.trace (E (MonoidAlgebra.single g 1) i) / (d i : ℂ) := by
    simp [z, hx]
  have hiy : iK ((m : K) * z) = lambda := by
    rw [map_mul, map_natCast, hiz]
    rw [← hx]
    rw [← mul_div_assoc, div_eq_iff hdC]
    exact hrel.symm.trans (mul_comm _ _)
  have hyIntImage : IsIntegral ℤ (iK ((m : K) * z)) := by
    rw [hiy]
    exact block_classSum_isIntegral d hd E g i
  have hyInt : IsIntegral ℤ ((m : K) * z) :=
    (isIntegral_algHom_iff (iK.restrictScalars ℤ) iK.injective).mp hyIntImage
  have hbezZ : (1 : ℤ) = (m : ℤ) * Nat.gcdA m (d i) +
      (d i : ℤ) * Nat.gcdB m (d i) := by
    calc
      (1 : ℤ) = (Nat.gcd m (d i) : ℕ) := by rw [hcop.gcd_eq_one]; norm_num
      _ = (m : ℤ) * Nat.gcdA m (d i) + (d i : ℤ) * Nat.gcdB m (d i) :=
        Nat.gcd_eq_gcd_ab m (d i)
  have hbezK : (1 : K) = (m : K) * (Nat.gcdA m (d i) : K) +
      (d i : K) * (Nat.gcdB m (d i) : K) := by
    exact_mod_cast hbezZ
  have hzEq : z = (Nat.gcdA m (d i)) • ((m : K) * z) +
      (Nat.gcdB m (d i)) • x := by
    have hdz : (d i : K) * z = x := by
      dsimp [z]
      field_simp
    rw [← hdz]
    rw [zsmul_eq_mul, zsmul_eq_mul]
    calc
      z = 1 * z := by simp
      _ = ((m : K) * (Nat.gcdA m (d i) : K) +
          (d i : K) * (Nat.gcdB m (d i) : K)) * z := by rw [← hbezK]
      _ = (Nat.gcdA m (d i) : K) * ((m : K) * z) +
          (Nat.gcdB m (d i) : K) * ((d i : K) * z) := by ring
  have hzInt : IsIntegral ℤ z := by
    rw [hzEq]
    exact (hyInt.zsmul _).add (hxInt.zsmul _)
  by_cases hx0 : x = 0
  · left
    rw [← hx, hx0, map_zero]
  · right
    have hz0 : z ≠ 0 := div_ne_zero hx0 hdK
    have hzNorm : ∀ σ : K →+* ℂ, ‖σ z‖ ≤ 1 := by
      intro σ
      change ‖σ (x / (d i : K))‖ ≤ 1
      rw [map_div₀ σ x (d i : K), map_natCast, norm_div, norm_natCast]
      exact (div_le_one (by positivity)).2 (hxNorm σ)
    obtain ⟨n, hn, hzn⟩ :=
      NumberField.Embeddings.pow_eq_one_of_norm_le_one K ℂ hz0 hzInt hzNorm
    have hiNorm : ‖iK z‖ = 1 :=
      Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hzn, map_one]) hn.ne'
    let f : Module.End ℂ (Fin (d i) → ℂ) := blockRepresentation d E i g
    have hfPow : f ^ Monoid.exponent G = 1 := by
      dsimp [f]
      simpa using congrArg (blockRepresentation d E i) (Monoid.pow_exponent_eq_one g)
    have hfinrank : Module.finrank ℂ (Fin (d i) → ℂ) ≠ 0 := by
      simp [hd0]
    have hfTrace : LinearMap.trace ℂ (Fin (d i) → ℂ) f =
        Matrix.trace (E (MonoidAlgebra.single g 1) i) := by
      change LinearMap.trace ℂ (Fin (d i) → ℂ)
        (Matrix.toLinAlgEquiv' (E (MonoidAlgebra.single g 1) i)) = _
      change LinearMap.trace ℂ (Fin (d i) → ℂ)
        (E (MonoidAlgebra.single g 1) i).toLin' = _
      exact Matrix.trace_toLin'_eq _
    have hfNorm : ‖LinearMap.trace ℂ (Fin (d i) → ℂ) f /
        (Module.finrank ℂ (Fin (d i) → ℂ) : ℂ)‖ = 1 := by
      rw [hfTrace]
      simp only [Module.finrank_pi, Fintype.card_fin]
      rw [← hiz]
      exact hiNorm
    have hfScalar := end_eq_algebraMap_of_pow_eq_one_of_norm_trace_div_finrank_eq_one
      f (Monoid.exponent_ne_zero.mpr Monoid.ExponentExists.of_finite) hfPow hfinrank hfNorm
    have hmatrix := congrArg LinearMap.toMatrix' hfScalar
    have hfMatrix : LinearMap.toMatrix' f = E (MonoidAlgebra.single g 1) i := by
      change LinearMap.toMatrix'
        (Matrix.toLinAlgEquiv' (E (MonoidAlgebra.single g 1) i)) = _
      change LinearMap.toMatrix' (E (MonoidAlgebra.single g 1) i).toLin' = _
      exact LinearMap.toMatrix'_toLin' _
    rw [hfMatrix, LinearMap.toMatrix'_algebraMap, hfTrace] at hmatrix
    simp only [Module.finrank_pi, Fintype.card_fin] at hmatrix
    exact hmatrix

theorem trace_lmul_single_eq_zero {G : Type*} [Group G] [Fintype G]
    {g : G} (hg : g ≠ 1) :
    LinearMap.trace ℂ ℂ[G] (Algebra.lmul ℂ ℂ[G] (MonoidAlgebra.single g 1)) = 0 := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ
    (MonoidAlgebra.basis G ℂ)]
  rw [Matrix.trace]
  apply Finset.sum_eq_zero
  intro h _
  rw [Matrix.diag, LinearMap.toMatrix_apply]
  rw [MonoidAlgebra.basis_apply, Algebra.coe_lmul_eq_mul,
    LinearMap.mul_apply', MonoidAlgebra.single_mul_single, mul_one]
  change (MonoidAlgebra.single (g * h) (1 : ℂ) : ℂ[G]) h = 0
  rw [Finsupp.single_eq_of_ne]
  intro hgh
  apply hg
  apply mul_right_cancel (b := h)
  simpa using hgh.symm

theorem matrix_stdBasis_repr {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (uv : n × n) :
    (Matrix.stdBasis ℂ n n).repr A uv = A uv.1 uv.2 := by
  simp [Matrix.stdBasis, Pi.basis_repr]

theorem trace_lmul_matrix {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) :
    LinearMap.trace ℂ (Matrix n n ℂ) (Algebra.lmul ℂ (Matrix n n ℂ) A) =
      (Fintype.card n : ℂ) * Matrix.trace A := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (Matrix.stdBasis ℂ n n), Matrix.trace]
  simp only [Matrix.diag, LinearMap.toMatrix_apply,
    Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
  rw [show (∑ uv : n × n, (Matrix.stdBasis ℂ n n).repr
      (A * Matrix.stdBasis ℂ n n uv) uv) =
      ∑ uv : n × n, (A * Matrix.single uv.1 uv.2 (1 : ℂ)) uv.1 uv.2 by
    apply Finset.sum_congr rfl
    intro uv _
    rw [Matrix.stdBasis_eq_single, matrix_stdBasis_repr]]
  have hmul (u v : n) :
      (A * Matrix.single u v (1 : ℂ)) u v = A u u := by
    rw [Matrix.mul_apply]
    simp [Matrix.single_apply]
  simp_rw [hmul]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Matrix.trace, Matrix.diag]
  rw [Finset.mul_sum]

theorem trace_lmul_pi_matrix {r : ℕ} (d : Fin r → ℕ)
    (A : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    LinearMap.trace ℂ (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
      (Algebra.lmul ℂ (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) A) =
      ∑ i, (d i : ℂ) * Matrix.trace (A i) := by
  classical
  let b : Module.Basis (Σ i, Fin (d i) × Fin (d i)) ℂ
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :=
    Pi.basis fun i => Matrix.stdBasis ℂ (Fin (d i)) (Fin (d i))
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.diag, LinearMap.toMatrix_apply]
  rw [show (∑ uv : Fin (d i) × Fin (d i),
      (b.repr ((Algebra.lmul ℂ (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) A)
        (b ⟨i, uv⟩))) ⟨i, uv⟩) =
      ∑ uv : Fin (d i) × Fin (d i),
        (Matrix.stdBasis ℂ (Fin (d i)) (Fin (d i))).repr
          (A i * Matrix.stdBasis ℂ (Fin (d i)) (Fin (d i)) uv) uv by
    apply Finset.sum_congr rfl
    intro uv _
    simp [b, Pi.basis_repr, Pi.basis_apply, Algebra.coe_lmul_eq_mul]]
  have h := trace_lmul_matrix (A i)
  rw [LinearMap.trace_eq_matrix_trace ℂ
    (Matrix.stdBasis ℂ (Fin (d i)) (Fin (d i))), Matrix.trace] at h
  simpa only [Matrix.diag, LinearMap.toMatrix_apply,
    Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', Fintype.card_fin] using h

def groupSum {G : Type*} [Group G] [Fintype G] : ℂ[G] :=
  ∑ g : G, MonoidAlgebra.single g 1

theorem single_mul_groupSum {G : Type*} [Group G] [Fintype G] (g : G) :
    MonoidAlgebra.single g (1 : ℂ) * groupSum = groupSum := by
  classical
  simp only [groupSum, Finset.mul_sum, MonoidAlgebra.single_mul_single, mul_one]
  exact Equiv.sum_comp (Equiv.mulLeft g) fun h : G => MonoidAlgebra.single h (1 : ℂ)

theorem groupSum_mul_single {G : Type*} [Group G] [Fintype G] (g : G) :
    groupSum * MonoidAlgebra.single g (1 : ℂ) = groupSum := by
  classical
  simp only [groupSum, Finset.sum_mul, MonoidAlgebra.single_mul_single, mul_one]
  exact Equiv.sum_comp (Equiv.mulRight g) fun h : G => MonoidAlgebra.single h (1 : ℂ)

def averagingIdempotent {G : Type*} [Group G] [Fintype G] : ℂ[G] :=
  (Fintype.card G : ℂ)⁻¹ • groupSum

theorem single_mul_averagingIdempotent {G : Type*} [Group G] [Fintype G] (g : G) :
    MonoidAlgebra.single g (1 : ℂ) * averagingIdempotent = averagingIdempotent := by
  rw [averagingIdempotent, mul_smul_comm, single_mul_groupSum]

theorem averagingIdempotent_mul_single {G : Type*} [Group G] [Fintype G] (g : G) :
    averagingIdempotent * MonoidAlgebra.single g (1 : ℂ) = averagingIdempotent := by
  rw [averagingIdempotent, smul_mul_assoc, groupSum_mul_single]

theorem averagingIdempotent_commute_all {G : Type*} [Group G] [Fintype G] (a : ℂ[G]) :
    a * averagingIdempotent = averagingIdempotent * a := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [add_mul, mul_add, ha, hb]
  | single g c =>
      calc
        MonoidAlgebra.single g c * averagingIdempotent =
            c • (MonoidAlgebra.single g (1 : ℂ) * averagingIdempotent) := by
          rw [show MonoidAlgebra.single g c =
            c • MonoidAlgebra.single g (1 : ℂ) by simp, smul_mul_assoc]
        _ = c • averagingIdempotent := by rw [single_mul_averagingIdempotent]
        _ = averagingIdempotent * MonoidAlgebra.single g c := by
          rw [show MonoidAlgebra.single g c = c • MonoidAlgebra.single g (1 : ℂ) by simp,
            mul_smul_comm, averagingIdempotent_mul_single]

theorem averagingIdempotent_sq {G : Type*} [Group G] [Fintype G] :
    averagingIdempotent (G := G) * averagingIdempotent = averagingIdempotent := by
  classical
  have hsum : groupSum * averagingIdempotent (G := G) =
      Fintype.card G • averagingIdempotent := by
    rw [groupSum, Finset.sum_mul]
    simp_rw [single_mul_averagingIdempotent (G := G)]
    simp
  calc
    averagingIdempotent * averagingIdempotent =
        (Fintype.card G : ℂ)⁻¹ •
          (groupSum (G := G) * averagingIdempotent (G := G)) := by
      rw [averagingIdempotent, smul_mul_assoc]
    _ = (Fintype.card G : ℂ)⁻¹ •
        (Fintype.card G • averagingIdempotent (G := G)) := by rw [hsum]
    _ = averagingIdempotent (G := G) := by
      rw [← Nat.cast_smul_eq_nsmul ℂ]
      rw [smul_smul]
      simp [Fintype.card_ne_zero]

theorem trace_lmul_single_one {G : Type*} [Group G] [Fintype G] :
    LinearMap.trace ℂ ℂ[G] (Algebra.lmul ℂ ℂ[G] (MonoidAlgebra.single 1 1)) =
      Fintype.card G := by
  rw [← MonoidAlgebra.one_def, map_one, LinearMap.trace_one]
  norm_cast
  exact Module.finrank_eq_card_basis (MonoidAlgebra.basis G ℂ)

theorem trace_lmul_averagingIdempotent {G : Type*} [Group G] [Fintype G] :
    LinearMap.trace ℂ ℂ[G]
      (Algebra.lmul ℂ ℂ[G] (averagingIdempotent (G := G))) = 1 := by
  classical
  rw [averagingIdempotent, groupSum, map_smul, map_sum]
  rw [map_smul, map_sum]
  have hsum : (∑ g : G, LinearMap.trace ℂ ℂ[G]
      (Algebra.lmul ℂ ℂ[G] (MonoidAlgebra.single g 1))) = (Fintype.card G : ℂ) := by
    rw [Finset.sum_eq_single 1]
    · exact trace_lmul_single_one
    · intro g _ hg
      exact trace_lmul_single_eq_zero hg
    · simp
  rw [hsum]
  simp [Fintype.card_ne_zero]

theorem trace_lmul_algEquiv {A B : Type*} [Ring A] [Ring B]
    [Algebra ℂ A] [Algebra ℂ B] [Module.Free ℂ A] [Module.Free ℂ B]
    [Module.Finite ℂ A] [Module.Finite ℂ B]
    (E : A ≃ₐ[ℂ] B) (a : A) :
    LinearMap.trace ℂ B (Algebra.lmul ℂ B (E a)) =
      LinearMap.trace ℂ A (Algebra.lmul ℂ A a) := by
  rw [← LinearMap.trace_conj' (Algebra.lmul ℂ A a) E.toLinearEquiv]
  congr 1
  ext x
  simp [LinearEquiv.conj_apply, Algebra.coe_lmul_eq_mul]

theorem coe_conjugacyClassFinset {G : Type*} [Group G] [Fintype G] (g : G) :
    (conjugacyClassFinset g : Set G) = MulAction.orbit (ConjAct G) g := by
  ext y
  rw [Finset.mem_coe, mem_conjugacyClassFinset, ConjAct.mem_orbit_conjAct,
    isConj_comm, isConj_iff]

theorem card_conjugacyClassFinset_eq_index_centralizer
    {G : Type*} [Group G] [Fintype G] (g : G) :
    (conjugacyClassFinset g).card = (Subgroup.centralizer {g}).index := by
  have hcard := congrArg Set.ncard (coe_conjugacyClassFinset g)
  have horbit : (conjugacyClassFinset g).card =
      (MulAction.stabilizer (ConjAct G) g).index := by
    rw [MulAction.index_stabilizer]
    simpa using hcard
  rw [horbit, Subgroup.centralizer_eq_comap_stabilizer]
  exact (Subgroup.index_comap_of_surjective _ ConjAct.toConjAct.surjective).symm

theorem eq_prime_pow_of_dvd_prime_pow {n p a : ℕ} (hp : Nat.Prime p)
    (h : n ∣ p ^ a) : ∃ k ≤ a, n = p ^ k := by
  obtain ⟨k, hk, hkassoc⟩ := (dvd_prime_pow hp.prime a).mp h
  refine ⟨k, hk, ?_⟩
  exact associated_iff_eq.mp hkassoc

theorem block_averagingIdempotent_scalar {G : Type*} [Group G] [Fintype G]
    {r : ℕ} (d : Fin r → ℕ) (hd : ∀ i, NeZero (d i))
    (E : ℂ[G] ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) (i : Fin r) :
    ∃ c : ℂ, E (averagingIdempotent (G := G)) i = Matrix.scalar (Fin (d i)) c := by
  letI : NeZero (d i) := hd i
  refine ⟨E averagingIdempotent i 0 0, ?_⟩
  apply matrix_eq_scalar_of_commute _ 0
  intro N
  let target : ∀ j, Matrix (Fin (d j)) (Fin (d j)) ℂ := Function.update 0 i N
  obtain ⟨a, ha⟩ := E.surjective target
  have hcomm := congrArg E (averagingIdempotent_commute_all a)
  have hi := congrFun hcomm i
  simpa [ha, target] using hi.symm

theorem exists_unique_trivial_block {G : Type*} [Group G] [Fintype G]
    {r : ℕ} (d : Fin r → ℕ) (hd : ∀ i, NeZero (d i))
    (E : ℂ[G] ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    ∃! i : Fin r,
      d i = 1 ∧ ∀ g : G, E (MonoidAlgebra.single g 1) i = 1 := by
  classical
  choose c hc using fun i => block_averagingIdempotent_scalar d hd E i
  have hc01 (i : Fin r) : c i = 0 ∨ c i = 1 := by
    letI : NeZero (d i) := hd i
    have hmat := congrFun (congrArg E (averagingIdempotent_sq (G := G))) i
    rw [map_mul, Pi.mul_apply, hc i, ← map_mul] at hmat
    have hentry := congrFun₂ hmat 0 0
    have hmul : c i * c i = c i := by
      simpa [Matrix.scalar_apply] using hentry
    have hzero : c i * (c i - 1) = 0 := by
      calc
        c i * (c i - 1) = c i * c i - c i := by ring
        _ = 0 := sub_eq_zero.mpr hmul
    rcases mul_eq_zero.mp hzero with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  let active : Finset (Fin r) := Finset.univ.filter fun i => c i = 1
  have htrace : (∑ i, (d i : ℂ) *
      Matrix.trace (E (averagingIdempotent (G := G)) i)) = 1 := by
    calc
      (∑ i, (d i : ℂ) * Matrix.trace (E averagingIdempotent i)) =
          LinearMap.trace ℂ (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
            (Algebra.lmul ℂ (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
              (E averagingIdempotent)) := (trace_lmul_pi_matrix d _).symm
      _ = LinearMap.trace ℂ ℂ[G]
          (Algebra.lmul ℂ ℂ[G] averagingIdempotent) := trace_lmul_algEquiv E _
      _ = 1 := trace_lmul_averagingIdempotent
  have hterm (i : Fin r) :
      (d i : ℂ) * Matrix.trace (E (averagingIdempotent (G := G)) i) =
        if c i = 1 then ((d i * d i : ℕ) : ℂ) else 0 := by
    letI : NeZero (d i) := hd i
    rw [hc i]
    rcases hc01 i with hzero | hone
    · simp [hzero]
    · simp [hone, Matrix.trace, Matrix.diag, Matrix.scalar_apply]
  have hcastSum : ((∑ i ∈ active, d i * d i : ℕ) : ℂ) = 1 := by
    rw [Nat.cast_sum]
    simp only [active, Finset.sum_filter]
    simpa only [hterm] using htrace
  have hsum : ∑ i ∈ active, d i * d i = 1 := by
    exact_mod_cast hcastSum
  have hactive : active.Nonempty := by
    rw [← Finset.card_pos]
    by_contra hzero
    have : active = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos hzero)
    rw [this] at hsum
    simp at hsum
  have hcardLe : active.card ≤ 1 := by
    calc
      active.card = ∑ i ∈ active, 1 := Finset.card_eq_sum_ones active
      _ ≤ ∑ i ∈ active, d i * d i := by
        apply Finset.sum_le_sum
        intro i hi
        have hdi : 0 < d i := Nat.pos_of_ne_zero (NeZero.ne (d i))
        nlinarith
      _ = 1 := hsum
  have hcard : active.card = 1 :=
    Nat.le_antisymm hcardLe (Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr hactive))
  obtain ⟨i0, hactiveEq⟩ := Finset.card_eq_one.mp hcard
  have hi0active : i0 ∈ active := by simp [hactiveEq]
  have hci0 : c i0 = 1 := (Finset.mem_filter.mp hi0active).2
  have hdi0sq : d i0 * d i0 = 1 := by simpa [hactiveEq] using hsum
  have hdi0 : d i0 = 1 := Nat.dvd_one.mp ⟨d i0, hdi0sq.symm⟩
  have havg0 : E (averagingIdempotent (G := G)) i0 = 1 := by
    rw [hc i0, hci0, hdi0]
    ext u v
    simp [Matrix.scalar_apply, Matrix.one_apply]
  have htriv0 (g : G) : E (MonoidAlgebra.single g 1) i0 = 1 := by
    have hmap := congrFun (congrArg E (single_mul_averagingIdempotent g)) i0
    rw [map_mul, Pi.mul_apply, havg0] at hmap
    simpa using hmap
  refine ⟨i0, ⟨hdi0, htriv0⟩, ?_⟩
  intro i hi
  have havgi : E (averagingIdempotent (G := G)) i = 1 := by
    rw [averagingIdempotent, groupSum, map_smul, map_sum]
    simp only [Pi.smul_apply, Finset.sum_apply]
    simp_rw [hi.2]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    simp [Fintype.card_ne_zero]
  have hci : c i = 1 := by
    letI : NeZero (d i) := hd i
    have hentry := congrFun₂ (hc i) 0 0
    rw [havgi] at hentry
    simpa [Matrix.scalar_apply, Matrix.one_apply] using hentry.symm
  have hiActive : i ∈ active := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hci⟩
  rw [hactiveEq] at hiActive
  simpa using hiActive

theorem block_trivial_of_one_at_nonidentity
    {G : Type*} [Group G] [Fintype G] [IsSimpleGroup G]
    {r : ℕ} (d : Fin r → ℕ)
    (E : ℂ[G] ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (i : Fin r) (g : G) (hg : g ≠ 1)
    (hone : E (MonoidAlgebra.single g 1) i = 1) :
    ∀ h : G, E (MonoidAlgebra.single h 1) i = 1 := by
  let ρ := blockMatrixRepresentation d E i
  have hgker : g ∈ ρ.ker := by
    apply MonoidHom.mem_ker.mpr
    exact hone
  have hker : ρ.ker = ⊤ :=
    ρ.normal_ker.eq_bot_or_eq_top.resolve_left fun hbot => by
      apply hg
      rw [← Subgroup.mem_bot, ← hbot]
      exact hgker
  intro h
  change ρ h = 1
  apply MonoidHom.mem_ker.mp
  rw [hker]
  exact Subgroup.mem_top h

theorem exists_nonidentity_classSize_prime_pow
    {G : Type*} [Group G] [Fintype G]
    {p q a b : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hqcard : q ∣ Fintype.card G)
    (hcard : Fintype.card G ∣ p ^ a * q ^ b) :
    ∃ g : G, g ≠ 1 ∧ ∃ k ≤ a, (conjugacyClassFinset g).card = p ^ k := by
  classical
  letI : Fact q.Prime := ⟨hq⟩
  let P : Sylow q G := default
  have hPne : (P : Subgroup G) ≠ ⊥ := by
    apply P.ne_bot_of_dvd_card
    simpa [Nat.card_eq_fintype_card] using hqcard
  letI : Nontrivial P := ((P : Subgroup G).nontrivial_iff_ne_bot).mpr hPne
  letI : Nontrivial (Subgroup.center P) := IsPGroup.center_nontrivial P.isPGroup'
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center P)
  let g : G := z.1.1
  have hg : g ≠ 1 := by
    intro h
    apply hz
    apply Subtype.ext
    apply Subtype.ext
    exact h
  refine ⟨g, hg, ?_⟩
  have hPcentral : (P : Subgroup G) ≤ Subgroup.centralizer {g} := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    have hcomm := (Subgroup.mem_center_iff.mp z.2) ⟨x, hx⟩
    exact congrArg Subtype.val hcomm.symm
  have hmP : (conjugacyClassFinset g).card ∣ P.index := by
    rw [card_conjugacyClassFinset_eq_index_centralizer]
    exact Subgroup.index_dvd_of_le hPcentral
  have hqm : ¬q ∣ (conjugacyClassFinset g).card := by
    intro hqclass
    exact P.not_dvd_index (hqclass.trans hmP)
  have hmtarget : (conjugacyClassFinset g).card ∣ p ^ a * q ^ b := by
    exact hmP.trans (P.index_dvd_card.trans (by
      simpa [Nat.card_eq_fintype_card] using hcard))
  have hmpow : (conjugacyClassFinset g).card ∣ p ^ a :=
    (hq.coprime_pow_of_not_dvd hqm).dvd_of_dvd_mul_right hmtarget
  exact eq_prime_pow_of_dvd_prime_pow hp hmpow

theorem false_of_simple_card_dvd_prime_pow_mul_prime_pow
    {G : Type*} [Group G] [Fintype G] [IsSimpleGroup G]
    {p q a b : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hqcard : q ∣ Fintype.card G)
    (hcard : Fintype.card G ∣ p ^ a * q ^ b)
    (hns : ¬IsSolvable G) : False := by
  classical
  obtain ⟨g, hg, k, hk, hclass⟩ :=
    exists_nonidentity_classSize_prime_pow hp hq hqcard hcard
  letI : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  letI : NeZero (Nat.card G : ℂ) := NeZero.charZero
  letI : IsSemisimpleRing ℂ[G] := inferInstance
  obtain ⟨r, d, hd, ⟨E⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ ℂ[G]
  obtain ⟨i0, hi0, hunique⟩ := exists_unique_trivial_block d hd E
  obtain ⟨K, hKfield, hKnumber, hKalgebra, iK, hlift⟩ := character_lift G
  letI : Field K := hKfield
  letI : NumberField K := hKnumber
  letI : Algebra ℚ K := hKalgebra
  have hliftBlock (i : Fin r) :
      ∃ x : K, iK x = Matrix.trace (E (MonoidAlgebra.single g 1) i) ∧
        IsIntegral ℤ x ∧ ∀ σ : K →+* ℂ, ‖σ x‖ ≤ d i := by
    obtain ⟨x, hx, hxInt, hxNorm⟩ := hlift
      (Fin (d i) → ℂ) inferInstance inferInstance inferInstance
      (blockRepresentation d E i) g
    refine ⟨x, ?_, hxInt, ?_⟩
    · calc
        iK x = LinearMap.trace ℂ (Fin (d i) → ℂ)
            (blockRepresentation d E i g) := hx
        _ = Matrix.trace (E (MonoidAlgebra.single g 1) i) := by
          change LinearMap.trace ℂ (Fin (d i) → ℂ)
            (E (MonoidAlgebra.single g 1) i).toLin' = _
          exact Matrix.trace_toLin'_eq _
    · intro σ
      simpa only [Module.finrank_pi, Fintype.card_fin] using hxNorm σ
  choose x hx hxInt hxNorm using hliftBlock
  have hclassify (i : Fin r) (hpdi : ¬p ∣ d i) :
      x i = 0 ∨ (i = i0 ∧ x i = 1) := by
    have hcop : Nat.Coprime (conjugacyClassFinset g).card (d i) := by
      rw [hclass]
      exact (hp.coprime_pow_of_not_dvd hpdi).symm
    rcases block_trace_eq_zero_or_eq_scalar_of_coprime iK d hd E g i (x i)
      (hx i) (hxInt i) (hxNorm i) hcop with hzero | hscalar
    · left
      apply iK.injective
      calc
        iK (x i) = Matrix.trace (E (MonoidAlgebra.single g 1) i) := hx i
        _ = 0 := hzero
        _ = iK 0 := (map_zero iK).symm
    · obtain ⟨hdi, hone⟩ :=
        block_is_one_dimensional_and_trivial_of_scalar_at_nonidentity
          d hd E i g hg hns ⟨_, hscalar⟩
      have htriv := block_trivial_of_one_at_nonidentity d E i g hg hone
      have hii0 : i = i0 := hunique i ⟨hdi, htriv⟩
      right
      refine ⟨hii0, ?_⟩
      apply iK.injective
      calc
        iK (x i) = Matrix.trace (E (MonoidAlgebra.single g 1) i) := hx i
        _ = 1 := by
          rw [hone, hdi]
          simp [Matrix.trace, Matrix.diag]
        _ = iK 1 := (map_one iK).symm
  have hxi0 : x i0 = 1 := by
    apply iK.injective
    calc
      iK (x i0) = Matrix.trace (E (MonoidAlgebra.single g 1) i0) := hx i0
      _ = 1 := by
        rw [hi0.2 g, hi0.1]
        simp [Matrix.trace, Matrix.diag]
      _ = iK 1 := (map_one iK).symm
  have hsumC : (∑ i, (d i : ℂ) * iK (x i)) = 0 := by
    simp_rw [hx]
    calc
      (∑ i, (d i : ℂ) * Matrix.trace (E (MonoidAlgebra.single g 1) i)) =
          LinearMap.trace ℂ (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
            (Algebra.lmul ℂ (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
              (E (MonoidAlgebra.single g 1))) := (trace_lmul_pi_matrix d _).symm
      _ = LinearMap.trace ℂ ℂ[G]
          (Algebra.lmul ℂ ℂ[G] (MonoidAlgebra.single g 1)) :=
        trace_lmul_algEquiv E _
      _ = 0 := trace_lmul_single_eq_zero hg
  have hsumK : (∑ i, (d i : K) * x i) = 0 := by
    apply iK.injective
    change iK (∑ i, (d i : K) * x i) = iK 0
    rw [map_sum, map_zero]
    simp only [map_mul, map_natCast]
    exact hsumC
  let divisible : Finset (Fin r) := Finset.univ.filter fun i => p ∣ d i
  let nondivisible : Finset (Fin r) := Finset.univ.filter fun i => ¬p ∣ d i
  have hi0nondivisible : i0 ∈ nondivisible := by
    simp [nondivisible, hi0.1, hp.not_dvd_one]
  have hnondivisible :
      (∑ i ∈ nondivisible, (d i : K) * x i) = 1 := by
    rw [Finset.sum_eq_single i0]
    · simp [hi0.1, hxi0]
    · intro i hi hii0
      have hpdi : ¬p ∣ d i := (Finset.mem_filter.mp hi).2
      rcases hclassify i hpdi with hzero | hone
      · simp [hzero]
      · exact (hii0 hone.1).elim
    · exact fun h => (h hi0nondivisible).elim
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i : Fin r => p ∣ d i) (fun i => (d i : K) * x i)
  have hdivisible : (∑ i ∈ divisible, (d i : K) * x i) = -1 := by
    change (∑ i ∈ divisible, (d i : K) * x i) +
      (∑ i ∈ nondivisible, (d i : K) * x i) =
        ∑ i, (d i : K) * x i at hsplit
    rw [hnondivisible, hsumK] at hsplit
    linear_combination hsplit
  let y : K := ∑ i ∈ divisible, ((d i / p : ℕ) : K) * x i
  have hpy : (p : K) * y = -1 := by
    rw [show (p : K) * y = ∑ i ∈ divisible, (d i : K) * x i by
      dsimp [y]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hpdi : p ∣ d i := (Finset.mem_filter.mp hi).2
      rw [← mul_assoc, ← Nat.cast_mul, Nat.mul_div_cancel' hpdi]]
    exact hdivisible
  have hyInt : IsIntegral ℤ y := by
    dsimp [y]
    apply IsIntegral.sum
    intro i hi
    simpa [nsmul_eq_mul] using (hxInt i).nsmul (d i / p)
  have hpK : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  let qrat : ℚ := -(1 / (p : ℚ))
  have hydiv : y = (-1 : K) / (p : K) := by
    apply (eq_div_iff hpK).mpr
    simpa [mul_comm] using hpy
  have hyq : y = (qrat : K) := by
    rw [hydiv]
    simp [qrat]
    ring
  obtain ⟨z : ℤ, hyz⟩ :=
    hyInt.exists_int_iff_exists_rat.mp ⟨qrat, hyq⟩
  have hqzK : (qrat : K) = (z : K) := hyq.symm.trans hyz
  have hqz : qrat = (z : ℚ) := by
    apply (algebraMap ℚ K).injective
    simpa using hqzK
  have hmulQ : (p : ℚ) * (z : ℚ) = -1 := by
    rw [← hqz]
    simp [qrat, hp.ne_zero]
  have hmulZ : (p : ℤ) * z = -1 := by exact_mod_cast hmulQ
  have habs := congrArg Int.natAbs hmulZ
  apply hp.not_dvd_one
  refine ⟨z.natAbs, ?_⟩
  simpa [Int.natAbs_mul] using habs.symm

theorem isSolvable_of_card_eq_prime_pow {G : Type*} [Group G] [Fintype G]
    {p n : ℕ} (hp : Nat.Prime p) (hcard : Fintype.card G = p ^ n) :
    IsSolvable G := by
  letI : Fact p.Prime := ⟨hp⟩
  have hP : IsPGroup p G := IsPGroup.of_card (by simpa using hcard)
  letI : Group.IsNilpotent G := hP.isNilpotent
  infer_instance

theorem isSolvable_of_card_dvd_prime_pow_mul_prime_pow
    {G : Type*} [Group G] [Fintype G]
    {p q a b : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hcard : Fintype.card G ∣ p ^ a * q ^ b) : IsSolvable G := by
  classical
  induction hGcard : Fintype.card G using Nat.strong_induction_on generalizing G with
  | h n ih =>
      by_cases hpG : p ∣ Fintype.card G
      · by_cases hqG : q ∣ Fintype.card G
        · by_contra hns
          letI : Nontrivial G := not_subsingleton_iff_nontrivial.mp fun hsub => by
            letI : Subsingleton G := hsub
            exact hns inferInstance
          by_cases hsimple :
              ∀ H : Subgroup G, H.Normal → H = ⊥ ∨ H = ⊤
          · letI : IsSimpleGroup G := ⟨hsimple⟩
            exact false_of_simple_card_dvd_prime_pow_mul_prime_pow
              hp hq hqG hcard hns
          · push Not at hsimple
            obtain ⟨H, hHnormal, hHbot, hHtop⟩ := hsimple
            letI : H.Normal := hHnormal
            have hHlt : Fintype.card H < Fintype.card G := by
              rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
              calc
                Nat.card H < Nat.card H * H.index :=
                  lt_mul_of_one_lt_right Nat.card_pos
                    (Subgroup.one_lt_index_of_ne_top hHtop)
                _ = Nat.card G := H.card_mul_index
            have hQlt : Fintype.card (G ⧸ H) < Fintype.card G := by
              rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
              calc
                Nat.card (G ⧸ H) = H.index := H.index_eq_card.symm
                _ < Nat.card H * H.index :=
                  lt_mul_of_one_lt_left (H.index_eq_card ▸ Nat.card_pos)
                    ((Subgroup.one_lt_card_iff_ne_bot H).mpr hHbot)
                _ = Nat.card G := H.card_mul_index
            have hHcard : Fintype.card H ∣ p ^ a * q ^ b := by
              have hHG : Fintype.card H ∣ Fintype.card G := by
                simpa [Nat.card_eq_fintype_card] using H.card_subgroup_dvd_card
              exact hHG.trans hcard
            have hQcard : Fintype.card (G ⧸ H) ∣ p ^ a * q ^ b := by
              have hQG : Fintype.card (G ⧸ H) ∣ Fintype.card G := by
                simpa [Nat.card_eq_fintype_card] using
                  Subgroup.card_dvd_of_surjective (QuotientGroup.mk' H)
                    (QuotientGroup.mk'_surjective H)
              exact hQG.trans hcard
            letI : IsSolvable H :=
              ih (Fintype.card H) (hGcard ▸ hHlt) hHcard rfl
            letI : IsSolvable (G ⧸ H) :=
              ih (Fintype.card (G ⧸ H)) (hGcard ▸ hQlt) hQcard rfl
            exact hns (solvable_of_ker_le_range H.subtype (QuotientGroup.mk' H) (by
              rw [QuotientGroup.ker_mk', H.range_subtype]))
        · have hpow : Fintype.card G ∣ p ^ a :=
            (hq.coprime_pow_of_not_dvd hqG).dvd_of_dvd_mul_right hcard
          obtain ⟨k, hk, hcardEq⟩ := eq_prime_pow_of_dvd_prime_pow hp hpow
          exact isSolvable_of_card_eq_prime_pow hp hcardEq
      · have hpow : Fintype.card G ∣ q ^ b :=
          (hp.coprime_pow_of_not_dvd hpG).dvd_of_dvd_mul_left hcard
        obtain ⟨k, hk, hcardEq⟩ := eq_prime_pow_of_dvd_prime_pow hq hpow
        exact isSolvable_of_card_eq_prime_pow hq hcardEq

end

end BurnsideCharacter
