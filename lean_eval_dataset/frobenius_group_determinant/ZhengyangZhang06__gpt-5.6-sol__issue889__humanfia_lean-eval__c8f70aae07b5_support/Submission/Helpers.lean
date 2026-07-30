import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Algebra.Central.Matrix
import Mathlib.Algebra.Algebra.Subalgebra.Pi
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.Algebra.Group.ConjFinite
import Lean.Elab.Tactic.Omega

open MvPolynomial Matrix

namespace Scratch

open scoped Function
open Module

theorem irreducible_rename_of_injective
    {R σ τ : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [Fintype σ] [DecidableEq τ] {p : MvPolynomial σ R}
    (hp : Irreducible p) (f : σ → τ) (hf : Function.Injective f) :
    Irreducible (MvPolynomial.rename f p) := by
  classical
  let emb : σ ↪ τ := ⟨f, hf⟩
  let s : Set τ := Set.range emb
  let ρ := (sᶜ : Set τ)
  let e : ρ ⊕ σ ≃ τ :=
    (Equiv.sumCongr (Equiv.refl ρ) emb.toEquivRange).trans
      ((Equiv.sumComm ρ s).trans (Equiv.Set.sumCompl s))
  have he (x : σ) : e (Sum.inr x) = f x := by
    change (Equiv.Set.sumCompl s)
      (Sum.inl (emb.toEquivRange x)) = f x
    rfl
  have he' : e ∘ Sum.inr = f := funext he
  have hp' : Prime p := UniqueFactorizationMonoid.irreducible_iff_prime.mp hp
  have hC : Prime (MvPolynomial.C p : MvPolynomial ρ (MvPolynomial σ R)) :=
    (MvPolynomial.prime_C_iff ρ).mpr hp'
  have hCirr : Irreducible
      (MvPolynomial.C p : MvPolynomial ρ (MvPolynomial σ R)) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mpr hC
  have hinr : Irreducible
      (MvPolynomial.rename Sum.inr p : MvPolynomial (ρ ⊕ σ) R) := by
    have hsum : (MvPolynomial.sumAlgEquiv R ρ σ)
        (MvPolynomial.rename Sum.inr p) = MvPolynomial.C p := by
      exact DFunLike.congr_fun
        (MvPolynomial.sumAlgEquiv_comp_rename_inr R ρ σ) p
    apply (MulEquiv.irreducible_iff
      (MvPolynomial.sumAlgEquiv R ρ σ).toMulEquiv).mp
    change Irreducible ((MvPolynomial.sumAlgEquiv R ρ σ)
      (MvPolynomial.rename Sum.inr p))
    rw [hsum]
    exact hCirr
  have hrename : MvPolynomial.rename e (MvPolynomial.rename Sum.inr p) =
      MvPolynomial.rename f p := by
    rw [MvPolynomial.rename_rename, he']
  rw [← hrename]
  exact (MulEquiv.irreducible_iff
    (MvPolynomial.renameEquiv R e).toMulEquiv).mpr hinr

noncomputable abbrev genericDet (K : Type*) [CommRing K] (n : ℕ) :
    MvPolynomial (Fin n × Fin n) K :=
  Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) K)

lemma degreeOf_genericDet_le_one (K : Type*) [CommRing K] [IsDomain K] (n : ℕ) :
    (genericDet K n.succ).degreeOf ((0, 0) : Fin n.succ × Fin n.succ) ≤ 1 := by
  classical
  rw [genericDet, Matrix.det_apply']
  refine (MvPolynomial.degreeOf_sum_le _ _ _).trans ?_
  apply Finset.sup_le
  intro σ hσ
  refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
  calc
    _ ≤ 0 + 1 := Nat.add_le_add (by
      rw [show (↑↑(Equiv.Perm.sign σ) :
          MvPolynomial (Fin n.succ × Fin n.succ) K) =
          MvPolynomial.C ((↑(Equiv.Perm.sign σ) : ℤ) : K) by rfl,
        MvPolynomial.degreeOf_C]) (by
        refine (MvPolynomial.degreeOf_prod_le _ _ _).trans ?_
        simp only [Matrix.mvPolynomialX_apply]
        have hsum :
            (∑ i : Fin n.succ,
              (MvPolynomial.X (σ i, i) : MvPolynomial (Fin n.succ × Fin n.succ) K).degreeOf
                ((0, 0) : Fin n.succ × Fin n.succ)) =
              (MvPolynomial.X (σ 0, 0) : MvPolynomial (Fin n.succ × Fin n.succ) K).degreeOf
                ((0, 0) : Fin n.succ × Fin n.succ) := by
          apply Finset.sum_eq_single 0
          · intro i hi hi0
            rw [MvPolynomial.degreeOf_X_of_ne]
            exact fun h => hi0 (congr_arg Prod.snd h).symm
          · simp
        rw [hsum]
        rw [MvPolynomial.degreeOf_X]
        split <;> omega)
    _ = 1 := by simp

section GenericDetStep

variable (K : Type*) [CommRing K] [IsDomain K]

abbrev StepIndex (n : ℕ) := Fin (n + 2)
abbrev StepVar (n : ℕ) := StepIndex n × StepIndex n
abbrev StepRest (n : ℕ) := {x : StepVar n // x ≠ ((0, 0) : StepVar n)}

noncomputable def splitEquiv (n : ℕ) :
    MvPolynomial (StepVar n) K ≃+* Polynomial (MvPolynomial (StepRest n) K) :=
  (MvPolynomial.renameEquiv K
      (Equiv.optionSubtypeNe ((0, 0) : StepVar n)).symm).toRingEquiv.trans
    (MvPolynomial.optionEquivLeft K (StepRest n)).toRingEquiv

noncomputable def splitHom (n : ℕ) :
    MvPolynomial (StepVar n) K →+* Polynomial (MvPolynomial (StepRest n) K) :=
  (splitEquiv K n).toRingHom

omit [IsDomain K] in
lemma splitHom_X_self (n : ℕ) :
    splitHom K n (MvPolynomial.X ((0, 0) : StepVar n)) = Polynomial.X := by
  simp [splitHom, splitEquiv]

omit [IsDomain K] in
lemma splitHom_X_ne (n : ℕ) (x : StepVar n) (hx : x ≠ ((0, 0) : StepVar n)) :
    splitHom K n (MvPolynomial.X x) = Polynomial.C (MvPolynomial.X ⟨x, hx⟩) := by
  simp [splitHom, splitEquiv, Equiv.optionSubtypeNe_symm_of_ne hx]

noncomputable def minorPoly (n : ℕ) (j : StepIndex n) : MvPolynomial (StepRest n) K :=
  Matrix.det fun i k : Fin (n + 1) =>
    MvPolynomial.X ⟨(i.succ, j.succAbove k), by
      intro h
      exact Fin.succ_ne_zero i (congr_arg Prod.fst h)⟩

omit [IsDomain K] in
lemma splitHom_minor (n : ℕ) (j : StepIndex n) :
    splitHom K n
        (Matrix.det ((Matrix.mvPolynomialX (StepIndex n) (StepIndex n) K).submatrix
          Fin.succ j.succAbove)) =
      Polynomial.C (minorPoly K n j) := by
  rw [RingHom.map_det (splitHom K n), minorPoly,
    RingHom.map_det Polynomial.C]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i k
  change splitHom K n (MvPolynomial.X (i.succ, j.succAbove k)) =
    Polynomial.C (MvPolynomial.X ⟨(i.succ, j.succAbove k), _⟩)
  rw [splitHom_X_ne]

noncomputable def splitDet (n : ℕ) : Polynomial (MvPolynomial (StepRest n) K) :=
  splitHom K n (genericDet K (n + 2))

lemma splitDet_coeff_one (n : ℕ) :
    (splitDet K n).coeff 1 = minorPoly K n 0 := by
  rw [splitDet, genericDet, Matrix.det_succ_row_zero]
  simp only [map_sum, map_mul, map_pow, map_neg, map_one]
  change Polynomial.lcoeff (MvPolynomial (StepRest n) K) 1
    (∑ x : StepIndex n,
      (-1) ^ (x : ℕ) * splitHom K n
        (Matrix.mvPolynomialX (StepIndex n) (StepIndex n) K 0 x) *
        splitHom K n (Matrix.det
          ((Matrix.mvPolynomialX (StepIndex n) (StepIndex n) K).submatrix
            Fin.succ x.succAbove))) = minorPoly K n 0
  rw [map_sum]
  calc
    _ = (Polynomial.lcoeff (MvPolynomial (StepRest n) K) 1)
        ((-1) ^ (0 : ℕ) * splitHom K n
          (Matrix.mvPolynomialX (StepIndex n) (StepIndex n) K 0 0) *
          splitHom K n (Matrix.det
            ((Matrix.mvPolynomialX (StepIndex n) (StepIndex n) K).submatrix
              Fin.succ (0 : StepIndex n).succAbove))) := by
      apply Finset.sum_eq_single 0
      · intro j hj hj0
        simp only [Matrix.mvPolynomialX_apply]
        rw [splitHom_X_ne]
        · rw [splitHom_minor]
          have hc : (((-1) ^ (j : ℕ) :
              Polynomial (MvPolynomial (StepRest n) K))).coeff 1 = 0 := by
            apply Polynomial.coeff_eq_zero_of_natDegree_lt
            have hu : IsUnit ((-1) ^ (j : ℕ) :
                Polynomial (MvPolynomial (StepRest n) K)) :=
              (isUnit_one : IsUnit
                (1 : Polynomial (MvPolynomial (StepRest n) K))).neg.pow (j : ℕ)
            rw [Polynomial.natDegree_eq_zero_of_isUnit hu]
            decide
          simp [hc]
        · exact fun h => hj0 (congr_arg Prod.snd h)
      · simp
    _ = minorPoly K n 0 := by
      simp only [Matrix.mvPolynomialX_apply]
      rw [splitHom_X_self, splitHom_minor]
      simp

def minorEmbedding (n : ℕ) :
    (Fin (n + 1) × Fin (n + 1)) → StepRest n :=
  fun x => ⟨(x.1.succ, x.2.succ), by
    intro h
    exact Fin.succ_ne_zero x.1 (congr_arg Prod.fst h)⟩

lemma minorEmbedding_injective (n : ℕ) :
    Function.Injective (minorEmbedding n) := by
  intro x y h
  apply Prod.ext
  · exact (Fin.succ_injective _)
      (congr_arg (fun z : StepRest n => z.1.1) h)
  · exact (Fin.succ_injective _)
      (congr_arg (fun z : StepRest n => z.1.2) h)

omit [IsDomain K] in
lemma minorPoly_zero_eq_rename (n : ℕ) :
    minorPoly K n 0 =
      MvPolynomial.rename (minorEmbedding n) (genericDet K (n + 1)) := by
  symm
  calc
    MvPolynomial.rename (minorEmbedding n) (genericDet K (n + 1)) =
        Matrix.det ((MvPolynomial.rename (minorEmbedding n)).mapMatrix
          (Matrix.mvPolynomialX (Fin (n + 1)) (Fin (n + 1)) K)) := by
      rw [genericDet]
      exact RingHom.map_det
        (MvPolynomial.rename (R := K) (minorEmbedding n)).toRingHom _
    _ = minorPoly K n 0 := by
      rw [minorPoly]
      apply congrArg Matrix.det
      apply Matrix.ext
      intro i j
      simp [minorEmbedding]

lemma irreducible_minorPoly_zero (n : ℕ)
    [UniqueFactorizationMonoid K]
    (hdet : Irreducible (genericDet K (n + 1))) :
    Irreducible (minorPoly K n 0) := by
  rw [minorPoly_zero_eq_rename]
  exact irreducible_rename_of_injective hdet (minorEmbedding n)
    (minorEmbedding_injective n)

noncomputable def swapPerm (n : ℕ) : Equiv.Perm (StepIndex n) :=
  Equiv.swap 0 1

noncomputable def swapMatrix (n : ℕ) : Matrix (StepIndex n) (StepIndex n) K :=
  (swapPerm n).permMatrix K

noncomputable def swapAssignment (n : ℕ) : StepRest n → K :=
  fun x => swapMatrix K n x.1.1 x.1.2

lemma eval_minorPoly_zero_swap (n : ℕ) :
    MvPolynomial.eval (swapAssignment K n) (minorPoly K n 0) = 0 := by
  classical
  rw [minorPoly, RingHom.map_det]
  apply Matrix.det_eq_zero_of_column_eq_zero 0
  intro i
  simp [swapAssignment, swapMatrix, swapPerm, Equiv.swap_apply_def]
  by_cases hi : i.succ = (1 : StepIndex n) <;> simp [hi]

lemma swapMatrix_det_ne_zero (n : ℕ) : Matrix.det (swapMatrix K n) ≠ 0 := by
  classical
  rw [swapMatrix, Matrix.det_permutation]
  exact (Equiv.Perm.sign (swapPerm n)).isUnit.map (Int.castRingHom K) |>.ne_zero

omit [IsDomain K] in
lemma eval_splitDet_coeff_zero_swap (n : ℕ) :
    MvPolynomial.eval (swapAssignment K n) ((splitDet K n).coeff 0) =
      Matrix.det (swapMatrix K n) := by
  classical
  let e := Equiv.optionSubtypeNe ((0, 0) : StepVar n)
  have hassignment :
      (fun x : StepVar n => Option.elim (e.symm x) 0 (swapAssignment K n)) =
        fun x => swapMatrix K n x.1 x.2 := by
    funext x
    by_cases hx : x = ((0, 0) : StepVar n)
    · subst x
      simp [e, swapMatrix, swapPerm]
    · simp [e, Equiv.optionSubtypeNe_symm_of_ne hx, swapAssignment]
  have hassignment' :
      ((fun x : Option (StepRest n) => Option.elim x 0 (swapAssignment K n)) ∘ e.symm) =
        fun x => swapMatrix K n x.1 x.2 := by
    simpa [Function.comp_def] using hassignment
  have hevaldet :
      MvPolynomial.eval (fun x : StepVar n => swapMatrix K n x.1 x.2)
          (genericDet K (n + 2)) = Matrix.det (swapMatrix K n) := by
    rw [genericDet]
    calc
      _ = Matrix.det ((MvPolynomial.eval
          (fun x : StepVar n => swapMatrix K n x.1 x.2)).mapMatrix
            (Matrix.mvPolynomialX (StepIndex n) (StepIndex n) K)) := by
        exact RingHom.map_det
          (MvPolynomial.eval
            (fun x : StepVar n => swapMatrix K n x.1 x.2)) _
      _ = Matrix.det (swapMatrix K n) := by
        apply congrArg Matrix.det
        apply Matrix.ext
        intro i j
        simp
  have h := MvPolynomial.optionEquivLeft_elim_eval K (StepRest n)
    (swapAssignment K n) 0
    (MvPolynomial.rename e.symm (genericDet K (n + 2)))
  rw [MvPolynomial.eval_rename, hassignment', hevaldet] at h
  simpa [splitDet, splitHom, splitEquiv, e, Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.eval_zero] using h.symm

lemma splitDet_natDegree_le_one (n : ℕ) :
    (splitDet K n).natDegree ≤ 1 := by
  change ((MvPolynomial.optionEquivLeft K (StepRest n))
    (MvPolynomial.rename
      (Equiv.optionSubtypeNe ((0, 0) : StepVar n)).symm
      (genericDet K (n + 2)))).natDegree ≤ 1
  rw [← MvPolynomial.degreeOf_eq_natDegree
    ((0, 0) : StepVar n) (genericDet K (n + 2))]
  exact degreeOf_genericDet_le_one K (n + 1)

lemma splitDet_degree_eq_one (n : ℕ)
    [UniqueFactorizationMonoid K]
    (hdet : Irreducible (genericDet K (n + 1))) :
    (splitDet K n).degree = 1 := by
  have hminor := irreducible_minorPoly_zero K n hdet
  have hcoeff : (splitDet K n).coeff 1 ≠ 0 := by
    rw [splitDet_coeff_one]
    exact hminor.ne_zero
  have hnat : (splitDet K n).natDegree = 1 :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      (splitDet_natDegree_le_one K n) hcoeff
  have hne : splitDet K n ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.coeff_zero] at hcoeff
    exact hcoeff rfl
  simpa [hnat] using Polynomial.degree_eq_natDegree hne

lemma minorPoly_zero_not_dvd_coeff_zero (n : ℕ) :
    ¬ minorPoly K n 0 ∣ (splitDet K n).coeff 0 := by
  intro hdiv
  have hzero :
      MvPolynomial.eval (swapAssignment K n) ((splitDet K n).coeff 0) = 0 := by
    obtain ⟨a, ha⟩ := hdiv
    rw [ha, map_mul, eval_minorPoly_zero_swap, zero_mul]
  rw [eval_splitDet_coeff_zero_swap] at hzero
  exact swapMatrix_det_ne_zero K n hzero

lemma splitDet_coeff_isRelPrime (n : ℕ)
    [UniqueFactorizationMonoid K]
    (hdet : Irreducible (genericDet K (n + 1))) :
    IsRelPrime ((splitDet K n).coeff 0) ((splitDet K n).coeff 1) := by
  have hminor := irreducible_minorPoly_zero K n hdet
  apply WfDvdMonoid.isRelPrime_of_no_irreducible_factors
  · intro hzero
    have : minorPoly K n 0 = 0 := by
      rw [← splitDet_coeff_one]
      exact hzero.2
    exact hminor.ne_zero this
  · intro z hz hz0 hz1
    rw [splitDet_coeff_one] at hz1
    have hassoc : Associated z (minorPoly K n 0) :=
      (hz.dvd_irreducible_iff_associated hminor).mp hz1
    exact minorPoly_zero_not_dvd_coeff_zero K n (hassoc.dvd'.trans hz0)

lemma irreducible_splitDet (n : ℕ)
    [UniqueFactorizationMonoid K]
    (hdet : Irreducible (genericDet K (n + 1))) :
    Irreducible (splitDet K n) :=
  Polynomial.irreducible_of_degree_eq_one_of_isRelPrime_coeff
    (splitDet_degree_eq_one K n hdet) (splitDet_coeff_isRelPrime K n hdet)

end GenericDetStep

theorem irreducible_genericDet_succ (K : Type*) [Field K] (n : ℕ) :
    Irreducible (genericDet K (n + 1)) := by
  induction n with
  | zero =>
      have hdet : genericDet K 1 =
          MvPolynomial.X ((0, 0) : Fin 1 × Fin 1) := by
        simp [genericDet]
      rw [hdet]
      exact (MvPolynomial.X_prime (R := K)
        (i := ((0, 0) : Fin 1 × Fin 1))).irreducible
  | succ n ih =>
      have hsplit : Irreducible (splitDet K n) :=
        irreducible_splitDet K n ih
      exact (MulEquiv.irreducible_iff (splitEquiv K n).toMulEquiv).mp hsplit

lemma genericDet_isHomogeneous (K : Type*) [CommRing K] (n : ℕ) :
    (genericDet K n).IsHomogeneous n := by
  classical
  rw [genericDet, Matrix.det_apply']
  apply MvPolynomial.IsHomogeneous.sum
  intro σ hσ
  rw [show ((↑(σ.sign) : ℤ) :
      MvPolynomial (Fin n × Fin n) K) =
      MvPolynomial.C (((↑(σ.sign) : ℤ) : K)) by rfl]
  have hprod :
      ( (∏ i : Fin n,
          Matrix.mvPolynomialX (Fin n) (Fin n) K (σ i) i) :
        MvPolynomial (Fin n × Fin n) K).IsHomogeneous n := by
    convert MvPolynomial.IsHomogeneous.prod Finset.univ
      (fun i : Fin n =>
        MvPolynomial.X (σ i, i) : Fin n → MvPolynomial (Fin n × Fin n) K)
      (fun _ => 1) (by
        intro i hi
        exact MvPolynomial.isHomogeneous_X K (σ i, i)) using 1 <;>
      simp [Matrix.mvPolynomialX_apply]
  simpa only [zero_add] using
    (MvPolynomial.isHomogeneous_C
      (Fin n × Fin n) ((↑(σ.sign) : ℤ) : K)).mul hprod

section BasisPolynomialEquiv

variable {K M ι κ : Type*} [Field K] [AddCommGroup M] [Module K M]
  [Fintype ι] [Fintype κ]

noncomputable def basisPolynomialEquiv (b : Basis ι K M) (c : Basis κ K M) :
    MvPolynomial ι K ≃ₐ[K] MvPolynomial κ K := by
  classical
  exact (SymmetricAlgebra.equivMvPolynomial b.dualBasis).symm.trans
    (SymmetricAlgebra.equivMvPolynomial c.dualBasis)

lemma eval_basisPolynomialEquiv_X (b : Basis ι K M) (c : Basis κ K M)
    (x : κ → K) (i : ι) :
    MvPolynomial.eval x (basisPolynomialEquiv b c (MvPolynomial.X i)) =
      b.repr (c.equivFun.symm x) i := by
  classical
  let L : Module.Dual K M →ₗ[K] K :=
    (MvPolynomial.aeval x).toLinearMap.comp
      ((SymmetricAlgebra.equivMvPolynomial c.dualBasis).toLinearMap.comp
        (SymmetricAlgebra.ι K (Module.Dual K M)))
  let R : Module.Dual K M →ₗ[K] K :=
    Module.Dual.eval K M (c.equivFun.symm x)
  have hLR : L = R := by
    apply c.dualBasis.ext
    intro j
    change L (c.dualBasis j) = R (c.dualBasis j)
    change MvPolynomial.eval x
        ((SymmetricAlgebra.equivMvPolynomial c.dualBasis)
          (SymmetricAlgebra.ι K (Module.Dual K M) (c.dualBasis j))) =
      c.dualBasis j (c.equivFun.symm x)
    rw [SymmetricAlgebra.equivMvPolynomial_ι_apply]
    simp [Finsupp.single_apply, mul_ite]
  rw [basisPolynomialEquiv, AlgEquiv.trans_apply,
    SymmetricAlgebra.equivMvPolynomial_symm_X]
  change L (b.dualBasis i) = _
  rw [hLR]
  exact Basis.dualBasis_apply b i (c.equivFun.symm x)

lemma eval_basisPolynomialEquiv (b : Basis ι K M) (c : Basis κ K M)
    (x : κ → K) (p : MvPolynomial ι K) :
    MvPolynomial.eval x (basisPolynomialEquiv b c p) =
      MvPolynomial.eval (fun i => b.repr (c.equivFun.symm x) i) p := by
  classical
  have hhom : (MvPolynomial.aeval x).comp (basisPolynomialEquiv b c).toAlgHom =
      MvPolynomial.aeval (fun i => b.repr (c.equivFun.symm x) i) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [eval_basisPolynomialEquiv_X]
  exact DFunLike.congr_fun hhom p

lemma basisPolynomialEquiv_X_eq_sum [Infinite K]
    (b : Basis ι K M) (c : Basis κ K M) (i : ι) :
    basisPolynomialEquiv b c (MvPolynomial.X i) =
      ∑ j : κ, MvPolynomial.C (b.repr (c j) i) * MvPolynomial.X j := by
  classical
  apply MvPolynomial.funext
  intro x
  rw [eval_basisPolynomialEquiv_X]
  simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  rw [Basis.equivFun_symm_apply, map_sum]
  simp [mul_comm]

lemma basisPolynomialEquiv_X_isHomogeneous [Infinite K]
    (b : Basis ι K M) (c : Basis κ K M) (i : ι) :
    (basisPolynomialEquiv b c (MvPolynomial.X i)).IsHomogeneous 1 := by
  classical
  rw [basisPolynomialEquiv_X_eq_sum]
  apply MvPolynomial.IsHomogeneous.sum
  intro j hj
  exact (MvPolynomial.isHomogeneous_X K j).C_mul _

lemma basisPolynomialEquiv_isHomogeneous [Infinite K]
    (b : Basis ι K M) (c : Basis κ K M) {p : MvPolynomial ι K} {d : ℕ}
    (hp : p.IsHomogeneous d) :
    (basisPolynomialEquiv b c p).IsHomogeneous d := by
  classical
  have heq : (basisPolynomialEquiv b c).toAlgHom =
      MvPolynomial.aeval (fun i => basisPolynomialEquiv b c (MvPolynomial.X i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  have hsubst := hp.aeval
    (fun i => basisPolynomialEquiv b c (MvPolynomial.X i))
    (basisPolynomialEquiv_X_isHomogeneous b c)
  have happ : basisPolynomialEquiv b c p =
      MvPolynomial.aeval
        (fun i => basisPolynomialEquiv b c (MvPolynomial.X i)) p :=
    DFunLike.congr_fun heq p
  rw [← happ] at hsubst
  simpa only [one_mul] using hsubst

end BasisPolynomialEquiv

section MatrixLeftMulDet

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

lemma det_mulVecLin (A : Matrix n n K) : A.mulVecLin.det = A.det := by
  classical
  rw [← LinearMap.det_toMatrix (Pi.basisFun K n)]
  exact congrArg Matrix.det (LinearMap.toMatrix'_toLin' A)

lemma det_lmul_matrix (A : Matrix n n K) :
    (Algebra.lmul K (Matrix n n K) A).det = A.det ^ Fintype.card n := by
  classical
  let e := Matrix.transposeLinearEquiv n n K K
  let g : Matrix n n K →ₗ[K] Matrix n n K :=
    LinearMap.pi fun j => A.mulVecLin.comp (LinearMap.proj j)
  have hconj : e.toLinearMap.comp
      ((Algebra.lmul K (Matrix n n K) A).comp e.symm.toLinearMap) = g := by
    ext B i j
    change (∑ x, A j x * B i x) = A.mulVecLin (B i) j
    rfl
  rw [← LinearMap.det_conj (Algebra.lmul K (Matrix n n K) A) e,
    hconj]
  change (LinearMap.pi
    (fun j => A.mulVecLin.comp (LinearMap.proj j))).det = _
  rw [LinearMap.det_pi]
  simp [det_mulVecLin, Finset.prod_const]

end MatrixLeftMulDet

section DependentBlockDiagonal

variable {K ι : Type*} [CommRing K] [Fintype ι] [LinearOrder ι]
  {m : ι → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]

def sigmaFiberEquiv (k : ι) : {x : Σ i, m i // x.1 = k} ≃ m k where
  toFun x := _root_.cast (congrArg m x.property) x.1.2
  invFun x := ⟨⟨k, x⟩, rfl⟩
  left_inv x := by
    rcases x with ⟨⟨i, x⟩, h⟩
    change i = k at h
    cases h
    rfl
  right_inv x := rfl

lemma det_blockDiagonal' (M : ∀ i, Matrix (m i) (m i) K) :
    Matrix.det (Matrix.blockDiagonal' M) = ∏ i, Matrix.det (M i) := by
  classical
  rw [(Matrix.blockTriangular_blockDiagonal' M).det_fintype]
  apply Finset.prod_congr rfl
  intro k hk
  let e := sigmaFiberEquiv (m := m) k
  calc
    Matrix.det ((Matrix.blockDiagonal' M).toSquareBlock Sigma.fst k) =
        Matrix.det (Matrix.reindex e e
          ((Matrix.blockDiagonal' M).toSquareBlock Sigma.fst k)) :=
      (Matrix.det_reindex_self e _).symm
    _ = Matrix.det (M k) := by
      apply congrArg Matrix.det
      apply Matrix.ext
      intro i j
      simp [e, sigmaFiberEquiv, Matrix.reindex_apply, Matrix.toSquareBlock_def]

end DependentBlockDiagonal

section DependentPiDet

variable {K ι : Type*} [CommRing K] [Fintype ι] [LinearOrder ι]
  {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
  [∀ i, Module.Free K (M i)] [∀ i, Module.Finite K (M i)]

lemma det_pi_dependent (f : ∀ i, M i →ₗ[K] M i) :
    (LinearMap.pi fun i => (f i).comp (LinearMap.proj i)).det =
      ∏ i, (f i).det := by
  classical
  let b (i : ι) := Module.Free.chooseBasis K (M i)
  let B := Pi.basis b
  simp_rw [← LinearMap.det_toMatrix B,
    ← LinearMap.det_toMatrix (b _)]
  have hmatrix :
      LinearMap.toMatrix B B
          (LinearMap.pi fun i => (f i).comp (LinearMap.proj i)) =
        Matrix.blockDiagonal' fun i => LinearMap.toMatrix (b i) (b i) (f i) := by
    ext ⟨i, a⟩ ⟨j, c⟩
    by_cases hij : i = j
    · subst j
      simp [B, b, LinearMap.toMatrix_apply', Pi.basis_apply, Pi.basis_repr,
        LinearMap.pi_apply, LinearMap.coe_comp, LinearMap.coe_proj,
        Function.comp_apply]
    · simp [B, b, LinearMap.toMatrix_apply', Pi.basis_apply, Pi.basis_repr,
        LinearMap.pi_apply, LinearMap.coe_comp, LinearMap.coe_proj,
        Function.comp_apply, Matrix.blockDiagonal'_apply_ne, hij]
  rw [hmatrix, det_blockDiagonal']

end DependentPiDet

section PiMatrixLeftMulDet

variable {K : Type*} [Field K]

lemma det_lmul_pi_matrix (n : ℕ) (d : Fin n → ℕ)
    (x : ∀ i, Matrix (Fin (d i)) (Fin (d i)) K) :
    (Algebra.lmul K (∀ i, Matrix (Fin (d i)) (Fin (d i)) K) x).det =
      ∏ i, Matrix.det (x i) ^ d i := by
  classical
  have hlmul :
      Algebra.lmul K (∀ i, Matrix (Fin (d i)) (Fin (d i)) K) x =
        LinearMap.pi fun i =>
          (Algebra.lmul K (Matrix (Fin (d i)) (Fin (d i)) K) (x i)).comp
            (LinearMap.proj i) := by
    ext y i a b
    rfl
  rw [hlmul, det_pi_dependent]
  apply Finset.prod_congr rfl
  intro i hi
  simpa using det_lmul_matrix (x i)

end PiMatrixLeftMulDet

section GroupDeterminantEval

variable (K G : Type*) [Field K] [Group G] [Fintype G] [DecidableEq G]

noncomputable def testGroupDeterminant : MvPolynomial G K :=
  Matrix.det fun g h : G => MvPolynomial.X (g * h)

noncomputable def groupCoefficientElement (y : G → K) : MonoidAlgebra K G :=
  (MonoidAlgebra.basis G K).equivFun.symm y

omit [Group G] [DecidableEq G] in
lemma groupCoefficientElement_apply (y : G → K) (g : G) :
    groupCoefficientElement K G y g = y g := by
  change (MonoidAlgebra.basis G K).equivFun
    (groupCoefficientElement K G y) g = y g
  rw [groupCoefficientElement, LinearEquiv.apply_symm_apply]

omit [Group G] [DecidableEq G] in
lemma groupCoefficientElement_repr (a : MonoidAlgebra K G) :
    groupCoefficientElement K G
      (fun g => (MonoidAlgebra.basis G K).repr a g) = a := by
  change (MonoidAlgebra.basis G K).equivFun.symm
    (fun g => (MonoidAlgebra.basis G K).repr a g) = a
  rw [← Basis.equivFun_apply, LinearEquiv.symm_apply_apply]

lemma leftMulMatrix_groupCoefficientElement (y : G → K) (g h : G) :
    Algebra.leftMulMatrix (MonoidAlgebra.basis G K)
        (groupCoefficientElement K G y) g h = y (g * h⁻¹) := by
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  change ((groupCoefficientElement K G y * MonoidAlgebra.single h 1 :
    MonoidAlgebra K G) g) = _
  rw [MonoidAlgebra.mul_single_apply]
  simp [groupCoefficientElement_apply]

lemma eval_testGroupDeterminant (y : G → K) :
    MvPolynomial.eval y (testGroupDeterminant K G) =
      (((↑((Equiv.inv G).sign) : ℤ) : K)) *
        (Algebra.lmul K (MonoidAlgebra K G)
          (groupCoefficientElement K G y)).det := by
  classical
  rw [testGroupDeterminant]
  calc
    MvPolynomial.eval y (Matrix.det fun g h : G => MvPolynomial.X (g * h)) =
        Matrix.det (fun g h : G => y (g * h)) := by
      rw [RingHom.map_det]
      apply congrArg Matrix.det
      apply Matrix.ext
      intro g h
      simp
    _ = Matrix.det ((Algebra.leftMulMatrix (MonoidAlgebra.basis G K)
        (groupCoefficientElement K G y)).submatrix id (Equiv.inv G)) := by
      apply congrArg Matrix.det
      apply Matrix.ext
      intro g h
      simp [leftMulMatrix_groupCoefficientElement]
    _ = (((↑((Equiv.inv G).sign) : ℤ) : K)) *
        Matrix.det (Algebra.leftMulMatrix (MonoidAlgebra.basis G K)
          (groupCoefficientElement K G y)) := Matrix.det_permute' _ _
    _ = _ := by
      rw [Algebra.leftMulMatrix_apply, LinearMap.det_toMatrix]

end GroupDeterminantEval

section WedderburnCoordinates

abbrev BlockVar (n : ℕ) (d : Fin n → ℕ) :=
  Σ i : Fin n, Fin (d i) × Fin (d i)

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]

noncomputable def blockStandardBasis (n : ℕ) (d : Fin n → ℕ) :
    Basis (BlockVar n d) K
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) K) :=
  Pi.basis fun i => Matrix.stdBasis K (Fin (d i)) (Fin (d i))

lemma blockStandardBasis_equivFun_apply (n : ℕ) (d : Fin n → ℕ)
    (x : ∀ i, Matrix (Fin (d i)) (Fin (d i)) K)
    (i : Fin n) (a b : Fin (d i)) :
    (blockStandardBasis (K := K) n d).equivFun x ⟨i, (a, b)⟩ = x i a b := by
  classical
  simp [blockStandardBasis, Basis.equivFun_apply, Matrix.stdBasis]

noncomputable def wedderburnBasis (n : ℕ) (d : Fin n → ℕ)
    (e : A ≃ₐ[K] ∀ i, Matrix (Fin (d i)) (Fin (d i)) K) :
    Basis (BlockVar n d) K A :=
  (blockStandardBasis (K := K) n d).map e.symm.toLinearEquiv

lemma wedderburnBasis_equivFun_apply (n : ℕ) (d : Fin n → ℕ)
    (e : A ≃ₐ[K] ∀ i, Matrix (Fin (d i)) (Fin (d i)) K)
    (x : A) (v : BlockVar n d) :
    (wedderburnBasis n d e).equivFun x v =
      (blockStandardBasis (K := K) n d).equivFun (e x) v := by
  classical
  simp [wedderburnBasis, Basis.equivFun_apply]

lemma wedderburnBasis_symm_coordinates (n : ℕ) (d : Fin n → ℕ)
    (e : A ≃ₐ[K] ∀ i, Matrix (Fin (d i)) (Fin (d i)) K)
    (x : BlockVar n d → K) (i : Fin n) (a b : Fin (d i)) :
    e ((wedderburnBasis n d e).equivFun.symm x) i a b = x ⟨i, (a, b)⟩ := by
  classical
  calc
    e ((wedderburnBasis n d e).equivFun.symm x) i a b =
        (blockStandardBasis (K := K) n d).equivFun
          (e ((wedderburnBasis n d e).equivFun.symm x)) ⟨i, (a, b)⟩ :=
      (blockStandardBasis_equivFun_apply n d _ i a b).symm
    _ = (wedderburnBasis n d e).equivFun
        ((wedderburnBasis n d e).equivFun.symm x) ⟨i, (a, b)⟩ :=
      (wedderburnBasis_equivFun_apply n d e _ _).symm
    _ = x ⟨i, (a, b)⟩ :=
      congrFun ((wedderburnBasis n d e).equivFun.apply_symm_apply x) ⟨i, (a, b)⟩

end WedderburnCoordinates

section BlockFactors

variable {K : Type*} [Field K]

def blockInclusion (n : ℕ) (d : Fin n → ℕ) (i : Fin n) :
    (Fin (d i) × Fin (d i)) → BlockVar n d :=
  fun x => ⟨i, x⟩

lemma blockInclusion_injective (n : ℕ) (d : Fin n → ℕ) (i : Fin n) :
    Function.Injective (blockInclusion n d i) := by
  intro x y h
  exact eq_of_heq (Sigma.mk.inj_iff.mp h |>.2)

noncomputable def blockFactor (n : ℕ) (d : Fin n → ℕ) (i : Fin n) :
    MvPolynomial (BlockVar n d) K :=
  MvPolynomial.rename (blockInclusion n d i) (genericDet K (d i))

lemma blockFactor_irreducible (n : ℕ) (d : Fin n → ℕ)
    (hd : ∀ i, NeZero (d i)) (i : Fin n) :
    Irreducible (blockFactor (K := K) n d i) := by
  letI := hd i
  have hgeneric : Irreducible (genericDet K (d i)) := by
    rw [← Nat.succ_pred (NeZero.ne (d i))]
    exact irreducible_genericDet_succ K (d i - 1)
  exact irreducible_rename_of_injective hgeneric (blockInclusion n d i)
    (blockInclusion_injective n d i)

lemma blockFactor_isHomogeneous (n : ℕ) (d : Fin n → ℕ) (i : Fin n) :
    (blockFactor (K := K) n d i).IsHomogeneous (d i) :=
  (genericDet_isHomogeneous K (d i)).rename_isHomogeneous

lemma eval_blockFactor (n : ℕ) (d : Fin n → ℕ)
    (x : BlockVar n d → K) (i : Fin n) :
    MvPolynomial.eval x (blockFactor (K := K) n d i) =
      Matrix.det (fun a b : Fin (d i) => x ⟨i, (a, b)⟩) := by
  classical
  rw [blockFactor, MvPolynomial.eval_rename, genericDet]
  calc
    _ = Matrix.det ((MvPolynomial.eval (x ∘ blockInclusion n d i)).mapMatrix
        (Matrix.mvPolynomialX (Fin (d i)) (Fin (d i)) K)) :=
      RingHom.map_det _ _
    _ = _ := by
      apply congrArg Matrix.det
      apply Matrix.ext
      intro a b
      simp [blockInclusion]

noncomputable def blockIdentityAssignment (n : ℕ) (d : Fin n → ℕ)
    (j : Fin n) : BlockVar n d → K :=
  fun x => if _h : x.1 = j then
    if _h' : x.2.1 = x.2.2 then 1 else 0
  else 0

lemma eval_blockFactor_identity (n : ℕ) (d : Fin n → ℕ)
    (hd : ∀ i, NeZero (d i)) (i j : Fin n) :
    MvPolynomial.eval (blockIdentityAssignment (K := K) n d j)
        (blockFactor (K := K) n d i) = if i = j then 1 else 0 := by
  classical
  letI := hd i
  letI : Nonempty (Fin (d i)) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (d i))⟩⟩
  rw [blockFactor, MvPolynomial.eval_rename, genericDet]
  calc
    MvPolynomial.eval
        (blockIdentityAssignment (K := K) n d j ∘ blockInclusion n d i)
        (Matrix.det (Matrix.mvPolynomialX (Fin (d i)) (Fin (d i)) K)) =
      Matrix.det ((MvPolynomial.eval
        (blockIdentityAssignment (K := K) n d j ∘ blockInclusion n d i)).mapMatrix
          (Matrix.mvPolynomialX (Fin (d i)) (Fin (d i)) K)) := by
        exact RingHom.map_det _ _
    _ = if i = j then 1 else 0 := by
      by_cases hij : i = j
      · subst j
        have hmat :
            (MvPolynomial.eval
                (blockIdentityAssignment (K := K) n d i ∘ blockInclusion n d i)).mapMatrix
              (Matrix.mvPolynomialX (Fin (d i)) (Fin (d i)) K) = 1 := by
          ext a b
          simp [Matrix.mvPolynomialX_apply, blockIdentityAssignment,
            blockInclusion, Matrix.one_apply]
        rw [hmat, Matrix.det_one, if_pos rfl]
      · have hmat :
            (MvPolynomial.eval
                (blockIdentityAssignment (K := K) n d j ∘ blockInclusion n d i)).mapMatrix
              (Matrix.mvPolynomialX (Fin (d i)) (Fin (d i)) K) = 0 := by
          ext a b
          simp [Matrix.mvPolynomialX_apply, blockIdentityAssignment,
            blockInclusion, hij]
        rw [hmat, Matrix.det_zero, if_neg hij]; infer_instance

lemma blockFactor_not_associated (n : ℕ) (d : Fin n → ℕ)
    (hd : ∀ i, NeZero (d i)) (i j : Fin n) (hij : i ≠ j) :
    ¬ Associated (blockFactor (K := K) n d i) (blockFactor (K := K) n d j) := by
  intro hassoc
  obtain ⟨a, ha⟩ := hassoc.dvd
  have heval := congrArg
    (MvPolynomial.eval (blockIdentityAssignment (K := K) n d j)) ha
  rw [map_mul, eval_blockFactor_identity n d hd i j,
    eval_blockFactor_identity n d hd j j] at heval
  simp [hij] at heval

end BlockFactors

section WedderburnFactorization

variable {K G : Type*} [Field K] [Infinite K]
  [Group G] [Fintype G] [DecidableEq G]

noncomputable def groupBlockPolynomialEquiv (n : ℕ) (d : Fin n → ℕ)
    (e : MonoidAlgebra K G ≃ₐ[K]
      ∀ i, Matrix (Fin (d i)) (Fin (d i)) K) :
    MvPolynomial G K ≃ₐ[K] MvPolynomial (BlockVar n d) K :=
  basisPolynomialEquiv (MonoidAlgebra.basis G K) (wedderburnBasis n d e)

omit [Infinite K] in
lemma eval_groupBlockPolynomialEquiv_groupDet (n : ℕ) (d : Fin n → ℕ)
    (e : MonoidAlgebra K G ≃ₐ[K]
      ∀ i, Matrix (Fin (d i)) (Fin (d i)) K)
    (x : BlockVar n d → K) :
    MvPolynomial.eval x
        (groupBlockPolynomialEquiv n d e (testGroupDeterminant K G)) =
      (((↑((Equiv.inv G).sign) : ℤ) : K)) *
        ∏ i, (MvPolynomial.eval x (blockFactor (K := K) n d i)) ^ d i := by
  classical
  let a : MonoidAlgebra K G := (wedderburnBasis n d e).equivFun.symm x
  have hnorm :
      (Algebra.lmul K (∀ i, Matrix (Fin (d i)) (Fin (d i)) K) (e a)).det =
        (Algebra.lmul K (MonoidAlgebra K G) a).det := by
    simpa only [Algebra.norm_apply] using Algebra.norm_eq_of_algEquiv e a
  calc
    MvPolynomial.eval x
        (groupBlockPolynomialEquiv n d e (testGroupDeterminant K G)) =
      MvPolynomial.eval
        (fun g => (MonoidAlgebra.basis G K).repr (a) g)
        (testGroupDeterminant K G) := by
          exact eval_basisPolynomialEquiv _ _ _ _
    _ = (((↑((Equiv.inv G).sign) : ℤ) : K)) *
        (Algebra.lmul K (MonoidAlgebra K G) a).det :=
      by simpa [groupCoefficientElement_repr] using
        eval_testGroupDeterminant K G
          (fun g => (MonoidAlgebra.basis G K).repr a g)
    _ = (((↑((Equiv.inv G).sign) : ℤ) : K)) *
        (Algebra.lmul K (∀ i, Matrix (Fin (d i)) (Fin (d i)) K) (e a)).det := by
      rw [hnorm]
    _ = (((↑((Equiv.inv G).sign) : ℤ) : K)) *
        ∏ i, Matrix.det (e a i) ^ d i := by
      rw [det_lmul_pi_matrix]
    _ = (((↑((Equiv.inv G).sign) : ℤ) : K)) *
        ∏ i, (MvPolynomial.eval x (blockFactor (K := K) n d i)) ^ d i := by
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      congr 1
      rw [eval_blockFactor]
      apply congrArg Matrix.det
      apply Matrix.ext
      intro r c
      exact wedderburnBasis_symm_coordinates n d e x i r c

lemma map_groupDeterminant_eq_blockFactors (n : ℕ) (d : Fin n → ℕ)
    (e : MonoidAlgebra K G ≃ₐ[K]
      ∀ i, Matrix (Fin (d i)) (Fin (d i)) K) :
    groupBlockPolynomialEquiv n d e (testGroupDeterminant K G) =
      MvPolynomial.C (((↑((Equiv.inv G).sign) : ℤ) : K)) *
        ∏ i, (blockFactor (K := K) n d i) ^ d i := by
  apply MvPolynomial.funext
  intro x
  rw [eval_groupBlockPolynomialEquiv_groupDet]
  simp

end WedderburnFactorization

section PiMatrixCenter

variable {K : Type*} [Field K]

noncomputable def piMatrixCenterEquiv (n : ℕ) (d : Fin n → ℕ)
    (hd : ∀ i, NeZero (d i)) :
    Subalgebra.center K (∀ i, Matrix (Fin (d i)) (Fin (d i)) K) ≃ₗ[K]
      (Fin n → K) := by
  classical
  let zeroIndex (i : Fin n) : Fin (d i) :=
    ⟨0, Nat.pos_of_ne_zero (NeZero.ne (d i))⟩
  let toFun :
      Subalgebra.center K (∀ i, Matrix (Fin (d i)) (Fin (d i)) K) →ₗ[K]
        (Fin n → K) :=
    { toFun := fun z i => z.1 i (zeroIndex i) (zeroIndex i)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let invFun : (Fin n → K) →ₗ[K]
      Subalgebra.center K (∀ i, Matrix (Fin (d i)) (Fin (d i)) K) :=
    { toFun := fun x => ⟨fun i => Matrix.scalar (Fin (d i)) (x i), by
        rw [Subalgebra.mem_center_iff]
        intro y
        ext i a b
        simp [mul_comm]⟩
      map_add' := by
        intro x y
        ext i a b
        by_cases h : a = b <;> simp [Matrix.scalar_apply, h]
      map_smul' := by
        intro r x
        ext i a b
        by_cases h : a = b <;> simp [Matrix.scalar_apply, h] }
  refine LinearEquiv.ofLinear toFun invFun ?_ ?_
  · apply LinearMap.ext
    intro x
    funext i
    simp [toFun, invFun, zeroIndex, Matrix.scalar_apply]
  · apply LinearMap.ext
    intro z
    have hzcenter (i : Fin n) :
        z.1 i ∈ Subalgebra.center K (Matrix (Fin (d i)) (Fin (d i)) K) := by
      rw [Subalgebra.mem_center_iff]
      intro M
      have hz := (Subalgebra.mem_center_iff.mp z.2) (Pi.single i M)
      simpa using congrFun hz i
    apply Subtype.ext
    funext i
    apply Matrix.ext
    intro a b
    change Matrix.scalar (Fin (d i))
      (z.1 i (zeroIndex i) (zeroIndex i)) a b = z.1 i a b
    obtain ⟨r, hr⟩ := (Algebra.IsCentral.mem_center_iff K).mp (hzcenter i)
    rw [hr]
    by_cases h : a = b <;>
      simp [zeroIndex, Matrix.scalar_apply, Matrix.algebraMap_matrix_apply, h]

end PiMatrixCenter

section GroupAlgebraCenter

variable {K G : Type*} [Field K] [Group G] [Fintype G] [DecidableEq G]

omit [Fintype G] [DecidableEq G] in
lemma center_coeff_eq_of_isConj
    (z : Subalgebra.center K (MonoidAlgebra K G)) {a b : G}
    (hab : IsConj a b) : z.1 a = z.1 b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hab
  have hz := congrArg (fun x : MonoidAlgebra K G => x (c * a))
    ((Subalgebra.mem_center_iff.mp z.2) (MonoidAlgebra.single c 1))
  simpa [MonoidAlgebra.single_mul_apply, MonoidAlgebra.mul_single_apply,
    hc, mul_assoc] using hz

noncomputable def centerClassFunction
    (z : Subalgebra.center K (MonoidAlgebra K G)) : ConjClasses G → K :=
  Quotient.lift (fun g => z.1 g) fun _ _ h => center_coeff_eq_of_isConj z h

omit [Fintype G] [DecidableEq G] in
@[simp] lemma centerClassFunction_mk
    (z : Subalgebra.center K (MonoidAlgebra K G)) (g : G) :
    centerClassFunction z (ConjClasses.mk g) = z.1 g := rfl

noncomputable def classFunctionElement (f : ConjClasses G → K) : MonoidAlgebra K G :=
  (MonoidAlgebra.basis G K).equivFun.symm fun g => f (ConjClasses.mk g)

omit [DecidableEq G] in
@[simp] lemma classFunctionElement_apply (f : ConjClasses G → K) (g : G) :
    classFunctionElement f g = f (ConjClasses.mk g) := by
  change (MonoidAlgebra.basis G K).equivFun (classFunctionElement f) g = _
  rw [classFunctionElement, LinearEquiv.apply_symm_apply]

omit [DecidableEq G] in
lemma classFunctionElement_mem_center (f : ConjClasses G → K) :
    classFunctionElement f ∈ Subalgebra.center K (MonoidAlgebra K G) := by
  rw [Subalgebra.mem_center_iff]
  intro y
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
      calc
        (x + y) * classFunctionElement f =
            x * classFunctionElement f + y * classFunctionElement f := add_mul _ _ _
        _ = classFunctionElement f * x + classFunctionElement f * y :=
          congrArg₂ (· + ·) hx hy
        _ = classFunctionElement f * (x + y) := (mul_add _ _ _).symm
  | single h r =>
      ext g
      have hconj : IsConj (g * h⁻¹) (h⁻¹ * g) := by
        rw [isConj_iff]
        refine ⟨h⁻¹, ?_⟩
        simp [mul_assoc]
      have hmk : ConjClasses.mk (g * h⁻¹) = ConjClasses.mk (h⁻¹ * g) :=
        ConjClasses.mk_eq_mk_iff_isConj.mpr hconj
      simp [MonoidAlgebra.single_mul_apply, MonoidAlgebra.mul_single_apply,
        classFunctionElement_apply, hmk, mul_comm]

noncomputable def groupAlgebraCenterEquiv :
    Subalgebra.center K (MonoidAlgebra K G) ≃ₗ[K] (ConjClasses G → K) := by
  let toFun : Subalgebra.center K (MonoidAlgebra K G) →ₗ[K] (ConjClasses G → K) :=
    { toFun := centerClassFunction
      map_add' := by
        intro x y
        funext q
        obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective q
        rfl
      map_smul' := by
        intro r x
        funext q
        obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective q
        rfl }
  let invFun : (ConjClasses G → K) →ₗ[K]
      Subalgebra.center K (MonoidAlgebra K G) :=
    { toFun := fun f => ⟨classFunctionElement f, classFunctionElement_mem_center f⟩
      map_add' := by
        intro f g
        apply Subtype.ext
        ext x
        simp
      map_smul' := by
        intro r f
        apply Subtype.ext
        ext x
        simp }
  refine LinearEquiv.ofLinear toFun invFun ?_ ?_
  · apply LinearMap.ext
    intro f
    funext q
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective q
    simp [toFun, invFun]
  · apply LinearMap.ext
    intro z
    apply Subtype.ext
    ext g
    simp [toFun, invFun]

end GroupAlgebraCenter

section CenterTransport

variable {K A B : Type*} [Field K] [Ring A] [Ring B] [Algebra K A] [Algebra K B]

noncomputable def centerLinearEquiv (e : A ≃ₐ[K] B) :
    Subalgebra.center K A ≃ₗ[K] Subalgebra.center K B where
  toFun z := ⟨e z.1, MulEquivClass.apply_mem_center e z.2⟩
  invFun z := ⟨e.symm z.1, MulEquivClass.apply_mem_center e.symm z.2⟩
  left_inv z := Subtype.ext (e.symm_apply_apply z.1)
  right_inv z := Subtype.ext (e.apply_symm_apply z.1)
  map_add' x y := Subtype.ext (map_add e x.1 y.1)
  map_smul' r x := Subtype.ext (map_smul e r x.1)

end CenterTransport

section WedderburnBlockCount

variable {K G : Type*} [Field K] [Group G] [Fintype G] [DecidableEq G]

lemma wedderburn_block_count_eq_conjClasses
    (n : ℕ) (d : Fin n → ℕ) (hd : ∀ i, NeZero (d i))
    (e : MonoidAlgebra K G ≃ₐ[K]
      ∀ i, Matrix (Fin (d i)) (Fin (d i)) K) :
    n = Nat.card (ConjClasses G) := by
  classical
  calc
    n = Module.finrank K (Fin n → K) := (Module.finrank_fin_fun K).symm
    _ = Module.finrank K
        (Subalgebra.center K (∀ i, Matrix (Fin (d i)) (Fin (d i)) K)) :=
      (piMatrixCenterEquiv n d hd).finrank_eq.symm
    _ = Module.finrank K (Subalgebra.center K (MonoidAlgebra K G)) :=
      (centerLinearEquiv e).finrank_eq.symm
    _ = Module.finrank K (ConjClasses G → K) :=
      groupAlgebraCenterEquiv.finrank_eq
    _ = Fintype.card (ConjClasses G) := Module.finrank_fintype_fun_eq_card K
    _ = Nat.card (ConjClasses G) := Fintype.card_eq_nat_card

end WedderburnBlockCount

section BasisPolynomialEquivSymm

variable {K M ι κ : Type*} [Field K] [AddCommGroup M] [Module K M]
  [Fintype ι] [Fintype κ]

lemma basisPolynomialEquiv_symm (b : Basis ι K M) (c : Basis κ K M) :
    (basisPolynomialEquiv b c).symm = basisPolynomialEquiv c b := rfl

end BasisPolynomialEquivSymm

section WedderburnHomogeneousTransport

variable {K G : Type*} [Field K] [Infinite K]
  [Group G] [Fintype G] [DecidableEq G]

omit [DecidableEq G] in
lemma groupBlockPolynomialEquiv_symm_isHomogeneous
    (n : ℕ) (d : Fin n → ℕ)
    (e : MonoidAlgebra K G ≃ₐ[K]
      ∀ i, Matrix (Fin (d i)) (Fin (d i)) K)
    {q : MvPolynomial (BlockVar n d) K} {m : ℕ}
    (hq : q.IsHomogeneous m) :
    ((groupBlockPolynomialEquiv n d e).symm q).IsHomogeneous m := by
  rw [groupBlockPolynomialEquiv, basisPolynomialEquiv_symm]
  exact basisPolynomialEquiv_isHomogeneous _ _ hq

end WedderburnHomogeneousTransport

section AdjustedBlockFactors

variable {K : Type*} [Field K]

noncomputable def adjustedBlockFactor (n : ℕ) (d : Fin n → ℕ)
    (i0 : Fin n) (u : K) (i : Fin n) : MvPolynomial (BlockVar n d) K :=
  MvPolynomial.C (if i0 = i then u else 1) * blockFactor n d i

lemma adjustedBlockFactor_scalar_ne_zero (n : ℕ)
    (i0 : Fin n) {u : K} (hu : u ≠ 0) (i : Fin n) :
    (if i0 = i then u else 1) ≠ 0 := by
  split_ifs <;> simp_all

lemma adjustedBlockFactor_scalar_isUnit (n : ℕ) (d : Fin n → ℕ)
    (i0 : Fin n) {u : K} (hu : u ≠ 0) (i : Fin n) :
    IsUnit (MvPolynomial.C (if i0 = i then u else 1) :
      MvPolynomial (BlockVar n d) K) :=
  (isUnit_iff_ne_zero.mpr (adjustedBlockFactor_scalar_ne_zero n i0 hu i)).map
    (MvPolynomial.C : K →+* MvPolynomial (BlockVar n d) K)

lemma adjustedBlockFactor_irreducible (n : ℕ) (d : Fin n → ℕ)
    (hd : ∀ i, NeZero (d i)) (i0 : Fin n) {u : K} (hu : u ≠ 0) (i : Fin n) :
    Irreducible (adjustedBlockFactor n d i0 u i) := by
  rw [adjustedBlockFactor]
  exact (irreducible_isUnit_mul
    (adjustedBlockFactor_scalar_isUnit n d i0 hu i)).mpr
      (blockFactor_irreducible n d hd i)

lemma adjustedBlockFactor_isHomogeneous (n : ℕ) (d : Fin n → ℕ)
    (i0 : Fin n) (u : K) (i : Fin n) :
    (adjustedBlockFactor n d i0 u i).IsHomogeneous (d i) := by
  exact (blockFactor_isHomogeneous (K := K) n d i).C_mul _

lemma adjustedBlockFactor_associated (n : ℕ) (d : Fin n → ℕ)
    (i0 : Fin n) {u : K} (hu : u ≠ 0) (i : Fin n) :
    Associated (adjustedBlockFactor n d i0 u i) (blockFactor n d i) := by
  rw [adjustedBlockFactor]
  exact associated_unit_mul_left _ _
    (adjustedBlockFactor_scalar_isUnit n d i0 hu i)

lemma adjustedBlockFactor_not_associated (n : ℕ) (d : Fin n → ℕ)
    (hd : ∀ i, NeZero (d i)) (i0 : Fin n) {u : K} (hu : u ≠ 0)
    (i j : Fin n) (hij : i ≠ j) :
    ¬ Associated (adjustedBlockFactor n d i0 u i)
      (adjustedBlockFactor n d i0 u j) := by
  intro h
  apply blockFactor_not_associated (K := K) n d hd i j hij
  exact (adjustedBlockFactor_associated (K := K) n d i0 hu i).symm.trans
    (h.trans (adjustedBlockFactor_associated (K := K) n d i0 hu j))

lemma prod_adjustedBlockFactor_pow (n : ℕ) (d : Fin n → ℕ)
    (i0 : Fin n) (u epsilon : K) (hu : u ^ d i0 = epsilon) :
    ∏ i, (adjustedBlockFactor n d i0 u i) ^ d i =
      MvPolynomial.C epsilon * ∏ i, (blockFactor n d i) ^ d i := by
  classical
  have hscalar :
      (∏ i, (MvPolynomial.C (if i0 = i then u else 1) :
        MvPolynomial (BlockVar n d) K) ^ d i) = MvPolynomial.C epsilon := by
    simp_rw [← map_pow (MvPolynomial.C : K →+* MvPolynomial (BlockVar n d) K)]
    rw [← map_prod]
    simp [hu]
  calc
    ∏ i, (adjustedBlockFactor n d i0 u i) ^ d i =
        (∏ i, (MvPolynomial.C (if i0 = i then u else 1) :
          MvPolynomial (BlockVar n d) K) ^ d i) *
          ∏ i, (blockFactor n d i) ^ d i := by
      simp_rw [adjustedBlockFactor, mul_pow]
      exact Finset.prod_mul_distrib
    _ = _ := by rw [hscalar]

end AdjustedBlockFactors

end Scratch
