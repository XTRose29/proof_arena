import Submission.HomogeneousSlice
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

open MvPolynomial

variable {K : Type*} [Field K]

namespace Submission.Helpers

lemma degreeIndex_finite {σ : Type*} [Finite σ] (m : ℕ) :
    Set.Finite {e : σ →₀ ℕ | e.degree = m} :=
  (Finsupp.finite_of_degree_le m).subset fun _ he => le_of_eq he

noncomputable instance degreeIndexFintype {σ : Type*} [Finite σ] (m : ℕ) :
    Fintype {e : σ →₀ ℕ // e.degree = m} :=
  (degreeIndex_finite m).fintype

noncomputable def homogeneousPieceEquivDegreeFinsupp {σ : Type*} (m : ℕ) :
    homogeneousSubmodule σ K m ≃ₗ[K]
      ({e : σ →₀ ℕ // e.degree = m} →₀ K) :=
  LinearEquiv.ofEq _ _ (homogeneousSubmodule_eq_finsupp_supported σ K m) ≪≫ₗ
    Finsupp.supportedEquivFinsupp {e : σ →₀ ℕ | e.degree = m}

noncomputable def degreeIndexEquivAntidiag {σ : Type*} [Fintype σ] [DecidableEq σ]
    (m : ℕ) :
    {e : σ →₀ ℕ // e.degree = m} ≃
      (Finset.univ : Finset σ).finsuppAntidiag m := by
  classical
  refine
    { toFun := fun e => ⟨e, Finset.mem_finsuppAntidiag.mpr ⟨?_, by simp⟩⟩
      invFun := fun e => ⟨e, ?_⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  · simpa only [Finsupp.degree_eq_sum] using e.2
  · rw [Finsupp.degree_eq_sum]
    exact (Finset.mem_finsuppAntidiag.mp e.2).1

lemma degreeIndex_card {σ : Type*} [Fintype σ] (m : ℕ) :
    Fintype.card {e : σ →₀ ℕ // e.degree = m} =
      (Fintype.card σ).multichoose m := by
  classical
  calc
    Fintype.card {e : σ →₀ ℕ // e.degree = m} =
        Fintype.card ((Finset.univ : Finset σ).finsuppAntidiag m) :=
      Fintype.card_congr (degreeIndexEquivAntidiag m)
    _ = ((Finset.univ : Finset σ).finsuppAntidiag m).card := Fintype.card_coe _
    _ = (Fintype.card σ).multichoose m :=
      Finset.card_finsuppAntidiag_nat_eq_multichoose _

lemma homogeneousSubmodule_finrank {σ : Type*} [Fintype σ] (m : ℕ) :
    Module.finrank K (homogeneousSubmodule σ K m) =
      (Fintype.card σ).multichoose m := by
  classical
  rw [(homogeneousPieceEquivDegreeFinsupp (K := K) m).finrank_eq,
    Module.finrank_finsupp_self, degreeIndex_card]

section GradedPieces

variable {σ : Type*}

abbrev HomogeneousPiece (m : ℕ) := homogeneousSubmodule σ K m

noncomputable def homogeneousIdealPart (I : Ideal (MvPolynomial σ K)) (m : ℕ) :
    Submodule K (HomogeneousPiece (K := K) (σ := σ) m) :=
  (I.restrictScalars K).comap
    (homogeneousSubmodule σ K m).subtype

abbrev HomogeneousQuotientPiece (I : Ideal (MvPolynomial σ K)) (m : ℕ) :=
  HomogeneousPiece (K := K) (σ := σ) m ⧸ homogeneousIdealPart I m

noncomputable def homogeneousMulLinear (g : MvPolynomial σ K) (d m : ℕ)
    (hg : g.IsHomogeneous d) (hdm : d ≤ m) :
    HomogeneousPiece (K := K) (σ := σ) (m - d) →ₗ[K]
      HomogeneousPiece (K := K) (σ := σ) m :=
  ((LinearMap.mulLeft K g).domRestrict (homogeneousSubmodule σ K (m - d))).codRestrict
    (homogeneousSubmodule σ K m) fun p => by
      change (g * p.1).IsHomogeneous m
      convert hg.mul p.2 using 1
      omega

lemma homogeneousMulLinear_apply (g : MvPolynomial σ K) (d m : ℕ)
    (hg : g.IsHomogeneous d) (hdm : d ≤ m)
    (p : HomogeneousPiece (K := K) (σ := σ) (m - d)) :
    (homogeneousMulLinear g d m hg hdm p : MvPolynomial σ K) = g * p :=
  rfl

def RegularModIdeal (I : Ideal (MvPolynomial σ K)) (g : MvPolynomial σ K) : Prop :=
  ∀ a : MvPolynomial σ K, g * a ∈ I → a ∈ I

noncomputable def homogeneousMulQuotient (I : Ideal (MvPolynomial σ K))
    (g : MvPolynomial σ K) (d m : ℕ) (hg : g.IsHomogeneous d) (hdm : d ≤ m) :
    HomogeneousQuotientPiece I (m - d) →ₗ[K] HomogeneousQuotientPiece I m :=
  (homogeneousIdealPart I (m - d)).mapQ (homogeneousIdealPart I m)
    (homogeneousMulLinear g d m hg hdm) <| by
      rintro p hp
      change g * p.1 ∈ I
      exact I.mul_mem_left g hp

lemma homogeneousMulQuotient_apply (I : Ideal (MvPolynomial σ K))
    (g : MvPolynomial σ K) (d m : ℕ) (hg : g.IsHomogeneous d) (hdm : d ≤ m)
    (p : HomogeneousPiece (K := K) (σ := σ) (m - d)) :
    homogeneousMulQuotient I g d m hg hdm (Submodule.Quotient.mk p) =
      Submodule.Quotient.mk (homogeneousMulLinear g d m hg hdm p) :=
  rfl

lemma homogeneousMulQuotient_injective (I : Ideal (MvPolynomial σ K))
    (g : MvPolynomial σ K) (d m : ℕ) (hg : g.IsHomogeneous d) (hdm : d ≤ m)
    (hreg : RegularModIdeal I g) :
    Function.Injective (homogeneousMulQuotient I g d m hg hdm) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm ?_ bot_le
  rintro x hx
  induction x using Submodule.Quotient.induction_on with
  | _ p =>
      rw [LinearMap.mem_ker, homogeneousMulQuotient_apply,
        Submodule.Quotient.mk_eq_zero] at hx
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      change p.1 ∈ I
      apply hreg p.1
      exact hx

lemma homogeneousIdealPart_mono {I J : Ideal (MvPolynomial σ K)} (hIJ : I ≤ J)
    (m : ℕ) : homogeneousIdealPart I m ≤ homogeneousIdealPart J m := by
  intro p hp
  exact hIJ hp

noncomputable def homogeneousQuotientFactor {I J : Ideal (MvPolynomial σ K)}
    (hIJ : I ≤ J) (m : ℕ) :
    HomogeneousQuotientPiece I m →ₗ[K] HomogeneousQuotientPiece J m :=
  Submodule.factor (homogeneousIdealPart_mono hIJ m)

lemma homogeneousQuotientFactor_apply {I J : Ideal (MvPolynomial σ K)}
    (hIJ : I ≤ J) (m : ℕ) (p : HomogeneousPiece (K := K) (σ := σ) m) :
    homogeneousQuotientFactor hIJ m (Submodule.Quotient.mk p) =
      Submodule.Quotient.mk p :=
  rfl

lemma homogeneousQuotientFactor_surjective {I J : Ideal (MvPolynomial σ K)}
    (hIJ : I ≤ J) (m : ℕ) :
    Function.Surjective (homogeneousQuotientFactor hIJ m) :=
  Submodule.factor_surjective (homogeneousIdealPart_mono hIJ m)

end GradedPieces

end Submission.Helpers
