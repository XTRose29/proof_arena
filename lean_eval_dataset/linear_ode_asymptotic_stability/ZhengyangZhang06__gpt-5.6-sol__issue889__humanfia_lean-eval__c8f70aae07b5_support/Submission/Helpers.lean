import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

open Filter Topology
open scoped Matrix Matrix.Norms.Operator
open NormedSpace

namespace Submission.Helpers

noncomputable section

lemma tendsto_cexp_mul_pow (μ : ℂ) (hμ : μ.re < 0) (k : ℕ) :
    Tendsto (fun t : ℝ => Complex.exp ((t : ℂ) * μ) * (t : ℂ) ^ k)
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (k : ℝ) (-μ.re) (neg_pos.mpr hμ)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simp [Complex.norm_exp, Complex.mul_re, Real.rpow_natCast,
    abs_of_nonneg ht, mul_comm]

lemma exp_mulVec_of_pow_mulVec_eq_zero {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → ℂ) (k : ℕ) (hN : N ^ k *ᵥ v = 0) (s : ℂ) :
    exp (s • N) *ᵥ v =
      ∑ j ∈ Finset.range k, ((j.factorial : ℂ)⁻¹ • (s • N) ^ j) *ᵥ v := by
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := fun M => M *ᵥ v
      map_add' := fun M P => Matrix.add_mulVec M P v
      map_smul' := fun c M => Matrix.smul_mulVec c M v }
  let Lc : Matrix (Fin n) (Fin n) ℂ →L[ℂ] (Fin n → ℂ) :=
    LinearMap.toContinuousLinearMap L
  have hs := (exp_series_hasSum_exp' (𝕂 := ℂ) (s • N)).map Lc Lc.continuous
  have hN' : ((Matrix.toLin' N) ^ k) v = 0 := by
    rw [← Matrix.toLin'_pow, Matrix.toLin'_apply]
    exact hN
  change Lc (exp (s • N)) = _
  calc
    Lc (exp (s • N)) =
        ∑' j : ℕ, Lc ((j.factorial : ℂ)⁻¹ • (s • N) ^ j) := hs.tsum_eq.symm
    _ = ∑ j ∈ Finset.range k, Lc ((j.factorial : ℂ)⁻¹ • (s • N) ^ j) := by
      rw [tsum_eq_sum]
      intro j hj
      have hkj : k ≤ j := Nat.le_of_not_gt (by simpa using hj)
      have hjN : N ^ j *ᵥ v = 0 := by
        have := Module.End.pow_map_zero_of_le hkj hN'
        simpa only [← Matrix.toLin'_pow, Matrix.toLin'_apply] using this
      change (((j.factorial : ℂ)⁻¹ • (s • N) ^ j) *ᵥ v) = 0
      rw [Matrix.smul_mulVec, smul_pow, Matrix.smul_mulVec, hjN, smul_zero, smul_zero]
    _ = ∑ j ∈ Finset.range k, ((j.factorial : ℂ)⁻¹ • (s • N) ^ j) *ᵥ v := by
      rfl

lemma exp_smul_algebraMap_mulVec {n : ℕ} (μ s : ℂ) (v : Fin n → ℂ) :
    exp (s • (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) μ)) *ᵥ v =
      Complex.exp (s * μ) • v := by
  have hdiag :
      s • (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) μ) =
        Matrix.diagonal (fun _ : Fin n => s * μ) := by
    simp [Matrix.algebraMap_eq_diagonal, ← Matrix.diagonal_smul]
  rw [hdiag, Matrix.exp_diagonal]
  simp [Pi.exp_def, Complex.exp_eq_exp_ℂ]

lemma exists_exp_mulVec_eq_finset_sum_of_mem_maxGenEigenspace {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) (v : Fin n → ℂ)
    (hv : v ∈ Module.End.maxGenEigenspace (Matrix.toLin' B) μ) :
    ∃ (k : ℕ) (N : Matrix (Fin n) (Fin n) ℂ), N ^ k *ᵥ v = 0 ∧
      ∀ s : ℂ,
        exp (s • B) *ᵥ v =
          ∑ j ∈ Finset.range k,
            (Complex.exp (s * μ) * ((j.factorial : ℂ)⁻¹ * s ^ j)) •
              (N ^ j *ᵥ v) := by
  let e : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin n → ℂ) :=
    Matrix.toLinAlgEquiv'
  change v ∈ (e B).maxGenEigenspace μ at hv
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace (e B) μ v).mp hv
  let N : Matrix (Fin n) (Fin n) ℂ :=
    e.symm (e B - algebraMap ℂ (Module.End ℂ (Fin n → ℂ)) μ)
  have heN : e N = e B - algebraMap ℂ (Module.End ℂ (Fin n → ℂ)) μ := by
    exact e.apply_symm_apply _
  have hNlin : (e N ^ k) v = 0 := by
    rw [heN]
    simpa [Algebra.algebraMap_eq_smul_one] using hk
  have hN : N ^ k *ᵥ v = 0 := by
    rw [← Matrix.toLinAlgEquiv'_apply, map_pow, hNlin]
  refine ⟨k, N, hN, fun s => ?_⟩
  have hB : B = algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) μ + N := by
    apply e.injective
    rw [map_add, e.commutes, heN, add_comm, sub_add_cancel]
  have hcomm :
      Commute
        (s • algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) μ)
        (s • N) :=
    let hcentral : Commute
        (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) μ) N := Algebra.commutes μ N
    (hcentral.smul_left s).smul_right s
  calc
    exp (s • B) *ᵥ v =
        exp (s • algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) μ + s • N) *ᵥ v := by
      rw [hB, smul_add]
    _ = (exp (s • algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) μ) *
          exp (s • N)) *ᵥ v := by
      rw [Matrix.exp_add_of_commute _ _ hcomm]
    _ = exp (s • algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) μ) *ᵥ
          (exp (s • N) *ᵥ v) := (Matrix.mulVec_mulVec _ _ _).symm
    _ = Complex.exp (s * μ) • (exp (s • N) *ᵥ v) :=
      exp_smul_algebraMap_mulVec μ s _
    _ = Complex.exp (s * μ) •
          (∑ j ∈ Finset.range k, ((j.factorial : ℂ)⁻¹ • (s • N) ^ j) *ᵥ v) := by
      rw [exp_mulVec_of_pow_mulVec_eq_zero N v k hN s]
    _ = ∑ j ∈ Finset.range k,
          (Complex.exp (s * μ) * ((j.factorial : ℂ)⁻¹ * s ^ j)) •
            (N ^ j *ᵥ v) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Matrix.smul_mulVec, smul_pow, Matrix.smul_mulVec,
        smul_smul, smul_smul, mul_assoc]

lemma tendsto_exp_mulVec_of_mem_maxGenEigenspace {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) (hμ : μ.re < 0)
    (v : Fin n → ℂ)
    (hv : v ∈ Module.End.maxGenEigenspace (Matrix.toLin' B) μ) :
    Tendsto (fun t : ℝ => exp ((t : ℂ) • B) *ᵥ v) atTop (nhds 0) := by
  obtain ⟨k, N, hN, hform⟩ :=
    exists_exp_mulVec_eq_finset_sum_of_mem_maxGenEigenspace B μ v hv
  rw [show (fun t : ℝ => exp ((t : ℂ) • B) *ᵥ v) =
      fun t : ℝ => ∑ j ∈ Finset.range k,
        (Complex.exp ((t : ℂ) * μ) *
          ((j.factorial : ℂ)⁻¹ * (t : ℂ) ^ j)) • (N ^ j *ᵥ v) by
    funext t
    exact hform t]
  have hterms : ∀ j ∈ Finset.range k,
      Tendsto
        (fun t : ℝ => (Complex.exp ((t : ℂ) * μ) *
          ((j.factorial : ℂ)⁻¹ * (t : ℂ) ^ j)) • (N ^ j *ᵥ v))
        atTop (nhds 0) := by
    intro j hj
    have hc : Tendsto (fun _ : ℝ => (j.factorial : ℂ)⁻¹) atTop
        (nhds (j.factorial : ℂ)⁻¹) := tendsto_const_nhds
    have hscalar := hc.mul (tendsto_cexp_mul_pow μ hμ j)
    have hvector := hscalar.smul_const (N ^ j *ᵥ v)
    simpa [mul_assoc, mul_comm, mul_left_comm] using hvector
  simpa only [Finset.sum_const_zero] using
    tendsto_finsetSum (s := Finset.range k) hterms

lemma tendsto_exp_mulVec_of_eigenvalues_re_neg {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' B) μ → μ.re < 0)
    (v : Fin n → ℂ) :
    Tendsto (fun t : ℝ => exp ((t : ℂ) • B) *ᵥ v) atTop (nhds 0) := by
  let T : Module.End ℂ (Fin n → ℂ) := Matrix.toLin' B
  have hvtop : v ∈ (⊤ : Submodule ℂ (Fin n → ℂ)) := Submodule.mem_top
  rw [← T.iSup_maxGenEigenspace_eq_top] at hvtop
  obtain ⟨m, hm, hsum⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp T.maxGenEigenspace v).mp hvtop
  have hterms : ∀ μ ∈ m.support,
      Tendsto (fun t : ℝ => exp ((t : ℂ) • B) *ᵥ m μ) atTop (nhds 0) := by
    intro μ hμsupport
    by_cases hmμ : m μ = 0
    · simp [hmμ]
    · have hmax : T.maxGenEigenspace μ ≠ ⊥ := by
        intro hbot
        have hz : m μ ∈ (⊥ : Submodule ℂ (Fin n → ℂ)) := hbot ▸ hm μ
        exact hmμ (by simpa using hz)
      have hgen : T.HasGenEigenvalue μ (Module.finrank ℂ (Fin n → ℂ)) := by
        change T.genEigenspace μ (Module.finrank ℂ (Fin n → ℂ)) ≠ ⊥
        rw [← T.maxGenEigenspace_eq_genEigenspace_finrank]
        exact hmax
      have heig : T.HasEigenvalue μ :=
        Module.End.hasEigenvalue_of_hasGenEigenvalue hgen
      apply tendsto_exp_mulVec_of_mem_maxGenEigenspace B μ (hB μ (by simpa [T] using heig))
      simpa [T] using hm μ
  have hsum_tendsto :
      Tendsto
        (fun t : ℝ => ∑ μ ∈ m.support, exp ((t : ℂ) • B) *ᵥ m μ)
        atTop (nhds 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum (s := m.support) hterms
  convert hsum_tendsto using 1
  funext t
  rw [← hsum]
  change Matrix.toLin' (exp ((t : ℂ) • B))
      (m.sum fun _μ z => z) = ∑ μ ∈ m.support, exp ((t : ℂ) • B) *ᵥ m μ
  rw [map_finsuppSum]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma eq_exp_mulVec_of_hasDerivAt {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (y : ℝ → (Fin n → ℂ))
    (hy : ∀ t : ℝ, 0 < t → HasDerivAt y (B *ᵥ y t) t) :
    ∀ t : ℝ, 0 < t →
      y t = exp (t • B) *ᵥ (exp ((-1 : ℝ) • B) *ᵥ y 1) := by
  let E : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t => exp ((-t) • B)
  let g : ℝ → (Fin n → ℂ) := fun t => E t *ᵥ y t
  have hEentry : ∀ (t : ℝ) (i j : Fin n),
      HasDerivAt (fun r : ℝ => E r i j) ((-(E t * B)) i j) t := by
    intro t i j
    letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) :=
      Matrix.linftyOpNormedAddCommGroup
    letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedSpace
    letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) :=
      Matrix.linftyOpNormedAlgebra
    let ev : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
      { toFun := fun M => M i j
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let evc : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ :=
      ⟨ev, ev.continuous_of_finiteDimensional⟩
    have hneg : HasDerivAt (fun r : ℝ => -r) (-1) t := hasDerivAt_neg t
    have hcomp := (hasDerivAt_exp_smul_const B (-t)).scomp t hneg
    have hE : HasDerivAt E (-(E t * B)) t := by
      simpa [E, Function.comp_def] using hcomp
    have hev := evc.hasFDerivAt.comp_hasDerivAt t hE
    simpa [evc, ev, Function.comp_def] using hev
  have hg : ∀ t : ℝ, 0 < t → HasDerivAt g 0 t := by
    intro t ht
    have hgraw : HasDerivAt g
        ((-(E t * B)) *ᵥ y t + E t *ᵥ (B *ᵥ y t)) t := by
      rw [hasDerivAt_pi]
      intro i
      have hsum : HasDerivAt
          (fun r : ℝ => ∑ j : Fin n, E r i j * y r j)
          (∑ j : Fin n,
            ((-(E t * B)) i j * y t j + E t i j * (B *ᵥ y t) j)) t := by
        apply HasDerivAt.fun_sum
        intro j hj
        have hEij : HasDerivAt (fun r : ℝ => E r i j) ((-(E t * B)) i j) t :=
          hEentry t i j
        have hyj : HasDerivAt (fun r : ℝ => y r j) ((B *ᵥ y t) j) t :=
          hasDerivAt_pi.mp (hy t ht) j
        exact hEij.mul hyj
      simpa only [g, Matrix.mulVec, dotProduct, Pi.add_apply, Matrix.neg_apply,
        neg_mul, Finset.sum_add_distrib] using hsum
    apply hgraw.congr_deriv
    rw [Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, neg_add_cancel]
  have hgdiff : DifferentiableOn ℝ g (Set.Ioi 0) := by
    intro t ht
    exact (hg t ht).differentiableAt.differentiableWithinAt
  have hgderiv : Set.EqOn (deriv g) 0 (Set.Ioi 0) := by
    intro t ht
    exact (hg t ht).deriv
  intro t ht
  have hconst : g t = g 1 :=
    isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi hgdiff hgderiv ht
      (show (0 : ℝ) < 1 from zero_lt_one)
  have hcomm : Commute (t • B) ((-t) • B) :=
    let hself : Commute B B := Commute.refl B
    (hself.smul_left t).smul_right (-t)
  have hinv : exp (t • B) * exp ((-t) • B) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ hcomm]
    simp
  calc
    y t = exp (t • B) *ᵥ (E t *ᵥ y t) := by
      change y t = exp (t • B) *ᵥ (exp ((-t) • B) *ᵥ y t)
      rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    _ = exp (t • B) *ᵥ (E 1 *ᵥ y 1) :=
      congr_arg (fun z => exp (t • B) *ᵥ z) (by simpa [g] using hconst)
    _ = exp (t • B) *ᵥ (exp ((-1 : ℝ) • B) *ᵥ y 1) := by rfl

end

end Submission.Helpers
