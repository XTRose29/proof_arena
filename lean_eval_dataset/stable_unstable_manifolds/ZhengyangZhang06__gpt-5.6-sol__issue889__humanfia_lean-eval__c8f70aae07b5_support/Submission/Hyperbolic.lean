import Submission.Jordan

open scoped TensorProduct

namespace Submission.Hyperbolic

open Module Polynomial TensorProduct
open Submission.Jordan

set_option maxHeartbeats 800000

noncomputable section

private def tailShift (s : ℕ) (z : Fin s → ℂ) : Fin s → ℂ :=
  fun j =>
    if h : j.val + 1 < s then z ⟨j.val + 1, h⟩ else 0

private theorem norm_tailShift_le (s : ℕ) (z : Fin s → ℂ) :
    ‖tailShift s z‖ ≤ ‖z‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg z)]
  intro j
  by_cases h : j.val + 1 < s
  · exact (by simpa [tailShift, h] using norm_le_pi_norm z ⟨j.val + 1, h⟩)
  · simp [tailShift, h]

/-- A real finite-dimensional endomorphism whose complex characteristic
polynomial has no root on the unit circle admits a continuous quadratic
Lyapunov function which strictly increases away from the origin. -/
theorem exists_strict_quadratic
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A : Module.End ℝ V)
    (hhyper :
      ∀ μ ∈ (A.charpoly.map (algebraMap ℝ ℂ)).roots, ‖μ‖ ≠ 1) :
    ∃ q : V → ℝ, Continuous q ∧
      (∀ (r : ℝ), 0 ≤ r → ∀ v, q (r • v) = r ^ 2 * q v) ∧
      ∀ v ≠ 0, q v < q (A v) := by
  classical
  let g : Module.End ℂ (ℂ ⊗[ℝ] V) := A.baseChange ℂ
  let c : JordanChainBasis g := Classical.choice (jordanChainBasis g)
  have hc_hyper (i : c.ι) : ‖c.eigenvalue i‖ ≠ 1 := by
    let j₀ : Fin (c.size i) := ⟨0, c.positive_size i⟩
    have heig : g.HasEigenvalue (c.eigenvalue i) := by
      apply Module.End.hasEigenvalue_of_hasEigenvector
      rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
      refine ⟨?_, c.basis.ne_zero ⟨i, j₀⟩⟩
      simpa [j₀] using c.chain i j₀
    have hroot : g.charpoly.IsRoot (c.eigenvalue i) :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly g _).mp heig
    have hmem : c.eigenvalue i ∈ g.charpoly.roots :=
      (Polynomial.mem_roots g.charpoly_monic.ne_zero).mpr hroot
    exact hhyper _ (by simpa [g] using hmem)
  let ε : c.ι → ℝ := fun i => |‖c.eigenvalue i‖ - 1| / 2
  have hε (i : c.ι) : 0 < ε i := by
    dsimp [ε]
    exact div_pos (abs_pos.mpr (sub_ne_zero.mpr (hc_hyper i))) (by norm_num)
  let oneTmul : V →ₗ[ℝ] ℂ ⊗[ℝ] V := TensorProduct.mk ℝ ℂ V 1
  let block (i : c.ι) : V →ₗ[ℝ] (Fin (c.size i) → ℂ) :=
    { toFun := fun v j =>
        ((ε i : ℝ) : ℂ) ^ (c.size i - 1 - j.val) *
          c.basis.repr (oneTmul v) ⟨i, j⟩
      map_add' := by
        intro x y
        ext j
        simp [mul_add]
      map_smul' := by
        intro r x
        ext j
        change
          ((ε i : ℝ) : ℂ) ^ (c.size i - 1 - j.val) *
              c.basis.repr (oneTmul (r • x)) ⟨i, j⟩ =
            r • (((ε i : ℝ) : ℂ) ^ (c.size i - 1 - j.val) *
              c.basis.repr (oneTmul x) ⟨i, j⟩)
        rw [oneTmul.map_smul]
        rw [← IsScalarTower.algebraMap_smul ℂ r (oneTmul x)]
        rw [map_smul]
        change _ * ((r : ℂ) * _) = (r : ℂ) * (_ * _)
        ring }
  have hblock_image (i : c.ι) (v : V) :
      block i (A v) =
        c.eigenvalue i • block i v +
          ((ε i : ℝ) : ℂ) • tailShift (c.size i) (block i v) := by
    ext j
    have hone :
        oneTmul (A v) = g (oneTmul v) := by
      simp [oneTmul, g]
    change
      ((ε i : ℝ) : ℂ) ^ (c.size i - 1 - j.val) *
          c.basis.repr (oneTmul (A v)) ⟨i, j⟩ =
        (c.eigenvalue i • block i v +
          ((ε i : ℝ) : ℂ) • tailShift (c.size i) (block i v)) j
    rw [hone, c.repr_apply]
    by_cases hj : j.val + 1 < c.size i
    · have hexp :
          c.size i - 1 - j.val =
            (c.size i - 1 - (j.val + 1)) + 1 := by
          omega
      simp only [Pi.add_apply, Pi.smul_apply, tailShift, dif_pos hj]
      change
        ((ε i : ℝ) : ℂ) ^ (c.size i - 1 - j.val) *
              (c.eigenvalue i * c.basis.repr (oneTmul v) ⟨i, j⟩ +
                c.basis.repr (oneTmul v) ⟨i, ⟨j.val + 1, hj⟩⟩) =
          c.eigenvalue i *
              (((ε i : ℝ) : ℂ) ^ (c.size i - 1 - j.val) *
                c.basis.repr (oneTmul v) ⟨i, j⟩) +
            (ε i : ℂ) *
              (((ε i : ℝ) : ℂ) ^ (c.size i - 1 - (j.val + 1)) *
                c.basis.repr (oneTmul v) ⟨i, ⟨j.val + 1, hj⟩⟩)
      rw [hexp, pow_succ]
      ring
    · simp [tailShift, hj, block]
      ring
  have hnorm_upper (i : c.ι) (v : V) (hi : ‖c.eigenvalue i‖ < 1) :
      ‖block i (A v)‖ ≤
        ((‖c.eigenvalue i‖ + 1) / 2) * ‖block i v‖ := by
    let z := block i v
    have hgap : ε i = (1 - ‖c.eigenvalue i‖) / 2 := by
      simp [ε, abs_of_neg (sub_neg.mpr hi)]
    rw [hblock_image]
    calc
      ‖c.eigenvalue i • z +
          (ε i : ℂ) • tailShift (c.size i) z‖
          ≤ ‖c.eigenvalue i • z‖ +
              ‖(ε i : ℂ) • tailShift (c.size i) z‖ := norm_add_le _ _
      _ = ‖c.eigenvalue i‖ * ‖z‖ +
            ε i * ‖tailShift (c.size i) z‖ := by
          rw [norm_smul, norm_smul, Complex.norm_real,
            Real.norm_of_nonneg (hε i).le]
      _ ≤ ‖c.eigenvalue i‖ * ‖z‖ + ε i * ‖z‖ := by
          gcongr
          exact norm_tailShift_le _ _
      _ = ((‖c.eigenvalue i‖ + 1) / 2) * ‖z‖ := by
          rw [hgap]
          ring
  have hnorm_lower (i : c.ι) (v : V) (hi : 1 < ‖c.eigenvalue i‖) :
      ((‖c.eigenvalue i‖ + 1) / 2) * ‖block i v‖ ≤
        ‖block i (A v)‖ := by
    let z := block i v
    let e : Fin (c.size i) → ℂ :=
      (ε i : ℂ) • tailShift (c.size i) z
    have hgap : ε i = (‖c.eigenvalue i‖ - 1) / 2 := by
      simp [ε, abs_of_pos (sub_pos.mpr hi)]
    have he : ‖e‖ ≤ ε i * ‖z‖ := by
      calc
        ‖e‖ = ε i * ‖tailShift (c.size i) z‖ := by
          change
            ‖(ε i : ℂ) • tailShift (c.size i) z‖ =
              ε i * ‖tailShift (c.size i) z‖
          rw [norm_smul, Complex.norm_real,
            Real.norm_of_nonneg (hε i).le]
        _ ≤ ε i * ‖z‖ := by
          gcongr
          exact norm_tailShift_le _ _
    have hreverse :
        ‖c.eigenvalue i • z‖ - ‖e‖ ≤
          ‖c.eigenvalue i • z + e‖ := by
      simpa [sub_eq_add_neg, norm_neg] using
        norm_sub_norm_le (c.eigenvalue i • z) (-e)
    calc
      ((‖c.eigenvalue i‖ + 1) / 2) * ‖z‖ =
          ‖c.eigenvalue i‖ * ‖z‖ - ε i * ‖z‖ := by
            rw [hgap]
            ring
      _ ≤ ‖c.eigenvalue i • z‖ - ‖e‖ := by
          rw [norm_smul]
          linarith
      _ ≤ ‖c.eigenvalue i • z + e‖ := hreverse
      _ = ‖block i (A v)‖ := by
          rw [hblock_image]
  let part (i : c.ι) (v : V) : ℝ :=
    if ‖c.eigenvalue i‖ < 1 then -(‖block i v‖ ^ 2)
    else ‖block i v‖ ^ 2
  let q : V → ℝ := fun v => ∑ i, part i v
  have hq_cont : Continuous q := by
    dsimp [q]
    apply continuous_finsetSum
    intro i _
    have hb : Continuous (block i) :=
      (block i).continuous_of_finiteDimensional
    have hn : Continuous fun v => ‖block i v‖ :=
      continuous_norm.comp hb
    dsimp [part]
    split
    · exact (hn.pow 2).neg
    · exact hn.pow 2
  have hq_smul :
      ∀ (r : ℝ), 0 ≤ r → ∀ v, q (r • v) = r ^ 2 * q v := by
    intro r hr v
    dsimp [q, part]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [(block i).map_smul]
    have hnorm :
        ‖r • block i v‖ = r * ‖block i v‖ := by
      rw [norm_smul, Real.norm_of_nonneg hr]
    rw [hnorm]
    split <;> ring
  have hpart_nonneg (i : c.ι) (v : V) :
      0 ≤ part i (A v) - part i v := by
    by_cases hi : ‖c.eigenvalue i‖ < 1
    · have hρ : (‖c.eigenvalue i‖ + 1) / 2 ≤ 1 := by linarith
      have hn :
          ‖block i (A v)‖ ≤ ‖block i v‖ :=
        (hnorm_upper i v hi).trans
          (mul_le_of_le_one_left (norm_nonneg _) hρ)
      simp only [part, if_pos hi]
      nlinarith [norm_nonneg (block i (A v)), norm_nonneg (block i v)]
    · have hi' : 1 < ‖c.eigenvalue i‖ :=
        lt_of_le_of_ne (le_of_not_gt hi) (Ne.symm (hc_hyper i))
      have hρ : 1 ≤ (‖c.eigenvalue i‖ + 1) / 2 := by linarith
      have hscale' :
          ‖block i v‖ ≤
            ((‖c.eigenvalue i‖ + 1) / 2) * ‖block i v‖ := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hρ (norm_nonneg (block i v))
      have hn :
          ‖block i v‖ ≤ ‖block i (A v)‖ :=
        hscale'.trans (hnorm_lower i v hi')
      simp only [part, if_neg hi]
      nlinarith [norm_nonneg (block i (A v)), norm_nonneg (block i v)]
  have hpart_pos (i : c.ι) (v : V) (hv : block i v ≠ 0) :
      0 < part i (A v) - part i v := by
    by_cases hi : ‖c.eigenvalue i‖ < 1
    · have hρ : (‖c.eigenvalue i‖ + 1) / 2 < 1 := by linarith
      have hnpos : 0 < ‖block i v‖ := norm_pos_iff.mpr hv
      have hn :
          ‖block i (A v)‖ < ‖block i v‖ :=
        (hnorm_upper i v hi).trans_lt (by
          simpa using mul_lt_mul_of_pos_right hρ hnpos)
      simp only [part, if_pos hi]
      nlinarith [norm_nonneg (block i (A v))]
    · have hi' : 1 < ‖c.eigenvalue i‖ :=
        lt_of_le_of_ne (le_of_not_gt hi) (Ne.symm (hc_hyper i))
      have hρ : 1 < (‖c.eigenvalue i‖ + 1) / 2 := by linarith
      have hnpos : 0 < ‖block i v‖ := norm_pos_iff.mpr hv
      have hscale' :
          ‖block i v‖ <
            ((‖c.eigenvalue i‖ + 1) / 2) * ‖block i v‖ := by
        simpa only [one_mul] using mul_lt_mul_of_pos_right hρ hnpos
      have hn :
          ‖block i v‖ < ‖block i (A v)‖ :=
        hscale'.trans_le (hnorm_lower i v hi')
      simp only [part, if_neg hi]
      nlinarith [norm_nonneg (block i (A v))]
  have honeTmul_ne {v : V} (hv : v ≠ 0) : oneTmul v ≠ 0 := by
    let b := Module.Free.chooseBasis ℝ V
    have hvrepr : b.repr v ≠ 0 := fun h => hv (b.repr.injective (by simpa using h))
    obtain ⟨k, hk⟩ : ∃ k, b.repr v k ≠ 0 := by
      by_contra h
      apply hvrepr
      ext k
      by_contra hk
      exact h ⟨k, hk⟩
    let l : V →ₗ[ℝ] ℂ :=
      Complex.ofRealCLM.toLinearMap.comp (b.coord k)
    have hlv : l v ≠ 0 := by
      simpa [l] using hk
    intro hzero
    apply hlv
    have happly := congrArg (fun w => l.liftBaseChange ℂ w) hzero
    simpa [oneTmul, l, LinearMap.liftBaseChange_one_tmul] using happly
  have hexists_block {v : V} (hv : v ≠ 0) :
      ∃ i, block i v ≠ 0 := by
    by_contra h
    have hzero (i : c.ι) : block i v = 0 := by
      by_contra hi
      exact h ⟨i, hi⟩
    have hrepr : c.basis.repr (oneTmul v) = 0 := by
      ext p
      rcases p with ⟨i, j⟩
      have hij := congrFun (hzero i) j
      change
        ((ε i : ℝ) : ℂ) ^ (c.size i - 1 - j.val) *
            c.basis.repr (oneTmul v) ⟨i, j⟩ = 0 at hij
      have he : ((ε i : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (hε i))
      exact (mul_eq_zero.mp hij).resolve_left (pow_ne_zero _ he)
    apply honeTmul_ne hv
    exact c.basis.repr.injective (by simpa using hrepr)
  refine ⟨q, hq_cont, hq_smul, ?_⟩
  intro v hv
  obtain ⟨i, hi⟩ := hexists_block hv
  have hsum :
      0 < ∑ i, (part i (A v) - part i v) :=
    Finset.sum_pos'
      (fun i _ => hpart_nonneg i v)
      ⟨i, Finset.mem_univ i, hpart_pos i v hi⟩
  dsimp [q]
  rw [← sub_pos, ← Finset.sum_sub_distrib]
  exact hsum

end

end Submission.Hyperbolic
