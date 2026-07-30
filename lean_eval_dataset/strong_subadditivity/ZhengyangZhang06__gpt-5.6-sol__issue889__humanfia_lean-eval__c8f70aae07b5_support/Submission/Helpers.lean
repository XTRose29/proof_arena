import ChallengeDeps

namespace Submission.Helpers

open LeanEval.Physics
open ComplexOrder
open scoped BigOperators
open scoped Matrix.Norms.L2Operator
open scoped Topology

noncomputable section

variable {X Y : Type*}

lemma posSemidef_reindex (M : Matrix X X ℂ) (hM : M.PosSemidef) (e : X ≃ Y) :
    (M.reindex e e).PosSemidef := by
  rw [Matrix.reindex_apply]
  exact hM.submatrix e.symm

lemma posDef_reindex (M : Matrix X X ℂ) (hM : M.PosDef) (e : X ≃ Y) :
    (M.reindex e e).PosDef := by
  rw [Matrix.reindex_apply]
  exact hM.submatrix e.symm.injective

variable [Fintype X] [Fintype Y]
variable [DecidableEq X] [DecidableEq Y]

omit [Fintype Y] [DecidableEq X] [DecidableEq Y] in
lemma posSemidef_traceLeft (M : Matrix (X × Y) (X × Y) ℂ) (hM : M.PosSemidef) :
    M.traceLeft.PosSemidef := by
  have htrace :
      M.traceLeft = ∑ x : X, M.submatrix (fun y : Y ↦ (x, y)) (fun y : Y ↦ (x, y)) := by
    ext i j
    simp [Matrix.traceLeft, Matrix.sum_apply]
  rw [htrace]
  exact Matrix.posSemidef_sum Finset.univ fun x _ ↦ hM.submatrix (fun y : Y ↦ (x, y))

omit [Fintype X] [DecidableEq X] [DecidableEq Y] in
lemma posSemidef_traceRight (M : Matrix (X × Y) (X × Y) ℂ) (hM : M.PosSemidef) :
    M.traceRight.PosSemidef := by
  have htrace :
      M.traceRight = ∑ y : Y, M.submatrix (fun x : X ↦ (x, y)) (fun x : X ↦ (x, y)) := by
    ext i j
    simp [Matrix.traceRight, Matrix.sum_apply]
  rw [htrace]
  exact Matrix.posSemidef_sum Finset.univ fun y _ ↦ hM.submatrix (fun x : X ↦ (x, y))

omit [Fintype Y] [DecidableEq X] [DecidableEq Y] in
lemma posDef_traceLeft [Nonempty X] (M : Matrix (X × Y) (X × Y) ℂ) (hM : M.PosDef) :
    M.traceLeft.PosDef := by
  have htrace :
      M.traceLeft = ∑ x : X, M.submatrix (fun y : Y ↦ (x, y)) (fun y : Y ↦ (x, y)) := by
    ext i j
    simp [Matrix.traceLeft, Matrix.sum_apply]
  rw [htrace]
  exact Matrix.posDef_sum Finset.univ_nonempty fun x _ ↦ hM.submatrix (by
    intro i j hij
    exact (Prod.mk.inj hij).2)

omit [Fintype X] [DecidableEq X] [DecidableEq Y] in
lemma posDef_traceRight [Nonempty Y] (M : Matrix (X × Y) (X × Y) ℂ) (hM : M.PosDef) :
    M.traceRight.PosDef := by
  have htrace :
      M.traceRight = ∑ y : Y, M.submatrix (fun x : X ↦ (x, y)) (fun x : X ↦ (x, y)) := by
    ext i j
    simp [Matrix.traceRight, Matrix.sum_apply]
  rw [htrace]
  exact Matrix.posDef_sum Finset.univ_nonempty fun y _ ↦ hM.submatrix (by
    intro i j hij
    exact (Prod.mk.inj hij).1)

omit [Fintype X] in
lemma posDef_add_smul_one (M : Matrix X X ℂ) (hM : M.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    (M + ε • (1 : Matrix X X ℂ)).PosDef :=
  Matrix.PosDef.posSemidef_add hM (Matrix.PosDef.one.smul hε)

local instance matrixCStarAlgebra : CStarAlgebra (Matrix X X ℂ) := {
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance }

lemma mul_cfc_log_eq_cfc_mul_log (M : Matrix X X ℂ) (hM : M.IsHermitian) :
    M * cfc Real.log M = cfc (fun x : ℝ ↦ x * Real.log x) M := by
  have hlog : ContinuousOn Real.log (spectrum ℝ M) :=
    M.finite_real_spectrum.continuousOn Real.log
  calc
    M * cfc Real.log M =
        cfc (fun x : ℝ ↦ x) M * cfc Real.log M := by
      rw [cfc_id' ℝ M hM.isSelfAdjoint]
    _ = cfc (fun x : ℝ ↦ x * Real.log x) M :=
      (cfc_mul (fun x : ℝ ↦ x) Real.log M (hg := hlog)).symm

lemma entropy_eq_neg_re_trace_cfc_mul_log (M : Matrix X X ℂ) (hM : M.IsHermitian) :
    entropy M = -Complex.re (Matrix.trace (cfc (fun x : ℝ ↦ x * Real.log x) M)) := by
  rw [entropy, mul_cfc_log_eq_cfc_mul_log M hM]

set_option maxHeartbeats 1000000 in
lemma continuousOn_entropy_posSemidef :
    ContinuousOn entropy {M : Matrix X X ℂ | M.PosSemidef} := by
  have hcfc :
      ContinuousOn
        (fun M : Matrix X X ℂ ↦ cfc (fun x : ℝ ↦ x * Real.log x) M)
        {M : Matrix X X ℂ | M.PosSemidef} := by
    exact ContinuousOn.cfc_of_mem_nhdsSet (𝕜 := ℝ) (A := Matrix X X ℂ)
      (p := IsSelfAdjoint) (s := Set.univ)
      (fun x : ℝ ↦ x * Real.log x) Filter.univ_mem continuousOn_id
      (ha' := fun M hM ↦ hM.isHermitian.isSelfAdjoint)
      (hf := Real.continuous_mul_log.continuousOn)
  have htrace : Continuous (fun N : Matrix X X ℂ ↦ Matrix.trace N) := by
    unfold Matrix.trace Matrix.diag
    fun_prop
  have hrhs :
      ContinuousOn
        (fun M : Matrix X X ℂ ↦
          -Complex.re (Matrix.trace (cfc (fun x : ℝ ↦ x * Real.log x) M)))
        {M : Matrix X X ℂ | M.PosSemidef} :=
    (Complex.continuous_re.comp_continuousOn (htrace.comp_continuousOn hcfc)).neg
  exact hrhs.congr fun M hM ↦
    entropy_eq_neg_re_trace_cfc_mul_log M hM.isHermitian

lemma tendsto_entropy_of_tendsto_posSemidef {ι : Type*} {l : Filter ι}
    (N : ι → Matrix X X ℂ) (M : Matrix X X ℂ) (hN : Filter.Tendsto N l (𝓝 M))
    (hNpos : ∀ i, (N i).PosSemidef) (hM : M.PosSemidef) :
    Filter.Tendsto (fun i ↦ entropy (N i)) l (𝓝 (entropy M)) := by
  have hN' :
      Filter.Tendsto N l (𝓝[{M : Matrix X X ℂ | M.PosSemidef}] M) :=
    tendsto_nhdsWithin_iff.mpr ⟨hN, Filter.Eventually.of_forall hNpos⟩
  exact (continuousOn_entropy_posSemidef M hM).tendsto.comp hN'

end

end Submission.Helpers
