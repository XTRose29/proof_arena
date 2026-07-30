import Submission.Helpers

namespace Submission.Reduction

open LeanEval.Physics
open ComplexOrder
open Filter
open scoped Topology

noncomputable section

variable {A B C : Type*}
variable [Fintype A] [Fintype B] [Fintype C]
variable [DecidableEq A] [DecidableEq B] [DecidableEq C]
variable [Nonempty A] [Nonempty B] [Nonempty C]

def marginalAB (M : Matrix (A × B × C) (A × B × C) ℂ) :
    Matrix (A × B) (A × B) ℂ :=
  (M.reindex (.symm <| .prodAssoc A B C) (.symm <| .prodAssoc A B C)).traceRight

def marginalBC (M : Matrix (A × B × C) (A × B × C) ℂ) : Matrix (B × C) (B × C) ℂ :=
  M.traceLeft

def marginalB (M : Matrix (A × B × C) (A × B × C) ℂ) : Matrix B B ℂ :=
  (marginalBC M).traceRight

def SSA (M : Matrix (A × B × C) (A × B × C) ℂ) : Prop :=
  entropy M + entropy (marginalB M) ≤ entropy (marginalAB M) + entropy (marginalBC M)

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [Nonempty A] [Nonempty B] [Nonempty C] in
lemma continuous_marginalAB :
    Continuous (marginalAB : Matrix (A × B × C) (A × B × C) ℂ →
      Matrix (A × B) (A × B) ℂ) := by
  change Continuous
    (fun M : Matrix (A × (B × C)) (A × (B × C)) ℂ ↦
      fun (i j : A × B) ↦ ∑ k, M (i.1, (i.2, k)) (j.1, (j.2, k)))
  fun_prop

omit [Fintype B] [Fintype C] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [Nonempty A] [Nonempty B] [Nonempty C] in
lemma continuous_marginalBC :
    Continuous (marginalBC : Matrix (A × B × C) (A × B × C) ℂ →
      Matrix (B × C) (B × C) ℂ) := by
  unfold marginalBC Matrix.traceLeft
  fun_prop

omit [Fintype B] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [Nonempty A] [Nonempty B] [Nonempty C] in
lemma continuous_marginalB :
    Continuous (marginalB : Matrix (A × B × C) (A × B × C) ℂ → Matrix B B ℂ) := by
  change Continuous
    (fun M : Matrix (A × (B × C)) (A × (B × C)) ℂ ↦
      fun i j ↦ ∑ c, ∑ a, M (a, (i, c)) (a, (j, c)))
  fun_prop

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [Nonempty A] [Nonempty B] [Nonempty C] in
lemma posSemidef_marginalAB (M : Matrix (A × B × C) (A × B × C) ℂ)
    (hM : M.PosSemidef) : (marginalAB M).PosSemidef := by
  unfold marginalAB
  exact Submission.Helpers.posSemidef_traceRight _
    (Submission.Helpers.posSemidef_reindex M hM _)

omit [Fintype B] [Fintype C] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [Nonempty A] [Nonempty B] [Nonempty C] in
lemma posSemidef_marginalBC (M : Matrix (A × B × C) (A × B × C) ℂ)
    (hM : M.PosSemidef) : (marginalBC M).PosSemidef := by
  exact Submission.Helpers.posSemidef_traceLeft M hM

omit [Fintype B] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [Nonempty A] [Nonempty B] [Nonempty C] in
lemma posSemidef_marginalB (M : Matrix (A × B × C) (A × B × C) ℂ)
    (hM : M.PosSemidef) : (marginalB M).PosSemidef := by
  exact Submission.Helpers.posSemidef_traceRight _
    (posSemidef_marginalBC M hM)

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [Nonempty A] [Nonempty B] in
lemma posDef_marginalAB (M : Matrix (A × B × C) (A × B × C) ℂ)
    (hM : M.PosDef) : (marginalAB M).PosDef := by
  unfold marginalAB
  exact Submission.Helpers.posDef_traceRight _
    (Submission.Helpers.posDef_reindex M hM _)

omit [Fintype B] [Fintype C] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [Nonempty B] [Nonempty C] in
lemma posDef_marginalBC (M : Matrix (A × B × C) (A × B × C) ℂ)
    (hM : M.PosDef) : (marginalBC M).PosDef := by
  exact Submission.Helpers.posDef_traceLeft M hM

omit [Fintype B] [DecidableEq A] [DecidableEq B] [DecidableEq C] [Nonempty B] in
lemma posDef_marginalB (M : Matrix (A × B × C) (A × B × C) ℂ)
    (hM : M.PosDef) : (marginalB M).PosDef := by
  exact Submission.Helpers.posDef_traceRight _ (posDef_marginalBC M hM)

omit [Nonempty B] in
theorem ssa_of_posDef
    (hcore : ∀ (M : Matrix (A × B × C) (A × B × C) ℂ), M.PosDef → SSA M)
    (M : Matrix (A × B × C) (A × B × C) ℂ) (hM : M.PosSemidef) :
    SSA M := by
  let ε : ℕ → ℝ := fun n ↦ ((n + 1 : ℕ) : ℝ)⁻¹
  let reg : ℕ → Matrix (A × B × C) (A × B × C) ℂ :=
    fun n ↦ M + ε n • (1 : Matrix (A × B × C) (A × B × C) ℂ)

  have hεpos (n : ℕ) : 0 < ε n := by
    dsimp [ε]
    positivity
  have hregPos (n : ℕ) : (reg n).PosDef := by
    exact Submission.Helpers.posDef_add_smul_one M hM (hεpos n)
  have hε :
      Tendsto ε atTop (𝓝 0) := by
    simpa [ε] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hreg :
      Tendsto reg atTop (𝓝 M) := by
    simpa [reg] using
      tendsto_const_nhds.add
        (hε.smul_const (1 : Matrix (A × B × C) (A × B × C) ℂ))

  have hAB :
      Tendsto (fun n ↦ marginalAB (reg n)) atTop (𝓝 (marginalAB M)) :=
    continuous_marginalAB.continuousAt.tendsto.comp hreg
  have hBC :
      Tendsto (fun n ↦ marginalBC (reg n)) atTop (𝓝 (marginalBC M)) :=
    continuous_marginalBC.continuousAt.tendsto.comp hreg
  have hB :
      Tendsto (fun n ↦ marginalB (reg n)) atTop (𝓝 (marginalB M)) :=
    continuous_marginalB.continuousAt.tendsto.comp hreg

  have hEntropy :
      Tendsto (fun n ↦ entropy (reg n)) atTop (𝓝 (entropy M)) :=
    Submission.Helpers.tendsto_entropy_of_tendsto_posSemidef reg M hreg
      (fun n ↦ (hregPos n).posSemidef) hM
  have hEntropyAB :
      Tendsto (fun n ↦ entropy (marginalAB (reg n))) atTop
        (𝓝 (entropy (marginalAB M))) :=
    Submission.Helpers.tendsto_entropy_of_tendsto_posSemidef
      (fun n ↦ marginalAB (reg n)) (marginalAB M) hAB
      (fun n ↦ (posDef_marginalAB (reg n) (hregPos n)).posSemidef)
      (posSemidef_marginalAB M hM)
  have hEntropyBC :
      Tendsto (fun n ↦ entropy (marginalBC (reg n))) atTop
        (𝓝 (entropy (marginalBC M))) :=
    Submission.Helpers.tendsto_entropy_of_tendsto_posSemidef
      (fun n ↦ marginalBC (reg n)) (marginalBC M) hBC
      (fun n ↦ (posDef_marginalBC (reg n) (hregPos n)).posSemidef)
      (posSemidef_marginalBC M hM)
  have hEntropyB :
      Tendsto (fun n ↦ entropy (marginalB (reg n))) atTop
        (𝓝 (entropy (marginalB M))) :=
    Submission.Helpers.tendsto_entropy_of_tendsto_posSemidef
      (fun n ↦ marginalB (reg n)) (marginalB M) hB
      (fun n ↦ (posDef_marginalB (reg n) (hregPos n)).posSemidef)
      (posSemidef_marginalB M hM)

  apply le_of_tendsto_of_tendsto (hEntropy.add hEntropyB) (hEntropyAB.add hEntropyBC)
  exact Eventually.of_forall fun n ↦ hcore (reg n) (hregPos n)

end

end Submission.Reduction
