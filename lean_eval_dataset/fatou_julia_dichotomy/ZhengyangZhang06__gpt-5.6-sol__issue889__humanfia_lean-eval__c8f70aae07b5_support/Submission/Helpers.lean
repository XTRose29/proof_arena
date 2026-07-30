import ChallengeDeps

open LeanEval.ComplexAnalysis.FatouJuliaProblem

namespace Submission.Helpers

noncomputable section

open Topology

def escapeRadius (c : ℂ) : ℝ := ‖c‖ + 2

lemma mandelbrot_iff_zero_mem_filledJulia (c : ℂ) :
    c ∈ Mandelbrot ↔ 0 ∈ FilledJulia c :=
  Iff.rfl

lemma tc_mem_filledJulia_iff (c z : ℂ) :
    Tc c z ∈ FilledJulia c ↔ z ∈ FilledJulia c := by
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨max M ‖z‖, fun n => ?_⟩
    cases n with
    | zero => simp
    | succ n =>
        rw [Function.iterate_succ_apply]
        exact (hM n).trans (le_max_left _ _)
  · rintro ⟨M, hM⟩
    refine ⟨M, fun n => ?_⟩
    rw [← Function.iterate_succ_apply]
    exact hM n.succ

lemma norm_add_one_lt_norm_tc_of_escape {c z : ℂ}
    (hz : escapeRadius c < ‖z‖) : ‖z‖ + 1 < ‖Tc c z‖ := by
  have hnum : ‖z‖ + 1 < ‖z‖ ^ 2 - ‖c‖ := by
    dsimp [escapeRadius] at hz
    nlinarith [norm_nonneg c, norm_nonneg z, sq_nonneg (‖z‖ - 1)]
  refine hnum.trans_le ?_
  calc
    ‖z‖ ^ 2 - ‖c‖ = ‖z ^ 2‖ - ‖-c‖ := by simp
    _ ≤ ‖z ^ 2 - -c‖ := norm_sub_norm_le _ _
    _ = ‖Tc c z‖ := by simp [Tc]

lemma norm_add_nat_le_norm_iterate_of_escape {c z : ℂ}
    (hz : escapeRadius c < ‖z‖) (n : ℕ) :
    ‖z‖ + n ≤ ‖(Tc c)^[n] z‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hR : escapeRadius c < ‖(Tc c)^[n] z‖ :=
        hz.trans_le ((le_add_of_nonneg_right (Nat.cast_nonneg n)).trans ih)
      have hstep := norm_add_one_lt_norm_tc_of_escape hR
      have hstep' : ‖(Tc c)^[n] z‖ + 1 < ‖(Tc c)^[n.succ] z‖ := by
        simpa only [Function.iterate_succ_apply'] using hstep
      calc
        ‖z‖ + (n.succ : ℝ) = (‖z‖ + n) + 1 := by push_cast; ring
        _ ≤ ‖(Tc c)^[n] z‖ + 1 := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right ih 1
        _ ≤ ‖(Tc c)^[n.succ] z‖ := hstep'.le

lemma mem_filledJulia_iff_forall_norm_le_escapeRadius (c z : ℂ) :
    z ∈ FilledJulia c ↔ ∀ n : ℕ, ‖(Tc c)^[n] z‖ ≤ escapeRadius c := by
  constructor
  · rintro ⟨M, hM⟩ n
    by_contra! hn
    obtain ⟨k, hk⟩ := exists_nat_gt M
    have hgrowth := norm_add_nat_le_norm_iterate_of_escape hn k
    have hbound := hM (k + n)
    rw [Function.iterate_add_apply] at hbound
    have hk' : M < ‖(Tc c)^[n] z‖ + k := by
      exact hk.trans_le (le_add_of_nonneg_left (norm_nonneg _))
    exact (not_le_of_gt (hk'.trans_le hgrowth)) hbound
  · intro h
    exact ⟨escapeRadius c, h⟩

lemma filledJulia_eq_iInter_closedBall (c : ℂ) :
    FilledJulia c = ⋂ n : ℕ, (Tc c)^[n] ⁻¹' Metric.closedBall 0 (escapeRadius c) := by
  ext z
  rw [mem_filledJulia_iff_forall_norm_le_escapeRadius]
  simp only [Set.mem_iInter, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]

lemma isClosed_filledJulia (c : ℂ) : IsClosed (FilledJulia c) := by
  rw [filledJulia_eq_iInter_closedBall]
  apply isClosed_iInter
  intro n
  have hTc : Continuous (Tc c) := by
    unfold Tc
    fun_prop
  exact Metric.isClosed_closedBall.preimage (hTc.iterate n)

lemma filledJulia_subset_closedBall (c : ℂ) :
    FilledJulia c ⊆ Metric.closedBall 0 (escapeRadius c) := by
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  simpa using (mem_filledJulia_iff_forall_norm_le_escapeRadius c z).1 hz 0

lemma isBounded_filledJulia (c : ℂ) : Bornology.IsBounded (FilledJulia c) :=
  Metric.isBounded_closedBall.subset (filledJulia_subset_closedBall c)

lemma isCompact_filledJulia (c : ℂ) : IsCompact (FilledJulia c) :=
  Metric.isCompact_iff_isClosed_bounded.2 ⟨isClosed_filledJulia c, isBounded_filledJulia c⟩

def tcOnFilledJulia (c : ℂ) : FilledJulia c → FilledJulia c := fun z =>
  ⟨Tc c z, (tc_mem_filledJulia_iff c z).2 z.property⟩

lemma continuous_tcOnFilledJulia (c : ℂ) : Continuous (tcOnFilledJulia c) := by
  apply Continuous.subtype_mk
  exact (by unfold Tc; fun_prop : Continuous (Tc c)).comp continuous_subtype_val

lemma filledJulia_nonempty (c : ℂ) : (FilledJulia c).Nonempty := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (1 - 4 * c) zero_lt_two
  let z := (1 + s) / 2
  have hfix : Function.IsFixedPt (Tc c) z := by
    change ((1 + s) / 2) ^ 2 + c = (1 + s) / 2
    field_simp
    linear_combination hs
  refine ⟨z, ‖z‖, fun n => ?_⟩
  rw [Function.iterate_fixed hfix]

noncomputable instance filledJuliaNonempty (c : ℂ) : Nonempty (FilledJulia c) :=
  Set.nonempty_coe_sort.mpr (filledJulia_nonempty c)

instance filledJuliaCompactSpace (c : ℂ) : CompactSpace (FilledJulia c) :=
  isCompact_iff_compactSpace.mp (isCompact_filledJulia c)

lemma norm_criticalOrbit_le_escapeRadius_of_mem_mandelbrot {c : ℂ} (hc : c ∈ Mandelbrot)
    (n : ℕ) : ‖(Tc c)^[n] 0‖ ≤ escapeRadius c :=
  (mem_filledJulia_iff_forall_norm_le_escapeRadius c 0).1
    ((mandelbrot_iff_zero_mem_filledJulia c).1 hc) n

lemma exists_norm_criticalOrbit_gt_escapeRadius_of_not_mem_mandelbrot {c : ℂ}
    (hc : c ∉ Mandelbrot) : ∃ n : ℕ, escapeRadius c < ‖(Tc c)^[n] 0‖ := by
  by_contra! h
  apply hc
  apply (mandelbrot_iff_zero_mem_filledJulia c).2
  exact (mem_filledJulia_iff_forall_norm_le_escapeRadius c 0).2 h

end

end Submission.Helpers
