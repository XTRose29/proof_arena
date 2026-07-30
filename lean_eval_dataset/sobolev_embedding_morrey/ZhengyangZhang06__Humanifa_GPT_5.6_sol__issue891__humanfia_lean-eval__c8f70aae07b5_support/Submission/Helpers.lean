import ChallengeDeps

namespace Submission.Helpers

open LeanEval.Analysis.SobolevMorreyProblem
open MeasureTheory
open scoped ENNReal NNReal

/-- Functions taking one fixed value satisfy the benchmark's global Hölder-space predicate. -/
theorem memHolder_const {n r : ℕ} {α : ℝ} (c : ℝ) :
    MemHolder (n := n) r α (fun _ : E n ↦ c) := by
  refine ⟨contDiff_const, ?_, ?_⟩
  · refine ⟨0, ?_⟩
    cases r with
    | zero =>
        rw [iteratedFDeriv_zero_eq_comp]
        exact HolderWith.const
    | succ r =>
        rw [iteratedFDeriv_succ_const]
        exact HolderWith.zero
  intro j _hj
  cases j with
  | zero =>
      refine ⟨‖c‖, fun x ↦ ?_⟩
      simp
  | succ j =>
      refine ⟨0, fun x ↦ ?_⟩
      simp [iteratedFDeriv_succ_const]

/-- Every real-valued function on the zero-dimensional model space takes one value. -/
theorem memHolder_zero_dim {r : ℕ} {α : ℝ} (f : E 0 → ℝ) :
    MemHolder r α f := by
  have hf : f = fun _ ↦ f 0 := by
    funext x
    rw [Subsingleton.elim x 0]
  rw [hf]
  exact memHolder_const (f 0)

/-- The mixed derivative indexed by the zero multi-index is the original
test function. -/
theorem mixedDeriv_zero {n : ℕ} (φ : E n → ℝ) :
    mixedDeriv (fun _ ↦ 0) φ = φ := by
  simp [mixedDeriv]

/-- The multi-index with one derivative in coordinate `i`. -/
def coordMulti {n : ℕ} (i : Fin n) : Fin n → ℕ :=
  fun j ↦ if j = i then 1 else 0

private theorem foldr_coordMulti {n : ℕ} (i : Fin n) (φ : E n → ℝ)
    (l : List (Fin n)) (hl : l.Nodup) :
    l.foldr (fun j ψ ↦ (partialDeriv j)^[coordMulti i j] ψ) φ =
      if i ∈ l then partialDeriv i φ else φ := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have htail := hl.tail
      rw [List.foldr_cons, ih htail]
      by_cases hai : a = i
      · subst a
        have hnot : i ∉ l := by
          exact (List.nodup_cons.mp hl).1
        simp [coordMulti, hnot]
      · have hia : i ≠ a := Ne.symm hai
        simp [coordMulti, hai, hia]

theorem mixedDeriv_coordMulti {n : ℕ} (i : Fin n) (φ : E n → ℝ) :
    mixedDeriv (coordMulti i) φ = partialDeriv i φ := by
  rw [mixedDeriv, foldr_coordMulti i φ (List.finRange n) (List.nodup_finRange n)]
  simp

theorem sum_coordMulti {n : ℕ} (i : Fin n) :
    ∑ j, coordMulti i j = 1 := by
  simp [coordMulti]

theorem IsWeakDeriv.integral_mul_partialDeriv_eq_neg {n : ℕ}
    {u g : E n → ℝ} {i : Fin n} (hug : IsWeakDeriv u g (coordMulti i))
    (φ : E n → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    ∫ x, u x * partialDeriv i φ x = -∫ x, g x * φ x := by
  simpa only [mixedDeriv_coordMulti, sum_coordMulti, pow_one, neg_one_mul] using
    hug φ hφ hφc

/-- The order-zero weak derivative in `MemSobolevWk` supplies an actual
`Lᵖ` representative of the original locally integrable function. -/
theorem MemSobolevWk.exists_aeEq_memLp {n k : ℕ} {p : ℝ≥0∞} {f : E n → ℝ}
    (hf : MemSobolevWk k p f) (hp : 1 ≤ p) :
    ∃ g : E n → ℝ, f =ᵐ[volume] g ∧ MemLp g p volume := by
  obtain ⟨g, hfg, hg⟩ := hf.2 (fun _ ↦ 0) (by simp)
  refine ⟨g, ?_, hg⟩
  apply ae_eq_of_integral_contDiff_smul_eq hf.1 (hg.locallyIntegrable hp)
  intro φ hφ hφc
  simpa [mixedDeriv_zero, smul_eq_mul, mul_comm] using hfg φ hφ hφc

/-- Locally integrable representatives of the same weak derivative agree
almost everywhere. -/
theorem IsWeakDeriv.ae_eq {n : ℕ} {u f g : E n → ℝ} {m : Fin n → ℕ}
    (huf : IsWeakDeriv u f m) (hug : IsWeakDeriv u g m)
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume) :
    f =ᵐ[volume] g := by
  apply ae_eq_of_integral_contDiff_smul_eq hf hg
  intro φ hφ hφc
  have h :=
    (huf φ hφ hφc).symm.trans (hug φ hφ hφc)
  have hsign : ((-1 : ℝ) ^ (∑ i, m i)) ≠ 0 := pow_ne_zero _ (by norm_num)
  simpa [smul_eq_mul, mul_comm] using mul_left_cancel₀ hsign h

/-- A fixed representative for each weak derivative supplied by Sobolev
membership. -/
noncomputable def MemSobolevWk.derivRep {n k : ℕ} {p : ℝ≥0∞} {f : E n → ℝ}
    (hf : MemSobolevWk k p f) (m : Fin n → ℕ) (hm : (∑ i, m i) ≤ k) :
    E n → ℝ :=
  Classical.choose (hf.2 m hm)

theorem MemSobolevWk.isWeakDeriv_derivRep {n k : ℕ} {p : ℝ≥0∞} {f : E n → ℝ}
    (hf : MemSobolevWk k p f) (m : Fin n → ℕ) (hm : (∑ i, m i) ≤ k) :
    IsWeakDeriv f (Submission.Helpers.MemSobolevWk.derivRep hf m hm) m :=
  (Classical.choose_spec (hf.2 m hm)).1

theorem MemSobolevWk.memLp_derivRep {n k : ℕ} {p : ℝ≥0∞} {f : E n → ℝ}
    (hf : MemSobolevWk k p f) (m : Fin n → ℕ) (hm : (∑ i, m i) ≤ k) :
    MemLp (Submission.Helpers.MemSobolevWk.derivRep hf m hm) p volume :=
  (Classical.choose_spec (hf.2 m hm)).2

/-- The numerical Morrey gap always supplies at least one derivative beyond
the requested classical differentiability order. -/
theorem succ_le_of_morrey_gap {n k r : ℕ} {α p : ℝ}
    (hp : (n : ℝ) < p) (hα : 0 < α)
    (hgap : (r : ℝ) + α < (k : ℝ) - n / p) :
    r + 1 ≤ k := by
  have hp0 : 0 < p := (Nat.cast_nonneg n).trans_lt hp
  have hn_div_nonneg : 0 ≤ (n : ℝ) / p := div_nonneg (Nat.cast_nonneg n) hp0.le
  have hrk : (r : ℝ) < k := by linarith
  have hrk_nat : r < k := by exact_mod_cast hrk
  exact Nat.succ_le_iff.mpr hrk_nat

/-- In positive dimension, the real Morrey assumption `n < p` places the
extended-real exponent in the locally integrable range. -/
theorem one_le_ofReal_of_dim_pos {n : ℕ} {p : ℝ}
    (hn : 0 < n) (hp : (n : ℝ) < p) :
    1 ≤ ENNReal.ofReal p := by
  rw [ENNReal.one_le_ofReal]
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (Nat.succ_le_iff.mpr hn)
  exact hn1.trans hp.le

end Submission.Helpers
