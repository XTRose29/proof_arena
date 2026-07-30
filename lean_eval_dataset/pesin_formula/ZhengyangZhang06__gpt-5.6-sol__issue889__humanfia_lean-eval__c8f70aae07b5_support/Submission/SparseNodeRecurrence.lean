import Submission.WeightedPesinRecurrence

namespace Submission.Helpers

def pathPrev {N : ℕ} (i : Fin (N + 1)) : Fin (N + 1) :=
  ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩

def pathNext {N : ℕ} (i : Fin (N + 1)) : Fin (N + 1) :=
  ⟨min (i.val + 1) N, Nat.lt_succ_iff.mpr (min_le_right _ _)⟩

/-- A discrete maximum principle for a tridiagonal recurrence on a finite
path.  The comparison weight is a strict supersolution at every interior
node, while the two endpoints provide the boundary values. -/
lemma finite_path_comparison
    {N : ℕ}
    (d w left right : Fin (N + 1) → ℝ) {delta : ℝ}
    (hd : ∀ i, 0 ≤ d i) (hw : ∀ i, 0 < w i)
    (hleft : ∀ i, 0 ≤ left i) (hright : ∀ i, 0 ≤ right i)
    (hdelta : 0 ≤ delta)
    (hboundary_left : d 0 ≤ delta * w 0)
    (hboundary_right : d (Fin.last N) ≤ delta * w (Fin.last N))
    (hstep : ∀ i, 0 < i.val → i.val < N →
      d i ≤ left i * d (pathPrev i) + right i * d (pathNext i))
    (hweight : ∀ i, 0 < i.val → i.val < N →
      left i * w (pathPrev i) + right i * w (pathNext i) ≤ w i / 2) :
    ∀ i, d i ≤ delta * w i := by
  classical
  let ratios : Finset ℝ := Finset.univ.image fun i => d i / w i
  have hratios_nonempty : ratios.Nonempty := by
    exact ⟨d 0 / w 0,
      Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
  let M : ℝ := ratios.max' hratios_nonempty
  have hratio_le (i : Fin (N + 1)) : d i / w i ≤ M := by
    apply Finset.le_max'
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hd_le (i : Fin (N + 1)) : d i ≤ M * w i :=
    (div_le_iff₀ (hw i)).mp (hratio_le i)
  have hM_nonneg : 0 ≤ M := by
    obtain ⟨i, _hi, hMi⟩ := Finset.mem_image.mp
      (Finset.max'_mem ratios hratios_nonempty)
    change 0 ≤ ratios.max' hratios_nonempty
    rw [← hMi]
    exact div_nonneg (hd i) (hw i).le
  obtain ⟨i, _hi, hMi⟩ := Finset.mem_image.mp
    (Finset.max'_mem ratios hratios_nonempty)
  have hdi : d i = M * w i := by
    have hratio : d i / w i = M := by simpa [M] using hMi
    exact (div_eq_iff (hw i).ne').mp hratio
  have hM_le_delta : M ≤ delta := by
    by_cases hi0 : i.val = 0
    · have hi : i = 0 := Fin.ext hi0
      have hb : d i ≤ delta * w i := by simpa [hi] using hboundary_left
      have hscaled : M * w i ≤ delta * w i := by rw [← hdi]; exact hb
      exact le_of_mul_le_mul_right hscaled (hw i)
    · by_cases hiN : i.val = N
      · have hi : i = Fin.last N := Fin.ext hiN
        have hb : d i ≤ delta * w i := by simpa [hi] using hboundary_right
        have hscaled : M * w i ≤ delta * w i := by rw [← hdi]; exact hb
        exact le_of_mul_le_mul_right hscaled (hw i)
      · have hi_pos : 0 < i.val := Nat.pos_of_ne_zero hi0
        have hi_le : i.val ≤ N := Nat.lt_succ_iff.mp i.isLt
        have hi_lt : i.val < N := lt_of_le_of_ne hi_le hiN
        have hrec := hstep i hi_pos hi_lt
        have hrec_le :
            left i * d (pathPrev i) + right i * d (pathNext i) ≤
              M * (left i * w (pathPrev i) +
                right i * w (pathNext i)) := by
          calc
            left i * d (pathPrev i) + right i * d (pathNext i) ≤
                left i * (M * w (pathPrev i)) +
                  right i * (M * w (pathNext i)) := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left (hd_le _) (hleft i))
                (mul_le_mul_of_nonneg_left (hd_le _) (hright i))
            _ = M * (left i * w (pathPrev i) +
                  right i * w (pathNext i)) := by ring
        have hhalf : M * w i ≤ M * (w i / 2) := by
          calc
            M * w i = d i := hdi.symm
            _ ≤ left i * d (pathPrev i) + right i * d (pathNext i) := hrec
            _ ≤ M * (left i * w (pathPrev i) +
                  right i * w (pathNext i)) := hrec_le
            _ ≤ M * (w i / 2) :=
              mul_le_mul_of_nonneg_left (hweight i hi_pos hi_lt) hM_nonneg
        have hhalf' : M * w i ≤ (M / 2) * w i := by
          calc
            M * w i ≤ M * (w i / 2) := hhalf
            _ = (M / 2) * w i := by ring
        have hM_le_half : M ≤ M / 2 :=
          le_of_mul_le_mul_right hhalf' (hw i)
        have hM_zero : M = 0 := by linarith
        rw [hM_zero]
        exact hdelta
  intro j
  calc
    d j ≤ M * w j := hd_le j
    _ ≤ delta * w j :=
      mul_le_mul_of_nonneg_right hM_le_delta (hw j).le

/-- A convenient two-weight form of `finite_path_comparison`.  Each of the
two directed weights contributes at most one quarter through either adjacent
edge, so their sum is a strict supersolution. -/
lemma finite_path_comparison_of_split_weights
    {N : ℕ}
    (d u v left right : Fin (N + 1) → ℝ) {delta : ℝ}
    (hd : ∀ i, 0 ≤ d i) (hu : ∀ i, 0 < u i) (hv : ∀ i, 0 < v i)
    (hleft : ∀ i, 0 ≤ left i) (hright : ∀ i, 0 ≤ right i)
    (hdelta : 0 ≤ delta)
    (hboundary_left : d 0 ≤ delta)
    (hboundary_right : d (Fin.last N) ≤ delta)
    (hboundary_weight_left : 1 ≤ u 0 + v 0)
    (hboundary_weight_right : 1 ≤ u (Fin.last N) + v (Fin.last N))
    (hleft_u : ∀ i, 0 < i.val → i.val < N →
      left i * u (pathPrev i) ≤ u i / 4)
    (hright_u : ∀ i, 0 < i.val → i.val < N →
      right i * u (pathNext i) ≤ u i / 4)
    (hleft_v : ∀ i, 0 < i.val → i.val < N →
      left i * v (pathPrev i) ≤ v i / 4)
    (hright_v : ∀ i, 0 < i.val → i.val < N →
      right i * v (pathNext i) ≤ v i / 4)
    (hstep : ∀ i, 0 < i.val → i.val < N →
      d i ≤ left i * d (pathPrev i) + right i * d (pathNext i)) :
    ∀ i, d i ≤ delta * (u i + v i) := by
  let w : Fin (N + 1) → ℝ := fun i => u i + v i
  have hw (i : Fin (N + 1)) : 0 < w i := by
    dsimp [w]
    linarith [hu i, hv i]
  apply finite_path_comparison d w left right hd hw hleft hright hdelta
  · calc
      d 0 ≤ delta := hboundary_left
      _ ≤ delta * w 0 := by
        have hone : 1 ≤ w 0 := by simpa [w] using hboundary_weight_left
        nlinarith
  · calc
      d (Fin.last N) ≤ delta := hboundary_right
      _ ≤ delta * w (Fin.last N) := by
        have hone : 1 ≤ w (Fin.last N) := by
          simpa [w] using hboundary_weight_right
        nlinarith
  · intro i hi0 hiN
    exact hstep i hi0 hiN
  · intro i hi0 hiN
    dsimp [w]
    calc
      left i * (u (pathPrev i) + v (pathPrev i)) +
          right i * (u (pathNext i) + v (pathNext i)) =
          (left i * u (pathPrev i) + right i * u (pathNext i)) +
            (left i * v (pathPrev i) + right i * v (pathNext i)) := by ring
      _ ≤ (u i / 4 + u i / 4) + (v i / 4 + v i / 4) :=
        add_le_add
          (add_le_add (hleft_u i hi0 hiN) (hright_u i hi0 hiN))
          (add_le_add (hleft_v i hi0 hiN) (hright_v i hi0 hiN))
      _ = (u i + v i) / 2 := by ring

end Submission.Helpers
