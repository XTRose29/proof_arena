import Submission.SecantLinearization

namespace Submission.Helpers

open LeanEval.Dynamics

lemma norm_clmPrefixProduct_le_pow
    (A : ℕ → EucPlane →L[ℝ] EucPlane) {M : ℝ}
    (hM : 0 ≤ M) (hA : ∀ k, ‖A k‖ ≤ M) :
    ∀ n, ‖clmPrefixProduct A n‖ ≤ M ^ n := by
  intro n
  induction n with
  | zero => simp [clmPrefixProduct]
  | succ n ih =>
      rw [clmPrefixProduct_succ]
      calc
        ‖A n ∘L clmPrefixProduct A n‖ ≤
            ‖A n‖ * ‖clmPrefixProduct A n‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ M * M ^ n := mul_le_mul (hA n) ih (norm_nonneg _)
          hM
        _ = M ^ (n + 1) := (pow_succ' M n).symm

lemma norm_clmPrefixProduct_le_pow_of_lt
    (A : ℕ → EucPlane →L[ℝ] EucPlane) {M : ℝ}
    (hM : 0 ≤ M) (n : ℕ) (hA : ∀ k, k < n → ‖A k‖ ≤ M) :
    ‖clmPrefixProduct A n‖ ≤ M ^ n := by
  induction n with
  | zero => simp [clmPrefixProduct]
  | succ n ih =>
      rw [clmPrefixProduct_succ]
      calc
        ‖A n ∘L clmPrefixProduct A n‖ ≤
            ‖A n‖ * ‖clmPrefixProduct A n‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ M * M ^ n :=
          mul_le_mul (hA n (Nat.lt_succ_self n))
            (ih fun k hk => hA k (hk.trans (Nat.lt_succ_self n)))
            (norm_nonneg _) hM
        _ = M ^ (n + 1) := (pow_succ' M n).symm

lemma clmPrefixProduct_sub_eq
    (A D : ℕ → EucPlane →L[ℝ] EucPlane) (n : ℕ) :
    clmPrefixProduct A (n + 1) - clmPrefixProduct D (n + 1) =
      A n ∘L (clmPrefixProduct A n - clmPrefixProduct D n) +
        (A n - D n) ∘L clmPrefixProduct D n := by
  rw [clmPrefixProduct_succ, clmPrefixProduct_succ]
  apply ContinuousLinearMap.ext
  intro z
  simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, map_sub]
  abel

lemma norm_clmPrefixProduct_sub_le_of_lt
    (A D : ℕ → EucPlane →L[ℝ] EucPlane) {M epsilon : ℝ}
    (hM : 1 ≤ M) (hepsilon : 0 ≤ epsilon)
    (n : ℕ)
    (hA : ∀ k, k < n → ‖A k‖ ≤ M)
    (hD : ∀ k, k < n → ‖D k‖ ≤ M)
    (hdiff : ∀ k, k < n → ‖A k - D k‖ ≤ epsilon) :
    ‖clmPrefixProduct A n - clmPrefixProduct D n‖ ≤
      n * epsilon * M ^ (n + 1) := by
  have hM_nonneg : 0 ≤ M := zero_le_one.trans hM
  induction n with
  | zero => simp [clmPrefixProduct]
  | succ n ih =>
      have ih' := ih
        (fun k hk => hA k (hk.trans (Nat.lt_succ_self n)))
        (fun k hk => hD k (hk.trans (Nat.lt_succ_self n)))
        (fun k hk => hdiff k (hk.trans (Nat.lt_succ_self n)))
      rw [clmPrefixProduct_sub_eq]
      calc
        ‖A n ∘L (clmPrefixProduct A n - clmPrefixProduct D n) +
            (A n - D n) ∘L clmPrefixProduct D n‖ ≤
            ‖A n ∘L (clmPrefixProduct A n - clmPrefixProduct D n)‖ +
              ‖(A n - D n) ∘L clmPrefixProduct D n‖ := norm_add_le _ _
        _ ≤ ‖A n‖ * ‖clmPrefixProduct A n - clmPrefixProduct D n‖ +
              ‖A n - D n‖ * ‖clmPrefixProduct D n‖ :=
          add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
            (ContinuousLinearMap.opNorm_comp_le _ _)
        _ ≤ M * (n * epsilon * M ^ (n + 1)) +
              epsilon * M ^ n := by
          apply add_le_add
          · calc
              ‖A n‖ * ‖clmPrefixProduct A n - clmPrefixProduct D n‖ ≤
                  M * ‖clmPrefixProduct A n - clmPrefixProduct D n‖ :=
                mul_le_mul_of_nonneg_right (hA n (Nat.lt_succ_self n))
                  (norm_nonneg _)
              _ ≤ M * (n * epsilon * M ^ (n + 1)) :=
                mul_le_mul_of_nonneg_left ih' hM_nonneg
          · calc
              ‖A n - D n‖ * ‖clmPrefixProduct D n‖ ≤
                  epsilon * ‖clmPrefixProduct D n‖ :=
                mul_le_mul_of_nonneg_right
                  (hdiff n (Nat.lt_succ_self n)) (norm_nonneg _)
              _ ≤ epsilon * M ^ n :=
                mul_le_mul_of_nonneg_left
                  (norm_clmPrefixProduct_le_pow_of_lt D hM_nonneg n
                    (fun k hk => hD k (hk.trans (Nat.lt_succ_self n))))
                  hepsilon
        _ ≤ (n + 1 : ℕ) * epsilon * M ^ (n + 2) := by
          have hpow : M ^ n ≤ M ^ (n + 1) := by
            exact pow_le_pow_right₀ hM (Nat.le_succ n)
          have hpow_nonneg : 0 ≤ M ^ n := pow_nonneg hM_nonneg n
          have hpow_succ_nonneg : 0 ≤ M ^ (n + 1) :=
            pow_nonneg hM_nonneg (n + 1)
          rw [show M * (n * epsilon * M ^ (n + 1)) =
            n * epsilon * M ^ (n + 2) by
              rw [pow_succ]
              ring]
          calc
            (n : ℝ) * epsilon * M ^ (n + 2) + epsilon * M ^ n ≤
                (n : ℝ) * epsilon * M ^ (n + 2) +
                  epsilon * M ^ (n + 1) := by
              gcongr
            _ ≤ (n : ℝ) * epsilon * M ^ (n + 2) +
                  epsilon * M ^ (n + 2) := by
              exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
                (pow_le_pow_right₀ hM (Nat.le_succ (n + 1))) hepsilon)
            _ = ((n + 1 : ℕ) : ℝ) * epsilon * M ^ (n + 2) := by
              norm_num [Nat.cast_add, Nat.cast_one]
              ring

lemma norm_clmPrefixProduct_sub_le
    (A D : ℕ → EucPlane →L[ℝ] EucPlane) {M epsilon : ℝ}
    (hM : 1 ≤ M) (hepsilon : 0 ≤ epsilon)
    (hA : ∀ k, ‖A k‖ ≤ M) (hD : ∀ k, ‖D k‖ ≤ M)
    (hdiff : ∀ k, ‖A k - D k‖ ≤ epsilon) :
    ∀ n, ‖clmPrefixProduct A n - clmPrefixProduct D n‖ ≤
      n * epsilon * M ^ (n + 1) := by
  intro n
  exact norm_clmPrefixProduct_sub_le_of_lt A D hM hepsilon n
    (fun k _ => hA k) (fun k _ => hD k) (fun k _ => hdiff k)

lemma clmPrefixProduct_fderiv_orbit
    (F : EucPlane → EucPlane) (hF : Differentiable ℝ F)
    (x : EucPlane) :
    ∀ n, clmPrefixProduct (fun k => fderiv ℝ F (F^[k] x)) n =
      fderiv ℝ (F^[n]) x := by
  intro n
  induction n with
  | zero => simp [clmPrefixProduct, fderiv_id]
  | succ n ih =>
      rw [clmPrefixProduct_succ, ih, Function.iterate_succ', fderiv_comp]
      · exact hF.differentiableAt
      · exact (hF.iterate n).differentiableAt

lemma norm_orbitSecantStep_sub_fderiv_le
    (F : EucPlane → EucPlane) (x y : EucPlane) (k : ℕ) {B : ℝ}
    (hrem : ‖F (F^[k] y) - F (F^[k] x) -
        fderiv ℝ F (F^[k] x) (F^[k] y - F^[k] x)‖ ≤
      B * ‖F^[k] y - F^[k] x‖ ^ 2) :
    ‖orbitSecantStep F x y k - fderiv ℝ F (F^[k] x)‖ ≤
      B * ‖F^[k] y - F^[k] x‖ := by
  exact norm_secantLinearMap_sub_fderiv_le F (F^[k] x) (F^[k] y) hrem

lemma norm_clmPrefixProduct_orbitSecantStep_sub_fderiv_iterate_le_of_lt
    (F : EucPlane → EucPlane) (hF : Differentiable ℝ F)
    (x y : EucPlane) {C B delta : ℝ}
    (hB : 0 ≤ B) (hdelta : 0 ≤ delta)
    (hM : 1 ≤ C + B * delta) (n : ℕ)
    (hderiv : ∀ k, k < n → ‖fderiv ℝ F (F^[k] x)‖ ≤ C)
    (horbit : ∀ k, k < n → ‖F^[k] y - F^[k] x‖ ≤ delta)
    (hrem : ∀ k, k < n → ‖F (F^[k] y) - F (F^[k] x) -
        fderiv ℝ F (F^[k] x) (F^[k] y - F^[k] x)‖ ≤
      B * ‖F^[k] y - F^[k] x‖ ^ 2) :
    ‖clmPrefixProduct (orbitSecantStep F x y) n -
        fderiv ℝ (F^[n]) x‖ ≤
      n * (B * delta) * (C + B * delta) ^ (n + 1) := by
  let D : ℕ → EucPlane →L[ℝ] EucPlane :=
    fun k => fderiv ℝ F (F^[k] x)
  have hD : ∀ k, k < n → ‖D k‖ ≤ C + B * delta := by
    intro k hk
    exact (hderiv k hk).trans (le_add_of_nonneg_right
      (mul_nonneg hB hdelta))
  have hdiff : ∀ k, k < n →
      ‖orbitSecantStep F x y k - D k‖ ≤ B * delta := by
    intro k hk
    exact (norm_orbitSecantStep_sub_fderiv_le F x y k (hrem k hk)).trans
      (mul_le_mul_of_nonneg_left (horbit k hk) hB)
  have hA : ∀ k, k < n →
      ‖orbitSecantStep F x y k‖ ≤ C + B * delta := by
    intro k hk
    calc
      ‖orbitSecantStep F x y k‖ =
          ‖D k + (orbitSecantStep F x y k - D k)‖ := by
        congr 1
        abel
      _ ≤ ‖D k‖ + ‖orbitSecantStep F x y k - D k‖ := norm_add_le _ _
      _ ≤ C + B * delta := add_le_add (hderiv k hk) (hdiff k hk)
  rw [← clmPrefixProduct_fderiv_orbit F hF x n]
  exact norm_clmPrefixProduct_sub_le_of_lt
    (orbitSecantStep F x y) D hM (mul_nonneg hB hdelta) n hA hD hdiff

lemma norm_clmPrefixProduct_orbitSecantStep_sub_fderiv_iterate_le
    (F : EucPlane → EucPlane) (hF : Differentiable ℝ F)
    (x y : EucPlane) {C B delta : ℝ}
    (hB : 0 ≤ B) (hdelta : 0 ≤ delta)
    (hM : 1 ≤ C + B * delta)
    (hderiv : ∀ k, ‖fderiv ℝ F (F^[k] x)‖ ≤ C)
    (horbit : ∀ k, ‖F^[k] y - F^[k] x‖ ≤ delta)
    (hrem : ∀ k, ‖F (F^[k] y) - F (F^[k] x) -
        fderiv ℝ F (F^[k] x) (F^[k] y - F^[k] x)‖ ≤
      B * ‖F^[k] y - F^[k] x‖ ^ 2) :
    ∀ n, ‖clmPrefixProduct (orbitSecantStep F x y) n -
        fderiv ℝ (F^[n]) x‖ ≤
      n * (B * delta) * (C + B * delta) ^ (n + 1) := by
  intro n
  exact norm_clmPrefixProduct_orbitSecantStep_sub_fderiv_iterate_le_of_lt
    F hF x y hB hdelta hM n
      (fun k _ => hderiv k) (fun k _ => horbit k) (fun k _ => hrem k)

end Submission.Helpers
