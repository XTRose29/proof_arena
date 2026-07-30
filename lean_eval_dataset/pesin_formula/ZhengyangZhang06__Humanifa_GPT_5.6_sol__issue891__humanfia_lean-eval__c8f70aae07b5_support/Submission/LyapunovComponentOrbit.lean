import Submission.LyapunovComponents
import Submission.DerivativeDistortion

namespace Submission.Helpers

open LeanEval.Dynamics Filter MeasureTheory

lemma ae_all_iterates_of_ae
    {M : Type*} [MeasurableSpace M] {mu : Measure M}
    {T : M → M} (hT : Measure.QuasiMeasurePreserving T mu mu)
    {p : M → Prop} (hp : ∀ᵐ x ∂mu, p x) :
    ∀ᵐ x ∂mu, ∀ n : ℕ, p (T^[n] x) := by
  rw [ae_all_iff]
  intro n
  exact (hT.iterate n).tendsto_ae hp

lemma lyapunovComponents_add
    (T T_inv : EucPlane → EucPlane) {x : EucPlane}
    (hx : SourceSplittingData T T_inv x) :
    lyapunovStableComponent T T_inv x +
        lyapunovUnstableComponent T T_inv x =
      ContinuousLinearMap.id ℝ EucPlane := by
  exact stableComponent_add_unstableComponent
    (stableProjection T x) (stableProjection T_inv x) hx.invertible

lemma component_fderiv_iterate_covariant
    (T : EucPlane → EucPlane) (hT_smooth : ContDiff ℝ 2 T)
    (S : EucPlane → EucPlane →L[ℝ] EucPlane) (x : EucPlane)
    (hcov : ∀ k : ℕ,
      S (T^[k + 1] x) ∘L fderiv ℝ T (T^[k] x) =
        fderiv ℝ T (T^[k] x) ∘L S (T^[k] x)) :
    ∀ n : ℕ,
      S (T^[n] x) ∘L fderiv ℝ (T^[n]) x =
        fderiv ℝ (T^[n]) x ∘L S x := by
  have hT_diff : Differentiable ℝ T :=
    hT_smooth.differentiable (by norm_num)
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hpoint : T^[n + 1] x = T (T^[n] x) := by
        exact Function.iterate_succ_apply' T n x
      have hderiv :
          fderiv ℝ (T^[n + 1]) x =
            fderiv ℝ T (T^[n] x) ∘L fderiv ℝ (T^[n]) x := by
        rw [Function.iterate_succ', fderiv_comp]
        · exact hT_diff.differentiableAt
        · exact (hT_diff.iterate n).differentiableAt
      have hcov_n :
          S (T (T^[n] x)) ∘L fderiv ℝ T (T^[n] x) =
            fderiv ℝ T (T^[n] x) ∘L S (T^[n] x) := by
        simpa [Function.iterate_succ_apply'] using hcov n
      rw [hpoint, hderiv]
      calc
        S (T (T^[n] x)) ∘L
              (fderiv ℝ T (T^[n] x) ∘L fderiv ℝ (T^[n]) x) =
            (S (T (T^[n] x)) ∘L fderiv ℝ T (T^[n] x)) ∘L
              fderiv ℝ (T^[n]) x :=
          (ContinuousLinearMap.comp_assoc _ _ _).symm
        _ = (fderiv ℝ T (T^[n] x) ∘L S (T^[n] x)) ∘L
              fderiv ℝ (T^[n]) x := by rw [hcov_n]
        _ = fderiv ℝ T (T^[n] x) ∘L
              (S (T^[n] x) ∘L fderiv ℝ (T^[n]) x) :=
          ContinuousLinearMap.comp_assoc _ _ _
        _ = fderiv ℝ T (T^[n] x) ∘L
              (fderiv ℝ (T^[n]) x ∘L S x) := by rw [ih]
        _ = (fderiv ℝ T (T^[n] x) ∘L fderiv ℝ (T^[n]) x) ∘L S x :=
          (ContinuousLinearMap.comp_assoc _ _ _).symm

theorem ae_all_lyapunovComponents_fderiv_iterate_covariant
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    {lam1 lam2 eta : ℝ}
    (hlam1 : lam1 = ∫ x, lyapunovUpperAt T x ∂mu)
    (hlam2 : lam2 = ∫ x, lyapunovLowerAt T x ∂mu)
    (hlam1_pos : 0 < lam1) (hlam2_neg : lam2 < 0)
    (heta : 0 < eta)
    (hgap : 8 * eta < lam1 - lam2)
    (hstable_neg : lam2 + 5 * eta < 0)
    (hunstable_neg : -lam1 + 5 * eta < 0)
    (hrate : 8 * eta < hyperbolicRate lam1 lam2) :
    ∀ᵐ x ∂mu, ∀ n : ℕ,
      lyapunovStableComponent T T_inv (T^[n] x) ∘L
          fderiv ℝ (T^[n]) x =
        fderiv ℝ (T^[n]) x ∘L lyapunovStableComponent T T_inv x ∧
      lyapunovUnstableComponent T T_inv (T^[n] x) ∘L
          fderiv ℝ (T^[n]) x =
        fderiv ℝ (T^[n]) x ∘L lyapunovUnstableComponent T T_inv x := by
  have hone := ae_lyapunovComponents_fderiv_covariant
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta hgap
      hstable_neg hunstable_neg hrate
  have hall := ae_all_iterates_of_ae hT.quasiMeasurePreserving hone
  filter_upwards [hall] with x hx
  intro n
  constructor
  · apply component_fderiv_iterate_covariant
      T hT_smooth (lyapunovStableComponent T T_inv) x
    intro k
    simpa [Function.iterate_succ_apply'] using (hx k).1
  · apply component_fderiv_iterate_covariant
      T hT_smooth (lyapunovUnstableComponent T T_inv) x
    intro k
    simpa [Function.iterate_succ_apply'] using (hx k).2

lemma norm_component_image_sub_le
    (F : EucPlane → EucPlane) (D S₀ S₁ : EucPlane →L[ℝ] EucPlane)
    {x y : EucPlane} {B : ℝ}
    (hcov : S₁ ∘L D = D ∘L S₀)
    (hrem : ‖F y - F x - D (y - x)‖ ≤ B * ‖y - x‖ ^ 2) :
    ‖S₁ (F y - F x)‖ ≤
      ‖D ∘L S₀‖ * ‖y - x‖ + ‖S₁‖ * (B * ‖y - x‖ ^ 2) := by
  let r := F y - F x - D (y - x)
  have hsplit : F y - F x = D (y - x) + r := by
    dsimp [r]
    abel
  have hlinear : S₁ (D (y - x)) = (D ∘L S₀) (y - x) := by
    exact congrArg (fun L : EucPlane →L[ℝ] EucPlane => L (y - x)) hcov
  rw [hsplit, map_add, hlinear]
  calc
    ‖(D ∘L S₀) (y - x) + S₁ r‖ ≤
        ‖(D ∘L S₀) (y - x)‖ + ‖S₁ r‖ := norm_add_le _ _
    _ ≤ ‖D ∘L S₀‖ * ‖y - x‖ + ‖S₁‖ * ‖r‖ :=
      add_le_add ((D ∘L S₀).le_opNorm _) (S₁.le_opNorm _)
    _ ≤ ‖D ∘L S₀‖ * ‖y - x‖ + ‖S₁‖ * (B * ‖y - x‖ ^ 2) := by
      gcongr

end Submission.Helpers
