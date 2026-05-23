import Mathlib
import Submission.Amplification

namespace Submission.Helpers

open scoped InnerProductSpace
open Submission.Amplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Direction 1 → 2: centralizer is WOT-closed -/

set_option maxHeartbeats 800000 in
lemma centralizer_wot_closed (U : Set (H →L[ℂ] H)) :
    IsClosed (ContinuousLinearMap.toWOT (RingHom.id ℂ) H H '' Set.centralizer U) := by
  apply isClosed_of_closure_subset
  intro T hT
  rw [Set.mem_image]
  let T₀ := (ContinuousLinearMap.toWOT (RingHom.id ℂ) H H).symm T
  refine ⟨T₀, ?_, (ContinuousLinearMap.toWOT (RingHom.id ℂ) H H).apply_symm_apply T⟩
  intro A hA
  ext x
  simp only [ContinuousLinearMap.mul_apply]
  suffices ∀ y : StrongDual ℂ H, y (T (A x)) = y (A (T x)) by
    by_contra h_ne
    obtain ⟨y, hy⟩ := @SeparatingDual.exists_ne_zero ℂ H _ _ _ _ _ inferInstance
      (T (A x) - A (T x)) (sub_ne_zero.mpr (Ne.symm h_ne))
    exact hy (by rw [map_sub, sub_eq_zero]; exact this y)
  intro y
  have hcont : Continuous (fun (S : H →WOT[ℂ] H) => y (S (A x)) - y (A (S x))) :=
    (ContinuousLinearMapWOT.continuous_dual_apply (A x) y).sub
      (ContinuousLinearMapWOT.continuous_dual_apply x (ContinuousLinearMap.comp y A))
  have hzero : ∀ S ∈ ContinuousLinearMap.toWOT (RingHom.id ℂ) H H '' Set.centralizer U,
      y (S (A x)) - y (A (S x)) = 0 := by
    rintro S ⟨S₀, hS₀, rfl⟩
    have h1 := hS₀ A hA
    have h2 := ContinuousLinearMap.ext_iff.mp h1 x
    simp only [ContinuousLinearMap.mul_apply] at h2
    show y (S₀ (A x)) - y (A (S₀ x)) = 0
    rw [h2.symm, sub_self]
  exact sub_eq_zero.mp (closure_minimal
    (fun S hS => show (fun S => y (S (A x)) - y (A (S x))) S ∈ ({0} : Set ℂ) from by simp [hzero S hS])
    (isClosed_singleton.preimage hcont) hT)

lemma double_commutant_imp_wot_closed (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (h : Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) = S) :
    IsClosed (ContinuousLinearMap.toWOT (RingHom.id ℂ) H H '' (S : Set (H →L[ℂ] H))) := by
  rw [← h]
  exact centralizer_wot_closed _

/-! ## Direction 2 → 3: WOT-closed implies PwConv-closed -/

lemma wot_closed_imp_pwconv_closed (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (h : IsClosed (ContinuousLinearMap.toWOT (RingHom.id ℂ) H H '' (S : Set (H →L[ℂ] H)))) :
    IsClosed (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
      (S : Set (H →L[ℂ] H))) := by
  constructor;
  convert h.isOpen_compl.preimage _;
  rotate_left;
  exact fun f => ContinuousLinearMap.toWOT ( RingHom.id ℂ ) H H f;
  · convert ContinuousLinearMapWOT.continuous_of_dual_apply_continuous _;
    intro x y;
    refine' Continuous.comp ( y.continuous ) _;
    exact continuous_eval_const x
  · ext; simp [Set.mem_compl_iff, Set.mem_preimage]

/-! ## Direction 3 → 1: PwConv-closed implies double commutant -/

lemma pwconv_closed_imp_double_commutant (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (h : IsClosed (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
      (S : Set (H →L[ℂ] H)))) :
    Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) = S := by
  apply Set.eq_of_subset_of_subset
  · intro T hT
    have h_mem := double_commutant_in_pwconv_closure S T hT
    rw [h.closure_eq] at h_mem
    obtain ⟨A, hA, hAT⟩ := h_mem
    have hTA : T = A := by
      simp [ContinuousLinearMap.toPointwiseConvergenceCLM] at hAT
      exact ContinuousLinearMap.ext (fun x => by exact congr_fun (congr_arg DFunLike.coe hAT.symm) x)
    rw [hTA]; exact hA
  · exact Set.subset_centralizer_centralizer

end Submission.Helpers