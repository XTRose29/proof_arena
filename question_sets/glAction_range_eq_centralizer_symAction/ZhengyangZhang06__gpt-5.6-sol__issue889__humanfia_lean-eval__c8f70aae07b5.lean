import ChallengeDeps
import Submission.Helpers

open LeanEval.RepresentationTheory
open scoped TensorProduct

namespace Submission

set_option maxRecDepth 10000 in
theorem glAction_range_eq_centralizer_symAction {R : Type*} [Field R]
    {M : Type*} [AddCommGroup M] [Module R M] [FiniteDimensional R M]
    {k : ℕ} [Invertible (k.factorial : R)] :
    Algebra.adjoin R (Set.range (glAction R M k)) =
      Subalgebra.centralizer R (Set.range (symAction R M k)) := by
  classical
  apply le_antisymm
  · exact Helpers.glAction_adjoin_le_centralizer k
  · intro z hz
    let b := Module.finBasis R M
    let e := Helpers.tensorEndEquiv b k
    let x : ⨂[R]^k (Module.End R M) := e.symm z
    rw [Subalgebra.mem_centralizer_iff] at hz
    have hinv (σ : Equiv.Perm (Fin k)) :
        PiTensorProduct.reindex R (fun _ : Fin k ↦ Module.End R M) σ x = x := by
      apply e.injective
      change e (PiTensorProduct.reindex R (fun _ : Fin k ↦ Module.End R M) σ x) = e x
      rw [show e (PiTensorProduct.reindex R (fun _ : Fin k ↦ Module.End R M) σ x) =
          PiTensorProduct.piTensorHomMap
            (PiTensorProduct.reindex R (fun _ : Fin k ↦ Module.End R M) σ x) by
            exact LinearMap.congr_fun (Helpers.tensorEndEquiv_eq_piTensorHomMap b k) _,
        show e x = PiTensorProduct.piTensorHomMap x by
          exact LinearMap.congr_fun (Helpers.tensorEndEquiv_eq_piTensorHomMap b k) _]
      rw [Helpers.piTensorHomMap_reindex]
      have hxmap : PiTensorProduct.piTensorHomMap x = z := by
        rw [← show e x = PiTensorProduct.piTensorHomMap x by
          exact LinearMap.congr_fun (Helpers.tensorEndEquiv_eq_piTensorHomMap b k) _]
        simp [x]
      rw [hxmap]
      have hcomm : (symAction R M k) σ * z = z * (symAction R M k) σ :=
        hz _ ⟨σ, rfl⟩
      rw [hcomm]
      rw [mul_assoc, ← map_mul]
      simp
    let A := Algebra.adjoin R (Set.range (glAction R M k))
    change z ∈ A.toSubmodule
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff A.toSubmodule z).mp
    intro φ hφ
    let ψ : Module.Dual R (⨂[R]^k (Module.End R M)) := φ.comp e.toLinearMap
    have hpoly : Helpers.tensorPolynomial b.end k ψ = 0 := by
      apply Helpers.tensorPolynomial_eq_zero_of_eval_det_one b.end k ψ
      intro C hC
      let Gm : Matrix.GeneralLinearGroup (Fin (Module.finrank R M)) R :=
        Matrix.GeneralLinearGroup.mkOfDetNeZero C (by rw [hC]; exact one_ne_zero)
      let G : (Module.End R M)ˣ :=
        Units.map (Matrix.toLinAlgEquiv b).toMonoidHom Gm
      have hsumC :
          (∑ ij : Fin (Module.finrank R M) × Fin (Module.finrank R M),
              C ij.1 ij.2 • b.end ij) = (G : Module.End R M) := by
        have hGval : (G : Module.End R M) = Matrix.toLinAlgEquiv b C := rfl
        rw [hGval]
        apply b.ext
        intro l
        simp [Fintype.sum_prod_type, Module.Basis.end_apply_apply]
      rw [Helpers.eval_tensorPolynomial, hsumC]
      change φ (e ((PiTensorProduct.tprod R)
        (fun _ : Fin k ↦ (G : Module.End R M)))) = 0
      have heG : e ((PiTensorProduct.tprod R)
          (fun _ : Fin k ↦ (G : Module.End R M))) = (glAction R M k) G := by
        rw [show e ((PiTensorProduct.tprod R)
            (fun _ : Fin k ↦ (G : Module.End R M))) =
              PiTensorProduct.piTensorHomMap ((PiTensorProduct.tprod R)
                (fun _ : Fin k ↦ (G : Module.End R M))) by
              exact LinearMap.congr_fun (Helpers.tensorEndEquiv_eq_piTensorHomMap b k) _]
        apply LinearMap.ext
        intro y
        induction y using PiTensorProduct.induction_on with
        | smul_tprod r v => simp [glAction]
        | add y₁ y₂ hy₁ hy₂ => simp [map_add, glAction, hy₁, hy₂]
      rw [heG]
      exact (Submodule.mem_dualAnnihilator φ).mp hφ _
        (Algebra.subset_adjoin ⟨G, rfl⟩)
    have hdiag (u : Module.End R M) :
        ψ ((PiTensorProduct.tprod R) (fun _ : Fin k ↦ u)) = 0 := by
      have heval : MvPolynomial.eval (b.end.equivFun u)
          (Helpers.tensorPolynomial b.end k ψ) = 0 := by simp [hpoly]
      rw [Helpers.eval_tensorPolynomial] at heval
      have hsumu : (∑ ij, b.end.equivFun u ij • b.end ij) = u :=
        b.end.sum_equivFun u
      have htensor :
          (PiTensorProduct.tprod R)
              (fun _ : Fin k ↦ ∑ ij, b.end.equivFun u ij • b.end ij) =
            (PiTensorProduct.tprod R) (fun _ : Fin k ↦ u) := by
        apply congrArg (PiTensorProduct.tprod R)
        funext _
        exact hsumu
      exact Eq.mp (congrArg (fun z ↦ ψ z = 0) htensor) heval
    have hψx := Helpers.apply_eq_zero_of_diagonal_and_invariant k ψ hdiag x hinv
    simpa [ψ, x, e] using hψx

end Submission
