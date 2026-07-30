import ChallengeDeps
import Submission.Helpers

open LeanEval.Dynamics
open scoped Topology ENNReal NNReal
open MeasureTheory

namespace Submission

theorem moran_equality_affine {d n : ℕ} (hn : 1 ≤ n)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (h_aff : IsAffineSymmetricIFS f lam)
    (h_osc : OpenSetCondition f)
    {S : Set (EuclideanSpace ℝ (Fin d))} (hS : IsAttractor f S) :
    dimH S = ENNReal.ofReal (- Real.log n / Real.log lam) := by
  rcases h_aff with ⟨hlam, hlam1, A, β, hrep⟩
  rcases h_osc with ⟨G, hGopen, hGne, hmap, hdisj⟩
  rcases hS with ⟨hScompact, hSne, hfixed⟩
  by_cases hd : d = 0
  · subst d
    have hnle : n ≤ 1 := by
      by_contra hnle
      have hn2 : 2 ≤ n := by omega
      let i : Fin n := ⟨0, by omega⟩
      let j : Fin n := ⟨1, by omega⟩
      have hij : i ≠ j := by
        intro h
        have hval := congrArg Fin.val h
        simp [i, j] at hval
      obtain ⟨x, hx⟩ := hGne
      have hix : f i x ∈ f i '' G := Set.mem_image_of_mem _ hx
      have hjx : f i x ∈ f j '' G := by
        have heq : f j x = f i x := Subsingleton.elim _ _
        rw [← heq]
        exact Set.mem_image_of_mem _ hx
      exact Set.disjoint_left.1 (hdisj i j hij) hix hjx
    have hnEq : n = 1 := by omega
    subst n
    have hsub : S.Subsingleton := fun _ _ _ _ ↦ Subsingleton.elim _ _
    simpa using hsub.dimH_zero
  · letI : Nonempty (Fin d) :=
      Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hd)
    letI : Nontrivial (EuclideanSpace ℝ (Fin d)) := inferInstance
    let φ : Fin n → EuclideanSpace ℝ (Fin d) →ᵈ EuclideanSpace ℝ (Fin d) :=
      fun i ↦ Helpers.affineDilation lam hlam (A i) (β i)
    have hφ (i : Fin n) : f i = φ i := by
      funext x
      simp [φ, hrep]
    let F : Helpers.UniformIFS (EuclideanSpace ℝ (Fin d)) n :=
      { q := ⟨lam, hlam.le⟩
        q_pos := by exact_mod_cast hlam
        q_lt_one := by exact_mod_cast hlam1
        φ := φ
        ratio_φ := fun i ↦ by
          simpa [φ] using Helpers.affineDilation_ratio lam hlam (A i) (β i)
        surjective_φ := fun i ↦ by
          simpa [φ] using Helpers.affineDilation_surjective lam hlam (A i) (β i)
        S := S
        S_compact := hScompact
        S_nonempty := hSne
        fixed := by simpa only [← hφ] using hfixed
        G := G
        G_open := hGopen
        G_nonempty := hGne
        mapsTo_G := fun i x hx ↦ by
          rw [← hφ i]
          exact hmap i (Set.mem_image_of_mem _ hx)
        disjoint_G := fun i j hij ↦ by
          simpa only [← hφ] using hdisj i j hij }
    have hq : (F.q : ℝ) = lam := by rfl
    simpa [Helpers.similarityExponent, hq] using F.dimH_eq_similarityExponent hn

end Submission
