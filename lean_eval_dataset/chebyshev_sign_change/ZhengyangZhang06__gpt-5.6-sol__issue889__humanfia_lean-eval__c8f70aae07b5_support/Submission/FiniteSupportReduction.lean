import Submission.FiniteSupportPD

open Complex Real Set

namespace Submission.FiniteSupportPD

lemma fourierSum_nonneg_of_finite_support
    (k : ℝ → ℂ) (hpd : IsQuadraticallyNonnegative k)
    (T : Finset ℝ) (hsupp : ∀ t, t ∉ T → k t = 0) (x : ℝ) :
    0 ≤ (∑ t ∈ T,
      k t * Complex.exp ((((t * x : ℝ) : ℂ) * I))).re := by
  classical
  let H : Submodule ℤ ℝ := Submodule.span ℤ (T : Set ℝ)
  letI : Module.Finite ℤ H :=
    Module.Finite.span_of_finite ℤ T.finite_toSet
  letI : Module.Free ℤ H := Module.free_of_finite_type_torsion_free'
  let ι := Module.Free.ChooseBasisIndex ℤ H
  letI : Fintype ι := Module.Free.ChooseBasisIndex.fintype ℤ H
  let coord : H ≃ₗ[ℤ] (ι → ℤ) :=
    (Module.Free.chooseBasis ℤ H).repr ≪≫ₗ
      Finsupp.linearEquivFunOnFinite ℤ ℤ ι
  let e : (ι → ℤ) →+ ℝ :=
    { toFun := fun d => (coord.symm d).1
      map_zero' := by simp
      map_add' := by intro a b; simp }
  let f : ↥T → (ι → ℤ) := fun y =>
    coord ⟨y.1, Submodule.subset_span y.2⟩
  let S : Finset (ι → ℤ) := T.attach.image f
  have hef (y : ↥T) : e (f y) = y.1 := by
    simp [e, f]
  have heinj : Function.Injective e := by
    intro a b hab
    exact coord.symm.injective (Subtype.ext hab)
  have hfinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have h := congrArg e hab
    rw [hef a, hef b] at h
    exact h
  have hSsupport : ∀ d, d ∉ S → k (e d) = 0 := by
    intro d hd
    apply hsupp (e d)
    intro hed
    let y : ↥T := ⟨e d, hed⟩
    have hfd : f y = d := heinj (by simp [y, hef])
    exact hd (Finset.mem_image.mpr ⟨y, by simp, hfd⟩)
  have hcore := fourierSum_nonneg_of_integer_coordinates
    e k hpd S hSsupport x
  have hsum :
      (∑ d ∈ S, k (e d) *
          Complex.exp ((((e d * x : ℝ) : ℂ) * I))) =
        ∑ t ∈ T, k t * Complex.exp ((((t * x : ℝ) : ℂ) * I)) := by
    dsimp [S]
    rw [Finset.sum_image]
    · conv_rhs => rw [← Finset.sum_attach]
      apply Finset.sum_congr rfl
      intro y _hy
      rw [hef]
    · intro a _ha b _hb hab
      exact hfinj hab
  rw [hsum] at hcore
  exact hcore

end Submission.FiniteSupportPD
