import Submission.Bounded

namespace Submission.Transport

open Function Set

noncomputable section

theorem natCard_connectedComponents_compl_eq_of_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {s : Set X} {t : Set Y} (himage : e '' s = t) :
    Nat.card (ConnectedComponents (sᶜ : Set X)) =
      Nat.card (ConnectedComponents (tᶜ : Set Y)) := by
  have hcomp : sᶜ = e ⁻¹' tᶜ := by
    ext x
    simp only [mem_compl_iff, mem_preimage]
    rw [← himage]
    simp
  exact Nat.card_congr (Helpers.connectedComponentsEquiv (e.sets hcomp))

abbrev planeEquiv : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.symm

def sphereEquiv :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ Circle where
  toFun z := ⟨planeEquiv z, by
    apply mem_sphere_zero_iff_norm.2
    rw [LinearIsometryEquiv.norm_map]
    exact mem_sphere_zero_iff_norm.1 z.2⟩
  invFun z := ⟨planeEquiv.symm z, by
    rw [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.norm_map,
      Circle.norm_coe]⟩
  left_inv z := by
    apply Subtype.ext
    exact planeEquiv.symm_apply_apply z
  right_inv z := by
    apply Circle.ext
    exact planeEquiv.apply_symm_apply z
  continuous_toFun :=
    (planeEquiv.continuous.comp continuous_subtype_val).subtype_mk fun z ↦ by
      apply mem_sphere_zero_iff_norm.2
      change ‖planeEquiv (z : EuclideanSpace ℝ (Fin 2))‖ = 1
      rw [LinearIsometryEquiv.norm_map]
      exact mem_sphere_zero_iff_norm.1 z.2
  continuous_invFun :=
    (planeEquiv.symm.continuous.comp continuous_subtype_val).subtype_mk fun z ↦ by
      change planeEquiv.symm (z : ℂ) ∈
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1
      rw [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.norm_map,
        Circle.norm_coe]

theorem jordan_curve_euclidean
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      EuclideanSpace ℝ (Fin 2))
    (hcont : Continuous r) (hinj : Function.Injective r) :
    Nat.card
        (ConnectedComponents ((Set.range r)ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) =
      2 := by
  let rc : C(Circle, ℂ) :=
    ⟨fun z ↦ planeEquiv (r (sphereEquiv.symm z)),
      planeEquiv.continuous.comp (hcont.comp sphereEquiv.symm.continuous)⟩
  have hrcinj : Function.Injective rc := by
    intro x y hxy
    apply sphereEquiv.symm.injective
    apply hinj
    exact planeEquiv.injective hxy
  have hrcard :
      Nat.card (ConnectedComponents ((Set.range rc)ᶜ : Set ℂ)) = 2 :=
    Bounded.jordan_curve_complex rc hrcinj
  have hrange : planeEquiv.toHomeomorph '' Set.range r = Set.range rc := by
    ext y
    constructor
    · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
      exact ⟨sphereEquiv z, by simp [rc]⟩
    · rintro ⟨z, rfl⟩
      exact ⟨r (sphereEquiv.symm z), ⟨sphereEquiv.symm z, rfl⟩, by simp [rc]⟩
  calc
    Nat.card
        (ConnectedComponents ((Set.range r)ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) =
        Nat.card (ConnectedComponents ((Set.range rc)ᶜ : Set ℂ)) :=
      natCard_connectedComponents_compl_eq_of_homeomorph
        planeEquiv.toHomeomorph hrange
    _ = 2 := hrcard

end

end Submission.Transport
