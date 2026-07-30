import Submission.Transport

open LeanEval.Dynamics.HalmosGenericWeakMixingProblem
open MeasureTheory Filter Topology

namespace Submission.Conull

variable {X : Type*} [MeasurableSpace X]

noncomputable def subtypeMeasure (m : Measure X) (D : Set X) : Measure D :=
  Measure.comap ((↑) : D → X) m

noncomputable def extendEquiv (D : Set X) (hD : MeasurableSet D)
    (S : D ≃ᵐ D) : X ≃ᵐ X := by
  classical
  exact (MeasurableEquiv.sumCompl hD).symm.trans
    ((MeasurableEquiv.sumCongr S (MeasurableEquiv.refl (Dᶜ : Set X))).trans
      (MeasurableEquiv.sumCompl hD))

@[simp]
theorem extendEquiv_apply_of_mem (D : Set X) (hD : MeasurableSet D)
    (S : D ≃ᵐ D) {x : X} (hx : x ∈ D) :
    extendEquiv D hD S x = S ⟨x, hx⟩ := by
  classical
  change Equiv.Set.sumCompl D
      (Equiv.sumCongr S.toEquiv (Equiv.refl (Dᶜ : Set X))
        ((Equiv.Set.sumCompl D).symm x)) = S ⟨x, hx⟩
  rw [Equiv.Set.sumCompl_symm_apply_of_mem hx]
  rfl

@[simp]
theorem extendEquiv_apply_of_not_mem (D : Set X) (hD : MeasurableSet D)
    (S : D ≃ᵐ D) {x : X} (hx : x ∉ D) :
    extendEquiv D hD S x = x := by
  classical
  change Equiv.Set.sumCompl D
      (Equiv.sumCongr S.toEquiv (Equiv.refl (Dᶜ : Set X))
        ((Equiv.Set.sumCompl D).symm x)) = x
  rw [Equiv.Set.sumCompl_symm_apply_of_notMem hx]
  rfl

theorem extendEquiv_iterate_apply (D : Set X) (hD : MeasurableSet D)
    (S : D ≃ᵐ D) (k : ℕ) (x : D) :
    ((extendEquiv D hD S : X → X)^[k]) x =
      ((S : D → D)^[k]) x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      exact extendEquiv_apply_of_mem D hD S ((S : D → D)^[k] x).property

theorem subtypeMeasure_preimage (m : Measure X) (D : Set X)
    (hD : MeasurableSet D) (hDfull : m Dᶜ = 0)
    {A : Set X} (_hA : MeasurableSet A) :
    subtypeMeasure m D (((↑) : D → X) ⁻¹' A) = m A := by
  unfold subtypeMeasure
  rw [comap_subtype_coe_apply hD m]
  apply measure_congr
  filter_upwards [ae_iff.mpr hDfull] with x hxD
  apply propext
  constructor
  · rintro ⟨y, hyA, rfl⟩
    exact hyA
  · intro hxA
    exact ⟨⟨x, hxD⟩, hxA, rfl⟩

theorem measurePreserving_extendEquiv (m : Measure X) (D : Set X)
    (hD : MeasurableSet D) (hDfull : m Dᶜ = 0) (S : D ≃ᵐ D)
    (hS : MeasurePreserving S (subtypeMeasure m D) (subtypeMeasure m D)) :
    MeasurePreserving (extendEquiv D hD S) m m := by
  refine ⟨(extendEquiv D hD S).measurable, ?_⟩
  ext A hA
  rw [Measure.map_apply (extendEquiv D hD S).measurable hA]
  let AD : Set D := ((↑) : D → X) ⁻¹' A
  have hAD : MeasurableSet AD := measurable_subtype_coe hA
  have hpre : m ((extendEquiv D hD S) ⁻¹' A) =
      subtypeMeasure m D (S ⁻¹' AD) := by
    unfold subtypeMeasure
    rw [comap_subtype_coe_apply hD m]
    apply measure_congr
    filter_upwards [ae_iff.mpr hDfull] with x hxD
    apply propext
    constructor
    · intro hxA
      refine ⟨⟨x, hxD⟩, ?_, rfl⟩
      change (S ⟨x, hxD⟩ : X) ∈ A
      rw [← extendEquiv_apply_of_mem D hD S hxD]
      exact hxA
    · rintro ⟨y, hy, rfl⟩
      change extendEquiv D hD S y ∈ A
      rw [extendEquiv_apply_of_mem D hD S y.property]
      exact hy
  rw [hpre, hS.measure_preimage hAD.nullMeasurableSet,
    subtypeMeasure_preimage m D hD hDfull hA]

noncomputable def extendAutomorphism (m : Measure X) (D : Set X)
    (hD : MeasurableSet D) (hDfull : m Dᶜ = 0)
    (S : Automorphism (subtypeMeasure m D)) : Automorphism m where
  toEquiv := extendEquiv D hD S.toEquiv
  measurePreserving :=
    measurePreserving_extendEquiv m D hD hDfull S.toEquiv S.measurePreserving

theorem measure_iterate_preimage_inter (m : Measure X) (D : Set X)
    (hD : MeasurableSet D) (hDfull : m Dᶜ = 0) (S : D ≃ᵐ D)
    (k : ℕ) {A B : Set X} (_hA : MeasurableSet A) (_hB : MeasurableSet B) :
    m ((((extendEquiv D hD S : X → X)^[k]) ⁻¹' A) ∩ B) =
      subtypeMeasure m D
        ((((S : D → D)^[k]) ⁻¹' (((↑) : D → X) ⁻¹' A)) ∩
          (((↑) : D → X) ⁻¹' B)) := by
  unfold subtypeMeasure
  rw [comap_subtype_coe_apply hD m]
  apply measure_congr
  filter_upwards [ae_iff.mpr hDfull] with x hxD
  apply propext
  constructor
  · rintro ⟨hxA, hxB⟩
    refine ⟨⟨x, hxD⟩, ⟨?_, hxB⟩, rfl⟩
    change (((S : D → D)^[k]) ⟨x, hxD⟩ : X) ∈ A
    rw [← extendEquiv_iterate_apply D hD S k ⟨x, hxD⟩]
    exact hxA
  · rintro ⟨y, ⟨hyA, hyB⟩, rfl⟩
    constructor
    · change ((extendEquiv D hD S : X → X)^[k]) y ∈ A
      rw [extendEquiv_iterate_apply D hD S k y]
      exact hyA
    · exact hyB

theorem isWeaklyMixing_extend (m : Measure X) (D : Set X)
    (hD : MeasurableSet D) (hDfull : m Dᶜ = 0)
    (S : Automorphism (subtypeMeasure m D)) (hS : IsWeaklyMixing (subtypeMeasure m D) S) :
    IsWeaklyMixing m (extendAutomorphism m D hD hDfull S) := by
  intro A B hA hB
  have hlim := hS (((↑) : D → X) ⁻¹' A) (((↑) : D → X) ⁻¹' B)
    (measurable_subtype_coe hA) (measurable_subtype_coe hB)
  have hmeasureA : subtypeMeasure m D (((↑) : D → X) ⁻¹' A) = m A :=
    subtypeMeasure_preimage m D hD hDfull hA
  have hmeasureB : subtypeMeasure m D (((↑) : D → X) ⁻¹' B) = m B :=
    subtypeMeasure_preimage m D hD hDfull hB
  have hmeasureInter (k : ℕ) :
      m (((((extendAutomorphism m D hD hDfull S).toEquiv : X → X)^[k]) ⁻¹' A) ∩ B) =
        subtypeMeasure m D
          ((((S.toEquiv : D → D)^[k]) ⁻¹' (((↑) : D → X) ⁻¹' A)) ∩
            (((↑) : D → X) ⁻¹' B)) :=
    measure_iterate_preimage_inter m D hD hDfull S.toEquiv k hA hB
  simpa only [hmeasureA, hmeasureB, hmeasureInter] using hlim

end Submission.Conull
