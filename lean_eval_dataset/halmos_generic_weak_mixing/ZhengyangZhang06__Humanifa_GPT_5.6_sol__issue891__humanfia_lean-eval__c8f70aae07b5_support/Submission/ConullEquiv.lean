import Submission.Helpers

open MeasureTheory

namespace Submission.ConullEquiv

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- A measurable, measure-preserving equivalence between conull measurable
subsets of two measure spaces. -/
structure Data (m : Measure X) (n : Measure Y) where
  source : Set X
  target : Set Y
  measurableSource : MeasurableSet source
  measurableTarget : MeasurableSet target
  sourceFull : m sourceᶜ = 0
  targetFull : n targetᶜ = 0
  equiv : source ≃ᵐ target
  measurePreserving : MeasurePreserving equiv
    (Measure.comap ((↑) : source → X) m)
    (Measure.comap ((↑) : target → Y) n)

theorem measurePreserving_of_smul (c : ENNReal) (hc0 : c ≠ 0)
    (hcTop : c ≠ (⊤ : ENNReal))
    {m : Measure X} {n : Measure Y} {f : X → Y}
    (h : MeasurePreserving f (c • m) (c • n)) :
    MeasurePreserving f m n := by
  refine ⟨h.measurable, ?_⟩
  apply Measure.ext
  intro s hs
  have heq := congrArg (fun q : Measure Y ↦ q s) h.map_eq
  rw [Measure.map_smul] at heq
  change c * (Measure.map f m) s = c * n s at heq
  exact (ENNReal.mul_right_inj hc0 hcTop).mp heq

theorem exists_data_of_mass_eq [StandardBorelSpace X]
    [StandardBorelSpace Y] (m : Measure X) (n : Measure Y)
    [IsFiniteMeasure m] [IsFiniteMeasure n] [NoAtoms m] [NoAtoms n]
    (hmass : m Set.univ = n Set.univ) (hmassPos : 0 < m Set.univ) :
    Nonempty (Data m n) := by
  let a := m Set.univ
  have ha0 : a ≠ 0 := hmassPos.ne'
  have haTop : a ≠ (⊤ : ENNReal) := by
    dsimp [a]
    exact measure_ne_top m Set.univ
  have haInv0 : a⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr haTop
  have haInvTop : a⁻¹ ≠ (⊤ : ENNReal) := ENNReal.inv_ne_top.mpr ha0
  let m' : Measure X := a⁻¹ • m
  let n' : Measure Y := a⁻¹ • n
  have hm' : m' Set.univ = 1 := by
    simp only [m', Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel ha0 haTop
  have hn' : n' Set.univ = 1 := by
    simp only [n', Measure.smul_apply, smul_eq_mul, ← hmass]
    exact ENNReal.inv_mul_cancel ha0 haTop
  letI : IsProbabilityMeasure m' := ⟨hm'⟩
  letI : IsProbabilityMeasure n' := ⟨hn'⟩
  letI : NoAtoms m' := ⟨fun x ↦ by simp [m', measure_singleton x]⟩
  letI : NoAtoms n' := ⟨fun y ↦ by simp [n', measure_singleton y]⟩
  let R := Helpers.commonUniformRange m' n'
  have hR : MeasurableSet R := Helpers.measurableSet_commonUniformRange m' n'
  have hRfull : volume Rᶜ = 0 := Helpers.volume_commonUniformRange_compl m' n'
  let D := Helpers.uniformSource m' R
  let E := Helpers.uniformSource n' R
  have hD : MeasurableSet D := Helpers.measurableSet_uniformSource m' hR
  have hE : MeasurableSet E := Helpers.measurableSet_uniformSource n' hR
  have hDfull' : m' Dᶜ = 0 := Helpers.measure_uniformSource_compl m' hR hRfull
  have hEfull' : n' Eᶜ = 0 := Helpers.measure_uniformSource_compl n' hR hRfull
  have hDfull : m Dᶜ = 0 := by
    have h := hDfull'
    simp only [m', Measure.smul_apply, smul_eq_mul] at h
    exact ((ENNReal.mul_right_inj haInv0 haInvTop).mp
      (h.trans (mul_zero a⁻¹).symm))
  have hEfull : n Eᶜ = 0 := by
    have h := hEfull'
    simp only [n', Measure.smul_apply, smul_eq_mul] at h
    exact ((ENNReal.mul_right_inj haInv0 haInvTop).mp
      (h.trans (mul_zero a⁻¹).symm))
  let e : D ≃ᵐ E := Helpers.commonUniformEquiv m' n'
  have he' : MeasurePreserving e
      (Measure.comap ((↑) : D → X) m')
      (Measure.comap ((↑) : E → Y) n') :=
    Helpers.measurePreserving_commonUniformEquiv m' n'
  have hcomapM : Measure.comap ((↑) : D → X) m' =
      a⁻¹ • Measure.comap ((↑) : D → X) m := by
    simp [m', Measure.comap_smul]
  have hcomapN : Measure.comap ((↑) : E → Y) n' =
      a⁻¹ • Measure.comap ((↑) : E → Y) n := by
    simp [n', Measure.comap_smul]
  have he : MeasurePreserving e
      (Measure.comap ((↑) : D → X) m)
      (Measure.comap ((↑) : E → Y) n) := by
    apply measurePreserving_of_smul a⁻¹ haInv0 haInvTop
    simpa only [hcomapM, hcomapN] using he'
  exact ⟨{
    source := D
    target := E
    measurableSource := hD
    measurableTarget := hE
    sourceFull := hDfull
    targetFull := hEfull
    equiv := e
    measurePreserving := he
  }⟩

end Submission.ConullEquiv
