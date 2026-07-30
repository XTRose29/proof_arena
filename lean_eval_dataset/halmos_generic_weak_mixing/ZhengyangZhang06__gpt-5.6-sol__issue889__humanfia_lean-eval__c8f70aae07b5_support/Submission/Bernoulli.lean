import ChallengeDeps

open LeanEval.Dynamics.HalmosGenericWeakMixingProblem
open MeasureTheory ProbabilityTheory Filter Topology
open scoped symmDiff

namespace Submission.Bernoulli

abbrev Alphabet := Set.Icc (0 : ℝ) 1

abbrev Space := ℤ → Alphabet

noncomputable def probability : Measure Space :=
  Measure.infinitePi (fun _ : ℤ ↦ (volume : Measure Alphabet))

instance : IsProbabilityMeasure probability := by
  unfold probability
  infer_instance

instance : NoAtoms probability := ⟨fun x ↦ by
  have hsub : ({x} : Set Space) ⊆ (fun y : Space ↦ y 0) ⁻¹' {x 0} := by
    intro y hy
    simpa only [Set.mem_singleton_iff, Set.mem_preimage] using congrFun hy 0
  apply measure_mono_null hsub
  unfold probability
  rw [(measurePreserving_eval_infinitePi
    (fun _ : ℤ ↦ (volume : Measure Alphabet)) 0).measure_preimage
      (MeasurableSet.singleton _).nullMeasurableSet]
  exact measure_singleton _⟩

def shiftIndex : ℤ ≃ ℤ where
  toFun i := i - 1
  invFun i := i + 1
  left_inv i := by simp
  right_inv i := by simp

noncomputable def shiftEquiv : Space ≃ᵐ Space :=
  MeasurableEquiv.piCongrLeft (fun _ : ℤ ↦ Alphabet) shiftIndex

@[simp]
theorem shiftEquiv_apply (x : Space) (i : ℤ) : shiftEquiv x i = x (i + 1) := by
  simpa [shiftEquiv, shiftIndex] using
    (MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : ℤ ↦ Alphabet) shiftIndex x (i + 1))

theorem shiftEquiv_map : probability.map shiftEquiv = probability := by
  unfold probability shiftEquiv
  exact Measure.infinitePi_map_piCongrLeft
    (fun _ : ℤ ↦ (volume : Measure Alphabet)) shiftIndex

noncomputable def shift : Automorphism probability where
  toEquiv := shiftEquiv
  measurePreserving := ⟨shiftEquiv.measurable, shiftEquiv_map⟩

@[simp]
theorem shift_iterate_apply (n : ℕ) (x : Space) (i : ℤ) :
    ((shiftEquiv : Space → Space)^[n]) x i = x (i + n) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih, shiftEquiv_apply]
      congr 1
      omega

theorem independent_coordinates :
    iIndepFun (fun i : ℤ ↦ fun x : Space ↦ x i) probability := by
  unfold probability
  simpa only [Function.comp_apply] using
    (iIndepFun_infinitePi
      (P := fun _ : ℤ ↦ (volume : Measure Alphabet))
      (X := fun _ : ℤ ↦ fun x : Alphabet ↦ x) (by fun_prop))

def translate (I : Finset ℤ) (n : ℕ) : Finset ℤ :=
  I.image (fun i ↦ i + (n : ℤ))

def translateTuple (I : Finset ℤ) (n : ℕ)
    (x : (i : translate I n) → Alphabet) : (i : I) → Alphabet :=
  fun i ↦ x ⟨i + (n : ℤ), by simp [translate]⟩

theorem measurable_translateTuple (I : Finset ℤ) (n : ℕ) :
    Measurable (translateTuple I n) := by
  apply measurable_pi_lambda _
  intro i
  exact measurable_pi_apply
    (⟨i + (n : ℤ), by simp [translate]⟩ : translate I n)

theorem eventually_disjoint_translate (I J : Finset ℤ) :
    ∀ᶠ n : ℕ in atTop, Disjoint (translate I n) J := by
  classical
  by_cases hI : I.Nonempty
  · by_cases hJ : J.Nonempty
    · let d : ℤ := J.max' hJ - I.min' hI
      let N : ℕ := d.natAbs + 1
      filter_upwards [eventually_ge_atTop N] with n hn
      rw [Finset.disjoint_left]
      intro z hzI hzJ
      rw [translate, Finset.mem_image] at hzI
      obtain ⟨i, hiI, rfl⟩ := hzI
      have hmin : I.min' hI ≤ i := I.min'_le i hiI
      have hmax : i + (n : ℤ) ≤ J.max' hJ := J.le_max' _ hzJ
      have hd : d ≤ (d.natAbs : ℤ) := Int.le_natAbs
      have hn' : (d.natAbs : ℤ) + 1 ≤ (n : ℤ) := by exact_mod_cast hn
      omega
    · simp [Finset.not_nonempty_iff_eq_empty.mp hJ]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hI, translate]

theorem cylinder_eventually_independent
    (I J : Finset ℤ) (S : Set ((i : I) → Alphabet))
    (T : Set ((j : J) → Alphabet)) (hS : MeasurableSet S)
    (hT : MeasurableSet T) :
    ∀ᶠ n : ℕ in atTop,
      probability (((shiftEquiv : Space → Space)^[n] ⁻¹'
          cylinder I S) ∩ cylinder J T) =
        probability (cylinder I S) * probability (cylinder J T) := by
  classical
  filter_upwards [eventually_disjoint_translate I J] with n hdis
  let K := translate I n
  let f : Space → ((i : K) → Alphabet) := fun x i ↦ x i
  let g : Space → ((j : J) → Alphabet) := fun x j ↦ x j
  have hfg : IndepFun f g probability := by
    exact independent_coordinates.indepFun_finset K J hdis (by fun_prop)
  have hfg' : IndepFun (translateTuple I n ∘ f) g probability :=
    hfg.comp (measurable_translateTuple I n) measurable_id
  have heq := hfg'.measure_inter_preimage_eq_mul S T hS hT
  have hfpre : (translateTuple I n ∘ f) ⁻¹' S =
      (shiftEquiv : Space → Space)^[n] ⁻¹' cylinder I S := by
    ext x
    simp only [Set.mem_preimage, Function.comp_apply, mem_cylinder]
    change (fun i : I ↦ x (i + (n : ℤ))) ∈ S ↔
      (fun i : I ↦ ((shiftEquiv : Space → Space)^[n]) x i) ∈ S
    simp only [shift_iterate_apply]
  have hgpre : g ⁻¹' T = cylinder J T := rfl
  rw [hfpre, hgpre] at heq
  have hmeasure :=
    (shift.measurePreserving.iterate n).measure_preimage hS.cylinder.nullMeasurableSet
  change probability ((shiftEquiv : Space → Space)^[n] ⁻¹' cylinder I S) =
    probability (cylinder I S) at hmeasure
  rw [hmeasure] at heq
  exact heq

theorem cylinders_measureDense :
    probability.MeasureDense
      (measurableCylinders (fun _ : ℤ ↦ Alphabet)) := by
  apply Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite probability
    isSetAlgebra_measurableCylinders
  simpa only using
    (generateFrom_measurableCylinders
      (α := fun _ : ℤ ↦ Alphabet)).symm

theorem measureReal_inter_symmDiff_le
    (A B C D : Set Space) :
    probability.real ((A ∩ B) ∆ (C ∩ D)) ≤
      probability.real (A ∆ C) + probability.real (B ∆ D) := by
  calc
    probability.real ((A ∩ B) ∆ (C ∩ D)) ≤
        probability.real ((A ∆ C) ∪ (B ∆ D)) :=
      measureReal_mono (by grind)
    _ ≤ probability.real (A ∆ C) + probability.real (B ∆ D) :=
      measureReal_union_le _ _

theorem abs_mul_sub_mul_le {a b c d : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    |a * b - c * d| ≤ |a - c| + |b - d| := by
  calc
    |a * b - c * d| = |(a - c) * b + c * (b - d)| := by ring_nf
    _ ≤ |(a - c) * b| + |c * (b - d)| := abs_add_le _ _
    _ = |a - c| * b + c * |b - d| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hb0, abs_of_nonneg hc0]
    _ ≤ |a - c| + |b - d| := by
      nlinarith [abs_nonneg (a - c), abs_nonneg (b - d)]

theorem product_perturbation (A B C D : Set Space)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hD : MeasurableSet D) :
    |probability.real A * probability.real B -
        probability.real C * probability.real D| ≤
      probability.real (A ∆ C) + probability.real (B ∆ D) := by
  refine (abs_mul_sub_mul_le measureReal_nonneg measureReal_le_one
    measureReal_nonneg measureReal_le_one).trans ?_
  exact add_le_add
    (abs_measureReal_sub_le_measureReal_symmDiff
      hA.nullMeasurableSet hC.nullMeasurableSet)
    (abs_measureReal_sub_le_measureReal_symmDiff
      hB.nullMeasurableSet hD.nullMeasurableSet)

theorem correlation_perturbation (n : ℕ) (A B C D : Set Space)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hD : MeasurableSet D) :
    |probability.real (((shiftEquiv : Space → Space)^[n] ⁻¹' A) ∩ B) -
        probability.real (((shiftEquiv : Space → Space)^[n] ⁻¹' C) ∩ D)| ≤
      probability.real (A ∆ C) + probability.real (B ∆ D) := by
  let f : Space → Space := (shiftEquiv : Space → Space)^[n]
  have hmp := shift.measurePreserving.iterate n
  have hf : Measurable f := by
    change Measurable ((shift.toEquiv : Space → Space)^[n])
    exact hmp.measurable
  have hpre : (f ⁻¹' A) ∆ (f ⁻¹' C) = f ⁻¹' (A ∆ C) := by
    ext x
    simp only [Set.mem_symmDiff, Set.mem_preimage]
  calc
    |probability.real (f ⁻¹' A ∩ B) - probability.real (f ⁻¹' C ∩ D)| ≤
        probability.real ((f ⁻¹' A ∩ B) ∆ (f ⁻¹' C ∩ D)) :=
      abs_measureReal_sub_le_measureReal_symmDiff
        ((hA.preimage hf).inter hB).nullMeasurableSet
        ((hC.preimage hf).inter hD).nullMeasurableSet
    _ ≤ probability.real ((f ⁻¹' A) ∆ (f ⁻¹' C)) +
        probability.real (B ∆ D) := measureReal_inter_symmDiff_le _ _ _ _
    _ = probability.real (A ∆ C) + probability.real (B ∆ D) := by
      rw [hpre]
      change probability.real
        (((shift.toEquiv : Space → Space)^[n]) ⁻¹' (A ∆ C)) + _ = _
      congr 1
      exact congrArg ENNReal.toReal
        (hmp.measure_preimage (hA.symmDiff hC).nullMeasurableSet)

theorem tendsto_correlation (A B : Set Space)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Tendsto (fun n : ℕ ↦
        probability.real (((shiftEquiv : Space → Space)^[n] ⁻¹' A) ∩ B))
      atTop (𝓝 (probability.real A * probability.real B)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ := ε / 8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨C, hCmem, hAC⟩ := cylinders_measureDense.approx A hA
    (measure_ne_top probability A) δ hδ
  obtain ⟨D, hDmem, hBD⟩ := cylinders_measureDense.approx B hB
    (measure_ne_top probability B) δ hδ
  have hC : MeasurableSet C := cylinders_measureDense.measurable C hCmem
  have hD : MeasurableSet D := cylinders_measureDense.measurable D hDmem
  have hACr : probability.real (A ∆ C) < δ :=
    (ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top probability _)).mp hAC
  have hBDr : probability.real (B ∆ D) < δ :=
    (ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top probability _)).mp hBD
  obtain ⟨I, S, hS, hCeq⟩ := (mem_measurableCylinders C).mp hCmem
  obtain ⟨J, T, hT, hDeq⟩ := (mem_measurableCylinders D).mp hDmem
  have hev := cylinder_eventually_independent I J S T hS hT
  rw [← hCeq, ← hDeq] at hev
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun n hn ↦ ?_⟩
  have hcyl := hN n hn
  have hcylReal := congrArg ENNReal.toReal hcyl
  simp only [ENNReal.toReal_mul] at hcylReal
  change probability.real (((shiftEquiv : Space → Space)^[n] ⁻¹' C) ∩ D) =
    probability.real C * probability.real D at hcylReal
  rw [Real.dist_eq]
  have hcorr := correlation_perturbation n A B C D hA hB hC hD
  have hprod := product_perturbation A B C D hA hB hC hD
  have hprod' :
      |probability.real C * probability.real D -
          probability.real A * probability.real B| ≤
        probability.real (A ∆ C) + probability.real (B ∆ D) := by
    rw [abs_sub_comm]
    exact hprod
  calc
    |probability.real (((shiftEquiv : Space → Space)^[n] ⁻¹' A) ∩ B) -
        probability.real A * probability.real B| =
      |(probability.real (((shiftEquiv : Space → Space)^[n] ⁻¹' A) ∩ B) -
          probability.real (((shiftEquiv : Space → Space)^[n] ⁻¹' C) ∩ D)) +
        (probability.real C * probability.real D -
          probability.real A * probability.real B)| := by
            congr 1
            rw [hcylReal]
            ring
    _ ≤ |probability.real (((shiftEquiv : Space → Space)^[n] ⁻¹' A) ∩ B) -
          probability.real (((shiftEquiv : Space → Space)^[n] ⁻¹' C) ∩ D)| +
        |probability.real C * probability.real D -
          probability.real A * probability.real B| := abs_add_le _ _
    _ ≤ (probability.real (A ∆ C) + probability.real (B ∆ D)) +
        (probability.real (A ∆ C) + probability.real (B ∆ D)) :=
      add_le_add hcorr hprod'
    _ < ε := by dsimp [δ] at hACr hBDr; linarith

theorem shift_isWeaklyMixing : IsWeaklyMixing probability shift := by
  intro A B hA hB
  have hcorr := tendsto_correlation A B hA hB
  have hconst : Tendsto
      (fun _ : ℕ ↦ probability.real A * probability.real B) atTop
      (𝓝 (probability.real A * probability.real B)) := tendsto_const_nhds
  have hzero : Tendsto (fun n : ℕ ↦
      |probability.real (((shiftEquiv : Space → Space)^[n] ⁻¹' A) ∩ B) -
        probability.real A * probability.real B|) atTop (𝓝 0) := by
    simpa using (hcorr.sub hconst).abs
  have hcesaro := hzero.cesaro
  simpa [shift, Measure.real, div_eq_inv_mul] using hcesaro

end Submission.Bernoulli
