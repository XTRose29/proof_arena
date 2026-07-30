import Submission.GDelta

open LeanEval.Dynamics.HalmosGenericWeakMixingProblem
open MeasureTheory ProbabilityTheory Filter Topology
open scoped symmDiff

namespace Submission.GeneralBernoulli

noncomputable section

variable {Z : Type*} [MeasurableSpace Z]

abbrev Space (Z : Type*) := ℤ → Z

noncomputable def probability (mu : Measure Z) : Measure (Space Z) :=
  Measure.infinitePi (fun _ : ℤ ↦ mu)

instance probability_isProbability (mu : Measure Z) [IsProbabilityMeasure mu] :
    IsProbabilityMeasure (probability mu) := by
  unfold probability
  infer_instance

def shiftIndex : ℤ ≃ ℤ where
  toFun i := i - 1
  invFun i := i + 1
  left_inv i := by simp
  right_inv i := by simp

noncomputable def shiftEquiv : Space Z ≃ᵐ Space Z :=
  MeasurableEquiv.piCongrLeft (fun _ : ℤ ↦ Z) shiftIndex

@[simp]
theorem shiftEquiv_apply (x : Space Z) (i : ℤ) :
    shiftEquiv x i = x (i + 1) := by
  simpa [shiftEquiv, shiftIndex] using
    (MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : ℤ ↦ Z) shiftIndex x (i + 1))

theorem shiftEquiv_map (mu : Measure Z) [IsProbabilityMeasure mu] :
    (probability mu).map shiftEquiv = probability mu := by
  unfold probability shiftEquiv
  exact Measure.infinitePi_map_piCongrLeft (fun _ : ℤ ↦ mu) shiftIndex

noncomputable def shift (mu : Measure Z) [IsProbabilityMeasure mu] :
    Automorphism (probability mu) where
  toEquiv := shiftEquiv
  measurePreserving := ⟨shiftEquiv.measurable, shiftEquiv_map mu⟩

@[simp]
theorem shift_iterate_apply (n : ℕ) (x : Space Z) (i : ℤ) :
    ((shiftEquiv : Space Z → Space Z)^[n]) x i = x (i + n) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih, shiftEquiv_apply]
      congr 1
      omega

theorem independent_coordinates (mu : Measure Z) [IsProbabilityMeasure mu] :
    iIndepFun (fun i : ℤ ↦ fun x : Space Z ↦ x i) (probability mu) := by
  unfold probability
  simpa only [Function.comp_apply] using
    (iIndepFun_infinitePi
      (P := fun _ : ℤ ↦ mu)
      (X := fun _ : ℤ ↦ fun x : Z ↦ x) (by fun_prop))

def translate (I : Finset ℤ) (n : ℕ) : Finset ℤ :=
  I.image (fun i ↦ i + (n : ℤ))

def translateTuple (I : Finset ℤ) (n : ℕ)
    (x : (i : translate I n) → Z) : (i : I) → Z :=
  fun i ↦ x ⟨i + (n : ℤ), by simp [translate]⟩

theorem measurable_translateTuple (I : Finset ℤ) (n : ℕ) :
    Measurable (translateTuple (Z := Z) I n) := by
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

theorem cylinder_eventually_independent (mu : Measure Z)
    [IsProbabilityMeasure mu] (I J : Finset ℤ)
    (S : Set ((i : I) → Z)) (T : Set ((j : J) → Z))
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    ∀ᶠ n : ℕ in atTop,
      probability mu (((shiftEquiv : Space Z → Space Z)^[n] ⁻¹'
          cylinder I S) ∩ cylinder J T) =
        probability mu (cylinder I S) * probability mu (cylinder J T) := by
  classical
  filter_upwards [eventually_disjoint_translate I J] with n hdis
  let K := translate I n
  let f : Space Z → ((i : K) → Z) := fun x i ↦ x i
  let g : Space Z → ((j : J) → Z) := fun x j ↦ x j
  have hfg : IndepFun f g (probability mu) :=
    (independent_coordinates mu).indepFun_finset K J hdis (by fun_prop)
  have hfg' : IndepFun (translateTuple I n ∘ f) g (probability mu) :=
    hfg.comp (measurable_translateTuple I n) measurable_id
  have heq := hfg'.measure_inter_preimage_eq_mul S T hS hT
  have hfpre : (translateTuple I n ∘ f) ⁻¹' S =
      (shiftEquiv : Space Z → Space Z)^[n] ⁻¹' cylinder I S := by
    ext x
    simp only [Set.mem_preimage, Function.comp_apply, mem_cylinder]
    change (fun i : I ↦ x (i + (n : ℤ))) ∈ S ↔
      (fun i : I ↦ ((shiftEquiv : Space Z → Space Z)^[n]) x i) ∈ S
    simp only [shift_iterate_apply]
  have hgpre : g ⁻¹' T = cylinder J T := rfl
  rw [hfpre, hgpre] at heq
  have hmeasure :=
    ((shift mu).measurePreserving.iterate n).measure_preimage
      hS.cylinder.nullMeasurableSet
  change probability mu ((shiftEquiv : Space Z → Space Z)^[n] ⁻¹'
      cylinder I S) = probability mu (cylinder I S) at hmeasure
  rw [hmeasure] at heq
  exact heq

theorem cylinders_measureDense (mu : Measure Z) [IsProbabilityMeasure mu] :
    (probability mu).MeasureDense
      (measurableCylinders (fun _ : ℤ ↦ Z)) := by
  apply Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite
    (probability mu) isSetAlgebra_measurableCylinders
  simpa only using
    (generateFrom_measurableCylinders (α := fun _ : ℤ ↦ Z)).symm

theorem tendsto_correlation (mu : Measure Z) [IsProbabilityMeasure mu]
    (A B : Set (Space Z)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Tendsto (fun n : ℕ ↦
        (probability mu).real
          (((shiftEquiv : Space Z → Space Z)^[n] ⁻¹' A) ∩ B))
      atTop (nhds ((probability mu).real A * (probability mu).real B)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ := ε / 8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨C, hCmem, hAC⟩ := (cylinders_measureDense mu).approx A hA
    (measure_ne_top (probability mu) A) δ hδ
  obtain ⟨D, hDmem, hBD⟩ := (cylinders_measureDense mu).approx B hB
    (measure_ne_top (probability mu) B) δ hδ
  have hC : MeasurableSet C := (cylinders_measureDense mu).measurable C hCmem
  have hD : MeasurableSet D := (cylinders_measureDense mu).measurable D hDmem
  have hACr : (probability mu).real (A ∆ C) < δ :=
    (ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top (probability mu) _)).mp hAC
  have hBDr : (probability mu).real (B ∆ D) < δ :=
    (ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top (probability mu) _)).mp hBD
  obtain ⟨I, S, hS, hCeq⟩ := (mem_measurableCylinders C).mp hCmem
  obtain ⟨J, U, hU, hDeq⟩ := (mem_measurableCylinders D).mp hDmem
  have hev := cylinder_eventually_independent mu I J S U hS hU
  rw [← hCeq, ← hDeq] at hev
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun n hn ↦ ?_⟩
  have hcylReal := congrArg ENNReal.toReal (hN n hn)
  simp only [ENNReal.toReal_mul] at hcylReal
  change (probability mu).real
      (((shiftEquiv : Space Z → Space Z)^[n] ⁻¹' C) ∩ D) =
    (probability mu).real C * (probability mu).real D at hcylReal
  rw [Real.dist_eq]
  have hcorr := GDelta.intersection_perturbation (probability mu)
    (shift mu) n A B C D hA hB hC hD
  have hprod := GDelta.product_perturbation (probability mu)
    A B C D hA hB hC hD
  have hprod' :
      |(probability mu).real C * (probability mu).real D -
          (probability mu).real A * (probability mu).real B| ≤
        (probability mu).real (A ∆ C) + (probability mu).real (B ∆ D) := by
    rw [abs_sub_comm]
    exact hprod
  calc
    |(probability mu).real
          (((shiftEquiv : Space Z → Space Z)^[n] ⁻¹' A) ∩ B) -
        (probability mu).real A * (probability mu).real B| =
      |((probability mu).real
          (((shiftEquiv : Space Z → Space Z)^[n] ⁻¹' A) ∩ B) -
          (probability mu).real
            (((shiftEquiv : Space Z → Space Z)^[n] ⁻¹' C) ∩ D)) +
        ((probability mu).real C * (probability mu).real D -
          (probability mu).real A * (probability mu).real B)| := by
            congr 1
            rw [hcylReal]
            ring
    _ ≤ |(probability mu).real
          (((shiftEquiv : Space Z → Space Z)^[n] ⁻¹' A) ∩ B) -
          (probability mu).real
            (((shiftEquiv : Space Z → Space Z)^[n] ⁻¹' C) ∩ D)| +
        |(probability mu).real C * (probability mu).real D -
          (probability mu).real A * (probability mu).real B| := abs_add_le _ _
    _ ≤ ((probability mu).real (A ∆ C) + (probability mu).real (B ∆ D)) +
        ((probability mu).real (A ∆ C) + (probability mu).real (B ∆ D)) :=
      add_le_add hcorr hprod'
    _ < ε := by dsimp [δ] at hACr hBDr; linarith

theorem shift_isWeaklyMixing (mu : Measure Z) [IsProbabilityMeasure mu] :
    IsWeaklyMixing (probability mu) (shift mu) := by
  intro A B hA hB
  have hcorr := tendsto_correlation mu A B hA hB
  have hconst : Tendsto
      (fun _ : ℕ ↦ (probability mu).real A * (probability mu).real B) atTop
      (nhds ((probability mu).real A * (probability mu).real B)) :=
    tendsto_const_nhds
  have hzero : Tendsto (fun n : ℕ ↦
      |(probability mu).real
          (((shiftEquiv : Space Z → Space Z)^[n] ⁻¹' A) ∩ B) -
        (probability mu).real A * (probability mu).real B|) atTop (nhds 0) := by
    simpa using (hcorr.sub hconst).abs
  have hcesaro := hzero.cesaro
  simpa [shift, Measure.real, div_eq_inv_mul] using hcesaro

end

end Submission.GeneralBernoulli
