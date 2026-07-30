import ChallengeDeps

open LeanEval.Dynamics.HalmosGenericWeakMixingProblem
open MeasureTheory Filter Topology

variable {X : Type*} [MeasurableSpace X]

namespace Submission.Helpers

namespace Automorphism

def refl (m : Measure X) : Automorphism m where
  toEquiv := MeasurableEquiv.refl X
  measurePreserving := MeasurePreserving.id m

def comp {m : Measure X} (S T : Automorphism m) : Automorphism m where
  toEquiv := T.toEquiv.trans S.toEquiv
  measurePreserving := S.measurePreserving.comp T.measurePreserving

def symm {m : Measure X} (T : Automorphism m) : Automorphism m where
  toEquiv := T.toEquiv.symm
  measurePreserving := T.measurePreserving.symm T.toEquiv

def conj {m : Measure X} (Q T : Automorphism m) : Automorphism m :=
  comp (comp Q T) (symm Q)

@[simp]
theorem coe_refl (m : Measure X) : (refl m).toEquiv = MeasurableEquiv.refl X := rfl

@[simp]
theorem coe_comp {m : Measure X} (S T : Automorphism m) :
    ((comp S T).toEquiv : X → X) = (S.toEquiv : X → X) ∘ T.toEquiv := rfl

@[simp]
theorem coe_symm {m : Measure X} (T : Automorphism m) :
    (symm T).toEquiv = T.toEquiv.symm := rfl

@[simp]
theorem coe_conj {m : Measure X} (Q T : Automorphism m) :
    ((conj Q T).toEquiv : X → X) =
      (Q.toEquiv : X → X) ∘ (T.toEquiv : X → X) ∘ Q.toEquiv.symm := by
  rfl

theorem measure_image {m : Measure X} (T : Automorphism m) (s : Set X) :
    m (T.toEquiv '' s) = m s := by
  change m (T.toEquiv.toEquiv '' s) = m s
  rw [Equiv.image_eq_preimage_symm]
  exact (T.measurePreserving.symm T.toEquiv).measure_preimage_equiv s

theorem measure_preimage {m : Measure X} (T : Automorphism m) (s : Set X) :
    m (T.toEquiv ⁻¹' s) = m s :=
  T.measurePreserving.measure_preimage_equiv s

end Automorphism

theorem isWeaklyMixing_conj_of {m : Measure X} {T : Automorphism m}
    (Q : Automorphism m) (hT : IsWeaklyMixing m T) :
    IsWeaklyMixing m (Automorphism.conj Q T) := by
  intro A B hA hB
  let S := Automorphism.conj Q T
  let q : X → X := Q.toEquiv
  let t : X → X := T.toEquiv
  let s : X → X := S.toEquiv
  have hsem : Function.Semiconj q t s := by
    intro x
    simp [q, t, s, S]
  have hset (k : ℕ) :
      s^[k] ⁻¹' A ∩ B =
        Q.toEquiv '' (t^[k] ⁻¹' (q ⁻¹' A) ∩ (q ⁻¹' B)) := by
    change _ = Q.toEquiv.toEquiv '' _
    rw [Equiv.image_eq_preimage_symm]
    ext x
    have hk := (hsem.iterate_right k) (Q.toEquiv.symm x)
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    change (s^[k] x ∈ A ∧ x ∈ B) ↔
      (q (t^[k] (Q.toEquiv.symm x)) ∈ A ∧ q (Q.toEquiv.symm x) ∈ B)
    rw [hk]
    simp [q]
  have hmeasure (k : ℕ) :
      m (s^[k] ⁻¹' A ∩ B) = m (t^[k] ⁻¹' (q ⁻¹' A) ∩ (q ⁻¹' B)) := by
    rw [hset]
    exact Automorphism.measure_image Q _
  have hA' : MeasurableSet (q ⁻¹' A) := Q.toEquiv.measurable hA
  have hB' : MeasurableSet (q ⁻¹' B) := Q.toEquiv.measurable hB
  have hlim := hT (q ⁻¹' A) (q ⁻¹' B) hA' hB'
  have hmA : m (q ⁻¹' A) = m A := Automorphism.measure_preimage Q A
  have hmB : m (q ⁻¹' B) = m B := Automorphism.measure_preimage Q B
  simpa only [hmeasure, hmA, hmB, s, t, S] using hlim

theorem ergodic_of_isWeaklyMixing (m : Measure X) [IsProbabilityMeasure m]
    (T : Automorphism m) (hT : IsWeaklyMixing m T) :
    Ergodic (T.toEquiv : X → X) m := by
  refine ⟨T.measurePreserving, ?_⟩
  refine ⟨?_⟩
  intro s hs hinv
  let a := (m s).toReal
  let b := (m sᶜ).toReal
  have hiter (k : ℕ) : (T.toEquiv : X → X)^[k] ⁻¹' s = s :=
    Function.IsFixedPt.preimage_iterate hinv k
  have hlim_zero := hT s sᶜ hs hs.compl
  have hlim_prod :
      Tendsto (fun n : ℕ =>
        (∑ k ∈ Finset.range n,
          |(m ((T.toEquiv : X → X)^[k] ⁻¹' s ∩ sᶜ)).toReal - a * b|) / (n : ℝ))
        atTop (𝓝 (a * b)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    simp_rw [hiter]
    simp [a, b, hn.ne']
  have hab : a * b = 0 := tendsto_nhds_unique hlim_prod hlim_zero
  rw [eventuallyConst_set']
  rcases mul_eq_zero.mp hab with ha | hb
  · left
    exact ae_eq_empty.mpr
      ((ENNReal.toReal_eq_zero_iff (m s)).mp ha |>.resolve_right (measure_ne_top m s))
  · right
    exact ae_eq_univ.mpr
      ((ENNReal.toReal_eq_zero_iff (m sᶜ)).mp hb |>.resolve_right (measure_ne_top m sᶜ))

theorem exists_strict_measurable_subset [StandardBorelSpace X]
    (m : Measure X) [IsFiniteMeasure m] [NoAtoms m] {s : Set X}
    (hs : MeasurableSet s) (hms : 0 < m s) :
    ∃ t : Set X, MeasurableSet t ∧ t ⊆ s ∧ 0 < m t ∧ m t < m s := by
  by_contra! h
  let μ : Measure X := (m s)⁻¹ • m.restrict s
  have hms_ne_top : m s ≠ ⊤ := measure_ne_top m s
  have hμ_apply (u : Set X) (hu : MeasurableSet u) :
      μ u = (m s)⁻¹ * m (u ∩ s) := by
    simp [μ, Measure.restrict_apply hu]
  have hμ_univ : μ Set.univ = 1 := by
    rw [hμ_apply Set.univ MeasurableSet.univ, Set.univ_inter]
    exact ENNReal.inv_mul_cancel hms.ne' hms_ne_top
  letI : IsZeroOneMeasure μ := ⟨by
    intro u hu
    by_cases hu0 : m (u ∩ s) = 0
    · left
      simp [hμ_apply u hu, hu0]
    · right
      have hu_pos : 0 < m (u ∩ s) := bot_lt_iff_ne_bot.mpr hu0
      have hsu : m s ≤ m (u ∩ s) :=
        h (u ∩ s) (hu.inter hs) Set.inter_subset_right hu_pos
      have hueq : m (u ∩ s) = m s :=
        le_antisymm (measure_mono Set.inter_subset_right) hsu
      rw [hμ_apply u hu, hueq]
      exact ENNReal.inv_mul_cancel hms.ne' hms_ne_top⟩
  haveI : NeZero μ := ⟨by
    intro hμ
    have := congrArg (fun ν : Measure X => ν Set.univ) hμ
    simp [hμ_univ] at this⟩
  obtain ⟨x, hx⟩ := IsZeroOneMeasure.exists_eq_dirac (μ := μ)
  have hzero : μ {x} = 0 := by
    rw [hμ_apply {x} (MeasurableSet.singleton x)]
    rw [measure_mono_null Set.inter_subset_left (measure_singleton x), mul_zero]
  have hone : μ {x} = 1 := by
    rw [hx]
    simp
  exact zero_ne_one (hzero.symm.trans hone)

theorem noAtoms_map_of_injective {Y : Type*} [MeasurableSpace Y]
    [MeasurableSingletonClass Y] (m : Measure X) [NoAtoms m]
    {f : X → Y} (hf : Measurable f) (hinj : Function.Injective f) :
    NoAtoms (m.map f) := by
  refine ⟨fun y ↦ ?_⟩
  rw [Measure.map_apply hf (MeasurableSet.singleton y)]
  exact (Set.subsingleton_singleton.preimage hinj).measure_zero m

theorem continuous_cdf_of_noAtoms (m : Measure ℝ) [IsProbabilityMeasure m]
    [NoAtoms m] : Continuous (ProbabilityTheory.cdf m) := by
  rw [continuous_iff_continuousAt]
  intro x
  let F := ProbabilityTheory.cdf m
  apply F.mono.continuousAt_iff_leftLim_eq_rightLim.mpr
  rw [F.rightLim_eq]
  apply le_antisymm (F.mono.leftLim_le le_rfl)
  have hz : ENNReal.ofReal (F x - Function.leftLim F x) = 0 := by
    rw [← F.measure_singleton, ProbabilityTheory.measure_cdf]
    exact measure_singleton x
  exact sub_nonpos.mp (ENNReal.ofReal_eq_zero.mp hz)

theorem exists_cdf_eq_of_mem_Ioo (m : Measure ℝ) [IsProbabilityMeasure m]
    [NoAtoms m] {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ x : ℝ, ProbabilityTheory.cdf m x = p := by
  let F := ProbabilityTheory.cdf m
  have haev : ∀ᶠ x in atBot, F x < p :=
    (ProbabilityTheory.tendsto_cdf_atBot m) (Iio_mem_nhds hp.1)
  have hbev : ∀ᶠ x in atTop, p < F x :=
    (ProbabilityTheory.tendsto_cdf_atTop m) (Ioi_mem_nhds hp.2)
  obtain ⟨a, ha⟩ := haev.exists
  obtain ⟨b, hb⟩ := hbev.exists
  have hab : a ≤ b := by
    by_contra hba
    have hmono := ProbabilityTheory.monotone_cdf (μ := m) (le_of_not_ge hba)
    linarith
  obtain ⟨x, -, hx⟩ := intermediate_value_Icc hab
      (continuous_cdf_of_noAtoms m).continuousOn
      ⟨ha.le, hb.le⟩
  exact ⟨x, hx⟩

theorem exists_measurableSet_measureReal_eq [StandardBorelSpace X]
    (m : Measure X) [IsProbabilityMeasure m] [NoAtoms m]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ s : Set X, MeasurableSet s ∧ (m s).toReal = p := by
  rcases hp0.eq_or_lt with rfl | hp0
  · exact ⟨∅, MeasurableSet.empty, by simp⟩
  rcases hp1.eq_or_lt with rfl | hp1
  · exact ⟨Set.univ, MeasurableSet.univ, by simp⟩
  let e := embeddingReal X
  let ν := m.map e
  letI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (measurable_embeddingReal X).aemeasurable
  letI : NoAtoms ν := noAtoms_map_of_injective m
    (measurable_embeddingReal X) (measurableEmbedding_embeddingReal X).injective
  obtain ⟨x, hx⟩ := exists_cdf_eq_of_mem_Ioo ν ⟨hp0, hp1⟩
  refine ⟨e ⁻¹' Set.Iic x, (measurable_embeddingReal X) measurableSet_Iic, ?_⟩
  rw [← Measure.map_apply (measurable_embeddingReal X) measurableSet_Iic]
  change ν.real (Set.Iic x) = p
  rw [← ProbabilityTheory.cdf_eq_real]
  exact hx

theorem exists_measurable_subset_measureReal_eq [StandardBorelSpace X]
    (m : Measure X) [IsFiniteMeasure m] [NoAtoms m]
    {s : Set X} (hs : MeasurableSet s) {p : ℝ}
    (hp0 : 0 ≤ p) (hp : p ≤ (m s).toReal) :
    ∃ t : Set X, MeasurableSet t ∧ t ⊆ s ∧ (m t).toReal = p := by
  by_cases hms : m s = 0
  · have hpz : p = 0 := by
      have : (m s).toReal = 0 := by simp [hms]
      linarith
    exact ⟨∅, MeasurableSet.empty, Set.empty_subset s, by simp [hpz]⟩
  let μ : Measure X := (m s)⁻¹ • m.restrict s
  have hms_ne_top : m s ≠ ⊤ := measure_ne_top m s
  have hms_real_pos : 0 < (m s).toReal := ENNReal.toReal_pos hms hms_ne_top
  have hμ_apply (u : Set X) (hu : MeasurableSet u) :
      μ u = (m s)⁻¹ * m (u ∩ s) := by
    simp [μ, Measure.restrict_apply hu]
  have hμ_univ : μ Set.univ = 1 := by
    rw [hμ_apply Set.univ MeasurableSet.univ, Set.univ_inter]
    exact ENNReal.inv_mul_cancel hms hms_ne_top
  letI : IsProbabilityMeasure μ := ⟨hμ_univ⟩
  letI : NoAtoms μ := ⟨by
    intro x
    simp [μ, measure_singleton x]⟩
  let q := p / (m s).toReal
  have hq0 : 0 ≤ q := div_nonneg hp0 hms_real_pos.le
  have hq1 : q ≤ 1 := (div_le_one hms_real_pos).mpr hp
  obtain ⟨u, hu, hμu⟩ := exists_measurableSet_measureReal_eq μ hq0 hq1
  refine ⟨u ∩ s, hu.inter hs, Set.inter_subset_right, ?_⟩
  rw [hμ_apply u hu, ENNReal.toReal_mul, ENNReal.toReal_inv] at hμu
  change (m s).toReal⁻¹ * (m (u ∩ s)).toReal =
    p / (m s).toReal at hμu
  field_simp [hms_real_pos.ne'] at hμu
  exact hμu

theorem measureReal_preimage_cdf_Iic (m : Measure ℝ) [IsProbabilityMeasure m]
    [NoAtoms m] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    m.real (ProbabilityTheory.cdf m ⁻¹' Set.Iic p) = p := by
  let F := ProbabilityTheory.cdf m
  have hupper : m.real (F ⁻¹' Set.Iic p) ≤ p := by
    apply le_of_forall_pos_le_add
    intro ε hε
    by_cases hpε : p + ε < 1
    · obtain ⟨y, hy⟩ := exists_cdf_eq_of_mem_Ioo m
        ⟨lt_of_le_of_lt hp0 (lt_add_of_pos_right p hε), hpε⟩
      have hsub : F ⁻¹' Set.Iic p ⊆ Set.Iic y := by
        intro z hz
        by_contra hyz
        have hyz' : y ≤ z := le_of_not_ge hyz
        have := ProbabilityTheory.monotone_cdf (μ := m) hyz'
        change F y ≤ F z at this
        change F z ≤ p at hz
        linarith
      calc
        m.real (F ⁻¹' Set.Iic p) ≤ m.real (Set.Iic y) := measureReal_mono hsub
        _ = F y := (ProbabilityTheory.cdf_eq_real m y).symm
        _ = p + ε := hy
    · exact measureReal_le_one.trans (le_of_not_gt hpε)
  have hlower : p ≤ m.real (F ⁻¹' Set.Iic p) := by
    rcases hp0.eq_or_lt with rfl | hp0
    · exact measureReal_nonneg
    by_cases hp1' : p = 1
    · subst p
      have hset : F ⁻¹' Set.Iic 1 = Set.univ := by
        ext x
        simp [F, ProbabilityTheory.cdf_le_one]
      rw [hset]
      simp
    · obtain ⟨x, hx⟩ := exists_cdf_eq_of_mem_Ioo m
        ⟨hp0, lt_of_le_of_ne hp1 hp1'⟩
      have hsub : Set.Iic x ⊆ F ⁻¹' Set.Iic p := by
        intro z hz
        change F z ≤ p
        rw [← hx]
        exact ProbabilityTheory.monotone_cdf (μ := m) hz
      calc
        p = F x := hx.symm
        _ = m.real (Set.Iic x) := ProbabilityTheory.cdf_eq_real m x
        _ ≤ m.real (F ⁻¹' Set.Iic p) := measureReal_mono hsub
  exact le_antisymm hupper hlower

noncomputable def cdfToUnitInterval (m : Measure ℝ) (x : ℝ) : Set.Icc (0 : ℝ) 1 :=
  ⟨ProbabilityTheory.cdf m x,
    ProbabilityTheory.cdf_nonneg m x, ProbabilityTheory.cdf_le_one m x⟩

theorem measurable_cdfToUnitInterval (m : Measure ℝ) [IsProbabilityMeasure m]
    [NoAtoms m] : Measurable (cdfToUnitInterval m) := by
  change Measurable (fun x ↦
    (⟨ProbabilityTheory.cdf m x, ProbabilityTheory.cdf_nonneg m x,
      ProbabilityTheory.cdf_le_one m x⟩ : Set.Icc (0 : ℝ) 1))
  exact (continuous_cdf_of_noAtoms m).measurable.subtype_mk

theorem map_cdfToUnitInterval (m : Measure ℝ) [IsProbabilityMeasure m]
    [NoAtoms m] : m.map (cdfToUnitInterval m) = volume := by
  letI : IsProbabilityMeasure (m.map (cdfToUnitInterval m)) :=
    Measure.isProbabilityMeasure_map (measurable_cdfToUnitInterval m).aemeasurable
  apply Measure.ext_of_Iic
  intro a
  rw [Measure.map_apply (measurable_cdfToUnitInterval m) measurableSet_Iic]
  have hreal := measureReal_preimage_cdf_Iic m a.2.1 a.2.2
  change m.real (ProbabilityTheory.cdf m ⁻¹' Set.Iic (a : ℝ)) = (a : ℝ) at hreal
  have hreal' : m.real (cdfToUnitInterval m ⁻¹' Set.Iic a) = (a : ℝ) := by
    have hpre : cdfToUnitInterval m ⁻¹' Set.Iic a =
        ProbabilityTheory.cdf m ⁻¹' Set.Iic (a : ℝ) := by
      ext x
      rfl
    rw [hpre]
    exact hreal
  rw [unitInterval.volume_Iic]
  rw [← ENNReal.ofReal_toReal (measure_ne_top m _)]
  change ENNReal.ofReal (m.real (cdfToUnitInterval m ⁻¹' Set.Iic a)) =
    ENNReal.ofReal (a : ℝ)
  rw [hreal']

theorem measure_preimage_cdf_singleton (m : Measure ℝ) [IsProbabilityMeasure m]
    [NoAtoms m] (c : ℝ) : m (ProbabilityTheory.cdf m ⁻¹' {c}) = 0 := by
  let F := ProbabilityTheory.cdf m
  by_cases hc0 : c < 0
  · have hset : F ⁻¹' {c} = ∅ := by
      ext x
      change (F x = c) ↔ False
      constructor
      · intro hx
        have hneg : F x < 0 := hx.trans_lt hc0
        exact (not_lt_of_ge (ProbabilityTheory.cdf_nonneg m x)) hneg
      · exact False.elim
    rw [hset, measure_empty]
  by_cases hc1 : 1 < c
  · have hset : F ⁻¹' {c} = ∅ := by
      ext x
      change (F x = c) ↔ False
      constructor
      · intro hx
        have hone : 1 < F x := hc1.trans_le hx.symm.le
        exact (not_lt_of_ge (ProbabilityTheory.cdf_le_one m x)) hone
      · exact False.elim
    rw [hset, measure_empty]
  have hc0' : 0 ≤ c := le_of_not_gt hc0
  have hc1' : c ≤ 1 := le_of_not_gt hc1
  have hreal : m.real (F ⁻¹' {c}) = 0 := by
    apply le_antisymm ?_ measureReal_nonneg
    apply le_of_forall_pos_le_add
    intro ε hε
    simp only [zero_add]
    rcases hc0'.eq_or_lt with rfl | hcpos
    · by_cases hε1 : 1 ≤ ε
      · exact measureReal_le_one.trans hε1
      · have hε1' : ε ≤ 1 := le_of_not_ge hε1
        have hsub : F ⁻¹' {(0 : ℝ)} ⊆ F ⁻¹' Set.Iic ε := by
          intro x hx
          change F x = 0 at hx
          change F x ≤ ε
          rw [hx]
          exact le_of_lt hε
        calc
          m.real (F ⁻¹' {(0 : ℝ)}) ≤ m.real (F ⁻¹' Set.Iic ε) :=
            measureReal_mono hsub
          _ = ε := measureReal_preimage_cdf_Iic m hε.le hε1'
    · let q := max 0 (c - ε)
      have hq0 : 0 ≤ q := le_max_left _ _
      have hqc : q < c := by
        simp only [q, max_lt_iff]
        exact ⟨hcpos, sub_lt_self c hε⟩
      have hq1 : q ≤ 1 := (le_of_lt hqc).trans hc1'
      let Ec := F ⁻¹' Set.Iic c
      let Eq := F ⁻¹' Set.Iic q
      have hEqc : Eq ⊆ Ec := fun x hx ↦ hx.trans hqc.le
      have hEq_meas : MeasurableSet Eq :=
        (continuous_cdf_of_noAtoms m).measurable measurableSet_Iic
      have hfib : F ⁻¹' {c} ⊆ Ec \ Eq := by
        intro x hx
        change F x = c at hx
        change F x ≤ c ∧ ¬F x ≤ q
        rw [hx]
        exact ⟨le_rfl, not_le_of_gt hqc⟩
      calc
        m.real (F ⁻¹' {c}) ≤ m.real (Ec \ Eq) := measureReal_mono hfib
        _ = m.real Ec - m.real Eq := measureReal_sdiff hEqc hEq_meas
        _ = c - q := by
          rw [show m.real Ec = c by
                simpa [Ec] using measureReal_preimage_cdf_Iic m hc0' hc1',
            show m.real Eq = q by
                simpa [Eq] using measureReal_preimage_cdf_Iic m hq0 hq1]
        _ ≤ ε := by simp [q, max_def]; split_ifs <;> linarith
  exact (ENNReal.toReal_eq_zero_iff (m (F ⁻¹' {c}))).mp hreal
    |>.resolve_right (measure_ne_top m _)

def cdfDuplicateValues (m : Measure ℝ) : Set ℝ :=
  {c | ∃ x y : ℝ, x < y ∧ ProbabilityTheory.cdf m x = c ∧
    ProbabilityTheory.cdf m y = c}

theorem countable_cdfDuplicateValues (m : Measure ℝ) :
    (cdfDuplicateValues m).Countable := by
  simpa [cdfDuplicateValues] using
    (ProbabilityTheory.monotone_cdf (μ := m)).countable_setOf_two_preimages

def cdfGood (m : Measure ℝ) : Set ℝ :=
  (ProbabilityTheory.cdf m ⁻¹' cdfDuplicateValues m)ᶜ

theorem measurableSet_cdfGood (m : Measure ℝ) [IsProbabilityMeasure m]
    [NoAtoms m] : MeasurableSet (cdfGood m) :=
  ((continuous_cdf_of_noAtoms m).measurable
    (countable_cdfDuplicateValues m).measurableSet).compl

theorem measure_cdfGood_compl (m : Measure ℝ) [IsProbabilityMeasure m]
    [NoAtoms m] : m (cdfGood m)ᶜ = 0 := by
  have hset : (cdfGood m)ᶜ =
      ⋃ c ∈ cdfDuplicateValues m, ProbabilityTheory.cdf m ⁻¹' {c} := by
    ext x
    simp [cdfGood]
  rw [hset]
  exact (measure_biUnion_null_iff (countable_cdfDuplicateValues m)).mpr
    (fun c _ ↦ measure_preimage_cdf_singleton m c)

theorem injOn_cdfToUnitInterval_cdfGood (m : Measure ℝ) :
    Set.InjOn (cdfToUnitInterval m) (cdfGood m) := by
  intro x hx y hy hxy
  have hFxy : ProbabilityTheory.cdf m x = ProbabilityTheory.cdf m y :=
    congrArg Subtype.val hxy
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hdup : ProbabilityTheory.cdf m x ∈ cdfDuplicateValues m :=
      ⟨x, y, hlt, rfl, hFxy.symm⟩
    have hx' : ProbabilityTheory.cdf m x ∉ cdfDuplicateValues m := by
      simpa [cdfGood] using hx
    exact hx' hdup
  · have hdup : ProbabilityTheory.cdf m y ∈ cdfDuplicateValues m :=
      ⟨y, x, hlt, rfl, hFxy⟩
    have hy' : ProbabilityTheory.cdf m y ∉ cdfDuplicateValues m := by
      simpa [cdfGood] using hy
    exact hy' hdup

noncomputable def uniformCoordinate [StandardBorelSpace X]
    (m : Measure X) (x : X) : Set.Icc (0 : ℝ) 1 :=
  cdfToUnitInterval (m.map (embeddingReal X)) (embeddingReal X x)

theorem measurable_uniformCoordinate [StandardBorelSpace X]
    (m : Measure X) [IsProbabilityMeasure m] [NoAtoms m] :
    Measurable (uniformCoordinate m) := by
  let e := embeddingReal X
  let ν := m.map e
  letI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (measurable_embeddingReal X).aemeasurable
  letI : NoAtoms ν := noAtoms_map_of_injective m
    (measurable_embeddingReal X) (measurableEmbedding_embeddingReal X).injective
  exact (measurable_cdfToUnitInterval ν).comp (measurable_embeddingReal X)

theorem map_uniformCoordinate [StandardBorelSpace X]
    (m : Measure X) [IsProbabilityMeasure m] [NoAtoms m] :
    m.map (uniformCoordinate m) = volume := by
  let e := embeddingReal X
  let ν := m.map e
  letI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (measurable_embeddingReal X).aemeasurable
  letI : NoAtoms ν := noAtoms_map_of_injective m
    (measurable_embeddingReal X) (measurableEmbedding_embeddingReal X).injective
  change m.map (cdfToUnitInterval ν ∘ e) = volume
  rw [← Measure.map_map (measurable_cdfToUnitInterval ν)
    (measurable_embeddingReal X)]
  exact map_cdfToUnitInterval ν

noncomputable def uniformGood [StandardBorelSpace X] (m : Measure X) : Set X :=
  embeddingReal X ⁻¹' cdfGood (m.map (embeddingReal X))

theorem measurableSet_uniformGood [StandardBorelSpace X]
    (m : Measure X) [IsProbabilityMeasure m] [NoAtoms m] :
    MeasurableSet (uniformGood m) := by
  let e := embeddingReal X
  let ν := m.map e
  letI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (measurable_embeddingReal X).aemeasurable
  letI : NoAtoms ν := noAtoms_map_of_injective m
    (measurable_embeddingReal X) (measurableEmbedding_embeddingReal X).injective
  exact (measurable_embeddingReal X) (measurableSet_cdfGood ν)

theorem measure_uniformGood_compl [StandardBorelSpace X]
    (m : Measure X) [IsProbabilityMeasure m] [NoAtoms m] :
    m (uniformGood m)ᶜ = 0 := by
  let e := embeddingReal X
  let ν := m.map e
  letI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (measurable_embeddingReal X).aemeasurable
  letI : NoAtoms ν := noAtoms_map_of_injective m
    (measurable_embeddingReal X) (measurableEmbedding_embeddingReal X).injective
  change m (e ⁻¹' cdfGood ν)ᶜ = 0
  rw [← Set.preimage_compl]
  rw [← Measure.map_apply (measurable_embeddingReal X)
    (measurableSet_cdfGood ν).compl]
  exact measure_cdfGood_compl ν

theorem injOn_uniformCoordinate_uniformGood [StandardBorelSpace X]
    (m : Measure X) : Set.InjOn (uniformCoordinate m) (uniformGood m) := by
  intro x hx y hy hxy
  apply (measurableEmbedding_embeddingReal X).injective
  apply injOn_cdfToUnitInterval_cdfGood (m.map (embeddingReal X)) hx hy
  exact hxy

theorem measure_image_uniformCoordinate [StandardBorelSpace X]
    (m : Measure X) [IsProbabilityMeasure m] [NoAtoms m]
    {s : Set X} (hs : MeasurableSet s) (hsgood : s ⊆ uniformGood m) :
    volume (uniformCoordinate m '' s) = m s := by
  have himage : MeasurableSet (uniformCoordinate m '' s) :=
    hs.image_of_measurable_injOn (measurable_uniformCoordinate m)
      ((injOn_uniformCoordinate_uniformGood m).mono hsgood)
  rw [← map_uniformCoordinate m]
  rw [Measure.map_apply (measurable_uniformCoordinate m) himage]
  apply measure_congr
  have hae : ∀ᵐ x ∂m, x ∈ uniformGood m :=
    ae_iff.mpr (measure_uniformGood_compl m)
  filter_upwards [hae] with x hxgood
  apply propext
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hygood := hsgood hy
    have : y = x :=
      injOn_uniformCoordinate_uniformGood m hygood hxgood hxy
    subst y
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

noncomputable def uniformRange [StandardBorelSpace X] (m : Measure X) :
    Set (Set.Icc (0 : ℝ) 1) :=
  uniformCoordinate m '' uniformGood m

theorem measurableSet_uniformRange [StandardBorelSpace X]
    (m : Measure X) [IsProbabilityMeasure m] [NoAtoms m] :
    MeasurableSet (uniformRange m) :=
  (measurableSet_uniformGood m).image_of_measurable_injOn
    (measurable_uniformCoordinate m) (injOn_uniformCoordinate_uniformGood m)

theorem volume_uniformRange_compl [StandardBorelSpace X]
    (m : Measure X) [IsProbabilityMeasure m] [NoAtoms m] :
    volume (uniformRange m)ᶜ = 0 := by
  let u := uniformCoordinate m
  let R := uniformRange m
  have hR : MeasurableSet R := measurableSet_uniformRange m
  have hpre : u ⁻¹' Rᶜ ⊆ (uniformGood m)ᶜ := by
    intro x hx hxgood
    exact hx ⟨x, hxgood, rfl⟩
  rw [← map_uniformCoordinate m]
  rw [Measure.map_apply (measurable_uniformCoordinate m) hR.compl]
  exact measure_mono_null hpre (measure_uniformGood_compl m)

noncomputable def uniformSource [StandardBorelSpace X]
    (m : Measure X) (R : Set (Set.Icc (0 : ℝ) 1)) : Set X :=
  uniformGood m ∩ uniformCoordinate m ⁻¹' R

theorem measurableSet_uniformSource [StandardBorelSpace X]
    (m : Measure X) [IsProbabilityMeasure m] [NoAtoms m]
    {R : Set (Set.Icc (0 : ℝ) 1)} (hR : MeasurableSet R) :
    MeasurableSet (uniformSource m R) :=
  (measurableSet_uniformGood m).inter ((measurable_uniformCoordinate m) hR)

theorem measure_uniformSource_compl [StandardBorelSpace X]
    (m : Measure X) [IsProbabilityMeasure m] [NoAtoms m]
    {R : Set (Set.Icc (0 : ℝ) 1)} (hR : MeasurableSet R)
    (hRfull : volume Rᶜ = 0) :
    m (uniformSource m R)ᶜ = 0 := by
  have hpre : m (uniformCoordinate m ⁻¹' Rᶜ) = 0 := by
    rw [← Measure.map_apply (measurable_uniformCoordinate m) hR.compl,
      map_uniformCoordinate m]
    exact hRfull
  have hset : (uniformSource m R)ᶜ =
      (uniformGood m)ᶜ ∪ uniformCoordinate m ⁻¹' Rᶜ := by
    ext x
    change ¬(x ∈ uniformGood m ∧ uniformCoordinate m x ∈ R) ↔
      x ∉ uniformGood m ∨ uniformCoordinate m x ∉ R
    tauto
  rw [hset, measure_union_null_iff]
  exact ⟨measure_uniformGood_compl m, hpre⟩

noncomputable def uniformSourceEquiv [StandardBorelSpace X]
    (m : Measure X) [IsProbabilityMeasure m] [NoAtoms m]
    (R : Set (Set.Icc (0 : ℝ) 1)) (hR : MeasurableSet R)
    (hRsub : R ⊆ uniformRange m) : uniformSource m R ≃ᵐ R := by
  let D := uniformSource m R
  let u := uniformCoordinate m
  let f : D → Set.Icc (0 : ℝ) 1 := fun x ↦ u x
  have hD : MeasurableSet D := measurableSet_uniformSource m hR
  letI : StandardBorelSpace D := hD.standardBorel
  have hf : Measurable f := (measurable_uniformCoordinate m).comp measurable_subtype_coe
  have hfinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact injOn_uniformCoordinate_uniformGood m x.property.1 y.property.1 hxy
  have hfrange : Set.range f = R := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact x.property.2
    · intro hz
      obtain ⟨x, hxgood, hux⟩ := hRsub hz
      refine ⟨⟨x, hxgood, ?_⟩, ?_⟩
      · change u x ∈ R
        change uniformCoordinate m x ∈ R
        rwa [hux]
      · dsimp [f, u]
        exact hux
  have hfemb : MeasurableEmbedding f := hf.measurableEmbedding hfinj
  let ec : Set.range f ≃ᵐ R :=
    { toEquiv := Equiv.setCongr hfrange
      measurable_toFun := measurable_subtype_coe.subtype_mk
      measurable_invFun := measurable_subtype_coe.subtype_mk }
  exact hfemb.equivRange.trans ec

@[simp]
theorem coe_uniformSourceEquiv [StandardBorelSpace X]
    (m : Measure X) [IsProbabilityMeasure m] [NoAtoms m]
    (R : Set (Set.Icc (0 : ℝ) 1)) (hR : MeasurableSet R)
    (hRsub : R ⊆ uniformRange m) (x : uniformSource m R) :
    ((uniformSourceEquiv m R hR hRsub x : R) : Set.Icc (0 : ℝ) 1) =
      uniformCoordinate m x := by
  simp [uniformSourceEquiv]

theorem uniformCoordinate_uniformSourceEquiv_symm [StandardBorelSpace X]
    (m : Measure X) [IsProbabilityMeasure m] [NoAtoms m]
    (R : Set (Set.Icc (0 : ℝ) 1)) (hR : MeasurableSet R)
    (hRsub : R ⊆ uniformRange m) (z : R) :
    uniformCoordinate m ((uniformSourceEquiv m R hR hRsub).symm z) = z := by
  have h := coe_uniformSourceEquiv m R hR hRsub
    ((uniformSourceEquiv m R hR hRsub).symm z)
  simpa only [MeasurableEquiv.apply_symm_apply] using h.symm

noncomputable def uniformBridge {Y : Type*} [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    (m : Measure X) (n : Measure Y)
    [IsProbabilityMeasure m] [NoAtoms m]
    [IsProbabilityMeasure n] [NoAtoms n]
    (R : Set (Set.Icc (0 : ℝ) 1)) (hR : MeasurableSet R)
    (hRm : R ⊆ uniformRange m) (hRn : R ⊆ uniformRange n) :
    uniformSource m R ≃ᵐ uniformSource n R :=
  (uniformSourceEquiv m R hR hRm).trans
    (uniformSourceEquiv n R hR hRn).symm

@[simp]
theorem uniformCoordinate_uniformBridge {Y : Type*} [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    (m : Measure X) (n : Measure Y)
    [IsProbabilityMeasure m] [NoAtoms m]
    [IsProbabilityMeasure n] [NoAtoms n]
    (R : Set (Set.Icc (0 : ℝ) 1)) (hR : MeasurableSet R)
    (hRm : R ⊆ uniformRange m) (hRn : R ⊆ uniformRange n)
    (x : uniformSource m R) :
    uniformCoordinate n (uniformBridge m n R hR hRm hRn x) =
      uniformCoordinate m x := by
  change uniformCoordinate n
      ((uniformSourceEquiv n R hR hRn).symm
        (uniformSourceEquiv m R hR hRm x)) = uniformCoordinate m x
  rw [uniformCoordinate_uniformSourceEquiv_symm]
  exact coe_uniformSourceEquiv m R hR hRm x

theorem measurePreserving_uniformBridge {Y : Type*} [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    (m : Measure X) (n : Measure Y)
    [IsProbabilityMeasure m] [NoAtoms m]
    [IsProbabilityMeasure n] [NoAtoms n]
    (R : Set (Set.Icc (0 : ℝ) 1)) (hR : MeasurableSet R)
    (hRm : R ⊆ uniformRange m) (hRn : R ⊆ uniformRange n) :
    MeasurePreserving (uniformBridge m n R hR hRm hRn)
      (Measure.comap ((↑) : uniformSource m R → X) m)
      (Measure.comap ((↑) : uniformSource n R → Y) n) := by
  have hDX : MeasurableSet (uniformSource m R) :=
    measurableSet_uniformSource m hR
  have hDY : MeasurableSet (uniformSource n R) :=
    measurableSet_uniformSource n hR
  letI : StandardBorelSpace (uniformSource m R) := hDX.standardBorel
  letI : StandardBorelSpace (uniformSource n R) := hDY.standardBorel
  let e := uniformBridge m n R hR hRm hRn
  refine ⟨e.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply e.measurable hs,
    comap_subtype_coe_apply hDX m,
    comap_subtype_coe_apply hDY n]
  let sx : Set X := ((↑) : uniformSource m R → X) '' (e ⁻¹' s)
  let sy : Set Y := ((↑) : uniformSource n R → Y) '' s
  have hsx : MeasurableSet sx :=
    (e.measurable hs).image_of_measurable_injOn measurable_subtype_coe
      (fun _ _ _ _ h ↦ Subtype.ext h)
  have hsy : MeasurableSet sy :=
    hs.image_of_measurable_injOn measurable_subtype_coe
      (fun _ _ _ _ h ↦ Subtype.ext h)
  have hsxgood : sx ⊆ uniformGood m := by
    rintro _ ⟨x, -, rfl⟩
    exact x.property.1
  have hsygood : sy ⊆ uniformGood n := by
    rintro _ ⟨y, -, rfl⟩
    exact y.property.1
  have himage : uniformCoordinate m '' sx = uniformCoordinate n '' sy := by
    ext r
    constructor
    · rintro ⟨_, ⟨x, hxs, rfl⟩, rfl⟩
      refine ⟨(e x : Y), ⟨e x, hxs, rfl⟩, ?_⟩
      exact uniformCoordinate_uniformBridge m n R hR hRm hRn x
    · rintro ⟨_, ⟨y, hys, rfl⟩, rfl⟩
      let x := e.symm y
      refine ⟨(x : X), ⟨x, ?_, rfl⟩, ?_⟩
      · change e x ∈ s
        simpa [x] using hys
      · calc
          uniformCoordinate m x = uniformCoordinate n (e x) :=
            (uniformCoordinate_uniformBridge m n R hR hRm hRn x).symm
          _ = uniformCoordinate n y := by simp [x]
  change m sx = n sy
  calc
    m sx = volume (uniformCoordinate m '' sx) :=
      (measure_image_uniformCoordinate m hsx hsxgood).symm
    _ = volume (uniformCoordinate n '' sy) := congrArg volume himage
    _ = n sy := measure_image_uniformCoordinate n hsy hsygood

noncomputable def commonUniformRange {Y : Type*} [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    (m : Measure X) (n : Measure Y) : Set (Set.Icc (0 : ℝ) 1) :=
  uniformRange m ∩ uniformRange n

theorem measurableSet_commonUniformRange {Y : Type*} [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    (m : Measure X) (n : Measure Y)
    [IsProbabilityMeasure m] [NoAtoms m]
    [IsProbabilityMeasure n] [NoAtoms n] :
    MeasurableSet (commonUniformRange m n) :=
  (measurableSet_uniformRange m).inter (measurableSet_uniformRange n)

theorem volume_commonUniformRange_compl {Y : Type*} [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    (m : Measure X) (n : Measure Y)
    [IsProbabilityMeasure m] [NoAtoms m]
    [IsProbabilityMeasure n] [NoAtoms n] :
    volume (commonUniformRange m n)ᶜ = 0 := by
  have hset : (commonUniformRange m n)ᶜ =
      (uniformRange m)ᶜ ∪ (uniformRange n)ᶜ := by
    ext z
    change ¬(z ∈ uniformRange m ∧ z ∈ uniformRange n) ↔
      z ∉ uniformRange m ∨ z ∉ uniformRange n
    tauto
  rw [hset, measure_union_null_iff]
  exact ⟨volume_uniformRange_compl m, volume_uniformRange_compl n⟩

noncomputable def commonUniformEquiv {Y : Type*} [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    (m : Measure X) (n : Measure Y)
    [IsProbabilityMeasure m] [NoAtoms m]
    [IsProbabilityMeasure n] [NoAtoms n] :
    uniformSource m (commonUniformRange m n) ≃ᵐ
      uniformSource n (commonUniformRange m n) :=
  (uniformSourceEquiv m (commonUniformRange m n)
      (measurableSet_commonUniformRange m n) Set.inter_subset_left).trans
    (uniformSourceEquiv n (commonUniformRange m n)
      (measurableSet_commonUniformRange m n) Set.inter_subset_right).symm

@[simp]
theorem uniformCoordinate_commonUniformEquiv {Y : Type*} [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    (m : Measure X) (n : Measure Y)
    [IsProbabilityMeasure m] [NoAtoms m]
    [IsProbabilityMeasure n] [NoAtoms n]
    (x : uniformSource m (commonUniformRange m n)) :
    uniformCoordinate n (commonUniformEquiv m n x) = uniformCoordinate m x := by
  let R := commonUniformRange m n
  let em := uniformSourceEquiv m R
    (measurableSet_commonUniformRange m n) Set.inter_subset_left
  let en := uniformSourceEquiv n R
    (measurableSet_commonUniformRange m n) Set.inter_subset_right
  change uniformCoordinate n (en.symm (em x)) = uniformCoordinate m x
  rw [uniformCoordinate_uniformSourceEquiv_symm]
  exact coe_uniformSourceEquiv m R
    (measurableSet_commonUniformRange m n) Set.inter_subset_left x

theorem measurePreserving_commonUniformEquiv {Y : Type*} [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    (m : Measure X) (n : Measure Y)
    [IsProbabilityMeasure m] [NoAtoms m]
    [IsProbabilityMeasure n] [NoAtoms n] :
    MeasurePreserving (commonUniformEquiv m n)
      (Measure.comap
        ((↑) : uniformSource m (commonUniformRange m n) → X) m)
      (Measure.comap
        ((↑) : uniformSource n (commonUniformRange m n) → Y) n) := by
  let R := commonUniformRange m n
  have hR : MeasurableSet R := measurableSet_commonUniformRange m n
  have hDX : MeasurableSet (uniformSource m R) :=
    measurableSet_uniformSource m hR
  have hDY : MeasurableSet (uniformSource n R) :=
    measurableSet_uniformSource n hR
  letI : StandardBorelSpace (uniformSource m R) := hDX.standardBorel
  letI : StandardBorelSpace (uniformSource n R) := hDY.standardBorel
  let e := commonUniformEquiv m n
  refine ⟨e.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply e.measurable hs,
    comap_subtype_coe_apply hDX m,
    comap_subtype_coe_apply hDY n]
  let sx : Set X := ((↑) : uniformSource m R → X) '' (e ⁻¹' s)
  let sy : Set Y := ((↑) : uniformSource n R → Y) '' s
  have hsx : MeasurableSet sx :=
    (e.measurable hs).image_of_measurable_injOn measurable_subtype_coe
      (fun _ _ _ _ h ↦ Subtype.ext h)
  have hsy : MeasurableSet sy :=
    hs.image_of_measurable_injOn measurable_subtype_coe
      (fun _ _ _ _ h ↦ Subtype.ext h)
  have hsxgood : sx ⊆ uniformGood m := by
    rintro _ ⟨x, -, rfl⟩
    exact x.property.1
  have hsygood : sy ⊆ uniformGood n := by
    rintro _ ⟨y, -, rfl⟩
    exact y.property.1
  have himage : uniformCoordinate m '' sx = uniformCoordinate n '' sy := by
    ext r
    constructor
    · rintro ⟨_, ⟨x, hxs, rfl⟩, rfl⟩
      refine ⟨(e x : Y), ⟨e x, hxs, rfl⟩, ?_⟩
      exact uniformCoordinate_commonUniformEquiv m n x
    · rintro ⟨_, ⟨y, hys, rfl⟩, rfl⟩
      let x := e.symm y
      refine ⟨(x : X), ⟨x, ?_, rfl⟩, ?_⟩
      · change e x ∈ s
        simpa [x] using hys
      · calc
          uniformCoordinate m x = uniformCoordinate n (e x) :=
            (uniformCoordinate_commonUniformEquiv m n x).symm
          _ = uniformCoordinate n y := by simp [x]
  change m sx = n sy
  calc
    m sx = volume (uniformCoordinate m '' sx) :=
      (measure_image_uniformCoordinate m hsx hsxgood).symm
    _ = volume (uniformCoordinate n '' sy) := congrArg volume himage
    _ = n sy := measure_image_uniformCoordinate n hsy hsygood

end Submission.Helpers
