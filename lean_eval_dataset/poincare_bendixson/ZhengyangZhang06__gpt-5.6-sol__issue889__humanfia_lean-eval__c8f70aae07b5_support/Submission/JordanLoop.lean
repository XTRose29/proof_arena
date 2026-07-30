import Submission.JordanCurve
import ChallengeDeps

open Function Set Topology

namespace Submission.JordanLoop

noncomputable section

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- Regard a based path as a map from the additive circle by identifying its
two endpoints. -/
def onAddCircle (γ : Path x x) : UnitAddCircle → X :=
  AddCircle.liftIco 1 0 γ.extend

theorem onAddCircle_coe (γ : Path x x) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    onAddCircle γ (t : UnitAddCircle) = γ.extend t := by
  exact AddCircle.liftIco_zero_coe_apply ht

theorem continuous_onAddCircle (γ : Path x x) :
    Continuous (onAddCircle γ) := by
  apply AddCircle.liftIco_zero_continuous
  · simp only [Path.extend_zero, Path.extend_one]
  · exact γ.continuous_extend.continuousOn

theorem injective_onAddCircle (γ : Path x x)
    (hγ : InjOn γ.extend (Ico (0 : ℝ) 1)) :
    Injective (onAddCircle γ) := by
  intro z w hzw
  let a := AddCircle.equivIco 1 0 z
  let b := AddCircle.equivIco 1 0 w
  have ha : (a : ℝ) ∈ Ico (0 : ℝ) 1 := by
    simpa only [zero_add] using a.2
  have hb : (b : ℝ) ∈ Ico (0 : ℝ) 1 := by
    simpa only [zero_add] using b.2
  have haz : ((a : ℝ) : UnitAddCircle) = z := by
    exact AddCircle.coe_equivIco
  have hbw : ((b : ℝ) : UnitAddCircle) = w := by
    exact AddCircle.coe_equivIco
  have hab : γ.extend (a : ℝ) = γ.extend (b : ℝ) := by
    rw [← onAddCircle_coe γ ha, ← onAddCircle_coe γ hb,
      haz, hbw]
    exact hzw
  have hab' : (a : ℝ) = (b : ℝ) :=
    hγ ha hb hab
  calc
    z = ((a : ℝ) : UnitAddCircle) := haz.symm
    _ = ((b : ℝ) : UnitAddCircle) := by rw [hab']
    _ = w := hbw

/-- The same loop with the standard unit circle as parameter space. -/
def onCircle (γ : Path x x) : Circle → X :=
  onAddCircle γ ∘ (AddCircle.homeomorphCircle one_ne_zero).symm

theorem continuous_onCircle (γ : Path x x) :
    Continuous (onCircle γ) :=
  (continuous_onAddCircle γ).comp
    (AddCircle.homeomorphCircle one_ne_zero).symm.continuous

theorem injective_onCircle (γ : Path x x)
    (hγ : InjOn γ.extend (Ico (0 : ℝ) 1)) :
    Injective (onCircle γ) :=
  (injective_onAddCircle γ hγ).comp
    (AddCircle.homeomorphCircle one_ne_zero).symm.injective

theorem range_onCircle (γ : Path x x) :
    range (onCircle γ) = range (onAddCircle γ) := by
  exact
    (AddCircle.homeomorphCircle one_ne_zero).symm.surjective.range_comp
      (onAddCircle γ)

theorem range_onAddCircle (γ : Path x x) :
    range (onAddCircle γ) = range γ := by
  apply Subset.antisymm
  · rintro y ⟨z, rfl⟩
    let t := AddCircle.equivIco 1 0 z
    have ht : (t : ℝ) ∈ Ico (0 : ℝ) 1 := by
      simpa only [zero_add] using t.2
    have htz : ((t : ℝ) : UnitAddCircle) = z :=
      AddCircle.coe_equivIco
    refine ⟨⟨t, ⟨ht.1, ht.2.le⟩⟩, ?_⟩
    rw [← Path.extend_extends' γ]
    rw [← onAddCircle_coe γ ht, htz]
  · rintro y ⟨t, rfl⟩
    by_cases ht : (t : ℝ) < 1
    · refine ⟨((t : ℝ) : UnitAddCircle), ?_⟩
      rw [onAddCircle_coe γ ⟨t.2.1, ht⟩,
        Path.extend_extends' γ t]
    · have ht1 : t = (1 : unitInterval) := by
        apply Subtype.ext
        exact le_antisymm t.2.2 (not_lt.mp ht)
      subst t
      refine ⟨(0 : UnitAddCircle), ?_⟩
      rw [← show ((0 : ℝ) : UnitAddCircle) = 0 by rfl,
        onAddCircle_coe γ (by norm_num : (0 : ℝ) ∈ Ico 0 1)]
      simp only [Path.extend_zero, Path.target]

theorem range_onCircle_eq_path (γ : Path x x) :
    range (onCircle γ) = range γ := by
  rw [range_onCircle, range_onAddCircle]

theorem injOn_extend_Icc {a b : X} (γ : Path a b)
    (hγ : Injective γ) :
    InjOn γ.extend (Icc (0 : ℝ) 1) := by
  intro s hs t ht hst
  have hst' :
      γ (⟨s, hs⟩ : unitInterval) =
        γ (⟨t, ht⟩ : unitInterval) := by
    simpa only [Path.extend_apply γ hs, Path.extend_apply γ ht] using hst
  exact congrArg Subtype.val (hγ hst')

/-- Two simple arcs with only their endpoints in common concatenate to a
simple loop (with the usual identification of parameter endpoints). -/
theorem injOn_extend_Ico_trans {a b : X}
    (γ₁ : Path a b) (γ₂ : Path b a)
    (hγ₁ : Injective γ₁) (hγ₂ : Injective γ₂)
    (hinter : range γ₁ ∩ range γ₂ ⊆ {a, b}) :
    InjOn (γ₁.trans γ₂).extend (Ico (0 : ℝ) 1) := by
  have hγ₁' := injOn_extend_Icc γ₁ hγ₁
  have hγ₂' := injOn_extend_Icc γ₂ hγ₂
  intro s hs t ht hst
  by_cases hsHalf : s ≤ 1 / 2
  · by_cases htHalf : t ≤ 1 / 2
    · rw [Path.extend_trans_of_le_half γ₁ γ₂ hsHalf,
        Path.extend_trans_of_le_half γ₁ γ₂ htHalf] at hst
      have hs' : 2 * s ∈ Icc (0 : ℝ) 1 := by
        constructor <;> linarith [hs.1]
      have ht' : 2 * t ∈ Icc (0 : ℝ) 1 := by
        constructor <;> linarith [ht.1]
      have := hγ₁' hs' ht' hst
      linarith
    · have htHalf' : 1 / 2 ≤ t := (not_le.mp htHalf).le
      rw [Path.extend_trans_of_le_half γ₁ γ₂ hsHalf,
        Path.extend_trans_of_half_le γ₁ γ₂ htHalf'] at hst
      have hs' : 2 * s ∈ Icc (0 : ℝ) 1 := by
        constructor <;> linarith [hs.1]
      have ht' : 2 * t - 1 ∈ Icc (0 : ℝ) 1 := by
        constructor <;> linarith [ht.2, not_le.mp htHalf]
      have hmem :
          γ₁.extend (2 * s) ∈ range γ₁ ∩ range γ₂ := by
        constructor
        · rw [← Path.extend_range γ₁]
          exact mem_range_self (2 * s)
        · rw [← Path.extend_range γ₂]
          exact ⟨2 * t - 1, hst.symm⟩
      have hend := hinter hmem
      simp only [mem_insert_iff, mem_singleton_iff] at hend
      rcases hend with ha | hb
      · have hs0 : 2 * s = 0 :=
          hγ₁' hs' ⟨by norm_num, by norm_num⟩
            (by simpa only [Path.extend_zero] using ha)
        have ht1 : 2 * t - 1 = 1 :=
          hγ₂' ht' ⟨by norm_num, by norm_num⟩
            (by simpa only [Path.extend_one] using hst ▸ ha)
        exfalso
        linarith [ht.2]
      · have hs1 : 2 * s = 1 :=
          hγ₁' hs' ⟨by norm_num, by norm_num⟩
            (by simpa only [Path.extend_one] using hb)
        have ht0 : 2 * t - 1 = 0 :=
          hγ₂' ht' ⟨by norm_num, by norm_num⟩
            (by simpa only [Path.extend_zero] using hst ▸ hb)
        linarith [not_le.mp htHalf]
  · have hsHalf' : 1 / 2 ≤ s := (not_le.mp hsHalf).le
    by_cases htHalf : t ≤ 1 / 2
    · rw [Path.extend_trans_of_half_le γ₁ γ₂ hsHalf',
        Path.extend_trans_of_le_half γ₁ γ₂ htHalf] at hst
      have hs' : 2 * s - 1 ∈ Icc (0 : ℝ) 1 := by
        constructor <;> linarith [hs.2, not_le.mp hsHalf]
      have ht' : 2 * t ∈ Icc (0 : ℝ) 1 := by
        constructor <;> linarith [ht.1]
      have hmem :
          γ₁.extend (2 * t) ∈ range γ₁ ∩ range γ₂ := by
        constructor
        · rw [← Path.extend_range γ₁]
          exact mem_range_self (2 * t)
        · rw [← Path.extend_range γ₂]
          exact ⟨2 * s - 1, hst⟩
      have hend := hinter hmem
      simp only [mem_insert_iff, mem_singleton_iff] at hend
      rcases hend with ha | hb
      · have ht0 : 2 * t = 0 :=
          hγ₁' ht' ⟨by norm_num, by norm_num⟩
            (by simpa only [Path.extend_zero] using ha)
        have hs1 : 2 * s - 1 = 1 :=
          hγ₂' hs' ⟨by norm_num, by norm_num⟩
            (by simpa only [Path.extend_one] using hst.symm ▸ ha)
        exfalso
        linarith [hs.2]
      · have ht1 : 2 * t = 1 :=
          hγ₁' ht' ⟨by norm_num, by norm_num⟩
            (by simpa only [Path.extend_one] using hb)
        have hs0 : 2 * s - 1 = 0 :=
          hγ₂' hs' ⟨by norm_num, by norm_num⟩
            (by simpa only [Path.extend_zero] using hst.symm ▸ hb)
        linarith [not_le.mp hsHalf]
    · have htHalf' : 1 / 2 ≤ t := (not_le.mp htHalf).le
      rw [Path.extend_trans_of_half_le γ₁ γ₂ hsHalf',
        Path.extend_trans_of_half_le γ₁ γ₂ htHalf'] at hst
      have hs' : 2 * s - 1 ∈ Icc (0 : ℝ) 1 := by
        constructor <;> linarith [hs.2, not_le.mp hsHalf]
      have ht' : 2 * t - 1 ∈ Icc (0 : ℝ) 1 := by
        constructor <;> linarith [ht.2, not_le.mp htHalf]
      have := hγ₂' hs' ht' hst
      linarith

theorem two_components_compl_trans
    {a b : LeanEval.Dynamics.Plane}
    (γ₁ : Path a b) (γ₂ : Path b a)
    (hγ₁ : Injective γ₁) (hγ₂ : Injective γ₂)
    (hinter : range γ₁ ∩ range γ₂ ⊆ {a, b}) :
    Nat.card
        (ConnectedComponents
          ((range γ₁ ∪ range γ₂)ᶜ : Set LeanEval.Dynamics.Plane)) =
      2 := by
  let γ := γ₁.trans γ₂
  have hcurve :
      Injective (onCircle γ) :=
    injective_onCircle γ
      (injOn_extend_Ico_trans γ₁ γ₂ hγ₁ hγ₂ hinter)
  let r :
      Metric.sphere (0 : LeanEval.Dynamics.Plane) 1 →
        LeanEval.Dynamics.Plane :=
    onCircle γ ∘ Transport.sphereEquiv
  have hrange : range r = range (onCircle γ) :=
    Transport.sphereEquiv.surjective.range_comp (onCircle γ)
  have hjordan :=
    JordanCurve.jordan_curve r
      ((continuous_onCircle γ).comp Transport.sphereEquiv.continuous)
      (hcurve.comp Transport.sphereEquiv.injective)
  rw [hrange, range_onCircle_eq_path, Path.trans_range] at hjordan
  exact hjordan

end

end Submission.JordanLoop
