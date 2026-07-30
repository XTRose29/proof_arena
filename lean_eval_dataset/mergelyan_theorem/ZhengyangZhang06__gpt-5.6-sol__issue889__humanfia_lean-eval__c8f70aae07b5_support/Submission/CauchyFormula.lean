import Submission.CauchyPompeiu

open Function Set
open scoped Interval Topology

noncomputable section

namespace Submission.Helpers

theorem measurableSet_reProdIm {s t : Set ℝ}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    MeasurableSet (s ×ℂ t) := by
  rw [Complex.reProdIm]
  exact (hs.preimage Complex.measurable_re).inter
    (ht.preimage Complex.measurable_im)

/-- The Cauchy--Riemann defect of a smooth function is supported inside the
topological support of the function itself. -/
theorem tsupport_crDefect_subset (g : ℂ → ℂ) :
    tsupport (crDefect g) ⊆ tsupport g := by
  rw [tsupport]
  refine closure_minimal ?_ (isClosed_tsupport g)
  intro z hz
  by_contra hzt
  have hD : fderiv ℝ g z = 0 := fderiv_of_notMem_tsupport ℝ hzt
  exact hz (by simp [crDefect, hD])

/-- A rectangular boundary integral vanishes when the integrand vanishes on
each of its four sides. -/
theorem rectBoundaryIntegral_eq_zero_of_boundary (F : ℂ → ℂ) (a b : ℂ)
    (hbottom : ∀ x ∈ [[a.re, b.re]], F (x + a.im * Complex.I) = 0)
    (htop : ∀ x ∈ [[a.re, b.re]], F (x + b.im * Complex.I) = 0)
    (hright : ∀ y ∈ [[a.im, b.im]], F (b.re + y * Complex.I) = 0)
    (hleft : ∀ y ∈ [[a.im, b.im]], F (a.re + y * Complex.I) = 0) :
    rectBoundaryIntegral F a b = 0 := by
  have hb :
      (∫ x : ℝ in a.re..b.re, F (x + a.im * Complex.I)) = 0 := by
    calc
      _ = ∫ _x : ℝ in a.re..b.re, (0 : ℂ) :=
        intervalIntegral.integral_congr hbottom
      _ = 0 := by simp
  have ht :
      (∫ x : ℝ in a.re..b.re, F (x + b.im * Complex.I)) = 0 := by
    calc
      _ = ∫ _x : ℝ in a.re..b.re, (0 : ℂ) :=
        intervalIntegral.integral_congr htop
      _ = 0 := by simp
  have hr :
      (∫ y : ℝ in a.im..b.im, F (b.re + y * Complex.I)) = 0 := by
    calc
      _ = ∫ _y : ℝ in a.im..b.im, (0 : ℂ) :=
        intervalIntegral.integral_congr hright
      _ = 0 := by simp
  have hl :
      (∫ y : ℝ in a.im..b.im, F (a.re + y * Complex.I)) = 0 := by
    calc
      _ = ∫ _y : ℝ in a.im..b.im, (0 : ℂ) :=
        intervalIntegral.integral_congr hleft
      _ = 0 := by simp
  simp [rectBoundaryIntegral, hb, ht, hr, hl]

/-- If the support of `g` lies strictly inside a square, then the
Cauchy-kernel-times-`g` integral on the boundary of that square vanishes. -/
theorem rectBoundaryIntegral_cauchyKernel_mul_eq_zero_of_tsupport_subset_ball
    (g : ℂ → ℂ) (z : ℂ) (R : ℝ) (hR : 0 < R)
    (hgR : tsupport g ⊆ Metric.ball z R) :
    rectBoundaryIntegral (fun w ↦ (w - z)⁻¹ * g w)
      ⟨z.re - R, z.im - R⟩ ⟨z.re + R, z.im + R⟩ = 0 := by
  have hgzero (w : ℂ) (hw : R ≤ dist w z) : g w = 0 := by
    by_contra hwg
    have hwt : w ∈ tsupport g := subset_tsupport g hwg
    have hwb := hgR hwt
    rw [Metric.mem_ball] at hwb
    exact (not_lt_of_ge hw) hwb
  apply rectBoundaryIntegral_eq_zero_of_boundary
  · intro x _hx
    dsimp
    rw [hgzero]
    · simp
    · calc
        R = |(x + ((z.im : ℂ) - (R : ℂ)) * Complex.I - z).im| := by
          simp [abs_of_pos hR]
        _ ≤ ‖x + ((z.im : ℂ) - (R : ℂ)) * Complex.I - z‖ :=
          Complex.abs_im_le_norm _
        _ = dist (x + ((z.im : ℂ) - (R : ℂ)) * Complex.I) z := by
          rw [dist_eq_norm]
        _ ≤ dist (x + ((z.im - R : ℝ) : ℂ) * Complex.I) z := by
          push_cast
          exact le_rfl
  · intro x _hx
    dsimp
    rw [hgzero]
    · simp
    · calc
        R = |(x + ((z.im : ℂ) + (R : ℂ)) * Complex.I - z).im| := by
          simp [abs_of_pos hR]
        _ ≤ ‖x + ((z.im : ℂ) + (R : ℂ)) * Complex.I - z‖ :=
          Complex.abs_im_le_norm _
        _ = dist (x + ((z.im : ℂ) + (R : ℂ)) * Complex.I) z := by
          rw [dist_eq_norm]
        _ ≤ dist (x + ((z.im + R : ℝ) : ℂ) * Complex.I) z := by
          push_cast
          exact le_rfl
  · intro y _hy
    dsimp
    rw [hgzero]
    · simp
    · calc
        R = |((z.re : ℂ) + (R : ℂ) + y * Complex.I - z).re| := by
          simp [abs_of_pos hR]
        _ ≤ ‖(z.re : ℂ) + (R : ℂ) + y * Complex.I - z‖ :=
          Complex.abs_re_le_norm _
        _ = dist ((z.re : ℂ) + (R : ℂ) + y * Complex.I) z := by
          rw [dist_eq_norm]
        _ ≤ dist ((z.re + R : ℝ) + y * Complex.I) z := by
          push_cast
          exact le_rfl
  · intro y _hy
    dsimp
    rw [hgzero]
    · simp
    · calc
        R = |((z.re : ℂ) - (R : ℂ) + y * Complex.I - z).re| := by
          simp [abs_of_pos hR]
        _ ≤ ‖(z.re : ℂ) - (R : ℂ) + y * Complex.I - z‖ :=
          Complex.abs_re_le_norm _
        _ = dist ((z.re : ℂ) - (R : ℂ) + y * Complex.I) z := by
          rw [dist_eq_norm]
        _ ≤ dist ((z.re - R : ℝ) + y * Complex.I) z := by
          push_cast
          exact le_rfl

/-- The four half-open rectangles surrounding an inner rectangle partition
the corresponding rectangular annulus, at the level of iterated integrals. -/
theorem rectIntegral_annulus (F : ℂ → ℂ)
    {x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : ℝ}
    (hx₀₁ : x₀ ≤ x₁) (hx₁₂ : x₁ ≤ x₂) (hx₂₃ : x₂ ≤ x₃)
    (hy₀₁ : y₀ ≤ y₁) (hy₁₂ : y₁ ≤ y₂) (hy₂₃ : y₂ ≤ y₃)
    (hF : MeasureTheory.Integrable F) :
    rectIntegral F ⟨x₀, y₀⟩ ⟨x₃, y₁⟩ +
        rectIntegral F ⟨x₀, y₂⟩ ⟨x₃, y₃⟩ +
        rectIntegral F ⟨x₀, y₁⟩ ⟨x₁, y₂⟩ +
        rectIntegral F ⟨x₂, y₁⟩ ⟨x₃, y₂⟩ =
      rectIntegral F ⟨x₀, y₀⟩ ⟨x₃, y₃⟩ -
        rectIntegral F ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ := by
  let B : Set ℂ := Ioc x₀ x₃ ×ℂ Ioc y₀ y₁
  let T : Set ℂ := Ioc x₀ x₃ ×ℂ Ioc y₂ y₃
  let L : Set ℂ := Ioc x₀ x₁ ×ℂ Ioc y₁ y₂
  let R : Set ℂ := Ioc x₂ x₃ ×ℂ Ioc y₁ y₂
  let O : Set ℂ := Ioc x₀ x₃ ×ℂ Ioc y₀ y₃
  let I : Set ℂ := Ioc x₁ x₂ ×ℂ Ioc y₁ y₂
  have hB : MeasurableSet B :=
    measurableSet_reProdIm measurableSet_Ioc measurableSet_Ioc
  have hT : MeasurableSet T :=
    measurableSet_reProdIm measurableSet_Ioc measurableSet_Ioc
  have hL : MeasurableSet L :=
    measurableSet_reProdIm measurableSet_Ioc measurableSet_Ioc
  have hR : MeasurableSet R :=
    measurableSet_reProdIm measurableSet_Ioc measurableSet_Ioc
  have hO : MeasurableSet O :=
    measurableSet_reProdIm measurableSet_Ioc measurableSet_Ioc
  have hI : MeasurableSet I :=
    measurableSet_reProdIm measurableSet_Ioc measurableSet_Ioc
  have hBT : Disjoint B T := by
    rw [Set.disjoint_left]
    intro z hzB hzT
    exact (not_lt_of_ge hy₁₂) (lt_of_lt_of_le hzT.2.1 hzB.2.2)
  have hBTL : Disjoint (B ∪ T) L := by
    rw [Set.disjoint_left]
    intro z hzBT hzL
    rcases hzBT with hzB | hzT
    · exact (not_lt_of_ge hzB.2.2) hzL.2.1
    · exact (not_lt_of_ge hzL.2.2) hzT.2.1
  have hBTLR : Disjoint (B ∪ T ∪ L) R := by
    rw [Set.disjoint_left]
    intro z hzBTL hzR
    rcases hzBTL with (hzB | hzT) | hzL
    · exact (not_lt_of_ge hzB.2.2) hzR.2.1
    · exact (not_lt_of_ge hzR.2.2) hzT.2.1
    · exact (not_lt_of_ge hx₁₂) (lt_of_lt_of_le hzR.1.1 hzL.1.2)
  have hpartition : B ∪ T ∪ L ∪ R = O \ I := by
    ext z
    simp only [mem_union, mem_sdiff, B, T, L, R, O, I,
      Complex.mem_reProdIm, mem_Ioc]
    grind
  have hIO : I ⊆ O := by
    intro z hz
    exact
      ⟨⟨lt_of_le_of_lt hx₀₁ hz.1.1, hz.1.2.trans hx₂₃⟩,
        ⟨lt_of_le_of_lt hy₀₁ hz.2.1, hz.2.2.trans hy₂₃⟩⟩
  have hx₀₃ : x₀ ≤ x₃ := hx₀₁.trans (hx₁₂.trans hx₂₃)
  have hy₀₃ : y₀ ≤ y₃ := hy₀₁.trans (hy₁₂.trans hy₂₃)
  rw [rectIntegral_eq_setIntegral F hx₀₃ hy₀₁ hF.integrableOn,
    rectIntegral_eq_setIntegral F hx₀₃ hy₂₃ hF.integrableOn,
    rectIntegral_eq_setIntegral F hx₀₁ hy₁₂
      hF.integrableOn,
    rectIntegral_eq_setIntegral F hx₂₃ hy₁₂
      hF.integrableOn,
    rectIntegral_eq_setIntegral F hx₀₃ hy₀₃ hF.integrableOn,
    rectIntegral_eq_setIntegral F hx₁₂ hy₁₂ hF.integrableOn]
  change
    (∫ z in B, F z) + (∫ z in T, F z) +
          (∫ z in L, F z) + (∫ z in R, F z) =
      (∫ z in O, F z) - ∫ z in I, F z
  calc
    _ = ∫ z in B ∪ T ∪ L ∪ R, F z := by
      rw [MeasureTheory.setIntegral_union hBTLR hR hF.integrableOn hF.integrableOn,
        MeasureTheory.setIntegral_union hBTL hL hF.integrableOn hF.integrableOn,
        MeasureTheory.setIntegral_union hBT hT hF.integrableOn hF.integrableOn]
    _ = ∫ z in O \ I, F z := by rw [hpartition]
    _ = _ := MeasureTheory.setIntegral_sdiff hI hF.integrableOn hIO

/-- A nested family of half-open squares shrinking to `z`. -/
def shrinkingSquare (z : ℂ) (n : ℕ) : Set ℂ :=
  Ioc (z.re - 1 / ((n : ℝ) + 1)) (z.re + 1 / ((n : ℝ) + 1)) ×ℂ
    Ioc (z.im - 1 / ((n : ℝ) + 1)) (z.im + 1 / ((n : ℝ) + 1))

theorem measurableSet_shrinkingSquare (z : ℂ) (n : ℕ) :
    MeasurableSet (shrinkingSquare z n) :=
  measurableSet_reProdIm measurableSet_Ioc measurableSet_Ioc

theorem antitone_shrinkingSquare (z : ℂ) :
    Antitone (shrinkingSquare z) := by
  intro n m hnm w hw
  have hr :
      1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
    Nat.one_div_le_one_div hnm
  exact
    ⟨⟨lt_of_le_of_lt (sub_le_sub_left hr z.re) hw.1.1,
        hw.1.2.trans (add_le_add_right hr z.re)⟩,
      ⟨lt_of_le_of_lt (sub_le_sub_left hr z.im) hw.2.1,
        hw.2.2.trans (add_le_add_right hr z.im)⟩⟩

theorem iInter_shrinkingSquare (z : ℂ) :
    ⋂ n : ℕ, shrinkingSquare z n = {z} := by
  ext w
  constructor
  · intro hw
    rw [mem_iInter] at hw
    have hre : ∀ n : ℕ, |w.re - z.re| ≤ 1 / ((n : ℝ) + 1) := by
      intro n
      have h := Complex.mem_reProdIm.mp (hw n)
      rw [abs_le]
      constructor <;> linarith [h.1.1, h.1.2]
    have him : ∀ n : ℕ, |w.im - z.im| ≤ 1 / ((n : ℝ) + 1) := by
      intro n
      have h := Complex.mem_reProdIm.mp (hw n)
      rw [abs_le]
      constructor <;> linarith [h.2.1, h.2.2]
    have hre0 : |w.re - z.re| ≤ 0 :=
      ge_of_tendsto' tendsto_one_div_add_atTop_nhds_zero_nat hre
    have him0 : |w.im - z.im| ≤ 0 :=
      ge_of_tendsto' tendsto_one_div_add_atTop_nhds_zero_nat him
    have hre_eq : w.re = z.re := by
      rw [← sub_eq_zero, ← abs_eq_zero]
      exact le_antisymm hre0 (abs_nonneg _)
    have him_eq : w.im = z.im := by
      rw [← sub_eq_zero, ← abs_eq_zero]
      exact le_antisymm him0 (abs_nonneg _)
    exact (Complex.ext hre_eq him_eq : w = z)
  · rintro rfl
    rw [mem_iInter]
    intro n
    dsimp [shrinkingSquare]
    rw [Complex.mem_reProdIm]
    simp only [mem_Ioc]
    have hn : 0 < (1 / ((n : ℝ) + 1) : ℝ) := by positivity
    constructor <;> constructor <;> linarith

theorem tendsto_setIntegral_shrinkingSquare_zero (F : ℂ → ℂ)
    (hF : MeasureTheory.Integrable F) (z : ℂ) :
    Filter.Tendsto (fun n : ℕ ↦ ∫ w in shrinkingSquare z n, F w)
      Filter.atTop (𝓝 0) := by
  have h :=
    MeasureTheory.tendsto_setIntegral_of_antitone
      (f := F) (fun n ↦ measurableSet_shrinkingSquare z n)
      (antitone_shrinkingSquare z) ⟨0, hF.integrableOn⟩
  rw [iInter_shrinkingSquare] at h
  simpa using h

/-- The small-square boundary limit along the concrete radii `1 / (n + 1)`. -/
theorem tendsto_rectBoundaryIntegral_cauchyKernel_mul_shrinkingSquare
    (G : ℂ → ℂ) (hG : Continuous G) (z : ℂ) :
    Filter.Tendsto
      (fun n : ℕ ↦
        rectBoundaryIntegral (fun w ↦ (w - z)⁻¹ * G w)
          ⟨z.re - 1 / ((n : ℝ) + 1), z.im - 1 / ((n : ℝ) + 1)⟩
          ⟨z.re + 1 / ((n : ℝ) + 1), z.im + 1 / ((n : ℝ) + 1)⟩)
      Filter.atTop (𝓝 ((2 * Real.pi * Complex.I) * G z)) := by
  apply (tendsto_rectBoundaryIntegral_cauchyKernel_mul_square G hG z).comp
  rw [tendsto_nhdsWithin_iff]
  exact
    ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Filter.Eventually.of_forall (fun n ↦ by
        simp only [mem_compl_iff, mem_singleton_iff]
        positivity)⟩

end Submission.Helpers
