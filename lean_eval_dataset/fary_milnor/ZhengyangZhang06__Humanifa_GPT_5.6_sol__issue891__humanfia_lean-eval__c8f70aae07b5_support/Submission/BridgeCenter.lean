import Submission.BridgeMate

open LeanEval.Geometry.FaryMilnorProblem
open Set
open Filter
open scoped Real
open scoped Topology
open scoped RealInnerProductSpace
open WithLp

namespace Submission.Helpers

theorem MinMaxBridgeData.height_endpoints_lt {r : ℝ → Space} {u : Space}
    {a b : ℝ} (hdata : MinMaxBridgeData r u a b) :
    height r u a < height r u b :=
  hdata.height_mono ⟨le_rfl, hdata.left_lt_right.le⟩
    ⟨hdata.left_lt_right.le, le_rfl⟩ hdata.left_lt_right

theorem strictMonoOn_le_of_le {f : ℝ → ℝ} {s : Set ℝ} {x y : ℝ}
    (hf : StrictMonoOn f s) (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≤ y) :
    f x ≤ f y := by
  rcases hxy.eq_or_lt with rfl | hlt
  · exact le_rfl
  · exact (hf hx hy hlt).le

noncomputable def minMaxHeightOrderIso {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) :
    Icc a b ≃o Icc (height r u a) (height r u b) := by
  let f : Icc a b → Icc (height r u a) (height r u b) := fun t =>
    ⟨height r u t, by
      constructor
      · exact strictMonoOn_le_of_le hdata.height_mono
          ⟨le_rfl, hdata.left_lt_right.le⟩ t.property t.property.1
      · exact strictMonoOn_le_of_le hdata.height_mono t.property
          ⟨hdata.left_lt_right.le, le_rfl⟩ t.property.2⟩
  have hf : StrictMono f := by
    intro x y hxy
    exact hdata.height_mono x.property y.property hxy
  have hsurj : Function.Surjective f := by
    intro x
    have himage : (x : ℝ) ∈ height r u '' Icc a b :=
      intermediate_value_Icc hdata.left_lt_right.le
        (continuous_height hknot u).continuousOn x.property
    obtain ⟨t, ht, htx⟩ := himage
    refine ⟨⟨t, ht⟩, ?_⟩
    exact Subtype.ext htx
  exact StrictMono.orderIsoOfSurjective f hf hsurj

@[simp] theorem minMaxHeightOrderIso_apply {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) (t : Icc a b) :
    ((minMaxHeightOrderIso hknot u hdata t :
      Icc (height r u a) (height r u b)) : ℝ) = height r u t := rfl

noncomputable def minMaxHeightParameter {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) (x : ℝ) : ℝ :=
  ((minMaxHeightOrderIso hknot u hdata).symm
    (projIcc (height r u a) (height r u b)
      (strictMonoOn_le_of_le hdata.height_mono
        ⟨le_rfl, hdata.left_lt_right.le⟩
        ⟨hdata.left_lt_right.le, le_rfl⟩ hdata.left_lt_right.le) x) : Icc a b)

theorem continuous_minMaxHeightParameter {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) :
    Continuous (minMaxHeightParameter hknot u hdata) := by
  exact continuous_subtype_val.comp
    ((minMaxHeightOrderIso hknot u hdata).symm.continuous.comp
      continuous_projIcc)

theorem minMaxHeightParameter_mem {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b x : ℝ}
    (hdata : MinMaxBridgeData r u a b) :
    minMaxHeightParameter hknot u hdata x ∈ Icc a b :=
  (minMaxHeightOrderIso hknot u hdata).symm
    (projIcc (height r u a) (height r u b)
      (strictMonoOn_le_of_le hdata.height_mono
        ⟨le_rfl, hdata.left_lt_right.le⟩
        ⟨hdata.left_lt_right.le, le_rfl⟩ hdata.left_lt_right.le) x) |>.property

theorem height_minMaxHeightParameter {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b x : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hx : x ∈ Icc (height r u a) (height r u b)) :
    height r u (minMaxHeightParameter hknot u hdata x) = x := by
  let z : Icc (height r u a) (height r u b) := ⟨x, hx⟩
  have happly := (minMaxHeightOrderIso hknot u hdata).apply_symm_apply z
  have hval := congrArg Subtype.val happly
  change height r u ((minMaxHeightOrderIso hknot u hdata).symm z) = x at hval
  simpa only [minMaxHeightParameter, z,
    projIcc_of_mem (strictMonoOn_le_of_le hdata.height_mono
      ⟨le_rfl, hdata.left_lt_right.le⟩
      ⟨hdata.left_lt_right.le, le_rfl⟩ hdata.left_lt_right.le) hx] using hval

theorem minMaxHeightParameter_height {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b t : ℝ}
    (hdata : MinMaxBridgeData r u a b) (ht : t ∈ Icc a b) :
    minMaxHeightParameter hknot u hdata (height r u t) = t := by
  apply hdata.height_mono.injOn (minMaxHeightParameter_mem hknot u hdata) ht
  rw [height_minMaxHeightParameter hknot u hdata]
  exact ⟨strictMonoOn_le_of_le hdata.height_mono
      ⟨le_rfl, hdata.left_lt_right.le⟩ ht ht.1,
    strictMonoOn_le_of_le hdata.height_mono ht
      ⟨hdata.left_lt_right.le, le_rfl⟩ ht.2⟩

theorem contDiffAt_minMaxHeightParameter {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b x₀ : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hx₀ : x₀ ∈ Ioo (height r u a) (height r u b)) :
    ContDiffAt ℝ ⊤ (minMaxHeightParameter hknot u hdata) x₀ := by
  let h := height r u
  let t₀ := minMaxHeightParameter hknot u hdata x₀
  have ht₀ : t₀ ∈ Ioo a b := by
    have htmem := minMaxHeightParameter_mem hknot u hdata (x := x₀)
    constructor
    · by_contra hta
      have heq : t₀ = a := le_antisymm (le_of_not_gt hta) htmem.1
      have hh := height_minMaxHeightParameter hknot u hdata
        ⟨hx₀.1.le, hx₀.2.le⟩
      change h t₀ = x₀ at hh
      rw [heq] at hh
      exact (ne_of_lt hx₀.1) hh
    · by_contra htb
      have heq : t₀ = b := le_antisymm htmem.2 (le_of_not_gt htb)
      have hh := height_minMaxHeightParameter hknot u hdata
        ⟨hx₀.1.le, hx₀.2.le⟩
      change h t₀ = x₀ at hh
      rw [heq] at hh
      exact (ne_of_lt hx₀.2) hh.symm
  have hgt : directionalUnitTangent r u t₀ ≠ 0 :=
    ne_of_gt (hdata.tangent_pos t₀ ht₀)
  let d := deriv h t₀
  have hd : d ≠ 0 := by
    dsimp [d, h]
    rw [deriv_height_eq_speed_mul_directionalUnitTangent hknot u t₀]
    exact mul_ne_zero (norm_ne_zero_iff.mpr (hknot.regular t₀)) hgt
  let du : ℝˣ := Units.mk0 d hd
  let e : ℝ ≃L[ℝ] ℝ := (ContinuousLinearEquiv.unitsEquivAut ℝ) du
  have hder : HasDerivAt h d t₀ :=
    (((contDiff_height hknot u).differentiable (by simp)).differentiableAt).hasDerivAt
  have hfder : HasFDerivAt h (e : ℝ →L[ℝ] ℝ) t₀ := by
    have heq : (e : ℝ →L[ℝ] ℝ) = ContinuousLinearMap.toSpanSingleton ℝ d := by
      apply ContinuousLinearMap.ext
      intro z
      rw [ContinuousLinearMap.toSpanSingleton_apply]
      change z * d = z • d
      simp [smul_eq_mul]
    rw [heq]
    exact hder.hasFDerivAt
  have hh : ContDiffAt ℝ ⊤ h t₀ := (contDiff_height hknot u).contDiffAt
  let inv : ℝ → ℝ := hh.localInverse hfder (by simp)
  have hinv : ContDiffAt ℝ ⊤ inv (h t₀) := hh.to_localInverse hfder (by simp)
  have hheight : h t₀ = x₀ := by
    exact height_minMaxHeightParameter hknot u hdata
      ⟨hx₀.1.le, hx₀.2.le⟩
  have hinv' : ContDiffAt ℝ ⊤ inv x₀ := by rwa [← hheight]
  have hleft : ∀ᶠ x in 𝓝 x₀, inv x = minMaxHeightParameter hknot u hdata x := by
    have hinvcont := hinv'.continuousAt
    have hinvI : ∀ᶠ x in 𝓝 x₀, inv x ∈ Ioo a b := by
      have hval : inv x₀ = t₀ := by
        rw [← hheight]
        exact hh.localInverse_apply_image hfder (by simp)
      have hopen : Ioo a b ∈ 𝓝 t₀ := isOpen_Ioo.mem_nhds ht₀
      rw [← hval] at hopen
      exact hinvcont.eventually hopen
    have hxI : ∀ᶠ x in 𝓝 x₀,
        x ∈ Ioo (height r u a) (height r u b) :=
      isOpen_Ioo.mem_nhds hx₀
    have hright : ∀ᶠ x in 𝓝 x₀, h (inv x) = x := by
      have hr := (hh.hasStrictFDerivAt' hfder (by simp)).eventually_right_inverse
      have : 𝓝 x₀ = 𝓝 (h t₀) := by rw [hheight]
      rwa [this]
    filter_upwards [hinvI, hxI, hright] with x hix hxx hhx
    apply hdata.height_mono.injOn ⟨hix.1.le, hix.2.le⟩
      (minMaxHeightParameter_mem hknot u hdata)
    rw [show height r u (inv x) = x by exact hhx,
      height_minMaxHeightParameter hknot u hdata ⟨hxx.1.le, hxx.2.le⟩]
  exact hinv'.congr_of_eventuallyEq (Filter.EventuallyEq.symm hleft)

noncomputable def centralMateDirectionMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) (x : ℝ) : Space :=
  mateDirectionMinMax hknot u hdata
    (minMaxHeightParameter hknot u hdata x)

theorem contDiffAt_centralMateDirectionMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b x : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hx : x ∈ Ioo (height r u a) (height r u b)) :
    ContDiffAt ℝ ⊤ (centralMateDirectionMinMax hknot u hdata) x := by
  have hp := contDiffAt_minMaxHeightParameter hknot u hdata hx
  have ht : minMaxHeightParameter hknot u hdata x ∈ Ioo a b := by
    have hm := minMaxHeightParameter_mem hknot u hdata (x := x)
    have hh := height_minMaxHeightParameter hknot u hdata
      ⟨hx.1.le, hx.2.le⟩
    constructor
    · by_contra h
      have heq := le_antisymm (le_of_not_gt h) hm.1
      rw [heq] at hh
      exact (ne_of_lt hx.1) hh
    · by_contra h
      have heq := le_antisymm hm.2 (le_of_not_gt h)
      rw [heq] at hh
      exact (ne_of_lt hx.2) hh.symm
  have hg := ne_of_gt (hdata.tangent_pos _ ht)
  exact (contDiffAt_mateDirectionMinMax hknot u hdata hg).comp x hp

theorem centralMateDirectionMinMax_ne_zero {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b x : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hx : x ∈ Ioo (height r u a) (height r u b)) :
    centralMateDirectionMinMax hknot u hdata x ≠ 0 := by
  have ht : minMaxHeightParameter hknot u hdata x ∈ Ioo a b := by
    have hm := minMaxHeightParameter_mem hknot u hdata (x := x)
    have hh := height_minMaxHeightParameter hknot u hdata
      ⟨hx.1.le, hx.2.le⟩
    constructor
    · by_contra h
      have heq := le_antisymm (le_of_not_gt h) hm.1
      rw [heq] at hh
      exact (ne_of_lt hx.1) hh
    · by_contra h
      have heq := le_antisymm hm.2 (le_of_not_gt h)
      rw [heq] at hh
      exact (ne_of_lt hx.2) hh.symm
  exact mateDirectionMinMax_ne_zero hknot u hdata
    (ne_of_gt (hdata.tangent_pos _ ht))

theorem inner_centralMateDirectionMinMax_eq_zero {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b x : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hx : x ∈ Ioo (height r u a) (height r u b)) :
    inner ℝ u (centralMateDirectionMinMax hknot u hdata x) = 0 := by
  have ht : minMaxHeightParameter hknot u hdata x ∈ Ioo a b := by
    have hm := minMaxHeightParameter_mem hknot u hdata (x := x)
    have hh := height_minMaxHeightParameter hknot u hdata
      ⟨hx.1.le, hx.2.le⟩
    constructor
    · by_contra h
      have heq := le_antisymm (le_of_not_gt h) hm.1
      rw [heq] at hh
      exact (ne_of_lt hx.1) hh
    · by_contra h
      have heq := le_antisymm hm.2 (le_of_not_gt h)
      rw [heq] at hh
      exact (ne_of_lt hx.2) hh.symm
  exact inner_mateDirectionMinMax_eq_zero hknot u hdata
    (ne_of_gt (hdata.tangent_pos _ ht))

end Submission.Helpers
