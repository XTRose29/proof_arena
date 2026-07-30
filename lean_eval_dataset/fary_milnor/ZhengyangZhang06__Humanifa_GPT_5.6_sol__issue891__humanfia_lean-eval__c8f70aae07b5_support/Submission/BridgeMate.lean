import Submission.CroftonCompact

open LeanEval.Geometry.FaryMilnorProblem
open Set
open Filter
open scoped Real
open scoped Topology
open scoped RealInnerProductSpace
open WithLp

namespace Submission.Helpers


def IsForwardHeightMate (r : ℝ → Space) (u : Space) (t y : ℝ) : Prop :=
  y ∈ Ioo t (t + period) ∧
    height r u y = height r u t ∧
      directionalUnitTangent r u t * directionalUnitTangent r u y < 0

theorem existsUnique_forwardHeightMate_minMax_first
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space) {a b t : ℝ}
    (hdata : MinMaxBridgeData r u a b) (ht : t ∈ Ioo a b) :
    ∃! y, IsForwardHeightMate r u t y := by
  have hperiod : 0 < period := by simp [period, Real.pi_pos]
  have hta : height r u a < height r u t :=
    hdata.height_mono ⟨le_rfl, hdata.left_lt_right.le⟩
      ⟨ht.1.le, ht.2.le⟩ ht.1
  have htb : height r u t < height r u b :=
    hdata.height_mono ⟨ht.1.le, ht.2.le⟩
      ⟨hdata.left_lt_right.le, le_rfl⟩ ht.2
  have hwrap : b < a + period := by
    linarith [hdata.right_mem.2, hdata.left_mem.1]
  have hcont : ContinuousOn (height r u) (Icc b (a + period)) :=
    (continuous_height hknot u).continuousOn
  have hendpoint : height r u (a + period) = height r u a :=
    periodic_height hknot u a
  have hbetween : height r u t ∈
      Icc (height r u (a + period)) (height r u b) := by
    rw [hendpoint]
    exact ⟨hta.le, htb.le⟩
  have himage : height r u t ∈ height r u '' Icc b (a + period) :=
    intermediate_value_Icc' hwrap.le hcont hbetween
  obtain ⟨y, hyIcc, hyheight⟩ := himage
  have hyne_b : y ≠ b := by
    intro hyb
    subst y
    linarith
  have hyne_aP : y ≠ a + period := by
    intro hya
    subst y
    rw [hendpoint] at hyheight
    linarith
  have hyopen : y ∈ Ioo b (a + period) :=
    ⟨lt_of_le_of_ne hyIcc.1 (Ne.symm hyne_b),
      lt_of_le_of_ne hyIcc.2 hyne_aP⟩
  have hty : t < y := ht.2.trans hyopen.1
  have hytP : y < t + period := by
    linarith [hyopen.2, ht.1]
  have hsign := mul_neg_of_pos_of_neg
    (hdata.tangent_pos t ht) (hdata.tangent_neg_wrap y hyopen)
  refine ⟨y, ⟨⟨hty, hytP⟩, hyheight, hsign⟩, ?_⟩
  intro z hz
  have hzgneg : directionalUnitTangent r u z < 0 := by
    rcases mul_neg_iff.mp hz.2.2 with h | h
    · exact h.2
    · exact (not_lt_of_ge (hdata.tangent_pos t ht).le h.1).elim
  have hzb : b < z := by
    by_contra h
    have hzb_le : z ≤ b := le_of_not_gt h
    by_cases hzb_eq : z = b
    · subst z
      rw [hdata.tangent_right] at hzgneg
      linarith
    have hzb_lt : z < b := lt_of_le_of_ne hzb_le hzb_eq
    have hzpos := hdata.tangent_pos z
      ⟨ht.1.trans hz.1.1, hzb_lt⟩
    linarith
  have hzaP : z < a + period := by
    by_contra h
    have hzaP_le : a + period ≤ z := le_of_not_gt h
    let z' := z - period
    have hz'a : a ≤ z' := by dsimp [z']; linarith
    have hz't : z' < t := by dsimp [z']; linarith [hz.1.2]
    have hz'b : z' < b := hz't.trans ht.2
    have hzg' : directionalUnitTangent r u z' =
        directionalUnitTangent r u z := by
      have hper := periodic_directionalUnitTangent hknot u z'
      have heq : z' + period = z := by dsimp [z']; ring
      rw [heq] at hper
      exact hper.symm
    rcases hz'a.eq_or_lt with hz'eq | hz'alt
    · rw [← hz'eq, hdata.tangent_left] at hzg'
      linarith
    · have hz'pos := hdata.tangent_pos z' ⟨hz'alt, hz'b⟩
      rw [hzg'] at hz'pos
      linarith
  have hzband : z ∈ Icc b (a + period) := ⟨hzb.le, hzaP.le⟩
  exact hdata.height_anti_wrap.injOn hzband hyIcc
    (hz.2.1.trans hyheight.symm)

theorem existsUnique_forwardHeightMate_minMax_second
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space) {a b t : ℝ}
    (hdata : MinMaxBridgeData r u a b) (ht : t ∈ Ioo b (a + period)) :
    ∃! y, IsForwardHeightMate r u t y := by
  have hperiod : 0 < period := by simp [period, Real.pi_pos]
  have hheight_aP : height r u (a + period) = height r u a :=
    periodic_height hknot u a
  have hheight_bP : height r u (b + period) = height r u b :=
    periodic_height hknot u b
  have hwrap : b < a + period := by
    linarith [hdata.right_mem.2, hdata.left_mem.1]
  have hta : height r u (a + period) < height r u t :=
    hdata.height_anti_wrap ⟨ht.1.le, ht.2.le⟩
      ⟨hwrap.le, le_rfl⟩ ht.2
  have htb : height r u t < height r u b :=
    hdata.height_anti_wrap ⟨le_rfl, hwrap.le⟩
      ⟨ht.1.le, ht.2.le⟩ ht.1
  have hnext : a + period < b + period := by linarith [hdata.left_lt_right]
  have hcont : ContinuousOn (height r u) (Icc (a + period) (b + period)) :=
    (continuous_height hknot u).continuousOn
  have hbetween : height r u t ∈
      Icc (height r u (a + period)) (height r u (b + period)) := by
    rw [hheight_bP]
    exact ⟨hta.le, htb.le⟩
  have himage : height r u t ∈
      height r u '' Icc (a + period) (b + period) :=
    intermediate_value_Icc hnext.le hcont hbetween
  obtain ⟨y, hyIcc, hyheight⟩ := himage
  have hyne_aP : y ≠ a + period := by
    intro hya
    subst y
    linarith
  have hyne_bP : y ≠ b + period := by
    intro hyb
    subst y
    rw [hheight_bP] at hyheight
    linarith
  have hyopen : y ∈ Ioo (a + period) (b + period) :=
    ⟨lt_of_le_of_ne hyIcc.1 (Ne.symm hyne_aP),
      lt_of_le_of_ne hyIcc.2 hyne_bP⟩
  have hty : t < y := ht.2.trans hyopen.1
  have hytP : y < t + period := by
    linarith [hyopen.2, ht.1]
  have hgypos : 0 < directionalUnitTangent r u y := by
    let y' := y - period
    have hy' : y' ∈ Ioo a b := by
      dsimp [y']
      constructor <;> linarith [hyopen.1, hyopen.2]
    have hper := periodic_directionalUnitTangent hknot u y'
    have heq : y' + period = y := by dsimp [y']; ring
    rw [heq] at hper
    rw [hper]
    exact hdata.tangent_pos y' hy'
  have hsign := mul_neg_of_neg_of_pos
    (hdata.tangent_neg_wrap t ht) hgypos
  refine ⟨y, ⟨⟨hty, hytP⟩, hyheight, hsign⟩, ?_⟩
  intro z hz
  have hzgpos : 0 < directionalUnitTangent r u z := by
    rcases mul_neg_iff.mp hz.2.2 with h | h
    · exact (not_lt_of_ge (hdata.tangent_neg_wrap t ht).le h.1).elim
    · exact h.2
  have hzaP : a + period < z := by
    by_contra h
    have hzle : z ≤ a + period := le_of_not_gt h
    by_cases hzeq : z = a + period
    · subst z
      rw [periodic_directionalUnitTangent hknot u a,
        hdata.tangent_left] at hzgpos
      linarith
    have hzlt : z < a + period := lt_of_le_of_ne hzle hzeq
    have hzneg := hdata.tangent_neg_wrap z ⟨ht.1.trans hz.1.1, hzlt⟩
    linarith
  have hzbP : z < b + period := by
    by_contra h
    have hbPz : b + period ≤ z := le_of_not_gt h
    let z' := z - period
    have hzb : b ≤ z' := by dsimp [z']; linarith
    have hz't : z' < t := by dsimp [z']; linarith [hz.1.2]
    have hz'aP : z' < a + period := hz't.trans ht.2
    have hzg' : directionalUnitTangent r u z' =
        directionalUnitTangent r u z := by
      have hper := periodic_directionalUnitTangent hknot u z'
      have heq : z' + period = z := by dsimp [z']; ring
      rw [heq] at hper
      exact hper.symm
    rcases hzb.eq_or_lt with hzeq | hzblt
    · rw [← hzeq, hdata.tangent_right] at hzg'
      linarith
    · have hzneg := hdata.tangent_neg_wrap z' ⟨hzblt, hz'aP⟩
      rw [hzg'] at hzneg
      linarith
  have hzband : z ∈ Icc (a + period) (b + period) :=
    ⟨hzaP.le, hzbP.le⟩
  have hy' : y - period ∈ Icc a b := by
    constructor <;> linarith [hyIcc.1, hyIcc.2]
  have hz' : z - period ∈ Icc a b := by
    constructor <;> linarith [hzband.1, hzband.2]
  have hheight' : height r u (y - period) = height r u (z - period) := by
    have hyper := periodic_height hknot u (y - period)
    have hzper := periodic_height hknot u (z - period)
    have hyEq : y - period + period = y := by ring
    have hzEq : z - period + period = z := by ring
    rw [hyEq] at hyper
    rw [hzEq] at hzper
    rw [← hyper, ← hzper]
    exact hyheight.trans hz.2.1.symm
  have heq := hdata.height_mono.injOn hy' hz' hheight'
  linarith

theorem existsUnique_forwardHeightMate_minMax
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space) {a b t : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hgt : directionalUnitTangent r u t ≠ 0) :
    ∃! y, IsForwardHeightMate r u t y := by
  have hp : 0 < period := by simp [period, Real.pi_pos]
  obtain ⟨m, hm, _hmuniq⟩ := existsUnique_add_zsmul_mem_Ico hp t a
  let z : ℝ := t + m • period
  have hz : z ∈ Ico a (a + period) := by simpa [z] using hm
  have hheightShift : height r u z = height r u t := by
    have hper := (periodic_height hknot u).sub_zsmul_eq (x := t) (-m)
    simpa [z, sub_neg_eq_add] using hper
  have hgShift : directionalUnitTangent r u z =
      directionalUnitTangent r u t := by
    have hper := (periodic_directionalUnitTangent hknot u).sub_zsmul_eq
      (x := t) (-m)
    simpa [z, sub_neg_eq_add] using hper
  have hza : a < z := by
    rcases hz.1.eq_or_lt with h | h
    · have hgzero : directionalUnitTangent r u t = 0 := by
        rw [← hgShift, ← h, hdata.tangent_left]
      exact (hgt hgzero).elim
    · exact h
  have hzb : z ≠ b := by
    intro h
    have hgzero : directionalUnitTangent r u t = 0 := by
      rw [← hgShift, h, hdata.tangent_right]
    exact hgt hgzero
  have hbase : ∃! y, IsForwardHeightMate r u z y := by
    rcases lt_or_gt_of_ne hzb with hzb' | hbz
    · exact existsUnique_forwardHeightMate_minMax_first hknot u hdata ⟨hza, hzb'⟩
    · exact existsUnique_forwardHeightMate_minMax_second hknot u hdata ⟨hbz, hz.2⟩
  obtain ⟨y, hy, hyuniq⟩ := hbase
  let y' : ℝ := y - m • period
  have hy't : t < y' := by dsimp [y', z] at *; linarith [hy.1.1]
  have hy'tP : y' < t + period := by dsimp [y', z] at *; linarith [hy.1.2]
  have hy'height : height r u y' = height r u t := by
    have hper := (periodic_height hknot u).sub_zsmul_eq (x := y) m
    rw [hper, hy.2.1, hheightShift]
  have hy'g : directionalUnitTangent r u y' =
      directionalUnitTangent r u y := by
    exact (periodic_directionalUnitTangent hknot u).sub_zsmul_eq (x := y) m
  have hy'sign : directionalUnitTangent r u t *
      directionalUnitTangent r u y' < 0 := by
    rw [hy'g, ← hgShift]
    exact hy.2.2
  refine ⟨y', ⟨⟨hy't, hy'tP⟩, hy'height, hy'sign⟩, ?_⟩
  intro w hw
  let w' : ℝ := w + m • period
  have hw'z : z < w' := by dsimp [w', z]; linarith [hw.1.1]
  have hw'zP : w' < z + period := by dsimp [w', z]; linarith [hw.1.2]
  have hw'height : height r u w' = height r u z := by
    have hper := (periodic_height hknot u).sub_zsmul_eq (x := w) (-m)
    have heq : w - (-m) • period = w' := by dsimp [w']; module
    rw [heq] at hper
    rw [hper, hw.2.1, hheightShift]
  have hw'g : directionalUnitTangent r u w' =
      directionalUnitTangent r u w := by
    have hper := (periodic_directionalUnitTangent hknot u).sub_zsmul_eq
      (x := w) (-m)
    have heq : w - (-m) • period = w' := by dsimp [w']; module
    rwa [heq] at hper
  have hw'sign : directionalUnitTangent r u z *
      directionalUnitTangent r u w' < 0 := by
    rw [hw'g, hgShift]
    exact hw.2.2
  have hwy := hyuniq w' ⟨⟨hw'z, hw'zP⟩, hw'height, hw'sign⟩
  dsimp [w', y'] at *
  linarith

noncomputable def forwardHeightMateMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) (t : ℝ) : ℝ :=
  if h : directionalUnitTangent r u t = 0 then t
  else Classical.choose (existsUnique_forwardHeightMate_minMax hknot u hdata h).exists

theorem forwardHeightMateMinMax_spec {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b t : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hgt : directionalUnitTangent r u t ≠ 0) :
    IsForwardHeightMate r u t (forwardHeightMateMinMax hknot u hdata t) := by
  rw [forwardHeightMateMinMax, dif_neg hgt]
  exact Classical.choose_spec
    (existsUnique_forwardHeightMate_minMax hknot u hdata hgt).exists

theorem forwardHeightMateMinMax_unique {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b t y : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hgt : directionalUnitTangent r u t ≠ 0)
    (hy : IsForwardHeightMate r u t y) :
    y = forwardHeightMateMinMax hknot u hdata t := by
  exact (existsUnique_forwardHeightMate_minMax hknot u hdata hgt).unique hy
    (forwardHeightMateMinMax_spec hknot u hdata hgt)

theorem contDiffAt_forwardHeightMateMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b t₀ : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hgt : directionalUnitTangent r u t₀ ≠ 0) :
    ContDiffAt ℝ ⊤ (forwardHeightMateMinMax hknot u hdata) t₀ := by
  let h := height r u
  let g := directionalUnitTangent r u
  let y₀ := forwardHeightMateMinMax hknot u hdata t₀
  have hy₀ := forwardHeightMateMinMax_spec hknot u hdata hgt
  change IsForwardHeightMate r u t₀ y₀ at hy₀
  have hgy₀ : g y₀ ≠ 0 := by
    intro hzero
    have hs := hy₀.2.2
    change g t₀ * g y₀ < 0 at hs
    rw [hzero] at hs
    norm_num at hs
  let d := deriv h y₀
  have hd : d ≠ 0 := by
    dsimp [d, h]
    rw [deriv_height_eq_speed_mul_directionalUnitTangent hknot u y₀]
    exact mul_ne_zero (norm_ne_zero_iff.mpr (hknot.regular y₀)) hgy₀
  let du : ℝˣ := Units.mk0 d hd
  let e : ℝ ≃L[ℝ] ℝ := (ContinuousLinearEquiv.unitsEquivAut ℝ) du
  have hder : HasDerivAt h d y₀ := by
    exact (((contDiff_height hknot u).differentiable (by simp)).differentiableAt).hasDerivAt
  have hfder : HasFDerivAt h (e : ℝ →L[ℝ] ℝ) y₀ := by
    have heq : (e : ℝ →L[ℝ] ℝ) = ContinuousLinearMap.toSpanSingleton ℝ d := by
      apply ContinuousLinearMap.ext
      intro x
      rw [ContinuousLinearMap.toSpanSingleton_apply]
      change x * d = x • d
      simp [smul_eq_mul]
    rw [heq]
    exact hder.hasFDerivAt
  have hh : ContDiffAt ℝ ⊤ h y₀ := (contDiff_height hknot u).contDiffAt
  let inv : ℝ → ℝ := hh.localInverse hfder (by simp)
  have hinv : ContDiffAt ℝ ⊤ inv (h y₀) := by
    exact hh.to_localInverse hfder (by simp)
  have hinvval : inv (h y₀) = y₀ := by
    exact hh.localInverse_apply_image hfder (by simp)
  let cand : ℝ → ℝ := fun t => inv (h t)
  have hcand : ContDiffAt ℝ ⊤ cand t₀ := by
    have hinv' : ContDiffAt ℝ ⊤ inv (h t₀) := by
      have hyheight := hy₀.2.1
      change h y₀ = h t₀ at hyheight
      rw [← hyheight]
      exact hinv
    exact hinv'.comp t₀ (contDiff_height hknot u).contDiffAt
  have hcandval : cand t₀ = y₀ := by
    dsimp [cand]
    rw [show h t₀ = h y₀ by exact hy₀.2.1.symm, hinvval]
  have hright : ∀ᶠ x in 𝓝 (h y₀), h (inv x) = x := by
    exact (hh.hasStrictFDerivAt' hfder (by simp)).eventually_right_inverse
  have hright_comp : ∀ᶠ t in 𝓝 t₀, h (cand t) = h t := by
    have htend : Tendsto h (𝓝 t₀) (𝓝 (h y₀)) := by
      have hyheight := hy₀.2.1
      change h y₀ = h t₀ at hyheight
      rw [hyheight]
      exact (continuous_height hknot u).continuousAt
    exact htend.eventually hright
  have hleft_lt : ∀ᶠ t in 𝓝 t₀, t < cand t := by
    have hcont : ContinuousAt (fun t => cand t - t) t₀ :=
      hcand.continuousAt.sub continuousAt_id
    have hpos : 0 < cand t₀ - t₀ := by rw [hcandval]; linarith [hy₀.1.1]
    exact (isOpen_Ioi.mem_nhds hpos) |> hcont.preimage_mem_nhds |> fun hmem => by
      filter_upwards [hmem] with t ht
      exact sub_pos.mp ht
  have hright_lt : ∀ᶠ t in 𝓝 t₀, cand t < t + period := by
    have hcont : ContinuousAt (fun t => t + period - cand t) t₀ :=
      (continuousAt_id.add continuousAt_const).sub hcand.continuousAt
    have hpos : 0 < t₀ + period - cand t₀ := by
      rw [hcandval]
      linarith [hy₀.1.2]
    exact (isOpen_Ioi.mem_nhds hpos) |> hcont.preimage_mem_nhds |> fun hmem => by
      filter_upwards [hmem] with t ht
      exact sub_pos.mp ht
  have hsign : ∀ᶠ t in 𝓝 t₀, g t * g (cand t) < 0 := by
    have hcont : ContinuousAt (fun t => g t * g (cand t)) t₀ := by
      exact (continuous_directionalUnitTangent hknot u).continuousAt.mul
        ((continuous_directionalUnitTangent hknot u).continuousAt.comp
          hcand.continuousAt)
    have hneg : g t₀ * g (cand t₀) < 0 := by
      rw [hcandval]
      exact hy₀.2.2
    exact (isOpen_Iio.mem_nhds hneg) |> hcont.preimage_mem_nhds
  have heq : ∀ᶠ t in 𝓝 t₀,
      forwardHeightMateMinMax hknot u hdata t = cand t := by
    filter_upwards [hright_comp, hleft_lt, hright_lt, hsign] with t hheight hlt hrt hs
    have hgne : g t ≠ 0 := fun hz => by rw [hz] at hs; norm_num at hs
    exact (forwardHeightMateMinMax_unique hknot u hdata hgne
      ⟨⟨hlt, hrt⟩, hheight, hs⟩).symm
  exact hcand.congr_of_eventuallyEq heq

theorem directionalUnitTangent_forwardHeightMateMinMax_ne_zero
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space) {a b t : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hgt : directionalUnitTangent r u t ≠ 0) :
    directionalUnitTangent r u
      (forwardHeightMateMinMax hknot u hdata t) ≠ 0 := by
  intro hzero
  have hs := (forwardHeightMateMinMax_spec hknot u hdata hgt).2.2
  rw [hzero] at hs
  norm_num at hs

theorem forwardHeightMateMinMax_mate
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space) {a b t : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hgt : directionalUnitTangent r u t ≠ 0) :
    forwardHeightMateMinMax hknot u hdata
        (forwardHeightMateMinMax hknot u hdata t) =
      t + period := by
  let y := forwardHeightMateMinMax hknot u hdata t
  have hy := forwardHeightMateMinMax_spec hknot u hdata hgt
  change IsForwardHeightMate r u t y at hy
  have hgy := directionalUnitTangent_forwardHeightMateMinMax_ne_zero
    hknot u hdata hgt
  symm
  apply forwardHeightMateMinMax_unique hknot u hdata hgy
  refine ⟨⟨hy.1.2, by linarith [hy.1.1]⟩, ?_, ?_⟩
  · rw [periodic_height hknot u t]
    exact hy.2.1.symm
  · rw [periodic_directionalUnitTangent hknot u t]
    nlinarith [hy.2.2]

theorem forwardHeightMateMinMax_add_period
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space) {a b t : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hgt : directionalUnitTangent r u t ≠ 0) :
    forwardHeightMateMinMax hknot u hdata (t + period) =
      forwardHeightMateMinMax hknot u hdata t + period := by
  have hgtP : directionalUnitTangent r u (t + period) ≠ 0 := by
    rw [periodic_directionalUnitTangent hknot u t]
    exact hgt
  symm
  apply forwardHeightMateMinMax_unique hknot u hdata hgtP
  have hy := forwardHeightMateMinMax_spec hknot u hdata hgt
  refine ⟨⟨by linarith [hy.1.1], by linarith [hy.1.2]⟩, ?_, ?_⟩
  · rw [periodic_height hknot u,
      periodic_height hknot u]
    exact hy.2.1
  · rw [periodic_directionalUnitTangent hknot u,
      periodic_directionalUnitTangent hknot u]
    exact hy.2.2

theorem forwardHeightMateMinMax_add_period_all
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space) {a b t : ℝ}
    (hdata : MinMaxBridgeData r u a b) :
    forwardHeightMateMinMax hknot u hdata (t + period) =
      forwardHeightMateMinMax hknot u hdata t + period := by
  by_cases hgt : directionalUnitTangent r u t = 0
  · have hgtP : directionalUnitTangent r u (t + period) = 0 := by
      rw [periodic_directionalUnitTangent hknot u t]
      exact hgt
    simp [forwardHeightMateMinMax, hgt, hgtP]
  · exact forwardHeightMateMinMax_add_period hknot u hdata hgt

theorem forwardHeightMateMinMax_point_mate
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space) {a b t : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hgt : directionalUnitTangent r u t ≠ 0) :
    r (forwardHeightMateMinMax hknot u hdata
        (forwardHeightMateMinMax hknot u hdata t)) = r t := by
  rw [forwardHeightMateMinMax_mate hknot u hdata hgt,
    hknot.periodic]

theorem forwardHeightMateMinMax_tangent_mate
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space) {a b t : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hgt : directionalUnitTangent r u t ≠ 0) :
    directionalUnitTangent r u
        (forwardHeightMateMinMax hknot u hdata
          (forwardHeightMateMinMax hknot u hdata t)) =
      directionalUnitTangent r u t := by
  rw [forwardHeightMateMinMax_mate hknot u hdata hgt,
    periodic_directionalUnitTangent hknot u t]

noncomputable def mateCenterMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) (t : ℝ) : Space :=
  (2 : ℝ)⁻¹ •
    (r t + r (forwardHeightMateMinMax hknot u hdata t))

noncomputable def mateAlphaMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) (t : ℝ) : ℝ :=
  (directionalUnitTangent r u t - directionalUnitTangent r u
    (forwardHeightMateMinMax hknot u hdata t)) / 2

noncomputable def mateDirectionMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) (t : ℝ) : Space :=
  (directionalUnitTangent r u t - directionalUnitTangent r u
    (forwardHeightMateMinMax hknot u hdata t))⁻¹ •
      (r t - r (forwardHeightMateMinMax hknot u hdata t))

theorem mateAlphaMinMax_ne_zero {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b t : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hgt : directionalUnitTangent r u t ≠ 0) :
    mateAlphaMinMax hknot u hdata t ≠ 0 := by
  have hs := (forwardHeightMateMinMax_spec hknot u hdata hgt).2.2
  unfold mateAlphaMinMax
  intro hzero
  have heq : directionalUnitTangent r u t = directionalUnitTangent r u
      (forwardHeightMateMinMax hknot u hdata t) := by linarith
  rw [heq] at hs
  exact (not_lt_of_ge (mul_self_nonneg _)) hs

theorem mateDirectionMinMax_ne_zero {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b t : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hgt : directionalUnitTangent r u t ≠ 0) :
    mateDirectionMinMax hknot u hdata t ≠ 0 := by
  let y := forwardHeightMateMinMax hknot u hdata t
  have hy := forwardHeightMateMinMax_spec hknot u hdata hgt
  change IsForwardHeightMate r u t y at hy
  have hden : directionalUnitTangent r u t - directionalUnitTangent r u y ≠ 0 := by
    intro hzero
    have heq := sub_eq_zero.mp hzero
    have hs := hy.2.2
    rw [heq] at hs
    exact (not_lt_of_ge (mul_self_nonneg _)) hs
  have hry : r t ≠ r y := by
    intro heq
    have hinj := injOn_periodic_shifted_Ico hknot.periodic
      hknot.injective_on_period t
    have htP : t < t + period := by simp [period, Real.pi_pos]
    have hty := hinj (mem_Ico.mpr ⟨le_rfl, htP⟩)
      (mem_Ico.mpr ⟨hy.1.1.le, hy.1.2⟩) heq
    linarith [hy.1.1]
  unfold mateDirectionMinMax
  change (directionalUnitTangent r u t - directionalUnitTangent r u y)⁻¹ •
    (r t - r y) ≠ 0
  exact smul_ne_zero (inv_ne_zero hden) (sub_ne_zero.mpr hry)

theorem inner_mateDirectionMinMax_eq_zero {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b t : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hgt : directionalUnitTangent r u t ≠ 0) :
    inner ℝ u (mateDirectionMinMax hknot u hdata t) = 0 := by
  have hy := (forwardHeightMateMinMax_spec hknot u hdata hgt).2.1
  unfold mateDirectionMinMax
  rw [real_inner_smul_right, inner_sub_right]
  change (directionalUnitTangent r u t - directionalUnitTangent r u
      (forwardHeightMateMinMax hknot u hdata t))⁻¹ *
    (height r u t - height r u
      (forwardHeightMateMinMax hknot u hdata t)) = 0
  rw [hy]
  simp

theorem curve_eq_mateCenter_add_alpha_smul_direction {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b t : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hgt : directionalUnitTangent r u t ≠ 0) :
    r t = mateCenterMinMax hknot u hdata t +
      mateAlphaMinMax hknot u hdata t • mateDirectionMinMax hknot u hdata t := by
  let y := forwardHeightMateMinMax hknot u hdata t
  have hy := forwardHeightMateMinMax_spec hknot u hdata hgt
  change IsForwardHeightMate r u t y at hy
  have hden : directionalUnitTangent r u t - directionalUnitTangent r u y ≠ 0 := by
    intro hzero
    have heq := sub_eq_zero.mp hzero
    have hs := hy.2.2
    rw [heq] at hs
    exact (not_lt_of_ge (mul_self_nonneg _)) hs
  unfold mateCenterMinMax mateAlphaMinMax mateDirectionMinMax
  change r t = (2 : ℝ)⁻¹ • (r t + r y) +
    ((directionalUnitTangent r u t - directionalUnitTangent r u y) / 2) •
      ((directionalUnitTangent r u t - directionalUnitTangent r u y)⁻¹ •
        (r t - r y))
  rw [smul_smul]
  have hcoef :
      (directionalUnitTangent r u t - directionalUnitTangent r u y) / 2 *
        (directionalUnitTangent r u t - directionalUnitTangent r u y)⁻¹ =
      (2 : ℝ)⁻¹ := by
    field_simp [hden]
  rw [hcoef]
  module

theorem contDiffAt_mateCenterMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b t : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hgt : directionalUnitTangent r u t ≠ 0) :
    ContDiffAt ℝ ⊤ (mateCenterMinMax hknot u hdata) t := by
  have hm := contDiffAt_forwardHeightMateMinMax hknot u hdata hgt
  unfold mateCenterMinMax
  exact (hknot.smooth.contDiffAt.add
    (hknot.smooth.contDiffAt.comp t hm)).const_smul (2 : ℝ)⁻¹

theorem contDiffAt_mateAlphaMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b t : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hgt : directionalUnitTangent r u t ≠ 0) :
    ContDiffAt ℝ ⊤ (mateAlphaMinMax hknot u hdata) t := by
  have hm := contDiffAt_forwardHeightMateMinMax hknot u hdata hgt
  unfold mateAlphaMinMax
  exact ((contDiff_directionalUnitTangent hknot u).contDiffAt.sub
    ((contDiff_directionalUnitTangent hknot u).contDiffAt.comp t hm)).div_const 2

theorem contDiffAt_mateDirectionMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b t : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hgt : directionalUnitTangent r u t ≠ 0) :
    ContDiffAt ℝ ⊤ (mateDirectionMinMax hknot u hdata) t := by
  have hm := contDiffAt_forwardHeightMateMinMax hknot u hdata hgt
  have hgdiff : ContDiffAt ℝ ⊤ (fun z => directionalUnitTangent r u z -
      directionalUnitTangent r u (forwardHeightMateMinMax hknot u hdata z)) t :=
    (contDiff_directionalUnitTangent hknot u).contDiffAt.sub
      ((contDiff_directionalUnitTangent hknot u).contDiffAt.comp t hm)
  have hrdiff : ContDiffAt ℝ ⊤ (fun z => r z -
      r (forwardHeightMateMinMax hknot u hdata z)) t :=
    hknot.smooth.contDiffAt.sub (hknot.smooth.contDiffAt.comp t hm)
  unfold mateDirectionMinMax
  exact (hgdiff.inv (by
    intro hzero
    apply mateAlphaMinMax_ne_zero hknot u hdata hgt
    unfold mateAlphaMinMax
    rw [hzero]
    norm_num)).smul hrdiff

theorem mateCenterMinMax_mate {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b t : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hgt : directionalUnitTangent r u t ≠ 0) :
    mateCenterMinMax hknot u hdata
        (forwardHeightMateMinMax hknot u hdata t) =
      mateCenterMinMax hknot u hdata t := by
  unfold mateCenterMinMax
  rw [forwardHeightMateMinMax_point_mate hknot u hdata hgt]
  module

theorem mateAlphaMinMax_mate {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b t : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hgt : directionalUnitTangent r u t ≠ 0) :
    mateAlphaMinMax hknot u hdata
        (forwardHeightMateMinMax hknot u hdata t) =
      -mateAlphaMinMax hknot u hdata t := by
  unfold mateAlphaMinMax
  rw [forwardHeightMateMinMax_tangent_mate hknot u hdata hgt]
  ring

theorem mateDirectionMinMax_mate {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b t : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hgt : directionalUnitTangent r u t ≠ 0) :
    mateDirectionMinMax hknot u hdata
        (forwardHeightMateMinMax hknot u hdata t) =
      mateDirectionMinMax hknot u hdata t := by
  unfold mateDirectionMinMax
  rw [forwardHeightMateMinMax_tangent_mate hknot u hdata hgt,
    forwardHeightMateMinMax_point_mate hknot u hdata hgt]
  have hden : directionalUnitTangent r u t - directionalUnitTangent r u
      (forwardHeightMateMinMax hknot u hdata t) ≠ 0 := by
    intro hzero
    apply mateAlphaMinMax_ne_zero hknot u hdata hgt
    unfold mateAlphaMinMax
    rw [hzero]
    norm_num
  rw [show directionalUnitTangent r u
        (forwardHeightMateMinMax hknot u hdata t) - directionalUnitTangent r u t =
      -(directionalUnitTangent r u t - directionalUnitTangent r u
        (forwardHeightMateMinMax hknot u hdata t)) by ring]
  rw [inv_neg]
  module

end Submission.Helpers
