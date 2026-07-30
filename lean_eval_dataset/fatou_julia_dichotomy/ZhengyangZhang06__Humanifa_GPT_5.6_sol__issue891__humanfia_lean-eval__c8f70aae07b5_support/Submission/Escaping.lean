import Submission.CantorClassification

open LeanEval.ComplexAnalysis.FatouJuliaProblem
open Function

namespace Submission.Escaping

noncomputable section

open Polynomial Topology

def openApprox (c : ℂ) (n : ℕ) : Set ℂ :=
  (Tc c)^[n] ⁻¹' Metric.ball 0 (Helpers.escapeRadius c)

lemma openApprox_succ (c : ℂ) (n : ℕ) :
    openApprox c (n + 1) = Tc c ⁻¹' openApprox c n := by
  ext z
  simp only [openApprox, Set.mem_preimage, Function.iterate_succ_apply]

lemma isOpen_openApprox (c : ℂ) (n : ℕ) : IsOpen (openApprox c n) := by
  apply Metric.isOpen_ball.preimage
  exact (by unfold Tc; fun_prop : Continuous (Tc c)).iterate n

lemma escapeRadius_pos (c : ℂ) : 0 < Helpers.escapeRadius c := by
  dsimp [Helpers.escapeRadius]
  positivity

lemma norm_tc_gt_escapeRadius_of_ge {c z : ℂ}
    (hz : Helpers.escapeRadius c ≤ ‖z‖) :
    Helpers.escapeRadius c < ‖Tc c z‖ := by
  have hlower : ‖z‖ ^ 2 - ‖c‖ ≤ ‖Tc c z‖ := by
    calc
      ‖z‖ ^ 2 - ‖c‖ = ‖z ^ 2‖ - ‖-c‖ := by simp
      _ ≤ ‖z ^ 2 - -c‖ := norm_sub_norm_le _ _
      _ = ‖Tc c z‖ := by simp [Tc]
  dsimp [Helpers.escapeRadius] at hz ⊢
  nlinarith [norm_nonneg c, norm_nonneg z, sq_nonneg (‖z‖ - (‖c‖ + 2))]

lemma norm_iterate_lt_escapeRadius_of_mem_filledJulia {c z : ℂ}
    (hz : z ∈ FilledJulia c) (n : ℕ) :
    ‖(Tc c)^[n] z‖ < Helpers.escapeRadius c := by
  have hbounds := (Helpers.mem_filledJulia_iff_forall_norm_le_escapeRadius c z).1 hz
  by_contra! hn
  have hnext := norm_tc_gt_escapeRadius_of_ge (c := c) (z := (Tc c)^[n] z) hn
  exact (not_lt_of_ge (hbounds (n + 1))) (by
    simpa only [Function.iterate_succ_apply'] using hnext)

lemma filledJulia_subset_openApprox (c : ℂ) (n : ℕ) :
    FilledJulia c ⊆ openApprox c n := by
  intro z hz
  simpa only [openApprox, Set.mem_preimage, Metric.mem_ball, dist_zero_right] using
    norm_iterate_lt_escapeRadius_of_mem_filledJulia hz n

lemma openApprox_succ_subset (c : ℂ) (n : ℕ) :
    openApprox c (n + 1) ⊆ openApprox c n := by
  intro z hz
  simp only [openApprox, Set.mem_preimage, Metric.mem_ball, dist_zero_right] at hz ⊢
  by_contra! hn
  have hnext := norm_tc_gt_escapeRadius_of_ge (c := c) (z := (Tc c)^[n] z) hn
  exact (not_lt_of_ge hnext.le) (by
    simpa only [Function.iterate_succ_apply'] using hz)

lemma exists_criticalValue_not_mem_openApprox {c : ℂ} (hc : c ∉ Mandelbrot) :
    ∃ n : ℕ, c ∉ openApprox c n := by
  obtain ⟨n, hn⟩ := Helpers.exists_norm_criticalOrbit_gt_escapeRadius_of_not_mem_mandelbrot hc
  cases n with
  | zero =>
      simp only [Function.iterate_zero_apply, norm_zero] at hn
      exact (not_lt_of_ge (escapeRadius_pos c).le hn).elim
  | succ n =>
      refine ⟨n, ?_⟩
      simpa only [openApprox, Set.mem_preimage, Metric.mem_ball, dist_zero_right,
        Function.iterate_succ_apply, Tc, zero_pow (by norm_num : 2 ≠ 0), zero_add] using
        (not_lt_of_ge hn.le)

noncomputable def escapeLevel (c : ℂ) (hc : c ∉ Mandelbrot) : ℕ :=
  by
    classical
    exact Nat.find (exists_criticalValue_not_mem_openApprox hc)

lemma criticalValue_not_mem_openApprox_escapeLevel {c : ℂ} (hc : c ∉ Mandelbrot) :
    c ∉ openApprox c (escapeLevel c hc) := by
  classical
  exact Nat.find_spec (exists_criticalValue_not_mem_openApprox hc)

lemma criticalValue_mem_openApprox_of_lt_escapeLevel {c : ℂ} (hc : c ∉ Mandelbrot)
    {n : ℕ} (hn : n < escapeLevel c hc) : c ∈ openApprox c n := by
  classical
  by_contra hmem
  exact (not_le_of_gt hn) (Nat.find_min' (exists_criticalValue_not_mem_openApprox hc) hmem)

structure DiskModel (U : Set ℂ) where
  isOpen : IsOpen U
  map : ℂ → ℂ
  homeomorph : U ≃ₜ Metric.ball (0 : ℂ) 1
  homeomorph_apply (z : U) : (homeomorph z : ℂ) = map z
  differentiableOn : DifferentiableOn ℂ map U
  deriv_ne (z : ℂ) : z ∈ U → deriv map z ≠ 0

lemma DiskModel.mapsTo {U : Set ℂ} (m : DiskModel U) :
    Set.MapsTo m.map U (Metric.ball (0 : ℂ) 1) := by
  intro z hz
  simpa only [← m.homeomorph_apply ⟨z, hz⟩] using (m.homeomorph ⟨z, hz⟩).2

lemma DiskModel.injOn {U : Set ℂ} (m : DiskModel U) : Set.InjOn m.map U := by
  intro z hz w hw hzw
  have hsub : (⟨z, hz⟩ : U) = ⟨w, hw⟩ := by
    apply m.homeomorph.injective
    apply Subtype.ext
    simpa only [m.homeomorph_apply] using hzw
  exact congrArg Subtype.val hsub

lemma DiskModel.surjOn {U : Set ℂ} (m : DiskModel U) :
    Metric.ball (0 : ℂ) 1 ⊆ m.map '' U := by
  intro w hw
  let z := m.homeomorph.symm ⟨w, hw⟩
  refine ⟨z, z.2, ?_⟩
  have hz := m.homeomorph_apply z
  simpa [z] using hz.symm

lemma DiskModel.isSimplyConnected {U : Set ℂ} (m : DiskModel U) : IsSimplyConnected U := by
  letI : ContractibleSpace (Metric.ball (0 : ℂ) 1) :=
    (convex_ball (0 : ℂ) 1).contractibleSpace ⟨0, Metric.mem_ball_self zero_lt_one⟩
  letI : SimplyConnectedSpace (Metric.ball (0 : ℂ) 1) :=
    SimplyConnectedSpace.ofContractible _
  exact m.homeomorph.toHomotopyEquiv.simplyConnectedSpace

noncomputable def initialDiskModel (c : ℂ) : DiskModel (openApprox c 0) := by
  let R : ℝ := Helpers.escapeRadius c
  have hR : 0 < R := escapeRadius_pos c
  let toFun : openApprox c 0 → Metric.ball (0 : ℂ) 1 := fun z =>
    ⟨z.1 / R, by
      rw [Metric.mem_ball, dist_zero_right, norm_div, Complex.norm_real,
        Real.norm_of_nonneg hR.le]
      apply (div_lt_one hR).2
      simpa only [openApprox, Function.iterate_zero_apply, Set.mem_preimage,
        Metric.mem_ball, dist_zero_right] using z.2⟩
  let invFun : Metric.ball (0 : ℂ) 1 → openApprox c 0 := fun w =>
    ⟨R * w.1, by
      have hw : ‖w.1‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using w.2
      simpa only [openApprox, Function.iterate_zero_apply, Set.mem_preimage,
        Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hR.le, R]
        using (by simpa only [mul_one] using mul_lt_mul_of_pos_left hw hR)⟩
  let e : openApprox c 0 ≃ Metric.ball (0 : ℂ) 1 :=
    { toFun := toFun
      invFun := invFun
      left_inv := fun z => by
        apply Subtype.ext
        change (R : ℂ) * (z.1 / R) = z.1
        field_simp [show (R : ℂ) ≠ 0 by exact_mod_cast hR.ne']
      right_inv := fun w => by
        apply Subtype.ext
        change (R : ℂ) * w.1 / R = w.1
        field_simp [show (R : ℂ) ≠ 0 by exact_mod_cast hR.ne'] }
  let h : openApprox c 0 ≃ₜ Metric.ball (0 : ℂ) 1 :=
    { e with
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact (continuous_subtype_val.div_const (R : ℂ))
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact continuous_const.mul continuous_subtype_val }
  exact
    { isOpen := isOpen_openApprox c 0
      map := fun z => z / R
      homeomorph := h
      homeomorph_apply := fun z => rfl
      differentiableOn := differentiableOn_id.div_const (R : ℂ)
      deriv_ne := fun z _ => by
        have hder : HasDerivAt (fun w : ℂ => w / (R : ℂ)) (1 / (R : ℂ)) z := by
          simpa only [id_eq] using (hasDerivAt_id z).div_const (R : ℂ)
        rw [hder.deriv]
        exact div_ne_zero one_ne_zero (by exact_mod_cast hR.ne') }

def discAut (a z : ℂ) : ℂ :=
  (z - a) / (1 - star a * z)

lemma discAut_denom_ne {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    1 - star a * z ≠ 0 := by
  intro hzero
  have hmul : star a * z = 1 := (sub_eq_zero.mp hzero).symm
  have hnorm : ‖a‖ * ‖z‖ = 1 := by
    calc
      ‖a‖ * ‖z‖ = ‖star a * z‖ := by simp
      _ = ‖(1 : ℂ)‖ := congrArg norm hmul
      _ = 1 := norm_one
  have hlt : ‖a‖ * ‖z‖ < 1 := by
    nlinarith [norm_nonneg a, norm_nonneg z,
      mul_nonneg (sub_nonneg.mpr ha.le) (norm_nonneg z)]
  linarith

lemma discAut_norm_identity (a z : ℂ) :
    ‖1 - star a * z‖ ^ 2 - ‖z - a‖ ^ 2 =
      (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_one,
    Complex.normSq_mul, one_mul]
  simp
  ring

lemma discAut_mem_ball {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    discAut a z ∈ Metric.ball (0 : ℂ) 1 := by
  have hpositive : 0 < (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
    apply mul_pos <;> nlinarith [norm_nonneg a, norm_nonneg z]
  have hsquares : ‖z - a‖ ^ 2 < ‖1 - star a * z‖ ^ 2 := by
    nlinarith [discAut_norm_identity a z]
  have hnorm : ‖z - a‖ < ‖1 - star a * z‖ :=
    (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquares
  rw [Metric.mem_ball, dist_zero_right, discAut, norm_div]
  exact (div_lt_one₀ (norm_pos_iff.mpr (discAut_denom_ne ha hz))).2 hnorm

lemma discAut_neg_apply_discAut {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    discAut (-a) (discAut a z) = z := by
  have hi : ‖discAut a z‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using discAut_mem_ball ha hz
  have hda := discAut_denom_ne ha hz
  have hdi := discAut_denom_ne (a := -a) (by simpa using ha) hi
  unfold discAut at hdi ⊢
  rw [star_neg] at hdi ⊢
  have hda' : 1 - z * star a ≠ 0 := by simpa only [mul_comm] using hda
  have hone : 1 - a * star a ≠ 0 := by
    intro hzero
    have hmul : a * star a = 1 := (sub_eq_zero.mp hzero).symm
    have hnorm := congrArg norm hmul
    simp only [norm_mul, norm_star, norm_one] at hnorm
    nlinarith [norm_nonneg a]
  ring_nf at hdi ⊢
  field_simp [hda', hdi, hone]
  ring_nf
  rw [inv_eq_one_div]
  field_simp [hone]
  ring

lemma differentiableOn_discAut {a : ℂ} (ha : ‖a‖ < 1) :
    DifferentiableOn ℂ (discAut a) (Metric.ball (0 : ℂ) 1) := by
  intro z hz
  have hz' : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  apply DifferentiableAt.differentiableWithinAt
  unfold discAut
  fun_prop (disch := exact discAut_denom_ne ha hz')

lemma deriv_discAut_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    deriv (discAut a) z ≠ 0 := by
  have hzmem : z ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  have himem := discAut_mem_ball ha hz
  have hf := (differentiableOn_discAut ha).differentiableAt
    (Metric.isOpen_ball.mem_nhds hzmem)
  have hg := (differentiableOn_discAut (a := -a) (by simpa using ha)).differentiableAt
    (Metric.isOpen_ball.mem_nhds himem)
  have hcomp := hg.hasDerivAt.comp z hf.hasDerivAt
  have heq : id =ᶠ[𝓝 z] discAut (-a) ∘ discAut a := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hzmem] with w hw
    exact (discAut_neg_apply_discAut ha (by
      simpa only [Metric.mem_ball, dist_zero_right, id_eq] using hw)).symm
  have hid := hcomp.congr_of_eventuallyEq heq
  have hder := hid.unique (hasDerivAt_id z)
  intro hzero
  rw [hzero, mul_zero] at hder
  exact zero_ne_one hder

noncomputable def discAutHomeomorph (a : ℂ) (ha : ‖a‖ < 1) :
    Metric.ball (0 : ℂ) 1 ≃ₜ Metric.ball (0 : ℂ) 1 :=
  { toFun := fun z => ⟨discAut a z, discAut_mem_ball ha (by
      simpa only [Metric.mem_ball, dist_zero_right] using z.2)⟩
    invFun := fun z => ⟨discAut (-a) z, discAut_mem_ball (by simpa using ha) (by
      simpa only [Metric.mem_ball, dist_zero_right] using z.2)⟩
    left_inv := fun z => by
      apply Subtype.ext
      exact discAut_neg_apply_discAut ha (by
        simpa only [Metric.mem_ball, dist_zero_right] using z.2)
    right_inv := fun z => by
      apply Subtype.ext
      simpa only [neg_neg] using discAut_neg_apply_discAut (a := -a) (by simpa using ha) (by
        simpa only [Metric.mem_ball, dist_zero_right] using z.2)
    continuous_toFun := by
      apply Continuous.subtype_mk
      change Continuous ((Metric.ball (0 : ℂ) 1).restrict (discAut a))
      exact continuousOn_iff_continuous_restrict.mp (differentiableOn_discAut ha).continuousOn
    continuous_invFun := by
      apply Continuous.subtype_mk
      change Continuous ((Metric.ball (0 : ℂ) 1).restrict (discAut (-a)))
      exact continuousOn_iff_continuous_restrict.mp
        (differentiableOn_discAut (by simpa using ha)).continuousOn }

noncomputable def DiskModel.normalize {U : Set ℂ} (m : DiskModel U) (c : ℂ) (hc : c ∈ U) :
    DiskModel U := by
  let a := m.map c
  have ha : ‖a‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right, a] using m.mapsTo hc
  let e := m.homeomorph.trans (discAutHomeomorph a ha)
  exact
    { isOpen := m.isOpen
      map := fun z => discAut a (m.map z)
      homeomorph := e
      homeomorph_apply := fun z => by
        change discAut a (m.homeomorph z) = discAut a (m.map z)
        rw [m.homeomorph_apply]
      differentiableOn := (differentiableOn_discAut ha).comp m.differentiableOn m.mapsTo
      deriv_ne := fun z hz => by
        have hm := m.differentiableOn.differentiableAt (m.isOpen.mem_nhds hz)
        have hma : ‖m.map z‖ < 1 := by
          simpa only [Metric.mem_ball, dist_zero_right] using m.mapsTo hz
        have hcomp := ((differentiableOn_discAut ha).differentiableAt
          (Metric.isOpen_ball.mem_nhds (m.mapsTo hz))).hasDerivAt.comp z hm.hasDerivAt
        change deriv (discAut a ∘ m.map) z ≠ 0
        rw [hcomp.deriv]
        exact mul_ne_zero (deriv_discAut_ne_zero ha hma) (m.deriv_ne z hz) }

lemma DiskModel.normalize_apply_base {U : Set ℂ} (m : DiskModel U) {c : ℂ} (hc : c ∈ U) :
    (m.normalize c hc).map c = 0 := by
  simp [DiskModel.normalize, discAut]

def normalizedSlope {U : Set ℂ} (m : DiskModel U) (c z : ℂ) : ℂ :=
  dslope m.map c z

lemma differentiableOn_normalizedSlope {U : Set ℂ} (m : DiskModel U) {c : ℂ} (hc : c ∈ U) :
    DifferentiableOn ℂ (normalizedSlope m c) U := by
  change DifferentiableOn ℂ (dslope m.map c) U
  exact (Complex.differentiableOn_dslope (m.isOpen.mem_nhds hc)).2 m.differentiableOn

lemma normalizedSlope_ne_zero {U : Set ℂ} (m : DiskModel U) {c z : ℂ}
    (hc : c ∈ U) (hz : z ∈ U) : normalizedSlope m c z ≠ 0 := by
  rcases eq_or_ne z c with rfl | hzc
  · simpa [normalizedSlope] using m.deriv_ne z hz
  · have hmap : m.map z ≠ m.map c := fun h => hzc (m.injOn hz hc h)
    rw [normalizedSlope, dslope_of_ne m.map hzc, slope_def_module]
    exact smul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hzc)) (sub_ne_zero.mpr hmap)

noncomputable def slopeRoot {U : Set ℂ} (m : DiskModel U) {c : ℂ} (hc : c ∈ U) : ℂ → ℂ := by
  let q := normalizedSlope m c
  have hq0 : 0 ∉ q '' U := by
    rintro ⟨z, hz, hzero⟩
    exact normalizedSlope_ne_zero m hc hz hzero
  exact Classical.choose (Complex.exists_continuousOn_pow_eq m.isSimplyConnected m.isOpen
    (differentiableOn_normalizedSlope m hc).continuousOn hq0 two_ne_zero)

lemma continuousOn_slopeRoot {U : Set ℂ} (m : DiskModel U) {c : ℂ} (hc : c ∈ U) :
    ContinuousOn (slopeRoot m hc) U := by
  let q := normalizedSlope m c
  have hq0 : 0 ∉ q '' U := by
    rintro ⟨z, hz, hzero⟩
    exact normalizedSlope_ne_zero m hc hz hzero
  exact (Classical.choose_spec (Complex.exists_continuousOn_pow_eq m.isSimplyConnected m.isOpen
    (differentiableOn_normalizedSlope m hc).continuousOn hq0 two_ne_zero)).1

lemma slopeRoot_sq {U : Set ℂ} (m : DiskModel U) {c : ℂ} (hc : c ∈ U) (z : ℂ) :
    slopeRoot m hc z ^ 2 = normalizedSlope m c z := by
  let q := normalizedSlope m c
  have hq0 : 0 ∉ q '' U := by
    rintro ⟨w, hw, hzero⟩
    exact normalizedSlope_ne_zero m hc hw hzero
  exact (Classical.choose_spec (Complex.exists_continuousOn_pow_eq m.isSimplyConnected m.isOpen
    (differentiableOn_normalizedSlope m hc).continuousOn hq0 two_ne_zero)).2 z

lemma slopeRoot_ne_zero {U : Set ℂ} (m : DiskModel U) {c z : ℂ}
    (hc : c ∈ U) (hz : z ∈ U) : slopeRoot m hc z ≠ 0 := by
  intro hzero
  apply normalizedSlope_ne_zero m hc hz
  rw [← slopeRoot_sq m hc z, hzero, zero_pow two_ne_zero]

lemma differentiableOn_slopeRoot {U : Set ℂ} (m : DiskModel U) {c : ℂ} (hc : c ∈ U) :
    DifferentiableOn ℂ (slopeRoot m hc) U := by
  intro z hz
  have hqdiff := (differentiableOn_normalizedSlope m hc).differentiableAt
    (m.isOpen.mem_nhds hz)
  have hscont := (continuousOn_slopeRoot m hc).continuousAt (m.isOpen.mem_nhds hz)
  have hpow : HasDerivAt (fun w : ℂ => w ^ 2) (2 * slopeRoot m hc z) (slopeRoot m hc z) := by
    simpa using hasDerivAt_pow 2 (slopeRoot m hc z)
  have hcomp : (fun w : ℂ => w ^ 2) ∘ slopeRoot m hc =ᶠ[𝓝 z]
      normalizedSlope m c :=
    Filter.Eventually.of_forall (slopeRoot_sq m hc)
  exact (hpow.of_comp_left hscont hqdiff.hasDerivAt
    (mul_ne_zero (by norm_num) (slopeRoot_ne_zero m hc hz)) hcomp).differentiableAt.differentiableWithinAt

def pullMap {U : Set ℂ} (m : DiskModel U) (c : ℂ) (hc : c ∈ U) (z : ℂ) : ℂ :=
  z * slopeRoot m hc (Tc c z)

lemma pullMap_sq {U : Set ℂ} (m : DiskModel U) {c : ℂ} (hc : c ∈ U)
    (hm0 : m.map c = 0) (z : ℂ) : pullMap m c hc z ^ 2 = m.map (Tc c z) := by
  have hds := sub_smul_dslope m.map c (Tc c z)
  change (Tc c z - c) * normalizedSlope m c (Tc c z) = m.map (Tc c z) - m.map c at hds
  rw [pullMap, mul_pow, slopeRoot_sq]
  calc
    z ^ 2 * normalizedSlope m c (Tc c z) =
        (Tc c z - c) * normalizedSlope m c (Tc c z) := by simp [Tc]
    _ = m.map (Tc c z) - m.map c := hds
    _ = m.map (Tc c z) := by rw [hm0, sub_zero]

lemma pullMap_mapsTo {U : Set ℂ} (m : DiskModel U) {c : ℂ} (hc : c ∈ U)
    (hm0 : m.map c = 0) :
    Set.MapsTo (pullMap m c hc) (Tc c ⁻¹' U) (Metric.ball (0 : ℂ) 1) := by
  intro z hz
  rw [Metric.mem_ball, dist_zero_right, ← pow_lt_one_iff_of_nonneg (norm_nonneg _) two_ne_zero,
    ← norm_pow, pullMap_sq m hc hm0]
  simpa only [Metric.mem_ball, dist_zero_right] using m.mapsTo hz

lemma pullMap_neg {U : Set ℂ} (m : DiskModel U) {c : ℂ} (hc : c ∈ U) (z : ℂ) :
    pullMap m c hc (-z) = -pullMap m c hc z := by
  simp [pullMap, Tc]

lemma pullMap_injOn {U : Set ℂ} (m : DiskModel U) {c : ℂ} (hc : c ∈ U)
    (hm0 : m.map c = 0) : Set.InjOn (pullMap m c hc) (Tc c ⁻¹' U) := by
  intro z hz w hw hzw
  have hmapsq : m.map (Tc c z) = m.map (Tc c w) := by
    rw [← pullMap_sq m hc hm0, ← pullMap_sq m hc hm0, hzw]
  have htc : Tc c z = Tc c w := m.injOn hz hw hmapsq
  have hsq : z ^ 2 = w ^ 2 := by
    simpa [Tc] using congrArg (· - c) htc
  rcases eq_or_eq_neg_of_sq_eq_sq z w hsq with h | h
  · exact h
  · have hzero : pullMap m c hc z = 0 := by
      have hwz : w = -z := by linear_combination h
      rw [hwz, pullMap_neg] at hzw
      linear_combination hzw / 2
    have hmz : m.map (Tc c z) = 0 := by
      rw [← pullMap_sq m hc hm0, hzero, zero_pow two_ne_zero]
    have htcc : Tc c z = c := m.injOn hz hc (hmz.trans hm0.symm)
    have hz0 : z = 0 := by
      have : z ^ 2 = 0 := by simpa [Tc] using congrArg (· - c) htcc
      exact (pow_eq_zero_iff two_ne_zero).mp this
    have hw0 : w = 0 := by
      have hwz : w = -z := by linear_combination h
      rw [hwz, hz0, neg_zero]
    exact hz0.trans hw0.symm

lemma pullMap_surjOn {U : Set ℂ} (m : DiskModel U) {c : ℂ} (hc : c ∈ U)
    (hm0 : m.map c = 0) :
    Metric.ball (0 : ℂ) 1 ⊆ pullMap m c hc '' (Tc c ⁻¹' U) := by
  intro u hu
  have hu' : ‖u‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hu
  have hu2 : u ^ 2 ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, norm_pow]
    nlinarith [norm_nonneg u, mul_nonneg (sub_nonneg.mpr hu'.le) (norm_nonneg u)]
  obtain ⟨y, hy, hmy⟩ := m.surjOn hu2
  obtain ⟨z, hzsq⟩ := IsAlgClosed.exists_pow_nat_eq (y - c) zero_lt_two
  have htcz : Tc c z = y := by simp [Tc, hzsq]
  have hz : z ∈ Tc c ⁻¹' U := by simpa only [Set.mem_preimage, htcz] using hy
  have hsq : pullMap m c hc z ^ 2 = u ^ 2 := by rw [pullMap_sq m hc hm0, htcz, hmy]
  rcases eq_or_eq_neg_of_sq_eq_sq (pullMap m c hc z) u hsq with h | h
  · exact ⟨z, hz, h⟩
  · refine ⟨-z, ?_, ?_⟩
    · simpa only [Set.mem_preimage, Tc, neg_sq] using hz
    · rw [pullMap_neg, h, neg_neg]

lemma differentiableOn_pullMap {U : Set ℂ} (m : DiskModel U) {c : ℂ} (hc : c ∈ U) :
    DifferentiableOn ℂ (pullMap m c hc) (Tc c ⁻¹' U) := by
  apply differentiableOn_id.mul
  apply (differentiableOn_slopeRoot m hc).comp
  · unfold Tc
    fun_prop
  · exact fun z hz => hz

lemma deriv_pullMap_ne_zero {U : Set ℂ} (m : DiskModel U) {c z : ℂ} (hc : c ∈ U)
    (hm0 : m.map c = 0) (hz : z ∈ Tc c ⁻¹' U) : deriv (pullMap m c hc) z ≠ 0 := by
  have hopen : IsOpen (Tc c ⁻¹' U) := m.isOpen.preimage (by unfold Tc; fun_prop)
  have hpull := (differentiableOn_pullMap m hc).differentiableAt (hopen.mem_nhds hz)
  rcases eq_or_ne z 0 with rfl | hz0
  · have hg := (differentiableOn_slopeRoot m hc).differentiableAt
      (m.isOpen.mem_nhds (by simpa [Tc] using hz))
    have htc : DifferentiableAt ℂ (Tc c) 0 := by unfold Tc; fun_prop
    have hg' : DifferentiableAt ℂ (slopeRoot m hc) (Tc c 0) := by simpa [Tc] using hg
    change deriv (id * (slopeRoot m hc ∘ Tc c)) 0 ≠ 0
    rw [deriv_mul differentiableAt_id (hg'.comp 0 htc), deriv_id]
    simpa [pullMap, Tc] using slopeRoot_ne_zero m hc
      (show c ∈ U from by simpa [Tc] using hz)
  · have htc : HasDerivAt (Tc c) (2 * z) z := by
      change HasDerivAt (fun w : ℂ => w ^ 2 + c) (2 * z) z
      simpa only [Tc, Nat.cast_ofNat, Nat.reduceSub, pow_one] using
        (hasDerivAt_pow 2 z).add_const c
    have hm := m.differentiableOn.differentiableAt (m.isOpen.mem_nhds hz)
    have hright := hm.hasDerivAt.comp z htc
    have hleft := hpull.hasDerivAt.pow 2
    have hevent : (fun w => m.map (Tc c w)) =ᶠ[𝓝 z]
        (fun w => pullMap m c hc w ^ 2) :=
      Filter.Eventually.of_forall fun w => (pullMap_sq m hc hm0 w).symm
    have hcoef := (hleft.congr_of_eventuallyEq hevent).unique hright
    intro hzero
    have hright_ne : deriv m.map (Tc c z) * (2 * z) ≠ 0 :=
      mul_ne_zero (m.deriv_ne _ hz) (mul_ne_zero (by norm_num) hz0)
    rw [hzero, mul_zero] at hcoef
    exact hright_ne hcoef.symm

noncomputable def DiskModel.pullback {U : Set ℂ} (m : DiskModel U) {c : ℂ} (hc : c ∈ U)
    (hm0 : m.map c = 0) : DiskModel (Tc c ⁻¹' U) := by
  let V := Tc c ⁻¹' U
  let f := pullMap m c hc
  have hVopen : IsOpen V := m.isOpen.preimage (by unfold Tc; fun_prop)
  have hmaps : Set.MapsTo f V (Metric.ball (0 : ℂ) 1) := pullMap_mapsTo m hc hm0
  let toFun : V → Metric.ball (0 : ℂ) 1 := fun z => ⟨f z, hmaps z.2⟩
  have htoFun_bij : Function.Bijective toFun := by
    constructor
    · intro z w hzw
      apply Subtype.ext
      apply pullMap_injOn m hc hm0 z.2 w.2
      exact congrArg Subtype.val hzw
    · rintro ⟨w, hw⟩
      obtain ⟨z, hz, hzw⟩ := pullMap_surjOn m hc hm0 hw
      exact ⟨⟨z, hz⟩, Subtype.ext hzw⟩
  let e : V ≃ Metric.ball (0 : ℂ) 1 := Equiv.ofBijective toFun htoFun_bij
  have hcont : Continuous e := by
    change Continuous toFun
    apply Continuous.subtype_mk
    change Continuous (V.restrict f)
    exact continuousOn_iff_continuous_restrict.mp (differentiableOn_pullMap m hc).continuousOn
  have hVconn : IsConnected V := by
    exact Connected.isConnected_preimage_tc m.isSimplyConnected.isPathConnected.isConnected hc
  have hfopen : ∀ s ⊆ V, IsOpen s → IsOpen (f '' s) := by
    have hanalytic : AnalyticOnNhd ℂ f V := (differentiableOn_pullMap m hc).analyticOnNhd hVopen
    rcases hanalytic.is_constant_or_isOpen hVconn.isPreconnected with hconst | hopen
    · exfalso
      obtain ⟨a, ha⟩ := hconst
      obtain ⟨z, hz, hz0⟩ := pullMap_surjOn m hc hm0
        (show (0 : ℂ) ∈ Metric.ball 0 1 by simp)
      obtain ⟨w, hw, hw1⟩ := pullMap_surjOn m hc hm0
        (show (1 / 2 : ℂ) ∈ Metric.ball 0 1 by norm_num [Metric.mem_ball, dist_zero_right])
      have ha0 : a = 0 := (ha z hz).symm.trans hz0
      have ha1 : a = 1 / 2 := (ha w hw).symm.trans hw1
      norm_num [ha0] at ha1
    · exact hopen
  have hopen : IsOpenMap e := by
    change IsOpenMap toFun
    apply IsOpenMap.subtype_mk
    intro A hA
    have hAopen : IsOpen (Subtype.val '' A) := hVopen.isOpenMap_subtype_val A hA
    have hAsub : Subtype.val '' A ⊆ V := by
      rintro _ ⟨z, -, rfl⟩
      exact z.2
    simpa only [Set.image_image, Set.restrict_apply] using hfopen _ hAsub hAopen
  let h : V ≃ₜ Metric.ball (0 : ℂ) 1 := e.toHomeomorphOfContinuousOpen hcont hopen
  exact
    { isOpen := hVopen
      map := f
      homeomorph := h
      homeomorph_apply := fun z => rfl
      differentiableOn := differentiableOn_pullMap m hc
      deriv_ne := fun z hz => deriv_pullMap_ne_zero m hc hm0 hz }

noncomputable def diskModelBeforeEscape (c : ℂ) (hc : c ∉ Mandelbrot) :
    (n : ℕ) → n ≤ escapeLevel c hc → DiskModel (openApprox c n)
  | 0, _ => initialDiskModel c
  | n + 1, hn => by
      have hnle : n ≤ escapeLevel c hc := Nat.le_of_succ_le hn
      have hcrit : c ∈ openApprox c n :=
        criticalValue_mem_openApprox_of_lt_escapeLevel hc (Nat.lt_of_succ_le hn)
      let m := diskModelBeforeEscape c hc n hnle
      let m0 := m.normalize c hcrit
      rw [openApprox_succ]
      exact m0.pullback hcrit (m.normalize_apply_base hcrit)

noncomputable def escapeDiskModel (c : ℂ) (hc : c ∉ Mandelbrot) :
    DiskModel (openApprox c (escapeLevel c hc)) :=
  diskModelBeforeEscape c hc (escapeLevel c hc) le_rfl

noncomputable def DiskModel.invMap {U : Set ℂ} (m : DiskModel U) (z : ℂ) : ℂ :=
  by
    classical
    exact if hz : z ∈ Metric.ball (0 : ℂ) 1 then (m.homeomorph.symm ⟨z, hz⟩ : U) else 0

lemma DiskModel.invMap_mem {U : Set ℂ} (m : DiskModel U) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) : m.invMap z ∈ U := by
  simp [DiskModel.invMap, hz]

lemma DiskModel.map_invMap {U : Set ℂ} (m : DiskModel U) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) : m.map (m.invMap z) = z := by
  have happ := m.homeomorph_apply (m.homeomorph.symm ⟨z, hz⟩)
  simpa [DiskModel.invMap, hz] using happ.symm

lemma DiskModel.invMap_map {U : Set ℂ} (m : DiskModel U) {z : ℂ} (hz : z ∈ U) :
    m.invMap (m.map z) = z := by
  have hmz := m.mapsTo hz
  rw [DiskModel.invMap, dif_pos hmz]
  have htarget : (⟨m.map z, hmz⟩ : Metric.ball (0 : ℂ) 1) = m.homeomorph ⟨z, hz⟩ := by
    apply Subtype.ext
    exact (m.homeomorph_apply ⟨z, hz⟩).symm
  rw [htarget, m.homeomorph.symm_apply_apply]

lemma DiskModel.continuousOn_invMap {U : Set ℂ} (m : DiskModel U) :
    ContinuousOn m.invMap (Metric.ball (0 : ℂ) 1) := by
  rw [continuousOn_iff_continuous_restrict]
  have hcont : Continuous fun z : Metric.ball (0 : ℂ) 1 =>
      ((m.homeomorph.symm z : U) : ℂ) :=
    continuous_subtype_val.comp m.homeomorph.symm.continuous
  convert hcont using 1
  funext z
  simp [DiskModel.invMap, z.2]

lemma DiskModel.differentiableOn_invMap {U : Set ℂ} (m : DiskModel U) :
    DifferentiableOn ℂ m.invMap (Metric.ball (0 : ℂ) 1) := by
  intro z hz
  have hcont := m.continuousOn_invMap.continuousAt (Metric.isOpen_ball.mem_nhds hz)
  have hmem := m.invMap_mem hz
  have hdiff := m.differentiableOn.differentiableAt (m.isOpen.mem_nhds hmem)
  have hevent : ∀ᶠ w in 𝓝 z, m.map (m.invMap w) = w := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
    exact m.map_invMap hw
  have hinv := hdiff.hasDerivAt.of_local_left_inverse hcont (m.deriv_ne _ hmem) hevent
  exact hinv.differentiableAt.differentiableWithinAt

noncomputable def branchRoot {U : Set ℂ} (m : DiskModel U) (c : ℂ) (hc : c ∉ U) : ℂ → ℂ := by
  have hzero : 0 ∉ (fun z : ℂ => z - c) '' U := by
    rintro ⟨z, hz, hzc⟩
    exact hc ((sub_eq_zero.mp hzc) ▸ hz)
  exact Classical.choose (Complex.exists_continuousOn_pow_eq m.isSimplyConnected m.isOpen
    (continuousOn_id.sub continuousOn_const) hzero two_ne_zero)

lemma continuousOn_branchRoot {U : Set ℂ} (m : DiskModel U) (c : ℂ) (hc : c ∉ U) :
    ContinuousOn (branchRoot m c hc) U := by
  have hzero : 0 ∉ (fun z : ℂ => z - c) '' U := by
    rintro ⟨z, hz, hzc⟩
    exact hc ((sub_eq_zero.mp hzc) ▸ hz)
  exact (Classical.choose_spec (Complex.exists_continuousOn_pow_eq m.isSimplyConnected m.isOpen
    (continuousOn_id.sub continuousOn_const) hzero two_ne_zero)).1

lemma branchRoot_sq {U : Set ℂ} (m : DiskModel U) (c : ℂ) (hc : c ∉ U) (z : ℂ) :
    branchRoot m c hc z ^ 2 = z - c := by
  have hzero : 0 ∉ (fun z : ℂ => z - c) '' U := by
    rintro ⟨w, hw, hwc⟩
    exact hc ((sub_eq_zero.mp hwc) ▸ hw)
  exact (Classical.choose_spec (Complex.exists_continuousOn_pow_eq m.isSimplyConnected m.isOpen
    (continuousOn_id.sub continuousOn_const) hzero two_ne_zero)).2 z

lemma branchRoot_ne_zero {U : Set ℂ} (m : DiskModel U) {c z : ℂ} (hc : c ∉ U) (hz : z ∈ U) :
    branchRoot m c hc z ≠ 0 := by
  intro hzero
  apply hc
  have hzc : z = c := sub_eq_zero.mp (by
    rw [← branchRoot_sq m c hc z, hzero, zero_pow two_ne_zero])
  exact hzc ▸ hz

lemma differentiableOn_branchRoot {U : Set ℂ} (m : DiskModel U) (c : ℂ) (hc : c ∉ U) :
    DifferentiableOn ℂ (branchRoot m c hc) U := by
  intro z hz
  have hscont := (continuousOn_branchRoot m c hc).continuousAt (m.isOpen.mem_nhds hz)
  have hpow : HasDerivAt (fun w : ℂ => w ^ 2) (2 * branchRoot m c hc z)
      (branchRoot m c hc z) := by
    simpa using hasDerivAt_pow 2 (branchRoot m c hc z)
  have hsub : HasDerivAt (fun w : ℂ => w - c) 1 z := by simpa using (hasDerivAt_id z).sub_const c
  have hcomp : (fun w : ℂ => w ^ 2) ∘ branchRoot m c hc =ᶠ[𝓝 z] fun w => w - c :=
    Filter.Eventually.of_forall (branchRoot_sq m c hc)
  have hdiff := hpow.of_comp_left hscont hsub
    (mul_ne_zero (by norm_num) (branchRoot_ne_zero m hc hz)) hcomp
  exact hdiff.differentiableAt.differentiableWithinAt

def inverseBranch {U : Set ℂ} (m : DiskModel U) (c : ℂ) (hc : c ∉ U)
    (b : Bool) (z : ℂ) : ℂ :=
  if b then -branchRoot m c hc z else branchRoot m c hc z

lemma inverseBranch_sq {U : Set ℂ} (m : DiskModel U) (c : ℂ) (hc : c ∉ U)
    (b : Bool) (z : ℂ) : inverseBranch m c hc b z ^ 2 = z - c := by
  cases b <;> simp [inverseBranch, branchRoot_sq]

lemma tc_inverseBranch {U : Set ℂ} (m : DiskModel U) (c : ℂ) (hc : c ∉ U)
    (b : Bool) (z : ℂ) : Tc c (inverseBranch m c hc b z) = z := by
  simp [Tc, inverseBranch_sq]

lemma differentiableOn_inverseBranch {U : Set ℂ} (m : DiskModel U) (c : ℂ) (hc : c ∉ U)
    (b : Bool) : DifferentiableOn ℂ (inverseBranch m c hc b) U := by
  cases b
  · change DifferentiableOn ℂ (branchRoot m c hc) U
    exact differentiableOn_branchRoot m c hc
  · change DifferentiableOn ℂ (fun z => -branchRoot m c hc z) U
    exact (differentiableOn_branchRoot m c hc).neg

lemma inverseBranch_mapsTo_preimage {U : Set ℂ} (m : DiskModel U) (c : ℂ) (hc : c ∉ U)
    (b : Bool) : Set.MapsTo (inverseBranch m c hc b) U (Tc c ⁻¹' U) := by
  intro z hz
  simpa only [Set.mem_preimage, tc_inverseBranch] using hz

def conjugateBranch {U : Set ℂ} (m : DiskModel U) (c : ℂ) (hc : c ∉ U)
    (_hpre : Tc c ⁻¹' U ⊆ U) (b : Bool) (z : ℂ) : ℂ :=
  m.map (inverseBranch m c hc b (m.invMap z))

lemma differentiableOn_conjugateBranch {U : Set ℂ} (m : DiskModel U) (c : ℂ) (hc : c ∉ U)
    (hpre : Tc c ⁻¹' U ⊆ U) (b : Bool) :
    DifferentiableOn ℂ (conjugateBranch m c hc hpre b) (Metric.ball (0 : ℂ) 1) := by
  apply m.differentiableOn.comp
  · apply (differentiableOn_inverseBranch m c hc b).comp m.differentiableOn_invMap
    exact fun z hz => m.invMap_mem hz
  · intro z hz
    exact hpre (inverseBranch_mapsTo_preimage m c hc b (m.invMap_mem hz))

lemma filledApprox_subset_openApprox_prev (c : ℂ) (n : ℕ) :
    Connected.filledApprox c (n + 1) ⊆ openApprox c n := by
  intro z hz
  simp only [Connected.filledApprox, openApprox, Set.mem_preimage, Metric.mem_closedBall,
    Metric.mem_ball, dist_zero_right] at hz ⊢
  by_contra! hn
  have hnext := norm_tc_gt_escapeRadius_of_ge (c := c) (z := (Tc c)^[n] z) hn
  exact (not_lt_of_ge hz) (by simpa only [Function.iterate_succ_apply'] using hnext)

lemma openApprox_subset_filledApprox (c : ℂ) (n : ℕ) :
    openApprox c n ⊆ Connected.filledApprox c n := by
  intro z hz
  simp only [openApprox, Set.mem_preimage, Metric.mem_ball, dist_zero_right] at hz
  simpa only [Connected.filledApprox, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    using hz.le

lemma filledApprox_subset_zero (c : ℂ) :
    ∀ n : ℕ, Connected.filledApprox c n ⊆ Connected.filledApprox c 0 := by
  intro n
  induction n with
  | zero => exact Set.Subset.rfl
  | succ n =>
      exact (Connected.filledApprox_succ_subset c n).trans ‹_›

lemma isCompact_filledApprox (c : ℂ) (n : ℕ) : IsCompact (Connected.filledApprox c n) := by
  exact (Connected.isCompact_filledApprox_zero c).of_isClosed_subset
    (Connected.isClosed_filledApprox c n) (filledApprox_subset_zero c n)

lemma filledJulia_subset_filledApprox (c : ℂ) (n : ℕ) :
    FilledJulia c ⊆ Connected.filledApprox c n := by
  intro z hz
  simpa only [Connected.filledApprox, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    using (Helpers.mem_filledJulia_iff_forall_norm_le_escapeRadius c z).1 hz n

lemma filledApprox_nonempty (c : ℂ) (n : ℕ) : (Connected.filledApprox c n).Nonempty :=
  (Helpers.filledJulia_nonempty c).mono (filledJulia_subset_filledApprox c n)

lemma exists_strict_norm_bound {U A : Set ℂ} (m : DiskModel U) (hA : IsCompact A)
    (hAne : A.Nonempty) (hAU : A ⊆ U) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ z ∈ A, ‖m.map z‖ ≤ q := by
  have hcont : ContinuousOn (fun z => ‖m.map z‖) A :=
    m.differentiableOn.continuousOn.norm.mono hAU
  obtain ⟨z, hz, hzmax⟩ := hA.exists_isMaxOn hAne hcont
  refine ⟨‖m.map z‖, norm_nonneg _, ?_, fun w hw => hzmax hw⟩
  simpa only [Metric.mem_ball, dist_zero_right] using m.mapsTo (hAU hz)

def escapeU (c : ℂ) (hc : c ∉ Mandelbrot) : Set ℂ :=
  openApprox c (escapeLevel c hc)

lemma criticalValue_not_mem_escapeU {c : ℂ} (hc : c ∉ Mandelbrot) : c ∉ escapeU c hc :=
  criticalValue_not_mem_openApprox_escapeLevel hc

lemma preimage_escapeU_subset {c : ℂ} (hc : c ∉ Mandelbrot) :
    Tc c ⁻¹' escapeU c hc ⊆ escapeU c hc := by
  rw [escapeU, ← openApprox_succ]
  exact openApprox_succ_subset c (escapeLevel c hc)

lemma exists_escape_branch_bound {c : ℂ} (hc : c ∉ Mandelbrot) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ b : Bool, ∀ z ∈ Metric.ball (0 : ℂ) 1,
      ‖conjugateBranch (escapeDiskModel c hc) c (criticalValue_not_mem_escapeU hc)
        (preimage_escapeU_subset hc) b z‖ ≤ q := by
  let n := escapeLevel c hc
  let U := escapeU c hc
  let m : DiskModel U := escapeDiskModel c hc
  let A := Connected.filledApprox c (n + 1)
  have hAU : A ⊆ U := filledApprox_subset_openApprox_prev c n
  obtain ⟨q, hq0, hq1, hq⟩ :=
    exists_strict_norm_bound m (isCompact_filledApprox c (n + 1))
      (filledApprox_nonempty c (n + 1)) hAU
  refine ⟨q, hq0, hq1, fun b z hz => ?_⟩
  apply hq
  apply openApprox_subset_filledApprox c (n + 1)
  change inverseBranch m c (criticalValue_not_mem_escapeU hc) b (m.invMap z) ∈
    Tc c ⁻¹' U
  exact inverseBranch_mapsTo_preimage m c (criticalValue_not_mem_escapeU hc) b (m.invMap_mem hz)

lemma discAut_self (z : ℂ) : discAut z z = 0 := by
  simp [discAut]

lemma discAut_neg_zero (z : ℂ) : discAut (-z) 0 = z := by
  simp [discAut]

def rho (z w : ℂ) : ℝ :=
  ‖discAut w z‖

lemma rho_nonneg (z w : ℂ) : 0 ≤ rho z w := norm_nonneg _

lemma rho_lt_one {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) : rho z w < 1 := by
  simpa only [rho, Metric.mem_ball, dist_zero_right] using discAut_mem_ball hw hz

lemma rho_eq_zero_iff {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    rho z w = 0 ↔ z = w := by
  rw [rho, norm_eq_zero, discAut, div_eq_zero_iff]
  simp only [sub_eq_zero]
  exact or_iff_left (fun h => discAut_denom_ne hw hz (sub_eq_zero.mpr h))

lemma schwarzPick {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
    (hmap : Set.MapsTo f (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1))
    {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) : rho (f z) (f w) ≤ rho z w := by
  have hzmem : z ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hwmem : w ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hw
  have hfw : ‖f w‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hmap hwmem
  let F : ℂ → ℂ := fun x => discAut (f w) (f (discAut (-w) x))
  have hdiff : DifferentiableOn ℂ F (Metric.ball (0 : ℂ) 1) := by
    apply (differentiableOn_discAut hfw).comp
    · apply hd.comp (differentiableOn_discAut (by simpa using hw))
      intro x hx
      exact discAut_mem_ball (by simpa using hw) (by
        simpa only [Metric.mem_ball, dist_zero_right] using hx)
    · intro x hx
      apply hmap
      exact discAut_mem_ball (by simpa using hw) (by
        simpa only [Metric.mem_ball, dist_zero_right] using hx)
  have hmaps : Set.MapsTo F (Metric.ball (0 : ℂ) 1) (Metric.closedBall 0 1) := by
    intro x hx
    have hinner := discAut_mem_ball (a := -w) (by simpa using hw) (by
      simpa only [Metric.mem_ball, dist_zero_right] using hx)
    have hfx := hmap hinner
    have hout := discAut_mem_ball hfw (by
      simpa only [Metric.mem_ball, dist_zero_right] using hfx)
    have hout' : ‖discAut (f w) (f (discAut (-w) x))‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hout
    simpa only [F, Metric.mem_closedBall, dist_zero_right] using hout'.le
  have hF0 : F 0 = 0 := by simp [F, discAut_neg_zero, discAut_self]
  have hxmem := discAut_mem_ball hw hz
  have hschwarz := Complex.norm_le_norm_of_mapsTo_ball hdiff hmaps hF0 (by
    simpa only [Metric.mem_ball, dist_zero_right] using hxmem)
  simpa only [F, rho, discAut_neg_apply_discAut hw hz] using hschwarz

lemma radial_denominator_bound {r : ℝ} {t : ℂ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ht : ‖t‖ ≤ 1) :
    (1 + r ^ 2) * ‖1 - t‖ ≤ 2 * ‖1 - (r : ℂ) ^ 2 * t‖ := by
  rw [← sq_le_sq₀ (mul_nonneg (by positivity) (norm_nonneg _))
    (mul_nonneg (by norm_num) (norm_nonneg _))]
  simp only [mul_pow, Complex.sq_norm, Complex.normSq_sub, Complex.normSq_one,
    Complex.normSq_mul]
  rw [← Complex.ofReal_pow, ← Complex.sq_norm]
  simp only [Complex.normSq_ofReal, map_mul, Complex.conj_ofReal, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, one_mul,
    zero_mul, sub_zero]
  let s := ‖t‖
  have hs0 : 0 ≤ s := norm_nonneg t
  have hs1 : s ≤ 1 := ht
  have htre : -s ≤ t.re := by
    simpa [s] using neg_le_of_abs_le (Complex.abs_re_le_norm t)
  have hr2 : 0 ≤ 1 - r ^ 2 := by nlinarith
  have hfactor : 0 ≤ 3 + r ^ 2 + (1 + 3 * r ^ 2) * s := by nlinarith [sq_nonneg r]
  have hbase : 0 ≤ (1 - s) * (3 + r ^ 2 + (1 + 3 * r ^ 2) * s) :=
    mul_nonneg (sub_nonneg.mpr hs1) hfactor
  have hre : 0 ≤ 2 * (1 - r ^ 2) * (t.re + s) :=
    mul_nonneg (mul_nonneg (by norm_num) hr2) (by linarith)
  nlinarith [mul_nonneg hr2 (add_nonneg hbase hre)]

lemma rho_radial_le {r : ℝ} {z w : ℂ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    rho ((r : ℂ) * z) ((r : ℂ) * w) ≤ (2 * r / (1 + r ^ 2)) * rho z w := by
  rcases eq_or_ne r 0 with rfl | hrne
  · simp [rho, discAut]
  have hrpos' : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrne)
  have hstar : star (r : ℂ) = (r : ℂ) := by
    rw [RCLike.star_def, Complex.conj_ofReal]
  have hrz : ‖(r : ℂ) * z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0]
    nlinarith [norm_nonneg z, mul_nonneg (sub_nonneg.mpr hr1.le) (norm_nonneg z)]
  have hrw : ‖(r : ℂ) * w‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0]
    nlinarith [norm_nonneg w, mul_nonneg (sub_nonneg.mpr hr1.le) (norm_nonneg w)]
  have hd : 0 < ‖1 - star w * z‖ := norm_pos_iff.mpr (discAut_denom_ne hw hz)
  have hdr : 0 < ‖1 - (r : ℂ) ^ 2 * (star w * z)‖ := by
    have hden := discAut_denom_ne hrw hrz
    apply norm_pos_iff.mpr
    intro hzero
    apply hden
    rw [star_mul, hstar]
    linear_combination hzero
  have ht : ‖star w * z‖ ≤ 1 := by
    rw [norm_mul, norm_star]
    nlinarith [norm_nonneg w, norm_nonneg z,
      mul_nonneg (sub_nonneg.mpr hw.le) (norm_nonneg z)]
  have hden := radial_denominator_bound hr0 hr1 ht
  have hDpos : 0 < ((1 + r ^ 2) * ‖1 - star w * z‖) / 2 := by positivity
  have hDle : ((1 + r ^ 2) * ‖1 - star w * z‖) / 2 ≤
      ‖1 - (r : ℂ) ^ 2 * (star w * z)‖ := by linarith
  have hnum : 0 ≤ r * ‖z - w‖ := mul_nonneg hr0 (norm_nonneg _)
  have hformula_left : rho ((r : ℂ) * z) ((r : ℂ) * w) =
      r * ‖z - w‖ / ‖1 - (r : ℂ) ^ 2 * (star w * z)‖ := by
    rw [rho, discAut, norm_div, norm_sub_rev]
    congr 1
    · calc
        ‖(r : ℂ) * w - (r : ℂ) * z‖ = ‖(r : ℂ) * (w - z)‖ := by congr 1; ring
        _ = r * ‖z - w‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0, norm_sub_rev]
    · congr 1
      rw [star_mul, hstar]
      ring
  have hformula_right : (2 * r / (1 + r ^ 2)) * rho z w =
      r * ‖z - w‖ / (((1 + r ^ 2) * ‖1 - star w * z‖) / 2) := by
    rw [rho, discAut, norm_div]
    field_simp [hd.ne', show 1 + r ^ 2 ≠ 0 by positivity]
  rw [hformula_left, hformula_right]
  exact div_le_div_of_nonneg_left hnum hDpos hDle

lemma exists_rho_contraction_of_norm_bound {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1)) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hbound : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖f z‖ ≤ q) :
    ∃ Q : ℝ, 0 ≤ Q ∧ Q < 1 ∧ ∀ z ∈ Metric.ball (0 : ℂ) 1,
      ∀ w ∈ Metric.ball (0 : ℂ) 1, rho (f z) (f w) ≤ Q * rho z w := by
  let r := (q + 1) / 2
  have hr0 : 0 < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hqr : q < r := by dsimp [r]; linarith
  let k : ℂ → ℂ := fun z => f z / (r : ℂ)
  have hkdiff : DifferentiableOn ℂ k (Metric.ball (0 : ℂ) 1) := hd.div_const (r : ℂ)
  have hkmaps : Set.MapsTo k (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right]
    change ‖f z / (r : ℂ)‖ < 1
    rw [norm_div, Complex.norm_real,
      Real.norm_of_nonneg hr0.le]
    exact (div_lt_one hr0).2 ((hbound z hz).trans_lt hqr)
  let Q := 2 * r / (1 + r ^ 2)
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hQ1 : Q < 1 := by
    change 2 * r / (1 + r ^ 2) < 1
    rw [div_lt_one₀ (by positivity : 0 < 1 + r ^ 2)]
    nlinarith [sq_pos_of_pos (sub_pos.mpr hr1)]
  refine ⟨Q, hQ0, hQ1, fun z hz w hw => ?_⟩
  have hz' : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hw' : ‖w‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hw
  have hkz : ‖k z‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hkmaps hz
  have hkw : ‖k w‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hkmaps hw
  have hfz : f z = (r : ℂ) * k z := by
    dsimp [k]
    field_simp [show (r : ℂ) ≠ 0 by exact_mod_cast hr0.ne']
  have hfw : f w = (r : ℂ) * k w := by
    dsimp [k]
    field_simp [show (r : ℂ) ≠ 0 by exact_mod_cast hr0.ne']
  calc
    rho (f z) (f w) = rho ((r : ℂ) * k z) ((r : ℂ) * k w) := by rw [hfz, hfw]
    _ ≤ Q * rho (k z) (k w) := rho_radial_le hr0.le hr1 hkz hkw
    _ ≤ Q * rho z w := mul_le_mul_of_nonneg_left (schwarzPick hkdiff hkmaps hz' hw') hQ0

lemma exists_escape_rho_contraction {c : ℂ} (hc : c ∉ Mandelbrot) :
    ∃ Q : ℝ, 0 ≤ Q ∧ Q < 1 ∧ ∀ b : Bool, ∀ z ∈ Metric.ball (0 : ℂ) 1,
      ∀ w ∈ Metric.ball (0 : ℂ) 1,
      rho (conjugateBranch (escapeDiskModel c hc) c (criticalValue_not_mem_escapeU hc)
          (preimage_escapeU_subset hc) b z)
        (conjugateBranch (escapeDiskModel c hc) c (criticalValue_not_mem_escapeU hc)
          (preimage_escapeU_subset hc) b w) ≤ Q * rho z w := by
  obtain ⟨q, hq0, hq1, hq⟩ := exists_escape_branch_bound hc
  let m := escapeDiskModel c hc
  let hcn := criticalValue_not_mem_escapeU hc
  let hpre := preimage_escapeU_subset hc
  obtain ⟨Qf, hQf0, hQf1, hQf⟩ := exists_rho_contraction_of_norm_bound
    (differentiableOn_conjugateBranch m c hcn hpre false) hq0 hq1 (hq false)
  obtain ⟨Qt, _hQt0, hQt1, hQt⟩ := exists_rho_contraction_of_norm_bound
    (differentiableOn_conjugateBranch m c hcn hpre true) hq0 hq1 (hq true)
  let Q := max Qf Qt
  refine ⟨Q, hQf0.trans (le_max_left Qf Qt), (max_lt_iff).2 ⟨hQf1, hQt1⟩, fun b => ?_⟩
  cases b
  · intro z hz w hw
    exact (hQf z hz w hw).trans
      (mul_le_mul_of_nonneg_right (le_max_left Qf Qt) (rho_nonneg z w))
  · intro z hz w hw
    exact (hQt z hz w hw).trans
      (mul_le_mul_of_nonneg_right (le_max_right Qf Qt) (rho_nonneg z w))

lemma filledJulia_subset_escapeU (c : ℂ) (hc : c ∉ Mandelbrot) :
    FilledJulia c ⊆ escapeU c hc :=
  filledJulia_subset_openApprox c (escapeLevel c hc)

noncomputable def juliaInverse (c : ℂ) (hc : c ∉ Mandelbrot) (b : Bool) :
    FilledJulia c → FilledJulia c := fun y =>
  let m := escapeDiskModel c hc
  let hcn := criticalValue_not_mem_escapeU hc
  ⟨inverseBranch m c hcn b y.1, (Helpers.tc_mem_filledJulia_iff c _).1 (by
    rw [tc_inverseBranch]
    exact y.2)⟩

lemma tcOn_juliaInverse (c : ℂ) (hc : c ∉ Mandelbrot) (b : Bool) (y : FilledJulia c) :
    Helpers.tcOnFilledJulia c (juliaInverse c hc b y) = y := by
  apply Subtype.ext
  exact tc_inverseBranch (escapeDiskModel c hc) c (criticalValue_not_mem_escapeU hc) b y

lemma continuous_juliaInverse (c : ℂ) (hc : c ∉ Mandelbrot) (b : Bool) :
    Continuous (juliaInverse c hc b) := by
  apply Continuous.subtype_mk
  rw [continuous_iff_continuousAt]
  intro y
  have hyU : y.1 ∈ escapeU c hc := filledJulia_subset_escapeU c hc y.2
  have hdiff := (differentiableOn_inverseBranch (escapeDiskModel c hc) c
    (criticalValue_not_mem_escapeU hc) b).differentiableAt
      ((escapeDiskModel c hc).isOpen.mem_nhds hyU)
  exact hdiff.continuousAt.comp continuous_subtype_val.continuousAt

def juliaBranchSet (c : ℂ) (hc : c ∉ Mandelbrot) (b : Bool) : Set (FilledJulia c) :=
  Set.range (juliaInverse c hc b)

lemma isClosed_juliaBranchSet (c : ℂ) (hc : c ∉ Mandelbrot) (b : Bool) :
    IsClosed (juliaBranchSet c hc b) := by
  simpa [juliaBranchSet] using
    (isCompact_univ.image (continuous_juliaInverse c hc b)).isClosed

lemma juliaBranchSet_disjoint (c : ℂ) (hc : c ∉ Mandelbrot) :
    Disjoint (juliaBranchSet c hc false) (juliaBranchSet c hc true) := by
  rw [Set.disjoint_left]
  rintro x ⟨y, rfl⟩ ⟨z, hz⟩
  have hyz : y = z := by
    rw [← tcOn_juliaInverse c hc false y, ← tcOn_juliaInverse c hc true z, hz]
  subst z
  have hval := congrArg Subtype.val hz
  change -branchRoot (escapeDiskModel c hc) c (criticalValue_not_mem_escapeU hc) y =
    branchRoot (escapeDiskModel c hc) c (criticalValue_not_mem_escapeU hc) y at hval
  have hroot0 : branchRoot (escapeDiskModel c hc) c
      (criticalValue_not_mem_escapeU hc) y = 0 := by
    linear_combination -hval / 2
  exact branchRoot_ne_zero (escapeDiskModel c hc) (criticalValue_not_mem_escapeU hc)
    (filledJulia_subset_escapeU c hc y.2) hroot0

lemma juliaBranchSet_cover (c : ℂ) (hc : c ∉ Mandelbrot) :
    juliaBranchSet c hc false ∪ juliaBranchSet c hc true = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  let y := Helpers.tcOnFilledJulia c x
  have hsq : x.1 ^ 2 = branchRoot (escapeDiskModel c hc) c
      (criticalValue_not_mem_escapeU hc) y ^ 2 := by
    rw [branchRoot_sq]
    simp [y, Helpers.tcOnFilledJulia, Tc]
  rcases eq_or_eq_neg_of_sq_eq_sq x.1
    (branchRoot (escapeDiskModel c hc) c (criticalValue_not_mem_escapeU hc) y) hsq with h | h
  · left
    exact ⟨y, Subtype.ext h.symm⟩
  · right
    exact ⟨y, Subtype.ext h.symm⟩

lemma isClopen_juliaBranchSet (c : ℂ) (hc : c ∉ Mandelbrot) (b : Bool) :
    IsClopen (juliaBranchSet c hc b) := by
  refine ⟨isClosed_juliaBranchSet c hc b, ?_⟩
  rw [← isClosed_compl_iff]
  cases b
  · have hcover := juliaBranchSet_cover c hc
    have hdisj := juliaBranchSet_disjoint c hc
    rw [Set.disjoint_left] at hdisj
    have heq : (juliaBranchSet c hc false)ᶜ = juliaBranchSet c hc true := by
      ext x
      simp only [Set.mem_compl_iff]
      constructor
      · intro hx
        rcases Set.eq_univ_iff_forall.mp hcover x with hx' | hx'
        · exact (hx hx').elim
        · exact hx'
      · intro hx hxf
        exact hdisj hxf hx
    rw [heq]
    exact isClosed_juliaBranchSet c hc true
  · have hcover := juliaBranchSet_cover c hc
    have hdisj := juliaBranchSet_disjoint c hc
    rw [Set.disjoint_left] at hdisj
    have heq : (juliaBranchSet c hc true)ᶜ = juliaBranchSet c hc false := by
      ext x
      simp only [Set.mem_compl_iff]
      constructor
      · intro hx
        rcases Set.eq_univ_iff_forall.mp hcover x with hx' | hx'
        · exact hx'
        · exact (hx hx').elim
      · intro hx hxt
        exact hdisj hx hxt
    rw [heq]
    exact isClosed_juliaBranchSet c hc false

def juliaCoord (c : ℂ) (hc : c ∉ Mandelbrot) (x : FilledJulia c) : ℂ :=
  (escapeDiskModel c hc).map x

lemma juliaCoord_mem (c : ℂ) (hc : c ∉ Mandelbrot) (x : FilledJulia c) :
    juliaCoord c hc x ∈ Metric.ball (0 : ℂ) 1 :=
  (escapeDiskModel c hc).mapsTo (filledJulia_subset_escapeU c hc x.2)

lemma juliaCoord_juliaInverse (c : ℂ) (hc : c ∉ Mandelbrot) (b : Bool)
    (y : FilledJulia c) :
    juliaCoord c hc (juliaInverse c hc b y) =
      conjugateBranch (escapeDiskModel c hc) c (criticalValue_not_mem_escapeU hc)
        (preimage_escapeU_subset hc) b (juliaCoord c hc y) := by
  let m := escapeDiskModel c hc
  change m.map (inverseBranch m c _ b y) =
    m.map (inverseBranch m c _ b (m.invMap (m.map y)))
  rw [m.invMap_map]
  exact filledJulia_subset_escapeU c hc y.2

lemma rho_juliaCoord_le_of_same_side {c : ℂ} (hc : c ∉ Mandelbrot) {Q : ℝ}
    (hQ : ∀ b : Bool, ∀ z ∈ Metric.ball (0 : ℂ) 1, ∀ w ∈ Metric.ball (0 : ℂ) 1,
      rho (conjugateBranch (escapeDiskModel c hc) c (criticalValue_not_mem_escapeU hc)
          (preimage_escapeU_subset hc) b z)
        (conjugateBranch (escapeDiskModel c hc) c (criticalValue_not_mem_escapeU hc)
          (preimage_escapeU_subset hc) b w) ≤ Q * rho z w)
    {x y : FilledJulia c}
    (hsame : x ∈ juliaBranchSet c hc false ↔ y ∈ juliaBranchSet c hc false) :
    rho (juliaCoord c hc x) (juliaCoord c hc y) ≤
      Q * rho (juliaCoord c hc (Helpers.tcOnFilledJulia c x))
        (juliaCoord c hc (Helpers.tcOnFilledJulia c y)) := by
  by_cases hx : x ∈ juliaBranchSet c hc false
  · have hy := hsame.mp hx
    obtain ⟨x₀, rfl⟩ := hx
    obtain ⟨y₀, rfl⟩ := hy
    rw [juliaCoord_juliaInverse, juliaCoord_juliaInverse,
      tcOn_juliaInverse, tcOn_juliaInverse]
    exact hQ false _ (juliaCoord_mem c hc x₀) _ (juliaCoord_mem c hc y₀)
  · have hy : y ∉ juliaBranchSet c hc false := fun h => hx (hsame.mpr h)
    have hx' : x ∈ juliaBranchSet c hc true := by
      rcases Set.eq_univ_iff_forall.mp (juliaBranchSet_cover c hc) x with h | h
      · exact (hx h).elim
      · exact h
    have hy' : y ∈ juliaBranchSet c hc true := by
      rcases Set.eq_univ_iff_forall.mp (juliaBranchSet_cover c hc) y with h | h
      · exact (hy h).elim
      · exact h
    obtain ⟨x₀, rfl⟩ := hx'
    obtain ⟨y₀, rfl⟩ := hy'
    rw [juliaCoord_juliaInverse, juliaCoord_juliaInverse,
      tcOn_juliaInverse, tcOn_juliaInverse]
    exact hQ true _ (juliaCoord_mem c hc x₀) _ (juliaCoord_mem c hc y₀)

lemma rho_juliaCoord_iterate_bound {c : ℂ} (hc : c ∉ Mandelbrot) {Q : ℝ} (hQ0 : 0 ≤ Q)
    (hQ : ∀ b : Bool, ∀ z ∈ Metric.ball (0 : ℂ) 1, ∀ w ∈ Metric.ball (0 : ℂ) 1,
      rho (conjugateBranch (escapeDiskModel c hc) c (criticalValue_not_mem_escapeU hc)
          (preimage_escapeU_subset hc) b z)
        (conjugateBranch (escapeDiskModel c hc) c (criticalValue_not_mem_escapeU hc)
          (preimage_escapeU_subset hc) b w) ≤ Q * rho z w) :
    ∀ (n : ℕ) (x y : FilledJulia c),
      (∀ k < n, ((Helpers.tcOnFilledJulia c)^[k] x ∈ juliaBranchSet c hc false ↔
        (Helpers.tcOnFilledJulia c)^[k] y ∈ juliaBranchSet c hc false)) →
      rho (juliaCoord c hc x) (juliaCoord c hc y) ≤ Q ^ n *
        rho (juliaCoord c hc ((Helpers.tcOnFilledJulia c)^[n] x))
          (juliaCoord c hc ((Helpers.tcOnFilledJulia c)^[n] y)) := by
  intro n
  induction n with
  | zero =>
      intro x y _
      simp
  | succ n ih =>
      intro x y hsame
      have hstep := rho_juliaCoord_le_of_same_side hc hQ
        (hsame 0 (Nat.zero_lt_succ n))
      have htail : ∀ k < n,
          ((Helpers.tcOnFilledJulia c)^[k] (Helpers.tcOnFilledJulia c x) ∈
              juliaBranchSet c hc false ↔
            (Helpers.tcOnFilledJulia c)^[k] (Helpers.tcOnFilledJulia c y) ∈
              juliaBranchSet c hc false) := by
        intro k hk
        simpa only [Function.iterate_succ_apply] using hsame (k + 1) (Nat.succ_lt_succ hk)
      have hrest := ih (Helpers.tcOnFilledJulia c x) (Helpers.tcOnFilledJulia c y) htail
      calc
        rho (juliaCoord c hc x) (juliaCoord c hc y) ≤
            Q * rho (juliaCoord c hc (Helpers.tcOnFilledJulia c x))
              (juliaCoord c hc (Helpers.tcOnFilledJulia c y)) := hstep
        _ ≤ Q * (Q ^ n *
            rho (juliaCoord c hc ((Helpers.tcOnFilledJulia c)^[n]
                (Helpers.tcOnFilledJulia c x)))
              (juliaCoord c hc ((Helpers.tcOnFilledJulia c)^[n]
                (Helpers.tcOnFilledJulia c y)))) :=
          mul_le_mul_of_nonneg_left hrest hQ0
        _ = Q ^ (n + 1) *
            rho (juliaCoord c hc ((Helpers.tcOnFilledJulia c)^[n + 1] x))
              (juliaCoord c hc ((Helpers.tcOnFilledJulia c)^[n + 1] y)) := by
          rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
          ring

lemma exists_iterate_separates {c : ℂ} (hc : c ∉ Mandelbrot) {x y : FilledJulia c}
    (hxy : x ≠ y) : ∃ k : ℕ,
      ¬((Helpers.tcOnFilledJulia c)^[k] x ∈ juliaBranchSet c hc false ↔
        (Helpers.tcOnFilledJulia c)^[k] y ∈ juliaBranchSet c hc false) := by
  obtain ⟨Q, hQ0, hQ1, hQ⟩ := exists_escape_rho_contraction hc
  by_contra! hsame
  have hxU := filledJulia_subset_escapeU c hc x.2
  have hyU := filledJulia_subset_escapeU c hc y.2
  have hcoord_ne : juliaCoord c hc x ≠ juliaCoord c hc y := fun h =>
    hxy (Subtype.ext ((escapeDiskModel c hc).injOn hxU hyU h))
  have hxcoord : ‖juliaCoord c hc x‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using juliaCoord_mem c hc x
  have hycoord : ‖juliaCoord c hc y‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using juliaCoord_mem c hc y
  have hrho_pos : 0 < rho (juliaCoord c hc x) (juliaCoord c hc y) :=
    lt_of_le_of_ne (rho_nonneg _ _) (Ne.symm (mt (rho_eq_zero_iff hxcoord hycoord).mp hcoord_ne))
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hrho_pos hQ1
  have hbound := rho_juliaCoord_iterate_bound hc hQ0 hQ n x y
    (fun k hk => hsame k)
  have htail : rho
      (juliaCoord c hc ((Helpers.tcOnFilledJulia c)^[n] x))
      (juliaCoord c hc ((Helpers.tcOnFilledJulia c)^[n] y)) < 1 := by
    apply rho_lt_one
    · simpa only [Metric.mem_ball, dist_zero_right] using
        juliaCoord_mem c hc ((Helpers.tcOnFilledJulia c)^[n] x)
    · simpa only [Metric.mem_ball, dist_zero_right] using
        juliaCoord_mem c hc ((Helpers.tcOnFilledJulia c)^[n] y)
  have hpow0 : 0 ≤ Q ^ n := pow_nonneg hQ0 n
  have hstrict : Q ^ n * rho
      (juliaCoord c hc ((Helpers.tcOnFilledJulia c)^[n] x))
      (juliaCoord c hc ((Helpers.tcOnFilledJulia c)^[n] y)) ≤ Q ^ n := by
    nlinarith
  exact (not_lt_of_ge (hbound.trans hstrict)) hn

theorem filledJuliaTotallySeparatedSpace {c : ℂ} (hc : c ∉ Mandelbrot) :
    TotallySeparatedSpace (FilledJulia c) := by
  rw [totallySeparatedSpace_iff_exists_isClopen]
  intro x y hxy
  obtain ⟨k, hk⟩ := exists_iterate_separates hc hxy
  let s := (Helpers.tcOnFilledJulia c)^[k] ⁻¹' juliaBranchSet c hc false
  have hs : IsClopen s := (isClopen_juliaBranchSet c hc false).preimage
    ((Helpers.continuous_tcOnFilledJulia c).iterate k)
  by_cases hx : x ∈ s
  · refine ⟨s, hs, hx, ?_⟩
    intro hy
    exact hk ⟨fun _ => hy, fun _ => hx⟩
  · have hy : y ∈ s := by
      by_contra hyn
      apply hk
      exact ⟨fun h => (hx h).elim, fun h => (hyn h).elim⟩
    refine ⟨sᶜ, hs.compl, hx, ?_⟩
    simpa using hy

lemma dist_le_two_mul_rho {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    dist z w ≤ 2 * rho z w := by
  have hden : 1 - star w * z ≠ 0 := discAut_denom_ne hw hz
  have hden_bound : ‖1 - star w * z‖ ≤ 2 := by
    calc
      ‖1 - star w * z‖ ≤ ‖(1 : ℂ)‖ + ‖star w * z‖ := norm_sub_le _ _
      _ = 1 + ‖w‖ * ‖z‖ := by simp
      _ ≤ 2 := by
        nlinarith [norm_nonneg w, norm_nonneg z,
          mul_nonneg (sub_nonneg.mpr hw.le) (norm_nonneg z)]
  have hid : z - w = discAut w z * (1 - star w * z) := by
    have hden' : 1 - z * star w ≠ 0 := by simpa only [mul_comm] using hden
    rw [discAut]
    field_simp [hden, hden']
  calc
    dist z w = ‖z - w‖ := dist_eq_norm z w
    _ = ‖discAut w z * (1 - star w * z)‖ := by rw [hid]
    _ = rho z w * ‖1 - star w * z‖ := by rw [norm_mul, rho]
    _ ≤ rho z w * 2 := mul_le_mul_of_nonneg_left hden_bound (rho_nonneg z w)
    _ = 2 * rho z w := by ring

noncomputable def juliaBit (c : ℂ) (hc : c ∉ Mandelbrot) (x : FilledJulia c) : Bool := by
  classical
  exact if x ∈ juliaBranchSet c hc false then false else true

lemma mem_juliaBranchSet_juliaBit (c : ℂ) (hc : c ∉ Mandelbrot) (x : FilledJulia c) :
    x ∈ juliaBranchSet c hc (juliaBit c hc x) := by
  classical
  by_cases hx : x ∈ juliaBranchSet c hc false
  · simp [juliaBit, hx]
  · have hx' : x ∈ juliaBranchSet c hc true := by
      rcases Set.eq_univ_iff_forall.mp (juliaBranchSet_cover c hc) x with h | h
      · exact (hx h).elim
      · exact h
    simpa [juliaBit, hx] using hx'

lemma juliaInverse_bit_tc (c : ℂ) (hc : c ∉ Mandelbrot) (x : FilledJulia c) :
    juliaInverse c hc (juliaBit c hc x) (Helpers.tcOnFilledJulia c x) = x := by
  obtain ⟨y, hy⟩ := mem_juliaBranchSet_juliaBit c hc x
  have hyx : y = Helpers.tcOnFilledJulia c x := by
    rw [← tcOn_juliaInverse c hc (juliaBit c hc x) y, hy]
  subst y
  exact hy

noncomputable def pullPrefix (c : ℂ) (hc : c ∉ Mandelbrot) :
    FilledJulia c → ℕ → FilledJulia c → FilledJulia c
  | _, 0, y => y
  | x, n + 1, y =>
      juliaInverse c hc (juliaBit c hc x)
        (pullPrefix c hc (Helpers.tcOnFilledJulia c x) n y)

lemma iterate_pullPrefix (c : ℂ) (hc : c ∉ Mandelbrot) :
    ∀ (n : ℕ) (x y : FilledJulia c),
      (Helpers.tcOnFilledJulia c)^[n] (pullPrefix c hc x n y) = y := by
  intro n
  induction n with
  | zero => simp [pullPrefix]
  | succ n ih =>
      intro x y
      rw [pullPrefix, Function.iterate_succ_apply, tcOn_juliaInverse]
      exact ih (Helpers.tcOnFilledJulia c x) y

lemma pullPrefix_iterate (c : ℂ) (hc : c ∉ Mandelbrot) :
    ∀ (n : ℕ) (x : FilledJulia c),
      pullPrefix c hc x n ((Helpers.tcOnFilledJulia c)^[n] x) = x := by
  intro n
  induction n with
  | zero => simp [pullPrefix]
  | succ n ih =>
      intro x
      rw [pullPrefix, Function.iterate_succ_apply,
        ih (Helpers.tcOnFilledJulia c x), juliaInverse_bit_tc]

lemma rho_pullPrefix_le {c : ℂ} (hc : c ∉ Mandelbrot) {Q : ℝ} (hQ0 : 0 ≤ Q)
    (hQ : ∀ b : Bool, ∀ z ∈ Metric.ball (0 : ℂ) 1, ∀ w ∈ Metric.ball (0 : ℂ) 1,
      rho (conjugateBranch (escapeDiskModel c hc) c (criticalValue_not_mem_escapeU hc)
          (preimage_escapeU_subset hc) b z)
        (conjugateBranch (escapeDiskModel c hc) c (criticalValue_not_mem_escapeU hc)
          (preimage_escapeU_subset hc) b w) ≤ Q * rho z w) :
    ∀ (n : ℕ) (x u v : FilledJulia c),
      rho (juliaCoord c hc (pullPrefix c hc x n u))
          (juliaCoord c hc (pullPrefix c hc x n v)) ≤
        Q ^ n * rho (juliaCoord c hc u) (juliaCoord c hc v) := by
  intro n
  induction n with
  | zero =>
      intro x u v
      simp [pullPrefix]
  | succ n ih =>
      intro x u v
      rw [pullPrefix, pullPrefix, juliaCoord_juliaInverse, juliaCoord_juliaInverse]
      calc
        rho
            (conjugateBranch (escapeDiskModel c hc) c (criticalValue_not_mem_escapeU hc)
              (preimage_escapeU_subset hc) (juliaBit c hc x)
              (juliaCoord c hc (pullPrefix c hc (Helpers.tcOnFilledJulia c x) n u)))
            (conjugateBranch (escapeDiskModel c hc) c (criticalValue_not_mem_escapeU hc)
              (preimage_escapeU_subset hc) (juliaBit c hc x)
              (juliaCoord c hc (pullPrefix c hc (Helpers.tcOnFilledJulia c x) n v))) ≤
          Q * rho (juliaCoord c hc (pullPrefix c hc (Helpers.tcOnFilledJulia c x) n u))
            (juliaCoord c hc (pullPrefix c hc (Helpers.tcOnFilledJulia c x) n v)) :=
          hQ _ _ (juliaCoord_mem c hc _) _ (juliaCoord_mem c hc _)
        _ ≤ Q * (Q ^ n * rho (juliaCoord c hc u) (juliaCoord c hc v)) :=
          mul_le_mul_of_nonneg_left (ih (Helpers.tcOnFilledJulia c x) u v) hQ0
        _ = Q ^ (n + 1) * rho (juliaCoord c hc u) (juliaCoord c hc v) := by ring

noncomputable def juliaAlternate (c : ℂ) (hc : c ∉ Mandelbrot)
    (x : FilledJulia c) (n : ℕ) : FilledJulia c :=
  let xn := (Helpers.tcOnFilledJulia c)^[n] x
  pullPrefix c hc x n
    (juliaInverse c hc (!(juliaBit c hc xn)) (Helpers.tcOnFilledJulia c xn))

lemma juliaAlternate_ne (c : ℂ) (hc : c ∉ Mandelbrot) (x : FilledJulia c) (n : ℕ) :
    juliaAlternate c hc x n ≠ x := by
  intro heq
  let xn := (Helpers.tcOnFilledJulia c)^[n] x
  have hsibling : juliaInverse c hc (!(juliaBit c hc xn))
      (Helpers.tcOnFilledJulia c xn) = xn := by
    have h := congrArg ((Helpers.tcOnFilledJulia c)^[n]) heq
    rw [juliaAlternate, iterate_pullPrefix] at h
    simpa [xn] using h
  have hmain : juliaInverse c hc (juliaBit c hc xn)
      (Helpers.tcOnFilledJulia c xn) = xn := juliaInverse_bit_tc c hc xn
  have hdisj := juliaBranchSet_disjoint c hc
  rw [Set.disjoint_left] at hdisj
  cases hbit : juliaBit c hc xn
  · have hfalse : xn ∈ juliaBranchSet c hc false := ⟨_, by simpa [hbit] using hmain⟩
    have htrue : xn ∈ juliaBranchSet c hc true := ⟨_, by simpa [hbit] using hsibling⟩
    exact hdisj hfalse htrue
  · have htrue : xn ∈ juliaBranchSet c hc true := ⟨_, by simpa [hbit] using hmain⟩
    have hfalse : xn ∈ juliaBranchSet c hc false := ⟨_, by simpa [hbit] using hsibling⟩
    exact hdisj hfalse htrue

lemma dist_juliaCoord_alternate_le {c : ℂ} (hc : c ∉ Mandelbrot) {Q : ℝ} (hQ0 : 0 ≤ Q)
    (hQ : ∀ b : Bool, ∀ z ∈ Metric.ball (0 : ℂ) 1, ∀ w ∈ Metric.ball (0 : ℂ) 1,
      rho (conjugateBranch (escapeDiskModel c hc) c (criticalValue_not_mem_escapeU hc)
          (preimage_escapeU_subset hc) b z)
        (conjugateBranch (escapeDiskModel c hc) c (criticalValue_not_mem_escapeU hc)
          (preimage_escapeU_subset hc) b w) ≤ Q * rho z w)
    (x : FilledJulia c) (n : ℕ) :
    dist (juliaCoord c hc (juliaAlternate c hc x n)) (juliaCoord c hc x) ≤ 2 * Q ^ n := by
  let xn := (Helpers.tcOnFilledJulia c)^[n] x
  let sibling := juliaInverse c hc (!(juliaBit c hc xn)) (Helpers.tcOnFilledJulia c xn)
  have hpref := rho_pullPrefix_le hc hQ0 hQ n x sibling xn
  have hrewrite : pullPrefix c hc x n xn = x := pullPrefix_iterate c hc n x
  have hrho : rho (juliaCoord c hc (juliaAlternate c hc x n)) (juliaCoord c hc x) ≤ Q ^ n := by
    change rho (juliaCoord c hc (pullPrefix c hc x n sibling)) (juliaCoord c hc x) ≤ Q ^ n
    calc
      rho (juliaCoord c hc (pullPrefix c hc x n sibling)) (juliaCoord c hc x) =
          rho (juliaCoord c hc (pullPrefix c hc x n sibling))
            (juliaCoord c hc (pullPrefix c hc x n xn)) := by rw [hrewrite]
      _ ≤ Q ^ n * rho (juliaCoord c hc sibling) (juliaCoord c hc xn) := hpref
      _ ≤ Q ^ n := mul_le_of_le_one_right (pow_nonneg hQ0 n)
        (rho_lt_one (by
          simpa only [Metric.mem_ball, dist_zero_right] using juliaCoord_mem c hc sibling) (by
          simpa only [Metric.mem_ball, dist_zero_right] using juliaCoord_mem c hc xn)).le
  exact (dist_le_two_mul_rho (by
    simpa only [Metric.mem_ball, dist_zero_right] using juliaCoord_mem c hc (juliaAlternate c hc x n)) (by
    simpa only [Metric.mem_ball, dist_zero_right] using juliaCoord_mem c hc x)).trans
      (mul_le_mul_of_nonneg_left hrho (by norm_num))

lemma tendsto_juliaCoord_alternate (c : ℂ) (hc : c ∉ Mandelbrot) (x : FilledJulia c) :
    Filter.Tendsto (fun n => juliaCoord c hc (juliaAlternate c hc x n)) Filter.atTop
      (𝓝 (juliaCoord c hc x)) := by
  obtain ⟨Q, hQ0, hQ1, hQ⟩ := exists_escape_rho_contraction hc
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (half_pos hε) hQ1
  refine ⟨N, fun n hn => ?_⟩
  have hpow : Q ^ n ≤ Q ^ N := pow_le_pow_of_le_one hQ0 hQ1.le hn
  have hdist := dist_juliaCoord_alternate_le hc hQ0 hQ x n
  nlinarith

lemma tendsto_juliaAlternate (c : ℂ) (hc : c ∉ Mandelbrot) (x : FilledJulia c) :
    Filter.Tendsto (juliaAlternate c hc x) Filter.atTop (𝓝 x) := by
  let m := escapeDiskModel c hc
  have hcoord := tendsto_juliaCoord_alternate c hc x
  have hxcoord := juliaCoord_mem c hc x
  have hinv : ContinuousAt m.invMap (juliaCoord c hc x) :=
    m.continuousOn_invMap.continuousAt (Metric.isOpen_ball.mem_nhds hxcoord)
  have hcomp := hinv.tendsto.comp hcoord
  have hxU := filledJulia_subset_escapeU c hc x.2
  have hxinv : m.invMap (juliaCoord c hc x) = x := by
    change m.invMap (m.map x) = x
    exact m.invMap_map hxU
  rw [hxinv] at hcomp
  have hval : Filter.Tendsto (fun n => (juliaAlternate c hc x n : ℂ)) Filter.atTop (𝓝 (x : ℂ)) := by
    apply hcomp.congr'
    exact Filter.Eventually.of_forall fun n =>
      m.invMap_map (filledJulia_subset_escapeU c hc (juliaAlternate c hc x n).2)
  exact tendsto_subtype_rng.mpr hval

theorem filledJuliaPerfectSpace {c : ℂ} (hc : c ∉ Mandelbrot) :
    PerfectSpace (FilledJulia c) := by
  constructor
  rw [preperfect_iff_nhds]
  intro x _ U hU
  have hevent : ∀ᶠ n in Filter.atTop, juliaAlternate c hc x n ∈ U :=
    (tendsto_juliaAlternate c hc x).eventually hU
  obtain ⟨n, hn⟩ := hevent.exists
  exact ⟨juliaAlternate c hc x n, ⟨hn, Set.mem_univ _⟩, juliaAlternate_ne c hc x n⟩

theorem homeomorph_cantor_of_not_mem_mandelbrot {c : ℂ} (hc : c ∉ Mandelbrot) :
    Nonempty ((FilledJulia c) ≃ₜ (ℕ → Bool)) := by
  letI : TotallySeparatedSpace (FilledJulia c) := filledJuliaTotallySeparatedSpace hc
  letI : PerfectSpace (FilledJulia c) := filledJuliaPerfectSpace hc
  exact ⟨CantorClassification.homeomorphCantor (FilledJulia c)⟩

end

end Submission.Escaping
