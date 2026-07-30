import Mathlib.Analysis.Complex.RiemannMapping
import Submission.Helpers

open Metric
open Filter
open Function Set
open scoped Topology

namespace Submission

noncomputable def diskMobius (a z : ℂ) : ℂ :=
  (z - a) / (1 - starRingEnd ℂ a * z)

noncomputable def diskMobiusInv (a z : ℂ) : ℂ :=
  (z + a) / (1 + starRingEnd ℂ a * z)

lemma diskMobius_denominator_ne_zero {a z : ℂ}
    (ha : a ∈ ball (0 : ℂ) 1) (hz : z ∈ ball (0 : ℂ) 1) :
    1 - starRingEnd ℂ a * z ≠ 0 := by
  have ha' : ‖a‖ < 1 := by simpa [mem_ball_zero_iff] using ha
  have hz' : ‖z‖ < 1 := by simpa [mem_ball_zero_iff] using hz
  have hlt : ‖starRingEnd ℂ a * z‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg a, norm_nonneg z]
  intro h
  have heq : starRingEnd ℂ a * z = 1 := (eq_of_sub_eq_zero h).symm
  rw [heq, norm_one] at hlt
  exact (lt_self_iff_false 1).mp hlt

lemma diskMobiusInv_denominator_ne_zero {a z : ℂ}
    (ha : a ∈ ball (0 : ℂ) 1) (hz : z ∈ ball (0 : ℂ) 1) :
    1 + starRingEnd ℂ a * z ≠ 0 := by
  have ha' : ‖a‖ < 1 := by simpa [mem_ball_zero_iff] using ha
  have hz' : ‖z‖ < 1 := by simpa [mem_ball_zero_iff] using hz
  have hlt : ‖starRingEnd ℂ a * z‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg a, norm_nonneg z]
  intro h
  have heq : starRingEnd ℂ a * z = -1 := by linear_combination h
  rw [heq, norm_neg, norm_one] at hlt
  exact (lt_self_iff_false 1).mp hlt

lemma diskMobius_norm_sq_sub_norm_sq (a z : ℂ) :
    ‖1 - starRingEnd ℂ a * z‖ ^ 2 - ‖z - a‖ ^ 2 =
      (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
  ring

lemma diskMobius_mapsTo_unitBall {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) :
    Set.MapsTo (diskMobius a) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
  intro z hz
  have ha' : ‖a‖ < 1 := by simpa [mem_ball_zero_iff] using ha
  have hz' : ‖z‖ < 1 := by simpa [mem_ball_zero_iff] using hz
  have hden0 := diskMobius_denominator_ne_zero ha hz
  have hsq := diskMobius_norm_sq_sub_norm_sq a z
  have haSq : ‖a‖ ^ 2 < 1 := by
    have hpos : 0 < (1 - ‖a‖) * (1 + ‖a‖) :=
      mul_pos (sub_pos.mpr ha') (by positivity)
    nlinarith
  have hzSq : ‖z‖ ^ 2 < 1 := by
    have hpos : 0 < (1 - ‖z‖) * (1 + ‖z‖) :=
      mul_pos (sub_pos.mpr hz') (by positivity)
    nlinarith
  have hpos : 0 < (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) :=
    mul_pos (sub_pos.mpr haSq) (sub_pos.mpr hzSq)
  have hnorm : ‖z - a‖ < ‖1 - starRingEnd ℂ a * z‖ := by
    nlinarith [sq_nonneg (‖z - a‖ + ‖1 - starRingEnd ℂ a * z‖),
      norm_nonneg (z - a), norm_nonneg (1 - starRingEnd ℂ a * z)]
  rw [mem_ball_zero_iff, diskMobius, norm_div, div_lt_one]
  · exact hnorm
  · exact norm_pos_iff.mpr hden0

lemma diskMobiusInv_mapsTo_unitBall {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) :
    Set.MapsTo (diskMobiusInv a) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
  intro z hz
  have h := diskMobius_mapsTo_unitBall
    (show -a ∈ ball (0 : ℂ) 1 by simpa [mem_ball_zero_iff] using ha) hz
  simpa [diskMobiusInv, diskMobius] using h

lemma diskMobiusInv_diskMobius {a z : ℂ}
    (ha : a ∈ ball (0 : ℂ) 1) (hz : z ∈ ball (0 : ℂ) 1) :
    diskMobiusInv a (diskMobius a z) = z := by
  have hden := diskMobius_denominator_ne_zero ha hz
  have hden' : 1 - z * starRingEnd ℂ a ≠ 0 := by
    simpa [mul_comm] using hden
  have hout := diskMobiusInv_denominator_ne_zero ha
    (diskMobius_mapsTo_unitBall ha hz)
  rw [diskMobiusInv]
  apply (div_eq_iff hout).2
  rw [diskMobius]
  field_simp [hden, hden']
  ring

lemma diskMobius_diskMobiusInv {a z : ℂ}
    (ha : a ∈ ball (0 : ℂ) 1) (hz : z ∈ ball (0 : ℂ) 1) :
    diskMobius a (diskMobiusInv a z) = z := by
  have hden := diskMobiusInv_denominator_ne_zero ha hz
  have hden' : 1 + z * starRingEnd ℂ a ≠ 0 := by
    simpa [mul_comm] using hden
  have hout := diskMobius_denominator_ne_zero ha
    (diskMobiusInv_mapsTo_unitBall ha hz)
  rw [diskMobius]
  apply (div_eq_iff hout).2
  rw [diskMobiusInv]
  field_simp [hden, hden']
  ring

lemma diskMobius_injOn_unitBall {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) :
    (ball (0 : ℂ) 1).InjOn (diskMobius a) := by
  intro x hx y hy hxy
  rw [← diskMobiusInv_diskMobius ha hx,
    ← diskMobiusInv_diskMobius ha hy, hxy]

lemma hasDerivAt_diskMobius {a z : ℂ}
    (ha : a ∈ ball (0 : ℂ) 1) (hz : z ∈ ball (0 : ℂ) 1) :
    HasDerivAt (diskMobius a)
      ((1 - starRingEnd ℂ a * a) /
        (1 - starRingEnd ℂ a * z) ^ 2) z := by
  have hden := diskMobius_denominator_ne_zero ha hz
  have hnum : HasDerivAt (fun w : ℂ => w - a) 1 z :=
    (hasDerivAt_id z).sub_const a
  have hden' : HasDerivAt
      (fun w : ℂ => 1 - starRingEnd ℂ a * w) (-(starRingEnd ℂ a)) z := by
    exact (hasDerivAt_const_mul (x := z) (starRingEnd ℂ a)).const_sub 1
  change HasDerivAt
    (fun w : ℂ => (w - a) / (1 - starRingEnd ℂ a * w)) _ z
  apply (hnum.div hden' hden).congr_deriv
  congr 1
  ring

lemma deriv_diskMobius_zero {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) :
    deriv (diskMobius a) 0 = 1 - starRingEnd ℂ a * a := by
  have hz : (0 : ℂ) ∈ ball 0 1 := by simp
  simpa using (hasDerivAt_diskMobius ha hz).deriv

lemma deriv_diskMobius_self {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) :
    deriv (diskMobius a) a = (1 - starRingEnd ℂ a * a)⁻¹ := by
  have hunit := diskMobius_denominator_ne_zero ha ha
  rw [(hasDerivAt_diskMobius ha ha).deriv]
  rw [div_eq_mul_inv, ← inv_pow, pow_two, ← mul_assoc,
    mul_inv_cancel₀ hunit, one_mul]

lemma hasDerivAt_of_continuousAt_sq_eq
    {u q : ℂ → ℂ} {z u' : ℂ}
    (hq : ContinuousAt q z) (hsq : ∀ w, q w ^ 2 = u w)
    (hq0 : q z ≠ 0) (hu : HasDerivAt u u' z) :
    HasDerivAt q (u' / (2 * q z)) z := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hsum : Tendsto (fun w => q w + q z) (𝓝[≠] z)
      (𝓝 (q z + q z)) :=
    (hq.tendsto.mono_left nhdsWithin_le_nhds).add_const (q z)
  have hsum0 : q z + q z ≠ 0 := by
    rw [← two_mul]
    exact mul_ne_zero (by norm_num) hq0
  have htendsto : Tendsto
      (fun w => slope u z w / (q w + q z)) (𝓝[≠] z)
      (𝓝 (u' / (q z + q z))) :=
    hu.tendsto_slope.div hsum hsum0
  have heq :
      (fun w => slope q z w) =ᶠ[𝓝[≠] z]
        (fun w => slope u z w / (q w + q z)) := by
    filter_upwards [hsum.eventually_ne hsum0, self_mem_nhdsWithin]
      with w hden hw
    have hwz : w - z ≠ 0 := sub_ne_zero.mpr hw
    simp only [slope, vsub_eq_sub, smul_eq_mul]
    rw [← hsq w, ← hsq z]
    field_simp [hden, hwz]
    ring_nf
  convert htendsto.congr' heq.symm using 1
  ring_nf

lemma exists_differentiable_squareRoot
    {U : Set ℂ} (hUc : IsSimplyConnected U) (hUo : IsOpen U)
    {u : ℂ → ℂ} (hu : DifferentiableOn ℂ u U) (hu0 : 0 ∉ u '' U) :
    ∃ q : ℂ → ℂ, DifferentiableOn ℂ q U ∧
      ContinuousOn q U ∧ ∀ z, q z ^ 2 = u z := by
  rcases Complex.exists_continuousOn_pow_eq hUc hUo hu.continuousOn hu0
      (by norm_num : 2 ≠ 0) with ⟨q, hqcont, hqpow⟩
  have hq0 : ∀ z ∈ U, q z ≠ 0 := by
    intro z hz hzero
    apply hu0
    refine ⟨z, hz, ?_⟩
    rw [← hqpow z, hzero, zero_pow (by norm_num : 2 ≠ 0)]
  refine ⟨q, ?_, hqcont, hqpow⟩
  intro z hz
  have huAt : DifferentiableAt ℂ u z :=
    (hu z hz).differentiableAt (hUo.mem_nhds hz)
  exact (hasDerivAt_of_continuousAt_sq_eq
    (hqcont.continuousAt (hUo.mem_nhds hz)) hqpow (hq0 z hz)
    huAt.hasDerivAt).differentiableAt.differentiableWithinAt

lemma squareRoot_mapsTo_unitBall {U : Set ℂ} {u q : ℂ → ℂ}
    (hu : Set.MapsTo u U (ball (0 : ℂ) 1))
    (hq : ∀ z, q z ^ 2 = u z) :
    Set.MapsTo q U (ball (0 : ℂ) 1) := by
  intro z hz
  rw [mem_ball_zero_iff]
  have huNorm : ‖u z‖ < 1 := by
    simpa [mem_ball_zero_iff] using hu hz
  have hpow : ‖q z‖ ^ 2 = ‖u z‖ := by
    rw [← norm_pow, hq z]
  by_contra hnot
  have hone : 1 ≤ ‖q z‖ := le_of_not_gt hnot
  nlinarith [norm_nonneg (q z)]

lemma squareRoot_injOn {U : Set ℂ} {u q : ℂ → ℂ}
    (hu : U.InjOn u) (hq : ∀ z, q z ^ 2 = u z) : U.InjOn q := by
  intro x hx y hy hxy
  apply hu hx hy
  rw [← hq x, ← hq y, hxy]

lemma diskMobius_comp_differentiableOn {U : Set ℂ} {h : ℂ → ℂ} {a : ℂ}
    (hUo : IsOpen U) (hh : DifferentiableOn ℂ h U)
    (ha : a ∈ ball (0 : ℂ) 1)
    (hmap : Set.MapsTo h U (ball (0 : ℂ) 1)) :
    DifferentiableOn ℂ (fun z => diskMobius a (h z)) U := by
  intro z hz
  exact ((hasDerivAt_diskMobius ha (hmap hz)).differentiableAt.comp z
    ((hh z hz).differentiableAt (hUo.mem_nhds hz))).differentiableWithinAt

lemma diskMobius_comp_injOn {U : Set ℂ} {h : ℂ → ℂ} {a : ℂ}
    (hh : U.InjOn h) (ha : a ∈ ball (0 : ℂ) 1)
    (hmap : Set.MapsTo h U (ball (0 : ℂ) 1)) :
    U.InjOn (fun z => diskMobius a (h z)) := by
  intro x hx y hy hxy
  apply hh hx hy
  exact diskMobius_injOn_unitBall ha (hmap hx) (hmap hy) hxy

lemma diskMobius_comp_avoids_zero {U : Set ℂ} {h : ℂ → ℂ} {a : ℂ}
    (ha : a ∈ ball (0 : ℂ) 1)
    (hmap : Set.MapsTo h U (ball (0 : ℂ) 1))
    (haNot : a ∉ h '' U) :
    0 ∉ (fun z => diskMobius a (h z)) '' U := by
  rintro ⟨z, hz, hzero⟩
  apply haNot
  refine ⟨z, hz, ?_⟩
  apply diskMobius_injOn_unitBall ha (hmap hz) ha
  simpa [diskMobius] using hzero

@[simp]
lemma diskMobius_self (a : ℂ) : diskMobius a a = 0 := by
  simp [diskMobius]

@[simp]
lemma diskMobiusInv_zero (a : ℂ) : diskMobiusInv a 0 = a := by
  simp [diskMobiusInv]

structure NormalizedDiskEmbedding (U : Set ℂ) (x : ℂ) where
  toFun : ℂ → ℂ
  differentiableOn : DifferentiableOn ℂ toFun U
  mapsTo : Set.MapsTo toFun U (ball (0 : ℂ) 1)
  injOn : U.InjOn toFun
  map_base : toFun x = 0
  deriv_ne_zero : deriv toFun x ≠ 0

instance {U : Set ℂ} {x : ℂ} : CoeFun (NormalizedDiskEmbedding U x)
    (fun _ => ℂ → ℂ) := ⟨NormalizedDiskEmbedding.toFun⟩

theorem exists_injective_not_dense_image_deriv_ne_zero
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U)
    (hU : U ≠ Set.univ) :
    ∃ f : ℂ → ℂ, Injective f ∧ ¬Dense (f '' U) ∧
      ∀ z ∈ U, deriv f z ≠ 0 := by
  wlog hUzero : 0 ∉ U
  · rw [ne_univ_iff_exists_notMem] at hU
    rcases hU with ⟨a, ha⟩
    specialize this (hUo.vadd (-a)) (by simpa) (by simp [hU])
      (by simpa [mem_vadd_set_iff_neg_vadd_mem])
    rcases this with ⟨f, hf_inj, hf_dense, hdf⟩
    refine ⟨f ∘ (-a + ·), hf_inj.comp (add_right_injective (-a)), ?_,
      fun z hz => ?_⟩
    · simpa only [← image_vadd, Set.image_image] using! hf_dense
    · simpa [Function.comp_def, deriv_comp_const_add] using
        hdf (-a + z) (mapsTo_image _ _ hz)
  rcases Complex.exists_continuousOn_pow_eq hUc hUo continuousOn_id
      (by rwa [image_id]) two_ne_zero with ⟨f, hfc, hf_inv⟩
  replace hf_inv : LeftInverse (· ^ 2) f := hf_inv
  have hfzero : ∀ z ∈ U, f z ≠ 0 := by
    intro z hz hfz
    simpa [hfz, (ne_of_mem_of_not_mem hz hUzero).symm] using hf_inv z
  have hdf : ∀ z ∈ U, HasStrictDerivAt f (2 * f z)⁻¹ z := by
    intro z hz
    apply HasStrictDerivAt.of_local_left_inverse
    · exact hfc.continuousAt (hUo.mem_nhds hz)
    · simpa using hasStrictDerivAt_pow 2 (f z)
    · simpa using hfzero z hz
    · exact .of_forall hf_inv
  refine ⟨f, hf_inv.injective, ?_, fun z hz => ?_⟩
  · simp only [Dense, not_forall, mem_closure_iff_frequently, not_frequently]
    rcases hUc.nonempty with ⟨x, hx⟩
    use -f x
    have himage : f '' U ∈ 𝓝 (f x) := by
      rw [← (hdf x hx).map_nhds_eq (by simpa using hfzero x hx)]
      exact Filter.image_mem_map (hUo.mem_nhds hx)
    rw [nhds_neg, eventually_neg]
    filter_upwards [himage]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    obtain rfl : a = b := by
      rw [← hf_inv b, hab]
      simp [hf_inv a]
    refine hfzero a ha ?_
    linear_combination hab / 2
  · simpa [(hdf z hz).hasDerivAt.deriv] using hfzero z hz

lemma exists_mapsTo_unitBall_injOn_deriv_ne_zero
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U)
    (hU : U ≠ Set.univ) :
    ∃ f : ℂ → ℂ, MapsTo f U (ball 0 1) ∧ InjOn f U ∧
      ∀ z ∈ U, deriv f z ≠ 0 := by
  rcases exists_injective_not_dense_image_deriv_ne_zero hUo hUc hU with
    ⟨f, hf_inj, hfd, hdf⟩
  obtain ⟨x, epsilon, hepsilon, hball⟩ :
      ∃ (x : ℂ) (epsilon : ℝ), 0 < epsilon ∧
        ∀ a ∈ U, epsilon < dist (f a) x := by
    simpa [Dense, mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall]
      using hfd
  have hfx : ∀ z ∈ U, f z ≠ x := fun z hz => by
    simpa using hepsilon.trans (hball z hz)
  use fun z => epsilon / (f z - x)
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    rw [mem_ball_zero_iff, norm_div, Complex.norm_real,
      Real.norm_of_nonneg hepsilon.le, div_lt_one₀]
    · simpa [dist_eq_norm] using hball z hz
    · simpa [sub_eq_zero] using hfx z hz
  · intro z hz w hw heq
    simpa [div_eq_mul_inv, hepsilon.ne', hf_inj.eq_iff] using heq
  · intro z hz
    have hdz : DifferentiableAt ℂ f z :=
      differentiableAt_of_deriv_ne_zero (hdf z hz)
    rw [(hasDerivAt_const _ _).fun_div (hdz.hasDerivAt.sub_const _) _ |>.deriv] <;>
      simp [*, ne_of_gt, sub_eq_zero]

lemma exists_normalizedDiskEmbedding {U : Set ℂ} {x : ℂ}
    (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hU : U ≠ Set.univ)
    (hx : x ∈ U) : Nonempty (NormalizedDiskEmbedding U x) := by
  rcases exists_mapsTo_unitBall_injOn_deriv_ne_zero hUo hUc hU with
    ⟨h, hmap, hinj, hderiv⟩
  let a := h x
  have ha : a ∈ ball (0 : ℂ) 1 := hmap hx
  let g : ℂ → ℂ := fun z => diskMobius a (h z)
  have hh : DifferentiableOn ℂ h U := by
    intro z hz
    exact (differentiableAt_of_deriv_ne_zero (hderiv z hz)).differentiableWithinAt
  have hgdiff : DifferentiableOn ℂ g U :=
    diskMobius_comp_differentiableOn hUo hh ha hmap
  have hgmap : Set.MapsTo g U (ball (0 : ℂ) 1) := fun z hz =>
    diskMobius_mapsTo_unitBall ha (hmap hz)
  have hginj : U.InjOn g := diskMobius_comp_injOn hinj ha hmap
  have hgbase : g x = 0 := by simp [g, a]
  have hunit := diskMobius_denominator_ne_zero ha ha
  have hgderiv0 : ∀ z ∈ U, deriv g z ≠ 0 := by
    intro z hz
    have hhAt : DifferentiableAt ℂ h z :=
      (hh z hz).differentiableAt (hUo.mem_nhds hz)
    have hgderiv : deriv g z =
        deriv (diskMobius a) (h z) * deriv h z := by
      rw [show g = diskMobius a ∘ h by rfl,
        deriv_comp z
          (hasDerivAt_diskMobius ha (hmap hz)).differentiableAt hhAt]
    rw [hgderiv, (hasDerivAt_diskMobius ha (hmap hz)).deriv]
    exact mul_ne_zero
      (div_ne_zero hunit
        (pow_ne_zero 2 (diskMobius_denominator_ne_zero ha (hmap hz))))
      (hderiv z hz)
  exact ⟨⟨g, hgdiff, hgmap, hginj, hgbase, hgderiv0 x hx⟩⟩

lemma NormalizedDiskEmbedding.exists_omittedPointImprovementData_full
    {U : Set ℂ} {x a : ℂ} (E : NormalizedDiskEmbedding U x)
    (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hx : x ∈ U)
    (ha : a ∈ ball (0 : ℂ) 1) (haNot : a ∉ E.toFun '' U) :
    ∃ (F : NormalizedDiskEmbedding U x) (b : ℂ) (q : ℂ → ℂ),
      b ^ 2 = -a ∧ b ∈ ball (0 : ℂ) 1 ∧
        (∀ z, q z ^ 2 = diskMobius a (E z)) ∧
        b = q x ∧
        F.toFun = (fun z => diskMobius b (q z)) ∧
        deriv F.toFun x =
          (1 - starRingEnd ℂ b * b)⁻¹ *
            (((1 - starRingEnd ℂ a * a) * deriv E.toFun x) / (2 * b)) := by
  let u : ℂ → ℂ := fun z => diskMobius a (E z)
  have hudiff : DifferentiableOn ℂ u U :=
    diskMobius_comp_differentiableOn hUo E.differentiableOn ha E.mapsTo
  have humap : MapsTo u U (ball (0 : ℂ) 1) := fun z hz =>
    diskMobius_mapsTo_unitBall ha (E.mapsTo hz)
  have huinj : U.InjOn u := diskMobius_comp_injOn E.injOn ha E.mapsTo
  have huavoid : 0 ∉ u '' U :=
    diskMobius_comp_avoids_zero ha E.mapsTo haNot
  have haunit := diskMobius_denominator_ne_zero ha ha
  rcases exists_differentiable_squareRoot hUc hUo hudiff huavoid with
    ⟨q, hqdiff, hqcont, hqpow⟩
  have hqzero : ∀ z ∈ U, q z ≠ 0 := by
    intro z hz hzero
    apply huavoid
    refine ⟨z, hz, ?_⟩
    rw [← hqpow z, hzero, zero_pow (by norm_num : 2 ≠ 0)]
  have hqmap : MapsTo q U (ball (0 : ℂ) 1) :=
    squareRoot_mapsTo_unitBall humap hqpow
  have hqinj : U.InjOn q := squareRoot_injOn huinj hqpow
  have ha0 : a ≠ 0 := by
    intro hazero
    apply haNot
    exact ⟨x, hx, by simpa [hazero] using E.map_base⟩
  have hux : u x = -a := by simp [u, E.map_base, diskMobius]
  have hq0 : q x ≠ 0 := hqzero x hx
  let b := q x
  have hb : b ∈ ball (0 : ℂ) 1 := hqmap hx
  have hbpow : b ^ 2 = -a := by rw [hqpow x, hux]
  have hbunit := diskMobius_denominator_ne_zero hb hb
  let g : ℂ → ℂ := fun z => diskMobius b (q z)
  have hgdiff : DifferentiableOn ℂ g U :=
    diskMobius_comp_differentiableOn hUo hqdiff hb hqmap
  have hgmap : MapsTo g U (ball (0 : ℂ) 1) := fun z hz =>
    diskMobius_mapsTo_unitBall hb (hqmap hz)
  have hginj : U.InjOn g := diskMobius_comp_injOn hqinj hb hqmap
  have hgbase : g x = 0 := by simp [g, b]
  have hEAt : DifferentiableAt ℂ E.toFun x :=
    (E.differentiableOn x hx).differentiableAt (hUo.mem_nhds hx)
  have huderiv : deriv u x =
      (1 - starRingEnd ℂ a * a) * deriv E.toFun x := by
    rw [show u = diskMobius a ∘ E.toFun by rfl,
      deriv_comp x
        (hasDerivAt_diskMobius ha (E.mapsTo hx)).differentiableAt hEAt,
      E.map_base, deriv_diskMobius_zero ha]
  have hqAt : DifferentiableAt ℂ q x :=
    (hqdiff x hx).differentiableAt (hUo.mem_nhds hx)
  have hqderiv : deriv q x = deriv u x / (2 * b) := by
    simpa only [b] using
      (hasDerivAt_of_continuousAt_sq_eq
        (hqcont.continuousAt (hUo.mem_nhds hx)) hqpow hq0
        ((hudiff x hx).differentiableAt (hUo.mem_nhds hx)).hasDerivAt).deriv
  have hgderiv : deriv g x =
      (1 - starRingEnd ℂ b * b)⁻¹ *
        (((1 - starRingEnd ℂ a * a) * deriv E.toFun x) / (2 * b)) := by
    rw [show g = diskMobius b ∘ q by rfl,
      deriv_comp x (hasDerivAt_diskMobius hb hb).differentiableAt hqAt,
      show q x = b by rfl, deriv_diskMobius_self hb, hqderiv, huderiv]
  have hgderiv0 : deriv g x ≠ 0 := by
    rw [hgderiv]
    exact mul_ne_zero (inv_ne_zero hbunit)
      (div_ne_zero (mul_ne_zero haunit E.deriv_ne_zero)
        (mul_ne_zero (by norm_num) hq0))
  let F : NormalizedDiskEmbedding U x :=
    ⟨g, hgdiff, hgmap, hginj, hgbase, hgderiv0⟩
  refine ⟨F, b, q, hbpow, hb, ?_, rfl, rfl, hgderiv⟩
  intro z
  simpa only [u] using hqpow z

lemma NormalizedDiskEmbedding.exists_omittedPointImprovementData
    {U : Set ℂ} {x a : ℂ} (E : NormalizedDiskEmbedding U x)
    (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hx : x ∈ U)
    (ha : a ∈ ball (0 : ℂ) 1) (haNot : a ∉ E.toFun '' U) :
    ∃ (F : NormalizedDiskEmbedding U x) (b : ℂ),
      b ^ 2 = -a ∧ b ∈ ball (0 : ℂ) 1 ∧
        deriv F.toFun x =
          (1 - starRingEnd ℂ b * b)⁻¹ *
            (((1 - starRingEnd ℂ a * a) * deriv E.toFun x) / (2 * b)) := by
  rcases E.exists_omittedPointImprovementData_full hUo hUc hx ha haNot with
    ⟨F, b, q, hbpow, hb, hqpow, hbq, hF, hderiv⟩
  exact ⟨F, b, hbpow, hb, hderiv⟩

lemma norm_one_sub_conj_mul_self {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖1 - starRingEnd ℂ z * z‖ = 1 - ‖z‖ ^ 2 := by
  have hmul : starRingEnd ℂ z * z = (‖z‖ ^ 2 : ℝ) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hmul]
  have hcast :
      (1 : ℂ) - ((‖z‖ ^ 2 : ℝ) : ℂ) = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow]
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  have hnonneg : 0 ≤ (1 - ‖z‖) * (1 + ‖z‖) :=
    mul_nonneg (sub_nonneg.mpr hz) (by positivity)
  nlinarith

lemma omittedPoint_gain_gt_one {r s : ℝ} (hr : r < 1) (hs : 0 < s)
    (hrel : s ^ 2 = r) :
    1 < (1 - r)⁻¹ * ((1 - r ^ 2) / (2 * s)) := by
  have hr0 : 0 ≤ r := by nlinarith [sq_nonneg s]
  have hsr : s < 1 := by
    by_contra hnot
    have hs1 : 1 ≤ s := le_of_not_gt hnot
    nlinarith [sq_nonneg (s - 1)]
  have h1r : 0 < 1 - r := sub_pos.mpr hr
  have heq :
      (1 - r)⁻¹ * ((1 - r ^ 2) / (2 * s)) = (1 + r) / (2 * s) := by
    field_simp [ne_of_gt h1r, ne_of_gt hs]
    ring
  rw [heq, lt_div_iff₀ (by positivity)]
  nlinarith [sq_pos_of_pos (sub_pos.mpr hsr)]

lemma omittedPoint_derivative_norm_lt
    {a b d : ℂ} (ha : a ∈ ball (0 : ℂ) 1)
    (hb : b ∈ ball (0 : ℂ) 1) (hbpow : b ^ 2 = -a)
    (ha0 : a ≠ 0) (hd : d ≠ 0) :
    ‖d‖ <
      ‖(1 - starRingEnd ℂ b * b)⁻¹ *
        (((1 - starRingEnd ℂ a * a) * d) / (2 * b))‖ := by
  have haNorm : ‖a‖ < 1 := by simpa [mem_ball_zero_iff] using ha
  have hbNorm : ‖b‖ < 1 := by simpa [mem_ball_zero_iff] using hb
  have hb0 : 0 < ‖b‖ := by
    rw [norm_pos_iff]
    intro hzero
    have : a = 0 := by
      have h := hbpow
      rw [hzero, zero_pow (by norm_num : 2 ≠ 0)] at h
      exact neg_eq_zero.mp h.symm
    exact ha0 this
  have hnormRel : ‖b‖ ^ 2 = ‖a‖ := by
    have h := congrArg norm hbpow
    simpa [norm_pow] using h
  have haLe : ‖a‖ ≤ 1 := haNorm.le
  have hbLe : ‖b‖ ≤ 1 := hbNorm.le
  have hgain := omittedPoint_gain_gt_one haNorm hb0 hnormRel
  have hnormTwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [norm_mul, norm_inv, norm_one_sub_conj_mul_self hbLe,
    norm_div, norm_mul, norm_one_sub_conj_mul_self haLe,
    norm_mul, hnormTwo]
  calc
    ‖d‖ = 1 * ‖d‖ := by ring
    _ < ((1 - ‖a‖)⁻¹ * ((1 - ‖a‖ ^ 2) / (2 * ‖b‖))) * ‖d‖ :=
      mul_lt_mul_of_pos_right hgain (norm_pos_iff.mpr hd)
    _ = (1 - ‖b‖ ^ 2)⁻¹ *
        ((1 - ‖a‖ ^ 2) * ‖d‖ / (2 * ‖b‖)) := by
      rw [hnormRel]
      ring

structure NormalizedDiskEmbedding.OmittedPointStep
    {U : Set ℂ} {x : ℂ}
    (E F : NormalizedDiskEmbedding U x) where
  a : ℂ
  b : ℂ
  q : ℂ → ℂ
  a_mem : a ∈ ball (0 : ℂ) 1
  a_omitted : a ∉ E.toFun '' U
  b_sq : b ^ 2 = -a
  b_mem : b ∈ ball (0 : ℂ) 1
  q_sq : ∀ z, q z ^ 2 = diskMobius a (E z)
  b_eq : b = q x
  toFun_eq : F.toFun = fun z => diskMobius b (q z)
  deriv_eq : deriv F.toFun x =
    (1 - starRingEnd ℂ b * b)⁻¹ *
      (((1 - starRingEnd ℂ a * a) * deriv E.toFun x) / (2 * b))

lemma NormalizedDiskEmbedding.exists_omittedPointStep
    {U : Set ℂ} {x a : ℂ} (E : NormalizedDiskEmbedding U x)
    (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hx : x ∈ U)
    (ha : a ∈ ball (0 : ℂ) 1) (haNot : a ∉ E.toFun '' U) :
    ∃ F : NormalizedDiskEmbedding U x, Nonempty (E.OmittedPointStep F) := by
  rcases E.exists_omittedPointImprovementData_full hUo hUc hx ha haNot with
    ⟨F, b, q, hbpow, hb, hqpow, hbq, hF, hderiv⟩
  exact ⟨F, ⟨⟨a, b, q, ha, haNot, hbpow, hb, hqpow, hbq, hF, hderiv⟩⟩⟩

lemma NormalizedDiskEmbedding.OmittedPointStep.deriv_norm_lt
    {U : Set ℂ} {x : ℂ} {E F : NormalizedDiskEmbedding U x}
    (step : E.OmittedPointStep F) (hx : x ∈ U) :
    ‖deriv E.toFun x‖ < ‖deriv F.toFun x‖ := by
  rw [step.deriv_eq]
  have ha0 : step.a ≠ 0 := by
    intro hzero
    apply step.a_omitted
    exact ⟨x, hx, by simpa [hzero] using E.map_base⟩
  exact omittedPoint_derivative_norm_lt step.a_mem step.b_mem step.b_sq
    ha0 E.deriv_ne_zero

lemma NormalizedDiskEmbedding.exists_deriv_norm_gt_of_omitted
    {U : Set ℂ} {x a : ℂ} (E : NormalizedDiskEmbedding U x)
    (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hx : x ∈ U)
    (ha : a ∈ ball (0 : ℂ) 1) (haNot : a ∉ E.toFun '' U) :
    ∃ F : NormalizedDiskEmbedding U x,
      ‖deriv E.toFun x‖ < ‖deriv F.toFun x‖ := by
  rcases E.exists_omittedPointImprovementData hUo hUc hx ha haNot with
    ⟨F, b, hbpow, hb, hderiv⟩
  refine ⟨F, ?_⟩
  rw [hderiv]
  have ha0 : a ≠ 0 := by
    intro hzero
    apply haNot
    exact ⟨x, hx, by simpa [hzero] using E.map_base⟩
  exact omittedPoint_derivative_norm_lt ha hb hbpow ha0 E.deriv_ne_zero

end Submission
