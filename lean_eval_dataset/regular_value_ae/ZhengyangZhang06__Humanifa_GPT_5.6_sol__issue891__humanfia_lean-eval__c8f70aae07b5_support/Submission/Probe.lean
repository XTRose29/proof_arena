import Mathlib

open Filter MeasureTheory Module Set
open scoped ContDiff ENNReal NNReal Topology

namespace Submission.Helpers

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def CriticalSet (f : E → ℝ) : Set E := {x | fderiv ℝ f x = 0}

def JetZeroSet (f : E → ℝ) (n : ℕ) : Set E :=
  {x | ∀ k, 1 ≤ k → k ≤ n → iteratedFDeriv ℝ k f x = 0}

def sardOrder : ℕ → ℕ
  | 0 => 1
  | d + 1 => sardOrder d + (d + 1)

lemma sardOrder_pos (d : ℕ) : 0 < sardOrder d := by
  induction d with
  | zero => simp [sardOrder]
  | succ d ih =>
      simp only [sardOrder]
      omega

lemma dimension_succ_le_sardOrder (d : ℕ) : d + 1 ≤ sardOrder d := by
  induction d with
  | zero => simp [sardOrder]
  | succ d ih =>
      simp only [sardOrder]
      omega

lemma sardOrder_pred_add_le {d k : ℕ} (hd : 1 ≤ d) (hk : k ≤ d) :
    sardOrder (d - 1) + k ≤ sardOrder d := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  simp only [Nat.succ_sub_one, sardOrder]
  omega

lemma criticalSet_eq_jetZeroSet_one (f : E → ℝ) :
    CriticalSet f = JetZeroSet f 1 := by
  ext x
  simp only [CriticalSet, JetZeroSet, mem_setOf_eq]
  constructor
  · intro hx k hk₁ hk
    have : k = 1 := by omega
    subst k
    apply ContinuousMultilinearMap.ext
    intro w
    rw [iteratedFDeriv_one_apply]
    change fderiv ℝ f x (w 0) = 0
    rw [hx]
    rfl
  · intro hx
    ext v
    let w : Fin 1 → E := fun _ ↦ v
    have h := congr_arg (fun A ↦ A w) (hx 1 le_rfl le_rfl)
    rw [iteratedFDeriv_one_apply] at h
    change fderiv ℝ f x v = 0 at h
    change fderiv ℝ f x v = 0
    exact h

lemma jetZeroSet_mono (f : E → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    JetZeroSet f n ⊆ JetZeroSet f m := by
  intro x hx k hk₁ hk
  exact hx k hk₁ (hk.trans hmn)

lemma jetZeroSet_one_subset_flat_or_strata (f : E → ℝ) (d : ℕ) :
    JetZeroSet f 1 ⊆
      JetZeroSet f (d + 1) ∪
        ⋃ k ∈ Set.Icc 1 d, JetZeroSet f k \ JetZeroSet f (k + 1) := by
  classical
  intro x hx
  by_cases hflat : x ∈ JetZeroSet f (d + 1)
  · exact Or.inl hflat
  · right
    simp only [JetZeroSet, mem_setOf_eq] at hflat
    push Not at hflat
    obtain ⟨j, hj₁, hjd, hjne⟩ := hflat
    have hex : ∃ j, 1 ≤ j ∧ j ≤ d + 1 ∧ iteratedFDeriv ℝ j f x ≠ 0 :=
      ⟨j, hj₁, hjd, hjne⟩
    let k := Nat.find hex
    have hk_spec := Nat.find_spec hex
    change 1 ≤ k ∧ k ≤ d + 1 ∧ iteratedFDeriv ℝ k f x ≠ 0 at hk_spec
    have hkpos : 1 ≤ k := hk_spec.1
    have hk_le : k ≤ d + 1 := hk_spec.2.1
    have hk_ne : iteratedFDeriv ℝ k f x ≠ 0 := hk_spec.2.2
    have hk1 : 1 ≤ k - 1 := by
      have hk_ne_one : k ≠ 1 := by
        intro hk_eq
        exact hk_ne (hk_eq.symm ▸ hx 1 le_rfl le_rfl)
      omega
    have hkd : k - 1 ≤ d := by omega
    apply mem_iUnion_of_mem (k - 1)
    apply mem_iUnion_of_mem ⟨hk1, hkd⟩
    constructor
    · intro j' hj'₁ hj'k
      by_contra hj'ne
      have hj'lt : j' < k := by omega
      have hkle := Nat.find_min' hex ⟨hj'₁, by omega, hj'ne⟩
      change k ≤ j' at hkle
      exact (not_le_of_gt hj'lt) hkle
    · intro hzero
      exact hk_ne (hzero k hkpos (by omega))

lemma exists_scalar_jet {f : E → ℝ} {x : E} {k : ℕ} {m n : ℕ∞ω}
    (hf : ContDiffAt ℝ n f x) (hm : 1 ≤ m) (hmk : m + k ≤ n)
    (hk : iteratedFDeriv ℝ k f x = 0)
    (hk₁ : iteratedFDeriv ℝ (k + 1) f x ≠ 0) :
    ∃ g : E → ℝ, ContDiffAt ℝ m g x ∧ g x = 0 ∧ fderiv ℝ g x ≠ 0 ∧
      ∀ y, iteratedFDeriv ℝ k f y = 0 → g y = 0 := by
  classical
  let j : E → E [×k]→L[ℝ] ℝ := iteratedFDeriv ℝ k f
  let A : E →L[ℝ] E [×k]→L[ℝ] ℝ := fderiv ℝ j x
  have hj : ContDiffAt ℝ m j x := by
    exact hf.iteratedFDeriv_right hmk
  have hA : A ≠ 0 := by
    intro hA
    apply hk₁
    apply norm_eq_zero.mp
    rw [← norm_fderiv_iteratedFDeriv (f := f) (x := x) (n := k)]
    change ‖A‖ = 0
    rw [hA]
    exact @norm_zero (E →L[ℝ] E [×k]→L[ℝ] ℝ) _
  obtain ⟨v, hv⟩ : ∃ v, A v ≠ 0 := by
    by_contra h
    push Not at h
    apply hA
    exact ContinuousLinearMap.ext fun v ↦ h v
  obtain ⟨L, -, hL⟩ := exists_dual_vector ℝ (A v) (norm_ne_zero_iff.mpr hv)
  let g : E → ℝ := fun y ↦ L (j y)
  have hg : ContDiffAt ℝ m g x := by
    exact L.contDiff.contDiffAt.comp x hj
  have hj' : HasFDerivAt j A x := by
    exact (hj.differentiableAt (zero_lt_one.trans_le hm).ne').hasFDerivAt
  have hg' : HasFDerivAt g (L.comp A) x := by
    exact L.hasFDerivAt.comp x hj'
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · change L (j x) = 0
    change L (iteratedFDeriv ℝ k f x) = 0
    rw [hk, map_zero]
  · rw [hg'.fderiv]
    intro hzero
    have hz := congr_arg (fun T : E →L[ℝ] ℝ ↦ T v) hzero
    change L (A v) = 0 at hz
    exact (norm_ne_zero_iff.mpr hv) (hL.symm.trans hz)
  · intro y hy
    change L (j y) = 0
    change L (iteratedFDeriv ℝ k f y) = 0
    rw [hy, map_zero]

lemma exists_implicit_parametrization [FiniteDimensional ℝ E] {n : ℕ∞ω}
    {g : E → ℝ} {x : E} (hg : ContDiffAt ℝ n g x) (hn : n ≠ 0)
    (hg' : fderiv ℝ g x ≠ 0) :
    ∃ (ψ : (fderiv ℝ g x).ker → E) (r : E → (fderiv ℝ g x).ker),
      ContDiffAt ℝ n ψ 0 ∧ ContinuousAt r x ∧ r x = 0 ∧ ψ 0 = x ∧
        ∀ᶠ y in 𝓝 x, g y = g x → ψ (r y) = y := by
  letI := FiniteDimensional.complete ℝ E
  let g' : E →L[ℝ] ℝ := fderiv ℝ g x
  have hsurj : g'.range = ⊤ := by
    apply Module.Dual.range_eq_top_of_ne_zero
    intro hzero
    apply hg'
    change g' = 0
    apply ContinuousLinearMap.ext
    intro y
    exact LinearMap.congr_fun hzero y
  have hstrict : HasStrictFDerivAt g g' x := hg.hasStrictFDerivAt hn
  let hker := g'.ker_closedComplemented_of_finiteDimensional_range
  let φ := hstrict.implicitFunctionDataOfComplemented g g' hsurj hker
  let ψ : g'.ker → E := φ.implicitFunction (g x)
  let r : E → g'.ker := φ.rightFun
  have hleft : ContDiffAt ℝ n φ.leftFun φ.pt := by
    simpa [φ] using hg
  have hright : ContDiffAt ℝ n φ.rightFun φ.pt := by
    change ContDiffAt ℝ n (fun y ↦ Classical.choose hker (y - x)) x
    fun_prop
  have huncurry :
      ContDiffAt ℝ n φ.implicitFunction.uncurry (φ.prodFun φ.pt) :=
    φ.contDiffAt_implicitFunction hleft hright hn
  have hprod : φ.prodFun φ.pt = (g x, (0 : g'.ker)) := by
    simp [φ, ImplicitFunctionData.prodFun]
  have hψ : ContDiffAt ℝ n ψ 0 := by
    rw [hprod] at huncurry
    have hpair :
        ContDiffAt ℝ n (fun z : g'.ker ↦ (g x, z)) 0 :=
      contDiffAt_const.prodMk
        (contDiffAt_id : ContDiffAt ℝ n id (0 : g'.ker))
    have hcomp := huncurry.comp 0 hpair
    simpa only [ψ, Function.comp_def, Function.uncurry_apply_pair] using hcomp
  have hr : ContinuousAt r x := hright.continuousAt
  have hrx : r x = 0 := by
    simp [r, φ]
  have hψx : ψ 0 = x := by
    simpa [ψ, φ] using φ.implicitFunction_apply_image.self_of_nhds
  have hevent : ∀ᶠ y in 𝓝 x, g y = g x → ψ (r y) = y := by
    filter_upwards [φ.leftFun_eq_iff_implicitFunction] with y hy
    simpa [ψ, r, φ] using hy.mp
  exact ⟨ψ, r, hψ, hr, hrx, hψx, hevent⟩

omit [NormedSpace ℝ E] in
lemma measure_image_eq_zero_of_locally
    [SecondCountableTopology E] (μ : Measure ℝ) (f : E → ℝ) (s : Set E)
    (h : ∀ x ∈ s, ∃ u ∈ 𝓝 x, μ (f '' (s ∩ u)) = 0) :
    μ (f '' s) = 0 := by
  classical
  let u : E → Set E := fun x ↦ if hx : x ∈ s then Classical.choose (h x hx) else univ
  have hu : ∀ x ∈ s, u x ∈ 𝓝 x := by
    intro x hx
    simpa only [u, dif_pos hx] using (Classical.choose_spec (h x hx)).1
  have hnull : ∀ x ∈ s, μ (f '' (s ∩ u x)) = 0 := by
    intro x hx
    simpa only [u, dif_pos hx] using (Classical.choose_spec (h x hx)).2
  obtain ⟨t, hts, htc, hcover⟩ :=
    TopologicalSpace.countable_cover_nhdsWithin
      (fun x hx ↦ mem_nhdsWithin_of_mem_nhds (hu x hx))
  have hscover : s ⊆ ⋃ x ∈ t, s ∩ u x := by
    intro y hy
    obtain ⟨x, hxt, hyu⟩ := mem_iUnion₂.mp (hcover hy)
    apply mem_iUnion_of_mem x
    apply mem_iUnion_of_mem hxt
    exact ⟨hy, hyu⟩
  apply measure_mono_null
    (show f '' s ⊆ ⋃ x ∈ t, f '' (s ∩ u x) by
      rw [← image_iUnion₂]
      exact image_mono hscover)
  exact (measure_biUnion_null_iff htc).2 fun x hx ↦ hnull x (hts hx)

lemma flat_isLittleOWithin
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {s : Set E} {x : E} {n : ℕ}
    (hs : Convex ℝ s) (hu : UniqueDiffOn ℝ s) (hx : x ∈ s)
    (hf : ContDiffOn ℝ n f s)
    (hz : ∀ k, 1 ≤ k → k ≤ n → iteratedFDerivWithin ℝ k f s x = 0) :
    (fun y ↦ f y - f x) =o[𝓝[s] x] fun y ↦ ‖y - x‖ ^ n := by
  induction n generalizing F f with
  | zero =>
      simp only [pow_zero, Asymptotics.isLittleO_one_iff]
      rw [tendsto_sub_nhds_zero_iff]
      exact hf.continuousOn.continuousWithinAt hx
  | succ n ih =>
      let f' : E → E →L[ℝ] F := fderivWithin ℝ f s
      have hf' : ContDiffOn ℝ n f' s := by
        exact hf.fderivWithin hu (by simp)
      have hz' :
          ∀ k, 1 ≤ k → k ≤ n → iteratedFDerivWithin ℝ k f' s x = 0 := by
        intro k hk₁ hkn
        apply norm_eq_zero.mp
        rw [norm_iteratedFDerivWithin_fderivWithin hu hx]
        exact norm_eq_zero.mpr (hz (k + 1) (by omega) (by omega))
      have ho :=
        ih hf' hz'
      have hfx' : f' x = 0 := by
        apply ContinuousLinearMap.ext
        intro v
        let w : Fin 1 → E := fun _ ↦ v
        have h := congr_arg
          (fun A : E [×1]→L[ℝ] F ↦ A w)
          (hz 1 le_rfl (by omega))
        rw [iteratedFDerivWithin_one_apply (hu x hx)] at h
        exact h
      have ho' : f' =o[𝓝[s] x] fun y ↦ ‖y - x‖ ^ n := by
        simpa only [hfx', sub_zero] using ho
      apply hs.isLittleO_pow_succ hx _ ho'
      intro y hy
      exact (hf.differentiableOn (by simp) y hy).hasFDerivWithinAt

lemma flat_eventually_norm_sub_le
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x : E} {n : ℕ}
    (hf : ContDiffAt ℝ n f x)
    (hz : ∀ k, 1 ≤ k → k ≤ n → iteratedFDeriv ℝ k f x = 0) :
    ∀ᶠ y in 𝓝 x, ‖f y - f x‖ ≤ ‖y - x‖ ^ n := by
  rcases hf.contDiffOn' le_rfl (by simp) with ⟨u, hu, hxu, hfu⟩
  obtain ⟨ε, hε, hεu⟩ := Metric.isOpen_iff.mp hu x hxu
  let b := Metric.ball x ε
  have hb : IsOpen b := Metric.isOpen_ball
  have hxb : x ∈ b := Metric.mem_ball_self hε
  have hfb : ContDiffOn ℝ n f b := hfu.mono fun y hy ↦ ⟨by simp, hεu hy⟩
  have hzb :
      ∀ k, 1 ≤ k → k ≤ n → iteratedFDerivWithin ℝ k f b x = 0 := by
    intro k hk₁ hkn
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hb.uniqueDiffOn
      (hf.of_le (by exact_mod_cast hkn)) hxb]
    exact hz k hk₁ hkn
  have ho :=
    flat_isLittleOWithin (convex_ball x ε) hb.uniqueDiffOn hxb hfb hzb
  have hnhds : 𝓝[b] x = 𝓝 x := hb.nhdsWithin_eq hxb
  rw [hnhds] at ho
  have h := (Asymptotics.isLittleO_iff.mp ho) zero_lt_one
  simpa only [one_mul, norm_pow, norm_norm] using h

def FlatPiece (f : E → ℝ) (s : Set E) (n i : ℕ) : Set E :=
  {x | 0 < i ∧ x ∈ s ∧ x ∈ JetZeroSet f n ∧
    ∀ y, dist y x < (i : ℝ)⁻¹ →
      dist (f y) (f x) ≤ dist y x ^ n}

lemma jetZeroSet_subset_iUnion_flatPiece
    {f : E → ℝ} {s : Set E} {n : ℕ}
    (hf : ∀ x ∈ s ∩ JetZeroSet f n, ContDiffAt ℝ n f x) :
    s ∩ JetZeroSet f n ⊆ ⋃ i, FlatPiece f s n i := by
  intro x hx
  have he := flat_eventually_norm_sub_le
    (E := E) (F := ℝ) (f := f) (x := x) (n := n) (hf x hx) hx.2
  rw [Metric.eventually_nhds_iff] at he
  obtain ⟨ε, hε, he⟩ := he
  obtain ⟨i, hi⟩ := exists_nat_gt (max ε⁻¹ 1)
  have hi₁ : (1 : ℝ) < i := (le_max_right ε⁻¹ 1).trans_lt hi
  have hi_pos : 0 < i := by exact_mod_cast (zero_lt_one.trans hi₁)
  have hi_pos_real : (0 : ℝ) < i := by exact_mod_cast hi_pos
  have hei : ε⁻¹ < (i : ℝ) := (le_max_left ε⁻¹ 1).trans_lt hi
  have hinv : (i : ℝ)⁻¹ < ε := (inv_lt_comm₀ hi_pos_real hε).mpr hei
  apply mem_iUnion_of_mem i
  refine ⟨hi_pos, hx.1, hx.2, ?_⟩
  intro y hy
  simpa only [dist_eq_norm] using he (hy.trans hinv)

lemma flatPiece_holderOn
    {f : E → ℝ} {s : Set E} {n i : ℕ} {x : E}
    (hx : x ∈ FlatPiece f s n i) :
    ∃ t ∈ 𝓝[FlatPiece f s n i] x,
      HolderOnWith 1 (n : ℝ≥0) f t := by
  have hi : (0 : ℝ) < i := by exact_mod_cast hx.1
  let r : ℝ := (2 * (i : ℝ))⁻¹
  have hr : 0 < r := by positivity
  let t := FlatPiece f s n i ∩ Metric.ball x r
  refine ⟨t, ?_, ?_⟩
  · exact inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hr))
  · intro p hp q hq
    have hpx : dist p x < r := hp.2
    have hqx : dist q x < r := hq.2
    have hradius : r + r = (i : ℝ)⁻¹ := by
      dsimp [r]
      field_simp
      norm_num
    have hpq : dist q p < (i : ℝ)⁻¹ := by
      calc
        dist q p ≤ dist q x + dist x p := dist_triangle q x p
        _ < r + r := add_lt_add hqx (by simpa only [dist_comm] using hpx)
        _ = (i : ℝ)⁻¹ := hradius
    have hreal := hp.1.2.2.2 q hpq
    rw [edist_dist, edist_dist, ENNReal.coe_one, one_mul,
      show ((n : ℝ≥0) : ℝ) = (n : ℝ) by norm_num,
      ENNReal.rpow_natCast, ← ENNReal.ofReal_pow dist_nonneg]
    exact ENNReal.ofReal_le_ofReal (by simpa only [dist_comm] using hreal)

set_option maxHeartbeats 800000 in
lemma measure_image_jetZeroSet_eq_zero
    [FiniteDimensional ℝ E] {f : E → ℝ} {s : Set E} {n : ℕ}
    (hn : finrank ℝ E < n)
    (hf : ∀ x ∈ s ∩ JetZeroSet f n, ContDiffAt ℝ n f x) :
    volume (f '' (s ∩ JetZeroSet f n)) = 0 := by
  have hn₀ : 0 < n := (Nat.zero_le _).trans_lt hn
  have hr : (0 : ℝ≥0) < n := by exact_mod_cast hn₀
  have hpiece : ∀ i, volume (f '' FlatPiece f s n i) = 0 := by
    intro i
    have hdim :
        dimH (f '' FlatPiece f s n i) ≤
          (finrank ℝ E : ℝ≥0∞) / (n : ℝ≥0) := by
      refine (dimH_image_le_of_locally_holder_on hr fun x hx ↦
        ⟨1, flatPiece_holderOn (f := f) (s := s) (n := n) (i := i) hx⟩).trans ?_
      gcongr
      exact (dimH_mono (subset_univ _)).trans_eq
        (Real.dimH_univ_eq_finrank E)
    have hratio :
        (finrank ℝ E : ℝ≥0∞) / (n : ℝ≥0) < 1 := by
      apply (ENNReal.div_lt_iff (Or.inl (by positivity)) (Or.inl (by simp))).mpr
      simpa using (show (finrank ℝ E : ℝ≥0∞) < n by exact_mod_cast hn)
    apply measure_zero_of_dimH_lt (μ := volume) _ (hdim.trans_lt hratio)
    simpa only [NNReal.coe_one, hausdorffMeasure_real] using
      (Measure.AbsolutelyContinuous.rfl : volume ≪ volume)
  apply measure_mono_null
    (show f '' (s ∩ JetZeroSet f n) ⊆ ⋃ i, f '' FlatPiece f s n i by
      rw [← image_iUnion]
      exact image_mono (jetZeroSet_subset_iUnion_flatPiece hf))
  exact measure_iUnion_null hpiece

end Submission.Helpers
