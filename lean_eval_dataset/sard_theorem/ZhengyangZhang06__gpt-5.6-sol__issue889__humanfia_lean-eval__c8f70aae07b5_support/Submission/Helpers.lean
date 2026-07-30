import ChallengeDeps

open LeanEval.Geometry.SardTheoremProblem
open MeasureTheory MeasureTheory.Measure Module Set
open Asymptotics Filter
open scoped ContDiff ENNReal NNReal Topology

namespace Submission.Helpers

universe u v

variable {V W : Type*}

theorem finrank_range_lt_iff_not_surjective
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (A : V →ₗ[ℝ] W) :
    finrank ℝ (LinearMap.range A) < finrank ℝ W ↔ ¬Function.Surjective A := by
  rw [← LinearMap.range_eq_top]
  constructor
  · intro h htop
    rw [htop, finrank_top] at h
    exact h.false
  · intro h
    exact lt_of_le_of_ne (LinearMap.range A).finrank_le fun heq =>
      h (Submodule.eq_top_of_finrank_eq heq)

theorem isOpen_setOf_surjective
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] :
    IsOpen {A : V →L[ℝ] W | Function.Surjective A} := by
  rw [isOpen_iff_mem_nhds]
  intro A hA
  have hsplit : A.HasRightInverse :=
    ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional hA
  let R : W →L[ℝ] V := hsplit.rightInverse
  have hR : Function.RightInverse R A :=
    hsplit.rightInverse_rightInverse
  have hunit : IsUnit (A.comp R) := by
    rw [ContinuousLinearMap.isUnit_iff_bijective]
    have hid : A.comp R = ContinuousLinearMap.id ℝ W := by
      ext y
      exact hR y
    rw [hid]
    exact ⟨fun _ _ h => h, fun y => ⟨y, rfl⟩⟩
  have hcontinuous :
      Continuous (fun B : V →L[ℝ] W => B.comp R) :=
    continuous_id.clm_comp_const R
  have hmem : {B : V →L[ℝ] W | IsUnit (B.comp R)} ∈ 𝓝 A :=
    hcontinuous.continuousAt (Units.isOpen.mem_nhds hunit)
  filter_upwards [hmem] with B hB
  have hsurj : Function.Surjective (B.comp R) :=
    (ContinuousLinearMap.isUnit_iff_bijective.mp hB).2
  intro y
  obtain ⟨z, hz⟩ := hsurj y
  exact ⟨R z, hz⟩

theorem isClosed_setOf_not_surjective
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] :
    IsClosed {A : V →L[ℝ] W | ¬Function.Surjective A} := by
  simpa only [Set.compl_setOf] using
    (isOpen_setOf_surjective (V := V) (W := W)).isClosed_compl

theorem isCompact_not_surjective
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {K : Set V} (hK : IsCompact K) {A : V → V →L[ℝ] W}
    (hA : ContinuousOn A K) :
    IsCompact {x | x ∈ K ∧ ¬Function.Surjective (A x)} := by
  let C : Set K := {x | ¬Function.Surjective (A x)}
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hC : IsClosed C := by
    change IsClosed ((fun x : K => A x) ⁻¹'
      {B : V →L[ℝ] W | ¬Function.Surjective B})
    convert (isClosed_setOf_not_surjective (V := V) (W := W)).preimage
      hA.restrict using 1
    ext x
    rfl
  have hCcompact : IsCompact C := hC.isCompact
  have himage : ((↑) : K → V) '' C =
      {x | x ∈ K ∧ ¬Function.Surjective (A x)} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hxK, hx⟩
      exact ⟨⟨x, hxK⟩, hx, rfl⟩
  rw [← himage]
  exact hCcompact.image continuous_subtype_val

set_option maxHeartbeats 800000 in
theorem OpenPartialHomeomorph.contDiffAt_symm_infty_of_one
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (e : OpenPartialHomeomorph V W) {y : W} (hy : y ∈ e.target)
    (he : ContDiffAt ℝ ∞ e (e.symm y))
    (hesymm : ContDiffAt ℝ 1 e.symm y) :
    ContDiffAt ℝ ∞ e.symm y := by
  let A : V →L[ℝ] W := fderiv ℝ e (e.symm y)
  let B : W →L[ℝ] V := fderiv ℝ e.symm y
  have he' : HasFDerivAt e A (e.symm y) :=
    (he.differentiableAt (by simp)).hasFDerivAt
  have hesymm' : HasFDerivAt e.symm B y :=
    (hesymm.differentiableAt (by simp)).hasFDerivAt
  have hleft_local :
      (e.symm : W → V) ∘ (e : V → W) =ᶠ[𝓝 (e.symm y)] id := by
    filter_upwards [e.open_source.mem_nhds (e.map_target hy)] with x hx
    exact e.left_inv hx
  have hright_local :
      (e : V → W) ∘ (e.symm : W → V) =ᶠ[𝓝 y] id := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    exact e.right_inv hz
  have hleft : B.comp A = ContinuousLinearMap.id ℝ V := by
    have houter : HasFDerivAt e.symm B (e (e.symm y)) := by
      simpa only [e.right_inv hy] using hesymm'
    have hder := (houter.comp (e.symm y) he').fderiv
    rw [hleft_local.fderiv_eq] at hder
    simpa only [fderiv_id] using hder.symm
  have hright : A.comp B = ContinuousLinearMap.id ℝ W := by
    have hder := (he'.comp y hesymm').fderiv
    rw [hright_local.fderiv_eq] at hder
    simpa only [fderiv_id] using hder.symm
  have hinj : Function.Injective A := by
    intro x z hxz
    have h := congrArg B hxz
    simpa only [← ContinuousLinearMap.comp_apply, hleft,
      ContinuousLinearMap.id_apply] using h
  have hsurj : Function.Surjective A := by
    intro z
    refine ⟨B z, ?_⟩
    simp only [← ContinuousLinearMap.comp_apply, hright,
      ContinuousLinearMap.id_apply]
  let Aequiv : V ≃L[ℝ] W :=
    ContinuousLinearEquiv.ofBijective A
      (LinearMap.ker_eq_bot.mpr hinj)
      (LinearMap.range_eq_top.mpr hsurj)
  apply e.contDiffAt_symm hy (f₀' := Aequiv)
  · simpa only [Aequiv, ContinuousLinearEquiv.coe_ofBijective] using he'
  · exact he

theorem volume_eq_zero_of_dimH_lt
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W]
    {s : Set W} (hs : dimH s < (finrank ℝ W : ℝ≥0∞)) : volume s = 0 := by
  have hs' :
      dimH s < ((finrank ℝ W : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_natCast]
    exact hs
  have hzero : μH[(finrank ℝ W : ℕ)] s = 0 := by
    simpa only [NNReal.coe_natCast] using
      (hausdorffMeasure_of_dimH_lt hs')
  rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hzero, smul_zero]

theorem volume_image_eq_zero_of_locally_holder
    [EMetricSpace V] [SecondCountableTopology V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W]
    {r : ℝ≥0} {g : V → W} {s : Set V} (hr : 0 < r)
    (hg : ∀ x ∈ s, ∃ C : ℝ≥0, ∃ t ∈ 𝓝[s] x, HolderOnWith C r g t)
    (hdim : dimH s / (r : ℝ≥0∞) < (finrank ℝ W : ℝ≥0∞)) :
    volume (g '' s) = 0 :=
  volume_eq_zero_of_dimH_lt <|
    (dimH_image_le_of_locally_holder_on hr hg).trans_lt hdim

theorem flat_isLittleO {V W : Type u}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {k : ℕ} {f : V → W} {x : V} (hf : ContDiff ℝ ∞ f)
    (hflat : ∀ i, 1 ≤ i → i ≤ k → iteratedFDeriv ℝ i f x = 0) :
    (fun y => f y - f x) =o[𝓝 x] fun y => ‖y - x‖ ^ k := by
  induction k generalizing f W with
  | zero =>
      simpa only [pow_zero] using
        (Asymptotics.isLittleO_one_iff ℝ).2
          (tendsto_sub_nhds_zero_iff.2 hf.continuous.continuousAt)
  | succ k ih =>
      let g : V → V →L[ℝ] W := fderiv ℝ f
      have hg : ContDiff ℝ ∞ g := hf.fderiv_right (by simp)
      have hgflat : ∀ i, 1 ≤ i → i ≤ k → iteratedFDeriv ℝ i g x = 0 := by
        intro i hi hik
        apply norm_eq_zero.mp
        rw [norm_iteratedFDeriv_fderiv]
        simpa using congrArg norm (hflat (i + 1) (by omega) (by omega))
      have hgx : g x = 0 := by
        apply norm_eq_zero.mp
        rw [← norm_iteratedFDeriv_one]
        simpa using congrArg norm (hflat 1 (by omega) (by omega))
      have hgo : g =o[𝓝 x] fun y => ‖y - x‖ ^ k := by
        simpa only [hgx, sub_zero] using
          ih (W := V →L[ℝ] W) (f := g) hg hgflat
      have hgo' : g =o[𝓝[univ] x] fun y => ‖y - x‖ ^ k := by
        simpa only [nhdsWithin_univ] using hgo
      simpa only [Nat.succ_eq_add_one, nhdsWithin_univ] using
        convex_univ.isLittleO_pow_succ (x₀ := x) (f := f) (f' := g) (s := univ)
          (mem_univ x)
          (fun y _ => by
            simpa only [g] using
              (hf.differentiable (by simp)).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
          hgo'

theorem flat_isLittleO_at {V W : Type u}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {k : ℕ} {f : V → W} {x : V} (hf : ContDiffAt ℝ k f x)
    (hflat : ∀ i, 1 ≤ i → i ≤ k → iteratedFDeriv ℝ i f x = 0) :
    (fun y => f y - f x) =o[𝓝 x] fun y => ‖y - x‖ ^ k := by
  induction k generalizing f W with
  | zero =>
      simpa only [pow_zero] using
        (Asymptotics.isLittleO_one_iff ℝ).2
          (tendsto_sub_nhds_zero_iff.2 hf.continuousAt)
  | succ k ih =>
      let g : V → V →L[ℝ] W := fderiv ℝ f
      have hg : ContDiffAt ℝ k g x := hf.fderiv_right_succ
      have hgflat : ∀ i, 1 ≤ i → i ≤ k → iteratedFDeriv ℝ i g x = 0 := by
        intro i hi hik
        apply norm_eq_zero.mp
        rw [norm_iteratedFDeriv_fderiv]
        simpa using congrArg norm (hflat (i + 1) (by omega) (by omega))
      have hgx : g x = 0 := by
        apply norm_eq_zero.mp
        rw [← norm_iteratedFDeriv_one]
        simpa using congrArg norm (hflat 1 (by omega) (by omega))
      have hgo : g =o[𝓝 x] fun y => ‖y - x‖ ^ k := by
        simpa only [hgx, sub_zero] using
          ih (W := V →L[ℝ] W) (f := g) hg hgflat
      have heventually : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ (k + 1) f y :=
        hf.eventually (by simp)
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp heventually
      have hgo' : g =o[𝓝[Metric.ball x ε] x] fun y => ‖y - x‖ ^ k :=
        hgo.mono nhdsWithin_le_nhds
      have hmain :=
        (convex_ball x ε).isLittleO_pow_succ
          (Metric.mem_ball_self hε)
          (fun y hy => by
            have hycd : ContDiffAt ℝ (k + 1) f y := hball hy
            exact (hycd.differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt)
          hgo'
      rw [Metric.isOpen_ball.nhdsWithin_eq (Metric.mem_ball_self hε)] at hmain
      simpa only [Nat.succ_eq_add_one] using hmain

theorem volume_image_eq_zero_of_locally_null
    [TopologicalSpace V] [SecondCountableTopology V]
    [MeasurableSpace W] {μ : Measure W} {g : V → W} {s : Set V}
    (hg : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, μ (g '' t) = 0) :
    μ (g '' s) = 0 := by
  classical
  let t : V → Set V := fun x =>
    if hx : x ∈ s then Classical.choose (hg x hx) else ∅
  have htx : ∀ x ∈ s, t x ∈ 𝓝[s] x := by
    intro x hx
    simpa only [t, dif_pos hx] using (Classical.choose_spec (hg x hx)).1
  have htzero : ∀ x ∈ s, μ (g '' t x) = 0 := by
    intro x hx
    simpa only [t, dif_pos hx] using (Classical.choose_spec (hg x hx)).2
  obtain ⟨c, hcs, hcc, hcover⟩ :=
    TopologicalSpace.countable_cover_nhdsWithin htx
  refine measure_mono_null (image_mono hcover) ?_
  have himage : g '' (⋃ x ∈ c, t x) = ⋃ x ∈ c, g '' t x := by
    simp only [image_iUnion]
  rw [himage]
  exact (measure_biUnion_null_iff hcc).2 fun x hx => htzero x (hcs hx)

theorem volume_image_eq_zero_of_pointwise_flat
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W]
    {k : ℕ} {g : V → W} {s : Set V} (hk : 0 < k)
    (hdim :
      (finrank ℝ V : ℝ≥0∞) / (k : ℝ≥0) < (finrank ℝ W : ℝ≥0∞))
    (hg : ∀ x ∈ s,
      (fun y => g y - g x) =o[𝓝 x] fun y => ‖y - x‖ ^ k) :
    volume (g '' s) = 0 := by
  let u : ℕ → Set V := fun n =>
    {x | x ∈ s ∧ ∀ y ∈ s,
      dist y x < 1 / (n + 1 : ℝ) →
        dist (g y) (g x) ≤ dist y x ^ k}
  have hsu : s ⊆ ⋃ n, u n := by
    intro x hx
    obtain ⟨ε, hε, hbound⟩ :=
      Metric.mem_nhds_iff.mp (hg x hx).eventuallyLE
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    refine mem_iUnion.2 ⟨n, hx, ?_⟩
    intro y hy hyx
    have hyε : y ∈ Metric.ball x ε := by
      rw [Metric.mem_ball]
      exact hyx.trans hn
    have hb := hbound hyε
    change ‖g y - g x‖ ≤ ‖‖y - x‖ ^ k‖ at hb
    simpa only [dist_eq_norm, Real.norm_eq_abs, abs_pow, abs_norm] using hb
  have hu : ∀ n, volume (g '' u n) = 0 := by
    intro n
    apply volume_image_eq_zero_of_locally_holder (r := (k : ℝ≥0))
    · exact_mod_cast hk
    · intro x hx
      let r : ℝ := 1 / (2 * (n + 1 : ℝ))
      have hr : 0 < r := by positivity
      refine ⟨1, u n ∩ Metric.ball x r,
        inter_mem_nhdsWithin _ (Metric.ball_mem_nhds x hr), ?_⟩
      intro y hy z hz
      have hzy : dist z y < 1 / (n + 1 : ℝ) := calc
        dist z y ≤ dist z x + dist x y := dist_triangle z x y
        _ < r + r := add_lt_add hz.2 (by simpa [dist_comm] using hy.2)
        _ = 1 / (n + 1 : ℝ) := by
          dsimp only [r]
          field_simp
          norm_num
      have hdist := hy.1.2 z hz.1.1 hzy
      rw [edist_dist, edist_dist, ENNReal.coe_one, one_mul,
        ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by simpa [dist_comm] using hdist)
    · calc
        dimH (u n) / (k : ℝ≥0) ≤
            (finrank ℝ V : ℝ≥0∞) / (k : ℝ≥0) := by
          gcongr
          simpa only [Real.dimH_univ_eq_finrank] using
            (dimH_mono (subset_univ (u n)))
        _ < (finrank ℝ W : ℝ≥0∞) := hdim
  refine measure_mono_null (image_mono hsu) ?_
  rw [image_iUnion]
  exact measure_iUnion_null hu

theorem volume_image_eq_zero_of_flat_stratum
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {f : V → ℝ} (hf : ContDiff ℝ ∞ f) :
    volume
      (f '' {x | ∀ i, 1 ≤ i → i ≤ finrank ℝ V + 1 →
        iteratedFDeriv ℝ i f x = 0}) = 0 := by
  apply volume_image_eq_zero_of_pointwise_flat
      (k := finrank ℝ V + 1) (by omega)
  · rw [finrank_self]
    apply (ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp))).2
    norm_cast
    omega
  · intro x hx
    exact flat_isLittleO hf hx

theorem volume_image_eq_zero_of_flat_on
    {V W : Type u}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W]
    {k : ℕ} {g : V → W} {s : Set V} (hk : 0 < k)
    (hdim :
      (finrank ℝ V : ℝ≥0∞) / (k : ℝ≥0) < (finrank ℝ W : ℝ≥0∞))
    (hg : ∀ x ∈ s, ContDiffAt ℝ ∞ g x)
    (hflat : ∀ x ∈ s, ∀ i, 1 ≤ i → i ≤ k →
      iteratedFDeriv ℝ i g x = 0) :
    volume (g '' s) = 0 := by
  apply volume_image_eq_zero_of_pointwise_flat hk hdim
  intro x hx
  exact flat_isLittleO_at (V := V) (W := W) (k := k) (f := g) (x := x)
    ((hg x hx).of_le
      (show (k : ℕ∞ω) ≤ (∞ : ℕ∞ω) from mod_cast le_top)) (hflat x hx)

theorem volume_range_eq_zero_of_contDiff_of_lt {m n : ℕ} (f : E m → E n)
    (hf : ContDiff ℝ 1 f) (hmn : m < n) : volume (range f) = 0 := by
  have hdim : dimH (range f) < (n : ℝ≥0∞) := by
    refine hf.dimH_range_le.trans_lt ?_
    simpa only [finrank_euclideanSpace_fin] using
      (Nat.cast_lt.mpr hmn : (m : ℝ≥0∞) < n)
  apply volume_eq_zero_of_dimH_lt
  simpa only [finrank_euclideanSpace_fin] using hdim

theorem det_fderiv_eq_zero_of_rank_lt {n : ℕ} {f : E n → E n} {x : E n}
    (hx : fderivRank f x < n) : (fderiv ℝ f x).det = 0 := by
  apply LinearMap.det_eq_zero_iff_ker_ne_bot.mpr
  intro hker
  have hinj : Function.Injective (fderiv ℝ f x).toLinearMap :=
    LinearMap.ker_eq_bot.mp hker
  have hrange := LinearMap.finrank_range_of_inj hinj
  rw [finrank_euclideanSpace_fin] at hrange
  exact hx.ne (by simpa only [fderivRank] using hrange)

end Submission.Helpers
