import Submission.Laplacian

namespace Submission.Helpers

open Filter
open scoped ContDiff InnerProductSpace Topology

attribute [fun_prop] ContDiff.inner ContDiffAt.inner

/-- A positive cosine weight on a sufficiently narrow slab. -/
noncomputable def cosineSlabBarrier
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E) (α a : ℝ) (x : E) : ℝ :=
  Real.cos (α * (⟪x, e⟫_ℝ - a))

lemma contDiff_cosineSlabBarrier
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E) (α a : ℝ) :
    ContDiff ℝ ∞ (cosineSlabBarrier e α a) := by
  unfold cosineSlabBarrier
  have hinner : ContDiff ℝ ∞ (fun x : E ↦ ⟪x, e⟫_ℝ) :=
    contDiff_id.inner ℝ contDiff_const
  exact Real.contDiff_cos.comp
    (contDiff_const.mul (hinner.sub contDiff_const))

lemma iteratedFDeriv_cosineSlabBarrier_two_apply_self
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e v x : E) (α a : ℝ) :
    iteratedFDeriv ℝ 2 (cosineSlabBarrier e α a) x ![v, v] =
      -(α * ⟪v, e⟫_ℝ) ^ 2 * cosineSlabBarrier e α a x := by
  let A : ℝ := α * (⟪x, e⟫_ℝ - a)
  let B : ℝ := α * ⟪v, e⟫_ℝ
  let q : ℝ → ℝ := fun t ↦ A + t * B
  have hq (t : ℝ) : HasDerivAt q B t := by
    have hbase :
        HasDerivAt
          ((fun _ : ℝ ↦ A) + fun s : ℝ ↦ s * B) B t :=
      ((hasDerivAt_const t A).add
        ((hasDerivAt_id' t).mul_const B)).congr_deriv (by ring)
    apply hbase.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun s ↦ by rfl
  have hcosline :
      cosineSlabBarrier e α a ∘ (fun t : ℝ ↦ x + t • v) =
        fun t ↦ Real.cos (q t) := by
    funext t
    apply congrArg Real.cos
    dsimp [cosineSlabBarrier, q, A, B, Function.comp_def]
    rw [inner_add_left, real_inner_smul_left]
    ring
  have hfirst : deriv (fun t ↦ Real.cos (q t)) =
      fun t ↦ -Real.sin (q t) * B := by
    funext t
    exact (hq t).cos.deriv
  have hsecond (t : ℝ) :
      HasDerivAt (fun s ↦ -Real.sin (q s) * B)
        (-(B ^ 2) * Real.cos (q t)) t := by
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using
      ((hq t).sin.fun_neg.mul_const B)
  rw [← iteratedDeriv_comp_affineLine_two (v := v)
    ((contDiff_cosineSlabBarrier e α a).contDiffAt.of_le
      (WithTop.coe_le_coe.2 (OrderTop.le_top (α := ℕ∞) 2)))]
  rw [hcosline]
  have htarget :
      -(α * ⟪v, e⟫_ℝ) ^ 2 * cosineSlabBarrier e α a x =
        -(B ^ 2) * Real.cos (q 0) := by
    simp [A, B, q, cosineSlabBarrier]
  rw [htarget]
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_one, hfirst]
  exact (hsecond 0).deriv

/-- The cosine slab weight is an eigenfunction of the Laplacian. -/
lemma laplacian_cosineSlabBarrier
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (e : E) (α a : ℝ) (he : ‖e‖ = 1)
    (x : E) :
    Laplacian.laplacian (cosineSlabBarrier e α a) x =
      -(α ^ 2) * cosineSlabBarrier e α a x := by
  rw [congrFun
    (InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis
      (cosineSlabBarrier e α a)) x]
  simp_rw [iteratedFDeriv_cosineSlabBarrier_two_apply_self]
  calc
    ∑ i, -(α * ⟪(stdOrthonormalBasis ℝ E) i, e⟫_ℝ) ^ 2 *
          cosineSlabBarrier e α a x =
        (-(α ^ 2) * cosineSlabBarrier e α a x) *
          ∑ i, ⟪(stdOrthonormalBasis ℝ E) i, e⟫_ℝ ^ 2 := by
            simp_rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = -(α ^ 2) * cosineSlabBarrier e α a x := by
      rw [(stdOrthonormalBasis ℝ E).sum_sq_inner_right, he]
      norm_num

lemma cosineSlabBarrier_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {e x : E} {α a b : ℝ} (hα : 0 < α)
    (hx : a ≤ ⟪x, e⟫_ℝ ∧ ⟪x, e⟫_ℝ ≤ b)
    (hwidth : α * (b - a) < Real.pi / 2) :
    0 < cosineSlabBarrier e α a x := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have hnonneg : 0 ≤ α * (⟪x, e⟫_ℝ - a) :=
      mul_nonneg hα.le (sub_nonneg.mpr hx.1)
    nlinarith [Real.pi_pos]
  · have hle : α * (⟪x, e⟫_ℝ - a) ≤ α * (b - a) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right hx.2 a) hα.le
    exact lt_of_le_of_lt hle hwidth

/-- At a local minimum of the second factor, the mixed first-derivative
term in the Laplacian product rule vanishes. -/
lemma laplacian_mul_of_isLocalMin_right
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {φ z : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ 2 φ x) (hz : ContDiffAt ℝ 2 z x)
    (hmin : IsLocalMin z x) :
    Laplacian.laplacian (fun y ↦ φ y * z y) x =
      φ x * Laplacian.laplacian z x +
        z x * Laplacian.laplacian φ x := by
  rw [congrFun
    (InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis
      (fun y ↦ φ y * z y)) x]
  rw [congrFun
    (InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis z)
      x]
  rw [congrFun
    (InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis φ)
      x]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  let v := (stdOrthonormalBasis ℝ E) i
  let line : ℝ → E := fun t ↦ x + t • v
  have hline : ContDiffAt ℝ 2 line 0 := by
    fun_prop
  have hφline : ContDiffAt ℝ 2 (φ ∘ line) 0 := by
    have hφAtLine : ContDiffAt ℝ 2 φ (line 0) := by
      simpa [line] using hφ
    exact hφAtLine.comp 0 hline
  have hzline : ContDiffAt ℝ 2 (z ∘ line) 0 := by
    have hzAtLine : ContDiffAt ℝ 2 z (line 0) := by
      simpa [line] using hz
    exact hzAtLine.comp 0 hline
  have hminline : IsLocalMin (z ∘ line) 0 := by
    have hminAtLine : IsLocalMin z (line 0) := by
      simpa [line] using hmin
    exact hminAtLine.comp_continuous hline.continuousAt
  have hzprime : deriv (z ∘ line) 0 = 0 :=
    hminline.deriv_eq_zero
  have hzprime' :
      deriv (fun t : ℝ ↦ z (x + t • v)) 0 = 0 := by
    simpa [line, Function.comp_def] using hzprime
  have hmul := iteratedDeriv_mul (n := 2) hφline hzline
  have hmul_product :
      iteratedDeriv 2 ((φ ∘ line) * (z ∘ line)) 0 =
        φ x * iteratedDeriv 2 (z ∘ line) 0 +
          z x * iteratedDeriv 2 (φ ∘ line) 0 := by
    rw [hmul]
    simp [Finset.sum_range_succ, hzprime', line, Function.comp_def]
    ring
  have hmulfun :
      ((fun y ↦ φ y * z y) ∘ line) =
        (φ ∘ line) * (z ∘ line) := by
    funext t
    rfl
  have hmul' :
      iteratedDeriv 2 ((fun y ↦ φ y * z y) ∘ line) 0 =
        φ x * iteratedDeriv 2 (z ∘ line) 0 +
          z x * iteratedDeriv 2 (φ ∘ line) 0 := by
    rw [hmulfun]
    exact hmul_product
  rw [iteratedDeriv_comp_affineLine_two (v := v) (hφ.mul hz),
    iteratedDeriv_comp_affineLine_two (v := v) hz,
    iteratedDeriv_comp_affineLine_two (v := v) hφ] at hmul'
  simpa [v, mul_comm, mul_left_comm, mul_assoc] using hmul'

/-- A weak maximum principle on a compact set contained in a sufficiently
narrow slab. Points where the candidate is negative are required to be
interior points of the compact set; this boundary formulation is convenient
for moving-plane caps. -/
lemma nonneg_of_narrow_slab
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {S : Set E} {w c : E → ℝ}
    {e : E} {α a b : ℝ}
    (hScompact : IsCompact S)
    (hslab : ∀ x ∈ S, a ≤ ⟪x, e⟫_ℝ ∧ ⟪x, e⟫_ℝ ≤ b)
    (he : ‖e‖ = 1) (hα : 0 < α)
    (hwidth : α * (b - a) < Real.pi / 2)
    (hwcont : ContinuousOn w S)
    (hwc2 : ∀ x ∈ S, w x < 0 → ContDiffAt ℝ 2 w x)
    (hnegativeInterior : ∀ x ∈ S, w x < 0 → S ∈ 𝓝 x)
    (hc : ∀ x ∈ S, w x < 0 → c x < α ^ 2)
    (hpde : ∀ x ∈ S, w x < 0 →
      Laplacian.laplacian w x + c x * w x ≤ 0) :
    ∀ x ∈ S, 0 ≤ w x := by
  let φ : E → ℝ := cosineSlabBarrier e α a
  let z : E → ℝ := fun x ↦ w x / φ x
  have hφpos : ∀ x ∈ S, 0 < φ x := by
    intro x hx
    exact cosineSlabBarrier_pos hα (hslab x hx) hwidth
  have hφcont : Continuous φ :=
    (contDiff_cosineSlabBarrier e α a).continuous
  have hzcont : ContinuousOn z S := by
    exact hwcont.div hφcont.continuousOn fun x hx ↦
      (hφpos x hx).ne'
  intro x hx
  by_contra hnot
  have hwxneg : w x < 0 := lt_of_not_ge hnot
  have hzxneg : z x < 0 := by
    exact div_neg_of_neg_of_pos hwxneg (hφpos x hx)
  obtain ⟨y, hyS, hymin⟩ :=
    hScompact.exists_isMinOn ⟨x, hx⟩ hzcont
  have hzyneg : z y < 0 :=
    lt_of_le_of_lt (hymin hx) hzxneg
  have hφypos : 0 < φ y := hφpos y hyS
  have hwy_eq : w y = z y * φ y := by
    dsimp [z]
    field_simp
  have hwyneg : w y < 0 := by
    rw [hwy_eq]
    exact mul_neg_of_neg_of_pos hzyneg hφypos
  have hlocal : IsLocalMin z y := by
    filter_upwards [hnegativeInterior y hyS hwyneg] with q hq
    exact hymin hq
  have hφc2 : ContDiffAt ℝ 2 φ y :=
    (contDiff_cosineSlabBarrier e α a).contDiffAt.of_le
      (WithTop.coe_le_coe.2 (OrderTop.le_top (α := ℕ∞) 2))
  have hwc2y : ContDiffAt ℝ 2 w y := hwc2 y hyS hwyneg
  have hzc2 : ContDiffAt ℝ 2 z y := by
    exact hwc2y.div hφc2 hφypos.ne'
  have hlapz : 0 ≤ Laplacian.laplacian z y :=
    laplacian_nonneg_of_isLocalMin hzc2 hlocal
  have hprod :
      Laplacian.laplacian (fun q ↦ φ q * z q) y =
        φ y * Laplacian.laplacian z y +
          z y * Laplacian.laplacian φ y :=
    laplacian_mul_of_isLocalMin_right hφc2 hzc2 hlocal
  have heventual : (fun q ↦ φ q * z q) =ᶠ[𝓝 y] w := by
    filter_upwards [hφc2.continuousAt.eventually_ne hφypos.ne'] with q hq
    dsimp [z]
    field_simp
  have hlapcongr :
      Laplacian.laplacian (fun q ↦ φ q * z q) y =
        Laplacian.laplacian w y :=
    (InnerProductSpace.laplacian_congr_nhds heventual).self_of_nhds
  have hφlap :
      Laplacian.laplacian φ y = -(α ^ 2) * φ y :=
    laplacian_cosineSlabBarrier e α a he y
  have hpdey := hpde y hyS hwyneg
  have hcy := hc y hyS hwyneg
  have hfirst_nonneg :
      0 ≤ φ y * Laplacian.laplacian z y :=
    mul_nonneg hφypos.le hlapz
  have hsecond_pos :
      0 < z y * φ y * (c y - α ^ 2) := by
    have : 0 < z y * (c y - α ^ 2) :=
      mul_pos_of_neg_of_neg hzyneg (sub_neg.mpr hcy)
    nlinarith
  rw [← hlapcongr, hprod, hφlap, hwy_eq] at hpdey
  nlinarith

end Submission.Helpers
