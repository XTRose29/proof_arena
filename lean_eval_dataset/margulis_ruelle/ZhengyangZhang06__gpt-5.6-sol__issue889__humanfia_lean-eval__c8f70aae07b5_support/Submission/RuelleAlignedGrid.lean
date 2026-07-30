import Submission.RuelleExpansion
import Submission.RuelleIterateEntropy

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory

noncomputable def rationalCutThreshold (k : ℕ) : ℚ :=
  (Encodable.decode (α := ℚ) (Nat.unpair k).2).getD 0

noncomputable def rationalPrefixDenominator (N : ℕ) : ℕ :=
  ∏ k : Set.Iic N, (rationalCutThreshold k.1).den

lemma rationalPrefixDenominator_pos (N : ℕ) :
    0 < rationalPrefixDenominator N := by
  rw [rationalPrefixDenominator]
  exact Finset.prod_pos fun k _hk => (rationalCutThreshold k.1).den_pos

lemma rationalCutThreshold_den_dvd_prefixDenominator
    {k N : ℕ} (hk : k ≤ N) :
    (rationalCutThreshold k).den ∣ rationalPrefixDenominator N := by
  let j : Set.Iic N := ⟨k, hk⟩
  change (rationalCutThreshold j.1).den ∣
    ∏ t : Set.Iic N, (rationalCutThreshold t.1).den
  rw [Fintype.prod_eq_mul_prod_compl j]
  exact dvd_mul_right _ _

lemma exists_aligned_rational_mesh
    (N : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    ∃ r : ℝ, 0 < r ∧ r < rho ∧
      ∀ k, k ≤ N → ∃ z : ℤ,
        (rationalCutThreshold k : ℝ) = r * z := by
  let D := rationalPrefixDenominator N
  have hD : 0 < D := rationalPrefixDenominator_pos N
  have hDrho : 0 < (D : ℝ) * rho := mul_pos (by exact_mod_cast hD) hrho
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hDrho
  let M := m + 1
  let r : ℝ := 1 / ((D * M : ℕ) : ℝ)
  have hM : 0 < M := by simp [M]
  have hDM : 0 < D * M := Nat.mul_pos hD hM
  have hD_real_ne : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hM_real_ne : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hMbound : 1 / (M : ℝ) < (D : ℝ) * rho := by
    simpa only [M, Nat.cast_add, Nat.cast_one] using hm
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hrlt : r < rho := by
    calc
      r = (1 / (M : ℝ)) / (D : ℝ) := by
        dsimp [r]
        push_cast
        field_simp [hD_real_ne, hM_real_ne]
      _ < ((D : ℝ) * rho) / (D : ℝ) :=
        div_lt_div_of_pos_right hMbound (by exact_mod_cast hD)
      _ = rho := by field_simp [hD_real_ne]
  refine ⟨r, hr, hrlt, ?_⟩
  intro k hk
  let q := rationalCutThreshold k
  have hdvd : q.den ∣ D :=
    rationalCutThreshold_den_dvd_prefixDenominator hk
  obtain ⟨a, ha⟩ := hdvd
  have ha_pos : 0 < a := by
    apply pos_of_mul_pos_right (a := q.den)
    · rw [← ha]
      exact hD
    · exact Nat.zero_le _
  let z : ℤ := q.num * (a * M : ℕ)
  refine ⟨z, ?_⟩
  rw [Rat.cast_def]
  dsimp [r, z]
  rw [ha]
  push_cast
  field_simp [q.den_nz, show (a : ℝ) ≠ 0 by exact_mod_cast ha_pos.ne',
    hM_real_ne]
  ring

lemma coordinate_lt_gridBoundary_iff
    {r : ℝ} (hr : 0 < r) {a b : ℝ}
    (hfloor : ⌊a / r⌋ = ⌊b / r⌋)
    (z : ℤ) :
    a < r * z ↔ b < r * z := by
  have halow : ((⌊a / r⌋ : ℤ) : ℝ) ≤ a / r := Int.floor_le _
  have hahigh : a / r < ((⌊a / r⌋ : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have hblow : ((⌊b / r⌋ : ℤ) : ℝ) ≤ b / r := Int.floor_le _
  have hbhigh : b / r < ((⌊b / r⌋ : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  constructor
  · intro ha
    have haz : a / r < (z : ℝ) := by
      apply (div_lt_iff₀ hr).2
      simpa [mul_comm] using ha
    have hpz : ⌊a / r⌋ < z := by
      exact_mod_cast (halow.trans_lt haz)
    have hpone : ⌊b / r⌋ + 1 ≤ z := by
      rw [← hfloor]
      omega
    have hbz : b / r < (z : ℝ) := by
      exact hbhigh.trans_le (by exact_mod_cast hpone)
    simpa [mul_comm] using (div_lt_iff₀ hr).1 hbz
  · intro hb
    have hbz : b / r < (z : ℝ) := by
      apply (div_lt_iff₀ hr).2
      simpa [mul_comm] using hb
    have hpz : ⌊b / r⌋ < z := by
      exact_mod_cast (hblow.trans_lt hbz)
    have hpone : ⌊a / r⌋ + 1 ≤ z := by
      rw [hfloor]
      omega
    have haz : a / r < (z : ℝ) := by
      exact hahigh.trans_le (by exact_mod_cast hpone)
    simpa [mul_comm] using (div_lt_iff₀ hr).1 haz

lemma coordinate_lt_aligned_cut_iff
    {r q : ℝ} (hr : 0 < r) {x y : EucPlane}
    (hgrid : squareGridIndex r x = squareGridIndex r y)
    (i : Fin 2) {z : ℤ} (hq : q = r * z) :
    x.ofLp i < q ↔ y.ofLp i < q := by
  rw [hq]
  fin_cases i
  · exact coordinate_lt_gridBoundary_iff hr
      (congrArg Prod.fst hgrid) z
  · exact coordinate_lt_gridBoundary_iff hr
      (congrArg Prod.snd hgrid) z

lemma rationalCutBit_eq_of_aligned_grid
    {r : ℝ} (hr : 0 < r) {N : ℕ}
    (halign : ∀ k, k ≤ N → ∃ z : ℤ,
      (rationalCutThreshold k : ℝ) = r * z)
    {x y : EucPlane}
    (hgrid : squareGridIndex r x = squareGridIndex r y)
    {k : ℕ} (hk : k ≤ N) :
    rationalCutBit k x = rationalCutBit k y := by
  obtain ⟨z, hz⟩ := halign k hk
  let i : Fin 2 :=
    ⟨(Nat.unpair k).1 % 2, Nat.mod_lt _ (by omega)⟩
  have hcut :
      x.ofLp i < (rationalCutThreshold k : ℝ) ↔
        y.ofLp i < (rationalCutThreshold k : ℝ) :=
    coordinate_lt_aligned_cut_iff hr hgrid i hz
  change
    {u : EucPlane | u.ofLp i < (rationalCutThreshold k : ℝ)}.indicator
        (fun _ => true) x =
      {u : EucPlane | u.ofLp i < (rationalCutThreshold k : ℝ)}.indicator
        (fun _ => true) y
  by_cases hx : x.ofLp i < (rationalCutThreshold k : ℝ)
  · have hy := hcut.mp hx
    rw [Set.indicator_of_mem
        (s := {u : EucPlane | u.ofLp i < (rationalCutThreshold k : ℝ)})
        hx (fun _ => true),
      Set.indicator_of_mem
        (s := {u : EucPlane | u.ofLp i < (rationalCutThreshold k : ℝ)})
        hy (fun _ => true)]
  · have hy : ¬y.ofLp i < (rationalCutThreshold k : ℝ) :=
      fun h => hx (hcut.mpr h)
    rw [Set.indicator_of_notMem
        (s := {u : EucPlane | u.ofLp i < (rationalCutThreshold k : ℝ)})
        hx (fun _ => true),
      Set.indicator_of_notMem
        (s := {u : EucPlane | u.ofLp i < (rationalCutThreshold k : ℝ)})
        hy (fun _ => true)]

lemma spatialPrefixObservation_eq_of_aligned_grid
    {r : ℝ} (hr : 0 < r) (N : ℕ)
    (halign : ∀ k, k ≤ N → ∃ z : ℤ,
      (rationalCutThreshold k : ℝ) = r * z)
    {x y : EucPlane}
    (hgrid : squareGridIndex r x = squareGridIndex r y) :
    spatialPrefixObservation rationalCutBit N x =
      spatialPrefixObservation rationalCutBit N y := by
  funext k
  exact rationalCutBit_eq_of_aligned_grid hr halign hgrid
    k.2

lemma exists_squareGridBox_of_compact
    {K : Set EucPlane} (hK_compact : IsCompact K)
    {r : ℝ} (hr : 0 < r) :
    ∃ box : Finset (ℤ × ℤ),
      ∀ x ∈ K, squareGridIndex r x ∈ box := by
  obtain ⟨R, hKR⟩ :=
    hK_compact.isBounded.subset_closedBall (0 : EucPlane)
  let L : ℤ := ⌈R / r⌉ + 1
  let box : Finset (ℤ × ℤ) :=
    (Finset.Icc (-L) L).product (Finset.Icc (-L) L)
  refine ⟨box, ?_⟩
  intro x hxK
  have hxnorm : ‖x‖ ≤ R := by
    have hxball := Metric.mem_closedBall.mp (hKR hxK)
    simpa [dist_eq_norm] using hxball
  have hcoord (i : Fin 2) : |x.ofLp i| ≤ R := by
    calc
      |x.ofLp i| = ‖x.ofLp i‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖x‖ := PiLp.norm_apply_le x i
      _ ≤ R := hxnorm
  have hindex (i : Fin 2) :
      -L ≤ ⌊x.ofLp i / r⌋ ∧ ⌊x.ofLp i / r⌋ ≤ L := by
    let a := x.ofLp i / r
    let Q := R / r
    let p : ℤ := ⌊a⌋
    have hR : 0 ≤ R := (norm_nonneg x).trans hxnorm
    have hxi_lower : -R ≤ x.ofLp i := (abs_le.mp (hcoord i)).1
    have hxi_upper : x.ofLp i ≤ R := (abs_le.mp (hcoord i)).2
    have ha_lower : -Q ≤ a := by
      dsimp [a, Q]
      simpa only [neg_div] using
        (div_le_div_iff_of_pos_right hr).2 hxi_lower
    have ha_upper : a ≤ Q := by
      dsimp [a, Q]
      exact (div_le_div_iff_of_pos_right hr).2 hxi_upper
    have hp_lower : -⌈Q⌉ ≤ p := by
      simpa only [Int.floor_neg, p] using Int.floor_mono ha_lower
    have hp_upper : p ≤ ⌈Q⌉ := by
      have hfloor :=
        (Int.floor_mono ha_upper).trans (Int.floor_le_ceil Q)
      simpa only [p] using hfloor
    change -(⌈Q⌉ + 1) ≤ p ∧ p ≤ ⌈Q⌉ + 1
    constructor
    · omega
    · omega
  dsimp only [box]
  rw [Finset.product_eq_sprod, Finset.mem_product]
  constructor
  · rw [Finset.mem_Icc]
    exact hindex 0
  · rw [Finset.mem_Icc]
    exact hindex 1

lemma entropyW_fiberPartition_le_of_ae_determined
    {M I J : Type*} [MeasurableSpace M]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [Inhabited I]
    [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T T_inv : M → M)
    (hT_right : Function.RightInverse T_inv T)
    (hT : MeasurePreserving T mu mu)
    (X : M → I) (hX : Measurable X)
    (Z : M → J) (hZ : Measurable Z)
    (good : Set M) (hfull : mu goodᶜ = 0)
    (hforward : ∀ x ∈ good, T x ∈ good)
    (hdet : ∀ x ∈ good, ∀ y ∈ good, Z x = Z y → X x = X y) :
    entropyW mu T (fiberPartition X) ≤
      entropyW mu T (fiberPartition Z) := by
  let PX := fiberPartition X
  let PZ := fiberPartition Z
  have hPX : IsMeasurablePartition mu PX :=
    isMeasurablePartition_fiberPartition mu X hX
  have hPZ : IsMeasurablePartition mu PZ :=
    isMeasurablePartition_fiberPartition mu Z hZ
  have hiterate (x : M) (hx : x ∈ good) (k : ℕ) :
      T^[k] x ∈ good := by
    induction k with
    | zero => exact hx
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact hforward _ ih
  have hblock (n : ℕ) :
      observationEntropy mu (observationBlock T X n) ≤
        observationEntropy mu (observationBlock T Z n) := by
    apply observationEntropy_le_of_ae_determined
      mu (observationBlock T X n) (observationBlock T Z n)
        (measurable_observationBlock T hT.measurable Z hZ n)
        good hfull
    intro x hx y hy hxy
    funext k
    exact hdet _ (hiterate x hx k.val) _ (hiterate y hy k.val)
      (congrFun hxy k)
  have hrate (n : ℕ) :
      partitionEntropy mu (iteratedJoin T PX n) / n ≤
        partitionEntropy mu (iteratedJoin T PZ n) / n := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    rw [← observationEntropy_observationBlock_fiberPartition,
      ← observationEntropy_observationBlock_fiberPartition]
    exact hblock n
  have hXlimit :=
    tendsto_partitionEntropy_iteratedJoin_div_entropyW
      mu T T_inv hT_right hT PX hPX
  have hZlimit :=
    tendsto_partitionEntropy_iteratedJoin_div_entropyW
      mu T T_inv hT_right hT PZ hPZ
  apply le_of_not_gt
  intro hgt
  let midpoint :=
    (entropyW mu T PX + entropyW mu T PZ) / 2
  have hZmid : entropyW mu T PZ < midpoint := by
    dsimp [midpoint]
    linarith
  have hmidX : midpoint < entropyW mu T PX := by
    dsimp [midpoint]
    linarith
  have hXevent : ∀ᶠ n : ℕ in atTop,
      midpoint < partitionEntropy mu (iteratedJoin T PX n) / n :=
    (tendsto_order.1 hXlimit).1 midpoint hmidX
  have hZevent : ∀ᶠ n : ℕ in atTop,
      partitionEntropy mu (iteratedJoin T PZ n) / n < midpoint :=
    (tendsto_order.1 hZlimit).2 midpoint hZmid
  obtain ⟨n, hXn, hZn⟩ := (hXevent.and hZevent).exists
  exact (not_lt_of_ge (hrate n)) (hZn.trans hXn)

lemma entropyW_rationalPrefix_le_expansion_add
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (S S_inv : EucPlane → EucPlane)
    (hS_smooth : ContDiff ℝ 2 S)
    (hS_inv_smooth : ContDiff ℝ 2 S_inv)
    (hS_left : Function.LeftInverse S_inv S)
    (hS_right : Function.RightInverse S_inv S)
    (K : Set EucPlane) (hK_compact : IsCompact K)
    (hSK : S '' K = K)
    (hmuK : mu Kᶜ = 0)
    (hS : MeasurePreserving S mu mu)
    (N : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    entropyW mu S
        (fiberPartition
          (spatialPrefixObservation rationalCutBit N)) ≤
      Real.log 3969 +
        (∫ x, derivativeExpansion S S_inv x ∂mu) + epsilon := by
  let F := derivativeExpansion S S_inv
  have hFcont : Continuous F :=
    continuous_derivativeExpansion S S_inv hS_smooth hS_inv_smooth
      hS_left hS_right
  have hFuc : UniformContinuousOn F K :=
    hK_compact.uniformContinuousOn_of_continuous hFcont.continuousOn
  obtain ⟨delta, hdelta, hFdelta⟩ :=
    (Metric.uniformContinuousOn_iff.mp hFuc) epsilon hepsilon
  obtain ⟨R, hKR⟩ :=
    hK_compact.isBounded.subset_closedBall (0 : EucPlane)
  let C := Metric.closedBall (0 : EucPlane) R
  have hCcompact : IsCompact C := isCompact_closedBall _ _
  have hCconvex : Convex ℝ C := convex_closedBall _ _
  obtain ⟨B, hBone, hB⟩ :=
    exists_fderiv_lipschitz_constant_on_compact_convex
      S hS_smooth hCcompact hCconvex
  let rho := min (delta / 2) (1 / (4 * B))
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hBone
  have hrho : 0 < rho := by
    dsimp [rho]
    positivity
  obtain ⟨r, hr, hrho_lt, halign⟩ :=
    exists_aligned_rational_mesh N hrho
  obtain ⟨box, hKbox⟩ := exists_squareGridBox_of_compact hK_compact hr
  have hrdelta : 2 * r < delta := by
    have hrhalf : r < delta / 2 :=
      hrho_lt.trans_le (min_le_left _ _)
    linarith
  have hrB : 4 * B * r ≤ 1 := by
    have hrinv : r < 1 / (4 * B) :=
      hrho_lt.trans_le (min_le_right _ _)
    have h4B : 0 < 4 * B := by positivity
    calc
      4 * B * r ≤ 4 * B * (1 / (4 * B)) :=
        (mul_lt_mul_of_pos_left hrinv h4B).le
      _ = 1 := by field_simp [hBpos.ne']
  let Y := spatialPrefixObservation rationalCutBit N
  let Z := squareGridObservation r box
  have hY : Measurable Y :=
    measurable_spatialPrefixObservation
      rationalCutBit measurable_rationalCutBit N
  have hZ : Measurable Z := measurable_squareGridObservation r box
  have hZdet : ∀ x ∈ K, ∀ y ∈ K, Z x = Z y → Y x = Y y := by
    intro x hx y hy hxy
    let qx : ↥box := ⟨squareGridIndex r x, hKbox x hx⟩
    have hxsome : Z x = some qx :=
      (squareGridObservation_eq_some_iff r box x qx).2 rfl
    have hysome : Z y = some qx := hxy.symm.trans hxsome
    have hgrid : squareGridIndex r x = squareGridIndex r y := by
      exact (squareGridObservation_eq_some_iff r box y qx).1 hysome |>.symm
    exact spatialPrefixObservation_eq_of_aligned_grid
      hr N halign hgrid
  have hprefixGrid :
      entropyW mu S (fiberPartition Y) ≤
        entropyW mu S (fiberPartition Z) := by
    apply entropyW_fiberPartition_le_of_ae_determined
      mu S S_inv hS_right hS Y hY Z hZ K hmuK
    · intro x hx
      rw [← hSK]
      exact ⟨x, hx, rfl⟩
    · exact hZdet
  have hgridConditional :
      entropyW mu S (fiberPartition Z) ≤
        conditionalObservationEntropy mu (fun x => Z (S x)) Z :=
    entropyW_fiberPartition_le_one_step_conditional
      mu S S_inv hS_right hS Z hZ
  have hosc : ∀ x ∈ K, ∀ z ∈ K, Z x = Z z →
      F x ≤ F z + epsilon := by
    intro x hx z hz hxz
    let qx : ↥box := ⟨squareGridIndex r x, hKbox x hx⟩
    have hxsome : Z x = some qx :=
      (squareGridObservation_eq_some_iff r box x qx).2 rfl
    have hzsome : Z z = some qx := hxz.symm.trans hxsome
    have hgrid : squareGridIndex r x = squareGridIndex r z := by
      exact (squareGridObservation_eq_some_iff r box z qx).1 hzsome |>.symm
    have hdistxz : dist x z < delta := by
      rw [dist_eq_norm]
      exact (norm_sub_lt_two_mul_of_squareGridIndex_eq hr hgrid).trans hrdelta
    have hFdist := hFdelta x hx z hz hdistxz
    rw [Real.dist_eq] at hFdist
    simpa only [add_comm] using
      (sub_lt_iff_lt_add.mp
        ((le_abs_self (F x - F z)).trans_lt hFdist)).le
  have hconditional :=
    conditionalObservationEntropy_squareGrid_le_integral_expansion
      mu S S_inv hS_smooth hS_inv_smooth hS_left hS_right
        K hK_compact hmuK hSK C hCconvex hKR (zero_le_one.trans hBone) hB
        hr hrB box hKbox hosc
  calc
    entropyW mu S
        (fiberPartition
          (spatialPrefixObservation rationalCutBit N)) =
        entropyW mu S (fiberPartition Y) := rfl
    _ ≤ entropyW mu S (fiberPartition Z) := hprefixGrid
    _ ≤ conditionalObservationEntropy mu (fun x => Z (S x)) Z :=
      hgridConditional
    _ ≤ Real.log 3969 +
        (∫ x, derivativeExpansion S S_inv x ∂mu) + epsilon := hconditional

lemma entropyW_rationalPrefix_le_expansion
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (S S_inv : EucPlane → EucPlane)
    (hS_smooth : ContDiff ℝ 2 S)
    (hS_inv_smooth : ContDiff ℝ 2 S_inv)
    (hS_left : Function.LeftInverse S_inv S)
    (hS_right : Function.RightInverse S_inv S)
    (K : Set EucPlane) (hK_compact : IsCompact K)
    (hSK : S '' K = K)
    (hmuK : mu Kᶜ = 0)
    (hS : MeasurePreserving S mu mu)
    (N : ℕ) :
    entropyW mu S
        (fiberPartition
          (spatialPrefixObservation rationalCutBit N)) ≤
      Real.log 3969 +
        ∫ x, derivativeExpansion S S_inv x ∂mu := by
  apply le_of_not_gt
  intro hgt
  let epsilon :=
    (entropyW mu S
      (fiberPartition (spatialPrefixObservation rationalCutBit N)) -
        (Real.log 3969 +
          ∫ x, derivativeExpansion S S_inv x ∂mu)) / 2
  have hepsilon : 0 < epsilon := div_pos (sub_pos.mpr hgt) (by norm_num)
  have hbound := entropyW_rationalPrefix_le_expansion_add
    mu S S_inv hS_smooth hS_inv_smooth hS_left hS_right
      K hK_compact hSK hmuK hS N hepsilon
  dsimp [epsilon] at hbound
  linarith

lemma kolmogorovSinaiEntropy_le_finiteDerivativeExpansion
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane)
    (hK_compact : IsCompact K)
    (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hmu_pres : MeasurePreserving T mu mu)
    {n : ℕ} (hn : 0 < n) :
    kolmogorovSinaiEntropy mu T ≤
      (Real.log 3969 +
        ∫ x, derivativeExpansion (T^[n]) (T_inv^[n]) x ∂mu) / n := by
  let S := T^[n]
  let S_inv := T_inv^[n]
  have hS_smooth : ContDiff ℝ 2 S := contDiff_iterate T hT_smooth n
  have hS_inv_smooth : ContDiff ℝ 2 S_inv :=
    contDiff_iterate T_inv hT_inv_smooth n
  have hS_left : Function.LeftInverse S_inv S := hT_left.iterate n
  have hS_right : Function.RightInverse S_inv S := hT_right.iterate n
  have hSK : S '' K = K := image_iterate_eq_of_image_eq T hK_inv n
  have hS : MeasurePreserving S mu mu := hmu_pres.iterate n
  let U := Real.log 3969 +
    ∫ x, derivativeExpansion S S_inv x ∂mu
  have hupperS : ∀ N,
      entropyW mu S
        (fiberPartition
          (spatialPrefixObservation rationalCutBit N)) ≤ U := by
    intro N
    exact entropyW_rationalPrefix_le_expansion
      mu S S_inv hS_smooth hS_inv_smooth hS_left hS_right
        K hK_compact hSK hmu_supp hS N
  have hemb : MeasurableEmbedding
      (fun x : K => fun k => rationalCutBit k x.1) := by
    exact measurableEmbedding_rationalCutCode.comp
      (MeasurableEmbedding.subtype_coe hK_compact.measurableSet)
  have hupperT : ∀ N,
      entropyW mu T
        (fiberPartition
          (spatialPrefixObservation rationalCutBit N)) ≤ U / n := by
    intro N
    let Y := spatialPrefixObservation rationalCutBit N
    let Q := fiberPartition (observationBlock T Y n)
    have hY : Measurable Y :=
      measurable_spatialPrefixObservation
        rationalCutBit measurable_rationalCutBit N
    have hblock : Measurable (observationBlock T Y n) :=
      measurable_observationBlock T hmu_pres.measurable Y hY n
    have hQ : IsMeasurablePartition mu Q :=
      isMeasurablePartition_fiberPartition mu _ hblock
    have hQbound : entropyW mu S Q ≤ U :=
      entropyW_le_of_uniform_spatial_prefix_bound
        mu S S_inv hS_right hS rationalCutBit measurable_rationalCutBit
          hmu_supp hemb hupperS Q hQ
    have hscale :=
      entropyW_iterate_fiberPartition_observationBlock
        mu T T_inv hT_right hmu_pres Y hY hn
    change entropyW mu T (fiberPartition Y) ≤ U / n
    apply (le_div_iff₀' (by exact_mod_cast hn : (0 : ℝ) < n)).2
    rw [← hscale]
    exact hQbound
  have hKS :=
    kolmogorovSinaiEntropy_le_of_uniform_spatial_prefix_bound
      mu T T_inv hT_right hmu_pres rationalCutBit
        measurable_rationalCutBit hmu_supp hemb hupperT
  simpa [S, S_inv, U] using hKS

end Submission.Helpers
