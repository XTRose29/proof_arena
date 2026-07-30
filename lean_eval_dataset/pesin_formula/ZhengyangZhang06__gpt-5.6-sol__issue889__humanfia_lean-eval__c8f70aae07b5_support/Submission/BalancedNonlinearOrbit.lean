import Submission.NonlinearOrbitGrowth
import Submission.GeometricBoundaryScale

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory

lemma eventually_exp_neg_mul_add_lt
    {s delta : ℝ} (hs : 0 < s) (hdelta : 0 < delta) (G : ℝ) :
    ∀ᶠ L : ℕ in atTop, Real.exp (-s * L + G) < delta := by
  have hpow : Tendsto (fun L : ℕ => Real.exp (-s) ^ L)
      atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_nonneg _)
      ((Real.exp_lt_one_iff).2 (by linarith))
  have htend : Tendsto (fun L : ℕ => Real.exp (-s * L + G))
      atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ => Real.exp G) atTop
        (nhds (Real.exp G)) := tendsto_const_nhds
    convert hconst.mul hpow using 1
    · funext L
      rw [Real.exp_add]
      rw [show -s * (L : ℝ) = (L : ℝ) * (-s) by ring_nf,
        Real.exp_nat_mul]
      ring_nf
    · ring_nf
  exact (tendsto_order.1 htend).2 delta hdelta

lemma eventually_exp_neg_mul_add_lt_geometricBoundaryScale
    {s t : ℝ} (hst : t < s) (G : ℝ) :
    let q : NNReal := ⟨Real.exp (-t), Real.exp_nonneg _⟩
    ∀ᶠ L : ℕ in atTop,
      Real.exp (-s * L + G) < geometricBoundaryScale q L := by
  let q : NNReal := ⟨Real.exp (-t), Real.exp_nonneg _⟩
  have hshift : Tendsto (fun L : ℕ => (L + 1 : ℝ)) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hlogdiv : Tendsto
      (fun L : ℕ => Real.log (L + 1 : ℝ) / (L + 1 : ℝ))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, id_eq, Nat.cast_add, Nat.cast_one] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hshift
  have hconstdiv : Tendsto (fun L : ℕ => (G + t) / (L + 1 : ℝ))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat (G + t)).comp
        (tendsto_add_atTop_nat 1)
  have hratio : Tendsto
      (fun L : ℕ => (Real.log (L + 1 : ℝ) + G + t) / (L + 1 : ℝ))
      atTop (nhds 0) := by
    convert hlogdiv.add hconstdiv using 1
    · funext L
      ring_nf
    · ring_nf
  have hgap : 0 < (s - t) / 2 := by linarith
  have hsmall : ∀ᶠ L : ℕ in atTop,
      (Real.log (L + 1 : ℝ) + G + t) / (L + 1 : ℝ) <
        (s - t) / 2 := (tendsto_order.1 hratio).2 _ hgap
  filter_upwards [hsmall, eventually_gt_atTop 0] with L hL hLpos
  have hLone : (1 : ℝ) ≤ L := by exact_mod_cast hLpos
  have hLadd_pos : (0 : ℝ) < L + 1 := by positivity
  have hlogineq : Real.log (L + 1 : ℝ) + G + t < (s - t) * L := by
    have hmul := (div_lt_iff₀ hLadd_pos).mp hL
    have hhalf : (s - t) / 2 * ((L : ℝ) + 1) ≤ (s - t) * L := by
      nlinarith
    exact hmul.trans_le hhalf
  have hexponent : -s * (L : ℝ) + G <
      -t * (L + 1 : ℝ) - Real.log (L + 1 : ℝ) := by
    linarith
  simp only [geometricBoundaryScale, NNReal.coe_div, NNReal.coe_pow]
  change Real.exp (-s * (L : ℝ) + G) <
    Real.exp (-t) ^ (L + 1) / (L + 1 : ℝ)
  rw [← Real.exp_nat_mul]
  rw [show (L + 1 : ℝ) = Real.exp (Real.log (L + 1 : ℝ)) by
    rw [Real.exp_log hLadd_pos]]
  rw [← Real.exp_sub]
  apply Real.exp_lt_exp.mpr
  norm_num [Nat.cast_add, Nat.cast_one] at hexponent ⊢
  nlinarith

lemma forward_budget_le_hyperbolicRate_add
    {lam1 lam2 : ℝ} (hlam1 : 0 < lam1) (hlam2 : lam2 < 0) (L : ℕ) :
    lam1 * balancedForward lam1 lam2 L ≤
      hyperbolicRate lam1 lam2 * L + lam1 := by
  let x : ℝ := lam1 / (lam1 - lam2) * (L : ℝ)
  let m : ℕ := balancedBackward lam1 lam2 L
  have hdenom : 0 < lam1 - lam2 := sub_pos.mpr (hlam2.trans hlam1)
  have hx_lt : x < (m : ℝ) + 1 := Nat.lt_floor_add_one x
  have hmL : m ≤ L := balancedBackward_le hlam1 hlam2 L
  have hidentity :
      hyperbolicRate lam1 lam2 * (L : ℝ) = lam1 * ((L : ℝ) - x) := by
    dsimp [hyperbolicRate, x]
    field_simp [hdenom.ne']
    ring_nf
  rw [balancedForward, Nat.cast_sub hmL]
  dsimp [m] at hx_lt
  rw [hidentity]
  nlinarith

lemma backward_budget_le_hyperbolicRate
    {lam1 lam2 : ℝ} (hlam1 : 0 < lam1) (hlam2 : lam2 < 0) (L : ℕ) :
    (-lam2) * balancedBackward lam1 lam2 L ≤
      hyperbolicRate lam1 lam2 * L := by
  let x : ℝ := lam1 / (lam1 - lam2) * (L : ℝ)
  have hdenom : 0 < lam1 - lam2 := sub_pos.mpr (hlam2.trans hlam1)
  have hx_nonneg : 0 ≤ x :=
    mul_nonneg (div_nonneg hlam1.le hdenom.le) (Nat.cast_nonneg L)
  have hfloor : (balancedBackward lam1 lam2 L : ℝ) ≤ x := by
    exact Nat.floor_le hx_nonneg
  have hstable : 0 ≤ -lam2 := (neg_pos.mpr hlam2).le
  calc
    (-lam2) * balancedBackward lam1 lam2 L ≤ (-lam2) * x :=
      mul_le_mul_of_nonneg_left hfloor hstable
    _ = hyperbolicRate lam1 lam2 * L := by
      dsimp [x, hyperbolicRate]
      field_simp [hdenom.ne']

theorem exists_ae_eventually_balanced_nonlinear_orbit_control
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    {lam1 lam2 epsilon : ℝ}
    (hlam1 : lam1 = ∫ x, lyapunovUpperAt T x ∂mu)
    (hlam2 : lam2 = ∫ x, lyapunovLowerAt T x ∂mu)
    (hlam1_pos : 0 < lam1) (hlam2_neg : lam2 < 0)
    (hepsilon : 0 < epsilon) :
    ∃ q : NNReal, 0 < q ∧ q < 1 ∧
      ∀ᵐ x ∂mu, ∀ᶠ L : ℕ in atTop,
        ∀ y ∈ K,
          dist x y ≤ Real.exp
              (-(hyperbolicRate lam1 lam2 + epsilon) * L) →
            (∀ j : Fin (balancedForward lam1 lam2 L),
              dist (T^[j.val] x) (T^[j.val] y) <
                geometricBoundaryScale q L) ∧
            ∀ k, 0 < k → k ≤ balancedBackward lam1 lam2 L →
              dist (T_inv^[k] x) (T_inv^[k] y) <
                geometricBoundaryScale q L := by
  let rho : ℝ := epsilon / 4
  let s : ℝ := 3 * epsilon / 4
  let t : ℝ := epsilon / 2
  let q : NNReal := ⟨Real.exp (-t), Real.exp_nonneg _⟩
  have hrho : 0 < rho := div_pos hepsilon (by norm_num)
  have hs : 0 < s := by dsimp [s]; linarith
  have hts : t < s := by dsimp [t, s]; linarith
  have hq_pos : 0 < q := by
    change 0 < Real.exp (-t)
    positivity
  have hq_lt : q < 1 := by
    change Real.exp (-t) < 1
    exact (Real.exp_lt_one_iff).2 (by dsimp [t]; linarith)
  have hT_inv := measurePreserving_inverse T T_inv hT_smooth hT_inv_smooth
    hT_left hT_right mu hT
  have hErg_inv := ergodic_inverse T T_inv hT_smooth hT_inv_smooth
    hT_left hT_right mu hErg
  have hK_inv_inv : T_inv '' K = K := inverse_image_eq_of_image_eq hT_left hK_inv
  obtain ⟨deltaF, hdeltaF, hforward⟩ := exists_ae_nonlinear_orbit_growth
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hrho
  have hlam_inv : -lam2 = ∫ x, lyapunovUpperAt T_inv x ∂mu := by
    calc
      -lam2 = -∫ x, lyapunovLowerAt T x ∂mu := congrArg Neg.neg hlam2
      _ = ∫ x, lyapunovUpperAt T_inv x ∂mu :=
        (integral_lyapunovUpperAt_inverse_eq_neg_integral_lyapunovLowerAt
          T T_inv hT_smooth hT_inv_smooth hT_left hT_right K hK_compact
            hK_inv mu hmu_supp hT hErg).symm
  obtain ⟨deltaB, hdeltaB, hbackward⟩ := exists_ae_nonlinear_orbit_growth
    T_inv T hT_inv_smooth hT_smooth hT_right hT_left
      K hK_compact hK_inv_inv mu hmu_supp hT_inv hErg_inv
      hlam_inv hrho
  refine ⟨q, hq_pos, hq_lt, ?_⟩
  filter_upwards [hforward, hbackward] with x hxforward hxbackward
  obtain ⟨GF, hGF, hxforward⟩ := hxforward
  obtain ⟨GB, hGB, hxbackward⟩ := hxbackward
  have hsmallF := eventually_exp_neg_mul_add_lt hs hdeltaF (lam1 + GF)
  have hsmallB := eventually_exp_neg_mul_add_lt hs hdeltaB GB
  have hgeomF :=
    eventually_exp_neg_mul_add_lt_geometricBoundaryScale hts (lam1 + GF)
  have hgeomB := eventually_exp_neg_mul_add_lt_geometricBoundaryScale hts GB
  filter_upwards [hsmallF, hsmallB, hgeomF, hgeomB]
    with L hLFsmall hLBsmall hLFgeom hLBgeom
  intro y hyK hxy
  have hforward_budget :
      lam1 * balancedForward lam1 lam2 L ≤
        hyperbolicRate lam1 lam2 * L + lam1 :=
    forward_budget_le_hyperbolicRate_add hlam1_pos hlam2_neg L
  have hbackward_budget :
      (-lam2) * balancedBackward lam1 lam2 L ≤
        hyperbolicRate lam1 lam2 * L :=
    backward_budget_le_hyperbolicRate hlam1_pos hlam2_neg L
  constructor
  · intro j
    have hjL : j.val ≤ L :=
      (Nat.le_of_lt j.isLt).trans (Nat.sub_le _ _)
    have hjbudget : lam1 * j.val ≤
        hyperbolicRate lam1 lam2 * L + lam1 := by
      have hjcast : (j.val : ℝ) ≤ balancedForward lam1 lam2 L := by
        exact_mod_cast Nat.le_of_lt j.isLt
      exact (mul_le_mul_of_nonneg_left hjcast hlam1_pos.le).trans hforward_budget
    have hjrho : rho * j.val ≤ rho * L := by
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hjL) hrho.le
    have hexponent :
        -(hyperbolicRate lam1 lam2 + epsilon) * L +
            ((lam1 + rho) * j.val + GF) ≤
          -s * L + (lam1 + GF) := by
      dsimp [rho, s]
      nlinarith
    have hinit : dist x y * Real.exp ((lam1 + rho) * j.val + GF) ≤
        deltaF := by
      calc
        dist x y * Real.exp ((lam1 + rho) * j.val + GF) ≤
            Real.exp (-(hyperbolicRate lam1 lam2 + epsilon) * L) *
              Real.exp ((lam1 + rho) * j.val + GF) :=
          mul_le_mul_of_nonneg_right hxy (Real.exp_nonneg _)
        _ = Real.exp (-(hyperbolicRate lam1 lam2 + epsilon) * L +
              ((lam1 + rho) * j.val + GF)) :=
          (Real.exp_add _ _).symm
        _ ≤ Real.exp (-s * L + (lam1 + GF)) :=
          Real.exp_le_exp.mpr hexponent
        _ ≤ deltaF := hLFsmall.le
    have hjgrowth := hxforward j.val y hyK (by
      simpa [max_eq_right (mul_nonneg (add_nonneg hlam1_pos.le hrho.le)
        (Nat.cast_nonneg j.val))] using hinit)
    calc
      dist (T^[j.val] x) (T^[j.val] y) ≤
          Real.exp ((lam1 + rho) * j.val + GF) * dist x y := hjgrowth
      _ ≤ Real.exp ((lam1 + rho) * j.val + GF) *
          Real.exp (-(hyperbolicRate lam1 lam2 + epsilon) * L) :=
        mul_le_mul_of_nonneg_left hxy (Real.exp_nonneg _)
      _ = Real.exp (-(hyperbolicRate lam1 lam2 + epsilon) * L +
            ((lam1 + rho) * j.val + GF)) := by
        calc
          Real.exp ((lam1 + rho) * (j.val : ℝ) + GF) *
              Real.exp (-(hyperbolicRate lam1 lam2 + epsilon) * (L : ℝ)) =
              Real.exp (-(hyperbolicRate lam1 lam2 + epsilon) * (L : ℝ)) *
                Real.exp ((lam1 + rho) * (j.val : ℝ) + GF) := mul_comm _ _
          _ = _ := (Real.exp_add _ _).symm
      _ ≤ Real.exp (-s * L + (lam1 + GF)) :=
        Real.exp_le_exp.mpr hexponent
      _ < geometricBoundaryScale q L := hLFgeom
  · intro k hk_pos hk_le
    have hkL : k ≤ L := hk_le.trans (balancedBackward_le hlam1_pos hlam2_neg L)
    have hkbudget : (-lam2) * k ≤ hyperbolicRate lam1 lam2 * L :=
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hk_le)
        (neg_pos.mpr hlam2_neg).le).trans hbackward_budget
    have hkrho : rho * k ≤ rho * L :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hkL) hrho.le
    have hexponent :
        -(hyperbolicRate lam1 lam2 + epsilon) * L +
            ((-lam2 + rho) * k + GB) ≤ -s * L + GB := by
      dsimp [rho, s]
      nlinarith
    have hinit : dist x y * Real.exp ((-lam2 + rho) * k + GB) ≤
        deltaB := by
      calc
        dist x y * Real.exp ((-lam2 + rho) * k + GB) ≤
            Real.exp (-(hyperbolicRate lam1 lam2 + epsilon) * L) *
              Real.exp ((-lam2 + rho) * k + GB) :=
          mul_le_mul_of_nonneg_right hxy (Real.exp_nonneg _)
        _ = Real.exp (-(hyperbolicRate lam1 lam2 + epsilon) * L +
              ((-lam2 + rho) * k + GB)) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (-s * L + GB) := Real.exp_le_exp.mpr hexponent
        _ ≤ deltaB := hLBsmall.le
    have hkgrowth := hxbackward k y hyK (by
      simpa [max_eq_right (mul_nonneg
        (add_nonneg (neg_pos.mpr hlam2_neg).le hrho.le)
        (Nat.cast_nonneg k))] using hinit)
    calc
      dist (T_inv^[k] x) (T_inv^[k] y) ≤
          Real.exp ((-lam2 + rho) * k + GB) * dist x y := hkgrowth
      _ ≤ Real.exp ((-lam2 + rho) * k + GB) *
          Real.exp (-(hyperbolicRate lam1 lam2 + epsilon) * L) :=
        mul_le_mul_of_nonneg_left hxy (Real.exp_nonneg _)
      _ = Real.exp (-(hyperbolicRate lam1 lam2 + epsilon) * L +
            ((-lam2 + rho) * k + GB)) := by
        calc
          Real.exp ((-lam2 + rho) * (k : ℝ) + GB) *
              Real.exp (-(hyperbolicRate lam1 lam2 + epsilon) * (L : ℝ)) =
              Real.exp (-(hyperbolicRate lam1 lam2 + epsilon) * (L : ℝ)) *
                Real.exp ((-lam2 + rho) * (k : ℝ) + GB) := mul_comm _ _
          _ = _ := (Real.exp_add _ _).symm
      _ ≤ Real.exp (-s * L + GB) := Real.exp_le_exp.mpr hexponent
      _ < geometricBoundaryScale q L := hLBgeom

end Submission.Helpers
