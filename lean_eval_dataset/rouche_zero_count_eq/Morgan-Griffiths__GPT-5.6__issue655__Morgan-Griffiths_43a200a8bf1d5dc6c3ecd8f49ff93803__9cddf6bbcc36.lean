import Mathlib

namespace Submission

open MeromorphicOn
open Filter
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem rouche_zero_count_eq {f g : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R)
    (hf : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖) :
    (∑ᶠ z, ((divisor (f + g) (Metric.closedBall 0 R))⁺) z) =
      (∑ᶠ z, ((divisor f (Metric.closedBall 0 R))⁺) z) :=
/-ResultProofBegin-/
by
  classical
  -- the perturbing entire function is analytic in a neighbourhood
  have hg' : AnalyticOnNhd ℂ g Set.univ :=
    (Complex.analyticOnNhd_univ_iff_differentiable).2
      ((Complex.analyticOn_univ_iff_differentiable).1 hg)
  have hgm : MeromorphicOn g Set.univ := hg'.meromorphicOn
  have hfm : MeromorphicOn f Set.univ := hf.meromorphicOn
  have hhm : MeromorphicOn (f + g) Set.univ := hfm.add hgm
  -- both functions are nonzero on the circle
  have hf_bd : ∀ z ∈ Metric.sphere (0:ℂ) R, f z ≠ 0 := by
    intro z hz hzero
    have hb := hbound z (by simpa [Metric.mem_sphere] using hz)
    simp [hzero] at hb
    exact (not_lt_of_ge (norm_nonneg _)) hb
  have hh_bd : ∀ z ∈ Metric.sphere (0:ℂ) R, (f + g) z ≠ 0 := by
    intro z hz hzero
    have hb := hbound z (by simpa [Metric.mem_sphere] using hz)
    have heq : g z = - f z := by
      have := hzero
      change f z + g z = 0 at this
      exact eq_neg_of_add_eq_zero_right this
    rw [heq, norm_neg] at hb
    exact (lt_irrefl _ hb)
  -- in particular the divisor of f has no term on the boundary
  have df_bd : ∀ z ∈ Metric.sphere (0:ℂ) R,
      MeromorphicOn.divisor f (Metric.closedBall (0:ℂ) R) z = 0 := by
    intro z hz
    have hzc : z ∈ Metric.closedBall (0:ℂ) R := Metric.sphere_subset_closedBall hz
    rw [MeromorphicOn.divisor_apply (fun x hx => hfm x (by simp)) hzc]
    have ho : meromorphicOrderAt f z = (0 : WithTop ℤ) :=
      (hf (by trivial)).meromorphicOrderAt_eq_zero_iff.mpr (hf_bd z hz)
    simp [ho]
  have dh_bd : ∀ z ∈ Metric.sphere (0:ℂ) R,
      MeromorphicOn.divisor (f+g) (Metric.closedBall (0:ℂ) R) z = 0 := by
    intro z hz
    have hzc : z ∈ Metric.closedBall (0:ℂ) R := Metric.sphere_subset_closedBall hz
    rw [MeromorphicOn.divisor_apply (fun x hx => hhm x (by trivial)) hzc]
    have hof : meromorphicOrderAt f z = (0 : WithTop ℤ) :=
      (hf (by trivial)).meromorphicOrderAt_eq_zero_iff.mpr (hf_bd z hz)
    have haf : AnalyticAt ℂ f z :=
      (hf (by trivial)).meromorphicOrderAt_nonneg_iff_analyticAt.mp (by simp [hof])
    have hah : AnalyticAt ℂ (f+g) z := haf.add (hg' z (by trivial))
    rw [hah.meromorphicOrderAt_eq,
      (hah.analyticOrderAt_eq_zero.mpr (hh_bd z hz))]
    simp
  -- the polar divisors are unchanged by the analytic summand
  have hpoles :
      (MeromorphicOn.divisor (f+g) (Metric.closedBall (0:ℂ) R))⁻ =
        (MeromorphicOn.divisor f (Metric.closedBall (0:ℂ) R))⁻ := by
    exact MeromorphicOn.negPart_divisor_add_of_analyticNhdOn_right
      (fun x hx => hfm x (by trivial)) (hg'.mono (by simp))

  -- It remains to compare the total (zeros minus poles) divisors.  Separating
  -- positive and negative parts is a purely finite algebraic step; the point
  -- of recording it here is that no convergence issue about `finsum` is
  -- hidden in this reduction.
  have reduce {U : Set ℂ}
      (d₁ d₂ : Function.locallyFinsuppWithin U ℤ)
      (hd₁ : d₁.support.Finite) (hd₂ : d₂.support.Finite)
      (hneg : d₁⁻ = d₂⁻)
      (ht : (∑ᶠ z, d₁ z) = ∑ᶠ z, d₂ z) :
      (∑ᶠ z, d₁⁺ z) = ∑ᶠ z, d₂⁺ z := by
    have finitePart (d : Function.locallyFinsuppWithin U ℤ)
        (h : d.support.Finite) :
        Function.HasFiniteSupport (fun z : ℂ => d⁺ z) ∧
        Function.HasFiniteSupport (fun z : ℂ => d⁻ z) := by
      constructor
      · exact h.subset (by
          intro z hz hzero
          have h' : d⁺ z = 0 := by simp [hzero]
          exact hz h')
      · exact h.subset (by
          intro z hz hzero
          have h' : d⁻ z = 0 := by simp [hzero]
          exact hz h')
    have esub (d : Function.locallyFinsuppWithin U ℤ) (hd : d.support.Finite) :
        ((∑ᶠ z, d⁺ z) - (∑ᶠ z, d⁻ z)) = ∑ᶠ z, d z := by
      rw [← finsum_sub_distrib (finitePart d hd).1 (finitePart d hd).2]
      exact finsum_congr (fun z => posPart_sub_negPart (d z))
    have hn : (∑ᶠ z, d₁⁻ z) = ∑ᶠ z, d₂⁻ z := by rw [hneg]
    have e1 := esub d₁ hd₁
    have e2 := esub d₂ hd₂
    omega
  apply reduce
    (MeromorphicOn.divisor (f+g) (Metric.closedBall (0:ℂ) R))
    (MeromorphicOn.divisor f (Metric.closedBall (0:ℂ) R))
  · exact (MeromorphicOn.divisor (f+g) (Metric.closedBall (0:ℂ) R)).finiteSupport
      (isCompact_closedBall 0 R)
  · exact (MeromorphicOn.divisor f (Metric.closedBall (0:ℂ) R)).finiteSupport
      (isCompact_closedBall 0 R)
  · exact hpoles
  -- no identically-zero component occurs on the disk: a boundary point
  -- supplies a finite order, and connectedness propagates it.
  have conn : IsConnected (Metric.closedBall (0:ℂ) R) :=
    ⟨Metric.nonempty_closedBall.mpr hR.le, (convex_closedBall (0:ℂ) R).isPreconnected⟩
  let w : ℂ := (R : ℂ)
  have hw : w ∈ Metric.sphere (0:ℂ) R := by
    rw [Metric.mem_sphere]
    simp [w, Complex.norm_real, abs_of_pos hR]
  have hwc : w ∈ Metric.closedBall (0:ℂ) R := Metric.sphere_subset_closedBall hw
  have orderf : ∀ u : (Metric.closedBall (0:ℂ) R),
      meromorphicOrderAt f (u:ℂ) ≠ ⊤ := by
    apply (MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall (U := Metric.closedBall (0:ℂ) R) (fun x hx => hfm x (by trivial)) conn).mp
    refine ⟨⟨w, hwc⟩, ?_⟩
    rw [(hf (by trivial)).meromorphicOrderAt_eq_zero_iff.mpr (hf_bd w hw)]
    simp
  have orderh : ∀ u : (Metric.closedBall (0:ℂ) R),
      meromorphicOrderAt (f+g) (u:ℂ) ≠ ⊤ := by
    apply (MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall (U := Metric.closedBall (0:ℂ) R) (fun x hx => hhm x (by trivial)) conn).mp
    refine ⟨⟨w, hwc⟩, ?_⟩
    have hof : meromorphicOrderAt f w = (0 : WithTop ℤ) :=
      (hf (by trivial)).meromorphicOrderAt_eq_zero_iff.mpr (hf_bd w hw)
    have haf : AnalyticAt ℂ f w :=
      (hf (by trivial)).meromorphicOrderAt_nonneg_iff_analyticAt.mp (by simp [hof])
    have hah : AnalyticAt ℂ (f+g) w := haf.add (hg' w (by trivial))
    rw [hah.meromorphicOrderAt_eq,
      (hah.analyticOrderAt_eq_zero.mpr (hh_bd w hw))]
    simp
  -- Since there is no boundary contribution, total divisors over the
  -- closed and open disks agree.  This is often a useful first reduction in
  -- the argument principle.
  have sumCB_f :
      (∑ᶠ z, MeromorphicOn.divisor f (Metric.closedBall (0:ℂ) R) z) =
        ∑ᶠ z, MeromorphicOn.divisor f (Metric.ball (0:ℂ) R) z := by
    apply finsum_congr
    intro z
    by_cases h : z ∈ Metric.ball (0:ℂ) R
    · rw [MeromorphicOn.divisor_apply (fun x hx => hfm x (by trivial)) h,
          MeromorphicOn.divisor_apply (fun x hx => hfm x (by trivial))
            (Metric.ball_subset_closedBall h)]
    · by_cases hc : z ∈ Metric.closedBall (0:ℂ) R
      · have hs : z ∈ Metric.sphere (0:ℂ) R := by
          rw [Metric.mem_sphere]
          have hle : dist z (0:ℂ) ≤ R := Metric.mem_closedBall.mp hc
          have hnl : ¬ dist z (0:ℂ) < R := by simpa [Metric.mem_ball] using h
          exact le_antisymm hle (le_of_not_gt hnl)
        rw [df_bd z hs]
        simp [h]
      · simp [h, hc]
  have sumCB_h :
      (∑ᶠ z, MeromorphicOn.divisor (f+g) (Metric.closedBall (0:ℂ) R) z) =
        ∑ᶠ z, MeromorphicOn.divisor (f+g) (Metric.ball (0:ℂ) R) z := by
    apply finsum_congr
    intro z
    by_cases h : z ∈ Metric.ball (0:ℂ) R
    · rw [MeromorphicOn.divisor_apply (fun x hx => hhm x (by trivial)) h,
          MeromorphicOn.divisor_apply (fun x hx => hhm x (by trivial))
            (Metric.ball_subset_closedBall h)]
    · by_cases hc : z ∈ Metric.closedBall (0:ℂ) R
      · have hs : z ∈ Metric.sphere (0:ℂ) R := by
          rw [Metric.mem_sphere]
          have hle : dist z (0:ℂ) ≤ R := Metric.mem_closedBall.mp hc
          have hnl : ¬ dist z (0:ℂ) < R := by simpa [Metric.mem_ball] using h
          exact le_antisymm hle (le_of_not_gt hnl)
        rw [dh_bd z hs]
        simp [h]
      · simp [h, hc]
  rw [sumCB_h, sumCB_f]
  -- Both meromorphic functions on the ball therefore have the finite
  -- zero/pole factorisation; these are the data entering the argument
  -- principle on the boundary circle.
  obtain ⟨af, hafA, haf0, hafE⟩ :=
    MeromorphicOn.extract_zeros_poles
      (f := f) (U := Metric.closedBall (0:ℂ) R)
      (fun x hx => hfm x (by trivial)) orderf
      ((MeromorphicOn.divisor f (Metric.closedBall (0:ℂ) R)).finiteSupport
        (isCompact_closedBall 0 R))
  obtain ⟨ah, hahA, hah0, hahE⟩ :=
    MeromorphicOn.extract_zeros_poles
      (f := f+g) (U := Metric.closedBall (0:ℂ) R)
      (fun x hx => hhm x (by trivial)) orderh
      ((MeromorphicOn.divisor (f+g) (Metric.closedBall (0:ℂ) R)).finiteSupport
        (isCompact_closedBall 0 R))
  -- Work in an annulus about the circle.  There, the original function is
  -- holomorphic and the inequality is an open condition.
  let V : Set ℂ := {z | AnalyticAt ℂ f z ∧ ‖g z‖ < ‖f z‖}
  have Vo : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    change AnalyticAt ℂ f z ∧ ‖g z‖ < ‖f z‖ at hz
    have e₁ := hz.1.eventually_analyticAt
    have e₂ : ∀ᶠ y : ℂ in nhds z, ‖g y‖ < ‖f y‖ :=
      ((hg' z (by trivial)).continuousAt.norm.eventually_lt hz.1.continuousAt.norm hz.2)
    exact Filter.inter_mem e₁ e₂
  have sV : Metric.sphere (0:ℂ) R ⊆ V := by
    intro z hz
    change AnalyticAt ℂ f z ∧ ‖g z‖ < ‖f z‖
    have ho : meromorphicOrderAt f z = (0 : WithTop ℤ) :=
      (hf (by trivial)).meromorphicOrderAt_eq_zero_iff.mpr (hf_bd z hz)
    constructor
    · exact (hf (by trivial)).meromorphicOrderAt_nonneg_iff_analyticAt.mp (by simp [ho])
    · exact hbound z (by simpa [Metric.mem_sphere] using hz)
  obtain ⟨δ, δpos, δV⟩ :=
    (isCompact_sphere (0:ℂ) R).exists_thickening_subset_open Vo sV
  let e : ℝ := min (δ/2) (R/2)
  have epos : 0 < e := lt_min (by linarith) (by linarith)
  have elt : e < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith [δpos])
  let r₁ : ℝ := R - e
  let r₂ : ℝ := R + e
  have r₁pos : 0 < r₁ := by dsimp [r₁, e]; have := min_le_right (δ/2) (R/2); linarith
  have r₂pos : 0 < r₂ := by dsimp [r₂]; linarith
  have r₁R : r₁ < R := by dsimp [r₁]; linarith
  have Rr₂ : R < r₂ := by dsimp [r₂]; linarith
  -- any point of this thin closed annulus lies in `V`.
  have band (z : ℂ) (hz₁ : r₁ ≤ ‖z‖) (hz₂ : ‖z‖ ≤ r₂) : z ∈ V := by
    apply δV
    apply Metric.mem_thickening_iff.mpr
    have hn : ‖z‖ ≠ 0 := ne_of_gt (lt_of_lt_of_le r₁pos hz₁)
    let y : ℂ := ( (R / ‖z‖ : ℝ) : ℂ) * z
    refine ⟨y, ?_, ?_⟩
    · rw [Metric.mem_sphere]
      rw [dist_zero_right, norm_mul]
      simp [Complex.norm_real, abs_of_pos hR, abs_of_pos (lt_of_lt_of_le r₁pos hz₁)]
      field_simp
    · rw [dist_eq_norm]
      change ‖z - (( (R / ‖z‖ : ℝ) : ℂ) * z)‖ < δ
      have E : z - (( (R / ‖z‖ : ℝ) : ℂ) * z) =
          (( (1 - R / ‖z‖ : ℝ) : ℂ) * z) := by
        push_cast
        ring
      rw [E, norm_mul, Complex.norm_real]
      change |1 - R / ‖z‖| * ‖z‖ < δ
      have hzn : 0 < ‖z‖ := lt_of_lt_of_le r₁pos hz₁
      have A : ‖z‖ - R ≤ e := by dsimp [r₂] at hz₂; linarith
      have B : -(e:ℝ) ≤ ‖z‖ - R := by dsimp [r₁] at hz₁; linarith
      have C : |1 - R / ‖z‖| * ‖z‖ = |‖z‖ - R| := by
        rw [one_sub_div, abs_div, abs_of_pos hzn]
        field_simp [hn]
        exact hn
      rw [C]
      exact lt_of_le_of_lt (abs_le.mpr ⟨B, A⟩) elt
  -- Clamp the real homotopy parameter. This gives a globally continuous
  -- parameter, which is convenient when taking circle averages.
  let p : ℝ → ℝ := fun t => max 0 (min 1 t)
  have pc : Continuous p := by
    dsimp [p]
    fun_prop
  have pp (t : ℝ) : p t ∈ Set.Icc (0:ℝ) 1 := by
    dsimp [p]
    constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_left _ _)
  have p0 : p 0 = 0 := by simp [p]
  have p1 : p 1 = 1 := by simp [p]
  let F : ℝ → ℂ → ℂ := fun t z => f z + (p t : ℂ) * g z
  have Fm (t : ℝ) : MeromorphicOn (F t) Set.univ := by
    have a : MeromorphicOn (fun z : ℂ => (p t : ℂ) * g z) Set.univ :=
      (analyticOnNhd_const.mul hg').meromorphicOn
    exact hfm.add a
  -- On the annulus all members of the homotopy are nonvanishing holomorphic.
  have Fann (t : ℝ) (z : ℂ) (hz₁ : r₁ ≤ ‖z‖) (hz₂ : ‖z‖ ≤ r₂) :
      AnalyticAt ℂ (F t) z ∧ F t z ≠ 0 := by
    have zv := band z hz₁ hz₂
    change AnalyticAt ℂ f z ∧ ‖g z‖ < ‖f z‖ at zv
    have ag := hg' z (by trivial)
    constructor
    · exact zv.1.add ((analyticAt_const.mul ag))
    · intro hzero
      have heq : f z = -((p t : ℂ) * g z) := by
        have h := hzero
        change f z + (p t : ℂ) * g z = 0 at h
        exact eq_neg_of_add_eq_zero_left h
      have pt := pp t
      have cle : ‖(p t : ℂ)‖ ≤ (1:ℝ) := by
        simpa [Complex.norm_real, abs_of_nonneg pt.1] using pt.2
      have b : ‖(p t : ℂ) * g z‖ ≤ ‖g z‖ := by
        rw [norm_mul]
        nlinarith [norm_nonneg (g z)]
      have bad : ‖g z‖ < ‖(p t : ℂ) * g z‖ := by simpa [heq] using zv.2
      exact (not_lt_of_ge b) bad
  -- Values of the divisor on the two nearby closed balls are exactly its
  -- values on the open R-ball.
  have zero_ann (t : ℝ) (z : ℂ) (hz₁ : r₁ ≤ ‖z‖) (hz₂ : ‖z‖ ≤ r₂) :
      meromorphicOrderAt (F t) z = (0 : WithTop ℤ) := by
    have A := Fann t z hz₁ hz₂
    rw [A.1.meromorphicOrderAt_eq,
      (A.1.analyticOrderAt_eq_zero.mpr A.2)]
    simp
  have dcomp (t : ℝ) (r : ℝ) (hrpos : 0 < r) (hr₁ : r₁ ≤ r) (hr₂ : r ≤ r₂) (z : ℂ) :
      MeromorphicOn.divisor (F t) (Metric.closedBall (0:ℂ) r) z =
        MeromorphicOn.divisor (F t) (Metric.ball (0:ℂ) R) z := by
    have mt := Fm t
    by_cases small : ‖z‖ < r₁
    · have hc : z ∈ Metric.closedBall (0:ℂ) r := by
        simpa [Metric.mem_closedBall] using (le_trans (le_of_lt small) hr₁)
      have hb : z ∈ Metric.ball (0:ℂ) R := by
        have : ‖z‖ < R := lt_trans small r₁R
        simpa [Metric.mem_ball] using this
      rw [MeromorphicOn.divisor_apply (fun x hx => mt x (by trivial)) hc,
        MeromorphicOn.divisor_apply (fun x hx => mt x (by trivial)) hb]
    · have low : r₁ ≤ ‖z‖ := le_of_not_gt small
      by_cases upper : ‖z‖ ≤ r
      · have hc : z ∈ Metric.closedBall (0:ℂ) r := by simpa [Metric.mem_closedBall] using upper
        rw [MeromorphicOn.divisor_apply (fun x hx => mt x (by trivial)) hc,
          zero_ann t z low (le_trans upper hr₂)]
        by_cases hb : ‖z‖ < R
        · have hb' : z ∈ Metric.ball (0:ℂ) R := by simpa [Metric.mem_ball] using hb
          rw [MeromorphicOn.divisor_apply (fun x hx => mt x (by trivial)) hb',
            zero_ann t z low (le_trans (le_of_lt hb) (le_of_lt Rr₂))]
        · have hb' : z ∉ Metric.ball (0:ℂ) R := by simpa [Metric.mem_ball] using hb
          simp [MeromorphicOn.divisor_def, hb']
      · have hc : z ∉ Metric.closedBall (0:ℂ) r := by simpa [Metric.mem_closedBall] using upper
        simp only [MeromorphicOn.divisor_def, hc, and_false, ↓reduceIte]
        by_cases hb : ‖z‖ < R
        · have hb' : z ∈ Metric.ball (0:ℂ) R := by simpa [Metric.mem_ball] using hb
          have mz : meromorphicOrderAt (F t) z = (0 : WithTop ℤ) :=
            zero_ann t z low (le_trans (le_of_lt hb) (le_of_lt Rr₂))
          have mb : MeromorphicOn (F t) (Metric.ball (0:ℂ) R) := fun x hx => mt x (by trivial)
          simp [MeromorphicOn.divisor_def, hb', mb, mz]
        · have hb' : z ∉ Metric.ball (0:ℂ) R := by simpa [Metric.mem_ball] using hb
          simp [MeromorphicOn.divisor_def, hb']
  have continuous_avg (r : ℝ) (hrpos : 0 < r) (hr₁ : r₁ ≤ r) (hr₂ : r ≤ r₂) :
      Continuous (fun t : ℝ =>
        Real.circleAverage (fun z : ℂ => Real.log ‖F t z‖) (0:ℂ) r) := by
    -- write the average as an ordinary parametric integral; the integrand is
    -- continuous since the whole circle lies in the zero-free annulus.
    unfold Real.circleAverage
    apply Continuous.const_smul
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ :=
        MeasureTheory.volume)
        (f := fun t (θ : ℝ) => Real.log ‖F t (circleMap (0:ℂ) r θ)‖) ?_ _ _)
    -- a pointwise proof is a useful way of using that `f` is only known
    -- holomorphic near this annulus (not across its poles).
    rw [continuous_iff_continuousAt]
    intro x
    let z : ℂ := circleMap (0:ℂ) r x.2
    have zn : ‖z‖ = r := by simp [z, abs_of_pos hrpos]
    have az : AnalyticAt ℂ f z := by
      have B := band z (by rw [zn]; exact hr₁) (by rw [zn]; exact hr₂)
      exact B.1
    have cz : ContinuousAt (fun q : ℝ × ℝ => circleMap (0:ℂ) r q.2) x := by
      fun_prop
    have cfz : ContinuousAt (fun q : ℝ × ℝ => f (circleMap (0:ℂ) r q.2)) x := by
      exact az.continuousAt.comp_of_eq cz rfl
    have cgz : ContinuousAt (fun q : ℝ × ℝ => g (circleMap (0:ℂ) r q.2)) x := by
      exact (hg' z (by trivial)).continuousAt.comp_of_eq cz rfl
    have cp' : Continuous (fun q : ℝ × ℝ => (p q.1 : ℂ)) := by
      fun_prop
    have cv : ContinuousAt
        (fun q : ℝ × ℝ => F q.1 (circleMap (0:ℂ) r q.2)) x := by
      change ContinuousAt
        (fun q : ℝ × ℝ => f (circleMap (0:ℂ) r q.2) +
          (p q.1 : ℂ) * g (circleMap (0:ℂ) r q.2)) x
      exact cfz.add (cp'.continuousAt.mul cgz)
    have nz : F x.1 (circleMap (0:ℂ) r x.2) ≠ 0 :=
      (Fann x.1 z (by rw [zn]; exact hr₁) (by rw [zn]; exact hr₂)).2
    exact (cv.norm.log (by simpa using nz))
  have avgformula (t : ℝ) (r : ℝ) (hrpos : 0 < r)
      (hr₁ : r₁ ≤ r) (hr₂ : r ≤ r₂) :
      Real.circleAverage (fun z : ℂ => Real.log ‖F t z‖) (0:ℂ) r =
        (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (F t) (Metric.ball (0:ℂ) R) u : ℤ) : ℝ) *
          Real.log (r * ‖(0:ℂ) - u‖⁻¹)) +
        ((MeromorphicOn.divisor (F t) (Metric.ball (0:ℂ) R) 0 : ℤ) : ℝ) *
          Real.log r + Real.log ‖meromorphicTrailingCoeffAt (F t) 0‖ := by
    have mf : MeromorphicOn (F t) (Metric.closedBall (0:ℂ) |r|) :=
      fun z hz => Fm t z (by trivial)
    have J := MeromorphicOn.circleAverage_log_norm (f := F t)
      (c := (0:ℂ)) (R := r) (ne_of_gt hrpos) mf
    -- The two divisors are literally equal pointwise, not just on their
    -- supports; this keeps all later finite sums elementary.
    rw [abs_of_pos hrpos] at J
    simp_rw [dcomp t r hrpos hr₁ hr₂] at J
    simpa using J
  -- finite support for this common integer divisor, obtained using either
  -- of the compact neighbouring closed balls
  have dfinite (t : ℝ) : Function.HasFiniteSupport
      (fun u : ℂ => MeromorphicOn.divisor (F t) (Metric.ball (0:ℂ) R) u) := by
    have hc := (MeromorphicOn.divisor (F t) (Metric.closedBall (0:ℂ) r₁)).finiteSupport
      (isCompact_closedBall (0:ℂ) r₁)
    have eqfun :
        (fun u : ℂ => MeromorphicOn.divisor (F t) (Metric.closedBall (0:ℂ) r₁) u) =
          (fun u : ℂ => MeromorphicOn.divisor (F t) (Metric.ball (0:ℂ) R) u) := by
      funext z
      exact dcomp t r₁ r₁pos (le_rfl) (le_trans (le_of_lt r₁R) (le_of_lt Rr₂)) z
    rw [← eqfun]
    exact hc
  -- On subtracting the two Jensen formulae the centre term is to be read
  -- separately (`log 0 = 0`); this is the last finite telescoping step of
  -- the argument principle reduction.
  have avgdiff (t : ℝ) :
      Real.circleAverage (fun z : ℂ => Real.log ‖F t z‖) 0 r₂ -
        Real.circleAverage (fun z : ℂ => Real.log ‖F t z‖) 0 r₁ =
       ((∑ᶠ u : ℂ, MeromorphicOn.divisor (F t) (Metric.ball (0:ℂ) R) u : ℤ) : ℝ) *
          (Real.log r₂ - Real.log r₁) := by
    have rr : r₁ < r₂ := lt_trans r₁R Rr₂
    have e2 := avgformula t r₂ r₂pos (le_of_lt rr) (le_rfl)
    have e1 := avgformula t r₁ r₁pos (le_rfl) (le_of_lt rr)
    -- a finite Jensen sum identity (the centre is supplied separately)
    have algebra (d : ℂ → ℤ) (hd : Function.HasFiniteSupport d) :
        ((∑ᶠ u : ℂ, (d u : ℝ) * Real.log (r₂ * ‖(0:ℂ) - u‖⁻¹)) +
              (d 0 : ℝ) * Real.log r₂) -
          ((∑ᶠ u : ℂ, (d u : ℝ) * Real.log (r₁ * ‖(0:ℂ) - u‖⁻¹)) +
              (d 0 : ℝ) * Real.log r₁) =
          ((∑ᶠ u : ℂ, d u : ℤ) : ℝ) * (Real.log r₂ - Real.log r₁) := by
      classical
      -- Adjoin the centre to the finite support, in order to put the two
      -- separately displayed centre terms under the same finite sum.
      let s : Finset ℂ := insert (0:ℂ) hd.toFinset
      have h0 : (0:ℂ) ∈ s := by simp [s]
      have hsupZ : Function.support d ⊆ (s : Set ℂ) := by
        intro u hu
        have hu' : u ∈ hd.toFinset := by simpa using hu
        change u ∈ s
        dsimp [s]
        exact Finset.mem_insert_of_mem hu'
      have hsup (r : ℝ) :
          Function.support
              (fun u : ℂ => (d u : ℝ) * Real.log (r * ‖(0:ℂ) - u‖⁻¹)) ⊆
            (s : Set ℂ) := by
        intro u hu
        have hdu : d u ≠ 0 := by
          intro h
          apply hu
          simp [h]
        have hu' : u ∈ hd.toFinset := by simpa using hdu
        change u ∈ s
        dsimp [s]
        exact Finset.mem_insert_of_mem hu'
      rw [finsum_eq_sum_of_support_subset _ (hsup r₂)]
      rw [finsum_eq_sum_of_support_subset _ (hsup r₁)]
      rw [finsum_eq_sum_of_support_subset _ hsupZ]
      push_cast
      let B : ℝ → ℂ → ℝ :=
        fun r u => if u = 0 then (d 0 : ℝ) * Real.log r else 0
      have sumB (r : ℝ) : (∑ u ∈ s, B r u) = (d 0 : ℝ) * Real.log r := by
        dsimp [B]
        simpa [h0] using
          (Finset.sum_ite_eq' s (0:ℂ)
            (fun _ : ℂ => (d 0 : ℝ) * Real.log r))
      rw [← sumB r₂, ← sumB r₁]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      rw [← Finset.sum_sub_distrib]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u hu
      by_cases zu : u = 0
      · subst u
        simp [B]
        ring
      · have hn : ‖(0:ℂ) - u‖ ≠ 0 := by
          simp [zu]
        have l2 : Real.log (r₂ * ‖(0:ℂ) - u‖⁻¹) =
            Real.log r₂ + Real.log (‖(0:ℂ) - u‖⁻¹) := by
          exact Real.log_mul (ne_of_gt r₂pos) (inv_ne_zero hn)
        have l1 : Real.log (r₁ * ‖(0:ℂ) - u‖⁻¹) =
            Real.log r₁ + Real.log (‖(0:ℂ) - u‖⁻¹) := by
          exact Real.log_mul (ne_of_gt r₁pos) (inv_ne_zero hn)
        dsimp [B]
        rw [if_neg zu, if_neg zu]
        -- keep the log arguments syntactically identical for `Real.log_mul`
        simp only [add_zero]
        rw [l2, l1]
        ring
    rw [e2, e1]
    -- the trailing coefficient term is independent of the radius;
    -- it cancels before applying the elementary finite-sum identity.
    calc
      _ =
          ((∑ᶠ u : ℂ,
              ((MeromorphicOn.divisor (F t) (Metric.ball (0:ℂ) R) u : ℤ) : ℝ) *
                Real.log (r₂ * ‖(0:ℂ) - u‖⁻¹)) +
              ((MeromorphicOn.divisor (F t) (Metric.ball (0:ℂ) R) 0 : ℤ) : ℝ) *
                Real.log r₂) -
            ((∑ᶠ u : ℂ,
              ((MeromorphicOn.divisor (F t) (Metric.ball (0:ℂ) R) u : ℤ) : ℝ) *
                Real.log (r₁ * ‖(0:ℂ) - u‖⁻¹)) +
              ((MeromorphicOn.divisor (F t) (Metric.ball (0:ℂ) R) 0 : ℤ) : ℝ) *
                Real.log r₁) := by ring
      _ =
          ((∑ᶠ u : ℂ, MeromorphicOn.divisor (F t)
              (Metric.ball (0:ℂ) R) u : ℤ) : ℝ) *
            (Real.log r₂ - Real.log r₁) := by
          exact algebra
            (fun u : ℂ => MeromorphicOn.divisor (F t)
              (Metric.ball (0:ℂ) R) u) (dfinite t)

  -- the difference of the two circle means is continuous in the homotopy
  -- parameter.  Dividing by the (positive) logarithmic width of the
  -- annulus, it takes values in the integers, and hence is constant.
  have rr : r₁ < r₂ := lt_trans r₁R Rr₂
  let L : ℝ := Real.log r₂ - Real.log r₁
  have Lpos : 0 < L := by
    dsimp [L]
    have hl : Real.log r₁ < Real.log r₂ := Real.log_lt_log r₁pos rr
    linarith
  have Lne : L ≠ 0 := ne_of_gt Lpos
  let D : ℝ → ℤ :=
    fun t => ∑ᶠ u : ℂ, MeromorphicOn.divisor (F t) (Metric.ball (0:ℂ) R) u
  let Q : ℝ → ℝ :=
    fun t =>
      (Real.circleAverage (fun z : ℂ => Real.log ‖F t z‖) 0 r₂ -
        Real.circleAverage (fun z : ℂ => Real.log ‖F t z‖) 0 r₁) / L
  have c2 : Continuous (fun t : ℝ =>
      Real.circleAverage (fun z : ℂ => Real.log ‖F t z‖) (0:ℂ) r₂) :=
    continuous_avg r₂ r₂pos (le_of_lt rr) (le_rfl)
  have c1 : Continuous (fun t : ℝ =>
      Real.circleAverage (fun z : ℂ => Real.log ‖F t z‖) (0:ℂ) r₁) :=
    continuous_avg r₁ r₁pos (le_rfl) (le_of_lt rr)
  have cQ : Continuous Q := by
    dsimp [Q]
    exact (c2.sub c1).div_const L
  have qeq (t : ℝ) : Q t = (D t : ℝ) := by
    dsimp [Q, D]
    rw [avgdiff t]
    -- cancellation is legitimate since the annular width is non-zero
    change
      ((( (∑ᶠ u : ℂ, MeromorphicOn.divisor (F t)
          (Metric.ball (0:ℂ) R) u : ℤ) : ℝ) * L) / L) = _
    exact mul_div_cancel_right₀ _ Lne
  have disc : IsDiscrete (Set.range (fun n : ℤ => (n : ℝ))) := by
    have hd : IsDiscrete
        ( (AddSubgroup.zmultiples (1:ℝ) : AddSubgroup ℝ) : Set ℝ) := by
      rw [SetLike.isDiscrete_iff_discreteTopology]
      infer_instance
    have es : Set.range (fun n : ℤ => (n : ℝ)) =
        ( (AddSubgroup.zmultiples (1:ℝ) : AddSubgroup ℝ) : Set ℝ) := by
      ext x
      rw [← Int.range_castAddHom]
      rfl
    rw [es]
    exact hd
  have qmaps : Set.MapsTo Q (Set.univ : Set ℝ)
      (Set.range (fun n : ℤ => (n : ℝ))) := by
    intro x hx
    refine ⟨D x, ?_⟩
    exact (qeq x).symm
  have qconst (x y : ℝ) : Q x = Q y := by
    exact (isPreconnected_univ.constant_of_mapsTo disc cQ.continuousOn qmaps
      (by trivial) (by trivial))
  have dc : D (1:ℝ) = D (0:ℝ) := by
    apply (Int.cast_injective : Function.Injective (fun n : ℤ => (n : ℝ)))
    calc
      (D (1:ℝ) : ℝ) = Q 1 := (qeq 1).symm
      _ = Q 0 := qconst 1 0
      _ = (D (0:ℝ) : ℝ) := qeq 0
  have Fzero : F 0 = f := by
    funext z
    dsimp [F]
    rw [p0]
    simp
  have Fone : F 1 = f + g := by
    funext z
    dsimp [F]
    rw [p1]
    simp
  -- specialize the constant integer count at the ends of the homotopy
  simpa [D, Fzero, Fone] using dc
/-ResultProofEnd-/
/-ResultEnd-/

end Submission
