import Submission.KnotFamilyStability

open LeanEval.Geometry.FaryMilnorProblem
open Set
open Filter
open scoped Real
open scoped Topology
open scoped RealInnerProductSpace
open WithLp

namespace Submission.Helpers

noncomputable def concatLeftParameter (n : ℕ) (s : ℝ) : ℝ :=
  1 - (1 - s) ^ n

noncomputable def concatRightParameter (n : ℕ) (s : ℝ) : ℝ :=
  s ^ n

theorem concatLeftParameter_mem_Icc (n : ℕ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    concatLeftParameter n s ∈ Icc (0 : ℝ) 1 := by
  have hbase : 0 ≤ 1 - s := sub_nonneg.mpr hs.2
  have hbase1 : 1 - s ≤ 1 := by linarith [hs.1]
  have hpow0 : 0 ≤ (1 - s) ^ n := pow_nonneg hbase n
  have hpow1 : (1 - s) ^ n ≤ 1 := by
    simpa using pow_le_pow_left₀ hbase hbase1 n
  exact ⟨by simp [concatLeftParameter]; linarith,
    by simp [concatLeftParameter]; linarith⟩

theorem concatRightParameter_mem_Icc (n : ℕ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    concatRightParameter n s ∈ Icc (0 : ℝ) 1 := by
  exact ⟨pow_nonneg hs.1 n, by
    simpa [concatRightParameter] using pow_le_pow_left₀ hs.1 hs.2 n⟩

theorem contDiff_concatLeftParameter (n : ℕ) :
    ContDiff ℝ ⊤ (concatLeftParameter n) := by
  unfold concatLeftParameter
  fun_prop

theorem contDiff_concatRightParameter (n : ℕ) :
    ContDiff ℝ ⊤ (concatRightParameter n) := by
  unfold concatRightParameter
  fun_prop

noncomputable def analyticConcat (A B : ℝ → ℝ → Space) (n : ℕ)
    (t s : ℝ) : Space :=
  (1 - s) • A t (concatLeftParameter n s) +
    s • B t (concatRightParameter n s)

theorem contDiff_analyticConcat {A B : ℝ → ℝ → Space}
    (hA : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => A p.1 p.2))
    (hB : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => B p.1 p.2)) (n : ℕ) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ => analyticConcat A B n p.1 p.2) := by
  have ha : ContDiff ℝ ⊤ (fun p : ℝ × ℝ =>
      concatLeftParameter n p.2) :=
    (contDiff_concatLeftParameter n).comp contDiff_snd
  have hb : ContDiff ℝ ⊤ (fun p : ℝ × ℝ =>
      concatRightParameter n p.2) :=
    (contDiff_concatRightParameter n).comp contDiff_snd
  have hAc : ContDiff ℝ ⊤ (fun p : ℝ × ℝ =>
      A p.1 (concatLeftParameter n p.2)) :=
    hA.comp (contDiff_fst.prodMk ha)
  have hBc : ContDiff ℝ ⊤ (fun p : ℝ × ℝ =>
      B p.1 (concatRightParameter n p.2)) :=
    hB.comp (contDiff_fst.prodMk hb)
  simpa [analyticConcat] using
    ((contDiff_const.sub contDiff_snd).smul hAc).add (contDiff_snd.smul hBc)

@[simp] theorem analyticConcat_zero (A B : ℝ → ℝ → Space) (n : ℕ) (t : ℝ) :
    analyticConcat A B n t 0 = A t 0 := by
  simp [analyticConcat, concatLeftParameter]

@[simp] theorem analyticConcat_one (A B : ℝ → ℝ → Space) (n : ℕ) (t : ℝ) :
    analyticConcat A B n t 1 = B t 1 := by
  simp [analyticConcat, concatRightParameter]

theorem velocity_analyticConcat {A B : ℝ → ℝ → Space}
    (hA : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => A p.1 p.2))
    (hB : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => B p.1 p.2))
    (n : ℕ) (s t : ℝ) :
    velocity (fun x => analyticConcat A B n x s) t =
      (1 - s) • velocity (fun x => A x (concatLeftParameter n s)) t +
        s • velocity (fun x => B x (concatRightParameter n s)) t := by
  have hAd := hasDerivAt_familySlice hA t (concatLeftParameter n s)
  have hBd := hasDerivAt_familySlice hB t (concatRightParameter n s)
  have hsum := (hAd.const_smul (1 - s)).add (hBd.const_smul s)
  have hsum' : HasDerivAt (fun x => analyticConcat A B n x s)
      ((1 - s) • familyVelocity A (t, concatLeftParameter n s) +
        s • familyVelocity B (t, concatRightParameter n s)) t :=
    hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)
  simpa [velocity, familyVelocity_eq_velocity hA,
    familyVelocity_eq_velocity hB] using hsum'.deriv

set_option maxHeartbeats 1000000 in
theorem exists_uniform_concat_bound {A B : ℝ → ℝ → Space}
    (hA : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => A p.1 p.2))
    (hB : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => B p.1 p.2))
    (hAknot : ∀ s ∈ Icc (0 : ℝ) 1, IsSmoothKnot (fun t => A t s))
    (hBknot : ∀ s ∈ Icc (0 : ℝ) 1, IsSmoothKnot (fun t => B t s)) :
    ∃ M : ℝ, 0 < M ∧ ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
      ∀ t : ℝ,
        ‖B t b - A t a‖ < M ∧
        ‖velocity (fun x => B x b) t - velocity (fun x => A x a) t‖ < M := by
  let D : Set (ℝ × (ℝ × ℝ)) :=
    Icc (0 : ℝ) period ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
  have hDcompact : IsCompact D := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hDnonempty : D.Nonempty := by
    exact ⟨(0, (0, 0)), ⟨⟨le_rfl, period_pos.le⟩,
      ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩⟩⟩⟩
  let F : ℝ × (ℝ × ℝ) → ℝ := fun z => max
    ‖B z.1 z.2.2 - A z.1 z.2.1‖
    ‖familyVelocity B (z.1, z.2.2) - familyVelocity A (z.1, z.2.1)‖
  have hFcont : Continuous F := by
    apply Continuous.max
    · exact ((hB.continuous.comp (continuous_fst.prodMk
          (continuous_snd.comp continuous_snd))).sub
        (hA.continuous.comp (continuous_fst.prodMk
          (continuous_fst.comp continuous_snd)))).norm
    · exact (((continuous_familyVelocity hB).comp (continuous_fst.prodMk
          (continuous_snd.comp continuous_snd))).sub
        ((continuous_familyVelocity hA).comp (continuous_fst.prodMk
          (continuous_fst.comp continuous_snd)))).norm
  obtain ⟨z₀, hz₀, hmax⟩ := hDcompact.exists_isMaxOn hDnonempty
    hFcont.continuousOn
  let M := F z₀ + 1
  have hMpos : 0 < M := by
    have hnonneg : 0 ≤ F z₀ := by
      exact le_max_of_le_left (norm_nonneg _)
    dsimp [M]
    linarith
  refine ⟨M, hMpos, ?_⟩
  intro a ha b hb t
  let fp : ℝ → Space := fun x => B x b - A x a
  have hfpperiod : Function.Periodic fp period :=
    (hBknot b hb).periodic.sub (hAknot a ha).periodic
  obtain ⟨tp, htp, htpeq⟩ := hfpperiod.exists_mem_Ico period_pos t 0
  have htpD : (tp, (a, b)) ∈ D := by
    change tp ∈ Icc (0 : ℝ) period ∧
      (a ∈ Icc (0 : ℝ) 1 ∧ b ∈ Icc (0 : ℝ) 1)
    exact ⟨⟨htp.1, by simpa using htp.2.le⟩, ⟨ha, hb⟩⟩
  have hFp := hmax htpD
  have hposBound : ‖B t b - A t a‖ < M := by
    have hle : ‖B tp b - A tp a‖ ≤ F (tp, (a, b)) := by
      exact le_max_left _ _
    rw [show B t b - A t a = fp t by rfl, htpeq]
    dsimp [fp]
    exact (hle.trans hFp).trans_lt (lt_add_one _)
  let fv : ℝ → Space := fun x =>
    velocity (fun y => B y b) x - velocity (fun y => A y a) x
  have hfvperiod : Function.Periodic fv period :=
    (periodic_velocity (hBknot b hb)).sub (periodic_velocity (hAknot a ha))
  obtain ⟨tv, htv, htveq⟩ := hfvperiod.exists_mem_Ico period_pos t 0
  have htvD : (tv, (a, b)) ∈ D := by
    change tv ∈ Icc (0 : ℝ) period ∧
      (a ∈ Icc (0 : ℝ) 1 ∧ b ∈ Icc (0 : ℝ) 1)
    exact ⟨⟨htv.1, by simpa using htv.2.le⟩, ⟨ha, hb⟩⟩
  have hFv := hmax htvD
  have hvelBound : ‖velocity (fun x => B x b) t -
      velocity (fun x => A x a) t‖ < M := by
    have hle : ‖familyVelocity B (tv, b) - familyVelocity A (tv, a)‖ ≤
        F (tv, (a, b)) := by
      exact le_max_right _ _
    rw [show velocity (fun x => B x b) t - velocity (fun x => A x a) t =
      fv t by rfl, htveq]
    dsimp [fv]
    rw [← familyVelocity_eq_velocity hB tv b,
      ← familyVelocity_eq_velocity hA tv a]
    exact (hle.trans hFv).trans_lt (lt_add_one _)
  exact ⟨hposBound, hvelBound⟩

theorem exists_uniform_c1_close_endpoint_radius {A : ℝ → ℝ → Space}
    (hA : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => A p.1 p.2))
    {q : ℝ → Space} {c epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hendpoint : ∀ t, A t c = q t) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ a, |a - c| < eta →
      ∀ t ∈ Icc (0 : ℝ) period,
        ‖A t a - q t‖ < epsilon ∧
        ‖familyVelocity A (t, a) - velocity q t‖ < epsilon := by
  let K : Set (ℝ × ℝ) :=
    Icc (0 : ℝ) period ×ˢ Icc (c - 1) (c + 1)
  have hKcompact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  let G : ℝ × ℝ → Space × Space := fun z =>
    (A z.1 z.2, familyVelocity A (z.1, z.2))
  have hGcont : Continuous G :=
    (hA.continuous.prodMk (continuous_familyVelocity hA))
  have hGuc : UniformContinuousOn G K :=
    hKcompact.uniformContinuousOn_of_continuous hGcont.continuousOn
  obtain ⟨delta, hdelta, hclose⟩ := (Metric.uniformContinuousOn_iff.mp hGuc)
    epsilon hepsilon
  let eta := min delta 1
  have heta : 0 < eta := lt_min hdelta zero_lt_one
  refine ⟨eta, heta, ?_⟩
  intro a ha t ht
  have haLower : c - 1 ≤ a := by
    have habs : |a - c| < 1 := ha.trans_le (min_le_right delta 1)
    linarith [(abs_lt.mp habs).1]
  have haUpper : a ≤ c + 1 := by
    have habs : |a - c| < 1 := ha.trans_le (min_le_right delta 1)
    linarith [(abs_lt.mp habs).2]
  have htc : (t, c) ∈ K := ⟨ht, by constructor <;> linarith⟩
  have hta : (t, a) ∈ K := ⟨ht, ⟨haLower, haUpper⟩⟩
  have hdist : dist (t, a) (t, c) < delta := by
    rw [dist_prod_same_left, Real.dist_eq]
    exact ha.trans_le (min_le_left delta 1)
  have hG := hclose (t, a) hta (t, c) htc hdist
  rw [Prod.dist_eq, max_lt_iff] at hG
  have hpos : ‖A t a - q t‖ < epsilon := by
    rw [← hendpoint t, ← dist_eq_norm]
    exact hG.1
  have hvel : ‖familyVelocity A (t, a) - velocity q t‖ < epsilon := by
    have hcvel : familyVelocity A (t, c) = velocity q t := by
      rw [familyVelocity_eq_velocity hA]
      have hfun : (fun x => A x c) = q := funext hendpoint
      rw [hfun]
    rw [← hcvel]
    rw [← dist_eq_norm]
    exact hG.2
  exact ⟨hpos, hvel⟩

theorem uniform_c1_close_all_of_on_period {A : ℝ → ℝ → Space}
    (hA : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => A p.1 p.2))
    {q : ℝ → Space} (hq : IsSmoothKnot q)
    (hAknot : ∀ s ∈ Icc (0 : ℝ) 1, IsSmoothKnot (fun t => A t s))
    {a epsilon : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hclose : ∀ t ∈ Icc (0 : ℝ) period,
      ‖A t a - q t‖ < epsilon ∧
      ‖familyVelocity A (t, a) - velocity q t‖ < epsilon) :
    ∀ t, ‖A t a - q t‖ < epsilon ∧
      ‖velocity (fun x => A x a) t - velocity q t‖ < epsilon := by
  intro t
  let fp : ℝ → Space := fun x => A x a - q x
  have hfpperiod : Function.Periodic fp period :=
    (hAknot a ha).periodic.sub hq.periodic
  obtain ⟨tp, htp, htpeq⟩ := hfpperiod.exists_mem_Ico period_pos t 0
  have htpIcc : tp ∈ Icc (0 : ℝ) period :=
    ⟨htp.1, by simpa using htp.2.le⟩
  have hp := (hclose tp htpIcc).1
  have hpos : ‖A t a - q t‖ < epsilon := by
    change ‖fp t‖ < epsilon
    rw [htpeq]
    exact hp
  let fv : ℝ → Space := fun x =>
    velocity (fun y => A y a) x - velocity q x
  have hfvperiod : Function.Periodic fv period :=
    (periodic_velocity (hAknot a ha)).sub (periodic_velocity hq)
  obtain ⟨tv, htv, htveq⟩ := hfvperiod.exists_mem_Ico period_pos t 0
  have htvIcc : tv ∈ Icc (0 : ℝ) period :=
    ⟨htv.1, by simpa using htv.2.le⟩
  have hv := (hclose tv htvIcc).2
  rw [familyVelocity_eq_velocity hA] at hv
  have hvel : ‖velocity (fun x => A x a) t - velocity q t‖ < epsilon := by
    change ‖fv t‖ < epsilon
    rw [htveq]
    exact hv
  exact ⟨hpos, hvel⟩

def IsKnotIsotopic (p q : ℝ → Space) : Prop :=
  ∃ R : ℝ → ℝ → Space,
    ContDiff ℝ ⊤ (fun z : ℝ × ℝ => R z.1 z.2) ∧
      (∀ t, R t 0 = p t) ∧
      (∀ t, R t 1 = q t) ∧
      ∀ s ∈ Icc (0 : ℝ) 1, IsSmoothKnot (fun t => R t s)

noncomputable def analyticCompose (A B : ℝ → ℝ → Space) (q : ℝ → Space)
    (n : ℕ) (t s : ℝ) : Space :=
  A t (concatLeftParameter n s) + B t (concatRightParameter n s) - q t

theorem contDiff_analyticCompose {A B : ℝ → ℝ → Space} {q : ℝ → Space}
    (hA : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => A p.1 p.2))
    (hB : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => B p.1 p.2))
    (hq : ContDiff ℝ ⊤ q) (n : ℕ) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ => analyticCompose A B q n p.1 p.2) := by
  have ha : ContDiff ℝ ⊤ (fun p : ℝ × ℝ =>
      concatLeftParameter n p.2) :=
    (contDiff_concatLeftParameter n).comp contDiff_snd
  have hb : ContDiff ℝ ⊤ (fun p : ℝ × ℝ =>
      concatRightParameter n p.2) :=
    (contDiff_concatRightParameter n).comp contDiff_snd
  have hAc : ContDiff ℝ ⊤ (fun p : ℝ × ℝ =>
      A p.1 (concatLeftParameter n p.2)) :=
    hA.comp (contDiff_fst.prodMk ha)
  have hBc : ContDiff ℝ ⊤ (fun p : ℝ × ℝ =>
      B p.1 (concatRightParameter n p.2)) :=
    hB.comp (contDiff_fst.prodMk hb)
  simpa [analyticCompose] using
    hAc.add hBc |>.sub (hq.comp contDiff_fst)

theorem velocity_analyticCompose {A B : ℝ → ℝ → Space} {q : ℝ → Space}
    (hA : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => A p.1 p.2))
    (hB : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => B p.1 p.2))
    (hq : ContDiff ℝ ⊤ q) (n : ℕ) (s t : ℝ) :
    velocity (fun x => analyticCompose A B q n x s) t =
      velocity (fun x => A x (concatLeftParameter n s)) t +
        velocity (fun x => B x (concatRightParameter n s)) t - velocity q t := by
  have hAd := hasDerivAt_familySlice hA t (concatLeftParameter n s)
  have hBd := hasDerivAt_familySlice hB t (concatRightParameter n s)
  have hqd : HasDerivAt q (deriv q t) t :=
    (hq.differentiable (by simp)).differentiableAt.hasDerivAt
  have hsum := hAd.add hBd |>.sub hqd
  have hsum' : HasDerivAt (fun x => analyticCompose A B q n x s)
      (familyVelocity A (t, concatLeftParameter n s) +
        familyVelocity B (t, concatRightParameter n s) - deriv q t) t :=
    hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)
  simpa [velocity, familyVelocity_eq_velocity hA,
    familyVelocity_eq_velocity hB] using hsum'.deriv

set_option maxHeartbeats 2000000 in
theorem IsKnotIsotopic.trans {p q r : ℝ → Space}
    (hpq : IsKnotIsotopic p q) (hqr : IsKnotIsotopic q r) :
    IsKnotIsotopic p r := by
  rcases hpq with ⟨A, hA, hA0, hA1, hAknot⟩
  rcases hqr with ⟨B, hB, hB0, hB1, hBknot⟩
  have hqknot : IsSmoothKnot q := by
    simpa only [hA1] using hAknot 1 ⟨zero_le_one, le_rfl⟩
  obtain ⟨epsilonA, hepsilonA, hstableA⟩ :=
    exists_uniform_c1_knot_family_neighborhood hA hAknot
  obtain ⟨epsilonB, hepsilonB, hstableB⟩ :=
    exists_uniform_c1_knot_family_neighborhood hB hBknot
  obtain ⟨etaA, hetaA, hcloseA⟩ :=
    exists_uniform_c1_close_endpoint_radius hA hepsilonB hA1
  obtain ⟨etaB, hetaB, hcloseB⟩ :=
    exists_uniform_c1_close_endpoint_radius hB hepsilonA hB0
  let eta := min etaA etaB
  have heta : 0 < eta := lt_min hetaA hetaB
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one heta
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hn' : (1 / 2 : ℝ) ^ (n + 1) < eta := by
    rw [pow_succ]
    have hnonneg : 0 ≤ (1 / 2 : ℝ) ^ n := pow_nonneg (by norm_num) n
    have hle : (1 / 2 : ℝ) ^ n * (1 / 2) ≤ (1 / 2 : ℝ) ^ n := by
      nlinarith
    exact hle.trans_lt hn
  refine ⟨analyticCompose A B q (n + 1),
    contDiff_analyticCompose hA hB hqknot.smooth (n + 1), ?_, ?_, ?_⟩
  · intro t
    simp [analyticCompose, concatLeftParameter, concatRightParameter,
      hA0, hB0]
  · intro t
    simp [analyticCompose, concatLeftParameter, concatRightParameter,
      hA1, hB1]
  · intro s hs
    let a := concatLeftParameter (n + 1) s
    let b := concatRightParameter (n + 1) s
    have ha : a ∈ Icc (0 : ℝ) 1 := concatLeftParameter_mem_Icc (n + 1) hs
    have hb : b ∈ Icc (0 : ℝ) 1 := concatRightParameter_mem_Icc (n + 1) hs
    have hCsmooth : ContDiff ℝ ⊤
        (fun t => analyticCompose A B q (n + 1) t s) :=
      (contDiff_analyticCompose hA hB hqknot.smooth (n + 1)).comp
        (contDiff_id.prodMk contDiff_const)
    have hCperiod : Function.Periodic
        (fun t => analyticCompose A B q (n + 1) t s) period := by
      simpa [analyticCompose, a, b] using
        ((hAknot a ha).periodic.add (hBknot b hb).periodic).sub hqknot.periodic
    by_cases hsleft : s ≤ 1 / 2
    · have hbsmall : |b - 0| < etaB := by
        have hpow : s ^ (n + 1) ≤ (1 / 2 : ℝ) ^ (n + 1) :=
          pow_le_pow_left₀ hs.1 hsleft (n + 1)
        have hpowNonneg : 0 ≤ s ^ (n + 1) := pow_nonneg hs.1 (n + 1)
        dsimp [b, concatRightParameter]
        rw [sub_zero, abs_of_nonneg hpowNonneg]
        exact hpow.trans_lt (hn'.trans_le (min_le_right etaA etaB))
      have hBclosePeriod := hcloseB b hbsmall
      have hBclose := uniform_c1_close_all_of_on_period hB hqknot hBknot hb
        hBclosePeriod
      apply hstableA a ha (fun t => analyticCompose A B q (n + 1) t s)
        hCsmooth hCperiod
      · intro t
        have hnear := (hBclose t).1
        rw [show analyticCompose A B q (n + 1) t s - A t a =
            B t b - q t by
          simp only [analyticCompose, a, b]
          module]
        exact hnear
      · intro t
        have hnear := (hBclose t).2
        rw [velocity_analyticCompose hA hB hqknot.smooth]
        simpa [a, b, show
          velocity (fun x => A x a) t + velocity (fun x => B x b) t -
              velocity q t - velocity (fun x => A x a) t =
            velocity (fun x => B x b) t - velocity q t by abel] using hnear
    · have hsright : 1 - s ≤ 1 / 2 := by linarith
      have habase : 0 ≤ 1 - s := sub_nonneg.mpr hs.2
      have hapow : (1 - s) ^ n ≤ (1 / 2 : ℝ) ^ n :=
        pow_le_pow_left₀ habase hsright n
      have hasmall : |a - 1| < etaA := by
        have hpowNonneg : 0 ≤ (1 - s) ^ (n + 1) := pow_nonneg habase (n + 1)
        dsimp [a, concatLeftParameter]
        rw [show 1 - (1 - s) ^ (n + 1) - 1 = -((1 - s) ^ (n + 1)) by ring,
          abs_neg, abs_of_nonneg hpowNonneg]
        have hapow' : (1 - s) ^ (n + 1) ≤ (1 / 2 : ℝ) ^ (n + 1) :=
          pow_le_pow_left₀ habase hsright (n + 1)
        exact hapow'.trans_lt (hn'.trans_le (min_le_left etaA etaB))
      have hAclosePeriod := hcloseA a hasmall
      have hAclose := uniform_c1_close_all_of_on_period hA hqknot hAknot ha
        hAclosePeriod
      apply hstableB b hb (fun t => analyticCompose A B q (n + 1) t s)
        hCsmooth hCperiod
      · intro t
        have hnear := (hAclose t).1
        rw [show analyticCompose A B q (n + 1) t s - B t b =
            A t a - q t by
          simp only [analyticCompose, a, b]
          module]
        exact hnear
      · intro t
        have hnear := (hAclose t).2
        rw [velocity_analyticCompose hA hB hqknot.smooth]
        simpa [a, b, show
          velocity (fun x => A x a) t + velocity (fun x => B x b) t -
              velocity q t - velocity (fun x => B x b) t =
            velocity (fun x => A x a) t - velocity q t by abel] using hnear

end Submission.Helpers
