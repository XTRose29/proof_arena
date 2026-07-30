import ChallengeDeps
import Submission.Helpers

open Set
open scoped Topology ContDiff

noncomputable section

namespace Submission.CK

open LeanEval.Analysis
open Submission.Helpers

variable {d : ℕ}

def characteristicField (F : E d × ℝ × ℝ → E d) (f : E d × ℝ × ℝ → ℝ) :
    ℝ × (E d × ℝ) → E d × ℝ :=
  fun z => (-F (z.2.1, z.1, z.2.2), f (z.2.1, z.1, z.2.2))

theorem analyticOnNhd_characteristicField
    {F : E d × ℝ × ℝ → E d} {f : E d × ℝ × ℝ → ℝ}
    (hF : AnalyticOnNhd ℝ F univ) (hf : AnalyticOnNhd ℝ f univ) :
    AnalyticOnNhd ℝ (characteristicField F f) univ := by
  intro z _
  have harg : AnalyticAt ℝ (fun z : ℝ × (E d × ℝ) => (z.2.1, z.1, z.2.2)) z := by
    have ht : AnalyticAt ℝ (fun z : ℝ × (E d × ℝ) => z.1) z :=
      (ContinuousLinearMap.fst ℝ ℝ (E d × ℝ)).analyticAt z
    have hstate : AnalyticAt ℝ (fun z : ℝ × (E d × ℝ) => z.2) z :=
      (ContinuousLinearMap.snd ℝ ℝ (E d × ℝ)).analyticAt z
    have hx : AnalyticAt ℝ (fun z : ℝ × (E d × ℝ) => z.2.1) z :=
      (ContinuousLinearMap.fst ℝ (E d) ℝ).analyticAt z.2 |>.comp hstate
    have hu : AnalyticAt ℝ (fun z : ℝ × (E d × ℝ) => z.2.2) z :=
      (ContinuousLinearMap.snd ℝ (E d) ℝ).analyticAt z.2 |>.comp hstate
    exact hx.prod (ht.prod hu)
  exact ((hF _ (mem_univ _)).comp harg).neg.prod ((hf _ (mem_univ _)).comp harg)

def initialState (u₀ : E d → ℝ) (x : E d) : E d × ℝ := (x, u₀ x)

def flowInput (u₀ : E d → ℝ) (q : E d × ℝ) : (E d × ℝ) × ℝ :=
  (initialState u₀ q.1, q.2)

def characteristic (φ : (E d × ℝ) × ℝ → E d × ℝ) (u₀ : E d → ℝ)
    (q : E d × ℝ) : E d × ℝ :=
  φ (flowInput u₀ q)

def spaceTime (φ : (E d × ℝ) × ℝ → E d × ℝ) (u₀ : E d → ℝ)
    (q : E d × ℝ) : E d × ℝ :=
  ((characteristic φ u₀ q).1, q.2)

def characteristicChart (φ : (E d × ℝ) × ℝ → E d × ℝ) (u₀ : E d → ℝ)
    (c : E d) (q : E d × ℝ) : E d × ℝ :=
  timeShearHomeomorph c (spaceTime φ u₀ q)

theorem analyticAt_flowInput {u₀ : E d → ℝ} (hu₀ : AnalyticOnNhd ℝ u₀ univ)
    (q : E d × ℝ) : AnalyticAt ℝ (flowInput u₀) q := by
  have hfst : AnalyticAt ℝ (fun p : E d × ℝ => p.1) q :=
    (ContinuousLinearMap.fst ℝ (E d) ℝ).analyticAt q
  have hsnd : AnalyticAt ℝ (fun p : E d × ℝ => p.2) q :=
    (ContinuousLinearMap.snd ℝ (E d) ℝ).analyticAt q
  have hinit : AnalyticAt ℝ (initialState u₀) q.1 :=
    analyticAt_id.prod (hu₀ q.1 (mem_univ _))
  exact (hinit.comp hfst).prod hsnd

theorem analyticAt_characteristicChart
    {u₀ : E d → ℝ} (hu₀ : AnalyticOnNhd ℝ u₀ univ)
    {φ : (E d × ℝ) × ℝ → E d × ℝ} {δ : ℝ} {x₀ : E d}
    (hφ : AnalyticOnNhd ℝ φ
      (Metric.ball (initialState u₀ x₀, (0 : ℝ)) δ))
    {q : E d × ℝ}
    (hq : flowInput u₀ q ∈ Metric.ball (initialState u₀ x₀, (0 : ℝ)) δ)
    (c : E d) : AnalyticAt ℝ (characteristicChart φ u₀ c) q := by
  have hchar : AnalyticAt ℝ (characteristic φ u₀) q :=
    (hφ _ hq).comp (analyticAt_flowInput hu₀ q)
  have hcharFirst : AnalyticAt ℝ (fun q => (characteristic φ u₀ q).1) q :=
    (ContinuousLinearMap.fst ℝ (E d) ℝ).analyticAt _ |>.comp hchar
  have hqSecond : AnalyticAt ℝ (fun q : E d × ℝ => q.2) q :=
    (ContinuousLinearMap.snd ℝ (E d) ℝ).analyticAt q
  have hspace : AnalyticAt ℝ (spaceTime φ u₀) q := hcharFirst.prod hqSecond
  have hshear : AnalyticAt ℝ (timeShearHomeomorph c) (spaceTime φ u₀ q) := by
    change AnalyticAt ℝ (fun p : E d × ℝ => (p.1 + p.2 • c, p.2)) _
    have hfst := (ContinuousLinearMap.fst ℝ (E d) ℝ).analyticAt (spaceTime φ u₀ q)
    have hsnd := (ContinuousLinearMap.snd ℝ (E d) ℝ).analyticAt (spaceTime φ u₀ q)
    exact (hfst.add (hsnd.smul analyticAt_const)).prod hsnd
  exact hshear.comp hspace

theorem characteristicChart_apply_zero
    {u₀ : E d → ℝ} {φ : (E d × ℝ) × ℝ → E d × ℝ}
    {δ : ℝ} {x₀ x : E d}
    (hinit : ∀ y, (y, (0 : ℝ)) ∈ Metric.ball (initialState u₀ x₀, (0 : ℝ)) δ →
      φ (y, 0) = y)
    (hx : (initialState u₀ x, (0 : ℝ)) ∈
      Metric.ball (initialState u₀ x₀, (0 : ℝ)) δ)
    (c : E d) : characteristicChart φ u₀ c (x, 0) = (x, 0) := by
  have h := hinit (initialState u₀ x) hx
  unfold characteristicChart spaceTime characteristic flowInput
  rw [h]
  simp [initialState]

theorem characteristicChart_fderiv_base
    {F : E d × ℝ × ℝ → E d} {f : E d × ℝ × ℝ → ℝ}
    {u₀ : E d → ℝ} {φ : (E d × ℝ) × ℝ → E d × ℝ}
    {δ : ℝ} {x₀ : E d}
    (hu₀ : AnalyticOnNhd ℝ u₀ univ)
    (hφ : AnalyticOnNhd ℝ φ
      (Metric.ball (initialState u₀ x₀, (0 : ℝ)) δ))
    (hinit : ∀ y, (y, (0 : ℝ)) ∈ Metric.ball (initialState u₀ x₀, (0 : ℝ)) δ →
      φ (y, 0) = y)
    (hderiv : ∀ p ∈ Metric.ball (initialState u₀ x₀, (0 : ℝ)) δ,
      HasDerivAt (fun t => φ (p.1, t))
        (characteristicField F f (p.2, φ p)) p.2)
    (hδ : 0 < δ) :
    fderiv ℝ (characteristicChart φ u₀ (F (x₀, 0, u₀ x₀))) (x₀, 0) =
      ContinuousLinearMap.id ℝ (E d × ℝ) := by
  let y₀ := initialState u₀ x₀
  let q₀ : E d × ℝ := (x₀, 0)
  let c := F (x₀, 0, u₀ x₀)
  have hbase : (y₀, (0 : ℝ)) ∈ Metric.ball (y₀, (0 : ℝ)) δ :=
    Metric.mem_ball_self hδ
  have hchartAt : AnalyticAt ℝ (characteristicChart φ u₀ c) q₀ := by
    apply analyticAt_characteristicChart hu₀ hφ
    simpa [q₀, y₀, flowInput, initialState]
  have hinl : HasFDerivAt (fun x : E d => (x, (0 : ℝ)))
      (ContinuousLinearMap.inl ℝ (E d) ℝ) x₀ := by fun_prop
  have hhorizontal := hchartAt.hasStrictFDerivAt.hasFDerivAt.comp x₀ hinl
  have hnear : ∀ᶠ x in 𝓝 x₀,
      (initialState u₀ x, (0 : ℝ)) ∈ Metric.ball (y₀, (0 : ℝ)) δ := by
    have hcont : ContinuousAt (fun x => (initialState u₀ x, (0 : ℝ))) x₀ :=
      ((analyticAt_id.prod (hu₀ x₀ (mem_univ _))).prod analyticAt_const).continuousAt
    exact hcont (Metric.isOpen_ball.mem_nhds hbase)
  have heq : (fun x => characteristicChart φ u₀ c (x, 0)) =ᶠ[𝓝 x₀]
      fun x => (x, (0 : ℝ)) := by
    filter_upwards [hnear] with x hx
    exact characteristicChart_apply_zero hinit hx c
  have hstandard : HasFDerivAt (fun x : E d => (x, (0 : ℝ)))
      (ContinuousLinearMap.inl ℝ (E d) ℝ) x₀ := by fun_prop
  have hhorizontal' := hstandard.congr_of_eventuallyEq heq
  have hhorEq := hhorizontal.unique hhorizontal'
  have hhor (v : E d) :
      fderiv ℝ (characteristicChart φ u₀ c) q₀ (v, 0) = (v, 0) := by
    have := congrArg (fun A : E d →L[ℝ] E d × ℝ => A v) hhorEq
    simpa [q₀] using this
  have hflow := hderiv (y₀, 0) hbase
  have hflowValue : φ (y₀, 0) = y₀ := hinit y₀ hbase
  rw [hflowValue] at hflow
  have hflowFirst : HasDerivAt (fun t => (φ (y₀, t)).1) (-c) 0 := by
    have h := (ContinuousLinearMap.fst ℝ (E d) ℝ).hasFDerivAt.comp_hasDerivAt 0 hflow
    simpa [characteristicField, y₀, initialState, c, Function.comp_def] using h
  have hfirst : HasDerivAt (fun t => (φ (y₀, t)).1 + t • c) 0 0 := by
    have hc : HasDerivAt (fun t : ℝ => t • c) c 0 := by
      simpa using HasDerivAt.smul_const (hasDerivAt_id (𝕜 := ℝ) 0) c
    have h := hflowFirst.add hc
    have hzero : (-c : E d) + c = 0 := neg_add_cancel c
    rw [hzero] at h
    change HasDerivAt (fun t : ℝ => ((φ (y₀, t)).1 + t • c : E d)) 0 0 at h
    exact h
  have hvertical : HasDerivAt (fun t => characteristicChart φ u₀ c (x₀, t))
      ((0 : E d), (1 : ℝ)) 0 := by
    convert hfirst.prodMk (hasDerivAt_id (𝕜 := ℝ) 0) using 1
    all_goals simp [characteristicChart, spaceTime, characteristic, flowInput, y₀, initialState]
  have hvertEq :=
    (hchartAt.hasStrictFDerivAt.hasFDerivAt.comp_hasDerivAt 0
      ((hasDerivAt_const (x := (0 : ℝ)) (c := x₀)).prodMk
        (hasDerivAt_id (𝕜 := ℝ) 0))).unique hvertical
  apply ContinuousLinearMap.ext
  intro v
  have hdecomp : v = (v.1, (0 : ℝ)) + v.2 • ((0 : E d), (1 : ℝ)) := by
    ext <;> simp
  rw [hdecomp, map_add, map_smul, hhor, hvertEq]
  simp

theorem exists_local_solution_preconnected
    (F : E d × ℝ × ℝ → E d) (f : E d × ℝ × ℝ → ℝ) (u₀ : E d → ℝ)
    (hF : AnalyticOnNhd ℝ F univ) (hf : AnalyticOnNhd ℝ f univ)
    (hu₀ : AnalyticOnNhd ℝ u₀ univ) (x₀ : E d) :
    ∃ (U : Set (E d × ℝ)) (u : E d × ℝ → ℝ),
      (x₀, (0 : ℝ)) ∈ U ∧ IsOpen U ∧ IsPreconnected U ∧ AnalyticOnNhd ℝ u U ∧
      (∀ x : E d, (x, (0 : ℝ)) ∈ U → u (x, 0) = u₀ x) ∧
      ∀ p ∈ U,
        fderiv ℝ u p ((0 : E d), (1 : ℝ)) =
          fderiv ℝ u p (F (p.1, p.2, u p), (0 : ℝ)) + f (p.1, p.2, u p) := by
  let V := characteristicField F f
  have hV : AnalyticOnNhd ℝ V univ := analyticOnNhd_characteristicField hF hf
  let y₀ := initialState u₀ x₀
  obtain ⟨δ, hδ, φ, hφ, hinit, hderiv⟩ :=
    exists_analytic_localFlow V hV y₀
  let c := F (x₀, 0, u₀ x₀)
  let q₀ : E d × ℝ := (x₀, 0)
  let chart := characteristicChart φ u₀ c
  have hflowBase : flowInput u₀ q₀ ∈ Metric.ball (y₀, (0 : ℝ)) δ := by
    simpa [q₀, y₀, flowInput, initialState] using
      (Metric.mem_ball_self hδ : (y₀, (0 : ℝ)) ∈ Metric.ball (y₀, (0 : ℝ)) δ)
  have hchartAt : AnalyticAt ℝ chart q₀ := by
    exact analyticAt_characteristicChart hu₀ hφ hflowBase c
  have hchartZero : chart q₀ = q₀ := by
    exact characteristicChart_apply_zero hinit hflowBase c
  have hchartDeriv : fderiv ℝ chart q₀ = ContinuousLinearMap.id ℝ (E d × ℝ) := by
    exact characteristicChart_fderiv_base hu₀ hφ hinit hderiv hδ
  let e : (E d × ℝ) ≃L[ℝ] (E d × ℝ) := ContinuousLinearEquiv.refl ℝ (E d × ℝ)
  have hchartF : HasFDerivAt chart (e : (E d × ℝ) →L[ℝ] (E d × ℝ)) q₀ := by
    have h := hchartAt.hasStrictFDerivAt.hasFDerivAt
    rw [hchartDeriv] at h
    simpa [e] using h
  have hchartC : ContDiffAt ℝ ω chart q₀ := hchartAt.contDiffAt
  have hω : (ω : ℕ∞ω) ≠ 0 := by simp
  let R := hchartC.toOpenPartialHomeomorph chart hchartF hω
  let inv := hchartC.localInverse hchartF hω
  have hinvR : inv = R.symm := rfl
  have hqSource : q₀ ∈ R.source := hchartC.mem_toOpenPartialHomeomorph_source hchartF hω
  have hinvAt : AnalyticAt ℝ inv q₀ := by
    have h := (hchartC.to_localInverse hchartF hω).analyticAt
    simpa [inv, hchartZero] using h
  have hflowNhd : flowInput u₀ ⁻¹' Metric.ball (y₀, (0 : ℝ)) δ ∈ 𝓝 q₀ := by
    exact (analyticAt_flowInput hu₀ q₀).continuousAt
      (by simpa [flowInput, q₀, y₀, initialState] using
        (Metric.ball_mem_nhds (y₀, (0 : ℝ)) hδ))
  have hinvNhd : chart ⁻¹' {z | AnalyticAt ℝ inv z} ∈ 𝓝 q₀ := by
    have hinvAt' : AnalyticAt ℝ inv (chart q₀) := by simpa [hchartZero] using hinvAt
    exact hchartAt.continuousAt ((isOpen_analyticAt ℝ inv).mem_nhds hinvAt')
  have hgoodNhd :
      R.source ∩ (flowInput u₀ ⁻¹' Metric.ball (y₀, (0 : ℝ)) δ) ∩
          chart ⁻¹' {z | AnalyticAt ℝ inv z} ∈ 𝓝 q₀ :=
    Filter.inter_mem (Filter.inter_mem (R.open_source.mem_nhds hqSource) hflowNhd) hinvNhd
  obtain ⟨ρ, hρ, hρgood⟩ := Metric.mem_nhds_iff.mp hgoodNhd
  let B := Metric.ball q₀ ρ
  have hBgood : B ⊆ R.source ∩ (flowInput u₀ ⁻¹' Metric.ball (y₀, (0 : ℝ)) δ) ∩
      chart ⁻¹' {z | AnalyticAt ℝ inv z} := hρgood
  have hBsource : B ⊆ R.source := fun q hq => (hBgood hq).1.1
  let S := timeShearHomeomorph c
  let U : Set (E d × ℝ) := S.symm '' (R '' B)
  let param : E d × ℝ → E d × ℝ := fun p => inv (S p)
  let u : E d × ℝ → ℝ := fun p => (characteristic φ u₀ (param p)).2
  have hparam (p : E d × ℝ) (hp : p ∈ U) :
      ∃ q ∈ B, param p = q ∧ S p = chart q := by
    rcases hp with ⟨z, ⟨q, hq, hz⟩, hpz⟩
    subst z
    have hRq : R q = chart q := rfl
    have hpEq : p = S.symm (R q) := hpz.symm
    refine ⟨q, hq, ?_, ?_⟩
    · rw [hpEq]
      simp only [param, Homeomorph.apply_symm_apply]
      rw [hinvR]
      exact R.left_inv (hBsource hq)
    · rw [hpEq, Homeomorph.apply_symm_apply, hRq]
  have hspace (p : E d × ℝ) (hp : p ∈ U) :
      spaceTime φ u₀ (param p) = p := by
    obtain ⟨q, hq, hpq, hSp⟩ := hparam p hp
    rw [hpq]
    apply S.injective
    rw [hSp]
    rfl
  have hparamGood (p : E d × ℝ) (hp : p ∈ U) :
      param p ∈ B := by
    obtain ⟨q, hq, hpq, _⟩ := hparam p hp
    simpa [hpq] using hq
  have hparamFlow (p : E d × ℝ) (hp : p ∈ U) :
      flowInput u₀ (param p) ∈ Metric.ball (y₀, (0 : ℝ)) δ :=
    (hBgood (hparamGood p hp)).1.2
  have hparamAnalytic (p : E d × ℝ) (hp : p ∈ U) : AnalyticAt ℝ param p := by
    obtain ⟨q, hq, hpq, hSp⟩ := hparam p hp
    have hinv : AnalyticAt ℝ inv (chart q) := (hBgood hq).2
    have hS : AnalyticAt ℝ S p := by
      change AnalyticAt ℝ (fun z : E d × ℝ => (z.1 + z.2 • c, z.2)) p
      have hfst := (ContinuousLinearMap.fst ℝ (E d) ℝ).analyticAt p
      have hsnd := (ContinuousLinearMap.snd ℝ (E d) ℝ).analyticAt p
      exact (hfst.add (hsnd.smul analyticAt_const)).prod hsnd
    rw [← hSp] at hinv
    have hcomp := hinv.comp hS
    simpa [param, Function.comp_def] using hcomp
  have huAnalytic : AnalyticOnNhd ℝ u U := by
    intro p hp
    have hchar : AnalyticAt ℝ (characteristic φ u₀) (param p) :=
      (hφ _ (hparamFlow p hp)).comp (analyticAt_flowInput hu₀ (param p))
    have hcomp := hchar.comp (hparamAnalytic p hp)
    exact (ContinuousLinearMap.snd ℝ (E d) ℝ).analyticAt _ |>.comp <| by
      simpa [u, Function.comp_def] using hcomp
  have hUOpen : IsOpen U := by
    apply S.symm.isOpenMap
    exact R.isOpen_image_of_subset_source Metric.isOpen_ball hBsource
  have hUPreconnected : IsPreconnected U := by
    have hBpre : IsPreconnected B := Metric.isPreconnected_ball
    have hRpre : IsPreconnected (R '' B) :=
      hBpre.image R (R.continuousOn.mono hBsource)
    exact hRpre.image S.symm S.symm.continuous.continuousOn
  have hq₀B : q₀ ∈ B := Metric.mem_ball_self hρ
  have hbaseU : q₀ ∈ U := by
    refine ⟨q₀, ⟨q₀, hq₀B, ?_⟩, ?_⟩
    · change chart q₀ = q₀
      exact hchartZero
    · simp [S, q₀]
  have hinitial : ∀ x : E d, (x, (0 : ℝ)) ∈ U → u (x, 0) = u₀ x := by
    intro x hx
    let p : E d × ℝ := (x, 0)
    have hs := hspace p hx
    have ht : (param p).2 = 0 := congrArg Prod.snd hs
    have hflow := hinit (initialState u₀ (param p).1) (by
      simpa [flowInput, ht] using hparamFlow p hx)
    have hchar : characteristic φ u₀ (param p) = initialState u₀ (param p).1 := by
      simpa [characteristic, flowInput, ht] using hflow
    have hxparam : (param p).1 = x := by
      have := congrArg Prod.fst hs
      simpa [spaceTime, p, hchar, initialState] using this
    change (characteristic φ u₀ (param p)).2 = u₀ x
    rw [hchar]
    simp [initialState, hxparam]
  refine ⟨U, u, hbaseU, hUOpen, hUPreconnected, huAnalytic, hinitial, ?_⟩
  intro p hp
  obtain ⟨q, hq, hpq, hSp⟩ := hparam p hp
  have hqflow : flowInput u₀ q ∈ Metric.ball (y₀, (0 : ℝ)) δ := (hBgood hq).1.2
  have hflow := hderiv (flowInput u₀ q) hqflow
  have hspaceq : spaceTime φ u₀ q = p := by simpa [hpq] using hspace p hp
  have huq : u p = (characteristic φ u₀ q).2 := by simp [u, hpq]
  have hqtime : q.2 = p.2 := by
    have := congrArg Prod.snd hspaceq
    simpa [spaceTime] using this
  have hqx : (characteristic φ u₀ q).1 = p.1 := by
    have := congrArg Prod.fst hspaceq
    simpa [spaceTime] using this
  have hflow' : HasDerivAt (fun t => characteristic φ u₀ (q.1, t))
      (V (q.2, characteristic φ u₀ q)) q.2 := by
    simpa [characteristic, flowInput] using hflow
  have hcurve : HasDerivAt (fun t => spaceTime φ u₀ (q.1, t))
      (-F (p.1, p.2, u p), (1 : ℝ)) q.2 := by
    have hfirst := (ContinuousLinearMap.fst ℝ (E d) ℝ).hasFDerivAt.comp_hasDerivAt q.2 hflow'
    have hfirst' : HasDerivAt (fun t => (characteristic φ u₀ (q.1, t)).1)
        (-F (p.1, p.2, u p)) q.2 := by
      simpa [V, characteristicField, hqx, hqtime, huq, Function.comp_def] using hfirst
    simpa [spaceTime] using hfirst'.prodMk (hasDerivAt_id (𝕜 := ℝ) q.2)
  have hvalue : HasDerivAt (fun t => (characteristic φ u₀ (q.1, t)).2)
      (f (p.1, p.2, u p)) q.2 := by
    have h := (ContinuousLinearMap.snd ℝ (E d) ℝ).hasFDerivAt.comp_hasDerivAt q.2 hflow'
    simpa [V, characteristicField, hqx, hqtime, huq, Function.comp_def] using h
  have hnearB : ∀ᶠ t in 𝓝 q.2, (q.1, t) ∈ B := by
    exact (continuousAt_const.prodMk continuousAt_id) (Metric.isOpen_ball.mem_nhds hq)
  have hcurveU (t : ℝ) (ht : (q.1, t) ∈ B) :
      spaceTime φ u₀ (q.1, t) ∈ U := by
    refine ⟨R (q.1, t), ⟨(q.1, t), ht, rfl⟩, ?_⟩
    change S.symm (chart (q.1, t)) = spaceTime φ u₀ (q.1, t)
    exact S.symm_apply_apply _
  have hcurveParam (t : ℝ) (ht : (q.1, t) ∈ B) :
      param (spaceTime φ u₀ (q.1, t)) = (q.1, t) := by
    have hmem := hcurveU t ht
    obtain ⟨q', hq', heq, hchart⟩ := hparam _ hmem
    rw [heq]
    apply R.injOn (hBsource hq') (hBsource ht)
    change chart q' = chart (q.1, t)
    rw [← hchart]
    rfl
  have heq : (fun t => u (spaceTime φ u₀ (q.1, t))) =ᶠ[𝓝 q.2]
      fun t => (characteristic φ u₀ (q.1, t)).2 := by
    filter_upwards [hnearB] with t ht
    simp [u, hcurveParam t ht]
  have huAt := (huAnalytic p hp).hasStrictFDerivAt.hasFDerivAt
  have hcomp := huAt.comp_hasDerivAt_of_eq q.2 hcurve (by simpa using hspaceq.symm)
  have hsame := hvalue.congr_of_eventuallyEq heq
  have hdirection : fderiv ℝ u p (-F (p.1, p.2, u p), (1 : ℝ)) =
      f (p.1, p.2, u p) := hcomp.unique hsame
  let A := fderiv ℝ u p
  have hdecomp : ((0 : E d), (1 : ℝ)) =
      (-F (p.1, p.2, u p), (1 : ℝ)) + (F (p.1, p.2, u p), (0 : ℝ)) := by
    ext <;> simp
  calc
    A ((0 : E d), (1 : ℝ)) =
        A ((-F (p.1, p.2, u p), (1 : ℝ)) + (F (p.1, p.2, u p), (0 : ℝ))) := by rw [hdecomp]
    _ = A (-F (p.1, p.2, u p), (1 : ℝ)) +
        A (F (p.1, p.2, u p), (0 : ℝ)) := map_add A _ _
    _ = f (p.1, p.2, u p) + A (F (p.1, p.2, u p), (0 : ℝ)) := by rw [hdirection]
    _ = A (F (p.1, p.2, u p), (0 : ℝ)) + f (p.1, p.2, u p) := add_comm _ _

def spatialField (F : E d × ℝ × ℝ → E d) (w : E d × ℝ → ℝ) :
    ℝ × E d → E d :=
  fun z => -F (z.2, z.1, w (z.2, z.1))

def graphMap (w : E d × ℝ → ℝ) : ℝ × E d → ℝ × (E d × ℝ) :=
  fun z => (z.1, (z.2, w (z.2, z.1)))

theorem hasDerivWithinAt_graphCurve
    {F : E d × ℝ × ℝ → E d} {f : E d × ℝ × ℝ → ℝ}
    {U : Set (E d × ℝ)} {w : E d × ℝ → ℝ}
    (hw : AnalyticOnNhd ℝ w U)
    (hPDE : ∀ p ∈ U,
      fderiv ℝ w p ((0 : E d), (1 : ℝ)) =
        fderiv ℝ w p (F (p.1, p.2, w p), (0 : ℝ)) + f (p.1, p.2, w p))
    {β : ℝ → ℝ × E d} {s scale : ℝ} {S : Set ℝ}
    (hβ : HasDerivWithinAt β
      (scale • augmentedField (spatialField F w) (β s)) S s)
    (hmem : ((β s).2, (β s).1) ∈ U) :
    HasDerivWithinAt (fun r => graphMap w (β r))
      (scale • augmentedField (characteristicField F f) (graphMap w (β s))) S s := by
  let p : E d × ℝ := ((β s).2, (β s).1)
  let X : E d := spatialField F w (β s)
  have htime : HasDerivWithinAt (fun r => (β r).1) scale S s := by
    have h := (ContinuousLinearMap.fst ℝ ℝ (E d)).hasFDerivAt.comp_hasDerivWithinAt s hβ
    simpa [augmentedField, Function.comp_def] using h
  have hx : HasDerivWithinAt (fun r => (β r).2) (scale • X) S s := by
    have h := (ContinuousLinearMap.snd ℝ ℝ (E d)).hasFDerivAt.comp_hasDerivWithinAt s hβ
    simpa [augmentedField, X, Function.comp_def] using h
  have hphysical : HasDerivWithinAt (fun r => ((β r).2, (β r).1))
      (scale • X, scale) S s := hx.prodMk htime
  have hwder := (hw p hmem).hasStrictFDerivAt.hasFDerivAt.comp_hasDerivWithinAt s hphysical
  have hdirection : fderiv ℝ w p (-F (p.1, p.2, w p), (1 : ℝ)) =
      f (p.1, p.2, w p) := by
    let A := fderiv ℝ w p
    have hdecomp : ((0 : E d), (1 : ℝ)) =
        (F (p.1, p.2, w p), (0 : ℝ)) + (-F (p.1, p.2, w p), (1 : ℝ)) := by
      ext <;> simp
    have hpde := hPDE p hmem
    change A ((0 : E d), (1 : ℝ)) =
      A (F (p.1, p.2, w p), (0 : ℝ)) + f (p.1, p.2, w p) at hpde
    rw [hdecomp, map_add] at hpde
    exact add_left_cancel hpde
  have hvalue : HasDerivWithinAt (fun r => w ((β r).2, (β r).1))
      (scale • f (p.1, p.2, w p)) S s := by
    have hscaled : (scale • X, scale) = scale • (-F (p.1, p.2, w p), (1 : ℝ)) := by
      simp [X, spatialField, p]
    have hmap : fderiv ℝ w p (scale • X, scale) = scale • f (p.1, p.2, w p) := by
      rw [hscaled, map_smul, hdirection]
    exact hwder.congr_deriv hmap
  have hgraph := htime.prodMk (hx.prodMk hvalue)
  simpa [graphMap, augmentedField, characteristicField, spatialField, p, X] using hgraph

theorem analyticAt_spatialField
    {F : E d × ℝ × ℝ → E d} {U : Set (E d × ℝ)} {w : E d × ℝ → ℝ}
    (hF : AnalyticOnNhd ℝ F univ) (hw : AnalyticOnNhd ℝ w U)
    {z : ℝ × E d} (hz : (z.2, z.1) ∈ U) :
    AnalyticAt ℝ (spatialField F w) z := by
  have htime : AnalyticAt ℝ (fun z : ℝ × E d => z.1) z :=
    (ContinuousLinearMap.fst ℝ ℝ (E d)).analyticAt z
  have hx : AnalyticAt ℝ (fun z : ℝ × E d => z.2) z :=
    (ContinuousLinearMap.snd ℝ ℝ (E d)).analyticAt z
  have hphysical : AnalyticAt ℝ (fun z : ℝ × E d => (z.2, z.1)) z := hx.prod htime
  have hwcomp : AnalyticAt ℝ (fun z : ℝ × E d => w (z.2, z.1)) z :=
    AnalyticAt.comp (f := fun z : ℝ × E d => (z.2, z.1)) (hw _ hz) hphysical
  have harg : AnalyticAt ℝ (fun z : ℝ × E d => (z.2, z.1, w (z.2, z.1))) z :=
    hx.prod (htime.prod hwcomp)
  exact ((hF _ (mem_univ _)).comp harg).neg

theorem analyticAt_graphMap
    {U : Set (E d × ℝ)} {w : E d × ℝ → ℝ}
    (hw : AnalyticOnNhd ℝ w U) {z : ℝ × E d} (hz : (z.2, z.1) ∈ U) :
    AnalyticAt ℝ (graphMap w) z := by
  have htime : AnalyticAt ℝ (fun z : ℝ × E d => z.1) z :=
    (ContinuousLinearMap.fst ℝ ℝ (E d)).analyticAt z
  have hx : AnalyticAt ℝ (fun z : ℝ × E d => z.2) z :=
    (ContinuousLinearMap.snd ℝ ℝ (E d)).analyticAt z
  have hphysical : AnalyticAt ℝ (fun z : ℝ × E d => (z.2, z.1)) z := hx.prod htime
  exact htime.prod (hx.prod
    (AnalyticAt.comp (f := fun z : ℝ × E d => (z.2, z.1)) (hw _ hz) hphysical))

theorem exists_graph_characteristic_flow
    {F : E d × ℝ × ℝ → E d} {U : Set (E d × ℝ)} {w : E d × ℝ → ℝ}
    (hF : AnalyticOnNhd ℝ F univ) (hU : IsOpen U) (hw : AnalyticOnNhd ℝ w U)
    {x₀ : E d} (hbase : (x₀, (0 : ℝ)) ∈ U) {u₀x : ℝ}
    (hw0 : w (x₀, 0) = u₀x) {aV : NNReal} (haV : 0 < aV) :
    ∃ ε > (0 : ℝ), ∃ r : NNReal, 0 < r ∧
      ∃ β : (ℝ × E d) → ℝ → ℝ × E d,
      ∀ z ∈ Metric.closedBall ((0 : ℝ), x₀) r,
        β z 0 = z ∧
        (∀ t ∈ Set.Icc (-ε) ε,
          HasDerivWithinAt (β z)
            (augmentedField (spatialField F w) (β z t)) (Set.Icc (-ε) ε) t) ∧
        ∀ t,
          ((β z t).2, (β z t).1) ∈ U ∧
          graphMap w (β z t) ∈ Metric.closedBall ((0 : ℝ), (x₀, u₀x)) aV := by
  let z₀ : ℝ × E d := (0, x₀)
  let Z₀ : ℝ × (E d × ℝ) := (0, (x₀, u₀x))
  have hspaceAt : AnalyticAt ℝ (spatialField F w) z₀ :=
    analyticAt_spatialField hF hw hbase
  have haugOne : ContDiffAt ℝ 1 (augmentedField (spatialField F w)) z₀ :=
    (analyticAt_const.prod hspaceAt).contDiffAt
  obtain ⟨ε₀, hε₀, a₀, r₀, L, K, hr₀, hplAll⟩ :=
    IsPicardLindelof.of_contDiffAt_one haugOne
  have hzero₀ : (0 : ℝ) ∈ Set.Icc (0 - ε₀) (0 + ε₀) := by constructor <;> linarith
  have hpl₀ := hplAll 0
  have hLpos : (0 : ℝ) < L := by
    have hnorm := hpl₀.norm_le 0 hzero₀ z₀
      (Metric.mem_closedBall_self (show (0 : ℝ) ≤ a₀ by positivity))
    have hone : (1 : ℝ) ≤ ‖augmentedField (spatialField F w) z₀‖ := by
      simp [augmentedField, Prod.norm_def]
    linarith
  have hmaxpos : 0 < max ((0 + ε₀) - (0 : ℝ)) ((0 : ℝ) - (0 - ε₀)) := by
    simpa using hε₀
  have ha₀ : (0 : ℝ) < a₀ := by
    have hbound : (L : ℝ) * max ((0 + ε₀) - (0 : ℝ)) ((0 : ℝ) - (0 - ε₀)) ≤
        (a₀ : ℝ) - (r₀ : ℝ) := by simpa using hpl₀.mul_max_le
    have hsub := (mul_pos hLpos hmaxpos).trans_le hbound
    exact lt_of_lt_of_le (by exact_mod_cast hr₀) (sub_pos.mp hsub).le
  have hgraphBase : graphMap w z₀ = Z₀ := by simp [graphMap, z₀, Z₀, hw0]
  have hgoodNhd : {z : ℝ × E d |
      (z.2, z.1) ∈ U ∧ graphMap w z ∈ Metric.ball Z₀ (aV : ℝ)} ∈ 𝓝 z₀ := by
    have hphysical : ContinuousAt (fun z : ℝ × E d => (z.2, z.1)) z₀ := by fun_prop
    have hUmem : (fun z : ℝ × E d => (z.2, z.1)) ⁻¹' U ∈ 𝓝 z₀ :=
      hphysical (hU.mem_nhds hbase)
    have hgraphMem : graphMap w ⁻¹' Metric.ball Z₀ (aV : ℝ) ∈ 𝓝 z₀ :=
      (analyticAt_graphMap hw hbase).continuousAt (by
        simpa [hgraphBase] using Metric.ball_mem_nhds Z₀ (by exact_mod_cast haV))
    exact Filter.inter_mem hUmem hgraphMem
  obtain ⟨η, hη, hηgood⟩ := Metric.mem_nhds_iff.mp hgoodNhd
  let a' : NNReal := ⟨min (a₀ : ℝ) η / 2, by positivity⟩
  have ha' : 0 < a' := by
    change 0 < min (a₀ : ℝ) η / 2
    positivity
  have ha'a₀ : a' ≤ a₀ := by
    change min (a₀ : ℝ) η / 2 ≤ (a₀ : ℝ)
    exact (half_le_self (by positivity)).trans (min_le_left _ _)
  have ha'η : (a' : ℝ) < η := by
    change min (a₀ : ℝ) η / 2 < η
    exact (half_lt_self (by positivity)).trans_le (min_le_right _ _)
  let r' : NNReal := a' / 2
  have hr' : 0 < r' := by positivity
  have hr'a' : r' < a' := by
    exact half_lt_self ha'
  obtain ⟨ε, hε, hpl⟩ := hpl₀.exists_shrink_radius hε₀ ha'a₀ hr'a'
  obtain ⟨β, hβ⟩ := Submission.Helpers.IsPicardLindelof.exists_flow_with_mem hpl
  refine ⟨ε, hε, r', hr', β, ?_⟩
  intro z hz
  have hzdata := hβ z hz
  refine ⟨?_, ?_, ?_⟩
  · simpa using hzdata.1
  · intro t ht
    simpa only [zero_sub, zero_add] using hzdata.2.1 t
      (by simpa only [zero_sub, zero_add] using ht)
  · intro t
    have hball : β z t ∈ Metric.ball z₀ η := by
      apply Metric.mem_ball.mpr
      exact (Metric.mem_closedBall.mp (hzdata.2.2 t)).trans_lt ha'η
    exact ⟨(hηgood hball).1, Metric.mem_closedBall.mpr (Metric.mem_ball.mp (hηgood hball).2).le⟩

theorem time_mul_mem_ball {x x₀ : E d} {t r s : ℝ}
    (hq : (x, t) ∈ Metric.ball (x₀, (0 : ℝ)) r) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (x, t * s) ∈ Metric.ball (x₀, (0 : ℝ)) r := by
  rw [Metric.mem_ball, Prod.dist_eq] at hq ⊢
  apply (max_le_max_left (dist x x₀) ?_).trans_lt hq
  rw [Real.dist_eq, Real.dist_eq, sub_zero, sub_zero, abs_mul]
  have hsAbs : |s| ≤ (1 : ℝ) := by rw [abs_of_nonneg hs.1]; exact hs.2
  calc
    |t| * |s| ≤ |t| * 1 := mul_le_mul_of_nonneg_left hsAbs (abs_nonneg t)
    _ = |t| := mul_one _

theorem analytic_solution_unique
    (F : E d × ℝ × ℝ → E d) (f : E d × ℝ × ℝ → ℝ) (u₀ : E d → ℝ)
    (hF : AnalyticOnNhd ℝ F univ) (hf : AnalyticOnNhd ℝ f univ)
    (hu₀ : AnalyticOnNhd ℝ u₀ univ)
    {U : Set (E d × ℝ)} (hUOpen : IsOpen U) (hUPre : IsPreconnected U)
    {x₀ : E d} (hbase : (x₀, (0 : ℝ)) ∈ U)
    {u v : E d × ℝ → ℝ} (hu : AnalyticOnNhd ℝ u U) (hv : AnalyticOnNhd ℝ v U)
    (huInit : ∀ x : E d, (x, (0 : ℝ)) ∈ U → u (x, 0) = u₀ x)
    (hvInit : ∀ x : E d, (x, (0 : ℝ)) ∈ U → v (x, 0) = u₀ x)
    (huPDE : ∀ p ∈ U,
      fderiv ℝ u p ((0 : E d), (1 : ℝ)) =
        fderiv ℝ u p (F (p.1, p.2, u p), (0 : ℝ)) + f (p.1, p.2, u p))
    (hvPDE : ∀ p ∈ U,
      fderiv ℝ v p ((0 : E d), (1 : ℝ)) =
        fderiv ℝ v p (F (p.1, p.2, v p), (0 : ℝ)) + f (p.1, p.2, v p)) :
    Set.EqOn u v U := by
  let V := characteristicField F f
  have hV : AnalyticOnNhd ℝ V univ := analyticOnNhd_characteristicField hF hf
  let y₀ := initialState u₀ x₀
  let q₀ : E d × ℝ := (x₀, 0)
  let Z₀ : ℝ × (E d × ℝ) := (0, y₀)
  obtain ⟨δ, hδ, φ, hφ, hφInit, hφDeriv⟩ :=
    exists_analytic_localFlow V hV y₀
  let c := F (x₀, 0, u₀ x₀)
  let chart := characteristicChart φ u₀ c
  let S := timeShearHomeomorph c
  have hflowBase : flowInput u₀ q₀ ∈ Metric.ball (y₀, (0 : ℝ)) δ := by
    simpa [q₀, y₀, flowInput, initialState] using
      (Metric.mem_ball_self hδ : (y₀, (0 : ℝ)) ∈ Metric.ball (y₀, (0 : ℝ)) δ)
  have hchartAt : AnalyticAt ℝ chart q₀ :=
    analyticAt_characteristicChart hu₀ hφ hflowBase c
  have hchartZero : chart q₀ = q₀ := characteristicChart_apply_zero hφInit hflowBase c
  have hchartDeriv : fderiv ℝ chart q₀ = ContinuousLinearMap.id ℝ (E d × ℝ) :=
    characteristicChart_fderiv_base hu₀ hφ hφInit hφDeriv hδ
  let e : (E d × ℝ) ≃L[ℝ] (E d × ℝ) := ContinuousLinearEquiv.refl ℝ (E d × ℝ)
  have hchartStrict : HasStrictFDerivAt chart (e : (E d × ℝ) →L[ℝ] (E d × ℝ)) q₀ := by
    have h := hchartAt.hasStrictFDerivAt
    rw [hchartDeriv] at h
    simpa [e] using h
  have hmapChart : Filter.map chart (𝓝 q₀) = 𝓝 q₀ := by
    simpa [hchartZero] using hchartStrict.map_nhds_eq_of_equiv
  have hspaceMap : Filter.map (spaceTime φ u₀) (𝓝 q₀) = 𝓝 q₀ := by
    have hfun : spaceTime φ u₀ = S.symm ∘ chart := by
      funext q
      simp [S, chart, characteristicChart]
    rw [hfun, ← Filter.map_map, hmapChart, S.symm.map_nhds_eq]
    simp [S, q₀]
  have hAugOne : ContDiffAt ℝ 1 (augmentedField V) Z₀ :=
    (analyticAt_const.prod (hV (0, y₀) (mem_univ _))).contDiffAt
  obtain ⟨εV, hεV, aV, rV, LV, KV, hrV, hplVAll⟩ :=
    IsPicardLindelof.of_contDiffAt_one hAugOne
  have hzeroV : (0 : ℝ) ∈ Set.Icc (0 - εV) (0 + εV) := by constructor <;> linarith
  have hplV := hplVAll 0
  have hLVpos : (0 : ℝ) < LV := by
    have hnorm := hplV.norm_le 0 hzeroV Z₀
      (Metric.mem_closedBall_self (show (0 : ℝ) ≤ aV by positivity))
    have hone : (1 : ℝ) ≤ ‖augmentedField V Z₀‖ := by
      simp [augmentedField, Prod.norm_def]
    linarith
  have hmaxV : 0 < max ((0 + εV) - (0 : ℝ)) ((0 : ℝ) - (0 - εV)) := by
    simpa using hεV
  have haV : 0 < aV := by
    have hbound : (LV : ℝ) * max ((0 + εV) - (0 : ℝ)) ((0 : ℝ) - (0 - εV)) ≤
        (aV : ℝ) - (rV : ℝ) := by simpa using hplV.mul_max_le
    have hsub := (mul_pos hLVpos hmaxV).trans_le hbound
    exact lt_of_lt_of_le hrV (by exact_mod_cast (sub_pos.mp hsub).le)
  have hu0base : u (x₀, 0) = u₀ x₀ := huInit x₀ hbase
  have hv0base : v (x₀, 0) = u₀ x₀ := hvInit x₀ hbase
  obtain ⟨εu, hεu, ru, hru, βu, hβu⟩ :=
    exists_graph_characteristic_flow hF hUOpen hu hbase hu0base haV
  obtain ⟨εv, hεv, rv, hrv, βv, hβv⟩ :=
    exists_graph_characteristic_flow hF hUOpen hv hbase hv0base haV
  have hstateAt : AnalyticAt ℝ (fun q => (q.2, characteristic φ u₀ q)) q₀ := by
    have hchar := (hφ _ hflowBase).comp (analyticAt_flowInput hu₀ q₀)
    have ht := (ContinuousLinearMap.snd ℝ (E d) ℝ).analyticAt q₀
    exact ht.prod hchar
  have hstateZero : (q₀.2, characteristic φ u₀ q₀) = Z₀ := by
    have hinit := hφInit y₀ (by simpa [flowInput, q₀, y₀, initialState] using hflowBase)
    simp [q₀, Z₀, y₀, characteristic, flowInput, hinit]
  have hgoodNhd : {q : E d × ℝ |
      flowInput u₀ q ∈ Metric.ball (y₀, (0 : ℝ)) δ ∧
      (q.2, characteristic φ u₀ q) ∈ Metric.ball Z₀ (aV : ℝ)} ∈ 𝓝 q₀ := by
    have hflowNhd := (analyticAt_flowInput hu₀ q₀).continuousAt
      (by simpa [flowInput, q₀, y₀, initialState] using
        (Metric.ball_mem_nhds (y₀, (0 : ℝ)) hδ))
    have hstateNhd := hstateAt.continuousAt (by
      simpa [hstateZero] using Metric.ball_mem_nhds Z₀ (by exact_mod_cast haV))
    exact Filter.inter_mem hflowNhd hstateNhd
  obtain ⟨η, hη, hηgood⟩ := Metric.mem_nhds_iff.mp hgoodNhd
  let m : ℝ := min η (min (ru : ℝ) (min (rv : ℝ) (min εu εv)))
  have hm : 0 < m := by simp [m, hη, hru, hrv, hεu, hεv]
  let θ := m / 2
  have hθ : 0 < θ := by simp [θ, hm]
  have hθη : θ < η := (half_lt_self hm).trans_le (min_le_left _ _)
  have hθru : θ < (ru : ℝ) := by
    exact (half_lt_self hm).trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hθrv : θ < (rv : ℝ) := by
    exact (half_lt_self hm).trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hθεu : θ < εu := by
    exact (half_lt_self hm).trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _))))
  have hθεv : θ < εv := by
    exact (half_lt_self hm).trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _))))
  have hinitialMem {q : E d × ℝ} (hq : q ∈ Metric.ball q₀ θ) {r : NNReal}
      (hθr : θ < (r : ℝ)) : ((0 : ℝ), q.1) ∈ Metric.closedBall ((0 : ℝ), x₀) r := by
    rw [Metric.mem_closedBall, Prod.dist_eq]
    have hqx : dist q.1 x₀ ≤ dist q q₀ := by
      change dist q.1 x₀ ≤ max (dist q.1 x₀) (dist q.2 (0 : ℝ))
      exact le_max_left _ _
    exact max_le (by simp) ((hqx.trans_lt (Metric.mem_ball.mp hq) |>.trans hθr).le)
  have htimeMem {q : E d × ℝ} (hq : q ∈ Metric.ball q₀ θ) {ε : ℝ}
      (hθε : θ < ε) : q.2 ∈ Set.Icc (-ε) ε := by
    have hqt : dist q.2 (0 : ℝ) ≤ dist q q₀ := by
      change dist q.2 (0 : ℝ) ≤ max (dist q.1 x₀) (dist q.2 (0 : ℝ))
      exact le_max_right _ _
    have habs : |q.2| < ε := by
      have : |q.2| ≤ dist q q₀ := by simpa [Real.dist_eq] using hqt
      exact (this.trans_lt (Metric.mem_ball.mp hq)).trans hθε
    exact ⟨by linarith [abs_lt.mp habs |>.1], by linarith [abs_lt.mp habs |>.2]⟩
  have hcompare
      (w : E d × ℝ → ℝ) (hw : AnalyticOnNhd ℝ w U)
      (hwInit : ∀ x : E d, (x, (0 : ℝ)) ∈ U → w (x, 0) = u₀ x)
      (hwPDE : ∀ p ∈ U,
        fderiv ℝ w p ((0 : E d), (1 : ℝ)) =
          fderiv ℝ w p (F (p.1, p.2, w p), (0 : ℝ)) + f (p.1, p.2, w p))
      (ε : ℝ) (r : NNReal) (β : (ℝ × E d) → ℝ → ℝ × E d)
      (hβ : ∀ z ∈ Metric.closedBall ((0 : ℝ), x₀) r,
        β z 0 = z ∧
        (∀ t ∈ Set.Icc (-ε) ε,
          HasDerivWithinAt (β z)
            (augmentedField (spatialField F w) (β z t)) (Set.Icc (-ε) ε) t) ∧
        ∀ t, ((β z t).2, (β z t).1) ∈ U ∧
          graphMap w (β z t) ∈ Metric.closedBall Z₀ aV)
      (hθr : θ < (r : ℝ)) (hθε : θ < ε)
      {q : E d × ℝ} (hq : q ∈ Metric.ball q₀ θ) :
      graphMap w (β (0, q.1) q.2) = (q.2, characteristic φ u₀ q) := by
    let z : ℝ × E d := (0, q.1)
    have hz : z ∈ Metric.closedBall ((0 : ℝ), x₀) r := hinitialMem hq hθr
    have ht : q.2 ∈ Set.Icc (-ε) ε := htimeMem hq hθε
    have hzero : (0 : ℝ) ∈ Set.Icc (-ε) ε := by
      have := ht
      constructor <;> linarith [this.1, this.2]
    let γw : ℝ → ℝ × (E d × ℝ) := fun s => graphMap w (β z (q.2 * s))
    let γφ : ℝ → ℝ × (E d × ℝ) := fun s =>
      (q.2 * s, characteristic φ u₀ (q.1, q.2 * s))
    have hγwDer : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt γw
          (q.2 • augmentedField V (γw s)) (Set.Icc (0 : ℝ) 1) s := by
      intro s hs
      have hβres := hasDerivWithinAt_rescaled_picard hzero (hβ z hz).2.1 ht hs
      exact hasDerivWithinAt_graphCurve hw hwPDE hβres ((hβ z hz).2.2 (q.2 * s)).1
    have hγφDer : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt γφ
          (q.2 • augmentedField V (γφ s)) (Set.Icc (0 : ℝ) 1) s := by
      intro s hs
      have hqs : (q.1, q.2 * s) ∈ Metric.ball q₀ θ := time_mul_mem_ball hq hs
      have hgood := hηgood (Metric.mem_ball.mpr ((Metric.mem_ball.mp hqs).trans hθη))
      have hflow := hφDeriv (flowInput u₀ (q.1, q.2 * s)) hgood.1
      have hstate : HasDerivAt
          (fun t => (t, φ (initialState u₀ q.1, t)))
          (augmentedField V (q.2 * s, characteristic φ u₀ (q.1, q.2 * s))) (q.2 * s) := by
        simpa [augmentedField, characteristic, flowInput] using
          (hasDerivAt_id (𝕜 := ℝ) (q.2 * s)).prodMk hflow
      have hmul : HasDerivWithinAt (fun a : ℝ => q.2 * a) q.2 (Set.Icc (0 : ℝ) 1) s :=
        (hasDerivAt_const_mul q.2).hasDerivWithinAt
      have hcomp := hstate.scomp_hasDerivWithinAt_of_eq s hmul rfl
      change HasDerivWithinAt
        (fun a => (q.2 * a, characteristic φ u₀ (q.1, q.2 * a)))
        (q.2 • augmentedField V (q.2 * s, characteristic φ u₀ (q.1, q.2 * s)))
        (Set.Icc (0 : ℝ) 1) s at hcomp
      simpa [γφ] using hcomp
    have hLip : ∀ s ∈ Set.Ico (0 : ℝ) 1,
        LipschitzOnWith (‖q.2‖₊ * KV) (fun z => q.2 • augmentedField V z)
          (Metric.closedBall Z₀ aV) := by
      intro _ _
      simpa [Function.comp_def] using
        (lipschitzWith_smul q.2).comp_lipschitzOnWith (hplV.lipschitzOnWith 0 hzeroV)
    have hright (s : ℝ) (hs : s ∈ Set.Ico (0 : ℝ) 1) :
        Set.Icc (0 : ℝ) 1 ∈ 𝓝[Set.Ici s] s := by
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      refine ⟨Set.Iio 1, Iio_mem_nhds hs.2, ?_⟩
      rintro t ⟨ht1, ht2⟩
      exact ⟨hs.1.trans ht2, ht1.le⟩
    have hγwMem : ∀ s ∈ Set.Ico (0 : ℝ) 1, γw s ∈ Metric.closedBall Z₀ aV := by
      intro s _
      exact (hβ z hz).2.2 (q.2 * s) |>.2
    have hγφMem : ∀ s ∈ Set.Ico (0 : ℝ) 1, γφ s ∈ Metric.closedBall Z₀ aV := by
      intro s hs
      have hqs : (q.1, q.2 * s) ∈ Metric.ball q₀ θ :=
        time_mul_mem_ball hq (Set.Ico_subset_Icc_self hs)
      exact Metric.mem_closedBall.mpr
        (Metric.mem_ball.mp (hηgood
          (Metric.mem_ball.mpr ((Metric.mem_ball.mp hqs).trans hθη))).2).le
    have hγw0 : γw 0 = (0, initialState u₀ q.1) := by
      have hb0 := (hβ z hz).1
      have hmem := (hβ z hz).2.2 0 |>.1
      have hw0 := hwInit q.1 (by simpa [z, hb0] using hmem)
      simp [γw, z, hb0, graphMap, initialState, hw0]
    have hγφ0 : γφ 0 = (0, initialState u₀ q.1) := by
      have hqs : (q.1, (0 : ℝ)) ∈ Metric.ball q₀ θ :=
        by simpa [q₀] using time_mul_mem_ball (s := 0) hq (by norm_num)
      have hgood := hηgood (Metric.mem_ball.mpr ((Metric.mem_ball.mp hqs).trans hθη))
      have hinit := hφInit (initialState u₀ q.1) (by
        simpa [flowInput] using hgood.1)
      simp [γφ, characteristic, flowInput, hinit]
    have hcurves : Set.EqOn γw γφ (Set.Icc (0 : ℝ) 1) :=
      ODE_solution_unique_of_mem_Icc_right
        (a := 0) (b := 1)
        (v := fun _ z => q.2 • augmentedField V z)
        (s := fun _ => Metric.closedBall Z₀ aV) hLip
        (HasDerivWithinAt.continuousOn hγwDer)
        (fun s hs => (hγwDer s (Set.Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
          (hright s hs))
        hγwMem
        (HasDerivWithinAt.continuousOn hγφDer)
        (fun s hs => (hγφDer s (Set.Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
          (hright s hs))
        hγφMem
        (hγw0.trans hγφ0.symm)
    have hone : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
    simpa [γw, γφ, z] using hcurves (x := 1) hone
  have hvalueAtSpace
      (w : E d × ℝ → ℝ) (ε : ℝ) (r : NNReal)
      (β : (ℝ × E d) → ℝ → ℝ × E d)
      (hβ : ∀ z ∈ Metric.closedBall ((0 : ℝ), x₀) r,
        β z 0 = z ∧
        (∀ t ∈ Set.Icc (-ε) ε,
          HasDerivWithinAt (β z)
            (augmentedField (spatialField F w) (β z t)) (Set.Icc (-ε) ε) t) ∧
        ∀ t, ((β z t).2, (β z t).1) ∈ U ∧
          graphMap w (β z t) ∈ Metric.closedBall Z₀ aV)
      (hθr : θ < (r : ℝ)) (hθε : θ < ε)
      (hw : AnalyticOnNhd ℝ w U)
      (hwInit : ∀ x : E d, (x, (0 : ℝ)) ∈ U → w (x, 0) = u₀ x)
      (hwPDE : ∀ p ∈ U,
        fderiv ℝ w p ((0 : E d), (1 : ℝ)) =
          fderiv ℝ w p (F (p.1, p.2, w p), (0 : ℝ)) + f (p.1, p.2, w p))
      {q : E d × ℝ} (hq : q ∈ Metric.ball q₀ θ) :
      w (spaceTime φ u₀ q) = (characteristic φ u₀ q).2 := by
    have hc := hcompare w hw hwInit hwPDE ε r β hβ hθr hθε hq
    have hphysical := congrArg (fun z : ℝ × (E d × ℝ) => (z.2.1, z.1)) hc
    have hvalue := congrArg (fun z : ℝ × (E d × ℝ) => z.2.2) hc
    change ((β (0, q.1) q.2).2, (β (0, q.1) q.2).1) = spaceTime φ u₀ q at hphysical
    change w ((β (0, q.1) q.2).2, (β (0, q.1) q.2).1) =
      (characteristic φ u₀ q).2 at hvalue
    rw [hphysical] at hvalue
    exact hvalue
  have hparamEq : ∀ᶠ q in 𝓝 q₀,
      u (spaceTime φ u₀ q) = v (spaceTime φ u₀ q) := by
    filter_upwards [Metric.ball_mem_nhds q₀ hθ] with q hq
    rw [hvalueAtSpace u εu ru βu hβu hθru hθεu hu huInit huPDE hq,
      hvalueAtSpace v εv rv βv hβv hθrv hθεv hv hvInit hvPDE hq]
  have huv : u =ᶠ[𝓝 q₀] v := by
    have hset : {p | u p = v p} ∈ Filter.map (spaceTime φ u₀) (𝓝 q₀) := hparamEq
    rw [hspaceMap] at hset
    exact hset
  exact hu.eqOn_of_preconnected_of_eventuallyEq hv hUPre hbase huv

end Submission.CK
