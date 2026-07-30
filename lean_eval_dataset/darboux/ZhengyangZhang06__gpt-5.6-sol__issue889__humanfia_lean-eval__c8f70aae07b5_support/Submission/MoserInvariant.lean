import Submission.PullbackInvariant

open Set Function Matrix Metric Filter
open scoped ContDiff NNReal Topology

namespace Submission.MoserInvariant

noncomputable section

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem tangentSolution_fst_eq
    (f : ℝ → V → V)
    (K : ℝ≥0) (hlip : ∀ t, LipschitzWith K (f t))
    {tmin tmax : ℝ} (htime : tmin ≤ tmax)
    {xcenter : V} {a r L Kbase : ℝ≥0}
    (hpl : IsPicardLindelof f
      (⟨tmin, ⟨le_rfl, htime⟩⟩ : Icc tmin tmax) xcenter a r L Kbase)
    {aT LT KT : ℝ≥0}
    (hplT : IsPicardLindelof (Submission.MoserFlow.tangentField f)
      (⟨tmin, ⟨le_rfl, htime⟩⟩ : Icc tmin tmax)
      (xcenter, ContinuousLinearMap.id ℝ V) aT r LT KT)
    {x : V} (hx : x ∈ closedBall xcenter r) (t : Icc tmin tmax) :
    (Submission.MoserFlow.solutionAt hplT t
      (x, ContinuousLinearMap.id ℝ V)).1 =
        Submission.MoserFlow.solutionAt hpl t x := by
  let basePath : ℝ → V := fun s => Submission.MoserFlow.solutionAt hpl
    (projIcc tmin tmax htime s) x
  let tangentPath : ℝ → V := fun s =>
    (Submission.MoserFlow.solutionAt hplT (projIcc tmin tmax htime s)
      (x, ContinuousLinearMap.id ℝ V)).1
  have hxT : (x, ContinuousLinearMap.id ℝ V) ∈
      closedBall (xcenter, ContinuousLinearMap.id ℝ V) r :=
    Submission.MoserFlow.tangentInitial_mem_closedBall hx
  have hbaseCont : ContinuousOn basePath (Icc tmin tmax) := by
    have heq : basePath =
        (Submission.MoserFlow.solutionCurve hpl hx).compProj := by
      funext s
      dsimp [basePath]
      rw [Submission.MoserFlow.solutionAt_of_mem hpl _ hx]
    rw [heq]
    exact (Submission.MoserFlow.solutionCurve hpl hx).continuous_compProj.continuousOn
  have htangentCont : ContinuousOn tangentPath (Icc tmin tmax) := by
    have heq : tangentPath = fun s =>
        ((Submission.MoserFlow.solutionCurve hplT hxT).compProj s).1 := by
      funext s
      dsimp [tangentPath]
      rw [Submission.MoserFlow.solutionAt_of_mem hplT _ hxT]
    rw [heq]
    exact (continuous_fst.comp
      (Submission.MoserFlow.solutionCurve hplT hxT).continuous_compProj).continuousOn
  have hbaseDeriv : ∀ s ∈ Ico tmin tmax,
      HasDerivWithinAt basePath (f s (basePath s)) (Ici s) s := by
    intro s hs
    have hsIcc : s ∈ Icc tmin tmax := Ico_subset_Icc_self hs
    have hd := Submission.MoserFlow.solutionAt_hasDerivWithinAt_time
      hpl hx ⟨s, hsIcc⟩
    have hd' := hd.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hs)
    simpa only [basePath, projIcc_of_mem htime hsIcc] using hd'
  have htangentDeriv : ∀ s ∈ Ico tmin tmax,
      HasDerivWithinAt tangentPath (f s (tangentPath s)) (Ici s) s := by
    intro s hs
    have hsIcc : s ∈ Icc tmin tmax := Ico_subset_Icc_self hs
    have hd := Submission.MoserFlow.solutionAt_hasDerivWithinAt_time
      hplT hxT ⟨s, hsIcc⟩
    have hdfst := hd.hasFDerivWithinAt.fst.hasDerivWithinAt
    have hd' := hdfst.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hs)
    simpa [tangentPath, projIcc_of_mem htime hsIcc,
      Submission.MoserFlow.tangentField] using hd'
  have hstart : tangentPath tmin = basePath tmin := by
    have htmin : tmin ∈ Icc tmin tmax := ⟨le_rfl, htime⟩
    dsimp [tangentPath, basePath]
    rw [projIcc_of_mem htime htmin,
      Submission.MoserFlow.solutionAt_initial hplT hxT,
      Submission.MoserFlow.solutionAt_initial hpl hx]
  have heq := ODE_solution_unique hlip htangentCont htangentDeriv
    hbaseCont hbaseDeriv hstart
  have ht := heq t.2
  simpa only [tangentPath, basePath, projIcc_of_mem htime t.2] using ht

theorem solutionFDerivAt_hasDerivWithinAt_time
    (f : ℝ → V → V)
    (K : ℝ≥0) (hlip : ∀ t, LipschitzWith K (f t))
    {tmin tmax : ℝ} (htime : tmin ≤ tmax)
    {xcenter : V} {a r L Kbase : ℝ≥0}
    (hpl : IsPicardLindelof f
      (⟨tmin, ⟨le_rfl, htime⟩⟩ : Icc tmin tmax) xcenter a r L Kbase)
    {aT LT KT : ℝ≥0}
    (hplT : IsPicardLindelof (Submission.MoserFlow.tangentField f)
      (⟨tmin, ⟨le_rfl, htime⟩⟩ : Icc tmin tmax)
      (xcenter, ContinuousLinearMap.id ℝ V) aT r LT KT)
    {x : V} (hx : x ∈ closedBall xcenter r) (t : Icc tmin tmax) :
    HasDerivWithinAt
      (fun s : ℝ => Submission.MoserFlow.solutionFDerivAt hplT
        (projIcc tmin tmax htime s) x)
      ((Submission.MoserFlow.spaceFDeriv f
        (t, Submission.MoserFlow.solutionAt hpl t x)).comp
          (Submission.MoserFlow.solutionFDerivAt hplT t x))
      (Icc tmin tmax) t := by
  have hxT : (x, ContinuousLinearMap.id ℝ V) ∈
      closedBall (xcenter, ContinuousLinearMap.id ℝ V) r :=
    Submission.MoserFlow.tangentInitial_mem_closedBall hx
  have hd := Submission.MoserFlow.solutionAt_hasDerivWithinAt_time hplT hxT t
  have hdsnd := hd.hasFDerivWithinAt.snd.hasDerivWithinAt
  have hfst := tangentSolution_fst_eq f K hlip htime hpl hplT hx t
  simpa [Submission.MoserFlow.solutionFDerivAt,
    Submission.MoserFlow.tangentField, hfst] using hdsnd

theorem pullbackValue_hasDerivWithinAt_zero
    (ω₀ : V [⋀^Fin 2]→L[ℝ] ℝ)
    (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (hδ : ContDiff ℝ ∞ δ)
    (f : ℝ → V → V)
    (K : ℝ≥0) (hlip : ∀ t, LipschitzWith K (f t))
    {tmin tmax : ℝ} (htime : tmin ≤ tmax)
    {xcenter : V} {a r L Kbase : ℝ≥0}
    (hpl : IsPicardLindelof f
      (⟨tmin, ⟨le_rfl, htime⟩⟩ : Icc tmin tmax) xcenter a r L Kbase)
    {aT LT KT : ℝ≥0}
    (hplT : IsPicardLindelof (Submission.MoserFlow.tangentField f)
      (⟨tmin, ⟨le_rfl, htime⟩⟩ : Icc tmin tmax)
      (xcenter, ContinuousLinearMap.id ℝ V) aT r LT KT)
    {x : V} (hx : x ∈ closedBall xcenter r)
    (hcoord : ∀ t : Icc tmin tmax, ∀ u v : V,
      δ (Submission.MoserFlow.solutionAt hpl t x) ![u, v] +
          (t : ℝ) * fderiv ℝ δ (Submission.MoserFlow.solutionAt hpl t x)
            (f t (Submission.MoserFlow.solutionAt hpl t x)) ![u, v] +
          Submission.MoserField.formPath ω₀ δ
            (t, Submission.MoserFlow.solutionAt hpl t x)
              ![Submission.MoserFlow.spaceFDeriv f
                (t, Submission.MoserFlow.solutionAt hpl t x) u, v] +
          Submission.MoserField.formPath ω₀ δ
            (t, Submission.MoserFlow.solutionAt hpl t x)
              ![u, Submission.MoserFlow.spaceFDeriv f
                (t, Submission.MoserFlow.solutionAt hpl t x) v] = 0)
    (u v : V) (t : Icc tmin tmax) :
    HasDerivWithinAt
      (fun s : ℝ =>
        let q := Submission.MoserFlow.solutionAt hpl
          (projIcc tmin tmax htime s) x
        let A := Submission.MoserFlow.solutionFDerivAt hplT
          (projIcc tmin tmax htime s) x
        Submission.MoserField.formPath ω₀ δ (s, q) ![A u, A v])
      0 (Icc tmin tmax) t := by
  let qPath : ℝ → V := fun s => Submission.MoserFlow.solutionAt hpl
    (projIcc tmin tmax htime s) x
  let APath : ℝ → (V →L[ℝ] V) := fun s =>
    Submission.MoserFlow.solutionFDerivAt hplT
      (projIcc tmin tmax htime s) x
  let formCurve : ℝ → V [⋀^Fin 2]→L[ℝ] ℝ := fun s =>
    Submission.MoserField.formPath ω₀ δ (s, qPath s)
  let args : Fin 2 → ℝ → V := fun i s => ![APath s u, APath s v] i
  have hq : HasDerivWithinAt qPath (f t (qPath t)) (Icc tmin tmax) t := by
    have hraw := Submission.MoserFlow.solutionAt_hasDerivWithinAt_time hpl hx t
    simpa [qPath, projIcc_of_mem htime t.2] using hraw
  have hδq : HasDerivWithinAt (fun s => δ (qPath s))
      (fderiv ℝ δ (qPath t) (f t (qPath t))) (Icc tmin tmax) t := by
    exact ((hδ.differentiable (by simp) (qPath t)).hasFDerivAt.comp_hasDerivWithinAt
      (t : ℝ) hq)
  have hform : HasDerivWithinAt formCurve
      (δ (qPath t) + (t : ℝ) • fderiv ℝ δ (qPath t) (f t (qPath t)))
      (Icc tmin tmax) t := by
    have htimeDeriv : HasDerivWithinAt (id : ℝ → ℝ) 1
        (Icc tmin tmax) (t : ℝ) :=
      (hasDerivAt_id (t : ℝ)).hasDerivWithinAt
    have hsum := (htimeDeriv.smul hδq).const_add ω₀
    change HasDerivWithinAt (fun s => ω₀ + s • δ (qPath s))
      (δ (qPath t) + (t : ℝ) • fderiv ℝ δ (qPath t) (f t (qPath t)))
      (Icc tmin tmax) t
    exact hsum.congr_deriv (by simp [add_comm])
  have hA : HasDerivWithinAt APath
      ((Submission.MoserFlow.spaceFDeriv f (t, qPath t)).comp (APath t))
      (Icc tmin tmax) t := by
    have hraw := solutionFDerivAt_hasDerivWithinAt_time
      f K hlip htime hpl hplT hx t
    simpa [APath, qPath, projIcc_of_mem htime t.2] using hraw
  have hargs : ∀ i, HasDerivWithinAt (args i)
      (((Submission.MoserFlow.spaceFDeriv f (t, qPath t)).comp (APath t))
        (![u, v] i)) (Icc tmin tmax) t := by
    intro i
    fin_cases i
    · have hu := hA.clm_apply
        (hasDerivAt_const (x := (t : ℝ)) u).hasDerivWithinAt
      simpa [args] using hu
    · have hv := hA.clm_apply
        (hasDerivAt_const (x := (t : ℝ)) v).hasDerivWithinAt
      simpa [args] using hv
  have hraw := hform.hasFDerivWithinAt.continuousAlternatingMap_apply
    (fun i => (hargs i).hasFDerivWithinAt) |>.hasDerivWithinAt
  have hupdate0 : Function.update
      (fun i : Fin 2 => ![APath t u, APath t v] i) 0
        (Submission.MoserFlow.spaceFDeriv f (t, qPath t) (APath t u)) =
      ![Submission.MoserFlow.spaceFDeriv f (t, qPath t) (APath t u), APath t v] := by
    funext i
    fin_cases i <;> simp
  have hupdate1 : Function.update
      (fun i : Fin 2 => ![APath t u, APath t v] i) 1
        (Submission.MoserFlow.spaceFDeriv f (t, qPath t) (APath t v)) =
      ![APath t u, Submission.MoserFlow.spaceFDeriv f (t, qPath t) (APath t v)] := by
    funext i
    fin_cases i <;> simp
  have hargsAt : (fun i => args i t) = ![APath t u, APath t v] := by
    funext i
    fin_cases i <;> rfl
  have hz : δ (qPath t) ![APath t u, APath t v] +
        (t : ℝ) * fderiv ℝ δ (qPath t) (f t (qPath t))
          ![APath t u, APath t v] +
        Submission.MoserField.formPath ω₀ δ (t, qPath t)
          ![Submission.MoserFlow.spaceFDeriv f (t, qPath t) (APath t u), APath t v] +
        Submission.MoserField.formPath ω₀ δ (t, qPath t)
          ![APath t u, Submission.MoserFlow.spaceFDeriv f (t, qPath t) (APath t v)] = 0 := by
    simpa [qPath, projIcc_of_mem htime t.2] using
      hcoord t (APath t u) (APath t v)
  have hzero : HasDerivWithinAt
      (fun s => formCurve s (fun i => args i s)) 0
      (Icc tmin tmax) t := by
    apply hraw.congr_deriv
    simp only [Fin.sum_univ_two]
    simp
    rw [hargsAt, hupdate0, hupdate1]
    change
      (δ (qPath t) ![APath t u, APath t v] +
          (t : ℝ) * fderiv ℝ δ (qPath t) (f t (qPath t))
            ![APath t u, APath t v]) +
        (Submission.MoserField.formPath ω₀ δ (t, qPath t)
            ![Submission.MoserFlow.spaceFDeriv f (t, qPath t) (APath t u), APath t v] +
          Submission.MoserField.formPath ω₀ δ (t, qPath t)
            ![APath t u, Submission.MoserFlow.spaceFDeriv f (t, qPath t) (APath t v)]) = 0
    simpa [add_assoc] using hz
  simpa [formCurve, args, qPath, APath] using hzero

theorem solutionAt_pullback_eq
    (ω₀ : V [⋀^Fin 2]→L[ℝ] ℝ)
    (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (hδ : ContDiff ℝ ∞ δ)
    (f : ℝ → V → V)
    (K : ℝ≥0) (hlip : ∀ t, LipschitzWith K (f t))
    {tmin tmax : ℝ} (htime : tmin ≤ tmax)
    {xcenter : V} {a r L Kbase : ℝ≥0}
    (hpl : IsPicardLindelof f
      (⟨tmin, ⟨le_rfl, htime⟩⟩ : Icc tmin tmax) xcenter a r L Kbase)
    {aT LT KT : ℝ≥0}
    (hplT : IsPicardLindelof (Submission.MoserFlow.tangentField f)
      (⟨tmin, ⟨le_rfl, htime⟩⟩ : Icc tmin tmax)
      (xcenter, ContinuousLinearMap.id ℝ V) aT r LT KT)
    {x : V} (hx : x ∈ ball xcenter r)
    (hcoord : ∀ t : Icc tmin tmax, ∀ u v : V,
      δ (Submission.MoserFlow.solutionAt hpl t x) ![u, v] +
          (t : ℝ) * fderiv ℝ δ (Submission.MoserFlow.solutionAt hpl t x)
            (f t (Submission.MoserFlow.solutionAt hpl t x)) ![u, v] +
          Submission.MoserField.formPath ω₀ δ
            (t, Submission.MoserFlow.solutionAt hpl t x)
              ![Submission.MoserFlow.spaceFDeriv f
                (t, Submission.MoserFlow.solutionAt hpl t x) u, v] +
          Submission.MoserField.formPath ω₀ δ
            (t, Submission.MoserFlow.solutionAt hpl t x)
              ![u, Submission.MoserFlow.spaceFDeriv f
                (t, Submission.MoserFlow.solutionAt hpl t x) v] = 0)
    (u v : V) :
    Submission.MoserField.formPath ω₀ δ
        (tmax, Submission.MoserFlow.solutionAt hpl
          (⟨tmax, ⟨htime, le_rfl⟩⟩ : Icc tmin tmax) x)
      ![Submission.MoserFlow.solutionFDerivAt hplT
          (⟨tmax, ⟨htime, le_rfl⟩⟩ : Icc tmin tmax) x u,
        Submission.MoserFlow.solutionFDerivAt hplT
          (⟨tmax, ⟨htime, le_rfl⟩⟩ : Icc tmin tmax) x v] =
      Submission.MoserField.formPath ω₀ δ (tmin, x) ![u, v] := by
  let value : ℝ → ℝ := fun s =>
    let q := Submission.MoserFlow.solutionAt hpl
      (projIcc tmin tmax htime s) x
    let A := Submission.MoserFlow.solutionFDerivAt hplT
      (projIcc tmin tmax htime s) x
    Submission.MoserField.formPath ω₀ δ (s, q) ![A u, A v]
  have hxClosed : x ∈ closedBall xcenter r := ball_subset_closedBall hx
  have hxT : (x, ContinuousLinearMap.id ℝ V) ∈
      closedBall (xcenter, ContinuousLinearMap.id ℝ V) r :=
    Submission.MoserFlow.tangentInitial_mem_closedBall hxClosed
  have hAstart : Submission.MoserFlow.solutionFDerivAt hplT
      (⟨tmin, ⟨le_rfl, htime⟩⟩ : Icc tmin tmax) x =
        ContinuousLinearMap.id ℝ V := by
    unfold Submission.MoserFlow.solutionFDerivAt
    rw [Submission.MoserFlow.solutionAt_initial hplT hxT]
  by_cases hlt : tmin < tmax
  · have hzero : ∀ t : Icc tmin tmax,
        HasDerivWithinAt value 0 (Icc tmin tmax) t := by
      intro t
      exact pullbackValue_hasDerivWithinAt_zero ω₀ δ hδ f K hlip htime
        hpl hplT hxClosed hcoord u v t
    have hdiff : DifferentiableOn ℝ value (Icc tmin tmax) := by
      intro t ht
      exact (hzero ⟨t, ht⟩).differentiableWithinAt
    have hderiv : ∀ t ∈ Icc tmin tmax,
        fderivWithin ℝ value (Icc tmin tmax) t = 0 := by
      intro t ht
      have hu := (uniqueDiffOn_Icc hlt).uniqueDiffWithinAt ht
      simpa using (hzero ⟨t, ht⟩).hasFDerivWithinAt.fderivWithin hu
    have heq := (convex_Icc tmin tmax).is_const_of_fderivWithin_eq_zero
      hdiff hderiv (show tmax ∈ Icc tmin tmax from ⟨hlt.le, le_rfl⟩)
        (show tmin ∈ Icc tmin tmax from ⟨le_rfl, hlt.le⟩)
    simpa [value, projIcc_of_mem htime, hAstart,
      Submission.MoserFlow.solutionAt_initial hpl hxClosed] using heq
  · have heq : tmax = tmin := le_antisymm (le_of_not_gt hlt) htime
    subst tmax
    simp [Submission.MoserFlow.solutionAt_initial hpl hxClosed, hAstart]

theorem unitTimeOneMap_pullback_eq
    (ω₀ : V [⋀^Fin 2]→L[ℝ] ℝ)
    (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (hδ : ContDiff ℝ ∞ δ)
    (f : ℝ → V → V) (hf : ContDiff ℝ ∞ (uncurry f))
    (L K : ℝ≥0) (hbound : ∀ t z, ‖f t z‖ ≤ L)
    (hlip : ∀ t, LipschitzWith K (f t))
    (x : V)
    (hcoord : ∀ t : Icc (0 : ℝ) 1, ∀ u v : V,
      δ (Submission.MoserGlobal.unitFlow f hf L K hbound hlip t x) ![u, v] +
          (t : ℝ) * fderiv ℝ δ
            (Submission.MoserGlobal.unitFlow f hf L K hbound hlip t x)
            (f t (Submission.MoserGlobal.unitFlow f hf L K hbound hlip t x)) ![u, v] +
          Submission.MoserField.formPath ω₀ δ
            (t, Submission.MoserGlobal.unitFlow f hf L K hbound hlip t x)
              ![Submission.MoserFlow.spaceFDeriv f
                (t, Submission.MoserGlobal.unitFlow f hf L K hbound hlip t x) u, v] +
          Submission.MoserField.formPath ω₀ δ
            (t, Submission.MoserGlobal.unitFlow f hf L K hbound hlip t x)
              ![u, Submission.MoserFlow.spaceFDeriv f
                (t, Submission.MoserGlobal.unitFlow f hf L K hbound hlip t x) v] = 0)
    (u v : V) :
    Submission.MoserField.formPath ω₀ δ
        (1, Submission.MoserSmoothFlow.unitTimeOneMap f hf L K hbound hlip x)
      ![fderiv ℝ (Submission.MoserSmoothFlow.unitTimeOneMap f hf L K hbound hlip) x u,
        fderiv ℝ (Submission.MoserSmoothFlow.unitTimeOneMap f hf L K hbound hlip) x v] =
      Submission.MoserField.formPath ω₀ δ (0, x) ![u, v] := by
  let flow := Submission.MoserGlobal.unitFlow f hf L K hbound hlip
  let data : (p : Icc (0 : ℝ) 1) →
      Submission.MoserFlow.PicardTowerData f p (flow p x) 1 1 := fun p =>
    Submission.MoserFlow.localPicardTowerData f hf p (flow p x) 1 1
  let cover : Icc (0 : ℝ) 1 → Set (Icc (0 : ℝ) 1) := fun p =>
    (fun q : Icc (0 : ℝ) 1 => (q : ℝ) - (p : ℝ)) ⁻¹'
        Ioo (-(data p).ε / 2) ((data p).ε / 2) ∩
      (fun q => flow q x) ⁻¹' ball (flow p x) 1
  have hcoverOpen : ∀ p, IsOpen (cover p) := by
    intro p
    apply IsOpen.inter
    · exact isOpen_Ioo.preimage (continuous_subtype_val.sub continuous_const)
    · exact isOpen_ball.preimage
        (Submission.MoserGlobal.unitFlow_continuous f hf L K hbound hlip x)
  have hcoverAll : univ ⊆ ⋃ p, cover p := by
    intro p _hp
    apply mem_iUnion.mpr
    refine ⟨p, ?_⟩
    constructor
    · change -(data p).ε / 2 < (p : ℝ) - p ∧
        (p : ℝ) - p < (data p).ε / 2
      constructor <;> simp only [sub_self] <;> linarith [(data p).hε]
    · exact mem_ball_self (by norm_num)
  obtain ⟨τ, hτ0, hτmono, ⟨m, hm⟩, hsegments⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hcoverOpen hcoverAll
  choose center hcenter using hsegments
  let step : (k : ℕ) → Submission.MoserFlow.PicardStepData f
      (τ k) (τ (k + 1)) (flow (center k) x) 1 1 := fun k => by
    let d := data (center k)
    have htime : (τ k : ℝ) ≤ τ (k + 1) := hτmono (Nat.le_succ k)
    have hkleft : τ k ∈ Icc (τ k) (τ (k + 1)) := ⟨le_rfl, htime⟩
    have hkright : τ (k + 1) ∈ Icc (τ k) (τ (k + 1)) := ⟨htime, le_rfl⟩
    have hleftRaw := hcenter k hkleft
    change
      (((τ k : ℝ) - center k ∈
          Ioo (-(data (center k)).ε / 2) ((data (center k)).ε / 2)) ∧
        flow (τ k) x ∈ ball (flow (center k) x) 1) at hleftRaw
    have hleft :
        ((τ k : ℝ) - center k ∈ Ioo (-d.ε / 2) (d.ε / 2)) ∧
          flow (τ k) x ∈ ball (flow (center k) x) 1 := by
      simpa only [d] using hleftRaw
    have hrightRaw := hcenter k hkright
    change
      (((τ (k + 1) : ℝ) - center k ∈
          Ioo (-(data (center k)).ε / 2) ((data (center k)).ε / 2)) ∧
        flow (τ (k + 1)) x ∈ ball (flow (center k) x) 1) at hrightRaw
    have hright :
        ((τ (k + 1) : ℝ) - center k ∈ Ioo (-d.ε / 2) (d.ε / 2)) ∧
          flow (τ (k + 1)) x ∈ ball (flow (center k) x) 1 := by
      simpa only [d] using hrightRaw
    have hmin : (center k : ℝ) - d.ε ≤ τ k := by
      linarith [hleft.1.1, d.hε]
    have hmax : (τ (k + 1) : ℝ) ≤ (center k : ℝ) + d.ε := by
      linarith [hright.1.2, d.hε]
    have hlength : (τ (k + 1) : ℝ) - τ k ≤ d.ε := by
      linarith [hleft.1.1, hright.1.2]
    have hspan : max ((τ (k + 1) : ℝ) - τ k) ((τ k : ℝ) - τ k) ≤
        max (((center k : ℝ) + d.ε) - center k)
          ((center k : ℝ) - ((center k : ℝ) - d.ε)) := by
      simpa only [sub_self, max_eq_left (sub_nonneg.mpr htime),
        add_sub_cancel_left, sub_sub_cancel, max_self] using hlength
    exact d.toStep htime hmin hmax hspan
  let maps : ℕ → V → V := fun k => (step k).map
  have hchain : ∀ k : ℕ,
      ContDiffAt ℝ 1 (Submission.MoserSmoothFlow.stepChain maps k) x ∧
      (Submission.MoserSmoothFlow.stepChain maps k =ᶠ[𝓝 x]
        fun y => flow (τ k) y) ∧
      ∀ u v : V,
        Submission.MoserField.formPath ω₀ δ
            (τ k, Submission.MoserSmoothFlow.stepChain maps k x)
          ![fderiv ℝ (Submission.MoserSmoothFlow.stepChain maps k) x u,
            fderiv ℝ (Submission.MoserSmoothFlow.stepChain maps k) x v] =
          Submission.MoserField.formPath ω₀ δ (0, x) ![u, v] := by
    intro k
    induction k with
    | zero =>
        constructor
        · exact contDiffAt_id
        constructor
        · apply Filter.Eventually.of_forall
          intro y
          rw [Submission.MoserSmoothFlow.stepChain_zero, id_eq, hτ0]
          exact (Submission.MoserGlobal.unitFlow_zero_time
            f hf L K hbound hlip y).symm
        · intro u v
          rw [hτ0]
          simp [Submission.MoserSmoothFlow.stepChain_zero]
    | succ k ih =>
        rcases ih with ⟨hreg, heq, hinv⟩
        have hkleft : τ k ∈ Icc (τ k) (τ (k + 1)) :=
          ⟨le_rfl, hτmono (Nat.le_succ k)⟩
        have hxballFlow : flow (τ k) x ∈ ball (flow (center k) x) 1 :=
          (hcenter k hkleft).2
        have hxEq : Submission.MoserSmoothFlow.stepChain maps k x = flow (τ k) x :=
          heq.self_of_nhds
        have hxball : Submission.MoserSmoothFlow.stepChain maps k x ∈
            ball (flow (center k) x) 1 := by
          rw [hxEq]
          exact hxballFlow
        have hstepAt : ContDiffAt ℝ 1 (step k).map
            (Submission.MoserSmoothFlow.stepChain maps k x) :=
          ((step k).map_contDiffOn hf).contDiffAt (isOpen_ball.mem_nhds hxball)
        have hregSucc : ContDiffAt ℝ 1
            (Submission.MoserSmoothFlow.stepChain maps (k + 1)) x := by
          change ContDiffAt ℝ 1
            ((step k).map ∘ Submission.MoserSmoothFlow.stepChain maps k) x
          exact hstepAt.comp x hreg
        have hballEv : ∀ᶠ y in 𝓝 x,
            Submission.MoserSmoothFlow.stepChain maps k y ∈
              ball (flow (center k) x) 1 :=
          hreg.continuousAt (isOpen_ball.mem_nhds hxball)
        have heqSucc : Submission.MoserSmoothFlow.stepChain maps (k + 1) =ᶠ[𝓝 x]
            fun y => flow (τ (k + 1)) y := by
          filter_upwards [heq, hballEv] with y hyEq hyBall
          change (step k).map (Submission.MoserSmoothFlow.stepChain maps k y) =
            flow (τ (k + 1)) y
          rw [hyEq]
          have hyBall' : flow (τ k) y ∈ ball (flow (center k) x) 1 := by
            rwa [← hyEq]
          have hyClosed : flow (τ k) y ∈ closedBall (flow (center k) x) 1 :=
            ball_subset_closedBall hyBall'
          change Submission.MoserFlow.solutionAt (step k).hpl (step k).endTime
              (flow (τ k) y) = flow (τ (k + 1)) y
          simpa only [flow, Submission.MoserFlow.PicardStepData.endTime] using
            Submission.MoserGlobal.solutionAt_eq_unitFlow f hf L K hbound hlip
              (τ k).2.1 (τ (k + 1)).2.2 (step k).htime
              (step k).hpl hyClosed rfl (step k).endTime
        constructor
        · exact hregSucc
        constructor
        · exact heqSucc
        · intro u v
          have htail := (step k).tail
          change ∃ aT LT KT : ℝ≥0,
            IsPicardLindelof (Submission.MoserFlow.tangentField f)
              (⟨(τ k : ℝ), ⟨le_rfl, (step k).htime⟩⟩ :
                Icc (τ k : ℝ) (τ (k + 1) : ℝ))
              (flow (center k) x, ContinuousLinearMap.id ℝ V) aT 1 LT KT ∧ True at htail
          obtain ⟨aT, LT, KT, hplT, _htail⟩ := htail
          have hxClosed : Submission.MoserSmoothFlow.stepChain maps k x ∈
              closedBall (flow (center k) x) 1 := ball_subset_closedBall hxball
          have hcoordLocal : ∀ t : Icc (τ k : ℝ) (τ (k + 1) : ℝ), ∀ a b : V,
              δ (Submission.MoserFlow.solutionAt (step k).hpl t
                  (Submission.MoserSmoothFlow.stepChain maps k x)) ![a, b] +
                (t : ℝ) * fderiv ℝ δ
                  (Submission.MoserFlow.solutionAt (step k).hpl t
                    (Submission.MoserSmoothFlow.stepChain maps k x))
                  (f t (Submission.MoserFlow.solutionAt (step k).hpl t
                    (Submission.MoserSmoothFlow.stepChain maps k x))) ![a, b] +
                Submission.MoserField.formPath ω₀ δ
                  (t, Submission.MoserFlow.solutionAt (step k).hpl t
                    (Submission.MoserSmoothFlow.stepChain maps k x))
                    ![Submission.MoserFlow.spaceFDeriv f
                      (t, Submission.MoserFlow.solutionAt (step k).hpl t
                        (Submission.MoserSmoothFlow.stepChain maps k x)) a, b] +
                Submission.MoserField.formPath ω₀ δ
                  (t, Submission.MoserFlow.solutionAt (step k).hpl t
                    (Submission.MoserSmoothFlow.stepChain maps k x))
                    ![a, Submission.MoserFlow.spaceFDeriv f
                      (t, Submission.MoserFlow.solutionAt (step k).hpl t
                        (Submission.MoserSmoothFlow.stepChain maps k x)) b] = 0 := by
            intro t a b
            have hsol := Submission.MoserGlobal.solutionAt_eq_unitFlow
              f hf L K hbound hlip (τ k).2.1 (τ (k + 1)).2.2 (step k).htime
              (step k).hpl hxClosed hxEq t
            let tu : Icc (0 : ℝ) 1 :=
              ⟨t, (τ k).2.1.trans t.2.1, t.2.2.trans (τ (k + 1)).2.2⟩
            rw [hsol]
            simpa only [tu] using hcoord tu a b
          have hlocal := solutionAt_pullback_eq ω₀ δ hδ f K hlip
            (step k).htime (step k).hpl hplT hxball hcoordLocal
            (fderiv ℝ (Submission.MoserSmoothFlow.stepChain maps k) x u)
            (fderiv ℝ (Submission.MoserSmoothFlow.stepChain maps k) x v)
          have hstepFD := Submission.MoserFlow.solutionAt_hasFDerivAt
            hf (step k).hpl hplT (step k).endTime hxball
          have hderivSucc : fderiv ℝ
              (Submission.MoserSmoothFlow.stepChain maps (k + 1)) x =
                (Submission.MoserFlow.solutionFDerivAt hplT (step k).endTime
                  (Submission.MoserSmoothFlow.stepChain maps k x)).comp
                    (fderiv ℝ (Submission.MoserSmoothFlow.stepChain maps k) x) := by
            change fderiv ℝ
              ((step k).map ∘ Submission.MoserSmoothFlow.stepChain maps k) x = _
            exact (hstepFD.comp x
              (hreg.differentiableAt (by norm_num)).hasFDerivAt).fderiv
          rw [hderivSucc]
          simp only [ContinuousLinearMap.comp_apply]
          exact hlocal.trans (hinv u v)
  obtain ⟨_hreg, heq, hinv⟩ := hchain m
  have hτm : τ m = (1 : Icc (0 : ℝ) 1) := hm m le_rfl
  have heqEnd : Submission.MoserSmoothFlow.stepChain maps m =ᶠ[𝓝 x]
      Submission.MoserSmoothFlow.unitTimeOneMap f hf L K hbound hlip := by
    filter_upwards [heq] with y hy
    rw [hτm] at hy
    exact hy
  have hmap := heqEnd.self_of_nhds
  have hderiv : fderiv ℝ (Submission.MoserSmoothFlow.stepChain maps m) x =
      fderiv ℝ (Submission.MoserSmoothFlow.unitTimeOneMap f hf L K hbound hlip) x :=
    heqEnd.fderiv_eq
  have hfinal := hinv u v
  rw [hτm, hmap, hderiv] at hfinal
  exact hfinal

theorem unitFlow_norm_le_exp
    (f : ℝ → V → V) (hf : ContDiff ℝ ∞ (uncurry f))
    (L K : ℝ≥0) (hbound : ∀ t z, ‖f t z‖ ≤ L)
    (hlip : ∀ t, LipschitzWith K (f t))
    (hzero : ∀ t : ℝ, f t 0 = 0)
    (x : V) (t : Icc (0 : ℝ) 1) :
    ‖Submission.MoserGlobal.unitFlow f hf L K hbound hlip t x‖ ≤
      ‖x‖ * Real.exp (K : ℝ) := by
  let path : ℝ → V := fun s => Submission.MoserGlobal.unitFlow
    f hf L K hbound hlip (projIcc (0 : ℝ) 1 zero_le_one s) x
  let zeroPath : ℝ → V := fun _ => 0
  have hpathCont : ContinuousOn path (Icc (0 : ℝ) 1) :=
    ((Submission.MoserGlobal.unitFlow_continuous f hf L K hbound hlip x).comp
      continuous_projIcc).continuousOn
  have hzeroCont : ContinuousOn zeroPath (Icc (0 : ℝ) 1) :=
    continuous_const.continuousOn
  have hpathDeriv : ∀ s ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt path (f s (path s)) (Ici s) s := by
    intro s hs
    have hsIcc : s ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self hs
    have hd := Submission.MoserGlobal.unitFlow_hasDerivWithinAt
      f hf L K hbound hlip x ⟨s, hsIcc⟩
    have hd' := hd.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hs)
    simpa only [path, projIcc_of_mem zero_le_one hsIcc] using hd'
  have hzeroDeriv : ∀ s ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt zeroPath (f s (zeroPath s)) (Ici s) s := by
    intro s _hs
    simpa [zeroPath, hzero] using
      (hasDerivAt_const (x := s) (0 : V)).hasDerivWithinAt
  have hstart : dist (path 0) (zeroPath 0) ≤ ‖x‖ := by
    have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    dsimp [path, zeroPath]
    rw [projIcc_of_mem zero_le_one h0]
    have ht0 : (⟨0, h0⟩ : Icc (0 : ℝ) 1) =
        Submission.MoserGlobal.unitInitialTime := Subtype.ext rfl
    rw [ht0,
      Submission.MoserGlobal.unitFlow_zero_time]
    simp
  have hdist := dist_le_of_trajectories_ODE hlip hpathCont hpathDeriv
    hzeroCont hzeroDeriv hstart (t : ℝ) t.2
  have hbase : ‖Submission.MoserGlobal.unitFlow f hf L K hbound hlip t x‖ ≤
      ‖x‖ * Real.exp ((K : ℝ) * (t : ℝ)) := by
    simpa [path, zeroPath, projIcc_of_mem zero_le_one t.2, hzero] using hdist
  have hKt : (K : ℝ) * (t : ℝ) ≤ K := by
    nlinarith [K.coe_nonneg, t.2.1, t.2.2]
  exact hbase.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hKt) (norm_nonneg x))

theorem moser_coordinate_identity_of_mem
    (ω₀ : V [⋀^Fin 2]→L[ℝ] ℝ)
    (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (hδ : ContDiff ℝ ∞ δ)
    (R ρ : ℝ)
    (hclosed : ∀ z ∈ ball (0 : V) R, extDeriv δ z = 0)
    (f : ℝ → V → V) (hf : ContDiff ℝ ∞ (uncurry f))
    (hfield : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ ball (0 : V) ρ,
      f t z = Submission.MoserField.moserField ω₀ δ (t, z))
    (hinv : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ ball (0 : V) ρ,
      (t, z) ∈ Submission.MoserField.invertibleLocus ω₀ δ)
    (t : Icc (0 : ℝ) 1) (q : V)
    (hqR : q ∈ ball (0 : V) R) (hqρ : q ∈ ball (0 : V) ρ)
    (u v : V) :
    δ q ![u, v] +
        (t : ℝ) * fderiv ℝ δ q (f t q) ![u, v] +
        Submission.MoserField.formPath ω₀ δ (t, q)
          ![Submission.MoserFlow.spaceFDeriv f (t, q) u, v] +
        Submission.MoserField.formPath ω₀ δ (t, q)
          ![u, Submission.MoserFlow.spaceFDeriv f (t, q) v] = 0 := by
  have hX : ContDiff ℝ ∞ (f t) :=
    hf.comp (contDiff_const.prodMk contDiff_id)
  have hclosedSegment : ∀ s ∈ Icc (0 : ℝ) 1,
      extDeriv δ (s • q) = 0 := by
    intro s hs
    apply hclosed
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hs.1]
    have hqnorm : ‖q‖ < R := by
      simpa [mem_ball, dist_zero_right] using hqR
    calc
      s * ‖q‖ ≤ 1 * ‖q‖ :=
        mul_le_mul_of_nonneg_right hs.2 (norm_nonneg q)
      _ < R := by simpa using hqnorm
  have heq : ∀ w : V,
      (fun z => Submission.MoserField.formPath ω₀ δ (t, z) ![f t z, w]) =ᶠ[𝓝 q]
        fun z => -Submission.RadialPrimitive.radialPrimitive δ z w := by
    intro w
    filter_upwards [isOpen_ball.mem_nhds hqρ] with z hz
    rw [hfield t t.2 z hz]
    have heqn := Submission.MoserField.moserField_equation
      ω₀ δ (t, z) (hinv t t.2 z hz)
    have happ := congrArg (fun l : V →L[ℝ] ℝ => l w) heqn
    simpa [Submission.MoserField.flat_apply] using happ
  have hcoord := Submission.PullbackInvariant.moser_coordinate_identity
    ω₀ δ hδ (f t) hX t q u v hclosedSegment heq
  rw [Submission.MoserFlow.fderiv_timeSlice_eq_spaceFDeriv f hf t q] at hcoord
  exact hcoord

end

end Submission.MoserInvariant
