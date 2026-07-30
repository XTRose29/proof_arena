import Submission.MoserFlow
import Mathlib.Topology.MetricSpace.Thickening

open Set Function Metric
open scoped ContDiff NNReal

namespace Submission.MoserGlobal

noncomputable section

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]

/-- A smooth retraction into the outer ball of a bump function, equal to the identity on its
inner ball. -/
def retractionAt (c : X) (b : ContDiffBump c) (x : X) : X :=
  c + b x • (x - c)

theorem retractionAt_contDiff (c : X) (b : ContDiffBump c) :
    ContDiff ℝ ∞ (retractionAt c b) := by
  unfold retractionAt
  exact contDiff_const.add (b.contDiff.smul (contDiff_id.sub contDiff_const))

theorem retractionAt_mem_closedBall (c : X) (b : ContDiffBump c) (x : X) :
    retractionAt c b x ∈ closedBall c b.rOut := by
  by_cases hx : x ∈ ball c b.rOut
  · rw [mem_closedBall, retractionAt, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg b.nonneg]
    calc
      b x * ‖x - c‖ ≤ 1 * ‖x - c‖ := by gcongr; exact b.le_one
      _ ≤ b.rOut := by simpa [mem_ball, dist_eq_norm] using (mem_ball.mp hx).le
  · have hb0 : b x = 0 := by
      apply b.zero_of_le_dist
      simpa [mem_ball, not_lt] using hx
    simp [retractionAt, hb0, b.rOut_pos.le]

theorem retractionAt_eq_self (c : X) (b : ContDiffBump c)
    {x : X} (hx : x ∈ closedBall c b.rIn) : retractionAt c b x = x := by
  rw [retractionAt, b.one_of_mem_closedBall hx, one_smul, add_sub_cancel]

theorem exists_timeBump {T : Set ℝ} (hT : IsOpen T) (hI : Icc (0 : ℝ) 1 ⊆ T) :
    ∃ b : ContDiffBump (1 / 2 : ℝ),
      Icc (0 : ℝ) 1 ⊆ closedBall (1 / 2 : ℝ) b.rIn ∧
      closedBall (1 / 2 : ℝ) b.rOut ⊆ T := by
  have h0T : (0 : ℝ) ∈ T := hI (by constructor <;> norm_num)
  have h1T : (1 : ℝ) ∈ T := hI (by constructor <;> norm_num)
  obtain ⟨ε0, hε0, hball0⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds h0T)
  obtain ⟨ε1, hε1, hball1⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds h1T)
  let δ := min ε0 ε1
  have hδ : 0 < δ := lt_min hε0 hε1
  let b : ContDiffBump (1 / 2 : ℝ) :=
    ⟨1 / 2 + δ / 4, 1 / 2 + δ / 2, by positivity, by linarith⟩
  refine ⟨b, ?_, ?_⟩
  · intro t ht
    rw [mem_closedBall, Real.dist_eq]
    have ht01 : 0 ≤ t ∧ t ≤ 1 := ht
    dsimp [b]
    rw [abs_le]
    constructor <;> linarith
  · intro t ht
    have htbound : -(δ / 2) ≤ t ∧ t ≤ 1 + δ / 2 := by
      rw [mem_closedBall, Real.dist_eq] at ht
      dsimp [b] at ht
      rw [abs_le] at ht
      constructor <;> linarith [ht.1, ht.2]
    by_cases ht0 : t < 0
    · apply hball0
      rw [mem_ball, Real.dist_eq, sub_zero, abs_of_neg ht0]
      have hδε0 : δ ≤ ε0 := min_le_left _ _
      linarith [htbound.1]
    · by_cases ht1 : t ≤ 1
      · exact hI ⟨le_of_not_gt ht0, ht1⟩
      · apply hball1
        rw [mem_ball, Real.dist_eq, abs_of_nonneg (by linarith)]
        have hδε1 : δ ≤ ε1 := min_le_right _ _
        linarith [htbound.2]

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- A globally smooth field agreeing with the Moser field near `[0,1] × {0}`. -/
theorem exists_global_moserField
    (ω₀ : V [⋀^Fin 2]→L[ℝ] ℝ)
    (hω₀ : ∀ v, v ≠ 0 → ∃ w, ω₀ ![v, w] ≠ 0)
    (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (hδ : ContDiff ℝ ∞ δ) (hδ0 : δ 0 = 0) :
    ∃ f : ℝ → V → V, ∃ ρ > (0 : ℝ), ∃ L K : ℝ≥0,
      ContDiff ℝ ∞ (uncurry f) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ ball (0 : V) ρ,
        f t z = Submission.MoserField.moserField ω₀ δ (t, z)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ ball (0 : V) ρ,
        (t, z) ∈ Submission.MoserField.invertibleLocus ω₀ δ) ∧
      (∀ t : ℝ, f t 0 = 0) ∧
      (∀ t z, ‖f t z‖ ≤ L) ∧ (∀ t, LipschitzWith K (f t)) := by
  obtain ⟨T, Z, hT, hZ, hIT, h0Z, hTZ⟩ :=
    Submission.MoserField.exists_open_prod_invertible ω₀ hω₀ δ hδ hδ0
  obtain ⟨bT, hIbT, hbTT⟩ := exists_timeBump hT hIT
  obtain ⟨ε, hε, hballZ⟩ := Metric.mem_nhds_iff.mp (hZ.mem_nhds h0Z)
  let bZ : ContDiffBump (0 : V) :=
    ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  let R : ℝ × V → ℝ × V := fun p =>
    (retractionAt (1 / 2 : ℝ) bT p.1,
      Submission.LocalForms.radialRetraction bZ p.2)
  have hR : ContDiff ℝ ∞ R := by
    exact (retractionAt_contDiff (1 / 2 : ℝ) bT).comp contDiff_fst |>.prodMk
      (Submission.LocalForms.radialRetraction_contDiff bZ |>.comp contDiff_snd)
  have hRmaps : MapsTo R univ (Submission.MoserField.invertibleLocus ω₀ δ) := by
    intro p _hp
    apply hTZ
    constructor
    · exact hbTT (retractionAt_mem_closedBall (1 / 2 : ℝ) bT p.1)
    · apply hballZ
      exact closedBall_subset_ball (by dsimp [bZ]; linarith) <|
        Submission.LocalForms.radialRetraction_mem_closedBall bZ p.2
  let f : ℝ → V → V := fun t z =>
    Submission.MoserField.moserField ω₀ δ (R (t, z))
  have hf : ContDiff ℝ ∞ (uncurry f) := by
    have hcomp : ContDiffOn ℝ ∞
        (Submission.MoserField.moserField ω₀ δ ∘ R) univ :=
      (Submission.MoserField.moserField_contDiffOn ω₀ δ hδ).comp
        hR.contDiffOn hRmaps
    exact contDiffOn_univ.mp hcomp
  let Q : Set (ℝ × V) :=
    closedBall (1 / 2 : ℝ) bT.rOut ×ˢ closedBall (0 : V) bZ.rOut
  have hQ : IsCompact Q :=
    (isCompact_closedBall (1 / 2 : ℝ) bT.rOut).prod
      (isCompact_closedBall (0 : V) bZ.rOut)
  have hQinv : Q ⊆ Submission.MoserField.invertibleLocus ω₀ δ := by
    intro p hp
    exact hTZ ⟨hbTT hp.1, hballZ <| closedBall_subset_ball
      (by dsimp [bZ]; linarith) hp.2⟩
  have hMcont : ContinuousOn (Submission.MoserField.moserField ω₀ δ) Q :=
    (Submission.MoserField.moserField_contDiffOn ω₀ δ hδ).continuousOn.mono hQinv
  have hMimage : IsCompact (Submission.MoserField.moserField ω₀ δ '' Q) :=
    hQ.image_of_continuousOn hMcont
  obtain ⟨C, hC⟩ := hMimage.isBounded.exists_norm_le
  have hcenterQ : ((1 / 2 : ℝ), (0 : V)) ∈ Q := by
    exact ⟨mem_closedBall_self bT.rOut_pos.le, mem_closedBall_self bZ.rOut_pos.le⟩
  have hC0 : 0 ≤ C :=
    norm_nonneg (Submission.MoserField.moserField ω₀ δ ((1 / 2 : ℝ), 0)) |>.trans
      (hC _ ⟨_, hcenterQ, rfl⟩)
  let L : ℝ≥0 := ⟨C, hC0⟩
  let aux : ℝ → V → V := fun s z =>
    Submission.MoserField.moserField ω₀ δ
      (s, Submission.LocalForms.radialRetraction bZ z)
  have hauxOn : ContDiffOn ℝ ∞ (uncurry aux) (T ×ˢ univ) := by
    have hmap : MapsTo
        (fun p : ℝ × V => (p.1, Submission.LocalForms.radialRetraction bZ p.2))
        (T ×ˢ univ) (Submission.MoserField.invertibleLocus ω₀ δ) := by
      intro p hp
      apply hTZ
      exact ⟨hp.1, hballZ <| closedBall_subset_ball
        (by dsimp [bZ]; linarith) <|
          Submission.LocalForms.radialRetraction_mem_closedBall bZ p.2⟩
    exact (Submission.MoserField.moserField_contDiffOn ω₀ δ hδ).comp
      (contDiffOn_fst.prodMk
        ((Submission.LocalForms.radialRetraction_contDiff bZ).comp contDiff_snd).contDiffOn)
      hmap
  have hTUopen : IsOpen (T ×ˢ (univ : Set V)) := hT.prod isOpen_univ
  let spacePart : ℝ × V → (V →L[ℝ] V) := fun p =>
    (fderiv ℝ (uncurry aux) p).comp (ContinuousLinearMap.inr ℝ ℝ V)
  have hspacePartCont : ContinuousOn spacePart (T ×ˢ (univ : Set V)) := by
    unfold spacePart
    exact (hauxOn.continuousOn_fderiv_of_isOpen hTUopen (by simp)).clm_comp
      continuousOn_const
  have hspacePartImage : IsCompact (spacePart '' Q) :=
    hQ.image_of_continuousOn (hspacePartCont.mono fun _ hp => ⟨hbTT hp.1, trivial⟩)
  obtain ⟨D, hD⟩ := hspacePartImage.isBounded.exists_norm_le
  have hD0 : 0 ≤ D :=
    norm_nonneg (spacePart ((1 / 2 : ℝ), (0 : V))) |>.trans
      (hD _ ⟨_, hcenterQ, rfl⟩)
  let K : ℝ≥0 := ⟨D, hD0⟩
  have hauxSlice (s : ℝ) (hs : s ∈ closedBall (1 / 2 : ℝ) bT.rOut) :
      ContDiff ℝ ∞ (aux s) := by
    have hcomp : ContDiffOn ℝ ∞
        (uncurry aux ∘ fun z : V => (s, z)) univ :=
      hauxOn.comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (fun _ _ => ⟨hbTT hs, trivial⟩)
    change ContDiffOn ℝ ∞ (aux s) univ at hcomp
    exact contDiffOn_univ.mp hcomp
  have htsupport (s : ℝ) : tsupport (aux s) ⊆ closedBall (0 : V) bZ.rOut := by
    apply closure_minimal _ isClosed_closedBall
    intro z hz
    by_contra hzball
    have hb0 : bZ z = 0 := by
      apply bZ.zero_of_le_dist
      have hdist : bZ.rOut < dist z 0 := by
        simpa [mem_closedBall, not_le] using hzball
      exact hdist.le
    apply hz
    simp [aux, Submission.LocalForms.radialRetraction, hb0,
      Submission.MoserField.moserField_zero]
  have hsliceFDeriv (s : ℝ) (hs : s ∈ closedBall (1 / 2 : ℝ) bT.rOut)
      (z : V) : fderiv ℝ (aux s) z = spacePart (s, z) := by
    have hp : (s, z) ∈ T ×ˢ (univ : Set V) := ⟨hbTT hs, trivial⟩
    have hfull : DifferentiableAt ℝ (uncurry aux) (s, z) :=
      (hauxOn.contDiffAt (hTUopen.mem_nhds hp)).differentiableAt (by simp)
    exact (hfull.hasFDerivAt.comp z (hasFDerivAt_prodMk_right s z)).fderiv
  have hderivBound (s : ℝ) (hs : s ∈ closedBall (1 / 2 : ℝ) bT.rOut)
      (z : V) : ‖fderiv ℝ (aux s) z‖₊ ≤ K := by
    by_cases hz : z ∈ closedBall (0 : V) bZ.rOut
    · rw [← NNReal.coe_le_coe]
      change ‖fderiv ℝ (aux s) z‖ ≤ D
      rw [hsliceFDeriv s hs z]
      exact hD _ ⟨(s, z), ⟨hs, hz⟩, rfl⟩
    · have hzts : z ∉ tsupport (aux s) := fun h => hz (htsupport s h)
      rw [fderiv_of_notMem_tsupport ℝ hzts]
      simp
  refine ⟨f, bZ.rIn, bZ.rIn_pos, L, K, hf, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht z hz
    have htfix : retractionAt (1 / 2 : ℝ) bT t = t :=
      retractionAt_eq_self (1 / 2 : ℝ) bT (hIbT ht)
    have hzfix : Submission.LocalForms.radialRetraction bZ z = z :=
      Submission.LocalForms.radialRetraction_eq_self bZ (mem_closedBall.mpr (mem_ball.mp hz).le)
    simp only [f, R, htfix, hzfix]
  · intro t ht z hz
    apply hTZ
    constructor
    · exact hIT ht
    · apply hballZ
      apply mem_ball.mpr
      have hzdist := mem_ball.mp hz
      dsimp [bZ] at hzdist ⊢
      linarith
  · intro t
    simp [f, R, Submission.LocalForms.radialRetraction,
      Submission.MoserField.moserField_zero]
  · intro t z
    change ‖Submission.MoserField.moserField ω₀ δ (R (t, z))‖ ≤ C
    exact hC _ ⟨R (t, z),
      ⟨retractionAt_mem_closedBall (1 / 2 : ℝ) bT t,
        Submission.LocalForms.radialRetraction_mem_closedBall bZ z⟩, rfl⟩
  · intro t
    have hs := retractionAt_mem_closedBall (1 / 2 : ℝ) bT t
    have hlip : LipschitzWith K (aux (retractionAt (1 / 2 : ℝ) bT t)) :=
      lipschitzWith_of_nnnorm_fderiv_le
        ((hauxSlice _ hs).differentiable (by simp)) (hderivBound _ hs)
    simpa only [f, R, aux] using hlip

section UnitFlow

variable (f : ℝ → V → V) (hf : ContDiff ℝ ∞ (uncurry f))
  (L K : ℝ≥0) (hbound : ∀ t z, ‖f t z‖ ≤ L)
  (hlip : ∀ t, LipschitzWith K (f t))

def unitInitialTime : Icc (0 : ℝ) 1 := ⟨0, by constructor <;> norm_num⟩

include f hf L K hbound hlip

omit [FiniteDimensional ℝ V] in
theorem unitPicardData (x : V) : IsPicardLindelof f unitInitialTime x L 0 L K where
  lipschitzOnWith t _ht := (hlip t).lipschitzOnWith
  continuousOn x _hx :=
    (hf.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
  norm_le t _ht z _hz := hbound t z
  mul_max_le := by simp [unitInitialTime]

/-- The selected global solution of the bounded field on the unit time interval. -/
def unitFlow (t : Icc (0 : ℝ) 1) (x : V) : V :=
  Submission.MoserFlow.solutionAt (unitPicardData f hf L K hbound hlip x) t x

@[simp]
theorem unitFlow_zero_time (x : V) :
    unitFlow f hf L K hbound hlip unitInitialTime x = x := by
  apply Submission.MoserFlow.solutionAt_initial
  simp

theorem unitFlow_hasDerivWithinAt (x : V) (t : Icc (0 : ℝ) 1) :
    HasDerivWithinAt (fun s : ℝ => unitFlow f hf L K hbound hlip
      (projIcc (0 : ℝ) 1 zero_le_one s) x)
      (f t (unitFlow f hf L K hbound hlip t x)) (Icc (0 : ℝ) 1) t := by
  apply Submission.MoserFlow.solutionAt_hasDerivWithinAt_time
  simp

theorem unitFlow_continuous (x : V) :
    Continuous fun t : Icc (0 : ℝ) 1 => unitFlow f hf L K hbound hlip t x := by
  let hpl := unitPicardData f hf L K hbound hlip x
  have hx : x ∈ closedBall x (0 : ℝ) := by simp
  have heq : (fun t : Icc (0 : ℝ) 1 => unitFlow f hf L K hbound hlip t x) =
      fun t => Submission.MoserFlow.solutionCurve hpl hx t := by
    funext t
    exact Submission.MoserFlow.solutionAt_of_mem hpl t hx
  rw [heq]
  exact (Submission.MoserFlow.solutionCurve hpl hx).continuous

theorem unitFlow_eq_of_equilibrium (hzero : ∀ t : ℝ, f t 0 = 0)
    (t : Icc (0 : ℝ) 1) : unitFlow f hf L K hbound hlip t 0 = 0 := by
  apply Submission.MoserFlow.solutionAt_eq_of_equilibrium
  · simp
  · exact hzero

theorem solutionAt_eq_unitFlow
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b)
    {xcenter y x : V} {A r L' K' : ℝ≥0}
    (hpl : IsPicardLindelof f
      (tmin := a) (tmax := b) ⟨a, by exact ⟨le_rfl, hab⟩⟩ xcenter A r L' K')
    (hy : y ∈ closedBall xcenter r)
    (hinit : y = unitFlow f hf L K hbound hlip
      ⟨a, by exact ⟨ha, hab.trans hb⟩⟩ x)
    (t : Icc a b) :
    Submission.MoserFlow.solutionAt hpl t y =
      unitFlow f hf L K hbound hlip
        ⟨t, ha.trans t.2.1, t.2.2.trans hb⟩ x := by
  let localPath : ℝ → V := fun s => Submission.MoserFlow.solutionAt hpl
    (projIcc a b hab s) y
  let globalPath : ℝ → V := fun s => unitFlow f hf L K hbound hlip
    (projIcc (0 : ℝ) 1 zero_le_one s) x
  have hlocalCont : ContinuousOn localPath (Icc a b) := by
    have heq : localPath =
        (Submission.MoserFlow.solutionCurve hpl hy).compProj := by
      funext s
      dsimp [localPath]
      rw [Submission.MoserFlow.solutionAt_of_mem hpl _ hy]
    rw [heq]
    exact (Submission.MoserFlow.solutionCurve hpl hy).continuous_compProj.continuousOn
  have hglobalCont : ContinuousOn globalPath (Icc a b) := by
    exact ((unitFlow_continuous f hf L K hbound hlip x).comp
      continuous_projIcc).continuousOn
  have hlocalDeriv : ∀ s ∈ Ico a b,
      HasDerivWithinAt localPath (f s (localPath s)) (Ici s) s := by
    intro s hs
    have hsIcc : s ∈ Icc a b := Ico_subset_Icc_self hs
    have hd := Submission.MoserFlow.solutionAt_hasDerivWithinAt_time hpl hy
      ⟨s, hsIcc⟩
    have hd' := hd.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hs)
    simpa only [localPath, projIcc_of_mem hab hsIcc] using hd'
  have hglobalDeriv : ∀ s ∈ Ico a b,
      HasDerivWithinAt globalPath (f s (globalPath s)) (Ici s) s := by
    intro s hs
    have hsIcc : s ∈ Icc a b := Ico_subset_Icc_self hs
    have hsUnit : s ∈ Icc (0 : ℝ) 1 :=
      ⟨ha.trans hsIcc.1, hsIcc.2.trans hb⟩
    have hd := unitFlow_hasDerivWithinAt f hf L K hbound hlip x ⟨s, hsUnit⟩
    have hseg : Icc a b ⊆ Icc (0 : ℝ) 1 := fun q hq =>
      ⟨ha.trans hq.1, hq.2.trans hb⟩
    have hd' := (hd.mono hseg).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hs)
    simpa only [globalPath, projIcc_of_mem zero_le_one hsUnit] using hd'
  have hstart : localPath a = globalPath a := by
    have haab : a ∈ Icc a b := ⟨le_rfl, hab⟩
    have haunit : a ∈ Icc (0 : ℝ) 1 := ⟨ha, hab.trans hb⟩
    calc
      localPath a = y := by
        dsimp [localPath]
        simpa only [projIcc_of_mem hab haab] using
          Submission.MoserFlow.solutionAt_initial hpl hy
      _ = globalPath a := by
        rw [hinit]
        dsimp [globalPath]
        rw [projIcc_of_mem zero_le_one haunit]
  have heq := ODE_solution_unique hlip hlocalCont hlocalDeriv
    hglobalCont hglobalDeriv hstart
  have htEq := heq t.2
  have htUnit : (t : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨ha.trans t.2.1, t.2.2.trans hb⟩
  simpa only [localPath, globalPath, projIcc_of_mem hab t.2,
    projIcc_of_mem zero_le_one htUnit]
    using htEq

end UnitFlow

end

end Submission.MoserGlobal
