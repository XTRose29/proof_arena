import Submission.HomotopyUniqueness
import Submission.Reduction
import Submission.Separation

namespace Submission.Helpers

open Set

noncomputable section

/-- The only general fact about self-maps of a sphere needed by the final
Jordan--Brouwer reduction: composition is commutative up to homotopy. -/
def SphereSelfMapsCommute (d : ℕ) : Prop :=
  ∀ f g : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1),
    ContinuousMap.Homotopic (f.comp g) (g.comp f)

/-- A homotopy of boundary data can be absorbed in a collar of the embedded
sphere.  Thus, if the second endpoint extends sphere-valuedly over the
closure of an open set whose frontier is the embedded sphere, then so does
the first endpoint. -/
theorem exists_closure_extension_of_homotopic_sphere_maps
    (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) (hinj : Function.Injective r)
    (U : Set (EuclideanSpace ℝ (Fin d)))
    (hfront : frontier U = Set.range r)
    (f g : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1))
    (G : C(closure U,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1))
    (hG : ∀ z, G ⟨r z, frontier_subset_closure (hfront.symm ▸ ⟨z, rfl⟩)⟩ = g z)
    (hfg : ContinuousMap.Homotopic f g) :
    ∃ F : C(closure U,
        Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1),
      ∀ z, F ⟨r z, frontier_subset_closure (hfront.symm ▸ ⟨z, rfl⟩)⟩ = f z := by
  classical
  let E := EuclideanSpace ℝ (Fin d)
  let S := Metric.sphere (0 : E) 1
  let Cset := closure U
  let e : C(S, Cset) :=
    { toFun := fun z ↦ ⟨r z, frontier_subset_closure (by
          rw [hfront]
          exact ⟨z, rfl⟩)⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact hcont }
  have heCompact : IsCompact (Set.range e) := isCompact_range e.continuous
  obtain ⟨W, hWOpen, hrW, ρ, hρ⟩ :=
    exists_open_neighborhood_retraction d hd r hcont hinj
  let WC : Set Cset := Subtype.val ⁻¹' W
  have hWCOpen : IsOpen WC := hWOpen.preimage continuous_subtype_val
  let ρC : C(WC, S) :=
    { toFun := fun w ↦ ρ ⟨(w : E), w.2⟩
      continuous_toFun := by
        apply ρ.continuous.comp
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp continuous_subtype_val }
  let goodW : Set WC := {w | dist
      (g (ρC w) : E) (G w.1 : E) < 2}
  have hgoodWOpen : IsOpen goodW := by
    exact isOpen_lt
      (g.continuous.comp ρC.continuous |>.dist
        (G.continuous.comp continuous_subtype_val))
      continuous_const
  let good : Set Cset := ((↑) : WC → Cset) '' goodW
  have hgoodOpen : IsOpen good := by
    exact hWCOpen.isOpenMap_subtype_val goodW hgoodWOpen
  have heGood : Set.range e ⊆ good := by
    rintro _ ⟨z, rfl⟩
    have heW : (e z : E) ∈ W := hrW ⟨z, rfl⟩
    let w : WC := ⟨e z, heW⟩
    refine ⟨w, ?_, rfl⟩
    change dist (g (ρC w) : E) (G (e z) : E) < 2
    rw [show ρC w = z by exact hρ z,
      show G (e z) = g z by exact hG z]
    simp
  have hgoodNhds : good ∈ nhdsSet (Set.range e) :=
    (hgoodOpen.mem_nhdsSet).2 heGood
  obtain ⟨O₂, hO₂Open, heO₂, hO₂Good⟩ :=
    heCompact.exists_isOpen_closure_subset hgoodNhds
  have hO₂Nhds : O₂ ∈ nhdsSet (Set.range e) :=
    (hO₂Open.mem_nhdsSet).2 heO₂
  obtain ⟨O₁, hO₁Open, heO₁, hO₁O₂⟩ :=
    heCompact.exists_isOpen_closure_subset hO₂Nhds
  have hO₁Nhds : O₁ ∈ nhdsSet (Set.range e) :=
    (hO₁Open.mem_nhdsSet).2 heO₁
  obtain ⟨O₀, hO₀Open, heO₀, hO₀O₁⟩ :=
    heCompact.exists_isOpen_closure_subset hO₁Nhds
  obtain ⟨φ, hφ0, hφ1, hφrange⟩ :=
    exists_continuous_zero_one_of_isClosed heCompact.isClosed
      hO₀Open.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr heO₀)
  obtain ⟨ψ, hψ0, hψ1, hψrange⟩ :=
    exists_continuous_zero_one_of_isClosed isClosed_closure
      hO₁Open.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr hO₀O₁)
  let C₂ : Set Cset := closure O₂
  have hC₂Good : C₂ ⊆ good := hO₂Good
  have hgoodData (w : Cset) (hw : w ∈ good) :
      ∃ hwW : (w : E) ∈ W,
        dist (g (ρ ⟨(w : E), hwW⟩) : E) (G w : E) < 2 := by
    rcases hw with ⟨v, hv, rfl⟩
    change dist (g (ρC v) : E) (G v.1 : E) < 2 at hv
    refine ⟨v.2, ?_⟩
    have hrho : ρ ⟨((v : Cset) : E), v.2⟩ = ρC v := by
      apply congrArg ρ
      apply Subtype.ext
      rfl
    rw [hrho]
    exact hv
  have hC₂W (w : C₂) : ((w : Cset) : E) ∈ W :=
    (hgoodData w (hC₂Good w.2)).choose
  let liftC₂ : C(C₂, WC) :=
    { toFun := fun w ↦ ⟨w.1, hC₂W w⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val }
  let ρC₂ : C(C₂, S) := ρC.comp liftC₂
  let GC₂ : C(C₂, S) :=
    G.comp
      { toFun := fun w ↦ w.1
        continuous_toFun := continuous_subtype_val }
  obtain ⟨H⟩ := hfg
  let φI : C(Cset, unitInterval) :=
    { toFun := fun w ↦ ⟨φ w, hφrange w⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact φ.continuous }
  let homotopyPart : C(C₂, S) :=
    { toFun := fun w ↦ H (φI w.1, ρC₂ w)
      continuous_toFun := H.continuous.comp
        ((φI.continuous.comp continuous_subtype_val).prodMk ρC₂.continuous) }
  let raw : C₂ → E := fun w ↦
    (1 - ψ w.1) • (homotopyPart w : E) +
      ψ w.1 • (GC₂ w : E)
  have hrawContinuous : Continuous raw := by
    exact (continuous_const.sub (ψ.continuous.comp continuous_subtype_val)).smul
      (continuous_subtype_val.comp homotopyPart.continuous) |>.add
        ((ψ.continuous.comp continuous_subtype_val).smul
          (continuous_subtype_val.comp GC₂.continuous))
  have hrawNe (w : C₂) : raw w ≠ 0 := by
    by_cases hwO₀ : (w : Cset) ∈ O₀
    · have hψw : ψ w.1 = 0 := hψ0 (subset_closure hwO₀)
      change (1 - ψ w.1) • (homotopyPart w : E) +
          ψ w.1 • (GC₂ w : E) ≠ 0
      rw [hψw]
      have hnorm := mem_sphere_zero_iff_norm.mp (homotopyPart w).2
      simp only [sub_zero, one_smul, zero_smul, add_zero]
      intro hzero
      rw [hzero, norm_zero] at hnorm
      norm_num at hnorm
    · have hφw : φ w.1 = 1 := hφ1 hwO₀
      have hφIw : φI w.1 = 1 := Subtype.ext hφw
      have hhomPart : homotopyPart w = g (ρC₂ w) := by
        change H (φI w.1, ρC₂ w) = _
        rw [hφIw]
        exact H.map_one_left (ρC₂ w)
      have hclose : dist (g (ρC₂ w) : E) (GC₂ w : E) < 2 := by
        have hg := (hgoodData w.1 (hC₂Good w.2)).choose_spec
        change dist (g (ρ ⟨((w : Cset) : E), hC₂W w⟩) : E)
          (G w.1 : E) < 2
        simpa only [hC₂W] using hg
      apply convexCombination_ne_zero_of_norm_eq_one_of_dist_lt_two
        (mem_sphere_zero_iff_norm.mp (homotopyPart w).2)
        (mem_sphere_zero_iff_norm.mp (GC₂ w).2)
        (by simpa only [hhomPart] using hclose)
        (hψrange w.1).1 (hψrange w.1).2
  let inside : C(C₂, S) :=
    { toFun := fun w ↦ ⟨NormedSpace.normalize (raw w), by
          rw [mem_sphere_zero_iff_norm]
          exact NormedSpace.norm_normalize (hrawNe w)⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        change Continuous (fun w ↦ ‖raw w‖⁻¹ • raw w)
        exact (hrawContinuous.norm.inv₀ fun w ↦
          norm_ne_zero_iff.mpr (hrawNe w)).smul hrawContinuous }
  have hinside_eq_G {w : C₂} (hw : (w : Cset) ∉ O₁) :
      inside w = G w.1 := by
    have hφw : φ w.1 = 1 := hφ1 (fun hwO₀ ↦ hw (hO₀O₁ (subset_closure hwO₀)))
    have hψw : ψ w.1 = 1 := hψ1 hw
    apply Subtype.ext
    change NormedSpace.normalize (raw w) = (G w.1 : E)
    have hφIw : φI w.1 = 1 := Subtype.ext hφw
    change NormedSpace.normalize
        ((1 - ψ w.1) • (homotopyPart w : E) +
          ψ w.1 • (GC₂ w : E)) = _
    rw [hψw]
    simp only [sub_self, zero_smul, one_smul, zero_add]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one
      (mem_sphere_zero_iff_norm.mp (GC₂ w).2)
  let Ffun : Cset → S := fun w ↦
    if hw : w ∈ C₂ then inside ⟨w, hw⟩ else G w
  have hFfunContinuous : Continuous Ffun := by
    have hclosedC₂ : IsClosed C₂ := isClosed_closure
    have hclosedO₁c : IsClosed O₁ᶜ := hO₁Open.isClosed_compl
    have hcover : C₂ ∪ O₁ᶜ = Set.univ := by
      apply Set.eq_univ_of_forall
      intro w
      by_cases hw : w ∈ O₁
      · exact Or.inl (subset_closure (hO₁O₂ (subset_closure hw)))
      · exact Or.inr hw
    have hcontC₂ : ContinuousOn Ffun C₂ := by
      rw [continuousOn_iff_continuous_restrict]
      have heq : C₂.restrict Ffun = fun w : C₂ ↦ inside w := by
        funext w
        simp only [Set.restrict, Ffun, dif_pos w.2]
      rw [heq]
      exact inside.continuous
    have hcontO₁c : ContinuousOn Ffun O₁ᶜ := by
      apply G.continuous.continuousOn.congr
      intro w hw
      by_cases hwC₂ : w ∈ C₂
      · rw [show Ffun w = inside ⟨w, hwC₂⟩ by simp [Ffun, hwC₂]]
        exact hinside_eq_G hw
      · simp [Ffun, hwC₂]
    have hUnion : ContinuousOn Ffun (C₂ ∪ O₁ᶜ) :=
      hcontC₂.union_of_isClosed hcontO₁c hclosedC₂ hclosedO₁c
    rw [hcover] at hUnion
    exact continuousOn_univ.mp hUnion
  let F : C(Cset, S) := ⟨Ffun, hFfunContinuous⟩
  refine ⟨F, ?_⟩
  intro z
  have heC₂ : e z ∈ C₂ := subset_closure (heO₂ ⟨z, rfl⟩)
  have hφz : φ (e z) = 0 := hφ0 ⟨z, rfl⟩
  have hψz : ψ (e z) = 0 := hψ0 (subset_closure (heO₀ ⟨z, rfl⟩))
  change Ffun (e z) = f z
  rw [show Ffun (e z) = inside ⟨e z, heC₂⟩ by simp [Ffun, heC₂]]
  apply Subtype.ext
  change NormedSpace.normalize (raw ⟨e z, heC₂⟩) = _
  have hρz : ρC₂ ⟨e z, heC₂⟩ = z := hρ z
  have hφIz : φI (e z) = 0 := Subtype.ext hφz
  change NormedSpace.normalize
      ((1 - ψ (e z)) •
          (H (φI (e z), ρC₂ ⟨e z, heC₂⟩) : E) +
        ψ (e z) • (G (e z) : E)) = _
  rw [hψz, hφIz, hρz]
  simp only [sub_zero, one_smul, zero_smul, add_zero]
  have hH0 : (H (0, z) : E) = (f z : E) :=
    congrArg Subtype.val (H.map_zero_left z)
  calc
    NormedSpace.normalize (H (0, z) : E) =
        NormedSpace.normalize (f z : E) := congrArg NormedSpace.normalize hH0
    _ = (f z : E) := NormedSpace.normalize_eq_self_of_norm_eq_one
      (mem_sphere_zero_iff_norm.mp (f z).2)

/-- If `P` is essential, then `P ∘ gaussMap x` cannot extend over the
closure of the bounded component containing `x`.  Patching such an extension
to the radial direction map outside the component would extend `P` over a
large ball. -/
theorem essential_comp_gaussMap_not_extend_bounded_component
    (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) (hinj : Function.Injective r)
    (x : ((Set.range r)ᶜ : Set (EuclideanSpace ℝ (Fin d))))
    (hxb : Bornology.IsBounded
      (connectedComponentIn (Set.range r)ᶜ
        (x : EuclideanSpace ℝ (Fin d))))
    (P : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1))
    (hP : ¬ SphereMapNullhomotopic d P)
    (D : C(closure (connectedComponentIn (Set.range r)ᶜ
        (x : EuclideanSpace ℝ (Fin d))),
      Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1))
    (hD : ∀ z, D ⟨r z, frontier_subset_closure (by
        rw [frontier_bounded_sphere_complement_component_eq_range
          d hd r hcont hinj x.2 hxb]
        exact ⟨z, rfl⟩)⟩ = P (gaussMap d r hcont x z)) : False := by
  classical
  let E := EuclideanSpace ℝ (Fin d)
  let S := Metric.sphere (0 : E) 1
  let U : Set E := connectedComponentIn (Set.range r)ᶜ (x : E)
  have hxU : (x : E) ∈ U := mem_connectedComponentIn x.2
  have hUOpen : IsOpen U :=
    (isOpen_compl_range_sphere_embedding d r hcont hinj).connectedComponentIn
  have hfront : frontier U = Set.range r :=
    frontier_bounded_sphere_complement_component_eq_range
      d hd r hcont hinj x.2 hxb
  let DE : C(closure U, E) :=
    { toFun := fun w ↦ (D w : E)
      continuous_toFun := continuous_subtype_val.comp D.continuous }
  obtain ⟨Dext, hDext⟩ :=
    DE.exists_extension isClosed_closure.isClosedEmbedding_subtypeVal
  obtain ⟨z₀, hz₀⟩ :=
    (isConnected_sphere (euclidean_rank_gt_one d hd) 0
      (show (0 : ℝ) ≤ 1 by norm_num)).nonempty
  let z₀ : S := ⟨z₀, hz₀⟩
  let radialOutside : C((Uᶜ : Set E), S) :=
    { toFun := fun w ↦ ⟨NormedSpace.normalize ((w : E) - (x : E)), by
          rw [mem_sphere_zero_iff_norm]
          apply NormedSpace.norm_normalize
          exact sub_ne_zero.mpr fun hwx ↦ w.2 (hwx ▸ hxU)⟩
      continuous_toFun := by
        have hv : Continuous (fun w : (Uᶜ : Set E) ↦ (w : E) - (x : E)) :=
          continuous_subtype_val.sub continuous_const
        apply Continuous.subtype_mk
        change Continuous (fun w : (Uᶜ : Set E) ↦
          ‖(w : E) - (x : E)‖⁻¹ • ((w : E) - (x : E)))
        exact (hv.norm.inv₀ fun w ↦ norm_ne_zero_iff.mpr <|
          sub_ne_zero.mpr fun hwx ↦ w.2 (hwx ▸ hxU)).smul hv }
  let outside : E → E := fun w ↦
    if hw : w ∈ Uᶜ then (P (radialOutside ⟨w, hw⟩) : E) else (P z₀ : E)
  have houtsideContinuous : ContinuousOn outside Uᶜ := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : (Uᶜ : Set E).restrict outside =
        fun w : (Uᶜ : Set E) ↦ (P (radialOutside w) : E) := by
      funext w
      dsimp only [Set.restrict, outside]
      rw [dif_pos w.2]
    rw [heq]
    exact continuous_subtype_val.comp (P.continuous.comp radialOutside.continuous)
  have hboundary : Set.EqOn Dext outside (frontier U) := by
    intro w hw
    have hwRange : w ∈ Set.range r := hfront ▸ hw
    obtain ⟨z, rfl⟩ := hwRange
    have hrClosure : r z ∈ closure U := frontier_subset_closure hw
    have hDextz : Dext (r z) = (D ⟨r z, hrClosure⟩ : E) :=
      DFunLike.congr_fun hDext ⟨r z, hrClosure⟩
    have hrCompl : r z ∈ Uᶜ := by
      rw [Set.mem_compl_iff]
      intro hrU
      exact (connectedComponentIn_subset (Set.range r)ᶜ (x : E) hrU) ⟨z, rfl⟩
    rw [hDextz, hD]
    change (P (gaussMap d r hcont x z) : E) = outside (r z)
    rw [show outside (r z) = (P (radialOutside ⟨r z, hrCompl⟩) : E) by
      dsimp only [outside]
      rw [dif_pos hrCompl]]
    congr 2
  let Qvec : E → E := U.piecewise Dext outside
  have hQvecContinuous : Continuous Qvec := by
    exact continuous_piecewise hboundary Dext.continuous.continuousOn
      (by simpa [hUOpen.isClosed_compl.closure_eq] using houtsideContinuous)
  have hQvecNorm (w : E) : ‖Qvec w‖ = 1 := by
    by_cases hw : w ∈ U
    · have hDextw : Dext w = (D ⟨w, subset_closure hw⟩ : E) :=
        DFunLike.congr_fun hDext ⟨w, subset_closure hw⟩
      rw [show Qvec w = Dext w by simp [Qvec, hw], hDextw]
      exact mem_sphere_zero_iff_norm.mp (D ⟨w, subset_closure hw⟩).2
    · have hwc : w ∈ Uᶜ := hw
      rw [show Qvec w = outside w by simp [Qvec, hw],
        show outside w = (P (radialOutside ⟨w, hwc⟩) : E) by
          dsimp only [outside]
          rw [dif_pos hwc]]
      exact mem_sphere_zero_iff_norm.mp (P (radialOutside ⟨w, hwc⟩)).2
  let Q : C(E, S) :=
    { toFun := fun w ↦ ⟨Qvec w, mem_sphere_zero_iff_norm.mpr (hQvecNorm w)⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact hQvecContinuous }
  obtain ⟨R, hRsub⟩ := hxb.closure.subset_ball (x : E)
  have hR : 0 < R := by
    have h := hRsub (subset_closure hxU)
    simpa only [Metric.mem_ball, dist_self] using h
  let affineBall : Metric.closedBall (0 : E) 1 → E :=
    fun q ↦ (x : E) + R • (q : E)
  have haffine : Continuous affineBall := by
    exact continuous_const.add (continuous_const.smul continuous_subtype_val)
  let Gball : C(Metric.closedBall (0 : E) 1, S) :=
    { toFun := fun q ↦ Q (affineBall q)
      continuous_toFun := Q.continuous.comp haffine }
  have hGball (z : S) :
      Gball (unitSphereClosedBallInclusion d z) = P z := by
    have hzOutside : (x : E) + R • (z : E) ∉ U := by
      intro hzU
      have hzBall := hRsub (subset_closure hzU)
      rw [Metric.mem_ball, dist_eq_norm] at hzBall
      have hznorm : ‖(z : E)‖ = 1 := mem_sphere_zero_iff_norm.mp z.2
      have : ‖(x : E) + R • (z : E) - (x : E)‖ = R := by
        rw [show (x : E) + R • (z : E) - (x : E) = R • (z : E) by abel,
          norm_smul, Real.norm_eq_abs, abs_of_pos hR, hznorm, mul_one]
      rw [this] at hzBall
      exact (lt_irrefl R) hzBall
    have hzCompl : (x : E) + R • (z : E) ∈ Uᶜ := hzOutside
    apply Subtype.ext
    change Qvec ((x : E) + R • (z : E)) = (P z : E)
    rw [show Qvec ((x : E) + R • (z : E)) =
        outside ((x : E) + R • (z : E)) by simp [Qvec, hzOutside],
      show outside ((x : E) + R • (z : E)) =
          (P (radialOutside ⟨(x : E) + R • (z : E), hzCompl⟩) : E) by
        dsimp only [outside]
        rw [dif_pos hzCompl]]
    congr 2
    apply Subtype.ext
    change NormedSpace.normalize
        ((x : E) + R • (z : E) - (x : E)) = (z : E)
    rw [show (x : E) + R • (z : E) - (x : E) = R • (z : E) by abel,
      NormedSpace.normalize_smul_of_pos hR]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one
      (mem_sphere_zero_iff_norm.mp z.2)
  exact hP (sphereMapNullhomotopic_of_closedBall_extension d P Gball hGball)

/-- If the Gauss maps based at two bounded complementary components commute
up to homotopy, then the two components coincide. -/
theorem bounded_components_eq_of_gaussMap_comp_comm
    (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) (hinj : Function.Injective r)
    (x y : ((Set.range r)ᶜ : Set (EuclideanSpace ℝ (Fin d))))
    (hxb : Bornology.IsBounded
      (connectedComponentIn (Set.range r)ᶜ
        (x : EuclideanSpace ℝ (Fin d))))
    (hyb : Bornology.IsBounded
      (connectedComponentIn (Set.range r)ᶜ
        (y : EuclideanSpace ℝ (Fin d))))
    (hcomm : ContinuousMap.Homotopic
      ((gaussMap d r hcont y).comp (gaussMap d r hcont x))
      ((gaussMap d r hcont x).comp (gaussMap d r hcont y))) :
    connectedComponentIn (Set.range r)ᶜ
        (x : EuclideanSpace ℝ (Fin d)) =
      connectedComponentIn (Set.range r)ᶜ
        (y : EuclideanSpace ℝ (Fin d)) := by
  classical
  let E := EuclideanSpace ℝ (Fin d)
  let S := Metric.sphere (0 : E) 1
  let U : Set E := connectedComponentIn (Set.range r)ᶜ (x : E)
  by_contra hcomponents
  have hyNotClosure : (y : E) ∉ closure U := by
    intro hycl
    have hUOpen : IsOpen U :=
      (isOpen_compl_range_sphere_embedding d r hcont hinj).connectedComponentIn
    let Uy : Set E := connectedComponentIn (Set.range r)ᶜ (y : E)
    have hUyOpen : IsOpen Uy :=
      (isOpen_compl_range_sphere_embedding d r hcont hinj).connectedComponentIn
    have hyUy : (y : E) ∈ Uy := mem_connectedComponentIn y.2
    obtain ⟨z, hzUy, hzU⟩ := mem_closure_iff.mp hycl Uy hUyOpen hyUy
    have hxz : U = connectedComponentIn (Set.range r)ᶜ z :=
      connectedComponentIn_eq hzU
    have hyz : Uy = connectedComponentIn (Set.range r)ᶜ z :=
      connectedComponentIn_eq hzUy
    exact hcomponents (hxz.trans hyz.symm)
  have hfront : frontier U = Set.range r :=
    frontier_bounded_sphere_complement_component_eq_range
      d hd r hcont hinj x.2 hxb
  let Cset := closure U
  let e : C(S, Cset) :=
    { toFun := fun z ↦ ⟨r z, frontier_subset_closure (by
          rw [hfront]
          exact ⟨z, rfl⟩)⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact hcont }
  let directionY : C(Cset, S) :=
    { toFun := fun w ↦ ⟨NormedSpace.normalize ((w : E) - (y : E)), by
          rw [mem_sphere_zero_iff_norm]
          apply NormedSpace.norm_normalize
          exact sub_ne_zero.mpr fun hwy ↦ hyNotClosure (hwy ▸ w.2)⟩
      continuous_toFun := by
        have hv : Continuous (fun w : Cset ↦ (w : E) - (y : E)) :=
          continuous_subtype_val.sub continuous_const
        apply Continuous.subtype_mk
        change Continuous (fun w : Cset ↦
          ‖(w : E) - (y : E)‖⁻¹ • ((w : E) - (y : E)))
        exact (hv.norm.inv₀ fun w ↦ norm_ne_zero_iff.mpr <|
          sub_ne_zero.mpr fun hwy ↦ hyNotClosure (hwy ▸ w.2)).smul hv }
  let gx := gaussMap d r hcont x
  let gy := gaussMap d r hcont y
  let G : C(Cset, S) := gx.comp directionY
  have hG (z : S) : G (e z) = (gx.comp gy) z := by
    change gx (directionY (e z)) = gx (gy z)
    congr 1
  obtain ⟨D, hD⟩ := exists_closure_extension_of_homotopic_sphere_maps
    d hd r hcont hinj U hfront (gy.comp gx) (gx.comp gy) G hG
      hcomm
  exact essential_comp_gaussMap_not_extend_bounded_component
    d hd r hcont hinj x hxb gy
      (gaussMap_not_nullhomotopic_of_isBounded d hd r hcont hinj y hyb)
      D (by
        intro z
        change D (e z) = gy (gx z)
        exact hD z)

/-- Commutativity, up to homotopy, of self-maps of the standard sphere
forces all bounded complementary components of an embedded sphere to
coincide. -/
theorem bounded_components_eq_of_sphereSelfMapsCommute
    (d : ℕ) (hd : 2 ≤ d) (hcomm : SphereSelfMapsCommute d)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) (hinj : Function.Injective r)
    (x y : ((Set.range r)ᶜ : Set (EuclideanSpace ℝ (Fin d))))
    (hxb : Bornology.IsBounded
      (connectedComponentIn (Set.range r)ᶜ
        (x : EuclideanSpace ℝ (Fin d))))
    (hyb : Bornology.IsBounded
      (connectedComponentIn (Set.range r)ᶜ
        (y : EuclideanSpace ℝ (Fin d)))) :
    connectedComponentIn (Set.range r)ᶜ
        (x : EuclideanSpace ℝ (Fin d)) =
      connectedComponentIn (Set.range r)ᶜ
        (y : EuclideanSpace ℝ (Fin d)) := by
  exact bounded_components_eq_of_gaussMap_comp_comm
    d hd r hcont hinj x y hxb hyb (hcomm _ _)

/-- The remaining sphere-map commutativity statement, together with the
already-proved existence of a bounded component, yields Jordan--Brouwer. -/
theorem jordan_brouwer_of_sphereSelfMapsCommute
    (d : ℕ) (hd : 2 ≤ d) (hcomm : SphereSelfMapsCommute d)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) (hinj : Function.Injective r) :
    Nat.card
        (ConnectedComponents ((Set.range r)ᶜ :
          Set (EuclideanSpace ℝ (Fin d)))) = 2 := by
  apply jordan_brouwer_of_bounded_component d hd r hcont
  · exact exists_bounded_sphere_complement_component d hd r hcont hinj
  · intro x hx y hy hxb hyb
    exact bounded_components_eq_of_sphereSelfMapsCommute d hd hcomm r hcont hinj
      ⟨x, hx⟩ ⟨y, hy⟩ hxb hyb

end

end Submission.Helpers
