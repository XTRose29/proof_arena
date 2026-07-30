import Submission.BoundedGauss
import Submission.Neighborhood
import Submission.ProperSubset

namespace Submission.Helpers

open Set

noncomputable section

/-- A convex combination of two unit vectors which are not antipodal cannot
vanish.  This elementary observation is used to splice two sphere-valued
maps in a neighborhood of the embedded sphere. -/
theorem convexCombination_ne_zero_of_norm_eq_one_of_dist_lt_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : dist a b < 2)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) • a + t • b ≠ 0 := by
  intro hzero
  have hscaled : (1 - t) • a = -(t • b) := by
    exact eq_neg_of_add_eq_zero_left hzero
  have hcoeff : 1 - t = t := by
    have hnorm := congrArg norm hscaled
    rw [norm_smul, norm_neg, norm_smul, ha, hb, mul_one, mul_one,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht1),
      abs_of_nonneg ht0] at hnorm
    exact hnorm
  have ht : t = 1 / 2 := by linarith
  have habneg : a = -b := by
    rw [ht] at hzero
    have hhalf : (1 - (1 / 2 : ℝ)) = 1 / 2 := by norm_num
    rw [hhalf, ← smul_add] at hzero
    exact add_eq_zero_iff_eq_neg.mp (smul_eq_zero.mp hzero |>.resolve_left (by norm_num))
  have hd : dist a b = 2 := by
    rw [habneg, dist_eq_norm]
    rw [show -b - b = (-2 : ℝ) • b by module, norm_smul,
      Real.norm_eq_abs, abs_of_nonpos (by norm_num), hb]
    norm_num
  exact (lt_irrefl 2) (hd ▸ hab)

/-- Homotopic Gauss maps based in bounded complementary components detect the
same component.  A homotopy between the boundary maps is spliced, using the
neighborhood retraction of the embedded sphere, to the direction map based at
the second point.  If the points belonged to different components this would
give a zero-free extension of the first Gauss map across the closure of its
bounded component, contradicting the Brouwer obstruction. -/
theorem bounded_components_eq_of_gaussMap_homotopic
    (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) (hinj : Function.Injective r)
    (x y : ((Set.range r)ᶜ : Set (EuclideanSpace ℝ (Fin d))))
    (hxb : Bornology.IsBounded
      (connectedComponentIn (Set.range r)ᶜ
        (x : EuclideanSpace ℝ (Fin d))))
    (hhom : ContinuousMap.Homotopic (gaussMap d r hcont x)
      (gaussMap d r hcont y)) :
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
  have hfront : frontier U = Set.range r := by
    exact frontier_bounded_sphere_complement_component_eq_range
      d hd r hcont hinj x.2 hxb
  let C := closure U
  let e : C(S, C) :=
    { toFun := fun z ↦ ⟨r z, frontier_subset_closure (by
          rw [hfront]
          exact ⟨z, rfl⟩)⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact hcont }
  have heCompact : IsCompact (Set.range e) := isCompact_range e.continuous
  let directionY : C(C, S) :=
    { toFun := fun w ↦ ⟨NormedSpace.normalize ((w : E) - (y : E)), by
          rw [mem_sphere_zero_iff_norm]
          apply NormedSpace.norm_normalize
          exact sub_ne_zero.mpr fun hwy ↦ hyNotClosure (hwy ▸ w.2)⟩
      continuous_toFun := by
        have hv : Continuous (fun w : C ↦ (w : E) - (y : E)) :=
          continuous_subtype_val.sub continuous_const
        apply Continuous.subtype_mk
        change Continuous (fun w : C ↦
          ‖(w : E) - (y : E)‖⁻¹ • ((w : E) - (y : E)))
        exact (hv.norm.inv₀ fun w ↦
          norm_ne_zero_iff.mpr (sub_ne_zero.mpr fun hwy ↦
            hyNotClosure (hwy ▸ w.2))).smul hv }
  have hdirectionY (z : S) : directionY (e z) = gaussMap d r hcont y z := by
    rfl
  obtain ⟨W, hWOpen, hrW, ρ, hρ⟩ :=
    exists_open_neighborhood_retraction d hd r hcont hinj
  let WC : Set C := Subtype.val ⁻¹' W
  have hWCOpen : IsOpen WC := hWOpen.preimage continuous_subtype_val
  let ρC : C(WC, S) :=
    { toFun := fun w ↦ ρ ⟨(w : E), w.2⟩
      continuous_toFun := by
        apply ρ.continuous.comp
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp continuous_subtype_val }
  let goodW : Set WC := {w | dist
      (gaussMap d r hcont y (ρC w) : E) (directionY w.1 : E) < 2}
  have hgoodWOpen : IsOpen goodW := by
    exact isOpen_lt
      ((gaussMap d r hcont y).continuous.comp ρC.continuous |>.dist
        (directionY.continuous.comp continuous_subtype_val))
      continuous_const
  let good : Set C := ((↑) : WC → C) '' goodW
  have hgoodOpen : IsOpen good := by
    exact hWCOpen.isOpenMap_subtype_val goodW hgoodWOpen
  have heGood : Set.range e ⊆ good := by
    rintro _ ⟨z, rfl⟩
    have heW : (e z : E) ∈ W := hrW ⟨z, rfl⟩
    let w : WC := ⟨e z, heW⟩
    refine ⟨w, ?_, rfl⟩
    change dist (gaussMap d r hcont y (ρC w)) (directionY (e z)) < 2
    rw [show ρC w = z by exact hρ z, hdirectionY]
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
  let C₂ : Set C := closure O₂
  have hC₂Good : C₂ ⊆ good := hO₂Good
  have hgoodData (w : C) (hw : w ∈ good) :
      ∃ hwW : (w : E) ∈ W,
        dist (gaussMap d r hcont y
          (ρ ⟨(w : E), hwW⟩) : E) (directionY w : E) < 2 := by
    rcases hw with ⟨v, hv, rfl⟩
    change dist (gaussMap d r hcont y (ρC v) : E)
      (directionY v.1 : E) < 2 at hv
    refine ⟨v.2, ?_⟩
    have hrho : ρ ⟨((v : C) : E), v.2⟩ = ρC v := by
      apply congrArg ρ
      apply Subtype.ext
      rfl
    rw [hrho]
    exact hv
  have hC₂W (w : C₂) : ((w : C) : E) ∈ W :=
    (hgoodData w (hC₂Good w.2)).choose
  let liftC₂ : C(C₂, WC) :=
    { toFun := fun w ↦ ⟨w.1, hC₂W w⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val }
  let ρC₂ : C(C₂, S) := ρC.comp liftC₂
  let directionYC₂ : C(C₂, S) :=
    directionY.comp
      { toFun := fun w ↦ w.1
        continuous_toFun := continuous_subtype_val }
  obtain ⟨H⟩ := hhom
  let φI : C(C, unitInterval) :=
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
      ψ w.1 • (directionYC₂ w : E)
  have hrawContinuous : Continuous raw := by
    exact (continuous_const.sub (ψ.continuous.comp continuous_subtype_val)).smul
      (continuous_subtype_val.comp homotopyPart.continuous) |>.add
        ((ψ.continuous.comp continuous_subtype_val).smul
          (continuous_subtype_val.comp directionYC₂.continuous))
  have hrawNe (w : C₂) : raw w ≠ 0 := by
    by_cases hwO₀ : (w : C) ∈ O₀
    · have hψw : ψ w.1 = 0 := hψ0 (subset_closure hwO₀)
      change (1 - ψ w.1) • (homotopyPart w : E) +
          ψ w.1 • (directionYC₂ w : E) ≠ 0
      rw [hψw]
      have hnorm := mem_sphere_zero_iff_norm.mp (homotopyPart w).2
      simp only [sub_zero, one_smul, zero_smul, add_zero]
      intro hzero
      rw [hzero, norm_zero] at hnorm
      norm_num at hnorm
    · have hφw : φ w.1 = 1 := hφ1 hwO₀
      have hφIw : φI w.1 = 1 := Subtype.ext hφw
      have hhomPart : homotopyPart w =
          gaussMap d r hcont y (ρC₂ w) := by
        change H (φI w.1, ρC₂ w) = _
        rw [hφIw]
        exact H.map_one_left (ρC₂ w)
      have hclose : dist (gaussMap d r hcont y (ρC₂ w) : E)
          (directionYC₂ w : E) < 2 := by
        have hg := (hgoodData w.1 (hC₂Good w.2)).choose_spec
        change dist
          (gaussMap d r hcont y
            (ρ ⟨((w : C) : E), hC₂W w⟩) : E)
          (directionY w.1 : E) < 2
        simpa only [hC₂W] using hg
      apply convexCombination_ne_zero_of_norm_eq_one_of_dist_lt_two
        (mem_sphere_zero_iff_norm.mp (homotopyPart w).2)
        (mem_sphere_zero_iff_norm.mp (directionYC₂ w).2)
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
  have hinside_eq_directionY {w : C₂} (hw : (w : C) ∉ O₁) :
      inside w = directionY w.1 := by
    have hφw : φ w.1 = 1 := hφ1 (fun hwO₀ ↦ hw (hO₀O₁ (subset_closure hwO₀)))
    have hψw : ψ w.1 = 1 := hψ1 hw
    apply Subtype.ext
    change NormedSpace.normalize (raw w) = (directionY w.1 : E)
    have hφIw : φI w.1 = 1 := Subtype.ext hφw
    have hhomPart : homotopyPart w = gaussMap d r hcont y (ρC₂ w) := by
      change H (φI w.1, ρC₂ w) = _
      rw [hφIw]
      exact H.map_one_left (ρC₂ w)
    change NormedSpace.normalize
        ((1 - ψ w.1) • (homotopyPart w : E) +
          ψ w.1 • (directionYC₂ w : E)) = _
    rw [hψw]
    simp only [sub_self, zero_smul, one_smul, zero_add]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one
      (mem_sphere_zero_iff_norm.mp (directionYC₂ w).2)
  let directionX : C → S := fun w ↦
    if hw : w ∈ C₂ then inside ⟨w, hw⟩ else directionY w
  have hdirectionXContinuous : Continuous directionX := by
    have hclosedC₂ : IsClosed C₂ := isClosed_closure
    have hclosedO₁c : IsClosed O₁ᶜ := hO₁Open.isClosed_compl
    have hcover : C₂ ∪ O₁ᶜ = Set.univ := by
      apply Set.eq_univ_of_forall
      intro w
      by_cases hw : w ∈ O₁
      · exact Or.inl (subset_closure (hO₁O₂ (subset_closure hw)))
      · exact Or.inr hw
    have hcontC₂ : ContinuousOn directionX C₂ := by
      rw [continuousOn_iff_continuous_restrict]
      have heq : C₂.restrict directionX = fun w : C₂ ↦ inside w := by
        funext w
        simp only [Set.restrict, directionX, dif_pos w.2]
      rw [heq]
      exact inside.continuous
    have hcontO₁c : ContinuousOn directionX O₁ᶜ := by
      apply directionY.continuous.continuousOn.congr
      intro w hw
      by_cases hwC₂ : w ∈ C₂
      · rw [show directionX w = inside ⟨w, hwC₂⟩ by simp [directionX, hwC₂]]
        exact hinside_eq_directionY hw
      · simp [directionX, hwC₂]
    have hUnion : ContinuousOn directionX (C₂ ∪ O₁ᶜ) :=
      hcontC₂.union_of_isClosed hcontO₁c hclosedC₂ hclosedO₁c
    rw [hcover] at hUnion
    exact continuousOn_univ.mp hUnion
  let direction : C(C, S) := ⟨directionX, hdirectionXContinuous⟩
  have hdirection (z : S) : direction (e z) = gaussMap d r hcont x z := by
    have heC₂ : e z ∈ C₂ := subset_closure (heO₂ ⟨z, rfl⟩)
    have hφz : φ (e z) = 0 := hφ0 ⟨z, rfl⟩
    have hψz : ψ (e z) = 0 := hψ0 (subset_closure (heO₀ ⟨z, rfl⟩))
    change directionX (e z) = gaussMap d r hcont x z
    rw [show directionX (e z) = inside ⟨e z, heC₂⟩ by
      simp [directionX, heC₂]]
    apply Subtype.ext
    change NormedSpace.normalize (raw ⟨e z, heC₂⟩) = _
    have hρz : ρC₂ ⟨e z, heC₂⟩ = z := hρ z
    have hφIz : φI (e z) = 0 := Subtype.ext hφz
    change NormedSpace.normalize
        ((1 - ψ (e z)) •
            (H (φI (e z), ρC₂ ⟨e z, heC₂⟩) : E) +
          ψ (e z) • (directionY (e z) : E)) = _
    rw [hψz, hφIz, hρz]
    simp only [sub_zero, one_smul, zero_smul, add_zero]
    have hH0 : (H (0, z) : E) = (gaussMap d r hcont x z : E) :=
      congrArg Subtype.val (H.map_zero_left z)
    calc
      NormedSpace.normalize (H (0, z) : E) =
          NormedSpace.normalize (gaussMap d r hcont x z : E) :=
        congrArg NormedSpace.normalize hH0
      _ = (gaussMap d r hcont x z : E) :=
        NormedSpace.normalize_eq_self_of_norm_eq_one
          (mem_sphere_zero_iff_norm.mp (gaussMap d r hcont x z).2)
  let directionE : C(C, E) :=
    { toFun := fun w ↦ (direction w : E)
      continuous_toFun := continuous_subtype_val.comp direction.continuous }
  obtain ⟨D, hD⟩ :=
    directionE.exists_extension isClosed_closure.isClosedEmbedding_subtypeVal
  let logRadius : C(S, ℝ) :=
    { toFun := fun z ↦ Real.log ‖r z - (x : E)‖
      continuous_toFun := by
        apply Continuous.log
        · exact (hcont.sub continuous_const).norm
        · intro z
          exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr fun h ↦ x.2 ⟨z, h⟩) }
  obtain ⟨L, hL⟩ :=
    logRadius.exists_extension (sphere_isClosedEmbedding d r hcont hinj)
  let F : C(E, E) :=
    { toFun := fun w ↦ Real.exp (L w) • D w
      continuous_toFun := (Real.continuous_exp.comp L.continuous).smul D.continuous }
  apply no_zeroFree_extension_over_bounded_open d U hxb (x : E)
    (mem_connectedComponentIn x.2) F
  · intro w hw
    have hDw : D w = (direction ⟨w, hw⟩ : E) := by
      exact DFunLike.congr_fun hD ⟨w, hw⟩
    change Real.exp (L w) • D w ≠ 0
    rw [hDw]
    apply smul_ne_zero (Real.exp_ne_zero (L w))
    intro hzero
    have hnorm := mem_sphere_zero_iff_norm.mp (direction ⟨w, hw⟩).2
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  · intro w hw
    have hwRange : w ∈ Set.range r := hfront ▸ hw
    obtain ⟨z, rfl⟩ := hwRange
    have hDz : D (r z) = (direction (e z) : E) := by
      exact DFunLike.congr_fun hD (e z)
    have hLz : L (r z) = logRadius z := DFunLike.congr_fun hL z
    change Real.exp (L (r z)) • D (r z) = r z - (x : E)
    rw [hDz, hdirection, hLz]
    change Real.exp (Real.log ‖r z - (x : E)‖) •
        NormedSpace.normalize (r z - (x : E)) = r z - (x : E)
    rw [Real.exp_log (norm_pos_iff.mpr <|
      sub_ne_zero.mpr fun h ↦ x.2 ⟨z, h⟩)]
    exact NormedSpace.norm_smul_normalize _

/-- The Gauss homotopy class completely distinguishes complementary
components.  On bounded components this is the splicing obstruction above;
all unbounded points lie in the already-constructed exterior component. -/
theorem gaussClassMap_injective
    (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) (hinj : Function.Injective r) :
    Function.Injective (gaussClassMap d r hcont hinj) := by
  intro a b hab
  induction a using Quotient.inductionOn with
  | _ x =>
    induction b using Quotient.inductionOn with
    | _ y =>
      have hhom : ContinuousMap.Homotopic
          (gaussMap d r hcont x) (gaussMap d r hcont y) :=
        Quotient.exact hab
      apply Quotient.sound
      by_cases hxb : Bornology.IsBounded
          (connectedComponentIn (Set.range r)ᶜ
            (x : EuclideanSpace ℝ (Fin d)))
      · have hcomponents := bounded_components_eq_of_gaussMap_homotopic
          d hd r hcont hinj x y hxb hhom
        apply (Set.image_injective.mpr Subtype.val_injective)
        rw [← connectedComponentIn_eq_image x.2,
          ← connectedComponentIn_eq_image y.2]
        exact hcomponents
      · by_cases hyb : Bornology.IsBounded
            (connectedComponentIn (Set.range r)ᶜ
              (y : EuclideanSpace ℝ (Fin d)))
        · have hcomponents := bounded_components_eq_of_gaussMap_homotopic
            d hd r hcont hinj y x hyb hhom.symm
          apply (Set.image_injective.mpr Subtype.val_injective)
          rw [← connectedComponentIn_eq_image x.2,
            ← connectedComponentIn_eq_image y.2]
          exact hcomponents.symm
        · have hcomponents := connectedComponentIn_eq_of_not_isBounded
            d hd r hcont hxb hyb
          apply (Set.image_injective.mpr Subtype.val_injective)
          rw [← connectedComponentIn_eq_image x.2,
            ← connectedComponentIn_eq_image y.2]
          exact hcomponents

end

end Submission.Helpers
