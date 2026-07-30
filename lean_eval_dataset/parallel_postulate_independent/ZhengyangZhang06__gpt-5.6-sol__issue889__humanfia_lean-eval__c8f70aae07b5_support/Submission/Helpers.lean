import ChallengeDeps

namespace Submission.Helpers

open LeanEval.Geometry
open scoped Congruent EuclideanGeometry RealInnerProductSpace

noncomputable section

abbrev EPoint := EuclideanSpace ℝ (Fin 2)

def euclideanBetweenness (a b c : EPoint) : Prop :=
  Wbtw ℝ a b c

def euclideanCongruence (a b c d : EPoint) : Prop :=
  dist a b = dist c d

lemma euclideanCongruence_refl (a b : EPoint) :
    euclideanCongruence a b b a := by
  simp [euclideanCongruence, dist_comm]

lemma euclideanCongruence_trans (a b c d e f : EPoint)
    (hcd : euclideanCongruence a b c d)
    (hef : euclideanCongruence a b e f) :
    euclideanCongruence c d e f :=
  hcd.symm.trans hef

lemma euclideanCongruence_id (a b c : EPoint)
    (h : euclideanCongruence a b c c) : a = b := by
  simpa [euclideanCongruence] using h

lemma euclideanSegmentConstruction (a b c d : EPoint) :
    ∃ x, euclideanBetweenness a b x ∧ euclideanCongruence b x c d := by
  by_cases hab : a = b
  · subst b
    let e : EPoint := EuclideanSpace.single 0 1
    let x : EPoint := dist c d • e + a
    refine ⟨x, ?_, ?_⟩
    · exact wbtw_self_left ℝ a x
    · have he : ‖e‖ = 1 := by simp [e]
      simp [euclideanCongruence, x, dist_eq_norm, norm_smul, he]
  · have hab' : 0 < dist a b := dist_pos.mpr hab
    let t : ℝ := 1 + dist c d / dist a b
    let x : EPoint := AffineMap.lineMap a b t
    refine ⟨x, ?_, ?_⟩
    · rw [euclideanBetweenness, wbtw_iff_left_eq_or_right_mem_image_Ici]
      exact Or.inr ⟨t, by simp [t]; positivity, rfl⟩
    · change dist b x = dist c d
      dsimp [x]
      rw [dist_right_lineMap, Real.norm_eq_abs]
      have ht : 1 - t = -(dist c d / dist a b) := by simp [t]
      rw [ht, abs_neg, abs_of_nonneg (div_nonneg dist_nonneg hab'.le)]
      exact div_mul_cancel₀ _ hab'.ne'

lemma euclideanFiveSegment (a b c d a' b' c' d' : EPoint)
    (hab : a ≠ b)
    (habc : euclideanBetweenness a b c)
    (ha'b'c' : euclideanBetweenness a' b' c')
    (hAB : euclideanCongruence a b a' b')
    (hBC : euclideanCongruence b c b' c')
    (hAD : euclideanCongruence a d a' d')
    (hBD : euclideanCongruence b d b' d') :
    euclideanCongruence c d c' d' := by
  change dist a b = dist a' b' at hAB
  change dist b c = dist b' c' at hBC
  change dist a d = dist a' d' at hAD
  change dist b d = dist b' d' at hBD
  change dist c d = dist c' d'
  by_cases hcb : c = b
  · subst c
    have hc'b' : c' = b' := by
      exact (dist_eq_zero.mp (by simpa using hBC.symm)).symm
    subst c'
    exact hBD
  have ha'b' : a' ≠ b' := by
    intro h
    subst b'
    have : dist a b = 0 := by simpa using hAB
    exact hab (dist_eq_zero.mp this)
  have hc'b' : c' ≠ b' := by
    intro h
    subst c'
    have : dist b c = 0 := by simpa using hBC
    exact hcb (dist_eq_zero.mp this).symm
  have hs : Sbtw ℝ a b c :=
    ⟨habc, hab.symm, Ne.symm hcb⟩
  have hs' : Sbtw ℝ a' b' c' :=
    ⟨ha'b'c', ha'b'.symm, Ne.symm hc'b'⟩
  have hABD : ![a, b, d] ≅ ![a', b', d'] :=
    EuclideanGeometry.side_side_side hAB hBD (by simpa [dist_comm] using hAD)
  have hangleABD : ∠ a b d = ∠ a' b' d' := by
    exact EuclideanGeometry.angle_eq_of_congruent
      hABD (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
  have hsum : ∠ a b d + ∠ c b d = Real.pi := by
    simpa only [EuclideanGeometry.angle_comm] using
      EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi d hs.angle₁₂₃_eq_pi
  have hsum' : ∠ a' b' d' + ∠ c' b' d' = Real.pi := by
    simpa only [EuclideanGeometry.angle_comm] using
      EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi d' hs'.angle₁₂₃_eq_pi
  have hangleCBD : ∠ c b d = ∠ c' b' d' := by
    linarith
  have hCBD : ![c, b, d] ≅ ![c', b', d'] :=
    EuclideanGeometry.side_angle_side hangleCBD (by simpa [dist_comm] using hBC) hBD
  exact hCBD.dist_eq (0 : Fin 3) (2 : Fin 3)

lemma euclideanBetweenness_id (a b : EPoint)
    (h : euclideanBetweenness a b a) : a = b := by
  change Wbtw ℝ a b a at h
  exact ((wbtw_self_iff ℝ).mp h).symm

lemma euclideanInnerPasch (a b c p q : EPoint)
    (hapc : euclideanBetweenness a p c)
    (hbqc : euclideanBetweenness b q c) :
    ∃ x, euclideanBetweenness p x b ∧ euclideanBetweenness q x a := by
  rcases hapc with ⟨u, ⟨hu0, hu1⟩, rfl⟩
  rcases hbqc with ⟨v, ⟨hv0, hv1⟩, rfl⟩
  let D : ℝ := u + v - u * v
  have hD₁ : D = u * (1 - v) + v := by simp [D]; ring
  have hD₂ : D = v * (1 - u) + u := by simp [D]; ring
  have hD0 : 0 ≤ D := by
    rw [hD₁]
    positivity
  by_cases hDz : D = 0
  · have hv : v = 0 := by
      rw [hD₁] at hDz
      nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hv1)]
    have hu : u = 0 := by
      rw [hD₂, hv] at hDz
      simpa using hDz
    subst u
    subst v
    refine ⟨a, ?_, ?_⟩
    · simp [euclideanBetweenness]
    · simp [euclideanBetweenness]
  · have hDp : 0 < D := lt_of_le_of_ne hD0 (Ne.symm hDz)
    let r : ℝ := u * (1 - v) / D
    let s : ℝ := v * (1 - u) / D
    have hr0 : 0 ≤ r := by
      exact div_nonneg (mul_nonneg hu0 (sub_nonneg.mpr hv1)) hDp.le
    have hr1 : r ≤ 1 := by
      rw [div_le_one hDp]
      rw [hD₁]
      linarith
    have hs0 : 0 ≤ s := by
      exact div_nonneg (mul_nonneg hv0 (sub_nonneg.mpr hu1)) hDp.le
    have hs1 : s ≤ 1 := by
      rw [div_le_one hDp]
      rw [hD₂]
      linarith
    let x : EPoint :=
      AffineMap.lineMap (AffineMap.lineMap a c u) b r
    have hA : (1 - r) * (1 - u) = s := by
      change (1 - u * (1 - v) / D) * (1 - u) =
        v * (1 - u) / D
      field_simp [hDz]
      rw [hD₁]
      ring
    have hB : r = (1 - s) * (1 - v) := by
      change u * (1 - v) / D =
        (1 - v * (1 - u) / D) * (1 - v)
      field_simp [hDz]
      rw [hD₂]
      ring
    have hC : (1 - r) * u = (1 - s) * v := by
      change (1 - u * (1 - v) / D) * u =
        (1 - v * (1 - u) / D) * v
      field_simp [hDz]
      ring
    have hx :
        x = AffineMap.lineMap (AffineMap.lineMap b c v) a s := by
      ext i
      simp [x, AffineMap.lineMap_apply]
      linear_combination (a i) * hA + (b i) * hB + (c i) * hC
    refine ⟨x, ?_, ?_⟩
    · exact ⟨r, ⟨hr0, hr1⟩, rfl⟩
    · exact ⟨s, ⟨hs0, hs1⟩, hx.symm⟩

lemma euclideanLowerDimension :
    ∃ a b c : EPoint,
      ¬ euclideanBetweenness a b c ∧
      ¬ euclideanBetweenness b c a ∧
      ¬ euclideanBetweenness c a b := by
  let o : EPoint := 0
  let x : EPoint := EuclideanSpace.single 0 1
  let y : EPoint := EuclideanSpace.single 1 1
  refine ⟨o, x, y, ?_, ?_, ?_⟩
  · rintro ⟨r, hr, h⟩
    have h0 := congrArg (fun p : EPoint => p 0) h
    norm_num [euclideanBetweenness, o, x, y, AffineMap.lineMap_apply] at h0
  · rintro ⟨r, hr, h⟩
    have h1 := congrArg (fun p : EPoint => p 1) h
    norm_num [euclideanBetweenness, o, x, y, AffineMap.lineMap_apply] at h1
  · rintro ⟨r, hr, h⟩
    have h0 := congrArg (fun p : EPoint => p 0) h
    have h1 := congrArg (fun p : EPoint => p 1) h
    norm_num [euclideanBetweenness, o, x, y, AffineMap.lineMap_apply] at h0 h1
    linarith

lemma euclideanUpperDimension (a b c p q : EPoint)
    (hpq : p ≠ q)
    (hpa : euclideanCongruence p a q a)
    (hpb : euclideanCongruence p b q b)
    (hpc : euclideanCongruence p c q c) :
    euclideanBetweenness a b c ∨
      euclideanBetweenness b c a ∨
      euclideanBetweenness c a b := by
  let S : AffineSubspace ℝ EPoint := AffineSubspace.perpBisector p q
  have ha : a ∈ S := by
    exact AffineSubspace.mem_perpBisector_iff_dist_eq'.2 hpa
  have hb : b ∈ S := by
    exact AffineSubspace.mem_perpBisector_iff_dist_eq'.2 hpb
  have hc : c ∈ S := by
    exact AffineSubspace.mem_perpBisector_iff_dist_eq'.2 hpc
  have hsubset : ({a, b, c} : Set EPoint) ⊆ S := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have hspan :
      vectorSpan ℝ ({a, b, c} : Set EPoint) ≤ S.direction := by
    rw [S.direction_eq_vectorSpan]
    exact vectorSpan_mono ℝ hsubset
  letI : Fact (Module.finrank ℝ EPoint = 1 + 1) := ⟨by simp⟩
  have hfin : Module.finrank ℝ S.direction = 1 := by
    dsimp [S]
    rw [AffineSubspace.direction_perpBisector]
    exact Submodule.finrank_orthogonal_span_singleton (vsub_ne_zero.mpr hpq.symm)
  have hcol : Collinear ℝ ({a, b, c} : Set EPoint) := by
    rw [collinear_iff_finrank_le_one]
    exact (Submodule.finrank_mono hspan).trans_eq hfin
  simpa [euclideanBetweenness] using hcol.wbtw_or_wbtw_or_wbtw

lemma euclideanContinuity (X Y : Set EPoint)
    (hcut :
      ∃ a, ∀ x ∈ X, ∀ y ∈ Y, euclideanBetweenness a x y) :
    ∃ b, ∀ x ∈ X, ∀ y ∈ Y, euclideanBetweenness x b y := by
  classical
  rcases hcut with ⟨a, ha⟩
  rcases X.eq_empty_or_nonempty with hX | hX
  · subst X
    exact ⟨a, by simp⟩
  rcases Y.eq_empty_or_nonempty with hY | hY
  · subst Y
    exact ⟨a, by simp⟩
  by_cases hXa : ∀ x ∈ X, x = a
  · refine ⟨a, ?_⟩
    intro x hx y hy
    rw [hXa x hx]
    exact wbtw_self_left ℝ a y
  push Not at hXa
  rcases hXa with ⟨x₀, hx₀, hx₀a⟩
  have hax₀ : a ≠ x₀ := hx₀a.symm
  let f : ℝ →ᵃ[ℝ] EPoint := AffineMap.lineMap a x₀
  have hf : Function.Injective f := AffineMap.lineMap_injective ℝ hax₀
  have hyRep : ∀ y : Y, ∃ r : ℝ, 1 ≤ r ∧ f r = y := by
    intro y
    have h := ha x₀ hx₀ y y.property
    rcases h.right_mem_image_Ici_of_left_ne hax₀ with ⟨r, hr, hry⟩
    exact ⟨r, hr, hry⟩
  let cy : Y → ℝ := fun y => Classical.choose (hyRep y)
  have hcy_ge (y : Y) : 1 ≤ cy y :=
    (Classical.choose_spec (hyRep y)).1
  have hcy_eq (y : Y) : f (cy y) = y :=
    (Classical.choose_spec (hyRep y)).2
  let y₀ : Y := ⟨Classical.choose hY, Classical.choose_spec hY⟩
  have hxRep : ∀ x : X, ∃ r : ℝ, 0 ≤ r ∧ f r = x := by
    intro x
    rcases ha x x.property y₀ y₀.property with ⟨t, ht, htx⟩
    refine ⟨t * cy y₀, mul_nonneg ht.1 (zero_le_one.trans (hcy_ge y₀)), ?_⟩
    calc
      f (t * cy y₀) =
          AffineMap.lineMap a (f (cy y₀)) t := by
            simp [f]
      _ = AffineMap.lineMap a y₀ t := by rw [hcy_eq]
      _ = x := htx
  let cx : X → ℝ := fun x => Classical.choose (hxRep x)
  have hcx_ge (x : X) : 0 ≤ cx x :=
    (Classical.choose_spec (hxRep x)).1
  have hcx_eq (x : X) : f (cx x) = x :=
    (Classical.choose_spec (hxRep x)).2
  have hbounds (x : X) (y : Y) : 0 ≤ cx x ∧ cx x ≤ cy y := by
    have h := ha x x.property y y.property
    have hf0 : f 0 = a := by simp [f]
    rw [← hf0, ← hcx_eq x, ← hcy_eq y] at h
    have hs : Wbtw ℝ (0 : ℝ) (cx x) (cy y) :=
      hf.wbtw_map_iff.mp h
    exact (wbtw_iff_of_le (zero_le_one.trans (hcy_ge y))).mp hs
  let A : Set ℝ := Set.range cx
  have hAne : A.Nonempty := by
    let x₀X : X := ⟨x₀, hx₀⟩
    refine ⟨cx x₀X, ?_⟩
    exact Set.mem_range_self x₀X
  have hAbdd : BddAbove A := by
    refine ⟨cy y₀, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (hbounds x y₀).2
  let s : ℝ := sSup A
  refine ⟨f s, ?_⟩
  intro x hx y hy
  let xs : X := ⟨x, hx⟩
  let ys : Y := ⟨y, hy⟩
  have hxs : cx xs ≤ s :=
    le_csSup hAbdd (Set.mem_range_self xs)
  have hsy : s ≤ cy ys := by
    apply csSup_le hAne
    rintro _ ⟨z, rfl⟩
    exact (hbounds z ys).2
  have hs : Wbtw ℝ (cx xs) s (cy ys) :=
    Wbtw.of_le_of_le hxs hsy
  have hmapped := hs.map f
  rw [hcx_eq xs, hcy_eq ys] at hmapped
  exact hmapped

lemma euclideanParallelAxiom :
    ∀ a b c d t : EPoint,
      euclideanBetweenness a d t →
      euclideanBetweenness b d c →
      a ≠ d →
      ∃ x y : EPoint,
        euclideanBetweenness a b x ∧
        euclideanBetweenness a c y ∧
        euclideanBetweenness x t y := by
  intro a b c d t hadt hbdc had
  rcases hadt with ⟨u, ⟨hu0, hu1⟩, hud⟩
  rcases hbdc with ⟨v, hv, hvd⟩
  have hu : u ≠ 0 := by
    intro h
    subst u
    simp at hud
    exact had hud
  have hup : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
  let r : ℝ := 1 / u
  have hr : 1 ≤ r := by
    dsimp [r]
    rw [le_div_iff₀ hup]
    simpa using hu1
  let x : EPoint := AffineMap.lineMap a b r
  let y : EPoint := AffineMap.lineMap a c r
  have hxty : AffineMap.lineMap x y v = t := by
    ext i
    have hd :=
      congrArg (fun z : EPoint => z i) (hud.trans hvd.symm)
    simp [x, y, r, AffineMap.lineMap_apply] at hd ⊢
    field_simp [hu]
    linear_combination -hd
  refine ⟨x, y, ?_, ?_, ?_⟩
  · rw [euclideanBetweenness, wbtw_iff_left_eq_or_right_mem_image_Ici]
    exact Or.inr ⟨r, hr, rfl⟩
  · rw [euclideanBetweenness, wbtw_iff_left_eq_or_right_mem_image_Ici]
    exact Or.inr ⟨r, hr, rfl⟩
  · exact ⟨v, hv, hxty⟩

@[reducible] def euclideanTarski : TarskiAbsolute EPoint where
  B := euclideanBetweenness
  C := euclideanCongruence
  congr_refl := euclideanCongruence_refl
  congr_trans := euclideanCongruence_trans
  congr_id := euclideanCongruence_id
  segment_construction := euclideanSegmentConstruction
  five_segment := euclideanFiveSegment
  betw_id := euclideanBetweenness_id
  inner_pasch := euclideanInnerPasch
  lower_dim := euclideanLowerDimension
  upper_dim := euclideanUpperDimension
  continuity := euclideanContinuity

lemma euclideanTarski_isEuclidean :
    Euclidean EPoint euclideanTarski :=
  euclideanParallelAxiom

end

end Submission.Helpers
