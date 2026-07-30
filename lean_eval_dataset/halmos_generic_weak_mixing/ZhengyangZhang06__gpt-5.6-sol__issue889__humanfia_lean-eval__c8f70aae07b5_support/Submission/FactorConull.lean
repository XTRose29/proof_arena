import Submission.FiniteFactor

open MeasureTheory

namespace Submission.FiniteFactor

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace Z] [StandardBorelSpace X] [StandardBorelSpace Y]
  [MeasurableSingletonClass Z]

section

variable (m : Measure X) (n : Measure Y)
  [IsFiniteMeasure m] [IsFiniteMeasure n] [NoAtoms m] [NoAtoms n]
  (f : X → Z) (g : Y → Z) (hf : Measurable f) (hg : Measurable g)
  (hLaw : ∀ z, m (fiber f z) = n (fiber g z))

noncomputable def sourceEmbedding : SourceSpace m n f g hf hg hLaw → X :=
  fun a ↦ ((a.2.1 : fiber f a.1) : X)

noncomputable def targetEmbedding : TargetSpace m n f g hf hg hLaw → Y :=
  fun a ↦ ((a.2.1 : fiber g a.1) : Y)

theorem measurable_sourceEmbedding :
    Measurable (sourceEmbedding m n f g hf hg hLaw) := by
  apply measurable_sigma
  intro i
  exact measurable_subtype_coe.comp measurable_subtype_coe

theorem measurable_targetEmbedding :
    Measurable (targetEmbedding m n f g hf hg hLaw) := by
  apply measurable_sigma
  intro i
  exact measurable_subtype_coe.comp measurable_subtype_coe

theorem sourceEmbedding_label (a : SourceSpace m n f g hf hg hLaw) :
    f (sourceEmbedding m n f g hf hg hLaw a) = a.1 :=
  a.2.1.property

theorem targetEmbedding_label (a : TargetSpace m n f g hf hg hLaw) :
    g (targetEmbedding m n f g hf hg hLaw a) = a.1 :=
  a.2.1.property

theorem injective_sourceEmbedding :
    Function.Injective (sourceEmbedding m n f g hf hg hLaw) := by
  rintro ⟨i, x⟩ ⟨j, y⟩ hxy
  have hij0 : (i : Z) = j := by
    rw [← sourceEmbedding_label m n f g hf hg hLaw ⟨i, x⟩,
      ← sourceEmbedding_label m n f g hf hg hLaw ⟨j, y⟩]
    exact congrArg f hxy
  have hij : i = j := Subtype.ext hij0
  subst j
  congr
  apply Subtype.ext
  apply Subtype.ext
  exact hxy

theorem injective_targetEmbedding :
    Function.Injective (targetEmbedding m n f g hf hg hLaw) := by
  rintro ⟨i, x⟩ ⟨j, y⟩ hxy
  have hij0 : (i : Z) = j := by
    rw [← targetEmbedding_label m n f g hf hg hLaw ⟨i, x⟩,
      ← targetEmbedding_label m n f g hf hg hLaw ⟨j, y⟩]
    exact congrArg g hxy
  have hij : i = j := Subtype.ext hij0
  subst j
  congr
  apply Subtype.ext
  apply Subtype.ext
  exact hxy

theorem map_sourcePiece (i : support m f) :
    (sourcePieceMeasure m n f g hf hg hLaw i).map
        (fun x ↦ ((x.1 : fiber f i) : X)) =
      m.restrict (fiber f i) := by
  let d := pieceData m n f g hf hg hLaw i
  let D : Set (fiber f i) := d.source
  have hD : MeasurableSet D := d.measurableSource
  have hDfull : fiberMeasure m f i Dᶜ = 0 := d.sourceFull
  calc
    (sourcePieceMeasure m n f g hf hg hLaw i).map
          (fun x ↦ ((x.1 : fiber f i) : X)) =
        ((sourcePieceMeasure m n f g hf hg hLaw i).map
          ((↑) : D → fiber f i)).map ((↑) : fiber f i → X) := by
            rw [Measure.map_map measurable_subtype_coe measurable_subtype_coe]
            rfl
    _ = (fiberMeasure m f i).map ((↑) : fiber f i → X) := by
      rw [show sourcePieceMeasure m n f g hf hg hLaw i =
          Measure.comap ((↑) : D → fiber f i) (fiberMeasure m f i) from rfl,
        map_comap_subtype_coe hD,
        Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.mpr hDfull)]
    _ = m.restrict (fiber f i) := by
      unfold fiberMeasure
      exact map_comap_subtype_coe (measurableSet_fiber hf i) m

theorem map_targetPiece (i : support m f) :
    (targetPieceMeasure m n f g hf hg hLaw i).map
        (fun y ↦ ((y.1 : fiber g i) : Y)) =
      n.restrict (fiber g i) := by
  let d := pieceData m n f g hf hg hLaw i
  let D : Set (fiber g i) := d.target
  have hD : MeasurableSet D := d.measurableTarget
  have hDfull : fiberMeasure n g i Dᶜ = 0 := d.targetFull
  calc
    (targetPieceMeasure m n f g hf hg hLaw i).map
          (fun y ↦ ((y.1 : fiber g i) : Y)) =
        ((targetPieceMeasure m n f g hf hg hLaw i).map
          ((↑) : D → fiber g i)).map ((↑) : fiber g i → Y) := by
            rw [Measure.map_map measurable_subtype_coe measurable_subtype_coe]
            rfl
    _ = (fiberMeasure n g i).map ((↑) : fiber g i → Y) := by
      rw [show targetPieceMeasure m n f g hf hg hLaw i =
          Measure.comap ((↑) : D → fiber g i) (fiberMeasure n g i) from rfl,
        map_comap_subtype_coe hD,
        Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.mpr hDfull)]
    _ = n.restrict (fiber g i) := by
      unfold fiberMeasure
      exact map_comap_subtype_coe (measurableSet_fiber hg i) n

section Global

variable [Fintype Z]

theorem sourceMeasurableEmbedding :
    MeasurableEmbedding (sourceEmbedding m n f g hf hg hLaw) where
  injective := injective_sourceEmbedding m n f g hf hg hLaw
  measurable := measurable_sourceEmbedding m n f g hf hg hLaw
  measurableSet_image' := by
    intro s hs
    rw [show sourceEmbedding m n f g hf hg hLaw '' s =
        ⋃ i, (fun x : SourcePiece m n f g hf hg hLaw i ↦
          ((x.1 : fiber f i) : X)) ''
            ((fun x : SourcePiece m n f g hf hg hLaw i ↦
              (⟨i, x⟩ : SourceSpace m n f g hf hg hLaw)) ⁻¹' s) by
      ext x
      simp [sourceEmbedding]]
    apply MeasurableSet.iUnion
    intro i
    have hs_i : MeasurableSet
        ((fun x : SourcePiece m n f g hf hg hLaw i ↦
          (⟨i, x⟩ : SourceSpace m n f g hf hg hLaw)) ⁻¹' s) :=
      (measurableSet_sigma_iff.mp hs) i
    have hinner : MeasurableSet
        (((↑) : SourcePiece m n f g hf hg hLaw i → fiber f i) ''
          ((fun x : SourcePiece m n f g hf hg hLaw i ↦
            (⟨i, x⟩ : SourceSpace m n f g hf hg hLaw)) ⁻¹' s)) :=
      (pieceData m n f g hf hg hLaw i).measurableSource.subtype_image hs_i
    simpa only [Set.image_image, Function.comp_def] using
      (measurableSet_fiber hf i).subtype_image hinner

theorem targetMeasurableEmbedding :
    MeasurableEmbedding (targetEmbedding m n f g hf hg hLaw) where
  injective := injective_targetEmbedding m n f g hf hg hLaw
  measurable := measurable_targetEmbedding m n f g hf hg hLaw
  measurableSet_image' := by
    intro s hs
    rw [show targetEmbedding m n f g hf hg hLaw '' s =
        ⋃ i, (fun y : TargetPiece m n f g hf hg hLaw i ↦
          ((y.1 : fiber g i) : Y)) ''
            ((fun y : TargetPiece m n f g hf hg hLaw i ↦
              (⟨i, y⟩ : TargetSpace m n f g hf hg hLaw)) ⁻¹' s) by
      ext y
      simp [targetEmbedding]]
    apply MeasurableSet.iUnion
    intro i
    have hs_i : MeasurableSet
        ((fun y : TargetPiece m n f g hf hg hLaw i ↦
          (⟨i, y⟩ : TargetSpace m n f g hf hg hLaw)) ⁻¹' s) :=
      (measurableSet_sigma_iff.mp hs) i
    have hinner : MeasurableSet
        (((↑) : TargetPiece m n f g hf hg hLaw i → fiber g i) ''
          ((fun y : TargetPiece m n f g hf hg hLaw i ↦
            (⟨i, y⟩ : TargetSpace m n f g hf hg hLaw)) ⁻¹' s)) :=
      (pieceData m n f g hf hg hLaw i).measurableTarget.subtype_image hs_i
    simpa only [Set.image_image, Function.comp_def] using
      (measurableSet_fiber hg i).subtype_image hinner

set_option linter.unusedSectionVars false in
theorem pairwise_disjoint_fiber :
    Pairwise (fun i j : support m f ↦
      Disjoint (fiber f (i : Z)) (fiber f (j : Z))) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hxi hxj
  apply hij
  apply Subtype.ext
  have hi : f x = (i : Z) := by simpa [fiber] using hxi
  have hj : f x = (j : Z) := by simpa [fiber] using hxj
  exact hi.symm.trans hj

theorem map_sourceEmbedding :
    (sourceMeasure m n f g hf hg hLaw).map
        (sourceEmbedding m n f g hf hg hLaw) = m := by
  unfold sourceMeasure
  rw [Measure.map_sum
    (measurable_sourceEmbedding m n f g hf hg hLaw).aemeasurable]
  calc
    Measure.sum (fun i ↦
        ((sourcePieceMeasure m n f g hf hg hLaw i).map (Sigma.mk i)).map
          (sourceEmbedding m n f g hf hg hLaw)) =
        Measure.sum (fun i : support m f ↦ m.restrict (fiber f i)) := by
      congr 1
      funext i
      rw [Measure.map_map (measurable_sourceEmbedding m n f g hf hg hLaw)
        (measurable_sigma_mk i)]
      exact map_sourcePiece m n f g hf hg hLaw i
    _ = m.restrict (⋃ i : support m f, fiber f i) :=
      (Measure.restrict_iUnion (pairwise_disjoint_fiber m f)
        (fun i ↦ measurableSet_fiber hf i)).symm
    _ = m := by
      apply Measure.restrict_eq_self_of_ae_mem
      change (⋃ i : support m f, fiber f i) ∈ ae m
      rw [mem_ae_iff]
      apply measure_mono_null
      · intro x hx
        have hnot : f x ∉ support m f := by
          intro hmem
          apply hx
          refine Set.mem_iUnion.2 ⟨⟨f x, hmem⟩, ?_⟩
          change f x = f x
          rfl
        show x ∈ ⋃ z : {z // z ∉ support m f}, fiber f (z : Z)
        refine Set.mem_iUnion.2
          ⟨(⟨f x, hnot⟩ : {z // z ∉ support m f}), ?_⟩
        change f x = f x
        rfl
      · apply measure_iUnion_null
        intro z
        have hz : ¬ 0 < m (fiber f (z : Z)) := z.property
        exact nonpos_iff_eq_zero.mp (not_lt.mp hz)

theorem map_targetEmbedding :
    (targetMeasure m n f g hf hg hLaw).map
        (targetEmbedding m n f g hf hg hLaw) = n := by
  unfold targetMeasure
  rw [Measure.map_sum
    (measurable_targetEmbedding m n f g hf hg hLaw).aemeasurable]
  calc
    Measure.sum (fun i ↦
        ((targetPieceMeasure m n f g hf hg hLaw i).map (Sigma.mk i)).map
          (targetEmbedding m n f g hf hg hLaw)) =
        Measure.sum (fun i : support m f ↦ n.restrict (fiber g i)) := by
      congr 1
      funext i
      rw [Measure.map_map (measurable_targetEmbedding m n f g hf hg hLaw)
        (measurable_sigma_mk i)]
      exact map_targetPiece m n f g hf hg hLaw i
    _ = n.restrict (⋃ i : support m f, fiber g i) := by
      rw [Measure.restrict_iUnion]
      · intro i j hij
        change Disjoint (fiber g (i : Z)) (fiber g (j : Z))
        rw [Set.disjoint_left]
        intro y hyi hyj
        apply hij
        have hi : g y = i := by simpa [fiber] using hyi
        have hj : g y = j := by simpa [fiber] using hyj
        exact Subtype.ext (hi.symm.trans hj)
      · intro i
        exact measurableSet_fiber hg i
    _ = n := by
      apply Measure.restrict_eq_self_of_ae_mem
      change (⋃ i : support m f, fiber g i) ∈ ae n
      rw [mem_ae_iff]
      apply measure_mono_null
      · intro y hy
        have hnot : g y ∉ support m f := by
          intro hmem
          apply hy
          refine Set.mem_iUnion.2 ⟨⟨g y, hmem⟩, ?_⟩
          change g y = g y
          rfl
        show y ∈ ⋃ z : {z // z ∉ support m f}, fiber g (z : Z)
        refine Set.mem_iUnion.2
          ⟨(⟨g y, hnot⟩ : {z // z ∉ support m f}), ?_⟩
        change g y = g y
        rfl
      · apply measure_iUnion_null
        intro z
        rw [← hLaw]
        have hz : ¬ 0 < m (fiber f (z : Z)) := z.property
        exact nonpos_iff_eq_zero.mp (not_lt.mp hz)

theorem sourceRangeFull :
    m (Set.range (sourceEmbedding m n f g hf hg hLaw))ᶜ = 0 := by
  let R := Set.range (sourceEmbedding m n f g hf hg hLaw)
  calc
    m Rᶜ = ((sourceMeasure m n f g hf hg hLaw).map
        (sourceEmbedding m n f g hf hg hLaw)) Rᶜ :=
      congrArg (fun q : Measure X ↦ q Rᶜ)
        (map_sourceEmbedding m n f g hf hg hLaw).symm
    _ = (sourceMeasure m n f g hf hg hLaw)
        (sourceEmbedding m n f g hf hg hLaw ⁻¹' Rᶜ) :=
      (sourceMeasurableEmbedding m n f g hf hg hLaw).map_apply _ _
    _ = 0 := by simp [R]

theorem targetRangeFull :
    n (Set.range (targetEmbedding m n f g hf hg hLaw))ᶜ = 0 := by
  let R := Set.range (targetEmbedding m n f g hf hg hLaw)
  calc
    n Rᶜ = ((targetMeasure m n f g hf hg hLaw).map
        (targetEmbedding m n f g hf hg hLaw)) Rᶜ :=
      congrArg (fun q : Measure Y ↦ q Rᶜ)
        (map_targetEmbedding m n f g hf hg hLaw).symm
    _ = (targetMeasure m n f g hf hg hLaw)
        (targetEmbedding m n f g hf hg hLaw ⁻¹' Rᶜ) :=
      (targetMeasurableEmbedding m n f g hf hg hLaw).map_apply _ _
    _ = 0 := by simp [R]

theorem measurePreserving_sourceEquivRange :
    MeasurePreserving
      (sourceMeasurableEmbedding m n f g hf hg hLaw).equivRange
      (sourceMeasure m n f g hf hg hLaw)
      (Measure.comap
        ((↑) : Set.range (sourceEmbedding m n f g hf hg hLaw) → X) m) := by
  let emb := sourceMeasurableEmbedding m n f g hf hg hLaw
  let μ := sourceMeasure m n f g hf hg hLaw
  refine ⟨emb.equivRange.measurable, ?_⟩
  have hfactor : μ.map (sourceEmbedding m n f g hf hg hLaw) =
      (μ.map emb.equivRange).map
        ((↑) : Set.range (sourceEmbedding m n f g hf hg hLaw) → X) := by
    calc
      μ.map (sourceEmbedding m n f g hf hg hLaw) =
          μ.map (((↑) : Set.range
            (sourceEmbedding m n f g hf hg hLaw) → X) ∘ emb.equivRange) := by
        congr 1
        funext a
        exact (congrArg Subtype.val (emb.equivRange_apply a)).symm
      _ = (μ.map emb.equivRange).map ((↑) :
          Set.range (sourceEmbedding m n f g hf hg hLaw) → X) :=
        (Measure.map_map measurable_subtype_coe emb.equivRange.measurable).symm
  calc
    μ.map emb.equivRange = Measure.comap
        ((↑) : Set.range (sourceEmbedding m n f g hf hg hLaw) → X)
        ((μ.map emb.equivRange).map ((↑) :
          Set.range (sourceEmbedding m n f g hf hg hLaw) → X)) :=
      ((MeasurableEmbedding.subtype_coe emb.measurableSet_range).comap_map _).symm
    _ = Measure.comap
        ((↑) : Set.range (sourceEmbedding m n f g hf hg hLaw) → X)
        (μ.map (sourceEmbedding m n f g hf hg hLaw)) :=
      congrArg (Measure.comap
        ((↑) : Set.range (sourceEmbedding m n f g hf hg hLaw) → X)) hfactor.symm
    _ = Measure.comap
        ((↑) : Set.range (sourceEmbedding m n f g hf hg hLaw) → X) m :=
      congrArg (Measure.comap
        ((↑) : Set.range (sourceEmbedding m n f g hf hg hLaw) → X))
        (map_sourceEmbedding m n f g hf hg hLaw)

theorem measurePreserving_targetEquivRange :
    MeasurePreserving
      (targetMeasurableEmbedding m n f g hf hg hLaw).equivRange
      (targetMeasure m n f g hf hg hLaw)
      (Measure.comap
        ((↑) : Set.range (targetEmbedding m n f g hf hg hLaw) → Y) n) := by
  let emb := targetMeasurableEmbedding m n f g hf hg hLaw
  let μ := targetMeasure m n f g hf hg hLaw
  refine ⟨emb.equivRange.measurable, ?_⟩
  have hfactor : μ.map (targetEmbedding m n f g hf hg hLaw) =
      (μ.map emb.equivRange).map
        ((↑) : Set.range (targetEmbedding m n f g hf hg hLaw) → Y) := by
    calc
      μ.map (targetEmbedding m n f g hf hg hLaw) =
          μ.map (((↑) : Set.range
            (targetEmbedding m n f g hf hg hLaw) → Y) ∘ emb.equivRange) := by
        congr 1
        funext a
        exact (congrArg Subtype.val (emb.equivRange_apply a)).symm
      _ = (μ.map emb.equivRange).map ((↑) :
          Set.range (targetEmbedding m n f g hf hg hLaw) → Y) :=
        (Measure.map_map measurable_subtype_coe emb.equivRange.measurable).symm
  calc
    μ.map emb.equivRange = Measure.comap
        ((↑) : Set.range (targetEmbedding m n f g hf hg hLaw) → Y)
        ((μ.map emb.equivRange).map ((↑) :
          Set.range (targetEmbedding m n f g hf hg hLaw) → Y)) :=
      ((MeasurableEmbedding.subtype_coe emb.measurableSet_range).comap_map _).symm
    _ = Measure.comap
        ((↑) : Set.range (targetEmbedding m n f g hf hg hLaw) → Y)
        (μ.map (targetEmbedding m n f g hf hg hLaw)) :=
      congrArg (Measure.comap
        ((↑) : Set.range (targetEmbedding m n f g hf hg hLaw) → Y)) hfactor.symm
    _ = Measure.comap
        ((↑) : Set.range (targetEmbedding m n f g hf hg hLaw) → Y) n :=
      congrArg (Measure.comap
        ((↑) : Set.range (targetEmbedding m n f g hf hg hLaw) → Y))
        (map_targetEmbedding m n f g hf hg hLaw)

noncomputable def rangeEquiv :
    Set.range (sourceEmbedding m n f g hf hg hLaw) ≃ᵐ
      Set.range (targetEmbedding m n f g hf hg hLaw) :=
  (sourceMeasurableEmbedding m n f g hf hg hLaw).equivRange.symm |>.trans
    ((factorEquiv m n f g hf hg hLaw).trans
      (targetMeasurableEmbedding m n f g hf hg hLaw).equivRange)

theorem rangeEquiv_label
    (x : Set.range (sourceEmbedding m n f g hf hg hLaw)) :
    g ((rangeEquiv m n f g hf hg hLaw x :
        Set.range (targetEmbedding m n f g hf hg hLaw)) : Y) =
      f (x : X) := by
  let es := sourceMeasurableEmbedding m n f g hf hg hLaw
  let et := targetMeasurableEmbedding m n f g hf hg hLaw
  let a := es.equivRange.symm x
  have hsource : sourceEmbedding m n f g hf hg hLaw a = (x : X) := by
    have h := congrArg Subtype.val (es.equivRange.apply_symm_apply x)
    simpa only [MeasurableEmbedding.equivRange_apply] using h
  have htarget :
      ((rangeEquiv m n f g hf hg hLaw x :
          Set.range (targetEmbedding m n f g hf hg hLaw)) : Y) =
        targetEmbedding m n f g hf hg hLaw
          (factorEquiv m n f g hf hg hLaw a) := by
    simp only [rangeEquiv, MeasurableEquiv.trans_apply,
      MeasurableEmbedding.equivRange_apply]
    rfl
  rw [htarget, targetEmbedding_label m n f g hf hg hLaw]
  change (a.1 : Z) = f (x : X)
  rw [← sourceEmbedding_label m n f g hf hg hLaw a, hsource]

noncomputable def conullEquivData : ConullEquiv.Data m n where
  source := Set.range (sourceEmbedding m n f g hf hg hLaw)
  target := Set.range (targetEmbedding m n f g hf hg hLaw)
  measurableSource :=
    (sourceMeasurableEmbedding m n f g hf hg hLaw).measurableSet_range
  measurableTarget :=
    (targetMeasurableEmbedding m n f g hf hg hLaw).measurableSet_range
  sourceFull := sourceRangeFull m n f g hf hg hLaw
  targetFull := targetRangeFull m n f g hf hg hLaw
  equiv := rangeEquiv m n f g hf hg hLaw
  measurePreserving :=
    ((measurePreserving_sourceEquivRange m n f g hf hg hLaw).symm
      (sourceMeasurableEmbedding m n f g hf hg hLaw).equivRange).trans
      (measurePreserving_factorEquiv m n f g hf hg hLaw) |>.trans
        (measurePreserving_targetEquivRange m n f g hf hg hLaw)

end Global

end

end Submission.FiniteFactor
