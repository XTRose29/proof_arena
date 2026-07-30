import Submission.ConullEquiv

open MeasureTheory

namespace Submission.FiniteFactor

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace Z]

def fiber (f : X → Z) (z : Z) : Set X := f ⁻¹' {z}

theorem measurableSet_fiber [MeasurableSingletonClass Z] {f : X → Z}
    (hf : Measurable f) (z : Z) : MeasurableSet (fiber f z) :=
  hf (MeasurableSet.singleton z)

noncomputable def fiberMeasure (m : Measure X) (f : X → Z) (z : Z) :
    Measure (fiber f z) :=
  Measure.comap ((↑) : fiber f z → X) m

def support (m : Measure X) (f : X → Z) : Set Z :=
  {z | 0 < m (fiber f z)}

theorem measurableSet_sigma_iff {ι : Type*} {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] {s : Set (Sigma α)} :
    MeasurableSet s ↔ ∀ i, MeasurableSet (Sigma.mk i ⁻¹' s) := by
  change MeasurableSet[⨅ i, (inferInstance : MeasurableSpace (α i)).map
    (Sigma.mk i)] s ↔ _
  rw [MeasurableSpace.measurableSet_iInf]
  rfl

theorem measurable_sigma_mk {ι : Type*} {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] (i : ι) :
    Measurable (Sigma.mk i : α i → Sigma α) := by
  apply Measurable.of_le_map
  exact iInf_le _ i

theorem measurable_sigma {ι : Type*} {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] {W : Type*} [MeasurableSpace W]
    {F : Sigma α → W} (hF : ∀ i, Measurable (fun x ↦ F ⟨i, x⟩)) :
    Measurable F := by
  intro s hs
  rw [measurableSet_sigma_iff]
  exact fun i ↦ hF i hs

def sigmaCongrRight {ι : Type*} {α β : ι → Type*}
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSpace (β i)]
    (e : ∀ i, α i ≃ᵐ β i) : Sigma α ≃ᵐ Sigma β where
  toEquiv := Equiv.sigmaCongrRight fun i ↦ (e i).toEquiv
  measurable_toFun := measurable_sigma fun i ↦
    (measurable_sigma_mk i).comp (e i).measurable
  measurable_invFun := measurable_sigma fun i ↦
    (measurable_sigma_mk i).comp (e i).symm.measurable

section Pieces

variable [StandardBorelSpace X] [StandardBorelSpace Y]
  [Fintype Z] [MeasurableSingletonClass Z]

noncomputable def pieceData (m : Measure X) (n : Measure Y)
    [IsFiniteMeasure m] [IsFiniteMeasure n] [NoAtoms m] [NoAtoms n]
    (f : X → Z) (g : Y → Z) (hf : Measurable f) (hg : Measurable g)
    (hLaw : ∀ z, m (fiber f z) = n (fiber g z)) (i : support m f) :
    ConullEquiv.Data (fiberMeasure m f i) (fiberMeasure n g i) := by
  let FX := fiber f (i : Z)
  let FY := fiber g (i : Z)
  have hFX : MeasurableSet FX := measurableSet_fiber hf i
  have hFY : MeasurableSet FY := measurableSet_fiber hg i
  letI : StandardBorelSpace FX := hFX.standardBorel
  letI : StandardBorelSpace FY := hFY.standardBorel
  letI : IsFiniteMeasure (fiberMeasure m f i) := by
    unfold fiberMeasure
    infer_instance
  letI : IsFiniteMeasure (fiberMeasure n g i) := by
    unfold fiberMeasure
    infer_instance
  letI : NoAtoms (fiberMeasure m f i) := ⟨fun x ↦ by
    unfold fiberMeasure
    rw [comap_subtype_coe_apply hFX m]
    simpa only [Set.image_singleton] using measure_singleton (μ := m) (x : X)⟩
  letI : NoAtoms (fiberMeasure n g i) := ⟨fun y ↦ by
    unfold fiberMeasure
    rw [comap_subtype_coe_apply hFY n]
    simpa only [Set.image_singleton] using measure_singleton (μ := n) (y : Y)⟩
  have hmassX : fiberMeasure m f i Set.univ = m (fiber f i) := by
    unfold fiberMeasure
    rw [comap_subtype_coe_apply hFX m]
    simp [FX]
  have hmassY : fiberMeasure n g i Set.univ = n (fiber g i) := by
    unfold fiberMeasure
    rw [comap_subtype_coe_apply hFY n]
    simp [FY]
  have hmass : fiberMeasure m f i Set.univ =
      fiberMeasure n g i Set.univ := by
    rw [hmassX, hmassY, hLaw]
  have hpos : 0 < fiberMeasure m f i Set.univ := by
    rw [hmassX]
    exact i.property
  exact Classical.choice
    (ConullEquiv.exists_data_of_mass_eq
      (fiberMeasure m f i) (fiberMeasure n g i) hmass hpos)

abbrev SourcePiece (m : Measure X) (n : Measure Y)
    [IsFiniteMeasure m] [IsFiniteMeasure n] [NoAtoms m] [NoAtoms n]
    (f : X → Z) (g : Y → Z) (hf : Measurable f) (hg : Measurable g)
    (hLaw : ∀ z, m (fiber f z) = n (fiber g z)) (i : support m f) :=
  (pieceData m n f g hf hg hLaw i).source

abbrev TargetPiece (m : Measure X) (n : Measure Y)
    [IsFiniteMeasure m] [IsFiniteMeasure n] [NoAtoms m] [NoAtoms n]
    (f : X → Z) (g : Y → Z) (hf : Measurable f) (hg : Measurable g)
    (hLaw : ∀ z, m (fiber f z) = n (fiber g z)) (i : support m f) :=
  (pieceData m n f g hf hg hLaw i).target

abbrev SourceSpace (m : Measure X) (n : Measure Y)
    [IsFiniteMeasure m] [IsFiniteMeasure n] [NoAtoms m] [NoAtoms n]
    (f : X → Z) (g : Y → Z) (hf : Measurable f) (hg : Measurable g)
    (hLaw : ∀ z, m (fiber f z) = n (fiber g z)) :=
  Σ i : support m f, SourcePiece m n f g hf hg hLaw i

abbrev TargetSpace (m : Measure X) (n : Measure Y)
    [IsFiniteMeasure m] [IsFiniteMeasure n] [NoAtoms m] [NoAtoms n]
    (f : X → Z) (g : Y → Z) (hf : Measurable f) (hg : Measurable g)
    (hLaw : ∀ z, m (fiber f z) = n (fiber g z)) :=
  Σ i : support m f, TargetPiece m n f g hf hg hLaw i

noncomputable def pieceEquiv (m : Measure X) (n : Measure Y)
    [IsFiniteMeasure m] [IsFiniteMeasure n] [NoAtoms m] [NoAtoms n]
    (f : X → Z) (g : Y → Z) (hf : Measurable f) (hg : Measurable g)
    (hLaw : ∀ z, m (fiber f z) = n (fiber g z)) (i : support m f) :
    SourcePiece m n f g hf hg hLaw i ≃ᵐ
      TargetPiece m n f g hf hg hLaw i :=
  (pieceData m n f g hf hg hLaw i).equiv

noncomputable def factorEquiv (m : Measure X) (n : Measure Y)
    [IsFiniteMeasure m] [IsFiniteMeasure n] [NoAtoms m] [NoAtoms n]
    (f : X → Z) (g : Y → Z) (hf : Measurable f) (hg : Measurable g)
    (hLaw : ∀ z, m (fiber f z) = n (fiber g z)) :
    SourceSpace m n f g hf hg hLaw ≃ᵐ TargetSpace m n f g hf hg hLaw :=
  sigmaCongrRight fun i ↦ pieceEquiv m n f g hf hg hLaw i

noncomputable def sourcePieceMeasure (m : Measure X) (n : Measure Y)
    [IsFiniteMeasure m] [IsFiniteMeasure n] [NoAtoms m] [NoAtoms n]
    (f : X → Z) (g : Y → Z) (hf : Measurable f) (hg : Measurable g)
    (hLaw : ∀ z, m (fiber f z) = n (fiber g z)) (i : support m f) :
    Measure (SourcePiece m n f g hf hg hLaw i) :=
  Measure.comap
    ((↑) : SourcePiece m n f g hf hg hLaw i → fiber f i)
    (fiberMeasure m f i)

noncomputable def targetPieceMeasure (m : Measure X) (n : Measure Y)
    [IsFiniteMeasure m] [IsFiniteMeasure n] [NoAtoms m] [NoAtoms n]
    (f : X → Z) (g : Y → Z) (hf : Measurable f) (hg : Measurable g)
    (hLaw : ∀ z, m (fiber f z) = n (fiber g z)) (i : support m f) :
    Measure (TargetPiece m n f g hf hg hLaw i) :=
  Measure.comap
    ((↑) : TargetPiece m n f g hf hg hLaw i → fiber g i)
    (fiberMeasure n g i)

noncomputable def sourceMeasure (m : Measure X) (n : Measure Y)
    [IsFiniteMeasure m] [IsFiniteMeasure n] [NoAtoms m] [NoAtoms n]
    (f : X → Z) (g : Y → Z) (hf : Measurable f) (hg : Measurable g)
    (hLaw : ∀ z, m (fiber f z) = n (fiber g z)) :
    Measure (SourceSpace m n f g hf hg hLaw) :=
  Measure.sum fun i =>
    (sourcePieceMeasure m n f g hf hg hLaw i).map (Sigma.mk i)

noncomputable def targetMeasure (m : Measure X) (n : Measure Y)
    [IsFiniteMeasure m] [IsFiniteMeasure n] [NoAtoms m] [NoAtoms n]
    (f : X → Z) (g : Y → Z) (hf : Measurable f) (hg : Measurable g)
    (hLaw : ∀ z, m (fiber f z) = n (fiber g z)) :
    Measure (TargetSpace m n f g hf hg hLaw) :=
  Measure.sum fun i =>
    (targetPieceMeasure m n f g hf hg hLaw i).map (Sigma.mk i)

set_option linter.unusedSectionVars false in
theorem measurePreserving_pieceEquiv (m : Measure X) (n : Measure Y)
    [IsFiniteMeasure m] [IsFiniteMeasure n] [NoAtoms m] [NoAtoms n]
    (f : X → Z) (g : Y → Z) (hf : Measurable f) (hg : Measurable g)
    (hLaw : ∀ z, m (fiber f z) = n (fiber g z)) (i : support m f) :
    MeasurePreserving (pieceEquiv m n f g hf hg hLaw i)
      (sourcePieceMeasure m n f g hf hg hLaw i)
      (targetPieceMeasure m n f g hf hg hLaw i) :=
  (pieceData m n f g hf hg hLaw i).measurePreserving

theorem measurePreserving_factorEquiv (m : Measure X) (n : Measure Y)
    [IsFiniteMeasure m] [IsFiniteMeasure n] [NoAtoms m] [NoAtoms n]
    (f : X → Z) (g : Y → Z) (hf : Measurable f) (hg : Measurable g)
    (hLaw : ∀ z, m (fiber f z) = n (fiber g z)) :
    MeasurePreserving (factorEquiv m n f g hf hg hLaw)
      (sourceMeasure m n f g hf hg hLaw)
      (targetMeasure m n f g hf hg hLaw) := by
  let e := factorEquiv m n f g hf hg hLaw
  refine ⟨e.measurable, ?_⟩
  unfold sourceMeasure targetMeasure
  rw [Measure.map_sum e.measurable.aemeasurable]
  congr 1
  funext i
  let ei := pieceEquiv m n f g hf hg hLaw i
  let mi := sourcePieceMeasure m n f g hf hg hLaw i
  let ni := targetPieceMeasure m n f g hf hg hLaw i
  calc
    (mi.map (Sigma.mk i)).map e = mi.map (e ∘ Sigma.mk i) :=
      Measure.map_map e.measurable (measurable_sigma_mk i)
    _ = mi.map (Sigma.mk i ∘ ei) := by rfl
    _ = (mi.map ei).map (Sigma.mk i) :=
      (Measure.map_map (measurable_sigma_mk i) ei.measurable).symm
    _ = ni.map (Sigma.mk i) := by
      exact congrArg
        (fun q : Measure (TargetPiece m n f g hf hg hLaw i) ↦
          q.map (fun x : TargetPiece m n f g hf hg hLaw i ↦
            (⟨i, x⟩ : TargetSpace m n f g hf hg hLaw)))
        (measurePreserving_pieceEquiv m n f g hf hg hLaw i).map_eq

end Pieces

end Submission.FiniteFactor
