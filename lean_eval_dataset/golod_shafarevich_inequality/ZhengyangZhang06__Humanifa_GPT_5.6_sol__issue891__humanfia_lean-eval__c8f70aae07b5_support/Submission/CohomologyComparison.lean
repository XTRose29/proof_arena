import ChallengeDeps

namespace Submission.CohomologyComparison

open CategoryTheory
open ContinuousCohomology

variable (p : ℕ) [Fact p.Prime] (G : Type) [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G]

noncomputable abbrev topRep : Action (TopModuleCat (ZMod p)) G :=
  LeanEval.GroupTheory.trivialZModpRep p G

noncomputable abbrev homogeneous : CochainComplex (TopModuleCat (ZMod p)) ℕ :=
  (homogeneousCochains (ZMod p) G).obj (topRep p G)

noncomputable abbrev ordinaryRep : Rep (ZMod p) G :=
  Rep.trivial (ZMod p) G (ZMod p)

noncomputable abbrev homogeneousTermOne : TopModuleCat (ZMod p) :=
  (invariants (ZMod p) G).obj (Iobj (Iobj (topRep p G)))

noncomputable abbrev homogeneousTermTwo : TopModuleCat (ZMod p) :=
  (invariants (ZMod p) G).obj (Iobj (Iobj (Iobj (topRep p G))))

noncomputable abbrev homogeneousTermThree : TopModuleCat (ZMod p) :=
  (invariants (ZMod p) G).obj (Iobj (Iobj (Iobj (Iobj (topRep p G)))))

noncomputable def evalOnePair :
    homogeneousTermOne p G →ₗ[ZMod p] (G → ZMod p) where
  toFun F g := F.1 1 g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def ofInhomogeneousOne :
    (G → ZMod p) →ₗ[ZMod p] homogeneousTermOne p G where
  toFun f := by
    refine ⟨⟨fun a ↦ ⟨fun b ↦ f (a⁻¹ * b), continuous_of_discreteTopology⟩,
      continuous_of_discreteTopology⟩, ?_⟩
    intro g
    apply ContinuousMap.ext
    intro a
    apply ContinuousMap.ext
    intro b
    change f ((g⁻¹ * a)⁻¹ * (g⁻¹ * b)) = f (a⁻¹ * b)
    apply congrArg f
    group
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def homogeneousOneEquiv :
    homogeneousTermOne p G ≃ₗ[ZMod p] (G → ZMod p) where
  toLinearMap := evalOnePair p G
  invFun := ofInhomogeneousOne p G
  left_inv F := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro a
    apply ContinuousMap.ext
    intro b
    dsimp only [ofInhomogeneousOne, evalOnePair, LinearMap.coe_mk, AddHom.coe_mk]
    simp only [ContinuousMap.coe_mk]
    change F.1 1 (a⁻¹ * b) = F.1 a b
    have h := F.2 a
    have h' := congrArg (fun x ↦ x a b) h
    change F.1 (a⁻¹ * a) (a⁻¹ * b) = F.1 a b at h'
    simpa only [inv_mul_cancel, inv_one, one_mul] using h'
  right_inv f := by
    ext g
    simp [evalOnePair, ofInhomogeneousOne]

noncomputable def evalOneTriple :
    homogeneousTermTwo p G →ₗ[ZMod p] (G × G → ZMod p) where
  toFun F gh := F.1 1 gh.1 (gh.1 * gh.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def ofInhomogeneousTwo :
    (G × G → ZMod p) →ₗ[ZMod p] homogeneousTermTwo p G where
  toFun f := by
    refine ⟨⟨fun a ↦ ⟨fun b ↦ ⟨fun c ↦ f (a⁻¹ * b, b⁻¹ * c),
      continuous_of_discreteTopology⟩, continuous_of_discreteTopology⟩,
      continuous_of_discreteTopology⟩, ?_⟩
    intro g
    apply ContinuousMap.ext
    intro a
    apply ContinuousMap.ext
    intro b
    apply ContinuousMap.ext
    intro c
    change f ((g⁻¹ * a)⁻¹ * (g⁻¹ * b), (g⁻¹ * b)⁻¹ * (g⁻¹ * c)) =
      f (a⁻¹ * b, b⁻¹ * c)
    apply congrArg f
    ext <;> group
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def homogeneousTwoEquiv :
    homogeneousTermTwo p G ≃ₗ[ZMod p] (G × G → ZMod p) where
  toLinearMap := evalOneTriple p G
  invFun := ofInhomogeneousTwo p G
  left_inv F := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro a
    apply ContinuousMap.ext
    intro b
    apply ContinuousMap.ext
    intro c
    change F.1 1 (a⁻¹ * b) ((a⁻¹ * b) * (b⁻¹ * c)) = F.1 a b c
    rw [show (a⁻¹ * b) * (b⁻¹ * c) = a⁻¹ * c by group]
    have h := F.2 a
    have h' := congrArg (fun x ↦ x a b c) h
    change F.1 (a⁻¹ * a) (a⁻¹ * b) (a⁻¹ * c) = F.1 a b c at h'
    simpa only [inv_mul_cancel] using h'
  right_inv f := by
    ext gh
    simp [evalOneTriple, ofInhomogeneousTwo]

noncomputable def evalOneQuadruple :
    homogeneousTermThree p G →ₗ[ZMod p] (G × G × G → ZMod p) where
  toFun F ghk := F.1 1 ghk.1 (ghk.1 * ghk.2.1)
    (ghk.1 * ghk.2.1 * ghk.2.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def ofInhomogeneousThree :
    (G × G × G → ZMod p) →ₗ[ZMod p] homogeneousTermThree p G where
  toFun f := by
    refine ⟨⟨fun a ↦ ⟨fun b ↦ ⟨fun c ↦ ⟨fun d ↦
      f (a⁻¹ * b, b⁻¹ * c, c⁻¹ * d), continuous_of_discreteTopology⟩,
      continuous_of_discreteTopology⟩, continuous_of_discreteTopology⟩,
      continuous_of_discreteTopology⟩, ?_⟩
    intro g
    apply ContinuousMap.ext
    intro a
    apply ContinuousMap.ext
    intro b
    apply ContinuousMap.ext
    intro c
    apply ContinuousMap.ext
    intro d
    change f ((g⁻¹ * a)⁻¹ * (g⁻¹ * b), (g⁻¹ * b)⁻¹ * (g⁻¹ * c),
      (g⁻¹ * c)⁻¹ * (g⁻¹ * d)) = f (a⁻¹ * b, b⁻¹ * c, c⁻¹ * d)
    apply congrArg f
    ext <;> group
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def homogeneousThreeEquiv :
    homogeneousTermThree p G ≃ₗ[ZMod p] (G × G × G → ZMod p) where
  toLinearMap := evalOneQuadruple p G
  invFun := ofInhomogeneousThree p G
  left_inv F := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro a
    apply ContinuousMap.ext
    intro b
    apply ContinuousMap.ext
    intro c
    apply ContinuousMap.ext
    intro d
    change F.1 1 (a⁻¹ * b) ((a⁻¹ * b) * (b⁻¹ * c))
      ((a⁻¹ * b) * (b⁻¹ * c) * (c⁻¹ * d)) = F.1 a b c d
    rw [show (a⁻¹ * b) * (b⁻¹ * c) = a⁻¹ * c by group,
      show a⁻¹ * c * (c⁻¹ * d) = a⁻¹ * d by group]
    have h := F.2 a
    have h' := congrArg (fun x ↦ x a b c d) h
    change F.1 (a⁻¹ * a) (a⁻¹ * b) (a⁻¹ * c) (a⁻¹ * d) = F.1 a b c d at h'
    simpa only [inv_mul_cancel] using h'
  right_inv f := by
    ext ghk
    rcases ghk with ⟨g, h, k⟩
    dsimp [evalOneQuadruple, ofInhomogeneousThree]
    apply congrArg f
    ext <;> group

noncomputable def termOneIso :
    (forget₂ (TopModuleCat (ZMod p)) (ModuleCat (ZMod p))).obj
        ((homogeneous p G).X 1) ≅ ModuleCat.of (ZMod p) (G → ZMod p) := by
  change ModuleCat.of (ZMod p) (homogeneousTermOne p G) ≅ _
  exact (homogeneousOneEquiv p G).toModuleIso

noncomputable def termTwoIso :
    (forget₂ (TopModuleCat (ZMod p)) (ModuleCat (ZMod p))).obj
        ((homogeneous p G).X 2) ≅ ModuleCat.of (ZMod p) (G × G → ZMod p) := by
  change ModuleCat.of (ZMod p) (homogeneousTermTwo p G) ≅ _
  exact (homogeneousTwoEquiv p G).toModuleIso

noncomputable def termThreeIso :
    (forget₂ (TopModuleCat (ZMod p)) (ModuleCat (ZMod p))).obj
        ((homogeneous p G).X 3) ≅ ModuleCat.of (ZMod p) (G × G × G → ZMod p) := by
  change ModuleCat.of (ZMod p) (homogeneousTermThree p G) ≅ _
  exact (homogeneousThreeEquiv p G).toModuleIso

noncomputable abbrev forgetTopology :
    TopModuleCat (ZMod p) ⥤ ModuleCat (ZMod p) :=
  forget₂ (TopModuleCat (ZMod p)) (ModuleCat (ZMod p))

noncomputable abbrev mappedHomogeneousShort : ShortComplex (ModuleCat (ZMod p)) :=
  ((homogeneous p G).sc 2).map (forgetTopology p)

/-- The same short complex with the neighboring degrees explicitly fixed as
`1`, `2`, and `3`.  This avoids relying on definitional reduction of the
predecessor and successor chosen by `HomologicalComplex.sc`. -/
noncomputable abbrev mappedHomogeneousExplicit : ShortComplex (ModuleCat (ZMod p)) :=
  ((homogeneous p G).sc' 1 2 3).map (forgetTopology p)

noncomputable def shortTermOneIso :
    (mappedHomogeneousExplicit p G).X₁ ≅
      (groupCohomology.shortComplexH2 (ordinaryRep p G)).X₁ := by
  change (forgetTopology p).obj ((homogeneous p G).X 1) ≅
    ModuleCat.of (ZMod p) (G → ZMod p)
  exact termOneIso p G

noncomputable def shortTermTwoIso :
    (mappedHomogeneousExplicit p G).X₂ ≅
      (groupCohomology.shortComplexH2 (ordinaryRep p G)).X₂ := by
  change (forgetTopology p).obj ((homogeneous p G).X 2) ≅
    ModuleCat.of (ZMod p) (G × G → ZMod p)
  exact termTwoIso p G

noncomputable def shortTermThreeIso :
    (mappedHomogeneousExplicit p G).X₃ ≅
      (groupCohomology.shortComplexH2 (ordinaryRep p G)).X₃ := by
  change (forgetTopology p).obj ((homogeneous p G).X 3) ≅
    ModuleCat.of (ZMod p) (G × G × G → ZMod p)
  exact termThreeIso p G

set_option backward.isDefEq.respectTransparency false in
theorem comm_dOne :
    (shortTermOneIso p G).hom ≫ (groupCohomology.shortComplexH2
      (ordinaryRep p G)).f =
      (mappedHomogeneousExplicit p G).f ≫ (shortTermTwoIso p G).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro F
  change homogeneousTermOne p G at F
  funext gh
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  dsimp [shortTermOneIso, shortTermTwoIso, termOneIso, termTwoIso,
    homogeneousOneEquiv, homogeneousTwoEquiv, evalOnePair, evalOneTriple,
    mappedHomogeneousExplicit, forgetTopology, homogeneous,
    groupCohomology.shortComplexH2, groupCohomology.d₁₂]
  simp only [LinearEquiv.toModuleIso_hom]
  dsimp [ShortComplex.map, HomologicalComplex.sc',
    HomologicalComplex.shortComplexFunctor']
  change F.1 1 gh.2 - F.1 1 (gh.1 * gh.2) + F.1 1 gh.1 =
    evalOneTriple p G (((homogeneous p G).d 1 2).hom F) gh
  change F.1 1 gh.2 - F.1 1 (gh.1 * gh.2) + F.1 1 gh.1 =
    (show C(G, C(G, C(G, ZMod p))) from
      ((ContinuousCohomology.MultiInd.d (ZMod p) G 2).app
        (topRep p G)).hom.hom F.1) 1 gh.1 (gh.1 * gh.2)
  rw [ContinuousCohomology.MultiInd.d_succ]
  rw [CategoryTheory.NatTrans.app_sub]
  rw [Action.sub_hom, TopModuleCat.hom_sub, sub_apply]
  rw [CategoryTheory.Functor.whiskerLeft_app,
    CategoryTheory.Functor.whiskerRight_app]
  rw [ContinuousCohomology.const_app_hom, ContinuousCohomology.I_map_hom]
  rw [TopModuleCat.hom_ofHom, TopModuleCat.hom_ofHom]
  change F.1 1 gh.2 - F.1 1 (gh.1 * gh.2) + F.1 1 gh.1 =
    (show C(G, C(G, C(G, ZMod p))) from
      (ContinuousLinearMap.const (ZMod p) G) F.1) 1 gh.1 (gh.1 * gh.2) -
      (show C(G, C(G, C(G, ZMod p))) from
        (ContinuousLinearMap.compLeftContinuous (ZMod p) G
          (((ContinuousCohomology.MultiInd.d (ZMod p) G 1).app
            (topRep p G)).hom.hom)) F.1) 1 gh.1 (gh.1 * gh.2)
  rw [ContinuousLinearMap.const_apply_apply,
    ContinuousLinearMap.compLeftContinuous_apply]
  change F.1 1 gh.2 - F.1 1 (gh.1 * gh.2) + F.1 1 gh.1 =
    (show ZMod p from F.1 gh.1 (gh.1 * gh.2)) -
      (show C(G, C(G, ZMod p)) from
        ((ContinuousCohomology.MultiInd.d (ZMod p) G 1).app
          (topRep p G)).hom.hom (F.1 1)) gh.1 (gh.1 * gh.2)
  rw [ContinuousCohomology.MultiInd.d_succ]
  rw [CategoryTheory.NatTrans.app_sub]
  rw [Action.sub_hom, TopModuleCat.hom_sub, sub_apply]
  rw [CategoryTheory.Functor.whiskerLeft_app,
    CategoryTheory.Functor.whiskerRight_app]
  rw [ContinuousCohomology.const_app_hom, ContinuousCohomology.I_map_hom]
  rw [TopModuleCat.hom_ofHom, TopModuleCat.hom_ofHom]
  change F.1 1 gh.2 - F.1 1 (gh.1 * gh.2) + F.1 1 gh.1 =
    (show ZMod p from F.1 gh.1 (gh.1 * gh.2)) -
      ((show C(G, C(G, ZMod p)) from
          (ContinuousLinearMap.const (ZMod p) G) (F.1 1))
          gh.1 (gh.1 * gh.2) -
        (show C(G, C(G, ZMod p)) from
          (ContinuousLinearMap.compLeftContinuous (ZMod p) G
            (((ContinuousCohomology.MultiInd.d (ZMod p) G 0).app
              (topRep p G)).hom.hom)) (F.1 1)) gh.1 (gh.1 * gh.2))
  rw [ContinuousLinearMap.const_apply_apply,
    ContinuousLinearMap.compLeftContinuous_apply]
  change F.1 1 gh.2 - F.1 1 (gh.1 * gh.2) + F.1 1 gh.1 =
    (show ZMod p from F.1 gh.1 (gh.1 * gh.2)) -
      ((show ZMod p from F.1 1 (gh.1 * gh.2)) -
        (show C(G, ZMod p) from
          ((ContinuousCohomology.MultiInd.d (ZMod p) G 0).app
            (topRep p G)).hom.hom (F.1 1 gh.1)) (gh.1 * gh.2))
  rw [ContinuousCohomology.MultiInd.d_zero,
    ContinuousCohomology.const_app_hom, TopModuleCat.hom_ofHom]
  change F.1 1 gh.2 - F.1 1 (gh.1 * gh.2) + F.1 1 gh.1 =
    (show ZMod p from F.1 gh.1 (gh.1 * gh.2)) -
      ((show ZMod p from F.1 1 (gh.1 * gh.2)) -
        (show ZMod p from F.1 1 gh.1))
  have hfirst : F.1 1 gh.2 = F.1 gh.1 (gh.1 * gh.2) := by
    have h := F.2 gh.1
    have h' := congrArg (fun x ↦ x gh.1 (gh.1 * gh.2)) h
    change F.1 (gh.1⁻¹ * gh.1) (gh.1⁻¹ * (gh.1 * gh.2)) =
      F.1 gh.1 (gh.1 * gh.2) at h'
    simpa only [inv_mul_cancel, inv_mul_cancel_left] using h'
  rw [hfirst]
  abel

set_option backward.isDefEq.respectTransparency false in
theorem comm_dTwo :
    (shortTermTwoIso p G).hom ≫ (groupCohomology.shortComplexH2
      (ordinaryRep p G)).g =
      (mappedHomogeneousExplicit p G).g ≫ (shortTermThreeIso p G).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro F
  change homogeneousTermTwo p G at F
  funext ghk
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  dsimp [shortTermTwoIso, shortTermThreeIso, termTwoIso, termThreeIso,
    homogeneousTwoEquiv, homogeneousThreeEquiv, evalOneTriple, evalOneQuadruple,
    mappedHomogeneousExplicit, forgetTopology, homogeneous,
    groupCohomology.shortComplexH2, groupCohomology.d₂₃]
  simp only [LinearEquiv.toModuleIso_hom]
  dsimp [ShortComplex.map, HomologicalComplex.sc',
    HomologicalComplex.shortComplexFunctor']
  change F.1 1 ghk.2.1 (ghk.2.1 * ghk.2.2) -
        F.1 1 (ghk.1 * ghk.2.1) (ghk.1 * ghk.2.1 * ghk.2.2) +
        F.1 1 ghk.1 (ghk.1 * (ghk.2.1 * ghk.2.2)) -
        F.1 1 ghk.1 (ghk.1 * ghk.2.1) =
    evalOneQuadruple p G (((homogeneous p G).d 2 3).hom F) ghk
  change F.1 1 ghk.2.1 (ghk.2.1 * ghk.2.2) -
        F.1 1 (ghk.1 * ghk.2.1) (ghk.1 * ghk.2.1 * ghk.2.2) +
        F.1 1 ghk.1 (ghk.1 * (ghk.2.1 * ghk.2.2)) -
        F.1 1 ghk.1 (ghk.1 * ghk.2.1) =
    (show C(G, C(G, C(G, C(G, ZMod p)))) from
      ((ContinuousCohomology.MultiInd.d (ZMod p) G 3).app
        (topRep p G)).hom.hom F.1)
      1 ghk.1 (ghk.1 * ghk.2.1) (ghk.1 * ghk.2.1 * ghk.2.2)
  rw [ContinuousCohomology.MultiInd.d_succ]
  rw [CategoryTheory.NatTrans.app_sub]
  rw [Action.sub_hom, TopModuleCat.hom_sub, sub_apply]
  rw [CategoryTheory.Functor.whiskerLeft_app,
    CategoryTheory.Functor.whiskerRight_app]
  rw [ContinuousCohomology.const_app_hom, ContinuousCohomology.I_map_hom]
  rw [TopModuleCat.hom_ofHom, TopModuleCat.hom_ofHom]
  change F.1 1 ghk.2.1 (ghk.2.1 * ghk.2.2) -
        F.1 1 (ghk.1 * ghk.2.1) (ghk.1 * ghk.2.1 * ghk.2.2) +
        F.1 1 ghk.1 (ghk.1 * (ghk.2.1 * ghk.2.2)) -
        F.1 1 ghk.1 (ghk.1 * ghk.2.1) =
    (show C(G, C(G, C(G, C(G, ZMod p)))) from
      (ContinuousLinearMap.const (ZMod p) G) F.1)
        1 ghk.1 (ghk.1 * ghk.2.1) (ghk.1 * ghk.2.1 * ghk.2.2) -
      (show C(G, C(G, C(G, C(G, ZMod p)))) from
        (ContinuousLinearMap.compLeftContinuous (ZMod p) G
          (((ContinuousCohomology.MultiInd.d (ZMod p) G 2).app
            (topRep p G)).hom.hom)) F.1)
        1 ghk.1 (ghk.1 * ghk.2.1) (ghk.1 * ghk.2.1 * ghk.2.2)
  rw [ContinuousLinearMap.const_apply_apply,
    ContinuousLinearMap.compLeftContinuous_apply]
  change F.1 1 ghk.2.1 (ghk.2.1 * ghk.2.2) -
        F.1 1 (ghk.1 * ghk.2.1) (ghk.1 * ghk.2.1 * ghk.2.2) +
        F.1 1 ghk.1 (ghk.1 * (ghk.2.1 * ghk.2.2)) -
        F.1 1 ghk.1 (ghk.1 * ghk.2.1) =
    (show ZMod p from
      F.1 ghk.1 (ghk.1 * ghk.2.1) (ghk.1 * ghk.2.1 * ghk.2.2)) -
      (show C(G, C(G, C(G, ZMod p))) from
        ((ContinuousCohomology.MultiInd.d (ZMod p) G 2).app
          (topRep p G)).hom.hom (F.1 1))
        ghk.1 (ghk.1 * ghk.2.1) (ghk.1 * ghk.2.1 * ghk.2.2)
  rw [ContinuousCohomology.MultiInd.d_succ]
  rw [CategoryTheory.NatTrans.app_sub]
  rw [Action.sub_hom, TopModuleCat.hom_sub, sub_apply]
  rw [CategoryTheory.Functor.whiskerLeft_app,
    CategoryTheory.Functor.whiskerRight_app]
  rw [ContinuousCohomology.const_app_hom, ContinuousCohomology.I_map_hom]
  rw [TopModuleCat.hom_ofHom, TopModuleCat.hom_ofHom]
  change F.1 1 ghk.2.1 (ghk.2.1 * ghk.2.2) -
        F.1 1 (ghk.1 * ghk.2.1) (ghk.1 * ghk.2.1 * ghk.2.2) +
        F.1 1 ghk.1 (ghk.1 * (ghk.2.1 * ghk.2.2)) -
        F.1 1 ghk.1 (ghk.1 * ghk.2.1) =
    (show ZMod p from
      F.1 ghk.1 (ghk.1 * ghk.2.1) (ghk.1 * ghk.2.1 * ghk.2.2)) -
      ((show C(G, C(G, C(G, ZMod p))) from
        (ContinuousLinearMap.const (ZMod p) G) (F.1 1))
          ghk.1 (ghk.1 * ghk.2.1) (ghk.1 * ghk.2.1 * ghk.2.2) -
        (show C(G, C(G, C(G, ZMod p))) from
          (ContinuousLinearMap.compLeftContinuous (ZMod p) G
            (((ContinuousCohomology.MultiInd.d (ZMod p) G 1).app
              (topRep p G)).hom.hom)) (F.1 1))
          ghk.1 (ghk.1 * ghk.2.1) (ghk.1 * ghk.2.1 * ghk.2.2))
  rw [ContinuousLinearMap.const_apply_apply,
    ContinuousLinearMap.compLeftContinuous_apply]
  change F.1 1 ghk.2.1 (ghk.2.1 * ghk.2.2) -
        F.1 1 (ghk.1 * ghk.2.1) (ghk.1 * ghk.2.1 * ghk.2.2) +
        F.1 1 ghk.1 (ghk.1 * (ghk.2.1 * ghk.2.2)) -
        F.1 1 ghk.1 (ghk.1 * ghk.2.1) =
    (show ZMod p from
      F.1 ghk.1 (ghk.1 * ghk.2.1) (ghk.1 * ghk.2.1 * ghk.2.2)) -
      ((show ZMod p from
        F.1 1 (ghk.1 * ghk.2.1) (ghk.1 * ghk.2.1 * ghk.2.2)) -
        (show C(G, C(G, ZMod p)) from
          ((ContinuousCohomology.MultiInd.d (ZMod p) G 1).app
            (topRep p G)).hom.hom (F.1 1 ghk.1))
          (ghk.1 * ghk.2.1) (ghk.1 * ghk.2.1 * ghk.2.2))
  rw [ContinuousCohomology.MultiInd.d_succ]
  rw [CategoryTheory.NatTrans.app_sub]
  rw [Action.sub_hom, TopModuleCat.hom_sub, sub_apply]
  rw [CategoryTheory.Functor.whiskerLeft_app,
    CategoryTheory.Functor.whiskerRight_app]
  rw [ContinuousCohomology.const_app_hom, ContinuousCohomology.I_map_hom]
  rw [TopModuleCat.hom_ofHom, TopModuleCat.hom_ofHom]
  change F.1 1 ghk.2.1 (ghk.2.1 * ghk.2.2) -
        F.1 1 (ghk.1 * ghk.2.1) (ghk.1 * ghk.2.1 * ghk.2.2) +
        F.1 1 ghk.1 (ghk.1 * (ghk.2.1 * ghk.2.2)) -
        F.1 1 ghk.1 (ghk.1 * ghk.2.1) =
    (show ZMod p from
      F.1 ghk.1 (ghk.1 * ghk.2.1) (ghk.1 * ghk.2.1 * ghk.2.2)) -
      ((show ZMod p from
        F.1 1 (ghk.1 * ghk.2.1) (ghk.1 * ghk.2.1 * ghk.2.2)) -
        ((show C(G, C(G, ZMod p)) from
          (ContinuousLinearMap.const (ZMod p) G) (F.1 1 ghk.1))
            (ghk.1 * ghk.2.1) (ghk.1 * ghk.2.1 * ghk.2.2) -
          (show C(G, C(G, ZMod p)) from
            (ContinuousLinearMap.compLeftContinuous (ZMod p) G
              (((ContinuousCohomology.MultiInd.d (ZMod p) G 0).app
                (topRep p G)).hom.hom)) (F.1 1 ghk.1))
            (ghk.1 * ghk.2.1) (ghk.1 * ghk.2.1 * ghk.2.2)))
  rw [ContinuousLinearMap.const_apply_apply,
    ContinuousLinearMap.compLeftContinuous_apply]
  change F.1 1 ghk.2.1 (ghk.2.1 * ghk.2.2) -
        F.1 1 (ghk.1 * ghk.2.1) (ghk.1 * ghk.2.1 * ghk.2.2) +
        F.1 1 ghk.1 (ghk.1 * (ghk.2.1 * ghk.2.2)) -
        F.1 1 ghk.1 (ghk.1 * ghk.2.1) =
    (show ZMod p from
      F.1 ghk.1 (ghk.1 * ghk.2.1) (ghk.1 * ghk.2.1 * ghk.2.2)) -
      ((show ZMod p from
        F.1 1 (ghk.1 * ghk.2.1) (ghk.1 * ghk.2.1 * ghk.2.2)) -
        ((show ZMod p from
          F.1 1 ghk.1 (ghk.1 * ghk.2.1 * ghk.2.2)) -
          (show C(G, ZMod p) from
            ((ContinuousCohomology.MultiInd.d (ZMod p) G 0).app
              (topRep p G)).hom.hom
                (F.1 1 ghk.1 (ghk.1 * ghk.2.1)))
            (ghk.1 * ghk.2.1 * ghk.2.2)))
  rw [ContinuousCohomology.MultiInd.d_zero,
    ContinuousCohomology.const_app_hom, TopModuleCat.hom_ofHom]
  change F.1 1 ghk.2.1 (ghk.2.1 * ghk.2.2) -
        F.1 1 (ghk.1 * ghk.2.1) (ghk.1 * ghk.2.1 * ghk.2.2) +
        F.1 1 ghk.1 (ghk.1 * (ghk.2.1 * ghk.2.2)) -
        F.1 1 ghk.1 (ghk.1 * ghk.2.1) =
    F.1 ghk.1 (ghk.1 * ghk.2.1) (ghk.1 * ghk.2.1 * ghk.2.2) -
      (F.1 1 (ghk.1 * ghk.2.1) (ghk.1 * ghk.2.1 * ghk.2.2) -
        (F.1 1 ghk.1 (ghk.1 * ghk.2.1 * ghk.2.2) -
          F.1 1 ghk.1 (ghk.1 * ghk.2.1)))
  have hfirst : F.1 1 ghk.2.1 (ghk.2.1 * ghk.2.2) =
      F.1 ghk.1 (ghk.1 * ghk.2.1) (ghk.1 * ghk.2.1 * ghk.2.2) := by
    have h := F.2 ghk.1
    have h' := congrArg (fun x ↦ x ghk.1 (ghk.1 * ghk.2.1)
      (ghk.1 * ghk.2.1 * ghk.2.2)) h
    change F.1 (ghk.1⁻¹ * ghk.1)
        (ghk.1⁻¹ * (ghk.1 * ghk.2.1))
        (ghk.1⁻¹ * (ghk.1 * ghk.2.1 * ghk.2.2)) =
      F.1 ghk.1 (ghk.1 * ghk.2.1) (ghk.1 * ghk.2.1 * ghk.2.2) at h'
    simpa only [inv_mul_cancel, inv_mul_cancel_left, mul_assoc] using h'
  rw [hfirst]
  simp only [mul_assoc]
  abel

noncomputable def explicitShortComplexIso :
    mappedHomogeneousExplicit p G ≅
      groupCohomology.shortComplexH2 (ordinaryRep p G) :=
  ShortComplex.isoMk (shortTermOneIso p G) (shortTermTwoIso p G) (shortTermThreeIso p G)
    (comm_dOne p G) (comm_dTwo p G)

noncomputable def normalizeMappedShortIso :
    mappedHomogeneousShort p G ≅ mappedHomogeneousExplicit p G :=
  (forgetTopology p).mapShortComplex.mapIso
    ((homogeneous p G).isoSc' 1 2 3 (by simp) (by simp))

noncomputable def shortComplexIso :
    mappedHomogeneousShort p G ≅
      groupCohomology.shortComplexH2 (ordinaryRep p G) :=
  normalizeMappedShortIso p G ≪≫ explicitShortComplexIso p G

/-- For a discrete group, degree-two continuous cohomology agrees with the
usual inhomogeneous group cohomology. -/
noncomputable def groupH2ContinuousIso :
    groupCohomology.H2 (ordinaryRep p G) ≅
      (forgetTopology p).obj
        ((continuousCohomology (ZMod p) G 2).obj (topRep p G)) := by
  change groupCohomology.H2 (ordinaryRep p G) ≅
    (forgetTopology p).obj ((homogeneous p G).homology 2)
  exact groupCohomology.H2Iso (ordinaryRep p G) ≪≫
    (groupCohomology.shortComplexH2
      (ordinaryRep p G)).moduleCatLeftHomologyData.homologyIso.symm ≪≫
    (ShortComplex.homologyMapIso (shortComplexIso p G)).symm ≪≫
    ((homogeneous p G).sc 2).mapHomologyIso (forgetTopology p)

noncomputable def groupH2ContinuousLinearEquiv :
    groupCohomology.H2 (ordinaryRep p G) ≃ₗ[ZMod p]
      (continuousCohomology (ZMod p) G 2).obj (topRep p G) :=
  LinearEquiv.ofBijective (groupH2ContinuousIso p G).hom.hom
    (ConcreteCategory.bijective_of_isIso (groupH2ContinuousIso p G).hom)

end Submission.CohomologyComparison
