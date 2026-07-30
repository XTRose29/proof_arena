import Submission.CircleWinding

open Complex
open scoped unitInterval

namespace Submission.CoreLift

noncomputable section

abbrev EdgeIndex := Fin 2 × Fin 3

abbrev EdgeDomain := EdgeIndex × unitInterval

instance : T2Space RadialMilnor.Fiber := by
  change T2Space {q : RadialMilnor.CSphere //
    0 < (RadialMilnor.polynomial q).re ∧ (RadialMilnor.polynomial q).im = 0}
  infer_instance

instance : T2Space RadialSpine.Spine := by
  change T2Space {q : RadialMilnor.Fiber //
    (RadialSpine.zTerm q.1.1.1).im = 0 ∧
      (RadialSpine.wTerm q.1.1.2).im = 0}
  infer_instance

instance : T2Space RadialCore.Core := by
  change T2Space {q : RadialSpine.Spine //
    0 ≤ (RadialSpine.zTerm q.1.1.1.1).re ∧
      0 ≤ (RadialSpine.wTerm q.1.1.1.2).re}
  infer_instance

def edgeParam (x : EdgeDomain) : RadialCore.Core :=
  CoreEdges.edge x.1.1 x.1.2 x.2

theorem edgeParam_continuous : Continuous edgeParam := by
  rw [continuous_prod_of_discrete_left]
  intro ij
  exact CoreEdges.edge_continuous ij.1 ij.2

theorem edgeParam_surjective : Function.Surjective edgeParam := by
  intro q
  obtain ⟨i, j, u, rfl⟩ := CoreClassification.exists_edge q
  exact ⟨((i, j), u), rfl⟩

def edgeParamMap : C(EdgeDomain, RadialCore.Core) :=
  ⟨edgeParam, edgeParam_continuous⟩

theorem edgeParam_isQuotientMap : Topology.IsQuotientMap edgeParamMap :=
  IsQuotientMap.of_surjective_continuous
    edgeParam_surjective edgeParam_continuous

def mappedEdge (g : C(RadialCore.Core, Circle)) (i : Fin 2) (j : Fin 3) :
    Path (g (CoreCycles.aVertex i)) (g (CoreCycles.bVertex j)) :=
  (CoreCycles.edgePath i j).map g.continuous

def edgeIncrement (g : C(RadialCore.Core, Circle)) (i : Fin 2) (j : Fin 3) : ℝ :=
  CircleWinding.pathIncrement (mappedEdge g i j)

theorem exp_edgeIncrement (g : C(RadialCore.Core, Circle))
    (i : Fin 2) (j : Fin 3) :
    Circle.exp (edgeIncrement g i j) =
      g (CoreCycles.bVertex j) * (g (CoreCycles.aVertex i))⁻¹ := by
  have hend := CircleWinding.exp_liftedPath (mappedEdge g i j) 1
  simpa [edgeIncrement, CircleWinding.pathIncrement,
    CircleWinding.normalizePath] using hend

def baseLift (g : C(RadialCore.Core, Circle)) : ℝ :=
  Classical.choose (Circle.exp_surjective (g (CoreCycles.aVertex 0)))

theorem exp_baseLift (g : C(RadialCore.Core, Circle)) :
    Circle.exp (baseLift g) = g (CoreCycles.aVertex 0) :=
  Classical.choose_spec (Circle.exp_surjective (g (CoreCycles.aVertex 0)))

def aLift (g : C(RadialCore.Core, Circle)) : Fin 2 → ℝ :=
  ![baseLift g,
    baseLift g + edgeIncrement g 0 0 - edgeIncrement g 1 0]

def bLift (g : C(RadialCore.Core, Circle)) : Fin 3 → ℝ :=
  ![baseLift g + edgeIncrement g 0 0,
    aLift g 1 + edgeIncrement g 1 1,
    aLift g 1 + edgeIncrement g 1 2]

theorem exp_aLift (g : C(RadialCore.Core, Circle)) (i : Fin 2) :
    Circle.exp (aLift g i) = g (CoreCycles.aVertex i) := by
  fin_cases i
  · simpa [aLift] using exp_baseLift g
  · change Circle.exp
      (baseLift g + edgeIncrement g 0 0 - edgeIncrement g 1 0) =
        g (CoreCycles.aVertex 1)
    rw [Circle.exp_sub, Circle.exp_add, exp_baseLift,
      exp_edgeIncrement, exp_edgeIncrement]
    simp

theorem exp_bLift (g : C(RadialCore.Core, Circle)) (j : Fin 3) :
    Circle.exp (bLift g j) = g (CoreCycles.bVertex j) := by
  fin_cases j
  · change Circle.exp (aLift g 0 + edgeIncrement g 0 0) =
      g (CoreCycles.bVertex 0)
    rw [Circle.exp_add, exp_aLift, exp_edgeIncrement]
    simp
  · change Circle.exp (aLift g 1 + edgeIncrement g 1 1) =
      g (CoreCycles.bVertex 1)
    rw [Circle.exp_add, exp_aLift, exp_edgeIncrement]
    simp
  · change Circle.exp (aLift g 1 + edgeIncrement g 1 2) =
      g (CoreCycles.bVertex 2)
    rw [Circle.exp_add, exp_aLift, exp_edgeIncrement]
    simp

def edgeLiftValue (g : C(RadialCore.Core, Circle))
    (i : Fin 2) (j : Fin 3) (u : unitInterval) : ℝ :=
  aLift g i + CircleWinding.liftedPath (mappedEdge g i j) u

theorem exp_edgeLiftValue (g : C(RadialCore.Core, Circle))
    (i : Fin 2) (j : Fin 3) (u : unitInterval) :
    Circle.exp (edgeLiftValue g i j u) = g (CoreEdges.edge i j u) := by
  rw [edgeLiftValue, Circle.exp_add, exp_aLift,
    CircleWinding.exp_liftedPath]
  change g (CoreCycles.aVertex i) *
      (g (CoreEdges.edge i j u) * (g (CoreCycles.aVertex i))⁻¹) =
    g (CoreEdges.edge i j u)
  simp

theorem firstCycle_increment_relation (g : C(RadialCore.Core, Circle))
    (h : CircleWinding.windingReal
      (CoreCycles.firstCycle.map g.continuous) = 0) :
    edgeIncrement g 0 1 =
      edgeIncrement g 0 0 - edgeIncrement g 1 0 + edgeIncrement g 1 1 := by
  rw [← CircleWinding.pathIncrement_loop] at h
  simp only [CoreCycles.firstCycle, Path.map_trans,
    CircleWinding.pathIncrement_trans] at h
  have h10 : CircleWinding.pathIncrement
      ((CoreCycles.edgePath 1 0).symm.map g.continuous) =
      -edgeIncrement g 1 0 := by
    rw [← Path.map_symm, CircleWinding.pathIncrement_symm]
    rfl
  have h01 : CircleWinding.pathIncrement
      ((CoreCycles.edgePath 0 1).symm.map g.continuous) =
      -edgeIncrement g 0 1 := by
    rw [← Path.map_symm, CircleWinding.pathIncrement_symm]
    rfl
  rw [h10, h01] at h
  change edgeIncrement g 0 0 +
      (-edgeIncrement g 1 0 +
        (edgeIncrement g 1 1 + -edgeIncrement g 0 1)) = 0 at h
  linarith

theorem secondCycle_increment_relation (g : C(RadialCore.Core, Circle))
    (h : CircleWinding.windingReal
      (CoreCycles.secondCycle.map g.continuous) = 0) :
    edgeIncrement g 0 2 =
      edgeIncrement g 0 0 - edgeIncrement g 1 0 + edgeIncrement g 1 2 := by
  rw [← CircleWinding.pathIncrement_loop] at h
  simp only [CoreCycles.secondCycle, Path.map_trans,
    CircleWinding.pathIncrement_trans] at h
  have h10 : CircleWinding.pathIncrement
      ((CoreCycles.edgePath 1 0).symm.map g.continuous) =
      -edgeIncrement g 1 0 := by
    rw [← Path.map_symm, CircleWinding.pathIncrement_symm]
    rfl
  have h02 : CircleWinding.pathIncrement
      ((CoreCycles.edgePath 0 2).symm.map g.continuous) =
      -edgeIncrement g 0 2 := by
    rw [← Path.map_symm, CircleWinding.pathIncrement_symm]
    rfl
  rw [h10, h02] at h
  change edgeIncrement g 0 0 +
      (-edgeIncrement g 1 0 +
        (edgeIncrement g 1 2 + -edgeIncrement g 0 2)) = 0 at h
  linarith

@[simp] theorem edgeLiftValue_zero (g : C(RadialCore.Core, Circle))
    (i : Fin 2) (j : Fin 3) : edgeLiftValue g i j 0 = aLift g i := by
  simp [edgeLiftValue]

theorem edgeLiftValue_one (g : C(RadialCore.Core, Circle))
    (hfirst : CircleWinding.windingReal
      (CoreCycles.firstCycle.map g.continuous) = 0)
    (hsecond : CircleWinding.windingReal
      (CoreCycles.secondCycle.map g.continuous) = 0)
    (i : Fin 2) (j : Fin 3) : edgeLiftValue g i j 1 = bLift g j := by
  have h1 := firstCycle_increment_relation g hfirst
  have h2 := secondCycle_increment_relation g hsecond
  change aLift g i + edgeIncrement g i j = bLift g j
  fin_cases i <;> fin_cases j <;>
    simp [aLift, bLift] <;> linarith

theorem zRoot_injective : Function.Injective CoreEdges.zRoot := by
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · exfalso
    have hre := congrArg Complex.re h
    norm_num [CoreEdges.zRoot] at hre
  · exfalso
    have hre := congrArg Complex.re h
    norm_num [CoreEdges.zRoot] at hre
  · rfl

theorem wRoot_injective : Function.Injective CoreEdges.wRoot := by
  intro i j h
  apply Fin.ext
  exact CoreEdges.wGenerator_isPrimitiveRoot.pow_inj i.2 j.2 h

theorem edge_parameter_eq {i i' : Fin 2} {j j' : Fin 3}
    {u u' : unitInterval}
    (h : CoreEdges.edge i j u = CoreEdges.edge i' j' u') : u = u' := by
  apply Subtype.ext
  have hp := congrArg
    (fun q : RadialCore.Core => normSq q.1.1.1.1.2) h
  simpa only [CoreEdges.edge_parameter] using hp

theorem edge_z_index_eq {i i' : Fin 2} {j j' : Fin 3}
    {u : unitInterval} (hu : (u : ℝ) < 1)
    (h : CoreEdges.edge i j u = CoreEdges.edge i' j' u) : i = i' := by
  have hz := congrArg (fun q : RadialCore.Core => q.1.1.1.1.1) h
  change CoreEdges.edgeZ i u = CoreEdges.edgeZ i' u at hz
  have hz' := congrArg RadialCore.zCoordinate hz
  simp only [CoreEdges.edgeZ, CoreEdges.zCoordinate_fromZCoordinate,
    CoreEdges.edgeZCoordinate] at hz'
  have hsqrt : Real.sqrt (1 - (u : ℝ)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (sub_pos.mpr hu))
  have hcast : (Real.sqrt (1 - (u : ℝ)) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr hsqrt
  exact zRoot_injective (mul_left_cancel₀ hcast hz')

theorem edge_w_index_eq {i i' : Fin 2} {j j' : Fin 3}
    {u : unitInterval} (hu : 0 < (u : ℝ))
    (h : CoreEdges.edge i j u = CoreEdges.edge i' j' u) : j = j' := by
  have hw := congrArg (fun q : RadialCore.Core => q.1.1.1.1.2) h
  change CoreEdges.edgeW j u = CoreEdges.edgeW j' u at hw
  have hw' := congrArg RadialCore.wCoordinate hw
  simp only [CoreEdges.edgeW, CoreEdges.wCoordinate_fromWCoordinate,
    CoreEdges.edgeWCoordinate] at hw'
  have hsqrt : Real.sqrt (u : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hu)
  have hcast : (Real.sqrt (u : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hsqrt
  exact wRoot_injective (mul_left_cancel₀ hcast hw')

def edgeLiftMap (g : C(RadialCore.Core, Circle)) : C(EdgeDomain, ℝ) :=
  ⟨fun x => edgeLiftValue g x.1.1 x.1.2 x.2, by
    rw [continuous_prod_of_discrete_left]
    intro ij
    unfold edgeLiftValue
    change Continuous (fun u : unitInterval =>
      aLift g ij.1 + CircleWinding.liftedPath (mappedEdge g ij.1 ij.2) u)
    exact continuous_const.add (CircleWinding.liftedPath (mappedEdge g ij.1 ij.2)).continuous⟩

theorem edgeLiftMap_factors (g : C(RadialCore.Core, Circle))
    (hfirst : CircleWinding.windingReal
      (CoreCycles.firstCycle.map g.continuous) = 0)
    (hsecond : CircleWinding.windingReal
      (CoreCycles.secondCycle.map g.continuous) = 0) :
    Function.FactorsThrough (edgeLiftMap g) edgeParam := by
  rintro ⟨⟨i, j⟩, u⟩ ⟨⟨i', j'⟩, u'⟩ h
  have hu : u = u' := edge_parameter_eq h
  subst u'
  by_cases hu0 : u = 0
  · subst u
    have hi : i = i' := by
      apply edge_z_index_eq (show ((0 : unitInterval) : ℝ) < 1 by norm_num)
      exact h
    subst i'
    simp [edgeLiftMap]
  by_cases hu1 : u = 1
  · subst u
    have hj : j = j' := by
      apply edge_w_index_eq (show 0 < ((1 : unitInterval) : ℝ) by norm_num)
      exact h
    subst j'
    simp only [edgeLiftMap, ContinuousMap.coe_mk, edgeLiftValue_one g hfirst hsecond]
  · have huVal0 : (u : ℝ) ≠ 0 := fun hval => hu0 (Subtype.ext hval)
    have huVal1 : (u : ℝ) ≠ 1 := fun hval => hu1 (Subtype.ext hval)
    have huPos : 0 < (u : ℝ) := lt_of_le_of_ne u.2.1 (Ne.symm huVal0)
    have huLt : (u : ℝ) < 1 := lt_of_le_of_ne u.2.2 huVal1
    have hi : i = i' := edge_z_index_eq huLt h
    have hj : j = j' := edge_w_index_eq huPos h
    subst i'
    subst j'
    rfl

def coreLift (g : C(RadialCore.Core, Circle))
    (hfirst : CircleWinding.windingReal
      (CoreCycles.firstCycle.map g.continuous) = 0)
    (hsecond : CircleWinding.windingReal
      (CoreCycles.secondCycle.map g.continuous) = 0) : C(RadialCore.Core, ℝ) :=
  edgeParam_isQuotientMap.lift (edgeLiftMap g)
    (edgeLiftMap_factors g hfirst hsecond)

theorem coreLift_edge (g : C(RadialCore.Core, Circle))
    (hfirst : CircleWinding.windingReal
      (CoreCycles.firstCycle.map g.continuous) = 0)
    (hsecond : CircleWinding.windingReal
      (CoreCycles.secondCycle.map g.continuous) = 0)
    (i : Fin 2) (j : Fin 3) (u : unitInterval) :
    coreLift g hfirst hsecond (CoreEdges.edge i j u) = edgeLiftValue g i j u := by
  have hcomp := edgeParam_isQuotientMap.lift_comp (edgeLiftMap g)
    (edgeLiftMap_factors g hfirst hsecond)
  exact DFunLike.congr_fun hcomp (((i, j), u) : EdgeDomain)

theorem exp_coreLift (g : C(RadialCore.Core, Circle))
    (hfirst : CircleWinding.windingReal
      (CoreCycles.firstCycle.map g.continuous) = 0)
    (hsecond : CircleWinding.windingReal
      (CoreCycles.secondCycle.map g.continuous) = 0)
    (q : RadialCore.Core) :
    Circle.exp (coreLift g hfirst hsecond q) = g q := by
  obtain ⟨i, j, u, rfl⟩ := CoreClassification.exists_edge q
  rw [coreLift_edge, exp_edgeLiftValue]

theorem exists_continuous_lift (g : C(RadialCore.Core, Circle))
    (hfirst : CircleWinding.windingReal
      (CoreCycles.firstCycle.map g.continuous) = 0)
    (hsecond : CircleWinding.windingReal
      (CoreCycles.secondCycle.map g.continuous) = 0) :
    ∃ G : C(RadialCore.Core, ℝ), ∀ q, Circle.exp (G q) = g q :=
  ⟨coreLift g hfirst hsecond, exp_coreLift g hfirst hsecond⟩

end

end Submission.CoreLift
