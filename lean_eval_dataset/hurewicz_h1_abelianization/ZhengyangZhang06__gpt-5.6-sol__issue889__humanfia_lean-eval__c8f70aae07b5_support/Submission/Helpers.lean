import ChallengeDeps

open CategoryTheory AlgebraicTopology Simplicial
open unitInterval

noncomputable section

namespace Submission.Helpers

private abbrev Triangle := stdSimplex ℝ (Fin 3)

private def triangleEdge01 :
    Path (stdSimplex.vertex (S := ℝ) (0 : Fin 3)) (stdSimplex.vertex (S := ℝ) (1 : Fin 3)) where
  toFun t := stdSimplex.map (S := ℝ) (2 : Fin 3).succAbove
    (TopCat.stdSimplexHomeomorphI.{0}.symm (ULift.up.{0, 0} t))
  continuous_toFun := by continuity
  source' := by
    change stdSimplex.map (S := ℝ) (2 : Fin 3).succAbove
      (TopCat.stdSimplexHomeomorphI.{0}.symm (0 : TopCat.I.{0})) = _
    simp
  target' := by
    change stdSimplex.map (S := ℝ) (2 : Fin 3).succAbove
      (TopCat.stdSimplexHomeomorphI.{0}.symm (1 : TopCat.I.{0})) = _
    have h : (2 : Fin 3).succAbove (1 : Fin 2) = (1 : Fin 3) := by decide
    simp [h]

private def triangleEdge12 :
    Path (stdSimplex.vertex (S := ℝ) (1 : Fin 3)) (stdSimplex.vertex (S := ℝ) (2 : Fin 3)) where
  toFun t := stdSimplex.map (S := ℝ) (0 : Fin 3).succAbove
    (TopCat.stdSimplexHomeomorphI.{0}.symm (ULift.up.{0, 0} t))
  continuous_toFun := by continuity
  source' := by
    change stdSimplex.map (S := ℝ) (0 : Fin 3).succAbove
      (TopCat.stdSimplexHomeomorphI.{0}.symm (0 : TopCat.I.{0})) = _
    simp
  target' := by
    change stdSimplex.map (S := ℝ) (0 : Fin 3).succAbove
      (TopCat.stdSimplexHomeomorphI.{0}.symm (1 : TopCat.I.{0})) = _
    simp

private def triangleEdge02 :
    Path (stdSimplex.vertex (S := ℝ) (0 : Fin 3)) (stdSimplex.vertex (S := ℝ) (2 : Fin 3)) where
  toFun t := stdSimplex.map (S := ℝ) (1 : Fin 3).succAbove
    (TopCat.stdSimplexHomeomorphI.{0}.symm (ULift.up.{0, 0} t))
  continuous_toFun := by continuity
  source' := by
    change stdSimplex.map (S := ℝ) (1 : Fin 3).succAbove
      (TopCat.stdSimplexHomeomorphI.{0}.symm (0 : TopCat.I.{0})) = _
    simp
  target' := by
    change stdSimplex.map (S := ℝ) (1 : Fin 3).succAbove
      (TopCat.stdSimplexHomeomorphI.{0}.symm (1 : TopCat.I.{0})) = _
    simp

private lemma triangle_edges_homotopic :
    (triangleEdge01.trans triangleEdge12).Homotopic triangleEdge02 := by
  letI : ContractibleSpace Triangle :=
    (convex_stdSimplex ℝ (Fin 3)).contractibleSpace
      ⟨Pi.single 0 1, single_mem_stdSimplex ℝ 0⟩
  exact SimplyConnectedSpace.paths_homotopic _ _

variable {X : Type} [TopologicalSpace X]

private abbrev singularSet := TopCat.toSSet.obj (TopCat.of X)

private def edgePath {v w : singularSet (X := X) _⦋0⦌}
    (e : SSet.Edge v w) :
    Path (TopCat.toSSetObj₀Equiv v) (TopCat.toSSetObj₀Equiv w) where
  toFun t := TopCat.toSSetObj₁Equiv e.edge (ULift.up.{0, 0} t)
  continuous_toFun := by fun_prop
  source' := by
    change TopCat.toSSetObj₁Equiv e.edge (0 : TopCat.I.{0}) = _
    rw [TopCat.toSSetObj₁Equiv_apply_zero, e.src_eq]
  target' := by
    change TopCat.toSSetObj₁Equiv e.edge (1 : TopCat.I.{0}) = _
    rw [TopCat.toSSetObj₁Equiv_apply_one, e.tgt_eq]

private lemma compStruct_edgePath_homotopic
    {v₀ v₁ v₂ : singularSet (X := X) _⦋0⦌}
    {e₀₁ : SSet.Edge v₀ v₁} {e₁₂ : SSet.Edge v₁ v₂} {e₀₂ : SSet.Edge v₀ v₂}
    (h : SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    (edgePath e₀₁).trans (edgePath e₁₂) |>.Homotopic (edgePath e₀₂) := by
  let f : C(Triangle, X) :=
    TopCat.toSSetObjEquiv (TopCat.of X) _ h.simplex
  have h₀₁ (t : I) : edgePath e₀₁ t = f (triangleEdge01 t) := by
    change (TopCat.toSSetObjEquiv (TopCat.of X) _ e₀₁.edge)
      (TopCat.stdSimplexHomeomorphI.{0}.symm (ULift.up.{0, 0} t)) =
        (TopCat.toSSetObjEquiv (TopCat.of X) _ h.simplex)
          (stdSimplex.map (S := ℝ) (2 : Fin 3).succAbove
            (TopCat.stdSimplexHomeomorphI.{0}.symm (ULift.up.{0, 0} t)))
    rw [← h.d₂]
    exact TopCat.toSSetObjEquiv_δ_apply h.simplex 2 _
  have h₁₂ (t : I) : edgePath e₁₂ t = f (triangleEdge12 t) := by
    change (TopCat.toSSetObjEquiv (TopCat.of X) _ e₁₂.edge)
      (TopCat.stdSimplexHomeomorphI.{0}.symm (ULift.up.{0, 0} t)) =
        (TopCat.toSSetObjEquiv (TopCat.of X) _ h.simplex)
          (stdSimplex.map (S := ℝ) (0 : Fin 3).succAbove
            (TopCat.stdSimplexHomeomorphI.{0}.symm (ULift.up.{0, 0} t)))
    rw [← h.d₀]
    exact TopCat.toSSetObjEquiv_δ_apply h.simplex 0 _
  have h₀₂ (t : I) : edgePath e₀₂ t = f (triangleEdge02 t) := by
    change (TopCat.toSSetObjEquiv (TopCat.of X) _ e₀₂.edge)
      (TopCat.stdSimplexHomeomorphI.{0}.symm (ULift.up.{0, 0} t)) =
        (TopCat.toSSetObjEquiv (TopCat.of X) _ h.simplex)
          (stdSimplex.map (S := ℝ) (1 : Fin 3).succAbove
            (TopCat.stdSimplexHomeomorphI.{0}.symm (ULift.up.{0, 0} t)))
    rw [← h.d₁]
    exact TopCat.toSSetObjEquiv_δ_apply h.simplex 1 _
  rcases triangle_edges_homotopic with ⟨H⟩
  have H' := H.map f
  have hv₀ : TopCat.toSSetObj₀Equiv v₀ = f (stdSimplex.vertex (0 : Fin 3)) := by
    simpa using h₀₁ 0
  have hv₂ : TopCat.toSSetObj₀Equiv v₂ = f (stdSimplex.vertex (2 : Fin 3)) := by
    simpa using h₀₂ 1
  refine ⟨(H'.pathCast hv₀ hv₂).cast ?_ ?_⟩
  · ext t
    change f ((triangleEdge01.trans triangleEdge12) t) =
      ((edgePath e₀₁).trans (edgePath e₁₂)) t
    simp only [Path.trans_apply]
    split_ifs
    · exact (h₀₁ _).symm
    · exact (h₁₂ _).symm
  · ext t
    change f (triangleEdge02 t) = edgePath e₀₂ t
    exact (h₀₂ _).symm

private abbrev integralChains :=
  (singularSet (X := X)).chainComplex (AddCommGrpCat.of ℤ)

private def pathSimplex {a b : X} (p : Path a b) :
    singularSet (X := X) _⦋1⦌ :=
  TopCat.toSSetObj₁Equiv.symm (TopCat.pathEquiv.symm p).hom

@[simp]
private lemma pathSimplex_δ_one {a b : X} (p : Path a b) :
    (singularSet (X := X)).δ 1 (pathSimplex p) =
      TopCat.toSSetObj₀Equiv.symm a := by
  simp only [pathSimplex, TopCat.δ_one_toSSetObj₁Equiv.symm]
  congr 1
  exact (TopCat.pathEquiv (X := TopCat.of X)).symm p |>.hom₀

@[simp]
private lemma pathSimplex_δ_zero {a b : X} (p : Path a b) :
    (singularSet (X := X)).δ 0 (pathSimplex p) =
      TopCat.toSSetObj₀Equiv.symm b := by
  simp only [pathSimplex, TopCat.δ_zero_toSSetObj₁Equiv.symm]
  congr 1
  exact (TopCat.pathEquiv (X := TopCat.of X)).symm p |>.hom₁

private lemma pathSimplex_isCycle {x : X} (p : Path x x) :
    (singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ) (pathSimplex p) ≫
      (integralChains (X := X)).d 1 0 = 0 := by
  rw [(singularSet (X := X)).ιChainComplex_d]
  simp [Fin.sum_univ_two]

private def pathHomologyMorphism {x : X} (p : Path x x) :
    AddCommGrpCat.of ℤ ⟶ (integralChains (X := X)).homology 1 :=
  (integralChains (X := X)).liftCycles
      ((singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ) (pathSimplex p))
      0 (by simp) (pathSimplex_isCycle p) ≫
    (integralChains (X := X)).homologyπ 1

private def pathHomologyClass {x : X} (p : Path x x) :
    ((integralChains (X := X)).homology 1 : Type) :=
  ((pathHomologyMorphism p).hom : ℤ →+
    ((integralChains (X := X)).homology 1 : Type)) (1 : ℤ)

private def triangleTime : C(Triangle, I) where
  toFun z := ⟨z.1 2 + z.1 1 / 2, by
    constructor
    · linarith [z.2.1 1, z.2.1 2]
    · have hz := z.2.2
      rw [Fin.sum_univ_three] at hz
      linarith [z.2.1 0, z.2.1 1, z.2.1 2]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_apply 2).comp continuous_subtype_val).add
      (((continuous_apply 1).comp continuous_subtype_val).div_const 2)

private lemma triangleTime_face_two (z : stdSimplex ℝ (Fin 2)) :
    (triangleTime (stdSimplex.map (S := ℝ) (2 : Fin 3).succAbove z) : ℝ) = z 1 / 2 := by
  change (stdSimplex.map (S := ℝ) (2 : Fin 3).succAbove z) 2 +
    (stdSimplex.map (S := ℝ) (2 : Fin 3).succAbove z) 1 / 2 = z 1 / 2
  classical
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply,
    show Finset.univ.filter (fun x : Fin 2 ↦ (2 : Fin 3).succAbove x = 2) = ∅ by decide,
    Finset.sum_empty, zero_add, FunOnFinite.linearMap_apply_apply,
    show Finset.univ.filter (fun x : Fin 2 ↦ (2 : Fin 3).succAbove x = 1) = {1} by decide,
    Finset.sum_singleton]

private lemma triangleTime_face_zero (z : stdSimplex ℝ (Fin 2)) :
    (triangleTime (stdSimplex.map (S := ℝ) (0 : Fin 3).succAbove z) : ℝ) =
      (1 + z 1) / 2 := by
  change (stdSimplex.map (S := ℝ) (0 : Fin 3).succAbove z) 2 +
    (stdSimplex.map (S := ℝ) (0 : Fin 3).succAbove z) 1 / 2 = (1 + z 1) / 2
  classical
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply,
    show Finset.univ.filter (fun x : Fin 2 ↦ (0 : Fin 3).succAbove x = 2) = {1} by decide,
    Finset.sum_singleton, FunOnFinite.linearMap_apply_apply,
    show Finset.univ.filter (fun x : Fin 2 ↦ (0 : Fin 3).succAbove x = 1) = {0} by decide,
    Finset.sum_singleton]
  have hz := stdSimplex.add_eq_one z
  linarith

private lemma triangleTime_face_one (z : stdSimplex ℝ (Fin 2)) :
    (triangleTime (stdSimplex.map (S := ℝ) (1 : Fin 3).succAbove z) : ℝ) = z 1 := by
  change (stdSimplex.map (S := ℝ) (1 : Fin 3).succAbove z) 2 +
    (stdSimplex.map (S := ℝ) (1 : Fin 3).succAbove z) 1 / 2 = z 1
  classical
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply,
    show Finset.univ.filter (fun x : Fin 2 ↦ (1 : Fin 3).succAbove x = 2) = {1} by decide,
    Finset.sum_singleton, FunOnFinite.linearMap_apply_apply,
    show Finset.univ.filter (fun x : Fin 2 ↦ (1 : Fin 3).succAbove x = 1) = ∅ by decide,
    Finset.sum_empty, zero_div, add_zero]

private def compositionSimplex {a b c : X} (p : Path a b) (q : Path b c) :
    singularSet (X := X) _⦋2⦌ :=
  (TopCat.toSSetObjEquiv (TopCat.of X) _).symm
    ⟨fun z ↦ (p.trans q) (triangleTime z), (p.trans q).continuous.comp triangleTime.continuous⟩

@[simp]
private lemma compositionSimplex_δ_two {a b c : X} (p : Path a b) (q : Path b c) :
    (singularSet (X := X)).δ 2 (compositionSimplex p q) = pathSimplex p := by
  apply (TopCat.toSSetObjEquiv (TopCat.of X) _).injective
  ext z
  rw [TopCat.toSSetObjEquiv_δ_apply]
  change (p.trans q) (triangleTime (stdSimplex.map (S := ℝ) (2 : Fin 3).succAbove z)) =
    p ⟨z 1, ⟨stdSimplex.zero_le z 1, stdSimplex.le_one z 1⟩⟩
  rw [Path.trans_apply]
  split_ifs with h
  · congr 1
    apply Subtype.ext
    change 2 * (triangleTime
      (stdSimplex.map (S := ℝ) (2 : Fin 3).succAbove z) : ℝ) = z 1
    rw [triangleTime_face_two]
    ring
  · exfalso
    apply h
    rw [triangleTime_face_two]
    linarith [stdSimplex.le_one z 1]

@[simp]
private lemma compositionSimplex_δ_zero {a b c : X} (p : Path a b) (q : Path b c) :
    (singularSet (X := X)).δ 0 (compositionSimplex p q) = pathSimplex q := by
  apply (TopCat.toSSetObjEquiv (TopCat.of X) _).injective
  ext z
  rw [TopCat.toSSetObjEquiv_δ_apply]
  change (p.trans q) (triangleTime (stdSimplex.map (S := ℝ) (0 : Fin 3).succAbove z)) =
    q ⟨z 1, ⟨stdSimplex.zero_le z 1, stdSimplex.le_one z 1⟩⟩
  rw [Path.trans_apply]
  split_ifs with h
  · have hz : z 1 = 0 := by
      rw [triangleTime_face_zero] at h
      linarith [stdSimplex.zero_le z 1]
    calc
      p _ = p 1 := by
        congr 1
        apply Subtype.ext
        change 2 * (triangleTime
          (stdSimplex.map (S := ℝ) (0 : Fin 3).succAbove z) : ℝ) = 1
        rw [triangleTime_face_zero, hz]
        norm_num
      _ = b := p.target'
      _ = q 0 := q.source'.symm
      _ = q ⟨z 1, ⟨stdSimplex.zero_le z 1, stdSimplex.le_one z 1⟩⟩ := by
        congr 1
        apply Subtype.ext
        exact hz.symm
  · congr 1
    apply Subtype.ext
    change 2 * (triangleTime
      (stdSimplex.map (S := ℝ) (0 : Fin 3).succAbove z) : ℝ) - 1 = z 1
    rw [triangleTime_face_zero]
    ring

@[simp]
private lemma compositionSimplex_δ_one {a b c : X} (p : Path a b) (q : Path b c) :
    (singularSet (X := X)).δ 1 (compositionSimplex p q) = pathSimplex (p.trans q) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of X) _).injective
  ext z
  rw [TopCat.toSSetObjEquiv_δ_apply]
  change (p.trans q) (triangleTime (stdSimplex.map (S := ℝ) (1 : Fin 3).succAbove z)) =
    (p.trans q) ⟨z 1, ⟨stdSimplex.zero_le z 1, stdSimplex.le_one z 1⟩⟩
  congr 1
  apply Subtype.ext
  exact triangleTime_face_one z

private lemma pathHomologyMorphism_trans {x : X} (p q : Path x x) :
    pathHomologyMorphism (p.trans q) =
      pathHomologyMorphism p + pathHomologyMorphism q := by
  let s := compositionSimplex p q
  have hb := (integralChains (X := X)).liftCycles_homologyπ_eq_zero_of_boundary
    ((singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ) s ≫
      (integralChains (X := X)).d 2 1)
    0 (by simp)
    ((singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ) s) rfl
  have hlift :
      (integralChains (X := X)).liftCycles
          ((singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ) (pathSimplex q))
          0 (by simp) (pathSimplex_isCycle q) -
        (integralChains (X := X)).liftCycles
          ((singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ)
            (pathSimplex (p.trans q))) 0 (by simp) (pathSimplex_isCycle (p.trans q)) +
        (integralChains (X := X)).liftCycles
          ((singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ) (pathSimplex p))
          0 (by simp) (pathSimplex_isCycle p) =
      (integralChains (X := X)).liftCycles
        ((singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ) (pathSimplex q) -
          (singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ)
            (pathSimplex (p.trans q)) +
          (singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ) (pathSimplex p))
        0 (by simp) (by
          simp only [Preadditive.add_comp, Preadditive.sub_comp]
          rw [pathSimplex_isCycle, pathSimplex_isCycle, pathSimplex_isCycle]
          simp) := by
    rw [← cancel_mono ((integralChains (X := X)).iCycles 1)]
    simp
  have hb' : pathHomologyMorphism q - pathHomologyMorphism (p.trans q) +
      pathHomologyMorphism p = 0 := by
    simp only [pathHomologyMorphism, ← Preadditive.sub_comp, ← Preadditive.add_comp]
    rw [hlift]
    simpa [s, Fin.sum_univ_three, sub_eq_add_neg] using hb
  calc
    pathHomologyMorphism (p.trans q) =
        pathHomologyMorphism (p.trans q) + 0 := by simp
    _ = pathHomologyMorphism (p.trans q) +
        (pathHomologyMorphism q - pathHomologyMorphism (p.trans q) +
          pathHomologyMorphism p) := by rw [hb']
    _ = pathHomologyMorphism p + pathHomologyMorphism q := by abel

private def simplexParameter (z : stdSimplex ℝ (Fin 2)) : I :=
  ⟨z 1, ⟨stdSimplex.zero_le z 1, stdSimplex.le_one z 1⟩⟩

private def lowerTriangleMap : C(Triangle, I × I) where
  toFun z :=
    (⟨z.1 2, ⟨z.2.1 2, stdSimplex.le_one z 2⟩⟩,
      ⟨z.1 1 + z.1 2, by
        constructor
        · exact add_nonneg (z.2.1 1) (z.2.1 2)
        · have hz := z.2.2
          rw [Fin.sum_univ_three] at hz
          linarith [z.2.1 0]⟩)
  continuous_toFun := by
    apply Continuous.prodMk
    · exact Continuous.subtype_mk ((continuous_apply 2).comp continuous_subtype_val) _
    · exact Continuous.subtype_mk
        (((continuous_apply 1).comp continuous_subtype_val).add
          ((continuous_apply 2).comp continuous_subtype_val)) _

private def upperTriangleMap : C(Triangle, I × I) where
  toFun z :=
    (⟨z.1 1 + z.1 2, by
        constructor
        · exact add_nonneg (z.2.1 1) (z.2.1 2)
        · have hz := z.2.2
          rw [Fin.sum_univ_three] at hz
          linarith [z.2.1 0]⟩,
      ⟨z.1 2, ⟨z.2.1 2, stdSimplex.le_one z 2⟩⟩)
  continuous_toFun := by
    apply Continuous.prodMk
    · exact Continuous.subtype_mk
        (((continuous_apply 1).comp continuous_subtype_val).add
          ((continuous_apply 2).comp continuous_subtype_val)) _
    · exact Continuous.subtype_mk ((continuous_apply 2).comp continuous_subtype_val) _

private lemma face_two_coord_one (z : stdSimplex ℝ (Fin 2)) :
    stdSimplex.map (S := ℝ) (2 : Fin 3).succAbove z 1 = z 1 := by
  classical
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply,
    show Finset.univ.filter (fun x : Fin 2 ↦ (2 : Fin 3).succAbove x = 1) = {1} by decide,
    Finset.sum_singleton]

private lemma face_two_coord_two (z : stdSimplex ℝ (Fin 2)) :
    stdSimplex.map (S := ℝ) (2 : Fin 3).succAbove z 2 = 0 := by
  classical
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply,
    show Finset.univ.filter (fun x : Fin 2 ↦ (2 : Fin 3).succAbove x = 2) = ∅ by decide,
    Finset.sum_empty]

private lemma face_zero_coord_one (z : stdSimplex ℝ (Fin 2)) :
    stdSimplex.map (S := ℝ) (0 : Fin 3).succAbove z 1 = z 0 := by
  classical
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply,
    show Finset.univ.filter (fun x : Fin 2 ↦ (0 : Fin 3).succAbove x = 1) = {0} by decide,
    Finset.sum_singleton]

private lemma face_zero_coord_two (z : stdSimplex ℝ (Fin 2)) :
    stdSimplex.map (S := ℝ) (0 : Fin 3).succAbove z 2 = z 1 := by
  classical
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply,
    show Finset.univ.filter (fun x : Fin 2 ↦ (0 : Fin 3).succAbove x = 2) = {1} by decide,
    Finset.sum_singleton]

private lemma face_one_coord_one (z : stdSimplex ℝ (Fin 2)) :
    stdSimplex.map (S := ℝ) (1 : Fin 3).succAbove z 1 = 0 := by
  classical
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply,
    show Finset.univ.filter (fun x : Fin 2 ↦ (1 : Fin 3).succAbove x = 1) = ∅ by decide,
    Finset.sum_empty]

private lemma lowerTriangleMap_face_two (z : stdSimplex ℝ (Fin 2)) :
    lowerTriangleMap (stdSimplex.map (S := ℝ) (2 : Fin 3).succAbove z) =
      (0, simplexParameter z) := by
  apply Prod.ext <;> apply Subtype.ext
  · exact face_two_coord_two z
  · change stdSimplex.map (S := ℝ) (2 : Fin 3).succAbove z 1 +
      stdSimplex.map (S := ℝ) (2 : Fin 3).succAbove z 2 = z 1
    rw [face_two_coord_one, face_two_coord_two, add_zero]

private lemma upperTriangleMap_face_zero (z : stdSimplex ℝ (Fin 2)) :
    upperTriangleMap (stdSimplex.map (S := ℝ) (0 : Fin 3).succAbove z) =
      (1, simplexParameter z) := by
  apply Prod.ext <;> apply Subtype.ext
  · change stdSimplex.map (S := ℝ) (0 : Fin 3).succAbove z 1 +
      stdSimplex.map (S := ℝ) (0 : Fin 3).succAbove z 2 = 1
    rw [face_zero_coord_one, face_zero_coord_two, stdSimplex.add_eq_one]
  · exact face_zero_coord_two z

private lemma triangleMaps_face_one (z : stdSimplex ℝ (Fin 2)) :
    lowerTriangleMap (stdSimplex.map (S := ℝ) (1 : Fin 3).succAbove z) =
      upperTriangleMap (stdSimplex.map (S := ℝ) (1 : Fin 3).succAbove z) := by
  apply Prod.ext
  · apply Subtype.ext
    change stdSimplex.map (S := ℝ) (1 : Fin 3).succAbove z 2 =
      stdSimplex.map (S := ℝ) (1 : Fin 3).succAbove z 1 +
        stdSimplex.map (S := ℝ) (1 : Fin 3).succAbove z 2
    rw [face_one_coord_one, zero_add]
  · apply Subtype.ext
    change stdSimplex.map (S := ℝ) (1 : Fin 3).succAbove z 1 +
      stdSimplex.map (S := ℝ) (1 : Fin 3).succAbove z 2 =
        stdSimplex.map (S := ℝ) (1 : Fin 3).succAbove z 2
    rw [face_one_coord_one, zero_add]

private lemma lowerTriangleMap_face_zero (z : stdSimplex ℝ (Fin 2)) :
    lowerTriangleMap (stdSimplex.map (S := ℝ) (0 : Fin 3).succAbove z) =
      (simplexParameter z, 1) := by
  apply Prod.ext <;> apply Subtype.ext
  · exact face_zero_coord_two z
  · change stdSimplex.map (S := ℝ) (0 : Fin 3).succAbove z 1 +
      stdSimplex.map (S := ℝ) (0 : Fin 3).succAbove z 2 = 1
    rw [face_zero_coord_one, face_zero_coord_two, stdSimplex.add_eq_one]

private lemma upperTriangleMap_face_two (z : stdSimplex ℝ (Fin 2)) :
    upperTriangleMap (stdSimplex.map (S := ℝ) (2 : Fin 3).succAbove z) =
      (simplexParameter z, 0) := by
  apply Prod.ext <;> apply Subtype.ext
  · change stdSimplex.map (S := ℝ) (2 : Fin 3).succAbove z 1 +
      stdSimplex.map (S := ℝ) (2 : Fin 3).succAbove z 2 = z 1
    rw [face_two_coord_one, face_two_coord_two, add_zero]
  · exact face_two_coord_two z

private def lowerHomotopySimplex {x : X} {p q : Path x x} (H : Path.Homotopy p q) :
    singularSet (X := X) _⦋2⦌ :=
  (TopCat.toSSetObjEquiv (TopCat.of X) _).symm
    ⟨fun z ↦ H (lowerTriangleMap z), H.continuous.comp lowerTriangleMap.continuous⟩

private def upperHomotopySimplex {x : X} {p q : Path x x} (H : Path.Homotopy p q) :
    singularSet (X := X) _⦋2⦌ :=
  (TopCat.toSSetObjEquiv (TopCat.of X) _).symm
    ⟨fun z ↦ H (upperTriangleMap z), H.continuous.comp upperTriangleMap.continuous⟩

@[simp]
private lemma lowerHomotopySimplex_δ_two {x : X} {p q : Path x x}
    (H : Path.Homotopy p q) :
    (singularSet (X := X)).δ 2 (lowerHomotopySimplex H) = pathSimplex p := by
  apply (TopCat.toSSetObjEquiv (TopCat.of X) _).injective
  ext z
  rw [TopCat.toSSetObjEquiv_δ_apply]
  change H (lowerTriangleMap (stdSimplex.map (S := ℝ) (2 : Fin 3).succAbove z)) =
    p (simplexParameter z)
  rw [lowerTriangleMap_face_two]
  simp

@[simp]
private lemma upperHomotopySimplex_δ_zero {x : X} {p q : Path x x}
    (H : Path.Homotopy p q) :
    (singularSet (X := X)).δ 0 (upperHomotopySimplex H) = pathSimplex q := by
  apply (TopCat.toSSetObjEquiv (TopCat.of X) _).injective
  ext z
  rw [TopCat.toSSetObjEquiv_δ_apply]
  change H (upperTriangleMap (stdSimplex.map (S := ℝ) (0 : Fin 3).succAbove z)) =
    q (simplexParameter z)
  rw [upperTriangleMap_face_zero]
  simp

private lemma homotopySimplex_δ_one {x : X} {p q : Path x x}
    (H : Path.Homotopy p q) :
    (singularSet (X := X)).δ 1 (lowerHomotopySimplex H) =
      (singularSet (X := X)).δ 1 (upperHomotopySimplex H) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of X) _).injective
  ext z
  rw [TopCat.toSSetObjEquiv_δ_apply, TopCat.toSSetObjEquiv_δ_apply]
  change H (lowerTriangleMap (stdSimplex.map (S := ℝ) (1 : Fin 3).succAbove z)) =
    H (upperTriangleMap (stdSimplex.map (S := ℝ) (1 : Fin 3).succAbove z))
  rw [triangleMaps_face_one]

private lemma homotopySimplex_constant_faces {x : X} {p q : Path x x}
    (H : Path.Homotopy p q) :
    (singularSet (X := X)).δ 0 (lowerHomotopySimplex H) =
      (singularSet (X := X)).δ 2 (upperHomotopySimplex H) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of X) _).injective
  ext z
  rw [TopCat.toSSetObjEquiv_δ_apply, TopCat.toSSetObjEquiv_δ_apply]
  change H (lowerTriangleMap (stdSimplex.map (S := ℝ) (0 : Fin 3).succAbove z)) =
    H (upperTriangleMap (stdSimplex.map (S := ℝ) (2 : Fin 3).succAbove z))
  rw [lowerTriangleMap_face_zero, upperTriangleMap_face_two]
  simp

private lemma pathHomologyMorphism_eq_of_homotopic {x : X} {p q : Path x x}
    (h : p.Homotopic q) : pathHomologyMorphism p = pathHomologyMorphism q := by
  obtain ⟨H⟩ := h
  let c₂ :=
    (singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ)
        (lowerHomotopySimplex H) -
      (singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ)
        (upperHomotopySimplex H)
  have hc₂ : c₂ ≫ (integralChains (X := X)).d 2 1 =
      (singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ) (pathSimplex p) -
        (singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ) (pathSimplex q) := by
    dsimp only [c₂]
    rw [Preadditive.sub_comp,
      (singularSet (X := X)).ιChainComplex_d,
      (singularSet (X := X)).ιChainComplex_d]
    simp [Fin.sum_univ_three, homotopySimplex_δ_one H,
      homotopySimplex_constant_faces H]
    abel
  have hb := (integralChains (X := X)).liftCycles_homologyπ_eq_zero_of_boundary
    (c₂ ≫ (integralChains (X := X)).d 2 1) 0 (by simp) c₂ rfl
  have hlift :
      (integralChains (X := X)).liftCycles
          ((singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ) (pathSimplex p))
          0 (by simp) (pathSimplex_isCycle p) -
        (integralChains (X := X)).liftCycles
          ((singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ) (pathSimplex q))
          0 (by simp) (pathSimplex_isCycle q) =
      (integralChains (X := X)).liftCycles
        (c₂ ≫ (integralChains (X := X)).d 2 1) 0 (by simp) (by simp) := by
    rw [← cancel_mono ((integralChains (X := X)).iCycles 1)]
    simp only [Preadditive.sub_comp,
      (integralChains (X := X)).liftCycles_i]
    exact hc₂.symm
  have hb' : pathHomologyMorphism p - pathHomologyMorphism q = 0 := by
    simp only [pathHomologyMorphism, ← Preadditive.sub_comp]
    rw [hlift]
    exact hb
  exact sub_eq_zero.mp hb'

private lemma pathHomologyClass_trans {x : X} (p q : Path x x) :
    pathHomologyClass (p.trans q) = pathHomologyClass p + pathHomologyClass q := by
  unfold pathHomologyClass
  rw [pathHomologyMorphism_trans]
  rfl

private lemma pathHomologyClass_eq_of_homotopic {x : X} {p q : Path x x}
    (h : p.Homotopic q) : pathHomologyClass p = pathHomologyClass q := by
  unfold pathHomologyClass
  rw [pathHomologyMorphism_eq_of_homotopic h]

private lemma pathHomologyClass_refl (x : X) :
    pathHomologyClass (Path.refl x) = 0 := by
  have h := pathHomologyClass_trans (Path.refl x) (Path.refl x)
  rw [pathHomologyClass_eq_of_homotopic
    (Path.Homotopic.trans_refl (Path.refl x))] at h
  have hc : pathHomologyClass (Path.refl x) + 0 =
      pathHomologyClass (Path.refl x) + pathHomologyClass (Path.refl x) := by
    simpa only [add_zero] using h
  exact (add_left_cancel hc).symm

private def quotientPathHomologyClass (x : X) :
    Path.Homotopic.Quotient x x → ((integralChains (X := X)).homology 1 : Type) :=
  Quotient.lift pathHomologyClass fun _ _ h ↦ by
    exact pathHomologyClass_eq_of_homotopic h

private def fundamentalGroupToHomology (x : X) :
    FundamentalGroup X x →* Multiplicative ((integralChains (X := X)).homology 1 : Type) where
  toFun g := Multiplicative.ofAdd (quotientPathHomologyClass x g)
  map_one' := by
    change pathHomologyClass (Path.refl x) = 0
    exact pathHomologyClass_refl x
  map_mul' g h := by
    induction g using Path.Homotopic.Quotient.ind with
    | mk p =>
      induction h using Path.Homotopic.Quotient.ind with
      | mk q =>
        change pathHomologyClass (q.trans p) = pathHomologyClass p + pathHomologyClass q
        rw [pathHomologyClass_trans]
        abel

private def hurewiczForward (x : X) :
    Additive (Abelianization (FundamentalGroup X x)) →+
      ((integralChains (X := X)).homology 1 : Type) :=
  (Abelianization.lift (fundamentalGroupToHomology x)).toAdditive

@[simp]
private lemma hurewiczForward_of_path (x : X) (p : Path x x) :
    hurewiczForward x
        (Additive.ofMul (Abelianization.of
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)))) =
      pathHomologyClass p :=
  rfl

private def connector [PathConnectedSpace X] (x y : X) : Path x y :=
  by
    classical
    exact if h : x = y then (Path.refl x).cast rfl h.symm else PathConnectedSpace.somePath x y

private def simplexEdge (e : singularSet (X := X) _⦋1⦌) :
    SSet.Edge ((singularSet (X := X)).δ 1 e) ((singularSet (X := X)).δ 0 e) :=
  SSet.Edge.mk e

private def simplexPath (e : singularSet (X := X) _⦋1⦌) :
    Path
      (TopCat.toSSetObj₀Equiv ((singularSet (X := X)).δ 1 e))
      (TopCat.toSSetObj₀Equiv ((singularSet (X := X)).δ 0 e)) :=
  edgePath (simplexEdge e)

private def connectorArrow [PathConnectedSpace X] (x y : X) :
    FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y :=
  Path.Homotopic.Quotient.mk (connector x y)

private def edgeArrow {v w : singularSet (X := X) _⦋0⦌} (e : SSet.Edge v w) :
    FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv v) ⟶
      FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv w) :=
  Path.Homotopic.Quotient.mk (edgePath e)

private def basedEdgeElementOfEdge [PathConnectedSpace X] (x : X)
    {v w : singularSet (X := X) _⦋0⦌} (e : SSet.Edge v w) : FundamentalGroup X x :=
  connectorArrow x (TopCat.toSSetObj₀Equiv v) ≫ edgeArrow e ≫
    Groupoid.inv (connectorArrow x (TopCat.toSSetObj₀Equiv w))

private def basedEdgeElement [PathConnectedSpace X] (x : X)
    (e : singularSet (X := X) _⦋1⦌) : FundamentalGroup X x :=
  basedEdgeElementOfEdge x (simplexEdge e)

private def basedEdgeValue [PathConnectedSpace X] (x : X)
    (e : singularSet (X := X) _⦋1⦌) :
    Additive (Abelianization (FundamentalGroup X x)) :=
  Additive.ofMul (Abelianization.of (basedEdgeElement x e))

private def basedEdgeValueOfEdge [PathConnectedSpace X] (x : X)
    {v w : singularSet (X := X) _⦋0⦌} (e : SSet.Edge v w) :
    Additive (Abelianization (FundamentalGroup X x)) :=
  Additive.ofMul (Abelianization.of (basedEdgeElementOfEdge x e))

private lemma basedEdgeValue_edge [PathConnectedSpace X] (x : X)
    {v w : singularSet (X := X) _⦋0⦌} (e : SSet.Edge v w) :
    basedEdgeValue x e.edge = basedEdgeValueOfEdge x e := by
  rcases e with ⟨e, hs, ht⟩
  dsimp only [SSet.Edge.edge, SSet.Edge.toTruncated, SSet.Edge.ofTruncated] at hs ht ⊢
  subst v
  subst w
  rfl

private lemma basedEdgeElementOfEdge_comp [PathConnectedSpace X] (x : X)
    {v₀ v₁ v₂ : singularSet (X := X) _⦋0⦌}
    {e₀₁ : SSet.Edge v₀ v₁} {e₁₂ : SSet.Edge v₁ v₂}
    {e₀₂ : SSet.Edge v₀ v₂} (h : SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    basedEdgeElementOfEdge x e₀₁ ≫ basedEdgeElementOfEdge x e₁₂ =
      basedEdgeElementOfEdge x e₀₂ := by
  have he : edgeArrow e₀₁ ≫ edgeArrow e₁₂ = edgeArrow e₀₂ := by
    apply Path.Homotopic.Quotient.eq.mpr
    exact compStruct_edgePath_homotopic h
  simp only [basedEdgeElementOfEdge, Category.assoc,
    Groupoid.inv_eq_inv, IsIso.inv_hom_id_assoc]
  rw [← Category.assoc (edgeArrow e₀₁) (edgeArrow e₁₂), he]

private lemma basedEdgeValueOfEdge_comp [PathConnectedSpace X] (x : X)
    {v₀ v₁ v₂ : singularSet (X := X) _⦋0⦌}
    {e₀₁ : SSet.Edge v₀ v₁} {e₁₂ : SSet.Edge v₁ v₂}
    {e₀₂ : SSet.Edge v₀ v₂} (h : SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    basedEdgeValueOfEdge x e₀₁ + basedEdgeValueOfEdge x e₁₂ =
      basedEdgeValueOfEdge x e₀₂ := by
  change Abelianization.of (basedEdgeElementOfEdge x e₀₁) *
      Abelianization.of (basedEdgeElementOfEdge x e₁₂) =
    Abelianization.of (basedEdgeElementOfEdge x e₀₂)
  rw [mul_comm, ← map_mul]
  exact congr_arg Abelianization.of (basedEdgeElementOfEdge_comp x h)

private def edgeGeneratorMorphism [PathConnectedSpace X] (x : X)
    (e : singularSet (X := X) _⦋1⦌) :
    AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of
      (Additive (Abelianization (FundamentalGroup X x))) :=
  AddCommGrpCat.ofHom (zmultiplesHom _ (basedEdgeValue x e))

private def basedEdgeMap [PathConnectedSpace X] (x : X) :
    (integralChains (X := X)).X 1 ⟶
      AddCommGrpCat.of (Additive (Abelianization (FundamentalGroup X x))) :=
  ((singularSet (X := X)).isColimitChainComplexXCofan (AddCommGrpCat.of ℤ) 1).desc
    (Limits.Cofan.mk _ (edgeGeneratorMorphism x))

@[reassoc (attr := simp)]
private lemma ιChainComplex_basedEdgeMap [PathConnectedSpace X] (x : X)
    (e : singularSet (X := X) _⦋1⦌) :
    (singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ) e ≫ basedEdgeMap x =
      edgeGeneratorMorphism x e := by
  exact ((singularSet (X := X)).isColimitChainComplexXCofan
    (AddCommGrpCat.of ℤ) 1).fac (Limits.Cofan.mk _ (edgeGeneratorMorphism x)) (Discrete.mk e)

private lemma basedEdgeValue_boundary [PathConnectedSpace X] (x : X)
    (s : singularSet (X := X) _⦋2⦌) :
    basedEdgeValue x ((singularSet (X := X)).δ 0 s) -
        basedEdgeValue x ((singularSet (X := X)).δ 1 s) +
      basedEdgeValue x ((singularSet (X := X)).δ 2 s) = 0 := by
  obtain ⟨v₀, v₁, v₂, e₀₁, e₁₂, e₀₂, h, rfl⟩ :=
    SSet.Edge.CompStruct.exists_of_simplex s
  rw [h.d₀, h.d₁, h.d₂, basedEdgeValue_edge x e₁₂,
    basedEdgeValue_edge x e₀₂, basedEdgeValue_edge x e₀₁]
  have hc := basedEdgeValueOfEdge_comp x h
  rw [← hc]
  abel

private lemma d_basedEdgeMap [PathConnectedSpace X] (x : X) :
    (integralChains (X := X)).d 2 1 ≫ basedEdgeMap x = 0 := by
  apply (singularSet (X := X)).chainComplex_hom_ext
  intro s
  rw [← Category.assoc, (singularSet (X := X)).ιChainComplex_d]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, ιChainComplex_basedEdgeMap]
  apply AddCommGrpCat.int_hom_ext
  simpa [Fin.sum_univ_three, edgeGeneratorMorphism, sub_eq_add_neg] using
    basedEdgeValue_boundary x s

private def hurewiczBackward [PathConnectedSpace X] (x : X) :
    (integralChains (X := X)).homology 1 ⟶
      AddCommGrpCat.of (Additive (Abelianization (FundamentalGroup X x))) :=
  ((integralChains (X := X)).homologyIsCokernel 2 1 (by simp)).desc
    (Limits.CokernelCofork.ofπ
      ((integralChains (X := X)).iCycles 1 ≫ basedEdgeMap x)
      (by
        rw [← Category.assoc, (integralChains (X := X)).toCycles_i]
        exact d_basedEdgeMap x))

@[reassoc]
private lemma homologyπ_hurewiczBackward [PathConnectedSpace X] (x : X) :
    (integralChains (X := X)).homologyπ 1 ≫ hurewiczBackward x =
      (integralChains (X := X)).iCycles 1 ≫ basedEdgeMap x := by
  let t : Limits.CokernelCofork ((integralChains (X := X)).toCycles 2 1) :=
    Limits.CokernelCofork.ofπ
      ((integralChains (X := X)).iCycles 1 ≫ basedEdgeMap x)
      (by
        rw [← Category.assoc, (integralChains (X := X)).toCycles_i]
        exact d_basedEdgeMap x)
  have h := Limits.Cofork.IsColimit.π_desc
    ((integralChains (X := X)).homologyIsCokernel 2 1 (by simp)) (t := t)
  have ht : Limits.Cofork.π t =
      (integralChains (X := X)).iCycles 1 ≫ basedEdgeMap x := rfl
  rw [ht] at h
  change (integralChains (X := X)).homologyπ 1 ≫ _ =
    (integralChains (X := X)).iCycles 1 ≫ basedEdgeMap x at h
  dsimp only [t] at h
  unfold hurewiczBackward
  exact h

private def hurewiczForwardMorphism (x : X) :
    AddCommGrpCat.of (Additive (Abelianization (FundamentalGroup X x))) ⟶
      (integralChains (X := X)).homology 1 :=
  AddCommGrpCat.ofHom (hurewiczForward x)

private lemma simplexPath_pathSimplex {a b : X} (p : Path a b) :
    (simplexPath (pathSimplex p)).cast (by simp) (by simp) = p := by
  ext t
  change (TopCat.toSSetObj₁Equiv
      (TopCat.toSSetObj₁Equiv.symm
        ((TopCat.pathEquiv (X := TopCat.of X)).symm p).hom)) (ULift.up t) = p t
  rw [Equiv.apply_symm_apply]
  rfl

private lemma pathSimplex_simplexPath (e : singularSet (X := X) _⦋1⦌) :
    pathSimplex (simplexPath e) = e := by
  apply TopCat.toSSetObj₁Equiv.injective
  simp only [pathSimplex, Equiv.apply_symm_apply]
  rfl

private lemma connector_eq_cast_refl [PathConnectedSpace X] (x y : X) (h : y = x) :
    connector x y = (Path.refl x).cast rfl h := by
  simp [connector, h.symm]

private lemma cast_refl_trans_path_trans_cast_refl_symm
    {x v w : X} (hv : v = x) (hw : w = x) (p : Path v w) :
    ((Path.refl x).cast rfl hv).trans
        (p.trans ((Path.refl x).cast rfl hw).symm) |>.Homotopic
      (p.cast hv.symm hw.symm) := by
  subst v
  subst w
  simpa using (Path.Homotopic.refl_trans (p.trans (Path.refl x))).trans
    (Path.Homotopic.trans_refl p)

private lemma basedEdgeElement_pathSimplex [PathConnectedSpace X] (x : X)
    (p : Path x x) :
    basedEdgeElement x (pathSimplex p) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) := by
  have hv : TopCat.toSSetObj₀Equiv
      ((singularSet (X := X)).δ 1 (pathSimplex p)) = x := by
    rw [pathSimplex_δ_one]
    exact Equiv.apply_symm_apply _ _
  have hw : TopCat.toSSetObj₀Equiv
      ((singularSet (X := X)).δ 0 (pathSimplex p)) = x := by
    rw [pathSimplex_δ_zero]
    exact Equiv.apply_symm_apply _ _
  change Path.Homotopic.Quotient.mk
      ((connector x (TopCat.toSSetObj₀Equiv
          ((singularSet (X := X)).δ 1 (pathSimplex p)))).trans
        ((simplexPath (pathSimplex p)).trans
          (connector x (TopCat.toSSetObj₀Equiv
            ((singularSet (X := X)).δ 0 (pathSimplex p)))).symm)) =
    Path.Homotopic.Quotient.mk p
  apply Path.Homotopic.Quotient.eq.mpr
  rw [connector_eq_cast_refl x _ hv, connector_eq_cast_refl x _ hw]
  have hpath := cast_refl_trans_path_trans_cast_refl_symm hv hw
    (simplexPath (pathSimplex p))
  have hp : (simplexPath (pathSimplex p)).cast hv.symm hw.symm = p := by
    simpa only [] using simplexPath_pathSimplex p
  rw [hp] at hpath
  exact hpath

private lemma hurewiczBackward_pathHomologyClass [PathConnectedSpace X] (x : X)
    (p : Path x x) :
    hurewiczBackward x (pathHomologyClass p) = basedEdgeValue x (pathSimplex p) := by
  change (pathHomologyMorphism p ≫ hurewiczBackward x) (1 : ℤ) = _
  rw [pathHomologyMorphism, Category.assoc, homologyπ_hurewiczBackward,
    ← Category.assoc, (integralChains (X := X)).liftCycles_i,
    ιChainComplex_basedEdgeMap]
  simp [edgeGeneratorMorphism]

private lemma hurewiczBackward_forward_of_path [PathConnectedSpace X] (x : X)
    (p : Path x x) :
    hurewiczBackward x
        (hurewiczForward x
          (Additive.ofMul (Abelianization.of
            (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))))) =
      Additive.ofMul (Abelianization.of
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))) := by
  rw [hurewiczForward_of_path, hurewiczBackward_pathHomologyClass]
  change Additive.ofMul (Abelianization.of (basedEdgeElement x (pathSimplex p))) = _
  rw [basedEdgeElement_pathSimplex]

private lemma hurewiczForward_hurewiczBackward [PathConnectedSpace X] (x : X) :
    hurewiczForwardMorphism x ≫ hurewiczBackward x = 𝟙 _ := by
  apply AddCommGrpCat.ext
  intro a
  change hurewiczBackward x (hurewiczForward x a) = a
  induction a using QuotientGroup.induction_on with
  | _ g =>
      induction g using Path.Homotopic.Quotient.ind with
      | mk p => exact hurewiczBackward_forward_of_path x p

private def sourceConnector [PathConnectedSpace X] (x : X)
    (e : singularSet (X := X) _⦋1⦌) :
    Path x (TopCat.toSSetObj₀Equiv ((singularSet (X := X)).δ 1 e)) :=
  connector x _

private def targetConnector [PathConnectedSpace X] (x : X)
    (e : singularSet (X := X) _⦋1⦌) :
    Path x (TopCat.toSSetObj₀Equiv ((singularSet (X := X)).δ 0 e)) :=
  connector x _

private def basedEdgePath [PathConnectedSpace X] (x : X)
    (e : singularSet (X := X) _⦋1⦌) : Path x x :=
  (sourceConnector x e).trans ((simplexPath e).trans (targetConnector x e).symm)

private lemma basedEdgeElement_eq_mk_basedEdgePath [PathConnectedSpace X] (x : X)
    (e : singularSet (X := X) _⦋1⦌) :
    basedEdgeElement x e =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (basedEdgePath x e)) := by
  rfl

private def basedLoopGeneratorMorphism [PathConnectedSpace X] (x : X)
    (e : singularSet (X := X) _⦋1⦌) :
    AddCommGrpCat.of ℤ ⟶ (integralChains (X := X)).X 1 :=
  (singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ)
    (pathSimplex (basedEdgePath x e))

private def basedLoopChainMap [PathConnectedSpace X] (x : X) :
    (integralChains (X := X)).X 1 ⟶ (integralChains (X := X)).X 1 :=
  ((singularSet (X := X)).isColimitChainComplexXCofan (AddCommGrpCat.of ℤ) 1).desc
    (Limits.Cofan.mk _ (basedLoopGeneratorMorphism x))

@[reassoc (attr := simp)]
private lemma ιChainComplex_basedLoopChainMap [PathConnectedSpace X] (x : X)
    (e : singularSet (X := X) _⦋1⦌) :
    (singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ) e ≫
        basedLoopChainMap x =
      basedLoopGeneratorMorphism x e := by
  exact ((singularSet (X := X)).isColimitChainComplexXCofan
    (AddCommGrpCat.of ℤ) 1).fac
      (Limits.Cofan.mk _ (basedLoopGeneratorMorphism x)) (Discrete.mk e)

private lemma basedLoopChainMap_d [PathConnectedSpace X] (x : X) :
    basedLoopChainMap x ≫ (integralChains (X := X)).d 1 0 = 0 := by
  apply (singularSet (X := X)).chainComplex_hom_ext
  intro e
  rw [← Category.assoc, ιChainComplex_basedLoopChainMap]
  exact pathSimplex_isCycle (basedEdgePath x e)

private def basedLoopHomologyMap [PathConnectedSpace X] (x : X) :
    (integralChains (X := X)).X 1 ⟶ (integralChains (X := X)).homology 1 :=
  (integralChains (X := X)).liftCycles (basedLoopChainMap x) 0 (by simp)
      (basedLoopChainMap_d x) ≫
    (integralChains (X := X)).homologyπ 1

@[reassoc]
private lemma ιChainComplex_basedLoopHomologyMap [PathConnectedSpace X] (x : X)
    (e : singularSet (X := X) _⦋1⦌) :
    (singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ) e ≫
        basedLoopHomologyMap x =
      pathHomologyMorphism (basedEdgePath x e) := by
  rw [basedLoopHomologyMap, ← Category.assoc,
    (integralChains (X := X)).comp_liftCycles]
  simp only [ιChainComplex_basedLoopChainMap]
  rfl

private lemma basedEdgeMap_hurewiczForward [PathConnectedSpace X] (x : X) :
    basedEdgeMap x ≫ hurewiczForwardMorphism x = basedLoopHomologyMap x := by
  apply (singularSet (X := X)).chainComplex_hom_ext
  intro e
  rw [← Category.assoc, ιChainComplex_basedEdgeMap]
  rw [ιChainComplex_basedLoopHomologyMap]
  apply AddCommGrpCat.int_hom_ext
  dsimp [edgeGeneratorMorphism, hurewiczForwardMorphism]
  change hurewiczForward x (1 • basedEdgeValue x e) = pathHomologyClass (basedEdgePath x e)
  simp only [one_smul]
  change hurewiczForward x
      (Additive.ofMul (Abelianization.of (basedEdgeElement x e))) = _
  rw [basedEdgeElement_eq_mk_basedEdgePath, hurewiczForward_of_path]

private def connectorGeneratorMorphism [PathConnectedSpace X] (x : X)
    (v : singularSet (X := X) _⦋0⦌) :
    AddCommGrpCat.of ℤ ⟶ (integralChains (X := X)).X 1 :=
  (singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ)
    (pathSimplex (connector x (TopCat.toSSetObj₀Equiv v)))

private def connectorChainMap [PathConnectedSpace X] (x : X) :
    (integralChains (X := X)).X 0 ⟶ (integralChains (X := X)).X 1 :=
  ((singularSet (X := X)).isColimitChainComplexXCofan (AddCommGrpCat.of ℤ) 0).desc
    (Limits.Cofan.mk _ (connectorGeneratorMorphism x))

@[reassoc (attr := simp)]
private lemma ιChainComplex_connectorChainMap [PathConnectedSpace X] (x : X)
    (v : singularSet (X := X) _⦋0⦌) :
    (singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ) v ≫
        connectorChainMap x =
      connectorGeneratorMorphism x v := by
  exact ((singularSet (X := X)).isColimitChainComplexXCofan
    (AddCommGrpCat.of ℤ) 0).fac
      (Limits.Cofan.mk _ (connectorGeneratorMorphism x)) (Discrete.mk v)

private lemma compositionSimplex_boundary {a b c : X} (p : Path a b) (q : Path b c) :
    (singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ)
        (compositionSimplex p q) ≫
        (integralChains (X := X)).d 2 1 =
      (singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ)
          (pathSimplex q) -
        (singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ)
          (pathSimplex (p.trans q)) +
        (singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ)
          (pathSimplex p) := by
  rw [(singularSet (X := X)).ιChainComplex_d]
  simp [Fin.sum_univ_three, sub_eq_add_neg]

private def homotopyBoundaryChain {y : X} {p q : Path y y} (H : Path.Homotopy p q) :
    AddCommGrpCat.of ℤ ⟶ (integralChains (X := X)).X 2 :=
  (singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ)
      (lowerHomotopySimplex H) -
    (singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ)
      (upperHomotopySimplex H)

private lemma homotopyBoundaryChain_d {y : X} {p q : Path y y}
    (H : Path.Homotopy p q) :
    homotopyBoundaryChain H ≫ (integralChains (X := X)).d 2 1 =
      (singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ)
          (pathSimplex p) -
        (singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ)
          (pathSimplex q) := by
  dsimp only [homotopyBoundaryChain]
  rw [Preadditive.sub_comp,
    (singularSet (X := X)).ιChainComplex_d,
    (singularSet (X := X)).ιChainComplex_d]
  simp [Fin.sum_univ_three, homotopySimplex_δ_one H,
    homotopySimplex_constant_faces H]
  abel

private def connectorCancellationHomotopy [PathConnectedSpace X] (x : X)
    (e : singularSet (X := X) _⦋1⦌) :
    Path.Homotopy
      ((targetConnector x e).trans (targetConnector x e).symm)
      (Path.refl x) :=
  Classical.choice (Path.Homotopic.trans_symm (targetConnector x e))

private def reflCancellationHomotopy (x : X) :
    Path.Homotopy ((Path.refl x).trans (Path.refl x)) (Path.refl x) :=
  Classical.choice (Path.Homotopic.refl_trans (Path.refl x))

private def edgeBoundaryWitness [PathConnectedSpace X] (x : X)
    (e : singularSet (X := X) _⦋1⦌) :
    AddCommGrpCat.of ℤ ⟶ (integralChains (X := X)).X 2 :=
  -((singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ)
      (compositionSimplex (sourceConnector x e)
        ((simplexPath e).trans (targetConnector x e).symm))) -
    (singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ)
      (compositionSimplex (simplexPath e) (targetConnector x e).symm) +
    (singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ)
      (compositionSimplex (targetConnector x e) (targetConnector x e).symm) +
    homotopyBoundaryChain (connectorCancellationHomotopy x e) +
    (singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ)
      (compositionSimplex (Path.refl x) (Path.refl x)) +
    homotopyBoundaryChain (reflCancellationHomotopy x)

private lemma edgeBoundaryWitness_d [PathConnectedSpace X] (x : X)
    (e : singularSet (X := X) _⦋1⦌) :
    edgeBoundaryWitness x e ≫ (integralChains (X := X)).d 2 1 =
      (singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ)
          (pathSimplex (basedEdgePath x e)) -
        (singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ) e +
        ((singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ)
            (pathSimplex (targetConnector x e)) -
          (singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ)
            (pathSimplex (sourceConnector x e))) := by
  dsimp only [edgeBoundaryWitness]
  simp only [Preadditive.add_comp, Preadditive.sub_comp, Preadditive.neg_comp]
  rw [compositionSimplex_boundary, compositionSimplex_boundary,
    compositionSimplex_boundary, homotopyBoundaryChain_d,
    compositionSimplex_boundary, homotopyBoundaryChain_d]
  dsimp only [basedEdgePath]
  rw [pathSimplex_simplexPath]
  abel

private def boundaryCorrectionMap [PathConnectedSpace X] (x : X) :
    (integralChains (X := X)).X 1 ⟶ (integralChains (X := X)).X 2 :=
  ((singularSet (X := X)).isColimitChainComplexXCofan (AddCommGrpCat.of ℤ) 1).desc
    (Limits.Cofan.mk _ (edgeBoundaryWitness x))

@[reassoc (attr := simp)]
private lemma ιChainComplex_boundaryCorrectionMap [PathConnectedSpace X] (x : X)
    (e : singularSet (X := X) _⦋1⦌) :
    (singularSet (X := X)).ιChainComplex (R := AddCommGrpCat.of ℤ) e ≫
        boundaryCorrectionMap x =
      edgeBoundaryWitness x e := by
  exact ((singularSet (X := X)).isColimitChainComplexXCofan
    (AddCommGrpCat.of ℤ) 1).fac
      (Limits.Cofan.mk _ (edgeBoundaryWitness x)) (Discrete.mk e)

private lemma boundaryCorrectionMap_d [PathConnectedSpace X] (x : X) :
    boundaryCorrectionMap x ≫ (integralChains (X := X)).d 2 1 =
      basedLoopChainMap x - 𝟙 _ +
        (integralChains (X := X)).d 1 0 ≫ connectorChainMap x := by
  apply (singularSet (X := X)).chainComplex_hom_ext
  intro e
  rw [← Category.assoc, ιChainComplex_boundaryCorrectionMap,
    edgeBoundaryWitness_d]
  simp only [Preadditive.comp_add, Preadditive.comp_sub, Category.comp_id,
    ιChainComplex_basedLoopChainMap]
  rw [← Category.assoc, (singularSet (X := X)).ιChainComplex_d]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp,
    ιChainComplex_connectorChainMap]
  dsimp only [basedLoopGeneratorMorphism, connectorGeneratorMorphism,
    sourceConnector, targetConnector]
  simp [Fin.sum_univ_two]
  abel

private lemma cycles_basedLoopChainMap_sub [PathConnectedSpace X] (x : X) :
    (integralChains (X := X)).iCycles 1 ≫ basedLoopChainMap x -
        (integralChains (X := X)).iCycles 1 =
      ((integralChains (X := X)).iCycles 1 ≫ boundaryCorrectionMap x) ≫
        (integralChains (X := X)).d 2 1 := by
  rw [Category.assoc, boundaryCorrectionMap_d]
  simp [Preadditive.comp_add, Preadditive.comp_sub]

private lemma cycles_basedLoopHomologyMap [PathConnectedSpace X] (x : X) :
    (integralChains (X := X)).iCycles 1 ≫ basedLoopHomologyMap x =
      (integralChains (X := X)).homologyπ 1 := by
  let k :=
    (integralChains (X := X)).iCycles 1 ≫ basedLoopChainMap x -
      (integralChains (X := X)).iCycles 1
  have hk : k ≫ (integralChains (X := X)).d 1 0 = 0 := by
    dsimp only [k]
    simp only [Preadditive.sub_comp, Category.assoc, basedLoopChainMap_d,
      (integralChains (X := X)).iCycles_d]
    simp
  have hb := (integralChains (X := X)).liftCycles_homologyπ_eq_zero_of_boundary
    k 0 (by simp)
    ((integralChains (X := X)).iCycles 1 ≫ boundaryCorrectionMap x)
    (cycles_basedLoopChainMap_sub x)
  have hlift :
      (integralChains (X := X)).iCycles 1 ≫
          (integralChains (X := X)).liftCycles
            (basedLoopChainMap x) 0 (by simp) (basedLoopChainMap_d x) - 𝟙 _ =
        (integralChains (X := X)).liftCycles k 0 (by simp) hk := by
    rw [← cancel_mono ((integralChains (X := X)).iCycles 1)]
    dsimp only [k]
    simp [Preadditive.sub_comp, Category.assoc]
  have hb' :
      (integralChains (X := X)).iCycles 1 ≫ basedLoopHomologyMap x -
          (integralChains (X := X)).homologyπ 1 = 0 := by
    calc
      (integralChains (X := X)).iCycles 1 ≫ basedLoopHomologyMap x -
          (integralChains (X := X)).homologyπ 1 =
          ((integralChains (X := X)).iCycles 1 ≫
              (integralChains (X := X)).liftCycles
                (basedLoopChainMap x) 0 (by simp) (basedLoopChainMap_d x) - 𝟙 _) ≫
            (integralChains (X := X)).homologyπ 1 := by
              simp [basedLoopHomologyMap, Preadditive.sub_comp, Category.assoc]
      _ = (integralChains (X := X)).liftCycles k 0 (by simp) hk ≫
            (integralChains (X := X)).homologyπ 1 := by rw [hlift]
      _ = 0 := hb
  exact sub_eq_zero.mp hb'

private lemma hurewiczBackward_hurewiczForward [PathConnectedSpace X] (x : X) :
    hurewiczBackward x ≫ hurewiczForwardMorphism x = 𝟙 _ := by
  rw [← cancel_epi ((integralChains (X := X)).homologyπ 1)]
  calc
    (integralChains (X := X)).homologyπ 1 ≫
        (hurewiczBackward x ≫ hurewiczForwardMorphism x) =
      ((integralChains (X := X)).homologyπ 1 ≫ hurewiczBackward x) ≫
        hurewiczForwardMorphism x := by rw [Category.assoc]
    _ = ((integralChains (X := X)).iCycles 1 ≫ basedEdgeMap x) ≫
        hurewiczForwardMorphism x := by rw [homologyπ_hurewiczBackward]
    _ = (integralChains (X := X)).iCycles 1 ≫
        (basedEdgeMap x ≫ hurewiczForwardMorphism x) := by rw [Category.assoc]
    _ = (integralChains (X := X)).iCycles 1 ≫ basedLoopHomologyMap x := by
      rw [basedEdgeMap_hurewiczForward]
    _ = (integralChains (X := X)).homologyπ 1 := cycles_basedLoopHomologyMap x
    _ = (integralChains (X := X)).homologyπ 1 ≫ 𝟙 _ := by simp

private def hurewiczIso [PathConnectedSpace X] (x : X) :
    AddCommGrpCat.of (Additive (Abelianization (FundamentalGroup X x))) ≅
      (integralChains (X := X)).homology 1 where
  hom := hurewiczForwardMorphism x
  inv := hurewiczBackward x
  hom_inv_id := hurewiczForward_hurewiczBackward x
  inv_hom_id := hurewiczBackward_hurewiczForward x

def hurewiczEquiv [PathConnectedSpace X] (x : X) :
    Additive (Abelianization (FundamentalGroup X x)) ≃+
      (LeanEval.Topology.Hurewicz.IntegralHomology 1 X : Type) :=
  (hurewiczIso x).addCommGroupIsoToAddEquiv

end Submission.Helpers
