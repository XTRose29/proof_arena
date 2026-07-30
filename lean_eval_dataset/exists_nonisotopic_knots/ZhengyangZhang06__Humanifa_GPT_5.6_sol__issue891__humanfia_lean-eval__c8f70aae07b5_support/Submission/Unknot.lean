import Submission.Compactification

open CategoryTheory
open scoped ContinuousMap FundamentalGroupoid unitInterval

namespace Submission.Unknot

noncomputable section

private def mulAtContinuousMap {G : Type*} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] (x : G) : C(G × G, G) :=
  ⟨fun p => p.1 * x⁻¹ * p.2, by fun_prop⟩

private theorem mulAtContinuousMap_basepoint
    {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] (x : G) :
    mulAtContinuousMap x (x, x) = x := by
  simp [mulAtContinuousMap]

private def productFundamentalHom
    {G : Type*} [TopologicalSpace G] (x : G) :
    (FundamentalGroup G x × FundamentalGroup G x) →*
      FundamentalGroup (G × G) (x, x) where
  toFun p := FundamentalGroup.fromPath
    (Path.Homotopic.prod (FundamentalGroup.toPath p.1) (FundamentalGroup.toPath p.2))
  map_one' := by
    change Path.Homotopic.prod (.refl x) (.refl x) = .refl (x, x)
    exact Path.Homotopic.prod_projLeft_projRight (.refl (x, x))
  map_mul' p q := by
    change Path.Homotopic.prod
        ((FundamentalGroup.toPath q.1).trans (FundamentalGroup.toPath p.1))
        ((FundamentalGroup.toPath q.2).trans (FundamentalGroup.toPath p.2)) =
      (Path.Homotopic.prod (FundamentalGroup.toPath q.1) (FundamentalGroup.toPath q.2)).trans
        (Path.Homotopic.prod (FundamentalGroup.toPath p.1) (FundamentalGroup.toPath p.2))
    exact (Path.Homotopic.comp_prod_eq_prod_comp _ _ _ _).symm

private def eckmannHiltonHom
    {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] (x : G) :
    (FundamentalGroup G x × FundamentalGroup G x) →* FundamentalGroup G x :=
  (FundamentalGroup.mapOfEq (mulAtContinuousMap x)
    (mulAtContinuousMap_basepoint x)).comp
    (productFundamentalHom x)

private theorem map_prod_refl_left
    {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (x : G) (q : Path.Homotopic.Quotient x x) :
    FundamentalGroup.mapOfEq (mulAtContinuousMap x) (mulAtContinuousMap_basepoint x)
        (FundamentalGroup.fromPath (Path.Homotopic.prod (.refl x) q)) =
      FundamentalGroup.fromPath q := by
  induction q using Path.Homotopic.Quotient.ind with
  | _ p =>
      rw [← Path.Homotopic.Quotient.mk_refl x,
        Path.Homotopic.prod_lift (Path.refl x) p,
        FundamentalGroup.mapOfEq_apply]
      apply congrArg FundamentalGroup.fromPath
      apply Path.Homotopic.Quotient.eq.mpr
      convert Path.Homotopic.refl p using 1
      ext t
      simp [mulAtContinuousMap]

private theorem map_prod_refl_right
    {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (x : G) (q : Path.Homotopic.Quotient x x) :
    FundamentalGroup.mapOfEq (mulAtContinuousMap x) (mulAtContinuousMap_basepoint x)
        (FundamentalGroup.fromPath (Path.Homotopic.prod q (.refl x))) =
      FundamentalGroup.fromPath q := by
  induction q using Path.Homotopic.Quotient.ind with
  | _ p =>
      rw [← Path.Homotopic.Quotient.mk_refl x,
        Path.Homotopic.prod_lift p (Path.refl x),
        FundamentalGroup.mapOfEq_apply]
      apply congrArg FundamentalGroup.fromPath
      apply Path.Homotopic.Quotient.eq.mpr
      convert Path.Homotopic.refl p using 1
      ext t
      simp [mulAtContinuousMap]

private theorem eckmannHiltonHom_one_left
    {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (x : G) (a : FundamentalGroup G x) : eckmannHiltonHom x (1, a) = a := by
  exact map_prod_refl_left x (FundamentalGroup.toPath a)

private theorem eckmannHiltonHom_one_right
    {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (x : G) (a : FundamentalGroup G x) : eckmannHiltonHom x (a, 1) = a := by
  exact map_prod_refl_right x (FundamentalGroup.toPath a)

/-- The fundamental group at every basepoint of a topological group is abelian. -/
theorem topologicalGroup_hasAbelianFundamentalGroups
    (G : Type*) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] :
    Helpers.HasAbelianFundamentalGroups G := by
  intro x a b
  let star : FundamentalGroup G x → FundamentalGroup G x → FundamentalGroup G x :=
    fun p q => eckmannHiltonHom x (p, q)
  have hstar : EckmannHilton.IsUnital star 1 :=
    EckmannHilton.IsUnital.mk {
      left_id := eckmannHiltonHom_one_left x
      right_id := eckmannHiltonHom_one_right x }
  have hdistrib : ∀ p q r s : FundamentalGroup G x,
      star (p * q) (r * s) = star p r * star q s := by
    intro p q r s
    change eckmannHiltonHom x (p * q, r * s) =
      eckmannHiltonHom x (p, r) * eckmannHiltonHom x (q, s)
    exact (eckmannHiltonHom x).map_mul (p, r) (q, s)
  exact (EckmannHilton.mul_comm hstar EckmannHilton.MulOneClass.isUnital hdistrib).comm a b

private def complexPhase (w : ℂ) (hw : w ≠ 0) : Circle :=
  ⟨w / (‖w‖ : ℂ), by simp [Submonoid.unitSphere, hw]⟩

private def unknotPhase : C(Compactification.SphereUnknotComplement, Circle) where
  toFun q := complexPhase q.1.1.2 q.2
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.div₀
    · fun_prop
    · exact Complex.continuous_ofReal.comp (continuous_norm.comp (by fun_prop))
    · intro q
      exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr q.2)

private def unknotSection : C(Circle, Compactification.SphereUnknotComplement) where
  toFun u := ⟨⟨(0, (u : ℂ)), by simp⟩, Circle.coe_ne_zero u⟩
  continuous_toFun := by fun_prop

private def unknotHomotopyDenom
    (p : I × Compactification.SphereUnknotComplement) : ℝ :=
  √(Complex.normSq (((p.1 : ℝ) : ℂ) * p.2.1.1.1) +
    Complex.normSq p.2.1.1.2)

private theorem unknotHomotopyDenom_pos
    (p : I × Compactification.SphereUnknotComplement) :
    0 < unknotHomotopyDenom p := by
  apply Real.sqrt_pos.2
  exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _)
    (Complex.normSq_pos.mpr p.2.2)

private theorem unknotHomotopyDenom_sq
    (p : I × Compactification.SphereUnknotComplement) :
    unknotHomotopyDenom p * unknotHomotopyDenom p =
      Complex.normSq (((p.1 : ℝ) : ℂ) * p.2.1.1.1) +
        Complex.normSq p.2.1.1.2 := by
  exact Real.mul_self_sqrt (add_nonneg (Complex.normSq_nonneg _)
    (Complex.normSq_nonneg _))

private theorem unknotHomotopyDenom_continuous : Continuous unknotHomotopyDenom := by
  unfold unknotHomotopyDenom
  fun_prop

private def unknotHomotopyPoint
    (p : I × Compactification.SphereUnknotComplement) :
    Compactification.SphereUnknotComplement := by
  let d := unknotHomotopyDenom p
  have hd : d ≠ 0 := (unknotHomotopyDenom_pos p).ne'
  refine ⟨⟨((((p.1 : ℝ) : ℂ) * p.2.1.1.1) / (d : ℂ),
      p.2.1.1.2 / (d : ℂ)), ?_⟩,
    div_ne_zero p.2.2 (Complex.ofReal_ne_zero.mpr hd)⟩
  rw [Complex.normSq_div, Complex.normSq_div, Complex.normSq_mul,
    Complex.normSq_ofReal, Complex.normSq_ofReal]
  have hdsq := unknotHomotopyDenom_sq p
  rw [Complex.normSq_mul, Complex.normSq_ofReal] at hdsq
  dsimp [d] at hd ⊢
  field_simp [hd]
  nlinarith

private theorem unknotHomotopyPoint_continuous : Continuous unknotHomotopyPoint := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  have hfirst : Continuous (fun p : I × Compactification.SphereUnknotComplement =>
      (((p.1 : ℝ) : ℂ) * p.2.1.1.1) / (unknotHomotopyDenom p : ℂ)) := by
    apply Continuous.div₀
    · fun_prop
    · exact Complex.continuous_ofReal.comp unknotHomotopyDenom_continuous
    · intro p
      exact Complex.ofReal_ne_zero.mpr (unknotHomotopyDenom_pos p).ne'
  have hsecond : Continuous (fun p : I × Compactification.SphereUnknotComplement =>
      p.2.1.1.2 / (unknotHomotopyDenom p : ℂ)) := by
    apply Continuous.div₀
    · fun_prop
    · exact Complex.continuous_ofReal.comp unknotHomotopyDenom_continuous
    · intro p
      exact Complex.ofReal_ne_zero.mpr (unknotHomotopyDenom_pos p).ne'
  exact hfirst.prodMk hsecond

private theorem unknotHomotopyPoint_zero
    (q : Compactification.SphereUnknotComplement) :
    unknotHomotopyPoint (0, q) = unknotSection (unknotPhase q) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · simp [unknotHomotopyPoint, unknotSection, unknotPhase]
  · simp [unknotHomotopyPoint, unknotHomotopyDenom, unknotSection, unknotPhase,
      complexPhase, Complex.norm_def]

private theorem unknotHomotopyPoint_one
    (q : Compactification.SphereUnknotComplement) :
    unknotHomotopyPoint (1, q) = q := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · simp [unknotHomotopyPoint, unknotHomotopyDenom, q.1.2]
  · simp [unknotHomotopyPoint, unknotHomotopyDenom, q.1.2]

private def unknotDeformation : ContinuousMap.Homotopy
    (unknotSection.comp unknotPhase)
    (ContinuousMap.id Compactification.SphereUnknotComplement) where
  toFun := unknotHomotopyPoint
  continuous_toFun := unknotHomotopyPoint_continuous
  map_zero_left := unknotHomotopyPoint_zero
  map_one_left := unknotHomotopyPoint_one

private theorem unknotPhase_section : unknotPhase.comp unknotSection =
    ContinuousMap.id Circle := by
  ext u
  simp [unknotPhase, unknotSection, complexPhase]

private def sphereUnknotHomotopyEquiv :
    Compactification.SphereUnknotComplement ≃ₕ Circle where
  toFun := unknotPhase
  invFun := unknotSection
  left_inv := ⟨unknotDeformation⟩
  right_inv := by
    rw [unknotPhase_section]

private noncomputable def fundamentalGroupMulEquivOfHomotopyEquiv
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (e x) := by
  let E := FundamentalGroupoidFunctor.equivOfHomotopyEquiv e
  exact MulEquiv.ofBijective (E.functor.mapEnd (FundamentalGroupoid.mk x))
    (E.fullyFaithfulFunctor.map_bijective _ _)

private theorem hasAbelianFundamentalGroups_homotopyEquiv_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) :
    Helpers.HasAbelianFundamentalGroups X ↔
      Helpers.HasAbelianFundamentalGroups Y := by
  constructor
  · intro h y a b
    let g := fundamentalGroupMulEquivOfHomotopyEquiv e.symm y
    apply g.injective
    simpa only [map_mul] using h (e.symm y) (g a) (g b)
  · intro h x a b
    let g := fundamentalGroupMulEquivOfHomotopyEquiv e x
    apply g.injective
    simpa only [map_mul] using h (e x) (g a) (g b)

/-- The complement of the compactified round knot has abelian fundamental groups. -/
theorem roundCompactComplement_hasAbelianFundamentalGroups :
    Helpers.HasAbelianFundamentalGroups
      (Compactification.CompactComplement Helpers.roundCircle) := by
  let e := Compactification.unknotCompactComplementHomeomorph.toHomotopyEquiv.trans
    sphereUnknotHomotopyEquiv
  exact (hasAbelianFundamentalGroups_homotopyEquiv_iff e).mpr
    (topologicalGroup_hasAbelianFundamentalGroups Circle)

end

end Submission.Unknot
