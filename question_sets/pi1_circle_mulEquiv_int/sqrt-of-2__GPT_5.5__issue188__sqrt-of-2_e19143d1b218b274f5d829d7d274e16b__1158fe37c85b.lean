import Mathlib

namespace Submission

open FundamentalGroup Path.Homotopic.Quotient

noncomputable def circleExpBase : Circle.exp ⁻¹' ({1} : Set Circle) :=
  ⟨0, by simp [Circle.exp_zero]⟩

noncomputable def circleExpFiberEquivInt : Circle.exp ⁻¹' ({1} : Set Circle) ≃ ℤ where
  toFun x := Classical.choose (Circle.exp_eq_one.mp x.2)
  invFun n := ⟨n * (2 * Real.pi), Circle.exp_eq_one.mpr ⟨n, rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    exact (Classical.choose_spec (Circle.exp_eq_one.mp x.2)).symm
  right_inv n := by
    dsimp
    let h := Classical.choose_spec (Circle.exp_eq_one.mp
      ((⟨n * (2 * Real.pi), Circle.exp_eq_one.mpr ⟨n, rfl⟩⟩ :
        Circle.exp ⁻¹' ({1} : Set Circle))).2)
    have h' : (Classical.choose (Circle.exp_eq_one.mp
      ((⟨n * (2 * Real.pi), Circle.exp_eq_one.mpr ⟨n, rfl⟩⟩ :
        Circle.exp ⁻¹' ({1} : Set Circle))).2)) * (2 * Real.pi) = n * (2 * Real.pi) := by
      simpa using h
    have hc : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have hreal :
        ((Classical.choose (Circle.exp_eq_one.mp
          ((⟨n * (2 * Real.pi), Circle.exp_eq_one.mpr ⟨n, rfl⟩⟩ :
            Circle.exp ⁻¹' ({1} : Set Circle))).2) : ℤ) : ℝ) = (n : ℝ) :=
      (mul_left_injective₀ hc) h'
    exact Int.cast_injective hreal

lemma circleExpFiberEquivInt_spec (e : Circle.exp ⁻¹' ({1} : Set Circle)) :
    ((circleExpFiberEquivInt e : ℤ) : ℝ) * (2 * Real.pi) = e.1 := by
  exact (Classical.choose_spec (Circle.exp_eq_one.mp e.2)).symm

lemma circleExpFiberEquivInt_eq_add_of_coe {a b c : Circle.exp ⁻¹' ({1} : Set Circle)}
    (h : c.1 = a.1 + b.1) :
    circleExpFiberEquivInt c = circleExpFiberEquivInt a + circleExpFiberEquivInt b := by
  apply (Int.cast_injective (α := ℝ))
  have hc : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  apply mul_left_injective₀ hc
  calc
    ((circleExpFiberEquivInt c : ℤ) : ℝ) * (2 * Real.pi) = c.1 :=
      circleExpFiberEquivInt_spec c
    _ = a.1 + b.1 := h
    _ = ((circleExpFiberEquivInt a : ℤ) : ℝ) * (2 * Real.pi) +
        ((circleExpFiberEquivInt b : ℤ) : ℝ) * (2 * Real.pi) := by
      rw [circleExpFiberEquivInt_spec a, circleExpFiberEquivInt_spec b]
    _ = (((circleExpFiberEquivInt a + circleExpFiberEquivInt b : ℤ) : ℝ) *
        (2 * Real.pi)) := by
      rw [Int.cast_add]
      ring

@[simp] lemma circleExpFiberEquivInt_base :
    circleExpFiberEquivInt circleExpBase = 0 := by
  change Classical.choose (Circle.exp_eq_one.mp circleExpBase.2) = 0
  have h := Classical.choose_spec (Circle.exp_eq_one.mp circleExpBase.2)
  have h' : ((Classical.choose (Circle.exp_eq_one.mp circleExpBase.2) : ℤ) : ℝ) *
      (2 * Real.pi) = ((0 : ℤ) : ℝ) * (2 * Real.pi) := by
    simpa [circleExpBase] using h
  have hc : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hreal : ((Classical.choose (Circle.exp_eq_one.mp circleExpBase.2) : ℤ) : ℝ) =
      ((0 : ℤ) : ℝ) :=
    (mul_left_injective₀ hc) h'
  exact Int.cast_injective hreal

lemma circleExp_liftPath_translate (γ : Path (1 : Circle) (1 : Circle))
    (e : Circle.exp ⁻¹' ({1} : Set Circle)) :
    Circle.isCoveringMap_exp.liftPath γ e (γ.source.trans e.2.symm) =
      ⟨fun t => e.1 + Circle.isCoveringMap_exp.liftPath γ circleExpBase
        (γ.source.trans circleExpBase.2.symm) t, by fun_prop⟩ := by
  refine ((Circle.isCoveringMap_exp.eq_liftPath_iff' _).mpr ⟨?_, ?_⟩).symm
  · ext t
    simp only [Function.comp_apply, ContinuousMap.coe_mk]
    rw [Circle.exp_add]
    have he : Circle.exp e.1 = 1 := by
      simpa only [Set.mem_singleton_iff] using e.2
    rw [he, one_mul]
    exact congr_arg Subtype.val (congr_fun
      (Circle.isCoveringMap_exp.liftPath_lifts γ circleExpBase
        (γ.source.trans circleExpBase.2.symm)) t)
  · simp [circleExpBase, Circle.isCoveringMap_exp.liftPath_zero]

lemma circleExp_monodromy_translate (γ : Path.Homotopic.Quotient (1 : Circle) (1 : Circle))
    (e : Circle.exp ⁻¹' ({1} : Set Circle)) :
    (Circle.isCoveringMap_exp.monodromy γ e).1 =
      e.1 + (Circle.isCoveringMap_exp.monodromy γ circleExpBase).1 := by
  obtain ⟨γ⟩ := γ
  change (Circle.isCoveringMap_exp.liftPath γ e (γ.source.trans e.2.symm) 1) =
    e.1 + Circle.isCoveringMap_exp.liftPath γ circleExpBase
      (γ.source.trans circleExpBase.2.symm) 1
  rw [circleExp_liftPath_translate]
  rfl

noncomputable def circleExpIntPath (n : ℤ) : Path (0 : ℝ) (n * (2 * Real.pi)) :=
  Path.segment 0 (n * (2 * Real.pi))

noncomputable def circleLoopOfInt (n : ℤ) : Path (1 : Circle) (1 : Circle) :=
  ((circleExpIntPath n).map Circle.exp.continuous).cast
    (by simp [Circle.exp_zero])
    (by
      change (1 : Circle) = Circle.exp (n * (2 * Real.pi))
      exact (Circle.exp_eq_one.mpr ⟨n, rfl⟩).symm)

lemma circleLoopOfInt_monodromy (n : ℤ) :
    Circle.isCoveringMap_exp.monodromy (Path.Homotopic.Quotient.mk (circleLoopOfInt n))
      circleExpBase =
    (⟨n * (2 * Real.pi), Circle.exp_eq_one.mpr ⟨n, rfl⟩⟩ :
      Circle.exp ⁻¹' ({1} : Set Circle)) := by
  apply Subtype.ext
  change (Circle.isCoveringMap_exp.liftPath (circleLoopOfInt n) circleExpBase
      ((circleLoopOfInt n).source.trans circleExpBase.2.symm) 1) = n * (2 * Real.pi)
  have hLift :
      Circle.isCoveringMap_exp.liftPath (circleLoopOfInt n) circleExpBase
        ((circleLoopOfInt n).source.trans circleExpBase.2.symm) =
      (circleExpIntPath n).toContinuousMap := by
    refine ((Circle.isCoveringMap_exp.eq_liftPath_iff' _).mpr ⟨?_, ?_⟩).symm
    · ext t
      simp [circleLoopOfInt, circleExpIntPath]
    · simp [circleExpBase, circleExpIntPath]
  rw [hLift]
  simp [circleExpIntPath]

noncomputable def pi1CircleWindingHom :
    FundamentalGroup Circle (1 : Circle) →* Multiplicative ℤ where
  toFun γ :=
    Multiplicative.ofAdd
      (circleExpFiberEquivInt (Circle.isCoveringMap_exp.monodromy γ.toPath circleExpBase))
  map_one' := by
    rw [show (toPath (1 : FundamentalGroup Circle (1 : Circle))) =
      Path.Homotopic.Quotient.refl (1 : Circle) by rfl]
    rw [show Circle.isCoveringMap_exp.monodromy (Path.Homotopic.Quotient.refl (1 : Circle)) =
      id by exact Circle.isCoveringMap_exp.monodromy_refl]
    simp
  map_mul' γ δ := by
    rw [show (toPath (γ * δ)) = Path.Homotopic.Quotient.trans δ.toPath γ.toPath by rfl]
    rw [Circle.isCoveringMap_exp.monodromy_trans_apply]
    rw [circleExpFiberEquivInt_eq_add_of_coe
      (circleExp_monodromy_translate γ.toPath
        (Circle.isCoveringMap_exp.monodromy δ.toPath circleExpBase))]
    simp [add_comm]

lemma pi1CircleWindingHom_surjective : Function.Surjective pi1CircleWindingHom := by
  intro m
  let n : ℤ := Multiplicative.toAdd m
  refine ⟨FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
    (circleLoopOfInt n)), ?_⟩
  simp only [pi1CircleWindingHom, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [circleLoopOfInt_monodromy]
  change Multiplicative.ofAdd (circleExpFiberEquivInt
    (circleExpFiberEquivInt.symm n)) = m
  simp [n]

lemma circleExp_monodromy_eq_refl_of_eq_base
    (γ : Path.Homotopic.Quotient (1 : Circle) (1 : Circle))
    (hγ : Circle.isCoveringMap_exp.monodromy γ circleExpBase = circleExpBase) :
    γ = Path.Homotopic.Quotient.refl (1 : Circle) := by
  obtain ⟨γ⟩ := γ
  let Γ := Circle.isCoveringMap_exp.liftPath γ circleExpBase
    (γ.source.trans circleExpBase.2.symm)
  have hΓ0 : Γ 0 = 0 := by
    simpa [Γ, circleExpBase] using
      (Circle.isCoveringMap_exp.liftPath_zero γ circleExpBase
        (γ.source.trans circleExpBase.2.symm))
  have hΓ1 : Γ 1 = 0 := by
    exact congr_arg Subtype.val hγ
  let Γpath : Path (0 : ℝ) (0 : ℝ) := ⟨Γ, hΓ0, hΓ1⟩
  have hmap :
      (Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.mk Γpath) Circle.exp).cast
        (by simp [Circle.exp_zero]) (by simp [Circle.exp_zero]) =
      Path.Homotopic.Quotient.mk γ := by
    rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast]
    apply congr_arg Path.Homotopic.Quotient.mk
    ext t
    exact congr_arg Subtype.val
      (congr_fun (Circle.isCoveringMap_exp.liftPath_lifts γ circleExpBase
        (γ.source.trans circleExpBase.2.symm)) t)
  have hΓpath : Path.Homotopic.Quotient.mk Γpath =
      Path.Homotopic.Quotient.refl (0 : ℝ) := by
    exact Quotient.sound (SimplyConnectedSpace.paths_homotopic Γpath (Path.refl 0))
  change Path.Homotopic.Quotient.mk γ = Path.Homotopic.Quotient.refl (1 : Circle)
  rw [← hmap, hΓpath]
  change Path.Homotopic.Quotient.mk
      (((Path.refl (0 : ℝ)).map Circle.exp.continuous).cast
        (by simp [Circle.exp_zero]) (by simp [Circle.exp_zero])) =
    Path.Homotopic.Quotient.mk (Path.refl (1 : Circle))
  apply congr_arg Path.Homotopic.Quotient.mk
  ext t
  simp [Circle.exp_zero]

lemma pi1CircleWindingHom_eq_one {γ : FundamentalGroup Circle (1 : Circle)}
    (hγ : pi1CircleWindingHom γ = 1) : γ = 1 := by
  have hwind :
      circleExpFiberEquivInt (Circle.isCoveringMap_exp.monodromy γ.toPath circleExpBase) = 0 := by
    simpa [pi1CircleWindingHom] using congr_arg Multiplicative.toAdd hγ
  have hbase : Circle.isCoveringMap_exp.monodromy γ.toPath circleExpBase = circleExpBase := by
    apply circleExpFiberEquivInt.injective
    simpa using hwind
  have hpath := circleExp_monodromy_eq_refl_of_eq_base γ.toPath hbase
  exact hpath

lemma pi1CircleWindingHom_injective : Function.Injective pi1CircleWindingHom := by
  intro γ δ hγδ
  have hker : pi1CircleWindingHom (γ * δ⁻¹) = 1 := by
    rw [map_mul, map_inv, hγδ]
    simp
  have h : γ * δ⁻¹ = 1 := pi1CircleWindingHom_eq_one hker
  calc
    γ = (γ * δ⁻¹) * δ := by group
    _ = δ := by rw [h]; simp

theorem pi1_circle_mulEquiv_int :
    Nonempty (HomotopyGroup.Pi 1 Circle (1 : Circle) ≃* Multiplicative ℤ) := by
  exact ⟨(HomotopyGroup.pi1MulEquivFundamentalGroup (X := Circle) (x := (1 : Circle))).trans
    (MulEquiv.ofBijective pi1CircleWindingHom
      ⟨pi1CircleWindingHom_injective, pi1CircleWindingHom_surjective⟩)⟩

end Submission
