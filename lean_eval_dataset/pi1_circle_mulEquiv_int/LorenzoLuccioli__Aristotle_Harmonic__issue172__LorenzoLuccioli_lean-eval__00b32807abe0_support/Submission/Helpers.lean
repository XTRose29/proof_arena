import Mathlib

namespace Submission.Helpers

open Topology unitInterval

noncomputable def covMap : IsCoveringMap (⇑Circle.exp) :=
  Circle.isCoveringMap_exp

noncomputable def fiberBasepoint : (⇑Circle.exp) ⁻¹' {(1 : Circle)} :=
  ⟨0, by simp [Circle.exp_zero]⟩

noncomputable def fiberPoint (n : ℤ) : (⇑Circle.exp) ⁻¹' {(1 : Circle)} :=
  ⟨n * (2 * Real.pi), by
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact Circle.exp_int_mul_two_pi n⟩

lemma fiberPoint_val (n : ℤ) : (fiberPoint n).1 = n * (2 * Real.pi) := rfl

lemma fiberPoint_zero : fiberPoint 0 = fiberBasepoint := by
  ext; simp [fiberPoint, fiberBasepoint]

noncomputable def fiberToInt (e : (⇑Circle.exp) ⁻¹' {(1 : Circle)}) : ℤ :=
  (Circle.exp_eq_one.mp (show Circle.exp e.1 = 1 from e.2)).choose

lemma fiberToInt_spec (e : (⇑Circle.exp) ⁻¹' {(1 : Circle)}) :
    e.1 = fiberToInt e * (2 * Real.pi) :=
  (Circle.exp_eq_one.mp (show Circle.exp e.1 = 1 from e.2)).choose_spec

lemma fiberPoint_toInt (n : ℤ) : fiberToInt (fiberPoint n) = n := by
  have h := fiberToInt_spec (fiberPoint n)
  simp only [fiberPoint_val] at h
  symm
  exact_mod_cast mul_right_cancel₀ (show (2 * Real.pi : ℝ) ≠ 0 by positivity) h

lemma fiberToInt_fiberPoint (e : (⇑Circle.exp) ⁻¹' {(1 : Circle)}) :
    fiberPoint (fiberToInt e) = e :=
  Subtype.ext (by simp [fiberPoint_val, ← fiberToInt_spec])

lemma fiberToInt_basepoint : fiberToInt fiberBasepoint = 0 := by
  rw [← fiberPoint_zero, fiberPoint_toInt]

noncomputable def windingNumber (γ : FundamentalGroup Circle (1 : Circle)) : ℤ :=
  fiberToInt (covMap.monodromy γ fiberBasepoint)

noncomputable def standardLoop (n : ℤ) : Path (1 : Circle) 1 where
  toFun t := Circle.exp (n * (2 * Real.pi) * t)
  continuous_toFun := Circle.exp.continuous.comp (by fun_prop)
  source' := by simp [Circle.exp_zero]
  target' := by simp only [Set.Icc.coe_one, mul_one]; exact Circle.exp_int_mul_two_pi n

noncomputable def intToLoop (n : ℤ) : FundamentalGroup Circle (1 : Circle) :=
  ⟦standardLoop n⟧

lemma monodromy_standardLoop (n : ℤ) :
    covMap.monodromy (intToLoop n) fiberBasepoint = fiberPoint n := by
  simp +decide [ IsCoveringMap.monodromy ];
  erw [ Quotient.lift_mk ];
  congr;
  have := IsCoveringMap.eq_liftPath_iff' ( p := Circle.exp ) ( γ := ContinuousMap.mk ( fun t : unitInterval => Circle.exp ( n * ( 2 * Real.pi ) * t ) ) ( by continuity ) ) ( e := 0 ) ( Γ := ContinuousMap.mk ( fun t : unitInterval => n * ( 2 * Real.pi ) * t ) ( by continuity ) );
  exact congr_arg ( fun f : C(unitInterval, ℝ) => f 1 ) ( this _ ( by norm_num ) |>.2 ⟨ by ext; norm_num, by norm_num ⟩ ) ▸ by norm_num;

lemma windingNumber_standardLoop (n : ℤ) : windingNumber (intToLoop n) = n := by
  simp only [windingNumber, monodromy_standardLoop, fiberPoint_toInt]

lemma monodromy_free (γ : FundamentalGroup Circle (1 : Circle))
    (h : covMap.monodromy γ fiberBasepoint = fiberBasepoint) : γ = 1 := by
  obtain ⟨ γ', hγ' ⟩ := γ;
  -- Let's denote the lift of γ by θ.
  obtain ⟨θ, hθ⟩ : ∃ θ : C(I, ℝ), Circle.exp ∘ θ = γ' ∧ θ 0 = 0 ∧ θ 1 = 0 := by
    refine' ⟨ _, _, _, _ ⟩;
    exact ⟨ covMap.liftPath ( Path.mk γ' hγ' ‹_› ) 0 ( by simp [ Circle.exp_zero ] ), by
      fun_prop ⟩
    all_goals generalize_proofs at *;
    · convert covMap.liftPath_lifts ( Path.mk γ' hγ' ‹_› ) 0 ( by simp [ Circle.exp_zero ] ) using 1;
    · convert covMap.liftPath_zero _ _ _;
    · convert congr_arg Subtype.val h using 1;
  -- Since θ is a path in ℝ from 0 to 0, it is homotopic to the constant path at 0.
  have hθ_homotopic : Path.Homotopic (Path.mk θ (by
  exact hθ.2.1) (by
  exact hθ.2.2)) (Path.refl 0) := by
    all_goals generalize_proofs at *;
    exact SimplyConnectedSpace.paths_homotopic _ _
  generalize_proofs at *;
  convert Path.Homotopic.map hθ_homotopic Circle.exp using 1;
  constructor <;> intro h <;> simp_all +decide [ Path.Homotopic ];
  · exact ⟨ hθ_homotopic.some.map Circle.exp ⟩;
  · convert Quotient.sound _;
    constructor;
    convert h.some using 1;
    · exact Eq.symm Circle.exp_zero;
    · exact Eq.symm Circle.exp_zero;
    · congr! 1;
      exact ContinuousMap.ext fun x => hθ.1 ▸ rfl;
    · exact congr_arg_heq Path.refl ‹_›

lemma monodromy_translate (γ : FundamentalGroup Circle (1 : Circle))
    (e : (⇑Circle.exp) ⁻¹' {(1 : Circle)}) :
    (covMap.monodromy γ e).1 = (covMap.monodromy γ fiberBasepoint).1 + e.1 := by
  -- By definition of $covMap.monodromy$, we know that
  obtain ⟨γ', hγ'⟩ : ∃ γ' : Path (1 : Circle) (1 : Circle), γ = ⟦γ'⟧ := by
    rcases γ with ⟨ ⟩ ; aesop;
  -- By definition of $covMap.monodromy$, we know that $(covMap.monodromy γ fiberBasepoint).val$ is the lift of $\gamma'$ starting at $0$.
  set θ₀ := covMap.liftPath γ' 0 (by
  aesop) with hθ₀
  generalize_proofs at *;
  -- By definition of $covMap.monodromy$, we know that $(covMap.monodromy γ e).val$ is the lift of $\gamma'$ starting at $e.val$.
  set θ_e := covMap.liftPath γ' e.val (by
  aesop) with hθ_e
  generalize_proofs at *;
  have h_lift_eq : θ_e = θ₀ + ContinuousMap.const I e.val := by
    apply ContinuousMap.ext
    intro t
    simp [hθ₀, hθ_e];
    have := @IsCoveringMap.eq_liftPath_iff';
    specialize this covMap ( show ( γ' : C(I, Circle) ) 0 = Circle.exp e.val from by assumption ) ( Γ := θ₀ + ContinuousMap.const I e.val ) ; simp_all +decide [ funext_iff, ContinuousMap.ext_iff ];
    convert this.mpr ⟨ _, _ ⟩ t t.2.1 t.2.2 |> Eq.symm using 1;
    · intro a ha hb; have := covMap.liftPath_lifts ( γ' : C(I, Circle) ) 0 ‹_›; simp_all +decide [ funext_iff, ContinuousMap.ext_iff ] ;
      exact e.2;
    · exact IsCoveringMap.liftPath_zero covMap (↑γ') 0 _;
  convert congr_arg ( fun f : C(I, ℝ) => f 1 ) h_lift_eq using 1;
  · rw [ hγ' ];
    exact Real.ext_cauchy rfl;
  · aesop

lemma monodromy_eval_injective (α β : FundamentalGroup Circle (1 : Circle))
    (h : covMap.monodromy α fiberBasepoint = covMap.monodromy β fiberBasepoint) :
    α = β := by
  -- By the properties of the monodromy homomorphism, we know that if $\alpha = \beta$, then their monodromy around any loop is the same.
  have h_monodromy_eq : covMap.monodromy (α * β⁻¹) fiberBasepoint = fiberBasepoint := by
    have h_eq : (covMap.monodromy (α * β⁻¹)) (covMap.monodromy β fiberBasepoint) = covMap.monodromy β fiberBasepoint := by
      convert covMap.monodromy_trans_apply ( β.symm ) ( α ) ( covMap.monodromy β fiberBasepoint ) using 1;
      convert h.symm using 1;
      rw [ show covMap.monodromy ( Path.Homotopic.Quotient.symm β ) ( covMap.monodromy β fiberBasepoint ) = fiberBasepoint from ?_ ];
      have h_monodromy_b_inv : covMap.monodromy (β.trans β.symm) fiberBasepoint = fiberBasepoint := by
        -- Since the trans of β and its symm is the identity, the monodromy of the identity is the identity map.
        have h_id : Path.Homotopic.Quotient.trans β (Path.Homotopic.Quotient.symm β) = Path.Homotopic.Quotient.refl (1 : Circle) := by
          exact Path.Homotopic.Quotient.trans_symm β;
        rw [ h_id, covMap.monodromy_refl ];
        rfl;
      convert h_monodromy_b_inv using 1;
      exact Eq.symm (IsCoveringMap.monodromy_trans_apply covMap β (Path.Homotopic.Quotient.symm β) fiberBasepoint);
    have h_eq : (covMap.monodromy (α * β⁻¹)) (covMap.monodromy β fiberBasepoint) = (covMap.monodromy (α * β⁻¹)) fiberBasepoint + (covMap.monodromy β fiberBasepoint).1 := by
      convert monodromy_translate ( α * β⁻¹ ) ( covMap.monodromy β fiberBasepoint ) using 1;
    aesop;
  have := monodromy_free ( α * β⁻¹ ) h_monodromy_eq; simp_all +decide [ mul_eq_one_iff_eq_inv ] ;

lemma intToLoop_windingNumber (γ : FundamentalGroup Circle (1 : Circle)) :
    intToLoop (windingNumber γ) = γ := by
  apply monodromy_eval_injective
  rw [monodromy_standardLoop]
  exact fiberToInt_fiberPoint _

lemma windingNumber_mul (γ δ : FundamentalGroup Circle (1 : Circle)) :
    windingNumber (γ * δ) = windingNumber γ + windingNumber δ := by
  -- By definition of fiberToInt, we know that fiberToInt (covMap.monodromy γ fiberBasepoint) * (2 * Real.pi) = (covMap.monodromy γ fiberBasepoint).val.
  have h_fiberToInt : ∀ e : (⇑Circle.exp) ⁻¹' {(1 : Circle)}, fiberToInt e * (2 * Real.pi) = e.val := by
    exact fun e => fiberToInt_spec e ▸ rfl;
  exact_mod_cast ( by nlinarith [ Real.pi_pos, h_fiberToInt ( covMap.monodromy ( γ * δ ) fiberBasepoint ), h_fiberToInt ( covMap.monodromy γ fiberBasepoint ), h_fiberToInt ( covMap.monodromy δ fiberBasepoint ), monodromy_translate γ ( covMap.monodromy δ fiberBasepoint ), monodromy_translate δ fiberBasepoint, show ( covMap.monodromy ( γ * δ ) fiberBasepoint : ℝ ) = ( covMap.monodromy γ ( covMap.monodromy δ fiberBasepoint ) : ℝ ) from congr_arg Subtype.val ( covMap.monodromy_trans_apply _ _ _ ) ] : ( fiberToInt ( covMap.monodromy ( γ * δ ) fiberBasepoint ) : ℝ ) = fiberToInt ( covMap.monodromy γ fiberBasepoint ) + fiberToInt ( covMap.monodromy δ fiberBasepoint ) )

noncomputable def fundamentalGroupCircleEquiv :
    FundamentalGroup Circle (1 : Circle) ≃* Multiplicative ℤ where
  toFun γ := Multiplicative.ofAdd (windingNumber γ)
  invFun n := intToLoop (Multiplicative.toAdd n)
  left_inv γ := intToLoop_windingNumber γ
  right_inv n := by
    show Multiplicative.ofAdd (windingNumber (intToLoop (Multiplicative.toAdd n))) = n
    rw [windingNumber_standardLoop]; simp
  map_mul' γ δ := by
    show Multiplicative.ofAdd (windingNumber (γ * δ)) =
      Multiplicative.ofAdd (windingNumber γ) * Multiplicative.ofAdd (windingNumber δ)
    rw [windingNumber_mul, ofAdd_add]

noncomputable def pi1MulEquivFundamentalGroup :
    HomotopyGroup.Pi 1 Circle (1 : Circle) ≃* FundamentalGroup Circle (1 : Circle) := {
  HomotopyGroup.pi1EquivFundamentalGroup with
  map_mul' := by
    intros x y
    simp [HomotopyGroup.pi1EquivFundamentalGroup];
    obtain ⟨ x, hx ⟩ := x;
    obtain ⟨ y, hy ⟩ := y;
    erw [ Quotient.eq ];
    refine' ⟨ _, _ ⟩;
    refine' ⟨ _, _, _ ⟩;
    refine' ⟨ fun p => if p.1 = 0 then ( genLoopEquivOfUnique ( Fin 1 ) ⟨ y, hy ⟩ ).trans ( genLoopEquivOfUnique ( Fin 1 ) ⟨ x, hx ⟩ ) p.2 else ( genLoopEquivOfUnique ( Fin 1 ) ⟨ y, hy ⟩ ).trans ( genLoopEquivOfUnique ( Fin 1 ) ⟨ x, hx ⟩ ) p.2, _ ⟩;
    all_goals norm_num [ genLoopEquivOfUnique ];
    · refine' Continuous.comp _ _;
      · exact?;
      · exact continuous_snd;
    · intro a ha hb; simp +decide [ GenLoop.loopHomeo, GenLoop.toLoop ] ;
      simp +decide [ GenLoop.fromLoop, Path.trans ];
      split_ifs <;> simp +decide [ Path.extend ];
      · simp +decide [ Set.IccExtend, Path.extend ];
        congr ; ext i ; fin_cases i ; simp +decide [ Cube.insertAt ];
        simp +decide [ Fin.ext_iff, Set.projIcc ];
      · simp +decide [ Set.IccExtend ];
        congr;
        ext i; fin_cases i; simp +decide [ Cube.insertAt ] ;
        simp +decide [ Fin.ext_iff, Set.projIcc ];
    · simp +decide [ GenLoop.fromLoop, Path.trans ];
      norm_num [ GenLoop.const ]
}

theorem main_result :
    Nonempty (HomotopyGroup.Pi 1 Circle (1 : Circle) ≃* Multiplicative ℤ) :=
  ⟨pi1MulEquivFundamentalGroup.trans fundamentalGroupCircleEquiv⟩

end Submission.Helpers