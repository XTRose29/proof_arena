import Mathlib

namespace Submission

open scoped Topology unitInterval
open Circle

noncomputable section

/-
Strategy: We construct a MulEquiv from FundamentalGroup Circle 1 to Multiplicative ℤ.

The covering map Circle.exp : ℝ → Circle satisfies:
- Circle.exp 0 = 1
- Circle.exp is a covering map (Circle.isCoveringMap_exp)
- Circle.exp t = 1 ↔ ∃ n : ℤ, t = 2 * π * n
- ℝ is simply connected

The winding number map: given a loop γ at 1, lift it to ℝ starting at 0.
The endpoint is 2πn for some n ∈ ℤ. Map γ to n.

This is a group isomorphism.
-/

private abbrev cov := Circle.isCoveringMap_exp

/-
Circle.exp t = 1 iff t is a multiple of 2π
-/
private lemma circle_exp_eq_one_iff (t : ℝ) :
    Circle.exp t = 1 ↔ ∃ n : ℤ, t = 2 * Real.pi * n := by
  grind +suggestions

-- Extract integer from fiber element
private noncomputable def fiberToInt (t : ℝ) (ht : Circle.exp t = 1) : ℤ :=
  ((circle_exp_eq_one_iff t).mp ht).choose

private lemma fiberToInt_spec (t : ℝ) (ht : Circle.exp t = 1) :
    t = 2 * Real.pi * (fiberToInt t ht : ℝ) :=
  ((circle_exp_eq_one_iff t).mp ht).choose_spec

-- Integer maps back to fiber
private lemma int_to_fiber (n : ℤ) : Circle.exp (2 * Real.pi * n) = 1 :=
  (circle_exp_eq_one_iff _).mpr ⟨n, rfl⟩

/-
fiberToInt is injective (since 2π ≠ 0)
-/
private lemma fiberToInt_injective (t₁ t₂ : ℝ) (h₁ : Circle.exp t₁ = 1)
    (h₂ : Circle.exp t₂ = 1) (heq : fiberToInt t₁ h₁ = fiberToInt t₂ h₂) : t₁ = t₂ := by
  rw [ fiberToInt_spec t₁ h₁, fiberToInt_spec t₂ h₂, heq ]

/-
fiberToInt is additive: if Circle.exp(t₁ + t₂) = 1 with t₁, t₂ in fiber,
then fiberToInt(t₁ + t₂) = fiberToInt(t₁) + fiberToInt(t₂)
-/
private lemma fiberToInt_add (t₁ t₂ : ℝ) (h₁ : Circle.exp t₁ = 1)
    (h₂ : Circle.exp t₂ = 1) :
    fiberToInt (t₁ + t₂) (by rw [Circle.exp_add, h₁, h₂, one_mul]) =
    fiberToInt t₁ h₁ + fiberToInt t₂ h₂ := by
  -- From fiberToInt_spec, t₁ = 2π * n₁ and t₂ = 2π * n₂, so t₁ + t₂ = 2π * (n₁ + n₂).
  have h3 : t₁ + t₂ = 2 * Real.pi * (fiberToInt t₁ h₁ + fiberToInt t₂ h₂) := by
    linarith [ fiberToInt_spec t₁ h₁, fiberToInt_spec t₂ h₂ ];
  -- By uniqueness (fiberToInt_injective), fiberToInt(t₁ + t₂) = n₁ + n₂.
  apply Eq.symm;
  apply Eq.symm; exact (by
    have := fiberToInt_spec (t₁ + t₂) (by
    convert int_to_fiber ( fiberToInt t₁ h₁ + fiberToInt t₂ h₂ ) using 1 ; push_cast [ h3 ] ; ring)
    all_goals generalize_proofs at *;
    exact_mod_cast ( mul_left_cancel₀ ( by positivity : ( 2 * Real.pi : ℝ ) ≠ 0 ) <| by linarith : ( fiberToInt ( t₁ + t₂ ) ‹_› : ℝ ) = fiberToInt t₁ h₁ + fiberToInt t₂ h₂ ))

-- The lift endpoint for a loop
private noncomputable def liftEnd (γ : Path (1 : Circle) 1) : ℝ :=
  cov.liftPath γ.toContinuousMap 0 (by simp [γ.source]) 1

/-
The lift endpoint is in the fiber
-/
private lemma liftEnd_fiber (γ : Path (1 : Circle) 1) :
    Circle.exp (liftEnd γ) = 1 := by
  have := cov.liftPath_lifts γ.toContinuousMap 0 ( by simp +decide [ γ.source ] );
  simpa using congr_fun this 1

/-
Homotopic loops have the same lift endpoint
-/
private lemma liftEnd_homotopic (γ₁ γ₂ : Path (1 : Circle) 1)
    (h : Path.Homotopic γ₁ γ₂) : liftEnd γ₁ = liftEnd γ₂ := by
  apply_rules [ IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel ]

/-
The lift endpoint of the constant loop is 0
-/
private lemma liftEnd_refl : liftEnd (Path.refl 1) = 0 := by
  -- The constant loop at 1 lifts to the constant path at 0 in ℝ.
  have h_const_lift : (cov.liftPath (Path.refl 1).toContinuousMap 0 (by simp)) = ContinuousMap.const _ 0 := by
    have : ((Path.refl 1).toContinuousMap : C(I, Circle)) = ContinuousMap.const _ 1 := by
      aesop
    grind +suggestions;
  exact congr_arg ( fun f => f 1 ) h_const_lift

/-
Key helper: the lift of a path starting at c (in the kernel of exp) equals
the lift starting at 0 plus c.
This uses: exp(x + c) = exp(x) when exp(c) = 1.
-/
private lemma liftPath_translate (γ : C(I, Circle)) (c : ℝ) (hc : Circle.exp c = 1)
    (h0 : γ 0 = Circle.exp 0) (hc' : γ 0 = Circle.exp c) :
    cov.liftPath γ c hc' =
    (ContinuousMap.mk (fun t => cov.liftPath γ 0 h0 t + c) (by fun_prop)) := by
  apply ContinuousMap.ext
  intro t
  simp [cov] at *;
  have h_liftPath_eq : ∀ t : I, Circle.exp ((cov.liftPath γ 0 h0) t + c) = γ t := by
    intro t; have := IsCoveringMap.liftPath_lifts cov γ 0 h0; simp_all +decide [ Circle.exp_add ] ;
    exact congr_fun this t;
  have h_liftPath_eq : cov.liftPath γ c hc' = ContinuousMap.mk (fun t => (cov.liftPath γ 0 h0) t + c) (by
  exact Continuous.add ( by exact? ) continuous_const) := by
    have h_liftPath_eq : Circle.exp ∘ (ContinuousMap.mk (fun t => (cov.liftPath γ 0 h0) t + c) (by
    exact Continuous.add ( by exact? ) continuous_const)) = γ := by
      exact funext h_liftPath_eq
    grind +suggestions;
  exact congr_arg ( fun f => f t ) h_liftPath_eq

/-
The lift endpoint is additive under path composition
Note: in FundamentalGroup, mul(a,b) = b ≫ a = b.trans a as paths
So liftEnd(a.trans b) = liftEnd(a) + liftEnd(b)
-/
private lemma liftEnd_trans (γ₁ γ₂ : Path (1 : Circle) 1) :
    liftEnd (γ₁.trans γ₂) = liftEnd γ₁ + liftEnd γ₂ := by
  rw [ add_comm ];
  -- By definition of monodromy, we have:
  have h_monodromy : (cov.liftPath (γ₁.trans γ₂).toContinuousMap 0 (by simp [γ₁.source]) 1) = (cov.liftPath γ₂.toContinuousMap (cov.liftPath γ₁.toContinuousMap 0 (by simp [γ₁.source]) 1) (by
  simp +decide [ γ₂.source ];
  exact Eq.symm ( liftEnd_fiber γ₁ )) 1) := by
    have := @IsCoveringMap.monodromy_trans_apply;
    convert congr_arg Subtype.val ( this cov ( Quotient.mk'' γ₁ ) ( Quotient.mk'' γ₂ ) ⟨ 0, by simp +decide [ γ₁.source ] ⟩ ) using 1
  generalize_proofs at *;
  unfold liftEnd at *;
  rw [ h_monodromy, liftPath_translate ];
  all_goals norm_num;
  convert liftEnd_fiber γ₁ using 1

-- The map from loops to integers, well-defined on homotopy classes
private noncomputable def windingNum : FundamentalGroup Circle 1 → ℤ :=
  fun γ => Quotient.lift (fun p => fiberToInt (liftEnd p) (liftEnd_fiber p))
    (fun a b h => by
      have heq := liftEnd_homotopic a b (Path.Homotopic.Quotient.eq.mp (Quotient.sound h))
      simp only [heq]) γ

/-
windingNum is a group homomorphism
FundamentalGroup multiplication: a * b = b ≫ a (in categorical sense)
In terms of paths: a * b corresponds to b.trans(a) in some sense
Actually End mul corresponds to ≫ which is Quotient.comp
-/
private lemma windingNum_one : windingNum 1 = 0 := by
  unfold windingNum;
  erw [ show ( 1 : FundamentalGroup Circle 1 ) = Quotient.mk'' ( Path.refl 1 ) from ?_ ];
  · convert fiberToInt_spec 0 _;
    all_goals norm_num [ Circle.exp_zero ];
    erw [ Quotient.lift_mk ] ; norm_num [ liftEnd_refl ];
  · rfl

private lemma windingNum_mul (a b : FundamentalGroup Circle 1) :
    windingNum (a * b) = windingNum a + windingNum b := by
  induction' a using Quotient.ind with a;
  nontriviality;
  induction' b using Quotient.ind with b;
  -- Apply the lemma that the fiberToInt of a sum is the sum of the fiberToInts.
  have h_fiberToInt : fiberToInt (liftEnd (b.trans a)) (liftEnd_fiber (b.trans a)) = fiberToInt (liftEnd b) (liftEnd_fiber b) + fiberToInt (liftEnd a) (liftEnd_fiber a) := by
    grind +suggestions;
  convert h_fiberToInt using 1;
  exact add_comm _ _

/-
windingNum is injective (uses simply-connectedness of ℝ)
-/
set_option maxHeartbeats 800000 in
private lemma windingNum_injective : Function.Injective windingNum := by
  intro a b hab
  obtain ⟨p_a, hp_a⟩ := Quotient.exists_rep a
  obtain ⟨p_b, hp_b⟩ := Quotient.exists_rep b
  have h_lift : liftEnd p_a = liftEnd p_b := by
    exact fiberToInt_injective _ _ ( liftEnd_fiber p_a ) ( liftEnd_fiber p_b ) <| by aesop;
  have h_homotopic : Path.Homotopic p_a p_b := by
    -- Since the lifts of p_a and p_b are homotopic, we can project this homotopy down to the circle.
    have h_homotopic : ContinuousMap.HomotopyRel (cov.liftPath p_a.toContinuousMap 0 (by simp [p_a.source]) : C(I, ℝ)) (cov.liftPath p_b.toContinuousMap 0 (by simp [p_b.source]) : C(I, ℝ)) {0, 1} := by
      have h_lift_homotopic : ∀ (p q : C(I, ℝ)), p 0 = q 0 → p 1 = q 1 → ContinuousMap.HomotopyRel p q {0, 1} := by
        intro p q hp hq;
        refine' ⟨ _, _ ⟩;
        refine' ⟨ _, _, _ ⟩;
        exact ⟨ fun ( t, x ) => ( 1 - t.val ) * p x + t.val * q x, by continuity ⟩;
        all_goals norm_num;
        exact fun a ha₁ ha₂ => ⟨ by rw [ hp ] ; ring, by rw [ hq ] ; ring ⟩;
      apply h_lift_homotopic;
      · simp +decide [ IsCoveringMap.liftPath ];
        grind +splitIndPred;
      · exact h_lift;
    constructor;
    constructor;
    swap;
    constructor;
    rotate_left;
    rotate_left;
    exact ContinuousMap.mk ( fun x => Circle.exp ( h_homotopic.toContinuousMap x ) ) ( by fun_prop );
    all_goals simp_all +decide [ ContinuousMap.HomotopyRel ];
    · -- Since h_homotopic is a homotopy between the lifts of p_a and p_b, and the lifts start at 0 and end at the same point, the exponential of the homotopy at these points should be 1.
      intros a ha hb
      have h_start : h_homotopic (⟨a, ha, hb⟩, 0) = 0 := by
        grind +suggestions
      have h_end : h_homotopic (⟨a, ha, hb⟩, 1) = liftEnd p_a := by
        have := h_homotopic.2; aesop;
      simp [h_start, h_end, Circle.exp_zero, Circle.exp_add];
      exact liftEnd_fiber p_a;
    · intro a ha hb; exact (by
      convert congr_arg ( fun x => x ⟨ a, ha, hb ⟩ ) ( cov.liftPath_lifts p_a.toContinuousMap 0 ( by simp +decide [ p_a.source ] ) ) using 1);
    · intro a ha hb; exact (by
      convert congr_arg ( fun x => x ⟨ a, ha, hb ⟩ ) ( IsCoveringMap.liftPath_lifts ( Circle.isCoveringMap_exp ) p_b.toContinuousMap 0 _ ) using 1)
  have h_eq : a = b := by
    exact hp_a.symm.trans ( Quotient.sound h_homotopic ) |> Eq.trans <| hp_b
  exact h_eq

/-
windingNum is surjective (construct explicit loops)
-/
set_option maxHeartbeats 800000 in
private lemma windingNum_surjective : Function.Surjective windingNum := by
  -- For any integer n, construct the loop γ_n(t) = Circle.exp(2 * π * n * t).
  have h_loop : ∀ n : ℤ, ∃ γ : Path (1 : Circle) 1, liftEnd γ = 2 * Real.pi * n := by
    intro n;
    refine' ⟨ _, _ ⟩;
    refine' ⟨ _, _, _ ⟩;
    exact ⟨ fun t => Circle.exp ( 2 * Real.pi * n * t ), by continuity ⟩;
    all_goals norm_num [ liftEnd ];
    exact int_to_fiber n;
    have := @cov.eq_liftPath_iff';
    specialize @this ⟨ fun t => Circle.exp ( 2 * Real.pi * n * t ), by continuity ⟩ 0 ( by simp +decide [ Circle.exp_zero ] ) ⟨ fun t => 2 * Real.pi * n * t, by continuity ⟩ ; norm_num at this;
    exact congr_arg ( fun f => f 1 ) ( this.mpr rfl ) ▸ by norm_num;
  -- For any integer n, construct the loop γ_n(t) = Circle.exp(2 * π * n * t) and show that its winding number is n.
  intro n
  obtain ⟨γ, hγ⟩ := h_loop n
  use Quotient.mk'' γ
  simp [windingNum, hγ];
  have := fiberToInt_spec ( liftEnd γ ) ( liftEnd_fiber γ );
  exact_mod_cast ( by nlinarith [ Real.pi_pos ] : ( fiberToInt ( liftEnd γ ) ( liftEnd_fiber γ ) : ℝ ) = n )

-- Package as MonoidHom
private noncomputable def windingNumHom : FundamentalGroup Circle 1 →* Multiplicative ℤ where
  toFun γ := Multiplicative.ofAdd (windingNum γ)
  map_one' := by simp [windingNum_one]
  map_mul' a b := by simp [windingNum_mul]

-- Package as MulEquiv
private noncomputable def windingNumEquiv :
    FundamentalGroup Circle 1 ≃* Multiplicative ℤ :=
  MulEquiv.ofBijective windingNumHom ⟨by
    intro a b h
    simp [windingNumHom] at h
    exact windingNum_injective h, by
    intro x
    obtain ⟨a, ha⟩ := windingNum_surjective x.toAdd
    exact ⟨a, by simp [windingNumHom, ha]⟩⟩

/-
The pi1 ≃* FundamentalGroup equivalence
-/
set_option maxHeartbeats 800000 in
private noncomputable def pi1MulEquivFG :
    π_ 1 Circle (1 : Circle) ≃* FundamentalGroup Circle (1 : Circle) := by
  refine MulEquiv.mk HomotopyGroup.pi1EquivFundamentalGroup ?_
  intro a b
  show HomotopyGroup.pi1EquivFundamentalGroup (a * b) =
    HomotopyGroup.pi1EquivFundamentalGroup a * HomotopyGroup.pi1EquivFundamentalGroup b
  obtain ⟨ a, ha ⟩ := a;
  induction b using Quotient.inductionOn';
  rename_i b;
  obtain ⟨ b, hb ⟩ := b;
  erw [ Quotient.eq' ];
  refine' ⟨ _, _ ⟩;
  refine' ⟨ _, _, _ ⟩;
  refine' ⟨ fun p => if p.1 = 0 then ( genLoopEquivOfUnique ( Fin 1 ) ) ( ( GenLoop.loopHomeo ( Classical.arbitrary ( Fin 1 ) ) ).symm ( ( ( GenLoop.loopHomeo ( Classical.arbitrary ( Fin 1 ) ) ).toEquiv ⟨ b, hb ⟩ ).trans ( ( GenLoop.loopHomeo ( Classical.arbitrary ( Fin 1 ) ) ).toEquiv ⟨ a, ha ⟩ ) ) ) p.2 else ( ( genLoopEquivOfUnique ( Fin 1 ) ) ⟨ b, hb ⟩ ).trans ( ( genLoopEquivOfUnique ( Fin 1 ) ) ⟨ a, ha ⟩ ) p.2, _ ⟩;
  all_goals simp +decide [ genLoopEquivOfUnique ];
  · refine' Continuous.if _ _ _;
    · simp +decide [ frontier_eq_closure_inter_closure ];
      simp +decide [ mem_closure_iff_seq_limit, mem_interior_iff_mem_nhds, nhds_prod_eq ];
      intro a_1 hp hq a_2 hp_1 hq_1 x hx hx' hx''; contrapose! hx''; simp_all +decide [ Filter.mem_prod_iff ] ;
      simp_all +decide [ GenLoop.fromLoop, GenLoop.toLoop ];
      simp_all +decide [ Path.trans_apply ];
      split_ifs at hx'' <;> simp_all +decide [ Cube.insertAt ];
      · simp_all +decide [ Homeomorph.funSplitAt ];
        simp_all +decide [ Homeomorph.piSplitAt ];
        simp_all +decide [ Equiv.piSplitAt ];
        simp_all +decide [ Fin.eq_zero ];
      · simp_all +decide [ Homeomorph.funSplitAt ];
        simp_all +decide [ Homeomorph.piSplitAt ];
        simp_all +decide [ Equiv.piSplitAt ];
        simp_all +decide [ Fin.eq_zero ];
    · fun_prop;
    · fun_prop;
  · simp +decide [ GenLoop.fromLoop, GenLoop.toLoop, GenLoop.const ]
    aesop

-- Main theorem
theorem pi1_circle_mulEquiv_int :
    Nonempty (HomotopyGroup.Pi 1 Circle (1 : Circle) ≃* Multiplicative ℤ) :=
  ⟨pi1MulEquivFG.trans windingNumEquiv⟩

end

end Submission
