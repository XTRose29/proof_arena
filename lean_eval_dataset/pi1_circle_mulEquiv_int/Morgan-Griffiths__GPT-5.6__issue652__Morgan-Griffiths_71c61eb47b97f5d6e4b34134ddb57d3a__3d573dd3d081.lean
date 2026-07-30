import Mathlib
namespace Submission

/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem pi1_circle_mulEquiv_int :
    Nonempty (HomotopyGroup.Pi 1 Circle (1 : Circle) ≃* Multiplicative ℤ) :=
/-ResultProofBegin-/by
  classical
  -- the universal-cover calculation
  have cover_calc :
      ∀ {E X A : Type} [TopologicalSpace E] [TopologicalSpace X]
        [AddCommGroup A] [AddAction A E]
        [SimplyConnectedSpace E] [PathConnectedSpace E],
        ∀ (p : E → X) (_ : IsAddQuotientCoveringMap p A) (e : E),
          Nonempty (FundamentalGroup X (p e) ≃* Multiplicative A) := by
    intro E X A _ _ _ _ _ _ p hp e
    classical
    letI : ContinuousConstVAdd A E := hp.toContinuousConstVAdd
    let b : X := p e
    let eb : p ⁻¹' {b} := ⟨e, rfl⟩
    let cov : IsCoveringMap p := hp.isCoveringMap
    let F : (p ⁻¹' {b}) ≃ A := hp.fiberEquivAddGroup eb
    -- translate inside a fibre
    let va (a : A) {x : X} (u : p ⁻¹' {x}) : p ⁻¹' {x} :=
      ⟨a +ᵥ (u:E), (hp.map_vadd a).trans u.2⟩
    have F_spec (u : p ⁻¹' {b}) (a : A) : F u = a ↔ (u:E) = a +ᵥ e := by
      change (hp.fiberEquivAddGroup eb u = a ↔ _)
      
      -- definition is inverse of the orbit equivalence
      change (Equiv.ofBijective _ _).symm u = a ↔ _
      rw [Equiv.symm_apply_eq]
      change (u = (⟨_, _⟩ : p ⁻¹' {b}) ↔ _)
      rw [Subtype.mk.injEq]
    have F_zero : F eb = (0 : A) := (F_spec eb 0).2 (by simp [eb])
    -- translating a lifted path is the lift with translated start
    have mono_vadd (a : A) {x y : X} (q : Path.Homotopic.Quotient x y)
        (u : p ⁻¹' {x}) :
        cov.monodromy q (va a u) = va a (cov.monodromy q u) := by
      obtain ⟨γ⟩ := q
      apply Subtype.ext
      have h0 : (γ : C(unitInterval, X)) 0 = p (u:E) := γ.source.trans u.2.symm
      have h0a : (γ : C(unitInterval, X)) 0 = p (a +ᵥ (u:E)) :=
        γ.source.trans ( (hp.map_vadd a).trans u.2).symm
      -- use uniqueness of path lifts
      change cov.liftPath (γ : C(unitInterval, X)) (a +ᵥ (u:E)) h0a 1 =
        a +ᵥ cov.liftPath (γ : C(unitInterval, X)) (u:E) h0 1
      let L : C(unitInterval, E) := cov.liftPath (γ : C(unitInterval, X)) (u:E) h0
      let La : C(unitInterval, E) :=
        ⟨fun t => a +ᵥ L t, (Continuous.const_vadd L.continuous a)⟩
      have hLa : La = cov.liftPath (γ : C(unitInterval, X)) (a +ᵥ (u:E)) h0a := by
        apply (cov.eq_liftPath_iff' _).2
        constructor
        · -- it lifts γ
          funext t
          change p (a +ᵥ (L t)) = γ t
          simpa [L, Function.comp_apply] using
            ( (hp.map_vadd a (e := L t)).trans
              (congrFun (cov.liftPath_lifts (γ : C(unitInterval, X)) (u:E) h0) t) )
        · change a +ᵥ (L 0) = a +ᵥ (u:E)
          simp [L, cov.liftPath_zero]
      exact congrArg (fun k : C(unitInterval, E) => k 1) hLa.symm
    have F_va (a : A) (u : p ⁻¹' {b}) : F (va a u) = a + F u := by
      apply (F_spec (va a u) (a + F u)).2
      change a +ᵥ (u:E) = (a + F u) +ᵥ e
      rw [(F_spec u (F u)).1 rfl]
      simp [add_vadd]
    let endpt (q : FundamentalGroup X b) : p ⁻¹' {b} :=
      cov.monodromy (FundamentalGroup.toPath q) eb
    let hom : FundamentalGroup X b →* Multiplicative A :=
      { toFun := fun q => Multiplicative.ofAdd (F (endpt q))
        map_one' := by
          change Multiplicative.ofAdd (F (endpt (1 : FundamentalGroup X b))) = _
          have h : endpt (1 : FundamentalGroup X b) = eb := by
            -- the identity is the constant loop
            change cov.monodromy (.refl b) eb = eb
            rw [cov.monodromy_refl]
            rfl
          rw [h, F_zero]
          rfl
        map_mul' := by
          intro q r
          change Multiplicative.ofAdd (F (endpt (q*r))) =
            Multiplicative.ofAdd (F (endpt q)) * Multiplicative.ofAdd (F (endpt r))
          change F (cov.monodromy ((FundamentalGroup.toPath r).trans
              (FundamentalGroup.toPath q)) eb) = F (endpt q) + F (endpt r)
          rw [cov.monodromy_trans_apply]
          have hq := mono_vadd (F (endpt r)) (FundamentalGroup.toPath q) eb
          have hr : va (F (endpt r)) eb = endpt r := by
            apply (Equiv.injective F)
            rw [F_va]
            simp [F_zero]
          -- first replace the inner endpoint, not the RHS
          have hc : cov.monodromy (FundamentalGroup.toPath q)
                (cov.monodromy (FundamentalGroup.toPath r) eb) =
                va (F (endpt r)) (endpt q) := by
            -- substitute both endpoint descriptions in the equivariance equation
            simpa [endpt, hr] using hq
          rw [hc, F_va]
          simp [add_comm]
      }
    have hinj : Function.Injective hom := by
      intro q r hqr
      have heq : endpt q = endpt r := by
        apply (Equiv.injective F)
        change Multiplicative.ofAdd (F (endpt q)) =
          Multiplicative.ofAdd (F (endpt r)) at hqr
        exact hqr
      change (FundamentalGroup.toPath q = FundamentalGroup.toPath r)
      obtain ⟨γ⟩ := q
      obtain ⟨δ⟩ := r
      let hγ0 : (γ : C(unitInterval, X)) 0 = p e := γ.source.trans rfl
      let hδ0 : (δ : C(unitInterval, X)) 0 = p e := δ.source.trans rfl
      let Lγ : C(unitInterval, E) := cov.liftPath (γ : C(unitInterval, X)) e hγ0
      let Lδ : C(unitInterval, E) := cov.liftPath (δ : C(unitInterval, X)) e hδ0
      have hend : Lγ 1 = Lδ 1 := by
        exact congrArg (fun z : p ⁻¹' {b} => (z:E)) heq
      let Pγ : Path e (Lγ 1) := ⟨Lγ, cov.liftPath_zero .., rfl⟩
      let Pδ : Path e (Lγ 1) := ⟨Lδ, cov.liftPath_zero .., hend.symm⟩
      have HP : (Path.Homotopic.Quotient.mk Pγ) =
          (Path.Homotopic.Quotient.mk Pδ) :=
        Subsingleton.elim _ _
      have Hmap := congrArg
        (fun z : Path.Homotopic.Quotient e (Lγ 1) =>
          z.map (⟨p, cov.continuous⟩ : C(E, X))) HP
      -- cast the target of the mapped lifts back to the base point
      have ht : p (Lγ 1) = b := by
        change p (cov.liftPath (γ : C(unitInterval, X)) e hγ0 1) = b
        simpa [b] using
          (congrFun (cov.liftPath_lifts (γ : C(unitInterval, X)) e hγ0) 1)
      have Hcast := congrArg
        (fun z : Path.Homotopic.Quotient (p e) (p (Lγ 1)) =>
          z.cast (show b = p e from rfl) ht.symm) Hmap
      have hcγ : ((Pγ.map cov.continuous).cast
            (show b = p e from rfl) ht.symm) = γ := by
        apply Path.ext
        funext t
        change p (Lγ t) = γ t
        change p (cov.liftPath (γ : C(unitInterval, X)) e hγ0 t) = γ t
        exact congrFun (cov.liftPath_lifts (γ : C(unitInterval, X)) e hγ0) t
      have hcδ : ((Pδ.map cov.continuous).cast
            (show b = p e from rfl) ht.symm) = δ := by
        apply Path.ext
        funext t
        change p (Lδ t) = δ t
        change p (cov.liftPath (δ : C(unitInterval, X)) e hδ0 t) = δ t
        exact congrFun (cov.liftPath_lifts (δ : C(unitInterval, X)) e hδ0) t
      change (Path.Homotopic.Quotient.mk γ = Path.Homotopic.Quotient.mk δ)
      simpa [← Path.Homotopic.Quotient.mk_map,
        ← Path.Homotopic.Quotient.mk_cast, hcγ, hcδ,
        Path.Homotopic.Quotient.mk''_eq_mk] using Hcast
    have hsurj : Function.Surjective hom := by
      intro z
      let a : A := Multiplicative.toAdd z
      let ρ : Path e (a +ᵥ e) := PathConnectedSpace.somePath e (a +ᵥ e)
      let γ : Path b b :=
        ⟨⟨fun t => p (ρ t), cov.continuous.comp ρ.continuous⟩,
          by change p (ρ 0) = b; simpa [b] using congrArg p ρ.source,
          by
            change p (ρ 1) = b
            calc p (ρ 1) = p (a +ᵥ e) := congrArg p ρ.target
                 _ = p e := hp.map_vadd a
                 _ = b := rfl⟩
      refine ⟨(FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)), ?_⟩
      change Multiplicative.ofAdd
        (F (cov.monodromy (Path.Homotopic.Quotient.mk γ) eb)) = z
      have h0 : (γ : C(unitInterval, X)) 0 = p e := by simp [γ, b]
      have hL : (ρ : C(unitInterval, E)) = cov.liftPath (γ : C(unitInterval, X)) e h0 := by
        apply (cov.eq_liftPath_iff' _).2
        constructor
        · rfl
        · exact ρ.source
      have hend : cov.monodromy (Path.Homotopic.Quotient.mk γ) eb = va a eb := by
        apply Subtype.ext
        change cov.liftPath (γ : C(unitInterval, X)) e h0 1 = a +ᵥ e
        rw [← hL]
        exact ρ.target
      rw [hend, F_va, F_zero]
      cases z
      simp [a]
    exact ⟨MulEquiv.ofBijective hom ⟨hinj, hsurj⟩⟩
  have hc := cover_calc (p := (Circle.exp : ℝ → Circle))
    Circle.isAddQuotientCoveringMap_exp (0 : ℝ)
  -- identify the deck group of exp with Z
  let t : ℝ := 2 * Real.pi
  have ht : t ≠ 0 := by
    dsimp [t]
    positivity
  let j : ℤ →+ (AddSubgroup.zmultiples t : AddSubgroup ℝ) :=
    { toFun := fun n => ⟨(n : ℝ) * t, (AddSubgroup.mem_zmultiples_iff).2 ⟨n, by
          simp [zsmul_eq_mul]⟩⟩
      map_zero' := by ext; simp
      map_add' := by
        intro m n
        ext
        push_cast
        ring }
  have hinj : Function.Injective j := by
    intro m n h
    have h' : (m : ℝ) * t = (n : ℝ) * t := congrArg (fun z : (AddSubgroup.zmultiples t : AddSubgroup ℝ) => (z : ℝ)) h
    have h'' : (m : ℝ) = (n : ℝ) := by
      exact (mul_right_cancel₀ ht h')
    exact_mod_cast h''
  have hsurj : Function.Surjective j := by
    intro x
    have hx := (AddSubgroup.mem_zmultiples_iff).1 x.property
    rcases hx with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    change (n : ℝ) * t = (x : ℝ)
    simpa [zsmul_eq_mul] using hn
  let aeq0 : ℤ ≃+ (AddSubgroup.zmultiples t : AddSubgroup ℝ) :=
    AddEquiv.ofBijective j ⟨hinj, hsurj⟩
  let aeq : (AddSubgroup.zmultiples t : AddSubgroup ℝ) ≃+ ℤ := aeq0.symm
  have heqsub :
      (AddSubgroup.zmultiples t : AddSubgroup ℝ) =
        (AddSubgroup.zmultiples (2 * Real.pi) : AddSubgroup ℝ) := by rfl
  -- compose the three standard isomorphisms
  have hc' : Nonempty
      (FundamentalGroup Circle (1 : Circle) ≃*
        Multiplicative (AddSubgroup.zmultiples t : AddSubgroup ℝ)) := by
    change Nonempty (FundamentalGroup Circle (Circle.exp 0) ≃* _) at hc
    rw [Circle.exp_zero] at hc
    simpa [t] using hc
  rcases hc' with ⟨u⟩
  let v : Multiplicative (AddSubgroup.zmultiples t : AddSubgroup ℝ) ≃*
      Multiplicative ℤ := AddEquiv.toMultiplicative aeq
  exact ⟨(HomotopyGroup.pi1MulEquivFundamentalGroup (X := Circle) (x := (1 : Circle))).trans
    (u.trans v)⟩
/-ResultProofEnd-/
/-ResultEnd-/

end Submission
