import Submission.OddOrder.PF.Section13.FTTypePBoundsInfrastructure

/-!
# Peterfalvi Section 13: the cyclic rectangle

This file selects the two distinguished rows of the cyclic-TI rectangle and
proves the support identity used on the complement of the two Fitting
supports.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.BG.Section07
open scoped BigOperators Classical Pointwise

variable {G : Type} [Group G] [Finite G] [IsMinSimpleOddGroup G]
variable {S U W W₁ W₂ : Subgroup G}
variable {defW : IsInternalDirectProductIn W₁ W₂ W}

local instance (priority := 10) cyclicRectangleFintype
    (X : Type) [Finite X] : Fintype X :=
  Fintype.ofFinite X

private theorem signIndex_signIndex
    (b : Bool) (j : IrreducibleCharacter W₂ ℂ) :
    ftTypePSignIndex b (ftTypePSignIndex b j) = j := by
  cases b <;> simp [ftTypePSignIndex]

private theorem signIndex_ne_trivial
    (b : Bool) (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    ftTypePSignIndex b j ≠ IrreducibleCharacter.trivial := by
  cases b with
  | false => simpa [ftTypePSignIndex] using hj
  | true =>
      intro h
      apply hj
      calc
        j = IrreducibleCharacter.dual (IrreducibleCharacter.dual j) :=
          (IrreducibleCharacter.dual_dual j).symm
        _ = IrreducibleCharacter.dual IrreducibleCharacter.trivial :=
          congrArg IrreducibleCharacter.dual h
        _ = IrreducibleCharacter.trivial :=
          IrreducibleCharacter.dual_trivial

/-- The row `eta_(#1,0)` of the cyclic rectangle. -/
noncomputable def ftTypePEta10
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ClassFunction G ℂ :=
  ctx.eta (ftTypePLeftIndex ctx) IrreducibleCharacter.trivial

/-- The row `eta_(0,#1)` of the cyclic rectangle. -/
noncomputable def ftTypePEta01
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ClassFunction G ℂ :=
  ctx.eta IrreducibleCharacter.trivial (ftTypePRightIndex ctx)

namespace FTTypePCyclicRectangleInternal

/-- The distinguished right column of the cyclic rectangle. -/
noncomputable def etaRightColumn
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ClassFunction G ℂ :=
  ∑ i : IrreducibleCharacter W₁ ℂ,
    ctx.eta i (ftTypePRightIndex ctx)

private theorem pairing_targetMap
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (phi psi : ClassFunction (⊤ : Subgroup G) ℂ) :
    characterPairing (ctx.targetMap phi) (ctx.targetMap psi) =
      characterPairing phi psi := by
  have hcard : Nat.card G = Nat.card (⊤ : Subgroup G) :=
    Nat.card_congr Subgroup.topEquiv.symm.toEquiv
  unfold characterPairing
  rw [hcard]
  congr 1
  apply Fintype.sum_equiv Subgroup.topEquiv.symm.toEquiv
  intro x
  simp [ClassFunction.comap_apply]

theorem characterPairing_eta
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (i k : IrreducibleCharacter W₁ ℂ)
    (j ell : IrreducibleCharacter W₂ ℂ) :
    characterPairing (ctx.eta i j) (ctx.eta k ell) =
      if (i, j) = (k, ell) then 1 else 0 := by
  rw [pairing_targetMap ctx]
  exact ctx.isoG.characterPairing_cyclicTIImage (i, j) (k, ell)

end FTTypePCyclicRectangleInternal

/-- The complement of the conjugacy-saturated supports of `ctx.H` and `K`. -/
def ftTypePNonFittingSet
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (K : Subgroup G) : Set G :=
  (classSupportWithin (⊤ : Subgroup G) (ctx.H : Set G) ∪
    classSupportWithin (⊤ : Subgroup G) (K : Set G))ᶜ

namespace FTTypePCyclicRectangleInternal

private theorem nonFitting_avoids_supports
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (K : Subgroup G) {x : G}
    (hx : x ∈ ftTypePNonFittingSet ctx K) :
    x ∉ classSupportWithin (⊤ : Subgroup G) (ctx.H : Set G) ∧
      x ∉ classSupportWithin (⊤ : Subgroup G) (K : Set G) := by
  change x ∉
    classSupportWithin (⊤ : Subgroup G) (ctx.H : Set G) ∪
      classSupportWithin (⊤ : Subgroup G) (K : Set G) at hx
  exact ⟨fun h ↦ hx (Or.inl h), fun h ↦ hx (Or.inr h)⟩

private theorem support_closed_under_zpowers
    (L : Subgroup G) {x y : G}
    (hy : y ∈ classSupportWithin (⊤ : Subgroup G) (L : Set G))
    (hx : x ∈ Subgroup.zpowers y) :
    x ∈ classSupportWithin (⊤ : Subgroup G) (L : Set G) := by
  rcases hy with ⟨z, hz, g, _hg, rfl⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  refine ⟨z ^ n, L.zpow_mem hz n, g, Subgroup.mem_top g, ?_⟩
  simpa only [inv_inv] using
    (conj_zpow (a := g⁻¹) (b := z) (i := n)).symm

theorem nonFitting_mem_of_zpowers_eq
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (K : Subgroup G) {x y : G}
    (hx : x ∈ ftTypePNonFittingSet ctx K)
    (hxy : Subgroup.zpowers x = Subgroup.zpowers y) :
    y ∈ ftTypePNonFittingSet ctx K := by
  obtain ⟨hxH, hxK⟩ := nonFitting_avoids_supports ctx K hx
  change y ∉
    classSupportWithin (⊤ : Subgroup G) (ctx.H : Set G) ∪
      classSupportWithin (⊤ : Subgroup G) (K : Set G)
  intro hy
  have hxPow : x ∈ Subgroup.zpowers y := by
    rw [← hxy]
    exact Subgroup.mem_zpowers x
  rcases hy with hyH | hyK
  · exact hxH (support_closed_under_zpowers ctx.H hyH hxPow)
  · exact hxK (support_closed_under_zpowers K hyK hxPow)

theorem induce_subgroupOf_mem_supportedOn_classSupportWithin
    {H L : Subgroup G} {A : Set G}
    (hHL : H ≤ L) (alpha : ClassFunction H ℂ)
    (halpha : alpha ∈
      ClassFunction.supportedOn {x : H | (x : G) ∈ A}) :
    ClassFunction.induce (H.subgroupOf L)
        (ClassFunction.toSubgroupOf H L hHL alpha) ∈
      ClassFunction.supportedOn
        {x : L | (x : G) ∈ classSupportWithin L A} := by
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hx
  rw [ClassFunction.induce_apply_formula]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro y _
  split_ifs with hy
  · rw [ClassFunction.toSubgroupOf_apply]
    apply ClassFunction.eq_zero_of_mem_supportedOn halpha
    intro hs
    apply hx
    refine ⟨
      ((Subgroup.subgroupOfEquivOfLe hHL ⟨y⁻¹ * x * y, hy⟩ : H) : G),
      hs, (y : G)⁻¹, L.inv_mem y.property, ?_⟩
    simp only [inv_inv]
    change (y : G) * ((y : G)⁻¹ * (x : G) * (y : G)) *
      (y : G)⁻¹ = (x : G)
    group
  · rfl

private theorem induce_eq_zero_on_nonFitting
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (K : Subgroup G) (phi : ClassFunction S ℂ)
    (hphi : phi ∈ ClassFunction.supportedOn
      ((ctx.H.subgroupOf S : Subgroup S) : Set S))
    {x : G} (hx : x ∈ ftTypePNonFittingSet ctx K) :
    ClassFunction.induce S phi x = 0 := by
  rw [ClassFunction.induce_apply_formula]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro y _
  split_ifs with hy
  · apply ClassFunction.eq_zero_of_mem_supportedOn hphi
    intro hyH
    apply (nonFitting_avoids_supports ctx K hx).1
    change (y⁻¹ * x * y : G) ∈ ctx.H at hyH
    refine ⟨y⁻¹ * x * y, hyH, y⁻¹, Subgroup.mem_top _, ?_⟩
    group
  · rfl

theorem tau1_lambda_eq_etaRightColumn_on_nonFitting
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (K : Subgroup G)
    (tau1 : ClassFunction S ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (lambda : ClassFunction S ℂ)
    (hcoh : coherent_with
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
      (nonidentitySet S) ctx.tau tau1)
    (hTIred : typeP_TIred_coherent ctx tau1)
    (hcalS : lambda ∈ ftTypePCoreFamily S)
    (hirr : lambda ∈ irr_Ind_Fitting S) :
    ∃ b : Bool, ∀ x ∈ ftTypePNonFittingSet ctx K,
      tau1 lambda x = ftTypePBooleanSign b * etaRightColumn ctx x := by
  obtain ⟨b, _hb, hrows⟩ := hTIred
  let j := ftTypePSignIndex b (ftTypePRightIndex ctx)
  have hj : j ≠ IrreducibleCharacter.trivial :=
    signIndex_ne_trivial b (ftTypePRightIndex ctx)
      (FTTypePBoundsInfrastructureInternal.rightIndex_ne_trivial ctx)
  have hjIndex : ftTypePSignIndex b j = ftTypePRightIndex ctx := by
    simpa only [j] using signIndex_signIndex b (ftTypePRightIndex ctx)
  have hmuFamily : ctx.mu j ∈ ftTypePFittingFamily S :=
    FTprTIred_Ind_Fitting ctx j hj
  have hdegree : lambda 1 = ctx.mu j 1 :=
    (FTtypeP_Ind_Fitting_1 ctx lambda hirr.2).trans
      (FTtypeP_Ind_Fitting_1 ctx (ctx.mu j) hmuFamily).symm

  let HInS : Subgroup S := ctx.H.subgroupOf S
  have hlambdaT : lambda ∈ seqIndT (k := ℂ) HInS := by
    simpa only [ftTypePFittingFamily, HInS] using hirr.2
  have hmuT : ctx.mu j ∈ seqIndT (k := ℂ) HInS := by
    simpa only [ftTypePFittingFamily, HInS] using hmuFamily
  have hlambdaOn : lambda ∈ ClassFunction.supportedOn (HInS : Set S) :=
    seqInd_on HInS hlambdaT
  have hmuOn : ctx.mu j ∈ ClassFunction.supportedOn (HInS : Set S) :=
    seqInd_on HInS hmuT

  let alpha : ClassFunction S ℂ := lambda - ctx.mu j
  have halphaOn : alpha ∈ ClassFunction.supportedOn (HInS : Set S) :=
    (ClassFunction.supportedOn (R := ℂ) (HInS : Set S)).sub_mem
      hlambdaOn hmuOn
  have halphaOff : alpha ∈
      ClassFunction.supportedOn (nonidentitySet S) := by
    rw [ClassFunction.mem_supportedOn_iff]
    intro y hy
    have hyOne : y = 1 := by
      simpa [nonidentitySet] using not_not.mp hy
    subst y
    simp only [alpha, ClassFunction.sub_apply, hdegree, sub_self]
  have halphaSpan : alpha ∈ AddSubgroup.closure
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ)) :=
    (AddSubgroup.closure
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))).sub_mem
        (AddSubgroup.subset_closure hcalS)
        (AddSubgroup.subset_closure (FTseqInd_TIred ctx j hj))
  have halphaA0 : alpha ∈
      ClassFunction.supportedOn (ftTypePSupport0InS S) := by
    rw [ClassFunction.mem_supportedOn_iff]
    intro y hy
    by_cases hyOne : y = 1
    · subst y
      simp only [alpha, ClassFunction.sub_apply, hdegree, sub_self]
    · apply ClassFunction.eq_zero_of_mem_supportedOn halphaOn
      intro hyH
      apply hy
      change (y : G) ∈
        Submission.OddOrder.BG.Section16.FTsupport0 S
      apply Submission.OddOrder.BG.Section16.Fitting_sub_FTsupp0 ctx.maxS
      refine ⟨hyH, ?_⟩
      intro hyAmbient
      apply hyOne
      exact Subtype.ext hyAmbient

  have hagree : tau1 alpha = ctx.tau alpha :=
    hcoh.agrees alpha halphaSpan halphaOff
  have htauInduce : ctx.tau alpha = ClassFunction.induce S alpha :=
    (FTtypeP_facts ctx).2.2.2.2.2.2.2.2.2 alpha halphaA0
  refine ⟨b, ?_⟩
  intro x hx
  have halphaZero : tau1 alpha x = 0 := by
    calc
      tau1 alpha x = ctx.tau alpha x :=
        congrArg (fun phi : ClassFunction G ℂ ↦ phi x) hagree
      _ = ClassFunction.induce S alpha x :=
        congrArg (fun phi : ClassFunction G ℂ ↦ phi x) htauInduce
      _ = 0 := induce_eq_zero_on_nonFitting ctx K alpha halphaOn hx
  have hlambdaMu : tau1 lambda x = tau1 (ctx.mu j) x := by
    change tau1 (lambda - ctx.mu j) x = 0 at halphaZero
    rw [map_sub, ClassFunction.sub_apply, sub_eq_zero] at halphaZero
    exact halphaZero
  calc
    tau1 lambda x = tau1 (ctx.mu j) x := hlambdaMu
    _ = (ftTypePBooleanSign b •
        ∑ i : IrreducibleCharacter W₁ ℂ,
          ctx.eta i (ftTypePRightIndex ctx)) x := by
      have hrow := hrows j hj
      rw [hjIndex] at hrow
      exact congrArg (fun phi : ClassFunction G ℂ ↦ phi x) hrow
    _ = ftTypePBooleanSign b * etaRightColumn ctx x := by
      simp only [ClassFunction.smul_apply, smul_eq_mul, etaRightColumn]

end FTTypePCyclicRectangleInternal

end

end Submission.OddOrder.PF
