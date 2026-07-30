import Submission.OddOrder.PF.Section13.FTTypePCyclicCover

/-!
# Peterfalvi Section 13: the first three type-P bounds

This module isolates Peterfalvi (13.6)--(13.8).  The common proof constructs
the reciprocal-Dade expansion on the Fitting subgroup once, separates its
distinguished coefficient from the residual tail, and then applies the three
specialized arithmetic arguments.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open scoped BigOperators Classical Pointwise IsMulCommutative

variable {G : Type} [Group G] [Finite G] [IsMinSimpleOddGroup G]
variable {S U W W₁ W₂ : Subgroup G}
variable {defW : IsInternalDirectProductIn W₁ W₂ W}

local instance (priority := 10) ftTypePBoundsFirstThreeFintypeOfFinite
    (X : Type*) [Finite X] : Fintype X :=
  Fintype.ofFinite X

universe u

namespace FTTypePBoundsFirstThreeInternal

private def irreducibleCoreSet (S : Subgroup G) :
    Set (ClassFunction S ℂ) :=
  {phi | phi ∈ ftTypePCoreFamily S ∧ IsIrreducibleCharacter S ℂ phi}

/-! ### Passing the upper-kernel condition between two inducing sources -/

/-- If two irreducible sources induce the same ambient character, membership
of a normal subgroup in the translation kernel is independent of which source
is used.  We only need the contrapositive direction below. -/
private theorem source_nonkernel_of_equal_inductions
    {Q : Type} [Group Q] [Fintype Q]
    (D H A : Subgroup Q) [D.Normal] [H.Normal] [A.Normal]
    (hAD : A ≤ D) (hAH : A ≤ H)
    (sigma : IrreducibleCharacter D ℂ)
    (rho : IrreducibleCharacter H ℂ)
    (hind :
      ClassFunction.induce D (sigma : ClassFunction D ℂ) =
        ClassFunction.induce H (rho : ClassFunction H ℂ))
    (hsigma : ¬ A.subgroupOf D ≤
      ClassFunction.translationKernel (sigma : ClassFunction D ℂ)) :
    ¬ A.subgroupOf H ≤
      ClassFunction.translationKernel (rho : ClassFunction H ℂ) := by
  intro hrho
  let V : FDRep ℂ Q := FDRep.induceFromSubgroup D sigma.representation
  letI : Nontrivial V := FDRep.induceFromSubgroup_nontrivial D sigma
  obtain ⟨chi, hchi⟩ :=
    ClassFunction.exists_irreducible_constituent_of_nontrivial V
  have hV :
      ClassFunction.ofRepresentation V.ρ =
        ClassFunction.induce D (sigma : ClassFunction D ℂ) := by
    exact
      (ClassFunction.ofRepresentation_induceFromSubgroup_general
        D sigma.representation).trans
        (congrArg (ClassFunction.induce D)
          sigma.ofRepresentation_representation)
  have hchiD : chi.IsConstituent
      (ClassFunction.induce D (sigma : ClassFunction D ℂ)) := by
    rw [← hV]
    exact hchi
  have hchiH : chi.IsConstituent
      (ClassFunction.induce H (rho : ClassFunction H ℂ)) := by
    rw [← hind]
    exact hchiD
  have hrhoKernel : A.subgroupOf H ≤ rho.representation.ρ.ker := by
    rw [← ClassFunction.translationKernel_irreducibleCharacter rho]
    exact hrho
  have hchiKernel : A ≤ chi.representation.ρ.ker :=
    (IrreducibleCharacter.sub_ker_constituent_induce_iff
      H A hAH chi rho hchiH).mp hrhoKernel
  have hsigmaKernel : A.subgroupOf D ≤ sigma.representation.ρ.ker :=
    (IrreducibleCharacter.sub_ker_constituent_induce_iff
      D A hAD chi sigma hchiD).mpr hchiKernel
  apply hsigma
  rw [ClassFunction.translationKernel_irreducibleCharacter sigma]
  exact hsigmaKernel

/-! ### Membership in the local Fitting layer -/

private theorem mem_calS1_of_mem_core_and_fitting
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (phi : ClassFunction S ℂ)
    (hcore : phi ∈ ftTypePCoreFamily S)
    (hfit : phi ∈ ftTypePFittingFamily S) :
    phi ∈ FTTypePBoundsInfrastructureInternal.fittingCoreFamily ctx := by
  let D : Subgroup S := ctx.PU.subgroupOf S
  let H : Subgroup S := ctx.H.subgroupOf S
  let A : Subgroup S := ctx.P.subgroupOf S
  letI : D.Normal :=
    Submission.OddOrder.BG.Section16.TypeSpecInternal.derivedWithin_normal16 S
  letI : H.Normal := fittingWithin_subgroupOf_normal S
  letI : A.Normal := by
    simpa only [A, FTTypePSetupContext.P] using Fcore_normal S
  have hAD : A ≤ D :=
    Subgroup.subgroupOf_mono S ctx.StypeP.2.1.2.2.2.1
  have hAH : A ≤ H :=
    Subgroup.subgroupOf_mono S (Fcore_sub_Fitting S)
  have hcoreD : phi ∈ seqIndD (k := ℂ) D (A.subgroupOf D) ⊥ := by
    simpa only [ftTypePCoreFamily, D, A,
      FTTypePSetupContext.PU, FTTypePSetupContext.P,
      pTypeHUInMaximal, pTypeHInDerived] using hcore
  have hfitH : phi ∈ seqIndT (k := ℂ) H := by
    simpa only [ftTypePFittingFamily, H] using hfit
  obtain ⟨sigma, hsigmaLayer, hphiD⟩ := seqIndP.mp hcoreD
  obtain ⟨rho, _hrhoLayer, hphiH⟩ := seqIndP.mp hfitH
  have hsigmaUpper : ¬ A.subgroupOf D ≤
      ClassFunction.translationKernel (sigma : ClassFunction D ℂ) :=
    (mem_Iirr_kerD.mp hsigmaLayer).2
  have hrhoUpper : ¬ A.subgroupOf H ≤
      ClassFunction.translationKernel (rho : ClassFunction H ℂ) :=
    source_nonkernel_of_equal_inductions D H A hAD hAH sigma rho
      (hphiD.symm.trans hphiH) hsigmaUpper
  change phi ∈ seqIndD (k := ℂ) H (A.subgroupOf H) ⊥
  apply seqIndP.mpr
  exact ⟨rho, mem_Iirr_kerD.mpr ⟨bot_le, hrhoUpper⟩, hphiH⟩

private theorem lambda_mem_calS1
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (lambda : ClassFunction S ℂ)
    (hirr : lambda ∈ irr_Ind_Fitting S)
    (hcore : lambda ∈ ftTypePCoreFamily S) :
    lambda ∈ FTTypePBoundsInfrastructureInternal.fittingCoreFamily ctx := by
  exact mem_calS1_of_mem_core_and_fitting ctx lambda hcore hirr.2

private theorem mu_mem_calS1
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    ctx.mu j ∈ FTTypePBoundsInfrastructureInternal.fittingCoreFamily ctx := by
  exact mem_calS1_of_mem_core_and_fitting ctx (ctx.mu j)
    (FTseqInd_TIred ctx j hj) (FTprTIred_Ind_Fitting ctx j hj)

/-! ### Subgroup and induction transports used in the classification -/

private theorem fitting_le_derived
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ctx.H ≤ ctx.PU := by
  exact ctx.StypeP.2.2.1.2.2.2

private theorem characterPairing_restrict_chain
    {Q : Type} [Group Q] [Fintype Q]
    (H T : Subgroup Q) (hHT : H ≤ T)
    (theta : IrreducibleCharacter H ℂ)
    (phi : ClassFunction Q ℂ) :
    let e : H.subgroupOf T ≃* H := Subgroup.subgroupOfEquivOfLe hHT
    let thetaT : IrreducibleCharacter (H.subgroupOf T) ℂ :=
      IrreducibleCharacter.comapMulEquiv e theta
    characterPairing (theta : ClassFunction H ℂ)
        (ClassFunction.restrict H phi) =
      characterPairing (thetaT : ClassFunction (H.subgroupOf T) ℂ)
        (ClassFunction.restrict (H.subgroupOf T)
          (ClassFunction.restrict T phi)) := by
  let e : H.subgroupOf T ≃* H := Subgroup.subgroupOfEquivOfLe hHT
  let thetaT : IrreducibleCharacter (H.subgroupOf T) ℂ :=
    IrreducibleCharacter.comapMulEquiv e theta
  have hcard : Nat.card H = Nat.card (H.subgroupOf T) :=
    (Nat.card_congr e.toEquiv).symm
  dsimp only
  unfold characterPairing
  rw [hcard]
  congr 1
  apply Fintype.sum_equiv e.symm.toEquiv
  intro x
  simp [thetaT, e, IrreducibleCharacter.comapMulEquiv_apply,
    ClassFunction.restrict_apply, Subgroup.subgroupOfEquivOfLe]

private theorem induce_realize_mem_closure
    {Q : Type u} [Group Q] [Fintype Q]
    (K : Subgroup Q)
    (T : Set (ClassFunction Q ℂ))
    (z : VirtualCharacter K ℂ)
    (hgenerator : ∀ theta : IrreducibleCharacter K ℂ,
      z theta ≠ 0 →
        ClassFunction.induce K (theta : ClassFunction K ℂ) ∈ T) :
    ClassFunction.induce K (VirtualCharacter.realize z) ∈
      AddSubgroup.closure T := by
  induction z using Finsupp.induction with
  | zero =>
      simpa using (AddSubgroup.zero_mem (AddSubgroup.closure T))
  | single_add theta n tail htheta hn ih =>
      have htailTheta : tail theta = 0 :=
        Finsupp.notMem_support_iff.mp htheta
      have hthetaGenerator :
          ClassFunction.induce K (theta : ClassFunction K ℂ) ∈ T := by
        apply hgenerator theta
        simpa [Finsupp.single_apply, htailTheta] using hn
      have htailGenerator : ∀ psi : IrreducibleCharacter K ℂ,
          tail psi ≠ 0 →
            ClassFunction.induce K (psi : ClassFunction K ℂ) ∈ T := by
        intro psi hpsi
        apply hgenerator psi
        by_cases hpsiTheta : psi = theta
        · subst psi
          exact (hpsi htailTheta).elim
        · simpa [Finsupp.single_apply, hpsiTheta] using hpsi
      have hsingle :
          ClassFunction.induce K
              (VirtualCharacter.realize
                (Finsupp.single theta n : VirtualCharacter K ℂ)) ∈
            AddSubgroup.closure T := by
        simpa only [VirtualCharacter.realize_single, map_smul,
          ← Int.cast_smul_eq_zsmul ℂ] using
          (AddSubgroup.closure T).zsmul_mem
            (AddSubgroup.subset_closure hthetaGenerator) n
      rw [VirtualCharacter.realize_add, map_add]
      exact (AddSubgroup.closure T).add_mem hsingle (ih htailGenerator)

/-- Transport failure of the `P`-kernel condition along the canonical copy of
`H` inside a larger subgroup `T`. -/
private theorem transported_source_nonkernel
    {Q : Type} [Group Q] [Fintype Q]
    (H T P : Subgroup Q) (hHT : H ≤ T) (hPH : P ≤ H)
    (theta : IrreducibleCharacter H ℂ)
    (htheta : ¬ P.subgroupOf H ≤
      ClassFunction.translationKernel (theta : ClassFunction H ℂ)) :
    let HT := H.subgroupOf T
    let e : HT ≃* H := Subgroup.subgroupOfEquivOfLe hHT
    let thetaT : IrreducibleCharacter HT ℂ :=
      IrreducibleCharacter.comapMulEquiv e theta
    ¬ (P.subgroupOf T).subgroupOf HT ≤
      ClassFunction.translationKernel (thetaT : ClassFunction HT ℂ) := by
  dsimp only
  intro hkernel
  apply htheta
  intro x hx
  rw [ClassFunction.mem_translationKernel_iff]
  intro y
  let e : H.subgroupOf T ≃* H :=
    Subgroup.subgroupOfEquivOfLe hHT
  have hxNested : e.symm x ∈
      (P.subgroupOf T).subgroupOf (H.subgroupOf T) := by
    change ((e.symm x : H.subgroupOf T) : Q) ∈ P
    exact hx
  have hvalue :=
    (ClassFunction.mem_translationKernel_iff
      (IrreducibleCharacter.comapMulEquiv e theta :
        ClassFunction (H.subgroupOf T) ℂ)
      (e.symm x)).mp (hkernel hxNested) (e.symm y)
  simpa only [IrreducibleCharacter.comapMulEquiv_apply,
    map_mul, MulEquiv.apply_symm_apply] using hvalue

/-! ### Classification of the local Fitting layer -/

/-- A member of the local Fitting layer is either a nonprincipal reduced
column or belongs to the integral span of irreducible members of the type-P
core family. -/
private theorem S1cases
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (zeta : ClassFunction S ℂ)
    (hzeta : zeta ∈
      FTTypePBoundsInfrastructureInternal.fittingCoreFamily ctx) :
    (∃ j : IrreducibleCharacter W₂ ℂ,
        j ≠ IrreducibleCharacter.trivial ∧ zeta = ctx.mu j) ∨
      zeta ∈ AddSubgroup.closure (irreducibleCoreSet S) := by
  let H : Subgroup S := ctx.H.subgroupOf S
  let D : Subgroup S := ctx.PU.subgroupOf S
  let P : Subgroup S := ctx.P.subgroupOf S
  let PH : Subgroup H := P.subgroupOf H
  let PD : Subgroup D := P.subgroupOf D
  have hHD : H ≤ D := by
    intro x hx
    exact fitting_le_derived ctx hx
  let HD : Subgroup D := H.subgroupOf D
  let e : HD ≃* H := Subgroup.subgroupOfEquivOfLe hHD
  letI : D.Normal := by
    simpa only [D, FTTypePSetupContext.PU] using
      Submission.OddOrder.BG.Section16.TypeSpecInternal.derivedWithin_normal16 S
  letI : H.Normal := fittingWithin_subgroupOf_normal S
  letI : HD.Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : H.Normal) D
  letI : PD.Normal := Subgroup.Normal.subgroupOf (Fcore_normal S) D
  have hPH : P ≤ H := by
    intro x hx
    exact Fcore_sub_Fitting S hx
  have hPDHD : PD ≤ HD := by
    intro x hx
    exact Fcore_sub_Fitting S hx
  obtain ⟨theta, hthetaLayer, hzetaInd⟩ := seqIndP.mp hzeta
  have hthetaNot : ¬ PH ≤
      ClassFunction.translationKernel (theta : ClassFunction H ℂ) :=
    (mem_Iirr_kerD.mp hthetaLayer).2
  let thetaD : IrreducibleCharacter HD ℂ :=
    IrreducibleCharacter.comapMulEquiv e theta
  have hthetaDNot : ¬ PD.subgroupOf HD ≤
      ClassFunction.translationKernel (thetaD : ClassFunction HD ℂ) := by
    exact transported_source_nonkernel H D P hHD hPH theta hthetaNot
  have hthetaTransport :
      ClassFunction.toSubgroupOf H D hHD
          (theta : ClassFunction H ℂ) =
        (thetaD : ClassFunction HD ℂ) := by
    ext x
    simp only [ClassFunction.toSubgroupOf_apply, thetaD, e,
      IrreducibleCharacter.comapMulEquiv_apply]
  let rho : VirtualCharacter D ℂ :=
    VirtualCharacter.induce HD (Finsupp.single thetaD 1)
  have hrhoRealize :
      VirtualCharacter.realize rho =
        ClassFunction.induce HD (thetaD : ClassFunction HD ℂ) := by
    simp only [rho, VirtualCharacter.realize_induce,
      VirtualCharacter.realize_single, Int.cast_one, one_smul]
  have hzetaTwoStage :
      ClassFunction.induce D (VirtualCharacter.realize rho) = zeta := by
    calc
      ClassFunction.induce D (VirtualCharacter.realize rho) =
          ClassFunction.induce D
            (ClassFunction.induce HD
              (thetaD : ClassFunction HD ℂ)) := by rw [hrhoRealize]
      _ = ClassFunction.induce D
          (ClassFunction.induce HD
            (ClassFunction.toSubgroupOf H D hHD
              (theta : ClassFunction H ℂ))) := by rw [hthetaTransport]
      _ = ClassFunction.induce H (theta : ClassFunction H ℂ) :=
        ClassFunction.induce_trans H D hHD _
      _ = zeta := hzetaInd.symm
  have hrhoConstituent
      (s : IrreducibleCharacter D ℂ) (hs : rho s ≠ 0) :
      s.IsConstituent
        (ClassFunction.induce HD (thetaD : ClassFunction HD ℂ)) := by
    unfold IrreducibleCharacter.IsConstituent
    have hcoeff :=
      VirtualCharacter.characterPairing_irreducible_realize s rho
    rw [hrhoRealize] at hcoeff
    rw [characterPairing_comm, hcoeff]
    exact Int.cast_ne_zero.mpr hs
  have hrhoNotKernel
      (s : IrreducibleCharacter D ℂ) (hs : rho s ≠ 0) :
      ¬ PD ≤ ClassFunction.translationKernel (s : ClassFunction D ℂ) := by
    intro hsKernel
    apply hthetaDNot
    rw [ClassFunction.translationKernel_irreducibleCharacter] at hsKernel ⊢
    exact (IrreducibleCharacter.sub_ker_constituent_induce_iff
      HD PD hPDHD s thetaD (hrhoConstituent s hs)).mpr hsKernel
  by_cases hselected : ∃ j : IrreducibleCharacter W₂ ℂ,
      rho (ctx.primeTI.primeTI_Ires ctx.isoS j) ≠ 0
  · obtain ⟨j, hjCoeff⟩ := hselected
    let s : IrreducibleCharacter D ℂ :=
      ctx.primeTI.primeTI_Ires ctx.isoS j
    have hsCoeff : rho s ≠ 0 := hjCoeff
    have hsNotKernel := hrhoNotKernel s hsCoeff
    have hj : j ≠ IrreducibleCharacter.trivial := by
      intro hj0
      subst j
      apply hsNotKernel
      dsimp only [s]
      rw [ctx.primeTI.prTIres0 ctx.isoS]
      intro x _
      rw [ClassFunction.mem_translationKernel_iff]
      intro y
      simp
    have hinner : characterPairing
        (thetaD : ClassFunction HD ℂ)
        (ClassFunction.restrict HD (s : ClassFunction D ℂ)) ≠ 0 := by
      have hpair : characterPairing
          (ClassFunction.induce HD (thetaD : ClassFunction HD ℂ))
          (s : ClassFunction D ℂ) ≠ 0 :=
        hrhoConstituent s hsCoeff
      rwa [ClassFunction.frobeniusReciprocity HD] at hpair
    have hpairZetaMu : characterPairing zeta (ctx.mu j) ≠ 0 := by
      rw [hzetaInd, ClassFunction.frobeniusReciprocity H]
      rw [characterPairing_restrict_chain H D hHD theta (ctx.mu j)]
      have hres := ctx.primeTI.cfRes_prTIred ctx.isoS j
      change ClassFunction.restrict D (ctx.mu j) =
        (Nat.card W₁ : ℂ) • (s : ClassFunction D ℂ) at hres
      rw [hres, map_smul, characterPairing_smul_right]
      exact mul_ne_zero
        (Nat.cast_ne_zero.mpr Nat.card_pos.ne') hinner
    have hzetaT : zeta ∈ seqIndT (k := ℂ) H :=
      FTTypePBoundsInfrastructureInternal.fittingCoreFamily_subset ctx hzeta
    have hmuT : ctx.mu j ∈ seqIndT (k := ℂ) H := by
      simpa only [ftTypePFittingFamily, H] using
        FTprTIred_Ind_Fitting ctx j hj
    have hzetaMu : zeta = ctx.mu j := by
      by_contra hne
      exact hpairZetaMu (seqInd_ortho H hzetaT hmuT hne)
    exact Or.inl ⟨j, hj, hzetaMu⟩
  · right
    rw [← hzetaTwoStage]
    apply induce_realize_mem_closure D (irreducibleCoreSet S) rho
    intro s hs
    have hsNotKernel := hrhoNotKernel s hs
    rcases ctx.primeTI.prTIres_irr_cases ctx.isoS s with
      ⟨j, hsSelected⟩ | ⟨hsIrr, _hsRectangle⟩
    · exfalso
      apply hselected
      refine ⟨j, ?_⟩
      rwa [← hsSelected]
    · have hcoreInd :
          ClassFunction.induce D (s : ClassFunction D ℂ) ∈
            ftTypePCoreFamily S := by
        change ClassFunction.induce D (s : ClassFunction D ℂ) ∈
          seqIndD (k := ℂ) D PD ⊥
        apply seqIndP.mpr
        exact ⟨s, mem_Iirr_kerD.mpr ⟨bot_le, hsNotKernel⟩, rfl⟩
      exact ⟨hcoreInd, hsIrr⟩

private theorem calS1_subset_coreClosure
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    (↑(FTTypePBoundsInfrastructureInternal.fittingCoreFamily ctx) :
        Set (ClassFunction S ℂ)) ⊆
      AddSubgroup.closure
        (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ)) := by
  intro zeta hzeta
  rcases S1cases ctx zeta hzeta with ⟨j, hj, rfl⟩ | hzetaCore
  · exact AddSubgroup.subset_closure (FTseqInd_TIred ctx j hj)
  · apply AddSubgroup.closure_mono _ hzetaCore
    intro phi hphi
    exact hphi.1

private abbrev calS1
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    Finset (ClassFunction S ℂ) :=
  FTTypePBoundsInfrastructureInternal.fittingCoreFamily ctx

/-! ## Moving between the ambient group and its top subgroup -/

private noncomputable def sourceMap :
    ClassFunction G ℂ →ₗ[ℂ] ClassFunction (⊤ : Subgroup G) ℂ :=
  ClassFunction.comap Subgroup.topEquiv.toMonoidHom

@[simp] private theorem sourceMap_targetMap
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (phi : ClassFunction (⊤ : Subgroup G) ℂ) :
    sourceMap (ctx.targetMap phi) = phi := by
  ext x
  simpa [sourceMap, ClassFunction.comap_apply] using
    congrArg phi (Subgroup.topEquiv.symm_apply_apply x)

@[simp] private theorem targetMap_sourceMap
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (phi : ClassFunction G ℂ) :
    ctx.targetMap (sourceMap phi) = phi := by
  ext x
  simpa [sourceMap, ClassFunction.comap_apply] using
    congrArg phi (Subgroup.topEquiv.apply_symm_apply x)

private theorem targetMap_pairing
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

private theorem sourceMap_pairing
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (phi psi : ClassFunction G ℂ) :
    characterPairing (sourceMap phi) (sourceMap psi) =
      characterPairing phi psi := by
  rw [← targetMap_pairing ctx (sourceMap phi) (sourceMap psi)]
  simp

private theorem sourceMap_virtual
    {phi : ClassFunction G ℂ}
    (hphi : ClassFunction.IsVirtual phi) :
    ClassFunction.IsVirtual (sourceMap phi) := by
  obtain ⟨z, hz⟩ := hphi
  refine ⟨VirtualCharacter.comap Subgroup.topEquiv.toMonoidHom z, ?_⟩
  rw [VirtualCharacter.realize_comap, hz]
  rfl

private theorem coherentWith_sourceMap
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    {T : Set (ClassFunction S ℂ)} {A : Set S}
    {sigma nu : ClassFunction S ℂ →ₗ[ℂ] ClassFunction G ℂ}
    (hcoh : coherent_with T A sigma nu) :
    coherent_with T A (sourceMap.comp sigma) (sourceMap.comp nu) := by
  refine
    { isometry := ?_
      mapsToVirtual := ?_
      agrees := ?_ }
  · intro phi hphi psi hpsi
    simpa [LinearMap.comp_apply] using
      (sourceMap_pairing ctx (nu phi) (nu psi)).trans
        (hcoh.isometry phi hphi psi hpsi)
  · intro phi hphi
    exact sourceMap_virtual (hcoh.mapsToVirtual phi hphi)
  · intro phi hphi hsupp
    simpa [LinearMap.comp_apply, hcoh.agrees phi hphi hsupp]

/-! ## The normalized-TI Dade datum on the nonidentity Fitting set -/

private abbrev HInS
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) : Subgroup S :=
  ctx.H.subgroupOf S

private abbrev PInH
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    Subgroup (HInS ctx) :=
  (ctx.P.subgroupOf S).subgroupOf (HInS ctx)

private theorem fittingSharp_normalizedTI
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    IsNormalizedTI (subgroupNonidentity ctx.H)
      (⊤ : Subgroup G) S :=
  (compl_of_typeII_IV S U W W₁ W₂ defW
    ctx.maxS ctx.StypeP ctx.notType5).2.2.2

private theorem fittingSharp_subset_top_nonidentity
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    subgroupNonidentity ctx.H ⊆
      (((⊤ : Subgroup G) : Set G) \ {(1 : G)}) := by
  rintro x ⟨hxH, hx⟩
  exact ⟨Subgroup.mem_top x, by simpa [Set.mem_singleton_iff] using hx⟩

private noncomputable def fittingSharpDade
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    DadeHypothesis (⊤ : Subgroup G) S
      (subgroupNonidentity ctx.H) :=
  normedTI_Dade (fittingSharp_normalizedTI ctx)
    (fittingSharp_subset_top_nonidentity ctx)

private theorem targetMap_eq_induce_top
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (phi : ClassFunction (⊤ : Subgroup G) ℂ) :
    ctx.targetMap phi = ClassFunction.induce (⊤ : Subgroup G) phi := by
  apply ClassFunction.ext
  intro x
  rw [ClassFunction.induce_apply_formula]
  have hvalue (y : G) :
      phi ⟨y⁻¹ * x * y, Subgroup.mem_top _⟩ =
        phi (Subgroup.topEquiv.symm x) := by
    have harg :
        (⟨y⁻¹ * x * y, Subgroup.mem_top _⟩ : (⊤ : Subgroup G)) =
          Subgroup.topEquiv.symm y⁻¹ *
            Subgroup.topEquiv.symm x *
              (Subgroup.topEquiv.symm y⁻¹)⁻¹ := by
      apply Subtype.ext
      simp
    rw [harg]
    exact ClassFunction.conj_apply phi
      (Subgroup.topEquiv.symm y⁻¹) (Subgroup.topEquiv.symm x)
  simp_rw [dif_pos (Subgroup.mem_top _), hvalue]
  simp only [ClassFunction.comap_apply, Finset.sum_const,
    nsmul_eq_mul, Finset.card_univ]
  rw [← Nat.card_eq_fintype_card,
    Nat.card_congr Subgroup.topEquiv.toEquiv]
  have hne : (Nat.card G : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp [hne]
  rfl

private theorem closure_fittingCore_supported
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    {phi : ClassFunction S ℂ}
    (hphi : phi ∈ AddSubgroup.closure
      (↑(FTTypePBoundsInfrastructureInternal.fittingCoreFamily ctx) :
        Set (ClassFunction S ℂ))) :
    phi ∈ ClassFunction.supportedOn (HInS ctx : Set S) := by
  induction hphi using AddSubgroup.closure_induction with
  | mem xi hxi =>
      apply seqInd_on (HInS ctx)
      simpa only [ftTypePFittingFamily, seqIndT, HInS] using
        FTTypePBoundsInfrastructureInternal.fittingCoreFamily_subset
          ctx hxi
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | neg x _ hx => exact Submodule.neg_mem _ hx

private theorem fittingCore_support_on_sharp
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    {phi : ClassFunction S ℂ}
    (hspan : phi ∈ AddSubgroup.closure
      (↑(FTTypePBoundsInfrastructureInternal.fittingCoreFamily ctx) :
        Set (ClassFunction S ℂ)))
    (hoff : phi ∈ ClassFunction.supportedOn (nonidentitySet S)) :
    phi ∈ ClassFunction.supportedOn
      {x : S | (x : G) ∈ subgroupNonidentity ctx.H} := by
  have hH := closure_fittingCore_supported ctx hspan
  rw [ClassFunction.mem_supportedOn_iff] at hH hoff ⊢
  intro x hx
  by_cases hxH : x ∈ HInS ctx
  · apply hoff
    intro hxOne
    apply hx
    exact ⟨hxH, by
      intro hval
      apply hxOne
      exact Subtype.ext hval⟩
  · exact hH x hxH

private theorem targetMap_fittingDade_eq_tau
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    {phi : ClassFunction S ℂ}
    (hspan : phi ∈ AddSubgroup.closure
      (↑(FTTypePBoundsInfrastructureInternal.fittingCoreFamily ctx) :
        Set (ClassFunction S ℂ)))
    (hoff : phi ∈ ClassFunction.supportedOn (nonidentitySet S)) :
    ctx.targetMap (Dade (fittingSharpDade ctx) phi) = ctx.tau phi := by
  have hsharp := fittingCore_support_on_sharp ctx hspan hoff
  have hDade := Dade_Ind (fittingSharpDade ctx)
    (fittingSharp_normalizedTI ctx) phi hsharp
  have hsupp0 : phi ∈ ClassFunction.supportedOn (ftTypePSupport0InS S) := by
    rw [ClassFunction.mem_supportedOn_iff]
    intro x hx
    apply ClassFunction.eq_zero_of_mem_supportedOn hsharp
    intro hxsharp
    apply hx
    exact Fitting_sub_FTsupp0 ctx.maxS hxsharp
  obtain ⟨_, _, _, _, _, _, _, _, _, htau⟩ := FTtypeP_facts ctx
  calc
    ctx.targetMap (Dade (fittingSharpDade ctx) phi) =
        ctx.targetMap
          (ClassFunction.induce (S.subgroupOf (⊤ : Subgroup G))
            (ClassFunction.toSubgroupOf S (⊤ : Subgroup G) le_top phi)) :=
      congrArg ctx.targetMap hDade
    _ = ClassFunction.induce (⊤ : Subgroup G)
        (ClassFunction.induce (S.subgroupOf (⊤ : Subgroup G))
          (ClassFunction.toSubgroupOf S (⊤ : Subgroup G) le_top phi)) :=
      targetMap_eq_induce_top ctx _
    _ = ClassFunction.induce S phi :=
      ClassFunction.induce_trans S (⊤ : Subgroup G) le_top phi
    _ = ctx.tau phi := (htau phi hsupp0).symm

private theorem fittingDade_coherentWith
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (tau1 : ClassFunction S ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (hcoh : coherent_with
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
      (nonidentitySet S) ctx.tau tau1)
    (hspan :
      (↑(FTTypePBoundsInfrastructureInternal.fittingCoreFamily ctx) :
          Set (ClassFunction S ℂ)) ⊆
        AddSubgroup.closure
          (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))) :
    coherent_with
      (↑(FTTypePBoundsInfrastructureInternal.fittingCoreFamily ctx) :
        Set (ClassFunction S ℂ))
      (nonidentitySet S) (Dade (fittingSharpDade ctx))
      (sourceMap.comp tau1) := by
  have hclosure :
      AddSubgroup.closure
          (↑(FTTypePBoundsInfrastructureInternal.fittingCoreFamily ctx) :
            Set (ClassFunction S ℂ)) ≤
        AddSubgroup.closure
          (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ)) :=
    (AddSubgroup.closure_le _).2 hspan
  have hsmall : coherent_with
      (↑(FTTypePBoundsInfrastructureInternal.fittingCoreFamily ctx) :
        Set (ClassFunction S ℂ))
      (nonidentitySet S) ctx.tau tau1 :=
    { isometry := fun phi hphi psi hpsi ↦
        hcoh.isometry phi (hclosure hphi) psi (hclosure hpsi)
      mapsToVirtual := fun phi hphi ↦
        hcoh.mapsToVirtual phi (hclosure hphi)
      agrees := fun phi hphi hoff ↦
        hcoh.agrees phi (hclosure hphi) hoff }
  have htop := coherentWith_sourceMap ctx hsmall
  refine
    { isometry := htop.isometry
      mapsToVirtual := htop.mapsToVirtual
      agrees := ?_ }
  intro phi hphi hoff
  have htarget := targetMap_fittingDade_eq_tau ctx hphi hoff
  calc
    (sourceMap.comp tau1) phi = (sourceMap.comp ctx.tau) phi :=
      htop.agrees phi hphi hoff
    _ = Dade (fittingSharpDade ctx) phi := by
      change sourceMap (ctx.tau phi) = _
      calc
        sourceMap (ctx.tau phi) =
            sourceMap
              (ctx.targetMap (Dade (fittingSharpDade ctx) phi)) :=
          congrArg sourceMap htarget.symm
        _ = Dade (fittingSharpDade ctx) phi :=
          sourceMap_targetMap ctx _

/-! ## Finite sums, norms, and signed cyclic-TI rows -/

private theorem finiteSet_card_eq_ncard
    {Q : Type u} [Fintype Q] (A : Set Q) :
    (FTTypePBoundsInfrastructureInternal.finiteSet A).card = A.ncard := by
  have hfinite :
      FTTypePBoundsInfrastructureInternal.finiteSet A =
        (Set.toFinite A).toFinset := by
    ext x
    simp [FTTypePBoundsInfrastructureInternal.finiteSet]
  rw [hfinite]
  exact (Set.ncard_eq_toFinset_card A (Set.toFinite A)).symm

private theorem subgroupNonidentity_ncard
    {Q : Type u} [Group Q] [Fintype Q] (K : Subgroup Q) :
    (subgroupNonidentity K).ncard = Nat.card K - 1 := by
  have hone : (1 : Q) ∈ (K : Set Q) := K.one_mem
  rw [show subgroupNonidentity K = (K : Set Q) \ {1} by
    ext x
    simp [subgroupNonidentity, nonidentitySet]]
  rw [Set.ncard_sdiff_singleton_of_mem hone, ← Nat.card_coe_set_eq,
    SetLike.coe_sort_coe]

private theorem setCard_subgroupNonidentity
    {Q : Type u} [Group Q] [Fintype Q] (K : Subgroup Q) :
    (FTTypePBoundsInfrastructureInternal.finiteSet
      (subgroupNonidentity K)).card = Nat.card K - 1 := by
  rw [finiteSet_card_eq_ncard, subgroupNonidentity_ncard]

private theorem semidirectCard
    {A B K : Subgroup G}
    (h : IsInternalSemidirectProductIn A B K) :
    Nat.card A * Nat.card B = Nat.card K := by
  simpa only [MathlibSupport.natCard_subgroupOf_eq h.1,
    MathlibSupport.natCard_subgroupOf_eq h.2.1] using
      h.2.2.2.card_mul

private theorem maximalCard
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    Nat.card ctx.PU * ctx.q = Nat.card S := by
  simpa only [FTTypePSetupContext.q] using
    semidirectCard ctx.StypeP.1.2.2.2

private theorem pairing_fintype_sum_left
    {Q I : Type*} [Group Q] [Fintype Q] [Fintype I]
    (f : I → ClassFunction Q ℂ) (psi : ClassFunction Q ℂ) :
    characterPairing (∑ i, f i) psi =
      ∑ i, characterPairing (f i) psi := by
  change characterPairingRight psi (∑ i, f i) = _
  exact map_sum (characterPairingRight psi) f Finset.univ

private theorem irreducible_isVirtual
    {Q : Type u} [Group Q] [Fintype Q]
    (chi : IrreducibleCharacter Q ℂ) :
    ClassFunction.IsVirtual (chi : ClassFunction Q ℂ) := by
  refine ⟨Finsupp.single chi 1, ?_⟩
  simp

private theorem irreducible_classFunctionNormSq
    {Q : Type u} [Group Q] [Fintype Q]
    (chi : IrreducibleCharacter Q ℂ) :
    classFunctionNormSq (chi : ClassFunction Q ℂ) = 1 := by
  letI : Invertible (Nat.card Q : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [classFunctionNormSq_eq_re_starCharacterPairing,
    PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
      (irreducible_isVirtual chi) (irreducible_isVirtual chi),
    IrreducibleCharacter.characterPairing_self chi]
  norm_num

private theorem irreducible_degree_one_of_commutative
    {Q : Type u} [Group Q] [Fintype Q] [IsMulCommutative Q]
    (chi : IrreducibleCharacter Q ℂ) :
    chi 1 = 1 := by
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Representation.IsIrreducible chi.representation.ρ :=
    MathlibSupport.representation_isIrreducible_of_simple_fdRep
      chi.representation
  rw [IrreducibleCharacter.apply_one_eq_finrank,
    Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative
      chi.representation.ρ]
  norm_num

private theorem classFunctionNormSq_of_virtualWitness
    {Q : Type u} [Group Q] [Fintype Q]
    (alpha : ClassFunction Q ℂ) (n : ℕ)
    (hwitness : ∃ z : VirtualCharacter Q ℂ,
      VirtualCharacter.realize z = alpha ∧ normSq z = (n : ℤ)) :
    classFunctionNormSq alpha = (n : ℝ) := by
  obtain ⟨z, hz, hnorm⟩ := hwitness
  have hvirtual : ClassFunction.IsVirtual alpha := ⟨z, hz⟩
  rw [classFunctionNormSq_eq_re_starCharacterPairing,
    PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
      hvirtual hvirtual, ← hz,
    VirtualCharacter.characterPairing_realize_self, hnorm]
  norm_num

/- `sumNormSq_subgroupNonidentity_eq` is intentionally universe-zero, so this
adapter is universe-zero at precisely the same dependency boundary. -/
private theorem virtual_mass_eq
    {Q : Type} [Group Q] [Fintype Q]
    (alpha : ClassFunction Q ℂ) (d : ℤ) (n : ℕ)
    (hone : alpha 1 = (d : ℂ))
    (hwitness : ∃ z : VirtualCharacter Q ℂ,
      VirtualCharacter.realize z = alpha ∧ normSq z = (n : ℤ)) :
    ftTypePSumNormSq (nonidentitySet Q) alpha =
      (Nat.card Q : ℝ) * (n : ℝ) - (d : ℝ) ^ 2 := by
  have hsupp : alpha ∈
      ClassFunction.supportedOn (((⊤ : Subgroup Q) : Set Q)) := by
    rw [ClassFunction.mem_supportedOn_iff]
    simp
  have hset : nonidentitySet Q =
      subgroupNonidentity (⊤ : Subgroup Q) := by
    ext x
    simp [subgroupNonidentity, nonidentitySet]
  rw [hset,
    FTTypePGeneratorBoundsInternal.sumNormSq_subgroupNonidentity_eq
      (⊤ : Subgroup Q) alpha hsupp,
    classFunctionNormSq_of_virtualWitness alpha n hwitness,
    hone, Complex.normSq_intCast]
  ring

private theorem eta_eq_signed_irreducible
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) :
    ∃ (chi : IrreducibleCharacter G ℂ) (epsilon : ℤ),
      IsSign epsilon ∧
        ctx.eta i j =
          (epsilon : ℂ) • (chi : ClassFunction G ℂ) := by
  obtain ⟨chiTop, epsilon, hepsilon, himage⟩ :=
    ctx.isoG.cyclicTIImage_eq_signed_irreducible (i, j)
  let chi : IrreducibleCharacter G ℂ :=
    IrreducibleCharacter.comapMulEquiv Subgroup.topEquiv.symm chiTop
  refine ⟨chi, epsilon, hepsilon, ?_⟩
  apply ClassFunction.ext
  intro x
  have hat := congrArg
    (fun phi : ClassFunction (⊤ : Subgroup G) ℂ ↦
      phi (Subgroup.topEquiv.symm x)) himage
  change ctx.isoG.cyclicTIImage (i, j) (Subgroup.topEquiv.symm x) =
    (epsilon : ℂ) * chi x
  simpa only [ClassFunction.smul_apply, smul_eq_mul, chi,
    IrreducibleCharacter.comapMulEquiv_apply] using hat

private theorem eta_isVirtual
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) :
    ClassFunction.IsVirtual (ctx.eta i j) := by
  obtain ⟨chi, epsilon, _hepsilon, heta⟩ :=
    eta_eq_signed_irreducible ctx i j
  refine ⟨Finsupp.single chi epsilon, ?_⟩
  rw [VirtualCharacter.realize_single]
  exact heta.symm

private theorem signIndex_involutive
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
      change IrreducibleCharacter.dual j ≠
        IrreducibleCharacter.trivial
      intro hdual
      apply hj
      calc
        j = IrreducibleCharacter.dual
            (IrreducibleCharacter.dual j) :=
          (IrreducibleCharacter.dual_dual j).symm
        _ = IrreducibleCharacter.dual
            IrreducibleCharacter.trivial :=
          congrArg IrreducibleCharacter.dual hdual
        _ = IrreducibleCharacter.trivial :=
          IrreducibleCharacter.dual_trivial

private theorem intSign_cast (b : Bool) :
    (((if b then -1 else 1 : ℤ) : ℂ)) = ftTypePBooleanSign b := by
  cases b <;> simp [ftTypePBooleanSign]

private theorem mu_pairing_eta10_eq_zero
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (tau1 : ClassFunction S ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (b : Bool) (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial)
    (hrow : tau1 (ctx.mu j) =
      ftTypePBooleanSign b •
        ∑ i : IrreducibleCharacter W₁ ℂ,
          ctx.eta i (ftTypePSignIndex b j)) :
    characterPairing (tau1 (ctx.mu j)) (ftTypePEta10 ctx) = 0 := by
  rw [hrow, characterPairing_smul_left, pairing_fintype_sum_left]
  have hsum :
      (∑ i : IrreducibleCharacter W₁ ℂ,
        characterPairing (ctx.eta i (ftTypePSignIndex b j))
          (ftTypePEta10 ctx)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [ftTypePEta10,
      FTTypePCyclicRectangleInternal.characterPairing_eta, if_neg]
    intro hpairs
    exact signIndex_ne_trivial b j hj (congrArg Prod.snd hpairs)
  rw [hsum, mul_zero]

/-! ## Integral-square inequalities -/

private theorem one_le_Pcard_sub_one
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    (1 : ℝ) ≤ ((Nat.card ctx.P - 1 : ℕ) : ℝ) := by
  have hpThree : 3 ≤ ctx.p :=
    ctx.primeTI.prime_cycTIhyp.two_lt_card_right
  have hpDvd : ctx.p ∣ Nat.card ctx.P := by
    simpa only [FTTypePSetupContext.p] using
      Subgroup.card_dvd_of_le ctx.StypeP.2.2.2.1.2.2.1
  have hpLe : ctx.p ≤ Nat.card ctx.P :=
    Nat.le_of_dvd Nat.card_pos hpDvd
  have honeNat : 1 ≤ Nat.card ctx.P - 1 := by omega
  exact_mod_cast honeNat

private theorem virtual_mass_ge_card_sub_one
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (alpha : ClassFunction ctx.H ℂ)
    (alphaDegree : ℤ) (alphaNorm : ℕ)
    (halphaOne : alpha 1 = (alphaDegree : ℂ))
    (halphaWitness : ∃ z : VirtualCharacter ctx.H ℂ,
      VirtualCharacter.realize z = alpha ∧
        normSq z = (alphaNorm : ℤ))
    (halphaNe : alpha ≠ 0)
    (hresidual :
      ((Nat.card ctx.P - 1 : ℕ) : ℝ) *
          (alphaDegree : ℝ) ^ 2 ≤
        ftTypePSumNormSq (nonidentitySet ctx.H) alpha) :
    ((Nat.card ctx.H - 1 : ℕ) : ℝ) ≤
      ftTypePSumNormSq (nonidentitySet ctx.H) alpha := by
  have hmass := virtual_mass_eq alpha alphaDegree alphaNorm
    halphaOne halphaWitness
  have hnorm := classFunctionNormSq_of_virtualWitness
    alpha alphaNorm halphaWitness
  have halphaNormNe : alphaNorm ≠ 0 := by
    intro hzero
    apply halphaNe
    apply (classFunctionNormSq_eq_zero_iff alpha).mp
    rw [hnorm, hzero]
    norm_num
  have halphaNormPos : 1 ≤ alphaNorm := by omega
  have hHcast : ((Nat.card ctx.H - 1 : ℕ) : ℝ) =
      (Nat.card ctx.H : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.card_pos (α := ctx.H))]
    norm_num
  by_cases hnormOne : alphaNorm = 1
  · obtain ⟨z, hz, hzNorm⟩ := halphaWitness
    have hzNormOne : normSq z = 1 := by
      simpa [hnormOne] using hzNorm
    obtain ⟨chi, epsilon, hepsilon, hzSingle⟩ :=
      eq_signed_single_of_normSq_eq_one z hzNormOne
    have halphaSigned :
        alpha = (epsilon : ℂ) • (chi : ClassFunction ctx.H ℂ) := by
      calc
        alpha = VirtualCharacter.realize z := hz.symm
        _ = VirtualCharacter.realize (Finsupp.single chi epsilon) := by
          rw [hzSingle]
        _ = (epsilon : ℂ) • (chi : ClassFunction ctx.H ℂ) := by
          rw [VirtualCharacter.realize_single]
    letI : IsMulCommutative ctx.H := FTtypeP_Fitting_abelian ctx
    have hdegreeOne := irreducible_degree_one_of_commutative chi
    have hdegreeCast : (alphaDegree : ℂ) = (epsilon : ℂ) := by
      calc
        (alphaDegree : ℂ) = alpha 1 := halphaOne.symm
        _ = (epsilon : ℂ) * chi 1 := by
          rw [halphaSigned]
          rfl
        _ = (epsilon : ℂ) := by rw [hdegreeOne, mul_one]
    have hdegreeEq : alphaDegree = epsilon :=
      Int.cast_injective hdegreeCast
    have hdegreeSq : (alphaDegree : ℝ) ^ 2 = 1 := by
      rw [hdegreeEq]
      rcases hepsilon with rfl | rfl <;> norm_num
    rw [hmass, hnormOne, hdegreeSq, hHcast]
    norm_num
  · have hnormTwo : 2 ≤ alphaNorm := by omega
    by_cases hdegreeSmall :
        (alphaDegree : ℝ) ^ 2 < (Nat.card ctx.H : ℝ)
    · have hdegreeSmallInt :
          alphaDegree ^ 2 < (Nat.card ctx.H : ℤ) := by
        exact_mod_cast hdegreeSmall
      have hdegreeLeInt :
          alphaDegree ^ 2 ≤ (Nat.card ctx.H : ℤ) - 1 := by
        omega
      have hdegreeLe : (alphaDegree : ℝ) ^ 2 ≤
          (Nat.card ctx.H : ℝ) - 1 := by
        exact_mod_cast hdegreeLeInt
      have hHnonneg : (0 : ℝ) ≤ (Nat.card ctx.H : ℝ) := by
        positivity
      have hnormTwoReal : (2 : ℝ) ≤ (alphaNorm : ℝ) := by
        exact_mod_cast hnormTwo
      have hproduct :
          (Nat.card ctx.H : ℝ) * 2 ≤
            (Nat.card ctx.H : ℝ) * (alphaNorm : ℝ) :=
        mul_le_mul_of_nonneg_left hnormTwoReal hHnonneg
      rw [hmass, hHcast]
      norm_num only [Nat.cast_ofNat]
      nlinarith [hproduct]
    · have hHle :
          (Nat.card ctx.H : ℝ) ≤ (alphaDegree : ℝ) ^ 2 :=
        le_of_not_gt hdegreeSmall
      have hdegreeLeMass :
          (alphaDegree : ℝ) ^ 2 ≤
            ftTypePSumNormSq (nonidentitySet ctx.H) alpha := by
        calc
          (alphaDegree : ℝ) ^ 2 ≤
              ((Nat.card ctx.P - 1 : ℕ) : ℝ) *
                (alphaDegree : ℝ) ^ 2 := by
            nlinarith [one_le_Pcard_sub_one ctx,
              sq_nonneg (alphaDegree : ℝ)]
          _ ≤ _ := hresidual
      rw [hHcast]
      nlinarith

private theorem lambda_mass_lower
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (lambda : ClassFunction S ℂ)
    (hirr : lambda ∈ irr_Ind_Fitting S)
    (a alphaDegree : ℤ) (alphaMass totalMass : ℝ)
    (ha : a = 1)
    (hlambdaNorm : classFunctionNormSq lambda = 1)
    (hmass : totalMass =
      (a : ℝ) ^ 2 * (classFunctionNormSq lambda)⁻¹ *
          ((Nat.card S : ℝ) -
            Complex.normSq (lambda 1) *
              (classFunctionNormSq lambda)⁻¹) -
        2 * (a : ℝ) *
          ((lambda 1).re * (alphaDegree : ℝ) *
            (classFunctionNormSq lambda)⁻¹) +
        alphaMass)
    (hresidual :
      ((Nat.card ctx.P - 1 : ℕ) : ℝ) *
          (alphaDegree : ℝ) ^ 2 ≤ alphaMass)
    (hdiv : (ctx.q : ℤ) ∣ alphaDegree) :
    (Nat.card S : ℝ) - Complex.normSq (lambda 1) ≤ totalMass := by
  have hmassSimple : totalMass =
      (Nat.card S : ℝ) - Complex.normSq (lambda 1) -
        2 * (lambda 1).re * (alphaDegree : ℝ) + alphaMass := by
    rw [ha, hlambdaNorm] at hmass
    norm_num only [Int.cast_one, one_pow, inv_one, one_mul, mul_one]
      at hmass
    linear_combination hmass
  have hlambdaOne := FTtypeP_Ind_Fitting_1 ctx lambda hirr.2
  have hlambdaOneReal :
      (lambda 1).re = ((ctx.u * ctx.q : ℕ) : ℝ) := by
    rw [hlambdaOne]
    norm_num
  obtain ⟨b, hb⟩ := hdiv
  have hP1 := FTTypePGeneratorBoundsInternal.P1_int2 ctx b
  have hP1scaled := mul_le_mul_of_nonneg_right hP1
    (sq_nonneg (ctx.q : ℝ))
  have hcross :
      2 * ((ctx.u * ctx.q : ℕ) : ℝ) *
          (alphaDegree : ℝ) ≤
        ((Nat.card ctx.P - 1 : ℕ) : ℝ) *
          (alphaDegree : ℝ) ^ 2 := by
    rw [hb]
    norm_num only [Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    nlinarith [hP1scaled]
  rw [hlambdaOneReal] at hmassSimple
  nlinarith

private theorem eta01_mass_lower
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (b : Bool) (a alphaDegree : ℤ)
    (alphaMass totalMass : ℝ)
    (ha : a = (if b then -1 else 1 : ℤ))
    (hmuNorm : classFunctionNormSq
      (ctx.mu (ftTypePSignIndex b (ftTypePRightIndex ctx))) =
        (ctx.q : ℝ))
    (hmass : totalMass =
      (a : ℝ) ^ 2 *
          (classFunctionNormSq
            (ctx.mu (ftTypePSignIndex b
              (ftTypePRightIndex ctx))))⁻¹ *
          ((Nat.card S : ℝ) -
            Complex.normSq
                (ctx.mu (ftTypePSignIndex b
                  (ftTypePRightIndex ctx)) 1) *
              (classFunctionNormSq
                (ctx.mu (ftTypePSignIndex b
                  (ftTypePRightIndex ctx))))⁻¹) -
        2 * (a : ℝ) *
          ((ctx.mu (ftTypePSignIndex b
                (ftTypePRightIndex ctx)) 1).re *
            (alphaDegree : ℝ) *
              (classFunctionNormSq
                (ctx.mu (ftTypePSignIndex b
                  (ftTypePRightIndex ctx))))⁻¹) +
        alphaMass)
    (hresidual :
      ((Nat.card ctx.P - 1 : ℕ) : ℝ) *
          (alphaDegree : ℝ) ^ 2 ≤ alphaMass) :
    (Nat.card ctx.PU : ℝ) - (ctx.u : ℝ) ^ 2 ≤ totalMass := by
  let j1 : IrreducibleCharacter W₂ ℂ :=
    ftTypePSignIndex b (ftTypePRightIndex ctx)
  have hj1 : j1 ≠ IrreducibleCharacter.trivial :=
    signIndex_ne_trivial b (ftTypePRightIndex ctx)
      (FTTypePBoundsInfrastructureInternal.rightIndex_ne_trivial ctx)
  have hmuOne : ctx.mu j1 1 = ((ctx.u * ctx.q : ℕ) : ℂ) :=
    FTprTIred1 ctx j1 hj1
  have hmuRe : (ctx.mu j1 1).re =
      ((ctx.u * ctx.q : ℕ) : ℝ) := by
    rw [hmuOne]
    norm_num
  have hmuSq : Complex.normSq (ctx.mu j1 1) =
      (((ctx.u * ctx.q : ℕ) : ℝ)) ^ 2 := by
    rw [hmuOne, Complex.normSq_natCast]
    ring
  have hqPos : (0 : ℝ) < ctx.q := Nat.cast_pos.mpr Nat.card_pos
  have hqNe : (ctx.q : ℝ) ≠ 0 := hqPos.ne'
  have hSCard : (Nat.card S : ℝ) =
      (Nat.card ctx.PU : ℝ) * (ctx.q : ℝ) := by
    exact_mod_cast (maximalCard ctx).symm
  have hsignSq :
      (((if b then -1 else 1 : ℤ) : ℝ)) ^ 2 = 1 := by
    cases b <;> norm_num
  have hmassSimple : totalMass =
      (Nat.card ctx.PU : ℝ) - (ctx.u : ℝ) ^ 2 -
        2 * (((if b then -1 else 1 : ℤ) : ℝ)) *
          (ctx.u : ℝ) * (alphaDegree : ℝ) + alphaMass := by
    change totalMass =
      (a : ℝ) ^ 2 *
          (classFunctionNormSq (ctx.mu j1))⁻¹ *
          ((Nat.card S : ℝ) - Complex.normSq (ctx.mu j1 1) *
            (classFunctionNormSq (ctx.mu j1))⁻¹) -
        2 * (a : ℝ) * ((ctx.mu j1 1).re *
          (alphaDegree : ℝ) *
            (classFunctionNormSq (ctx.mu j1))⁻¹) + alphaMass
      at hmass
    calc
      totalMass =
          (a : ℝ) ^ 2 *
              (classFunctionNormSq (ctx.mu j1))⁻¹ *
              ((Nat.card S : ℝ) - Complex.normSq (ctx.mu j1 1) *
                (classFunctionNormSq (ctx.mu j1))⁻¹) -
            2 * (a : ℝ) * ((ctx.mu j1 1).re *
              (alphaDegree : ℝ) *
                (classFunctionNormSq (ctx.mu j1))⁻¹) + alphaMass :=
        hmass
      _ = _ := by
        change classFunctionNormSq (ctx.mu j1) = (ctx.q : ℝ) at hmuNorm
        rw [ha, hmuNorm, hmuRe, hmuSq, hSCard, hsignSq]
        field_simp [hqNe]
        norm_num only [Nat.cast_mul]
        ring
  have hP1 := FTTypePGeneratorBoundsInternal.P1_int2 ctx
    ((if b then -1 else 1 : ℤ) * alphaDegree)
  have hcross :
      2 * (((if b then -1 else 1 : ℤ) : ℝ)) *
          (ctx.u : ℝ) * (alphaDegree : ℝ) ≤
        ((Nat.card ctx.P - 1 : ℕ) : ℝ) *
          (alphaDegree : ℝ) ^ 2 := by
    norm_num only [Int.cast_mul] at hP1
    calc
      2 * (((if b then -1 else 1 : ℤ) : ℝ)) *
            (ctx.u : ℝ) * (alphaDegree : ℝ) =
          2 * (ctx.u : ℝ) *
            ((((if b then -1 else 1 : ℤ) : ℝ)) *
              (alphaDegree : ℝ)) := by ring
      _ ≤ ((Nat.card ctx.P - 1 : ℕ) : ℝ) *
            ((((if b then -1 else 1 : ℤ) : ℝ)) *
              (alphaDegree : ℝ)) ^ 2 := hP1
      _ = ((Nat.card ctx.P - 1 : ℕ) : ℝ) *
            (alphaDegree : ℝ) ^ 2 := by
        rw [mul_pow, hsignSq, one_mul]
  nlinarith

private theorem mu_classFunctionNormSq
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ) :
    classFunctionNormSq (ctx.mu j) = (ctx.q : ℝ) := by
  have hvirtual : ClassFunction.IsVirtual (ctx.mu j) :=
    (ctx.primeTI.prTIred_char ctx.isoS j).isVirtual
  rw [classFunctionNormSq_eq_re_starCharacterPairing,
    PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
      hvirtual hvirtual,
    ctx.primeTI.cfnorm_prTIred ctx.isoS j]
  norm_num

private theorem coreClosure_of_S1case
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (zeta : ClassFunction S ℂ)
    (hcase :
      (∃ j : IrreducibleCharacter W₂ ℂ,
        j ≠ IrreducibleCharacter.trivial ∧ zeta = ctx.mu j) ∨
      zeta ∈ AddSubgroup.closure
        {phi : ClassFunction S ℂ |
          phi ∈ ftTypePCoreFamily S ∧
            IsIrreducibleCharacter S ℂ phi}) :
    zeta ∈ AddSubgroup.closure
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ)) := by
  rcases hcase with ⟨j, hj, rfl⟩ | hclosure
  · exact AddSubgroup.subset_closure (FTseqInd_TIred ctx j hj)
  · exact (AddSubgroup.closure_mono
      (fun phi hphi ↦ hphi.1)) hclosure

/-! ## Orthogonality to the cyclic-TI image -/

private theorem coreFamily_cfConjC_subset
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    cfConjC_subset
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
      (FTtypePKernelLayer ctx.primeDadeF) := by
  refine ⟨?_, ?_⟩
  · intro phi hphi
    simpa only [ftTypePCoreFamily, FTtypePKernelLayer,
      PrimeDadeHypothesis.signalizerInKernel] using hphi
  · intro phi hphi
    change phi ∈ seqIndD (k := ℂ)
      (pTypeCoreDerived S) (pTypeCoreFitting S) ⊥ at hphi
    change ClassFunction.inverseLinear phi ∈ seqIndD (k := ℂ)
      (pTypeCoreDerived S) (pTypeCoreFitting S) ⊥
    exact seqInd_inverse_mem (k := ℂ)
      (pTypeCoreDerived S) (pTypeCoreFitting S) ⊥ hphi

/- This is the single top-subgroup coherence adapter used by both the
pairing and pointwise-vanishing arguments below. -/
private theorem primeDade_coherentWith_top
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (tau1 : ClassFunction S ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (hcoh : coherent_with
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
      (nonidentitySet S) ctx.tau tau1) :
    coherent_with
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
      (nonidentitySet S)
      (Dade ctx.primeDadeF.prDade_hyp) (sourceMap.comp tau1) := by
  have hsource := coherentWith_sourceMap ctx hcoh
  exact
    { isometry := hsource.isometry
      mapsToVirtual := hsource.mapsToVirtual
      agrees := by
        intro phi hphi hsupp
        have hagree := hsource.agrees phi hphi hsupp
        simpa only [FTTypePSetupContext.tau, LinearMap.comp_apply,
          sourceMap_targetMap] using hagree }

private theorem coherent_ortho_eta
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (tau1 : ClassFunction S ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (hcoh : coherent_with
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
      (nonidentitySet S) ctx.tau tau1)
    (phi : ClassFunction S ℂ)
    (hphi : phi ∈ ftTypePCoreFamily S)
    (hirr : IsIrreducibleCharacter S ℂ phi)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) :
    characterPairing (tau1 phi) (ctx.eta i j) = 0 := by
  have htop := coherent_ortho_cycTIiso
    ctx.primeDadeF ctx.isoS ctx.isoG (mFT_odd S)
    (coreFamily_cfConjC_subset ctx)
    (primeDade_coherentWith_top ctx tau1 hcoh)
    hphi hirr
    (IrreducibleCharacter.cyclicTICharacter defW i j)
  rw [← sourceMap_pairing ctx (tau1 phi) (ctx.eta i j)]
  simpa only [LinearMap.comp_apply, FTTypePSetupContext.eta,
    sourceMap_targetMap,
    CyclicTIIsometryData.cyclicTIImage,
    CyclicTIIsometryData.cyclicTISourceIrreducible] using htop

private theorem coherent_image_vanish_on_cyclicTI
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (tau1 : ClassFunction S ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (hcoh : coherent_with
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
      (nonidentitySet S) ctx.tau tau1)
    (phi : ClassFunction S ℂ)
    (hphi : phi ∈ ftTypePCoreFamily S)
    (hirr : IsIrreducibleCharacter S ℂ phi) :
    Set.EqOn (fun w : W ↦ tau1 phi (w : G)) 0
      (cyclicTISetInW W W₁ W₂) := by
  have horth (chi : IrreducibleCharacter W ℂ) :
      characterPairing (sourceMap (tau1 phi))
        (ctx.isoG.linearMap (chi : ClassFunction W ℂ)) = 0 := by
    simpa only [LinearMap.comp_apply] using
      coherent_ortho_cycTIiso
        ctx.primeDadeF ctx.isoS ctx.isoG (mFT_odd S)
        (coreFamily_cfConjC_subset ctx)
        (primeDade_coherentWith_top ctx tau1 hcoh)
        hphi hirr chi
  have hvanish := ctx.isoG.orthogonal_vanish
    (sourceMap (tau1 phi)) horth
  intro w hw
  simpa [sourceMap, ClassFunction.comap_apply] using hvanish hw

private theorem coreIrrClosure_pairing_eta_eq_zero
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (tau1 : ClassFunction S ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (hcoh : coherent_with
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
      (nonidentitySet S) ctx.tau tau1)
    (zeta : ClassFunction S ℂ)
    (hzeta : zeta ∈ AddSubgroup.closure
      {phi : ClassFunction S ℂ |
        phi ∈ ftTypePCoreFamily S ∧
          IsIrreducibleCharacter S ℂ phi})
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) :
    characterPairing (tau1 zeta) (ctx.eta i j) = 0 := by
  induction hzeta using AddSubgroup.closure_induction with
  | mem phi hphi =>
      exact coherent_ortho_eta ctx tau1 hcoh phi hphi.1 hphi.2 i j
  | zero => simp
  | add phi psi _ _ hphi hpsi =>
      simp only [map_add, characterPairing_add_left,
        hphi, hpsi, add_zero]
  | neg phi _ hphi =>
      change characterPairingRight (ctx.eta i j) (tau1 (-phi)) = 0
      change characterPairingRight (ctx.eta i j) (tau1 phi) = 0 at hphi
      simp only [map_neg, hphi, neg_zero]

/-! ## Primitive-root congruences for the two Fitting factors -/

private theorem q_prime
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) : ctx.q.Prime := by
  simpa only [FTTypePSetupContext.q] using
    (FTtypeP_primes S U W W₁ W₂ defW ctx.maxS ctx.StypeP).1

private theorem p_prime
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) : ctx.p.Prime := by
  simpa only [FTTypePSetupContext.p] using
    (FTtypeP_primes S U W W₁ W₂ defW ctx.maxS ctx.StypeP).2

private theorem exists_factor_prime_elements
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ∃ (y : W₁) (x : W₂),
      orderOf y = ctx.q ∧ orderOf x = ctx.p := by
  letI : Fact ctx.q.Prime := ⟨q_prime ctx⟩
  letI : Fact ctx.p.Prime := ⟨p_prime ctx⟩
  obtain ⟨y, hy⟩ :=
    exists_prime_orderOf_dvd_card' (G := W₁) ctx.q (by
      simp [FTTypePSetupContext.q])
  obtain ⟨x, hx⟩ :=
    exists_prime_orderOf_dvd_card' (G := W₂) ctx.p (by
      simp [FTTypePSetupContext.p])
  exact ⟨y, x, hy, hx⟩

private theorem ne_one_of_prime_order
    {Q : Type u} [Group Q] {r : ℕ}
    (hr : r.Prime) {x : Q} (hx : orderOf x = r) : x ≠ 1 := by
  intro hxOne
  apply hr.ne_one
  calc
    r = orderOf x := hx.symm
    _ = 1 := by rw [hxOne, orderOf_one]

private theorem eta10_modEq_one_on_right
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (y : W₁) (x : W₂)
    (hyOrder : orderOf y = ctx.q)
    (hxne : x ≠ 1) :
    ∃ eps : ℂ, IsPrimitiveRoot eps ctx.q ∧
      IsIntegralModEq (1 - eps) (ftTypePEta10 ctx (x : G)) 1 := by
  have hyne : y ≠ 1 := ne_one_of_prime_order (q_prime ctx) hyOrder
  letI : NeZero (ctx.q : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr (q_prime ctx).ne_zero⟩
  obtain ⟨eps, heps⟩ :=
    HasEnoughRootsOfUnity.exists_primitiveRoot ℂ ctx.q
  let source : IrreducibleCharacter W ℂ :=
    IrreducibleCharacter.cyclicTICharacter defW
      (ftTypePLeftIndex ctx) IrreducibleCharacter.trivial
  let w : W := defW.mulEquiv (y, x)
  have hw : w ∈ cyclicTISetInW W W₁ W₂ := by
    rw [mem_cyclicTISetInW, defW.mulEquiv_mem_left_iff,
      defW.mulEquiv_mem_right_iff]
    exact ⟨hxne, hyne⟩
  have hrestrict := ctx.isoG.restrict (source : ClassFunction W ℂ) hw
  have hetaW : ftTypePEta10 ctx (w : G) = source w := by
    change ctx.isoG.linearMap (source : ClassFunction W ℂ)
      (Subgroup.topEquiv.symm (w : G)) = source w
    convert hrestrict using 1
    apply congrArg (fun z : (⊤ : Subgroup G) =>
      ctx.isoG.linearMap (source : ClassFunction W ℂ) z)
    apply Subtype.ext
    rfl
  obtain ⟨zeta, hzeta⟩ := eta_isVirtual ctx
    (ftTypePLeftIndex ctx) IrreducibleCharacter.trivial
  have hyOrderG : orderOf (y : G) = ctx.q :=
    (Subgroup.orderOf_coe y).trans hyOrder
  have htarget := vchar_ker_mod_prim_of_isAlgClosed
    heps zeta (y : G) (x : G) hyOrderG (defW.commute y x)
  rw [hzeta] at htarget
  have htarget' : IsIntegralModEq (1 - eps)
      (source w) (ftTypePEta10 ctx (x : G)) := by
    rw [← hetaW]
    simpa only [ftTypePEta10, w, defW.coe_mulEquiv_apply] using htarget
  let leftW : W := defW.leftEmbedding y
  let rightW : W := defW.rightEmbedding x
  have hleftInjective : Function.Injective defW.leftEmbedding := by
    intro a b hab
    apply Subtype.ext
    simpa only [defW.coe_leftEmbedding_apply] using
      congrArg (fun z : W => (z : G)) hab
  have hleftOrder : orderOf leftW = ctx.q :=
    (orderOf_injective defW.leftEmbedding hleftInjective y).trans hyOrder
  have hcommW : Commute leftW rightW := by
    rw [commute_iff_eq]
    apply Subtype.ext
    exact (defW.commute y x).eq
  have hproductW : leftW * rightW = w := by
    apply Subtype.ext
    rfl
  have hsource := vchar_ker_mod_prim_of_isAlgClosed heps
    (Finsupp.single source 1 : VirtualCharacter W ℂ)
    leftW rightW hleftOrder hcommW
  letI : IsCyclic W₁ := ctx.primeTI.prime_cycTIhyp.left_cyclic
  have hleftDegree : ftTypePLeftIndex ctx 1 = 1 :=
    irreducible_degree_one_of_commutative (ftTypePLeftIndex ctx)
  have hsource' : IsIntegralModEq (1 - eps) (source w) 1 := by
    simpa only [VirtualCharacter.realize_single, Int.cast_one,
      one_smul, hproductW, rightW, source,
      IrreducibleCharacter.cyclicTICharacter_rightEmbedding,
      hleftDegree, IrreducibleCharacter.trivial_apply, one_mul]
      using hsource
  exact ⟨eps, heps, htarget'.symm.trans hsource'⟩

private theorem eta10_alpha_ne_zero
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (zeta1 : ClassFunction S ℂ) (a : ℤ)
    (alpha : ClassFunction ctx.H ℂ)
    (ha : a = 0)
    (hpointwise : ∀ x : ctx.H, x ≠ 1 →
      ftTypePEta10 ctx (x : G) =
        ((a : ℂ) / characterPairing zeta1 zeta1) *
            zeta1 ⟨(x : G), (fittingWithin_le S) x.property⟩ +
          alpha x) :
    alpha ≠ 0 := by
  obtain ⟨y, x, hyOrder, hxOrder⟩ := exists_factor_prime_elements ctx
  have hxne : x ≠ 1 := ne_one_of_prime_order (p_prime ctx) hxOrder
  let xP : ctx.P :=
    ⟨x, ctx.StypeP.2.2.2.1.2.2.1 x.property⟩
  let xH : ctx.H := ⟨x, Fcore_sub_Fitting S xP.property⟩
  have hxHne : xH ≠ 1 := by
    intro hxOne
    apply hxne
    apply Subtype.ext
    exact congrArg (fun z : ctx.H => (z : G)) hxOne
  intro halpha
  have hetaX := hpointwise xH hxHne
  have hetaXZero : ftTypePEta10 ctx (x : G) = 0 := by
    simpa only [ha, Int.cast_zero, zero_div, zero_mul, zero_add,
      halpha, ClassFunction.zero_apply] using hetaX
  obtain ⟨eps, heps, hmod⟩ :=
    eta10_modEq_one_on_right ctx y x hyOrder hxne
  rw [hetaXZero] at hmod
  have hmod' : IsIntegralModEq (1 - eps) ((1 : ℤ) : ℂ) 0 := by
    simpa only [Int.cast_one] using hmod.symm
  have honeDiv : (ctx.q : ℤ) ∣ 1 :=
    int_eqAmod_prime_prim_of_isAlgClosed heps (q_prime ctx) 1 hmod'
  have hqNeOne : (ctx.q : ℤ) ≠ 1 := by
    exact_mod_cast (q_prime ctx).ne_one
  exact hqNeOne
    (Int.eq_one_of_dvd_one (Int.ofNat_zero_le ctx.q) honeDiv)

private theorem q_dvd_alphaDegree
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (tau1 : ClassFunction S ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (lambda : ClassFunction S ℂ)
    (hcoh : coherent_with
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
      (nonidentitySet S) ctx.tau tau1)
    (hirr : lambda ∈ irr_Ind_Fitting S)
    (hcalS : lambda ∈ ftTypePCoreFamily S)
    (a : ℤ) (alpha : ClassFunction ctx.H ℂ)
    (alphaDegree : ℤ)
    (ha : a = 1)
    (halphaOne : alpha 1 = (alphaDegree : ℂ))
    (halphaOnP : ∀ x : ctx.P,
      alpha ⟨x, Fcore_sub_Fitting S x.property⟩ = alpha 1)
    (hpointwise : ∀ x : ctx.H, x ≠ 1 →
      tau1 lambda (x : G) =
        ((a : ℂ) / characterPairing lambda lambda) *
            lambda ⟨(x : G), (fittingWithin_le S) x.property⟩ +
          alpha x) :
    (ctx.q : ℤ) ∣ alphaDegree := by
  obtain ⟨y, x, hyOrder, hxOrder⟩ := exists_factor_prime_elements ctx
  have hyne : y ≠ 1 := ne_one_of_prime_order (q_prime ctx) hyOrder
  have hxne : x ≠ 1 := ne_one_of_prime_order (p_prime ctx) hxOrder
  let xP : ctx.P :=
    ⟨x, ctx.StypeP.2.2.2.1.2.2.1 x.property⟩
  let xH : ctx.H := ⟨x, Fcore_sub_Fitting S xP.property⟩
  let xS : S := ⟨x, Fcore_sub S xP.property⟩
  let yS : S := ⟨y, ctx.primeTI.complement_le_group y.property⟩
  let w : W := defW.mulEquiv (y, x)
  have hw : w ∈ cyclicTISetInW W W₁ W₂ := by
    rw [mem_cyclicTISetInW, defW.mulEquiv_mem_left_iff,
      defW.mulEquiv_mem_right_iff]
    exact ⟨hxne, hyne⟩
  have hxPU : (x : G) ∈ ctx.PU :=
    ctx.StypeP.2.1.2.2.2.1 xP.property
  have hwNotPU : (w : G) ∉ ctx.PU := by
    intro hwPU
    have hyEq : (y : G) = (w : G) * (x : G)⁻¹ := by
      dsimp only [w]
      rw [defW.coe_mulEquiv_apply]
      group
    have hyPU : (y : G) ∈ ctx.PU := by
      rw [hyEq]
      exact ctx.PU.mul_mem hwPU (ctx.PU.inv_mem hxPU)
    have hyBot : yS ∈ (⊥ : Subgroup S) :=
      ctx.StypeP.1.2.2.2.2.2.2.disjoint.le_bot
        ⟨hyPU, y.property⟩
    apply hyne
    apply Subtype.ext
    exact congrArg (fun z : S => (z : G))
      (Subgroup.mem_bot.mp hyBot)
  have hproductNotH : yS * xS ∉ HInS ctx := by
    intro hproductH
    apply hwNotPU
    have hproductPU : ((yS * xS : S) : G) ∈ ctx.PU :=
      ctx.StypeP.2.2.1.2.2.2 hproductH
    change (y : G) * (x : G) ∈ ctx.PU at hproductPU
    simpa only [w, defW.coe_mulEquiv_apply] using hproductPU
  have hlambdaOn : lambda ∈
      ClassFunction.supportedOn ((HInS ctx : Subgroup S) : Set S) :=
    seqInd_on (HInS ctx) hirr.2
  have hlambdaProduct : lambda (yS * xS) = 0 :=
    ClassFunction.eq_zero_of_mem_supportedOn hlambdaOn hproductNotH
  have htauW := coherent_image_vanish_on_cyclicTI
    ctx tau1 hcoh lambda hcalS hirr.1 hw
  have htauProduct : tau1 lambda ((y : G) * (x : G)) = 0 := by
    rw [← defW.coe_mulEquiv_apply (y, x)]
    exact htauW
  letI : NeZero (ctx.q : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr (q_prime ctx).ne_zero⟩
  obtain ⟨eps, heps⟩ :=
    HasEnoughRootsOfUnity.exists_primitiveRoot ℂ ctx.q
  obtain ⟨zTau, hzTau⟩ :=
    hcoh.mapsToVirtual lambda (AddSubgroup.subset_closure hcalS)
  have hyOrderG : orderOf (y : G) = ctx.q :=
    (Subgroup.orderOf_coe y).trans hyOrder
  have htauMod := vchar_ker_mod_prim_of_isAlgClosed
    heps zTau (y : G) (x : G) hyOrderG (defW.commute y x)
  rw [hzTau, htauProduct] at htauMod
  let lambdaIrr : IrreducibleCharacter S ℂ := ⟨lambda, hirr.1⟩
  let zLambda : VirtualCharacter S ℂ := Finsupp.single lambdaIrr 1
  have hyOrderS : orderOf yS = ctx.q :=
    (orderOf_injective S.subtype S.subtype_injective yS).symm.trans
      hyOrderG
  have hcommS : Commute yS xS := by
    rw [commute_iff_eq]
    apply Subtype.ext
    exact (defW.commute y x).eq
  have hlambdaMod := vchar_ker_mod_prim_of_isAlgClosed
    heps zLambda yS xS hyOrderS hcommS
  have hlambdaMod' : IsIntegralModEq (1 - eps) 0 (lambda xS) := by
    simpa only [zLambda, lambdaIrr,
      VirtualCharacter.realize_single, Int.cast_one, one_smul,
      hlambdaProduct] using hlambdaMod
  have htauLambda : IsIntegralModEq (1 - eps)
      (tau1 lambda (x : G)) (lambda xS) :=
    htauMod.symm.trans hlambdaMod'
  have hxHne : xH ≠ 1 := by
    intro hxOne
    apply hxne
    apply Subtype.ext
    exact congrArg (fun z : ctx.H => (z : G)) hxOne
  have hpoint := hpointwise xH hxHne
  change tau1 lambda (x : G) =
      ((a : ℂ) / characterPairing lambda lambda) * lambda xS +
        alpha xH at hpoint
  letI : Invertible (Nat.card S : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hlambdaNorm : characterPairing lambda lambda = 1 :=
    IrreducibleCharacter.characterPairing_self ⟨lambda, hirr.1⟩
  have halphaX : alpha xH = alpha 1 := by
    simpa only [xH, xP] using halphaOnP xP
  rw [ha, Int.cast_one, hlambdaNorm, div_one, one_mul,
    halphaX, halphaOne] at hpoint
  have hdifference :
      tau1 lambda (x : G) - lambda xS = (alphaDegree : ℂ) := by
    linear_combination hpoint
  have hdegreeMod :
      IsIntegralModEq (1 - eps) (alphaDegree : ℂ) 0 := by
    have hsub := htauLambda.sub
      (IsIntegralModEq.refl (1 - eps) (lambda xS))
    simpa only [hdifference, sub_self] using hsub
  exact int_eqAmod_prime_prim_of_isAlgClosed
    heps (q_prime ctx) alphaDegree hdegreeMod


private theorem mu_pairing_eta01_pivot
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (tau1 : ClassFunction S ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (b : Bool)
    (hrow : ∀ j : IrreducibleCharacter W₂ ℂ,
      j ≠ IrreducibleCharacter.trivial →
        tau1 (ctx.mu j) =
          ftTypePBooleanSign b •
            ∑ i : IrreducibleCharacter W₁ ℂ,
              ctx.eta i (ftTypePSignIndex b j)) :
    characterPairing
      (tau1 (ctx.mu
        (ftTypePSignIndex b (ftTypePRightIndex ctx))))
      (ftTypePEta01 ctx) = ftTypePBooleanSign b := by
  have hpivotNe :
      ftTypePSignIndex b (ftTypePRightIndex ctx) ≠
        IrreducibleCharacter.trivial :=
    signIndex_ne_trivial b (ftTypePRightIndex ctx)
      (FTTypePBoundsInfrastructureInternal.rightIndex_ne_trivial ctx)
  rw [hrow _ hpivotNe, characterPairing_smul_left,
    pairing_fintype_sum_left, signIndex_involutive]
  have hsum :
      (∑ i : IrreducibleCharacter W₁ ℂ,
        characterPairing
          (ctx.eta i (ftTypePRightIndex ctx))
          (ftTypePEta01 ctx)) = 1 := by
    rw [Finset.sum_eq_single IrreducibleCharacter.trivial]
    · rw [ftTypePEta01,
        FTTypePCyclicRectangleInternal.characterPairing_eta,
        if_pos rfl]
    · intro i _ hne
      rw [ftTypePEta01,
        FTTypePCyclicRectangleInternal.characterPairing_eta, if_neg]
      intro hpairs
      exact hne (congrArg Prod.fst hpairs)
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  rw [hsum, mul_one]

private theorem mu_pairing_eta01_eq_zero_of_ne
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (tau1 : ClassFunction S ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (b : Bool) (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial)
    (hjne : j ≠ ftTypePSignIndex b (ftTypePRightIndex ctx))
    (hrow : tau1 (ctx.mu j) =
      ftTypePBooleanSign b •
        ∑ i : IrreducibleCharacter W₁ ℂ,
          ctx.eta i (ftTypePSignIndex b j)) :
    characterPairing (tau1 (ctx.mu j)) (ftTypePEta01 ctx) = 0 := by
  have hcolumn : ftTypePSignIndex b j ≠ ftTypePRightIndex ctx := by
    intro hcolumn
    apply hjne
    calc
      j = ftTypePSignIndex b (ftTypePSignIndex b j) :=
        (signIndex_involutive b j).symm
      _ = ftTypePSignIndex b (ftTypePRightIndex ctx) :=
        congrArg (ftTypePSignIndex b) hcolumn
  rw [hrow, characterPairing_smul_left, pairing_fintype_sum_left]
  have hsum :
      (∑ i : IrreducibleCharacter W₁ ℂ,
        characterPairing (ctx.eta i (ftTypePSignIndex b j))
          (ftTypePEta01 ctx)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [ftTypePEta01,
      FTTypePCyclicRectangleInternal.characterPairing_eta, if_neg]
    intro hpairs
    exact hcolumn (congrArg Prod.snd hpairs)
  rw [hsum, mul_zero]

/-! ## Case adapters consumed by the three final bounds -/

private theorem fittingCore_pairing_eta10_of_case
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (tau1 : ClassFunction S ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (hcoh : coherent_with
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
      (nonidentitySet S) ctx.tau tau1)
    (b : Bool)
    (hrows : ∀ j : IrreducibleCharacter W₂ ℂ,
      j ≠ IrreducibleCharacter.trivial →
        tau1 (ctx.mu j) = ftTypePBooleanSign b •
          ∑ i : IrreducibleCharacter W₁ ℂ,
            ctx.eta i (ftTypePSignIndex b j))
    (zeta : ClassFunction S ℂ)
    (hcase :
      (∃ j : IrreducibleCharacter W₂ ℂ,
        j ≠ IrreducibleCharacter.trivial ∧ zeta = ctx.mu j) ∨
      zeta ∈ AddSubgroup.closure
        {phi : ClassFunction S ℂ |
          phi ∈ ftTypePCoreFamily S ∧
            IsIrreducibleCharacter S ℂ phi}) :
    characterPairing (tau1 zeta) (ftTypePEta10 ctx) = 0 := by
  rcases hcase with ⟨j, hj, rfl⟩ | hclosure
  · exact mu_pairing_eta10_eq_zero ctx tau1 b j hj (hrows j hj)
  · simpa only [ftTypePEta10] using
      coreIrrClosure_pairing_eta_eq_zero ctx tau1 hcoh zeta hclosure
        (ftTypePLeftIndex ctx) IrreducibleCharacter.trivial

private theorem fittingCore_pairing_eta01_of_case
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (tau1 : ClassFunction S ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (hcoh : coherent_with
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
      (nonidentitySet S) ctx.tau tau1)
    (b : Bool)
    (hrows : ∀ j : IrreducibleCharacter W₂ ℂ,
      j ≠ IrreducibleCharacter.trivial →
        tau1 (ctx.mu j) = ftTypePBooleanSign b •
          ∑ i : IrreducibleCharacter W₁ ℂ,
            ctx.eta i (ftTypePSignIndex b j))
    (zeta : ClassFunction S ℂ)
    (hne : zeta ≠
      ctx.mu (ftTypePSignIndex b (ftTypePRightIndex ctx)))
    (hcase :
      (∃ j : IrreducibleCharacter W₂ ℂ,
        j ≠ IrreducibleCharacter.trivial ∧ zeta = ctx.mu j) ∨
      zeta ∈ AddSubgroup.closure
        {phi : ClassFunction S ℂ |
          phi ∈ ftTypePCoreFamily S ∧
            IsIrreducibleCharacter S ℂ phi}) :
    characterPairing (tau1 zeta) (ftTypePEta01 ctx) = 0 := by
  rcases hcase with ⟨j, hj, rfl⟩ | hclosure
  · have hjne : j ≠ ftTypePSignIndex b (ftTypePRightIndex ctx) := by
      intro hjEq
      apply hne
      rw [hjEq]
    exact mu_pairing_eta01_eq_zero_of_ne
      ctx tau1 b j hj hjne (hrows j hj)
  · simpa only [ftTypePEta01] using
      coreIrrClosure_pairing_eta_eq_zero ctx tau1 hcoh zeta hclosure
        IrreducibleCharacter.trivial (ftTypePRightIndex ctx)

private theorem eta10_mass_lower
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (zeta1 : ClassFunction S ℂ) (a : ℤ)
    (alpha : ClassFunction ctx.H ℂ)
    (alphaDegree : ℤ) (alphaNorm : ℕ)
    (ha : a = 0)
    (halphaOne : alpha 1 = (alphaDegree : ℂ))
    (halphaWitness : ∃ z : VirtualCharacter ctx.H ℂ,
      VirtualCharacter.realize z = alpha ∧
        normSq z = (alphaNorm : ℤ))
    (hpointwise : ∀ x : ctx.H, x ≠ 1 →
      ftTypePEta10 ctx (x : G) =
        ((a : ℂ) / characterPairing zeta1 zeta1) *
            zeta1 ⟨(x : G), (fittingWithin_le S) x.property⟩ +
          alpha x)
    (hmass : ftTypePSumNormSq (subgroupNonidentity ctx.H)
        (ftTypePEta10 ctx) =
      (a : ℝ) ^ 2 * (classFunctionNormSq zeta1)⁻¹ *
          ((Nat.card S : ℝ) - Complex.normSq (zeta1 1) *
            (classFunctionNormSq zeta1)⁻¹) -
        2 * (a : ℝ) *
          ((zeta1 1).re * (alphaDegree : ℝ) *
            (classFunctionNormSq zeta1)⁻¹) +
        ftTypePSumNormSq (nonidentitySet ctx.H) alpha)
    (hresidual :
      ((Nat.card ctx.P - 1 : ℕ) : ℝ) *
          (alphaDegree : ℝ) ^ 2 ≤
        ftTypePSumNormSq (nonidentitySet ctx.H) alpha) :
    (ftTypePSetCard (subgroupNonidentity ctx.H) : ℝ) ≤
      ftTypePSumNormSq (subgroupNonidentity ctx.H)
        (ftTypePEta10 ctx) := by
  have halphaNe := eta10_alpha_ne_zero
    ctx zeta1 a alpha ha hpointwise
  have halphaMass := virtual_mass_ge_card_sub_one
    ctx alpha alphaDegree alphaNorm halphaOne halphaWitness
      halphaNe hresidual
  have hmassAlpha :
      ftTypePSumNormSq (subgroupNonidentity ctx.H)
          (ftTypePEta10 ctx) =
        ftTypePSumNormSq (nonidentitySet ctx.H) alpha := by
    rw [ha] at hmass
    norm_num at hmass
    exact hmass
  simpa only [ftTypePSetCard, setCard_subgroupNonidentity,
    hmassAlpha] using halphaMass

/-! ## Restriction to the Fitting subgroup -/

private noncomputable def residualFittingRestriction
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ClassFunction S ℂ →ₗ[ℂ] ClassFunction ctx.H ℂ :=
  ClassFunction.comap (Subgroup.inclusion (fittingWithin_le S))

@[simp] private theorem residualFittingRestriction_apply
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (phi : ClassFunction S ℂ) (x : ctx.H) :
    residualFittingRestriction ctx phi x =
      phi ⟨(x : G), (fittingWithin_le S) x.property⟩ :=
  rfl

private theorem residualFittingInS_map
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    (HInS ctx).map S.subtype = ctx.H := by
  simpa only [HInS] using
    Subgroup.map_subgroupOf_eq_of_le (fittingWithin_le S)

private theorem residualFittingInS_commutative
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    IsMulCommutative (HInS ctx) := by
  letI : IsMulCommutative ctx.H := FTtypeP_Fitting_abelian ctx
  rw [isMulCommutative_iff]
  intro x y
  let e : HInS ctx ≃* ctx.H :=
    Subgroup.subgroupOfEquivOfLe (fittingWithin_le S)
  exact e.injective (mul_comm (e x) (e y))

private theorem residual_seqInd_degree
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    {xi : ClassFunction S ℂ}
    (hxi : xi ∈ seqIndT (k := ℂ) (HInS ctx)) :
    xi 1 = ((HInS ctx).index : ℂ) := by
  letI : IsMulCommutative (HInS ctx) :=
    residualFittingInS_commutative ctx
  obtain ⟨theta, _htheta, rfl⟩ := seqIndP.mp hxi
  rw [ClassFunction.induce_one,
    irreducible_degree_one_of_commutative theta, mul_one]

private theorem residual_sourceMap_targetMap
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (phi : ClassFunction (⊤ : Subgroup G) ℂ) :
    sourceMap (ctx.targetMap phi) = phi := by
  ext x
  simpa [sourceMap, ClassFunction.comap_apply] using
    congrArg phi (Subgroup.topEquiv.symm_apply_apply x)

/-! ## Moving coherence to the normalized-TI Dade map -/

private theorem residual_fittingDade_coherent
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (tau1 : ClassFunction S ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (hcoh : coherent_with
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
      (nonidentitySet S) ctx.tau tau1)
    (hcore :
      (↑(calS1 ctx) : Set (ClassFunction S ℂ)) ⊆
        AddSubgroup.closure
          (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))) :
    coherent_with
      (↑(calS1 ctx) : Set (ClassFunction S ℂ))
      (nonidentitySet S) (Dade (fittingSharpDade ctx))
      (sourceMap.comp tau1) := by
  have hclosure :
      AddSubgroup.closure
          (↑(calS1 ctx) : Set (ClassFunction S ℂ)) ≤
        AddSubgroup.closure
          (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ)) :=
    (AddSubgroup.closure_le _).2 hcore
  refine
    { isometry := ?_
      mapsToVirtual := ?_
      agrees := ?_ }
  · intro phi hphi psi hpsi
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
      sourceMap_pairing ctx]
    exact hcoh.isometry phi (hclosure hphi) psi (hclosure hpsi)
  · intro phi hphi
    exact sourceMap_virtual (hcoh.mapsToVirtual phi (hclosure hphi))
  · intro phi hphi hsupp
    have htau1 : tau1 phi = ctx.tau phi :=
      hcoh.agrees phi (hclosure hphi) hsupp
    have hDade :
        ctx.targetMap (Dade (fittingSharpDade ctx) phi) = ctx.tau phi :=
      targetMap_fittingDade_eq_tau ctx hphi hsupp
    calc
      (sourceMap.comp tau1) phi = sourceMap (ctx.tau phi) := by
        rw [LinearMap.comp_apply, htau1]
      _ = sourceMap
          (ctx.targetMap (Dade (fittingSharpDade ctx) phi)) := by rw [hDade]
      _ = Dade (fittingSharpDade ctx) phi :=
        residual_sourceMap_targetMap ctx _

private theorem residual_adjusted_agrees
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    {J L : Subgroup Gamma} (H : Subgroup L) [H.Normal]
    (K M : Subgroup H)
    (ddA : DadeHypothesis J L
      (subgroupNonidentity (H.map L.subtype)))
    (nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction J ℂ)
    (hcoh : coherent_with
      (↑(seqIndD (k := ℂ) H K M) : Set (ClassFunction L ℂ))
      (nonidentitySet L) (Dade ddA) nu)
    {xi0 xi : ClassFunction L ℂ}
    (hxi0 : xi0 ∈ seqIndD (k := ℂ) H K M)
    (hxi : xi ∈ seqIndD (k := ℂ) H K M) :
    Dade ddA (invDadeSeqIndAdjusted xi0 xi) =
      nu (invDadeSeqIndAdjusted xi0 xi) := by
  let weighted : ClassFunction L ℂ :=
    (xi0 1) • xi - (xi 1) • xi0
  have hweighted : weighted ∈ AddSubgroup.closure
      (↑(seqIndD (k := ℂ) H K M) : Set (ClassFunction L ℂ)) := by
    obtain ⟨m, hm⟩ := Cnat_seqInd1 H hxi0
    obtain ⟨n, hn⟩ := Cnat_seqInd1 H hxi
    unfold weighted
    rw [hm, hn]
    have hmxi :=
      (AddSubgroup.closure
          (↑(seqIndD (k := ℂ) H K M) : Set (ClassFunction L ℂ))).nsmul_mem
        (AddSubgroup.subset_closure hxi) m
    have hnxi0 :=
      (AddSubgroup.closure
          (↑(seqIndD (k := ℂ) H K M) : Set (ClassFunction L ℂ))).nsmul_mem
        (AddSubgroup.subset_closure hxi0) n
    rw [← Nat.cast_smul_eq_nsmul (R := ℂ) m xi] at hmxi
    rw [← Nat.cast_smul_eq_nsmul (R := ℂ) n xi0] at hnxi0
    exact (AddSubgroup.closure
      (↑(seqIndD (k := ℂ) H K M) : Set (ClassFunction L ℂ))).sub_mem
        hmxi hnxi0
  have hweightedSupport :
      weighted ∈ ClassFunction.supportedOn (nonidentitySet L) := by
    have hsupp := sub_seqInd_on H hxi hxi0
    rw [ClassFunction.mem_supportedOn_iff] at hsupp ⊢
    intro x hx
    apply hsupp
    intro hxH
    apply hx
    simpa [nonidentitySet] using hxH.2
  have hagree := hcoh.agrees weighted hweighted hweightedSupport
  have hdegree : xi0 1 ≠ 0 :=
    seqInd1_neq0 H
      (FTTypePBoundsInfrastructureInternal.seqIndD_mem_seqIndT
        H K M hxi0)
  have hadjusted :
      invDadeSeqIndAdjusted xi0 xi = (xi0 1)⁻¹ • weighted := by
    unfold invDadeSeqIndAdjusted weighted
    apply ClassFunction.ext
    intro x
    simp only [ClassFunction.sub_apply, ClassFunction.smul_apply,
      smul_eq_mul]
    field_simp [hdegree]
  rw [hadjusted, map_smul, map_smul, hagree]

private theorem residual_starPairing_sub_left
    {Q : Type u} [Group Q] [Fintype Q]
    (phi psi theta : ClassFunction Q ℂ) :
    starCharacterPairing (phi - psi) theta =
      starCharacterPairing phi theta - starCharacterPairing psi theta := by
  simp [sub_eq_add_neg, starCharacterPairing, twistedCharacterPairing,
    add_mul, Finset.sum_add_distrib]
  ring

private theorem residual_coherentCoefficient_virtual
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    {J L : Subgroup Gamma} (H : Subgroup L) [H.Normal]
    (K M : Subgroup H)
    (ddA : DadeHypothesis J L
      (subgroupNonidentity (H.map L.subtype)))
    (nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction J ℂ)
    (hcoh : coherent_with
      (↑(seqIndD (k := ℂ) H K M) : Set (ClassFunction L ℂ))
      (nonidentitySet L) (Dade ddA) nu)
    {xi0 xi : ClassFunction L ℂ}
    (hxi0 : xi0 ∈ seqIndD (k := ℂ) H K M)
    (hxi : xi ∈ seqIndD (k := ℂ) H K M)
    (chi : ClassFunction J ℂ)
    (hchi : ClassFunction.IsVirtual chi)
    (horth : characterPairing (nu xi0) chi = 0) :
    invDadeSeqIndCoefficient ddA xi0 chi xi =
      characterPairing (nu xi) chi := by
  have hnuXi := hcoh.mapsToVirtual xi (AddSubgroup.subset_closure hxi)
  have hnuXi0 := hcoh.mapsToVirtual xi0 (AddSubgroup.subset_closure hxi0)
  unfold invDadeSeqIndCoefficient
  rw [residual_adjusted_agrees H K M ddA nu hcoh hxi0 hxi]
  unfold invDadeSeqIndAdjusted
  rw [map_sub, map_smul, residual_starPairing_sub_left,
    starCharacterPairing_smul_left,
    PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
      hnuXi hchi,
    PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
      hnuXi0 hchi,
    horth, mul_zero, sub_zero]

private theorem residual_fittingCoefficient_virtual
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (ddH : DadeHypothesis (⊤ : Subgroup G) S
      (subgroupNonidentity ((HInS ctx).map S.subtype)))
    (tau1 : ClassFunction S ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (hcoh : coherent_with
      (↑(calS1 ctx) : Set (ClassFunction S ℂ))
      (nonidentitySet S) (Dade ddH) (sourceMap.comp tau1))
    (zeta0 xi : ClassFunction S ℂ)
    (hzeta0 : zeta0 ∈ calS1 ctx)
    (hxi : xi ∈ calS1 ctx)
    (chi : ClassFunction G ℂ)
    (hchi : ClassFunction.IsVirtual chi)
    (horth : characterPairing (tau1 zeta0) chi = 0) :
    invDadeSeqIndCoefficient ddH zeta0 (sourceMap chi) xi =
      characterPairing (tau1 xi) chi := by
  have horthTop :
      characterPairing ((sourceMap.comp tau1) zeta0) (sourceMap chi) = 0 := by
    rw [LinearMap.comp_apply, sourceMap_pairing ctx]
    exact horth
  have hcoeff := residual_coherentCoefficient_virtual
    (HInS ctx) (PInH ctx) ⊥ ddH (sourceMap.comp tau1) hcoh
      hzeta0 hxi (sourceMap chi) (sourceMap_virtual hchi) horthTop
  rwa [LinearMap.comp_apply, sourceMap_pairing ctx] at hcoeff

/-! ## Virtuality of the residual tail -/

private theorem residual_virtual_starPairing_integer
    {Q : Type u} [Group Q] [Fintype Q]
    {phi psi : ClassFunction Q ℂ}
    (hphi : ClassFunction.IsVirtual phi)
    (hpsi : ClassFunction.IsVirtual psi) :
    ∃ n : ℤ, starCharacterPairing phi psi = (n : ℂ) := by
  obtain ⟨n, hn⟩ :=
    PTypeCorePairingInternal.pTypeCore_virtual_pairing_isInt hphi hpsi
  exact ⟨n,
    (PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
      hphi hpsi).trans hn⟩

private theorem residual_adjustedDade_isVirtual
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (ddH : DadeHypothesis (⊤ : Subgroup G) S
      (subgroupNonidentity ((HInS ctx).map S.subtype)))
    (zeta0 xi : ClassFunction S ℂ)
    (hzeta0 : zeta0 ∈ seqIndT (k := ℂ) (HInS ctx))
    (hxi : xi ∈ seqIndT (k := ℂ) (HInS ctx)) :
    ClassFunction.IsVirtual
      (Dade ddH (invDadeSeqIndAdjusted zeta0 xi)) := by
  obtain ⟨v0, hv0⟩ := seqInd_vcharW (HInS ctx) hzeta0
  obtain ⟨v, hv⟩ := seqInd_vcharW (HInS ctx) hxi
  let delta : VirtualCharacter S ℂ := v - v0
  let weighted : ClassFunction S ℂ :=
    (zeta0 1) • xi - (xi 1) • zeta0
  have hdegree : zeta0 1 ≠ 0 := seqInd1_neq0 (HInS ctx) hzeta0
  have hadjusted :
      invDadeSeqIndAdjusted zeta0 xi = (zeta0 1)⁻¹ • weighted := by
    unfold invDadeSeqIndAdjusted weighted
    apply ClassFunction.ext
    intro x
    simp only [ClassFunction.sub_apply, ClassFunction.smul_apply,
      smul_eq_mul]
    field_simp [hdegree]
  have hrealize : VirtualCharacter.realize delta =
      invDadeSeqIndAdjusted zeta0 xi := by
    dsimp only [delta]
    rw [VirtualCharacter.realize_sub, hv, hv0]
    unfold invDadeSeqIndAdjusted
    rw [residual_seqInd_degree ctx hzeta0,
      residual_seqInd_degree ctx hxi, div_self]
    · simp
    · exact Nat.cast_ne_zero.mpr
        (HInS ctx).index_ne_zero_of_finite
  have hweightedSupported : weighted ∈
      ClassFunction.supportedOn
        {x : S |
          (x : G) ∈ subgroupNonidentity ((HInS ctx).map S.subtype)} := by
    have hsupp := sub_seqInd_on (HInS ctx) hxi hzeta0
    rw [ClassFunction.mem_supportedOn_iff] at hsupp ⊢
    intro x hx
    apply hsupp
    intro hxSharp
    apply hx
    exact ⟨⟨x, hxSharp.1, rfl⟩, by
      intro hxG
      apply hxSharp.2
      apply Subtype.ext
      exact hxG⟩
  have hsupported : VirtualCharacter.realize delta ∈
      ClassFunction.supportedOn
        {x : S |
          (x : G) ∈ subgroupNonidentity ((HInS ctx).map S.subtype)} := by
    rw [hrealize, hadjusted]
    exact (ClassFunction.supportedOn _).smul_mem _ hweightedSupported
  refine ⟨Dade_virtualCharacter ddH delta, ?_⟩
  rw [← Dade_vchar ddH delta hsupported, hrealize]

private theorem residual_tailCoefficient_integer
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (ddH : DadeHypothesis (⊤ : Subgroup G) S
      (subgroupNonidentity ((HInS ctx).map S.subtype)))
    (zeta0 xi : ClassFunction S ℂ)
    (hzeta0 : zeta0 ∈ seqIndT (k := ℂ) (HInS ctx))
    (hxi : xi ∈ seqIndT (k := ℂ) (HInS ctx))
    (chi : ClassFunction G ℂ)
    (hchi : ClassFunction.IsVirtual chi) :
    ∃ n : ℤ,
      star (invDadeSeqIndCoefficient ddH zeta0 (sourceMap chi) xi) =
        (n : ℂ) := by
  obtain ⟨n, hn⟩ := residual_virtual_starPairing_integer
    (residual_adjustedDade_isVirtual ctx ddH zeta0 xi hzeta0 hxi)
    (sourceMap_virtual hchi)
  refine ⟨n, ?_⟩
  unfold invDadeSeqIndCoefficient
  rw [hn]
  simp

private theorem residual_virtual_zero
    {Q : Type u} [Group Q] :
    ClassFunction.IsVirtual (0 : ClassFunction Q ℂ) :=
  ⟨0, by simp⟩

private theorem residual_virtual_add
    {Q : Type u} [Group Q] {phi psi : ClassFunction Q ℂ}
    (hphi : ClassFunction.IsVirtual phi)
    (hpsi : ClassFunction.IsVirtual psi) :
    ClassFunction.IsVirtual (phi + psi) := by
  obtain ⟨v, rfl⟩ := hphi
  obtain ⟨w, rfl⟩ := hpsi
  exact ⟨v + w, VirtualCharacter.realize_add v w⟩

private theorem residual_virtual_int_smul
    {Q : Type u} [Group Q] (n : ℤ) {phi : ClassFunction Q ℂ}
    (hphi : ClassFunction.IsVirtual phi) :
    ClassFunction.IsVirtual ((n : ℂ) • phi) := by
  obtain ⟨v, rfl⟩ := hphi
  refine ⟨n • v, ?_⟩
  rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ]

private theorem residual_virtual_finset_sum
    {Q I : Type u} [Group Q] [DecidableEq I]
    (T : Finset I) (phi : I → ClassFunction Q ℂ)
    (hphi : ∀ i ∈ T, ClassFunction.IsVirtual (phi i)) :
    ClassFunction.IsVirtual (∑ i ∈ T, phi i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using (residual_virtual_zero (Q := Q))
  | @insert i T hi ih =>
      rw [Finset.sum_insert hi]
      exact residual_virtual_add
        (hphi i (Finset.mem_insert_self i T))
        (ih (fun j hj ↦ hphi j (Finset.mem_insert_of_mem hj)))

private theorem residualFittingRestriction_isVirtual
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    {phi : ClassFunction S ℂ}
    (hphi : ClassFunction.IsVirtual phi) :
    ClassFunction.IsVirtual (residualFittingRestriction ctx phi) := by
  obtain ⟨v, hv⟩ := hphi
  refine ⟨VirtualCharacter.comap
    (Subgroup.inclusion (fittingWithin_le S)) v, ?_⟩
  rw [VirtualCharacter.realize_comap, hv]
  rfl

private noncomputable def residualOrbitIrreducible
    {Q : Type u} [Group Q] [Fintype Q]
    (H : Subgroup Q) [H.Normal]
    (theta : IrreducibleCharacter H ℂ)
    (xi : ClassFunction.normalOrbit H
      (theta : ClassFunction H ℂ)) :
    IrreducibleCharacter H ℂ :=
  ⟨xi.1, by
    obtain ⟨x, hx⟩ := xi.2
    rw [← hx]
    exact ClassFunction.isIrreducibleCharacter_normalConjugate H x theta⟩

@[simp] private theorem residualOrbitIrreducible_coe
    {Q : Type u} [Group Q] [Fintype Q]
    (H : Subgroup Q) [H.Normal]
    (theta : IrreducibleCharacter H ℂ)
    (xi : ClassFunction.normalOrbit H
      (theta : ClassFunction H ℂ)) :
    ((residualOrbitIrreducible H theta xi :
        IrreducibleCharacter H ℂ) : ClassFunction H ℂ) = xi.1 :=
  rfl

private theorem residual_orbitSum_isVirtual
    {Q : Type u} [Group Q] [Fintype Q]
    (H : Subgroup Q) [H.Normal]
    (theta : IrreducibleCharacter H ℂ) :
    ClassFunction.IsVirtual
      (∑ xi : ClassFunction.normalOrbit H
          (theta : ClassFunction H ℂ),
        (xi : ClassFunction H ℂ)) := by
  let z : VirtualCharacter H ℂ :=
    ∑ xi : ClassFunction.normalOrbit H
        (theta : ClassFunction H ℂ),
      Finsupp.single (residualOrbitIrreducible H theta xi) 1
  refine ⟨z, ?_⟩
  unfold z
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro xi _
  simp only [VirtualCharacter.realize_single, Int.cast_one, one_smul,
    residualOrbitIrreducible_coe]

private theorem residual_normalizedTailTerm_isVirtual
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (xi : ClassFunction S ℂ)
    (hxi : xi ∈ seqIndT (k := ℂ) (HInS ctx))
    (c : ℂ) (n : ℤ) (hc : star c = (n : ℂ)) :
    ClassFunction.IsVirtual
      (residualFittingRestriction ctx
        ((star c / starCharacterPairing xi xi) • xi)) := by
  let H : Subgroup S := HInS ctx
  letI : Invertible (Nat.card H : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨theta, _htheta, hxiEq⟩ := seqIndP.mp hxi
  let orbitSum : ClassFunction H ℂ :=
    ∑ omega : ClassFunction.normalOrbit H
        (theta : ClassFunction H ℂ),
      (omega : ClassFunction H ℂ)
  let e : H ≃* ctx.H :=
    Subgroup.subgroupOfEquivOfLe (fittingWithin_le S)
  let orbitSumH : ClassFunction ctx.H ℂ :=
    ClassFunction.comap e.symm.toMonoidHom orbitSum
  have horbit : ClassFunction.IsVirtual orbitSum :=
    residual_orbitSum_isVirtual H theta
  have horbitH : ClassFunction.IsVirtual orbitSumH := by
    obtain ⟨v, hv⟩ := horbit
    refine ⟨VirtualCharacter.comap e.symm.toMonoidHom v, ?_⟩
    rw [VirtualCharacter.realize_comap, hv]
  have hrestrict :
      ClassFunction.restrict H
          (ClassFunction.induce H (theta : ClassFunction H ℂ)) =
        (ClassFunction.inertiaIndex H
            (theta : ClassFunction H ℂ) : ℂ) • orbitSum := by
    simpa only [orbitSum] using
      ClassFunction.cfResInd_sum_cfclass H
        (theta : ClassFunction H ℂ)
  have hindVirtual : ClassFunction.IsVirtual
      (ClassFunction.induce H (theta : ClassFunction H ℂ)) := by
    obtain ⟨v, hv⟩ := seqInd_vcharW H hxi
    exact ⟨v, hv.trans hxiEq⟩
  have hstarNorm :
      starCharacterPairing
          (ClassFunction.induce H (theta : ClassFunction H ℂ))
          (ClassFunction.induce H (theta : ClassFunction H ℂ)) =
        (ClassFunction.inertiaIndex H
          (theta : ClassFunction H ℂ) : ℂ) := by
    rw [PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
      hindVirtual hindVirtual]
    exact ClassFunction.cfnorm_Ind_irr H theta
  have hindex :
      (ClassFunction.inertiaIndex H
        (theta : ClassFunction H ℂ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr
      (ClassFunction.inertiaIndex_pos H
        (theta : ClassFunction H ℂ)).ne'
  have hterm :
      residualFittingRestriction ctx
          ((star c /
              starCharacterPairing
                (ClassFunction.induce H (theta : ClassFunction H ℂ))
                (ClassFunction.induce H (theta : ClassFunction H ℂ))) •
            ClassFunction.induce H (theta : ClassFunction H ℂ)) =
        (n : ℂ) • orbitSumH := by
    apply ClassFunction.ext
    intro x
    let xH : H := e.symm x
    have hx := congrArg (fun f : ClassFunction H ℂ ↦ f xH) hrestrict
    change ClassFunction.induce H (theta : ClassFunction H ℂ)
        ⟨(x : G), (fittingWithin_le S) x.property⟩ =
      (ClassFunction.inertiaIndex H
          (theta : ClassFunction H ℂ) : ℂ) * orbitSum xH at hx
    simp only [residualFittingRestriction_apply,
      ClassFunction.smul_apply, smul_eq_mul, orbitSumH,
      ClassFunction.comap_apply]
    rw [hc, hstarNorm, hx]
    field_simp [hindex]
    rfl
  rw [hxiEq, hterm]
  exact residual_virtual_int_smul n horbitH

/-! ## The residual has the core in its translation kernel -/

private theorem residual_tail_translationKernel
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (xi : ClassFunction S ℂ)
    (hxi : xi ∈ seqIndT (k := ℂ) (HInS ctx))
    (hout : xi ∉ calS1 ctx) :
    ctx.P.subgroupOf S ≤ ClassFunction.translationKernel xi := by
  let H : Subgroup S := HInS ctx
  let P : Subgroup S := ctx.P.subgroupOf S
  let PH : Subgroup H := P.subgroupOf H
  letI : P.Normal := by
    change (ctx.P.subgroupOf S).Normal
    simpa only [P, FTTypePSetupContext.P] using (Fcore_normal S)
  obtain ⟨theta, _htheta, hxiEq⟩ := seqIndP.mp hxi
  have hPH : P ≤ H :=
    Subgroup.subgroupOf_mono S (Fcore_sub_Fitting S)
  have htheta : PH ≤
      ClassFunction.translationKernel
        (theta : ClassFunction H ℂ) := by
    by_contra hnot
    apply hout
    change xi ∈ seqIndD (k := ℂ) H PH ⊥
    exact seqIndP.mpr
      ⟨theta, mem_Iirr_kerD.mpr ⟨bot_le, hnot⟩, hxiEq⟩
  rw [hxiEq]
  exact ClassFunction.le_translationKernel_induce
    P H hPH (theta : ClassFunction H ℂ) htheta

private theorem residual_tail_constant_on_P
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (xi : ClassFunction S ℂ)
    (hxi : xi ∈ seqIndT (k := ℂ) (HInS ctx))
    (hout : xi ∉ calS1 ctx)
    (b : ℂ) (x : ctx.P) :
    residualFittingRestriction ctx (b • xi)
        ⟨x, Fcore_sub_Fitting S x.property⟩ =
      residualFittingRestriction ctx (b • xi) 1 := by
  let xS : S := ⟨x, Fcore_sub S x.property⟩
  have hxKernel : xS ∈ ClassFunction.translationKernel xi :=
    residual_tail_translationKernel ctx xi hxi hout x.property
  have hxValue :=
    (ClassFunction.mem_translationKernel_iff xi xS).mp hxKernel (1 : S)
  simp only [residualFittingRestriction_apply,
    ClassFunction.smul_apply, smul_eq_mul]
  have hxCast :
      (⟨((⟨x, Fcore_sub_Fitting S x.property⟩ : ctx.H) : G),
          (fittingWithin_le S)
            (⟨x, Fcore_sub_Fitting S x.property⟩ : ctx.H).property⟩ : S) =
        xS := rfl
  rw [hxCast]
  change b * xi xS = b * xi (1 : S)
  simpa only [mul_one] using congrArg (fun z : ℂ ↦ b * z) hxValue

/-! ## Restriction pairings and square masses -/

private theorem residualFittingRestriction_pairing
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (phi psi : ClassFunction S ℂ)
    (hphi : phi ∈
      ClassFunction.supportedOn ((HInS ctx : Subgroup S) : Set S)) :
    characterPairing (residualFittingRestriction ctx phi)
        (residualFittingRestriction ctx psi) =
      ((HInS ctx).index : ℂ) * characterPairing phi psi := by
  let H : Subgroup S := HInS ctx
  let e : H ≃* ctx.H :=
    Subgroup.subgroupOfEquivOfLe (fittingWithin_le S)
  have hcardH : Nat.card H = Nat.card ctx.H :=
    Nat.card_congr e.toEquiv
  have hindexCard : H.index * Nat.card H = Nat.card S :=
    H.index_mul_card
  have hsumS :
      (∑ x : S, phi x * psi x⁻¹) =
        ∑ x : H, phi (x : S) * psi ((x⁻¹ : H) : S) := by
    let t : Finset S := Finset.univ.filter fun x : S ↦ x ∈ H
    have hunivH :
        (Finset.univ : Finset H) =
          (Finset.univ : Finset S).subtype (fun x ↦ x ∈ H) := by
      ext x
      simp
    have hvanish : ∀ x ∈ (Finset.univ : Finset S), x ∉ t →
        phi x * psi x⁻¹ = 0 := by
      intro x _ hx
      have hxH : x ∉ H := by
        simpa only [t, Finset.mem_filter, Finset.mem_univ,
          true_and] using hx
      rw [ClassFunction.eq_zero_of_mem_supportedOn hphi hxH, zero_mul]
    calc
      (∑ x : S, phi x * psi x⁻¹) =
          ∑ x ∈ t, phi x * psi x⁻¹ := by
        symm
        exact Finset.sum_subset (Finset.subset_univ _) hvanish
      _ = ∑ x : H, phi (x : S) * psi ((x⁻¹ : H) : S) := by
        rw [show (∑ x : H, phi (x : S) * psi ((x⁻¹ : H) : S)) =
            Finset.sum
              ((Finset.univ : Finset S).subtype (fun x ↦ x ∈ H))
              (fun x ↦ phi (x : S) * psi ((x⁻¹ : H) : S)) by
          rw [← hunivH]]
        simpa only [t, Subgroup.coe_inv] using
          (Finset.sum_subtype_eq_sum_filter
            (p := fun x : S ↦ x ∈ H)
            (s := (Finset.univ : Finset S))
            (fun x : S ↦ phi x * psi x⁻¹)).symm
  have hsumH :
      (∑ x : ctx.H,
          residualFittingRestriction ctx phi x *
            residualFittingRestriction ctx psi x⁻¹) =
        ∑ x : H, phi (x : S) * psi ((x⁻¹ : H) : S) := by
    symm
    apply Fintype.sum_equiv e.toEquiv
    intro x
    rfl
  unfold characterPairing
  rw [← hcardH, hsumH, ← hsumS]
  have hH0 : (Nat.card H : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hS0 : (Nat.card S : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hcast :
      (H.index : ℂ) * (Nat.card H : ℂ) = (Nat.card S : ℂ) := by
    exact_mod_cast hindexCard
  field_simp [hH0, hS0]
  rw [← hcast]
  ring

private theorem residual_starPairing_eq_pairing
    {Q : Type u} [Group Q] [Fintype Q]
    {phi psi : ClassFunction Q ℂ}
    (hphi : ClassFunction.IsVirtual phi)
    (hpsi : ClassFunction.IsVirtual psi) :
    starCharacterPairing phi psi = characterPairing phi psi :=
  PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
    hphi hpsi

private theorem residual_normSq_add_of_orthogonal
    {Q : Type u} [Group Q] [Fintype Q]
    (phi psi : ClassFunction Q ℂ)
    (horth : starCharacterPairing phi psi = 0) :
    classFunctionNormSq (phi + psi) =
      classFunctionNormSq phi + classFunctionNormSq psi := by
  have horth' : starCharacterPairing psi phi = 0 := by
    calc
      starCharacterPairing psi phi =
          star (starCharacterPairing phi psi) :=
        starCharacterPairing_conj_symm psi phi
      _ = 0 := by rw [horth]; simp
  rw [classFunctionNormSq_eq_re_starCharacterPairing,
    classFunctionNormSq_eq_re_starCharacterPairing,
    classFunctionNormSq_eq_re_starCharacterPairing,
    starCharacterPairing_add_left,
    starCharacterPairing_add_right,
    starCharacterPairing_add_right, horth, horth']
  simp

private theorem residual_normSq_smul
    {Q : Type u} [Group Q] [Fintype Q]
    (a : ℂ) (phi : ClassFunction Q ℂ) :
    classFunctionNormSq (a • phi) =
      Complex.normSq a * classFunctionNormSq phi := by
  unfold classFunctionNormSq
  simp only [ClassFunction.smul_apply, smul_eq_mul,
    Complex.normSq_mul, Finset.mul_sum]
  ring

private theorem residual_pairing_self_eq_normSq
    {Q : Type u} [Group Q] [Fintype Q]
    {phi : ClassFunction Q ℂ}
    (hphi : ClassFunction.IsVirtual phi) :
    characterPairing phi phi = (classFunctionNormSq phi : ℂ) := by
  rw [← residual_starPairing_eq_pairing hphi hphi]
  exact starCharacterPairing_self_eq_classFunctionNormSq phi

private theorem residual_sumNormSq_nonidentity_eq
    {Q : Type} [Group Q] [Fintype Q]
    (phi : ClassFunction Q ℂ) :
    ftTypePSumNormSq (nonidentitySet Q) phi =
      (Nat.card Q : ℝ) * classFunctionNormSq phi -
        Complex.normSq (phi 1) := by
  have htop : phi ∈
      ClassFunction.supportedOn ((⊤ : Subgroup Q) : Set Q) := by
    rw [ClassFunction.mem_supportedOn_iff]
    simp
  have hset : nonidentitySet Q =
      subgroupNonidentity (⊤ : Subgroup Q) := by
    ext x
    simp [subgroupNonidentity, nonidentitySet]
  rw [hset,
    FTTypePGeneratorBoundsInternal.sumNormSq_subgroupNonidentity_eq
      (⊤ : Subgroup Q) phi htop]

private theorem residual_ambientSharpMass_eq_restriction
    (H : Subgroup G) (chi : ClassFunction G ℂ) :
    ftTypePSumNormSq (subgroupNonidentity H) chi =
      ftTypePSumNormSq (nonidentitySet H)
        (ClassFunction.comap H.subtype chi) := by
  let sharpG := {x : G // x ∈ subgroupNonidentity H}
  let sharpH := {x : H // x ∈ nonidentitySet H}
  let e : sharpG ≃ sharpH :=
    { toFun := fun x ↦ ⟨⟨x, x.property.1⟩, by
          intro hx
          apply x.property.2
          exact congrArg Subtype.val hx⟩
      invFun := fun x ↦ ⟨x.1, ⟨x.1.property, by
          intro hx
          apply x.property
          apply Subtype.ext
          exact hx⟩⟩
      left_inv := fun x ↦ by apply Subtype.ext; rfl
      right_inv := fun x ↦ by
        apply Subtype.ext
        apply Subtype.ext
        rfl }
  unfold ftTypePSumNormSq FTTypePBoundsInfrastructureInternal.finiteSet
  change
    Finset.sum
        (Finset.univ.filter
          (fun x : G ↦ x ∈ subgroupNonidentity H))
        (fun x ↦ Complex.normSq (chi x)) =
      Finset.sum
        ((@Finset.univ H (ftTypePBoundsFirstThreeFintypeOfFinite H)).filter
          (fun x : H ↦ x ∈ nonidentitySet H))
        (fun x ↦
          Complex.normSq ((ClassFunction.comap H.subtype chi) x))
  rw [← Finset.sum_subtype_eq_sum_filter,
    ← Finset.sum_subtype_eq_sum_filter]
  apply Finset.sum_equiv e
  · intro x
    simp
  · intro x hx
    rfl

private theorem residual_nonidentity_card
    {Q : Type u} [Group Q] [Fintype Q] :
    (FTTypePBoundsInfrastructureInternal.finiteSet
      (nonidentitySet Q)).card = Nat.card Q - 1 := by
  have hfinset :
      FTTypePBoundsInfrastructureInternal.finiteSet
          (nonidentitySet Q) =
        (Finset.univ : Finset Q).erase 1 := by
    ext x
    simp [FTTypePBoundsInfrastructureInternal.finiteSet,
      nonidentitySet]
  rw [hfinset, Finset.card_erase_of_mem (Finset.mem_univ 1),
    Finset.card_univ, ← Nat.card_eq_fintype_card]

private theorem residual_P_mass_lower
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (alpha : ClassFunction ctx.H ℂ) (d : ℤ)
    (halphaOne : alpha 1 = (d : ℂ))
    (hconstant : ∀ x : ctx.P,
      alpha ⟨x, Fcore_sub_Fitting S x.property⟩ = alpha 1) :
    ((Nat.card ctx.P - 1 : ℕ) : ℝ) * (d : ℝ) ^ 2 ≤
      ftTypePSumNormSq (nonidentitySet ctx.H) alpha := by
  let inc : ctx.P ↪ ctx.H :=
    ⟨fun x ↦ ⟨x, Fcore_sub_Fitting S x.property⟩, by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : ctx.H ↦ (z : G)) hxy⟩
  let sharpP : Finset ctx.P :=
    FTTypePBoundsInfrastructureInternal.finiteSet
      (nonidentitySet ctx.P)
  let sharpH : Finset ctx.H :=
    FTTypePBoundsInfrastructureInternal.finiteSet
      (nonidentitySet ctx.H)
  have hsubset : sharpP.map inc ⊆ sharpH := by
    intro _ hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    have hxNe : x ≠ 1 := by
      simpa [sharpP, FTTypePBoundsInfrastructureInternal.finiteSet,
        nonidentitySet] using hx
    simp only [sharpH, FTTypePBoundsInfrastructureInternal.finiteSet,
      Finset.mem_filter, Finset.mem_univ, true_and,
      nonidentitySet, Set.mem_setOf_eq]
    intro hinc
    apply hxNe
    apply Subtype.ext
    exact congrArg (fun z : ctx.H ↦ (z : G)) hinc
  have hle :
      (∑ y ∈ sharpP.map inc, Complex.normSq (alpha y)) ≤
        ∑ y ∈ sharpH, Complex.normSq (alpha y) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun y _ _ ↦ Complex.normSq_nonneg (alpha y))
  have hleft :
      (∑ y ∈ sharpP.map inc, Complex.normSq (alpha y)) =
        ((Nat.card ctx.P - 1 : ℕ) : ℝ) * (d : ℝ) ^ 2 := by
    have hconstant' (x : ctx.P) : alpha (inc x) = alpha 1 := by
      change alpha ⟨x, Fcore_sub_Fitting S x.property⟩ = alpha 1
      exact hconstant x
    rw [Finset.sum_map]
    simp_rw [hconstant', halphaOne, Complex.normSq_intCast]
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : sharpP.card = Nat.card ctx.P - 1 := by
      simpa only [sharpP] using
        (residual_nonidentity_card (Q := ctx.P))
    rw [hcard]
    norm_num only [Nat.cast_sub, Nat.cast_one]
    ring
  rw [← hleft]
  unfold ftTypePSumNormSq
  have hsharpH :
      @FTTypePBoundsInfrastructureInternal.finiteSet ctx.H
          (ftTypePBoundsFintypeOfFinite ctx.H)
          (nonidentitySet ctx.H) = sharpH := by
    ext y
    simp [sharpH, FTTypePBoundsInfrastructureInternal.finiteSet]
  rw [hsharpH]
  exact hle

private theorem residual_normSq_real_mul_add_int
    (c : ℝ) (z : ℂ) (d : ℤ) :
    Complex.normSq ((c : ℂ) * z + (d : ℂ)) =
      c ^ 2 * Complex.normSq z +
        2 * c * (d : ℝ) * z.re + (d : ℝ) ^ 2 := by
  rw [Complex.normSq_add, Complex.normSq_mul]
  simp only [Complex.normSq_ofReal, Complex.normSq_intCast,
    map_intCast, Complex.mul_re, Complex.intCast_re,
    Complex.intCast_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  ring

private theorem residual_split_mass_identity
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (zeta : ClassFunction S ℂ)
    (chi : ClassFunction G ℂ)
    (a d : ℤ)
    (alpha : ClassFunction ctx.H ℂ)
    (hzeta : zeta ∈ seqIndT (k := ℂ) (HInS ctx))
    (halphaVirtual : ClassFunction.IsVirtual alpha)
    (halphaOne : alpha 1 = (d : ℂ))
    (hpointwise : ∀ x : ctx.H, x ≠ 1 →
      chi (x : G) =
        ((a : ℂ) / characterPairing zeta zeta) *
            zeta ⟨(x : G), (fittingWithin_le S) x.property⟩ +
          alpha x)
    (horth : characterPairing
      (residualFittingRestriction ctx zeta) alpha = 0)
    (hzetaPos : 0 < classFunctionNormSq zeta) :
    ftTypePSumNormSq (subgroupNonidentity ctx.H) chi =
      (a : ℝ) ^ 2 * (classFunctionNormSq zeta)⁻¹ *
          ((Nat.card S : ℝ) -
            Complex.normSq (zeta 1) *
              (classFunctionNormSq zeta)⁻¹) -
        2 * (a : ℝ) *
          ((zeta 1).re * (d : ℝ) *
            (classFunctionNormSq zeta)⁻¹) +
        ftTypePSumNormSq (nonidentitySet ctx.H) alpha := by
  let zetaH : ClassFunction ctx.H ℂ :=
    residualFittingRestriction ctx zeta
  let chiH : ClassFunction ctx.H ℂ :=
    ClassFunction.comap ctx.H.subtype chi
  let r : ℝ := classFunctionNormSq zeta
  let b : ℂ := (a : ℂ) / (r : ℂ)
  let beta : ClassFunction ctx.H ℂ := b • zetaH
  have hzetaVirtual : ClassFunction.IsVirtual zeta := by
    obtain ⟨v, hv⟩ := seqInd_vcharW (HInS ctx) hzeta
    exact ⟨v, hv⟩
  have hzetaHVirtual : ClassFunction.IsVirtual zetaH :=
    residualFittingRestriction_isVirtual ctx hzetaVirtual
  have hpairSelf : characterPairing zeta zeta = (r : ℂ) := by
    simpa only [r] using residual_pairing_self_eq_normSq hzetaVirtual
  have hr0 : r ≠ 0 := ne_of_gt hzetaPos
  have hpointwiseH : ∀ x : ctx.H, x ≠ 1 →
      chiH x = (beta + alpha) x := by
    intro x hx
    change chi (x : G) = b * zetaH x + alpha x
    rw [hpointwise x hx, hpairSelf]
    rfl
  have hmassPoint :
      ftTypePSumNormSq (nonidentitySet ctx.H) chiH =
        ftTypePSumNormSq (nonidentitySet ctx.H) (beta + alpha) := by
    unfold ftTypePSumNormSq
    apply Finset.sum_congr rfl
    intro x hx
    have hxNe : x ≠ 1 := by
      simpa [FTTypePBoundsInfrastructureInternal.finiteSet,
        nonidentitySet] using hx
    rw [hpointwiseH x hxNe]
  have hambient :
      ftTypePSumNormSq (subgroupNonidentity ctx.H) chi =
        ftTypePSumNormSq (nonidentitySet ctx.H) chiH := by
    simpa only [chiH] using
      residual_ambientSharpMass_eq_restriction ctx.H chi
  have hzetaSupport : zeta ∈
      ClassFunction.supportedOn ((HInS ctx : Subgroup S) : Set S) :=
    seqInd_on (HInS ctx) hzeta
  have hrestrictPair :=
    residualFittingRestriction_pairing ctx zeta zeta hzetaSupport
  have hzetaHNorm : classFunctionNormSq zetaH =
      ((HInS ctx).index : ℝ) * r := by
    have hpairH : characterPairing zetaH zetaH =
        (((HInS ctx).index : ℝ) * r : ℝ) := by
      rw [hrestrictPair, hpairSelf]
      norm_num
    have hself := residual_pairing_self_eq_normSq hzetaHVirtual
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_mul, Complex.ofReal_natCast] using
      hself.symm.trans hpairH
  have hbetaOrth : starCharacterPairing beta alpha = 0 := by
    rw [starCharacterPairing_smul_left,
      residual_starPairing_eq_pairing hzetaHVirtual halphaVirtual,
      horth, mul_zero]
  have hsum := residual_sumNormSq_nonidentity_eq (beta + alpha)
  have hnormAdd := residual_normSq_add_of_orthogonal beta alpha hbetaOrth
  have hbetaNorm := residual_normSq_smul b zetaH
  have halphaMass := residual_sumNormSq_nonidentity_eq alpha
  have hbetaOne : beta 1 = ((a : ℝ) / r : ℝ) * zeta 1 := by
    simp only [beta, b, zetaH, residualFittingRestriction_apply,
      ClassFunction.smul_apply, smul_eq_mul]
    have hone :
        (⟨((1 : ctx.H) : G),
          (fittingWithin_le S) (1 : ctx.H).property⟩ : S) = 1 := by
      rfl
    rw [hone]
    norm_num
  have hvalueOne : Complex.normSq ((beta + alpha) 1) =
      ((a : ℝ) / r) ^ 2 * Complex.normSq (zeta 1) +
        2 * ((a : ℝ) / r) * (d : ℝ) * (zeta 1).re +
          (d : ℝ) ^ 2 := by
    rw [ClassFunction.add_apply, hbetaOne, halphaOne]
    exact residual_normSq_real_mul_add_int
      ((a : ℝ) / r) (zeta 1) d
  have hcardH : Nat.card (HInS ctx) = Nat.card ctx.H :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (fittingWithin_le S)).toEquiv
  have hcardS : (Nat.card S : ℝ) =
      (Nat.card ctx.H : ℝ) * ((HInS ctx).index : ℝ) := by
    have h := (HInS ctx).index_mul_card
    rw [hcardH] at h
    exact_mod_cast (show Nat.card S =
      Nat.card ctx.H * (HInS ctx).index by
        simpa only [mul_comm] using h.symm)
  rw [hambient, hmassPoint, hsum, hnormAdd, hbetaNorm,
    hzetaHNorm, hvalueOne, halphaMass]
  rw [halphaOne, Complex.normSq_intCast]
  simp only [b, r, Complex.normSq_div, Complex.normSq_intCast,
    Complex.normSq_ofReal, inv_pow, div_pow]
  field_simp [hr0]
  rw [hcardS]
  ring

/-! ## Evaluation of reciprocal Dade and positivity of the pivot -/

private theorem residual_invDade_of_constant
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    {Q L : Subgroup Gamma} {A : Set Gamma}
    (dd : DadeHypothesis Q L A) (chi : ClassFunction Q ℂ)
    {a : Gamma} (ha : a ∈ A)
    (hchi : ∀ x : DadeSignalizer dd a,
      chi ⟨(x : Gamma) * a,
        Q.mul_mem (Dade_signalizer_sub dd a x.property)
          (dd.2.1 (dd.1.1 ha))⟩ =
        chi ⟨a, dd.2.1 (dd.1.1 ha)⟩) :
    invDade dd chi ⟨a, dd.1.1 ha⟩ =
      chi ⟨a, dd.2.1 (dd.1.1 ha)⟩ := by
  rw [invDade_apply]
  change
    (if _ha : a ∈ A then
      (Nat.card (DadeSignalizer dd a) : ℂ)⁻¹ *
        ∑ x : DadeSignalizer dd a,
          chi ⟨(x : Gamma) * a,
            Q.mul_mem (Dade_signalizer_sub dd a x.property)
              (dd.2.1 (dd.1.1 ha))⟩
    else 0) = chi ⟨a, dd.2.1 (dd.1.1 ha)⟩
  rw [dif_pos ha]
  rw [show (∑ x : DadeSignalizer dd a,
      chi ⟨(x : Gamma) * a,
        Q.mul_mem (Dade_signalizer_sub dd a x.property)
          (dd.2.1 (dd.1.1 ha))⟩) =
      ∑ _x : DadeSignalizer dd a,
        chi ⟨a, dd.2.1 (dd.1.1 ha)⟩ by
    apply Finset.sum_congr rfl
    intro x _
    exact hchi x]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Nat.card_eq_fintype_card]
  field_simp [Nat.cast_ne_zero.mpr
    (Fintype.card_pos.ne' : Fintype.card (DadeSignalizer dd a) ≠ 0)]

private theorem residual_invDade_fitting_value
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (ddH : DadeHypothesis (⊤ : Subgroup G) S
      (subgroupNonidentity ((HInS ctx).map S.subtype)))
    (chi : ClassFunction G ℂ)
    (x : ctx.H) (hx : x ≠ 1) :
    invDade ddH (sourceMap chi)
        ⟨(x : G), (fittingWithin_le S) x.property⟩ = chi (x : G) := by
  let xS : S := ⟨(x : G), (fittingWithin_le S) x.property⟩
  have hxA : (xS : G) ∈
      subgroupNonidentity ((HInS ctx).map S.subtype) := by
    rw [residualFittingInS_map ctx]
    exact ⟨x.property, by
      intro hxOne
      apply hx
      exact Subtype.ext hxOne⟩
  have hTI : IsNormalizedTI
      (subgroupNonidentity ((HInS ctx).map S.subtype))
      (⊤ : Subgroup G) S := by
    simpa only [residualFittingInS_map ctx] using
      fittingSharp_normalizedTI ctx
  have hsignal : DadeSignalizer ddH (xS : G) = ⊥ :=
    ((Dade_normedTI_P ddH).mp hTI).2 hxA
  have hconstant : ∀ y : DadeSignalizer ddH (xS : G),
      sourceMap chi
          ⟨(y : G) * (xS : G),
            (⊤ : Subgroup G).mul_mem
              (Dade_signalizer_sub ddH (xS : G) y.property)
              (ddH.2.1 (ddH.1.1 hxA))⟩ =
        sourceMap chi
          ⟨(xS : G), ddH.2.1 (ddH.1.1 hxA)⟩ := by
    intro y
    have hyMem : (y : G) ∈ (⊥ : Subgroup G) := by
      rw [← hsignal]
      exact y.property
    have hy : (y : G) = 1 := by simpa using hyMem
    apply congrArg (sourceMap chi)
    apply Subtype.ext
    simpa only [hy, one_mul]
  have hvalue := residual_invDade_of_constant
    ddH (sourceMap chi) hxA hconstant
  simpa [xS, sourceMap, ClassFunction.comap_apply] using hvalue

private theorem residual_seqInd_norm_pos
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (zeta : ClassFunction S ℂ)
    (hzeta : zeta ∈ seqIndT (k := ℂ) (HInS ctx)) :
    0 < classFunctionNormSq zeta := by
  have hnonneg := classFunctionNormSq_nonneg zeta
  have hne : classFunctionNormSq zeta ≠ 0 := by
    intro hzero
    have hzetaZero := (classFunctionNormSq_eq_zero_iff zeta).mp hzero
    have hdegree := seqInd1_neq0 (HInS ctx) hzeta
    apply hdegree
    rw [hzetaZero]
    rfl
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

private theorem residual_pairing_finset_sum_right
    {Q I : Type u} [Group Q] [Fintype Q] [DecidableEq I]
    (phi : ClassFunction Q ℂ) (T : Finset I)
    (psi : I → ClassFunction Q ℂ) :
    characterPairing phi (∑ i ∈ T, psi i) =
      ∑ i ∈ T, characterPairing phi (psi i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih =>
      rw [Finset.sum_insert hi, characterPairing_add_right,
        ih, Finset.sum_insert hi]

/-! ## The residual split consumed by the three public estimates -/

private theorem calS1_split1
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (tau1 : ClassFunction S ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (zeta1 : ClassFunction S ℂ)
    (chi : ClassFunction G ℂ)
    (hcoh : coherent_with
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
      (nonidentitySet S) ctx.tau tau1)
    (hzeta1 : zeta1 ∈ calS1 ctx)
    (hchi : ClassFunction.IsVirtual chi)
    (horth : ∀ zeta ∈ calS1 ctx, zeta ≠ zeta1 →
      characterPairing (tau1 zeta) chi = 0) :
    ∃ a : ℤ,
      ((a : ℂ) = characterPairing (tau1 zeta1) chi) ∧
      ∃ alpha : ClassFunction ctx.H ℂ,
        ∃ alphaDegree : ℤ,
          ∃ alphaNorm : ℕ,
            (alpha 1 = (alphaDegree : ℂ)) ∧
            (∃ z : VirtualCharacter ctx.H ℂ,
              VirtualCharacter.realize z = alpha ∧
                normSq z = (alphaNorm : ℤ)) ∧
            (∀ x : ctx.P,
              alpha ⟨x, Fcore_sub_Fitting S x.property⟩ = alpha 1) ∧
            (∀ x : ctx.H, x ≠ 1 →
              chi (x : G) =
                ((a : ℂ) / characterPairing zeta1 zeta1) *
                    zeta1 ⟨x, (fittingWithin_le S) x.property⟩ +
                  alpha x) ∧
            (ftTypePSumNormSq (subgroupNonidentity ctx.H) chi =
              (a : ℝ) ^ 2 * (classFunctionNormSq zeta1)⁻¹ *
                  ((Nat.card S : ℝ) -
                    Complex.normSq (zeta1 1) *
                      (classFunctionNormSq zeta1)⁻¹) -
                2 * (a : ℝ) *
                  ((zeta1 1).re * (alphaDegree : ℝ) *
                    (classFunctionNormSq zeta1)⁻¹) +
                ftTypePSumNormSq (nonidentitySet ctx.H) alpha) ∧
            ((((Nat.card ctx.P - 1 : ℕ) : ℝ) *
                (alphaDegree : ℝ) ^ 2) ≤
              ftTypePSumNormSq (nonidentitySet ctx.H) alpha) ∧
            (0 < classFunctionNormSq zeta1) := by
  classical
  let H : Subgroup S := HInS ctx
  let P : Subgroup H := PInH ctx
  let allRows : Finset (ClassFunction S ℂ) := seqIndT (k := ℂ) H
  let zeta0 : ClassFunction S ℂ := ClassFunction.inverseLinear zeta1
  have hzeta0 : zeta0 ∈ calS1 ctx :=
    seqInd_inverse_mem (k := ℂ) H P ⊥ hzeta1
  have hzeta0Ne : zeta0 ≠ zeta1 :=
    seqInd_conjC_neq (k := ℂ) H (mFT_odd S) P ⊥ hzeta1
  have hzeta1Rows : zeta1 ∈ allRows :=
    FTTypePBoundsInfrastructureInternal.fittingCoreFamily_subset ctx hzeta1
  have hzeta0Rows : zeta0 ∈ allRows :=
    FTTypePBoundsInfrastructureInternal.fittingCoreFamily_subset ctx hzeta0
  have hHmap : H.map S.subtype = ctx.H := by
    simpa only [H] using residualFittingInS_map ctx
  let ddH : DadeHypothesis (⊤ : Subgroup G) S
      (subgroupNonidentity (H.map S.subtype)) := by
    simpa only [hHmap] using fittingSharpDade ctx
  have hcohH : coherent_with
      (↑(calS1 ctx) : Set (ClassFunction S ℂ))
      (nonidentitySet S) (Dade ddH) (sourceMap.comp tau1) := by
    have hraw := residual_fittingDade_coherent ctx tau1 hcoh
      (calS1_subset_coreClosure ctx)
    simpa only [ddH, hHmap] using hraw
  have horth0 : characterPairing (tau1 zeta0) chi = 0 :=
    horth zeta0 hzeta0 hzeta0Ne
  have hzeta1ImageVirtual : ClassFunction.IsVirtual (tau1 zeta1) :=
    hcoh.mapsToVirtual zeta1 (calS1_subset_coreClosure ctx hzeta1)
  obtain ⟨a, haPair⟩ :=
    PTypeCorePairingInternal.pTypeCore_virtual_pairing_isInt
      hzeta1ImageVirtual hchi
  have ha : (a : ℂ) = characterPairing (tau1 zeta1) chi :=
    haPair.symm
  have hcoeffCore (xi : ClassFunction S ℂ) (hxi : xi ∈ calS1 ctx) :
      invDadeSeqIndCoefficient ddH zeta0 (sourceMap chi) xi =
        characterPairing (tau1 xi) chi :=
    residual_fittingCoefficient_virtual
      ctx ddH tau1 hcohH zeta0 xi hzeta0 hxi chi hchi horth0
  have hcoeffPivot :
      invDadeSeqIndCoefficient ddH zeta0 (sourceMap chi) zeta1 =
        (a : ℂ) := by
    rw [hcoeffCore zeta1 hzeta1, ← haPair]

  let rows : Finset (ClassFunction S ℂ) := allRows.erase zeta0
  let tail : Finset (ClassFunction S ℂ) :=
    rows.filter fun xi ↦ xi ∉ calS1 ctx
  let coeff : ClassFunction S ℂ → ℂ := fun xi ↦
    invDadeSeqIndCoefficient ddH zeta0 (sourceMap chi) xi
  let tailTerm : ClassFunction S ℂ → ClassFunction S ℂ :=
    fun xi ↦ (star (coeff xi) / starCharacterPairing xi xi) • xi
  let alphaS : ClassFunction S ℂ := ∑ xi ∈ tail, tailTerm xi
  let alpha : ClassFunction ctx.H ℂ :=
    residualFittingRestriction ctx alphaS

  have htailRows {xi : ClassFunction S ℂ} (hxi : xi ∈ tail) :
      xi ∈ allRows :=
    (Finset.mem_erase.mp (Finset.mem_filter.mp hxi).1).2
  have htailOutside {xi : ClassFunction S ℂ} (hxi : xi ∈ tail) :
      xi ∉ calS1 ctx :=
    (Finset.mem_filter.mp hxi).2
  have halphaVirtual : ClassFunction.IsVirtual alpha := by
    have hsum : ClassFunction.IsVirtual
        (∑ xi ∈ tail,
          residualFittingRestriction ctx (tailTerm xi)) := by
      apply residual_virtual_finset_sum tail
      intro xi hxi
      obtain ⟨n, hn⟩ := residual_tailCoefficient_integer
        ctx ddH zeta0 xi hzeta0Rows (htailRows hxi) chi hchi
      exact residual_normalizedTailTerm_isVirtual
        ctx xi (htailRows hxi) (coeff xi) n hn
    dsimp only [alpha, alphaS]
    rw [map_sum]
    simpa only [tailTerm] using hsum
  have halphaConstant : ∀ x : ctx.P,
      alpha ⟨x, Fcore_sub_Fitting S x.property⟩ = alpha 1 := by
    intro x
    dsimp only [alpha, alphaS]
    rw [map_sum]
    simp only [ClassFunction.finset_sum_apply]
    apply Finset.sum_congr rfl
    intro xi hxi
    exact residual_tail_constant_on_P ctx xi (htailRows hxi)
      (htailOutside hxi)
      (star (coeff xi) / starCharacterPairing xi xi) x
  have hzetaSupport : zeta1 ∈
      ClassFunction.supportedOn ((H : Subgroup S) : Set S) :=
    seqInd_on H hzeta1Rows
  have horthAlpha : characterPairing
      (residualFittingRestriction ctx zeta1) alpha = 0 := by
    dsimp only [alpha, alphaS]
    rw [map_sum, residual_pairing_finset_sum_right]
    apply Finset.sum_eq_zero
    intro xi hxi
    have hne : zeta1 ≠ xi := by
      intro heq
      apply htailOutside hxi
      rw [← heq]
      exact hzeta1
    dsimp only [tailTerm]
    rw [map_smul, characterPairing_smul_right,
      residualFittingRestriction_pairing ctx zeta1 xi hzetaSupport,
      seqInd_ortho H hzeta1Rows (htailRows hxi) hne,
      mul_zero, mul_zero]

  obtain ⟨zAlpha, hzAlpha⟩ := halphaVirtual
  have halphaVirtualAgain : ClassFunction.IsVirtual alpha :=
    ⟨zAlpha, hzAlpha⟩
  let alphaDegree : ℤ := VirtualCharacter.integralDegree zAlpha
  have halphaOne : alpha 1 = (alphaDegree : ℂ) := by
    rw [← hzAlpha, VirtualCharacter.realize_one_eq_integralDegree]
  let alphaNorm : ℕ := (normSq zAlpha).toNat
  have hzAlphaNorm : normSq zAlpha = (alphaNorm : ℤ) := by
    exact_mod_cast
      (Int.toNat_of_nonneg (normSq_nonneg zAlpha)).symm
  have halphaWitness : ∃ z : VirtualCharacter ctx.H ℂ,
      VirtualCharacter.realize z = alpha ∧
        normSq z = (alphaNorm : ℤ) :=
    ⟨zAlpha, hzAlpha, hzAlphaNorm⟩

  have hzeta1Rows' : zeta1 ∈ rows :=
    Finset.mem_erase.mpr ⟨Ne.symm hzeta0Ne, hzeta1Rows⟩
  have hcoeffZero (xi : ClassFunction S ℂ)
      (hxi : xi ∈ calS1 ctx) (hne : xi ≠ zeta1) :
      coeff xi = 0 := by
    dsimp only [coeff]
    rw [hcoeffCore xi hxi, horth xi hxi hne]
  have hsplit :
      IsInvDadeSeqIndSum H ddH zeta0 rows (sourceMap chi) := by
    simpa only [rows, allRows] using
      FTTypePBoundsInfrastructureInternal.invDade_split_erase
        H ddH zeta0 (sourceMap chi) hzeta0Rows
  have hsumAt (x : S) :
      (∑ xi ∈ rows,
        (star (coeff xi) / starCharacterPairing xi xi) * xi x) =
      ((a : ℂ) / characterPairing zeta1 zeta1) * zeta1 x +
        alphaS x := by
    have hpartition := Finset.sum_filter_add_sum_filter_not
      (s := rows) (p := fun xi ↦ xi ∈ calS1 ctx)
      (f := fun xi ↦
        (star (coeff xi) / starCharacterPairing xi xi) * xi x)
    rw [← hpartition]
    have hcorePart :
        (∑ xi ∈ rows.filter (fun xi ↦ xi ∈ calS1 ctx),
          (star (coeff xi) / starCharacterPairing xi xi) * xi x) =
        (star (coeff zeta1) / starCharacterPairing zeta1 zeta1) *
          zeta1 x := by
      rw [Finset.sum_eq_single zeta1]
      · intro xi hxi hne
        have hxiCore := (Finset.mem_filter.mp hxi).2
        rw [hcoeffZero xi hxiCore hne]
        simp
      · intro hnot
        exact (hnot
          (Finset.mem_filter.mpr ⟨hzeta1Rows', hzeta1⟩)).elim
    rw [hcorePart]
    have htailEq :
        rows.filter (fun xi ↦ ¬xi ∈ calS1 ctx) = tail := rfl
    rw [htailEq]
    have hzetaVirtual : ClassFunction.IsVirtual zeta1 := by
      obtain ⟨v, hv⟩ := seqInd_vcharW H hzeta1Rows
      exact ⟨v, hv⟩
    have hcoeffPivot' : coeff zeta1 = (a : ℂ) := by
      dsimp only [coeff]
      exact hcoeffPivot
    rw [hcoeffPivot']
    have hstarA : star (a : ℂ) = (a : ℂ) := by simp
    rw [hstarA, residual_starPairing_eq_pairing
      hzetaVirtual hzetaVirtual]
    dsimp only [alphaS, tailTerm]
    simp only [ClassFunction.finset_sum_apply,
      ClassFunction.smul_apply, smul_eq_mul]
  have hpointwise : ∀ x : ctx.H, x ≠ 1 →
      chi (x : G) =
        ((a : ℂ) / characterPairing zeta1 zeta1) *
            zeta1 ⟨x, (fittingWithin_le S) x.property⟩ +
          alpha x := by
    intro x hx
    let xS : S := ⟨(x : G), (fittingWithin_le S) x.property⟩
    have hxSupport : (xS : G) ∈
        subgroupNonidentity (H.map S.subtype) := by
      rw [hHmap]
      exact ⟨x.property, by
        intro hxOne
        apply hx
        exact Subtype.ext hxOne⟩
    have hvalue := hsplit.value_on_support xS hxSupport
    rw [residual_invDade_fitting_value ctx ddH chi x hx,
      hsumAt xS] at hvalue
    dsimp only [xS, alpha] at hvalue ⊢
    simpa only [residualFittingRestriction_apply] using hvalue
  have hzetaPositive := residual_seqInd_norm_pos ctx zeta1 hzeta1Rows
  have hmass := residual_split_mass_identity
    ctx zeta1 chi a alphaDegree alpha hzeta1Rows
      halphaVirtualAgain halphaOne hpointwise horthAlpha hzetaPositive
  have hresidual := residual_P_mass_lower
    ctx alpha alphaDegree halphaOne halphaConstant
  exact ⟨a, ha, alpha, alphaDegree, alphaNorm,
    halphaOne, halphaWitness, halphaConstant, hpointwise,
    hmass, hresidual, hzetaPositive⟩

end FTTypePBoundsFirstThreeInternal

open FTTypePBoundsFirstThreeInternal

/-! ## Peterfalvi (13.6)--(13.8) -/

/-- `PFsection13.v: FTtypeP_sum_Ind_Fitting_lb`, Peterfalvi (13.6). -/
theorem FTtypeP_sum_Ind_Fitting_lb
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (tau1 : ClassFunction S ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (lambda : ClassFunction S ℂ)
    (hcoh : coherent_with
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
      (nonidentitySet S) ctx.tau tau1)
    (hirr : lambda ∈ irr_Ind_Fitting S)
    (hcalS : lambda ∈ ftTypePCoreFamily S) :
    ftTypePSumNormSq (subgroupNonidentity ctx.H) (tau1 lambda) ≥
      (Nat.card S : ℝ) - Complex.normSq (lambda 1) := by
  have hlambdaLayer : lambda ∈
      FTTypePBoundsInfrastructureInternal.fittingCoreFamily ctx :=
    lambda_mem_calS1 ctx lambda hirr hcalS
  have hlambdaSpan : lambda ∈ AddSubgroup.closure
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ)) :=
    AddSubgroup.subset_closure hcalS
  letI : Invertible (Nat.card S : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have htargetVirtual : ClassFunction.IsVirtual (tau1 lambda) :=
    hcoh.mapsToVirtual lambda hlambdaSpan
  have htargetOrthogonal : ∀ zeta ∈
      FTTypePBoundsInfrastructureInternal.fittingCoreFamily ctx,
      zeta ≠ lambda →
        characterPairing (tau1 zeta) (tau1 lambda) = 0 := by
    intro zeta hzeta hne
    have hzetaSpan : zeta ∈ AddSubgroup.closure
        (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ)) :=
      coreClosure_of_S1case ctx zeta (S1cases ctx zeta hzeta)
    rw [hcoh.isometry zeta hzetaSpan lambda hlambdaSpan]
    exact seqInd_ortho (HInS ctx)
      (FTTypePBoundsInfrastructureInternal.seqIndD_mem_seqIndT
        (HInS ctx) (PInH ctx) ⊥ hzeta)
      (FTTypePBoundsInfrastructureInternal.seqIndD_mem_seqIndT
        (HInS ctx) (PInH ctx) ⊥ hlambdaLayer)
      hne
  obtain ⟨a, haPair, alpha, alphaDegree, _alphaNorm,
      halphaOne, _halphaWitness, halphaOnP, hpointwise,
      hmass, hresidual, _hlambdaNormPos⟩ :=
    calS1_split1 ctx tau1 lambda (tau1 lambda) hcoh hlambdaLayer
      htargetVirtual htargetOrthogonal
  have hpairSelf :
      characterPairing (tau1 lambda) (tau1 lambda) = 1 := by
    rw [hcoh.isometry lambda hlambdaSpan lambda hlambdaSpan]
    exact IrreducibleCharacter.characterPairing_self ⟨lambda, hirr.1⟩
  have haComplex : (a : ℂ) = ((1 : ℤ) : ℂ) := by
    simpa only [Int.cast_one] using haPair.trans hpairSelf
  have ha : a = 1 := Int.cast_injective (α := ℂ) haComplex
  have hlambdaNorm : classFunctionNormSq lambda = 1 :=
    irreducible_classFunctionNormSq ⟨lambda, hirr.1⟩
  have hdegreeDivisible : (ctx.q : ℤ) ∣ alphaDegree :=
    q_dvd_alphaDegree ctx tau1 lambda hcoh hirr hcalS
      a alpha alphaDegree ha halphaOne halphaOnP hpointwise
  exact lambda_mass_lower ctx lambda hirr a alphaDegree
    (ftTypePSumNormSq (nonidentitySet ctx.H) alpha)
    (ftTypePSumNormSq (subgroupNonidentity ctx.H) (tau1 lambda))
    ha hlambdaNorm hmass hresidual hdegreeDivisible

/-- `PFsection13.v: FTtypeP_sum_cycTIiso10_lb`, Peterfalvi (13.7). -/
theorem FTtypeP_sum_cycTIiso10_lb
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ftTypePSumNormSq (subgroupNonidentity ctx.H) (ftTypePEta10 ctx) ≥
      (ftTypePSetCard (subgroupNonidentity ctx.H) : ℝ) := by
  obtain ⟨tau1, hcoh, hTIred⟩ := FTtypeP_coherence ctx
  obtain ⟨b, _hbThree, hrows⟩ := hTIred
  let j0 : IrreducibleCharacter W₂ ℂ := ftTypePRightIndex ctx
  have hj0 : j0 ≠ IrreducibleCharacter.trivial :=
    FTTypePBoundsInfrastructureInternal.rightIndex_ne_trivial ctx
  have hmuLayer : ctx.mu j0 ∈
      FTTypePBoundsInfrastructureInternal.fittingCoreFamily ctx :=
    mu_mem_calS1 ctx j0 hj0
  have hetaVirtual : ClassFunction.IsVirtual (ftTypePEta10 ctx) := by
    simpa only [ftTypePEta10] using
      eta_isVirtual ctx (ftTypePLeftIndex ctx)
        IrreducibleCharacter.trivial
  have htargetOrthogonal : ∀ zeta ∈
      FTTypePBoundsInfrastructureInternal.fittingCoreFamily ctx,
      zeta ≠ ctx.mu j0 →
        characterPairing (tau1 zeta) (ftTypePEta10 ctx) = 0 := by
    intro zeta hzeta _hne
    exact fittingCore_pairing_eta10_of_case
      ctx tau1 hcoh b hrows zeta (S1cases ctx zeta hzeta)
  obtain ⟨a, haPair, alpha, alphaDegree, alphaNorm,
      halphaOne, halphaWitness, _halphaOnP, hpointwise,
      hmass, hresidual, _hmuNormPos⟩ :=
    calS1_split1 ctx tau1 (ctx.mu j0) (ftTypePEta10 ctx)
      hcoh hmuLayer hetaVirtual htargetOrthogonal
  have hpairZero :
      characterPairing (tau1 (ctx.mu j0)) (ftTypePEta10 ctx) = 0 :=
    mu_pairing_eta10_eq_zero ctx tau1 b j0 hj0 (hrows j0 hj0)
  have haComplex : (a : ℂ) = ((0 : ℤ) : ℂ) := by
    simpa only [Int.cast_zero] using haPair.trans hpairZero
  have ha : a = 0 := Int.cast_injective (α := ℂ) haComplex
  exact eta10_mass_lower ctx (ctx.mu j0) a alpha alphaDegree alphaNorm
    ha halphaOne halphaWitness hpointwise hmass hresidual

/-- `PFsection13.v: FTtypeP_sum_cycTIiso01_lb`, Peterfalvi (13.8). -/
theorem FTtypeP_sum_cycTIiso01_lb
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ftTypePSumNormSq (subgroupNonidentity ctx.H) (ftTypePEta01 ctx) ≥
      (Nat.card ctx.PU : ℝ) - (ctx.u : ℝ) ^ 2 := by
  obtain ⟨tau1, hcoh, hTIred⟩ := FTtypeP_coherence ctx
  obtain ⟨b, _hbThree, hrows⟩ := hTIred
  let j1 : IrreducibleCharacter W₂ ℂ :=
    ftTypePSignIndex b (ftTypePRightIndex ctx)
  have hj1 : j1 ≠ IrreducibleCharacter.trivial :=
    signIndex_ne_trivial b (ftTypePRightIndex ctx)
      (FTTypePBoundsInfrastructureInternal.rightIndex_ne_trivial ctx)
  have hmuLayer : ctx.mu j1 ∈
      FTTypePBoundsInfrastructureInternal.fittingCoreFamily ctx :=
    mu_mem_calS1 ctx j1 hj1
  have hetaVirtual : ClassFunction.IsVirtual (ftTypePEta01 ctx) := by
    simpa only [ftTypePEta01] using
      eta_isVirtual ctx IrreducibleCharacter.trivial
        (ftTypePRightIndex ctx)
  have htargetOrthogonal : ∀ zeta ∈
      FTTypePBoundsInfrastructureInternal.fittingCoreFamily ctx,
      zeta ≠ ctx.mu j1 →
        characterPairing (tau1 zeta) (ftTypePEta01 ctx) = 0 := by
    intro zeta hzeta hne
    exact fittingCore_pairing_eta01_of_case
      ctx tau1 hcoh b hrows zeta hne (S1cases ctx zeta hzeta)
  obtain ⟨a, haPair, alpha, alphaDegree, _alphaNorm,
      _halphaOne, _halphaWitness, _halphaOnP, _hpointwise,
      hmass, hresidual, _hmuNormPos⟩ :=
    calS1_split1 ctx tau1 (ctx.mu j1) (ftTypePEta01 ctx)
      hcoh hmuLayer hetaVirtual htargetOrthogonal
  have hpairSign :
      characterPairing (tau1 (ctx.mu j1)) (ftTypePEta01 ctx) =
        ftTypePBooleanSign b := by
    simpa only [j1] using mu_pairing_eta01_pivot ctx tau1 b hrows
  have haComplex :
      (a : ℂ) = (((if b then -1 else 1 : ℤ) : ℂ)) :=
    haPair.trans (hpairSign.trans (intSign_cast b).symm)
  have ha : a = (if b then -1 else 1 : ℤ) :=
    Int.cast_injective (α := ℂ) haComplex
  have hmuNorm : classFunctionNormSq (ctx.mu j1) = (ctx.q : ℝ) :=
    mu_classFunctionNormSq ctx j1
  exact eta01_mass_lower ctx b a alphaDegree
    (ftTypePSumNormSq (nonidentitySet ctx.H) alpha)
    (ftTypePSumNormSq (subgroupNonidentity ctx.H) (ftTypePEta01 ctx))
    ha (by simpa only [j1] using hmuNorm) hmass hresidual

end

end Submission.OddOrder.PF
