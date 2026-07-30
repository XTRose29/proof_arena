import Submission.OddOrder.PF.Section12.FTType1Partition

/-!
# Peterfalvi Section 12: type-I subcoherence

This module proves Peterfalvi (12.2)(b).  It first fixes the canonical target
family attached to the irreducible type-I characters, then flattens those
families over the constituents of each sequentially induced character.  The
result is the subcoherent family used by the remaining type-I arguments.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open ClassFunction
open scoped BigOperators Classical Pointwise

variable {G : Type} [Group G] [Finite G] [IsMinSimpleOddGroup G]

local instance : Fintype G := Fintype.ofFinite G

/-! ## Canonical irreducible target families -/

namespace FTType1Context

/-- The canonical target family supplied by irreducible subcoherence. -/
noncomputable def R1 {L : Subgroup G} (ctx : FTType1Context L) :
    ClassFunction L ℂ → Finset (ClassFunction G ℂ) :=
  Classical.choose (FTtype1_irr_subcoherent ctx)

/-- The chosen target family satisfies irreducible subcoherence. -/
theorem R1_subcoherent {L : Subgroup G} (ctx : FTType1Context L) :
    subcoherent
      (FTType1IrrFamily L : Set (ClassFunction L ℂ))
      ctx.tau ctx.R1 :=
  Classical.choose_spec (FTtype1_irr_subcoherent ctx)

end FTType1Context

/-- The three conclusions attached to one irreducible index in
Peterfalvi (12.2)(b). -/
structure FTType1IrrPairFacts
    {L : Subgroup G} (ctx : FTType1Context L)
    (i : IrreducibleCharacter L ℂ) : Prop where
  orthonormal :
    FTType1Orthonormal (ctx.R1 (i : ClassFunction L ℂ))
  card_eq_two :
    (ctx.R1 (i : ClassFunction L ℂ)).card = 2
  dade_difference :
    ctx.tau
        ((i : ClassFunction L ℂ) -
          ClassFunction.inverseLinear (G := L) (k := ℂ)
            (i : ClassFunction L ℂ)) =
      ∑ mu ∈ ctx.R1 (i : ClassFunction L ℂ), mu

/-- Peterfalvi (12.2)(b), including the relation between the irreducible
target families and the family attached to a sequentially induced
character. -/
structure FTType1SubcoherentConclusion
    {L : Subgroup G} (ctx : FTType1Context L)
    (R : ClassFunction L ℂ → Finset (ClassFunction G ℂ)) : Prop where
  subcoherent_family :
    subcoherent
      (FTType1SeqIndFamily L : Set (ClassFunction L ℂ))
      ctx.tau R
  irreducible_pairs :
    ∀ i ∈ FTType1IrrIndex L, FTType1IrrPairFacts ctx i
  flatten :
    ∀ chi : ClassFunction L ℂ,
      R chi = (constituents chi).biUnion
        (fun i ↦ ctx.R1 (i : ClassFunction L ℂ))

universe u

private theorem orthonormalFullNorm
    {Q : Type u} [Group Q] [Fintype Q]
    (E : Finset (ClassFunction Q ℂ))
    (hE : FTType1Orthonormal E) :
    characterPairing (∑ alpha ∈ E, alpha) (∑ alpha ∈ E, alpha) =
      (E.card : ℂ) := by
  rw [FTType1InfrastructureInternal.pairingFinsetSumLeft]
  calc
    (∑ alpha ∈ E, characterPairing alpha (∑ beta ∈ E, beta)) =
        ∑ _alpha ∈ E, (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro alpha halpha
      rw [FTType1InfrastructureInternal.pairingFinsetSumRight,
        Finset.sum_eq_single alpha]
      · rw [hE alpha halpha alpha halpha, if_pos rfl]
      · intro beta hbeta hne
        rw [hE alpha halpha beta hbeta, if_neg hne.symm]
      · exact fun h ↦ (h halpha).elim
    _ = (E.card : ℂ) := by simp

private theorem irreduciblePairFacts
    {L : Subgroup G} (ctx : FTType1Context L) :
    ∀ i ∈ FTType1IrrIndex L, FTType1IrrPairFacts ctx i := by
  classical
  letI : Invertible (Nat.card L : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  intro i hi
  have hsubI := ctx.R1_subcoherent
  have hiI : (i : ClassFunction L ℂ) ∈ FTType1IrrFamily L :=
    Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have horth : FTType1Orthonormal
      (ctx.R1 (i : ClassFunction L ℂ)) :=
    hsubI.image_orthonormal (i : ClassFunction L ℂ) hiI
  have hiNe : i ≠
      (IrreducibleCharacter.trivial : IrreducibleCharacter L ℂ) := by
    intro hiOne
    subst i
    rw [FTType1IrrIndex, mem_Iirr_kerD] at hi
    apply hi.2
    intro x hx y
    simp
  have hiDual : i ≠ IrreducibleCharacter.dual i := by
    intro hidual
    apply hiNe
    exact (odd_eq_conj_irr1 (mFT_odd L) i).mp hidual.symm
  let d : ClassFunction L ℂ :=
    (i : ClassFunction L ℂ) -
      ClassFunction.inverseLinear (i : ClassFunction L ℂ)
  have hdSpan : d ∈ AddSubgroup.closure
      (FTType1IrrFamily L : Set (ClassFunction L ℂ)) :=
    (AddSubgroup.closure _).sub_mem
      (AddSubgroup.subset_closure hiI)
      (AddSubgroup.subset_closure (hsubI.inverse_mem _ hiI))
  have hdOff : d ∈ ClassFunction.supportedOn (nonidentitySet L) :=
    FTType1InfrastructureInternal.inverseSubSupported _
  have hsourceNorm : characterPairing d d = (2 : ℂ) := by
    dsimp only [d]
    rw [FTType1InfrastructureInternal.pairingSubLeft,
      FTType1InfrastructureInternal.pairingSubRight,
      FTType1InfrastructureInternal.pairingSubRight,
      ClassFunction.inverseLinear_irreducible,
      IrreducibleCharacter.characterPairing_self,
      IrreducibleCharacter.characterPairing_self,
      IrreducibleCharacter.characterPairing_eq_zero hiDual,
      IrreducibleCharacter.characterPairing_eq_zero hiDual.symm]
    norm_num
  have htargetNorm := orthonormalFullNorm _ horth
  have hiso := hsubI.tau_isometry d hdSpan hdOff d hdSpan hdOff
  have hdiff := hsubI.tau_inverse_sub (i : ClassFunction L ℂ) hiI
  have hcardCast :
      ((ctx.R1 (i : ClassFunction L ℂ)).card : ℂ) = 2 := by
    rw [← htargetNorm, ← hdiff, hiso, hsourceNorm]
  exact ⟨horth, Nat.cast_injective hcardCast, hdiff⟩

/-! ## Lifting subcoherence through the constituent partition -/

/-- `PFsection12.v: FTtype1_subcoherent`, Peterfalvi (12.2)(b). -/
theorem FTtype1_subcoherent
    {L : Subgroup G} (ctx : FTType1Context L) :
    ∃ R : ClassFunction L ℂ → Finset (ClassFunction G ℂ),
      FTType1SubcoherentConclusion ctx R := by
  classical
  letI : Invertible (Nat.card L : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let H := FTType1FittingIn L
  letI : H.Normal := Fcore_normal L
  let R : ClassFunction L ℂ → Finset (ClassFunction G ℂ) :=
    fun chi ↦ (constituents chi).biUnion
      (fun i ↦ ctx.R1 (i : ClassFunction L ℂ))
  have hsubI := ctx.R1_subcoherent
  have hmemI {chi : ClassFunction L ℂ}
      (hchi : chi ∈ FTType1SeqIndFamily L)
      {i : IrreducibleCharacter L ℂ} (hi : i ∈ constituents chi) :
      (i : ClassFunction L ℂ) ∈ FTType1IrrFamily L := by
    apply Finset.mem_image.mpr
    exact ⟨i, (FTtype1_irrP ctx i).mpr ⟨chi, hchi, hi⟩, rfl⟩
  have hseqInIrrClosure {chi : ClassFunction L ℂ}
      (hchi : chi ∈ FTType1SeqIndFamily L) :
      chi ∈ AddSubgroup.closure
        (FTType1IrrFamily L : Set (ClassFunction L ℂ)) := by
    rw [(FTtype1_seqInd_facts ctx chi hchi).constituent_sum]
    apply AddSubgroup.sum_mem
    intro i hi
    exact AddSubgroup.subset_closure (hmemI hchi hi)
  have hspanSeq : AddSubgroup.closure
      (FTType1SeqIndFamily L : Set (ClassFunction L ℂ)) ≤
      AddSubgroup.closure
        (FTType1IrrFamily L : Set (ClassFunction L ℂ)) := by
    apply (AddSubgroup.closure_le _).2
    intro chi hchi
    exact hseqInIrrClosure hchi
  have hdistinctOfPairingZero
      {phi psi : ClassFunction L ℂ}
      (hphi : phi ∈ FTType1SeqIndFamily L)
      (hpsi : psi ∈ FTType1SeqIndFamily L)
      (hp : characterPairing phi psi = 0)
      {i j : IrreducibleCharacter L ℂ}
      (hi : i ∈ constituents phi) (hj : j ∈ constituents psi) :
      i ≠ j := by
    obtain ⟨V, hV⟩ := seqInd_char H hphi
    obtain ⟨W, hW⟩ := seqInd_char H hpsi
    have hpair' : characterPairing
        (ClassFunction.ofRepresentation V.ρ)
        (ClassFunction.ofRepresentation W.ρ) = 0 := by
      rw [hV, hW]
      exact hp
    have hdis :=
      FTType1InfrastructureInternal.constituentsDisjointOfPairingEqZero
        V W hpair'
    rw [hV, hW] at hdis
    intro hij
    subst j
    exact (Set.disjoint_left.mp hdis) hi hj
  have hdualMemInverse
      {psi : ClassFunction L ℂ} {j : IrreducibleCharacter L ℂ}
      (hj : j ∈ constituents psi) :
      IrreducibleCharacter.dual j ∈
        constituents (ClassFunction.inverseLinear psi) := by
    rw [ClassFunction.mem_constituents_iff] at hj ⊢
    unfold IrreducibleCharacter.IsConstituent at hj ⊢
    rw [← ClassFunction.inverseLinear_irreducible,
      FTType1InfrastructureInternal.pairingInverse]
    exact hj
  have hdistinctDualOfPairingZero
      {phi psi : ClassFunction L ℂ}
      (hphi : phi ∈ FTType1SeqIndFamily L)
      (hpsi : psi ∈ FTType1SeqIndFamily L)
      (hp : characterPairing phi (ClassFunction.inverseLinear psi) = 0)
      {i j : IrreducibleCharacter L ℂ}
      (hi : i ∈ constituents phi) (hj : j ∈ constituents psi) :
      i ≠ IrreducibleCharacter.dual j := by
    exact hdistinctOfPairingZero hphi
      (seqInd_inverse_mem (k := ℂ) H ⊤ ⊥ hpsi) hp hi
      (hdualMemInverse hj)
  have htargetOrthogonal
      {phi psi : ClassFunction L ℂ}
      (hphi : phi ∈ FTType1SeqIndFamily L)
      (hpsi : psi ∈ FTType1SeqIndFamily L)
      (hp : characterPairing phi psi = 0)
      (hpInv : characterPairing phi
        (ClassFunction.inverseLinear psi) = 0)
      {i j : IrreducibleCharacter L ℂ}
      (hi : i ∈ constituents phi) (hj : j ∈ constituents psi)
      {alpha beta : ClassFunction G ℂ}
      (ha : alpha ∈ ctx.R1 (i : ClassFunction L ℂ))
      (hb : beta ∈ ctx.R1 (j : ClassFunction L ℂ)) :
      characterPairing alpha beta = 0 := by
    have hij := hdistinctOfPairingZero hphi hpsi hp hi hj
    have hijDual :=
      hdistinctDualOfPairingZero hphi hpsi hpInv hi hj
    have hpij := IrreducibleCharacter.characterPairing_eq_zero hij
    have hpijDual :=
      IrreducibleCharacter.characterPairing_eq_zero hijDual
    exact hsubI.image_orthogonal
      (j : ClassFunction L ℂ) (hmemI hpsi hj)
      (i : ClassFunction L ℂ) (hmemI hphi hi)
      hpij (by
        simpa only [ClassFunction.inverseLinear_irreducible] using hpijDual)
      alpha ha beta hb
  have htargetDistinct
      {chi : ClassFunction L ℂ}
      (hchi : chi ∈ FTType1SeqIndFamily L)
      {i j : IrreducibleCharacter L ℂ}
      (hi : i ∈ constituents chi) (hj : j ∈ constituents chi)
      (hij : i ≠ j)
      {alpha beta : ClassFunction G ℂ}
      (ha : alpha ∈ ctx.R1 (i : ClassFunction L ℂ))
      (hb : beta ∈ ctx.R1 (j : ClassFunction L ℂ)) :
      characterPairing alpha beta = 0 := by
    have hijDual : i ≠ IrreducibleCharacter.dual j :=
      hdistinctDualOfPairingZero hchi hchi
        (seqInd_conjC_ortho (k := ℂ) H (mFT_odd L) ⊤ ⊥ hchi)
        hi hj
    exact hsubI.image_orthogonal
      (j : ClassFunction L ℂ) (hmemI hchi hj)
      (i : ClassFunction L ℂ) (hmemI hchi hi)
      (IrreducibleCharacter.characterPairing_eq_zero hij)
      (by simpa only [ClassFunction.inverseLinear_irreducible] using
        (IrreducibleCharacter.characterPairing_eq_zero hijDual))
      alpha ha beta hb
  have hRdisjoint
      {chi : ClassFunction L ℂ}
      (hchi : chi ∈ FTType1SeqIndFamily L)
      {i j : IrreducibleCharacter L ℂ}
      (hi : i ∈ constituents chi) (hj : j ∈ constituents chi)
      (hij : i ≠ j) :
      Disjoint (ctx.R1 (i : ClassFunction L ℂ))
        (ctx.R1 (j : ClassFunction L ℂ)) := by
    rw [Finset.disjoint_left]
    intro alpha ha hb
    have hzero := htargetDistinct hchi hi hj hij ha hb
    have hone := hsubI.image_orthonormal
      (i : ClassFunction L ℂ) (hmemI hchi hi) alpha ha alpha ha
    rw [if_pos rfl] at hone
    exact one_ne_zero (hone.symm.trans hzero)
  have hRpairwise {chi : ClassFunction L ℂ}
      (hchi : chi ∈ FTType1SeqIndFamily L) :
      Set.PairwiseDisjoint (↑(constituents chi) :
        Set (IrreducibleCharacter L ℂ))
        (fun i ↦ ctx.R1 (i : ClassFunction L ℂ)) := by
    intro i hi j hj hij
    exact hRdisjoint hchi hi hj hij
  have hisoI := FTtype1_irr_isometry ctx
  have hsubS : subcoherent
      (FTType1SeqIndFamily L : Set (ClassFunction L ℂ)) ctx.tau R := by
    refine
      { finite := (FTType1SeqIndFamily L).finite_toSet
        source_character := ?_
        source_virtual := ?_
        zero_not_mem := ?_
        degree_ne_zero := ?_
        inverse_ne := ?_
        inverse_mem := ?_
        tau_isometry := ?_
        tau_virtual := ?_
        tau_supported := ?_
        pairwise_orthogonal := ?_
        image_virtual := ?_
        image_orthonormal := ?_
        tau_inverse_sub := ?_
        image_orthogonal := ?_ }
    · intro phi hphi
      obtain ⟨V, hV⟩ := seqInd_char H hphi
      refine ⟨VirtualCharacter.ofFDRep V, ?_, ?_⟩
      · intro i
        change 0 ≤ (i.multiplicity V : ℤ)
        exact Int.natCast_nonneg _
      · rw [VirtualCharacter.realize_ofFDRep]
        exact hV
    · intro phi hphi
      exact (show ClassFunction.IsOrdinaryCharacter phi from
        (by
          obtain ⟨V, hV⟩ := seqInd_char H hphi
          refine ⟨VirtualCharacter.ofFDRep V, ?_, ?_⟩
          · intro i
            change 0 ≤ (i.multiplicity V : ℤ)
            exact Int.natCast_nonneg _
          · rw [VirtualCharacter.realize_ofFDRep]
            exact hV)).isVirtual
    · intro hzero
      exact (seqInd_neq0 H hzero) rfl
    · intro phi hphi
      exact seqInd1_neq0 H hphi
    · intro phi hphi
      exact seqInd_conjC_neq (k := ℂ) H (mFT_odd L) ⊤ ⊥ hphi
    · intro phi hphi
      exact seqInd_inverse_mem (k := ℂ) H ⊤ ⊥ hphi
    · intro phi hphi hoff psi hpsi hpsiOff
      exact hisoI.isometry phi (hspanSeq hphi) hoff
        psi (hspanSeq hpsi) hpsiOff
    · intro phi hphi hoff
      exact hisoI.mapsToVirtual phi (hspanSeq hphi) hoff
    · intro phi hphi hoff
      exact hisoI.supported phi (hspanSeq hphi) hoff
    · exact seqInd_orthogonal H
        (Iirr_kerD (k := ℂ) (⊤ : Subgroup H) ⊥)
    · intro chi hchi alpha halpha
      rcases Finset.mem_biUnion.mp halpha with ⟨i, hi, hai⟩
      exact hsubI.image_virtual (i : ClassFunction L ℂ)
        (hmemI hchi hi) alpha hai
    · intro chi hchi alpha halpha beta hbeta
      rcases Finset.mem_biUnion.mp halpha with ⟨i, hi, hai⟩
      rcases Finset.mem_biUnion.mp hbeta with ⟨j, hj, hbj⟩
      by_cases hij : i = j
      · subst j
        exact hsubI.image_orthonormal
          (i : ClassFunction L ℂ) (hmemI hchi hi)
          alpha hai beta hbj
      · rw [if_neg]
        · exact htargetDistinct hchi hi hj hij hai hbj
        · intro hab
          subst beta
          have hzero := htargetDistinct hchi hi hj hij hai hbj
          have hone := hsubI.image_orthonormal
            (i : ClassFunction L ℂ) (hmemI hchi hi)
            alpha hai alpha hai
          rw [if_pos rfl] at hone
          exact one_ne_zero (hone.symm.trans hzero)
    · intro chi hchi
      have hfacts := FTtype1_seqInd_facts ctx chi hchi
      let s := constituents chi
      have hsum : chi = ∑ i ∈ s, (i : ClassFunction L ℂ) := by
        simpa only [s] using hfacts.constituent_sum
      have hinverse : ClassFunction.inverseLinear chi =
          ∑ i ∈ s,
            ClassFunction.inverseLinear (i : ClassFunction L ℂ) := by
        rw [hsum, map_sum]
      have hdifference :
          chi - ClassFunction.inverseLinear chi =
            ∑ i ∈ s, ((i : ClassFunction L ℂ) -
              ClassFunction.inverseLinear (i : ClassFunction L ℂ)) := by
        calc
          chi - ClassFunction.inverseLinear chi =
              (∑ i ∈ s, (i : ClassFunction L ℂ)) -
                ClassFunction.inverseLinear chi :=
            congrArg
              (fun phi : ClassFunction L ℂ ↦
                phi - ClassFunction.inverseLinear chi) hsum
          _ = (∑ i ∈ s, (i : ClassFunction L ℂ)) -
              ∑ i ∈ s,
                ClassFunction.inverseLinear (i : ClassFunction L ℂ) :=
            congrArg
              (fun phi : ClassFunction L ℂ ↦
                (∑ i ∈ s, (i : ClassFunction L ℂ)) - phi) hinverse
          _ = ∑ i ∈ s, ((i : ClassFunction L ℂ) -
              ClassFunction.inverseLinear (i : ClassFunction L ℂ)) := by
            rw [← Finset.sum_sub_distrib]
      calc
        ctx.tau (chi - ClassFunction.inverseLinear chi) =
            ctx.tau (∑ i ∈ constituents chi,
              ((i : ClassFunction L ℂ) -
                ClassFunction.inverseLinear (i : ClassFunction L ℂ))) := by
          simpa only [s] using congrArg ctx.tau hdifference
        _ = ∑ i ∈ constituents chi,
            ctx.tau ((i : ClassFunction L ℂ) -
              ClassFunction.inverseLinear (i : ClassFunction L ℂ)) := by
          rw [map_sum]
        _ = ∑ i ∈ constituents chi,
            ∑ alpha ∈ ctx.R1 (i : ClassFunction L ℂ), alpha := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hsubI.tau_inverse_sub (i : ClassFunction L ℂ)
            (hmemI hchi hi)
        _ = ∑ alpha ∈ R chi, alpha := by
          dsimp only [R]
          rw [Finset.sum_biUnion (hRpairwise hchi)]
    · intro xi hxi phi hphi hp hpInv alpha halpha beta hbeta
      rcases Finset.mem_biUnion.mp halpha with ⟨i, hi, hai⟩
      rcases Finset.mem_biUnion.mp hbeta with ⟨j, hj, hbj⟩
      exact htargetOrthogonal hphi hxi hp hpInv hi hj hai hbj
  exact ⟨R, ⟨hsubS, irreduciblePairFacts ctx, fun _ ↦ rfl⟩⟩

/-! ## Canonical sequential-induction target family -/

namespace FTType1Context

/-- The canonical target family supplied by type-I subcoherence. -/
noncomputable def R {L : Subgroup G} (ctx : FTType1Context L) :
    ClassFunction L ℂ → Finset (ClassFunction G ℂ) :=
  Classical.choose (FTtype1_subcoherent ctx)

/-- The canonical family satisfies Peterfalvi (12.2)(b). -/
theorem R_spec {L : Subgroup G} (ctx : FTType1Context L) :
    FTType1SubcoherentConclusion ctx ctx.R :=
  Classical.choose_spec (FTtype1_subcoherent ctx)

end FTType1Context

end

end Submission.OddOrder.PF
