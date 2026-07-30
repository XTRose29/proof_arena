import Submission.OddOrder.PF.Section10.FTType345SupportNorm

/-!
# Peterfalvi Section 10: bridge coherence

This phase contains the reusable uniqueness argument from the first half of
Peterfalvi (10.5). The source objects and bridge support/norm facts are provided
by `FTType345SupportNorm`.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open scoped BigOperators Classical Pointwise IsMulCommutative
open FTType345ConstantsInternal

variable {Gamma : Type} [Group Gamma] [Fintype Gamma]
variable [IsMinSimpleOddGroup Gamma]
variable {M U W W₁ W₂ : Subgroup Gamma}
variable {defW : IsInternalDirectProductIn W₁ W₂ W}

private theorem ftType345_virtual_of_imageClosure
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    {S₁ : Set (ClassFunction M ℂ)}
    {tau₁ : ClassFunction M ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup Gamma) ℂ}
    (hcoh : coherent_with S₁ (nonidentitySet M)
      (ftType345Tau hmaxM) tau₁)
    {Y : ClassFunction (⊤ : Subgroup Gamma) ℂ}
    (hY : Y ∈ AddSubgroup.closure (tau₁ '' S₁)) :
    ClassFunction.IsVirtual Y := by
  induction hY using AddSubgroup.closure_induction with
  | mem psi hpsi =>
      obtain ⟨phi, hphi, rfl⟩ := hpsi
      exact hcoh.mapsToVirtual phi (AddSubgroup.subset_closure hphi)
  | zero => exact ClassFunction.IsVirtual.zero
  | add a b ha hb iha ihb => exact iha.add ihb
  | neg a ha iha => exact iha.neg

private theorem ftType345_imageClosure_orthogonal_cyclicTI
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    {S₁ : Set (ClassFunction M ℂ)}
    {tau₁ : ClassFunction M ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup Gamma) ℂ}
    (hsub : cfConjC_subset S₁
      (FTtypePKernelLayer (ftType345PrimeDade hmaxM MtypeP)))
    (hirr : ∀ phi ∈ S₁, IsIrreducibleCharacter M ℂ phi)
    (hcoh : coherent_with S₁ (nonidentitySet M)
      (ftType345Tau hmaxM) tau₁)
    {Y : ClassFunction (⊤ : Subgroup Gamma) ℂ}
    (hY : Y ∈ AddSubgroup.closure (tau₁ '' S₁))
    (chi : IrreducibleCharacter W ℂ) :
    characterPairing Y
      ((ftType345IsoG hmaxM MtypeP).linearMap
        (chi : ClassFunction W ℂ)) = 0 := by
  induction hY using AddSubgroup.closure_induction with
  | mem psi hpsi =>
      obtain ⟨phi, hphi, rfl⟩ := hpsi
      exact coherent_ortho_cycTIiso
        (ftType345PrimeDade hmaxM MtypeP)
        (ftType345IsoM MtypeP) (ftType345IsoG hmaxM MtypeP)
        (mFT_odd M) hsub hcoh hphi (hirr phi hphi) chi
  | zero => simp
  | add a b ha hb iha ihb =>
      rw [characterPairing_add_left, iha, ihb, add_zero]
  | neg a ha iha =>
      calc
        characterPairing (-a)
            ((ftType345IsoG hmaxM MtypeP).linearMap
              (chi : ClassFunction W ℂ)) =
            -characterPairing a
              ((ftType345IsoG hmaxM MtypeP).linearMap
                (chi : ClassFunction W ℂ)) := by
          change characterPairingRight
            ((ftType345IsoG hmaxM MtypeP).linearMap
              (chi : ClassFunction W ℂ)) (-a) = _
          exact map_neg _ a
        _ = 0 := by rw [iha, neg_zero]

/-! ## Peterfalvi (10.5): reusable coherence bridge -/

/-- `PFsection10.v: FTtype345_bridge_coherence`, the exported reusable form
of the first half of Peterfalvi (10.5). -/
theorem FTtype345_bridge_coherence
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype2 : FTtype M ≠ 2)
    (zeta : ClassFunction M ℂ)
    (hzeta : FTType345ReferenceChoice M W₁ zeta)
    (S₁ : Set (ClassFunction M ℂ))
    (tau₁ : ClassFunction M ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup Gamma) ℂ)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ)
    (X Y : ClassFunction (⊤ : Subgroup Gamma) ℂ)
    (hcoh : coherent_with S₁ (nonidentitySet M)
      (ftType345Tau hmaxM) tau₁)
    (hdecomp :
      ftType345Tau hmaxM (FTtype345_bridge MtypeP zeta i j) = X + Y)
    (hsub : cfConjC_subset S₁
      (FTtypePKernelLayer (ftType345PrimeDade hmaxM MtypeP)))
    (hirr : ∀ phi ∈ S₁, IsIrreducibleCharacter M ℂ phi)
    (hj : j ≠ IrreducibleCharacter.trivial)
    (hYspan : Y ∈ AddSubgroup.closure (tau₁ '' S₁))
    (hYX : characterPairing Y X = 0)
    (hYnorm : characterPairing Y Y = FTtype345_ratio MtypeP ^ 2) :
    X = (FTtype345_TIsign MtypeP : ℂ) •
      (ftType345Eta hmaxM MtypeP i j -
        ftType345Eta hmaxM MtypeP i
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)) := by
  have hYvirtual : ClassFunction.IsVirtual Y :=
    ftType345_virtual_of_imageClosure hmaxM hcoh hYspan
  have hDadeVirtual :=
    vchar_Dade_FTtype345_bridge hmaxM MtypeP notMtype2
      zeta hzeta i j hj
  have hXeq : X =
      ftType345Tau hmaxM (FTtype345_bridge MtypeP zeta i j) - Y := by
    rw [hdecomp]
    abel
  have hXvirtual : ClassFunction.IsVirtual X := by
    rw [hXeq]
    exact hDadeVirtual.sub hYvirtual
  have hXY : characterPairing X Y = 0 := by
    rw [characterPairing_comm, hYX]
  have hsumNorm : characterPairing (X + Y) (X + Y) =
      characterPairing X X + characterPairing Y Y := by
    rw [characterPairing_add_left, characterPairing_add_right,
      characterPairing_add_right, hXY, hYX]
    ring
  have hXnorm : characterPairing X X = 2 := by
    have hnorm := norm_FTtype345_bridge hmaxM MtypeP notMtype2
      zeta hzeta i j hj
    rw [hdecomp, hsumNorm, hYnorm] at hnorm
    linear_combination hnorm
  obtain ⟨xv, hxv⟩ := hXvirtual
  have hxvNorm : normSq xv = 2 := by
    apply Int.cast_injective (α := ℂ)
    rw [← VirtualCharacter.characterPairing_realize_self, hxv, hXnorm]
    norm_num
  have hYzero : Set.EqOn
      (fun w : W ↦ Y
        ⟨w, (ftType345PrimeDade hmaxM MtypeP).prDade_cycTI.le_group
          w.property⟩)
      0 (cyclicTISetInW W W₁ W₂) := by
    apply (ftType345IsoG hmaxM MtypeP).orthogonal_vanish
    intro chi
    exact ftType345_imageClosure_orthogonal_cyclicTI
      hmaxM MtypeP hsub hirr hcoh hYspan chi
  have heq : Set.EqOn
      (fun w : W ↦ VirtualCharacter.realize xv
        ⟨w, (ftType345PrimeDade hmaxM MtypeP).prDade_cycTI.le_group
          w.property⟩)
      (fun w : W ↦
        ((FTtype345_TIsign MtypeP : ℂ) •
          (ftType345Eta hmaxM MtypeP i j -
            ftType345Eta hmaxM MtypeP i
              (IrreducibleCharacter.trivial :
                IrreducibleCharacter W₂ ℂ)))
          ⟨w, (ftType345PrimeDade hmaxM MtypeP).prDade_cycTI.le_group
            w.property⟩)
      (cyclicTISetInW W W₁ W₂) := by
    intro w hw
    rw [hxv, hXeq]
    simp only [ClassFunction.sub_apply]
    have hYw : Y
        ⟨w, (ftType345PrimeDade hmaxM MtypeP).prDade_cycTI.le_group
          w.property⟩ = 0 := by
      simpa only [Pi.zero_apply] using hYzero hw
    rw [hYw, sub_zero]
    exact FTType345SupportNormInternal.ftType345_Dade_bridge_value_on_cyclicTI
      hmaxM MtypeP notMtype2 zeta hzeta i j hj w hw
  have hsigned :=
    (ftType345IsoG hmaxM MtypeP).eq_signed_sub_cTIiso xv
      (FTtype345_TIsign MtypeP)
      ((ftType345PrimeTI MtypeP).primeTISign_isSign
        (ftType345IsoM MtypeP) (FTtype345_jOne MtypeP))
      i j IrreducibleCharacter.trivial hxvNorm hj heq
  rw [hxv] at hsigned
  exact hsigned

end

end Submission.OddOrder.PF
