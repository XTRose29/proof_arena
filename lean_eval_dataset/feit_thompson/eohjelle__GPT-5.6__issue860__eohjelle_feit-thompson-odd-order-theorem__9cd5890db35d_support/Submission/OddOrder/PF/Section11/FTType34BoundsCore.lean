import Mathlib.Tactic
import Submission.OddOrder.BG.Section15.FittingCoreStructure
import Submission.OddOrder.PF.Section06.BoundedSeqIndCoherence
import Submission.OddOrder.PF.Section08.FTPrimeDadeCoherence
import Submission.OddOrder.PF.Section08.FTSupportPartition
import Submission.OddOrder.PF.Section09.PTypeCoreCoherence
import Submission.OddOrder.PF.Section10.FTType5Exclusion

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section06
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open scoped BigOperators Classical Pointwise IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] [IsMinSimpleOddGroup G]

local instance (priority := 10) ftType34FintypeOfFinite
    (X : Type) [Finite X] : Fintype X :=
  Fintype.ofFinite X

/-! ## Peterfalvi (11.1) -/

private theorem three_pow_dominates_quadratic (n : ℕ) (hn : 5 ≤ n) :
    4 * n ^ 2 + 1 < 3 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      calc
        4 * (n + 1) ^ 2 + 1 < 3 * (4 * n ^ 2 + 1) := by
          nlinarith
        _ ≤ 3 * 3 ^ n := Nat.mul_le_mul_left 3 (Nat.le_of_lt ih)
        _ = 3 ^ (n + 1) := by rw [pow_succ]; omega

/-- `PFsection11.v: lbound_expn_odd_prime`, Peterfalvi (11.1). -/
theorem lbound_expn_odd_prime (p q : ℕ)
    (hpOdd : Odd p) (hqOdd : Odd q)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    4 * q ^ 2 + 1 < p ^ q := by
  have hp3 : 3 ≤ p := (Nat.Prime.odd_iff hp).mp hpOdd
  have hq3 : 3 ≤ q := (Nat.Prime.odd_iff hq).mp hqOdd
  by_cases hqSmall : q < 5
  · have hqEq : q = 3 := by
      obtain ⟨k, hk⟩ := hqOdd
      omega
    subst q
    have hp5 : 5 ≤ p := by
      obtain ⟨k, hk⟩ := hpOdd
      omega
    calc
      4 * 3 ^ 2 + 1 < 5 ^ 3 := by norm_num
      _ ≤ p ^ 3 := Nat.pow_le_pow_left hp5 3
  · have hq5 : 5 ≤ q := by omega
    calc
      4 * q ^ 2 + 1 < 3 ^ q := three_pow_dominates_quadratic q hq5
      _ ≤ p ^ q := Nat.pow_le_pow_left hp3 q

/-! ## The common type-III/IV context -/

/-- Stable input data for Peterfalvi Section 11. -/
structure FTType34Base
    (M U W W₁ W₂ : Subgroup G)
    (defW : IsInternalDirectProductIn W₁ W₂ W) where
  MtypeP : of_typeP M U W W₁ W₂ defW
  notMtype2 : FTtype M ≠ 2
  ptypeCtx : PTypeFCoreContext M U W W₁ W₂

namespace FTType34Base

variable {M U W W₁ W₂ : Subgroup G}
variable {defW : IsInternalDirectProductIn W₁ W₂ W}

abbrev maxM (base : FTType34Base M U W W₁ W₂ defW) :
    M ∈ minSimple_max_groups (G := G) :=
  base.ptypeCtx.maxM

abbrev primeTI (base : FTType34Base M U W W₁ W₂ defW) :
    PrimeTIHypothesis M (derivedWithin M) W W₁ W₂ defW :=
  FT_primeTI_hyp defW base.MtypeP

noncomputable abbrev isoM
    (base : FTType34Base M U W W₁ W₂ defW) :
    CyclicTIIsometryData (k := ℂ) base.primeTI.prime_cycTIhyp :=
  base.primeTI.prime_cycTIhyp.cyclicTIIsometryData

noncomputable abbrev primeDade
    (base : FTType34Base M U W W₁ W₂ defW) :
    PrimeDadeHypothesis (⊤ : Subgroup G) M (derivedWithin M) (FTcore M)
      (FTsupport M) (FTsupport0 M) W W₁ W₂ defW :=
  FT_prDade_hyp defW base.maxM base.MtypeP

noncomputable abbrev isoG
    (base : FTType34Base M U W W₁ W₂ defW) :
    CyclicTIIsometryData (k := ℂ) base.primeDade.prDade_cycTI :=
  base.primeDade.prDade_cycTI.cyclicTIIsometryData

noncomputable abbrev targetMap
    (_base : FTType34Base M U W W₁ W₂ defW) :
    ClassFunction (⊤ : Subgroup G) ℂ →ₗ[ℂ] ClassFunction G ℂ :=
  ClassFunction.comap Subgroup.topEquiv.symm.toMonoidHom

theorem targetMap_injective
    (base : FTType34Base M U W W₁ W₂ defW) :
    Function.Injective base.targetMap :=
  ClassFunction.comap_injective _ Subgroup.topEquiv.symm.surjective

noncomputable abbrev tau
    (base : FTType34Base M U W W₁ W₂ defW) :
    ClassFunction M ℂ →ₗ[ℂ] ClassFunction G ℂ :=
  base.targetMap.comp (Dade (FT_Dade0_hyp M base.maxM))

noncomputable def R
    (base : FTType34Base M U W W₁ W₂ defW)
    (phi : ClassFunction M ℂ) : Finset (ClassFunction G ℂ) :=
  (FTtypeP_coh_base base.primeDade base.isoM base.isoG (mFT_odd M) phi).map
    ⟨base.targetMap, base.targetMap_injective⟩

noncomputable abbrev sourceMap
    (_base : FTType34Base M U W W₁ W₂ defW) :
    ClassFunction G ℂ →ₗ[ℂ] ClassFunction (⊤ : Subgroup G) ℂ :=
  ClassFunction.comap Subgroup.topEquiv.toMonoidHom

@[simp]
theorem sourceMap_targetMap
    (base : FTType34Base M U W W₁ W₂ defW)
    (phi : ClassFunction (⊤ : Subgroup G) ℂ) :
    base.sourceMap (base.targetMap phi) = phi := by
  ext x
  simpa [ClassFunction.comap_apply] using
    congrArg phi (Subgroup.topEquiv.symm_apply_apply x)

@[simp]
theorem targetMap_sourceMap
    (base : FTType34Base M U W W₁ W₂ defW)
    (phi : ClassFunction G ℂ) :
    base.targetMap (base.sourceMap phi) = phi := by
  ext x
  simpa [ClassFunction.comap_apply] using
    congrArg phi (Subgroup.topEquiv.apply_symm_apply x)

theorem targetMap_pairing
    (base : FTType34Base M U W W₁ W₂ defW)
    (phi psi : ClassFunction (⊤ : Subgroup G) ℂ) :
    characterPairing (base.targetMap phi) (base.targetMap psi) =
      characterPairing phi psi := by
  have hcard : Nat.card G = Nat.card (⊤ : Subgroup G) :=
    Nat.card_congr Subgroup.topEquiv.symm.toEquiv
  unfold characterPairing
  rw [hcard]
  congr 1
  apply Fintype.sum_equiv Subgroup.topEquiv.symm.toEquiv
  intro x
  simp [ClassFunction.comap_apply]

theorem sourceMap_pairing
    (base : FTType34Base M U W W₁ W₂ defW)
    (phi psi : ClassFunction G ℂ) :
    characterPairing (base.sourceMap phi) (base.sourceMap psi) =
      characterPairing phi psi := by
  rw [← base.targetMap_pairing (base.sourceMap phi) (base.sourceMap psi)]
  simp

theorem targetMap_virtual
    (base : FTType34Base M U W W₁ W₂ defW)
    {phi : ClassFunction (⊤ : Subgroup G) ℂ}
    (hphi : ClassFunction.IsVirtual phi) :
    ClassFunction.IsVirtual (base.targetMap phi) := by
  obtain ⟨z, hz⟩ := hphi
  refine ⟨VirtualCharacter.comap
    Subgroup.topEquiv.symm.toMonoidHom z, by
      rw [VirtualCharacter.realize_comap, hz]⟩

theorem sourceMap_virtual
    (base : FTType34Base M U W W₁ W₂ defW)
    {phi : ClassFunction G ℂ}
    (hphi : ClassFunction.IsVirtual phi) :
    ClassFunction.IsVirtual (base.sourceMap phi) := by
  obtain ⟨z, hz⟩ := hphi
  refine ⟨VirtualCharacter.comap Subgroup.topEquiv.toMonoidHom z, by
    rw [VirtualCharacter.realize_comap, hz]⟩

theorem targetMap_supported
    (base : FTType34Base M U W W₁ W₂ defW)
    {phi : ClassFunction (⊤ : Subgroup G) ℂ}
    (hphi : phi ∈ ClassFunction.supportedOn
      (nonidentitySet (⊤ : Subgroup G))) :
    base.targetMap phi ∈ ClassFunction.supportedOn (nonidentitySet G) := by
  rw [ClassFunction.mem_supportedOn_iff] at hphi ⊢
  intro x hx
  have hxOne : x = 1 := by
    simpa [nonidentitySet] using not_not.mp hx
  subst x
  simpa [ClassFunction.comap_apply] using
    hphi (1 : (⊤ : Subgroup G)) (by simp [nonidentitySet])

theorem coherent_targetMap_iff
    (base : FTType34Base M U W W₁ W₂ defW)
    {S : Set (ClassFunction M ℂ)} {A : Set M}
    {sigma : ClassFunction M ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup G) ℂ} :
    coherent S A (base.targetMap.comp sigma) ↔ coherent S A sigma := by
  constructor
  · rintro ⟨nu, hnu⟩
    refine ⟨base.sourceMap.comp nu, ?_⟩
    exact
      { isometry := by
          intro phi hphi psi hpsi
          simpa [LinearMap.comp_apply] using
            (base.sourceMap_pairing (nu phi) (nu psi)).trans
              (hnu.isometry phi hphi psi hpsi)
        mapsToVirtual := by
          intro phi hphi
          exact base.sourceMap_virtual (hnu.mapsToVirtual phi hphi)
        agrees := by
          intro phi hphi hsupp
          have hagree := hnu.agrees phi hphi hsupp
          simpa [LinearMap.comp_apply, hagree] }
  · rintro ⟨nu, hnu⟩
    refine ⟨base.targetMap.comp nu, ?_⟩
    exact
      { isometry := by
          intro phi hphi psi hpsi
          simpa [LinearMap.comp_apply] using
            (base.targetMap_pairing (nu phi) (nu psi)).trans
              (hnu.isometry phi hphi psi hpsi)
        mapsToVirtual := by
          intro phi hphi
          exact base.targetMap_virtual (hnu.mapsToVirtual phi hphi)
        agrees := by
          intro phi hphi hsupp
          simpa [LinearMap.comp_apply, hnu.agrees phi hphi hsupp] }

abbrev notMtype5 (base : FTType34Base M U W W₁ W₂ defW) :
    FTtype M ≠ 5 :=
  base.ptypeCtx.not_type5

abbrev H (_base : FTType34Base M U W W₁ W₂ defW) : Subgroup G :=
  Fitting_core M

abbrev HU (_base : FTType34Base M U W W₁ W₂ defW) : Subgroup G :=
  derivedWithin M

abbrev U' (_base : FTType34Base M U W W₁ W₂ defW) : Subgroup G :=
  derivedWithin U

abbrev H0 (base : FTType34Base M U W W₁ W₂ defW) : Subgroup G :=
  Ptype_Fcore_kernel base.ptypeCtx

abbrev C (base : FTType34Base M U W W₁ W₂ defW) : Subgroup G :=
  centralizerWithin U base.H

abbrev HC (base : FTType34Base M U W W₁ W₂ defW) : Subgroup G :=
  base.H ⊔ base.C

abbrev H0C (base : FTType34Base M U W W₁ W₂ defW) : Subgroup G :=
  base.H0 ⊔ base.C

abbrev p (_base : FTType34Base M U W W₁ W₂ defW) : ℕ :=
  Nat.card W₂

abbrev q (_base : FTType34Base M U W W₁ W₂ defW) : ℕ :=
  Nat.card W₁

abbrev CInU (base : FTType34Base M U W W₁ W₂ defW) : Subgroup U :=
  base.C.subgroupOf U

abbrev u (base : FTType34Base M U W W₁ W₂ defW) : ℕ :=
  base.CInU.index

abbrev HUInM (base : FTType34Base M U W W₁ W₂ defW) : Subgroup M :=
  base.HU.subgroupOf M

abbrev subgroupInHU
    (base : FTType34Base M U W W₁ W₂ defW) (A : Subgroup G) :
    Subgroup base.HUInM :=
  (A.subgroupOf M).subgroupOf base.HUInM

abbrev HInHU (base : FTType34Base M U W W₁ W₂ defW) :
    Subgroup base.HUInM := base.subgroupInHU base.H

abbrev H0InHU (base : FTType34Base M U W W₁ W₂ defW) :
    Subgroup base.HUInM := base.subgroupInHU base.H0

abbrev UInHU (base : FTType34Base M U W W₁ W₂ defW) :
    Subgroup base.HUInM := base.subgroupInHU U

abbrev CInHU (base : FTType34Base M U W W₁ W₂ defW) :
    Subgroup base.HUInM := base.subgroupInHU base.C

abbrev HCInHU (base : FTType34Base M U W W₁ W₂ defW) :
    Subgroup base.HUInM := base.subgroupInHU base.HC

abbrev H0CInHU (base : FTType34Base M U W W₁ W₂ defW) :
    Subgroup base.HUInM := base.subgroupInHU base.H0C

abbrev W₁InM (_base : FTType34Base M U W W₁ W₂ defW) : Subgroup M :=
  W₁.subgroupOf M

abbrev W₂InM (_base : FTType34Base M U W W₁ W₂ defW) : Subgroup M :=
  W₂.subgroupOf M

theorem derived_complement_decomposition
    (base : FTType34Base M U W W₁ W₂ defW) :
    IsInternalSemidirectProductIn base.HU W₁ M :=
  base.MtypeP.1.2.2.2

theorem fcore_complement_decomposition
    (base : FTType34Base M U W W₁ W₂ defW) :
    IsInternalSemidirectProductIn base.H U base.HU :=
  base.MtypeP.2.1.2.2.2

theorem HU_le_M (base : FTType34Base M U W W₁ W₂ defW) :
    base.HU ≤ M :=
  base.derived_complement_decomposition.1

theorem H_le_HU (base : FTType34Base M U W W₁ W₂ defW) :
    base.H ≤ base.HU :=
  base.fcore_complement_decomposition.1

theorem U_le_HU (base : FTType34Base M U W W₁ W₂ defW) :
    U ≤ base.HU :=
  base.fcore_complement_decomposition.2.1

theorem H0_lt_H (base : FTType34Base M U W W₁ W₂ defW) :
    base.H0 < base.H :=
  Ptype_Fcore_kernel_lt base.ptypeCtx

theorem H0_le_H (base : FTType34Base M U W W₁ W₂ defW) :
    base.H0 ≤ base.H :=
  base.H0_lt_H.le

theorem C_le_U (base : FTType34Base M U W W₁ W₂ defW) :
    base.C ≤ U :=
  centralizerWithin_le_left U base.H

theorem C_le_HU (base : FTType34Base M U W W₁ W₂ defW) :
    base.C ≤ base.HU :=
  base.C_le_U.trans base.U_le_HU

theorem HC_le_HU (base : FTType34Base M U W W₁ W₂ defW) :
    base.HC ≤ base.HU :=
  sup_le base.H_le_HU base.C_le_HU

theorem H0C_le_HU (base : FTType34Base M U W W₁ W₂ defW) :
    base.H0C ≤ base.HU :=
  sup_le (base.H0_le_H.trans base.H_le_HU) base.C_le_HU

theorem H0C_le_HC (base : FTType34Base M U W W₁ W₂ defW) :
    base.H0C ≤ base.HC :=
  sup_le (base.H0_le_H.trans le_sup_left) le_sup_right

theorem q_prime (base : FTType34Base M U W W₁ W₂ defW) :
    base.q.Prime :=
  (compl_of_typeII_IV M U W W₁ W₂ defW base.maxM
    base.MtypeP base.notMtype5).2.2.1

theorem p_prime (base : FTType34Base M U W W₁ W₂ defW) :
    base.p.Prime := by
  have hcore := typeII_IV_core base.ptypeCtx
  rw [TypeIIIVCoreConclusion, if_neg base.notMtype2] at hcore
  exact hcore.1

theorem p_odd (base : FTType34Base M U W W₁ W₂ defW) : Odd base.p :=
  mFT_odd W₂

theorem q_odd (base : FTType34Base M U W W₁ W₂ defW) : Odd base.q :=
  mFT_odd W₁

theorem notMtype1 (base : FTType34Base M U W W₁ W₂ defW) :
    FTtype M ≠ 1 :=
  FTtypeP_neq1 M U W W₁ W₂ defW base.maxM base.MtypeP

theorem type_eq_three_or_four
    (base : FTType34Base M U W W₁ W₂ defW) :
    FTtype M = 3 ∨ FTtype M = 4 := by
  have hrange := FTtype_range M
  have hnot1 := base.notMtype1
  have hnot2 := base.notMtype2
  have hnot5 := base.notMtype5
  omega

theorem type_gt_two (base : FTType34Base M U W W₁ W₂ defW) :
    2 < FTtype M := by
  rcases base.type_eq_three_or_four with h | h <;> omega

theorem FTcore_eq_HU (base : FTType34Base M U W W₁ W₂ defW) :
    FTcore M = base.HU :=
  FTcore_type_gt2 M base.type_gt_two

end FTType34Base

/-! ## Character layers -/

variable {M U W W₁ W₂ : Subgroup G}
variable {defW : IsInternalDirectProductIn W₁ W₂ W}

def ftType34Layer
    (base : FTType34Base M U W W₁ W₂ defW)
    (Y : Subgroup base.HUInM) : Finset (ClassFunction M ℂ) :=
  seqIndD (k := ℂ) base.HUInM ⊤ Y

def ftType34S1
    (base : FTType34Base M U W W₁ W₂ defW) :
    Finset (ClassFunction M ℂ) :=
  ftType34Layer base base.HCInHU

def ftType34S2
    (base : FTType34Base M U W W₁ W₂ defW) :
    Finset (ClassFunction M ℂ) :=
  seqIndD (k := ℂ) base.HUInM base.HCInHU base.CInHU

def ftType34Bridge0
    (muZero zeta : ClassFunction M ℂ) : ClassFunction M ℂ :=
  muZero - zeta

def ftType34Coherent
    (base : FTType34Base M U W W₁ W₂ defW)
    (Y : Subgroup base.HUInM) : Prop :=
  coherent (↑(ftType34Layer base Y) : Set (ClassFunction M ℂ))
    (nonidentitySet M) base.tau

private theorem ftType34_kernelLayer_subcoherent
    (base : FTType34Base M U W W₁ W₂ defW) :
    subcoherent (FTtypePKernelLayer base.primeDade) base.tau base.R := by
  let R₀ := FTtypeP_coh_base base.primeDade base.isoM base.isoG (mFT_odd M)
  have hsub := FTtypeP_subcoherent
    base.primeDade base.isoM base.isoG (mFT_odd M)
  exact
    { finite := hsub.finite
      source_character := hsub.source_character
      source_virtual := hsub.source_virtual
      zero_not_mem := hsub.zero_not_mem
      degree_ne_zero := hsub.degree_ne_zero
      inverse_ne := hsub.inverse_ne
      inverse_mem := hsub.inverse_mem
      tau_isometry := by
        intro phi hphi hphiOff psi hpsi hpsiOff
        change characterPairing
            (base.targetMap (Dade base.primeDade.prDade_hyp phi))
            (base.targetMap (Dade base.primeDade.prDade_hyp psi)) = _
        rw [base.targetMap_pairing]
        exact hsub.tau_isometry phi hphi hphiOff psi hpsi hpsiOff
      tau_virtual := by
        intro phi hphi hphiOff
        exact base.targetMap_virtual (hsub.tau_virtual phi hphi hphiOff)
      tau_supported := by
        intro phi hphi hphiOff
        exact base.targetMap_supported (hsub.tau_supported phi hphi hphiOff)
      pairwise_orthogonal := hsub.pairwise_orthogonal
      image_virtual := by
        intro xi hxi alpha halpha
        rw [FTType34Base.R] at halpha
        rcases Finset.mem_map.mp halpha with ⟨beta, hbeta, rfl⟩
        exact base.targetMap_virtual (hsub.image_virtual xi hxi beta hbeta)
      image_orthonormal := by
        intro xi hxi alpha halpha beta hbeta
        rw [FTType34Base.R] at halpha hbeta
        rcases Finset.mem_map.mp halpha with ⟨alpha₀, halpha₀, rfl⟩
        rcases Finset.mem_map.mp hbeta with ⟨beta₀, hbeta₀, rfl⟩
        change characterPairing (base.targetMap alpha₀)
          (base.targetMap beta₀) = _
        rw [base.targetMap_pairing]
        simpa only [EmbeddingLike.apply_eq_iff_eq] using
          hsub.image_orthonormal xi hxi alpha₀ halpha₀ beta₀ hbeta₀
      tau_inverse_sub := by
        intro xi hxi
        change base.targetMap
            (Dade base.primeDade.prDade_hyp
              (xi - ClassFunction.inverseLinear xi)) = _
        rw [hsub.tau_inverse_sub xi hxi]
        simp [FTType34Base.R, R₀, Finset.sum_map]
      image_orthogonal := by
        intro xi hxi phi hphi hpair hpairInv alpha halpha beta hbeta
        rw [FTType34Base.R] at halpha hbeta
        rcases Finset.mem_map.mp halpha with ⟨alpha₀, halpha₀, rfl⟩
        rcases Finset.mem_map.mp hbeta with ⟨beta₀, hbeta₀, rfl⟩
        change characterPairing (base.targetMap alpha₀)
          (base.targetMap beta₀) = 0
        rw [base.targetMap_pairing]
        exact hsub.image_orthogonal xi hxi phi hphi hpair hpairInv
          alpha₀ halpha₀ beta₀ hbeta₀ }

private theorem ftType34_bottom_subcoherent
    (base : FTType34Base M U W W₁ W₂ defW) :
    subcoherent
      (↑(ftType34Layer base ⊥) : Set (ClassFunction M ℂ))
      base.tau base.R := by
  simpa [FTtypePKernelLayer, PrimeDadeHypothesis.signalizerInKernel,
    ftType34Layer, base.FTcore_eq_HU] using
      ftType34_kernelLayer_subcoherent base

/-! ## Fresh subgroup and cardinality adapters -/

private theorem semidirect_sup_eq34
    {A B K : Subgroup G} (h : IsInternalSemidirectProductIn A B K) :
    A ⊔ B = K := by
  apply le_antisymm (sup_le h.1 h.2.1)
  intro x hx
  obtain ⟨⟨a, b⟩, hab⟩ := h.2.2.2.2 ⟨x, hx⟩
  have habG : (a : G) * (b : G) = x := congrArg Subtype.val hab
  rw [← habG]
  exact Subgroup.mul_mem_sup a.property b.property

private theorem directProduct_sup_eq34
    {A B K : Subgroup G} (h : IsInternalDirectProductIn A B K) :
    A ⊔ B = K := by
  apply le_antisymm (sup_le h.left_le h.right_le)
  intro x hx
  obtain ⟨⟨a, b⟩, hab⟩ := h.complement.2 ⟨x, hx⟩
  have habG : (a : G) * (b : G) = x := congrArg Subtype.val hab
  rw [← habG]
  exact Subgroup.mul_mem_sup a.property b.property

private theorem directProduct_disjoint34
    {A B K : Subgroup G} (h : IsInternalDirectProductIn A B K) :
    Disjoint A B := by
  rw [disjoint_iff]
  apply eq_bot_iff.mpr
  intro y hy
  let yK : K := ⟨y, h.left_le hy.1⟩
  let yA : A.subgroupOf K := ⟨yK, hy.1⟩
  let yB : B.subgroupOf K := ⟨yK, hy.2⟩
  have hpairs : (yA, (1 : B.subgroupOf K)) =
      ((1 : A.subgroupOf K), yB) := by
    apply h.complement.1
    apply Subtype.ext
    simp [yA, yB, yK]
  have hyOne : yA = 1 := congrArg Prod.fst hpairs
  apply Subgroup.mem_bot.mpr
  simpa [yA, yK] using
    congrArg (fun z : A.subgroupOf K ↦ (z : G)) hyOne

private theorem subgroupOf_disjoint34
    {A B K : Subgroup G} (hAK : A ≤ K) (hBK : B ≤ K)
    (hdis : Disjoint A B) :
    Disjoint (A.subgroupOf K) (B.subgroupOf K) := by
  rw [disjoint_iff]
  apply eq_bot_iff.mpr
  intro x hx
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  apply Subgroup.mem_bot.mp
  rw [← disjoint_iff.mp hdis]
  exact hx

private theorem directProduct_restrict_left34
    {A₀ A B K : Subgroup G} (h : IsInternalDirectProductIn A B K)
    (hA₀A : A₀ ≤ A) :
    IsInternalDirectProductIn A₀ B (A₀ ⊔ B) := by
  have hdis : Disjoint A₀ B :=
    (directProduct_disjoint34 h).mono hA₀A le_rfl
  have hnorm : A₀ ≤ Subgroup.normalizer (B : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha b hb
    let aA : A := ⟨a, hA₀A ha⟩
    let bB : B := ⟨b, hb⟩
    have hcomm := h.commute aA bB
    have hab : a * b = b * a := by
      change a * b = b * a at hcomm
      exact hcomm
    have heq : a * b * a⁻¹ = b := by
      calc
        a * b * a⁻¹ = b * a * a⁻¹ := by rw [hab]
        _ = b := by simp
    rw [heq]
    exact hb
  exact
    { left_le := le_sup_left
      right_le := le_sup_right
      complement := by
        apply Subgroup.isComplement'_of_card_mul_and_disjoint
        · have hcard :=
            natCard_sup_eq_mul_of_disjoint_of_le_normalizer hdis hnorm
          simpa only [MathlibSupport.natCard_subgroupOf_eq le_sup_left,
            MathlibSupport.natCard_subgroupOf_eq le_sup_right] using
              hcard.symm
        · exact subgroupOf_disjoint34 le_sup_left le_sup_right hdis
      commute := by
        intro a b
        exact h.commute ⟨a, hA₀A a.property⟩ b }

private theorem subgroupInHU_mono34
    (base : FTType34Base M U W W₁ W₂ defW)
    {A B : Subgroup G} (hAB : A ≤ B) :
    base.subgroupInHU A ≤ base.subgroupInHU B :=
  Subgroup.subgroupOf_mono base.HUInM (Subgroup.subgroupOf_mono M hAB)

private theorem subgroupInHU_lt_top34
    (base : FTType34Base M U W W₁ W₂ defW)
    {A : Subgroup G} (hA : A < base.HU) :
    base.subgroupInHU A < ⊤ := by
  refine lt_of_le_of_ne le_top ?_
  intro htop
  have hleNested : base.HUInM ≤ A.subgroupOf M :=
    Subgroup.subgroupOf_eq_top.mp htop
  have hle : base.HU ≤ A := by
    intro x hx
    have hxM : x ∈ M := base.HU_le_M hx
    have hxNested : (⟨x, hxM⟩ : M) ∈ base.HUInM := hx
    exact hleNested hxNested
  exact (not_le_of_gt hA) hle

private theorem subgroupInHU_index_eq_relIndex34
    (base : FTType34Base M U W W₁ W₂ defW)
    (A : Subgroup G) :
    (base.subgroupInHU A).index = A.relIndex base.HU := by
  change (A.subgroupOf M).relIndex (base.HU.subgroupOf M) = _
  exact Subgroup.relIndex_subgroupOf (H := A) base.HU_le_M

private theorem map_subgroupInHU_eq34
    (base : FTType34Base M U W W₁ W₂ defW)
    (A : Subgroup G) (hAHU : A ≤ base.HU) :
    (base.subgroupInHU A).map base.HUInM.subtype = A.subgroupOf M := by
  simpa [FTType34Base.subgroupInHU, FTType34Base.HUInM,
    Subgroup.map_map] using
      Subgroup.map_subgroupOf_eq_of_le
        (Subgroup.subgroupOf_mono M hAHU)

private noncomputable def subgroupInHU_equiv34
    (base : FTType34Base M U W W₁ W₂ defW)
    (A : Subgroup G) (hAHU : A ≤ base.HU) :
    base.subgroupInHU A ≃* A :=
  (Subgroup.subgroupOfEquivOfLe
      (Subgroup.subgroupOf_mono M hAHU)).trans
    (Subgroup.subgroupOfEquivOfLe (hAHU.trans base.HU_le_M))

private theorem derivedWithin_normal34 (M : Subgroup G) :
    ((derivedWithin M).subgroupOf M).Normal := by
  unfold derivedWithin
  rw [M.map_subtype_commutator]
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.commutator_le_self M)).2
  exact Subgroup.normalizer_commutator_ge_left M M

private theorem centralizerWithin_normalized34
    {A B C : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G))
    (hAC : A ≤ Subgroup.normalizer (C : Set G)) :
    A ≤ Subgroup.normalizer (centralizerWithin B C : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro a ha x hx
  refine ⟨(Subgroup.mem_normalizer_iff.mp (hAB ha) x).mp hx.1, ?_⟩
  intro c hc
  have haInvC : a⁻¹ ∈ Subgroup.normalizer (C : Set G) :=
    (Subgroup.normalizer (C : Set G)).inv_mem (hAC ha)
  have hc' : a⁻¹ * c * a ∈ C := by
    simpa only [inv_inv] using
      (Subgroup.mem_normalizer_iff.mp haInvC c).mp hc
  have hcomm := hx.2 (a⁻¹ * c * a) hc'
  calc
    c * (a * x * a⁻¹) = a * ((a⁻¹ * c * a) * x) * a⁻¹ := by group
    _ = a * (x * (a⁻¹ * c * a)) * a⁻¹ := by rw [hcomm]
    _ = (a * x * a⁻¹) * c := by group

/-! ## Group and index calculations -/

private theorem ftType34_p_ne_q
    (base : FTType34Base M U W W₁ W₂ defW) :
    base.p ≠ base.q := by
  intro hpq
  have hcop := base.primeTI.factor_card_coprime
  have hqOne : base.q = 1 := by
    change Nat.Coprime base.q base.p at hcop
    rw [hpq] at hcop
    exact (Nat.coprime_self base.q).mp hcop
  exact base.q_prime.ne_one hqOne

private noncomputable abbrev ftType34FactorFacts
    (base : FTType34Base M U W W₁ W₂ defW) :
    PTypeFCoreFactorFacts base.ptypeCtx :=
  Ptype_Fcore_factor_facts base.ptypeCtx

private theorem ftType34_factorPrime_eq_p
    (base : FTType34Base M U W W₁ W₂ defW) :
    ptypeFactorPrime base.ptypeCtx = base.p :=
  typeIII_IV_core_prime base.ptypeCtx base.notMtype2

private theorem ftType34_factor_card
    (base : FTType34Base M U W W₁ W₂ defW) :
    Nat.card (ptypeFCoreFactor base.ptypeCtx) = base.p ^ base.q := by
  rw [(ftType34FactorFacts base).factor_card,
    ftType34_factorPrime_eq_p base]

private theorem ftType34_factor_elementary
    (base : FTType34Base M U W W₁ W₂ defW) :
    IsElementaryAbelianGroup base.p (ptypeFCoreFactor base.ptypeCtx) := by
  simpa only [ftType34_factorPrime_eq_p base] using
    ptypeFCoreFactor_elementary base.ptypeCtx

private theorem ftType34_HC_eq_fittingWithin
    (base : FTType34Base M U W W₁ W₂ defW) :
    base.HC = fittingWithin M :=
  directProduct_sup_eq34
    (typeP_context M U W W₁ W₂ defW base.MtypeP).fitting_decomposition

private theorem ftType34_HC_direct
    (base : FTType34Base M U W W₁ W₂ defW) :
    IsInternalDirectProductIn base.H base.C base.HC := by
  have h :=
    (typeP_context M U W W₁ W₂ defW base.MtypeP).fitting_decomposition
  simpa only [directProduct_sup_eq34 h] using h

private theorem ftType34_H0C_direct
    (base : FTType34Base M U W W₁ W₂ defW) :
    IsInternalDirectProductIn base.H0 base.C base.H0C :=
  directProduct_restrict_left34 (ftType34_HC_direct base) base.H0_le_H

private theorem ftType34_C_normal_M
    (base : FTType34Base M U W W₁ W₂ defW) :
    PTypeNormalIn base.C M := by
  have hMnormH : M ≤ Subgroup.normalizer (base.H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Fcore_sub M)).mp
      (Fcore_normal M)
  have hUnormC : U ≤ Subgroup.normalizer (base.C : Set G) :=
    centralizerWithin_normalized34 Subgroup.le_normalizer
      ((base.U_le_HU.trans base.HU_le_M).trans hMnormH)
  have hHcentC : base.H ≤ Subgroup.centralizer (base.C : Set G) := by
    intro h hh
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (hc.2 h hh).symm
  have hHnormC : base.H ≤ Subgroup.normalizer (base.C : Set G) :=
    hHcentC.trans (Subgroup.centralizer_le_normalizer (base.C : Set G))
  have hW₁normC : W₁ ≤ Subgroup.normalizer (base.C : Set G) :=
    centralizerWithin_normalized34 base.MtypeP.2.1.2.2.1
      (base.MtypeP.1.2.1.1.trans hMnormH)
  have hMnormC : M ≤ Subgroup.normalizer (base.C : Set G) := by
    calc
      M = base.HU ⊔ W₁ :=
        (semidirect_sup_eq34
          base.derived_complement_decomposition).symm
      _ = (base.H ⊔ U) ⊔ W₁ := by
        rw [semidirect_sup_eq34 base.fcore_complement_decomposition]
      _ ≤ Subgroup.normalizer (base.C : Set G) :=
        sup_le (sup_le hHnormC hUnormC) hW₁normC
  have hCM : base.C ≤ M := base.C_le_HU.trans base.HU_le_M
  exact ⟨hCM,
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCM).mpr hMnormC⟩

private theorem normal_sup_in_ambient34
    {A B : Subgroup G} (hA : PTypeNormalIn A M)
    (hB : PTypeNormalIn B M) :
    PTypeNormalIn (A ⊔ B) M := by
  refine ⟨sup_le hA.1 hB.1, ?_⟩
  letI : (A.subgroupOf M).Normal := hA.2
  letI : (B.subgroupOf M).Normal := hB.2
  rw [Subgroup.subgroupOf_sup hA.1 hB.1]
  infer_instance

private theorem ftType34_HC_normal_M
    (base : FTType34Base M U W W₁ W₂ defW) :
    PTypeNormalIn base.HC M :=
  normal_sup_in_ambient34 ⟨Fcore_sub M, Fcore_normal M⟩
    (ftType34_C_normal_M base)

private theorem ftType34_H0C_normal_M
    (base : FTType34Base M U W W₁ W₂ defW) :
    PTypeNormalIn base.H0C M :=
  normal_sup_in_ambient34
    ⟨Ptype_Fcore_kernel_le_M base.ptypeCtx,
      Ptype_Fcore_kernel_normal_M base.ptypeCtx⟩
    (ftType34_C_normal_M base)

private theorem ftType34_map_subgroupInHU_normal
    (base : FTType34Base M U W W₁ W₂ defW)
    {A : Subgroup G} (hA : PTypeNormalIn A M) (hAHU : A ≤ base.HU) :
    ((base.subgroupInHU A).map base.HUInM.subtype : Subgroup M).Normal := by
  rw [map_subgroupInHU_eq34 base A hAHU]
  exact hA.2

private theorem ftType34_HU_index
    (base : FTType34Base M U W W₁ W₂ defW) :
    base.HUInM.index = base.q := by
  calc
    base.HUInM.index = Nat.card (W₁.subgroupOf M) :=
      base.derived_complement_decomposition.2.2.2.symm.index_eq_card
    _ = Nat.card W₁ := MathlibSupport.natCard_subgroupOf_eq
      base.derived_complement_decomposition.2.1
    _ = base.q := rfl

private theorem relIndex_mul_card34
    {A B : Subgroup G} (hAB : A ≤ B) :
    A.relIndex B * Nat.card A = Nat.card B := by
  change (A.subgroupOf B).index * Nat.card A = Nat.card B
  simpa only [MathlibSupport.natCard_subgroupOf_eq hAB] using
    (A.subgroupOf B).index_mul_card

private theorem directProduct_card34
    {A B K : Subgroup G} (h : IsInternalDirectProductIn A B K) :
    Nat.card A * Nat.card B = Nat.card K := by
  simpa only [MathlibSupport.natCard_subgroupOf_eq h.left_le,
    MathlibSupport.natCard_subgroupOf_eq h.right_le] using
      h.complement.card_mul

private theorem semidirectProduct_card34
    {A B K : Subgroup G} (h : IsInternalSemidirectProductIn A B K) :
    Nat.card A * Nat.card B = Nat.card K := by
  simpa only [MathlibSupport.natCard_subgroupOf_eq h.1,
    MathlibSupport.natCard_subgroupOf_eq h.2.1] using
      h.2.2.2.card_mul

private theorem ftType34_H0C_HC_relIndex
    (base : FTType34Base M U W W₁ W₂ defW) :
    base.H0CInHU.relIndex base.HCInHU = base.p ^ base.q := by
  have hHC := ftType34_HC_direct base
  have hH0C := ftType34_H0C_direct base
  have hrelAmbient : base.H0C.relIndex base.HC =
      base.H0.relIndex base.H := by
    apply Nat.mul_right_cancel
      (Nat.mul_pos
        (show 0 < Nat.card base.H0 from Nat.card_pos)
        (show 0 < Nat.card base.C from Nat.card_pos))
    calc
      base.H0C.relIndex base.HC *
          (Nat.card base.H0 * Nat.card base.C) =
          base.H0C.relIndex base.HC * Nat.card base.H0C := by
            rw [directProduct_card34 hH0C]
      _ = Nat.card base.HC := relIndex_mul_card34 base.H0C_le_HC
      _ = Nat.card base.H * Nat.card base.C :=
        (directProduct_card34 hHC).symm
      _ = (base.H0.relIndex base.H * Nat.card base.H0) *
          Nat.card base.C := by rw [relIndex_mul_card34 base.H0_le_H]
      _ = base.H0.relIndex base.H *
          (Nat.card base.H0 * Nat.card base.C) := by ac_rfl
  have hHCsub : base.HC.subgroupOf M ≤ base.HUInM :=
    Subgroup.subgroupOf_mono M base.HC_le_HU
  calc
    base.H0CInHU.relIndex base.HCInHU =
        (base.H0C.subgroupOf M).relIndex (base.HC.subgroupOf M) := by
      simpa [FTType34Base.H0CInHU, FTType34Base.HCInHU,
        FTType34Base.subgroupInHU] using
          (Subgroup.relIndex_subgroupOf
            (H := base.H0C.subgroupOf M) hHCsub)
    _ = base.H0C.relIndex base.HC := by
      simpa using Subgroup.relIndex_subgroupOf
        (H := base.H0C) (base.HC_le_HU.trans base.HU_le_M)
    _ = base.H0.relIndex base.H := hrelAmbient
    _ = Nat.card (ptypeFCoreFactor base.ptypeCtx) := rfl
    _ = base.p ^ base.q := ftType34_factor_card base

set_option synthInstance.maxHeartbeats 100000 in
private theorem ftType34_HC_quotient_abelian
    (base : FTType34Base M U W W₁ W₂ defW)
    [(base.H0CInHU.subgroupOf base.HCInHU).Normal] :
    IsMulCommutative
      (base.HCInHU ⧸ base.H0CInHU.subgroupOf base.HCInHU) := by
  letI : ((base.H0CInHU.map base.HUInM.subtype : Subgroup M)).Normal :=
    ftType34_map_subgroupInHU_normal base
      (ftType34_H0C_normal_M base) base.H0C_le_HU
  letI : base.H0CInHU.Normal :=
    Subgroup.Normal.of_map_subtype
      (inferInstance :
        ((base.H0CInHU.map base.HUInM.subtype : Subgroup M)).Normal)
  letI : (base.H0.subgroupOf base.H).Normal :=
    Ptype_Fcore_kernel_normal_Fcore base.ptypeCtx
  have hHcommAmbient : _root_.commutator base.H ≤
      base.H0.subgroupOf base.H :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
      (ftType34_factor_elementary base).commutative
  have hHH0 : ⁅base.HInHU, base.HInHU⁆ ≤ base.H0InHU := by
    apply Subgroup.commutator_le.mpr
    intro x hx y hy
    let xH : base.H :=
      ⟨(((x : base.HUInM) : M) : G), hx⟩
    let yH : base.H :=
      ⟨(((y : base.HUInM) : M) : G), hy⟩
    have hxy : ⁅xH, yH⁆ ∈ _root_.commutator base.H := by
      change ⁅xH, yH⁆ ∈ ⁅(⊤ : Subgroup base.H), ⊤⁆
      exact Subgroup.commutator_mem_commutator
        (Subgroup.mem_top xH) (Subgroup.mem_top yH)
    have hout := hHcommAmbient hxy
    change ⁅(((x : base.HUInM) : M) : G),
      (((y : base.HUInM) : M) : G)⁆ ∈ base.H0
    change ⁅(xH : G), (yH : G)⁆ ∈ base.H0 at hout
    exact hout
  have hHH : ⁅base.HInHU, base.HInHU⁆ ≤ base.H0CInHU :=
    hHH0.trans (subgroupInHU_mono34 base le_sup_left)
  have hHC : ⁅base.HInHU, base.CInHU⁆ ≤ base.H0CInHU := by
    apply Subgroup.commutator_le.mpr
    intro h hh c hc
    change ⁅(((h : base.HUInM) : M) : G),
      (((c : base.HUInM) : M) : G)⁆ ∈ base.H0C
    have hcommOne :
        ⁅(((h : base.HUInM) : M) : G),
          (((c : base.HUInM) : M) : G)⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hc.2 _ hh)
    rw [hcommOne]
    exact base.H0C.one_mem
  have hCH : ⁅base.CInHU, base.HInHU⁆ ≤ base.H0CInHU := by
    rw [Subgroup.commutator_comm]
    exact hHC
  have hCC : ⁅base.CInHU, base.CInHU⁆ ≤ base.H0CInHU :=
    (Subgroup.commutator_le_self base.CInHU).trans
      (subgroupInHU_mono34 base le_sup_right)
  have hHsup : ⁅base.HInHU, base.HInHU ⊔ base.CInHU⁆ ≤
      base.H0CInHU :=
    commutator_sup_le_of_normal hHH hHC
  have hCsup : ⁅base.CInHU, base.HInHU ⊔ base.CInHU⁆ ≤
      base.H0CInHU :=
    commutator_sup_le_of_normal hCH hCC
  have hsupH : ⁅base.HInHU ⊔ base.CInHU, base.HInHU⁆ ≤
      base.H0CInHU := by
    rw [Subgroup.commutator_comm]
    exact hHsup
  have hsupC : ⁅base.HInHU ⊔ base.CInHU, base.CInHU⁆ ≤
      base.H0CInHU := by
    rw [Subgroup.commutator_comm]
    exact hCsup
  have hHCeq : base.HCInHU = base.HInHU ⊔ base.CInHU := by
    change ((base.H ⊔ base.C).subgroupOf M).subgroupOf base.HUInM =
      (base.H.subgroupOf M).subgroupOf base.HUInM ⊔
        (base.C.subgroupOf M).subgroupOf base.HUInM
    rw [Subgroup.subgroupOf_sup
      (base.H_le_HU.trans base.HU_le_M)
      (base.C_le_HU.trans base.HU_le_M)]
    rw [Subgroup.subgroupOf_sup
      (Subgroup.subgroupOf_mono M base.H_le_HU)
      (Subgroup.subgroupOf_mono M base.C_le_HU)]
  apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
  intro z hz
  change (z : base.HUInM) ∈ base.H0CInHU
  have hzAmbient : (z : base.HUInM) ∈
      ⁅base.HCInHU, base.HCInHU⁆ := by
    rw [← base.HCInHU.map_subtype_commutator]
    exact ⟨z, hz, rfl⟩
  have hcommEq : ⁅base.HCInHU, base.HCInHU⁆ =
      ⁅base.HInHU ⊔ base.CInHU,
        base.HInHU ⊔ base.CInHU⁆ :=
    congrArg (fun S : Subgroup base.HUInM ↦ ⁅S, S⁆) hHCeq
  have hzSup : (z : base.HUInM) ∈
      ⁅base.HInHU ⊔ base.CInHU,
        base.HInHU ⊔ base.CInHU⁆ :=
    hcommEq ▸ hzAmbient
  exact (commutator_sup_le_of_normal hsupH hsupC) hzSup

private theorem ftType34_HC_index
    (base : FTType34Base M U W W₁ W₂ defW) :
    (base.HCInHU.map base.HUInM.subtype : Subgroup M).index =
      base.q * base.u := by
  have hHCcard := directProduct_card34 (ftType34_HC_direct base)
  have hHUcard :=
    semidirectProduct_card34 base.fcore_complement_decomposition
  have huCard : base.u * Nat.card base.C = Nat.card U := by
    change base.CInU.index * Nat.card base.C = Nat.card U
    simpa only [MathlibSupport.natCard_subgroupOf_eq base.C_le_U] using
      base.CInU.index_mul_card
  have hrel : base.HC.relIndex base.HU = base.u := by
    apply Nat.mul_right_cancel
      (Nat.mul_pos
        (show 0 < Nat.card base.H from Nat.card_pos)
        (show 0 < Nat.card base.C from Nat.card_pos))
    calc
      base.HC.relIndex base.HU *
          (Nat.card base.H * Nat.card base.C) =
          base.HC.relIndex base.HU * Nat.card base.HC := by rw [hHCcard]
      _ = Nat.card base.HU := relIndex_mul_card34 base.HC_le_HU
      _ = Nat.card base.H * Nat.card U := hHUcard.symm
      _ = Nat.card base.H * (base.u * Nat.card base.C) := by rw [huCard]
      _ = base.u * (Nat.card base.H * Nat.card base.C) := by ac_rfl
  rw [map_subgroupInHU_eq34 base base.HC base.HC_le_HU]
  calc
    (base.HC.subgroupOf M).index =
        (base.HC.subgroupOf M).relIndex base.HUInM *
          base.HUInM.index :=
      (Subgroup.relIndex_mul_index
        (Subgroup.subgroupOf_mono M base.HC_le_HU)).symm
    _ = base.HC.relIndex base.HU * base.HUInM.index := by
      rw [Subgroup.relIndex_subgroupOf base.HU_le_M]
    _ = base.u * base.q := by rw [hrel, ftType34_HU_index base]
    _ = base.q * base.u := Nat.mul_comm _ _

private theorem ftType34_HC_mod_bot_nilpotent
    (base : FTType34Base M U W W₁ W₂ defW)
    [((⊥ : Subgroup base.HUInM).subgroupOf base.HCInHU).Normal] :
    Group.IsNilpotent
      (base.HCInHU ⧸
        (⊥ : Subgroup base.HUInM).subgroupOf base.HCInHU) := by
  have hnilHC : Group.IsNilpotent base.HC := by
    rw [ftType34_HC_eq_fittingWithin base]
    infer_instance
  letI : Group.IsNilpotent base.HC := hnilHC
  letI : Group.IsNilpotent base.HCInHU :=
    Group.nilpotent_of_mulEquiv
      (subgroupInHU_equiv34 base base.HC base.HC_le_HU).symm
  infer_instance

/-! ## Peterfalvi (11.3)--(11.4) -/

/-- `PFsection11.v: FTtype34_noncoherence`, Peterfalvi (11.3). -/
theorem FTtype34_noncoherence
    (base : FTType34Base M U W W₁ W₂ defW) :
    ¬ ftType34Coherent base base.H0CInHU := by
  intro hcohH0C
  letI : IsSolvable M := mmax_sol base.maxM
  letI : base.HUInM.Normal := derivedWithin_normal34 M
  letI : ((base.H0CInHU.map base.HUInM.subtype : Subgroup M)).Normal :=
    ftType34_map_subgroupInHU_normal base
      (ftType34_H0C_normal_M base) base.H0C_le_HU
  letI : ((base.HCInHU.map base.HUInM.subtype : Subgroup M)).Normal :=
    ftType34_map_subgroupInHU_normal base
      (ftType34_HC_normal_M base) base.HC_le_HU
  letI : (((⊥ : Subgroup base.HUInM).map
      base.HUInM.subtype : Subgroup M)).Normal := by simp
  letI : ((⊥ : Subgroup base.HUInM).subgroupOf base.HCInHU).Normal := by
    rw [Subgroup.bot_subgroupOf]
    infer_instance
  have hbottom : ftType34Coherent base ⊥ := by
    apply bounded_seqIndD_coherence base.HUInM base.tau base.R
      (ftType34_bottom_subcoherent base) ⊥ base.H0CInHU base.HCInHU
    · exact bot_le
    · exact subgroupInHU_mono34 base base.H0C_le_HC
    · exact ftType34_HC_mod_bot_nilpotent base
    · exact hcohH0C
    · rw [ftType34_HU_index base, ftType34_H0C_HC_relIndex base]
      exact lbound_expn_odd_prime base.p base.q base.p_odd base.q_odd
        base.p_prime base.q_prime (ftType34_p_ne_q base)
  have hsource :=
    (base.coherent_targetMap_iff
      (S := (↑(ftType34Layer base ⊥) : Set (ClassFunction M ℂ)))
      (A := nonidentitySet M)
      (sigma := Dade (FT_Dade0_hyp M base.maxM))).mp hbottom
  exact (FTtype345_noncoherence M base.maxM base.type_gt_two) (by
    simpa [ftType34Layer,
      FTType345ConstantsInternal.ftType345InducedFamily10] using hsource)

/-- `PFsection11.v: bounded_proper_coherent`, Peterfalvi (11.4). -/
theorem bounded_proper_coherent
    (base : FTType34Base M U W W₁ W₂ defW)
    (H₁ : Subgroup G)
    (hH₁normal : PTypeNormalIn H₁ M)
    (hH₁proper : H₁ < base.HU)
    (hcoh : ftType34Coherent base (base.subgroupInHU H₁)) :
    H₁.relIndex base.HU ≤ 2 * base.q * base.u + 1 := by
  letI : IsSolvable M := mmax_sol base.maxM
  letI : base.HUInM.Normal := derivedWithin_normal34 M
  letI : (((base.subgroupInHU H₁).map
      base.HUInM.subtype : Subgroup M)).Normal :=
    ftType34_map_subgroupInHU_normal base hH₁normal hH₁proper.le
  letI : ((base.H0CInHU.map base.HUInM.subtype : Subgroup M)).Normal :=
    ftType34_map_subgroupInHU_normal base
      (ftType34_H0C_normal_M base) base.H0C_le_HU
  letI : ((base.HCInHU.map base.HUInM.subtype : Subgroup M)).Normal :=
    ftType34_map_subgroupInHU_normal base
      (ftType34_HC_normal_M base) base.HC_le_HU
  letI : base.H0CInHU.Normal :=
    Subgroup.Normal.of_map_subtype
      (inferInstance :
        ((base.H0CInHU.map base.HUInM.subtype : Subgroup M)).Normal)
  letI : base.HCInHU.Normal :=
    Subgroup.Normal.of_map_subtype
      (inferInstance :
        ((base.HCInHU.map base.HUInM.subtype : Subgroup M)).Normal)
  letI : (base.H0CInHU.subgroupOf base.HCInHU).Normal :=
    Subgroup.Normal.subgroupOf
      (inferInstance : base.H0CInHU.Normal) base.HCInHU
  have hcenter :
      (base.HCInHU.subgroupOf base.HCInHU).map
          (QuotientGroup.mk'
            (base.H0CInHU.subgroupOf base.HCInHU)) ≤
        Subgroup.center
          (base.HCInHU ⧸ base.H0CInHU.subgroupOf base.HCInHU) := by
    rw [Subgroup.center_eq_top_iff.mpr
      (ftType34_HC_quotient_abelian base)]
    exact le_top
  rcases coherent_seqIndD_bound
      (L := M) (G := G)
      base.HUInM base.tau base.R
      (ftType34_bottom_subcoherent base)
      (base.subgroupInHU H₁) base.H0CInHU base.HCInHU base.HCInHU
      (subgroupInHU_lt_top34 base hH₁proper)
      (subgroupInHU_mono34 base base.H0C_le_HC) le_rfl hcenter hcoh with
    hbad | hbound
  · exact (FTtype34_noncoherence base hbad).elim
  · have hAindex : (base.subgroupInHU H₁).index =
        H₁.relIndex base.HU := subgroupInHU_index_eq_relIndex34 base H₁
    rw [hAindex, ftType34_HC_index base,
      Subgroup.subgroupOf_self, Subgroup.index_top,
      Nat.cast_one, Real.sqrt_one, mul_one] at hbound
    have hreal : (H₁.relIndex base.HU : ℝ) ≤
        ((2 * base.q * base.u + 1 : ℕ) : ℝ) := by
      norm_num [Nat.cast_add, Nat.cast_mul] at hbound ⊢
      nlinarith
    exact_mod_cast hreal


private theorem secondDerivedInM_eq_commutator_map34
    (M : Subgroup G) :
    (secondDerivedWithin M).subgroupOf M =
      (_root_.commutator ((derivedWithin M).subgroupOf M)).map
        ((derivedWithin M).subgroupOf M).subtype := by
  have hderM : derivedWithin M ≤ M :=
    TypeSpecInternal.derivedWithin_le16_final M
  change (derivedWithin (derivedWithin M)).subgroupOf M =
    (_root_.commutator ((derivedWithin M).subgroupOf M)).map
      ((derivedWithin M).subgroupOf M).subtype
  rw [show derivedWithin (derivedWithin M) =
      ⁅derivedWithin M, derivedWithin M⁆ by
    exact (derivedWithin M).map_subtype_commutator]
  rw [subgroupOf_commutator_eq hderM hderM]
  exact ((derivedWithin M).subgroupOf M).map_subtype_commutator.symm

private instance ftType34DerivedInM_normal34
    (M : Subgroup G) : ((derivedWithin M).subgroupOf M).Normal :=
  TypeSpecInternal.derivedWithin_normal16 M

private instance ftType34SecondDerivedInM_normal34
    (M : Subgroup G) :
    ((secondDerivedWithin M).subgroupOf M).Normal := by
  let K : Subgroup M := (derivedWithin M).subgroupOf M
  letI : K.Normal := ftType34DerivedInM_normal34 M
  rw [secondDerivedInM_eq_commutator_map34 M]
  infer_instance

private theorem subgroupOf_lt34
    {A B K : Subgroup G} (hBK : B ≤ K) (hAB : A < B) :
    A.subgroupOf K < B.subgroupOf K := by
  refine ⟨Subgroup.subgroupOf_mono K hAB.le, ?_⟩
  intro hBA
  apply (not_le_of_gt hAB)
  intro b hb
  let bK : K := ⟨b, hBK hb⟩
  have hbA : bK ∈ A.subgroupOf K := hBA hb
  exact hbA

private theorem ftType34_secondDerived_normal_M
    (base : FTType34Base M U W W₁ W₂ defW) :
    PTypeNormalIn (secondDerivedWithin M) M := by
  refine ⟨(Subgroup.map_subtype_le
    (_root_.commutator base.HU)).trans base.HU_le_M, ?_⟩
  exact ftType34SecondDerivedInM_normal34 M

private theorem ftType34_secondDerived_le_HC
    (base : FTType34Base M U W W₁ W₂ defW) :
    secondDerivedWithin M ≤ base.HC := by
  rw [ftType34_HC_eq_fittingWithin base]
  exact base.MtypeP.2.2.1.2.1

private theorem ftType34_secondDerived_coherent
    (base : FTType34Base M U W W₁ W₂ defW) :
    ftType34Coherent base (base.subgroupInHU (secondDerivedWithin M)) := by
  let H1 : Subgroup base.HUInM :=
    base.subgroupInHU (secondDerivedWithin M)
  have hNleHU : secondDerivedWithin M ≤ base.HU :=
    Subgroup.map_subtype_le (_root_.commutator base.HU)
  letI : ((H1.map base.HUInM.subtype : Subgroup M)).Normal := by
    dsimp only [H1]
    rw [map_subgroupInHU_eq34 base (secondDerivedWithin M) hNleHU]
    exact ftType34SecondDerivedInM_normal34 M
  have hclosed := seqInd_conjC_subset1 (k := ℂ) base.HUInM
    (⊤ : Subgroup base.HUInM) (⊤ : Subgroup base.HUInM) H1 le_rfl
  have hsub := subset_subcoherent
    (ftType34_bottom_subcoherent base) hclosed
  apply uniform_degree_coherence hsub
  intro phi hphi psi hpsi
  change phi ∈ seqIndD (k := ℂ) base.HUInM ⊤ H1 at hphi
  change psi ∈ seqIndD (k := ℂ) base.HUInM ⊤ H1 at hpsi
  obtain ⟨chi, hchi, rfl⟩ := seqIndP.mp hphi
  obtain ⟨eta, heta, rfl⟩ := seqIndP.mp hpsi
  have hcomm : _root_.commutator base.HUInM ≤ H1 := by
    intro x hx
    change (x : M) ∈ (secondDerivedWithin M).subgroupOf M
    rw [secondDerivedInM_eq_commutator_map34 M]
    exact ⟨x, hx, rfl⟩
  have hchiDer : _root_.commutator base.HUInM ≤
      ClassFunction.translationKernel (chi : ClassFunction base.HUInM ℂ) :=
    hcomm.trans (mem_Iirr_kerD.mp hchi).1
  have hetaDer : _root_.commutator base.HUInM ≤
      ClassFunction.translationKernel (eta : ClassFunction base.HUInM ℂ) :=
    hcomm.trans (mem_Iirr_kerD.mp heta).1
  have hchiOne : chi 1 = 1 :=
    internal.pTypeLinear_apply_one chi
      (PTypeCoreContextInternal.pTypeCore_linear_of_commutator_le_kernel
        chi hchiDer)
  have hetaOne : eta 1 = 1 :=
    internal.pTypeLinear_apply_one eta
      (PTypeCoreContextInternal.pTypeCore_linear_of_commutator_le_kernel
        eta hetaDer)
  rw [ClassFunction.induce_one, ClassFunction.induce_one,
    hchiOne, hetaOne]

private theorem ftType34_HC_HU_relIndex
    (base : FTType34Base M U W W₁ W₂ defW) :
    base.HC.relIndex base.HU = base.u := by
  have hHCcard := directProduct_card34 (ftType34_HC_direct base)
  have hHUcard :=
    semidirectProduct_card34 base.fcore_complement_decomposition
  have huCard : base.u * Nat.card base.C = Nat.card U := by
    change base.CInU.index * Nat.card base.C = Nat.card U
    simpa only [MathlibSupport.natCard_subgroupOf_eq base.C_le_U] using
      base.CInU.index_mul_card
  apply Nat.mul_right_cancel
    (Nat.mul_pos
      (show 0 < Nat.card base.H from Nat.card_pos)
      (show 0 < Nat.card base.C from Nat.card_pos))
  calc
    base.HC.relIndex base.HU *
        (Nat.card base.H * Nat.card base.C) =
        base.HC.relIndex base.HU * Nat.card base.HC := by rw [hHCcard]
    _ = Nat.card base.HU := relIndex_mul_card34 base.HC_le_HU
    _ = Nat.card base.H * Nat.card U := hHUcard.symm
    _ = Nat.card base.H * (base.u * Nat.card base.C) := by rw [huCard]
    _ = base.u * (Nat.card base.H * Nat.card base.C) := by ac_rfl

private theorem ftType34_u_gt_one
    (base : FTType34Base M U W W₁ W₂ defW) :
    1 < base.u := by
  have hUne : U ≠ ⊥ :=
    (compl_of_typeII_IV M U W W₁ W₂ defW base.maxM
      base.MtypeP base.notMtype5).2.1
  have hnotCentral :
      ¬ U ≤ Subgroup.centralizer (base.H : Set G) :=
    (typeP_context M U W W₁ W₂ defW
      base.MtypeP).nontrivial_not_le_centralizer hUne
  have hCneU : base.C ≠ U := by
    intro hCU
    apply hnotCentral
    intro u hu
    have huC : u ∈ base.C := hCU.symm ▸ hu
    exact huC.2
  have hCInUne : base.CInU ≠ ⊤ := by
    intro htop
    apply hCneU
    exact le_antisymm base.C_le_U
      (Subgroup.subgroupOf_eq_top.mp htop)
  exact Subgroup.one_lt_index_of_ne_top hCInUne

private theorem ftType34_secondDerived_small
    (base : FTType34Base M U W W₁ W₂ defW)
    (hproper : secondDerivedWithin M < base.HC) :
    (secondDerivedWithin M).relIndex base.HC < 2 * base.q + 1 := by
  have hbound := bounded_proper_coherent base (secondDerivedWithin M)
    (ftType34_secondDerived_normal_M base)
    (hproper.trans_le base.HC_le_HU)
    (ftType34_secondDerived_coherent base)
  have htower :=
    Subgroup.relIndex_mul_relIndex (secondDerivedWithin M) base.HC base.HU
      hproper.le base.HC_le_HU
  rw [ftType34_HC_HU_relIndex base] at htower
  nlinarith [ftType34_u_gt_one base]

private theorem relIndex_eq_card_map_quotient34
    {Q : Type*} [Group Q] [Finite Q]
    {N H : Subgroup Q} (hNnormal : N.Normal) (hNH : N ≤ H) :
    N.relIndex H = Nat.card (H.map (QuotientGroup.mk' N)) := by
  letI : N.Normal := hNnormal
  let q : Q →* Q ⧸ N := QuotientGroup.mk' N
  let f : H →* Q ⧸ N := q.comp H.subtype
  have hker : f.ker = N.subgroupOf H := by
    ext x
    change q (x : Q) = 1 ↔ (x : Q) ∈ N
    exact QuotientGroup.eq_one_iff (x : Q)
  have hrange : f.range = H.map q := by
    dsimp [f]
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  calc
    N.relIndex H = (N.subgroupOf H).index := rfl
    _ = f.ker.index := congrArg Subgroup.index hker.symm
    _ = Nat.card f.range := Subgroup.index_ker f
    _ = Nat.card (H.map q) :=
      Nat.card_congr (MulEquiv.subgroupCongr hrange).toEquiv

/-- Restrict a Frobenius kernel to a nontrivial ambient-normal subkernel. -/
private theorem frobenius_subkernel34
    {Q : Type*} [Group Q] [Finite Q]
    {K R A : Subgroup Q}
    (hfrob : IsFrobeniusDecomposition K R)
    (hAK : A ≤ K) (hAnormal : A.Normal) (hAne : A ≠ ⊥) :
    IsFrobeniusDecomposition
      (A.subgroupOf (R ⊔ A))
      (R.subgroupOf (R ⊔ A)) := by
  let J : Subgroup Q := R ⊔ A
  let AJ : Subgroup J := A.subgroupOf J
  let RJ : Subgroup J := R.subgroupOf J
  letI : A.Normal := hAnormal
  have hRnormA : R ≤ Subgroup.normalizer (A : Set Q) := by
    rw [A.normalizer_eq_top]
    exact le_top
  have hcomp : AJ.IsComplement' RJ := by
    simpa only [J, AJ, RJ] using
      properKernel_subgroupOf_isComplement
        hfrob.isComplement hAK hRnormA
  have hAJnormal : AJ.Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : A.Normal) J
  have hAJne : AJ ≠ ⊥ := by
    intro hbot
    apply hAne
    apply le_antisymm _ bot_le
    intro a ha
    let aJ : J := ⟨a, (show A ≤ J from le_sup_right) ha⟩
    have haAJ : aJ ∈ AJ := ha
    rw [hbot] at haAJ
    exact Subgroup.mem_bot.mpr
      (congrArg Subtype.val (Subgroup.mem_bot.mp haAJ))
  have hRJne : RJ ≠ ⊥ := by
    intro hbot
    apply hfrob.complement_ne_bot
    apply le_antisymm _ bot_le
    intro r hr
    let rJ : J := ⟨r, (show R ≤ J from le_sup_left) hr⟩
    have hrRJ : rJ ∈ RJ := hr
    rw [hbot] at hrRJ
    exact Subgroup.mem_bot.mpr
      (congrArg Subtype.val (Subgroup.mem_bot.mp hrRJ))
  refine
    { isComplement := hcomp
      kernel_normal := hAJnormal
      kernel_ne_bot := hAJne
      complement_ne_bot := hRJne
      fixedPointFree := ?_ }
  intro r hr k hk
  let rQ : R := ⟨((r : J) : Q), r.property⟩
  let kQ : K := ⟨((k : J) : Q), hAK k.property⟩
  have hrQ : rQ ≠ 1 := by
    intro hrOne
    apply hr
    apply Subtype.ext
    exact Subtype.ext (congrArg (fun x : R ↦ (x : Q)) hrOne)
  have hkQ :
      (rQ : Q) * (kQ : Q) * (rQ : Q)⁻¹ = (kQ : Q) := by
    exact congrArg (fun x : J ↦ (x : Q)) hk
  have hkOne := hfrob.fixedPointFree rQ hrQ kQ hkQ
  apply Subtype.ext
  exact Subtype.ext (congrArg (fun x : K ↦ (x : Q)) hkOne)

/-- Numerical form of the odd Frobenius estimate for the restricted kernel. -/
private theorem two_complement_card_le_subkernel_card_sub_one34
    {Q : Type*} [Group Q] [Fintype Q]
    {K R A : Subgroup Q}
    (hoddQ : Odd (Nat.card Q))
    (hfrob : IsFrobeniusDecomposition K R)
    (hAK : A ≤ K) (hAnormal : A.Normal) (hAne : A ≠ ⊥) :
    2 * Nat.card R ≤ Nat.card A - 1 := by
  let J : Subgroup Q := R ⊔ A
  let AJ : Subgroup J := A.subgroupOf J
  let RJ : Subgroup J := R.subgroupOf J
  have hfrobA : IsFrobeniusDecomposition AJ RJ := by
    simpa only [J, AJ, RJ] using
      frobenius_subkernel34 hfrob hAK hAnormal hAne
  have hoddJ : Odd (Nat.card J) :=
    Odd.of_dvd_nat hoddQ
      (by
        simpa only [Subgroup.card_top] using
          Subgroup.card_dvd_of_le
            (show J ≤ (⊤ : Subgroup Q) from le_top))
  have hbound := odd_Frobenius_index_ler AJ RJ hoddJ hfrobA
  have hindex : AJ.index = Nat.card R := by
    calc
      AJ.index = Nat.card RJ :=
        hfrobA.isComplement.symm.index_eq_card
      _ = Nat.card R :=
        MathlibSupport.natCard_subgroupOf_eq
          (show R ≤ J from le_sup_left)
  have hcardA : Nat.card AJ = Nat.card A :=
    MathlibSupport.natCard_subgroupOf_eq
      (show A ≤ J from le_sup_right)
  rw [hindex, hcardA] at hbound
  have hreal :
      (2 * Nat.card R : ℝ) ≤ ((Nat.card A - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (Nat.card_pos (α := A))]
    have htwice :
        (2 : ℝ) * (Nat.card R : ℝ) ≤
          (Nat.card A : ℝ) - 1 := by
      nlinarith [hbound]
    norm_num [Nat.cast_mul] at htwice ⊢
    exact htwice
  exact_mod_cast hreal

private theorem primeTI_centralizerWithin_subgroupOf_zpowers34
    {L K W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (h : PrimeTIHypothesis L K W W₁ W₂ defW)
    (x : L) (hxW₁ : x ∈ W₁.subgroupOf L) (hx : x ≠ 1) :
    centralizerWithin (K.subgroupOf L) (Subgroup.zpowers x) =
      W₂.subgroupOf L := by
  let x₁ : W₁ := ⟨(x : G), hxW₁⟩
  have hx₁ : x₁ ≠ 1 := by
    intro hx₁one
    apply hx
    apply Subtype.ext
    simpa only [x₁, Subgroup.coe_one] using
      congrArg Subtype.val hx₁one
  have hcent := h.centralizer_kernel x₁ hx₁
  ext z
  constructor
  · intro hz
    have hzG :
        (z : G) ∈
          centralizerWithin K (Subgroup.zpowers (x : G)) := by
      refine ⟨hz.1, ?_⟩
      intro y hy
      have hyMap : y ∈ (Subgroup.zpowers x).map L.subtype := by
        rwa [MonoidHom.map_zpowers]
      rcases hyMap with ⟨yL, hyL, rfl⟩
      exact congrArg Subtype.val (hz.2 yL hyL)
    rw [hcent] at hzG
    exact hzG
  · intro hz
    have hzG :
        (z : G) ∈
          centralizerWithin K (Subgroup.zpowers (x : G)) := by
      rw [hcent]
      exact hz
    refine ⟨hzG.1, ?_⟩
    intro y hy
    apply Subtype.ext
    apply hzG.2 (y : G)
    change (y : G) ∈ Subgroup.zpowers (L.subtype x)
    rw [← MonoidHom.map_zpowers]
    exact Subgroup.mem_map_of_mem L.subtype hy

private theorem primeTI_frobenius_quotient_of_fixed_le34
    {L K W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (h : PrimeTIHypothesis L K W W₁ W₂ defW)
    (D : Subgroup L) [D.Normal]
    (hDK : D < K.subgroupOf L)
    (hW₂D : W₂.subgroupOf L ≤ D) :
    IsFrobeniusDecomposition
      ((K.subgroupOf L).map (QuotientGroup.mk' D))
      ((W₁.subgroupOf L).map (QuotientGroup.mk' D)) := by
  classical
  let KL : Subgroup L := K.subgroupOf L
  let RL : Subgroup L := W₁.subgroupOf L
  let q : L →* L ⧸ D := QuotientGroup.mk' D
  let Kq : Subgroup (L ⧸ D) := KL.map q
  let Rq : Subgroup (L ⧸ D) := RL.map q
  letI : KL.Normal := h.kernel_normal
  letI : Kq.Normal :=
    Subgroup.Normal.map (inferInstance : KL.Normal) q
      (QuotientGroup.mk'_surjective D)
  have hDleK : D ≤ KL := hDK.le
  have hcomp : Kq.IsComplement' Rq := by
    simpa only [Kq, Rq, KL, RL, q] using
      h.semidirect_complement.quotient_isComplement hDleK
  have hKqne : Kq ≠ ⊥ := by
    simpa only [Kq, KL, q] using
      (IsFrobeniusDecomposition.quotient_kernel_ne_bot hDK)
  have hRLne : RL ≠ ⊥ := by
    intro hbot
    apply h.complement_ne_bot
    apply le_bot_iff.mp
    intro r hr
    let rL : L := ⟨r, h.complement_le_group hr⟩
    have hrL : rL ∈ RL := hr
    rw [hbot] at hrL
    exact Subgroup.mem_bot.mpr
      (congrArg Subtype.val (Subgroup.mem_bot.mp hrL))
  have hRqne : Rq ≠ ⊥ := by
    simpa only [Rq, RL, q] using
      h.semidirect_complement.quotient_right_ne_bot hDleK hRLne
  have hfixed : ∀ r : Rq, r ≠ 1 → ∀ k : Kq,
      (r : L ⧸ D) * (k : L ⧸ D) * (r : L ⧸ D)⁻¹ =
        (k : L ⧸ D) → k = 1 := by
    intro r hr k hk
    rcases r.property with ⟨r₀, hr₀, hrEq⟩
    let rL : RL := ⟨r₀, hr₀⟩
    have hrLne : rL ≠ 1 := by
      intro hrOne
      apply hr
      apply Subtype.ext
      rw [← hrEq]
      have hr₀one : r₀ = 1 := congrArg Subtype.val hrOne
      rw [hr₀one, map_one]
      rfl
    have hcentL :
        centralizerWithin KL (Subgroup.zpowers (rL : L)) =
          W₂.subgroupOf L := by
      have hrLne' : (rL : L) ≠ 1 := by
        intro hrOne
        exact hrLne (Subtype.ext hrOne)
      simpa only [KL, RL] using
        primeTI_centralizerWithin_subgroupOf_zpowers34 h
          (rL : L) rL.property hrLne'
    let Rr : Subgroup L := Subgroup.zpowers (rL : L)
    letI : IsSolvable Rr := inferInstance
    have hRrRL : Rr ≤ RL := by
      intro x hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact RL.zpow_mem rL.property n
    have hcopKL : Nat.Coprime (Nat.card KL) (Nat.card RL) := by
      simpa only [KL, RL,
        MathlibSupport.natCard_subgroupOf_eq h.kernel_le_group,
        MathlibSupport.natCard_subgroupOf_eq h.complement_le_group] using
          h.kernel_complement_card_coprime
    have hcopDRr : Nat.Coprime (Nat.card D) (Nat.card Rr) :=
      (hcopKL.coprime_dvd_left
          (Subgroup.card_dvd_of_le hDleK)).coprime_dvd_right
        (Subgroup.card_dvd_of_le hRrRL)
    have hcentMap :=
      map_centralizerWithin_quotient_eq_of_coprime_of_solvable_right
        (N := D) (Y := KL) (R := Rr) hDleK hcopDRr
    have hcentBot :
        centralizerWithin Kq (Subgroup.zpowers (r : L ⧸ D)) = ⊥ := by
      calc
        centralizerWithin Kq (Subgroup.zpowers (r : L ⧸ D)) =
            centralizerWithin Kq (Rr.map q) := by
          dsimp only [Rr]
          rw [MonoidHom.map_zpowers, hrEq]
        _ = (centralizerWithin KL Rr).map q := hcentMap.symm
        _ = (W₂.subgroupOf L).map q := by rw [hcentL]
        _ = ⊥ := by
          apply (Subgroup.map_eq_bot_iff _).mpr
          simpa only [q, QuotientGroup.ker_mk'] using hW₂D
    have hrk : Commute (r : L ⧸ D) (k : L ⧸ D) := by
      rw [commute_iff_eq]
      calc
        (r : L ⧸ D) * (k : L ⧸ D) =
            ((r : L ⧸ D) * (k : L ⧸ D) *
                (r : L ⧸ D)⁻¹) * (r : L ⧸ D) := by group
        _ = (k : L ⧸ D) * (r : L ⧸ D) := by rw [hk]
    have hkcent :
        (k : L ⧸ D) ∈ centralizerWithin Kq
          (Subgroup.zpowers (r : L ⧸ D)) := by
      refine ⟨k.property, ?_⟩
      intro y hy
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (hrk.zpow_left n).eq
    rw [hcentBot] at hkcent
    exact Subtype.ext (Subgroup.mem_bot.mp hkcent)
  exact
    { isComplement := hcomp
      kernel_normal := inferInstance
      kernel_ne_bot := hKqne
      complement_ne_bot := hRqne
      fixedPointFree := hfixed }

private theorem ftType34_secondDerived_large
    (base : FTType34Base M U W W₁ W₂ defW)
    (hproper : secondDerivedWithin M < base.HC) :
    2 * base.q + 1 ≤
      (secondDerivedWithin M).relIndex base.HC := by
  let N : Subgroup M := (secondDerivedWithin M).subgroupOf M
  let K : Subgroup M := base.HUInM
  let HCm : Subgroup M := base.HC.subgroupOf M
  let qM : M →* M ⧸ N := QuotientGroup.mk' N
  let A : Subgroup (M ⧸ N) := HCm.map qM
  let R : Subgroup (M ⧸ N) := (W₁.subgroupOf M).map qM
  have hNnormal : N.Normal := ftType34SecondDerivedInM_normal34 M
  letI : N.Normal := hNnormal
  have hNltHU : secondDerivedWithin M < base.HU :=
    hproper.trans_le base.HC_le_HU
  have hNK : N < K := by
    simpa only [N, K, FTType34Base.HUInM] using
      subgroupOf_lt34 base.HU_le_M hNltHU
  have hNHC : N < HCm := by
    simpa only [N, HCm] using
      subgroupOf_lt34
        (base.HC_le_HU.trans base.HU_le_M) hproper
  have hW₂N : W₂.subgroupOf M ≤ N := by
    intro x hx
    change (x : G) ∈ secondDerivedWithin M
    exact base.MtypeP.2.2.2.1.2.2.2.1 hx
  have hfrob : IsFrobeniusDecomposition
      (K.map qM) R := by
    simpa only [K, R, qM] using
      primeTI_frobenius_quotient_of_fixed_le34
        base.primeTI N hNK hW₂N
  have hHCnormal : HCm.Normal := by
    simpa only [HCm] using (ftType34_HC_normal_M base).2
  letI : A.Normal := by
    dsimp only [A]
    exact Subgroup.Normal.map hHCnormal qM
      (QuotientGroup.mk'_surjective N)
  have hAK : A ≤ K.map qM :=
    Subgroup.map_mono
      (Subgroup.subgroupOf_mono M base.HC_le_HU)
  have hAne : A ≠ ⊥ := by
    simpa only [A, HCm, qM] using
      (IsFrobeniusDecomposition.quotient_kernel_ne_bot hNHC)
  have hoddQ : Odd (Nat.card (M ⧸ N)) :=
    odd_natCard_quotient N (mFT_odd M)
  have htwice : 2 * Nat.card R ≤ Nat.card A - 1 :=
    two_complement_card_le_subkernel_card_sub_one34
      hoddQ hfrob hAK (inferInstance : A.Normal) hAne
  have hRcard : Nat.card R = base.q := by
    let R₀ : Subgroup M := W₁.subgroupOf M
    let f : R₀ →* M ⧸ N := qM.comp R₀.subtype
    have hker : f.ker = ⊥ := by
      ext x
      change qM (x : M) = 1 ↔ x = 1
      constructor
      · intro hxQ
        have hxN : (x : M) ∈ N :=
          (QuotientGroup.eq_one_iff (x : M)).mp hxQ
        have hxK : (x : M) ∈ K := hNK.le hxN
        have hxbot : (x : M) ∈ (⊥ : Subgroup M) :=
          base.derived_complement_decomposition.2.2.2.disjoint.le_bot
            ⟨hxK, x.property⟩
        exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
      · intro hx
        subst x
        simp
    have hrange : f.range = R₀.map qM := by
      dsimp [f]
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    calc
      Nat.card R = Nat.card f.range := by
        dsimp only [R, R₀]
        exact Nat.card_congr
          (MulEquiv.subgroupCongr hrange.symm).toEquiv
      _ = f.ker.index := (Subgroup.index_ker f).symm
      _ = Nat.card R₀ := by rw [hker, Subgroup.index_bot]
      _ = base.q := by
        exact MathlibSupport.natCard_subgroupOf_eq
          base.derived_complement_decomposition.2.1
  have hAcard :
      Nat.card A =
        (secondDerivedWithin M).relIndex base.HC := by
    calc
      Nat.card A = N.relIndex HCm :=
        (relIndex_eq_card_map_quotient34 hNnormal hNHC.le).symm
      _ = (secondDerivedWithin M).relIndex base.HC := by
        simpa only [N, HCm] using
          (Subgroup.relIndex_subgroupOf
            (H := secondDerivedWithin M)
            (base.HC_le_HU.trans base.HU_le_M))
  rw [hRcard, hAcard] at htwice
  have hindexPos :
      0 < (secondDerivedWithin M).relIndex base.HC := by
    rw [← hAcard]
    exact Nat.card_pos
  omega

/-- Peterfalvi (11.5). -/
theorem FTtype34_der2
    (base : FTType34Base M U W W₁ W₂ defW) :
    secondDerivedWithin M = base.HC := by
  apply le_antisymm (ftType34_secondDerived_le_HC base)
  by_contra hnot
  have hproper : secondDerivedWithin M < base.HC :=
    lt_of_le_of_ne (ftType34_secondDerived_le_HC base)
      (fun heq ↦ hnot heq.symm.le)
  exact (not_lt_of_ge (ftType34_secondDerived_large base hproper))
    (ftType34_secondDerived_small base hproper)

/-! ## Peterfalvi (11.6) -/

private theorem inf_commutator_eq_map_commutator_of_normal_complement34
    {Q : Type*} [Group Q]
    {K R : Subgroup Q} [K.Normal]
    (hcomp : K.IsComplement' R) :
    R ⊓ _root_.commutator Q =
      (_root_.commutator R).map R.subtype := by
  apply le_antisymm
  · intro x hx
    let q : Q →* Q ⧸ K := QuotientGroup.mk' K
    let e : Q ⧸ K ≃* R := hcomp.symm.QuotientMulEquiv
    let f : Q →* R := e.toMonoidHom.comp q
    have hfSurj : Function.Surjective f :=
      e.surjective.comp (QuotientGroup.mk'_surjective K)
    have hmapComm :
        (_root_.commutator Q).map f = _root_.commutator R := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hfSurj]
      rfl
    have hfx : f x ∈ _root_.commutator R := by
      rw [← hmapComm]
      exact Subgroup.mem_map_of_mem f hx.2
    let xR : R := ⟨x, hx.1⟩
    have hfxEq : f x = xR := by
      change e (q x) = xR
      apply hcomp.quotientMap_injective_on_right le_rfl
      exact hcomp.symm.quotientGroupMk_leftQuotientEquiv (q x)
    exact ⟨xR, hfxEq ▸ hfx, rfl⟩
  · apply le_inf
    · exact Subgroup.map_subtype_le (_root_.commutator R)
    · rw [R.map_subtype_commutator]
      simpa only [_root_.commutator_def] using
        (Subgroup.commutator_mono
          (show R ≤ (⊤ : Subgroup Q) from le_top)
          (show R ≤ (⊤ : Subgroup Q) from le_top))

/-- The four clauses of Peterfalvi (11.6). -/
structure FTType34Facts
    (base : FTType34Base M U W W₁ W₂ defW) : Prop where
  H_isPGroup : IsPGroup base.p base.H
  U_le_centralizer_H0 :
    U ≤ Subgroup.centralizer (base.H0 : Set G)
  H0_eq_derived_H : base.H0 = derivedWithin base.H
  C_eq_derived_U : base.C = base.U'
private theorem ftType34_U_centralizes_H0_phase2
    {M U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (base : FTType34Base M U W W₁ W₂ defW) :
    U ≤ Subgroup.centralizer (base.H0 : Set G) := by
  let J : Subgroup G := U ⊔ W₁
  have hJleM : J ≤ M := by
    exact sup_le
      (base.U_le_HU.trans base.HU_le_M)
      base.derived_complement_decomposition.2.1
  have hnorm : J ≤ Subgroup.normalizer (base.H0 : Set G) := by
    exact hJleM.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (Ptype_Fcore_kernel_le_M base.ptypeCtx)).mp
          (Ptype_Fcore_kernel_normal_M base.ptypeCtx))
  have hcop : Nat.Coprime (Nat.card base.H0) (Nat.card J) :=
    (Ptype_Fcore_coprime base.ptypeCtx).coprime_dvd_left
      (Subgroup.card_dvd_of_le base.H0_le_H)
  have hsol : IsSolvable base.H0 := by
    letI : IsSolvable M := mmax_sol base.maxM
    exact isSolvable_of_injective
      (Subgroup.inclusion (Ptype_Fcore_kernel_le_M base.ptypeCtx))
      (Subgroup.inclusion_injective
        (Ptype_Fcore_kernel_le_M base.ptypeCtx))
  have hW₂not : ¬ W₂ ≤ base.H0 := by
    intro hW₂H0
    letI : (base.H0.subgroupOf M).Normal :=
      Ptype_Fcore_kernel_normal_M base.ptypeCtx
    have hcard := ptypeW₂_quotient_image_card
      (K := base.H0) base.ptypeCtx
      (base.H0_le_H.trans base.H_le_HU)
      (inf_eq_left.mpr base.H0_le_H)
    have hmapBot :
        (W₂.subgroupOf M).map
          (QuotientGroup.mk' (base.H0.subgroupOf M)) = ⊥ := by
      apply (Subgroup.map_eq_bot_iff _).mpr
      intro w hw
      change w ∈ (QuotientGroup.mk' (base.H0.subgroupOf M)).ker
      rw [QuotientGroup.ker_mk']
      exact hW₂H0 hw
    have hpOne : base.p = 1 := by
      calc
        base.p = ptypeFactorPrime base.ptypeCtx :=
          (ftType34_factorPrime_eq_p base).symm
        _ = Nat.card
            ((W₂.subgroupOf M).map
              (QuotientGroup.mk' (base.H0.subgroupOf M))) := hcard.symm
        _ = 1 := by rw [hmapBot]; simp
    exact base.p_prime.ne_one hpOne
  have hcentLeW₂ : centralizerWithin base.H0 W₁ ≤ W₂ := by
    calc
      centralizerWithin base.H0 W₁ ≤
          centralizerWithin base.H W₁ :=
        centralizerWithin_mono_left base.H0_le_H
      _ = W₂ :=
        typeP_cent_core_compl M U W W₁ W₂ defW base.MtypeP
  have hcentBot : centralizerWithin base.H0 W₁ = ⊥ := by
    let I : Subgroup W₂ :=
      (centralizerWithin base.H0 W₁).subgroupOf W₂
    letI : Fact (Nat.card W₂).Prime := ⟨base.p_prime⟩
    rcases I.eq_bot_or_eq_top_of_prime_card with hIbot | hItop
    · apply le_bot_iff.mp
      intro x hx
      have hdis : Disjoint (centralizerWithin base.H0 W₁) W₂ :=
        Subgroup.subgroupOf_eq_bot.mp hIbot
      have hxbot : x ∈ (⊥ : Subgroup G) := by
        rw [← disjoint_iff.mp hdis]
        exact ⟨hx, hcentLeW₂ hx⟩
      exact hxbot
    · exfalso
      apply hW₂not
      exact (Subgroup.subgroupOf_eq_top.mp hItop).trans
        (centralizerWithin_le_left base.H0 W₁)
  have hfix := Frobenius_Wielandt_fixpoint
    (Ptype_compl_Frobenius base.ptypeCtx) hnorm hcop hsol
  exact hfix.2.1 hcentBot

/-- BG 6.3(a) identifies the selected lower term with the derived subgroup
of the Fitting factor.  The two explicit hypotheses are the preceding
phase-2 conclusions, which avoids any dependency cycle between the private
lemmas. -/
private theorem ftType34_H0_eq_derived_H_phase2
    {M U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (base : FTType34Base M U W W₁ W₂ defW)
    (hder2 : secondDerivedWithin M = base.HC)
    (hUcent : U ≤ Subgroup.centralizer (base.H0 : Set G)) :
    base.H0 = derivedWithin base.H := by
  let Hs : Subgroup base.HU := base.H.subgroupOf base.HU
  let Us : Subgroup base.HU := U.subgroupOf base.HU
  letI : Hs.Normal := base.fcore_complement_decomposition.2.2.1
  have hcomp : Hs.IsComplement' Us :=
    base.fcore_complement_decomposition.2.2.2
  have hnorm : Us ≤ Subgroup.normalizer (Hs : Set base.HU) := by
    rw [Hs.normalizer_eq_top]
    exact le_top
  have hcopAmbient : Nat.Coprime (Nat.card base.H) (Nat.card U) :=
    (Ptype_Fcore_coprime base.ptypeCtx).coprime_dvd_right
      (Subgroup.card_dvd_of_le
        (show U ≤ U ⊔ W₁ from le_sup_left))
  have hcardHs : Nat.card Hs = Nat.card base.H := by
    dsimp only [Hs]
    exact MathlibSupport.natCard_subgroupOf_eq base.H_le_HU
  have hcardUs : Nat.card Us = Nat.card U := by
    dsimp only [Us]
    exact MathlibSupport.natCard_subgroupOf_eq base.U_le_HU
  have hcop : Nat.Coprime (Nat.card Hs) (Nat.card Us) := by
    simpa only [hcardHs, hcardUs] using hcopAmbient
  letI : IsSolvable Hs := by
    letI : IsSolvable M := mmax_sol base.maxM
    letI : IsSolvable base.HU :=
      isSolvable_of_injective
        (Subgroup.inclusion base.HU_le_M)
        (Subgroup.inclusion_injective base.HU_le_M)
    exact isSolvable_subgroup_of_isSolvable Hs
  have hHder : Hs ≤ _root_.commutator base.HU := by
    intro h hh
    have hhAmbient : ((h : base.HU) : G) ∈ secondDerivedWithin M := by
      rw [hder2]
      exact (le_sup_left : base.H ≤ base.H ⊔ base.C) hh
    change ((h : base.HU) : G) ∈ derivedWithin base.HU at hhAmbient
    rw [derivedWithin] at hhAmbient
    rcases hhAmbient with ⟨d, hd, hdh⟩
    have hdEq : d = h := Subtype.ext hdh
    exact hdEq ▸ hd
  have hBG := coprime_der1_sdprod hcomp hnorm hcop hHder
  apply le_antisymm
  · intro x hx
    let xHU : base.HU :=
      ⟨x, base.H_le_HU (base.H0_le_H hx)⟩
    have hxCent : xHU ∈ centralizerWithin Hs Us := by
      refine ⟨base.H0_le_H hx, ?_⟩
      intro u hu
      apply Subtype.ext
      exact (hUcent hu x hx).symm
    have hxComm : xHU ∈ ⁅Hs, Hs⁆ := hBG.2 hxCent
    have hxMap : x ∈ (⁅Hs, Hs⁆).map base.HU.subtype :=
      ⟨xHU, hxComm, rfl⟩
    have hmapHs : Hs.map base.HU.subtype = base.H := by
      exact Subgroup.map_subgroupOf_eq_of_le base.H_le_HU
    rw [Subgroup.map_commutator, hmapHs] at hxMap
    rw [derivedWithin, base.H.map_subtype_commutator]
    exact hxMap
  · letI : (base.H0.subgroupOf base.H).Normal :=
      Ptype_Fcore_kernel_normal_Fcore base.ptypeCtx
    have hab : IsMulCommutative
        (base.H ⧸ base.H0.subgroupOf base.H) :=
      (ftType34_factor_elementary base).commutative
    have hcomm : _root_.commutator base.H ≤
        base.H0.subgroupOf base.H :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hab
    intro x hx
    rw [derivedWithin] at hx
    rcases hx with ⟨d, hd, rfl⟩
    exact hcomm hd

/-! ### Nilpotent group with p-group abelianization -/

/-- A finite nilpotent group whose abelianization is a `p`-group is itself a
`p`-group.  This local copy removes the last draft-only dependency from
(11.6). -/
private theorem isPGroup_of_nilpotent_of_abelianization_isPGroup34
    {Q : Type*} [Group Q] [Finite Q]
    {p : ℕ} [Fact p.Prime]
    (hnil : Group.IsNilpotent Q)
    (hab : IsPGroup p (Q ⧸ _root_.commutator Q)) :
    IsPGroup p Q := by
  letI : Group.IsNilpotent Q := hnil
  let D : Subgroup Q := _root_.commutator Q
  let O : Subgroup Q := pPrimeCore p Q
  let P : Subgroup Q := pCore p Q
  letI : D.Normal := by dsimp [D]; infer_instance
  letI : O.Normal := by dsimp [O]; infer_instance
  letI : P.Normal := by dsimp [P]; infer_instance
  have hcomp : P.IsComplement' O := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
      (disjoint_pCore_pPrimeCore (G := Q) (p := p))
    rw [← Subgroup.normal_mul P O,
      sup_pCore_pPrimeCore_eq_top_of_isNilpotent (G := Q) p]
    rfl
  have hOD : O ≤ D := by
    let qD : Q →* Q ⧸ D := QuotientGroup.mk' D
    let Obar : Subgroup (Q ⧸ D) := O.map qD
    have hObarP : IsPGroup p Obar := hab.to_subgroup Obar
    have hObarPrime : IsPPrimeSubgroup p Obar := by
      rw [IsPPrimeSubgroup]
      exact (pPrimeCore_coprime_card (G := Q) (p := p)).coprime_dvd_right
        (Subgroup.card_map_dvd O qD)
    have hObarCore : Obar ≤ pPrimeCore p (Q ⧸ D) := by
      apply le_pPrimeCore hObarPrime
      dsimp [Obar]
      infer_instance
    have hObarBot : Obar = ⊥ := by
      apply le_bot_iff.mp
      rw [← disjoint_iff.mp
        (disjoint_pPrimeCore_of_isPGroup (G := Q ⧸ D) hObarP)]
      exact le_inf le_rfl hObarCore
    have hker : O ≤ qD.ker := (Subgroup.map_eq_bot_iff O).mp hObarBot
    simpa [qD, QuotientGroup.ker_mk'] using hker
  have hObot : O = ⊥ := by
    by_contra hOne
    let qP : Q →* Q ⧸ P := QuotientGroup.mk' P
    have hqPO : Function.Surjective (qP.comp O.subtype) := by
      intro z
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective P z
      obtain ⟨po, hpo, _⟩ := hcomp.existsUnique g
      refine ⟨po.2, ?_⟩
      change qP (po.2 : Q) = qP g
      rw [← hpo, map_mul]
      have hpone : qP (po.1 : Q) = 1 :=
        (QuotientGroup.eq_one_iff (po.1 : Q)).mpr po.1.property
      rw [hpone, one_mul]
    have hOmap : O.map qP = ⊤ := by
      have hrange : (qP.comp O.subtype).range = O.map qP := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rw [← hrange]
      exact MonoidHom.range_eq_top.mpr hqPO
    have hcommTop : _root_.commutator (Q ⧸ P) = ⊤ := by
      apply top_unique
      rw [← hOmap]
      calc
        O.map qP ≤ D.map qP := Subgroup.map_mono hOD
        _ = _ := by
          dsimp [D]
          rw [map_commutator_eq,
            MonoidHom.range_eq_top.mpr
              (QuotientGroup.mk'_surjective P)]
          rfl
    let e : (Q ⧸ P) ≃* O := hcomp.symm.QuotientMulEquiv
    letI : Nontrivial O := O.nontrivial_iff_ne_bot.mpr hOne
    letI : Nontrivial (Q ⧸ P) := e.toEquiv.nontrivial
    exact (ne_of_lt
      (IsSolvable.commutator_lt_top_of_nontrivial (Q ⧸ P))) hcommTop
  have hPtop : P = ⊤ := by
    have hsup := sup_pCore_pPrimeCore_eq_top_of_isNilpotent (G := Q) p
    simpa [P, O, hObot] using hsup
  have htopP : IsPGroup p (⊤ : Subgroup Q) := by
    rw [← hPtop]
    exact pCore_isPGroup
  exact htopP.of_equiv Subgroup.topEquiv

/-- Final group-theoretic clause of (11.6), after identification of the lower
term with the derived subgroup. -/
private theorem ftType34_H_isPGroup_phase2
    {M U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (base : FTType34Base M U W W₁ W₂ defW)
    (hH0 : base.H0 = derivedWithin base.H) :
    IsPGroup base.p base.H := by
  letI : Fact base.p.Prime := ⟨base.p_prime⟩
  have hsub : base.H0.subgroupOf base.H =
      _root_.commutator base.H := by
    apply Subgroup.map_injective base.H.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le base.H0_le_H,
      base.H.map_subtype_commutator]
    simpa only [derivedWithin, base.H.map_subtype_commutator] using hH0
  have hab := (ftType34_factor_elementary base).isPGroup
  change IsPGroup base.p
    (base.H ⧸ base.H0.subgroupOf base.H) at hab
  have hab' : IsPGroup base.p
      (base.H ⧸ _root_.commutator base.H) :=
    hab.of_equiv (QuotientGroup.quotientMulEquivOfEq hsub)
  exact isPGroup_of_nilpotent_of_abelianization_isPGroup34
    (Fcore_nil M) hab'

private theorem ftType34_U_centralizes_H0
    (base : FTType34Base M U W W₁ W₂ defW) :
    U ≤ Subgroup.centralizer (base.H0 : Set G) :=
  ftType34_U_centralizes_H0_phase2 base

private theorem ftType34_H0_eq_derived_H
    (base : FTType34Base M U W W₁ W₂ defW) :
    base.H0 = derivedWithin base.H :=
  ftType34_H0_eq_derived_H_phase2 base
    (FTtype34_der2 base) (ftType34_U_centralizes_H0 base)

private theorem ftType34_C_eq_derived_U
    (base : FTType34Base M U W W₁ W₂ defW) :
    base.C = base.U' := by
  let Hs : Subgroup base.HU := base.H.subgroupOf base.HU
  let Us : Subgroup base.HU := U.subgroupOf base.HU
  let Cs : Subgroup base.HU := base.C.subgroupOf base.HU
  letI : Hs.Normal := base.fcore_complement_decomposition.2.2.1
  have hcomp : Hs.IsComplement' Us :=
    base.fcore_complement_decomposition.2.2.2
  have hcommEq :
      _root_.commutator base.HU =
        base.HC.subgroupOf base.HU := by
    apply Subgroup.map_injective base.HU.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le base.HC_le_HU]
    change secondDerivedWithin M = base.HC
    exact FTtype34_der2 base
  have hHCsplit :
      base.HC.subgroupOf base.HU = Hs ⊔ Cs := by
    change (base.H ⊔ base.C).subgroupOf base.HU =
      base.H.subgroupOf base.HU ⊔
        base.C.subgroupOf base.HU
    rw [Subgroup.subgroupOf_sup base.H_le_HU base.C_le_HU]
  have hCsUs : Cs ≤ Us :=
    Subgroup.subgroupOf_mono base.HU base.C_le_U
  have hinter :
      Us ⊓ _root_.commutator base.HU = Cs := by
    rw [hcommEq, hHCsplit]
    exact (PTypeCoreContextInternal.pTypeCore_inf_sup_eq_of_complement
      Hs Us Hs Cs hcomp le_rfl hCsUs).2
  have hsemider :
      Us ⊓ _root_.commutator base.HU =
        (_root_.commutator Us).map Us.subtype :=
    inf_commutator_eq_map_commutator_of_normal_complement34 hcomp
  have hderived :
      (_root_.commutator Us).map Us.subtype =
        base.U'.subgroupOf base.HU := by
    change pTypeDerivedComplementInMaximal Us.subtype =
      (derivedWithin U).subgroupOf base.HU
    rw [← internal.pTypeDerivedComplementInMaximal_eq_subgroupOf
        base.U_le_HU,
      internal.pTypeDerivedComplementInMaximal_eq_derivedWithin_subgroupOf
        base.U_le_HU]
  have hCsEq : Cs = base.U'.subgroupOf base.HU :=
    hinter.symm.trans (hsemider.trans hderived)
  have hmap := congrArg
    (fun S : Subgroup base.HU ↦ S.map base.HU.subtype) hCsEq
  have hUPrimeHU : base.U' ≤ base.HU :=
    (Subgroup.map_subtype_le (_root_.commutator U)).trans base.U_le_HU
  simpa only [Cs,
    Subgroup.map_subgroupOf_eq_of_le base.C_le_HU,
    Subgroup.map_subgroupOf_eq_of_le hUPrimeHU] using hmap

private theorem ftType34_H_isPGroup
    (base : FTType34Base M U W W₁ W₂ defW) :
    IsPGroup base.p base.H :=
  ftType34_H_isPGroup_phase2 base
    (ftType34_H0_eq_derived_H base)

/-- `PFsection11.v: FTtype34_facts`, Peterfalvi (11.6). -/
theorem FTtype34_facts
    (base : FTType34Base M U W W₁ W₂ defW) :
    FTType34Facts base :=
  { H_isPGroup := ftType34_H_isPGroup base
    U_le_centralizer_H0 := ftType34_U_centralizes_H0 base
    H0_eq_derived_H := ftType34_H0_eq_derived_H base
    C_eq_derived_U := ftType34_C_eq_derived_U base }

/-! ## Internal interface for the final 11.7 module -/

namespace FTType34BoundsCoreInternal

theorem factor_card
    (base : FTType34Base M U W W₁ W₂ defW) :
    Nat.card (ptypeFCoreFactor base.ptypeCtx) = base.p ^ base.q :=
  ftType34_factor_card base

theorem factor_elementary
    (base : FTType34Base M U W W₁ W₂ defW) :
    IsElementaryAbelianGroup base.p
      (ptypeFCoreFactor base.ptypeCtx) :=
  ftType34_factor_elementary base

end FTType34BoundsCoreInternal

end

end Submission.OddOrder.PF
