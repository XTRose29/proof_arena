import Submission.OddOrder.PF.Section03.CyclicTISymmetry
import Submission.OddOrder.PF.Section08.FTContextDefinitions
import Submission.OddOrder.PF.Section09.PTypeReducibleCoreCases
import Submission.OddOrder.PF.Section10.FTType345Coherence

/-!
# Peterfalvi Section 10: the Suzuki-cover contradiction

This file contains the last phase of Peterfalvi (10.8).  It turns the
coprime-order lower bound from `FTType345Coherence` into a contradiction by
combining the one-set Dade cover inequality with the type-II partner of the
selected type-P maximal subgroup.

The counting argument is carried out directly from the general Dade,
normalized-TI, Frobenius, and type-P APIs.  In particular, none of the
Section-10-specific cover or partner-counting assertions is taken as an
additional premise.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section14
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open FTType345ConstantsInternal
open scoped BigOperators Classical Pointwise IsMulCommutative

variable {Gamma : Type} [Group Gamma] [Fintype Gamma]
variable [IsMinSimpleOddGroup Gamma]
variable {M U W W₁ W₂ : Subgroup Gamma}
variable {defW : IsInternalDirectProductIn W₁ W₂ W}

local instance noncoherenceInvertibleNatCardComplex
    {Q : Type} [Group Q] [Fintype Q] :
    Invertible (Nat.card Q : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-! ## Finite-set and Frobenius adapters -/

/-- A normalized-TI set has the expected conjugacy-saturated cardinality. -/
private theorem ncard_classSupport_normalizedTI10
    {S : Set Gamma} {N : Subgroup Gamma}
    (hTI : IsNormalizedTI S (⊤ : Subgroup Gamma) N) :
    (classSupportWithin (⊤ : Subgroup Gamma) S).ncard =
      S.ncard * N.index := by
  let action := subgroupConjugationActionOnAmbient (⊤ : Subgroup Gamma)
  letI : SMul (⊤ : Subgroup Gamma) Gamma := action.toSMul
  letI : MulAction (⊤ : Subgroup Gamma) Gamma := action.toMulAction
  letI : MulAction (⊤ : Subgroup Gamma) (Set Gamma) := Set.mulActionSet
  have hpart := normalizedTI_classSupport_partition hTI
  change IsSetPartition (MulAction.orbit (⊤ : Subgroup Gamma) S)
      (classSupportWithin (⊤ : Subgroup Gamma) S) ∧
    (MulAction.orbit (⊤ : Subgroup Gamma) S).ncard =
      N.relIndex (⊤ : Subgroup Gamma) at hpart
  have horbitFinite :
      (MulAction.orbit (⊤ : Subgroup Gamma) S).Finite := Set.toFinite _
  have hblock : ∀ B ∈ MulAction.orbit (⊤ : Subgroup Gamma) S,
      B.ncard = S.ncard := by
    intro B hB
    rcases hB with ⟨g, rfl⟩
    exact Set.ncard_smul_set g S
  rw [← hpart.1.1]
  have hsUnion : ⋃₀ (MulAction.orbit (⊤ : Subgroup Gamma) S) =
      ⋃ B ∈ MulAction.orbit (⊤ : Subgroup Gamma) S, B := by
    ext x
    simp
  rw [hsUnion]
  calc
    (⋃ B ∈ MulAction.orbit (⊤ : Subgroup Gamma) S, B).ncard =
        ∑ᶠ B ∈ MulAction.orbit (⊤ : Subgroup Gamma) S, B.ncard :=
      horbitFinite.ncard_biUnion
        (fun B _ ↦ Set.toFinite B) hpart.1.2.1
    _ = ∑ᶠ _B ∈ MulAction.orbit (⊤ : Subgroup Gamma) S, S.ncard :=
      finsum_mem_congr rfl hblock
    _ = (∑ᶠ _B ∈ MulAction.orbit (⊤ : Subgroup Gamma) S, (1 : ℕ)) *
          S.ncard := by
      rw [finsum_mem_mul' (fun _B : Set Gamma ↦ 1) S.ncard horbitFinite]
      simp
    _ = (MulAction.orbit (⊤ : Subgroup Gamma) S).ncard * S.ncard := by
      rw [finsum_one]
    _ = N.relIndex (⊤ : Subgroup Gamma) * S.ncard := by rw [hpart.2]
    _ = S.ncard * N.index := by
      rw [N.relIndex_top_right, Nat.mul_comm]

/-- A subgroup's nonidentity set has one fewer element. -/
private theorem subgroupNonidentity_ncard10 (H : Subgroup Gamma) :
    (subgroupNonidentity H).ncard = Nat.card H - 1 := by
  have hone : (1 : Gamma) ∈ (H : Set Gamma) := H.one_mem
  rw [show subgroupNonidentity H = (H : Set Gamma) \ {1} by
    ext x
    simp [subgroupNonidentity, nonidentitySet]]
  rw [Set.ncard_sdiff_singleton_of_mem hone, ← Nat.card_coe_set_eq,
    SetLike.coe_sort_coe]

/-- Cardinality, normalized by the ambient group, decreases when a
normalized-TI set is saturated by conjugacy. -/
private theorem classSupport_ratio_eq10
    {S : Set Gamma} {N : Subgroup Gamma}
    (hTI : IsNormalizedTI S (⊤ : Subgroup Gamma) N) :
    (classSupportWithin (⊤ : Subgroup Gamma) S).ncard /
        (Nat.card Gamma : ℝ) =
      S.ncard / (Nat.card N : ℝ) := by
  have hcard := ncard_classSupport_normalizedTI10 hTI
  have hindex : N.index * Nat.card N = Nat.card Gamma := by
    simpa only [Subgroup.card_top] using N.index_mul_card
  rw [hcard]
  norm_num only [Nat.cast_mul]
  rw [← hindex]
  norm_num only [Nat.cast_mul]
  field_simp [Nat.cast_ne_zero.mpr Nat.card_pos.ne',
    Nat.cast_ne_zero.mpr N.index_ne_zero_of_finite]

/-- The centralizer of a nonidentity Frobenius-kernel element lies in the
kernel. -/
private theorem centralizer_frobeniusKernel_le10
    {Q : Type*} [Group Q] [Finite Q]
    {K R : Subgroup Q}
    (hFrob : IsFrobeniusDecomposition K R)
    {z : Q} (hzK : z ∈ K) (hzOne : z ≠ 1) :
    Subgroup.centralizer (Subgroup.zpowers z : Set Q) ≤ K := by
  intro x hx
  by_contra hxK
  obtain ⟨k, hxR⟩ :=
    hFrob.exists_kernel_conjugate_complement_of_not_mem hxK
  rcases hxR with ⟨r, hrR, hrx⟩
  have hrx' : (k : Q) * r * (k : Q)⁻¹ = x := by
    simpa [MulAut.conj_apply] using hrx
  let rR : R := ⟨r, hrR⟩
  have hrRne : rR ≠ 1 := by
    intro hrOne
    apply hxK
    have hrOneQ : r = 1 := congrArg Subtype.val hrOne
    have hxOne : x = 1 := by
      calc
        x = (k : Q) * r * (k : Q)⁻¹ := hrx'.symm
        _ = 1 := by rw [hrOneQ]; simp
    exact hxOne ▸ K.one_mem
  have hzKconj : (k : Q)⁻¹ * z * (k : Q) ∈ K := by
    simpa using hFrob.kernel_normal.conj_mem z hzK (k : Q)⁻¹
  let zK : K := ⟨(k : Q)⁻¹ * z * (k : Q), hzKconj⟩
  have hzKne : zK ≠ 1 := by
    intro hzKOne
    apply hzOne
    have hval := congrArg Subtype.val hzKOne
    dsimp only [zK] at hval
    calc
      z = (k : Q) * ((k : Q)⁻¹ * z * (k : Q)) * (k : Q)⁻¹ := by
        group
      _ = 1 := by rw [hval]; simp
  have hxcomm : Commute x z :=
    (Subgroup.mem_centralizer_iff.mp hx z
      (Subgroup.mem_zpowers z)).symm
  have hxfix : x * z * x⁻¹ = z := by
    calc
      x * z * x⁻¹ = z * x * x⁻¹ := by rw [hxcomm.eq]
      _ = z := by simp
  have hfix : (rR : Q) * (zK : Q) * (rR : Q)⁻¹ = (zK : Q) := by
    change r * ((k : Q)⁻¹ * z * (k : Q)) * r⁻¹ =
      (k : Q)⁻¹ * z * (k : Q)
    calc
      r * ((k : Q)⁻¹ * z * (k : Q)) * r⁻¹ =
          (k : Q)⁻¹ *
            (((k : Q) * r * (k : Q)⁻¹) * z *
              ((k : Q) * r * (k : Q)⁻¹)⁻¹) * (k : Q) := by
        group
      _ = (k : Q)⁻¹ * (x * z * x⁻¹) * (k : Q) := by rw [hrx']
      _ = (k : Q)⁻¹ * z * (k : Q) := by rw [hxfix]
  exact hzKne (hFrob.fixedPointFree rR hrRne zK hfix)

/-- Ambient form of the preceding centralizer lemma for `IsFrobeniusIn`. -/
private theorem centralizer_frobeniusIn_kernel_le10
    {H V D : Subgroup Gamma}
    (hFrob : IsFrobeniusIn H V D)
    {z : Gamma} (hzH : z ∈ H) (hzOne : z ≠ 1) :
    centralizerWithin D (Subgroup.zpowers z) ≤ H := by
  intro x hx
  have hzSup : z ∈ H ⊔ V := (le_sup_left : H ≤ H ⊔ V) hzH
  have hxSup : x ∈ H ⊔ V := by
    rw [hFrob.1]
    exact hx.1
  let zSup : ↥(H ⊔ V) := ⟨z, hzSup⟩
  let xSup : ↥(H ⊔ V) := ⟨x, hxSup⟩
  have hzSupOne : zSup ≠ 1 := by
    intro h
    exact hzOne (congrArg Subtype.val h)
  have hxCent : xSup ∈
      Subgroup.centralizer (Subgroup.zpowers zSup : Set ↥(H ⊔ V)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    apply Subtype.ext
    exact hx.2 (z ^ n) (Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) n)
  have hxKernel := centralizer_frobeniusKernel_le10 hFrob.2.2
    (show zSup ∈ H.subgroupOf (H ⊔ V) from hzH) hzSupOne hxCent
  exact hxKernel

/-- Repackage the Frobenius datum supplied by BG Summary II in the
ambient-subgroup form used by Peterfalvi. -/
private theorem summaryFrobeniusData_isFrobeniusIn10
    {L : Subgroup Gamma} (data : BGSummaryIIFrobeniusData L) :
    IsFrobeniusIn (Fitting_core L) data.complement L := by
  have hFL : Fitting_core L ≤ L := Fcore_sub L
  have hsup : Fitting_core L ⊔ data.complement = L := by
    apply le_antisymm (sup_le hFL data.complement_le)
    intro x hxL
    let xL : L := ⟨x, hxL⟩
    have hxTop : xL ∈ (⊤ : Subgroup L) := Subgroup.mem_top xL
    rw [← data.frobenius.isComplement.sup_eq_top,
      ← Subgroup.subgroupOf_sup hFL data.complement_le] at hxTop
    exact hxTop
  have hsd : IsInternalSemidirectProductIn
      (Fitting_core L) data.complement L :=
    ⟨hFL, data.complement_le, data.frobenius.kernel_normal,
      data.frobenius.isComplement⟩
  refine ⟨hsup, ?_⟩
  rw [hsup]
  exact ⟨hsd, data.frobenius⟩

private theorem pairing_sub_left10
    {Q : Type*} [Group Q] [Fintype Q]
    (a b c : ClassFunction Q ℂ) :
    characterPairing (a - b) c =
      characterPairing a c - characterPairing b c := by
  change characterPairingLeft (a - b) c = _
  exact map_sub (characterPairingRight c) a b

private theorem pairing_sub_right10
    {Q : Type*} [Group Q] [Fintype Q]
    (a b c : ClassFunction Q ℂ) :
    characterPairing a (b - c) =
      characterPairing a b - characterPairing a c := by
  change characterPairingRight (b - c) a = _
  exact map_sub (characterPairingLeft a) b c

private theorem pairing_fintype_sum_left10
    {Q I : Type*} [Group Q] [Fintype Q] [Fintype I]
    (f : I → ClassFunction Q ℂ) (a : ClassFunction Q ℂ) :
    characterPairing (∑ i, f i) a =
      ∑ i, characterPairing (f i) a := by
  change characterPairingRight a (∑ i, f i) = _
  exact map_sum (characterPairingRight a) f Finset.univ

private theorem pairing_fintype_sum_right10
    {Q I : Type*} [Group Q] [Fintype Q] [Fintype I]
    (a : ClassFunction Q ℂ) (f : I → ClassFunction Q ℂ) :
    characterPairing a (∑ i, f i) =
      ∑ i, characterPairing a (f i) := by
  change characterPairingLeft a (∑ i, f i) = _
  exact map_sum (characterPairingLeft a) f Finset.univ

private theorem inverseLinear_involutive10
    {Q : Type*} [Group Q] (phi : ClassFunction Q ℂ) :
    ClassFunction.inverseLinear (ClassFunction.inverseLinear phi) = phi := by
  ext x
  simp

/-- The integral span of a subfamily of a prime-Dade kernel layer is
supported on the Dade set once its identity value vanishes. -/
private theorem kernelLayer_closure_supportedOn_dadeSet10
    {L K H X X₁ X₂ : Subgroup Gamma}
    {A A₀ : Set Gamma}
    {defX : IsInternalDirectProductIn X₁ X₂ X}
    (pd : PrimeDadeHypothesis (⊤ : Subgroup Gamma) L K H A A₀
      X X₁ X₂ defX)
    {S : Set (ClassFunction L ℂ)}
    (hS : S ⊆ FTtypePKernelLayer pd)
    {phi : ClassFunction L ℂ}
    (hphi : phi ∈ AddSubgroup.closure S)
    (hoff : phi ∈ ClassFunction.supportedOn (nonidentitySet L)) :
    phi ∈ ClassFunction.supportedOn
      {x : L | (x : Gamma) ∈ A} := by
  letI : CoeTC L Gamma := ⟨fun x ↦ x.1⟩
  have hle : AddSubgroup.closure S ≤
      (ClassFunction.supportedOn (R := ℂ)
        (primeDadeSupport L A)).toAddSubgroup := by
    apply (AddSubgroup.closure_le _).mpr
    intro psi hpsi
    have hpsiLayer := hS hpsi
    change psi ∈ seqIndD (k := ℂ) (K.subgroupOf L)
      pd.signalizerInKernel ⊥ at hpsiLayer
    obtain ⟨theta, htheta, rfl⟩ := seqIndP.mp hpsiLayer
    exact pd.prDade_Ind_irr_on theta (mem_Iirr_kerD.mp htheta).2
  have hprime : phi ∈
      ClassFunction.supportedOn (primeDadeSupport L A) := hle hphi
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hxA
  by_cases hxOne : x = 1
  · exact ClassFunction.eq_zero_of_mem_supportedOn hoff (by simpa [hxOne])
  · apply ClassFunction.eq_zero_of_mem_supportedOn hprime
    intro hxPrime
    rw [mem_primeDadeSupport] at hxPrime
    rcases hxPrime with hxPrime | hxPrime
    · exact hxOne (Subtype.ext hxPrime)
    · exact hxA hxPrime

/-! ## Orthogonality for two restricted coherent families -/

private theorem irreducible_dual_sub_supported10
    {Q : Type*} [Group Q] [Fintype Q]
    (chi : IrreducibleCharacter Q ℂ) :
    (chi : ClassFunction Q ℂ) -
        (IrreducibleCharacter.dual chi : ClassFunction Q ℂ) ∈
      ClassFunction.supportedOn (nonidentitySet Q) := by
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hx
  have hxOne : x = 1 := by simpa [nonidentitySet] using not_not.mp hx
  subst x
  simp [IrreducibleCharacter.apply_one_eq_finrank]

private theorem sub_supported_of_one_eq10
    {Q : Type*} [Group Q]
    (phi psi : ClassFunction Q ℂ) (h : phi 1 = psi 1) :
    phi - psi ∈ ClassFunction.supportedOn (nonidentitySet Q) := by
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hx
  have hxOne : x = 1 := by
    simpa [nonidentitySet] using not_not.mp hx
  subst x
  simp [h]

private theorem isOrthonormalPair_of_realizations10
    {Q : Type*} [Group Q] [Fintype Q]
    (a b : VirtualCharacter Q ℂ)
    (ha : characterPairing (VirtualCharacter.realize a)
        (VirtualCharacter.realize a) = 1)
    (hb : characterPairing (VirtualCharacter.realize b)
        (VirtualCharacter.realize b) = 1)
    (hab : characterPairing (VirtualCharacter.realize a)
        (VirtualCharacter.realize b) = 0) :
    IntegralLattice.IsOrthonormalPair a b := by
  constructor
  · apply Int.cast_injective (α := ℂ)
    unfold normSq
    simpa only [VirtualCharacter.characterPairing_realize, Int.cast_one] using ha
  constructor
  · apply Int.cast_injective (α := ℂ)
    unfold normSq
    simpa only [VirtualCharacter.characterPairing_realize, Int.cast_one] using hb
  · apply Int.cast_injective (α := ℂ)
    simpa only [VirtualCharacter.characterPairing_realize, Int.cast_zero] using hab

/-- Dade support is inverse-stable when the underlying Dade set is the
nonidentity part of a subgroup. -/
private theorem dadeSupport_subgroupNonidentity_invStable10
    {G L H : Subgroup Gamma}
    (ddA : DadeHypothesis G L (subgroupNonidentity H)) :
    IsInvStable (Dade_support ddA) := by
  have hinv : ∀ x : Gamma,
      x ∈ Dade_support ddA → x⁻¹ ∈ Dade_support ddA := by
    intro x
    rintro ⟨a, haA, z, hz, g, hgG, hzx⟩
    have haH : a ∈ H := haA.1
    have ha1 : a ≠ 1 := haA.2
    rcases Set.mem_mul.mp hz with ⟨s, hs, b, hb, rfl⟩
    rw [Set.mem_singleton_iff] at hb
    subst b
    have hsa : Commute s a :=
      (Subgroup.mem_centralizer_iff.mp
        (Dade_signalizer_cent ddA a hs) a
          (Subgroup.mem_zpowers a)).symm
    have haInvA : a⁻¹ ∈ subgroupNonidentity H :=
      ⟨H.inv_mem haH, inv_ne_one.mpr ha1⟩
    have hsignalizerInv :
        DadeSignalizer ddA a⁻¹ = DadeSignalizer ddA a := by
      simp [DadeSignalizer, Subgroup.zpowers_inv]
    refine ⟨a⁻¹, haInvA, s⁻¹ * a⁻¹, ?_, g, hgG, ?_⟩
    · apply Set.mem_mul.mpr
      exact ⟨s⁻¹, by simpa [hsignalizerInv] using
          (DadeSignalizer ddA a).inv_mem hs,
        a⁻¹, Set.mem_singleton a⁻¹, rfl⟩
    · have hsaInv : s⁻¹ * a⁻¹ = a⁻¹ * s⁻¹ := by
        simpa only [mul_inv_rev] using congrArg Inv.inv hsa.symm
      rw [← hzx, mul_inv_rev, hsaInv]
      group
  intro x
  constructor
  · intro hx
    simpa only [inv_inv] using hinv x⁻¹ hx
  · exact hinv x

/-- Dade images are orthogonal when their global supports are disjoint and
the first underlying Dade set is a subgroup's nonidentity set. -/
private theorem disjoint_Dade_ortho_left10
    {G L₁ L₂ H₁ : Subgroup Gamma} {A₁ A₂ : Set Gamma}
    (ddA₁ : DadeHypothesis G L₁ A₁)
    (ddA₂ : DadeHypothesis G L₂ A₂)
    (hA₁ : A₁ = subgroupNonidentity H₁)
    (hdis : Disjoint (Dade_support ddA₁) (Dade_support ddA₂))
    (phi : ClassFunction L₁ ℂ) (psi : ClassFunction L₂ ℂ) :
    characterPairing (Dade ddA₁ phi) (Dade ddA₂ psi) = 0 := by
  subst A₁
  have hsubdis : Disjoint
      {x : G | (x : Gamma) ∈ Dade_support ddA₁}
      {x : G | (x : Gamma) ∈ Dade_support ddA₂} := by
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    exact Set.disjoint_left.mp hdis hx₁ hx₂
  apply characterPairing_eq_zero_of_disjoint_of_invStable_left hsubdis
  · intro x
    change (x : Gamma)⁻¹ ∈ Dade_support ddA₁ ↔
      (x : Gamma) ∈ Dade_support ddA₁
    exact dadeSupport_subgroupNonidentity_invStable10 ddA₁ (x : Gamma)
  · exact Dade_cfunS ddA₁ phi
  · exact Dade_cfunS ddA₂ psi

/-- Restricted-family form of Peterfalvi 4.1 used inside source
`Frob_der1_type2`. -/
private theorem disjoint_coherent_pair_ortho10
    {G L₁ L₂ : Subgroup Gamma}
    {H₁ : Subgroup Gamma}
    {A₁ A₂ : Set Gamma}
    (ddA₁ : DadeHypothesis G L₁ A₁)
    (ddA₂ : DadeHypothesis G L₂ A₂)
    (hA₁ : A₁ = subgroupNonidentity H₁)
    (hdis : Disjoint (Dade_support ddA₁) (Dade_support ddA₂))
    (K₁ : Subgroup L₁) [K₁.Normal]
    (K₂ : Subgroup L₂) [K₂.Normal]
    (S₁ : Set (ClassFunction L₁ ℂ))
    (S₂ : Set (ClassFunction L₂ ℂ))
    (nu₁ : ClassFunction L₁ ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (nu₂ : ClassFunction L₂ ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (coh₁ : coherent_with S₁ (nonidentitySet L₁) (Dade ddA₁) nu₁)
    (coh₂ : coherent_with S₂ (nonidentitySet L₂) (Dade ddA₂) nu₂)
    (chi₁ : IrreducibleCharacter L₁ ℂ)
    (chi₂ : IrreducibleCharacter L₂ ℂ)
    (hchi₁ : (chi₁ : ClassFunction L₁ ℂ) ∈ S₁)
    (hdual₁ : (IrreducibleCharacter.dual chi₁ : ClassFunction L₁ ℂ) ∈ S₁)
    (hchi₂ : (chi₂ : ClassFunction L₂ ℂ) ∈ S₂)
    (hdual₂ : (IrreducibleCharacter.dual chi₂ : ClassFunction L₂ ℂ) ∈ S₂)
    (hseq₁ : (chi₁ : ClassFunction L₁ ℂ) ∈
      seqIndD (k := ℂ) K₁ ⊤ ⊥)
    (hseq₂ : (chi₂ : ClassFunction L₂ ℂ) ∈
      seqIndD (k := ℂ) K₂ ⊤ ⊥) :
    characterPairing (nu₁ (chi₁ : ClassFunction L₁ ℂ))
      (nu₂ (chi₂ : ClassFunction L₂ ℂ)) = 0 := by
  have hchi₁Span : (chi₁ : ClassFunction L₁ ℂ) ∈
      AddSubgroup.closure S₁ := AddSubgroup.subset_closure hchi₁
  have hdual₁Span :
      (IrreducibleCharacter.dual chi₁ : ClassFunction L₁ ℂ) ∈
        AddSubgroup.closure S₁ := AddSubgroup.subset_closure hdual₁
  have hchi₂Span : (chi₂ : ClassFunction L₂ ℂ) ∈
      AddSubgroup.closure S₂ := AddSubgroup.subset_closure hchi₂
  have hdual₂Span :
      (IrreducibleCharacter.dual chi₂ : ClassFunction L₂ ℂ) ∈
        AddSubgroup.closure S₂ := AddSubgroup.subset_closure hdual₂
  obtain ⟨a, ha⟩ := coh₁.mapsToVirtual _ hchi₁Span
  obtain ⟨b, hb⟩ := coh₁.mapsToVirtual _ hdual₁Span
  obtain ⟨c, hc⟩ := coh₂.mapsToVirtual _ hchi₂Span
  obtain ⟨d, hd⟩ := coh₂.mapsToVirtual _ hdual₂Span
  have hoddL₁ : Odd (Nat.card L₁) :=
    Odd.of_dvd_nat (mFT_odd G) (Subgroup.card_dvd_of_le ddA₁.2.1)
  have hoddL₂ : Odd (Nat.card L₂) :=
    Odd.of_dvd_nat (mFT_odd G) (Subgroup.card_dvd_of_le ddA₂.2.1)
  letI : Invertible (Nat.card L₁ : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card L₂ : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hab : IntegralLattice.IsOrthonormalPair a b := by
    apply isOrthonormalPair_of_realizations10
    · rw [ha, coh₁.isometry _ hchi₁Span _ hchi₁Span,
        IrreducibleCharacter.characterPairing_self]
    · rw [hb, coh₁.isometry _ hdual₁Span _ hdual₁Span,
        IrreducibleCharacter.characterPairing_self]
    · rw [ha, hb, coh₁.isometry _ hchi₁Span _ hdual₁Span]
      simpa only [← ClassFunction.inverseLinear_irreducible] using
        seqInd_conjC_ortho (k := ℂ) K₁ hoddL₁ ⊤ ⊥ hseq₁
  have hcd : IntegralLattice.IsOrthonormalPair c d := by
    apply isOrthonormalPair_of_realizations10
    · rw [hc, coh₂.isometry _ hchi₂Span _ hchi₂Span,
        IrreducibleCharacter.characterPairing_self]
    · rw [hd, coh₂.isometry _ hdual₂Span _ hdual₂Span,
        IrreducibleCharacter.characterPairing_self]
    · rw [hc, hd, coh₂.isometry _ hchi₂Span _ hdual₂Span]
      simpa only [← ClassFunction.inverseLinear_irreducible] using
        seqInd_conjC_ortho (k := ℂ) K₂ hoddL₂ ⊤ ⊥ hseq₂
  have hdiff₁Span :
      (chi₁ : ClassFunction L₁ ℂ) -
          (IrreducibleCharacter.dual chi₁ : ClassFunction L₁ ℂ) ∈
        AddSubgroup.closure S₁ :=
    (AddSubgroup.closure S₁).sub_mem hchi₁Span hdual₁Span
  have hdiff₂Span :
      (chi₂ : ClassFunction L₂ ℂ) -
          (IrreducibleCharacter.dual chi₂ : ClassFunction L₂ ℂ) ∈
        AddSubgroup.closure S₂ :=
    (AddSubgroup.closure S₂).sub_mem hchi₂Span hdual₂Span
  have hagree₁ := coh₁.agrees _ hdiff₁Span
    (irreducible_dual_sub_supported10 chi₁)
  have hagree₂ := coh₂.agrees _ hdiff₂Span
    (irreducible_dual_sub_supported10 chi₂)
  have hpairs :
      characterPairing (VirtualCharacter.realize (a - b))
        (VirtualCharacter.realize (c - d)) = 0 := by
    rw [VirtualCharacter.realize_sub, VirtualCharacter.realize_sub,
      ha, hb, hc, hd, ← map_sub, ← map_sub, hagree₁, hagree₂]
    exact disjoint_Dade_ortho_left10 ddA₁ ddA₂ hA₁ hdis _ _
  have habOne : VirtualCharacter.realize (a - b) 1 = 0 := by
    rw [VirtualCharacter.realize_sub, ha, hb, ← map_sub, hagree₁, Dade1]
  have hcdOne : VirtualCharacter.realize (c - d) 1 = 0 := by
    rw [VirtualCharacter.realize_sub, hc, hd, ← map_sub, hagree₂, Dade1]
  have hac := orthonormal_vchar_diff_ortho a b c d hab hcd
    hpairs habOne hcdOne
  simpa only [ha, hc] using hac

/-! ## The one-set Suzuki estimate -/

/-- Pure finite-set form of the one-set Suzuki estimate.  The covered
complement is partitioned into a region of pointwise squared norm at least
one and a residual region. -/
private theorem oneCover_upper_bound10
    {Q : Type*} [Fintype Q]
    (chi : Q → ℂ) (C C₀ C₁ : Set Q)
    (hpartition : C = C₀ ∪ C₁)
    (hdisjoint : Disjoint C₀ C₁)
    (hlarge : ∀ x ∈ C₀, 1 ≤ Complex.normSq (chi x))
    (rho base : ℝ)
    (hSuzuki :
      (Nat.card Q : ℝ)⁻¹ *
          ((∑ x : Q, if x ∈ C then Complex.normSq (chi x) else 0) -
            C.ncard) + rho - base ≤ 0) :
    rho ≤ base + C₁.ncard / (Nat.card Q : ℝ) := by
  classical
  have hcard0 :
      (Finset.univ.filter (fun x : Q ↦ x ∈ C₀)).card = C₀.ncard := by
    calc
      _ = ((↑(Finset.univ.filter (fun x : Q ↦ x ∈ C₀)) : Set Q)).ncard :=
        (Set.ncard_coe_finset _).symm
      _ = C₀.ncard := by
        congr 1
        ext x
        simp
  have hmass : (C₀.ncard : ℝ) ≤
      ∑ x : Q, if x ∈ C then Complex.normSq (chi x) else 0 := by
    calc
      (C₀.ncard : ℝ) =
          ∑ x : Q, if x ∈ C₀ then (1 : ℝ) else 0 := by
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast hcard0.symm
      _ ≤
          ∑ x : Q, if x ∈ C then Complex.normSq (chi x) else 0 := by
        apply Finset.sum_le_sum
        intro x _
        by_cases hx₀ : x ∈ C₀
        · have hxC : x ∈ C := by
            rw [hpartition]
            exact Or.inl hx₀
          simp only [hx₀, hxC, if_true]
          exact hlarge x hx₀
        · by_cases hxC : x ∈ C
          · simp only [hx₀, hxC, if_false, if_true]
            exact Complex.normSq_nonneg _
          · simp [hx₀, hxC]
  have hcardC : C.ncard = C₀.ncard + C₁.ncard := by
    rw [hpartition, Set.ncard_union_eq hdisjoint]
  have hinvnonneg : (0 : ℝ) ≤ (Nat.card Q : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  have hterm :
      -(C₁.ncard / (Nat.card Q : ℝ)) ≤
        (Nat.card Q : ℝ)⁻¹ *
          ((∑ x : Q, if x ∈ C then Complex.normSq (chi x) else 0) -
            C.ncard) := by
    rw [hcardC]
    norm_num only [Nat.cast_add]
    have := mul_le_mul_of_nonneg_left
      (show -(C₁.ncard : ℝ) ≤
          (∑ x : Q, if x ∈ C then Complex.normSq (chi x) else 0) -
            ((C₀.ncard : ℝ) + C₁.ncard) by linarith)
      hinvnonneg
    simpa [div_eq_inv_mul, mul_comm, mul_left_comm] using this
  linarith

/-- Transporting a Dade hypothesis along an equality of supports does not
change the inverse Dade map. -/
private theorem invDade_transport_support10
    {G L : Subgroup Gamma} {A B : Set Gamma}
    (hAB : A = B) (ddA : DadeHypothesis G L A)
    (chi : ClassFunction G ℂ) :
    invDade (hAB ▸ ddA) chi = invDade ddA chi := by
  subst B
  rfl

/-! ## The derived-family lower bound -/

/-- The quotient image of a subgroup has the corresponding relative
index. -/
private theorem relIndex_eq_card_map_quotient10
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

/-- The second cyclic factor in the derived subgroup amplifies the odd
Frobenius quotient bound. -/
private theorem ftType345_derived_card_bound
    (MtypeP : of_typeP M U W W₁ W₂ defW) :
    2 * Nat.card W₁ * Nat.card W₂ <
      Nat.card (ftType345DerivedInM M) := by
  let K : Subgroup M := ftType345DerivedInM M
  let N : Subgroup M := (secondDerivedWithin M).subgroupOf M
  let q : M →* M ⧸ N := QuotientGroup.mk' N
  have hNnormal : N.Normal := by infer_instance
  letI : N.Normal := hNnormal
  have hNK : N ≤ K := by
    intro x hx
    change (x : Gamma) ∈ derivedWithin M
    change (x : Gamma) ∈
      (_root_.commutator (derivedWithin M)).map
        (derivedWithin M).subtype at hx
    exact Subgroup.map_subtype_le _ hx
  have hFrob :=
    FTType345ConstantsInternal.ftType345_derived_quotient_frobenius
      MtypeP
  have hoddQ : Odd (Nat.card (M ⧸ N)) :=
    odd_natCard_quotient N (mFT_odd M)
  have hbound := odd_Frobenius_index_ler
    (K.map q) ((W₁.subgroupOf M).map q) hoddQ hFrob
  have hRqCard : Nat.card ((W₁.subgroupOf M).map q) = Nat.card W₁ := by
    have hOuterM : IsInternalSemidirectProductIn
        (derivedWithin M) W₁ M := MtypeP.1.2.2.2
    let A : Subgroup M := W₁.subgroupOf M
    let f : A →* M ⧸ N := q.comp A.subtype
    have hker : f.ker = ⊥ := by
      ext x
      change (QuotientGroup.mk' N) (x : M) = 1 ↔ x = 1
      constructor
      · intro hxQ
        have hxN : (x : M) ∈ N :=
          (QuotientGroup.eq_one_iff (x : M)).mp hxQ
        have hxK : (x : M) ∈ K := hNK hxN
        have hxbot : (x : M) ∈ (⊥ : Subgroup M) := by
          exact hOuterM.2.2.2.disjoint.le_bot ⟨hxK, x.property⟩
        exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
      · intro hx
        subst x
        simp
    have hrange : f.range = A.map q := by
      dsimp [f]
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    calc
      Nat.card (A.map q) = Nat.card f.range :=
        Nat.card_congr (MulEquiv.subgroupCongr hrange.symm).toEquiv
      _ = f.ker.index := (Subgroup.index_ker f).symm
      _ = Nat.card A := by rw [hker, Subgroup.index_bot]
      _ = Nat.card W₁ :=
        MathlibSupport.natCard_subgroupOf_eq hOuterM.2.1
  have hKqCard : Nat.card (K.map q) = N.relIndex K := by
    exact (relIndex_eq_card_map_quotient10 hNnormal hNK).symm
  have hKqOne : 1 ≤ Nat.card (K.map q) := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  have hquotNat : 2 * Nat.card W₁ < Nat.card (K.map q) := by
    have hindex : (K.map q).index =
        Nat.card ((W₁.subgroupOf M).map q) :=
      hFrob.isComplement.symm.index_eq_card
    rw [hindex, hRqCard] at hbound
    have hcast : (2 * Nat.card W₁ : ℕ) < Nat.card (K.map q) := by
      norm_num only [Nat.cast_sub hKqOne, Nat.cast_mul, Nat.cast_ofNat] at hbound
      exact_mod_cast (show (2 : ℝ) * Nat.card W₁ <
          Nat.card (K.map q) by nlinarith)
    exact hcast
  have hrelMul : Nat.card (K.map q) * Nat.card N = Nat.card K := by
    rw [hKqCard]
    change (N.subgroupOf K).index * Nat.card N = Nat.card K
    simpa only [MathlibSupport.natCard_subgroupOf_eq hNK] using
      (N.subgroupOf K).index_mul_card
  have hW₂N : W₂.subgroupOf M ≤ N := by
    intro x hx
    exact MtypeP.2.2.2.1.2.2.2.1 hx
  have hW₂M : W₂ ≤ M :=
    MtypeP.2.2.2.1.2.2.1.trans (Fcore_sub M)
  have hW₂dvdN : Nat.card W₂ ∣ Nat.card N := by
    simpa only [MathlibSupport.natCard_subgroupOf_eq hW₂M] using
      Subgroup.card_dvd_of_le hW₂N
  have hW₂leN : Nat.card W₂ ≤ Nat.card N :=
    Nat.le_of_dvd Nat.card_pos hW₂dvdN
  calc
    2 * Nat.card W₁ * Nat.card W₂ <
        Nat.card (K.map q) * Nat.card W₂ :=
      Nat.mul_lt_mul_of_pos_right hquotNat Nat.card_pos
    _ ≤ Nat.card (K.map q) * Nat.card N :=
      Nat.mul_le_mul_left _ hW₂leN
    _ = Nat.card K := hrelMul

/-- An integral combination of the derived induced family that vanishes at
the identity is supported on the exact FT support used by the restricted
Dade map. -/
private theorem ftType345_derived_family_closure_supported
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (htypeMgt2 : 2 < FTtype M)
    {phi : ClassFunction M ℂ}
    (hphi : phi ∈ AddSubgroup.closure
      (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ)))
    (hoff : phi ∈ ClassFunction.supportedOn (nonidentitySet M)) :
    phi ∈ ClassFunction.supportedOn
      {x : M | (x : Gamma) ∈ FTsupport M} := by
  let K : Subgroup M := ftType345DerivedInM M
  have hKnormal : K.Normal :=
    TypeSpecInternal.derivedWithin_normal16 M
  letI : K.Normal := hKnormal
  have hphiK : phi ∈ ClassFunction.supportedOn (K : Set M) := by
    have hle : AddSubgroup.closure
        (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ)) ≤
        (ClassFunction.supportedOn (K : Set M)).toAddSubgroup := by
      apply (AddSubgroup.closure_le _).mpr
      intro psi hpsi
      exact seqInd_on K hpsi
    exact hle hphi
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hx
  by_cases hxK : x ∈ K
  · by_cases hxOne : x = 1
    · exact ClassFunction.eq_zero_of_mem_supportedOn hoff (by simpa [hxOne])
    · exfalso
      apply hx
      have hxDerived : (x : Gamma) ∈ subgroupNonidentity (derivedWithin M) :=
        ⟨hxK, fun hx ↦ hxOne (Subtype.ext hx)⟩
      rw [FTsupp_eq1 hmaxM htypeMgt2,
        FTsupp1_type_gt2 M htypeMgt2]
      exact hxDerived
  · exact ClassFunction.eq_zero_of_mem_supportedOn hphiK hxK

/-! ## The type-II partner support -/

private theorem reducedColumn_mem_fullDerivedFamily10
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    (ftType345PrimeTI MtypeP).primeTIRed
        (ftType345IsoM MtypeP) j ∈
      ftType345InducedFamily10 M := by
  let K : Subgroup M := ftType345DerivedInM M
  apply (seqIndC1P (k := ℂ) K).mpr
  refine ⟨(ftType345PrimeTI MtypeP).primeTI_Ires
      (ftType345IsoM MtypeP) j, ?_, ?_⟩
  · intro htriv
    apply hj
    apply (ftType345PrimeTI MtypeP).prTIres_inj
      (ftType345IsoM MtypeP)
    exact htriv.trans
      ((ftType345PrimeTI MtypeP).prTIres0
        (ftType345IsoM MtypeP)).symm
  · exact ((ftType345PrimeTI MtypeP).cfInd_prTIres
      (ftType345IsoM MtypeP) j).symm

/-- Source `Frob_der1_type2`. -/
private theorem ftType345_Frob_der1_type2
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype2 : FTtype M ≠ 2)
    (zeta : ClassFunction M ℂ)
    (hzeta : FTType345ReferenceChoice M W₁ zeta)
    (tau₁ : ClassFunction M ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup Gamma) ℂ)
    (hcoh : coherent_with
      (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ))
      (nonidentitySet M) (ftType345Tau hmaxM) tau₁)
    {S V : Subgroup Gamma}
    (hmaxS : S ∈ minSimple_max_groups (G := Gamma))
    (xdefW : IsInternalDirectProductIn W₂ W₁ W)
    (StypeP : of_typeP S V W W₂ W₁ xdefW)
    (hStype2 : FTtype S = 2) :
    IsFrobeniusIn (Fitting_core S) V (derivedWithin S) := by
  classical
  let ctxS : PTypeFCoreContext S V W W₂ W₁ :=
    Ptype_Fcore_context hmaxS xdefW StypeP (by omega)
  let factsS := Ptype_Fcore_factor_facts ctxS
  let D := Ptype_factor_action ctxS factsS
  let HU := pTypeHUInMaximal S (derivedWithin S)
  let H := pTypeHInDerived S (derivedWithin S) (Fitting_core S)
  let H₀ := pTypeH0InDerived S (derivedWithin S)
    (Ptype_Fcore_kernel ctxS)
  let H₀C := pTypeH0CInDerived S (derivedWithin S)
    (Ptype_Fcore_kernel ctxS) V W₂ D
  let H₀CPrime := pTypeH0CPrimeInDerived S (derivedWithin S)
    (Ptype_Fcore_kernel ctxS) V W₂ D
  let actionCard := pTypeActionFactorCard D
  letI : H₀.Normal := pTypeH0InDerived_normal ctxS
  have hcases := typeP_reducible_core_cases
    S V W W₂ W₁ xdefW hmaxS StypeP (by omega)
  rcases hcases with hInduced | hFull
  · obtain ⟨lambda, hlambdaPrime, hlambdaDegree, xi, hxiLinear,
        hlambdaInduced⟩ := hInduced
    have hlambdaLayer : (lambda : ClassFunction S ℂ) ∈
        seqIndD (k := ℂ) HU H ⊥ :=
      seqIndS HU
        (Iirr_kerDS (k := ℂ)
          (A₁ := H₀CPrime) (A₂ := ⊥)
          (B₁ := H) (B₂ := H) bot_le le_rfl) hlambdaPrime
    have hlambdaFull : (lambda : ClassFunction S ℂ) ∈
        seqIndD (k := ℂ) HU ⊤ ⊥ :=
      seqIndS HU
        (Iirr_kerDS (k := ℂ)
          (A₁ := H₀CPrime) (A₂ := ⊥)
          (B₁ := H) (B₂ := ⊤) bot_le le_top) hlambdaPrime
    have hred := typeP_reducible_core_Ind
      S V W W₂ W₁ xdefW hmaxS StypeP (by omega)
    obtain ⟨nu, hnuRed⟩ := hred.2.1
    obtain ⟨r, hrErase, hnuEq⟩ :=
      Finset.mem_image.mp (hred.2.2.1 hnuRed)
    have hr : r ≠
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ) :=
      (Finset.mem_erase.mp hrErase).1
    have hnuFacts := hred.2.2.2 nu hnuRed
    have hnuDegree : nu 1 = ((D.q * actionCard : ℕ) : ℂ) := hnuFacts.1
    have hnuKernelRaw : nu ∈ seqIndD (k := ℂ) HU H H₀C :=
      hnuFacts.2.1
    have hnuLayer : nu ∈ seqIndD (k := ℂ) HU H ⊥ :=
      seqIndS HU
        (Iirr_kerDS (k := ℂ)
          (A₁ := H₀C) (A₂ := ⊥)
          (B₁ := H) (B₂ := H) bot_le le_rfl) hnuKernelRaw
    let pdS := FT_prDade_hypF xdefW hmaxS StypeP
    let isoS :=
      pdS.prDade_prTI.prime_cycTIhyp.cyclicTIIsometryData (k := ℂ)
    let isoGS := pdS.prDade_cycTI.cyclicTIIsometryData (k := ℂ)
    have hlambdaKernel : (lambda : ClassFunction S ℂ) ∈
        FTtypePKernelLayer pdS := by
      change (lambda : ClassFunction S ℂ) ∈ seqIndD (k := ℂ) HU H ⊥
      exact hlambdaLayer
    have hnuKernel : nu ∈ FTtypePKernelLayer pdS := by
      change nu ∈ seqIndD (k := ℂ) HU H ⊥
      exact hnuLayer
    have hlambdaInvKernel :
        ClassFunction.inverseLinear (lambda : ClassFunction S ℂ) ∈
          FTtypePKernelLayer pdS := by
      change ClassFunction.inverseLinear (lambda : ClassFunction S ℂ) ∈
        seqIndD (k := ℂ) ((derivedWithin S).subgroupOf S)
          pdS.signalizerInKernel ⊥
      exact seqInd_inverse_mem (k := ℂ)
        ((derivedWithin S).subgroupOf S) pdS.signalizerInKernel ⊥
        hlambdaKernel
    have hnuInvKernel : ClassFunction.inverseLinear nu ∈
        FTtypePKernelLayer pdS := by
      change ClassFunction.inverseLinear nu ∈
        seqIndD (k := ℂ) ((derivedWithin S).subgroupOf S)
          pdS.signalizerInKernel ⊥
      exact seqInd_inverse_mem (k := ℂ)
        ((derivedWithin S).subgroupOf S) pdS.signalizerInKernel ⊥
        hnuKernel
    let calT₂ : Set (ClassFunction S ℂ) :=
      {(lambda : ClassFunction S ℂ),
        ClassFunction.inverseLinear (lambda : ClassFunction S ℂ),
        nu, ClassFunction.inverseLinear nu}
    have hcalT₂sub : cfConjC_subset calT₂
        (FTtypePKernelLayer pdS) := by
      constructor
      · intro phi hphi
        simp only [calT₂, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hphi
        rcases hphi with rfl | rfl | rfl | rfl
        · exact hlambdaKernel
        · exact hlambdaInvKernel
        · exact hnuKernel
        · exact hnuInvKernel
      · intro phi hphi
        simp only [calT₂, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hphi ⊢
        rcases hphi with rfl | rfl | rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl
            (inverseLinear_involutive10 (lambda : ClassFunction S ℂ))
        · exact Or.inr (Or.inr (Or.inr rfl))
        · exact Or.inr (Or.inr (Or.inl
            (inverseLinear_involutive10 nu)))
    have hlambdaInvDegree :
        ClassFunction.inverseLinear (lambda : ClassFunction S ℂ) 1 =
          ((D.q * actionCard : ℕ) : ℂ) := by
      rw [ClassFunction.inverseLinear_apply, inv_one, hlambdaDegree]
    have hnuInvDegree : ClassFunction.inverseLinear nu 1 =
        ((D.q * actionCard : ℕ) : ℂ) := by
      rw [ClassFunction.inverseLinear_apply, inv_one, hnuDegree]
    have hcalT₂each : ∀ chi ∈ calT₂,
        chi 1 = ((D.q * actionCard : ℕ) : ℂ) := by
      intro chi hchi
      simp only [calT₂, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hchi
      rcases hchi with rfl | rfl | rfl | rfl
      · exact hlambdaDegree
      · exact hlambdaInvDegree
      · exact hnuDegree
      · exact hnuInvDegree
    have hcalT₂degree : ∀ chi ∈ calT₂, ∀ psi ∈ calT₂,
        chi 1 = psi 1 := by
      intro chi hchi psi hpsi
      exact (hcalT₂each chi hchi).trans (hcalT₂each psi hpsi).symm
    have hcoherentT₂ : coherent calT₂ (nonidentitySet S)
        (Dade (FT_Dade0_hyp S hmaxS)) := by
      apply uniform_degree_coherence
        (subset_subcoherent
          (FTtypeP_subcoherent pdS isoS isoGS (mFT_odd S))
          hcalT₂sub)
      exact hcalT₂degree
    obtain ⟨tau₂, hcoh₂⟩ := hcoherentT₂
    have hlambdaT₂ : (lambda : ClassFunction S ℂ) ∈ calT₂ := by
      simp [calT₂]
    have hlambdaInvT₂ :
        ClassFunction.inverseLinear (lambda : ClassFunction S ℂ) ∈
          calT₂ := by
      simp [calT₂]
    have hnuT₂ : nu ∈ calT₂ := by simp [calT₂]
    have hmuST₂ : pdS.prDade_prTI.primeTIRed isoS r ∈ calT₂ := by
      rw [hnuEq]
      exact hnuT₂
    have hnuCases := FTtypeP_coherent_TIred pdS isoS isoGS
      (mFT_odd S) calT₂ tau₂ lambda r hcalT₂sub hcoh₂
        hlambdaT₂ hmuST₂

    have htypeMgt2 : 2 < FTtype M := by
      have hnot1 := FTtypeP_neq1 M U W W₁ W₂ defW hmaxM MtypeP
      have hrange := FTtype_range M
      omega
    have hnotConj : ¬ FTAmbientConjugate M S := by
      rintro ⟨g, hSmap⟩
      have htype : FTtype S = FTtype M := by
        rw [hSmap]
        exact FTtypeJ M g
      exact notMtype2 (htype.symm.trans hStype2)
    have hnoSupport : ¬ ∃ g : Gamma,
        FTsupports M (conjugateSubgroup8 S g) := by
      rintro ⟨g, hsupp⟩
      let L : Subgroup Gamma := conjugateSubgroup8 S g
      have hmaxL : L ∈ minSimple_max_groups (G := Gamma) := by
        simpa only [L, conjugateSubgroup8] using
          (mmaxJ S (MulAut.conj g)).2 hmaxS
      have hLtype2 : FTtype L = 2 := by
        calc
          FTtype L = FTtype S := by
            simpa only [L, conjugateSubgroup8, conjugateSubgroup16] using
              FTtypeJ S g
          _ = 2 := hStype2
      rcases hsupp with ⟨y, hyM, hCyM, hCyL⟩
      have hyOuter : y ∈ outerExceptionalSet M (FTsupport0 M) :=
        ⟨FTsupp_sub0 M hyM, hCyM⟩
      let data := (FTsupport_facts M hmaxM).element_data y hyOuter
      have hLmem : L ∈ minSimple_max_groups_of (G := Gamma)
          (elementCentralizer y : Set Gamma) := ⟨hmaxL, hCyL⟩
      have hLN : L = elementNormalizer15 y := by
        rw [data.unique_maximal_centralizer] at hLmem
        exact Set.mem_singleton_iff.mp hLmem
      have hNtype2 : FTtype (elementNormalizer15 y) = 2 := by
        rw [← hLN]
        exact hLtype2
      let fdata := data.typeTwo_frobenius hNtype2
      have hFrobM := summaryFrobeniusData_isFrobeniusIn10 fdata
      exact (typePF_exclusion M U W W₁ W₂ fdata.complement
        defW MtypeP) (Frobenius_of_typeF M fdata.complement hFrobM)
    have hdisExplicit : Disjoint (FT_Dade1_support M)
        (FT_Dade_full_support S) := by
      by_contra hnotDis
      exact hnoSupport
        ((FT_Dade_support_disjoint hmaxM hmaxS hnotConj).2.1.mpr hnotDis)
    have hdis : Disjoint
        (Dade_support (FT_Dade1_hyp M hmaxM))
        (Dade_support (FT_Dade_hyp S hmaxS)) := by
      rw [FT_Dade1_supportE M hmaxM, FT_Dade_supportE S hmaxS]
      exact hdisExplicit

    let pdM := ftType345PrimeDade hmaxM MtypeP
    have hfullMsub : cfConjC_subset
        (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ))
        (FTtypePKernelLayer pdM) := by
      have hcore : FTcore M = derivedWithin M :=
        FTcore_type_gt2 M htypeMgt2
      constructor
      · intro phi hphi
        simpa [ftType345InducedFamily10, FTtypePKernelLayer,
          PrimeDadeHypothesis.signalizerInKernel, pdM, hcore] using hphi
      · intro phi hphi
        exact seqInd_inverse_mem (k := ℂ) (ftType345DerivedInM M)
          (⊤ : Subgroup (ftType345DerivedInM M)) ⊥ hphi
    have hcohM₁ : coherent_with
        (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ))
        (nonidentitySet M) (Dade (FT_Dade1_hyp M hmaxM)) tau₁ := by
      refine
        { isometry := hcoh.isometry
          mapsToVirtual := hcoh.mapsToVirtual
          agrees := ?_ }
      intro phi hphi hoff
      have hsupport := kernelLayer_closure_supportedOn_dadeSet10
        pdM hfullMsub.1 hphi hoff
      have hsupport₁ : phi ∈ ClassFunction.supportedOn
          {x : M | (x : Gamma) ∈ FTsupport1 M} := by
        simpa only [FTsupp_eq1 hmaxM htypeMgt2] using hsupport
      exact (hcoh.agrees phi hphi hoff).trans
        (FT_Dade1E M hmaxM phi hsupport₁).symm
    have hcohSFull : coherent_with calT₂ (nonidentitySet S)
        (Dade (FT_Dade_hyp S hmaxS)) tau₂ := by
      refine
        { isometry := hcoh₂.isometry
          mapsToVirtual := hcoh₂.mapsToVirtual
          agrees := ?_ }
      intro phi hphi hoff
      have hsupport := kernelLayer_closure_supportedOn_dadeSet10
        pdS hcalT₂sub.1 hphi hoff
      exact (hcoh₂.agrees phi hphi hoff).trans
        (FT_DadeE S hmaxS phi hsupport).symm
    let KM : Subgroup M := ftType345DerivedInM M
    let KS : Subgroup S := HU
    letI : KM.Normal := by infer_instance
    letI : KS.Normal := by infer_instance
    let zetaIrr : IrreducibleCharacter M ℂ := ⟨zeta, hzeta.irreducible⟩
    have hzetaDual :
        (IrreducibleCharacter.dual zetaIrr : ClassFunction M ℂ) ∈
          ftType345InducedFamily10 M := by
      simpa only [zetaIrr, ftType345InducedFamily10,
        ← ClassFunction.inverseLinear_irreducible] using
        seqInd_inverse_mem (k := ℂ) (ftType345DerivedInM M)
          (⊤ : Subgroup (ftType345DerivedInM M)) ⊥ hzeta.mem_calS
    have hlambdaDual :
        (IrreducibleCharacter.dual lambda : ClassFunction S ℂ) ∈
          calT₂ := by
      simpa only [← ClassFunction.inverseLinear_irreducible] using
        hlambdaInvT₂
    have hZetaLambda : characterPairing (tau₁ zeta)
        (tau₂ (lambda : ClassFunction S ℂ)) = 0 := by
      exact disjoint_coherent_pair_ortho10
        (FT_Dade1_hyp M hmaxM) (FT_Dade_hyp S hmaxS)
        (FTsupp1_type_gt2 M htypeMgt2) hdis
        KM KS
        (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ))
        calT₂ tau₁ tau₂ hcohM₁ hcohSFull zetaIrr lambda
        hzeta.mem_calS hzetaDual hlambdaT₂ hlambdaDual
        hzeta.mem_calS hlambdaFull

    have hEtaSwap (i : IrreducibleCharacter W₁ ℂ)
        (j : IrreducibleCharacter W₂ ℂ) :
        ftType345Eta hmaxM MtypeP i j =
          isoGS.cyclicTIImage (j, i) := by
      simpa only [ftType345Eta,
        CyclicTIIsometryData.cyclicTIImage,
        CyclicTIIsometryData.cyclicTISourceIrreducible,
        CyclicTIHypothesis.cyclicTIIsometry] using
        (CyclicTIHypothesis.cycTIisoC defW xdefW
          (ftType345PrimeDade hmaxM MtypeP).prDade_cycTI
          pdS.prDade_cycTI i j)
    have hZetaEta (i : IrreducibleCharacter W₁ ℂ)
        (j : IrreducibleCharacter W₂ ℂ) :
        characterPairing (tau₁ zeta)
          (ftType345Eta hmaxM MtypeP i j) = 0 := by
      simpa only [ftType345Eta,
        CyclicTIIsometryData.cyclicTIImage,
        CyclicTIIsometryData.cyclicTISourceIrreducible] using
        coherent_ortho_cycTIiso pdM (ftType345IsoM MtypeP)
          (ftType345IsoG hmaxM MtypeP) (mFT_odd M)
          hfullMsub hcoh hzeta.mem_calS hzeta.irreducible
          (IrreducibleCharacter.cyclicTICharacter defW i j)
    have hSEtaLambda (j : IrreducibleCharacter W₂ ℂ)
        (i : IrreducibleCharacter W₁ ℂ) :
        characterPairing (isoGS.cyclicTIImage (j, i))
          (tau₂ (lambda : ClassFunction S ℂ)) = 0 := by
      rw [characterPairing_comm]
      simpa only [CyclicTIIsometryData.cyclicTIImage,
        CyclicTIIsometryData.cyclicTISourceIrreducible] using
        coherent_ortho_cycTIiso pdS isoS isoGS (mFT_odd S)
          hcalT₂sub hcoh₂ hlambdaT₂ lambda.property
          (IrreducibleCharacter.cyclicTICharacter xdefW j i)

    letI : IsCyclic W₂ := (ftType345PrimeTI MtypeP).fixed_cyclic
    obtain ⟨s, hs⟩ :=
      IrreducibleCharacter.exists_ne_trivial_of_one_lt_card
        (k := ℂ) (ftType345PrimeTI MtypeP).prime_cycTIhyp.one_lt_card_right
    let muM : ClassFunction M ℂ :=
      (ftType345PrimeTI MtypeP).primeTIRed
        (ftType345IsoM MtypeP) s
    have hmuExpansion : tau₁ muM =
        (FTtype345_TIsign MtypeP : ℂ) •
          ∑ i : IrreducibleCharacter W₁ ℂ,
            ftType345Eta hmaxM MtypeP i s := by
      simpa only [muM] using
        FTType345CoherenceInternal.ftType345_tau1mu
          hmaxM MtypeP notMtype2 zeta hzeta tau₁ hcoh s hs
    obtain ⟨r₀, cS, hcS, hnuExpansion⟩ :
        ∃ r₀ : IrreducibleCharacter W₁ ℂ, ∃ cS : ℂ,
          cS ≠ 0 ∧ tau₂ nu = cS •
            ∑ j : IrreducibleCharacter W₂ ℂ,
              isoGS.cyclicTIImage (j, r₀) := by
      rcases hnuCases with hfirst | hsecond
      · refine ⟨r,
          (pdS.prDade_prTI.primeTISign isoS r : ℂ), ?_, ?_⟩
        · exact Int.cast_ne_zero.mpr
            (isSign_ne_zero
              (pdS.prDade_prTI.primeTISign_isSign isoS r))
        · rw [← hnuEq]
          exact hfirst
      · refine ⟨IrreducibleCharacter.dual r,
          -(pdS.prDade_prTI.primeTISign isoS r : ℂ), ?_, ?_⟩
        · exact neg_ne_zero.mpr (Int.cast_ne_zero.mpr
            (isSign_ne_zero
              (pdS.prDade_prTI.primeTISign_isSign isoS r)))
        · rw [← hnuEq]
          exact hsecond.1
    have hZetaRow (r' : IrreducibleCharacter W₁ ℂ) :
        characterPairing (tau₁ zeta)
          (∑ j : IrreducibleCharacter W₂ ℂ,
            isoGS.cyclicTIImage (j, r')) = 0 := by
      rw [pairing_fintype_sum_right10]
      apply Finset.sum_eq_zero
      intro j _
      rw [← hEtaSwap r' j]
      exact hZetaEta r' j
    have hColumnLambda :
        characterPairing
          (∑ i : IrreducibleCharacter W₁ ℂ,
            ftType345Eta hmaxM MtypeP i s)
          (tau₂ (lambda : ClassFunction S ℂ)) = 0 := by
      rw [pairing_fintype_sum_left10]
      apply Finset.sum_eq_zero
      intro i _
      rw [hEtaSwap i s]
      exact hSEtaLambda s i
    have hMuLambda : characterPairing (tau₁ muM)
        (tau₂ (lambda : ClassFunction S ℂ)) = 0 := by
      rw [hmuExpansion, characterPairing_smul_left,
        hColumnLambda, mul_zero]
    have hZetaNu : characterPairing (tau₁ zeta) (tau₂ nu) = 0 := by
      rw [hnuExpansion, characterPairing_smul_right,
        hZetaRow r₀, mul_zero]

    let d := FTtype345_TIirr_degree MtypeP
    let alpha : ClassFunction M ℂ := muM - (d : ℂ) • zeta
    let beta : ClassFunction S ℂ := nu - (lambda : ClassFunction S ℂ)
    have hmuMmem : muM ∈ ftType345InducedFamily10 M := by
      exact reducedColumn_mem_fullDerivedFamily10 MtypeP s hs
    have hAlphaClosure : alpha ∈ AddSubgroup.closure
        (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ)) := by
      dsimp only [alpha]
      apply (AddSubgroup.closure
        (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ))).sub_mem
      · exact AddSubgroup.subset_closure hmuMmem
      · simpa only [Nat.cast_smul_eq_nsmul] using
          (AddSubgroup.closure
            (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ))).nsmul_mem
            (AddSubgroup.subset_closure hzeta.mem_calS) d
    have hAlphaOff : alpha ∈
        ClassFunction.supportedOn (nonidentitySet M) := by
      dsimp only [alpha]
      apply sub_supported_of_one_eq10
      dsimp only [muM, d]
      simp only [ClassFunction.smul_apply, smul_eq_mul]
      rw [(ftType345PrimeTI MtypeP).prTIred_1
        (ftType345IsoM MtypeP) s,
        (FTtype345_constants hmaxM MtypeP notMtype2).degree_constant
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ)
          s hs,
        hzeta.degree]
      ring
    have hBetaClosure : beta ∈ AddSubgroup.closure calT₂ := by
      exact (AddSubgroup.closure calT₂).sub_mem
        (AddSubgroup.subset_closure hnuT₂)
        (AddSubgroup.subset_closure hlambdaT₂)
    have hBetaOff : beta ∈
        ClassFunction.supportedOn (nonidentitySet S) := by
      dsimp only [beta]
      apply sub_supported_of_one_eq10
      rw [hnuDegree, hlambdaDegree]
    have hAlphaBeta : characterPairing (tau₁ alpha) (tau₂ beta) = 0 := by
      rw [hcohM₁.agrees alpha hAlphaClosure hAlphaOff,
        hcohSFull.agrees beta hBetaClosure hBetaOff]
      exact disjoint_Dade_ortho_left10
        (FT_Dade1_hyp M hmaxM) (FT_Dade_hyp S hmaxS)
          (FTsupp1_type_gt2 M htypeMgt2) hdis alpha beta
    have hMuNuZero : characterPairing (tau₁ muM) (tau₂ nu) = 0 := by
      have h := hAlphaBeta
      dsimp only [alpha, beta] at h
      rw [map_sub, map_smul, map_sub, pairing_sub_left10,
        pairing_sub_right10, pairing_sub_right10,
        characterPairing_smul_left, characterPairing_smul_left,
        hMuLambda, hZetaNu,
        hZetaLambda] at h
      simpa using h
    have hsumPair : characterPairing
        (∑ i : IrreducibleCharacter W₁ ℂ,
          ftType345Eta hmaxM MtypeP i s)
        (∑ j : IrreducibleCharacter W₂ ℂ,
          isoGS.cyclicTIImage (j, r₀)) = 1 := by
      calc
        characterPairing
            (∑ i : IrreducibleCharacter W₁ ℂ,
              ftType345Eta hmaxM MtypeP i s)
            (∑ j : IrreducibleCharacter W₂ ℂ,
              isoGS.cyclicTIImage (j, r₀)) =
            ∑ i : IrreducibleCharacter W₁ ℂ,
              ∑ j : IrreducibleCharacter W₂ ℂ,
                characterPairing
                  (ftType345Eta hmaxM MtypeP i s)
                  (isoGS.cyclicTIImage (j, r₀)) := by
              rw [pairing_fintype_sum_left10]
              apply Finset.sum_congr rfl
              intro i _
              rw [pairing_fintype_sum_right10]
        _ = ∑ i : IrreducibleCharacter W₁ ℂ,
              ∑ j : IrreducibleCharacter W₂ ℂ,
                if (i, s) = (r₀, j) then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              rw [← hEtaSwap r₀ j]
              simpa only [ftType345Eta] using
                (ftType345IsoG hmaxM MtypeP).characterPairing_cyclicTIImage
                  (i, s) (r₀, j)
        _ = 1 := by
              rw [Finset.sum_eq_single r₀]
              · simp
              · intro i _ hi
                simp [hi]
              · simp
    have hcM : (FTtype345_TIsign MtypeP : ℂ) ≠ 0 := by
      exact Int.cast_ne_zero.mpr
        (isSign_ne_zero
          ((ftType345PrimeTI MtypeP).primeTISign_isSign
            (ftType345IsoM MtypeP) (FTtype345_jOne MtypeP)))
    rw [hmuExpansion, hnuExpansion, characterPairing_smul_left,
      characterPairing_smul_right, hsumPair] at hMuNuZero
    exact ((mul_ne_zero hcM hcS) (by simpa using hMuNuZero)).elim
  · letI : IsCyclic V := hFull.2.2.1
    have hII := compl_of_typeII S V W W₂ W₁ xdefW
      hmaxS StypeP hStype2
    have hZ : IsZGroup8 V := by
      intro p hp P
      exact Subgroup.isCyclic_of_le le_top
    have hFrob : IsFrobeniusIn (Fitting_core (derivedWithin S)) V
        (derivedWithin S) :=
      (typeF_context (derivedWithin S) V
        hII.2.2.2.1).frobenius_iff_zgroup.mpr hZ
    rwa [hII.2.2.2.2] at hFrob

/-- Every element whose order is not coprime to `|W₁|` is conjugate either
to a nonidentity element of the type-II partner's Fitting core or to the
cyclic-TI rectangle. -/
private theorem ftType345_partner_nonCoprime_support
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    {S V : Subgroup Gamma}
    (hmaxS : S ∈ minSimple_max_groups (G := Gamma))
    (xdefW : IsInternalDirectProductIn W₂ W₁ W)
    (StypeP : of_typeP S V W W₂ W₁ xdefW)
    (hStype2 : FTtype S = 2)
    (hFrobS : IsFrobeniusIn (Fitting_core S) V (derivedWithin S))
    {x : Gamma}
    (hxnoncop : ¬ Nat.Coprime (orderOf x) (Nat.card W₁)) :
    x ∈ classSupportWithin (⊤ : Subgroup Gamma)
          (subgroupNonidentity (Fitting_core S)) ∪
        classSupportWithin (⊤ : Subgroup Gamma)
          (cyclicTISet W W₁ W₂) := by
  obtain ⟨p, hp, hpOrder, hpW₁⟩ :=
    Nat.Prime.not_coprime_iff_dvd.mp hxnoncop
  letI : Fact p.Prime := ⟨hp⟩
  let m : ℕ := orderOf x / p
  let a : Gamma := x ^ m
  have haOrder : orderOf a = p := by
    exact orderOf_pow_orderOf_div (orderOf_pos x).ne' hpOrder
  have haOne : a ≠ 1 := by
    intro ha
    have : orderOf a = 1 := orderOf_eq_one_iff.mpr ha
    rw [haOrder] at this
    exact hp.ne_one this
  have haP : IsPElement p a := by
    refine ⟨1, ?_⟩
    simpa [haOrder] using pow_orderOf_eq_one a
  have hpH : p ∈ primeSupport (Nat.card (Fitting_core S)) := by
    refine ⟨hp, hpW₁.trans ?_⟩
    exact Subgroup.card_dvd_of_le StypeP.2.2.2.1.2.2.1
  let PH : Sylow p (Fitting_core S) := Classical.choice Sylow.nonempty
  obtain ⟨PG, hPG⟩ := FTContextInternal.exists_sylow_eq_map_of_sylow_hall8 hp
    (FTcore_facts S hmaxS).fittingCore_hall_G hpH PH
  have hPGH : (PG : Subgroup Gamma) ≤ Fitting_core S := by
    rw [hPG]
    exact Subgroup.map_subtype_le _
  have hAp : IsPGroup p (Subgroup.zpowers a) := haP.zpowers_isPGroup
  obtain ⟨P, hAP⟩ := hAp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Gamma P PG
  let e : Gamma ≃* Gamma := MulAut.conj g
  let ac : Gamma := e a
  let xc : Gamma := e x
  have hPmap : (P : Subgroup Gamma).map e.toMonoidHom =
      (PG : Subgroup Gamma) := by
    change ((g • P : Sylow p Gamma) : Subgroup Gamma) = _
    exact congrArg (fun T : Sylow p Gamma ↦ (T : Subgroup Gamma)) hg
  have hacH : ac ∈ Fitting_core S := by
    have haA : a ∈ Subgroup.zpowers a := Subgroup.mem_zpowers a
    have haMap : e a ∈ (Subgroup.zpowers a).map e.toMonoidHom :=
      Subgroup.mem_map_of_mem e.toMonoidHom haA
    have hmaple : (Subgroup.zpowers a).map e.toMonoidHom ≤
        (PG : Subgroup Gamma) := by
      rw [← hPmap]
      exact Subgroup.map_mono hAP
    exact hPGH (hmaple haMap)
  have hacOne : ac ≠ 1 := by
    simpa only [map_one] using e.injective.ne haOne
  have hax : Commute a x := by
    dsimp only [a]
    exact (Commute.refl x).pow_left m
  have hacxc : Commute ac xc := hax.map e.toMonoidHom
  have hTI : IsNormalizedTI (subgroupNonidentity (Fitting_core S))
      (⊤ : Subgroup Gamma) S := by
    have h := (FTtypeII_ker_TI S hmaxS hStype2).2.2
    rwa [FTsupp1_type2 S hStype2] at h
  have hxcS : xc ∈ S := by
    apply hTI.centralizerWithin_zpowers_le ⟨hacH, hacOne⟩
    refine ⟨Subgroup.mem_top xc, ?_⟩
    intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (hacxc.zpow_left n).eq
  have hxOne : x ≠ 1 := by
    intro hx
    subst x
    exact hxnoncop (by simp)
  have hxcOne : xc ≠ 1 := by
    simpa only [map_one] using e.injective.ne hxOne
  by_cases hxcDerived : xc ∈ derivedWithin S
  · left
    have hxcH : xc ∈ Fitting_core S := by
      apply centralizer_frobeniusIn_kernel_le10 hFrobS hacH hacOne
      refine ⟨hxcDerived, ?_⟩
      intro z hz
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact (hacxc.zpow_left n).eq
    refine ⟨xc, ⟨hxcH, hxcOne⟩, g, Subgroup.mem_top g, ?_⟩
    dsimp only [xc, e]
    simp only [MulAut.conj_apply]
    group
  · right
    have hxcNotSupport : xc ∉ FTsupport S := by
      intro hsupport
      simp only [FTsupport, ftSupport, Set.mem_iUnion] at hsupport
      rcases hsupport with ⟨y, -, hxy⟩
      apply hxcDerived
      simpa [FTder, ftDerived, show FTtype S ≠ 1 by omega] using hxy.1.1
    have hpiNot : ¬ IsPiNumber
        (primeSupport (Nat.card (derivedWithin S))) (orderOf xc) := by
      intro hpi
      let DS : Subgroup S := (derivedWithin S).subgroupOf S
      have houter := StypeP.1.2.2.2
      have hDSnormal : DS.Normal := TypeSpecInternal.derivedWithin_normal16 S
      have hDScop : Nat.Coprime (Nat.card DS) DS.index := by
        have hindex : DS.index = Nat.card W₂ := by
          rw [houter.2.2.2.symm.index_eq_card,
            MathlibSupport.natCard_subgroupOf_eq houter.2.1]
        rw [hindex, MathlibSupport.natCard_subgroupOf_eq houter.1]
        have hcop := StypeP.1.2.1.2.coprime_card_index.symm
        rw [houter.2.2.2.index_eq_card,
          MathlibSupport.natCard_subgroupOf_eq houter.1,
          MathlibSupport.natCard_subgroupOf_eq houter.2.1] at hcop
        exact hcop
      have hHallDS : IsHall (primeSupport (Nat.card DS)) DS :=
        isHall_primeSupport DS hDScop
      have hxcDS : (⟨xc, hxcS⟩ : S) ∈ DS := by
        let A : Subgroup S := Subgroup.zpowers ⟨xc, hxcS⟩
        have hApi : IsPiNumber (primeSupport (Nat.card DS)) (Nat.card A) := by
          rw [Nat.card_zpowers]
          rw [MathlibSupport.natCard_subgroupOf_eq houter.1]
          simpa only [← Subgroup.orderOf_coe ⟨xc, hxcS⟩] using hpi
        exact FTContextInternal.isPiNumber_le_normal_isHall8
          hDSnormal hHallDS hApi
          (Subgroup.mem_zpowers (⟨xc, hxcS⟩ : S))
      exact hxcDerived hxcDS
    have hpDerived : p ∈ primeSupport (Nat.card (derivedWithin S)) := by
      refine ⟨hp, hpW₁.trans ?_⟩
      exact Subgroup.card_dvd_of_le
        (StypeP.2.2.2.1.2.2.1.trans StypeP.2.1.2.2.2.1)
    have hpOrderXc : p ∣ orderOf xc := by
      have horder : orderOf xc = orderOf x :=
        orderOf_injective e.toMonoidHom e.injective x
      rw [horder]
      exact hpOrder
    have hpiComplNot : ¬ IsPiNumber
        (primeSupport (Nat.card (derivedWithin S)))ᶜ (orderOf xc) := by
      intro hpi
      exact (hpi hp hpOrderXc) hpDerived
    have hxcSupport0 : xc ∈ FTsupport0 S := by
      right
      simpa [FTder, ftDerived, show FTtype S ≠ 1 by omega] using
        (show xc ∈ S ∧
            ¬ IsPiNumber (primeSupport (Nat.card (derivedWithin S)))
              (orderOf xc) ∧
            ¬ IsPiNumber (primeSupport (Nat.card (derivedWithin S)))ᶜ
              (orderOf xc) from ⟨hxcS, hpiNot, hpiComplNot⟩)
    have hclassS : xc ∈ classSupportWithin S
        (cyclicTISet W W₂ W₁) := by
      have hdiff : xc ∈ FTsupport0 S \ FTsupport S :=
        ⟨hxcSupport0, hxcNotSupport⟩
      rw [FTsupp0_typeP S V W₂ W₁ W xdefW hmaxS StypeP] at hdiff
      simpa only [cyclicTISet] using hdiff
    rcases hclassS with ⟨v, hv, y, hyS, hy⟩
    refine ⟨v, ?_, y * g, Subgroup.mem_top (y * g), ?_⟩
    simpa only [cyclicTISet_swap] using hv
    change (y * g)⁻¹ * v * (y * g) = x
    calc
      (y * g)⁻¹ * v * (y * g) = g⁻¹ * (y⁻¹ * v * y) * g := by group
      _ = g⁻¹ * xc * g := by
        simpa only using congrArg (fun z : Gamma ↦ g⁻¹ * z * g) hy
      _ = x := by
        dsimp only [xc, e]
        simp only [MulAut.conj_apply]
        group

/-- Counting consequence of the preceding support inclusion. -/
private theorem ftType345_partner_nonCoprime_support_bound
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    {S V : Subgroup Gamma}
    (hmaxS : S ∈ minSimple_max_groups (G := Gamma))
    (xdefW : IsInternalDirectProductIn W₂ W₁ W)
    (StypeP : of_typeP S V W W₂ W₁ xdefW)
    (hStype2 : FTtype S = 2)
    (hFrobS : IsFrobeniusIn (Fitting_core S) V (derivedWithin S))
    (G₁ : Set (⊤ : Subgroup Gamma))
    (hG₁ : ∀ g ∈ G₁,
      ¬ Nat.Coprime (orderOf g) (Nat.card W₁)) :
    G₁.ncard / (Nat.card Gamma : ℝ) ≤
      (Nat.card (Fitting_core S) : ℝ) / (Nat.card S : ℝ) +
        (cyclicTISet W W₁ W₂).ncard / (Nat.card W : ℝ) := by
  let SH : Set (⊤ : Subgroup Gamma) :=
    {g | (g : Gamma) ∈ classSupportWithin (⊤ : Subgroup Gamma)
      (subgroupNonidentity (Fitting_core S))}
  let SW : Set (⊤ : Subgroup Gamma) :=
    {g | (g : Gamma) ∈ classSupportWithin (⊤ : Subgroup Gamma)
      (cyclicTISet W W₁ W₂)}
  have hsub : G₁ ⊆ SH ∪ SW := by
    intro g hg
    exact ftType345_partner_nonCoprime_support MtypeP hmaxS xdefW
      StypeP hStype2 hFrobS (by
        simpa only [Subgroup.orderOf_coe] using hG₁ g hg)
  have hcardSub : (G₁.ncard : ℝ) ≤ SH.ncard + SW.ncard := by
    have hcardNat :=
      (Set.ncard_mono hsub).trans (Set.ncard_union_le SH SW)
    exact_mod_cast hcardNat
  have hSHcard : SH.ncard =
      (classSupportWithin (⊤ : Subgroup Gamma)
        (subgroupNonidentity (Fitting_core S))).ncard := by
    calc
      SH.ncard =
          (classSupportWithin (⊤ : Subgroup Gamma)
            (subgroupNonidentity (Fitting_core S)) ∩
              ((⊤ : Subgroup Gamma) : Set Gamma)).ncard := by
        exact Set.ncard_subtype _ _
      _ = _ := by rw [Set.inter_eq_left.mpr (fun _ _ ↦ Subgroup.mem_top _)]
  have hSWcard : SW.ncard =
      (classSupportWithin (⊤ : Subgroup Gamma)
        (cyclicTISet W W₁ W₂)).ncard := by
    calc
      SW.ncard =
          (classSupportWithin (⊤ : Subgroup Gamma)
            (cyclicTISet W W₁ W₂) ∩
              ((⊤ : Subgroup Gamma) : Set Gamma)).ncard := by
        exact Set.ncard_subtype _ _
      _ = _ := by rw [Set.inter_eq_left.mpr (fun _ _ ↦ Subgroup.mem_top _)]
  have hTIH : IsNormalizedTI (subgroupNonidentity (Fitting_core S))
      (⊤ : Subgroup Gamma) S := by
    have h := (FTtypeII_ker_TI S hmaxS hStype2).2.2
    rwa [FTsupp1_type2 S hStype2] at h
  have hratioH : (SH.ncard : ℝ) / Nat.card Gamma ≤
      Nat.card (Fitting_core S) / (Nat.card S : ℝ) := by
    rw [hSHcard, classSupport_ratio_eq10 hTIH,
      subgroupNonidentity_ncard10]
    apply div_le_div_of_nonneg_right
    · exact_mod_cast Nat.sub_le _ _
    · positivity
  have hratioW : (SW.ncard : ℝ) / Nat.card Gamma =
      (cyclicTISet W W₁ W₂).ncard / (Nat.card W : ℝ) := by
    rw [hSWcard]
    exact classSupport_ratio_eq10 (FT_cyclicTI_hyp defW MtypeP).normedTI
  have hGpos : (0 : ℝ) < Nat.card Gamma := Nat.cast_pos.mpr Nat.card_pos
  calc
    (G₁.ncard : ℝ) / Nat.card Gamma ≤
        ((SH.ncard : ℝ) + SW.ncard) / Nat.card Gamma :=
      div_le_div_of_nonneg_right hcardSub hGpos.le
    _ = (SH.ncard : ℝ) / Nat.card Gamma +
        (SW.ncard : ℝ) / Nat.card Gamma := by ring
    _ ≤ _ := by rw [hratioW]; linarith

/-! ## Peterfalvi (10.8) -/

set_option maxHeartbeats 2000000 in
/-- `PFsection10.v: FTtype345_noncoherence_main`, Peterfalvi (10.8). -/
theorem FTtype345_noncoherence_main
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype2 : FTtype M ≠ 2)
    (zeta : ClassFunction M ℂ)
    (hzeta : FTType345ReferenceChoice M W₁ zeta)
    (tau₁ : ClassFunction M ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup Gamma) ℂ)
    (hcoh : coherent_with
      (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ))
      (nonidentitySet M) (ftType345Tau hmaxM) tau₁) :
    False := by
  let K : Subgroup M := ftType345DerivedInM M
  let calS : Finset (ClassFunction M ℂ) := ftType345InducedFamily10 M
  let ddM := FT_Dade_hyp M hmaxM
  let chi : ClassFunction (⊤ : Subgroup Gamma) ℂ := tau₁ zeta
  let rho : ClassFunction M ℂ := invDade ddM chi
  let C : Set (⊤ : Subgroup Gamma) :=
    {g | (g : Gamma) ∉ FT_Dade_full_support M}
  let G₀₁ : Set (⊤ : Subgroup Gamma) :=
    {g | Nat.Coprime (orderOf g) (Nat.card W₁)}
  let G₀ : Set (⊤ : Subgroup Gamma) := C ∩ G₀₁
  let G₁ : Set (⊤ : Subgroup Gamma) := C \ G₀₁
  have htypeMgt2 : 2 < FTtype M := by
    have hnot1 := FTtypeP_neq1 M U W W₁ W₂ defW hmaxM MtypeP
    have hrange := FTtype_range M
    omega
  have hchiVirtual : ClassFunction.IsVirtual chi := by
    exact hcoh.mapsToVirtual zeta
      (AddSubgroup.subset_closure hzeta.mem_calS)
  have hchiNorm : classFunctionNormSq chi = 1 := by
    rw [classFunctionNormSq_eq_re_starCharacterPairing,
      PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
        hchiVirtual hchiVirtual]
    rw [hcoh.isometry zeta
      (AddSubgroup.subset_closure hzeta.mem_calS) zeta
      (AddSubgroup.subset_closure hzeta.mem_calS)]
    rw [IrreducibleCharacter.characterPairing_self ⟨zeta, hzeta.irreducible⟩]
    norm_num
  have hSuzuki := Dade_cover_inequality
    (I := Fin 1) (fun _ ↦ ddM)
    (fun i j hij ↦ (hij (Subsingleton.elim i j)).elim)
    chi hchiNorm
  have hCover : DadeCoverComplement (fun _ : Fin 1 ↦ ddM) =
      {g : Gamma | g ∉ FT_Dade_full_support M} := by
    ext g
    simp [DadeCoverComplement, FT_Dade_supportE M hmaxM]
  have hCcard : C.ncard =
      ({g : Gamma | g ∉ FT_Dade_full_support M} : Set Gamma).ncard := by
    calc
      C.ncard =
          (({g : Gamma | g ∉ FT_Dade_full_support M} : Set Gamma) ∩
            ((⊤ : Subgroup Gamma) : Set Gamma)).ncard := by
        simpa [C] using
          (Set.ncard_subtype (fun g : Gamma ↦ g ∈ (⊤ : Subgroup Gamma))
            ({g : Gamma | g ∉ FT_Dade_full_support M} : Set Gamma))
      _ = _ := by rw [Set.inter_eq_left.mpr (fun _ _ ↦ Subgroup.mem_top _)]
  have hSuzuki' :
      (Nat.card (⊤ : Subgroup Gamma) : ℝ)⁻¹ *
          ((∑ g : (⊤ : Subgroup Gamma),
              if g ∈ C then Complex.normSq (chi g) else 0) - C.ncard) +
        classFunctionNormSq rho -
          (FTsupport M).ncard / (Nat.card M : ℝ) ≤ 0 := by
    simpa only [Fin.sum_univ_one, hCover, hCcard, rho, C,
      Set.mem_setOf_eq, sub_eq_add_neg, add_assoc] using hSuzuki
  have hcoprimeLower : ∀ g ∈ G₀, 1 ≤ Complex.normSq (chi g) := by
    intro g hg
    have hgG₀₁ : g ∈ G₀₁ := hg.2
    change Nat.Coprime (orderOf g) (Nat.card W₁) at hgG₀₁
    have hcop : Nat.Coprime (orderOf (g : Gamma)) (Nat.card W₁) := by
      simpa only [Subgroup.orderOf_coe] using hgG₀₁
    have hnorm :=
      FTType345CoherenceInternal.ftType345_zeta_tau1_coprime
        hmaxM MtypeP notMtype2 zeta hzeta tau₁ hcoh g hg.1 hcop
    exact Complex.one_le_normSq_iff.mpr hnorm
  have hpartition : C = G₀ ∪ G₁ := by
    ext g
    simp [G₀, G₁]
  have hdisjoint : Disjoint G₀ G₁ := by
    rw [Set.disjoint_left]
    intro g hg₀ hg₁
    exact hg₁.2 hg₀.2
  have hSuzukiClassical :
      (Nat.card (⊤ : Subgroup Gamma) : ℝ)⁻¹ *
          ((∑ g : (⊤ : Subgroup Gamma),
              @ite ℝ (g ∈ C) (Classical.propDecidable _)
                (Complex.normSq (chi g)) 0) - C.ncard) +
        classFunctionNormSq rho -
          (FTsupport M).ncard / (Nat.card M : ℝ) ≤ 0 := by
    have hsum :
        (∑ g : (⊤ : Subgroup Gamma),
            @ite ℝ (g ∈ C) (Classical.propDecidable _)
              (Complex.normSq (chi g)) 0) =
          ∑ g : (⊤ : Subgroup Gamma),
            if g ∈ C then Complex.normSq (chi g) else 0 := by
      apply Finset.sum_congr rfl
      intro g _
      by_cases hgC : g ∈ C <;> simp only [hgC, if_pos, if_neg]
    rw [hsum]
    exact hSuzuki'
  have hUpper : classFunctionNormSq rho ≤
      (FTsupport M).ncard / (Nat.card M : ℝ) +
        G₁.ncard / (Nat.card Gamma : ℝ) := by
    simpa only [Subgroup.card_top] using
      oneCover_upper_bound10 chi C G₀ G₁ hpartition hdisjoint
        hcoprimeLower _ _ hSuzukiClassical
  letI : K.Normal := by infer_instance
  have hfamilyCard : 1 < calS.card := by
    have htwo := seqInd_nontrivial (k := ℂ) K (mFT_odd M)
      (⊤ : Subgroup K) ⊥ hzeta.mem_calS
    change 1 < (seqIndD (k := ℂ) K (⊤ : Subgroup K) ⊥).card
    omega
  have hKindex : K.index = Nat.card W₁ := by
    have hOuterM : IsInternalSemidirectProductIn
        (derivedWithin M) W₁ M := MtypeP.1.2.2.2
    exact hOuterM.2.2.2.symm.index_eq_card.trans
      (MathlibSupport.natCard_subgroupOf_eq hOuterM.2.1)
  have hzetaIndex : zeta 1 = (K.index : ℂ) := by
    rw [hzeta.degree]
    exact_mod_cast hKindex.symm
  have hcohOuter : coherent_with
      (↑calS : Set (ClassFunction M ℂ))
      (nonidentitySet M) (Dade ddM) tau₁ := by
    have hagrees :
        ∀ phi ∈ AddSubgroup.closure
            (↑calS : Set (ClassFunction M ℂ)),
          phi ∈ ClassFunction.supportedOn (nonidentitySet M) →
            tau₁ phi = Dade ddM phi := by
      intro phi hphi hphiOff
      have hphiSupport : phi ∈ ClassFunction.supportedOn
          {x : M | (x : Gamma) ∈ FTsupport M} :=
        ftType345_derived_family_closure_supported
          hmaxM htypeMgt2 hphi hphiOff
      exact (hcoh.agrees phi hphi hphiOff).trans
        (FT_DadeE M hmaxM phi hphiSupport).symm
    exact
      { isometry := hcoh.isometry
        mapsToVirtual := hcoh.mapsToVirtual
        agrees := hagrees }
  have hKmap : K.map M.subtype = derivedWithin M := by
    simpa only [K, ftType345DerivedInM] using
      Subgroup.map_subgroupOf_eq_of_le
        (TypeSpecInternal.derivedWithin_le16_final M)
  have hKsupport : subgroupNonidentity (K.map M.subtype) = FTsupport M := by
    rw [hKmap, FTsupp_eq1 hmaxM htypeMgt2,
      FTsupp1_type_gt2 M htypeMgt2]
  let ddK : DadeHypothesis (⊤ : Subgroup Gamma) M
      (subgroupNonidentity (K.map M.subtype)) :=
    hKsupport.symm ▸ ddM
  have hcohOuterK : coherent_with
      (↑calS : Set (ClassFunction M ℂ))
      (nonidentitySet M) (Dade ddK) tau₁ := by
    simpa only [ddK, hKsupport] using hcohOuter
  have hDerivedCard := ftType345_derived_card_bound MtypeP
  have hindexHalf : (K.index : ℝ) ≤
      ((Nat.card K : ℝ) - 1) / 2 := by
    have hW₂pos : 0 < Nat.card W₂ := Nat.card_pos
    have hstrict : 2 * Nat.card W₁ < Nat.card K := by
      calc
        2 * Nat.card W₁ ≤ 2 * Nat.card W₁ * Nat.card W₂ := by
          nlinarith
        _ < Nat.card K := hDerivedCard
    rw [hKindex]
    have hgap : 2 * Nat.card W₁ + 1 ≤ Nat.card K :=
      Nat.add_one_le_iff.mpr hstrict
    have hgapR : (2 * Nat.card W₁ + 1 : ℝ) ≤ Nat.card K := by
      exact_mod_cast hgap
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hgapR
    nlinarith
  let zetaIrr : IrreducibleCharacter M ℂ := ⟨zeta, hzeta.irreducible⟩
  have hLowerRaw :=
    (Dade_Ind1_sub_lin K ddK tau₁ zetaIrr hcohOuterK
      hfamilyCard hzeta.mem_calS hzetaIndex).norm_bounds hindexHalf
  have hInvDade : invDade ddK chi = invDade ddM chi := by
    simpa only [ddK] using
      invDade_transport_support10 hKsupport.symm ddM chi
  have hLower : 1 - (Nat.card W₁ : ℝ) / (Nat.card K : ℝ) ≤
      classFunctionNormSq rho := by
    rw [hKindex] at hLowerRaw
    simpa [rho, chi, zetaIrr, hInvDade] using hLowerRaw.1
  have hstrict :
      1 - G₁.ncard / (Nat.card Gamma : ℝ) -
          (Nat.card W₁ : ℝ)⁻¹ <
        (Nat.card W₁ : ℝ) / (Nat.card K : ℝ) := by
    have hsupportCard : (FTsupport M).ncard = Nat.card K - 1 := by
      rw [FTsupp_eq1 hmaxM htypeMgt2,
        FTsupp1_type_gt2 M htypeMgt2, subgroupNonidentity_ncard10]
      exact congrArg (fun n : ℕ ↦ n - 1)
        (MathlibSupport.natCard_subgroupOf_eq
          (TypeSpecInternal.derivedWithin_le16_final M)).symm
    have hMcard : Nat.card M = Nat.card K * Nat.card W₁ := by
      have hOuterM : IsInternalSemidirectProductIn
          (derivedWithin M) W₁ M := MtypeP.1.2.2.2
      simpa only [K, ftType345DerivedInM,
        MathlibSupport.natCard_subgroupOf_eq hOuterM.1,
        MathlibSupport.natCard_subgroupOf_eq hOuterM.2.1] using
          hOuterM.2.2.2.card_mul.symm
    have hKpos : (0 : ℝ) < Nat.card K := by
      exact_mod_cast (Nat.card_pos : 0 < Nat.card K)
    have hW₁pos : (0 : ℝ) < Nat.card W₁ := by
      exact_mod_cast (Nat.card_pos : 0 < Nat.card W₁)
    have hGpos : (0 : ℝ) < Nat.card Gamma := by
      exact_mod_cast (Nat.card_pos : 0 < Nat.card Gamma)
    have hcompare := hLower.trans hUpper
    rw [hsupportCard, hMcard] at hcompare
    norm_num only [Nat.cast_mul, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr
      Nat.card_pos.ne')] at hcompare
    field_simp [ne_of_gt hKpos, ne_of_gt hW₁pos, ne_of_gt hGpos] at hcompare ⊢
    nlinarith
  obtain ⟨S, pairMS, xdefW, V, StypeP⟩ :=
    FTtypeP_pair_witness defW hmaxM MtypeP
  have hStype2 : FTtype S = 2 := by
    rcases pairMS.one_type_two with hM2 | hS2
    · exact (notMtype2 hM2).elim
    · exact hS2
  have hFrobS := ftType345_Frob_der1_type2
    hmaxM MtypeP notMtype2 zeta hzeta tau₁ hcoh
      (S := S) (V := V) pairMS.T_maximal xdefW StypeP hStype2
  have hG₁Bound : G₁.ncard / (Nat.card Gamma : ℝ) ≤
      (Nat.card (Fitting_core S) : ℝ) / (Nat.card S : ℝ) +
        (cyclicTISet W W₁ W₂).ncard / (Nat.card W : ℝ) := by
    apply ftType345_partner_nonCoprime_support_bound MtypeP
      (S := S) (V := V) pairMS.T_maximal xdefW StypeP hStype2 hFrobS G₁
    intro g hg
    exact hg.2
  have hInner : IsInternalSemidirectProductIn
      (Fitting_core S) V (derivedWithin S) := StypeP.2.1.2.2.2
  have hOuter : IsInternalSemidirectProductIn
      (derivedWithin S) W₂ S := StypeP.1.2.2.2
  have hcardInner : Nat.card (Fitting_core S) * Nat.card V =
      Nat.card (derivedWithin S) := by
    simpa only [MathlibSupport.natCard_subgroupOf_eq hInner.1,
      MathlibSupport.natCard_subgroupOf_eq hInner.2.1] using
        hInner.2.2.2.card_mul
  have hcardOuter : Nat.card (derivedWithin S) * Nat.card W₂ =
      Nat.card S := by
    simpa only [MathlibSupport.natCard_subgroupOf_eq hOuter.1,
      MathlibSupport.natCard_subgroupOf_eq hOuter.2.1] using
        hOuter.2.2.2.card_mul
  have hcardS : Nat.card S =
      Nat.card (Fitting_core S) * Nat.card V * Nat.card W₂ := by
    rw [← hcardOuter, ← hcardInner]
  have hcardW : Nat.card W = Nat.card W₁ * Nat.card W₂ := by
    simpa only [MathlibSupport.natCard_subgroupOf_eq defW.left_le,
      MathlibSupport.natCard_subgroupOf_eq defW.right_le] using
        defW.complement.card_mul.symm
  have hcyclicCard : (cyclicTISet W W₁ W₂).ncard =
      (Nat.card W₁ - 1) * (Nat.card W₂ - 1) :=
    defW.ncard_cyclicTISet
  have hstrict' :
      1 - ((Nat.card (Fitting_core S) : ℝ) / Nat.card S +
          (cyclicTISet W W₁ W₂).ncard / (Nat.card W : ℝ)) -
          (Nat.card W₁ : ℝ)⁻¹ <
        (Nat.card W₁ : ℝ) / (Nat.card K : ℝ) := by
    exact lt_of_le_of_lt (by linarith [hG₁Bound]) hstrict
  let ctxS : PTypeFCoreContext S V W W₂ W₁ :=
    Ptype_Fcore_context pairMS.T_maximal xdefW StypeP (by omega)
  have hVW₂ := Ptype_compl_Frobenius ctxS
  let J : Subgroup Gamma := V ⊔ W₂
  have hVbound : ((V.subgroupOf J).index : ℝ) ≤
      ((Nat.card (V.subgroupOf J) : ℝ) - 1) / 2 := by
    apply odd_Frobenius_index_ler (V.subgroupOf J) (W₂.subgroupOf J)
      (mFT_odd J)
    simpa only [J, PTypeFrobeniusProduct] using hVW₂
  have hVindex : (V.subgroupOf J).index = Nat.card W₂ := by
    rw [hVW₂.isComplement.symm.index_eq_card,
      MathlibSupport.natCard_subgroupOf_eq le_sup_right]
  have hVcard : Nat.card (V.subgroupOf J) = Nat.card V :=
    MathlibSupport.natCard_subgroupOf_eq le_sup_left
  rw [hVindex, hVcard] at hVbound
  have hW₁three : 3 ≤ Nat.card W₁ := by
    have hodd := mFT_odd W₁
    have hone := W₁.one_lt_card_iff_ne_bot.mpr MtypeP.1.2.2.1
    rcases hodd with ⟨k, hk⟩
    omega
  have hW₂three : 3 ≤ Nat.card W₂ := by
    have hodd := mFT_odd W₂
    have hone := W₂.one_lt_card_iff_ne_bot.mpr MtypeP.2.2.2.1.2.1
    rcases hodd with ⟨k, hk⟩
    omega
  have hVsix : (6 : ℝ) ≤ Nat.card V := by
    have hW₂real : (3 : ℝ) ≤ Nat.card W₂ := by exact_mod_cast hW₂three
    nlinarith
  have hleft : (2 * (Nat.card W₂ : ℝ))⁻¹ ≤
      1 - ((Nat.card (Fitting_core S) : ℝ) / Nat.card S +
          (cyclicTISet W W₁ W₂).ncard / (Nat.card W : ℝ)) -
          (Nat.card W₁ : ℝ)⁻¹ := by
    rw [hcardS, hcardW, hcyclicCard]
    norm_num only [Nat.cast_mul,
      Nat.cast_sub (show 1 ≤ Nat.card W₁ by omega),
      Nat.cast_sub (show 1 ≤ Nat.card W₂ by omega)]
    have hFpos : (0 : ℝ) < Nat.card (Fitting_core S) := by
      exact_mod_cast (Nat.card_pos : 0 < Nat.card (Fitting_core S))
    have hVpos : (0 : ℝ) < Nat.card V := by
      exact_mod_cast (Nat.card_pos : 0 < Nat.card V)
    have hW₁pos : (0 : ℝ) < Nat.card W₁ := by
      exact_mod_cast (Nat.card_pos : 0 < Nat.card W₁)
    have hW₂pos : (0 : ℝ) < Nat.card W₂ := by
      exact_mod_cast (Nat.card_pos : 0 < Nat.card W₂)
    have hW₁real : (3 : ℝ) ≤ Nat.card W₁ := by
      exact_mod_cast hW₁three
    have hprod : 0 ≤
        ((Nat.card W₁ : ℝ) - 3) * ((Nat.card V : ℝ) - 6) :=
      mul_nonneg (sub_nonneg.mpr hW₁real) (sub_nonneg.mpr hVsix)
    field_simp [ne_of_gt hFpos, ne_of_gt hVpos,
      ne_of_gt hW₁pos, ne_of_gt hW₂pos]
    nlinarith
  have hright : (Nat.card W₁ : ℝ) / (Nat.card K : ℝ) ≤
      (2 * (Nat.card W₂ : ℝ))⁻¹ := by
    have hKpos : (0 : ℝ) < Nat.card K := by
      exact_mod_cast (Nat.card_pos : 0 < Nat.card K)
    have hW₂pos : (0 : ℝ) < Nat.card W₂ := by
      exact_mod_cast (Nat.card_pos : 0 < Nat.card W₂)
    have hderivedReal :
        (2 * Nat.card W₁ * Nat.card W₂ : ℝ) ≤ Nat.card K := by
      exact_mod_cast (Nat.le_of_lt hDerivedCard)
    rw [inv_eq_one_div,
      div_le_div_iff₀ hKpos
        (mul_pos (by norm_num) hW₂pos)]
    nlinarith
  linarith

end

end Submission.OddOrder.PF
