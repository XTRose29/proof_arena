import Submission.OddOrder.BG.Section03.FrobeniusBasic
import Submission.OddOrder.BG.Section03.FrobeniusPartition
import Submission.OddOrder.BG.Section16.TypeSpecAndFinalSummary
import Submission.OddOrder.PF.Section05.SubcoherentProperties
import Submission.OddOrder.PF.Section07.CoherentFrobeniusPartition
import Submission.OddOrder.PF.Section07.InverseDade
import Submission.OddOrder.PF.Section08.FTSupportPartition
import Submission.OddOrder.PF.Section11.FTType34Structure

/-!
# Peterfalvi Section 12: type-I infrastructure

This module fixes the common objects used throughout the type-I analysis:
the sequential-induction and irreducible families, the support sets, the
result records for Peterfalvi (12.2), and the canonical Dade context.  Generic
pairing and semidirect-product adapters shared by the later proof phases are
kept in `FTType1InfrastructureInternal`.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open scoped BigOperators Classical Pointwise

universe uQ

variable {G : Type} [Group G] [Finite G] [IsMinSimpleOddGroup G]

local instance : Fintype G := Fintype.ofFinite G

/-! ## Type-I character data -/

/-- The Fitting core of `L`, displayed as a subgroup of `L`. -/
abbrev FTType1FittingIn (L : Subgroup G) : Subgroup L :=
  (Fitting_core L).subgroupOf L

/-- Sequentially induced characters from nontrivial characters of the
Fitting core. -/
noncomputable def FTType1SeqIndFamily (L : Subgroup G) :
    Finset (ClassFunction L ℂ) :=
  seqIndD (k := ℂ) (FTType1FittingIn L) ⊤ ⊥

/-- Irreducible characters whose kernel contains no more than the trivial
subgroup of the Fitting core. -/
noncomputable def FTType1IrrIndex (L : Subgroup G) :
    Finset (IrreducibleCharacter L ℂ) :=
  Iirr_kerD (k := ℂ) (FTType1FittingIn L) ⊥

/-- The class-function family indexed by `FTType1IrrIndex`. -/
noncomputable def FTType1IrrFamily (L : Subgroup G) :
    Finset (ClassFunction L ℂ) :=
  (FTType1IrrIndex L).image
    (fun chi : IrreducibleCharacter L ℂ ↦ (chi : ClassFunction L ℂ))

/-- Identity together with the Feit--Thompson support of `L`. -/
def FTType1CharacterSupport (L : Subgroup G) : Set L :=
  {x | x = 1 ∨ (x : G) ∈ ftSupport L}

/-- The part of the Fitting core outside its derived subgroup, displayed in
`L`. -/
def FTType1FittingDerivedLayer (L : Subgroup G) : Set L :=
  {x | (x : G) ∈ Fitting_core L ∧
    (x : G) ∉ derivedWithin (Fitting_core L)}

/-- Constituent blocks attached to the sequential-induction family. -/
def FTType1ConstituentFamily (L : Subgroup G) :
    Set (Set (IrreducibleCharacter L ℂ)) :=
  {A | ∃ chi ∈ FTType1SeqIndFamily L,
    A = (ClassFunction.constituents chi :
      Set (IrreducibleCharacter L ℂ))}

/-- Pairwise orthonormality for a finite family of class functions. -/
def FTType1Orthonormal
    {Q : Type uQ} [Group Q] [Fintype Q]
    (S : Finset (ClassFunction Q ℂ)) : Prop :=
  ∀ mu ∈ S, ∀ nu ∈ S,
    characterPairing mu nu = if mu = nu then 1 else 0

/-! ## Results packaged for later phases -/

/-- The three conclusions about one sequentially induced character in
Peterfalvi (12.2)(a). -/
structure FTType1SeqIndFacts
    (L : Subgroup G) (chi : ClassFunction L ℂ) : Prop where
  constituent_sum :
    chi = ∑ i ∈ ClassFunction.constituents chi,
      (i : ClassFunction L ℂ)
  constituent_degrees_constant :
    ∃ c : ℂ, ∀ i ∈ ClassFunction.constituents chi, i 1 = c
  constituent_supported :
    ∀ i ∈ ClassFunction.constituents chi,
      (i : ClassFunction L ℂ) ∈
        ClassFunction.supportedOn (FTType1CharacterSupport L)

/-- The isometry, integrality, and support conclusions for the Dade image of
the integral span of the type-I irreducibles. -/
structure FTType1IrrIsometryConclusion
    (L : Subgroup G)
    (tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ) : Prop where
  isometry :
    ∀ phi ∈ AddSubgroup.closure
        (FTType1IrrFamily L : Set (ClassFunction L ℂ)),
      phi ∈ ClassFunction.supportedOn (nonidentitySet L) →
      ∀ psi ∈ AddSubgroup.closure
          (FTType1IrrFamily L : Set (ClassFunction L ℂ)),
        psi ∈ ClassFunction.supportedOn (nonidentitySet L) →
        characterPairing (tau phi) (tau psi) = characterPairing phi psi
  mapsToVirtual :
    ∀ phi ∈ AddSubgroup.closure
        (FTType1IrrFamily L : Set (ClassFunction L ℂ)),
      phi ∈ ClassFunction.supportedOn (nonidentitySet L) →
      ClassFunction.IsVirtual (tau phi)
  supported :
    ∀ phi ∈ AddSubgroup.closure
        (FTType1IrrFamily L : Set (ClassFunction L ℂ)),
      phi ∈ ClassFunction.supportedOn (nonidentitySet L) →
      tau phi ∈ ClassFunction.supportedOn (nonidentitySet G)

/-- The maximality and type-I hypotheses fixed throughout the first part of
Section 12. -/
structure FTType1Context (L : Subgroup G) : Prop where
  maxL : L ∈ minSimple_max_groups (G := G)
  type_one : FTtype L = 1

namespace FTType1Context

/-- The canonical Dade map belonging to a type-I context. -/
noncomputable def tau {L : Subgroup G} (ctx : FTType1Context L) :
    ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ :=
  (ClassFunction.comap Subgroup.topEquiv.symm.toMonoidHom).comp
    (Dade (FT_Dade_hyp L ctx.maxL))

/-- The canonical inverse-Dade map belonging to a type-I context. -/
noncomputable def rho {L : Subgroup G} (ctx : FTType1Context L) :
    ClassFunction G ℂ →ₗ[ℂ] ClassFunction L ℂ :=
  (invDade (FT_DadeF_hyp L ctx.maxL)).comp
    (ClassFunction.comap Subgroup.topEquiv.toMonoidHom)

end FTType1Context

/-! ## Generic adapters shared by the Section 12 phases -/

namespace FTType1InfrastructureInternal

private theorem ambientDisjointOfSubgroupOf
    {Q : Type uQ} [Group Q] {A B K : Subgroup Q}
    (hAK : A ≤ K) (_hBK : B ≤ K)
    (hdis : Disjoint (A.subgroupOf K) (B.subgroupOf K)) :
    Disjoint A B := by
  rw [disjoint_iff]
  apply le_antisymm _ bot_le
  intro x hx
  apply Subgroup.mem_bot.mpr
  let xK : K := ⟨x, hAK hx.1⟩
  have hxInf : xK ∈ (A.subgroupOf K) ⊓ (B.subgroupOf K) :=
    ⟨hx.1, hx.2⟩
  have hxBot : xK ∈ (⊥ : Subgroup K) := by
    rw [← disjoint_iff.mp hdis]
    exact hxInf
  exact congrArg Subtype.val (Subgroup.mem_bot.mp hxBot)

/-- Restrict the complement in an internal semidirect product to a subgroup
containing its normal factor. -/
theorem semidirectInfRight
    {Q : Type uQ} [Group Q] {N H T : Subgroup Q}
    (hsd : IsInternalSemidirectProductIn N H ⊤)
    (hNT : N ≤ T) :
    IsInternalSemidirectProductIn N (H ⊓ T) T := by
  have hTopNormalizesN :
      (⊤ : Subgroup Q) ≤ Subgroup.normalizer (N : Set Q) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mp
      hsd.2.2.1
  have hNnormal : (N.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNT).mpr
      (le_top.trans hTopNormalizesN)
  have hNHdis : Disjoint N H :=
    ambientDisjointOfSubgroupOf le_top le_top hsd.2.2.2.disjoint
  have hRestrictedDisjoint :
      Disjoint (N.subgroupOf T) ((H ⊓ T).subgroupOf T) := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro x hx
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    apply Subgroup.mem_bot.mp
    rw [← disjoint_iff.mp hNHdis]
    exact ⟨hx.1, hx.2.1⟩
  have hNHtop : N ⊔ H = ⊤ := by
    apply le_antisymm le_top
    have hSubgroupOfTop :
        (N ⊔ H).subgroupOf (⊤ : Subgroup Q) = ⊤ := by
      rw [Subgroup.subgroupOf_sup le_top le_top]
      exact hsd.2.2.2.sup_eq_top
    exact Subgroup.subgroupOf_eq_top.mp hSubgroupOfTop
  have hNnormalAmbient : N.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    exact top_unique hTopNormalizesN
  have hAmbientSup : N ⊔ (H ⊓ T) = T := by
    letI : N.Normal := hNnormalAmbient
    apply SetLike.ext'
    rw [Subgroup.normal_mul, Subgroup.mul_inf_assoc N H T hNT,
      ← Subgroup.normal_mul N H, hNHtop]
    simp
  have hRestrictedSup :
      N.subgroupOf T ⊔ (H ⊓ T).subgroupOf T = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNT inf_le_right, hAmbientSup]
    exact Subgroup.subgroupOf_self T
  refine ⟨hNT, inf_le_right, hNnormal, ?_⟩
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    hRestrictedDisjoint
  letI : (N.subgroupOf T).Normal := hNnormal
  rw [← Subgroup.normal_mul, hRestrictedSup]
  rfl

private noncomputable def semidirectQuotientEquiv
    {Q : Type uQ} [Group Q] {N H K : Subgroup Q}
    (hsd : IsInternalSemidirectProductIn N H K) :
    letI : (N.subgroupOf K).Normal := hsd.2.2.1
    K ⧸ N.subgroupOf K ≃* H := by
  letI : (N.subgroupOf K).Normal := hsd.2.2.1
  exact hsd.2.2.2.symm.QuotientMulEquiv.trans
    (Subgroup.subgroupOfEquivOfLe hsd.2.1)

/-- The quotient by the normal factor of a semidirect product is commutative
when the complement is commutative. -/
theorem semidirectQuotientCommutative
    {Q : Type uQ} [Group Q] {N H K : Subgroup Q}
    (hsd : IsInternalSemidirectProductIn N H K)
    (hH : IsMulCommutative H) :
    letI : (N.subgroupOf K).Normal := hsd.2.2.1
    IsMulCommutative (K ⧸ N.subgroupOf K) := by
  letI : (N.subgroupOf K).Normal := hsd.2.2.1
  let e := semidirectQuotientEquiv hsd
  apply isMulCommutative_iff.mpr
  intro x y
  apply e.injective
  simpa only [map_mul] using
    (isMulCommutative_iff.mp hH (e x) (e y))

/-- An irreducible character, regarded as a class function, is virtual. -/
theorem irreducibleIsVirtual
    {Q : Type uQ} [Group Q] [Fintype Q]
    (chi : IrreducibleCharacter Q ℂ) :
    ClassFunction.IsVirtual (chi : ClassFunction Q ℂ) := by
  refine ⟨Finsupp.single chi 1, ?_⟩
  simp

/-- Simultaneous inversion of both inputs preserves the character pairing. -/
theorem pairingInverse
    {Q : Type uQ} [Group Q] [Fintype Q]
    (phi psi : ClassFunction Q ℂ) :
    characterPairing (ClassFunction.inverseLinear phi)
        (ClassFunction.inverseLinear psi) = characterPairing phi psi := by
  unfold characterPairing
  congr 1
  refine Fintype.sum_equiv (Equiv.inv Q) _ _ fun x ↦ ?_
  simp only [Equiv.inv_apply, ClassFunction.inverseLinear_apply, inv_inv]

/-- Inversion can be transferred from the left input of the pairing to the
right input. -/
theorem pairingInverseLeft
    {Q : Type uQ} [Group Q] [Fintype Q]
    (phi psi : ClassFunction Q ℂ) :
    characterPairing (ClassFunction.inverseLinear phi) psi =
      characterPairing phi (ClassFunction.inverseLinear psi) := by
  unfold characterPairing
  congr 1
  refine Fintype.sum_equiv (Equiv.inv Q) _ _ fun x ↦ ?_
  simp only [Equiv.inv_apply, ClassFunction.inverseLinear_apply, inv_inv]

private theorem pairingNegLeft
    {Q : Type uQ} [Group Q] [Fintype Q]
    (phi psi : ClassFunction Q ℂ) :
    characterPairing (-phi) psi = -characterPairing phi psi := by
  rw [← neg_one_smul ℂ phi, characterPairing_smul_left]
  ring

private theorem pairingNegRight
    {Q : Type uQ} [Group Q] [Fintype Q]
    (phi psi : ClassFunction Q ℂ) :
    characterPairing phi (-psi) = -characterPairing phi psi := by
  rw [← neg_one_smul ℂ psi, characterPairing_smul_right]
  ring

/-- The character pairing is additive over subtraction in its left input. -/
theorem pairingSubLeft
    {Q : Type uQ} [Group Q] [Fintype Q]
    (phi psi theta : ClassFunction Q ℂ) :
    characterPairing (phi - psi) theta =
      characterPairing phi theta - characterPairing psi theta := by
  rw [sub_eq_add_neg, characterPairing_add_left, pairingNegLeft,
    sub_eq_add_neg]

/-- The character pairing is additive over subtraction in its right input. -/
theorem pairingSubRight
    {Q : Type uQ} [Group Q] [Fintype Q]
    (phi psi theta : ClassFunction Q ℂ) :
    characterPairing phi (psi - theta) =
      characterPairing phi psi - characterPairing phi theta := by
  rw [sub_eq_add_neg, characterPairing_add_right, pairingNegRight,
    sub_eq_add_neg]

/-- Move a finite sum out of the left input of the character pairing. -/
theorem pairingFinsetSumLeft
    {Q : Type uQ} [Group Q] [Fintype Q]
    {I : Type*} (s : Finset I) (f : I → ClassFunction Q ℂ)
    (psi : ClassFunction Q ℂ) :
    characterPairing (∑ i ∈ s, f i) psi =
      ∑ i ∈ s, characterPairing (f i) psi := by
  exact map_sum (characterPairingRight psi) (fun i ↦ f i) s

/-- Move a finite sum out of the right input of the character pairing. -/
theorem pairingFinsetSumRight
    {Q : Type uQ} [Group Q] [Fintype Q]
    (phi : ClassFunction Q ℂ) {I : Type*}
    (s : Finset I) (f : I → ClassFunction Q ℂ) :
    characterPairing phi (∑ i ∈ s, f i) =
      ∑ i ∈ s, characterPairing phi (f i) := by
  exact map_sum (characterPairingLeft phi) (fun i ↦ f i) s

/-- A class function and its inverse-value transform agree at the identity. -/
theorem inverseSubSupported
    {Q : Type uQ} [Group Q] (phi : ClassFunction Q ℂ) :
    phi - ClassFunction.inverseLinear phi ∈
      ClassFunction.supportedOn (nonidentitySet Q) := by
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hx
  have hxOne : x = 1 := by
    simpa [nonidentitySet] using not_not.mp hx
  subst x
  simp

private theorem representationCharacterInvEqStar
    {Q : Type uQ} {V : Type*} [Group Q] [Fintype Q]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ Q V) (x : Q) :
    rho.character x⁻¹ = star (rho.character x) := by
  let n := Nat.card Q
  have hn : n ≠ 0 := Nat.card_pos.ne'
  letI : NeZero n := ⟨hn⟩
  let omega₀ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have homega₀ : IsPrimitiveRoot omega₀ n := by
    simpa only [omega₀] using Complex.isPrimitiveRoot_exp n hn
  let omega : ℂˣ := Units.mk0 omega₀ (homega₀.ne_zero hn)
  have homega : IsPrimitiveRoot omega n := by
    apply IsPrimitiveRoot.coe_units_iff.mp
    simpa [omega] using homega₀
  have homegaNorm : ‖(omega : ℂ)‖ = 1 := by
    simpa [omega] using homega₀.norm'_eq_one hn
  have homegaPow : (omega : ℂ) ^ n = 1 := by
    exact congrArg (fun z : ℂˣ ↦ (z : ℂ)) homega.pow_eq_one
  have hpow : (rho x) ^ n = 1 := by
    rw [← map_pow, pow_card_eq_one', map_one]
  have hxinvPow : x⁻¹ = x ^ (n - 1) := by
    exact inv_eq_of_mul_eq_one_right (by
      rw [mul_pow_sub_one hn, pow_card_eq_one'])
  have hinvPow : rho x⁻¹ = (rho x) ^ (n - 1) := by
    rw [hxinvPow, map_pow]
  have hweight (i : ZMod n) :
      (primitiveRootUnitWeight homega i : ℂ) =
        (omega : ℂ) ^ i.val := by
    conv_lhs =>
      rw [← ZMod.natCast_zmod_val i,
        primitiveRootUnitWeight_natCast]
    rfl
  have hweightStar (i : ZMod n) :
      (starRingEnd ℂ) (primitiveRootUnitWeight homega i : ℂ) =
        (primitiveRootUnitWeight homega i : ℂ) ^ (n - 1) := by
    let w : ℂ := primitiveRootUnitWeight homega i
    have hwNorm : ‖w‖ = 1 := by
      rw [show w = (omega : ℂ) ^ i.val by exact hweight i,
        norm_pow, homegaNorm, one_pow]
    have hwPow : w ^ n = 1 := by
      rw [show w = (omega : ℂ) ^ i.val by exact hweight i,
        ← pow_mul, Nat.mul_comm, pow_mul, homegaPow, one_pow]
    have hwInv : w⁻¹ = w ^ (n - 1) :=
      inv_eq_of_mul_eq_one_right (by rw [mul_pow_sub_one hn, hwPow])
    change (starRingEnd ℂ) w = w ^ (n - 1)
    rw [← Complex.inv_eq_conj hwNorm, hwInv]
  have htraceOne :=
    trace_pow_eq_sum_primitiveRootUnitWeight homega (rho x) hpow 1
  have htracePred :=
    trace_pow_eq_sum_primitiveRootUnitWeight homega (rho x) hpow (n - 1)
  simp only [pow_one] at htraceOne
  calc
    rho.character x⁻¹ = LinearMap.trace ℂ V (rho x⁻¹) := rfl
    _ = LinearMap.trace ℂ V ((rho x) ^ (n - 1)) := by rw [hinvPow]
    _ = ∑ i : ZMod n,
          (Module.finrank ℂ
              (Module.End.eigenspace (rho x)
                (primitiveRootUnitWeight homega i : ℂ)) : ℂ) *
            (primitiveRootUnitWeight homega i : ℂ) ^ (n - 1) :=
      htracePred
    _ = star (∑ i : ZMod n,
          (Module.finrank ℂ
              (Module.End.eigenspace (rho x)
                (primitiveRootUnitWeight homega i : ℂ)) : ℂ) *
            (primitiveRootUnitWeight homega i : ℂ)) := by
      change _ = (starRingEnd ℂ) (∑ i : ZMod n,
        (Module.finrank ℂ
            (Module.End.eigenspace (rho x)
              (primitiveRootUnitWeight homega i : ℂ)) : ℂ) *
          (primitiveRootUnitWeight homega i : ℂ))
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul, map_natCast, hweightStar]
    _ = star (LinearMap.trace ℂ V (rho x)) := by rw [htraceOne]
    _ = star (rho.character x) := rfl

private theorem irreducibleCharacterApplyInvEqStar
    {Q : Type uQ} [Group Q] [Fintype Q]
    (chi : IrreducibleCharacter Q ℂ) (x : Q) :
    chi x⁻¹ = star (chi x) := by
  rw [← chi.representation_character,
    ← chi.representation_character]
  exact representationCharacterInvEqStar chi.representation.ρ x

/-- Complex conjugation of a realized virtual character is evaluation at the
inverse group element. -/
theorem starRealizeApplyEqInverse
    {Q : Type uQ} [Group Q] [Fintype Q]
    (z : VirtualCharacter Q ℂ) (x : Q) :
    star (VirtualCharacter.realize z x) =
      VirtualCharacter.realize z x⁻¹ := by
  classical
  induction z using Finsupp.induction with
  | zero => simp
  | single_add chi n z hchi hn ih =>
      rw [VirtualCharacter.realize_add,
        VirtualCharacter.realize_single]
      change (starRingEnd ℂ) ((n : ℂ) * chi.val x +
          VirtualCharacter.realize z x) =
        (n : ℂ) * chi.val x⁻¹ +
          VirtualCharacter.realize z x⁻¹
      have hchiStar :=
        (irreducibleCharacterApplyInvEqStar chi x).symm
      change (starRingEnd ℂ) (chi.val x) = chi.val x⁻¹ at hchiStar
      have ih' := ih
      change (starRingEnd ℂ) (VirtualCharacter.realize z x) =
        VirtualCharacter.realize z x⁻¹ at ih'
      rw [map_add, map_mul, map_intCast, ih', hchiStar]

/-- The star pairing and the inverse-value pairing agree on two realized
virtual characters. -/
theorem starPairingRealizeEqPairing
    {Q : Type uQ} [Group Q] [Fintype Q]
    (z w : VirtualCharacter Q ℂ) :
    starCharacterPairing (VirtualCharacter.realize z)
        (VirtualCharacter.realize w) =
      characterPairing (VirtualCharacter.realize z)
        (VirtualCharacter.realize w) := by
  apply starCharacterPairing_eq_characterPairing_of_star_apply_eq_inv
  exact starRealizeApplyEqInverse w

/-- The right input alone needs to be virtual for the star pairing and the
inverse-value pairing to agree. -/
theorem starPairingEqPairingOfRightVirtual
    {Q : Type uQ} [Group Q] [Fintype Q]
    (phi : ClassFunction Q ℂ) {psi : ClassFunction Q ℂ}
    (hpsi : ClassFunction.IsVirtual psi) :
    starCharacterPairing phi psi = characterPairing phi psi := by
  obtain ⟨z, rfl⟩ := hpsi
  apply starCharacterPairing_eq_characterPairing_of_star_apply_eq_inv
  exact starRealizeApplyEqInverse z

/-- Pullback along inversion is pointwise complex conjugation for a virtual
character. -/
theorem inverseEqConjOfVirtual
    {Q : Type uQ} [Group Q] [Fintype Q]
    {phi : ClassFunction Q ℂ}
    (hphi : ClassFunction.IsVirtual phi) :
    ClassFunction.inverseLinear phi = cfConjC phi := by
  obtain ⟨z, rfl⟩ := hphi
  ext x
  exact (starRealizeApplyEqInverse z x).symm

/-- Complex conjugation sends an irreducible character to its contragredient
dual. -/
theorem conjugateIrreducibleEqDual
    {Q : Type uQ} [Group Q] [Fintype Q]
    (chi : IrreducibleCharacter Q ℂ) :
    IrreducibleCharacter.mapRingEquiv complexConjugation chi =
      IrreducibleCharacter.dual chi := by
  ext x
  rw [IrreducibleCharacter.mapRingEquiv_apply,
    IrreducibleCharacter.dual_apply]
  change star (chi x) = chi x⁻¹
  exact (irreducibleCharacterApplyInvEqStar chi x).symm

private theorem virtualCharacterOfFDRepApply
    {Q : Type} [Group Q] [Fintype Q]
    (V : FDRep ℂ Q) (chi : IrreducibleCharacter Q ℂ) :
    VirtualCharacter.ofFDRep V chi = (chi.multiplicity V : ℤ) := by
  simp [VirtualCharacter.ofFDRep]

/-- Ordinary characters with zero pairing have disjoint irreducible
constituent sets. -/
theorem constituentsDisjointOfPairingEqZero
    {Q : Type} [Group Q] [Fintype Q]
    (V W : FDRep ℂ Q)
    (hpair : characterPairing
      (ClassFunction.ofRepresentation V.ρ)
      (ClassFunction.ofRepresentation W.ρ) = 0) :
    Disjoint
      (ClassFunction.constituents (ClassFunction.ofRepresentation V.ρ) :
        Set (IrreducibleCharacter Q ℂ))
      (ClassFunction.constituents (ClassFunction.ofRepresentation W.ρ) :
        Set (IrreducibleCharacter Q ℂ)) := by
  rw [Set.disjoint_left]
  intro chi hchiV hchiW
  let zV := VirtualCharacter.ofFDRep V
  let zW := VirtualCharacter.ofFDRep W
  have hmultV : 0 < chi.multiplicity V :=
    (chi.isConstituent_ofRepresentation_iff_multiplicity_pos V).mp
      ((ClassFunction.mem_constituents_iff _ _).mp hchiV)
  have hmultW : 0 < chi.multiplicity W :=
    (chi.isConstituent_ofRepresentation_iff_multiplicity_pos W).mp
      ((ClassFunction.mem_constituents_iff _ _).mp hchiW)
  have hchiSupport : chi ∈ zV.support := by
    rw [Finsupp.mem_support_iff]
    simpa [zV, virtualCharacterOfFDRepApply] using hmultV.ne'
  have htermPos : 0 < zV chi * zW chi := by
    rw [virtualCharacterOfFDRepApply, virtualCharacterOfFDRepApply]
    exact mul_pos (by exact_mod_cast hmultV) (by exact_mod_cast hmultW)
  have htermsNonneg : ∀ eta ∈ zV.support, 0 ≤ zV eta * zW eta := by
    intro eta _
    rw [virtualCharacterOfFDRepApply, virtualCharacterOfFDRepApply]
    positivity
  have hdotPos : 0 < coeffDot zV zW := by
    unfold coeffDot
    change 0 < ∑ eta ∈ zV.support, zV eta * zW eta
    exact lt_of_lt_of_le htermPos
      (Finset.single_le_sum htermsNonneg hchiSupport)
  have hdotCast : (coeffDot zV zW : ℂ) = 0 := by
    have hrealize := VirtualCharacter.characterPairing_realize zV zW
    rw [VirtualCharacter.realize_ofFDRep,
      VirtualCharacter.realize_ofFDRep, hpair] at hrealize
    exact hrealize.symm
  have hdotZero : coeffDot zV zW = 0 := by
    exact Int.cast_injective (α := ℂ) (by simpa using hdotCast)
  omega

/-- A virtual character of norm one is a signed irreducible character. -/
theorem existsSignedIrreducibleOfVirtualNormOne
    {Q : Type uQ} [Group Q] [Fintype Q]
    {phi : ClassFunction Q ℂ}
    (hphi : ClassFunction.IsVirtual phi)
    (hnorm : characterPairing phi phi = 1) :
    ∃ (chi : IrreducibleCharacter Q ℂ) (epsilon : ℤ),
      IsSign epsilon ∧
        phi = (epsilon : ℂ) • (chi : ClassFunction Q ℂ) := by
  obtain ⟨z, hz⟩ := hphi
  have hnormZ : normSq z = 1 := by
    apply Int.cast_injective (α := ℂ)
    rw [← VirtualCharacter.characterPairing_realize_self, hz, hnorm]
    norm_num
  obtain ⟨chi, epsilon, hepsilon, hsingle⟩ :=
    eq_signed_single_of_normSq_eq_one z hnormZ
  refine ⟨chi, epsilon, hepsilon, ?_⟩
  rw [← hz, hsingle, VirtualCharacter.realize_single]

/-- Two norm-one virtual characters with nonzero pairing are scalar
multiple of one another. -/
theorem virtualNormOneCollinear
    {Q : Type uQ} [Group Q] [Fintype Q]
    {phi psi : ClassFunction Q ℂ}
    (hphiVirtual : ClassFunction.IsVirtual phi)
    (hphiNorm : characterPairing phi phi = 1)
    (hpsiVirtual : ClassFunction.IsVirtual psi)
    (hpsiNorm : characterPairing psi psi = 1)
    (hpair : characterPairing phi psi ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ phi = c • psi := by
  letI : Invertible (Nat.card Q : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨chi, epsilon, hepsilon, hphi⟩ :=
    existsSignedIrreducibleOfVirtualNormOne hphiVirtual hphiNorm
  obtain ⟨eta, delta, hdelta, hpsi⟩ :=
    existsSignedIrreducibleOfVirtualNormOne hpsiVirtual hpsiNorm
  have hchiEta : chi = eta := by
    by_contra hne
    apply hpair
    rw [hphi, hpsi, characterPairing_smul_left,
      characterPairing_smul_right,
      IrreducibleCharacter.characterPairing_eq_zero hne]
    simp
  subst eta
  let c : ℂ := ((epsilon * delta : ℤ) : ℂ)
  have hc : c ≠ 0 := by
    exact Int.cast_ne_zero.mpr
      (mul_ne_zero (isSign_ne_zero hepsilon) (isSign_ne_zero hdelta))
  refine ⟨c, hc, ?_⟩
  rw [hphi, hpsi]
  change (epsilon : ℂ) • (chi : ClassFunction Q ℂ) =
    ((epsilon * delta : ℤ) : ℂ) •
      ((delta : ℂ) • (chi : ClassFunction Q ℂ))
  rw [smul_smul, Int.cast_mul]
  congr 1
  rcases hdelta with rfl | rfl <;> norm_num

end FTType1InfrastructureInternal

end

end Submission.OddOrder.PF
