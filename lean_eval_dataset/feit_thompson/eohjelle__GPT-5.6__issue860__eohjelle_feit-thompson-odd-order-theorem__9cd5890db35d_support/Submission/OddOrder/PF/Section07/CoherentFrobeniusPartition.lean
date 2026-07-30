import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Submission.OddOrder.BG.Section03.FrobeniusBasic
import Submission.OddOrder.BG.Section03.FrobeniusSolvableKernel
import Submission.OddOrder.PF.Section04.VirtualCharacterPairs
import Submission.OddOrder.PF.Section05.DadeAutomorphismCoherence
import Submission.OddOrder.PF.Section06.FrobeniusKernelInduction
import Submission.OddOrder.PF.Section06.OddFrobeniusIndexBound
import Submission.OddOrder.PF.Section06.SibleyCoherence
import Submission.OddOrder.PF.Section07.DadeCoverSeqInd

/-!
# Peterfalvi Section 7: disjoint Dade maps and Frobenius partitions

This file ports the odd-order half of `PFsection7.v` (source lines 503--834).
It contains the parity lemma for real virtual characters, the orthogonality
statements for Dade maps with disjoint support, Peterfalvi (7.9), the
Frobenius-index estimate used again in Section 14, and Peterfalvi (7.10)--
(7.11).

MathComp orders its concrete algebraic closure.  Lean's `Complex` is not an
ordered field, so every numerical inequality below is stated in `Real`; the
character identities remain in `Complex`.  Divisibility of an integral
character pairing by two is represented by `evenCharacterPairing`.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.MathlibSupport
open scoped BigOperators Classical Pointwise

universe u

local instance coherentFrobeniusPartitionInvertibleCard
    {Q : Type u} [Group Q] [Fintype Q] :
    Invertible (Nat.card Q : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-! ## Parity of real virtual-character pairings -/

/-- Source `cfReal`: invariance under inversion.  On virtual characters this
is equivalent to taking real values, since character values at inverses are
their complex conjugates. -/
def cfReal {Q : Type u} [Group Q] (phi : ClassFunction Q ℂ) : Prop :=
  ClassFunction.inverseLinear phi = phi

/-- The integral character pairing of `phi` and `psi` is divisible by two.
The virtual-character hypotheses at use sites guarantee integrality. -/
def evenCharacterPairing {Q : Type u} [Group Q] [Fintype Q]
    (phi psi : ClassFunction Q ℂ) : Prop :=
  ∃ n : ℤ, characterPairing phi psi = ((2 * n : ℤ) : ℂ)

private theorem inverseLinear_involutive_partition
    {Q : Type u} [Group Q] (phi : ClassFunction Q ℂ) :
    ClassFunction.inverseLinear (ClassFunction.inverseLinear phi) = phi := by
  ext x
  simp

private theorem pairing_inverseLinear_left_partition
    {Q : Type u} [Group Q] [Fintype Q]
    (phi psi : ClassFunction Q ℂ) :
    characterPairing (ClassFunction.inverseLinear phi) psi =
      characterPairing phi (ClassFunction.inverseLinear psi) := by
  unfold characterPairing
  congr 1
  refine Fintype.sum_equiv (Equiv.inv Q) _ _ fun x ↦ ?_
  simp only [Equiv.inv_apply, ClassFunction.inverseLinear_apply, inv_inv]

/- The inverse-value identity used below is private in the earlier PF files.
Keep the local proof here rather than depending on another module's
implementation detail. -/
private theorem representation_character_inv_eq_star_partition
    {Q : Type u} {V : Type*} [Group Q] [Fintype Q]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ Q V) (g : Q) :
    rho.character g⁻¹ = star (rho.character g) := by
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
  have hpow : (rho g) ^ n = 1 := by
    rw [← map_pow, pow_card_eq_one', map_one]
  have hginvPow : g⁻¹ = g ^ (n - 1) := by
    exact inv_eq_of_mul_eq_one_right (by
      rw [mul_pow_sub_one hn, pow_card_eq_one'])
  have hinvPow : rho g⁻¹ = (rho g) ^ (n - 1) := by
    rw [hginvPow, map_pow]
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
    trace_pow_eq_sum_primitiveRootUnitWeight homega (rho g) hpow 1
  have htracePred :=
    trace_pow_eq_sum_primitiveRootUnitWeight homega (rho g) hpow (n - 1)
  simp only [pow_one] at htraceOne
  calc
    rho.character g⁻¹ = LinearMap.trace ℂ V (rho g⁻¹) := rfl
    _ = LinearMap.trace ℂ V ((rho g) ^ (n - 1)) := by rw [hinvPow]
    _ = ∑ i : ZMod n,
          (Module.finrank ℂ
              (Module.End.eigenspace (rho g)
                (primitiveRootUnitWeight homega i : ℂ)) : ℂ) *
            (primitiveRootUnitWeight homega i : ℂ) ^ (n - 1) :=
      htracePred
    _ = star (∑ i : ZMod n,
          (Module.finrank ℂ
              (Module.End.eigenspace (rho g)
                (primitiveRootUnitWeight homega i : ℂ)) : ℂ) *
            (primitiveRootUnitWeight homega i : ℂ)) := by
      change _ = (starRingEnd ℂ) (∑ i : ZMod n,
        (Module.finrank ℂ
            (Module.End.eigenspace (rho g)
              (primitiveRootUnitWeight homega i : ℂ)) : ℂ) *
          (primitiveRootUnitWeight homega i : ℂ))
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul, map_natCast, hweightStar]
    _ = star (LinearMap.trace ℂ V (rho g)) := by rw [htraceOne]
    _ = star (rho.character g) := rfl

private theorem irreducibleCharacter_apply_inv_eq_star_partition
    {Q : Type u} [Group Q] [Fintype Q]
    (chi : IrreducibleCharacter Q ℂ) (g : Q) :
    chi g⁻¹ = star (chi g) := by
  rw [← chi.representation_character,
    ← chi.representation_character]
  exact representation_character_inv_eq_star_partition
    chi.representation.ρ g

private theorem star_realize_apply_eq_inverse_partition
    {Q : Type u} [Group Q] [Fintype Q]
    (z : VirtualCharacter Q ℂ) (x : Q) :
    star (VirtualCharacter.realize z x) =
      VirtualCharacter.realize z x⁻¹ := by
  classical
  induction z using Finsupp.induction with
  | zero => simp
  | single_add chi n z hchi hn ih =>
      rw [VirtualCharacter.realize_add, VirtualCharacter.realize_single]
      change (starRingEnd ℂ) ((n : ℂ) * chi.val x +
          VirtualCharacter.realize z x) =
        (n : ℂ) * chi.val x⁻¹ + VirtualCharacter.realize z x⁻¹
      have hchiStar :=
        (irreducibleCharacter_apply_inv_eq_star_partition chi x).symm
      change (starRingEnd ℂ) (chi.val x) = chi.val x⁻¹ at hchiStar
      change (starRingEnd ℂ) (VirtualCharacter.realize z x) =
        VirtualCharacter.realize z x⁻¹ at ih
      rw [map_add, map_mul, map_intCast, ih, hchiStar]

private theorem starCharacterPairing_realize_eq_characterPairing_partition
    {Q : Type u} [Group Q] [Fintype Q]
    (z w : VirtualCharacter Q ℂ) :
    starCharacterPairing (VirtualCharacter.realize z)
        (VirtualCharacter.realize w) =
      characterPairing (VirtualCharacter.realize z)
        (VirtualCharacter.realize w) := by
  apply starCharacterPairing_eq_characterPairing_of_star_apply_eq_inv
  exact star_realize_apply_eq_inverse_partition w

private theorem inverseLinear_realize_eq_cfConjC_partition
    {Q : Type u} [Group Q] [Fintype Q]
    (z : VirtualCharacter Q ℂ) :
    ClassFunction.inverseLinear (VirtualCharacter.realize z) =
      cfConjC (VirtualCharacter.realize z) := by
  ext x
  exact (star_realize_apply_eq_inverse_partition z x).symm

private theorem cfReal_of_virtual_cfConjC
    {Q : Type u} [Group Q] [Fintype Q]
    {phi : ClassFunction Q ℂ}
    (hphi : ClassFunction.IsVirtual phi)
    (hconj : cfConjC phi = phi) :
    cfReal phi := by
  obtain ⟨z, rfl⟩ := hphi
  rw [cfReal, inverseLinear_realize_eq_cfConjC_partition, hconj]

private theorem coeffDot_eq_sum_univ
    {I : Type*} [Fintype I] (a b : IntegralLattice I) :
    coeffDot a b = ∑ i : I, a i * b i := by
  classical
  unfold coeffDot
  change (∑ i ∈ a.support, a i * b i) = ∑ i ∈ Finset.univ, a i * b i
  apply Finset.sum_subset (Finset.subset_univ a.support)
  intro i _ hi
  have hai : a i = 0 := Finsupp.notMem_support_iff.mp hi
  rw [hai, zero_mul]

/-- In characteristic two, a dual-invariant dot product is represented only
by the unique fixed coordinate of the duality involution. -/
private theorem coeffDot_mod_two_eq_fixed
    {I : Type*} [Fintype I] [DecidableEq I]
    (sigma : Equiv.Perm I) (i0 : I)
    (hinvol : ∀ i, sigma (sigma i) = i)
    (hsigma : ∀ i, sigma i = i ↔ i = i0)
    (a b : IntegralLattice I)
    (ha : ∀ i, a (sigma i) = a i)
    (hb : ∀ i, b (sigma i) = b i) :
    ((coeffDot a b : ℤ) : ZMod 2) =
      (a i0 : ZMod 2) * (b i0 : ZMod 2) := by
  let moved : Finset I := Finset.univ.filter fun i ↦ sigma i ≠ i
  have hsigmaMoved : ∀ i, i ∈ moved → sigma i ∈ moved := by
    intro i hi
    simp only [moved, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    intro hfix
    apply hi
    exact sigma.injective hfix
  have hsigmaMovedNe : ∀ i, i ∈ moved → sigma i ≠ i := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hpair (i : I) :
      (a i : ZMod 2) * (b i : ZMod 2) +
          (a (sigma i) : ZMod 2) * (b (sigma i) : ZMod 2) = 0 := by
    rw [ha, hb]
    have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
    calc
      (a i : ZMod 2) * (b i : ZMod 2) +
          (a i : ZMod 2) * (b i : ZMod 2) =
          (2 : ZMod 2) * ((a i : ZMod 2) * (b i : ZMod 2)) := by ring_nf
      _ = 0 := by rw [htwo, zero_mul]
  have hmoved :
      ∑ i ∈ moved, (a i : ZMod 2) * (b i : ZMod 2) = 0 := by
    apply Finset.sum_involution
        (s := moved) (f := fun i ↦ (a i : ZMod 2) * (b i : ZMod 2))
        (fun i _ ↦ sigma i)
    · intro i _
      exact hpair i
    · intro i hi _
      exact hsigmaMovedNe i hi
    · exact hsigmaMoved
    · intro i _
      exact hinvol i
  have hfixed : Finset.univ.filter (fun i ↦ sigma i = i) = {i0} := by
    ext i
    simp [hsigma i]
  rw [coeffDot_eq_sum_univ]
  simp only [Int.cast_sum, Int.cast_mul]
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset I)) (p := fun i ↦ sigma i = i)]
  rw [hfixed, Finset.sum_singleton]
  have hmoved' :
      Finset.univ.filter (fun i ↦ ¬ sigma i = i) = moved := by
    ext i
    simp [moved]
  rw [hmoved', hmoved, add_zero]

private theorem virtualCoefficient_dual
    {Q : Type u} [Group Q] [Fintype Q]
    (z : VirtualCharacter Q ℂ)
    (hz : cfReal (VirtualCharacter.realize z))
    (chi : IrreducibleCharacter Q ℂ) :
    z (IrreducibleCharacter.dual chi) = z chi := by
  apply Int.cast_injective (α := ℂ)
  calc
    (z (IrreducibleCharacter.dual chi) : ℂ) =
        characterPairing
          (IrreducibleCharacter.dual chi : ClassFunction Q ℂ)
          (VirtualCharacter.realize z) :=
      (VirtualCharacter.characterPairing_irreducible_realize
        (IrreducibleCharacter.dual chi) z).symm
    _ = characterPairing
          (ClassFunction.inverseLinear (chi : ClassFunction Q ℂ))
          (VirtualCharacter.realize z) := by
      rw [ClassFunction.inverseLinear_irreducible]
    _ = characterPairing (chi : ClassFunction Q ℂ)
          (ClassFunction.inverseLinear (VirtualCharacter.realize z)) :=
      pairing_inverseLinear_left_partition _ _
    _ = characterPairing (chi : ClassFunction Q ℂ)
          (VirtualCharacter.realize z) := by rw [hz]
    _ = (z chi : ℂ) :=
      VirtualCharacter.characterPairing_irreducible_realize chi z

private theorem evenCharacterPairing_realize_iff
    {Q : Type u} [Group Q] [Fintype Q]
    (a b : VirtualCharacter Q ℂ) :
    evenCharacterPairing (VirtualCharacter.realize a)
        (VirtualCharacter.realize b) ↔
      Even (coeffDot a b) := by
  rw [evenCharacterPairing, VirtualCharacter.characterPairing_realize]
  constructor
  · rintro ⟨n, hn⟩
    apply even_iff_two_dvd.mpr
    refine ⟨n, ?_⟩
    apply Int.cast_injective (α := ℂ)
    simpa [hn]
  · intro h
    obtain ⟨n, hn⟩ := even_iff_two_dvd.mp h
    exact ⟨n, by rw [hn]⟩

private theorem evenCharacterPairing_realize_one_iff
    {Q : Type u} [Group Q] [Fintype Q]
    (a : VirtualCharacter Q ℂ) :
    evenCharacterPairing (VirtualCharacter.realize a)
        ((IrreducibleCharacter.trivial : IrreducibleCharacter Q ℂ) :
          ClassFunction Q ℂ) ↔
      Even (a IrreducibleCharacter.trivial) := by
  let oneV : VirtualCharacter Q ℂ :=
    Finsupp.single IrreducibleCharacter.trivial 1
  have hone : VirtualCharacter.realize oneV =
      ((IrreducibleCharacter.trivial : IrreducibleCharacter Q ℂ) :
        ClassFunction Q ℂ) := by
    rw [VirtualCharacter.realize_single]
    ext x
    simp [oneV, IrreducibleCharacter.trivial_apply]
  rw [← hone, evenCharacterPairing_realize_iff]
  have hdot : coeffDot a oneV = a IrreducibleCharacter.trivial := by
    simpa [oneV] using
      coeffDot_single_right a IrreducibleCharacter.trivial 1
  rw [hdot]

/-- Peterfalvi's parity lemma preceding (7.9). -/
theorem cfdot_real_vchar_even
    {Q : Type u} [Group Q] [Fintype Q]
    (hodd : Odd (Nat.card Q))
    (phi psi : ClassFunction Q ℂ)
    (hphi : ClassFunction.IsVirtual phi ∧ cfReal phi)
    (hpsi : ClassFunction.IsVirtual psi ∧ cfReal psi) :
    evenCharacterPairing phi psi ↔
      evenCharacterPairing phi
          ((IrreducibleCharacter.trivial : IrreducibleCharacter Q ℂ) :
            ClassFunction Q ℂ) ∨
        evenCharacterPairing psi
          ((IrreducibleCharacter.trivial : IrreducibleCharacter Q ℂ) :
            ClassFunction Q ℂ) := by
  obtain ⟨a, rfl⟩ := hphi.1
  obtain ⟨b, rfl⟩ := hpsi.1
  have ha : ∀ chi : IrreducibleCharacter Q ℂ,
      a (IrreducibleCharacter.dual chi) = a chi :=
    virtualCoefficient_dual a hphi.2
  have hb : ∀ chi : IrreducibleCharacter Q ℂ,
      b (IrreducibleCharacter.dual chi) = b chi :=
    virtualCoefficient_dual b hpsi.2
  have hmod := coeffDot_mod_two_eq_fixed
    (IrreducibleCharacter.dualEquiv :
      Equiv.Perm (IrreducibleCharacter Q ℂ))
    IrreducibleCharacter.trivial
    (fun chi ↦ IrreducibleCharacter.dual_dual chi)
    (fun chi ↦ odd_eq_conj_irr1 hodd chi)
    a b ha hb
  rw [evenCharacterPairing_realize_iff,
    evenCharacterPairing_realize_one_iff,
    evenCharacterPairing_realize_one_iff]
  rw [← ZMod.intCast_eq_zero_iff_even,
    ← ZMod.intCast_eq_zero_iff_even,
    ← ZMod.intCast_eq_zero_iff_even]
  rw [hmod, mul_eq_zero]

private theorem starCharacterPairing_eq_characterPairing_of_virtual
    {Q : Type u} [Group Q] [Fintype Q]
    {phi psi : ClassFunction Q ℂ}
    (hphi : ClassFunction.IsVirtual phi)
    (hpsi : ClassFunction.IsVirtual psi) :
    starCharacterPairing phi psi = characterPairing phi psi := by
  obtain ⟨z, rfl⟩ := hphi
  obtain ⟨w, rfl⟩ := hpsi
  exact starCharacterPairing_realize_eq_characterPairing_partition z w

private theorem irreducible_isVirtual_partition
    {Q : Type u} [Group Q] [Fintype Q]
    (chi : IrreducibleCharacter Q ℂ) :
    ClassFunction.IsVirtual (chi : ClassFunction Q ℂ) := by
  refine ⟨Finsupp.single chi 1, ?_⟩
  simp

private theorem cfConjC_dadeInducedTrivial
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    {Q : Subgroup Gamma} (K : Subgroup Q) :
    cfConjC (dadeInducedTrivial K) = dadeInducedTrivial K := by
  unfold dadeInducedTrivial cfConjC
  rw [ClassFunction.mapRingHom_induce]
  congr 1
  ext x
  simp [IrreducibleCharacter.trivial_apply]

private theorem mapRingEquiv_conjugation_eq_dual_partition
    {Q : Type u} [Group Q] [Fintype Q]
    (chi : IrreducibleCharacter Q ℂ) :
    IrreducibleCharacter.mapRingEquiv complexConjugation chi =
      IrreducibleCharacter.dual chi := by
  ext x
  rw [IrreducibleCharacter.mapRingEquiv_apply,
    IrreducibleCharacter.dual_apply]
  change star (chi x) = chi x⁻¹
  exact (irreducibleCharacter_apply_inv_eq_star_partition chi x).symm

/-! ## Orthogonality for disjoint Dade supports -/

private theorem dadeSupport_subgroupNonidentity_invStable
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
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
    have hsa : Commute s a := by
      exact (Subgroup.mem_centralizer_iff.mp
        (Dade_signalizer_cent ddA a hs) a (Subgroup.mem_zpowers a)).symm
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

private theorem dadeSupportSubtype_disjoint
    {Gamma : Type u} [Group Gamma]
    {G L₁ L₂ : Subgroup Gamma} {A₁ A₂ : Set Gamma}
    (ddA₁ : DadeHypothesis G L₁ A₁)
    (ddA₂ : DadeHypothesis G L₂ A₂)
    (hdis : Disjoint (Dade_support ddA₁) (Dade_support ddA₂)) :
    Disjoint
      {x : G | (x : Gamma) ∈ Dade_support ddA₁}
      {x : G | (x : Gamma) ∈ Dade_support ddA₂} := by
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  exact Set.disjoint_left.mp hdis hx₁ hx₂

section DisjointDadeOrtho

variable {Gamma : Type u} [Group Gamma] [Fintype Gamma]
variable {G L₁ L₂ H₁ H₂ : Subgroup Gamma}

local notation "A₁" => subgroupNonidentity H₁
local notation "A₂" => subgroupNonidentity H₂

variable (ddA₁ : DadeHypothesis G L₁ (subgroupNonidentity H₁))
variable (ddA₂ : DadeHypothesis G L₂ (subgroupNonidentity H₂))

/-- Dade maps with disjoint global supports are orthogonal. -/
theorem disjoint_Dade_ortho
    (disjointA : Disjoint (Dade_support ddA₁) (Dade_support ddA₂))
    (phi : ClassFunction L₁ ℂ) (psi : ClassFunction L₂ ℂ) :
    characterPairing (Dade ddA₁ phi) (Dade ddA₂ psi) = 0 := by
  apply characterPairing_eq_zero_of_disjoint_of_invStable_left
    (dadeSupportSubtype_disjoint ddA₁ ddA₂ disjointA)
  · intro x
    change (x : Gamma)⁻¹ ∈ Dade_support ddA₁ ↔
      (x : Gamma) ∈ Dade_support ddA₁
    exact dadeSupport_subgroupNonidentity_invStable ddA₁ (x : Gamma)
  · exact Dade_cfunS ddA₁ phi
  · exact Dade_cfunS ddA₂ psi

private theorem irreducible_dual_sub_supported
    {Q : Type u} [Group Q] [Fintype Q]
    (chi : IrreducibleCharacter Q ℂ) :
    (chi : ClassFunction Q ℂ) -
        (IrreducibleCharacter.dual chi : ClassFunction Q ℂ) ∈
      ClassFunction.supportedOn (nonidentitySet Q) := by
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hx
  have hx1 : x = 1 := by simpa [nonidentitySet] using not_not.mp hx
  subst x
  simp [IrreducibleCharacter.apply_one_eq_finrank]

private theorem isOrthonormalPair_of_realizations
    {Q : Type u} [Group Q] [Fintype Q]
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

/-- Coherent images belonging to two disjoint Dade families are orthogonal.
This is the reusable form of the application of Peterfalvi (4.1). -/
theorem disjoint_coherent_ortho
    (disjointA : Disjoint (Dade_support ddA₁) (Dade_support ddA₂))
    (hoddG : Odd (Nat.card G))
    (K₁ : Subgroup L₁) [K₁.Normal]
    (K₂ : Subgroup L₂) [K₂.Normal]
    (nu₁ : ClassFunction L₁ ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (nu₂ : ClassFunction L₂ ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (coh₁ : coherent_with
      (↑(seqIndD (k := ℂ) K₁ ⊤ ⊥) :
        Set (ClassFunction L₁ ℂ))
      (nonidentitySet L₁) (Dade ddA₁) nu₁)
    (coh₂ : coherent_with
      (↑(seqIndD (k := ℂ) K₂ ⊤ ⊥) :
        Set (ClassFunction L₂ ℂ))
      (nonidentitySet L₂) (Dade ddA₂) nu₂)
    (chi₁ : IrreducibleCharacter L₁ ℂ)
    (chi₂ : IrreducibleCharacter L₂ ℂ)
    (hchi₁ : (chi₁ : ClassFunction L₁ ℂ) ∈
      seqIndD (k := ℂ) K₁ ⊤ ⊥)
    (hchi₂ : (chi₂ : ClassFunction L₂ ℂ) ∈
      seqIndD (k := ℂ) K₂ ⊤ ⊥) :
    characterPairing (nu₁ (chi₁ : ClassFunction L₁ ℂ))
      (nu₂ (chi₂ : ClassFunction L₂ ℂ)) = 0 := by
  let S₁ : Set (ClassFunction L₁ ℂ) :=
    ↑(seqIndD (k := ℂ) K₁ ⊤ ⊥)
  let S₂ : Set (ClassFunction L₂ ℂ) :=
    ↑(seqIndD (k := ℂ) K₂ ⊤ ⊥)
  have hoddL₁ : Odd (Nat.card L₁) :=
    Odd.of_dvd_nat hoddG (Subgroup.card_dvd_of_le ddA₁.2.1)
  have hoddL₂ : Odd (Nat.card L₂) :=
    Odd.of_dvd_nat hoddG (Subgroup.card_dvd_of_le ddA₂.2.1)
  have hdual₁ :
      (IrreducibleCharacter.dual chi₁ : ClassFunction L₁ ℂ) ∈ S₁ := by
    rw [← ClassFunction.inverseLinear_irreducible]
    exact seqInd_inverse_mem (k := ℂ) K₁ ⊤ ⊥ hchi₁
  have hdual₂ :
      (IrreducibleCharacter.dual chi₂ : ClassFunction L₂ ℂ) ∈ S₂ := by
    rw [← ClassFunction.inverseLinear_irreducible]
    exact seqInd_inverse_mem (k := ℂ) K₂ ⊤ ⊥ hchi₂
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
  have hab : IntegralLattice.IsOrthonormalPair a b := by
    apply isOrthonormalPair_of_realizations
    · rw [ha, coh₁.isometry _ hchi₁Span _ hchi₁Span,
        IrreducibleCharacter.characterPairing_self]
    · rw [hb, coh₁.isometry _ hdual₁Span _ hdual₁Span,
        IrreducibleCharacter.characterPairing_self]
    · rw [ha, hb,
        coh₁.isometry _ hchi₁Span _ hdual₁Span]
      simpa only [← ClassFunction.inverseLinear_irreducible] using
        seqInd_conjC_ortho (k := ℂ) K₁ hoddL₁ ⊤ ⊥ hchi₁
  have hcd : IntegralLattice.IsOrthonormalPair c d := by
    apply isOrthonormalPair_of_realizations
    · rw [hc, coh₂.isometry _ hchi₂Span _ hchi₂Span,
        IrreducibleCharacter.characterPairing_self]
    · rw [hd, coh₂.isometry _ hdual₂Span _ hdual₂Span,
        IrreducibleCharacter.characterPairing_self]
    · rw [hc, hd,
        coh₂.isometry _ hchi₂Span _ hdual₂Span]
      simpa only [← ClassFunction.inverseLinear_irreducible] using
        seqInd_conjC_ortho (k := ℂ) K₂ hoddL₂ ⊤ ⊥ hchi₂
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
  have hagree₁ :
      nu₁ ((chi₁ : ClassFunction L₁ ℂ) -
          (IrreducibleCharacter.dual chi₁ : ClassFunction L₁ ℂ)) =
        Dade ddA₁ ((chi₁ : ClassFunction L₁ ℂ) -
          (IrreducibleCharacter.dual chi₁ : ClassFunction L₁ ℂ)) :=
    coh₁.agrees _ hdiff₁Span (irreducible_dual_sub_supported chi₁)
  have hagree₂ :
      nu₂ ((chi₂ : ClassFunction L₂ ℂ) -
          (IrreducibleCharacter.dual chi₂ : ClassFunction L₂ ℂ)) =
        Dade ddA₂ ((chi₂ : ClassFunction L₂ ℂ) -
          (IrreducibleCharacter.dual chi₂ : ClassFunction L₂ ℂ)) :=
    coh₂.agrees _ hdiff₂Span (irreducible_dual_sub_supported chi₂)
  have hpairs :
      characterPairing (VirtualCharacter.realize (a - b))
        (VirtualCharacter.realize (c - d)) = 0 := by
    rw [VirtualCharacter.realize_sub, VirtualCharacter.realize_sub,
      ha, hb, hc, hd, ← map_sub, ← map_sub, hagree₁, hagree₂]
    exact disjoint_Dade_ortho ddA₁ ddA₂ disjointA _ _
  have habOne : VirtualCharacter.realize (a - b) 1 = 0 := by
    rw [VirtualCharacter.realize_sub, ha, hb, ← map_sub, hagree₁,
      Dade1]
  have hcdOne : VirtualCharacter.realize (c - d) 1 = 0 := by
    rw [VirtualCharacter.realize_sub, hc, hd, ← map_sub, hagree₂,
      Dade1]
  have hac := orthonormal_vchar_diff_ortho a b c d hab hcd
    hpairs habOne hcdOne
  simpa only [ha, hc] using hac

end DisjointDadeOrtho

section DadeSubLinNonorthogonal

variable {Gamma : Type u} [Group Gamma] [Fintype Gamma]
variable {G L₁ L₂ : Subgroup Gamma}
variable (H₁ : Subgroup L₁) [H₁.Normal]
variable (H₂ : Subgroup L₂) [H₂.Normal]

local notation "A₁'" =>
  subgroupNonidentity (H₁.map L₁.subtype)
local notation "A₂'" =>
  subgroupNonidentity (H₂.map L₂.subtype)
local notation "S₁'" =>
  seqIndD (k := ℂ) H₁ (⊤ : Subgroup H₁) ⊥
local notation "S₂'" =>
  seqIndD (k := ℂ) H₂ (⊤ : Subgroup H₂) ⊥

variable (ddA₁ : DadeHypothesis G L₁
  (subgroupNonidentity (H₁.map L₁.subtype)))
variable (ddA₂ : DadeHypothesis G L₂
  (subgroupNonidentity (H₂.map L₂.subtype)))

private theorem deltaContext
    (hoddG : Odd (Nat.card G))
    {L : Subgroup Gamma} (H : Subgroup L) [H.Normal]
    (ddA : DadeHypothesis G L
      (subgroupNonidentity (H.map L.subtype)))
    (nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (zeta : IrreducibleCharacter L ℂ)
    (hcoh : coherent_with
      (↑(seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥) :
        Set (ClassFunction L ℂ))
      (nonidentitySet L) (Dade ddA) nu)
    (hzeta : (zeta : ClassFunction L ℂ) ∈
      seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥)
    (hzeta1 : zeta 1 = (H.index : ℂ)) :
    let beta := dadeInd1Beta H ddA (zeta : ClassFunction L ℂ)
    let delta := beta + nu zeta
    characterPairing delta
          ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
            ClassFunction G ℂ) = 1 ∧
      ClassFunction.IsVirtual delta ∧ cfReal delta := by
  let calS := seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥
  let beta := dadeInd1Beta H ddA (zeta : ClassFunction L ℂ)
  let delta := beta + nu zeta
  have hoddL : Odd (Nat.card L) :=
    Odd.of_dvd_nat hoddG (Subgroup.card_dvd_of_le ddA.2.1)
  have hcalS : 1 < calS.card := by
    have htwo : 2 ≤ calS.card := by
      simpa only [calS] using
        seqInd_nontrivial (k := ℂ) H hoddL
          (⊤ : Subgroup H) ⊥ hzeta
    omega
  let data := Dade_Ind1_sub_lin H ddA nu zeta hcoh hcalS hzeta hzeta1
  have hzetaSpan : (zeta : ClassFunction L ℂ) ∈
      AddSubgroup.closure
        (↑calS : Set (ClassFunction L ℂ)) :=
    AddSubgroup.subset_closure hzeta
  have hnuVirtual : ClassFunction.IsVirtual (nu zeta) :=
    hcoh.mapsToVirtual _ hzetaSpan
  have hdeltaVirtual : ClassFunction.IsVirtual delta :=
    data.beta_virtual.add hnuVirtual
  have honeVirtual : ClassFunction.IsVirtual
      ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
        ClassFunction G ℂ) :=
    irreducible_isVirtual_partition IrreducibleCharacter.trivial
  have hdeltaStarOne :
      starCharacterPairing delta
        ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
          ClassFunction G ℂ) = 1 := by
    change starCharacterPairing (beta + nu zeta) _ = 1
    rw [starCharacterPairing_add_left,
      data.beta_pairing_one,
      data.image_orthogonal_one (zeta : ClassFunction L ℂ) hzeta,
      add_zero]
  have hdeltaOne :
      characterPairing delta
        ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
          ClassFunction G ℂ) = 1 := by
    rw [← starCharacterPairing_eq_characterPairing_of_virtual
      hdeltaVirtual honeVirtual]
    exact hdeltaStarOne
  let zetaC : IrreducibleCharacter L ℂ :=
    IrreducibleCharacter.mapRingEquiv complexConjugation zeta
  have hzetaCeq : zetaC = IrreducibleCharacter.dual zeta :=
    mapRingEquiv_conjugation_eq_dual_partition zeta
  have hzetaCmem : (zetaC : ClassFunction L ℂ) ∈ calS := by
    rw [hzetaCeq, ← ClassFunction.inverseLinear_irreducible]
    exact seqInd_inverse_mem (k := ℂ) H ⊤ ⊥ hzeta
  have hzetaCSpan : (zetaC : ClassFunction L ℂ) ∈
      AddSubgroup.closure (↑calS : Set (ClassFunction L ℂ)) :=
    AddSubgroup.subset_closure hzetaCmem
  have hdiffSpan :
      (zeta : ClassFunction L ℂ) - (zetaC : ClassFunction L ℂ) ∈
        AddSubgroup.closure (↑calS : Set (ClassFunction L ℂ)) :=
    (AddSubgroup.closure (↑calS : Set (ClassFunction L ℂ))).sub_mem
      hzetaSpan hzetaCSpan
  have hdiffOn :
      (zeta : ClassFunction L ℂ) - (zetaC : ClassFunction L ℂ) ∈
        ClassFunction.supportedOn (nonidentitySet L) := by
    rw [hzetaCeq]
    exact irreducible_dual_sub_supported zeta
  have hagree :
      nu ((zeta : ClassFunction L ℂ) - (zetaC : ClassFunction L ℂ)) =
        Dade ddA
          ((zeta : ClassFunction L ℂ) - (zetaC : ClassFunction L ℂ)) :=
    hcoh.agrees _ hdiffSpan hdiffOn
  have hconjNu : cfConjC (nu zeta) = nu zetaC := by
    exact cfConjC_Dade_coherent ddA H ⊤ ⊥ hcoh hoddG zeta hzeta
  have hconjBeta :
      cfConjC beta =
        Dade ddA (dadeInducedTrivial H - (zetaC : ClassFunction L ℂ)) := by
    have htriv :
        ClassFunction.mapRingHom (starRingEnd ℂ) (dadeInducedTrivial H) =
          dadeInducedTrivial H := by
      change cfConjC (dadeInducedTrivial H) = dadeInducedTrivial H
      exact cfConjC_dadeInducedTrivial H
    have hzetaConj :
        ClassFunction.mapRingHom (starRingEnd ℂ)
            (zeta : ClassFunction L ℂ) =
          (zetaC : ClassFunction L ℂ) := by
      change cfConjC (zeta : ClassFunction L ℂ) =
        (zetaC : ClassFunction L ℂ)
      rw [cfConjC_irreducible]
    change ClassFunction.mapRingHom (starRingEnd ℂ)
        (Dade ddA (dadeInducedTrivial H - (zeta : ClassFunction L ℂ))) = _
    rw [← Dade_conjC, map_sub, htriv, hzetaConj]
  have hconjDelta : cfConjC delta = delta := by
    change cfConjC (beta + nu zeta) = beta + nu zeta
    rw [map_add, hconjBeta, hconjNu]
    have hsource :
        dadeInducedTrivial H - (zetaC : ClassFunction L ℂ) =
          (dadeInducedTrivial H - (zeta : ClassFunction L ℂ)) +
            ((zeta : ClassFunction L ℂ) - (zetaC : ClassFunction L ℂ)) := by
      abel
    have hnuCancel :
        nu ((zeta : ClassFunction L ℂ) - (zetaC : ClassFunction L ℂ)) +
            nu zetaC = nu zeta := by
      have hsourceCancel :
          ((zeta : ClassFunction L ℂ) - (zetaC : ClassFunction L ℂ)) +
              (zetaC : ClassFunction L ℂ) = zeta := by
        module
      calc
        nu ((zeta : ClassFunction L ℂ) - (zetaC : ClassFunction L ℂ)) +
              nu zetaC =
            nu (((zeta : ClassFunction L ℂ) -
              (zetaC : ClassFunction L ℂ)) + zetaC) :=
          (map_add nu _ _).symm
        _ = nu zeta := congrArg nu hsourceCancel
    calc
      Dade ddA (dadeInducedTrivial H - (zetaC : ClassFunction L ℂ)) +
            nu zetaC =
          (Dade ddA (dadeInducedTrivial H - (zeta : ClassFunction L ℂ)) +
              Dade ddA ((zeta : ClassFunction L ℂ) -
                (zetaC : ClassFunction L ℂ))) + nu zetaC := by
            rw [← map_add, ← hsource]
      _ = (Dade ddA
              (dadeInducedTrivial H - (zeta : ClassFunction L ℂ)) +
            nu ((zeta : ClassFunction L ℂ) -
              (zetaC : ClassFunction L ℂ))) + nu zetaC := by
            rw [hagree]
      _ = Dade ddA
              (dadeInducedTrivial H - (zeta : ClassFunction L ℂ)) +
            nu zeta := by
            rw [add_assoc, hnuCancel]
      _ = beta + nu zeta := rfl
  exact ⟨hdeltaOne, hdeltaVirtual,
    cfReal_of_virtual_cfConjC hdeltaVirtual hconjDelta⟩

set_option maxHeartbeats 2000000 in
/-- Peterfalvi (7.9): for two disjoint Dade families, at least one of the
two linear-subtraction cross pairings is nonzero. -/
theorem Dade_sub_lin_nonorthogonal
    (disjointA : Disjoint (Dade_support ddA₁) (Dade_support ddA₂))
    (hoddG : Odd (Nat.card G))
    (nu₁ : ClassFunction L₁ ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (nu₂ : ClassFunction L₂ ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (coh₁ : coherent_with
      (↑S₁' : Set (ClassFunction L₁ ℂ))
      (nonidentitySet L₁) (Dade ddA₁) nu₁)
    (coh₂ : coherent_with
      (↑S₂' : Set (ClassFunction L₂ ℂ))
      (nonidentitySet L₂) (Dade ddA₂) nu₂)
    (zeta₁ : IrreducibleCharacter L₁ ℂ)
    (zeta₂ : IrreducibleCharacter L₂ ℂ)
    (hzeta₁ : (zeta₁ : ClassFunction L₁ ℂ) ∈ S₁')
    (hzeta₂ : (zeta₂ : ClassFunction L₂ ℂ) ∈ S₂')
    (hzeta₁One : zeta₁ 1 = (H₁.index : ℂ))
    (hzeta₂One : zeta₂ 1 = (H₂.index : ℂ)) :
    starCharacterPairing
        (dadeInd1Beta H₁ ddA₁ (zeta₁ : ClassFunction L₁ ℂ))
        (nu₂ zeta₂) ≠ 0 ∨
      starCharacterPairing
        (dadeInd1Beta H₂ ddA₂ (zeta₂ : ClassFunction L₂ ℂ))
        (nu₁ zeta₁) ≠ 0 := Classical.byContradiction (fun hcross => by
  let beta₁ := dadeInd1Beta H₁ ddA₁ (zeta₁ : ClassFunction L₁ ℂ)
  let beta₂ := dadeInd1Beta H₂ ddA₂ (zeta₂ : ClassFunction L₂ ℂ)
  let delta₁ := beta₁ + nu₁ zeta₁
  let delta₂ := beta₂ + nu₂ zeta₂
  obtain ⟨hdelta₁One, hdelta₁Virtual, hdelta₁Real⟩ :=
    deltaContext hoddG H₁ ddA₁ nu₁ zeta₁ coh₁ hzeta₁ hzeta₁One
  obtain ⟨hdelta₂One, hdelta₂Virtual, hdelta₂Real⟩ :=
    deltaContext hoddG H₂ ddA₂ nu₂ zeta₂ coh₂ hzeta₂ hzeta₂One
  have hdelta₁OneOdd :
      ¬ evenCharacterPairing delta₁
        ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
          ClassFunction G ℂ) := by
    rintro ⟨n, hn⟩
    rw [hdelta₁One] at hn
    have hnCast : ((1 : ℤ) : ℂ) = ((2 * n : ℤ) : ℂ) := by
      simpa only [Int.cast_one] using hn
    have hnInt : (1 : ℤ) = 2 * n := Int.cast_injective hnCast
    omega
  have hdelta₂OneOdd :
      ¬ evenCharacterPairing delta₂
        ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
          ClassFunction G ℂ) := by
    rintro ⟨n, hn⟩
    rw [hdelta₂One] at hn
    have hnCast : ((1 : ℤ) : ℂ) = ((2 * n : ℤ) : ℂ) := by
      simpa only [Int.cast_one] using hn
    have hnInt : (1 : ℤ) = 2 * n := Int.cast_injective hnCast
    omega
  have hdeltaPairOdd : ¬ evenCharacterPairing delta₁ delta₂ := by
    rw [cfdot_real_vchar_even hoddG delta₁ delta₂
      ⟨hdelta₁Virtual, hdelta₁Real⟩
      ⟨hdelta₂Virtual, hdelta₂Real⟩]
    exact not_or_intro hdelta₁OneOdd hdelta₂OneOdd
  have hdeltaPairNe : characterPairing delta₁ delta₂ ≠ 0 := by
    intro hzero
    apply hdeltaPairOdd
    exact ⟨0, by simp [hzero]⟩
  push Not at hcross
  rcases hcross with ⟨hcross₁₂, hcross₂₁⟩
  have hoddL₁ : Odd (Nat.card L₁) :=
    Odd.of_dvd_nat hoddG (Subgroup.card_dvd_of_le ddA₁.2.1)
  have hoddL₂ : Odd (Nat.card L₂) :=
    Odd.of_dvd_nat hoddG (Subgroup.card_dvd_of_le ddA₂.2.1)
  have hcalS₁ : 1 < (S₁').card := by
    have htwo := seqInd_nontrivial (k := ℂ) H₁ hoddL₁ ⊤ ⊥ hzeta₁
    omega
  have hcalS₂ : 1 < (S₂').card := by
    have htwo := seqInd_nontrivial (k := ℂ) H₂ hoddL₂ ⊤ ⊥ hzeta₂
    omega
  let data₁ := Dade_Ind1_sub_lin H₁ ddA₁ nu₁ zeta₁
    coh₁ hcalS₁ hzeta₁ hzeta₁One
  let data₂ := Dade_Ind1_sub_lin H₂ ddA₂ nu₂ zeta₂
    coh₂ hcalS₂ hzeta₂ hzeta₂One
  have hzeta₁Span : (zeta₁ : ClassFunction L₁ ℂ) ∈
      AddSubgroup.closure (↑S₁' : Set (ClassFunction L₁ ℂ)) :=
    AddSubgroup.subset_closure hzeta₁
  have hzeta₂Span : (zeta₂ : ClassFunction L₂ ℂ) ∈
      AddSubgroup.closure (↑S₂' : Set (ClassFunction L₂ ℂ)) :=
    AddSubgroup.subset_closure hzeta₂
  have hnu₁Virtual : ClassFunction.IsVirtual (nu₁ zeta₁) :=
    coh₁.mapsToVirtual _ hzeta₁Span
  have hnu₂Virtual : ClassFunction.IsVirtual (nu₂ zeta₂) :=
    coh₂.mapsToVirtual _ hzeta₂Span
  have hcross₁₂' : characterPairing beta₁ (nu₂ zeta₂) = 0 := by
    rw [← starCharacterPairing_eq_characterPairing_of_virtual
      data₁.beta_virtual hnu₂Virtual]
    exact hcross₁₂
  have hcross₂₁' : characterPairing (nu₁ zeta₁) beta₂ = 0 := by
    rw [characterPairing_comm,
      ← starCharacterPairing_eq_characterPairing_of_virtual
        data₂.beta_virtual hnu₁Virtual]
    exact hcross₂₁
  have hbetaOrtho : characterPairing beta₁ beta₂ = 0 := by
    change characterPairing
      (Dade ddA₁
        (dadeInducedTrivial H₁ - (zeta₁ : ClassFunction L₁ ℂ)))
      (Dade ddA₂
        (dadeInducedTrivial H₂ - (zeta₂ : ClassFunction L₂ ℂ))) = 0
    exact disjoint_Dade_ortho ddA₁ ddA₂ disjointA
      (dadeInducedTrivial H₁ - (zeta₁ : ClassFunction L₁ ℂ))
      (dadeInducedTrivial H₂ - (zeta₂ : ClassFunction L₂ ℂ))
  have hnuOrtho : characterPairing (nu₁ zeta₁) (nu₂ zeta₂) = 0 := by
    exact disjoint_coherent_ortho ddA₁ ddA₂ (disjointA := disjointA) hoddG
      H₁ H₂ nu₁ nu₂ coh₁ coh₂ zeta₁ zeta₂ hzeta₁ hzeta₂
  apply hdeltaPairNe
  change characterPairing (beta₁ + nu₁ zeta₁)
    (beta₂ + nu₂ zeta₂) = 0
  rw [characterPairing_add_left,
    characterPairing_add_right, characterPairing_add_right,
    hbetaOrtho, hcross₁₂', hcross₂₁', hnuOrtho]
  simp)

end DadeSubLinNonorthogonal

/-! ## Coherent Frobenius partitions -/

private theorem Dade_support_eq_classSupport_of_normalizedTI
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    {G L : Subgroup Gamma} {A : Set Gamma}
    (ddA : DadeHypothesis G L A)
    (hTI : IsNormalizedTI A G L) :
    Dade_support ddA = classSupportWithin G A := by
  have hbot : ∀ a : Gamma, a ∈ A → DadeSignalizer ddA a = ⊥ :=
    ((Dade_normedTI_P ddA).mp hTI).2
  ext x
  constructor
  · rintro ⟨a, haA, z, hz, g, hgG, hzx⟩
    rcases Set.mem_mul.mp hz with ⟨s, hs, b, hb, hsb⟩
    have hs1 : s = 1 := by
      rw [hbot a haA] at hs
      simpa using hs
    have hb : b = a := Set.mem_singleton_iff.mp hb
    subst s
    subst b
    simp only [one_mul] at hsb
    subst z
    exact ⟨a, haA, g, hgG, hzx⟩
  · rintro ⟨a, haA, g, hgG, hax⟩
    refine ⟨a, haA, a, ?_, g, hgG, hax⟩
    exact Set.mem_mul.mpr
      ⟨1, (DadeSignalizer ddA a).one_mem,
        a, Set.mem_singleton a, one_mul a⟩

private theorem classSupport_subgroupNonidentity_disjoint_of_coprime
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    (G H₁ H₂ : Subgroup Gamma)
    (hcop : Nat.Coprime (Nat.card H₁) (Nat.card H₂)) :
    Disjoint
      (classSupportWithin G (subgroupNonidentity H₁))
      (classSupportWithin G (subgroupNonidentity H₂)) := by
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  rcases hx₁ with ⟨a, ha, g₁, hg₁, hax⟩
  rcases hx₂ with ⟨b, hb, g₂, hg₂, hbx⟩
  have hconj : IsConj a b := by
    apply isConj_iff.mpr
    refine ⟨g₂ * g₁⁻¹, ?_⟩
    calc
      g₂ * g₁⁻¹ * a * (g₂ * g₁⁻¹)⁻¹ =
          g₂ * (g₁⁻¹ * a * g₁) * g₂⁻¹ := by group
      _ = g₂ * x * g₂⁻¹ :=
        congrArg (fun y : Gamma ↦ g₂ * y * g₂⁻¹) hax
      _ = b := by rw [← hbx]; group
  have hord : orderOf a = orderOf b := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    exact SemiconjBy.orderOf_eq g (mul_inv_eq_iff_eq_mul.mp hg)
  have hda : orderOf a ∣ Nat.card H₁ := by
    let a₁ : H₁ := ⟨a, ha.1⟩
    have := orderOf_dvd_natCard a₁
    simpa only [← Subgroup.orderOf_coe a₁] using this
  have hdb : orderOf a ∣ Nat.card H₂ := by
    let b₂ : H₂ := ⟨b, hb.1⟩
    have := orderOf_dvd_natCard b₂
    rw [hord]
    simpa only [← Subgroup.orderOf_coe b₂] using this
  have hone : orderOf a = 1 := Nat.eq_one_of_dvd_coprimes hcop hda hdb
  exact ha.2 (orderOf_eq_one_iff.mp hone)

/-- The part of `G` left after removing the conjugacy supports of all
nonidentity Frobenius kernels. -/
def coherentFrobeniusRemainder
    {Gamma : Type u} [Group Gamma]
    {I : Type*} [Fintype I]
    (G : Subgroup Gamma) (H : I → Subgroup Gamma) : Set Gamma :=
  (G : Set Gamma) \
    ⋃ i, classSupportWithin G (subgroupNonidentity (H i))

private def coherentFrobeniusIndex
    {Gamma : Type u} [Group Gamma]
    {I : Type*} (L H : I → Subgroup Gamma) (i : I) : ℝ :=
  ((H i).subgroupOf (L i)).index

private def coherentFrobeniusKernelCard
    {Gamma : Type u} [Group Gamma]
    {I : Type*} (H : I → Subgroup Gamma) (i : I) : ℝ :=
  Nat.card (H i)

private theorem coherent_image_signed_irreducible_partition
    {L Q : Type u} [Group L] [Fintype L] [Group Q] [Fintype Q]
    {S : Set (ClassFunction L ℂ)}
    {tau nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction Q ℂ}
    (hnu : coherent_with S (nonidentitySet L) tau nu)
    (chi : IrreducibleCharacter L ℂ)
    (hchi : (chi : ClassFunction L ℂ) ∈ S) :
    ∃ (psi : IrreducibleCharacter Q ℂ) (epsilon : ℤ),
      IsSign epsilon ∧
        nu (chi : ClassFunction L ℂ) =
          (epsilon : ℂ) • (psi : ClassFunction Q ℂ) := by
  have hspan : (chi : ClassFunction L ℂ) ∈ AddSubgroup.closure S :=
    AddSubgroup.subset_closure hchi
  obtain ⟨z, hz⟩ := hnu.mapsToVirtual _ hspan
  have hpair :
      characterPairing (VirtualCharacter.realize z)
          (VirtualCharacter.realize z) = 1 := by
    rw [hz, hnu.isometry _ hspan _ hspan,
      IrreducibleCharacter.characterPairing_self]
  have hnorm : normSq z = 1 := by
    apply Int.cast_injective (α := ℂ)
    unfold normSq
    simpa only [VirtualCharacter.characterPairing_realize, Int.cast_one] using hpair
  obtain ⟨psi, epsilon, hepsilon, hsingle⟩ :=
    eq_signed_single_of_normSq_eq_one z hnorm
  refine ⟨psi, epsilon, hepsilon, ?_⟩
  calc
    nu (chi : ClassFunction L ℂ) = VirtualCharacter.realize z := hz.symm
    _ = (epsilon : ℂ) • (psi : ClassFunction Q ℂ) := by
      rw [hsingle, VirtualCharacter.realize_single]

private theorem frobeniusIndexBounds_partition
    {Q : Type u} [Group Q] [Fintype Q]
    (K R : Subgroup Q)
    (hoddQ : Odd (Nat.card Q))
    (hFrob : IsFrobeniusDecomposition K R) :
    1 < (K.index : ℝ) ∧
      (K.index : ℝ) ≤ ((Nat.card K : ℝ) - 1) / 2 := by
  have hindex : K.index = Nat.card R :=
    hFrob.isComplement.symm.index_eq_card
  constructor
  · rw [hindex]
    exact_mod_cast R.one_lt_card_iff_ne_bot.mpr hFrob.complement_ne_bot
  · exact odd_Frobenius_index_ler K R hoddQ hFrob

private theorem subgroupNonidentity_ncard
    {Q : Type u} [Group Q] [Fintype Q]
    (K : Subgroup Q) :
    (subgroupNonidentity K).ncard = Nat.card K - 1 := by
  have hone : (1 : Q) ∈ (K : Set Q) := K.one_mem
  rw [show subgroupNonidentity K = (K : Set Q) \ {1} by
    ext x
    simp [subgroupNonidentity, nonidentitySet]]
  rw [Set.ncard_sdiff_singleton_of_mem hone, ← Nat.card_coe_set_eq,
    SetLike.coe_sort_coe]

private theorem coherentFrobeniusRemainder_eq_DadeCoverComplement
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    {I : Type*} [Fintype I]
    (G : Subgroup Gamma) (H L : I → Subgroup Gamma)
    (ddA : ∀ i,
      DadeHypothesis G (L i) (subgroupNonidentity (H i)))
    (hTI : ∀ i,
      IsNormalizedTI (subgroupNonidentity (H i)) G (L i)) :
    coherentFrobeniusRemainder G H = DadeCoverComplement ddA := by
  unfold coherentFrobeniusRemainder DadeCoverComplement
  congr 1
  apply Set.iUnion_congr
  intro i
  exact (Dade_support_eq_classSupport_of_normalizedTI
    (ddA i) (hTI i)).symm

private theorem coherentWithDade_of_coherentInduce
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    {G L : Subgroup Gamma}
    (K : Subgroup L) [K.Normal]
    (ddA : DadeHypothesis G L
      (subgroupNonidentity (K.map L.subtype)))
    (hTI : IsNormalizedTI
      (subgroupNonidentity (K.map L.subtype)) G L)
    (nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (hcoh : coherent_with
      (↑(seqIndD (k := ℂ) K (⊤ : Subgroup K) ⊥) :
        Set (ClassFunction L ℂ))
      (nonidentitySet L) (sibleyInduce G L ddA.2.1) nu) :
    coherent_with
      (↑(seqIndD (k := ℂ) K (⊤ : Subgroup K) ⊥) :
        Set (ClassFunction L ℂ))
      (nonidentitySet L) (Dade ddA) nu := by
  refine ⟨hcoh.isometry, hcoh.mapsToVirtual, ?_⟩
  intro phi hphi hoff
  have hspanK :
      phi ∈ ClassFunction.supportedOn (K : Set L) := by
    have hclosure : ∀ {psi : ClassFunction L ℂ},
        psi ∈ AddSubgroup.closure
            (↑(seqIndD (k := ℂ) K (⊤ : Subgroup K) ⊥) :
              Set (ClassFunction L ℂ)) →
          psi ∈ ClassFunction.supportedOn (K : Set L) := by
      intro psi hpsi
      induction hpsi using AddSubgroup.closure_induction with
      | mem xi hxi => exact seqInd_on K hxi
      | zero =>
          exact (ClassFunction.supportedOn (R := ℂ) (K : Set L)).zero_mem
      | add x y hx hy ihx ihy =>
          exact (ClassFunction.supportedOn (R := ℂ) (K : Set L)).add_mem ihx ihy
      | neg x hx ihx =>
          exact (ClassFunction.supportedOn (R := ℂ) (K : Set L)).neg_mem ihx
    exact hclosure hphi
  have hsupport :
      phi ∈ ClassFunction.supportedOn
        {x : L | (x : Gamma) ∈ subgroupNonidentity (K.map L.subtype)} := by
    rw [ClassFunction.mem_supportedOn_iff]
    intro x hx
    by_cases hxK : x ∈ K
    · apply ClassFunction.eq_zero_of_mem_supportedOn hoff
      intro hxne
      apply hx
      exact ⟨⟨x, hxK, rfl⟩, fun hx1 ↦
        hxne (Subtype.ext hx1)⟩
    · exact ClassFunction.eq_zero_of_mem_supportedOn hspanK hxK
  calc
    nu phi = sibleyInduce G L ddA.2.1 phi := hcoh.agrees phi hphi hoff
    _ = Dade ddA phi := (Dade_Ind ddA hTI phi hsupport).symm

private theorem starCharacterPairing_sub_left_partition
    {Q : Type u} [Group Q] [Fintype Q]
    (phi psi theta : ClassFunction Q ℂ) :
    starCharacterPairing (phi - psi) theta =
      starCharacterPairing phi theta - starCharacterPairing psi theta := by
  simp [sub_eq_add_neg, starCharacterPairing,
    twistedCharacterPairing, add_mul, Finset.sum_add_distrib]
  ring_nf

private theorem starCharacterPairing_sub_right_partition
    {Q : Type u} [Group Q] [Fintype Q]
    (phi psi theta : ClassFunction Q ℂ) :
    starCharacterPairing phi (psi - theta) =
      starCharacterPairing phi psi - starCharacterPairing phi theta := by
  simp [sub_eq_add_neg, starCharacterPairing,
    twistedCharacterPairing, mul_add, Finset.sum_add_distrib]

private theorem starCharacterPairing_finset_sum_left_partition
    {Q : Type u} [Group Q] [Fintype Q]
    {J : Type*} (s : Finset J) (phi : J → ClassFunction Q ℂ)
    (psi : ClassFunction Q ℂ) :
    starCharacterPairing (∑ i ∈ s, phi i) psi =
      ∑ i ∈ s, starCharacterPairing (phi i) psi := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, starCharacterPairing_add_left, ih,
        Finset.sum_insert hi]

private theorem starCharacterPairing_finset_sum_right_partition
    {Q : Type u} [Group Q] [Fintype Q]
    (phi : ClassFunction Q ℂ)
    {J : Type*} (s : Finset J) (psi : J → ClassFunction Q ℂ) :
    starCharacterPairing phi (∑ i ∈ s, psi i) =
      ∑ i ∈ s, starCharacterPairing phi (psi i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, starCharacterPairing_add_right, ih,
        Finset.sum_insert hi]

private theorem classFunctionNormSq_add_of_orthogonal_partition
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
    starCharacterPairing_add_left, starCharacterPairing_add_right,
    starCharacterPairing_add_right, horth, horth']
  simp

private theorem classFunctionNormSq_smul_partition
    {Q : Type u} [Group Q] [Fintype Q]
    (a : ℂ) (phi : ClassFunction Q ℂ) :
    classFunctionNormSq (a • phi) =
      Complex.normSq a * classFunctionNormSq phi := by
  unfold classFunctionNormSq
  simp only [ClassFunction.smul_apply, smul_eq_mul, Complex.normSq_mul,
    Finset.mul_sum]
  ring_nf

private theorem classFunctionNormSq_sum_orthogonal_partition
    {Q : Type u} [Group Q] [Fintype Q]
    {J : Type*} [DecidableEq J]
    (s : Finset J) (phi : J → ClassFunction Q ℂ)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      starCharacterPairing (phi i) (phi j) = 0) :
    classFunctionNormSq (∑ i ∈ s, phi i) =
      ∑ i ∈ s, classFunctionNormSq (phi i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [classFunctionNormSq]
  | @insert i s hi ih =>
      have his :
          starCharacterPairing (phi i) (∑ j ∈ s, phi j) = 0 := by
        rw [starCharacterPairing_finset_sum_right_partition]
        apply Finset.sum_eq_zero
        intro j hj
        exact horth i (Finset.mem_insert_self i s) j
          (Finset.mem_insert_of_mem hj) (fun hij ↦ hi (hij ▸ hj))
      rw [Finset.sum_insert hi,
        classFunctionNormSq_add_of_orthogonal_partition _ _ his,
        Finset.sum_insert hi]
      congr 1
      exact ih fun a ha b hb hab ↦
        horth a (Finset.mem_insert_of_mem ha)
          b (Finset.mem_insert_of_mem hb) hab

private theorem virtual_starPairing_integer_partition
    {Q : Type u} [Group Q] [Fintype Q]
    {phi psi : ClassFunction Q ℂ}
    (hphi : ClassFunction.IsVirtual phi)
    (hpsi : ClassFunction.IsVirtual psi) :
    ∃ n : ℤ, starCharacterPairing phi psi = (n : ℂ) := by
  obtain ⟨z, rfl⟩ := hphi
  obtain ⟨w, rfl⟩ := hpsi
  refine ⟨coeffDot z w, ?_⟩
  rw [starCharacterPairing_realize_eq_characterPairing_partition,
    VirtualCharacter.characterPairing_realize]

private theorem one_le_normSq_of_nonzero_integer_partition
    (n : ℤ) (hn : n ≠ 0) :
    1 ≤ Complex.normSq (n : ℂ) := by
  rw [Complex.normSq_intCast]
  have hpos : 0 < n * n := mul_self_pos.mpr hn
  exact_mod_cast (Int.add_one_le_iff.mpr hpos)

private theorem irreducibleCharacter_finrank_pos_partition
    {Q : Type u} [Group Q] [Fintype Q]
    (chi : IrreducibleCharacter Q ℂ) :
    0 < Module.finrank ℂ chi.representation := by
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Nontrivial chi.representation := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    apply CategoryTheory.id_nonzero chi.representation
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro x
    exact Subsingleton.elim _ _
  exact Module.finrank_pos

set_option maxHeartbeats 2000000 in
/-- Peterfalvi (7.10).  Among at least two pairwise coprime Frobenius
kernels, one satisfies the displayed global uncovered-set estimate. -/
theorem coherent_Frobenius_bound
    {Gamma : Type} [Group Gamma] [Fintype Gamma]
    {I : Type*} [Fintype I]
    (G : Subgroup Gamma)
    (hoddG : Odd (Nat.card G))
    (hI : 2 ≤ Nat.card I)
    (L H E : I → Subgroup Gamma)
    (hHL : ∀ i, H i ≤ L i)
    (hEL : ∀ i, E i ≤ L i)
    (frobeniusL_G : ∀ i,
      L i ≤ G ∧ IsSolvable (L i) ∧
        IsFrobeniusDecomposition
          ((H i).subgroupOf (L i))
          ((E i).subgroupOf (L i)))
    (normedTI_A : ∀ i,
      IsNormalizedTI (subgroupNonidentity (H i)) G (L i))
    (card_coprime : ∀ i j, i ≠ j →
      Nat.Coprime (Nat.card (H i)) (Nat.card (H j))) :
    ∃ i,
      let e := coherentFrobeniusIndex L H i
      let h := coherentFrobeniusKernelCard H i
      (e - 1) *
          ((h - 2 * e - 1) / (e * h) +
            2 / (h * (h + 2))) ≤
        (((coherentFrobeniusRemainder G H).ncard : ℝ) - 1) /
          (Nat.card G : ℝ) := by
  classical
  let K : (i : I) → Subgroup (L i) :=
    fun i ↦ (H i).subgroupOf (L i)
  let R : (i : I) → Subgroup (L i) :=
    fun i ↦ (E i).subgroupOf (L i)
  have hKmap (i : I) : (K i).map (L i).subtype = H i := by
    simpa [K] using Subgroup.map_subgroupOf_eq_of_le (hHL i)
  have hRmap (i : I) : (R i).map (L i).subtype = E i := by
    simpa [R] using Subgroup.map_subgroupOf_eq_of_le (hEL i)
  have hFrob (i : I) : IsFrobeniusDecomposition (K i) (R i) :=
    (frobeniusL_G i).2.2
  letI normalK (i : I) : (K i).Normal := (hFrob i).kernel_normal
  have hoddL (i : I) : Odd (Nat.card (L i)) :=
    Odd.of_dvd_nat hoddG
      (Subgroup.card_dvd_of_le (frobeniusL_G i).1)
  let A : I → Set Gamma :=
    fun i ↦ subgroupNonidentity ((K i).map (L i).subtype)
  have hAeq (i : I) : A i = subgroupNonidentity (H i) := by
    simp only [A, hKmap]
  have hTIK (i : I) : IsNormalizedTI (A i) G (L i) := by
    simpa only [hAeq] using normedTI_A i
  have hAinG (i : I) : A i ⊆ (G : Set Gamma) \ {1} := by
    intro x hx
    rw [hAeq] at hx
    exact ⟨(frobeniusL_G i).1 (hHL i hx.1), hx.2⟩
  let ddA : ∀ i, DadeHypothesis G (L i) (A i) :=
    fun i ↦ normedTI_Dade (hTIK i) (hAinG i)
  have hdis (i j : I) (hij : i ≠ j) :
      Disjoint (Dade_support (ddA i)) (Dade_support (ddA j)) := by
    rw [Dade_support_eq_classSupport_of_normalizedTI (ddA i) (hTIK i),
      Dade_support_eq_classSupport_of_normalizedTI (ddA j) (hTIK j),
      hAeq, hAeq]
    exact classSupport_subgroupNonidentity_disjoint_of_coprime
      G (H i) (H j) (card_coprime i j hij)
  have hirrS (i : I) (phi : ClassFunction (L i) ℂ)
      (hphi : phi ∈ seqIndD (k := ℂ) (K i) ⊤ ⊥) :
      IsIrreducibleCharacter (L i) ℂ phi := by
    obtain ⟨theta, htheta, rfl⟩ :=
      (seqIndC1P (k := ℂ) (K i)).mp hphi
    exact irr_induced_Frobenius_ker (hFrob i) theta htheta
  have hzetaExists (i : I) :
      ∃ zeta : IrreducibleCharacter (L i) ℂ,
        (zeta : ClassFunction (L i) ℂ) ∈
            seqIndD (k := ℂ) (K i) ⊤ ⊥ ∧
          zeta 1 = ((K i).index : ℂ) := by
    letI : IsSolvable (L i) := (frobeniusL_G i).2.1
    letI : IsSolvable (K i) := inferInstance
    letI : Nontrivial (K i) :=
      (K i).nontrivial_iff_ne_bot.mpr (hFrob i).kernel_ne_bot
    have hbot : (⊥ : Subgroup (K i)) < ⊤ := by
      exact bot_lt_iff_ne_bot.mpr top_ne_bot
    obtain ⟨phi, hphi, hphiOne⟩ :=
      exists_linInd (K i) (⊥ : Subgroup (K i)) hbot
    exact ⟨⟨phi, hirrS i phi hphi⟩, hphi, hphiOne⟩
  let zeta : ∀ i, IrreducibleCharacter (L i) ℂ :=
    fun i ↦ Classical.choose (hzetaExists i)
  have hzetaMem (i : I) :
      (zeta i : ClassFunction (L i) ℂ) ∈
        seqIndD (k := ℂ) (K i) ⊤ ⊥ :=
    (Classical.choose_spec (hzetaExists i)).1
  have hzetaOne (i : I) : zeta i 1 = ((K i).index : ℂ) :=
    (Classical.choose_spec (hzetaExists i)).2
  have hcohExists (i : I) :
      ∃ nu : ClassFunction (L i) ℂ →ₗ[ℂ] ClassFunction G ℂ,
        coherent_with
          (↑(seqIndD (k := ℂ) (K i) ⊤ ⊥) :
            Set (ClassFunction (L i) ℂ))
          (nonidentitySet (L i)) (Dade (ddA i)) nu := by
    letI : IsSolvable (L i) := (frobeniusL_G i).2.1
    have hnilK : Group.IsNilpotent (K i) :=
      Frobenius_sol_kernel_nil (hFrob i) (frobeniusL_G i).2.1
    let eKH : K i ≃* H i :=
      Subgroup.subgroupOfEquivOfLe (hHL i)
    have hnilH : Group.IsNilpotent (H i) :=
      (Group.isNilpotent_congr eKH).mp hnilK
    obtain ⟨nu, hnuInd⟩ :=
      Sibley_coherence G (L i) (H i) (E i)
        (frobeniusL_G i).1 (hHL i) (hEL i) (hoddL i)
        hnilH (normedTI_A i) (Or.inl (hFrob i))
    refine ⟨nu, ?_⟩
    exact coherentWithDade_of_coherentInduce
      (K i) (ddA i) (hTIK i) nu (by
        simpa only [sibleyFamily, K] using hnuInd)
  let nu : ∀ i,
      ClassFunction (L i) ℂ →ₗ[ℂ] ClassFunction G ℂ :=
    fun i ↦ Classical.choose (hcohExists i)
  have hcoh (i : I) :
      coherent_with
        (↑(seqIndD (k := ℂ) (K i) ⊤ ⊥) :
          Set (ClassFunction (L i) ℂ))
        (nonidentitySet (L i)) (Dade (ddA i)) (nu i) :=
    Classical.choose_spec (hcohExists i)
  have hcalS (i : I) :
      1 < (seqIndD (k := ℂ) (K i) ⊤ ⊥).card := by
    have := seqInd_nontrivial (k := ℂ) (K i) (hoddL i)
      ⊤ ⊥ (hzetaMem i)
    omega
  let data (i : I) :
      DadeInd1SubLinConclusion (K i) (ddA i) (nu i) (zeta i) :=
    Dade_Ind1_sub_lin (K i) (ddA i) (nu i) (zeta i)
      (hcoh i) (hcalS i) (hzetaMem i) (hzetaOne i)
  let e : I → ℝ := fun i ↦ ((K i).index : ℝ)
  let h : I → ℝ := fun i ↦ (Nat.card (H i) : ℝ)
  have hKcard (i : I) : Nat.card (K i) = Nat.card (H i) := by
    exact Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq (hHL i)
  have hebounds (i : I) :
      1 < e i ∧ e i ≤ (h i - 1) / 2 := by
    simpa only [e, h, hKcard] using
      frobeniusIndexBounds_partition (K i) (R i) (hoddL i) (hFrob i)
  have hHcardOne (i : I) : 1 < Nat.card (H i) := by
    rw [← hKcard]
    exact (K i).one_lt_card_iff_ne_bot.mpr (hFrob i).kernel_ne_bot
  have hoddH (i : I) : Odd (Nat.card (H i)) :=
    Odd.of_dvd_nat (hoddL i)
      (Subgroup.card_dvd_of_le (hHL i))
  have hIne : (Finset.univ : Finset I).Nonempty := by
    let hi : Nonempty I :=
      (Nat.card_pos_iff.mp (lt_of_lt_of_le Nat.zero_lt_two hI)).1
    exact ⟨Classical.choice hi, Finset.mem_univ _⟩
  obtain ⟨i₀, -, hminimal⟩ :=
    Finset.exists_min_image Finset.univ
      (fun i ↦ Nat.card (H i)) hIne
  have hgap (i : I) (hi : i ≠ i₀) :
      Nat.card (H i₀) + 2 ≤ Nat.card (H i) := by
    have hle := hminimal i (Finset.mem_univ i)
    have hneCard : Nat.card (H i₀) ≠ Nat.card (H i) := by
      intro heq
      have hcop := card_coprime i₀ i hi.symm
      rw [heq] at hcop
      have hone : Nat.card (H i) = 1 := by
        simpa using hcop
      exact (Nat.ne_of_gt (hHcardOne i)) hone
    rcases hoddH i₀ with ⟨a, ha⟩
    rcases hoddH i with ⟨b, hb⟩
    omega
  let beta (i : I) : ClassFunction G ℂ :=
    dadeInd1Beta (K i) (ddA i)
      (zeta i : ClassFunction (L i) ℂ)
  let chi (i : I) : ClassFunction G ℂ := nu i (zeta i)
  let c (i j : I) : ℂ := starCharacterPairing (beta i) (chi j)
  let calB : Finset I :=
    Finset.univ.filter fun i ↦ i ≠ i₀ ∧ c i i₀ = 0
  let ea (i : I) : ℝ :=
    ((A i).ncard : ℝ) / (Nat.card (L i) : ℝ)
  let sumB : ℝ := ∑ i ∈ calB, ea i
  have hea (i : I) : ea i = (h i - 1) / (e i * h i) := by
    have hAcard : (A i).ncard = Nat.card (H i) - 1 := by
      rw [hAeq, subgroupNonidentity_ncard]
    have hLcard : Nat.card (L i) = (K i).index * Nat.card (H i) := by
      rw [← hKcard, (K i).index_mul_card]
    dsimp only [ea]
    rw [hAcard, hLcard]
    dsimp only [e, h]
    rw [Nat.cast_sub (le_of_lt (hHcardOne i))]
    push_cast
    ring_nf
  have hnuVirtual (i : I) : ClassFunction.IsVirtual (chi i) :=
    (hcoh i).mapsToVirtual _
      (AddSubgroup.subset_closure (hzetaMem i))
  obtain ⟨psi₀, epsilon, hepsilon, hchi₀⟩ :=
    coherent_image_signed_irreducible_partition
      (hcoh i₀) (zeta i₀) (hzetaMem i₀)
  have hepsilonNe : epsilon ≠ 0 := isSign_ne_zero hepsilon
  have hepsilonNorm : Complex.normSq (epsilon : ℂ) = 1 := by
    rcases hepsilon with rfl | rfl <;> norm_num
  have hpsiNorm :
      classFunctionNormSq (psi₀ : ClassFunction G ℂ) = 1 := by
    rw [classFunctionNormSq_eq_re_starCharacterPairing,
      starCharacterPairing_eq_characterPairing_of_virtual
        (irreducible_isVirtual_partition psi₀)
        (irreducible_isVirtual_partition psi₀),
      IrreducibleCharacter.characterPairing_self]
    norm_num
  have hpsiOrth (i : I) (hi : i ≠ i₀) :
      OrthogonalToSeqIndImage (K i) (nu i)
        (psi₀ : ClassFunction G ℂ) := by
    intro xi hxi
    let xiIrr : IrreducibleCharacter (L i) ℂ :=
      ⟨xi, hirrS i xi hxi⟩
    have hchar : characterPairing (nu i xi)
        (nu i₀ (zeta i₀)) = 0 := by
      exact disjoint_coherent_ortho (ddA i) (ddA i₀)
        (disjointA := hdis i i₀ hi) hoddG (K i) (K i₀)
        (nu i) (nu i₀) (hcoh i) (hcoh i₀)
        xiIrr (zeta i₀) hxi (hzetaMem i₀)
    have hstar : starCharacterPairing (nu i xi) (chi i₀) = 0 := by
      rw [starCharacterPairing_eq_characterPairing_of_virtual
        ((hcoh i).mapsToVirtual _ (AddSubgroup.subset_closure hxi))
        (hnuVirtual i₀)]
      exact hchar
    simp only [chi] at hstar
    rw [hchi₀, starCharacterPairing_smul_right] at hstar
    exact (mul_eq_zero.mp hstar).resolve_left
      (star_ne_zero.mpr (Int.cast_ne_zero.mpr hepsilonNe))
  have hcoverLower :
      1 - e i₀ / h i₀ - ea i₀ - sumB ≤
        (((coherentFrobeniusRemainder G H).ncard : ℝ) - 1) /
          (Nat.card G : ℝ) := by
    have hboundInput :
        ((K i₀).index : ℝ) ≤
          ((Nat.card (K i₀) : ℝ) - 1) / 2 := by
      simpa only [e, h, hKcard i₀] using (hebounds i₀).2
    have hbound₀ := (data i₀).norm_bounds hboundInput
    have hnormInv₀ :
        1 - e i₀ / h i₀ ≤
          classFunctionNormSq
            (invDade (ddA i₀) (psi₀ : ClassFunction G ℂ)) := by
      have hscale :
          invDade (ddA i₀) (chi i₀) =
            (epsilon : ℂ) •
              invDade (ddA i₀) (psi₀ : ClassFunction G ℂ) := by
        simp only [chi]
        rw [hchi₀, map_smul]
      rw [hscale, classFunctionNormSq_smul_partition,
        hepsilonNorm, one_mul] at hbound₀
      simpa only [hKcard, e, h] using hbound₀.1
    have hnormOther (i : I) (hi₀ : i ≠ i₀)
        (hiB : i ∉ calB) :
        ea i ≤ classFunctionNormSq
          (invDade (ddA i) (psi₀ : ClassFunction G ℂ)) := by
      have hcNe : c i i₀ ≠ 0 := by
        intro hc
        apply hiB
        simp [calB, hi₀, hc]
      obtain ⟨n, hn⟩ := virtual_starPairing_integer_partition
        (data i).beta_virtual (hnuVirtual i₀)
      have hcEq : c i i₀ = (n : ℂ) := by
        simpa only [c, beta] using hn
      have hnNe : n ≠ 0 := by
        intro hn0
        apply hcNe
        rw [hcEq, hn0]
        simp
      have horth := (data i).orthogonal_irreducible psi₀ (hpsiOrth i hi₀)
      have hnorm := horth.2
      have hpairScale :
          starCharacterPairing (beta i) (psi₀ : ClassFunction G ℂ) =
            (epsilon : ℂ)⁻¹ * c i i₀ := by
        simp only [c, chi]
        rw [hchi₀, starCharacterPairing_smul_right]
        rw [star_intCast]
        field_simp [Int.cast_ne_zero.mpr hepsilonNe]
      have hpairScale' :
          starCharacterPairing
              (dadeInd1Beta (K i) (ddA i)
                (zeta i : ClassFunction (L i) ℂ))
              (psi₀ : ClassFunction G ℂ) =
            (epsilon : ℂ)⁻¹ * c i i₀ := by
        simpa only [beta] using hpairScale
      rw [hpairScale', Complex.normSq_mul, Complex.normSq_inv,
        hepsilonNorm, inv_one, one_mul] at hnorm
      have hone := one_le_normSq_of_nonzero_integer_partition n hnNe
      rw [hcEq] at hnorm
      calc
        ea i ≤ ea i * Complex.normSq (n : ℂ) := by
          apply le_mul_of_one_le_right
          · positivity
          · exact hone
        _ = _ := by simpa only [ea] using hnorm.symm
    have hcover := Dade_cover_inequality ddA hdis
      (psi₀ : ClassFunction G ℂ) hpsiNorm
    have hrem : DadeCoverComplement ddA =
        coherentFrobeniusRemainder G H := by
      ext x
      simp only [DadeCoverComplement, coherentFrobeniusRemainder]
      rw [show (⋃ i, Dade_support (ddA i)) =
          ⋃ i, classSupportWithin G (subgroupNonidentity (H i)) by
        apply Set.iUnion_congr
        intro i
        rw [Dade_support_eq_classSupport_of_normalizedTI
          (ddA i) (hTIK i), hAeq]]
    have honeIn : (1 : Gamma) ∈ DadeCoverComplement ddA := by
      refine ⟨G.one_mem, ?_⟩
      intro hone
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hone
      exact not_support_Dade_1 (ddA i) hi
    have huncovered :
        1 ≤ ∑ g : G,
          if (g : Gamma) ∈ DadeCoverComplement ddA then
            Complex.normSq ((psi₀ : ClassFunction G ℂ) g) else 0 := by
      have hdegree : 1 ≤ Complex.normSq (psi₀ 1) := by
        rw [IrreducibleCharacter.apply_one_eq_finrank]
        rw [Complex.normSq_natCast]
        have hfin : (1 : ℝ) ≤
            (Module.finrank ℂ psi₀.representation : ℝ) := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt (irreducibleCharacter_finrank_pos_partition psi₀))
        nlinarith
      calc
        1 ≤ Complex.normSq ((psi₀ : ClassFunction G ℂ) (1 : G)) :=
          hdegree
        _ = if ((1 : G) : Gamma) ∈ DadeCoverComplement ddA then
              Complex.normSq ((psi₀ : ClassFunction G ℂ) (1 : G))
            else 0 := (if_pos honeIn).symm
        _ ≤ ∑ g : G,
              if (g : Gamma) ∈ DadeCoverComplement ddA then
                Complex.normSq ((psi₀ : ClassFunction G ℂ) g)
              else 0 := by
          exact Finset.single_le_sum
            (s := Finset.univ)
            (f := fun g : G ↦
              if (g : Gamma) ∈ DadeCoverComplement ddA then
                Complex.normSq ((psi₀ : ClassFunction G ℂ) g)
              else 0)
            (fun g _ ↦ by
              by_cases hg : (g : Gamma) ∈ DadeCoverComplement ddA
              · rw [if_pos hg]
                exact Complex.normSq_nonneg _
              · rw [if_neg hg])
            (Finset.mem_univ (1 : G))
    have hsumTerms :
        1 - e i₀ / h i₀ - ea i₀ - sumB ≤
          ∑ i : I,
            (classFunctionNormSq
                (invDade (ddA i) (psi₀ : ClassFunction G ℂ)) - ea i) := by
      rw [← Finset.add_sum_erase Finset.univ
        (fun i : I ↦
          classFunctionNormSq
              (invDade (ddA i) (psi₀ : ClassFunction G ℂ)) - ea i)
        (Finset.mem_univ i₀)]
      apply add_le_add
      · linarith
      · rw [← Finset.sum_filter_add_sum_filter_not
          (s := Finset.univ.erase i₀)
          (p := fun i ↦ i ∈ calB)]
        have hfilterB :
            (Finset.univ.erase i₀).filter (fun i ↦ i ∈ calB) =
              calB := by
          ext i
          simp [calB]
        have hBpart :
            -sumB ≤ ∑ i ∈ (Finset.univ.erase i₀).filter
                (fun i ↦ i ∈ calB),
              (classFunctionNormSq
                  (invDade (ddA i) (psi₀ : ClassFunction G ℂ)) - ea i) := by
          rw [hfilterB]
          simp only [sumB]
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_le_sum
          intro i hi
          have hnonneg := classFunctionNormSq_nonneg
            (invDade (ddA i) (psi₀ : ClassFunction G ℂ))
          linarith
        have houtside :
            0 ≤ ∑ i ∈ (Finset.univ.erase i₀).filter
                (fun i ↦ i ∉ calB),
              (classFunctionNormSq
                  (invDade (ddA i) (psi₀ : ClassFunction G ℂ)) - ea i) := by
          apply Finset.sum_nonneg
          intro i hi
          have hiData := Finset.mem_filter.mp hi
          exact sub_nonneg.mpr
            (hnormOther i (Finset.mem_erase.mp hiData.1).1 hiData.2)
        linarith
    rw [hrem] at hcover huncovered
    have hcardG : 0 < (Nat.card G : ℝ) := Nat.cast_pos.mpr Nat.card_pos
    have hcover' :
        (∑ i : I,
            (classFunctionNormSq
                (invDade (ddA i) (psi₀ : ClassFunction G ℂ)) - ea i)) ≤
          (((coherentFrobeniusRemainder G H).ncard : ℝ) - 1) /
            (Nat.card G : ℝ) := by
      change
        (Nat.card G : ℝ)⁻¹ *
              ((∑ g : G,
                  if (g : Gamma) ∈ coherentFrobeniusRemainder G H then
                    Complex.normSq ((psi₀ : ClassFunction G ℂ) g)
                  else 0) -
                ((coherentFrobeniusRemainder G H).ncard : ℝ)) +
            ∑ i : I,
              (classFunctionNormSq
                  (invDade (ddA i) (psi₀ : ClassFunction G ℂ)) - ea i) ≤
          0 at hcover
      apply (le_div_iff₀ hcardG).2
      have hscaled := mul_le_mul_of_nonneg_left hcover hcardG.le
      field_simp [ne_of_gt hcardG] at hscaled
      have hprod :
          (Nat.card G : ℝ) *
                (∑ i : I,
                  (classFunctionNormSq
                      (invDade (ddA i) (psi₀ : ClassFunction G ℂ)) - ea i)) ≤
            ((coherentFrobeniusRemainder G H).ncard : ℝ) -
              (∑ g : G,
                if (g : Gamma) ∈ coherentFrobeniusRemainder G H then
                  Complex.normSq ((psi₀ : ClassFunction G ℂ) g)
                else 0) := by
        linarith
      calc
        (∑ i : I,
            (classFunctionNormSq
                (invDade (ddA i) (psi₀ : ClassFunction G ℂ)) - ea i)) *
              (Nat.card G : ℝ) =
            (Nat.card G : ℝ) *
              (∑ i : I,
                (classFunctionNormSq
                    (invDade (ddA i) (psi₀ : ClassFunction G ℂ)) - ea i)) := by
          rw [mul_comm]
        _ ≤ ((coherentFrobeniusRemainder G H).ncard : ℝ) -
              (∑ g : G,
                if (g : Gamma) ∈ coherentFrobeniusRemainder G H then
                  Complex.normSq ((psi₀ : ClassFunction G ℂ) g)
                else 0) := hprod
        _ ≤ ((coherentFrobeniusRemainder G H).ncard : ℝ) - 1 := by
          exact sub_le_sub_left huncovered _
    exact hsumTerms.trans hcover'
  have hsumBUpper : sumB ≤ (e i₀ - 1) / (h i₀ + 2) := by
    let phi (i : I) : ClassFunction G ℂ :=
      dadeInd1CoherentSum (K i) (nu i)
    let X : ClassFunction G ℂ :=
      ∑ i ∈ calB, c i₀ i • phi i
    let gamma₀ : ClassFunction G ℂ := (data i₀).gamma
    let gamma₁ : ClassFunction G ℂ := gamma₀ - X
    have hphiNuOrtho (i j : I) (hij : i ≠ j)
        {xi : ClassFunction (L j) ℂ}
        (hxi : xi ∈ seqIndD (k := ℂ) (K j) (⊤ : Subgroup (K j)) ⊥) :
        starCharacterPairing (phi i) (nu j xi) = 0 := by
      unfold phi dadeInd1CoherentSum
      rw [starCharacterPairing_finset_sum_left_partition]
      apply Finset.sum_eq_zero
      intro eta heta
      rw [starCharacterPairing_smul_left]
      let etaIrr : IrreducibleCharacter (L i) ℂ :=
        ⟨eta, hirrS i eta heta⟩
      let xiIrr : IrreducibleCharacter (L j) ℂ :=
        ⟨xi, hirrS j xi hxi⟩
      have ho := disjoint_coherent_ortho
        (ddA i) (ddA j) (disjointA := hdis i j hij) hoddG
        (K i) (K j) (nu i) (nu j) (hcoh i) (hcoh j)
        etaIrr xiIrr heta hxi
      rw [starCharacterPairing_eq_characterPairing_of_virtual
        ((hcoh i).mapsToVirtual _
          (AddSubgroup.subset_closure heta))
        ((hcoh j).mapsToVirtual _
          (AddSubgroup.subset_closure hxi)), ho, mul_zero]
    have hphiOrtho (i j : I) (hij : i ≠ j) :
        starCharacterPairing (phi i) (phi j) = 0 := by
      unfold phi dadeInd1CoherentSum
      simp only [starCharacterPairing_finset_sum_left_partition,
        starCharacterPairing_finset_sum_right_partition,
        starCharacterPairing_smul_left,
        starCharacterPairing_smul_right]
      apply Finset.sum_eq_zero
      intro xj hxj
      rw [mul_eq_zero]
      right
      apply Finset.sum_eq_zero
      intro xi hxi
      let xiIrr : IrreducibleCharacter (L i) ℂ :=
        ⟨xi, hirrS i xi hxi⟩
      let xjIrr : IrreducibleCharacter (L j) ℂ :=
        ⟨xj, hirrS j xj hxj⟩
      have ho := disjoint_coherent_ortho
        (ddA i) (ddA j) (disjointA := hdis i j hij) hoddG
        (K i) (K j) (nu i) (nu j) (hcoh i) (hcoh j)
        xiIrr xjIrr hxi hxj
      rw [starCharacterPairing_eq_characterPairing_of_virtual
        ((hcoh i).mapsToVirtual _ (AddSubgroup.subset_closure hxi))
        ((hcoh j).mapsToVirtual _ (AddSubgroup.subset_closure hxj)), ho]
      simp
    have hphiNorm (i : I) :
        classFunctionNormSq (phi i) = (h i - 1) / e i := by
      let calS : Finset (ClassFunction (L i) ℂ) :=
        seqIndD (k := ℂ) (K i) (⊤ : Subgroup (K i)) ⊥
      have hmemClosure {xi : ClassFunction (L i) ℂ} (hxi : xi ∈ calS) :
          xi ∈ AddSubgroup.closure
            (↑calS : Set (ClassFunction (L i) ℂ)) :=
        AddSubgroup.subset_closure hxi
      have hnuPair {xi mu : ClassFunction (L i) ℂ}
          (hxi : xi ∈ calS) (hmu : mu ∈ calS) :
          starCharacterPairing (nu i xi) (nu i mu) =
            characterPairing xi mu := by
        rw [starCharacterPairing_eq_characterPairing_of_virtual
          ((hcoh i).mapsToVirtual _ (hmemClosure hxi))
          ((hcoh i).mapsToVirtual _ (hmemClosure hmu))]
        exact (hcoh i).isometry xi (hmemClosure hxi) mu (hmemClosure hmu)
      have hcalSOrth : Set.Pairwise
          (↑calS : Set (ClassFunction (L i) ℂ))
          (fun xi mu ↦ characterPairing xi mu = 0) := by
        exact seqInd_orthogonal (K i) _
      have hdegreeStar {xi : ClassFunction (L i) ℂ} (hxi : xi ∈ calS) :
          star (xi 1) = xi 1 := by
        obtain ⟨n, hn⟩ := Cnat_seqInd1 (K i) hxi
        rw [hn]
        simp
      have hpairStar {xi : ClassFunction (L i) ℂ} (hxi : xi ∈ calS) :
          star (characterPairing xi xi) = characterPairing xi xi := by
        let xiIrr : IrreducibleCharacter (L i) ℂ :=
          ⟨xi, hirrS i xi hxi⟩
        have hself : characterPairing xi xi = 1 := by
          exact xiIrr.characterPairing_self
        rw [hself]
        simp
      have hquotStar {xi : ClassFunction (L i) ℂ} (hxi : xi ∈ calS) :
          star (xi 1 / ((K i).index : ℂ) / characterPairing xi xi) =
            xi 1 / ((K i).index : ℂ) / characterPairing xi xi := by
        change (starRingEnd ℂ)
            (xi 1 / ((K i).index : ℂ) / characterPairing xi xi) = _
        have hdegreeStar' := hdegreeStar hxi
        have hpairStar' := hpairStar hxi
        change (starRingEnd ℂ) (xi 1) = xi 1 at hdegreeStar'
        change (starRingEnd ℂ) (characterPairing xi xi) =
          characterPairing xi xi at hpairStar'
        rw [map_div₀, map_div₀, hdegreeStar', hpairStar']
        simp
      have hsumSelf :
          starCharacterPairing (phi i) (phi i) =
            ((Nat.card (K i) : ℂ) - 1) / ((K i).index : ℂ) := by
        unfold phi dadeInd1CoherentSum
        rw [starCharacterPairing_finset_sum_left_partition]
        simp only [starCharacterPairing_finset_sum_right_partition,
          starCharacterPairing_smul_left,
          starCharacterPairing_smul_right]
        calc
          _ = ∑ xi ∈ calS,
              (xi 1 / ((K i).index : ℂ) / characterPairing xi xi) *
                star (xi 1 / ((K i).index : ℂ) /
                  characterPairing xi xi) *
                characterPairing xi xi := by
            apply Finset.sum_congr rfl
            intro xi hxi
            rw [Finset.sum_eq_single xi]
            · rw [hnuPair hxi hxi]
              ring_nf
            · intro mu hmu hne
              rw [hnuPair hxi hmu, hcalSOrth hxi hmu hne.symm]
              simp
            · intro hnot
              exact (hnot hxi).elim
          _ = ((K i).index : ℂ)⁻¹ ^ 2 *
              (∑ xi ∈ calS,
                xi 1 ^ 2 / characterPairing xi xi) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro xi hxi
            rw [hquotStar hxi]
            have hpairNe : characterPairing xi xi ≠ 0 :=
              cfnorm_seqInd_neq0 (K i) hxi
            have hindex : ((K i).index : ℂ) ≠ 0 :=
              Nat.cast_ne_zero.mpr (K i).index_ne_zero_of_finite
            field_simp [hpairNe, hindex]
          _ = ((Nat.card (K i) : ℂ) - 1) /
              ((K i).index : ℂ) := by
            rw [sum_seqIndC1_square (k := ℂ) (K i)]
            have hindex : ((K i).index : ℂ) ≠ 0 :=
              Nat.cast_ne_zero.mpr (K i).index_ne_zero_of_finite
            field_simp [hindex]
      rw [classFunctionNormSq_eq_re_starCharacterPairing, hsumSelf]
      simp only [e, h, hKcard i]
      norm_num
    have hgammaX : starCharacterPairing gamma₁ X = 0 := by
      unfold gamma₁ X
      rw [starCharacterPairing_sub_left_partition]
      apply sub_eq_zero.mpr
      rw [starCharacterPairing_finset_sum_right_partition,
        starCharacterPairing_finset_sum_left_partition]
      apply Finset.sum_congr rfl
      intro i hi
      have hiB := Finset.mem_filter.mp hi
      have hcross := Dade_sub_lin_nonorthogonal
        (H₁ := K i₀) (H₂ := K i)
        (ddA₁ := ddA i₀) (ddA₂ := ddA i)
        (disjointA := hdis i₀ i hiB.2.1.symm)
        hoddG (nu i₀) (nu i) (hcoh i₀) (hcoh i)
        (zeta i₀) (zeta i) (hzetaMem i₀) (hzetaMem i)
        (hzetaOne i₀) (hzetaOne i)
      have _hcNonzero : c i₀ i ≠ 0 :=
        hcross.resolve_right (fun hne ↦ hne
          (by simpa only [c, beta, chi] using hiB.2.2))
      have honeCross {xi : ClassFunction (L i) ℂ}
          (hxi : xi ∈ seqIndD (k := ℂ) (K i)
            (⊤ : Subgroup (K i)) ⊥) :
          starCharacterPairing
              ((IrreducibleCharacter.trivial :
                IrreducibleCharacter G ℂ) : ClassFunction G ℂ)
            (nu i xi) = 0 := by
        calc
          starCharacterPairing
                ((IrreducibleCharacter.trivial :
                  IrreducibleCharacter G ℂ) : ClassFunction G ℂ)
              (nu i xi) =
              star (starCharacterPairing (nu i xi)
                ((IrreducibleCharacter.trivial :
                  IrreducibleCharacter G ℂ) : ClassFunction G ℂ)) :=
            starCharacterPairing_conj_symm _ _
          _ = 0 := by
            rw [(data i).image_orthogonal_one xi hxi]
            simp
      have hchiCross {xi : ClassFunction (L i) ℂ}
          (hxi : xi ∈ seqIndD (k := ℂ) (K i)
            (⊤ : Subgroup (K i)) ⊥) :
          starCharacterPairing (chi i₀) (nu i xi) = 0 := by
        let xiIrr : IrreducibleCharacter (L i) ℂ :=
          ⟨xi, hirrS i xi hxi⟩
        have ho := disjoint_coherent_ortho
          (ddA i₀) (ddA i)
          (disjointA := hdis i₀ i hiB.2.1.symm) hoddG
          (K i₀) (K i) (nu i₀) (nu i) (hcoh i₀) (hcoh i)
          (zeta i₀) xiIrr (hzetaMem i₀) hxi
        rw [starCharacterPairing_eq_characterPairing_of_virtual
          (hnuVirtual i₀)
          ((hcoh i).mapsToVirtual _
            (AddSubgroup.subset_closure hxi))]
        simpa only [chi] using ho
      have hgammaPair {xi : ClassFunction (L i) ℂ}
          (hxi : xi ∈ seqIndD (k := ℂ) (K i)
            (⊤ : Subgroup (K i)) ⊥) :
          starCharacterPairing gamma₀ (nu i xi) =
            starCharacterPairing (beta i₀) (nu i xi) := by
        symm
        rw [show beta i₀ = dadeInd1Beta (K i₀) (ddA i₀)
            (zeta i₀ : ClassFunction (L i₀) ℂ) by rfl,
          (data i₀).decomposition]
        simp only [starCharacterPairing_add_left,
          starCharacterPairing_sub_left_partition,
          starCharacterPairing_smul_left]
        rw [honeCross hxi, hchiCross hxi,
          hphiNuOrtho i₀ i hiB.2.1.symm hxi]
        ring
      have hcoeffXi {xi : ClassFunction (L i) ℂ}
          (hxi : xi ∈ seqIndD (k := ℂ) (K i)
            (⊤ : Subgroup (K i)) ⊥) :
          starCharacterPairing gamma₀ (nu i xi) =
            (c i₀ i / ((K i).index : ℂ)) * xi 1 := by
        rw [hgammaPair hxi]
        let pi : ClassFunction (L i) ℂ :=
          ((zeta i) 1) • xi - (xi 1) • (zeta i : ClassFunction (L i) ℂ)
        have hpiClosure : pi ∈ AddSubgroup.closure
            (↑(seqIndD (k := ℂ) (K i) (⊤ : Subgroup (K i)) ⊥) :
              Set (ClassFunction (L i) ℂ)) := by
          obtain ⟨m, hm⟩ := Cnat_seqInd1 (K i) hxi
          obtain ⟨n, hn⟩ := Cnat_seqInd1 (K i) (hzetaMem i)
          unfold pi
          rw [hm, hn]
          have hnMem := (AddSubgroup.closure
            (↑(seqIndD (k := ℂ) (K i) (⊤ : Subgroup (K i)) ⊥) :
              Set (ClassFunction (L i) ℂ))).nsmul_mem
                (AddSubgroup.subset_closure hxi) n
          have hmMem := (AddSubgroup.closure
            (↑(seqIndD (k := ℂ) (K i) (⊤ : Subgroup (K i)) ⊥) :
              Set (ClassFunction (L i) ℂ))).nsmul_mem
                (AddSubgroup.subset_closure (hzetaMem i)) m
          rw [← Nat.cast_smul_eq_nsmul (R := ℂ) n xi] at hnMem
          rw [← Nat.cast_smul_eq_nsmul (R := ℂ) m
            (zeta i : ClassFunction (L i) ℂ)] at hmMem
          exact (AddSubgroup.closure
            (↑(seqIndD (k := ℂ) (K i) (⊤ : Subgroup (K i)) ⊥) :
              Set (ClassFunction (L i) ℂ))).sub_mem hnMem hmMem
        have hpiOn : pi ∈
            ClassFunction.supportedOn (nonidentitySet (L i)) := by
          have hraw := sub_seqInd_on (K i) hxi (hzetaMem i)
          rw [ClassFunction.mem_supportedOn_iff] at hraw ⊢
          intro x hx
          apply hraw
          intro hxSharp
          apply hx
          simpa [nonidentitySet] using hxSharp.2
        have hagree : nu i pi = Dade (ddA i) pi :=
          (hcoh i).agrees pi hpiClosure hpiOn
        have hpiVirtual : ClassFunction.IsVirtual (Dade (ddA i) pi) := by
          rw [← hagree]
          exact (hcoh i).mapsToVirtual pi hpiClosure
        have hzero :
            starCharacterPairing (beta i₀) (nu i pi) = 0 := by
          rw [hagree,
            starCharacterPairing_eq_characterPairing_of_virtual
              (data i₀).beta_virtual hpiVirtual]
          simpa only [beta, dadeInd1Beta] using
            disjoint_Dade_ortho (ddA i₀) (ddA i)
              (hdis i₀ i hiB.2.1.symm)
              (dadeInducedTrivial (K i₀) -
                (zeta i₀ : ClassFunction (L i₀) ℂ)) pi
        have hlinear :
            starCharacterPairing (beta i₀) (nu i pi) =
              star ((zeta i) 1) *
                  starCharacterPairing (beta i₀) (nu i xi) -
                star (xi 1) * c i₀ i := by
          unfold pi
          rw [map_sub, map_smul, map_smul,
            starCharacterPairing_sub_right_partition,
            starCharacterPairing_smul_right,
            starCharacterPairing_smul_right]
        have hxiStar : star (xi 1) = xi 1 := by
          obtain ⟨n, hn⟩ := Cnat_seqInd1 (K i) hxi
          rw [hn]
          simp
        have hzetaStar :
            star ((zeta i) 1) = ((K i).index : ℂ) := by
          rw [hzetaOne i]
          simp
        have hrel : ((K i).index : ℂ) *
              starCharacterPairing (beta i₀) (nu i xi) =
            xi 1 * c i₀ i := by
          have hrel0 : star ((zeta i) 1) *
                starCharacterPairing (beta i₀) (nu i xi) -
              star (xi 1) * c i₀ i = 0 := hlinear.symm.trans hzero
          rw [hzetaStar, hxiStar] at hrel0
          exact sub_eq_zero.mp hrel0
        have hv : ((K i).index : ℂ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (K i).index_ne_zero_of_finite
        calc
          starCharacterPairing (beta i₀) (nu i xi) =
              ((K i).index : ℂ)⁻¹ *
                (((K i).index : ℂ) *
                  starCharacterPairing (beta i₀) (nu i xi)) := by
            field_simp [hv]
          _ = ((K i).index : ℂ)⁻¹ * (xi 1 * c i₀ i) := by
            rw [hrel]
          _ = (c i₀ i / ((K i).index : ℂ)) * xi 1 := by
            rw [div_eq_mul_inv]
            ring
      have hprojection :
          starCharacterPairing gamma₀ (phi i) =
            c i₀ i * classFunctionNormSq (phi i) := by
        have hdegreeStar {xi : ClassFunction (L i) ℂ}
            (hxi : xi ∈ seqIndD (k := ℂ) (K i)
              (⊤ : Subgroup (K i)) ⊥) :
            star (xi 1) = xi 1 := by
          obtain ⟨n, hn⟩ := Cnat_seqInd1 (K i) hxi
          rw [hn]
          simp
        have hpairStar {xi : ClassFunction (L i) ℂ}
            (hxi : xi ∈ seqIndD (k := ℂ) (K i)
              (⊤ : Subgroup (K i)) ⊥) :
            star (characterPairing xi xi) = characterPairing xi xi := by
          let xiIrr : IrreducibleCharacter (L i) ℂ :=
            ⟨xi, hirrS i xi hxi⟩
          have hself : characterPairing xi xi = 1 :=
            xiIrr.characterPairing_self
          rw [hself]
          simp
        have hquotStar {xi : ClassFunction (L i) ℂ}
            (hxi : xi ∈ seqIndD (k := ℂ) (K i)
              (⊤ : Subgroup (K i)) ⊥) :
            star (xi 1 / ((K i).index : ℂ) /
                characterPairing xi xi) =
              xi 1 / ((K i).index : ℂ) /
                characterPairing xi xi := by
          change (starRingEnd ℂ)
              (xi 1 / ((K i).index : ℂ) /
                characterPairing xi xi) = _
          have hdegreeStar' := hdegreeStar hxi
          have hpairStar' := hpairStar hxi
          change (starRingEnd ℂ) (xi 1) = xi 1 at hdegreeStar'
          change (starRingEnd ℂ) (characterPairing xi xi) =
            characterPairing xi xi at hpairStar'
          rw [map_div₀, map_div₀, hdegreeStar', hpairStar']
          simp
        rw [hphiNorm i]
        unfold phi dadeInd1CoherentSum
        rw [starCharacterPairing_finset_sum_right_partition]
        simp only [starCharacterPairing_smul_right]
        calc
          _ = (((K i).index : ℂ)⁻¹ ^ 2 * c i₀ i) *
                (∑ xi ∈ seqIndD (k := ℂ) (K i)
                  (⊤ : Subgroup (K i)) ⊥,
                  xi 1 ^ 2 / characterPairing xi xi) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro xi hxi
            rw [hquotStar hxi, hcoeffXi hxi]
            ring
          _ = c i₀ i *
                (((Nat.card (K i) : ℂ) - 1) /
                  ((K i).index : ℂ)) := by
            rw [sum_seqIndC1_square (k := ℂ) (K i)]
            have hindex : ((K i).index : ℂ) ≠ 0 :=
              Nat.cast_ne_zero.mpr (K i).index_ne_zero_of_finite
            field_simp [hindex]
          _ = c i₀ i *
                (((h i - 1) / e i : ℝ) : ℂ) := by
            simp only [h, e, hKcard i]
            norm_num
      rw [starCharacterPairing_smul_right,
        starCharacterPairing_smul_left, hprojection]
      rw [starCharacterPairing_finset_sum_right_partition]
      simp only [starCharacterPairing_smul_left,
        starCharacterPairing_smul_right]
      rw [Finset.sum_eq_single i]
      · rw [starCharacterPairing_self_eq_classFunctionNormSq,
          hphiNorm i]
        ring
      · intro j hj hji
        rw [hphiOrtho i j hji.symm, mul_zero]
      · intro hnot
        exact (hnot hi).elim
    have hnormSplit :
        classFunctionNormSq gamma₀ =
          classFunctionNormSq gamma₁ + classFunctionNormSq X := by
      have hsum : gamma₀ = gamma₁ + X := by
        simp [gamma₁]
      rw [hsum, classFunctionNormSq_add_of_orthogonal_partition]
      exact hgammaX
    have hnormX :
        ∑ i ∈ calB,
            Complex.normSq (c i₀ i) * ((h i - 1) / e i) =
          classFunctionNormSq X := by
      unfold X
      rw [classFunctionNormSq_sum_orthogonal_partition]
      · simp_rw [classFunctionNormSq_smul_partition, hphiNorm]
      · intro i hi j hj hij
        rw [starCharacterPairing_smul_left,
          starCharacterPairing_smul_right, hphiOrtho i j hij]
        simp
    have hcoeff (i : I) (hi : i ∈ calB) :
        1 ≤ Complex.normSq (c i₀ i) := by
      have hiData := Finset.mem_filter.mp hi
      have hcross := Dade_sub_lin_nonorthogonal
        (H₁ := K i₀) (H₂ := K i)
        (ddA₁ := ddA i₀) (ddA₂ := ddA i)
        (disjointA := hdis i₀ i hiData.2.1.symm)
        hoddG (nu i₀) (nu i) (hcoh i₀) (hcoh i)
        (zeta i₀) (zeta i) (hzetaMem i₀) (hzetaMem i)
        (hzetaOne i₀) (hzetaOne i)
      have hcNe : c i₀ i ≠ 0 :=
        hcross.resolve_right (fun hne ↦ hne
          (by simpa only [c, beta, chi] using hiData.2.2))
      obtain ⟨n, hn⟩ := virtual_starPairing_integer_partition
        (data i₀).beta_virtual (hnuVirtual i)
      have hnNe : n ≠ 0 := by
        intro hn0
        apply hcNe
        simp only [c, beta]
        rw [hn, hn0]
        simp
      simp only [c, beta]
      rw [hn]
      exact one_le_normSq_of_nonzero_integer_partition n hnNe
    have hweighted :
        (h i₀ + 2) * sumB ≤ classFunctionNormSq X := by
      rw [← hnormX]
      simp only [sumB]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hiData := Finset.mem_filter.mp hi
      have hgapReal : h i₀ + 2 ≤ h i := by
        change (Nat.card (H i₀) : ℝ) + 2 ≤ (Nat.card (H i) : ℝ)
        exact_mod_cast hgap i hiData.2.1
      have hePos : 0 < e i := lt_trans zero_lt_one (hebounds i).1
      have hhOne : 1 < h i := by
        change (1 : ℝ) < (Nat.card (H i) : ℝ)
        exact_mod_cast hHcardOne i
      have hhiPos : 0 < h i := lt_trans zero_lt_one hhOne
      have hcoeffOne := hcoeff i hi
      rw [hea i]
      calc
        (h i₀ + 2) * ((h i - 1) / (e i * h i)) ≤
            h i * ((h i - 1) / (e i * h i)) := by
          exact mul_le_mul_of_nonneg_right hgapReal
            (div_nonneg (sub_nonneg.mpr hhOne.le)
              (mul_nonneg hePos.le hhiPos.le))
        _ = (h i - 1) / e i := by field_simp
        _ ≤ Complex.normSq (c i₀ i) * ((h i - 1) / e i) := by
          exact le_mul_of_one_le_left
            (div_nonneg (sub_nonneg.mpr hhOne.le) hePos.le) hcoeffOne
    have hgammaUpper : classFunctionNormSq gamma₀ ≤ e i₀ - 1 := by
      have hboundInput :
          ((K i₀).index : ℝ) ≤
            ((Nat.card (K i₀) : ℝ) - 1) / 2 := by
        simpa only [e, h, hKcard i₀] using (hebounds i₀).2
      simpa only [gamma₀, e] using
        ((data i₀).norm_bounds hboundInput).2
    have hXle : classFunctionNormSq X ≤ e i₀ - 1 := by
      rw [hnormSplit] at hgammaUpper
      have := classFunctionNormSq_nonneg gamma₁
      linarith
    have hh2Pos : 0 < h i₀ + 2 := by positivity
    apply (le_div_iff₀ hh2Pos).2
    simpa only [mul_comm] using hweighted.trans hXle
  refine ⟨i₀, ?_⟩
  dsimp only [coherentFrobeniusIndex, coherentFrobeniusKernelCard]
  change (e i₀ - 1) *
      ((h i₀ - 2 * e i₀ - 1) / (e i₀ * h i₀) +
        2 / (h i₀ * (h i₀ + 2))) ≤ _
  have heNe : e i₀ ≠ 0 := ne_of_gt (lt_trans zero_lt_one (hebounds i₀).1)
  have hhPos : 0 < h i₀ := by
    change 0 < (Nat.card (H i₀) : ℝ)
    exact_mod_cast Nat.zero_lt_of_lt (hHcardOne i₀)
  have hhNe : h i₀ ≠ 0 := ne_of_gt hhPos
  have hh2Ne : h i₀ + 2 ≠ 0 := by positivity
  have hidentity :
      (e i₀ - 1) *
          ((h i₀ - 2 * e i₀ - 1) / (e i₀ * h i₀) +
            2 / (h i₀ * (h i₀ + 2))) =
        1 - e i₀ / h i₀ - (h i₀ - 1) / (e i₀ * h i₀) -
          (e i₀ - 1) / (h i₀ + 2) := by
    field_simp [heNe, hhNe, hh2Ne]
    ring_nf
  rw [hidentity, ← hea]
  exact le_trans (sub_le_sub_left hsumBUpper _) hcoverLower

/-- Peterfalvi (7.11): the identity cannot be the only element outside the
pairwise disjoint conjugacy supports of the Frobenius kernels. -/
theorem no_coherent_Frobenius_partition
    {Gamma : Type} [Group Gamma] [Fintype Gamma]
    {I : Type*} [Fintype I]
    (G : Subgroup Gamma)
    (hoddG : Odd (Nat.card G))
    (hI : 2 ≤ Nat.card I)
    (L H E : I → Subgroup Gamma)
    (hHL : ∀ i, H i ≤ L i)
    (hEL : ∀ i, E i ≤ L i)
    (frobeniusL_G : ∀ i,
      L i ≤ G ∧ IsSolvable (L i) ∧
        IsFrobeniusDecomposition
          ((H i).subgroupOf (L i))
          ((E i).subgroupOf (L i)))
    (normedTI_A : ∀ i,
      IsNormalizedTI (subgroupNonidentity (H i)) G (L i))
    (card_coprime : ∀ i j, i ≠ j →
      Nat.Coprime (Nat.card (H i)) (Nat.card (H j))) :
    coherentFrobeniusRemainder G H ≠ {1} := by
  intro hpartition
  obtain ⟨i, hi⟩ := coherent_Frobenius_bound G hoddG hI
    L H E hHL hEL frobeniusL_G normedTI_A card_coprime
  let K : Subgroup (L i) := (H i).subgroupOf (L i)
  let R : Subgroup (L i) := (E i).subgroupOf (L i)
  have hoddL : Odd (Nat.card (L i)) :=
    Odd.of_dvd_nat hoddG
      (Subgroup.card_dvd_of_le (frobeniusL_G i).1)
  have hKcard : Nat.card K = Nat.card (H i) := by
    exact Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq (hHL i)
  have hb := frobeniusIndexBounds_partition K R hoddL
    (frobeniusL_G i).2.2
  let e : ℝ := coherentFrobeniusIndex L H i
  let h : ℝ := coherentFrobeniusKernelCard H i
  have he : 1 < e := by simpa [e, coherentFrobeniusIndex, K] using hb.1
  have heh : e ≤ (h - 1) / 2 := by
    have hKcardCast : (Nat.card K : ℝ) = (Nat.card (H i) : ℝ) := by
      exact_mod_cast hKcard
    change ((K.index : ℕ) : ℝ) ≤
      ((Nat.card (H i) : ℝ) - 1) / 2
    simpa only [hKcardCast] using hb.2
  have hh : 1 < h := by
    change 1 < (Nat.card (H i) : ℝ)
    rw [← hKcard]
    exact_mod_cast K.one_lt_card_iff_ne_bot.mpr
      (frobeniusL_G i).2.2.kernel_ne_bot
  have hfirst : 0 ≤ (h - 2 * e - 1) / (e * h) := by
    have hnum : 0 ≤ h - 2 * e - 1 := by linarith
    exact div_nonneg hnum (mul_nonneg (le_of_lt (lt_trans zero_lt_one he))
      (le_of_lt (lt_trans zero_lt_one hh)))
  have hsecond : 0 < 2 / (h * (h + 2)) := by positivity
  have hlhs :
      0 < (e - 1) *
        ((h - 2 * e - 1) / (e * h) + 2 / (h * (h + 2))) := by
    exact mul_pos (sub_pos.mpr he) (add_pos_of_nonneg_of_pos hfirst hsecond)
  rw [hpartition, Set.ncard_singleton] at hi
  dsimp only at hi
  have hi' : (e - 1) *
        ((h - 2 * e - 1) / (e * h) + 2 / (h * (h + 2))) ≤ 0 := by
    simpa only [e, h, Nat.cast_one, sub_self, zero_div] using hi
  exact (not_lt_of_ge hi') hlhs

end

end Submission.OddOrder.PF
