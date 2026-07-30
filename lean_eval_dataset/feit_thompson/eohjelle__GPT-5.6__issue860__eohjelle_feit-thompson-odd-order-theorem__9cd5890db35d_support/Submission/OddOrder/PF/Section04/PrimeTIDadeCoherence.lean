import Submission.OddOrder.PF.Section04.PrimeTIDadeRestrictions
import Submission.OddOrder.PF.Section03.CyclicTISignedDifference
import Submission.OddOrder.PF.Section02.PartitionCentralizerRightCoset
import Submission.OddOrder.PF.Section02.DadeZIsometry
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.RootsOfUnity.Complex
import Submission.OddOrder.MathlibSupport.CharacterValueCyclotomic

/-!
# Dade coherence for the uniform prime-TI columns

This file ports Peterfalvi 4.8 and 4.9, from `prDade_sub_TIirr_on`
through `uniform_prTIred_coherent`.  The coefficient field is specialized to
`ℂ`: the Dade isometry is formulated with the star pairing, and over `ℂ`
complex conjugation of a virtual character is evaluation at the inverse.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical Pointwise
open Submission.OddOrder.MathlibSupport

universe u

variable {Gamma : Type} [Group Gamma] [Fintype Gamma]
  {G L K H W W₁ W₂ : Subgroup Gamma}
  {A A₀ : Set Gamma}
  {defW : IsInternalDirectProductIn W₁ W₂ W}

local instance subgroupCoeTCToAmbient (S : Subgroup Gamma) :
    CoeTC S Gamma :=
  ⟨fun x ↦ x.1⟩

local instance subgroupOfCoeTCToAmbient (S T : Subgroup Gamma) :
    CoeTC (S.subgroupOf T) Gamma :=
  ⟨fun x ↦ x.1.1⟩

local instance primeTIDadeCoherenceInvertibleCard
    {Q : Type u} [Group Q] [Fintype Q] :
    Invertible (Nat.card Q : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-- For a complex representation of a finite group, inversion of the group
element is complex conjugation of the character value.  Keeping the short
finite-order trace argument here avoids making PF Section 4 depend on the
unrelated Appendix C development. -/
private theorem representation_character_inv_eq_star
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

private theorem irreducibleCharacter_apply_inv_eq_star
    {Q : Type u} [Group Q] [Fintype Q]
    (chi : IrreducibleCharacter Q ℂ) (g : Q) :
    chi g⁻¹ = star (chi g) := by
  rw [← chi.representation_character,
    ← chi.representation_character]
  exact representation_character_inv_eq_star
    chi.representation.ρ g

private theorem characterPairing_fintype_sum_left
    {Q I : Type*} [Group Q] [Fintype Q] [Fintype I]
    (f : I → ClassFunction Q ℂ) (g : ClassFunction Q ℂ) :
    characterPairing (∑ i, f i) g =
      ∑ i, characterPairing (f i) g := by
  change characterPairingRight g (∑ i, f i) = _
  exact map_sum (characterPairingRight g) f Finset.univ

private theorem characterPairing_fintype_sum_right
    {Q I : Type*} [Group Q] [Fintype Q] [Fintype I]
    (f : ClassFunction Q ℂ) (g : I → ClassFunction Q ℂ) :
    characterPairing f (∑ i, g i) =
      ∑ i, characterPairing f (g i) := by
  change characterPairingLeft f (∑ i, g i) = _
  exact map_sum (characterPairingLeft f) g Finset.univ

private theorem characterPairing_neg_left
    {Q : Type*} [Group Q] [Fintype Q]
    (f g : ClassFunction Q ℂ) :
    characterPairing (-f) g = -characterPairing f g := by
  change characterPairingRight g (-f) = _
  exact map_neg (characterPairingRight g) f

private theorem characterPairing_neg_right
    {Q : Type*} [Group Q] [Fintype Q]
    (f g : ClassFunction Q ℂ) :
    characterPairing f (-g) = -characterPairing f g := by
  change characterPairingLeft f (-g) = _
  exact map_neg (characterPairingLeft f) g

private theorem star_realize_apply_eq_inverse
    {Q : Type u} [Group Q] [Fintype Q]
    (z : VirtualCharacter Q ℂ) (x : Q) :
    star (VirtualCharacter.realize z x) =
      VirtualCharacter.realize z x⁻¹ := by
  classical
  induction z using Finsupp.induction with
  | zero => simp
  | single_add chi n z hchi hn ih =>
      rw [VirtualCharacter.realize_add,
        VirtualCharacter.realize_single]
      have hchiStar : star (chi.1 x) = chi.1 x⁻¹ :=
        (irreducibleCharacter_apply_inv_eq_star chi x).symm
      calc
        star ((n : ℂ) * chi.1 x +
            VirtualCharacter.realize z x) =
            star ((n : ℂ) * chi.1 x) +
              star (VirtualCharacter.realize z x) :=
          map_add (starRingEnd ℂ) _ _
        _ = star (n : ℂ) * star (chi.1 x) +
              star (VirtualCharacter.realize z x) := by
          exact congrArg
            (fun t : ℂ ↦ t + star (VirtualCharacter.realize z x))
            (map_mul (starRingEnd ℂ) (n : ℂ) (chi.1 x))
        _ = (n : ℂ) * chi.1 x⁻¹ +
              VirtualCharacter.realize z x⁻¹ := by
          have hnStar : star (n : ℂ) = (n : ℂ) :=
            map_intCast (starRingEnd ℂ) n
          exact congrArg₂ (fun a b : ℂ ↦ a + b)
            (congrArg₂ (fun a b : ℂ ↦ a * b) hnStar hchiStar)
            ih

private theorem starCharacterPairing_realize_eq_characterPairing
    {Q : Type u} [Group Q] [Fintype Q]
    (z w : VirtualCharacter Q ℂ) :
    starCharacterPairing (VirtualCharacter.realize z)
        (VirtualCharacter.realize w) =
      characterPairing (VirtualCharacter.realize z)
        (VirtualCharacter.realize w) := by
  apply starCharacterPairing_eq_characterPairing_of_star_apply_eq_inv
  exact star_realize_apply_eq_inverse w

private theorem finsupp_sum_zsmul_sub
    {I M : Type*} [AddCommGroup M]
    (z : I →₀ ℤ) (f : I → M) (a : M) :
    z.sum (fun i n ↦ n • (f i - a)) =
      z.sum (fun i n ↦ n • f i) -
        (z.sum fun _ n ↦ n) • a := by
  classical
  simp only [Finsupp.sum]
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul]

private theorem finsupp_sum_zsmul_apply_one
    {Q I : Type*} [Group Q]
    (z : I →₀ ℤ) (f : I → ClassFunction Q ℂ) (d : ℂ)
    (hdegree : ∀ i, f i 1 = d) :
    (z.sum fun i n ↦ n • f i) 1 =
      ((z.sum fun _ n ↦ n : ℤ) : ℂ) * d := by
  classical
  simp only [Finsupp.sum, ClassFunction.finset_sum_apply,
    ← Int.cast_smul_eq_zsmul ℂ]
  simp only [ClassFunction.smul_apply, Pi.smul_apply, smul_eq_mul,
    hdegree]
  push_cast
  rw [Finset.sum_mul]

private def primeTIRedCoherentTarget
    (pti : PrimeTIHypothesis L K W W₁ W₂ defW)
    (isoL : CyclicTIIsometryData (k := ℂ) pti.prime_cycTIhyp)
    {hG : CyclicTIHypothesis G W W₁ W₂ defW}
    (isoG : CyclicTIIsometryData (k := ℂ) hG)
    (j₀ j : IrreducibleCharacter W₂ ℂ) : ClassFunction G ℂ :=
  (pti.primeTISign isoL j₀ : ℂ) •
    ∑ i : IrreducibleCharacter W₁ ℂ,
      isoG.cyclicTIImage (i, j)

private def primeTIRedCoherentMap
    (pti : PrimeTIHypothesis L K W W₁ W₂ defW)
    (isoL : CyclicTIIsometryData (k := ℂ) pti.prime_cycTIhyp)
    {hG : CyclicTIHypothesis G W W₁ W₂ defW}
    (isoG : CyclicTIIsometryData (k := ℂ) hG)
    (j₀ : IrreducibleCharacter W₂ ℂ) :
    ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ where
  toFun phi :=
    ∑ j : IrreducibleCharacter W₂ ℂ,
      ((Nat.card W₁ : ℂ)⁻¹ *
          characterPairing (pti.primeTIRed isoL j) phi) •
        primeTIRedCoherentTarget pti isoL isoG j₀ j
  map_add' phi psi := by
    simp only [characterPairing_add_right, mul_add, add_smul,
      Finset.sum_add_distrib]
  map_smul' c phi := by
    simp only [characterPairing_smul_right, smul_smul,
      Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    simp only [RingHom.id_apply]
    ring

private theorem primeTIRedCoherentMap_apply
    (pti : PrimeTIHypothesis L K W W₁ W₂ defW)
    (isoL : CyclicTIIsometryData (k := ℂ) pti.prime_cycTIhyp)
    {hG : CyclicTIHypothesis G W W₁ W₂ defW}
    (isoG : CyclicTIIsometryData (k := ℂ) hG)
    (j₀ : IrreducibleCharacter W₂ ℂ)
    (phi : ClassFunction L ℂ) :
    primeTIRedCoherentMap pti isoL isoG j₀ phi =
      ∑ j : IrreducibleCharacter W₂ ℂ,
        ((Nat.card W₁ : ℂ)⁻¹ *
            characterPairing (pti.primeTIRed isoL j) phi) •
          primeTIRedCoherentTarget pti isoL isoG j₀ j :=
  rfl

private theorem primeTIRedCoherentMap_primeTIRed
    (pti : PrimeTIHypothesis L K W W₁ W₂ defW)
    (isoL : CyclicTIIsometryData (k := ℂ) pti.prime_cycTIhyp)
    {hG : CyclicTIHypothesis G W W₁ W₂ defW}
    (isoG : CyclicTIIsometryData (k := ℂ) hG)
    (j₀ j : IrreducibleCharacter W₂ ℂ) :
    primeTIRedCoherentMap pti isoL isoG j₀
        (pti.primeTIRed isoL j) =
      primeTIRedCoherentTarget pti isoL isoG j₀ j := by
  classical
  rw [primeTIRedCoherentMap_apply, Finset.sum_eq_single j]
  · rw [pti.cfdot_prTIred isoL, if_pos rfl]
    field_simp [Nat.cast_ne_zero.mpr (Nat.card_pos.ne' : Nat.card W₁ ≠ 0)]
    simp
  · intro r _ hrj
    rw [pti.cfdot_prTIred isoL, if_neg hrj]
    simp
  · simp

private theorem characterPairing_primeTIRedCoherentTarget
    (pti : PrimeTIHypothesis L K W W₁ W₂ defW)
    (isoL : CyclicTIIsometryData (k := ℂ) pti.prime_cycTIhyp)
    {hG : CyclicTIHypothesis G W W₁ W₂ defW}
    (isoG : CyclicTIIsometryData (k := ℂ) hG)
    (j₀ j r : IrreducibleCharacter W₂ ℂ) :
    characterPairing
        (primeTIRedCoherentTarget pti isoL isoG j₀ j)
        (primeTIRedCoherentTarget pti isoL isoG j₀ r) =
      if j = r then (Nat.card W₁ : ℂ) else 0 := by
  letI : IsCyclic W₁ := pti.complement_cyclic
  have hepsilon :
      (pti.primeTISign isoL j₀ : ℂ) *
          (pti.primeTISign isoL j₀ : ℂ) = 1 := by
    rcases pti.primeTISign_isSign isoL j₀ with h | h <;>
      simp [h]
  rw [primeTIRedCoherentTarget, primeTIRedCoherentTarget,
    characterPairing_smul_left, characterPairing_smul_right,
    characterPairing_fintype_sum_left]
  simp_rw [characterPairing_fintype_sum_right,
    isoG.characterPairing_cyclicTIImage]
  by_cases hjr : j = r
  · subst r
    simp [Prod.ext_iff,
      IrreducibleCharacter.card_eq_natCard_of_isCyclic]
    rw [← mul_assoc, hepsilon, one_mul]
  · simp [Prod.ext_iff, hjr]

private theorem primeTIRedCoherentMap_isometry_on_span
    (pti : PrimeTIHypothesis L K W W₁ W₂ defW)
    (isoL : CyclicTIIsometryData (k := ℂ) pti.prime_cycTIhyp)
    {hG : CyclicTIHypothesis G W W₁ W₂ defW}
    (isoG : CyclicTIIsometryData (k := ℂ) hG)
    (j₀ : IrreducibleCharacter W₂ ℂ)
    (T : Set (ClassFunction L ℂ))
    (hT : T ⊆ Set.range (pti.primeTIRed isoL))
    {phi psi : ClassFunction L ℂ}
    (hphi : phi ∈ AddSubgroup.closure T)
    (hpsi : psi ∈ AddSubgroup.closure T) :
    characterPairing
        (primeTIRedCoherentMap pti isoL isoG j₀ phi)
        (primeTIRedCoherentMap pti isoL isoG j₀ psi) =
      characterPairing phi psi := by
  induction hphi, hpsi using AddSubgroup.closure_induction₂ with
  | mem f g hf hg =>
      obtain ⟨j, rfl⟩ := hT hf
      obtain ⟨r, rfl⟩ := hT hg
      rw [primeTIRedCoherentMap_primeTIRed,
        primeTIRedCoherentMap_primeTIRed,
        characterPairing_primeTIRedCoherentTarget,
        pti.cfdot_prTIred isoL]
  | zero_left => simp
  | zero_right => simp
  | add_left f g q hf hg hq ihf ihg =>
      simp only [map_add, characterPairing_add_left, ihf, ihg]
  | add_right f g q hf hg hq ihf ihg =>
      simp only [map_add, characterPairing_add_right, ihf, ihg]
  | neg_left f g hf hg ih =>
      simp only [map_neg, characterPairing_neg_left, ih]
  | neg_right f g hf hg ih =>
      simp only [map_neg, characterPairing_neg_right, ih]

/-- The cyclic-TI support has no kernel elements.  This is the direct-product
form of the source calculation `V \subset ~: K`: an element of `K \cap W`
has trivial `W₁` coordinate because `K` and `W₁` have coprime orders,
and hence lies in `W₂`. -/
private theorem cyclicTISet_subset_kernel_compl
    (pti : PrimeTIHypothesis L K W W₁ W₂ defW) :
    cyclicTISet W W₁ W₂ ⊆ (K : Set Gamma)ᶜ := by
  intro a ha haK
  have haW : a ∈ W := (mem_cyclicTISet.mp ha).1
  let aW : W := ⟨a, haW⟩
  let p : W₁ × W₂ := defW.mulEquiv.symm aW
  have haDecomp : a = (p.1 : Gamma) * (p.2 : Gamma) := by
    have h := defW.coe_mulEquiv_apply p
    rw [defW.mulEquiv.apply_symm_apply] at h
    simpa [aW] using h
  have hp₁K : (p.1 : Gamma) ∈ K := by
    rw [haDecomp] at haK
    have hp₂K : (p.2 : Gamma) ∈ K :=
      pti.fixed_le_kernel p.2.property
    have := K.mul_mem haK (K.inv_mem hp₂K)
    simpa [mul_assoc] using this
  have hdisjoint : Disjoint K W₁ :=
    Subgroup.disjoint_of_coprime_natCard
      pti.kernel_complement_card_coprime
  have hp₁one : p.1 = 1 := by
    apply Subtype.ext
    apply Subgroup.mem_bot.mp
    rw [← disjoint_iff.mp hdisjoint]
    exact ⟨hp₁K, p.1.property⟩
  have haW₂ : a ∈ W₂ := by
    have hp := (defW.mulEquiv_mem_right_iff p).mpr hp₁one
    rw [haDecomp]
    exact hp
  exact (mem_cyclicTISet.mp ha).2.2 haW₂

namespace PrimeDadeHypothesis

variable (pd : PrimeDadeHypothesis G L K H A A₀ W W₁ W₂ defW)

/-- Peterfalvi 4.8, first part: equal-degree entries in one row have
difference supported on the enlarged Dade set. -/
theorem prDade_sub_TIirr_on
    (isoL : CyclicTIIsometryData (k := ℂ)
      pd.prDade_prTI.prime_cycTIhyp)
    (i : IrreducibleCharacter W₁ ℂ)
    (j r : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial)
    (hr : r ≠ IrreducibleCharacter.trivial)
    (hdegree :
      pd.prDade_prTI.primeTICharacter isoL i j 1 =
        pd.prDade_prTI.primeTICharacter isoL i r 1) :
    pd.prDade_prTI.primeTICharacter isoL i j -
        pd.prDade_prTI.primeTICharacter isoL i r ∈
      ClassFunction.supportedOn {x : L | (x : Gamma) ∈ A₀} := by
  let pti := pd.prDade_prTI
  letI : IsCyclic W₂ := pti.fixed_cyclic
  rw [ClassFunction.mem_supportedOn_iff]
  intro g hgA₀
  rw [ClassFunction.sub_apply, sub_eq_zero]
  rcases pti.semidirect_complement.2 g with ⟨⟨kL, xL⟩, hkxL⟩
  let k₀ : K := ⟨((kL : L) : Gamma), kL.property⟩
  let x₀ : W₁ := ⟨((xL : L) : Gamma), xL.property⟩
  have hgDecomp : (k₀ : Gamma) * (x₀ : Gamma) = (g : Gamma) := by
    simpa [k₀, x₀] using congrArg Subtype.val hkxL
  by_cases hx : x₀ = 1
  · by_cases hg : g = 1
    · simpa [hg] using hdegree
    · have hgK : (g : Gamma) ∈ K := by
        have hkg : (k₀ : Gamma) = (g : Gamma) := by
          simpa [hx] using hgDecomp
        rw [← hkg]
        exact k₀.property
      let gK : K.subgroupOf L := ⟨g, hgK⟩
      have hgA : (g : Gamma) ∉ A := by
        intro hga
        exact hgA₀ (pd.set_subset_dadeSet hga)
      have hgOne : (gK : Gamma) ≠ 1 := by
        intro h
        apply hg
        apply Subtype.ext
        simpa [gK] using h
      have hgSupp : gK ∉ primeDadeSupport (K.subgroupOf L) A := by
        rw [mem_primeDadeSupport, not_or]
        exact ⟨hgOne, hgA⟩
      have hjzero :
          (pti.primeTI_Ires isoL j :
            ClassFunction (K.subgroupOf L) ℂ) gK = 0 :=
        ClassFunction.eq_zero_of_mem_supportedOn
          (pd.prDade_TIres_on isoL j hj)
          hgSupp
      have hrzero :
          (pti.primeTI_Ires isoL r :
            ClassFunction (K.subgroupOf L) ℂ) gK = 0 :=
        ClassFunction.eq_zero_of_mem_supportedOn
          (pd.prDade_TIres_on isoL r hr)
          hgSupp
      have hresj := congrArg
        (fun f : ClassFunction (K.subgroupOf L) ℂ ↦ f gK)
        (pti.cfRes_prTIirr isoL i j)
      have hresr := congrArg
        (fun f : ClassFunction (K.subgroupOf L) ℂ ↦ f gK)
        (pti.cfRes_prTIirr isoL i r)
      rw [hjzero] at hresj
      rw [hrzero] at hresr
      exact hresj.trans hresr.symm
  · have hxNorm :
        (x₀ : Gamma) ∈ Subgroup.normalizer (K : Set Gamma) :=
        pti.group_le_normalizer_kernel
          (pti.complement_le_group x₀.property)
    have hxCop : Nat.Coprime (Nat.card K) (orderOf (x₀ : Gamma)) :=
      pti.kernel_complement_card_coprime.coprime_dvd_right
        (W₁.orderOf_dvd_natCard x₀.property)
    have hpart := partition_cent_rcoset K (x₀ : Gamma) hxNorm hxCop
    let conjugationAction := subgroupConjugationActionOnAmbient K
    letI : SMul K Gamma := conjugationAction.toSMul
    letI : MulAction K Gamma := conjugationAction.toMulAction
    letI : MulAction K (Set Gamma) := Set.mulActionSet
    let C := centralizerWithin K (Subgroup.zpowers (x₀ : Gamma))
    have hC : C = W₂ := pti.centralizer_kernel x₀ hx
    have hgCoset :
        (g : Gamma) ∈ (K : Set Gamma) * ({(x₀ : Gamma)} : Set Gamma) := by
      exact Set.mem_mul.mpr
        ⟨(k₀ : Gamma), k₀.property, (x₀ : Gamma), by simp,
          hgDecomp⟩
    have hgUnion : (g : Gamma) ∈
        ⋃₀ (MulAction.orbit K
          ((C : Set Gamma) * ({(x₀ : Gamma)} : Set Gamma))) := by
      rw [hpart.1.1]
      exact hgCoset
    rcases Set.mem_sUnion.mp hgUnion with ⟨S, hS, hgS⟩
    rcases hS with ⟨y, rfl⟩
    rcases Set.mem_smul_set.mp hgS with ⟨z, hz, hzg⟩
    rcases Set.mem_mul.mp hz with ⟨c, hc, t, ht, hct⟩
    have htEq : t = (x₀ : Gamma) := Set.mem_singleton_iff.mp ht
    subst t
    have hconj :
        (g : Gamma) =
          (y : Gamma) * (c * (x₀ : Gamma)) * (y : Gamma)⁻¹ := by
      change (y : Gamma) * z * (y : Gamma)⁻¹ = (g : Gamma) at hzg
      rw [← hzg, ← hct]
    have hcW₂ : c ∈ W₂ := by
      rw [← hC]
      exact hc
    have hcOne : c = 1 := by
      by_contra hcNe
      let c₀ : W₂ := ⟨c, hcW₂⟩
      have hc₀Ne : c₀ ≠ 1 := by
        intro h
        exact hcNe (congrArg Subtype.val h)
      have hprodV :
          (((defW.mulEquiv (x₀, c₀) : W) : Gamma)) ∈
            cyclicTISet W W₁ W₂ := by
        rw [mem_cyclicTISet, defW.mulEquiv_mem_left_iff,
          defW.mulEquiv_mem_right_iff]
        exact ⟨(defW.mulEquiv (x₀, c₀)).property, hc₀Ne, hx⟩
      have hcxV : c * (x₀ : Gamma) ∈ cyclicTISet W W₁ W₂ := by
        have hprod :
            (((defW.mulEquiv (x₀, c₀) : W) : Gamma)) =
              c * (x₀ : Gamma) := by
          exact (defW.commute x₀ c₀).eq
        rwa [hprod] at hprodV
      have hgClass : (g : Gamma) ∈
          classSupportWithin L (cyclicTISet W W₁ W₂) := by
        refine ⟨c * (x₀ : Gamma), hcxV, ?_⟩
        refine ⟨(y : Gamma)⁻¹,
          L.inv_mem (pti.kernel_le_group y.property), ?_⟩
        simpa using hconj.symm
      apply hgA₀
      rw [pd.prDade_def.dadeSet_eq]
      exact Or.inr hgClass
    have hconjL :
        g =
          (⟨(y : Gamma), pti.kernel_le_group y.property⟩ : L) *
            (⟨(x₀ : Gamma), pti.complement_le_group x₀.property⟩ : L) *
            (⟨(y : Gamma), pti.kernel_le_group y.property⟩ : L)⁻¹ := by
      apply Subtype.ext
      simpa [hcOne] using hconj
    let xW : W := defW.leftEmbedding x₀
    have hxW₂ : (x₀ : Gamma) ∉ W₂ := by
      intro hmem
      have hmem' : (((defW.mulEquiv (x₀, 1) : W) : Gamma)) ∈ W₂ := by
        simpa using hmem
      exact hx ((defW.mulEquiv_mem_right_iff (x₀, 1)).mp hmem')
    have hxPrime : xW ∈ primeTISetInW W W₂ :=
      mem_primeTISetInW.mpr hxW₂
    have hvaluej :=
      (pti.primeTICharacterData isoL).restrict_character i j hxPrime
    have hvaluer :=
      (pti.primeTICharacterData isoL).restrict_character i r hxPrime
    have hvaluej' :
        pti.primeTICharacter isoL i j
            ⟨(x₀ : Gamma), pti.complement_le_group x₀.property⟩ =
          (pti.primeTISign isoL j : ℂ) *
            IrreducibleCharacter.cyclicTICharacter defW i j xW := by
      simpa [xW, PrimeTIHypothesis.primeTICharacter,
        PrimeTIHypothesis.primeTIIndex,
        PrimeTIHypothesis.primeTISign] using hvaluej
    have hvaluer' :
        pti.primeTICharacter isoL i r
            ⟨(x₀ : Gamma), pti.complement_le_group x₀.property⟩ =
          (pti.primeTISign isoL r : ℂ) *
            IrreducibleCharacter.cyclicTICharacter defW i r xW := by
      simpa [xW, PrimeTIHypothesis.primeTICharacter,
        PrimeTIHypothesis.primeTIIndex,
        PrimeTIHypothesis.primeTISign] using hvaluer
    have hsign := pd.prDade_TIsign_eq isoL i j r hdegree
    have hvalues :
        pti.primeTICharacter isoL i j
            ⟨(x₀ : Gamma), pti.complement_le_group x₀.property⟩ =
          pti.primeTICharacter isoL i r
            ⟨(x₀ : Gamma), pti.complement_le_group x₀.property⟩ := by
      calc
        _ = (pti.primeTISign isoL j : ℂ) *
            IrreducibleCharacter.cyclicTICharacter defW i j xW := by
          exact hvaluej'
        _ = (pti.primeTISign isoL r : ℂ) *
            IrreducibleCharacter.cyclicTICharacter defW i r xW := by
          rw [hsign]
          simp [xW,
            IrreducibleCharacter.cyclicTICharacter_leftEmbedding]
        _ = _ := by
          exact hvaluer'.symm
    rw [hconjL,
      ClassFunction.conj_apply
        (pti.primeTICharacter isoL i j)
        ⟨(y : Gamma), pti.kernel_le_group y.property⟩
        ⟨(x₀ : Gamma), pti.complement_le_group x₀.property⟩,
      ClassFunction.conj_apply
        (pti.primeTICharacter isoL i r)
        ⟨(y : Gamma), pti.kernel_le_group y.property⟩
        ⟨(x₀ : Gamma), pti.complement_le_group x₀.property⟩]
    exact hvalues

/-- Peterfalvi 4.8, last part: Dade sends an equal-degree row difference to
the correspondingly signed difference in the ambient cyclic-TI isometry. -/
theorem prDade_sub_TIirr
    (isoL : CyclicTIIsometryData (k := ℂ)
      pd.prDade_prTI.prime_cycTIhyp)
    (isoG : CyclicTIIsometryData (k := ℂ) pd.prDade_cycTI)
    (i : IrreducibleCharacter W₁ ℂ)
    (j r : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial)
    (hr : r ≠ IrreducibleCharacter.trivial)
    (hdegree :
      pd.prDade_prTI.primeTICharacter isoL i j 1 =
        pd.prDade_prTI.primeTICharacter isoL i r 1) :
    Dade pd.prDade_hyp
        (pd.prDade_prTI.primeTICharacter isoL i j -
          pd.prDade_prTI.primeTICharacter isoL i r) =
      (pd.prDade_prTI.primeTISign isoL j : ℂ) •
        (isoG.cyclicTIImage (i, j) - isoG.cyclicTIImage (i, r)) := by
  let pti := pd.prDade_prTI
  by_cases hjr : j = r
  · subst r
    simp
  · let alpha : VirtualCharacter L ℂ :=
      Finsupp.single (pti.primeTIIndex isoL (i, j)) 1 -
        Finsupp.single (pti.primeTIIndex isoL (i, r)) 1
    have hrealizeAlpha :
        VirtualCharacter.realize alpha =
          pti.primeTICharacter isoL i j -
            pti.primeTICharacter isoL i r := by
      simp [alpha, PrimeTIHypothesis.primeTICharacter]
    have halpha : VirtualCharacter.realize alpha ∈
        ClassFunction.supportedOn {x : L | (x : Gamma) ∈ A₀} := by
      rw [hrealizeAlpha]
      exact pd.prDade_sub_TIirr_on isoL i j r hj hr hdegree
    obtain ⟨beta, hDadeBeta, hbetaSupport⟩ :=
      (Dade_Zisometry pd.prDade_hyp).2 alpha halpha
    have hindex :
        pti.primeTIIndex isoL (i, j) ≠
          pti.primeTIIndex isoL (i, r) := by
      intro hidx
      have hp := (pti.primeTIirr_spec isoL).1 hidx
      exact hjr (congrArg Prod.snd hp)
    have hnormAlpha : normSq alpha = 2 := by
      simp [alpha, normSq, sub_eq_add_neg, coeffDot_add_left,
        coeffDot_add_right, coeffDot_neg_left, coeffDot_neg_right,
        hindex, hindex.symm]
    have hstar :=
      (Dade_Zisometry pd.prDade_hyp).1 alpha alpha halpha halpha
    rw [hDadeBeta,
      starCharacterPairing_realize_eq_characterPairing beta beta,
      starCharacterPairing_realize_eq_characterPairing alpha alpha,
      VirtualCharacter.characterPairing_realize,
      VirtualCharacter.characterPairing_realize] at hstar
    change ((normSq beta : ℤ) : ℂ) =
      ((normSq alpha : ℤ) : ℂ) at hstar
    rw [hnormAlpha] at hstar
    have hnormBeta : normSq beta = 2 := by
      exact Int.cast_injective hstar
    have heq : Set.EqOn
        (fun w : W ↦ VirtualCharacter.realize beta
          ⟨w, pd.prDade_cycTI.le_group w.property⟩)
        (fun w : W ↦
          ((pti.primeTISign isoL j : ℂ) •
            (isoG.cyclicTIImage (i, j) -
              isoG.cyclicTIImage (i, r)))
            ⟨w, pd.prDade_cycTI.le_group w.property⟩)
        (cyclicTISetInW W W₁ W₂) := by
      intro w hw
      let wG : G := ⟨w, pd.prDade_cycTI.le_group w.property⟩
      let wL : L := ⟨w, pti.directProduct_le_group w.property⟩
      have hwAmbient : (w : Gamma) ∈ cyclicTISet W W₁ W₂ := hw
      have hwClass : (w : Gamma) ∈
          classSupportWithin L (cyclicTISet W W₁ W₂) := by
        refine ⟨(w : Gamma), hwAmbient, ?_⟩
        exact ⟨1, L.one_mem, by simp⟩
      have hwA₀ : (w : Gamma) ∈ A₀ := by
        rw [pd.prDade_def.dadeSet_eq]
        exact Or.inr hwClass
      have hbetaEval := congrArg
        (fun f : ClassFunction G ℂ ↦ f wG) hDadeBeta
      have hDadeEval := Dade_id pd.prDade_hyp
        (VirtualCharacter.realize alpha) hwA₀
      have hsource :
          VirtualCharacter.realize beta wG =
            pti.primeTICharacter isoL i j wL -
              pti.primeTICharacter isoL i r wL := by
        calc
          VirtualCharacter.realize beta wG =
              Dade pd.prDade_hyp (VirtualCharacter.realize alpha) wG :=
            hbetaEval.symm
          _ = VirtualCharacter.realize alpha wL := by
            simpa [wG, wL] using hDadeEval
          _ = pti.primeTICharacter isoL i j wL -
              pti.primeTICharacter isoL i r wL := by
            simpa [wL] using congrArg
              (fun f : ClassFunction L ℂ ↦ f wL) hrealizeAlpha
      have hwPrime : w ∈ primeTISetInW W W₂ :=
        pti.cyclicTISetInW_subset_primeTISetInW hw
      have hLj :=
        (pti.primeTICharacterData isoL).restrict_character i j hwPrime
      have hLr :=
        (pti.primeTICharacterData isoL).restrict_character i r hwPrime
      have hLj' :
          pti.primeTICharacter isoL i j wL =
            (pti.primeTISign isoL j : ℂ) *
              IrreducibleCharacter.cyclicTICharacter defW i j w := by
        simpa [wL, PrimeTIHypothesis.primeTICharacter,
          PrimeTIHypothesis.primeTIIndex,
          PrimeTIHypothesis.primeTISign] using hLj
      have hLr' :
          pti.primeTICharacter isoL i r wL =
            (pti.primeTISign isoL r : ℂ) *
              IrreducibleCharacter.cyclicTICharacter defW i r w := by
        simpa [wL, PrimeTIHypothesis.primeTICharacter,
          PrimeTIHypothesis.primeTIIndex,
          PrimeTIHypothesis.primeTISign] using hLr
      have hGj : isoG.cyclicTIImage (i, j) wG =
          IrreducibleCharacter.cyclicTICharacter defW i j w := by
        simpa [wG, CyclicTIIsometryData.cyclicTIImage,
          CyclicTIIsometryData.cyclicTISourceIrreducible] using
          isoG.restrict
            (IrreducibleCharacter.cyclicTICharacter defW i j :
              ClassFunction W ℂ) hw
      have hGr : isoG.cyclicTIImage (i, r) wG =
          IrreducibleCharacter.cyclicTICharacter defW i r w := by
        simpa [wG, CyclicTIIsometryData.cyclicTIImage,
          CyclicTIIsometryData.cyclicTISourceIrreducible] using
          isoG.restrict
            (IrreducibleCharacter.cyclicTICharacter defW i r :
              ClassFunction W ℂ) hw
      have hsign := pd.prDade_TIsign_eq isoL i j r hdegree
      simp only [ClassFunction.smul_apply, ClassFunction.sub_apply,
        smul_eq_mul]
      rw [hsource, hLj', hLr', hsign, hGj, hGr]
      ring
    have hbetaEq := isoG.eq_signed_sub_cTIiso beta
      (pti.primeTISign isoL j)
      (pti.primeTISign_isSign isoL j) i j r hnormBeta hjr heq
    rw [hrealizeAlpha] at hDadeBeta
    exact hDadeBeta.trans hbetaEq

include pd

/-- The cyclic-TI set is disjoint from the prime-TI kernel. -/
theorem prDade_supp_disjoint :
    cyclicTISet W W₁ W₂ ⊆ (K : Set Gamma)ᶜ :=
  cyclicTISet_subset_kernel_compl pd.prDade_prTI

/-- Peterfalvi 4.9.  The uniform family of reduced prime-TI columns is
orthogonal, inverse-stable and coherent with the Dade isometry. -/
theorem uniform_prTIred_coherent
    (isoL : CyclicTIIsometryData (k := ℂ)
      pd.prDade_prTI.prime_cycTIhyp)
    (isoG : CyclicTIIsometryData (k := ℂ) pd.prDade_cycTI)
    (j₀ : IrreducibleCharacter W₂ ℂ)
    (hj₀ : j₀ ≠ IrreducibleCharacter.trivial) :
    let T := pd.prDade_prTI.uniform_prTIred_seq isoL j₀
    ((0 : ClassFunction L ℂ) ∉ T ∧
      T.Pairwise (fun phi psi ↦ characterPairing phi psi = 0) ∧
      (∀ phi ∈ T, ClassFunction.inverseLinear phi ≠ phi) ∧
      (∀ phi ∈ T, ClassFunction.inverseLinear phi ∈ T) ∧
      (∀ phi ∈ AddSubgroup.closure T,
        (phi ∈ ClassFunction.supportedOn {x : L | x ≠ 1} ↔
          phi ∈ ClassFunction.supportedOn
            {x : L | (x : Gamma) ∈ A})) ∧
      (∃ phi, phi ≠ 0 ∧ phi ∈ AddSubgroup.closure T ∧
        phi ∈ ClassFunction.supportedOn
          {x : L | (x : Gamma) ∈ A})) ∧
    ∃ tau₁ : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ,
      (∀ j, tau₁ (pd.prDade_prTI.primeTIRed isoL j) =
        (pd.prDade_prTI.primeTISign isoL j₀ : ℂ) •
          ∑ i : IrreducibleCharacter W₁ ℂ,
            isoG.cyclicTIImage (i, j)) ∧
      (∀ phi ∈ AddSubgroup.closure T,
        ∀ psi ∈ AddSubgroup.closure T,
          characterPairing (tau₁ phi) (tau₁ psi) =
            characterPairing phi psi) ∧
      (∀ phi ∈ AddSubgroup.closure T,
        phi ∈ ClassFunction.supportedOn {x : L | x ≠ 1} →
          tau₁ phi = Dade pd.prDade_hyp phi) := by
  let pti := pd.prDade_prTI
  let T := pti.uniform_prTIred_seq isoL j₀
  change
    ((0 : ClassFunction L ℂ) ∉ T ∧
      T.Pairwise (fun phi psi ↦ characterPairing phi psi = 0) ∧
      (∀ phi ∈ T, ClassFunction.inverseLinear phi ≠ phi) ∧
      (∀ phi ∈ T, ClassFunction.inverseLinear phi ∈ T) ∧
      (∀ phi ∈ AddSubgroup.closure T,
        (phi ∈ ClassFunction.supportedOn {x : L | x ≠ 1} ↔
          phi ∈ ClassFunction.supportedOn
            {x : L | (x : Gamma) ∈ A})) ∧
      (∃ phi, phi ≠ 0 ∧ phi ∈ AddSubgroup.closure T ∧
        phi ∈ ClassFunction.supportedOn
          {x : L | (x : Gamma) ∈ A})) ∧
    ∃ tau₁ : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ,
      (∀ j, tau₁ (pti.primeTIRed isoL j) =
        (pti.primeTISign isoL j₀ : ℂ) •
          ∑ i : IrreducibleCharacter W₁ ℂ,
            isoG.cyclicTIImage (i, j)) ∧
      (∀ phi ∈ AddSubgroup.closure T,
        ∀ psi ∈ AddSubgroup.closure T,
          characterPairing (tau₁ phi) (tau₁ psi) =
            characterPairing phi psi) ∧
      (∀ phi ∈ AddSubgroup.closure T,
        phi ∈ ClassFunction.supportedOn {x : L | x ≠ 1} →
          tau₁ phi = Dade pd.prDade_hyp phi)
  have hzero : (0 : ClassFunction L ℂ) ∉ T := by
    rintro ⟨j, hj, heq⟩
    exact pti.prTIred_neq0 isoL j heq
  have hpairwise :
      T.Pairwise (fun phi psi ↦ characterPairing phi psi = 0) := by
    intro phi hphi psi hpsi hne
    rcases hphi with ⟨j, hj, rfl⟩
    rcases hpsi with ⟨r, hr, rfl⟩
    have hjr : j ≠ r := by
      intro hjr
      subst r
      exact hne rfl
    rw [pti.cfdot_prTIred isoL, if_neg hjr]
  have hnotFixed :
      ∀ phi ∈ T, ClassFunction.inverseLinear phi ≠ phi := by
    rintro phi ⟨j, hj, rfl⟩
    exact pti.prTIred_not_real isoL hj.1
  have hinverseClosed :
      ∀ phi ∈ T, ClassFunction.inverseLinear phi ∈ T := by
    rintro phi ⟨j, hj, rfl⟩
    have hdualNe : IrreducibleCharacter.dual j ≠
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) := by
      intro hdual
      apply hj.1
      calc
        j = IrreducibleCharacter.dual (IrreducibleCharacter.dual j) :=
          (IrreducibleCharacter.dual_dual j).symm
        _ = IrreducibleCharacter.dual
            (IrreducibleCharacter.trivial :
              IrreducibleCharacter W₂ ℂ) :=
          congrArg IrreducibleCharacter.dual hdual
        _ = IrreducibleCharacter.trivial :=
          IrreducibleCharacter.dual_trivial
    have hdualDegree :
        pti.primeTIRed isoL (IrreducibleCharacter.dual j) 1 =
          pti.primeTIRed isoL j₀ 1 := by
      calc
        _ = ClassFunction.inverseLinear (pti.primeTIRed isoL j) 1 :=
          congrArg (fun f : ClassFunction L ℂ ↦ f 1)
            (pti.prTIred_aut isoL j).symm
        _ = pti.primeTIRed isoL j 1 := by simp
        _ = _ := hj.2
    rw [pti.prTIred_aut isoL j]
    exact ⟨IrreducibleCharacter.dual j,
      ⟨hdualNe, hdualDegree⟩, rfl⟩
  have hspanPrimeDade :
      ∀ {phi}, phi ∈ AddSubgroup.closure T →
        phi ∈ ClassFunction.supportedOn (primeDadeSupport L A) := by
    intro phi hphi
    induction hphi using AddSubgroup.closure_induction with
    | mem phi hphi =>
        rcases hphi with ⟨j, hj, rfl⟩
        exact pd.prDade_TIred_on isoL j hj.1
    | zero =>
        exact (ClassFunction.supportedOn (R := ℂ)
          (primeDadeSupport L A)).zero_mem
    | add phi psi hphi hpsi ihphi ihpsi =>
        exact (ClassFunction.supportedOn (R := ℂ)
          (primeDadeSupport L A)).add_mem ihphi ihpsi
    | neg phi hphi ihphi =>
        exact (ClassFunction.supportedOn (R := ℂ)
          (primeDadeSupport L A)).neg_mem ihphi
  have hAOne : (1 : Gamma) ∉ A := by
    intro hone
    exact (pd.prDade_def.set_le_kernel_diff_one hone).2 (by simp)
  have hsupport : ∀ phi ∈ AddSubgroup.closure T,
      (phi ∈ ClassFunction.supportedOn {x : L | x ≠ 1} ↔
        phi ∈ ClassFunction.supportedOn
          {x : L | (x : Gamma) ∈ A}) := by
    intro phi hphi
    constructor
    · intro hoff
      have hbig := hspanPrimeDade hphi
      apply ClassFunction.mem_supportedOn_iff.mpr
      intro x hxA
      have hxA' : (x : Gamma) ∉ A := by simpa using hxA
      by_cases hx1 : (x : Gamma) = 1
      · have hxeq : x = 1 := by
          apply Subtype.ext
          simpa using hx1
        subst x
        exact ClassFunction.eq_zero_of_mem_supportedOn hoff (by simp)
      · apply ClassFunction.eq_zero_of_mem_supportedOn hbig
        simp only [primeDadeSupport, Set.mem_setOf_eq, not_or]
        exact ⟨hx1, hxA'⟩
    · intro hA
      apply ClassFunction.mem_supportedOn_iff.mpr
      intro x hx
      have hxeq : x = 1 := by
        simpa only [Set.mem_setOf_eq, not_ne_iff] using hx
      subst x
      apply ClassFunction.eq_zero_of_mem_supportedOn hA
      simpa using hAOne
  let mu₀ := pti.primeTIRed isoL j₀
  have hmu₀T : mu₀ ∈ T :=
    ⟨j₀, ⟨hj₀, rfl⟩, rfl⟩
  have hinvMu₀T : ClassFunction.inverseLinear mu₀ ∈ T :=
    hinverseClosed mu₀ hmu₀T
  have hdiffSpan : ClassFunction.inverseLinear mu₀ - mu₀ ∈
      AddSubgroup.closure T :=
    (AddSubgroup.closure T).sub_mem
      (AddSubgroup.subset_closure hinvMu₀T)
      (AddSubgroup.subset_closure hmu₀T)
  have hdiffNe : ClassFunction.inverseLinear mu₀ - mu₀ ≠ 0 := by
    apply sub_ne_zero.mpr
    dsimp only [mu₀]
    exact pti.prTIred_not_real isoL hj₀
  have hdiffOff : ClassFunction.inverseLinear mu₀ - mu₀ ∈
      ClassFunction.supportedOn {x : L | x ≠ 1} := by
    apply ClassFunction.mem_supportedOn_iff.mpr
    intro x hx
    have hxeq : x = 1 := by
      simpa only [Set.mem_setOf_eq, not_ne_iff] using hx
    subst x
    simp [mu₀]
  have hdiffA : ClassFunction.inverseLinear mu₀ - mu₀ ∈
      ClassFunction.supportedOn {x : L | (x : Gamma) ∈ A} :=
    (hsupport _ hdiffSpan).mp hdiffOff
  have hexists : ∃ phi, phi ≠ 0 ∧ phi ∈ AddSubgroup.closure T ∧
      phi ∈ ClassFunction.supportedOn
        {x : L | (x : Gamma) ∈ A} :=
    ⟨ClassFunction.inverseLinear mu₀ - mu₀,
      hdiffNe, hdiffSpan, hdiffA⟩
  have hTRange : T ⊆ Set.range (pti.primeTIRed isoL) := by
    rintro phi ⟨j, hj, rfl⟩
    exact ⟨j, rfl⟩
  have hDadeDiff (j : IrreducibleCharacter W₂ ℂ)
      (hj : j ≠ IrreducibleCharacter.trivial)
      (hdegree : pti.primeTIRed isoL j 1 =
        pti.primeTIRed isoL j₀ 1) :
      Dade pd.prDade_hyp
          (pti.primeTIRed isoL j - pti.primeTIRed isoL j₀) =
        primeTIRedCoherentTarget pti isoL isoG j₀ j -
          primeTIRedCoherentTarget pti isoL isoG j₀ j₀ := by
    have hentry (i : IrreducibleCharacter W₁ ℂ) :
        pti.primeTICharacter isoL i j 1 =
          pti.primeTICharacter isoL i j₀ 1 := by
      rw [pti.prTIirr_1 isoL i j, pti.prTIirr_1 isoL i j₀]
      apply mul_left_cancel₀
        (Nat.cast_ne_zero.mpr
          (Nat.card_pos.ne' : Nat.card W₁ ≠ 0))
      rw [← pti.prTIred_1 isoL j, ← pti.prTIred_1 isoL j₀]
      exact hdegree
    calc
      Dade pd.prDade_hyp
          (pti.primeTIRed isoL j - pti.primeTIRed isoL j₀) =
          ∑ i : IrreducibleCharacter W₁ ℂ,
            Dade pd.prDade_hyp
              (pti.primeTICharacter isoL i j -
                pti.primeTICharacter isoL i j₀) := by
            rw [pti.primeTIRed_eq_sum, pti.primeTIRed_eq_sum,
              ← Finset.sum_sub_distrib, map_sum]
      _ = ∑ i : IrreducibleCharacter W₁ ℂ,
          (pti.primeTISign isoL j : ℂ) •
            (isoG.cyclicTIImage (i, j) -
              isoG.cyclicTIImage (i, j₀)) := by
            apply Finset.sum_congr rfl
            intro i _
            exact pd.prDade_sub_TIirr isoL isoG i j j₀
              hj hj₀ (hentry i)
      _ = ∑ i : IrreducibleCharacter W₁ ℂ,
          (pti.primeTISign isoL j₀ : ℂ) •
            (isoG.cyclicTIImage (i, j) -
              isoG.cyclicTIImage (i, j₀)) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [pd.prDade_TIsign_eq isoL i j j₀ (hentry i)]
      _ = primeTIRedCoherentTarget pti isoL isoG j₀ j -
          primeTIRedCoherentTarget pti isoL isoG j₀ j₀ := by
            rw [show (∑ i,
                  (pti.primeTISign isoL j₀ : ℂ) •
                    (isoG.cyclicTIImage (i, j) -
                      isoG.cyclicTIImage (i, j₀))) =
                (pti.primeTISign isoL j₀ : ℂ) •
                  ∑ i, (isoG.cyclicTIImage (i, j) -
                    isoG.cyclicTIImage (i, j₀)) by
              rw [Finset.smul_sum]]
            rw [Finset.sum_sub_distrib, smul_sub]
            rfl
  have hMapDiff (j : IrreducibleCharacter W₂ ℂ)
      (hj : j ≠ IrreducibleCharacter.trivial)
      (hdegree : pti.primeTIRed isoL j 1 =
        pti.primeTIRed isoL j₀ 1) :
      primeTIRedCoherentMap pti isoL isoG j₀
          (pti.primeTIRed isoL j - pti.primeTIRed isoL j₀) =
        Dade pd.prDade_hyp
          (pti.primeTIRed isoL j - pti.primeTIRed isoL j₀) := by
    calc
      _ = primeTIRedCoherentTarget pti isoL isoG j₀ j -
          primeTIRedCoherentTarget pti isoL isoG j₀ j₀ := by
            rw [map_sub, primeTIRedCoherentMap_primeTIRed,
              primeTIRedCoherentMap_primeTIRed]
      _ = _ := (hDadeDiff j hj hdegree).symm
  refine ⟨⟨hzero, hpairwise, hnotFixed, hinverseClosed,
    hsupport, hexists⟩, ?_⟩
  refine ⟨primeTIRedCoherentMap pti isoL isoG j₀, ?_, ?_, ?_⟩
  · intro j
    exact primeTIRedCoherentMap_primeTIRed pti isoL isoG j₀ j
  · intro phi hphi psi hpsi
    exact primeTIRedCoherentMap_isometry_on_span
      pti isoL isoG j₀ T hTRange hphi hpsi
  · intro phi hphi hphiOff
    let J := {j : IrreducibleCharacter W₂ ℂ //
      j ≠ IrreducibleCharacter.trivial ∧
        pti.primeTIRed isoL j 1 = pti.primeTIRed isoL j₀ 1}
    let m : J → ClassFunction L ℂ :=
      fun j ↦ pti.primeTIRed isoL j.1
    have hT_eq : T = Set.range m := by
      ext theta
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨⟨j, hj⟩, rfl⟩
      · rintro ⟨j, rfl⟩
        exact ⟨j.1, j.property, rfl⟩
    have hphiRange : phi ∈ AddSubgroup.closure (Set.range m) := by
      rw [← hT_eq]
      exact hphi
    obtain ⟨z, hz⟩ :=
      AddSubgroup.exists_finsupp_of_mem_closure_range m phi hphiRange
    have hmDegree (j : J) :
        m j 1 = pti.primeTIRed isoL j₀ 1 :=
      j.property.2
    have hphi1 : phi 1 = 0 :=
      ClassFunction.eq_zero_of_mem_supportedOn hphiOff (by simp)
    have hcoeffMul :
        ((z.sum (fun _ n ↦ n) : ℤ) : ℂ) *
            pti.primeTIRed isoL j₀ 1 = 0 := by
      rw [← finsupp_sum_zsmul_apply_one z m
        (pti.primeTIRed isoL j₀ 1) hmDegree, ← hz]
      exact hphi1
    have hcoeffCast : ((z.sum (fun _ n ↦ n) : ℤ) : ℂ) = 0 :=
      (mul_eq_zero.mp hcoeffMul).resolve_right
        (pti.prTIred_1_neq0 isoL j₀)
    have hcoeff : (z.sum (fun _ n ↦ n) : ℤ) = 0 := by
      apply Int.cast_injective (α := ℂ)
      simpa only [Int.cast_zero] using hcoeffCast
    have hphiDiff :
        phi = z.sum (fun j n ↦ n •
          (m j - pti.primeTIRed isoL j₀)) := by
      rw [finsupp_sum_zsmul_sub, hcoeff, zero_smul, sub_zero]
      exact hz
    have map_zsum
        (F : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
        (q : J →₀ ℤ) (f : J → ClassFunction L ℂ) :
        F (q.sum (fun j n ↦ n • f j)) =
          q.sum (fun j n ↦ n • F (f j)) := by
      classical
      simp only [Finsupp.sum, map_sum, map_zsmul]
    calc
      primeTIRedCoherentMap pti isoL isoG j₀ phi =
          primeTIRedCoherentMap pti isoL isoG j₀
            (z.sum (fun j n ↦ n •
              (m j - pti.primeTIRed isoL j₀))) :=
        congrArg _ hphiDiff
      _ = z.sum (fun j n ↦ n •
          primeTIRedCoherentMap pti isoL isoG j₀
            (m j - pti.primeTIRed isoL j₀)) :=
        map_zsum _ z _
      _ = z.sum (fun j n ↦ n •
          Dade pd.prDade_hyp
            (m j - pti.primeTIRed isoL j₀)) := by
        apply Finsupp.sum_congr
        intro j _
        rw [show m j = pti.primeTIRed isoL j.1 by rfl,
          hMapDiff j.1 j.property.1 j.property.2]
      _ = Dade pd.prDade_hyp
          (z.sum (fun j n ↦ n •
            (m j - pti.primeTIRed isoL j₀))) :=
        (map_zsum (Dade pd.prDade_hyp) z _).symm
      _ = Dade pd.prDade_hyp phi :=
        congrArg _ hphiDiff.symm

end PrimeDadeHypothesis

end

end Submission.OddOrder.PF
