import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.RootsOfUnity.Complex
import Submission.OddOrder.MathlibSupport.CharacterValueCyclotomic
import Submission.OddOrder.PF.Section05.CoherenceBasics
import Submission.OddOrder.PF.Section05.SeqIndGlobal
import Submission.OddOrder.PF.Section04.PrimeTIDadeCoherence
import Submission.OddOrder.PF.Section04.VirtualCharacterPairs
import Submission.OddOrder.PF.Section03.CyclicTISmallSupport

/-!
# Construction of subcoherent families

This file ports Peterfalvi 5.3(a,b), the two constructions between the
definition of subcoherence and its elementary consequences.  The first
construction splits the image of every non-real irreducible difference into
an orthonormal pair.  The second applies it to the irreducible part of a
prime-Dade kernel layer and inserts the explicit reduced-column pairs.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical Pointwise
open Submission.OddOrder.MathlibSupport

universe u

-- The prime-Dade construction follows the universe-0 ambient specialization
-- of `uniform_prTIred_coherent`; the preliminary 5.3(a) construction below
-- remains universe-polymorphic in its two abstract group types.
variable {Gamma : Type} [Group Gamma] [Fintype Gamma]
  {G L K H W W₁ W₂ : Subgroup Gamma}
  {A A₀ : Set Gamma}
  {defW : IsInternalDirectProductIn W₁ W₂ W}

attribute [local instance] subgroupCoeTCToAmbient
  subgroupOfCoeTCToAmbient

local instance subcoherentConstructionInvertibleCard
    {Q : Type u} [Group Q] [Fintype Q] :
    Invertible (Nat.card Q : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

private theorem characterPairing_neg_left'
    {Q : Type u} [Group Q] [Fintype Q]
    (phi psi : ClassFunction Q ℂ) :
    characterPairing (-phi) psi = -characterPairing phi psi := by
  calc
    characterPairing (-phi) psi =
        characterPairing ((-1 : ℂ) • phi) psi := by
      rw [neg_one_smul ℂ phi]
    _ = (-1 : ℂ) * characterPairing phi psi :=
      characterPairing_smul_left (-1 : ℂ) phi psi
    _ = -characterPairing phi psi := neg_one_mul _

private theorem characterPairing_neg_right'
    {Q : Type u} [Group Q] [Fintype Q]
    (phi psi : ClassFunction Q ℂ) :
    characterPairing phi (-psi) = -characterPairing phi psi := by
  calc
    characterPairing phi (-psi) =
        characterPairing phi ((-1 : ℂ) • psi) := by
      rw [neg_one_smul ℂ psi]
    _ = (-1 : ℂ) * characterPairing phi psi :=
      characterPairing_smul_right (-1 : ℂ) phi psi
    _ = -characterPairing phi psi := neg_one_mul _

private theorem characterPairing_sub_left'
    {Q : Type u} [Group Q] [Fintype Q]
    (phi psi theta : ClassFunction Q ℂ) :
    characterPairing (phi - psi) theta =
      characterPairing phi theta - characterPairing psi theta := by
  rw [sub_eq_add_neg, characterPairing_add_left,
    characterPairing_neg_left', sub_eq_add_neg]

private theorem characterPairing_sub_right'
    {Q : Type u} [Group Q] [Fintype Q]
    (phi psi theta : ClassFunction Q ℂ) :
    characterPairing phi (psi - theta) =
      characterPairing phi psi - characterPairing phi theta := by
  rw [sub_eq_add_neg, characterPairing_add_right,
    characterPairing_neg_right', sub_eq_add_neg]

private theorem inverseLinear_involutive'
    {Q : Type u} [Group Q] (phi : ClassFunction Q ℂ) :
    ClassFunction.inverseLinear (ClassFunction.inverseLinear phi) = phi := by
  ext x
  simp

private theorem characterPairing_inverseLinear'
    {Q : Type u} [Group Q] [Fintype Q]
    (phi psi : ClassFunction Q ℂ) :
    characterPairing (ClassFunction.inverseLinear phi)
        (ClassFunction.inverseLinear psi) = characterPairing phi psi := by
  unfold characterPairing
  congr 1
  refine Fintype.sum_equiv (Equiv.inv Q) _ _ fun x ↦ ?_
  simp only [Equiv.inv_apply, ClassFunction.inverseLinear_apply, inv_inv]

private theorem characterPairing_inverseLinear_left'
    {Q : Type u} [Group Q] [Fintype Q]
    (phi psi : ClassFunction Q ℂ) :
    characterPairing (ClassFunction.inverseLinear phi) psi =
      characterPairing phi (ClassFunction.inverseLinear psi) := by
  calc
    characterPairing (ClassFunction.inverseLinear phi) psi =
        characterPairing (ClassFunction.inverseLinear phi)
          (ClassFunction.inverseLinear
            (ClassFunction.inverseLinear psi)) := by
          rw [inverseLinear_involutive']
    _ = characterPairing phi (ClassFunction.inverseLinear psi) :=
      characterPairing_inverseLinear' phi
        (ClassFunction.inverseLinear psi)

private theorem inverse_sub_supported'
    {Q : Type u} [Group Q] (phi : ClassFunction Q ℂ) :
    phi - ClassFunction.inverseLinear phi ∈
      ClassFunction.supportedOn (nonidentitySet Q) := by
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hx
  have hxone : x = 1 := by
    simpa [nonidentitySet] using not_not.mp hx
  subst x
  simp

private theorem irreducibleCharacter_apply_one_ne_zero'
    {Q : Type u} [Group Q] [Fintype Q]
    (chi : IrreducibleCharacter Q ℂ) : chi 1 ≠ 0 := by
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Nontrivial chi.representation := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    apply CategoryTheory.id_nonzero chi.representation
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro x
    exact Subsingleton.elim _ _
  rw [← chi.representation_character, FDRep.char_one]
  exact Nat.cast_ne_zero.mpr Module.finrank_pos.ne'

private theorem isSign_mul_self' {a : ℤ} (ha : IsSign a) :
    a * a = 1 := by
  rcases ha with rfl | rfl <;> norm_num

private theorem irreducible_isOrdinaryCharacter
    {Q : Type u} [Group Q] [Fintype Q]
    (chi : IrreducibleCharacter Q ℂ) :
    ClassFunction.IsOrdinaryCharacter (chi : ClassFunction Q ℂ) := by
  refine ⟨Finsupp.single chi 1, ?_, by simp⟩
  intro psi
  by_cases hpsi : psi = chi
  · subst psi
    simp
  · simp [hpsi]

private theorem virtualCharacter_ofFDRep_isOrdinary
    {Q : Type} [Group Q] [Fintype Q]
    (V : FDRep ℂ Q) :
    (VirtualCharacter.ofFDRep V).IsOrdinary := by
  intro chi
  change 0 ≤ (chi.multiplicity V : ℤ)
  exact Int.natCast_nonneg _

/-- Finite-order trace identity used to compare the star and inverse-value
pairings over `ℂ`. -/
private theorem representation_character_inv_eq_star'
    {Q : Type u} {V : Type*} [Group Q] [Fintype Q]
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

private theorem irreducibleCharacter_apply_inv_eq_star'
    {Q : Type u} [Group Q] [Fintype Q]
    (chi : IrreducibleCharacter Q ℂ) (x : Q) :
    chi x⁻¹ = star (chi x) := by
  rw [← chi.representation_character,
    ← chi.representation_character]
  exact representation_character_inv_eq_star'
    chi.representation.ρ x

private theorem star_realize_apply_eq_inverse'
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
      change (starRingEnd ℂ) ((n : ℂ) * chi.val x +
          VirtualCharacter.realize z x) =
        (n : ℂ) * chi.val x⁻¹ +
          VirtualCharacter.realize z x⁻¹
      have hchiStar :=
        (irreducibleCharacter_apply_inv_eq_star' chi x).symm
      change (starRingEnd ℂ) (chi.val x) = chi.val x⁻¹ at hchiStar
      have ih' := ih
      change (starRingEnd ℂ) (VirtualCharacter.realize z x) =
        VirtualCharacter.realize z x⁻¹ at ih'
      rw [map_add, map_mul, map_intCast, ih', hchiStar]

private theorem starCharacterPairing_realize_eq_characterPairing'
    {Q : Type u} [Group Q] [Fintype Q]
    (z w : VirtualCharacter Q ℂ) :
    starCharacterPairing (VirtualCharacter.realize z)
        (VirtualCharacter.realize w) =
      characterPairing (VirtualCharacter.realize z)
        (VirtualCharacter.realize w) := by
  apply starCharacterPairing_eq_characterPairing_of_star_apply_eq_inv
  exact star_realize_apply_eq_inverse' w

private theorem characterPairing_realize_self_of_normSq_one'
    {Q : Type u} [Group Q] [Fintype Q]
    (z : VirtualCharacter Q ℂ) (hz : normSq z = 1) :
    characterPairing (VirtualCharacter.realize z)
        (VirtualCharacter.realize z) = 1 := by
  rw [VirtualCharacter.characterPairing_realize]
  change (normSq z : ℂ) = 1
  rw [hz]
  norm_num

private structure OrthonormalDifference
    (Q : Type u) [Group Q] where
  left : VirtualCharacter Q ℂ
  right : VirtualCharacter Q ℂ

namespace OrthonormalDifference

private def targetFinset
    {Q : Type u} [Group Q] (p : OrthonormalDifference Q) :
    Finset (ClassFunction Q ℂ) :=
  {VirtualCharacter.realize p.left, -VirtualCharacter.realize p.right}

end OrthonormalDifference

/-- Peterfalvi 5.3(a).  An integral isometry on a dual-closed family of
non-real irreducibles canonically supplies the two-element data required for
subcoherence.  The three final assumptions are the expanded Lean form of the
source assertion that the map is an integral isometry into virtual
characters supported away from the identity. -/
theorem irr_subcoherent
    {L₀ G₀ : Type u} [Group L₀] [Fintype L₀]
    [Group G₀] [Fintype G₀]
    (S : Set (ClassFunction L₀ ℂ))
    (tau : ClassFunction L₀ ℂ →ₗ[ℂ] ClassFunction G₀ ℂ)
    (hS : cfConjC_subset S
      (Set.range fun chi : IrreducibleCharacter L₀ ℂ ↦
        (chi : ClassFunction L₀ ℂ)))
    (hnr : ∀ phi ∈ S, ClassFunction.inverseLinear phi ≠ phi)
    (hiso : ∀ phi ∈ AddSubgroup.closure S,
      phi ∈ ClassFunction.supportedOn (nonidentitySet L₀) →
      ∀ psi ∈ AddSubgroup.closure S,
        psi ∈ ClassFunction.supportedOn (nonidentitySet L₀) →
        characterPairing (tau phi) (tau psi) =
          characterPairing phi psi)
    (hvirt : ∀ phi ∈ AddSubgroup.closure S,
      phi ∈ ClassFunction.supportedOn (nonidentitySet L₀) →
        ClassFunction.IsVirtual (tau phi))
    (hsupp : ∀ phi ∈ AddSubgroup.closure S,
      phi ∈ ClassFunction.supportedOn (nonidentitySet L₀) →
        tau phi ∈ ClassFunction.supportedOn (nonidentitySet G₀)) :
    ∃ R : ClassFunction L₀ ℂ → Finset (ClassFunction G₀ ℂ),
      subcoherent S tau R := by
  classical
  have hpairExists (x : {phi : ClassFunction L₀ ℂ // phi ∈ S}) :
      ∃ p : OrthonormalDifference G₀,
        IntegralLattice.IsOrthonormalPair p.left p.right ∧
          tau (x.1 - ClassFunction.inverseLinear x.1) =
            VirtualCharacter.realize (p.left - p.right) := by
    let d := x.1 - ClassFunction.inverseLinear x.1
    have hdSpan : d ∈ AddSubgroup.closure S :=
      (AddSubgroup.closure S).sub_mem
        (AddSubgroup.subset_closure x.property)
        (AddSubgroup.subset_closure (hS.2 x.1 x.property))
    have hdOff : d ∈
        ClassFunction.supportedOn (nonidentitySet L₀) :=
      inverse_sub_supported' x.1
    obtain ⟨z, hz⟩ := hvirt d hdSpan hdOff
    obtain ⟨chi, hchi⟩ := hS.1 x.property
    have hinvChi : ClassFunction.inverseLinear x.1 =
        (IrreducibleCharacter.dual chi : ClassFunction L₀ ℂ) := by
      rw [← hchi]
      exact ClassFunction.inverseLinear_irreducible chi
    have hchiNe : chi ≠ IrreducibleCharacter.dual chi := by
      intro heq
      apply hnr x.1 x.property
      calc
        ClassFunction.inverseLinear x.1 =
            (IrreducibleCharacter.dual chi : ClassFunction L₀ ℂ) :=
          hinvChi
        _ = (chi : ClassFunction L₀ ℂ) :=
          congrArg (fun eta : IrreducibleCharacter L₀ ℂ ↦
            (eta : ClassFunction L₀ ℂ)) heq.symm
        _ = x.1 := hchi
    have hnormSource : characterPairing d d = (2 : ℂ) := by
      dsimp only [d]
      rw [characterPairing_sub_left', characterPairing_sub_right',
        characterPairing_sub_right', hinvChi, ← hchi]
      rw [IrreducibleCharacter.characterPairing_self,
        IrreducibleCharacter.characterPairing_self,
        IrreducibleCharacter.characterPairing_eq_zero hchiNe,
        IrreducibleCharacter.characterPairing_eq_zero hchiNe.symm]
      norm_num
    have hnormTarget : characterPairing (tau d) (tau d) = (2 : ℂ) := by
      rw [hiso d hdSpan hdOff d hdSpan hdOff, hnormSource]
    have hnormZ : normSq z = 2 := by
      apply Int.cast_injective (α := ℂ)
      rw [← VirtualCharacter.characterPairing_realize_self, hz,
        hnormTarget]
      norm_num
    obtain ⟨i, j, epsilon, delta, hij, hepsilon, hdelta, hzsum⟩ :=
      eq_sum_signed_singles_of_normSq_eq_two z hnormZ
    let a : VirtualCharacter G₀ ℂ := Finsupp.single i epsilon
    let b : VirtualCharacter G₀ ℂ := -Finsupp.single j delta
    refine ⟨⟨a, b⟩, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · simp [a, normSq, isSign_mul_self' hepsilon]
      · simp [b, normSq, coeffDot_neg_right,
          isSign_mul_self' hdelta]
      · simp [a, b, hij]
    · calc
        tau d = VirtualCharacter.realize z := hz.symm
        _ = VirtualCharacter.realize
            (Finsupp.single i epsilon + Finsupp.single j delta) := by
              rw [hzsum]
        _ = VirtualCharacter.realize (a - b) := by
              congr 1
              simp [a, b]
  choose p hpOrtho hpDiff using hpairExists
  let R : ClassFunction L₀ ℂ → Finset (ClassFunction G₀ ℂ) :=
    fun phi ↦ if hphi : phi ∈ S then
      (p ⟨phi, hphi⟩).targetFinset else ∅
  have hR (phi : ClassFunction L₀ ℂ) (hphi : phi ∈ S) :
      R phi = (p ⟨phi, hphi⟩).targetFinset := by
    simp [R, hphi]
  have hpDiff' (phi : ClassFunction L₀ ℂ) (hphi : phi ∈ S) :
      tau (phi - ClassFunction.inverseLinear phi) =
        VirtualCharacter.realize
          ((p ⟨phi, hphi⟩).left - (p ⟨phi, hphi⟩).right) :=
    hpDiff ⟨phi, hphi⟩
  have hpTargetNe (x : {phi : ClassFunction L₀ ℂ // phi ∈ S}) :
      VirtualCharacter.realize (p x).left ≠
        -VirtualCharacter.realize (p x).right := by
    intro heq
    have hcross : characterPairing
        (VirtualCharacter.realize (p x).left)
        (VirtualCharacter.realize (p x).right) = 0 := by
      rw [VirtualCharacter.characterPairing_realize,
        (hpOrtho x).2.2]
      norm_num
    have hself : characterPairing
        (VirtualCharacter.realize (p x).right)
        (VirtualCharacter.realize (p x).right) = 1 := by
      exact characterPairing_realize_self_of_normSq_one'
        (p x).right (hpOrtho x).2.1
    rw [heq, characterPairing_neg_left', hself] at hcross
    norm_num at hcross
  refine ⟨R, {
    finite := (Set.finite_range fun chi : IrreducibleCharacter L₀ ℂ ↦
      (chi : ClassFunction L₀ ℂ)).subset hS.1
    source_character := ?_
    source_virtual := ?_
    zero_not_mem := ?_
    degree_ne_zero := ?_
    inverse_ne := hnr
    inverse_mem := hS.2
    tau_isometry := hiso
    tau_virtual := hvirt
    tau_supported := hsupp
    pairwise_orthogonal := ?_
    image_virtual := ?_
    image_orthonormal := ?_
    tau_inverse_sub := ?_
    image_orthogonal := ?_ }⟩
  · intro phi hphi
    obtain ⟨chi, rfl⟩ := hS.1 hphi
    exact irreducible_isOrdinaryCharacter chi
  · intro phi hphi
    obtain ⟨chi, rfl⟩ := hS.1 hphi
    exact ⟨Finsupp.single chi 1, by simp⟩
  · intro hzero
    obtain ⟨chi, hchi⟩ := hS.1 hzero
    have hdegree := irreducibleCharacter_apply_one_ne_zero' chi
    apply hdegree
    simpa using congrArg (fun f : ClassFunction L₀ ℂ ↦ f 1) hchi
  · intro phi hphi
    obtain ⟨chi, rfl⟩ := hS.1 hphi
    exact irreducibleCharacter_apply_one_ne_zero' chi
  · intro phi hphi psi hpsi hne
    obtain ⟨chi, rfl⟩ := hS.1 hphi
    obtain ⟨eta, rfl⟩ := hS.1 hpsi
    apply IrreducibleCharacter.characterPairing_eq_zero
    intro hchiEta
    subst eta
    exact hne rfl
  · intro xi hxi alpha halpha
    rw [hR xi hxi, OrthonormalDifference.targetFinset] at halpha
    simp only [Finset.mem_insert, Finset.mem_singleton] at halpha
    rcases halpha with rfl | rfl
    · exact ⟨(p ⟨xi, hxi⟩).left, rfl⟩
    · exact ⟨-(p ⟨xi, hxi⟩).right, by simp⟩
  · intro xi hxi alpha halpha beta hbeta
    rw [hR xi hxi, OrthonormalDifference.targetFinset] at halpha hbeta
    simp only [Finset.mem_insert, Finset.mem_singleton] at halpha hbeta
    rcases halpha with rfl | rfl <;> rcases hbeta with rfl | rfl
    · rw [if_pos rfl]
      exact characterPairing_realize_self_of_normSq_one'
        (p ⟨xi, hxi⟩).left (hpOrtho ⟨xi, hxi⟩).1
    · rw [if_neg (hpTargetNe ⟨xi, hxi⟩),
        characterPairing_neg_right',
        VirtualCharacter.characterPairing_realize,
        (hpOrtho ⟨xi, hxi⟩).2.2]
      norm_num
    · have hne : -VirtualCharacter.realize (p ⟨xi, hxi⟩).right ≠
          VirtualCharacter.realize (p ⟨xi, hxi⟩).left :=
        fun h ↦ hpTargetNe ⟨xi, hxi⟩ h.symm
      rw [if_neg hne, characterPairing_neg_left',
        VirtualCharacter.characterPairing_realize, coeffDot_comm,
        (hpOrtho ⟨xi, hxi⟩).2.2]
      norm_num
    · rw [if_pos rfl, characterPairing_neg_left',
        characterPairing_neg_right', neg_neg]
      exact characterPairing_realize_self_of_normSq_one'
        (p ⟨xi, hxi⟩).right (hpOrtho ⟨xi, hxi⟩).2.1
  · intro xi hxi
    rw [hpDiff' xi hxi, hR xi hxi]
    simp [OrthonormalDifference.targetFinset,
      hpTargetNe ⟨xi, hxi⟩, sub_eq_add_neg]
  · intro xi hxi phi hphi hphiXi hphiInvXi alpha halpha beta hbeta
    let x : {theta : ClassFunction L₀ ℂ // theta ∈ S} := ⟨phi, hphi⟩
    let y : {theta : ClassFunction L₀ ℂ // theta ∈ S} := ⟨xi, hxi⟩
    have hdxSpan : phi - ClassFunction.inverseLinear phi ∈
        AddSubgroup.closure S :=
      (AddSubgroup.closure S).sub_mem
        (AddSubgroup.subset_closure hphi)
        (AddSubgroup.subset_closure (hS.2 phi hphi))
    have hdySpan : xi - ClassFunction.inverseLinear xi ∈
        AddSubgroup.closure S :=
      (AddSubgroup.closure S).sub_mem
        (AddSubgroup.subset_closure hxi)
        (AddSubgroup.subset_closure (hS.2 xi hxi))
    have hdxOff := inverse_sub_supported' phi
    have hdyOff := inverse_sub_supported' xi
    have hsourcePair : characterPairing
        (phi - ClassFunction.inverseLinear phi)
        (xi - ClassFunction.inverseLinear xi) = 0 := by
      rw [characterPairing_sub_left', characterPairing_sub_right',
        characterPairing_sub_right', characterPairing_inverseLinear_left',
        characterPairing_inverseLinear', hphiXi, hphiInvXi]
      simp
    have htargetPair : characterPairing
        (VirtualCharacter.realize ((p x).left - (p x).right))
        (VirtualCharacter.realize ((p y).left - (p y).right)) = 0 := by
      rw [← hpDiff' phi hphi, ← hpDiff' xi hxi,
        hiso _ hdxSpan hdxOff _ hdySpan hdyOff, hsourcePair]
    have hxOne : VirtualCharacter.realize
        ((p x).left - (p x).right) 1 = 0 := by
      rw [← hpDiff' phi hphi]
      exact ClassFunction.eq_zero_of_mem_supportedOn
        (hsupp _ hdxSpan hdxOff) (by simp [nonidentitySet])
    have hyOne : VirtualCharacter.realize
        ((p y).left - (p y).right) 1 = 0 := by
      rw [← hpDiff' xi hxi]
      exact ClassFunction.eq_zero_of_mem_supportedOn
        (hsupp _ hdySpan hdyOff) (by simp [nonidentitySet])
    have hfour := vchar_pairs_orthonormal
      (p x).left (p x).right (p y).left (p y).right
      (1 : ℂ) (1 : ℂ) (hpOrtho x) (hpOrtho y)
      one_ne_zero one_ne_zero (by simpa using htargetPair) hxOne
      (by simpa using hyOne)
    rw [hR phi hphi, OrthonormalDifference.targetFinset] at halpha
    rw [hR xi hxi, OrthonormalDifference.targetFinset] at hbeta
    simp only [Finset.mem_insert, Finset.mem_singleton] at halpha hbeta
    rcases halpha with rfl | rfl <;> rcases hbeta with rfl | rfl
    · rw [VirtualCharacter.characterPairing_realize, hfour.2.2.1]
      norm_num
    · rw [characterPairing_neg_right',
        VirtualCharacter.characterPairing_realize, hfour.2.2.2.1]
      norm_num
    · rw [characterPairing_neg_left',
        VirtualCharacter.characterPairing_realize, hfour.2.2.2.2.1]
      norm_num
    · rw [characterPairing_neg_left', characterPairing_neg_right',
        VirtualCharacter.characterPairing_realize, hfour.2.2.2.2.2]
      norm_num

namespace PrimeDadeHypothesis

/-- The signed cyclic-TI column denoted `dsw j k` in the proof of
Peterfalvi 5.3(b). -/
def primeDadeSignedColumn
    (pd : PrimeDadeHypothesis G L K H A A₀ W W₁ W₂ defW)
    (isoL : CyclicTIIsometryData (k := ℂ)
      pd.prDade_prTI.prime_cycTIhyp)
    (isoG : CyclicTIIsometryData (k := ℂ) pd.prDade_cycTI)
    (j r : IrreducibleCharacter W₂ ℂ) :
    Finset (ClassFunction G ℂ) :=
  Finset.univ.image fun i : IrreducibleCharacter W₁ ℂ ↦
    (pd.prDade_prTI.primeTISign isoL j : ℂ) •
      isoG.cyclicTIImage (i, r)

/-- The explicit target pair attached to a reduced prime-TI column. -/
def primeDadeReducedImageFamily
    (pd : PrimeDadeHypothesis G L K H A A₀ W W₁ W₂ defW)
    (isoL : CyclicTIIsometryData (k := ℂ)
      pd.prDade_prTI.prime_cycTIhyp)
    (isoG : CyclicTIIsometryData (k := ℂ) pd.prDade_cycTI)
    (j : IrreducibleCharacter W₂ ℂ) :
    Finset (ClassFunction G ℂ) :=
  pd.primeDadeSignedColumn isoL isoG j j ∪
    (pd.primeDadeSignedColumn isoL isoG j
      (IrreducibleCharacter.dual j)).image fun alpha ↦ -alpha

@[simp]
theorem mem_primeDadeSignedColumn
    (pd : PrimeDadeHypothesis G L K H A A₀ W W₁ W₂ defW)
    (isoL : CyclicTIIsometryData (k := ℂ)
      pd.prDade_prTI.prime_cycTIhyp)
    (isoG : CyclicTIIsometryData (k := ℂ) pd.prDade_cycTI)
    (j r : IrreducibleCharacter W₂ ℂ) (alpha : ClassFunction G ℂ) :
    alpha ∈ pd.primeDadeSignedColumn isoL isoG j r ↔
      ∃ i : IrreducibleCharacter W₁ ℂ,
        alpha = (pd.prDade_prTI.primeTISign isoL j : ℂ) •
          isoG.cyclicTIImage (i, r) := by
  simp [primeDadeSignedColumn, eq_comm]

private theorem primeDadeSignedColumn_map_injective
    (pd : PrimeDadeHypothesis G L K H A A₀ W W₁ W₂ defW)
    (isoL : CyclicTIIsometryData (k := ℂ)
      pd.prDade_prTI.prime_cycTIhyp)
    (isoG : CyclicTIIsometryData (k := ℂ) pd.prDade_cycTI)
    (j r : IrreducibleCharacter W₂ ℂ) :
    Function.Injective
      (fun i : IrreducibleCharacter W₁ ℂ ↦
        (pd.prDade_prTI.primeTISign isoL j : ℂ) •
          isoG.cyclicTIImage (i, r)) := by
  intro i k hik
  by_contra hne
  have hsign : (pd.prDade_prTI.primeTISign isoL j : ℂ) ≠ 0 :=
    Int.cast_ne_zero.mpr
      (isSign_ne_zero (pd.prDade_prTI.primeTISign_isSign isoL j))
  have himage : isoG.cyclicTIImage (i, r) =
      isoG.cyclicTIImage (k, r) :=
    smul_right_injective (ClassFunction G ℂ) hsign hik
  have hpair := congrArg
    (fun alpha : ClassFunction G ℂ ↦
      characterPairing (isoG.cyclicTIImage (i, r)) alpha) himage
  rw [isoG.characterPairing_cyclicTIImage,
    isoG.characterPairing_cyclicTIImage, if_pos rfl,
    if_neg (by simpa using hne)] at hpair
  norm_num at hpair

theorem card_primeDadeSignedColumn
    (pd : PrimeDadeHypothesis G L K H A A₀ W W₁ W₂ defW)
    (isoL : CyclicTIIsometryData (k := ℂ)
      pd.prDade_prTI.prime_cycTIhyp)
    (isoG : CyclicTIIsometryData (k := ℂ) pd.prDade_cycTI)
    (j r : IrreducibleCharacter W₂ ℂ) :
    (pd.primeDadeSignedColumn isoL isoG j r).card = Nat.card W₁ := by
  letI : IsCyclic W₁ := pd.prDade_prTI.complement_cyclic
  rw [primeDadeSignedColumn, Finset.card_image_iff.mpr]
  · simpa only [Finset.card_univ] using
      (IrreducibleCharacter.card_eq_natCard_of_isCyclic
        (C := W₁) (k := ℂ))
  · exact (primeDadeSignedColumn_map_injective pd isoL isoG j r).injOn

theorem sum_primeDadeSignedColumn
    (pd : PrimeDadeHypothesis G L K H A A₀ W W₁ W₂ defW)
    (isoL : CyclicTIIsometryData (k := ℂ)
      pd.prDade_prTI.prime_cycTIhyp)
    (isoG : CyclicTIIsometryData (k := ℂ) pd.prDade_cycTI)
    (j r : IrreducibleCharacter W₂ ℂ) :
    ∑ alpha ∈ pd.primeDadeSignedColumn isoL isoG j r, alpha =
      (pd.prDade_prTI.primeTISign isoL j : ℂ) •
        ∑ i : IrreducibleCharacter W₁ ℂ,
          isoG.cyclicTIImage (i, r) := by
  rw [primeDadeSignedColumn]
  rw [Finset.sum_image]
  · rw [Finset.smul_sum]
  · intro i hi k hk hik
    exact primeDadeSignedColumn_map_injective pd isoL isoG j r hik

private theorem primeDadeSignedColumn_virtual
    (pd : PrimeDadeHypothesis G L K H A A₀ W W₁ W₂ defW)
    (isoL : CyclicTIIsometryData (k := ℂ)
      pd.prDade_prTI.prime_cycTIhyp)
    (isoG : CyclicTIIsometryData (k := ℂ) pd.prDade_cycTI)
    (j r : IrreducibleCharacter W₂ ℂ)
    {alpha : ClassFunction G ℂ}
    (halpha : alpha ∈ pd.primeDadeSignedColumn isoL isoG j r) :
    ClassFunction.IsVirtual alpha := by
  obtain ⟨i, rfl⟩ :=
    (pd.mem_primeDadeSignedColumn isoL isoG j r _).mp halpha
  obtain ⟨chi, epsilon, hepsilon, himage⟩ :=
    isoG.cyclicTIImage_eq_signed_irreducible (i, r)
  let delta := pd.prDade_prTI.primeTISign isoL j
  refine ⟨Finsupp.single chi (delta * epsilon), ?_⟩
  rw [VirtualCharacter.realize_single, Int.cast_mul, himage, smul_smul]

private theorem primeDadeSignedColumn_orthonormal
    (pd : PrimeDadeHypothesis G L K H A A₀ W W₁ W₂ defW)
    (isoL : CyclicTIIsometryData (k := ℂ)
      pd.prDade_prTI.prime_cycTIhyp)
    (isoG : CyclicTIIsometryData (k := ℂ) pd.prDade_cycTI)
    (j r : IrreducibleCharacter W₂ ℂ)
    {alpha beta : ClassFunction G ℂ}
    (halpha : alpha ∈ pd.primeDadeSignedColumn isoL isoG j r)
    (hbeta : beta ∈ pd.primeDadeSignedColumn isoL isoG j r) :
    characterPairing alpha beta = if alpha = beta then 1 else 0 := by
  obtain ⟨i, rfl⟩ :=
    (pd.mem_primeDadeSignedColumn isoL isoG j r _).mp halpha
  obtain ⟨k, rfl⟩ :=
    (pd.mem_primeDadeSignedColumn isoL isoG j r _).mp hbeta
  have hsquare :
      (pd.prDade_prTI.primeTISign isoL j : ℂ) *
        (pd.prDade_prTI.primeTISign isoL j : ℂ) = 1 := by
    rcases pd.prDade_prTI.primeTISign_isSign isoL j with h | h <;>
      simp [h]
  by_cases hik : i = k
  · subst k
    rw [if_pos rfl, characterPairing_smul_left,
      characterPairing_smul_right,
      isoG.characterPairing_cyclicTIImage, if_pos rfl]
    calc
      _ = ((pd.prDade_prTI.primeTISign isoL j : ℂ) *
          (pd.prDade_prTI.primeTISign isoL j : ℂ)) * 1 := by ring
      _ = 1 := by rw [hsquare, one_mul]
  · have hne :
        (pd.prDade_prTI.primeTISign isoL j : ℂ) •
              isoG.cyclicTIImage (i, r) ≠
            (pd.prDade_prTI.primeTISign isoL j : ℂ) •
              isoG.cyclicTIImage (k, r) :=
        (primeDadeSignedColumn_map_injective pd isoL isoG j r).ne hik
    rw [if_neg hne, characterPairing_smul_left,
      characterPairing_smul_right,
      isoG.characterPairing_cyclicTIImage,
      if_neg (by simpa using hik)]
    simp

private theorem primeDadeSignedColumns_orthogonal
    (pd : PrimeDadeHypothesis G L K H A A₀ W W₁ W₂ defW)
    (isoL : CyclicTIIsometryData (k := ℂ)
      pd.prDade_prTI.prime_cycTIhyp)
    (isoG : CyclicTIIsometryData (k := ℂ) pd.prDade_cycTI)
    (j₁ j₂ r₁ r₂ : IrreducibleCharacter W₂ ℂ)
    (hr : r₁ ≠ r₂)
    {alpha beta : ClassFunction G ℂ}
    (halpha : alpha ∈ pd.primeDadeSignedColumn isoL isoG j₁ r₁)
    (hbeta : beta ∈ pd.primeDadeSignedColumn isoL isoG j₂ r₂) :
    characterPairing alpha beta = 0 := by
  obtain ⟨i, rfl⟩ :=
    (pd.mem_primeDadeSignedColumn isoL isoG j₁ r₁ _).mp halpha
  obtain ⟨k, rfl⟩ :=
    (pd.mem_primeDadeSignedColumn isoL isoG j₂ r₂ _).mp hbeta
  rw [characterPairing_smul_left, characterPairing_smul_right,
    isoG.characterPairing_cyclicTIImage,
    if_neg (by intro h; exact hr (congrArg Prod.snd h)), mul_zero,
    mul_zero]

private theorem primeDadeSignedColumn_disjoint_negDual
    (pd : PrimeDadeHypothesis G L K H A A₀ W W₁ W₂ defW)
    (isoL : CyclicTIIsometryData (k := ℂ)
      pd.prDade_prTI.prime_cycTIhyp)
    (isoG : CyclicTIIsometryData (k := ℂ) pd.prDade_cycTI)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.dual j) :
    Disjoint (pd.primeDadeSignedColumn isoL isoG j j)
      ((pd.primeDadeSignedColumn isoL isoG j
        (IrreducibleCharacter.dual j)).image fun alpha ↦ -alpha) := by
  rw [Finset.disjoint_left]
  intro alpha halpha halphaNeg
  obtain ⟨beta, hbeta, hneg⟩ := Finset.mem_image.mp halphaNeg
  have hcross := primeDadeSignedColumns_orthogonal pd isoL isoG
    j j j (IrreducibleCharacter.dual j) hj halpha hbeta
  have hself := primeDadeSignedColumn_orthonormal pd isoL isoG
    j (IrreducibleCharacter.dual j) hbeta hbeta
  rw [if_pos rfl] at hself
  have halphaEq : alpha = -beta := hneg.symm
  rw [halphaEq, characterPairing_neg_left', hself] at hcross
  norm_num at hcross

theorem sum_primeDadeReducedImageFamily
    (pd : PrimeDadeHypothesis G L K H A A₀ W W₁ W₂ defW)
    (isoL : CyclicTIIsometryData (k := ℂ)
      pd.prDade_prTI.prime_cycTIhyp)
    (isoG : CyclicTIIsometryData (k := ℂ) pd.prDade_cycTI)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.dual j) :
    ∑ alpha ∈ pd.primeDadeReducedImageFamily isoL isoG j, alpha =
      (pd.prDade_prTI.primeTISign isoL j : ℂ) •
        ((∑ i : IrreducibleCharacter W₁ ℂ,
            isoG.cyclicTIImage (i, j)) -
          ∑ i : IrreducibleCharacter W₁ ℂ,
            isoG.cyclicTIImage
              (i, IrreducibleCharacter.dual j)) := by
  let C := pd.primeDadeSignedColumn isoL isoG j j
  let D := pd.primeDadeSignedColumn isoL isoG j
    (IrreducibleCharacter.dual j)
  have hdisj : Disjoint C (D.image fun alpha ↦ -alpha) :=
    primeDadeSignedColumn_disjoint_negDual pd isoL isoG j hj
  rw [primeDadeReducedImageFamily, Finset.sum_union hdisj]
  have hnegInj : Set.InjOn (fun alpha : ClassFunction G ℂ ↦ -alpha) D :=
    Set.injOn_of_injective neg_injective
  rw [Finset.sum_image hnegInj]
  rw [Finset.sum_neg_distrib,
    sum_primeDadeSignedColumn, sum_primeDadeSignedColumn, smul_sub]
  rw [sub_eq_add_neg]

private theorem primeDadeReducedImageFamily_virtual
    (pd : PrimeDadeHypothesis G L K H A A₀ W W₁ W₂ defW)
    (isoL : CyclicTIIsometryData (k := ℂ)
      pd.prDade_prTI.prime_cycTIhyp)
    (isoG : CyclicTIIsometryData (k := ℂ) pd.prDade_cycTI)
    (j : IrreducibleCharacter W₂ ℂ)
    {alpha : ClassFunction G ℂ}
    (halpha : alpha ∈ pd.primeDadeReducedImageFamily isoL isoG j) :
    ClassFunction.IsVirtual alpha := by
  rw [primeDadeReducedImageFamily, Finset.mem_union] at halpha
  rcases halpha with halpha | halpha
  · exact primeDadeSignedColumn_virtual pd isoL isoG j j halpha
  · obtain ⟨beta, hbeta, rfl⟩ := Finset.mem_image.mp halpha
    exact (primeDadeSignedColumn_virtual pd isoL isoG j
      (IrreducibleCharacter.dual j) hbeta).neg

private theorem primeDadeReducedImageFamily_orthonormal
    (pd : PrimeDadeHypothesis G L K H A A₀ W W₁ W₂ defW)
    (isoL : CyclicTIIsometryData (k := ℂ)
      pd.prDade_prTI.prime_cycTIhyp)
    (isoG : CyclicTIIsometryData (k := ℂ) pd.prDade_cycTI)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.dual j)
    {alpha beta : ClassFunction G ℂ}
    (halpha : alpha ∈ pd.primeDadeReducedImageFamily isoL isoG j)
    (hbeta : beta ∈ pd.primeDadeReducedImageFamily isoL isoG j) :
    characterPairing alpha beta = if alpha = beta then 1 else 0 := by
  let C := pd.primeDadeSignedColumn isoL isoG j j
  let D := pd.primeDadeSignedColumn isoL isoG j
    (IrreducibleCharacter.dual j)
  have hdisj : Disjoint C (D.image fun gamma ↦ -gamma) :=
    primeDadeSignedColumn_disjoint_negDual pd isoL isoG j hj
  rw [primeDadeReducedImageFamily, Finset.mem_union] at halpha hbeta
  rcases halpha with halpha | halpha <;>
    rcases hbeta with hbeta | hbeta
  · exact primeDadeSignedColumn_orthonormal pd isoL isoG j j halpha hbeta
  · have hne : alpha ≠ beta := by
      intro heq
      exact (Finset.disjoint_left.mp hdisj halpha) (heq.symm ▸ hbeta)
    obtain ⟨beta₀, hbeta₀, rfl⟩ := Finset.mem_image.mp hbeta
    rw [if_neg hne, characterPairing_neg_right']
    exact neg_eq_zero.mpr (primeDadeSignedColumns_orthogonal pd isoL isoG
      j j j (IrreducibleCharacter.dual j) hj halpha hbeta₀)
  · have hne : alpha ≠ beta := by
      intro heq
      exact (Finset.disjoint_left.mp hdisj hbeta) (heq ▸ halpha)
    obtain ⟨alpha₀, halpha₀, rfl⟩ := Finset.mem_image.mp halpha
    rw [if_neg hne, characterPairing_neg_left']
    exact neg_eq_zero.mpr (primeDadeSignedColumns_orthogonal pd isoL isoG
      j j (IrreducibleCharacter.dual j) j hj.symm halpha₀ hbeta)
  · obtain ⟨alpha₀, halpha₀, rfl⟩ := Finset.mem_image.mp halpha
    obtain ⟨beta₀, hbeta₀, rfl⟩ := Finset.mem_image.mp hbeta
    rw [characterPairing_neg_left', characterPairing_neg_right', neg_neg]
    have hbase := primeDadeSignedColumn_orthonormal pd isoL isoG j
      (IrreducibleCharacter.dual j) halpha₀ hbeta₀
    simpa only [neg_inj] using hbase

private theorem primeDadeReducedImageFamilies_orthogonal
    (pd : PrimeDadeHypothesis G L K H A A₀ W W₁ W₂ defW)
    (isoL : CyclicTIIsometryData (k := ℂ)
      pd.prDade_prTI.prime_cycTIhyp)
    (isoG : CyclicTIIsometryData (k := ℂ) pd.prDade_cycTI)
    (j r : IrreducibleCharacter W₂ ℂ)
    (hjr : j ≠ r)
    (hjdualr : j ≠ IrreducibleCharacter.dual r)
    {alpha beta : ClassFunction G ℂ}
    (halpha : alpha ∈ pd.primeDadeReducedImageFamily isoL isoG j)
    (hbeta : beta ∈ pd.primeDadeReducedImageFamily isoL isoG r) :
    characterPairing alpha beta = 0 := by
  have hdualjr : IrreducibleCharacter.dual j ≠ r := by
    intro h
    apply hjdualr
    calc
      j = IrreducibleCharacter.dual (IrreducibleCharacter.dual j) :=
        (IrreducibleCharacter.dual_dual j).symm
      _ = IrreducibleCharacter.dual r :=
        congrArg IrreducibleCharacter.dual h
  have hdualjdualr :
      IrreducibleCharacter.dual j ≠ IrreducibleCharacter.dual r := by
    intro h
    apply hjr
    calc
      j = IrreducibleCharacter.dual (IrreducibleCharacter.dual j) :=
        (IrreducibleCharacter.dual_dual j).symm
      _ = IrreducibleCharacter.dual (IrreducibleCharacter.dual r) :=
        congrArg IrreducibleCharacter.dual h
      _ = r := IrreducibleCharacter.dual_dual r
  rw [primeDadeReducedImageFamily, Finset.mem_union] at halpha hbeta
  rcases halpha with halpha | halpha <;>
    rcases hbeta with hbeta | hbeta
  · exact primeDadeSignedColumns_orthogonal pd isoL isoG
      j r j r hjr halpha hbeta
  · obtain ⟨beta₀, hbeta₀, rfl⟩ := Finset.mem_image.mp hbeta
    rw [characterPairing_neg_right']
    exact neg_eq_zero.mpr (primeDadeSignedColumns_orthogonal pd isoL isoG
      j r j (IrreducibleCharacter.dual r) hjdualr halpha hbeta₀)
  · obtain ⟨alpha₀, halpha₀, rfl⟩ := Finset.mem_image.mp halpha
    rw [characterPairing_neg_left']
    exact neg_eq_zero.mpr (primeDadeSignedColumns_orthogonal pd isoL isoG
      j r (IrreducibleCharacter.dual j) r hdualjr halpha₀ hbeta)
  · obtain ⟨alpha₀, halpha₀, rfl⟩ := Finset.mem_image.mp halpha
    obtain ⟨beta₀, hbeta₀, rfl⟩ := Finset.mem_image.mp hbeta
    rw [characterPairing_neg_left', characterPairing_neg_right', neg_neg]
    exact primeDadeSignedColumns_orthogonal pd isoL isoG
      j r (IrreducibleCharacter.dual j)
      (IrreducibleCharacter.dual r) hdualjdualr halpha₀ hbeta₀

/- Peterfalvi 5.3(b).  For a dual-closed part of the prime-Dade kernel
layer, the irreducible members use the abstract pairs from 5.3(a), while
every reduced column is assigned its two explicit signed cyclic-TI columns. -/
set_option maxHeartbeats 2000000 in
theorem prDade_subcoherent
    (pd : PrimeDadeHypothesis G L K H A A₀ W W₁ W₂ defW)
    (isoL : CyclicTIIsometryData (k := ℂ)
      pd.prDade_prTI.prime_cycTIhyp)
    (isoG : CyclicTIIsometryData (k := ℂ) pd.prDade_cycTI)
    (S : Set (ClassFunction L ℂ))
    (hS : cfConjC_subset S
      (↑(seqIndD (k := ℂ) (K.subgroupOf L)
        pd.signalizerInKernel ⊥) : Set (ClassFunction L ℂ)))
    (hnr : ∀ phi ∈ S, ClassFunction.inverseLinear phi ≠ phi) :
    ∃ R : ClassFunction L ℂ → Finset (ClassFunction G ℂ),
      subcoherent S (Dade pd.prDade_hyp) R ∧
        (∀ phi ∈ S, IsIrreducibleCharacter L ℂ phi →
          ∀ w : IrreducibleCharacter W ℂ, ∀ alpha ∈ R phi,
            characterPairing alpha
              (isoG.linearMap (w : ClassFunction W ℂ)) = 0) ∧
        ∀ j : IrreducibleCharacter W₂ ℂ,
          R (pd.prDade_prTI.primeTIRed isoL j) =
            pd.primeDadeReducedImageFamily isoL isoG j := by
  classical
  let pti := pd.prDade_prTI
  let KL : Subgroup L := K.subgroupOf L
  let S₀ : Set (ClassFunction L ℂ) :=
    ↑(seqIndD (k := ℂ) KL pd.signalizerInKernel ⊥)
  let IrrL : Set (ClassFunction L ℂ) :=
    Set.range fun chi : IrreducibleCharacter L ℂ ↦
      (chi : ClassFunction L ℂ)
  let S₁ : Set (ClassFunction L ℂ) := S ∩ IrrL
  letI : KL.Normal := pd.prDade_prTI.kernel_normal
  have hmemberPrimeSupport {phi : ClassFunction L ℂ} (hphi : phi ∈ S) :
      phi ∈ ClassFunction.supportedOn (primeDadeSupport L A) := by
    have hphi₀ : phi ∈ seqIndD (k := ℂ) KL pd.signalizerInKernel ⊥ :=
      hS.1 hphi
    obtain ⟨theta, htheta, rfl⟩ := seqIndP.mp hphi₀
    exact pd.prDade_Ind_irr_on theta (mem_Iirr_kerD.mp htheta).2
  have hspanPrimeSupport {phi : ClassFunction L ℂ}
      (hphi : phi ∈ AddSubgroup.closure S) :
      phi ∈ ClassFunction.supportedOn (primeDadeSupport L A) := by
    induction hphi using AddSubgroup.closure_induction with
    | mem phi hphi => exact hmemberPrimeSupport hphi
    | zero =>
        exact (ClassFunction.supportedOn (R := ℂ)
          (primeDadeSupport L A)).zero_mem
    | add phi psi hphi hpsi ihphi ihpsi =>
        exact (ClassFunction.supportedOn (R := ℂ)
          (primeDadeSupport L A)).add_mem ihphi ihpsi
    | neg phi hphi ihphi =>
        exact (ClassFunction.supportedOn (R := ℂ)
          (primeDadeSupport L A)).neg_mem ihphi
  have hspanVirtual {phi : ClassFunction L ℂ}
      (hphi : phi ∈ AddSubgroup.closure S) :
      ClassFunction.IsVirtual phi := by
    induction hphi using AddSubgroup.closure_induction with
    | mem phi hphi => exact seqInd_vcharW KL (hS.1 hphi)
    | zero => exact ClassFunction.IsVirtual.zero
    | add phi psi hphi hpsi ihphi ihpsi => exact ihphi.add ihpsi
    | neg phi hphi ihphi => exact ihphi.neg
  have hspanSupportA {phi : ClassFunction L ℂ}
      (hphi : phi ∈ AddSubgroup.closure S)
      (hoff : phi ∈ ClassFunction.supportedOn (nonidentitySet L)) :
      phi ∈ ClassFunction.supportedOn {x : L | (x : Gamma) ∈ A} := by
    have hprime := hspanPrimeSupport hphi
    rw [ClassFunction.mem_supportedOn_iff]
    intro x hxA
    have hxA' : (x : Gamma) ∉ A := by simpa using hxA
    by_cases hx1 : x = 1
    · subst x
      exact ClassFunction.eq_zero_of_mem_supportedOn hoff
        (by simp [nonidentitySet])
    · apply ClassFunction.eq_zero_of_mem_supportedOn hprime
      change ¬(x.1 = (1 : Gamma) ∨ x.1 ∈ A)
      rw [not_or]
      constructor
      · intro hx
        apply hx1
        exact Subtype.ext hx
      · simpa using hxA'
  have hspanSupportA₀ {phi : ClassFunction L ℂ}
      (hphi : phi ∈ AddSubgroup.closure S)
      (hoff : phi ∈ ClassFunction.supportedOn (nonidentitySet L)) :
      phi ∈ ClassFunction.supportedOn {x : L | (x : Gamma) ∈ A₀} := by
    have hA := hspanSupportA hphi hoff
    apply ClassFunction.mem_supportedOn_iff.mpr
    intro x hxA₀
    apply ClassFunction.eq_zero_of_mem_supportedOn hA
    intro hxA
    exact hxA₀ (pd.set_subset_dadeSet hxA)
  have hDadeIsometry : ∀ phi ∈ AddSubgroup.closure S,
      phi ∈ ClassFunction.supportedOn (nonidentitySet L) →
      ∀ psi ∈ AddSubgroup.closure S,
        psi ∈ ClassFunction.supportedOn (nonidentitySet L) →
        characterPairing (Dade pd.prDade_hyp phi)
            (Dade pd.prDade_hyp psi) = characterPairing phi psi := by
    intro phi hphi hphiOff psi hpsi hpsiOff
    obtain ⟨z, hz⟩ := hspanVirtual hphi
    obtain ⟨w, hw⟩ := hspanVirtual hpsi
    have hzA₀ : VirtualCharacter.realize z ∈
        ClassFunction.supportedOn {x : L | (x : Gamma) ∈ A₀} := by
      rw [hz]
      exact hspanSupportA₀ hphi hphiOff
    have hwA₀ : VirtualCharacter.realize w ∈
        ClassFunction.supportedOn {x : L | (x : Gamma) ∈ A₀} := by
      rw [hw]
      exact hspanSupportA₀ hpsi hpsiOff
    obtain ⟨z', hz', _⟩ :=
      (Dade_Zisometry pd.prDade_hyp).2 z hzA₀
    obtain ⟨w', hw', _⟩ :=
      (Dade_Zisometry pd.prDade_hyp).2 w hwA₀
    have hstar₀ := (Dade_Zisometry pd.prDade_hyp).1 z w hzA₀ hwA₀
    have hstar : characterPairing
        (VirtualCharacter.realize z') (VirtualCharacter.realize w') =
        characterPairing
          (VirtualCharacter.realize z) (VirtualCharacter.realize w) := by
      rw [← starCharacterPairing_realize_eq_characterPairing' z' w',
        ← starCharacterPairing_realize_eq_characterPairing' z w]
      simpa only [hz', hw'] using hstar₀
    calc
      characterPairing (Dade pd.prDade_hyp phi)
          (Dade pd.prDade_hyp psi) =
          characterPairing (VirtualCharacter.realize z')
            (VirtualCharacter.realize w') := by
              rw [← hz, ← hw, hz', hw']
      _ = characterPairing (VirtualCharacter.realize z)
          (VirtualCharacter.realize w) := hstar
      _ = characterPairing phi psi := by rw [hz, hw]
  have hDadeVirtual : ∀ phi ∈ AddSubgroup.closure S,
      phi ∈ ClassFunction.supportedOn (nonidentitySet L) →
        ClassFunction.IsVirtual (Dade pd.prDade_hyp phi) := by
    intro phi hphi hoff
    obtain ⟨z, hz⟩ := hspanVirtual hphi
    have hzA₀ : VirtualCharacter.realize z ∈
        ClassFunction.supportedOn {x : L | (x : Gamma) ∈ A₀} := by
      rw [hz]
      exact hspanSupportA₀ hphi hoff
    obtain ⟨beta, hbeta, _⟩ :=
      (Dade_Zisometry pd.prDade_hyp).2 z hzA₀
    refine ⟨beta, ?_⟩
    rw [← hz]
    exact hbeta.symm
  have hDadeSupported : ∀ phi ∈ AddSubgroup.closure S,
      phi ∈ ClassFunction.supportedOn (nonidentitySet L) →
        Dade pd.prDade_hyp phi ∈
          ClassFunction.supportedOn (nonidentitySet G) := by
    intro phi hphi hoff
    exact Dade_cfun pd.prDade_hyp phi
  have hS₁sub : S₁ ⊆ S := Set.inter_subset_left
  have hS₁closed : cfConjC_closed S₁ := by
    intro phi hphi
    rcases hphi with ⟨hphiS, chi, rfl⟩
    refine ⟨hS.2 _ hphiS, ?_⟩
    refine ⟨IrreducibleCharacter.dual chi, ?_⟩
    exact (ClassFunction.inverseLinear_irreducible chi).symm
  have hS₁ : cfConjC_subset S₁ IrrL := by
    exact ⟨Set.inter_subset_right, hS₁closed⟩
  have hspanS₁ : AddSubgroup.closure S₁ ≤ AddSubgroup.closure S :=
    AddSubgroup.closure_mono hS₁sub
  obtain ⟨R₁, hR₁⟩ := irr_subcoherent S₁ (Dade pd.prDade_hyp)
    hS₁ (fun phi hphi ↦ hnr phi hphi.1)
    (fun phi hphi hoff psi hpsi hpsiOff ↦
      hDadeIsometry phi (hspanS₁ hphi) hoff
        psi (hspanS₁ hpsi) hpsiOff)
    (fun phi hphi hoff ↦ hDadeVirtual phi (hspanS₁ hphi) hoff)
    (fun phi hphi hoff ↦ hDadeSupported phi (hspanS₁ hphi) hoff)
  have inS₁_of_not_reduced {phi : ClassFunction L ℂ}
      (hphi : phi ∈ S)
      (hno : ¬ ∃ j : IrreducibleCharacter W₂ ℂ,
        phi = pti.primeTIRed isoL j) : phi ∈ S₁ := by
    refine ⟨hphi, ?_⟩
    have hphi₀ : phi ∈ seqIndD (k := ℂ) KL pd.signalizerInKernel ⊥ :=
      hS.1 hphi
    obtain ⟨theta, htheta, hthetaEq⟩ := seqIndP.mp hphi₀
    rcases pti.prTIres_irr_cases isoL theta with hred | hirr
    · obtain ⟨j, hj⟩ := hred
      exfalso
      apply hno
      refine ⟨j, ?_⟩
      calc
        phi = ClassFunction.induce KL
            (theta : ClassFunction KL ℂ) := hthetaEq
        _ = ClassFunction.induce KL
            (pti.primeTI_Ires isoL j : ClassFunction KL ℂ) := by rw [hj]
        _ = pti.primeTIRed isoL j := pti.cfInd_prTIres isoL j
    · refine ⟨⟨phi, ?_⟩, rfl⟩
      rw [hthetaEq]
      exact hirr.1
  have hR₁_cyclic (phi : ClassFunction L ℂ) (hphi : phi ∈ S₁)
      (q : IrreducibleCharacter W₁ ℂ × IrreducibleCharacter W₂ ℂ)
      (alpha : ClassFunction G ℂ) (halpha : alpha ∈ R₁ phi) :
      characterPairing alpha (isoG.cyclicTIImage q) = 0 := by
    let d := phi - ClassFunction.inverseLinear phi
    let beta := Dade pd.prDade_hyp d
    have hdSpan : d ∈ AddSubgroup.closure S₁ :=
      (AddSubgroup.closure S₁).sub_mem
        (AddSubgroup.subset_closure hphi)
        (AddSubgroup.subset_closure (hS₁closed phi hphi))
    have hdOff : d ∈ ClassFunction.supportedOn (nonidentitySet L) :=
      inverse_sub_supported' phi
    obtain ⟨chi, hchi⟩ := hphi.2
    have hinvChi : ClassFunction.inverseLinear phi =
        (IrreducibleCharacter.dual chi : ClassFunction L ℂ) := by
      rw [← hchi]
      exact ClassFunction.inverseLinear_irreducible chi
    have hchiNe : chi ≠ IrreducibleCharacter.dual chi := by
      intro heq
      apply hnr phi hphi.1
      calc
        ClassFunction.inverseLinear phi =
            (IrreducibleCharacter.dual chi : ClassFunction L ℂ) :=
          hinvChi
        _ = (chi : ClassFunction L ℂ) :=
          congrArg (fun eta : IrreducibleCharacter L ℂ ↦
            (eta : ClassFunction L ℂ)) heq.symm
        _ = phi := hchi
    have hnormSource : characterPairing d d = (2 : ℂ) := by
      dsimp only [d]
      rw [characterPairing_sub_left', characterPairing_sub_right',
        characterPairing_sub_right', hinvChi, ← hchi]
      rw [IrreducibleCharacter.characterPairing_self,
        IrreducibleCharacter.characterPairing_self,
        IrreducibleCharacter.characterPairing_eq_zero hchiNe,
        IrreducibleCharacter.characterPairing_eq_zero hchiNe.symm]
      norm_num
    obtain ⟨z, hz⟩ := hR₁.tau_virtual d hdSpan hdOff
    have hnormTarget : characterPairing beta beta = (2 : ℂ) := by
      change characterPairing (Dade pd.prDade_hyp d)
        (Dade pd.prDade_hyp d) = (2 : ℂ)
      rw [hR₁.tau_isometry d hdSpan hdOff d hdSpan hdOff,
        hnormSource]
    have hnormZ : normSq z = 2 := by
      apply Int.cast_injective (α := ℂ)
      rw [← VirtualCharacter.characterPairing_realize_self, hz]
      exact hnormTarget
    have hzero : Set.EqOn
        (fun w : W ↦ beta
          ⟨w, pd.prDade_cycTI.le_group w.property⟩) 0
        (cyclicTISetInW W W₁ W₂) := by
      intro w hw
      let wG : G := ⟨w, pd.prDade_cycTI.le_group w.property⟩
      let wL : L := ⟨w, pti.directProduct_le_group w.property⟩
      have hwAmbient : (w : Gamma) ∈ cyclicTISet W W₁ W₂ := hw
      have hwClass : (w : Gamma) ∈
          classSupportWithin L (cyclicTISet W W₁ W₂) := by
        exact ⟨(w : Gamma), hwAmbient, 1, L.one_mem, by simp⟩
      have hwA₀ : (w : Gamma) ∈ A₀ := by
        rw [pd.prDade_def.dadeSet_eq]
        exact Or.inr hwClass
      have hdA : d ∈
          ClassFunction.supportedOn {x : L | (x : Gamma) ∈ A} :=
        hspanSupportA (hspanS₁ hdSpan) hdOff
      have hwNotK : (w : Gamma) ∉ K :=
        pd.prDade_supp_disjoint hwAmbient
      have hwNotA : (w : Gamma) ∉ A := by
        intro hwA
        exact hwNotK (pd.prDade_def.set_le_kernel_diff_one hwA).1
      have hDadeEval := Dade_id pd.prDade_hyp d hwA₀
      change beta wG = (0 : W → ℂ) w
      simp only [Pi.zero_apply]
      calc
        beta wG = d wL := by simpa [beta, wG, wL] using hDadeEval
        _ = 0 := ClassFunction.eq_zero_of_mem_supportedOn hdA hwNotA
    have hNCle : isoG.cyclicTINC beta ≤ 2 := by
      have hbound := isoG.cyclicTINC_realize_le_normSq z
      rw [hz, hnormZ] at hbound
      exact_mod_cast hbound
    letI : IsCyclic W₁ := pti.complement_cyclic
    letI : IsCyclic W₂ := pti.fixed_cyclic
    have hcard₁ : Fintype.card (IrreducibleCharacter W₁ ℂ) =
        Nat.card W₁ := by
      exact IrreducibleCharacter.card_eq_natCard_of_isCyclic
        (C := W₁) (k := ℂ)
    have hcard₂ : Fintype.card (IrreducibleCharacter W₂ ℂ) =
        Nat.card W₂ := by
      exact IrreducibleCharacter.card_eq_natCard_of_isCyclic
        (C := W₂) (k := ℂ)
    have hminGt : 2 < min
        (Fintype.card (IrreducibleCharacter W₁ ℂ))
        (Fintype.card (IrreducibleCharacter W₂ ℂ)) := by
      rw [hcard₁, hcard₂]
      have hleft := pd.prDade_cycTI.two_lt_card_left
      have hright := pd.prDade_cycTI.two_lt_card_right
      omega
    have hNCzero : isoG.cyclicTINC beta = 0 := by
      by_contra hne
      have hpos : 0 < isoG.cyclicTINC beta := Nat.pos_of_ne_zero hne
      have hsmall : isoG.cyclicTINC beta <
          2 * min
            (Fintype.card (IrreducibleCharacter W₁ ℂ))
            (Fintype.card (IrreducibleCharacter W₂ ℂ)) := by
        omega
      have hminLe := isoG.cyclicTINC_min_le beta hzero hpos hsmall
      omega
    have hbetaCyclic : characterPairing beta
        (isoG.cyclicTIImage q) = 0 := by
      by_contra hpair
      have hmem : q ∈ isoG.cyclicTICoefficientSupport beta :=
        (isoG.mem_cyclicTICoefficientSupport beta q).2 hpair
      have hpos : 0 < isoG.cyclicTINC beta := by
        exact Finset.card_pos.mpr ⟨q, hmem⟩
      omega
    have hbetaAlpha : characterPairing beta alpha = 1 := by
      rw [show beta = Dade pd.prDade_hyp
          (phi - ClassFunction.inverseLinear phi) by rfl,
        hR₁.tau_inverse_sub phi hphi]
      change (characterPairingRight alpha
        (∑ gamma ∈ R₁ phi, gamma)) = 1
      rw [map_sum, Finset.sum_eq_single alpha]
      · change characterPairing alpha alpha = 1
        simpa using
          hR₁.image_orthonormal phi hphi alpha halpha alpha halpha
      · intro gamma hgamma hgammaNe
        change characterPairing gamma alpha = 0
        rw [hR₁.image_orthonormal phi hphi gamma hgamma alpha halpha,
          if_neg hgammaNe]
      · intro halphaNot
        exact (halphaNot halpha).elim
    obtain ⟨za, hza⟩ := hR₁.image_virtual phi hphi alpha halpha
    have hnormZa : normSq za = 1 := by
      apply Int.cast_injective (α := ℂ)
      rw [← VirtualCharacter.characterPairing_realize_self, hza,
        hR₁.image_orthonormal phi hphi alpha halpha alpha halpha,
        if_pos rfl]
      norm_num
    obtain ⟨eta, epsilon, hepsilon, hzaSingle⟩ :=
      eq_signed_single_of_normSq_eq_one za hnormZa
    have halphaEq : alpha =
        (epsilon : ℂ) • (eta : ClassFunction G ℂ) := by
      rw [← hza, hzaSingle, VirtualCharacter.realize_single]
    obtain ⟨theta, delta, hdelta, hqImage⟩ :=
      isoG.cyclicTIImage_eq_signed_irreducible q
    by_contra hpairAlpha
    have hetaTheta : eta = theta := by
      by_contra hne
      apply hpairAlpha
      rw [halphaEq, hqImage, characterPairing_smul_left,
        characterPairing_smul_right,
        IrreducibleCharacter.characterPairing_eq_zero hne]
      simp
    have hbetaEta : characterPairing beta
        (eta : ClassFunction G ℂ) ≠ 0 := by
      intro hzero
      rw [halphaEq, characterPairing_smul_right, hzero, mul_zero] at hbetaAlpha
      exact zero_ne_one hbetaAlpha
    apply hbetaEta
    have hdeltaNe : (delta : ℂ) ≠ 0 :=
      Int.cast_ne_zero.mpr (isSign_ne_zero hdelta)
    rw [hqImage, ← hetaTheta, characterPairing_smul_right] at hbetaCyclic
    exact (mul_eq_zero.mp hbetaCyclic).resolve_left hdeltaNe
  have hR₁_reduced (phi : ClassFunction L ℂ) (hphi : phi ∈ S₁)
      (j : IrreducibleCharacter W₂ ℂ)
      (alpha beta : ClassFunction G ℂ)
      (halpha : alpha ∈ R₁ phi)
      (hbeta : beta ∈ pd.primeDadeReducedImageFamily isoL isoG j) :
      characterPairing alpha beta = 0 := by
    rw [primeDadeReducedImageFamily, Finset.mem_union] at hbeta
    rcases hbeta with hbeta | hbeta
    · obtain ⟨i, rfl⟩ :=
        (pd.mem_primeDadeSignedColumn isoL isoG j j _).mp hbeta
      rw [characterPairing_smul_right,
        hR₁_cyclic phi hphi (i, j) alpha halpha, mul_zero]
    · obtain ⟨gamma, hgamma, rfl⟩ := Finset.mem_image.mp hbeta
      obtain ⟨i, rfl⟩ :=
        (pd.mem_primeDadeSignedColumn isoL isoG j
          (IrreducibleCharacter.dual j) _).mp hgamma
      rw [characterPairing_neg_right', characterPairing_smul_right,
        hR₁_cyclic phi hphi (i, IrreducibleCharacter.dual j)
          alpha halpha, mul_zero, neg_zero]
  have hred_nontrivial (j : IrreducibleCharacter W₂ ℂ)
      (hjS : pti.primeTIRed isoL j ∈ S) :
      j ≠ IrreducibleCharacter.trivial := by
    intro hj
    subst j
    apply hnr (pti.primeTIRed isoL IrreducibleCharacter.trivial) hjS
    rw [pti.prTIred_aut isoL, IrreducibleCharacter.dual_trivial]
  have hred_ne_dual (j : IrreducibleCharacter W₂ ℂ)
      (hjS : pti.primeTIRed isoL j ∈ S) :
      j ≠ IrreducibleCharacter.dual j := by
    intro hj
    apply hnr (pti.primeTIRed isoL j) hjS
    rw [pti.prTIred_aut isoL, ← hj]
  have hred_tau_inverse (j : IrreducibleCharacter W₂ ℂ)
      (hjS : pti.primeTIRed isoL j ∈ S) :
      Dade pd.prDade_hyp
          (pti.primeTIRed isoL j -
            ClassFunction.inverseLinear (pti.primeTIRed isoL j)) =
        ∑ alpha ∈ pd.primeDadeReducedImageFamily isoL isoG j, alpha := by
    have hj := hred_nontrivial j hjS
    have hjdual := hred_ne_dual j hjS
    let T := pti.uniform_prTIred_seq isoL j
    obtain ⟨_, tau₁, htau₁, _, hagree⟩ :=
      pd.uniform_prTIred_coherent isoL isoG j hj
    have hjT : pti.primeTIRed isoL j ∈ T := by
      exact ⟨j, ⟨hj, rfl⟩, rfl⟩
    have hdualNontrivial : IrreducibleCharacter.dual j ≠
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) := by
      intro hdual
      apply hj
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
          pti.primeTIRed isoL j 1 := by
      calc
        pti.primeTIRed isoL (IrreducibleCharacter.dual j) 1 =
            ClassFunction.inverseLinear (pti.primeTIRed isoL j) 1 :=
          congrArg (fun f : ClassFunction L ℂ ↦ f 1)
            (pti.prTIred_aut isoL j).symm
        _ = pti.primeTIRed isoL j 1 := by simp
    have hdualT : pti.primeTIRed isoL (IrreducibleCharacter.dual j) ∈ T :=
      ⟨IrreducibleCharacter.dual j,
        ⟨hdualNontrivial, hdualDegree⟩, rfl⟩
    have hdiffSpan : pti.primeTIRed isoL j -
        ClassFunction.inverseLinear (pti.primeTIRed isoL j) ∈
        AddSubgroup.closure T := by
      rw [pti.prTIred_aut isoL]
      exact (AddSubgroup.closure T).sub_mem
        (AddSubgroup.subset_closure hjT)
        (AddSubgroup.subset_closure hdualT)
    have hdiffOff := inverse_sub_supported' (pti.primeTIRed isoL j)
    calc
      Dade pd.prDade_hyp
          (pti.primeTIRed isoL j -
            ClassFunction.inverseLinear (pti.primeTIRed isoL j)) =
          tau₁ (pti.primeTIRed isoL j -
            ClassFunction.inverseLinear (pti.primeTIRed isoL j)) :=
        (hagree _ hdiffSpan hdiffOff).symm
      _ = (pti.primeTISign isoL j : ℂ) •
          ((∑ i : IrreducibleCharacter W₁ ℂ,
              isoG.cyclicTIImage (i, j)) -
            ∑ i : IrreducibleCharacter W₁ ℂ,
              isoG.cyclicTIImage
                (i, IrreducibleCharacter.dual j)) := by
        rw [map_sub, pti.prTIred_aut isoL, htau₁ j,
          htau₁ (IrreducibleCharacter.dual j), smul_sub]
      _ = ∑ alpha ∈ pd.primeDadeReducedImageFamily isoL isoG j,
          alpha := (pd.sum_primeDadeReducedImageFamily
            isoL isoG j hjdual).symm
  let R : ClassFunction L ℂ → Finset (ClassFunction G ℂ) := fun phi ↦
    if hred : ∃ j : IrreducibleCharacter W₂ ℂ,
        phi = pti.primeTIRed isoL j then
      pd.primeDadeReducedImageFamily isoL isoG (Classical.choose hred)
    else R₁ phi
  have hRred (j : IrreducibleCharacter W₂ ℂ) :
      R (pti.primeTIRed isoL j) =
        pd.primeDadeReducedImageFamily isoL isoG j := by
    let hred : ∃ r : IrreducibleCharacter W₂ ℂ,
        pti.primeTIRed isoL j = pti.primeTIRed isoL r := ⟨j, rfl⟩
    have hchosen : j = Classical.choose hred :=
      pti.prTIred_inj isoL (Classical.choose_spec hred)
    rw [show R (pti.primeTIRed isoL j) =
        pd.primeDadeReducedImageFamily isoL isoG
          (Classical.choose hred) by
      simp only [R, dif_pos hred]]
    rw [← hchosen]
  have hRbase (phi : ClassFunction L ℂ)
      (hno : ¬ ∃ j : IrreducibleCharacter W₂ ℂ,
        phi = pti.primeTIRed isoL j) : R phi = R₁ phi := by
    change (if hred : ∃ j : IrreducibleCharacter W₂ ℂ,
        phi = pti.primeTIRed isoL j then
      pd.primeDadeReducedImageFamily isoL isoG (Classical.choose hred)
    else R₁ phi) = R₁ phi
    rw [dif_neg hno]
  have hsourceCharacter (phi : ClassFunction L ℂ) (hphi : phi ∈ S) :
      ClassFunction.IsOrdinaryCharacter phi := by
    obtain ⟨V, hV⟩ := seqInd_char KL (hS.1 hphi)
    refine ⟨VirtualCharacter.ofFDRep V,
      virtualCharacter_ofFDRep_isOrdinary V, ?_⟩
    rw [VirtualCharacter.realize_ofFDRep, hV]
  refine ⟨R, ?_, ?_, hRred⟩
  · refine {
      finite :=
        (seqIndD (k := ℂ) KL pd.signalizerInKernel ⊥).finite_toSet.subset
          hS.1
      source_character := hsourceCharacter
      source_virtual := ?_
      zero_not_mem := ?_
      degree_ne_zero := ?_
      inverse_ne := hnr
      inverse_mem := hS.2
      tau_isometry := hDadeIsometry
      tau_virtual := hDadeVirtual
      tau_supported := hDadeSupported
      pairwise_orthogonal := ?_
      image_virtual := ?_
      image_orthonormal := ?_
      tau_inverse_sub := ?_
      image_orthogonal := ?_ }
    · intro phi hphi
      exact seqInd_vcharW KL (hS.1 hphi)
    · intro hzero
      exact (seqInd_neq0 KL (hS.1 hzero)) rfl
    · intro phi hphi
      exact seqInd1_neq0 KL (hS.1 hphi)
    · intro phi hphi psi hpsi hne
      exact seqInd_ortho KL (hS.1 hphi) (hS.1 hpsi) hne
    · intro xi hxi alpha halpha
      by_cases hred : ∃ j : IrreducibleCharacter W₂ ℂ,
          xi = pti.primeTIRed isoL j
      · obtain ⟨j, rfl⟩ := hred
        rw [hRred j] at halpha
        exact primeDadeReducedImageFamily_virtual pd isoL isoG j halpha
      · rw [hRbase xi hred] at halpha
        exact hR₁.image_virtual xi (inS₁_of_not_reduced hxi hred)
          alpha halpha
    · intro xi hxi alpha halpha beta hbeta
      by_cases hred : ∃ j : IrreducibleCharacter W₂ ℂ,
          xi = pti.primeTIRed isoL j
      · obtain ⟨j, rfl⟩ := hred
        rw [hRred j] at halpha hbeta
        exact primeDadeReducedImageFamily_orthonormal pd isoL isoG j
          (hred_ne_dual j hxi) halpha hbeta
      · rw [hRbase xi hred] at halpha hbeta
        exact hR₁.image_orthonormal xi
          (inS₁_of_not_reduced hxi hred) alpha halpha beta hbeta
    · intro xi hxi
      by_cases hred : ∃ j : IrreducibleCharacter W₂ ℂ,
          xi = pti.primeTIRed isoL j
      · obtain ⟨j, rfl⟩ := hred
        rw [hRred j]
        exact hred_tau_inverse j hxi
      · rw [hRbase xi hred]
        exact hR₁.tau_inverse_sub xi (inS₁_of_not_reduced hxi hred)
    · intro xi hxi phi hphi hphiXi hphiInvXi alpha halpha beta hbeta
      by_cases hredXi : ∃ j : IrreducibleCharacter W₂ ℂ,
          xi = pti.primeTIRed isoL j
      · obtain ⟨j, rfl⟩ := hredXi
        rw [hRred j] at hbeta
        by_cases hredPhi : ∃ r : IrreducibleCharacter W₂ ℂ,
            phi = pti.primeTIRed isoL r
        · obtain ⟨r, rfl⟩ := hredPhi
          rw [hRred r] at halpha
          have hrj : r ≠ j := by
            intro hrj
            subst r
            have hnorm := cfnorm_seqInd_neq0 KL (hS.1 hxi)
            exact hnorm hphiXi
          have hrdualj : r ≠ IrreducibleCharacter.dual j := by
            intro hre
            have hleft :
                ClassFunction.inverseLinear (pti.primeTIRed isoL j) =
                  pti.primeTIRed isoL r :=
              (pti.prTIred_aut isoL j).trans
                (congrArg (pti.primeTIRed isoL) hre.symm)
            have hpairSelf := hphiInvXi
            rw [← hleft] at hpairSelf
            have hnorm := cfnorm_seqInd_neq0 KL
              (hS.1 (hS.2 _ hxi))
            exact hnorm hpairSelf
          exact primeDadeReducedImageFamilies_orthogonal pd isoL isoG
            r j hrj hrdualj halpha hbeta
        · rw [hRbase phi hredPhi] at halpha
          exact hR₁_reduced phi (inS₁_of_not_reduced hphi hredPhi)
            j alpha beta halpha hbeta
      · rw [hRbase xi hredXi] at hbeta
        by_cases hredPhi : ∃ r : IrreducibleCharacter W₂ ℂ,
            phi = pti.primeTIRed isoL r
        · obtain ⟨r, rfl⟩ := hredPhi
          rw [hRred r] at halpha
          rw [characterPairing_comm]
          exact hR₁_reduced xi (inS₁_of_not_reduced hxi hredXi)
            r beta alpha hbeta halpha
        · rw [hRbase phi hredPhi] at halpha
          exact hR₁.image_orthogonal xi
            (inS₁_of_not_reduced hxi hredXi) phi
            (inS₁_of_not_reduced hphi hredPhi)
            hphiXi hphiInvXi alpha halpha beta hbeta
  · intro phi hphi hirr w alpha halpha
    have hno : ¬ ∃ j : IrreducibleCharacter W₂ ℂ,
        phi = pti.primeTIRed isoL j := by
      rintro ⟨j, rfl⟩
      exact pti.prTIred_not_irr isoL j hirr
    rw [hRbase phi hno] at halpha
    let q := IrreducibleCharacter.cyclicTICharacterIndex defW w
    have horth := hR₁_cyclic phi (inS₁_of_not_reduced hphi hno)
      q alpha halpha
    simpa [q, CyclicTIIsometryData.cyclicTIImage,
      CyclicTIIsometryData.cyclicTISourceIrreducible] using horth

end PrimeDadeHypothesis

end

end Submission.OddOrder.PF
